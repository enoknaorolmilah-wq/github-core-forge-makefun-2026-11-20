import { createServer } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

const ENV_URL = (process.env.MAKEFUN_ENV_URL || '').replace(/\/+$/, '');
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN || '';
// This source is intentionally self-contained for the Node 22 trial pod.
const ZERO = '0'.repeat(40);
const repos = new Map();
let nextId = 1000;
let requestId = 0;
let primaryOwner = '';

function hash(type, data) {
  const b = Buffer.isBuffer(data) ? data : Buffer.from(data);
  return createHash('sha1').update(`${type} ${b.length}\0`).update(b).digest('hex');
}
function putObject(repo, type, data) {
  const b = Buffer.from(data);
  const sha = hash(type, b);
  repo.objects.set(sha, { type, data: b });
  return sha;
}
function pkt(data) {
  const b = Buffer.isBuffer(data) ? data : Buffer.from(data, 'utf8');
  return Buffer.concat([Buffer.from((b.length + 4).toString(16).padStart(4, '0')), b]);
}
function flush() { return Buffer.from('0000'); }
function packetLines(items) {
  return Buffer.concat(items.map((x) => x === null ? flush() : pkt(x)));
}
function readPackets(buffer, start = 0, stopAtFlush = true) {
  const packets = [];
  let at = start;
  while (at + 4 <= buffer.length) {
    const n = parseInt(buffer.toString('ascii', at, at + 4), 16);
    if (!Number.isFinite(n)) break;
    if (n === 0) { at += 4; packets.push(null); if (stopAtFlush) break; else continue; }
    if (n === 1 || n === 2) { at += 4; packets.push(n === 1 ? 'delim' : 'response-end'); continue; }
    if (n < 4 || at + n > buffer.length) break;
    packets.push(buffer.subarray(at + 4, at + n));
    at += n;
  }
  return { packets, offset: at };
}
function parseTree(data) {
  const entries = [];
  let at = 0;
  while (at < data.length) {
    const sp = data.indexOf(32, at), nul = data.indexOf(0, sp + 1);
    if (sp < 0 || nul < 0 || nul + 21 > data.length) break;
    entries.push({ mode: data.toString('ascii', at, sp), name: data.toString('utf8', sp + 1, nul), sha: data.subarray(nul + 1, nul + 21).toString('hex') });
    at = nul + 21;
  }
  return entries;
}
function buildTree(repo, files) {
  const root = { files: new Map(), dirs: new Map() };
  for (const [path, sha] of files) {
    const parts = path.split('/').filter(Boolean);
    let node = root;
    for (const part of parts.slice(0, -1)) {
      if (!node.dirs.has(part)) node.dirs.set(part, { files: new Map(), dirs: new Map() });
      node = node.dirs.get(part);
    }
    if (parts.length) node.files.set(parts[parts.length - 1], sha);
  }
  const build = (node) => {
    const entries = [];
    for (const [name, sha] of node.files) entries.push({ mode: '100644', name, sha });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, sha: build(child) });
    entries.sort((a, b) => Buffer.compare(Buffer.from(a.name + (a.mode === '40000' ? '/' : '')), Buffer.from(b.name + (b.mode === '40000' ? '/' : ''))));
    return putObject(repo, 'tree', Buffer.concat(entries.flatMap((e) => [Buffer.from(`${e.mode} ${e.name}\0`), Buffer.from(e.sha, 'hex')])));
  };
  return build(root);
}
function flattenTree(repo, tree, prefix = '', out = new Map()) {
  const obj = repo.objects.get(tree);
  if (!obj || obj.type !== 'tree') return out;
  for (const e of parseTree(obj.data)) {
    if (e.mode === '40000' || e.mode === '040000') flattenTree(repo, e.sha, `${prefix}${e.name}/`, out);
    else if (e.mode !== '160000') out.set(`${prefix}${e.name}`, e.sha);
  }
  return out;
}
function parseCommit(repo, sha) {
  const obj = repo.objects.get(sha);
  if (!obj || obj.type !== 'commit') return null;
  const head = obj.data.toString('utf8').split('\n\n')[0].split('\n');
  const tree = (head.find((x) => x.startsWith('tree ')) || '').slice(5);
  const parents = head.filter((x) => x.startsWith('parent ')).map((x) => x.slice(7));
  const message = obj.data.toString('utf8').split('\n\n').slice(1).join('\n\n').trimEnd();
  return { tree, parents, message };
}
function commitFiles(repo, sha) {
  const c = parseCommit(repo, sha);
  return c ? flattenTree(repo, c.tree) : new Map();
}
function makeCommit(repo, files, parent, message, identity = 'GitHub Forge <forge@example.invalid>') {
  const tree = buildTree(repo, files);
  const stamp = 1700000000 + repo.commitClock++;
  const who = `${identity} ${stamp} +0000`;
  const data = Buffer.from(`tree ${tree}\n${parent ? `parent ${parent}\n` : ''}author ${who}\ncommitter ${who}\n\n${message.endsWith('\n') ? message : `${message}\n`}`);
  const sha = putObject(repo, 'commit', data);
  repo.commits.set(sha, { sha, message: message.trimEnd(), parent: parent || null });
  return sha;
}
function repoKey(owner, name) { return `${String(owner).toLowerCase()}/${String(name).toLowerCase()}`; }
function makeRepo(name, owner = null, options = {}) {
  if (!name) return null;
  let r = repos.get(repoKey(owner || '', name));
  if (owner && r) return r;
  if (owner) {
    const orphan = repos.get(repoKey('', name));
    if (orphan && !orphan.owner) {
      repos.delete(repoKey('', name));
      orphan.owner = owner;
      repos.set(repoKey(owner, name), orphan);
      return orphan;
    }
  }
  if (!owner) {
    for (const candidate of repos.values()) if (candidate.name.toLowerCase() === String(name).toLowerCase() && !candidate.owner) return candidate;
  }
  const id = nextId++;
  r = {
    id, databaseId: id, owner: owner || null, name: String(name), private: options.private !== false,
    description: options.description || '', defaultBranch: options.default_branch || options.defaultBranch || 'main',
    refs: new Map(), objects: new Map(), commits: new Map(), issues: new Map(), pulls: new Map(),
    labels: new Map(), issueSeq: 0, pullSeq: 0, refFiles: new Map(), created: id, commitClock: 1
  };
  if (owner) repos.set(repoKey(owner, name), r);
  else repos.set(repoKey('', name), r);
  return r;
}
function resolveRepo(owner, name, bind = true) {
  const key = repoKey(owner, name);
  let r = repos.get(key);
  if (!r) r = repos.get(repoKey('', name));
  if (r && !r.owner && bind) {
    repos.delete(repoKey('', name));
    r.owner = owner;
    repos.set(key, r);
    if (!primaryOwner) primaryOwner = owner;
  }
  if (r && String(r.owner).toLowerCase() === String(owner).toLowerCase()) return r;
  return null;
}
function lookupRepoById(id) { return [...repos.values()].find((r) => String(r.id) === String(id) || globalId('Repository', r.id) === id) || null; }
function globalId(type, id, number) {
  return Buffer.from(`${type}:${id}${number === undefined ? '' : `:${number}`}`).toString('base64');
}
function decodeId(value) {
  try { return Buffer.from(String(value), 'base64').toString('utf8'); } catch { return ''; }
}
function updateBranchFiles(repo, ref, sha) {
  const files = commitFiles(repo, sha);
  repo.refFiles.set(ref.slice('refs/heads/'.length), files);
}
function refsFor(repo) { return [...repo.refs.entries()].sort(([a], [b]) => a.localeCompare(b)); }
function branchSha(repo, name) { return repo.refs.get(name.startsWith('refs/') ? name : `refs/heads/${name}`) || null; }
function reqAuth(req) {
  const h = String(req.headers.authorization || '');
  return !!TOKEN && h === `Bearer ${TOKEN}`;
}
function sendJson(res, status, value, headers = {}) {
  const body = `${JSON.stringify(value)}\n`;
  res.writeHead(status, { 'content-type': 'application/json; charset=utf-8', 'content-length': Buffer.byteLength(body), 'x-github-request-id': `F${(++requestId).toString(36).toUpperCase()}`, ...headers });
  res.end(body);
}
function sendRaw(res, status, body, type, headers = {}) {
  res.writeHead(status, { 'content-type': type, 'content-length': body.length, ...headers });
  res.end(body);
}
async function readBody(req, limit = 64 * 1024 * 1024) {
  const chunks = [];
  let size = 0;
  for await (const chunk of req) {
    size += chunk.length;
    if (size > limit) throw new Error('request body too large');
    chunks.push(Buffer.from(chunk));
  }
  return Buffer.concat(chunks, size);
}
async function jsonBody(req) {
  const b = await readBody(req, 16 * 1024 * 1024);
  try { return { value: b.length ? JSON.parse(b.toString('utf8')) : {}, raw: b, bad: false }; }
  catch { return { value: null, raw: b, bad: true }; }
}
function error(res, status, message) { sendJson(res, status, { message }); }
function repoJson(r) {
  return { id: r.databaseId, node_id: globalId('Repository', r.id), name: r.name, full_name: `${r.owner || ''}/${r.name}`, owner: { login: r.owner || '' }, private: r.private, description: r.description, default_branch: r.defaultBranch, has_issues: true, open_issues_count: [...r.issues.values()].filter((x) => x.state === 'open').length, html_url: `http://github.local/${r.owner || ''}/${r.name}` };
}
function issueJson(r, issue) {
  return { id: issue.id, node_id: globalId('Issue', r.id, issue.number), number: issue.number, title: issue.title, body: issue.body, state: issue.state, labels: issue.labels.map((name) => ({ id: r.labels.get(name)?.id || 0, name, color: r.labels.get(name)?.color || 'ededed' })), user: { login: r.owner || '' }, comments: issue.comments.length, created_at: issue.created_at, updated_at: issue.updated_at, html_url: `http://github.local/${r.owner}/${r.name}/issues/${issue.number}` };
}
function createIssue(r, data = {}) {
  const number = ++r.issueSeq;
  const issue = { id: nextId++, number, title: String(data.title || ''), body: String(data.body || ''), state: 'open', labels: Array.isArray(data.labels) ? data.labels.map((x) => typeof x === 'string' ? x : x?.name).filter((x) => r.labels.has(x)) : [], comments: [], created_at: new Date().toISOString(), updated_at: new Date().toISOString() };
  r.issues.set(number, issue);
  return issue;
}
function pullJson(r, p) {
  const headSha = branchSha(r, p.head), baseSha = branchSha(r, p.base);
  return { id: p.id, node_id: globalId('PullRequest', r.id, p.number), number: p.number, state: p.state, title: p.title, body: p.body, merged: p.merged, mergeable: p.conflicted ? false : true, mergeable_state: p.conflicted ? 'dirty' : 'clean', head: { ref: p.head, sha: headSha || ZERO, label: `${r.owner}:${p.head}`, repo: repoJson(r) }, base: { ref: p.base, sha: baseSha || ZERO, label: `${r.owner}:${p.base}`, repo: repoJson(r) }, merged_at: p.merged_at || null, merge_commit_sha: p.merge_commit_sha || null, created_at: p.created_at };
}
function allRefs(repo) {
  const a = refsFor(repo);
  if (a.length) {
    const head = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
    return [['HEAD', head || a[0][1]], ...a];
  }
  return [['HEAD', null]];
}
function isAncestor(repo, oldSha, newSha) {
  if (oldSha === ZERO) return true;
  const seen = new Set(), todo = [newSha];
  while (todo.length) {
    const sha = todo.pop();
    if (sha === oldSha) return true;
    if (!sha || seen.has(sha)) continue;
    seen.add(sha);
    const c = parseCommit(repo, sha);
    if (c) todo.push(...c.parents);
  }
  return false;
}
function reachable(repo, roots, depth = 0, boundaries = []) {
  const found = new Set(), shallow = new Set(), boundarySet = new Set(boundaries);
  const todo = roots.map((sha) => ({ sha, level: 1 }));
  while (todo.length) {
    const { sha, level } = todo.pop();
    if (!sha || found.has(sha)) continue;
    const obj = repo.objects.get(sha);
    if (!obj) continue;
    found.add(sha);
    if (obj.type === 'commit') {
      const c = parseCommit(repo, sha);
      if (!c) continue;
      todo.push({ sha: c.tree, level });
      if (c.parents.length && (boundarySet.has(sha) || (depth > 0 && level >= depth))) shallow.add(sha);
      else for (const parent of c.parents) todo.push({ sha: parent, level: level + 1 });
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) if (e.mode !== '160000') todo.push({ sha: e.sha, level });
    } else if (obj.type === 'tag') {
      const target = obj.data.toString().match(/^object ([0-9a-f]{40})/m);
      if (target) todo.push({ sha: target[1], level });
    }
  }
  return { found, shallow: [...shallow] };
}

function parsePack(pack, repo) {
  const objects = new Map();
  if (pack.length < 32 || pack.toString('ascii', 0, 4) !== 'PACK') throw new Error('invalid pack');
  const count = pack.readUInt32BE(8), trailer = pack.length - 20;
  let pos = 12;
  const raw = [];
  function inflateAt(at) {
    const result = inflateSync(pack.subarray(at), { info: true });
    const data = result.buffer;
    const used = result.engine.bytesWritten;
    if (!used) throw new Error('bad zlib stream');
    return { data, next: at + used };
  }
  for (let i = 0; i < count; i++) {
    const entryOffset = pos;
    let byte = pack[pos++], typeCode = (byte >> 4) & 7, size = byte & 15, shift = 4;
    while (byte & 128) { byte = pack[pos++]; size += (byte & 127) * 2 ** shift; shift += 7; }
    let baseOffset = null, baseOid = null;
    if (typeCode === 6) {
      byte = pack[pos++];
      let n = byte & 127;
      while (byte & 128) { byte = pack[pos++]; n = (n + 1) * 128 + (byte & 127); }
      baseOffset = entryOffset - n;
    } else if (typeCode === 7) { baseOid = pack.subarray(pos, pos + 20).toString('hex'); pos += 20; }
    const inflated = inflateAt(pos);
    pos = inflated.next;
    if (inflated.data.length !== size) throw new Error('pack object size mismatch');
    raw.push({ entryOffset, typeCode, size, data: inflated.data, baseOffset, baseOid });
  }
  const offsetMap = new Map(raw.map((x) => [x.entryOffset, x]));
  const codeTypes = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };
  const resolve = (entry, active = new Set()) => {
    if (entry.resolved) return entry.resolved;
    if (active.has(entry.entryOffset)) throw new Error('delta cycle');
    active.add(entry.entryOffset);
    let type = codeTypes[entry.typeCode], data = entry.data;
    if (entry.typeCode === 6 || entry.typeCode === 7) {
      let base;
      if (entry.typeCode === 6) {
        const b = offsetMap.get(entry.baseOffset);
        if (!b) throw new Error('missing ofs delta base');
        base = resolve(b, active);
      } else {
        const b = [...objects].find(([sha]) => sha === entry.baseOid)?.[1];
        base = b || repo.objects.get(entry.baseOid);
        if (!base) throw new Error('missing ref delta base');
      }
      type = base.type;
      data = applyDelta(base.data, entry.data);
    }
    const result = { type, data, sha: hash(type, data) };
    entry.resolved = result;
    active.delete(entry.entryOffset);
    return result;
  };
  for (const entry of raw) {
    const obj = resolve(entry);
    objects.set(obj.sha, { type: obj.type, data: obj.data });
  }
  if (pos !== trailer) throw new Error('trailing pack data');
  return objects;
}
function applyDelta(base, delta) {
  let p = 0;
  const varint = () => { let n = 0, s = 0, b; do { b = delta[p++]; n += (b & 127) * 2 ** s; s += 7; } while (b & 128); return n; };
  const baseSize = varint(), targetSize = varint();
  if (baseSize !== base.length) throw new Error('delta base mismatch');
  const out = Buffer.alloc(targetSize); let w = 0;
  while (p < delta.length) {
    const op = delta[p++];
    if (op & 128) {
      let off = 0, size = 0, sh = 0;
      for (let i = 0; i < 4; i++) { if (op & (1 << i)) off += delta[p++] * 2 ** sh; sh += 8; }
      sh = 0;
      for (let i = 4; i < 7; i++) { if (op & (1 << i)) size += delta[p++] * 2 ** sh; sh += 8; }
      if (!size) size = 65536;
      base.copy(out, w, off, off + size); w += size;
    } else { const size = op & 127; delta.copy(out, w, p, p + size); p += size; w += size; }
  }
  return out;
}
function writePack(objects) {
  const parts = [];
  const head = Buffer.alloc(12); head.write('PACK'); head.writeUInt32BE(2, 4); head.writeUInt32BE(objects.length, 8); parts.push(head);
  const typeCodes = { commit: 1, tree: 2, blob: 3, tag: 4 };
  for (const o of objects) {
    let size = o.data.length, first = (typeCodes[o.type] << 4) | (size & 15); size = Math.floor(size / 16);
    const bytes = [];
    while (size) { bytes.push(first | 128); first = size & 127; size = Math.floor(size / 128); }
    bytes.push(first);
    parts.push(Buffer.from(bytes), deflateSync(o.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

function sendEmpty(res, status) {
  res.writeHead(status, { 'content-type': 'application/json; charset=utf-8', 'content-length': '0', 'x-github-request-id': `F${(++requestId).toString(36).toUpperCase()}` });
  res.end();
}
function restContent(repo, ref, path) {
  const sha = branchSha(repo, ref || repo.defaultBranch);
  if (!sha) return null;
  const files = commitFiles(repo, sha);
  const blob = files.get(path);
  if (blob) {
    const obj = repo.objects.get(blob);
    if (!obj) return null;
    return { type: 'file', encoding: 'base64', content: obj.data.toString('base64').replace(/(.{60})/g, '$1\n').trimEnd(), sha: blob, size: obj.data.length, name: path.split('/').pop(), path };
  }
  const prefix = path ? `${path.replace(/\/+$/, '')}/` : '';
  const dirs = new Map();
  for (const [file, blobSha] of files) {
    if (!file.startsWith(prefix)) continue;
    const rest = file.slice(prefix.length), first = rest.split('/')[0];
    if (!first) continue;
    const nested = rest.includes('/');
    if (!dirs.has(first)) dirs.set(first, nested ? { type: 'dir', sha: null, path: `${prefix}${first}` } : { type: 'file', sha: blobSha, path: `${prefix}${first}` });
  }
  if (dirs.size || path === '') return [...dirs.entries()].sort(([a], [b]) => a.localeCompare(b)).map(([name, v]) => ({ name, ...v }));
  return null;
}
function branchFiles(repo, branch) {
  const ref = branch.startsWith('refs/') ? branch : `refs/heads/${branch}`;
  if (repo.refFiles.has(ref.slice('refs/heads/'.length))) return new Map(repo.refFiles.get(ref.slice('refs/heads/'.length)));
  const sha = repo.refs.get(ref);
  return sha ? commitFiles(repo, sha) : new Map();
}
function diffFiles(repo, beforeSha, afterSha) {
  const before = beforeSha ? commitFiles(repo, beforeSha) : new Map();
  const after = afterSha ? commitFiles(repo, afterSha) : new Map();
  const out = [];
  for (const path of new Set([...before.keys(), ...after.keys()])) {
    const old = before.get(path), next = after.get(path);
    if (old === next) continue;
    const a = old && repo.objects.get(old)?.data.toString('utf8').split('\n') || [];
    const b = next && repo.objects.get(next)?.data.toString('utf8').split('\n') || [];
    out.push({ filename: path, status: !old ? 'added' : !next ? 'removed' : 'modified', additions: b.filter((x) => !a.includes(x)).length, deletions: a.filter((x) => !b.includes(x)).length, changes: Math.max(1, b.length + a.length), patch: '' });
  }
  return out;
}
function createPull(repo, body = {}) {
  const head = String(body.head || ''), base = String(body.base || repo.defaultBranch);
  const headSha = branchSha(repo, head), baseSha = branchSha(repo, base);
  if (!headSha || !baseSha) return null;
  const number = ++repo.pullSeq;
  const p = { id: nextId++, number, state: 'open', merged: false, title: String(body.title || ''), body: String(body.body || ''), head, base, conflicted: false, merge_commit_sha: null, merged_at: null, created_at: new Date().toISOString() };
  repo.pulls.set(number, p);
  return p;
}
function mergePull(repo, p) {
  if (!p || p.state !== 'open') return { status: 405, body: { message: 'Pull Request is not mergeable' } };
  const headSha = branchSha(repo, p.head), baseSha = branchSha(repo, p.base);
  if (!headSha || !baseSha) return { status: 405, body: { message: 'Pull Request is not mergeable' } };
  if (p.conflicted || !isAncestor(repo, baseSha, headSha)) return { status: 405, body: { message: 'Pull Request is not mergeable' } };
  const files = commitFiles(repo, baseSha);
  for (const [path, sha] of commitFiles(repo, headSha)) files.set(path, sha);
  const sha = makeCommit(repo, files, baseSha, `Squash merge pull request #${p.number}: ${p.title}`);
  repo.refs.set(`refs/heads/${p.base}`, sha);
  updateBranchFiles(repo, `refs/heads/${p.base}`, sha);
  p.state = 'closed'; p.merged = true; p.merge_commit_sha = sha; p.merged_at = new Date().toISOString();
  for (const other of repo.pulls.values()) {
    if (other.number === p.number || other.state !== 'open' || other.base !== p.base) continue;
    const headFiles = commitFiles(repo, branchSha(repo, other.head) || '');
    const oldBase = commitFiles(repo, baseSha);
    const nowBase = commitFiles(repo, sha);
    for (const path of headFiles.keys()) {
      if (headFiles.get(path) !== oldBase.get(path) && nowBase.get(path) !== oldBase.get(path) && nowBase.get(path) !== headFiles.get(path)) other.conflicted = true;
    }
  }
  return { status: 200, body: { sha, merged: true, message: 'Pull Request successfully merged' } };
}
function getUserLogin() { return primaryOwner || ''; }

async function handleRest(req, res, url) {
  const method = req.method || 'GET';
  const path = url.pathname.slice('/api/v3'.length);
  if (!reqAuth(req)) return error(res, 401, 'Requires authentication');
  if (method === 'GET' && (path === '' || path === '/')) return sendJson(res, 200, { current_user_url: '/api/v3/user', user_url: '/api/v3/users/{user}', repository_url: '/api/v3/repos/{owner}/{repo}' }, { 'x-oauth-scopes': 'repo, read:org' });
  if (method === 'GET' && path === '/meta') return sendJson(res, 200, { installed_version: '3.0.0', verifiable_password_authentication: true });
  if (method === 'GET' && path === '/user') {
    const login = getUserLogin();
    return login ? sendJson(res, 200, { id: 1, login, type: 'User', name: login }) : error(res, 404, 'Not Found');
  }
  if (path === '/user/repos' && method === 'POST') {
    const parsed = await jsonBody(req);
    if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
    const data = parsed.value || {};
    const name = String(data.name || '');
    if (!name) return error(res, 422, 'Repository name is required');
    let r = makeRepo(name, null, data);
    r.private = data.private !== false;
    r.description = String(data.description || '');
    r.defaultBranch = String(data.default_branch || data.defaultBranch || 'main');
    return sendJson(res, 201, repoJson(r));
  }
  if (path === '/user/repos' && method === 'GET') {
    const list = [...repos.values()].filter((r) => !r.owner || !primaryOwner || r.owner === primaryOwner).sort((a, b) => a.created - b.created);
    const per = Math.max(1, Math.min(100, Number(url.searchParams.get('per_page') || 30)));
    const page = Math.max(1, Number(url.searchParams.get('page') || 1));
    const result = list.slice((page - 1) * per, page * per).map(repoJson);
    const headers = {};
    if (page * per < list.length) {
      const base = `http://${req.headers.host || 'localhost'}/api/v3/user/repos`;
      headers.link = `<${base}?per_page=${per}&page=${page + 1}>; rel="next", <${base}?per_page=${per}&page=${Math.ceil(list.length / per)}>; rel="last"`;
    }
    return sendJson(res, 200, result, headers);
  }
  const parts = path.split('/').filter(Boolean);
  if (parts[0] !== 'repos' || parts.length < 3) return error(res, 404, 'Not Found');
  const owner = decodeURIComponent(parts[1]), name = decodeURIComponent(parts[2]);
  const repo = resolveRepo(owner, name, true);
  if (!repo) return error(res, 404, 'Not Found');
  if (parts.length === 3) {
    if (method === 'GET') return sendJson(res, 200, repoJson(repo));
    if (method === 'PATCH') {
      const parsed = await jsonBody(req); if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
      if (parsed.value.description !== undefined) repo.description = String(parsed.value.description);
      if (parsed.value.default_branch) repo.defaultBranch = String(parsed.value.default_branch);
      return sendJson(res, 200, repoJson(repo));
    }
    if (method === 'DELETE') {
      repos.delete(repoKey(owner, name));
      repos.delete(repoKey('', name));
      return sendEmpty(res, 204);
    }
  }
  const sub = parts.slice(3);
  if (sub[0] === 'branches' && method === 'GET') {
    if (sub.length > 1) {
      const branch = decodeURIComponent(sub.slice(1).join('/')), sha = branchSha(repo, branch);
      return sha ? sendJson(res, 200, { name: branch, commit: { sha, url: '' }, protected: false }) : error(res, 404, 'Branch not found');
    }
    return sendJson(res, 200, refsFor(repo).filter(([ref]) => ref.startsWith('refs/heads/')).map(([ref, sha]) => ({ name: ref.slice(11), commit: { sha, commit: { message: parseCommit(repo, sha)?.message || '' } }, protected: false })));
  }
  if (sub[0] === 'git' && sub[1] === 'refs') {
    if (method === 'POST' && sub.length === 2) {
      const parsed = await jsonBody(req); if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
      const ref = String(parsed.value.ref || ''), sha = String(parsed.value.sha || '');
      if (!ref.startsWith('refs/') || !repo.objects.has(sha)) return error(res, 422, 'Reference does not exist');
      repo.refs.set(ref, sha);
      if (ref.startsWith('refs/heads/')) updateBranchFiles(repo, ref, sha);
      if (ref === `refs/heads/${repo.defaultBranch}` && !primaryOwner) primaryOwner = owner;
      return sendJson(res, 201, { ref, node_id: globalId('Ref', nextId++), object: { sha, type: repo.objects.get(sha)?.type || 'commit', url: '' } });
    }
    if (method === 'GET' && sub.length >= 3) {
      const ref = `${sub[2]}/${sub.slice(3).map(decodeURIComponent).join('/')}`, sha = repo.refs.get(ref);
      return sha ? sendJson(res, 200, { ref, node_id: globalId('Ref', nextId++), object: { sha, type: repo.objects.get(sha)?.type || 'commit', url: '' } }) : error(res, 404, 'Reference does not exist');
    }
  }
  if (sub[0] === 'commits' && method === 'GET') {
    const ref = url.searchParams.get('sha') || repo.defaultBranch, start = branchSha(repo, ref);
    const out = [], seen = new Set(), todo = start ? [start] : [];
    while (todo.length && out.length < 100) {
      const sha = todo.shift(); if (seen.has(sha)) continue; seen.add(sha);
      const c = parseCommit(repo, sha); if (!c) continue;
      out.push({ sha, commit: { message: c.message, tree: { sha: c.tree }, author: { name: 'GitHub Forge', date: new Date(0).toISOString() } }, parents: c.parents.map((x) => ({ sha: x })) });
      todo.push(...c.parents);
    }
    return sendJson(res, 200, out);
  }
  if (sub[0] === 'contents') {
    const filePath = sub.slice(1).map(decodeURIComponent).join('/');
    if (method === 'GET') {
      const item = restContent(repo, url.searchParams.get('ref') || repo.defaultBranch, filePath);
      return item ? sendJson(res, 200, item) : error(res, 404, 'Not Found');
    }
    if (method === 'PUT') {
      const parsed = await jsonBody(req); if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
      const data = parsed.value || {}, branch = String(data.branch || repo.defaultBranch);
      let files = branchFiles(repo, branch);
      const old = files.get(filePath);
      if (old && String(data.sha || '') !== old) return error(res, 409, 'sha does not match');
      if (!old && data.sha) return error(res, 409, 'sha does not match');
      let content;
      try { content = Buffer.from(String(data.content || ''), 'base64'); } catch { return error(res, 422, 'Invalid content'); }
      const blob = putObject(repo, 'blob', content);
      files.set(filePath, blob);
      const ref = `refs/heads/${branch}`, parent = repo.refs.get(ref) || null;
      const commit = makeCommit(repo, files, parent, String(data.message || 'Update file'));
      repo.refs.set(ref, commit); repo.refFiles.set(branch, files);
      if (!parent && branch === repo.defaultBranch && !primaryOwner) primaryOwner = owner;
      return sendJson(res, old ? 200 : 201, { content: { name: filePath.split('/').pop(), path: filePath, sha: blob, size: content.length, url: '', html_url: '', git_url: '', download_url: '', type: 'file', encoding: 'base64' }, commit: { sha: commit, message: String(data.message || 'Update file'), url: '' } });
    }
    if (method === 'DELETE') {
      const parsed = await jsonBody(req); if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
      const data = parsed.value || {}, branch = String(data.branch || repo.defaultBranch), files = branchFiles(repo, branch), old = files.get(filePath);
      if (!old) return error(res, 404, 'Not Found');
      if (data.sha && String(data.sha) !== old) return error(res, 409, 'sha does not match');
      files.delete(filePath);
      const commit = makeCommit(repo, files, repo.refs.get(`refs/heads/${branch}`) || null, String(data.message || 'Delete file'));
      repo.refs.set(`refs/heads/${branch}`, commit); repo.refFiles.set(branch, files);
      return sendJson(res, 200, { commit: { sha: commit, message: String(data.message || 'Delete file') }, content: null });
    }
  }
  if (sub[0] === 'labels') {
    if (method === 'POST') {
      const parsed = await jsonBody(req); if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
      const data = parsed.value || {}, labelName = String(data.name || '');
      if (!labelName) return error(res, 422, 'name is required');
      if (repo.labels.has(labelName)) return error(res, 422, 'already_exists');
      const label = { id: nextId++, name: labelName, color: String(data.color || 'ededed'), description: String(data.description || '') };
      repo.labels.set(labelName, label);
      return sendJson(res, 201, label);
    }
    if (method === 'GET') return sendJson(res, 200, [...repo.labels.values()]);
  }
  if (sub[0] === 'issues') {
    if (sub.length === 1 && method === 'POST') {
      const parsed = await jsonBody(req); if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
      const labels = Array.isArray(parsed.value.labels) ? parsed.value.labels.map((x) => typeof x === 'string' ? x : x?.name) : [];
      if (labels.some((x) => !repo.labels.has(x))) return error(res, 422, 'Validation Failed: label does not exist');
      return sendJson(res, 201, issueJson(repo, createIssue(repo, parsed.value)));
    }
    if (sub.length === 1 && method === 'GET') {
      const state = (url.searchParams.get('state') || 'open').toLowerCase();
      let list = [...repo.issues.values()].filter((x) => state === 'all' || x.state === state);
      const direction = (url.searchParams.get('direction') || 'desc').toLowerCase();
      list.sort((a, b) => (a.number - b.number) * (direction === 'asc' ? 1 : -1));
      return sendJson(res, 200, list.map((x) => issueJson(repo, x)));
    }
    const number = Number(sub[1]), issue = repo.issues.get(number);
    if (sub[2] === 'comments') {
      if (!issue) return error(res, 404, 'Not Found');
      if (method === 'POST') {
        const parsed = await jsonBody(req); if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
        const c = { id: nextId++, body: String(parsed.value.body || ''), user: { login: owner }, created_at: new Date().toISOString() };
        issue.comments.push(c); return sendJson(res, 201, c);
      }
      if (method === 'GET') return sendJson(res, 200, issue.comments);
    }
    if (sub.length === 2 && method === 'GET') return issue ? sendJson(res, 200, issueJson(repo, issue)) : error(res, 404, 'Not Found');
    if (sub.length === 2 && method === 'PATCH') {
      if (!issue) return error(res, 404, 'Not Found');
      const parsed = await jsonBody(req); if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
      const data = parsed.value || {};
      if (data.title !== undefined) issue.title = String(data.title);
      if (data.body !== undefined) issue.body = String(data.body);
      if (data.state === 'closed' || data.state === 'open') issue.state = data.state;
      issue.updated_at = new Date().toISOString();
      return sendJson(res, 200, issueJson(repo, issue));
    }
  }
  if (sub[0] === 'pulls') {
    if (sub.length === 1 && method === 'POST') {
      const parsed = await jsonBody(req); if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
      const pull = createPull(repo, parsed.value);
      return pull ? sendJson(res, 201, pullJson(repo, pull)) : error(res, 422, 'Head or base branch not found');
    }
    if (sub.length === 1 && method === 'GET') {
      const state = (url.searchParams.get('state') || 'open').toLowerCase();
      return sendJson(res, 200, [...repo.pulls.values()].filter((p) => state === 'all' || p.state === state).map((p) => pullJson(repo, p)));
    }
    const number = Number(sub[1]), pull = repo.pulls.get(number);
    if (sub[2] === 'merge' && method === 'PUT') {
      if (!pull) return error(res, 404, 'Not Found');
      const result = mergePull(repo, pull);
      return sendJson(res, result.status, result.body);
    }
    if (sub[2] === 'files' && method === 'GET') {
      if (!pull) return error(res, 404, 'Not Found');
      return sendJson(res, 200, diffFiles(repo, branchSha(repo, pull.base), branchSha(repo, pull.head)));
    }
    if (sub.length === 2 && method === 'GET') return pull ? sendJson(res, 200, pullJson(repo, pull)) : error(res, 404, 'Not Found');
  }
  return error(res, 404, 'Not Found');
}

function lexGraphql(text) {
  const out = [];
  for (let i = 0; i < text.length;) {
    const c = text[i];
    if (/\s|,/u.test(c)) { i++; continue; }
    if (c === '#') { while (i < text.length && text[i] !== '\n') i++; continue; }
    if (c === '"' && text.slice(i, i + 3) === '"""') {
      const end = text.indexOf('"""', i + 3);
      if (end < 0) throw new Error('Unterminated block string');
      out.push({ kind: 'string', value: text.slice(i + 3, end) }); i = end + 3; continue;
    }
    if (c === '"') {
      let j = i + 1, escaped = false;
      while (j < text.length) { if (!escaped && text[j] === '"') break; if (!escaped && text[j] === '\\') escaped = true; else escaped = false; j++; }
      if (j >= text.length) throw new Error('Unterminated string');
      out.push({ kind: 'string', value: JSON.parse(text.slice(i, j + 1)) }); i = j + 1; continue;
    }
    if (/[A-Za-z_]/u.test(c)) {
      let j = i + 1; while (j < text.length && /[A-Za-z0-9_]/u.test(text[j])) j++;
      out.push({ kind: 'name', value: text.slice(i, j) }); i = j; continue;
    }
    if (/[0-9-]/u.test(c)) {
      let j = i + 1; while (j < text.length && /[0-9.eE+-]/u.test(text[j])) j++;
      out.push({ kind: 'number', value: text.slice(i, j) }); i = j; continue;
    }
    if (text.slice(i, i + 3) === '...') { out.push({ kind: 'punct', value: '...' }); i += 3; continue; }
    if ('!$():=@[]{|}&'.includes(c)) { out.push({ kind: 'punct', value: c }); i++; continue; }
    throw new Error(`Unexpected character ${c}`);
  }
  return out;
}
function parseGraphql(text, variables = {}) {
  const t = lexGraphql(text); let i = 0;
  const peek = (v) => t[i]?.value === v;
  const take = () => t[i++];
  const expect = (v) => { if (!peek(v)) throw new Error(`Expected ${v}`); return take(); };
  const skipGroup = (open, close) => {
    if (!peek(open)) return;
    let depth = 0;
    do { const x = take(); if (x.value === open) depth++; if (x.value === close) depth--; } while (i < t.length && depth > 0);
  };
  const value = () => {
    if (peek('$')) { take(); const name = take()?.value; return variables[name]; }
    if (peek('[')) { take(); const a = []; while (i < t.length && !peek(']')) a.push(value()); expect(']'); return a; }
    if (peek('{')) {
      take(); const o = {};
      while (i < t.length && !peek('}')) { const key = take()?.value; expect(':'); o[key] = value(); }
      expect('}'); return o;
    }
    const x = take();
    if (!x) throw new Error('Missing value');
    if (x.kind === 'string') return x.value;
    if (x.kind === 'number') return Number(x.value);
    if (x.value === 'true') return true;
    if (x.value === 'false') return false;
    if (x.value === 'null') return null;
    return x.value;
  };
  const selection = () => {
    expect('{');
    const fields = [];
    while (i < t.length && !peek('}')) {
      if (peek('...')) {
        take();
        if (peek('on')) { take(); const type = take()?.value; fields.push({ fragment: type, fields: selection() }); }
        else { take(); }
        continue;
      }
      let first = take();
      if (!first || first.kind !== 'name') throw new Error('Expected field');
      let alias = null, name = first.value;
      if (peek(':')) { take(); alias = name; name = take()?.value; }
      const args = {};
      if (peek('(')) {
        take();
        while (i < t.length && !peek(')')) { const key = take()?.value; expect(':'); args[key] = value(); }
        expect(')');
      }
      while (peek('@')) { take(); take(); if (peek('(')) skipGroup('(', ')'); }
      fields.push({ name, alias, args, fields: peek('{') ? selection() : null });
    }
    expect('}');
    return fields;
  };
  let operation = 'query';
  if (!peek('{')) {
    const op = take();
    if (op && ['query', 'mutation', 'subscription'].includes(op.value)) operation = op.value;
    else if (op?.value !== 'fragment') throw new Error('Invalid operation');
    if (t[i]?.kind === 'name' && !peek('on')) take();
    if (peek('(')) skipGroup('(', ')');
    while (peek('@')) { take(); take(); if (peek('(')) skipGroup('(', ')'); }
  }
  const fields = selection();
  return { operation, fields };
}
function wrap(kind, value) { return { __kind: kind, value }; }
function introspectionType(name) {
  const fieldLists = {
    Issue: ['id', 'number', 'title', 'state', 'body', 'labels', 'url'],
    PullRequest: ['id', 'number', 'headRefName', 'baseRefName', 'mergeable', 'state', 'merged', 'files', 'title', 'body'],
    Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest'],
    User: ['id', 'login'],
    Query: ['viewer', 'repository', 'node', '__type'],
  };
  const enums = { SearchType: ['ISSUE', 'DISCUSSION', 'REPOSITORY', 'USER', 'COMMIT', 'TOPIC'], IssueState: ['OPEN', 'CLOSED'], PullRequestState: ['OPEN', 'CLOSED', 'MERGED'], MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] };
  if (!fieldLists[name] && !enums[name]) return null;
  return { __kind: 'TypeInfo', value: { name, fields: (fieldLists[name] || []).map((x) => wrap('TypeField', { name: x })), enumValues: (enums[name] || []).map((x) => wrap('TypeEnum', { name: x })) } };
}
function resolveField(parent, field, errors) {
  const name = field.name, args = field.args || {};
  if (name === '__typename') return parent?.__kind || 'Query';
  if (name === '__type') return introspectionType(args.name);
  const kind = parent?.__kind, value = parent?.value;
  const allowed = {
    User: ['id', 'login'],
    Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'description'],
    Issue: ['id', 'number', 'title', 'state', 'body', 'labels', 'url'],
    PullRequest: ['id', 'number', 'headRefName', 'baseRefName', 'mergeable', 'state', 'merged', 'files', 'title', 'body'],
    IssueConnection: ['nodes', 'pageInfo', 'totalCount'],
    PullConnection: ['nodes', 'pageInfo', 'totalCount'],
    FileConnection: ['nodes', 'pageInfo', 'totalCount'],
    PageInfo: ['hasNextPage', 'endCursor', 'startCursor'],
    PullFile: ['path', 'additions', 'deletions', 'changeType'],
    TypeInfo: ['name', 'fields', 'enumValues', 'kind', 'description'],
    TypeField: ['name', 'description', 'args', 'type', 'isDeprecated', 'deprecationReason'],
    TypeEnum: ['name', 'description', 'isDeprecated', 'deprecationReason'],
    Label: ['name'],
    CommentEdge: ['node'],
    Comment: ['id', 'body'],
    BranchRef: ['name', 'target'],
    Node: ['id'],
  };
  if (kind && allowed[kind] && !allowed[kind].includes(name)) {
    errors.push(`Cannot query field "${name}" on type "${kind === 'PullConnection' ? 'PullRequestConnection' : kind === 'IssueConnection' ? 'IssueConnection' : kind}".`);
    return null;
  }
  if (!parent || parent == null) return null;
  if (kind === 'User') return name === 'login' ? value.login : value.id || 1;
  if (kind === 'Repository') {
    const r = value;
    if (name === 'id') return globalId('Repository', r.id);
    if (name === 'databaseId') return r.databaseId;
    if (name === 'name') return r.name;
    if (name === 'nameWithOwner') return `${r.owner}/${r.name}`;
    if (name === 'owner') return wrap('User', { login: r.owner });
    if (name === 'defaultBranchRef') return branchSha(r, r.defaultBranch) ? wrap('BranchRef', { name: r.defaultBranch, sha: branchSha(r, r.defaultBranch) }) : null;
    if (name === 'viewerPermission') return 'ADMIN';
    if (name === 'hasIssuesEnabled') return true;
    if (name === 'description') return r.description;
    if (name === 'issue') { const x = r.issues.get(Number(args.number)); return x ? wrap('Issue', { r, issue: x }) : null; }
    if (name === 'issues') {
      let list = [...r.issues.values()];
      if (args.states?.length) list = list.filter((x) => args.states.map((s) => String(s).toLowerCase()).includes(x.state));
      const desc = args.orderBy?.direction === 'DESC';
      list.sort((a, b) => desc ? b.number - a.number : a.number - b.number);
      const after = args.after ? Number(decodeId(args.after).replace(/^cursor:/, '')) || 0 : 0;
      const first = Math.max(0, Math.min(1000, Number(args.first ?? list.length)));
      const sliced = list.slice(after, after + first);
      return wrap('IssueConnection', { r, items: sliced, offset: after, hasNextPage: after + first < list.length, totalCount: list.length });
    }
    if (name === 'pullRequests') {
      const list = [...r.pulls.values()].filter((p) => p.state === 'open');
      const first = Math.max(0, Math.min(1000, Number(args.first ?? list.length)));
      return wrap('PullConnection', { r, items: list.slice(0, first), hasNextPage: list.length > first, totalCount: list.length });
    }
    if (name === 'pullRequest') { const p = r.pulls.get(Number(args.number)); return p ? wrap('PullRequest', { r, pull: p }) : null; }
  }
  if (kind === 'BranchRef') return name === 'name' ? value.name : wrap('Commit', { sha: value.sha });
  if (kind === 'Issue') {
    const { r, issue } = value;
    return ({ id: globalId('Issue', r.id, issue.number), number: issue.number, title: issue.title, body: issue.body, state: issue.state.toUpperCase(), labels: issue.labels.map((x) => ({ __kind: 'Label', value: { name: x } })), url: `http://github.local/${r.owner}/${r.name}/issues/${issue.number}` })[name] ?? null;
  }
  if (kind === 'PullRequest') {
    const { r, pull } = value;
    if (name === 'files') return wrap('FileConnection', { r, items: diffFiles(r, branchSha(r, pull.base), branchSha(r, pull.head)).slice(0, Number(args.first || 100)) });
    return ({ id: globalId('PullRequest', r.id, pull.number), number: pull.number, title: pull.title, body: pull.body, headRefName: pull.head, baseRefName: pull.base, mergeable: pull.conflicted ? 'CONFLICTING' : 'MERGEABLE', state: pull.merged ? 'MERGED' : pull.state.toUpperCase(), merged: pull.merged })[name] ?? null;
  }
  if (kind === 'IssueConnection' || kind === 'PullConnection' || kind === 'FileConnection') {
    if (name === 'nodes') return value.items.map((x) => kind === 'IssueConnection' ? wrap('Issue', { r: value.r, issue: x }) : kind === 'PullConnection' ? wrap('PullRequest', { r: value.r, pull: x }) : wrap('PullFile', { file: x }));
    if (name === 'totalCount') return value.totalCount ?? value.items.length;
    if (name === 'pageInfo') return wrap('PageInfo', { hasNextPage: value.hasNextPage || false, endCursor: globalId('cursor', (value.offset || 0) + value.items.length) });
  }
  if (kind === 'PageInfo') return value[name] ?? null;
  if (kind === 'PullFile') return value.file[name === 'path' ? 'filename' : name] ?? null;
  if (kind === 'TypeInfo') return value[name] ?? null;
  if (kind === 'TypeField' || kind === 'TypeEnum') return value[name] ?? null;
  if (kind === 'Label') return value[name] ?? null;
  if (kind === 'CommentEdge') return name === 'node' ? wrap('Comment', value.node) : null;
  if (kind === 'Comment') return name === 'id' ? globalId('IssueComment', value.id) : value[name] ?? null;
  if (kind === 'Node') return value[name] ?? null;
  return null;
}
function projectGraphql(parent, fields, errors) {
  const out = {};
  for (const field of fields || []) {
    if (field.fragment) {
      if (!parent?.__kind || field.fragment === parent.__kind || (field.fragment === 'Repository' && parent.__kind === 'Repository')) Object.assign(out, projectGraphql(parent, field.fields, errors));
      continue;
    }
    const key = field.alias || field.name;
    const value = resolveField(parent, field, errors);
    if (Array.isArray(value)) out[key] = value.map((x) => field.fields ? projectGraphql(x, field.fields, errors) : x);
    else if (field.fields && value != null && typeof value === 'object') out[key] = projectGraphql(value, field.fields, errors);
    else out[key] = value === undefined ? null : value;
  }
  return out;
}
function rootField(field, operation, errors) {
  const name = field.name, args = field.args || {};
  if (operation === 'query') {
    if (name === 'viewer') return wrap('User', { login: primaryOwner || '', id: 1 });
    if (name === 'repository') {
      const r = resolveRepo(args.owner, args.name, false);
      return r ? wrap('Repository', r) : null;
    }
    if (name === 'node') {
      const decoded = decodeId(args.id);
      const [type, rid, number] = decoded.split(':');
      const r = lookupRepoById(rid);
      if (type === 'Repository' && r) return wrap('Repository', r);
      if (r && type === 'Issue') { const i = r.issues.get(Number(number)); if (i) return wrap('Issue', { r, issue: i }); }
      if (r && type === 'PullRequest') { const p = r.pulls.get(Number(number)); if (p) return wrap('PullRequest', { r, pull: p }); }
      return null;
    }
    if (name === '__type') return introspectionType(args.name);
    errors.push(`Cannot query field "${name}" on type "Query".`);
    return null;
  }
  const input = args.input || {};
  if (name === 'createIssue') {
    const r = lookupRepoById(input.repositoryId); if (!r) return null;
    return { __kind: 'MutationCreateIssue', value: { issue: createIssue(r, input) , r } };
  }
  if (name === 'closeIssue') {
    const decoded = decodeId(input.issueId), [, rid, num] = decoded.split(':');
    const r = lookupRepoById(rid), issue = r?.issues.get(Number(num));
    if (!r || !issue) return null; issue.state = 'closed';
    return { __kind: 'MutationCloseIssue', value: { issue, r } };
  }
  if (name === 'createPullRequest') {
    const r = lookupRepoById(input.repositoryId); if (!r) return null;
    const p = createPull(r, { head: input.headRefName, base: input.baseRefName, title: input.title, body: input.body });
    return p ? { __kind: 'MutationCreatePullRequest', value: { pullRequest: p, r } } : null;
  }
  if (name === 'mergePullRequest') {
    const decoded = decodeId(input.pullRequestId), [, rid, num] = decoded.split(':');
    const r = lookupRepoById(rid), pull = r?.pulls.get(Number(num));
    if (!r || !pull) return null;
    mergePull(r, pull);
    return { __kind: 'MutationMergePullRequest', value: { pullRequest: pull, r } };
  }
  if (name === 'addComment') {
    const decoded = decodeId(input.subjectId), [, rid, num] = decoded.split(':');
    const r = lookupRepoById(rid), issue = r?.issues.get(Number(num));
    if (!r || !issue) return null;
    const comment = { id: nextId++, body: String(input.body || '') };
    issue.comments.push(comment);
    return { __kind: 'MutationAddComment', value: { commentEdge: { node: comment } } };
  }
  errors.push(`Cannot query field "${name}" on type "Mutation".`);
  return null;
}
function projectMutation(parent, field, errors) {
  const { __kind: kind, value } = parent;
  if (kind === 'MutationCreateIssue') {
    if (field.name !== 'issue') { errors.push(`Cannot query field "${field.name}" on type "CreateIssuePayload".`); return null; }
    return wrap('Issue', { r: value.r, issue: value.issue });
  }
  if (kind === 'MutationCloseIssue') {
    if (field.name !== 'issue') return null;
    return wrap('Issue', { r: value.r, issue: value.issue });
  }
  if (kind === 'MutationCreatePullRequest' || kind === 'MutationMergePullRequest') {
    if (field.name !== 'pullRequest') return null;
    return wrap('PullRequest', { r: value.r, pull: value.pullRequest });
  }
  if (kind === 'MutationAddComment') return field.name === 'commentEdge' ? { __kind: 'CommentEdge', value: value.commentEdge } : null;
  if (kind === 'CommentEdge') return field.name === 'node' ? value.node : null;
  if (kind === 'Comment') return value[field.name] ?? null;
  return resolveField(parent, field, errors);
}
function executeGraphql(doc, variables = {}) {
  try {
    const ast = parseGraphql(doc, variables), errors = [], data = {};
    for (const field of ast.fields) {
      const key = field.alias || field.name;
      if (ast.operation === 'query') {
        const value = rootField(field, 'query', errors);
        data[key] = field.fields && value != null ? projectGraphql(value, field.fields, errors) : value;
      } else {
        const value = rootField(field, 'mutation', errors);
        data[key] = field.fields && value != null ? field.fields.reduce((o, f) => {
          if (f.fragment) { Object.assign(o, projectGraphql(value, f.fields, errors)); return o; }
          const v = projectMutation(value, f, errors);
          o[f.alias || f.name] = f.fields && v != null ? projectGraphql(v, f.fields, errors) : v;
          return o;
        }, {}) : value;
      }
    }
    return { data, ...(errors.length ? { errors: errors.map((message) => ({ message })) } : {}) };
  } catch (e) {
    return { data: null, errors: [{ message: e instanceof Error ? e.message : String(e) }] };
  }
}
async function handleGraphql(req, res) {
  if (!reqAuth(req)) return error(res, 401, 'Requires authentication');
  const parsed = await jsonBody(req);
  if (parsed.bad) return error(res, 400, 'Problems parsing JSON');
  const body = parsed.value;
  if (Array.isArray(body)) return sendJson(res, 200, body.map((x) => executeGraphql(x.query || '', x.variables || {})));
  if (!body || typeof body.query !== 'string') return sendJson(res, 200, { data: null, errors: [{ message: 'query is required' }] });
  return sendJson(res, 200, executeGraphql(body.query, body.variables || {}));
}

const RECEIVE_CAPS = 'report-status side-band-64k delete-refs ofs-delta thin-pack shallow multi_ack_detailed agent=git/2.43.0 object-format=sha1';
function v0Advertisement(repo, service) {
  const out = [pkt(`# service=${service}\n`), flush()];
  const refs = refsFor(repo);
  if (!refs.length) out.push(pkt(`${ZERO} capabilities^{}\0${RECEIVE_CAPS} symref=HEAD:refs/heads/${repo.defaultBranch}\n`));
  else {
    const head = repo.refs.get(`refs/heads/${repo.defaultBranch}`) || refs[0][1];
    out.push(pkt(`${head} HEAD\0${RECEIVE_CAPS} symref=HEAD:refs/heads/${repo.defaultBranch}\n`));
    for (const [ref, sha] of refs) {
      out.push(pkt(`${sha} ${ref}\n`));
      if (ref.startsWith('refs/tags/')) {
        const obj = repo.objects.get(sha);
        const target = obj?.type === 'tag' ? obj.data.toString().match(/^object ([0-9a-f]{40})/m)?.[1] : null;
        if (target) out.push(pkt(`${target} ${ref}^{}\n`));
      }
    }
  }
  out.push(flush());
  return Buffer.concat(out);
}
function v2Advertisement() {
  return packetLines(['version 2\n', 'agent=git/2.43.0\n', 'ls-refs=unborn\n', 'fetch=shallow wait-for-done\n', 'object-format=sha1\n', 'server-option\n', 'object-info\n', null]);
}
function v2LsRefs(repo, lines) {
  const prefixes = lines.filter((x) => x.startsWith('ref-prefix ')).map((x) => x.slice(11).trim());
  const symrefs = lines.includes('symrefs');
  const peel = lines.includes('peel');
  const out = [];
  const match = (ref) => prefixes.length === 0 || prefixes.some((p) => ref.startsWith(p));
  const refs = refsFor(repo);
  const headSha = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
  if (symrefs && prefixes.length === 0) {
    if (headSha) out.push(`${headSha} HEAD symref-target:refs/heads/${repo.defaultBranch}\n`);
    else out.push(`unborn HEAD symref-target:refs/heads/${repo.defaultBranch}\n`);
  }
  for (const [ref, sha] of refs) {
    if (!match(ref)) continue;
    let line = `${sha} ${ref}`;
    if (peel && ref.startsWith('refs/tags/')) {
      const obj = repo.objects.get(sha), target = obj?.type === 'tag' ? obj.data.toString().match(/^object ([0-9a-f]{40})/m)?.[1] : null;
      if (target) line += ` peeled:${target}`;
    }
    out.push(`${line}\n`);
  }
  return packetLines([...out, null]);
}
function fetchObjects(repo, wants, haves, depth, shallow) {
  const bases = reachable(repo, haves, 0, shallow);
  const target = reachable(repo, wants, depth || 0, []);
  const send = [];
  for (const sha of target.found) if (!bases.found.has(sha)) {
    const obj = repo.objects.get(sha);
    if (obj) send.push(obj);
  }
  const oldBoundaries = shallow || [];
  const newBoundaries = target.shallow;
  const unshallow = oldBoundaries.filter((x) => !newBoundaries.includes(x));
  return { pack: writePack(send), shallow: newBoundaries, unshallow };
}
function sidebandPack(pack) {
  const result = [pkt('packfile\n')];
  const max = 60000;
  for (let i = 0; i < pack.length; i += max) result.push(pkt(Buffer.concat([Buffer.from([1]), pack.subarray(i, i + max)])));
  result.push(flush());
  return Buffer.concat(result);
}
function processV2Fetch(repo, packets) {
  let command = '', afterDelim = false;
  const args = [];
  for (const packet of packets) {
    if (packet === 'delim') { afterDelim = true; continue; }
    if (!Buffer.isBuffer(packet)) continue;
    const line = packet.toString('utf8').replace(/\n$/, '');
    if (line.startsWith('command=')) command = line.slice(8);
    else if (afterDelim) args.push(line);
  }
  if (command === 'ls-refs') return v2LsRefs(repo, args);
  if (command !== 'fetch') return packetLines(['acknowledgments\n', 'NAK\n', null]);
  const wants = args.filter((x) => x.startsWith('want ')).map((x) => x.slice(5));
  const haves = args.filter((x) => x.startsWith('have ')).map((x) => x.slice(5));
  const shallow = args.filter((x) => x.startsWith('shallow ')).map((x) => x.slice(8));
  const depthLine = args.find((x) => x.startsWith('deepen '));
  const depth = depthLine ? Math.max(1, Number(depthLine.slice(7)) || 1) : 0;
  if (!wants.length) return packetLines(['acknowledgments\n', 'NAK\n', null]);
  const f = fetchObjects(repo, wants, haves, depth, shallow);
  const sections = [pkt('acknowledgments\n'), pkt('NAK\n'), flush()];
  if (depth || shallow.length) {
    sections.push(pkt('shallow-info\n'));
    for (const sha of f.shallow) sections.push(pkt(`shallow ${sha}\n`));
    for (const sha of f.unshallow) sections.push(pkt(`unshallow ${sha}\n`));
    sections.push(flush());
  }
  sections.push(sidebandPack(f.pack));
  return Buffer.concat(sections);
}
function processV0Fetch(repo, packets) {
  const lines = packets.filter(Buffer.isBuffer).map((x) => x.toString('utf8').replace(/\0.*$/, '').replace(/\n$/, ''));
  const wants = lines.filter((x) => x.startsWith('want ')).map((x) => x.slice(5).split(' ')[0]);
  const haves = lines.filter((x) => x.startsWith('have ')).map((x) => x.slice(5));
  const shallow = lines.filter((x) => x.startsWith('shallow ')).map((x) => x.slice(8));
  const depthLine = lines.find((x) => x.startsWith('deepen '));
  const depth = depthLine ? Number(depthLine.slice(7)) || 1 : 0;
  const f = fetchObjects(repo, wants, haves, depth, shallow);
  const out = [];
  for (const sha of f.shallow) out.push(pkt(`shallow ${sha}\n`));
  for (const sha of f.unshallow) out.push(pkt(`unshallow ${sha}\n`));
  out.push(pkt('NAK\n'));
  for (let i = 0; i < f.pack.length; i += 60000) out.push(pkt(Buffer.concat([Buffer.from([1]), f.pack.subarray(i, i + 60000)])));
  out.push(flush());
  return Buffer.concat(out);
}
function applyReceive(repo, packetData, packBytes) {
  const commands = [];
  for (const lineBuf of packetData) {
    if (!Buffer.isBuffer(lineBuf)) continue;
    const line = lineBuf.toString('utf8').split('\0', 1)[0].split('\n', 1)[0].trim();
    const m = line.match(/^([0-9a-f]{40}) ([0-9a-f]{40}) (.+)$/i);
    if (m) commands.push({ old: m[1].toLowerCase(), next: m[2].toLowerCase(), ref: m[3] });
  }
  let unpackOk = true;
  try { if (packBytes.length) for (const [sha, o] of parsePack(packBytes, repo)) repo.objects.set(sha, o); }
  catch { unpackOk = false; }
  const lines = [`unpack ${unpackOk ? 'ok' : 'error'}\n`];
  for (const c of commands) {
    if (!unpackOk) { lines.push(`ng ${c.ref} unpacker error\n`); continue; }
    const current = repo.refs.get(c.ref) || ZERO;
    if (current !== c.old) { lines.push(`ng ${c.ref} stale info\n`); continue; }
    if (c.next === ZERO) {
      repo.refs.delete(c.ref);
      if (c.ref.startsWith('refs/heads/')) repo.refFiles.delete(c.ref.slice(11));
      lines.push(`ok ${c.ref}\n`);
      continue;
    }
    const obj = repo.objects.get(c.next);
    if (!obj) { lines.push(`ng ${c.ref} missing object\n`); continue; }
    if (c.ref.startsWith('refs/heads/') && current !== ZERO && !isAncestor(repo, current, c.next)) {
      lines.push(`ng ${c.ref} non-fast-forward\n`); continue;
    }
    repo.refs.set(c.ref, c.next);
    if (c.ref.startsWith('refs/heads/')) {
      updateBranchFiles(repo, c.ref, c.next);
      if (repo.refs.size === 1 && current === ZERO) repo.defaultBranch = c.ref.slice(11);
      if (!primaryOwner) primaryOwner = repo.owner || '';
    }
    lines.push(`ok ${c.ref}\n`);
  }
  const report = packetLines(lines.concat([null]));
  return Buffer.concat([pkt(Buffer.concat([Buffer.from([1]), report])), flush()]);
}
async function handleGit(req, res, url) {
  if (!reqAuth(req)) return sendRaw(res, 401, Buffer.from('Unauthorized'), 'text/plain');
  const path = url.pathname.split('/').filter(Boolean);
  if (path.length < 2 || !path[1].endsWith('.git')) return sendRaw(res, 404, Buffer.from('Not Found'), 'text/plain');
  const owner = decodeURIComponent(path[0]), name = decodeURIComponent(path[1].slice(0, -4));
  const repo = resolveRepo(owner, name, true);
  if (!repo) return sendRaw(res, 404, Buffer.from('Not Found'), 'text/plain');
  const operation = path.slice(2).join('/');
  if (operation === 'info/refs' && req.method === 'GET') {
    const service = url.searchParams.get('service');
    if (service !== 'git-upload-pack' && service !== 'git-receive-pack') return sendRaw(res, 400, Buffer.from('Invalid service'), 'text/plain');
    const isV2 = service === 'git-upload-pack' && String(req.headers['git-protocol'] || '').includes('version=2');
    const body = isV2 ? v2Advertisement() : v0Advertisement(repo, service);
    return sendRaw(res, 200, body, `application/x-${service}-advertisement`, { 'cache-control': 'no-cache', pragma: 'no-cache' });
  }
  if (operation === 'git-upload-pack' && req.method === 'POST') {
    const body = await readBody(req);
    const parsed = readPackets(body, 0, false);
    const isV2 = String(req.headers['git-protocol'] || '').includes('version=2');
    let result;
    try { result = isV2 ? processV2Fetch(repo, parsed.packets) : processV0Fetch(repo, parsed.packets); }
    catch { result = Buffer.alloc(0); }
    return sendRaw(res, 200, result, 'application/x-git-upload-pack-result', { 'cache-control': 'no-cache' });
  }
  if (operation === 'git-receive-pack' && req.method === 'POST') {
    const body = await readBody(req);
    const parsed = readPackets(body);
    const pack = body.subarray(parsed.offset);
    const result = applyReceive(repo, parsed.packets, pack);
    return sendRaw(res, 200, result, 'application/x-git-receive-pack-result', { 'cache-control': 'no-cache' });
  }
  return sendRaw(res, 404, Buffer.from('Not Found'), 'text/plain');
}

const MCP_TOOLS = [
  { name: 'create_repo', description: 'Create a repository in the in-memory forge.', inputSchema: { type: 'object', properties: { name: { type: 'string' }, owner: { type: 'string' }, description: { type: 'string' }, private: { type: 'boolean' } }, required: ['name'] } },
  { name: 'get_repo', description: 'Read a repository by owner and name.', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' } }, required: ['owner', 'repo'] } },
  { name: 'create_issue', description: 'Create an issue in a repository.', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, body: { type: 'string' } }, required: ['owner', 'repo', 'title'] } },
  { name: 'list_issues', description: 'List repository issues, optionally filtered by state.', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, state: { type: 'string' } }, required: ['owner', 'repo'] } },
  { name: 'create_pull_request', description: 'Open a pull request between two branches.', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, title: { type: 'string' }, head: { type: 'string' }, base: { type: 'string' }, body: { type: 'string' } }, required: ['owner', 'repo', 'title', 'head', 'base'] } },
  { name: 'merge_pull_request', description: 'Squash merge an open pull request.', inputSchema: { type: 'object', properties: { owner: { type: 'string' }, repo: { type: 'string' }, pull_number: { type: 'integer' } }, required: ['owner', 'repo', 'pull_number'] } },
];
function rpcError(id, code, message) { return { jsonrpc: '2.0', id: id ?? null, error: { code, message } }; }
function mcpResult(id, value, isError = false) {
  const text = JSON.stringify(value);
  return { jsonrpc: '2.0', id, result: { content: [{ type: 'text', text }], structuredContent: value, ...(isError ? { isError: true } : {}) } };
}
function callMcpTool(name, args) {
  const normalized = String(name || '').toLowerCase().replace(/[^a-z0-9]/g, '');
  const tool = MCP_TOOLS.find((x) => normalized === x.name.replace(/_/g, '') || normalized.endsWith(x.name.replace(/_/g, '')));
  if (!tool) return { error: rpcError(null, -32602, `Unknown tool: ${name}`) };
  const required = tool.inputSchema.required || [];
  const missing = required.filter((k) => args[k] === undefined || args[k] === null || args[k] === '');
  if (missing.length) return { result: mcpResult(null, { message: `Missing required arguments: ${missing.join(', ')}` }, true) };
  if (tool.name === 'create_repo') {
    const r = makeRepo(args.name, args.owner || null, args);
    if (args.owner) primaryOwner = primaryOwner || String(args.owner);
    return { result: mcpResult(null, repoJson(r)) };
  }
  const r = resolveRepo(args.owner, args.repo, true);
  if (!r) return { result: mcpResult(null, { message: 'Not Found' }, true) };
  if (tool.name === 'get_repo') return { result: mcpResult(null, repoJson(r)) };
  if (tool.name === 'create_issue') return { result: mcpResult(null, issueJson(r, createIssue(r, args))) };
  if (tool.name === 'list_issues') {
    const state = String(args.state || 'open').toLowerCase();
    return { result: mcpResult(null, [...r.issues.values()].filter((x) => state === 'all' || x.state === state).map((x) => issueJson(r, x))) };
  }
  if (tool.name === 'create_pull_request') {
    const p = createPull(r, args);
    return p ? { result: mcpResult(null, pullJson(r, p)) } : { result: mcpResult(null, { message: 'Head or base branch not found' }, true) };
  }
  if (tool.name === 'merge_pull_request') {
    const p = r.pulls.get(Number(args.pull_number));
    if (!p) return { result: mcpResult(null, { message: 'Not Found' }, true) };
    const merged = mergePull(r, p);
    return { result: mcpResult(null, { ...merged.body, number: p.number, merged: p.merged }) };
  }
  return { error: rpcError(null, -32602, `Unknown tool: ${name}`) };
}
async function handleMcp(req, res) {
  let parsed;
  try { parsed = await jsonBody(req); } catch { parsed = { bad: true }; }
  if (parsed.bad) return sendJson(res, 400, rpcError(null, -32700, 'Parse error'));
  const request = parsed.value;
  if (!request || typeof request !== 'object') return sendJson(res, 400, rpcError(null, -32700, 'Parse error'));
  if (!reqAuth(req)) return sendJson(res, 401, { message: 'Requires authentication' });
  const id = request.id;
  const method = String(request.method || '');
  if (method === 'notifications/initialized' || (method.startsWith('notifications/') && id === undefined)) {
    res.writeHead(202, { 'content-length': '0' }); return res.end();
  }
  if (method === 'server/discover') return sendJson(res, 200, { jsonrpc: '2.0', id, result: { resultType: 'discover', supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'], capabilities: { tools: { listChanged: false } }, serverInfo: { name: 'github-core-forge', version: '1.0.0' } } });
  if (method === 'initialize') {
    const p = request.params || {};
    return sendJson(res, 200, { jsonrpc: '2.0', id, result: { protocolVersion: p.protocolVersion || '2025-11-25', capabilities: { tools: { listChanged: false } }, serverInfo: { name: 'github-core-forge', version: '1.0.0' } } }, { 'mcp-session-id': 'forge-session' });
  }
  if (method === 'tools/list') return sendJson(res, 200, { jsonrpc: '2.0', id, result: { tools: MCP_TOOLS } });
  if (method === 'tools/call') {
    const params = request.params || {};
    const answer = callMcpTool(params.name, params.arguments || {});
    if (answer.error) { answer.error.id = id ?? null; return sendJson(res, 200, answer.error); }
    answer.result.id = id;
    return sendJson(res, 200, answer.result);
  }
  return sendJson(res, 200, rpcError(id, -32601, 'Method not found'));
}

const server = createServer((req, res) => {
  const url = new URL(req.url || '/', 'http://forge.local');
  const path = url.pathname;
  const run = async () => {
    if (req.method === 'GET' && path === '/healthz') return sendJson(res, 200, { ok: true });
    if (path === '/mcp' && req.method === 'POST') return handleMcp(req, res);
    if (path === '/api/graphql' && req.method === 'POST') return handleGraphql(req, res);
    if (path === '/api/v3' || path.startsWith('/api/v3/')) return handleRest(req, res, url);
    const parts = path.split('/').filter(Boolean);
    if (parts.length >= 2 && parts[1].endsWith('.git')) return handleGit(req, res, url);
    return sendJson(res, 404, { message: 'Not Found' });
  };
  run().catch((e) => {
    if (res.headersSent) { res.destroy(); return; }
    if ((req.url || '').startsWith('/api/')) error(res, 500, e instanceof Error ? e.message : 'Internal Server Error');
    else sendRaw(res, 500, Buffer.from('Internal Server Error'), 'text/plain');
  });
});

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
async function register(port) {
  for (;;) {
    try {
      const response = await fetch(`${ENV_URL}/register`, { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ port }), signal: AbortSignal.timeout(30000) });
      if (response.status === 200 || response.status === 409) return;
      if (response.status === 400 || response.status === 405) throw new Error(`register failed: HTTP ${response.status}`);
    } catch (e) {
      if (e instanceof Error && e.message.startsWith('register failed:')) throw e;
    }
    await sleep(500);
  }
}
async function waitForDone() {
  while (true) {
    try {
      const response = await fetch(`${ENV_URL}/done`, { signal: AbortSignal.timeout(30000) });
      if (response.ok && (await response.json()).done === true) return;
    } catch {}
    await sleep(250);
  }
}
async function main() {
  if (!ENV_URL) throw new Error('MAKEFUN_ENV_URL is not set');
  await new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, () => resolve());
  });
  const address = server.address();
  await register(address.port);
  await waitForDone();
  await new Promise((resolve) => server.close(resolve));
}
main().then(() => process.exit(0), (e) => {
  process.stderr.write(`[entry] ${e instanceof Error ? e.message : String(e)}\n`);
  process.exit(1);
});
