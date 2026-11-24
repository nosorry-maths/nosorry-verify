// Trusted setup of a REPOSITORY submission (runs as the runner's account, with network, before any submitted code):
//   * fetch the repository at the exact commit, as data; delete any compiled file it ships (.lake, *.olean…);
//   * require a declarative lakefile.toml (a lakefile.lean is Lean code that Lake would run) and a valid lean-toolchain;
//   * check every dependency of lake-manifest.json against an allowlist, then fetch each at its exact revision;
//   * install the repository's toolchain, fetch Mathlib's prebuilt cache, compute LEAN_PATH and the library roots.
// Writes $NV/workspace.env. Nothing of the repository is executed here.
import fs from "node:fs";
import path from "node:path";
import { execFileSync } from "node:child_process";

const NV = process.env.NV ?? "/opt/nv";
const REPO = path.join(NV, "repo");
const plan = JSON.parse(fs.readFileSync(path.join(NV, "in", "plan.json"), "utf8"));
const r = plan.repo ?? {};
const die = (m) => { fs.writeFileSync(path.join(NV, "out", "setup-error.txt"), m); console.log("REFUSED:", m); process.exit(0); };
const sh = (cmd, args, opts = {}) => execFileSync(cmd, args, { stdio: ["ignore", "pipe", "pipe"], encoding: "utf8", maxBuffer: 256 << 20, ...opts });

if (!/^https:\/\/github\.com\/[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+?(\.git)?$/.test(r.url ?? "")) die("repository url must be https://github.com/<owner>/<repo>");
if (!/^[0-9a-f]{40}$/.test(r.commit ?? "")) die("commit must be a full 40-character hash");
if (!/^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$/.test(r.module ?? "")) die("module must be a Lean module name such as MyProof.Main");

// Dependencies may only come from these sources (their lakefiles run during the cache fetch and the build).
const ALLOWED_DEPS = [/^https:\/\/github\.com\/leanprover-community\//, /^https:\/\/github\.com\/leanprover\//, /^https:\/\/github\.com\/google-deepmind\/formal-conjectures(\.git)?$/];

// 1. the repository, as data
fs.mkdirSync(REPO, { recursive: true });
sh("git", ["init", "-q", REPO]);
try { sh("git", ["-C", REPO, "fetch", "-q", "--depth", "1", r.url, r.commit]); } catch (e) { die(`cannot fetch ${r.url} at ${r.commit}: ${String(e.stderr ?? e.message).slice(0, 300)}`); }
sh("git", ["-C", REPO, "checkout", "-q", "--detach", "FETCH_HEAD"]);
const sizeMb = Number(sh("du", ["-sm", "--exclude=.git", REPO]).split(/\s/)[0]);
if (sizeMb > 1024) die(`repository too large (${sizeMb} MB of sources; at most 1 GB)`);
// never trust compiled files shipped with the sources
sh("find", [REPO, "-path", `${REPO}/.git`, "-prune", "-o", "(", "-name", ".lake", "-o", "-name", "*.olean", "-o", "-name", "*.olean.*", "-o", "-name", "*.ilean", "-o", "-name", "*.ir", ")", "-prune", "-exec", "rm", "-rf", "{}", "+"]);
if (fs.existsSync(path.join(REPO, "lakefile.lean"))) die("lakefile.lean is not accepted (Lake would run it): use a lakefile.toml");
if (!fs.existsSync(path.join(REPO, "lakefile.toml"))) die("no lakefile.toml at the repository root");
const tc = fs.existsSync(path.join(REPO, "lean-toolchain")) ? fs.readFileSync(path.join(REPO, "lean-toolchain"), "utf8").trim() : "";
if (!/^leanprover\/lean4:v4\.\d+\.\d+(-rc\d+)?$/.test(tc)) die(`lean-toolchain must name a Lean 4 release (got "${tc.slice(0, 60)}")`);

// 2. dependencies, checked then fetched at their exact revisions
let manifest;
try { manifest = JSON.parse(fs.readFileSync(path.join(REPO, "lake-manifest.json"), "utf8")); } catch { die("lake-manifest.json missing or unreadable (run `lake update` and commit it)"); }
const pkgs = manifest.packages ?? [];
const pkgDir = manifest.packagesDir ?? ".lake/packages";
if (!/^[\w./-]+$/.test(pkgDir) || pkgDir.includes("..")) die("odd packagesDir in lake-manifest.json");
if (!pkgs.some((p) => /google-deepmind\/formal-conjectures/.test(p.url ?? ""))) die("the repository must depend on formal-conjectures (nosorry statements import FormalConjecturesUtil)");
for (const p of pkgs) {
  if (p.type !== "git") die(`dependency ${p.name}: only git dependencies are accepted`);
  if (!ALLOWED_DEPS.some((re) => re.test(p.url ?? ""))) die(`dependency ${p.name} (${p.url}) is not from an accepted source (leanprover-community, leanprover, formal-conjectures)`);
  if (!/^[0-9a-f]{40}$/.test(p.rev ?? "")) die(`dependency ${p.name}: rev must be a full hash`);
  if (!/^[\w.-]+$/.test(p.name ?? "")) die("odd package name in lake-manifest.json");
  const d = path.join(REPO, pkgDir, p.name);
  fs.mkdirSync(d, { recursive: true });
  sh("git", ["init", "-q", d]);
  sh("git", ["-C", d, "fetch", "-q", "--depth", "1", p.url, p.rev]);
  sh("git", ["-C", d, "checkout", "-q", "--detach", "FETCH_HEAD"]);
  console.log(`dependency ${p.name} @ ${p.rev.slice(0, 8)}`);
}

// 3. toolchain, Mathlib cache, paths
const ELAN = path.join(NV, "elan");
const env = { ...process.env, ELAN_HOME: ELAN, PATH: `${ELAN}/bin:${process.env.PATH}` };
if (!fs.existsSync(path.join(ELAN, "bin", "elan"))) sh("sh", ["-c", "curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none"], { env });
sh(path.join(ELAN, "bin", "elan"), ["toolchain", "install", tc], { env });
sh(path.join(ELAN, "bin", "elan"), ["default", tc], { env });
const TC_BIN = path.dirname(sh(path.join(ELAN, "bin", "elan"), ["which", "lake"], { env, cwd: REPO }).trim());
try { console.log(sh("lake", ["exe", "cache", "get"], { env, cwd: REPO }).split("\n").slice(-3).join("\n")); }
catch (e) { console.log("Mathlib cache: not available for this repository (", String(e.stderr ?? e.message).split("\n").slice(-2).join(" "), ")"); }
const LEAN_PATH = sh(path.join(TC_BIN, "lake"), ["env", "printenv", "LEAN_PATH"], { env, cwd: REPO }).trim();

// library roots of the repository (its own modules, replayed in the kernel), from [[lean_lib]] name / roots
const toml = fs.readFileSync(path.join(REPO, "lakefile.toml"), "utf8");
const roots = new Set();
for (const block of toml.split(/^\s*\[\[/m).slice(1)) {
  if (!/^lean_lib\]\]/.test(block)) continue;
  const name = block.match(/^\s*name\s*=\s*"([^"]+)"/m)?.[1];
  const rs = block.match(/^\s*roots\s*=\s*\[([^\]]*)\]/m)?.[1];
  const list = rs ? [...rs.matchAll(/[`"]([A-Za-z0-9_.']+)[`"]?/g)].map((m) => m[1]) : name ? [name] : [];
  for (const x of list) roots.add(x.split(".")[0]);
}
if (!roots.size) die("no [[lean_lib]] in lakefile.toml");
if (!roots.has(r.module.split(".")[0])) die(`module ${r.module} is not in the repository's libraries (${[...roots].join(", ")})`);
// A library may not take the name of a dependency's modules (it would shadow them).
const RESERVED = /^(Mathlib|FormalConjectures|FormalConjecturesUtil|FormalConjecturesForMathlib|Batteries|Aesop|Qq|ProofWidgets|Plausible|LeanSearchClient|ImportGraph|Lean|Init|Std|Lake|Challenge|Compare|Solution)$/;
for (const x of roots) if (RESERVED.test(x)) die(`library root ${x} is reserved (it is the name of a dependency or of the checker)`);

// 4. trusted build of the dependencies the statement and the proof rely on (allowlisted code only, before any submitted
//    code runs): Mathlib (replays its cache and writes the trace files Lake wants), formal-conjectures' utilities, and
//    the modules the reference statement imports. Afterwards the dependencies are read-only for the sandboxed build.
const chalImports = [...fs.readFileSync(path.join(NV, "in", "Challenge.lean"), "utf8").matchAll(/^\s*import\s+([\w.«»]+)/gm)].map((m) => m[1]);
const targets = [...new Set(["Mathlib", "FormalConjecturesUtil", "FormalConjecturesForMathlib", ...chalImports])];
try { console.log(sh(path.join(TC_BIN, "lake"), ["build", ...targets], { env, cwd: REPO, timeout: 4 * 3600_000 }).split("\n").slice(-3).join("\n")); }
catch (e) { die(`the dependencies do not build with ${tc}: ${String(e.stdout ?? e.message).split("\n").slice(-12).join("\n").slice(0, 1500)}`); }
// LEAN_PATH without the repository's own build directory: the reference statement never sees submitted modules.
const repoBuild = path.join(REPO, ".lake", "build");
const LEAN_PATH_PKGS = LEAN_PATH.split(":").filter((p) => p && !p.startsWith(repoBuild)).join(":");

fs.writeFileSync(path.join(NV, "workspace.env"), [
  `TC_BIN=${TC_BIN}`, `LEAN_PATH_BASE=${LEAN_PATH}`, `LEAN_PATH_PKGS=${LEAN_PATH_PKGS}`, `TOOLCHAIN=${tc}`, `FC_REV=${pkgs.find((p) => /formal-conjectures/.test(p.url)).rev}`,
  `REPO_DIR=${REPO}`, `REPLAY_ROOTS=${[...roots].join(",")}`, `PKG_DIR=${path.join(REPO, pkgDir)}`,
].join("\n") + "\n");
sh("chmod", ["-R", "a+rX", NV]);
console.log(`repository ready: ${tc}, libraries ${[...roots].join(", ")}, ${pkgs.length} dependencies`);
