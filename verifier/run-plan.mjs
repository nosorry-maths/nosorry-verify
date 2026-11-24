// Runs the Lean stages of one nosorry verification, as the worker does locally (worker/worker.mjs), and writes
// $NV/out/result.json. It runs as the runner's account; every Lean command runs as the unprivileged `outsider`
// account in a transient systemd service: no network, read-only system, write access to its own out/ only, memory and
// time limits, every leftover process killed when it ends. Nothing the submission prints reaches the job log: outputs
// are captured into the result.
//
// The plan comes from the job branch and is DATA: only validated parameters are taken from it, never commands.
import fs from "node:fs";
import path from "node:path";
import { spawnSync } from "node:child_process";

const NV = process.env.NV ?? "/opt/nv";
const IN = path.join(NV, "in"), OUT = path.join(NV, "out"), JOB = path.join(NV, "job");
const env = Object.fromEntries(fs.readFileSync(path.join(NV, "workspace.env"), "utf8").split("\n").filter(Boolean).map((l) => [l.slice(0, l.indexOf("=")), l.slice(l.indexOf("=") + 1)]));
const TC = env.TC_BIN, BASE = env.LEAN_PATH_BASE;
fs.mkdirSync(OUT, { recursive: true });

const result = { nonce: null, stages: {}, toolchain: env.TOOLCHAIN, fc_rev: env.FC_REV, error: null };
const save = () => fs.writeFileSync(path.join(OUT, "result.json"), JSON.stringify(result));

function fail(msg) { result.error = msg; save(); console.log("plan refused or failed:", msg); process.exit(0); }

let plan;
try { plan = JSON.parse(fs.readFileSync(path.join(IN, "plan.json"), "utf8")); } catch { fail("plan.json missing or unreadable"); }
const NAME = /^[A-Za-z_À-ɏͰ-Ͽ«][A-Za-z0-9_'!?.À-ɏͰ-Ͽ₀-ₜ«»]{0,300}$/u;
if (typeof plan.nonce !== "string" || !/^[a-f0-9]{32}$/.test(plan.nonce)) fail("bad nonce");
result.nonce = plan.nonce;
if (!["proof", "disproof", "partial", "finding", "formalization"].includes(plan.kind)) fail("bad kind");
if (typeof plan.target !== "string" || !NAME.test(plan.target)) fail("bad target");
if (plan.metric_decl != null && (typeof plan.metric_decl !== "string" || !NAME.test(plan.metric_decl))) fail("bad metric_decl");
const isFormalization = plan.kind === "formalization";
if (!fs.existsSync(path.join(IN, "Challenge.lean"))) fail("Challenge.lean missing");
if (!isFormalization && !fs.existsSync(path.join(IN, "Solution.lean"))) fail("Solution.lean missing");

// Same layout as the local worker: ref/ (reference), sub/ (the untrusted submission), chk/ (checker, read-only).
const dirs = {};
for (const d of ["ref", "sub", "chk"]) {
  dirs[d] = path.join(JOB, d);
  fs.mkdirSync(path.join(dirs[d], "src"), { recursive: true });
  fs.mkdirSync(path.join(dirs[d], "out"), { recursive: true });
}
fs.copyFileSync(path.join(IN, "Challenge.lean"), path.join(dirs.ref, "src", "Challenge.lean"));
if (!isFormalization) fs.copyFileSync(path.join(IN, "Solution.lean"), path.join(dirs.sub, "src", "Solution.lean"));
fs.copyFileSync(path.join(NV, "base", "verifier", "Compare.lean"), path.join(dirs.chk, "src", "Compare.lean"));
spawnSync("chmod", ["-R", "a+rX", JOB]);
// Only ref/out and sub/out are writable by the sandbox account.
for (const d of ["ref", "sub"]) spawnSync("sudo", ["chown", "outsider:outsider", path.join(dirs[d], "out")]);

const memTotalKb = Number(fs.readFileSync("/proc/meminfo", "utf8").match(/MemTotal:\s+(\d+)/)[1]);
const MEM_MAX = `${Math.max(6 * 1024 * 1024, memTotalKb - 3 * 1024 * 1024)}K`; // leave 3 GB to the runner itself

/** One Lean command in a throwaway, locked-down systemd service. */
function lean(stage, dir, tool, args, timeoutSec, { writable = false } = {}) {
  const t0 = Date.now();
  const unit = `nv-${stage}-${process.pid}`;
  const props = [
    "User=outsider", "Group=outsider", "PrivateNetwork=yes", "PrivateTmp=yes", "NoNewPrivileges=yes",
    "ProtectSystem=strict", "ProtectHome=tmpfs", "ProtectKernelTunables=yes", "ProtectControlGroups=yes",
    "RestrictSUIDSGID=yes", "LockPersonality=yes", "TasksMax=256", `MemoryMax=${MEM_MAX}`, `RuntimeMaxSec=${timeoutSec}`,
    `WorkingDirectory=${dir}`, ...(writable ? [`ReadWritePaths=${path.join(dir, "out")}`] : []),
  ].flatMap((p) => ["-p", p]);
  const leanPath = `${BASE}:${path.join(dir, "out")}`;
  const envs = [`LEAN_PATH=${leanPath}`, `PATH=${TC}:/usr/bin:/bin`, "HOME=/tmp", `NOSORRY_LEAN=${TC}/lean`, "NOSORRY_TMP=/tmp", "LANG=C.UTF-8"]
    .flatMap((e) => ["-E", e]);
  // Without --quiet, systemd-run ends with a summary on its stderr (runtime, CPU, "Memory peak: …"): kept as telemetry,
  // removed from the stage output.
  const r = spawnSync("sudo", ["systemd-run", "--wait", "--pipe", "--collect", `--unit=${unit}`, ...props, ...envs, path.join(TC, tool), ...args],
    { encoding: "utf8", maxBuffer: 64 * 1024 * 1024, stdio: ["ignore", "pipe", "pipe"] });
  spawnSync("sudo", ["pkill", "-KILL", "-u", "outsider"]);
  const ms = Date.now() - t0;
  const SUMMARY = /^(Running as unit|Finished with result|Main processes terminated|Service runtime|CPU time consumed|Memory peak|Memory swap peak|IP traffic|IO bytes)\b/;
  const errLines = (r.stderr ?? "").split("\n");
  const memPeak = errLines.filter((l) => /^Memory peak:/.test(l)).pop()?.replace(/^Memory peak:\s*/, "") ?? null;
  const swapPeak = errLines.filter((l) => /^Memory swap peak:/.test(l)).pop()?.replace(/^Memory swap peak:\s*/, "") ?? null;
  const stderr = errLines.filter((l) => !SUMMARY.test(l)).join("\n");
  // The worker reads the checker's verdict from the LAST line of stdout (one JSON object, possibly long): keep it whole,
  // and only the tail of the rest.
  const so = (r.stdout ?? "").replace(/\n+$/, "");
  const cut = so.lastIndexOf("\n");
  const lastLine = so.slice(cut + 1).slice(0, 4_000_000);
  const before = stderr + so.slice(0, Math.max(0, cut));
  const out = (before.slice(-20000) + "\n" + lastLine).replace(/^\n/, "");
  const timedOut = ms >= timeoutSec * 1000 - 2000;
  result.stages[stage] = { code: timedOut ? -2 : (r.status ?? -1), out, ms, timedOut, mem_peak: memPeak, swap_peak: swapPeak };
  save();
  console.log(`stage ${stage}: exit ${result.stages[stage].code} in ${(ms / 1000).toFixed(0)} s, memory peak ${memPeak ?? "?"}${swapPeak && !/^0/.test(swapPeak) ? `, swap peak ${swapPeak}` : ""}`);
  return result.stages[stage];
}

/** Copy the compiled module out of an untrusted directory: regular files of the expected names only. */
function copyModule(fromDir, toDir, name) {
  let ok = false;
  for (const ext of [".olean", ".ilean", ".olean.server", ".olean.private", ".ir"]) {
    const src = path.join(fromDir, name + ext);
    let st; try { st = fs.lstatSync(src); } catch { continue; }
    if (!st.isFile() || st.size > 512 * 1024 * 1024) continue;
    fs.copyFileSync(src, path.join(toDir, name + ext));
    if (ext === ".olean") ok = true;
  }
  spawnSync("chmod", ["-R", "a+rX", toDir]);
  return ok;
}

// The same commands, in the same order, as worker/worker.mjs. Stop at the first command that fails.
const ref = lean("ref", dirs.ref, "lean", ["src/Challenge.lean", "-o", "out/Challenge.olean", "-i", "out/Challenge.ilean"], 1200, { writable: true });
if (ref.code === 0) {
  copyModule(path.join(dirs.ref, "out"), path.join(dirs.chk, "out"), "Challenge");
  if (isFormalization) {
    lean("inspect", dirs.chk, "lean", ["--run", "src/Compare.lean", "inspect", "Challenge", plan.target], 600);
  } else {
    const sub = lean("sub", dirs.sub, "lean", ["src/Solution.lean", "-o", "out/Solution.olean", "-i", "out/Solution.ilean"], 1200, { writable: true });
    if (sub.code === 0) {
      if (!copyModule(path.join(dirs.sub, "out"), path.join(dirs.chk, "out"), "Solution")) result.stages.sub.no_olean = true;
      else {
        const cmp = lean("compare", dirs.chk, "lean", ["--run", "src/Compare.lean", "Challenge", "Solution", plan.target, ...(plan.kind === "disproof" ? ["neg"] : [])], 600);
        if (cmp.code === 0 && plan.metric_decl && plan.kind === "proof")
          lean("metric", dirs.chk, "lean", ["--run", "src/Compare.lean", "Challenge", "Solution", plan.metric_decl], 600);
        if (cmp.code === 0) lean("kernel", dirs.chk, "leanchecker", ["Solution"], 1800);
      }
    }
  }
}
save();
console.log("plan done");
