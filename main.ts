// A tiny stack virtual machine, written from the published ISA (v1) alone.
// Plain JavaScript in a .ts file (erasable syntax only), Node 22 stdlib only.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
// ISA bounds and the exit codes of the ten traps.
const STACK_CAP = 256, CALL_CAP = 64, MEM_WORDS = 256, STEP_CAP = 1000000, OUT_CAP = 65536;
const X_UNDER = 2, X_OVER = 3, X_DIV0 = 4, X_OPCODE = 5, X_MEM = 6;
const X_CALL = 7, X_RET = 8, X_PC = 9, X_STEPS = 10, X_OUT = 11;
// Every finish (halt, EXIT, trap) unwinds through this signal.
class Done { constructor(code) { this.code = code; } }
const finish = (code) => { throw new Done(code); };
// Immediate length; -1 when the byte is no opcode.
function immLen(op) {
  if (op === 0x01) return 1;
  if (op === 0x02) return 4;
  if (op >= 0x30 && op <= 0x33) return 2;
  const known = (op >= 0x00 && op <= 0x07) || (op >= 0x10 && op <= 0x1e) ||
    op === 0x20 || op === 0x21 || op === 0x22 || op === 0x34 ||
    op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53);
  return known ? 0 : -1;
}

// Stack effect [popped, pushed], checked before the op runs.
function stackFlow(op) {
  if (op === 0x00 || op === 0x30 || op === 0x33 || op === 0x34) return [0, 0];
  if (op === 0x01 || op === 0x02 || op === 0x52) return [0, 1];
  if (op === 0x04) return [1, 2];
  if (op === 0x17 || op === 0x1b || op === 0x40) return [1, 1];
  if (op === 0x05) return [2, 2];
  if (op === 0x06) return [2, 3];
  if (op === 0x07) return [3, 3];
  if (op === 0x41) return [2, 0];
  if (op === 0x03 || op === 0x31 || op === 0x32 || op >= 0x50) return [1, 0];
  return [2, 1];
}

function runVm(prog, input) {
  const stack = [], calls = [], out = [];
  const mem = new Int32Array(MEM_WORDS);
  let pc = 0, steps = 0, inAt = 0;
  const u16 = (at) => prog[at] | (prog[at + 1] << 8);
  const s16 = (at) => (u16(at) << 16) >> 16;
  try {
    for (;;) {
      // Step order: cap, pc range, opcode, fit, stack bounds.
      if (steps >= STEP_CAP) finish(X_STEPS);
      if (pc < 0 || pc >= prog.length) finish(X_PC);
      const op = prog[pc];
      const imm = immLen(op);
      if (imm < 0) finish(X_OPCODE);
      if (pc + imm >= prog.length) finish(X_PC);
      steps++;
      const flow = stackFlow(op);
      if (stack.length < flow[0]) finish(X_UNDER);
      if (stack.length - flow[0] + flow[1] > STACK_CAP) finish(X_OVER);
      const next = pc + 1 + imm;
      pc = next;
      switch (op) {
        case 0x00: finish(0); break;
        case 0x01: stack.push((prog[next - 1] << 24) >> 24); break; // PUSH8 sign-extends
        case 0x02:
          stack.push(prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24));
          break;
        case 0x03: stack.pop(); break;
        case 0x04: stack.push(stack[stack.length - 1]); break;
        case 0x05: { const b = stack.pop(), a = stack.pop(); stack.push(b, a); break; }
        case 0x06: stack.push(stack[stack.length - 2]); break;
        case 0x07: { const c = stack.pop(), b = stack.pop(), a = stack.pop(); stack.push(b, c, a); break; }
        case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
        case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
        case 0x1e: case 0x20: case 0x21: case 0x22: {
          const b = stack.pop(), a = stack.pop();
          let r;
          if (op === 0x10) r = a + b;
          else if (op === 0x11) r = a - b;
          else if (op === 0x12) r = Math.imul(a, b); // exact low 32 bits
          else if (op === 0x13) {
            if (b === 0) finish(X_DIV0);
            r = a === -2147483648 && b === -1 ? a : Math.trunc(a / b);
          } else if (op === 0x14) {
            if (b === 0) finish(X_DIV0);
            r = b === -1 ? 0 : a % b;
          } else if (op === 0x15) {
            if (b === 0) finish(X_DIV0);
            r = Math.floor((a >>> 0) / (b >>> 0));
          } else if (op === 0x16) {
            if (b === 0) finish(X_DIV0);
            r = (a >>> 0) % (b >>> 0);
          }
          else if (op === 0x18) r = a & b;
          else if (op === 0x19) r = a | b;
          else if (op === 0x1a) r = a ^ b;
          else if (op === 0x1c) r = a << (b & 31); // shift counts use the low 5 bits
          else if (op === 0x1d) r = a >> (b & 31);
          else if (op === 0x1e) r = a >>> (b & 31);
          else if (op === 0x20) r = a === b ? 1 : 0;
          else if (op === 0x21) r = a < b ? 1 : 0;
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
          stack.push(r | 0); // wraps to a signed 32-bit value
          break;
        }
        case 0x17: stack.push((-stack.pop()) | 0); break;
        case 0x1b: stack.push(~stack.pop()); break;
        case 0x30: pc = next + s16(next - 2); break; // jumps are next-relative
        case 0x31: if (stack.pop() === 0) pc = next + s16(next - 2); break;
        case 0x32: if (stack.pop() !== 0) pc = next + s16(next - 2); break;
        case 0x33:
          if (calls.length >= CALL_CAP) finish(X_CALL);
          calls.push(next);
          pc = u16(next - 2); // CALL's target is absolute, unsigned
          break;
        case 0x34:
          if (calls.length === 0) finish(X_RET);
          pc = calls.pop();
          break;
        case 0x40: {
          const addr = stack[stack.length - 1];
          if (addr < 0 || addr >= MEM_WORDS) finish(X_MEM);
          stack[stack.length - 1] = mem[addr];
          break;
        }
        case 0x41: {
          const addr = stack.pop(), v = stack.pop();
          if (addr < 0 || addr >= MEM_WORDS) finish(X_MEM);
          mem[addr] = v;
          break;
        }
        case 0x50: { // a print past the output cap writes nothing
          const text = String(stack[stack.length - 1]);
          if (out.length + text.length > OUT_CAP) finish(X_OUT);
          stack.pop();
          for (let i = 0; i < text.length; i++) out.push(text.charCodeAt(i));
          break;
        }
        case 0x51:
          if (out.length + 1 > OUT_CAP) finish(X_OUT);
          out.push(stack.pop() & 255);
          break;
        case 0x52: stack.push(inAt < input.length ? input[inAt++] : -1); break;
        case 0x53: finish(stack.pop() & 255); break;
        default: finish(X_OPCODE);
      }
    }
  } catch (err) {
    if (err instanceof Done) return { bytes: Uint8Array.from(out), code: err.code };
    throw err;
  }
}

const inDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(inDir).sort()) {
  const ans = runVm(readFileSync(join(inDir, id, 'program.bin')), readFileSync(join(inDir, id, 'input.bin')));
  mkdirSync(join(outDir, id), { recursive: true });
  writeFileSync(join(outDir, id, 'stdout.bin'), ans.bytes);
  writeFileSync(join(outDir, id, 'exit.txt'), ans.code + '\n');
}
