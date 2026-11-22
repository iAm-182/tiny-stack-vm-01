// Tiny stack VM for make.fun's tiny-stack-vm-01 ISA v1.
// Original implementation written for this competition from the published ISA.
// Answers every instance in /input/<id>/ as /output/<id>/stdout.bin + exit.txt.
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const LIM = 1000000, OMAX = 65536;
// One program. Traps end the run at once with the trap's code; output written before stands.
function run(p: Uint8Array, inp: Uint8Array) {
  const n = p.length, st = new Int32Array(256);
  let sp = 0;
  const cs = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256), out = new Uint8Array(OMAX);
  let ol = 0, ip = 0, pc = 0, steps = 0;
  const end = (c: number) => ({ out: out.subarray(0, ol), code: c });
  for (;;) {
    if (steps === LIM) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    steps++;
    switch (op) {
      case 0: return end(0); // HALT
      case 1: // PUSH8, sign-extended
        if (pc + 1 >= n) return end(9);
        if (sp + 1 > 256) return end(3);
        st[sp++] = (p[pc + 1] << 24) >> 24; pc += 2; break;
      case 2: // PUSH32, little-endian
        if (pc + 4 >= n) return end(9);
        if (sp + 1 > 256) return end(3);
        st[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24); pc += 5; break;
      case 3: // POP
        if (sp < 1) return end(2);
        sp--; pc++; break;
      case 4: // DUP
        if (sp < 1) return end(2);
        if (sp + 1 > 256) return end(3);
        st[sp] = st[sp - 1]; sp++; pc++; break;
      case 5: { // SWAP
        if (sp < 2) return end(2);
        const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; pc++; break;
      }
      case 6: // OVER
        if (sp < 2) return end(2);
        if (sp + 1 > 256) return end(3);
        st[sp] = st[sp - 2]; sp++; pc++; break;
      case 7: { // ROT (a b c -- b c a)
        if (sp < 3) return end(2);
        const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; pc++; break;
      }
      case 0x17: // NEG, wraps: -INT_MIN stays INT_MIN
        if (sp < 1) return end(2);
        st[sp - 1] = (-st[sp - 1]) | 0; pc++; break;
      case 0x1b: // NOT
        if (sp < 1) return end(2);
        st[sp - 1] = ~st[sp - 1]; pc++; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        if (sp < 2) return end(2);
        const b = st[sp - 1], a = st[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break; // ADD
          case 0x11: r = (a - b) | 0; break; // SUB
          case 0x12: r = Math.imul(a, b); break; // MUL, exact low 32 bits
          case 0x13: // DIV, signed, truncates toward zero; INT_MIN/-1 -> INT_MIN via |0
            if (b === 0) return end(4);
            r = (a / b) | 0; break;
          case 0x14: // MOD, sign of a; x % -1 is 0 (|0 turns -0 into 0)
            if (b === 0) return end(4);
            r = (a % b) | 0; break;
          case 0x15: // DIVU
            if (b === 0) return end(4);
            r = ((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: // MODU
            if (b === 0) return end(4);
            r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break; // AND
          case 0x19: r = a | b; break; // OR
          case 0x1a: r = a ^ b; break; // XOR
          case 0x1c: r = a << (b & 31); break; // SHL
          case 0x1d: r = a >> (b & 31); break; // SHR, arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // SHRU, logical
          case 0x20: r = a === b ? 1 : 0; break; // EQ
          case 0x21: r = a < b ? 1 : 0; break; // LT, signed
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        }
        st[sp - 2] = r; sp--; pc++; break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit rel. to next insn
        if (pc + 2 >= n) return end(9);
        const rel = ((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16, nx = pc + 3;
        if (op === 0x30) { pc = nx + rel; break; }
        if (sp < 1) return end(2);
        const v = st[--sp];
        pc = (op === 0x31 ? v === 0 : v !== 0) ? nx + rel : nx; break;
      }
      case 0x33: // CALL, unsigned 16-bit absolute target
        if (pc + 2 >= n) return end(9);
        if (cp === 64) return end(7);
        cs[cp++] = pc + 3; pc = p[pc + 1] | (p[pc + 2] << 8); break;
      case 0x34: // RET
        if (cp === 0) return end(8);
        pc = cs[--cp]; break;
      case 0x40: { // LOAD
        if (sp < 1) return end(2);
        const a = st[sp - 1];
        if (a < 0 || a > 255) return end(6);
        st[sp - 1] = mem[a]; pc++; break;
      }
      case 0x41: { // STORE (v addr --)
        if (sp < 2) return end(2);
        const a = st[sp - 1], v = st[sp - 2];
        if (a < 0 || a > 255) return end(6);
        sp -= 2; mem[a] = v; pc++; break;
      }
      case 0x50: { // PRINT, decimal ASCII, no newline; over-limit write writes nothing
        if (sp < 1) return end(2);
        const t = String(st[sp - 1]);
        if (ol + t.length > OMAX) return end(11);
        sp--;
        for (let i = 0; i < t.length; i++) out[ol++] = t.charCodeAt(i);
        pc++; break;
      }
      case 0x51: // PUTC, one byte v & 255
        if (sp < 1) return end(2);
        if (ol + 1 > OMAX) return end(11);
        out[ol++] = st[--sp] & 255; pc++; break;
      case 0x52: // IN, next byte or -1 once input is used up
        if (sp + 1 > 256) return end(3);
        st[sp++] = ip < inp.length ? inp[ip++] : -1; pc++; break;
      case 0x53: // EXIT, code v & 255
        if (sp < 1) return end(2);
        return end(st[--sp] & 255);
      default: return end(5); // unknown opcode
    }
  }
}
for (const id of readdirSync(IN).sort()) {
  const d = join(IN, id);
  const prog = new Uint8Array(readFileSync(join(d, 'program.bin')));
  const inp = existsSync(join(d, 'input.bin')) ? new Uint8Array(readFileSync(join(d, 'input.bin'))) : new Uint8Array(0);
  const r = run(prog, inp);
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), r.out);
  writeFileSync(join(OUT, id, 'exit.txt'), `${r.code}\n`);
}
