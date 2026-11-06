From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** pod_write_ent(pp, e) (fuzz/pod.h:200-206, with pod_put :175-182, pod_pad :184-188, pod_put32 :190-193; 364
    bytes, 91 instructions at 0x14a18 in the UBSan image; frame 32 bytes, saves ra, s0, s1, s2 at sp - 8 .. sp - 32).
    The plain build has no pod_write_ent symbol: it inlines the body into LLVMFuzzerTestOneInput three times
    (0x13358, 0x13cf8, 0x13f6c in the plain image, each the pod.h:177 guard of the first pod_put32), so this
    contract has no plain twin.

    What it does on the path the premises select (len is the u64 at pp + 16384, n = |enc_pod e|):
      0x14a18-0x14a28 prologue; 0x14a2c `andi a2,a1,3` and 0x14a38 `andi a0,a0,7` (alignment checks, s0 = pp at
      0x14a34); s2 = pp + 0x4000 (0x14a44), a0 = len (0x14a48); 0x14a4c-0x14a5c capacity guard len + 4 <= 16384;
      0x14a70 `lw a5,4(a1)` reads e->size and 0x14a84-0x14a90 store its 4 bytes at pp + len; len += 4 (0x14a94-0x14aa8);
      0x14aac guard; 0x14ac0 `lw a3,0(a1)` reads e->type and 0x14ad4-0x14ae0 store its 4 bytes at pp + len + 4;
      len += 4 (0x14ae4-0x14aec); 0x14af0 `lwu s1,4(a1)` re-reads e->size; 0x14af8 guard len + 8 + size <= 16384;
      0x14b18 memcpy(pp + len + 8, e + 8, size); len += size (0x14b1c-0x14b24); 0x14b28-0x14b2c s1 = (-len) & 7, the
      pad; 0x14b38 guard; 0x14b58 memset(pp + len + 8 + size, 0, pad); len += pad (0x14b5c-0x14b64); 0x14b68-0x14b7c
      epilogue and `ret`. memcpy and memset are called even when their count is 0.
    So the bytes written at pp + len are le32 e_size ++ le32 e_type ++ e_body ++ zeros pad, the size word first: the
    order of the shared enc_pod. pod_pad pads pp->len, not e->size, to a multiple of 8, so the pad is pad8 e_size only
    when len is 8-aligned at entry: hence the premise len mod 8 = 0.
    Reads: the 104 bytes of e (type, size, body), the len cell. Writes: [pp + len, pp + len + n), the len cell
    (pp + 16384, 8 bytes, stored four times), and its frame [sp - 32, sp). memcpy and memset use no stack.

    Its trap site is 0x14b80 `unimp`, reached from ten branches; the premise that makes each dead:
      0x14a30 `bnez` (e & 3, e->size access not 4-aligned): bv_unsigned a1 mod 4 = 0;
      0x14a3c `bnez` (pp & 7, pp->len access not 8-aligned): bv_unsigned a0 mod 8 = 0;
      0x14a64 `bgeu len,0x4001` / 0x14a6c `bltu ~pp,len` (pp->buf + len out of bounds / wrapping, put32 e->size),
      0x14ab8 / 0x14abc (the same at len + 4, put32 e->type),
      0x14b00 / 0x14b08 (the same at len + 8, the memcpy destination),
      0x14b40 / 0x14b48 (the same at len + 8 + size, the memset destination): each of those offsets is at most
        len + n <= 16384 (the capacity premise), and pp + 16384 + 8 <= 2^64 (the bound in the len cell's rw_cells),
        so none is >= 16385 and pp + offset < 2^64.
    The four capacity guards (0x14a5c, 0x14aac, 0x14af8, 0x14b38; else the put is skipped) are not traps; with
    len mod 8 = 0 and len + n <= 16384 every one falls through, so all n bytes are written.

    Callee contracts its walk takes as premises (the released forms relocated to rate's UBSan image):
    U/Prog/memcpy_c.v memcpy_contract (memcpy at 0x1d214; 0x14b18 `jal`, a0 = pp + len + 8, a1 = e + 8, a2 = e_size)
    and U/Prog/memset_c.v memset_contract (MEMSET = 0x1d618; 0x14b58 `jal`, a0 = pp + len + 8 + e_size, a1 = 0,
    a2 = pad).

    Call sites (LLVMFuzzerTestOneInput, UBSan, 0x12fe0; frame 0x250 bytes, so sp = S - 592 with S its 16-aligned
    entry sp). Each struct pod_ent lives at sp + 0xe8 (type at +0, size at +4, the 96-byte body at +8):
      0x13398 (pod.h:404, shape-7 Int pod): a0 = s8 (0x13394 `mv a0,s8`), a1 = sp + 0xe8 (0x13390); e was set by
        memset(sp + 0xf0, 0, 0x60) at 0x13384 (pod.h:403) and `sw s1,0xe8(sp)`, `sw s1,0xec(sp)` (0x13388, 0x1338c;
        s1 = 4 at 0x132c4): Ent 4 4 (le32 0);
      0x13efc (pod.h:430, the count loop): a0 = s8 (0x13ef8), a1 = sp + 0xe8 (0x13ef4); e was built by ent_build,
        which starts with memset(sp + 0xe8, 0, 0x68) at 0x1356c (pod.h:279);
      0x14010 (pod.h:416, the Int-7 value): a0 = s8 (0x1400c), a1 = sp + 0xe8 (0x14008); e was set by
        memset(sp + 0xf4, 0, 0x5c) at 0x13ff4 (pod.h:413), `sw s1,0xe8(sp)` (0x13ff8), `sw s1,0xec(sp)` (0x13ffc)
        and `sw a0,0xf0(sp)` (0x14004) with a0 = 7 set at 0x14000: Ent 4 4 (le32 7).
      s8 = pp, the malloc(19744) result (0x1310c `jal` malloc at 0x16a7c with a0 = 0x5000 - 0x2e0, 0x13118
      `mv s8,a0`), spilled to 0xd8(sp) at 0x13298 and reloaded from there after the calls that use s8 (fourteen
      `ld s8,0xd8(sp)`, the first 0x13650 and the last 0x13e48). &pp->len is held in s11 = pp + 0x4000 (0x131a0
      `lui a0,4`, 0x131a8 `add s11,s8,a0`), spilled to 0xc8(sp) at 0x13338.
    Why each premise holds there:
      pp 8-aligned: malloc returns 16-aligned blocks (main's own check 0x13194 `andi a0,s8,7`, 0x13198 `beqz`,
        pod.h:387, tests the same);
      the len cell: memset(pp, 0, 19744) at 0x13124 (pod.h:384), then the walk's record invariant; len is the length
        of the bytes written so far, a multiple of 8 (the header is 8 or 16 bytes, key + flags 8, a Struct header 8,
        every enc_pod a multiple of 8);
      len + n <= 16384: at 0x13efc the stop rule 0x13ee4-0x13eec (`ld a0,0(s11)`, `addi a1,a0,0x70`,
        `bltu s6,a1` with s6 = 0x4000, the value of the two `lui s6,4` at 0x13c50 and 0x13dd8 that are the last
        definitions of s6 before it; pod.h:428) gives len + 112 <= 16384 and n <= 104
        for e_size <= 96; at 0x13398 and 0x14010 n = 16 and the model's bound (the record is at most 5440 bytes;
        len <= 5440 - 56 before every call, e_size <= 45) gives it;
      the buffer [pp + len, pp + len + n): inside the malloc block, still memset's zeros (the walk's invariant), and
        writable;
      e: a1 = sp + 0xe8 with sp 16-aligned, so 4-aligned; its 104 bytes are ent_mem e by the stores listed above, with
        e_size = 4 or the ent_build model's e_size <= 45, and length e_body = e_size;
      apart: pp's record is a heap block, e and [lo, sp) are stack (e = sp + 0xe8 lies above sp);
      the stack: the harness walk's stk below its sp, with far more than 32 bytes of room;
      mem_inv: the walk's invariant. *)
Definition POD_WRITE_ENT : Z := 0x14a18.
(** The frame. *)
Definition PWE_STACK : Z := 32.
(** offsetof(struct pod_props, len) = sizeof pp->buf. *)
Definition PWE_LEN : Z := 16384.
(** buf and the len cell, [pp, pp + 16392). *)
Definition PWE_REC : Z := 16392.
(** sizeof(struct pod_ent), and its body. *)
Definition PWE_ENT : Z := 104.
Definition PWE_BODY : Z := 96.

Definition pod_write_ent_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e : ent) (len : Z) (junk : list byte) (lo : Z),
    bv_unsigned a0 mod 8 = 0 ->
    rw_cells rsegs m (bv_unsigned a0 + PWE_LEN) [C8 (Z_to_bv 64 len)] ->
    0 <= len -> len mod 8 = 0 -> len + Z.of_nat (length (enc_pod e)) <= PWE_LEN ->
    rw_cells rsegs m (bv_unsigned a0 + len) [CB (length (enc_pod e)) junk] ->
    bv_unsigned a1 mod 4 = 0 ->
    bytes_at rsegs m (bv_unsigned a1) (ent_mem e) ->
    Z.of_nat (length (e_body e)) = e_size e -> e_size e <= PWE_BODY ->
    (bv_unsigned a0 + PWE_REC <= bv_unsigned a1 \/ bv_unsigned a1 + PWE_ENT <= bv_unsigned a0) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PWE_STACK <= bv_unsigned sp ->
    (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
    (bv_unsigned a0 + PWE_REC <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a1 + PWE_ENT <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - PWE_STACK, bv_unsigned sp);
                (bv_unsigned a0 + len, bv_unsigned a0 + len + Z.of_nat (length (enc_pod e)));
                (bv_unsigned a0 + PWE_LEN, bv_unsigned a0 + PWE_LEN + 8)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (bv_unsigned a0 + len) (enc_pod e) /\
         bytes_at rsegs m' (bv_unsigned a0 + PWE_LEN) (le8 (Z_to_bv 64 (len + Z.of_nat (length (enc_pod e))))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 POD_WRITE_ENT) fc None m (seg_rom rsegs)).

(** The arithmetic premises met by one concrete value: a 13-byte String ent (twelve 'x' and a NUL) at len = 16.
    n = 8 + 13 + 3 = 24, and the len cell moves (16 + n <> 16), so the post cannot hold with m' = m. *)
Example pod_write_ent_witness :
  let e := Ent 8 13 (repeat (Z_to_bv 8 120) 12 ++ [Z_to_bv 8 0]) in
  Z.of_nat (length (e_body e)) = e_size e /\ e_size e <= PWE_BODY /\
  length (enc_pod e) = 24%nat /\ length (ent_mem e) = 104%nat /\
  16 mod 8 = 0 /\ 16 + Z.of_nat (length (enc_pod e)) <= PWE_LEN /\ 16 + Z.of_nat (length (enc_pod e)) <> 16.
Proof. vm_compute. repeat split; try reflexivity; intro H; discriminate H. Qed.
