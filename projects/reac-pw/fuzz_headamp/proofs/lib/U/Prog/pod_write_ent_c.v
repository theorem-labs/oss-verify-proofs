From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** pod_write_ent(pp, e) (fuzz/pod.h:200-206, with pod_put :175-182, pod_pad :184-188, pod_put32 :190-193; 364
    bytes, 91 instructions at 0x14b5c in the UBSan image; frame 32 bytes, saves ra, s0, s1, s2 at sp - 8 .. sp - 32).
    The plain build inlines it (headamp's plain image has no pod_write_ent symbol), so this contract has no plain twin.

    What it does on the path the premises select (len is the u64 at pp + 16384, n = |enc_pod e|):
      0x14b5c-0x14b6c prologue; 0x14b70 `andi a2,a1,3` and 0x14b7c `andi a0,a0,7` (alignment checks, s0 = pp at
      0x14b78); s2 = pp + 0x4000 (0x14b88), a0 = len (0x14b8c); 0x14b90-0x14ba0 capacity guard len + 4 <= 16384;
      0x14bb4 `lw a5,4(a1)` reads e->size and 0x14bc8-0x14bd4 store its 4 bytes at pp + len; len += 4 (0x14bd8-0x14bec);
      0x14bf0 guard; 0x14c04 `lw a3,0(a1)` reads e->type and 0x14c18-0x14c24 store its 4 bytes at pp + len + 4;
      len += 4 (0x14c28-0x14c30); 0x14c34 `lwu s1,4(a1)` re-reads e->size; 0x14c3c guard len + 8 + size <= 16384;
      0x14c5c memcpy(pp + len + 8, e + 8, size); len += size (0x14c60-0x14c68); 0x14c6c-0x14c70 s1 = (-len) & 7, the
      pad; 0x14c7c guard; 0x14c9c memset(pp + len + 8 + size, 0, pad); len += pad (0x14ca0-0x14ca8); 0x14cac-0x14cc0
      epilogue and `ret`. memcpy and memset are called even when their count is 0.
    So the bytes written at pp + len are le32 e_size ++ le32 e_type ++ e_body ++ zeros pad, the size word first: the
    order of the shared enc_pod. pod_pad pads pp->len, not e->size, to a multiple of 8, so the pad is pad8 e_size only
    when len is 8-aligned at entry: hence the premise len mod 8 = 0.
    Reads: the 104 bytes of e (type, size, body), the len cell. Writes: [pp + len, pp + len + n), the len cell
    (pp + 16384, 8 bytes, stored four times), and its frame [sp - 32, sp). memcpy and memset use no stack.

    Its trap site is 0x14cc4 `unimp`, reached from ten branches; the premise that makes each dead:
      0x14b74 `bnez` (e & 3, e->size access not 4-aligned): bv_unsigned a1 mod 4 = 0;
      0x14b80 `bnez` (pp & 7, pp->len access not 8-aligned): bv_unsigned a0 mod 8 = 0;
      0x14ba8 `bgeu len,0x4001` / 0x14bb0 `bltu ~pp,len` (pp->buf + len out of bounds / wrapping, put32 e->size),
      0x14bfc / 0x14c00 (the same at len + 4, put32 e->type),
      0x14c44 / 0x14c4c (the same at len + 8, the memcpy destination),
      0x14c84 / 0x14c8c (the same at len + 8 + size, the memset destination): each of those offsets is at most
        len + n <= 16384 (the capacity premise), and pp + 16384 + 8 <= 2^64 (the bound in the len cell's rw_cells),
        so none is >= 16385 and pp + offset < 2^64.
    The four capacity guards (0x14ba0, 0x14bf0, 0x14c3c, 0x14c7c; else the put is skipped) are not traps; with
    len mod 8 = 0 and len + n <= 16384 every one falls through, so all n bytes are written.

    Callee contracts its walk takes as premises (the released forms relocated to headamp's UBSan image):
    U/Prog/memcpy_c.v memcpy_contract (memcpy at 0x1d748; 0x14c5c `jal`, a0 = pp + len + 8, a1 = e + 8, a2 = e_size)
    and U/Prog/memset_c.v memset_contract (MEMSET = 0x1db4c; 0x14c9c `jal`, a0 = pp + len + 8 + e_size, a1 = 0,
    a2 = pad).

    Call sites (LLVMFuzzerTestOneInput, UBSan, [0x12fa8, 0x148ac); frame 0x260 bytes, so sp = S - 608 with S its
    16-aligned entry sp): 0x132fc, 0x13e08 and 0x13f14 are the three `jal` instructions of that function whose
    target is POD_WRITE_ENT = 0x14b5c. At each one the two instructions before the call set the arguments:
    a0 = s8 (0x132f8 / 0x13e04 / 0x13f10 `mv a0,s8`) and a1 = sp + 0xb8 (0x132f4 / 0x13e00 / 0x13f0c
    `addi a1,sp,0xb8`). That the premises above hold at those three sites -- pp 8-aligned, the len cell, the
    capacity bound, the buffer, ent_mem of e, apartness, the stack and mem_inv -- is shown by headamp's own walk
    of LLVMFuzzerTestOneInput, which carries the record invariant; this file states the contract only. *)
Definition POD_WRITE_ENT : Z := 0x14b5c.
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
