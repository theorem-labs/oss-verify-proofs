(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 8608e43486c0 for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan) instead of a lib/A/Img0 module; every pc,
   table address and frame cell is rate's (measured below); the registers are rate's (the cursor stays in s9, what is
   left of the input is the register s8, a5 holds what was left before the kind byte, s6 the sign-extended kind byte
   and later the shadow address the cases reload, s2 the shadow offset, s4 the frame's shadow base); the frame's
   shadow pattern has 56 bytes; the case tail writes no real-frame cell (in.n goes to s8); the post of a writing
   block and the chaining lemmas are RtPgSteps.v's rts_post / rts_post_seq / rts_blk_seq (not restated here). *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the BLOCK STATEMENTS of the
   walk piece "ent_build A" of LLVMFuzzerTestOneInput (0x80714): the pod loop's head C (0x8127c) to the dispatch of
   ent_build's `switch (kind % 10)` (pod.h:279-281), and the cases 2 and 3 (pod.h:298-324) to the join J (0x81e00).
   Statement text only: no function is proved here (kind: segment lemma).

   WHY BLOCKS. The piece is cut at the points where the code calls something (the __asan_memset of e at 0x812c0,
   the fuzz_u32 read-ahead block of lib/A/RtPgSteps.v, the jump table block rts_jt_block of the same file) and at
   the first store of each case's common tail. Each block is stated over the machine state it starts from (its
   registers, the 8-byte frame cells it reads, the input bytes) in the shape of a callee contract, so that the blocks
   are proved independently and the piece is their chaining with SRr_bind:
     w6_head  C 0x8127c .. 0x812c0 + the memset call: k into [R+0x128], e's 13 shadow granules := 0, e := 0^104;
              returns at 0x812c4.
     w6_kind  0x812c4 .. the case entry: in.n = 0 goes to 0x813a0; else the kind byte, kind % 10 (0xcd multiply,
              0x812e4 .. 0x812fc), case 9 to 0x81954 by `bltu` 0x8130c, cases 0 .. 8 through rts_jt_block.
     w6_c2h   case 2's head 0x816ac: m = fuzz_u8; m odd stops at 0x816d8 (the fuzz_u32 block's start), m even (or
              no byte) loads ints[(m >> 1) % 14] and stops at 0x81d94.
     w6_c3h   case 3's head 0x81710: m odd stops at 0x81c0c; else NaN (m = 0xfe), inf (m = 0xfc) or
              floats[(m >> 1) % 21], stopping at 0x81de4.
     w6_tail  0x81d94 (case 2, type 4) / 0x81de4 (case 3, type 6) .. J 0x81e00: e.type, e.size = 4, e.body[0..4)
              := the value, s8 := in.n.
   THE REGISTERS (checked against the code): s1 = R (x9) the real frame's base, s4 = shadow_addr F (x20),
   s2 = SHADOW_OFF (x18); in the pod loop the cursor in.p is s9 (x25) and in.n is s8 (x24); after the kind read the
   cursor is s9 = c (one past the kind byte), s8 = in.n - 1, a4 (x14) = c - 1 the kind byte's address, and a5 (x15)
   the in.n of the kind read (the read-ahead compares it with 3, 4, 5). [R+0x138] = F + 0xf0 (the address of e),
   [R+0xe8] the shadow address the cases reload into s6 (x22). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSteps.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term (as
   RtPgSteps.v) *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition W6_C : Z := 0x8127c.        (* `sd a1,0x128(s1)`: the pod loop's head *)
Definition W6_MEMSET : Z := 0x51cfc.   (* __asan_memset, the `jal` target at 0x812c0 *)
Definition W6_RET : Z := 0x812c4.      (* after the memset of e *)
Definition W6_D0E : Z := 0x813a0.      (* case 0 with no input left (`beqz s8` 0x812c4 taken) *)
Definition W6_D9 : Z := 0x81954.       (* case 9 (`bltu a2,a1` 0x8130c taken) *)
Definition W6_D2 : Z := 0x816ac.
Definition W6_D3 : Z := 0x81710.
Definition W6_U2 : Z := 0x816d8.       (* case 2's fuzz_u32 block (RtPgSteps rts_u32_block2) .. 0x81d94 *)
Definition W6_U3 : Z := 0x81c0c.       (* case 3's fuzz_u32 block (RtPgSteps rts_u32_block3) .. 0x81de4 *)
Definition W6_T2 : Z := 0x81d94.       (* case 2's tail: e.type := 4 *)
Definition W6_T3 : Z := 0x81de4.       (* case 3's tail: e.type := 6 *)
Definition W6_J : Z := 0x81e00.        (* the join: the inlined pod_write_ent begins *)
(* the tables the cases read (registered globals, .rodata): ints[14] at 0x210e0, floats[21] at 0x21140 *)
Definition W6_INTS : Z := 0x210e0.
Definition W6_FLOATS : Z := 0x21140.

(* ======================================== the code table ========================================
   Every instruction word of [0x8127c, 0x82280): the pod loop (the dispatch, the ten cases' fast paths, the join and
   the record's write, the out-of-line reads of the two fuzz_u32 sites) and the slow blocks of its checks (0x820dc ..
   0x8227c). 0x82280 is SELI, the next piece. The report calls past 0x83000 are never stepped. Precomputed once. *)
Definition W6_TLO : Z := 0x8127c.
Definition W6_TN : nat := 1025.
Definition w6_tbl : ctable := Eval vm_compute in build_table rsegs W6_TLO W6_TN TEmpty.
Lemma w6_tbl_ok : table_ok rsegs w6_tbl.
Proof.
pose proof (build_table_ok0 rsegs W6_TN W6_TLO ltac:(unfold W6_TLO; lia)) as H.
assert (E : build_table rsegs W6_TLO W6_TN TEmpty = w6_tbl) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.

(* ======================================== the model's values ======================================== *)
(* kind % 10 as the code computes it (case 9 by the branch, cases 0 .. 8 by the table) *)
Definition w6_case_pc (kd : Z) : Z := if kd mod 10 =? 9 then W6_D9 else jt_tgt (kd mod 10).
(* the registers the kind block writes, per outcome *)
Definition w6_kind_clob (kd : Z) : list (bv 5) :=
if kd mod 10 =? 9 then [10; 11; 12; 14; 15; 17; 24; 25]%bv else [10; 11; 12; 14; 15; 17; 22; 24; 25]%bv.
(* case 2's int when m is even (ints[(m >> 1) % 14]; with no byte left m = 0 and ints[0]) *)
Definition w6_int_even (m : Z) : Z := nth (Z.to_nat ((m / 2) mod 14)) Tables.ints 0.
(* case 3's bits when m is even: NaN, inf, or floats[(m >> 1) % 21] (Model.ent_build's case 3) *)
Definition w6_float_even (m : Z) : Z :=
if m / 2 =? 127 then 0x7fc00000
else if m / 2 =? 126 then (if Z.testbit m 1 then 0xff800000 else 0x7f800000)
else nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ===================== the context every block runs in =====================
   The harness's journal from the segment's start (rt_seg_pre's first conjunct), the real frame [R, R + 0x1e0)
   (hi_rsz) inside the journal's stack window with the callees' stack below it, the frame for locals F = the
   side-stack frame (3, pos) the harness holds, and the read-only segments as in the image (rt_seg_pre's
   rom_view). *)
Definition w6_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 16 = 0 /\ R + 0x1e0 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (3, pos) own /\ F = frame_addr lyc 3 pos /\
rom_view rsegs W memc.

(* ===================== w6_head: C 0x8127c .. the memset of e, back at 0x812c4 =====================
     0x8127c  sd a1,0x128(s1)                      [R+0x128] := k (the pod index)
     0x81280 .. 0x812b0  13 x sb zero,o(s4)        shadow_addr F + 0x1e .. 0x2a := 0 (e in scope, pod.h:426)
     0x812b4  a2 := 0x68; 0x812b8 ld a0,0x138(s1) (= F + 0xf0); 0x812bc a1 := 0
     0x812c0  jal __asan_memset (0x51cfc)          e := 104 zero bytes (pod.h:279), returns a0 = F + 0xf0
   The memset is the kernel's aintrin_realizes OSet (lib/Reusable/YG0d.v), a hypothesis of the proof. Wr: the
   callee's stack [R - ESTACK, R), the cell [R+0x128, R+0x130), the 13 granules and e. *)
Definition w6_head_wr (R F : Z) : Z -> Prop :=
fun a => (R - ESTACK <= a < R) \/ (R + 0x128 <= a < R + 0x130) \/
(shadow_addr F + 0x1e <= a < shadow_addr F + 0x2b) \/ (F + 0xf0 <= a < F + 0x158).
Definition w6_head_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos kk : Z) (pat : list Z),
w6_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 20 = w64 (shadow_addr F) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 11 = w64 kk ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) ->
rt_fsh rsegs (w_H W) memc F pat -> length pat = 56%nat ->
SRr rsegs W (cfg_at rsegs W6_C regs memc mdc)
(rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_RET rts_caller_saved (w6_head_wr R F)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (F + 0xf0) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x128) 8 (kk mod 2 ^ 64) /\
(forall i, 0 <= i < 13 -> aview rsegs (w_H W2) mem2 (shadow_addr F + 0x1e + i) = Some 0) /\
(forall i, 0 <= i < 104 -> aview rsegs (w_H W2) mem2 (F + 0xf0 + i) = Some 0))).

(* the input bytes r at cursor cur, as rate_build_contract gives them (garr8, range_addressable, 0 < src,
   src + left <= 2 ^ 63, amem_range) and outside the callees' stack below R and the real frame's cells the blocks read
   or write, [R + 0x60, R + 0x120) and [R + 0x128, R + 0x140) (RtPgImgA hi_w1's (XR, 0x60, 0xc0) and
   (XR, 0x128, 0x18); RtPgSeg rs_in) *)
Definition w6_in (W : world rsegs) (memc : word -> option byte) (R cur : Z) (r : list byte) : Prop :=
garr8 rsegs (mrestrict (w_H W) memc) cur (u8s r) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
0 < cur /\ cur + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range cur (Z.of_nat (length r)) /\
(forall a, cur <= a < cur + Z.of_nat (length r) ->
 ~ (R - T_SEG_STK <= a < R) /\ ~ (R + 0x60 <= a < R + 0x120) /\ ~ (R + 0x128 <= a < R + 0x140)).

(* ===================== w6_kind: 0x812c4 .. the case entry (no store) =====================
     0x812c4  beqz s8 -> 0x813a0                    in.n = 0: kind = 0, case 0 with nothing read
     0x812c8 .. 0x812d4  the shadow check of s9 (NE-SLOW, slow block 0x820dc)
     0x812d8  lbu a0,0(s9); a5 := s8; s8 := s8 - 1
     0x812e4 .. 0x812fc  a1 := kind % 10 (a1 = (kind * 0xcd) >> 11, a1 := (kind - 10 a1) & 0xff), a7 := 10
     0x81300  a4 := s9 (the kind's address); s9 += 1; a2 := 8; 0x8130c bltu a2,a1 -> 0x81954 (case 9)
     0x81310 .. 0x81330  rts_jt_block (lib/A/RtPgSteps.v) to jt_tgt (kind % 10).
   The cursor is s9 = cur and the input left is r (s8 = |r|). *)
Definition w6_kind_R (kd cur nl' : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 14 = w64 cur /\ getr regs2 25 = w64 (cur + 1) /\ getr regs2 24 = w64 nl' /\
getr regs2 15 = w64 (nl' + 1) /\ getr regs2 17 = w64 10 /\
(if kd mod 10 =? 9 then getr regs2 10 = w64 kd /\ getr regs2 11 = w64 9 /\ getr regs2 12 = w64 8
 else bv_unsigned (getr regs2 10) = (kd mod 256) * 2 ^ 56 /\ getr regs2 11 = w64 (jt_tgt (kd mod 10)) /\
      getr regs2 12 = w64 JT_A /\ getr regs2 22 = w64 (sext8 kd)).
Definition w6_kind_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z) (r : list byte),
w6_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 18 = w64 SHADOW_OFF -> getr regs 25 = w64 cur -> getr regs 24 = w64 (Z.of_nat (length r)) ->
w6_in W memc R cur r ->
SRr rsegs W (cfg_at rsegs W6_RET regs memc mdc)
(fun W2 c2 =>
 (r = [] /\
  rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_D0E [] (fun _ => True) W2 c2) \/
 (exists b r', r = b :: r' /\
  rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (w6_case_pc (bv_unsigned b))
  (w6_kind_clob (bv_unsigned b)) (w6_kind_R (bv_unsigned b) cur (Z.of_nat (length r'))) W2 c2)).

(* ===================== w6_c2h / w6_c3h: a case's head (no store) =====================
   At the case entry (w6_kind's post): s9 = c (the cursor after kind), s8 = |r| (in.n after kind), a4 = c - 1,
   a5 = |r| + 1 (in.n of the kind read), [R+0xe8] = vb. m = fuzz_u8 r.
   case 2 (pod.h:298-303): 0x816ac beqz s8 -> 0x819b8 (m = 0: a1 := 0, a2 := 0, s6 := [R+0xe8]); the check of s9
     (NE-SLOW, 0x8217c) with s6 := [R+0xe8] between its load and its branch; lbu a2 = m; a1 := a5 - 2; s9 := a4 + 2;
     m odd: stop at 0x816d8 (the u32 block: a1 = |r'|, s9 = c + 1, a4 = c - 1, a5 = |r'| + 2, exactly
     rts_u32_block2's premises); m even: 0x819c4 .. 0x81a04 a2 := ints[(m >> 1) % 14] (mulhu by the constant at
     0x10318; the check of the int, NE-SLOW 0x82138), stop at 0x81d94.
   case 3 (pod.h:304-324): 0x81710, the same read (m = 0: 0x81a0c, then the floats arm 0x81d14); m odd: stop at
     0x81c0c; m = 0xfe: a2 := 0x7fc00000 (0x81d08); m = 0xfc: a2 := 0x7f800000 (0x8174c); else a2 :=
     floats[(m >> 1) % 21] (0x81d10 .. 0x81d4c, mulhu by the constant at 0x10310, the check NE-SLOW 0x821ec, its
     slow path reached at floats[20]); stop at 0x81de4.
   The value is given mod 2 ^ 32 (`lw` sign-extends; the tail stores its low 4 bytes). *)
Definition w6_head_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R c vb : Z)
(r : list byte) : Prop :=
getr regs 9 = w64 R /\ getr regs 18 = w64 SHADOW_OFF /\ getr regs 25 = w64 c /\
getr regs 24 = w64 (Z.of_nat (length r)) /\ getr regs 14 = w64 (c - 1) /\
getr regs 15 = w64 (Z.of_nat (length r) + 1) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 vb /\ 0 <= vb < 2 ^ 64 /\
0 < c - 1 /\ w6_in W memc R c r.
Definition w6_case_head_stmt (c3 : bool) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c vb : Z) (r : list byte),
w6_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6_head_in W memc regs R c vb r ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (if c3 then W6_FLOATS else W6_INTS) (if c3 then 84 else 56) ->
SRr rsegs W (cfg_at rsegs (if c3 then W6_D3 else W6_D2) regs memc mdc)
(fun W2 c2 =>
 let mv := fst (Cursor.fuzz_u8 r) in let r1 := snd (Cursor.fuzz_u8 r) in
 if Z.odd mv then
  rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6_U3 else W6_U2)
  [10; 11; 12; 13; 22; 25]%bv
  (fun regs2 => getr regs2 11 = w64 (Z.of_nat (length r1)) /\ getr regs2 12 = w64 mv /\
     getr regs2 25 = w64 (c + 1) /\ getr regs2 22 = w64 vb) W2 c2
 else
  rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6_T3 else W6_T2)
  [10; 11; 12; 13; 22; 25]%bv
  (fun regs2 => (exists v, getr regs2 12 = w64 v /\
       v mod 2 ^ 32 = (if c3 then w6_float_even mv else w6_int_even mv) mod 2 ^ 32) /\
     getr regs2 11 = w64 (Z.of_nat (length r1)) /\
     getr regs2 25 = w64 (c + Z.of_nat (length r - length r1)) /\ getr regs2 22 = w64 vb) W2 c2).
Definition w6_c2h_stmt : Prop := w6_case_head_stmt false.
Definition w6_c3h_stmt : Prop := w6_case_head_stmt true.

(* ===================== w6_tail: 0x81d94 / 0x81de4 .. J 0x81e00 =====================
     0x81d94  ld a0,0x138(s1); a3 := 4; sw a3,0(a0) (e.type = POD_INT); j 0x81df4        (case 2)
     0x81de4  ld a0,0x138(s1); a3 := 6; sw a3,0(a0) (e.type = POD_FLOAT); a3 := 4        (case 3)
     0x81df4  sw a3,4(a0) (e.size = 4); sw a2,8(a0) (e.body[0..4) = the value); mv s8,a1 (in.n) -> J 0x81e00
   e = F + 0xf0 lies in the frame (3, pos) the harness owns; the cursor stays in s9. *)
Definition w6_tail_wr (F : Z) : Z -> Prop := fun a => F + 0xf0 <= a < F + 0xfc.
Definition w6_tail_stmt (c3 : bool) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos n' v : Z),
w6_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (F + 0xf0) ->
getr regs 11 = w64 n' -> getr regs 12 = w64 v ->
SRr rsegs W (cfg_at rsegs (if c3 then W6_T3 else W6_T2) regs memc mdc)
(rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_J [10; 13; 24]%bv (w6_tail_wr F)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (F + 0xf0) /\ getr regs2 13 = w64 4 /\ getr regs2 24 = w64 n' /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0xf0) 4 (if c3 then 6 else 4) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0xf4) 4 4 /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0xf8) 4 (v mod 2 ^ 32))).
Definition w6_tail2_stmt : Prop := w6_tail_stmt false.
Definition w6_tail3_stmt : Prop := w6_tail_stmt true.

End d.
End b.
