(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0Def.v at 27540f54413f for reac-pw/fuzz_rate's image A; rate's pcs (the head's two out-of-line blocks 0x81b38 and 0x81b58, the arms DIG 0x813f8 and ODD 0x81b6c), registers (in.n in s10, &ch in s6, the `v / 10` multiplier in t2) and code table; the frame's shadow rows in RtPgMem's seven-flag words; the piece lemma rt7_piece from the three block statements. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Def.v at 21da95a5fcd3 for image B (fuzz_rate.asan-ubsan): image B's pcs (the arms DIG 0x8152c and ODD 0x81de0, the out-of-line range 0x81d58 .. 0x81e54 and the slow blocks 0x82270 / 0x82314), registers (what is left in t1, &ch in s2, p in s9, the cursor in the cell R+0x128, c in a3, the digit loop's 4 / 10 / 9 in t0 / t2 / t3, the `v / 10` multiplier in s5) and code table; the frame's shadow rows in lib/AU/RtPgMemB.v's words; the statements over lib/AU/RtPgSegB.v's cuts; names rt7_ -> rt7b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0DefB.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role; the segments are lib/AU/Img0.v rsegs; role B's pcs (the arms DIG 0x80ce8 and ODD 0x815e0, the head's out-of-line range 0x81594 .. 0x81650 and the slow blocks 0x81a70 / 0x81b14), registers (p in s8, the kind byte's address in a6, the left side of the trap tests in s4) and the cursor's cell R+0x118; the cuts are lib/AU/RPgSeg.v's (rs_ names), the frame's shadow rows lib/AU/RPgMem.v's rm_sh; names rt7b_ -> r7b_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the two inner cut states of
   ent_build's case-0 head, the statements of its three blocks and the piece lemma from them. Proves no
   function (kind: statement text).

   THE CODE (pod.h:224-249, ent_headamp_key up to the end of the channel text ch). The piece runs from the jump
   table's case-0 target D0 = 0x80c14, or from D0E = 0x80c88 when no input byte is left (`beqz s2` 0x80b9c), to
   G = 0x80dc8, where the parts begin (lib/AU/RPgSeg.v rs_cut_D, rs_cut_D0E, rs_cut_G). At D0, a6 is the kind
   byte's address, s2 the cursor after it, s6 what is left after it, t1 what was left before it, s4 = 1 the left
   side of the trap tests and t2 = 10 (0x80ba8, the dispatch's `kind mod 10`); s3 = shadow_addr F, s11 the shadow
   offset. At D0E the cursor is in s8.
     0x80c14-0x80c40  t[96] in scope: 12 shadow bytes of F+0x20 := 0
     0x80c44          beqz s6 -> 0x80cc0: no input byte left for c
     0x80c48-0x80c50  the trap test of c's read (`addi a0,s2,1; bltu s4,a0`, trap 0x80c4c)
     0x80c54-0x80c64  c = fuzz_u8: the shadow check of the cursor (slow block 0x81a70), a3 := c (`lbu` 0x80c64)
     0x80c68-0x80c70  a0 := a6 + 2; bne t1, 2 -> 0x81594: a byte is left for p
     0x80c74-0x80c84  no byte for p: R+0x118 := a6 + 2, t1 := 0, s8 := 0, t3 := 9, j 0x815c4
     0x81594-0x815c0  p = fuzz_u8: the trap test (0x81598), t3 := 9 (0x815ac), the shadow check (slow block
                      0x81b14), s8 := p, t1 := t1 - 3, R+0x118 := a6 + 3
     0x815c4-0x815dc  ch[24] in scope: 3 shadow bytes of F+0xa0 := 0; s2 := [R+0xd0] = &ch, t0 := 4;
                      bgeu 199, a3 -> DIG (c < 200), else ODD
     0x80c88-0x80cbc  D0E: t in scope, t2 := 10, s2 := s8 (the cursor), then
     0x80cc0-0x80ce4  (also from 0x80c44) t1 := 0, s8 := 0, a3 := 0, ch in scope, R+0x118 := s2,
                      s2 := [R+0xd0], t0 := 4, t3 := 9; falls into DIG
     0x80ce8-0x80dc4  DIG, c < 200: the digits of c mod 64 into r[4] (r into scope 0x80cf0 with shadow byte 0x04;
                      the bound trap 0x80cfc; the store's check takes its slow block 0x80d58 inline), reversed into
                      ch (the read's check, slow block 0x80d9c inline), the NUL's trap 0x80db4 and its store, r out
                      of scope again (0x80dc4)
     0x815e0-0x81650  ODD, c >= 200: odd_ch[c mod 14] (the pointer table ent_headamp_key.odd_ch 0x9a820 in
                      .data.rel.ro; the trap 0x8160c; its 8-byte load is checked by `lbu; beqz +8; j` 0x81620-0x81628),
                      the strlen wrapper (0x41b60), __asan_memcpy (0x5116c) into ch, t1 back from s4, j G
   So the piece is three blocks: the head (D0 -> DIG / ODD, D0E -> DIG), DIG (-> G) and ODD (-> G). On every arm
   t1 = what is left of the input, s2 = &ch, s8 = p and R+0x118 the cursor, which G also carries. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgMem RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===================================== the two inner pcs ===================================== *)
Definition R7B_DIG : Z := 0x80ce8.   (* the digits of c mod 64, c < 200 (`li a2,0`) *)
Definition R7B_ODD : Z := 0x815e0.   (* odd_ch[c mod 14], c >= 200 (`auipc a1`) *)

(* The instruction table of the piece: the straight range D0 .. G (109 words, the digit and reverse loops' slow
   blocks 0x80d58 and 0x80d9c among them), the head's and ODD's out-of-line range 0x81594 .. 0x81650 (48 words)
   and the two out-of-line slow blocks the head's checks branch to (`andi u,x,7; blt u,t,<back>; j <report>`): c's
   read 0x81a70, p's read 0x81b14. The token engine must decode them. *)
Definition r7b_tbl : ctable :=
  build_table rsegs 0x80c14 109
  (build_table rsegs 0x81594 48
  (build_table rsegs 0x81a70 3
  (build_table rsegs 0x81b14 3 TEmpty))).
Lemma r7b_tbl_ok : table_ok rsegs r7b_tbl.
Proof.
unfold r7b_tbl.
apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.

(* The frame's shadow rows at the pcs of the piece, in RPgMem's words (the flags t ch r e e42 e62 role; e62 is in
   scope from the pod loop's stores 0x80b58 .. 0x80b88 and closes only after J). RPgSeg.rs_PJ (at D0 / D0E) and
   rs_PG (at DIG / ODD / G) are these words by definition. *)
(* after the t stores and before the ch stores *)
Definition r7b_PT : list Z := rm_sh true false false false false true false.
(* inside the digit and the reverse loops r is in scope as well (shadow byte 0x04, 0x80cf0) *)
Definition r7b_PR : list Z := rm_sh true true true false false true false.

(* What case 0 reads of the turn's input before the two arms: the kind byte, then c and p (pod.h:234); on an
   empty input fuzz_u8 gives 0 and does not move the cursor (fuzz.h:37-43). RPgSeg.rs_g_of is this with the
   channel text of c in place of c. *)
Definition r7b_cp_of (rr : list byte) : Z * Z * list byte :=
let '(_, r1) := Cursor.fuzz_u8 rr in
let '(c, r2) := Cursor.fuzz_u8 r1 in
let '(pb, r3) := Cursor.fuzz_u8 r2 in
(c, pb, r3).
Lemma r7b_g_of_cp : forall rr c pb r3,
(c, pb, r3) = r7b_cp_of rr ->
rs_g_of rr = (if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [], pb, r3).
Proof.
intros rr c pb r3 H. unfold rs_g_of, r7b_cp_of in *.
destruct (Cursor.fuzz_u8 rr) as [kd r1]. destruct (Cursor.fuzz_u8 r1) as [c' r2].
destruct (Cursor.fuzz_u8 r2) as [pb' r3']. injection H as <- <- <-. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================== the locations both inner cuts carry =====================
   RPgSeg.rs_L_Dc (rs_L_Dc0 and s10 = -8, the byte DIG's 0x80dc4 stores to close r) and the four values case 0
   holds at both arms and at G: t1 = what is left of the input, s2 = &ch, s8 = the key's second input byte p, and
   the cursor in the cell R+0x118. *)
Definition r7b_L_arm (cx : rs_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (pb : Z) : list (rl_loc * Z) :=
rs_L_Dc segs cx sh np ps cnt es
++ [(LReg 6, Z.of_nat (length r)); (LReg 18, e_F (x_e segs cx) + 0xa0); (LReg 24, pb);
    (LCell XR 0x118, rs_cur segs cx rest r)].

(* ---------------- DIG = 0x80ce8: the digits arm, c < 200 ----------------
   t and ch are in scope and r is not yet (its granule opens at 0x80cf0), so the frame's shadow row is
   RPgSeg.rs_PG, the row G also has. a3 = c, t0 = 4, t2 = 10 and t3 = 9 are the digit loop's four values
   (0x80c64 / 0x80cc8, 0x815d4 / 0x80ce0, 0x80ba8 / 0x80cb8, 0x80c80 / 0x815ac / 0x80ce4); the `v / 10`
   multiplier is s7 (rs_Rc0). *)
Definition r7b_cut_DIG (cx : rs_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base segs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx segs cx W2 mem2 regs2
(r7b_L_arm cx sh np ps cnt es rest r pb
 ++ [(LReg 13, c); (LReg 5, 4); (LReg 7, 10); (LReg 28, 9)]) /\
rs_fsh_at segs cx W2 mem2 rs_PG /\
rs_pp_at segs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e segs cx) + 0x210) (rs_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = r7b_cp_of rr /\
0 <= c < 200 /\ 0 <= pb < 256.

(* ---------------- ODD = 0x815e0: the table arm, c >= 200 ----------------
   The same row and the same four values; a3 = c. *)
Definition r7b_cut_ODD (cx : rs_scx segs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
rs_pod_base segs B MT cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
rs_at_cx segs cx W2 mem2 regs2
(r7b_L_arm cx sh np ps cnt es rest r pb ++ [(LReg 13, c)]) /\
rs_fsh_at segs cx W2 mem2 rs_PG /\
rs_pp_at segs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
garr8 segs (mrestrict (w_H W2) mem2) (e_F (x_e segs cx) + 0x210) (rs_u8s (zeros 104)) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = r7b_cp_of rr /\
200 <= c < 256 /\ 0 <= pb < 256.

(* ===================== the continuations of the two inner cuts ===================== *)
Section f.
Variable cx : rs_scx segs.
Variable POST : world segs -> config -> Prop.
Variable rest : list byte.
Definition r7b_from_DIG (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
r7b_cut_DIG cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs R7B_DIG regs2 mem2 md2) POST.
Definition r7b_from_ODD (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
r7b_cut_ODD cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (cfg_at segs R7B_ODD regs2 mem2 md2) POST.
End f.

(* ===================== the three block statements of the piece ===================== *)
(* the digits arm: from DIG to G, with the channel text dec64 (c mod 64) in ch *)
Definition r7b_dig_stmt : Prop :=
forall cx POST rest i k,
rs_start_M01 segs B cx rest -> rs_from_G segs B MT cx POST rest i k ->
r7b_from_DIG cx POST rest i k.
(* the table arm: from ODD to G, with odd_ch[c mod 14] in ch (the strlen wrapper and __asan_memcpy) *)
Definition r7b_odd_stmt : Prop :=
forall cx POST rest i k,
rs_start_M01 segs B cx rest -> rs_from_G segs B MT cx POST rest i k ->
r7b_from_ODD cx POST rest i k.
(* the head: both entries of case 0 to the two arms *)
Definition r7b_head_stmt : Prop :=
forall cx POST rest i k kd,
rs_start_M01 segs B cx rest -> kd mod 10 = 0 ->
r7b_from_DIG cx POST rest i k -> r7b_from_ODD cx POST rest i k ->
rs_from_D segs B MT cx POST rest i k kd /\ rs_from_D0E segs B MT cx POST rest i k.

(* ===================== the piece: RPgSeg.rs_piece_W7a_stmt from the three blocks ===================== *)
Lemma r7b_piece : r7b_head_stmt -> r7b_dig_stmt -> r7b_odd_stmt -> rs_piece_W7a_stmt segs B MT.
Proof.
intros HH HD HO cx POST rest i k kd Hst Hkd HG.
exact (HH cx POST rest i k kd Hst Hkd (HD cx POST rest i k Hst HG) (HO cx POST rest i k Hst HG)).
Qed.

End d.
End c.
End b.

Print Assumptions r7b_tbl_ok.
Print Assumptions r7b_g_of_cp.
Print Assumptions r7b_piece.
