(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the two inner cut states of
   ent_build's case 0 head in LLVMFuzzerTestOneInput 0x80c40, the statements of its three blocks and their
   composition into HPgSeg.hsu_piece_W7a_stmt. Proves no function (kind: segment lemma).

   THE CODE (pod.h:224-249, ent_headamp_key up to the end of the channel text ch). The piece runs from the jump
   table's case-0 target D = 0x8194c, or from D0E = 0x819c0 when no input byte is left, to G = 0x81afc, where the
   parts begin (lib/AU/HPgSeg.v hsu_cut_D, hsu_cut_D0E, hsu_cut_G at headamp_bld_B).
     0x8194c-0x81978  t[96] in scope: 12 shadow bytes of F+0x20 := 0 (granules 4 .. 15)
     0x8197c          beqz s4: no input byte left after the kind byte
     0x82294-0x82298  (s4 = 0) s5 := s2, j 0x819f4
     0x81980-0x8199c  c = fuzz_u8: the UBSan test `bltu a6,s2+1` (a6 = 1), the shadow check of the cursor s2
                      (slow block 0x827c4), then `lbu a3,0(s2)`
     0x819a0-0x819ac  a0 := a7 + 2, t3 := 9; `bne t1,2`: a second byte is left
     0x819b0-0x819bc  (t1 = 2) R+0x110 := a0, t1 := 0, s10 := 0 (p = 0), j 0x822fc
     0x822d0-0x822f8  p = fuzz_u8: the UBSan test, the shadow check of a0 (slow block 0x82868), `lbu s10,0(a0)`,
                      R+0x110 := a7 + 3, t1 := t1 - 3
     0x822fc-0x82314  ch[24] in scope: 3 shadow bytes of F+0xa0 := 0 (granules 20 .. 22), s2 := [R+0xc8] = &ch,
                      t0 := 4, `bgeu 0xc7,a3`: c < 200 to DIG, else ODD
     0x819c0-0x819f0  D0E: the t stores, t2 := 10
     0x819f4-0x81a18  no byte for c: t3 := 9, t1 := 0, s10 := 0, a3 := 0 (c = p = 0), the ch stores,
                      R+0x110 := s5, s2 := [R+0xc8], t0 := 4, then DIG
     0x81a1c-0x81af8  DIG, c < 200: the digits of c mod 64 into r[4] (r in scope with shadow 0x04 at 0x81a24, the
                      `% 10` by mulhu with s8, a UBSan test `bne a2,t0` per digit), reversed into ch, the
                      pointer-overflow test of &ch[n] against [R+0xc0] = ~&ch, its NUL, r out of scope (s7 = -8)
     0x82318-0x82388  ODD, c >= 200: odd_ch[c mod 14] (the cell 0x9c560 + 8 (c mod 14) of .data.rel.ro, the
                      pointer-overflow test of its offset, its shadow check), strlen through 0x41c18,
                      __asan_memcpy 0x51d8c into ch, t1 kept in s5 across the two calls, j G
   So the piece is three blocks: the head (D and D0E to DIG / ODD), DIG and ODD (both to G). The registers and
   real-frame cells the inner cuts name are image B's: s0 = S, s1 = R, s3 = (F >> 3) + K, s11 = K, s8 = the `/ 10`
   multiplier, s6 = &r = F+0xe0, s9 = &t = F+0x20, s2 = &ch = F+0xa0, s10 = p, t1 = what is left of the input,
   a3 = c, t0 = 4, t3 = 9, t2 = 10, s7 = -8; R+0x110 = the cursor after c and p, R+0xc0 = ~&ch, R+0xc8 = &ch and
   the cells of HPgSeg.hsu_L_Dc. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Accessors Spa Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ===================================== the two inner pcs ===================================== *)
Definition E0_DIG : Z := 0x81a1c.   (* the digits of c mod 64, c < 200 *)
Definition E0_ODD : Z := 0x82318.   (* odd_ch[c mod 14], c >= 200 *)

(* The instruction table of the piece: its three straight ranges and the two slow blocks the input reads branch
   to (`andi u,x,7; blt u,t,<back>; j <report>`); the slow blocks of the r and ch checks of DIG (0x81a8c, 0x81ad0)
   lie inside the first range. *)
Definition e0_tbl : ctable :=
  build_table rsegs 0x8194c 108            (* 0x8194c .. 0x81af8: D, D0E, the 0x819f4 path, DIG *)
  (build_table rsegs 0x82294 2             (* 0x82294 .. 0x82298: s4 = 0 *)
  (build_table rsegs 0x822d0 47            (* 0x822d0 .. 0x82388: p, the ch stores, the arm test, ODD *)
  (build_table rsegs 0x827c4 3             (* the slow block of the read of c *)
  (build_table rsegs 0x82868 3 TEmpty)))). (* the slow block of the read of p *)
Lemma e0_tbl_ok : table_ok rsegs e0_tbl.
Proof.
unfold e0_tbl.
apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok; [lia|].
apply build_table_ok; [lia|]. apply build_table_ok0. lia.
Qed.

(* The frame's shadow row at the pcs of the piece, in HPgMem's words (hmu_sh t ch r e e42 e62 res x): e62 is in
   scope from the pod loop's stores 0x8188c .. 0x818bc and closes only after the join. *)
Lemma e0_PJ_sh : hsu_PJ headamp_himg_B = hmu_sh false false false false false true false false.
Proof. vm_compute. reflexivity. Qed.
Lemma e0_PG_sh : hsu_PG headamp_himg_B = hmu_sh true true false false false true false false.
Proof. vm_compute. reflexivity. Qed.
(* after the t stores and before the ch stores *)
Definition e0_PT : list Z := hmu_sh true false false false false true false false.
(* inside the digits and the reverse loop r is in scope as well (shadow byte 0x04, 0x81a24) *)
Definition e0_PR : list Z := hmu_sh true true true false false true false false.

(* What case 0 reads of the turn's input before the two arms: the kind byte, then c and p (pod.h:234); on an
   empty input fuzz_u8 gives 0 and does not move the cursor (fuzz.h:37-43). HPgSeg.hsu_g_of is this with the
   channel text of c in place of c. *)
Definition e0_cp_of (rr : list byte) : Z * Z * list byte :=
let '(_, r1) := Cursor.fuzz_u8 rr in
let '(c, r2) := Cursor.fuzz_u8 r1 in
let '(pb, r3) := Cursor.fuzz_u8 r2 in
(c, pb, r3).
Lemma e0_g_of_cp : forall rr c pb r3,
(c, pb, r3) = e0_cp_of rr ->
hsu_g_of rr = (if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [], pb, r3).
Proof.
intros rr c pb r3 H. unfold hsu_g_of, e0_cp_of in *.
destruct (Cursor.fuzz_u8 rr) as [kd r1]. destruct (Cursor.fuzz_u8 r1) as [c' r2].
destruct (Cursor.fuzz_u8 r2) as [pb' r3']. injection H as <- <- <-. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Arguments x_e {segs} _.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================== the locations both inner cuts carry =====================
   HPgSeg.hsu_L_Dc and the four values case 0 holds at both arms and at G: R+0x110 = the cursor after c and p,
   t1 = what is left of the input, s2 = &ch, s10 = p. This list IS the location list of hsu_cut_G. *)
Definition e0_L_arm (cx : hsu_scx rsegs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest r : list byte) (pb : Z) : list (hd_loc * Z) :=
hsu_L_Dc rsegs cx sh np ps cnt es
++ [(LCell XR 0x110, hsu_cur rsegs cx rest r); (LReg 6, Z.of_nat (length r));
    (LReg 18, e_F (x_e cx) + HSU_CH); (LReg 26, pb)].

(* ---------------- DIG = 0x81a1c: the digits arm, c < 200 ----------------
   t and ch are in scope and r is not yet (its granule opens at 0x81a24), so the frame's shadow row is
   HPgSeg.hsu_PG, the row G also has. a3 = c, t0 = 4 (r's shadow byte and the digit count's UBSan bound),
   t3 = 9 and t2 = 10 are the digit loop's constants, s7 = -8 the byte that closes r again. *)
Definition e0_cut_DIG (cx : hsu_scx rsegs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx rsegs cx W2 mem2 regs2
(e0_L_arm cx sh np ps cnt es rest r pb
 ++ [(LReg 13, c); (LReg 5, 4); (LReg 28, 9); (LReg 7, 10); (LReg 23, -8)]) /\
hsu_fsh_at rsegs cx W2 mem2 (hsu_PG headamp_himg_B) /\
hsu_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
hsu_obj_at rsegs cx W2 mem2 HSU_E62 (zeros 104) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = e0_cp_of rr /\
0 <= c < 200 /\ 0 <= pb < 256.

(* ---------------- ODD = 0x82318: the table arm, c >= 200 ----------------
   The same row and the same arm locations; a3 = c. *)
Definition e0_cut_ODD (cx : hsu_scx rsegs) (sh np : Z) (ps : list (Z * pval)) (cnt : Z) (es : list ent)
(rest rr r : list byte) (c pb : Z) ly2 S2 W2 regs2 mem2 md2 : Prop :=
hsu_pod_base rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r ly2 S2 W2 regs2 mem2 md2 /\
hsu_at_cx rsegs cx W2 mem2 regs2 (e0_L_arm cx sh np ps cnt es rest r pb ++ [(LReg 13, c)]) /\
hsu_fsh_at rsegs cx W2 mem2 (hsu_PG headamp_himg_B) /\
hsu_pp_at rsegs cx W2 mem2 (pc_image (PbCut sh ps (Some es))) /\
hsu_obj_at rsegs cx W2 mem2 HSU_E62 (zeros 104) /\
fst (Cursor.fuzz_u8 rr) mod 10 = 0 /\ (c, pb, r) = e0_cp_of rr /\
200 <= c < 256 /\ 0 <= pb < 256.

(* ===================== the continuations of the two inner cuts ===================== *)
Section f.
Variable cx : hsu_scx rsegs.
Variable POST : world rsegs -> config -> Prop.
Variable rest : list byte.
Definition e0_from_DIG (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
e0_cut_DIG cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (cfg_at rsegs E0_DIG regs2 mem2 md2) POST.
Definition e0_from_ODD (i k : nat) : Prop :=
forall ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r c pb,
(length ps = i)%nat -> (length es = k)%nat ->
e0_cut_ODD cx sh np ps cnt es rest rr r c pb ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (cfg_at rsegs E0_ODD regs2 mem2 md2) POST.
End f.

(* ===================== the three block statements of the piece =====================
   Together they give HPgSeg.hsu_piece_W7a_stmt at headamp_himg_B / headamp_bld_B (lib/AU/HPgE0.v). *)
(* the digits arm: from DIG to G, with the channel text dec64 (c mod 64) in ch *)
Definition e0_dig_stmt : Prop :=
forall cx POST rest i k,
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
hsu_from_G rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i k ->
e0_from_DIG cx POST rest i k.
(* the table arm: from ODD to G, with odd_ch[c mod 14] in ch (the strlen wrapper and __asan_memcpy) *)
Definition e0_odd_stmt : Prop :=
forall cx POST rest i k,
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
hsu_from_G rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i k ->
e0_from_ODD cx POST rest i k.
(* the head: both entries of case 0 to the two arms *)
Definition e0_head_stmt : Prop :=
forall cx POST rest i k kd,
hsu_start_M01 rsegs B headamp_himg_B cx rest -> kd mod 10 = 0 ->
e0_from_DIG cx POST rest i k -> e0_from_ODD cx POST rest i k ->
hsu_from_D rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i k kd /\
hsu_from_D0E rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i k.

(* the piece is the three blocks in a row: the head to the two arms, each arm to G *)
Lemma e0_piece_of_blocks : e0_head_stmt -> e0_dig_stmt -> e0_odd_stmt ->
hsu_piece_W7a_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
intros Hh Hd Ho cx POST rest i k kd HST Hkd HG.
exact (Hh cx POST rest i k kd HST Hkd (Hd cx POST rest i k HST HG) (Ho cx POST rest i k HST HG)).
Qed.

End d.
End b.

Print Assumptions e0_tbl_ok.
Print Assumptions e0_PJ_sh.
Print Assumptions e0_PG_sh.
Print Assumptions e0_g_of_cp.
Print Assumptions e0_piece_of_blocks.
