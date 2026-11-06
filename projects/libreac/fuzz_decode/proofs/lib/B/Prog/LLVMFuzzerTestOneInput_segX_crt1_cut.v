(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_cut: the facts that carry the frame invariant and the memory clauses of image B's
   LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v dec_b_core and the clauses llvm_b_st_5cc and
   llvm_b_st_6f0 share) across the runs and the four calls of segment crt1 (+0x5cc .. +0x6ec).
   c1_mem is the memory part of a cut point; c1_step carries dec_b_core and c1_mem to a later state of the same
   frame from five "kept" facts (the spill area and the saved words but 80(s1), which the segment writes and carries
   apart, the fake frame, its shadow, the copy, the input payload); c1_keep_window gives those five from a call that keeps every byte outside its stack window and outside
   one written block (a program leaf, __asan_memset), c1_keep_acall from check_round_trip's acall_kept.
   PORT: c1_cell_view / c1_cell_agree / c1_val_mem_kept / c1_mode_kept / c1_mem_kept are
   lib/B/Prog/LLVMFuzzerTestOneInput_segX_up_kit.v up_cell_view / up_cell_agree / up_val_mem_kept / up_mode_kept /
   up_mem_kept (commit aea2a52bae6; the mode tables' +4 / +8 words through the read-only view as a Theorem Labs lane's
   8975dd26876 up_ro_agree / up_tab_ro), and c1_core_kept / c1_garr8_kept / c1_rom_covers / c1_ro_rd_covered /
   c1_in_rom / c1_rom_rd are lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_defs.v ex_core_kept / ex_garr8_kept
   (commit 44e7264cb0a) / ex_rom_covers / ex_ro_rd_covered / ex_in_rom / ex_rom_rd (a Theorem Labs lane's 38678070ce7),
   copied here so that this lane does not build on two lanes' working copies; c1_mem lists crt1's own slots. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally; this file uses the plain ones (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

Section C1Cut. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).

(* The memory clauses of every cut point of crt1 (llvm_b_st_5cc's, which llvm_b_st_6f0 repeats; 80(s1) is added by
   the segment itself and is carried apart). *)
Definition c1_mem (cx : dctx) (W : world segs) (mem : word -> option byte) (res out mode nch ns : Z) : Prop :=
  dec_b_frs cx (aview segs (w_H W) mem) /\
  dec_b_mode_ok cx W mem mode nch ns /\
  dec_b_fsh cx (aview segs (w_H W) mem) 0 4 /\
  garr8 segs (rd W mem) res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
  dec_b_slot cx (aview segs (w_H W) mem) 24 (dec_b_len (d_n cx)) /\
  dec_b_slot cx (aview segs (w_H W) mem) 32 SHADOW_OFF /\
  dec_b_slot cx (aview segs (w_H W) mem) 40 res /\
  dec_b_slot cx (aview segs (w_H W) mem) 56 (ns mod 2 ^ 32) /\
  dec_b_slot cx (aview segs (w_H W) mem) 64 (nch mod 2 ^ 32) /\
  dec_b_slot cx (aview segs (w_H W) mem) 72 (ns mod 2 ^ 64) /\
  dec_b_slot cx (aview segs (w_H W) mem) 88 out /\
  dec_b_slot cx (aview segs (w_H W) mem) 112 (d_F cx).

(* ---- constant cells (up_kit.v:79-106) ---- *)
Lemma c1_cell_view : forall ly S W mem md a w v k,
  AR segs B ly S W mem md -> In (ACell (ANum a) w (AV (ANum v))) (as_const B ly) -> (k < w)%nat ->
  aview segs (w_H W) mem (a + Z.of_nat k) = Some (le_byte v w k).
Proof.
  intros ly S W mem md a w v k HAR Hin Hk.
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as Hc.
  unfold cell_holds in Hc. cbn [c_at YG0f.c_val c_w aeval] in Hc. exact (Hc k Hk).
Qed.

Lemma c1_cell_agree : forall ly S W mem md ly2 S2 W2 mem2 md2 a w v,
  AR segs B ly S W mem md -> AR segs B ly2 S2 W2 mem2 md2 ->
  (forall l, In (ACell (ANum a) w (AV (ANum v))) (as_const B l)) ->
  forall j, 0 <= j < Z.of_nat w -> aview segs (w_H W2) mem2 (a + j) = aview segs (w_H W) mem (a + j).
Proof.
  intros ly S W mem md ly2 S2 W2 mem2 md2 a w v HAR HAR2 Hin j Hj.
  replace j with (Z.of_nat (Z.to_nat j)) by lia.
  rewrite (c1_cell_view ly2 S2 W2 mem2 md2 a w v (Z.to_nat j) HAR2 (Hin ly2) ltac:(lia)).
  rewrite (c1_cell_view ly S W mem md a w v (Z.to_nat j) HAR (Hin ly) ltac:(lia)).
  reflexivity.
Qed.

Lemma c1_val_mem_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a n v,
  (forall j, 0 <= j < Z.of_nat n -> aview segs H' m' (a + j) = aview segs H m (a + j)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
  intros H H' m m' a n v Hk Hv k Hkn. rewrite <- (Hv k Hkn). apply (mbyte_of_aview segs). apply Hk. lia.
Qed.

(* The rows of dec_crt_cells the mode clause reads as constant cells (check_round_trip_cg.v dec_crt_cells): the three
   pointer words and the value-4 shadow granule of each table. Each row is picked by its type, not its position. *)
Lemma c1_mode_rows : dec_crt_cells B ->
  (forall l, In (z8 (ANum (decodeb_obj 4%nat)) 0x20d60) (as_const B l)) /\
  (forall l, In (z8 (ANum (decodeb_obj 5%nat)) 0x20da0) (as_const B l)) /\
  (forall l, In (z8 (ANum (decodeb_obj 6%nat)) 0x20d80) (as_const B l)) /\
  (forall l, In (z1 (ANum (AsanCells.shadow_addr 0x20d68)) 4) (as_const B l)) /\
  (forall l, In (z1 (ANum (AsanCells.shadow_addr 0x20da8)) 4) (as_const B l)) /\
  (forall l, In (z1 (ANum (AsanCells.shadow_addr 0x20d88)) 4) (as_const B l)).
Proof.
  intros HC. unfold dec_crt_cells in HC.
  repeat split; intros l; specialize (HC l); decompose [and] HC; assumption.
Qed.

(* The value-0 shadow granule at each table's base, as dec_crt_cells states it: a fact of the record
   (dec_tab_zshadow_at), which check_round_trip_cg.v dec_tab_zshadow_rd reads at an AR state. ly is any layout:
   the rows are stated under `forall ly`, and these three do not depend on it. *)
Lemma c1_tab_zshadow : dec_crt_cells B -> forall ly : alayout,
  dec_tab_zshadow_at B 0x20d60 /\ dec_tab_zshadow_at B 0x20da0 /\ dec_tab_zshadow_at B 0x20d80.
Proof.
  intros HC ly. unfold dec_crt_cells in HC. specialize (HC ly). decompose [and] HC.
  split; [assumption | split; assumption].
Qed.

(* ---- the read-only view at the DEC_RO_RD bytes (exit_defs.v ex_rom_covers .. ex_rom_rd) ---- *)
Definition c1_rom_covers (a n : Z) : bool :=
  existsb (fun s : Segment => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
    (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool segs.
Lemma c1_ro_rd_covered : forallb (fun r => c1_rom_covers (fst r) (snd r)) DEC_RO_RD = true.
Proof. vm_compute. reflexivity. Qed.
Lemma c1_in_rom : forall a, dec_in_ro_rd a -> in_rom segs a /\ in_img segs a.
Proof.
  intros a Ha. unfold dec_in_ro_rd in Ha. apply Exists_exists in Ha as ([lo n] & Hin & Hz).
  pose proof c1_ro_rd_covered as Hc. rewrite forallb_forall in Hc. specialize (Hc _ Hin).
  unfold c1_rom_covers in Hc. cbn [fst snd] in Hc. apply existsb_exists in Hc as (sg & Hsg & Hb).
  apply andb_true_iff in Hb as [Hb Hhi]. apply andb_true_iff in Hb as [Hw Hlo].
  apply negb_true_iff in Hw. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  unfold in_zr in Hz. cbn [fst snd] in Hz.
  split; exists sg; (split; [exact Hsg|]); [split; [exact Hw|] |]; lia.
Qed.

(* The scoped read-only view (dec_rom_view_rd) at any state the slot's journal reaches, from the entry's rom_view
   (dec_b_rom), the journal's image clause (YCbq.v:362) and dec_ro_rd_scoped. *)
Lemma c1_rom_rd : forall cx STK own ly' S' W' mem' md' k,
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  rom_view segs (d_W cx) (d_mem cx) ->
  @ajournal rc dec_B_sink_head segs B STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    own ly' S' W' mem' md' k ->
  dec_rom_view_rd W' mem'.
Proof.
  intros cx STK own ly' S' W' mem' md' k HO HE HR HJ a Ha.
  destruct (dec_ro_rd_scoped B HO HE a Ha) as [Hno Hne]. destruct (c1_in_rom a Ha) as [Hr Hi].
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Hi Hno Hne); [exact (HR a Hr)|].
  apply fp_spares_closed. intros Ho. exact (sink_closed_nil Ho).
Qed.

(* The same at the frame invariant's journal. *)
Lemma c1_rom_core : forall cx ly S W regs mem md k,
  dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_b_rom cx ->
  dec_b_core B cx ly S W regs mem md k -> dec_rom_view_rd W mem.
Proof.
  intros cx ly S W regs mem md k HO HE HR (HJ & _). exact (c1_rom_rd cx _ _ _ _ _ _ _ _ HO HE HR HJ).
Qed.

(* Two states whose read-only view shows the image at the DEC_RO_RD bytes agree there. *)
Lemma c1_ro_agree : forall (W W2 : world segs) mem mem2,
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  forall a, dec_in_ro_rd a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a.
Proof. intros W W2 mem mem2 HR HR2 a Ha. rewrite (HR2 a Ha), (HR a Ha). reflexivity. Qed.

(* The +4 / +8 words of the three mode tables are DEC_RO_RD bytes. *)
Lemma c1_tab_ro : forall t a, t = 0x20d60 \/ t = 0x20da0 \/ t = 0x20d80 -> t + 4 <= a < t + 12 -> dec_in_ro_rd a.
Proof.
  intros t a Ht Ha. unfold dec_in_ro_rd. apply Exists_exists.
  exists (t + 4, 8). split; [|unfold in_zr; cbn [fst snd]; lia].
  unfold DEC_RO_RD. destruct Ht as [-> | [-> | ->]]; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

(* up_kit.v:109-163: the pointer word is a constant cell, the two fields are DEC_RO_RD bytes (the image at both
   states), the local mode lies in the fake frame. *)
Lemma c1_mode_kept : forall cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns,
  dec_crt_cells B ->
  AR segs B ly S W mem md -> AR segs B ly2 S2 W2 mem2 md2 ->
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  dec_b_mode_ok cx W mem mode nch ns -> dec_b_mode_ok cx W2 mem2 mode nch ns.
Proof.
  intros cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns HC HAR HAR2 HRO HRO2 KF (Hsrc & Hb1 & Hb2 & V4 & V8).
  assert (CELL : forall a w v, (forall l, In (ACell (ANum a) w (AV (ANum v))) (as_const B l)) ->
    forall j, 0 <= j < Z.of_nat w -> aview segs (w_H W2) mem2 (a + j) = aview segs (w_H W) mem (a + j))
    by (intros a w v Hin; exact (c1_cell_agree ly S W mem md ly2 S2 W2 mem2 md2 a w v HAR HAR2 Hin)).
  destruct (c1_mode_rows HC) as (R4 & R5 & R6 & _).
  assert (TAB : forall q t, t = 0x20d60 \/ t = 0x20da0 \/ t = 0x20d80 ->
    (forall l, In (z8 (ANum q) t) (as_const B l)) ->
    rdword (aview segs (w_H W) mem) q = Some mode ->
    rdword (aview segs (w_H W2) mem2) q = Some mode /\
    val_mem segs (mrestrict (w_H W2) mem2) (mode + 4) 4%nat (nch mod 2 ^ 32) /\
    val_mem segs (mrestrict (w_H W2) mem2) (mode + 8) 4%nat (ns mod 2 ^ 32)).
  { intros q t Ht Rq Hq.
    assert (Htr : 0 <= t < 18446744073709551616) by (destruct Ht as [-> | [-> | ->]]; lia).
    assert (Hw : rdword (aview segs (w_H W) mem) q = Some t).
    { eapply rdword_cell; [change (2 ^ 64) with 18446744073709551616; exact Htr|].
      exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ (Rq ly)). }
    rewrite Hw in Hq. injection Hq as Hq. subst mode.
    split; [rewrite <- Hw; apply rdword_ext; intros j Hj; apply (CELL q 8%nat t Rq); lia|].
    split; apply (c1_val_mem_kept (w_H W) (w_H W2) mem mem2); [| exact V4 | | exact V8];
      intros j Hj; apply (c1_ro_agree W W2 mem mem2 HRO HRO2); apply (c1_tab_ro t); first [exact Ht | lia]. }
  destruct Hsrc as [H4 | [H5 | [H6 | Hloc]]].
  - destruct (TAB (decodeb_obj 4%nat) 0x20d60 (or_introl eq_refl) R4 H4) as (Q1 & Q2 & Q3).
    split; [left; exact Q1|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Q2 | exact Q3].
  - destruct (TAB (decodeb_obj 5%nat) 0x20da0 (or_intror (or_introl eq_refl)) R5 H5) as (Q1 & Q2 & Q3).
    split; [right; left; exact Q1|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Q2 | exact Q3].
  - destruct (TAB (decodeb_obj 6%nat) 0x20d80 (or_intror (or_intror eq_refl)) R6 H6) as (Q1 & Q2 & Q3).
    split; [right; right; left; exact Q1|]. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Q2 | exact Q3].
  - subst mode. split; [right; right; right; reflexivity|]. split; [exact Hb1|]. split; [exact Hb2|].
    split; apply (c1_val_mem_kept (w_H W) (w_H W2) mem mem2); [| exact V4 | | exact V8];
      intros j Hj; apply KF; lia.
Qed.

(* exit_defs.v:76-83. *)
Lemma c1_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview segs H' m' (base + i) = aview segs H m (base + i)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
  intros H H' m m' base l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  intros k Hk8. rewrite <- (Hv k Hk8). apply (mbyte_of_aview segs).
  replace (base + Z.of_nat j + Z.of_nat k) with (base + (Z.of_nat j + Z.of_nat k)) by lia. apply Hk. lia.
Qed.

(* up_kit.v:167-192, at crt1's slots; the read-only views at both states are for c1_mode_kept. *)
Lemma c1_mem_kept : forall cx ly S W mem md ly2 S2 W2 mem2 md2 res out mode nch ns,
  dec_crt_cells B ->
  AR segs B ly S W mem md -> AR segs B ly2 S2 W2 mem2 md2 ->
  dec_rom_view_rd W mem -> dec_rom_view_rd W2 mem2 ->
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 ->
  (forall a, d_sp1 cx <= a < d_sp0 cx -> ~ (d_sp1 cx + 80 <= a < d_sp1 cx + 88) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall i, 0 <= i < Z.of_nat (length (d_body cx)) ->
     aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) mem (res + i)) ->
  c1_mem cx W mem res out mode nch ns -> c1_mem cx W2 mem2 res out mode nch ns.
Proof.
  intros cx ly S W mem md ly2 S2 W2 mem2 md2 res out mode nch ns HC HAR HAR2 HRO HRO2 Hsp1 KS KF KH KR
    ((F0 & F8 & F16) & Hmode & (H0 & H4 & H5 & H6) & Hg & S24 & S32 & S40 & S56 & S64 & S72 & S88 & S112).
  assert (SLOT : forall off v, 0 <= off <= 112 -> off + 8 <= 80 \/ 88 <= off ->
    dec_b_slot cx (aview segs (w_H W) mem) off v -> dec_b_slot cx (aview segs (w_H W2) mem2) off v).
  { intros off v Hoff Hov Hs. unfold dec_b_slot in *. rewrite <- Hs. apply rdword_ext. intros j Hj. apply KS; lia. }
  split; [split; [apply SLOT; [lia | lia | exact F0] | split; [apply SLOT; [lia | lia | exact F8] | apply SLOT; [lia | lia | exact F16]]]|].
  split; [exact (c1_mode_kept cx ly S W mem md ly2 S2 W2 mem2 md2 mode nch ns HC HAR HAR2 HRO HRO2 KF Hmode)|].
  split.
  { split; [intros i Hi; rewrite KH by lia; exact (H0 i Hi)|].
    split; [rewrite KH by lia; exact H4|]. split; [rewrite KH by lia; exact H5|].
    intros i Hi; rewrite KH by lia; exact (H6 i Hi). }
  split; [apply (c1_garr8_kept (w_H W) (w_H W2) mem mem2); [rewrite length_map; exact KR | exact Hg]|].
  split; [apply SLOT; [lia | lia | exact S24]|]. split; [apply SLOT; [lia | lia | exact S32]|].
  split; [apply SLOT; [lia | lia | exact S40]|]. split; [apply SLOT; [lia | lia | exact S56]|].
  split; [apply SLOT; [lia | lia | exact S64]|]. split; [apply SLOT; [lia | lia | exact S72]|].
  split; [apply SLOT; [lia | lia | exact S88] | apply SLOT; [lia | lia | exact S112]].
Qed.

(* exit_defs.v:87-120. *)
Lemma c1_core_kept : forall cx ly S W regs mem md k ly2 S2 W2 regs2 mem2 md2 k2,
  dec_b_core B cx ly S W regs mem md k ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  frames S2 = [(DEC_FCLASS, d_fpos cx)] ->
  YK11.getr regs2 8 = YK11.getr regs 8 -> YK11.getr regs2 9 = YK11.getr regs 9 -> spZ regs2 = spZ regs ->
  YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  (forall a, d_sp0 cx - 104 <= a < d_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W2) mem2 a) ->
  (0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B ly2 S2)) ->
  (forall i, 0 <= i < Z.of_nat (length (d_pl cx)) ->
     aview segs (w_H W2) mem2 (d_p cx + i) = aview segs (w_H W) mem (d_p cx + i)) ->
  dec_b_core B cx ly2 S2 W2 regs2 mem2 md2 k2.
Proof.
  intros cx ly S W regs mem md k ly2 S2 W2 regs2 mem2 md2 k2 Hcore HJ2 Hfr2 E8 E9 Esp E3 E4 Ksv KF PF Hpay2 Kpay.
  destruct Hcore as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
    HFLw & Hpay & Hgarr).
  unfold dec_b_core.
  split; [exact HJ2|]. split; [exact Hfr2|].
  split; [rewrite E8; exact Hs0|]. split; [rewrite E9; exact Hs1|]. split; [rewrite Esp; exact Hsp|].
  split; [exact Hsp1r|]. split; [exact Hsp1al|]. split; [rewrite E3; exact Hgp|]. split; [rewrite E4; exact Htp|].
  split.
  { unfold dec_b_saved in *. rewrite Forall_forall in Hsaved |- *. intros o Hin. specialize (Hsaved o Hin).
    assert (Hb : 8 <= fst o <= 104).
    { unfold dec_b_saved_at in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [cbn [fst]; lia|]). destruct Hin. }
    rewrite <- Hsaved. apply rdword_ext. intros j Hj. apply Ksv. lia. }
  split; [exact HF4096|]. split; [exact HFal|]. split; [exact PF|].
  split; [rewrite <- HFLw; apply rdword_ext; intros j Hj; apply KF; lia|].
  split; [exact Hpay2|].
  apply (c1_garr8_kept (w_H W) (w_H W2) mem mem2); [|exact Hgarr].
  rewrite length_map. exact Kpay.
Qed.

(* ---- one step of the frame: dec_b_core and c1_mem at a later state ---- *)
(* The two instance facts and the entry's rom_view give the read-only view at both states (c1_rom_core /
   c1_rom_rd), which the mode clause reads the tables' fields through. *)
Lemma c1_step : forall cx ly S W regs mem md k res out mode nch ns ly2 S2 W2 regs2 mem2 md2 k2,
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_b_rom cx ->
  dec_b_core B cx ly S W regs mem md k -> c1_mem cx W mem res out mode nch ns ->
  @ajournal rc dec_B_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  frames S2 = [(DEC_FCLASS, d_fpos cx)] ->
  (forall b, In b (ablocks B ly S) -> In b (ablocks B ly2 S2)) ->
  YK11.getr regs2 8 = YK11.getr regs 8 -> YK11.getr regs2 9 = YK11.getr regs 9 -> spZ regs2 = spZ regs ->
  YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  (forall a, d_sp1 cx <= a < d_sp0 cx -> ~ (d_sp1 cx + 80 <= a < d_sp1 cx + 88) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a /\
     apresent (w_H W2) mem2 a) ->
  (forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall i, 0 <= i < Z.of_nat (length (d_body cx)) ->
     aview segs (w_H W2) mem2 (res + i) = aview segs (w_H W) mem (res + i)) ->
  (forall i, 0 <= i < Z.of_nat (length (d_pl cx)) ->
     aview segs (w_H W2) mem2 (d_p cx + i) = aview segs (w_H W) mem (d_p cx + i)) ->
  dec_b_core B cx ly2 S2 W2 regs2 mem2 md2 k2 /\ c1_mem cx W2 mem2 res out mode nch ns.
Proof.
  intros cx ly S W regs mem md k res out mode nch ns ly2 S2 W2 regs2 mem2 md2 k2 HC HO HE HR Hcore Hmem HJ2 Hfr2 Hbl
    E8 E9 Esp E3 E4 KS KF KH KR KP.
  pose proof Hcore as (HJ & _ & _ & _ & _ & Hsp1r & _ & _ & _ & _ & _ & _ & _ & _ & Hpay & _).
  pose proof (c1_rom_core cx ly S W regs mem md k HO HE HR Hcore) as HRO.
  pose proof (c1_rom_rd cx _ _ _ _ _ _ _ _ HO HE HR HJ2) as HRO2.
  split.
  - apply (c1_core_kept cx ly S W regs mem md k ly2 S2 W2 regs2 mem2 md2 k2 Hcore HJ2 Hfr2 E8 E9 Esp E3 E4).
    + intros a Ha. apply KS; lia.
    + intros a Ha. exact (proj1 (KF a Ha)).
    + intros a Ha. exact (proj2 (KF a Ha)).
    + intros Hn. exact (Hbl _ (Hpay Hn)).
    + exact KP.
  - apply (c1_mem_kept cx ly S W mem md ly2 S2 W2 mem2 md2 res out mode nch ns HC (proj1 HJ) (proj1 HJ2) HRO HRO2
             Hsp1r KS).
    + intros a Ha. exact (proj1 (KF a Ha)).
    + exact KH.
    + exact KR.
    + exact Hmem.
Qed.
End C1Cut.
