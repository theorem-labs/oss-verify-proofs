(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AHandoffLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AMainEntry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AEntryLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_initR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstate.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_img.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kitL.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_init1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RT_initK.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared.InitMem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AHandoffLib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.MainExport.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AMainEntry.MainFactsBoth.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AEntryLib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_initR.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate.RT_artR OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_img OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kitL OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_init1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section GET.
Variables (V : nat -> Z) (m : word -> option byte) (l : list mfact).
Hypothesis HF : Forall (mfact_ok bsegs V m) l.

Lemma G_cell : forall a w v, existsb (mfact_eqb (MCell a w v)) l = true -> rw_cells bsegs m (zv V a) [cellw w (zv V v)].
Proof. intros a w v H. exact (mfact_find bsegs V m l (MCell a w v) HF H). Qed.
Lemma G_zeroc : forall a n, existsb (mfact_eqb (MZeroC a n)) l = true -> rw_cells bsegs m (zv V a) [CB (Z.to_nat n) (zeros n)].
Proof. intros a n H. exact (mfact_find bsegs V m l (MZeroC a n) HF H). Qed.
Lemma G_zero : forall a n, existsb (mfact_eqb (MZero a n)) l = true -> 0 <= zv V a -> zv V a + n <= 2^64 -> zfill m (zv V a) n.
Proof. intros a n H H0 H1. split; [exact H0|]. split; [exact H1|]. exact (mfact_find bsegs V m l (MZero a n) HF H). Qed.
Lemma G_fill : forall a n c, existsb (mfact_eqb (MFill a n c)) l = true -> 0 <= zv V a -> zv V a + n <= 2^64 -> bfill m (zv V a) n c.
Proof. intros a n c H H0 H1. split; [exact H0|]. split; [exact H1|]. exact (mfact_find bsegs V m l (MFill a n c) HF H). Qed.
Lemma G_wr : forall a n, existsb (fun f => match f with MWr a' n' => zexp_eqb a' a && (n' =? n) | _ => false end) l = true -> wr_at bsegs m (zv V a) n.
Proof. intros a n H. exact (mwr_find bsegs V m l a n HF H). Qed.
Lemma G_img : forall lo hi, existsb (fun f => match f with MImg lo' hi' => (lo' <=? lo) && (hi <=? hi') | _ => false end) l = true -> pristine m lo hi.
Proof. intros lo hi H x Hx. exact (mimg_cover bsegs V m l lo hi HF H x Hx). Qed.
(* [comment removed for export] *)
Lemma G_chunk : forall A cs, cells_wf cs -> AEntryLib.fchk bsegs l A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 -> rw_cells bsegs m A cs.
Proof. intros A cs W C H0 H1. exact (chunk_of_facts bsegs V m l A cs HF W C H0 H1). Qed.
End GET.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KIT.
Variable m : word -> option byte.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_img : forall a cs, cells_at bsegs m a cs -> ASEG2_LO <= a -> a + Z.of_nat (cells_size cs) <= AIMG_HI ->
  rw_cells bsegs m a cs.
Proof.
  intros a cs H H1 H2. split; [exact H|]. unfold ASEG2_LO, AIMG_HI in *. split; [lia|]. split; [lia|].
  intros i Hi. apply img_rw_wview. unfold ASEG2_LO, AIMG_HI. lia.
Qed.
Lemma rw_wr : forall a cs lo n, cells_at bsegs m a cs -> wr_at bsegs m lo n -> lo <= a ->
  a + Z.of_nat (cells_size cs) <= lo + n -> rw_cells bsegs m a cs.
Proof. intros a cs lo n H W H1 H2. split; [exact H|]. eapply wr_at_sub; [exact W| lia| lia]. Qed.

(* [comment removed for export] *)
Lemma bytes_eq_unsigned : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma cells_recast : forall A cs cs', cells_at bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  cells_at bsegs m A cs'.
Proof. intros A cs cs' [W B] W' E. split; [exact W'| rewrite E; exact B]. Qed.
Lemma rw_recast : forall A cs cs', rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  cells_size cs' = cells_size cs -> rw_cells bsegs m A cs'.
Proof. intros. eapply rw_cells_recast; eauto. Qed.

(* [comment removed for export] *)
Lemma zfill_cells : forall a n off cs, zfill m a n -> 0 <= off -> off + Z.of_nat (cells_size cs) <= n -> cells_wf cs ->
  cells_bytes cs = repeat (zb 0) (cells_size cs) -> rw_cells bsegs m (a + off) cs.
Proof.
  intros a n off cs (Z1 & Z2 & Z) Ho Hn W E. pose proof (cells_bytes_length cs W) as L. split; [split; [exact W|]|].
  - unfold bytes_at. rewrite L. split; [lia|]. split; [lia|]. intros i Hi. unfold mrd.
    replace (a + off + Z.of_nat i) with (a + (off + Z.of_nat i)) by lia. rewrite Z by lia. rewrite E.
    symmetry. rewrite (nth_error_repeat (zb 0) Hi). reflexivity.
  - unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. rewrite wview_empty.
    replace (a + off + i) with (a + (off + i)) by lia. rewrite Z by lia. discriminate.
Qed.
Lemma zfill_junk : forall a n off k, zfill m a n -> 0 <= off -> off + k <= n -> 0 <= k ->
  exists j, rw_cells bsegs m (a + off) [CB (Z.to_nat k) j].
Proof.
  intros a n off k Z Ho Hk Hk0. exists (repeat (zb 0) (Z.to_nat k)). apply (zfill_cells a n off); try assumption.
  - cbn. lia.
  - cbn. rewrite repeat_length. split; [reflexivity| exact I].
  - cbn. rewrite app_nil_r, Nat.add_0_r. reflexivity.
Qed.
Lemma zfill_vis : forall a n lo hi, zfill m a n -> a <= lo -> hi <= a + n -> stk bsegs m lo hi.
Proof.
  intros a n lo hi (Z1 & Z2 & Z) H1 H2. split; [lia|]. split; [lia|]. intros x Hx.
  replace x with (a + (x - a)) by lia. split.
  - rewrite wview_empty. rewrite Z by lia. discriminate.
  - unfold mrd. rewrite Z by lia. eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wr_vis : forall lo n, wr_at bsegs m lo n -> AIMG_HI <= lo -> stk bsegs m lo (lo + n).
Proof.
  intros lo n (W1 & W2 & W) H. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (W (a - lo) ltac:(lia)) as Wa. replace (lo + (a - lo)) with a in Wa by lia. split; [exact Wa|].
  pose proof (wview_noseg_some m (wa a) (noseg_Z a ltac:(lia)) Wa) as S.
  unfold mrd. destruct (m (wa a)) as [b|]; [exists b; reflexivity| exfalso; apply S; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma wr_vis_o : forall lo n a b, wr_at bsegs m lo n -> (lo + n <= AIMG_LO \/ AIMG_HI <= lo) -> lo <= a -> b <= lo + n ->
  stk bsegs m a b.
Proof.
  intros lo n a b (W1 & W2 & W) H Ha Hb. split; [lia|]. split; [lia|]. intros x Hx.
  pose proof (W (x - lo) ltac:(lia)) as Wa. replace (lo + (x - lo)) with x in Wa by lia. split; [exact Wa|].
  pose proof (wview_noseg_some m (wa x) (noseg_out x ltac:(lia) ltac:(lia)) Wa) as S.
  unfold mrd. destruct (m (wa x)) as [b0|]; [exists b0; reflexivity| exfalso; apply S; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma zeroc_zfill : forall a n, rw_cells bsegs m a [CB (Z.to_nat n) (zeros n)] -> 0 <= n -> (a + n <= AIMG_LO \/ AIMG_HI <= a) ->
  zfill m a n.
Proof.
  intros a n [[Wf (B0 & B1 & HB)] _] Hn Ho. cbn [cells_bytes cbytes] in HB, B1. rewrite app_nil_r in HB, B1.
  assert (Hl : length (zeros n) = Z.to_nat n) by (unfold zeros; apply repeat_length). rewrite Hl in B1.
  split; [exact B0|]. split; [lia|]. intros i Hi.
  assert (Hi' : (Z.to_nat i < length (zeros n))%nat) by (rewrite Hl; lia).
  pose proof (HB _ Hi') as Hb. replace (a + Z.of_nat (Z.to_nat i)) with (a + i) in Hb by lia.
  unfold zeros in Hb. rewrite (nth_error_repeat (Z_to_bv 8 0)) in Hb by (rewrite Hl in Hi'; exact Hi').
  unfold mrd in Hb. destruct (m (wa (a + i))) as [b|] eqn:E; [exact Hb|].
  exfalso. rewrite (seg_rom_noseg bsegs (wa (a + i)) (noseg_out (a + i) ltac:(lia) ltac:(lia))) in Hb. discriminate.
Qed.

(* [comment removed for export] *)
Definition brun (lo len v : Z) : Prop := forall i, 0 <= i < len -> m (wa (lo + i)) = Some (zb v).
Lemma brun_zero : forall a n, zfill m a n -> brun a n 0.
Proof. intros a n (_ & _ & Z) i Hi. rewrite Z by lia. reflexivity. Qed.
Lemma brun_fill : forall a n c, bfill m a n c -> brun a n c.
Proof. intros a n c (_ & _ & Z) i Hi. rewrite Z by lia. reflexivity. Qed.
Lemma brun_w1 : forall a v, cells_at bsegs m a [W1 v] -> AIMG_HI <= a < 2^64 -> brun a 1 v.
Proof.
  intros a v [_ (_ & _ & B)] Ha i Hi. assert (i = 0) as -> by lia.
  specialize (B 0%nat ltac:(cbn; lia)). cbn [nth_error cells_bytes cbytes app] in B.
  replace (a + Z.of_nat 0) with (a + 0) in B by lia. unfold mrd in B.
  destruct (m (wa (a + 0))) as [b|] eqn:E; [exact B|].
  exfalso. rewrite (seg_rom_noseg bsegs (wa (a + 0)) (noseg_Z (a + 0) ltac:(lia))) in B. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rw_join : forall A cs, rw_cells bsegs m A cs -> rw_cells bsegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros A cs H. pose proof (cells_bytes_length cs (proj1 (proj1 H))) as L.
  eapply rw_recast; [exact H| cbn; split; [exact L| exact I] | cbn; rewrite app_nil_r; reflexivity| cbn; lia].
Qed.
(* [comment removed for export] *)
Lemma rw_nil : forall A, 0 <= A <= 2^64 -> rw_cells bsegs m A [].
Proof.
  intros A HA. split; [split; [exact I|]|]; cbn; [unfold bytes_at; cbn| unfold wr_at]; (split; [lia|]); (split; [lia|]); intros i Hi; lia.
Qed.
(* [comment removed for export] *)
Lemma wr_vis_sub : forall lo n a b, wr_at bsegs m lo n -> AIMG_HI <= lo -> lo <= a -> b <= lo + n -> stk bsegs m a b.
Proof.
  intros lo n a b W H H1 H2. destruct (Z_le_gt_dec a b).
  - eapply stk_sub; [apply wr_vis; [exact W| exact H] | lia | lia].
  - destruct W as (W1 & W2 & _). split; [lia|]. split; [lia|]. intros x Hx. lia.
Qed.
End KIT.

(* [comment removed for export] *)
Lemma rw_cons : forall m A c A' cs, rw_cells bsegs m A [c] -> rw_cells bsegs m A' cs -> A' = A + Z.of_nat (Cells.csize c) ->
  rw_cells bsegs m A (c :: cs).
Proof.
  intros m A c A' cs H1 H2 ->. apply (proj2 (rw_cells_app m A [c] cs)). cbn [cells_size]. rewrite Nat.add_0_r. split; assumption.
Qed.
Lemma ca_cons : forall m A c A' cs, cells_at bsegs m A [c] -> cells_at bsegs m A' cs -> A' = A + Z.of_nat (Cells.csize c) ->
  cells_at bsegs m A (c :: cs).
Proof.
  intros m A c A' cs H1 H2 ->. apply (proj2 (cells_at_app m A [c] cs)). cbn [cells_size]. rewrite Nat.add_0_r. split; assumption.
Qed.
Lemma rw_addr : forall m A A' cs, rw_cells bsegs m A' cs -> A' = A -> rw_cells bsegs m A cs.
Proof. intros m A A' cs H ->. exact H. Qed.
Lemma ca_addr : forall m A A' cs, cells_at bsegs m A' cs -> A' = A -> cells_at bsegs m A cs.
Proof. intros m A A' cs H ->. exact H. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RD.
Variables (V : nat -> Z) (m : word -> option byte) (l : list mfact).
Hypothesis HF : Forall (mfact_ok bsegs V m) l.

Lemma R_lit : forall A cs, cells_wf cs -> RT_initR.fchk bsegs None l A (cells_bytes cs) = true ->
  0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 -> cells_at bsegs m A cs.
Proof. intros A cs W C H0 H1. exact (RT_initR.rd_chunk bsegs V m None l A cs HF W C H0 H1). Qed.
Lemma R_litrw : forall A cs, cells_wf cs -> RT_initR.fchk bsegs None l A (cells_bytes cs) = true ->
  ASEG2_LO <= A -> A + Z.of_nat (cells_size cs) <= AIMG_HI -> rw_cells bsegs m A cs.
Proof.
  intros A cs W C H0 H1. apply rw_img; [| exact H0| exact H1].
  apply R_lit; [exact W| exact C| unfold ASEG2_LO in H0; lia| unfold AIMG_HI in H1; lia].
Qed.
Lemma R_litj : forall A n, RT_initR.fcov bsegs None l A n = true -> ASEG2_LO <= A -> A + Z.of_nat n <= AIMG_HI ->
  exists j, rw_cells bsegs m A [CB n j].
Proof.
  intros A n C H0 H1.
  destruct (RT_initR.rd_junk bsegs V m None l A n HF C ltac:(unfold ASEG2_LO in H0; cbn; lia) ltac:(unfold AIMG_HI in H1; cbn; lia)) as [j J].
  exists j. apply rw_img; [exact J| exact H0| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma R_sym : forall b N off cs,
  existsb (fun f => match f with MWr a' n' => zexp_eqb a' b && (n' =? N) | _ => false end) l = true ->
  cells_wf cs -> RT_initR.fchk bsegs (Some b) l off (cells_bytes cs) = true ->
  0 <= off -> off + Z.of_nat (cells_size cs) <= N -> rw_cells bsegs m (zv V b + off) cs.
Proof.
  intros b N off cs HW W C H0 H1. destruct (G_wr V m l HF b N HW) as (W0 & W1 & WW). split.
  - exact (RT_initR.rd_chunk bsegs V m (Some b) l off cs HF W C ltac:(cbn; lia) ltac:(cbn; lia)).
  - split; [lia|]. split; [lia|]. intros i Hi. replace (zv V b + off + i) with (zv V b + (off + i)) by lia. apply WW. lia.
Qed.
Lemma R_symj : forall b N off n,
  existsb (fun f => match f with MWr a' n' => zexp_eqb a' b && (n' =? N) | _ => false end) l = true ->
  RT_initR.fcov bsegs (Some b) l off n = true ->
  0 <= off -> off + Z.of_nat n <= N -> exists j, rw_cells bsegs m (zv V b + off) [CB n j].
Proof.
  intros b N off n HW C H0 H1. destruct (G_wr V m l HF b N HW) as (W0 & W1 & WW).
  destruct (RT_initR.rd_junk bsegs V m (Some b) l off n HF C ltac:(cbn; lia) ltac:(cbn; lia)) as [j J]. exists j. split; [exact J|].
  cbn [cells_size Cells.csize]. split; [lia|]. split; [lia|]. intros i Hi. replace (zv V b + off + i) with (zv V b + (off + i)) by lia. apply WW. lia.
Qed.
End RD.

End CeilWrap.

Ltac glue1 F := first [exact F | eapply rw_addr; [exact F | cbn; lia]].
Ltac glue fs :=
  lazymatch fs with
  | (?F, ?rest) => eapply rw_cons; [glue1 F | glue rest | cbn; lia]
  | ?F => glue1 F
  end.
Ltac cglue1 F := first [exact F | exact (proj1 F) | eapply ca_addr; [first [exact F | exact (proj1 F)] | cbn; lia]].
Ltac cglue fs :=
  lazymatch fs with
  | (?F, ?rest) => eapply ca_cons; [cglue1 F | cglue rest | cbn; lia]
  | ?F => cglue1 F
  end.
Ltac wf := cbn; repeat first [exact I | reflexivity | split].
Ltac bytes_eq := apply bytes_eq_unsigned; vm_compute; reflexivity.
(* [comment removed for export] *)
Ltac U := cbv delta [AIMG_LO AIMG_HI ADATA_LO ABSS_LO ASEG2_LO ASEG3_LO alink_lo1 alink_hi1 alink_lo2 alink_hi2
  A_ALLOC A_SPACEBEG A_RIS A_SECONDARY A_GSTATS A_QUAR A_MAXUSERSZ A_ASAN_INITED A_KHIGHMEMEND A_KMIDMEMBEG A_KMIDMEMEND
  A_MCS A_CAN_POISON A_TSD_KEY_INITED A_TSD_KEY A_SHADOW_OFF_CELL A_UAR_OPTION A_ALLOC_OOM A_MAY_RETURN_NULL A_PAGESIZE_CACHED
  A_LIBC_PAGESIZE A_IA_INITED A_IA_MAP1 A_DYING A_MFHOOKS A_AFLAGS A_MU_GLOBALS A_GLOBALS_REGD A_TPCG_INITED A_GLOBREC_LO
  A_GLOBREC_HI A_CFLAGS A_STACKSTORE A_DEPOT A_DEPOT_NIDS A_DEPOT_MAP1 ATP AERRNO A_TSD_PTR A_TSD_MAIN A_DTV_PTR A_LSAN_DISABLE
  A_DTV A_TLSBASE A_FSTLS_CELL AHOOKS AMALLOC AFREE AREALLOC KHIGHMEM_BEG KHIGHMEM_END KHIGHSHADOW_BEG KHIGHSHADOW_END KLOWSHADOW_BEG KLOWSHADOW_END
  SHADOW_OFFSET FS_TOTAL FS_FRAMES_OFF FS_FLAGS_OFF FS_LOG NODEBLOCK_SIZE STOREBLOCK_SIZE SSTORE_NBLOCKS SSTORE_BLOCK_FRAMES DEPOT_TAB_LOG DEPOT_L2_NODES
  DEPOT_NODE_SZ PRIM_RES_SIZE PTRARR_RES_SIZE KSPACESIZE KREGIONSIZE KFREEARRAY_OFF KFREEARRAY_SIZE KNUMCLASSES KMAXSIZE T_CTX T_STACK_TOP T_STACK_BOTTOM
  T_QCACHE T_ACACHE T_UNWINDING T_FAKESTACK CTX_TID CTX_THREAD A_TLSMOD A_DTLS_OFF A_VERBOSITY QBATCH_SIZE QUAR_MAX_SIZE QUAR_MIN_SIZE QUAR_MAX_CACHE
  HIGHSHADOW_SIZE LOWSHADOW_SIZE A_TOOLNAME A_ASAN_STR A_PRINTF_CB A_EMB_CB A_EMB EMB_CAP].
Ltac L := U; cbn; lia.

End RT_initK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.MallocShared Require Import InitMem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AHandoffLib MainExport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AMainEntry.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AMainEntry.MainFactsBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AEntryLib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import AMainEntry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstate.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate.RT_artR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_img RT_kitL RT_init1.
Import RT_initK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition hw (w : bool) : nat := if w then 0%nat else 1%nat.

Section INIT2.
Variables (w : bool) (V : nat -> Z) (usp : Z) (m : word -> option byte).
Hypothesis IP : init_pure (hw w) V usp.
Hypothesis HFW : Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w).
Let st := st_main (hw w) V usp.
Let WF : RTWF st := st_main_wf (hw w) V usp IP.
Let HF : Forall (mfact_ok bsegs V m) both_mem_facts := proj1 (proj1 (Forall_app _ _ _) HFW).

(* [comment removed for export] *)
Local Ltac chunk := apply (R_litrw V m both_mem_facts HF); [wf | vm_compute; reflexivity | L | L].
Local Ltac cchunk := apply (R_lit V m both_mem_facts HF); [wf | vm_compute; reflexivity | L | L].
(* [comment removed for export] *)
Local Ltac lit H A cs := assert (H : rw_cells bsegs m A cs) by chunk.
Local Ltac junk A n j J :=
  destruct (R_litj V m both_mem_facts HF A n ltac:(vm_compute; reflexivity) ltac:(L) ltac:(L)) as [j J].
Local Ltac gcell H a w v :=
  pose proof (G_cell V m both_mem_facts HF a w v ltac:(vm_compute; reflexivity)) as H; cbn [zv cellw] in H.

(* [comment removed for export] *)
Lemma L_link : R_link m.
Proof.
  split.
  - apply alink_cells; apply (G_img V m both_mem_facts HF); vm_compute; reflexivity.
  - intros a Ha. apply (G_img V m both_mem_facts HF A_GLOBREC_LO A_GLOBREC_HI); [vm_compute; reflexivity| exact Ha].
Qed.

(* [comment removed for export] *)
Lemma L_consts : R_consts st m.
Proof.
  unfold R_consts. cbn [st_ia_inited st st_main].
  repeat match goal with
  | |- _ /\ _ => split
  | |- cells_at _ _ _ _ => cchunk
  | |- rw_cells _ _ _ _ => chunk
  end.
  - exists (zb 0). chunk.
  - unfold R_emb. cbn [emb_d emb_sz st_tls st st_main tl_emb_d tl_emb_sz Z.eqb]. split; [| intros H; exfalso; exact (H eq_refl)].
    exists (repeat (zb 0) 8), (repeat (zb 0) 8). chunk.
Qed.

(* [comment removed for export] *)
Lemma L_alloc : R_alloc st m.
Proof.
  unfold R_alloc. cbn [st_pbase st_spacebeg st_pa st_nreserved st_sec st_qglobal st st_main nsec zlen length Z.of_nat qc_first qc_last qc_bytes fold_right].
  split; [| split; [| split; [| split]]].
  - (* [comment removed for export] *)
    gcell X1 (ZLit 680792) 8%nat (ZMul (ZLit 4096) (ZV 208)).
    lit X2 (A_ALLOC + 8) [W8 PRIM_RES_SIZE].
    junk (A_ALLOC + 16) 16%nat j1 J1.
    gcell X5 (ZLit 680824) 8%nat (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536)).
    replace (4096 * V 208%nat + -4096 * V 209%nat + 65536) with (4096 * (V 208%nat - V 209%nat) + 65536) in X5 by lia.
    lit X6 (A_ALLOC + 40) [W4 (2^32 - 1)].
    junk (A_ALLOC + 44) 4%nat j2 J2.
    gcell X8 (ZLit 680840) 8%nat (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)).
    replace (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) with (4096 * (V 208%nat - V 209%nat) + 65536 + KSPACESIZE) in X8 by (unfold KSPACESIZE; lia).
    lit X9 (A_ALLOC + 56) [W1 0].
    junk (A_ALLOC + 57) 7%nat j3 J3.
    exists j1, j2, j3. unfold A_ALLOC in *. glue (X1, (X2, (J1, (X5, (X6, (J2, (X8, (X9, J3)))))))).
  - (* [comment removed for export] *)
    lit X1 A_SECONDARY [W8 4096].
    gcell X2 (ZLit 680864) 8%nat (ZMul (ZLit 4096) (ZV 226)).
    gcell X3 (ZLit 680872) 8%nat (ZMul (ZLit 4096) (ZV 226)).
    lit X4 (A_SECONDARY + 24) [W8 PTRARR_RES_SIZE].
    junk (A_SECONDARY + 32) 16%nat j1 J1.
    lit X6 (A_SECONDARY + 48) [W8 0]. lit X7 (A_SECONDARY + 56) [W8 0].
    junk (A_SECONDARY + 64) 552%nat j2 J2.
    lit X9 (A_SECONDARY + 616) [W1 0].
    junk (A_SECONDARY + 617) 7%nat j3 J3.
    exists j1, j2, j3. unfold A_SECONDARY, A_ALLOC in *. glue (X1, (X2, (X3, (X4, (J1, (X6, (X7, (J2, (X9, J3))))))))).
  - (* [comment removed for export] *)
    junk A_GSTATS 40%nat j J. exists j. exact J.
  - (* [comment removed for export] *)
    junk A_QUAR 64%nat j1 J1.
    lit X2 (A_QUAR + 64) [W8 QUAR_MAX_SIZE]. lit X3 (A_QUAR + 72) [W8 QUAR_MIN_SIZE]. lit X4 (A_QUAR + 80) [W8 QUAR_MAX_CACHE].
    junk (A_QUAR + 88) 64%nat j2 J2.
    lit X6 (A_QUAR + 152) [W1 0]. lit X7 (A_QUAR + 153) [W1 0].
    junk (A_QUAR + 154) 6%nat j3 J3.
    lit N1 (A_QUAR + 160) [W8 0]. lit N2 (A_QUAR + 168) [W8 0]. lit N3 (A_QUAR + 176) [W8 0]. lit N4 (A_QUAR + 184) [W8 0].
    junk (A_QUAR + 192) 64%nat j4 J4.
    exists j1, j2, j3, j4. unfold A_QUAR, A_ALLOC in *.
    glue (J1, (X2, (X3, (X4, (J2, (X6, (X7, (J3, (N1, (N2, (N3, (N4, J4)))))))))))).
  - (* [comment removed for export] *) cchunk.
Qed.

(* [comment removed for export] *)
Local Ltac gwr H a n := pose proof (G_wr V m both_mem_facts HF a n ltac:(vm_compute; reflexivity)) as H; cbn [zv] in H.
Local Ltac gzero H a n W :=
  pose proof (G_zero V m both_mem_facts HF a n ltac:(vm_compute; reflexivity)
                ltac:(cbn [zv]; destruct W as (? & ? & _); lia) ltac:(cbn [zv]; destruct W as (? & ? & _); lia)) as H; cbn [zv] in H.

(* [comment removed for export] *)
Lemma ris_eq : ris st = 4096 * V 208%nat + -4096 * V 209%nat + 137439019008.
Proof. unfold ris. cbn [st_spacebeg st st_main]. unfold KSPACESIZE. lia. Qed.

Lemma L_rinfo : R_rinfo st m.
Proof.
  gwr W (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096.
  gzero P7 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096 W.
  rewrite <- ris_eq in P7.
  split.
  - eapply zfill_vis; [exact P7| lia| lia].
  - intros c Hc. exists (repeat (zb 0) 4), (repeat (zb 0) 3), (repeat (zb 0) 56).
    unfold rinfo_cells. unfold num_freed. rewrite (rg0 (hw w) V usp). cbn -[st Z.add Z.mul].
    unfold rinfo. replace (ris st + 128 * c) with (ris st + (128 * c)) by lia.
    apply (zfill_cells m _ _ _ _ P7); [lia| cbn; unfold KNUMCLASSES in Hc; lia| wf| bytes_eq].
Qed.

(* [comment removed for export] *)
Lemma L_regions : R_regions st m.
Proof.
  intros c Hc. pose proof (region_range st WF c Hc) as RR. pose proof (S_range st WF) as SR. pose proof (P_range st WF) as PR.
  rewrite (rg0 (hw w) V usp) in *. cbn [r_mapped r_mapped_fa r_allocated r_fa region0] in *.
  assert (HB : 0 <= rbeg st c /\ rbeg st c + KREGIONSIZE <= 2^47).
  { unfold KHIGHMEM_BEG, AIMG_HI, KSPACESIZE, PRIM_RES_SIZE, KREGIONSIZE in *. lia. }
  assert (HFA : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KREGIONSIZE, KFREEARRAY_OFF in *.
  pose proof (rt_SH_bounds (rbeg st c) ltac:(lia)) as S1. pose proof (rt_SH_bounds (fabeg st c) ltac:(lia)) as S2.
  change (0 / 8) with 0. rewrite !Z.add_0_r.
  split; [| split; [| split; [| split; [| split]]]].
  - apply stk_empty. lia.
  - apply stk_empty. lia.
  - apply stk_empty. lia.
  - apply stk_empty. lia.
  - intros i Hi. exfalso. unfold num_freed in Hi. rewrite (rg0 (hw w) V usp) in Hi. cbn in Hi. unfold zlen in Hi. cbn in Hi. lia.
  - cbn. apply rw_nil. lia.
Qed.

(* [comment removed for export] *)
Lemma L_avail : R_avail st m.
Proof.
  intros c k Hc Hin. exfalso. unfold avail_cptrs, apend_cptrs in Hin. rewrite (rg0 (hw w) V usp), (cch0 (hw w) V usp) in Hin.
  cbn in Hin. exact Hin.
Qed.

(* [comment removed for export] *)
Local Abbreviation TZ := (ZMul (ZLit 4096) (ZV 227)).     (* [comment removed for export] *)
Local Abbreviation CZ := (ZMul (ZLit 4096) (ZV 228)).     (* [comment removed for export] *)
Local Abbreviation DZ := (ZMul (ZLit 4096) (ZV 310)).     (* [comment removed for export] *)
Local Abbreviation FZ := (ZMul (ZLit 4096) (ZV 377)).     (* [comment removed for export] *)
Local Abbreviation TOPZ := (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344)))).

(* [comment removed for export] *)
Lemma L_cache : R_cache st m.
Proof.
  gwr T1 constr:(TZ) 4096. gzero T13 (ZAdd TZ (ZLit 80)) 3088 T1.
  intros c Hc. rewrite (cch0 (hw w) V usp). unfold pc_max_count, pc_class_size. cbn [st_cache_inited st st_main andb zlen length Z.of_nat].
  split.
  - unfold pcaddr, acache. cbn [st_t st st_main]. unfold T_ACACHE.
    eapply rw_addr; [apply (zfill_cells m _ _ (128 + 80 * c) [W4 0; W4 0; W8 0] T13); [lia| cbn; unfold KNUMCLASSES in Hc; lia| wf| bytes_eq] | lia].
  - intros i Hi. exfalso. unfold zlen in Hi. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma top_eq : ASTACK_TOP (st_sp0 st) = 32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat).
Proof.
  cbn [st_sp0 st st_main]. pose proof (ip_usp_vars _ _ _ IP) as E. pose proof (ip_top _ _ _ IP) as T.
  unfold ASTACK_TOP, roundup. rewrite E.
  replace (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 160 + 4096 - 1)
    with ((16 * V 6%nat + 3935 - 4096 * V 344%nat) + (8 * V 0%nat + V 10%nat + V 344%nat) * 4096) by lia.
  rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma L_thread : R_thread st m.
Proof.
  gwr T1 constr:(TZ) 4096.
  gcell T2 constr:(TZ) 8%nat constr:(CZ).
  gcell T3 (ZAdd TZ (ZLit 8)) 8%nat constr:(TOPZ).
  gcell T4 (ZAdd TZ (ZLit 16)) 8%nat (ZAdd TOPZ (ZLit (-8388608))).
  gcell T5 (ZAdd TZ (ZLit 24)) 8%nat (ZLit 0). gcell T6 (ZAdd TZ (ZLit 32)) 8%nat (ZLit 0).
  gcell T7 (ZAdd TZ (ZLit 40)) 1%nat (ZLit 0).
  pose proof (G_zeroc V m both_mem_facts HF (ZAdd TZ (ZLit 41)) 7 ltac:(vm_compute; reflexivity)) as J2. cbn [zv] in J2.
  gcell T9 (ZAdd TZ (ZLit 48)) 8%nat (ZLit 6148264). gcell T10 (ZAdd TZ (ZLit 56)) 8%nat (ZLit 6148484).
  gcell T11 (ZAdd TZ (ZLit 64)) 8%nat (ZLit 6146424). gcell T12 (ZAdd TZ (ZLit 72)) 8%nat constr:(FZ).
  gzero T13 (ZAdd TZ (ZLit 80)) 3088 T1.
  gcell T14 (ZAdd TZ (ZLit 3168)) 1%nat (ZLit 0).
  gcell T16 (ZAdd CZ (ZLit 8)) 4%nat (ZLit 0). gcell T17 (ZAdd CZ (ZLit 152)) 8%nat constr:(TZ).
  pose proof (t_range st WF) as [TR _]. cbn [st_t st st_main] in TR. destruct TR as [_ [_ TRi]].
  unfold R_thread. cbn [st_t st_ctx st_sp0 st_fs st_tls st_qthread tl_dtls_block tl_dtls_w st st_main].
  replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat)) with (ASTACK_TOP usp) in T3
    by (pose proof top_eq as E; cbn [st_sp0 st st_main] in E; lia).
  replace (32768 * V 0%nat + (4096 * V 10%nat + 4096 * V 344%nat) + -8388608) with (ASTACK_BOTTOM usp) in T4
    by (unfold ASTACK_BOTTOM; pose proof top_eq as E; cbn [st_sp0 st st_main] in E; lia).
  assert (J1 : rw_cells bsegs m (4096 * V 227%nat + 24) [W8 0; W8 0]) by glue (T5, T6). apply rw_join in J1.
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - eapply wr_vis_o; [exact T1| lia| lia| lia].
  - eexists _, _, _, _, _. glue (T2, (T3, (T4, (J1, (T7, (J2, (T9, (T10, (T11, T12))))))))).
  - unfold qcache_t. cbn [st_t st st_main zlen length Z.of_nat qc_first qc_last qc_bytes fold_right]. unfold T_QCACHE.
    eapply rw_addr; [apply (zfill_cells m _ _ 0 [W8 0; W8 0; W8 0; W8 0] T13); [lia| cbn; lia| wf| bytes_eq] | lia].
  - unfold T_UNWINDING. exact T14.
  - unfold CTX_TID. exact T16.
  - unfold CTX_THREAD. exact T17.
  - gcell S4 (ZLit 6282520) 8%nat constr:(CZ). gcell S5 (ZLit 6146416) 8%nat constr:(FZ). gcell S6 (ZLit 6146424) 8%nat constr:(DZ).
    gcell S7 (ZAdd DZ (ZLit 24)) 8%nat (ZLit 6146416).
    split; [cchunk|]. split; [exact (proj1 S4)|]. split; [cchunk|]. split; [cchunk|].
    split; [exact (proj1 S5)|]. split; [exact (proj1 S6)|].
    eapply ca_addr; [exact (proj1 S7)| unfold A_TLSMOD; lia].
Qed.

(* [comment removed for export] *)
Lemma L_live : R_live st m.
Proof. intros A n Hin. destruct Hin. Qed.
Lemma L_quar : R_quar st m.
Proof. split; [intros A n Hin; cbv delta [st] in Hin; rewrite (qelems0 (hw w) V usp) in Hin; destruct Hin| intros A n Hin; destruct Hin]. Qed.
Lemma L_batches : R_batches st m.
Proof. split; [exact I|]. split; [exact I|]. split; [exact I|]. intros bd Hbd. destruct Hbd. Qed.
Lemma L_ptrarr : R_ptrarr st m.
Proof.
  pose proof (pa_range st WF) as PR. cbn [st_pa st_nreserved st st_main] in PR.
  split; [| split; [intros i Hi; exfalso; unfold nsec, zlen in Hi; cbn in Hi; lia| intros e He; destruct He]].
  cbn [st_pa st_nreserved st st_main]. rewrite Z.mul_0_r, Z.add_0_r. apply stk_empty.
  destruct PR as ([PRa|PRb] & PRc & _); unfold AIMG_HI, KHIGHMEM_BEG, PTRARR_RES_SIZE in *; pose proof ceil_lt64; lia.
Qed.

(* [comment removed for export] *)
Local Ltac gimg H lo hi := pose proof (G_img V m both_mem_facts HF lo hi ltac:(vm_compute; reflexivity)) as H.

Lemma SH_4096 : forall v c, SH (4096 * v + c) = 512 * v + c / 8 + 2147450880.
Proof. intros v c. unfold SH, SHADOW_OFFSET. replace (4096 * v + c) with (c + (512 * v) * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma L_fs : R_fs st m.
Proof.
  gwr F1 constr:(FZ) 11571200.
  pose proof (G_zeroc V m both_mem_facts HF FZ 88 ltac:(vm_compute; reflexivity)) as F2. cbn [zv] in F2.
  gcell F3 (ZAdd FZ (ZLit 88)) 8%nat (ZLit 20).
  gzero F4 (ZAdd FZ (ZLit 96)) 11571104 F1.
  gwr F5w (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400.
  gzero F5 (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400 F5w.
  pose proof (fs_range st WF) as FR. cbn [st_fs st st_main] in FR. destruct FR as (FRa & FRc & FRm).
  assert (FRo : 4096 * V 377%nat + FS_TOTAL <= AIMG_LO \/ AIMG_HI <= 4096 * V 377%nat) by (destruct FRa; unfold AIMG_LO, AIMG_HI, KHIGHMEM_BEG in *; lia).
  apply zeroc_zfill in F2; [| lia| unfold FS_TOTAL in FRo; lia].
  unfold R_fs. cbn [st_fs st_lf st st_main].
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - eapply wr_vis_o; [exact F1| unfold FS_TOTAL in FRo; lia| lia| unfold FS_TOTAL; lia].
  - rewrite !SH_4096. eapply zfill_vis; [exact F5| unfold FS_FRAMES_OFF; change ((4096 + 2 ^ 15) / 8) with 4608; lia| unfold FS_TOTAL; change (11571200 / 8) with 1446400; lia].
  - intros k Hk. rewrite (fhint0 (hw w) V usp).
    eapply rw_addr; [apply (zfill_cells m _ _ (8 * k) [W8 0] F2); [lia| cbn; lia| wf| bytes_eq] | lia].
  - exact F3.
  - eapply rw_addr; [apply (zfill_cells m _ _ 0 [W1 0] F4); [lia| cbn; lia| wf| bytes_eq] | lia].
  - intros k pos Hk Hp. unfold flag_val, flag_live. cbn [st_lf st st_main existsb].
    pose proof (fflag_addr_range (4096 * V 377%nat) k pos Hk Hp) as [R1 R2].
    eapply rw_addr; [apply (zfill_cells m _ _ (fflag_addr (4096 * V 377%nat) k pos - (4096 * V 377%nat + 96)) [W1 0] F4); [lia| cbn; lia| wf| bytes_eq] | lia].
  - intros F k Hin. destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma L_ia : R_ia m.
Proof.
  gimg I9 A_IA_MAP1 (A_IA_MAP1 + 262144).
  intros i Hi. apply bss_zero_cells; [eapply pristine_sub; [exact I9| L| L] | L | L | wf | bytes_eq].
Qed.

(* [comment removed for export] *)
Local Abbreviation NZ := (ZMul (ZLit 4096) (ZV 453)).     (* [comment removed for export] *)
Local Abbreviation SZ := (ZMul (ZLit 4096) (ZV 454)).     (* [comment removed for export] *)
Let HW : Forall (mfact_ok bsegs V m) (both_mem_facts_w w) := proj2 (proj1 (Forall_app _ _ _) HFW).

Lemma nthz_single_0 : forall (x : Z), nthz [x] 0 0 = x.
Proof. intros. reflexivity. Qed.
Lemma nthz_single_pos : forall (x : Z) k, 0 < k -> nthz [x] k 0 = 0.
Proof.
  intros x k Hk. unfold nthz. destruct (Z.ltb_spec0 k 0) as [Hl|Hl]; [lia|].
  destruct (Z.to_nat k) as [|n1] eqn:E; [lia|]. cbn. destruct n1; reflexivity.
Qed.

Lemma L_depot : R_depot st m.
Proof.
  gwr D4 constr:(NZ) 1048576. gwr D13 constr:(SZ) 8388608.
  pose proof (nb_range st WF (4096 * V 453%nat) ltac:(cbn; left; reflexivity)) as (NRa & NRc & _).
  pose proof (sb_range st WF (4096 * V 454%nat) ltac:(cbn; left; reflexivity)) as (SRa & SRc & _).
  unfold R_depot. cbn [st_depot st st_main d_tab d_nblocks d_sblocks d_T depot0].
  change (d_U (depot0 (hw w) V)) with 1. change (d_nsb (depot0 (hw w) V)) with 1.
  (* [comment removed for export] *)
  assert (HB : exists B TB HS, B = dbucket (H0 (hw w)) /\ TB = A_DEPOT + 4 * B /\ HS = H0 (hw w) /\ 0 <= B < 2^DEPOT_TAB_LOG
            /\ rw_cells bsegs m 1554568 [W8 (T0 (hw w))] /\ rw_cells bsegs m 1554592 [W4 (T0 (hw w))]
            /\ rw_cells bsegs m (4096 * V 453%nat + 16) [W8 HS]
            /\ pristine m 1554600 TB /\ rw_cells bsegs m TB [W4 1] /\ pristine m (TB + 4) 5814424).
  { destruct w; cbn [hw H0 T0 both_mem_facts_w] in *.
    - exists 959707, 5458948, 4675877751747421403.
      refine (conj _ (conj eq_refl (conj eq_refl (conj _ _)))); [vm_compute; reflexivity| cbv; split; [discriminate| reflexivity]|].
      pose proof (G_cell V m _ HW (ZLit 1554568) 8%nat (ZLit 3) ltac:(vm_compute; reflexivity)) as H1.
      pose proof (G_cell V m _ HW (ZLit 1554592) 4%nat (ZLit 3) ltac:(vm_compute; reflexivity)) as H2.
      pose proof (G_cell V m _ HW (ZAdd NZ (ZLit 16)) 8%nat (ZLit 4675877751747421403) ltac:(vm_compute; reflexivity)) as H3.
      pose proof (G_img V m _ HW 1554600 5458948 ltac:(vm_compute; reflexivity)) as H4.
      pose proof (G_cell V m _ HW (ZLit 5458948) 4%nat (ZLit 1) ltac:(vm_compute; reflexivity)) as H5.
      pose proof (G_img V m _ HW (5458948 + 4) 5814424 ltac:(vm_compute; reflexivity)) as H6.
      cbn [zv cellw] in H1, H2, H3, H5. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))).
    - exists 495072, 3600408, 16284882238369664480.
      refine (conj _ (conj eq_refl (conj eq_refl (conj _ _)))); [vm_compute; reflexivity| cbv; split; [discriminate| reflexivity]|].
      pose proof (G_cell V m _ HW (ZLit 1554568) 8%nat (ZLit 2) ltac:(vm_compute; reflexivity)) as H1.
      pose proof (G_cell V m _ HW (ZLit 1554592) 4%nat (ZLit 2) ltac:(vm_compute; reflexivity)) as H2.
      pose proof (G_cell V m _ HW (ZAdd NZ (ZLit 16)) 8%nat (ZLit 16284882238369664480) ltac:(vm_compute; reflexivity)) as H3.
      pose proof (G_img V m _ HW 1554600 3600408 ltac:(vm_compute; reflexivity)) as H4.
      pose proof (G_cell V m _ HW (ZLit 3600408) 4%nat (ZLit 1) ltac:(vm_compute; reflexivity)) as H5.
      pose proof (G_img V m _ HW (3600408 + 4) 5814424 ltac:(vm_compute; reflexivity)) as H6.
      cbn [zv cellw] in H1, H2, H3, H5. exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))). }
  destruct HB as (B & TB & HS & EB & ETB & EHS & RB & H1 & H2 & H3 & H4 & H5 & H6). unfold A_DEPOT in ETB. unfold DEPOT_TAB_LOG in RB.
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - (* [comment removed for export] *) intros i Hi. unfold DEPOT_TAB_LOG in Hi. rewrite <- EB. destruct (Z.eqb_spec i B) as [->|NE].
    + eapply rw_addr; [exact H5| L].
    + destruct (Z_lt_le_dec i B).
      * apply bss_zero_cells; [eapply pristine_sub; [exact H4| L| L] | L | L | wf | bytes_eq].
      * apply bss_zero_cells; [eapply pristine_sub; [exact H6| L| L] | L | L | wf | bytes_eq].
  - (* [comment removed for export] *)
    lit D1 A_DEPOT_NIDS [W4 1]. junk (A_DEPOT_NIDS + 4) 4%nat j J.
    lit D2 (A_DEPOT_NIDS + 8) [W1 0]. lit D2a (A_DEPOT_NIDS + 9) [W1 0]. lit D2b (A_DEPOT_NIDS + 10) [W1 0]. lit D2c (A_DEPOT_NIDS + 11) [W1 0].
    exists j. unfold A_DEPOT_NIDS in *. glue (D1, (J, (D2, (D2a, (D2b, D2c))))).
  - (* [comment removed for export] *) intros k Hk. destruct (Z.eq_dec k 0) as [->|NZ0].
    + rewrite nthz_single_0. rewrite Z.mul_0_r, Z.add_0_r. gcell D3 (ZLit 5814440) 8%nat constr:(NZ). exact D3.
    + rewrite nthz_single_pos by lia. gimg I11 (A_DEPOT_MAP1 + 8) (A_DEPOT_MAP1 + 262144).
      apply bss_zero_cells; [eapply pristine_sub; [exact I11| L| L] | L | L | wf | bytes_eq].
  - (* [comment removed for export] *) intros b [<-|[]].
    eapply wr_vis_o; [exact D4| destruct NRa; unfold AIMG_HI, KHIGHMEM_BEG in *; lia| lia| unfold NODEBLOCK_SIZE; lia].
  - (* [comment removed for export] *) intros id Hid. assert (id = 1) as -> by lia.
    unfold dnode_addr, dnode. cbn [d_nblocks d_nodes depot0].
    change (nthz [4096 * V 453%nat] (1 / DEPOT_L2_NODES) 0) with (4096 * V 453%nat).
    change (dn_hash (nthz [(H0 (hw w), 0, 1)] (1 - 1) (0, 0, 0))) with (H0 (hw w)).
    change (dn_link (nthz [(H0 (hw w), 0, 1)] (1 - 1) (0, 0, 0))) with 0.
    change (dn_store (nthz [(H0 (hw w), 0, 1)] (1 - 1) (0, 0, 0))) with 1.
    change (1 mod DEPOT_L2_NODES) with 1.
    rewrite <- EHS. gcell D5 (ZAdd NZ (ZLit 24)) 4%nat (ZLit 0). gcell D6 (ZAdd NZ (ZLit 28)) 4%nat (ZLit 1).
    unfold DEPOT_NODE_SZ. glue (H3, (D5, D6)).
  - (* [comment removed for export] *) lit D7 (A_STACKSTORE + 8) [W8 (STOREBLOCK_SIZE * 1)]. unfold A_STACKSTORE in *. glue (H1, D7).
  - (* [comment removed for export] *) intros b Hb. destruct (Z.eq_dec b 0) as [->|NZ0].
    + rewrite nthz_single_0. gcell D8 (ZLit 1554584) 8%nat constr:(SZ). apply rw_join in H2.
      lit D9 (A_STACKSTORE + 28) [W1 0]. lit D10 (A_STACKSTORE + 29) [W1 0]. lit D11 (A_STACKSTORE + 30) [W1 0]. lit D12 (A_STACKSTORE + 31) [W1 0].
      eexists _. unfold A_STACKSTORE in *. glue (D8, (H2, (D9, (D10, (D11, D12))))).
    + rewrite nthz_single_pos by lia. exists (repeat (zb 0) 4).
      unfold SSTORE_NBLOCKS in Hb. apply bss_zero_cells; [eapply pristine_sub; [exact H4| L| L] | L | L | wf | bytes_eq].
  - (* [comment removed for export] *) intros b [<-|[]].
    eapply wr_vis_o; [exact D13| destruct SRa; unfold AIMG_HI, KHIGHMEM_BEG in *; lia| lia| unfold STOREBLOCK_SIZE; lia].
Qed.

End INIT2.
End CeilWrap.
