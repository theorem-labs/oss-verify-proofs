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
From Stdlib Require Permutation.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RT_artB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pwdj_app_disj : forall L1 L2 x y, pwdj (L1 ++ L2) -> In x L1 -> In y L2 -> snd x <= fst y \/ snd y <= fst x.
Proof.
  induction L1 as [|r L1 IH]; intros L2 x y HP Hx Hy; [destruct Hx|].
  cbn in HP. destruct HP as [HF HP]. destruct Hx as [<-|Hx].
  - rewrite Forall_forall in HF. specialize (HF y ltac:(apply in_or_app; right; exact Hy)). lia.
  - eapply IH; eauto.
Qed.

Lemma pwdj_app_r : forall L1 L2, pwdj (L1 ++ L2) -> pwdj L2.
Proof. induction L1 as [|r L1 IH]; intros L2 H; [exact H|]. cbn in H. apply IH. tauto. Qed.

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma NoDup_app_mid : forall {A} (a b c : list A), List.NoDup (a ++ b ++ c) -> List.NoDup b.
Proof. intros A a b c H. apply NoDup_app_remove_l in H. apply NoDup_app_remove_r in H. exact H. Qed.

(* [comment removed for export] *)
Lemma rt_ranges_tail : forall st, rt_ranges st =
  [(st_pbase st, st_pbase st + PRIM_RES_SIZE); (st_pa st, st_pa st + PTRARR_RES_SIZE)]
  ++ (map (fun e => (fst e, fst e + snd e)) (st_loose0 st)
  ++ map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st)
  ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st))
  ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st))).
Proof. reflexivity. Qed.

Section D.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Let P := st_pbase st.

Lemma prim_vs_tail : forall r, In r (map (fun e => (fst e, fst e + snd e)) (st_loose0 st)
  ++ map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st)
  ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st))
  ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st))) ->
  P + PRIM_RES_SIZE <= fst r \/ snd r <= P.
Proof.
  intros r Hr. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW.
  pose proof (pwdj_app_disj _ _ (P, P + PRIM_RES_SIZE) r PW ltac:(left; reflexivity) Hr) as D. cbn [fst snd] in D. lia.
Qed.

(* [comment removed for export] *)
Lemma blk_cptrs_map : forall c, blk_cptrs st c = map (fun b : Z * Z => b_cptr st (fst b) (snd b)) (lb_prim st c ++ q_prim st c ++ qp_prim st c).
Proof. intros c. unfold blk_cptrs, live_cptrs, quar_cptrs, qpend_cptrs. rewrite !map_app. reflexivity. Qed.

Lemma blk_cptrs_nodup : forall c, 0 <= c < KNUMCLASSES -> List.NoDup (blk_cptrs st c).
Proof.
  intros c Hc. pose proof (wc_used_nodup st c (wf_class_ok st WF c Hc)) as ND. rewrite used_cptrs_split in ND.
  apply NoDup_app_remove_l in ND. apply NoDup_app_remove_r in ND. exact ND.
Qed.

Lemma prim_block_cptr : forall A n, In (A, n) (all_blocks st) -> bprim n = true ->
  In (A, n) (lb_prim st (pclass n) ++ q_prim st (pclass n) ++ qp_prim st (pclass n))
  /\ In (b_cptr st A n) (blk_cptrs st (pclass n))
  /\ carved_cptr st (pclass n) (b_cptr st A n)
  /\ b_lo A n = cptr_addr st (pclass n) (b_cptr st A n).
Proof.
  intros A n Hin EP.
  assert (IN : In (A, n) (lb_prim st (pclass n) ++ q_prim st (pclass n) ++ qp_prim st (pclass n))).
  { unfold all_blocks in Hin. rewrite !in_app_iff in Hin. rewrite !in_app_iff.
    destruct Hin as [HA|[HA|HA]]; [left; unfold lb_prim| right; left; unfold q_prim| right; right; unfold qp_prim]; apply filter_In; (split; [exact HA|]); cbn [snd]; rewrite EP, Z.eqb_refl; reflexivity. }
  assert (IN2 : In (b_cptr st A n) (blk_cptrs st (pclass n))).
  { rewrite blk_cptrs_map. apply in_map_iff. exists (A, n). split; [reflexivity| exact IN]. }
  pose proof (wk_block st (wf_blocks_ok st WF) _ Hin) as WB. unfold wf_block in WB. cbn [fst snd] in WB.
  (nelim WB 4%nat; intros _ _ HP _). (nelim (HP EP) 3%nat; intros Hc _ Hab).
  split; [exact IN|]. split; [exact IN2|]. split.
  - apply (wc_used_carved st (pclass n) (wf_class_ok st WF (pclass n) ltac:(unfold KNUMCLASSES; lia))).
    rewrite used_cptrs_split. apply in_or_app. right. apply in_or_app. left. exact IN2.
  - unfold b_lo. rewrite EP. exact Hab.
Qed.

Lemma blocks_disj : forall A1 n1 A2 n2,
  In (A1, n1) (all_blocks st) -> In (A2, n2) (all_blocks st) -> A1 <> A2 ->
  b_hi A1 n1 <= b_lo A2 n2 \/ b_hi A2 n2 <= b_lo A1 n1.
Proof.
  intros A1 n1 A2 n2 H1 H2 NE.
  (nelimp (block_geom st WF A1 n1 H1) 11%nat; intros _ _ _ _ _ _ _ _ _ G1p G1s).
  (nelimp (block_geom st WF A2 n2 H2) 11%nat; intros _ _ _ _ _ _ _ _ _ G2p G2s).
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW.
  destruct (bprim n1) eqn:E1; destruct (bprim n2) eqn:E2.
  - (* [comment removed for export] *)
    (nelim (G1p eq_refl) 6%nat; intros C1 RB1 RE1 _ _ BH1). (nelim (G2p eq_refl) 6%nat; intros C2 RB2 RE2 _ _ BH2). clear G1p G1s G2p G2s.
    cbn zeta in *.
    (nelim (prim_block_cptr A1 n1 H1 E1) 4%nat; intros IN1 IK1 CV1 L1). (nelim (prim_block_cptr A2 n2 H2 E2) 4%nat; intros IN2 IK2 CV2 L2).
    set (c1 := pclass n1) in *. set (c2 := pclass n2) in *.
    destruct (Z.eq_dec c1 c2) as [EC|NC].
    + (* [comment removed for export] *)
      assert (Hc32 : 0 <= c1 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
      pose proof (wf_class_ok st WF c1 Hc32) as WC.
      assert (NK : b_cptr st A1 n1 <> b_cptr st A2 n2).
      { intros EK. apply NE.
        pose proof (blk_cptrs_nodup c1 Hc32) as ND. rewrite blk_cptrs_map in ND.
        rewrite <- EC in IN2.
        pose proof (nodup_map_inj (fun b : Z * Z => b_cptr st (fst b) (snd b)) _ (A1, n1) (A2, n2) ND IN1 IN2 ltac:(cbn [fst snd]; exact EK)) as EQ.
        congruence. }
      rewrite <- EC in L2, BH2, RB2, RE2, CV2.
      (nelim (carved_chunk st WF c1 (b_cptr st A1 n1) Hc32 ltac:(lia) CV1) 3%nat; intros X1 Y1 M1).
      (nelim (carved_chunk st WF c1 (b_cptr st A2 n2) Hc32 ltac:(lia) CV2) 3%nat; intros X2 Y2 M2).
      rewrite <- L1 in X1, Y1, M1. rewrite <- L2 in X2, Y2, M2.
      pose proof (csize_pos c1 ltac:(lia)) as SP.
      assert (NL : b_lo A1 n1 <> b_lo A2 n2).
      { rewrite L1, L2. unfold cptr_addr. intros E. apply NK. lia. }
      (* [comment removed for export] *)
      apply Z.mod_divide in M1; [|lia]. apply Z.mod_divide in M2; [|lia]. destruct M1 as [q1 M1]. destruct M2 as [q2 M2].
      rewrite BH1, BH2. set (s := csize c1) in *. set (rb := rbeg st c1) in *.
      assert (q1 <> q2) by (intros ->; apply NL; lia).
      destruct (Z_lt_le_dec q1 q2); [left| right]; nia.
    + (* [comment removed for export] *)
      rewrite BH1, BH2.
      assert (MM1 : r_mapped (rg st c1) <= KFREEARRAY_OFF) by (apply (wc_mapped_max st c1 (wf_class_ok st WF c1 ltac:(unfold KNUMCLASSES; lia)))).
      assert (MM2 : r_mapped (rg st c2) <= KFREEARRAY_OFF) by (apply (wc_mapped_max st c2 (wf_class_ok st WF c2 ltac:(unfold KNUMCLASSES; lia)))).
      rewrite (rbeg_val st c1) in *. rewrite (rbeg_val st c2) in *. unfold KREGIONSIZE, KFREEARRAY_OFF in *.
      destruct (Z_lt_le_dec c1 c2); [left| right]; nia.
  - (* [comment removed for export] *)
    (nelim (G1p eq_refl) 6%nat; intros _ _ _ Q1 Q2 _). (nelim (G2s eq_refl) 3%nat; intros S2 T2 _). clear G1p G1s G2p G2s.
    destruct (prim_vs_tail (b_lo A2 n2, b_lo A2 n2 + smapsize n2)) as [D|D].
    { apply in_or_app. right. apply in_or_app. left. apply in_map_iff. exists (b_lo A2 n2, n2). split; [reflexivity| exact S2]. }
    + cbn [fst snd] in D. left. unfold P in *. lia.
    + cbn [fst snd] in D. right. unfold P in *. lia.
  - (nelim (G2p eq_refl) 6%nat; intros _ _ _ Q1 Q2 _). (nelim (G1s eq_refl) 3%nat; intros S1 T1 _). clear G1p G1s G2p G2s.
    destruct (prim_vs_tail (b_lo A1 n1, b_lo A1 n1 + smapsize n1)) as [D|D].
    { apply in_or_app. right. apply in_or_app. left. apply in_map_iff. exists (b_lo A1 n1, n1). split; [reflexivity| exact S1]. }
    + cbn [fst snd] in D. right. unfold P in *. lia.
    + cbn [fst snd] in D. left. unfold P in *. lia.
  - (* [comment removed for export] *)
    (nelim (G1s eq_refl) 3%nat; intros S1 T1 _). (nelim (G2s eq_refl) 3%nat; intros S2 T2 _). clear G1p G1s G2p G2s.
    assert (NM : b_lo A1 n1 <> b_lo A2 n2).
    { intros E. apply NE.
      pose proof (nodup_map_inj fst _ (b_lo A1 n1, n1) (b_lo A2 n2, n2) (ws_nodup st (wf_sec_ok st WF)) S1 S2 ltac:(cbn [fst]; exact E)) as EQ.
      injection EQ as EQ1 EQ2. subst n2.
      (nelimp (block_geom st WF A1 n1 H1) 10%nat; intros _ _ _ _ _ _ _ _ EA1 _).
      (nelimp (block_geom st WF A2 n1 H2) 10%nat; intros _ _ _ _ _ _ _ _ EA2 _). lia. }
    cbn [app] in PW. (nelim PW 3%nat; intros _ _ PW). apply pwdj_app_r in PW.
    assert (R1 : In (b_lo A1 n1, b_lo A1 n1 + smapsize n1) (map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st) ++
       map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st)) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st)))).
    { apply in_or_app. left. apply in_map_iff. exists (b_lo A1 n1, n1). split; [reflexivity| exact S1]. }
    assert (R2 : In (b_lo A2 n2, b_lo A2 n2 + smapsize n2) (map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st) ++
       map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st)) ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st)))).
    { apply in_or_app. left. apply in_map_iff. exists (b_lo A2 n2, n2). split; [reflexivity| exact S2]. }
    destruct (pwdj_In _ _ _ PW R1 R2) as [EQ|D]; [injection EQ as EQ1 EQ2; exfalso; exact (NM EQ1)|].
    cbn [fst snd] in D. rewrite T1, T2. lia.
Qed.
End D.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ACEILv : alloc_ceiling = alloc_ceiling.
Proof. reflexivity. Qed.

Ltac art_open H := (nelim H 17%nat; intros st HR WF HM HO HB HG HFR Hsp0 HLB HLF HTRS HQ HB0 HB1 HSPB HSW).

Theorem artd_block_range : forall sp0 SPB LB LF TRS B m mo g A n,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> ablock_range A n.
Proof.
  intros sp0 SPB LB LF TRS B m mo g A n H Hin. art_open H. subst LB.
  assert (HA : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  (nelimp (block_geom st WF A n HA) 7%nat; intros Gn GA G1 G2 G3 G4 _).
  unfold ablock_range. idtac. unfold usz in G3. blia.
Qed.

Theorem artd_blocks_disjoint : forall sp0 SPB LB LF TRS B m mo g A1 n1 A2 n2,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (A1, n1) LB -> In (A2, n2) LB -> A1 <> A2 ->
  A1 + Z.max n1 1 + 16 <= A2 \/ A2 + Z.max n2 1 + 16 <= A1.
Proof.
  intros sp0 SPB LB LF TRS B m mo g A1 n1 A2 n2 H I1 I2 NE. art_open H. subst LB.
  assert (J1 : In (A1, n1) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact I1).
  assert (J2 : In (A2, n2) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact I2).
  (nelimp (block_geom st WF A1 n1 J1) 6%nat; intros _ _ _ X1 Y1 _).
  (nelimp (block_geom st WF A2 n2 J2) 6%nat; intros _ _ _ X2 Y2 _).
  unfold usz in Y1, Y2.
  destruct (blocks_disj st WF A1 n1 A2 n2 J1 J2 NE); [left| right]; lia.
Qed.

Theorem artd_block_wr : forall sp0 SPB LB LF TRS B m mo g A n,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> wr_at asegs m A n.
Proof.
  intros sp0 SPB LB LF TRS B m mo g A n H Hin. art_open H. subst LB.
  assert (J : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  (nelimp (block_geom st WF A n J) 6%nat; intros Gn _ _ X Y _).
  (nelim (rr_live st m HR A n Hin) 5%nat; intros _ _ _ V _).
  eapply stk_wr_at; [exact V| lia| unfold usz in Y; lia].
Qed.

Theorem artd_block_slack : forall sp0 SPB LB LF TRS B m mo g A n i,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (A, n) LB ->
  0 <= i -> A + n + i < roundup (A + Z.max n 1) 16 -> m (wa (A + n + i)) <> None.
Proof.
  intros sp0 SPB LB LF TRS B m mo g A n i H Hin Hi Hr. art_open H. subst LB.
  assert (J : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  (nelimp (block_geom st WF A n J) 9%nat; intros Gn _ K X Y _ _ BH _).
  (nelim (rr_live st m HR A n Hin) 5%nat; intros _ _ _ V _).
  pose proof (roundup16_le (A + usz n) (b_hi A n) BH Y) as RU. unfold usz in RU, Y.
  eapply stk_some; [exact V| | unfold AIMG_HI, KHIGHMEM_BEG in *; blia]. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_live_split : forall n, sh_live n = zrep SV_HEAP_LEFT_RZ (sh_left n) ++ shadow_enc (usz n) ++ zrep SV_HEAP_LEFT_RZ (sh_tot n - sh_left n - zlen (shadow_enc (usz n))).
Proof. intros n. unfold sh_live, sh_chunk. reflexivity. Qed.

Lemma zcells_size : forall vs, Z.of_nat (cells_size (zcells vs)) = zlen vs.
Proof. intros. rewrite zcells_shcells, rt_shcells_size. reflexivity. Qed.

(* [comment removed for export] *)
Lemma SH_mod8 : forall a, a mod 64 = 0 -> SH a mod 8 = 0.
Proof. intros a Ha. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. Qed.

Theorem artd_shadow : forall sp0 SPB LB LF TRS B m mo g A n,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (A, n) LB ->
  cells_at asegs m (SH A) (shcells (shadow_enc (Z.max n 1))) /\ shadow_ok m A n.
Proof.
  intros sp0 SPB LB LF TRS B m mo g A n H Hin. art_open H. subst LB.
  assert (J : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  (nelimp (block_geom st WF A n J) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  unfold KHIGHMEM_BEG in K.
  (nelim (rr_live st m HR A n Hin) 5%nat; intros _ _ SEC V SHD). unfold R_bshadow in SHD.
  (* [comment removed for export] *)
  assert (MID : rw_cells asegs m (SH A) (shcells (shadow_enc (Z.max n 1)))).
  { destruct (bprim n) eqn:EP.
    - rewrite sh_live_split in SHD. unfold zcells in SHD. rewrite !map_app in SHD. fold (zcells (zrep SV_HEAP_LEFT_RZ (sh_left n))) in SHD.
      fold (zcells (shadow_enc (usz n))) in SHD.
      fold (zcells (zrep SV_HEAP_LEFT_RZ (sh_tot n - sh_left n - zlen (shadow_enc (usz n))))) in SHD.
      pose proof (rw_cells_mid m _ _ _ _ SHD) as MID. rewrite zcells_size in MID.
      assert (SL : 0 <= sh_left n) by (unfold sh_left, SEC_HDR, SEC_RZ; rewrite EP; pose proof (rz_size_range n); Z.div_mod_to_equations; lia).
      unfold zlen in MID. rewrite (zrep_length _ _ SL) in MID.
      assert (ES : SH (b_lo A n) + sh_left n = SH A).
      { transitivity (SH (b_lo A n + 8 * sh_left n)); [| f_equal; lia]. rewrite rt_SH_aligned_add by exact L8. clear - SL. Z.div_mod_to_equations. lia. }
      rewrite ES in MID. rewrite zcells_shcells in MID. exact MID.
    - rewrite zcells_shcells in SHD. exact SHD. }
  split; [exact (proj1 MID)|].
  (* [comment removed for export] *)
  split.
  - intros i Hi. apply (rt_shadow_enc_addressable m A (Z.max n 1) i); [exact (proj1 MID)| | blia| unfold usz in Y; lia| lia].
    apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact GA].
  - (* [comment removed for export] *)
    assert (VR : exists lo hi, stk asegs m lo hi /\ lo mod 8 = 0 /\ hi mod 8 = 0 /\ lo <= SH A /\ SH (b_hi A n) <= hi /\ AIMG_HI <= lo).
    { destruct (bprim n) eqn:EP.
      - (nelim (Gp eq_refl) 4%nat; intros Hc RB RE _). cbn zeta in RB, RE.
        assert (Hc32 : 0 <= pclass n < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
        (nelim (rr_regions st m HR (pclass n) Hc32) 3%nat; intros _ VS _).
        (nelim (region_range st WF (pclass n) Hc32) 6%nat; intros R1 _ _ R4 _ R6).
        pose proof (P_range st WF) as (P1 & _). unfold KHIGHMEM_BEG in P1.
        set (rb := rbeg st (pclass n)) in *. set (mp := r_mapped (rg st (pclass n))) in *.
        exists (SH rb), (SH rb + mp / 8).
        assert (RB8 : rb mod 8 = 0) by (apply (mod0_trans _ 8 4096); [lia|lia|reflexivity|exact R4]).
        split; [exact VS|]. split; [apply SH_mod8; apply (mod0_trans _ 64 4096); [lia|lia|reflexivity|exact R4]|].
        split; [apply mod0_add; [lia| apply SH_mod8; apply (mod0_trans _ 64 4096); [lia|lia|reflexivity|exact R4]| clear - R6; Z.div_mod_to_equations; lia]|].
        split; [apply rt_SH_mono; lia|]. split; [| pose proof (rt_SH_bounds rb ltac:(clear - P1 R1 RB CE RE X Y; unfold usz in Y; lia)); unfold AIMG_HI; lia].
        rewrite <- (rt_SH_aligned_add rb mp RB8). apply rt_SH_mono. exact RE.
      - (nelim (Gs eq_refl) 4%nat; intros S1 T1 _ M4).
        (nelim (SEC EP) 3%nat; intros _ VS _).
        replace (b_map_beg A) with (b_lo A n) in VS by (unfold b_lo; rewrite EP; reflexivity).
        exists (SH (b_lo A n)), (SH (b_lo A n) + smapsize n / 8).
        (nelim (sec_facts n EP) 4%nat; intros _ _ F3 _).
        split; [exact VS|]. split; [apply SH_mod8; apply (mod0_trans _ 64 4096); [lia|lia|reflexivity|exact M4]|].
        split; [apply mod0_add; [lia| apply SH_mod8; apply (mod0_trans _ 64 4096); [lia|lia|reflexivity|exact M4]| clear - F3; Z.div_mod_to_equations; lia]|].
        split; [apply rt_SH_mono; lia|]. split; [| pose proof (rt_SH_bounds (b_lo A n) ltac:(clear - K CE X Y; unfold usz in Y; blia)); unfold AIMG_HI; lia].
        rewrite <- (rt_SH_aligned_add (b_lo A n) (smapsize n) L8). apply rt_SH_mono. lia. }
    (nelim VR 8%nat; intros lo hi VS LO8 HI8 LO HI LOI).
    intros j Hj. eapply stk_some; [exact VS| | exact LOI].
    assert (U : SH (A + n - 1) < SH (b_hi A n)) by (apply rt_SH_lt_of; unfold usz in Y; clear - Y H16 Gn; Z.div_mod_to_equations; lia).
    pose proof (le_floor8 lo (SH A) LO8 LO). pose proof (ceil8_le (SH (A + n - 1)) hi HI8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Section L.
Variable st : rtstate.
Hypothesis WF : RTWF st.

(* [comment removed for export] *)
Lemma loose0_range : forall b k, In (b, k) (st_loose0 st) ->
  oclr b (b + k) /\ b < b + k /\ b + k <= alloc_ceiling /\ b mod 4096 = 0.
Proof.
  intros b k H. pose proof (wb_ranges st (wf_base_ok st WF) (b, b + k)) as R. cbn [fst snd] in R. apply R.
  unfold rt_ranges. do 2 right. apply in_or_app. left. apply in_map_iff. exists (b, k). split; [reflexivity| exact H].
Qed.

(* [comment removed for export] *)
Lemma sec_range : forall e, In e (st_sec st) ->
  ablk (fst e) (fst e + smapsize (snd e)) /\ fst e + smapsize (snd e) <= alloc_ceiling /\ fst e mod 4096 = 0.
Proof.
  intros e He. (nelim (ws_entry st (wf_sec_ok st WF) e He) 4%nat; intros E1 E2 E3 _).
  pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R.
  specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
  (nelim R 4%nat; intros R1 R2 R3 R4). (nelim (sec_facts (snd e) E1) 5%nat; intros F1 _ _ F4 _).
  split; [apply oclr_ablk; [exact R1| unfold usz in F4; lia| exact R3]|]. split; [exact R3| exact R4].
Qed.

Lemma loose0_vs_block : forall b k A n, In (b, k) (st_loose0 st) -> In (A, n) (all_blocks st) ->
  b_hi A n <= b \/ b + k <= b_lo A n.
Proof.
  intros b k A n HL HB.
  (nelimp (block_geom st WF A n HB) 11%nat; intros _ _ _ _ _ _ _ _ _ Gp Gs).
  pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW.
  assert (INL : In (b, b + k) (map (fun e => (fst e, fst e + snd e)) (st_loose0 st))).
  { apply in_map_iff. exists (b, k). split; [reflexivity| exact HL]. }
  destruct (bprim n) eqn:EP.
  - (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _).
    destruct (prim_vs_tail st WF (b, b + k) ltac:(apply in_or_app; left; exact INL)) as [D|D]; cbn [fst snd] in D; [left|right]; lia.
  - (nelim (Gs eq_refl) 3%nat; intros S1 T1 _).
    cbn [app] in PW. (nelim PW 3%nat; intros _ _ PW).
    pose proof (pwdj_app_disj _ _ (b, b + k) (b_lo A n, b_lo A n + smapsize n) PW INL
                  ltac:(apply in_or_app; left; apply in_map_iff; exists (b_lo A n, n); split; [reflexivity| exact S1])) as D.
    cbn [fst snd] in D. rewrite T1. lia.
Qed.
End L.

(* [comment removed for export] *)
Lemma fsz_12 : forall k, (k = 1 \/ k = 2) -> fsz k = 64 * 2 ^ k /\ fcap k = 2 ^ (14 - k) /\ 0 <= fflags_off k /\ fflags_off k + fcap k <= 0x9000 /\ 4096 <= fflags_off k.
Proof. intros k [-> | ->]; vm_compute; repeat split; try reflexivity; try discriminate. Qed.

Theorem artd_frame_facts : forall sp0 SPB LB LF TRS B m mo g Fr k, ARTd sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF ->
  (k = 1 \/ k = 2) /\ Fr mod fsz k = 0 /\ AIMG_HI <= Fr /\ Fr + fsz k <= alloc_ceiling
  /\ wr_at asegs m Fr (fsz k - 8) /\ wr_at asegs m (SH Fr) (fsz k / 8)
  /\ (exists fl, cells_at asegs m (Fr + fsz k - 8) [C8 (wz fl)] /\ rw_cells asegs m fl [C1 (zb 1)]
                 /\ (forall A n, In (A, n) LB -> fl < A - 16 \/ A + n <= fl) /\ fl + 1 <= Fr - 8 )
  /\ (forall A n, In (A, n) LB -> A + n + 16 <= Fr \/ Fr + fsz k <= A - 16).
Proof.
  intros sp0 SPB LB LF TRS B m mo g Fr k H Hin. art_open H. subst LB LF.
  (nelim (wff_frame st (wf_fs_ok st WF) Fr k Hin) 3%nat; intros Hk Hpos EF).
  (nelim (fsz_12 k Hk) 5%nat; intros FZ FC FO1 FO2 FO3).
  pose proof (wb_fs_loose st (wf_base_ok st WF)) as FL.
  (nelim (loose0_range st WF _ _ FL) 4%nat; intros R1 R2 R3 R4). unfold KHIGHMEM_BEG, FS_TOTAL in R1, R2, R3.
  (nelim (rr_fs st m HR) 7%nat; intros VF VS _ _ _ FLG SAV).
  set (fs := st_fs st) in *. set (pos := fpos st Fr k) in *.
  assert (K2 : 2 <= 2 ^ k <= 4) by (destruct Hk as [-> | ->]; cbn; lia).
  assert (EFr : Fr = fs + 0x9000 + 2^20 * k + fsz k * pos).
  { rewrite EF. unfold fframe_addr, FS_FRAMES_OFF, FS_LOG. rewrite Z.shiftl_mul_pow2 by lia. change (2^15) with 32768. lia. }
  assert (FrLo : fs + 0x9000 + 2^20 <= Fr) by (rewrite EFr, FZ; nia).
  assert (FrHi : Fr + fsz k <= fs + 0xb09000).
  { rewrite EFr, FZ. rewrite FC in Hpos.
    destruct Hk as [-> | ->]; cbn -[Z.add Z.mul Z.le] in Hpos |- *; change (2^(14-1)) with 8192 in Hpos + change (2^(14-2)) with 4096 in Hpos; lia. }
  assert (AL : Fr mod fsz k = 0).
  { rewrite EFr, FZ. apply mod0_add; [lia| | rewrite Z.mul_comm; apply Z_mod_mult].
    apply mod0_add; [lia| apply mod0_add; [lia| apply (mod0_trans _ (64 * 2^k) 4096); [lia|lia| destruct Hk as [-> | ->]; reflexivity| exact R4] | destruct Hk as [-> | ->]; reflexivity]|].
    replace (2^20 * k) with ((2^12 * k) * (64 * 4)) by lia. apply (mod0_trans _ (64 * 2^k) (64 * 4)); [lia|lia| destruct Hk as [-> | ->]; reflexivity| apply Z_mod_mult]. }
  assert (AL8 : Fr mod 8 = 0) by (apply (mod0_trans _ 8 (fsz k)); [lia| rewrite FZ; lia| rewrite FZ; destruct Hk as [-> | ->]; reflexivity| exact AL]).
  idtac.
  split; [exact Hk|]. split; [exact AL|]. split; [clear - R1 R2 FrLo; blia|]. split; [lia|].
  split; [eapply stk_wr_at; [exact VF| lia| unfold FS_TOTAL; lia]|].
  split.
  { eapply stk_wr_at; [exact VS| apply rt_SH_mono; unfold FS_FRAMES_OFF; lia|].
    rewrite <- (rt_SH_aligned_add Fr (fsz k) AL8) at 1 by lia.
    replace (SH Fr + fsz k / 8) with (SH (Fr + fsz k)) by (rewrite (rt_SH_aligned_add Fr (fsz k) AL8); reflexivity).
    apply rt_SH_mono. unfold FS_TOTAL. lia. }
  split.
  - exists (fflag_addr fs k pos). split; [exact (SAV Fr k Hin)|]. split.
    + pose proof (FLG k pos ltac:(lia) ltac:(rewrite FC; destruct Hk as [-> | ->]; cbn; lia)) as F1.
      replace (flag_val st k pos) with 1 in F1; [exact F1|].
      unfold flag_val, flag_live. symmetry.
      match goal with |- (if ?c then 1 else 0) = 1 => enough (E : c = true) by (rewrite E; reflexivity) end.
      apply existsb_exists. exists (Fr, k). split; [exact Hin|]. cbn [fst snd]. rewrite Z.eqb_refl. cbn [andb]. apply Z.eqb_eq. exact EF.
    + split.
      * intros A n HA. assert (J : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact HA).
        (nelimp (block_geom st WF A n J) 6%nat; intros _ _ _ X Y _).
        unfold fflag_addr. destruct (loose0_vs_block st WF _ _ A n FL J); [right| left]; unfold usz, FS_TOTAL in *; lia.
      * unfold fflag_addr. lia.
  - intros A n HA. assert (J : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact HA).
    (nelimp (block_geom st WF A n J) 11%nat; intros _ _ _ X Y _ _ _ _ Gp Gs).
    destruct (loose0_vs_block st WF _ _ A n FL J) as [D|D].
    + left. unfold usz in *. clear - D X Y FrLo. lia.
    + right. unfold FS_TOTAL in *. clear - D X FrHi. lia.
Qed.


(* [comment removed for export] *)
Theorem artd_block_band : forall sp0 SPB LB LF TRS B m mo g A n,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (A, n) LB -> ablk A (A + Z.max n 1).
Proof.
  intros sp0 SPB LB LF TRS B m mo g A n H Hin. art_open H. subst LB.
  assert (HA : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  (nelimp (block_geom st WF A n HA) 7%nat; intros Gn GA G1 G2 G3 G4 _).
  apply (ablk_sub _ _ _ _ G1); unfold usz in G3; lia.
Qed.

Theorem artd_frame_band : forall sp0 SPB LB LF TRS B m mo g Fr k,
  ARTd sp0 SPB LB LF TRS B m mo g -> In (Fr, k) LF -> ablk Fr (Fr + fsz k).
Proof.
  intros sp0 SPB LB LF TRS B m mo g Fr k H Hin. art_open H. subst LB LF.
  (nelim (wff_frame st (wf_fs_ok st WF) Fr k Hin) 3%nat; intros Hk Hpos EF).
  (nelim (fsz_12 k Hk) 5%nat; intros FZ FC FO1 FO2 FO3).
  pose proof (wb_fs_loose st (wf_base_ok st WF)) as FL.
  (nelim (loose0_range st WF _ _ FL) 4%nat; intros R1 R2 R3 R4).
  assert (BK : ablk (st_fs st) (st_fs st + FS_TOTAL)) by (apply oclr_ablk; [exact R1| unfold FS_TOTAL; lia| exact R3]).
  set (fs := st_fs st) in *. set (pos := fpos st Fr k) in *.
  assert (K2 : 2 <= 2 ^ k <= 4) by (destruct Hk as [-> | ->]; cbn; lia).
  assert (EFr : Fr = fs + 0x9000 + 2^20 * k + fsz k * pos).
  { rewrite EF. unfold fframe_addr, FS_FRAMES_OFF, FS_LOG. rewrite Z.shiftl_mul_pow2 by lia. change (2^15) with 32768. lia. }
  assert (FrLo : fs + 0x9000 + 2^20 <= Fr) by (rewrite EFr, FZ; nia).
  assert (FrHi : Fr + fsz k <= fs + 0xb09000).
  { rewrite EFr, FZ. rewrite FC in Hpos.
    destruct Hk as [-> | ->]; cbn -[Z.add Z.mul Z.le] in Hpos |- *; change (2^(14-1)) with 8192 in Hpos + change (2^(14-2)) with 4096 in Hpos; lia. }
  apply (ablk_sub _ _ _ _ BK); unfold FS_TOTAL; lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac art_open H := (nelim H 17%nat; intros st HR WF HM HO HB HG HFR Hsp0 HLB HLF HTRS HQ HB0 HB1 HSPB HSW).
End RT_artB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
Import RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_kitL RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma disjoint_from_mono : forall W a n n', disjoint_from W a n -> n' <= n -> disjoint_from W a n'.
Proof. induction W as [|[lo hi] W IH]; intros a n n' H Hle; [exact I|]. cbn in *. destruct H as [H1 H2]. split; [lia| eapply IH; eauto]. Qed.

Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof. induction W as [|[lo hi] W IH]; intros a n a' n' H H1 H2; [exact I|]. cbn in *. destruct H as [H3 H4]. split; [lia| eapply IH; eauto]. Qed.

Lemma disjoint_from_app : forall W1 W2 a n, disjoint_from (W1 ++ W2) a n <-> disjoint_from W1 a n /\ disjoint_from W2 a n.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 a n; cbn; [tauto|]. rewrite IH. tauto.
Qed.

Lemma disjoint_from_incl : forall W1 W2 a n, incl W1 W2 -> disjoint_from W2 a n -> disjoint_from W1 a n.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 a n HI H; [exact I|]. cbn. split.
  - assert (IN : In (lo, hi) W2) by (apply HI; left; reflexivity). clear HI IH.
    induction W2 as [|[l h] W2 IH2]; [destruct IN|]. cbn in H. destruct H as [H1 H2].
    destruct IN as [E|IN]; [injection E; intros; subst; exact H1| apply IH2; assumption].
  - eapply IH; [| exact H]. intros x Hx. apply HI. right. exact Hx.
Qed.

Lemma disjoint_from_nil : forall a n, disjoint_from [] a n.
Proof. intros. exact I. Qed.

Lemma disjoint_from_cons : forall lo hi W a n, disjoint_from ((lo, hi) :: W) a n <-> (a + n <= lo \/ hi <= a) /\ disjoint_from W a n.
Proof. intros. cbn. tauto. Qed.

(* [comment removed for export] *)
Definition wins (W : list (Z * Z)) (lo hi : Z) : Prop := Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= hi) W.
Lemma wins_disjoint : forall W lo hi a n, wins W lo hi -> (a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof.
  induction W as [|[l h] W IH]; intros lo hi a n HW H; [exact I|]. inversion HW; subst. cbn [fst snd] in *. cbn. split; [lia| eapply IH; eauto].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WOK.
Variable st : rtstate.
Variable W : list (Z * Z).
Let d := st_depot st.

Definition WOK_link : Prop := (forall a v, In (a, v) ALINK_WORDS -> disjoint_from W a 8) /\ disjoint_from W A_GLOBREC_LO (A_GLOBREC_HI - A_GLOBREC_LO).
Definition WOK_consts : Prop :=
  disjoint_from W A_SHADOW_OFF_CELL 8 /\ disjoint_from W A_UAR_OPTION 4 /\ disjoint_from W A_AFLAGS 120
  /\ disjoint_from W A_CFLAGS 288 /\ disjoint_from W A_PAGESIZE_CACHED 8 /\ disjoint_from W A_KHIGHMEMEND 8
  /\ disjoint_from W A_KMIDMEMBEG 8 /\ disjoint_from W A_KMIDMEMEND 8 /\ disjoint_from W A_ASAN_INITED 3
  /\ disjoint_from W A_MCS 4 /\ disjoint_from W A_CAN_POISON 1 /\ disjoint_from W A_TSD_KEY_INITED 1
  /\ disjoint_from W A_TSD_KEY 4 /\ disjoint_from W A_MAY_RETURN_NULL 2 /\ disjoint_from W A_ALLOC_OOM 1
  /\ disjoint_from W A_DYING 4 /\ disjoint_from W A_VERBOSITY 4 /\ disjoint_from W A_MFHOOKS 80
  /\ disjoint_from W A_LSAN_DISABLE 4 /\ disjoint_from W A_IA_INITED 4 /\ disjoint_from W AHOOKS 24
  /\ disjoint_from W A_LIBC_PAGESIZE 8 /\ disjoint_from W A_MU_GLOBALS 8 /\ disjoint_from W A_GLOBALS_REGD 8
  /\ disjoint_from W A_TPCG_INITED 1
  /\ disjoint_from W A_TOOLNAME 8 /\ disjoint_from W A_PRINTF_CB 8 /\ disjoint_from W A_EMB 56.   (* [comment removed for export] *)
Definition WOK_alloc : Prop :=
  disjoint_from W A_ALLOC 64 /\ disjoint_from W A_SECONDARY 624 /\ disjoint_from W A_GSTATS 40
  /\ disjoint_from W A_QUAR 256 /\ disjoint_from W A_MAXUSERSZ 13.
Definition WOK_rinfo : Prop := forall c, 0 <= c < KNUMCLASSES -> disjoint_from W (rinfo st c) 128.
Definition WOK_regions : Prop := forall c, 0 <= c < KNUMCLASSES ->
  (forall i, 0 <= i < num_freed st c -> disjoint_from W (fabeg st c + 4 * i) 4)
  /\ disjoint_from W (SH (rbeg st c + r_allocated (rg st c))) ((r_mapped (rg st c) - r_allocated (rg st c)) / 8).
Definition WOK_avail : Prop := forall c k, 0 <= c < KNUMCLASSES -> In k (avail_cptrs st c ++ apend_cptrs st c) ->
  disjoint_from W (SH (cptr_addr st c k)) (csize c / 8).
Definition WOK_cache : Prop := forall c, 0 <= c < KNUMCLASSES ->
  disjoint_from W (pcaddr st c) 16 /\ forall i, 0 <= i < zlen (cch st c) -> disjoint_from W (pcaddr st c + 16 + 4 * i) 4.
Definition WOK_thread : Prop :=
  disjoint_from W (st_t st) 80 /\ disjoint_from W (qcache_t st) 32 /\ disjoint_from W (st_t st + T_UNWINDING) 1
  /\ disjoint_from W (st_ctx st + CTX_TID) 4 /\ disjoint_from W (st_ctx st + CTX_THREAD) 8
  /\ disjoint_from W A_TSD_PTR 8 /\ disjoint_from W A_TSD_MAIN 8 /\ disjoint_from W A_DTV_PTR 8
  /\ disjoint_from W (A_DTV + 8 * A_TLSMOD) 8 /\ disjoint_from W A_FSTLS_CELL 8 /\ disjoint_from W (ATP + A_DTLS_OFF) 8
  /\ disjoint_from W (tl_dtls_block (st_tls st) + 16 * A_TLSMOD + 8) 8.
(* [comment removed for export] *)
Definition WOK_block (A n : Z) : Prop :=
  disjoint_from W (b_chunk_beg A) 16
  /\ (16 < rz_size n -> disjoint_from W (b_alloc_beg A n) 16)
  /\ (bprim n = false -> disjoint_from W (b_map_beg A) 32)
  /\ disjoint_from W (SH (b_lo A n)) (sh_tot n).
Definition WOK_live : Prop := forall A n, In (A, n) (st_lb st) -> WOK_block A n.
Definition WOK_quar : Prop := forall A n, In (A, n) (qelems st ++ st_qpend st) -> WOK_block A n.
Definition WOK_batch (b : qbatch) : Prop :=
  disjoint_from W (qb_addr b) 24 /\ (forall i, 0 <= i < qb_count b -> disjoint_from W (qb_addr b + 24 + 8 * i) 8)
  /\ disjoint_from W (SH (qb_addr b)) 1024.
Definition WOK_batches : Prop := forall b, In b (qall st) -> WOK_batch b.
Definition WOK_ptrarr : Prop := (forall i, 0 <= i < nsec st -> disjoint_from W (st_pa st + 8 * i) 8)
  /\ (forall e, In e (st_spend st) -> disjoint_from W (fst e) 32).
Definition WOK_depot : Prop :=
  (forall i, 0 <= i < 2^DEPOT_TAB_LOG -> disjoint_from W (A_DEPOT + 4 * i) 4)
  /\ disjoint_from W A_DEPOT_NIDS 12
  /\ (forall k, 0 <= k < 2^15 -> disjoint_from W (A_DEPOT_MAP1 + 8 * k) 8)
  /\ (forall id, 1 <= id <= d_U d -> disjoint_from W (dnode_addr d id) 16)
  /\ disjoint_from W A_STACKSTORE 16
  /\ (forall b, 0 <= b < SSTORE_NBLOCKS -> disjoint_from W (A_STACKSTORE + 16 + 16 * b) 16).
Definition WOK_fs : Prop :=
  (forall k, 0 <= k < 11 -> disjoint_from W (st_fs st + 8 * k) 8)
  /\ disjoint_from W (st_fs st + 88) 8 /\ disjoint_from W (st_fs st + 96) 1
  /\ (forall k pos, 0 <= k < 11 -> 0 <= pos < fcap k -> disjoint_from W (fflag_addr (st_fs st) k pos) 1)
  /\ (forall F k, In (F, k) (st_lf st) -> disjoint_from W (F + fsz k - 8) 8).
Definition WOK_ia : Prop := forall i, 0 <= i < 2^15 -> disjoint_from W (A_IA_MAP1 + 8 * i) 8.
Definition WOK_lowshadow : Prop := forall g, SH AIMG_LO <= g < SH AIMG_HI -> disjoint_from W g 1.

Definition WOK_all : Prop :=
  WOK_link /\ WOK_consts /\ WOK_alloc /\ WOK_rinfo /\ WOK_regions /\ WOK_avail /\ WOK_cache /\ WOK_thread
  /\ WOK_live /\ WOK_quar /\ WOK_batches /\ WOK_ptrarr /\ WOK_depot /\ WOK_fs /\ WOK_ia /\ WOK_lowshadow.
End WOK.

(* [comment removed for export] *)
Lemma WOK_block_intro : forall W A n,
  (forall a sz, b_lo A n <= a -> a + sz <= A -> disjoint_from W a sz) ->
  disjoint_from W (SH (b_lo A n)) (sh_tot n) ->
  b_lo A n + rz_size n <= A ->
  WOK_block W A n.
Proof.
  intros W A n BELOW SHD LE. pose proof (rz_size_range n) as (Z1 & Z2).
  split; [|split; [|split]].
  - apply BELOW; unfold b_chunk_beg; [|lia]. unfold b_lo, b_alloc_beg, b_map_beg. destruct (bprim n); [lia|]. unfold SEC_HDR, SEC_RZ. lia.
  - intros HRZ. apply BELOW; unfold b_alloc_beg; [|lia]. unfold b_lo, b_alloc_beg, b_map_beg. destruct (bprim n); [lia|]. unfold SEC_HDR, SEC_RZ. lia.
  - intros EP. apply BELOW; unfold b_lo; rewrite ?EP; [lia|]. unfold b_map_beg, SEC_HDR, SEC_RZ. lia.
  - exact SHD.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nthz_In : forall (l : list Z) i dflt, 0 <= i < zlen l -> In (nthz l i dflt) l.
Proof.
  intros l i dflt Hi. unfold nthz. destruct (Z.ltb_spec0 i 0); [lia|]. apply nth_In. unfold zlen in Hi. lia.
Qed.

Lemma zcells_zrep_size : forall v k, 0 <= k -> Z.of_nat (cells_size (zcells (zrep v k))) = k.
Proof. intros. rewrite zcells_size. apply zrep_length. assumption. Qed.

Lemma sh_chunk_len : forall left tot mid, 0 <= left -> left + zlen mid <= tot -> zlen (sh_chunk left tot mid) = tot.
Proof.
  intros left tot mid H1 H2. unfold sh_chunk. rewrite !zlen_app. unfold zlen in *. rewrite !(zrep_length) by lia. lia.
Qed.

Lemma sh_fits : forall n, 0 <= n -> 0 <= sh_left n /\ sh_left n + zlen (shadow_enc (usz n)) <= sh_tot n.
Proof.
  intros n Hn. unfold sh_left, sh_tot, zlen. rewrite rt_shadow_enc_length by (unfold usz; lia).
  pose proof (rz_size_range n) as (Z1 & Z2). pose proof (usz_le_rounded8 n) as (U1 & U2 & U3).
  destruct (bprim n) eqn:EP.
  - destruct (prim_facts n EP) as (_ & F2 & F3 & F4 & F5). rewrite F5. split; [Z.div_mod_to_equations; lia|].
    unfold usz in *. Z.div_mod_to_equations. nia.
  - destruct (sec_facts n EP) as (_ & F2 & F3 & F4 & F5 & _). rewrite F5. unfold SEC_HDR, SEC_RZ. split; [Z.div_mod_to_equations; lia|].
    unfold usz in *. Z.div_mod_to_equations. nia.
Qed.

Lemma sh_live_len : forall n, 0 <= n -> zlen (sh_live n) = sh_tot n.
Proof. intros n Hn. destruct (sh_fits n Hn) as [A B]. unfold sh_live. apply sh_chunk_len; assumption. Qed.

Lemma sh_quar_len : forall n, 0 <= n -> zlen (sh_quar n) = sh_tot n.
Proof.
  intros n Hn. destruct (sh_fits n Hn) as [A B]. unfold sh_quar. apply sh_chunk_len; [assumption|].
  unfold zlen in *. rewrite zrep_length by lia. lia.
Qed.


Section FPT.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (W : list (Z * Z)) (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.


Lemma rwT : forall a cs, rw_cells asegs m a cs -> disjoint_from W a (Z.of_nat (cells_size cs)) -> rw_cells asegs m' a cs.
Proof. intros a cs H D. eapply rw_cells_transport; [exact H| exact MU| exact WM| exact D]. Qed.
Lemma roT : forall a cs, cells_at asegs m a cs -> disjoint_from W a (Z.of_nat (cells_size cs)) -> cells_at asegs m' a cs.
Proof. intros a cs H D. eapply (ro_cells_transport asegs W m m'); [exact H| exact MU| exact D]. Qed.
Lemma rwTn : forall a cs n, rw_cells asegs m a cs -> Z.of_nat (cells_size cs) <= n -> disjoint_from W a n -> rw_cells asegs m' a cs.
Proof. intros a cs n H Hn D. eapply rwT; [exact H|]. eapply disjoint_from_mono; eauto. Qed.
Lemma roTn : forall a cs n, cells_at asegs m a cs -> Z.of_nat (cells_size cs) <= n -> disjoint_from W a n -> cells_at asegs m' a cs.
Proof. intros a cs n H Hn D. eapply roT; [exact H|]. eapply disjoint_from_mono; eauto. Qed.
Lemma visT : forall lo hi, vis m lo hi -> AIMG_HI <= lo -> vis m' lo hi.
Proof. intros lo hi H Hlo. eapply stk_wmono_noseg; eauto. Qed.
(* [comment removed for export] *)
Lemma visTo : forall lo hi, vis m lo hi -> oclr lo hi -> hi <= alloc_ceiling -> vis m' lo hi.
Proof. intros lo hi H O Hhi. eapply stk_wmono_oclr; eauto. pose proof ceil_lt64. lia. Qed.

Local Ltac tr H K := first [ eapply (roT _ _ H); exact K | eapply (rwT _ _ H); exact K
                           | eapply (roTn _ _ _ H); [| exact K]; cbn; lia | eapply (rwTn _ _ _ H); [| exact K]; cbn; lia ].

(* [comment removed for export] *)
Lemma T_link : R_link m -> WOK_link W -> R_link m'.
Proof.
  intros [H HP] [K KP]. split; [intros a v Hin; tr (H a v Hin) (K a v Hin)|].
  intros a Ha. rewrite <- (HP a Ha). apply MU. eapply disjoint_outside; [exact KP|]. rewrite wa_unsigned by (unfold A_GLOBREC_LO, A_GLOBREC_HI in Ha; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma T_consts : R_consts st m -> WOK_consts W -> R_consts st m'.
Proof.
  intros H K. unfold R_consts, WOK_consts in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & [oom H15] & H16 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & [(j0 & j1 & H28) H29]).
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K28).
  split; [tr H1 K1|]. split; [tr H2 K2|]. split; [tr H3 K3|]. split; [tr H4 K4|]. split; [tr H5 K5|]. split; [tr H6 K6|].
  split; [tr H7 K7|]. split; [tr H8 K8|]. split; [tr H9 K9|]. split; [tr H10 K10|]. split; [tr H11 K11|]. split; [tr H12 K12|].
  split; [tr H13 K13|]. split; [tr H14 K14|]. split; [exists oom; tr H15 K15|]. split; [tr H16 K16|]. split; [tr H17 K17|].
  split; [tr H18 K18|]. split; [tr H19 K19|]. split; [tr H20 K20|]. split; [tr H21 K21|]. split; [tr H22 K22|]. split; [tr H23 K23|]. split; [tr H24 K24|].
  split; [tr H25 K25|]. split; [tr H26 K26|]. split; [tr H27 K27|].
  split; [exists j0, j1; tr H28 K28|].
  intros Hd. apply visT; [exact (H29 Hd)|]. pose proof (emb_block_range st WF Hd). unfold AIMG_HI, KHIGHMEM_BEG in *. blia.
Qed.

(* [comment removed for export] *)
Lemma T_alloc : R_alloc st m -> WOK_alloc W -> R_alloc st m'.
Proof.
  intros H K. unfold R_alloc, WOK_alloc in *.
  destruct H as ((j1 & j2 & j3 & H1) & (k1 & k2 & k3 & H2) & [j H3] & (l1 & l2 & l3 & l4 & H4) & H5).
  destruct K as (K1 & K2 & K3 & K4 & K5).
  split; [exists j1, j2, j3; tr H1 K1|]. split; [exists k1, k2, k3; tr H2 K2|]. split; [exists j; tr H3 K3|].
  split; [exists l1, l2, l3, l4; tr H4 K4|]. tr H5 K5.
Qed.

(* [comment removed for export] *)
Lemma ris_range : KHIGHMEM_BEG <= ris st /\ ris st + 4096 <= alloc_ceiling /\ st_pbase st <= ris st /\ ris st + 4096 <= st_pbase st + PRIM_RES_SIZE.
Proof.
  pose proof (S_range st WF) as (S1 & S2 & S3). pose proof (P_range st WF) as (P1 & P2 & P3).
  unfold ris, KSPACESIZE in *. lia.
Qed.
Lemma T_rinfo : R_rinfo st m -> WOK_rinfo st W -> R_rinfo st m'.
Proof.
  intros [V H] K. pose proof ris_range as (X1 & X2 & X3 & X4). split; [apply visT; [exact V| unfold AIMG_HI, KHIGHMEM_BEG in *; lia]|].
  intros c Hc. destruct (H c Hc) as (jr & je & js & RC). exists jr, je, js. tr RC (K c Hc).
Qed.

(* [comment removed for export] *)
Lemma region_facts : forall c, 0 <= c < KNUMCLASSES ->
  let rb := rbeg st c in let r := rg st c in
  KHIGHMEM_BEG <= rb /\ st_pbase st <= rb /\ rb + KREGIONSIZE <= st_pbase st + PRIM_RES_SIZE /\ st_pbase st + PRIM_RES_SIZE <= alloc_ceiling
  /\ 0 <= r_allocated r <= r_mapped r /\ r_mapped r <= KFREEARRAY_OFF /\ 0 <= r_mapped_fa r <= KFREEARRAY_SIZE
  /\ rb mod 8 = 0 /\ r_allocated r mod 8 = 0 /\ r_mapped r mod 8 = 0.
Proof.
  intros c Hc. destruct (region_range st WF c Hc) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof (S_range st WF) as (S1 & S2 & S3). pose proof (P_range st WF) as (P1 & P2 & P3).
  pose proof (wf_class_ok st WF c Hc) as WC. pose proof (wc_fa_max st c WC). pose proof (wc_fa_nonneg st c WC).
  pose proof (wc_alloc_carved st c WC) as AC.
  cbn zeta. unfold KREGIONSIZE, KSPACESIZE in *.
  assert (rbeg st c mod 8 = 0) by (apply (mod0_trans _ 8 4096); [lia|lia|reflexivity|exact R4]).
  assert (r_mapped (rg st c) mod 8 = 0) by (apply (mod0_trans _ 8 (2^18)); [lia|lia|reflexivity|exact R6]).
  assert (r_allocated (rg st c) mod 8 = 0).
  { rewrite AC. destruct (Z.eq_dec c 0) as [->|NZ].
    - pose proof (wb_class0 st (wf_base_ok st WF)) as [E _]. unfold ncarved. rewrite E. cbn. reflexivity.
    - apply (mod0_trans _ 8 (csize c)); [lia| pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)); lia| apply (mod0_trans _ 8 32); [lia|lia|reflexivity| apply csize_mod32; unfold KNUMCLASSES in Hc; lia]| apply Z_mod_mult]. }
  repeat split; try lia.
Qed.


Lemma T_regions : R_regions st m -> WOK_regions st W -> R_regions st m'.
Proof.
  intros H K c Hc. destruct (H c Hc) as (V1 & V2 & V3 & V4 & FA & TL). destruct (K c Hc) as [KF KT].
  pose proof (region_facts c Hc) as RF. cbn zeta in RF.
  destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  pose proof (rt_SH_bounds (rbeg st c) ltac:(unfold KHIGHMEM_BEG, KREGIONSIZE in *; lia)) as B1.
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  pose proof (rt_SH_bounds (fabeg st c) ltac:(lia)) as B2.
  split; [apply visT; [exact V1| unfold AIMG_HI; lia]|]. split; [apply visT; [exact V2| unfold AIMG_HI; lia]|].
  split; [apply visT; [exact V3| unfold AIMG_HI; lia]|]. split; [apply visT; [exact V4| unfold AIMG_HI; lia]|].
  split.
  - intros i Hi. tr (FA i Hi) (KF i Hi).
  - eapply rwT; [exact TL|]. rewrite zcells_zrep_size by (Z.div_mod_to_equations; lia). exact KT.
Qed.

(* [comment removed for export] *)
Lemma T_avail : R_avail st m -> WOK_avail st W -> R_avail st m'.
Proof.
  intros H K c k Hc Hk. eapply rwT; [exact (H c k Hc Hk)|].
  destruct (Z.eq_dec c 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hk. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hk. cbn in Hk.
    unfold apend_cptrs in Hk. apply in_map_iff in Hk as ([c' k'] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c'. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)) as SP.
  unfold sh_avail. rewrite zcells_zrep_size by (Z.div_mod_to_equations; lia). exact (K c k Hc Hk).
Qed.

(* [comment removed for export] *)
Lemma T_cache : R_cache st m -> WOK_cache st W -> R_cache st m'.
Proof.
  intros H K c Hc. destruct (H c Hc) as [H1 H2]. destruct (K c Hc) as [K1 K2]. split.
  - tr H1 K1.
  - intros i Hi. tr (H2 i Hi) (K2 i Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma t_range : oclr (st_t st) (st_t st + 4096) /\ st_t st + 4096 <= alloc_ceiling.
Proof.
  pose proof (wb_t_loose st (wf_base_ok st WF)) as TL. destruct (loose0_range st WF _ _ TL) as (R1 & R2 & R3 & R4). split; [exact R1| exact R3].
Qed.
Lemma T_thread : R_thread st m -> WOK_thread st W -> R_thread st m'.
Proof.
  intros H K. destruct H as (V & (j1 & j2 & j3 & j4 & j5 & HT) & HQ & HU & HC1 & HC2 & I1 & I2 & I3 & I4 & I5 & I6 & HD).
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12).
  pose proof t_range as [T1 T2].
  split; [apply visTo; [exact V| exact T1| exact T2]|].
  split; [exists j1, j2, j3, j4, j5; tr HT K1|].
  split; [tr HQ K2|]. split; [tr HU K3|]. split; [tr HC1 K4|]. split; [tr HC2 K5|].
  split; [tr I1 K6|]. split; [tr I2 K7|]. split; [tr I3 K8|]. split; [tr I4 K9|]. split; [tr I5 K10|]. split; [tr I6 K11|].
  tr HD K12.
Qed.

(* [comment removed for export] *)
Lemma T_block : forall live A n, In (A, n) (all_blocks st) ->
  R_block st m live A n -> WOK_block W A n -> R_block st m' live A n.
Proof.
  intros live A n HB (HD & BG & SC & V & SHD) (K1 & K2 & K3 & K4).
  pose proof (block_geom st WF A n HB) as (Gn & GA & K & X & Y & CE & L16 & H16 & EA & Gp & Gs). unfold usz in Y. unfold KHIGHMEM_BEG in K.
  split; [|split; [|split; [|split]]].
  - destruct HD as (b1 & cid & HC & HB1). exists b1, cid. split; [| exact HB1]. tr HC K1.
  - intros HRZ. tr (BG HRZ) (K2 HRZ).
  - intros EP. destruct (SC EP) as (V1 & V2 & HC). destruct (Gs EP) as (S1 & T1 & T2 & M4).
    assert (E : b_map_beg A = b_lo A n) by (unfold b_lo; rewrite EP; reflexivity).
    pose proof (rt_SH_bounds (b_lo A n) ltac:(blia)).
    split; [apply visT; [exact V1| rewrite E; unfold AIMG_HI; blia]|].
    split; [apply visT; [exact V2| rewrite E; unfold AIMG_HI; lia]|].
    tr HC (K3 EP).
  - apply visT; [exact V| unfold AIMG_HI; blia].
  - unfold R_bshadow in *. pose proof (rt_SH_bounds (b_lo A n) ltac:(blia)) as SB. destruct (bprim n) eqn:EP.
    + destruct live.
      * eapply rwT; [exact SHD|]. rewrite zcells_size. rewrite sh_live_len by lia. exact K4.
      * eapply rwT; [exact SHD|]. rewrite zcells_size. rewrite sh_quar_len by lia. exact K4.
      * apply visT; [exact SHD| unfold AIMG_HI; lia].
    + destruct live; [| exact I| exact I]. eapply rwT; [exact SHD|]. rewrite zcells_size.
      (* [comment removed for export] *)
      assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
      destruct (sh_fits n ltac:(lia)) as [SL SF].
      assert (ES : SH (b_lo A n) + sh_left n = SH A).
      { transitivity (SH (b_lo A n + 8 * sh_left n)); [| f_equal; lia]. rewrite rt_SH_aligned_add by exact L8. clear - SL. Z.div_mod_to_equations. lia. }
      eapply disjoint_from_sub; [exact K4| lia| lia].
Qed.

Lemma T_live : R_live st m -> WOK_live st W -> R_live st m'.
Proof.
  intros H K A n Hin. assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hin).
  apply T_block; [exact HB| exact (H A n Hin)| exact (K A n Hin)].
Qed.
Lemma T_quar : R_quar st m -> WOK_quar st W -> R_quar st m'.
Proof.
  intros [H HP] K. split.
  - intros A n Hin. assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin).
    apply T_block; [exact HB| exact (H A n Hin)| apply K; rewrite in_app_iff; left; exact Hin].
  - intros A n Hin. assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin).
    apply T_block; [exact HB| exact (HP A n Hin)| apply K; rewrite in_app_iff; right; exact Hin].
Qed.

(* [comment removed for export] *)
Lemma T_qlist : forall q, (forall b, In b q -> In b (qall st)) -> R_qlist m q -> WOK_batches st W -> R_qlist m' q.
Proof.
  induction q as [|b q IH]; intros Hsub H K; [exact I|]. cbn [R_qlist] in H |- *. destruct H as (HL & (V & SL & SHD) & HQ).
  assert (Hb : In b (qall st)) by (apply Hsub; left; reflexivity).
  destruct (K b Hb) as (K1 & K2 & K3).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as (_ & k & CV & EQ).
  assert (Hc : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  destruct (carved_chunk st WF 24 k Hc ltac:(lia) CV) as (C1 & C2 & C3). rewrite <- EQ in C1.
  pose proof (region_facts 24 Hc) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
  split; [| split; [split; [| split]|]].
  - tr HL K1.
  - apply visT; [exact V| unfold AIMG_HI; lia].
  - intros i Hi. tr (SL i Hi) (K2 i Hi).
  - eapply rwT; [exact SHD|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia. exact K3.
  - apply IH; [| exact HQ| exact K]. intros b' Hb'. apply Hsub. right. exact Hb'.
Qed.
Lemma T_batches : R_batches st m -> WOK_batches st W -> R_batches st m'.
Proof.
  intros (H1 & H2 & H3 & H4) K.
  split; [| split; [| split]].
  - apply T_qlist; [| exact H1| exact K]. intros b Hb; unfold qall; rewrite !in_app_iff; tauto.
  - apply T_qlist; [| exact H2| exact K]. intros b Hb; unfold qall; rewrite !in_app_iff; tauto.
  - apply T_qlist; [| exact H3| exact K]. intros b Hb; unfold qall; rewrite !in_app_iff; tauto.
  - intros bd Hbd. destruct (H4 bd Hbd) as ([nx HL] & V & SL & SHD).
    assert (Hb : In (fst bd) (qall st)) by (unfold qall; rewrite !in_app_iff; right; right; right; apply in_map; exact Hbd).
    destruct (K (fst bd) Hb) as (K1 & K2 & K3).
    destruct (wq_batch st (wf_quar_ok st WF) (fst bd) Hb) as (_ & k & CV & EQ).
    assert (Hc : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
    destruct (carved_chunk st WF 24 k Hc ltac:(lia) CV) as (C1 & C2 & C3). rewrite <- EQ in C1.
    pose proof (region_facts 24 Hc) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
    unfold KHIGHMEM_BEG, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
    split; [exists nx; tr HL K1|]. split; [apply visT; [exact V| unfold AIMG_HI; lia]|]. split; [intros i Hi; tr (SL i Hi) (K2 i Hi)|].
    eapply rwT; [exact SHD|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia. exact K3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_range : ablk (st_pa st) (st_pa st + PTRARR_RES_SIZE) /\ st_pa st + PTRARR_RES_SIZE <= alloc_ceiling /\ 8 * st_nreserved st <= PTRARR_RES_SIZE /\ nsec st <= st_nreserved st /\ 0 <= nsec st.
Proof.
  pose proof (wb_ranges st (wf_base_ok st WF) (st_pa st, st_pa st + PTRARR_RES_SIZE) ltac:(right; left; reflexivity)) as R. cbn [fst snd] in R.
  pose proof (wb_nres st (wf_base_ok st WF)). pose proof (ws_nres st (wf_sec_ok st WF)). unfold nsec. pose proof (zlen_nonneg (st_sec st)). unfold nsec in *.
  destruct R as (R1 & R2 & R3 & R4).
  split; [apply oclr_ablk; [exact R1| unfold PTRARR_RES_SIZE; lia| exact R3]|]. lia.
Qed.
Lemma T_ptrarr : R_ptrarr st m -> WOK_ptrarr st W -> R_ptrarr st m'.
Proof.
  intros (V & H & HS) [K KS]. pose proof pa_range as (P1 & P2 & P3 & P4 & P5). unfold KHIGHMEM_BEG, PTRARR_RES_SIZE in *.
  split; [apply visT; [exact V| exact (ablk_img _ _ P1)]|].
  split; [intros i Hi; tr (H i Hi) (K i Hi)|].
  intros e He. destruct (HS e He) as (V1 & V2 & HC). destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
  destruct (ws_entry st (wf_sec_ok st WF) e HE) as (E1 & E2 & E3 & _).
  destruct (sec_range st WF e HE) as (R & Rc & _). destruct (ablk_lin _ _ R) as (Ri & R0 & _ & R47).
  pose proof (rt_SH_bounds (fst e) ltac:(clear - R0 R47 E1; destruct (sec_facts (snd e) E1) as (_ & _ & _ & F4 & _); unfold usz in F4; lia)).
  split; [apply visT; [exact V1| exact Ri]|].
  split; [apply visT; [exact V2| unfold AIMG_HI in *; lia]|].
  tr HC (KS e He).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nb_range : forall b, In b (d_nblocks (st_depot st)) -> ablk b (b + NODEBLOCK_SIZE) /\ b + NODEBLOCK_SIZE <= alloc_ceiling /\ b mod 4096 = 0.
Proof.
  intros b Hb. pose proof (wb_ranges st (wf_base_ok st WF) (b, b + NODEBLOCK_SIZE)) as R. cbn [fst snd] in R.
  specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; right; left; apply in_map_iff; exists b; auto)).
  destruct R as (R1 & R2 & R3 & R4). split; [apply oclr_ablk; [exact R1| unfold NODEBLOCK_SIZE; lia| exact R3]|]. lia.
Qed.
Lemma sb_range : forall b, In b (d_sblocks (st_depot st)) -> ablk b (b + STOREBLOCK_SIZE) /\ b + STOREBLOCK_SIZE <= alloc_ceiling /\ b mod 4096 = 0.
Proof.
  intros b Hb. pose proof (wb_ranges st (wf_base_ok st WF) (b, b + STOREBLOCK_SIZE)) as R. cbn [fst snd] in R.
  specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; right; right; apply in_map_iff; exists b; auto)).
  destruct R as (R1 & R2 & R3 & R4). split; [apply oclr_ablk; [exact R1| unfold STOREBLOCK_SIZE; lia| exact R3]|]. lia.
Qed.
Lemma T_depot : R_depot st m -> WOK_depot st W -> R_depot st m'.
Proof.
  intros H K. destruct H as (TAB & [j NIDS] & MAP1 & NBV & NODES & SS & BLKS & SBV).
  destruct K as (K1 & K2 & K3 & K4 & K5 & K6). unfold R_depot.
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  - intros i Hi. tr (TAB i Hi) (K1 i Hi).
  - exists j. tr NIDS K2.
  - intros k Hk. tr (MAP1 k Hk) (K3 k Hk).
  - intros b Hb. destruct (nb_range b Hb) as (R1 & R2 & R3). apply visT; [exact (NBV b Hb)| exact (ablk_img _ _ R1)].
  - intros id Hid. tr (NODES id Hid) (K4 id Hid).
  - tr SS K5.
  - intros b Hb. destruct (BLKS b Hb) as (j1 & HC). exists j1. tr HC (K6 b Hb).
  - intros b Hb. destruct (sb_range b Hb) as (R1 & R2 & R3). apply visT; [exact (SBV b Hb)| exact (ablk_img _ _ R1)].
Qed.

(* [comment removed for export] *)
Lemma fs_range : ablk (st_fs st) (st_fs st + FS_TOTAL) /\ st_fs st + FS_TOTAL <= alloc_ceiling /\ st_fs st mod 4096 = 0.
Proof.
  pose proof (loose0_range st WF _ _ (wb_fs_loose st (wf_base_ok st WF))) as (R1 & R2 & R3 & R4).
  split; [apply oclr_ablk; [exact R1| unfold FS_TOTAL; lia| exact R3]|]. lia.
Qed.
Lemma T_fs : R_fs st m -> WOK_fs st W -> R_fs st m'.
Proof.
  intros H K. destruct H as (V1 & V2 & HINTS & LOG & GC & FLG & SAV). destruct K as (K1 & K2 & K3 & K4 & K5).
  pose proof fs_range as (F1 & F2 & F3). unfold KHIGHMEM_BEG in F1.
  pose proof (rt_SH_bounds (st_fs st + FS_FRAMES_OFF) ltac:(unfold FS_FRAMES_OFF, FS_TOTAL in *; blia)) as B1.
  split; [apply visT; [exact V1| unfold AIMG_HI; blia]|].
  split; [apply visT; [exact V2| unfold AIMG_HI; lia]|].
  split; [intros k Hk; tr (HINTS k Hk) (K1 k Hk)|].
  split; [tr LOG K2|]. split; [tr GC K3|]. split.
  - intros k pos Hk Hpos. tr (FLG k pos Hk Hpos) (K4 k pos Hk Hpos).
  - intros F k Hin. tr (SAV F k Hin) (K5 F k Hin).
Qed.

(* [comment removed for export] *)
Lemma T_ia : R_ia m -> WOK_ia W -> R_ia m'.
Proof. intros H K i Hi. tr (H i Hi) (K i Hi). Qed.
Lemma T_lowshadow : R_lowshadow m -> WOK_lowshadow W -> R_lowshadow m'.
Proof. intros H K g Hg. tr (H g Hg) (K g Hg). Qed.

Theorem RTREP_transport : RTREP st m -> WOK_all st W -> RTREP st m'.
Proof.
  intros HR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16). constructor.
  - apply T_link; [exact (rr_link st m HR)| exact K1].
  - apply T_consts; [exact (rr_consts st m HR)| exact K2].
  - apply T_alloc; [exact (rr_alloc st m HR)| exact K3].
  - apply T_rinfo; [exact (rr_rinfo st m HR)| exact K4].
  - apply T_regions; [exact (rr_regions st m HR)| exact K5].
  - apply T_avail; [exact (rr_avail st m HR)| exact K6].
  - apply T_cache; [exact (rr_cache st m HR)| exact K7].
  - apply T_thread; [exact (rr_thread st m HR)| exact K8].
  - apply T_live; [exact (rr_live st m HR)| exact K9].
  - apply T_quar; [exact (rr_quar st m HR)| exact K10].
  - apply T_batches; [exact (rr_batches st m HR)| exact K11].
  - apply T_ptrarr; [exact (rr_ptrarr st m HR)| exact K12].
  - apply T_depot; [exact (rr_depot st m HR)| exact K13].
  - apply T_fs; [exact (rr_fs st m HR)| exact K14].
  - apply T_ia; [exact (rr_ia st m HR)| exact K15].
  - apply T_lowshadow; [exact (rr_lowshadow st m HR)| exact K16].
Qed.
End FPT.


End CeilWrap.
