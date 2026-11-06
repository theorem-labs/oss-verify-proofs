(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvOpsRc63.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

Section RcS.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Definition head_ws (ba : Z) (its : list (Z * Z)) (rest : list batch) : list (Z * Z) :=
    (IB bt + 912, q_bytes (BATCH ba its :: rest)) :: (ba + 8, ba_bytes (BATCH ba its)) :: (ba + 16, Z.of_nat (length its)) :: itemw (ba + 24) its.

  Lemma ideal_head_item : forall (X : Z -> Prop) (Xd : Xdec X) st Lc FF (M0 Mx : mem) mdl ba m n its rest (qt qg : Z),
    WFq bt st Lc FF qt qg -> Rep bt st Lc FF M0 mdl -> a_gq st = BATCH ba ((m, n) :: its) :: rest ->
    (forall z, qhdr bt z -> X z) -> (forall z, ba <= z < ba + BATCHSZ -> X z) ->
    (forall b0, In b0 rest -> forall z, ba_addr b0 <= z < ba_addr b0 + BATCHSZ -> ~ X z -> Mx (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)) ->
    let ws := head_ws ba its rest in
    let M0' := fun a : word => if Xd (u a) then putl M0 ws a else Mx a in
    ws_ok ws
    /\ (forall a v z, In (a, v) ws -> a <= z < a + 8 -> X z /\ (qhdr bt z \/ ba <= z < ba + BATCHSZ))
    /\ rep_list bt M0' (IB bt + 888) (BATCH ba its :: rest) /\ rep_batches bt M0' (BATCH ba its :: rest)
    /\ writableZ SG M0 ba (ba + BATCHSZ).
  Proof.
    intros X Xd st Lc FF M0 Mx mdl ba m n its rest qt qg W R Hgq XQ XO KEEPB. cbn zeta. (lazymatch goal with |- ?G => let G' := eval unfold head_ws in G in change_no_check G' end).
    set (b := BATCH ba ((m, n) :: its)) in *. set (b' := BATCH ba its). set (gq' := b' :: rest).
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & (WQ1 & WQ2 & WQ3 & WQ4 & WQ5 & WQ6) & _).
    assert (Hb : In b (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite Hgq; left; reflexivity).
    destruct (batch_facts bt st Lc FF W b Hb) as (CVB & BL & BB1 & BB2). unfold b in CVB, BL, BB1, BB2. cbn [ba_addr ba_items length] in CVB, BL, BB1, BB2.
    assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    destruct (space_facts bt st Lc FF W) as (_ & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia).
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    pose proof R as (R1 & R2 & R3 & R4 & R5 & R6 & _).
    destruct R2 as (_ & _ & _ & _ & _ & _ & IL & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & TP & _).
    (* [comment removed for export] *)
    set (ws := (IB bt + 912, q_bytes gq') :: (ba + 8, ba_bytes b') :: (ba + 16, Z.of_nat (length its)) :: itemw (ba + 24) its).
    assert (WSZ : forall a v, In (a, v) ws -> (a = IB bt + 912) \/ (ba + 8 <= a /\ a + 8 <= ba + BATCHSZ)).
    { intros a v [E | [E | [E | Hi]]]; [left; congruence | right; injection E as <- _; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia | right; injection E as <- _; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia|].
      right. destruct (itemw_in its (ba + 24) a v Hi) as (j & mn & Hj & -> & _). pose proof (nth_error_lt _ _ _ Hj) as Hl. unfold BATCHSZ, BATCHCAP in *. lia. }
    assert (WSOK : ws_ok ws).
    { intros a v Hin. destruct (WSZ a v Hin) as [-> | [A1 A2]]; [clear -INI I1 I2; ulia | clear -A1 A2 BB1 BB2 SBH B3 B4 B5; ulia]. }
    set (IDEAL := putl M0 ws).
    set (M0' := fun a : word => if Xd (u a) then IDEAL a else Mx a).
    assert (WSX : forall a v z, In (a, v) ws -> a <= z < a + 8 -> X z /\ (qhdr bt z \/ ba <= z < ba + BATCHSZ)).
    { intros a v z Hin Hz. destruct (WSZ a v Hin) as [-> | [A1 A2]].
      - assert (Q : qhdr bt z) by ((lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); lia). split; [exact (XQ z Q) | left; exact Q].
      - assert (Q : ba <= z < ba + BATCHSZ) by lia. split; [exact (XO z Q) | right; exact Q]. }
    assert (OFFX : forall i, ~ X i -> 0 <= i < 2 ^ 64 -> M0' (Z_to_bv 64 i) = Mx (Z_to_bv 64 i)).
    { intros i NX Hr. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). rewrite (u64_lit i) by lia. destruct (Xd i); [contradiction | reflexivity]. }
    assert (INX : forall i, X i -> 0 <= i < 2 ^ 64 -> M0' (Z_to_bv 64 i) = IDEAL (Z_to_bv 64 i)).
    { intros i HX Hr. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). rewrite (u64_lit i) by lia. destruct (Xd i); [reflexivity | contradiction]. }
    assert (IDOUT : forall i, (forall a v, In (a, v) ws -> i < a \/ a + 8 <= i) -> 0 <= i < 2 ^ 64 -> IDEAL (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
    { intros i OUT Hr. (lazymatch goal with |- ?G => let G' := eval unfold IDEAL in G in change_no_check G' end). apply putl_out; [exact WSOK|]. intros a v Hin. rewrite u64_lit by lia. exact (OUT a v Hin). }
    assert (WSI : forall a v, In (a, v) ws -> (a = IB bt + 912 /\ v = q_bytes gq') \/ (a = ba + 8 /\ v = ba_bytes b') \/ (a = ba + 16 /\ v = Z.of_nat (length its))
                    \/ (exists j mn, nth_error its j = Some mn /\ a = ba + 24 + 8 * Z.of_nat j /\ v = fst mn)).
    { intros a v [E | [E | [E | Hi]]]; [left | right; left | right; right; left | right; right; right]; try (injection E as <- <-; split; reflexivity).
      exact (itemw_in its (ba + 24) a v Hi). }
    assert (FARI : IB bt + 920 <= ba) by (clear -BB1 INI I2 SBH; ulia).
    assert (SEPH : forall a' v', In (a', v') ws -> (a' = IB bt + 912 /\ v' = q_bytes gq') \/ a' + 8 <= IB bt + 912 \/ IB bt + 912 + 8 <= a').
    { intros a' v' Hin. destruct (WSI a' v' Hin) as [X0 | [[-> _] | [[-> _] | (j & mn & _ & -> & _)]]]; [left; exact X0 | right; right; lia | right; right; lia | right; right; lia]. }
    assert (SEP8 : forall a' v', In (a', v') ws -> (a' = ba + 8 /\ v' = ba_bytes b') \/ a' + 8 <= ba + 8 \/ ba + 8 + 8 <= a').
    { intros a' v' Hin. destruct (WSI a' v' Hin) as [[-> _] | [X0 | [[-> _] | (j & mn & _ & -> & _)]]]; [right; left; lia | left; exact X0 | right; right; lia | right; right; lia]. }
    assert (SEP16 : forall a' v', In (a', v') ws -> (a' = ba + 16 /\ v' = Z.of_nat (length its)) \/ a' + 8 <= ba + 16 \/ ba + 16 + 8 <= a').
    { intros a' v' Hin. destruct (WSI a' v' Hin) as [[-> _] | [[-> _] | [X0 | (j & mn & _ & -> & _)]]]; [right; left; lia | right; left; lia | left; exact X0 | right; right; lia]. }
    assert (SEPI : forall j mn, nth_error its j = Some mn -> forall a' v', In (a', v') ws ->
                     (a' = ba + 24 + 8 * Z.of_nat j /\ v' = fst mn) \/ a' + 8 <= ba + 24 + 8 * Z.of_nat j \/ ba + 24 + 8 * Z.of_nat j + 8 <= a').
    { intros j mn Hj a' v' Hin. destruct (WSI a' v' Hin) as [[-> _] | [[-> _] | [[-> _] | (j' & mn' & Hj' & -> & ->)]]]; [right; left; lia | right; left; lia | right; left; lia |].
      destruct (Nat.eq_dec j' j) as [-> | NEj]; [left; split; [reflexivity | congruence] | right; lia]. }
    (* [comment removed for export] *)
    assert (HDRX : forall i, IB bt + 888 <= i < IB bt + 920 -> 0 <= i < 2 ^ 64 /\ X i) by (intros i Hi; split; [clear -Hi INI I1 I2; ulia | apply XQ; exact Hi]).
    assert (OBJX : forall i, ba <= i < ba + BATCHSZ -> 0 <= i < 2 ^ 64 /\ X i) by (intros i Hi; split; [clear -Hi BB1 BB2 SBH B3 B4 B5; ulia | apply XO; exact Hi]).
    assert (HDRSAME : forall i, IB bt + 888 <= i < IB bt + 912 -> M0' (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
    { intros i Hi. destruct (HDRX i ltac:(lia)) as [Hr HX]. rewrite (INX i HX Hr). apply IDOUT; [| exact Hr].
      intros a v Hin. destruct (WSZ a v Hin) as [-> | [A1 A2]]; [lia | clear -Hi A1 BB1 INI I2 SBH; ulia]. }
    assert (NL : rep_list bt M0' (IB bt + 888) gq').
    { destruct IL as (L1 & L2 & L3 & L4). rewrite Hgq in L1, L2, L3. (lazymatch goal with |- ?G => let G' := eval unfold rep_list in G in change_no_check G' end).
      assert (RI : 0 <= IB bt + 888 /\ IB bt + 920 < 2 ^ 64) by (clear -INI I1 I2; ulia).
      split. { (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). cbn [length] in L1 |- *. eapply (cellZ_frame _ _ _ _ _ _ L1); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply HDRSAME; lia]. }
      split. { (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). cbn [ba_addr] in L2 |- *. eapply (cellZ_frame _ _ _ _ _ _ L2); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply HDRSAME; lia]. }
      split. { rewrite (last_addr_map gq' (b :: rest) eq_refl). eapply (cellZ_frame _ _ _ _ _ _ L3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply HDRSAME; lia]. }
      replace (IB bt + 888 + 24) with (IB bt + 912) by lia.
      eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 (IB bt + 912) (q_bytes gq') WSOK ltac:(left; reflexivity) SEPH ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      intros i Hi. cbn in Hi. destruct (HDRX i ltac:(lia)) as [Hr HX]. exact (INX i HX Hr). }
    (* [comment removed for export] *)
    assert (OBJI : forall i, ba <= i < ba + BATCHSZ -> M0' (Z_to_bv 64 i) = IDEAL (Z_to_bv 64 i)) by (intros i Hi; destruct (OBJX i Hi) as [Hr HX]; exact (INX i HX Hr)).
    (* [comment removed for export] *)
    assert (RESTSAME : forall b0, In b0 rest -> forall i, ba_addr b0 <= i < ba_addr b0 + BATCHSZ -> M0' (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
    { intros b0 Hb0 i Hi. assert (Hb2 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite Hgq; right; exact Hb0).
      destruct (batch_facts bt st Lc FF W b0 Hb2) as (CV0 & _ & C1 & C2).
      assert (Hr : 0 <= i < 2 ^ 64) by (clear -Hi C1 C2 SBH B3 B4 B5; ulia).
      assert (DIS : ba + BATCHSZ <= ba_addr b0 \/ ba_addr b0 + BATCHSZ <= ba).
      { destruct (chunk_cases bt st Lc FF W BATCHCLASS ba BATCHCLASS (ba_addr b0) HC24 HC24 CVB CV0) as [[_ EA] | Dj]; [| change (csize BATCHCLASS) with 8192 in Dj; (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia].
        exfalso. rewrite Hgq, map_app in WQ5. cbn [map ba_addr] in WQ5. apply (NoDup_remove_2 _ _ _ WQ5). apply in_app_iff. right. change (ba_addr b) with ba. rewrite EA. apply in_map. exact Hb0. }
      assert (IDS : IDEAL (Z_to_bv 64 i) = M0 (Z_to_bv 64 i)).
      { apply IDOUT; [| exact Hr]. intros a v Hin. destruct (WSZ a v Hin) as [-> | [A1 A2]]; [clear -Hi C1 INI I2 SBH; ulia | clear -Hi A1 A2 DIS; lia]. }
      destruct (Xd i) as [HX | NX]; [rewrite (INX i HX Hr); exact IDS|].
      rewrite (OFFX i NX Hr). exact (KEEPB b0 Hb0 i Hi NX). }
    assert (NB : rep_batches bt M0' gq').
    { intros i b0 Hb0. destruct i as [|i].
      - cbn in Hb0. injection Hb0 as <-. destruct (R6 0%nat b ltac:(rewrite Hgq; reflexivity)) as (C1 & C2 & C3 & C4 & CW). unfold b in C1, CW. cbn [ba_addr] in C1, CW |- *.
        assert (RB : 0 <= ba /\ ba + BATCHSZ < 2 ^ 64) by (clear -BB1 BB2 SBH B3 B4 B5; ulia). unfold BATCHSZ, BATCHCAP in *.
        split. { rewrite Hgq in C1. (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). cbn [nth_error] in C1 |- *. eapply (cellZ_frame _ _ _ _ _ _ C1); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. intros i Hi. cbn in Hi.
                 rewrite (OBJI i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); lia)). apply IDOUT; [| lia]. intros a v Hin. destruct (WSZ a v Hin) as [-> | [A1 A2]]; lia. }
        split. { eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 (ba + 8) (ba_bytes b') WSOK ltac:(right; left; reflexivity) SEP8 ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
                 intros i Hi. cbn in Hi. apply OBJI. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). lia. }
        split. { (lazymatch goal with |- ?G => let G' := eval unfold b' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end). eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 (ba + 16) (Z.of_nat (length its)) WSOK ltac:(right; right; left; reflexivity) SEP16 ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
                 intros i Hi. cbn in Hi. apply OBJI. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). lia. }
        split. { (lazymatch goal with |- ?G => let G' := eval unfold b' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ba_items] in G in change_no_check G' end). intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl.
                 eapply (cellZ_frame _ _ _ _ _ _ (putl_hit SG ws M0 (ba + 24 + 8 * Z.of_nat j) (fst mn) WSOK ltac:(do 3 right; exact (itemw_nth its (ba + 24) j mn Hj)) (SEPI j mn Hj) ltac:(lia))); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
                 intros i Hi. cbn in Hi. apply OBJI. (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end). lia. }
        eapply (writableZ_frame _ _ _ _ _ CW). intros i Hi. rewrite (OBJI i ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hi)).
        destruct (decide (IDEAL (Z_to_bv 64 i) = M0 (Z_to_bv 64 i))) as [E | NE]; [left; exact E | right; exact (proj2 (putl_changed ws M0 _ WSOK NE))].
      - unfold gq' in Hb0. cbn [nth_error] in Hb0. pose proof (nth_error_In _ _ Hb0) as Hin0.
        destruct (R6 (S i) b0 ltac:(rewrite Hgq; exact Hb0)) as (C1 & C2 & C3 & C4 & CW). rewrite Hgq in C1.
        assert (Hb2 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite Hgq; right; exact Hin0).
        destruct (batch_facts bt st Lc FF W b0 Hb2) as (_ & BL0 & D1 & D2).
        assert (RB : 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64) by (clear -D1 D2 SBH B3 B4 B5; ulia). unfold BATCHSZ, BATCHCAP in *.
        assert (SM : forall i0, ba_addr b0 <= i0 < ba_addr b0 + 8192 -> M0' (Z_to_bv 64 i0) = M0 (Z_to_bv 64 i0)) by (intros i0 Hi0; apply (RESTSAME b0 Hin0); (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hi0).
        split. { (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). cbn [nth_error] in C1 |- *. eapply (cellZ_frame _ _ _ _ _ _ C1); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply SM; lia]. }
        split. { eapply (cellZ_frame _ _ _ _ _ _ C2); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply SM; lia]. }
        split. { eapply (cellZ_frame _ _ _ _ _ _ C3); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply SM; lia]. }
        split. { intros j mn Hj. pose proof (nth_error_lt _ _ _ Hj) as Hl. eapply (cellZ_frame _ _ _ _ _ _ (C4 j mn Hj)); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i0 Hi0; cbn in Hi0; apply SM; lia]. }
        eapply (writableZ_frame _ _ _ _ _ CW). intros i0 Hi0. left. apply SM. exact Hi0. }
    split; [exact WSOK|]. split; [exact WSX|]. split; [exact NL|]. split; [exact NB|].
    destruct (R6 0%nat b ltac:(rewrite Hgq; reflexivity)) as (_ & _ & _ & _ & CW). exact CW.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem secfree_unmap : forall st' Lc FF (Mmid M' : mem) mdl' lo hi (qt qg : Z),
    WFq bt st' Lc FF qt qg -> Rep bt st' Lc FF Mmid mdl' -> dyn_ok IA lo hi ->
    (forall lo' hi', In (lo', hi') (all_ranges bt st') -> hi <= lo' \/ hi' <= lo) ->
    (forall a : word, ~ (lo <= u a < hi) -> M' a = Mmid a) ->
    Rep bt st' Lc FF M' mdl'.
  Proof.
    intros st' Lc FF Mmid M' mdl' lo hi qt qg W R DOK AP EQ.
    apply (Rep_local bt st' Lc FF Mmid M' mdl' W R). intros z Hs Hr. apply EQ. rewrite u64_lit by lia.
    intros Hz. exact (apart_not_supp bt st' Lc FF W lo hi DOK AP z Hz Hs).
  Qed.

  (* [comment removed for export] *)
  Lemma secfree_map_apart : forall st Lc FF (qt qg : Z) ba it its rest i s, WFq bt st Lc FF qt qg ->
    a_gq st = BATCH ba (it :: its) :: rest -> nth_error (a_sec st) i = Some s ->
    dyn_ok IA (sc_map s) (sc_map s + sc_mapsz s)
    /\ forall lo' hi', In (lo', hi') (all_ranges bt (op_recycle_sec st i)) -> sc_map s + sc_mapsz s <= lo' \/ hi' <= sc_map s.
  Proof.
    intros st Lc FF qt qg ba it its rest i s W Hgq Hnth.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (M1 & M2 & _) & _).
    assert (Hs : In s (a_sec st)) by exact (nth_error_In _ _ Hnth).
    split; [exact (proj1 (M1 _ _ (all_ranges_dyn bt st _ (sec_dyn st s Hs))))|].
    (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_sec in G in change_no_check G' end). rewrite (op_qitem_eq st ba it its rest Hgq).
    set (SR := swap_remove (a_sec st) i). pose proof (swap_remove_perm (a_sec st) i s Hnth) as PERM. fold SR in PERM.
    set (st' := op_sec_free (set_gq st (BATCH ba its :: rest)) i).
    assert (PMR : Permutation ((sc_map s, sc_map s + sc_mapsz s) :: all_ranges bt st') (all_ranges bt st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). change (a_sec st') with SR. change (a_dep st') with (a_dep st).
      set (f := fun s0 : schunk => (sc_map s0, sc_map s0 + sc_mapsz s0)).
      set (DD := map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st))).
      transitivity (bt_fixed bt ++ f s :: map f SR ++ DD); [apply Permutation_middle|].
      apply Permutation_app_head. change (f s :: map f SR ++ DD) with (map f (s :: SR) ++ DD).
      apply Permutation_app_tail. exact (Permutation_map f PERM). }
    assert (PWA : PW (all_ranges bt st)).
    { apply PW_of_splits. intros l1 [xlo xhi] l2 [ylo yhi] E Hy. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). exact (M2 l1 l2 xlo xhi ylo yhi E Hy). }
    pose proof (PW_perm _ _ (Permutation_sym PMR) PWA) as [SEPS _].
    intros lo' hi' Hin. pose proof (seps_In _ _ _ SEPS Hin) as D. cbn in D. exact D.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition foot_recycle_sec (st : ast) (i : nat) (s : schunk) (z : Z) : Prop :=
    (IB bt + 120 <= z < IB bt + 728)
    \/ (bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8)
    \/ (idx_lo st <= z < idx_hi st)
    \/ (sc_map s <= z < sc_map s + sc_mapsz s)
    \/ (sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s))
    \/ (T + 2768 <= z < T + 3168) \/ CEIL <= z.

  Definition OPS_REPX_recycle_sec : Prop := forall (X : Z -> Prop) (Xd : Xdec X) st Lc FF (M M' : mem) mdl mdl' ba m n its rest i s (qt qg : Z),
    WFq bt st Lc FF qt qg -> RepX bt X st Lc FF M mdl ->
    a_gq st = BATCH ba ((m, n) :: its) :: rest -> is_primary n = false -> nth_error (a_sec st) i = Some s -> sc_user s = m + 16 ->
    (forall z, X z -> XB bt st z) -> (forall z, qhdr bt z -> X z) -> (forall z, ba <= z < ba + BATCHSZ -> X z) ->
    (forall a : word, qhdr bt (u a) -> M' a <> None) ->
    (forall a : word, M' a <> M a -> (foot_recycle_sec st i s (u a) \/ X (u a)) /\ (M' a <> None \/ sc_map s <= u a < sc_map s + sc_mapsz s)) ->
    let len := Z.of_nat (length (a_sec st)) in
    cellZ SG M' (IB bt + 120) 8 (len - 1) -> byteZ SG M' (IB bt + 680) 0 ->
    (forall sl, Z.of_nat i < len - 1 -> nth_error (a_sec st) (length (a_sec st) - 1) = Some sl ->
        cellZ SG M' (bt_ptrarr bt + 8 * Z.of_nat i) 8 (sc_map sl) /\ cellZ SG M' (sc_map sl + 24) 8 (Z.of_nat i)) ->
    Permutation ((Z_to_bv 64 (sc_map s), Z_to_bv 64 (sc_mapsz s)) :: vm_maps (m_vmmaps mdl')) (vm_maps (m_vmmaps mdl)) ->
    (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a) ->
    Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl')) ->
    (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a) ->
    Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0
                                   /\ 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
           (m_vm_lazy mdl') ->
    vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl) ->
    vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) ->
    vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    (* [comment removed for export] *)
    MInv (release_aa (a_aa st) (sc_map s) (sc_n s)) mdl' -> eager_used mdl' + sc_mapsz s <= eager_used mdl ->
    RepX bt X (op_recycle_sec st i) Lc FF M' mdl'.

  Theorem OPS_REPX_recycle_sec_pf : OPS_REPX_recycle_sec.
  Proof.
    intros X Xd st Lc FF M M' mdl mdl' ba m n its rest i s qt qg W (M0 & R & D) Hgq HPn Hnth Hus XBD XQ XO HDEF STEP. cbn zeta.
    intros CNCH CMTX CMOVE PM NA NP' LZ FL' E1 E2 E3 E4 E6 E5 MI EAG.
    set (len := Z.of_nat (length (a_sec st))) in *. set (gq' := BATCH ba its :: rest).
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & (WQ1 & WQ2 & WQ3 & WQ4 & WQ5 & WQ6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & IN8 & _ & INT & _) & _).
    assert (Hs : In s (a_sec st)) by exact (nth_error_In _ _ Hnth).
    destruct (sec_facts bt st Lc FF W s Hs) as (SA1 & SA2 & SA3 & SA4 & SA5 & SA6 & SA7 & SA8).
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN8)) as ((PD1 & PD2 & PD3 & PD4 & PD5) & _).
    pose proof (space_vs_fixed bt st Lc FF W _ _ IN8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as SP8'.
    pose proof (nth_error_lt _ _ _ Hnth) as Hil.
    assert (PTRfacts : 0 <= Z.of_nat i < len /\ len <= a_nres st /\ 8 * a_nres st <= 2 ^ 23) by ((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); clear -Hil S1 S3; lia).
    (* [comment removed for export] *)
    assert (XDYN : forall lo hi z, In (lo, hi) (dyn_ranges st) -> lo <= z < hi -> ~ X z).
    { intros lo hi z Hin Hz HX. destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as ((_ & _ & _ & D4 & _) & _).
      destruct (XB_zone bt st Lc FF W z (XBD z HX)) as [[HI _] | [HS _]]; [clear -HI Hz D4; lia|].
      destruct (space_vs_dyn bt st Lc FF W lo hi Hin); clear -H HS Hz; ulia. }
    assert (XPTR : forall z, bt_ptrarr bt <= z < bt_ptrarr bt + 2 ^ 23 -> ~ X z).
    { intros z Hz HX. destruct (XB_zone bt st Lc FF W z (XBD z HX)) as [[HI _] | [HS _]]; [clear -HI Hz PD4; lia | clear -HS Hz SP8'; ulia]. }
    assert (XIMG : forall z, ia_img_lo IA <= z < ia_img_hi IA -> ~ qhdr bt z -> ~ X z).
    { intros z Hz NQ HX. destruct (XB_zone bt st Lc FF W z (XBD z HX)) as [[_ Q] | [HS _]]; [exact (NQ Q) | clear -HS Hz I2 B3; ulia]. }
    pose proof (sec_dyn st s Hs) as HDs.
    pose proof (Xdec_iv (sc_map s) (sc_map s + sc_mapsz s)) as Md.
    set (Mx := fun a : word => if Md (u a) then M0 a else M' a).
    assert (MM0 : forall a : word, ~ X (u a) -> M a = M0 a).
    { intros a NX. destruct (decide (M a = M0 a)) as [E | NE]; [exact E | exfalso; exact (NX (proj1 (D a NE)))]. }
    (* [comment removed for export] *)
    assert (KEEPB : forall b0, In b0 rest -> forall z, ba_addr b0 <= z < ba_addr b0 + BATCHSZ -> ~ X z -> Mx (Z_to_bv 64 z) = M0 (Z_to_bv 64 z)).
    { intros b0 Hb0 z Hz NX. assert (Hb2 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; right; rewrite Hgq; right; exact Hb0).
      destruct (batch_facts bt st Lc FF W b0 Hb2) as (_ & _ & C1 & C2).
      assert (Hr : 0 <= z < 2 ^ 64) by (clear -Hz C1 C2 B3 B4 B5; ulia).
      (lazymatch goal with |- ?G => let G' := eval unfold Mx in G in change_no_check G' end). rewrite (u64_lit z) by lia. destruct (Md z) as [IM | NM]; [reflexivity|].
      rewrite <- (MM0 (Z_to_bv 64 z)) by (rewrite u64_lit by lia; exact NX).
      destruct (decide (M' (Z_to_bv 64 z) = M (Z_to_bv 64 z))) as [E | NE]; [exact E | exfalso].
      destruct (STEP _ NE) as [[F | F] _]; rewrite u64_lit in F by lia; [| exact (NX F)].
      pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _).
      assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
      unfold foot_recycle_sec in F. destruct F as [F|[F|[F|[F|[F|[F|F]]]]]].
      - clear -F Hz C1 INI I2 B3. ulia.
      - clear -F Hz C1 C2 SP8' PTRfacts. ulia.
      - unfold idx_lo, idx_hi in F. destruct (nth_error (a_sec st) (length (a_sec st) - 1)) as [sl|] eqn:EL; [| lia].
        pose proof (nth_error_In _ _ EL) as Hsl. destruct (sec_facts bt st Lc FF W sl Hsl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
        destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st sl Hsl)) as [SP | SP]; clear -SP F Hz C1 C2 Q5 Q6 Q7; ulia.
      - exact (NM F).
      - unfold sh_lo, sh_hi in F. clear -F Hz C1 SA1 SA2 B3 B6 B7. Zlia.
      - clear -F Hz C1 C2 TPG. ulia.
      - clear -F Hz C2 B4. ulia. }
    destruct (ideal_head_item X Xd st Lc FF M0 Mx mdl ba m n its rest qt qg W R Hgq XQ XO KEEPB) as (WSOK & WSX & NL & NB & CW).
    set (ws := head_ws ba its rest) in *.
    set (M0m := fun a : word => if Xd (u a) then putl M0 ws a else Mx a) in *.
    set (M0' := fun a : word => if Xd (u a) then putl M0 ws a else M' a).
    assert (OFFXM : forall z, ~ X z -> ~ (sc_map s <= z < sc_map s + sc_mapsz s) -> 0 <= z < 2 ^ 64 -> M0m (Z_to_bv 64 z) = M' (Z_to_bv 64 z)).
    { intros z NX NM Hr. (lazymatch goal with |- ?G => let G' := eval unfold M0m, Mx in G in change_no_check G' end). rewrite (u64_lit z) by lia. destruct (Xd z); [contradiction|]. destruct (Md z); [contradiction | reflexivity]. }
    (* [comment removed for export] *)
    assert (QREL : forall x, In x (flat_map ba_items gq') <-> In x (flat_map ba_items (a_gq st)) /\ x <> (m, n)).
    { destruct (quar_gq_head st ba (m, n) its rest Hgq) as [EQ0 _].
      assert (NDQ : List.NoDup (flat_map ba_items (a_tq st) ++ (m, n) :: (its ++ flat_map ba_items rest))) by (rewrite <- EQ0; exact (NoDup_map_inv _ _ WQ6)).
      intros x. rewrite Hgq. (lazymatch goal with |- ?G => let G' := eval unfold gq' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [flat_map ba_items] in G in change_no_check G' end). pose proof (NoDup_app_remove_l _ _ NDQ) as ND2. inversion ND2 as [| ? ? NI _]; subst. split.
      - intros Hx. split; [right; exact Hx | intros ->; exact (NI Hx)].
      - intros [[E | Hx] NE]; [exfalso; apply NE; rewrite E; reflexivity | exact Hx]. }
    assert (RC : Rep bt (op_sec_free (set_gq st gq') i) Lc FF M0m mdl').   (* [comment removed for export] *)
    { apply (OPS_REP_secfree_pf bt st Lc FF M0 M0m mdl mdl' gq' m n i s qt qg W R QREL ltac:(rewrite Hgq; (lazymatch goal with |- ?G => let G' := eval cbn [flat_map ba_items] in G in change_no_check G' end); left; reflexivity) HPn Hnth Hus); try assumption.
      - (* [comment removed for export] *) intros a NE. unfold M0m in NE |- *. destruct (Xd (u a)) as [HX | NX].
        + destruct (putl_changed ws M0 a WSOK NE) as ((a0 & v0 & Hin & Hz) & Dd). split; [| exact Dd].
          destruct (WSX a0 v0 (u a) Hin Hz) as (_ & [Q | Q]); [left; exact Q | right; left; exists (BATCH ba ((m, n) :: its)); split; [rewrite Hgq; left; reflexivity | exact Q]].
        + unfold Mx in NE |- *. destruct (Md (u a)) as [IM | NM]; [exfalso; exact (NE eq_refl)|].
          rewrite <- (MM0 a NX) in NE. destruct (STEP a NE) as [[F | F] Dd]; [| contradiction].
          split; [| destruct Dd as [Dd | Dd]; [exact Dd | contradiction]].
          unfold foot_recycle_sec in F. (lazymatch goal with |- ?G => let G' := eval unfold foot_secfree in G in change_no_check G' end).
          destruct F as [F|[F|[F|[F|[F|[F|F]]]]]]; [do 2 right; left; exact F | do 3 right; left; exact F | do 4 right; left; exact F | contradiction | do 5 right; left; exact F | do 6 right; left; exact F | do 7 right; exact F].
      - (* [comment removed for export] *) eapply (cellZ_frame _ _ _ _ _ _ CNCH); [clear -INI I1; lia | clear -INI I2; ulia |]. intros z Hz. cbn in Hz.
        apply OFFXM; [apply XIMG; [clear -Hz INI; lia | (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); clear -Hz; lia] | | clear -Hz INI I1 I2; ulia].
        destruct (RNG _ _ (all_ranges_dyn bt st _ HDs)) as ((_ & _ & _ & D4 & _) & _). clear -Hz INI D4. lia.
      - (* [comment removed for export] *) eapply (byteZ_frame _ _ _ _ _ CMTX); [clear -INI I1; lia | clear -INI I2; ulia |].
        apply OFFXM; [apply XIMG; [clear -INI; lia | (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); lia] | | clear -INI I1 I2; ulia].
        destruct (RNG _ _ (all_ranges_dyn bt st _ HDs)) as ((_ & _ & _ & D4 & _) & _). clear -INI D4. lia.
      - (* [comment removed for export] *) intros sl LT HL. destruct (CMOVE sl LT HL) as [CP CI]. pose proof (nth_error_In _ _ HL) as Hsl.
        destruct (sec_facts bt st Lc FF W sl Hsl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
        assert (NEs : sl <> s).
        { intros ->. pose proof (proj1 (NoDup_nth_error (a_sec st)) (NoDup_map_inv _ _ S5) i (length (a_sec st) - 1)%nat Hil ltac:(rewrite Hnth, HL; reflexivity)). unfold len in LT. lia. }
        destruct (sec_cases bt st Lc FF W sl s Hsl Hs) as [E | DJ]; [exact (False_ind _ (NEs E))|].
        split.
        + eapply (cellZ_frame _ _ _ _ _ _ CP); [clear -PD1; lia | clear -PTRfacts PD1 PD2 PD3; ulia |]. intros z Hz. cbn in Hz.
          apply OFFXM; [apply XPTR; clear -Hz PTRfacts; lia | | clear -Hz PTRfacts PD1 PD2 PD3; ulia].
          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 HDs) as D8. hnf in D8. cbn in D8. clear -Hz PTRfacts D8. lia.
        + eapply (cellZ_frame _ _ _ _ _ _ CI); [clear -Q1; lia | clear -Q2 Q5 Q6 Q7; ulia |]. intros z Hz. cbn in Hz.
          apply OFFXM; [apply (XDYN _ _ z (sec_dyn st sl Hsl)); clear -Hz Q5 Q6 Q7; unfold PG in *; lia | clear -Hz DJ Q5 Q6 Q7; unfold PG in *; lia | clear -Hz Q1 Q2 Q5 Q6 Q7; ulia]. }
    (* [comment removed for export] *)
    pose proof (OPS_WFq_recycle_sec_pf bt st Lc FF ba m n its rest i s qt qg W Hgq HPn Hnth Hus) as W'.
    destruct (secfree_map_apart st Lc FF qt qg ba (m, n) its rest i s W Hgq Hnth) as [DOK AP].
    assert (EST : op_recycle_sec st i = op_sec_free (set_gq st gq') i).
    { (lazymatch goal with |- ?G => let G' := eval unfold op_recycle_sec in G in change_no_check G' end). rewrite (op_qitem_eq st ba (m, n) its rest Hgq). reflexivity. }
    rewrite EST in W', AP |- *.
    assert (RF : Rep bt (op_sec_free (set_gq st gq') i) Lc FF M0' mdl').
    { apply (secfree_unmap _ Lc FF M0m M0' mdl' _ _ qt qg W' RC DOK AP). intros a NM. (lazymatch goal with |- ?G => let G' := eval unfold M0', M0m, Mx in G in change_no_check G' end).
      destruct (Xd (u a)); [reflexivity|]. destruct (Md (u a)); [contradiction | reflexivity]. }
    exists M0'. split; [exact RF|].
    intros a NE. unfold M0' in NE. destruct (Xd (u a)) as [HX | NX]; [| exfalso; exact (NE eq_refl)]. split; [exact HX|].
    destruct (decide (M' a = M a)) as [E1' | NE1].
    - destruct (decide (M a = M0 a)) as [E2' | NE2]; [| rewrite E1'; exact (proj2 (D a NE2))].
      rewrite E1', E2' in NE. assert (NE3 : putl M0 ws a <> M0 a) by (intros E3'; apply NE; symmetry; exact E3').
      destruct (putl_changed ws M0 a WSOK NE3) as ((a0 & v0 & Hin & Hz) & _).
      destruct (WSX a0 v0 (u a) Hin Hz) as (_ & [Q | Q]); [exact (HDEF a Q)|].
      rewrite E1', E2'. pose proof (proj1 (CW (u a) Q)) as DF.
      assert (EA : Z_to_bv 64 (u a) = a) by (apply bv_eq; rewrite u64_lit by (pose proof (u64_range a); lia); reflexivity). rewrite EA in DF. exact DF.
    - destruct (STEP a NE1) as [_ [Dd | IM]]; [exact Dd|]. exfalso. exact (XDYN _ _ (u a) HDs IM HX).
  Qed.
End RcS.
End AsAinvOpsRc63.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvOpsRc93.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3.
Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.

Section LiveWF.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Theorem OPS_WFq_sec_free_live_pf : forall st L1 L2 FF p n i s (qt qg : Z),
    WFq bt st (L1 ++ (p, n) :: L2) FF qt qg -> is_primary n = false ->
    nth_error (a_sec st) i = Some s -> sc_user s = p ->
    WFq bt (op_sec_free st i) (L1 ++ L2) FF qt qg.
  Proof using.
    intros st L1 L2 FF p n i s qt qg W HP Hnth Hus.
    set (Lc := L1 ++ (p, n) :: L2) in *. set (Lc' := L1 ++ L2).
    pose proof W as ((WR1 & WR2) & WC & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM & WMP & (G1 & G2 & G3) & GBT).
    assert (Hin : In (p, n) Lc) by ((lazymatch goal with |- ?G => let G' := eval unfold Lc in G in change_no_check G' end); apply in_or_app; right; left; reflexivity).
    assert (INL : forall x, In x Lc' <-> In x Lc /\ x <> (p, n)) by (intros x; (lazymatch goal with |- ?G => let G' := eval unfold Lc', Lc in G in change_no_check G' end); apply in_remove_mid; exact LV2).
    assert (Hs : In s (a_sec st)) by (exact (nth_error_In _ _ Hnth)).
    assert (Hsn : sc_n s = n).
    { destruct (S7 p n Hin HP) as (sc & Hsc & Eu & En). rewrite <- (sec_user_inj bt st Lc FF sc s W Hsc Hs ltac:(lia)). exact En. }
    assert (NQ : ~ In (p - 16, n) (quar st)).
    { pose proof (proj1 (S6 s Hs)) as X. rewrite Hus, Hsn in X. exact (X Hin). }
    set (SR := swap_remove (a_sec st) i).
    pose proof (swap_remove_perm (a_sec st) i s Hnth) as PERM. fold SR in PERM.
    assert (NDS : List.NoDup (s :: SR)) by (exact (Permutation_NoDup (Permutation_sym PERM) (NoDup_map_inv _ _ S5))).
    assert (INS : forall x, In x SR <-> In x (a_sec st) /\ x <> s).
    { intros x. split.
      - intros Hx. split; [exact (Permutation_in x PERM (or_intror Hx))|]. intros ->. inversion NDS as [| ? ? NI _]; subst. exact (NI Hx).
      - intros [Hx NE]. destruct (Permutation_in x (Permutation_sym PERM) Hx) as [E | Hx']; [exfalso; exact (NE (eq_sym E)) | exact Hx']. }
    set (st' := op_sec_free st i).
    assert (ESEC : a_sec st' = SR) by reflexivity.
    assert (REGQ : forall m' n', In (m', n') (quar st) -> registered st (m' + 16) n' -> registered st' (m' + 16) n').
    { intros m' n' Hq (s0 & Hs0 & Eu0 & En0). exists s0. split; [| exact (conj Eu0 En0)]. rewrite ESEC. apply INS. split; [exact Hs0|].
      intros ->. apply NQ. replace (p - 16) with m' by lia. rewrite <- Hsn, En0. exact Hq. }
    assert (LIVC : forall c a, in_live_c Lc' c a <-> in_live_c Lc c a).
    { intros c a. (lazymatch goal with |- ?G => let G' := eval unfold in_live_c in G in change_no_check G' end). split.
      - intros (p' & n' & Hi & X). exists p', n'. split; [exact (proj1 (proj1 (INL _) Hi)) | exact X].
      - intros (p' & n' & Hi & X). exists p', n'. split; [| exact X]. apply INL. split; [exact Hi|]. intros E. injection E as -> ->. destruct X as (X & _). rewrite HP in X. discriminate X. }
    assert (WM' : wf_meter st').
    { (* [comment removed for export] *)
      destruct WM as (M1 & M2 & M3 & M4 & M5). (lazymatch goal with |- ?G => let G' := eval unfold wf_meter in G in change_no_check G' end).
      change (a_kact st') with (a_kact st). change (a_shsec st') with (a_shsec st + 2 * PG). rewrite ESEC. change (a_reg st') with (a_reg st).
      change (sum_mu st') with (sum_mu st).
      pose proof (Permutation_length PERM) as LEN. cbn [length] in LEN.
      split; [exact M1|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); clear -M2; lia|]. split; [rewrite <- LEN in M3; rewrite Nat2Z.inj_succ in M3; clear -M3; lia|]. split; [exact M4 | exact M5]. }
    (lazymatch goal with |- ?G => let G' := eval unfold WFq in G in change_no_check G' end).
    split; [| split; [exact WC | split; [| split; [| split; [| split; [exact WK | split; [exact WD | split; [exact WM' | split; [| split; [| exact GBT]]]]]]]]]].
    - (* [comment removed for export] *)
      split; [| exact WR2].
      intros c' Hc'. destruct (WR1 c' Hc') as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & PART' & FHK').
      (lazymatch goal with |- ?G => let G' := eval unfold wf_region in G in change_no_check G' end). change (a_reg st' c') with (a_reg st c'). do 8 (split; [assumption|]). split; [exact Z9|]. split; [| exact FHK'].
      apply partition_part5. apply partition_part5 in PART'. destruct PART' as (PP & PN1 & PN2).
      split; [| exact (conj PN1 PN2)].
      apply (part5_ext _ _ _ _ _ _ _ _ _ _ _ PP). intros a. split; [exact (LIVC c' a)|]. split; [am_tauto | split; [am_tauto | split; [am_tauto | am_tauto]]].
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_quarantine_q in G in change_no_check G' end). change (a_tq st') with (a_tq st). change (a_gq st') with (a_gq st). change (quar st') with (quar st).
      split. { rewrite Forall_forall in Q1 |- *. intros b Hb. destruct (Q1 b Hb) as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
               intros m' n' Hi. destruct (B3 m' n' Hi) as (N & [X | [X RG]]); (split; [exact N|]); [left; exact X | right; split; [exact X|]].
               apply REGQ; [| exact RG]. (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). apply in_flat_map. exists b. split; [apply in_or_app; left; exact Hb | exact Hi]. }
      split. { rewrite Forall_forall in Q2 |- *. intros b Hb. destruct (Q2 b Hb) as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
               intros m' n' Hi. destruct (B3 m' n' Hi) as (N & [X | [X RG]]); (split; [exact N|]); [left; exact X | right; split; [exact X|]].
               apply REGQ; [| exact RG]. (lazymatch goal with |- ?G => let G' := eval unfold quar in G in change_no_check G' end). apply in_flat_map. exists b. split; [apply in_or_app; right; exact Hb | exact Hi]. }
      split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5 | exact Q6].
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_secondary in G in change_no_check G' end). rewrite ESEC. change (a_nres st') with (a_nres st). change (quar st') with (quar st).
      split. { pose proof (Permutation_length PERM) as PL. cbn [length] in PL. lia. }
      split; [exact S2|]. split; [exact S3|].
      split. { intros s0 Hs0. exact (S4 s0 (proj1 (proj1 (INS s0) Hs0))). }
      split. { pose proof (Permutation_NoDup (Permutation_sym (Permutation_map sc_map PERM)) S5) as X. cbn [map] in X. inversion X; assumption. }
      split. { intros s0 Hs0. apply INS in Hs0. destruct Hs0 as [Hs0 NEs]. rewrite <- (S6 s0 Hs0). rewrite (INL (sc_user s0, sc_n s0)). split; [am_tauto|].
               intros X. split; [exact X|]. intros E. injection E as E1 E2. apply NEs. apply (sec_user_inj bt st Lc FF s0 s W Hs0 Hs). lia. }
      split. { intros p' n' Hi HP'. apply INL in Hi. destruct Hi as [Hi NE]. destruct (S7 p' n' Hi HP') as (s0 & Hs0 & Eu0 & En0). exists s0. split; [| exact (conj Eu0 En0)].
               rewrite ESEC. apply INS. split; [exact Hs0|]. intros ->. apply NE. f_equal; lia. }
      intros m' n' Hq HP'. exact (REGQ m' n' Hq (S8 m' n' Hq HP')).
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold wf_live in G in change_no_check G' end). split; [| split].
      + intros p' n' Hi. apply INL in Hi. exact (LV1 p' n' (proj1 Hi)).
      + (lazymatch goal with |- ?G => let G' := eval unfold Lc' in G in change_no_check G' end) . unfold Lc in LV2. exact (NoDup_remove_1 _ _ _ LV2).
      + intros p1 n1 p2 n2 H1 H2 NE. exact (LV3 p1 n1 p2 n2 (proj1 (proj1 (INL _) H1)) (proj1 (proj1 (INL _) H2)) NE).
    - (* [comment removed for export] *)
      destruct WMP as (M1 & M2 & MREST).
      assert (PMR : Permutation ((sc_map s, sc_map s + sc_mapsz s) :: all_ranges bt st') (all_ranges bt st)).
      { (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). rewrite ESEC. change (a_dep st') with (a_dep st).
        set (f := fun s0 : schunk => (sc_map s0, sc_map s0 + sc_mapsz s0)).
        set (DD := map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st))).
        transitivity (bt_fixed bt ++ f s :: map f SR ++ DD); [apply Permutation_middle|].
        apply Permutation_app_head. change (f s :: map f SR ++ DD) with (map f (s :: SR) ++ DD).
        apply Permutation_app_tail. exact (Permutation_map f PERM). }
      split. { intros lo hi Hi. apply (M1 lo hi). exact (Permutation_in _ PMR (or_intror Hi)). }
      destruct MREST as (K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20).
      split; [| do 17 (split; [assumption|]); intros b0 n0 lo hi Hb0 Hi; apply (K20 b0 n0 lo hi Hb0);
                unfold dyn_ranges in Hi |- *; rewrite ESEC in Hi; change (a_dep st') with (a_dep st) in Hi; rewrite !in_app_iff in Hi |- *;
                destruct Hi as [Hi | Hi]; [left | right; exact Hi];
                apply in_map_iff in Hi; destruct Hi as (s0 & E0 & Hs0); apply in_map_iff; exists s0; split; [exact E0 | exact (proj1 (proj1 (INS s0) Hs0))]].
      apply AsAinvOpsS3.splits_of_PW.
      assert (PWA : PW (all_ranges bt st)).
      { apply PW_of_splits. intros l1 [xlo xhi] l2 [ylo yhi] E Hy. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). exact (M2 l1 l2 xlo xhi ylo yhi E Hy). }
      exact (proj2 (PW_perm _ _ (Permutation_sym PMR) PWA)).
    - (* [comment removed for export] *)
      split; [exact G1|]. (lazymatch goal with |- ?G => let G' := eval unfold Lc' in G in change_no_check G' end) . unfold Lc in G2, G3. rewrite length_app in G2 |- *. rewrite PHI_app in G3 |- *. cbn [PHI] in G3.
      destruct (LV1 p n Hin) as (N1 & _). fold (PHI L2) in G3. cbn [snd] in G3. unfold MBLK in *. split; [rewrite Nat2Z.inj_add in *; cbn [length] in G2; lia | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma bounds_sec_free_live : forall st L1 L2 FF p n i B C K (qt qg : Z),
    WFq bt st (L1 ++ (p, n) :: L2) FF qt qg -> bounds st (L1 ++ (p, n) :: L2) B C K ->
    bounds (op_sec_free st i) (L1 ++ L2) (Z.max 0 (B - (n + MBLK))) (Z.max 0 (C - 1)) K.
  Proof using.
    intros st L1 L2 FF p n i B C K qt qg W ((B1 & B2) & B3 & B4).
    pose proof W as (_ & _ & _ & _ & (LV1 & _) & _).
    assert (P0 : 0 <= PHI (L1 ++ L2)).
    { apply PHI_nonneg. intros b m Hi. destruct (LV1 b m ltac:(apply in_app_or in Hi; apply in_or_app; destruct Hi as [Hi | Hi]; [left; exact Hi | right; right; exact Hi])) as (N1 & _). lia. }
    rewrite PHI_app in B1, B2, P0. cbn [PHI snd] in B1, B2. fold (PHI L2) in B1, B2. rewrite length_app in B3. cbn [length] in B3.
    (lazymatch goal with |- ?G => let G' := eval unfold bounds in G in change_no_check G' end). rewrite PHI_app, length_app. change (a_kact (op_sec_free st i)) with (a_kact st).
    split; [lia|]. split; [lia | exact B4].
  Qed.
End LiveWF.
End AsAinvOpsRc93.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvZone3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsD3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrameE3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvOpsRc23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53 AsAinvOpsRc63 AsAinvOpsRc93 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc53.AsAinvRelease3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= am_lia.
#[local] Notation u := bv_unsigned.

Section RC9.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SG := (bt_segs bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Ltac ulia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP in *; lia.
  Ltac uilia := unfold DEPOT_NIDS, DEPOT_MAP1 in *; unfold IB, DEPOT_TAB, SSOBJ, IA_FLAG, IA_INST, IASZ in *; ulia.
  Ltac dsj := repeat match goal with H : _ \/ _ |- _ => destruct H end.
  Ltac Zlia := try ceil; unfold AS_HEAPLO, AS_LO, PTRLO, SB, PG, FAKE_SIZE, IASZ, KSPACE, BATCHSZ, BATCHCAP, T_PC, PC_SZ, T_QC, T_UNW, NMAX in *; unfold boxed in *; dsj; Z.div_mod_to_equations; lia.


  (* [comment removed for export] *)
  Definition foot_secfree_live (st : ast) (i : nat) (s : schunk) (z : Z) : Prop :=
    (IB bt + 120 <= z < IB bt + 728)
    \/ (bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8)
    \/ (idx_lo st <= z < idx_hi st)
    \/ (sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s))
    \/ (T + 2768 <= z < T + 3168) \/ CEIL <= z.

  Definition OPS_REP_secfree_live : Prop := forall st L1 L2 FF (M M' : mem) mdl mdl' p n i s (qt qg : Z),
    WFq bt st (L1 ++ (p, n) :: L2) FF qt qg -> Rep bt st (L1 ++ (p, n) :: L2) FF M mdl ->
    is_primary n = false ->
    nth_error (a_sec st) i = Some s -> sc_user s = p ->
    let len := Z.of_nat (length (a_sec st)) in
    agrees_off (foot_secfree_live st i s) M M' ->
    cellZ SG M' (IB bt + 120) 8 (len - 1) -> byteZ SG M' (IB bt + 680) 0 ->
    (forall sl, Z.of_nat i < len - 1 -> nth_error (a_sec st) (length (a_sec st) - 1) = Some sl ->
        cellZ SG M' (bt_ptrarr bt + 8 * Z.of_nat i) 8 (sc_map sl) /\ cellZ SG M' (sc_map sl + 24) 8 (Z.of_nat i)) ->
    (* [comment removed for export] *)
    Permutation ((Z_to_bv 64 (sc_map s), Z_to_bv 64 (sc_mapsz s)) :: vm_maps (m_vmmaps mdl')) (vm_maps (m_vmmaps mdl)) ->
    (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a) ->
    Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl')) ->
    (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a) ->
    Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0
                                   /\ 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
           (m_vm_lazy mdl') ->
    vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl) ->
    vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) ->
    vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    (* [comment removed for export] *)
    MInv (release_aa (a_aa st) (sc_map s) (sc_n s)) mdl' -> eager_used mdl' + sc_mapsz s <= eager_used mdl ->
    Rep bt (op_sec_free st i) (L1 ++ L2) FF M' mdl'.

  Lemma PIN9dec : forall st i s, Xdec (fun z => (0 <= z < 0) \/ (0 <= z < 0) \/ (IB bt + 120 <= z < IB bt + 128) \/ (IB bt + 680 <= z < IB bt + 681)
      \/ (bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8) \/ (idx_lo st <= z < idx_hi st)
      \/ (sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s))).
  Proof using. intros st i s. repeat (apply Xdec_or; [apply Xdec_iv|]). apply Xdec_iv. Qed.

  Theorem OPS_REP_secfree_live_pf : OPS_REP_secfree_live.
  Proof using.
    intros st La Lb FF M M' mdl mdl' p n i s qt qg W R HPn Hnth Hus. cbn zeta.
    intros AGR CNCH CMTX CMOVE PM NA NP' LZ FL' E1 E2 E3 E4 E6 E5 MI EAG.
    set (Lc := La ++ (p, n) :: Lb) in *. set (Lc' := La ++ Lb).
    set (len := Z.of_nat (length (a_sec st))) in *.
    (* [comment removed for export] *)
    pose proof W as ((WR1 & WR2) & WC & (WQ1 & WQ2 & WQ3 & WQ4 & WQ5 & WQ6) & (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8) & (LV1 & LV2 & LV3) & WK & WD & WM' & (RNG & PW' & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & G).
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
    pose proof (image_facts bt st Lc FF W) as IMF. cbn zeta in IMF.
    destruct IMF as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & YC).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & SP4 & SP5) & SP6 & SP7 & SP8 & SPH). assert (SBH : AS_HEAPLO <= SBEG) by (clear -SP7 SPH; lia). box SP4. box SP5.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. pose proof (band_facts bt st Lc FF W) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    pose proof (thread_page_facts bt st Lc FF W) as (_ & _ & _ & _ & TPI & TPB).
    assert (TPG : T + PG <= SBEG \/ SBEG + KSPACE + PG <= T) by (apply (space_vs_fixed bt st Lc FF W _ _ INT); ulia).
    pose proof (img_pw bt st Lc FF W) as IPW. unfold img_ranges in IPW. cbn [PW seps fst snd] in IPW.
    destruct IPW as ((J1 & J2 & J3 & J4 & J5 & J6 & J7 & _) & _). box J1. box J2. box J3. box J4. box J5. box J6. box J7. box TPI. box TPB. box TPG.
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DC & DT & DR & _).
    assert (HC24 : 1 <= BATCHCLASS <= 30) by ((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia).
    (* [comment removed for export] *)
    assert (Hs : In s (a_sec st)) by exact (nth_error_In _ _ Hnth).
    assert (HinP : In (p, n) Lc) by ((lazymatch goal with |- ?G => let G' := eval unfold Lc in G in change_no_check G' end); apply in_or_app; right; left; reflexivity).
    assert (INL : forall x, In x Lc' <-> In x Lc /\ x <> (p, n)) by (intros x; (lazymatch goal with |- ?G => let G' := eval unfold Lc', Lc in G in change_no_check G' end); apply in_remove_mid; exact LV2).
    assert (Hsn : sc_n s = n).
    { destruct (S7 p n HinP HPn) as (sc & Hsc & Eu & En). rewrite <- (sec_user_inj bt st Lc FF sc s W Hsc Hs ltac:(lia)). exact En. }
    destruct (sec_facts bt st Lc FF W s Hs) as (SA1 & SA2 & SA3 & SA4 & SA5 & SA6 & SA7 & SA8).
    pose proof (nth_error_lt _ _ _ Hnth) as Hil.
    set (SR := swap_remove (a_sec st) i).
    pose proof (swap_remove_perm (a_sec st) i s Hnth) as PERM. fold SR in PERM.
    assert (NDS0 : List.NoDup (a_sec st)) by exact (NoDup_map_inv _ _ S5).
    assert (NDS : List.NoDup (s :: SR)) by exact (Permutation_NoDup (Permutation_sym PERM) NDS0).
    assert (INSR : forall x, In x SR <-> In x (a_sec st) /\ x <> s).
    { intros x. split.
      - intros Hx. split; [exact (Permutation_in x PERM (or_intror Hx))|]. intros ->. inversion NDS as [| ? ? NI _]; subst. exact (NI Hx).
      - intros [Hx NE]. destruct (Permutation_in x (Permutation_sym PERM) Hx) as [E | Hx']; [exfalso; exact (NE (eq_sym E)) | exact Hx']. }
    set (st' := op_sec_free st i).
    assert (ESEN : sec_entry st i = s) by ((lazymatch goal with |- ?G => let G' := eval unfold sec_entry in G in change_no_check G' end); exact (nth_error_nth _ _ _ Hnth)).
    (* [comment removed for export] *)
    assert (GQfacts : forall z, gq_objs st z -> exists b, In b (a_tq st ++ a_gq st) /\ In b (a_gq st) /\ carved bt st BATCHCLASS (ba_addr b)
                        /\ SBEG <= ba_addr b /\ ba_addr b + BATCHSZ <= SBEG + KSPACE /\ ba_addr b <= z < ba_addr b + BATCHSZ).
    { intros z (b & Hb & Hz). assert (Hb2 : In b (a_tq st ++ a_gq st)) by (apply in_app_iff; right; exact Hb).
      destruct (batch_facts bt st Lc FF W b Hb2) as (CVb & _ & Bl1 & Bl2). exists b. repeat (split; [assumption|]). exact Hz. }
    assert (GQspace : forall z, gq_objs st z -> SBEG <= z < SBEG + KSPACE).
    { intros z Gz. destruct (GQfacts z Gz) as (b & _ & _ & _ & Bl1 & Bl2 & Hz). lia. }
    (* [comment removed for export] *)
    assert (IDXfacts : forall z, idx_lo st <= z < idx_hi st -> exists sl, nth_error (a_sec st) (length (a_sec st) - 1) = Some sl /\ In sl (a_sec st) /\ sc_map sl + 24 <= z < sc_map sl + 32).
    { intros z Hz. unfold idx_lo, idx_hi in Hz. destruct (nth_error (a_sec st) (length (a_sec st) - 1)) as [sl|] eqn:EL; [| lia].
      exists sl. split; [reflexivity|]. split; [exact (nth_error_In _ _ EL) | exact Hz]. }
    (* [comment removed for export] *)
    assert (RMSband : forall z, sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s) -> SB <= z < AS_HEAPLO).
    { intros z Hz. unfold sh_lo, sh_hi in Hz. clear -Hz SA1 SA2 B6 B7. Zlia. }
    assert (PTRfacts : 0 <= Z.of_nat i < len /\ len <= a_nres st /\ 8 * a_nres st <= 2 ^ 23) by ((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); clear -Hil S1 S3; lia).
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN8)) as ((PD1 & PD2 & PD3 & PD4 & PD5) & _). box PD4. box PD5.
    pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ IN8) (all_ranges_fixed bt st _ INT) ltac:(intros E; injection E; intros; ulia)) as D8T. hnf in D8T. cbn in D8T. box D8T.
    pose proof (space_vs_fixed bt st Lc FF W _ _ IN8 ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as SP8'. box SP8'.
    assert (IDXdyn : forall z, idx_lo st <= z < idx_hi st -> exists sl, In sl (a_sec st) /\ sc_map sl + 24 <= z < sc_map sl + 32 /\ sc_map sl + 32 <= sc_map sl + sc_mapsz sl
                     /\ 0 < sc_map sl /\ sc_map sl + sc_mapsz sl <= CEIL /\ In (sc_map sl, sc_map sl + sc_mapsz sl) (dyn_ranges st)).
    { intros z Hz; destruct (IDXfacts z Hz) as (sl & _ & Hsl & Hz2); exists sl; destruct (sec_facts bt st Lc FF W sl Hsl) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8);
         (split; [exact Hsl|]); (split; [exact Hz2|]); (split; [clear -A5 A6 A7; unfold PG in *; lia|]); (split; [exact A1|]); (split; [exact A2|]); exact (sec_dyn st sl Hsl). }
    (* [comment removed for export] *)
    set (PIN := fun z : Z => (0 <= z < 0) \/ (0 <= z < 0) \/ (IB bt + 120 <= z < IB bt + 128) \/ (IB bt + 680 <= z < IB bt + 681)
                             \/ (bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8) \/ (idx_lo st <= z < idx_hi st)
                             \/ (sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s))).
    pose proof (PIN9dec st i s) as PINd. fold PIN in PINd.
    set (Mmid := fun a : word => if PINd (u a) then M a else M' a).
    assert (P : Rep bt st Lc FF Mmid mdl).
    { apply (Rep_frame_q bt st Lc FF M Mmid mdl W R); intros a NEa; unfold Mmid in NEa |- *;
         destruct (PINd (u a)) as [IN|NI]; [exfalso; exact (NEa eq_refl)|];
         destruct (AGR a NEa) as [Hf Hd]; (split; [| exact Hd]);
         intros HC; unfold foot_secfree_live in Hf; unfold PIN in NI;
         destruct Hf as [Hf|[Hf|[Hf|[Hf|[Hf|Hf]]]]]; [ | am_tauto | am_tauto | am_tauto | exact (stats_not_cells bt st Lc FF W (u a) Hf HC) | exact (ceil_not_cells bt st Lc FF W (u a) Hf HC)];
         apply (instjunk_not_cells bt st Lc FF W (u a)); [| exact HC]; (lazymatch goal with |- ?G => let G' := eval unfold instjunk in G in change_no_check G' end);
         destruct (Z_lt_dec (u a) (IB bt + 128)) as [L1|L1]; [exfalso; apply NI; right; right; left; lia|];
         destruct (Z.eq_dec (u a) (IB bt + 680)) as [L2|L2]; [exfalso; apply NI; right; right; right; left; lia | lia]. }
    (* [comment removed for export] *)
    assert (AG : forall z, ~ PIN z -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mmid in G in change_no_check G' end). rewrite (u64_lit z) by lia. destruct (PINd z) as [IN|NI]; [exfalso; exact (Hz IN) | reflexivity]. }
    assert (DEF : DEFK Mmid M').
    { intros a NEa. unfold Mmid in NEa. destruct (PINd (u a)) as [IN|NI]; [| exfalso; exact (NEa eq_refl)]. exact (proj2 (AGR a NEa)). }
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    assert (PTRZ : forall z, bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8 -> bt_ptrarr bt <= z < bt_ptrarr bt + 2 ^ 23) by (intros z Hz; clear -Hz PTRfacts; lia).
    (* [comment removed for export] *)
    assert (IMGR1 : forall z, ia_img_lo IA <= z < ia_img_hi IA -> ~ (IB bt + 120 <= z < IB bt + 128) -> z <> IB bt + 680 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N3 N4. apply AG; [| clear -Hz I1 I2; ulia]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - clear -X; lia.
      - clear -X; lia.
      - exact (N3 X).
      - apply N4. lia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz PD4. Zlia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). destruct (RNG _ _ (all_ranges_dyn bt st _ HD)) as ((_ & _ & _ & D4 & _) & _). clear -Hz Hz2 Hz3 D4. lia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz I2. ulia. }
    assert (IMGR : forall z, ia_img_lo IA <= z < ia_img_hi IA -> ~ qhdr bt z -> ~ (IB bt + 120 <= z < IB bt + 128) -> z <> IB bt + 680 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z))
      by (intros z Hz _ N3 N4; exact (IMGR1 z Hz N3 N4)).
    assert (TPR : forall z, T <= z < T + PG -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - clear -X; lia.
      - clear -X; lia.
      - clear -X Hz TPI INI. Zlia.
      - clear -X Hz TPI INI. Zlia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz D8T. Zlia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT HD) as D. hnf in D. cbn in D. clear -Hz Hz2 Hz3 D. lia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz TPB. Zlia. }
    assert (FIXR : forall lo hi, In (lo, hi) (bt_fixed bt) -> hi - lo < KSPACE -> hi - lo <> PG -> (hi <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= lo) ->
                   forall z, lo <= z < hi -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros lo hi Hin Hlen Hpg H8 z Hz Hr. apply AG; [| exact Hr].
      destruct (fixed_range bt st Lc FF W lo hi Hin) as ((D1 & D2 & D3 & D4 & D5) & _).
      pose proof (space_vs_fixed bt st Lc FF W lo hi Hin Hlen) as SP.
      (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - clear -X; lia.
      - clear -X; lia.
      - clear -X Hz D4 INI. lia.
      - clear -X Hz D4 INI. lia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz H8. lia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W Hin HD) as D. hnf in D. cbn in D. clear -Hz Hz2 Hz3 D. lia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz D5. ulia. }
    assert (PTRR : forall z, bt_ptrarr bt <= z < bt_ptrarr bt + 2 ^ 23 -> ~ (bt_ptrarr bt + 8 * Z.of_nat i <= z < bt_ptrarr bt + 8 * Z.of_nat i + 8) -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N5 Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - clear -X; lia.
      - clear -X; lia.
      - clear -X Hz PD4 INI. Zlia.
      - clear -X Hz PD4 INI. Zlia.
      - exact (N5 X).
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 HD) as D. hnf in D. cbn in D. clear -Hz Hz2 Hz3 D. lia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz PD5. Zlia. }
    assert (DYNR : forall lo hi, In (lo, hi) (dyn_ranges st) -> forall z, lo <= z < hi -> ~ (idx_lo st <= z < idx_hi st) -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros lo hi Hin z Hz N6 Hr. apply AG; [| exact Hr].
      destruct (RNG _ _ (all_ranges_dyn bt st _ Hin)) as ((D1 & D2 & D3 & D4 & D5) & _).
      pose proof (space_vs_dyn bt st Lc FF W lo hi Hin) as SP.
      (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end); intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - clear -X; lia.
      - clear -X; lia.
      - clear -X Hz D4 INI. lia.
      - clear -X Hz D4 INI. lia.
      - pose proof (PTRZ z X) as ZP. pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 Hin) as D. hnf in D. cbn in D. clear -ZP Hz D. lia.
      - exact (N6 X).
      - pose proof (RMSband z X) as ZS. clear -ZS Hz D5. ulia. }
    assert (SPCR : forall z, SBEG <= z < SBEG + KSPACE + PG -> ~ gq_objs st z -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N2 Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - clear -X; lia.
      - clear -X; lia.
      - clear -X Hz SBH INI I2. ulia.
      - clear -X Hz SBH INI I2. ulia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz SP8'. Zlia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). pose proof (space_vs_dyn bt st Lc FF W _ _ HD) as SP. clear -Hz Hz2 Hz3 SP. ulia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz SBH. ulia. }
    assert (SPCR0 : forall z, SBEG <= z < SBEG + KSPACE + PG -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - clear -X; lia.
      - clear -X; lia.
      - clear -X Hz SBH INI I2. ulia.
      - clear -X Hz SBH INI I2. ulia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz SP8'. Zlia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). pose proof (space_vs_dyn bt st Lc FF W _ _ HD) as SP. clear -Hz Hz2 Hz3 SP. ulia.
      - pose proof (RMSband z X) as ZS. clear -ZS Hz SBH. ulia. }
    assert (BANDR : forall z, SB <= z < AS_HEAPLO -> ~ (sh_lo (sc_map s) <= z < sh_hi (sc_map s) (sc_mapsz s)) -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N7 Hr. apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
      - clear -X; lia.
      - clear -X; lia.
      - clear -X Hz INI I2. ulia.
      - clear -X Hz INI I2. ulia.
      - pose proof (PTRZ z X) as ZP. clear -ZP Hz PD5. Zlia.
      - destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). destruct (RNG _ _ (all_ranges_dyn bt st _ HD)) as ((_ & _ & _ & _ & D5) & _). clear -Hz Hz2 Hz3 D5. ulia.
      - exact (N7 X). }
    (* [comment removed for export] *)
    assert (CHKR : forall c' a', 1 <= c' <= 30 -> carved bt st c' a' ->
               ~ (c' = BATCHCLASS /\ exists b, In b (a_gq st) /\ ba_addr b = a') ->
               forall z, a' <= z < a' + csize c' -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros c' a' Hc' CV' NB z Hz Hr. destruct (carved_range bt st Lc FF W c' a' Hc' CV') as (D1 & D2 & D3 & D4 & D5).
      apply SPCR; [clear -Hz D3 D4; ulia | | exact Hr].
      intros Gi. destruct (GQfacts z Gi) as (b & _ & Hb & CVb & Bl1 & Bl2 & Hi2).
      destruct (chunk_cases bt st Lc FF W c' a' BATCHCLASS (ba_addr b) Hc' HC24 CV' CVb) as [[EC EA] | D].
      + apply NB. split; [exact EC|]. exists b. split; [exact Hb | symmetry; exact EA].
      + change (csize BATCHCLASS) with 8192 in D. unfold BATCHSZ in *. clear -D Hz Hi2. lia. }
    destruct (WR1 BATCHCLASS HC24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PARTB & _). pose proof PARTB as (_ & _ & _ & _ & _ & _ & _ & NBL & _).
    assert (BR : forall b0, In b0 (a_tq st ++ a_gq st) -> 0 <= ba_addr b0 /\ ba_addr b0 + BATCHSZ < 2 ^ 64 /\ Z.of_nat (length (ba_items b0)) <= BATCHCAP).
    { intros b0 Hb0. destruct (batch_facts bt st Lc FF W b0 Hb0) as (_ & BL1 & BL2 & BL3). clear -BL1 BL2 BL3 X14 X15. ulia. }
    assert (BAT : forall b0 z, In b0 (a_tq st) -> ba_addr b0 <= z < ba_addr b0 + BATCHSZ -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros b0 z Hb0 Hz Hr. assert (Hb2 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; left; exact Hb0).
      destruct (batch_facts bt st Lc FF W b0 Hb2) as (CVb & _ & BL2 & BL3).
      apply (CHKR BATCHCLASS (ba_addr b0) HC24 CVb); [| change (csize BATCHCLASS) with 8192; unfold BATCHSZ in Hz; exact Hz | exact Hr].
      intros (_ & b & Hb & EA). destruct (in_split _ _ Hb0) as (t1 & t2 & ET). rewrite ET, !map_app in WQ5. cbn [map] in WQ5. rewrite <- app_assoc in WQ5. cbn [app] in WQ5.
      apply (NoDup_remove_2 _ _ _ WQ5). apply in_app_iff. right. apply in_app_iff. right. rewrite <- EA. apply in_map. exact Hb. }
    (* [comment removed for export] *)
    assert (HDRR : forall p' n' z, In (p', n') Lc \/ In (p' - 16, n') (quar st) -> foot_hdr p' n' z -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros p' n' z Hown Hf Hr. pose proof (rz_range n') as RZ'.
      destruct (hdr_zone bt st Lc FF W p' n' z Hown Hf) as [(HP' & W1 & W2 & W3 & CV' & HC' & N1' & W4) | (HP' & sc' & Hs' & Eu' & En' & W1 & N1')].
      - apply (CHKR (blk_class n') (prim_alloc_beg p' n') HC' CV'); [| clear -W1 W2 W3 W4 N1' RZ'; unfold prim_alloc_beg in *; lia | exact Hr].
        intros (EC & b & Hb & EA). apply (NBL (ba_addr b) ltac:(exists b; split; [apply in_app_iff; right; exact Hb | reflexivity]) eq_refl). rewrite EA, <- EC.
        destruct Hown as [Hown1|Hown1].
        * left. pose proof (live_chunk bt st Lc FF W p' n' Hown1 HP') as Gv. cbn zeta in Gv. destruct Gv as (_ & _ & G3 & _). exact G3.
        * right; left. pose proof (quar_chunk bt st Lc FF W (p' - 16) n' Hown1 HP') as Gv. cbn zeta in Gv. replace (p' - 16 + 16) with p' in Gv by lia.
          destruct Gv as (_ & _ & G3 & _). exact G3.
      - destruct (sec_facts bt st Lc FF W sc' Hs') as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
        apply (DYNR _ _ (sec_dyn st sc' Hs')); [rewrite Eu', En' in *; clear -W1 A5 A6 N1'; ulia | | exact Hr].
        intros X. destruct (IDXfacts z X) as (sl & _ & Hsl & Hz2).
        destruct (sec_cases bt st Lc FF W sc' sl Hs' Hsl) as [<- | D]; [rewrite Eu', En' in *; clear -W1 A5 Hz2; unfold PG in *; lia|].
        destruct (sec_facts bt st Lc FF W sl Hsl) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). rewrite Eu', En' in *. clear -W1 A5 A6 N1' Hz2 D C5 C6 C7. unfold PG in *. lia. }
    assert (CHvsFAd : forall c' a' c0, 1 <= c' <= 30 -> carved bt st c' a' -> 1 <= c0 <= 30 -> a' + csize c' <= fa_beg SBEG c0 \/ fa_beg SBEG c0 + 2 ^ 29 <= a').
    { intros c' a' c0 Hc' CVa Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (E1' & E2' & E3' & E4' & E5' & _).
      destruct (carved_range bt st Lc FF W c' a' Hc' CVa) as (D1 & D2 & _).
      pose proof (region_facts bt st Lc FF W c' Hc') as RF. cbn zeta in RF. destruct RF as (F1 & F2 & F3 & F4 & F5 & _).
      unfold region_beg, fa_beg, region_beg, KFAOFF, KREGION in *.
      destruct (Z.lt_trichotomy c0 c') as [LT|[->|GT]]; [| left; clear -D1 D2 F2 F3; lia |].
      * right. assert (c0 * 2 ^ 32 + 2 ^ 32 <= c' * 2 ^ 32) by (replace (c0 * 2 ^ 32 + 2 ^ 32) with ((c0 + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia). clear -H D1 D2 F2 F3. lia.
      * left. assert (c' * 2 ^ 32 + 2 ^ 32 <= c0 * 2 ^ 32) by (replace (c' * 2 ^ 32 + 2 ^ 32) with ((c' + 1) * 2 ^ 32) by lia; apply Z.mul_le_mono_nonneg_r; lia).
        destruct (WR1 c' Hc') as (R1' & _ & R3' & _). unfold KREGION_EXHAUST, KUSERMAP in R3'. clear -H D1 D2 F2 F3 R1' R3'. lia. }
    clear WR2 WC WQ1 WQ2 WQ3 WQ4 S2 LV1 LV3 WK WD WM' PW' R6a R6b IN6 G PARTB.
    pose proof P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19).
    try ceil; unfold AS_HEAPLO, AS_LO, PG, FAKE_SIZE, KSPACE in X1, X2, X3, X4, X5, X6, X8, X9, X10, X11, X12, X13, X14, X15, Z2, Z4, Z6, Z8, Z10, Z12, Z14, Z16.
    (lazymatch goal with |- ?G => let G' := eval unfold Rep in G in change_no_check G' end).
    (* [comment removed for export] *)
    split. { eapply cells_hold_frame; [exact P1 | exact YC |]. intros c0 z Hc0 Hz. rewrite Forall_forall in DC.
             destruct (img_kinds bt st Lc FF W z ltac:(left; exists c0; split; [exact Hc0 | exact Hz])) as [LT _].
             assert (ND : ~ img_dyn IA z) by exact (DC c0 Hc0 z Hz). unfold img_dyn in ND. unfold qhdr, IB in *.
             apply (IMGR z LT); [intros X; apply ND; right; right; left; lia | intros X; apply ND; left; lia | intros X; apply ND; left; lia]. }
    (* [comment removed for export] *)
    split. { destruct P2 as (I1' & I2' & I3 & I4 & I5 & I6 & IL & IP & IW). (lazymatch goal with |- ?G => let G' := eval unfold rep_instance in G in change_no_check G' end).
             change (a_nres st') with (a_nres st). change (a_sec st') with SR. change (a_gq st') with (a_gq st).
             assert (AGI : forall z, ((IB bt + 112 <= z < IB bt + 120) \/ (IB bt + 880 <= z < IB bt + 888) \/ (IB bt + 920 <= z < IB bt + 985)) -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
             { intros z Hz Hr. apply IMGR; [clear -Hz INI; lia | (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); clear -Hz; lia | clear -Hz; lia | clear -Hz; lia]. }
             split; [frZ AGI I1'|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold SR in G in change_no_check G' end); rewrite (swap_remove_length (a_sec st) i s Hnth); exact CNCH|]. split; [exact CMTX|]. split; [frB AGI I4|]. split; [frB AGI I5|]. split; [frB AGI I6|].
             split. { eapply rep_list_frame; [exact IL | clear -INI I1; lia | clear -INI I2; ulia |]. intros z Hz Hr.
                      apply IMGR1; [clear -Hz INI; lia | clear -Hz; lia | clear -Hz; lia]. }
             split. { intros j sj Hsj. destruct (nth_error_swap_remove (a_sec st) i j s sj Hnth Hsj) as (JL & [[-> HL] | [NEj Hj]]).
                      - exact (proj1 (CMOVE sj ltac:((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); lia) HL)).
                      - pose proof (IP j sj Hj) as C. eapply (cellZ_frame _ _ _ _ _ _ C); [clear -PD1; lia | clear -JL PTRfacts PD1 PD2 PD3; unfold len in *; ulia |]. intros z Hz. cbn in Hz.
                        apply PTRR; [clear -Hz JL PTRfacts; unfold len in *; lia | clear -Hz NEj; lia | clear -Hz JL PTRfacts PD1 PD2 PD3; unfold len in *; ulia]. }
             frW DEF IW. }
    (* [comment removed for export] *)
    split. { destruct P3 as (T1 & T2 & T3 & T4 & T5 & T6 & TL & TP & TW & TC1 & TC2 & TC3 & TC4). (lazymatch goal with |- ?G => let G' := eval unfold rep_thread in G in change_no_check G' end).
             change (a_tq st') with (a_tq st). change (a_cinit st') with (a_cinit st). change (a_cache st') with (a_cache st).
             assert (AGT : forall z, T <= z < T + PG -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)) by exact TPR.
             assert (AGC : forall z, bt_tctx bt <= z < bt_tctx bt + 160 -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
             { intros z Hz Hr. apply (FIXR _ _ INC); [ulia | ulia | | clear -Hz; lia | exact Hr].
               pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INC) (all_ranges_fixed bt st _ IN8) ltac:(intros E; injection E; intros; lia)) as D. hnf in D. cbn in D. exact D. }
             unfold T_QC, T_PC, PC_SZ, T_UNW, PG in *.
             split; [frZ AGT T1|]. split; [frZ AGT T2|]. split; [frZ AGT T3|]. split; [frB AGT T4|]. split; [frZ AGT T5|]. split; [frB AGT T6|].
             split. { eapply rep_list_frame; [exact TL | lia | lia |]. intros z Hz Hr. apply AGT; [clear -Hz; lia | exact Hr]. }
             split. { intros c' Hc'. pose proof (cache_len bt st Lc FF W c' Hc') as CL'.
                      eapply rep_pclass_frame; [exact (TP c' Hc') | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); ulia | exact CL' |].
                      unfold T_PC, PC_SZ in *. intros z Hz Hr. apply AGT; [clear -Hz Hc'; lia | exact Hr]. }
             split; [frW DEF TW|]. split; [frZ AGC TC1|]. split; [frZ AGC TC2|]. split; [frZ AGT TC3 | frZ AGT TC4]. }
    (* [comment removed for export] *)
    split. { intros c0 Hc0. destruct (P4 c0 Hc0) as [G0 F0]. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF.
             destruct RF as (E1' & E2' & E3' & E4' & E5' & E6' & E7' & E8' & E9' & E10' & _).
             change (a_reg st' c0) with (a_reg st c0).
             eapply rep_region_frame; [exact DEF | exact G0 | exact F0 | ulia | ulia | ulia | ulia | ulia |].
             intros z Hz Hr. unfold foot_region in Hz. destruct Hz as [[Hz _] | Hz].
             - apply SPCR; [clear -Hz E9' E10'; ulia | intros Zi; pose proof (GQspace z Zi) as ZS; clear -ZS Hz E9'; ulia | exact Hr].
             - apply SPCR; [clear -Hz E1' E2' E5' E6' E7' E8'; ulia | | exact Hr].
               intros Zi. destruct (GQfacts z Zi) as (bl & _ & _ & CVl & Bl1 & Bl2 & Hi2).
               destruct (CHvsFAd BATCHCLASS (ba_addr bl) c0 HC24 CVl Hc0) as [D | D]; change (csize BATCHCLASS) with 8192 in D; unfold BATCHSZ in Hi2; clear -D Hz Hi2 E6' E7'; lia. }
    (* [comment removed for export] *)
    split. { change (a_tq st') with (a_tq st). eapply rep_batches_frame; [exact DEF | exact P5 | intros b0 Hb0; exact (BR b0 ltac:(apply in_app_iff; left; exact Hb0)) |].
             intros b0 z Hb0 Hz Hr. unfold foot_batch in Hz. apply (BAT b0 z Hb0); [| exact Hr].
             destruct (BR b0 ltac:(apply in_app_iff; left; exact Hb0)) as (_ & _ & Q3). clear -Hz Q3. ulia. }
    (* [comment removed for export] *)
    split. { change (a_gq st') with (a_gq st). eapply rep_batches_frame; [exact DEF | exact P6 | intros b0 Hb0; exact (BR b0 ltac:(apply in_app_iff; right; exact Hb0)) |].
             intros b0 z Hb0 Hz Hr. unfold foot_batch in Hz.
             assert (Hb2 : In b0 (a_tq st ++ a_gq st)) by (apply in_app_iff; right; exact Hb0).
             destruct (batch_facts bt st Lc FF W b0 Hb2) as (_ & _ & BL2 & BL3). destruct (BR b0 Hb2) as (_ & _ & Q3).
             apply SPCR0; [clear -Hz Q3 BL2 BL3; ulia | exact Hr]. }
    (* [comment removed for export] *)
    split. { change (rep_secondary bt st' M') with (forall j sj, nth_error SR j = Some sj ->
                 cellZ SG M' (sc_map sj) 8 (sc_map sj) /\ cellZ SG M' (sc_map sj + 8) 8 (sc_mapsz sj) /\ cellZ SG M' (sc_map sj + 16) 8 (sec_needed (sc_n sj))
                 /\ cellZ SG M' (sc_map sj + 24) 8 (Z.of_nat j) /\ writableZ SG M' (sc_map sj) (sc_map sj + sc_mapsz sj)).
             intros j sj Hsj. destruct (nth_error_swap_remove (a_sec st) i j s sj Hnth Hsj) as (JL & CASE).
             assert (Hoj : exists oj, nth_error (a_sec st) oj = Some sj) by (destruct CASE as [[_ HL] | [_ Hj]]; [exists (length (a_sec st) - 1)%nat; exact HL | exists j; exact Hj]).
             destruct Hoj as (oj & Hoj). pose proof (nth_error_In _ _ Hoj) as Hinj.
             destruct (P7 oj sj Hoj) as (C1 & C2 & C3 & C4 & CW). destruct (sec_facts bt st Lc FF W sj Hinj) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
             assert (RJ : 0 <= sc_map sj /\ sc_map sj + 32 < 2 ^ 64 /\ sc_map sj + 32 <= sc_map sj + sc_mapsz sj) by (clear -A1 A2 A5 A6 A7; ulia).
             assert (AGs : forall z, sc_map sj <= z < sc_map sj + 24 -> 0 <= z < 2 ^ 64 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
             { intros z Hz Hr. apply (DYNR _ _ (sec_dyn st sj Hinj)); [clear -Hz RJ; lia | | exact Hr].
               intros X. destruct (IDXfacts z X) as (sl & _ & Hsl & Hz2).
               destruct (sec_cases bt st Lc FF W sj sl Hinj Hsl) as [<- | D]; [clear -Hz Hz2; lia|].
               destruct (sec_facts bt st Lc FF W sl Hsl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). clear -Hz Hz2 D RJ Q5 Q6 Q7. unfold PG in *. lia. }
             split; [eapply (cellZ_frame _ _ _ _ _ _ C1); [clear -RJ; lia | clear -RJ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply AGs; clear -Hz RJ; lia]|].
             split; [eapply (cellZ_frame _ _ _ _ _ _ C2); [clear -RJ; lia | clear -RJ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply AGs; clear -Hz RJ; lia]|].
             split; [eapply (cellZ_frame _ _ _ _ _ _ C3); [clear -RJ; lia | clear -RJ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; apply AGs; clear -Hz RJ; lia]|].
             split; [| frW DEF CW].
             destruct CASE as [[-> HL] | [NEj Hj]].
             - exact (proj2 (CMOVE sj ltac:((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); lia) HL)).
             - assert (oj = j) by (apply (proj1 (NoDup_nth_error (a_sec st)) NDS0 oj j (nth_error_lt _ _ _ Hoj)); rewrite Hoj, Hj; reflexivity). subst oj.
               eapply (cellZ_frame _ _ _ _ _ _ C4); [clear -RJ; lia | clear -RJ; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. intros z Hz. cbn in Hz.
               apply (DYNR _ _ (sec_dyn st sj Hinj)); [clear -Hz RJ; lia | | clear -Hz RJ; lia].
               intros X. destruct (IDXfacts z X) as (sl & HLs & Hsl & Hz2).
               destruct (sec_cases bt st Lc FF W sj sl Hinj Hsl) as [<- | D].
               + assert (j = (length (a_sec st) - 1)%nat) by (apply (proj1 (NoDup_nth_error (a_sec st)) NDS0 j _ (nth_error_lt _ _ _ Hj)); rewrite Hj, HLs; reflexivity). lia.
               + destruct (sec_facts bt st Lc FF W sl Hsl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8). clear -Hz Hz2 D RJ Q5 Q6 Q7. unfold PG in *. lia. }
    (* [comment removed for export] *)
    split. { destruct P8 as [HLh HQh]. split.
             - intros p' n' Hin0. pose proof (proj1 (proj1 (INL _) Hin0)) as Hin'. destruct (live_range bt st Lc FF W p' n' Hin') as (A1 & A2 & A3 & A4). pose proof (rz_range n') as RZ'.
               eapply rep_hdr_frame; [exact DEF | exact (HLh p' n' Hin') | clear -A1 A3 RZ'; ulia | clear -A2 A3; ulia |]. intros z Hz Hr. exact (HDRR p' n' z (or_introl Hin') Hz Hr).
             - intros m0 n' Hq'. change (quar st') with (quar st) in Hq'. pose proof Hq' as Hq0. destruct (HQh m0 n' Hq0) as [Hh HW]. split; [| frW DEF HW].
               destruct (quar_item_range bt st Lc FF W m0 n' Hq0) as (QB1 & QB2 & QB3). pose proof (rz_range n') as RZn.
               eapply rep_hdr_frame; [exact DEF | exact Hh | clear -QB1 QB2 QB3 RZn; ulia | clear -QB1 QB2 QB3 RZn; ulia |]. intros z Hz Hr.
               apply (HDRR (m0 + 16) n' z); [right; replace (m0 + 16 - 16) with m0 by lia; exact Hq0 | exact Hz | exact Hr]. }
    (* [comment removed for export] *)
    assert (IMGR0 : forall z, ia_img_lo IA <= z < ia_img_hi IA -> ~ (IB bt + 112 <= z < IB bt + 985) -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz N0. apply IMGR; [exact Hz | (lazymatch goal with |- ?G => let G' := eval unfold qhdr in G in change_no_check G' end); clear -N0; lia | clear -N0; lia | clear -N0; lia]. }
    split. { change (rep_depot bt st' M') with (rep_depot bt st M'). eapply rep_depot_frame; [exact DEF | exact P9 | uilia | uilia | uilia | uilia | | |].
             - intros id Hid. destruct (node_addr_range bt st Lc FF W id Hid) as (_ & A1 & A2 & _). clear -A1 A2. ulia.
             - intros z Hz Hr. destruct (img_kinds bt st Lc FF W z ltac:(right; right; left; exact Hz)) as [LT _]. apply (IMGR0 z LT).
               unfold foot_depot_static in Hz. unfold DEPOT_NIDS, DEPOT_MAP1 in Hz. unfold IB, DEPOT_TAB, SSOBJ in *. clear -Hz J1 J2. Zlia.
             - intros id z Hid Hz Hr. unfold foot_node in Hz. destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & A1 & A2 & A3).
               pose proof (node_addr_block bt st id Hid) as Hbk. set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
               destruct HIn as [Eb | Hnb].
               + apply (FIXR _ _ INN); [clear; ulia | clear; ulia | | clear -Hz Hbk Eb; rewrite Eb; lia | exact Hr].
                 pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INN) (all_ranges_fixed bt st _ IN8) ltac:(intros E; injection E; intros; lia)) as D. hnf in D. cbn in D. exact D.
               + apply (DYNR _ _ (node_dyn st bb Hnb)); [clear -Hz Hbk; lia | | exact Hr].
                 intros X. destruct (IDXfacts z X) as (sl & _ & Hsl & Hz2). destruct (sec_facts bt st Lc FF W sl Hsl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
                 destruct (sec_vs_node bt st Lc FF W sl bb Hsl Hnb) as [HSN|HSN]; clear -HSN Hz Hbk Hz2 Q5 Q6 Q7; unfold PG in *; lia. }
    (* [comment removed for export] *)
    split. { change (rep_fake bt st' FF M') with (rep_fake bt st FF M'). pose proof (dtls_facts bt st Lc FF W) as [DT1 DT2]. eapply rep_fake_frame; [exact DEF | exact P10 | ulia | ulia | uilia | uilia | clear -DT1; ulia | clear -DT2; ulia | | |].
             - intros f k0 Hf. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _). clear -A1 A2 A4 X5 X6. ulia.
             - intros z Hz Hr. unfold foot_fake_static in Hz.
               assert (FS8 : bt_fs bt + FAKE_SIZE <= bt_ptrarr bt \/ bt_ptrarr bt + 2 ^ 23 <= bt_fs bt).
               { pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INFS) (all_ranges_fixed bt st _ IN8) ltac:(intros E; injection E; intros; ulia)) as D. hnf in D. cbn in D. exact D. }
               destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
               1-3: apply (FIXR _ _ INFS); [clear; ulia | clear; ulia | exact FS8 | clear -Hz; ulia | exact Hr].
               + destruct (img_kinds bt st Lc FF W z ltac:(do 3 right; left; exact Hz)) as [LT _]. apply (IMGR0 z LT). unfold IB in *. clear -Hz J5. Zlia.
               + destruct (dtls_cell_facts bt st Lc FF W z Hz) as (DF1 & DF2 & DF3 & DF4 & DF5 & DF6 & DF7).
                 pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & IN6' & R6a' & R6b' & _) & _).
                 apply AG; [| exact Hr]. (lazymatch goal with |- ?G => let G' := eval unfold PIN in G in change_no_check G' end). intros [X|[X|[X|[X|[X|[X|X]]]]]].
                 * clear -X; lia.
                 * clear -X; lia.
                 * apply DF3. clear -X INI. lia.
                 * apply DF3. clear -X INI. lia.
                 * pose proof (PTRZ z X) as ZP. apply (DF6 _ _ IN8); [clear; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); lia | exact ZP].
                 * destruct (IDXdyn z X) as (sl & _ & Hz2 & Hz3 & _ & _ & HD). apply (DF7 _ _ HD). clear -Hz2 Hz3. lia.
                 * pose proof (RMSband z X) as ZS. apply DF4. clear -ZS. ulia.
             - intros f k0 z Hf Hz Hr. unfold foot_fword in Hz. destruct (fake_frame_facts bt st Lc FF W f k0 Hf) as (A1 & A2 & A3 & A4 & _).
               apply (FIXR _ _ INFS); [clear; ulia | clear; ulia | | clear -Hz A1 A2 A4; ulia | exact Hr].
               pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INFS) (all_ranges_fixed bt st _ IN8) ltac:(intros E; injection E; intros; ulia)) as D. hnf in D. cbn in D. exact D. }
    (* [comment removed for export] *)
    split. { change (rep_ialloc bt st' M') with (rep_ialloc bt st M'). eapply rep_ialloc_frame; [exact P11 | uilia | uilia | uilia | uilia |].
             intros z Hz Hr. destruct (img_kinds bt st Lc FF W z ltac:(do 4 right; left; exact Hz)) as [LT _]. apply (IMGR0 z LT).
             unfold ialloc_cells in Hz. unfold IB, IA_FLAG, IA_INST, IASZ in *. clear -Hz J3 J4. Zlia. }
    (* [comment removed for export] *)
    split. { destruct P12 as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). (lazymatch goal with |- ?G => let G' := eval unfold rep_shadow in G in change_no_check G' end).
             change (a_reg st') with (a_reg st). change (a_sec st') with SR.
             assert (SHR : forall lo1 hi1 g, lo1 / 8 <= g < hi1 / 8 -> 0 <= lo1 -> hi1 <= CEIL + 8 -> SB <= SB + g < AS_HEAPLO /\ 0 <= SB + g /\ SB + g + 1 < 2 ^ 64).
             { intros lo1 hi1 g Hg Hg0 Hg1. clear -Hg Hg0 Hg1 B6 B7. Zlia. }
             assert (SHSEP : forall X Y g, X / 8 <= g < Y / 8 -> (sc_map s + sc_mapsz s <= X \/ Y <= sc_map s) -> ~ (sh_lo (sc_map s) <= SB + g < sh_hi (sc_map s) (sc_mapsz s))).
             { intros X Y g Hg SEP Hr. unfold sh_lo, sh_hi in Hr. clear -Hg SEP Hr SA3 SA4. unfold PG in *. Z.div_mod_to_equations. lia. }
             assert (RMREG : forall c0, 1 <= c0 <= 30 -> sc_map s + sc_mapsz s <= region_beg SBEG c0 \/ fa_beg SBEG c0 + 2 ^ 29 <= sc_map s).
             { intros c0 Hc0. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
               destruct (space_vs_dyn bt st Lc FF W _ _ (sec_dyn st s Hs)) as [SP | SP]; [left; clear -SP D1; lia | right; clear -SP D5; unfold KSPACE, PG in *; lia]. }
             split. { intros c0 g Hc0 Hg NL'. pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 X14; ulia) ltac:(clear -D2 D3 D4 D5 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      change (quar st') with (quar st).
                      assert (NL0 : ~ live_granule Lc g).
                      { intros (p' & n' & Hi' & UG). assert (DEC : {(p', n') = (p, n)} + {(p', n') <> (p, n)}) by (decide equality; apply Z.eq_dec). destruct DEC as [E | NE]; [| apply NL'; exists p', n'; split; [apply INL; split; assumption | exact UG]].
                        injection E as -> ->. unfold user_granule in UG. destruct (RMREG c0 Hc0) as [SEP | SEP]; rewrite <- Hus in UG; rewrite <- Hsn in UG; clear -UG Hg SEP SA5 SA6 D2 D3 D5 SA3 SA4; unfold PG in *; Z.div_mod_to_equations; lia. }
                      pose proof (SH1 c0 g Hc0 Hg NL0) as BY. eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      apply (SHSEP _ _ g Hg). destruct (RMREG c0 Hc0) as [SEP | SEP]; [left; exact SEP | right; clear -SEP D2 D3 D5; lia]. }
             split. { intros c0 g Hc0 Hg. pose proof (SH2 c0 g Hc0 Hg) as BY.
                      pose proof (region_facts bt st Lc FF W c0 Hc0) as RF. cbn zeta in RF. destruct RF as (D1 & D2 & D3 & D4 & D5 & D6 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -D1 D2 D3 D4 X14; ulia) ltac:(clear -D5 D6 X15; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      apply (SHSEP _ _ g Hg). destruct (RMREG c0 Hc0) as [SEP | SEP]; [left; clear -SEP D1 D2 D3 D4; lia | right; clear -SEP D6; lia]. }
             split. { intros sc g Hsc Hg NUG. apply INSR in Hsc. destruct Hsc as [Hsc NEs]. pose proof (SH3 sc g Hsc Hg NUG) as BY. destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & _).
                      destruct (SHR _ _ g Hg ltac:(clear -A1; ulia) ltac:(clear -A2; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      apply (SHSEP _ _ g Hg). destruct (sec_cases bt st Lc FF W s sc Hs Hsc) as [E | D]; [exfalso; exact (NEs (eq_sym E)) | exact D]. }
             split. { intros sc g Hsc HQ' HU. apply INSR in Hsc. destruct Hsc as [Hsc NEs]. change (quar st') with (quar st) in HQ'. pose proof HQ' as HQ.
                      pose proof (SH4 sc g Hsc HQ HU) as BY. destruct (sec_facts bt st Lc FF W sc Hsc) as (A1 & A2 & A3 & A4 & A5 & A6 & _).
                      unfold user_granule in HU.
                      destruct (SHR (sc_user sc) (sc_user sc + sc_n sc + 7) g ltac:(clear -HU; lia) ltac:(clear -A1 A5; ulia) ltac:(clear -A2 A6; ulia)) as (QQ1 & QQ2 & QQ3).
                      eapply (byteZ_frame _ _ _ _ _ BY); [exact QQ2 | exact QQ3 | apply BANDR; [exact QQ1 | | lia]].
                      intros Hr. unfold sh_lo, sh_hi in Hr.
                      destruct (sec_cases bt st Lc FF W s sc Hs Hsc) as [E | D]; [exact (NEs (eq_sym E))|].
                      clear -HU Hr D A3 A4 A5 A6 SA3 SA4. unfold PG in *. Z.div_mod_to_equations. lia. }
             split. { intros c0 g Hc0 Hg. exact (def_keep Mmid M' _ DEF (SH5 c0 g Hc0 Hg)). }
             intros sc g Hsc Hg. apply INSR in Hsc. exact (def_keep Mmid M' _ DEF (SH6 sc g (proj1 Hsc) Hg)). }
    (* [comment removed for export] *)
    split. { destruct P13 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12). (lazymatch goal with |- ?G => let G' := eval unfold rep_ledger in G in change_no_check G' end).
             change (a_dep st') with (a_dep st).
             assert (HOL : forall a, holes bt st' a <-> holes bt st a) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold holes in G in change_no_check G' end); change (a_reg st') with (a_reg st); am_tauto).
             assert (COM : forall a, committed bt st' a <-> committed bt st a) by (intros a; (lazymatch goal with |- ?G => let G' := eval unfold committed in G in change_no_check G' end); change (a_reg st') with (a_reg st); change (a_nres st') with (a_nres st); am_tauto).
             split. { destruct L1 as (F6l & PF & FOK & FPW & FH). exists F6l.
                      split. { apply (Permutation_cons_inv (a := (Z_to_bv 64 (sc_map s), Z_to_bv 64 (sc_mapsz s)))).
                               eapply Permutation_trans; [exact PM|]. eapply Permutation_trans; [exact PF|].
                               (lazymatch goal with |- ?G => let G' := eval unfold dyn_maps in G in change_no_check G' end). change (a_sec st') with SR. change (a_dep st') with (a_dep st).
                               set (f := fun s0 : schunk => (Z_to_bv 64 (sc_map s0), Z_to_bv 64 (sc_mapsz s0))).
                               set (DD := map (fun b : Z => (Z_to_bv 64 b, Z_to_bv 64 (2 ^ 20))) (dp_nodeblocks (a_dep st)) ++ map (fun b : Z => (Z_to_bv 64 b, Z_to_bv 64 (2 ^ 23))) (dp_storeblocks (a_dep st))).
                               apply Permutation_sym. transitivity (F6l ++ bt_maps0 bt ++ f s :: map f SR ++ DD).
                               { rewrite !(app_assoc F6l (bt_maps0 bt)). apply Permutation_middle. }
                               apply Permutation_app_head. apply Permutation_app_head. change (f s :: map f SR ++ DD) with (map f (s :: SR) ++ DD).
                               apply Permutation_app_tail. exact (Permutation_map f PERM). }
                      split; [exact FOK|]. split; [exact FPW|]. intros a Ha. rewrite (HOL a). exact (FH a Ha). }
             split; [intros a; rewrite (NA a), (L2 a), (HOL a), (COM a); am_tauto|].
             split; [intros a; rewrite (LZ a), (L3 a), (HOL a), (COM a); am_tauto|].
             split; [exact FL'|]. unfold alloc_top in L10 |- *. rewrite E1, E2, E3, E4, E6, E5. repeat (split; [assumption|]). exact NP'. }
    (* [comment removed for export] *)
    split. { apply (rep_budget_sec_free bt st st' Lc Lc' FF mdl mdl' s qt qg W P14 Hs).
             - (* [comment removed for export] *)
               intros p0 n0 Hin0. pose proof (proj1 (INL _) Hin0) as [Hin' NE]. split; [exact Hin'|]. rewrite Hus, Hsn. exact NE.
             - reflexivity.
             - reflexivity.
             - reflexivity.
             - (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa op_sec_free] in G in change_no_check G' end). rewrite ESEN. reflexivity.
             - reflexivity.
             - change (a_sec st') with SR. exact (Permutation_sym PERM).
             - (lazymatch goal with |- ?G => let G' := eval unfold st' in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa op_sec_free] in G in change_no_check G' end). rewrite ESEN. exact MI.
             - exact EAG. }
    (* [comment removed for export] *)
    split. { intros p' n' Hin0. pose proof (proj1 (proj1 (INL _) Hin0)) as Hin'. destruct (P15 p' n' Hin') as [W1 W2]. split; [frW DEF W1 | frW DEF W2]. }
    split. { intros f k0 Hf. frW DEF (P16 f k0 Hf). }
    assert (RTC : forall z, ia_rtc_sb IA <= z < ia_rtc_sb IA + 8 \/ ia_rtc_uar IA <= z < ia_rtc_uar IA + 4 -> M' (Z_to_bv 64 z) = Mmid (Z_to_bv 64 z)).
    { intros z Hz. destruct (img_kinds bt st Lc FF W z ltac:(do 5 right; (lazymatch goal with |- ?G => let G' := eval unfold rtc_cells in G in change_no_check G' end); exact Hz)) as [LT _]. apply (IMGR0 z LT).
      unfold IB in *. clear -Hz J6 J7. Zlia. }
    split; [eapply (cellZ_frame _ _ _ _ _ _ P17); [ulia | ulia | intros z Hz; apply RTC; left; cbn in Hz; lia] |].
    split; [eapply (cellZ_frame _ _ _ _ _ _ P18); [ulia | ulia | intros z Hz; apply RTC; right; cbn in Hz; lia] |].
    exact (rep_last_keep bt _ _ Mmid M' DEF P19 (fun H => H)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma secfree_live_map_apart : forall st Lc FF (qt qg : Z) i s, WFq bt st Lc FF qt qg -> nth_error (a_sec st) i = Some s ->
    dyn_ok IA (sc_map s) (sc_map s + sc_mapsz s)
    /\ forall lo' hi', In (lo', hi') (all_ranges bt (op_sec_free st i)) -> sc_map s + sc_mapsz s <= lo' \/ hi' <= sc_map s.
  Proof using.
    intros st Lc FF qt qg i s W Hnth.
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (M1 & M2 & _) & _).
    assert (Hs : In s (a_sec st)) by exact (nth_error_In _ _ Hnth).
    split; [exact (proj1 (M1 _ _ (all_ranges_dyn bt st _ (sec_dyn st s Hs))))|].
    set (SR := swap_remove (a_sec st) i). pose proof (swap_remove_perm (a_sec st) i s Hnth) as PERM. fold SR in PERM.
    set (st' := op_sec_free st i).
    assert (PMR : Permutation ((sc_map s, sc_map s + sc_mapsz s) :: all_ranges bt st') (all_ranges bt st)).
    { (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). change (a_sec st') with SR. change (a_dep st') with (a_dep st).
      set (f := fun s0 : schunk => (sc_map s0, sc_map s0 + sc_mapsz s0)).
      set (DD := map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st))).
      transitivity (bt_fixed bt ++ f s :: map f SR ++ DD); [apply Permutation_middle|].
      apply Permutation_app_head. change (f s :: map f SR ++ DD) with (map f (s :: SR) ++ DD).
      apply Permutation_app_tail. exact (Permutation_map f PERM). }
    assert (PWA : PW (all_ranges bt st)).
    { apply PW_of_splits. intros l1 [xlo xhi] l2 [ylo yhi] E Hy. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). exact (M2 l1 l2 xlo xhi ylo yhi E Hy). }
    pose proof (PW_perm _ _ (Permutation_sym PMR) PWA) as [SEPS _].
    intros lo' hi' Hin. pose proof (seps_In _ _ _ SEPS Hin) as D. cbn in D. exact D.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition XL (s : schunk) (z : Z) : Prop :=
    (sc_map s <= z < sc_map s + sc_mapsz s) \/ (T + 2768 <= z < T + 3168) \/ CEIL <= z.

  Definition OPS_REPX_sec_free_live : Prop := forall (X : Z -> Prop) st L1 L2 FF (M M' : mem) mdl mdl' p n i s (qt qg : Z),
    WFq bt st (L1 ++ (p, n) :: L2) FF qt qg -> RepX bt X st (L1 ++ (p, n) :: L2) FF M mdl ->
    (forall z, X z -> XL s z) ->
    is_primary n = false -> nth_error (a_sec st) i = Some s -> sc_user s = p ->
    (forall a : word, M' a <> M a -> foot_recycle_sec bt st i s (u a) /\ (M' a <> None \/ sc_map s <= u a < sc_map s + sc_mapsz s)) ->
    let len := Z.of_nat (length (a_sec st)) in
    cellZ SG M' (IB bt + 120) 8 (len - 1) -> byteZ SG M' (IB bt + 680) 0 ->
    (forall sl, Z.of_nat i < len - 1 -> nth_error (a_sec st) (length (a_sec st) - 1) = Some sl ->
        cellZ SG M' (bt_ptrarr bt + 8 * Z.of_nat i) 8 (sc_map sl) /\ cellZ SG M' (sc_map sl + 24) 8 (Z.of_nat i)) ->
    Permutation ((Z_to_bv 64 (sc_map s), Z_to_bv 64 (sc_mapsz s)) :: vm_maps (m_vmmaps mdl')) (vm_maps (m_vmmaps mdl)) ->
    (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a) ->
    Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl')) ->
    (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a) ->
    Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0
                                   /\ 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
           (m_vm_lazy mdl') ->
    vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl) ->
    vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl) ->
    vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) ->
    vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    (* [comment removed for export] *)
    MInv (release_aa (a_aa st) (sc_map s) (sc_n s)) mdl' -> eager_used mdl' + sc_mapsz s <= eager_used mdl ->
    Rep bt (op_sec_free st i) (L1 ++ L2) FF M' mdl'.

  Theorem OPS_REPX_sec_free_live_pf : OPS_REPX_sec_free_live.
  Proof using.
    intros X st La Lb FF M M' mdl mdl' p n i s qt qg W (M0 & R & D) XSUB HPn Hnth Hus STEP. cbn zeta.
    intros CNCH CMTX CMOVE PM NA NP' LZ FL' E1 E2 E3 E4 E6 E5 MI EAG.
    set (Lc := La ++ (p, n) :: Lb) in *. set (len := Z.of_nat (length (a_sec st))) in *.
    pose proof W as (_ & _ & _ & (S1 & S2 & S3 & S4 & S5 & _) & _ & _ & _ & _ & (RNG & _ & _ & _ & _ & IN8 & _) & _).
    assert (Hs : In s (a_sec st)) by exact (nth_error_In _ _ Hnth).
    destruct (sec_facts bt st Lc FF W s Hs) as (SA1 & SA2 & SA3 & SA4 & SA5 & SA6 & SA7 & SA8).
    pose proof (img_lits bt st Lc FF W) as [I1 I2].
    pose proof (bt_ok_W bt st Lc FF W) as (_ & _ & PRV & QI1 & _).
    destruct QI1 as (plo & phi & Hplo & PP1 & PP2). destruct (PRV plo phi (or_introl Hplo)) as [PP3 PP4].
    assert (INI : ia_img_lo IA <= IB bt + 112 /\ IB bt + 985 <= ia_img_hi IA) by ((lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end); clear -PP1 PP2 PP3 PP4; lia). clear plo phi Hplo PP1 PP2 PP3 PP4.
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN8)) as ((PD1 & PD2 & PD3 & PD4 & PD5) & _).
    pose proof (nth_error_lt _ _ _ Hnth) as Hil.
    assert (PTRfacts : 0 <= Z.of_nat i < len /\ len <= a_nres st /\ 8 * a_nres st <= 2 ^ 23) by ((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); clear -Hil S1 S3; lia).
    pose proof (sec_dyn st s Hs) as HDs.
    (* [comment removed for export] *)
    assert (STEP0 : forall a : word, M' a <> M0 a -> foot_recycle_sec bt st i s (u a) /\ (M' a <> None \/ sc_map s <= u a < sc_map s + sc_mapsz s)).
    { intros a NE. destruct (decide (M' a = M a)) as [E | NE1]; [| exact (STEP a NE1)].
      rewrite E in NE. destruct (D a NE) as [HX DF]. rewrite E. split; [| left; exact DF].
      (lazymatch goal with |- ?G => let G' := eval unfold foot_recycle_sec in G in change_no_check G' end). destruct (XSUB _ HX) as [F | [F | F]]; [do 3 right; left; exact F | do 5 right; left; exact F | do 6 right; exact F]. }
    pose proof (Xdec_iv (sc_map s) (sc_map s + sc_mapsz s)) as Md.
    set (Mx := fun a : word => if Md (u a) then M0 a else M' a).
    assert (OFFM : forall z, ~ (sc_map s <= z < sc_map s + sc_mapsz s) -> 0 <= z < 2 ^ 64 -> Mx (Z_to_bv 64 z) = M' (Z_to_bv 64 z)).
    { intros z NM Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mx in G in change_no_check G' end). rewrite (u64_lit z) by lia. destruct (Md z); [contradiction | reflexivity]. }
    assert (RC : Rep bt (op_sec_free st i) (La ++ Lb) FF Mx mdl').
    { apply (OPS_REP_secfree_live_pf st La Lb FF M0 Mx mdl mdl' p n i s qt qg W R HPn Hnth Hus); try assumption.
      - (* [comment removed for export] *) intros a NE. unfold Mx in NE |- *. destruct (Md (u a)) as [IM | NM]; [exfalso; exact (NE eq_refl)|].
        destruct (STEP0 a NE) as [F Dd]. split; [| destruct Dd as [Dd | Dd]; [exact Dd | contradiction]].
        unfold foot_recycle_sec in F. (lazymatch goal with |- ?G => let G' := eval unfold foot_secfree_live in G in change_no_check G' end).
        destruct F as [F|[F|[F|[F|[F|[F|F]]]]]]; [left; exact F | right; left; exact F | do 2 right; left; exact F | contradiction | do 3 right; left; exact F | do 4 right; left; exact F | do 5 right; exact F].
      - (* [comment removed for export] *) eapply (cellZ_frame _ _ _ _ _ _ CNCH); [clear -INI I1; lia | clear -INI I2; ulia |]. intros z Hz. cbn in Hz.
        apply OFFM; [| clear -Hz INI I1 I2; ulia].
        destruct (RNG _ _ (all_ranges_dyn bt st _ HDs)) as ((_ & _ & _ & D4 & _) & _). clear -Hz INI D4. lia.
      - (* [comment removed for export] *) eapply (byteZ_frame _ _ _ _ _ CMTX); [clear -INI I1; lia | clear -INI I2; ulia |].
        apply OFFM; [| clear -INI I1 I2; ulia].
        destruct (RNG _ _ (all_ranges_dyn bt st _ HDs)) as ((_ & _ & _ & D4 & _) & _). clear -INI D4. lia.
      - (* [comment removed for export] *) intros sl LT HL. destruct (CMOVE sl LT HL) as [CP CI]. pose proof (nth_error_In _ _ HL) as Hsl.
        destruct (sec_facts bt st Lc FF W sl Hsl) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
        assert (NEs : sl <> s).
        { intros ->. pose proof (proj1 (NoDup_nth_error (a_sec st)) (NoDup_map_inv _ _ S5) i (length (a_sec st) - 1)%nat Hil ltac:(rewrite Hnth, HL; reflexivity)). unfold len in LT. lia. }
        destruct (sec_cases bt st Lc FF W sl s Hsl Hs) as [E | DJ]; [exact (False_ind _ (NEs E))|].
        split.
        + eapply (cellZ_frame _ _ _ _ _ _ CP); [clear -PD1; lia | clear -PTRfacts PD1 PD2 PD3; ulia |]. intros z Hz. cbn in Hz.
          apply OFFM; [| clear -Hz PTRfacts PD1 PD2 PD3; ulia].
          pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W IN8 HDs) as D8. hnf in D8. cbn in D8. clear -Hz PTRfacts D8. lia.
        + eapply (cellZ_frame _ _ _ _ _ _ CI); [clear -Q1; lia | clear -Q2 Q5 Q6 Q7; ulia |]. intros z Hz. cbn in Hz.
          apply OFFM; [clear -Hz DJ Q5 Q6 Q7; unfold PG in *; lia | clear -Hz Q1 Q2 Q5 Q6 Q7; ulia]. }
    (* [comment removed for export] *)
    pose proof (OPS_WFq_sec_free_live_pf bt st La Lb FF p n i s qt qg W HPn Hnth Hus) as W'.
    destruct (secfree_live_map_apart st Lc FF qt qg i s W Hnth) as [DOK AP].
    apply (secfree_unmap bt _ (La ++ Lb) FF Mx M' mdl' _ _ qt qg W' RC DOK AP). intros a NM. (lazymatch goal with |- ?G => let G' := eval unfold Mx in G in change_no_check G' end).
    destruct (Md (u a)); [contradiction | reflexivity].
  Qed.
End RC9.
