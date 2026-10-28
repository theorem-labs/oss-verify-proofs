(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BStep BLFrame BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DKit LbB_Kit LbB_HKit.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition zpatch (o : Z) (src : list byte) (cs : list Z) : list Z :=
  map (fun t : nat => let z := Z.of_nat t in
                      if ((o <=? z) && (z <? o + Zlen src))%bool then bv_unsigned (nth (Z.to_nat (z - o)) src (Z_to_bv 8 0))
                      else Znth z cs)
      (seq 0 (length cs)).

Lemma Zlen_zpatch : forall o src cs, Zlen (zpatch o src cs) = Zlen cs.
Proof. intros. unfold zpatch, Zlen. rewrite length_map, length_seq. reflexivity. Qed.

Lemma Znth_zpatch : forall o src cs i, 0 <= i < Zlen cs ->
  Znth i (zpatch o src cs) = if ((o <=? i) && (i <? o + Zlen src))%bool then bv_unsigned (nth (Z.to_nat (i - o)) src (Z_to_bv 8 0))
                             else Znth i cs.
Proof.
  intros o src cs i Hi. unfold Znth at 1. unfold zpatch. unfold Zlen in Hi.
  set (g := fun t : nat => let z := Z.of_nat t in
                      if ((o <=? z) && (z <? o + Zlen src))%bool then bv_unsigned (nth (Z.to_nat (z - o)) src (Z_to_bv 8 0))
                      else Znth z cs).
  rewrite (nth_indep _ 0 (g 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth. rewrite seq_nth by lia. subst g. cbn beta zeta. rewrite Nat.add_0_l, Z2Nat.id by lia. reflexivity.
Qed.

Lemma word_to_le_bytes_1 : forall b : byte, word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof.
  intros b. change (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b))) with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b)))].
  pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R.
  rewrite u64_of_Z by lia. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Section Str.
  #[local] Notation str_repA := (@str_rep AC_A ASEGS LY_A MI_A).
  #[local] Notation fld := (CRep.fld ASEGS).

  Lemma strA_recontent : forall A M M' s ms cs o (src : list byte),
    str_repA A M s ms cs -> Zlen cs = str_cap ms -> 0 <= o -> o + Zlen src <= str_cap ms ->
    mdef M' s 24 ->
    agree_on (fun a => str_fp s ms cs a /\ ~ (str_data s ms + o <= a < str_data s ms + o + Zlen src)) M M' ->
    bytes_at asegs M' (str_data s ms + o) src ->
    exists cs', str_repA A M' s ms cs' /\ Zlen cs' = Zlen cs.
  Proof.
    intros A M M' s ms cs o src STR HL Ho Hok HD' HA HB.
    pose proof STR as (Hs & Hs' & HD & Hlen & HM & HC & HZ).
    assert (ZS : 0 <= Zlen src) by (unfold Zlen; lia).
    exists (zpatch o src cs). rewrite Zlen_zpatch. split; [| reflexivity].
    assert (DAT : (ms = SShort /\ str_data s ms = s + 1 /\ str_cap ms = 22)
                  \/ (exists d asz, ms = SLong d asz /\ str_data s ms = d /\ str_cap ms = asz - 1 /\ 0 < d /\ (s + 24 <= d \/ d + asz <= s)
                                     /\ d + asz <= 2 ^ 63)).
    { destruct ms as [|d asz]; [left; repeat split; reflexivity | right].
      destruct HM as (Hd0 & _ & Hdsz & _ & _ & _ & Hdj & _). exists d, asz. repeat split; try assumption; reflexivity. }

    assert (T : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                (forall x, a <= x < a + Z.of_nat k -> str_fp s ms cs x /\ ~ (str_data s ms + o <= x < str_data s ms + o + Zlen src)) ->
                fld M a k v -> fld M' a k v).
    { intros a k v H0 H1 HP HF. eapply fld_agree; [exact H0 | exact H1 | exact HF |].
      eapply agree_on_weaken; [exact HA|]. intros x Hx. apply HP. unfold zwin in Hx. exact Hx. }
    unfold str_rep. rewrite !Zlen_zpatch. split; [exact Hs|]. split; [exact Hs'|]. split; [exact HD'|]. split; [lia|]. split; [| split].
    - destruct DAT as [(E & Hdat & Hcap)|(d & asz & E & Hdat & Hcap & Hd0 & Hdj & Hdhi)]; rewrite E in *; cbn [str_data str_cap] in *.
      + apply T; [lia | cbn; lia | | exact HM]. intros x Hx. cbn in Hx. split; [left; unfold zwin; lia | lia].
      + destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & F0 & F1 & F2).
        repeat (split; [assumption|]). split; [|split]; (apply T; [lia | cbn; lia | | assumption]);
          intros x Hx; cbn in Hx; (split; [left; unfold zwin; lia | lia]).
    - intros i Hi. rewrite Znth_zpatch by lia.
      destruct (andb (o <=? i) (i <? o + Zlen src)) eqn:Eb.
      + apply andb_true_iff in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        set (b := nth (Z.to_nat (i - o)) src (Z_to_bv 8 0)).
        pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. split; [lia|].
        unfold fld. rewrite word_to_le_bytes_1.
        pose proof (bytes_at_rdn asegs M' _ _ (Z.to_nat (i - o)) 1 HB ltac:(unfold Zlen in *; lia)) as RD.
        unfold wa in RD. replace (str_data s ms + o + Z.of_nat (Z.to_nat (i - o))) with (str_data s ms + i) in RD by lia.
        rewrite <- LbB_Conv.rdn_HL in RD. unfold asegs, RefMemImage.Ref.loaded_segments in RD. rewrite RD. f_equal. subst b.
        rewrite <- (firstn_skipn 0 (skipn (Z.to_nat (i - o)) src)) at 1.
        cbn [firstn skipn app]. destruct (skipn (Z.to_nat (i - o)) src) as [|b0 r] eqn:SK.
        * exfalso. apply (f_equal (@length byte)) in SK. rewrite length_skipn in SK. cbn in SK. unfold Zlen in *. lia.
        * cbn. rewrite <- (Nat.add_0_r (Z.to_nat (i - o))). rewrite <- (nth_skipn). rewrite SK. reflexivity.
      + destruct (HC i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
        assert (NI : ~ (o <= i < o + Zlen src)).
        { intros K. apply Bool.andb_false_iff in Eb. destruct Eb as [Eb|Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
        destruct DAT as [(E & Hdat & Hcap)|(d & asz & E & Hdat & Hcap & Hd0 & Hdj & Hdhi)]; subst ms; cbn [str_data str_cap str_fp] in *;
          (apply T; [lia | cbn; lia | | exact HF]); intros x Hx; cbn in Hx; (split; [| lia]); [left | right]; unfold zwin; lia.
    - destruct DAT as [(E & Hdat & Hcap)|(d & asz & E & Hdat & Hcap & Hd0 & Hdj & Hdhi)]; subst ms; cbn [str_data str_cap str_fp] in *;
        (apply T; [lia | cbn; lia | | exact HZ]); intros x Hx; cbn in Hx; (split; [| lia]); [left | right]; unfold zwin; lia.
  Qed.
End Str.

Lemma pc_lb_small_app : forall L L', lb_small (L ++ L') = lb_small L + lb_small L'.
Proof. induction L as [|b L IH]; intros L'; [reflexivity|]. cbn [app]. rewrite !lb_small_cons, IH. lia. Qed.
Lemma pc_nlarge_app : forall L L', nlarge (L ++ L') = nlarge L + nlarge L'.
Proof. induction L as [|b L IH]; intros L'; [reflexivity|]. cbn [app]. rewrite !nlarge_cons, IH. lia. Qed.
Lemma pc_lb_small_perm : forall L L', Permutation L L' -> lb_small L = lb_small L'.
Proof.
  intros L L' P. induction P; [reflexivity | rewrite !lb_small_cons; lia | rewrite !lb_small_cons; lia | lia].
Qed.
Lemma pc_nlarge_perm : forall L L', Permutation L L' -> nlarge L = nlarge L'.
Proof.
  intros L L' P. induction P; [reflexivity | rewrite !nlarge_cons; lia | rewrite !nlarge_cons; lia | lia].
Qed.
Lemma pc_lb_small_nonneg : forall L, Forall (fun b => 0 <= blk_size b) L -> 0 <= lb_small L.
Proof.
  induction L as [|b L IH]; intros F; [cbn; lia|]. rewrite lb_small_cons.
  pose proof (nsmall_bounds (blk_size b) (Forall_inv F)). pose proof (IH (Forall_inv_tail F)). lia.
Qed.
Lemma pc_nlarge_nonneg : forall L, 0 <= nlarge L.
Proof. induction L as [|b L IH]; [cbn; lia|]. rewrite nlarge_cons. pose proof (nlg_bounds (blk_size b)). lia. Qed.

Lemma rtbl_rew : forall W W' R T T',
  Forall2 (fun re re' => fst re' = fst re /\ edenot (wenv W') (snd re') = edenot (wenv W) (snd re)) T T' ->
  rtbl W R T -> rtbl W' R T'.
Proof.
  intros W W' R T T' F2 HT. unfold rtbl in *. induction F2 as [|re re' T0 T0' [E1 E2] F2 IH]; [constructor|].
  apply Forall_cons_iff in HT as [H1 H2]. constructor; [| exact (IH H2)]. rewrite E1, E2. exact H1.
Qed.

Lemma ftbl_rew : forall W W' B m T T',
  Forall2 (fun f f' => fst f' = fst f /\ edenot (wenv W') (snd f') = edenot (wenv W) (snd f)) T T' ->
  ftbl W B m T -> ftbl W' B m T'.
Proof.
  intros W W' B m T T' F2 HT. unfold ftbl in *. induction F2 as [|[[k w] e] [[k' w'] e'] T0 T0' [E1 E2] F2 IH]; [constructor|].
  cbn [fst snd] in E1, E2. injection E1 as -> ->.
  apply Forall_cons_iff in HT as [H1 H2]. constructor; [| exact (IH H2)]. cbn beta iota. rewrite E2. exact H1.
Qed.

Section CL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma blk_cls : forall s' LB mm LBx LBr q A n SP a,
    as_RHEAP H s' LB mm -> Permutation LB (LBx ++ LBr) -> In (q, A, n) LBr -> aceil <= SP -> aclient_addr H LBx SP a ->
    SP <= a \/ (a < aceil /\ ~ (A <= a < A + n) /\ ~ (sh A <= a < sh A + nsh n)).
  Proof.
    intros s' LB mm LBx LBr q A n SP a RH PE INq HSP Hc.
    assert (INqL : In (q, A, n) LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact INq).
    pose proof (ah_blocks H HH _ _ _ (q, A, n) RH INqL) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof aceil_facts as ACF.
    assert (SHA : sh A + nsh n <= sh aceil).
    { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
    assert (SHB : sh aceil < 0x10007fff8000) by (unfold sh; rewrite ASHADOW_BASE_val; acb; Z.div_mod_to_equations; lia).
    unfold AIMG_TOP in RI.
    assert (SHL : 0x7fff7000 < sh A) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (NDq : forall b0, In b0 LBx -> blk_id b0 <> q).
    { intros b0 Hb E. pose proof (ah_nodup H HH _ _ _ RH) as ND.
      pose proof (Permutation_NoDup (Permutation_map blk_id PE) ND) as ND'. rewrite map_app in ND'.
      apply (LbB_HKit.nodup_app_disj _ _ _ q ND').
      - apply in_map_iff. exists b0. split; [exact E | exact Hb].
      - apply in_map_iff. exists (q, A, n). split; [reflexivity | exact INq]. }
    acb.
    unfold aclient_addr in Hc.
    destruct Hc as [Hc|[Hc|[(b0 & Hb & Hr)|[(b0 & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
    - left. exact Hc.
    - right. unfold aimg_client in Hc. destruct Hc as [Hc|[Hc|[Hc|Hc]]]; (split; [lia | split; lia]).
    - right. assert (Hb' : In b0 LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; left; exact Hb).
      pose proof (NDq b0 Hb) as Hid.
      pose proof (ah_disj H HH _ _ _ (q, A, n) b0 RH INqL Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      destruct b0 as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in QAPP, HI2.
      destruct D as [D|D]; destruct QAPP as [QAPP|QAPP]; split; try lia; split; lia.
    - right. assert (Hb' : In b0 LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; left; exact Hb).
      pose proof (NDq b0 Hb) as Hid.
      pose proof (ah_disj H HH _ _ _ (q, A, n) b0 RH INqL Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b0 RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      unfold blk_addr, blk_size in D, Hr, Q0, Q16, Qn, QI, QC, QF, QAPP. cbn [fst snd] in D.
      destruct b0 as [[pb Ab] nb]. cbn [fst snd] in *.
      unfold aapp, aapp_lo, aapp_hi in RAPP, QAPP. acb.
      unfold nsh, sh, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct D as [D|D]; split; try lia; split; lia.
    - right. assert (HI2 : sh A + nsh n <= AHI_LO) by (apply sh_nsh_high; unfold AAPP_HI; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in F4, HI2. unfold AFS_SIZE in *.
      destruct RF as [RF|RF]; destruct F4 as [F4|F4]; split; try lia; split; lia.
    - right. unfold aapp, aapp_lo, aapp_hi in RAPP, F4. acb.
      unfold sh, nsh, AFS_SIZE, AHI_LO, ALOWSH_LO, AIMG_TOP in *. rewrite ASHADOW_BASE_val in *.
      Z.div_mod_to_equations.
      destruct RF as [RF|RF]; split; try lia; split; lia.
    - right. assert (SA0 : 0x7fff8000 <= sh aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in RAPP, Hc. destruct RAPP as [RP|RP]; split; try lia; split; lia.
  Qed.

  Lemma xpres_drop_blk : forall s' LB mm LBx LBr q A n SP X m1 m2,
    as_RHEAP H s' LB mm -> Permutation LB (LBx ++ LBr) -> In (q, A, n) LBr -> aceil <= SP ->
    xpres H LBx SP (X ++ [(A, A + n); (sh A, sh A + nsh n)]) m1 m2 -> xpres H LBx SP X m1 m2.
  Proof.
    intros s' LB mm LBx LBr q A n SP X m1 m2 RH PE INq HSP XP a Ha [Hc Hx].
    apply XP; [exact Ha|]. split; [exact Hc|].
    intros K. apply rin_ivs_app in K. destruct K as [K|K]; [exact (Hx K)|].
    assert (INqL : In (q, A, n) LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; exact INq).
    destruct (blk_cls s' LB mm LBx LBr q A n SP a RH PE INq HSP Hc) as [C|(C1 & C2 & C3)].
    - pose proof (ah_blocks H HH _ _ _ (q, A, n) RH INqL) as (R0 & _ & Rn & _ & RC & _). cbn in RC.
      pose proof aceil_facts as ACF.
      cbn [rin_ivs fst snd] in K. destruct K as [K|[K|K]]; [lia | | contradiction].
      assert (sh A + nsh n <= sh aceil).
      { unfold sh, nsh. acb. Z.div_mod_to_equations. nia. }
      assert (sh aceil < aceil) by (apply sh_below_aceil; acb; unfold AAPP_HI; lia). lia.
    - cbn [rin_ivs fst snd] in K. destruct K as [K|[K|K]]; [exact (C2 K) | exact (C3 K) | contradiction].
  Qed.
End CL.
