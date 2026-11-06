(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk MemSplit Frame MmapSim LibIface LibBudget LibEff S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Export S1AddrFacts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import RunsLib S1CxxTable StaticsGen S1Statics S1Cells
  S1TargetDefs S1TargetBlocks S1ExitKn S1ExitDefs S1Spec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition dclear_ivs : list (Z * Z) :=
  [(0xee0e8, 0xee1b0); (0xee1b0, 0xee390); (0xee4e8, 0xee4e9); (0x120700, 0x120708); (0x120718, 0x120720);
   (0x120920, 0x120924); (0x120e88, 0x120e90)].

Definition dcore_ivs : list (Z * Z) :=
  [(0x10000, 0xee000); (0xee0e8, 0xee390); (0xee4e8, 0xee4e9); (0xfe4f0, 0xfe4f1); (0xfe4f4, 0xfe4f5);
   (0x100610, 0x100614); (0x120700, 0x120708); (0x120708, 0x12070c); (0x120718, 0x120720);
   (0x120728, 0x120730); (0x120828, 0x120830);
   (0x120920, 0x120924); (0x120e88, 0x120e90)].
Definition dout_ivs : list (Z * Z) := [(0xee390, 0xee480); (0x1212a8, 0x1212b0)].
Definition dimg_ivs : list (Z * Z) := dcore_ivs ++ dout_ivs.

Lemma dimg_img : forall a, in_ivs dimg_ivs a -> 0x10000 <= a < 0x122000.
Proof. intros a H. apply in_ivsb_spec in H. cbn [in_ivsb dimg_ivs dcore_ivs dout_ivs app] in H. lia. Qed.

Lemma dimg_not_static : forall a, in_ivs dimg_ivs a -> ~ mng_static a.
Proof. intros a H. apply in_ivsb_spec in H. cbn [in_ivsb dimg_ivs dcore_ivs dout_ivs app] in H. unfold mng_static. lia. Qed.

Lemma dimg_not_errno : forall a, in_ivs dimg_ivs a -> ~ errno_win L a.
Proof. intros a H. apply in_ivsb_spec in H. cbn [in_ivsb dimg_ivs dcore_ivs dout_ivs app] in H. unfold errno_win, zwin. cbn. lia. Qed.

Lemma dimg_clear_sx :
  Forall (fun iv : Z * Z => iv = (0x10000, 0xee000) \/ runs_clear D_SX (fst iv) (Z.to_nat (snd iv - fst iv)) = true) dimg_ivs.
Proof.
  unfold dimg_ivs, dcore_ivs, dout_ivs. cbn [app].
  repeat (apply Forall_cons; [cbn [fst snd]; first [left; reflexivity | right; vm_compute; reflexivity] |]). apply Forall_nil.
Qed.

Lemma dimg_not_sx : forall a, in_ivs dimg_ivs a -> ~ sx_region S1ST a.
Proof.
  intros a Ha Hsx. pose proof Ha as (lo & hi & Hin & Hr). apply s1_region in Hsx.
  destruct Hsx as [Hruns | Hh].
  - pose proof (proj1 (Forall_forall _ _) dimg_clear_sx (lo, hi) Hin) as Hc. cbn [fst snd] in Hc.
    destruct Hc as [E0 | Hc].
    + injection E0 as -> ->. pose proof (D_SX_rw a Hruns) as (lo' & hi' & Hin' & Hr'). cbn in Hin'. destruct Hin' as [E|[]]. injection E as <- <-.
      lia.
    + apply Hruns. apply (runs_clear_lookup D_SX lo (Z.to_nat (hi - lo))); [exact Hc | lia].
  - assert (Hb : in_ivsb dimg_ivs a = true) by (apply in_ivsb_spec; exact Ha).
    cbn [in_ivsb dimg_ivs dcore_ivs dout_ivs app] in Hb. unfold zwin in Hh. cbn in Hh. lia.
Qed.

Definition file_ivs : list (Z * Z) :=
  [(0xee394, 0xee398); (0xee3a8, 0xee3b0); (0xee3c0, 0xee3c8); (0xee3d0, 0xee3d8);
   (0xee3e0, 0xee418); (0xee41c, 0xee420); (0xee424, 0xee480)].

Record stdout_k (j : nat) (M : word -> option byte) : Prop := {
  sk_flags : cell M 0xee390 4 5;
  sk_rpos  : cell M 0xee398 8 0;
  sk_rend  : cell M 0xee3a0 8 0;
  sk_wend  : cell M 0xee3b0 8 0x1216a8;
  sk_wpos  : cell M 0xee3b8 8 (0x1212a8 + 2 * Z.of_nat j);
  sk_wbase : cell M 0xee3c8 8 0x1212a8;
  sk_write : cell M 0xee3d8 8 0xd537c;
  sk_mode  : cell M 0xee418 4 0xffffffff;
  sk_lbf   : cell M 0xee420 4 0xffffffff;
  sk_clear : Forall (fun iv => img_clear M (fst iv) (snd iv)) file_ivs;
  sk_pend  : rdn RSEGS M (Z_to_bv 64 0x1212a8) (2 * j) = Some (zero_lines j)
}.

Definition stdout_st (k : nat) (M : word -> option byte) : Prop :=
  match k with O => img_clear M 0xee390 0xee480 | S j => (j <= 3)%nat /\ stdout_k j M end.

Record tmem (sp0 tid : Z) (k : nat) (b : Z) (M : word -> option byte) : Prop := {
  tm_text  : img_clear M 0x10000 0xee000;
  tm_clear : Forall (fun iv => img_clear M (fst iv) (snd iv)) dclear_ivs;
  tm_init  : cell M INITIALIZED 1 1;
  tm_slot  : cell M AT_SLOT 4 2;
  tm_f1    : cell M AT_F1 8 AT_CALL;
  tm_a1    : cell M AT_A1 8 AEF_GUARD;
  tm_cb    : cell M AEF_CB 1 b;
  tm_tid   : cell M 0x100610 4 tid;
  tm_stack : stack_writableZ M sp0;
  tm_out   : stdout_st k M
}.

Section Xfer.
Context {AC : AllocCeiling}.
  Variables (sp0 tid : Z).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.

  Lemma stdout_st_agree : forall k M M',
    (forall i, 0xee390 <= i < 0xee480 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    (forall i, 0x1212a8 <= i < 0x1212b0 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
    stdout_st k M -> stdout_st k M'.
  Proof.
    intros k M M' H1 H2 S. destruct k as [|j]; cbn [stdout_st] in *.
    - eapply img_clear_agree; [exact H1 | exact S].
    - destruct S as [Hj S]. split; [exact Hj|]. destruct S. unfold cell in *.
      constructor; unfold cell;
        try (eapply rdn_agree; [lia | cbn; lia | | eassumption]; intros i Hi; cbn in Hi; first [apply H1; lia | apply H2; lia]).
      + apply Forall_forall. intros [lo hi] Hin. pose proof (proj1 (Forall_forall _ _) sk_clear0 _ Hin) as Hc. cbn [fst snd] in Hc |- *.
        assert (Hb : 0xee390 <= lo /\ hi <= 0xee480).
        { unfold file_ivs in Hin. cbn in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
        eapply img_clear_agree; [|exact Hc]. intros i Hi. apply H1. lia.
  Qed.

  Lemma tmem_xfer_core : forall k k' b M M',
    tmem sp0 tid k b M ->
    (forall a, in_ivs dcore_ivs a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a, sp0 - 8388608 <= a < sp0 -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
    stdout_st k' M' ->
    tmem sp0 tid k' b M'.
  Proof.
    intros k k' b M M' TM Hag Hdef SO.
    assert (HI : forall lo hi, In (lo, hi) dcore_ivs -> forall i, lo <= i < hi -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hin i Hi. apply Hag. exists lo, hi. split; assumption. }
    unfold dcore_ivs in HI.
    destruct TM as [T1 T2 T3 TS1 TF1 TA1 TCB T4 T8 T9]. constructor.
    - eapply img_clear_agree; [|exact T1]. apply HI. cbn; tauto.
    - unfold dclear_ivs in *.
      repeat match goal with |- Forall _ (_ :: _) => apply Forall_cons | |- Forall _ [] => apply Forall_nil end;
        cbn [fst snd]; lazymatch goal with |- img_clear M' ?lo ?hi =>
          apply Forall_forall with (x := (lo, hi)) in T2; [|cbn; tauto]; cbn [fst snd] in T2;
          eapply img_clear_agree; [|exact T2]; intros i Hi end.
      + apply (HI 0xee0e8 0xee390); [cbn; tauto | lia].
      + apply (HI 0xee0e8 0xee390); [cbn; tauto | lia].
      + apply (HI 0xee4e8 0xee4e9); [cbn; tauto | lia].
      + apply (HI 0x120700 0x120708); [cbn; tauto | lia].
      + apply (HI 0x120718 0x120720); [cbn; tauto | lia].
      + apply (HI 0x120920 0x120924); [cbn; tauto | lia].
      + apply (HI 0x120e88 0x120e90); [cbn; tauto | lia].
    - unfold cell in *. eapply rdn_agree; [unfold INITIALIZED; lia | unfold INITIALIZED; cbn; lia | | exact T3].
      intros i Hi. apply (HI 0xfe4f0 0xfe4f1); [cbn; tauto | unfold INITIALIZED in Hi; cbn in Hi; lia].
    - unfold cell in *. eapply rdn_agree; [unfold AT_SLOT; lia | unfold AT_SLOT; cbn; lia | | exact TS1].
      intros i Hi. apply (HI 0x120708 0x12070c); [cbn; tauto | unfold AT_SLOT in Hi; cbn in Hi; lia].
    - unfold cell in *. eapply rdn_agree; [unfold AT_F1; lia | unfold AT_F1; cbn; lia | | exact TF1].
      intros i Hi. apply (HI 0x120728 0x120730); [cbn; tauto | unfold AT_F1 in Hi; cbn in Hi; lia].
    - unfold cell in *. eapply rdn_agree; [unfold AT_A1; lia | unfold AT_A1; cbn; lia | | exact TA1].
      intros i Hi. apply (HI 0x120828 0x120830); [cbn; tauto | unfold AT_A1 in Hi; cbn in Hi; lia].
    - unfold cell in *. eapply rdn_agree; [unfold AEF_CB; lia | unfold AEF_CB; cbn; lia | | exact TCB].
      intros i Hi. apply (HI 0xfe4f4 0xfe4f5); [cbn; tauto | unfold AEF_CB in Hi; cbn in Hi; lia].
    - unfold cell in *. eapply rdn_agree; [lia | cbn; lia | | exact T4].
      intros i Hi. apply (HI 0x100610 0x100614); [cbn; tauto | cbn in Hi; lia].
    - eapply (stack_def_xfer sp0 Hsp); [exact T8 | exact Hdef].
    - exact SO.
  Qed.

  Lemma tmem_xfer : forall k b M M',
    tmem sp0 tid k b M ->
    (forall a, in_ivs dimg_ivs a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a, sp0 - 8388608 <= a < sp0 -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
    tmem sp0 tid k b M'.
  Proof.
    intros k b M M' TM Hag Hdef. eapply tmem_xfer_core; [exact TM | | exact Hdef |].
    - intros a Ha. apply Hag. unfold dimg_ivs. apply in_ivs_app. left; exact Ha.
    - eapply stdout_st_agree; [ | | exact (tm_out _ _ _ _ _ TM)];
        intros i Hi; apply Hag; unfold dimg_ivs; apply in_ivs_app; right;
        [exists 0xee390, 0xee480 | exists 0x1212a8, 0x1212b0]; (split; [cbn; tauto | lia]).
  Qed.

  Lemma tmem_set_cb : forall k b b' M M',
    tmem sp0 tid k b M -> frame_mod M M' aef_region -> cell M' AEF_CB 1 b' -> tmem sp0 tid k b' M'.
  Proof.
    intros k b b' M M' TM [FE FG] HC.
    assert (OUT : forall i, 0 <= i < 2 ^ 64 -> i <> AEF_CB -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi Hne. apply FE. unfold aef_region, AEF_CB in *. cbn [outside]. unfold in_rng. rewrite !u64_lit by lia. split; [lia | exact I]. }
    assert (HI : forall lo hi, In (lo, hi) dcore_ivs -> (lo, hi) <> (0xfe4f4, 0xfe4f5) ->
                 forall i, lo <= i < hi -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hin Hne i Hi. unfold dcore_ivs in Hin. cbn in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; first [congruence | apply OUT; unfold AEF_CB; lia] |]). destruct Hin. }
    unfold dcore_ivs in HI.
    destruct TM as [T1 T2 T3 TS1 TF1 TA1 TCB T4 T8 T9]. constructor.
    - eapply img_clear_agree; [|exact T1]. apply HI; [cbn; tauto | intros E; discriminate E].
    - unfold dclear_ivs in *.
      repeat match goal with |- Forall _ (_ :: _) => apply Forall_cons | |- Forall _ [] => apply Forall_nil end;
        cbn [fst snd]; lazymatch goal with |- img_clear M' ?lo ?hi =>
          apply Forall_forall with (x := (lo, hi)) in T2; [|cbn; tauto]; cbn [fst snd] in T2;
          eapply img_clear_agree; [|exact T2]; intros i Hi; apply OUT; unfold AEF_CB; lia end.
    - unfold cell in *. eapply rdn_agree; [unfold INITIALIZED; lia | unfold INITIALIZED; cbn; lia | | exact T3].
      intros i Hi. apply OUT; unfold INITIALIZED, AEF_CB in *; cbn in Hi; lia.
    - unfold cell in *. eapply rdn_agree; [unfold AT_SLOT; lia | unfold AT_SLOT; cbn; lia | | exact TS1].
      intros i Hi. apply OUT; unfold AT_SLOT, AEF_CB in *; cbn in Hi; lia.
    - unfold cell in *. eapply rdn_agree; [unfold AT_F1; lia | unfold AT_F1; cbn; lia | | exact TF1].
      intros i Hi. apply OUT; unfold AT_F1, AEF_CB in *; cbn in Hi; lia.
    - unfold cell in *. eapply rdn_agree; [unfold AT_A1; lia | unfold AT_A1; cbn; lia | | exact TA1].
      intros i Hi. apply OUT; unfold AT_A1, AEF_CB in *; cbn in Hi; lia.
    - exact HC.
    - unfold cell in *. eapply rdn_agree; [lia | cbn; lia | | exact T4].
      intros i Hi. apply OUT; unfold AEF_CB; cbn in Hi; lia.
    - eapply stack_writableZ_grows; [exact FG | exact T8].
    - eapply stdout_st_agree; [ | | exact T9]; intros i Hi; apply OUT; unfold AEF_CB; lia.
  Qed.
End Xfer.

Section Abs.
Context {AC : AllocCeiling}.
  Context {AMB : Amb}.
  Variable MI : MallocIface SEGS L.
  Variables (sp0 tid : Z).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.

  Hypothesis HAC : alloc_ceiling = sp0 - 8388608.

  Record tabs (A : AS MI) (M : word -> option byte) (model : Model) : Prop := {
    ta_ainv : ainv MI A M model;
    ta_mstd : mstd model;
    ta_caps : caps MI A = lib_caps;
    ta_big  : bigcap MI A = LIB_BIGCAP;
    ta_own  : forall a, owned MI A a -> in_ranges (ly_img L) a -> mng_static a;
    ta_fd1  : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
  }.

  Lemma dimg_not_owned : forall A M model a, tabs A M model -> in_ivs dimg_ivs a -> ~ owned MI A a.
  Proof.
    intros A M model a TA Ha Ho. apply (dimg_not_static a Ha). apply (ta_own _ _ _ TA a Ho).
    apply img_iff. apply dimg_img. exact Ha.
  Qed.

  Lemma tstep_lib : forall k b A A' M M' model model',
    tmem sp0 tid k b M -> tabs A M model ->
    ainv MI A' M' model' -> mstd model' -> m_fds model' = m_fds model ->
    eff MI A A' M M' (sp0 - 208 - LIB_STACK, sp0 - 208) (sx_region S1ST) ->
    tmem sp0 tid k b M' /\ tabs A' M' model'
    /\ (forall i, sp0 - 208 <= i < sp0 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  Proof.
    intros k b A A' M M' model model' TM TA AI' MS' FDS EF.
    pose proof ac_bounds_lit as Hcv. pose proof (ta_ainv _ _ _ TA) as AI.
    destruct EF as [C B O FR D OI].
    assert (AGI : forall a, in_ivs dimg_ivs a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. pose proof (dimg_img a Ha) as Hr. apply FR. rewrite u64_of by lia.
      intros [H|[H|[H|[H|[H|H]]]]].
      - exact (dimg_not_owned A M model a TA Ha H).
      - apply (dimg_not_owned A M model a TA Ha). apply OI; [exact H | apply img_iff; exact Hr].
      - destruct H as [Hni _]. apply Hni. apply img_iff. exact Hr.
      - exact (dimg_not_sx a Ha H).
      - unfold W_of, LIB_STACK in H. cbn in H. pose proof Hsp. lia.
      - exact (dimg_not_errno a Ha H). }
    assert (AGS : forall i, sp0 - 208 <= i < sp0 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply FR. rewrite u64_of by lia.
      intros [H|[H|[H|[H|[H|H]]]]].
      - exact (high_not_owned MI A M model i AI ltac:(lia) H).
      - exact (high_not_owned MI A' M' model' i AI' ltac:(lia) H).
      - destruct H as (_ & _ & Hn). exact (stack_defined sp0 Hsp M i (tm_stack _ _ _ _ _ TM) ltac:(lia) Hn).
      - exact (high_not_sx i ltac:(lia) H).
      - unfold W_of, LIB_STACK in H. cbn in H. pose proof Hsp. lia.
      - exact (high_not_errno i ltac:(lia) H). }
    split; [|split; [|exact AGS]].
    - eapply (tmem_xfer sp0 tid Hsp); [exact TM | exact AGI |].
      intros a Ha Hd. destruct (D a ltac:(lia) Hd) as [H|[H|[H|H]]]; [exact H | exfalso..].
      + exact (high_not_owned MI A M model a AI ltac:(lia) H).
      + exact (high_not_sx a ltac:(lia) H).
      + exact (high_not_errno a ltac:(lia) H).
    - constructor.
      + exact AI'. + exact MS'.
      + rewrite C. exact (ta_caps _ _ _ TA).
      + rewrite B. exact (ta_big _ _ _ TA).
      + intros a Ho Hi. apply (ta_own _ _ _ TA); [apply OI; assumption | exact Hi].
      + rewrite FDS. exact (ta_fd1 _ _ _ TA).
  Qed.

  Lemma tstep_free : forall k b A A' M M' model model' (p n sp : Z),
    tmem sp0 tid k b M -> tabs A M model ->
    (n = 0 \/ In (p, n) (live MI A)) ->
    sp0 - 208 <= sp <= sp0 -> MALLOC_STACK MI <= 65536 ->
    ainv MI A' M' model' -> mstd model' -> m_fds model' = m_fds model ->
    caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
    (forall a, owned MI A' a -> owned MI A a \/ p <= a < p + n) ->
    frame_eq (fun a => owned MI A a \/ p <= a < p + n \/ zwin (sp - MALLOC_STACK MI) sp a \/ errno_win L a) M M' ->
    (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ p <= bv_unsigned a < p + n \/ errno_win L (bv_unsigned a)) ->
    tmem sp0 tid k b M' /\ tabs A' M' model'
    /\ (forall i, sp <= i < sp0 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  Proof.
    intros k b A A' M M' model model' p n sp TM TA Hlive Hspr HMS AI' MS' FDS C B O FR D.
    pose proof ac_bounds_lit as Hcv. pose proof (ta_ainv _ _ _ TA) as AI.
    assert (BLK : forall a, p <= a < p + n -> a < alloc_ceiling /\ ~ in_ranges (ly_img L) a).
    { intros a Ha. destruct Hlive as [-> | Hin]; [lia|].
      destruct (ai_live_block MI A M model p n AI Hin) as (_ & _ & _ & Hc & Hb).
      split; [lia|]. exact (proj1 (proj2 (Hb a Ha))). }
    assert (AGI : forall a, in_ivs dimg_ivs a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. pose proof (dimg_img a Ha) as Hr. apply FR. rewrite u64_of by lia.
      intros [H|[H|[H|H]]].
      - exact (dimg_not_owned A M model a TA Ha H).
      - apply (proj2 (BLK a H)). apply img_iff. exact Hr.
      - unfold zwin in H. lia.
      - exact (dimg_not_errno a Ha H). }
    assert (AGS : forall i, sp <= i < sp0 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply FR. rewrite u64_of by lia.
      intros [H|[H|[H|H]]].
      - exact (high_not_owned MI A M model i AI ltac:(lia) H).
      - pose proof (BLK i H). lia.
      - unfold zwin in H. lia.
      - exact (high_not_errno i ltac:(lia) H). }
    split; [|split; [|exact AGS]].
    - eapply (tmem_xfer sp0 tid Hsp); [exact TM | exact AGI |].
      intros a Ha Hd. destruct (D (Z_to_bv 64 a) Hd) as [H|[H|[H|H]]]; [exact H | exfalso; rewrite u64_of in H by lia ..].
      + exact (high_not_owned MI A M model a AI ltac:(lia) H).
      + pose proof (BLK a H). lia.
      + exact (high_not_errno a ltac:(lia) H).
    - constructor.
      + exact AI'. + exact MS'.
      + rewrite C. exact (ta_caps _ _ _ TA).
      + rewrite B. exact (ta_big _ _ _ TA).
      + intros a Ho Hi. destruct (O a Ho) as [H|H]; [exact (ta_own _ _ _ TA a H Hi)|].
        exfalso. exact (proj2 (BLK a H) Hi).
      + rewrite FDS. exact (ta_fd1 _ _ _ TA).
  Qed.

  Lemma tstep_malloc : forall k b A A' M M' model model' (P : Z -> Prop),
    tmem sp0 tid k b M -> tabs A M model -> MALLOC_STACK MI <= 65536 ->
    ainv MI A' M' model' -> mstd model' -> m_fds model' = m_fds model ->
    caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
    (forall a, P a -> exists q k, In (q, k) (live MI A') /\ q <= a < q + k) ->
    (forall a, owned MI A' a -> owned MI A a \/ (~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) = None)) ->
    frame_eq (fun a => owned MI A' a \/ P a \/ zwin (sp0 - 208 - MALLOC_STACK MI) (sp0 - 208) a \/ errno_win L a) M M' ->
    (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ errno_win L (bv_unsigned a)) ->
    tmem sp0 tid k b M' /\ tabs A' M' model'
    /\ (forall i, sp0 - 208 <= i < sp0 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  Proof.
    intros k b A A' M M' model model' P TM TA HMS AI' MS' FDS C B HP NEWT FR D.
    pose proof ac_bounds_lit as Hcv. pose proof (ta_ainv _ _ _ TA) as AI.
    assert (BLK : forall a, P a -> a < alloc_ceiling /\ ~ in_ranges (ly_img L) a).
    { intros a Ha. destruct (HP a Ha) as (q & kk & Hin & Hr).
      destruct (ai_live_block MI A' M' model' q kk AI' Hin) as (_ & _ & _ & Hc & Hb).
      split; [lia|]. exact (proj1 (proj2 (Hb a Hr))). }
    assert (OWN' : forall a, owned MI A' a -> in_ranges (ly_img L) a -> owned MI A a).
    { intros a Ho Hi. destruct (NEWT a Ho) as [H|[H _]]; [exact H | exfalso; exact (H Hi)]. }
    assert (AGI : forall a, in_ivs dimg_ivs a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. pose proof (dimg_img a Ha) as Hr. apply FR. rewrite u64_of by lia.
      intros [H|[H|[H|H]]].
      - apply (dimg_not_owned A M model a TA Ha). apply OWN'; [exact H | apply img_iff; exact Hr].
      - apply (proj2 (BLK a H)). apply img_iff. exact Hr.
      - unfold zwin in H. lia.
      - exact (dimg_not_errno a Ha H). }
    assert (AGS : forall i, sp0 - 208 <= i < sp0 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply FR. rewrite u64_of by lia.
      intros [H|[H|[H|H]]].
      - exact (high_not_owned MI A' M' model' i AI' ltac:(lia) H).
      - pose proof (BLK i H). lia.
      - unfold zwin in H. lia.
      - exact (high_not_errno i ltac:(lia) H). }
    split; [|split; [|exact AGS]].
    - eapply (tmem_xfer sp0 tid Hsp); [exact TM | exact AGI |].
      intros a Ha Hd. destruct (D (Z_to_bv 64 a) Hd) as [H|[H|H]]; [exact H | exfalso; rewrite u64_of in H by lia ..].
      + exact (high_not_owned MI A M model a AI ltac:(lia) H).
      + exact (high_not_errno a ltac:(lia) H).
    - constructor.
      + exact AI'. + exact MS'.
      + rewrite C. exact (ta_caps _ _ _ TA).
      + rewrite B. exact (ta_big _ _ _ TA).
      + intros a Ho Hi. exact (ta_own _ _ _ TA a (OWN' a Ho Hi) Hi).
      + rewrite FDS. exact (ta_fd1 _ _ _ TA).
  Qed.

  Lemma tstep_printf : forall k k' b A M M' model (rs : list (word * Z)),
    tmem sp0 tid k b M -> tabs A M model -> sx_inv S1ST true M ->
    frame_mod M M' rs ->
    (forall a : word, ~ outside a rs ->
        (sp0 - 8388608 <= bv_unsigned a < sp0 - 208) \/ in_ivs dout_ivs (bv_unsigned a)) ->
    stdout_st k' M' ->
    tmem sp0 tid k' b M' /\ tabs A M' model /\ sx_inv S1ST true M'
    /\ (forall i, sp0 - 208 <= i < sp0 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  Proof.
    intros k k' b A M M' model rs TM TA SX [FE FG] HRS SO.
    pose proof ac_bounds_lit as Hcv. pose proof (ta_ainv _ _ _ TA) as AI.
    assert (OUT : forall a : word, ~ ((sp0 - 8388608 <= bv_unsigned a < sp0 - 208) \/ in_ivs dout_ivs (bv_unsigned a)) -> M' a = M a).
    { intros a Hn. apply FE. destruct (Classical_Prop.classic (outside a rs)) as [H|H]; [exact H|]. exfalso. apply Hn. apply HRS. exact H. }
    assert (DOUT : forall a, in_ivs dout_ivs a -> 0xee390 <= a < 0xee480 \/ 0x1212a8 <= a < 0x1212b0).
    { intros a H. apply in_ivsb_spec in H. cbn [in_ivsb dout_ivs] in H. lia. }
    assert (AGC : forall a, in_ivs dcore_ivs a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. assert (Hb : in_ivsb dcore_ivs a = true) by (apply in_ivsb_spec; exact Ha). cbn [in_ivsb dcore_ivs] in Hb.
      apply OUT. rewrite u64_of by lia. intros [H|H]; [lia|]. apply DOUT in H. lia. }
    assert (AGS : forall i, sp0 - 208 <= i < sp0 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply OUT. rewrite u64_of by lia. intros [H|H]; [lia|]. apply DOUT in H. lia. }
    split; [|split; [|split; [|exact AGS]]].
    - eapply (tmem_xfer_core sp0 tid Hsp); [exact TM | exact AGC | | exact SO]. intros a _ Hd Hn. exact (FG _ Hd Hn).
    - constructor; try (destruct TA; assumption).
      eapply (ai_frame MI A M M' model model AI); [ | | reflexivity | reflexivity].
      + intros a Ho. apply OUT. intros [H|H].
        * exact (high_not_owned MI A M model (bv_unsigned a) AI ltac:(lia) Ho).
        * apply (dimg_not_owned A M model (bv_unsigned a) TA); [|exact Ho]. unfold dimg_ivs. apply in_ivs_app. right; exact H.
      + intros a Hd Hn. exact (FG a Hd Hn).
    - eapply (sx_frame S1ST true M M' SX). intros a [Hs|Hr]; apply OUT; intros [H|H].
      + exact (high_not_sx (bv_unsigned a) ltac:(lia) Hs).
      + apply (dimg_not_sx (bv_unsigned a)); [|exact Hs]. unfold dimg_ivs. apply in_ivs_app. right; exact H.
      + destruct Hr as (lo & hi & Hin & Hlh). cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-. lia.
      + destruct Hr as (lo & hi & Hin & Hlh). cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-. apply DOUT in H. lia.
  Qed.
End Abs.
