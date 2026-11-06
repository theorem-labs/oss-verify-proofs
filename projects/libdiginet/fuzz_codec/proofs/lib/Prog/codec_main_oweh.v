From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree codec_cells codec_img
  codec_main_inv LLVMFuzzerTestOneInput_c codec_main_owe_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** A branch that the facts in context decide. *)
Ltac br_not := first [ if_false | (let E := fresh "E" in if_cases E; [ zify_cond E; exfalso; lia | ]) ].
Ltac br_yes := first [ if_true | (let E := fresh "E" in if_cases E; [ | zify_cond E; exfalso; lia ]) ].

(** owe() with a NULL desk on a kind that needs one owes E_ARG. *)
Lemma owe_null_needs : forall kind a b c delta bytes n, ~ (kind = 1 \/ kind = 4 \/ kind = 11) ->
  owe_spec kind None a b c delta bytes n = (E_ARG, noc).
Proof.
  intros kind a b c delta bytes n H. unfold owe_spec.
  destruct (Z.eqb_spec kind 1); [tauto|]. destruct (Z.eqb_spec kind 4); [tauto|].
  destruct (Z.eqb_spec kind 11); [tauto|]. reflexivity.
Qed.

Lemma owe_want_earg : forall k od, od = None -> ~ (k_kind k = 1 \/ k_kind k = 4 \/ k_kind k = 11) ->
  k_want_rc k = -1 -> k_want_len k = 0 -> k_want_key k = 0 -> k_want_display k = 0 -> owe_want_ok k od.
Proof.
  intros k od -> ND H1 H2 H3 H4. unfold owe_want_ok, owe_k. rewrite owe_null_needs by exact ND.
  cbn [fst snd]. unfold E_ARG. split; [exact H1|]. cbn [Z.eqb]. tauto.
Qed.

(** owe()'s switch (0x14390-0x143b0): kind 11 (SYSEX) is the default 0x1483c, the others go through T3. *)
Lemma oweh_dispatch : forall e fuel, env_ok e -> (forall kind, 0 <= kind <= 11 -> owe_ok e kind fuel) ->
  forall (ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops : word)
         (k : kcall) (od : option desk) (c rem : Z) (tl : list byte) (m1 : word -> option byte),
    fuel_ok ops (S fuel) ->
    rec_ok k od -> (od = None -> k_kind k = 1 \/ k_kind k = 4 \/ k_kind k = 11) ->
    k_rc k = fst (enc_k k od) ->
    k_want_rc k = 0 -> k_want_len k = 0 -> k_want_key k = 0 -> k_want_display k = 0 ->
    cur_ok e c rem ->
    rw_cells rsegs m1 (bv_unsigned (e_sp e) + -400) (body_cells e k c rem tl) ->
    fr_ok e m1 ->
    evt rsegs (Qk e)
      (st e (body_regs e ra' t0' t1' t2' a0' (Z_to_bv 64 (k_kind k)) a2' a3' a4' a5' a6' a7' s5' ops s8'
                       (Z_to_bv 64 (k_desk k)) t3' t4' t5' t6')
          0x14390 m1).
Proof.
  intros e fuel HE OW ra' t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HREC HND HRC W0 W1 W2 W3 HC FR HFR.
  pose proof HREC as (Hk & _).
  pose proof HFR as (_ & _ & _ & _ & HMI).
  unfold st, body_regs.
  assert (Kc : k_kind k = 0 \/ k_kind k = 1 \/ k_kind k = 2 \/ k_kind k = 3 \/ k_kind k = 4 \/ k_kind k = 5 \/
               k_kind k = 6 \/ k_kind k = 7 \/ k_kind k = 8 \/ k_kind k = 9 \/ k_kind k = 10 \/ k_kind k = 11) by lia.
  destruct Kc as [K|[K|[K|[K|[K|[K|[K|[K|[K|[K|[K|K]]]]]]]]]]]; rewrite K.
  all: zstep; zstep.
  12: br_yes.
  1-11: br_not; do 7 zstep.
  all: lazymatch type of K with _ = ?j =>
         let O := fresh "O" in
         pose proof (OW j ltac:(lia)) as O; unfold owe_ok, st, body_regs in O;
         let v := eval vm_compute in (owe_pc j) in replace (owe_pc j) with v in O by reflexivity;
         eapply O; [ exact HF | exact HREC | exact K | intros HN; pose proof (HND HN); lia
                   | exact HRC | exact W0 | exact W1 | exact W2 | exact W3 | exact HC | exact FR | exact HFR ]
       end.
Qed.

(** 0x1435c lw a1, kind; ld s10, desk; sw a0, k.rc; bltu 11, a1 (never); needs_desk = bit kind of 0x812 is 0;
    want_rc = want_len = want_key = want_display = 0; NULL desk on a kind that needs one: E_ARG 0x14848 ->
    0x14804 want_rc = -1 -> CHK; else the switch. *)
Lemma codec_main_oweh : S_oweh.
Proof.
  unfold S_oweh. intros e fuel HE OW CH.
  pose proof (oweh_dispatch e fuel HE OW) as DSP.
  unfold join_ok, st, body_regs.
  intros ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s8' s10' t3' t4' t5' t6' ops k od c rem tl m1
         HF HREC HC FR HFR.
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _).
  destruct HFR as (SV & ST & MU & WM & HMI).
  unfold LLVM_CODEC_STACK in HLO, MU.
  pose proof ST as [Hlo0 _].
  pose proof HREC as (Hk & Hpd & Hr & Hbe & Hout).
  pose proof (pd_range _ _ _ Hpd) as [Hp Hd].
  pose proof (owe_k_code k od) as Cw. destruct (enc_agree k od HREC) as [EA _].
  assert (Hrc : - 2 ^ 31 <= fst (enc_k k od) < 2 ^ 31) by (rewrite EA; unfold code_ok in Cw; lia).
  clear Cw EA.
  apply flat_of_body in FR.
  zstep.
  rewrite ?(sx32_lit (k_kind k)) by lia.
  zstep. zstep. zstep. zstep.
  br_not.
  do 5 zstep.
  if_cases E2.
  - (* bit kind of 0x812 is 0: the kind needs a desk *)
    zify_cond E2.
    assert (ND : ~ (k_kind k = 1 \/ k_kind k = 4 \/ k_kind k = 11)).
    { intros HK. destruct HK as [HK|[HK|HK]]; rewrite HK in E2; compute in E2;
        first [ discriminate E2 | lia | exact (E2 eq_refl) | tauto ]. }
    do 4 zstep.
    if_cases E3.
    + zify_cond E3.
      to_body FR.
      lazymatch type of FR with rw_cells _ _ _ (body_cells _ ?K' _ _ _) =>
        eapply DSP with (k := K') (od := od) (c := c) (rem := rem) (tl := tl) end;
        [ exact HF | exact HREC | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
        | exact HC | exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) ].
      intros HN. exfalso. destruct Hpd as [(_ & Hd0 & _) | [(_ & _ & Ho) | (_ & _ & Ho)]];
        [ cbn [k_desk] in E3; lia | rewrite HN in Ho; discriminate Ho | rewrite HN in Ho; discriminate Ho ].
    + zify_cond E3.
      assert (Hod : od = None).
      { destruct Hpd as [(_ & _ & Ho) | [(_ & Hd0 & _) | (_ & Hd0 & _)]]; [exact Ho | lia | lia]. }
      do 4 zstep.
      try replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) in FR
        by (apply bv_eq; vm_compute; reflexivity).
      to_body FR.
      unfold chk_ok, st, body_regs in CH.
      lazymatch type of FR with rw_cells _ _ _ (body_cells _ ?K' _ _ _) =>
        eapply CH with (k := K') (od := od) (c := c) (rem := rem) (tl := tl) end;
        [ exact HF | exact HREC | reflexivity | | exact HC | exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) ].
      apply owe_want_earg; [ exact Hod | exact ND | reflexivity .. ].
  - (* bit kind of 0x812 is 1: BUTTON, JOG or SYSEX, no desk needed *)
    zify_cond E2.
    assert (D : k_kind k = 1 \/ k_kind k = 4 \/ k_kind k = 11).
    { assert (Kc : k_kind k = 0 \/ k_kind k = 1 \/ k_kind k = 2 \/ k_kind k = 3 \/ k_kind k = 4 \/ k_kind k = 5 \/
                   k_kind k = 6 \/ k_kind k = 7 \/ k_kind k = 8 \/ k_kind k = 9 \/ k_kind k = 10 \/ k_kind k = 11) by lia.
      destruct Kc as [HK|[HK|[HK|[HK|[HK|[HK|[HK|[HK|[HK|[HK|[HK|HK]]]]]]]]]]];
        first [ lia | (exfalso; rewrite HK in E2; compute in E2; first [ discriminate E2 | lia | exact (E2 eq_refl) ]) ]. }
    do 3 zstep.
    to_body FR.
    lazymatch type of FR with rw_cells _ _ _ (body_cells _ ?K' _ _ _) =>
      eapply DSP with (k := K') (od := od) (c := c) (rem := rem) (tl := tl) end;
      [ exact HF | exact HREC | intros _; exact D | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | exact HC | exact FR | exact (conj SV (conj ST (conj MU (conj WM HMI)))) ].
Qed.
