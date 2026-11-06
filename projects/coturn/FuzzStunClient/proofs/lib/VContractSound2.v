(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec Hoare ZStores RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import TolowerDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VGamma VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Section CS2.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variable CI : cimg.
  Hypothesis PO : params_ok SEGS P.

  Notation gammaP := (gamma SEGS P E mem0).
  Notation MCP := (MC SEGS P E mem0).

  (* [comment removed for export] *)
  Definition contract_post (c : contract) (tgt : Z) : Prop :=
    forall A spoff A1 v nu regs mem (ra : word),
      contract_apply P CI c A spoff = CROk A1 v ->
      gammaP A nu regs mem ->
      get_reg A 2 = Some (lsymc SP0 spoff) ->
      (contract_K c = 0 \/ in_ranges (vp_wstack P) (spoff - contract_K c) (contract_K c) = true) ->
      ret_ok ra -> getr regs 1%bv = ra ->
      exists regs' mem' nu',
           msteps SEGS (mkst regs (wordZ tgt) mem rom) (mkst regs' ra mem' rom)
        /\ gammaP (contract_frame c A1 spoff v) nu' regs' mem'
        /\ getr regs' 1%bv = ra
        /\ ext (vs_next A) nu nu' /\ (vs_next A <= vs_next (contract_frame c A1 spoff v))%positive
        /\ frame_mod mem mem' (unit_regions P E).

  Definition contract_dead (c : contract) : Prop :=
    forall A spoff nu regs mem,
      contract_apply P CI c A spoff = CRDead -> gammaP A nu regs mem -> False.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable a_tolower : Z.
  Hypothesis TOLOWER : forall regs mem (c : Z) (ret : word),
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = Z_to_bv 64 c -> 0 <= c <= 255 ->
    exists regs',
      msteps SEGS (mkst regs (wordZ a_tolower) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10%bv = Z_to_bv 64 (tolower_Z c)
      /\ regs_agree (fun r => In r tolower_clob) regs regs'.

  #[using="Type"] Lemma tolower_clob_CS : forallb (fun r : reg => existsb (Z.eqb (bv_unsigned r)) CALLER_SAVED) tolower_clob = true.
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma tolower_clob_ra : existsb (fun r : reg => Z.eqb (bv_unsigned r) 1) tolower_clob = false.
  Proof. reflexivity. Qed.

  #[using="PO TOLOWER"] Theorem tolower_post : contract_post C_tolower a_tolower.
  Proof.
    intros A spoff A1 v nu regs mem ra Happ HGm Hsp HK Hret Hra.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    cbn [contract_apply] in Happ. unfold c_tolower, getA in Happ.
    destruct (get_reg A A0r) as [e|] eqn:Eg; [|discriminate].
    destruct (dead_lin A e) eqn:Ed; [discriminate|].
    pose proof (bnd_sound A nu e HL) as Hb.
    destruct (bnd A e) as [[lo|] [hi|]]; try discriminate.
    destruct (Z.ltb_spec lo 0); [discriminate|]. destruct (Z.ltb_spec 255 hi); [discriminate|]. cbn [orb] in Happ.
    destruct Hb as [Hlo Hhi]; cbn [fst snd lo_le hi_ge] in Hlo, Hhi.
    set (c := eval nu e) in *.
    destruct (reg_val SEGS P E mem0 A nu regs mem 10%bv e HGm ltac:(vm_compute; lia) Eg) as [Hw Hbe].
    assert (H10 : getr regs 10%bv = Z_to_bv 64 c).
    { apply bv_eq. rewrite Hw, u_Z_to_bv64. reflexivity. }
    destruct (TOLOWER regs mem c ra Hret Hra H10 ltac:(lia)) as [regs' (RUN&R10&AG)].
    pose proof (tolower_Z_range c ltac:(lia)) as Htc.
    (* [comment removed for export] *)
    assert (RES : exists nu', aext A A1 nu nu' /\ lgamma A1 nu' /\
                  match v with Some e' => eval nu' e' = tolower_Z c /\ lin_below e' (vs_next A1) = true | None => False end).
    { destruct (lin_is_const e) eqn:Ec.
      - injection Happ as <- <-. exists nu. split; [apply aext_refl|]. split; [exact HL|].
        rewrite eval_lconst. split; [|apply lin_below_lconst]. unfold tolower_Z. rewrite <- (eval_is_const nu e Ec). reflexivity.
      - set (rlo := if 65 <=? lo then Z.min lo 97 else lo) in Happ. set (rhi := if 65 <=? hi then Z.max hi (Z.min (hi + 32) 122) else hi) in Happ.
        pose proof (afresh_sound A nu (Some rlo, Some rhi) (tolower_Z c) HL) as FR.
        destruct (afresh A (Some rlo, Some rhi)) as [v1 A1']. injection Happ as <- <-.
        apply FR. unfold rlo, rhi, tolower_Z. split; cbn [fst snd lo_le hi_ge].
        + destruct (Z.leb_spec 65 lo); destruct (65 <=? c) eqn:E1; destruct (c <=? 90) eqn:E2; cbn [andb];
            try apply Z.leb_le in E1; try apply Z.leb_gt in E1; try apply Z.leb_le in E2; try apply Z.leb_gt in E2; (ltac2:(LK.k [@Hlo; @H1; @E1; @E2]); lia).
        + destruct (Z.leb_spec 65 hi); destruct (65 <=? c) eqn:E1; destruct (c <=? 90) eqn:E2; cbn [andb];
            try apply Z.leb_le in E1; try apply Z.leb_gt in E1; try apply Z.leb_le in E2; try apply Z.leb_gt in E2; lia. }
    destruct RES as [nu' (X1&L1&V1)].
    exists regs', mem, nu'.
    pose proof (regs_agree_CS tolower_clob regs regs' tolower_clob_CS AG) as HKr.
    destruct (gamma_call_post SEGS P E mem0 rom PO A (contract_frame C_tolower A1 spoff v) nu nu' regs regs' mem mem []
                HGm (proj1 X1) ltac:(destruct (contract_frame_shape C_tolower A1 spoff v) as (_&_&_&_&F5&_); rewrite F5; exact (proj1 (proj2 X1)))
                ltac:(apply lgamma_contract_frame; [exact L1|destruct v; [exact (proj2 V1)|exact I]]))
      as [HG' FM'].
    - (* [comment removed for export] *)
      eapply (gamma_regs_contract_frame SEGS P E mem0 C_tolower A A1 spoff v nu nu' regs regs'); try eassumption.
      + right. split; [exact HR|destruct HB as (_&_&RB&_); exact RB].
      + exact (proj1 X1).
      + destruct X1 as (_&_&(SR&_)). exact SR.
      + destruct v as [e'|]; [|exact I]. rewrite R10, u_Z_to_bv64, (proj1 V1). reflexivity.
    - intros off w v0 Hin. destruct (contract_frame_shape C_tolower A1 spoff v) as (F1&_). rewrite F1 in Hin. cbn in Hin.
      destruct X1 as (_&_&(_&SS&_)). rewrite SS in Hin. left. split; [exact Hin|intros x _; exact I].
    - intros a w v0 Hin. destruct (contract_frame_shape C_tolower A1 spoff v) as (_&F2&_). rewrite F2 in Hin.
      destruct X1 as (_&_&(_&_&SG&_)). rewrite SG in Hin. split; [exact Hin|intros x _; exact I].
    - intros lo' hi' Hin. destruct (contract_frame_shape C_tolower A1 spoff v) as (_&_&F3&_). apply F3 in Hin as [Hin _].
      destruct X1 as (_&_&(_&_&_&SN&_)). rewrite SN in Hin. left. split; [exact Hin|intros x _; exact I].
    - apply frame_mod_refl.
    - intros x Hx. exfalso. apply Hx. exact I.
    - split; [exact RUN|]. split; [exact HG'|]. split; [rewrite (regs_agree_ra tolower_clob regs regs' tolower_clob_ra AG); exact Hra|].
      split; [exact (proj1 X1)|]. split; [|exact FM'].
      destruct (contract_frame_shape C_tolower A1 spoff v) as (_&_&_&_&F5&_). rewrite F5. exact (proj1 (proj2 X1)).
  Qed.

  #[using="Type"] Theorem tolower_dead : contract_dead C_tolower.
  Proof.
    intros A spoff nu regs mem Happ HGm. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    cbn [contract_apply] in Happ. unfold c_tolower, getA in Happ.
    destruct (get_reg A A0r) as [e|]; [|discriminate].
    destruct (dead_lin A e) eqn:Ed; [exact (dead_lin_false A nu e HL Ed)|].
    destruct (bnd A e) as [[lo|] [hi|]]; try discriminate. destruct (_ || _); [discriminate|].
    destruct (lin_is_const e); [discriminate|]. destruct (afresh A _); discriminate.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma keeps_CS regs regs' :
    keeps regs regs' -> forall r : reg, bv_unsigned r <> 0 -> ~ In (bv_unsigned r) CALLER_SAVED -> getr regs' r = getr regs r.
  Proof. intros K r Hr Hn. apply (keeps_getr _ _ r K). exact (not_caller_saved_kept r Hr Hn). Qed.

  #[using="Type"] Lemma keeps_ra regs regs' : keeps regs regs' -> getr regs' 1%bv = getr regs 1%bv.
  Proof. intros K. apply (keeps_getr _ _ 1%bv K). unfold callee_kept. cbn. left. reflexivity. Qed.

  #[using="Type"] Lemma keeps_a0 regs regs' : keeps regs regs' -> getr regs' 10%bv = getr regs 10%bv.
  Proof. intros K. apply (keeps_getr _ _ 10%bv K). unfold callee_kept. cbn. do 6 right. left. reflexivity. Qed.

  #[using="Type"] Lemma length_zeros k : length (zeros k) = k.
  Proof. apply repeat_length. Qed.

  #[using="Type"] Lemma nth_zeros k j : nth j (zeros k) (Z_to_bv 8 0) = Z_to_bv 8 0.
  Proof. unfold zeros. destruct (Nat.lt_ge_cases j k); [apply nth_repeat|rewrite nth_overflow; [reflexivity|rewrite repeat_length; lia]]. Qed.

  #[using="Type"] Lemma skipn_repeat' {A} (x : A) j : forall k, skipn j (repeat x k) = repeat x (k - j).
  Proof. induction j as [|j IH]; intros k; [cbn; rewrite Nat.sub_0_r; reflexivity|]. destruct k as [|k]; [reflexivity|]. cbn [repeat skipn]. rewrite IH. reflexivity. Qed.
  #[using="Type"] Lemma firstn_repeat' {A} (x : A) m : forall k, (m <= k)%nat -> firstn m (repeat x k) = repeat x m.
  Proof. induction m as [|m IH]; intros k Hk; [reflexivity|]. destruct k as [|k]; [lia|]. cbn [repeat firstn]. rewrite IH by lia. reflexivity. Qed.
  #[using="Type"] Lemma sub_zeros k j m : (j + m <= k)%nat -> sub (zeros k) j m = zeros m.
  Proof.
    intros H. unfold sub, zeros. rewrite skipn_repeat', firstn_repeat' by lia. reflexivity.
  Qed.

  #[using="Type"] Lemma bytes_le_zeros k : bytes_le_to_Z (zeros k) = 0.
  Proof. induction k as [|k IH]; [reflexivity|]. cbn [zeros repeat bytes_le_to_Z]. fold (zeros k). rewrite IH. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="PO"] Lemma stack_dst A nu regs mem de ne off lo hi :
    gammaP A nu regs mem -> 0 <= eval nu ne ->
    stack_range P A de ne true = RR_stack off lo hi ->
    let d := e_sp0 E + eval nu off in
    eval nu de = d /\ lo <= eval nu off /\ eval nu off + eval nu ne <= hi /\ - vp_frame P <= lo /\ hi <= 0 /\
    0 <= d /\ d + eval nu ne < 2 ^ 64 /\
    store_ok SEGS mem (wordZ d) (Z.to_nat (eval nu ne)) = true /\
    (exists r, In r (vp_wstack P) /\ fst r <= lo /\ hi <= snd r).
  Proof.
    intros HGm Hn Hs. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&_). pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&_).
    destruct (stack_range_sound P E A nu de ne true off lo hi HL HF Hs) as (_&Ed&H1&H2&H3&H4&Hw).
    specialize (Hw eq_refl). destruct (in_ranges_sound _ _ _ Hw) as [rlo [rhi (Hr&R1&R2)]].
    cbn zeta. split; [exact Ed|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
    - apply store_ok_bytes; [lia|lia|]. intros j Hj. apply (MC_frame_ok SEGS P E mem0 mem _ HM). lia.
    - exists (rlo, rhi). cbn [fst snd]. split; [exact Hr|lia].
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS mem0 PO"] Lemma stack_R_ok off lo hi len :
    - vp_frame P <= lo -> hi <= 0 -> lo <= off -> off + len <= hi ->
    (exists r, In r (vp_wstack P) /\ fst r <= lo /\ hi <= snd r) ->
    env_ok P E ->
    forall x, ~ outside x [(wordZ (e_sp0 E + off), len)] ->
      ~ outside x (unit_regions P E) /\ ~ outside x (footprint P E) /\
      forall plo phi, In (plo, phi) (vp_pristine P) -> ~ (plo <= bv_unsigned x < phi).
  Proof.
    intros Hlo Hhi H1 H2 [r (Hr&R1&R2)] HE x Hx.
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    cbn [outside] in Hx. unfold in_rng in Hx. rewrite u_wordZ in Hx by lia.
    assert (Hin : e_sp0 E + off <= bv_unsigned x < e_sp0 E + off + len) by (destruct (Z_le_gt_dec (e_sp0 E + off) (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) (e_sp0 E + off + len)); first [lia | exfalso; apply Hx; split; [lia|exact I]]).
    split; [|split].
    - unfold unit_regions. rewrite outside_app. intros [Hs _].
      destruct (PR _ Hr). clear -Hs Hr Hin R1 R2 H1 H2 H E1 E2 E12 P0 P1 H0.
      induction (vp_wstack P) as [|r0 t IH]; [destruct Hr|]. cbn [map outside] in Hs. destruct Hs as [Hs1 Hs2].
      destruct Hr as [->|Hr]; [|exact (IH Hr Hs2)]. apply Hs1. unfold in_rng. rewrite u_wordZ by lia. cbn [fst snd] in *. lia.
    - unfold footprint. cbn [outside]. intros [Hs _]. apply Hs. unfold in_rng. rewrite u_wordZ by lia. lia.
    - intros plo phi Hp. destruct (PP _ _ Hp). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable a_memset : Z.
  Hypothesis MEMSET : forall mem (d : word) (n : Z) regs (ret : word),
    0 <= n -> bv_unsigned d + n < 2 ^ 64 -> store_ok SEGS mem d (Z.to_nat n) = true ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = d -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (wordZ a_memset) mem rom) (mkst regs' ret (wbytes mem d (zeros (Z.to_nat n))) rom)
      /\ keeps regs regs'.

  #[using="Type"] Lemma zero_slots8_in sl o k x :
    In x (zero_slots8 sl o k) -> In x sl \/ exists i, (i < k)%nat /\ x = (o + 8 * Z.of_nat i, (8, Some (lconst 0))).
  Proof.
    revert sl o. induction k as [|k IH]; intros sl o Hin; cbn [zero_slots8] in Hin; [left; exact Hin|].
    destruct (IH _ _ Hin) as [H|[i [Hi ->]]].
    - apply cm_set_in in H as [->|H]; [right; exists 0%nat; split; [lia|f_equal; lia]|left; exact H].
    - right. exists (S i). split; [lia|]. f_equal. lia.
  Qed.

  #[using="Type"] Lemma zero_slots1_in sl o k x :
    In x (zero_slots1 sl o k) -> In x sl \/ exists i, (i < k)%nat /\ x = (o + Z.of_nat i, (1, Some (lconst 0))).
  Proof.
    revert sl o. induction k as [|k IH]; intros sl o Hin; cbn [zero_slots1] in Hin; [left; exact Hin|].
    destruct (IH _ _ Hin) as [H|[i [Hi ->]]].
    - apply cm_set_in in H as [->|H]; [right; exists 0%nat; split; [lia|f_equal; lia]|left; exact H].
    - right. exists (S i). split; [lia|]. f_equal. lia.
  Qed.

  #[using="PO MEMSET"] Theorem memset_post : contract_post C_memset a_memset.
  Proof.
    intros A spoff A1 v nu regs mem ra Happ HGm Hsp HKw Hret Hra.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&_).
    cbn [contract_apply] in Happ. unfold c_memset, getA in Happ.
    destruct (nonneg_len A (get_reg A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate.
    destruct (nonneg_len_sound A nu _ _ _ _ HL En) as [ne (Ene&Hn0&Hn1&Hn2)]. rewrite Ene in Happ. cbn [lin_of] in Happ.
    destruct (get_reg A A0r) as [de|] eqn:Ede; [|discriminate].
    destruct (stack_range P A de ne true) as [off lo hi| | | |msg] eqn:Esr; try discriminate.
    destruct (is_zero_val A (get_reg A A1r)) eqn:Ez; [|discriminate]. cbn [negb] in Happ.
    destruct (stack_dst A nu regs mem de ne off lo hi HGm ltac:(lia) Esr) as (Ed&H1&H2&H3&H4&Hd0&Hdn&Hok&Hws).
    set (n := eval nu ne) in *. set (ov := eval nu off) in *. set (d := e_sp0 E + ov) in *.
    (* [comment removed for export] *)
    assert (R10 : getr regs 10%bv = wordZ d).
    { apply (reg_word SEGS P E mem0 A nu regs mem 10%bv de d HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn]); lia)|exact Ede|exact Ed|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn]); lia)]. }
    assert (R12 : getr regs 12%bv = Z_to_bv 64 n).
    { apply (reg_word SEGS P E mem0 A nu regs mem 12%bv ne n HGm); [vm_compute; lia|exact Ene|reflexivity|lia]. }
    assert (R11 : getr regs 11%bv = Z_to_bv 64 0).
    { pose proof (gamma_get_reg SEGS P E mem0 A nu regs mem 11%bv HGm) as [W11 _]. change (rz 11%bv) with A1r in W11.
      destruct (get_reg A A1r) as [ce|] eqn:Ec; [|cbn in Ez; discriminate].
      apply bv_eq. rewrite u_Z_to_bv64. change (zwrap 64 0) with 0.
      apply (is_zero_val_sound mem0 A nu (Some ce) (getr regs 11%bv) HL Ez). exact (proj2 W11). }
    destruct (MEMSET mem (wordZ d) n regs ra ltac:(lia) ltac:(rewrite u_wordZ; lia) Hok Hret Hra R10 R11 R12) as [regs' [RUN K]].
    set (mem' := wbytes mem (wordZ d) (zeros (Z.to_nat n))) in *.
    assert (FM : frame_mod mem mem' [(wordZ d, n)]).
    { unfold mem'. replace n with (Z.of_nat (length (zeros (Z.to_nat n)))) at 2 by (rewrite length_zeros; lia).
      apply frame_mod_wbytes. rewrite length_zeros, u_wordZ; lia. }
    (* [comment removed for export] *)
    assert (RD : rdn SEGS mem' (wordZ d) (Z.to_nat n) = Some (zeros (Z.to_nat n))).
    { unfold mem'. rewrite <- (length_zeros (Z.to_nat n)) at 2. apply rdn_wbytes_hit. rewrite length_zeros, u_wordZ; lia. }
    assert (RD1 : forall j, 0 <= j < n -> rdn SEGS mem' (wordZ (d + j)) 1 = Some [Z_to_bv 8 0]).
    { intros j Hj. unfold mem'. replace j with (Z.of_nat (Z.to_nat j)) by lia.
      rewrite (rdn_wbytes_byte SEGS mem d (zeros (Z.to_nat n)) (Z.to_nat j)); rewrite ?length_zeros; try (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hd0; @Hj; @Hdn]); lia).
      rewrite nth_zeros. reflexivity. }
    (* [comment removed for export] *)
    set (A1b := set_slots A (cm_kill (vs_slots A) lo hi)) in *.
    assert (CASES : (A1 = A1b /\ v = Some de) \/
                    (lin_is_const off = true /\ lin_is_const ne = true /\ v = Some de /\
                     let o := lc off in let k := lc ne in let q := Z.to_nat (k / 8) in let r := Z.to_nat (k mod 8) in
                     let A2 := set_slots A1b (zero_slots1 (zero_slots8 (vs_slots A1b) o q) (o + 8 * Z.of_nat q) r) in
                     A1 = (if 0 <? k then add_nul (add_nul A2 o o) (o + k - 1) (o + k - 1) else A2))).
    { destruct (lin_is_const off && lin_is_const ne && (lc ne <=? MEMSET_TRACK_MAX)) eqn:Ec.
      - apply andb_prop in Ec as [Ec _]. apply andb_prop in Ec as [Ec1 Ec2]. right. injection Happ as <- <-. auto.
      - left. injection Happ as <- <-. auto. }
    assert (LG : lgamma A1 nu /\ vs_next A1 = vs_next A /\ vs_regs A1 = vs_regs A /\ vs_globs A1 = vs_globs A /\
                 (forall x, In x (vs_slots A1) -> In x (cm_kill (vs_slots A) lo hi) \/
                     exists o w, x = (o, (w, Some (lconst 0))) /\ ov <= o /\ o + w <= ov + n /\ 0 < w) /\
                 (forall f, In f (vs_nul A1) -> In f (vs_nul A) \/ (0 < n /\ (f = (ov, ov) \/ f = (ov + n - 1, ov + n - 1))))).
    { destruct HL as (LS&LC&LM&LV&(B0&B1&B2&B3&B4&B5)).
      destruct CASES as [[-> _]|(Co&Cn&_&EA1)].
      - unfold A1b. split; [|cbn; repeat split; auto]. split; [exact LS|]. split; [exact LC|]. split; [exact LM|]. split; [exact LV|].
        split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [intros k w e Hin; apply cm_kill_sub in Hin; exact (B3 _ _ _ Hin)|]. split; [exact B4|exact B5].
      - pose proof (eval_is_const nu off Co) as Eo. pose proof (eval_is_const nu ne Cn) as Ek.
        assert (Eo' : lc off = ov) by (unfold ov; rewrite Eo; reflexivity). assert (Ek' : lc ne = n) by (unfold n; rewrite Ek; reflexivity).
        rewrite Eo', Ek' in EA1. cbn zeta in EA1.
        set (q := Z.to_nat (n / 8)) in EA1. set (r := Z.to_nat (n mod 8)) in EA1.
        set (sl := zero_slots1 (zero_slots8 (vs_slots A1b) ov q) (ov + 8 * Z.of_nat q) r) in EA1.
        set (A2 := set_slots A1b sl) in EA1.
        pose proof (Z.div_mod n 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hmb.
        assert (Hq : 8 * Z.of_nat q <= n) by (unfold q; rewrite Z2Nat.id by (apply Z.div_pos; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hn0; @Hn1; @E1; @E12; @P0; @Ek'; @Hmb]); lia)); (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hn0; @Hn1; @E1; @E12; @P0; @Ek'; @Hmb]); nia)).
        assert (Hr : 8 * Z.of_nat q + Z.of_nat r = n) by (unfold q, r; rewrite !Z2Nat.id by (try apply Z.div_pos; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hn0; @Hn1; @Hmb; @E1; @E12; @P0; @H2; @H4; @Hd0; @Hdm; @Hq]); lia)); (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hn0; @Hn1; @Hmb; @E1; @E12; @P0; @H2; @H4; @Hd0; @Hdm; @Hq]); lia)).
        assert (SL : forall x, In x sl -> In x (cm_kill (vs_slots A) lo hi) \/ exists o w, x = (o, (w, Some (lconst 0))) /\ ov <= o /\ o + w <= ov + n /\ 0 < w).
        { intros x Hx. unfold sl in Hx. apply zero_slots1_in in Hx as [Hx|[i [Hi ->]]].
          - apply zero_slots8_in in Hx as [Hx|[i [Hi ->]]]; [left; exact Hx|]. right. eexists _, _. split; [reflexivity|]. lia.
          - right. eexists _, _. split; [reflexivity|]. (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hr; @Hi]); lia). }
        assert (EA2 : exists l, A1 = set_nul A2 l /\ forall f, In f l -> In f (vs_nul A) \/ (0 < n /\ (f = (ov, ov) \/ f = (ov + n - 1, ov + n - 1)))).
        { destruct (Z.ltb_spec 0 n).
          - destruct (add_nul_eq A2 ov ov) as [l1 [EN1 Hl1]].
            destruct (add_nul_eq (set_nul A2 l1) (ov + n - 1) (ov + n - 1)) as [l2 [EN2 Hl2]].
            exists l2. rewrite EA1, EN1, EN2. split; [reflexivity|]. intros f Hf.
            destruct (Hl2 f Hf) as [->|Hf1]; [right; auto|]. cbn in Hf1. destruct (Hl1 f Hf1) as [->|Hf0]; [right; auto|left; exact Hf0].
          - exists (vs_nul A). rewrite EA1. split; [destruct A; reflexivity|]. intros f Hf; left; exact Hf. }
        destruct EA2 as [l [-> Hl]]. cbn. split; [|repeat split; auto].
        split; [exact LS|]. split; [exact LC|]. split; [exact LM|]. split; [exact LV|].
        split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [|split; [exact B4|exact B5]].
        intros k w e Hin. destruct (SL _ Hin) as [Hin'|[o [w' [X _]]]]; [apply cm_kill_sub in Hin'; exact (B3 _ _ _ Hin')|].
        injection X as X1 X2 X3. subst. apply lin_below_lconst. }
    destruct LG as (L1&N1&RG1&G1&SL1&NL1).
    assert (Hv : v = Some de) by (destruct CASES as [[_ X]|(_&_&X&_)]; exact X).
    exists regs', mem', nu.
    destruct (gamma_call_post SEGS P E mem0 rom PO A (contract_frame C_memset A1 spoff v) nu nu regs regs' mem mem' [(wordZ d, n)]
                HGm (ext_refl _ _) ltac:(destruct (contract_frame_shape C_memset A1 spoff v) as (_&_&_&_&F5&_); rewrite F5, N1; lia)
                ltac:(apply lgamma_contract_frame; [exact L1|rewrite Hv; cbn; rewrite N1; exact (proj2 (reg_val SEGS P E mem0 A nu regs mem 10%bv de HGm ltac:(vm_compute; lia) Ede))]))
      as [HG' FM'].
    - eapply (gamma_regs_contract_frame SEGS P E mem0 C_memset A A1 spoff v nu nu regs regs'); try eassumption.
      + right. split; [exact HR|destruct HB as (_&_&RB&_); exact RB].
      + apply ext_refl.
      + exact (keeps_CS regs regs' K).
      + rewrite Hv. rewrite (keeps_a0 _ _ K), R10, u_wordZ, Ed by lia. symmetry. apply zwrap_id. lia.
    - intros off' w' v' Hin. destruct (contract_frame_shape C_memset A1 spoff v) as (F1&_). rewrite F1 in Hin. cbn in Hin.
      destruct (SL1 _ Hin) as [Hk|[o [w'' [X (Q1&Q2&Q3)]]]].
      + left. split; [eapply cm_kill_sub; exact Hk|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hk) as D.
        destruct (HSl _ _ _ (cm_kill_sub _ _ _ _ Hk)) as [(Ra&Rb&Rc) _].
        intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u_wordZ by lia. unfold d. lia.
      + injection X as X1 X2 X3. subst off' w' v'. right. split; [unfold ov, n in *; lia|]. cbn [cell_holds].
        exists (zeros (Z.to_nat w'')). split.
        * replace (e_sp0 E + o) with (d + (o - ov)) by (unfold d; lia).
          pose proof (rdn_sub SEGS mem' (Z.to_nat n) (wordZ d) (zeros (Z.to_nat n)) (Z.to_nat (o - ov)) (Z.to_nat w'') RD ltac:(lia)) as X.
          rewrite sub_zeros in X by lia. unfold at_ in X. rewrite u_wordZ, Z2Nat.id in X by lia. exact X.
        * rewrite bytes_le_zeros, eval_lconst. reflexivity.
    - intros a w' v' Hin. destruct (contract_frame_shape C_memset A1 spoff v) as (_&F2&_). rewrite F2, G1 in Hin.
      split; [exact Hin|]. destruct (HG _ _ _ Hin) as [(Ra&Rb&Rc) _]. 
      intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u_wordZ by lia. unfold d. lia.
    - intros mlo mhi Hin. destruct (contract_frame_shape C_memset A1 spoff v) as (_&_&F3&_). apply F3 in Hin as [Hin _].
      destruct (NL1 _ Hin) as [Hold|[Hnp [Ef|Ef]]]; [|injection Ef as Ef1 Ef2; subst mlo mhi|injection Ef as Ef1 Ef2; subst mlo mhi].
      + (* [comment removed for export] *)
        destruct (HN _ _ Hold) as [z [b (Q1&Q2&Q3&Q4)]]. right.
        assert (UNCH : z < ov \/ ov + n <= z -> rdn SEGS mem' (wordZ (e_sp0 E + z)) 1 = Some [b]).
        { intros Hz. rewrite <- Q3. apply (rdn_unchanged SEGS mem0 rom mem mem' [(wordZ d, n)] (e_sp0 E + z) 1 (proj1 FM)); [lia|lia|].
          intros x Hx. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite !u_wordZ by lia. unfold d. lia. }
        destruct (Z_lt_le_dec z ov) as [Hz|Hz]; [|destruct (Z_lt_le_dec z (ov + n)) as [Hz'|Hz']].
        * exists z, b. split; [exact Q1|]. split; [exact Q2|]. split; [apply UNCH; lia|exact Q4].
        * exists z, (Z_to_bv 8 0). split; [exact Q1|]. split; [exact Q2|]. split; [|reflexivity].
          replace (e_sp0 E + z) with (d + (z - ov)) by (unfold d; lia). apply RD1. lia.
        * exists z, b. split; [exact Q1|]. split; [exact Q2|]. split; [apply UNCH; lia|exact Q4].
      + right. exists ov, (Z_to_bv 8 0). split; [lia|]. split; [unfold ov, n in *; lia|]. split; [|reflexivity].
        replace (e_sp0 E + ov) with (d + 0) by (unfold d; lia). apply RD1. lia.
      + right. exists (ov + n - 1), (Z_to_bv 8 0). split; [lia|]. split; [unfold ov, n in *; lia|]. split; [|reflexivity].
        replace (e_sp0 E + (ov + n - 1)) with (d + (n - 1)) by (unfold d; lia). apply RD1. lia.
    - exact FM.
    - apply (stack_R_ok ov lo hi n); auto; lia.
    - split; [exact RUN|]. split; [exact HG'|]. split; [rewrite (keeps_ra _ _ K); exact Hra|].
      split; [apply ext_refl|]. split; [|exact FM'].
      destruct (contract_frame_shape C_memset A1 spoff v) as (_&_&_&_&F5&_). rewrite F5, N1. lia.
  Qed.

  #[using="Type"] Theorem memset_dead : contract_dead C_memset.
  Proof.
    intros A spoff nu regs mem Happ HGm. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    cbn [contract_apply] in Happ. unfold c_memset, getA in Happ.
    destruct (nonneg_len A (get_reg A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate; [|exact (nonneg_len_dead A nu _ _ HL En)].
    destruct (get_reg A A0r) as [de|]; [|discriminate].
    destruct (stack_range P A de _ true) as [off lo hi| | | |msg] eqn:Esr; try discriminate; [|exact (stack_range_dead P A nu _ _ true HL Esr)].
    destruct (negb _); [discriminate|]. destruct (lin_is_const off && _ && _); discriminate.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variable a_memcpy : Z.
  Hypothesis MEMCPY : forall mem (dst src : word) (n : Z) regs (ret : word),
    0 <= n < 2 ^ 64 ->
    (forall i, 0 <= i < n -> exists b, rdn SEGS mem (at_ src i) 1 = Some [b]) ->
    store_ok SEGS mem dst (Z.to_nat n) = true ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs' (bs' : list byte),
      length bs' = Z.to_nat n
      /\ msteps SEGS (mkst regs (wordZ a_memcpy) mem rom) (mkst regs' ret (wbytes mem dst bs') rom)
      /\ keeps regs regs'.

  #[using="Type"] Lemma readable_range_cases A base n :
    match readable_range P A base n with RR_stack _ _ _ | RR_data _ | RR_img _ _ => true | _ => false end = true \/
    readable_range P A base n = RR_dead \/ exists m, readable_range P A base n = RR_fail m.
  Proof. destruct (readable_range P A base n); eauto. Qed.

  #[using="PO MEMCPY"] Theorem memcpy_post : contract_post C_memcpy a_memcpy.
  Proof.
    intros A spoff A1 v nu regs mem ra Happ HGm Hsp HKw Hret Hra.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&_).
    cbn [contract_apply] in Happ. unfold c_memcpy, getA in Happ.
    destruct (nonneg_len A (get_reg A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate.
    destruct (nonneg_len_sound A nu _ _ _ _ HL En) as [ne (Ene&Hn0&Hn1&Hn2)]. rewrite Ene in Happ. cbn [lin_of] in Happ.
    destruct (get_reg A A0r) as [de|] eqn:Ede; [|discriminate].
    destruct (get_reg A A1r) as [se|] eqn:Ese; [|discriminate].
    destruct (stack_range P A de ne true) as [off lo hi| | | |msg] eqn:Esr; try discriminate.
    pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem se ne _ HGm ltac:(lia) eq_refl) as RS.
    destruct (readable_range P A se ne) as [so slo shi|soff|ilo ihi| |msg] eqn:Err; try discriminate; try (destruct RS; fail);
      injection Happ as <- <-.
    all: destruct (stack_dst A nu regs mem de ne off lo hi HGm ltac:(lia) Esr) as (Ed&H1&H2&H3&H4&Hd0&Hdn&Hok&Hws).
    all: set (n := eval nu ne) in *; set (ov := eval nu off) in *; set (d := e_sp0 E + ov) in *.
    all: destruct RS as (S0&S1&SB).
    all: assert (R10 : getr regs 10%bv = wordZ d) by (apply (reg_word SEGS P E mem0 A nu regs mem 10%bv de d HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn]); lia)|exact Ede|exact Ed|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn]); lia)]).
    all: assert (R11 : getr regs 11%bv = wordZ (eval nu se)) by (apply (reg_word SEGS P E mem0 A nu regs mem 11%bv se _ HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E4; @E5; @Hn0; @Hn1; @S0; @S1]); lia)|exact Ese|reflexivity|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E4; @E5; @Hn0; @Hn1; @S0; @S1]); lia)]).
    all: assert (R12 : getr regs 12%bv = Z_to_bv 64 n) by (apply (reg_word SEGS P E mem0 A nu regs mem 12%bv ne n HGm); [vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E2; @E4; @E5; @P1; @Hn0; @Hn1; @H2; @H4; @Hd0]); lia)|exact Ene|reflexivity|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @E2; @E4; @E5; @P1; @Hn0; @Hn1; @H2; @H4; @Hd0]); lia)]).
    all: assert (SRC : forall i, 0 <= i < n -> exists b, rdn SEGS mem (at_ (wordZ (eval nu se)) i) 1 = Some [b])
      by (intros i Hi; unfold at_; rewrite u_wordZ by lia; exact (SB i Hi)).
    all: destruct (MEMCPY mem (wordZ d) (wordZ (eval nu se)) n regs ra ltac:((ltac2:(LK.k [@E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P1; @Hn0; @Hn1; @H2; @H4; @Hd0; @S1; @S0; @Hdn]); lia)) SRC Hok ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P1; @Hn0; @Hn1; @H2; @H4; @Hd0; @S1; @S0; @Hdn]); lia)) ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @P1; @Hn0; @Hn1; @H2; @H4; @Hd0; @S1; @S0; @Hdn]); lia)) Hret Hra R10 R11 R12)
      as [regs' [bs (Hlen&RUN&K)]].
    all: set (mem' := wbytes mem (wordZ d) bs) in *.
    all: assert (FM : frame_mod mem mem' [(wordZ d, n)]) by (unfold mem'; replace n with (Z.of_nat (length bs)) by (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hn0; @Hn1; @Hlen; @Hdn; @Hd0]); lia); apply frame_mod_wbytes; rewrite u_wordZ; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hn0; @Hn1; @Hlen; @Hdn; @Hd0]); lia)).
    all: destruct (kill_nul_eq (set_slots A (cm_kill (vs_slots A) lo hi)) lo (hi - 1) None) as [nl [EK Hnl]]; rewrite EK.
    all: set (A1 := set_nul (set_slots A (cm_kill (vs_slots A) lo hi)) nl).
    all: assert (L1 : lgamma A1 nu) by (destruct HL as (LS&LC&LM&LV&(B0&B1&B2&B3&B4&B5)); split; [exact LS|]; split; [exact LC|]; split; [exact LM|]; split; [exact LV|];
           split; [exact B0|]; split; [exact B1|]; split; [exact B2|]; split; [intros k w e Hin; apply cm_kill_sub in Hin; exact (B3 _ _ _ Hin)|]; split; [exact B4|exact B5]).
    all: exists regs', mem', nu.
    all: destruct (gamma_call_post SEGS P E mem0 rom PO A (contract_frame C_memcpy A1 spoff (Some de)) nu nu regs regs' mem mem' [(wordZ d, n)]
                HGm (ext_refl _ _) ltac:(destruct (contract_frame_shape C_memcpy A1 spoff (Some de)) as (_&_&_&_&F5&_); rewrite F5; cbn; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia))
                ltac:(apply lgamma_contract_frame; [exact L1|cbn; exact (proj2 (reg_val SEGS P E mem0 A nu regs mem 10%bv de HGm ltac:(vm_compute; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia)) Ede))]))
      as [HG' FM'];
      [ eapply (gamma_regs_contract_frame SEGS P E mem0 C_memcpy A A1 spoff (Some de) nu nu regs regs'); try eassumption;
        [ right; split; [exact HR|destruct HB as (_&_&RB&_); exact RB] | apply ext_refl | reflexivity | exact (keeps_CS regs regs' K)
        | rewrite (keeps_a0 _ _ K), R10, u_wordZ, Ed by (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia); symmetry; apply zwrap_id; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia) ]
      | intros off' w' v' Hin; destruct (contract_frame_shape C_memcpy A1 spoff (Some de)) as (F1&_); rewrite F1 in Hin; cbn in Hin;
        left; split; [eapply cm_kill_sub; exact Hin|]; pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as D;
        destruct (HSl _ _ _ (cm_kill_sub _ _ _ _ Hin)) as [(Ra&Rb&Rc) _];
        intros x Hx; cbn [outside]; split; [|exact I]; unfold in_rng; rewrite !u_wordZ by (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia); unfold d; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia)
      | intros ga gw gv Hin; destruct (contract_frame_shape C_memcpy A1 spoff (Some de)) as (_&F2&_); rewrite F2 in Hin; cbn in Hin;
        split; [exact Hin|]; destruct (HG _ _ _ Hin) as [(Ra&Rb&Rc) _];
        intros x Hx; cbn [outside]; split; [|exact I]; unfold in_rng; rewrite !u_wordZ by (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia); unfold d; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia)
      | intros mlo mhi Hin; destruct (contract_frame_shape C_memcpy A1 spoff (Some de)) as (_&_&F3&_); apply F3 in Hin as [Hin _]; cbn in Hin;
        destruct (Hnl _ Hin) as [Hold [X|X]]; [cbn in X; discriminate|]; cbn in Hold, X;
        destruct (HN _ _ Hold) as [z [b (Q1&Q2&Q3&Q4)]]; right; exists z, b;
        split; [exact Q1|]; split; [exact Q2|]; split; [|exact Q4];
        rewrite <- Q3; apply (rdn_unchanged SEGS mem0 rom mem mem' [(wordZ d, n)] (e_sp0 E + z) 1 (proj1 FM)); [(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia)|(ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia)|];
        intros x Hx; cbn [outside]; split; [|exact I]; unfold in_rng; rewrite !u_wordZ by (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia); unfold d; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia)
      | exact FM
      | apply (stack_R_ok ov lo hi n); auto; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia)
      | split; [exact RUN|]; split; [exact HG'|]; split; [rewrite (keeps_ra _ _ K); exact Hra|];
        split; [apply ext_refl|]; split; [|exact FM'];
        destruct (contract_frame_shape C_memcpy A1 spoff (Some de)) as (_&_&_&_&F5&_); rewrite F5; cbn; (ltac2:(LK.k [@E3; @E7; @E8; @E9; @E11; @Hlen; @F5; @E4; @E5; @Hn0; @Hn1; @Hd0; @Hdn; @E2; @P1; @H2; @H4; @Rc; @Hx; @E12; @Ra; @H1; @D; @P0; @H3; @Q1; @Q2; @X]); lia) ].
  Qed.

  #[using="PO"] Theorem memcpy_dead : contract_dead C_memcpy.
  Proof.
    intros A spoff nu regs mem Happ HGm. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    cbn [contract_apply] in Happ. unfold c_memcpy, getA in Happ.
    destruct (nonneg_len A (get_reg A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate; [|exact (nonneg_len_dead A nu _ _ HL En)].
    destruct (nonneg_len_sound A nu _ _ _ _ HL En) as [ne (Ene&Hn0&Hn1&Hn2)]. rewrite Ene in Happ. cbn [lin_of] in Happ.
    destruct (get_reg A A0r) as [de|]; [|discriminate]. destruct (get_reg A A1r) as [se|]; [|discriminate].
    destruct (stack_range P A de ne true) as [off lo hi| | | |msg] eqn:Esr; try discriminate; [|exact (stack_range_dead P A nu _ _ true HL Esr)].
    pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem se ne _ HGm ltac:(lia) eq_refl) as RS.
    destruct (readable_range P A se ne); try discriminate. exact RS.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition cmp_spec (a : Z) : Prop :=
    forall mem (l r : word) (n : nat) (la lb : list byte) regs (ret : word),
      rdn SEGS mem l n = Some la -> rdn SEGS mem r n = Some lb ->
      Z.of_nat n < 2 ^ 64 -> bv_unsigned l + Z.of_nat n < 2 ^ 64 -> bv_unsigned r + Z.of_nat n < 2 ^ 64 ->
      ret_ok ret -> getr regs 1%bv = ret ->
      getr regs 10%bv = l -> getr regs 11%bv = r -> getr regs 12%bv = Z_to_bv 64 (Z.of_nat n) ->
      exists regs' (dlt : Z),
        msteps SEGS (mkst regs (wordZ a) mem rom) (mkst regs' ret mem rom)
        /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
        /\ getr regs' 1%bv = getr regs 1%bv
        /\ - 255 <= dlt <= 255 /\ getr regs' 10%bv = Z_to_bv 64 dlt.

  #[using="PO"] Lemma memcmp_post_gen c a :
    (forall A spoff, contract_apply P CI c A spoff = c_memcmp P A) -> contract_K c = 0 ->
    cmp_spec a -> contract_post c a.
  Proof.
    intros Ec HK0 CMP A spoff A1 v nu regs mem ra Happ HGm Hsp HKw Hret Hra. rewrite Ec in Happ.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&_).
    unfold c_memcmp, getA in Happ.
    destruct (nonneg_len A (get_reg A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate.
    destruct (nonneg_len_sound A nu _ _ _ _ HL En) as [ne (Ene&Hn0&Hn1&Hn2)]. rewrite Ene in Happ. cbn [lin_of] in Happ.
    destruct (get_reg A A0r) as [ae|] eqn:Eae; [|discriminate]. destruct (get_reg A A1r) as [be|] eqn:Ebe; [|discriminate].
    pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem ae ne _ HGm ltac:(lia) eq_refl) as RA.
    pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem be ne _ HGm ltac:(lia) eq_refl) as RB.
    set (n := eval nu ne) in *.
    assert (MAIN : readable SEGS mem (eval nu ae) n -> readable SEGS mem (eval nu be) n ->
              (let '(v0, A1') := afresh A (Some (-255), Some 255) in CROk A1' v0) = CROk A1 v ->
              exists regs' mem' nu',
                msteps SEGS (mkst regs (wordZ a) mem rom) (mkst regs' ra mem' rom) /\
                gammaP (contract_frame c A1 spoff v) nu' regs' mem' /\ getr regs' 1%bv = ra /\
                ext (vs_next A) nu nu' /\ (vs_next A <= vs_next (contract_frame c A1 spoff v))%positive /\
                frame_mod mem mem' (unit_regions P E)).
    { intros RA' RB' EQ.
      destruct (readable_rdn SEGS mem _ _ RA' ltac:(lia)) as [la [Hla Lla]].
      destruct (readable_rdn SEGS mem _ _ RB' ltac:(lia)) as [lb [Hlb Llb]].
      destruct RA' as (A0'&A1'&_). destruct RB' as (B0'&B1'&_).
      assert (R10 : getr regs 10%bv = wordZ (eval nu ae)) by (apply (reg_word SEGS P E mem0 A nu regs mem 10%bv ae _ HGm); [vm_compute; lia|exact Eae|reflexivity|lia]).
      assert (R11 : getr regs 11%bv = wordZ (eval nu be)) by (apply (reg_word SEGS P E mem0 A nu regs mem 11%bv be _ HGm); [vm_compute; lia|exact Ebe|reflexivity|lia]).
      assert (R12 : getr regs 12%bv = Z_to_bv 64 (Z.of_nat (Z.to_nat n))).
      { rewrite Z2Nat.id by lia. apply (reg_word SEGS P E mem0 A nu regs mem 12%bv ne n HGm); [vm_compute; lia|exact Ene|reflexivity|lia]. }
      destruct (CMP mem (wordZ (eval nu ae)) (wordZ (eval nu be)) (Z.to_nat n) la lb regs ra Hla Hlb ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @A0'; @A1'; @Lla; @Llb; @Hn0; @Hn1; @B1'; @B0']); lia))
                  ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @A0'; @A1'; @Lla; @Llb; @Hn0; @Hn1; @B1'; @B0']); lia)) ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @A0'; @A1'; @Lla; @Llb; @Hn0; @Hn1; @B1'; @B0']); lia)) Hret Hra R10 R11 R12) as [regs' [dlt (RUN&HKr&Hra'&Hd&R10')]].
      pose proof (afresh_sound A nu (Some (-255), Some 255) dlt HL ltac:(split; cbn; lia)) as FR.
      destruct (afresh A (Some (-255), Some 255)) as [v1 A1x]. injection EQ as EA Ev. subst A1 v.
      destruct FR as [nu' (X1&L1&V1)]. destruct v1 as [e1|]; [|destruct V1]. destruct V1 as [V1 B1].
      exists regs', mem, nu'.
      destruct (gamma_call_post SEGS P E mem0 rom PO A (contract_frame c A1x spoff (Some e1)) nu nu' regs regs' mem mem []
                  HGm (proj1 X1) ltac:(destruct (contract_frame_shape c A1x spoff (Some e1)) as (_&_&_&_&F5&_); rewrite F5; exact (proj1 (proj2 X1)))
                  ltac:(apply lgamma_contract_frame; [exact L1|exact B1]))
        as [HG' FM'].
      - eapply (gamma_regs_contract_frame SEGS P E mem0 c A A1x spoff (Some e1) nu nu' regs regs'); try eassumption.
        + right. split; [exact HR|destruct HB as (_&_&RBl&_); exact RBl].
        + exact (proj1 X1).
        + destruct X1 as (_&_&(SR&_)). exact SR.
        + rewrite R10', u_Z_to_bv64, V1. reflexivity.
      - intros off w v0 Hin. destruct (contract_frame_shape c A1x spoff (Some e1)) as (F1&_). rewrite F1, HK0 in Hin. cbn in Hin.
        destruct X1 as (_&_&(_&SS&_)). rewrite SS in Hin. left. split; [exact Hin|intros x _; exact I].
      - intros ga w v0 Hin. destruct (contract_frame_shape c A1x spoff (Some e1)) as (_&F2&_). rewrite F2 in Hin.
        destruct X1 as (_&_&(_&_&SG&_)). rewrite SG in Hin. split; [exact Hin|intros x _; exact I].
      - intros lo' hi' Hin. destruct (contract_frame_shape c A1x spoff (Some e1)) as (_&_&F3&_). apply F3 in Hin as [Hin _].
        destruct X1 as (_&_&(_&_&_&SN&_)). rewrite SN in Hin. left. split; [exact Hin|intros x _; exact I].
      - apply frame_mod_refl.
      - intros x Hx. exfalso. apply Hx. exact I.
      - split; [exact RUN|]. split; [exact HG'|]. split; [rewrite Hra'; exact Hra|].
        split; [exact (proj1 X1)|]. split; [|exact FM'].
        destruct (contract_frame_shape c A1x spoff (Some e1)) as (_&_&_&_&F5&_). rewrite F5. exact (proj1 (proj2 X1)). }
    destruct (readable_range P A ae ne); try discriminate; try (destruct RA; fail);
    destruct (readable_range P A be ne); try discriminate; try (destruct RB; fail); exact (MAIN RA RB Happ).
  Qed.

  #[using="PO"] Lemma memcmp_dead_gen c : (forall A spoff, contract_apply P CI c A spoff = c_memcmp P A) -> contract_dead c.
  Proof.
    intros Ec A spoff nu regs mem Happ HGm. rewrite Ec in Happ. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    unfold c_memcmp, getA in Happ.
    destruct (nonneg_len A (get_reg A A2r) MAXLEN) as [nlo nhi| |msg] eqn:En; try discriminate; [|exact (nonneg_len_dead A nu _ _ HL En)].
    destruct (nonneg_len_sound A nu _ _ _ _ HL En) as [ne (Ene&Hn0&Hn1&Hn2)]. rewrite Ene in Happ. cbn [lin_of] in Happ.
    destruct (get_reg A A0r) as [ae|]; [|discriminate]. destruct (get_reg A A1r) as [be|]; [|discriminate].
    pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem ae ne _ HGm ltac:(lia) eq_refl) as RA.
    pose proof (readable_range_sound SEGS P E mem0 PO A nu regs mem be ne _ HGm ltac:(lia) eq_refl) as RB.
    destruct (readable_range P A ae ne); try discriminate; try exact RA;
    destruct (readable_range P A be ne); try discriminate; try exact RB; destruct (afresh A _); discriminate.
  Qed.

  Variable a_memcmp a_bcmp : Z.
  Hypothesis MEMCMP : cmp_spec a_memcmp.
  Hypothesis BCMP : cmp_spec a_bcmp.

  #[using="PO MEMCMP"] Theorem memcmp_post : contract_post C_memcmp a_memcmp.
  Proof. apply memcmp_post_gen; [intros; reflexivity|reflexivity|exact MEMCMP]. Qed.
  #[using="PO BCMP"] Theorem bcmp_post : contract_post C_bcmp a_bcmp.
  Proof. apply memcmp_post_gen; [intros; reflexivity|reflexivity|exact BCMP]. Qed.
  #[using="PO"] Theorem memcmp_dead : contract_dead C_memcmp.
  Proof. apply memcmp_dead_gen. intros; reflexivity. Qed.
  #[using="PO"] Theorem bcmp_dead : contract_dead C_bcmp.
  Proof. apply memcmp_dead_gen. intros; reflexivity. Qed.
End CS2.
