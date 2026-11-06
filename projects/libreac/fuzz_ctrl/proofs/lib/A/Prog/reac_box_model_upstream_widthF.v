(* The footprint twin of reac_box_model_upstream_width.v (RECIPE.md step 1 (a working note, not in this delivery)): the same run as an
   ExecF.evtF under a footprint RNG, with one rng premise per region the run reads or writes.
   reac_box_model_upstream_width.v and its theorem are unchanged; reac_box_model_upstream_width_holds_of_F re-derives
   the old statement from this one with ExecF.RNG_all. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT reac_box_model_upstream_width_c
  reac_box_model_upstream_width.
(* Last: StepF's step / if_true (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* A shadow address is [x / 8 + off]: its access side goal needs the Euclidean equations of the division, which
   StepF's [alia] does not add, so the shadow loads go through StepF's acc_hint hook. *)
Ltac has_div E := lazymatch E with context [Z.div _ _] => idtac end.

Ltac solve_acc_div_with H E :=
  lazymatch goal with
  | |- acc_in ?RNG (_, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with
      | rng _ ?lo ?len =>
          apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
          split; Z.div_mod_to_equations; lia
      end
  end.

Ltac acc_hintF :=
  lazymatch goal with
  | |- acc_in ?RNG (?a, _) =>
      let E := addr_expr a in
      has_div E;
      match goal with
      | H : rng RNG ?lo _ |- _ => has_div lo; solve_acc_div_with H E
      end
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= acc_hintF.

Section WF.
  Variables (ra sp1 gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mp off : Z) (bs : list byte) (W : list ivl)
    (Q : machine_state -> Prop) (RNG : footprint).
  Hypothesis Hr : 0 <= mp < 2^64.
  Hypothesis E : mp <> 0.
  Hypothesis H24 : mp + 24 <= 2^64.
  Hypothesis Hlen : length bs = 8%nat.
  Hypothesis HB : bytes_at rsegs m (mp + 16) bs.
  Hypothesis HSR : asan_shadow_rd rsegs m off (mp + 16) 8 W.
  Hypothesis HAD : asan_addressable rsegs m off (mp + 16) 8.
  Hypothesis H3 : asan_rt3 rsegs m off (mp + 16) 8.
  (* The footprint premises of the body: the 8 bytes at mp + 16 and their shadow span, in the [off] form the body
     uses (reac_box_model_upstream_width_F_holds sets off := ASAN_K in the statement's premise). mp need not be
     8-aligned, so the two shadow loads, at (mp + 16) / 8 + off and (mp + 20) / 8 + off, can be two bytes. *)
  Hypothesis Rm : rng RNG (mp + 16) 8.
  Hypothesis Rs : rng RNG ((mp + 16) / 8 + off) ((mp + 23) / 8 - (mp + 16) / 8 + 1).

  Abbreviation ST pc x10 x11 x12 x13 x14 :=
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x11 x12 x13 x14,
    evtF rsegs RNG Q (ST 0x86a64 (Z_to_bv 64 (bm_uw mp bs)) x11 x12 x13 x14).

  Lemma w_maxF : forall x10 x12 x13 x14,
    0 <= bm_in_ch bs -> 0 <= bm_out_ch bs ->
    (bm_in_ch bs = 0 \/ (2 <= bm_in_ch bs <= 40 /\ bm_in_ch bs mod 2 = 0)) ->
    (bm_out_ch bs = 0 \/ (2 <= bm_out_ch bs <= 40 /\ bm_out_ch bs mod 2 = 0)) ->
    evtF rsegs RNG Q (ST 0x86a4c x10 (Z_to_bv 64 (bm_in_ch bs)) x12 x13 x14).
  Proof.
    intros x10 x12 x13 x14 Li Lo Hi Ho.
    assert (U : bm_uw mp bs = Z.max (bm_in_ch bs) 2).
    { unfold bm_uw, bm_wok. destruct Hi as [Hi|Hi]; destruct Ho as [Ho|Ho]; decide_tests; reflexivity. }
    pose proof (bm_in_ch_range bs) as Ri.
    pose proof EXIT as EX. rewrite U in EX.
    step. step. rewrite (rc_ltu 2 (bm_in_ch bs)) by lia.
    destruct (Z.ltb_spec 2 (bm_in_ch bs)) as [G|G]; cbv iota.
    - step. step. rewrite Z.max_l in EX by lia. apply EX.
    - step. step. step. rewrite Z.max_r in EX by lia. apply EX.
  Qed.

  Lemma w_outF : forall x10 x13 x14,
    0 <= bm_in_ch bs -> 0 <= bm_out_ch bs ->
    (bm_in_ch bs = 0 \/ (2 <= bm_in_ch bs <= 40 /\ bm_in_ch bs mod 2 = 0)) ->
    evtF rsegs RNG Q (ST 0x86a30 x10 (Z_to_bv 64 (bm_in_ch bs)) (Z_to_bv 64 (bm_out_ch bs)) x13 x14).
  Proof.
    intros x10 x13 x14 Li Lo Hi. pose proof (bm_out_ch_range bs) as Ro.
    step. rewrite (rc_eqb (bm_out_ch bs) 0) by lia.
    destruct (Z.eqb_spec (bm_out_ch bs) 0) as [Zo|Zo]; cbv iota.
    - apply w_maxF; [exact Li | exact Lo | exact Hi | left; exact Zo].
    - step. step. step. rewrite (rc_addiw (bm_out_ch bs) (-41)) by lia.
      step. rewrite (rc_wok_ltu (bm_out_ch bs)) by lia.
      destruct (Z.leb_spec 2 (bm_out_ch bs)) as [G1|G1]; destruct (Z.leb_spec (bm_out_ch bs) 40) as [G2|G2];
        cbn [andb negb].
      + step. step. rewrite (rc_odd_eqb (bm_out_ch bs)) by lia.
        destruct (Z.eqb_spec (bm_out_ch bs mod 2) 0) as [Ev|Od]; cbn [negb].
        * apply w_maxF; [exact Li | exact Lo | exact Hi | right; lia].
        * destruct Hi as [Hi|Hi]; uw_zero EXIT mp bs.
      + destruct Hi as [Hi|Hi]; uw_zero EXIT mp bs.
      + destruct Hi as [Hi|Hi]; uw_zero EXIT mp bs.
      + destruct Hi as [Hi|Hi]; uw_zero EXIT mp bs.
  Qed.

  Lemma w_lw2F : 0 <= bm_in_ch bs -> forall x12 x13 x14,
    evtF rsegs RNG Q (ST 0x86a0c (Z_to_bv 64 (mp + 20)) (Z_to_bv 64 (bm_in_ch bs)) x12 x13 x14).
  Proof.
    intros Ni x12 x13 x14.
    destruct (rc_rd4_opaque rsegs m (mp + 16) bs 4 HB ltac:(lia)) as (L2 & EL2 & RD2).
    replace (mp + 16 + Z.of_nat 4) with (mp + 20) in RD2 by lia.
    pose proof (bm_in_ch_range bs) as Ri. pose proof (bm_out_ch_range bs) as Ro.
    step. rewrite (rc_lw_out bs L2 EL2).
    step. rewrite (rc_lts0 (bm_out_ch bs)) by lia.
    destruct (Z.ltb_spec (bm_out_ch bs) 0) as [No|No]; cbv iota.
    - step. uw_zero EXIT mp bs.
    - step. rewrite (rc_eqb (bm_in_ch bs) 0) by lia.
      destruct (Z.eqb_spec (bm_in_ch bs) 0) as [Zi|Zi]; cbv iota.
      + apply w_outF; [lia | lia | left; exact Zi].
      + step. step. step. rewrite (rc_addiw (bm_in_ch bs) (-41)) by lia.
        step. rewrite (rc_wok_ltu (bm_in_ch bs)) by lia.
        destruct (Z.leb_spec 2 (bm_in_ch bs)) as [G1|G1]; destruct (Z.leb_spec (bm_in_ch bs) 40) as [G2|G2];
          cbn [andb negb].
        * step. step. rewrite (rc_odd_eqb (bm_in_ch bs)) by lia.
          destruct (Z.eqb_spec (bm_in_ch bs mod 2) 0) as [Ev|Od]; cbn [negb].
          -- apply w_outF; [lia | lia | right; lia].
          -- uw_zero EXIT mp bs.
        * uw_zero EXIT mp bs.
        * uw_zero EXIT mp bs.
        * uw_zero EXIT mp bs.
  Qed.

  Lemma w_lw1F : forall x13 x14,
    evtF rsegs RNG Q (ST 0x869f0 (Z_to_bv 64 mp) (Z_to_bv 64 (mp + 16)) (Z_to_bv 64 off) x13 x14).
  Proof.
    intros x13 x14.
    destruct (rc_rd4_opaque rsegs m (mp + 16) bs 0 HB ltac:(lia)) as (L1 & EL1 & RD1).
    replace (mp + 16 + Z.of_nat 0) with (mp + 16) in RD1 by lia.
    pose proof (bm_in_ch_range bs) as Ri.
    step. rewrite (rc_lw_in bs L1 EL1).
    step. rewrite (rc_lts0 (bm_in_ch bs)) by lia.
    destruct (Z.ltb_spec (bm_in_ch bs) 0) as [Ni|Ni]; cbv iota.
    - step. uw_zero EXIT mp bs.
    - destruct (asan_shadow_read_at rsegs m off (mp + 16) 8 W 4 ((mp + 20) / 8 + off) HSR ltac:(lia)
                  ltac:(unfold asan_shadow; replace (mp + 16 + 4) with (mp + 20) by lia; reflexivity))
        as (k & RK & BK).
      pose proof (reac_box_model_upstream_width_chk4 rsegs m off (mp + 16) 8 4 k HAD H3 ltac:(lia) ltac:(lia) BK)
        as OK.
      replace (mp + 16 + 4) with (mp + 20) in OK by lia.
      pose proof (rc_byte_signed k) as KR. clear BK.
      pose proof (Z.mod_pos_bound (mp + 20) 8 ltac:(lia)) as M.
      step. step.
      rewrite (unsigned_lit (mp + 20)) by lia. rewrite rc_shr3.
      step. step.
      clear RK.
      step.
      unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
      destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
      + apply (w_lw2F Ni).
      + step.
        rewrite (unsigned_lit (mp + 20)) by lia. rewrite rc_land7.
        step. step.
        rewrite (rc_lts_signed ((mp + 20) mod 8 + 3) (bv_signed k)) by lia.
        replace ((mp + 20) mod 8 + 3 <? bv_signed k) with true
          by (symmetry; apply Z.ltb_lt; destruct OK; lia).
        apply (w_lw2F Ni).
  Qed.

  Lemma w_entryF : forall x11 x13 x14,
    evtF rsegs RNG Q (ST 0x869dc (Z_to_bv 64 mp) x11 (Z_to_bv 64 off) x13 x14).
  Proof using Hr E H24 Hlen HB HSR HAD H3 Rm Rs EXIT.
    intros x11 x13 x14.
    destruct (asan_shadow_read_at rsegs m off (mp + 16) 8 W 0 ((mp + 16) / 8 + off) HSR ltac:(lia)
                ltac:(unfold asan_shadow; rewrite Z.add_0_r; reflexivity)) as (k & RK & BK).
    pose proof (reac_box_model_upstream_width_chk4 rsegs m off (mp + 16) 8 0 k HAD H3 ltac:(lia) ltac:(lia) BK)
      as OK.
    rewrite Z.add_0_r in OK.
    pose proof (rc_byte_signed k) as KR. clear BK.
    pose proof (Z.mod_pos_bound (mp + 16) 8 ltac:(lia)) as M.
    step. step.
    rewrite (unsigned_lit (mp + 16)) by lia. rewrite rc_shr3.
    step. step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply w_lw1F.
    - step.
      rewrite (unsigned_lit (mp + 16)) by lia. rewrite rc_land7.
      step. step.
      rewrite (rc_lts_signed ((mp + 16) mod 8 + 3) (bv_signed k)) by lia.
      replace ((mp + 16) mod 8 + 3 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply w_lw1F.
  Qed.
End WF.

(* route (C): the proof, on the _on twin (no shadow_rw premise; the proof never used it). *)
Theorem reac_box_model_upstream_width_F_holds_on : reac_box_model_upstream_width_contract_F_on.
Proof.
  unfold reac_box_model_upstream_width_contract_F_on, REAC_BOX_MODEL_UPSTREAM_WIDTH,
    REAC_BOX_MODEL_UPSTREAM_WIDTH_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    mp lo bs Ha0 HM ST HLO HD HCE HADR HW RFR RGK RCK RMP.
  pose proof (rc_word_range a0 mp Ha0) as Hr. apply rc_word in Ha0. subst a0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  assert (WV : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; destruct ST as (_ & _ & H); exact (proj1 (H x ltac:(lia)))).
  destruct (Z.eq_dec mp 0) as [E|E].
  - subst mp. clear HM HD HADR RMP.
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    step. if_true.
    step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. cbv beta. do 5 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
  - destruct (HM E) as (H24 & Hlen & HB). clear HM.
    pose proof (HD E) as HD1. clear HD.
    pose proof (HADR E) as HADR1. clear HADR.
    destruct (RMP E) as (Rm & Rs). clear RMP.
    pose proof (rt_asan_rt m _ HCE HW) as HRT.
    pose proof (rt_shadow_rd m (mp + 16) 8 _ HADR1 (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
    pose proof (rt_addressable m (mp + 16) 8 HADR1) as HAD.
    pose proof (rt_rt3 m (mp + 16) 8 HADR1) as H3.
    set (off := ASAN_K) in HRT, HSR, HAD, H3, Rs. clearbody off.
    (* the two runtime cells are read at literal addresses: their rng premises in literal form *)
    pose proof RGK as RGz. pose proof RCK as RCz.
    unfold GOT_CELL_K in RGz. unfold CELL_K in RCz.
    carve_frame 16%nat ST.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_shadow_rd_munch rsegs m m1 off (mp + 16) 8 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
    pose proof (asan_addressable_munch rsegs m m1 off (mp + 16) 8 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
    pose proof (asan_rt3_munch rsegs m m1 off (mp + 16) 8 _ _ H3 HSR MU (fun x Hx => Hx)) as H31.
    pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    step. rewrite (rc_eqb mp 0) by lia. destruct (Z.eqb_spec mp 0); [lia|]. cbv iota.
    step. step. step.
    clear RG RC.
    refine (w_entryF ra _ gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 mp off bs
              _ _ RNG Hr E H24 Hlen HB HSR1 HAD1 H31 Rm Rs _ _ _ _).
    intros x11 x12 x13 x14.
    step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. cbv beta. do 5 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WV) | exact ST].
Qed.

(* The old name, from the _on twin (route (C) form rule: the old statement stays, proved in one line). *)
Theorem reac_box_model_upstream_width_F_holds : reac_box_model_upstream_width_contract_F.
Proof. exact (reac_box_model_upstream_width_contract_F_of_on reac_box_model_upstream_width_F_holds_on). Qed.

(* The plain _on twin, at ExecF.RNG_all. *)
Theorem reac_box_model_upstream_width_holds_on : reac_box_model_upstream_width_contract_on.
Proof. exact (reac_box_model_upstream_width_contract_on_of_F_on reac_box_model_upstream_width_F_holds_on). Qed.

(* RECIPE step 1: the old theorem's statement, back from the footprint form at ExecF.RNG_all. *)
Theorem reac_box_model_upstream_width_holds_of_F : reac_box_model_upstream_width_contract.
Proof. exact (reac_box_model_upstream_width_contract_of_F reac_box_model_upstream_width_F_holds). Qed.
