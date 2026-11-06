(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnF), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACa1.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedTurnF.v. *)
(* The image-B (UBSan) walk of the end of one frame-loop turn
   of LLVMFuzzerTestOneInput, over image B's own addresses, registers, spill slots and UBSan
   guards; the shape is image A's.
   Ported from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurnF.v at e6bd82f51c9. *)
(* The frame-loop turn of LLVMFuzzerTestOneInput (image B, entry 0x80a3c), segment F:
   0x81d5c (GP_end) .. 0x81bb0 (GP_sched, another turn) or 0x81da4 (GP_freeT, the last turn),
   LLVMFEntrySchedTurnDefs.v.
     81d5c addiw s5,s5,1        one more turn is done
     81d60 sb   s8,0x62(s3)     shadow[98]  := 0xf8   (s8 = -8, s3 = the frame's shadow base)
     81d64 sb   s8,0x64(s3)     shadow[100] := 0xf8
     81d68 sb   s8,0x66(s3)     shadow[102] := 0xf8
     81d6c bnez s5,0x81bb0      another turn
     81d70 j    0x81da4         the last turn
   The counter s5 holds `i - frames` (TF's tcom). `addiw` adds 1 in 32 bits and sign-extends,
   which `aluw_inc` turns into the plain sum for a counter in [-4097, 0). While `i + 1 <
   frames` the counter stays negative, the branch is taken and the state is the head of the
   loop with `n` turns left (GSn n); when `i + 1 = frames` it is 0 and the fall-through
   reaches the free of the table (GI_freeT). The three stores put 0xf8 back into the shadow
   of ch, param and value, so the frame's shadow returns from GSH_turn to GSH_sched.
   Image A writes 0xf8 from s9 (x25) through the shadow base in s6 (x22) and counts in s2
   (x18); image B writes it from s8 (x24) through s3 (x19) and counts in s5 (x21). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC85 GrantFrame YC1h YC1g ACj1 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantBContracts LLVMFEntryDefs LLVMFEntrySeat LLVMFEntrySchedTurnDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel NextModel GrantModel SlotNeeds_c GrantSlotPlan HeadampSched SegSetModel Seg_sched_turn HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable POST : ecx -> world SEGS -> config -> Prop.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The names of LLVMFEntrySchedTurnDefs.v at this section's asyms, meter and laws. Image A's
   TD has no image-B twin (its work is inside the want_of call); this lane's own names
   (gslots_turn, gtregs, shr, G_sh, BxL, Bsp0, stk96, G_A, rs_A) take none of B, MT, LAWS. *)
#[local] Notation tbody := (tbody B MT).
#[local] Notation tcom := (tcom B MT).
#[local] Notation GSn := (GSn B MT).
#[local] Notation TB := (TB B MT).
#[local] Notation trec := (trec B MT).
#[local] Notation TC := (TC B MT).
#[local] Notation TCr := (TCr B MT).
#[local] Notation TE := (TE B MT).
#[local] Notation TF := (TF B MT).
#[local] Notation gtracked := (gtracked B).
#[local] Notation gctx := (gctx B MT LAWS).
#[local] Notation gaddr_ok := (gaddr_ok B).
#[local] Notation ginput_ok := (ginput_ok B MT LAWS).
#[local] Notation tbody_keep := (tbody_keep B MT).
#[local] Notation tcom_keep := (tcom_keep B MT).
#[local] Notation gpres := (gpres B MT LAWS).
#[local] Notation gtracked_rng := (gtracked_rng B MT LAWS).
#[local] Notation table_out := (table_out B MT LAWS).
#[local] Notation gtab_keep := (gtab_keep B).
#[local] Notation GI_sched_of := (GI_sched_of B MT).
#[local] Notation tcom_of_GI_sched := (tcom_of_GI_sched B MT).
#[local] Notation GI_freeT_of := (GI_freeT_of B MT).
#[local] Notation table_sep := (table_sep B LAWS).
#[local] Notation table_new := (table_new B LAWS).
#[local] Notation garo := (garo B MT).
#[local] Notation gtab_obj := (gtab_obj B).
#[local] Notation obj_gtab := (obj_gtab B).


(* The end of a turn: 0x81d5c .. the head of the loop (0x81bb0) or the free of the table (0x81da4). *)
Lemma segF : seg_F_ok B MT POST.
Proof.
  intros n HFT HGS cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE
    (i & t & T' & us' & HT & Hm & R20 & Hsch & Htab & HI1 & Hlus & Hus).
  destruct (gctx cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  destruct (gpres cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr) as (HFP & HSP).
  pose proof HT as (HTB & Hi & R21).
  pose proof HTB as (HBD & Hk & Hacc & Hbl & Hn & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27 & _).
  pose proof (ginput_ok cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HIN.
  pose proof (table_out cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HTO.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hlen & HINP).
  pose proof (Seg_sched_turn.frames_range (c_pl cx)) as HFR.
  pose proof asan_consts as (C1 & _).
  assert (GS : GE_STK = 32768) by reflexivity.
  assert (HSOv : 0 <= SHADOW_OFF /\ SHADOW_OFF + 2 ^ 44 + 128 <= 2 ^ 64) by (unfold SHADOW_OFF; lia).
  assert (HSHr : SHADOW_OFF <= gSH cx fp /\ gSH cx fp + 128 <= SHADOW_OFF + 2 ^ 44).
  { rewrite HSH. lia. }
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) E) by apply gagree0.
  (* s3 (x19) is the frame's shadow base, s5 (x21) the counter, s8 (x24) the byte -8. *)
  assert (E19 : bv_unsigned (ew E 19) = gSH cx fp).
  { unfold E. rewrite (ew_Eimg_Ereg_nat _ _ 19 19 eq_refl), R19. apply unsigned_lit_small. lia. }
  assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat i - GrantSlotPlan.frames (c_pl cx))).
  { unfold E. rewrite (ew_Eimg_Ereg_nat _ _ 21 21 eq_refl). exact R21. }
  assert (E24 : ew E 24 = w64 (-8)).
  { unfold E. rewrite (ew_Eimg_Ereg_nat _ _ 24 24 eq_refl). exact R24. }
  assert (HS : st_ok_pi SEGS VAL E (mkSS GP_end sr_atoms [shr 98; shr 100; shr 102] None G_sh) (restrict (w_H W3) ms3)).
  { rewrite (gms_eq (w_H W3) GP_end ms3 Hpc Hrv Hsvc Hrom Hfrg Hfc). apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - repeat apply Forall_cons; try apply Forall_nil;
        (eapply shr_ok; [exact E19 | lia | lia | apply (apresent_writable SEGS); apply HSP; lia]).
    - apply pairwise_disjoint_of_extents. unfold extent_of_region, shr.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E19.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok G_sh]. split; [|exact I]. unfold afact_ok.
      cbn [af_lo af_hi af_al2]. rewrite E19. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  (* 0x81d5c .. 0x81d68: the count and the three shadow stores; the run stops at 0x81d6c. *)
  paj_run_tok RUN HS HJ SHOK Bsp0.
  { awr_sh3 fp E19 EFA HSH. }
  lazymatch goal with HF1 : frame_of E _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ?m1)) |- _ => rename HF1 into HFr1 end.
  (* 0x81d6c bnez s5,0x81bb0 *)
  psrr_branch_tok RUN BR HS SHOK Bsp0.
  - (* taken: another turn *)
    rewrite branch_ne_U in Hc. unfold U in Hc. rewrite (aluw_inc E 21 _ E21) in Hc by lia.
    cbn [sv_denot] in Hc. rewrite !Z_to_bv_unsigned in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    unfold bv_wrap in Hc. change (bv_modulus 64) with (2 ^ 64) in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bsp0 GP_sched.
    { awr_sh3 fp E19 EFA HSH. }
    lazymatch goal with HF2 : frame_of E _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)) |- _ =>
      lazymatch m1 with ms3 => fail | _ => rename HF2 into HFr2 end end.
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
      pose proof (st_ok_pi_restrict_reg _ _ _ _ 21 HSx) as F21;
      let e := eval vm_compute in (sr_get (ss_regs ssx) 21) in change (sr_get (ss_regs ssx) 21) with e in F21;
      cbn [ms_regs restrict] in F21; rewrite (aluw_inc E 21 _ E21) in F21 by lia;
      pose proof (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msF) (ms_regs ms3) []
        [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HSx HAE ltac:(vm_compute; reflexivity)) as FR;
      cbn [ms_regs restrict] in FR;
      assert (HKA : forall a, 0 <= a < 2 ^ 64 -> ~ (a = gSH cx fp + 98 \/ a = gSH cx fp + 100 \/ a = gSH cx fp + 102) ->
        aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
        by (intros a Ha Hw; apply (kept2 _ _ _ _ _ _ _ _ HFr1 HFr2 a Ha); inw_tac E19; apply Hw; lia);
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HSx eq_refl) as RG98;
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HSx eq_refl) as RG100;
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HSx eq_refl) as RG102;
      cbn [ms_mem restrict] in RG98, RG100, RG102;
      pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG98 (or_introl eq_refl) E19) as V98;
      pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG100 (or_introl eq_refl) E19) as V100;
      pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG102 (or_introl eq_refl) E19) as V102;
      cbn [sv_denot] in V98, V100, V102;
      apply (HGS cx fp k acc ly3 S3 W3 msF mdF HB HJ Hfr HMLE)
    end.
    assert (Hn0 : n <> 0%nat) by (intros ->; lia).
    rewrite E24 in V98, V100, V102.
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (w64 (-8)) + 0)) mod 256) with 248 in V98, V100, V102.
    destruct (gshadow_set3 cx fp W3 ms3 W3 _ GSH_turn 248 248 248 HSHW GSH_turn_len
      ltac:(intros j Hj H98 H100 H102; apply HKA; [lia | lia]) V98 V100 V102) as (HSH2 & HSL2).
    rewrite GSH_back in HSH2, HSL2.
    split.
    + apply (GI_sched_of cx fp (S i) t).
      * eapply tcom_keep; [exact HF4096 | exact HFceil | exact HFapp | lia | lia | exact HIN | exact HT
          | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc
          | repeat split; apply FR; cbv; tauto | lia | rewrite F21; f_equal; lia
          | intros a Ha Hw; apply HKA; [eapply gtracked_rng; eauto; lia | intros Hq; apply Hw; unfold gwr; lia]
          | exact HSH2 | exact HSL2 ].
      * rewrite FR by (cbv; tauto). exact R20.
      * rewrite Hsch. split; [|split; [exact HI1 | split; [exact Hlus|]]].
        -- eapply gtab_keep; [exact Htab|]. intros j Hj. destruct (HTO j Hj) as (Hw & Hr). apply HKA; [exact Hr|].
           intros Hq; apply Hw; unfold gwr; lia.
        -- eapply gfarr_keep; [exact Hus|]. intros a Ha. rewrite Hlus in Ha. apply HKA.
           ++ unfold GO_UNSET in Ha. lia.
           ++ rewrite HSH. unfold GO_UNSET, SHADOW_OFF in *. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. lia.
    + split; [rewrite F21; f_equal; lia | lia].
  - (* not taken: the last turn, 0x81d70 j 0x81da4 *)
    rewrite branch_ne_U in Hc. unfold U in Hc. rewrite (aluw_inc E 21 _ E21) in Hc by lia.
    cbn [sv_denot] in Hc. rewrite !Z_to_bv_unsigned in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    unfold bv_wrap in Hc. change (bv_modulus 64) with (2 ^ 64) in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bsp0 GP_freeT.
    { awr_sh3 fp E19 EFA HSH. }
    lazymatch goal with HF2 : frame_of E _ (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ?m2)) |- _ =>
      lazymatch m1 with ms3 => fail | _ => rename HF2 into HFr2 end end.
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
      pose proof (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msF) (ms_regs ms3) []
        [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HSx HAE ltac:(vm_compute; reflexivity)) as FR;
      cbn [ms_regs restrict] in FR;
      assert (HKA : forall a, 0 <= a < 2 ^ 64 -> ~ (a = gSH cx fp + 98 \/ a = gSH cx fp + 100 \/ a = gSH cx fp + 102) ->
        aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a)
        by (intros a Ha Hw; apply (kept2 _ _ _ _ _ _ _ _ HFr1 HFr2 a Ha); inw_tac E19; apply Hw; lia);
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HSx eq_refl) as RG98;
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HSx eq_refl) as RG100;
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HSx eq_refl) as RG102;
      cbn [ms_mem restrict] in RG98, RG100, RG102;
      pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG98 (or_introl eq_refl) E19) as V98;
      pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG100 (or_introl eq_refl) E19) as V100;
      pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG102 (or_introl eq_refl) E19) as V102;
      cbn [sv_denot] in V98, V100, V102;
      apply (HFT cx fp k acc ly3 S3 W3 msF mdF HB HJ Hfr HMLE)
    end.
    rewrite E24 in V98, V100, V102.
    change (bv_unsigned (Z_to_bv 64 (bv_unsigned (w64 (-8)) + 0)) mod 256) with 248 in V98, V100, V102.
    destruct (gshadow_set3 cx fp W3 ms3 W3 _ GSH_turn 248 248 248 HSHW GSH_turn_len
      ltac:(intros j Hj H98 H100 H102; apply HKA; [lia | lia]) V98 V100 V102) as (HSH2 & HSL2).
    rewrite GSH_back in HSH2, HSL2.
    apply (GI_freeT_of cx fp t).
    + eapply tbody_keep; [exact HF4096 | exact HFceil | exact HFapp | lia | lia | exact HIN | exact HTB
        | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc
        | repeat split; apply FR; cbv; tauto
        | intros a Ha Hw; apply HKA; [eapply gtracked_rng; eauto; lia | intros Hq; apply Hw; unfold gwr; lia]
        | exact HSH2 | exact HSL2 ].
    + rewrite FR by (cbv; tauto). exact R20.
Qed.


End c.
End b.
End a.
