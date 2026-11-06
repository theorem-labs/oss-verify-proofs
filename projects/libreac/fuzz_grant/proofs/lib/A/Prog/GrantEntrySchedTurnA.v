(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnB), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACa1.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurnB.v; 270 of its 363 lines of code are new or changed and 227 lines of the source are left out. *)
(* The frame-loop turn of LLVMFuzzerTestOneInput, segment A: 0x815c4 .. the return of reac_headamp_tx_next (GrantEntrySchedTurnDefs.v). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC85 GrantFrame YC1h YC1g ACj1 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantEntryDefs GrantEntrySeat HeadampTxEffective HeadampDefault HeadampTxNext.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel NextModel GrantModel SlotNeeds_c GrantSlotPlan HeadampSched SegSetModel Seg_sched_turn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntrySchedTurnDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma w64_turns : forall x m, -4097 < x < 0 -> (m < 4097)%nat -> w64 x = w64 (- Z.of_nat m) -> x = - Z.of_nat m.
Proof.
  intros x m Hx Hm H. apply (f_equal (@bv_unsigned 64)) in H. unfold w64 in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H. lia.
Qed.
(* lia below runs on contexts with many / and mod; the facts it needs about them are posed by hand. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
Hypothesis NXT : theadamp_tx_next_spec B.
Variable POST : ecx -> world SEGS -> config -> Prop.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The names of GrantEntrySchedTurnDefs.v at this section's asyms, meter and laws. *)
#[local] Notation tbody := (tbody B MT).
#[local] Notation tcom := (tcom B MT).
#[local] Notation GSn := (GSn B MT).
#[local] Notation TB := (TB B MT).
#[local] Notation trec := (trec B MT).
#[local] Notation TC := (TC B MT).
#[local] Notation TCr := (TCr B MT).
#[local] Notation TD := (TD B MT).
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


(* The head of the loop .. the return of reac_headamp_tx_next (0x815c4 .. 0x815f0). *)
Lemma pres_regs : forall regs regs2, aregs_preserved regs regs2 ->
  forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv -> getr regs2 r0 = getr regs r0.
Proof.
  intros regs regs2 HP r0 Hr0.
  assert (Hc : acallee_saved (bv_unsigned r0)).
  { unfold acallee_saved. cbv [In] in Hr0.
    repeat (destruct Hr0 as [<- | Hr0];
      [match goal with |- context [bv_unsigned ?r] => let x := eval vm_compute in (bv_unsigned r) in
         change (bv_unsigned r) with x end; lia |]).
    destruct Hr0. }
  pose proof (HP _ Hc) as H.
  assert (Ez : Z_to_bv 5 (bv_unsigned r0) = r0)
    by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
  rewrite Ez in H. exact H.
Qed.

Lemma segA : seg_A_ok B MT POST.
Proof.
  intros m HTB cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE (HGI & R18m & Hm4097).
  destruct (tcom_of_GI_sched _ _ _ _ _ _ _ _ _ HGI) as (i & t & HT & R19 & HU).
  destruct (GrantSlotPlan.sched_at (c_pl cx) t i) as [T us] eqn:Hsch.
  destruct HU as (Htab & HI1 & Hlus & Hus).
  destruct (NextModel.next_model T t) as [[r [[c p] v]] T'] eqn:Hnx.
  destruct (gctx cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  destruct (gpres cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr) as (HFP & HSP).
  pose proof HT as (HTB0 & Hi & R18).
  pose proof HTB0 as (HBD & Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R23 & R24 & R25 & R27 & HSC & HSL & HWS & HST & HH).
  pose proof (ginput_ok cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HIN.
  pose proof (table_out cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HTO.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hlen & HINP).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  pose proof HSL as ((M16 & M24 & M48 & M56 & M136 & M144 & M152 & M176) & L8 & L32 & L40 & L72 & L80 & L104 & L112 & L128).
  pose proof (Seg_sched_turn.frames_range (c_pl cx)) as HFR.
  pose proof asan_consts as (C1 & _).
  pose proof (proj1 HJ) as HAR3.
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (GS : GE_STK = 32768) by reflexivity.
  assert (Hm : GrantSlotPlan.frames (c_pl cx) - Z.of_nat i = Z.of_nat m).
  { rewrite R18 in R18m. apply w64_turns in R18m; [lia | lia | exact Hm4097]. }
  pose proof Htab as (Hint & Ht0 & HTl & HTb).
  pose proof (HeadampSched.frame_ok (c_pl cx) t i Ht0) as FO.
  destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] fr] pe] eqn:Hsrd.
  rewrite Hsch, Hnx in FO.
  destruct FO as (FL1 & FL2 & FL3 & FLT' & FI1 & FSch & FR01 & FR1).
  assert (HSHr : 2147450880 <= gSH cx fp /\ gSH cx fp + 128 <= 2147450880 + 2 ^ 44) by (rewrite HSH; unfold SHADOW_OFF; dm (gF cx fp) 8; lia).
  assert (Hsep : gSH cx fp + 128 <= gF cx fp \/ gF cx fp + 1024 <= gSH cx fp).
  { rewrite HSH. dm (gF cx fp) 8. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR3 Hfin) as HFoff.
  unfold off_img in HFoff. rewrite EFA, fsb4 in HFoff.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ GE_CID fp HAR3 Hint Hfin) as HdTF.
  unfold zdisjoint in HdTF. cbn [fst snd] in HdTF. rewrite EFA, fsb4 in HdTF. change (req_size 460) with 460 in HdTF.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hint) as (_ & _ & HTc & HTapp & _).
  change (req_size 460) with 460 in HTc, HTapp.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) E) by (subst E; apply gagree0).
  assert (EE : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
    by (intros n0 r0 Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = gF cx fp + 784)
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; unfold GO_CH; lia).
  assert (U21 : bv_unsigned (ew E 21) = gF cx fp + 800)
    by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; unfold GO_PAR; lia).
  assert (U22 : bv_unsigned (ew E 22) = gSH cx fp) by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL E (mkSS GP_sched sr_atoms rs_A None G_A) (restrict (w_H W3) ms3)).
  { rewrite (gms_eq (w_H W3) GP_sched ms3 Hpc Hrv Hsvc Hrom Hfrg Hfc). apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold rs_A. apply Forall_cons.
      { unfold region_ok, stk128.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (c_sp1 cx) 128 8 (SOff 19 32) (gF cx fp + 816)).
        - cbn [sv_denot]. rewrite U19. f_equal. lia.
        - cbn. lia.
        - cbn. lia.
        - apply val_mem_of_rdword. exact L128. }
      apply Forall_cons; [eapply cellr_ok; [exact U19 | lia | lia | apply (apresent_writable SEGS);
        replace (gF cx fp + 784 + 0) with (gF cx fp + 784) by lia; apply HFP; lia]|].
      apply Forall_cons; [eapply cellr_ok; [exact U21 | lia | lia | apply (apresent_writable SEGS);
        replace (gF cx fp + 800 + 0) with (gF cx fp + 800) by lia; apply HFP; lia]|].
      apply Forall_cons; [eapply cellr_ok; [exact U19 | lia | lia | apply (apresent_writable SEGS);
        replace (gF cx fp + 784 + 32) with (gF cx fp + 816) by lia; apply HFP; lia]|].
      repeat apply Forall_cons; try apply Forall_nil;
        (eapply shr_ok; [exact U22 | lia | lia | apply (apresent_writable SEGS); apply HSP; lia]).
    - apply pairwise_disjoint_of_extents. unfold extent_of_region, rs_A, stk128, cellr, shr.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19, U21, U22.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok G_A]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U19, U21, U22. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
  assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  clear HE.
  paj_run_tok RUN HS HJ SHOK Bsp0.
  { awr_fr fp EFA HSH. }
  lazymatch goal with HFx : frame_of E _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ?m1)) |- _ =>
    rename HFx into HFr1 end.
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msX) |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
    rename HSx into HSc;
    prreg HSc (1%bv : bv 5) Q1; prreg HSc (10%bv : bv 5) Q10; prreg HSc (11%bv : bv 5) Q11;
    prreg HSc (12%bv : bv 5) Q12; prreg HSc (13%bv : bv 5) Q13;
    pose proof (st_ok_region_nth _ _ _ 4 _ HSc eq_refl) as RG98;
    pose proof (st_ok_region_nth _ _ _ 5 _ HSc eq_refl) as RG100;
    pose proof (st_ok_region_nth _ _ _ 6 _ HSc eq_refl) as RG102;
    cbn [ms_mem restrict] in RG98, RG100, RG102;
    pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG98 (or_introl eq_refl) U22) as V98;
    pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG100 (or_introl eq_refl) U22) as V100;
    pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG102 (or_introl eq_refl) U22) as V102;
    rewrite ge_sv_SOff0, (EE 24%nat 24%bv eq_refl), R24 in V98, V100, V102;
    change (bv_unsigned (w64 1) mod 256) with 1 in V98, V100, V102;
    pose proof (regs_kept_of_st_ok SEGS E _ _ (ms_regs ms3) [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv
      HSc HAE ltac:(vm_compute; reflexivity)) as QR;
    cbn [ms_regs restrict] in QR;
    rewrite (st_ok_restrict_mkst _ _ _ _ _ HSc eq_refl); cbn [ss_pc setpc];
    rewrite pa_sigma_reac_headamp_tx_next;
    assert (HKA : forall a, 0 <= a < 2 ^ 64 ->
        ~ (a = gF cx fp + 784 \/ a = gF cx fp + 800 \/ a = gF cx fp + 816 \/
           a = gSH cx fp + 98 \/ a = gSH cx fp + 100 \/ a = gSH cx fp + 102) ->
        aview SEGS (w_H W3) (ms_mem msX) a = aview SEGS (w_H W3) (ms_mem ms3) a)
      by (intros a Ha Hw; rewrite (aview_kept_out _ _ _ _ _ HFr1 a Ha); [reflexivity|];
          inw_tac U22; first [lia | rewrite ?U19, ?U21, ?U9 in *; apply Hw; lia]);
    destruct (gpres cx fp k ly3 S3 W3 (ms_mem msX) mdX HB HJ Hfr) as (HFP' & HSP');
    rename msX into msc; remember mdX as mdc eqn:Hmdc
  end.
  assert (Hra : getr (ms_regs msc) 1 = w64 (BASE + GP_nx)) by (rewrite Q1; reflexivity).
  rewrite (EE 20%nat 20%bv eq_refl), R20 in Q10.
  rewrite (EE 19%nat 19%bv eq_refl), R19 in Q11.
  rewrite (EE 21%nat 21%bv eq_refl), R21 in Q12.
  rewrite U19 in Q13. replace (gF cx fp + 784 + 32) with (gF cx fp + GO_VAL) in Q13 by (unfold GO_VAL; lia).
  assert (Usp : spZ (ms_regs msc) = c_sp1 cx).
  { unfold spZ. rewrite (QR 2%bv ltac:(cbv; tauto)), G2. apply unsigned_lit_small. lia. }
  assert (Us0 : s0Z (ms_regs msc) = spZ (c_regs cx)).
  { unfold s0Z. rewrite (QR 8%bv ltac:(cbv; tauto)), G8. apply unsigned_lit_small. lia. }
  pose proof HB as ((HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & _) & _).
  pose proof HJ as (_ & HLY & _ & _ & _ & _ & _ & _ & J9 & _ & _ & _ & _ & J14 & _).
  assert (HFX : forall a, gF cx fp <= a < gF cx fp + 1024 -> 0 <= a < 2 ^ 64) by (intros; lia).
  assert (Hcells : forall o, o = GO_CH \/ o = GO_PAR \/ o = GO_VAL ->
     nx_out_ok (spZ (ms_regs msc)) t (gF cx fp + o) /\
     nx_may_write B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) ly3 S3 [(GE_CID, fp)] (gF cx fp + o) /\
     apresent (w_H W3) (ms_mem msc) (gF cx fp + o)).
  { intros o Ho. assert (Ho' : 784 <= o <= 816) by (unfold GO_CH, GO_PAR, GO_VAL in Ho; lia).
    split; [|split].
    - unfold nx_out_ok, TX_SIZE. rewrite Usp.
      clear - Ho' HF4096 HFceil Hceil GS Hsp1 HdTF HFoff HFapp C1 H47.
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL, NEXT_STK in *.
      repeat split; lia.
    - unfold nx_may_write, awr_byte. right; right; right. exists GE_CID, fp. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EFA, fsb4. lia.
    - apply HFP'. lia. }
  assert (Hshb : forall o v0, (o = GO_CH /\ v0 = 98) \/ (o = GO_PAR /\ v0 = 100) \/ (o = GO_VAL /\ v0 = 102) ->
     aview SEGS (w_H W3) (ms_mem msc) (gSH cx fp + v0) = Some 1 ->
     range_addressable (aview SEGS (w_H W3) (ms_mem msc)) SHADOW_OFF (gF cx fp + o) 1).
  { intros o v0 Hov Hv. apply range_addressable_partial; [| | lia].
    2: { dm (gF cx fp) 64. destruct Hov as [(-> & _) | [(-> & _) | (-> & _)]]; unfold GO_CH, GO_PAR, GO_VAL;
         [dm (gF cx fp + 784) 8 | dm (gF cx fp + 800) 8 | dm (gF cx fp + 816) 8]; lia. }
    unfold shadow_of_addr. replace (SHADOW_OFF + (gF cx fp + o) / 8) with (gSH cx fp + v0); [exact Hv|].
    rewrite HSH. destruct Hov as [(-> & ->) | [(-> & ->) | (-> & ->)]]; unfold GO_CH, GO_PAR, GO_VAL;
    [ replace (gF cx fp + 784) with (gF cx fp + 98 * 8) by lia
    | replace (gF cx fp + 800) with (gF cx fp + 100 * 8) by lia
    | replace (gF cx fp + 816) with (gF cx fp + 102 * 8) by lia ];
    rewrite Z.div_add by lia; lia. }
  assert (HSV' : gsaved cx W3 msc).
  { destruct HSV as (S8 & S16). split.
    - rewrite <- S8. apply rdword_ext. intros kk Hkk. apply HKA; [lia|]. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. lia.
    - intros j Hj. rewrite <- (S16 j Hj). apply rdword_ext. intros kk Hkk. apply HKA; [lia|].
      unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. lia. }
  assert (HCH : achain ly3 (aview SEGS (w_H W3) (ms_mem msc)) (spZ (ms_regs msc)) (s0Z (ms_regs msc)) (gch cx)).
  { rewrite Usp, Us0. apply (achain_ly_top (c_ly cx)); [destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|].
    eapply (ge_achain B MT cx HB).
    - intros a Ha. apply J9; lia.
    - exact (proj1 HSV').
    - pose proof (proj2 HSV' 0 ltac:(lia)) as S0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in S0 by lia.
      rewrite S0. reflexivity.
    - lia. }
  assert (HOBJ : obj_at SEGS (mrestrict (w_H W3) (ms_mem msc)) t LAY_TX (tx_vals T)).
  { apply (gtab_obj cx ly3 S3 W3 msc). eapply gtab_keep; [exact Htab|]. intros j Hj. destruct (HTO j Hj) as (Hw & Hr).
    apply HKA; [exact Hr|]. intros Hq. apply Hw. unfold gwr, GO_UNSET, GO_CH, GO_PAR, GO_VAL. lia. }
  eapply SRr_bind.
  { exact (NXT GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)]
      ly3 S3 W3 (ms_mem msc) mdc k (ms_regs msc) t (gF cx fp + GO_CH) (gF cx fp + GO_PAR) (gF cx fp + GO_VAL) T (gch cx)
      HJ (garo cx fp k ly3 S3 W3 (ms_mem msc) mdc HB HJ)
      ltac:(rewrite Hra; apply ret_ok_codeptr_v; [unfold GP_nx; lia | reflexivity])
      ltac:(unfold raZ; rewrite Hra; unfold w64, GP_nx; rewrite unsigned_lit_small; pose proof pa_base_lo; pose proof pa_B_ok; lia)
      ltac:(rewrite (QR 3%bv ltac:(cbv; tauto)), G3; exact Hgp0)
      ltac:(rewrite (QR 4%bv ltac:(cbv; tauto)), G4; exact Htp0)
      Q10 Q11 Q12 Q13 HCH
      ltac:(rewrite Usp; dm (c_sp1 cx) 32; dm (c_sp1 cx) 16; lia) ltac:(rewrite Usp; unfold NEXT_STK; lia) ltac:(rewrite Usp; lia)
      ltac:(intros a Ha; apply J14; rewrite Usp in Ha; unfold NEXT_STK in Ha; lia)
      Hint HTl HI1 HOBJ
      ltac:(intros a Ha; unfold nx_may_write, awr_byte; right; right; left; exists t, 460;
            split; [exact Hint | split; [exact (table_new cx ly3 S3 W3 (ms_mem ms3) md3 t HAR3 Hbl)
                                       | change (req_size 460) with 460; unfold TX_SIZE in Ha; lia]])
      (proj1 (Hcells GO_CH ltac:(tauto))) (proj1 (Hcells GO_PAR ltac:(tauto))) (proj1 (Hcells GO_VAL ltac:(tauto)))
      ltac:(unfold GO_CH, GO_PAR; lia) ltac:(unfold GO_CH, GO_VAL; lia) ltac:(unfold GO_PAR, GO_VAL; lia)
      (proj1 (proj2 (Hcells GO_CH ltac:(tauto)))) (proj1 (proj2 (Hcells GO_PAR ltac:(tauto))))
      (proj1 (proj2 (Hcells GO_VAL ltac:(tauto))))
      (proj2 (proj2 (Hcells GO_CH ltac:(tauto)))) (proj2 (proj2 (Hcells GO_PAR ltac:(tauto))))
      (proj2 (proj2 (Hcells GO_VAL ltac:(tauto))))
      (Hshb GO_CH 98 ltac:(tauto) V98) (Hshb GO_PAR 100 ltac:(tauto) V100) (Hshb GO_VAL 102 ltac:(tauto) V102)). }
  intros W4 c4 Hwle (regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & HM2).
  rewrite Hnx in HM2. destruct HM2 as (Q10' & Hobj & HM2').
  lazymatch type of HM2' with _ /\ _ => destruct HM2' as (Hr1 & _) | _ => rename HM2' into Hr1 end.
  destruct HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (QP : forall r0 : bv 5, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv ->
               getr regs2 r0 = getr (ms_regs ms3) r0).
  { intros r0 Hr0. rewrite <- (QR r0 Hr0). exact (pres_regs _ _ HP2 r0 Hr0). }
  (* the bytes the call keeps; every lia below runs on the few facts it needs *)
  assert (Hsp1p : 0 <= c_sp1 cx) by ((clear - HF4096 HFceil Hceil Hsp1 GS; lia)).
  assert (HKC : forall a, 0 <= a < 2 ^ 64 -> gtracked cx fp a \/ (gF cx fp <= a < gF cx fp + 1024) ->
     ~ (t <= a < t + 460) -> ~ (a = gF cx fp + 784 \/ a = gF cx fp + 800 \/ a = gF cx fp + 816) ->
     aview SEGS (w_H W4) mem2 a = aview SEGS (w_H W3) (ms_mem msc) a).
  { intros a Ha Htr Hnt Hnc.
    assert (Hnx' : ~ nx_touch t (gF cx fp + GO_CH) (gF cx fp + GO_PAR) (gF cx fp + GO_VAL) a)
      by ((clear - Hnt Hnc; unfold nx_touch, TX_SIZE, GO_CH, GO_PAR, GO_VAL; lia)).
    destruct Htr as [[Hs | [(b & n & Hin & Hb) | [Hf | Hsh]]] | Hf].
    - (apply K1; [clear - Hs Ha Hceil Hsp1 GS; lia | rewrite Usp; clear - Hs; unfold NEXT_STK; lia | exact Hnx']).
    - (replace a with (b + (a - b)) by ring; apply (K2 b n (a - b));
        [ rewrite Hbl; apply in_app_iff; left; exact Hin
        | clear - Hb; lia
        | replace (b + (a - b)) with a by ring; exact Hnx' ]).
    - (apply (K4 GE_CID fp a Hfin); [|exact Hnx'];
      left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, fsb4; clear - Hf; lia).
    - (apply (K4 GE_CID fp a Hfin); [|exact Hnx'];
      right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA, fsb4; change (1024 / 8) with 128; rewrite <- HSH;
      clear - Hsh; lia).
    - (apply (K4 GE_CID fp a Hfin); [|exact Hnx'];
      left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, fsb4; clear - Hf; lia). }
  assert (HKT : forall a, gtracked cx fp a -> ~ gwr cx fp a ->
     aview SEGS (w_H W4) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Htr Hw.
    assert (Ha : 0 <= a < 2 ^ 64)
      by ((eapply gtracked_rng; [exact HB | exact HF4096 | exact HFceil | exact H47 | exact Hsp1p | exact Htr])).
    assert (Hw' : ~ (a = gF cx fp + 784 \/ a = gF cx fp + 800 \/ a = gF cx fp + 816 \/
                     a = gSH cx fp + 98 \/ a = gSH cx fp + 100 \/ a = gSH cx fp + 102))
      by ((clear - Hw; intros Hq; apply Hw; unfold gwr, GO_CH, GO_PAR, GO_VAL; lia)).
    rewrite (HKC a Ha (or_introl Htr)).
    - exact (HKA a Ha Hw').
    - destruct Htr as [Hs | [(b & n & Hin & Hb) | [Hf | Hsh]]].
      + (clear - Hs HTc Hceil Hsp1 GS; lia).
      + pose proof (table_sep cx ly3 S3 W3 (ms_mem ms3) md3 t b n HAR3 Hbl Hin) as Hd. (clear - Hb Hd; lia).
      + (clear - Hf HdTF; lia).
      + (clear - Hsh HTapp HSHr; unfold in_app, kLowShadowBeg, kHighMemBeg in HTapp; lia).
    - (clear - Hw'; lia). }
  assert (HV1 : forall v0, v0 = 98 \/ v0 = 100 \/ v0 = 102 ->
     aview SEGS (w_H W4) mem2 (gSH cx fp + v0) = aview SEGS (w_H W3) (ms_mem msc) (gSH cx fp + v0)).
  { intros v0 Hv0. apply HKC.
    - (clear - Hv0 HSHr; lia).
    - left. right; right; right. (clear - Hv0; lia).
    - (clear - Hv0 HTapp HSHr; unfold in_app, kLowShadowBeg, kHighMemBeg in HTapp; lia).
    - (clear - Hv0 Hsep; lia). }
  assert (HSHK : forall j, 0 <= j < 104 -> j <> 98 -> j <> 100 -> j <> 102 ->
     aview SEGS (w_H W4) (ms_mem (mkst regs2 (getr (ms_regs msc) 1) mem2 (seg_rom SEGS))) (gSH cx fp + j) =
     aview SEGS (w_H W3) (ms_mem ms3) (gSH cx fp + j)).
  { intros j Hj H98 H100 H102. cbn [ms_mem mkst]. apply HKT.
    - right; right; right. (clear - Hj; lia).
    - intros Hq. unfold gwr, GO_UNSET, GO_CH, GO_PAR, GO_VAL in Hq. (clear - Hq Hj H98 H100 H102 Hsep; lia). }
  assert (V98' : aview SEGS (w_H W4) (ms_mem (mkst regs2 (getr (ms_regs msc) 1) mem2 (seg_rom SEGS))) (gSH cx fp + 98) = Some 1)
    by (cbn [ms_mem mkst]; rewrite (HV1 98 (or_introl eq_refl)); exact V98).
  assert (V100' : aview SEGS (w_H W4) (ms_mem (mkst regs2 (getr (ms_regs msc) 1) mem2 (seg_rom SEGS))) (gSH cx fp + 100) = Some 1)
    by (cbn [ms_mem mkst]; rewrite (HV1 100 (or_intror (or_introl eq_refl))); exact V100).
  assert (V102' : aview SEGS (w_H W4) (ms_mem (mkst regs2 (getr (ms_regs msc) 1) mem2 (seg_rom SEGS))) (gSH cx fp + 102) = Some 1)
    by (cbn [ms_mem mkst]; rewrite (HV1 102 (or_intror (or_intror eq_refl))); exact V102).
  destruct (gshadow_set3 cx fp W3 ms3 W4 (mkst regs2 (getr (ms_regs msc) 1) mem2 (seg_rom SEGS)) GSH_sched 1 1 1
    HSHW GSH_sched_len HSHK V98' V100' V102') as (HSH2 & HSL2).
  apply (HTB cx fp k acc ly3 S3 W4 (mkst regs2 (getr (ms_regs msc) 1) mem2 (seg_rom SEGS)) md2 HB HJ2 Hfr HMLE).
  exists i, t, T, us, r, c, p, v, T'.
  split.
  { (eapply tcom_keep; [exact HF4096 | exact HFceil | exact HFapp | exact Hceil | exact Hsp1 | exact HIN | exact HT
      | cbn [ms_pc_val mkst]; exact Hra | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | repeat split; apply QP; cbv; tauto | exact Hi
      | transitivity (getr (ms_regs ms3) 18); [apply QP; cbv; tauto | exact R18]
      | exact HKT | exact HSH2 | exact HSL2 ]). }
  split; [exact Hm|]. split; [transitivity (getr (ms_regs ms3) 19); [apply QP; cbv; tauto | exact R19]|].
  split; [exact Hsch|]. split; [exact Hnx|]. split; [exact Q10'|].
  split; [exact (obj_gtab cx ly3 S3 W4 (mkst regs2 (getr (ms_regs msc) 1) mem2 (seg_rom SEGS)) t T' Hint Ht0 FLT' Hobj)|].
  split; [exact Hlus|].
  split.
  { eapply gfarr_keep; [exact Hus|]. intros a Ha. rewrite Hlus in Ha. unfold GO_UNSET in Ha. change (Z.of_nat 144) with 144 in Ha.
    cbn [ms_mem mkst].
    (rewrite HKC; [| apply HFX; clear - Ha; lia | right; clear - Ha; lia | clear - Ha HdTF; lia | clear - Ha; lia]).
    (apply HKA; [apply HFX; clear - Ha; lia|]; clear - Ha Hsep; lia). }
  intros Hr. destruct (Hr1 Hr) as (C1v & C2v & C3v). split; [exact C1v|]. split; [exact C2v | exact C3v].
Qed.


End c.
End b.
End a.
