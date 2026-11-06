(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: parse_items image B', segment ENTRY + EPILOGUE, rebound to the batch kit 240b06ed4fd4
   (PRH_FnParse.v ed236011cf99:360-466, tparse_items_specX d CTX CTX0 CW): no DW, the cursor set CW with its two entry
   premises prh_cw_entry / wild_room (pi_ent's last two conjuncts), the post at fpostWFbm (wbudget CW 0). The journal at
   the entry is the EMPTY-budget one from S (ajournal_x = ajournal_xw .. []), so the head's spec gets WS0 = [] and
   wbudget CW 0 [] (wfresh of [] is 0); skip_ws (tskip_ws_specX, unbudgeted) is called at that empty budget by the old
   window rule and cited from lib/B/Prog/skip_ws_mn.v skip_ws_holds. The EPILOGUE is generic in the
   budget predicate (PItems_pres.v pi_epi_spec): rebase / unbase around its run (YCbqGwild). The depth refusal proves
   the batch kit's post: the OUTCOME clause, the ledger move at the granted trace, and the empty free order (PvB_Frees.v
   pvf_zero_foR).
   THE RE-HIDING MOVE: every segment here concludes YA0nH.SRr' at the zone YGcfRehidePost.RZ_cf (the post fpostWFbm is
   at wle'). The prologue and the skip_ws call free nothing, so they run plain over the journal at wle and lift once
   (YGcfRhLift.ra_rh_of_SRr in pie_core, YA0nH.SRr_SRr' under SRr'_bind in pie_call); the epilogue takes the journal at
   wle' (pi_epi_spec) and runs with the R runner. The post is the text's tpiP_Q (pi_post), built through tpiP_Q_of_R.
   rule 24: no function proved
   proves no function (kind: segment lemma of an existing walk; the top theorem that proves parse_items is not
   this file's) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YC80xf YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YI00 YI04 YI16 YK06 YK0o YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_Charge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB PItems_defs PItems_pres PItems_agr PItems_kept.
(* the travelling run position and live requests (the post-implication form (b)), and the B'
   skip_ws (lib/B/Prog/skip_ws_mn.v skip_ws_holds), cited at the skip_ws call *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_posb skip_ws_mn.
(* The batch kit's budgeted journal (YCbqGwild) and PValueB's leaf free order (lib/B/Prog/PvB_Frees.v pvf_zero_foR, by path) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Frees.
(* the re-hiding relation (YA0nH), its step lemmas (YSRrG), the lift of a plain segment (YGcfRhLift) and the hull meters
   (PresetHullBudget) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

From Stdlib Require Import FunctionalExtensionality.

(* ---- The kit's post body is STABLE (PItems_pres.v pi_Qstable): it reads memory only through rdW and ignores the model ---- *)
Section stab. Context {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive} {PIi : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Lemma pi_post_stable : forall (B : asyms) ly0 S0 d o tb text len p q v Lam peak cnt fail ran most own kr,
  pi_Qstable (pi_post B ly0 S0 d o tb text len p q v Lam peak cnt fail ran most own kr).
Proof.
intros B ly0 S0 d o tb text len p q v Lam peak cnt fail ran most own kr ly S Hp W regs m m' md md' Hm HQ.
assert (Em : mrestrict (w_H W) m' = mrestrict (w_H W) m) by (apply functional_extensionality; exact Hm).
unfold pi_post, tpiP_Q, tpiP_ASome, tpiP_ANone, prh_ledger, prh_glob, prh_most, prh_own, prh_hblock in *.
pattern (mrestrict (w_H W) m'). rewrite Em. exact HQ.
Qed.
End stab.

(* ---- the overlay stays normal across a straight-line run (YAkMemnorm.memnorm): a byte the run did not write is
   the old one, and a written byte is one the run could write, where the old overlay was already normal ---- *)
Lemma pie_memnorm_frame : forall (sg : list Segment) E rs (m m' : word -> option byte),
  YAkMemnorm.memnorm sg m -> frame_of E rs m m' ->
  (forall x : word, in_wrange E rs (bv_unsigned x) -> wview sg m x <> None) ->
  YAkMemnorm.memnorm sg m'.
Proof.
intros sg E rs m m' (Hi & Ht) HF HW.
assert (Ha : forall a : word, in_wrange E rs (bv_unsigned a) -> YAkMemnorm.ro_addr sg a = false /\
  (find_segment sg (bv_unsigned a) 1 <> None \/ bv_unsigned a < TASK_SIZE)).
{ intros a Hin. pose proof (HW a Hin) as W. unfold wview in W. revert W.
  destruct (m a) as [b0|] eqn:E0; intros W; [exact (conj (Hi a b0 E0) (Ht a b0 E0))|].
  unfold YAkMemnorm.ro_addr. revert W.
  destruct (find_segment sg (bv_unsigned a) 1) as [seg|]; intros W; [|exfalso; exact (W eq_refl)].
  revert W. destruct (seg_writable seg); intros W; [|exfalso; exact (W eq_refl)].
  split; [reflexivity | left; discriminate]. }
assert (Hdec : forall a, in_wrange E rs a \/ ~ in_wrange E rs a).
{ intros a. unfold in_wrange.
  destruct (Exists_dec (fun r => base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r) rs)
    as [Hx | Hx].
  - intros r. destruct (Z_le_gt_dec (base_val E (YP09.r_base r) + YP09.r_wlo r) a);
    destruct (Z_lt_ge_dec a (base_val E (YP09.r_base r) + YP09.r_whi r)); [left; lia | right; lia | right; lia | right; lia].
  - left. apply Exists_exists in Hx. exact Hx.
  - right. intros Hy. apply Hx. apply Exists_exists. exact Hy. }
split; intros x c Ex.
- destruct (Hdec (bv_unsigned x)) as [Hin | Hn]; [exact (proj1 (Ha x Hin))|]. rewrite (HF x Hn) in Ex. exact (Hi x c Ex).
- destruct (Hdec (bv_unsigned x)) as [Hin | Hn]; [exact (proj2 (Ha x Hin))|]. rewrite (HF x Hn) in Ex. exact (Ht x c Ex).
Qed.

Section mn. Context {fx : YK11.FPState}.
(* a byte a symbolic state's region may write is a byte the overlay can hold *)
Lemma pie_wrange_wview : forall sg val E ss (ms : machine_state) (H : word -> bool) (x : word),
  st_ok_pi sg val E ss (restrict H ms) -> in_wrange E (ss_mem ss) (bv_unsigned x) -> wview sg (ms_mem ms) x <> None.
Proof.
intros sg val E ss ms H x HS (r & Hin & Hx).
destruct (st_ok_mem_ok sg E _ _ HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & Hw & _).
specialize (Hw (bv_unsigned x - base_val E (YP09.r_base r)) ltac:(lia)).
replace (base_val E (YP09.r_base r) + (bv_unsigned x - base_val E (YP09.r_base r))) with (bv_unsigned x) in Hw by lia.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. cbn [ms_mem restrict] in Hw.
intros Hn. apply Hw. revert Hn. unfold wview, YK04.mrestrict.
destruct (H x); destruct (ms_mem ms x); intros Hn; first [discriminate Hn | exact Hn].
Qed.
End mn.

(* ==================================================================================================
   THE EPILOGUE, PI_O_EPI (0x87e88 .. 0x87ec4): a0 = s5, ra and s0 .. s11 reloaded from sp + 136 .. sp + 40,
   sp += 144, ret. Proved at the section's (current) float state; pi_epi_holds below is PItems_pres.v's
   pi_epi_spec at the image-B listing.
   ================================================================================================== *)
(* the frame words the epilogue reloads, as the extra atoms 32 .. 44 of the run's environment *)
Definition pie_saved : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition pie_extra (regs0 : bvmap 5 word) : list word := map (fun r => getr regs0 r) pie_saved.
Definition pie_frame_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 40 144 0 0
    [YP09.mkChunk 136 (CVal 8 (SOff 32 0)); YP09.mkChunk 128 (CVal 8 (SOff 33 0)); YP09.mkChunk 120 (CVal 8 (SOff 34 0));
     YP09.mkChunk 112 (CVal 8 (SOff 35 0)); YP09.mkChunk 104 (CVal 8 (SOff 36 0)); YP09.mkChunk 96 (CVal 8 (SOff 37 0));
     YP09.mkChunk 88 (CVal 8 (SOff 38 0)); YP09.mkChunk 80 (CVal 8 (SOff 39 0)); YP09.mkChunk 72 (CVal 8 (SOff 40 0));
     YP09.mkChunk 64 (CVal 8 (SOff 41 0)); YP09.mkChunk 56 (CVal 8 (SOff 42 0)); YP09.mkChunk 48 (CVal 8 (SOff 43 0));
     YP09.mkChunk 40 (CVal 8 (SOff 44 0))].
Definition pie_Bx : sv := SOff 32 0.

Section epi. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} {PIi : PrhImg}.
#[local] Notation PIB := (@PI_prog_B rc).
#[local] Notation segs := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable HL : Z.
Hypothesis LAWS : AR_laws_x segs B ARx HL.

Definition ss_epi : sstate :=
  mkSS (PI_AT (L := B_prog_listing) (PI := PIB) PI_O_EPI) sr_atoms [pie_frame_region] None
    (mkFacts [(2%nat, mkAF 0 (2 ^ 47) 4)] [] []).

Lemma pie_holds : forall (P : list (list Z) -> Prop) (fx0 : YK11.FPState) (d : nat) ly S Hp W mem md
  (regs0 : bvmap 5 word) e q v
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  lyc Sc Hpc Wc memc mdc k (regs : bvmap 5 word) res WS0,
  pi_ajR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 d e q v lyc Sc Hpc Wc memc mdc k WS0 -> P WS0 ->
  pi_epi_pre (fx := fx) fx0 regs0 W mem e q v Q lyc Sc Hpc Wc regs memc mdc res ->
  SRr' segs YGcfRehidePost.RZ_cf Wc
    (cfg_at (fx := fx) segs (VAL A_TEXT + PI_AT (L := B_prog_listing) (PI := PIB) PI_O_EPI) regs memc mdc)
    (fpostWFbm (fx := fx0) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs0 ly S Hp W mem md Q).
Proof.
intros P fx0 d ly S Hp W mem md regs0 e q v Q lyc Sc Hpc Wc memc mdc k regs res WS0 HJw HPW
  (Hfp & HMN & HFR & H21 & HQs & HQ).
unfold pi_ajR in HJw.
(* THE BUDGETED JOURNAL at wle': the run takes the empty-budget journal, rebased at the block's depot
   (YCbqGwild.ajournal_xw_rebaseR); HWD is the wild part's cover the step back needs (ajournal_xw_unbase0R) *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
destruct HFR as (Hsp & H3 & H4 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 & HWK & Hret & He0 & He16).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _).
pose proof Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold PI_FRAME in Hsp.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp. unfold bv_modulus in Rsp. change (spZ regs) with (bv_unsigned (getr regs 2)) in Hsp.
remember (Eimg (L := B_prog_listing) (PI := PIB) (Ereg regs (pie_extra regs0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E21 : ew E 21 = getr regs 21) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 21 21%bv eq_refl)).
assert (E32 : ew E 32 = getr regs0 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = getr regs0 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr regs0 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr regs0 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = getr regs0 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = getr regs0 20) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = getr regs0 21) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = getr regs0 22) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = getr regs0 23) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = getr regs0 24) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = getr regs0 25) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = getr regs0 26) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew E 44 = getr regs0 27) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HS : @st_ok_pi segs VAL fx E ss_epi
  (restrict (w_H Wc) (mkst (fx := fx) regs (Z_to_bv 64 (VAL A_TEXT + PI_AT (L := B_prog_listing) (PI := PIB) PI_O_EPI)) memc (seg_rom segs)))).
{ rewrite restrict_mkst_fx, HE. unfold ss_epi. apply pa_entry_st_ok_full; rewrite <- ?HE.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pie_frame_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    change (spZ regs) with (bv_unsigned (getr regs 2)) in *.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    Local Ltac pie_ck V Vm :=
      lazymatch type of Vm with val_mem _ _ _ _ ?val =>
      lazymatch goal with |- YP09.chunk_ok _ _ _ ?b (YP09.mkChunk ?off (CVal 8 ?ev)) =>
        apply (chunk_ok_val _ _ _ b off 8 ev val);
        [ cbn [sv_denot]; rewrite V, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | let Rr := fresh "Rr" in
          lazymatch val with bv_unsigned ?w => pose proof (bv_unsigned_in_range 64 w) as Rr end;
          unfold bv_modulus in Rr; cbn in Rr |- *; lia
        | zside | exact Vm ] end end.
    repeat apply Forall_cons; try apply Forall_nil.
    + pie_ck E32 V1.
    + pie_ck E33 V8.
    + pie_ck E34 V9.
    + pie_ck E35 V18.
    + pie_ck E36 V19.
    + pie_ck E37 V20.
    + pie_ck E38 V21.
    + pie_ck E39 V22.
    + pie_ck E40 V23.
    + pie_ck E41 V24.
    + pie_ck E42 V25.
    + pie_ck E43 V26.
    + pie_ck E44 V27.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    change (spZ regs) with (bv_unsigned (getr regs 2)) in *. change (2 ^ 4) with 16.
    repeat split; lia. }
clear HE.
assert (SHOK : sh_ok segs pie_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at.
change (w64 (VAL A_TEXT + PI_AT (L := B_prog_listing) (PI := PIB) PI_O_EPI))
  with (Z_to_bv 64 (VAL A_TEXT + PI_AT (L := B_prog_listing) (PI := PIB) PI_O_EPI)).
pose (RUN := @PI_RUNR fx rc SK B_prog_listing PL_prog_B PIB B prh_pst ARx HL LAWS).
paj_run_tok_x RUN HS HJ SHOK BAND_SPAN.
{ awr_ok_tac. }
pi_kept_of (@pa_segs rc B_prog_listing PIB) HFr (fun _ : Z => False) ltac:(fun h => cbn [ew ewset Nat.eqb] in h).
rename KEPT into K1.
assert (MN1 : YAkMemnorm.memnorm segs (ms_mem ms)).
{ apply (pie_memnorm_frame segs E _ memc (ms_mem ms) HMN HF).
  intros x (r & Hr & Hx). cbn [ss_mem ss_epi In] in Hr. destruct Hr as [<- | []]. cbn in Hx. lia. }
clear HF.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10.
prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23. prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25.
prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
(* the return makes no world step: the plain return rule, lifted (YA0nH.SRr_SRr') *)
apply (SRr_SRr' segs YGcfRehidePost.RZ_cf).
eapply (@paj_ret_at fx rc B_prog_listing PL_prog_B PIB Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold fpostWFbm, fpostWFb, YCbqGwild.fpostWF_xbR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?dd = _ /\ _ =>
  exists fx, lyc, Sc, Hpc, rg, m, dd, k, WS0 end.
unfold YK0s.ret_ok in Hret.
split; [rewrite R1, E32, Hret; reflexivity|].
split; [exact (proj1 Hfp)|]. split; [exact (proj2 Hfp)|].
split; [exact HPW|].
(* back from the rebased depot to the journal from S at WS0 (the run stored nothing) *)
split.
{ apply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) segs B prh_pst ARx (wle' segs YGcfRehidePost.RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (st_depot Sc) WS0); [|exact HWD].
  apply (ajournal_x_materializeR (SK := SK) segs B prh_pst ARx LAWS (@pa_segs_low rc B_prog_listing PIB)
    (wle' segs YGcfRehidePost.RZ_cf)). exact HJ. }
split.
{ intros a Ha Hf. rewrite K1 by (try tauto; change (spZ regs0) with (bv_unsigned (getr regs0 2)) in *;
    pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as R0; unfold bv_modulus in R0; cbn in R0; lia).
  exact (HWK a Ha Hf). }
split.
{ apply pi_aregs.
  - intros r Hr. unfold PI_KEPT in Hr.
    repeat (destruct Hr as [<- | Hr]; [first [rewrite R1, E32 | rewrite R3, E3, H3 | rewrite R4, E4, H4 | rewrite R8, E33
      | rewrite R9, E34 | rewrite R18, E35 | rewrite R19, E36 | rewrite R20, E37 | rewrite R21, E38 | rewrite R22, E39
      | rewrite R23, E40 | rewrite R24, E41 | rewrite R25, E42 | rewrite R26, E43 | rewrite R27, E44]; reflexivity |]).
    destruct Hr.
  - rewrite R2, Usp. change (spZ regs) with (bv_unsigned (getr regs 2)). rewrite Hsp.
    replace (bv_unsigned (getr regs0 2) - 144 + 144) with (bv_unsigned (getr regs0 2)) by lia.
    apply Z_to_bv_bv_unsigned. }
unfold fQmn. split; [|intros _; exact MN1].
apply (HQs lyc Sc Hpc Wc _ memc _ mdc).
- intros x. apply HFr. intros (r & Hin & Hr). cbn in Hin. destruct Hin as [<- | []]. cbn in Hr. lia.
- apply HQ. rewrite R10, E21. exact H21.
Qed.
End epi.

(* the epilogue at every float state: PItems_pres.v's pi_epi_spec at the image-B listing *)
Lemma pi_epi_holds : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} {PIi : PrhImg} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world (@pa_segs rc B_prog_listing (@PI_prog_B rc)) -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) (HL : Z),
  AR_laws_x (@pa_segs rc B_prog_listing (@PI_prog_B rc)) B ARx HL ->
  forall d : nat, pi_epi_spec (L := B_prog_listing) (PA := @PI_prog_B rc) (PL := PL_prog_B) B ARx SK d.
Proof.
intros rc ci cp RL PIi B ARx SK HL LAWS d P fxc fx0 ly S Hp W mem md regs0 e q v Q lyc Sc Hpc Wc memc mdc k regs res WS0
  HJ HPW HP.
exact (pie_holds (fx := fxc) B ARx SK HL LAWS P fx0 d ly S Hp W mem md regs0 e q v Q lyc Sc Hpc Wc memc mdc k regs res WS0
  HJ HPW HP).
Qed.

(* ==================================================================================================
   THE ENTRY BLOCK, PI_O_ENTRY .. PI_O_SKW0 (0x87a38 .. 0x87b20): the prologue (frame 144, ra and
   s0 .. s11 saved), the node's two UBSan checks and its shadow check, the type word (5 array / 6 object),
   q's alignment check, s0 = q + 16 and its shadow check, depth += 1 with its signed-overflow check, the
   depth store, s5 = -1, the depth-limit branch, q's shadow check, in->p += 1 with its pointer-overflow
   check, the store of in->p, and the call of skip_ws.
   ================================================================================================== *)
(* the shadow base and span, as the engine reads them (the GOT word and the shadow cell of the image) *)
Definition pie_Bx2 : sv := SOff 32 0.
(* atoms: 32 = SHADOW_OFF, 33 = in->p, 34 = in->end, 35 = in->depth *)
Definition pie_regions : smem :=
  [ stack_region 144; got_regionP; bcell_regionP 32;
    YP09.mkRegion (Some 10%nat) 0 16 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))];
    YP09.mkRegion (Some 10%nat) 16 24 16 20 [YP09.mkChunk 16 (CVal 4 (SOff 35 0))];
    YP09.mkRegion (Some 11%nat) 0 56 0 4 [] ].
Definition pie_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 24) 3);
            (11%nat, mkAF 4096 (2 ^ 47 - 56) 3); (12%nat, mkAF 0 1 0);
            (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 1 (2 ^ 62) 0);
            (34%nat, mkAF 1 (2 ^ 62) 0); (35%nat, mkAF 0 32 0) ] [] [].
(* the entry's listing offset, read off the instance's own maps (no address literal) *)
Definition PIE_K : Z := Eval vm_compute in (B_prog_sigma AS_parse_items - B_prog_val A_TEXT + PI_O_ENTRY).
Definition PIE_EPI : Z := Eval vm_compute in (B_prog_sigma AS_parse_items - B_prog_val A_TEXT + PI_O_EPI).
Definition PIE_HEAD : Z := Eval vm_compute in (B_prog_sigma AS_parse_items - B_prog_val A_TEXT + PI_O_HEAD).
Definition ss_ent : sstate := mkSS PIE_K sr_atoms pie_regions None pie_facts.
Definition pie_SH : list shent := [mkSHE 10 0 24; mkSHE 11 0 56].
Definition pie_extra2 (p ed dp : Z) : list word := map (Z_to_bv 64) [SHADOW_OFF; p; ed; dp].

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} {PIi : PrhImg}.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PLb := PL_prog_B.
#[local] Notation PIb := (@PI_prog_B rc).
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable HL : Z.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis PAL : PALib (L := Lb) (PI := PIb) B.

(* the two image words the entry block reads (the shadow GOT slot and the shadow cell) lie in the image *)
Lemma pie_obj_img : forall x a, (x = A_OBJ 0 \/ x = A_OBJ 12) -> VAL x <= a < VAL x + 8 -> in_img SEGS a.
Proof.
intros x a Hx Ha.
assert (H8 : forall g : Z, g <= a < g + 8 ->
  a = g \/ a = g + 1 \/ a = g + 2 \/ a = g + 3 \/ a = g + 4 \/ a = g + 5 \/ a = g + 6 \/ a = g + 7) by (intros; lia).
destruct Hx as [->| ->]; apply in_img_b_sound;
[ destruct (H8 (VAL (A_OBJ 0)) Ha) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]
| destruct (H8 (VAL (A_OBJ 12)) Ha) as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]] ];
vm_compute; reflexivity.
Qed.

(* a byte at or above the allocation ceiling is not an image byte, so the stack and the node (when it is in
   the caller's window) are apart from the GOT word and the shadow cell *)
Lemma pie_img_below : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
Proof. exact (@pa_segs_low rc Lb PIb). Qed.

(* the environment the entry run uses: the entry registers, then SHADOW_OFF, in->p, in->end, in->depth *)
Definition PIE_E (regs : bvmap 5 word) (p ed dp : Z) : env :=
  @Eimg rc Lb PIb (Ereg regs (pie_extra2 p ed dp)).

(* THE ENTRY STATE. Every premise below is a conjunct of the kit's rd_pre at the entry, or an ARx law applied to it;
   the two apartness premises on the node are the four prhReader_at places read off at the call site. *)
Lemma pie_st_ok : forall ly S Hp (W : world SEGS) (regs : bvmap 5 word) mem md (q v p ed dp : Z) (o : bool),
  ARx ly S Hp W mem md ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v -> getr regs 12 = w64 (if o then 1 else 0) ->
  val_mem SEGS (rdW W mem) q 8 p -> val_mem SEGS (rdW W mem) (q + 8) 8 ed ->
  val_mem SEGS (rdW W mem) (q + 16) 4 dp -> rd_rw SEGS (rdW W mem) q 24 -> q mod 8 = 0 ->
  1 <= p < 2 ^ 62 -> 1 <= ed < 2 ^ 62 -> 0 <= dp <= 32 ->
  4096 <= v -> v mod 8 = 0 -> v + 56 <= 2 ^ 47 -> amem_range v 56 -> rd_rw SEGS (rdW W mem) v 56 ->
  (q + 24 <= v \/ v + 56 <= q) ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  (v + 56 <= spZ regs - 144 \/ spZ regs <= v) ->
  2 ^ 46 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  (forall a, spZ regs - 144 <= a < spZ regs -> apresent (w_H W) mem a) ->
  spZ regs <= q -> q + 24 <= 2 ^ 47 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  @st_ok_pi SEGS VAL fx (PIE_E regs p ed dp) ss_ent
    (restrict (w_H W) (mkst (fx := fx) regs (Z_to_bv 64 (VAL A_TEXT + PIE_K)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS pie_Bx2 pie_SH (PIE_E regs p ed dp) (rdW W mem).
Proof.
intros ly S Hp W regs mem md q v p ed dp o HAR H10 H11 H12 Vp Ved Vdp Hqrw Hq8 Hp62 Hed62 Hdp
  Hv4096 Hv8 Hv47 Hvam Hvrw Hqv Hvimg Hvsp Hsplo Hsphi Hspal Hpres Hsq Hq47 Hqra Hvra.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hq4096 : 4096 <= q) by lia.
(* the GOT word and the shadow cell, from AR's constant law and PALib *)
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
pose proof (pal_got_cell B PAL) as HgcD.
assert (Hgot : IMG_LO_B <= VAL (A_OBJ 0) /\ VAL (A_OBJ 0) + 8 <= IMG_TOP_B)
  by exact (@pa_obj_img rc Lb PIb 0%nat ltac:(lia)).
assert (Hcell : IMG_LO_B <= VAL (A_OBJ 12) /\ VAL (A_OBJ 12) + 8 <= IMG_TOP_B)
  by exact (@pa_obj_img rc Lb PIb 12%nat ltac:(lia)).
(* the image hull, read from its generated names (no copied literal) *)
assert (HIMG : 0 <= IMG_LO_B /\ IMG_TOP_B < 2 ^ 46) by (unfold IMG_LO_B, IMG_TOP_B; lia).
(* the two image words are apart from the cursor (the cursor is on the stack) and from the node (premise) *)
assert (Hqimg : forall a, q <= a < q + 24 -> ~ in_img SEGS a)
  by (intros a Ha Hin; pose proof (pie_img_below a Hin); unfold kLowMemEnd in *; lia).
assert (Hqapart : forall x, (x = A_OBJ 0 \/ x = A_OBJ 12) -> q + 24 <= VAL x \/ VAL x + 8 <= q).
{ intros x Hx. destruct (Z_le_gt_dec (q + 24) (VAL x)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (VAL x + 8) q) as [H2|H2]; [right; exact H2|]. exfalso.
  destruct (Z_le_gt_dec q (VAL x)) as [H3|H3].
  - exact (Hqimg (VAL x) ltac:(lia) (pie_obj_img x (VAL x) Hx ltac:(lia))).
  - exact (Hqimg q ltac:(lia) (pie_obj_img x q Hx ltac:(lia))). }
assert (Hvapart : forall x, (x = A_OBJ 0 \/ x = A_OBJ 12) -> v + 56 <= VAL x \/ VAL x + 8 <= v).
{ intros x Hx. destruct (Z_le_gt_dec (v + 56) (VAL x)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (VAL x + 8) v) as [H2|H2]; [right; exact H2|]. exfalso.
  destruct (Z_le_gt_dec v (VAL x)) as [H3|H3].
  - exact (Hvimg (VAL x) ltac:(lia) (pie_obj_img x (VAL x) Hx ltac:(lia))).
  - exact (Hvimg v ltac:(lia) (pie_obj_img x v Hx ltac:(lia))). }
assert (Hspimg : forall a, spZ regs - 144 <= a < spZ regs -> ~ in_img SEGS a)
  by (intros a Ha Hin; pose proof (pie_img_below a Hin); unfold kLowMemEnd in *; lia).
assert (Hspapart : forall x, (x = A_OBJ 0 \/ x = A_OBJ 12) -> spZ regs <= VAL x \/ VAL x + 8 <= spZ regs - 144).
{ intros x Hx. destruct (Z_le_gt_dec (spZ regs) (VAL x)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (VAL x + 8) (spZ regs - 144)) as [H2|H2]; [right; exact H2|]. exfalso.
  destruct (Z_le_gt_dec (spZ regs - 144) (VAL x)) as [H3|H3].
  - exact (Hspimg (VAL x) ltac:(lia) (pie_obj_img x (VAL x) Hx ltac:(lia))).
  - exact (Hspimg (spZ regs - 144) ltac:(lia) (pie_obj_img x (spZ regs - 144) Hx ltac:(lia))). }
set (E := PIE_E regs p ed dp).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (pie_extra2 p ed dp)) k)
  by (intros k Hk; unfold E, PIE_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (if o then 1 else 0))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 ed) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 dp) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E240 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (unfold E, PIE_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E252 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (unfold E, PIE_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some n) = w)
  by (intros n w Hn Hw; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hw).
assert (U10 : base_val E (Some 10%nat) = q) by (apply (VB 10%nat q E10); lia).
assert (U11 : base_val E (Some 11%nat) = v) by (apply (VB 11%nat v E11); lia).
assert (U240 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0))
  by (apply (VB (A_OBJ 0) _ E240); pose proof (@pa_val_range rc Lb PIb (A_OBJ 0)); lia).
assert (U252 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12))
  by (apply (VB (A_OBJ 12) _ E252); pose proof (@pa_val_range rc Lb PIb (A_OBJ 12)); lia).
assert (HBx : U E pie_Bx2 = SHADOW_OFF)
  by (unfold pie_Bx2; rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia); reflexivity).
assert (Hvrw' : forall oo, 0 <= oo < 4 -> writable_at SEGS (rdW W mem) (v + oo)) by (intros oo Hoo; apply Hvrw; lia).
assert (Hqrw' : forall oo, 0 <= oo < 24 -> writable_at SEGS (rdW W mem) (q + oo)) by (intros oo Hoo; apply Hqrw; lia).
assert (Usp2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
assert (W10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
assert (W11 : bv_unsigned (ew E 11) = v) by (rewrite E11; apply unsigned_lit_small; lia).
assert (W240 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0))
  by (rewrite E240; apply unsigned_lit_small; pose proof (@pa_val_range rc Lb PIb (A_OBJ 0)); lia).
assert (W252 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12))
  by (rewrite E252; apply unsigned_lit_small; pose proof (@pa_val_range rc Lb PIb (A_OBJ 12)); lia).
split.
- rewrite restrict_mkst_fx. unfold ss_ent. fold E. apply pa_entry_st_ok_full.
  + unfold E, PIE_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold pie_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite Usp2. split; [lia|]. split; [lia|]. split; [|constructor].
      intros oo Hoo. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite U240. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [ cbn [sv_denot]; rewrite E252, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (@pa_val_range rc Lb PIb (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite U252. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    * rewrite U10. split; [lia|]. split; [lia|].
      split; [intros oo Hoo; apply Hqrw'; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ q 0 8 (SOff 33 0) p);
         [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Vp.
      -- apply (chunk_ok_val SEGS E _ q 8 8 (SOff 34 0) ed);
         [ cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Ved].
    * rewrite U10. split; [lia|]. split; [lia|].
      split; [intros oo Hoo; apply Hqrw'; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ q 16 4 (SOff 35 0) dp);
      [ cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vdp].
    * rewrite U11. split; [lia|]. split; [lia|]. split; [|constructor].
      intros oo Hoo. apply Hvrw'. lia.
  + apply pairwise_disjoint_of_extents.
    unfold pie_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Usp, W10, W11, W240, W252.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    pose proof (Hqapart (A_OBJ 0) ltac:(left; reflexivity)) as Dq0.
    pose proof (Hqapart (A_OBJ 12) ltac:(right; reflexivity)) as Dq12.
    pose proof (Hvapart (A_OBJ 0) ltac:(left; reflexivity)) as Dv0.
    pose proof (Hvapart (A_OBJ 12) ltac:(right; reflexivity)) as Dv12.
    pose proof (Hspapart (A_OBJ 0) ltac:(left; reflexivity)) as Ds0.
    pose proof (Hspapart (A_OBJ 12) ltac:(right; reflexivity)) as Ds12.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pie_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, E12, E32, E33, E34, E35, !unsigned_lit_small by (unfold SHADOW_OFF; try lia; destruct o; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; try lia; destruct o; cbn; lia.
- unfold sh_ok, pie_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E pie_Bx2 10 q 24 q 0 24 Hqra HBx);
    [ rewrite (U_atom E 10 q E10) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E pie_Bx2 11 v 56 v 0 56 Hvra HBx);
    [ rewrite (U_atom E 11 v E11) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* WHERE THE NODE LIVES (PRH_FnReader.v prhReader_at's four places: a harness block's user bytes, another live
   allocator block, a live fake frame of the entry state, the caller's window), read off for the entry run: its
   bytes are not image bytes, it is apart from the 144-byte frame below sp, and the run may write it (the window or
   a block in FP, awr_byte; a fake frame in FP, YC80xf's wr_fp_frame) *)
Lemma pie_v_place : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own (regs0 : bvmap 5 word) e v STK q,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs0 e v 56 ->
  YM05.alloc_ceiling <= spZ regs0 - STK -> 144 <= STK -> 0 <= e ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) /\
  (v + 56 <= spZ regs0 - 144 \/ spZ regs0 <= v) /\
  (forall a, v <= a < v + 56 ->
     awr_byte (STK + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly S) (ablocks B ly S) ly [] a \/
     wr_fp_frame (rd_fp q v) S ly a).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v STK q HAR HLED Hat Hstk H144 He.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
assert (HinFP : forall a, v <= a < v + 56 -> inFP (rd_fp q v) a)
  by (intros a Ha; exists (v, v + 56); split; [right; right; left; reflexivity | cbn [fst snd]; lia]).
(* a block of the entry state that holds the node's bytes *)
assert (HB : forall b m, In (b, m) (ablocks B ly S) -> b <= v -> v + 56 <= b + req_size m ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) /\ (v + 56 <= spZ regs0 - 144 \/ spZ regs0 <= v) /\
  (forall a, v <= a < v + 56 ->
     awr_byte (STK + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly S) (ablocks B ly S) ly [] a \/
     wr_fp_frame (rd_fp q v) S ly a)).
{ intros b m Hin H1 H2.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hin) as (_ & H4096 & Hc & _).
  split; [intros a Ha; apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m a HAR Hin); lia|].
  split; [left; lia|].
  intros a Ha. left. right. left. split; [exact (HinFP a Ha)|]. exists b, m. split; [exact Hin | lia]. }
destruct Hat as [(a0 & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- pose proof HLED as HF. apply prh_ledger_blocks in HF. pose proof (proj1 (Forall_forall _ _) HF (a0, k) Hin) as (Hk & Hblk & _).
  cbn [fst snd] in Hk, Hblk. apply (HB _ _ Hblk); [lia|]. unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
- apply (HB _ _ Hin); [lia|]. unfold req_size. destruct (Z.eqb_spec m 0); lia.
- destruct (frames_bounds_x _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  split; [intros a Ha; apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos a HAR Hin); lia|].
  split; [left; lia|].
  intros a Ha. right. split; [exact (HinFP a Ha)|]. exists cid, pos. split; [exact Hin|].
  unfold in_zr, frame_rng. cbn [fst snd]. lia.
- split; [intros a Ha Him; pose proof (pie_img_below a Him); unfold kLowMemEnd in *; lia|].
  split; [right; lia|].
  intros a Ha. left. left. lia.
Qed.

(* A HARNESS HEAD IS NEVER A NODE BYTE: the head word of a live harness block (the 8 bytes at a - cf_head that
   prh_hblock reads) is apart from the node's 56 bytes, in each of the node's four places. Instance fact used:
   8 <= cf_head (alloc.c's HEAD is 16), so a block's head lies below its own user bytes. *)
Lemma pie_head_apart : forall ly S Hp (W : world SEGS) mem md Lam peak cnt fail ran most own (regs0 : bvmap 5 word) e v,
  8 <= cf_head ->
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs0 e v 56 -> YM05.alloc_ceiling <= spZ regs0 ->
  forall a k x, In (a, k) Lam -> a - cf_head <= x < a - cf_head + 8 -> ~ (v <= x < v + 56).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v H8 HAR HLED Hat Hsp a k x Hin Hx Hv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HLED as HND. apply prh_ledger_nodup in HND. pose proof HLED as HF. apply prh_ledger_blocks in HF.
pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk & Hblk & _ & _ & _). cbn [fst snd] in Hk, Hblk.
assert (Hrq : forall n, 0 <= n -> n <= req_size n) by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & H4096 & Hc & _).
destruct Hat as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hin' & Hnl & H1 & H2) | [(cid & pos & Hin' & H1 & H2) | (H1 & H2)]]].
- (* the node is in a harness block: the same one (its head is below its user bytes) or another (disjoint) *)
  destruct (Z.eq_dec a a') as [<- | Hne].
  + lia.
  + pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hblk' & _ & _ & _). cbn [fst snd] in Hk', Hblk'.
    assert (Hd : (a - cf_head, k + cf_head) <> (a' - cf_head, k' + cf_head)) by (intros E; injection E; lia).
    pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md _ _ _ _ HAR Hblk Hblk' Hd) as HD.
    unfold zdisjoint in HD. cbn [fst snd] in HD.
    assert (R1 : k + cf_head <= req_size (k + cf_head)) by (apply Hrq; lia).
    assert (R2 : k' + cf_head <= req_size (k' + cf_head)) by (apply Hrq; lia). lia.
- (* the node is in another allocator block, which is not this harness block *)
  assert (Hd : (a - cf_head, k + cf_head) <> (b, m)).
  { intros E. injection E as E1 E2. apply Hnl. replace (b + cf_head) with a by lia. replace (m - cf_head) with k by lia.
    exact Hin. }
  pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md _ _ _ _ HAR Hblk Hin' Hd) as HD.
  unfold zdisjoint in HD. cbn [fst snd] in HD.
  assert (R1 : k + cf_head <= req_size (k + cf_head)) by (apply Hrq; lia).
  assert (R2 : m <= req_size m) by (apply Hrq; lia). lia.
- (* the node is in a fake frame, apart from every block *)
  pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md _ _ cid pos HAR Hblk Hin') as HD.
  unfold zdisjoint in HD. cbn [fst snd] in HD.
  assert (R1 : k + cf_head <= req_size (k + cf_head)) by (apply Hrq; lia). lia.
- (* the node is in the caller's window, above every block *)
  assert (R1 : k + cf_head <= req_size (k + cf_head)) by (apply Hrq; lia). lia.
Qed.

(* THE LEDGER IS KEPT by a memory change that keeps alloc.c's seven statics (prh_pst: the five cells and #102's
   g_most / g_own_ran_out) and every live harness block's head word (the only bytes prh_ledger reads); at image B's
   statics (prh_img_B) *)
Lemma pie_ledger_kept : forall ly S Hp (W : world SEGS) m m' Lam peak cnt fail ran most own,
  prh_ledger (PI := prh_img_B) B ly S Hp W m Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  (forall a k x, In (a, k) Lam -> a - cf_head <= x < a - cf_head + 8 ->
     aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  prh_ledger (PI := prh_img_B) B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' Lam peak cnt fail ran most own HLG HST HHD.
pose proof HLG as V1. apply prh_ledger_live in V1. pose proof HLG as V2. apply prh_ledger_peak in V2.
pose proof HLG as V3. apply prh_ledger_count in V3. pose proof HLG as V4. apply prh_ledger_fail in V4.
pose proof HLG as V5. apply prh_ledger_ran in V5. pose proof HLG as Hb. apply prh_ledger_bounds in Hb.
(* the E sweep's two cells, g_most and g_own_ran_out, by their named projections *)
pose proof HLG as V6. apply prh_ledger_most in V6. pose proof HLG as V7. apply prh_ledger_own in V7.
pose proof HLG as HND. apply prh_ledger_nodup in HND. pose proof HLG as HF. apply prh_ledger_blocks in HF.
pose proof HLG as HP. apply prh_ledger_heads in HP.
assert (KS : forall b n x, In (b, n) (@prh_pst prh_img_B) -> b <= x < b + n ->
  aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x).
{ intros b n x Hin Hx. apply HST. apply Exists_exists. exists (b, n). split; [exact Hin|].
  unfold in_zr. cbn [fst snd]. lia. }
Local Ltac pie_inpst := unfold prh_pst; repeat (first [left; reflexivity | right]).
split; [|split; [exact HND | split; [|exact HP]]].
- unfold prh_glob, prh_most, prh_own. destruct V6 as (V6 & M6). destruct V7 as (V7 & O7).
  split; [|split; [|split; [|split; [|split; [|split; [split; [|exact M6] | split; [split; [|exact O7] | exact Hb]]]]]]];
  apply (pi_val_kept (L := Lb) (PI := PIb) (w_H W) m m'); try assumption; intros x Hx;
  [ apply (KS (@pi_g_live prh_img_B) (Z.of_nat (@pi_gz_live prh_img_B)) x ltac:(pie_inpst)); lia
  | apply (KS (@pi_g_peak prh_img_B) (Z.of_nat (@pi_gz_peak prh_img_B)) x ltac:(pie_inpst)); lia
  | apply (KS (@pi_g_count prh_img_B) (Z.of_nat (@pi_gz_count prh_img_B)) x ltac:(pie_inpst)); lia
  | apply (KS (@pi_g_fail prh_img_B) (Z.of_nat (@pi_gz_fail prh_img_B)) x ltac:(pie_inpst)); lia
  | apply (KS (@pi_g_ran_out prh_img_B) (Z.of_nat (@pi_gz_ran_out prh_img_B)) x ltac:(pie_inpst)); lia
  | apply (KS (@pi_g_most prh_img_B) (Z.of_nat (@pi_gz_most prh_img_B)) x ltac:(pie_inpst)); clear - Hx; lia
  | apply (KS (@pi_g_own_ran_out prh_img_B) (Z.of_nat (@pi_gz_own_ran_out prh_img_B)) x ltac:(pie_inpst));
    clear - Hx; lia ].
- apply Forall_forall. intros [a k] Hin. pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk & Hbl & Hhp & Hal & Hv).
  cbn [fst snd] in *. split; [exact Hk|]. split; [exact Hbl|]. split; [exact Hhp|]. split; [exact Hal|].
  apply (pi_val_kept (L := Lb) (PI := PIb) (w_H W) m m'); [|exact Hv].
  intros x Hx. apply (HHD a k x Hin). cbn in Hx. lia.
Qed.

(* the entry environment's atoms, as the run and its post read them *)
Lemma pie_E_low : forall regs p ed dp k, (k < A_TEXT)%nat ->
  ew (PIE_E regs p ed dp) k = ew (Ereg regs (pie_extra2 p ed dp)) k.
Proof. intros regs p ed dp k Hk. unfold PIE_E. apply Eimg_low. exact Hk. Qed.
Lemma pie_E_reg : forall regs p ed dp (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (PIE_E regs p ed dp) n = getr regs r.
Proof.
intros regs p ed dp n r Hn Hr. rewrite pie_E_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hr).
Qed.
Lemma pie_E_extra : forall regs p ed dp j, (j < 4)%nat ->
  ew (PIE_E regs p ed dp) (32 + j) = nth j (pie_extra2 p ed dp) (Z_to_bv 64 0).
Proof. intros regs p ed dp j Hj. rewrite pie_E_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma pie_pc : @pa_sigma rc Lb PIb AS_parse_items = VAL A_TEXT + PIE_K.
Proof. vm_compute. reflexivity. Qed.

(* THE DEPTH TEST at 0x87aec, `blt a1 (= 32), a0 (= depth + 1)`: below the limit it is not taken (the 32 values
   decided by computation), at the limit d = 32 it is *)
Lemma pie_lt_small : forall n : nat, (n < 32)%nat ->
  branch_taken BC_LT (Z_to_bv 64 32) (Z_to_bv 64 (Z.of_nat n + 1)) = false.
Proof. intros n Hn. do 32 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. Qed.
Lemma pie_lt_32 : branch_taken BC_LT (Z_to_bv 64 32) (Z_to_bv 64 (Z.of_nat 32 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.
(* the run's depth atom (35) and the test's two operands, at the entry environment *)
Lemma pie_den35 : forall regs p ed dp, 0 <= dp < 2 ^ 63 ->
  sv_denot (PIE_E regs p ed dp) (SOff 35 1) = Z_to_bv 64 (dp + 1).
Proof.
intros regs p ed dp Hdp. cbn [sv_denot].
change (ew (PIE_E regs p ed dp) 35) with (ew (PIE_E regs p ed dp) (32 + 3)).
rewrite (pie_E_extra regs p ed dp 3) by lia. cbn [nth pie_extra2 map].
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma pie_den33 : forall regs p ed dp, 0 <= p < 2 ^ 63 ->
  sv_denot (PIE_E regs p ed dp) (SOff 33 0) = Z_to_bv 64 p.
Proof.
intros regs p ed dp Hp. cbn [sv_denot].
change (ew (PIE_E regs p ed dp) 33) with (ew (PIE_E regs p ed dp) (32 + 1)).
rewrite (pie_E_extra regs p ed dp 1) by lia. cbn [nth pie_extra2 map].
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma pie_den34 : forall regs p ed dp, 0 <= ed < 2 ^ 63 ->
  sv_denot (PIE_E regs p ed dp) (SOff 34 0) = Z_to_bv 64 ed.
Proof.
intros regs p ed dp Hed. cbn [sv_denot].
change (ew (PIE_E regs p ed dp) 34) with (ew (PIE_E regs p ed dp) (32 + 2)).
rewrite (pie_E_extra regs p ed dp 2) by lia. cbn [nth pie_extra2 map].
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
(* a register atom with offset 0: the entry register's own value *)
Lemma pie_den_reg : forall regs p ed dp (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (PIE_E regs p ed dp) (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr regs r)).
Proof.
intros regs p ed dp n r Hn Hr. cbn [sv_denot]. rewrite (pie_E_reg regs p ed dp n r Hn Hr), Z.add_0_r. reflexivity.
Qed.
Lemma pie_den32 : forall E, sv_denot E (SLit 32) = Z_to_bv 64 32.
Proof. intros E. reflexivity. Qed.
(* a byte of the zeroed node read as a 64-bit word: 0 *)
Lemma pie_zero_u64 : forall (m : word -> option byte) v off, garr8 SEGS m v (repeat 0 56) ->
  0 <= off -> off + 8 <= 56 -> rd_u64 SEGS m (v + off) 0.
Proof.
intros m v off HZ H0 H8. split; [lia|]. intros k Hk.
destruct (HZ (Z.to_nat off + k)%nat ltac:(rewrite repeat_length; lia)) as [V _].
rewrite nth_repeat in V. specialize (V 0%nat ltac:(lia)).
replace (v + Z.of_nat (Z.to_nat off + k) + Z.of_nat 0) with (v + off + Z.of_nat k) in V by lia.
rewrite V. unfold YO0f.le_byte.
rewrite !Zmod_0_l, !Z.shiftr_0_l, !Zmod_0_l. reflexivity.
Qed.


End ent.

(* the bytes the entry block may write: the 144-byte frame below the entry sp, the cursor's p field and depth word,
   the node's type word *)
Definition pie_wset (regs : bvmap 5 word) (q v a : Z) : Prop :=
  (spZ regs - 144 <= a < spZ regs) \/ (q <= a < q + 8) \/ (q + 16 <= a < q + 20) \/ (v <= a < v + 4).

(* the engine's own states, named: at the depth branch; past it (not taken) and at the skip_ws call; taken and at
   the epilogue *)
Definition PIE_SS_BR : sstate := Eval vm_compute in
  (sh_ss (fst (sym_runN_pi_tok B_prog_tpi B_prog_tw (run_K A_LIM pie_Bx2 pie_SH ss_ent) pie_Bx2 BAND_SPAN pie_SH
     FUEL ss_ent))).
Definition PIE_SS_NT : sstate := add_cond PIE_SS_BR (mkAC (neg_bc BC_LT) (SLit 32) (SOff 35 1)).
Definition PIE_SS_CALL : sstate := Eval vm_compute in
  (sh_ss (fst (sym_runN_pi_tok B_prog_tpi B_prog_tw (run_K A_LIM pie_Bx2 pie_SH PIE_SS_NT) pie_Bx2 BAND_SPAN pie_SH
     FUEL PIE_SS_NT))).
Definition PIE_SS_TK : sstate := add_cond PIE_SS_BR (mkAC BC_LT (SLit 32) (SOff 35 1)).
Definition PIE_SS_REF : sstate := Eval vm_compute in
  (sh_ss (fst (sym_run_toN_pi_tok B_prog_tpi B_prog_tw (run_K A_LIM pie_Bx2 pie_SH PIE_SS_TK) pie_Bx2 BAND_SPAN
     pie_SH FUEL PIE_EPI PIE_SS_TK))).

(* the write permission of every stretch of the entry block (the same six regions, so one tactic) *)
Ltac pie_wr B2 B10 B11 Hvwr :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
  intros a (r & Hr & Ha);
  try unfold ss_ent, pie_regions, stack_region, got_regionP, bcell_regionP in Hr;
  cbn [ss_mem add_cond] in Hr;
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?B2, ?B10, ?B11 in Ha;
  [ left; left; lia | lia | lia | left; left; lia | left; left; lia | apply Hvwr; lia ].

(* the ledger does not move on the refusal path, at the batch kit's ledger move (PRH_FnParse.v rd_ledger_move: g_most, and the
   granted trace, empty here since the depth refusal makes no call; PItems_head.v's hd_move_id, restated here so this file
   does not import the head segment) *)
Lemma pie_move_id : forall {cp : CfParams} Lam peak cnt fail ran most, 0 <= cnt < 2 ^ 64 -> 0 <= Ledger.lsum Lam <= peak ->
  rd_ledger_move Lam peak cnt fail ran most [] [] [] [] Lam peak cnt fail ran.
Proof.
intros cp Lam peak cnt fail ran most Hcnt Hsum. unfold rd_ledger_move. cbn [PjGrammar.calls lszR nliveR hpeakR map length].
split; [split; [intros i Hi; lia | split; [left; reflexivity | intros i Hi; lia]]|].
split; [rewrite Z.add_0_r; symmetry; apply Z.mod_small; lia|].
split; [split; [intros H; lia | intros _; reflexivity]|].
split; [cbn [app]; apply Permutation_refl|].
split; [apply Permutation_refl|].
split; [reflexivity|]. unfold prh_refused_peak. cbn [List.seq map fold_right]. lia.
Qed.

(* the entry's empty budget is within every cursor set's room: wfresh of [] is 0 *)
Lemma pie_wbudget_nil : forall CW : list (list Z), YCbqGwild.wbudget CW 0 [].
Proof. intros CW. unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn. lia. Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PLb := PL_prog_B.
#[local] Notation PIb := (@PI_prog_B rc).
#[local] Notation SEGS := (@pa_segs rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation VAL := (@pa_val rc B_prog_listing (@PI_prog_B rc)).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable HL : Z.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis PAL : PALib (L := Lb) (PI := PIb) B.
Variable SK : YI16.sink_head.
Variable d : nat.

(* a journal at wle is one at wle' SEGS RZ_cf (YCbqG.ajournal_xwR_mono, YA0nH.wle_wle'): the entry segment frees
   nothing, so it keeps its journal at wle and hands it on at wle' where a spec takes that form *)
Lemma pie_aj_lift {ly S Hp W mem md regs0 dd e q v lyc Sc Hpc Wc memc mdc k WS} :
  pi_aj B ARx SK ly S Hp W mem md regs0 dd e q v lyc Sc Hpc Wc memc mdc k WS ->
  pi_ajR B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) ly S Hp W mem md regs0 dd e q v lyc Sc Hpc Wc memc mdc k WS.
Proof.
intros HJ. unfold pi_aj, pi_ajR in *.
exact (ajournal_xwR_mono (SK := SK) SEGS B _ ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* generic in the post's budget predicate P: the entry block runs at the EMPTY budget (ajournal_x_init_W), so both arms
   take the journal at WS0 = [] *)
Lemma pie_core : forall (P : list (list Z) -> Prop) ly S Hp (W : world SEGS) (regs : bvmap 5 word) mem md ch e q v text
  len p (tb : list Z) (o : bool) Lam peak cnt fail ran most own kr,
  afn_pre_x SEGS B ARx (STK_parse_items d) ly S Hp W regs mem md ch -> YAkMemnorm.memnorm SEGS mem ->
  fwin ly W regs mem e -> frm_zero (@YK11.fp_csr fx) ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v -> getr regs 12 = w64 (if o then 1 else 0) ->
  pj_in_okR SEGS (rdW W mem) q text len p (Z.of_nat d) tb ->
  spZ regs <= q -> q + 24 <= spZ regs + e ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF q 24 ->
  prhPv_node B (STK_parse_items d) e ly S W regs mem Lam v ->
  (q + 24 <= v \/ v + 56 <= q) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  room_live_cf S -> 8 <= cf_head -> 144 <= STK_parse_items d ->
  (* the refusal arm, at the epilogue (closed by pie_refuse) *)
  (forall (ms' : machine_state) (md' : Model) (k' : Z),
     st_ok_pi SEGS VAL (PIE_E regs p (text + len) (Z.of_nat d)) PIE_SS_REF (restrict (w_H W) ms') ->
     pi_aj B ARx SK ly S Hp W mem md regs d e q v ly S Hp W (ms_mem ms') md' k' [] ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ pie_wset regs q v a ->
        aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W (ms_mem ms')) -> YAkMemnorm.memnorm SEGS (ms_mem ms') ->
     d = PjGrammar.MAXD ->
     SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg ms' md')
       (fpostWFbm (fx := fx) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs ly S Hp W mem md
          (pi_post B ly S d o tb text len p q v Lam peak cnt fail ran most own kr))) ->
  (* the main arm, at the skip_ws call (closed by pie_call) *)
  (forall (ms' : machine_state) (md' : Model) (k' : Z),
     st_ok SEGS (PIE_E regs p (text + len) (Z.of_nat d)) (setpc PIE_SS_CALL (@pa_sigma rc Lb PIb AS_skip_ws))
       (restrict (w_H W) ms') ->
     pi_aj B ARx SK ly S Hp W mem md regs d e q v ly S Hp W (ms_mem ms') md' k' [] ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ pie_wset regs q v a ->
        aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W (ms_mem ms')) -> YAkMemnorm.memnorm SEGS (ms_mem ms') ->
     (d < PjGrammar.MAXD)%nat ->
     SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg ms' md')
       (fpostWFbm (fx := fx) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs ly S Hp W mem md
          (pi_post B ly S d o tb text len p q v Lam peak cnt fail ran most own kr))) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (cfg_at (fx := fx) SEGS (@pa_sigma rc Lb PIb AS_parse_items) regs mem md)
    (fpostWFbm (fx := fx) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs ly S Hp W mem md
       (pi_post B ly S d o tb text len p q v Lam peak cnt fail ran most own kr)).
Proof.
intros P ly S Hp W regs mem md ch e q v text len p tb o Lam peak cnt fail ran most own kr HAFN HMN HWIN
  HFRM H10 H11 H12 HIN Hsq Hqe Hqra HNODE Hqv HLED HRL H8 HSTK CREF CCALL.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hastk & Hpres & Hch & HQT).
pose proof Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof HIN as (Vp & Ved & Vdp & Hqrw & Hq8 & Ht0 & Htl & Hple & Hlen & Hsrc & Hdqt & Hd032).
pose proof HNODE as (Hv4096 & Hv8 & (Hvrw8 & Hvrw) & HZ & Hat & Hvam & Hvown & Hvra).
assert (F1 : YM05.alloc_ceiling <= spZ regs - STK_parse_items d) by lia.
destruct (pie_v_place B ARx HL LAWS ly S Hp W mem md Lam peak cnt fail ran most own regs e v (STK_parse_items d) q HAR HLED
  Hat F1 HSTK He0) as (Hvimg & Hvsp & Hvwr).
assert (F2 : 1 <= p < 2 ^ 62) by lia.
assert (F3 : 1 <= text + len < 2 ^ 62) by lia.
assert (F4 : 0 <= Z.of_nat d <= 32) by lia.
assert (F5 : v + 56 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; lia).
assert (F6 : 2 ^ 46 <= spZ regs) by lia.
assert (F7 : spZ regs <= 2 ^ 47) by lia.
assert (F8 : forall a, spZ regs - 144 <= a < spZ regs -> apresent (w_H W) mem a) by (intros a Ha; apply Hpres; lia).
assert (F9 : q + 24 <= 2 ^ 47) by lia.
destruct (pie_st_ok B ARx HL LAWS PAL ly S Hp W regs mem md q v p (text + len) (Z.of_nat d) o HAR H10 H11 H12 Vp Ved
  Vdp Hqrw Hq8 F2 F3 F4 Hv4096 Hv8 F5 Hvam Hvrw Hqv Hvimg Hvsp F6 F7 Hal F8 Hsq F9 Hqra Hvra) as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) SEGS B prh_pst ARx (STK_parse_items d) e (rd_fp q v)
  ly S Hp W regs mem md ch HAFN HWIN) as HJ.
assert (HEI : img_env VAL A_LIM (PIE_E regs p (text + len) (Z.of_nat d))) by (unfold PIE_E; apply Eimg_env).
set (EE := PIE_E regs p (text + len) (Z.of_nat d)) in *.
assert (B2 : bv_unsigned (ew EE 2) = spZ regs)
  by (unfold EE; rewrite (pie_E_reg regs p (text + len) (Z.of_nat d) 2 2%bv) by first [reflexivity | lia]; reflexivity).
assert (B10 : bv_unsigned (ew EE 10) = q)
  by (unfold EE; rewrite (pie_E_reg regs p (text + len) (Z.of_nat d) 10 10%bv) by first [reflexivity | lia];
      rewrite H10; apply unsigned_lit_small; lia).
assert (B11 : bv_unsigned (ew EE 11) = v)
  by (unfold EE; rewrite (pie_E_reg regs p (text + len) (Z.of_nat d) 11 11%bv) by first [reflexivity | lia];
      rewrite H11; apply unsigned_lit_small; lia).
(* the prologue frees nothing: a plain run over the journal at wle, lifted once (YGcfRhLift.ra_rh_of_SRr) *)
apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf).
unfold cfg_at. rewrite (pie_pc (rc := rc)). change (w64 (VAL A_TEXT + PIE_K)) with (Z_to_bv 64 (VAL A_TEXT + PIE_K)).
pose (RUN := @PI_RUNF fx rc SK Lb PLb PIb B prh_pst ARx HL LAWS).
pose (RUNTO := @PI_RUNTOF fx rc SK Lb PLb PIb B prh_pst ARx HL LAWS).
pose (BR := @paj_branch fx rc Lb PIb).
pose proof (fun x => pie_wrange_wview SEGS VAL EE _ _ (w_H W) x HS) as HWV1.
paj_run_tok_x RUN HS HJ SHOK BAND_SPAN; [pie_wr B2 B10 B11 Hvwr |].
rename HFr into HFr1. rename HG into HG1.
pose proof (pie_memnorm_frame SEGS EE _ mem _ HMN HF HWV1) as MN1. clear HF HWV1.
pi_kept_of (@pa_segs rc B_prog_listing (@PI_prog_B rc)) HFr1 (pie_wset regs q v) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?B2, ?B10, ?B11 in h;
  unfold pie_wset).
rename KEPT into K1.
psrr_branch_tok RUN BR HS SHOK BAND_SPAN.
- (* TAKEN: the raised depth exceeds 32, so d = MAXD and the block jumps to the epilogue with s5 = -1 *)
  rewrite pie_den32 in Hc. unfold EE in Hc. rewrite pie_den35 in Hc by lia.
  assert (Hd : d = PjGrammar.MAXD).
  { destruct (Nat.lt_ge_cases d 32) as [Hlt | Hge]; [rewrite (pie_lt_small d Hlt) in Hc; discriminate|].
    unfold PjGrammar.MAXD. lia. }
  pose proof (fun x => pie_wrange_wview SEGS VAL EE _ _ (w_H W) x HS) as HWV2.
  paj_run_to_tok_x RUNTO HS HJ SHOK BAND_SPAN PIE_EPI; [pie_wr B2 B10 B11 Hvwr |].
  rename HFr into HFr2. rename HG into HG2.
  pose proof (pie_memnorm_frame SEGS EE _ _ _ MN1 HF HWV2) as MN2. clear HF HWV2.
  pi_kept_of (@pa_segs rc B_prog_listing (@PI_prog_B rc)) HFr2 (pie_wset regs q v) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?B2, ?B10, ?B11 in h;
    unfold pie_wset).
  rename KEPT into K2.
  match type of HS with st_ok_pi _ _ _ ?st _ => replace st with PIE_SS_REF in HS by (vm_compute; reflexivity) end.
  apply SRr_ret. cbv beta.
  eapply (CREF _ _ _ HS HJ); [| | exact MN2 | exact Hd].
  + intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
  + intros x Hx. apply HG2. apply HG1. exact Hx.
- (* NOT TAKEN: d < MAXD, on to the skip_ws call *)
  rewrite pie_den32 in Hc. unfold EE in Hc. rewrite pie_den35 in Hc by lia.
  assert (Hd : (d < PjGrammar.MAXD)%nat).
  { destruct (Nat.eq_dec d 32) as [-> | Hne]; [rewrite pie_lt_32 in Hc; discriminate|]. unfold PjGrammar.MAXD. lia. }
  pose proof (fun x => pie_wrange_wview SEGS VAL EE _ _ (w_H W) x HS) as HWV2.
  paj_run_tok_x RUN HS HJ SHOK BAND_SPAN; [pie_wr B2 B10 B11 Hvwr |].
  rename HFr into HFr2. rename HG into HG2.
  pose proof (pie_memnorm_frame SEGS EE _ _ _ MN1 HF HWV2) as MN2. clear HF HWV2.
  pi_kept_of (@pa_segs rc B_prog_listing (@PI_prog_B rc)) HFr2 (pie_wset regs q v) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?B2, ?B10, ?B11 in h;
    unfold pie_wset).
  rename KEPT into K2.
  match type of HS with st_ok _ _ (setpc ?st _) _ => replace st with PIE_SS_CALL in HS by (vm_compute; reflexivity) end.
  apply SRr_ret. cbv beta.
  eapply (CCALL _ _ _ HS HJ); [| | exact MN2 | exact Hd].
  + intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
  + intros x Hx. apply HG2. apply HG1. exact Hx.
Qed.

(* a frame word the refusal state holds: the entry register r saved at sp + od (od in -104 .. -8) *)
Ltac pie_frw E RG0 B2 Hsp' D :=
  lazymatch goal with |- val_mem _ _ (spZ ?rg + ?o) 8 _ =>
    replace (spZ rg + o) with (bv_unsigned (ew E 2) + (o - 144)) by (rewrite B2, Hsp'; unfold PI_FRAME; lia);
    eapply (pi_field _ _ _ 2 _ _ _ _ _ _ (o - 144) 8%N _ _ RG0 eq_refl);
    [ cbn [Z.sub]; repeat (first [left; reflexivity | right])
    | exact D
    | match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as Rw;
        unfold bv_modulus in Rw; cbn in Rw |- *; lia end
    | cbn; lia ] end.

(* THE DEPTH-REFUSAL ARM, closed: d = MAXD, the run reached the epilogue with s5 = -1, and the kit's post holds with
   res = None, tr = [], D = [], the ledger unmoved, the depth word at 33 and the node freeable at depth 0 (its type
   word set, every other byte still zero). No allocator event: the live requests are the entry's (pi_live_nil) and the
   position transfer is pi_posb_post of the entry relation pi_posb_nil. The batch kit: at d = MAXD the all-granted run is the
   same refusal (jr_cont refuses before any call), so the granted trace is [] (the OUTCOME holds at the position i
   itself, and the ledger move's refusal peak is 0), and the free order is the empty list of the zeroed node
   (PvB_Frees.v pvf_zero_foR; jf_cont refuses too). Generic in the budget predicate P (any P with P []). The post is
   built through the text's record (tpiP_Q_of_R): no allocation, so the hull use is hull_used_refl; no call, so no call was
   refused (pi_grant_granted at ok = []). The journal is at wle (nothing freed); the epilogue takes it at wle'. *)
Lemma pie_refuse : forall (P : list (list Z) -> Prop) ly S Hp (W : world SEGS) (regs : bvmap 5 word) mem md ch e q v
  text len p (tb : list Z) (o : bool) Lam peak cnt fail ran most own kr (ms' : machine_state) (md' : Model) (k' : Z),
  P [] ->
  afn_pre_x SEGS B ARx (STK_parse_items d) ly S Hp W regs mem md ch ->
  fwin ly W regs mem e -> frm_zero (@YK11.fp_csr fx) ->
  getr regs 10 = w64 q -> getr regs 11 = w64 v -> getr regs 12 = w64 (if o then 1 else 0) ->
  pj_in_okR SEGS (rdW W mem) q text len p (Z.of_nat d) tb ->
  spZ regs <= q -> q + 24 <= spZ regs + e ->
  prhPv_node B (STK_parse_items d) e ly S W regs mem Lam v ->
  (q + 24 <= v \/ v + 56 <= q) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  room_live_cf S -> 8 <= cf_head -> 144 <= STK_parse_items d ->
  st_ok_pi SEGS VAL (PIE_E regs p (text + len) (Z.of_nat d)) PIE_SS_REF (restrict (w_H W) ms') ->
  pi_aj B ARx SK ly S Hp W mem md regs d e q v ly S Hp W (ms_mem ms') md' k' [] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pie_wset regs q v a ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
  mem_grows (rdW W mem) (rdW W (ms_mem ms')) -> YAkMemnorm.memnorm SEGS (ms_mem ms') ->
  d = PjGrammar.MAXD ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg ms' md')
    (fpostWFbm (fx := fx) B ARx SK P (STK_parse_items d) e (rd_fp q v) regs ly S Hp W mem md
       (pi_post B ly S d o tb text len p q v Lam peak cnt fail ran most own kr)).
Proof.
intros P ly S Hp W regs mem md ch e q v text len p tb o Lam peak cnt fail ran most own kr ms' md' k' HP0
  HAFN HWIN HFRM H10 H11 H12 HIN Hsq Hqe HNODE Hqv HLED HRL H8 HSTK HS HJ KEPT HGR HMN Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hastk & Hpres & Hch & HQT).
pose proof Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof HIN as (Vp & Ved & Vdp & Hqrw & Hq8 & Ht0 & Htl & Hple & Hlen & Hsrc & Hdqt & Hd032).
pose proof HNODE as (Hv4096 & Hv8 & (Hvrw8 & Hvrw) & HZ & Hat & Hvam & Hvown & Hvra).
assert (F1 : YM05.alloc_ceiling <= spZ regs - STK_parse_items d) by lia.
destruct (pie_v_place B ARx HL LAWS ly S Hp W mem md Lam peak cnt fail ran most own regs e v (STK_parse_items d) q HAR HLED
  Hat F1 HSTK He0) as (Hvimg & Hvsp & Hvwr).
assert (Hv47 : v + 56 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; lia).
(* the run's atoms at the entry environment, then the environment made opaque for prreg *)
pose proof (pie_den33 regs p (text + len) (Z.of_nat d) ltac:(lia)) as D33.
pose proof (pie_den34 regs p (text + len) (Z.of_nat d) ltac:(lia)) as D34.
pose proof (pie_den35 regs p (text + len) (Z.of_nat d) ltac:(lia)) as D35.
assert (DR : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (PIE_E regs p (text + len) (Z.of_nat d)) (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr regs r)))
  by (intros n r Hn Hr; exact (pie_den_reg regs p (text + len) (Z.of_nat d) n r Hn Hr)).
assert (E2 : ew (PIE_E regs p (text + len) (Z.of_nat d)) 2 = getr regs 2) by (apply pie_E_reg; [lia | reflexivity]).
assert (E3 : ew (PIE_E regs p (text + len) (Z.of_nat d)) 3 = getr regs 3) by (apply pie_E_reg; [lia | reflexivity]).
assert (E4 : ew (PIE_E regs p (text + len) (Z.of_nat d)) 4 = getr regs 4) by (apply pie_E_reg; [lia | reflexivity]).
assert (E10 : ew (PIE_E regs p (text + len) (Z.of_nat d)) 10 = getr regs 10) by (apply pie_E_reg; [lia | reflexivity]).
assert (E11 : ew (PIE_E regs p (text + len) (Z.of_nat d)) 11 = getr regs 11) by (apply pie_E_reg; [lia | reflexivity]).
assert (E12 : ew (PIE_E regs p (text + len) (Z.of_nat d)) 12 = getr regs 12) by (apply pie_E_reg; [lia | reflexivity]).
remember (PIE_E regs p (text + len) (Z.of_nat d)) as EE eqn:HEE.
clear HEE.
assert (B2 : bv_unsigned (ew EE 2) = spZ regs) by (rewrite E2; reflexivity).
assert (B10 : bv_unsigned (ew EE 10) = q) by (rewrite E10, H10; apply unsigned_lit_small; lia).
assert (B11 : bv_unsigned (ew EE 11) = v) by (rewrite E11, H11; apply unsigned_lit_small; lia).
(* the type word the run stored: 5 for an array, 6 for an object *)
assert (DTY : sv_denot EE (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 5)) =
  Z_to_bv 64 (if o then 6 else 5)).
{ cbn [sv_denot]. rewrite E12, H12. apply bv_eq. destruct o; vm_compute; reflexivity. }
(* the regions of the refusal state *)
pose proof (pi_region_nth SEGS VAL EE PIE_SS_REF _ 0 _ HS eq_refl) as RG0.
pose proof (pi_region_nth SEGS VAL EE PIE_SS_REF _ 3 _ HS eq_refl) as RG3.
pose proof (pi_region_nth SEGS VAL EE PIE_SS_REF _ 4 _ HS eq_refl) as RG4.
pose proof (pi_region_nth SEGS VAL EE PIE_SS_REF _ 5 _ HS eq_refl) as RG5.
cbn [ms_mem restrict mkst] in RG0, RG3, RG4, RG5.
(* the cursor and the node fields at the refusal state *)
assert (Mp : val_mem SEGS (rdW W (ms_mem ms')) q 8 p).
{ replace q with (bv_unsigned (ew EE 10) + 0) by lia.
  eapply (pi_field _ _ _ 10 _ _ _ _ _ _ 0 8%N _ _ RG3 eq_refl);
  [ repeat (first [left; reflexivity | right]) | exact D33 | cbn; lia | cbn; lia ]. }
assert (Med : val_mem SEGS (rdW W (ms_mem ms')) (q + 8) 8 (text + len)).
{ replace (q + 8) with (bv_unsigned (ew EE 10) + 8) by lia.
  eapply (pi_field _ _ _ 10 _ _ _ _ _ _ 8 8%N _ _ RG3 eq_refl);
  [ repeat (first [left; reflexivity | right]) | exact D34 | cbn; lia | cbn; lia ]. }
assert (Mdp : val_mem SEGS (rdW W (ms_mem ms')) (q + 16) 4 (Z.of_nat d + 1)).
{ replace (q + 16) with (bv_unsigned (ew EE 10) + 16) by lia.
  eapply (pi_field _ _ _ 10 _ _ _ _ _ _ 16 4%N _ _ RG4 eq_refl);
  [ repeat (first [left; reflexivity | right]) | exact D35 | cbn; lia | cbn; lia ]. }
assert (Mty : val_mem SEGS (rdW W (ms_mem ms')) v 4 (if o then 6 else 5)).
{ replace v with (bv_unsigned (ew EE 11) + 0) at 1 by lia.
  eapply (pi_field _ _ _ 11 _ _ _ _ _ _ 0 4%N _ _ RG5 eq_refl);
  [ repeat (first [left; reflexivity | right]) | exact DTY | destruct o; cbn; lia | cbn; lia ]. }
(* writability survives (memory only grows) *)
assert (RWq : rd_rw SEGS (rdW W (ms_mem ms')) q 24)
  by (intros x Hx; apply (writable_at_grows SEGS _ _ x HGR); apply Hqrw; exact Hx).
assert (RWv : rd_rw SEGS (rdW W (ms_mem ms')) v 56)
  by (intros x Hx; apply (writable_at_grows SEGS _ _ x HGR); apply Hvrw; exact Hx).
(* the node's bytes past the type word are kept, so they are still zero *)
assert (KV : forall x, v + 4 <= x < v + 56 -> aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) mem x).
{ intros x Hx. apply KEPT; [lia|]. unfold pie_wset.
  intros [Hf | [Hf | [Hf | Hf]]]; first [lia | destruct Hqv as [Hqv' | Hqv']; lia]. }
assert (Z8 : forall off, 8 <= off -> off + 8 <= 56 -> rd_u64 SEGS (rdW W (ms_mem ms')) (v + off) 0).
{ intros off H1 H2. destruct (pie_zero_u64 _ v off HZ ltac:(lia) H2) as [Hr Hvm]. split; [exact Hr|].
  apply (pi_val_kept (L := Lb) (PI := PIb) (w_H W) mem (ms_mem ms')); [|exact Hvm].
  intros x Hx. apply KV. lia. }
(* the node's header at the refusal: its type word, every other word zero (pj_fdR's and the free order's leaf) *)
assert (HDR : pj_hdrR SEGS (rdW W (ms_mem ms')) v (if o then 6 else 5) 0 0 0 0 0 0).
{ split; [split; [exact Hv8 | exact RWv]|].
  split; [split; [destruct o; lia | exact Mty]|].
  split; [exact (Z8 8 ltac:(lia) ltac:(lia))|]. split; [exact (Z8 16 ltac:(lia) ltac:(lia))|].
  split; [exact (Z8 24 ltac:(lia) ltac:(lia))|]. split; [exact (Z8 32 ltac:(lia) ltac:(lia))|].
  split; [exact (Z8 40 ltac:(lia) ltac:(lia)) | exact (Z8 48 ltac:(lia) ltac:(lia))]. }
(* at d = MAXD the all-granted run and the model's free list are the refusal's own: no event, nothing to free *)
assert (GT : prhPi_gtrace d o (rest_atR tb text p) = []).
{ rewrite Hd. unfold prhPi_gtrace, PjGrammar.jr_items, PjGrammar.jr_cont. reflexivity. }
assert (FR0 : prhPi_frees d o (rest_atR tb text p) [] = []).
{ rewrite Hd. unfold prhPi_frees, PresetReqAt.jf_cont. reflexivity. }
(* the machine state, in cfg_at form at the epilogue *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (21%bv : bv 5) Q21.
assert (Hsp' : spZ (ms_regs ms') = spZ regs - PI_FRAME).
{ unfold spZ. rewrite Q2, B2. unfold PI_FRAME. apply unsigned_lit_small. unfold spZ in *. lia. }
pmkst HS.
lazymatch goal with |- SRr' _ _ _ {| cfg_ms := mkst ?rg ?pcw ?mm _; cfg_model := ?mdx |} _ =>
  replace pcw with (w64 (VAL A_TEXT + PI_AT (L := Lb) (PI := PIb) PI_O_EPI))
    by (unfold w64; f_equal; vm_compute; reflexivity) end.
apply (pie_holds (fx := fx) B ARx SK HL LAWS P fx d ly S Hp W mem md regs e q v
  (pi_post B ly S d o tb text len p q v Lam peak cnt fail ran most own kr) ly S Hp W (ms_mem ms') md' k'
  (ms_regs ms') (-1) [] (pie_aj_lift HJ) HP0).
unfold pi_epi_pre.
split; [split; [exact HFRM | intros r Hr; reflexivity]|].
split; [exact HMN|].
split.
{ unfold pi_frame.
  split; [exact Hsp'|]. split; [rewrite Q3, E3; reflexivity|]. split; [rewrite Q4, E4; reflexivity|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 1%nat 1%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 8%nat 8%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 9%nat 9%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 18%nat 18%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 19%nat 19%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 20%nat 20%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 21%nat 21%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 22%nat 22%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 23%nat 23%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 24%nat 24%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 25%nat 25%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 26%nat 26%bv ltac:(lia) eq_refl)|].
  split; [pie_frw EE RG0 B2 Hsp' (DR 27%nat 27%bv ltac:(lia) eq_refl)|].
  split.
  { intros a Ha Hn. apply KEPT; [lia|]. unfold pie_wset. intros [Hf | [Hf | [Hf | Hf]]]; [lia | | |]; apply Hn.
    - exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
    - exists (q + 16, q + 20). split; [right; left; reflexivity | cbn [fst snd]; lia].
    - exists (v, v + 56). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
  split; [exact Hra|]. split; [exact He0 | exact He16]. }
split; [rewrite Q21; apply bv_eq; vm_compute; reflexivity|].
split; [apply pi_post_stable|].
(* the text's post, None arm, through its record (PRH_FnParse.v tpiP_R, tpiP_Q_of_R, tpiP_RNone) *)
intros regs'' H10''.
unfold pi_post.
apply (tpiP_Q_of_R (ok := []) (res := None) (tr := []) (okr := []) (D := []) (Lam' := Lam) (peak' := peak)
  (cnt' := cnt) (fail' := fail) (ran' := ran) md').
refine {| tpiP_run := ?[frun]; tpiP_ledger := ?[fled]; tpiP_room := ?[froom]; tpiP_hull := ?[fhull];
  tpiP_live := ?[flive]; tpiP_pos := ?[fpos]; tpiP_outcome := ?[fout]; tpiP_injected := ?[finj];
  tpiP_ledger_move := ?[fmove]; tpiP_blocks_move := ?[fblk]; tpiP_bytes := ?[fbytes]; tpiP_lsum := ?[flsum];
  tpiP_arm := ?[farm] |}.
[frun]: { rewrite Hd; unfold PjGrammar.jr_items, PjGrammar.jr_cont; reflexivity. }
[fled]: { eapply pie_ledger_kept; [exact HLED | |].
  - intros a Ha. pose proof (pie_img_below a (pst_in_img_B a Ha)) as Hlo. apply KEPT; [unfold kLowMemEnd in Hlo; lia|].
    unfold pie_wset. intros [Hf | [Hf | [Hf | Hf]]]; try (unfold kLowMemEnd in Hlo; lia).
    apply (Hvimg a ltac:(lia) (pst_in_img_B a Ha)).
  - intros a kk x Hin Hx.
    pose proof HLED as HF. apply prh_ledger_blocks in HF. pose proof (proj1 (Forall_forall _ _) HF (a, kk) Hin) as (Hk & Hblk & _).
    cbn [fst snd] in Hk, Hblk.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & H4096 & Hc & _).
    assert (Hrq : kk + cf_head <= req_size (kk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    apply KEPT; [lia|]. unfold pie_wset. intros [Hf | [Hf | [Hf | Hf]]]; try lia.
    exact (pie_head_apart B ARx HL LAWS ly S Hp W mem md Lam peak cnt fail ran most own regs e v H8 HAR HLED Hat
      ltac:(lia) a kk x Hin Hx ltac:(lia)). }
[froom]: { exact HRL. }
(* THE HULL USE: no allocation, the meters are the entry's *)
[fhull]: { exact (PresetHullBudget.hull_used_refl S _). }
[flive]: { exact (PItems_posb.pi_live_nil _). }
[fpos]: { exact (PItems_posb.pi_posb_post S S [] (PItems_posb.pi_posb_nil S)). }
(* THE OUTCOME (the batch kit): the all-granted run is this refusal, with no event, so the position is i itself *)
[fout]: { rewrite GT. intros sm x os i H0 hist Hpos _ _ _. split; [reflexivity|].
  split; [rewrite Hd; unfold PjGrammar.jr_items, PjGrammar.jr_cont; reflexivity|].
  exists hist. replace (i + length (PresetReqAt.rd_hevs []))%nat with i by (rewrite Nat.add_comm; reflexivity).
  exact Hpos. }
(* THE INJECTED READING: the refusal made no call, so none was refused (ok = [] is all-granted over tr = []) *)
[finj]: { intros sm x os i H0 hist _ _ _ _. exact (pi_grant_granted [] [] cnt fail _ eq_refl). }
[fmove]: { rewrite GT. pose proof HLED as HBD. apply prh_ledger_bounds in HBD. destruct HBD as (Hl0 & _ & Hc0 & _).
  apply pie_move_id; lia. }
[fblk]: { unfold rd_blocks_move. split; [intros a kk Hin; destruct Hin|].
  split; [cbn [prhReader_ab map app]; apply Permutation_refl|].
  split; [apply Permutation_refl|]. cbn [hpeakR]. lia. }
[fbytes]: { unfold prh_held; cbn [PjGrammar.held PjGrammar.calls]; lia. }
[flsum]: { reflexivity. }
[farm]: {
  apply tpiP_ANone_of_R.
  refine {| tpiPn_ret := ?[nret]; tpiPn_freeord := ?[nfo]; tpiPn_in_after := ?[nin]; tpiPn_fd := ?[nfd] |}.
  [nret]: { exact H10''. }
  (* the partial tree's free order: the zeroed node frees nothing, and neither does the text's model *)
  [nfo]: { intros _ n _. exists []. split; [exact (PvB_Frees.pvf_zero_foR SEGS _ _ n v _ HDR)|]. rewrite FR0. reflexivity. }
  [nin]: { exists p, (Z.of_nat d + 1). split; [lia|]. split; [rewrite Hd; unfold PjGrammar.MAXD; lia|].
    split; [exact Mp|]. split; [exact Med|]. split; [exact Mdp | exact RWq]. }
  [nfd]: { rewrite Hd, Nat.sub_diag. cbn [pj_fdR].
    split; [constructor|]. split; [intros b x Hb; destruct Hb|].
    exists (if o then 6 else 5), 0, 0, 0, 0, 0, 0, false, [], [], [], [].
    split; [exact HDR|].
    split; [left; split; reflexivity|].
    split; [left; split; [reflexivity | split; reflexivity]|].
    split; [left; split; [reflexivity | split; reflexivity]|].
    split; [apply Permutation_refl|].
    split; reflexivity. } }
Qed.

(* ==================================================================================================
   THE CALL ARM: the skip_ws call at 0x87b20 (the kit's tskip_ws_specX through YCbqGcallW.v aj_call_xW_sp, window
   e + 144, footprint [(q, q + 8)]), then PItems_pres.v's pi_head_spec at the return site PI_O_HEAD (0x87b24).
   ================================================================================================== *)
(* a region of a symbolic state at a call stop (st_ok of setpc ..., the region list unchanged) *)
Lemma pie_region_nth_st : forall E ss ms i r, st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r ->
  region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HSt Hi. destruct (st_ok_mem_ok SEGS E ss ms HSt) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.

(* the frame region the prologue builds, as every state of the entry run holds it (13 saved words) *)
Definition PIE_FRREG : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0
    [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma pie_frreg_call : nth_error (ss_mem PIE_SS_CALL) 0 = Some PIE_FRREG.
Proof. vm_compute. reflexivity. Qed.

(* the epilogue's frame predicate read off a state holding PIE_FRREG *)
Lemma pie_frame_at : forall (regs regs' : bvmap 5 word) (W : world SEGS) mem m' e q v EE,
  region_ok SEGS EE (rdW W m') PIE_FRREG ->
  bv_unsigned (ew EE 2) = spZ regs ->
  (forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
     sv_denot EE (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr regs r))) ->
  spZ regs' = spZ regs - PI_FRAME -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  (forall a, spZ regs <= a < spZ regs + e -> ~ inFP (rd_fp q v) a ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a) ->
  YK0s.ret_ok (getr regs 1) -> 0 <= e -> e mod 16 = 0 ->
  pi_frame regs regs' W mem W m' e q v.
Proof.
intros regs regs' W mem m' e q v EE RG0 B2 DR Hsp' H3 H4 HW Hra He0 He16.
unfold PIE_FRREG in RG0. unfold pi_frame.
split; [exact Hsp'|]. split; [exact H3|]. split; [exact H4|].
split; [pie_frw EE RG0 B2 Hsp' (DR 1%nat 1%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 8%nat 8%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 9%nat 9%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 18%nat 18%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 19%nat 19%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 20%nat 20%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 21%nat 21%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 22%nat 22%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 23%nat 23%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 24%nat 24%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 25%nat 25%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 26%nat 26%bv ltac:(lia) eq_refl)|].
split; [pie_frw EE RG0 B2 Hsp' (DR 27%nat 27%bv ltac:(lia) eq_refl)|].
split; [exact HW|]. split; [exact Hra|]. split; [exact He0 | exact He16].
Qed.

(* bytes read through one world's reader agree with another's wherever their views agree (PItems_body_key.v's pik_val_win) *)
Lemma pie_val_win : forall (W1 W2 : world SEGS) m1 m2 a n x,
  (forall k, (k < n)%nat -> aview SEGS (w_H W2) m2 (a + Z.of_nat k) = aview SEGS (w_H W1) m1 (a + Z.of_nat k)) ->
  val_mem SEGS (rdW W1 m1) a n x -> val_mem SEGS (rdW W2 m2) a n x.
Proof.
intros W1 W2 m1 m2 a n x HA HV kk Hk.
rewrite (mbyte_of_aview SEGS (w_H W1) (w_H W2) m1 m2 (a + Z.of_nat kk) (HA kk Hk)). exact (HV kk Hk).
Qed.

(* the frame across a call that keeps the view on [sp + 40, entry sp + e) but for q's p field (PItems_body_key.v's pik_frame_win) *)
Lemma pie_frame_win : forall (regs0 regs regs' : bvmap 5 word) (W : world SEGS) mem (Wc W' : world SEGS) memc mem' e q v,
  pi_frame regs0 regs W mem Wc memc e q v ->
  spZ regs' = spZ regs -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 -> spZ regs0 <= q ->
  (forall a, spZ regs <= a < spZ regs0 + e -> ~ (q <= a < q + 8) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H Wc) memc a) ->
  pi_frame regs0 regs' W mem W' mem' e q v.
Proof.
intros regs0 regs regs' W mem Wc W' memc mem' e q v
  (Fsp & F3 & F4 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & Fw & Fr & He0 & He16)
  Hsp H3 H4 Hq HW.
unfold PI_FRAME in Fsp.
assert (VW : forall o x, 40 <= o -> o + 8 <= 144 ->
  val_mem SEGS (rdW Wc memc) (spZ regs + o) 8 x -> val_mem SEGS (rdW W' mem') (spZ regs' + o) 8 x).
{ intros o x Ho1 Ho2 Hv. rewrite Hsp. apply (pie_val_win Wc W' memc mem'); [|exact Hv].
  intros kk Hk. apply HW; lia. }
split; [rewrite Hsp; unfold PI_FRAME; lia|]. split; [rewrite H3; exact F3|]. split; [rewrite H4; exact F4|].
split; [apply VW; [lia | lia | exact V1]|]. split; [apply VW; [lia | lia | exact V2]|].
split; [apply VW; [lia | lia | exact V3]|]. split; [apply VW; [lia | lia | exact V4]|].
split; [apply VW; [lia | lia | exact V5]|]. split; [apply VW; [lia | lia | exact V6]|].
split; [apply VW; [lia | lia | exact V7]|]. split; [apply VW; [lia | lia | exact V8]|].
split; [apply VW; [lia | lia | exact V9]|]. split; [apply VW; [lia | lia | exact V10]|].
split; [apply VW; [lia | lia | exact V11]|]. split; [apply VW; [lia | lia | exact V12]|].
split; [apply VW; [lia | lia | exact V13]|].
split; [|split; [exact Fr | split; [exact He0 | exact He16]]].
intros a Ha Hn. rewrite <- (Fw a Ha Hn). apply HW; [lia|].
intros Hqa. apply Hn. exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma pie_zmaxl_in : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. induction l as [|y l IH]; intros H; [destruct H|]. cbn [zmaxl fold_right].
destruct H as [<-|H]; [lia|]. specialize (IH H). fold (zmaxl l). lia.
Qed.

(* the stack budget of the skip_ws call: its frame and parse_items' own fit in parse_items' bound (image B) *)
Lemma pie_stk_skw : forall dd, STK_skip_ws + PI_FRAME <= STK_parse_items dd.
Proof.
intros dd. unfold STK_parse_items, LEAF_pv_pi.
assert (FR1 : PRH_Base.pi_frame F_parse_items = PI_FRAME) by reflexivity. rewrite FR1.
pose proof (pie_zmaxl_in STK_skip_ws [STK_RT_ECALL; STK_RT_STRTOD; STK_fuzz_malloc; STK_fuzz_free; STK_literal;
  STK_parse_string; STK_grow; STK_skip_ws] ltac:(do 7 right; left; reflexivity)) as H1.
pose proof (pi_frame_nonneg F_parse_value) as H2. pose proof (pi_frame_nonneg F_parse_items) as H3.
pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - dd)) as H4.
assert (H5 : 0 <= Z.of_nat (PjGrammar.MAXD - dd) * (PRH_Base.pi_frame F_parse_value + PRH_Base.pi_frame F_parse_items))
  by nia.
unfold PI_FRAME in *. lia.
Qed.

Lemma pie_rdword_of_val : forall (H : word -> bool) (mem : word -> option byte) a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bb : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bb 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bb 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bb 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bb 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bb 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bb 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bb 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bb 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* fpre's read-only view rides through a journal whose footprint does not open the sink (PItems_body_key.v's pik_rod_kept, with
   S1ImgB.v pst_not_ro_B for the statics) *)
Lemma pie_rod_kept : forall STK sp0 FP ly S Hp (W : world SEGS) mem md own lyc Sc Hpc (W' : world SEGS) mem' md' k,
  ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc W' mem' md' k HJ Hsk Hrod a Hro Hos Her.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (Hrod a Hro Hos Her) | | exact Hos | exact Her | | apply fp_spares_closed; exact Hsk].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
- intros Hp'. exact (pst_not_ro_B a Hp' Hro).
Qed.

Lemma pie_den33p : forall regs p ed dp, 0 <= p < 2 ^ 63 ->
  sv_denot (PIE_E regs p ed dp) (SOff 33 1) = Z_to_bv 64 (p + 1).
Proof.
intros regs p ed dp Hp. cbn [sv_denot].
change (ew (PIE_E regs p ed dp) 33) with (ew (PIE_E regs p ed dp) (32 + 1)).
rewrite (pie_E_extra regs p ed dp 1) by lia. cbn [nth pie_extra2 map].
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Section call.
Variable CTX0 : list (list Z).
(* The batch kit's cursor set (PRH_FnParse.v ed236011cf99 tparse_items_specX's CW): every spec and pre takes it after CTX0 *)
Variable CW : list (list Z).
(* the callee text, the kit's tskip_ws_specX (PRH_FnReader.v), at every float state: PROVED on B' by a Theorem Labs lane
   (lib/B/Prog/skip_ws_mn.v skip_ws_holds, generic in ARx over this Section's own LAWS and the PALibCore of its PAL) *)
Let TSKW : forall fy : YK11.FPState, tskip_ws_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK :=
  fun fy => OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.skip_ws_holds (fx := fy) (HL := HL)
    SK B ARx LAWS (YC1fP.palib_core B PAL).
(* the head segment, from the return site on (PItems_head.v pi_head_holds). *)
Hypothesis HEAD : pi_head_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW.
(* the shadow laws PItems_kept.v's proofs take at the return state of a call (each is a law of the
   allocator's invariant ARcf: YGcfHeadSh.v ARx_hshadow_law_cf for HSH; the zero-shadow and image-shadow ranges for
   HZS / HIMG). *)
Hypothesis HSH : pi_hshadow_law (L := Lb) (PA := PIb) B ARx cf_head.
Hypothesis HZS : pi_zs_law (L := Lb) (PA := PIb) B ARx.
Hypothesis HIMG : pi_img_law (L := Lb) (PA := PIb) B ARx.
(* the kept-across-a-call statements, PROVED in PItems_kept.v (alloc.c's statics are not read-only at image B:
   S1ImgB.v pst_not_ro_B) *)
Let HKC : pi_cur_kept_call_stmt (L := Lb) (PA := PIb) (SKq := SK) B ARx :=
  pi_cur_kept_call (L := Lb) (PA := PIb) (SKq := SK) B ARx LAWS HSH HZS HIMG pst_not_ro_B.
Let HKN : pi_node_kept_call_stmt (L := Lb) (PA := PIb) (SKq := SK) B ARx :=
  pi_node_kept_call (L := Lb) (PA := PIb) (SKq := SK) B ARx.

(* off the image, two equal views are two equal readers: the same byte and the same writability (PItems_body_key.v's
   pik_agree_view) *)
Lemma pie_agree_view : forall (W1 W2 : world SEGS) m1 m2 x, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x ->
  mbyte SEGS (rdW W2 m2) x = mbyte SEGS (rdW W1 m1) x /\
  (writable_at SEGS (rdW W1 m1) x -> writable_at SEGS (rdW W2 m2) x).
Proof.
intros W1 W2 m1 m2 x Hx Hn E.
pose proof (mbyte_of_aview SEGS _ _ _ _ x E) as EM. split; [exact EM|].
unfold mbyte in EM. rewrite (seg_rom_none SEGS x Hx Hn) in EM.
unfold writable_at, wview. revert EM.
destruct (mrestrict (w_H W1) m1 (Z_to_bv 64 x)) as [b|] eqn:E1;
  destruct (mrestrict (w_H W2) m2 (Z_to_bv 64 x)) as [b'|] eqn:E2; intros EM Hw.
- intros C; discriminate C.
- discriminate EM.
- intros C; discriminate C.
- exfalso. apply Hw. rewrite unsigned_lit_small by lia. rewrite (find_segment_none SEGS x Hn). reflexivity.
Qed.

(* the white space skip_ws consumes is a prefix of what it reads *)
Lemma pie_skip_suffix : forall x, exists l, x = l ++ PjGrammar.skip x.
Proof.
induction x as [|b r IH]; [exists []; reflexivity|]. cbn [PjGrammar.skip].
destruct (PjGrammar.ws b); [destruct IH as (l & Hl); exists (b :: l); cbn [app]; f_equal; exact Hl|].
exists []. reflexivity.
Qed.
Lemma pie_tl_skipn : forall {X} (l : list X) k, tl (skipn k l) = skipn (S k) l.
Proof. intros X l k. revert l. induction k as [|k IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.
(* the cursor skip_ws leaves after the opener (pi_head_pre's p1) *)
Lemma pie_rest_skip : forall (tb : list Z) text len p, Z.of_nat (length tb) = len -> text <= p < text + len ->
  rest_atR tb text (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text (p + 1))))) =
  PjGrammar.skip (tl (rest_atR tb text p)).
Proof.
intros tb text len p Hl Hp.
assert (Ht : tl (rest_atR tb text p) = rest_atR tb text (p + 1)).
{ unfold rest_atR. rewrite pie_tl_skipn. f_equal. lia. }
rewrite Ht. set (y := rest_atR tb text (p + 1)).
destruct (pie_skip_suffix y) as (l & Hy).
assert (Hly : length y = Z.to_nat (text + len - (p + 1))) by (unfold y, rest_atR; rewrite length_skipn; lia).
assert (Hl2 : length y = (length l + length (PjGrammar.skip y))%nat) by (rewrite Hy at 1; rewrite length_app; reflexivity).
unfold rest_atR at 1.
replace (Z.to_nat (text + len - Z.of_nat (length (PjGrammar.skip y)) - text)) with (length l + Z.to_nat (p + 1 - text))%nat
  by lia.
rewrite <- skipn_skipn. fold (rest_atR tb text (p + 1)). fold y.
rewrite Hy at 1. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

(* THE CALL ARM: from the state at the skip_ws call (the run's PIE_SS_CALL) to the head segment. skip_ws makes no
   allocator event (its post keeps S), so the head's pre gets the entry relations pi_posb_nil / pi_live_nil at [].
   The journal is the EMPTY-budget one from S (WS0 = []): skip_ws' unbudgeted window rule applies to it unchanged,
   and the head's spec gets WS0 = [] with wbudget CW 0 []. skip_ws frees nothing: its plain call rule, lifted under
   SRr'_bind (YA0nH.SRr_SRr'); the head's spec takes the journal at wle' (pie_aj_lift) *)
Lemma pie_call : forall ly S Hp (W : world SEGS) (regs : bvmap 5 word) mem md ch CTX e q v text len p (tb : list Z)
  (o : bool) Lam peak cnt fail ran most own kr (ms' : machine_state) (md' : Model) (k' : Z),
  pi_ent (L := Lb) (PA := PIb) B fx ly S Hp W regs mem ch CTX Lam peak cnt fail ran most own e q text len p d kr tb v o
    CTX0 CW ->
  afn_pre_x SEGS B ARx (STK_parse_items d) ly S Hp W regs mem md ch -> spZ regs + 64 <= ly_stk_hi ly ->
  8 <= cf_head ->
  st_ok SEGS (PIE_E regs p (text + len) (Z.of_nat d)) (setpc PIE_SS_CALL (@pa_sigma rc Lb PIb AS_skip_ws))
    (restrict (w_H W) ms') ->
  pi_aj B ARx SK ly S Hp W mem md regs d e q v ly S Hp W (ms_mem ms') md' k' [] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ pie_wset regs q v a ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a) ->
  mem_grows (rdW W mem) (rdW W (ms_mem ms')) -> YAkMemnorm.memnorm SEGS (ms_mem ms') ->
  (d < PjGrammar.MAXD)%nat ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg ms' md')
    (fpostWFbm (fx := fx) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_items d) e (rd_fp q v) regs ly S Hp W mem md
       (pi_post B ly S d o tb text len p q v Lam peak cnt fail ran most own kr)).
Proof.
intros ly S Hp W regs mem md ch CTX e q v text len p tb o Lam peak cnt fail ran most own kr
  ms' md' k' HENT HAFN Hshi64 H8 HS HJ KEPT HGR HMNc Hd.
assert (Hd32 : (d < 32)%nat) by (unfold PjGrammar.MAXD in Hd; exact Hd).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR. unfold ASAN_CEIL in CR.
pose proof HENT as (Emn & Epk1 & Epk2 & Ein & Eclo & Ecent & Echn & Ecur & E10 & E11 & E12 & Egp & Etp & RDP & Eplt & Enth
  & Eroom & Efch & Efrm & Erod & Ecw & Ewr & Ehull).
pose proof RDP as (HFRM & _ & _ & _ & HIN & HWIN & Hsq & Hqe & Hqra & HSRC & HHOME & _ & HNODE & Hqv & Htv & Hvw & HLED
  & HdM & HCNT).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hastk & Hpres & Hch & HQT).
pose proof Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof HIN as (Vp & Ved & Vdp & Hqrw & Hq8 & Ht0 & Htl & Hple & Hlen & Hsrc & Hdqt & Hd032).
pose proof HNODE as (Hv4096 & Hv8 & (Hvrw8 & Hvrw) & HZ & Hat & Hvam & Hvown & Hvra).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & Hthv). rewrite Hlen in Htc, Htam, Htra, Hthv.
pose proof (pie_stk_skw d) as HSTKB. unfold STK_skip_ws, PI_FRAME in HSTKB.
pose proof (pi_frame_nonneg F_skip_ws) as HSKW0.
assert (HSTK : 144 <= STK_parse_items d) by (unfold STK_skip_ws in *; lia).
assert (F1 : YM05.alloc_ceiling <= spZ regs - STK_parse_items d) by lia.
destruct (pie_v_place B ARx HL LAWS ly S Hp W mem md Lam peak cnt fail ran most own regs e v (STK_parse_items d) q HAR HLED
  Hat F1 HSTK He0) as (Hvimg & Hvsp & Hvwr).
assert (Hv47 : v + 56 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvam; lia).
assert (Hq0 : YM05.alloc_ceiling <= q) by lia.
(* the run's atoms at the entry environment *)
pose proof (pie_den33p regs p (text + len) (Z.of_nat d) ltac:(lia)) as D33.
pose proof (pie_den34 regs p (text + len) (Z.of_nat d) ltac:(lia)) as D34.
pose proof (pie_den35 regs p (text + len) (Z.of_nat d) ltac:(lia)) as D35.
assert (DR : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (PIE_E regs p (text + len) (Z.of_nat d)) (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr regs r)))
  by (intros n r Hn Hr; exact (pie_den_reg regs p (text + len) (Z.of_nat d) n r Hn Hr)).
assert (EK : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (PIE_E regs p (text + len) (Z.of_nat d)) n = getr regs r)
  by (intros n r Hn Hr; exact (pie_E_reg regs p (text + len) (Z.of_nat d) n r Hn Hr)).
assert (E32 : ew (PIE_E regs p (text + len) (Z.of_nat d)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (exact (pie_E_extra regs p (text + len) (Z.of_nat d) 0 ltac:(lia))).
assert (DTY : sv_denot (PIE_E regs p (text + len) (Z.of_nat d))
  (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) (SLit 5)) = Z_to_bv 64 (if o then 6 else 5)).
{ cbn [sv_denot]. rewrite (EK 12%nat 12%bv ltac:(lia) eq_refl), E12. apply bv_eq. destruct o; vm_compute; reflexivity. }
assert (HEI : img_env VAL A_LIM (PIE_E regs p (text + len) (Z.of_nat d))) by (unfold PIE_E; apply Eimg_env).
remember (PIE_E regs p (text + len) (Z.of_nat d)) as EE eqn:HEE.
assert (B2 : bv_unsigned (ew EE 2) = spZ regs) by (rewrite (EK 2%nat 2%bv ltac:(lia) eq_refl); reflexivity).
assert (B10 : bv_unsigned (ew EE 10) = q) by (rewrite (EK 10%nat 10%bv ltac:(lia) eq_refl), E10; apply unsigned_lit_small; lia).
assert (B11 : bv_unsigned (ew EE 11) = v) by (rewrite (EK 11%nat 11%bv ltac:(lia) eq_refl), E11; apply unsigned_lit_small; lia).
(* the registers at the call *)
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10. prreg HS (18%bv : bv 5) R18.
prreg HS (19%bv : bv 5) R19. prreg HS (21%bv : bv 5) R21. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26.
prreg HS (27%bv : bv 5) R27.
assert (Usp : spZ (ms_regs ms') = spZ regs - PI_FRAME).
{ unfold spZ. rewrite R2, B2. unfold PI_FRAME. apply unsigned_lit_small. unfold spZ in *. lia. }
assert (Us0 : s0Z (ms_regs ms') = q + 16).
{ unfold s0Z. rewrite R8, B10. apply unsigned_lit_small. lia. }
assert (Ra0 : getr (ms_regs ms') 10 = w64 q) by (rewrite R10, (EK 10%nat 10%bv ltac:(lia) eq_refl); exact E10).
assert (Q3 : getr (ms_regs ms') 3 = getr regs 3) by (rewrite R3; exact (EK 3%nat 3%bv ltac:(lia) eq_refl)).
assert (Q4 : getr (ms_regs ms') 4 = getr regs 4) by (rewrite R4; exact (EK 4%nat 4%bv ltac:(lia) eq_refl)).
assert (Q9 : getr (ms_regs ms') 9 = w64 q) by (rewrite R9, (EK 10%nat 10%bv ltac:(lia) eq_refl); exact E10).
assert (Q19 : getr (ms_regs ms') 19 = w64 v) by (rewrite R19, (EK 11%nat 11%bv ltac:(lia) eq_refl); exact E11).
assert (Q18 : getr (ms_regs ms') 18 = w64 (if o then 1 else 0)) by (rewrite R18, (EK 12%nat 12%bv ltac:(lia) eq_refl); exact E12).
assert (Q8 : getr (ms_regs ms') 8 = w64 (q + 16)) by (rewrite R8, B10; reflexivity).
assert (Q21 : getr (ms_regs ms') 21 = w64 (-1)) by (rewrite R21; apply bv_eq; vm_compute; reflexivity).
assert (Q26 : getr (ms_regs ms') 26 = w64 SHADOW_OFF) by (rewrite R26; exact E32).
assert (HSB : 0 <= SHADOW_OFF < 2 ^ 32) by (unfold SHADOW_OFF; lia).
assert (Q25 : getr (ms_regs ms') 25 = w64 (pi_sh (q + 16))).
{ rewrite R25. rewrite (hd_alu_shx (Z_to_bv 64 (bv_unsigned (ew EE 10) + 16)) (ew EE 32) (q + 16) SHADOW_OFF
    ltac:(rewrite B10; reflexivity) E32 ltac:(lia) HSB).
  unfold pi_sh, w64. reflexivity. }
assert (Q27 : getr (ms_regs ms') 27 = w64 (pi_sh q)).
{ rewrite R27. rewrite (hd_alu_shx (ew EE 10) (ew EE 32) q SHADOW_OFF ltac:(rewrite (EK 10%nat 10%bv ltac:(lia) eq_refl), E10; reflexivity)
    E32 ltac:(lia) HSB).
  unfold pi_sh, w64. reflexivity. }
(* the memory at the call: the cursor's fields, the node's type word, the frame *)
pose proof (pie_region_nth_st EE _ _ 0 _ HS pie_frreg_call) as RG0.
pose proof (pie_region_nth_st EE _ _ 3 _ HS eq_refl) as RG3.
pose proof (pie_region_nth_st EE _ _ 4 _ HS eq_refl) as RG4.
pose proof (pie_region_nth_st EE _ _ 5 _ HS eq_refl) as RG5.
cbn [ms_mem restrict mkst] in RG0, RG3, RG4, RG5.
assert (Mp : val_mem SEGS (rdW W (ms_mem ms')) q 8 (p + 1)).
{ replace q with (bv_unsigned (ew EE 10) + 0) by lia.
  eapply (pi_field _ _ _ 10 _ _ _ _ _ _ 0 8%N _ _ RG3 eq_refl);
  [ repeat (first [left; reflexivity | right]) | exact D33 | cbn; lia | cbn; lia ]. }
assert (Med : val_mem SEGS (rdW W (ms_mem ms')) (q + 8) 8 (text + len)).
{ replace (q + 8) with (bv_unsigned (ew EE 10) + 8) by lia.
  eapply (pi_field _ _ _ 10 _ _ _ _ _ _ 8 8%N _ _ RG3 eq_refl);
  [ repeat (first [left; reflexivity | right]) | exact D34 | cbn; lia | cbn; lia ]. }
assert (Mdp : val_mem SEGS (rdW W (ms_mem ms')) (q + 16) 4 (Z.of_nat d + 1)).
{ replace (q + 16) with (bv_unsigned (ew EE 10) + 16) by lia.
  eapply (pi_field _ _ _ 10 _ _ _ _ _ _ 16 4%N _ _ RG4 eq_refl);
  [ repeat (first [left; reflexivity | right]) | exact D35 | cbn; lia | cbn; lia ]. }
assert (Mty : val_mem SEGS (rdW W (ms_mem ms')) v 4 (if o then 6 else 5)).
{ replace v with (bv_unsigned (ew EE 11) + 0) at 1 by lia.
  eapply (pi_field _ _ _ 11 _ _ _ _ _ _ 0 4%N _ _ RG5 eq_refl);
  [ repeat (first [left; reflexivity | right]) | exact DTY | destruct o; cbn; lia | cbn; lia ]. }
assert (RWq : rd_rw SEGS (rdW W (ms_mem ms')) q 24)
  by (intros x Hx; apply (writable_at_grows SEGS _ _ x HGR); apply Hqrw; exact Hx).
assert (RWv : rd_rw SEGS (rdW W (ms_mem ms')) v 56)
  by (intros x Hx; apply (writable_at_grows SEGS _ _ x HGR); apply Hvrw; exact Hx).
(* what the prologue did not write *)
assert (NWlow : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (v <= a < v + 56) -> ~ pie_wset regs q v a).
{ intros a Ha Hv. unfold pie_wset. intros [Hf | [Hf | [Hf | Hf]]]; lia. }
assert (NWsh : forall a, SHADOW_OFF <= a < kHighMemBeg -> ~ pie_wset regs q v a).
{ intros a Ha. unfold pie_wset.
  intros [Hf | [Hf | [Hf | Hf]]]; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *; lia. }
assert (KT : forall a, text <= a < text + len -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KEPT; [lia|]. apply NWlow; [lia|]. destruct Htv; lia. }
assert (KSH : forall a, 0 <= a < 2 ^ 47 ->
  aview SEGS (w_H W) (ms_mem ms') (shadow_of_addr SHADOW_OFF a) = aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF a)).
{ intros a Ha. unfold shadow_of_addr. apply KEPT; [unfold SHADOW_OFF; lia|]. apply NWsh. unfold SHADOW_OFF, kHighMemBeg; lia. }
assert (KV : forall x, v + 4 <= x < v + 56 -> aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) mem x).
{ intros x Hx. apply KEPT; [lia|]. unfold pie_wset.
  intros [Hf | [Hf | [Hf | Hf]]]; first [lia | destruct Hqv as [Hqv' | Hqv']; lia]. }
assert (Z8 : forall off, 8 <= off -> off + 8 <= 56 -> rd_u64 SEGS (rdW W (ms_mem ms')) (v + off) 0).
{ intros off H1 H2. destruct (pie_zero_u64 _ v off HZ ltac:(lia) H2) as [Hr Hvm]. split; [exact Hr|].
  apply (pi_val_kept (L := Lb) (PI := PIb) (w_H W) mem (ms_mem ms')); [|exact Hvm].
  intros x Hx. apply KV. lia. }
(* the ledger at the call *)
assert (LEDc : prh_ledger B ly S Hp W (ms_mem ms') Lam peak cnt fail ran most own).
{ eapply pie_ledger_kept; [exact HLED | |].
  - intros a Ha. pose proof (pie_img_below a (pst_in_img_B a Ha)) as Hlo. apply KEPT; [unfold kLowMemEnd in Hlo; lia|].
    unfold pie_wset. intros [Hf | [Hf | [Hf | Hf]]]; try (unfold kLowMemEnd in Hlo; lia).
    apply (Hvimg a ltac:(lia) (pst_in_img_B a Ha)).
  - intros a kk x Hin Hx.
    pose proof HLED as HF. apply prh_ledger_blocks in HF. pose proof (proj1 (Forall_forall _ _) HF (a, kk) Hin) as (Hk & Hblk & _).
    cbn [fst snd] in Hk, Hblk.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & H4096 & Hc & _).
    assert (Hrq : kk + cf_head <= req_size (kk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    apply KEPT; [lia|]. unfold pie_wset. intros [Hf | [Hf | [Hf | Hf]]]; try lia.
    exact (pie_head_apart B ARx HL LAWS ly S Hp W mem md Lam peak cnt fail ran most own regs e v H8 HAR HLED Hat
      ltac:(lia) a kk x Hin Hx ltac:(lia)). }
(* the cursor, the text, the node and the ledger at the call (pi_cur at p + 1, depth d + 1) *)
assert (HTXT : garr8 SEGS (rdW W (ms_mem ms')) text tb)
  by (apply (pi_garr8_kept (L := Lb) (PI := PIb) (w_H W) mem (ms_mem ms')); [rewrite Hlen; exact KT | exact Hsrc]).
assert (PCUR : pi_cur (L := Lb) (PA := PIb) B regs e q v text len tb d ly S Hp W (ms_mem ms') (p + 1) Lam peak cnt fail ran
  most own).
{ split.
  { split; [exact Mp|]. split; [exact Med|]. split; [exact Mdp|]. split; [exact RWq|]. split; [exact Hq8|].
    split; [exact Ht0|]. split; [exact Htl|]. split; [lia|]. split; [exact Hlen|]. split; [exact HTXT|].
    split; [exact Hdqt | lia]. }
  split; [apply (pi_ra_kept (L := Lb) (PI := PIb) (w_H W) mem (ms_mem ms')); [intros x Hx; apply KSH; lia | exact Hqra]|].
  split.
  { split; [exact HTXT|]. split; [exact Ht4|]. split; [rewrite Hlen; exact Htc|]. split; [rewrite Hlen; exact Htam|].
    split; [rewrite Hlen; apply (pi_ra_kept (L := Lb) (PI := PIb) (w_H W) mem (ms_mem ms'));
      [intros x Hx; apply KSH; lia | exact Htra]|].
    intros Hn. rewrite Hlen in Hn |- *. intros s Hs. specialize (Hthv Hn s Hs).
    unfold shadow_addr in Hs. rewrite KEPT; [exact Hthv | unfold SHADOW_OFF in Hs |- *; lia |].
    apply NWsh. unfold SHADOW_OFF, kHighMemBeg in Hs |- *. lia. }
  split; [exact HHOME|]. split; [exact Hat|].
  split; [apply (pi_ra_kept (L := Lb) (PI := PIb) (w_H W) mem (ms_mem ms')); [intros x Hx; apply KSH; lia | exact Hvra]|].
  split; [exact LEDc|].
  assert (Hlr : length (rest_atR tb text (p + 1)) = (length (rest_atR tb text p) - 1)%nat)
    by (unfold rest_atR; rewrite !length_skipn; lia).
  assert (Hlr0 : (1 <= length (rest_atR tb text p))%nat) by (unfold rest_atR; rewrite length_skipn; lia).
  rewrite Hlr. lia. }
(* the frame at the call *)
assert (FRc : pi_frame regs (ms_regs ms') W mem W (ms_mem ms') e q v).
{ apply (pie_frame_at regs (ms_regs ms') W mem (ms_mem ms') e q v EE RG0 B2
    DR Usp Q3 Q4); [| exact Hra | exact He0 | exact He16].
  intros a Ha Hn. apply KEPT; [lia|]. unfold pie_wset. intros [Hf | [Hf | [Hf | Hf]]]; [lia | | |]; apply Hn.
  - exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; lia].
  - exists (q + 16, q + 20). split; [right; left; reflexivity | cbn [fst snd]; lia].
  - exists (v, v + 56). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
(* the frame-pointer chain the call sees: s0 = q + 16, whose two words below are the end and the cursor (the cursor
   lies in the text, below alloc_ceiling and so below q, so the chain stops there) *)
pose proof HJ as HJ0. unfold pi_aj, pi_ajR in HJ0.
pose proof HJ0 as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastkc & _ & _).
assert (HCH : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms')) (spZ regs - PI_FRAME) (q + 16) ch1).
{ destruct (Z_lt_le_dec (q + 16) (ly_top ly - 16)) as [Hlt | Hge].
  - exists [(q + 16, text + len, p + 1)]. right.
    split; [unfold PI_FRAME; lia|]. split; [exact Hlt|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
    split.
    + cbn [fpchain]. split; [reflexivity|]. split; [rewrite Z.add_mod, Hq8 by lia; reflexivity|].
      split; [replace (q + 16 - 8) with (q + 8) by lia; apply (pie_rdword_of_val (w_H W) (ms_mem ms') (q + 8) (text + len));
              [exact Med | lia]|].
      split; [replace (q + 16 - 16) with q by lia; apply (pie_rdword_of_val (w_H W) (ms_mem ms') q (p + 1));
              [exact Mp | lia]|].
      split; [lia|].
      unfold bad_next. replace (p + 1 <=? q + 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    + constructor; [cbn [fst]; unfold PI_FRAME; lia | constructor].
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH as (ch1 & HCH).
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  eapply (aj_call_xW_sp (SK := SK) SEGS B prh_pst ARx LAWS (pa_segs_low (PAImg := PIb)) W EE _ ms'
    (STK_parse_items d + e) (spZ regs + e) (rd_fp q v) ly S Hp W mem md [] ly S Hp _ k'
    STK_skip_ws (PI_FRAME + e) [(q, q + 8)] (- (PI_FRAME + e)) (Z_to_bv 64 (VAL A_TEXT + PIE_HEAD)) ch1
    (fQmn (ms_mem ms') (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
       prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
       pj_in_okR SEGS (rdW W' mem') q text len
         (text + len - Z.of_nat (length (PjGrammar.skip (rest_atR tb text (p + 1))))) (Z.of_nat d + 1) tb))
    HS eq_refl HJ).
  - rewrite Usp. unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.mod_opp_l_z; [reflexivity | lia | rewrite Z.add_mod, He16 by lia; reflexivity].
  - unfold PI_FRAME. lia.
  - exact HSKW0.
  - unfold STK_skip_ws, PI_FRAME in *. lia.
  - unfold PI_FRAME. lia.
  - unfold PI_FRAME. rewrite Z.add_mod, He16 by lia; reflexivity.
  - lia.
  - rewrite Q3. exact Hgp.
  - rewrite Q4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold PIE_HEAD; lia | reflexivity].
  - pose proof (pa_B_ok (PAImg := PIb)) as HB. pose proof (pa_val_range (PAImg := PIb) A_TEXT) as HBr.
    unfold PIE_HEAD. rewrite unsigned_lit_small by lia. vm_compute. discriminate.
  - replace (spZ regs + e + - (PI_FRAME + e)) with (spZ regs - PI_FRAME) by (unfold PI_FRAME; lia).
    rewrite Us0. exact HCH.
  - intros HAF HWIN'. cbn [ss_pc setpc].
    pose proof PCUR as (PIN & PRA & PSRC & _).
    refine (TSKW fx ly S Hp W (ms_regs ms') (ms_mem ms') md' ch1 (PI_FRAME + e) q text len (p + 1) (Z.of_nat d + 1) tb
      Lam peak cnt fail ran most own _ Ra0 PIN HWIN' _ _ PRA PSRC HHOME LEDc).
    + split; [exact HAF|]. split.
      { apply (pie_rod_kept (STK_parse_items d + e) (spZ regs + e) (rd_fp q v) ly S Hp W mem md [] ly S Hp W (ms_mem ms')
          md' k' HJ0); [|exact Erod].
        intros (r & Hr & H0). cbn [rd_fp In] in Hr.
        destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in H0; lia. }
      split; [rewrite Usp; unfold PI_FRAME; lia|].
      (* fpre's frm_zero (FRM0-ENTRY): the prologue runs no float instruction, so the rounding mode is the entry's *)
      split; [|exact HFRM].
      unfold raZ. rewrite R1. pose proof (pa_val_range (PAImg := PIb) A_TEXT) as HBr.
      pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR'. unfold ASAN_CEIL in CR'.
      unfold PIE_HEAD. let w := eval vm_compute in (VAL A_TEXT) in change (VAL A_TEXT) with w.
      rewrite unsigned_lit_small by lia. lia.
    + rewrite Usp. unfold PI_FRAME. lia.
    + rewrite Usp. unfold PI_FRAME. lia.
  - intros a (r & Hr & Ha). left. exists r. split; [|exact Ha].
    destruct Hr as [<- | []]. left. reflexivity. }
(* back at the return site 0x87b24 *)
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HKS &
  ((Hrk & HHp & HSeq & Hab & Hled2 & Hin2) & HMNk)).
replace (spZ regs + e + - (PI_FRAME + e)) with (spZ regs - PI_FRAME) in HJ1 by (unfold PI_FRAME; lia).
replace (spZ regs + e + - (PI_FRAME + e)) with (spZ regs - PI_FRAME) in HX by (unfold PI_FRAME; lia).
replace (Z_to_bv 64 (VAL A_TEXT + PIE_HEAD)) with (w64 (VAL A_TEXT + PI_AT (L := Lb) (PI := PIb) PI_O_HEAD))
  by (unfold w64; f_equal; vm_compute; reflexivity).
pose proof HJ2 as (HAR2 & HLY2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk2 & _ & _).
pose proof Hastk2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
pose proof HLY2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo2 & Eshi2 & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo1 & Eshi1 & _).
(* the registers at the return site: skip_ws keeps every callee-saved one *)
assert (S9 : getr regs2 9 = w64 q) by (rewrite <- Q9; exact (HKS 9 ltac:(unfold acallee_saved; lia))).
assert (S8 : getr regs2 8 = w64 (q + 16)) by (rewrite <- Q8; exact (HKS 8 ltac:(unfold acallee_saved; lia))).
assert (S18 : getr regs2 18 = w64 (if o then 1 else 0)) by (rewrite <- Q18; exact (HKS 18 ltac:(unfold acallee_saved; lia))).
assert (S19 : getr regs2 19 = w64 v) by (rewrite <- Q19; exact (HKS 19 ltac:(unfold acallee_saved; lia))).
assert (S21 : getr regs2 21 = w64 (-1)) by (rewrite <- Q21; exact (HKS 21 ltac:(unfold acallee_saved; lia))).
assert (S25 : getr regs2 25 = w64 (pi_sh (q + 16))) by (rewrite <- Q25; exact (HKS 25 ltac:(unfold acallee_saved; lia))).
assert (S26 : getr regs2 26 = w64 SHADOW_OFF) by (rewrite <- Q26; exact (HKS 26 ltac:(unfold acallee_saved; lia))).
assert (S27 : getr regs2 27 = w64 (pi_sh q)) by (rewrite <- Q27; exact (HKS 27 ltac:(unfold acallee_saved; lia))).
assert (S2r : getr regs2 2 = getr (ms_regs ms') 2) by exact (HKS 2 ltac:(unfold acallee_saved; lia)).
assert (S3 : getr regs2 3 = getr (ms_regs ms') 3) by exact (HKS 3 ltac:(unfold acallee_saved; lia)).
assert (S4 : getr regs2 4 = getr (ms_regs ms') 4) by exact (HKS 4 ltac:(unfold acallee_saved; lia)).
assert (Usp2 : spZ regs2 = spZ (ms_regs ms')) by (unfold spZ; rewrite S2r; reflexivity).
(* the cursor skip_ws left *)
set (y := rest_atR tb text (p + 1)) in *.
set (p1 := text + len - Z.of_nat (length (PjGrammar.skip y))) in *.
pose proof (PjGrammar.skip_len y) as Hsk.
assert (Hly : length y = (length (rest_atR tb text p) - 1)%nat) by (unfold y, rest_atR; rewrite !length_skipn; lia).
assert (Hlr0 : (1 <= length (rest_atR tb text p))%nat) by (unfold rest_atR; rewrite length_skipn; lia).
assert (Hrp : length (rest_atR tb text p) = Z.to_nat (text + len - p)) by (unfold rest_atR; rewrite length_skipn; lia).
assert (Hlr1 : length (rest_atR tb text p1) = length (PjGrammar.skip y)).
{ unfold rest_atR at 1. rewrite length_skipn. unfold p1. lia. }
(* the cursor, the text, the node's place and the ledger at the return state (PItems_kept.v's statement) *)
assert (HCUR2 : pi_cur (L := Lb) (PA := PIb) B regs e q v text len tb d ly2 S2 Hp2 W2 mem2 p1 Lam peak cnt fail ran
  most own).
{ (* skip_ws is unbudgeted: its journal is the empty-budget one, WS1 := [] *)
  apply (HKC regs e q v text len tb d ly S Hp W (ms_mem ms') md' (p + 1) Lam peak cnt fail ran most own
    STK_skip_ws (spZ regs - PI_FRAME) (PI_FRAME + e) [(q, q + 8)] [] ly2 S2 Hp2 W2 mem2 md2 k1 p1 Lam peak cnt fail ran
    most own []).
  - exact PCUR.
  - exact HJ1.
  - exact HX.
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - lia.
  - destruct HHOME as [[(b & m & Hbin & Hb1 & Hb2) | Hro] | (b & m & Hbin & _ & Hb1 & Hb2)].
    + right; right. pose proof HLED as HHB. apply prh_ledger_blocks in HHB.
      pose proof (proj1 (Forall_forall _ _) HHB _ Hbin) as (K0 & Kin & _). cbn [fst snd] in K0, Kin.
      exists (b - cf_head), (m + cf_head). split; [exact Kin | lia].
    + destruct Hro as [Hro | Hki]; [left; exact Hro | right; left; exact Hki].
    + right; right. exists b, m. auto.
  - intros b m Hbin _. rewrite Hab, HHp. split; [exact Hbin | tauto].
  - intros a Ha (r & Hr & Hrr). destruct Hr as [<- | []]. cbn [fst snd] in Hrr. lia.
  - intros a Ha (r & Hr & Hrr). destruct Hr as [<- | []]. cbn [fst snd] in Hrr. unfold shadow_of_addr in Hrr.
    unfold amem_range in Htam. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - intros a Ha (r & Hr & Hrr). destruct Hr as [<- | []]. cbn [fst snd] in Hrr. unfold shadow_of_addr in Hrr.
    unfold amem_range in Hvam. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
  - intros (r & Hr & H0). destruct Hr as [<- | []]. cbn [fst snd] in H0. lia.
  - left. exact Hin2.
  - exact Hled2.
  - rewrite Hlr1. lia.
  - left. reflexivity.
  - intros a kk Hk _. exact Hk.
  - exact Hsq.
  - exact Hqe.
  - intros a kk Hk. left. exact Hk.
  - exact HARc. }
(* the node's bytes across the call *)
assert (KN : forall a, v <= a < v + 56 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms') a).
{ apply (HKN regs e v ly S Hp W (ms_mem ms') md' STK_skip_ws (spZ regs - PI_FRAME) (PI_FRAME + e) [(q, q + 8)] []
    ly2 S2 Hp2 W2 mem2 md2 k1 Lam [] Hat HJ1 HX).
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - unfold PI_FRAME; lia.
  - lia.
  - intros a Ha (r & Hr & Hrr). destruct Hr as [<- | []]. cbn [fst snd] in Hrr. destruct Hqv; lia.
  - intros b m Hbin _ _. rewrite Hab. exact Hbin.
  - intros a kk Hin. pose proof HLED as HHB. apply prh_ledger_blocks in HHB.
    pose proof (proj1 (Forall_forall _ _) HHB _ Hin) as (_ & Kin & _). exact Kin.
  - exact Hvw. }
assert (KNv : forall x, v <= x < v + 56 -> mbyte SEGS (rdW W2 mem2) x = mbyte SEGS (rdW W (ms_mem ms')) x /\
  (writable_at SEGS (rdW W (ms_mem ms')) x -> writable_at SEGS (rdW W2 mem2) x))
  by (intros x Hx; apply pie_agree_view; [lia | apply Hvimg; lia | apply KN; lia]).
assert (VK2 : forall a n x, v <= a -> a + Z.of_nat n <= v + 56 ->
  val_mem SEGS (rdW W (ms_mem ms')) a n x -> val_mem SEGS (rdW W2 mem2) a n x).
{ intros a n x H1 H2 Hv kk Hk. rewrite (proj1 (KNv (a + Z.of_nat kk) ltac:(lia))). exact (Hv kk Hk). }
(* the frame across the call *)
assert (FR2 : pi_frame regs regs2 W mem W2 mem2 e q v).
{ apply (pie_frame_win regs (ms_regs ms') regs2 W mem W W2 (ms_mem ms') mem2 e q v FRc Usp2
    ltac:(rewrite S3; reflexivity) ltac:(rewrite S4; reflexivity) Hsq).
  intros a Ha Hn. apply HX; [rewrite Usp in Ha; unfold PI_FRAME in *; lia|].
  intros (r & Hr & Hrr). destruct Hr as [<- | []]. cbn [fst snd] in Hrr. lia. }
(* PItems_head.v's segment, at the entry's empty budget WS0 = [], its journal at wle' *)
apply (HEAD fx fx ly S Hp W mem md ch CTX regs e q v o text len tb p Lam peak cnt fail ran most own kr ly2 S2 Hp2 W2 mem2
  md2 (k' + k1) regs2 []
  (@pie_aj_lift ly S Hp W mem md regs d e q v ly2 S2 Hp2 W2 mem2 md2 (k' + k1) [] HJ2) (pie_wbudget_nil CW)).
unfold pi_head_pre.
split; [split; [exact HFRM | intros r Hr; reflexivity]|].
split; [exact HENT|].
split; [exact (HMNk HMNc)|].
(* the travelling position and live requests over the empty prefix trace: skip_ws keeps S (HSeq : S2 = S) *)
split; [exact (PItems_posb.pi_posb_eq S S S2 [] HSeq (PItems_posb.pi_posb_nil S))|].
split; [eapply PItems_posb.pi_live_eq; [|apply PItems_posb.pi_live_nil]; rewrite HSeq; apply Permutation_refl|].
split; [exact FR2|].
split; [exact S9|]. split; [exact S19|]. split; [exact S18|]. split; [exact S8|].
split; [exact S26|]. split; [exact S27|]. split; [exact S25|]. split; [exact S21|].
split; [unfold PjGrammar.MAXD; exact Hd32|].
split; [exact Hab|].
exists p1. split; [unfold p1, y; exact (pie_rest_skip tb text len p Hlen ltac:(lia))|].
split; [exact HCUR2|].
split.
{ split.
  { split; [split; [exact Hv8 | intros x Hx; apply (proj2 (KNv x Hx)); apply RWv; exact Hx]|].
    split; [split; [destruct o; lia | apply VK2; [lia | cbn; lia | exact Mty]]|].
    split; [destruct (Z8 8 ltac:(lia) ltac:(lia)) as [Z0 Zv]; split; [exact Z0 | apply VK2; [lia | cbn; lia | exact Zv]]|].
    split; [destruct (Z8 16 ltac:(lia) ltac:(lia)) as [Z0 Zv]; split; [exact Z0 | apply VK2; [lia | cbn; lia | exact Zv]]|].
    split; [destruct (Z8 24 ltac:(lia) ltac:(lia)) as [Z0 Zv]; split; [exact Z0 | apply VK2; [lia | cbn; lia | exact Zv]]|].
    split; [destruct (Z8 32 ltac:(lia) ltac:(lia)) as [Z0 Zv]; split; [exact Z0 | apply VK2; [lia | cbn; lia | exact Zv]]|].
    split; [destruct (Z8 40 ltac:(lia) ltac:(lia)) as [Z0 Zv]; split; [exact Z0 | apply VK2; [lia | cbn; lia | exact Zv]]|].
    destruct (Z8 48 ltac:(lia) ltac:(lia)) as [Z0 Zv]; split; [exact Z0 | apply VK2; [lia | cbn; lia | exact Zv]]. }
  split; [reflexivity|]. split; [lia|]. split; [lia|].
  split; [left; split; [reflexivity | split; reflexivity]|].
  split; [intros _; reflexivity|].
  split; [constructor|]. split; [intros b x Hb; destruct Hb|].
  destruct o; reflexivity. }
pose proof Eroom as (RL1 & RL2 & RL3).
split; [exact (Hrk RL1)|]. split; [exact RL2|].
(* The batch kit's tip 03fcabb582d0: rd_room's live conjunct is prh_live_evs over the live list, and skip_ws keeps the state *)
first [rewrite HSeq; exact RL3 | rewrite <- HSeq; exact RL3].
Qed.

(* THE ENTRY OF parse_items, image B': the kit's tparse_items_specX d CTX CTX0 CW (the batch kit 240b06ed4fd4), from the entry
   block (pie_core), the depth refusal (pie_refuse, closed) and the skip_ws call (pie_call: skip_ws_mn.v's skip_ws_holds,
   then PItems_head.v's segment), the post at the budget wbudget CW 0. The text's hull budget (Hhull) is threaded to the
   walk as pi_ent's last conjunct. Instance fact taken: 8 <= cf_head (the harness head covers a head word; alloc.c's
   HEAD is 16), so a harness head is never a node byte. *)
Theorem pi_entry_holds : 8 <= cf_head -> forall CTX : list (list Z),
  tparse_items_specX (fx := fx) (L := Lb) (PA := PIb) B ARx SK d CTX CTX0 CW.
Proof.
intros H8 CTX ly S Hp W regs mem md ch e q text len p tb v o Lam peak cnt fail ran most own
  HFPRE HMN Hin Hclo Hcent Hcw Hchn Hpart H10 H11 H12 HRDP Hplt Hnth Hroom Hwr Hpk1 Hpk2 Hhull Hch0 Hfrms.
pose proof HFPRE as (HAFN & Hrod & Hshi64 & Hra0 & Hfrm0).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & _).
pose proof HRDP as (HFRM & _ & _ & _ & HIN & HWIN & Hsq & Hqe & Hqra & HSRC & HHOME & _ & HNODE & Hqv & Htv & Hvw & HLED
  & HdM & HCNT).
pose proof Hroom as (HRL & _ & _).
pose proof (pie_stk_skw d) as HSTKB. unfold STK_skip_ws, PI_FRAME in HSTKB.
pose proof (pi_frame_nonneg F_skip_ws) as HSKW0.
assert (HSTK : 144 <= STK_parse_items d) by lia.
assert (HENT : pi_ent (L := Lb) (PA := PIb) B fx ly S Hp W regs mem ch CTX Lam peak cnt fail ran most own e q text len p
  d 0 tb v o CTX0 CW).
{ unfold pi_ent. repeat (split; [assumption|]). assumption. }
apply (pie_core (YCbqGwild.wbudget CW 0) ly S Hp W regs mem md ch e q v text len p tb o Lam peak cnt fail ran most own 0
  HAFN HMN HWIN HFRM H10 H11 H12 HIN Hsq Hqe Hqra HNODE Hqv HLED HRL H8 HSTK).
- intros ms' md' k' HS HJ KEPT HGR HMN' Hd.
  exact (pie_refuse (YCbqGwild.wbudget CW 0) ly S Hp W regs mem md ch e q v text len p tb o Lam peak cnt fail ran most
    own 0 ms' md' k' (pie_wbudget_nil CW) HAFN HWIN HFRM H10 H11 H12 HIN Hsq Hqe HNODE Hqv HLED HRL H8 HSTK HS HJ KEPT
    HGR HMN' Hd).
- intros ms' md' k' HS HJ KEPT HGR HMN' Hd.
  exact (pie_call ly S Hp W regs mem md ch CTX e q v text len p tb o Lam peak cnt fail ran most own 0
    ms' md' k' HENT HAFN Hshi64 H8 HS HJ KEPT HGR HMN' Hd).
Qed.

End call.

End core.

Check pi_entry_holds.
Print Assumptions pi_entry_holds.
Print Assumptions pi_epi_holds.
Print Assumptions pi_post_stable.
