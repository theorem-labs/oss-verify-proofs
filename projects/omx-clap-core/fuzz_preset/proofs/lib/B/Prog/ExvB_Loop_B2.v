(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL piece B2 (the separator): ExvB_Loop_Stmt.v's
   CUT_LS (B 0x83ca0 = exv_pc 0x774, the nested ex_value returned 0) from the downstream cuts CUT_CX, CUT_CC and
   CUT_CLm at m - 1: `mv a0, s3; jal ex_ws` (B 0x83ca0 / 0x83ca4), ex_ws's PROVED text (EXV_HYP's exv_ws) in the
   caller-window form (YCbqGcallW.v aj_call_xW_sp: window e1 = exv_sp E + e_d E - exv_s1 E, callee sp = exv_s1 E,
   o = exv_s1 E - (exv_sp E + e_d E), FP1 = [(q, q + 8)]), EXBs re-seated after the call (KIT_CALLs), then
   ExvB_Loop_B2_post.v's stretch from the return site B 0x83ca8 to the three cuts. in->p after ex_ws is x0 + ip'
   with ip' = len - |skip (x from ip2)|; the grammar's continuation reads from ip' (PURE_SUFFIX, skip a suffix).
   Old-pin kit rebind (4f18c75d4900): ex_ws's m-form post (fpostWm: its Q with S' = S, plus the memnorm keep from
   the call memory), so the room is exv_room_refl and the keep composes with EXB's (exvl_P (e_mem E)); the memnorm
   keep rides the table runs by ExvB_Loop_exw.v's SRr_run_to_tok_AJx_inv into KIT_RUNs / KIT_CALLs; fpre's
   `raZ < alloc_ceiling` from the jal's return pc B2_PC (a listing literal below 2 ^ 32).
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 0x774, 0x77c (DERIVED: B 0x83ca0 / 0x83ca8 minus B's ex_value entry); 8, 16, 24, 32, 40 (LENGTH: struct
   ex fields); 288, 304 (LENGTH: ex_value's frame realignment); 2 ^ 64, 2 ^ 32, 4096 (LENGTH: bounds); register numbers 1-4,
   8-10, 18-27 (WORD). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_kit ExvB_Loop_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Open_kt ExvB_Loop_exw.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_B2_seat ExvB_Loop_B2_post.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- pure: the whitespace skip leaves a suffix, and skipping twice is skipping once ---- *)
Lemma b2_skip_suffix : forall y : list Z, exists k, PjGrammar.skip y = skipn k y.
Proof.
induction y as [|b r IH]; [exists 0%nat; reflexivity|]. cbn [PjGrammar.skip].
destruct (PjGrammar.ws b); [destruct IH as (k & Hk); exists (S k); exact Hk | exists 0%nat; reflexivity].
Qed.
Lemma b2_skip_idem : forall y : list Z, PjGrammar.skip (PjGrammar.skip y) = PjGrammar.skip y.
Proof.
induction y as [|b r IH]; [reflexivity|]. cbn [PjGrammar.skip].
destruct (PjGrammar.ws b) eqn:Hw; [exact IH | cbn [PjGrammar.skip]; rewrite Hw; reflexivity].
Qed.

(* the stretch to the call: no state, no fact *)
Definition ss_b2c : sstate := mkSS B2_LS sr_atoms [] None (mkFacts [] [] []).
(* the registers the stretch to the call keeps (it writes a0 and ra) *)
Definition b2_keep0 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma b2_ra_ok : YK0s.ret_ok (w64 B2_PC) /\ 4096 <= bv_unsigned (w64 B2_PC) /\ bv_unsigned (w64 B2_PC) < 2 ^ 32.
Proof.
split; [unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity |].
split; [vm_compute; intros H; discriminate H | vm_compute; reflexivity].
Qed.

(* acallee_saved of a register literal *)
Ltac b2_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] =>
    let z := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with z end; lia.

Section b2. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis KRUN : forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK.
Hypothesis KOFS : forall fx : YK11.FPState, KIT_EXB_OF_S (fx := fx) B ARx SK.
Hypothesis KCALL : forall fx : YK11.FPState, KIT_CALLs (fx := fx) B ARx SK.
Hypothesis KCHAIN : forall fx : YK11.FPState, KIT_CALL_CHAIN (fx := fx) B ARx SK.
Hypothesis KROD : forall fx : YK11.FPState, KIT_RODATA (fx := fx) B ARx SK.
Hypothesis PSUF : PURE_SUFFIX.
Lemma b2_val_kept2 : forall H H' (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview rsegs H' m' x = aview rsegs H m x) ->
  val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview rsegs H H' m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.

Lemma exvl_B2 : forall n m,
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_CLm (fx := fx) B ARx SK n (m - 1)) ->
  forall fx : YK11.FPState, CUT_LS (fx := fx) B ARx SK n m.
Proof.
intros n m HCX HCC HCL fx.
pose proof (b2_post_ok B ARx SK HYP KRUN KOFS fx n m (HCX fx) (HCC fx) (HCL fx)) as HPOST.
unfold b2_post in HPOST. cbv zeta in HPOST.
unfold CUT_LS. intros E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip2 vv dlc nm u. cbv zeta.
intros Hn HPRE HBs Hi1 Hc1 Hc Hdep Hacc Hcur Hip Hdl Hii Hm HV Hdif H21 H27 H22 H23 HSP.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HBs as (regs0 & HB & HAG).
destruct (b2_geom B ARx SK HYP fx E lyc Sc Hpc Wc regs0 memc mdc k pos HPRE HB)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & GPRES & GAR).
pose proof HPRE as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (HFN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PLEN & _).
destruct HFN as (_ & _ & HFN64).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & _ & _ & HFZ & _ & _ & (_ & HPM) & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4
  & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HJ as (_ & JLY & _).
destruct JLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
pose proof Hcur as (Vq & Ve & Vdep & Vscr & Vdl).
assert (Hlen0 : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
(* ---- B 0x83ca0 .. ex_ws's entry ---- *)
remember (Ereg regs []) as E0 eqn:HE0.
assert (HS : st_ok rsegs E0 ss_b2c (restrict (w_H Wc) (@YK11.mkst fx regs (Z_to_bv 64 B2_LS) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_b2c. apply exw_st_ok_full.
  - rewrite HE0. apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok rsegs B2_BX [] E0 (mrestrict (w_H Wc) memc)) by constructor.
pose (RUNTO := SRr_run_to_tok_AJx_inv (fx := fx) (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low
  B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P (e_mem E)) (exvl_PLAW (e_mem E))).
unfold cfg_at. change (w64 (exv_pc 0x774)) with (Z_to_bv 64 B2_LS).
exw_run_to RUNTO HS HJ SHOK HPM (B_prog_sigma AS_ex_ws).
{ apply awr_ok_nil. }
exw_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac).
rename KEPT into K0.
lazymatch type of HS with st_ok _ ?Ex' _ _ =>
  assert (AG : env_agree 32 (Ereg regs []) Ex')
    by (rewrite HE0; split; [intros nn Hnn; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; reflexivity
                            | reflexivity]) end.
assert (KR : forall r, In r b2_keep0 -> getr (ms_regs ms) r = getr regs r)
  by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ b2_keep0 HS AG ltac:(vm_compute; reflexivity) r Hr)).
assert (KRb : forall r, In r exv_bregs -> r <> 24%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr _. apply KR. unfold exv_bregs in Hr. unfold b2_keep0. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; b2_in. }
assert (HBs1 := KRUN fx E lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms) (ms_mem ms) _ HPRE HBs HJ
  (fun a Ha _ _ _ => K0 a Ha (fun x => x)) (fun a Ha => apresent_grows _ _ _ a HG Ha) HPM KRb).
pose proof HBs1 as (regs1 & HB1 & HAG1).
pose proof HB1 as HB10. unfold EXB in HB10. cbv zeta in HB10.
destruct HB10 as (_ & _ & _ & _ & _ & _ & _ & HLED1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HSRC1 & HINB1 & _ & _ & _ & _).
assert (RKc : forall r : bv 5, r <> 24%bv -> In r b2_keep0 -> getr (ms_regs ms) r = getr regs0 r)
  by (intros r Hr24 Hr; rewrite (KR r Hr); exact (HAG r Hr24)).
assert (R2c : getr (ms_regs ms) 2 = w64 (exv_s1 E)) by (rewrite (RKc 2%bv ltac:(discriminate) ltac:(b2_in)); exact R2).
assert (R8c : getr (ms_regs ms) 8 = w64 (exv_sp E)) by (rewrite (RKc 8%bv ltac:(discriminate) ltac:(b2_in)); exact R8).
assert (R3c : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite (RKc 3%bv ltac:(discriminate) ltac:(b2_in)); exact R3).
assert (R4c : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite (RKc 4%bv ltac:(discriminate) ltac:(b2_in)); exact R4).
assert (Usp : spZ (ms_regs ms) = exv_s1 E) by (unfold spZ; rewrite R2c; unfold w64; apply unsigned_lit_small; lia).
assert (Us0 : s0Z (ms_regs ms) = exv_sp E) by (unfold s0Z; rewrite R8c; unfold w64; apply unsigned_lit_small; lia).
prreg HS (1%bv : bv 5) R1c.
assert (Rra : getr (ms_regs ms) 1 = w64 B2_PC) by (rewrite R1c; unfold w64; f_equal; vm_compute; reflexivity).
prreg HS (10%bv : bv 5) R10c. cbn [ew ewset Nat.eqb] in R10c.
rewrite HE0, (ew_Ereg_nat regs [] 19 19%bv eq_refl), (HAG 19%bv ltac:(discriminate)), R19 in R10c.
destruct (KCHAIN fx E lyc Sc Hpc Wc regs1 (ms_mem ms) _ k pos (ms_regs ms) HPRE HB1 R2c R8c) as (ch1 & HCH & _).
destruct (KROD fx E lyc Sc Hpc Wc regs1 (ms_mem ms) _ k pos HPRE HB1) as (HROD & _).
assert (Vq1 : val_mem rsegs (mrestrict (w_H Wc) (ms_mem ms)) (e_q E) 8 (e_x0 E + ip2)).
{ apply (exw_val_kept rsegs (w_H Wc) memc (ms_mem ms)); [|exact Vq]. intros x Hx. apply K0; [lia | tauto]. }
assert (Ve1 : val_mem rsegs (mrestrict (w_H Wc) (ms_mem ms)) (e_q E + 8) 8 (e_x0 E + exv_len E)).
{ apply (exw_val_kept rsegs (w_H Wc) memc (ms_mem ms)); [|exact Ve]. intros x Hx. apply K0; [lia | tauto]. }
assert (HFP1 : forall a, inFP [(e_q E, e_q E + 8)] a -> inFP (exv_FP E) a).
{ intros a (r0 & Hr0 & Ha0). exists r0. split; [|exact Ha0]. destruct Hr0 as [<- | []]. right. left. reflexivity. }
(* ---- the call ---- *)
eapply SRr_bind.
{ eapply (aj_call_xW_sp (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low Wc _ _ ms
    (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)]
    lyc Sc Hpc _ k STK_ex_ws (exv_sp E + e_d E - exv_s1 E) [(e_q E, e_q E + 8)] (exv_s1 E - (exv_sp E + e_d E))
    (w64 B2_PC) ch1
    (fun ly' S' Hp' (W' : world rsegs) (regs' : bvmap 5 word) mem' md' =>
       ((room_live_cf Sc -> room_live_cf S') /\
        val_mem rsegs (mrestrict (w_H W') mem') (e_q E) 8
          (e_x0 E + Z.of_nat (length (e_x E)) - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat ip2) (e_x E)))))
        /\ Hp' = Hpc /\ S' = Sc /\ ablocks B ly' S' = ablocks B lyc Sc /\
        prh_ledger (L := B_prog_listing) (PA := PI_prog_B) B ly' S' Hp' W' mem' (e_Lam E) (e_peak E) (e_cnt E)
          (e_fail E) (e_ran E) (e_most E) (e_own E)) /\
       (YAkMemnorm.memnorm rsegs (ms_mem ms) -> YAkMemnorm.memnorm rsegs mem'))
    HS eq_refl HJ).
  - rewrite Usp. lia.
  - lia.
  - lia.
  - change (@STK_ex_ws prh_img_B) with 16. lia.
  - change (@STK_ex_ws prh_img_B) with 16. lia.
  - lia.
  - lia.
  - lia.
  - exact R3c.
  - exact R4c.
  - exact Rra.
  - exact (proj1 b2_ra_ok).
  - exact (proj1 (proj2 b2_ra_ok)).
  - replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E))) with (exv_s1 E) by lia. rewrite Us0. exact HCH.
  - intros HAF HWIN. cbn [ss_pc].
    lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?z) _ _) _) _ =>
      replace (Z_to_bv 64 z) with (w64 (B_prog_sigma AS_ex_ws)) by (unfold w64; f_equal; vm_compute; reflexivity) end.
    refine (exv_ws B ARx SK HYP fx lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ ch1 (e_q E) (e_x0 E) ip2
      (exv_sp E + e_d E - exv_s1 E) (e_x E) (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
      _ _ _ _ _ _ _ _ _ _ _ _ _).
    + split; [exact HAF|]. split; [exact HROD|]. split; [rewrite Usp, Ehi; unfold exv_sp in *; lia|].
      split; [unfold raZ; rewrite Rra; pose proof (proj2 (proj2 b2_ra_ok)) as HRA; pose proof (@alloc_ceiling_value rc);
      lia | exact HFZ].
    + exact R10c.
    + exact Vq1.
    + exact Ve1.
    + lia.
    + rewrite Usp. lia.
    + rewrite Usp. lia.
    + exact HWIN.
    + exact HSRC1.
    + exact HINB1.
    + rewrite <- Hlen0. lia.
    + rewrite <- Hlen0. lia.
    + exact HLED1.
  - intros a Ha. left. exact (HFP1 a Ha). }
(* ---- back at B 0x83ca8: re-seat ---- *)
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HPR
  & ((_ & Vq2 & HHp & HS2 & HAB & HLED2) & HMN2)).
replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E)) + (exv_sp E + e_d E - exv_s1 E)) with (exv_sp E + e_d E)
  in HJ1 by lia.
replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E))) with (exv_s1 E) in HX by lia.
replace (exv_s1 E + (exv_sp E + e_d E - exv_s1 E)) with (exv_sp E + e_d E) in HX by lia.
assert (HPR' : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HPR. exact Hr. }
assert (HR2 : forall r, In r exv_bregs -> r <> 24%bv -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr _. apply HPR'. unfold exv_bregs in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; b2_cs. }
destruct (KCALL fx E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) _ k pos fx [(e_q E, e_q E + 8)] _ ly2 S2 Hp2 W2 regs2 mem2 md2 k1
  HPRE HBs1 HFP1 HJ2 HJ1 HX HR2 (fun r _ => eq_refl) HFZ (exv_room_eq Sc Sc S2 (exv_room_refl Sc) HS2)
  (fun H => HMN2 (HPM H)) HHp HAB HLED2) as (HBs2 & HFRAME).
(* the frame did not move *)
pose proof HBs2 as (regs3 & HB3 & HAG3).
destruct (b2_geom B ARx SK HYP fx E ly2 S2 Hp2 W2 regs3 mem2 md2 (k + k1) pos HPRE HB3)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G12' & G13' & _ & _).
pose proof HB3 as HB30. unfold EXB in HB30. cbv zeta in HB30.
destruct HB30 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R18' & _).
assert (HFA : frame_addr ly2 1 pos = frame_addr lyc 1 pos).
{ assert (Hw : w64 (frame_addr ly2 1 pos) = w64 (frame_addr lyc 1 pos)).
  { rewrite <- R18', <- R18, <- (HAG3 18%bv ltac:(discriminate)), (HPR' 18%bv ltac:(b2_cs)).
    exact (RKc 18%bv ltac:(discriminate) ltac:(b2_in)). }
  apply (f_equal (@bv_unsigned 64)) in Hw. unfold w64 in Hw. rewrite !unsigned_lit_small in Hw by lia. exact Hw. }
(* the position after the whitespace *)
destruct (b2_skip_suffix (skipn (Z.to_nat ip2) (e_x E))) as (kk & Hkk).
rewrite skipn_skipn in Hkk.
pose proof (PSUF (e_x E) _ _ Hkk) as HSUF.
pose proof (length_skipn (kk + Z.to_nat ip2) (e_x E)) as LS1.
pose proof (length_skipn (Z.to_nat ip2) (e_x E)) as LS2.
set (L := length (PjGrammar.skip (skipn (Z.to_nat ip2) (e_x E)))) in *.
assert (HLk : L = (length (e_x E) - (kk + Z.to_nat ip2))%nat) by (unfold L; rewrite Hkk; exact LS1).
assert (HIP : Z.to_nat (exv_len E - Z.of_nat L) = (length (e_x E) - L)%nat) by (rewrite Hlen0; lia).
assert (HSK2 : skipn (Z.to_nat (exv_len E - Z.of_nat L)) (e_x E) = PjGrammar.skip (skipn (Z.to_nat ip2) (e_x E)))
  by (rewrite HIP; exact HSUF).
assert (HLle : (L <= length (e_x E) - Z.to_nat ip2)%nat) by lia.
(* the spills and the cursor cells, kept across the run and the call *)
assert (KK : forall a, exv_s1 E <= a < exv_sp E -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a)
  by (intros a Ha; rewrite (HFRAME a Ha); apply K0; [lia | tauto]).
assert (KQ : forall a, e_q E + 8 <= a < e_q E + 40 -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).
{ intros a Ha. rewrite HX; [apply K0; [lia | tauto] | lia |].
  intros (r0 & Hr0 & Ha0). destruct Hr0 as [<- | []]. cbn [fst snd] in Ha0. lia. }
apply (HPOST E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos c i cap acc (exv_len E - Z.of_nat L) vv dlc nm u
  Hn HPRE HBs2 Hi1 Hc1 Hc Hdep Hacc).
- split; [|split; [|split; [|split]]].
  + replace (e_x0 E + (exv_len E - Z.of_nat L)) with (e_x0 E + Z.of_nat (length (e_x E)) - Z.of_nat L) by lia.
    exact Vq2.
  + eapply (b2_val_kept2 _ _ memc mem2); [|exact Ve]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KQ. lia.
  + eapply (b2_val_kept2 _ _ memc mem2); [|exact Vdep]. intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply KQ. lia.
  + eapply (b2_val_kept2 _ _ memc mem2); [|exact Vscr]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KQ. lia.
  + eapply (b2_val_kept2 _ _ memc mem2); [|exact Vdl]. intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply KQ. lia.
- rewrite Hlen0. lia.
- exact Hdl.
- rewrite Hlen0. lia.
- rewrite Hlen0. lia.
- rewrite HSK2. exact HV.
- exact Hdif.
- rewrite (HPR' 21%bv ltac:(b2_cs)), (KR 21%bv ltac:(b2_in)). exact H21.
- rewrite (HPR' 27%bv ltac:(b2_cs)), (KR 27%bv ltac:(b2_in)). exact H27.
- rewrite (HPR' 22%bv ltac:(b2_cs)), (KR 22%bv ltac:(b2_in)). exact H22.
- rewrite (HPR' 23%bv ltac:(b2_cs)), (KR 23%bv ltac:(b2_in)). exact H23.
- unfold exv_spills in HSP |- *. rewrite HFA.
  destruct HSP as (S152 & S88 & S56 & S48 & S40 & S80 & S24 & S16 & S72 & S8 & S32 & S136 & S112 & S128 & S64 & S104
    & S96 & S120 & S144).
  repeat match goal with |- _ /\ _ => split end;
    unfold exv_spill in *; (eapply (b2_val_kept2 _ _ memc mem2); [| eassumption]);
    intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply KK; lia.
Qed.
Print Assumptions exvl_B2.
End b2.

About exvl_B2.
Print Assumptions exvl_B2.
