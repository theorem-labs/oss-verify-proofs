(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rests on memnorm through EXV_PRE's last conjunct and EXB's exv_rm keep (old-pin kit 4f18c75d4900); not on
   tex_word_specX. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan), ex_value, segment CL, piece B1 (the item): from the cut LR
   (B 0x83c8c, exv_pc 0x760) through the NESTED ex_value call to the cut LS (B 0x83ca0, exv_pc 0x774) or the exit CX
   (B 0x83fa8, exv_pc 0xa7c). The lemma exvl_B1 is ExvB_Loop.v's Section hypothesis PB1.
   THE CODE (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, the B' writer's listing of the B' pin, rows 474-478):
   `mv a0, s3` (the cursor q), `mv a1, s4` (the kid), `jal ex_value`; then ExvB_Loop_B1_post.v's stretch.
   THE PROOF: one symbolic run of the listing engine from a state seated at LR (registers as atoms, no region) to the
   call; EXBs at the call state by KIT_RUNs (nothing written); the call by YCbqGcallW.v's aj_call_xWF_sp with the
   nested text at n' (STK_ex_value n', window e1 = exv_sp E + e_d E - exv_s1 E, offset o = exv_s1 E - (exv_sp E +
   e_d E), footprint exv_FP E itself), its premises from EXV_PRE, EXBs (KIT_CALL_CHAIN, KIT_RODATA, KIT_WDEST,
   KIT_CHILD) and the cut's own facts; after it EXBs at the callee's float state fx' by KIT_CALLs (its pre-call EXBs
   moved to fx' by ExvB_Loop_kitP.v's exv_exb_fx) and the callee's post, the spills by its keep clause, and the
   continuation ExvB_Loop_B1_post.v's exb1_post_ls (result 0: the item
   (nm, u), PURE_L_STEP / PURE_V_REST / PURE_SUFFIX give LS's grammar premise) or exb1_post_cx (result -1: the
   grammar refuses, exv_V E = None by PURE_L_STEP).
   Old-pin kit 4f18c75d4900 rebind: the run is YC1fPx.v's paj_run_x_inv carrying EXB's memnorm keep (P := exvl_P
   (e_mem E), ExvB_Loop_exw.v) into KIT_RUNs and, with EXV_PRE's memnorm, to the text's memnorm premise at the call
   memory; fpre's `raZ < alloc_ceiling` from the jal's return pc B 0x83c98 (exb1_ra_ceil, YM05.alloc_ceiling_value);
   KIT_CALLs's exv_room Sc S2 is the post's room / iface implications and its hull use, its memnorm keep the post's
   fQmn keep composed with the run's.
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 0x760 (DERIVED: B 0x83c8c minus B's ex_value entry, the internal file neutral_dis.py); 304, 288 (LENGTH: ex_value's frame
   pi_frame F_ex_value at prh_img_B and its 32-alignment slack); 8, 160, 40 (LENGTH: a word, the end of the spill area,
   struct ex); 1, 2, 3, 4, 8, 9, 10, 11, 18, 19, 20, 22, 23, 24, 25, 26, 27 (WORD: register numbers); 16, 32 (LENGTH:
   stack alignments); 2 ^ 40, 2 ^ 64, 4096 (LENGTH: code-offset and address bounds); 0, -1 (WORD: the callee's
   results). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_kit ExvB_Loop_Stmt ExvB_Open_kt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_kitP ExvB_Loop_B1_post.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_exw.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the LR seat: the registers as atoms, no region ---- *)
Definition EXB1_PC1 : Z := B_prog_sigma AS_ex_value - B_prog_base + 0x760.
Definition ss_exb1_1 : sstate := mkSS EXB1_PC1 sr_atoms [] None (mkFacts [] [] []).
Section e1. Context {rc : YM05.RunCeil}.
Definition exb1_E1 (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PI_prog_B (Ereg regs []).
(* the return site and the call target, as numbers the engine's code-pointer facts take *)
Lemma exb1_ra_rng : 4096 <= @pa_val _ B_prog_listing PI_prog_B A_TEXT + EXB1_PC2 < 2 ^ 64 /\
  0 <= EXB1_PC2 < 2 ^ 40 /\ EXB1_PC2 mod 2 = 0.
Proof.
let v := eval vm_compute in (@pa_val _ B_prog_listing PI_prog_B A_TEXT) in
  change (@pa_val _ B_prog_listing PI_prog_B A_TEXT) with v.
unfold EXB1_PC2. let v := eval vm_compute in (B_prog_sigma AS_ex_value - B_prog_base) in
  change (B_prog_sigma AS_ex_value - B_prog_base) with v.
lia.
Qed.
(* fpre's return-address bound at the nested call: the return pc is below the ceiling's floor CEIL_MIN *)
Lemma exb1_ra_ceil : @pa_val _ B_prog_listing PI_prog_B A_TEXT + EXB1_PC2 < alloc_ceiling.
Proof.
pose proof alloc_ceiling_value as ((HC & _) & _).
let v := eval vm_compute in (@pa_val _ B_prog_listing PI_prog_B A_TEXT) in
  change (@pa_val _ B_prog_listing PI_prog_B A_TEXT) with v.
unfold EXB1_PC2. let v := eval vm_compute in (B_prog_sigma AS_ex_value - B_prog_base) in
  change (B_prog_sigma AS_ex_value - B_prog_base) with v.
lia.
Qed.
End e1.

Lemma exb1_fr_nil : forall {rc : YM05.RunCeil} E (H : word -> bool) (m m' : word -> option byte),
  frame_of E [] (mrestrict H m) (mrestrict H m') ->
  (forall a, aview rsegs H m' a = aview rsegs H m a) /\ (forall a, apresent H m a -> apresent H m' a).
Proof.
intros rc E H m m' HFr.
assert (HN : forall x, ~ in_wrange E [] x) by (intros x (rg & [] & _)).
split.
- intros a. apply aview_eq_of. apply HFr. apply HN.
- intros a (Hh & b & Hb). split; [exact Hh|]. exists b.
  pose proof (HFr (Z_to_bv 64 a) (HN _)) as E1. unfold mrestrict in E1. rewrite Hh in E1. rewrite E1. exact Hb.
Qed.

Lemma exb1_ap : forall regs regs' : bvmap 5 word, aregs_preserved regs regs' ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' HP r Hr. pose proof (HP _ Hr) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Section s1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Lemma exb1_seat1 : forall (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte),
  st_ok_pi rsegs VAL (exb1_E1 regs) ss_exb1_1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + EXB1_PC1)) mem (seg_rom rsegs)))
  /\ sh_ok rsegs exb1_Bx exb1_SH (exb1_E1 regs) (rdW W mem).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. split.
- unfold ss_exb1_1. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + exact I.
  + split; [exact I | split; exact I].
- unfold sh_ok, exb1_SH. apply Forall_nil.
Qed.
End s1.

(* the item's node, read through a view that agrees everywhere *)
Section kc. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Lemma exb1_child_kept : forall E (W : world rsegs) (m m' : word -> option byte) i kid tk,
  (forall a, aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
  exv_child E W m i kid tk -> exv_child E W m' i kid tk.
Proof.
intros E W m m' i kid tk HK (Hv & Hi & Ht & kids & Hk & Hr & Hkid).
refine (conj Hv (conj Hi (conj Ht (ex_intro _ kids (conj _ (conj Hr Hkid)))))).
exact (exb1_val_kept W W m m' _ 8 kids (fun x _ => HK x) Hk).
Qed.
End kc.

Ltac exb1_neq := let X := fresh "X" in intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X.
Ltac exb1_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?b) =>
  let z := eval vm_compute in (bv_unsigned b) in change (bv_unsigned b) with z end; unfold acallee_saved; lia.
Ltac exb1_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ---- THE PIECE ---- *)
Section m. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis KCALL : forall fx : YK11.FPState, KIT_CALLs (fx := fx) B ARx SK.
Hypothesis KCHAIN : forall fx : YK11.FPState, KIT_CALL_CHAIN (fx := fx) B ARx SK.
Hypothesis KROD : forall fx : YK11.FPState, KIT_RODATA (fx := fx) B ARx SK.
Hypothesis KWD : forall fx : YK11.FPState, KIT_WDEST (fx := fx) B ARx SK.
Hypothesis KCHILD : forall fx : YK11.FPState, KIT_CHILD (fx := fx) B ARx SK.
Hypothesis KRUN : forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK.
Hypothesis KEXB : forall fx : YK11.FPState, KIT_EXB_OF_S (fx := fx) B ARx SK.
Hypothesis PLS : PURE_L_STEP.
Hypothesis PVR : PURE_V_REST.
Hypothesis PSUF : PURE_SUFFIX.

Lemma exvl_B1 : forall n' m, (forall fx : YK11.FPState, tex_value_specX (fx := fx) (PA := PI_prog_B) B ARx SK n') ->
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK (S n')) ->
  (forall fx : YK11.FPState, CUT_LS (fx := fx) B ARx SK (S n') m) ->
  forall fx : YK11.FPState, CUT_LR (fx := fx) B ARx SK (S n') m.
Proof.
intros n' m HR HX HL fx. unfold CUT_LR.
intros E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip ip1 vv dlc kid tk nm. cbv zeta.
intros Hn HPRE HBs Hi1 Hc Hc2 Hdep Hacc Hcur Hip Hip1 Hdl Hii Hm HV Hname Hkid Hdif H20 H27 H22 H23 HSP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof HBs as (regs0 & HB0 & HR0).
pose proof HB0 as HB0'. unfold EXB in HB0'. cbv zeta in HB0'.
destruct HB0' as (HJ & _ & _ & HFZ & _ & _ & (_ & HPM) & _ & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & _).
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (_ & _ & _ & _ & _ & _ & HPq8 & _ & HPq1 & HPq2 & HPwin & _ & _ & HPlen & _ & HPdep & HPdep32 & _ &
  _ & _ & HPdj1 & HPdj2 & _ & _ & HPMN0).
destruct (exb1_geom B ARx SK E lyc Sc Hpc Wc memc mdc k pos HJ HPwin)
  as (Gsp & Gd0 & Gd16 & Gceil & G47 & (Gs1a & Gs1b) & Gs1m & GSTK & GF & Ghi & Gtop).
pose proof (exb1_stk_S n') as HSS. pose proof (exb1_stk_ge n') as HSG.
assert (HSTK : exv_STK E = STK_ex_value n' + 304) by (unfold exv_STK; rewrite Hn; exact HSS).
pose proof exb1_ra_rng as (HRA1 & HRA2 & HRA3).
assert (Hsp64 : 0 <= exv_sp E < 2 ^ 64) by (unfold exv_sp, spZ; apply u64_range).
(* ---- the run to the call: mv a0, s3; mv a1, s4; jal ex_value ---- *)
destruct (exb1_seat1 (fx := fx) Wc regs memc) as [HS SHOK].
remember (exb1_E1 regs) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (HAG : env_agree 32 (Ereg regs []) Ev) by (rewrite HEv; apply exb1_agree).
pose (RUN := paj_run_x_inv (fx := fx) (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B PST ARx LAWS
  (exvl_P (e_mem E)) (exvl_PLAW (e_mem E))).
unfold cfg_at.
replace (w64 (exv_pc 0x760)) with (Z_to_bv 64 (BASE + EXB1_PC1)) by (unfold w64; f_equal; vm_compute; reflexivity).
paj_run_tok_x_inv RUN HS HJ SHOK HPM exb1_Bspan; [unfold ss_exb1_1; cbn [ss_mem]; apply awr_ok_nil |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?md1) _ => remember md1 as MD1 eqn:HMD1 end.
destruct (exb1_fr_nil Ev (w_H Wc) memc (ms_mem ms) HFr) as [FK1 FP1].
assert (RK1 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. exact (regs_kept_of_st_ok rsegs Ev _ (restrict (w_H Wc) ms) regs [] [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 25; 26; 27]%bv
    HS HAG ltac:(vm_compute; reflexivity) r Hr). }
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (1%bv : bv 5) Rra.
assert (A0 : getr (ms_regs ms) 10 = w64 (e_q E)).
{ rewrite Ra0, HEv. unfold exb1_E1. rewrite (exb1_E_reg regs [] 19%bv 19) by reflexivity.
  rewrite (HR0 19%bv) by exb1_neq. exact R19. }
assert (A1 : getr (ms_regs ms) 11 = w64 kid).
{ rewrite Ra1, HEv. unfold exb1_E1. rewrite (exb1_E_reg regs [] 20%bv 20) by reflexivity. exact H20. }
assert (Hsp1 : getr (ms_regs ms) 2 = w64 (exv_s1 E)).
{ rewrite RK1 by exb1_in. rewrite (HR0 2%bv) by exb1_neq. exact R2. }
assert (Hs01 : getr (ms_regs ms) 8 = w64 (exv_sp E)).
{ rewrite RK1 by exb1_in. rewrite (HR0 8%bv) by exb1_neq. exact R8. }
assert (Usp1 : spZ (ms_regs ms) = exv_s1 E).
{ unfold spZ. rewrite Hsp1. unfold w64. apply unsigned_lit_small. lia. }
(* EXBs at the call state *)
assert (HBs1 : EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) MD1 k pos).
{ apply (KRUN fx E lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms) (ms_mem ms) MD1 HPRE HBs HJ).
  - intros a _ _ _ _. apply FK1.
  - exact FP1.
  - exact HPM.
  - intros r Hr Hn24. apply RK1. unfold exv_bregs in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; try exb1_in. exfalso. exact (Hn24 eq_refl). }
pose proof HBs1 as (regs1 & HB1 & HR1).
pose proof HB1 as HB1'. unfold EXB in HB1'. cbv zeta in HB1'.
destruct HB1' as (_ & _ & _ & _ & _ & _ & _ & HLED1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HSRC1 & HTB1 & _ & HSB1 & _ & _).
destruct (KCHAIN fx E lyc Sc Hpc Wc regs1 (ms_mem ms) MD1 k pos (ms_regs ms) HPRE HB1 Hsp1 Hs01) as (ch1 & Hch & Hapart).
(* the kid's tree *)
assert (HCH : exists Dk, kid = 0 \/
  (prhex_tree (PA := PI_prog_B) lyc Sc (e_Lam E) Wc (ms_regs ms) (ms_mem ms) kid tk Dk /\
   Forall (fun ak => 0 < fst ak) Dk /\
   (forall z, PRH_Reader.pj_footR kid Dk z ->
      ~ (e_scr E <= z < e_scr E + exv_len E + 1) /\ ~ (e_q E <= z < e_q E + 40) /\
      ~ (spZ (ms_regs ms) - STK_ex_value n' <= z < spZ (ms_regs ms)) /\ ~ (as_errno B <= z < as_errno B + 4)))).
{ destruct Hkid as [H0 | Hch0]; [exists []; left; exact H0|].
  destruct (KCHILD fx E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) MD1 k pos i kid tk HPRE HBs1
    (exb1_child_kept E Wc memc (ms_mem ms) i kid tk FK1 Hch0)) as (Dk & HT & HFa & HD).
  exists Dk. right. split; [exact (HT (ms_regs ms))|]. split; [exact HFa|].
  intros z Hz. destruct (HD z Hz) as (D1 & D2 & D3 & D4). split; [exact D1|]. split; [exact D2|]. split; [|exact D4].
  intros Hzz. apply D3. rewrite Usp1 in Hzz. unfold exv_sp in *. lia. }
destruct HCH as (Dk & HTREE).
(* the nested text at the call *)
pose proof (HR fx lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) MD1 ch1 (e_q E) kid (e_x0 E) ip1 (e_dep E + 1) dlc (e_scr E)
  (exv_sp E + e_d E - exv_s1 E) (e_x E) tk Dk (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)) as T.
cbv zeta in T.
unfold fpostWFm in T.
lazymatch type of T with context [fpostWF _ _ _ _ _ _ _ _ _ _ _ _ _ ?Q] => pose (KQ := Q) end.
eapply SRr_bind.
{ eapply (aj_call_xWF_sp (SK := SK) rsegs B PST ARx LAWS B_prog_segs_low Wc Ev _ ms
    (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
    [(1, pos)] lyc Sc Hpc MD1 k (STK_ex_value n') (exv_sp E + e_d E - exv_s1 E) (exv_FP E)
    (exv_s1 E - (exv_sp E + e_d E)) (Z_to_bv 64 (BASE + EXB1_PC2)) ch1 KQ HS eq_refl HJ).
  - rewrite Usp1. lia.
  - clear - Gs1m Gsp Gd16. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - clear - Gs1m Gsp Gd16. lia.
  - lia.
  - rewrite RK1 by exb1_in. rewrite (HR0 3%bv) by exb1_neq. exact R3.
  - rewrite RK1 by exb1_in. rewrite (HR0 4%bv) by exb1_neq. exact R4.
  - rewrite Rra. f_equal; vm_compute; reflexivity.
  - apply (ret_ok_codeptr_v (PI := PI_prog_B)); lia.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E))) with (exv_s1 E) by lia.
    replace (s0Z (ms_regs ms)) with (exv_sp E); [exact Hch|].
    unfold s0Z. rewrite Hs01. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - intros HPRE1 HWIN1. refine (T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    + split; [exact HPRE1|]. split; [exact (proj1 (KROD fx E lyc Sc Hpc Wc regs1 (ms_mem ms) MD1 k pos HPRE HB1))|].
      split; [rewrite Usp1, Ghi; lia|].
      assert (Hra1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + EXB1_PC2)) by (rewrite Rra; f_equal; vm_compute; reflexivity).
      split; [unfold raZ; rewrite Hra1, unsigned_lit_small by lia; exact exb1_ra_ceil | exact HFZ].
    + exact (HPM HPMN0).
    + exact HFZ.
    + rewrite Hn in HCNT. exact HCNT.
    + exact A0.
    + exact A1.
    + exact (exb1_cur_kept Wc Wc memc (ms_mem ms) _ _ _ _ _ _ (fun x _ => FK1 x) Hcur).
    + exact HPq8.
    + exact Hapart.
    + rewrite Usp1. unfold exv_sp in *. lia.
    + rewrite Usp1. unfold exv_sp in *. lia.
    + exact HWIN1.
    + exact HSRC1.
    + exact HTB1.
    + exact HPlen.
    + unfold exv_len in *. lia.
    + lia.
    + rewrite Hn in HPdep32. lia.
    + exact Hdl.
    + apply (KWD fx E lyc Sc Hpc Wc regs1 (ms_mem ms) MD1 k pos (ms_regs ms) (STK_ex_value n') HPRE HB1 Hsp1); lia.
    + exact HSB1.
    + exact HPdj1.
    + exact HPdj2.
    + exact HTREE.
    + exact HLED1.
  - intros a Ha. left. exact Ha. }
(* ---- after the call, at the callee's float state fx' ---- *)
cbv beta. intros W2 c2 Hwle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ' & HFK' & HJ2 & HJ1c & HX' & HP' & HQ).
unfold KQ, fQmn in HQ. cbv beta in HQ.
destruct HQ as ((HRM2 & HHU2 & HIF2 & rr & p' & dep' & dl' & H10' & Hcur2 & Hdl2 & HHp2 & HAB2 & HLED2 & HM) & HMN2).
assert (Esp : exv_sp E + e_d E + (exv_s1 E - (exv_sp E + e_d E)) + (exv_sp E + e_d E - exv_s1 E) = exv_sp E + e_d E)
  by lia.
rewrite Esp in HJ1c.
assert (KC : EXBs (fx := fx') B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos /\
  (forall a, exv_s1 E <= a < exv_sp E -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) (ms_mem ms) a)).
{ assert (HBs1' : EXBs (fx := fx') B ARx SK E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) MD1 k pos).
  { exists regs1. split; [|exact HR1].
    exact (exv_exb_fx B ARx SK fx fx' E lyc Sc Hpc Wc regs1 (ms_mem ms) MD1 k pos HB1 HFK' HFZ'). }
  apply (KCALL fx E lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) MD1 k pos fx' (exv_FP E)
    (STK_ex_value n' + (exv_sp E + e_d E - exv_s1 E)) ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE HBs1' (fun a Ha => Ha) HJ2 HJ1c).
  - intros a Ha Hf. apply HX'; [lia | exact Hf].
  - intros r Hr _. apply (exb1_ap _ _ HP'). unfold exv_bregs in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; exb1_cs.
  - exact HFK'.
  - exact HFZ'.
  - exact (conj HRM2 (conj HIF2 HHU2)).
  - intros H0. exact (HMN2 (HPM H0)).
  - exact HHp2.
  - exact HAB2.
  - exact HLED2. }
destruct KC as (HBs2 & HK2).
(* the spills at the return state *)
destruct (exb1_geom B ARx SK E ly2 S2 Hp2 W2 mem2 md2 (k + k1) pos HJ2 HPwin) as (_ & _ & _ & _ & _ & _ & _ & _ & GF2 & _).
  assert (Hfa : frame_addr ly2 1 pos = frame_addr lyc 1 pos) by (unfold frame_addr; rewrite GF2, GF; reflexivity).
  pose proof (exb1_spills_kept E Wc W2 (ms_mem ms) mem2 lyc ly2 pos c vv i (fun x Hx => HK2 x ltac:(unfold exv_sp in *; lia))
    Hfa (exb1_spills_kept E Wc Wc memc (ms_mem ms) lyc lyc pos c vv i (fun x _ => FK1 x) eq_refl HSP)) as HSP2.
  assert (R27 : forall r, In r [22; 23; 27]%bv -> getr regs2 r = getr regs r).
  { intros r Hr. rewrite (exb1_ap _ _ HP').
    - apply RK1. destruct Hr as [<-|[<-|[<-|[]]]]; exb1_in.
    - destruct Hr as [<-|[<-|[<-|[]]]]; exb1_cs. }
  (* the grammar step at the item *)
  assert (HL1 : exv_V E = match exv_name (c =? 123) (skipn (Z.to_nat ip) (e_x E)) with
    | None => None
    | Some (nm0, y1) => match prhex_V (Z.of_nat (S (Z.to_nat (e_dep E)))) y1 with
      | None => None
      | Some (u, r) => match PjGrammar.skip r with
        | c0 :: r1 => if c0 =? 44 then exv_L (S (Z.to_nat (e_dep E))) (c =? 123) (S i) (exv_cap i cap) ((nm0, u) :: acc) r1
          else if c0 =? PjGrammar.closer (c =? 123) then Some (PjGrammar.mk (c =? 123) (rev ((nm0, u) :: acc)), r1)
          else None
        | [] => None end end end).
  { rewrite HV. apply PLS. }
  rewrite Hname in HL1. cbv beta iota in HL1.
  replace (Z.of_nat (S (Z.to_nat (e_dep E)))) with (e_dep E + 1) in HL1 by lia.
  destruct (prhex_V (e_dep E + 1) (skipn (Z.to_nat ip1) (e_x E))) as [[u rest]|] eqn:HVn.
  + (* the item read: result 0, to LS *)
    destruct HM as (Er & Ep & Ed & Edl). subst rr p' dep'.
    destruct (PVR _ _ _ _ HVn) as (Hlt & kk & Hsuf).
    rewrite length_skipn in Hlt.
    assert (Hrest : skipn (Z.to_nat (exv_len E - Z.of_nat (length rest))) (e_x E) = rest).
    { rewrite skipn_skipn in Hsuf. pose proof (PSUF (e_x E) rest (kk + Z.to_nat ip1)%nat Hsuf) as Hs.
      replace (Z.to_nat (exv_len E - Z.of_nat (length rest))) with (length (e_x E) - length rest)%nat
        by (unfold exv_len; lia).
      exact Hs. }
    apply (exb1_post_ls B ARx SK HYP KRUN (fx := fx') (S n') m (HL fx') E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos c i
      cap acc (exv_len E - Z.of_nat (length rest)) vv dl' nm u Hn HPRE HBs2 Hi1 Hc Hc2 Hdep Hacc).
    * exact Hcur2.
    * unfold exv_len in *. lia.
    * exact Hdl2.
    * unfold exv_len in *. lia.
    * unfold exv_len in *. lia.
    * rewrite HL1, Hrest. reflexivity.
    * exact (Hdif u dl' Hdl2 Edl).
    * exact H10'.
    * rewrite R27 by exb1_in. exact H27.
    * rewrite R27 by exb1_in. exact H22.
    * rewrite R27 by exb1_in. exact H23.
    * exact HSP2.
  + (* the grammar refuses: result -1, to CX *)
    destruct HM as (Er & Ep & Ed). subst rr.
    pose proof HSP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S120 & _).
    apply (exb1_post_cx B ARx SK HYP KRUN KEXB (fx := fx') (S n') (HX fx') E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos
      Hn HPRE HBs2).
    * exists p', dep', dl'. split; [exact Hcur2|]. split; [exact Hdl2|]. rewrite HL1.
      split; [reflexivity|]. unfold exv_len. lia.
    * exact H10'.
    * exact S120.
Qed.
End m.

Print Assumptions exvl_B1.
