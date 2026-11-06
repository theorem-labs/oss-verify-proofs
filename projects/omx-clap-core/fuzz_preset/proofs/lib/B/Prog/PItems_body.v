(* Theorem Labs, 2026-10: segment LOOP + KEY of parse_items' image-B walk.
   Blocks: PI_O_LOOP (0x87b70, the grow call of a member), PI_O_BODY (0x87bbc, where both grow calls join and where
   the walk's induction cuts), PI_O_KEY (0x87bc0, the object key: skip_ws, the quote test, parse_string, the store
   into keys[n], skip_ws, the colon test, in->p++) and PI_O_FREE (0x87ec8, the missing-colon free path).
   The pres and the specs are in lib/B/Prog/PItems_pres.v; this file holds only lemmas and the Section
   hypotheses of its neighbours and callees.
   THE FREED BLOCK of PI_O_FREE is parse_string's own, allocated INSIDE this call (pi_free_pre: In (kx, kk) Lamc,
   ~ In (kx, kk) Lam, and kx - cf_head is no block of the entry state S), so no byte of it is in FP = rd_fp q v and
   the journal's block clause does not cover it.
   Numerals: 4 is a LENGTH (one instruction). Every pc is PI_AT PI_O_* at the image-B listing instance. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YC80xf YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres.
(* the segment specs run at the world relation wle' segs RZ_cf (YA0nH; the runner and branch over R, YSRrG) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section body. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
#[local] Notation Lb := B_prog_listing.
#[local] Notation PLb := PL_prog_B.
#[local] Notation PIb := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ Lb PIb).
#[local] Notation VALb := (@pa_val _ Lb PIb).
#[local] Notation PIATb o := (@PI_AT _ Lb PIb o).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib (PI := PIb) B.

(* the epilogue, PItems_entry.v's pi_epi_holds (the top supplies it as EPI : forall d, pi_epi_spec B ARx SK d); the value
   segment is NOT a Section hypothesis: each step takes pi_val_spec at its own d / N, as PItems_top.v consumes it *)
Hypothesis HEPI : forall d, pi_epi_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d.

(* the callee texts (the kit's, lib/A), at this image and at EVERY float state the run can reach *)
Hypothesis TSKW : forall fy : YK11.FPState, tskip_ws_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK.
Hypothesis TGROW : forall (fy : YK11.FPState) CTX0,
  tgrow_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK CTX0.
Hypothesis TPSTR : forall (fy : YK11.FPState) CTX0 CW,
  tparse_string_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK CTX0 CW.
Hypothesis TFREE : forall fy : YK11.FPState, tfuzz_free_specX (fx := fy) (L := Lb) (PA := PIb) B ARx SK.

(* membership in PI_KEPT, as pi_aregs proves it (PItems_defs.v) *)
Ltac pi_kept_in := unfold PI_KEPT; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).

(* ---- the two plumbing lemmas every block of this segment uses: a block that writes no memory leaves the
   reader equal (funext over frame_of with no write window), and a block that writes no register leaves every
   register of PI_KEPT and sp equal, so a pre moves to the new registers ---- *)
Lemma pi_mem_eq : forall (E : env) (m m' : word -> option byte),
  frame_of E [] m m' -> m' = m.
Proof.
  intros E m m' HFr. apply functional_extensionality. intros x. apply HFr.
  intros (r & Hin & _). exact (in_nil Hin).
Qed.

Lemma pi_body_pre_regs : forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k (regs regs' : bvmap 5 word) N CTX0 CW,
  (forall r, In r PI_KEPT -> getr regs' r = getr regs r) -> getr regs' 2 = getr regs 2 ->
  pi_body_pre (fx := fxc) (L := Lb) (PA := PIb) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW ->
  pi_body_pre (fx := fxc) (L := Lb) (PA := PIb) B fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d
    Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs' N CTX0 CW.
Proof.
  intros fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p d Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs regs' N CTX0 CW HK H2 HP.
  assert (KIN : forall r : bv 5, In r PI_KEPT -> getr regs' r = getr regs r) by exact HK.
  assert (K3 : getr regs' (3%bv : bv 5) = getr regs 3) by (apply KIN; pi_kept_in).
  assert (K4 : getr regs' (4%bv : bv 5) = getr regs 4) by (apply KIN; pi_kept_in).
  assert (K8 : getr regs' (8%bv : bv 5) = getr regs 8) by (apply KIN; pi_kept_in).
  assert (K9 : getr regs' (9%bv : bv 5) = getr regs 9) by (apply KIN; pi_kept_in).
  assert (K18 : getr regs' (18%bv : bv 5) = getr regs 18) by (apply KIN; pi_kept_in).
  assert (K19 : getr regs' (19%bv : bv 5) = getr regs 19) by (apply KIN; pi_kept_in).
  assert (K20 : getr regs' (20%bv : bv 5) = getr regs 20) by (apply KIN; pi_kept_in).
  assert (K21 : getr regs' (21%bv : bv 5) = getr regs 21) by (apply KIN; pi_kept_in).
  assert (K22 : getr regs' (22%bv : bv 5) = getr regs 22) by (apply KIN; pi_kept_in).
  assert (K23 : getr regs' (23%bv : bv 5) = getr regs 23) by (apply KIN; pi_kept_in).
  assert (K24 : getr regs' (24%bv : bv 5) = getr regs 24) by (apply KIN; pi_kept_in).
  assert (K25 : getr regs' (25%bv : bv 5) = getr regs 25) by (apply KIN; pi_kept_in).
  assert (K26 : getr regs' (26%bv : bv 5) = getr regs 26) by (apply KIN; pi_kept_in).
  assert (K27 : getr regs' (27%bv : bv 5) = getr regs 27) by (apply KIN; pi_kept_in).
  assert (Ksp : spZ regs' = spZ regs) by (unfold spZ; rewrite H2; reflexivity).
  destruct HP as (HFP & HENT & HMN & HFRM & HREGS & HRB & H21 & Hex).
  split; [exact HFP|]. split; [exact HENT|]. split; [exact HMN|].
  split; [unfold pi_frame in HFRM |- *; rewrite Ksp, K3, K4; exact HFRM|].
  split; [unfold pi_regs in HREGS |- *; rewrite K9, K19, K18, K8, K20, K26, K27, K25, K23; exact HREGS|].
  split; [unfold pi_regs_body in HRB |- *; rewrite Ksp, K22, K24; exact HRB|].
  split; [rewrite K21; exact H21 | exact Hex].
Qed.

(* the array arm of the loop body has no key: jr_name false y is `jret ([], y)` (PjGrammar.v:252), so jrl's body
   after grow IS the value continuation at the empty name *)
Lemma pi_jbind_jret : forall (A Bt : Type) (a : A) (kk : A -> M Bt) ok,
  jbind (jret a) kk ok = kk a ok.
Proof.
  intros A Bt a kk ok. unfold jbind, jret. destruct (kk a ok) as [[r t] o]. reflexivity.
Qed.

Lemma pi_jrb_array : forall f D n cap accr y ok r t ok2,
  pi_val_k f D false n cap accr [] y ok = (r, t, ok2) ->
  pi_jrb f D false n cap accr y ok = (r, t, ok2).
Proof.
  intros f D n cap accr y ok r t ok2 H. unfold pi_jrb.
  replace (jr_name false y) with (jret (([] : list Z), y)) by reflexivity.
  rewrite pi_jbind_jret. exact H.
Qed.

Lemma pi_jrb_array_eq : forall f D n cap accr y ok,
  pi_jrb f D false n cap accr y ok = pi_val_k f D false n cap accr [] y ok.
Proof.
  intros f D n cap accr y ok.
  destruct (pi_val_k f D false n cap accr [] y ok) as [[r t] o2] eqn:Ek.
  apply pi_jrb_array. exact Ek.
Qed.

(* the array arm keeps the kit's free model: jr_name false y is `jret ([], y)` with no event, so pi_jfb past it is
   pi_jfv_k at the empty key block list (PresetReqAt.lf [] = []) *)
Lemma pi_fl_eqV_of_B : forall d x0 ok0 f n cap af y,
  pi_fl_eqB d false x0 ok0 f n cap af y -> pi_fl_eqV d false x0 ok0 f n cap af [] y.
Proof.
  intros d x0 ok0 f n cap af y HB ok1. rewrite (HB ok1).
  exact (pi_jfb_key f (Nat.succ d) false n cap af y ok1 [] y [] ok1 eq_refl).
Qed.

Lemma pi_val_pre_of_body : forall (fxc fx0 : YK11.FPState) ly S Hp W mem md ch CTX regs0 e q v text len tb p d
    Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW,
  pi_body_pre (fx := fxc) (L := Lb) (PA := PIb) B fx0 ly S Hp W mem md ch CTX regs0 e q v false text len tb p d
    Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW ->
  pi_val_pre (fx := fxc) (L := Lb) (PA := PIb) B fx0 ly S Hp W mem md ch CTX regs0 e q v false text len tb p d
    Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc mdc k regs N CTX0 CW.
Proof.
  intros fxc fx0 ly S Hp W mem md ch CTX regs0 e q v text len tb p d Lam peak cnt fail ran most own kr
    lyc Sc Hpc Wc memc mdc k regs N CTX0 CW HP.
  destruct HP as (HFP & HENT & HMN & HFRM & HREGS & HRB & H21 & Hex).
  destruct Hex as (f & n & cap & acc & kids & keys & Di & pc & ok0 & tr0 & D0 & Lamc & peakc & cntc & failc & ranc
    & HCUR & HN & HNC & HCONT & HDEP & HAP & HPERM & HF & HRUN & HLED & HBLK & HPOSB & HLIVE & HBB & HOK & HLS
    & HROOM & HGR & HCAP & HNCP & af & HFO & HFLB).
  split; [exact HFP|]. split; [exact HENT|]. split; [exact HMN|]. split; [exact HFRM|].
  split; [exact HREGS|]. split; [exact HRB|]. split; [exact H21|].
  exists f, n, cap, acc, kids, keys, Di, [], [], pc, ok0, tr0, D0, Lamc, peakc, cntc, failc, ranc.
  split; [exact HCUR|]. split; [exact HN|]. split; [exact HNC|]. split; [exact HCONT|].
  split; [exact HDEP|]. split; [exact HAP|].
  split; [cbn; split; reflexivity|].
  split; [rewrite app_nil_r; exact HPERM|].
  split; [exact HF|].
  split.
  { unfold pi_val_eq. intros ok1 r t ok2 Hk. apply HRUN. apply pi_jrb_array. exact Hk. }
  split; [exact HLED|]. split; [exact HBLK|]. split; [exact HPOSB|]. split; [exact HLIVE|].
  split; [exact HBB|]. split; [exact HOK|]. split; [exact HLS|].
  split; [rewrite pi_jrb_array_eq in HROOM; exact HROOM|].
  split; [exact HGR|]. split; [exact HCAP|]. split; [exact HNCP|].
  (* the batch-kit free model past the empty array key: af kept, lk = [] (the key block list Dk = []) *)
  exists af, []. split; [exact HFO|]. split; [intros _; reflexivity|].
  exact (pi_fl_eqV_of_B d (rest_atR tb text p) ok0 f n cap af (rest_atR tb text pc) HFLB).
Qed.

(* ---- PI_O_BODY (0x87bbc): `beqz s2, PI_O_VAL` - the array arm (s2 = 0) goes to segment VALUE, the object arm
   falls through to PI_O_KEY. The block writes no register and no memory, so the pre moves across by
   pi_body_pre_regs and pi_mem_eq. No UBSan check is in this block. ---- *)
Theorem pi_body_holds : forall d CTX0 CW N,
  pi_key_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N ->
  pi_val_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N ->
  pi_body_spec (L := Lb) (PA := PIb) (PL := PLb) B ARx SK d CTX0 CW N.
Proof.
  intros d CTX0 CW N HKEY HVALd fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran
    most own kr lyc Sc Hpc Wc memc mdc k regs WS0 HJw HWS HPRE.
  (* THE BUDGETED JOURNAL at the walk's relation wle' segs RZ_cf: the run takes the empty-budget
     journal (rebased at the block's depot); HWD is the wild part's cover the step back needs
     (YCbqGwild.ajournal_xw_unbase0R) *)
  unfold pi_ajR in HJw.
  pose proof (ajxR_wild HJw) as HWD.
  pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
  pose proof HPRE as HP0.
  destruct HP0 as (HFP & HENT & HMN & HFRM & HREGS & HRB & H21 & Hex).
  unfold pi_goalR, cfg_at.
  remember (Eimg (PI := PIb) (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VALb A_LIM E) by (subst E; apply Eimg_env).
  assert (HS : st_ok_pi (fx := fxc) SEGS VALb E
    (mkSS (PIATb PI_O_BODY) sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H Wc) (@YK11.mkst fxc regs
       (Z_to_bv 64 (VALb A_TEXT + PIATb PI_O_BODY)) memc (seg_rom SEGS)))).
  { rewrite (restrict_mkst_fx (fx := fxc)).
    apply (pa_entry_st_ok_full (fx := fxc) (L := Lb) (PI := PIb)
             E (PIATb PI_O_BODY) sr_atoms regs [] (mkFacts [] [] [])
             (mrestrict (w_H Wc) memc)).
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - cbn; exact I.
    - repeat split; exact I. }
  assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
  pose (RUNTO := PI_RUNTOR (fx := fxc) (SK := SK) (L := Lb) (PL := PLb) (PI := PIb) B prh_pst ARx LAWS).
  pose (BR := paj_branchR (fx := fxc) (L := Lb) (PI := PIb) (wle' SEGS YGcfRehidePost.RZ_cf)).
  assert (E18 : ew E 18%nat = Z_to_bv 64 (if o then 1 else 0)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs [] 18 (18%bv : bv 5) eq_refl).
    exact (proj1 (proj2 (proj2 HREGS))). }
  assert (Hob : 0 <= (if o then 1 else 0) < 2 ^ 64) by (destruct o; lia).
  psrr_branch_tok RUNTO BR HS SHOK BAND_SPAN.
  2: { (* s2 <> 0: the object, fall through to PI_O_KEY *)
    rewrite branch_eq_U, U_SLit, (U_atom E 18 (if o then 1 else 0) E18) in Hc by lia.
    apply Z.eqb_neq in Hc.
    assert (Ho : o = true).
    { destruct o; [reflexivity | exfalso; apply Hc; reflexivity]. }
    subst o.
    pi_run_to RUNTO HS HJ SHOK (PIATb PI_O_KEY).
    { apply awr_ok_nil. }
    assert (HM : ms_mem ms = memc).
    { apply (pi_mem_eq E memc (ms_mem ms)). cbn [ss_mem add_cond] in HF. exact HF. }
    assert (HAE : env_agree 32 (Ereg regs []) E)
      by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (HKr : forall r, In r PI_KEPT -> getr (ms_regs ms) r = getr regs r)
      by (intros r Hr; exact (regs_kept_of_st_ok_pi E _ _ regs [] PI_KEPT HS HAE
            ltac:(vm_compute; reflexivity) r Hr)).
    prreg HS (2%bv : bv 5) R2.
    assert (E2 : ew E 2%nat = getr regs 2).
    { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
      exact (ew_Ereg_nat regs [] 2 (2%bv : bv 5) eq_refl). }
    pmkst HS.
    pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) as HJb.
    rewrite HM.
    eapply (HKEY fxc fx0 ly S Hp W mem md ch CTX regs0 e q v true text len tb p Lam peak cnt fail ran most own kr).
    + rewrite <- HM. exact HJb.
    + exact HWS.
    + split; [reflexivity|].
      apply (pi_body_pre_regs fxc fx0 ly S Hp W mem md ch CTX regs0 e q v true text len tb p d
               Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc _ k regs (ms_regs ms) N CTX0 CW HKr).
      * rewrite R2, E2. reflexivity.
      * exact HPRE. }
  (* s2 = 0: the array, to PI_O_VAL *)
  rewrite branch_eq_U, U_SLit, (U_atom E 18 (if o then 1 else 0) E18) in Hc by lia.
  apply Z.eqb_eq in Hc.
  assert (Ho : o = false).
  { destruct o; [exfalso; revert Hc; cbv iota; intros Hc'; discriminate Hc' | reflexivity]. }
  subst o.
  pi_run_to RUNTO HS HJ SHOK (PIATb PI_O_VAL).
  { apply awr_ok_nil. }
  assert (HM : ms_mem ms = memc).
  { apply (pi_mem_eq E memc (ms_mem ms)). cbn [ss_mem add_cond] in HF. exact HF. }
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HKr : forall r, In r PI_KEPT -> getr (ms_regs ms) r = getr regs r)
    by (intros r Hr; exact (regs_kept_of_st_ok_pi E _ _ regs [] PI_KEPT HS HAE
          ltac:(vm_compute; reflexivity) r Hr)).
  prreg HS (2%bv : bv 5) R2.
  assert (E2 : ew E 2%nat = getr regs 2).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    exact (ew_Ereg_nat regs [] 2 (2%bv : bv 5) eq_refl). }
  pmkst HS.
  pose proof (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD) as HJb.
  rewrite HM.
  eapply (HVALd fxc fx0 ly S Hp W mem md ch CTX regs0 e q v false text len tb p Lam peak cnt fail ran most own kr).
  + rewrite <- HM. exact HJb.
  + exact HWS.
  + apply pi_val_pre_of_body.
    apply (pi_body_pre_regs fxc fx0 ly S Hp W mem md ch CTX regs0 e q v false text len tb p d
             Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc _ k regs (ms_regs ms) N CTX0 CW HKr).
    * rewrite R2, E2. reflexivity.
    * exact HPRE.
Qed.

End body.
