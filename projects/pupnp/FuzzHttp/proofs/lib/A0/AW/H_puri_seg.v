(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF F_ctypeA H_parse_uric H2Kit AWRng.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_memptr_cmp.
Import ListNotations.
Open Scope Z_scope.

Definition puri_entryA : Z := 0x8c930.
Notation PURI_DEPTH_A := 16384%Z.
Notation ERRNO_A := 0x5e68cc%Z.
Notation HTTPS_A := 0x21ca0%Z.
Notation GOT_GIF_A := 0xaad48%Z.
Notation GIF_A := 0xaea40%Z.
Notation got_sspA := 0xaad68%Z.
Notation ssp_guardA := 0x6069b0%Z.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Variables (U O ulen lo q kq kO : Z) (ustr slack : list byte) (st : fsstate FI).
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= q - PURI_DEPTH_A.
Hypothesis AL16 : q = 16 * kq.
Hypothesis QHI : q < 2^63.
Hypothesis RF0 : RFAKE FI st m0.
Hypothesis FCO : fs_call_ok FI st tp 1.
Hypothesis FE0 : FSENV FI m0.
Hypothesis Q47 : q <= 2^47 - 64.
Hypothesis SHZ : shz m0 (sh lo) (sh q).
Hypothesis SHR : shr m0 (sh lo - sh lo mod 8) (sh q + 8).

Let F := fs_F FI st 3.  Let FL := fs_FL FI st 3.  Let st1 := fs_next FI st 3.  Let SF := sh F.

Notation WP := [(O, O + 216); (ERRNO_A, ERRNO_A + 4)]%Z.
Notation W0 := ((lo, q) :: FSIV WP)%Z.

Notation ushadow w :=
  ([C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
   C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).

Definition minvU (q' : Z) (m : mem) (w : Z) (v16 v24 v32 v40 v48 v56 v64 : word) (wb : list byte) : Prop :=
  (exists k', q' = 32 * k') /\ q + -240 <= q' <= q + -224
  /\ stk asegs m lo q'
  /\ (exists j0 j96, rw_cells asegs m q' [CB 16 j0; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64;
                                         C8 (wz F); C8 (wz F); C8 (wz U); CB 16 j96; C8 (wz F)])
  /\ rw_cells asegs m (F + 32) [CB 256 wb]
  /\ stk asegs m (q' + 120) (q + -104)
  /\ rw_cells asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m F [C8 (wz 0x41b58ab3); C8 (wz 0x20973); C8 (wz 0x8c930); C8 (wz q')]
  /\ (exists j216, rw_cells asegs m (F + 288) [CB 216 j216; C8 (wz FL)])
  /\ rw_cells asegs m SF (ushadow w)
  /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)]
  /\ mem_inv asegs m
  /\ munch W0 m0 m /\ wmono asegs m0 m
  /\ fkeep FI WP st m0 m /\ asan_env asegs m
  /\ (exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 3 :: fs_live FI st).

Ltac mv_tacU := unfold minvU; split; [eexists; eassumption|]; split; [assumption|];
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eexists; split; eassumption.

Hypothesis OAL : O = 8 * kO.
Hypothesis OLO : 0x609000 <= O.
Hypothesis OHI : O + 216 <= alloc_ceiling.
Hypothesis OLB : lb (fs_live FI st) O 216.
Hypothesis SHWO : shw m0 O 216.
Hypothesis ULEN : Z.of_nat (length ustr) = ulen.
Hypothesis ULR : 0 <= ulen < 2^31.
Hypothesis PAD : (- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack).
Hypothesis UIMG : 0x609000 <= U.
Hypothesis UHI : U + ulen + 1 + Z.of_nat (length slack) <= alloc_ceiling.
Hypothesis UFS : U + ulen + 1 + Z.of_nat (length slack) <= FSB FI \/ FSB FI + A0_FS_SIZE <= U.
Definition UBANDd : Prop := U + ulen + 1 + Z.of_nat (length slack) <= 0x7fff7000 \/ 0x10007fff8000 <= U.
Hypothesis UBAND : UBANDd.
Hypothesis SHWU : shw m0 U (ulen + 1).
Hypothesis SHWHTTPS : shw m0 HTTPS_A 6.
Hypothesis SHWGIF : shw m0 GIF_A 4.
Hypothesis SHWMARK : shw m0 MARKTAB_A 10.
Hypothesis SHWRESV : shw m0 RESVTAB_A 13.
Hypothesis TPV : tp = Z_to_bv 64 6187376.
Variable canary : word.

#[using="U ulen lo ustr slack m0 RF0 OLB ULR"] Lemma geomU : exists kF kB,
  F = 64 * kF /\ SF = 8 * kF + 2147450880 /\ FSB FI = 4096 * kB /\ sh (FSB FI) = 512 * kB + 2147450880
  /\ FSB FI + 36864 <= F /\ F + 512 <= FSB FI + 11571200 /\ FSB FI + 4096 <= FL /\ FL + 1 <= FSB FI + 36864
  /\ (O + 216 <= F \/ F + 512 <= O) /\ FSB FI + 36864 <= O /\ O + 216 <= FSB FI + 11571200
  /\ 6328320 <= FSB FI /\ FSB FI + 11571200 <= alloc_ceiling
  /\ (FSB FI + 11571200 <= 2147446784 \/ 17594333495296 <= FSB FI).
Proof.
  destruct (new_frame_facts FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  cbn [FB_of SB_of] in FHI.
  pose proof (lb_apart_new FI st 3 m0 F SF FL O 216 RF0 ltac:(lia) eq_refl eq_refl eq_refl OLB) as PFAP. cbn [FB_of] in PFAP.
  destruct OLB as (g & Hg & G1 & G2). pose proof (live_wf FI st m0 RF0) as LW. rewrite Forall_forall in LW.
  destruct (LW g Hg) as (KR & GLO & GHI & _). unfold ff_size in *.
  pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
  exists (F / 64), (FSB FI / 4096).
  split; [clear - FAL; Z.div_mod_to_equations; lia|].
  split; [unfold SF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia|].
  split; [clear - FSB4; Z.div_mod_to_equations; lia|].
  split; [unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia|].
  repeat (split; [first [assumption | lia]|]). first [assumption | lia].
Qed.

Notation USTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 SF) x19 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
           x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

#[using="STACK_MALLOC_3 kq ustr slack CLO LO AL16 QHI RF0 FCO FE0 Q47 st1 OHI OLB ULR"] Lemma prologueU : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
  forall (Q : machine_state -> Prop),
  (forall q' m v16 v24 v32 v40 v48 v56 wb x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
     minvU q' m 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb ->
     munch ((lo, q) :: FSIV [])%Z m0 m -> fkeep FI [] st m0 m ->
     evt asegs Q (USTP 0x8cadc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s3 s6 (Z_to_bv 64 (O + 8)) s8 s9 s10 x28 x29 x30 x31 m)) ->
  evt asegs Q
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 U) (Z_to_bv 64 ulen) (Z_to_bv 64 O) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 puri_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AG Q K. unfold puri_entryA.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (new_frame_facts FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _ & _ & _ & _ & _ & APART).
  cbn [FB_of SB_of] in APART.
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  pose proof (munch_refl W0 m0) as MU. pose proof (wmono_refl asegs m0) as WM.
  pose proof (munch_refl ((lo, q) :: FSIV [])%Z m0) as MUP.
  pose proof (munch_refl [(lo, q)]%Z m0) as MU0. pose proof (wmono_refl asegs m0) as WM0.
  pose proof (fkeep_refl FI [] st m0) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
  pose proof RF0 as RF.
  carve_frame 224%nat ST.
  step. do 14 (step; fix_lit_store).
  step.
  step.
  rewrite (unsigned_lit (q + -224)) by lia. rewrite land_align32 by lia.
  remember (q + -224 - (q + -224) mod 32)%Z as q' eqn:Eq0.
  assert (Hq : q' = q + -224 \/ q' = q + -224 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
  assert (Hq32 : exists k', q' = 32 * k') by (exists ((q + -224) / 32); clear - Eq0; Z.div_mod_to_equations; lia).
  assert (QL : q + -240 <= q' <= q + -224) by (clear - Hq; lia).
  clear Eq0.
  lazymatch goal with FRx : rw_cells asegs ?mm (q + -224) (?c0 :: ?c1 :: ?rest) |- _ =>
    destruct (align_frame_gen mm lo (q + -224) q' [c0; c1] rest 120%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
    clear FRx end.
  clear Hq.
  clear ST. rename STq into ST. change (Z.of_nat 120) with 120 in GAP, FRhi. replace (q + -224 + 120) with (q + -104) in GAP, FRhi by lia.
  step.
  step. step.
  step. step. step. step.
  step. step.
  step; fix_lit_store.
  step.   lit_branch.
  step.
  step.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  call (STACK_MALLOC_3 st lo q' 352 F SF FL 512 472%nat 64%nat).
  all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).
  match goal with A : asan_env asegs _ |- _ => try clear AE; rename A into AE end.
  match goal with R : RFAKE FI (fs_next FI st 3) _ |- _ => rename R into RF end.
  match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end. fold st1 in LIVE1, RF.
  match goal with K0 : fkeep FI [] st _ _ |- _ => rename K0 into FKc end.
  match goal with P : rw_cells asegs _ F _ |- _ => rename P into FRF end.
  match goal with P : rw_cells asegs _ SF _ |- _ => rename P into SHF; shadow_cells_lit SHF end.
  match goal with P : rw_cells asegs _ FL _ |- _ => rename P into FLG end.
  fs_after_call FI FK FKc LSUB LIVE1 [(lo, q); (F, F + 512); (SF, SF + 64)]%Z.
  pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
  unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
  change (ff_addr (fs_newff FI st 3)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 3)) with FL in LVL. change (sh F) with SF in LVS.
  step.
  step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
  step; fix_lit_store. step; fix_lit_store.
  do 8 step.
  step; fix_lit_store. step; fix_lit_store.
  step; fix_lit_store.
  step; fix_lit_store.
  step. step.
  replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
    by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; reflexivity).

  hideW MU WM. lazymatch type of MUP with ?T => change (hid2 T) in MUP end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 4 sstep.
  step.
  do 32 sstep.
  step.
  do 8 sstep.
  unhide_transport MUs WMs.
  assert (SUBP : sub_fp [(SF, SF + 64)]%Z ((lo, q) :: FSIV [])%Z).
  { intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia| exact I]. }
  assert (SUB0 : sub_fp [(SF, SF + 64)]%Z W0).
  { intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia| exact I]. }
  unfold hid2 in MUP.
  lazymatch type of MUs with munch _ ?ma ?mf => pose proof (munch_absorb _ _ m0 ma mf MUP MUs SUBP) as MUP' end. clear MUP. rename MUP' into MUP.
  absorbW MU WM MUs WMs SUB0. clear MUs WMs SUBP SUB0.
  step.
  step; fix_lit_store.

  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  splitcb QC 0%nat [16; 8; 8; 8; 8; 8; 8]%nat. recell QC 1%nat. recell QC 2%nat. recell QC 3%nat. recell QC 4%nat. recell QC 5%nat. recell QC 6%nat. name_junk QC.
  splitcb FRF 4%nat [256; 216]%nat. name_junk FRF.
  split_chunk FRF 4%nat FH R1. split_chunk R1 1%nat WBC FT.
  replace (F + 32 + 256) with (F + 288) in FT by lia.
  lazymatch type of FK with fkeep _ _ _ _ ?mm => assert (FKW : fkeep FI WP st m0 mm) by (eapply fkeep_weaken; [exact FK| intros a Ha; exact I| intros g Hg; exact Hg]) end.
  destruct Hq32 as (kq' & Hq32).
  change (Z.of_nat 32) with 32 in WBC.
  eapply K; [mv_tacU| exact MUP| exact FK].
Qed.

#[using="HC FI U ulen lo ustr slack st m0 F FL SF SHWO ULR"] Lemma WP_app : app_ivs WP.
Proof.
  pose proof (shw_win_ok _ _ _ SHWO) as WK. unfold app_ivs.
  apply Forall_cons; [eapply app_iv_of_win_ok; [exact WK| lia| lia]|].
  apply Forall_cons; [apply app_iv_low; lia|]. apply Forall_nil.
Qed.
#[using="U ulen ustr slack st m0 CLO F FL SF SHWO ULR"] Lemma W0_fsw : Forall (fsw_iv FI) W0.
Proof. apply fsw_cons_app; [apply app_iv_stack; exact CLO| apply fsw_FSIV; exact WP_app]. Qed.

#[using="U ulen kq ustr slack st CLO LO AL16 Q47 SHZ SHR F FL SF SHWO ULR"] Lemma shwStk_now : forall m q', munch W0 m0 m -> q + -240 <= q' <= q + -224 -> shw m lo (q' - lo).
Proof.
  intros m q' MU Hq.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (shz_stack_fs FI W0 m0 m lo (sh lo) (sh q) SHZ CLO (stack_lo_ok lo) (sh_hi_ok q ltac:(clear - Q47; lia)) MU W0_fsw) as SHZm.
  pose proof (shr_stack_fs FI W0 m0 m lo _ _ SHR CLO (Z.le_refl _) (sh_hi_ok8 q Q47) MU W0_fsw) as SHRm.
  apply (shw_of_shz_shr m (sh lo) (sh q) (sh lo - sh lo mod 8) (sh q + 8) lo (q' - lo) SHZm SHRm).
  - unfold win_ok. split; [lia|]. right. lia.
  - lia.
  - unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
  - lia.
  - unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.
#[using="U ulen lo ustr slack st m0 F FL SF SHWO ULEN ULR PAD UHI"] Lemma WP_out : forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside WP a.
Proof.
  intros a Ha. apply (app_ivs_outside WP a WP_app).
  pose proof (fsb_ok FI) as FSBOK. destruct FSBOK as (F1 & F2 & F3 & F4 & F5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold shband, SH_LO, SH_HI. unfold sh, SHADOW_OFF in Ha. Z.div_mod_to_equations. lia.
Qed.

#[using="U ulen ustr slack RF0 F FL SF OLB SHWO ULEN ULR PAD UHI"] Lemma shwO_now : forall m X n, munch W0 m0 m -> fkeep FI WP st m0 m -> O <= X -> X + n <= O + 216 -> 0 <= n -> shw m X n.
Proof.
  intros m X n MU FK H1 H2 H3.
  eapply (shw_fkeep FI WP st m0 m X n); [eapply shw_sub; [exact SHWO| lia| lia| lia]| exact FK| exact RF0| eapply lb_sub; [exact OLB| lia| lia]| exact WP_out].
Qed.
#[using="ustr slack st CLO F FL SF SHWO ULR UFS SHWU"] Lemma shwU_now : forall m X n, munch W0 m0 m -> U <= X -> X + n <= U + (ulen + 1) -> 0 <= n -> shw m X n.
Proof.
  intros m X n MU H1 H2 H3.
  apply (shw_frame_fs FI W0 m0 m X n (shw_sub _ _ _ _ _ SHWU H1 H2 H3) MU W0_fsw). clear - UFS H1 H2 H3. lia.
Qed.
#[using="U ulen ustr slack st CLO F FL SF SHWO ULR"] Lemma shwG_now : forall m X n, shw m0 X n -> munch W0 m0 m -> X + n <= 0x609000 -> shw m X n.
Proof.
  intros m X n H MU HX. apply (shw_frame_fs FI W0 m0 m X n H MU W0_fsw). left.
  pose proof (fsb_ok FI) as (B1 & _). lia.
Qed.

#[using="U ulen lo ustr slack m0 RF0 OLB ULR"] Lemma liveU : forall stc, fs_live FI stc = fs_newff FI st 3 :: fs_live FI st ->
  lb (fs_live FI stc) F 512 /\ ls (fs_live FI stc) SF 64 /\ lf (fs_live FI stc) FL /\ lb (fs_live FI stc) O 216
  /\ (forall g, In g (fs_live FI st) -> In g (fs_live FI stc)).
Proof.
  intros stc LIVE1.
  destruct (new_frame_facts FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
  assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
  pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
  unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
  change (ff_addr (fs_newff FI st 3)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 3)) with FL in LVL. change (sh F) with SF in LVS.
  split; [exact LVF|]. split; [exact LVS|]. split; [exact LVL|]. split; [exact (lb_mono _ _ _ _ OLB LSUB)| exact LSUB].
Qed.

#[using="U ulen ustr slack st F FL SF ULR"] Lemma sub_fp_O : forall a b, O <= a -> b <= O + 216 -> sub_fp [(a, b)] W0.
Proof. intros a b H1 H2 xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & _ & H4 & _). split; [lia| exact I]. Qed.

Definition pinvR (m : mem) : Prop :=
  bytes_at asegs m U (ustr ++ Z_to_bv 8 0 :: slack)
  /\ (exists ev, rw_cells asegs m ERRNO_A [C4 ev])
  /\ rw_cells asegs m got_sspA [C8 (wz ssp_guardA)] /\ rw_cells asegs m ssp_guardA [C8 canary]
  /\ rw_cells asegs m GOT_GIF_A [C8 (wz GIF_A)] /\ (exists gv, rw_cells asegs m GIF_A [C4 gv]).
Definition pinvU (m : mem) (junk : list byte) : Prop := rw_cells asegs m O [CB 216 junk] /\ pinvR m.
Ltac pr_tacU := unfold pinvR; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [eassumption| eexists; eassumption].
Ltac pv_tacU := unfold pinvU; split; [eassumption| pr_tacU].

#[using="HC FI U ulen slack ULR UFS"] Lemma sub_fp_cons2 : forall (a b : ivl) (W : list ivl), sub_fp [a] W -> sub_fp [b] W -> sub_fp [a; b] W.
Proof. intros [a1 a2] [b1 b2] W HA HB xo Ho. specialize (HA xo Ho). specialize (HB xo Ho). cbn [outside] in *. tauto. Qed.
#[using="U ulen ustr slack st F FL SF ULR"] Lemma sub_fp_stk : forall a b, lo <= a -> b <= q -> sub_fp [(a, b)] W0.
Proof. intros a b H1 H2 xo Ho. cbn [outside] in *. destruct Ho as (H0 & _). split; [lia| exact I]. Qed.

#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma out_open : forall m junk (off n : nat), rw_cells asegs m O [CB 216 junk] -> (off + n <= 216)%nat ->
  exists ja jb jc, rw_cells asegs m O [CB off ja] /\ rw_cells asegs m (O + Z.of_nat off) [CB n jb]
                   /\ rw_cells asegs m (O + Z.of_nat off + Z.of_nat n) [CB (216 - off - n) jc].
Proof.
  intros m junk off n OUT H.
  apply (rw_cells_split_CB asegs m O [] 216 junk [] [off; n; (216 - off - n)%nat]) in OUT; [| cbn; lia]. cbn [app mk_CB_cells] in OUT.
  lazymatch type of OUT with rw_cells _ _ _ [CB _ ?a; CB _ ?b; CB _ ?c] =>
    exists a, b, c; destruct (proj1 (rw_cells_app asegs m O [CB off a] [CB n b; CB (216 - off - n) c]) OUT) as [O1 O23];
    cbn [cells_size csize Nat.add] in O23; rewrite Nat.add_0_r in O23;
    destruct (proj1 (rw_cells_app asegs m (O + Z.of_nat off) [CB n b] [CB (216 - off - n) c]) O23) as [O2 O3];
    cbn [cells_size csize Nat.add] in O3; rewrite Nat.add_0_r in O3 end.
  split; [exact O1|]. split; [exact O2| exact O3].
Qed.
#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma out_close : forall m (off n : nat) ca cb cc, rw_cells asegs m O ca -> cells_size ca = off ->
  rw_cells asegs m (O + Z.of_nat off) cb -> cells_size cb = n ->
  rw_cells asegs m (O + Z.of_nat off + Z.of_nat n) cc -> cells_size cc = (216 - off - n)%nat -> (off + n <= 216)%nat ->
  exists junk', rw_cells asegs m O [CB 216 junk'].
Proof.
  intros m off n ca cb cc A EA B EB C EC H.
  assert (BC : rw_cells asegs m (O + Z.of_nat off) (cb ++ cc)) by (apply rw_cells_app; rewrite EB; split; assumption).
  assert (ABC : rw_cells asegs m O (ca ++ cb ++ cc)) by (apply rw_cells_app; rewrite EA; split; assumption).
  destruct (rw_cells_forget asegs m O _ ABC) as [j J]. exists j.
  rewrite !cells_size_app, EA, EB, EC in J. replace (off + (n + (216 - off - n)))%nat with 216%nat in J by lia. exact J.
Qed.

#[using="IC CLO LO RF0 Q47 OHI OLB SHWO ULEN ULR PAD UHI UFS"] Lemma memsetO : forall (off n : nat) (ret : Z) q' m w v16 v24 v32 v40 v48 v56 v64 wb junk
    x5 x6 x7 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
  minvU q' m w v16 v24 v32 v40 v48 v56 v64 wb -> pinvU m junk -> (off + n <= 216)%nat -> (0 < n)%nat ->
  ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
  (forall m' junk' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     minvU q' m' w v16 v24 v32 v40 v48 v56 v64 wb -> pinvU m' junk' ->
     evt asegs Q (USTP ret q' (Z_to_bv 64 ret) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x19 x22 x23 x24 x25 x26 y28 y29 y30 y31 m')) ->
  evt asegs Q (USTP 0x56f48 q' (Z_to_bv 64 ret) x5 x6 x7 (Z_to_bv 64 (O + Z.of_nat off)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat n))
                    x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros INV PINV HON HN0 ERET K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (out_open m junk off n OUT HON) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  assert (SHWx : shw m (O + Z.of_nat off) (Z.of_nat n)) by (apply (shwO_now m _ _ MU FK); lia).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  hideW MU WM.
  eapply evt_cut.
  { eapply (ic_memset IC) with (P := O + Z.of_nat off) (c := 0) (n := Z.of_nat n) (lo := lo) (q := q') (junk := jb);
    [ rewrite Nat2Z.id; exact O2 | exact (proj1 SHWx) | exact (proj1 (proj2 SHWx)) | rng_tac | exact AE | exact ST | exact CLO | unfold A0_RT_STACK; lia | lia
    | left; lia | constructor; [left; cbn [fst snd]; lia| constructor] | exact MI | reflexivity | reflexivity | reflexivity | lia | lia ]. }
  intros ms' PO. unfold asan_memset_post2 in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MI' & ST' & AE' & O2').
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear O2 ST AE MI SHWx.
  transport_after_call asegs m m' MUt WMt.
  absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_O (O + Z.of_nat off) (O + Z.of_nat off + Z.of_nat n) ltac:(lia) ltac:(lia)) (sub_fp_stk lo q' ltac:(lia) ltac:(lia))).
  clear MUt WMt.
  rewrite ERET.
  destruct (out_close m' off n _ _ _ O1 ltac:(cbn [cells_size csize Nat.add]; lia) O2' ltac:(cbn [cells_size csize Nat.add]; rewrite Nat2Z.id; lia)
              O3 ltac:(cbn [cells_size csize Nat.add]; lia) HON) as [junk' OUT].
  apply (K m' junk'); [mv_tacU| pv_tacU].
Qed.

#[using="IC CLO LO RF0 Q47 OHI OLB SHWO ULEN ULR PAD UHI UFS"] Lemma memsetOo : forall (off n : nat) (ret : Z) q' m w v16 v24 v32 v40 v48 v56 v64 wb junk
    x5 x6 x7 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
  minvU q' m w v16 v24 v32 v40 v48 v56 v64 wb -> pinvU m junk -> (off + n <= 216)%nat -> (0 < n)%nat ->
  ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
  (forall m' ja jc y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     minvU q' m' w v16 v24 v32 v40 v48 v56 v64 wb -> pinvR m' ->
     rw_cells asegs m' O [CB off ja] -> rw_cells asegs m' (O + Z.of_nat off) [CB n (repeat (Z_to_bv 8 0) n)] ->
     rw_cells asegs m' (O + Z.of_nat off + Z.of_nat n) [CB (216 - off - n) jc] ->
     evt asegs Q (USTP ret q' (Z_to_bv 64 ret) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x19 x22 x23 x24 x25 x26 y28 y29 y30 y31 m')) ->
  evt asegs Q (USTP 0x56f48 q' (Z_to_bv 64 ret) x5 x6 x7 (Z_to_bv 64 (O + Z.of_nat off)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat n))
                    x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros INV PINV HON HN0 ERET K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (out_open m junk off n OUT HON) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  assert (SHWx : shw m (O + Z.of_nat off) (Z.of_nat n)) by (apply (shwO_now m _ _ MU FK); lia).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  hideW MU WM.
  eapply evt_cut.
  { eapply (ic_memset IC) with (P := O + Z.of_nat off) (c := 0) (n := Z.of_nat n) (lo := lo) (q := q') (junk := jb);
    [ rewrite Nat2Z.id; exact O2 | exact (proj1 SHWx) | exact (proj1 (proj2 SHWx)) | rng_tac | exact AE | exact ST | exact CLO | unfold A0_RT_STACK; lia | lia
    | left; lia | constructor; [left; cbn [fst snd]; lia| constructor] | exact MI | reflexivity | reflexivity | reflexivity | lia | lia ]. }
  intros ms' PO. unfold asan_memset_post2 in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MI' & ST' & AE' & O2').
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear O2 ST AE MI SHWx.
  transport_after_call asegs m m' MUt WMt.
  absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_O (O + Z.of_nat off) (O + Z.of_nat off + Z.of_nat n) ltac:(lia) ltac:(lia)) (sub_fp_stk lo q' ltac:(lia) ltac:(lia))).
  clear MUt WMt.
  rewrite ERET.
  rewrite Nat2Z.id in O2'.
  apply (K m' ja jc); [mv_tacU| pr_tacU| exact O1| exact O2'| exact O3].
Qed.

Definition WEU : list ivl := [(lo, q); (F, F + 512); (SF, SF + 64); (FL, FL + 1)]%Z.
Definition rframeU (R : mem -> Prop) : Prop := forall m m', R m -> munch WEU m m' -> wmono asegs m m' -> R m'.
#[using="U ulen ustr slack m0 RF0 OLB ULR"] Lemma sub_fp_WEU : sub_fp WEU W0.
Proof.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  intros xo Ho. unfold WEU. cbn [outside] in *. destruct Ho as (H1 & H2 & H3 & _).
  split; [exact H1|]. split; [clear - H2 GF1 GF2; lia|]. split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia|]. split; [clear - H2 GF4 GF5; lia| exact I].
Qed.

Definition postU (X : Z -> mem -> Prop) : machine_state -> Prop :=
  fun ms' => exists (r : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W0 m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
    /\ fkeep FI WP st m0 m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ X r m'.

#[using="SET_SHADOW_F5 kq ustr slack CLO LO AL16 RF0 Q47 OLB ULEN ULR PAD UHI"] Lemma exitU : forall (r : Z) (X : Z -> mem -> Prop) q' m w v16 v24 v32 v40 v48 v56 v64 wb
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m w v16 v24 v32 v40 v48 v56 v64 wb -> X r m -> rframeU (X r) ->
  evt asegs (postU X) (USTP 0x8cdc4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) (Z_to_bv 64 r) x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV HX RFR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (new_frame_facts FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  clear PFAP PFS1 PFS2. hideW MU WM.
  pose proof (munch_refl WEU m) as MUE. pose proof (wmono_refl asegs m) as WME. unfold WEU in MUE.
  pose proof (munch_refl [(lo, q); (F, F + 512); (SF, SF + 64)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  step. step. step; fix_lit_store.
  step.
  step.   if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
  step. step.
  step.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  eapply evt_cut.
  { eapply (SET_SHADOW_F5 SF 64 lo q'); [exact SHF| reflexivity| lia| clear - ESF EKF GF1 FSB1; lia| clear - ESF EKF GF2 FSB2 ACR; lia| exact AE| exact ST| exact CLO| unfold A0_RT_STACK; lia| lia| exact MI| reflexivity| reflexivity]. }
  intros ms' PO. unfold set_shadow_f5_post in PO.
  destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MI' & SHF' & ST' & AE').
  unfold shadow_cells in SHF'. cbv [repeat map Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in SHF'.
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear SHF ST AE MI.
  transport_after_call asegs m1 m' MUt WMt. clear MUt WMt.
  replace (ret_pc (Z_to_bv 64 576996)) with (Z_to_bv 64 576996) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  sstep.
  env_sync AE' MU0 WM0. fk_sync FI RF MU0 FK LSUB.

  join_chunks WBC FT FRt. join_chunks FH FRt FRF.
  lazymatch type of RF with RFAKE _ ?st2 ?mb2 =>
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (SHF2 : rw_cells asegs mc (sh (ff_addr (fs_newff FI st 3))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 3))))))
      by (change (ff_addr (fs_newff FI st 3)) with F; change (sh F) with SF; unfold ff_shsize; rewrite FCLS; exact SHF');
    destruct (release FI st2 (fs_newff FI st 3) (fs_live FI st) mb2 mc _ RF LIVE1 MU0 WM0 FLG SHF2 FRF
                ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3]
  end end.
  clear RF MU0 WM0 SHF2.
  step.   step.   step.
  do 13 step.
  step.   step.

  release_frame QC ST' (q' + 120)%Z.
  pose proof (stk_merge asegs _ _ _ _ ST' GAP ltac:(lia)) as STm. clear ST' GAP.
  release_frame FRhi STm q.
  absorbW MU WM MUE WME sub_fp_WEU.
  apply evt_done. unfold postU. exists r. do 14 eexists.
  lazymatch goal with |- exists _ _, MS _ _ _ _ _ ?mm _ = _ /\ _ => exists mm, (fs_after_release FI stc) end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FK|]. split; [exact LIVE3|]. split; [exact RF3|].
  split; [exact STm|]. split; [assumption|]. exact (RFR m _ HX MUE WME).
Qed.

#[using="IC kO CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS SHWU SHWMARK SHWRESV"] Lemma puricO : forall (off : nat) (bp ret : Z) q' m w v16 v24 v32 v40 v48 v56 v64 wb junk
    x5 x6 x7 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
  minvU q' m w v16 v24 v32 v40 v48 v56 v64 wb -> pinvU m junk -> (off = 32 \/ off = 48)%nat -> 0 <= bp <= ulen ->
  ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
  (forall m' ja jc (i : Z) y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     minvU q' m' w v16 v24 v32 v40 v48 v56 v64 wb -> pinvR m' -> 0 <= i <= ulen - bp ->
     rw_cells asegs m' O [CB off ja] -> rw_cells asegs m' (O + Z.of_nat off) [C8 (Z_to_bv 64 (U + bp)); C8 (Z_to_bv 64 i)] ->
     rw_cells asegs m' (O + Z.of_nat off + 16) [CB (200 - off) jc] ->
     evt asegs Q (USTP ret q' (Z_to_bv 64 ret) y5 y6 y7 (Z_to_bv 64 i) y11 y12 y13 y14 y15 y16 y17 x19 x22 x23 x24 x25 x26 y28 y29 y30 y31 m')) ->
  evt asegs Q (USTP 0x8d60c q' (Z_to_bv 64 ret) x5 x6 x7 (Z_to_bv 64 (U + bp)) (Z_to_bv 64 (ulen - bp)) (Z_to_bv 64 (O + Z.of_nat off))
                    x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros INV PINV HOFF HBP ERET K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (HON : (off + 16 <= 216)%nat) by lia.
  destruct (out_open m junk off 16 OUT HON) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  splitcb O2 0%nat [8; 8]%nat. recell O2 0%nat. recell O2 1%nat. name_junk O2.
  assert (SHWo : shw m (O + Z.of_nat off) 16) by (apply (shwO_now m _ _ MU FK); lia).
  assert (SHWi : shw m (U + bp) (ulen - bp)) by (apply (shwU_now m _ _ MU); lia).
  assert (SHWM : shw m MARKTAB_A 10) by (apply (shwG_now m _ _ SHWMARK MU); lia).
  assert (SHWR : shw m RESVTAB_A 13) by (apply (shwG_now m _ _ SHWRESV MU); lia).
  pose proof (bytes_at_bound _ _ _ _ TXT) as TB. rewrite length_app in TB. cbn [length] in TB.
  assert (LTX : (Z.to_nat bp <= length (ustr ++ Z_to_bv 8 0 :: slack))%nat) by (rewrite length_app; cbn [length]; lia).
  pose proof TXT as TXTi. rewrite <- (firstn_skipn (Z.to_nat bp) (ustr ++ Z_to_bv 8 0 :: slack)) in TXTi. apply bytes_at_app in TXTi. destruct TXTi as [_ TXTi].
  rewrite firstn_length_le in TXTi by exact LTX. replace (U + Z.of_nat (Z.to_nat bp)) with (U + bp) in TXTi by lia.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  hideW MU WM.
  eapply evt_cut.
  { eapply (parse_uric_spec_A IC (U + bp) (O + Z.of_nat off) (ulen - bp) lo (skipn (Z.to_nat bp) (ustr ++ Z_to_bv 8 0 :: slack)));
    [ exact TXTi | rewrite length_skipn, length_app; cbn [length]; lia | lia | exact O2
    | lia | rewrite length_skipn, length_app; cbn [length]; lia | exact SHWi
    | lia | lia | clear - OAL HOFF; Z.div_mod_to_equations; lia | exact SHWo
    | rewrite length_skipn, length_app; cbn [length]; clear - UFS PFS1 PFS2 HBP HOFF ULEN; lia
    | exact SHWM | exact SHWR | exact AE | exact ST | exact CLO | unfold A0_RT_STACK; lia | lia | exact MI | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO. unfold parse_uric_post_A in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & i & -> & MUc & WMc & MI' & ST' & AE' & O2' & TXTi' & IR).
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear O2 ST AE MI SHWo SHWi SHWM SHWR TXTi TXTi'.
  transport_after_call asegs m m' MUt WMt.
  absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_stk lo q' ltac:(lia) ltac:(lia)) (sub_fp_O (O + Z.of_nat off) (O + Z.of_nat off + 16) ltac:(lia) ltac:(lia))).
  clear MUt WMt.
  rewrite ERET.
  change (Z.of_nat 16) with 16 in O3. replace (216 - off - 16)%nat with (200 - off)%nat in O3 by lia.
  apply (K m' ja jc i); [mv_tacU| pr_tacU| exact IR| exact O1| exact O2'| exact O3].
Qed.

#[using="U ulen ustr slack m0 CLO RF0 OHI OLB ULR"] Lemma WEU_dj_O : forall X n, O <= X -> X + n <= O + 216 -> disjoint_from WEU X n.
Proof.
  intros X n H1 H2. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  unfold WEU. cbn [disjoint_from].
  split; [left; clear - H2 OHI CLO; lia|]. split; [clear - H1 H2 PFAP; lia|].
  split; [clear - H1 H2 ESF EKF GF1 GF2 PFS1 PFS2 FSB1 FSB2 FSB5 ACR; lia|]. split; [right; clear - H1 GF5 PFS1; lia| exact I].
Qed.
#[using="O ustr m0 CLO RF0 OLB ULR UHI UFS UBAND"] Lemma WEU_dj_U : forall X n, U <= X -> X + n <= U + ulen + 1 + Z.of_nat (length slack) -> disjoint_from WEU X n.
Proof.
  intros X n H1 H2. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  unfold WEU. cbn [disjoint_from].
  split; [left; clear - H2 UHI CLO; lia|]. split; [clear - H1 H2 UFS GF1 GF2; lia|].
  split; [clear - H1 H2 UBu ESF EKF GF1 GF2 FSB1 FSB2 ACR; lia|]. split; [clear - H1 H2 UFS GF4 GF5; lia| exact I].
Qed.
#[using="U O ulen ustr slack m0 CLO RF0 OLB ULR"] Lemma WEU_dj_low : forall X n, 0 <= n -> X + n <= 0x609000 -> disjoint_from WEU X n.
Proof.
  intros X n H0 H1. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  unfold WEU. cbn [disjoint_from]. repeat (split; [left; clear - H0 H1 CLO ACR ESF EKF GF1 GF4 FSB1; lia|]). exact I.
Qed.
#[using="O ulen m0 CLO RF0 OLB ULEN ULR UHI UFS UBAND"] Lemma pinvR_rframe : rframeU pinvR.
Proof.
  intros m m' (TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)) MU WM. unfold pinvR.
  split; [apply (bytes_at_transport asegs WEU m m' _ _ TXT MU); apply WEU_dj_U; [lia| rewrite length_app; cbn [length]; lia]|].
  split; [exists ev; apply (rw_cells_transport asegs WEU m m' _ _ ERRC MU WM); apply WEU_dj_low; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WEU m m' _ _ SSPG MU WM); apply WEU_dj_low; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WEU m m' _ _ SSPC MU WM); apply WEU_dj_low; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs WEU m m' _ _ GOTG MU WM); apply WEU_dj_low; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  exists gv. apply (rw_cells_transport asegs WEU m m' _ _ GIFC MU WM); apply WEU_dj_low; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

Definition XU (rv : Z -> Prop) : Z -> mem -> Prop := fun r m' => rv r /\ exists junk', pinvU m' junk'.
#[using="ulen m0 CLO RF0 OHI OLB ULEN ULR UHI UFS UBAND"] Lemma XU_rframe : forall rv r, rframeU (XU rv r).
Proof.
  intros rv r m m' (HR & junk' & OUT & PR) MU WM. split; [exact HR|]. exists junk'. split; [| exact (pinvR_rframe m m' PR MU WM)].
  apply (rw_cells_transport asegs WEU m m' _ _ OUT MU WM). apply WEU_dj_O; cbn [cells_size csize Nat.add]; lia.
Qed.

Notation XOK := (XU (fun r => r = 1)).
#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma tail2U : forall (bp i : Z) q' m w v16 v24 v32 v40 v48 v56 v64 wb junk
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m w v16 v24 v32 v40 v48 v56 v64 wb -> pinvU m junk -> 0 <= bp -> 0 <= i -> bp + i <= ulen ->
  evt asegs (postU XOK)
    (USTP 0x8cd68 q' x1 x5 x6 x7 (Z_to_bv 64 i) x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 bp) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP0 I0 BPI.
  pose proof INV as INV'.
  destruct INV' as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & FK & AE & _).
  pose proof PINV as PINV'. destruct PINV' as (_ & TXT & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (SHWT : shw m U (ulen + 1)) by (apply (shwU_now m _ _ MU); lia).

  assert (NF : forall y1 y10 y11 y12, evt asegs (postU XOK)
            (USTP 0x8cdb0 q' y1 x5 x6 x7 y10 y11 y12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 (bp + i)) x26 x28 x29 x30 x31 m)).
  { intros y1 y10 y11 y12. step. step. step. step.
    apply (memsetO 48 16 0x8cdc0 q' m w v16 v24 v32 v40 v48 v56 v64 wb junk); [exact INV| exact PINV| lia| lia| apply ret_pc_even; [lia| reflexivity]|].
    intros m' junk' y5 y6 y7 z10 z11 z12 z13 z14 z15 z16 z17 y28 y29 y30 y31 INV2 PINV2.
    step.
    apply (exitU 1 XOK q' m' w v16 v24 v32 v40 v48 v56 v64 wb); [exact INV2| split; [reflexivity| exists junk'; exact PINV2]| apply XU_rframe]. }
  step.
  rewrite ?(unsigned_lit bp), ?(unsigned_lit i) by lia.
  step.   if_cases K1; zify_cond K1.
  { apply NF. }
  rewrite ?(unsigned_lit (bp + i)), ?(unsigned_lit ulen) in K1 by lia.
  step. step.
  destruct (nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat (bp + i))) as [b|] eqn:Hb.
  2:{ exfalso. apply nth_error_None in Hb. rewrite length_app in Hb. cbn [length] in Hb. lia. }
  pose proof (u8ro_read asegs m U _ (bp + i) b (Z_to_bv 64 (U + (bp + i))) TXT Hb ltac:(lia) eq_refl) as RD.
  step. step.
  gen2 CONT 0x8cd88 11%nat 12%nat.
  { intros yi yj.
    step.   step.
    step.   if_cases K2; zify_cond K2.
    { apply NF. }
    step.   step. step.
    step.   rewrite ?(unsigned_lit ulen), ?(unsigned_lit (bp + i + 1)) by lia.
    step.   step.
    apply (puricO 48 (bp + i + 1) 0x8cdac q' m w v16 v24 v32 v40 v48 v56 v64 wb junk); [exact INV| exact PINV| right; reflexivity| lia| apply ret_pc_even; [lia| reflexivity]|].
    intros m' ja jc i2 y5 y6 y7 z11 z12 z13 z14 z15 z16 z17 y28 y29 y30 y31 INV2 PR2 I2 O1 O2 O3.
    destruct (out_close m' 48 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'].
    step.   step.
    apply (exitU 1 XOK q' m' w v16 v24 v32 v40 v48 v56 v64 wb); [exact INV2| split; [reflexivity| exists junk'; split; [exact OUT'| exact PR2]]| apply XU_rframe]. }
  chkbN 11 (U + (bp + i)) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma tailU : forall (bp : Z) q' m w v16 v24 v32 v40 v48 v56 v64 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m w v16 v24 v32 v40 v48 v56 v64 wb -> pinvU m junk -> 0 <= bp <= ulen ->
  evt asegs (postU XOK)
    (USTP 0x8cce8 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 bp) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP.
  pose proof INV as INV'.
  destruct INV' as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  step.   rewrite (unsigned_lit bp) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
  step. step.
  step.   rewrite ?(unsigned_lit ulen), ?(unsigned_lit bp) by lia.
  step. step.
  step.
  apply (puricO 32 bp 0x8cd04 q' m w v16 v24 v32 v40 v48 v56 v64 wb junk); [exact INV| exact PINV| left; reflexivity| exact BP| apply ret_pc_even; [lia| reflexivity]|].
  clear INV PINV ST QC. intros m' ja jc i y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV PR IR O1 O2 O3.
  pose proof INV as INV'.
  destruct INV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & FK & AE & _).
  pose proof PR as PR'. destruct PR' as (TXT & _).
  assert (SHWO' : shw m' O 216) by (apply (shwO_now m' _ _ MU FK); lia).
  assert (SHWT : shw m' U (ulen + 1)) by (apply (shwU_now m' _ _ MU); lia).
  change (Z.of_nat 32) with 32 in O2, O3.
  step. step. step.
  chk8N 12 (O + 40) SHWO'. step. lit_branch.
  step.
  step.   if_cases K1; zify_cond K1.
  {
    destruct (out_close m' 32 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'].
    apply (tail2U bp i q' m' w v16 v24 v32 v40 v48 v56 v64 wb junk'); [exact INV| split; [exact OUT'| exact PR]| lia| lia| lia]. }
  rewrite ?(unsigned_lit i) in K1 by lia.
  step. step.
  chk8N 11 (O + 32) SHWO'. step. lit_branch.
  step.
  destruct (nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat bp)) as [b|] eqn:Hb.
  2:{ exfalso. apply nth_error_None in Hb. rewrite length_app in Hb. cbn [length] in Hb. lia. }
  pose proof (u8ro_read asegs m' U _ bp b (Z_to_bv 64 (U + bp)) TXT Hb ltac:(lia) eq_refl) as RD.
  step. step.

  gen2 CONT 0x8cd44 12%nat 13%nat.
  { intros yi yj.
    step.   step.
    step.   if_cases K2; zify_cond K2.
    { destruct (out_close m' 32 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'].
      apply (tail2U bp i q' m' w v16 v24 v32 v40 v48 v56 v64 wb junk'); [exact INV| split; [exact OUT'| exact PR]| lia| lia| lia]. }
    step. step. step.
    chk8N 12 (O + 24) SHWO'. step. lit_branch.

    splitcb O1 0%nat [24; 4; 4]%nat. recell O1 1%nat. name_junk O1.
    destruct INV as ((kq2 & Hq32b) & Hq2 & ST & (j0b & j96b & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI2 & MU2 & WM2 & FK2 & AE2 & (stc & RF & LIVE1)).
    pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
    destruct PR as (TXT2 & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
    pose proof UBAND as UBu. unfold UBANDd in UBu.
    pose proof (munch_refl [(O + 24, O + 28)]%Z m') as MU0. pose proof (wmono_refl asegs m') as WM0.
    hideW MU2 WM2.
    step; fix_lit_store.
    destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
    absorbW MU2 WM2 MU0 WM0 (sub_fp_O (O + 24) (O + 28) ltac:(lia) ltac:(lia)).
    env_sync AE2 MU0 WM0. fs_sync FI RF MU0 WM0 FK2 LSUB.
    clear UBu.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (out_close mm 32 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
      apply (tail2U bp i q' mm w v16 v24 v32 v40 v48 v56 v64 wb junk'); [mv_tacU| split; [exact OUT'| pr_tacU]| lia| lia| lia] end. }
  chkbN 12 (U + bp) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma nohpU : forall (bp : Z) q' m w v16 v24 v32 v40 v48 v56 v64 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m w v16 v24 v32 v40 v48 v56 v64 wb -> pinvU m junk -> 0 <= bp <= ulen ->
  evt asegs (postU XOK)
    (USTP 0x8ccd8 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 bp) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP.
  step. step. step.
  step.
  apply (memsetO 64 152 0x8cce8 q' m w v16 v24 v32 v40 v48 v56 v64 wb junk); [exact INV| exact PINV| lia| lia| apply ret_pc_even; [lia| reflexivity]|].
  intros m' junk' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV2 PINV2.
  apply (tailU bp q' m' w v16 v24 v32 v40 v48 v56 v64 wb junk'); [exact INV2| exact PINV2| exact BP].
Qed.

Notation XALL := (XU (fun r => r = 1 \/ r = -108)).
#[using="Type"] Lemma postU_mono : forall (X Y : Z -> mem -> Prop) ms, (forall r m, X r m -> Y r m) -> postU X ms -> postU Y ms.
Proof.
  intros X Y ms H (r & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & st' & E & P).
  exists r, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', st'. split; [exact E|].
  destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9). repeat (split; [assumption|]). apply H. exact P9.
Qed.
#[using="Type"] Lemma XOK_ALL : forall r m, XOK r m -> XALL r m.
Proof. intros r m (E & J). split; [left; exact E| exact J]. Qed.

#[using="ulen ustr slack CLO RF0 OLB ULR"] Lemma stackcallU : forall q' m m' w v16 v24 v32 v40 v48 v56 v64 wb,
  minvU q' m w v16 v24 v32 v40 v48 v56 v64 wb -> munch [(lo, q')]%Z m m' -> wmono asegs m m' ->
  mem_inv asegs m' -> stk asegs m' lo q' -> asan_env asegs m' ->
  minvU q' m' w v16 v24 v32 v40 v48 v56 v64 wb.
Proof.
  intros until wb. intros INV MUc WMc MI' ST' AE'.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  hideW MU WM.
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear ST AE MI.
  transport_after_call asegs m m' MUt WMt.
  absorbW MU WM MUt WMt (sub_fp_stk lo q' ltac:(lia) ltac:(lia)).
  clear MUt WMt.
  mv_tacU.
Qed.
#[using="CLO"] Lemma stack_dj : forall q' X n, q + -240 <= q' <= q + -224 -> X + n <= alloc_ceiling -> disjoint_from [(lo, q')]%Z X n.
Proof. intros q' X n Hq H. cbn [disjoint_from]. split; [left; clear - H CLO; lia| exact I]. Qed.
#[using="HC FI ulen st CLO F FL SF ULEN ULR UHI"] Lemma pinvR_stack : forall q' m m', q + -240 <= q' <= q + -224 -> pinvR m -> munch [(lo, q')]%Z m m' -> wmono asegs m m' -> pinvR m'.
Proof.
  intros q' m m' Hq (TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)) MU WM. unfold pinvR.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  split; [apply (bytes_at_transport asegs _ m m' _ _ TXT MU); apply (stack_dj q' _ _ Hq); rewrite length_app; cbn [length]; lia|].
  split; [exists ev; apply (rw_cells_transport asegs _ m m' _ _ ERRC MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m m' _ _ SSPG MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m m' _ _ SSPC MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m m' _ _ GOTG MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  exists gv. apply (rw_cells_transport asegs _ m m' _ _ GIFC MU WM); apply (stack_dj q' _ _ Hq); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.
#[using="HC FI U ulen ustr slack st CLO F FL SF OHI ULR"] Lemma out_stack : forall q' m m' junk, q + -240 <= q' <= q + -224 -> rw_cells asegs m O [CB 216 junk] -> munch [(lo, q')]%Z m m' -> wmono asegs m m' ->
  rw_cells asegs m' O [CB 216 junk].
Proof. intros q' m m' junk Hq OUT MU WM. apply (rw_cells_transport asegs _ m m' _ _ OUT MU WM). apply (stack_dj q' _ _ Hq). cbn [cells_size csize Nat.add]. lia. Qed.

#[using="U O ulen lo ustr slack m0 RF0 FL OLB ULR"] Lemma shwW_now : forall m, rw_cells asegs m SF (ushadow 0) -> shw m (F + 32) 256.
Proof.
  intros m SHF.
  destruct geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (FAL : F mod 8 = 0) by (clear - EKF; Z.div_mod_to_equations; lia).
  change (rw_cells asegs m (sh F) (shadow_cells [241; 241; 241; 241;
            0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
            243; 243; 243; 243; 243; 243; 243; 243;
            0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) in SHF.
  assert (S32 : sh (F + 32) = sh F + 4) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (S287 : sh (F + 32 + 256 - 1) = sh F + 35) by (unfold sh; clear - EKF; Z.div_mod_to_equations; lia).
  assert (SM : sh F mod 8 = 0) by (unfold sh, SHADOW_OFF; clear - EKF; Z.div_mod_to_equations; lia).
  split; [| split].
  - apply (accessible_of_chunk m F _ (F + 32) 256 SHF FAL); [lia| cbn [length]; lia|].
    intros i Hi H1 H2. cbn [length] in Hi.
    do 36 (destruct i as [|i]; [first [reflexivity | exfalso; lia]|]). exfalso. lia.
  - apply (sh_readable_of_chunk m F _ (F + 32) 256 SHF).
    + rewrite S32. clear - SM. Z.div_mod_to_equations. lia.
    + rewrite S287. cbn [length]. clear - SM. Z.div_mod_to_equations. lia.
  - unfold win_ok. split; [lia|]. clear - GF1 GF2 FSB1 FSB2 FSB5 ACR. lia.
Qed.

#[using="U ulen ustr slack m0 RF0 FL OLB ULR"] Lemma sub_fp_SF : sub_fp [(SF, SF + 64)]%Z W0.
Proof.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia| exact I].
Qed.

#[using="SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OHI OLB ULEN ULR PAD UHI UFS UBAND"] Lemma failU : forall q' m v16 v24 v32 v40 v48 v56 v64 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 0 v16 v24 v32 v40 v48 v56 v64 wb -> pinvU m junk ->
  evt asegs (postU XALL)
    (USTP 0x8d2e4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  hideW MU WM.
  pose proof (munch_refl [(SF, SF + 64)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  step.
  do 32 sstep.
  unhide_transport MUs WMs.
  absorbW MU WM MUs WMs sub_fp_SF.
  env_sync AE MUs WMs. fs_sync FI RF MUs WMs FK LSUB.
  clear UBu.
  step.   step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (exitU (-108) XALL q' mm 248 v16 v24 v32 v40 v48 v56 v64 wb); [mv_tacU| split; [right; reflexivity| exists junk; pv_tacU]| apply XU_rframe] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma hpendU : forall (bp2 size : Z) q' m v16 v48 v56 v64 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m 0 v16 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v48 v56 v64 wb -> pinvU m junk ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen ->
  evt asegs (postU XALL)
    (USTP 0x8d390 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 size) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP SZ BPS.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (AIV : app_ivs [(O + 64, O + 80)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  destruct (out_open m junk 64 16 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  change (O + Z.of_nat 64) with (O + 64) in O2.
  pose proof (munch_refl [(O + 64, O + 80)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step. step.
  chk8N 11 (O + 72) SHWO'. step. lit_branch.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step. step.
  chk8N 11 (O + 64) SHWO1. step. lit_branch.
  step.
  step; fix_lit_store.
  step.   rewrite (unsigned_lit size) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
  absorbW MU WM MU0 WM0 (sub_fp_O (O + 64) (O + 80) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear SHWO' SHWO1 AIV.

  hideW MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  step.
  do 32 sstep.
  unhide_transport MUs WMs.
  absorbW MU WM MUs WMs sub_fp_SF.
  env_sync AE MUs WMs. fs_sync FI RF MUs WMs FK LSUB.
  clear UBu.
  step.   if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?signed_of_Z by lia. rewrite ?unsigned_lit by lia. lia. }
  step. step.
  step.
  replace (Z_to_bv 64 (size + bp2)) with (Z_to_bv 64 (bp2 + size)) by (f_equal; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (out_close mm 64 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
    eapply evt_mono; [apply (tailU (bp2 + size) q' mm 248 v16 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v48 v56 v64 wb junk'); [mv_tacU| split; [exact OUT'| pr_tacU]| lia]|] end.
  intros ms' H. exact (postU_mono _ _ ms' XOK_ALL H).
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma inetU : forall (bp2 size af srv : Z) (off N : nat) (pre host rest : list byte) q' m v48 v56 v64 wb junk
    x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x19 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v48 v56 v64 wb -> pinvU m junk ->
  wb = pre ++ host ++ Z_to_bv 8 0 :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In (Z_to_bv 8 0) host ->
  ((af = 2 /\ off = 84%nat /\ N = 4%nat) \/ (af = 10 /\ off = 88%nat /\ N = 16%nat)) ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen ->
  evt asegs (postU XALL)
    (USTP 0x8d2d8 q' x1 x5 x6 x7 (Z_to_bv 64 af) x11 (Z_to_bv 64 (O + Z.of_nat off)) x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 size) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL AF BP SZ BPS.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (HON : (off + N <= 216)%nat) by (destruct AF as [(_ & -> & ->)|(_ & -> & ->)]; lia).
  assert (OFR : (84 <= off <= 88)%nat /\ (4 <= N <= 16)%nat) by (destruct AF as [(_ & -> & ->)|(_ & -> & ->)]; lia).
  destruct (out_open m junk off N OUT HON) as (ja & jb & jc & O1 & O2 & O3). clear OUT.

  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  pose proof (bytes_at_bound _ _ _ _ WBB) as WBL.
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  rewrite EWB in WBB. apply bytes_at_app in WBB. destruct WBB as [_ WBB]. rewrite <- ESRV in WBB.
  replace (host ++ Z_to_bv 8 0 :: rest) with ((host ++ [Z_to_bv 8 0]) ++ rest) in WBB by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in WBB. destruct WBB as [HOST _].
  assert (LH : Z.of_nat (length pre) + Z.of_nat (length host) + 1 <= 256).
  { rewrite EWB in LWB. rewrite !length_app in LWB. cbn [length] in LWB. lia. }
  assert (SHWW : shw m (F + 32) 256) by exact (shwW_now m SHF).
  assert (SHWh : shw m srv (Z.of_nat (length host) + 1)) by (apply (shw_sub m (F + 32) 256 _ _ SHWW); lia).
  assert (SHWo : shw m (O + Z.of_nat off) (Z.of_nat N)) by (apply (shwO_now m _ _ MU FK); lia).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (shwStk_now m q' MU Hq) as SHWS.
  hideW MU WM.
  step.
  step.
  eapply evt_cut.
  { eapply (ic_inet_pton IC) with (af := af) (S := srv) (A := O + Z.of_nat off) (str := host) (ojunk := jb) (N := N) (canary := canary) (lo := lo) (q := q');
    [ exact HOST | exact NONUL | exact O2 | destruct AF as [(-> & _ & ->)|(-> & _ & ->)]; [left| right]; split; [reflexivity| lia | reflexivity | reflexivity]
    | exact SSPG | exact SSPC
    | exact (proj1 SHWh) | exact (proj1 (proj2 SHWh)) | exact (proj2 (proj2 SHWh)) | lia
    | exact (proj1 SHWo) | exact (proj1 (proj2 SHWo)) | exact (proj2 (proj2 SHWo))
    | exact AE | exact ST | exact CLO | unfold A0_RT_STACK; lia | lia
    | clear - Hq Q47; lia | exact (proj1 SHWS) | exact (proj1 (proj2 SHWS))
    | lia | lia | lia | lia | clear - ESRV PFAP OFR LH; lia
    | exact MI | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO. unfold inet_pton_post_A in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & r & outs & -> & MUc & WMc & MI' & ST' & AE' & _ & _ & _ & _ & _ & O2' & R01).
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  clear O2 ST AE MI SHWW SHWh SHWo HOST SHWS.
  transport_after_call asegs m m' MUt WMt.
  absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_stk lo q' ltac:(lia) ltac:(lia)) (sub_fp_O (O + Z.of_nat off) (O + Z.of_nat off + Z.of_nat N) ltac:(lia) ltac:(lia))).
  clear MUt WMt.
  replace (ret_pc (Z_to_bv 64 578272)) with (Z_to_bv 64 578272) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  destruct (out_close m' off N _ _ _ O1 ltac:(cbn [cells_size csize Nat.add]; lia) O2' ltac:(cbn [cells_size csize Nat.add]; lia)
              O3 ltac:(cbn [cells_size csize Nat.add]; lia) HON) as [junk' OUT].
  step.   if_cases K0; zify_cond K0.
  - apply (hpendU bp2 size q' m' (Z_to_bv 64 srv) v48 v56 v64 wb junk'); [mv_tacU| pv_tacU| lia| lia| lia].
  - apply (failU q' m' (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v48 v56 v64 wb junk'); [mv_tacU| pv_tacU].
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma fam4U : forall (bp2 size port srv : Z) (pre host rest : list byte) q' m v48 v56 v64 wb junk
    x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x19 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v48 v56 v64 wb -> pinvU m junk ->
  wb = pre ++ host ++ Z_to_bv 8 0 :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In (Z_to_bv 8 0) host ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen -> 0 <= port < 2^64 ->
  evt asegs (postU XALL)
    (USTP 0x8d1f8 q' x1 x5 x6 x7 x10 x11 (Z_to_bv 64 port) (Z_to_bv 64 (O + 80)) x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 size) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL BP SZ BPS PR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (AIV : app_ivs [(O + 80, O + 84)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  destruct (out_open m junk 80 4 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  change (O + Z.of_nat 80) with (O + 80) in O2.
  pose proof (munch_refl [(O + 80, O + 84)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step.
  chk8N 10 (O + 80) SHWO'. step. lit_branch.
  step.
  step; fix_lit_store.
  step. step.
  step.
  assert (H16 : forall x, bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 48))) 48)) < 65536).
  { intros x. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. Z.div_mod_to_equations. lia. }
  eapply evt_cut.
  { eapply (ic_htons IC); [exact (H16 port)| assumption]. }
  intros ms' PO. unfold leaf_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & _ & _ & _).
  replace (ret_pc (Z_to_bv 64 578076)) with (Z_to_bv 64 578076) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step. step.
  chk8N 12 (O + 82) SHWO1. step. lit_branch.
  step; fix_lit_store.
  step. step.
  step.
  absorbW MU WM MU0 WM0 (sub_fp_O (O + 80) (O + 84) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu SHWO' SHWO1 AIV H16.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (out_close mm 80 4 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
    apply (inetU bp2 size 2 srv 84 4 pre host rest q' mm v48 v56 v64 wb junk'); [mv_tacU| pv_tacU| exact EWB| exact ESRV| exact NONUL| left; repeat split| lia| lia| lia] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV"] Lemma fam6U : forall (bp2 size port srv : Z) (pre host rest : list byte) q' m v48 v56 v64 wb junk
    x1 x5 x6 x7 x10 x11 x14 x15 x16 x17 x19 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v48 v56 v64 wb -> pinvU m junk ->
  wb = pre ++ host ++ Z_to_bv 8 0 :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In (Z_to_bv 8 0) host ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen -> 0 <= port < 2^64 ->
  evt asegs (postU XALL)
    (USTP 0x8d260 q' x1 x5 x6 x7 x10 x11 (Z_to_bv 64 port) (Z_to_bv 64 (O + 80)) x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 size) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL BP SZ BPS PR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (AIV : app_ivs [(O + 80, O + 108)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  destruct (out_open m junk 80 28 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  assert (SHWG0 : shw m GIF_A 4) by (apply (shwG_now m _ _ SHWGIF MU); lia).
  change (O + Z.of_nat 80) with (O + 80) in O2.
  pose proof (munch_refl [(O + 80, O + 108)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step.
  chk8N 10 (O + 80) SHWO'. step. lit_branch.
  step.
  step; fix_lit_store.
  step. step.
  step.
  assert (H16 : forall x, bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 x)) 48))) 48)) < 65536).
  { intros x. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. Z.div_mod_to_equations. lia. }
  eapply evt_cut.
  { eapply (ic_htons IC); [exact (H16 port)| assumption]. }
  intros ms' PO. unfold leaf_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & _ & _ & _).
  replace (ret_pc (Z_to_bv 64 578180)) with (Z_to_bv 64 578180) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step. step.
  chk8N 12 (O + 82) SHWO1. step. lit_branch.
  step. step.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SHWO2 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV);
    assert (SHWG : shw mm GIF_A 4) by exact (shw_frame _ m mm GIF_A 4 SHWG0 MU0 AIV) end.
  step. step.
  gen2 CONT 0x8d2b4 10%nat 11%nat.
  { intros yi yj.
    step. step. step.
    chk8N 11 (O + 104) SHWO2. step.   step. lit_branch.
    step; fix_lit_store.
    step. step.
    absorbW MU WM MU0 WM0 (sub_fp_O (O + 80) (O + 108) ltac:(lia) ltac:(lia)).
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    clear UBu SHWO' SHWO1 SHWO2 SHWG SHWG0 AIV H16.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (out_close mm 80 28 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
      apply (inetU bp2 size 10 srv 88 16 pre host rest q' mm v48 v56 v64 wb junk'); [mv_tacU| pv_tacU| exact EWB| exact ESRV| exact NONUL| right; repeat split| lia| lia| lia] end. }
  chkwN 10 715328 4 SHWG kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep. zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV"] Lemma portfamU : forall (bp2 e fam port srv : Z) (pre host rest : list byte) q' m wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x25 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 port) wb ->
  pinvU m junk ->
  wb = pre ++ host ++ Z_to_bv 8 0 :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In (Z_to_bv 8 0) host ->
  0 <= bp2 -> 0 <= e - (F + 32) <= 255 -> bp2 + (e - (F + 32)) <= ulen -> 0 <= port < 2^64 -> 0 <= fam < 2^64 ->
  evt asegs (postU XALL)
    (USTP 0x8d1c0 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 (Z_to_bv 64 fam) x25 (Z_to_bv 64 e) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL BP SZ BPS PR FR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  destruct (out_open m junk 208 2 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  change (O + Z.of_nat 208) with (O + 208) in O2.
  pose proof (munch_refl [(O + 208, O + 210)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step. step.
  chk8N 11 (O + 208) SHWO'. step.   step. lit_branch.
  step.
  step; fix_lit_store.
  step. step.
  step.   rewrite ?(unsigned_lit e), ?(unsigned_lit (F + 32)) by lia.
  absorbW MU WM MU0 WM0 (sub_fp_O (O + 208) (O + 210) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu SHWO'.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (out_close mm 208 2 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
    assert (INV2 : minvU q' mm 0 (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 port) wb) by mv_tacU;
    assert (PINV2 : pinvU mm junk') by pv_tacU end.
  step.   if_cases K1; zify_cond K1.
  { lazymatch type of INV2 with minvU _ ?mm _ _ _ _ _ _ _ _ _ =>
      apply (fam6U bp2 (e - (F + 32)) port srv pre host rest q' mm (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 port) wb junk'); assumption end. }
  step.
  step.   if_cases K2; zify_cond K2.
  { lazymatch type of INV2 with minvU _ ?mm _ _ _ _ _ _ _ _ _ =>
      apply (hpendU bp2 (e - (F + 32)) q' mm (Z_to_bv 64 srv) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 port) wb junk'); assumption end. }
  lazymatch type of INV2 with minvU _ ?mm _ _ _ _ _ _ _ _ _ =>
    apply (fam4U bp2 (e - (F + 32)) port srv pre host rest q' mm (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 port) wb junk'); assumption end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV"] Lemma port6U : forall (bp2 size port srv : Z) (pre host rest : list byte) q' m wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 port) wb ->
  pinvU m junk ->
  wb = pre ++ host ++ Z_to_bv 8 0 :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In (Z_to_bv 8 0) host ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen -> 0 <= port < 2^64 ->
  evt asegs (postU XALL)
    (USTP 0x8d240 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 size) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL BP SZ BPS PR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  destruct (out_open m junk 208 2 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  change (O + Z.of_nat 208) with (O + 208) in O2.
  pose proof (munch_refl [(O + 208, O + 210)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step. step.
  chk8N 11 (O + 208) SHWO'. step. lit_branch.
  step.
  step; fix_lit_store.
  step.
  absorbW MU WM MU0 WM0 (sub_fp_O (O + 208) (O + 210) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu SHWO'.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (out_close mm 208 2 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
    apply (fam6U bp2 size port srv pre host rest q' mm (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 port) wb junk');
      [mv_tacU| pv_tacU| exact EWB| exact ESRV| exact NONUL| lia| lia| lia| lia] end.
Qed.

Notation zbU := (Z_to_bv 8 0).

#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma wb_nthU : forall (wb : list byte) i, length wb = 256%nat -> 0 <= i <= 255 -> exists b, nth_error wb (Z.to_nat i) = Some b.
Proof.
  intros wb i L Hi. destruct (nth_error wb (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma wb_decomp : forall (wb : list byte) (a z : Z), 0 <= a <= z ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j b, a <= j < z -> nth_error wb (Z.to_nat j) = Some b -> bv_unsigned b <> 0) ->
  exists pre s rest, wb = pre ++ s ++ zbU :: rest /\ Z.of_nat (length pre) = a /\ Z.of_nat (length s) = z - a /\ ~ In zbU s.
Proof.
  intros wb a z AZ WZ WNZ.
  destruct (nth_error_split _ _ _ WZ) as (l1 & l2 & E & L1).
  exists (firstn (Z.to_nat a) l1), (skipn (Z.to_nat a) l1), l2.
  split; [rewrite app_assoc, firstn_skipn; exact E|].
  split; [rewrite firstn_length_le by lia; lia|].
  split; [rewrite length_skipn; lia|].
  intros HIn. destruct (In_nth_error _ _ HIn) as [n Hn].
  assert (LN : (n < length (skipn (Z.to_nat a) l1))%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  rewrite length_skipn in LN. rewrite nth_error_skipn in Hn.
  apply (WNZ (a + Z.of_nat n) zbU ltac:(lia)); [| reflexivity].
  rewrite E. rewrite nth_error_app1 by lia. replace (Z.to_nat (a + Z.of_nat n)) with (Z.to_nat a + n)%nat by lia. exact Hn.
Qed.
#[using="Type"] Lemma wb_strU : forall m (wb pre s rest : list byte), bytes_at asegs m (F + 32) wb -> wb = pre ++ s ++ zbU :: rest ->
  bytes_at asegs m (F + 32 + Z.of_nat (length pre)) (s ++ [zbU]).
Proof.
  intros m wb pre s rest WBB E. rewrite E in WBB. apply bytes_at_app in WBB. destruct WBB as [_ WBB].
  replace (s ++ zbU :: rest) with ((s ++ [zbU]) ++ rest) in WBB by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in WBB. exact (proj1 WBB).
Qed.

#[using="U O ulen lo ustr slack m0 RF0 FL OLB ULR"] Lemma wb_sh0 : forall m c (a : word), rw_cells asegs m SF (ushadow 0) -> 0 <= c <= 255 -> a = wa (sh (F + 32 + c)) ->
  ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 0].
Proof.
  intros m c a SHF Hc Ha.
  pose proof (proj1 (shwW_now m SHF)) as ACC.
  destruct geomU as (kF & kB & EKF & _).
  apply (acc_load0 m (F + 32) 256 (F + 32 + c) a ACC); [clear - EKF Hc; Z.div_mod_to_equations; lia | clear - EKF Hc; Z.div_mod_to_equations; lia | exact Ha].
Qed.

Ltac chkW r c SHF HC :=
  let a := reg_val r in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let SHR := fresh "SHR" in
    assert (SHR : ov_read_bytes asegs mm a 1 = Some [Z_to_bv 8 0]) by (apply (wb_sh0 mm c a SHF HC); shadow_addr_tac) end;
  step; clear_shr.

#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma wrap_sub_ltU : forall c a n, 0 <= c < 2^32 -> - 2^32 < a <= 0 -> 0 <= n < 2^32 ->
  Z.land (c + a) 18446744073709551615 < n -> - a <= c < - a + n.
Proof.
  intros c a n Hc Ha Hn H. change 18446744073709551615%Z with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z.lt_ge_cases c (- a)).
  - rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
  - rewrite Z.mod_small in H by lia. lia.
Qed.
#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma wrap_sub_geU : forall c a n, 0 <= c < 2^32 -> - 2^32 < a <= 0 -> 0 <= n < 2^32 ->
  ~ (Z.land (c + a) 18446744073709551615 < n) -> ~ (- a <= c < - a + n).
Proof.
  intros c a n Hc Ha Hn H Hd. apply H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma portnameU : forall (bp2 size port : Z) q' m v16 v48 v56 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m 0 v16 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) v48 v56 (Z_to_bv 64 port) wb ->
  pinvU m junk ->
  0 <= bp2 -> 0 <= size <= 255 -> bp2 + size <= ulen -> 0 <= port < 2^64 ->
  evt asegs (postU XALL)
    (USTP 0x8d370 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 (Z_to_bv 64 size) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP SZ BPS PR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  destruct (out_open m junk 208 2 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
  change (O + Z.of_nat 208) with (O + 208) in O2.
  pose proof (munch_refl [(O + 208, O + 210)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step. step.
  chk8N 11 (O + 208) SHWO'. step.   step. lit_branch.
  step.
  step; fix_lit_store.
  absorbW MU WM MU0 WM0 (sub_fp_O (O + 208) (O + 210) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu SHWO'.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (out_close mm 208 2 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
    apply (hpendU bp2 size q' mm v16 v48 v56 (Z_to_bv 64 port) wb junk'); [mv_tacU| pv_tacU| lia| lia| lia] end.
Qed.

#[using="U ulen ustr slack st F FL SF ULR"] Lemma sub_fp_errno : sub_fp [(ERRNO_A, ERRNO_A + 4)]%Z W0.
Proof. intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & _ & _ & H5 & _). split; [lia| exact I]. Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma portU : forall (bp2 p z fam srv : Z) (pre host rest : list byte) q' m v64 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x26 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) v64 wb ->
  pinvU m junk ->
  wb = pre ++ host ++ zbU :: rest -> srv = F + 32 + Z.of_nat (length pre) -> ~ In zbU host ->
  0 <= bp2 -> 1 <= p <= z -> z <= 255 -> bp2 + z <= ulen -> 0 <= fam < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j b, p <= j < z -> nth_error wb (Z.to_nat j) = Some b -> bv_unsigned b <> 0) ->
  evt asegs (postU XALL)
    (USTP 0x8d148 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (F + 32 + p)) (Z_to_bv 64 F) x23 (Z_to_bv 64 fam) x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV EWB ESRV NONUL BP PZ Z255 BPZ FR WZ WNZ.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold UBANDd in UBu.

  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  destruct (wb_decomp wb p z ltac:(lia) WZ WNZ) as (pre2 & pstr & rest2 & EWB2 & LP2 & LS2 & NN2).
  pose proof (wb_strU m wb pre2 pstr rest2 WBB EWB2) as PSTR. rewrite LP2 in PSTR.
  assert (ETP : bv_unsigned tp - 164 = ERRNO_A) by (rewrite TPV; reflexivity).
  hideW MU WM.
  assert (EXIT : forall (e' : Z) y10 y11 y12 y13, p <= e' <= z ->
    evt asegs (postU XALL)
      (USTP 0x8d18c q' x1 x5 x6 x7 y10 y11 y12 y13 x14 x15 x16 x17 (Z_to_bv 64 (F + 32 + p)) (Z_to_bv 64 F) x23 (Z_to_bv 64 fam) x25 (Z_to_bv 64 (F + 32 + e')) x28 x29 x30 x31 m)).
  { intros e' y10 y11 y12 y13 HE.
    assert (SHWW : shw m (F + 32) 256) by exact (shwW_now m SHF).
    assert (SHWp : shw m (F + 32 + p) (Z.of_nat (length pstr) + 1)) by (apply (shw_sub m (F + 32) 256 _ _ SHWW); lia).
    step. step. step.
    step.
    eapply evt_cut.
    { eapply (ic_strtol0 IC) with (S := F + 32 + p) (str := pstr) (errv := ev) (canary := canary) (lo := lo) (q := q').
      all: [> exact PSTR | rewrite ETP; exact ERRC | exact SSPG | exact SSPC | exact AE
      | exact (proj1 SHWp) | exact (proj1 (proj2 SHWp)) | exact (proj2 (proj2 SHWp)) | lia
      | exact ST | exact CLO | unfold A0_STRTOL_DEPTH; lia | lia
      | rewrite TPV; rewrite unsigned_lit by lia; lia | rewrite TPV; rewrite unsigned_lit by lia; lia
      | rewrite TPV; rewrite unsigned_lit by lia; reflexivity
      | lia | lia | exact MI | reflexivity | reflexivity | reflexivity ]. }
    intros ms' PO. unfold strtol0_post_A in PO. rewrite ETP in PO.
    destruct PO as (y5 & y6 & y7 & z10 & z11 & z12 & z13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & ev' & -> & MUc & WMc & MI' & ST' & AE' & _ & _ & _ & ERRC').
    pose proof MUc as MUt. pose proof WMc as WMt.
    fs_sync FI RF MUc WMc FK LSUB.
    clear ST AE MI SHWW SHWp ERRC WBB.
    transport_after_call asegs m m' MUt WMt.
    absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_stk lo q' ltac:(lia) ltac:(lia)) sub_fp_errno).
    clear MUt WMt.
    replace (ret_pc (Z_to_bv 64 577948)) with (Z_to_bv 64 577948) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    hideW MU WM.
    step. step. step.
    step. if_cases K1.
    { clear K1. unfold hid2 in MU, WM.
      apply (failU q' m' (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) v64 wb junk); [mv_tacU| pv_tacU]. }
    clear K1.
    step. step.
    assert (SHWW : shw m' (F + 32) 256) by exact (shwW_now m' SHF).
    assert (SHWp : shw m' (F + 32 + p) (Z.of_nat (length pstr) + 1)) by (apply (shw_sub m' (F + 32) 256 _ _ SHWW); lia).
    eapply evt_cut.

    { eapply (ic_atoi IC) with (S := F + 32 + p) (str := pstr) (errv := ev') (canary := canary) (lo := lo) (q := q').
      all: [> exact PSTR | exact NN2 | rewrite ETP; exact ERRC' | exact SSPG | exact SSPC | exact AE'
      | exact (proj1 SHWp) | exact (proj1 (proj2 SHWp)) | exact (proj2 (proj2 SHWp)) | lia
      | exact ST' | exact CLO | unfold A0_RT_STACK; lia | lia
      | rewrite TPV; rewrite unsigned_lit by lia; lia | rewrite TPV; rewrite unsigned_lit by lia; lia
      | rewrite TPV; rewrite unsigned_lit by lia; reflexivity
      | lia | lia | exact MI' | reflexivity ]. }
    intros ms' PO. unfold strtol0_post_A in PO. rewrite ETP in PO.
    destruct PO as (t5 & t6 & t7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m2 & ev2 & -> & MUc & WMc & MI2 & ST2 & AE2 & _ & _ & _ & ERRC2).
    pose proof MUc as MUt. pose proof WMc as WMt.
    fs_sync FI RF MUc WMc FK LSUB.
    clear ST' AE' MI' SHWW SHWp PSTR ERRC'.
    transport_after_call asegs m' m2 MUt WMt.
    absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_stk lo q' ltac:(lia) ltac:(lia)) sub_fp_errno).
    clear MUt WMt.
    replace (ret_pc (Z_to_bv 64 577972)) with (Z_to_bv 64 577972) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    hideW MU WM.
    pose proof (munch_refl [(q' + 64, q' + 72)]%Z m2) as MU0. pose proof (wmono_refl asegs m2) as WM0.
    step.
    step.
    step. if_cases K2.
    { clear K2.
      absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 64) (q' + 72) ltac:(lia) ltac:(lia)).
      env_sync AE2 MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (failU q' mm (Z_to_bv 64 srv) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) w10 wb junk); [mv_tacU| pv_tacU] end. }
    clear K2.
    absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 64) (q' + 72) ltac:(lia) ltac:(lia)).
    env_sync AE2 MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    pose proof (bv_unsigned_in_range 64 w10) as PR. unfold bv_modulus in PR.
    rewrite <- (Z_to_bv_lit_self w10) in QC.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (portfamU bp2 (F + 32 + e') fam (bv_unsigned w10) srv pre host rest q' mm wb junk);
        [mv_tacU| pv_tacU| exact EWB| exact ESRV| exact NONUL| lia| lia| lia| lia| lia] end. }
  assert (LOOP : forall (k : nat) (c a0v a2v : Z) y13 y26, z - c < Z.of_nat k -> p <= c <= z -> a0v = F + 32 + c -> a2v = F + 32 + c - 1 ->
    evt asegs (postU XALL)
      (USTP 0x8d154 q' x1 x5 x6 x7 (Z_to_bv 64 a0v) (Z_to_bv 64 10) (Z_to_bv 64 a2v) y13 x14 x15 x16 x17 (Z_to_bv 64 (F + 32 + p)) (Z_to_bv 64 F) x23 (Z_to_bv 64 fam) x25 y26 x28 x29 x30 x31 m)).
  { induction k as [|k IH]; intros c a0v a2v y13 y26 HK HCz -> ->; [lia|].
    destruct (wb_nthU wb c LWB ltac:(lia)) as [b Hb]. pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
    pose proof (u8ro_read asegs m (F + 32) wb c b (Z_to_bv 64 (F + 32 + c - 1 + 1)) WBB Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    assert (HC255 : 0 <= c <= 255) by lia.
    step. step.
    chkW 13 c SHF HC255.
    step. lit_branch.
    step.
    step. step. step. step.
    step. if_cases K0; zify_cond K0.
    - assert (BNZ : bv_unsigned b <> 0).
      { intros E0. rewrite E0 in K0. vm_compute in K0. discriminate K0. }
      assert (c <> z) by (intros ->; rewrite WZ in Hb; injection Hb as <-; apply BNZ; reflexivity).
      eapply (IH (c + 1)); lia.
    - step. replace (Z_to_bv 64 (F + 32 + c - 1 + 1)) with (Z_to_bv 64 (F + 32 + c)) by (f_equal; lia). eapply (EXIT c); lia. }
  step. step. step.
  eapply (LOOP (S (Z.to_nat (z - p))) p); lia.
Qed.

#[using="U ulen ustr slack m0 RF0 FL SF OLB ULR"] Lemma sub_fp_F : forall a b, F <= a -> b <= F + 512 -> sub_fp [(a, b)] W0.
Proof.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & _).
  intros a b H1 H2 xo Ho. cbn [outside] in *. destruct Ho as (_ & H2' & _). split; [lia| exact I].
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v4exitU : forall (bp2 z j ld defport : Z) (bc : byte) q' m v16 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31,
  minvU q' m 0 v16 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 defport) wb ->
  pinvU m junk ->
  0 <= bp2 -> 0 <= j <= z -> z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  nth_error wb (Z.to_nat j) = Some bc ->
  (ld = 0 \/ exists d, ld = F + 32 + d /\ 0 <= d < j) ->
  evt asegs (postU XALL)
    (USTP 0x8d0a4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (F + 32 + j + 1)) (Z_to_bv 64 ld) (zxb bc) (Z_to_bv 64 (F + 32 + j)) (Z_to_bv 64 j) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP JZ Z255 BPZ DP WZ WNZ Hbc LD.
  lazymatch type of LD with ?T => change (hid2 T) in LD end.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  pose proof (bv_unsigned_in_range 8 bc) as BR. unfold bv_modulus in BR. cbn in BR.
  assert (HJ255 : 0 <= j <= 255) by lia.
  pose proof (munch_refl [(F + 32 + j, F + 32 + j + 1)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  destruct (cb_split1 m (F + 32) 256 wb (Z.to_nat j) bc WBC Hbc ltac:(lia)) as [TX1 TX23]. clear WBC.
  rewrite Z2Nat.id in TX23 by lia.
  remember (256 - Z.to_nat j - 1)%nat as nr eqn:Enr.
  step. step.
  chkW 10 j SHF HJ255.
  step. lit_branch.
  step.
  remember (F + 32 + j) as V eqn:EV.
  step; fix_lit_store.
  subst V.
  apply (rw_cells_reshape asegs _ _ _ [CB 1 [zbU]; CB nr (skipn (Z.to_nat j + 1) wb)]) in TX23;
    [| destruct TX23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
  subst nr.
  pose proof (cb_join1 _ (F + 32) 256 wb (Z.to_nat j) zbU TX1 ltac:(rewrite Z2Nat.id by lia; exact TX23) ltac:(lia) LWB) as WBC.
  clear TX1 TX23.
  absorbW MU WM MU0 WM0 (sub_fp_F (F + 32 + j) (F + 32 + j + 1) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  hideW MU WM.

  assert (LW' : length (setb wb (Z.to_nat j) zbU) = 256%nat) by (rewrite setb_length; lia).
  assert (WZj : nth_error (setb wb (Z.to_nat j) zbU) (Z.to_nat j) = Some zbU) by (apply setb_same; lia).
  assert (WOTH : forall i, i <> Z.to_nat j -> nth_error (setb wb (Z.to_nat j) zbU) i = nth_error wb i) by (intros i Hi; apply setb_other; lia).
  set (wb' := setb wb (Z.to_nat j) zbU) in *. clearbody wb'.
  assert (WNZh : forall j' b, 0 <= j' < j -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
  destruct (wb_decomp wb' 0 j ltac:(lia) WZj WNZh) as (pre & host & rest & EWB & LPRE & LHOST & NONUL).
  assert (JLT : bv_unsigned bc <> 0 -> j < z).
  { intros Hc0. destruct (Z.eq_dec j z) as [E|]; [|lia]. exfalso. subst j. rewrite WZ in Hbc. injection Hbc as <-. apply Hc0. reflexivity. }
  assert (WZ' : j < z -> nth_error wb' (Z.to_nat z) = Some zbU) by (intros Hjz; rewrite WOTH by lia; exact WZ).
  assert (WNZ' : forall j' b, j + 1 <= j' < z -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
  clear WNZh WNZ WZ Hbc.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(q' + 16, q' + 24)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  unfold hid2 in LD. destruct LD as [-> | (d & -> & Hd)].
  -
    step.   lit_branch.
    step.
    step.   if_cases K1; zify_cond K1.
    + clear MU0 WM0 K1. unfold hid2 in MU, WM.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (portnameU bp2 j defport q' mm v16 (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) wb' junk); [mv_tacU| pv_tacU| lia| lia| lia| lia] end.
    + rewrite (unsigned_lit (bv_unsigned bc)) in K1 by lia.
      step.   step.
      step; fix_lit_store.
      step.
      absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 16) (q' + 24) ltac:(lia) ltac:(lia)).
      env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
      replace (Z_to_bv 64 (F + 32 + j + 1)) with (Z_to_bv 64 (F + 32 + (j + 1))) by (f_equal; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (portU bp2 (j + 1) z 0 (F + 32) pre host rest q' mm (Z_to_bv 64 defport) wb' junk);
          [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia| apply WZ'; lia| exact WNZ'] end.
  -
    pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
    destruct (wb_nthU wb' (d + 1) LW' ltac:(lia)) as [bd Hbd]. pose proof (bv_unsigned_in_range 8 bd) as BRd. unfold bv_modulus in BRd. cbn in BRd.
    lazymatch type of WBB with bytes_at _ ?mm _ _ =>
      pose proof (u8ro_read asegs mm (F + 32) wb' (d + 1) bd (Z_to_bv 64 (F + 32 + d + 1)) WBB Hbd ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    assert (HD255 : 0 <= d + 1 <= 255) by lia.
    step.   if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    step. step. step.
    chkW 11 (d + 1) SHF HD255.
    step. lit_branch.
    step.
    step. step. step. step.
    lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned (v_sltiu ?x 10) ≪ 1)] =>
      assert (EF : exists fam, 0 <= fam < 2^64 /\ Z_to_bv 64 (bv_unsigned (v_sltiu x 10) ≪ 1) = Z_to_bv 64 fam)
        by (unfold v_sltiu; destruct (bv_unsigned x <? bv_wrap 64 10); [exists 2| exists 0]; (split; [lia| reflexivity])) end.
    destruct EF as (fam & HF & ->).
    step.
    step; fix_lit_store.
    step.
    absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 16) (q' + 24) ltac:(lia) ltac:(lia)).
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    clear RD WBB.
    step.   if_cases K1; zify_cond K1.
    + rewrite (unsigned_lit (bv_unsigned bc)) in K1 by lia.
      replace (Z_to_bv 64 (F + 32 + j + 1)) with (Z_to_bv 64 (F + 32 + (j + 1))) by (f_equal; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (portU bp2 (j + 1) z fam (F + 32) pre host rest q' mm (Z_to_bv 64 defport) wb' junk);
          [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia| apply WZ'; lia| exact WNZ'] end.
    + clear K1. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (portfamU bp2 (F + 32 + j) fam defport (F + 32) pre host rest q' mm wb' junk);
          [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v4loopU : forall (k : nat) (bp2 z j ld defport : Z) (bc : byte) q' m v16 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
  z - j < Z.of_nat k ->
  minvU q' m 0 v16 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 defport) wb ->
  pinvU m junk ->
  0 <= bp2 -> 0 <= j <= z -> z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  nth_error wb (Z.to_nat j) = Some bc ->
  (ld = 0 \/ exists d, ld = F + 32 + d /\ 0 <= d < j) ->
  evt asegs (postU XALL)
    (USTP 0x8d03c q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (F + 32 + j + 1)) (Z_to_bv 64 ld) (zxb bc) (Z_to_bv 64 (F + 32 + j)) (Z_to_bv 64 j) (Z_to_bv 64 47) x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until x31; intros HK INV PINV BP JZ Z255 BPZ DP WZ WNZ Hbc LD; [lia|].
  lazymatch type of LD with ?T => change (hid2 T) in LD end.
  pose proof INV as INV'.
  destruct INV' as (_ & _ & _ & _ & WBC & _ & _ & _ & _ & SHF & _ & MI & _).
  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  clear WBC.
  pose proof (bv_unsigned_in_range 8 bc) as BR. unfold bv_modulus in BR. cbn in BR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & _ & PFS1 & PFS2 & FSB1 & FSB2 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.

  assert (EXIT : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31, evt asegs (postU XALL)
            (USTP 0x8d0a4 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (F + 32 + j + 1)) (Z_to_bv 64 ld) (zxb bc) (Z_to_bv 64 (F + 32 + j)) (Z_to_bv 64 j) (Z_to_bv 64 47) y28 y29 y30 y31 m)).
  { intros. apply (v4exitU bp2 z j ld defport bc q' m v16 wb junk); assumption. }
  step.
  step.   if_cases K1; zify_cond K1.
  { apply EXIT. }
  step.
  step.
  replace (Z.land (bv_unsigned (zxb bc)) 255) with (bv_unsigned bc)
    by (unfold zxb; rewrite unsigned_lit by lia; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  eapply evt_cut.
  { eapply (isalnum_spec_A); [rewrite unsigned_lit by lia; lia| exact MI]. }
  intros ms' PO. unfold ctype_post_A in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & _ & _ & _).
  replace (ret_pc (Z_to_bv 64 577612)) with (Z_to_bv 64 577612) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite (unsigned_lit (bv_unsigned bc)) by lia.
  assert (CONT4c : forall (ld' : Z) z10 z11 z12 z13, bv_unsigned bc <> 0 ->
            hid2 (ld' = 0 \/ exists d, ld' = F + 32 + d /\ 0 <= d < j + 1) ->
            evt asegs (postU XALL)
              (USTP 0x8d068 q' (Z_to_bv 64 577612) y5 y6 y7 z10 z11 z12 z13 y14 y15 y16 y17 (Z_to_bv 64 (F + 32 + j + 1)) (Z_to_bv 64 ld') (zxb bc) (Z_to_bv 64 (F + 32 + j)) (Z_to_bv 64 j) (Z_to_bv 64 47) y28 y29 y30 y31 m)).
  { intros ld' z10 z11 z12 z13 BNZ LD'.
    assert (JLT : j < z). { destruct (Z.eq_dec j z) as [E|]; [|lia]. exfalso. subst j. rewrite WZ in Hbc. injection Hbc as <-. apply BNZ. reflexivity. }
    destruct (wb_nthU wb (j + 1) LWB ltac:(lia)) as [bn Hbn]. pose proof (bv_unsigned_in_range 8 bn) as BRn. unfold bv_modulus in BRn. cbn in BRn.
    pose proof (u8ro_read asegs m (F + 32) wb (j + 1) bn (Z_to_bv 64 (F + 32 + j + 1)) WBB Hbn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    assert (HJ1 : 0 <= j + 1 <= 255) by lia.
    step. step. step.
    chkW 11 (j + 1) SHF HJ1.
    step. lit_branch.
    step.
    step. step. step.
    replace (Z_to_bv 64 (F + 32 + j + 2)) with (Z_to_bv 64 (F + 32 + (j + 1) + 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (F + 32 + j + 1)) with (Z_to_bv 64 (F + 32 + (j + 1))) by (f_equal; lia).
    step.   if_cases K5; zify_cond K5.
    - clear K5. unfold hid2 in LD'. apply (IH bp2 z (j + 1) ld' defport bn q' m v16 wb junk); try assumption; lia.
    - clear K5. step.   unfold hid2 in LD'. apply (v4exitU bp2 z (j + 1) ld' defport bn q' m v16 wb junk); try assumption; lia. }
  assert (CONT40 : forall z10 z11 z12 z13, bv_unsigned bc <> 0 ->
            evt asegs (postU XALL)
              (USTP 0x8d05c q' (Z_to_bv 64 577612) y5 y6 y7 z10 z11 z12 z13 y14 y15 y16 y17 (Z_to_bv 64 (F + 32 + j + 1)) (Z_to_bv 64 ld) (zxb bc) (Z_to_bv 64 (F + 32 + j)) (Z_to_bv 64 j) (Z_to_bv 64 47) y28 y29 y30 y31 m)).
  { intros z10 z11 z12 z13 BNZ.
    step.
    step.   if_cases K4; zify_cond K4.
    - clear K4. apply (CONT4c ld); [exact BNZ|]. unfold hid2 in *. destruct LD as [L0 | (d & L1 & L2)]; [left; exact L0| right; exists d; split; [exact L1| lia]].
    - clear K4. step.
      apply (CONT4c (F + 32 + j)); [exact BNZ|]. unfold hid2. right. exists j. split; [reflexivity| lia]. }
  step. step.
  step.   if_cases K2; zify_cond K2.
  { apply CONT40. intros E0. rewrite E0 in K2. vm_compute in K2. discriminate K2. }
  clear K2.
  step.   if_cases K3; zify_cond K3.
  { apply EXIT. }
  apply CONT40. intros E0. rewrite E0 in K3. discriminate K3.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v4U : forall (bp2 z defport : Z) (b0 : byte) q' m v16 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x25 x26 x28 x29 x30 x31,
  minvU q' m 0 v16 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 defport) wb ->
  pinvU m junk ->
  0 <= bp2 -> 0 <= z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  nth_error wb 0%nat = Some b0 ->
  evt asegs (postU XALL)
    (USTP 0x8d028 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 (zxb b0) (Z_to_bv 64 (F + 32)) x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP Z255 BPZ DP WZ WNZ Hb0.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & _ & PFS1 & PFS2 & FSB1 & FSB2 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (bv_unsigned_in_range 8 b0) as BR. unfold bv_modulus in BR. cbn in BR.
  step. step. step. step.
  step.   if_cases K0; zify_cond K0.
  - clear K0.
    replace (Z_to_bv 64 (F + 33)) with (Z_to_bv 64 (F + 32 + 0 + 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (F + 32)) with (Z_to_bv 64 (F + 32 + 0)) by (f_equal; lia).
    apply (v4exitU bp2 z 0 0 defport b0 q' m v16 wb junk); try assumption; lia.
  - clear K0.
    replace (Z_to_bv 64 (F + 33)) with (Z_to_bv 64 (F + 32 + 0 + 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (F + 32)) with (Z_to_bv 64 (F + 32 + 0)) by (f_equal; lia).
    apply (v4loopU (S (Z.to_nat z)) bp2 z 0 0 defport b0 q' m v16 wb junk); try assumption; lia.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v6brU : forall (bp2 z c a2v defport : Z) q' m wb junk
    x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m 0 (Z_to_bv 64 (F + 33)) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 defport) wb ->
  pinvU m junk ->
  0 <= bp2 -> 1 <= c < z -> z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  a2v = (F + 32 + c) / 8 + 2147450880 ->
  evt asegs (postU XALL)
    (USTP 0x8d0fc q' x1 x5 x6 x7 (Z_to_bv 64 (F + 32 + c)) x11 (Z_to_bv 64 a2v) x13 x14 x15 x16 x17 (Z_to_bv 64 (F + 32 + c + 2)) (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 (c + 1)) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP CZ Z255 BPZ DP WZ WNZ ->.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  destruct (wb_nthU wb c LWB ltac:(lia)) as [bc Hbc].
  assert (HC255 : 0 <= c <= 255) by lia.
  pose proof (munch_refl [(F + 32 + c, F + 32 + c + 1)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  destruct (cb_split1 m (F + 32) 256 wb (Z.to_nat c) bc WBC Hbc ltac:(lia)) as [TX1 TX23]. clear WBC.
  rewrite Z2Nat.id in TX23 by lia.
  remember (256 - Z.to_nat c - 1)%nat as nr eqn:Enr.
  chkW 12 c SHF HC255.
  step. lit_branch.
  remember (F + 32 + c) as V eqn:EV.
  step; fix_lit_store.
  subst V.
  apply (rw_cells_reshape asegs _ _ _ [CB 1 [zbU]; CB nr (skipn (Z.to_nat c + 1) wb)]) in TX23;
    [| destruct TX23 as [[W23 _] _]; cbn in W23 |- *; LiaTuning.ctauto | reflexivity | reflexivity].
  subst nr.
  pose proof (cb_join1 _ (F + 32) 256 wb (Z.to_nat c) zbU TX1 ltac:(rewrite Z2Nat.id by lia; exact TX23) ltac:(lia) LWB) as WBC.
  clear TX1 TX23.
  absorbW MU WM MU0 WM0 (sub_fp_F (F + 32 + c) (F + 32 + c + 1) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  hideW MU WM.

  assert (LW' : length (setb wb (Z.to_nat c) zbU) = 256%nat) by (rewrite setb_length; lia).
  assert (WZc : nth_error (setb wb (Z.to_nat c) zbU) (Z.to_nat c) = Some zbU) by (apply setb_same; lia).
  assert (WOTH : forall i, i <> Z.to_nat c -> nth_error (setb wb (Z.to_nat c) zbU) i = nth_error wb i) by (intros i Hi; apply setb_other; lia).
  set (wb' := setb wb (Z.to_nat c) zbU) in *. clearbody wb'.
  assert (WNZh : forall j' b, 1 <= j' < c -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
  destruct (wb_decomp wb' 1 c ltac:(lia) WZc WNZh) as (pre & host & rest & EWB & LPRE & LHOST & NONUL).
  assert (WZ' : nth_error wb' (Z.to_nat z) = Some zbU) by (rewrite WOTH by lia; exact WZ).
  assert (WNZ' : forall j' b, c + 2 <= j' < z -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
  destruct (wb_nthU wb' (c + 1) LW' ltac:(lia)) as [bn Hbn]. pose proof (bv_unsigned_in_range 8 bn) as BRn. unfold bv_modulus in BRn. cbn in BRn.
  assert (C2Z : bv_unsigned bn <> 0 -> c + 2 <= z).
  { intros Hn0. destruct (Z.eq_dec (c + 1) z) as [E|]; [|lia]. exfalso. rewrite E, WZ' in Hbn. injection Hbn as <-. apply Hn0. reflexivity. }
  clear WNZh WNZ WZ Hbc.
  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  lazymatch type of WBB with bytes_at _ ?mm _ _ =>
    pose proof (u8ro_read asegs mm (F + 32) wb' (c + 1) bn (Z_to_bv 64 (F + 32 + c + 2 + -1)) WBB Hbn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
  assert (HC1 : 0 <= c + 1 <= 255) by lia.
  step. step. step.
  chkW 11 (c + 1) SHF HC1.
  step. lit_branch.
  step.
  step.
  step.   if_cases K1; zify_cond K1.
  - clear K1 RD WBB. unfold hid2 in MU, WM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (port6U bp2 (c + 1) defport (F + 33) pre host rest q' mm wb' junk);
        [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia] end.
  - rewrite (unsigned_lit (bv_unsigned bn)) in K1 by lia.
    clear RD WBB. unfold hid2 in MU, WM.
    step.   step.
    replace (Z_to_bv 64 (F + 32 + c + 2)) with (Z_to_bv 64 (F + 32 + (c + 2))) by (f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (portU bp2 (c + 2) z 10 (F + 33) pre host rest q' mm (Z_to_bv 64 defport) wb' junk);
        [mv_tacU| pv_tacU| exact EWB| lia| exact NONUL| lia| lia| lia| lia| lia| exact WZ'| exact WNZ'] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v6loopU : forall (k : nat) (bp2 z c a2v defport : Z) q' m wb junk
    x1 x5 x6 x7 x13 x14 x15 x16 x17 x23 x24 x26 x28 x29 x30 x31,
  z - c < Z.of_nat k ->
  minvU q' m 0 (Z_to_bv 64 (F + 33)) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 defport) wb ->
  pinvU m junk ->
  0 <= bp2 -> 1 <= c <= z -> z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  a2v = (F + 32 + c) / 8 + 2147450880 ->
  evt asegs (postU XALL)
    (USTP 0x8cff4 q' x1 x5 x6 x7 (Z_to_bv 64 (F + 32 + c)) (Z_to_bv 64 93) (Z_to_bv 64 a2v) x13 x14 x15 x16 x17 (Z_to_bv 64 (F + 32 + c + 2)) (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 (c + 1)) x26 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until x31; intros HK INV PINV BP CZ Z255 BPZ DP WZ WNZ EA2; [lia|].
  pose proof INV as INV'.
  destruct INV' as (_ & _ & _ & _ & WBC & _ & _ & _ & _ & SHF & _).
  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  assert (LWB : length wb = 256%nat) by (destruct WBC as [[W _] _]; cbn in W; tauto).
  clear WBC.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & _ & PFS1 & PFS2 & FSB1 & FSB2 & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct (wb_nthU wb c LWB ltac:(lia)) as [bc Hbc]. pose proof (bv_unsigned_in_range 8 bc) as BR. unfold bv_modulus in BR. cbn in BR.
  pose proof (u8ro_read asegs m (F + 32) wb c bc (Z_to_bv 64 (F + 32 + c + 2 + -2)) WBB Hbc ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  step.
  step.   if_cases K0; zify_cond K0.
  { clear K0. apply (failU q' m (Z_to_bv 64 (F + 33)) (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 defport) wb junk); assumption. }
  rewrite (unsigned_lit (bv_unsigned bc)) in K0 by lia.
  assert (CLT : c < z). { destruct (Z.eq_dec c z) as [E|]; [|lia]. exfalso. subst c. rewrite WZ in Hbc. injection Hbc as <-. apply K0. reflexivity. }
  step.   if_cases K1; zify_cond K1.
  { clear K1. apply (v6brU bp2 z c a2v defport q' m wb junk); try assumption; lia. }
  clear K1.
  step. step. step.
  step. step.
  assert (HC1 : 0 <= c + 1 <= 255) by lia.
  chkW 12 (c + 1) SHF HC1.
  step.
  lit_branch.
  replace (Z_to_bv 64 (F + 32 + c + 3)) with (Z_to_bv 64 (F + 32 + (c + 1) + 2)) by (f_equal; lia).
  replace (Z_to_bv 64 (F + 32 + c + 1)) with (Z_to_bv 64 (F + 32 + (c + 1))) by (f_equal; lia).
  replace (Z_to_bv 64 (c + 2)) with (Z_to_bv 64 (c + 1 + 1)) by (f_equal; lia).
  eapply (IH bp2 z (c + 1) _ defport q' m wb junk); try eassumption; try lia.
  rewrite unsigned_lit by lia. rewrite shiftr3_div. reflexivity.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma v6U : forall (bp2 z defport : Z) q' m v16 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x25 x26 x28 x29 x30 x31,
  minvU q' m 0 v16 (Z_to_bv 64 bp2) (Z_to_bv 64 (U + bp2)) (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 defport) wb ->
  pinvU m junk ->
  0 <= bp2 -> 1 <= z <= 255 -> bp2 + z <= ulen -> 0 <= defport < 2^64 ->
  nth_error wb (Z.to_nat z) = Some zbU ->
  (forall j' b, 0 <= j' < z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0) ->
  evt asegs (postU XALL)
    (USTP 0x8cfd0 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 (Z_to_bv 64 (F + 32)) x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP Z255 BPZ DP WZ WNZ.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof (munch_refl [(q' + 16, q' + 24)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step. step. step.
  step; fix_lit_store.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 16) (q' + 24) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  step. step.
  assert (HC1 : 0 <= 1 <= 255) by lia.
  chkW 12 1 SHF HC1.
  step. lit_branch.
  replace (Z_to_bv 64 (F + 35)) with (Z_to_bv 64 (F + 32 + 1 + 2)) by (f_equal; lia).
  replace (Z_to_bv 64 2) with (Z_to_bv 64 (1 + 1)) by reflexivity.
  lazymatch goal with |- context [TNode ?l (Some (Z_to_bv 64 (F + 33))) ?r] =>
    replace (TNode l (Some (Z_to_bv 64 (F + 33))) r) with (TNode l (Some (Z_to_bv 64 (F + 32 + 1))) r) by (do 2 f_equal; f_equal; lia) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply (v6loopU (S (Z.to_nat z)) bp2 z 1 _ defport q' mm wb junk); [lia| mv_tacU| pv_tacU| lia| lia| lia| lia| lia| exact WZ| exact WNZ|] end.
  rewrite unsigned_lit by lia. rewrite shiftr3_div. f_equal. f_equal. lia.
Qed.

Definition hpU_stmt : Prop :=
  forall (bp defport : Z) q' m v16 v24 v32 v40 v48 v56 wb junk
         x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 x26 x28 x29 x30 x31,
  minvU q' m 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb -> pinvU m junk -> 0 <= bp -> bp + 1 < ulen -> (defport = 80 \/ defport = 443) ->
  evt asegs (postU XALL)
    (USTP 0x8cef0 q' x1 x5 x6 x7 (Z_to_bv 64 defport) x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 x24 (Z_to_bv 64 bp) x26 x28 x29 x30 x31 m).

#[using="HC FI U ulen lo ustr slack st F FL SF ULR UFS"] Lemma nul_splitU : forall (l1 l2 : list byte), exists s r, l1 ++ zbU :: l2 = s ++ zbU :: r /\ ~ In zbU s /\ (length s <= length l1)%nat.
Proof.
  induction l1 as [|a l1 IH]; intros l2.
  - exists [], l2. cbn. repeat split; [LiaTuning.ctauto| lia].
  - destruct (Z.eq_dec (bv_unsigned a) 0) as [E|NE].
    + exists [], (l1 ++ zbU :: l2). assert (a = zbU) as -> by (apply bv_eq; rewrite E; reflexivity).
      cbn. repeat split; [LiaTuning.ctauto| lia].
    + destruct (IH l2) as (s & r & E & NI & L). exists (a :: s), r. cbn. rewrite E. repeat split; [| cbn in *; lia].
      intros [H|H]; [| exact (NI H)]. apply NE. subst a. reflexivity.
Qed.
#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma mod8_shiftU : forall x d, 0 <= d -> (x + d) mod 8 <= x mod 8 + d.
Proof. intros x d Hd. rewrite <- Z.add_mod_idemp_l by lia. apply Z.mod_le; [| lia]. pose proof (Z.mod_pos_bound x 8). lia. Qed.
#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma stpnA_length : forall (str : list byte), length (stpn_result_A str 255) = 255%nat.
Proof. intros str. unfold stpn_result_A, stpn_k_A. rewrite length_app, firstn_length, repeat_length. lia. Qed.
#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma stpnA_nth_lt : forall (str : list byte) j, (j < stpn_k_A str 255)%nat -> nth_error (stpn_result_A str 255 ++ [zbU]) j = nth_error str j.
Proof.
  intros str j Hj. unfold stpn_result_A. pose proof (Nat.le_min_l (length str) 255). unfold stpn_k_A in *.
  rewrite nth_error_app1. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
  rewrite nth_error_app1 by (rewrite firstn_length; lia).
  rewrite nth_error_firstn. destruct (Nat.ltb_spec0 j (Nat.min (length str) 255)); [reflexivity| lia].
Qed.
#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma stpnA_nth_z : forall (str : list byte), nth_error (stpn_result_A str 255 ++ [zbU]) (stpn_k_A str 255) = Some zbU.
Proof.
  intros str. unfold stpn_result_A. pose proof (Nat.le_min_l (length str) 255). pose proof (Nat.le_min_r (length str) 255). unfold stpn_k_A in *.
  set (k := Nat.min (length str) 255) in *.
  destruct (Nat.eq_dec k 255).
  - rewrite nth_error_app2. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
    rewrite length_app, firstn_length, repeat_length. replace (k - (Nat.min k (length str) + (255 - k)))%nat with 0%nat by lia. reflexivity.
  - rewrite nth_error_app1. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
    rewrite nth_error_app2 by (rewrite firstn_length; lia). rewrite firstn_length.
    replace (k - Nat.min k (length str))%nat with 0%nat by lia.
    destruct (255 - k)%nat eqn:E; [lia|]. reflexivity.
Qed.

#[using="U ulen lo ustr slack FL SF ULR"] Lemma wb_join255 : forall m (xs : list byte), rw_cells asegs m (F + 32) [CB 255 xs] -> rw_cells asegs m (F + 287) [CB 1 [zbU]] ->
  rw_cells asegs m (F + 32) [CB 256 (xs ++ [zbU])].
Proof.
  intros m xs W1 W2.
  pose proof (proj2 (rw_cells_app asegs m (F + 32) [CB 255 xs] [CB 1 [zbU]])) as J.
  cbn [cells_size csize Nat.add] in J. replace (F + 32 + Z.of_nat 255) with (F + 287) in J by lia.
  specialize (J (conj W1 W2)). cbn [app] in J.
  pose proof (rw_cells_merge asegs m (F + 32) [] [CB 255 xs; CB 1 [zbU]] []) as M.
  rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  specialize (M J). exact M.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma hpBU : forall (bp2 defport : Z) q' m v16 v32 v56 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31,
  minvU q' m 0 v16 (Z_to_bv 64 bp2) v32 (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) v56 (Z_to_bv 64 defport) wb ->
  pinvU m junk -> 0 <= bp2 <= ulen -> 0 <= defport < 2^16 ->
  evt asegs (postU XALL)
    (USTP 0x8cfa8 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) x23 (Z_to_bv 64 (F + 32)) (Z_to_bv 64 (U + bp2)) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP DP.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold UBANDd in UBu.

  destruct (nul_splitU (skipn (Z.to_nat bp2) ustr) slack) as (str & rest & ES & NI & LS). rewrite length_skipn in LS.
  assert (LR : Z.of_nat (length rest) = ulen - bp2 - Z.of_nat (length str) + Z.of_nat (length slack)).
  { pose proof (f_equal (@length byte) ES) as EL. rewrite !length_app, length_skipn in EL. cbn [length] in EL. lia. }
  assert (PAD' : (- (U + bp2 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length rest)).
  { replace (- (U + bp2 + Z.of_nat (length str) + 1)) with (- (U + ulen + 1) + (ulen - bp2 - Z.of_nat (length str))) by lia.
    etransitivity; [apply mod8_shiftU; lia|]. lia. }
  assert (SHWs : shw m (U + bp2) (Z.min 255 (Z.of_nat (length str) + 1))) by (apply (shwU_now m _ _ MU); lia).
  assert (SHWd : shw m (F + 32) 255) by (apply (shw_sub m (F + 32) 256 _ _ (shwW_now m SHF)); lia).
  splitcb WBC 0%nat [255; 1]%nat. name_junk WBC. split_chunk WBC 1%nat WB1 WB2.
  assert (SRC : bytes_at asegs m (U + bp2) (str ++ zbU :: rest)).
  { rewrite <- ES. pose proof TXT as T. rewrite <- (firstn_skipn (Z.to_nat bp2) (ustr ++ zbU :: slack)) in T. apply bytes_at_app in T. destruct T as [_ T].
    rewrite firstn_length, Nat.min_l in T by (rewrite length_app; cbn [length]; lia). rewrite Z2Nat.id in T by lia.
    rewrite skipn_app in T. replace (Z.to_nat bp2 - length ustr)%nat with 0%nat in T by lia. cbn [skipn] in T. exact T. }
  pose proof (munch_refl [(F + 287, F + 288); (q' + 32, q' + 40)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step; fix_lit_store.
  step. step.
  step; fix_lit_store.
  step.
  step.
  clear SHWs SHWd.
  absorbW MU WM MU0 WM0 (sub_fp_cons2 _ _ W0 (sub_fp_F (F + 287) (F + 288) ltac:(lia) ltac:(lia)) (sub_fp_stk (q' + 32) (q' + 40) ltac:(lia) ltac:(lia))).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SHWs : shw mm (U + bp2) (Z.min 255 (Z.of_nat (length str) + 1))) by (apply (shwU_now mm _ _ MU); lia);
    assert (SHWd : shw mm (F + 32) 255) by (apply (shw_sub mm (F + 32) 256 _ _ (shwW_now mm SHF)); lia) end.
  hideW MU WM.
  eapply evt_cut.
  { eapply (ic_strncpy IC) with (D := F + 32) (S := U + bp2) (n := 255) (str := str) (slack := rest) (lo := lo) (q := q');
    [ exact WB1 | lia | exact SRC | exact NI | exact PAD'
    | exact (proj1 SHWs) | exact (proj1 (proj2 SHWs)) | exact (proj2 (proj2 SHWs))
    | exact (proj1 SHWd) | exact (proj1 (proj2 SHWd)) | exact (proj2 (proj2 SHWd))
    | exact AE | exact ST | exact CLO | unfold A0_RT_STACK; lia | lia
    | lia | lia | lia | lia | lia
    | exact MI | reflexivity | reflexivity | reflexivity ]. }
  intros ms' PO. unfold strncpy_post_A in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MI' & ST' & AE' & WB1' & _).
  pose proof MUc as MUt. pose proof WMc as WMt.
  fs_sync FI RF MUc WMc FK LSUB.
  lazymatch type of MUt with munch _ ?ma _ => clear WB1 ST AE MI SHWs SHWd SRC end.
  lazymatch type of MUt with munch _ ?ma ?mb => transport_after_call asegs ma mb MUt WMt end.
  absorbW MU WM MUt WMt (sub_fp_cons2 _ _ W0 (sub_fp_stk lo q' ltac:(lia) ltac:(lia)) (sub_fp_F (F + 32) (F + 32 + 255) ltac:(lia) ltac:(lia))).
  clear MUt WMt.
  replace (ret_pc (Z_to_bv 64 577472)) with (Z_to_bv 64 577472) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  change (Z.to_nat 255) with 255%nat in WB1'.
  apply (rw_cells_reshape asegs _ _ _ [CB 1 [zbU]]) in WB2; [| cbn; LiaTuning.ctauto | reflexivity | reflexivity].
  pose proof (wb_join255 _ _ WB1' WB2) as WBC. clear WB1' WB2.

  set (wb' := stpn_result_A str 255 ++ [zbU]) in *.
  assert (LW : length wb' = 256%nat) by (subst wb'; rewrite length_app, stpnA_length; reflexivity).
  set (zn := stpn_k_A str 255).
  assert (ZN : (zn <= length str /\ zn <= 255)%nat) by (subst zn; unfold stpn_k_A; split; [apply Nat.le_min_l| apply Nat.le_min_r]).
  assert (WZ : nth_error wb' (Z.to_nat (Z.of_nat zn)) = Some zbU) by (rewrite Nat2Z.id; subst wb' zn; apply stpnA_nth_z).
  assert (WNZ : forall j' b, 0 <= j' < Z.of_nat zn -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0).
  { intros j' b Hj' Hb E0. subst wb'. rewrite stpnA_nth_lt in Hb by (subst zn; lia). apply NI.
    assert (b = zbU) as <- by (apply bv_eq; rewrite E0; reflexivity). eapply nth_error_In. exact Hb. }
  clearbody wb' zn.
  destruct (wb_nthU wb' 0 LW ltac:(lia)) as [b0 Hb0]. change (Z.to_nat 0) with 0%nat in Hb0.
  pose proof (bv_unsigned_in_range 8 b0) as BR0. unfold bv_modulus in BR0. cbn in BR0.
  pose proof (proj2 (proj1 WBC)) as WBB. cbn [cells_bytes cbytes] in WBB. rewrite app_nil_r in WBB.
  pose proof (u8ro_read asegs m' (F + 32) wb' 0 b0 (Z_to_bv 64 (F + 32)) WBB Hb0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  pose proof (munch_refl [(q' + 56, q' + 64)]%Z m') as MU0. pose proof (wmono_refl asegs m') as WM0.
  hideW MU WM.
  hide WBC. step.   unhide WBC.
  step.
  step; fix_lit_store.
  clear RD WBB.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 56) (q' + 64) ltac:(lia) ltac:(lia)).
  env_sync AE' MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  step.   if_cases K0; zify_cond K0.
  - clear K0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (v4U bp2 (Z.of_nat zn) defport b0 q' mm v16 wb' junk);
        [mv_tacU| pv_tacU| lia| lia| lia| lia| exact WZ| exact WNZ| exact Hb0] end.
  - rewrite (unsigned_lit (bv_unsigned b0)) in K0 by lia.
    assert (Z1 : 1 <= Z.of_nat zn).
    { destruct zn as [|zn']; [| lia]. exfalso. change (Z.to_nat (Z.of_nat 0)) with 0%nat in WZ. rewrite WZ in Hb0. injection Hb0 as E0. subst b0. vm_compute in K0. discriminate K0. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (v6U bp2 (Z.of_nat zn) defport q' mm v16 wb' junk);
        [mv_tacU| pv_tacU| lia| lia| lia| lia| exact WZ| exact WNZ] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWGIF SHWMARK SHWRESV TPV"] Lemma hpU : hpU_stmt.
Proof.
  unfold hpU_stmt. intros until x31. intros INV PINV BP BPL DPd.
  assert (DP : 0 <= defport < 2^16) by lia. clear DPd.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  pose proof (munch_refl [(q' + 64, q' + 72)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step; fix_lit_store.
  step. step. step.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 64) (q' + 72) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.

  hideW MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 32 sstep.
  unhide_transport MUs WMs.
  absorbW MU WM MUs WMs sub_fp_SF.
  env_sync AE MUs WMs. fs_sync FI RF MUs WMs FK LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(q' + 24, q' + 56)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  hideW MU WM.
  step.
  step; fix_lit_store.
  step.
  step.
  step; fix_lit_store.
  step.
  step; fix_lit_store.
  step. step.
  step.
  absorbW MU WM MU0 WM0 (sub_fp_stk (q' + 24) (q' + 56) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply (memsetO 64 152 0x8cfa8 q' mm 0 v16 (Z_to_bv 64 (bp + 2)) v32 (Z_to_bv 64 (O + 64)) (Z_to_bv 64 (O + 80)) v56 (Z_to_bv 64 defport) wb junk);
      [mv_tacU| pv_tacU| lia| lia| apply ret_pc_even; [lia| reflexivity]|] end.
  intros m' junk' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV2 PINV2.
  apply (hpBU (bp + 2) defport q' m' v16 v32 v56 wb junk'); [exact INV2| exact PINV2| lia| lia].
Qed.

Definition https6A : list byte := map (Z_to_bv 8) [104; 116; 116; 112; 115; 0].
#[using="HC FI U ulen lo ustr slack st F FL SF ULR"] Lemma https_bytesA : forall m, mem_inv asegs m -> bytes_at asegs m HTTPS_A https6A.
Proof.
  intros m MI. pose proof (ro_cells_image asegs m HTTPS_A https6A MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.
#[using="HC FI U lo st F FL SF ULEN ULR PAD"] Lemma nth_UA : forall i, 0 <= i <= ulen -> exists b, nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat i) = Some b.
Proof.
  intros i Hi. destruct (nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat i)) as [b|] eqn:Hb; [exists b; reflexivity|].
  exfalso. apply nth_error_None in Hb. rewrite length_app in Hb. cbn [length] in Hb. lia.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma slashU : forall (bp sbuf ssize : Z) q' m v16 v24 v32 v40 v48 v56 wb ja jc
    x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x24 x26 x28 x29 x30 x31,
  minvU q' m 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb -> pinvR m ->
  rw_cells asegs m O [CB 8 ja] -> rw_cells asegs m (O + 8) [C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 ssize)] -> rw_cells asegs m (O + 24) [CB 192 jc] ->
  0 <= bp -> bp + 1 < ulen -> 0 <= ssize < 2^64 -> (ssize = 5 -> sbuf = U /\ 5 <= ulen) ->
  evt asegs (postU XALL)
    (USTP 0x8cbd0 q' x1 x5 x6 x7 x10 (Z_to_bv 64 (bp + 1)) x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) (Z_to_bv 64 (O + 8)) x24 (Z_to_bv 64 bp) x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PR O1 O2 O3 BP0 BP1 SS HS.
  pose proof INV as INV'.
  destruct INV' as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & FK & AE & _).
  pose proof PR as PR'. destruct PR' as (TXT & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (SHWT : shw m U (ulen + 1)) by (apply (shwU_now m _ _ MU); lia).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (OUTJ : exists junk, rw_cells asegs m O [CB 216 junk]).
  { replace (O + 24) with (O + Z.of_nat 8 + Z.of_nat 16) in O3 by lia. exact (out_close m 8 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)). }
  assert (NOHP : forall y1 y10 y11 y12 y13, evt asegs (postU XALL)
            (USTP 0x8ccd8 q' y1 x5 x6 x7 y10 y11 y12 y13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) (Z_to_bv 64 (O + 8)) x24 (Z_to_bv 64 bp) x26 x28 x29 x30 x31 m)).
  { intros y1 y10 y11 y12 y13. destruct OUTJ as [junk OUT]. eapply evt_mono; [apply (nohpU bp q' m 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb junk); [exact INV| split; [exact OUT| exact PR]| lia]|].
    intros ms' H. exact (postU_mono _ _ ms' XOK_ALL H). }
  assert (HP : forall defport y1 y11 y12 y13, (defport = 80 \/ defport = 443) -> evt asegs (postU XALL)
            (USTP 0x8cef0 q' y1 x5 x6 x7 (Z_to_bv 64 defport) y11 y12 y13 x14 x15 x16 x17 x19 (Z_to_bv 64 F) (Z_to_bv 64 (O + 8)) x24 (Z_to_bv 64 bp) x26 x28 x29 x30 x31 m)).
  { intros defport y1 y11 y12 y13 HD. destruct OUTJ as [junk OUT]. apply (hpU bp defport q' m v16 v24 v32 v40 v48 v56 wb junk); [exact INV| split; [exact OUT| exact PR]| lia| lia| exact HD]. }
  destruct (nth_UA bp ltac:(lia)) as [b0 Hb0]. destruct (nth_UA (bp + 1) ltac:(lia)) as [b1 Hb1].
  pose proof (u8ro_read asegs m U _ bp b0 (Z_to_bv 64 (U + bp)) TXT Hb0 ltac:(lia) eq_refl) as RD0.
  pose proof (u8ro_read asegs m U _ (bp + 1) b1 (Z_to_bv 64 (U + (bp + 1))) TXT Hb1 ltac:(lia) eq_refl) as RD1.
  step. step. step. step.
  gen2 CONT1 0x8cbe8 12%nat 13%nat.
  { intros yi yj.
    step. step.
    step. if_cases K0; zify_cond K0. { apply NOHP. }
    step. step. step. step.
    gen2 CONT2 0x8cc0c 11%nat 12%nat.
    { intros zi zj.
      step. step.
      step. if_cases K1; zify_cond K1. { apply NOHP. }
      step. step. step.
      chk8N 11 (O + 16) SHWO'. step. lit_branch.
      step.
      step.
      step. if_cases K2; zify_cond K2.
      { step. step.   apply HP. left; reflexivity. }
      rewrite ?(unsigned_lit ssize) in K2 by lia. rewrite ?unsigned_lit in K2 by lia.
      destruct (HS ltac:(lia)) as [-> UL5].
      step. step.
      chk8N 10 (O + 8) SHWO'. step. lit_branch.
      step.
      step. step. step.
      step.
      pose proof (https_bytesA _ MI) as HB6.
      destruct (P0.H_memptr_cmp.strncasecmp_model_some (map (Z_to_bv 8) [104; 116; 116; 112; 115]) (ustr ++ Z_to_bv 8 0 :: slack) [] 5 ltac:(lia)
                  ltac:(rewrite length_app; cbn [length]; lia)) as (v & HM & HV).
      change (map (Z_to_bv 8) [104; 116; 116; 112; 115] ++ [Z_to_bv 8 0]) with https6A in HM.
      assert (SHWH : shw m HTTPS_A 6) by (apply (shwG_now m _ _ SHWHTTPS MU); lia).
      pose proof (bytes_at_bound _ _ _ _ TXT) as TB. rewrite length_app in TB. cbn [length] in TB.
      assert (SHWT5 : shw m U 5) by (apply (shw_sub m U (ulen + 1) U 5 SHWT); lia).
      assert (SHWH5 : shw m HTTPS_A 5) by (apply (shw_sub m HTTPS_A 6 HTTPS_A 5 SHWH); lia).
      eapply evt_cut.
      { eapply (ic_strncasecmp IC) with (A := U) (B := HTTPS_A) (n := 5) (ls := ustr ++ Z_to_bv 8 0 :: slack) (rs := https6A) (v := v) (lo := lo) (q := q');
        [ exact TXT | exact HB6 | exact HM
        | replace (Z.min 5 _) with 5 by (rewrite length_app; cbn [length]; lia); exact (proj1 SHWT5)
        | replace (Z.min 5 _) with 5 by (rewrite length_app; cbn [length]; lia); exact (proj1 (proj2 SHWT5))
        | replace (Z.min 5 _) with 5 by (cbn; lia); exact (proj1 SHWH5)
        | replace (Z.min 5 _) with 5 by (cbn; lia); exact (proj1 (proj2 SHWH5))
        | replace (Z.min 5 _) with 5 by (rewrite length_app; cbn [length]; lia); rng_tac
        | replace (Z.min 5 _) with 5 by (cbn; lia); rng_tac
        | exact AE | exact ST | exact CLO | unfold A0_RT_STACK; lia | lia
        | left; rewrite length_app; cbn [length]; lia | left; cbn; lia | exact MI | reflexivity | reflexivity | reflexivity | lia ]. }
      intros ms' PO. unfold strncmp_post_A in PO.
      destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MI' & ST' & AE' & TXT' & HB').
      pose proof (stackcallU q' m m' 248 _ _ _ _ _ _ _ wb INV MUc WMc MI' ST' AE') as INV2.
      pose proof (pinvR_stack q' m m' Hq PR MUc WMc) as PR2.
      destruct OUTJ as [junk OUT]. pose proof (out_stack q' m m' junk Hq OUT MUc WMc) as OUT2.
      replace (ret_pc (Z_to_bv 64 576604)) with (Z_to_bv 64 576604) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step.   if_cases K3; zify_cond K3.
      - step.
        apply (hpU bp 443 q' m' v16 v24 v32 v40 v48 v56 wb junk); [exact INV2| split; [exact OUT2| exact PR2]| lia| lia| right; reflexivity].
      - step. step.
        apply (hpU bp 80 q' m' v16 v24 v32 v40 v48 v56 wb junk); [exact INV2| split; [exact OUT2| exact PR2]| lia| lia| left; reflexivity]. }
    chkbN 11 (U + (bp + 1)) SHWT kk SHRk Hk.
    destruct Hk as [-> | [G1 G2]].
    - step. step. lit_branch. apply CONT2.
    - step. rewrite (sxb_small kk) by lia.
      step. if_cases G3; zify_cond G3; [| exfalso; lia].
      zstep.
      step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
      apply CONT2. }
  chkbN 12 (U + bp) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT1.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT1.
Qed.

#[using="Type"] Lemma zero16_cells : forall m X, rw_cells asegs m X [CB 16 (repeat (Z_to_bv 8 0) 16)] -> rw_cells asegs m X [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m X H. splitcb H 0%nat [8; 8]%nat. recell H 0%nat. recell H 1%nat.
  lazymatch type of H with rw_cells _ _ _ [C8 ?a; C8 ?b] =>
    replace a with (Z_to_bv 64 0) in H by (apply bv_eq; vm_compute; reflexivity);
    replace b with (Z_to_bv 64 0) in H by (apply bv_eq; vm_compute; reflexivity) end.
  exact H.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma noschU : forall q' m v16 v24 v32 v40 v48 v56 wb ja jc
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb -> pinvR m ->
  rw_cells asegs m O [CB 8 ja] -> rw_cells asegs m (O + 8) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells asegs m (O + 24) [CB 192 jc] ->
  evt asegs (postU XALL)
    (USTP 0x8cb90 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 (Z_to_bv 64 (O + 8)) x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PR O1 O2 O3.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PR as (TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  pose proof (munch_refl [(O, O + 32)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step.
  chk8N 10 O SHWO'. step. lit_branch.
  step. step.
  step; fix_lit_store.
  assert (AIV : app_ivs [(O, O + 32)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step.
  chk8N 12 (O + 24) SHWO1. step. lit_branch.
  step.
  step; fix_lit_store.
  step.
  step.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  absorbW MU WM MU0 WM0 (sub_fp_O O (O + 32) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu SHWO' SHWO1 AIV.
  destruct (rw_cells_forget asegs _ _ _ O1) as [ja' O1']. destruct (rw_cells_forget asegs _ _ _ O3) as [jc' O3'].
  cbn [cells_size csize Nat.add] in O1', O3'. clear O1 O3.
  step.   if_cases K1; zify_cond K1.
  -
    replace (O + 24) with (O + Z.of_nat 8 + Z.of_nat 16) in O3' by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (out_close mm 8 16 _ _ _ O1' eq_refl O2 eq_refl O3' eq_refl ltac:(lia)) as [junk OUT];
      eapply evt_mono; [apply (nohpU 0 q' mm 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb junk); [mv_tacU| split; [exact OUT| pr_tacU]| lia]|] end.
    intros ms' H. exact (postU_mono _ _ ms' XOK_ALL H).
  - rewrite ?unsigned_lit in K1 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (slashU 0 0 0 q' mm v16 v24 v32 v40 v48 v56 wb ja' jc'); [mv_tacU| pr_tacU| exact O1'| exact O2| exact O3'| lia| lia| lia| intros X; exfalso; lia] end.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma foundschU : forall (i : Z) q' m v16 v24 v32 v40 v48 v56 wb ja jc
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb -> pinvR m ->
  rw_cells asegs m O [CB 8 ja] -> rw_cells asegs m (O + 8) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells asegs m (O + 24) [CB 192 jc] ->
  1 <= i < ulen ->
  evt asegs (postU XALL)
    (USTP 0x8cc68 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 i) x22 (Z_to_bv 64 (O + 8)) x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PR O1 O2 O3 HI.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  destruct PR as (TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
  assert (AIV : app_ivs [(O, O + 32)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  pose proof (munch_refl [(O, O + 32)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  hideW MU WM.
  step. step. step.
  chk8N 11 (O + 16) SHWO'. step. lit_branch.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step.
  chk8N 10 (O + 8) SHWO1. step.   step. lit_branch.
  step.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO2 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step.
  chk8N 10 O SHWO2. step. lit_branch.
  step; fix_lit_store.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO3 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
  step. step. step.
  chk8N 11 (O + 24) SHWO3. step. lit_branch.
  step.
  step; fix_lit_store.
  step. step.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  absorbW MU WM MU0 WM0 (sub_fp_O O (O + 32) ltac:(lia) ltac:(lia)).
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  clear UBu SHWO' SHWO1 SHWO2 SHWO3 AIV.
  destruct (rw_cells_forget asegs _ _ _ O1) as [ja' O1']. destruct (rw_cells_forget asegs _ _ _ O3) as [jc' O3'].
  cbn [cells_size csize Nat.add] in O1', O3'. clear O1 O3.
  step.   if_cases K1; zify_cond K1.
  - rewrite ?unsigned_lit in K1 by lia.
    replace (Z_to_bv 64 (i + 2)) with (Z_to_bv 64 (i + 1 + 1)) by (f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply (slashU (i + 1) U i q' mm v16 v24 v32 v40 v48 v56 wb ja' jc'); [mv_tacU| pr_tacU| exact O1'| exact O2| exact O3'| lia| lia| lia| intros X; split; [reflexivity| lia]] end.
  - replace (O + 24) with (O + Z.of_nat 8 + Z.of_nat 16) in O3' by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (out_close mm 8 16 _ _ _ O1' eq_refl O2 eq_refl O3' eq_refl ltac:(lia)) as [junk OUT];
      eapply evt_mono; [apply (nohpU (i + 1) q' mm 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb junk); [mv_tacU| split; [exact OUT| pr_tacU]| lia]|] end.
    intros ms' H. exact (postU_mono _ _ ms' XOK_ALL H).
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma schloopU : forall (k : nat) (i : Z) q' m v16 v24 v32 v40 v48 v56 wb ja jc
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31,
  ulen - i < Z.of_nat k -> 1 <= i < ulen ->
  minvU q' m 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb -> pinvR m ->
  rw_cells asegs m O [CB 8 ja] -> rw_cells asegs m (O + 8) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells asegs m (O + 24) [CB 192 jc] ->
  evt asegs (postU XALL)
    (USTP 0x8cb44 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 i) (Z_to_bv 64 114349209288704) (Z_to_bv 64 (O + 8)) (Z_to_bv 64 46)
          x25 (Z_to_bv 64 58) x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros until x31; intros HK HI INV PR O1 O2 O3; [lia|].
  pose proof INV as INV'.
  destruct INV' as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & FK & AE & _).
  pose proof PR as PR'. destruct PR' as (TXT & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (SHWT : shw m U (ulen + 1)) by (apply (shwU_now m _ _ MU); lia).
  destruct (nth_UA i ltac:(lia)) as [b Hb]. pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
  pose proof (u8ro_read asegs m U _ i b (Z_to_bv 64 (U + i)) TXT Hb ltac:(lia) eq_refl) as RD.

  assert (NOSCH : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y25 y28 y29 y30 y31, evt asegs (postU XALL)
            (USTP 0x8cb90 q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 (Z_to_bv 64 114349209288704) (Z_to_bv 64 (O + 8)) (Z_to_bv 64 46)
                  y25 (Z_to_bv 64 58) y28 y29 y30 y31 m)).
  { intros. apply (noschU q' m v16 v24 v32 v40 v48 v56 wb ja jc); assumption. }
  assert (NEXT : forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y25 y28 y29 y30 y31, evt asegs (postU XALL)
            (USTP 0x8cb3c q' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 i) (Z_to_bv 64 114349209288704) (Z_to_bv 64 (O + 8)) (Z_to_bv 64 46)
                  y25 (Z_to_bv 64 58) y28 y29 y30 y31 m)).
  { intros. step.
    step.   if_cases K1; zify_cond K1.
    - apply NOSCH.
    - rewrite ?unsigned_lit in K1 by lia. apply (IH (i + 1) q' m v16 v24 v32 v40 v48 v56 wb ja jc); try assumption; lia. }
  step. step. step. step.
  gen2 CONT 0x8cb5c 11%nat 12%nat.
  { intros yi yj.
    step.
    step.   if_cases K2; zify_cond K2.
    { apply (foundschU i q' m v16 v24 v32 v40 v48 v56 wb ja jc); assumption. }
    step.   step.
    eapply evt_cut.
    { eapply (isalnum_spec_A); [unfold zxb; rewrite unsigned_lit by lia; lia| exact MI]. }
    intros ms' PO. unfold ctype_post_A in PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & -> & _ & _ & _).
    replace (ret_pc (Z_to_bv 64 576364)) with (Z_to_bv 64 576364) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step.   if_cases K3; zify_cond K3.
    { apply NEXT. }
    step.   if_cases K4; zify_cond K4.
    { apply NOSCH. }
    step. step.
    step.   if_cases K5; zify_cond K5.
    { apply NEXT. }
    step.   apply NOSCH. }
  chkbN 11 (U + i) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 SHZ SHR OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma bodyU : forall q' m v16 v24 v32 v40 v48 v56 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb -> pinvU m junk ->
  evt asegs (postU XALL)
    (USTP 0x8cadc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 (Z_to_bv 64 (O + 8)) x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV.
  step. step. step.
  step.
  apply (memsetOo 8 16 0x8caec q' m 248 v16 v24 v32 v40 v48 v56 (Z_to_bv 64 (O + 16)) wb junk); [exact INV| exact PINV| lia| lia| apply ret_pc_even; [lia| reflexivity]|].
  clear INV PINV. intros m' ja jc y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV PR O1 O2 O3.
  apply zero16_cells in O2. change (O + Z.of_nat 8) with (O + 8) in O2.
  change (216 - 8 - 16)%nat with 192%nat in O3. replace (O + Z.of_nat 8 + Z.of_nat 16) with (O + 24) in O3 by lia.
  pose proof INV as INV'.
  destruct INV' as ((kq' & Hq32) & Hq & ST & (j0 & j96 & QC) & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & FK & AE & _).
  pose proof PR as PR'. destruct PR' as (TXT & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (SHWT : shw m' U (ulen + 1)) by (apply (shwU_now m' _ _ MU); lia).
  assert (NOSCH : forall y1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z19 z22 z24 z25 z26 z28 z29 z30 z31, evt asegs (postU XALL)
            (USTP 0x8cb90 q' y1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z19 z22 (Z_to_bv 64 (O + 8)) z24 z25 z26 z28 z29 z30 z31 m')).
  { intros. apply (noschU q' m' v16 v24 v32 v40 v48 v56 wb ja jc); assumption. }
  step.   if_cases K0; zify_cond K0.
  { apply NOSCH. }
  rewrite ?unsigned_lit in K0 by lia.
  destruct (nth_UA 0 ltac:(lia)) as [b Hb].
  pose proof (u8ro_read asegs m' U _ 0 b (Z_to_bv 64 U) TXT Hb ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. step. step.
  gen2 CONT 0x8cb04 10%nat 11%nat.
  { intros yi yj.
    step.
    step.   if_cases K1; zify_cond K1.
    { apply NOSCH. }
    rewrite ?unsigned_lit in K1 by lia.
    step. step.
    step. step. step.
    step.   if_cases K2; zify_cond K2.
    { apply NOSCH. }
    step. step. step. step. step.
    step.
    apply (schloopU (Datatypes.S (Z.to_nat ulen)) 1 q' m' v16 v24 v32 v40 v48 v56 wb ja jc); try assumption; lia. }
  chkbN 10 U SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    step.
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="ulen CLO RF0 F FL SF OLB ULEN ULR UHI UFS UBAND"] Lemma pinvU_pro : forall m junk,
  pinvU m0 junk -> munch ((lo, q) :: FSIV [])%Z m0 m -> wmono asegs m0 m -> fkeep FI [] st m0 m -> pinvU m junk.
Proof.
  intros m junk (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)) MU WM FK.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  pose proof UBAND as UBu. unfold UBANDd in UBu.
  assert (DJL : forall X n, 0 <= n -> X + n <= 0x609000 -> disjoint_from ((lo, q) :: FSIV [])%Z X n).
  { intros X n H0 H1. cbn [disjoint_from]. repeat (split; [left; clear - H0 H1 CLO ACR FSB1 ESHB EKB; lia|]). exact I. }
  unfold pinvU, pinvR.
  split; [apply (rw_cells_fkeep FI [] st m0 m _ _ OUT FK WM); [left; apply (lb_sub _ O 216 _ _ OLB); cbn [cells_size csize Nat.add]; lia| exact I]|].
  split; [apply (bytes_at_transport asegs _ m0 m _ _ TXT MU); rewrite length_app; cbn [length disjoint_from];
          split; [left; clear - UHI CLO ULEN; lia|]; split; [clear - UFS ULEN; lia|]; split; [clear - UBu ULEN ESHB EKB FSB1 FSB2 ACR; lia| exact I]|].
  split; [exists ev; apply (rw_cells_transport asegs _ m0 m _ _ ERRC MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m0 m _ _ SSPG MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m0 m _ _ SSPC MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  split; [apply (rw_cells_transport asegs _ m0 m _ _ GOTG MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia|].
  exists gv. apply (rw_cells_transport asegs _ m0 m _ _ GIFC MU WM); apply DJL; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Qed.

#[using="IC STACK_MALLOC_3 SET_SHADOW_F5 kq kO CLO LO AL16 QHI RF0 FCO FE0 Q47 SHZ SHR F FL st1 SF OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWHTTPS SHWGIF SHWMARK SHWRESV TPV"] Lemma puri_evt : forall junk t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 -> pinvU m0 junk ->
  evt asegs (postU XALL)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 U) (Z_to_bv 64 ulen) (Z_to_bv 64 O) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 puri_entryA) fc None m0 (seg_rom asegs)).
Proof.
  intros junk t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE PINV.
  apply (prologueU t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE).
  intros q' m v16 v24 v32 v40 v48 v56 wb x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 MV MUP FKP.
  assert (PV : pinvU m junk).
  { destruct MV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WM & _). exact (pinvU_pro m junk PINV MUP WM FKP). }
  apply (bodyU q' m v16 v24 v32 v40 v48 v56 wb junk); [exact MV| exact PV].
Qed.

End W.
