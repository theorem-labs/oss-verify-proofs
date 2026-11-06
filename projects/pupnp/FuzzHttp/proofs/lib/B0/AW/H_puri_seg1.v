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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF F_ctypeA H_parse_uric H2Kit AWRng AWUb.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_memptr_cmp.
Import ListNotations.
Open Scope Z_scope.

Definition puri_entryA : Z := 0x8d38c.
Notation PURI_DEPTH_A := 16384%Z.
Notation ERRNO_A := 0x5e750c%Z.
Notation HTTPS_A := 0x21c40%Z.
Notation GOT_GIF_A := 0xab9a8%Z.
Notation GIF_A := 0xaf6a0%Z.
Notation got_sspA := 0xab9c8%Z.
Notation ssp_guardA := 0x6075f0%Z.

Definition puriF {HC : HasCeiling} (FI : fs_if) (st : fsstate FI) : Z := fs_F FI st 3.
Definition puriFL {HC : HasCeiling} (FI : fs_if) (st : fsstate FI) : Z := fs_FL FI st 3.
Definition puriSF {HC : HasCeiling} (FI : fs_if) (st : fsstate FI) : Z := sh (fs_F FI st 3).

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_3 : stack_malloc_stmt FI 3.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Variables (U O ulen lo q kq kO : Z) (ustr slack : list byte) (st : fsstate FI).
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
Variable canary : word.

Local Notation F := (puriF FI st).  Local Notation FL := (puriFL FI st).  Local Notation SF := (puriSF FI st).  Let st1 := fs_next FI st 3.

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

Notation USTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 SF) (Z_to_bv 64 U) x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 2147450880)
           x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Notation zbU := (Z_to_bv 8 0).

Definition minvU (q' : Z) (m : mem) (w : Z) (v0 v8 v16 v24 v32 v40 v48 v56 : word) (wb : list byte) : Prop :=
  (exists k', q' = 32 * k') /\ q + -208 <= q' <= q + -192
  /\ stk asegs m lo q'
  /\ (exists j64, rw_cells asegs m q' [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; CB 16 j64; C8 (wz F)])
  /\ rw_cells asegs m (F + 32) [CB 256 wb]
  /\ stk asegs m (q' + 88) (q + -104)
  /\ rw_cells asegs m (q + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m F [C8 (wz 0x41b58ab3); C8 (wz 0x2096c); C8 (wz 0x8d38c); C8 (wz q')]
  /\ (exists j216, rw_cells asegs m (F + 288) [CB 216 j216; C8 (wz FL)])
  /\ rw_cells asegs m SF (ushadow w)
  /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)]
  /\ mem_inv asegs m
  /\ munch W0 m0 m /\ wmono asegs m0 m
  /\ fkeep FI WP st m0 m /\ asan_env asegs m
  /\ (exists stc, RFAKE FI stc m /\ fs_live FI stc = fs_newff FI st 3 :: fs_live FI st).

Definition UBANDd : Prop := U + ulen + 1 + Z.of_nat (length slack) <= 0x7fff7000 \/ 0x10007fff8000 <= U.

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
Hypothesis UBAND : UBANDd.
Hypothesis SHWU : shw m0 U (ulen + 1).
Hypothesis SHWHTTPS : shw m0 HTTPS_A 6.
Hypothesis SHWGIF : shw m0 GIF_A 4.
Hypothesis SHWMARK : shw m0 MARKTAB_A 10.
Hypothesis SHWRESV : shw m0 RESVTAB_A 13.
Hypothesis TPV : tp = Z_to_bv 64 6190512.

Ltac mv_tacU := unfold minvU; split; [eexists; eassumption|]; split; [assumption|];
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eexists; split; eassumption.

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
  split; [unfold puriSF, puriF, sh, SHADOW_OFF in *; clear - FAL; Z.div_mod_to_equations; lia|].
  split; [clear - FSB4; Z.div_mod_to_equations; lia|].
  split; [unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia|].
  repeat (split; [first [assumption | lia]|]). first [assumption | lia].
Qed.

#[using="STACK_MALLOC_3 kq ustr slack st1 CLO LO AL16 QHI RF0 FCO FE0 Q47 OHI OLB ULR"] Lemma prologueU : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
  forall (Q : machine_state -> Prop),
  (forall q' m v0 v8 v16 v24 v32 v40 v48 v56 wb x1 x5 x6 x7 x11 x12 x13 x14 x16 x17 x28 x29 x30 x31,
     minvU q' m 248 v0 v8 v16 v24 v32 v40 v48 v56 wb ->
     munch ((lo, q) :: FSIV [])%Z m0 m -> fkeep FI [] st m0 m ->
     evt asegs Q (USTP 0x8d524 q' x1 x5 x6 x7 (Z_to_bv 64 F) x11 x12 x13 x14 (Z_to_bv 64 F) x16 x17 (Z_to_bv 64 O) (Z_to_bv 64 ulen) s6 s7 s8 s9 s10 x28 x29 x30 x31 m)) ->
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
  carve_frame 192%nat ST.
  step. do 14 (step; fix_lit_store).
  step.
  step.
  rewrite (unsigned_lit (q + -192)) by lia. rewrite land_align32 by lia.
  remember (q + -192 - (q + -192) mod 32)%Z as q' eqn:Eq0.
  assert (Hq : q' = q + -192 \/ q' = q + -192 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
  assert (Hq32 : exists k', q' = 32 * k') by (exists ((q + -192) / 32); clear - Eq0; Z.div_mod_to_equations; lia).
  assert (QL : q + -208 <= q' <= q + -192) by (clear - Hq; lia).
  clear Eq0.
  lazymatch goal with FRx : rw_cells asegs ?mm (q + -192) (?c0 :: ?c1 :: ?rest) |- _ =>
    destruct (align_frame_gen mm lo (q + -192) q' [c0; c1] rest 88%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
    clear FRx end.
  clear Hq.
  clear ST. rename STq into ST. change (Z.of_nat 88) with 88 in GAP, FRhi. replace (q + -192 + 88) with (q + -104) in GAP, FRhi by lia.
  step.
  step. step.
  step. step. step. step.
  step. step.
  step.
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
  step; fix_lit_store.
  do 8 step.
  step; fix_lit_store. step; fix_lit_store. step; fix_lit_store.
  step. step.
  replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
    by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; reflexivity).

  hideW MU WM. lazymatch type of MUP with ?T => change (hid2 T) in MUP end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 64)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 4 sstep.
  step.
  do 40 sstep.
  unhide_transport MUs WMs.
  assert (SUBP : sub_fp [(SF, SF + 64)]%Z ((lo, q) :: FSIV [])%Z).
  { intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia| exact I]. }
  assert (SUB0 : sub_fp [(SF, SF + 64)]%Z W0).
  { intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia| exact I]. }
  unfold hid2 in MUP.
  lazymatch type of MUs with munch _ ?ma ?mf => pose proof (munch_absorb _ _ m0 ma mf MUP MUs SUBP) as MUP' end. clear MUP. rename MUP' into MUP.
  absorbW MU WM MUs WMs SUB0. clear MUs WMs SUBP SUB0.

  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  splitcb QC 0%nat [8; 8; 8; 8; 8; 8; 8; 8; 16]%nat. recell QC 0%nat. recell QC 1%nat. recell QC 2%nat. recell QC 3%nat. recell QC 4%nat. recell QC 5%nat. recell QC 6%nat. recell QC 7%nat. name_junk QC.
  splitcb FRF 4%nat [256; 216]%nat. name_junk FRF.
  split_chunk FRF 4%nat FH R1. split_chunk R1 1%nat WBC FT.
  replace (F + 32 + 256) with (F + 288) in FT by lia.
  lazymatch type of FK with fkeep _ _ _ _ ?mm => assert (FKW : fkeep FI WP st m0 mm) by (eapply fkeep_weaken; [exact FK| intros a Ha; exact I| intros g Hg; exact Hg]) end.
  destruct Hq32 as (kq' & Hq32).
  change (Z.of_nat 32) with 32 in WBC.
  eapply K; [mv_tacU| exact MUP| exact FK].
Qed.

#[using="U ulen lo ustr slack m0 SHWO ULR"] Lemma WP_app : app_ivs WP.
Proof.
  pose proof (shw_win_ok _ _ _ SHWO) as WK. unfold app_ivs.
  apply Forall_cons; [eapply app_iv_of_win_ok; [exact WK| lia| lia]|].
  apply Forall_cons; [apply app_iv_low; lia|]. apply Forall_nil.
Qed.
#[using="U ulen ustr slack m0 CLO SHWO ULR"] Lemma W0_fsw : Forall (fsw_iv FI) W0.
Proof. apply fsw_cons_app; [apply app_iv_stack; exact CLO| apply fsw_FSIV; exact WP_app]. Qed.

#[using="U ulen kq ustr slack CLO LO AL16 Q47 SHZ SHR SHWO ULR"] Lemma shwStk_now : forall m q', munch W0 m0 m -> q + -208 <= q' <= q + -192 -> shw m lo (q' - lo).
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
#[using="U ulen lo ustr slack m0 SHWO ULEN ULR PAD UHI"] Lemma WP_out : forall a, sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE -> outside WP a.
Proof.
  intros a Ha. apply (app_ivs_outside WP a WP_app).
  pose proof (fsb_ok FI) as FSBOK. destruct FSBOK as (F1 & F2 & F3 & F4 & F5).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold shband, SH_LO, SH_HI. unfold sh, SHADOW_OFF in Ha. Z.div_mod_to_equations. lia.
Qed.

#[using="U ulen ustr slack RF0 OLB SHWO ULEN ULR PAD UHI"] Lemma shwO_now : forall m X n, munch W0 m0 m -> fkeep FI WP st m0 m -> O <= X -> X + n <= O + 216 -> 0 <= n -> shw m X n.
Proof.
  intros m X n MU FK H1 H2 H3.
  eapply (shw_fkeep FI WP st m0 m X n); [eapply shw_sub; [exact SHWO| lia| lia| lia]| exact FK| exact RF0| eapply lb_sub; [exact OLB| lia| lia]| exact WP_out].
Qed.
#[using="ustr slack CLO SHWO ULR UFS SHWU"] Lemma shwU_now : forall m X n, munch W0 m0 m -> U <= X -> X + n <= U + (ulen + 1) -> 0 <= n -> shw m X n.
Proof.
  intros m X n MU H1 H2 H3.
  apply (shw_frame_fs FI W0 m0 m X n (shw_sub _ _ _ _ _ SHWU H1 H2 H3) MU W0_fsw). clear - UFS H1 H2 H3. lia.
Qed.
#[using="U ulen ustr slack CLO SHWO ULR"] Lemma shwG_now : forall m X n, shw m0 X n -> munch W0 m0 m -> X + n <= 0x609000 -> shw m X n.
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

#[using="U ulen ustr slack ULR"] Lemma sub_fp_O : forall a b, O <= a -> b <= O + 216 -> sub_fp [(a, b)] W0.
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
#[using="U ulen ustr slack ULR"] Lemma sub_fp_stk : forall a b, lo <= a -> b <= q -> sub_fp [(a, b)] W0.
Proof. intros a b H1 H2 xo Ho. cbn [outside] in *. destruct Ho as (H0 & _). split; [lia| exact I]. Qed.

#[using="U ulen lo ustr slack ULR"] Lemma out_open : forall m junk (off n : nat), rw_cells asegs m O [CB 216 junk] -> (off + n <= 216)%nat ->
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
#[using="U ulen lo ustr slack ULR"] Lemma out_close : forall m (off n : nat) ca cb cc, rw_cells asegs m O ca -> cells_size ca = off ->
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

#[using="IC ulen kO CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UHI UFS"] Lemma memsetO : forall (off n : nat) (ret : Z) q' m w v0 v8 v16 v24 v32 v40 v48 v56 wb junk
    x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
  minvU q' m w v0 v8 v16 v24 v32 v40 v48 v56 wb -> pinvU m junk -> (off + n <= 216)%nat -> (0 < n)%nat ->
  ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
  (forall m' junk' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     minvU q' m' w v0 v8 v16 v24 v32 v40 v48 v56 wb -> pinvU m' junk' ->
     evt asegs Q (USTP ret q' (Z_to_bv 64 ret) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x20 x21 x22 x23 x24 x25 x26 y28 y29 y30 y31 m')) ->
  evt asegs Q (USTP 0x56f30 q' (Z_to_bv 64 ret) x5 x6 x7 (Z_to_bv 64 (O + Z.of_nat off)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat n))
                    x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros INV PINV HON HN0 ERET K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
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

#[using="IC ulen kO CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UHI UFS"] Lemma memsetOo : forall (off n : nat) (ret : Z) q' m w v0 v8 v16 v24 v32 v40 v48 v56 wb junk
    x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
  minvU q' m w v0 v8 v16 v24 v32 v40 v48 v56 wb -> pinvU m junk -> (off + n <= 216)%nat -> (0 < n)%nat ->
  ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
  (forall m' ja jc y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     minvU q' m' w v0 v8 v16 v24 v32 v40 v48 v56 wb -> pinvR m' ->
     rw_cells asegs m' O [CB off ja] -> rw_cells asegs m' (O + Z.of_nat off) [CB n (repeat (Z_to_bv 8 0) n)] ->
     rw_cells asegs m' (O + Z.of_nat off + Z.of_nat n) [CB (216 - off - n) jc] ->
     evt asegs Q (USTP ret q' (Z_to_bv 64 ret) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 x20 x21 x22 x23 x24 x25 x26 y28 y29 y30 y31 m')) ->
  evt asegs Q (USTP 0x56f30 q' (Z_to_bv 64 ret) x5 x6 x7 (Z_to_bv 64 (O + Z.of_nat off)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.of_nat n))
                    x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros INV PINV HON HN0 ERET K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
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

#[using="SET_SHADOW_F5 ulen kq ustr slack CLO LO AL16 RF0 Q47 OLB ULEN ULR PAD UHI"] Lemma exitU : forall (r : Z) (X : Z -> mem -> Prop) q' m w v0 v8 v16 v24 v32 v40 v48 v56 wb
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x24 x25 x26 x28 x29 x30 x31,
  minvU q' m w v0 v8 v16 v24 v32 v40 v48 v56 wb -> X r m -> rframeU (X r) ->
  evt asegs (postU X) (USTP 0x8d8f8 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 r) x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV HX RFR.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
  destruct (new_frame_facts FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
  pose proof (new_frame_fk FI st 3 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
  clear PFAP PFS1 PFS2. hideW MU WM.
  pose proof (munch_refl WEU m) as MUE. pose proof (wmono_refl asegs m) as WME. unfold WEU in MUE.
  pose proof (munch_refl [(lo, q); (F, F + 512); (SF, SF + 64)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  step. step. step; fix_lit_store.
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
  replace (ret_pc (Z_to_bv 64 579860)) with (Z_to_bv 64 579860) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
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

  release_frame QC ST' (q' + 88)%Z.
  pose proof (stk_merge asegs _ _ _ _ ST' GAP ltac:(lia)) as STm. clear ST' GAP.
  release_frame FRhi STm q.
  absorbW MU WM MUE WME sub_fp_WEU.
  apply evt_done. unfold postU. exists r. do 14 eexists.
  lazymatch goal with |- exists _ _, MS _ _ _ _ _ ?mm _ = _ /\ _ => exists mm, (fs_after_release FI stc) end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FK|]. split; [exact LIVE3|]. split; [exact RF3|].
  split; [exact STm|]. split; [assumption|]. exact (RFR m _ HX MUE WME).
Qed.

#[using="IC kO CLO LO RF0 Q47 OAL OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS SHWU SHWMARK SHWRESV"] Lemma puricO : forall (off : nat) (bp ret : Z) q' m w v0 v8 v16 v24 v32 v40 v48 v56 wb junk
    x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 (Q : machine_state -> Prop),
  minvU q' m w v0 v8 v16 v24 v32 v40 v48 v56 wb -> pinvU m junk -> (off = 32 \/ off = 48)%nat -> 0 <= bp <= ulen ->
  ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
  (forall m' ja jc (i : Z) y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
     minvU q' m' w v0 v8 v16 v24 v32 v40 v48 v56 wb -> pinvR m' -> 0 <= i <= ulen - bp ->
     rw_cells asegs m' O [CB off ja] -> rw_cells asegs m' (O + Z.of_nat off) [C8 (Z_to_bv 64 (U + bp)); C8 (Z_to_bv 64 i)] ->
     rw_cells asegs m' (O + Z.of_nat off + 16) [CB (200 - off) jc] ->
     evt asegs Q (USTP ret q' (Z_to_bv 64 ret) y5 y6 y7 (Z_to_bv 64 i) y11 y12 y13 y14 y15 y16 y17 x20 x21 x22 x23 x24 x25 x26 y28 y29 y30 y31 m')) ->
  evt asegs Q (USTP 0x8e19c q' (Z_to_bv 64 ret) x5 x6 x7 (Z_to_bv 64 (U + bp)) (Z_to_bv 64 (ulen - bp)) (Z_to_bv 64 (O + Z.of_nat off))
                    x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 m).
Proof.
  intros until Q; intros INV PINV HOFF HBP ERET K.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j64 & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
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

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma tail2U : forall (bp i : Z) q' m w v0 v8 v16 v24 v32 v48 v56 wb junk
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31,
  minvU q' m w v0 v8 v16 v24 v32 (Z_to_bv 64 1) v48 v56 wb -> pinvU m junk -> 0 <= bp -> 0 <= i -> bp + i <= ulen ->
  evt asegs (postU XOK)
    (USTP 0x8d864 q' x1 x5 x6 x7 (Z_to_bv 64 i) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) x23 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 bp) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP0 I0 BPI.
  pose proof INV as INV'.
  destruct INV' as ((kq' & Hq32) & Hq & ST & (j64 & QC) & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & FK & AE & _).
  pose proof PINV as PINV'. destruct PINV' as (_ & TXT & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (SHWT : shw m U (ulen + 1)) by (apply (shwU_now m _ _ MU); lia).

  assert (NF : forall y1 y10 y11 y12, evt asegs (postU XOK)
            (USTP 0x8d8c4 q' y1 x5 x6 x7 y10 y11 y12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) x23 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 (bp + i)) x28 x29 x30 x31 m)).
  { intros y1 y10 y11 y12. clear ST QC MI MU WM FK AE TXT SHWT.
    destruct INV as ((kq2 & Hq32b) & Hq2 & ST & (j64b & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI & MU & WM & FK & AE & (stc & RF & LIVE1)).
    destruct PINV as (OUT & TXT & (ev & ERRC) & SSPG & SSPC & GOTG & (gv & GIFC)).
    pose proof geomU as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & PFAP & PFS1 & PFS2 & FSB1 & FSB2 & FSB5).
    assert (SHWO' : shw m O 216) by (apply (shwO_now m _ _ MU FK); lia).
    destruct (out_open m junk 48 16 OUT ltac:(lia)) as (ja & jb & jc & O1 & O2 & O3). clear OUT.
    change (Z.of_nat 48) with 48 in O2, O3. change (Z.of_nat 16) with 16 in O3.
    splitcb O2 0%nat [8; 8]%nat. recell O2 0%nat. recell O2 1%nat. name_junk O2.
    pose proof UBAND as UBu. unfold UBANDd in UBu.
    pose proof (munch_refl [(O + 48, O + 64)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    hideW MU WM.
    step. step. step.
    chk8N 11 (O + 48) SHWO'. step. lit_branch.
    step; fix_lit_store.
    assert (AIV : app_ivs [(O + 48, O + 64)]%Z) by (apply Forall_cons; [eapply app_iv_of_win_ok; [exact (shw_win_ok _ _ _ SHWO')| lia| lia]| apply Forall_nil]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (SHWO1 : shw mm O 216) by exact (shw_frame _ m mm O 216 SHWO' MU0 AIV) end.
    step. step. step.
    chk8N 11 (O + 56) SHWO1. step. lit_branch.
    step; fix_lit_store.
    step.
    destruct (liveU stc LIVE1) as (LVF & LVS & LVL & PLB1 & LSUB).
    absorbW MU WM MU0 WM0 (sub_fp_O (O + 48) (O + 64) ltac:(lia) ltac:(lia)).
    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    clear UBu SHWO' SHWO1 AIV.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (out_close mm 48 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'];
      apply (exitU 1 XOK q' mm w v0 v8 v16 v24 v32 (Z_to_bv 64 1) v48 v56 wb); [mv_tacU| split; [reflexivity| exists junk'; split; [exact OUT'| pr_tacU]]| apply XU_rframe] end. }
  step.
  rewrite ?(unsigned_lit bp), ?(unsigned_lit i) by lia.
  replace (i + bp) with (bp + i) by lia.
  step.   if_cases K1; zify_cond K1.
  { apply NF. }
  rewrite ?(unsigned_lit (bp + i)), ?(unsigned_lit ulen) in K1 by lia.
  step. step.
  step. ubr.
  zstep. zstep. ub_b2z. step. lit_branch_safe.
  ub_null.
  destruct (nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat (bp + i))) as [b|] eqn:Hb.
  2:{ exfalso. apply nth_error_None in Hb. rewrite length_app in Hb. cbn [length] in Hb. lia. }
  pose proof (u8ro_read asegs m U _ (bp + i) b (Z_to_bv 64 (U + (bp + i))) TXT Hb ltac:(lia) eq_refl) as RD.
  step. step.
  gen2 CONT 0x8d898 11%nat 12%nat.
  { intros yi yj.
    step.   step.
    step.   if_cases K2; zify_cond K2.
    { apply NF. }
    zstep. step. ubr.
    step.   step.
    step.   rewrite ?(unsigned_lit ulen), ?(unsigned_lit (bp + i + 1)) by lia.
    step.   step.
    apply (puricO 48 (bp + i + 1) 0x8d8c0 q' m w v0 v8 v16 v24 v32 (Z_to_bv 64 1) v48 v56 wb junk); [exact INV| exact PINV| right; reflexivity| lia| apply ret_pc_even; [lia| reflexivity]|].
    intros m' ja jc i2 y5 y6 y7 z11 z12 z13 z14 z15 z16 z17 y28 y29 y30 y31 INV2 PR2 I2 O1 O2 O3.
    destruct (out_close m' 48 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'].
    step.   step.
    apply (exitU 1 XOK q' m' w v0 v8 v16 v24 v32 (Z_to_bv 64 1) v48 v56 wb); [exact INV2| split; [reflexivity| exists junk'; split; [exact OUT'| exact PR2]]| apply XU_rframe]. }
  chkbN 11 (U + (bp + i)) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="U ulen lo ustr slack ULR"] Lemma slti0_nonnegU : forall x, 0 <= x < 2^63 -> (Z.lxor x 9223372036854775808 <? 9223372036854775808) = false.
Proof. intros x Hx. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia. Qed.

Ltac ub_ptr := rewrite ?slti0_nonnegU by lia; ub_b2z; cbn [Z.b2z]; change (Z.lxor (Z.lxor 0 0) 1) with 1.

#[using="U ulen lo ustr slack ULR"] Lemma Z_to_le_bytes_appU : forall n k z, Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros k z.
  - cbn [Nat.add app]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
#[using="U ulen lo ustr slack ULR"] Lemma le8_small_splitU : forall v, (0 <= v < 2^32)%Z -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
  intros v Hv. unfold le8, le4, RiscvSemantics.word_to_le_bytes. rewrite !unsigned_lit by lia. rewrite (Z_to_le_bytes_appU 4 4 v : Z_to_le_bytes 8 v = _).
  f_equal. f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z. rewrite Z.div_small by lia. reflexivity.
Qed.
#[using="HC FI U ulen lo ustr slack ULR UFS"] Lemma rw_cells_C8_C4C4U : forall m A pre v post, rw_cells asegs m A (pre ++ C8 (Z_to_bv 64 v) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells asegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros m A pre v post [[W B] WR] Hv. split; [split|].
  - rewrite cells_wf_app in *. cbn in *. LiaTuning.ctauto.
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite (le8_small_splitU v Hv) in B. rewrite <- !app_assoc in *. cbn [app] in *. exact B.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact WR.
Qed.
#[using="HC FI U ulen lo ustr slack ULR UFS"] Lemma rw_cells_C4C4_C8U : forall m A pre v post, rw_cells asegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells asegs m A (pre ++ C8 (Z_to_bv 64 v) :: post).
Proof.
  intros m A pre v post [[W B] WR] Hv. split; [split|].
  - rewrite cells_wf_app in *. cbn in *. LiaTuning.ctauto.
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite (le8_small_splitU v Hv). rewrite <- !app_assoc in *. cbn [app] in *. exact B.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *.
    replace (cells_size pre + (8 + cells_size post))%nat with (cells_size pre + (4 + (4 + cells_size post)))%nat by lia. exact WR.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma tailU : forall (bp : Z) q' m w v0 v8 v16 v24 v32 v48 v56 wb junk
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x23 x28 x29 x30 x31,
  minvU q' m w v0 v8 v16 v24 v32 (Z_to_bv 64 1) v48 v56 wb -> pinvU m junk -> 0 <= bp <= ulen ->
  evt asegs (postU XOK)
    (USTP 0x8d7d8 q' x1 x5 x6 x7 (Z_to_bv 64 (U + bp)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) x23 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 bp) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP.
  pose proof INV as INV'.
  destruct INV' as ((kq' & Hq32) & Hq & ST & (j64 & QC) & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  zstep. zstep. zstep. zstep.
  ub_ptr. step. lit_branch_safe.
  step.   rewrite ?(unsigned_lit ulen), ?(unsigned_lit bp) by lia.
  step. step.
  step.
  apply (puricO 32 bp 0x8d7fc q' m w v0 v8 v16 v24 v32 (Z_to_bv 64 1) v48 v56 wb junk); [exact INV| exact PINV| left; reflexivity| exact BP| apply ret_pc_even; [lia| reflexivity]|].
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
    apply (tail2U bp i q' m' w v0 v8 v16 v24 v32 v48 v56 wb junk'); [exact INV| split; [exact OUT'| exact PR]| lia| lia| lia]. }
  rewrite ?(unsigned_lit i) in K1 by lia.
  step. step.
  chk8N 11 (O + 32) SHWO'. step. lit_branch.
  step.
  ub_null.
  destruct (nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat bp)) as [b|] eqn:Hb.
  2:{ exfalso. apply nth_error_None in Hb. rewrite length_app in Hb. cbn [length] in Hb. lia. }
  pose proof (u8ro_read asegs m' U _ bp b (Z_to_bv 64 (U + bp)) TXT Hb ltac:(lia) eq_refl) as RD.
  step. step.

  gen2 CONT 0x8d840 12%nat 13%nat.
  { intros yi yj.
    step.   step.
    step.   if_cases K2; zify_cond K2.
    { destruct (out_close m' 32 16 _ _ _ O1 eq_refl O2 eq_refl O3 eq_refl ltac:(lia)) as [junk' OUT'].
      apply (tail2U bp i q' m' w v0 v8 v16 v24 v32 v48 v56 wb junk'); [exact INV| split; [exact OUT'| exact PR]| lia| lia| lia]. }
    step. step. step.
    chk8N 12 (O + 24) SHWO'. step. lit_branch.

    splitcb O1 0%nat [24; 4; 4]%nat. recell O1 1%nat. name_junk O1.
    destruct INV as ((kq2 & Hq32b) & Hq2 & ST & (j64b & QC) & WBC & GAP & FRhi & FH & (j216 & FT) & SHF & FLG & MI2 & MU2 & WM2 & FK2 & AE2 & (stc & RF & LIVE1)).
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
      apply (tail2U bp i q' mm w v0 v8 v16 v24 v32 v48 v56 wb junk'); [mv_tacU| split; [exact OUT'| pr_tacU]| lia| lia| lia] end. }
  chkbN 12 (U + bp) SHWT kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="IC SET_SHADOW_F5 kq kO CLO LO AL16 RF0 Q47 OAL OLO OHI OLB SHWO ULEN ULR PAD UIMG UHI UFS UBAND SHWU SHWMARK SHWRESV"] Lemma nohpU : forall (bp : Z) q' m w v0 v8 v16 v24 v32 v48 v56 wb junk
    x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31,
  minvU q' m w v0 v8 v16 v24 v32 (Z_to_bv 64 1) v48 v56 wb -> pinvU m junk -> 0 <= bp <= ulen ->
  evt asegs (postU XOK)
    (USTP 0x8d7b8 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 F) x21 (Z_to_bv 64 F) (Z_to_bv 64 1) (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 bp) x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PINV BP.
  step. step. step.
  step.
  apply (memsetO 64 152 0x8d7c8 q' m w v0 v8 v16 v24 v32 (Z_to_bv 64 1) v48 v56 wb junk); [exact INV| exact PINV| lia| lia| apply ret_pc_even; [lia| reflexivity]|].
  intros m' junk' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 INV2 PINV2.
  step.   rewrite (unsigned_lit bp) by lia. rewrite Z.add_0_r. rewrite swrap32_id by lia.
  step.
  zstep. ub_b2z. step. lit_branch_safe.
  apply (tailU bp q' m' w v0 v8 v16 v24 v32 v48 v56 wb junk'); [exact INV2| exact PINV2| exact BP].
Qed.

End W.
