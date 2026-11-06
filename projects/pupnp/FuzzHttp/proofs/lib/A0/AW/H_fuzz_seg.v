(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpRepA AWKit AWAuto AWAuto2 FakeKit HObjK HObjF H2Kit H_parser_init.
Import ListNotations.
Open Scope Z_scope.

Definition fuzz_entryF : Z := 0x86514.
Notation FUZZ_DEPTH_A := 65536%Z.

Definition fuzzF {HC : HasCeiling} (FI : fs_if) (st : fsstate FI) : Z := fs_F FI st 4.
Definition fuzzFL {HC : HasCeiling} (FI : fs_if) (st : fsstate FI) : Z := fs_FL FI st 4.
Definition fuzzSF {HC : HasCeiling} (FI : fs_if) (st : fsstate FI) : Z := sh (fuzzF FI st).
Arguments fuzzF : simpl never.
Arguments fuzzFL : simpl never.
Arguments fuzzSF : simpl never.

Notation fshadow w :=
  ([C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
    C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
    C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
    C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
    C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
    C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
    C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
    C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w); C1 (Z_to_bv 8 w);
    C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
    C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
    C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
    C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
    C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis IC : icpt_contracts.
Hypothesis STACK_MALLOC_4 : stack_malloc_stmt FI 4.
Hypothesis SET_SHADOW_F5 : set_shadow_f5_stmt.
Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Variables (lo q kq : Z) (st : fsstate FI).
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= q - FUZZ_DEPTH_A.
Hypothesis AL16 : q = 16 * kq.
Hypothesis QHI : q < 2^64.
Hypothesis RF0 : RFAKE FI st m0.
Hypothesis FCO : fs_call_ok FI st tp 1.
Hypothesis FE0 : FSENV FI m0.

Local Notation F := (fuzzF FI st).  Local Notation FL := (fuzzFL FI st).  Local Notation SF := (fuzzSF FI st).
Local Notation P := (fuzzF FI st + 32)%Z.
Let st1 := fs_next FI st 4.

Notation FSTP pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q') x10 x11 x12 x13 x14 x15 x16 x17
           (Z_to_bv 64 F) (Z_to_bv 64 SF) x20 x21 x22 (Z_to_bv 64 F) s8 s9 s10 s11
           x28 x29 x30 x31)
      F_ (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

Definition minvF (q' : Z) (m : mem) (w : Z) : Prop :=
  (exists k', q' = 32 * k') /\ q + -112 <= q' <= q + -96
  /\ stk asegs m lo q'
  /\ (exists j0 j8, rw_cells asegs m q' [CB 8 j0; CB 8 j8; C8 (wz F)])
  /\ stk asegs m (q' + 24) (q + -72)
  /\ rw_cells asegs m (q + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m F [C8 (wz 0x41b58ab3); C8 (wz 0x11c10); C8 (wz 0x86514); C8 (wz q')]
  /\ (exists jt, rw_cells asegs m (F + 536) [CB 480 jt; C8 (wz FL)])
  /\ rw_cells asegs m SF (fshadow w)
  /\ rw_cells asegs m FL [C1 (Z_to_bv 8 1)].

#[using="m0 RF0"] Lemma geomF : exists kF kB,
  F = 64 * kF /\ SF = 8 * kF + 2147450880 /\ FSB FI = 4096 * kB /\ sh (FSB FI) = 512 * kB + 2147450880
  /\ FSB FI + 36864 <= F /\ F + 1024 <= FSB FI + 11571200 /\ FSB FI + 4096 <= FL /\ FL + 1 <= FSB FI + 36864
  /\ 6328320 <= FSB FI /\ FSB FI + 11571200 <= alloc_ceiling
  /\ (FSB FI + 11571200 <= 2147446784 \/ 17594333495296 <= FSB FI).
Proof.
  destruct (new_frame_facts FI st 4 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  cbn [FB_of SB_of] in FHI.
  pose proof (fsb_ok FI) as (FSB1 & FSB2 & _ & FSB4 & FSB5).
  exists (F / 64), (FSB FI / 4096).
  split; [clear - FAL; Z.div_mod_to_equations; lia|].
  split; [unfold fuzzSF, sh, SHADOW_OFF; clear - FAL; Z.div_mod_to_equations; lia|].
  split; [clear - FSB4; Z.div_mod_to_equations; lia|].
  split; [unfold sh, SHADOW_OFF; clear - FSB4; Z.div_mod_to_equations; lia|].
  repeat (split; [first [assumption | lia]|]). first [assumption | lia].
Qed.

#[using="m0 RF0"] Lemma liveF : forall stc, fs_live FI stc = fs_newff FI st 4 :: fs_live FI st ->
  lb (fs_live FI stc) F 1024 /\ ls (fs_live FI stc) SF 128 /\ lf (fs_live FI stc) FL
  /\ (forall g, In g (fs_live FI st) -> In g (fs_live FI stc)).
Proof.
  intros stc LIVE1.
  destruct (new_frame_facts FI st 4 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
  assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI stc)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
  pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
  unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
  change (ff_addr (fs_newff FI st 4)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 4)) with FL in LVL. change (sh F) with SF in LVS.
  split; [exact LVF|]. split; [exact LVS|]. split; [exact LVL| exact LSUB].
Qed.

#[using="m0 RF0"] Lemma shwP_of : forall m, rw_cells asegs m SF (fshadow 0) -> shw m P 504.
Proof.
  intros m SHF. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomF as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & FSB1 & FSB2 & FSB5).
  assert (F8 : F mod 8 = 0) by (clear - EKF; Z.div_mod_to_equations; lia).
  change (fshadow 0) with (shadow_cells ([241; 241; 241; 241] ++ repeat 0 63 ++ repeat 243 9 ++ repeat 0 52)) in SHF.
  change (fuzzSF FI st) with (sh F) in SHF.
  split; [| split].
  - eapply (accessible_of_chunk m F _ P 504 SHF F8); [lia| cbn [length app repeat]; lia|].
    intros i Hi H1 H2. cbn [length app repeat] in Hi.
    assert (Ei : (4 <= i < 67)%nat) by lia. clear - Ei.
    do 4 (destruct i as [|i]; [lia|]). cbn [nth app repeat].
    do 63 (destruct i as [|i]; [reflexivity|]). lia.
  - eapply (sh_readable_of_chunk m F _ P 504 SHF); cbn [length app repeat]; unfold sh, SHADOW_OFF; clear - EKF; Z.div_mod_to_equations; lia.
  - unfold win_ok. split; [lia|]. clear - GF1 GF2 FSB1 FSB2 FSB5 ACR. change (2^47) with 140737488355328. lia.
Qed.

#[using="STACK_MALLOC_4 kq CLO LO AL16 QHI RF0 FCO FE0"] Lemma prologueF : forall (D n : Z) t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
  forall (Q : machine_state -> Prop),
  (forall q' m jp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
     minvF q' m 0 -> rw_cells asegs m P [CB 504 jp] ->
     mem_inv asegs m -> asan_env asegs m -> RFAKE FI st1 m -> fs_live FI st1 = fs_newff FI st 4 :: fs_live FI st ->
     munch ((lo, q) :: FSIV [])%Z m0 m -> wmono asegs m0 m -> fkeep FI [] st m0 m ->
     evt asegs Q (FSTP 0x86710 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 2147450880) x28 x29 x30 x31 m)) ->
  evt asegs Q
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 fuzz_entryF) fc None m0 (seg_rom asegs)).
Proof.
  intros D n t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AG Q K. unfold fuzz_entryF.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
  pose proof geomF as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & FSB1 & FSB2 & FSB5).
  destruct (new_frame_facts FI st 4 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _ & _ & _ & _ & _ & APART).
  cbn [FB_of SB_of] in APART.
  pose proof (new_frame_fk FI st 4 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  pose proof (munch_refl ((lo, q) :: FSIV [])%Z m0) as MUP. pose proof (wmono_refl asegs m0) as WMP.
  pose proof (munch_refl [(lo, q)]%Z m0) as MU0. pose proof (wmono_refl asegs m0) as WM0.
  pose proof (fkeep_refl FI [] st m0) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
  pose proof RF0 as RF.
  carve_frame 96%nat ST.
  step. do 10 (step; fix_lit_store).
  step.
  step.
  rewrite (unsigned_lit (q + -96)) by lia. rewrite land_align32 by lia.
  remember (q + -96 - (q + -96) mod 32)%Z as q' eqn:Eq0.
  assert (Hq : q' = q + -96 \/ q' = q + -96 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
  assert (Hq32 : exists k', q' = 32 * k') by (exists ((q + -96) / 32); clear - Eq0; Z.div_mod_to_equations; lia).
  assert (QL : q + -112 <= q' <= q + -96) by (clear - Hq; lia).
  clear Eq0.
  lazymatch goal with FRx : rw_cells asegs ?mm (q + -96) (?c0 :: ?c1 :: ?rest) |- _ =>
    destruct (align_frame_gen mm lo (q + -96) q' [c0; c1] rest 24%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & QC) & GAP & FRhi);
    clear FRx end.
  clear Hq.
  clear ST. rename STq into ST. change (Z.of_nat 24) with 24 in GAP, FRhi. replace (q + -96 + 24) with (q + -72) in GAP, FRhi by lia.
  step.
  step.
  step. step. step. step.
  step. step.
  step.
  step.   lit_branch.
  step.
  step.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  call (STACK_MALLOC_4 st lo q' 608 F SF FL 1024 984%nat 128%nat).
  all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).
  match goal with A : asan_env asegs _ |- _ => try clear AE; rename A into AE end.
  match goal with R : RFAKE FI (fs_next FI st 4) _ |- _ => rename R into RF end.
  match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end. fold st1 in LIVE1, RF.
  match goal with K0 : fkeep FI [] st _ _ |- _ => rename K0 into FKc end.
  match goal with P0 : rw_cells asegs _ F _ |- _ => rename P0 into FRF end.
  match goal with P0 : rw_cells asegs _ SF _ |- _ => rename P0 into SHF; shadow_cells_lit SHF end.
  match goal with P0 : rw_cells asegs _ FL _ |- _ => rename P0 into FLG end.
  fs_after_call FI FK FKc LSUB LIVE1 [(lo, q); (F, F + 1024); (SF, SF + 128)]%Z.
  pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
  unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
  change (ff_addr (fs_newff FI st 4)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 4)) with FL in LVL. change (sh F) with SF in LVS.
  step. step. step.
  step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
  step; fix_lit_store.
  do 7 step.
  step; fix_lit_store. step; fix_lit_store. step; fix_lit_store.
  step. step.
  replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
    by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; reflexivity).

  lazymatch type of MUP with ?T => change (hid2 T) in MUP end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(SF, SF + 128)]%Z mm) as MUs; pose proof (wmono_refl asegs mm) as WMs end.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 4 sstep.
  step.
  do 12 sstep.
  do 60 sstep.
  unhide_transport MUs WMs.
  assert (SUBP : sub_fp [(SF, SF + 128)]%Z ((lo, q) :: FSIV [])%Z).
  { intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia| exact I]. }
  unfold hid2 in MUP.
  lazymatch type of MUs with munch _ ?ma ?mf => pose proof (munch_absorb _ _ m0 ma mf MUP MUs SUBP) as MUP' end.
  clear MUP. rename MUP' into MUP. clear MUs WMs SUBP.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  splitcb QC 0%nat [8; 8]%nat. name_junk QC.
  splitcb FRF 4%nat [504; 480]%nat. name_junk FRF.
  split_chunk FRF 4%nat FH R1. split_chunk R1 1%nat PCH FT.
  change (Z.of_nat 32) with 32 in PCH.
  destruct Hq32 as (kq' & Hq32).
  eapply K; [| exact PCH| assumption| exact AE| exact RF| exact LIVE1| exact MUP| exact WMP| exact FK].
  unfold minvF. split; [eexists; eassumption|]. split; [assumption|].
  repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]). eassumption.
Qed.

Definition WEF : list ivl := [(lo, q); (F, F + 1024); (SF, SF + 128); (FL, FL + 1)]%Z.
Definition postF (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch WEF m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'.

#[using="SET_SHADOW_F5 kq m0 CLO LO AL16 QHI RF0"] Lemma exitF : forall q' m w jp (stc : fsstate FI) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
  minvF q' m w -> rw_cells asegs m P [CB 504 jp] ->
  mem_inv asegs m -> asan_env asegs m -> RFAKE FI stc m -> fs_live FI stc = fs_newff FI st 4 :: fs_live FI st ->
  evt asegs (postF m) (FSTP 0x8676c q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 m).
Proof.
  intros until x31. intros INV PCH MI AE RF LIVE1.
  destruct INV as ((kq' & Hq32) & Hq & ST & (j0 & j8 & QC) & GAP & FRhi & FH & (jt & FT) & SHF & FLG).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomF as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & FSB1 & FSB2 & FSB5).
  destruct (new_frame_facts FI st 4 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & _).
  pose proof (new_frame_fk FI st 4 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveF stc LIVE1) as (LVF & LVS & LVL & LSUB).
  pose proof (munch_refl WEF m) as MUE. pose proof (wmono_refl asegs m) as WME. unfold WEF in MUE.
  step.

  lazymatch type of MUE with ?T => change (hid2 T) in MUE end.
  pose proof (munch_refl [(SF, SF + 128)]%Z m) as MUs. pose proof (wmono_refl asegs m) as WMs.
  hide_mem_except SHF. unhide MUs. unhide WMs.
  do 63 sstep.
  unhide_transport MUs WMs.
  assert (SUBE : sub_fp [(SF, SF + 128)]%Z WEF).
  { intros xo Ho. unfold WEF in Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [exact H3| exact I]. }
  assert (SUB0 : sub_fp [(SF, SF + 128)]%Z [(lo, q); (F, F + 1024); (SF, SF + 128)]%Z).
  { intros xo Ho. cbn [outside] in *. destruct Ho as (_ & _ & H3 & _). split; [exact H3| exact I]. }
  unfold hid2 in MUE.
  lazymatch type of MUs with munch _ ?ma ?mf =>
    pose proof (munch_absorb _ _ m ma mf MUE MUs SUBE) as MUE';
    pose proof (munch_absorb _ _ m ma mf (munch_refl [(lo, q); (F, F + 1024); (SF, SF + 128)]%Z m) MUs SUB0) as MU0 end.
  clear MUE. rename MUE' into MUE. pose proof WMs as WM0. clear MUs WMs SUBE SUB0. unfold WEF in MUE.
  step. step. step; fix_lit_store.
  step.   if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0.
  step. step.
  step.
  env_sync AE MU0 WM0. rf_sync FI RF MU0 WM0.
  eapply evt_cut.
  { eapply (SET_SHADOW_F5 SF 128 lo q'); [exact SHF| reflexivity| lia| clear - ESF EKF GF1 FSB1; lia| clear - ESF EKF GF2 FSB2 ACR; lia| exact AE| exact ST| exact CLO| unfold A0_RT_STACK; lia| lia| exact MI| reflexivity| reflexivity]. }
  intros ms' PO. unfold set_shadow_f5_post in PO.
  destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & -> & MUc & WMc & MI' & SHF' & ST' & AE').
  unfold shadow_cells in SHF'. cbv [repeat map Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in SHF'.
  pose proof MUc as MUt. pose proof WMc as WMt.
  rf_sync FI RF MUc WMc.
  clear SHF ST AE MI.
  transport_after_call asegs m2 m' MUt WMt. clear MUt WMt.
  replace (ret_pc (Z_to_bv 64 551048)) with (Z_to_bv 64 551048) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  sstep.
  env_sync AE' MU0 WM0.

  join_chunks PCH FT R1. join_chunks FH R1 FRF.
  lazymatch type of RF with RFAKE _ ?st2 ?mb2 =>
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (SHF2 : rw_cells asegs mc (sh (ff_addr (fs_newff FI st 4))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 4))))))
      by (change (ff_addr (fs_newff FI st 4)) with F; change (sh F) with SF; unfold ff_shsize; rewrite FCLS; exact SHF');
    destruct (release FI st2 (fs_newff FI st 4) (fs_live FI st) mb2 mc _ RF LIVE1 MU0 WM0 FLG SHF2 FRF
                ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3]
  end end.
  clear RF MU0 WM0 SHF2.
  step.   step.   step.
  do 9 step.
  step.   step.

  release_frame QC ST' (q' + 24)%Z.
  pose proof (stk_merge asegs _ _ _ _ ST' GAP ltac:(lia)) as STm. clear ST' GAP.
  release_frame FRhi STm q.
  apply evt_done. unfold postF. do 14 eexists.
  lazymatch goal with |- exists _ _, MS _ _ _ _ _ ?mm _ = _ /\ _ => exists mm, (fs_after_release FI stc) end.
  split; [reflexivity|]. split; [exact MUE|]. split; [exact WME|]. split; [assumption|]. split; [exact LIVE3|]. split; [exact RF3|].
  split; [exact STm| assumption].
Qed.

#[using="m0 RF0"] Lemma sub_fp_WEF : sub_fp WEF ((lo, q) :: FSIV [])%Z.
Proof.
  pose proof geomF as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & FSB1 & FSB2 & FSB5).
  intros xo Ho. unfold WEF. cbn [outside] in *. destruct Ho as (H1 & H2 & H3 & _).
  split; [exact H1|]. split; [clear - H2 GF1 GF2; lia|]. split; [clear - H3 ESF ESHB EKF EKB GF1 GF2; lia|]. split; [clear - H2 GF4 GF5; lia| exact I].
Qed.
#[using="m0 CLO RF0"] Lemma fkeep_WEF : forall m m', munch WEF m m' -> fkeep FI [] st m m'.
Proof.
  intros m m' MU.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomF as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 4 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  eapply (fkeep_of_munch FI [] WEF st st m m0 m' RF0 (fun g H => H) MU). unfold WEF. fk_forall.
Qed.

Definition postF0 : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((lo, q) :: FSIV [])%Z m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
    /\ fkeep FI [] st m0 m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'.

#[using="STACK_MALLOC_4 SET_SHADOW_F5 kq CLO LO AL16 QHI RF0 FCO FE0 st1"] Lemma frontF0 : forall (D : Z) t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
  evt asegs postF0
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 fuzz_entryF) fc None m0 (seg_rom asegs)).
Proof.
  intros D t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE.
  eapply (prologueF D 0); [exact ST| exact MI| exact AE|].
  intros q' m jp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV PCH MI1 AE1 RF1 LIVE1 MUP WMP FK.
  step.   lit_branch.
  eapply evt_mono; [eapply (exitF q' m 0 jp st1); eassumption|].
  intros ms' PO. unfold postF in PO.
  destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m' & st' & -> & MUE & WME & MI' & LIVE' & RF' & ST' & AE').
  unfold postF0. exists y0, y1, y2, b1, b2, b3, b4, b5, b6, b7, y3, y4, y5, y6, m', st'.
  split; [reflexivity|]. split; [exact (munch_absorb _ _ m0 m m' MUP MUE sub_fp_WEF)|]. split; [exact (wmono_trans asegs _ _ _ WMP WME)|].
  split; [exact MI'|]. split; [exact (fkeep_trans FI [] st m0 m m' FK (fkeep_WEF m m' MUE))|]. split; [exact LIVE'|]. split; [exact RF'|].
  split; [exact ST'| exact AE'].
Qed.

Definition initvF (b0 : byte) : Z * Z * Z := if Z.land (bv_unsigned b0) 1 =? 0 then (1, 0, 0) else (0, 2, 1).
Definition postF1 (D n : Z) (b0 : byte) : machine_state -> Prop :=
  fun ms' => exists q' m t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR (Z_to_bv 64 0x86764) (Z_to_bv 64 q') gp tp t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 q')
                  (Z_to_bv 64 P) (Z_to_bv 64 (D + 1)) (Z_to_bv 64 (n - 1)) a3 a4 a5 a6 a7
                  (Z_to_bv 64 F) (Z_to_bv 64 SF) (Z_to_bv 64 (n - 1)) (Z_to_bv 64 (D + 1)) (Z_to_bv 64 P) (Z_to_bv 64 F) s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (Z_to_bv 64 0x8b2d4) fc None m (seg_rom asegs)
    /\ minvF q' m 0
    /\ parser_init_cells_A m P (fst (fst (initvF b0))) (snd (fst (initvF b0))) (snd (initvF b0))
    /\ shw m P 504
    /\ mem_inv asegs m /\ asan_env asegs m /\ RFAKE FI st1 m /\ fs_live FI st1 = fs_newff FI st 4 :: fs_live FI st
    /\ munch ((lo, q) :: FSIV [])%Z m0 m /\ wmono asegs m0 m /\ fkeep FI [] st m0 m.

#[using="IC STACK_MALLOC_4 kq CLO LO AL16 QHI RF0 FCO FE0"] Lemma frontF1 : forall (D n : Z) (b0 : byte) t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 ->
  1 <= n < 2^63 -> shw m0 D n -> bytes_at asegs m0 D [b0] ->
  0x609000 <= D -> D + n <= alloc_ceiling -> (D + n <= FSB FI \/ FSB FI + A0_FS_SIZE <= D) ->
  evt asegs (postF1 D n b0)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (Z_to_bv 64 fuzz_entryF) fc None m0 (seg_rom asegs)).
Proof.
  intros D n b0 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AE NR SHWD BD DLO DHI DFS.
  eapply (prologueF D n); [exact ST| exact MI| exact AE|].
  intros q' m jp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV PCH MI1 AE1 RF1 LIVE1 MUP WMP FK.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof geomF as (kF & kB & EKF & ESF & EKB & ESHB & GF1 & GF2 & GF4 & GF5 & FSB1 & FSB2 & FSB5).
  pose proof (new_frame_fk FI st 4 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
  destruct (liveF st1 LIVE1) as (LVF & LVS & LVL & LSUB).

  assert (FSW : Forall (fsw_iv FI) ((lo, q) :: FSIV [])%Z).
  { apply Forall_cons; [left; apply app_iv_high; lia|]. apply Forall_cons; [left; apply (fsb_app_iv FI)|].
    apply Forall_cons; [right; cbn [fst snd]; lia| apply Forall_nil]. }
  pose proof (shw_frame_fs FI _ m0 m D n SHWD MUP FSW DFS) as SHWDn.
  assert (BDn : bytes_at asegs m D [b0]).
  { apply (bytes_at_transport asegs _ m0 m D [b0] BD MUP). cbn [disjoint_from length Z.of_nat Pos.of_succ_nat].
    pose proof (shw_win_ok _ _ _ SHWD) as WK. unfold win_ok in WK.
    split; [lia|]. split; [lia|]. split; [| exact I]. clear - WK ESHB EKB NR DLO FSB1 FSB2 ACR. change (Z.of_nat 1) with 1. lia. }
  pose proof (shwP_of m ltac:(destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & SHF & _); exact SHF)) as SHWPn.
  destruct INV as ((kq' & Hq32) & Hq & ST1 & (j0 & j8 & QC) & GAP & FRhi & FH & (jt & FT) & SHF & FLG).
  step.   if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
  step. step.
  gen2 CONT 0x86724 10%nat 11%nat.
  { intros yi yj.
    pose proof (bytes_at_ov_read asegs m D [b0] 0 1 BDn ltac:(cbn; lia)) as RD0.
    change (Z.of_nat 0) with 0 in RD0. rewrite Z.add_0_r in RD0. cbn [firstn skipn] in RD0. unfold wa in RD0.
    step.
    clear RD0. zstep. zstep. zstep. zstep.
    step.   if_cases KB; zify_cond KB.
    -
      step. step. step.
      eapply evt_cut.
      { eapply (parser_response_init_spec_A IC P 2 lo jp); [exact ST1| exact CLO| unfold A0_RT_STACK; lia| lia| exact MI1| exact AE1| exact PCH| lia| lia| clear - EKF; Z.div_mod_to_equations; lia| exact SHWPn| lia]. }
      intros ms' PO.
      destruct PO as (y0 & y1 & y2 & b0' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m' & -> & MUc & WMc & MI' & ST' & AE' & CELLS).
      pose proof MUc as MUt. pose proof WMc as WMt.
      assert (SUBC : sub_fp [(lo, q'); (P, P + 504)]%Z ((lo, q) :: FSIV [])%Z).
      { intros xo Ho. cbn [outside] in *. destruct Ho as (H1 & H2 & _). split; [clear - H1 Hq; lia|]. split; [clear - H2 GF1 GF2; lia| exact I]. }
      pose proof (munch_absorb _ _ m0 m m' MUP MUc SUBC) as MUP'. pose proof (wmono_trans asegs _ _ _ WMP WMc) as WMP'. clear MUP WMP SUBC.
      fs_sync FI RF1 MUc WMc FK LSUB.
      clear ST1 AE1 MI1 PCH SHWPn SHWDn BDn.
      transport_after_call asegs m m' MUt WMt. clear MUt WMt.
      replace (ret_pc (Z_to_bv 64 550740)) with (Z_to_bv 64 550740) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step. step. step. step.
      replace (n + -1) with (n - 1) by lia.
      apply evt_done. unfold postF1. exists q', m'. do 12 eexists.
      split; [reflexivity|].
      split; [unfold minvF; split; [eexists; exact Hq32|]; split; [exact Hq|];
              repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eassumption|].
      split; [unfold initvF; destruct (Z.eqb_spec (Z.land (bv_unsigned b0) 1) 0) as [E0|E0]; [exfalso; exact (KB E0)| exact CELLS]|].
      split; [exact (shwP_of m' SHF)|].
      split; [exact MI'|]. split; [exact AE'|]. split; [exact RF1|]. split; [exact LIVE1|]. split; [exact MUP'|]. split; [exact WMP'| exact FK].
    -
      step. step.
      eapply evt_cut.
      { eapply (parser_request_init_spec_A IC P lo jp); [exact ST1| exact CLO| unfold A0_RT_STACK; lia| lia| exact MI1| exact AE1| exact PCH| lia| lia| clear - EKF; Z.div_mod_to_equations; lia| exact SHWPn]. }
      intros ms' PO.
      destruct PO as (y0 & y1 & y2 & b0' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & m' & -> & MUc & WMc & MI' & ST' & AE' & CELLS).
      pose proof MUc as MUt. pose proof WMc as WMt.
      assert (SUBC : sub_fp [(lo, q'); (P, P + 504)]%Z ((lo, q) :: FSIV [])%Z).
      { intros xo Ho. cbn [outside] in *. destruct Ho as (H1 & H2 & _). split; [clear - H1 Hq; lia|]. split; [clear - H2 GF1 GF2; lia| exact I]. }
      pose proof (munch_absorb _ _ m0 m m' MUP MUc SUBC) as MUP'. pose proof (wmono_trans asegs _ _ _ WMP WMc) as WMP'. clear MUP WMP SUBC.
      fs_sync FI RF1 MUc WMc FK LSUB.
      clear ST1 AE1 MI1 PCH SHWPn SHWDn BDn.
      transport_after_call asegs m m' MUt WMt. clear MUt WMt.
      replace (ret_pc (Z_to_bv 64 550724)) with (Z_to_bv 64 550724) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      step.
      step. step. step. step.
      replace (n + -1) with (n - 1) by lia.
      apply evt_done. unfold postF1. exists q', m'. do 12 eexists.
      split; [reflexivity|].
      split; [unfold minvF; split; [eexists; exact Hq32|]; split; [exact Hq|];
              repeat (split; [first [eassumption | (eexists; eassumption) | (eexists; eexists; eassumption)] |]); eassumption|].
      split; [unfold initvF; destruct (Z.eqb_spec (Z.land (bv_unsigned b0) 1) 0) as [E0|E0]; [exact CELLS| exfalso; exact (E0 KB)]|].
      split; [exact (shwP_of m' SHF)|].
      split; [exact MI'|]. split; [exact AE'|]. split; [exact RF1|]. split; [exact LIVE1|]. split; [exact MUP'|]. split; [exact WMP'| exact FK].
  }
  chkbN 10 D SHWDn kk SHRk Hk.
  destruct Hk as [-> | [G1 G2]].
  - step. step. lit_branch. apply CONT.
  - step. rewrite (sxb_small kk) by lia.
    step. if_cases G3; zify_cond G3; [| exfalso; lia].
    zstep.
    step. if_cases G4; zify_cond G4; zify_granule G4; [| exfalso; lia].
    apply CONT.
Qed.

#[using="Type"] Lemma midF : forall q' m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x28 x29 x30 x31,
  evt asegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x8676c) (Z_to_bv 64 q') gp tp x5 x6 x7 (Z_to_bv 64 q) (Z_to_bv 64 q')
                                      (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 x17
                                      (Z_to_bv 64 F) (Z_to_bv 64 SF) x20 x21 (Z_to_bv 64 P) (Z_to_bv 64 F) s8 s9 s10 s11 x28 x29 x30 x31)
                                 F_ (Z_to_bv 64 0x869cc) fc None m (seg_rom asegs))
    (FSTP 0x86764 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 (Z_to_bv 64 P) x28 x29 x30 x31 m).
Proof.
  intros. step. step. apply evt_done. reflexivity.
Qed.

End W.

