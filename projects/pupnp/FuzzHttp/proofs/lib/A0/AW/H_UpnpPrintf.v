(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import AWKit AWAuto FakeKit.
Import ListNotations.
Open Scope Z_scope.

Definition UpnpPrintf_entryA : Z := 0x8d7bc.
Notation INITWASCALLED_A := 0x5e5fc0%Z.

Section W.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_2 : stack_malloc_stmt FI 2.

Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Definition UpnpPrintf_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (st' : fsstate FI),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch ((lo, q) :: FSIV []) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ fkeep FI [] st m m' /\ fs_live FI st' = fs_live FI st /\ RFAKE FI st' m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' INITWASCALLED_A [C1 (Z_to_bv 8 0)].

#[using="STACK_MALLOC_2"] Lemma UpnpPrintf_spec_A : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (st : fsstate FI) (lo : Z),
  rw_cells asegs m INITWASCALLED_A [C1 (Z_to_bv 8 0)] ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 224 - 16 - A0_RT_STACK -> q mod 16 = 0 -> q < 2^64 ->
  mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m -> fs_call_ok FI st tp 1 ->
  FSENV FI m ->
  evt asegs (UpnpPrintf_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz UpnpPrintf_entryA) fc None m (seg_rom asegs)).
Proof.
  intros ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m st lo.
  intros IW ST CLO LO AL16 QHI MI AG RF FCO FE. unfold UpnpPrintf_entryA. unfold A0_RT_STACK in LO.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AG as AE. apply asan_env_globals in AG. ag_split AG.
  pose proof (fsb_ok FI) as (FSB1 & FSB2 & FSB3 & FSB4). unfold app_mem in FSB3.
  assert (ESHB : sh (FSB FI) = FSB FI / 8 + 2147450880) by reflexivity.
  set (F := fs_F FI st 2). set (FL := fs_FL FI st 2). set (st1 := fs_next FI st 2).
  pose (SF := sh F). assert (ESF1 : sh F = SF) by reflexivity. assert (ESF : SF = F / 8 + 2147450880) by reflexivity. clearbody SF.
  destruct (new_frame_facts FI st 2 m F SF FL RF ltac:(lia) eq_refl (eq_sym ESF1) eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
  cbn [FB_of SB_of] in FHI, APART.
  pose proof (new_frame_fk FI st 2 m F SF FL RF ltac:(lia) eq_refl (eq_sym ESF1) eq_refl) as NFK.
  pose proof (munch_refl ((lo, q) :: FSIV []) m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(lo, q)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  pose proof (fkeep_refl FI [] st m) as FK. assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st)) by (intros g Hg; exact Hg).
  carve_frame 224%nat ST.
  step. do 14 (step; fix_lit_store).
  step.
  step.
  rewrite (unsigned_lit (q + -224)) by lia. rewrite land_align32 by lia.
  remember (q + -224 - (q + -224) mod 32)%Z as q' eqn:Eq0.
  assert (Hq : q' = q + -224 \/ q' = q + -224 - 16) by (subst q'; apply align32_cases; clear - AL16; Z.div_mod_to_equations; lia).
  clear Eq0.
  lazymatch goal with FRx : rw_cells asegs ?mm (q + -224) (?c0 :: ?c1 :: ?rest) |- _ =>
    destruct (align_frame_gen mm lo (q + -224) q' [c0; c1] rest 88%nat ST ltac:(lia) FRx eq_refl ltac:(lia) Hq) as (STq & (jq & Q) & GAP & FRhi);
    clear FRx end.
  clear ST. rename STq into ST. change (Z.of_nat 88) with 88 in GAP, FRhi. replace (q + -224 + 88) with (q + -136) in GAP, FRhi by lia.
  step.
  do 5 step.
  step. step. step. step.
  step. step.
  step; fix_lit_store. step; fix_lit_store. step; fix_lit_store.
  step.   lit_branch.
  step.
  step.
  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  call (STACK_MALLOC_2 st lo q' 224 F SF FL 256 216%nat 32%nat).
  all: side (try (first [ assumption | reflexivity | (unfold A0_RT_STACK in *; lia) ])).
  match goal with A : asan_env asegs _ |- _ => clear AE; rename A into AE end.
  match goal with R : RFAKE FI _ _ |- _ => rename R into RF end.
  match goal with E : fs_live FI _ = _ :: _ |- _ => rename E into LIVE1 end. fold st1 in LIVE1, RF.
  match goal with K : fkeep FI [] st _ _ |- _ => rename K into FKc end.
  match goal with P : rw_cells asegs _ F _ |- _ => rename P into FRF end.
  match goal with P : rw_cells asegs _ SF _ |- _ => rename P into SHF; shadow_cells_lit SHF end.
  match goal with P : rw_cells asegs _ FL _ |- _ => rename P into FLG end.
  fs_after_call FI FK FKc LSUB LIVE1 [(lo, q); (F, F + 256); (SF, SF + 32)]%Z.
  pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
  unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
  change (ff_addr (fs_newff FI st 2)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 2)) with FL in LVL. rewrite ESF1 in LVS.
  step. step.
  step.   if_cases K0; zify_cond K0. 2:{ exfalso. lia. } clear K0.
  do 8 step.
  step; fix_lit_store. step; fix_lit_store. step; fix_lit_store.
  step. step.
  replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 F)) 3 + 2147450880)) with (Z_to_bv 64 SF)
    by (f_equal; rewrite unsigned_lit by lia; rewrite shiftr3_div; lia).
  do 4 sstep.
  step.
  do 12 sstep.
  step.
  do 12 sstep.
  step. step.
  step; fix_lit_store.
  step. lit_branch.

  sstep.
  step. step. step; fix_lit_store.
  step.   if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
  step.
  do 32 sstep.
  step.

  env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
  sstep.
  env_sync AE MU0 WM0. fk_sync FI RF MU0 FK LSUB.
  lazymatch type of RF with RFAKE _ ?st2 ?mb =>
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (SHF' : rw_cells asegs mc (sh (ff_addr (fs_newff FI st 2))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 2))))))
      by (change (ff_addr (fs_newff FI st 2)) with F; rewrite ESF1; unfold ff_shsize; rewrite FCLS; exact SHF);
    destruct (release FI st2 (fs_newff FI st 2) (fs_live FI st) mb mc _ RF LIVE1 MU0 WM0 FLG SHF' FRF
                ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3]
  end end.
  clear RF MU0 WM0 SHF'.
  step.   step.
  do 13 step.
  step.   step.

  match goal with P : stk asegs _ lo q' |- _ => release_frame Q P (q' + 88)%Z end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with A : stk asegs mm lo (q' + 88)%Z, B : stk asegs mm (q' + 88)%Z _ |- _ =>
      pose proof (stk_merge asegs mm _ _ _ A B ltac:(lia)) as STm; clear A B end end.
  release_frame FRhi STm q.
  unfold UpnpPrintf_post_A. finish.
  { rewrite LIVE3. reflexivity. }
  { exact RF3. }
Qed.

End W.
