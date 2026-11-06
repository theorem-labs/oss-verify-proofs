(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HttpRepA AWKit AWAuto HObjA AWUb.
Import ListNotations.
Open Scope Z_scope.

Definition FreeListAlloc_entryA : Z := 0x8c37c.
Definition FreeListFree_entryA : Z := 0x8c480.
Definition FreeListDestroy_entryA : Z := 0x8c5a4.

Definition fl_cells (flh fk : Z) : list cell := [C8 (wz flh); C8 (wz 24); C4 (wz 100); C4 (wz fk)].

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

#[using="Type"] Lemma flaseg : forall (lo FL fk : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 16 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m FL (fl_cells 0 fk) -> 0x609000 <= FL -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra (wz q) gp tp t0' t1' t2' s0 s1 (wz 24) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz A0_malloc) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m'
      /\ rw_cells asegs m' FL (fl_cells 0 fk))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FreeListAlloc_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo FL fk ra q gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 FLC FLLO FLHI AL SHWF. unfold fl_cells, FreeListAlloc_entryA in *.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 16%nat ST.
  walk_lia_to 0x8c38c%Z. ub_align.
  walk_lia_to 0x8c434%Z.
  cstep. env_now AE0 MU WM. release_to q. step.
  apply evt_done. unfold A0_malloc, fl_cells. do 15 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Definition ffseg1_post (lo FL N flh fk : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    (fk + 1 < 100 /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (j1 j2 : word) m',
       ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom asegs)
       /\ munch [(FL, FL + 24); (N, N + 24); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m'
       /\ rw_cells asegs m' FL (fl_cells N (fk + 1))
       /\ rw_cells asegs m' N [C8 (wz flh); C8 j1; C8 j2])
    \/ (100 <= fk + 1 /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j : list byte),
       ms' = MS (mkR (wz 0x8c538) (wz (q + -16)) gp tp t0 t1 t2 s0 s1 (wz N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz A0_free) fc None m' (seg_rom asegs)
       /\ munch [(FL, FL + 24); (N, N + 24); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
       /\ stk asegs m' lo (q + -16)
       /\ rw_cells asegs m' (q + -16) [CB 8 j; C8 ra]
       /\ rw_cells asegs m' FL (fl_cells flh fk)).

#[using="Type"] Lemma ffseg1 : forall (lo FL N flh fk : Z) (n1 n2 n3 : word) ra (q : Z) gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 16 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m FL (fl_cells flh fk) -> 0x609000 <= FL -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  0 <= fk <= 99 -> 0 <= flh < 2^64 ->
  rw_cells asegs m N [C8 n1; C8 n2; C8 n3] -> shw m N 24 -> 0x609000 <= N -> N + 24 <= alloc_ceiling -> N mod 8 = 0 ->
  (FL + 24 <= N \/ N + 24 <= FL) ->
  evt asegs (ffseg1_post lo FL N flh fk ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz FL) (wz N) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FreeListFree_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo FL N flh fk n1 n2 n3 ra q gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 FLC FLLO FLHI AL SHWF FK FLH NC SHWN NLO NHI NAL DJ. unfold fl_cells, FreeListFree_entryA in *.
  a0_prologue AE0 [(FL, FL + 24); (N, N + 24); (lo, q)]%Z m.
  carve_frame 16%nat ST.
  walk_lia_to 0x8c490%Z. ub_align.
  walk_lia_to 0x8c4c0%Z.
  step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
  walk_lia_to 0x8c4dc%Z.
  cstep. if_cases KF; zify_cond KF.
  all: rewrite ?signed_lit in KF by lia.
  -
    walk_lia_to 0x8c534%Z. step.
    apply evt_done. unfold ffseg1_post, fl_cells, A0_free. right. split; [lia|]. do 16 eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). assumption.
  -
    walk_lia_to 0x8c4e8%Z.
    zstep. cstep. step. ubr.
    walk_lia_to 0x8c52c%Z.
    env_now AE0 MU WM. release_to q. step.
    apply evt_done. unfold ffseg1_post, fl_cells. left. split; [lia|]. do 17 eexists. split; [reflexivity|].
    repeat (split; [eassumption|]). eassumption.
Qed.

#[using="Type"] Lemma ffseg2 : forall (lo : Z) (j : list byte) ra (q : Z) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -16) -> alloc_ceiling <= lo -> lo <= q - 16 -> q < 2^64 -> mem_inv asegs m ->
  rw_cells asegs m (q + -16) [CB 8 j; C8 ra] ->
  evt asegs (fun ms' => exists m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q)
    (MS (mkR x1 (wz (q + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c538) fc None m (seg_rom asegs)).
Proof.
  intros lo j ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m.
  intros ST CLO LO QHI MI FR.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x8c544%Z. release_to q. step.
  apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Notation FDFR m q s3 s2 s1 s0 ra := (rw_cells asegs m q [CB 8 _; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

#[using="Type"] Lemma fdsegA : forall (lo FL flh fk : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 48 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m FL (fl_cells flh fk) -> 0x609000 <= FL -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  0 <= flh < 2^64 ->
  evt asegs (fun ms' => exists (j : list byte) a1' a2' m',
      ms' = MS (mkR ra (wz (q + -48)) gp tp t0 t1 t2 (wz FL) (wz 0x7fff8000) (wz flh) a1' a2' a3 a4 a5 a6 a7
                    (wz (Z.shiftr FL 3 + 2147450880)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if flh =? 0 then 0x8c624 else 0x8c5f0)) fc None m' (seg_rom asegs)
      /\ munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (q + -48)
      /\ rw_cells asegs m' (q + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m' FL (fl_cells flh fk))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FreeListDestroy_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo FL flh fk ra q gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 FLC FLLO FLHI AL SHWF FLH. unfold fl_cells, FreeListDestroy_entryA in *.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 48%nat ST.
  walk_lia_to 0x8c5c4%Z. ub_align.
  walk_lia_to 0x8c5ec%Z.
  cstep. if_cases K; zify_cond K.
  - apply evt_done. replace (flh =? 0) with true by (symmetry; apply Z.eqb_eq; lia). unfold fl_cells.
    do 4 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
  - apply evt_done. replace (flh =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold fl_cells.
    do 4 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

#[using="Type"] Lemma fdsegB : forall (N nx : Z) (j1 j2 : word) (q : Z) ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  mem_inv asegs m -> rw_cells asegs m N [C8 (wz nx); C8 j1; C8 j2] -> shw m N 24 -> 0 < N < 2^64 -> N mod 8 = 0 ->
  s1 = wz 0x7fff8000 ->
  evt asegs (fun ms' => exists a1',
      ms' = MS (mkR (wz 0x8c610) (wz q) gp tp t0 t1 t2 s0 s1 (wz N) a1' a2 a3 a4 a5 a6 a7 s2 (wz nx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz A0_free) fc None m (seg_rom asegs))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c5f0) fc None m (seg_rom asegs)).
Proof.
  intros N nx j1 j2 q ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros MI NC SHWN NR NAL ->.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  ub_align.
  walk_lia_to 0x8c60c%Z. step.
  apply evt_done. unfold A0_free. eexists. reflexivity.
Qed.

#[using="Type"] Lemma fdsegC : forall (FL hd fk nx : Z) (q : Z) ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  mem_inv asegs m -> rw_cells asegs m FL (fl_cells hd fk) -> 0x609000 <= FL -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  0 <= nx < 2^64 ->
  evt asegs (fun ms' => exists m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 (wz FL) (wz 0x7fff8000) (wz nx) a1 a2 a3 a4 a5 a6 a7
                    (wz (Z.shiftr FL 3 + 2147450880)) (wz nx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if nx =? 0 then 0x8c624 else 0x8c5f0)) fc None m' (seg_rom asegs)
      /\ munch [(FL, FL + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' FL (fl_cells nx fk))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 (wz FL) (wz 0x7fff8000) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (Z.shiftr FL 3 + 2147450880)) (wz nx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c610) fc None m (seg_rom asegs)).
Proof.
  intros FL hd fk nx q ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros MI FLC FLLO FLHI AL SHWF NXR. unfold fl_cells in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(FL, FL + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x8c620%Z.
  cstep. if_cases K; zify_cond K.
  - apply evt_done. replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
  - apply evt_done. replace (nx =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

#[using="Type"] Lemma fdsegD : forall (lo FL hd fk : Z) (j : list byte) ra (q : Z) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x19
    (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -48) -> alloc_ceiling <= lo -> lo <= q - 48 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m (q + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m FL (fl_cells hd fk) -> 0x609000 <= FL -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  evt asegs (fun ms' => exists a1' a2' m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(FL, FL + 24); (lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m'
      /\ rw_cells asegs m' FL (fl_cells hd 0))
    (MS (mkR x1 (wz (q + -48)) gp tp t0 t1 t2 (wz FL) (wz 0x7fff8000) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (Z.shiftr FL 3 + 2147450880)) x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c624) fc None m (seg_rom asegs)).
Proof.
  intros lo FL hd fk j ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x19 F fc m.
  intros ST CLO LO QHI MI AE0 FR FLC FLLO FLHI AL SHWF. unfold fl_cells in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(FL, FL + 24); (lo, q)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x8c664%Z.
  env_now AE0 MU WM. release_to q. step.
  apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Variable FI : fs_if.
Variable AI : am_if FI.
Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
Local Notation K := (am_K FI AI).
Local Notation BLK := (block K).
Local Notation BL := (list (block K)).
Local Notation lbrm k LB := (lb_remove (am_K_eqb FI AI) k LB).
Local Notation flseg := (flseg FI AI).
Local Notation bsub := (bsub FI AI).

Definition FreeListAlloc_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB : BL) (st : fsstate FI) (FL fk lo : Z) (ras : list Z),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 16 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 < am_stack_top FI AI ->
  mem_inv asegs m ->
  fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras -> In (PC0_MALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  rw_cells asegs m FL (fl_cells 0 fk) -> 0x609000 <= FL -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  am_budget FI AI s LB 24 -> a0 = wz FL ->
  AJ FI AI J (malloc_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB 24 lo m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FreeListAlloc_entryA) fc None m (seg_rom asegs))
    s LB.

#[using="AC ASL"] Theorem FreeListAlloc_spec_A : FreeListAlloc_stmt_A.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st FL fk lo ras.
  intros HR RF AE ST CLO LO QAL QTOP MI CH TR FLC FLLO FLHI AL SHWF BUD ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LO' : lo <= q - 16 - 4096) by (unfold A0_RT_STACK in LO; exact LO).
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  eapply (aj_evt FI AI J). { eapply (flaseg lo FL fk); try eassumption; lia. }
  intros ms' (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m1 & -> & MU1 & WM1 & MI1 & ST1 & AE1 & FLC1).
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  pose proof (rheap_blk_write FI AI s LB m m1 _ HR MU1 WM1 BIV1) as HR1.
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1 ltac:(constructor; [split; [left; cbn; lia| cbn; lia]| constructor])) as RF1.
  pose proof (fpchain_frame ras m m1 _ q _ _ CH MU1 WM1 ltac:(constructor; [cbn; lia| constructor])) as CH1.
  assert (AP1 : apres FI AI LB q m m1).
  { eapply (apres_seg FI AI ASL s LB LB q _ m m m1 HR (fun b H => H) MU1 WM1). constructor; [left; cbn; lia| constructor]. }
  eapply (aj_mono FI AI J).
  { eapply (ac_malloc FI AI J AC) with (lo := lo) (n := 24) (ras := ras) (st := st);
      first [ exact HR1 | exact AE1 | exact RF1 | exact ST1 | exact CLO | exact QAL | exact QTOP | exact MI1 | exact CH1 | exact TR | exact BUD | reflexivity
            | (unfold A0_RT_STACK; lia) | (unfold A0_MAXREQ; lia) | lia ]. }
  intros s' LB' ms' P. unfold malloc_post_A in *.
  destruct P as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & k & A & junk & E & (P1 & P2 & P3 & P4 & P5) & REST1 & REST2 & REST3 & REST4 & WM2 & NS2).
  exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', k, A, junk.
  split; [exact E|]. split; [split; [exact P1| split; [exact P2| split; [exact P3| split; [exact P4| exact (apres_trans FI AI _ _ _ _ _ AP1 P5)]]]]|].
  split; [exact REST1|]. split; [exact REST2|]. split; [exact REST3|]. split; [exact REST4|]. split; [exact (wmono_trans asegs _ _ _ WM1 WM2)| exact NS2].
Qed.

Definition FreeListFree_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (ns0 : Z) (LB : BL) (k : K) (FL N lo : Z) (FB : BL) (m : mem) : aps FI AI -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (flh' fk' : Z) (FB' : BL),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ apx FI AI [(FL, FL + 24)] (lbrm k LB) q m m'
    /\ RHEAP_A FI AI s' LB' m' /\ (forall b, In b (lbrm k LB) -> In b LB')
    /\ rw_cells asegs m' FL (fl_cells flh' fk') /\ flseg m' FB' flh' /\ fk' = Z.of_nat (length FB') /\ fk' <= 99
    /\ bsub FB' LB' /\ NoDup (map blk_id FB')
    /\ ((LB' = LB /\ FB' = (k, N, 24) :: FB) \/ (LB' = lbrm k LB /\ FB' = FB))
    /\ am_nsec FI AI s' = ns0.

Definition FreeListFree_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB : BL) (st : fsstate FI) (k : K) (FL N flh fk lo : Z) (FB : BL)
         (n1 n2 n3 : word),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 16 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 < am_stack_top FI AI ->
  mem_inv asegs m ->
  ~ valid_frame (am_stack_top FI AI) (q + -16) (bv_unsigned s0) ->
  rw_cells asegs m FL (fl_cells flh fk) -> mlocNB FI AI q st FL 24 -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  flseg m FB flh -> fk = Z.of_nat (length FB) -> fk <= 99 -> bsub FB LB ->
  In (k, N, 24) LB -> rw_cells asegs m N [C8 n1; C8 n2; C8 n3] -> NoDup (map blk_id ((k, N, 24) :: FB)) ->
  a0 = wz FL -> a1 = wz N ->
  AJ FI AI J (FreeListFree_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB k FL N lo FB m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FreeListFree_entryA) fc None m (seg_rom asegs))
    s LB.

#[using="AC ASL"] Theorem FreeListFree_spec_A : FreeListFree_stmt_A.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st k FL N flh fk lo FB n1 n2 n3.
  intros HR RF AE ST CLO LO QAL QTOP MI NVF FLC FLL FLHI AL SHWF FLS FK FK99 FSUB HIN NC ND -> ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (LO' : lo <= q - 16 - 4096) by (unfold A0_RT_STACK in LO; exact LO). clear LO.
  destruct (am_block_range FI AI s LB m _ HR HIN) as (R1 & R2 & R3 & R4 & R5 & R5d & R6). cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5, R5d, R6.
  assert (SUBR : forall b, In b (lbrm k LB) -> In b LB) by (intros b Hb; eapply (lb_remove_sub FI AI); exact Hb).
  assert (SUBNE : forall b, In b (lbrm k LB) -> In b LB /\ b <> (k, N, 24)).
  { intros b Hb. split; [apply SUBR; exact Hb|]. intros ->. exact (lb_remove_neq FI AI _ _ _ Hb eq_refl). }
  pose proof (mlocNB_mblocA FI AI (lbrm k LB) q st FL 24 FLL) as FLM.
  destruct (mblocA_range FI AI s LB _ q st m FL 24 HR SUBR RF FLM ltac:(lia) ltac:(lia)) as (FLLO & _ & _).
  pose proof (mlocNB_apart FI AI s LB m st q FL 24 (k, N, 24) HR RF FLL HIN ltac:(lia) ltac:(lia)) as DJF.
  cbn [blk_addr blk_size fst snd] in DJF.
  pose proof (block_shw FI AI s LB m (k, N, 24) N 24 HR HIN ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWN.
  assert (FLH : 0 <= flh < 2^64).
  { destruct FB as [|b FB']; cbn [HObjA.flseg] in FLS. { subst flh. lia. }
    destruct FLS as (_ & Eb & _). pose proof (FSUB b (or_introl eq_refl)) as Hb. rewrite Eb in Hb.
    destruct (am_block_range FI AI s LB m _ HR Hb) as (Q1 & _ & _ & Q4 & _). cbn in Q1, Q4. lia. }

  assert (FBD : forall b, In b FB -> blk_size b = 24 /\ (N + 24 <= blk_addr b \/ blk_addr b + 24 <= N) /\ In b (lbrm k LB)
                                   /\ 0x609000 <= blk_addr b /\ blk_addr b + 24 <= alloc_ceiling
                                   /\ (FL + 24 <= blk_addr b \/ blk_addr b + 24 <= FL)).
  { intros b Hb.
    assert (NE : (k, N, 24) <> b) by (eapply (nodup_in_neq FI AI [(k, N, 24)] FB); [exact ND| left; reflexivity| exact Hb]).
    destruct (flseg_shape FI AI FB m flh b FLS Hb) as [Eb _].
    assert (SZ : blk_size b = 24) by (rewrite Eb; reflexivity).
    pose proof (FSUB b Hb) as HbL. destruct (am_block_range FI AI s LB m _ HR HbL) as (Q1 & _ & _ & Q4 & Q5 & Q5d & _). rewrite SZ in Q4.
    pose proof (mlocNB_apart FI AI s LB m st q FL 24 b HR RF FLL HbL ltac:(lia) ltac:(lia)) as DFb. rewrite SZ in DFb.
    split; [exact SZ|]. split; [| split; [| split; [exact Q5| split; [lia| exact DFb]]]].
    - pose proof (am_blocks_disjoint FI AI s LB m _ _ HR HIN HbL NE) as D. cbn in D. rewrite SZ in D. lia.
    - apply (in_lb_remove FI AI); [exact HbL|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
      intros E. apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact Hb. }
  eapply (aj_evt FI AI J). { eapply (ffseg1 lo FL N flh fk n1 n2 n3); try eassumption; try lia. all: Z.div_mod_to_equations; lia. }
  intros ms' [(LT & v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & j1 & j2 & m1 & -> & MU1 & WM1 & MI1 & ST1 & AE1 & FLC1 & NC1)
             |(GE & v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1 & FLC1)].
  -
    apply (aj_ret FI AI J). unfold FreeListFree_post_A.
    do 14 eexists. exists m1, N, (fk + 1), ((k, N, 24) :: FB). split; [reflexivity|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact AE1|].
    split. { eapply (rfake_frame FI); [exact RF| exact MU1| exact WM1|].
             constructor; [eapply (rf_ok_mbloc FI AI s LB _ q st m FL 24 HR SUBR FLM); lia|].
             constructor; [eapply (rf_ok_blk FI AI s LB m st (k, N, 24)); [exact HR| exact HIN| cbn; lia| cbn; lia| lia]|].
             constructor; [apply (rf_ok_stack FI); cbn; lia| constructor]. }
    split. { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR SUBR MU1 WM1).
             constructor; [right; right; cbn; lia|].
             constructor. { right; left. cbn [fst snd]. intros a Ha.
                            eapply (fresh_block_not_aclient FI AI ASL s LB _ (k, N, 24) q m a HR HIN SUBNE); [lia| cbn; lia]. }
             constructor; [left; cbn; lia| constructor]. }
    split. { eapply (am_heap_frame FI AI); [exact HR| exact MU1| exact WM1|].
             constructor; [eapply (mblocA_hf FI AI LB _ q st m FL 24 RF FLM ltac:(lia) SUBR)|].
             constructor; [right; right; left; exists (k, N, 24); split; [exact HIN| cbn; lia]|].
             constructor; [left; cbn; lia| constructor]. }
    split; [exact SUBR|]. split; [exact FLC1|]. split.
    { cbn [HObjA.flseg]. split; [lia|]. split; [reflexivity|]. exists flh, j1, j2. split; [exact NC1|].
      eapply (flseg_transport FI AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb. destruct (FBD b Hb) as (_ & D & _ & Q1 & Q4 & DF). cbn. lia. }
    split; [cbn [length]; lia|]. split; [lia|]. split. { intros b [<-|Hb]; [exact HIN| apply FSUB; exact Hb]. } split; [exact ND|].
    split; [left; split; reflexivity| reflexivity].
  -
    assert (W3 : Forall (fun iv : Z * Z => alloc_ceiling <= fst iv
                        \/ (exists lo hi, am_static FI AI lo hi /\ lo <= fst iv /\ snd iv <= hi /\ a0_wsafe (fst iv) (snd iv))
                        \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
                        \/ (FSB FI <= fst iv /\ snd iv <= FSB FI + A0_FS_SIZE)
                        \/ (sh (FSB FI) <= fst iv /\ snd iv <= sh (FSB FI) + A0_FS_SHSIZE)) [(FL, FL + 24); (N, N + 24); (lo, q)]).
    { constructor; [eapply (mblocA_hf FI AI LB _ q st m FL 24 RF FLM ltac:(lia) SUBR)|].
      constructor; [right; right; left; exists (k, N, 24); split; [exact HIN| cbn; lia]|].
      constructor; [left; cbn; lia| constructor]. }
    pose proof (am_heap_frame FI AI s LB m m1 _ HR MU1 WM1 W3) as HR1.
    assert (RF1 : RFAKE FI st m1).
    { eapply (rfake_frame FI); [exact RF| exact MU1| exact WM1|].
      constructor; [eapply (rf_ok_mbloc FI AI s LB _ q st m FL 24 HR SUBR FLM); lia|].
      constructor; [eapply (rf_ok_blk FI AI s LB m st (k, N, 24)); [exact HR| exact HIN| cbn; lia| cbn; lia| lia]|].
      constructor; [apply (rf_ok_stack FI); cbn; lia| constructor]. }
    assert (AE1 : asan_env asegs m1).
    { eapply asan_env_frame; [exact AE| exact MU1| exact WM1|]. unfold env_safe.
      constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
    assert (FL1 : flseg m1 FB flh).
    { eapply (flseg_transport FI AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb. destruct (FBD b Hb) as (_ & D & _ & Q1 & Q4 & DF). cbn. lia. }
    assert (HP1 : apx FI AI [(FL, FL + 24)] (lbrm k LB) q m m1).
    { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR SUBR MU1 WM1).
      constructor; [right; right; cbn; lia|].
      constructor. { right; left. cbn [fst snd]. intros a Ha.
                     eapply (fresh_block_not_aclient FI AI ASL s LB _ (k, N, 24) q m a HR HIN SUBNE); [lia| cbn; lia]. }
      constructor; [left; cbn; lia| constructor]. }
    eapply (aj_bind FI AI J).
    { eapply (ac_free FI AI J AC) with (lo := lo) (k := k) (A := N) (n := 24) (ras := []) (st := st).
      - exact HR1.
      - exact HIN.
      - exact AE1.
      - exact RF1.
      - exact ST1.
      - exact CLO.
      - unfold A0_RT_STACK. clear - LO'. lia.
      - clear - QAL. Z.div_mod_to_equations. lia.
      - clear - QTOP. lia.
      - exact MI1.
      - cbn [fpchain]. exact NVF.
      - rewrite unsigned_lit by (clear; lia). unfold A0_TRACES. repeat first [left; reflexivity | right].
      - reflexivity. }
    intros s' LB' ms'' POST. unfold free_post_A in POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & AFR & -> & HR2 & NS2).
    destruct AFR as (MI2 & ST2 & AE2 & RF2 & AP2).
    replace (ret_pc (Z_to_bv 64 574776)) with (Z_to_bv 64 574776) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (apres_rw_cells FI AI _ _ _ _ _ _ AP2 FR1 ltac:(apply aclient_range_above; cbn; lia)) as FR2.
    assert (FLM2 : mblocA FI AI (lbrm k LB) (q + -16) st FL 24) by (eapply (mblocA_weaken FI AI); [exact FLM| lia| auto| auto]).
    assert (FLC2 : rw_cells asegs m2 FL (fl_cells flh fk)).
    { eapply (apres_rw_cells FI AI); [exact AP2| exact FLC1|]. unfold fl_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      eapply (mblocA_client FI AI); [exact RF1| exact FLM2]. }
    assert (FL2 : flseg m2 FB flh).
    { clear - FL1 AP2 FBD. revert flh FL1. induction FB as [|b FB IH]; intros flh FL1; cbn [HObjA.flseg] in *; [exact FL1|].
      destruct FL1 as (NZ & Eb & nx & j1 & j2 & NCb & FLS'). split; [exact NZ|]. split; [exact Eb|]. exists nx, j1, j2. split.
      - eapply (apres_rw_cells FI AI); [exact AP2| exact NCb|]. destruct (FBD b (or_introl eq_refl)) as (_ & _ & Hb & _).
        eapply (aclient_range_block FI AI); [exact Hb| rewrite Eb; cbn; lia| rewrite Eb; cbn; lia].
      - apply IH; [| exact FLS']. intros b0 Hb0. apply FBD. right. exact Hb0. }
    eapply (aj_evt FI AI J). { eapply (ffseg2 lo j); try eassumption; lia. }
    intros ms' (m3 & -> & MU3 & WM3 & MI3 & ST3).
    assert (BIV3 : Forall (blk_iv FI AI (lbrm k LB)) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
    apply (aj_ret FI AI J). unfold FreeListFree_post_A.
    do 14 eexists. exists m3, flh, fk, FB. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|].
    split. { eapply asan_env_frame; [exact AE2| exact MU3| exact WM3|]. unfold env_safe. constructor; [left; cbn; lia| constructor]. }
    split. { eapply (rfake_blk_write FI AI s' _ st m2 m3 _ HR2 RF2 MU3 WM3). constructor; [split; [left; cbn; lia| cbn; lia]| constructor]. }
    split. { eapply (apx_trans FI AI); [exact HP1|]. eapply (apx_trans FI AI).
             - apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP2| lia| auto].
             - eapply (apx_seg FI AI ASL s' _ _ q _ _ m2 m2 m3 HR2 (fun b H => H) MU3 WM3). constructor; [left; cbn; lia| constructor]. }
    split; [exact (rheap_blk_write FI AI s' _ m2 m3 _ HR2 MU3 WM3 BIV3)|].
    split; [auto|].
    split. { eapply rw_cells_transport; [exact FLC2| exact MU3| exact WM3| unfold fl_cells; cbn [disjoint_from cells_size csize Nat.add]; lia]. }
    split. { eapply (flseg_transport FI AI); [exact FL2| exact MU3| exact WM3|]. intros b Hb. destruct (FBD b Hb) as (_ & D & _ & Q1 & Q4 & DF). cbn. lia. }
    split; [exact FK|]. split; [lia|].
    split. { intros b Hb. destruct (FBD b Hb) as (_ & _ & X & _). exact X. } split. { cbn in ND. inversion ND; assumption. }
    split; [right; split; reflexivity| exact NS2].
Qed.

Definition FreeListDestroy_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (ns0 : Z) (LB0 LBK : BL) (FL lo : Z) (m : mem) (OWNED : BL) : aps FI AI -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ apx FI AI [(FL, FL + 24)] LBK q m m'
    /\ RHEAP_A FI AI s' LB' m' /\ bsub LBK LB' /\ (forall b, In b LB' -> In b LB0)
    /\ (forall b, In b OWNED -> ~ In b LB')
    /\ rw_cells asegs m' FL (fl_cells 0 0)
    /\ am_nsec FI AI s' = ns0.

#[using="Type"] Lemma flseg_apres : forall FB N (LBK : BL) q m m',
  flseg m FB N -> apres FI AI LBK q m m' -> (forall b, In b FB -> In b LBK) -> flseg m' FB N.
Proof.
  induction FB as [|b FB IH]; intros N LBK q m m' FLS HP SUB; cbn [HObjA.flseg] in *; [exact FLS|].
  destruct FLS as (NZ & Eb & nx & j1 & j2 & NC & FLS'). split; [exact NZ|]. split; [exact Eb|]. exists nx, j1, j2. split.
  - eapply (apres_rw_cells FI AI); [exact HP| exact NC|].
    eapply (aclient_range_block FI AI); [apply SUB; left; reflexivity| rewrite Eb; cbn; lia| rewrite Eb; cbn; lia].
  - eapply IH; [exact FLS'| exact HP|]. intros b0 Hb0. apply SUB. right. exact Hb0.
Qed.

#[using="AC ASL AMS"] Lemma fld_loop : forall (FB : BL) (N : Z) (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x19 : word)
    (F : bvmap 5 word) fc (m0 m : mem) (s : aps FI AI) (LB LB0 LBK : BL) (st : fsstate FI) (FL fk lo : Z) (j : list byte) (ns0 : Z) (OWNED : BL),
  flseg m FB N -> N <> 0 -> bsub FB LB -> bsub LBK LB -> NoDup (map blk_id (FB ++ LBK)) -> (forall b, In b LB -> In b LB0) ->
  (forall b0, In b0 OWNED -> In b0 FB \/ ~ In b0 LB) ->
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
  stk asegs m lo (q + -48) -> alloc_ceiling <= lo -> lo <= q - 48 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  rw_cells asegs m (q + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs m FL (fl_cells N fk) -> mlocNB FI AI q st FL 24 -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  apx FI AI [(FL, FL + 24)] LBK q m0 m -> am_nsec FI AI s = ns0 ->
  AJ FI AI J (FreeListDestroy_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st ns0 LB0 LBK FL lo m0 OWNED)
    (MS (mkR x1 (wz (q + -48)) gp (wz A0_TP) t0 t1 t2 (wz FL) (wz 0x7fff8000) (wz N) a1 a2 a3 a4 a5 a6 a7
             (wz (Z.shiftr FL 3 + 2147450880)) x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x8c5f0) fc None m (seg_rom asegs)) s LB.
Proof.
  induction FB as [|b FB IH]; intros N ra q gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x19 F fc m0 m s LB LB0 LBK st FL fk lo j ns0 OWNED;
    intros FLS NZ FSUB KSUB ND SUB0 GONE HR RF AE ST CLO LO QAL QTOP MI FR FLC FLL FLHI AL SHWF HP0 NS0.
  { cbn [HObjA.flseg] in FLS. exfalso. exact (NZ FLS). }
  cbn [HObjA.flseg] in FLS. destruct FLS as (_ & Eb & nx & j1 & j2 & NC & FLS').
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (LO' : lo <= q - 48 - 4096) by (unfold A0_RT_STACK in LO; exact LO).
  pose proof (FSUB b (or_introl eq_refl)) as HIN. rewrite Eb in HIN.
  destruct (am_block_range FI AI s LB m _ HR HIN) as (R1 & R2 & R3 & R4 & R5 & R5d & R6). cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5, R5d, R6.
  pose proof (block_shw FI AI s LB m _ N 24 HR HIN ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia)) as SHWN.
  pose proof (mlocNB_mblocA FI AI LB q st FL 24 FLL) as FLM.
  destruct (mblocA_range FI AI s LB _ q st m FL 24 HR (fun b H => H) RF FLM ltac:(lia) ltac:(lia)) as (FLLO & _ & _).
  assert (NXR : 0 <= nx < 2^64).
  { destruct FB as [|b' FB']; cbn [HObjA.flseg] in FLS'. { subst nx. lia. }
    destruct FLS' as (_ & Eb' & _). pose proof (FSUB b' (or_intror (or_introl eq_refl))) as Hb'. rewrite Eb' in Hb'.
    destruct (am_block_range FI AI s LB m _ HR Hb') as (Q1 & _ & _ & Q4 & _). cbn in Q1, Q4. lia. }

  assert (KEEP : forall b0, In b0 (FB ++ LBK) -> In b0 (lbrm (blk_id b) LB)).
  { intros b0 Hb0. apply (in_lb_remove FI AI).
    - apply in_app_or in Hb0. destruct Hb0 as [H|H]; [apply FSUB; right; exact H| apply KSUB; exact H].
    - cbn in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact Hb0. }
  eapply (aj_evt FI AI J). { eapply (fdsegB N nx j1 j2 (q + -48)); try eassumption; try reflexivity; try lia. }
  intros ms' (c1 & ->).
  eapply (aj_bind FI AI J).
  { eapply (ac_free FI AI J AC) with (lo := lo) (k := blk_id b) (A := N) (n := 24) (ras := []) (st := st).
    - exact HR.
    - exact HIN.
    - exact AE.
    - exact RF.
    - exact ST.
    - exact CLO.
    - unfold A0_RT_STACK. clear - LO'. lia.
    - clear - QAL. Z.div_mod_to_equations. lia.
    - clear - QTOP. lia.
    - exact MI.
    - cbn [fpchain]. unfold valid_frame. rewrite unsigned_lit by (clear - FLLO FLHI ACR; lia). clear - FLHI CLO LO'. lia.
    - rewrite unsigned_lit by (clear; lia). unfold A0_TRACES. repeat first [left; reflexivity | right].
    - reflexivity. }
  intros s' LB' ms'' POST. unfold free_post_A in POST.
  destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & AFR & -> & HR2 & NS2).
  destruct AFR as (MI2 & ST2 & AE2 & RF2 & AP2).
  replace (ret_pc (Z_to_bv 64 574992)) with (Z_to_bv 64 574992) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof (apres_rw_cells FI AI _ _ _ _ _ _ AP2 FR ltac:(apply aclient_range_above; cbn; lia)) as FR2.
  assert (FLM2 : mblocA FI AI (lbrm (blk_id b) LB) (q + -48) st FL 24) by (apply (mlocNB_mblocA FI AI); eapply (mlocNB_weaken FI AI); [exact FLL| lia| auto]).
  assert (FLC2 : rw_cells asegs m2 FL (fl_cells N fk)).
  { eapply (apres_rw_cells FI AI); [exact AP2| exact FLC|]. unfold fl_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
    eapply (mblocA_client FI AI); [exact RF| exact FLM2]. }
  assert (QC : alloc_ceiling <= q + -48) by lia.
  pose proof (mblocA_shw_apres FI AI AMS s' _ _ (q + -48) st m m2 FL 24 FLM2 SHWF AP2 RF HR2 (fun b H => H) QC) as SHWF2.
  assert (HP2 : apx FI AI [(FL, FL + 24)] LBK q m0 m2).
  { eapply (apx_trans FI AI); [exact HP0|]. apply apx_of_apres. eapply (apres_weaken FI AI); [exact AP2| lia|].
    intros b0' Hb0. apply KEEP. apply in_or_app. right. exact Hb0. }
  assert (FLS2 : flseg m2 FB nx).
  { eapply flseg_apres; [exact FLS'| exact AP2|]. intros b0' Hb0. apply KEEP. apply in_or_app. left. exact Hb0. }
  assert (ND2 : NoDup (map blk_id (FB ++ LBK))) by (cbn in ND; inversion ND; assumption).
  eapply (aj_evt FI AI J). { eapply (fdsegC FL N fk nx (q + -48)); try eassumption; lia. }
  intros ms' (m3 & -> & MU3 & WM3 & MI3 & FLC3).
  assert (FLM8 : mblocA FI AI (lbrm (blk_id b) LB) (q + -48) st FL 8) by (eapply (mblocA_sub FI AI); [exact FLM2| lia| lia]).
  assert (HR3 : RHEAP_A FI AI s' (lbrm (blk_id b) LB) m3).
  { eapply (am_heap_frame FI AI); [exact HR2| exact MU3| exact WM3|]. constructor; [| constructor].
    exact (mblocA_hf FI AI _ _ (q + -48) st m2 FL 8 RF2 FLM8 QC (fun b1 H => H)). }
  assert (RF3 : RFAKE FI st m3).
  { eapply (rfake_frame FI); [exact RF2| exact MU3| exact WM3|].
    constructor; [| constructor]. eapply (rf_ok_mbloc FI AI s' _ _ (q + -48) st m2 FL 8 HR2 (fun b H => H)); [| lia| lia].
    eapply (mblocA_sub FI AI); [exact FLM2| lia| lia]. }
  assert (AE3 : asan_env asegs m3).
  { eapply asan_env_frame; [exact AE2| exact MU3| exact WM3|]. unfold env_safe. constructor; [left; cbn; lia| constructor]. }
  pose proof (rw_cells_transport asegs _ m2 m3 _ _ FR2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR3.
  assert (ST3 : stk asegs m3 lo (q + -48)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]).
  assert (AIV : app_ivs [(FL, FL + 8)]) by (pose proof (shw_win_ok _ _ _ SHWF) as WKF; unfold win_ok in WKF; app_ivs_tac).
  pose proof (shw_frame _ m2 m3 FL 24 SHWF2 MU3 AIV) as SHWF3.
  assert (FLS3 : flseg m3 FB nx).
  { eapply (flseg_transport FI AI); [exact FLS2| exact MU3| exact WM3|]. intros b0' Hb0.
    pose proof (KEEP b0' ltac:(apply in_or_app; left; exact Hb0)) as Hk. apply (lb_remove_sub FI AI) in Hk.
    pose proof (mlocNB_apart FI AI s LB m st q FL 24 b0' HR RF FLL Hk ltac:(lia) ltac:(lia)) as DFb.
    destruct (am_block_range FI AI s LB m _ HR Hk) as (Q1 & _ & Q3 & Q4 & _).
    destruct (flseg_shape FI AI FB m2 nx b0' FLS2 Hb0) as [Eb0 _]. rewrite Eb0 in DFb, Q3 |- *. cbn [blk_addr blk_size fst snd] in *. cbn. lia. }
  assert (HP3 : apx FI AI [(FL, FL + 24)] LBK q m0 m3).
  { eapply (apx_trans FI AI); [exact HP2|]. eapply (apx_seg FI AI ASL s' _ _ q _ _ m2 m2 m3 HR2 (fun b8 H8 => KEEP b8 (in_or_app _ _ _ (or_intror H8))) MU3 WM3).
    constructor; [right; right; cbn; lia| constructor]. }
  destruct (Z.eqb_spec nx 0) as [NX0|NX1].
  -
    eapply (aj_evt FI AI J). { eapply (fdsegD lo FL nx fk j); try eassumption; lia. }
    intros ms' (c1' & c2' & m4 & -> & MU4 & WM4 & MI4 & ST4 & AE4 & FLC4).
    apply (aj_ret FI AI J). unfold FreeListDestroy_post_A. subst nx.
    do 14 eexists. exists m4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [exact AE4|].
    assert (FLM3 : mblocA FI AI (lbrm (blk_id b) LB) q st FL 24) by (apply (mlocNB_mblocA FI AI); exact FLL).
    split. { eapply (rfake_frame FI); [exact RF3| exact MU4| exact WM4|].
             constructor; [eapply (rf_ok_mbloc FI AI s' _ _ q st m3 FL 24 HR3 (fun b1 H => H) FLM3); lia|].
             constructor; [apply (rf_ok_stack FI); cbn; lia| constructor]. }
    split. { eapply (apx_trans FI AI); [exact HP3|]. eapply (apx_seg FI AI ASL s' _ _ q _ _ m3 m3 m4 HR3 (fun b8 H8 => KEEP b8 (in_or_app _ _ _ (or_intror H8))) MU4 WM4).
             constructor; [right; right; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
    split. { eapply (am_heap_frame FI AI); [exact HR3| exact MU4| exact WM4|].
             constructor; [exact (mblocA_hf FI AI _ _ q st m3 FL 24 RF3 FLM3 ltac:(lia) (fun b1 H => H))|].
             constructor; [left; cbn; lia| constructor]. }
    split; [intros b0' Hb0; apply KEEP; apply in_or_app; right; exact Hb0|].
    split; [intros b0' Hb0; apply SUB0; eapply (lb_remove_sub FI AI); exact Hb0|].
    split; [| split; [exact FLC4| rewrite NS2; exact NS0]].
    destruct FB as [|bx FBx]; [| exfalso; cbn [HObjA.flseg] in FLS'; destruct FLS' as (NZx & _); apply NZx; reflexivity].
    intros b0' Hb0 IN1. destruct (GONE b0' Hb0) as [[E|[]]|NI].
    + subst b0'. exact (lb_remove_neq FI AI _ _ _ IN1 eq_refl).
    + apply NI. exact (lb_remove_sub FI AI _ _ _ IN1).
  -
    eapply (IH nx ra q gp u0 u1 u2 s0 s1) with (LB0 := LB0) (OWNED := OWNED); try eassumption; try lia.
    + intros b0' Hb0. apply KEEP. apply in_or_app. left. exact Hb0.
    + intros b0' Hb0. apply KEEP. apply in_or_app. right. exact Hb0.
    + intros b0' Hb0. apply SUB0. eapply (lb_remove_sub FI AI). exact Hb0.
    + intros b0' Hb0. destruct (GONE b0' Hb0) as [[E|INF]|NI].
      * subst b0'. right. intros IN1. exact (lb_remove_neq FI AI _ _ _ IN1 eq_refl).
      * left. exact INF.
      * right. intros IN1. apply NI. exact (lb_remove_sub FI AI _ _ _ IN1).
Qed.

Definition FreeListDestroy_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB : BL) (st : fsstate FI) (FL flh fk lo : Z) (FB LBK : BL),
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 48 - A0_RT_STACK -> q mod 16 = 0 -> q + 16 <= am_stack_top FI AI ->
  mem_inv asegs m ->
  rw_cells asegs m FL (fl_cells flh fk) -> mlocNB FI AI q st FL 24 -> FL + 24 <= alloc_ceiling -> FL mod 8 = 0 -> shw m FL 24 ->
  flseg m FB flh -> bsub FB LB -> bsub LBK LB -> NoDup (map blk_id (FB ++ LBK)) ->
  a0 = wz FL ->
  AJ FI AI J (FreeListDestroy_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (am_nsec FI AI s) LB LBK FL lo m FB)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FreeListDestroy_entryA) fc None m (seg_rom asegs))
    s LB.

#[using="AC ASL AMS"] Theorem FreeListDestroy_spec_A : FreeListDestroy_stmt_A.
Proof.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB st FL flh fk lo FB LBK.
  intros HR RF AE ST CLO LO QAL QTOP MI FLC FLL FLHI AL SHWF FLS FSUB KSUB ND ->.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (TK1 & TK2 & TK3 & TK4).
  assert (LO' : lo <= q - 48 - 4096) by (unfold A0_RT_STACK in LO; exact LO).
  pose proof (mlocNB_mblocA FI AI LB q st FL 24 FLL) as FLM.
  destruct (mblocA_range FI AI s LB _ q st m FL 24 HR (fun b H => H) RF FLM ltac:(lia) ltac:(lia)) as (FLLO & _ & _).
  assert (FLH : 0 <= flh < 2^64).
  { destruct FB as [|b FB']; cbn [HObjA.flseg] in FLS. { subst flh. lia. }
    destruct FLS as (_ & Eb & _). pose proof (FSUB b (or_introl eq_refl)) as Hb. rewrite Eb in Hb.
    destruct (am_block_range FI AI s LB m _ HR Hb) as (Q1 & _ & _ & Q4 & _). cbn in Q1, Q4. lia. }
  eapply (aj_evt FI AI J). { eapply (fdsegA lo FL flh fk); try eassumption; lia. }
  intros ms' (j & c1 & c2 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & FLC1).
  assert (BIV1 : Forall (blk_iv FI AI LB) [(lo, q)]) by (constructor; [left; cbn; lia| constructor]).
  pose proof (rheap_blk_write FI AI s LB m m1 _ HR MU1 WM1 BIV1) as HR1.
  pose proof (rfake_blk_write FI AI s LB st m m1 _ HR RF MU1 WM1 ltac:(constructor; [split; [left; cbn; lia| cbn; lia]| constructor])) as RF1.
  pose proof (asan_env_frame asegs m m1 _ AE MU1 WM1 (env_safe_blk FI AI s LB m _ HR BIV1)) as AE1.
  pose proof (shw_frame _ m m1 FL 24 SHWF MU1 (app_ivs_blk FI AI s LB m _ HR BIV1)) as SHWF1.
  assert (HP1 : apx FI AI [(FL, FL + 24)] LBK q m m1).
  { eapply (apx_seg FI AI ASL s LB _ q _ _ m m m1 HR KSUB MU1 WM1). constructor; [left; cbn; lia| constructor]. }
  assert (FLS1 : flseg m1 FB flh).
  { eapply (flseg_transport FI AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb.
    destruct (am_block_range FI AI s LB m _ HR (FSUB b Hb)) as (Q1 & _ & Q3 & Q4 & _).
    destruct (flseg_shape FI AI FB m flh b FLS Hb) as [Eb _]. rewrite Eb in Q3, Q4. cbn [blk_addr blk_size fst snd] in *. cbn. lia. }
  destruct (Z.eqb_spec flh 0) as [F0|F1].
  -
    subst flh. eapply (aj_evt FI AI J). { eapply (fdsegD lo FL 0 fk j); try eassumption; lia. }
    intros ms' (c1' & c2' & m4 & -> & MU4 & WM4 & MI4 & ST4 & AE4 & FLC4).
    apply (aj_ret FI AI J). unfold FreeListDestroy_post_A.
    do 14 eexists. exists m4. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|]. split; [exact AE4|].
    split. { eapply (rfake_frame FI); [exact RF1| exact MU4| exact WM4|].
             constructor; [eapply (rf_ok_mbloc FI AI s LB _ q st m1 FL 24 HR1 (fun b1 H => H) FLM); lia|].
             constructor; [apply (rf_ok_stack FI); cbn; lia| constructor]. }
    split. { eapply (apx_trans FI AI); [exact HP1|]. eapply (apx_seg FI AI ASL s LB _ q _ _ m1 m1 m4 HR1 KSUB MU4 WM4).
             constructor; [right; right; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
    split. { eapply (am_heap_frame FI AI); [exact HR1| exact MU4| exact WM4|].
             constructor; [exact (mblocA_hf FI AI _ _ q st m1 FL 24 RF1 FLM ltac:(lia) (fun b1 H => H))|].
             constructor; [left; cbn; lia| constructor]. }
    split; [exact KSUB|]. split; [intros b0' Hb0; exact Hb0|]. split; [| split; [exact FLC4| reflexivity]].
    destruct FB as [|bx FBx]; [intros b0' []| exfalso; cbn [HObjA.flseg] in FLS; destruct FLS as (NZx & _); apply NZx; reflexivity].
  - eapply (fld_loop FB flh ra q gp t0 t1 t2 s0 s1) with (LB0 := LB) (OWNED := FB); try eassumption; try lia.
    + intros b0' Hb0; exact Hb0.
    + intros b0' Hb0; left; exact Hb0.
Qed.
End W.
