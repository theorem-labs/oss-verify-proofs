(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg RtCells F_syscalls StdioFiles Stdio_kit MonadF AExit.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import LiaTier0U.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

Definition cxa3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (f a : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x6c37e0, 0x6c37e4); (0x6c3810, 0x6c3810 + 8); (0x6c3910, 0x6c3910 + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x6c37e0 [C4 (Z_to_bv 64 4)]
    /\ rw_cells asegs m' 0x6c3810 [C8 f]
    /\ rw_cells asegs m' 0x6c3910 [C8 a].

(* [comment removed for export] *)
Lemma cxa_atexit_musl3 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 f0 a00 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0x6c3a18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
  rw_cells asegs m 0x6c37d8 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells asegs m 0x6c37dc [C4 z64] ->                                             (* [comment removed for export] *)
  rw_cells asegs m 0x6c37e0 [C4 (Z_to_bv 64 3)] ->                                  (* [comment removed for export] *)
  rw_cells asegs m 0x6c37e8 [C8 (Z_to_bv 64 0x6c37f0)] ->                           (* [comment removed for export] *)
  rw_cells asegs m 0x6c3810 [C8 f0] ->                                              (* [comment removed for export] *)
  rw_cells asegs m 0x6c3910 [C8 a00] ->                                             (* [comment removed for export] *)
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF asegs RNG (cxa3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo a0 a1 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x146c4c) fc None m (seg_rom asegs)).
Proof.
  intros until a00. intros ST LIBC FIN ALK SLOT HEAD F3 A3 MI LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6c37e0, 0x6c37e4); (0x6c3810, 0x6c3810 + 8); (0x6c3910, 0x6c3910 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x159114%Z.
  (* [comment removed for export] *)
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  (* [comment removed for export] *)
  hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep.
  (* [comment removed for export] *)
  astep. astep. astep.
  replace (sx32 (Z_to_bv 64 3)) with (Z_to_bv 64 3 : word) by (vm_compute; reflexivity).
  repeat astep.
  release_frame FR ST (bv_unsigned sp).
  unfold cxa3_post. sys_finish.
Qed.

Definition cxa4_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (f a : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x6c37e0, 0x6c37e4); (0x6c3818, 0x6c3818 + 8); (0x6c3918, 0x6c3918 + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x6c37e0 [C4 (Z_to_bv 64 5)]
    /\ rw_cells asegs m' 0x6c3818 [C8 f]
    /\ rw_cells asegs m' 0x6c3918 [C8 a].

(* [comment removed for export] *)
Lemma cxa_atexit_musl4 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 f0 a00 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0x6c3a18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
  rw_cells asegs m 0x6c37d8 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells asegs m 0x6c37dc [C4 z64] ->                                             (* [comment removed for export] *)
  rw_cells asegs m 0x6c37e0 [C4 (Z_to_bv 64 4)] ->                                  (* [comment removed for export] *)
  rw_cells asegs m 0x6c37e8 [C8 (Z_to_bv 64 0x6c37f0)] ->                           (* [comment removed for export] *)
  rw_cells asegs m 0x6c3818 [C8 f0] ->                                              (* [comment removed for export] *)
  rw_cells asegs m 0x6c3918 [C8 a00] ->                                             (* [comment removed for export] *)
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF asegs RNG (cxa4_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo a0 a1 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x146c4c) fc None m (seg_rom asegs)).
Proof.
  intros until a00. intros ST LIBC FIN ALK SLOT HEAD F3 A3 MI LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6c37e0, 0x6c37e4); (0x6c3818, 0x6c3818 + 8); (0x6c3918, 0x6c3918 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x159114%Z.
  (* [comment removed for export] *)
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  (* [comment removed for export] *)
  hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep.
  (* [comment removed for export] *)
  astep. astep. astep.
  replace (sx32 (Z_to_bv 64 4)) with (Z_to_bv 64 4 : word) by (vm_compute; reflexivity).
  repeat astep.
  release_frame FR ST (bv_unsigned sp).
  unfold cxa4_post. sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ICX_W (sp : Z) : list (Z * Z) :=
  [(sp - 96, sp); (0x6a3798, 0x6a379c); (0x6c37e0, 0x6c37e4); (0x6c3818, 0x6c3828); (0x6c3918, 0x6c3928)]%Z.

Definition icx3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (f a : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (0x6a3798, 0x6a379c); (0x6c37e0, 0x6c37e4); (0x6c3818, 0x6c3828); (0x6c3918, 0x6c3928)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x6a3798 [C4 z64]
    /\ rw_cells asegs m' 0x6c37e0 [C4 (Z_to_bv 64 6)]
    /\ rw_cells asegs m' 0x6c3818 [C8 f; C8 (Z_to_bv 64 0x759b0)]
    /\ rw_cells asegs m' 0x6c3918 [C8 a; C8 z64].

(* [comment removed for export] *)
Definition acxa_atexit_stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 f4 f5 a04 a05 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rt_inited m ->
  rw_cells asegs m 0x166d18 [C8 (Z_to_bv 64 16)] ->                                 (* [comment removed for export] *)
  rw_cells asegs m 0x6a3798 [C4 z64] ->                                             (* [comment removed for export] *)
  rw_cells asegs m 0x1680a8 [C8 (Z_to_bv 64 0x146c4c)] ->                           (* [comment removed for export] *)
  rw_cells asegs m 0x6c3a18 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
  rw_cells asegs m 0x6c37d8 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells asegs m 0x6c37dc [C4 z64] ->                                             (* [comment removed for export] *)
  rw_cells asegs m 0x6c37e0 [C4 (Z_to_bv 64 4)] ->                                  (* [comment removed for export] *)
  rw_cells asegs m 0x6c37e8 [C8 (Z_to_bv 64 0x6c37f0)] ->                           (* [comment removed for export] *)
  rw_cells asegs m 0x6c3818 [C8 f4; C8 f5] ->
  rw_cells asegs m 0x6c3918 [C8 a04; C8 a05] ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 RTP ->
  (lo <= bv_unsigned sp - 96)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF asegs RNG (icx3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo a0 a1 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x7592c) fc None m (seg_rom asegs)).

Lemma acxa_atexit_proof : acxa_atexit_stmt.
Proof.
  unfold acxa_atexit_stmt. intros until a05. intros ST INI GOT CNT REAL LIBC FIN ALK SLOT HEAD FF AA MI -> LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0x6a3798, 0x6a379c); (0x6c37e0, 0x6c37e4); (0x6c3818, 0x6c3828); (0x6c3918, 0x6c3928)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x88cb4%Z.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  steps_to 0x75954%Z.
  release_frame FR0 ST (bv_unsigned sp + -48)%Z.
  (* [comment removed for export] *)
  steps_to 0x75958%Z.
  replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) in * by (vm_compute; reflexivity).
  rewrite ?unsigned_lit in * by lia. change (0 + 1)%Z with 1%Z in *.
  (* [comment removed for export] *)
  steps_to 0x146c4c%Z.
  carve_frame 48%nat ST.
  steps_to 0x159114%Z.
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep.
  astep. astep. astep.
  replace (sx32 (Z_to_bv 64 4)) with (Z_to_bv 64 4 : word) by (vm_compute; reflexivity).
  steps_to 0x75970%Z.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -96)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -48)%Z end.
  (* [comment removed for export] *)
  steps_to 0x146c4c%Z.
  carve_frame 48%nat ST.
  steps_to 0x159114%Z.
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep.
  astep. astep. astep.
  replace (sx32 (Z_to_bv 64 5)) with (Z_to_bv 64 5 : word) by (vm_compute; reflexivity).
  steps_to 0x7598c%Z.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -96)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -48)%Z end.
  (* [comment removed for export] *)
  steps_to 0xaf40c%Z.
  carve_frame 16%nat ST.
  do 7 hstep.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep. hstep. rewrite ?unsigned_lit by lia. change (1 + -1)%Z with 0%Z.
  steps_to 0x75990%Z.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -48)%Z end.
  replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) in * by (vm_compute; reflexivity).
  repeat astep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _ |- _ => release_frame H ST (bv_unsigned sp) end.
  unfold icx3_post. sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ATX_FIN : Z := 0x6c37d8.    (* [comment removed for export] *)
Definition ATX_LOCK : Z := 0x6c37dc.   (* [comment removed for export] *)
Definition ATX_SLOT : Z := 0x6c37e0.   (* [comment removed for export] *)
Definition ATX_HEAD : Z := 0x6c37e8.   (* [comment removed for export] *)
Definition ATX_BUILTIN : Z := 0x6c37f0.  (* [comment removed for export] *)
Definition ATX_F : Z := 0x6c37f8.
Definition ATX_A : Z := 0x6c38f8.

Definition atexit_cells (fs args : list word) (n : Z) (m : mem) : Prop :=
  rw_cells asegs m ATX_FIN [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m ATX_LOCK [C4 z64] /\ rw_cells asegs m ATX_SLOT [C4 (Z_to_bv 64 n)]
  /\ rw_cells asegs m ATX_HEAD [C8 (Z_to_bv 64 ATX_BUILTIN)] /\ rw_cells asegs m ATX_BUILTIN [C8 z64]
  /\ rw_cells asegs m ATX_F (map C8 fs) /\ rw_cells asegs m ATX_A (map C8 args)
  /\ length fs = 32%nat /\ length args = 32%nat.

Definition ATEXIT (tbl : list (Z * Z)) (m : mem) : Prop :=
  exists fj aj : list word,
    atexit_cells (map (fun e => Z_to_bv 64 (fst e)) (rev tbl) ++ fj) (map (fun e => Z_to_bv 64 (snd e)) (rev tbl) ++ aj) (Z.of_nat (length tbl)) m.

(* [comment removed for export] *)
Definition AATEXIT : Z := 0x146d14.
Definition ACALL_THUNK : Z := 0x146dd8.
Definition AAEF_GUARD : Z := 0xafe40.
Definition AIN_CB : Z := 0x6a1354.
Definition TBL_MAIN : list (Z * Z) := [(0x759b0, 0); (0x108810, 0x6a1828); (0x146dd8, 0x9f478)].
Definition TBL_REG : list (Z * Z) := (0x146dd8, 0xafe40) :: TBL_MAIN.
Definition TBL_RUN (f a : Z) : list (Z * Z) := (0x759b0, 0) :: (f, a) :: TBL_REG.

Lemma cells_size_map_C8' : forall ws : list word, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.

Definition aincb (cb : Z) (m : mem) : Prop := rw_cells asegs m 0x6a1354 [C1 (Z_to_bv 8 cb)].
Definition aincb_addr (a : Z) : Prop := 0x6a1354 <= a < 0x6a1355.
Lemma aincb_magree : forall (P : Z -> Prop) cb m m',
  DrvAgree.magree asegs P m m' -> (forall a, aincb_addr a -> P a) -> aincb cb m -> aincb cb m'.
Proof. intros P cb m m' AG HP A. unfold aincb in *. eapply DrvAgree.rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold aincb_addr; cbn in Ha; lia]. Qed.
Lemma aincb_munch : forall W cb m m',
  munch W m m' -> wmono asegs m m' -> (forall a, aincb_addr a -> outside W a) -> aincb cb m -> aincb cb m'.
Proof. intros W cb m m' MU WM HW. apply (aincb_magree _ _ _ _ (DrvAgree.magree_of_munch asegs _ _ _ MU WM)). intros a Ha. cbn beta. apply HW. exact Ha. Qed.
Lemma aincb_addr_range : forall a, aincb_addr a -> a = 0x6a1354.
Proof. intros a Ha. unfold aincb_addr in Ha. lia. Qed.
End CANSEC1.
