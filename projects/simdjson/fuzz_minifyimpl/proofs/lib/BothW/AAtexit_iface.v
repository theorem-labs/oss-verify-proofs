(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells F_syscalls StdioFiles Stdio_kit MonadF AExit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

Definition cxa4_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (f a : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d1f00, 0x6d1f04); (0x6d1f38, 0x6d1f38 + 8); (0x6d2038, 0x6d2038 + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x6d1f00 [C4 (Z_to_bv 64 5)]
    /\ rw_cells bsegs m' 0x6d1f38 [C8 f]
    /\ rw_cells bsegs m' 0x6d2038 [C8 a].

(* [comment removed for export] *)
Lemma cxa_atexit_musl4 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 f0 a00 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0x6d2138 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1ef8 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1efc [C4 z64] ->                                             (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1f00 [C4 (Z_to_bv 64 4)] ->                                  (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1f08 [C8 (Z_to_bv 64 0x6d1f10)] ->                           (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1f38 [C8 f0] ->                                              (* [comment removed for export] *)
  rw_cells bsegs m 0x6d2038 [C8 a00] ->                                             (* [comment removed for export] *)
  mem_inv bsegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (cxa4_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo a0 a1 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1545d0) fc None m (seg_rom bsegs)).
Proof.
  intros until a00. intros ST LIBC FIN ALK SLOT HEAD F3 A3 MI LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d1f00, 0x6d1f04); (0x6d1f38, 0x6d1f38 + 8); (0x6d2038, 0x6d2038 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x166a98%Z.
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

Definition cxa5_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (f a : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d1f00, 0x6d1f04); (0x6d1f40, 0x6d1f40 + 8); (0x6d2040, 0x6d2040 + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x6d1f00 [C4 (Z_to_bv 64 6)]
    /\ rw_cells bsegs m' 0x6d1f40 [C8 f]
    /\ rw_cells bsegs m' 0x6d2040 [C8 a].

(* [comment removed for export] *)
Lemma cxa_atexit_musl5 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 f0 a00 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0x6d2138 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1ef8 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1efc [C4 z64] ->                                             (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1f00 [C4 (Z_to_bv 64 5)] ->                                  (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1f08 [C8 (Z_to_bv 64 0x6d1f10)] ->                           (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1f40 [C8 f0] ->                                              (* [comment removed for export] *)
  rw_cells bsegs m 0x6d2040 [C8 a00] ->                                             (* [comment removed for export] *)
  mem_inv bsegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (cxa5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo a0 a1 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1545d0) fc None m (seg_rom bsegs)).
Proof.
  intros until a00. intros ST LIBC FIN ALK SLOT HEAD F3 A3 MI LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d1f00, 0x6d1f04); (0x6d1f40, 0x6d1f40 + 8); (0x6d2040, 0x6d2040 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x166a98%Z.
  (* [comment removed for export] *)
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  (* [comment removed for export] *)
  hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep.
  (* [comment removed for export] *)
  astep. astep. astep.
  replace (sx32 (Z_to_bv 64 5)) with (Z_to_bv 64 5 : word) by (vm_compute; reflexivity).
  repeat astep.
  release_frame FR ST (bv_unsigned sp).
  unfold cxa5_post. sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ICX_W (sp : Z) : list (Z * Z) :=
  [(sp - 96, sp); (0x6b1eb8, 0x6b1ebc); (0x6d1f00, 0x6d1f04); (0x6d1f38, 0x6d1f48); (0x6d2038, 0x6d2048)]%Z.

Definition icx3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (f a : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (0x6b1eb8, 0x6b1ebc); (0x6d1f00, 0x6d1f04); (0x6d1f38, 0x6d1f48); (0x6d2038, 0x6d2048)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x6b1eb8 [C4 z64]
    /\ rw_cells bsegs m' 0x6d1f00 [C4 (Z_to_bv 64 6)]
    /\ rw_cells bsegs m' 0x6d1f38 [C8 f; C8 (Z_to_bv 64 0x76be0)]
    /\ rw_cells bsegs m' 0x6d2038 [C8 a; C8 z64].

(* [comment removed for export] *)
Definition acxa_atexit_stmt : Prop := forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 f4 f5 a04 a05 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  rt_inited m ->
  rw_cells bsegs m 0x174938 [C8 (Z_to_bv 64 16)] ->                                 (* [comment removed for export] *)
  rw_cells bsegs m 0x6b1eb8 [C4 z64] ->                                             (* [comment removed for export] *)
  rw_cells bsegs m 0x175cc0 [C8 (Z_to_bv 64 0x1545d0)] ->                           (* [comment removed for export] *)
  rw_cells bsegs m 0x6d2138 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1ef8 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1efc [C4 z64] ->                                             (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1f00 [C4 (Z_to_bv 64 4)] ->                                  (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1f08 [C8 (Z_to_bv 64 0x6d1f10)] ->                           (* [comment removed for export] *)
  rw_cells bsegs m 0x6d1f38 [C8 f4; C8 f5] ->
  rw_cells bsegs m 0x6d2038 [C8 a04; C8 a05] ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 RTP ->
  (lo <= bv_unsigned sp - 96)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (icx3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo a0 a1 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x76b5c) fc None m (seg_rom bsegs)).

Lemma acxa_atexit_proof : acxa_atexit_stmt.
Proof.
  unfold acxa_atexit_stmt. intros until a05. intros ST INI GOT CNT REAL LIBC FIN ALK SLOT HEAD FF AA MI -> LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (0x6b1eb8, 0x6b1ebc); (0x6d1f00, 0x6d1f04); (0x6d1f38, 0x6d1f48); (0x6d2038, 0x6d2048)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  steps_to 0x89ee4%Z.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  steps_to 0x76b84%Z.
  release_frame FR0 ST (bv_unsigned sp + -48)%Z.
  (* [comment removed for export] *)
  steps_to 0x76b88%Z.
  replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) in * by (vm_compute; reflexivity).
  rewrite ?unsigned_lit in * by lia. change (0 + 1)%Z with 1%Z in *.
  (* [comment removed for export] *)
  steps_to 0x1545d0%Z.
  carve_frame 48%nat ST.
  steps_to 0x166a98%Z.
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep.
  astep. astep. astep.
  replace (sx32 (Z_to_bv 64 4)) with (Z_to_bv 64 4 : word) by (vm_compute; reflexivity).
  steps_to 0x76ba0%Z.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -96)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -48)%Z end.
  (* [comment removed for export] *)
  steps_to 0x1545d0%Z.
  carve_frame 48%nat ST.
  steps_to 0x166a98%Z.
  hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
  hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep.
  astep. astep. astep.
  replace (sx32 (Z_to_bv 64 5)) with (Z_to_bv 64 5 : word) by (vm_compute; reflexivity).
  steps_to 0x76bbc%Z.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -96)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -48)%Z end.
  (* [comment removed for export] *)
  steps_to 0xb063c%Z.
  carve_frame 16%nat ST.
  do 7 hstep.
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep. hstep. rewrite ?unsigned_lit by lia. change (1 + -1)%Z with 0%Z.
  steps_to 0x76bc0%Z.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -64)%Z _ |- _ => release_frame H ST (bv_unsigned sp + -48)%Z end.
  replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) in * by (vm_compute; reflexivity).
  repeat astep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _ |- _ => release_frame H ST (bv_unsigned sp) end.
  unfold icx3_post. sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ATX_FIN : Z := 0x6d1ef8.    (* [comment removed for export] *)
Definition ATX_LOCK : Z := 0x6d1efc.   (* [comment removed for export] *)
Definition ATX_SLOT : Z := 0x6d1f00.   (* [comment removed for export] *)
Definition ATX_HEAD : Z := 0x6d1f08.   (* [comment removed for export] *)
Definition ATX_BUILTIN : Z := 0x6d1f10.  (* [comment removed for export] *)
Definition ATX_F : Z := 0x6d1f18.
Definition ATX_A : Z := 0x6d2018.

Definition atexit_cells (fs args : list word) (n : Z) (m : mem) : Prop :=
  rw_cells bsegs m ATX_FIN [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m ATX_LOCK [C4 z64] /\ rw_cells bsegs m ATX_SLOT [C4 (Z_to_bv 64 n)]
  /\ rw_cells bsegs m ATX_HEAD [C8 (Z_to_bv 64 ATX_BUILTIN)] /\ rw_cells bsegs m ATX_BUILTIN [C8 z64]
  /\ rw_cells bsegs m ATX_F (map C8 fs) /\ rw_cells bsegs m ATX_A (map C8 args)
  /\ length fs = 32%nat /\ length args = 32%nat.

Definition ATEXIT (tbl : list (Z * Z)) (m : mem) : Prop :=
  exists fj aj : list word,
    atexit_cells (map (fun e => Z_to_bv 64 (fst e)) (rev tbl) ++ fj) (map (fun e => Z_to_bv 64 (snd e)) (rev tbl) ++ aj) (Z.of_nat (length tbl)) m.

(* [comment removed for export] *)
Definition AATEXIT : Z := 0x154698.       (* [comment removed for export] *)
Definition ACALL_THUNK : Z := 0x15475c.   (* [comment removed for export] *)
Definition AAEF_GUARD : Z := 0xb1070.     (* [comment removed for export] *)
Definition AIN_CB : Z := 0x6afad4.        (* [comment removed for export] *)
Definition TBL_MAIN : list (Z * Z) := [(0x76be0, 0); (0x116254, 0x6aff48); (0x15475c, 0xa06a8)].
Definition TBL_REG : list (Z * Z) := (0x15475c, 0xb1070) :: TBL_MAIN.
Definition TBL_RUN (f a : Z) : list (Z * Z) := (0x76be0, 0) :: (f, a) :: TBL_REG.

(* [comment removed for export] *)
Lemma cells_size_map_C8' : forall ws : list word, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
Definition aincb (cb : Z) (m : mem) : Prop := rw_cells bsegs m 0x6afad4 [C1 (Z_to_bv 8 cb)].
Definition aincb_addr (a : Z) : Prop := 0x6afad4 <= a < 0x6afad5.
Lemma aincb_magree : forall (P : Z -> Prop) cb m m',
  DrvAgree.magree bsegs P m m' -> (forall a, aincb_addr a -> P a) -> aincb cb m -> aincb cb m'.
Proof. intros P cb m m' AG HP A. unfold aincb in *. eapply DrvAgree.rw_cells_magree; [exact AG| exact A| intros a Ha; apply HP; unfold aincb_addr; cbn in Ha; lia]. Qed.
Lemma aincb_munch : forall W cb m m',
  munch W m m' -> wmono bsegs m m' -> (forall a, aincb_addr a -> outside W a) -> aincb cb m -> aincb cb m'.
Proof. intros W cb m m' MU WM HW. apply (aincb_magree _ _ _ _ (DrvAgree.magree_of_munch bsegs _ _ _ MU WM)). intros a Ha. cbn beta. apply HW. exact Ha. Qed.
Lemma aincb_addr_range : forall a, aincb_addr a -> a = 0x6afad4.
Proof. intros a Ha. unfold aincb_addr in Ha. lia. Qed.
End CANSEC1.
