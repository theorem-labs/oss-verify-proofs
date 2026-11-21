(* reloc-zl14c *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep InitMem Frame.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import StrFun STRW_tac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU7 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).
(* [comment removed for export] *)
Ltac astep := lstep; try (first [if_true | if_false]).
Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *) Context {rc : runConstT}.
Definition PATEXIT : Z := 0x1a29c.          (* [comment removed for export] *)
Definition PFUNCS_ON_EXIT : Z := 0x1a1d0.   (* [comment removed for export] *)
Definition PATX_CALL : Z := 0x1a360.        (* [comment removed for export] *)
Definition PAEF_GUARD : Z := 0x14d24.       (* [comment removed for export] *)
Definition PAEF_INCB : Z := 0x34174.        (* [comment removed for export] *)
Definition PATX : Z := 0x942b0.             (* [comment removed for export] *)
Definition PATX_N : Z := 544.
Definition PLOCK_FN : Z := 0x21a88.         (* [comment removed for export] *)
Definition PUNLOCK_FN : Z := 0x21d10.       (* [comment removed for export] *)
Definition PLIBC : Z := 0x944f8.            (* [comment removed for export] *)
Definition PNEEDLK : Z := 0x944fb.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atx_cells0 (m : mem) : Prop :=
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m PATX [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (PATX + 288) [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition atx_cellsA (m : mem) : Prop :=
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m PATX [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0);
                       C8 (Z_to_bv 64 (PATX + 24)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 PATX_CALL)]
  /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (PATX + 288) [C8 (Z_to_bv 64 PAEF_GUARD)].

(* [comment removed for export] *)
Definition atx_cellsR (m : mem) : Prop := atx_cellsA m /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m PAEF_INCB [C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition atx_addr (a : Z) : Prop := (PATX <= a < PATX + PATX_N) \/ (PAEF_INCB <= a < PAEF_INCB + 1).

(* [comment removed for export] *)
Definition atx_addrA (a : Z) : Prop := PATX <= a < PATX + PATX_N.
(* [comment removed for export] *)
Lemma disjoint_from_sub : forall (W : list (Z * Z)) A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof.
  intros W A n A' n' H H1 H2. induction W as [|[lo' hi'] W IH]; cbn in *; [exact I|]. destruct H as [H H']. split; [lia| apply IH; exact H'].
Qed.
Lemma atx_cellsA_munch : forall W m m', munch W m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' -> disjoint_from W PATX PATX_N -> atx_cellsA m -> atx_cellsA m'.
Proof.
  intros W m m' MU WM HW H. unfold atx_cellsA, PATX, PATX_N in *. destruct H as [A B]. split.
  - eapply rw_cells_transport; [exact A| exact MU| exact WM|]. eapply disjoint_from_sub; [exact HW| lia| cbn; lia].
  - eapply rw_cells_transport; [exact B| exact MU| exact WM|]. eapply disjoint_from_sub; [exact HW| lia| cbn; lia].
Qed.
Lemma atx_cells0_munch : forall W m m', munch W m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' -> disjoint_from W PATX PATX_N -> atx_cells0 m -> atx_cells0 m'.
Proof.
  intros W m m' MU WM HW H. unfold atx_cells0, PATX, PATX_N in *. destruct H as [A B]. split.
  - eapply rw_cells_transport; [exact A| exact MU| exact WM|]. eapply disjoint_from_sub; [exact HW| lia| cbn; lia].
  - eapply rw_cells_transport; [exact B| exact MU| exact WM|]. eapply disjoint_from_sub; [exact HW| lia| cbn; lia].
Qed.
Lemma atx_cellsR_munch : forall W m m', munch W m m' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' -> disjoint_from W PATX PATX_N -> disjoint_from W PAEF_INCB 1 ->
  atx_cellsR m -> atx_cellsR m'.
Proof.
  intros W m m' MU WM HW HW2 H. destruct H as [A C]. split; [eapply atx_cellsA_munch; [exact MU| exact WM| exact HW| exact A]|].
  eapply rw_cells_transport; [exact C| exact MU| exact WM|]. exact HW2.
Qed.

(* [comment removed for export] *)
Ltac atx_chunk0 NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A cs);
  [ apply (InitMem.rw_cells_recast (run_segments psegs rc_inp rc_sp rc_mb) m A [CB (length bs) bs] cs);
    [ apply (InitMem.rw_cells_image0 (run_segments psegs rc_inp rc_sp rc_mb) m A bs);
      [ intros a Ha; cbn [length] in Ha; apply NONE; unfold atx_addr, PATX, PATX_N, PAEF_INCB; left; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].
Lemma atx_cells0_init : forall m : mem, (forall a : word, atx_addr (bv_unsigned a) -> m a = None) -> atx_cells0 m.
Proof.
  intros m NONE. unfold atx_cells0, PATX.
  atx_chunk0 NONE m 0x942b0 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                            C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H1.
  atx_chunk0 NONE m (0x942b0 + 288) [C8 (Z_to_bv 64 0)] H2.
  split; [exact H1| exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition atexit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (PATX, PATX + PATX_N)] m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp)
    /\ atx_cellsA m'.

Lemma atexit_guard_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) ->
  atx_cells0 m ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m PNEEDLK [C1 (Z_to_bv 8 0)] ->        (* [comment removed for export] *)
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  a0 = Z_to_bv 64 PAEF_GUARD ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x95000 <= lo)%Z ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (atexit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PATEXIT) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros ST [AX AXA] LCH MI -> LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold PATX, PATX_N, PLIBC, PNEEDLK, PAEF_GUARD, PATEXIT in *. change (606896 + 288) with 607184 in AXA.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x942b0, 0x942b0 + 544)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  (* [comment removed for export] *)
  lstep. carve_frame 48%nat ST. do 5 lstep.
  (* [comment removed for export] *)
  do 6 lstep.
  (* [comment removed for export] *)
  astep. astep. astep. astep.
  (* [comment removed for export] *)
  astep. astep. astep.
  (* [comment removed for export] *)
  astep. astep. astep. astep.
  (* [comment removed for export] *)
  astep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. astep.
  (* [comment removed for export] *)
  do 9 astep.
  (* [comment removed for export] *)
  astep. astep. astep. astep. astep.
  (* [comment removed for export] *)
  astep. do 5 astep. release_frame FR ST (bv_unsigned sp). astep. astep.
  unfold atexit_post, atx_cellsA. sys_finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition funcs_on_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (PATX, PATX + PATX_N)] m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp).

Lemma funcs_on_exit_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) ->
  (atx_cells0 m \/ atx_cellsR m) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m PNEEDLK [C1 (Z_to_bv 8 0)] ->        (* [comment removed for export] *)
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x95000 <= lo)%Z ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (funcs_on_exit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PFUNCS_ON_EXIT) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until lo. intros ST AX LCH MI LO LOLO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold atx_cells0, atx_cellsR, atx_cellsA, PATX, PATX_N, PLIBC, PNEEDLK, PFUNCS_ON_EXIT, PAEF_INCB, PATX_CALL, PAEF_GUARD in *.
  change (606896 + 288) with 607184 in AX. change (606896 + 24) with 606920 in AX.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x942b0, 0x942b0 + 544)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  destruct AX as [[AX AXA]|[[AX AXA] CB0]].
  - (* [comment removed for export] *)
    lstep. carve_frame 48%nat ST. do 5 lstep.
    (* [comment removed for export] *)
    do 5 lstep. astep. astep. astep. astep.
    (* [comment removed for export] *)
    astep. astep.
    (* [comment removed for export] *)
    astep. astep. astep. do 5 astep. release_frame FR ST (bv_unsigned sp). astep. astep.
    astep. astep. astep.
    unfold funcs_on_exit_post. sys_finish.
  - (* [comment removed for export] *)
    lstep. carve_frame 48%nat ST. do 5 lstep.
    do 5 lstep. astep. astep. astep. astep.
    (* [comment removed for export] *)
    astep. astep. astep. replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity). astep.
    (* [comment removed for export] *)
    astep. astep. astep.
    (* [comment removed for export] *)
    astep. astep. astep. astep. astep.
    (* [comment removed for export] *)
    astep. astep. astep. astep. astep.
    (* [comment removed for export] *)
    astep. astep. astep. astep. astep. astep. astep.
    (* [comment removed for export] *)
    astep. astep. astep. astep. astep.
    astep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. astep.
    (* [comment removed for export] *)
    astep. astep. astep.
    (* [comment removed for export] *)
    astep. astep. astep. astep. astep. astep.
    (* [comment removed for export] *)
    astep. astep. astep. do 5 astep. release_frame FR ST (bv_unsigned sp). astep. astep.
    astep. astep. astep.
    unfold funcs_on_exit_post. sys_finish.
Qed.
End CANSEC1.
