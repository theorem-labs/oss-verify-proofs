(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge ITree Nodes Decode SysStep Arr.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells F_syscalls StdioFiles Stdio_kit MonadF AAtexit_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw DrvAgree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).
Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.

(* [comment removed for export] *)
Definition hidden (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Ltac unhide H := unfold hidden in H.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition AATEXIT_W (sp : Z) : list (Z * Z) := [(sp - 48, sp); (0x6d1f00, 0x6d1f04); (0x6d1f30, 0x6d1f38); (0x6d2030, 0x6d2038)]%Z.
Definition AATEXIT_STACK : Z := 48.     (* [comment removed for export] *)

Definition atexit3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d1f00, 0x6d1f04); (0x6d1f30, 0x6d1f38); (0x6d2030, 0x6d2038)]%Z m m'   (* [comment removed for export] *)
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ ATEXIT TBL_REG m'.

(* [comment removed for export] *)
Lemma atexit3_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0x6d2138 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->      (* [comment removed for export] *)
  ATEXIT TBL_MAIN m ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AAEF_GUARD ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (atexit3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AATEXIT) fc None m (seg_rom bsegs)).
Proof.
  intros until tm1. intros ST LIBC ATX MI -> LO KH RSTK RIMG.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KHIGH in KH.
  (* [comment removed for export] *)
  destruct ATX as (fj & aj & FIN & ALK & SLOT & HEAD & NEXT & FF & AA & LF & LA).
  unfold ATX_FIN, ATX_LOCK, ATX_SLOT, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A in *.
  unfold TBL_MAIN in FF, AA, SLOT, LF, LA. cbn [rev app map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ] in FF, AA, SLOT, LF, LA.
  destruct fj as [|f1 fj]; [cbn in LF; lia|]. destruct aj as [|g1 aj]; [cbn in LA; lia|].
  cbn [length] in LF, LA. cbn [map] in FF, AA. change (Z.of_nat 3) with 3%Z in SLOT.
  change (C8 (Z_to_bv 64 0x15475c) :: C8 (Z_to_bv 64 0x116254) :: C8 (Z_to_bv 64 0x76be0) :: C8 f1 :: map C8 fj)
    with ([C8 (Z_to_bv 64 0x15475c); C8 (Z_to_bv 64 0x116254); C8 (Z_to_bv 64 0x76be0); C8 f1] ++ map C8 fj) in FF.
  change (C8 (Z_to_bv 64 0xa06a8) :: C8 (Z_to_bv 64 0x6aff48) :: C8 (Z_to_bv 64 0) :: C8 g1 :: map C8 aj)
    with ([C8 (Z_to_bv 64 0xa06a8); C8 (Z_to_bv 64 0x6aff48); C8 (Z_to_bv 64 0); C8 g1] ++ map C8 aj) in AA.
  apply (proj1 (rw_cells_app bsegs m _ _ _)) in FF. destruct FF as [FF FFR].
  apply (proj1 (rw_cells_app bsegs m _ _ _)) in AA. destruct AA as [AA AAR].
  match type of FFR with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in FFR end.
  match type of AAR with rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' in AAR end.
  pose proof (cells_size_map_C8' fj) as SZF. pose proof (cells_size_map_C8' aj) as SZA.
  hide FFR. hide AAR.
  unfold AAEF_GUARD, AATEXIT.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x6d1f00, 0x6d1f04); (0x6d1f30, 0x6d1f38); (0x6d2030, 0x6d2038)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  (* [comment removed for export] *)
  steps_to 0x166a98%Z.
  hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep. hstep.
  (* [comment removed for export] *)
  hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep.
  (* [comment removed for export] *)
  hstep. astep.
  (* [comment removed for export] *)
  hstep. nlit. hstep. astep.
  steps_to 0x166d20%Z.
  (* [comment removed for export] *)
  hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
  (* [comment removed for export] *)
  hstep. do 5 hstep.
  release_frame FR ST (bv_unsigned sp)%Z.
  hstep. hstep.
  unfold atexit3_post. apply evtF_done.
  do 15 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  (* [comment removed for export] *)
  unhide FFR. unhide AAR.
  lazymatch type of MU with munch _ _ ?m' =>
    pose proof (rw_cells_transport bsegs _ m m' _ _ FFR MU WM ltac:(rewrite SZF; cbn [disjoint_from]; lia)) as FFR';
    pose proof (rw_cells_transport bsegs _ m m' _ _ AAR MU WM ltac:(rewrite SZA; cbn [disjoint_from]; lia)) as AAR';
    clear FFR AAR
  end.
  exists fj, aj. unfold atexit_cells, TBL_REG, TBL_MAIN, ACALL_THUNK, AAEF_GUARD, ATX_FIN, ATX_LOCK, ATX_SLOT, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A.
  cbn [rev app map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ].
  repeat match goal with |- _ /\ _ => split end; try hyp_by_addr.
  - change (C8 (Z_to_bv 64 0x15475c) :: C8 (Z_to_bv 64 0x116254) :: C8 (Z_to_bv 64 0x76be0) :: C8 (Z_to_bv 64 0x15475c) :: map C8 fj)
      with ([C8 (Z_to_bv 64 0x15475c); C8 (Z_to_bv 64 0x116254); C8 (Z_to_bv 64 0x76be0); C8 (Z_to_bv 64 0x15475c)] ++ map C8 fj).
    apply (proj2 (rw_cells_app bsegs _ _ _ _)). split; [hyp_by_addr|].
    match goal with |- rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' end. hyp_by_addr.
  - change (C8 (Z_to_bv 64 0xa06a8) :: C8 (Z_to_bv 64 0x6aff48) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 0xb1070) :: map C8 aj)
      with ([C8 (Z_to_bv 64 0xa06a8); C8 (Z_to_bv 64 0x6aff48); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0xb1070)] ++ map C8 aj).
    apply (proj2 (rw_cells_app bsegs _ _ _ _)). split; [hyp_by_addr|].
    match goal with |- rw_cells _ _ ?A _ => let A' := eval vm_compute in A in change A with A' end. hyp_by_addr.
  - cbn [length]. lia.
  - cbn [length]. lia.
Qed.
End CANSEC1.
