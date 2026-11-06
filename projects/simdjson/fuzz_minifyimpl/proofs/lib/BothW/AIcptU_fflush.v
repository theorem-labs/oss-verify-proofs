(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep ZBridge InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ITreeA StepF StrwF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells ShadowTac F_syscalls StdioFiles Stdio_kit F_tryinit AIcptU_hmap.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac iprem :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => first [assumption | eassumption]
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH in *; lia] end ]
  | |- rng_aimg _ => assumption
  | |- _ => unfold KHIGH in *; first [assumption | lia]
  end.

Notation rt_real_fflush m := (rw_cells bsegs m 0x175c18 [C8 (Z_to_bv 64 0x15c458)]).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition fflush_i_mid (ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR (Z_to_bv 64 0x74280) (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2
                  a0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15c458) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 80)
    /\ rw_cells bsegs m' (bv_unsigned sp - 80) [CB 56 junk; C8 s1; C8 s0; C8 ra].

Lemma fflush_i_pre : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> KHIGH <= lo ->
  rt_inited m -> rt_real_fflush m -> rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fflush_i_mid ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6c538) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST LO KLO INI RFF RI RSTK.
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 80%nat ST.
  do 5 zstep. zstep.                       (* [comment removed for export] *)
  call_sp tryinit_spec. all: iprem.
  zstep. if_false.                         (* [comment removed for export] *)
  do 3 zstep. zstep.                       (* [comment removed for export] *)
  apply evtF_done. unfold fflush_i_mid.
  replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia.
  replace (bv_unsigned sp - 96) with (bv_unsigned sp + -96) by lia.
  do 16 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption.
  exact FR.
Qed.

(* [comment removed for export] *)
Definition fflush_i_post_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (rav s0v s1v : word) (lo T boff : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 272, bv_unsigned sp); (T + boff, T + boff + 8)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (T + boff) hm_bucket0.

Lemma fflush_i_post : forall RNG x1 sp gp tp t0 t1 t2 x9 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T addr boff : Z) (junk : list byte),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp - 80) -> lo <= bv_unsigned sp - 272 -> KHIGH <= lo ->
  rw_cells bsegs m (bv_unsigned sp - 80) [CB 56 junk; C8 s1v; C8 s0v; C8 rav] ->
  ((addr = 0x178ab0 /\ boff = 2555520) \/ (addr = 0x1788d0 /\ boff = 741600)) ->
  rw_cells bsegs m 0x17ccc0 [C8 (Z_to_bv 64 HMAP)] -> rw_cells bsegs m HMAP [C8 (Z_to_bv 64 T)] ->
  rw_cells bsegs m (T + boff) hm_bucket0 ->
  0x6d4000 <= T -> T + 0x38e000 <= lo -> T mod 8 = 0 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (T + boff) 120 ->
  evtF bsegs RNG (fflush_i_post_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rav s0v s1v lo T boff m)
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp t0 t1 t2 (Z_to_bv 64 addr) x9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x74280) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI ST LO KLO FR HA MAPP MAPC BC TLO THI TAL RI RSTK RB.
  pose proof (munch_refl [(bv_unsigned sp + -272, bv_unsigned sp); (T + boff, T + boff + 8)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO. unfold HMAP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in * by lia.
  unfold hm_bucket0 in BC.
  apply (rw_cells_split_CB bsegs m _ [] 56%nat junk _ [8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  destruct HA as [[-> ->]|[-> ->]].
  - zstep. if_false.                         (* [comment removed for export] *)
    do 5 zstep.
    do 6 zstep.                              (* [comment removed for export] *)
    (* [comment removed for export] *)
    match type of FR with rw_cells _ ?mm ?A [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
      pose proof (rw_cells_recast_mid mm A [c0; c1; c2; c3; c4; c5] [c6]
                    [C1 (Z_to_bv 8 0xaa); C1 (Z_to_bv 8 0xaa); C1 (Z_to_bv 8 0xaa); CB 5 (repeat (Z_to_bv 8 0xaa) 5)] [c7; c8; c9] FR
                    ltac:(cbn; repeat split) ltac:(apply bytes_eq_of_unsigned_i; vm_compute; reflexivity) ltac:(reflexivity)) as FR2
    end.
    cbn [app] in FR2. clear FR.
    do 2 zstep.                              (* [comment removed for export] *)
    do 1 zstep.                              (* [comment removed for export] *)
    (* [comment removed for export] *)
    match type of FR2 with rw_cells _ ?mm ?A [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12] =>
      destruct (proj1 (rw_cells_app bsegs mm A [c0] [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12]) FR2) as [FRA FRB];
      cbn [cells_size csize Nat.add] in FRB; change (Z.of_nat 8) with 8 in FRB;
      destruct (proj1 (rw_cells_app bsegs mm _ [c1; c2; c3; c4; c5; c6; c7; c8] [c9; c10; c11; c12]) FRB) as [HC FRC];
      cbn [cells_size csize Nat.add] in FRC; change (Z.of_nat 43) with 43 in FRC
    end.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in HC, FRC by lia.
    replace (bv_unsigned sp + -72 + 43) with (bv_unsigned sp + -29) in FRC by lia.
    clear FR2 FRB.
    zstep.                                   (* [comment removed for export] *)
    call_sp (acquire_miss_spec RNG lo T (bv_unsigned sp + -72) 0x178ab0 2555520).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- _ \/ _ => first [left; split; reflexivity | right; split; reflexivity]
         | |- rw_cells _ _ _ hm_bucket0 => unfold hm_bucket0; eassumption
         | |- rw_cells _ _ _ _ => unfold HMAP; eassumption
         | |- @eq word _ _ => reflexivity
         | |- _ => unfold HMAP, KHIGH in *; iprem
         end.
    unfold hm_handle_miss, hm_bucket0, HMAP in *.
    zstep. zstep. if_true.                   (* [comment removed for export] *)
    do 2 zstep. zstep.                       (* [comment removed for export] *)
    (* [comment removed for export] *)
    carve_frame 16%nat PC.
    do 3 zstep. zstep. if_true.              (* [comment removed for export] *)
    zstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -96) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -80) end.
    do 2 zstep.
    (* [comment removed for export] *)
    do 4 zstep.
    (* [comment removed for export] *)
    match type of PC0 with rw_cells _ ?mm _ ?hc => match type of FRC with rw_cells _ _ _ ?tc => match type of FRA with rw_cells _ _ _ ?ac =>
      assert (FRJ : rw_cells bsegs mm (bv_unsigned sp + -80) (ac ++ hc ++ tc));
      [ apply (proj2 (rw_cells_app bsegs mm (bv_unsigned sp + -80) ac (hc ++ tc))); split; [exact FRA|];
        cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8; replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by lia;
        apply (proj2 (rw_cells_app bsegs mm (bv_unsigned sp + -72) hc tc)); split; [exact PC0|];
        cbn [cells_size csize Nat.add]; change (Z.of_nat 43) with 43; replace (bv_unsigned sp + -72 + 43) with (bv_unsigned sp + -29) by lia; exact FRC
      | cbn [app] in FRJ; clear FRA PC0 FRC ] end end end.
    match goal with S : stk _ _ lo _ |- _ => release_frame FRJ S (bv_unsigned sp) end.
    zstep. zstep.
    apply evtF_done. unfold fflush_i_post_post, hm_bucket0.
    replace (bv_unsigned sp - 272) with (bv_unsigned sp + -272) by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
  - zstep. if_false.                         (* [comment removed for export] *)
    do 5 zstep.
    do 6 zstep.                              (* [comment removed for export] *)
    (* [comment removed for export] *)
    match type of FR with rw_cells _ ?mm ?A [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9] =>
      pose proof (rw_cells_recast_mid mm A [c0; c1; c2; c3; c4; c5] [c6]
                    [C1 (Z_to_bv 8 0xaa); C1 (Z_to_bv 8 0xaa); C1 (Z_to_bv 8 0xaa); CB 5 (repeat (Z_to_bv 8 0xaa) 5)] [c7; c8; c9] FR
                    ltac:(cbn; repeat split) ltac:(apply bytes_eq_of_unsigned_i; vm_compute; reflexivity) ltac:(reflexivity)) as FR2
    end.
    cbn [app] in FR2. clear FR.
    do 2 zstep.                              (* [comment removed for export] *)
    do 1 zstep.                              (* [comment removed for export] *)
    (* [comment removed for export] *)
    match type of FR2 with rw_cells _ ?mm ?A [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12] =>
      destruct (proj1 (rw_cells_app bsegs mm A [c0] [c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12]) FR2) as [FRA FRB];
      cbn [cells_size csize Nat.add] in FRB; change (Z.of_nat 8) with 8 in FRB;
      destruct (proj1 (rw_cells_app bsegs mm _ [c1; c2; c3; c4; c5; c6; c7; c8] [c9; c10; c11; c12]) FRB) as [HC FRC];
      cbn [cells_size csize Nat.add] in FRC; change (Z.of_nat 43) with 43 in FRC
    end.
    replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) in HC, FRC by lia.
    replace (bv_unsigned sp + -72 + 43) with (bv_unsigned sp + -29) in FRC by lia.
    clear FR2 FRB.
    zstep.                                   (* [comment removed for export] *)
    call_sp (acquire_miss_spec RNG lo T (bv_unsigned sp + -72) 0x1788d0 741600).
    all: lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- _ \/ _ => first [left; split; reflexivity | right; split; reflexivity]
         | |- rw_cells _ _ _ hm_bucket0 => unfold hm_bucket0; eassumption
         | |- rw_cells _ _ _ _ => unfold HMAP; eassumption
         | |- @eq word _ _ => reflexivity
         | |- _ => unfold HMAP, KHIGH in *; iprem
         end.
    unfold hm_handle_miss, hm_bucket0, HMAP in *.
    zstep. zstep. if_true.                   (* [comment removed for export] *)
    do 2 zstep. zstep.                       (* [comment removed for export] *)
    (* [comment removed for export] *)
    carve_frame 16%nat PC.
    do 3 zstep. zstep. if_true.              (* [comment removed for export] *)
    zstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -96) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -80) end.
    do 2 zstep.
    (* [comment removed for export] *)
    do 4 zstep.
    (* [comment removed for export] *)
    match type of PC0 with rw_cells _ ?mm _ ?hc => match type of FRC with rw_cells _ _ _ ?tc => match type of FRA with rw_cells _ _ _ ?ac =>
      assert (FRJ : rw_cells bsegs mm (bv_unsigned sp + -80) (ac ++ hc ++ tc));
      [ apply (proj2 (rw_cells_app bsegs mm (bv_unsigned sp + -80) ac (hc ++ tc))); split; [exact FRA|];
        cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8; replace (bv_unsigned sp + -80 + 8) with (bv_unsigned sp + -72) by lia;
        apply (proj2 (rw_cells_app bsegs mm (bv_unsigned sp + -72) hc tc)); split; [exact PC0|];
        cbn [cells_size csize Nat.add]; change (Z.of_nat 43) with 43; replace (bv_unsigned sp + -72 + 43) with (bv_unsigned sp + -29) by lia; exact FRC
      | cbn [app] in FRJ; clear FRA PC0 FRC ] end end end.
    match goal with S : stk _ _ lo _ |- _ => release_frame FRJ S (bv_unsigned sp) end.
    zstep. zstep.
    apply evtF_done. unfold fflush_i_post_post, hm_bucket0.
    replace (bv_unsigned sp - 272) with (bv_unsigned sp + -272) by lia.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
End CANSEC1.
