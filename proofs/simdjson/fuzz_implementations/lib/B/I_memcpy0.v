(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread I_consts I_qck F_memcpy D_kit I_memcpyw.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Lemma rw_cells_nil0 : forall (m : mem) A, 0 <= A -> A <= 2^64 -> rw_cells bsegs m A [CB 0 []].
Proof.
  intros m A H0 H1. split; [split; [cbn; repeat split; reflexivity|]|]; cbn [cells_bytes cbytes app cells_size csize].
  - apply bytes_at_nil; lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
Qed.

Definition imemcpy0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (d lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - IMEMCPY_DEPTH, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Theorem imemcpy0_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d s lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 0 ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - IMEMCPY_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 <= d < 2^64 -> 0 <= s < 2^64 ->
  icells m -> mem_inv bsegs m ->
  evt bsegs (imemcpy0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x85924) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros -> -> -> ST LO LOLO SPH D0 S0 IC MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  pose proof IC as (G2 & G1 & RM & SHC & RI).
  pose proof (munch_refl [(usp - 2240, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  call (imemcpy_prologue usp d s 0); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia| lia | exact IC| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST1.
  rewrite !Z.add_0_r.

  lstep. lstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 S0. rewrite lxor_ones64 in K1 by lia. lia. }
  lstep. lstep. lstep. if_lit.
  lstep. if_lit. lstep.

  lstep. lstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 D0. rewrite lxor_ones64 in K2 by lia. lia. }
  lstep. lstep. if_lit.
  lstep. if_lit. lstep.

  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  do 3 lstep.
  eapply evt_cut.
  { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] []);
      [ rewrite EUs; apply bytes_at_nil; lia
      | reflexivity
      | rewrite EUd; cbn [Z.to_nat bv_unsigned Z_to_bv]; apply rw_cells_nil0; lia
      | rewrite EUd, EUs, (unsigned_lit 0) by lia; lia
      | assumption ]. }
  intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
  rewrite EUd, (unsigned_lit 0), Z.add_0_r in MUc by lia.
  lazymatch type of MUc with munch _ ?m1 ?m2 =>
    assert (MUe : munch [] m1 m2) by (eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia);
    clear MUc; transport_after_call bsegs m1 m2 MUe WMc; clear MUe WMc end.
  destruct_ands PO.
  replace (ret_pc (Z_to_bv 64 0x85a24)) with (Z_to_bv 64 0x85a24 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  do 12 lstep.
  lazymatch goal with ST3 : stk bsegs _ lo (usp + -2160) |- _ => release_frame FR ST3 (usp + -80); release_frame FRs ST3 usp end.
  lstep.
  unfold imemcpy0_post. sys_finish.
  all: try (rewrite (unsigned_lit usp) by lia).
  all: first [ assumption | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia ].
Qed.
