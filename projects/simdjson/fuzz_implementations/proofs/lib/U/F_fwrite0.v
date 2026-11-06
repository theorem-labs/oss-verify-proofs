(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX Image.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Printf_lib Stdio_iface F_towrite F_fwritex_gen.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition F_FWRITE : Z := 0xcaa2c.
Definition FWRITE0_DEPTH : Z := 128.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition fwrite0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (cap : nat) (junk : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 148); (wpos, wpos)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail)
    /\ rw_cells usegs m' wpos [CB cap junk].

Lemma fwrite0_active_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp S : Z) (flags : word) (wpos wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (cap : nat) (junk : list byte) (lo : Z),
  rw_cells usegs m Fp (file_cells flags (bufp + bufsize) wpos bufp wfn bufp bufsize fd mode lbf tail) ->
  rw_cells usegs m wpos [CB cap junk] ->
  (lbf = 10 \/ lbf = 0xffffffff) ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 Fp ->
  (0 <= bufp) -> (bufp <= wpos <= bufp + bufsize) -> (0 < bufp + bufsize < 2^64) -> (wpos + Z.of_nat cap < 2^64) ->
  (0 <= Fp) -> (bv_unsigned sp <= S < 2^64) ->
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE0_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^63) ->
  (Fp + 232 <= lo) -> (wpos + Z.of_nat cap <= lo) -> (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  mem_inv usegs m ->
  evt usegs (fwrite0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags (bufp + bufsize) wpos bufp wfn bufp bufsize fd mode lbf tail cap junk lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_FWRITE) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros FC DST LBF -> -> -> -> B0 WP WEND CAPHI Fp0 SR ST LO GLO SPHI SEPF SEPW SEPW2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_FWRITE, FWRITE0_DEPTH, GLOBALS_TOP in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 148); (wpos, wpos)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold file_cells in FC.

  carve_frame 64%nat ST.
  do 8 step.
  do 3 step.
  step.
  step.
  try match goal with |- context [Z_to_bv 64 (0 * 1)] => change (Z_to_bv 64 (0 * 1)) with (Z_to_bv 64 0 : word) end.
  step. if_lit.
  do 2 step.
  step.

  carve_frame 64%nat ST.
  do 8 lstep.
  do 2 step.
  step.
  step.
  step. if_cases Hw; zify_cond Hw.
  1:{ exfalso. clear - Hw WEND B0 WP. try rewrite land_W64 in Hw. try rewrite Z.mod_small in Hw by lia. try rewrite unsigned_lit in Hw by lia. lia. }
  step.
  step.
  step. if_cases Hr; zify_cond Hr.
  2:{ exfalso. clear - Hr. rewrite land_W64 in Hr. pose proof (Z.mod_pos_bound (bufp + bufsize - wpos) (2^64) ltac:(lia)). lia. }
  step.
  step.

  destruct LBF as [-> | ->];
    [ step; if_lit; step; if_lit
    | step; if_lit ].
  all: name_sp sp (-64)%Z.
  all: replace (bv_unsigned sp + -128) with (bv_unsigned sp0 + -64) in * by lia.
  all: eapply evt_cut; [ lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply fwx_tail with (lo := lo) (cap := cap) (src := []) (i := 0) (S := S) (Fp := Fp) (junk := junk) (m0 := mm) end;
         [ exact FR0 | exact FC | exact DST | cbn; lia | apply bytes_at_nil; lia | reflexivity | eassumption | cbn; lia | lia
         | apply munch_refl | apply wmono_refl | eassumption | lia .. ] | ].
  all: cbv beta; intros ms' PO;
       destruct PO as (t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2);
       lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call usegs ma mb MU2 WM2 end;
       unname_sp.
  all: lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.
  all: cbn [length Nat.sub skipn] in DST2; rewrite Z.add_0_r in FC2.

  all: step; step; if_lit; step; step; step; step.
  all: do 8 step.
  all: release_frame FR ST2 (bv_unsigned sp).
  all: step.
  all: rewrite Nat.sub_0_r in DST2; change (skipn 0 junk) with junk in DST2;
       apply (proj1 (F_fwritex.rw_cells_app usegs _ _ [_] _)) in DST2; destruct DST2 as [_ DST2]; cbn [cells_size csize Nat.add] in DST2; rewrite Z.add_0_r in DST2.
  all: apply evt_done; unfold fwrite0_post; sys_finish.
Qed.

Definition fwrite0_idle_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (wfn bufp bufsize fd : Z) (lbf : Z) (tail : list byte) (cap : nat) (junk : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (bufp, bufp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' Fp (file_cells flags (bufp + bufsize) bufp bufp wfn bufp bufsize fd mode' lbf tail)
    /\ rw_cells usegs m' bufp [CB cap junk].

Lemma fwrite0_idle_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp S : Z) (flags mode : word) (wpos wbase wfn bufp bufsize fd : Z) (lbf : Z) (tail : list byte) (cap : nat) (junk : list byte) (lo : Z),
  rw_cells usegs m Fp (file_cells flags 0 wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  Z.land (bv_unsigned flags) 8 = 0 ->
  rw_cells usegs m bufp [CB cap junk] ->
  (lbf = 10 \/ lbf = 0xffffffff) ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 Fp ->
  (0 <= bufp) -> (0 <= bufsize) -> (0 < bufp + bufsize < 2^64) -> (bufp + Z.of_nat cap < 2^64) ->
  (0 <= Fp) -> (bv_unsigned sp <= S < 2^64) ->
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE0_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^63) ->
  (Fp + 232 <= lo) -> (bufp + Z.of_nat cap <= lo) -> (bufp + Z.of_nat cap <= Fp \/ Fp + 232 <= bufp) ->
  mem_inv usegs m ->
  evt usegs (fwrite0_idle_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags wfn bufp bufsize fd lbf tail cap junk lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_FWRITE) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros FC NOWR DST LBF -> -> -> -> B0 BS0 WEND CAPHI Fp0 SR ST LO GLO SPHI SEPF SEPW SEPW2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_FWRITE, FWRITE0_DEPTH, GLOBALS_TOP in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232); (bufp, bufp)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold file_cells in FC.

  carve_frame 64%nat ST.
  do 8 step.
  do 3 step.
  step.
  step.
  try match goal with |- context [Z_to_bv 64 (0 * 1)] => change (Z_to_bv 64 (0 * 1)) with (Z_to_bv 64 0 : word) end.
  step. if_lit.
  do 2 step.
  step.

  carve_frame 64%nat ST.
  do 8 lstep.
  do 2 step.
  step.
  step.
  step. if_lit.
  step.
  step.
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (towrite_proof) with (flags := flags) (wend := 0) (wpos := wpos) (wbase := wbase) (writefn := wfn) (buf := bufp) (bufsize := bufsize) (fd := fd) (mode := mode) (lbf := lbf) (tail := tail) end;
      [ rewrite unsigned_lit by lia; unfold file_cells; hyp_by_addr | exact NOWR | lia | lia | lia | assumption ]. }
  cbv beta. intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mode' & m2 & -> & MU2 & WM2 & MI2 & FC2).
  rewrite unsigned_lit in MU2, FC2 by lia.
  lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call usegs ma mb MU2 WM2 end. clear MU2 WM2.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.
  unfold file_cells in FC2.
  step. if_lit.
  step.
  step.
  step.
  step.
  step. if_cases Hr; zify_cond Hr.
  2:{ exfalso. clear - Hr. rewrite land_W64 in Hr. pose proof (Z.mod_pos_bound (bufp + bufsize - bufp) (2^64) ltac:(lia)). lia. }
  step.
  step.
  destruct LBF as [-> | ->];
    [ step; if_lit; step; if_lit
    | step; if_lit ].
  all: name_sp sp (-64)%Z.
  all: replace (bv_unsigned sp + -128) with (bv_unsigned sp0 + -64) in * by lia.
  all: eapply evt_cut; [ lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply fwx_tail with (lo := lo) (cap := cap) (src := []) (i := 0) (S := S) (Fp := Fp) (junk := junk) (m0 := mm) end;
         [ exact FR0 | unfold file_cells; hyp_by_addr | exact DST | cbn; lia | apply bytes_at_nil; lia | reflexivity | eassumption | cbn; lia | lia
         | apply munch_refl | apply wmono_refl | eassumption | lia .. ] | ].
  all: cbv beta; intros ms' PO;
       destruct PO as (x0' & x1' & x2' & b1' & b2' & b3'' & b4' & b5' & b6' & b7' & x3' & x4' & x5' & x6' & m3 & -> & MU3 & WM3 & MI3 & ST3 & FC3 & DST3 & SRC3);
       lazymatch type of MU3 with munch _ ?ma ?mb => transport_after_call usegs ma mb MU3 WM3 end;
       unname_sp.
  all: lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.
  all: cbn [length Nat.sub skipn] in DST3; rewrite Z.add_0_r in FC3.
  all: step; step; if_lit; step; step; step; step.
  all: do 8 step.
  all: release_frame FR ST3 (bv_unsigned sp).
  all: step.
  all: rewrite Nat.sub_0_r in DST3; change (skipn 0 junk) with junk in DST3;
       apply (proj1 (F_fwritex.rw_cells_app usegs _ _ [_] _)) in DST3; destruct DST3 as [_ DST3]; cbn [cells_size csize Nat.add] in DST3; rewrite Z.add_0_r in DST3.
  all: apply evt_done; unfold fwrite0_idle_post; sys_finish.
  all: first [ exact FC3 | exact DST3 ].
Qed.
