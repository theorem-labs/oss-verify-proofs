(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ITree Nodes Decode SysStep MonadX ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_m2s I_consts I_qck I_memcpyw FX_lib FX_Layout FX_Stdio_iface F_towrite F_fwritex_gen F_fwritex I_memcpy0.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation bsegs := ImageA.bsegs.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition F_FWRITE : Z := 0x168e70.
Definition FWRITE0_DEPTH : Z := 128 + 2240.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition fwx_ret0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (i lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail).

Lemma fwx_tail0 : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S i lo : Z),
  rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells bsegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  stk bsegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64 - 2240) -> (bv_unsigned sp < 2^63) ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (0 <= wpos < 2^64) -> (0 <= S < 2^64) -> (0 <= i < 2^63) ->
  kHighShadowEnd + 8 <= lo -> icells m ->
  evt bsegs (fwx_ret0_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail i lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x168e30) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FR FC ST LO0 SPHI MU WM MI Fp0 SEPF WP0 SR I0 HSH IC.
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  unfold file_cells in FC. unfold kHighShadowEnd in *.
  assert (EUf : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  step. step. step. step.
  eapply evt_cut.
  { eapply (imemcpy0_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wpos S lo);
      first [ reflexivity | exact IC | exact MI | rewrite ?EUf; first [ exact ST | unfold kHighShadowEnd in *; lia ] ]. }
  intros ms' PO. unfold imemcpy0_post in PO. rewrite EUf in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call bsegs ma mb MU2 WM2 end.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.
  clear MU2 WM2.
  do 4 step.
  do 9 step.
  release_frame FR ST2 (bv_unsigned sp).
  replace (wpos + 0) with wpos by lia. replace (i + 0) with i by lia.
  unfold fwx_ret0_post, file_cells. sys_finish.
Qed.

Definition fwrite0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 148)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail).

Lemma fwrite0_active_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp S : Z) (flags : word) (wpos wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (lo : Z),
  rw_cells bsegs m Fp (file_cells flags (bufp + bufsize) wpos bufp wfn bufp bufsize fd mode lbf tail) ->
  (lbf = 10 \/ lbf = 0xffffffff) ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 Fp -> (Fp = RSTDOUT \/ Fp = RSTDERR) ->
  (0 <= bufp) -> (bufp <= wpos <= bufp + bufsize) -> (0 < bufp + bufsize < 2^64) ->
  (0 <= Fp) -> (bv_unsigned sp <= S < 2^64) ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE0_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^63) ->
  (Fp + 232 <= lo) -> kHighShadowEnd + 8 <= lo -> icells m ->
  mem_inv bsegs m ->
  evt bsegs (fwrite0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags (bufp + bufsize) wpos bufp wfn bufp bufsize fd mode lbf tail lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_FWRITE) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FC LBF -> -> -> -> FPC B0 WP WEND Fp0 SR ST LO GLO SPHI SEPF HSH IC MI.
  pose proof IC as (G2 & G1 & RM & SHC & RI). clear IC. unfold kHighShadowEnd in HSH.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_FWRITE, FWRITE0_DEPTH, GLOBALS_TOP in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 148)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
         eapply fwx_tail0 with (lo := lo) (i := 0) (S := S) (Fp := Fp) (m0 := mm) end;
         first [ exact FR0 | exact FC | eassumption | apply munch_refl | apply wmono_refl | (split; [eassumption | split; [eassumption | split; [eassumption | split; eassumption]]]) | unfold kHighShadowEnd in *; lia ] | ].
  all: cbv beta; intros ms' PO;
       destruct PO as (t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2);
       lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call bsegs ma mb MU2 WM2 end;
       unname_sp.
  all: lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.

  all: step; step; if_lit; step; step; step; step.
  all: do 8 step.
  all: release_frame FR ST2 (bv_unsigned sp).
  all: step.
  all: apply evt_done; unfold fwrite0_post; sys_finish.
Qed.

Definition fwrite0_idle_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (wfn bufp bufsize fd : Z) (lbf : Z) (tail : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' Fp (file_cells flags (bufp + bufsize) bufp bufp wfn bufp bufsize fd mode' lbf tail).

Lemma fwrite0_idle_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp S : Z) (flags mode : word) (wpos wbase wfn bufp bufsize fd : Z) (lbf : Z) (tail : list byte) (lo : Z),
  rw_cells bsegs m Fp (file_cells flags 0 wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  Z.land (bv_unsigned flags) 8 = 0 ->
  (lbf = 10 \/ lbf = 0xffffffff) ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 Fp -> (Fp = RSTDOUT \/ Fp = RSTDERR) ->
  (0 <= bufp) -> (0 <= bufsize) -> (0 < bufp + bufsize < 2^64) ->
  (0 <= Fp) -> (bv_unsigned sp <= S < 2^64) ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FWRITE0_DEPTH) -> (GLOBALS_TOP <= lo) -> (bv_unsigned sp < 2^63) ->
  (Fp + 232 <= lo) -> kHighShadowEnd + 8 <= lo -> icells m ->
  mem_inv bsegs m ->
  evt bsegs (fwrite0_idle_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags wfn bufp bufsize fd lbf tail lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 F_FWRITE) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FC NOWR LBF -> -> -> -> FPC B0 BS0 WEND Fp0 SR ST LO GLO SPHI SEPF HSH IC MI.
  pose proof IC as (G2 & G1 & RM & SHC & RI). clear IC. unfold kHighShadowEnd in HSH.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold F_FWRITE, FWRITE0_DEPTH, GLOBALS_TOP in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp, Fp + 232)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
  lazymatch type of MU2 with munch _ ?ma ?mb => transport_after_call bsegs ma mb MU2 WM2 end. clear MU2 WM2.
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
         eapply fwx_tail0 with (lo := lo) (i := 0) (S := S) (Fp := Fp) (m0 := mm) end;
         first [ exact FR0 | eassumption | apply munch_refl | apply wmono_refl | (split; [eassumption | split; [eassumption | split; [eassumption | split; eassumption]]]) | unfold kHighShadowEnd in *; lia | unfold file_cells; hyp_by_addr | match goal with |- ?g => idtac "LEFT" g end ] | ].
  all: cbv beta; intros ms' PO;
       destruct PO as (x0' & x1' & x2' & b1' & b2' & b3'' & b4' & b5' & b6' & b7' & x3' & x4' & x5' & x6' & m3 & -> & MU3 & WM3 & MI3 & ST3 & FC3);
       lazymatch type of MU3 with munch _ ?ma ?mb => transport_after_call bsegs ma mb MU3 WM3 end;
       unname_sp.
  all: lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.
  all: step; step; if_lit; step; step; step; step.
  all: do 8 step.
  all: release_frame FR ST3 (bv_unsigned sp).
  all: step.
  all: apply evt_done; unfold fwrite0_idle_post; sys_finish.
  all: first [ exact FC3 ].
Qed.
