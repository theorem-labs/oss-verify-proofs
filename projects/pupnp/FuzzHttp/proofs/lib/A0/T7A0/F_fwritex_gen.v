(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ITree Nodes Decode SysStep SFModel.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Shadow Contracts IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit Stdio_base.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition OUT_DEPTH0 : Z := 64 + A0_RT_STACK.

Section FWX.
Context {HC : HasCeiling}.
Hypothesis MCI : memcpy_i_stmt.

Definition fwx_nofit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp S l wfn lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 (Z_to_bv 64 wfn) t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 wfn) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

#[using="Type"] Lemma fwx_nofit : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) (S l lo : Z),
  rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
  (0 < wend < 2^64) -> (0 <= wpos <= wend) -> (wend - wpos < l < 2^64) -> (0 <= S < 2^64) -> (0 <= wfn < 2^64) -> (wfn mod 2 = 0) ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64) -> (0 <= lo) ->
  mem_inv asegs m ->
  (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  evt asegs (fwx_nofit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp S l wfn lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9af84) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros FC -> -> -> WEND WPOS L SR WFN WFE ST LO LO0 MI SEPF.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold file_cells in FC.
  carve_frame 64%nat ST.
  do 13 step.
  if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
  do 3 step.
  if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
  do 13 step.
  rewrite (ret_pc_even wfn) by (first [lia | exact WFE]).
  release_frame FR ST (bv_unsigned sp).
  unfold fwx_nofit_post. sys_finish.
Qed.

Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' Fp (file_cells flags wend (wpos + l) wbase wfn bufp bufsize fd mode lbf tail)
    /\ rw_cells asegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
    /\ bytes_at asegs m' S src
    /\ asan_env asegs m'.

#[using="MCI"] Lemma fwx_tail : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l i lo : Z),
  rw_cells asegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  rw_cells asegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
  bytes_at asegs m S src -> Z.of_nat (length src) = l ->
  stk asegs m lo (bv_unsigned sp + -64) -> (0 <= lo <= bv_unsigned sp - 64 - A0_RT_STACK) -> (alloc_ceiling <= lo) -> (bv_unsigned sp < 2^63) ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= alloc_ceiling \/ bv_unsigned sp <= wpos) ->
  (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wpos + l <= S) -> (S + l <= alloc_ceiling \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
  (0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
  asan_env asegs m0 -> shw m0 wpos l -> shw m0 S l -> icpt_rng wpos l -> icpt_rng S l ->   env_safe [(Fp, Fp + 232); (wpos, wpos + l)] -> app_iv (Fp, Fp + 232) -> app_iv (wpos, wpos + l) ->
  evt asegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9b07c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros FR FC DST CAP SRC LEN ST LO0 CLO SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI ENV SHD SHS ICD ICS ES AF AW.
  pose proof (@alloc_ceiling_bounds HC) as CEILB. unfold A0_RT_STACK in LO0.
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
  assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  unfold file_cells in FC.

  apply (rw_cells_split_CB asegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
  cbn [mk_CB_cells app] in DST.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
  cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
  step. step. step.
  replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
  assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
  call (memcpy_i_callq MCI lo).
  1:{ exact SRC. }
  1:{ rewrite Nat2Z.id. reflexivity. }
  1:{ rewrite Nat2Z.id. exact DSTa. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
  1:{ rewrite LEN. eapply shw_frame; [exact SHD | exact MU | app_ivs_tac]. }
  1:{ rewrite LEN. eapply shw_frame; [exact SHS | exact MU | app_ivs_tac]. }
  1:{ rewrite LEN. exact ICD. }
  1:{ rewrite LEN. exact ICS. }
  1:{ eapply asan_env_frame; [exact ENV | exact MU | exact WM | env_safe_tac]. }
  1:{ exact ST. }
  1:{ lia. } 1:{ unfold A0_RT_STACK in *; lia. } 1:{ lia. } 1:{ lia. } 1:{ rewrite LEN. env_safe_tac. } 1:{ lia. }
  rewrite !Nat2Z.id in *.
  rename PC into ST. clear PC0.
  do 4 step.
  do 9 step.
  release_frame FR ST (bv_unsigned sp).
  rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST' : rw_cells asegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
      by (apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact PC1|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb);
    assert (ENV' : asan_env asegs mm) by (eapply asan_env_frame; [exact ENV | exact MU | exact WM | env_safe_tac])
  end.
  cbn [app] in DST'. rewrite !LEN in *.
  unfold fwx_ret_post, file_cells. sys_finish.
Qed.

#[using="MCI"] Lemma fwx_fit_plain : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l lo : Z),
  rw_cells asegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  rw_cells asegs m wpos [CB cap junk] -> Z.of_nat cap = wend - wpos ->
  bytes_at asegs m S src -> Z.of_nat (length src) = l ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
  (0 < wend < 2^64) -> (0 <= wpos) -> (l <= wend - wpos) -> (S < 2^64) ->
  (2^31 <= lbf < 2^32) ->
  stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - OUT_DEPTH0) -> (0 <= lo) -> (alloc_ceiling <= lo) -> (bv_unsigned sp < 2^63) ->
  mem_inv asegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (wend <= alloc_ceiling \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wend <= S) -> (S + l <= alloc_ceiling \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
  asan_env asegs m -> shw m wpos l -> shw m S l -> icpt_rng wpos l -> icpt_rng S l ->   env_safe [(Fp, Fp + 232); (wpos, wpos + l)] -> app_iv (Fp, Fp + 232) -> app_iv (wpos, wpos + l) ->
  evt asegs (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9af84) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI LBF ST LO LO0 CLO SPHI MI Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 ENV SHD SHS ICD ICS ES AF AW.
  unfold OUT_DEPTH0, A0_RT_STACK in LO.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold file_cells in FC.
  carve_frame 64%nat ST.
  do 13 step.
  if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
  do 3 step.
  if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
  do 3 step.
  pose proof (sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
  specialize (NEG ltac:(lia)).
  if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
  eapply fwx_tail; [exact FR | exact FC | exact DST | lia | exact SRC | exact LEN | exact ST | unfold A0_RT_STACK in *; lia | lia | lia | exact MU | exact WM | exact MI | first [assumption | lia] ..].
Qed.
End FWX.
