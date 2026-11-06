(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac ITree Nodes Decode SysStep SFModel.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_syscalls BM_memcpy BM_stdio_lib BX_file BP_policy BP_mjx BP_fwritex.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Export BM_fwrite.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Pol.
Variable P : acc -> Prop.
Hypothesis PSTK : POL_STACK P.
Hypothesis PIMG : POL_IMG P.
Hypothesis PHSH : POL_HSH P.
Hypothesis PLSH : POL_LSH P.
Hypothesis PNUL : POL_NUL P.

(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N lo : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2240, bv_unsigned sp); (Dst, Dst + N)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at bsegs m' Src src
    /\ mjx m'.

Lemma memcpy_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte) (lo : Z),
  bytes_at bsegs m Src src -> length src = Z.to_nat N -> rw_cells bsegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N < 2^40)%Z -> (0 < Src)%Z -> (Src + N < 2^47)%Z -> (0 < Dst)%Z -> (Dst + N < 2^47)%Z -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> (A_CEIL <= lo)%Z -> (lo <= bv_unsigned sp - 2240)%Z -> (bv_unsigned sp <= A_STK_HI)%Z ->
  mjx m -> dst_loc Dst N -> (N = 0 \/ src_loc Src N)%Z ->
  (Src + N <= lo \/ bv_unsigned sp <= Src)%Z -> (Dst + N <= lo \/ bv_unsigned sp <= Dst)%Z ->
  evtA bsegs P (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N lo src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x52b50) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros BA LEN DC SEP HN HS HSN HD HDN MI SK LOC LO SPHI MJ DL SL HJS HJD.
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evtA_mono.
  { eapply (memcpy_callZ P PSTK PIMG PHSH PLSH PNUL) with (src := src) (junk := junk) (lo := lo); rewrite ?ES, ?EN;
      first [exact BA | exact LEN | exact DC | exact SEP | exact MI | exact SK | exact MJ | exact DL | exact SL | lia]. }
  intros ms' Q. unfold memcpy_postZ, memcpy_postv in *. rewrite ES, EN in Q. exact Q.
Qed.

(* [comment removed for export] *)
Definition fwx_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' Fp (file_cells flags wend (wpos + l) wbase wfn bufp bufsize fd mode lbf tail)
    /\ rw_cells bsegs m' wpos [CB (length src) src; CB (cap - length src) (skipn (length src) junk)]
    /\ bytes_at bsegs m' S src
    /\ mjx m'.

Lemma fwx_tail : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l i lo : Z),
  rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells bsegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  rw_cells bsegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
  bytes_at bsegs m S src -> Z.of_nat (length src) = l ->
  stk bsegs m lo (bv_unsigned sp + -64) -> (A_CEIL <= lo)%Z -> (lo <= bv_unsigned sp - FWX_DEPTH)%Z -> (bv_unsigned sp <= A_STK_HI)%Z ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  mjx m -> dst_loc wpos l -> src_loc S l -> (in_stackw Fp 232 \/ (0xa99f8 <= Fp /\ Fp + 232 <= 0xaa000))%Z ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (0 < wpos) -> (wpos + Z.of_nat cap < 2^47) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
  (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wpos + l <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
  (0 <= i) -> (i + l < 2^63) -> (0 < S) -> (S + l < 2^47) -> (l < 2^40) ->
  evtA bsegs P (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x98930) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FR FC DST CAP SRC LEN ST LOC LO SPHI MU WM MI MJ DL SL FPL Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI SHL L40.
  unfold A_CEIL, A_STK_HI, FWX_DEPTH in LOC, LO, SPHI.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
  assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  assert (PFP : forall a k, (Fp <= a)%Z -> (a + Z.of_nat k <= Fp + 232)%Z -> P (Z_to_bv 64 a, k)).
  { intros a k Ha Hk. unfold in_stackw, A_CEIL, A_STK_HI in FPL. destruct FPL as [[X1 X2]|[X1 X2]]; [apply PSTK; lia| apply PIMG; lia]. }
  hideH FPL. hideH DL. hideH SL.
  unfold file_cells in FC.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB bsegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
  cbn [mk_CB_cells app] in DST.
  apply (proj1 (BP_fwritex.rw_cells_app bsegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
  cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
  step. step. step.
  replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
  assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = (bv_unsigned sp + -64)%Z) by (apply unsigned_lit; lia).
  callA memcpy_callw.
  1:{ exact SRC. }
  1:{ rewrite Nat2Z.id. reflexivity. }
  1:{ rewrite Nat2Z.id. exact DSTa. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
  1:{ rewrite USP. exact ST. } 1:{ unfold A_CEIL; lia. } 1:{ rewrite USP; lia. } 1:{ rewrite USP; unfold A_STK_HI; lia. }
  1:{ exact MJ. } 1:{ unhideH DL. rewrite LEN. exact DL. } 1:{ right. unhideH SL. rewrite LEN. exact SL. }
  1:{ rewrite USP. lia. } 1:{ rewrite USP. lia. }
  rewrite ?USP in *. rewrite !Nat2Z.id in *.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48)] mx) as MUT; pose proof (wmono_refl bsegs mx) as WMT;
    match goal with H : mjx mx |- _ => rename H into MJ1 end end.
  do 4 step.
  do 9 step.
  match goal with H : stk bsegs _ lo _ |- _ => rename H into ST' end.
  release_frame FR ST' (bv_unsigned sp).
  rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST' : rw_cells bsegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
      by (match goal with H : rw_cells bsegs mm wpos [CB (length src) src] |- _ =>
            apply (proj2 (BP_fwritex.rw_cells_app bsegs _ _ [_] _)); split; [exact H|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb end)
  end.
  cbn [app] in DST'. rewrite !LEN in *.
  apply evtA_done. unfold fwx_ret_post, file_cells.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [ reflexivity | ].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  (* [comment removed for export] *)
  eapply mjx_transport; [exact MJ1| exact MUT| exact WMT|].
  unhideH FPL; unfold in_stackw, A_CEIL, A_STK_HI in FPL.
  repeat (apply Forall_cons; [unfold mjx_ok_iv, A_CEIL, A_STK_HI; cbn [fst snd]; lia|]); apply Forall_nil.
Qed.

(* [comment removed for export] *)
Lemma fwx_fit_plain : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l lo : Z),
  rw_cells bsegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  rw_cells bsegs m wpos [CB cap junk] -> Z.of_nat cap = wend - wpos ->
  bytes_at bsegs m S src -> Z.of_nat (length src) = l ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 l -> a2 = Z_to_bv 64 Fp ->
  (0 < wend < 2^47) -> (0 < wpos) -> (l <= wend - wpos) -> (0 < S) -> (S + l < 2^47) -> (l < 2^40) ->
  (2^31 <= lbf < 2^32) ->
  stk bsegs m lo (bv_unsigned sp) -> (A_CEIL <= lo)%Z -> (lo <= bv_unsigned sp - FWX_DEPTH)%Z -> (bv_unsigned sp <= A_STK_HI)%Z -> (bv_unsigned sp < 2^63) ->
  mem_inv bsegs m -> mjx m -> dst_loc wpos l -> src_loc S l -> (in_stackw Fp 232 \/ (0xa99f8 <= Fp /\ Fp + 232 <= 0xaa000))%Z ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (wend <= lo \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wend <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
  evtA bsegs P (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x98838) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI SL2 L40 LBF ST LOC LO SPHI SP63 MI MJ DL SL FPL Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3.
  unfold A_CEIL, A_STK_HI, FWX_DEPTH in LOC, LO, SPHI.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (PFP : forall a k, (Fp <= a)%Z -> (a + Z.of_nat k <= Fp + 232)%Z -> P (Z_to_bv 64 a, k)).
  { intros a k Ha Hk. unfold in_stackw, A_CEIL, A_STK_HI in FPL. destruct FPL as [[X1 X2]|[X1 X2]]; [apply PSTK; lia| apply PIMG; lia]. }
  hideH FPL. hideH DL. hideH SL.
  unfold file_cells in FC.
  carve_frame 64%nat ST.
  do 13 step.
  if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
  do 3 step.
  if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
  do 3 step.
  pose proof (BP_fwritex.sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
  specialize (NEG ltac:(lia)).
  if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
  unhideH FPL. unhideH DL. unhideH SL.
  lazymatch goal with MUx : munch _ m ?mx, WMx : wmono bsegs m ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MJx : mjx mx) by (eapply mjx_transport; [exact MJ| exact MUx| exact WMx|];
      unfold dst_loc, in_stackw, A_CEIL, A_STK_HI in DL, FPL;
      repeat (apply Forall_cons; [unfold mjx_ok_iv, A_CEIL, A_STK_HI; cbn [fst snd]; lia|]); apply Forall_nil) end.
  eapply fwx_tail; [exact FR | exact FC | exact DST | lia | exact SRC | exact LEN | exact ST | unfold A_CEIL; lia | unfold FWX_DEPTH; lia | unfold A_STK_HI; lia
                  | eassumption | eassumption | exact MI | exact MJx | exact DL | exact SL | exact FPL | lia ..].
Qed.

End Pol.
End RC__1.
