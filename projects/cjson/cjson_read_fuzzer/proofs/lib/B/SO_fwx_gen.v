(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac ITree Nodes Decode SysStep SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import F_syscalls F_memcpy F_pad F_fmt_fp_lib Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import SO_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require F_fwritex.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition FWX_TAIL_DEPTH : Z := AINTRIN_STACK.   (* [comment removed for export] *)

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
    /\ bytes_at bsegs m' S src.

Lemma fwx_tail : forall (x1 ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0v s1v s2v s3v s4v s5v : word) (j8 : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem)
    (Fp : Z) (flags : word) (wend wpos wbase wfn bufp bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte)
    (cap : nat) (junk src : list byte) (S l i lo : Z),
  rw_cells bsegs m (bv_unsigned sp + -64) [CB 8 j8; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
  rw_cells bsegs m Fp (file_cells flags wend wpos wbase wfn bufp bufsize fd mode lbf tail) ->
  rw_cells bsegs m wpos [CB cap junk] -> (length src <= cap)%nat ->
  bytes_at bsegs m S src -> Z.of_nat (length src) = l ->
  stk bsegs m lo (bv_unsigned sp + -64) -> (0 <= lo /\ lo + FWX_TAIL_DEPTH <= bv_unsigned sp - 64) -> (bv_unsigned sp < 2^63) ->
  munch [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (0 <= wpos) -> (wpos + Z.of_nat cap < 2^64) -> (wpos + Z.of_nat cap <= lo \/ bv_unsigned sp <= wpos) ->
  (wpos + Z.of_nat cap <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wpos + l <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp + 40 \/ Fp + 48 <= S) ->
  (0 <= i) -> (i + l < 2^63) -> (S < 2^64) ->
  (* [comment removed for export] *)
  icpt_cells m -> alloc_ceiling <= lo -> l < 2^31 ->
  app_range S l -> app_range wpos l -> wr_range_ok wpos l ->
  (0 < l -> shadow_ok m S l) -> (0 < l -> shadow_ok m wpos l) ->
  evt bsegs (fwx_ret_post ra sp gp tp s0v s1v s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l (i + l) lo m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 l)
               (Z_to_bv 64 wpos) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 S) (Z_to_bv 64 i) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x93b1c) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FR FC DST CAP SRC LEN ST LO0 SPHI MU WM MI Fp0 SEPF W0 WHI SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 I0 IL SHI.
  intros IC CEIL L31 ARs ARd WRd SOs SOd.
  pose proof (app_range_lt47 _ _ ARs) as RS47. pose proof (app_range_lt47 _ _ ARd) as RD47.
  pose proof (rw_cells_bound _ _ _ _ DST) as BD. cbn [cells_size csize Nat.add] in BD. rewrite Nat.add_0_r in BD.
  assert (LJ : length junk = cap) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
  pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE. unfold FWX_TAIL_DEPTH in LO0. pose proof AINTRIN_STACK_val as AIS.
  unfold file_cells, file_cells_r, AF_STDIO_CLOSE, AF_STDIO_SEEK in FC.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB bsegs _ _ [] cap junk [] [length src; cap - length src]%nat) in DST; [ | cbn; lia ].
  cbn [mk_CB_cells app] in DST.
  apply (proj1 (F_fwritex.rw_cells_app bsegs _ _ [_] _)) in DST. destruct DST as [DSTa DSTb].
  cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
  step. step. step.
  replace (Z_to_bv 64 l : word) with (Z_to_bv 64 (Z.of_nat (length src)) : word) by (rewrite LEN; reflexivity).
  assert (SEPfr : bv_unsigned sp + -64 + 64 <= wpos \/ wpos + Z.of_nat (length src) <= bv_unsigned sp + -64) by lia.
  sepM. callsp memcpy_icpt_callv.
  1:{ exact SRC. }
  1:{ reflexivity. }
  1:{ rewrite Nat2Z.id. exact DSTa. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact MI. }
  1:{ exact IC. } 1:{ exact ST. } 1:{ exact CEIL. } 1:{ lia. } 1:{ lia. }
  1:{ rewrite LEN. exact ARs. } 1:{ rewrite LEN. exact ARd. } 1:{ rewrite LEN. exact WRd. }
  1:{ rewrite LEN. exact SOs. } 1:{ rewrite LEN. exact SOd. }
  1:{ lia. } 1:{ lia. }
  rewrite !Nat2Z.id in *.
  change bsegs with bsegs in *.
  match goal with H : stk bsegs _ lo _ |- _ => rename H into ST end.
  sepM. do 4 step.
  do 9 step.
  release_frame FR ST (bv_unsigned sp).
  rewrite firstn_all2 in DSTb by (rewrite length_skipn; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (DST' : rw_cells bsegs mm wpos ([CB (length src) src] ++ [CB (cap - length src)%nat (skipn (length src) junk)]))
      by (apply (proj2 (F_fwritex.rw_cells_app bsegs _ _ [_] _)); split; [exact PC|]; cbn [cells_size csize]; rewrite Nat.add_0_r; exact DSTb)
  end.
  cbn [app] in DST'. rewrite !LEN in *.
  unfold fwx_ret_post, file_cells, file_cells_r, AF_STDIO_CLOSE, AF_STDIO_SEEK. sys_finish.
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
  (0 < wend < 2^64) -> (0 <= wpos) -> (l <= wend - wpos) -> (S < 2^64) ->
  (2^31 <= lbf < 2^32) ->
  stk bsegs m lo (bv_unsigned sp) -> (lo + 64 + FWX_TAIL_DEPTH <= bv_unsigned sp) -> (0 <= lo) -> (bv_unsigned sp < 2^63) ->
  mem_inv bsegs m ->
  (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
  (wend <= lo \/ bv_unsigned sp <= wpos) -> (wend <= Fp \/ Fp + 232 <= wpos) ->
  (S + l <= wpos \/ wend <= S) -> (S + l <= lo \/ bv_unsigned sp <= S) -> (S + l <= Fp \/ Fp + 232 <= S) ->
  (* [comment removed for export] *)
  icpt_cells m -> alloc_ceiling <= lo -> l < 2^31 ->
  app_range S l -> app_range wpos l -> wr_range_ok wpos l ->
  (0 < l -> shadow_ok m S l) -> (0 < l -> shadow_ok m wpos l) ->
  evt bsegs (fwx_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp flags wend wpos wbase wfn bufp bufsize fd mode lbf tail cap junk src S l l lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x93a24) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros FC DST CAPE SRC LEN -> -> -> WEND W0 FIT SHI LBF ST LO LO0 SPHI MI Fp0 SEPF SEPW1 SEPW2 SEPS1 SEPS2 SEPS3.
  intros IC CEIL L31 ARs ARd WRd SOs SOd.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. unfold FWX_TAIL_DEPTH in LO. pose proof AINTRIN_STACK_val as AIS.
  pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE.
  pose proof (munch_refl [(lo, bv_unsigned sp); (Fp + 40, Fp + 48); (wpos, wpos + l)] m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MUf.   (* [comment removed for export] *)
  pose proof (wmono_refl bsegs m) as WM.
  unfold file_cells, file_cells_r, AF_STDIO_CLOSE, AF_STDIO_SEEK in FC.
  carve_frame 64%nat ST.
  sepM. do 13 step.
  if_cases Hw; zify_cond Hw. 1:{ exfalso. lia. }
  do 3 step.
  if_cases Hr; zify_cond Hr. 2:{ exfalso. rewrite land_W64, Z.mod_small in Hr by lia. lia. }
  do 3 step.
  pose proof (F_fwritex.sx32_neg (Z_to_bv 64 lbf)) as NEG. rewrite unsigned_lit in NEG by lia. rewrite Z.mod_small in NEG by lia.
  specialize (NEG ltac:(lia)).
  if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  assert (AIf : Forall app_iv [(bv_unsigned sp - 64, bv_unsigned sp)])
    by (apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IC1 : icpt_cells mm) by (eapply icpt_cells_munch; [exact IC| exact MUf|]; unfold icpt_cell_ivs; repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil);
    assert (SOs1 : 0 < l -> shadow_ok mm S l) by (intros H0; eapply shadow_ok_munch_app; [apply SOs; exact H0| exact MUf| lia| exact ARs| exact AIf]);
    assert (SOd1 : 0 < l -> shadow_ok mm wpos l) by (intros H0; eapply shadow_ok_munch_app; [apply SOd; exact H0| exact MUf| lia| exact ARd| exact AIf])
  end.
  clear MUf.
  eapply fwx_tail; [exact FR | exact FC | exact DST | | exact SRC | exact LEN | exact ST | | | eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia | exact WM | exact MI | ..].
  all: try (cut_to CAPE LEN FIT SPHI Fp0 SEPF W0 WEND LO SEPW1 SEPW2 SEPS1 SEPS2 SEPS3 AIS Hw L31 SHI CEIL; lia).
  all: first [exact IC1 | exact CEIL | exact ARs | exact ARd | exact WRd | exact SOs1 | exact SOd1 | unfold FWX_TAIL_DEPTH; lia].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
