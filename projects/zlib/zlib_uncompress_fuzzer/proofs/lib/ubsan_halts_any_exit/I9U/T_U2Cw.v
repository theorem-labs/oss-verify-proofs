(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U Require TBase T_Entry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S Require S_HeadA S_Check.

Module T_Uw.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_UW_BODY : Z := 97124.
Definition L_UW_EPI : Z := 97356.
Definition L_UW_TAIL : Z := 97396.

Section Uw.
Context {RCa1 : RunCtx}.
Hypothesis MEMCPY : memcpy_spec_t.

Lemma uw_epi_t : forall Rb l M MD T (spc ret rv v0 v1 v2 v3 v4 v5 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = spc + -64 -> zget_l Rb l kS2 = rv ->
  0 <= spc + -64 -> spc <= 140737488355328 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -24) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -32) v2 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -48) v4 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -56) v5 ->
  (forall R',
     zget R' kSP = spc -> zget R' kA0 = rv ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS5 = v5 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_EPI (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T spc ret rv v0 v1 v2 v3 v4 v5 Hh Lsp Ls2 Hc1 Hc2 Hra Hret Hrr H0 H1 H2 H3 H4 H5 K.
  zkeys. unfold L_UW_EPI in *. pose proof two64_eq as TW64.
  zstep Rfd.
  do 7 (zstep Rfd).
  zstep Rfd.
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?R _ _) _ => apply (K R) end; zreg.
Qed.


Lemma uw_tail_t : forall Rb l M MD T (p spc whave wnext dist zc : Z),
  m_halted MD = None ->
  zget_l Rb l kS3 = p -> zget_l Rb l kS4 = dist -> zget_l Rb l kSP = spc + -64 ->
  0 < p -> p + STATE_SIZE <= zc -> zc <= spc + -64 -> spc <= 140737488355328 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) whave -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) wnext ->
  0 <= whave -> whave <= WIN_SIZE -> 0 <= wnext -> wnext < WIN_SIZE -> (whave < WIN_SIZE -> wnext = whave) ->
  0 <= dist -> wnext + dist <= WIN_SIZE ->
  (forall R' M' whave' wnext',
     zget R' kS3 = p -> zget R' kS4 = dist -> zget R' kSP = spc + -64 -> zget R' kS2 = 0 ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS1 = zget_l Rb l kS1 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(p + 76, 8)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_EPI (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_TAIL (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p spc whave wnext dist zc Hh Ls3 Ls4 Lsp Hp0 Hp1 Hc1 Hc2 Wp H60 H64 H68
         Wh0 Wh1 Wn0 Wn1 Whn Hd0 Hd1 K.
  zkeys. unfold L_UW_TAIL, L_UW_EPI in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(p + 76, 8)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(p + 76, 8)]) M) by (apply mpostL_refl).
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zstep Rfd.
  zsetreg (if wnext + dist =? 32768 then 0 else wnext + dist) ltac:(symmetry; apply xor_seqz_sel; lia).
  tstep1 Rfd.
  zstep Rfd.
  destruct (Z_lt_dec whave 32768) as [Hlt|Hge].
  - zbr Rfd false.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
      apply (K R Mx (whave + dist) (if wnext + dist =? 32768 then 0 else wnext + dist)) end;
      try zreg; try assumption; destruct (Z.eqb_spec (wnext + dist) 32768); lia.
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
      apply (K R Mx whave (if wnext + dist =? 32768 then 0 else wnext + dist)) end;
      try zreg; try assumption; destruct (Z.eqb_spec (wnext + dist) 32768); lia.
Qed.

Definition uw_body_fp (p wa : Z) : list (Z * Z) := [(p + 72, 12); (wa, WIN_SIZE)].
Definition L_UW_FULL : Z := 97320.
Definition L_UW_PART : Z := 97136.

Lemma uw_full_t : forall Rb l M MD T (p ob osz wa cout copy spc ret v0 v1 v2 v3 v4 v5 zc : Z) (fo : Z -> Z) (M0 : mem),
  m_halted MD = None ->
  zget_l Rb l kA0 = wa -> zget_l Rb l kA2 = WIN_SIZE -> zget_l Rb l kS0 = ob + cout -> zget_l Rb l kS1 = copy ->
  zget_l Rb l kS3 = p -> zget_l Rb l kSP = spc + -64 ->
  zc <= spc + -64 -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -64 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 < wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  WIN_SIZE <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wa WIN_SIZE ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) WIN_SIZE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) wa ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -24) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -32) v2 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -48) v4 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -56) v5 ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X (uw_body_fp p wa)) M ->
  (forall R' M' whave' wnext',
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS5 = v5 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wa ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X (uw_body_fp p wa)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_FULL (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wa cout copy spc ret v0 v1 v2 v3 v4 v5 zc fo M0
         Hh La0 La2 Ls0 Ls1 Ls3 Lsp Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wp Wwa H60 H72 HOB Hfo Hra Hret Hrr H0 H1 H2 H3 H4 H5 HAG K.
  zkeys. unfold L_UW_FULL in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M0 (uw_body_fp p wa) ltac:(unfold uw_body_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  unfold uw_body_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  zstep Rfd.
  zstep Rfd. zlit.
  zbr Rfd false.
  zstep Rfd.
  zstep Rfd.
  pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 _ ob osz fo (cout - 32768) 32768 HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
  apply mem_arr8_mem_is in Hsrc.
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc) ?Mx _) _ =>
    eapply (MEMCPY R lc Mx MD T wa (ob + 1 * (cout - 32768)) _ 32768 _ Hh) end.
  - zreg. - zreg. - zreg. - zreg. - reflexivity.
  - exact Hsrc.
  - rewrite length_map, zseq_length. lia.
  - exact Wwa.
  - lia. - lia. - lia. - lia. - zlia.
  - intros M' R' HP HD HS HW E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
    zimps.
    clear HD HS Hsrc HOB. apply mpost_mpostL1 in HP. zreattachL HP.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?lc) ?Mx _) _ =>
      eapply (uw_epi_t R' lc Mx MD T spc ret 0 v0 v1 v2 v3 v4 v5 Hh) end; try zreg; try assumption; try klia.
    intros R9 Q3 Q11 Q9 Q10 Q19 Q20 Q4 Q5 Q22 Q23 Q24 Q25 Q26 Q27 Q28.
    zimps. zkeys. apply (K R9 M1 32768 0); try assumption; try lia; try zkept.
Qed.

Lemma uw_part_t : forall Rb l M MD T (p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 v5 zc : Z) (fo : Z -> Z) (M0 : mem),
  m_halted MD = None ->
  zget_l Rb l kA0 = wa -> zget_l Rb l kA2 = WIN_SIZE -> zget_l Rb l kS0 = ob + cout -> zget_l Rb l kS1 = copy ->
  zget_l Rb l kS3 = p -> zget_l Rb l kSP = spc + -64 ->
  zc <= spc + -64 -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -64 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 < wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  0 <= copy -> copy < WIN_SIZE -> copy <= cout -> cout <= osz ->
  0 <= whave -> whave <= WIN_SIZE -> 0 <= wnext -> wnext < WIN_SIZE -> (whave < WIN_SIZE -> wnext = whave) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wa WIN_SIZE ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) whave -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) wnext ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) wa ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -24) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -32) v2 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -48) v4 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -56) v5 ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X (uw_body_fp p wa)) M ->
  (forall R' M' whave' wnext',
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS5 = v5 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wa ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X (uw_body_fp p wa)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_PART (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 v5 zc fo M0
         Hh La0 La2 Ls0 Ls1 Ls3 Lsp Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcp2 Hcout Wh0 Wh1 Wn0 Wn1 Whn Wp Wwa H60 H64 H68 H72 HOB Hfo Hra Hret Hrr H0 H1 H2 H3 H4 H5 HAG K.
  zkeys. unfold L_UW_PART in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M0 (uw_body_fp p wa) ltac:(unfold uw_body_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  unfold uw_body_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (J : forall RJ dist, dist = Z.min (32768 - wnext) copy ->
    zget RJ 11 = wa -> zget RJ 12 = wnext -> zget RJ 9 = ob + cout -> zget RJ 10 = copy -> zget RJ 20 = p ->
    zget RJ 3 = spc + -64 -> zget RJ 19 = 32768 - wnext -> zget RJ 21 = dist ->
    zget RJ 4 = zget_l Rb l 4 -> zget RJ 5 = zget_l Rb l 5 -> zget RJ 23 = zget_l Rb l 23 ->
    zget RJ 24 = zget_l Rb l 24 -> zget RJ 25 = zget_l Rb l 25 -> zget RJ 26 = zget_l Rb l 26 -> zget RJ 27 = zget_l Rb l 27 ->
    zget RJ 28 = zget_l Rb l 28 ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) 97156 (zupd RJ []) Mc MD) T) end.
  { intros RJ dist Hdist G11 G12 G9 G10 G20 G3 G19 G21 G4 G5 G23 G24 G25 G26 G27 G28.
    zstep Rfd. znot.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd. zext32.
    zbr Rfd false.
    zstep Rfd. zbool.
    zstep Rfd.
    zstep Rfd.
    zsetreg 0 ltac:(symmetry; apply seqz_xor_neq; lia).
    zstep Rfd. zlit.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 _ ob osz fo (cout - copy) dist HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
    apply mem_arr8_mem_is in Hsrc.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc) ?Mx _) _ =>
      eapply (MEMCPY R lc Mx MD T (wa + wnext) (ob + 1 * (cout - copy)) _ dist _ Hh) end.
    - zreg. - zreg. - zreg. - zreg. - reflexivity.
    - exact Hsrc.
    - rewrite length_map, zseq_length. lia.
    - eapply mem_wr_sub; [exact Wwa | lia | lia].
    - lia. - lia. - lia. - lia. - zlia.
    - intros M' R' HP HD HS HW E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
      zimps.
      clear HD HS Hsrc.
      apply mpost_mpostL1 in HP. zreattachL HP.
      destruct (Z_le_dec copy (32768 - wnext)) as [Fit|NoFit].
      +
        zbr Rfd true.
        lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
          eapply (uw_tail_t R [] Mx MD T p spc whave wnext dist zc Hh) end; try zreg; try assumption; try klia.
        intros R2' M2 whave' wnext' Q20 Q21 Q3 Q19 Q9 Q10 Q4 Q5 Q23 Q24 Q25 Q26 Q27 Q28 W1 W2 W3 W4 W5 C60 C64 C68 HP2.
        zimps. clear H60 H64 H68. zreattachL HP2.
        lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
          eapply (uw_epi_t R [] Mx MD T spc ret 0 v0 v1 v2 v3 v4 v5 Hh) end; try zreg; try assumption; try klia.
        intros R9 X3 X11 X9 X10 X19 X20 X22 X4 X5 X23 X24 X25 X26 X27 X28.
        zimps. zkeys. apply (K R9 M2 whave' wnext'); try assumption; try lia; try zkept.
      +
        zbr Rfd false.
        tstep1 Rfd.
        zstep Rfd.
        zstep Rfd. zext32.
        zbr Rfd false.
        zstep Rfd.
        zstep Rfd.
        zsetreg 0 ltac:(symmetry; apply seqz_xor_neq; lia).
        zstep Rfd. zlit.
        zbr Rfd false.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd.
        pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 _ ob osz fo (cout - (copy - dist)) (copy - dist) HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc2.
        apply mem_arr8_mem_is in Hsrc2.
        lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc) ?Mx _) _ =>
          eapply (MEMCPY R lc Mx MD T wa (ob + 1 * (cout - (copy - dist))) _ (copy - dist) _ Hh) end.
        * zreg. * zreg. * zreg. * zreg. * reflexivity.
        * exact Hsrc2.
        * rewrite length_map, zseq_length. lia.
        * eapply mem_wr_sub; [exact Wwa | lia | lia].
        * lia. * lia. * lia. * lia. * zlia.
        * intros M2 R2' HP2 HD2 HS2 HW2 F11 F3 F4 F5 F9 F10 F19 F20 F21 F22 F23 F24 F25 F26 F27 F28.
          zimps. clear HD2 HS2 Hsrc2 HOB. apply mpost_mpostL1 in HP2. zreattachL HP2.
          zstep Rfd.
          tstep1 Rfd.
          tstep1 Rfd.
          tstep1 Rfd.
          zstep Rfd.
          lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
            eapply (uw_epi_t R [] Mx MD T spc ret 0 v0 v1 v2 v3 v4 v5 Hh) end; try zreg; try assumption; try klia.
          intros R9 X3 X11 X9 X10 X19 X20 X22 X4 X5 X23 X24 X25 X26 X27 X28.
          zimps. zkeys.
          lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K R9 Mx 32768 (copy - dist)) end;
            try assumption; try lia; try zkept. }
  destruct (Z_lt_dec (32768 - wnext) copy) as [Lt|Ge].
  - zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R _ _) _ => apply (J R (32768 - wnext)) end; try zreg; lia.
  - zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R _ _) _ => apply (J R copy) end; try zreg; lia.
Qed.
Lemma uw_body_t : forall Rb l M MD T (p ob osz wa ws whave wnext cout copy spc ret v0 v1 v2 v3 v4 v5 zc : Z) (fo : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA0 = wa -> zget_l Rb l kS0 = ob + cout -> zget_l Rb l kS1 = copy -> zget_l Rb l kS3 = p ->
  zget_l Rb l kSP = spc + -64 ->
  zc <= spc + -64 -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -64 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 < wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  0 <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  (ws = 0 \/ ws = WIN_SIZE) -> 0 <= whave -> 0 <= wnext ->
  (ws = WIN_SIZE -> whave <= WIN_SIZE /\ wnext < WIN_SIZE /\ (whave < WIN_SIZE -> wnext = whave)) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wa WIN_SIZE ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 68) 15 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) ws -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) whave ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) wnext -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) wa ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -24) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -32) v2 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -48) v4 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -56) v5 ->
  (forall R' M' whave' wnext',
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS5 = v5 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wa ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (uw_body_fp p wa) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_BODY (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wa ws whave wnext cout copy spc ret v0 v1 v2 v3 v4 v5 zc fo
         Hh La0 Ls0 Ls1 Ls3 Lsp Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Hws Wh0 Wn0 Wfacts
         Wp Wwa H56 H60 H64 H68 H72 HOB Hfo Hra Hret Hrr H0 H1 H2 H3 H4 H5 K.
  zkeys. unfold L_UW_BODY in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (uw_body_fp p wa) ltac:(unfold uw_body_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (uw_body_fp p wa)) M) by (apply mpostL_refl).
  unfold uw_body_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  assert (FULL : forall RJ Mq (whave1 wnext1 : Z), 32768 <= copy ->
    zget RJ 11 = wa -> zget RJ 13 = 32768 -> zget RJ 9 = ob + cout -> zget RJ 10 = copy -> zget RJ 20 = p -> zget RJ 3 = spc + -64 ->
    zget RJ 4 = zget_l Rb l 4 -> zget RJ 5 = zget_l Rb l 5 -> zget RJ 22 = zget_l Rb l 22 -> zget RJ 23 = zget_l Rb l 23 ->
    zget RJ 24 = zget_l Rb l 24 -> zget RJ 25 = zget_l Rb l 25 -> zget RJ 26 = zget_l Rb l 26 -> zget RJ 27 = zget_l Rb l 27 ->
    zget RJ 28 = zget_l Rb l 28 ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq p 7176 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq wa 32768 ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 72) 32768 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 88) wa ->
    mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) Mq ob osz fo ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -8) ret -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -24) v1 ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -32) v2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -48) v4 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -56) v5 ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(p + 72, 12); (wa, 32768)]) Mq ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_FULL (zupd RJ []) Mq MD) T).
  { intros RJ Mq whave1 wnext1 Hc G11 G13 G9 G10 G20 G3 G4 G5 G22 G23 G24 G25 G26 G27 G28 Wp' Wwa' C60 C72 HOB' Cra C0 C1 C2 C3 C4 C5 HAG'.
    eapply (uw_full_t RJ [] Mq MD T p ob osz wa cout copy spc ret v0 v1 v2 v3 v4 v5 zc fo M Hh); try zreg; try assumption; try klia. }
  assert (PART : forall RJ Mq (whave1 wnext1 : Z), copy < 32768 ->
    0 <= whave1 -> whave1 <= 32768 -> 0 <= wnext1 -> wnext1 < 32768 -> (whave1 < 32768 -> wnext1 = whave1) ->
    zget RJ 11 = wa -> zget RJ 13 = 32768 -> zget RJ 9 = ob + cout -> zget RJ 10 = copy -> zget RJ 20 = p -> zget RJ 3 = spc + -64 ->
    zget RJ 4 = zget_l Rb l 4 -> zget RJ 5 = zget_l Rb l 5 -> zget RJ 22 = zget_l Rb l 22 -> zget RJ 23 = zget_l Rb l 23 ->
    zget RJ 24 = zget_l Rb l 24 -> zget RJ 25 = zget_l Rb l 25 -> zget RJ 26 = zget_l Rb l 26 -> zget RJ 27 = zget_l Rb l 27 ->
    zget RJ 28 = zget_l Rb l 28 ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq p 7176 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq wa 32768 ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 72) 32768 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 76) whave1 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 80) wnext1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 88) wa ->
    mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) Mq ob osz fo ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -8) ret -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -24) v1 ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -32) v2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -48) v4 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (spc + -56) v5 ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(p + 72, 12); (wa, 32768)]) Mq ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_PART (zupd RJ []) Mq MD) T).
  { intros RJ Mq whave1 wnext1 Hc W1 W2 W3 W4 W5 G11 G13 G9 G10 G20 G3 G4 G5 G22 G23 G24 G25 G26 G27 G28 Wp' Wwa' C60 C64 C68 C72 HOB' Cra C0 C1 C2 C3 C4 C5 HAG'.
    eapply (uw_part_t RJ [] Mq MD T p ob osz wa whave1 wnext1 cout copy spc ret v0 v1 v2 v3 v4 v5 zc fo M Hh); try zreg; try assumption; try klia. }
  unfold L_UW_FULL, L_UW_PART in FULL, PART.
  tstep1 Rfd.
  destruct Hws as [Hws0 | Hws1]; subst ws.
  - zbr Rfd true.
    tstep1 Rfd.
    zstep Rfd.
    zbr Rfd false.
    zstep Rfd.
    zstep Rfd. zlit.
    tstep1 Rfd.                       (* sw a2,72(s3): wsize *)
    (* whave (p+76) and wnext (p+80) are cleared by two sw (76 is not 8-aligned), not one sd *)
    tstep1 Rfd.                       (* sw zero,76(s3) *)
    tstep1 Rfd.                       (* sw zero,80(s3) *)
    match goal with H1 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (p + 76) 0, H2 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (p + 80) 0 |- _ =>
      rename H1 into Hwh; rename H2 into Hwn end.
    destruct (Z_lt_dec copy 32768) as [Lt|Ge].
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => apply (PART R Mx 0 0) end; try zreg; try assumption; try lia.
    + zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => apply (FULL R Mx 0 0) end; try zreg; try assumption; try lia.
  - zbr Rfd false.
    specialize (Wfacts eq_refl). dand Wfacts as (W2 & W4 & W5).
    destruct (Z_lt_dec copy 32768) as [Lt|Ge].
    + zbr Rfd false.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => apply (PART R Mx whave wnext) end; try zreg; try assumption; try lia.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => apply (FULL R Mx whave wnext) end; try zreg; try assumption; try lia.
Qed.

Definition uw_fp (p wa spc : Z) : list (Z * Z) := [(spc + -64, 64); (p + 72, 12); (wa, WIN_SIZE)].

Lemma uw_entry_t : forall Rb l M MD T (u p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 v5 zc : Z) (fo : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA0 = u -> zget_l Rb l kA1 = ob + cout -> zget_l Rb l kA2 = copy -> zget_l Rb l kSP = spc ->
  zget_l Rb l kRA = ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  zget_l Rb l kS0 = v0 -> zget_l Rb l kS1 = v1 -> zget_l Rb l kS2 = v2 -> zget_l Rb l kS3 = v3 -> zget_l Rb l kS4 = v4 -> zget_l Rb l kS5 = v5 ->
  zc + FRA <= u -> u + 208 <= 140737488355328 -> u mod 16 = 0 -> zc <= spc + -64 -> spc <= u ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -64 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 <= wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (wa = 0 \/ p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa = 0 \/ wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  0 <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  0 <= whave -> 0 <= wnext ->
  (wa <> 0 -> whave <= WIN_SIZE /\ wnext < WIN_SIZE /\ (whave < WIN_SIZE -> wnext = whave)) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -64) 64 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> (wa <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wa WIN_SIZE) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 68) 15 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) (if wa =? 0 then 0 else WIN_SIZE) ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) whave -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) wnext -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) wa ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  (forall R' M', wa = 0 ->
     zget R' kA3 = A_ZCALLOC -> zget R' kA0 = 0 -> zget R' kA1 = WIN_SIZE -> zget R' kA2 = 1 ->
     zget R' kS0 = ob + cout -> zget R' kS1 = copy -> zget R' kS2 = 1 -> zget R' kS3 = p -> zget R' kS4 = v4 -> zget R' kS5 = v5 ->
     zget R' kSP = spc + -64 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -8) ret -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -24) v1 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -32) v2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -48) v4 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -56) v5 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(spc + -64, 64)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd R' []) M' MD) T) ->
  (forall R' M' whave' wnext', wa <> 0 ->
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS5 = v5 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wa ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (uw_fp p wa spc) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 v5 zc fo
         Hh La0 La1 La2 Lsp Lra Hret Hrr Ls0 Ls1 Ls2 Ls3 Ls4 Ls5
         Hu0 Hu1 Hual Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wh0 Wn0 Wfacts Wfr Wp Wwa H64u H72u H88u H56 H60 H64 H68 H72 HOB Hfo KW K.
  zkeys. unfold L_UW, T_ZW in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (uw_fp p wa spc) ltac:(unfold uw_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (uw_fp p wa spc)) M) by (apply mpostL_refl).
  unfold uw_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  Local Ltac prologue :=
    zstep Rfd;
    do 7 (tstep1 Rfd);
    zstep Rfd;
    zstep Rfd;
    zstep Rfd; zalign;
    zbr Rfd false;
    tstep1 Rfd;
    zbr Rfd false;
    zstep Rfd; zalign;
    zbr Rfd false;
    zstep Rfd;
    tstep1 Rfd.
  destruct (Z.eq_dec wa 0) as [Wz | Wnz].
  -
    clear Wwa Wfacts. subst wa.
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(spc + -64, 64)] ltac:(ranges_ok_tac)) as HST';
    assert (HAG' : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(spc + -64, 64)]) M) by (apply mpostL_refl).
    prologue.
    zbr Rfd false.
    tstep1 Rfd.
    zstep Rfd.
    zbr Rfd false.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd. zlit.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ => apply (KW R Mx eq_refl) end; try zreg; try assumption; try exact HAG'.
  -
    specialize (Wwa Wnz). specialize (Wfacts Wnz). prologue.
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
      eapply (uw_body_t R [] Mx MD T p ob osz wa (if wa =? 0 then 0 else 32768) whave wnext cout copy spc ret v0 v1 v2 v3 v4 v5 zc fo Hh) end;
      try zreg; try assumption; try klia.
    + slia.
    + slia.
    + destruct (Z.eqb_spec wa 0); [lia_std | right; reflexivity].
    + intros R9 M9 whave' wnext'. intros. zimps.
      match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ M9 _ |- _ => unfold uw_body_fp in HP; cbv [WIN_SIZE] in HP; zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K R9 Mx whave' wnext' Wnz) end; try assumption; try zkept.
Qed.

Definition uw_res_fp (p wres spc : Z) : list (Z * Z) := [(spc + -64, 64); (p + 72, 24); (wres, WIN_SIZE)].

Lemma uw_resume_t : forall Rb l M MD T (p ob osz wres cout copy spc ret v0 v1 v2 v3 v4 v5 zc : Z) (fo : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA0 = wres -> zget_l Rb l kS0 = ob + cout -> zget_l Rb l kS1 = copy -> zget_l Rb l kS2 = 1 ->
  zget_l Rb l kS3 = p -> zget_l Rb l kSP = spc + -64 ->
  zc <= spc + -64 -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -64 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 <= wres -> wres + WIN_SIZE <= zc -> wres mod 16 = 0 ->
  ZSEP (wres = 0 \/ p + STATE_SIZE <= wres \/ wres + WIN_SIZE <= p) -> ZSEP (wres = 0 \/ wres + WIN_SIZE <= ob \/ ob + osz <= wres) ->
  0 <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -64) 64 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> (wres <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wres WIN_SIZE) ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 68) 15 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) 0 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -24) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -32) v2 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -48) v4 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -56) v5 ->
  (forall R' M', wres = 0 ->
     zget R' kSP = spc -> zget R' kA0 = 1 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS5 = v5 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) 0 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(spc + -64, 64); (p + 72, 24)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  (forall R' M' whave' wnext', wres <> 0 ->
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS5 = v5 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wres ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (uw_res_fp p wres spc) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZB (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wres cout copy spc ret v0 v1 v2 v3 v4 v5 zc fo
         Hh La0 Ls0 Ls1 Ls2 Ls3 Lsp Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hw0 Hw1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wfr Wp Ww H56 H60 H72 HOB Hfo Hra Hret Hrr H0 H1 H2 H3 H4 H5 K0 K1.
  zkeys. unfold L_ZB in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (uw_res_fp p wres spc) ltac:(unfold uw_res_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (uw_res_fp p wres spc)) M) by (apply mpostL_refl).
  unfold uw_res_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  destruct (Z.eq_dec wres 0) as [Wz | Wnz].
  - clear Ww. revert La0. subst wres. intros La0.
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(spc + -64, 64); (p + 72, 24)] ltac:(ranges_ok_tac)) as HST';
    assert (HAG' : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(spc + -64, 64); (p + 72, 24)]) M) by (apply mpostL_refl).
    tstep1 Rfd.
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
      eapply (uw_epi_t R [] Mx MD T spc ret 1 v0 v1 v2 v3 v4 v5 Hh) end; try zreg; try assumption; try klia.
    intros R9. intros. zimps. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K0 R9 Mx eq_refl) end; try assumption; try zkept; try exact HAG'.
  - specialize (Ww Wnz).
    destruct (mem_wr_u32_exists_R M (p + 76) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (wh0 & Hwh0 & Rwh0).
    destruct (mem_wr_u32_exists_R M (p + 80) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (wn0 & Hwn0 & Rwn0).
    tstep1 Rfd.
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
      eapply (uw_body_t R [] Mx MD T p ob osz wres 0 wh0 wn0 cout copy spc ret v0 v1 v2 v3 v4 v5 zc fo Hh) end;
      try zreg; try assumption; try klia.
    + slia.
    + slia.
    + intros R9 M9 whave' wnext'. intros. zimps.
      match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ M9 _ |- _ => unfold uw_body_fp in HP; cbv [WIN_SIZE] in HP; zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K1 R9 Mx whave' wnext' Wnz) end; try assumption; try zkept.
Qed.
End Uw.
End T_Uw.

Module T_Check.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_HeadA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I7S.S_Check.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.I9U.TBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_CHECK_LOOP_T : Z := 87968.
Definition L_CHECK_BODY_T : Z := 90704.
Definition L_CHECK_CMP_T : Z := 92244.
Definition L_LEAVEX_CK_T : Z := 95968.

Lemma mem_u32_lo8_t {RCa1 : RunCtx}  : forall M a e, mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e -> mem_u8 (run_segments R_segs rc_inp rc_sp rc_mb) M a (e mod 256).
Proof.
  intros M a e H. unfold mem_u32, mem_u8 in *. rewrite le4_split in H.
  pose proof (mem_is_app_l (run_segments R_segs rc_inp rc_sp rc_mb) M _ _ _ H) as H0. rewrite Z_to_le_bytes_1_mod. exact H0.
Qed.

Definition fp_check_t (u p : Z) : list (Z * Z) :=
  [(p + 8, 4); (p + 40, 16); (u + -384, 128); (u + 40, 16); (u + 96, 8); (u + -168, 8)].

Section WITH_ADLER.
Context {RCa1 : RunCtx}.
Hypothesis ADLER : adler32_spec_t.

Lemma check_main_t : forall cx fin MD T M0 Rb l M st lf cf (cin1 hold1 bits1 : Z),
  ctx_ok ROMHI_T cx -> c_ob cx + c_osz cx <= c_u cx - FRA -> m_halted MD = None ->
  (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = CHECK -> sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -256 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kS0 = c_p cx -> zget_l Rb l kS2 = c_u cx -> zget_l Rb l kA3 = c_u cx ->
  zget_l Rb l kRA = 16209 -> zget_l Rb l kA4 = 5 ->
  zget_l Rb l kS1 = c_ob cx + t_cout st ->
  zget_l Rb l kS4 = c_q cx + cin1 -> zget_l Rb l kS11 = c_n cx - cin1 ->
  zget_l Rb l kS9 = hold1 -> zget_l Rb l kS5 = bits1 ->
  t_cin st <= cin1 <= c_n cx -> 32 <= bits1 <= 40 -> 0 <= hold1 < 2 ^ bits1 -> bits1 <= 8 * cin1 ->
  8 * (c_n cx - cin1) + bits1 = 8 * (c_n cx - t_cin st) + t_bits st ->
  k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK_BODY_T (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf cin1 hold1 bits1 CX OBLOW Hh Hfin Hm SI
         LSP LGP LTP L11 LS0 LA3 LRA LA4 L2 L4 L10 L3 L8 Hc1 Hb1 Hh1 Hbc1 HW1 KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST]. destruct SLO as [HL HO].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. unfold FRA in OBLOW. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags t_cin t_cout t_hold t_bits t_out] in *. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  assert (Hf0 : flags = 0) by lia. subst flags. clear Hfl.
  pose proof (hold_u64 hold1 bits1 ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  pose proof (mem_u32_lo8_t _ _ _ H16) as H16b. cbn [Z.modulo Z.pos_div_eucl] in H16b.
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn. dand SR' as (_ & H24 & _).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _ & _ & _ & _ & Q80 & _).
  unfold s_lo in HL, HO. icx_cbn.
  destruct (mem_wr_u64_exists_R M (u + 40) ltac:(eapply mem_wr_sub; [exact Wstk | lia | lia])) as (to & Hto & Rto).
  destruct (mem_wr_u64_exists_R M (p + 48) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (tt & Htt & Rtt).
  destruct (mem_wr_u64_exists_R M (p + 40) ltac:(eapply mem_wr_sub; [exact Wp | lia | cbv [STATE_SIZE]; lia])) as (ck & Hck & Rck).
  clear Ww FRM CST HK Hmode SREST SRET Hlens Hcodes Hin.
  zkeysb. unfold L_CHECK_BODY_T, L_CHECK_CMP_T, L_DISP, L_LEAVE in *. cbv [A_ADLER32] in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (fp_check_t u p) ltac:(unfold fp_check_t; ranges_ok_tac)) as HSTc.
  assert (HAGc : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (fp_check_t u p)) M) by (apply mpostL_refl).
  unfold fp_check_t in HSTc, HAGc.
  assert (REATT : forall Mq m' c1 h1 b1 o1,
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 8) m' -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (u + -168) o1 ->
    mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M Mq [(p + 8, 4); (p + 40, 16); (u + -384, 128); (u + 40, 16); (u + 96, 8); (u + -168, 8)] ->
    m' <> LENEXT -> m' <> DIST ->
    k_mem (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin M0
          (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                 m' c1 h1 b1 o1) lf cf Mq).
  { intros Mq m' c1 h1 b1 o1 Hm8 Ho1 HPq Hne1 Hne2.
    clear HST HAG Wstk Wp Wob ROM HSTc HAGc H16 H16b H24 Q136 Q80 HL HO Hto Htt Hck.
    open_kmem KM0. open_std STD. destruct SAT as [Hmode SREST]. clear Hmode.
    unfold s_lo in SLO. icx_cbn. destruct SLO as [HL' HO']. clear HO'.
    unfold st_rest in SREST. icx_cbn.
    dand SREST as (H12 & H24 & H64 & H68 & H92 & H96 & H100 & H104 & H112 & H120 & H124 & H128 & H132 & H136 & H140 & H144).
    fp_frame_from HP0.
    cbv [N_LENS N_CODES] in Hlens, Hcodes.
    zreattachL HPq.
    unfold k_mem; split_conj;
      [ close_std
      | unfold st_at, st_rest, ck_st; icx_cbn; split_conj; assumption
      | unfold s_ret, ck_st in *; icx_cbn; assumption
      | unfold s_lo, ck_st; icx_cbn; split; assumption
      | assumption | assumption | exact HAG
      | lazymatch goal with |- s_bk _ _ ?MX => match goal with H : s_bk _ _ MX |- _ => eapply (s_bk_other _ _ _ _ H); cbn [t_mode]; assumption end end ]. }
  zstep Rfd.
  zstep Rfd.
  tstep1 Rfd.
  zsetreg (out - (osz - cout)) ltac:(first [lia | rewrite swrap32_small by lia; lia]).
  zstep Rfd.
  zstep Rfd.
  zstep Rfd. zstep Rfd. zext32.
  zstep Rfd. zgen.
  tstep1 Rfd.
  zstep Rfd. zlit.
  zstep Rfd. zgen.
  tstep1 Rfd.
  zbr Rfd false.
  try clear Hto; try clear Htt.
  lazymatch type of HAG with framed (fun X => mpostL _ _ X ?FPL) _ =>
  assert (CMP : forall RC Mq c,
    zget RC kSP = u + -256 -> zget RC kGP = K0 kGP -> zget RC kTP = K0 kTP -> zget RC kS0 = p ->
    zget RC kS2 = u -> zget RC kA3 = u -> zget RC kA1 = 0 -> zget RC kRA = 16209 ->
    zget RC kS1 = ob + cout -> zget RC kS4 = q + cin1 -> zget RC kS11 = n - cin1 -> zget RC kS9 = hold1 -> zget RC kS5 = bits1 ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq p 7176 ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 16) 5 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 28) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 40) c ->
    mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (u + -144) (osz - cout) ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X FPL) Mq ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(p + 8, 4); (p + 40, 16); (u + -384, 128); (u + 40, 16); (u + 96, 8); (u + -168, 8)]) Mq ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK_CMP_T (zupd RC []) Mq MD) T) end.
  { intros RC Mq c. clear HAG HAGc Wstk Wp Wob ROM Hck H24 H16 H16b Q136 Q80 HL HO.
    intros E3 E4 E5 E28 E9 E14 E12 E2 E19 E21 E27 E20 E25 Wstk Wp H16 H24 Hck HL HAG HAGc.
    unfold L_CHECK_CMP_T. zkeys.
    tstep1 Rfd.
    zstep Rfd.
    zbr Rfd false.
    do 13 (zstep Rfd).
    zgenreg sw.
    zstep Rfd.
    destruct (zcond BC_NE sw c) eqn:Hcc.
    -
      zbrH Rfd true.
      zstep Rfd. zstep Rfd. zlit.
      tstep1 Rfd.
      tstep1 Rfd.
      zstep Rfd. zstep Rfd. zstep Rfd.
      zstep Rfd.
      tstep1 Rfd.
      zstep Rfd.
      pose proof (sinv_ck _ _ lf cf BAD cin1 hold1 bits1 (osz - cout) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                    ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(right; split; [reflexivity | cbv; reflexivity])) as SI1.
      pose proof (meas_ck (ICX u p q n ob osz w cin0 cout0 W0 K0 zc)
                    (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                    BAD cin1 hold1 bits1 (osz - cout) ltac:(right; split; [cbn; lia | vm_compute; reflexivity])) as MB1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        eapply (KD R' Mx (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                 BAD cin1 hold1 bits1 (osz - cout)) lf cf SI1 MB1) end.
      + unfold s_regs_disp, s_fix, s_vars, ck_st; icx_cbn; zkeys; split_conj; zreg.
      + apply REATT; [assumption | assumption | exact HAGc | cbv; intros EE; discriminate EE | cbv; intros EE; discriminate EE].
    -
      zbrH Rfd false.
      zstep Rfd. zstep Rfd.
      zstep Rfd.
      tstep1 Rfd.
      zstep Rfd. zlit.
      tstep1 Rfd.
      zstep Rfd. zstep Rfd.
      tstep1 Rfd.
      zbr Rfd false.
      tstep1 Rfd.
      zbr Rfd true.
      zstep Rfd. zstep Rfd.
      zstep Rfd.
      zstep Rfd. zlit.
      tstep1 Rfd.
      zstep Rfd.
      zstep Rfd. zstep Rfd.
      zstep Rfd.
      pose proof (sinv_ck _ _ lf cf DONE cin1 0 0 (osz - cout) SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                    ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(right; split; [reflexivity | cbv; reflexivity])) as SI1.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
        destruct (REATT Mx DONE cin1 0 0 (osz - cout) ltac:(assumption) ltac:(assumption) HAGc ltac:(cbv; intros EE; discriminate EE) ltac:(cbv; intros EE; discriminate EE))
          as (STD' & SAT' & _ & SLO' & Hl' & Hc' & HP' & SBK');
        eapply (KL R' Mx (ck_st (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                                 DONE cin1 0 0 (osz - cout)) 1 lf cf SI1) end.
      + unfold s_regs_leave, ck_st; icx_cbn; zkeys; split_conj; zreg.
      + exact STD'.
      + exact SAT'.
      + exact SLO'.
      + exact SBK'.
      + exact Hl'.
      + exact Hc'.
      + exact HP'. }
  destruct (Z.eq_dec out (osz - cout)) as [Ecout | Ecout].
  -
    zbr Rfd true.
    zstep Rfd.
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?RC ?Mx _) _ => apply (CMP RC Mx ck) end; first [zreg | assumption].
  -
    zbr Rfd false.
    tstep1 Rfd.
    zstep Rfd. zbool.
    zstep Rfd.
    zstep Rfd.
    zsetreg 0 ltac:(symmetry; apply seqz_xor_neq; lia).
    zstep Rfd. zlit.
    zstep Rfd. zbool.
    zstep Rfd. zlit.
    zstep Rfd. zlit.
    zbr Rfd true.
    zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    zsetreg (ob + cout - (out - (osz - cout))) ltac:(lia).
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      destruct (mem_wr_arr_exists_R Mx ob osz Wob ltac:(lia) ltac:(lia) ltac:(lia)) as (fo & HOB & Hfo) end.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
      pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 Mx ob osz fo (cout - (out - (osz - cout))) (out - (osz - cout)) HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc end.
    replace (ob + 1 * (cout - (out - (osz - cout)))) with (ob + cout - (out - (osz - cout))) in Hsrc by lia.
    clear HOB.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?lc) ?Mx _) _ =>
      eapply (ADLER R' lc Mx MD T ck (ob + cout - (out - (osz - cout))) (out - (osz - cout)) (out - (osz - cout)) (u + -256) _
                (fun j => fo (cout - (out - (osz - cout)) + j)) Hh) end;
      try zreg.
    all: lazymatch goal with
         | |- forall M' : mem, _ => idtac
         | |- _ => cbv [FR_AD]; first [ reflexivity | exact Hsrc | assumption | rewrite Z.mod_small by lia; reflexivity
                         | eapply mem_wr_sub; [exact Wstk | lia | lia] | intros i Hi; apply Hfo; lia | lia ]
         end.
    intros Ma Ra HP. intros. zimps. zkeys.
    clear Hsrc.
    apply mpost_mpostL1 in HP. cbv [FR_AD] in HP. zreattachL HP.
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd. zlit.
    zstep Rfd. zlit.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd false.
    lazymatch goal with Hnew : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (p + 40) ?c' |- realizes _ (zcfg _ _ ?RC ?Mx _) _ =>
      apply (CMP RC Mx c') end; first [zreg | assumption].
Qed.

Lemma check_loop_t : forall (k : nat) cx fin MD T Rb l M (cinj holdj j : Z),
  m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  ctx_lin ROMHI_T cx ->
  32 - 8 * Z.of_nat k <= j < 40 - 8 * Z.of_nat k -> (1 <= k <= 4)%nat -> 0 <= j ->
  0 <= cinj <= c_n cx -> 0 <= holdj < 2 ^ j -> j <= 8 * cinj ->
  zget_l Rb l kS2 = c_u cx -> zget_l Rb l kA3 = c_u cx ->
  zget_l Rb l kA5 = j -> zget_l Rb l kS5 = j -> zget_l Rb l kA1 = c_q cx + cinj -> zget_l Rb l kA6 = c_q cx + cinj ->
  zget_l Rb l kS11 = c_n cx - cinj -> zget_l Rb l kS9 = holdj ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_q cx) (c_n cx) fin ->
  (forall R' hold' j',
     zget R' kS9 = hold' -> j' = j + 8 * (c_n cx - cinj) -> 0 <= hold' < 2 ^ j' -> c_n cx - cinj < Z.of_nat k ->
     zget R' kA3 = c_u cx ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA ->
     zget R' kS10 = zget_l Rb l kS10 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS3 = zget_l Rb l kS3 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LEAVEX_CK_T (zupd R' []) M MD) T) ->
  (forall R' hold' j',
     zget R' kS4 = c_q cx + cinj + Z.of_nat k -> zget R' kS11 = c_n cx - cinj - Z.of_nat k ->
     zget R' kS5 = j' -> zget R' kS9 = hold' ->
     j' = j + 8 * Z.of_nat k -> 0 <= hold' < 2 ^ j' -> Z.of_nat k <= c_n cx - cinj ->
     zget R' kA3 = c_u cx ->
     zget R' kSP = zget_l Rb l kSP -> zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS2 = zget_l Rb l kS2 ->
     zget R' kS1 = zget_l Rb l kS1 -> zget R' kRA = zget_l Rb l kRA -> zget R' kA4 = zget_l Rb l kA4 ->
     zget R' kS10 = zget_l Rb l kS10 -> zget R' kS7 = zget_l Rb l kS7 -> zget R' kS3 = zget_l Rb l kS3 ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK_BODY_T (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK_LOOP_T (zupd Rb l) M MD) T.
Proof.
  induction k as [|k IH]; intros cx fin MD T Rb l M cinj holdj j Hh Hfin CXl Hj Hk Hj0 Hc Hhj Hjc LS0 LA3 LA5 L8 LA1 LA6 L10 L3 Hin KLV KDN; [lia|].
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc].
  unfold ctx_lin in CXl; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T] in CXl; destr_conj CXl.
  zkeysb. unfold L_CHECK_LOOP_T, L_CHECK_BODY_T, L_LEAVEX_CK_T in *. pose proof two64_eq as TW64.
  assert (Hj40 : 2 ^ j <= 2 ^ 39) by (apply Z.pow_le_mono_r; lia). change (2 ^ 39) with 549755813888 in Hj40.
  destruct (Z.eq_dec (n - cinj) 0) as [Hv0 | Hv0].
  -
    zbr Rfd false.
    zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KLV R' holdj j) end; try zreg; try lia.
  - zbr Rfd true.
    pose proof (Hfin cinj ltac:(lia)) as Hb0.
    zstep Rfd.
    zstep Rfd.
    zbr Rfd true.
    zstep Rfd.
    zstep Rfd.
    tstep1 Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zsetreg (fin cinj * 2 ^ j) ltac:(rewrite (Z.mod_small j) by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    zstep Rfd.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd.
    pose proof (pullbyte_bound holdj j (fin cinj) ltac:(lia) Hhj Hb0) as Hpb.
    destruct k as [|k'].
    +
      zbr Rfd false.
      zstep Rfd.
      lazymatch goal with |- realizes _ (zcfg _ _ ?R' _ _) _ => apply (KDN R' (fin cinj * 2 ^ j + holdj) (j + 8)) end; try zreg; try lia.
    + zbr Rfd true.
      lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') _ _) _ =>
        eapply (IH (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' M (cinj + 1) (fin cinj * 2 ^ j + holdj) (j + 8) Hh Hfin) end;
        [ unfold ctx_lin; icx_cbn; cbv [FRA STATE_SIZE WIN_SIZE ROM_LO_ALL ROMHI_T]; split_conj; assumption || lia
        | lia | lia | lia | icx_cbn; lia | lia | icx_cbn; lia
        | (icx_cbn; zreg) .. | exact Hin | | ].
      * intros R' hold' j'. icx_cbn. intros. eapply KLV; try eassumption; try lia; try zkept.
      * intros R' hold' j'. icx_cbn. intros. eapply KDN; try eassumption; try lia; try zkept.
Qed.

Lemma check_body_t : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> c_ob cx + c_osz cx <= c_u cx - FRA -> m_halted MD = None ->
  (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = CHECK -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CHECK (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX OBLOW Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0. pose proof KM as KM0. pose proof K as KA0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. pose proof (proj1 CX) as CXl. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  assert (Hf0 : flags = 0) by lia. subst flags. clear Hfl.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  pose proof FRM as FRM'. unfold i_frame in FRM'. icx_cbn.
  dand FRM' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q136 & _).
  pose proof SRET as SRET'. unfold s_ret in SRET'. icx_cbn.
  clear ROM Wob Ww FRM CST HK Hmode SREST SRET SLO Hlens Hcodes.
  zkeysb. unfold L_CHECK, L_CHECK_LOOP_T, L_CHECK_BODY_T, L_LEAVEX_CK_T, L_LEAVE in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  zbr Rfd false.
  zstep Rfd.
  destruct (Z_lt_dec 31 bits) as [Hb32 | Hb32].
  - zbr Rfd true.
    zstep Rfd. zstep Rfd. zstep Rfd.
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (check_main_t (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' l' Mx
                (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf cin hold bits CX0 OBLOW Hh Hfin eq_refl SI0) end;
      [ (icx_cbn; zreg) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
  - zbr Rfd false.
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
    assert (Hkk : exists k : nat, 32 - 8 * Z.of_nat k <= bits < 40 - 8 * Z.of_nat k /\ (1 <= k <= 4)%nat).
    { exists (Z.to_nat (4 - bits / 8)).
      rewrite Z2Nat.id by (Z.to_euclidean_division_equations; lia).
      split; [Z.to_euclidean_division_equations; lia|]. Z.to_euclidean_division_equations; lia. }
    dand Hkk as (k & Hk1 & Hk2).
    lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R' ?l') ?Mx _) _ =>
      eapply (check_loop_t k (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T R' l' Mx cin hold bits Hh Hfin CXl Hk1 Hk2) end;
      [ lia | icx_cbn; lia | lia | lia | (icx_cbn; zreg) .. | exact Hin | | ].
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_LEAVEX_CK_T in *.
      zstep Rfd.
      zstep Rfd.
      zsetreg (8 * (n - cin)) ltac:(rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 3) with 8; rewrite ?Z.mod_small by lia; lia).
      zstep Rfd. zext32.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      zstep Rfd.
      pose proof (sinv_ck _ _ lf cf CHECK n hold' j' out SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                    ltac:(cbn; lia) ltac:(lia) ltac:(assumption) ltac:(lia) ltac:(cbn; lia)
                    ltac:(left; split; [reflexivity | intros X; exact X])) as SI1.
      clear H16. open_kmem KM0. destruct SAT as [Hmode SREST].
      lazymatch goal with |- realizes _ (zcfg _ _ ?Rx ?Mx _) _ =>
        eapply (KL Rx Mx _ ret lf cf SI1) end.
      * unfold s_regs_leave, ck_st; icx_cbn; zkeys; split_conj; try zreg. all: zkept.
      * exact STD.
      * unfold ck_st; split; [exact Hmode | exact SREST].
      * exact SLO.
      * sbk.
      * exact Hlens.
      * exact Hcodes.
      * exact HAG.
    +
      intros R' hold' j'. icx_cbn. intros. zimps. zkeys. unfold L_CHECK_BODY_T in *.
      eapply (check_main_t (ICX u p q n ob osz w cin0 cout0 W0 K0 zc) fin MD T M0 R' [] M
                (IST CHECK last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                lf cf (cin + Z.of_nat k) hold' j' CX0 OBLOW Hh Hfin eq_refl SI0);
        [ (icx_cbn; first [zreg | zkeys; cbv [zget_l alookup]; first [zkept | lia]]) .. | icx_cbn; lia | lia | lia | lia | icx_cbn; lia | exact KM0 | exact KA0 ].
Qed.

Theorem arm_CHECK_t : arm_stmt_ob L_CHECK CHECK.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX OBLOW Hh Hfin Hm SI RE KM K. eapply check_body_t; eassumption. Qed.

End WITH_ADLER.

Lemma length_body_t {RCa1 : RunCtx}  : forall cx fin MD T M0 Rb l M st lf cf,
  ctx_ok ROMHI_T cx -> m_halted MD = None -> (forall i, 0 <= i < c_n cx -> 0 <= fin i < 256) ->
  t_mode st = LENGTH -> sinv cx st lf cf ->
  s_regs_arm cx st Rb l -> k_mem cx fin M0 st lf cf M ->
  KALL cx fin MD T M0 (meas cx st) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_LENGTH (zupd Rb l) M MD) T.
Proof.
  intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K.
  pose proof CX as CX0. pose proof SI as SI0.
  open_K K. open_kmem KM. open_std STD. destruct SAT as [Hmode SREST].
  pose proof SI as SI'. dand SI' as (RNG_ & _ & PROG_ & _).
  pose proof (flags_not_m1 _ _ _ _ SI ltac:(rewrite Hm; cbv; discriminate) ltac:(rewrite Hm; cbv; discriminate)) as Hfl.
  destruct cx as [u p q n ob osz w cin0 cout0 W0 K0 zc]. open_cx CX.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  cbn [t_mode t_flags] in Hm, Hfl. subst mode. icx_cbn.
  unfold RNG in RNG_. icx_cbn. cbv [N_CODES N_LENS] in RNG_. destr_conj RNG_.
  pose proof (proj1 PROG_) as PG1. pose proof (proj1 (proj2 PROG_)) as PG2. clear PROG_. unfold Wm in PG1, PG2. icx_cbn.
  assert (Hf0 : flags = 0) by lia. subst flags. clear Hfl.
  unfold s_regs_arm, s_fix, s_vars in RE. icx_cbn. destr_conj RE.
  pose proof (hold_u64 hold bits ltac:(lia) ltac:(lia)) as Hh64.
  pose proof CST as CST'. unfold i_cst in CST'. icx_cbn. dand CST' as (_ & _ & _ & H16 & _).
  pose proof SREST as SR'. unfold st_rest in SR'. icx_cbn. dand SR' as (_ & H24 & _).
  zkeysb. unfold L_LENGTH, L_LEAVE in *.
  pose proof two64_eq as TW64.
  fp_frame_from HP0.
  tstep1 Rfd.
  zbr Rfd false.
  tstep1 Rfd.
  zbr Rfd true.
  zstep Rfd. zstep Rfd.
  zstep Rfd.
  zstep Rfd. zlit.
  clear H16 H24.
  tstep1 Rfd.
  zstep Rfd.
  zstep Rfd. zstep Rfd.
  zstep Rfd.
  pose proof (sinv_ck _ _ lf cf DONE cin hold bits out SI0 eq_refl ltac:((first [solve [zkeep_section; tauto] | tauto]))
                ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)
                ltac:(left; split; [reflexivity | intros _; cbv; reflexivity])) as SI1.
  lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
    eapply (KL R' Mx (ck_st (IST LENGTH last 0 cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext)
                             DONE cin hold bits out) 1 lf cf SI1) end.
  - unfold s_regs_leave, ck_st; icx_cbn; zkeys; split_conj; zreg.
  - close_std.
  - unfold ck_st; split; [assumption | exact SREST].
  - exact SLO.
  - sbk.
  - exact Hlens.
  - exact Hcodes.
  - exact HAG.
Qed.

Theorem arm_LENGTH_t {RCa1 : RunCtx}  : arm_stmt L_LENGTH LENGTH.
Proof. intros cx fin MD T M0 Rb l M st lf cf CX Hh Hfin Hm SI RE KM K. eapply length_body_t; eassumption. Qed.
End T_Check.

