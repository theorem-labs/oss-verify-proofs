(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.I9S Require SBase S_Entry SMemsetOk.

Module S_Uw.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.I9S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Definition L_UW_BODY : Z := 94300.
Definition L_UW_EPI : Z := 94468.
Definition L_UW_TAIL : Z := 94504.

Section Uw.
Hypothesis MEMCPY : memcpy_spec_s.

Lemma uw_epi_s : forall Rb l M MD T (spc ret rv v0 v1 v2 v3 v4 : Z),
  m_halted MD = None ->
  zget_l Rb l kSP = spc + -48 -> zget_l Rb l kS2 = rv ->
  0 <= spc + -48 -> spc <= 140737488355328 ->
  mem_u64 R_segs M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 R_segs M (spc + -16) v0 -> mem_u64 R_segs M (spc + -24) v1 -> mem_u64 R_segs M (spc + -32) v2 ->
  mem_u64 R_segs M (spc + -40) v3 -> mem_u64 R_segs M (spc + -48) v4 ->
  (forall R',
     zget R' kSP = spc -> zget R' kA0 = rv ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     realizes R_segs (zcfg R_segs ret (zupd R' []) M MD) T) ->
  realizes R_segs (zcfg R_segs L_UW_EPI (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T spc ret rv v0 v1 v2 v3 v4 Hh Lsp Ls2 Hc1 Hc2 Hra Hret Hrr H0 H1 H2 H3 H4 K.
  zkeys. unfold L_UW_EPI in *. pose proof two64_eq as TW64.
  zstep Rfd.
  zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.
  zstep Rfd.
  zret Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ ?R _ _) _ => apply (K R) end; zreg.
Qed.


Lemma uw_tail_s : forall Rb l M MD T (p spc whave wnext dist zc : Z),
  m_halted MD = None ->
  zget_l Rb l kS3 = p -> zget_l Rb l kS4 = dist -> zget_l Rb l kSP = spc + -48 ->
  0 < p -> p + STATE_SIZE <= zc -> zc <= spc + -48 -> spc <= 140737488355328 ->
  mem_wr R_segs M p STATE_SIZE ->
  mem_u32 R_segs M (p + 72) WIN_SIZE -> mem_u32 R_segs M (p + 76) whave -> mem_u32 R_segs M (p + 80) wnext ->
  0 <= whave -> whave <= WIN_SIZE -> 0 <= wnext -> wnext < WIN_SIZE -> (whave < WIN_SIZE -> wnext = whave) ->
  0 <= dist -> wnext + dist <= WIN_SIZE ->
  (forall R' M' whave' wnext',
     zget R' kS3 = p -> zget R' kS4 = dist -> zget R' kSP = spc + -48 -> zget R' kS2 = 0 ->
     zget R' kS0 = zget_l Rb l kS0 -> zget R' kS1 = zget_l Rb l kS1 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 R_segs M' (p + 72) WIN_SIZE -> mem_u32 R_segs M' (p + 76) whave' -> mem_u32 R_segs M' (p + 80) wnext' ->
     mpostL R_segs M M' [(p + 76, 8)] ->
     realizes R_segs (zcfg R_segs L_UW_EPI (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_UW_TAIL (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p spc whave wnext dist zc Hh Ls3 Ls4 Lsp Hp0 Hp1 Hc1 Hc2 Wp H60 H64 H68
         Wh0 Wh1 Wn0 Wn1 Whn Hd0 Hd1 K.
  zkeys. unfold L_UW_TAIL, L_UW_EPI in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable R_segs M [(p + 76, 8)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X [(p + 76, 8)]) M) by (apply mpostL_refl).
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
Definition L_UW_FULL : Z := 94436.
Definition L_UW_PART : Z := 94312.

Lemma uw_full_s : forall Rb l M MD T (p ob osz wa cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z) (M0 : mem),
  m_halted MD = None ->
  zget_l Rb l kA0 = wa -> zget_l Rb l kA1 = WIN_SIZE -> zget_l Rb l kS0 = ob + cout -> zget_l Rb l kS1 = copy ->
  zget_l Rb l kS3 = p -> zget_l Rb l kSP = spc + -48 ->
  zc <= spc + -48 -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -48 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 < wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  WIN_SIZE <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  mem_wr R_segs M p STATE_SIZE -> mem_wr R_segs M wa WIN_SIZE ->
  mem_u32 R_segs M (p + 72) WIN_SIZE -> mem_u64 R_segs M (p + 88) wa ->
  mem_arr 1 R_segs M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_u64 R_segs M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 R_segs M (spc + -16) v0 -> mem_u64 R_segs M (spc + -24) v1 -> mem_u64 R_segs M (spc + -32) v2 ->
  mem_u64 R_segs M (spc + -40) v3 -> mem_u64 R_segs M (spc + -48) v4 ->
  framed (fun X => mpostL R_segs M0 X (uw_body_fp p wa)) M ->
  (forall R' M' whave' wnext',
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 R_segs M' (p + 72) WIN_SIZE -> mem_u32 R_segs M' (p + 76) whave' -> mem_u32 R_segs M' (p + 80) wnext' ->
     mem_u64 R_segs M' (p + 88) wa ->
     framed (fun X => mpostL R_segs M0 X (uw_body_fp p wa)) M' ->
     realizes R_segs (zcfg R_segs ret (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_UW_FULL (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wa cout copy spc ret v0 v1 v2 v3 v4 zc fo M0
         Hh La0 La1 Ls0 Ls1 Ls3 Lsp Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wp Wwa H60 H72 HOB Hfo Hra Hret Hrr H0 H1 H2 H3 H4 HAG K.
  zkeys. unfold L_UW_FULL in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable R_segs M0 (uw_body_fp p wa) ltac:(unfold uw_body_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  unfold uw_body_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  zstep Rfd.
  zstep Rfd.
  zlit.
  zstep Rfd.
  zstep Rfd.
  pose proof (mem_arr_sub R_segs 1 _ ob osz fo (cout - 32768) 32768 HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
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
      eapply (uw_epi_s R' lc Mx MD T spc ret 0 v0 v1 v2 v3 v4 Hh) end; try zreg; try assumption; try klia.
    intros R9 Q3 Q11 Q9 Q10 Q19 Q20 Q21 Q4 Q5 Q22 Q23 Q24 Q25 Q26 Q27 Q28.
    zimps. zkeys. apply (K R9 M1 32768 0); try assumption; try lia; try zkept.
Qed.

Lemma uw_part_s : forall Rb l M MD T (p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z) (M0 : mem),
  m_halted MD = None ->
  zget_l Rb l kA0 = wa -> zget_l Rb l kA1 = WIN_SIZE -> zget_l Rb l kS0 = ob + cout -> zget_l Rb l kS1 = copy ->
  zget_l Rb l kS3 = p -> zget_l Rb l kSP = spc + -48 ->
  zc <= spc + -48 -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -48 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 < wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  0 <= copy -> copy < WIN_SIZE -> copy <= cout -> cout <= osz ->
  0 <= whave -> whave <= WIN_SIZE -> 0 <= wnext -> wnext < WIN_SIZE -> (whave < WIN_SIZE -> wnext = whave) ->
  mem_wr R_segs M p STATE_SIZE -> mem_wr R_segs M wa WIN_SIZE ->
  mem_u32 R_segs M (p + 72) WIN_SIZE -> mem_u32 R_segs M (p + 76) whave -> mem_u32 R_segs M (p + 80) wnext ->
  mem_u64 R_segs M (p + 88) wa ->
  mem_arr 1 R_segs M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_u64 R_segs M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 R_segs M (spc + -16) v0 -> mem_u64 R_segs M (spc + -24) v1 -> mem_u64 R_segs M (spc + -32) v2 ->
  mem_u64 R_segs M (spc + -40) v3 -> mem_u64 R_segs M (spc + -48) v4 ->
  framed (fun X => mpostL R_segs M0 X (uw_body_fp p wa)) M ->
  (forall R' M' whave' wnext',
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 R_segs M' (p + 72) WIN_SIZE -> mem_u32 R_segs M' (p + 76) whave' -> mem_u32 R_segs M' (p + 80) wnext' ->
     mem_u64 R_segs M' (p + 88) wa ->
     framed (fun X => mpostL R_segs M0 X (uw_body_fp p wa)) M' ->
     realizes R_segs (zcfg R_segs ret (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_UW_PART (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo M0
         Hh La0 La1 Ls0 Ls1 Ls3 Lsp Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcp2 Hcout Wh0 Wh1 Wn0 Wn1 Whn Wp Wwa H60 H64 H68 H72 HOB Hfo Hra Hret Hrr H0 H1 H2 H3 H4 HAG K.
  zkeys. unfold L_UW_PART in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable R_segs M0 (uw_body_fp p wa) ltac:(unfold uw_body_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  unfold uw_body_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  tstep1 Rfd.
  tstep1 Rfd.
  zstep Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (J : forall RJ dist, dist = Z.min (32768 - wnext) copy ->
    zget RJ 11 = wa -> zget RJ 13 = wnext -> zget RJ 9 = ob + cout -> zget RJ 10 = copy -> zget RJ 20 = p ->
    zget RJ 3 = spc + -48 -> zget RJ 19 = 32768 - wnext -> zget RJ 21 = dist ->
    zget RJ 4 = zget_l Rb l 4 -> zget RJ 5 = zget_l Rb l 5 -> zget RJ 22 = zget_l Rb l 22 -> zget RJ 23 = zget_l Rb l 23 ->
    zget RJ 24 = zget_l Rb l 24 -> zget RJ 25 = zget_l Rb l 25 -> zget RJ 26 = zget_l Rb l 26 -> zget RJ 27 = zget_l Rb l 27 ->
    zget RJ 28 = zget_l Rb l 28 ->
    realizes R_segs (zcfg R_segs 94332 (zupd RJ []) Mc MD) T) end.
  { intros RJ dist Hdist G11 G13 G9 G10 G20 G3 G19 G21 G4 G5 G22 G23 G24 G25 G26 G27 G28.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    zstep Rfd. zext32.
    zstep Rfd.
    pose proof (mem_arr_sub R_segs 1 _ ob osz fo (cout - copy) dist HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
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
          eapply (uw_tail_s R [] Mx MD T p spc whave wnext dist zc Hh) end; try zreg; try assumption; try klia.
        intros R2' M2 whave' wnext' Q20 Q21 Q3 Q19 Q9 Q10 Q4 Q5 Q22 Q23 Q24 Q25 Q26 Q27 Q28 W1 W2 W3 W4 W5 C60 C64 C68 HP2.
        zimps. clear H60 H64 H68. zreattachL HP2.
        lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
          eapply (uw_epi_s R [] Mx MD T spc ret 0 v0 v1 v2 v3 v4 Hh) end; try zreg; try assumption; try klia.
        intros R9 X3 X11 X9 X10 X19 X20 X21 X4 X5 X22 X23 X24 X25 X26 X27 X28.
        zimps. zkeys. apply (K R9 M2 whave' wnext'); try assumption; try lia; try zkept.
      +
        zbr Rfd false.
        tstep1 Rfd.
        zstep Rfd.
        zstep Rfd.
        zstep Rfd. zext32.
        zstep Rfd.
        zstep Rfd.
        pose proof (mem_arr_sub R_segs 1 _ ob osz fo (cout - (copy - dist)) (copy - dist) HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc2.
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
            eapply (uw_epi_s R [] Mx MD T spc ret 0 v0 v1 v2 v3 v4 Hh) end; try zreg; try assumption; try klia.
          intros R9 X3 X11 X9 X10 X19 X20 X21 X4 X5 X22 X23 X24 X25 X26 X27 X28.
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

Lemma uw_body_s : forall Rb l M MD T (p ob osz wa ws whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA0 = wa -> zget_l Rb l kS0 = ob + cout -> zget_l Rb l kS1 = copy -> zget_l Rb l kS3 = p ->
  zget_l Rb l kSP = spc + -48 ->
  zc <= spc + -48 -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -48 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 < wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  0 <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  (ws = 0 \/ ws = WIN_SIZE) -> 0 <= whave -> 0 <= wnext ->
  (ws = WIN_SIZE -> whave <= WIN_SIZE /\ wnext < WIN_SIZE /\ (whave < WIN_SIZE -> wnext = whave)) ->
  mem_wr R_segs M p STATE_SIZE -> mem_wr R_segs M wa WIN_SIZE ->
  mem_u32 R_segs M (p + 68) 15 -> mem_u32 R_segs M (p + 72) ws -> mem_u32 R_segs M (p + 76) whave ->
  mem_u32 R_segs M (p + 80) wnext -> mem_u64 R_segs M (p + 88) wa ->
  mem_arr 1 R_segs M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_u64 R_segs M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 R_segs M (spc + -16) v0 -> mem_u64 R_segs M (spc + -24) v1 -> mem_u64 R_segs M (spc + -32) v2 ->
  mem_u64 R_segs M (spc + -40) v3 -> mem_u64 R_segs M (spc + -48) v4 ->
  (forall R' M' whave' wnext',
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 R_segs M' (p + 72) WIN_SIZE -> mem_u32 R_segs M' (p + 76) whave' -> mem_u32 R_segs M' (p + 80) wnext' ->
     mem_u64 R_segs M' (p + 88) wa ->
     mpostL R_segs M M' (uw_body_fp p wa) ->
     realizes R_segs (zcfg R_segs ret (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_UW_BODY (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wa ws whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo
         Hh La0 Ls0 Ls1 Ls3 Lsp Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Hws Wh0 Wn0 Wfacts
         Wp Wwa H56 H60 H64 H68 H72 HOB Hfo Hra Hret Hrr H0 H1 H2 H3 H4 K.
  zkeys. unfold L_UW_BODY in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable R_segs M (uw_body_fp p wa) ltac:(unfold uw_body_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X (uw_body_fp p wa)) M) by (apply mpostL_refl).
  unfold uw_body_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  assert (FULL : forall RJ Mq (whave1 wnext1 : Z), 32768 <= copy ->
    zget RJ 11 = wa -> zget RJ 12 = 32768 -> zget RJ 9 = ob + cout -> zget RJ 10 = copy -> zget RJ 20 = p -> zget RJ 3 = spc + -48 ->
    zget RJ 4 = zget_l Rb l 4 -> zget RJ 5 = zget_l Rb l 5 -> zget RJ 22 = zget_l Rb l 22 -> zget RJ 23 = zget_l Rb l 23 ->
    zget RJ 24 = zget_l Rb l 24 -> zget RJ 25 = zget_l Rb l 25 -> zget RJ 26 = zget_l Rb l 26 -> zget RJ 27 = zget_l Rb l 27 ->
    zget RJ 28 = zget_l Rb l 28 ->
    mem_wr R_segs Mq p 7176 -> mem_wr R_segs Mq wa 32768 ->
    mem_u32 R_segs Mq (p + 72) 32768 -> mem_u64 R_segs Mq (p + 88) wa ->
    mem_arr 1 R_segs Mq ob osz fo ->
    mem_u64 R_segs Mq (spc + -8) ret -> mem_u64 R_segs Mq (spc + -16) v0 -> mem_u64 R_segs Mq (spc + -24) v1 ->
    mem_u64 R_segs Mq (spc + -32) v2 -> mem_u64 R_segs Mq (spc + -40) v3 -> mem_u64 R_segs Mq (spc + -48) v4 ->
    framed (fun X => mpostL R_segs M X [(p + 72, 12); (wa, 32768)]) Mq ->
    realizes R_segs (zcfg R_segs L_UW_FULL (zupd RJ []) Mq MD) T).
  { intros RJ Mq whave1 wnext1 Hc G11 G12 G9 G10 G20 G3 G4 G5 G22 G23 G24 G25 G26 G27 G28 Wp' Wwa' C60 C72 HOB' Cra C0 C1 C2 C3 C4 HAG'.
    eapply (uw_full_s RJ [] Mq MD T p ob osz wa cout copy spc ret v0 v1 v2 v3 v4 zc fo M Hh); try zreg; try assumption; try klia. }
  assert (PART : forall RJ Mq (whave1 wnext1 : Z), copy < 32768 ->
    0 <= whave1 -> whave1 <= 32768 -> 0 <= wnext1 -> wnext1 < 32768 -> (whave1 < 32768 -> wnext1 = whave1) ->
    zget RJ 11 = wa -> zget RJ 12 = 32768 -> zget RJ 9 = ob + cout -> zget RJ 10 = copy -> zget RJ 20 = p -> zget RJ 3 = spc + -48 ->
    zget RJ 4 = zget_l Rb l 4 -> zget RJ 5 = zget_l Rb l 5 -> zget RJ 22 = zget_l Rb l 22 -> zget RJ 23 = zget_l Rb l 23 ->
    zget RJ 24 = zget_l Rb l 24 -> zget RJ 25 = zget_l Rb l 25 -> zget RJ 26 = zget_l Rb l 26 -> zget RJ 27 = zget_l Rb l 27 ->
    zget RJ 28 = zget_l Rb l 28 ->
    mem_wr R_segs Mq p 7176 -> mem_wr R_segs Mq wa 32768 ->
    mem_u32 R_segs Mq (p + 72) 32768 -> mem_u32 R_segs Mq (p + 76) whave1 -> mem_u32 R_segs Mq (p + 80) wnext1 -> mem_u64 R_segs Mq (p + 88) wa ->
    mem_arr 1 R_segs Mq ob osz fo ->
    mem_u64 R_segs Mq (spc + -8) ret -> mem_u64 R_segs Mq (spc + -16) v0 -> mem_u64 R_segs Mq (spc + -24) v1 ->
    mem_u64 R_segs Mq (spc + -32) v2 -> mem_u64 R_segs Mq (spc + -40) v3 -> mem_u64 R_segs Mq (spc + -48) v4 ->
    framed (fun X => mpostL R_segs M X [(p + 72, 12); (wa, 32768)]) Mq ->
    realizes R_segs (zcfg R_segs L_UW_PART (zupd RJ []) Mq MD) T).
  { intros RJ Mq whave1 wnext1 Hc W1 W2 W3 W4 W5 G11 G12 G9 G10 G20 G3 G4 G5 G22 G23 G24 G25 G26 G27 G28 Wp' Wwa' C60 C64 C68 C72 HOB' Cra C0 C1 C2 C3 C4 HAG'.
    eapply (uw_part_s RJ [] Mq MD T p ob osz wa whave1 wnext1 cout copy spc ret v0 v1 v2 v3 v4 zc fo M Hh); try zreg; try assumption; try klia. }
  unfold L_UW_FULL, L_UW_PART in FULL, PART.
  tstep1 Rfd.
  destruct Hws as [Hws0 | Hws1]; subst ws.
  - zbr Rfd true.
    tstep1 Rfd.
    zstep Rfd.
    zstep Rfd. zlit.
    tstep1 Rfd.                       (* sw a1,72(s3): wsize *)
    (* 1.4: whave (p+76) and wnext (p+80) are cleared by two sw (76 is not 8-aligned), not one sd *)
    tstep1 Rfd.                       (* sw zero,76(s3) *)
    tstep1 Rfd.                       (* sw zero,80(s3) *)
    match goal with H1 : mem_u32 R_segs ?Mx (p + 76) 0, H2 : mem_u32 R_segs ?Mx (p + 80) 0 |- _ =>
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

Definition uw_fp (p wa spc : Z) : list (Z * Z) := [(spc + -48, 48); (p + 72, 12); (wa, WIN_SIZE)].

Lemma uw_entry_s : forall Rb l M MD T (u p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA0 = u -> zget_l Rb l kA1 = ob + cout -> zget_l Rb l kA2 = copy -> zget_l Rb l kSP = spc ->
  zget_l Rb l kRA = ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  zget_l Rb l kS0 = v0 -> zget_l Rb l kS1 = v1 -> zget_l Rb l kS2 = v2 -> zget_l Rb l kS3 = v3 -> zget_l Rb l kS4 = v4 ->
  zc + FRA <= u -> u + 208 <= 140737488355328 -> zc <= spc + -48 -> spc <= u ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -48 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 <= wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (wa = 0 \/ p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa = 0 \/ wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  0 <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  0 <= whave -> 0 <= wnext ->
  (wa <> 0 -> whave <= WIN_SIZE /\ wnext < WIN_SIZE /\ (whave < WIN_SIZE -> wnext = whave)) ->
  mem_wr R_segs M (spc + -48) 48 -> mem_wr R_segs M p STATE_SIZE -> (wa <> 0 -> mem_wr R_segs M wa WIN_SIZE) ->
  mem_u64 R_segs M (u + 56) p -> mem_u64 R_segs M (u + 64) A_ZCALLOC -> mem_u64 R_segs M (u + 80) 0 ->
  mem_u32 R_segs M (p + 68) 15 -> mem_u32 R_segs M (p + 72) (if wa =? 0 then 0 else WIN_SIZE) ->
  mem_u32 R_segs M (p + 76) whave -> mem_u32 R_segs M (p + 80) wnext -> mem_u64 R_segs M (p + 88) wa ->
  mem_arr 1 R_segs M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  (forall R' M', wa = 0 ->
     zget R' kA3 = A_ZCALLOC -> zget R' kA0 = 0 -> zget R' kA1 = WIN_SIZE -> zget R' kA2 = 1 ->
     zget R' kS0 = ob + cout -> zget R' kS1 = copy -> zget R' kS2 = 1 -> zget R' kS3 = p -> zget R' kS4 = v4 ->
     zget R' kSP = spc + -48 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     mem_u64 R_segs M' (spc + -8) ret -> mem_u64 R_segs M' (spc + -16) v0 -> mem_u64 R_segs M' (spc + -24) v1 ->
     mem_u64 R_segs M' (spc + -32) v2 -> mem_u64 R_segs M' (spc + -40) v3 -> mem_u64 R_segs M' (spc + -48) v4 ->
     mpostL R_segs M M' [(spc + -48, 48)] ->
     realizes R_segs (zcfg R_segs T_ZW (zupd R' []) M' MD) T) ->
  (forall R' M' whave' wnext', wa <> 0 ->
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 R_segs M' (p + 72) WIN_SIZE -> mem_u32 R_segs M' (p + 76) whave' -> mem_u32 R_segs M' (p + 80) wnext' ->
     mem_u64 R_segs M' (p + 88) wa ->
     mpostL R_segs M M' (uw_fp p wa spc) ->
     realizes R_segs (zcfg R_segs ret (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_UW (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo
         Hh La0 La1 La2 Lsp Lra Hret Hrr Ls0 Ls1 Ls2 Ls3 Ls4
         Hu0 Hu1 Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wh0 Wn0 Wfacts Wfr Wp Wwa H64u H72u H88u H56 H60 H64 H68 H72 HOB Hfo KW K.
  zkeys. unfold L_UW, T_ZW in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable R_segs M (uw_fp p wa spc) ltac:(unfold uw_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X (uw_fp p wa spc)) M) by (apply mpostL_refl).
  unfold uw_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  Local Ltac prologue :=
    zstep Rfd;
    do 6 (tstep1 Rfd);
    zstep Rfd;
    zstep Rfd;
    tstep1 Rfd;
    tstep1 Rfd;
    zstep Rfd.
  destruct (Z.eq_dec wa 0) as [Wz | Wnz].
  -
    clear Wwa Wfacts. subst wa.
    pose proof (mpostL_stable R_segs M [(spc + -48, 48)] ltac:(ranges_ok_tac)) as HST';
    assert (HAG' : framed (fun X => mpostL R_segs M X [(spc + -48, 48)]) M) by (apply mpostL_refl).
    prologue.
    zbr Rfd false.
    tstep1 Rfd.
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
      eapply (uw_body_s R [] Mx MD T p ob osz wa (if wa =? 0 then 0 else 32768) whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo Hh) end;
      try zreg; try assumption; try klia.
    + slia.
    + slia.
    + destruct (Z.eqb_spec wa 0); [lia_std | right; reflexivity].
    + intros R9 M9 whave' wnext'. intros. zimps.
      match goal with HP : mpostL R_segs _ M9 _ |- _ => unfold uw_body_fp in HP; cbv [WIN_SIZE] in HP; zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K R9 Mx whave' wnext' Wnz) end; try assumption; try zkept.
Qed.

Definition uw_res_fp (p wres spc : Z) : list (Z * Z) := [(spc + -48, 48); (p + 72, 24); (wres, WIN_SIZE)].

Lemma uw_resume_s : forall Rb l M MD T (p ob osz wres cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kA0 = wres -> zget_l Rb l kS0 = ob + cout -> zget_l Rb l kS1 = copy -> zget_l Rb l kS2 = 1 ->
  zget_l Rb l kS3 = p -> zget_l Rb l kSP = spc + -48 ->
  zc <= spc + -48 -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + -48 \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 <= wres -> wres + WIN_SIZE <= zc -> wres mod 16 = 0 ->
  ZSEP (wres = 0 \/ p + STATE_SIZE <= wres \/ wres + WIN_SIZE <= p) -> ZSEP (wres = 0 \/ wres + WIN_SIZE <= ob \/ ob + osz <= wres) ->
  0 <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  mem_wr R_segs M (spc + -48) 48 -> mem_wr R_segs M p STATE_SIZE -> (wres <> 0 -> mem_wr R_segs M wres WIN_SIZE) ->
  mem_u32 R_segs M (p + 68) 15 -> mem_u32 R_segs M (p + 72) 0 -> mem_u64 R_segs M (p + 88) 0 ->
  mem_arr 1 R_segs M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_u64 R_segs M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 R_segs M (spc + -16) v0 -> mem_u64 R_segs M (spc + -24) v1 -> mem_u64 R_segs M (spc + -32) v2 ->
  mem_u64 R_segs M (spc + -40) v3 -> mem_u64 R_segs M (spc + -48) v4 ->
  (forall R' M', wres = 0 ->
     zget R' kSP = spc -> zget R' kA0 = 1 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     mem_u32 R_segs M' (p + 72) 0 -> mem_u64 R_segs M' (p + 88) 0 ->
     mpostL R_segs M M' [(spc + -48, 48); (p + 72, 24)] ->
     realizes R_segs (zcfg R_segs ret (zupd R' []) M' MD) T) ->
  (forall R' M' whave' wnext', wres <> 0 ->
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 R_segs M' (p + 72) WIN_SIZE -> mem_u32 R_segs M' (p + 76) whave' -> mem_u32 R_segs M' (p + 80) wnext' ->
     mem_u64 R_segs M' (p + 88) wres ->
     mpostL R_segs M M' (uw_res_fp p wres spc) ->
     realizes R_segs (zcfg R_segs ret (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_ZB (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wres cout copy spc ret v0 v1 v2 v3 v4 zc fo
         Hh La0 Ls0 Ls1 Ls2 Ls3 Lsp Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hw0 Hw1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wfr Wp Ww H56 H60 H72 HOB Hfo Hra Hret Hrr H0 H1 H2 H3 H4 K0 K1.
  zkeys. unfold L_ZB in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable R_segs M (uw_res_fp p wres spc) ltac:(unfold uw_res_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X (uw_res_fp p wres spc)) M) by (apply mpostL_refl).
  unfold uw_res_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  destruct (Z.eq_dec wres 0) as [Wz | Wnz].
  - clear Ww. revert La0. subst wres. intros La0.
    pose proof (mpostL_stable R_segs M [(spc + -48, 48); (p + 72, 24)] ltac:(ranges_ok_tac)) as HST';
    assert (HAG' : framed (fun X => mpostL R_segs M X [(spc + -48, 48); (p + 72, 24)]) M) by (apply mpostL_refl).
    tstep1 Rfd.
    zbr Rfd true.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
      eapply (uw_epi_s R [] Mx MD T spc ret 1 v0 v1 v2 v3 v4 Hh) end; try zreg; try assumption; try klia.
    intros R9. intros. zimps. zkeys.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K0 R9 Mx eq_refl) end; try assumption; try zkept; try exact HAG'.
  - specialize (Ww Wnz).
    destruct (mem_wr_u32_exists_R M (p + 76) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (wh0 & Hwh0 & Rwh0).
    destruct (mem_wr_u32_exists_R M (p + 80) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (wn0 & Hwn0 & Rwn0).
    tstep1 Rfd.
    zbr Rfd false.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R ?Mx _) _ =>
      eapply (uw_body_s R [] Mx MD T p ob osz wres 0 wh0 wn0 cout copy spc ret v0 v1 v2 v3 v4 zc fo Hh) end;
      try zreg; try assumption; try klia.
    + slia.
    + slia.
    + intros R9 M9 whave' wnext'. intros. zimps.
      match goal with HP : mpostL R_segs _ M9 _ |- _ => unfold uw_body_fp in HP; cbv [WIN_SIZE] in HP; zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K1 R9 Mx whave' wnext' Wnz) end; try assumption; try zkept.
Qed.
End Uw.
End FXG.
End S_Uw.

Module S_U2A.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.I9S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

(* 1.4: the za walk is new code at 1.4. inflateInit_ (from the zalloc return, 0x150f0) memsets the state
   (memset(p + 8, 0, 7168), SMemsetOk.memset7168_ok), stores strm / mode / strm->state, wrap 5 and wbits 15, then calls
   the one 1.4 inflateReset (0x14f0c; window unchanged, keep-reset inline); inflateInit_ returns 0 to uncompress2_z
   (0x14dc0), which sets next_out = BUF, avail_out = BUF_N, avail_in = n (len and left fall to 0, s2 = max) and
   reaches the first inflate call (0x14e30). The fields memset leaves zero are handed on as 0. *)
Definition L_ZA : Z := 86352.              (* 0x150f0: inflateInit_ after jalr zalloc *)
Definition L_CALL2 : Z := 85648.           (* 0x14e30: uncompress2_z, mv a0,sp before the first jal inflate *)
Definition RA_II : Z := 85536.             (* 0x14dc0: uncompress2_z after jal inflateInit_ *)

End FXG.
Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Lemma mem_u32_relit : forall M a e e', mem_u32 R_segs M a e -> e mod 4294967296 = e' mod 4294967296 -> mem_u32 R_segs M a e'.
Proof.
  intros M a e e' H E. unfold mem_u32 in *.
  rewrite <- (Z_to_le_bytes_mod32 4 e) in H by lia. rewrite E, Z_to_le_bytes_mod32 in H by lia. exact H.
Qed.

(* 1.4: a u32 / u64 zero inside a memset region *)
Lemma mz_u32 : forall M a len off, mem_zero R_segs M a len -> 0 <= off -> off + 4 <= len -> 0 <= a + off ->
  a + off + 4 <= two64 -> mem_u32 R_segs M (a + off) 0.
Proof.
  intros M a len off Hz H1 H2 H3 H4. unfold mem_u32, mem_is. change (length (Z_to_le_bytes 4 0)) with 4%nat.
  rewrite (mem_zero_sub R_segs M a len off 4 Hz) by lia. reflexivity.
Qed.
Lemma mz_u64 : forall M a len off, mem_zero R_segs M a len -> 0 <= off -> off + 8 <= len -> 0 <= a + off ->
  a + off + 8 <= two64 -> mem_u64 R_segs M (a + off) 0.
Proof.
  intros M a len off Hz H1 H2 H3 H4. unfold mem_u64, mem_is. change (length (Z_to_le_bytes 8 0)) with 8%nat.
  rewrite (mem_zero_sub R_segs M a len off 8 Hz) by lia. reflexivity.
Qed.

(* 1.4: split the u64 fact at a (on the current memory) into its two u32 halves *)
End FXG.
Ltac split64 a ahi nlo nhi :=
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    match goal with H : mem_u64 R_segs Mx a _ |- _ =>
      pose proof (mem_u64_lo32 _ _ _ _ H) as nlo; pose proof (mem_u64_hi32 _ _ _ _ H) as nhi; cbn in nhi;
      replace (a + 4) with ahi in nhi by lia
    end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.PropExec.FPState}.

Theorem za_prefix_s : forall Rb l M MD T (u p q n zc : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z),
  m_halted MD = None ->
  zget_l Rb l kSP = u + -32 -> zget_l Rb l kS1 = u -> zget_l Rb l kA0 = p ->
  zget_l Rb l kS3 = n -> zget_l Rb l kS4 = 262144 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  zc + FRA <= u -> DATA_LO + DATA_LEN <= zc -> u + 208 <= 140737488355328 -> u mod 16 = 0 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= zc ->
  ZSEP (p + STATE_SIZE <= q \/ q + n <= p) -> ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p) ->
  rom_ok M -> mem_wr R_segs M (u + -1024) 1232 -> mem_wr R_segs M p STATE_SIZE ->
  mem_arr 1 R_segs M q n fin ->
  mem_u64 R_segs M (u + -32) BUF -> mem_u64 R_segs M (u + -24) (u + 160) -> mem_u64 R_segs M (u + -16) (u + 168) ->
  mem_u64 R_segs M (u + -8) RA_II ->
  mem_u64 R_segs M u q -> mem_u32 R_segs M (u + 8) 0 ->
  mem_u64 R_segs M (u + 64) A_ZCALLOC -> mem_u64 R_segs M (u + 72) A_ZCFREE -> mem_u64 R_segs M (u + 80) 0 ->
  (forall R' M' (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z),
     zget R' kSP = u ->
     zget R' kS0 = u + 168 -> zget R' kS1 = u + 160 -> zget R' kS2 = 4294967295 -> zget R' kS3 = 0 -> zget R' kS4 = 0 ->
     zget R' kS5 = s5 -> zget R' kGP = gp -> zget R' kTP = tp ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     rom_ok M' -> mem_wr R_segs M' (u + -1024) 1232 -> mem_wr R_segs M' p STATE_SIZE -> mem_arr 1 R_segs M' q n fin ->
     mem_u64 R_segs M' u q -> mem_u32 R_segs M' (u + 8) n -> mem_u64 R_segs M' (u + 24) BUF -> mem_u32 R_segs M' (u + 32) 262144 ->
     mem_u64 R_segs M' (u + 56) p -> mem_u64 R_segs M' (u + 64) A_ZCALLOC -> mem_u64 R_segs M' (u + 72) A_ZCFREE -> mem_u64 R_segs M' (u + 80) 0 ->
     mem_u64 R_segs M' p u -> mem_u32 R_segs M' (p + 8) HEAD -> mem_u32 R_segs M' (p + 12) 0 ->
     mem_u32 R_segs M' (p + 16) 5 -> mem_u32 R_segs M' (p + 28) (-1) -> mem_u64 R_segs M' (p + 56) 0 ->
     mem_u32 R_segs M' (p + 68) 15 -> mem_u32 R_segs M' (p + 72) 0 -> mem_u32 R_segs M' (p + 76) 0 -> mem_u32 R_segs M' (p + 80) 0 ->
     mem_u64 R_segs M' (p + 88) 0 -> mem_u64 R_segs M' (p + 96) 0 -> mem_u32 R_segs M' (p + 104) 0 ->
     mem_u32 R_segs M' (p + 108) vlen -> mem_u32 R_segs M' (p + 112) vofs -> mem_u32 R_segs M' (p + 116) vext ->
     mem_u64 R_segs M' (p + 120) (p + 1384) -> mem_u64 R_segs M' (p + 128) (p + 1384) ->
     mem_u32 R_segs M' (p + 136) vlb -> mem_u32 R_segs M' (p + 140) vdb ->
     mem_u32 R_segs M' (p + 144) vnc -> mem_u32 R_segs M' (p + 148) vnl -> mem_u32 R_segs M' (p + 152) vnd -> mem_u32 R_segs M' (p + 156) vsh ->
     mem_u64 R_segs M' (p + 160) (p + 1384) -> mem_u32 R_segs M' (p + 7160) 1 ->
     0 <= vlen < 4294967296 -> 0 <= vofs < 4294967296 -> 0 <= vext < 4294967296 -> 0 <= vlb < 4294967296 -> 0 <= vdb < 4294967296 ->
     0 <= vnc < 4294967296 -> 0 <= vnl < 4294967296 -> 0 <= vnd < 4294967296 -> 0 <= vsh < 4294967296 ->
     mpostL R_segs M M' [(u + -80, 48); (u, 112); (p, STATE_SIZE)] ->
     realizes R_segs (zcfg R_segs L_CALL2 (zupd R' []) M' MD) T) ->
  realizes R_segs (zcfg R_segs L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin
         Hh Lsp Ls1 La0 Ls3 Ls4 Lgp Ltp Ls5 Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Sprom
         ROM Wstk Wp Hin Fm32 Fm24 Fm16 Fm8 S8 S16 S72 S80 S88 K.
  zkeysb. unfold L_ZA, L_CALL2, RA_II in *. cbv [STATE_SIZE FRA ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF HEAD DATA_LO DATA_LEN] in *.
  pose proof two64_eq as TW64.
  pose proof (mpostL_stable R_segs M [(u + -80, 48); (u, 112); (p, 7176)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL R_segs M X [(u + -80, 48); (u, 112); (p, 7176)]) M) by (apply mpostL_refl).
  (* inflateInit_ after zalloc: the state pointer is not NULL; memset(p + 8, 0, 7168) *)
  zbr Rfd false.                      (* 150f0 beqz a0 *)
  zstep Rfd.                          (* 150f4 mv s0,a0 *)
  zstep Rfd.                          (* 150f8 addi a0,a0,8 *)
  zstep Rfd.                          (* 150fc li a2,7 *)
  tstep1 Rfd.                         (* 15100 slli a2,a2,10 *)
  zstep Rfd.                          (* 15104 li a1,0 *)
  zstep Rfd.                          (* 15108 jal memset *)
  lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?R ?lc) ?Mx _) _ =>
    eapply (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.I9S.SMemsetOk.memset7168_ok R lc Mx MD T (p + 8) 86380 Hh) end.
  - zreg. - zreg. - zreg. - zreg. - reflexivity.
  - eapply mem_wr_sub; [exact Wp | lia | lia].
  - lia. - lia.
  - Z.to_euclidean_division_equations; lia.
  - intros M1 R1 HP HZ HW1 E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
    zimps. apply mpost_mpostL1 in HP. zreattachL HP.
    (* the fields memset leaves zero and nothing below stores over *)
    pose proof (mz_u64 M1 (p + 8) 7168 80 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z88.
    pose proof (mz_u32 M1 (p + 8) 7168 100 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z108.
    pose proof (mz_u32 M1 (p + 8) 7168 104 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z112.
    pose proof (mz_u32 M1 (p + 8) 7168 108 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z116.
    pose proof (mz_u32 M1 (p + 8) 7168 128 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z136.
    pose proof (mz_u32 M1 (p + 8) 7168 132 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z140.
    pose proof (mz_u32 M1 (p + 8) 7168 136 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z144.
    pose proof (mz_u32 M1 (p + 8) 7168 140 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z148.
    pose proof (mz_u32 M1 (p + 8) 7168 144 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z152.
    pose proof (mz_u32 M1 (p + 8) 7168 148 HZ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Z156.
    replace (p + 8 + 80) with (p + 88) in Z88 by lia.
    replace (p + 8 + 100) with (p + 108) in Z108 by lia. replace (p + 8 + 104) with (p + 112) in Z112 by lia.
    replace (p + 8 + 108) with (p + 116) in Z116 by lia. replace (p + 8 + 128) with (p + 136) in Z136 by lia.
    replace (p + 8 + 132) with (p + 140) in Z140 by lia. replace (p + 8 + 136) with (p + 144) in Z144 by lia.
    replace (p + 8 + 140) with (p + 148) in Z148 by lia. replace (p + 8 + 144) with (p + 152) in Z152 by lia.
    replace (p + 8 + 148) with (p + 156) in Z156 by lia.
    clear HZ.
    (* back in inflateInit_: state->strm, mode = HEAD, strm->state; wrap 5, wbits 15; inflateReset *)
    tstep1 Rfd.                       (* 1510c lui a0,0x4 *)
    zstep Rfd.                        (* 15110 mv a1,s1 *)
    zstep Rfd.                        (* 15114 ld a2,64(s1) *)
    zstep Rfd.                        (* 15118 addi a0,a0,-204 *)
    zstep Rfd.                        (* 1511c sd s1,0(s0) *)
    zstep Rfd.                        (* 15120 sw a0,8(s0) *)
    zstep Rfd.                        (* 15124 sd s0,56(s1) *)
    zbr Rfd false.                    (* 15128 beqz a2 *)
    zstep Rfd.                        (* 1512c li a0,5 *)
    zstep Rfd.                        (* 15130 li a2,15 *)
    tstep1 Rfd.                       (* 15134 slli a0,a0,32 *)
    tstep1 Rfd.                       (* 15138 slli a2,a2,32 *)
    zstep Rfd.                        (* 1513c addi a0,a0,5 *)
    zstep Rfd.                        (* 15140 addi a2,a2,15 *)
    zstep Rfd.                        (* 15144 sd a0,16(s0) *)
    zstep Rfd.                        (* 15148 sd a2,64(s0) *)
    split64 (p + 16) (p + 20) W16 W20. split64 (p + 64) (p + 68) W64 W68.
    zstep Rfd.                        (* 1514c mv a0,a1 *)
    zstep Rfd.                        (* 15150 jal inflateReset *)
    (* inflateReset (0x14f0c): frame 32; the state checks *)
    zstep Rfd.                        (* 14f0c addi sp,sp,-32 *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* sd ra, s0, s1, s2 *)
    zstep Rfd.                        (* 14f20 mv s0,a0 *)
    zstep Rfd.                        (* 14f24 li a0,-2 *)
    zbr Rfd false.                    (* 14f28 beqz s0 *)
    zstep Rfd. zbr Rfd false.         (* ld a1,64(s0); beqz a1 *)
    zstep Rfd. zbr Rfd false.         (* ld a2,72(s0); beqz a2 *)
    zstep Rfd. zbr Rfd false.         (* ld s2,56(s0); beqz s2 *)
    zstep Rfd. zbr Rfd true.          (* ld a1,0(s2); beq a1,s0 *)
    zstep Rfd.                        (* 14f64 lw a1,8(s2) *)
    tstep1 Rfd.                       (* 14f68 lui a3,0xffffc *)
    zstep Rfd.                        (* 14f6c addi s1,a3,204 *)
    zstep Rfd.                        (* 14f70 addw a1,a1,s1 *)
    zstep Rfd.                        (* 14f74 li a3,31 *)
    zbr Rfd false.                    (* 14f78 bltu a3,a1 *)
    zstep Rfd.                        (* 14f7c lw a3,64(s2) *)
    zstep Rfd.                        (* 14f80 lw a1,68(s2) *)
    zbr Rfd true.                     (* 14f84 beq a1,a3: the window size is unchanged *)
    zstep Rfd.                        (* 14fc8 lw a1,20(s2) *)
    zstep Rfd.                        (* 14fcc sw a1,16(s2) *)
    zstep Rfd.                        (* 14fd0 sd zero,72(s2) *)
    zstep Rfd.                        (* 14fd4 sw zero,80(s2) *)
    (* the keep-reset part, inline *)
    zstep Rfd. zbr Rfd false.         (* ld a1,72(s0); beqz a1 *)
    zstep Rfd. zbr Rfd false.         (* ld a1,56(s0); beqz a1 *)
    zstep Rfd. zbr Rfd false.         (* ld a2,0(a1); bne a2,s0 *)
    zstep Rfd.                        (* 14ff0 lw a2,8(a1) *)
    zstep Rfd.                        (* 14ff4 addw a2,a2,s1 *)
    zstep Rfd.                        (* 14ff8 li a3,31 *)
    zbr Rfd false.                    (* 14ffc bltu a3,a2 *)
    zstep Rfd.                        (* 15000 sd zero,48(a1) *)
    zstep Rfd.                        (* 15004 sd zero,16(s0) *)
    zstep Rfd.                        (* 15008 sd zero,40(s0) *)
    zstep Rfd.                        (* 1500c sd zero,48(s0) *)
    zstep Rfd.                        (* 15010 lwu a0,16(a1) *)
    tstep1 Rfd.                       (* 15014 lui a2,0x2 *)
    zstep Rfd.                        (* 15018 addiw a2,a2,-1032 *)
    zstep Rfd.                        (* 1501c add a2,a1,a2 *)
    zstep Rfd.                        (* 15020 sw zero,88(s0) *)
    zbr Rfd false.                    (* 15024 beqz a0 *)
    zstep Rfd.                        (* 15028 andi a0,a0,1 *)
    zstep Rfd.                        (* 1502c sd a0,96(s0) *)
    zstep Rfd.                        (* 15030 li a0,0 *)
    tstep1 Rfd.                       (* 15034 lui a3,0x4 *)
    zstep Rfd.                        (* 15038 li a4,-1 *)
    zstep Rfd.                        (* 1503c addi a5,a1,1384 *)
    zstep Rfd.                        (* 15040 sd a5,160(a1) *)
    zstep Rfd.                        (* 15044 sd zero,96(a1) *)
    zstep Rfd.                        (* 15048 sw zero,104(a1) *)
    zstep Rfd.                        (* 1504c sd a5,120(a1) *)
    zstep Rfd.                        (* 15050 sd a5,128(a1) *)
    tstep1 Rfd.                       (* 15054 lui a5,0x8 *)
    zstep Rfd.                        (* 15058 addiw a3,a3,-204 *)
    tstep1 Rfd.                       (* 1505c slli a4,a4,32 *)
    zstep Rfd.                        (* 15060 sd a3,8(a1) *)
    zstep Rfd.                        (* 15064 sd a4,24(a1) *)
    zstep Rfd.                        (* 15068 sw a5,32(a1) *)
    zstep Rfd.                        (* 1506c sd zero,56(a1) *)
    zstep Rfd.                        (* 15070 addi a4,a4,1 *)
    zstep Rfd.                        (* 15074 sd a4,0(a2) *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* ld ra, s0, s1, s2 *)
    zstep Rfd.                        (* 15088 addi sp,sp,32 *)
    zret Rfd.                         (* 1508c ret *)
    (* inflateInit_ returns Z_OK *)
    zbr Rfd true.                     (* 15154 beqz a0 *)
    zstep Rfd.                        (* 151c8 li a3,0 *)
    zstep Rfd. zstep Rfd. zstep Rfd. zstep Rfd.   (* ld ra, s0, s1, s2 *)
    zstep Rfd.                        (* 151dc addi sp,sp,32 *)
    zstep Rfd.                        (* 151e0 mv a0,a3 *)
    zret Rfd.                         (* 151e4 ret *)
    (* uncompress2_z: next_out = BUF, avail_out = 0, max = 2^32 - 1; the first refills *)
    zbr Rfd false.                    (* 14dc0 bnez a0 *)
    zstep Rfd.                        (* 14dc4 or a0,s2,s4 *)
    zbr Rfd true.                     (* 14dc8 bnez a0 *)
    zstep Rfd.                        (* 14dd0 sd s2,24(sp) *)
    zstep Rfd.                        (* 14dd4 sw zero,32(sp) *)
    zstep Rfd.                        (* 14dd8 li a1,-1 *)
    tstep1 Rfd.                       (* 14ddc srli s2,a1,32 *)
    zbr Rfd true.                     (* 14de0 beqz zero *)
    zstep Rfd.                        (* 14e00 mv a0,s4 *)
    zbr Rfd true.                     (* 14e04 bltu s4,s2 *)
    zstep Rfd.                        (* 14e0c sw a0,32(sp) *)
    zstep Rfd.                        (* 14e10 sub s4,s4,a0 *)
    zstep Rfd.                        (* 14e14 lw a0,8(sp) *)
    zbr Rfd false.                    (* 14e18 bnez a0 *)
    zstep Rfd.                        (* 14e1c mv a0,s3 *)
    zbr Rfd true.                     (* 14e20 bltu s3,s2 *)
    zstep Rfd.                        (* 14e28 sw a0,8(sp) *)
    zstep Rfd.                        (* 14e2c sub s3,s3,a0 *)
    (* at L_CALL2: the K facts *)
    split64 (p + 8) (p + 12) C8 C12. split64 (p + 24) (p + 28) C24 C28. split64 (p + 72) (p + 76) C72 C76.
    split64 (p + 7160) (p + 7164) C7160 C7164.
    lazymatch goal with |- realizes _ (zcfg _ _ ?R' ?Mx _) _ =>
      eapply (K R' Mx 0 0 0 0 0 0 0 0 0) end;
      first [ zreg | assumption | exact HAG | lia
            | lazymatch goal with |- mem_u32 _ _ _ _ => idtac | |- mem_u64 _ _ _ _ => idtac end;
              match goal with H : mem_u32 R_segs ?My ?a ?v |- mem_u32 R_segs ?My ?a ?v' =>
                                first [exact H | replace v' with v by reflexivity; exact H
                                       | (eapply (mem_u32_relit _ _ _ _ H); reflexivity)]
                            | H : mem_u64 R_segs ?My ?a ?v |- mem_u64 R_segs ?My ?a ?v' =>
                                first [exact H | replace v' with v by reflexivity; exact H] end
            | match goal with |- ?G => idtac "KSIDE" G end ].
Qed.
End FXG.
End S_U2A.


