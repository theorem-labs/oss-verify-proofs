(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase S_Entry SMemsetOk.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout S_ZAwRun.
Export OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.

Module S_Uw.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_Uw.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.


Section Uw.
Context {RCa1 : RunCtx}.
Hypothesis MEMCPY : memcpy_spec_s.

Definition uw_fp (p wa spc : Z) : list (Z * Z) := [(spc + -48, 48); (p + 72, 12); (wa, WIN_SIZE)].

Lemma uw_fp_twin : forall p wa spc, uw_fp p wa spc = uw_fp_l p wa spc.
Proof. intros. reflexivity. Qed.
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
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -48) 48 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> (wa <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wa WIN_SIZE) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 68) 15 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) (if wa =? 0 then 0 else WIN_SIZE) ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) whave -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) wnext -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) wa ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  (forall R' M', wa = 0 ->
     zget R' kA3 = A_ZCALLOC -> zget R' kA0 = 0 -> zget R' kA1 = WIN_SIZE -> zget R' kA2 = 1 ->
     zget R' kS0 = ob + cout -> zget R' kS1 = copy -> zget R' kS2 = 1 -> zget R' kS3 = p -> zget R' kS4 = v4 ->
     zget R' kSP = spc + -48 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -8) ret -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -24) v1 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -32) v2 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (spc + -48) v4 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(spc + -48, 48)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd R' []) M' MD) T) ->
  (forall R' M' whave' wnext', wa <> 0 ->
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wa ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (uw_fp p wa spc) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo
         Hh La0 La1 La2 Lsp Lra Hret Hrr Ls0 Ls1 Ls2 Ls3 Ls4
         Hu0 Hu1 Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wh0 Wn0 Wfacts Wfr Wp Wwa H64u H72u H88u H56 H60 H64 H68 H72 HOB Hfo KW K.
  eapply (uw_entry_l MEMCPY Rb l M MD T u p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo Hh);
    [ (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_Uw.split_lists; assumption) | assumption .. | idtac | idtac ].
  - intros R9 M9 Wz RH9 RK9 FR9. intros. OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_Uw.open_lists. zgetl_nil. apply (KW R9 M9 Wz); assumption.
  - intros R9 M9 whave' wnext' Wnz RH9 RK9. intros. OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_Uw.open_lists. zgetl_nil. apply (K R9 M9 whave' wnext' Wnz); assumption.
Qed.

Definition uw_res_fp (p wres spc : Z) : list (Z * Z) := [(spc + -48, 48); (p + 72, 24); (wres, WIN_SIZE)].

Lemma uw_res_fp_twin : forall p wres spc, uw_res_fp p wres spc = uw_res_fp_l p wres spc.
Proof. intros. reflexivity. Qed.
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
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -48) 48 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> (wres <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wres WIN_SIZE) ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 68) 15 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) 0 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -8) ret -> Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -16) v0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -24) v1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -32) v2 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -40) v3 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + -48) v4 ->
  (forall R' M', wres = 0 ->
     zget R' kSP = spc -> zget R' kA0 = 1 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) 0 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(spc + -48, 48); (p + 72, 24)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  (forall R' M' whave' wnext', wres <> 0 ->
     zget R' kSP = spc -> zget R' kA0 = 0 ->
     zget R' kS0 = v0 -> zget R' kS1 = v1 -> zget R' kS2 = v2 -> zget R' kS3 = v3 -> zget R' kS4 = v4 ->
     zget R' kGP = zget_l Rb l kGP -> zget R' kTP = zget_l Rb l kTP ->
     zget R' kS5 = zget_l Rb l kS5 -> zget R' kS6 = zget_l Rb l kS6 -> zget R' kS7 = zget_l Rb l kS7 ->
     zget R' kS8 = zget_l Rb l kS8 -> zget R' kS9 = zget_l Rb l kS9 -> zget R' kS10 = zget_l Rb l kS10 ->
     zget R' kS11 = zget_l Rb l kS11 ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wres ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (uw_res_fp p wres spc) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZB (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wres cout copy spc ret v0 v1 v2 v3 v4 zc fo
         Hh La0 Ls0 Ls1 Ls2 Ls3 Lsp Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hw0 Hw1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wfr Wp Ww H56 H60 H72 HOB Hfo Hra Hret Hrr H0 H1 H2 H3 H4 K0 K1.
  eapply (uw_resume_l MEMCPY Rb l M MD T p ob osz wres cout copy spc ret v0 v1 v2 v3 v4 zc fo Hh);
    [ (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_Uw.split_lists; assumption) | assumption ..
    | (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_Uw.split_lists; assumption) | assumption | assumption | idtac | idtac ].
  - intros R9 M9 Wz RH9 RK9. intros. OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_Uw.open_lists. zgetl_nil. apply (K0 R9 M9 Wz); assumption.
  - intros R9 M9 whave' wnext' Wnz RH9 RK9. intros. OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_Uw.open_lists. zgetl_nil. apply (K1 R9 M9 whave' wnext' Wnz); assumption.
Qed.
End Uw.
End S_Uw.

Module S_U2A.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_U2A.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition L_ZA : Z := 86352.              (* 0x150f0: inflateInit_ after jalr zalloc *)
Definition L_CALL2 : Z := 85648.           (* 0x14e30: uncompress2_z, mv a0,sp before the first jal inflate *)
Definition RA_II : Z := 85536.             (* 0x14dc0: uncompress2_z after jal inflateInit_ *)
Lemma L_ZA_twin : L_ZA = OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZA.
Proof. reflexivity. Qed.
Lemma L_CALL2_twin : L_CALL2 = OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CALL2.
Proof. reflexivity. Qed.
Lemma RA_II_twin : RA_II = OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.RA_II.
Proof. reflexivity. Qed.

Ltac zgen :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => let x' := fresh "gv" in set (x' := e); clearbody x'
  end.

Theorem za_prefix_s {RCa1 : RunCtx}  : forall Rb l M MD T (u p q n zc : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z),
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
  rom_ok M -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -32) BUF -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -24) (u + 160) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -16) (u + 168) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -8) RA_II ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M u q -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 8) 0 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  (forall R' M' (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z),
     zget R' kSP = u ->
     zget R' kS0 = u + 168 -> zget R' kS1 = u + 160 -> zget R' kS2 = 4294967295 -> zget R' kS3 = 0 -> zget R' kS4 = 0 ->
     zget R' kS5 = s5 -> zget R' kGP = gp -> zget R' kTP = tp ->
     zget R' kS6 = s6 -> zget R' kS7 = s7 -> zget R' kS8 = s8 -> zget R' kS9 = s9 -> zget R' kS10 = s10 -> zget R' kS11 = s11 ->
     rom_ok M' -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p STATE_SIZE -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' u q -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 8) n -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 24) BUF -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 32) 262144 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + 80) 0 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' p u -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 8) HEAD -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 12) 0 ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 16) 5 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 28) (-1) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 56) 0 ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 68) 15 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) 0 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) 0 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) 0 ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 96) 0 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 104) 0 ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 108) vlen -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 112) vofs -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 116) vext ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 120) (p + 1384) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 128) (p + 1384) ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 136) vlb -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 140) vdb ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 144) vnc -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 148) vnl -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 152) vnd -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 156) vsh ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 160) (p + 1384) -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 7160) 1 ->
     0 <= vlen < 4294967296 -> 0 <= vofs < 4294967296 -> 0 <= vext < 4294967296 -> 0 <= vlb < 4294967296 -> 0 <= vdb < 4294967296 ->
     0 <= vnc < 4294967296 -> 0 <= vnl < 4294967296 -> 0 <= vnd < 4294967296 -> 0 <= vsh < 4294967296 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(u + -80, 48); (u, 112); (p, STATE_SIZE)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CALL2 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin
         Hh Lsp Ls1 La0 Ls3 Ls4 Lgp Ltp Ls5 Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Sprom
         ROM Wstk Wp Hin Fm32 Fm24 Fm16 Fm8 S8 S16 S72 S80 S88 K.
  eapply (za_prefix_l Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin Hh);
    [ (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_U2A.split_lists; assumption) | assumption ..
    | (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_U2A.split_lists; assumption) | assumption | assumption | assumption | assumption | assumption | idtac ].
  intros R9 M9 vlen vofs vext vlb vdb vnc vnl vnd vsh RH9. intros. OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAwRun.S_U2A.open_lists. zgetl_nil.
  eapply (K R9 M9 vlen vofs vext vlb vdb vnc vnl vnd vsh); assumption.
Qed.
End S_U2A.
