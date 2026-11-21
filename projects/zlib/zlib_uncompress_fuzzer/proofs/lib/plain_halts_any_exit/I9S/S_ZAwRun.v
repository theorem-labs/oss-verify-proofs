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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZGo11 SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.

Module S_Uw.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the text's own labels are fields of the layout text; here they have their short names only *)
Local Notation L_UW_BODY := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_BODY (only parsing).
Local Notation L_UW_EPI := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_EPI (only parsing).
Local Notation L_UW_TAIL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_TAIL (only parsing).
Local Notation L_UW_FULL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_FULL (only parsing).
Local Notation L_UW_PART := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_PART (only parsing).
Local Notation L_ZAW_PART_J := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZAW_PART_J (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation rkeeps := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps (only parsing).
Local Notation fholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (only parsing).
Local Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).
Local Notation FR_UWL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW (only parsing).

(* OPENERS OF THE LIST FORM (they only unfold, split and name): every list-form hypothesis: the meaning over the
   layout's lists is unfolded, the conjunction split and its parts named; the same for a goal *)
Ltac open_lists :=
  repeat match goal with
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             progress cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_epi OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_ret
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_tail OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_tail_k
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_fp OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_part_j
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_entry
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_kw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_resume] in H; destr_conj H
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps _ _ _ _ |- _ =>
             progress cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw_tail] in H; destr_conj H
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds _ _ _ _ _ |- _ =>
             progress cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw] in H; destr_conj H
         end.
Ltac split_lists :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rkeeps OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_epi OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_ret
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_tail OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_tail_k
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_fp OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_part_j
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_body OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_entry
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_kw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_resume
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw_tail OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw];
  split_conj.

Section Uw.
Context {RCa1 : RunCtx}.
Hypothesis MEMCPY : memcpy_spec_s.

(* the closers of the list form: a premise that is a list's meaning is split and closed part by part; a keep
   list's goal is closed from the opened keep facts *)
Local Ltac lclose := first [ solve [split_lists; first [zreg | assumption]] | assumption
                           | (cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp]; klia) ].
Local Ltac kkeep := open_lists; zgetl_nil; zkeys; zimps; split_lists; zkeys; zkept.

Lemma uw_epi_s : forall Rb l M MD T (spc ret rv v0 v1 v2 v3 v4 : Z),
  m_halted MD = None ->
  rholds (qargs [spc; rv]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_epi ->
  0 <= spc - FR_UWL -> spc <= 140737488355328 ->
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [ret; v0; v1; v2; v3; v4]) M spc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw ->
  Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  (forall R',
     rholds (qargs [spc; rv; v0; v1; v2; v3; v4]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_ret ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_EPI (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T spc ret rv v0 v1 v2 v3 v4 Hh RHb Hc1 Hc2 FRb Hret Hrr K.
  open_lists. zkeys. unfold L_UW_EPI in *. cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW] in *. pose proof two64_eq as TW64.
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => apply (K RR) end); split_lists; zreg.
Qed.


Lemma uw_tail_s : forall Rb l M MD T (p spc whave wnext dist zc : Z),
  m_halted MD = None ->
  rholds (qargs [p; dist; spc]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_tail ->
  0 < p -> p + STATE_SIZE <= zc -> zc <= spc - FR_UWL -> spc <= 140737488355328 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) whave -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) wnext ->
  0 <= whave -> whave <= WIN_SIZE -> 0 <= wnext -> wnext < WIN_SIZE -> (whave < WIN_SIZE -> wnext = whave) ->
  0 <= dist -> wnext + dist <= WIN_SIZE ->
  (forall R' M' whave' wnext',
     rholds (qargs [p; dist; spc]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_tail_k ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw_tail ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(p + 76, 8)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_EPI (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_TAIL (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p spc whave wnext dist zc Hh RHb Hp0 Hp1 Hc1 Hc2 Wp H60 H64 H68
         Wh0 Wh1 Wn0 Wn1 Whn Hd0 Hd1 K.
  open_lists. zkeys. unfold L_UW_TAIL, L_UW_EPI in *. cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW] in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(p + 76, 8)] ltac:(ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(p + 76, 8)]) M) by (apply mpostL_refl).
  zto_branch_h Rfd (first [ zhint xor_seqz_sel ]).
  destruct (Z_lt_dec whave 32768) as [Hlt|Hge].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ =>
      apply (K RR Mx (whave + dist) (if wnext + dist =? 32768 then 0 else wnext + dist)) end);
      first [ solve [split_lists; zreg] | assumption | (destruct (Z.eqb_spec (wnext + dist) 32768); lia) ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ =>
      apply (K RR Mx whave (if wnext + dist =? 32768 then 0 else wnext + dist)) end);
      first [ solve [split_lists; zreg] | assumption | (destruct (Z.eqb_spec (wnext + dist) 32768); lia) ].
Qed.

Definition uw_body_fp (p wa : Z) : list (Z * Z) := [(p + 72, 12); (wa, WIN_SIZE)].

Lemma uw_full_s : forall Rb l M MD T (p ob osz wa cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z) (M0 : mem),
  m_halted MD = None ->
  rholds (qargs [wa; ob + cout; copy; p; spc]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_fp ->
  zc <= spc - FR_UWL -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc - FR_UWL \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 < wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  WIN_SIZE <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wa WIN_SIZE ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) WIN_SIZE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) wa ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [ret; v0; v1; v2; v3; v4]) M spc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw ->
  Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X (uw_body_fp p wa)) M ->
  (forall R' M' whave' wnext',
     rholds (qargs [spc; 0; v0; v1; v2; v3; v4]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_ret ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wa ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X (uw_body_fp p wa)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_FULL (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wa cout copy spc ret v0 v1 v2 v3 v4 zc fo M0
         Hh RHb Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wp Wwa H60 H72 HOB Hfo FRb Hret Hrr HAG K.
  open_lists. zkeys. unfold L_UW_FULL in *. cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW] in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M0 (uw_body_fp p wa) ltac:(unfold uw_body_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  unfold uw_body_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 _ ob osz fo (cout - 32768) 32768 HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
  apply mem_arr8_mem_is in Hsrc.
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RR ?lc) ?Mx _) _ =>
    eapply (MEMCPY RR lc Mx MD T wa (ob + 1 * (cout - 32768)) _ 32768 _ Hh) end).
  - zreg. - zreg. - zreg. - zreg. - reflexivity.
  - exact Hsrc.
  - rewrite length_map, zseq_length. lia.
  - exact Wwa.
  - lia. - lia. - lia. - lia. - zlia.
  - intros M' R' HP HD HS HW E11 E3 E4 E5 E9 E10 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
    zimps.
    clear HD HS Hsrc HOB. apply mpost_mpostL1 in HP. zreattachL HP.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd _ ?lc) ?Mx _) _ =>
      eapply (uw_epi_s R' lc Mx MD T spc ret 0 v0 v1 v2 v3 v4 Hh) end); try lclose.
    intros R9 RH9 RK9.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K R9 Mx 32768 0) end;
      first [ exact RH9 | assumption | lia | kkeep ].
Qed.

Lemma uw_part_s : forall Rb l M MD T (p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z) (M0 : mem),
  m_halted MD = None ->
  rholds (qargs [wa; ob + cout; copy; p; spc]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_fp ->
  zc <= spc - FR_UWL -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc - FR_UWL \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 < wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  0 <= copy -> copy < WIN_SIZE -> copy <= cout -> cout <= osz ->
  0 <= whave -> whave <= WIN_SIZE -> 0 <= wnext -> wnext < WIN_SIZE -> (whave < WIN_SIZE -> wnext = whave) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wa WIN_SIZE ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) whave -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) wnext ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) wa ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [ret; v0; v1; v2; v3; v4]) M spc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw ->
  Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X (uw_body_fp p wa)) M ->
  (forall R' M' whave' wnext',
     rholds (qargs [spc; 0; v0; v1; v2; v3; v4]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_ret ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wa ->
     framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 X (uw_body_fp p wa)) M' ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_PART (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo M0
         Hh RHb Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcp2 Hcout Wh0 Wh1 Wn0 Wn1 Whn Wp Wwa H60 H64 H68 H72 HOB Hfo FRb Hret Hrr HAG K.
  open_lists. zkeys. unfold L_UW_PART in *. cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW] in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M0 (uw_body_fp p wa) ltac:(unfold uw_body_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  unfold uw_body_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  zto_branch Rfd.
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mc _) _ =>
  assert (J : forall RJ dist, dist = Z.min (32768 - wnext) copy ->
    rholds (qargs [wa; wnext; ob + cout; copy; p; spc; 32768 - wnext; dist]) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_part_j ->
    rkeeps RJ Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZAW_PART_J (zupd RJ []) Mc MD) T) end.
  { intros RJ dist Hdist RHJ RKJ.
    open_lists. zgetl_nil. zkeys. unfold L_ZAW_PART_J.
    pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 _ ob osz fo (cout - copy) dist HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
    apply mem_arr8_mem_is in Hsrc.
    zuntil_h Rfd (first [ zhint zext32_shift ])
      (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RR ?lc) ?Mx _) _ =>
         eapply (MEMCPY RR lc Mx MD T (wa + wnext) (ob + 1 * (cout - copy)) _ dist _ Hh) end).
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
      + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ =>
          eapply (uw_tail_s RR [] Mx MD T p spc whave wnext dist zc Hh) end); try lclose.
        intros R2' M2 whave' wnext' RH2 RK2 W1 W2 W3 W4 W5 C60 C64 C68 HP2.
        open_lists. zgetl_nil. zkeys. zimps. clear H60 H64 H68. zreattachL HP2.
        lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ =>
          eapply (uw_epi_s RR [] Mx MD T spc ret 0 v0 v1 v2 v3 v4 Hh) end; try lclose.
        intros R9 RH9 RK9.
        apply (K R9 M2 whave' wnext'); first [ exact RH9 | assumption | lia | kkeep ].
      +
        pose proof (mem_arr_sub (run_segments R_segs rc_inp rc_sp rc_mb) 1 _ ob osz fo (cout - (copy - dist)) (copy - dist) HOB ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc2.
        apply mem_arr8_mem_is in Hsrc2.
        zuntil_h Rfd (first [ zhint zext32_shift ])
          (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RR ?lc) ?Mx _) _ =>
             eapply (MEMCPY RR lc Mx MD T wa (ob + 1 * (cout - (copy - dist))) _ (copy - dist) _ Hh) end).
        * zreg. * zreg. * zreg. * zreg. * reflexivity.
        * exact Hsrc2.
        * rewrite length_map, zseq_length. lia.
        * eapply mem_wr_sub; [exact Wwa | lia | lia].
        * lia. * lia. * lia. * lia. * zlia.
        * intros M2 R2' HP2 HD2 HS2 HW2 N11 N3 N4 N5 N9 N10 N19 N20 N21 N22 N23 N24 N25 N26 N27 N28.
          zimps. clear HD2 HS2 Hsrc2 HOB. apply mpost_mpostL1 in HP2. zreattachL HP2.
          zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ =>
            eapply (uw_epi_s RR [] Mx MD T spc ret 0 v0 v1 v2 v3 v4 Hh) end); try lclose.
          intros R9 RH9 RK9.
          lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K R9 Mx 32768 (copy - dist)) end;
            first [ exact RH9 | assumption | lia | kkeep ]. }
  destruct (Z_lt_dec (32768 - wnext) copy) as [Lt|Ge].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => apply (J RR (32768 - wnext)) end);
      first [ solve [split_lists; zreg] | lia ].
  - zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR _ _) _ => apply (J RR copy) end);
      first [ solve [split_lists; zreg] | lia ].
Qed.

Lemma uw_body_s : forall Rb l M MD T (p ob osz wa ws whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z),
  m_halted MD = None ->
  rholds (qargs [wa; ob + cout; copy; p; spc]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_body ->
  zc <= spc - FR_UWL -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc - FR_UWL \/ spc <= ob) ->
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
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [ret; v0; v1; v2; v3; v4]) M spc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw ->
  Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  (forall R' M' whave' wnext',
     rholds (qargs [spc; 0; v0; v1; v2; v3; v4]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_ret ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wa ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (uw_body_fp p wa) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_BODY (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wa ws whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo
         Hh RHb Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Hws Wh0 Wn0 Wfacts
         Wp Wwa H56 H60 H64 H68 H72 HOB Hfo FRb Hret Hrr K.
  open_lists. zkeys. unfold L_UW_BODY in *. cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW] in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (uw_body_fp p wa) ltac:(unfold uw_body_fp; cbv [WIN_SIZE]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (uw_body_fp p wa)) M) by (apply mpostL_refl).
  unfold uw_body_fp in HST, HAG; cbv [WIN_SIZE] in HST, HAG.
  assert (FULL : forall RJ Mq (whave1 wnext1 : Z), 32768 <= copy ->
    rholds (qargs [wa; ob + cout; copy; p; spc]) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_fp ->
    rkeeps RJ Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq p 7176 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq wa 32768 ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 72) 32768 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 88) wa ->
    mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) Mq ob osz fo ->
    fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [ret; v0; v1; v2; v3; v4]) Mq spc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(p + 72, 12); (wa, 32768)]) Mq ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_FULL (zupd RJ []) Mq MD) T).
  { intros RJ Mq whave1 wnext1 Hc RHJ RKJ Wp' Wwa' C60 C72 HOB' FRJ HAG'.
    eapply (uw_full_s RJ [] Mq MD T p ob osz wa cout copy spc ret v0 v1 v2 v3 v4 zc fo M Hh); try lclose.
    intros R9 M9 whave' wnext' RH9 RK9. intros.
    apply (K R9 M9 whave' wnext'); first [ exact RH9 | assumption | kkeep ]. }
  assert (PART : forall RJ Mq (whave1 wnext1 : Z), copy < 32768 ->
    0 <= whave1 -> whave1 <= 32768 -> 0 <= wnext1 -> wnext1 < 32768 -> (whave1 < 32768 -> wnext1 = whave1) ->
    rholds (qargs [wa; ob + cout; copy; p; spc]) RJ [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_fp ->
    rkeeps RJ Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
    mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq p 7176 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) Mq wa 32768 ->
    mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 72) 32768 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 76) whave1 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 80) wnext1 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mq (p + 88) wa ->
    mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) Mq ob osz fo ->
    fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [ret; v0; v1; v2; v3; v4]) Mq spc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw ->
    framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(p + 72, 12); (wa, 32768)]) Mq ->
    realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_PART (zupd RJ []) Mq MD) T).
  { intros RJ Mq whave1 wnext1 Hc W1 W2 W3 W4 W5 RHJ RKJ Wp' Wwa' C60 C64 C68 C72 HOB' FRJ HAG'.
    eapply (uw_part_s RJ [] Mq MD T p ob osz wa whave1 wnext1 cout copy spc ret v0 v1 v2 v3 v4 zc fo M Hh); try lclose.
    intros R9 M9 whave' wnext' RH9 RK9. intros.
    apply (K R9 M9 whave' wnext'); first [ exact RH9 | assumption | kkeep ]. }
  unfold L_UW_FULL, L_UW_PART in FULL, PART.
  zto_branch Rfd.
  destruct Hws as [Hws0 | Hws1]; subst ws.
  - zto_branch Rfd.
    match goal with H1 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (p + 76) 0, H2 : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?Mx (p + 80) 0 |- _ =>
      rename H1 into Hwh; rename H2 into Hwn end.
    destruct (Z_lt_dec copy 32768) as [Lt|Ge].
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ => apply (PART RR Mx 0 0) end); try lclose.
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ => apply (FULL RR Mx 0 0) end); try lclose.
  - zto_branch Rfd.
    specialize (Wfacts eq_refl). dand Wfacts as (W2 & W4 & W5).
    destruct (Z_lt_dec copy 32768) as [Lt|Ge].
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ => apply (PART RR Mx whave wnext) end); try lclose.
    + zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ => apply (FULL RR Mx whave wnext) end); try lclose.
Qed.

Definition uw_fp_l (p wa spc : Z) : list (Z * Z) := [(spc + - FR_UWL, FR_UWL); (p + 72, 12); (wa, WIN_SIZE)].

Lemma uw_entry_l : forall Rb l M MD T (u p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z),
  m_halted MD = None ->
  rholds (qargs [u; ob + cout; copy; spc; ret; v0; v1; v2; v3; v4]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_entry ->
  Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  zc + FRA <= u -> u + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_TOP <= 140737488355328 -> zc <= spc + - FR_UWL -> spc <= u ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + - FR_UWL \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 <= wa -> wa + WIN_SIZE <= zc -> wa mod 16 = 0 ->
  ZSEP (wa = 0 \/ p + STATE_SIZE <= wa \/ wa + WIN_SIZE <= p) -> ZSEP (wa = 0 \/ wa + WIN_SIZE <= ob \/ ob + osz <= wa) ->
  0 <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  0 <= whave -> 0 <= wnext ->
  (wa <> 0 -> whave <= WIN_SIZE /\ wnext < WIN_SIZE /\ (whave < WIN_SIZE -> wnext = whave)) ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + - FR_UWL) FR_UWL -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> (wa <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wa WIN_SIZE) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 56) p -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 68) 15 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) (if wa =? 0 then 0 else WIN_SIZE) ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 76) whave -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 80) wnext -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) wa ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  (forall R' M', wa = 0 ->
     rholds (qargs [A_ZCALLOC; ob + cout; copy; p; v4; spc]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_kw ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
     fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [ret; v0; v1; v2; v3; v4]) M' spc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(spc + - FR_UWL, FR_UWL)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd R' []) M' MD) T) ->
  (forall R' M' whave' wnext', wa <> 0 ->
     rholds (qargs [spc; 0; v0; v1; v2; v3; v4]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_ret ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wa ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (uw_fp_l p wa spc) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p ob osz wa whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo
         Hh RHb Hret Hrr
         Hu0 Hu1 Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hwa0 Hwa1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wh0 Wn0 Wfacts Wfr Wp Wwa H64u H72u H88u H56 H60 H64 H68 H72 HOB Hfo KW K.
  open_lists. zkeys. unfold L_UW, T_ZW in *. cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_TOP Z.opp] in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (uw_fp_l p wa spc) ltac:(unfold uw_fp_l; cbv [WIN_SIZE OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (uw_fp_l p wa spc)) M) by (apply mpostL_refl).
  unfold uw_fp_l in HST, HAG; cbv [WIN_SIZE OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp] in HST, HAG.
  destruct (Z.eq_dec wa 0) as [Wz | Wnz].
  -
    clear Wwa Wfacts. subst wa.
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(spc + - FR_UWL, FR_UWL)] ltac:(cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp]; ranges_ok_tac)) as HST';
    assert (HAG' : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(spc + - FR_UWL, FR_UWL)]) M) by (apply mpostL_refl).
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp] in HST', HAG'.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ => apply (KW RR Mx eq_refl) end);
      first [ solve [split_lists; first [zreg | assumption]] | assumption | exact HAG' ].
  -
    specialize (Wwa Wnz). specialize (Wfacts Wnz).
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ =>
      eapply (uw_body_s RR [] Mx MD T p ob osz wa (if wa =? 0 then 0 else 32768) whave wnext cout copy spc ret v0 v1 v2 v3 v4 zc fo Hh) end);
      try lclose.
    + slia.
    + slia.
    + destruct (Z.eqb_spec wa 0); [lia_std | right; reflexivity].
    + intros R9 M9 whave' wnext' RH9 RK9. intros.
      match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ M9 _ |- _ => unfold uw_body_fp in HP; cbv [WIN_SIZE] in HP; zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K R9 Mx whave' wnext' Wnz) end;
        first [ exact RH9 | assumption | kkeep ].
Qed.

Definition uw_res_fp_l (p wres spc : Z) : list (Z * Z) := [(spc + - FR_UWL, FR_UWL); (p + 72, 24); (wres, WIN_SIZE)].

Lemma uw_resume_l : forall Rb l M MD T (p ob osz wres cout copy spc ret v0 v1 v2 v3 v4 zc : Z) (fo : Z -> Z),
  m_halted MD = None ->
  rholds (qargs [wres; ob + cout; copy; p; spc]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_resume ->
  zc <= spc + - FR_UWL -> spc <= 140737488355328 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  0 < ob -> 1 <= osz -> ob + osz <= 140737488355328 -> ZSEP (ob + osz <= spc + - FR_UWL \/ spc <= ob) ->
  ZSEP (p + STATE_SIZE <= ob \/ ob + osz <= p) ->
  0 <= wres -> wres + WIN_SIZE <= zc -> wres mod 16 = 0 ->
  ZSEP (wres = 0 \/ p + STATE_SIZE <= wres \/ wres + WIN_SIZE <= p) -> ZSEP (wres = 0 \/ wres + WIN_SIZE <= ob \/ ob + osz <= wres) ->
  0 <= copy -> copy <= cout -> cout <= osz -> copy < 4294967296 ->
  mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (spc + - FR_UWL) FR_UWL -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE -> (wres <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M wres WIN_SIZE) ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 68) 15 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 72) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 88) 0 ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M ob osz fo -> (forall i, 0 <= i < osz -> 0 <= fo i < 256) ->
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [ret; v0; v1; v2; v3; v4]) M spc OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_uw ->
  Z.land ret (-2) = ret -> 0 <= ret < two64 ->
  (forall R' M', wres = 0 ->
     rholds (qargs [spc; 1; v0; v1; v2; v3; v4]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_ret ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) 0 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) 0 ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(spc + - FR_UWL, FR_UWL); (p + 72, 24)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  (forall R' M' whave' wnext', wres <> 0 ->
     rholds (qargs [spc; 0; v0; v1; v2; v3; v4]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_ret ->
     rkeeps R' Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.keep_zaw ->
     0 <= whave' -> whave' <= WIN_SIZE -> 0 <= wnext' -> wnext' < WIN_SIZE -> (whave' < WIN_SIZE -> wnext' = whave') ->
     mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 72) WIN_SIZE -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 76) whave' -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 80) wnext' ->
     mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' (p + 88) wres ->
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' (uw_res_fp_l p wres spc) ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) ret (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZB (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T p ob osz wres cout copy spc ret v0 v1 v2 v3 v4 zc fo
         Hh RHb Hc1 Hc2 Hp0 Hp1 Hpal Hob0 Hosz Hob1 Sobs Spob Hw0 Hw1 Hwal Spw Swob
         Hcp0 Hcp1 Hcout Hcp2 Wfr Wp Ww H56 H60 H72 HOB Hfo FRb Hret Hrr K0 K1.
  zkeys. unfold L_ZB in *. cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp] in *. pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M (uw_res_fp_l p wres spc) ltac:(unfold uw_res_fp_l; cbv [WIN_SIZE OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X (uw_res_fp_l p wres spc)) M) by (apply mpostL_refl).
  unfold uw_res_fp_l in HST, HAG; cbv [WIN_SIZE OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp] in HST, HAG.
  destruct (Z.eq_dec wres 0) as [Wz | Wnz].
  - clear Ww. subst wres. open_lists. zkeys.
    pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(spc + - FR_UWL, FR_UWL); (p + 72, 24)] ltac:(cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp]; ranges_ok_tac)) as HST';
    assert (HAG' : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(spc + - FR_UWL, FR_UWL); (p + 72, 24)]) M) by (apply mpostL_refl).
    cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_UW Z.opp] in HST', HAG'.
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ =>
      eapply (uw_epi_s RR [] Mx MD T spc ret 1 v0 v1 v2 v3 v4 Hh) end); try lclose.
    intros R9 RH9 RK9.
    lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K0 R9 Mx eq_refl) end;
      first [ exact RH9 | assumption | exact HAG' | kkeep ].
  - specialize (Ww Wnz). open_lists. zkeys.
    destruct (mem_wr_u32_exists_R M (p + 76) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (wh0 & Hwh0 & Rwh0).
    destruct (mem_wr_u32_exists_R M (p + 80) ltac:(eapply mem_wr_sub; [exact Wp | lia | lia])) as (wn0 & Hwn0 & Rwn0).
    zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ =>
      eapply (uw_body_s RR [] Mx MD T p ob osz wres 0 wh0 wn0 cout copy spc ret v0 v1 v2 v3 v4 zc fo Hh) end);
      try lclose.
    + slia.
    + slia.
    + intros R9 M9 whave' wnext' RH9 RK9. intros.
      match goal with HP : mpostL (run_segments R_segs rc_inp rc_sp rc_mb) _ M9 _ |- _ => unfold uw_body_fp in HP; cbv [WIN_SIZE] in HP; zreattachL HP end.
      lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ => apply (K1 R9 Mx whave' wnext' Wnz) end;
        first [ exact RH9 | assumption | kkeep ].
Qed.
End Uw.
End S_Uw.

Module S_U2A.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZGo11.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

(* the text's own labels are fields of the layout text; here they have their short names only *)
Local Notation L_ZA := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_ZA (only parsing).
Local Notation L_CALL2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_CALL2 (only parsing).
Local Notation RA_II := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.RA_II (only parsing).
(* the meaning words of the list form, by their short names *)
Local Notation rholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds (only parsing).
Local Notation fholds := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds (only parsing).
Local Notation qargs := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs (only parsing).

(* OPENERS OF THE LIST FORM (they only unfold, split and name) *)
Ltac open_lists :=
  repeat match goal with
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds _ _ _ _ |- _ =>
             progress cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_za OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_za_k] in H; destr_conj H
         | H : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds _ _ _ _ _ |- _ =>
             progress cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
                  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_ii] in H; destr_conj H
         end.
Ltac split_lists :=
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qargs nth fst snd
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_za OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_za_k OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_ii];
  split_conj.

Lemma mem_u32_relit {RCa1 : RunCtx}  : forall M a e e', mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e -> e mod 4294967296 = e' mod 4294967296 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a e'.
Proof.
  intros M a e e' H E. unfold mem_u32 in *.
  rewrite <- (Z_to_le_bytes_mod32 4 e) in H by lia. rewrite E, Z_to_le_bytes_mod32 in H by lia. exact H.
Qed.

Lemma mz_u32 {RCa1 : RunCtx}  : forall M a len off, mem_zero (run_segments R_segs rc_inp rc_sp rc_mb) M a len -> 0 <= off -> off + 4 <= len -> 0 <= a + off ->
  a + off + 4 <= two64 -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + off) 0.
Proof.
  intros M a len off Hz H1 H2 H3 H4. unfold mem_u32, mem_is. change (length (Z_to_le_bytes 4 0)) with 4%nat.
  rewrite (mem_zero_sub (run_segments R_segs rc_inp rc_sp rc_mb) M a len off 4 Hz) by lia. reflexivity.
Qed.
Lemma mz_u64 {RCa1 : RunCtx}  : forall M a len off, mem_zero (run_segments R_segs rc_inp rc_sp rc_mb) M a len -> 0 <= off -> off + 8 <= len -> 0 <= a + off ->
  a + off + 8 <= two64 -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (a + off) 0.
Proof.
  intros M a len off Hz H1 H2 H3 H4. unfold mem_u64, mem_is. change (length (Z_to_le_bytes 8 0)) with 8%nat.
  rewrite (mem_zero_sub (run_segments R_segs rc_inp rc_sp rc_mb) M a len off 8 Hz) by lia. reflexivity.
Qed.

Ltac split64 a ahi nlo nhi :=
  lazymatch goal with |- realizes _ (zcfg _ _ _ ?Mx _) _ =>
    match goal with H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) Mx a _ |- _ =>
      pose proof (mem_u64_lo32 _ _ _ _ H) as nlo; pose proof (mem_u64_hi32 _ _ _ _ H) as nhi; cbn in nhi;
      replace (a + 4) with ahi in nhi by lia
    end
  end.

Lemma za_prefix_l {RCa1 : RunCtx}  : forall Rb l M MD T (u p q n zc : Z) (gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z),
  m_halted MD = None ->
  rholds (qargs [u; p; n; gp; tp; s5; s6; s7; s8; s9; s10; s11]) Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_za ->
  zc + FRA <= u -> DATA_LO + DATA_LEN <= zc -> u + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_TOP <= 140737488355328 -> u mod 16 = 0 ->
  0 < p -> p + STATE_SIZE <= zc -> p mod 16 = 0 ->
  1 <= q -> 0 <= n -> n < 67108864 -> q + n <= zc ->
  ZSEP (p + STATE_SIZE <= q \/ q + n <= p) -> ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p) ->
  rom_ok M -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_LO) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_LEN -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  fholds (run_segments R_segs rc_inp rc_sp rc_mb) (qargs [u; BUF; RA_II]) M u OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zaw_ii ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M u q -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 8) 0 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  (forall R' M' (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z),
     rholds (qargs [u; p; n; gp; tp; s5; s6; s7; s8; s9; s10; s11]) R' [] OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zaw_za_k ->
     rom_ok M' -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' (u + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_LO) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_LEN -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M' p STATE_SIZE -> mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M' q n fin ->
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
     mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M M' [(u + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LO, OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LEN); (u, 112); (p, STATE_SIZE)] ->
     realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_CALL2 (zupd R' []) M' MD) T) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M MD T u p q n zc gp tp s5 s6 s7 s8 s9 s10 s11 fin
         Hh RHb
         Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn Spq Sprom
         ROM Wstk Wp Hin FRb S8 S16 S72 S80 S88 K.
  open_lists.
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_LO OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_LEN OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_STACK_TOP
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LO OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LEN] in *.
  zkeysb. unfold L_ZA, L_CALL2, RA_II in *. cbv [STATE_SIZE FRA ROM_LO_ALL A_ZCALLOC A_ZCFREE BUF HEAD DATA_LO DATA_LEN] in *.
  pose proof two64_eq as TW64.
  pose proof (mpostL_stable (run_segments R_segs rc_inp rc_sp rc_mb) M [(u + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LO, OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LEN); (u, 112); (p, 7176)] ltac:(cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LO OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LEN]; ranges_ok_tac)) as HST.
  assert (HAG : framed (fun X => mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M X [(u + OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LO, OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LEN); (u, 112); (p, 7176)]) M) by (apply mpostL_refl).
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LO OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.FR_ZAW_BELOW_LEN] in HST, HAG.
  zuntil Rfd (idtac; lazymatch goal with |- realizes _ (zcfg _ _ (zupd ?RR ?lc) ?Mx _) _ =>
    eapply (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SMemsetOk.memset7168_ok RR lc Mx MD T (p + 8) _ Hh) end).
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
    zuntil Rfd (idtac; split64 (p + 16) (p + 20) W16 W20; split64 (p + 64) (p + 68) W64 W68).
    zuntil Rfd (idtac; split64 (p + 8) (p + 12) C8 C12; split64 (p + 24) (p + 28) C24 C28; split64 (p + 72) (p + 76) C72 C76;
                split64 (p + 7160) (p + 7164) C7160 C7164;
                lazymatch goal with |- realizes _ (zcfg _ _ ?RR ?Mx _) _ => eapply (K RR Mx 0 0 0 0 0 0 0 0 0) end);
      first [ solve [split_lists; zreg] | zreg | assumption | exact HAG | lia
            | lazymatch goal with |- mem_u32 _ _ _ _ => idtac | |- mem_u64 _ _ _ _ => idtac end;
              match goal with H : mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' =>
                                first [exact H | replace v' with v by reflexivity; exact H
                                       | (eapply (mem_u32_relit _ _ _ _ H); reflexivity)]
                            | H : mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v |- mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) ?My ?a ?v' =>
                                first [exact H | replace v' with v by reflexivity; exact H] end ].
Qed.
End S_U2A.
