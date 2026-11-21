(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from P/SO_diag.v: the stderr diagnostic over rzt (rzt_stderr_pieces, rzt_stderr_fprintf, so_fprintf_diag_proof, so_diag_str_of, so_diag_usage_proof) restated over BudgetWit.Rzb.rzb, with their released proofs. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: chan_ok also gives the channel reader, so its two halves go to rzt_stdio_writev_b, as P/SO_diag.v does there. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac PropExec MState Mem Exec ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad FmtFp Stdio Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_fmt_fp_lib F_pad Exit Printf_model F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_vsnprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_vsnprintf.F_vfprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_vsnprintf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import PImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_piface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_rz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_diag.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_diag.SO_fwritex_stderr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_diag.SO_stdio_flush.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_diag.SO_fwrite.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SO_fprintf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_fprintf.SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SO_diag.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.BudgetWit Require Import Rzb P_SO_rzB P_SO_fprintfB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation rztb := (rzt_b psegs).

Lemma rzt_stderr_pieces_b : forall {St} (ps : list (list Z)) (buf : list Z) (st : St) mo,
  chan_ok mo 2 -> Forall (fun p => zlength p <= 2^25) ps -> zlength buf <= INTERNAL_BUFSIZ ->
  exists e buf', buf ++ concat ps = e ++ buf' /\ zlength buf' <= INTERNAL_BUFSIZ /\
    rztb (stderr_pieces buf ps st) mo (map (WriteEv (Z_to_bv 64 2)) (to_bytes e)) (fun r => r = (buf', st)).
Proof.
  intros St ps. induction ps as [|p ps IH]; intros buf st mo CH SM HB.
  - exists [], buf. cbn [concat]. rewrite app_nil_r. split; [reflexivity|]. split; [exact HB|].
    cbn [stderr_pieces to_bytes map]. apply rzt_mret_b. reflexivity.
  - apply Forall_cons_iff in SM. destruct SM as [SP SM]. cbn [stderr_pieces concat].
    destruct (Z.ltb_spec (INTERNAL_BUFSIZ - zlength buf) (zlength p)) as [LT|GE].
    + destruct (IH [] st mo CH SM ltac:(unfold INTERNAL_BUFSIZ, zlength; cbn; lia)) as (e2 & buf2 & E2 & HB2 & RZ2).
      exists ((buf ++ p) ++ e2), buf2. split; [cbn [app] in E2; rewrite E2, !app_assoc; reflexivity|]. split; [exact HB2|].
      rewrite to_bytes_app, map_app.
      eapply rzt_mbind_b.
      * apply (rzt_stdio_writev_b psegs st mo 2 buf p (proj1 CH) (proj2 CH)). unfold INTERNAL_BUFSIZ in *. lia.
      * intros [] s' Hs. cbn [snd] in Hs. subst s'. exact RZ2.
    + destruct (IH (buf ++ p) st mo CH SM ltac:(rewrite zlength_app'; lia)) as (e2 & buf2 & E2 & HB2 & RZ2).
      exists e2, buf2. split; [rewrite <- E2, app_assoc; reflexivity|]. split; [exact HB2| exact RZ2].
Qed.

Lemma rzt_stderr_fprintf_b : forall {St} (ps : list (list Z)) (st : St) mo,
  chan_ok mo 2 -> Forall (fun p => zlength p <= 2^25) ps ->
  rztb (stderr_fprintf ps st) mo (map (WriteEv (Z_to_bv 64 2)) (to_bytes (concat ps))) (fun r => snd r = st).
Proof.
  intros St ps st mo CH SM.
  destruct (rzt_stderr_pieces_b ps [] st mo CH SM ltac:(unfold INTERNAL_BUFSIZ, zlength; cbn; lia)) as (e & buf' & E & HB & RZ).
  cbn [app] in E. rewrite E, to_bytes_app, map_app. unfold stderr_fprintf.
  eapply rzt_mbind_b; [exact RZ|]. intros b s' Hs. injection Hs as -> ->.
  replace (to_bytes buf') with (to_bytes (buf' ++ [])) by (rewrite app_nil_r; reflexivity).
  apply (rzt_stdio_writev_b psegs st mo 2 buf' [] (proj1 CH) (proj2 CH)).
  unfold INTERNAL_BUFSIZ, zlength in *. cbn [length]. lia.
Qed.

Theorem so_fprintf_diag_proof_b : so_fprintf_diag_stmt_b.
Proof.
  unfold so_fprintf_diag_stmt_b. intros until K. intros HM CH SEF Ha0 DA SM ST LO GLO QHI SSP MI FRM HK HC.
  pose proof (@fprintf_diag_proof unit d ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m tt lo canary fwritex_stderr_proof stdio_write_flush_proof SEF Ha0 DA ST LO GLO QHI SSP MI FRM) as H.
  unfold implM in H.
  assert (RZ : rztb (s_diag (St:=unit) d tt) mo (W 2 (fdiag_bytes d)) (fun r => snd r = tt)).
  { pose proof (rzt_stderr_fprintf_b (fdiag_pieces d) tt mo CH (fdiag_pieces_small d SM)) as R.
    destruct d; cbn [diag_args] in DA; try contradiction; exact R. }
  apply (RZ _ _ K HM H HK). intros [[] []] ms' PO _. cbn [fst snd] in PO. unfold fprintf_diag_post in PO.
  destruct PO as (x5 & x6 & x7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FOK & ST' & SF' & SSP' & _).
  eapply HC; eassumption.
Qed.

Section StrDiag.
  Variable d_of : list Z -> diag_msg.
  Variable fmt : Z.
  Variable msg : list byte -> list byte.
  Hypothesis d_of_shape : forall s, d_of s = DUsage s \/ d_of s = DCannotOpen s \/ d_of s = DReadError s.
  Hypothesis fmt_eq : forall s, match d_of s with DUsage _ => A_FMT_usage | DCannotOpen _ => A_FMT_cannot_open | _ => A_FMT_read_error end = fmt.
  Hypothesis msg_eq : forall s : list byte, fdiag_bytes (d_of (map bv_unsigned s)) = msg s.

  Lemma so_diag_str_of_b : so_fprintf_diag_stmt_b -> so_diag_str_stmt_b fmt msg.
  Proof.
    intros FP. unfold so_diag_str_stmt_b. intros until K. intros HM CH SEF Ha0 Ha1 BY NI SLK LEN DJ GA ST LO GLO QHI SSP MI FRM HK HC.
    rewrite <- msg_eq. unfold so_fprintf_diag_stmt_b in FP.
    eapply FP; [exact HM | exact CH | exact SEF | exact Ha0 | | | exact ST | exact LO | exact GLO | exact QHI | exact SSP | exact MI | exact FRM | exact HK | exact HC].
    - pose proof (d_of_shape (map bv_unsigned s)) as SH. pose proof (fmt_eq (map bv_unsigned s)) as FE.
      assert (BODY : exists slack0 : list byte,
             bytes_at psegs m (bv_unsigned a2) (zb (map bv_unsigned s) ++ Z_to_bv 8 0 :: slack0)
             /\ Forall (fun c => 0 < c < 256) (map bv_unsigned s)
             /\ ((- (bv_unsigned a2 + zlength (map bv_unsigned s) + 1)) mod 8 <= zlength slack0)
             /\ (zlength (map bv_unsigned s) < INT_MAX - 256)
             /\ (bv_unsigned a2 + zlength (map bv_unsigned s) + 1 + zlength slack0 <= lo \/ bv_unsigned sp <= bv_unsigned a2)
             /\ (GLOBALS_TOP <= bv_unsigned a2)).
      { exists slack. rewrite zb_of_bytes, zlength_map'. split; [exact BY|]. split; [apply bytes_Forall_pos; exact NI|].
        split; [exact SLK|]. split; [unfold INT_MAX; lia|]. split; [exact DJ| exact GA]. }
      unfold diag_args. destruct SH as [E|[E|E]]; rewrite E in FE |- *; (split; [rewrite Ha1, <- FE; reflexivity| exact BODY]).
    - unfold diag_small. destruct (d_of_shape (map bv_unsigned s)) as [E|[E|E]]; rewrite E, zlength_map'; lia.
  Qed.
End StrDiag.

Theorem so_diag_usage_proof_b : so_diag_usage_stmt_b.
Proof. apply (so_diag_str_of_b DUsage); [intros; left; reflexivity | intros; reflexivity | apply msg_usage_eq | apply so_fprintf_diag_proof_b]. Qed.
