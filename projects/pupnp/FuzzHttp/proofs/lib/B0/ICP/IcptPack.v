(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts Globals IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit I_asan_memset I_memset_i I_asan_memcpy I_memcpy_i I_strlen I_memchr I_read I_fwrite I_strncmp I_asan_memmove I_printf_front
  I_strncasecmp M_sspdefs I_strtol I_strtoll I_atoi M_stpncpy I_strncpy I_inet_pton I_asan_dtor I_memcmp I_strchr M_twoway_A I_strstr.
Import ListNotations.
Open Scope Z_scope.

Section P.
Context {HC : HasCeiling}.

#[using="Type"] Lemma env_safe_stack : forall lo q, alloc_ceiling <= lo -> env_safe [(lo, q)].
Proof. intros lo q H. pose proof alloc_ceiling_bounds. constructor; [left; cbn; lia| constructor]. Qed.
#[using="Type"] Lemma env_safe_cons_stack : forall A B lo q, env_safe [(A, B)] -> alloc_ceiling <= lo -> env_safe [(A, B); (lo, q)].
Proof. intros A B lo q H1 H2. inversion H1; subst. constructor; [assumption|]. apply env_safe_stack; assumption. Qed.
#[using="Type"] Lemma env_safe_stack_cons : forall A B lo q, env_safe [(A, B)] -> alloc_ceiling <= lo -> env_safe [(lo, q); (A, B)].
Proof. intros A B lo q H1 H2. pose proof alloc_ceiling_bounds. constructor; [left; cbn; lia| assumption]. Qed.

Ltac exs Q := repeat (let x := fresh "x" in destruct Q as [x Q]; exists x).

#[using="Type"] Lemma ic_strlen_proof : strlen_stmt_A.
Proof.
  intros until lo. intros STR NONUL PAD ACC RDB (WIN & W2 & NS) AE ST CLO LO Q64 SEP MI ->.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply strlen_i_spec; try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold istrlen_post in Q. unfold strlen_post_A. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_memchr_proof : memchr_stmt_A.
Proof.
  intros until lo. intros BUF OK ACC RDB (WIN & W2 & NS) AE ST CLO LO Q64 SEP MI -> -> -> RC RN.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply memchr_i_spec; try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold imemchr_post in Q. unfold memchr_post_A. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_memset_proof : asan_memset_stmt2 A0_asan_memset.
Proof.
  intros until junk. intros DST ACC RDB (WIN & W2 & NS) AE ST CLO LO Q64 SEP SAFE MI -> -> -> Hn Hc.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply asan_memset_spec; try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold amemset_post in Q. unfold asan_memset_post2. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_cons_stack; assumption].
Qed.

#[using="Type"] Lemma ic_memset_i_proof : asan_memset_stmt2 A0_memset_i.
Proof.
  intros until junk. intros DST ACC RDB (WIN & W2 & NS) AE ST CLO LO Q64 SEP SAFE MI -> -> -> Hn Hc.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply memset_i_spec; try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold imemset_post in Q. unfold asan_memset_post2. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_cons_stack; assumption].
Qed.

#[using="Type"] Lemma ic_memcpy_proof : asan_memcpy_stmt A0_asan_memcpy.
Proof.
  intros until junk. intros DST SRC LEN SEP ACD RDD ACS RDS (WD & WD2 & ND) (WS & WS2 & NS) AE ST CLO LO Q64 SEPD SAFE SEPS MI -> -> -> Hn.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply asan_memcpy_spec; try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold amemcpy_post in Q. unfold asan_memcpy_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_cons_stack; assumption].
Qed.

#[using="Type"] Lemma ic_memcpy_i_proof : asan_memcpy_stmt A0_memcpy_i.
Proof.
  intros until junk. intros DST SRC LEN SEP ACD RDD ACS RDS (WD & WD2 & ND) (WS & WS2 & NS) AE ST CLO LO Q64 SEPD SAFE SEPS MI -> -> -> Hn.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply memcpy_i_spec; try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold imemcpy_post in Q. unfold asan_memcpy_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_cons_stack; assumption].
Qed.

#[using="Type"] Lemma ic_read_front_proof : read_front_stmt.
Proof.
  intros until lo. intros AE ST CLO LO Q64 MI -> -> ->.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE.
  eapply evt_mono.
  { eapply read_front_spec; try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold read_front_post0 in Q. unfold read_front_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_read_back_proof : read_back_stmt.
Proof.
  intros until junk. intros FRM AE ST CLO LO Q64 CHK RR RC SEP HB MI.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply read_back_spec; try eassumption; try lia.
    intros POS. destruct (CHK POS) as (_ & AC & RD & (W & W2 & NS)). repeat (split; [assumption|]). assumption. }
  intros ms' Q. unfold icpt_back_post0 in Q. unfold icpt_back_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST'). repeat (split; [assumption|]).
  eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_fwrite_front_proof : fwrite_front_stmt.
Proof.
  intros until lo. intros AE ST CLO LO Q64 MI -> -> -> ->.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE.
  eapply evt_mono.
  { eapply fwrite_front_spec; try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold fwrite_front_post0 in Q. unfold fwrite_front_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_fwrite_back_proof : fwrite_back_stmt.
Proof.
  intros until junk. intros FRM AE ST CLO LO Q64 HR HS HN CHK SEP HP MI.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply fwrite_back_spec; try eassumption; try lia.
    intros POS. destruct (CHK POS) as (AC & RD & (W & W2 & NS)). repeat (split; [assumption|]). assumption. }
  intros ms' Q. unfold icpt_back_post0 in Q. unfold icpt_back_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST'). repeat (split; [assumption|]).
  eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.
#[using="Type"] Lemma ic_strncmp_proof : strncmp_stmt_A A0_strncmp false.
Proof.
  intros until lo. intros LS RS MOD ACA RDA ACB RDB (WA & WA2 & NA) (WB & WB2 & NB) AE ST CLO LO Q64 SEPA SEPB MI -> -> -> RN.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply strncmp_i_spec with (A := A) (B := B) (ls := ls) (rs := rs) (n := n); try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold istrncmp_post in Q. unfold strncmp_post_A. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_memmove_proof : asan_memmove_stmt.
Proof.
  intros until us. intros ARR HS HD ACD RDD ACS RDS (WD & WD2 & ND) (WS & WS2 & NS) AE ST CLO LO Q64 ULO UHI MI -> -> -> Hn.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply asan_memmove_spec with (U := U) (us := us) (D := D) (S := S) (n := n); try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold amemmove_post in Q. unfold asan_memmove_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM|].
  constructor; [left; cbn; lia|]. apply env_safe_stack; exact CLO.
Qed.

#[using="Type"] Lemma ic_vprintf_front_proof : vprintf_front_stmt.
Proof.
  intros until argw. intros AE ST CLO LO Q64 MI E0 E1 VA SEPV AP0 APM ACCF RDF.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply vprintf_front_spec; try eassumption; lia. }
  intros ms' Q. unfold vprintf_front_post0 in Q. unfold vprintf_front_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_vfprintf_front_proof : vfprintf_front_stmt.
Proof.
  intros until argw. intros AE ST CLO LO Q64 MI E0 E1 E2 STRM VA SEPV AP0 APM ACCF RDF.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply vfprintf_front_spec; try eassumption; lia. }
  intros ms' Q. unfold vfprintf_front_post0 in Q. unfold vfprintf_front_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_fprintf_s_front_proof : forall fmt flen, fprintf_s_front_stmt fmt flen.
Proof.
  intros fmt flen. intros until sbuf. intros HF AE ST CLO LO Q64 MI E0 E1 E2 STRM ACCF RDF SSTR NOTIN SPOS SEPS ACCS RDS (WINS & W2 & NS).
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply fprintf_s_front_spec with (S := S) (sbuf := sbuf); try eassumption; lia. }
  intros ms' Q. unfold fprintf_front_post0 in Q. unfold fprintf_front_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_fprintf_u_front_proof : fprintf_u_front_stmt.
Proof.
  intros until lo. intros AE ST CLO LO Q64 MI E0 E1 STRM ACCF RDF.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply fprintf_u_front_spec; try eassumption; lia. }
  intros ms' Q. unfold fprintf_front_post0 in Q. unfold fprintf_front_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma ic_strncasecmp_proof : strncmp_stmt_A A0_strncasecmp true.
Proof.
  intros until lo. intros LS RS MOD ACA RDA ACB RDB (WA & WA2 & NA) (WB & WB2 & NB) AE ST CLO LO Q64 SEPA SEPB MI -> -> -> RN.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply strncasecmp_i_spec with (A := A) (B := B) (ls := ls) (rs := rs) (n := n); try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold istrncasecmp_post in Q. unfold strncmp_post_A. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO].
Qed.

#[using="Type"] Lemma env_safe_errno : forall lo q, alloc_ceiling <= lo -> env_safe [(lo, q); (6190512 - 164, 6190512 - 164 + 4)].
Proof. intros lo q H. pose proof alloc_ceiling_bounds. constructor; [left; cbn; lia|]. constructor; [| constructor]. cbn. lia. Qed.
#[using="Type"] Lemma env_safe_errno_E : forall lo q E, alloc_ceiling <= lo -> 0x609000 <= E -> env_safe [(lo, q); (E, E + 8); (6190512 - 164, 6190512 - 164 + 4)].
Proof. intros lo q E H HE. pose proof alloc_ceiling_bounds. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [| constructor]. cbn. lia. Qed.

#[using="Type"] Lemma ic_strtol_proof : strtol_stmt_A.
Proof.
  intros until q. intros STR EC ERR GOT CAN AE ACS RDS WS NS ACE RDE WE HB ST CLO LO Q63 TP1 TP2 TPV S1 S2 E1 E2 EAL SEPE MI -> -> ->.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_STRTOL_DEPTH in LO.
  eapply evt_mono.
  { eapply strtol_i_spec with (S := S) (str := str) (E := E) (ejunk := ejunk) (errv := errv) (canary := canary) (lo := lo);
      try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold istrtol_post in Q. unfold strtol_post_A. exs Q.
  destruct Q as (EQ & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM|]. rewrite TPV. apply env_safe_errno_E; assumption.
Qed.

#[using="Type"] Lemma ic_strtoll_proof : strtoll_stmt_A.
Proof.
  intros until q. intros STR EC ERR GOT CAN AE ACS RDS WS NS ACE RDE WE ST CLO LO Q63 TP1 TP2 TPV S1 S2 E1 E2 EAL SEPE MI -> -> ->.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_STRTOL_DEPTH in LO.
  eapply evt_mono.
  { eapply strtoll_i_spec with (S := S) (str := str) (E := E) (base := 10) (ejunk := ejunk) (errv := errv) (canary := canary) (lo := lo);
      try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold istrtol_post in Q. unfold strtol_post_A. exs Q.
  destruct Q as (EQ & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM|]. rewrite TPV. apply env_safe_errno_E; assumption.
Qed.

#[using="Type"] Lemma ic_strtol0_proof : strtol0_stmt_A.
Proof.
  intros until q. intros STR ERR GOT CAN AE ACS RDS WS NS ST CLO LO Q63 TP1 TP2 TPV S1 S2 MI -> -> ->.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_STRTOL_DEPTH in LO.
  eapply evt_mono.
  { eapply strtol0_i_spec with (S := S) (str := str) (base := 10) (errv := errv) (canary := canary) (lo := lo);
      try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold istrtol0_post in Q. unfold strtol0_post_A. exs Q.
  destruct Q as (EQ & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM|]. rewrite TPV. apply env_safe_errno; assumption.
Qed.

#[using="Type"] Lemma ic_atoi_proof : atoi_stmt_A.
Proof.
  intros until q. intros STR NONUL ERR GOT CAN AE ACS RDS WS NS ST CLO LO Q63 TP1 TP2 TPV S1 S2 MI ->.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  eapply evt_mono.
  { eapply atoi_i_spec with (S := S) (str := str) (errv := errv) (canary := canary) (lo := lo); try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold istrtol0_post in Q. unfold strtol0_post_A. exs Q.
  destruct Q as (EQ & MU & WM & MI' & ST' & R). repeat (split; [assumption|]).
  split; [| exact R]. eapply asan_env_frame; [exact AE| exact MU| exact WM|]. rewrite TPV. apply env_safe_errno; assumption.
Qed.

#[using="Type"] Lemma ic_strncpy_proof : strncpy_stmt_A.
Proof.
  intros until lo. intros DST RN SRC NONUL PAD ACS RDS WS ACD RDD WD AE ST CLO LO Q64 D1 D2 S1 S2 SEP MI -> -> ->.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  assert (DL : length djunk = Z.to_nat n) by (destruct DST as [[W _] _]; cbn in W; tauto).
  pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as DARR.
  eapply evt_mono.
  { eapply strncpy_i_spec with (D := D) (S := S) (n := n) (str := str) (slack := slack) (dbs := djunk) (lo := lo);
      try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold istrncpy_post in Q. unfold strncpy_post_A. exs Q.
  destruct Q as (EQ & MU & WM & MI' & ST' & DA & SA). repeat (split; [assumption|]).
  split. { eapply asan_env_frame; [exact AE| exact MU| exact WM|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
  split; [| exact SA].
  pose proof (rw_cells_of_u8arr _ _ _ _ DA) as DC. rewrite stpn_result_length in DC. exact DC.
Qed.

#[using="Type"] Lemma ic_inet_pton_proof : inet_pton_stmt_A.
Proof.
  intros until lo. intros SRC NONUL DST AF GOT GUARD ACS RDS WS NSS ACD RDD WD AE ST CLO LO Q64 Q47 ACK RDK S1 S2 D1 D2 SEP MI -> -> ->.
  pose proof alloc_ceiling_bounds as ACB0. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_RT_STACK in LO.
  unfold A0_got_ssp, A0_ssp_guard in *.
  eapply evt_mono.
  { eapply inet_pton_i_spec with (af := af) (S := S) (A := A) (str := str) (ojunk := ojunk) (N := N) (canary := canary) (lo := lo);
      try eassumption; try reflexivity; lia. }
  intros ms' Q. unfold iinet_post in Q. unfold inet_pton_post_A. exs Q.
  destruct Q as (EQ & MU & WM & MI' & ST' & (ACK' & RDK') & R). repeat (split; [assumption|]).
  split. { eapply asan_env_frame; [exact AE| exact MU| exact WM|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
  split; [exact ACK'|]. split; [exact RDK'|]. exact R.
Qed.

Definition ivl_eqb (a b : ivl) : bool := (fst a =? fst b) && (snd a =? snd b).
#[using="Type"] Lemma outside_in : forall W x a b, outside W x -> In (a, b) W -> ~ (a <= x < b).
Proof.
  induction W as [|[c d] W IH]; intros x a b OUT HIn; [destruct HIn|]. cbn [outside] in OUT. destruct OUT as [O1 O2].
  destruct HIn as [E|HIn]; [inversion E; subst; exact O1| eapply IH; eassumption].
Qed.
#[using="Type"] Lemma sub_fp_incl_b : forall W W' : list ivl, forallb (fun iv => existsb (ivl_eqb iv) W') W = true -> sub_fp W W'.
Proof.
  intros W W' H x OUT. induction W as [|[a b] W IH]; cbn [outside]; [exact I|].
  cbn [forallb] in H. apply andb_true_iff in H. destruct H as [H1 H2]. split; [| apply IH; exact H2].
  apply existsb_exists in H1. destruct H1 as ([a' b'] & HIn & HE). unfold ivl_eqb in HE; cbn [fst snd] in HE.
  apply andb_true_iff in HE. destruct HE as [E1 E2]. apply Z.eqb_eq in E1, E2. subst. eapply outside_in; eassumption.
Qed.
#[using="Type"] Lemma dtor_fp_sub : forall lo q, sub_fp (dtor_Wx lo q) ((lo, q) :: dtor_W).
Proof.
  intros lo q x OUT. unfold dtor_Wx. cbn [outside] in OUT |- *. destruct OUT as [O1 O2]. split; [exact O1|].
  clear O1. revert x O2. change (sub_fp ((724608, 724616) :: (728560, 728568) :: (2147540804, 2147541452) :: WL0) dtor_W).
  apply sub_fp_incl_b. vm_compute. reflexivity.
Qed.
#[using="Type"] Lemma odr_cells_split : forall (m : mem) b0 b1 b2, rw_cells asegs m 6188000 [C1 b0; C1 b1; C1 b2] ->
  forall o, 0x5e6be0 <= o < 0x5e6be3 -> exists c, rw_cells asegs m o [C1 c].
Proof.
  intros m b0 b1 b2 ODR o Ho.
  apply (proj1 (HttpTac.rw_cells_app asegs _ 6188000 [C1 b0] [C1 b1; C1 b2])) in ODR. destruct ODR as [O0 O12].
  cbn [cells_size csize Nat.add] in O12. change (6188000 + Z.of_nat 1) with 6188001 in O12.
  apply (proj1 (HttpTac.rw_cells_app asegs _ 6188001 [C1 b1] [C1 b2])) in O12. destruct O12 as [O1 O2].
  cbn [cells_size csize Nat.add] in O2. change (6188001 + Z.of_nat 1) with 6188002 in O2.
  assert (o = 6188000 \/ o = 6188001 \/ o = 6188002) as [->|[->| ->]] by lia; eexists; eassumption.
Qed.

#[using="Type"] Lemma ic_asan_dtor_proof : asan_dtor_stmt.
Proof.
  intros until lo. intros AE ST CLO LO Q64 MI GSH [bs SHD].
  pose proof alloc_ceiling_bounds as ACB. unfold alloc_floor, alloc_ceiling_max in ACB. unfold A0_RT_STACK in LO.
  pose proof AE as (AG & ((fw & FLAG) & (b0 & b1 & b2 & ODR) & D1 & D3 & D4 & D5 & MTX & DC) & IEz).
  pose proof (icpt_env_of_zaw _ IEz) as IE. pose proof (ie_got_rms _ IE) as D2. unfold env_got_rms in D2.
  assert (LE : LENV m) by (split; [exact IE| unfold dtor_xenv; repeat (split; [assumption|]); assumption]).
  assert (GF : gfacts m 0 0x5e6be0 A0_DESCS).
  { apply gfacts_intro; [exact A0_DESCS_ok| rewrite A0_DESCS_globals; exact GSH| eapply odr_cells_split; exact ODR]. }
  eapply evt_mono.
  { eapply asan_dtor_spec with (lo := lo) (fw := fw) (b0 := b0) (b1 := b1) (b2 := b2) (junkD := bs);
      [ exact MI | exact ST | lia | lia | lia | exact LE | exact MTX | exact DC | exact GF | exact SHD | exact ODR | exact FLAG ]. }
  intros ms' Q. unfold dtor_post_x in Q. unfold asan_dtor_post. exs Q.
  destruct Q as (E & MU & WM & MI' & ST' & MTX' & ODR' & FLAG').
  split; [exact E|]. split; [eapply munch_weaken; [apply dtor_fp_sub| exact MU]|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  assert (XB : xband_safe (dtor_Wx lo q)) by (apply dtor_Wx_xband; lia).
  pose proof (LENV_frame_x _ _ _ LE MU WM XB) as [IE' (E1 & E2 & E3 & E4 & E5)].
  destruct AG as (G1 & G2 & G3 & G4). unfold A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL in *.
  split; [| split].
  - unfold asan_globals, A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL.
    split; [ecfx G1 MU WM XB|]. split; [ecfx G2 MU WM XB|]. split; [ecfx G3 MU WM XB| ecfx G4 MU WM XB].
  - split; [exact FLAG'|]. split; [exact ODR'|]. split; [exact E1|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|]. split; [exact MTX'|].
    eapply rw_cells_transport; [exact DC| exact MU| exact WM|]. apply xband_disjoint; [exact XB| lia| | |];
      rewrite cells_size_desc; change (length A0_DESCS) with 81%nat; lia.
  - exact IE'.
Qed.

#[using="Type"] Lemma ic_strstr_chunked_proof : strstr_chunked_stmt_A.
Proof.
  intros until lo. intros HAY NONUL PAD GOT GUARD ACC RDB WIN NS ACCN RDN AE ST CLO LO Q64 HLO HHI MI -> ->.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_STRSTR_DEPTH in LO.
  destruct (ie_real_cmp _ IE) as (RSC & RMC).
  eapply evt_mono.
  { eapply strstr_i_spec with (H := H) (hay := hay) (slack := slack) (canary := canary) (lo := lo);
      first [ eassumption | reflexivity | exact RMC | exact RSC | lia ]. }
  intros ms' Q. unfold istrstr_post in Q. unfold strstr_chunked_post_A.
  destruct Q as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & E & MU & WM & MI' & ST' & HAY' & GOT' & GUARD' & R).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', r.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [eapply asan_env_frame; [exact AE| exact MU| exact WM| apply env_safe_stack; exact CLO]|].
  split; [exact HAY'|]. split; [exact GOT'|]. split; [exact GUARD'|]. lia.
Qed.

End P.
