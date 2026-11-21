(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* THE BRIDGE TEXT of the walk text I9S/S_ZA.v IN THE FORM FOR THE HAND TEXT's OLD PATH (a per-image text: one
   an image, the same module, section and item names on every image). It is scaffolding until the texts above
   name the list-form items. It holds no run and no step. Each hand module's name holds the run-form text's
   module of the same name; then the hand sentences that other texts name and that the run-form text holds in
   the list form stand word for word, each proved from the list-form item; the items that the hand text holds
   outside a module are brought in by a re-export. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase S_Entry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout S_ZARun.
Export OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.

Module S_Ret.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_Ret.
End S_Ret.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZAw. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.

Module S_LeaveA.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_LeaveA.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop S_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry S_Uw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Section Leave.
Context {RCa1 : RunCtx}.
Variables (cx : ictx) (fin : Z -> Z) (MD : Model) (T : TSet) (M0 : mem).
Hypothesis CX : ctx_ok ROMHI_S cx.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < c_n cx -> 0 <= fin i < 256.
Hypothesis OBLOW : c_ob cx + c_osz cx <= c_u cx - FRA.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.

Hypothesis HKRL : KRL cx fin MD T M0.
Hypothesis HKRX : KRX cx fin MD T M0.
Hypothesis HKW : KW cx fin MD T M0.

Lemma leave_uwret_s : forall Rb l M st rv uwret lf cf,
  sinv cx st lf cf ->
  zget_l Rb l kSP = c_u cx + -224 -> zget_l Rb l kGP = c_K cx kGP -> zget_l Rb l kTP = c_K cx kTP ->
  zget_l Rb l kA0 = uwret -> (uwret = 0 \/ uwret = 1) -> zget_l Rb l kS1 = rv ->
  zget_l Rb l kS5 = c_n cx - c_cin0 cx -> zget_l Rb l kS2 = c_n cx - t_cin st ->
  zget_l Rb l kS9 = t_out st -> zget_l Rb l kS3 = c_osz cx - t_cout st -> zget_l Rb l kS0 = c_p cx ->
  s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf ->
  mpostL (run_segments R_segs rc_inp rc_sp rc_mb) M0 M (fp_call cx) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_UW_RET (zupd Rb l) M MD) T.
Proof.
  intros Rb l M st rv uwret lf cf SI Lsp Lgp Ltp La0 Huw Ls0 Ls4 Ls1 Ls8 Ls2 Ls9 STD SAT STRM Hlens Hcodes HP0.
  eapply (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_Leave.leave_uwret_l cx fin MD T M0); try eassumption.
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_LeaveA.split_za_lists; eassumption.
Qed.
End Leave.
End S_LeaveA.

Module S_Leave.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_Leave.
End S_Leave.

Module S_Inflate.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_Inflate.
End S_Inflate.

Module S_U2B.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2B.
End S_U2B.

Module S_U2C.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2C.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop S_Ret OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry S_Uw S_LeaveA S_Leave S_Inflate S_U2B.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Section U2.
Context {RCa1 : RunCtx}.
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet) (Mza : mem).
Variable zc : Z.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < n -> 0 <= fin i < 256.
Hypothesis Hu0 : zc + FRA <= u. Hypothesis Hzimg : DATA_LO + DATA_LEN <= zc. Hypothesis Hu1 : u + 208 <= 140737488355328. Hypothesis Hua : u mod 16 = 0.
Hypothesis Hp0 : 0 < p. Hypothesis Hp1 : p + STATE_SIZE <= zc. Hypothesis Hpa : p mod 16 = 0.
Hypothesis Hq1 : 1 <= q. Hypothesis Hn0 : 0 <= n. Hypothesis Hn1 : n < 67108864. Hypothesis Hqn : q + n <= zc.
Hypothesis Spq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p).
Hypothesis Spob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p).
Hypothesis Sobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF).
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p).
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.
Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.

Let cxc := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2C.cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc.
Let wok := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2C.wok p q n zc.
Let fp_u2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2C.fp_u2 u p.

Variable wph : Z.
Hypothesis Hwph : wok wph.

Let KZE2 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2C.KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T Mza wph.
Let KZE1 := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2C.KZE1 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T Mza wph.
Let PCALL := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2C.PCALL u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T Mza zc wph.

Definition KZW : Prop := forall (R : tree Z) (M : mem) (cin0 cout0 W0 ra : Z) (st : ist) (rv : Z) (lf cf : Z -> Z),
  let cx := cxc 0 cin0 cout0 W0 ra in
  (ra = RA_C1 \/ ra = RA_C2) -> 0 <= cin0 <= n -> 0 <= cout0 <= 262144 ->
  sinv cx st lf cf -> cout0 < t_cout st -> t_mode st <= DONE ->
  zget R kA3 = A_ZCALLOC -> zget R kA0 = 0 -> zget R kA1 = WIN_SIZE -> zget R kA2 = 1 ->
  zget R kS0 = BUF + t_cout st -> zget R kS1 = t_out st - (262144 - t_cout st) -> zget R kS2 = 1 -> zget R kS3 = p ->
  zget R kS4 = t_out st - (262144 - t_cout st) ->
  zget R kSP = u + -272 -> zget R kGP = gp -> zget R kTP = tp ->
  zget R kS5 = n - cin0 -> zget R kS6 = 262144 - t_cout st -> zget R kS7 = t_hold st -> zget R kS8 = t_bits st ->
  zget R kS9 = t_out st -> zget R kS11 = q + t_cin st ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -232) L_UW_RET -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -240) p ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -248) rv -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -256) (n - t_cin st) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -264) (262144 - t_cout st) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -272) (t_out st - (262144 - t_cout st)) ->
  s_std cx fin M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M ->
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 168) N_LENS lf -> mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (p + 1384) N_CODES cf ->
  wph = 0 -> mpostL (run_segments R_segs rc_inp rc_sp rc_mb) Mza M (fp_u2 0) ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) T_ZW (zupd R []) M MD) T.
Hypothesis HZE2 : KZE2.
Hypothesis HZE1 : KZE1.
Hypothesis HZW : KZW.

Lemma KZW_twin : KZW <-> OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2C.KZW_l u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T Mza zc wph.
Proof.
  split.
  - intros K R0 M cin0 cout0 W0 ra st rv lf cf cx0. subst cx0. intros.
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_LeaveA.open_za_lists. zgetl_nil.
    eapply (K R0 M cin0 cout0 W0 ra st rv lf cf); eassumption.
  - intros K R0 M cin0 cout0 W0 ra st rv lf cf cx0. subst cx0. intros.
    eapply (K R0 M cin0 cout0 W0 ra st rv lf cf);
      OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_LeaveA.split_za_lists; cbv beta iota delta [zget_l alookup]; eassumption.
Qed.

Theorem pcall_all : forall B, PCALL B.
Proof.
  exact (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_U2C.pcall_all_l u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T Mza zc Hh Hfin Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn
           Spq Spob Sobq Sprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 MEMCPY ADLER
           A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
           A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH wph Hwph HZE2 HZE1 (proj1 KZW_twin HZW)).
Qed.

End U2.
End S_U2C.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_Entry. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop. Import S_Ret. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import S_Entry. Import S_Uw. Import S_LeaveA. Import S_Leave. Import S_Inflate. Import S_U2A. Import S_U2B. Import S_U2C.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Section ZA.
Context {RCa1 : RunCtx}.
Variables (u p q n gp tp s5 s6 s7 s8 s9 s10 s11 : Z) (fin : Z -> Z) (MD : Model) (T : TSet).
Variable zc : Z.
Hypothesis Hh : m_halted MD = None.
Hypothesis Hfin : forall i, 0 <= i < n -> 0 <= fin i < 256.
Hypothesis Hu0 : zc + FRA <= u. Hypothesis Hzimg : DATA_LO + DATA_LEN <= zc. Hypothesis Hu1 : u + 208 <= 140737488355328. Hypothesis Hua : u mod 16 = 0.
Hypothesis Hp0 : 0 < p. Hypothesis Hp1 : p + STATE_SIZE <= zc. Hypothesis Hpa : p mod 16 = 0.
Hypothesis Hq1 : 1 <= q. Hypothesis Hn0 : 0 <= n. Hypothesis Hn1 : n < 67108864. Hypothesis Hqn : q + n <= zc.
Hypothesis Spq : ZSEP (p + STATE_SIZE <= q \/ q + n <= p).
Hypothesis Spob : ZSEP (p + STATE_SIZE <= BUF \/ BUF + 262144 <= p).
Hypothesis Sobq : ZSEP (BUF + 262144 <= q \/ q + n <= BUF).
Hypothesis Sprom : ZSEP (p + STATE_SIZE <= ROM_LO_ALL \/ ROMHI_S <= p).
Hypothesis Rgp : 0 <= gp < two64. Hypothesis Rtp : 0 <= tp < two64.
Hypothesis Rs5 : 0 <= s5 < two64. Hypothesis Rs6 : 0 <= s6 < two64. Hypothesis Rs7 : 0 <= s7 < two64. Hypothesis Rs8 : 0 <= s8 < two64.
Hypothesis Rs9 : 0 <= s9 < two64. Hypothesis Rs10 : 0 <= s10 < two64. Hypothesis Rs11 : 0 <= s11 < two64.
Hypothesis MEMCPY : memcpy_spec_s.
Hypothesis ADLER : adler32_spec_s.
Hypothesis A_HEAD : arm_stmt L_HEAD HEAD.
Hypothesis A_DICTID : arm_stmt L_DICTID DICTID.
Hypothesis A_DICT : arm_stmt L_DICT DICT.
Hypothesis A_TYPE : arm_stmt L_TYPE TYPE.
Hypothesis A_TYPEDO : arm_stmt L_TYPEDO TYPEDO.
Hypothesis A_STORED : arm_stmt L_STORED STORED.
Hypothesis A_COPY_ : arm_stmt L_COPY_ COPY_.
Hypothesis A_COPY : arm_stmt L_COPY COPY.
Hypothesis A_TABLE : arm_stmt L_TABLE TABLE.
Hypothesis A_LENLENS : arm_stmt L_LENLENS LENLENS.
Hypothesis A_CODELENS : arm_stmt L_CODELENS CODELENS.
Hypothesis A_LEN_ : arm_stmt L_LEN_ LEN_.
Hypothesis A_LEN : arm_stmt L_LEN LEN.
Hypothesis A_LENEXT : arm_stmt L_LENEXT LENEXT.
Hypothesis A_DIST : arm_stmt L_DIST DIST.
Hypothesis A_DISTEXT : arm_stmt L_DISTEXT DISTEXT.
Hypothesis A_MATCH : arm_stmt L_MATCH MATCH.
Hypothesis A_LIT : arm_stmt L_LIT LIT.
Hypothesis A_CHECK : arm_stmt_ob L_CHECK CHECK.
Hypothesis A_LENGTH : arm_stmt L_LENGTH LENGTH.

Theorem za_cps : forall Rb l M,
  zget_l Rb l kSP = u + -32 -> zget_l Rb l kS1 = u -> zget_l Rb l kA0 = p ->
  zget_l Rb l kS3 = n -> zget_l Rb l kS4 = 262144 -> zget_l Rb l kS5 = s5 ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  zget_l Rb l kS6 = s6 -> zget_l Rb l kS7 = s7 -> zget_l Rb l kS8 = s8 -> zget_l Rb l kS9 = s9 ->
  zget_l Rb l kS10 = s10 -> zget_l Rb l kS11 = s11 ->
  rom_ok M -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -32) BUF -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -24) (u + 160) -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -16) (u + 168) ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -8) RA_II ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u) q -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 8) 0 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 64) A_ZCALLOC -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 72) A_ZCFREE -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (u + 80) 0 ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M 0 ->
  KZW u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc 0 ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZA (zupd Rb l) M MD) T.
Proof.
  intros Rb l M Lsp Ls1 La0 Ls3 Ls4 Ls5 Lgp Ltp Ls6 Ls7 Ls8 Ls9 Ls10 Ls11
         ROM Wstk Wp Hin Fm32 Fm24 Fm16 Fm8 S8 S16 S72 S80 S88 HZE2 HZW.
  eapply (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.za_cps_l u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T zc Hh Hfin Hu0 Hzimg Hu1 Hua Hp0 Hp1 Hpa Hq1 Hn0 Hn1 Hqn
            Spq Spob Sobq Sprom Rgp Rtp Rs5 Rs6 Rs7 Rs8 Rs9 Rs10 Rs11 MEMCPY ADLER
            A_HEAD A_DICTID A_DICT A_TYPE A_TYPEDO A_STORED A_COPY_ A_COPY A_TABLE A_LENLENS A_CODELENS
            A_LEN_ A_LEN A_LENEXT A_DIST A_DISTEXT A_MATCH A_LIT A_CHECK A_LENGTH Rb l M); try eassumption;
    first [ apply (proj1 (S_U2C.KZW_twin u p q n gp tp s5 s6 s7 s8 s9 s10 s11 fin MD T M zc 0)); exact HZW
          | OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZARun.S_LeaveA.split_za_lists; eassumption ].
Qed.
End ZA.
