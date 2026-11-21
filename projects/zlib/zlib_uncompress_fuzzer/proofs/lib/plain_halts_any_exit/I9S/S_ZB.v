(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* THE BRIDGE TEXT OF THE WALK TEXT BELOW IT: the hand text's sentences that other texts name, word for word under
   their old names, each proved from its list-form item of the both-image text. It holds no run and no step.
   Scaffolding until the texts above name the list-form items. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SBase S_Entry S_ZA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require RefMemcpyLib FuzzMem S9MemcpyBase S9Memcpy S9AdlerBase S9AdlerIface S9Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require S9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_It3.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZBI. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZBI.




From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require ZStep.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZBF. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZBF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require SQuant SLayoutSigL.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require SLayout.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZBRun.
Export OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZBRun.







Module S_Tok.
Include OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZBRun.S_Tok.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.IConj.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel.InflateInv.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Frame OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.Hoare.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.FuzzMem OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9MemcpyBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9Memcpy OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9AdlerBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9AdlerIface OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9Adler.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.S9LibStmt.
Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SBase OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_LeaveA OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.S_U2A OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2B OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2C S_It7 S_Fast1 S_Fast7.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Definition tok_mem {RCa1 : RunCtx}  (cx : ictx) (st : ist) (rv : Z) (lf cf : Z -> Z) (M : mem) : Prop :=
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -232) L_UW_RET /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -240) (c_p cx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -248) rv /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -256) (c_n cx - t_cin st) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -264) (c_osz cx - t_cout st) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -272) (t_out st - (c_osz cx - t_cout st)) /\
  i_frame cx M /\ i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M /\ i_hooks cx M /\
  st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\ strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf.

(* the kept frame definition and its list-form item say the same *)
Lemma tok_mem_twin {RCa1 : RunCtx}  : forall cx st rv lf cf M,
  tok_mem_l cx st rv lf cf M <-> tok_mem cx st rv lf cf M.
Proof.
  intros cx st rv lf cf M. unfold tok_mem_l, tok_mem.
  cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fhold1 OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_off OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_width
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.fs_quant fst snd OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth
       OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.f_zb_tok OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.L_UW_RET L_UW_RET].
  split; intros HH; destr_conj HH; split_conj; assumption.
Qed.

Definition tok_regs (p q n cin0 s11v : Z) (st : ist) : list Z :=
  [BUF + t_cout st; t_out st - (262144 - t_cout st); 1; p; t_out st - (262144 - t_cout st); n - cin0;
   262144 - t_cout st; t_hold st; t_bits st; t_out st; s11v; q + t_cin st].

Definition zwtok_S9 {RCa1 : RunCtx}  : ZWINV := fun u p q n zc sE sW M =>
  exists (s5 s6 s7 s8 s9 s10 s11 cin0 cout0 W0 ra rv s11v : Z) (st : ist) (lf cf : Z -> Z),
    sE = [s5; s6; s7; s8; s9; s10; s11] /\ sW = tok_regs p q n cin0 s11v st /\
    tok_pure u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra s11v st lf cf /\
    tok_mem (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st rv lf cf M.

(* the kept value list and the kept invariant say the same as their list-form items *)
Lemma tok_regs_twin : forall u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra st rv fv,
  tok_regs_l (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st rv fv = tok_regs p q n cin0 (nth 0 fv 0) st.
Proof. intros. reflexivity. Qed.

Lemma zwtok_S9_twin {RCa1 : RunCtx}  : forall u p q n zc sE sW M,
  zwtok_S9_l u p q n zc sE sW M <-> zwtok_S9 u p q n zc sE sW M.
Proof.
  intros u p q n zc sE sW M. unfold zwtok_S9_l, zwtok_S9.
  split.
  - intros (s5 & s6 & s7 & s8 & s9 & s10 & s11 & cin0 & cout0 & W0 & ra & rv & fv & st & lf & cf & EsE & EsW & PURE & TM).
    exists s5, s6, s7, s8, s9, s10, s11, cin0, cout0, W0, ra, rv, (nth 0 fv 0), st, lf, cf.
    split; [exact EsE | split; [ | split; [exact PURE | exact (proj1 (tok_mem_twin _ _ _ _ _ _) TM)]]].
    exact (eq_trans EsW (tok_regs_twin u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra st rv fv)).
  - intros (s5 & s6 & s7 & s8 & s9 & s10 & s11 & cin0 & cout0 & W0 & ra & rv & s11v & st & lf & cf & EsE & EsW & PURE & TM).
    exists s5, s6, s7, s8, s9, s10, s11, cin0, cout0, W0, ra, rv, [s11v], st, lf, cf.
    split; [exact EsE | split; [ | split; [exact PURE | exact (proj2 (tok_mem_twin _ _ _ _ _ _) TM)]]].
    exact (eq_trans EsW (eq_sym (tok_regs_twin u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra st rv [s11v]))).
Qed.

Theorem zw_local {RCa1 : RunCtx}  : zw_local_stmt_S9 zwtok_S9.
Proof.
  intros u p q n zc sE sW M M' AG H.
  apply (proj1 (zwtok_S9_twin u p q n zc sE sW M')).
  apply (zw_local_l u p q n zc sE sW M M' AG).
  exact (proj2 (zwtok_S9_twin u p q n zc sE sW M) H).
Qed.
End S_Tok.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import SBase. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_Entry. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_Entry.S_Loop. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_Ret. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import S_Entry. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.S_Uw. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_LeaveA. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_Leave. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_Inflate. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZAw.S_U2A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2B. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require S_ZA. Import OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.S_ZA.S_U2C. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S Require Import S_ZA. Import S_Tok.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.

Section ZB.
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
Variable w : Z.
Hypothesis Hw : wok p q n zc w.
Variables (site : bool) (cin0 cout0 W0 rv : Z) (st : ist) (lf cf : Z -> Z).
Hypothesis Hcin0 : 0 <= cin0 <= n.
Hypothesis Hcout0 : 0 <= cout0 <= 262144.
Hypothesis SI : sinv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) st lf cf.
Hypothesis Hcc : cout0 < t_cout st.

Theorem zb_cps : forall Rb l M,
  zget_l Rb l kSP = u + -272 -> zget_l Rb l kA0 = w ->
  zget_l Rb l kS0 = BUF + t_cout st -> zget_l Rb l kS1 = t_out st - (262144 - t_cout st) ->
  zget_l Rb l kS2 = 1 -> zget_l Rb l kS3 = p -> zget_l Rb l kS4 = t_out st - (262144 - t_cout st) ->
  zget_l Rb l kS5 = n - cin0 -> zget_l Rb l kS6 = 262144 - t_cout st -> zget_l Rb l kS7 = t_hold st ->
  zget_l Rb l kS8 = t_bits st -> zget_l Rb l kS9 = t_out st -> zget_l Rb l kS11 = q + t_cin st ->
  zget_l Rb l kGP = gp -> zget_l Rb l kTP = tp ->
  rom_ok M -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M (u + -1024) 1232 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M p STATE_SIZE ->
  (w <> 0 -> mem_wr (run_segments R_segs rc_inp rc_sp rc_mb) M w WIN_SIZE) ->
  mem_arr 1 (run_segments R_segs rc_inp rc_sp rc_mb) M q n fin ->
  tok_mem (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) st rv lf cf M ->
  KZE2 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M w ->
  KZE1 u p gp tp s5 s6 s7 s8 s9 s10 s11 MD T M w ->
  realizes (run_segments R_segs rc_inp rc_sp rc_mb) (zcfg (run_segments R_segs rc_inp rc_sp rc_mb) L_ZB (zupd Rb l) M MD) T.
Proof.
  intros Rb l M. intros.
  assert (RHL : OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds
                  (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) (Some st)
                     [t_out st - (262144 - t_cout st); rv; w])
                  Rb l OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zb_v).
  { cbv [OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.rholds OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qvalv OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.SQuant.qval nth fst snd
         OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.I9S.SLayout.L.s_regs_zb_v]. split_conj; assumption. }
  assert (TML : tok_mem_l (cxc u p q n gp tp s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 (ra_site site)) st rv lf cf M).
  { apply (proj2 (tok_mem_twin _ _ _ _ _ _)). assumption. }
  apply zb_cps_l with (u := u) (p := p) (q := q) (n := n) (gp := gp) (tp := tp)
    (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11)
    (fin := fin) (zc := zc) (w := w) (site := site) (cin0 := cin0) (cout0 := cout0) (W0 := W0)
    (rv := rv) (st := st) (lf := lf) (cf := cf); assumption.
Qed.
End ZB.
