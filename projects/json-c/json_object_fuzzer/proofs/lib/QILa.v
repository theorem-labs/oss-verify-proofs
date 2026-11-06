(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEUF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEUF.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qkko.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qkko.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlmN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlmN.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWrz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWrz.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt1H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt1H.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpfz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpfz.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMgr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMgr.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ2r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ2r.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ2r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ2r.Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAzu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAzu.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6vt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6vt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZUC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZUC.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2EX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDr.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpfz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpfz.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSCases2F.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis FL0 : pf_fl pf = 0.
Hypothesis UTFR : utf8rep = Qa8x.Mq3.utf8rep.
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Lemma case_finish : CASEx ST_finish.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR.
pose proof INV as [(LEN32 & D32 & _) _].
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 512 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
eapply (seg_finish_B HIx GA GA_outside GA_pres PUT pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | |].
-
intros D0 gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | | exact FS | exact FRM].
eapply (JOUT_of_PBJ (pf_len pf) m ts ts _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pj' dp lp gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hdp Hlp Hstp INV' OBJV PBK' BK' FS' FRM'.
set (ts' := TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) in *.
assert (Ecs' : cur_st ts' = tl_st lp) by (unfold cur_st, ts'; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
assert (Ess' : cur_ss ts' = tl_ss lp) by (unfold cur_ss, ts'; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
assert (RK' : rank (tl_st lp) (tl_ss lp) = 3%nat) by (destruct Hstp as [-> | ->]; reflexivity).
assert (RK : rank (tl_st l) (tl_ss l) = 5%nat) by (rewrite Hst; reflexivity).
eapply (IHR ts'); [| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
+ unfold mredo in *. rewrite Ecs', Ess', RK'. rewrite Est, Ess, RK in M. change (mbase pf ts') with (mbase pf ts). lia.
+ intros E. exfalso. rewrite Ecs' in E. destruct Hstp as [E2 | E2]; rewrite E2 in E; discriminate E.
+ unfold SPOK. rewrite Ecs'. intros HH. exfalso. destruct Hstp as [E2 | E2]; rewrite E2 in HH; discriminate HH.
+ unfold ts'. eapply (tdepth_ok_pop ts l dp lp); [exact TD | exact Hl | exact Hdp | exact Hlp | reflexivity |].
rewrite LEN32. pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _). lia.
+ unfold PBS. rewrite Ecs'. assert (HZP : zin (tl_st lp) [ST_array_add; ST_ovadd] = true) by (destruct Hstp as [-> | ->]; reflexivity).
assert (HP9 : jpi (tl_st lp) (tl_ss lp) <= jpi (tl_st l) (tl_ss l)) by (rewrite Hst; destruct Hstp as [-> | ->]; jl_arith).
destruct Hstp as [E9 | E9]; rewrite E9; pbs_norm; (eapply (PBJ_pop m m' ts dp l lp _ _ _ _ Hdp); [rewrite <- Hdp; exact Hl | exact Hlp | rewrite Hst; reflexivity | exact HZP | exact PBK | exact PBK' | lia | exact HP9]).
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| unfold bx; rewrite Ecs', Ess', Est, Ess, Hst; change (t_co ts') with (t_co ts); destruct Hstp as [-> | ->]; bres_norm; bx_fin]). unfold mredo. rewrite Ecs', Ess', RK', Est, Ess, RK. change (mbase pf ts') with (mbase pf ts). lia.
+ split; [intros _; exact OBJV | intros E; exfalso; rewrite Ecs' in E; destruct Hstp as [E2 | E2]; rewrite E2 in E; discriminate E].
Qed.
End PeSCases2F.
End RC__1.
