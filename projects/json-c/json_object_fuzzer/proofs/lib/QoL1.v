(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa Q6q3 QWxq_c1 Qc3B QEpW Qe4Y QbFI Qwm6 QZsi Qhd4 QupI QdM4 QXcG Qsn5 QJFf Qknc QBrp Q2ui Q1KO QRGF QlES Q9Ho QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH Q6EJ QyaF QXVi QQjP QJQc QKY2 QXDj Q45h QOTx Q25t QNDM Q7DP QZxC QvSK QVHx Qzcu QiHh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.json_c.json_object_fuzzer.images.AsanUbsan.

Import Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.

Import QWTC QND5 QsSk Qt8n QWtD QDlz QOTP Q1LT QpvH.

Import QyaF QXVi QQjP QJQc QKY2.
Import QXDj Q45h QOTx Q25t QNDM Q7DP QZxC.Mq0 QvSK.

Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Lemma REGS_MAIN_S : forall w ch, HSCLASS_S w ch ->
pc ch = QupI.MAIN_A
/\ nth 1 (s_regs (a_ss ch)) (ELit 0) = ELit QupI.RA_MAIN
/\ nth 2 (s_regs (a_ss ch)) (ELit 0) = EAlu Instr.ALU_ADD e_sp0 (ELit (-48))
/\ nth 3 (s_regs (a_ss ch)) (ELit 0) = ELit QupI.A_GP
/\ nth 4 (s_regs (a_ss ch)) (ELit 0) = ELit Qwm6.Mq4.A_TP
/\ nth 10 (s_regs (a_ss ch)) (ELit 0) = EVar 1
/\ nth 11 (s_regs (a_ss ch)) (ELit 0) = EAlu Instr.ALU_ADD e_sp0 (ELit 8).
Proof. intros [|] ch [-> | ->]; vm_compute; repeat split; reflexivity. Qed.

Section PerState.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation EI := (E0 JOB6PH sp rdraw brk0 argv envp uid hw).
#[local] Notation mv := (view LV mo FULL).

Lemma atop_al16 : atopE E mod 16 = 0.
Proof. rewrite (MV4 atop_val). destruct Hsp as (_ & _ & H3). replace (usp - 8388608) with (usp + (-524288) * 16) by lia. rewrite Z.mod_add by lia. exact H3. Qed.
Definition RCJ : Q6q3.RunConsts :=
Q6q3.mkRunConsts (atopE E) (ev E 45) (bv_unsigned (edenot E (EBlob false 25 8 8)))
(MA main_atop_bounds) atop_al16 (u64_range (edenot E (EBlob false 25 8 8))).
#[local] Existing Instance RCJ.
Lemma RCJ_ceil : @Q6q3.rc_ceil RCJ = atopE E.  Proof. reflexivity. Qed.
Lemma RCJ_can : @Q6q3.rc_canary RCJ = ev E 45.  Proof. reflexivity. Qed.
Lemma RCJ_sec : Z_to_bv 64 (@Q6q3.rc_secret RCJ) = edenot E (EBlob false 25 8 8).
Proof. cbn [Q6q3.rc_secret RCJ]. apply Z_to_bv_bv_unsigned. Qed.

Lemma Senv : forall n, (n < NX0)%nat -> ev E n = ev EI n.
Proof. exact (proj1 (P co_sinv)). Qed.
Lemma reg_at : forall k : Z, 1 <= k <= 31 -> reg_get R (Z_to_bv 5 k) = edenot E (nth (Z.to_nat k) (s_regs (a_ss ch)) (ELit 0)).
Proof.
intros k Hk. pose proof (P co_regs (Z_to_bv 5 k)) as G. unfold getr, sr_get, ridx in G.
assert (U : bv_unsigned (Z_to_bv 5 k) = k) by (apply Z_to_bv_small; unfold bv_modulus; cbn; lia).
assert (B : bv_eqb (Z_to_bv 5 k) 0 = false).
{ unfold bv_eqb. rewrite U. change (bv_unsigned (0 : bv 5)) with 0. apply Z.eqb_neq. lia. }
rewrite B, U in G. exact G.
Qed.
Lemma u_sp_off : forall d, - usp <= d -> usp + d < 2^64 -> edenot E (EAlu Instr.ALU_ADD e_sp0 (ELit d)) = Z_to_bv 64 (usp + d).
Proof.
intros d D1 D2. apply bv_eq. cbn [edenot]. rewrite u_add64, (MA main_sp0).
pose proof (u64_range sp) as RG. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma regs_main :
reg_get R (Z_to_bv 5 1) = Z_to_bv 64 QupI.RA_MAIN /\ reg_get R (Z_to_bv 5 2) = Z_to_bv 64 (usp - 48)
/\ reg_get R (Z_to_bv 5 3) = Z_to_bv 64 QupI.A_GP /\ reg_get R (Z_to_bv 5 4) = Z_to_bv 64 Qwm6.Mq4.A_TP
/\ reg_get R (Z_to_bv 5 10) = Z_to_bv 64 argc /\ reg_get R (Z_to_bv 5 11) = Z_to_bv 64 (usp + 8).
Proof.
destruct (REGS_MAIN_S w ch HCL) as (_ & R1 & R2 & R3 & R4 & R10 & R11).
destruct Hsp as (S1 & S2 & _). unfold sp_window_lo, sp_window_hi in *.
rewrite !reg_at by lia. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite R1, R2, R3, R4, R10, R11.
rewrite (u_sp_off (-48)), (u_sp_off 8) by lia.
repeat split; try reflexivity.
cbn [edenot]. rewrite (Senv 1%nat ltac:(unfold NX0; lia)).
destruct (QpvH.uE0 JOB6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
apply bv_eq. rewrite U3. destruct Hva as [A _]. rewrite u64_lit by lia. reflexivity.
Qed.

Lemma drv_pre_at : forall LO, usp - 8388608 <= LO -> LO + 2^22 <= usp - 48 ->
@QupI.drvA_pre RCJ argv usp LO mv mo.
Proof.
intros LO L1 L2.
pose proof (@drv_pre sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ RCJ_ceil) as D.
destruct D as [D1 D2 D3 D4 D5 D6 D7 D8]. constructor; try assumption.
- destruct D2 as [C1 C2]. split; lia.
- exact (proj2 (QWxq_c1.stk_split _ _ _ LO _ D3 ltac:(lia))).
Qed.

Theorem hmain_state :
forall (Hwx : QQIi.wx_segs_nowrap QbFI.asegs) (Hsegs : segs_in_base LV QbFI.asegs)
(Hsh : shoff_ok LV) (Hbx : bands_excl LV) (Hbc : bands_cover LV)
(H6 : @QZsi.heap_iface_A RCJ Qwm6.Mq4.A4L)
(H6_J : @QZsi.hiA_J RCJ Qwm6.Mq4.A4L H6 = QRGF.aj_base_vj QbFI.asegs LV Hwx Hsegs)
(GA : (word -> option byte) -> Prop) (TGT_STACK_A TGT_BB_A TGT_BD_A : Z)
(TGT : @QupI.target_A_stmt RCJ (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6) GA TGT_STACK_A TGT_BB_A TGT_BD_A)
(OBL_GA_of : forall argv0 USP A LB LM FR B m md, @QupI.drvA_mem argv0 USP m -> @Qhd4.HEAPA RCJ Qwm6.Mq4.A4L (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6) A LB LM FR B m md -> GA m)
(BANDS : QlES.Band)
(OBL_ISH : forall A LB LM FR B m md, @Qhd4.HEAPA RCJ Qwm6.Mq4.A4L (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6) A LB LM FR B m md -> @Q9Ho.ISH BANDS m)
(OBL_BLO : @QlES.band_lo BANDS <= @Qhd4.hiA_bot RCJ Qwm6.Mq4.A4L (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6))
(A0 : @QZsi.ASA RCJ Qwm6.Mq4.A4L H6) (LM0 : list QCcH.blk) (B0 : QZsi.bud) (LO : Z),

(forall ms, ms_mem ms = FULL -> @QZsi.HEAPA RCJ Qwm6.Mq4.A4L H6 A0 [] LM0 [] B0 mv (mkCfg ms mo)) ->
Z.of_nat (length LM0) < 8 ->
QXcG.Mq0.DRVA6_BQ TGT_BB_A <= QZsi.bQ B0 -> QXcG.Mq0.DRVA6_BB TGT_BB_A <= QZsi.bB B0 -> QXcG.Mq0.DRVA6_BN TGT_BB_A <= QZsi.bN B0 -> QXcG.Mq0.DRVA6_BD TGT_BD_A <= QZsi.bD B0 ->
QXcG.Mq0.DRVA6_BD TGT_BD_A <= 134217728 * QZsi.bM B0 ->
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A -> 1536 + 4 * TGT_BB_A <= 2^30 -> 0 <= TGT_BD_A ->
usp <= @QZsi.hiA_top RCJ Qwm6.Mq4.A4L H6 + 160 -> @QZsi.hiA_bot RCJ Qwm6.Mq4.A4L H6 <= LO ->
usp - 8388608 <= LO -> LO + 2^22 <= usp - 48 ->
Q6EJ.srealizes JOB6SEGS (cfg_of JOB6SEGS R (pc ch) FULL mo) (QBxa.Mq5.spec argv (m_fs mo)).
Proof.
intros Hwx Hsegs Hsh Hbx Hbc H6 H6_J GA TS_ TB_ TD_ TGT OGA BANDS OISH OBLO A0 LM0 B0 LO HEAP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT L1 L2.
apply (srz_A_to_C JOB6SEGS).
destruct (REGS_MAIN_S w ch HCL) as (PC & _).
unfold cfg_of, mkst. cbn [fp_regs fp_csr asanreflect_fx fx0]. rewrite PC.
apply (QVHx.Mq0.srealizes_canon JOB6SEGS R bvmap_empty (Z_to_bv 64 QupI.MAIN_A) (Z_to_bv 32 0) None FULL (seg_rom JOB6SEGS) mo).
destruct regs_main as (G1 & G2 & G3 & G4 & G10 & G11).
refine (@Qzcu.main_phase_jo RCJ LV Hwx Hsegs Hsh Hbx Hbc H6 H6_J GA TS_ TB_ TD_ TGT OGA BANDS OISH OBLO
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) mv
(mkCfg (QEpW.MS (Qe4Y.canonR R) bvmap_empty (Z_to_bv 64 QupI.MAIN_A) (Z_to_bv 32 0) None FULL (seg_rom JOB6SEGS)) mo)
A0 LM0 B0 argv usp LO _ _ _ Hva (drv_pre_at LO L1 L2) (HEAP (QEpW.MS (Qe4Y.canonR R) bvmap_empty (Z_to_bv 64 QupI.MAIN_A) (Z_to_bv 32 0) None FULL (seg_rom JOB6SEGS)) eq_refl) HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT G1 G2 G3 G4 G10 G11 _).
- exact (MA main_cinvA (QEpW.MS (Qe4Y.canonR R) bvmap_empty (Z_to_bv 64 QupI.MAIN_A) (Z_to_bv 32 0) None FULL (seg_rom JOB6SEGS)) eq_refl).
- exact (P co_halt).
- reflexivity.
- unfold QwAs.Mq1.frm0. reflexivity.
Qed.

Inductive handoff_rest : Prop :=
| HandoffRest :
forall (Hwx : QQIi.wx_segs_nowrap QbFI.asegs) (Hsegs : segs_in_base LV QbFI.asegs)
(Hsh : shoff_ok LV) (Hbx : bands_excl LV) (Hbc : bands_cover LV)
(H6 : @QZsi.heap_iface_A RCJ Qwm6.Mq4.A4L)
(H6_J : @QZsi.hiA_J RCJ Qwm6.Mq4.A4L H6 = QRGF.aj_base_vj QbFI.asegs LV Hwx Hsegs)
(GA : (word -> option byte) -> Prop) (TGT_STACK_A TGT_BB_A TGT_BD_A : Z)
(TGT : @QupI.target_A_stmt RCJ (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6) GA TGT_STACK_A TGT_BB_A TGT_BD_A)
(OBL_GA_of : forall argv0 USP A LB LM FR B m md, @QupI.drvA_mem argv0 USP m -> @Qhd4.HEAPA RCJ Qwm6.Mq4.A4L (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6) A LB LM FR B m md -> GA m)
(BANDS : QlES.Band)
(OBL_ISH : forall A LB LM FR B m md, @Qhd4.HEAPA RCJ Qwm6.Mq4.A4L (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6) A LB LM FR B m md -> @Q9Ho.ISH BANDS m)
(OBL_BLO : @QlES.band_lo BANDS <= @Qhd4.hiA_bot RCJ Qwm6.Mq4.A4L (Qhd4.hi5_of_v6 Qwm6.Mq4.A4L H6))
(A0 : @QZsi.ASA RCJ Qwm6.Mq4.A4L H6) (LM0 : list QCcH.blk) (B0 : QZsi.bud) (LO : Z),
(forall ms, ms_mem ms = FULL -> @QZsi.HEAPA RCJ Qwm6.Mq4.A4L H6 A0 [] LM0 [] B0 mv (mkCfg ms mo)) ->
Z.of_nat (length LM0) < 8 ->
QXcG.Mq0.DRVA6_BQ TGT_BB_A <= QZsi.bQ B0 -> QXcG.Mq0.DRVA6_BB TGT_BB_A <= QZsi.bB B0 -> QXcG.Mq0.DRVA6_BN TGT_BB_A <= QZsi.bN B0 -> QXcG.Mq0.DRVA6_BD TGT_BD_A <= QZsi.bD B0 ->
QXcG.Mq0.DRVA6_BD TGT_BD_A <= 134217728 * QZsi.bM B0 ->
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A -> 1536 + 4 * TGT_BB_A <= 2^30 -> 0 <= TGT_BD_A ->
usp <= @QZsi.hiA_top RCJ Qwm6.Mq4.A4L H6 + 160 -> @QZsi.hiA_bot RCJ Qwm6.Mq4.A4L H6 <= LO ->
usp - 8388608 <= LO -> LO + 2^22 <= usp - 48 ->
handoff_rest.

Theorem hmain_of_rest : handoff_rest -> Q6EJ.srealizes JOB6SEGS (cfg_of JOB6SEGS R (pc ch) FULL mo) (QBxa.Mq5.spec argv (m_fs mo)).
Proof.
intros [Hwx Hsegs Hsh Hbx Hbc H6 H6_J GA TS_ TB_ TD_ TGT OGA BANDS OISH OBLO A0 LM0 B0 LO HEAP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT L1 L2].
exact (hmain_state Hwx Hsegs Hsh Hbx Hbc H6 H6_J GA TS_ TB_ TD_ TGT OGA BANDS OISH OBLO A0 LM0 B0 LO HEAP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT L1 L2).
Qed.
End PerState.

Lemma spec_nil : forall argv fs, QBxa.Mq5.spec argv fs [].
Proof.
intros argv fs. unfold QBxa.Mq5.spec.
assert (D : forall msg, QBxa.Mq5.t_die msg fs []) by (intros msg; unfold QBxa.Mq5.t_die; apply Q85Z.t_emit_has_nil).
destruct argv as [|a [|path [|b r]]]; try apply D.
destruct (4096 <=? length path)%nat; [apply D|]. destruct (QBxa.Mq5.list_byte_eqb path []); [apply D|].
destruct (QBxa.Mq5.list_byte_eqb path QBxa.Mq5.dot_path); [left; apply D|].
destruct (fs_lookup fs path); [left; apply D| apply D].
Qed.

Section Run.
Variable sp : word.
Variable rdraw : EntryDraw.
Variables brk0 mbase : word.
Variables argv envp : list (list byte).
Variable ifs : Fs.Fs.
Variable stdin : InputStream.
Variables uid gid hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abort_terminal : bool.
Variable urnd : InputStream.
Variable tmp : Fs.Fs.
#[local] Notation fs := (fs_seed_tmp ifs tmp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk JOB6SEGS brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.

Hypothesis OBL_HANDOFF_REST : forall E R FULL mo w ch (HCL : HSCLASS_S w ch)
(CS : cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL mo),
handoff_rest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.

Theorem HMAIN_jo : forall h ch, QiHh.HS2s h = Some ch ->
forall E R FULL model, cs_ok JOB6SEGS BJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JOB6PH sp rdraw brk0 argv envp uid hw) (argH0 JOB6PH sp rdraw argv envp uid hw) fs E ch R FULL model ->
Q6EJ.srealizes JOB6SEGS (cfg_of JOB6SEGS R (pc ch) FULL model) (QBxa.Mq5.spec argv (m_fs model)).
Proof.
intros h ch Hh E R FULL model HC. destruct (HS2s_class h ch Hh) as [w HCL].
exact (hmain_of_rest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL model w ch HCL HC (OBL_HANDOFF_REST E R FULL model w ch HCL HC)).
Qed.

Theorem jo_both_srealizes :
Q6EJ.srealizes JOB6SEGS (init_config JOB6SEGS AsanUbsan.M.init_pc JOB6PH sp brk0 mbase rdraw QpvH.LIMIT
(QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp))
(QBxa.Mq5.spec argv fs).
Proof.
exact (QiHh.asan_startup_job6S sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp
Hsp Hbrk Hva Hve Hfit Huid (fun fs' => QBxa.Mq5.spec argv fs') (fun fs' => spec_nil argv fs') HMAIN_jo).
Qed.
End Run.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2y2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXcG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5o6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5o6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Cb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Cb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZxC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZxC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvSK.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVHx. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzcu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Lemma REGS_MAIN_S : forall w ch, HSCLASS_S w ch ->
pc ch = Q2y2.MAIN_A
/\ nth 1 (s_regs (a_ss ch)) (ELit 0) = ELit Q2y2.RA_MAIN
/\ nth 2 (s_regs (a_ss ch)) (ELit 0) = EAlu Instr.ALU_ADD e_sp0 (ELit (-48))
/\ nth 3 (s_regs (a_ss ch)) (ELit 0) = ELit Q2y2.A_GP
/\ nth 4 (s_regs (a_ss ch)) (ELit 0) = ELit Qwm6.Mq0.A_TP
/\ nth 10 (s_regs (a_ss ch)) (ELit 0) = EVar 1
/\ nth 11 (s_regs (a_ss ch)) (ELit 0) = EAlu Instr.ALU_ADD e_sp0 (ELit 8).
Proof. intros [|] ch [-> | ->]; vm_compute; repeat split; reflexivity. Qed.

Section PerState.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation LV := (LV_J E).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation MV4 L := (L sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation EI := (E0 JO6PH sp rdraw brk0 argv envp uid hw).
#[local] Notation mv := (view LV mo FULL).

Lemma atop_al16 : atopE E mod 16 = 0.
Proof. rewrite (MV4 atop_val). destruct Hsp as (_ & _ & H3). replace (usp - 8388608) with (usp + (-524288) * 16) by lia. rewrite Z.mod_add by lia. exact H3. Qed.
Definition RCJ : Q6q3.RunConsts :=
Q6q3.mkRunConsts (atopE E) (ev E 45) (bv_unsigned (edenot E (EBlob false 25 8 8)))
(MA main_atop_bounds) atop_al16 (u64_range (edenot E (EBlob false 25 8 8))).
#[local] Existing Instance RCJ.
Lemma RCJ_ceil : @Q6q3.rc_ceil RCJ = atopE E.  Proof. reflexivity. Qed.
Lemma RCJ_can : @Q6q3.rc_canary RCJ = ev E 45.  Proof. reflexivity. Qed.
Lemma RCJ_sec : Z_to_bv 64 (@Q6q3.rc_secret RCJ) = edenot E (EBlob false 25 8 8).
Proof. cbn [Q6q3.rc_secret RCJ]. apply Z_to_bv_bv_unsigned. Qed.

Lemma Senv : forall n, (n < NX0)%nat -> ev E n = ev EI n.
Proof. exact (proj1 (P co_sinv)). Qed.
Lemma reg_at : forall k : Z, 1 <= k <= 31 -> reg_get R (Z_to_bv 5 k) = edenot E (nth (Z.to_nat k) (s_regs (a_ss ch)) (ELit 0)).
Proof.
intros k Hk. pose proof (P co_regs (Z_to_bv 5 k)) as G. unfold getr, sr_get, ridx in G.
assert (U : bv_unsigned (Z_to_bv 5 k) = k) by (apply Z_to_bv_small; unfold bv_modulus; cbn; lia).
assert (B : bv_eqb (Z_to_bv 5 k) 0 = false).
{ unfold bv_eqb. rewrite U. change (bv_unsigned (0 : bv 5)) with 0. apply Z.eqb_neq. lia. }
rewrite B, U in G. exact G.
Qed.
Lemma u_sp_off : forall d, - usp <= d -> usp + d < 2^64 -> edenot E (EAlu Instr.ALU_ADD e_sp0 (ELit d)) = Z_to_bv 64 (usp + d).
Proof.
intros d D1 D2. apply bv_eq. cbn [edenot]. rewrite u_add64, (MA main_sp0).
pose proof (u64_range sp) as RG. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma regs_main :
reg_get R (Z_to_bv 5 1) = Z_to_bv 64 Q2y2.RA_MAIN /\ reg_get R (Z_to_bv 5 2) = Z_to_bv 64 (usp - 48)
/\ reg_get R (Z_to_bv 5 3) = Z_to_bv 64 Q2y2.A_GP /\ reg_get R (Z_to_bv 5 4) = Z_to_bv 64 Qwm6.Mq0.A_TP
/\ reg_get R (Z_to_bv 5 10) = Z_to_bv 64 argc /\ reg_get R (Z_to_bv 5 11) = Z_to_bv 64 (usp + 8).
Proof.
destruct (REGS_MAIN_S w ch HCL) as (_ & R1 & R2 & R3 & R4 & R10 & R11).
destruct Hsp as (S1 & S2 & _). unfold sp_window_lo, sp_window_hi in *.
rewrite !reg_at by lia. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite R1, R2, R3, R4, R10, R11.
rewrite (u_sp_off (-48)), (u_sp_off 8) by lia.
repeat split; try reflexivity.
cbn [edenot]. rewrite (Senv 1%nat ltac:(unfold NX0; lia)).
destruct (QpvH.uE0 JO6PH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
apply bv_eq. rewrite U3. destruct Hva as [A _]. rewrite u64_lit by lia. reflexivity.
Qed.

Lemma drv_pre_at : forall LO, usp - 8388608 <= LO -> LO + 2^22 <= usp - 48 ->
@Q2y2.drvA_pre RCJ argv usp LO mv mo.
Proof.
intros LO L1 L2.
pose proof (@drv_pre sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS RCJ RCJ_ceil) as D.
destruct D as [D1 D2 D3 D4 D5 D6 D7 D8]. constructor; try assumption.
- destruct D2 as [C1 C2]. split; lia.
- exact (proj2 (QWxq_c1.stk_split _ _ _ LO _ D3 ltac:(lia))).
Qed.

Theorem hmain_state :
forall (Hwx : QQIi.wx_segs_nowrap QvG1.asegs) (Hsegs : segs_in_base LV QvG1.asegs)
(Hsh : shoff_ok LV) (Hbx : bands_excl LV) (Hbc : bands_cover LV)
(H6 : @QZsi.heap_iface_A RCJ Qwm6.Mq0.A4L)
(H6_J : @QZsi.hiA_J RCJ Qwm6.Mq0.A4L H6 = QRGF.aj_base_vj QvG1.asegs LV Hwx Hsegs)
(GA : (word -> option byte) -> Prop) (TGT_STACK_A TGT_BB_A TGT_BD_A : Z)
(TGT : @Q2y2.target_A_stmt RCJ (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6) GA TGT_STACK_A TGT_BB_A TGT_BD_A)
(OBL_GA_of : forall argv0 USP A LB LM FR B m md, @Q2y2.drvA_mem argv0 USP m -> @Qhd4.HEAPA RCJ Qwm6.Mq0.A4L (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6) A LB LM FR B m md -> GA m)
(BANDS : QlES.Band)
(OBL_ISH : forall A LB LM FR B m md, @Qhd4.HEAPA RCJ Qwm6.Mq0.A4L (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6) A LB LM FR B m md -> @Q9Ho.Mq0.ISH BANDS m)
(OBL_BLO : @QlES.band_lo BANDS <= @Qhd4.hiA_bot RCJ Qwm6.Mq0.A4L (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6))
(A0 : @QZsi.ASA RCJ Qwm6.Mq0.A4L H6) (LM0 : list QCcH.blk) (B0 : QZsi.bud) (LO : Z),

(forall ms, ms_mem ms = FULL -> @QZsi.HEAPA RCJ Qwm6.Mq0.A4L H6 A0 [] LM0 [] B0 mv (mkCfg ms mo)) ->
Z.of_nat (length LM0) < 8 ->
QXcG.DRVA6_BQ TGT_BB_A <= QZsi.bQ B0 -> QXcG.DRVA6_BB TGT_BB_A <= QZsi.bB B0 -> QXcG.DRVA6_BN TGT_BB_A <= QZsi.bN B0 -> QXcG.DRVA6_BD TGT_BD_A <= QZsi.bD B0 ->
QXcG.DRVA6_BD TGT_BD_A <= 134217728 * QZsi.bM B0 ->
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A -> 1536 + 4 * TGT_BB_A <= 2^30 -> 0 <= TGT_BD_A ->
usp <= @QZsi.hiA_top RCJ Qwm6.Mq0.A4L H6 + 160 -> @QZsi.hiA_bot RCJ Qwm6.Mq0.A4L H6 <= LO ->
usp - 8388608 <= LO -> LO + 2^22 <= usp - 48 ->
Q6EJ.srealizes JO6SEGS (cfg_of JO6SEGS R (pc ch) FULL mo) (QBxa.Mq5.spec argv (m_fs mo)).
Proof.
intros Hwx Hsegs Hsh Hbx Hbc H6 H6_J GA TS_ TB_ TD_ TGT OGA BANDS OISH OBLO A0 LM0 B0 LO HEAP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT L1 L2.
apply (srz_A_to_C JO6SEGS).
destruct (REGS_MAIN_S w ch HCL) as (PC & _).
unfold cfg_of, mkst. cbn [fp_regs fp_csr asanreflect_fx fx0]. rewrite PC.
apply (QVHx.srealizes_canon JO6SEGS R bvmap_empty (Z_to_bv 64 Q2y2.MAIN_A) (Z_to_bv 32 0) None FULL (seg_rom JO6SEGS) mo).
destruct regs_main as (G1 & G2 & G3 & G4 & G10 & G11).
refine (@Qzcu.Mq0.main_phase_jo RCJ LV Hwx Hsegs Hsh Hbx Hbc H6 H6_J GA TS_ TB_ TD_ TGT OGA BANDS OISH OBLO
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bvmap_empty (Z_to_bv 32 0) mv
(mkCfg (QEpW.MS (Qe4Y.canonR R) bvmap_empty (Z_to_bv 64 Q2y2.MAIN_A) (Z_to_bv 32 0) None FULL (seg_rom JO6SEGS)) mo)
A0 LM0 B0 argv usp LO _ _ _ Hva (drv_pre_at LO L1 L2) (HEAP (QEpW.MS (Qe4Y.canonR R) bvmap_empty (Z_to_bv 64 Q2y2.MAIN_A) (Z_to_bv 32 0) None FULL (seg_rom JO6SEGS)) eq_refl) HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT G1 G2 G3 G4 G10 G11 _).
- exact (MA main_cinvA (QEpW.MS (Qe4Y.canonR R) bvmap_empty (Z_to_bv 64 Q2y2.MAIN_A) (Z_to_bv 32 0) None FULL (seg_rom JO6SEGS)) eq_refl).
- exact (P co_halt).
- reflexivity.
- unfold QwAs.Mq1.frm0. reflexivity.
Qed.

Inductive handoff_rest : Prop :=
| HandoffRest :
forall (Hwx : QQIi.wx_segs_nowrap QvG1.asegs) (Hsegs : segs_in_base LV QvG1.asegs)
(Hsh : shoff_ok LV) (Hbx : bands_excl LV) (Hbc : bands_cover LV)
(H6 : @QZsi.heap_iface_A RCJ Qwm6.Mq0.A4L)
(H6_J : @QZsi.hiA_J RCJ Qwm6.Mq0.A4L H6 = QRGF.aj_base_vj QvG1.asegs LV Hwx Hsegs)
(GA : (word -> option byte) -> Prop) (TGT_STACK_A TGT_BB_A TGT_BD_A : Z)
(TGT : @Q2y2.target_A_stmt RCJ (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6) GA TGT_STACK_A TGT_BB_A TGT_BD_A)
(OBL_GA_of : forall argv0 USP A LB LM FR B m md, @Q2y2.drvA_mem argv0 USP m -> @Qhd4.HEAPA RCJ Qwm6.Mq0.A4L (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6) A LB LM FR B m md -> GA m)
(BANDS : QlES.Band)
(OBL_ISH : forall A LB LM FR B m md, @Qhd4.HEAPA RCJ Qwm6.Mq0.A4L (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6) A LB LM FR B m md -> @Q9Ho.Mq0.ISH BANDS m)
(OBL_BLO : @QlES.band_lo BANDS <= @Qhd4.hiA_bot RCJ Qwm6.Mq0.A4L (Qhd4.hi5_of_v6 Qwm6.Mq0.A4L H6))
(A0 : @QZsi.ASA RCJ Qwm6.Mq0.A4L H6) (LM0 : list QCcH.blk) (B0 : QZsi.bud) (LO : Z),
(forall ms, ms_mem ms = FULL -> @QZsi.HEAPA RCJ Qwm6.Mq0.A4L H6 A0 [] LM0 [] B0 mv (mkCfg ms mo)) ->
Z.of_nat (length LM0) < 8 ->
QXcG.DRVA6_BQ TGT_BB_A <= QZsi.bQ B0 -> QXcG.DRVA6_BB TGT_BB_A <= QZsi.bB B0 -> QXcG.DRVA6_BN TGT_BB_A <= QZsi.bN B0 -> QXcG.DRVA6_BD TGT_BD_A <= QZsi.bD B0 ->
QXcG.DRVA6_BD TGT_BD_A <= 134217728 * QZsi.bM B0 ->
0 <= TGT_STACK_A <= 2^21 -> 0 <= TGT_BB_A -> 1536 + 4 * TGT_BB_A <= 2^30 -> 0 <= TGT_BD_A ->
usp <= @QZsi.hiA_top RCJ Qwm6.Mq0.A4L H6 + 160 -> @QZsi.hiA_bot RCJ Qwm6.Mq0.A4L H6 <= LO ->
usp - 8388608 <= LO -> LO + 2^22 <= usp - 48 ->
handoff_rest.

Theorem hmain_of_rest : handoff_rest -> Q6EJ.srealizes JO6SEGS (cfg_of JO6SEGS R (pc ch) FULL mo) (QBxa.Mq5.spec argv (m_fs mo)).
Proof.
intros [Hwx Hsegs Hsh Hbx Hbc H6 H6_J GA TS_ TB_ TD_ TGT OGA BANDS OISH OBLO A0 LM0 B0 LO HEAP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT L1 L2].
exact (hmain_state Hwx Hsegs Hsh Hbx Hbc H6 H6_J GA TS_ TB_ TD_ TGT OGA BANDS OISH OBLO A0 LM0 B0 LO HEAP HLM HBQ HBB HBN HBD HBM TS TB TB6 TD TOP BOT L1 L2).
Qed.
End PerState.

Lemma spec_nil : forall argv fs, QBxa.Mq5.spec argv fs [].
Proof.
intros argv fs. unfold QBxa.Mq5.spec.
assert (D : forall msg, QBxa.Mq5.t_die msg fs []) by (intros msg; unfold QBxa.Mq5.t_die; apply Q85Z.t_emit_has_nil).
destruct argv as [|a [|path [|b r]]]; try apply D.
destruct (4096 <=? length path)%nat; [apply D|]. destruct (QBxa.Mq5.list_byte_eqb path []); [apply D|].
destruct (QBxa.Mq5.list_byte_eqb path QBxa.Mq5.dot_path); [left; apply D|].
destruct (fs_lookup fs path); [left; apply D| apply D].
Qed.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qb9l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section Run.
Variable sp : word.
Variable rdraw : EntryDraw.
Variables brk0 mbase : word.
Variables argv envp : list (list byte).
Variable ifs : Fs.Fs.
Variable stdin : InputStream.
Variables uid gid hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abort_terminal : bool.
Variable urnd : InputStream.
Variable tmp : Fs.Fs.
#[local] Notation fs := (fs_seed_tmp ifs tmp).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk JO6SEGS brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.

Hypothesis OBL_HANDOFF_REST : forall E R FULL mo w ch (HCL : HSCLASS_S w ch)
(CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo),
handoff_rest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL mo w ch HCL CS.

Theorem HMAIN_jo : forall h ch, Qb9l.HS2s h = Some ch ->
forall E R FULL model, cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL model ->
Q6EJ.srealizes JO6SEGS (cfg_of JO6SEGS R (pc ch) FULL model) (QBxa.Mq5.spec argv (m_fs model)).
Proof.
intros h ch Hh E R FULL model HC. destruct (HS2s_class h ch Hh) as [w HCL].
exact (hmain_of_rest sp rdraw brk0 argv envp fs uid hw Hsp Hva Hve Hfit E R FULL model w ch HCL HC (OBL_HANDOFF_REST E R FULL model w ch HCL HC)).
Qed.

Theorem jo_asan_srealizes :
Q6EJ.srealizes JO6SEGS (init_config JO6SEGS Asan.M.init_pc JO6PH sp brk0 mbase rdraw QpvH.LIMIT
(QpvH.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp))
(QBxa.Mq5.spec argv fs).
Proof.
exact (Qb9l.asan_startup_jo6S sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abort_terminal urnd tmp
Hsp Hbrk Hva Hve Hfit Huid (fun fs' => QBxa.Mq5.spec argv fs') (fun fs' => spec_nil argv fs') HMAIN_jo).
Qed.
End Run.
