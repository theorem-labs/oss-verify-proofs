(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qb4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qb4w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtMn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qjk3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qjk3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Quoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Quoa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY9Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY9Y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyuL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyuL.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBGG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBGG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qh14.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qh14. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGEL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGEL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmtA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdgq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdgq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIjw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIjw.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEE7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEE7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrIB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHNo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHNo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QL1n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QL1n.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition DC_STK0_P : Z := 16 + 112 + 10528.
Definition DC_STK1_P : Z := 112.

Section HarnJoP3.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Hypothesis GETB : jo_get_pure_stmt S4L HIx S4F 0x244d0.
Hypothesis GETD : hi_top S4L HIx < 2^62 -> jo_get_double_stmt S4L HIx S4F 0x24f14 (64 + 8928) GD_LCONV_P GD_DP_P.
Hypothesis GETI : hi_top S4L HIx < 2^62 -> jo_get_num_stmt S4L HIx S4F 0x24618 448.
Hypothesis GETI64 : hi_top S4L HIx < 2^62 -> jo_get_num_stmt S4L HIx S4F 0x2481c 448.
Hypothesis GETU64 : hi_top S4L HIx < 2^62 -> jo_get_num_stmt S4L HIx S4F 0x24958 448.
Hypothesis GETS : hi_top S4L HIx < 2^62 -> get_string_stmt_P HIx.
Hypothesis GETS0 : get_string_null_P HIx.
Hypothesis GETSL : jo_get_pure_stmt S4L HIx S4F 0x252d8.
Hypothesis GETO : jo_get_pure_stmt S4L HIx S4F 0x2437c.
Hypothesis GETA : jo_get_pure_stmt S4L HIx S4F 0x254f0.
Hypothesis GETT : jo_get_pure_stmt S4L HIx S4F 0x23934.
Hypothesis VISIT : jo_visit_stmt S4L HIx S4F JCVISIT_P EMIT_P 112 96.
Hypothesis SETI : jo_set_scalar_stmt S4L HIx S4F 0x24770.
Hypothesis SETI64 : jo_set_scalar_stmt S4L HIx S4F 0x24798.
Hypothesis SETU64 : jo_set_scalar_stmt S4L HIx S4F 0x24a90.
Hypothesis SETB : jo_set_scalar_stmt S4L HIx S4F 0x24598.
Hypothesis SETD : jo_set_double_stmt2 HIx SD_ENTRY_P SD_TBL_P SD_STK.
Hypothesis CFP : cfp_stmt rsegs CFP_P CFP_STK_P IHI_P.
Hypothesis CRLS : crls_stmt rsegs CRLS_P CRLS_FRAME_P.
Hypothesis SETS : jo_set_string_stmt S4L HIx S4F 0x25304 (64 + 8256).
Hypothesis SETSL : jo_set_string_len_stmt S4L HIx S4F 0x25460 (64 + 8256).
Hypothesis TOKPARSE : tokparse_stmt_P HIx.
Hypothesis DEEP : hi_top S4L HIx < 2^62 -> jo_deep_copy_stmt S4L HIx S4F jc_glob_P 0x258a0 0x25548 DC_STK0_P DC_STK1_P.
Hypothesis PUT : put_stmt_P HIx.
Hypothesis PUTX : jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.

Section Ctx.
Variables (sp0 lo : Z) (LB : list blk) (m0 : word -> option byte) (md0 : Model) (F0 : bvmap 5 word) (fc0 : bv 32).
Variables (ra0 s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (T : TSet).
Variables (data0 size : Z) (payload : list byte).
Let spf : Z := sp0 - 80.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= sp0 - TGT_STACK.
Hypothesis SPA : sp0 mod 16 = 0.
Hypothesis HT : sp0 <= hi_top S4L HIx.
Hypothesis HT62 : hi_top S4L HIx < 2^62.
Hypothesis RA0 : bv_unsigned ra0 mod 2 = 0.
Hypothesis FRM0 : frm0 fc0.
Hypothesis PLEN : Z.of_nat (length payload) = size.
Hypothesis SZ : 0 <= size < 2^26.
Hypothesis D0 : 0 < data0.
Hypothesis DSZ : data0 + size < 2^63.
Hypothesis INB : size = 0 \/ In (data0, size) LB.
Hypothesis DLO : data0 + size <= alloc_ceiling.

Hypothesis K : forall ms' m' md' (A' : AS S4L HIx) (errv' gp' : word) (LK : list blk),
ret_statew S4L ra0 (Z_to_bv 64 sp0) gp' (Z_to_bv 64 0x75e70) s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 fc0 (Z_to_bv 64 0) m' ms' ->
model_vm_only md0 md' ->
stk rsegs m' lo sp0 ->
heap_presx S4L (xtgt S4L) LB sp0 m0 m' ->
rw_cells rsegs m' (T_LOCCELL S4L) [C8 (Z_to_bv 64 (T_GLOBLOC S4L))] ->
rw_cells rsegs m' (0x75e70 - 164) [C4 errv'] ->
hglob_P m' ->
HEAPx A' (LB ++ LK) m' md' ->
realizes rsegs (mkCfg ms' md') T.

Notation HINVc := (HINV sp0 lo LB m0 md0 F0 ra0 s0v s1v data0 size).
Notation SINVc := (SINV HIx sp0 lo LB m0 md0 F0 ra0 s0v s1v data0 size).

Local Ltac feed_hyps t :=
lazymatch type of t with
| forall _ : ?A, _ => first [ feed_hyps (t GETB) | feed_hyps (t GETD) | feed_hyps (t GETI) | feed_hyps (t GETI64) | feed_hyps (t GETU64) | feed_hyps (t GETS) | feed_hyps (t GETS0) | feed_hyps (t GETSL) | feed_hyps (t GETO) | feed_hyps (t GETA) | feed_hyps (t GETT) | feed_hyps (t VISIT) | feed_hyps (t SETI) | feed_hyps (t SETI64) | feed_hyps (t SETU64) | feed_hyps (t SETB) | feed_hyps (t SETD) | feed_hyps (t CFP) | feed_hyps (t CRLS) | feed_hyps (t SETS) | feed_hyps (t SETSL) | feed_hyps (t TOKPARSE) | feed_hyps (t DEEP) | feed_hyps (t PUT) | feed_hyps (t PUTX) | feed_hyps (t LO) | feed_hyps (t LOS) | feed_hyps (t SPA) | feed_hyps (t HT) | feed_hyps (t HT62) | feed_hyps (t RA0) | feed_hyps (t FRM0) | feed_hyps (t PLEN) | feed_hyps (t SZ) | feed_hyps (t D0) | feed_hyps (t DSZ) | feed_hyps (t INB) | feed_hyps (t DLO) | feed_hyps (t K) | exact t ]
| _ => exact t
end.
Let HINV_callc := ltac:(feed_hyps (HINV_call sp0 lo LB m0 md0 F0 ra0 s0v s1v data0 size payload)).

#[using="RC__ lo LB m0 md0 F0 ra0 s0v s1v data0 size payload SPA SZ D0 INB DLO"] Lemma spf16'' : spf mod 16 = 0.
Proof. unfold spf. replace (sp0 - 80) with (sp0 + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact SPA. Qed.

#[using="PUT PUTX LB m0 md0 F0 ra0 s0v s1v data0 size payload LO LOS SPA HT HT62 SZ D0 INB DLO"] Lemma put_any : forall (ret : Z) (d : jroot) (q : Z) m md (A : AS S4L HIx) (DBS LBx : list blk) errv
(gp t0 t1 t2 s0r s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
0 <= ret < 2^64 -> ret mod 2 = 0 ->
HEAPx A (DBS ++ LBx) m md -> jroot_rep S4L S4F d m DBS q ->
stk rsegs m lo spf -> rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
(forall m' md' (A' : AS S4L HIx) F' fc' (errv' : word) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
model_vm_only md md' -> fsaved F F' -> (frm0 fc -> frm0 fc') -> stk rsegs m' lo spf ->
heap_pres S4L LBx spf m m' -> rw_cells rsegs m' (0x75e70 - 164) [C4 errv'] -> HEAPx A' LBx m' md' ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x75e70) xt0 xt1 xt2 s0r s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
F' (Z_to_bv 64 ret) fc' None m' (seg_rom rsegs)) md') T) ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x75e70) t0 t1 t2 s0r s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 put_entry_P) fc None m (seg_rom rsegs)) md) T.
Proof.
intros ret d q m md A DBS LBx errv gp t0 t1 t2 s0r s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc Hret Hret2 HP RR ST ERR KQ.
pose proof spf16'' as SPF16. unfold TGT_STACK in LOS. unfold_consts.
assert (TREE : forall s : option jshape, put_pre S4L S4F s m DBS q 1 ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x75e70) t0 t1 t2 s0r s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 put_entry_P) fc None m (seg_rom rsegs)) md) T).
{ intros s PRE. pose proof PUT as PU. unfold put_stmt_P, put_stmt in PU.
eapply PU with (A := A) (BS := DBS) (LB := LBx) (s := s) (lo := lo) (rc := 1);
[ exact HP | exact PRE | reflexivity | rewrite unsigned_lit by (unfold spf; lia); exact ST | exact LO
| rewrite unsigned_lit by (unfold spf; lia); unfold put_stk_P, spf; lia | rewrite unsigned_lit by (unfold spf; lia); exact SPF16
| rewrite unsigned_lit by (unfold spf; lia); unfold spf; lia | exact ERR | reflexivity | rewrite unsigned_lit by lia; exact Hret2 |].
intros ms' md' (m' & A' & r' & RS & VM' & ST' & HPR' & ERR' & OUT).
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', ERR', OUT |- *. rewrite unsigned_lit in ST', HPR' by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
destruct OUT as [[_ HP'] | (s' & _ & Hrc & _)]; [| lia].
eapply KQ; [exact VM' | exact FS' | exact FRM' | exact ST' | exact HPR' | exact ERR' | exact HP']. }
destruct d as [|s|tojs|].
- destruct RR as [-> ->]. apply (TREE None). split; reflexivity.
- destruct RR as [Hq J]. apply (TREE (Some s)). split; [exact Hq|]. split; [lia | exact J].
- pose proof PUTX as PX. unfold jo_put_xleaf_stmt in PX.
eapply PX with (A := A) (BS := DBS) (LB := LBx) (r := JRdblx tojs) (lo := lo);
[ split; [exact HP|]; rewrite unsigned_lit by (unfold spf; lia);
split; [exact ST|]; split; [exact LO|]; split; [unfold put_stk_P, spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR|]; split; [reflexivity | rewrite unsigned_lit by lia; exact Hret2]
| exact RR | exact I | reflexivity |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) _ ERRx [A' HP'].
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', ERRx, HP' |- *. rewrite unsigned_lit in ST', HPR' by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
eapply KQ; [exact VM' | exact FS' | exact FRM' | exact ST' | exact HPR' | exact ERRx | exact HP'].
- pose proof PUTX as PX. unfold jo_put_xleaf_stmt in PX.
eapply PX with (A := A) (BS := DBS) (LB := LBx) (r := JRstrx) (lo := lo);
[ split; [exact HP|]; rewrite unsigned_lit by (unfold spf; lia);
split; [exact ST|]; split; [exact LO|]; split; [unfold put_stk_P, spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR|]; split; [reflexivity | rewrite unsigned_lit by lia; exact Hret2]
| exact RR | exact I | reflexivity |].
intros ms' md' m' rv (RS & VM' & ST' & HPR' & [errv' ERR']) _ ERRx [A' HP'].
destruct RS as (xt0 & xt1 & xt2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & xt3 & xt4 & xt5 & xt6 & F' & fc' & -> & FS' & FRM').
cbn [hl_segs hl_tp S4L] in ST', HPR', ERRx, HP' |- *. rewrite unsigned_lit in ST', HPR' by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia | exact Hret2]).
eapply KQ; [exact VM' | exact FS' | exact FRM' | exact ST' | exact HPR' | exact ERRx | exact HP'].
Qed.

#[using="lo LB m0 md0 F0 ra0 s0v s1v data0 size payload LO LOS SZ D0 INB DLO"] Lemma presxD_eq : forall LBx m m' a,
heap_presxD S4L (spf + 8) LBx spf m m' ->
(forall b, In b LBx -> 0 <= snd b /\ fst b + snd b <= alloc_ceiling) ->
0 <= a < 2^64 ->
((spf <= a < spf + 8 \/ spf + 16 <= a) \/ (s4_client_static a /\ ~ s4_volatile a) \/ in_block LBx a) ->
m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).
Proof.
intros LBx m m' a HPD BLK Ha Hc. unfold TGT_STACK in LOS. apply (HPD a Ha).
- destruct Hc as [Hc | [Hc | Hc]]; [left; unfold spf in *; lia | right; left; exact Hc | right; right; exact Hc].
- destruct Hc as [Hc | [[Hc _] | (b & Hb & Hr)]]; [unfold spf in *; lia | |].
+ pose proof (hl_static_in_img S4L a Hc) as Hi. cbn in Hi. unfold spf. clia.
+ destruct b as [ba bn]. destruct (BLK _ Hb) as [Hn Hhi]. cbn in Hn, Hhi, Hr. unfold spf. clia.
Qed.

#[using="lo m0 md0 F0 ra0 s0v s1v data0 size payload LO LOS SZ D0 INB DLO"] Lemma presxD_presx : forall LBx m m',
heap_presxD S4L (spf + 8) LBx spf m m' ->
(forall b, In b LBx -> 0 <= snd b /\ fst b + snd b <= alloc_ceiling) -> incl LB LBx ->
heap_presx S4L (xtgt S4L) LB sp0 m m'.
Proof.
intros LBx m m' HPD BLK Hi a Ha Hc. eapply presxD_eq; [exact HPD | exact BLK | exact Ha |].
destruct Hc as [Hc | [[Hc Hx] | (b & Hb & Hr)]].
- left. unfold spf. lia.
- right; left. split; [exact Hc|]. intros V. apply Hx. left. exact V.
- right; right. exists b. split; [apply Hi; exact Hb | exact Hr].
Qed.

#[using="lo LB m0 md0 F0 ra0 s0v s1v data0 size payload LO LOS SZ D0 INB DLO"] Lemma presxD_rw_cells : forall LBx m m' A cs,
heap_presxD S4L (spf + 8) LBx spf m m' ->
(forall b, In b LBx -> 0 <= snd b /\ fst b + snd b <= alloc_ceiling) ->
rw_cells rsegs m A cs ->
((spf <= A /\ A + Z.of_nat (cells_size cs) <= spf + 8) \/ spf + 16 <= A \/ (forall a, A <= a < A + Z.of_nat (cells_size cs) -> s4_client_static a /\ ~ s4_volatile a)) ->
A + Z.of_nat (cells_size cs) <= 2^64 ->
rw_cells rsegs m' A cs.
Proof.
intros LBx m m' A cs HPD BLK RW HA Hhi. pose proof (rw_cells_bound _ _ _ _ RW) as B0.
eapply rw_cells_pointwise; [exact RW|]. intros a Ha. eapply presxD_eq; [exact HPD | exact BLK | lia |].
destruct HA as [HA | [HA | HA]]; [left; lia | left; lia | right; left; apply HA; exact Ha].
Qed.

#[using="lo LB m0 md0 F0 ra0 s0v s1v data0 size payload LO LOS SZ D0 INB DLO"] Lemma presxD_hglob : forall LBx m m',
heap_presxD S4L (spf + 8) LBx spf m m' ->
(forall b, In b LBx -> 0 <= snd b /\ fst b + snd b <= alloc_ceiling) ->
hglob_P m -> jc_glob_P m' -> hglob_P m'.
Proof.
intros LBx m m' HPD BLK [[_ [U8 GF]] (J1 & J2 & J3 & J4)] JG'.
assert (E : forall a, (0x63d78 <= a < 0x63d90 \/ 0x64ee0 <= a < 0x64ee3 \/ 0x60918 <= a < 0x60920 \/ 0x63c50 <= a < 0x63c58) -> m' (wa a) = m (wa a)).
{ intros a Ha. eapply presxD_eq; [exact HPD | exact BLK | lia |]. right; left. cbn. unfold s4_client_static, s4_volatile. lia. }
split; [split; [exact JG' | split]|].
- eapply bytes_at_pointwise; [exact U8|]. intros a Ha. unfold UTF8REP_ADDR in Ha. cbn in Ha. apply E. lia.
- eapply bytes_at_pointwise; [exact GF|]. intros a Ha. unfold GOT_free_userdata in Ha. rewrite length_le8 in Ha. apply E. lia.
- unfold jox_P, JO_SDTBL_P, JO_LCONV_P, JO_GOTUDS_P, JO_GOTSCF_P in *.
split; [| split; [| split]]; (eapply bytes_at_pointwise; [eassumption|]); intros a Ha; rewrite length_le8 in Ha; apply E; lia.
Qed.

Ltac permx := cbv delta [blk]; perm; try (apply Permutation_sym; apply Permutation_middle); try apply Permutation_middle.

Section Tail.
Variable p : Z.
Notation sstatec := (sstate sp0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p).

#[using="DEEP PUT PUTX fc0 payload LO LOS SPA HT HT62 SZ D0 INB DLO K"] Lemma seg_tail : forall m md (A : AS S4L HIx) F fc errv ptr rem data r BS LK
(x1 gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
SINVc p m md A F fc errv ptr rem data r BS LK ->
(exists (n : Z) (sj23 : list byte), 0 <= n <= 10 /\ rw_cells rsegs m (spf + 16) [C1 (Z_to_bv 8 (2 * n)); CB 23 sj23]) ->
realizes rsegs (mkCfg (sstatec x1 gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x21118 fc m) md) T.
Proof.
intros m md A F fc errv ptr rem data r BS LK x1 gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SI (n & sj23 & Hn & STRs).
pose proof SI as ((PX & VM & FS & FRM & LOC & LCK & G & ST & SAV & ERR & [j16 SCR] & [sj STR] & FD & PP & D1 & D2 & R0) & HP & RR & RD).
clear STR. pose proof FD as (FDc & B & L & P0 & P1). clear B.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof spf16'' as SPF16. unfold hsave in SAV. unfold TGT_STACK in LOS. unfold sstate. unfold_consts.
unfold LOCCELL in LOC. cbn in LOC. unfold LOCALE_LOCK in LCK.
pose proof G as [[JG _] (J1 & J2 & J3 & J4)]. unfold JO_GOTSCF_P, JO_GOTSCF_VAL_P in J4.
pose proof (munch_refl [(spf + 8, spf + 16)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
assert (BLK : forall a k, In (a, k) (BS ++ LK ++ LB) -> 0 <= k /\ 0 < a /\ a + k <= alloc_ceiling).
{ intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP Hin) as (Hk & _ & Hlo & Hhi & _). lia. }
apply rz_evt; [exact MOK|].
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (bytes_at_read rsegs mX 0x63d88 _ 0 8 J4 ltac:(lia) ltac:(rewrite length_le8; lia)) as RDG; rename mX into m1 end.
change (Z.to_nat 0) with 0%nat in RDG. rewrite skipn_O in RDG. rewrite firstn_all2 in RDG by (rewrite length_le8; lia). replace (0x63d88 + 0) with 0x63d88 in RDG by lia.
step. step. rewrite ?load_u64. step. step. step. fold_mkR.

match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
assert (HP1 : HEAPx A (BS ++ LK ++ LB) m1 md) by (heap_now S4L HIx HP MU WM MI1).
assert (G1 : hglob_P m1) by (eapply hglob_P_outside; [exact G | exact MU | exact WM | apply Forall_cons; [cbn; right; unfold spf; clia | apply Forall_nil]]).
assert (PX1 : heap_presx S4L (xtgt S4L) LB sp0 m0 m1).
{ eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munchx; [exact MU | exact WM |].
eapply (client_outsidex HIx); [exact HP | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [left; cbn; unfold spf; clia | apply Forall_nil]. }
assert (RR1 : jroot_rep S4L S4F r m1 BS p).
{ eapply (jroot_rep_agree S4L S4F); [exact RR | | apply incl_refl]. eapply agree_of_munch; [exact MU | exact WM |].
intros a k Hin. destruct (BLK a k ltac:(apply in_or_app; left; exact Hin)) as (Hk & _ & Hhi). cbn. unfold spf. clia. }
assert (ST1 : stk rsegs m1 lo spf) by (first [exact ST | eapply stk_transport_disjoint; [exact ST | exact MU | exact WM | cbn; lia]]).
apply rw_cells_app with (cs1 := [_]) in SCR as [SCR0 DC]. cbn [cells_size csize Nat.add] in DC.
change (spf + Z.of_nat 8) with (spf + 8) in DC.
clear MU WM HP G PX RR ST RDG.

apply evt_RZ_done.
pose proof (DEEP HT62) as DP. unfold jo_deep_copy_stmt, DC_STK0_P, DC_STK1_P in DP.
eapply DP with (A := A) (BS := BS) (LB := LK ++ LB) (r := r) (lo := lo) (D := spf + 8);
[ split; [exact HP1|]; rewrite unsigned_lit by (unfold spf; lia);
split; [exact ST1|]; split; [exact LO|]; split; [unfold spf; lia|]; split; [exact SPF16|]; split; [unfold spf; lia|];
split; [exact ERR|]; split; [reflexivity | vm_compute; reflexivity]
| exact (proj1 (proj1 G1)) | exact RR1 | exact DC | rewrite unsigned_lit by (unfold spf; lia); unfold spf; lia
| unfold spf; lia | unfold spf; lia | unfold spf; destruct (proj1 (Z.mod_divide sp0 16 ltac:(lia)) SPA) as [k Hk]; apply Z.mod_divide; [lia|]; exists (2 * k - 9); lia
| exact FRM | reflexivity | apply bv_eq; rewrite !unsigned_lit by (unfold spf; lia); unfold spf; lia | reflexivity |].
intros ms2 md2 m2 rv (RS2 & VM2 & ST2 & HPD2 & [errv2 ERR2]) JG2 RR2 OUT2.
destruct RS2 as (yt0 & yt1 & yt2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in ST2, HPD2, ERR2, RR2, OUT2 |- *. rewrite unsigned_lit in ST2, HPD2 by (unfold spf; lia).
replace (ret_pc (Z_to_bv 64 0x21130)) with (Z_to_bv 64 0x21130 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (COMMON : forall (A2 : AS S4L HIx) (d : jroot) (q : Z) (CBS REM : list blk),
HEAPx A2 (BS ++ CBS ++ REM ++ LK ++ LB) m2 md2 ->
rw_cells rsegs m2 (spf + 8) [C8 (Z_to_bv 64 q)] -> jroot_rep S4L S4F d m2 CBS q ->
realizes rsegs (mkCfg (MS (mkR (Z_to_bv 64 0x21130) (Z_to_bv 64 spf) gp (Z_to_bv 64 0x75e70) yt0 yt1 yt2 (Z_to_bv 64 p) s1 (Z_to_bv 64 rv) ya1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 yt3 yt4 yt5 yt6)
F2 (Z_to_bv 64 0x21130) fc2 None m2 (seg_rom rsegs)) md2) T).
2:{ destruct OUT2 as [(-> & A2 & d & q & CBS & REM & CP & Hq & DC2 & RRd & HP2) | (-> & A2 & REM & DC2 & HP2)].
- eapply (COMMON A2 d q CBS REM); [| exact DC2 | exact RRd]. eapply (heap_perm S4L HIx); [exact HP2 | permx].
- eapply (COMMON A2 JRnull 0 [] REM); [| exact DC2 | split; reflexivity]. eapply (heap_perm S4L HIx); [exact HP2 | permx]. }
intros A2 d q CBS REM HP2 DC2 RRd.
assert (BLK2 : forall b, In b (BS ++ CBS ++ REM ++ LK ++ LB) -> 0 <= snd b /\ fst b + snd b <= alloc_ceiling).
{ intros [a k] Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP2 Hin) as (Hk & _ & Hlo & Hhi & _). cbn. lia. }
assert (BLK2' : forall b, In b (LK ++ LB) -> 0 <= snd b /\ fst b + snd b <= alloc_ceiling).
{ intros b Hb. apply BLK2. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI2. cbn [hl_segs S4L] in MI2.

assert (SAV2 : rw_cells rsegs m2 (spf + 56) [C8 s1v; C8 s0v; C8 ra0]) by (eapply presxD_rw_cells; [exact HPD2 | exact BLK2' | exact SAV | right; left; lia | cbn; unfold spf; lia]).
assert (STR2 : rw_cells rsegs m2 (spf + 16) [C1 (Z_to_bv 8 (2 * n)); CB 23 sj23]) by (eapply presxD_rw_cells; [exact HPD2 | exact BLK2' | exact STRs | right; left; lia | cbn; unfold spf; lia]).
assert (FD2 : rw_cells rsegs m2 (spf + 40) [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)]) by (eapply presxD_rw_cells; [exact HPD2 | exact BLK2' | exact FDc | right; left; lia | cbn; unfold spf; lia]).
assert (SCR2 : rw_cells rsegs m2 spf [CB 8 (firstn 8 j16)]) by (eapply presxD_rw_cells; [exact HPD2 | exact BLK2' | exact SCR0 | left; cbn; lia | cbn; unfold spf; lia]).
assert (LOC2 : rw_cells rsegs m2 LOCCELL [C8 (Z_to_bv 64 GLOBLOC)]) by (unfold LOCCELL; eapply presxD_rw_cells; [exact HPD2 | exact BLK2' | exact LOC | right; right; cbn; unfold s4_client_static, s4_volatile; intros; lia | cbn; lia]).
assert (G2 : hglob_P m2) by (eapply presxD_hglob; [exact HPD2 | exact BLK2' | exact G1 | exact JG2]).
assert (PX2 : heap_presx S4L (xtgt S4L) LB sp0 m0 m2).
{ eapply heap_presx_trans; [exact PX1|]. eapply presxD_presx; [exact HPD2 | exact BLK2' | intros b Hb; apply in_or_app; right; exact Hb]. }
clear SAV STRs FDc SCR0 LOC LCK DC HPD2 HP1 G1 PX1 RR1 ST1 MI1 ERR.
apply rz_evt; [exact MOK2|].
pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
step. step. fold_mkR. apply evt_RZ_done.

eapply (put_any 0x21138 d q m2 md2 A2 CBS (BS ++ REM ++ LK ++ LB) errv2);
[lia | reflexivity | eapply (heap_perm S4L HIx); [exact HP2 | permx] | exact RRd | exact ST2 | exact ERR2 |
| match goal with |- ?g => idtac "PUTANY" g end; fail ..].
clear MU WM.
intros m3 md3 A3 F3 fc3 errv3 zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 VM3 FS3 FRM3 ST3 HPR3 ERR3 HP3.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3. pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
assert (RR3 : jroot_rep S4L S4F r m3 BS p).
{ eapply (jroot_rep_agree S4L S4F); [exact RR2 | | apply incl_refl].
eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb]. }
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in SAV2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in STR2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FD2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in SCR2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in DC2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in LOC2; [| right; left; unfold LOCCELL; cbn; unfold s4_client_static; intros; lia].
cbn [hl_segs S4L] in SAV2, STR2, FD2, SCR2, DC2, LOC2.
assert (G3 : hglob_P m3) by (eapply hglob_P_pres; [exact HPR3 | exact G2]).
assert (PX3 : heap_presx S4L (xtgt S4L) LB sp0 m0 m3).
{ eapply heap_presx_trans; [exact PX2|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR3 | unfold spf; lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb]. }
apply rz_evt; [exact MOK3|].
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
step. step. fold_mkR. apply evt_RZ_done.

eapply (put_any 0x21140 r p m3 md3 A3 BS (REM ++ LK ++ LB) errv3);
[lia | reflexivity | exact HP3 | exact RR3 | exact ST3 | exact ERR3 |].
clear MU WM.
intros m4 md4 A4 F4 fc4 errv4 wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 VM4 FS4 FRM4 ST4 HPR4 ERR4 HP4.
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4. pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L] in MI4.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in SAV2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in STR2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in FD2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in SCR2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in DC2; [| left; cbn; unfold spf; lia].
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR4) in LOC2; [| right; left; unfold LOCCELL; cbn; unfold s4_client_static; intros; lia].
cbn [hl_segs S4L] in SAV2, STR2, FD2, SCR2, DC2, LOC2.
assert (G4 : hglob_P m4) by (eapply hglob_P_pres; [exact HPR4 | exact G3]).
assert (PX4 : heap_presx S4L (xtgt S4L) LB sp0 m0 m4).
{ eapply heap_presx_trans; [exact PX3|]. apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR4 | unfold spf; lia | intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb]. }

apply rz_evt; [exact MOK4|].
pose proof (munch_refl (@nil (Z * Z)) m4) as MU. pose proof (wmono_refl rsegs m4) as WM.
step. step. rewrite short_flag0 by lia. step. try if_true. step. step. step. step.

assert (FRALL : rw_cells rsegs m4 spf ([CB 8 (firstn 8 j16)] ++ [C8 (Z_to_bv 64 q)] ++ [C1 (Z_to_bv 8 (2 * n)); CB 23 sj23] ++ [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] ++ [C8 s1v; C8 s0v; C8 ra0])).
{ apply (proj2 (rw_cells_app rsegs m4 _ _ _)). split; [exact SCR2|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app rsegs m4 _ _ _)). split; [change (spf + Z.of_nat 8) with (spf + 8); exact DC2|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app rsegs m4 _ _ _)). split; [change (spf + Z.of_nat 8 + Z.of_nat 8) with (spf + 8 + 8); replace (spf + 8 + 8) with (spf + 16) by lia; exact STR2|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app rsegs m4 _ _ _)). split; [change (spf + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24) with (spf + 8 + 8 + 24); replace (spf + 8 + 8 + 24) with (spf + 40) by lia; exact FD2|]. cbn [cells_size csize Nat.add].
change (spf + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 24 + Z.of_nat 16) with (spf + 8 + 8 + 24 + 16). replace (spf + 8 + 8 + 24 + 16) with (spf + 56) by lia. exact SAV2. }
cbn [app] in FRALL. clear SCR2 DC2 STR2 FD2 SAV2.
release_frame FRALL ST4 sp0.
step. step. fold_mkR.
apply evt_RZ_done.
replace (spf + 80) with sp0 by (unfold spf; lia).
eapply (K _ m4 md4 A4 errv4 gp (REM ++ LK)).
- apply ret_statew_intro.
+ eapply fsaved_trans; [exact FS|]. eapply fsaved_trans; [exact FS2|]. eapply fsaved_trans; [exact FS3 | exact FS4].
+ intros _. exact (FRM4 (FRM3 (FRM2 FRM))).
- eapply model_vm_only_trans; [exact VM|]. eapply model_vm_only_trans; [exact VM2|]. eapply model_vm_only_trans; [exact VM3 | exact VM4].
- exact ST4.
- exact PX4.
- exact LOC2.
- exact ERR4.
- exact G4.
- eapply (heap_perm S4L HIx); [exact HP4 | permx].
Qed.
End Tail.

Local Ltac feed_hyps2 t :=
lazymatch type of t with
| forall _ : ?A, _ => first [ feed_hyps2 (t GETB) | feed_hyps2 (t GETD) | feed_hyps2 (t GETI) | feed_hyps2 (t GETI64) | feed_hyps2 (t GETU64) | feed_hyps2 (t GETS) | feed_hyps2 (t GETS0) | feed_hyps2 (t GETSL) | feed_hyps2 (t GETO) | feed_hyps2 (t GETA) | feed_hyps2 (t GETT) | feed_hyps2 (t VISIT) | feed_hyps2 (t SETI) | feed_hyps2 (t SETI64) | feed_hyps2 (t SETU64) | feed_hyps2 (t SETB) | feed_hyps2 (t SETD) | feed_hyps2 (t CFP) | feed_hyps2 (t CRLS) | feed_hyps2 (t SETS) | feed_hyps2 (t SETSL) | feed_hyps2 (t TOKPARSE) | feed_hyps2 (t DEEP) | feed_hyps2 (t PUT) | feed_hyps2 (t PUTX) | feed_hyps2 (t LO) | feed_hyps2 (t LOS) | feed_hyps2 (t SPA) | feed_hyps2 (t HT) | feed_hyps2 (t HT62) | feed_hyps2 (t RA0) | feed_hyps2 (t FRM0) | feed_hyps2 (t PLEN) | feed_hyps2 (t SZ) | feed_hyps2 (t D0) | feed_hyps2 (t DSZ) | feed_hyps2 (t INB) | feed_hyps2 (t DLO) | feed_hyps2 (t K) | exact t ]
| _ => exact t
end.
Let seg_gettersc := ltac:(feed_hyps2 (seg_getters HIx GETB GETD GETI GETI64 GETU64 GETS GETS0 GETSL GETO GETA GETT VISIT sp0 lo LB m0 md0 F0 ra0 s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 T data0 size payload)).
Let seg_settersc := ltac:(feed_hyps2 (seg_setters HIx SETI SETI64 SETU64 SETB SETD CFP CRLS SETS SETSL sp0 lo LB m0 md0 F0 ra0 s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 T data0 size payload)).

#[using="HIx GETB GETD GETI GETI64 GETU64 GETS GETS0 GETSL GETO GETA GETT VISIT SETI SETI64 SETU64 SETB SETD CFP CRLS SETS SETSL sp0 lo LB m0 md0 F0 ra0 s0v s1v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 T data0 size payload spf LO LOS SPA HT HT62 SZ D0 INB DLO"] Lemma jox_presx : forall X LBx SP m m',
heap_presx S4L X LBx SP m m' -> (forall a, X a -> s4_volatile a \/ LOCCELL <= a < LOCCELL + 8) -> jox_P m -> jox_P m'.
Proof.
intros X LBx SP m m' HPX HX (J1 & J2 & J3 & J4). unfold jox_P, JO_SDTBL_P, JO_LCONV_P, JO_GOTUDS_P, JO_GOTSCF_P in *.
assert (E : forall a, (0x60918 <= a < 0x60920 \/ 0x63c50 <= a < 0x63c58 \/ 0x63d80 <= a < 0x63d90) -> m' (wa a) = m (wa a)).
{ intros a Ha. apply (HPX a); [lia|]. right; left. split; [cbn; unfold s4_client_static; lia|].
intros Xa. destruct (HX a Xa) as [V|V]; [unfold s4_volatile in V; lia | unfold LOCCELL in V; lia]. }
split; [| split; [| split]]; (eapply bytes_at_pointwise; [eassumption|]); intros a Ha; rewrite length_le8 in Ha; apply E; lia.
Qed.

#[using="GETB GETD GETI GETI64 GETU64 GETS GETS0 GETSL GETO GETA GETT VISIT SETI SETI64 SETU64 SETB SETD CFP CRLS SETS SETSL TOKPARSE DEEP PUT PUTX spf LO LOS SPA HT HT62 FRM0 PLEN SZ D0 DSZ INB DLO K HINV_callc seg_gettersc seg_settersc"] Lemma harness_run : forall (gp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (A : AS S4L HIx) (errv : word),
HEAPx A LB m0 md0 ->
bytes_at rsegs m0 data0 payload ->
rw_cells rsegs m0 LOCCELL [C8 (Z_to_bv 64 GLOBLOC)] -> rw_cells rsegs m0 LOCALE_LOCK [C4 (Z_to_bv 64 0)] -> hglob_P m0 ->
stk rsegs m0 lo sp0 -> rw_cells rsegs m0 (0x75e70 - 164) [C4 errv] ->
realizes rsegs (mkCfg (MS (mkR ra0 (Z_to_bv 64 sp0) gp (Z_to_bv 64 0x75e70) t0 t1 t2 s0v s1v (Z_to_bv 64 data0) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F0 (Z_to_bv 64 0x20e60) fc0 None m0 (seg_rom rsegs)) md0) T.
Proof.
intros gp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 A errv HP PAY LOC LCK G ST ERR.
unfold TGT_STACK in LOS. unfold_consts. pose proof spf16'' as SPF16.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK. pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m0) as WM. pose proof (munch_refl [(lo, sp0)] m0) as MU.
assert (BLK : forall a k, In (a, k) LB -> 0 <= k /\ 0 < a /\ a + k <= alloc_ceiling).
{ intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP Hin) as (Hk & _ & Hlo & Hhi & _). lia. }
assert (PAYk : forall mx, munch [(lo, sp0)] m0 mx -> bytes_at rsegs mx data0 payload).
{ intros mx MUx. eapply bytes_at_transport; [exact PAY | exact MUx | cbn; clia]. }
clear PAY. unfold LOCCELL, LOCALE_LOCK in LOC, LCK. cbn in LOC.
pose proof G as [[JG [U8 GF]] JOX]. stash G. stash JOX. stash U8. stash GF.
apply rz_evt; [exact MOK|].
step. change (sp0 + -80) with (sp0 - 80) in *.
carve_frame 80%nat ST.
step. step. step. step. step. fold_mkR.

lazymatch type of FR with rw_cells _ ?mX _ (CB 40 ?j :: ?rest) =>
pose proof (rw_cells_CB_cut rsegs mX (sp0 - 80) 40 j 16 ltac:(apply (proj1 (rw_cells_app rsegs mX (sp0 - 80) [CB 40 j] rest)) in FR as [FRh _]; exact FRh) ltac:(lia)) as [SCR STR];
apply (proj1 (rw_cells_app rsegs mX (sp0 - 80) [CB 40 j] rest)) in FR as [_ FR2] end.
cbn [cells_size csize Nat.add] in FR2. change (Z.of_nat 40) with 40 in FR2. change (Z.of_nat 16) with 16 in STR. change (40 - 16)%nat with 24%nat in STR.
lazymatch type of FR2 with rw_cells _ ?mX _ (?c1 :: ?c2 :: ?rest) =>
change (rw_cells rsegs mX (sp0 - 80 + 40) ([c1; c2] ++ rest)) in FR2 end.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FR2 as [FD SAV]. cbn [cells_size csize Nat.add] in SAV. change (Z.of_nat 16) with 16 in SAV.
replace (sp0 - 80 + 40 + 16) with (sp0 - 80 + 56) in SAV by lia.
step. step. step. step. fold_mkR.

pose proof CRLS as CR. unfold crls_stmt, crls_post, crls_W, CRLS_FRAME_P in CR.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m1 end.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
eapply evt_cut.
{ eapply (CR _ (Z_to_bv 64 (sp0 - 80))) with (S := sp0 - 80 + 16) (P := sp0 - 80 + 40) (ptr := data0) (rem := size) (lo := lo) (maxlen := 20) (data := payload);
[ f_equal; lia | f_equal; lia | reflexivity | lia | exact STR | exact FD | apply PAYk; exact MU | exact PLEN | lia
| rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; lia | lia | rewrite unsigned_lit by lia; clia | exact MI1 ]. }
intros ms' (yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & yt3 & yt4 & yt5 & yt6 & m2 & n & k & str & rest & -> & MU2 & WM2 & MI2 & Hn & Hstr & NONUL & STR2 & Hk & FD2 & B2 & ST2).
rewrite unsigned_lit in ST2, MU2 by lia.
replace (ret_pc (Z_to_bv 64 0x20e88)) with (Z_to_bv 64 0x20e88 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).

assert (MU02 : munch [(lo, sp0)] m0 m2).
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn. intros x Hx. lia. }
pose proof (wmono_trans _ _ _ _ WM WM2) as WM02.
eapply rw_cells_transport in SAV; [| exact MU2 | exact WM2 | cbn; lia].
eapply rw_cells_transport in SCR; [| exact MU2 | exact WM2 | cbn; lia].
eapply rw_cells_transport in LOC; [| exact MU2 | exact WM2 | cbn; lia].
eapply rw_cells_transport in LCK; [| exact MU2 | exact WM2 | cbn; lia].
eapply rw_cells_transport in ERR; [| exact MU2 | exact WM2 | cbn; lia].
clear MU WM STR FD MI1.
assert (HP2 : HEAPx A LB m2 md0) by (heap_now S4L HIx HP MU02 WM02 MI2).
unstash G. assert (G2 : hglob_P m2) by (eapply hglob_P_outside; [exact G | exact MU02 | exact WM02 | apply Forall_cons; [cbn; lia | apply Forall_nil]]).
assert (PX2 : heap_presx S4L (xtgt S4L) LB sp0 m0 m2).
{ eapply heap_presx_of_munchx; [exact MU02 | exact WM02 |].
eapply (client_outsidex HIx); [exact HP | intros b Hb; exact Hb | clia | apply Forall_cons; [left; cbn; clia | apply Forall_nil]]. }

step. step. rewrite short_flag0 by lia. step. try if_true. step. step. fold_mkR.

pose proof STR2 as STRB. apply rw_cells_app with (cs1 := [_]) in STRB as [_ STRB]. cbn [cells_size csize Nat.add] in STRB.
pose proof (rw_cells_bytes_at rsegs m2 _ _ STRB) as SB. cbn [cells_bytes cbytes app] in SB. rewrite app_nil_r in SB.
change (sp0 - 80 + 16 + Z.of_nat 1) with (sp0 - 80 + 16 + 1) in SB.
replace (str ++ Z_to_bv 8 0 :: rest) with ((str ++ [Z_to_bv 8 0]) ++ rest) in SB by (rewrite <- app_assoc; reflexivity).
apply bytes_at_app in SB as [SB0 SBR]. rewrite length_app in SBR. cbn [length] in SBR.
assert (LREST : Z.of_nat (length rest) = 22 - Z.of_nat (length str)).
{ destruct STR2 as [[WF _] _]. cbn in WF. rewrite length_app in WF. cbn [length] in WF. lia. }
pose proof (Z.mod_pos_bound (- (sp0 - 80 + 16 + 1 + Z.of_nat (length str) + 1)) 8 ltac:(lia)) as MB.
pose proof G2 as [[JG2 [U82 GF2]] JOX2].
pose proof TOKPARSE as TP'. unfold tokparse_stmt_P, tokparse_stmt in TP'.
apply evt_RZ_done.
eapply TP' with (sb := sp0 - 80 + 16 + 1) (str0 := str) (slack := rest) (lo := lo) (LBc := LB);
[ exact HP2 | exact SB0 | exact NONUL | lia
| replace (sp0 - 80 + 16 + 1 + Z.of_nat (length str) + 1) with (sp0 - 80 + 16 + 1 + Z.of_nat (length str + 1)) by lia; exact SBR
| lia | rewrite unsigned_lit by lia; lia | lia
| cbn [tokparse_statics tpc_LOCC tpc_GLOBL tpc_LOCK tpc_G tpc_UTF8A tpc_GOTA tpc_GOTV tokparse_consts_P];
split; [exact LOC | split; [exact LCK | split; [exact JG2 | split; [exact U82 | exact GF2]]]]
| rewrite unsigned_lit by lia; exact ST2 | exact LO | rewrite unsigned_lit by lia; cbn [tpc_stk tokparse_consts_P]; unfold TOKPARSE_STK_P; lia
| rewrite unsigned_lit by lia; exact SPF16 | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact ERR | reflexivity | vm_compute; reflexivity | exact FRM0 | f_equal; lia | ].
intros ms3 md3 (m3 & A3 & gp3 & r & errv3 & RBS & LK3 & RS3 & VM3 & ST3 & ERR3 & STAT3 & PX3 & HP3 & RES3).
destruct RS3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F3 & fc3 & -> & FS3 & FRM3).
cbn [hl_segs hl_tp S4L tpc_X tokparse_consts_P] in ST3, ERR3, PX3, HP3, RES3, STAT3 |- *. rewrite unsigned_lit in ST3, PX3 by lia.
replace (ret_pc (Z_to_bv 64 0x20ea4)) with (Z_to_bv 64 0x20ea4 : word) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
destruct STAT3 as (LOC3 & LCK3 & JG3 & U83 & GF3).
cbn [tpc_LOCC tpc_GLOBL tpc_LOCK tpc_G tpc_UTF8A tpc_GOTA tpc_GOTV tokparse_consts_P] in LOC3, LCK3, JG3, U83, GF3.
assert (XX : forall a, ja_xloc_P a -> s4_volatile a \/ LOCCELL <= a < LOCCELL + 8) by (intros a Ha; exact Ha).
assert (G3 : hglob_P m3).
{ split; [split; [exact JG3 | split; [exact U83 | exact GF3]]|]. eapply jox_presx; [exact PX3 | exact XX | exact JOX2]. }
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ PX3) in SAV; [| left; cbn; lia].
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ PX3) in SCR; [| left; cbn; lia].
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ PX3) in STR2; [| left; cbn; lia].
apply (heap_presx_rw_cells S4L _ _ _ _ _ _ _ PX3) in FD2; [| left; cbn; lia].
cbn [hl_segs S4L] in SAV, SCR, STR2, FD2.
assert (B3 : bytes_at rsegs m3 data0 payload).
{ eapply (window_bytes sp0 LB ra0 data0 size payload SZ D0 INB DLO m2 m3 data0 size payload); [exact B2 | exact PLEN | lia | lia | lia |].
intros a Ha (b & Hb & Hr). apply (PX3 a Ha). right; right. exists b. split; [exact Hb | exact Hr]. }
assert (PX03 : heap_presx S4L (xtgt S4L) LB sp0 m0 m3).
{ eapply heap_presx_trans; [exact PX2|]. eapply heap_presx_weaken; [exact PX3 | lia | intros b Hb; exact Hb |].
intros a Ha. unfold ja_xloc_P, xtgt, T_LOCCELL, LOCCELL in *. cbn [hl_volatile hl_tp S4L] in *. exact Ha. }
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3. pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI3. cbn [hl_segs S4L] in MI3.
assert (Rr : 0 <= r < 2^64).
{ destruct RES3 as [[-> _] | (NZ & s & Js & _)]; [lia|].
destruct (jval_root_in rsegs S4F s m3 RBS r 1 Js) as (nr & INr & Hnr).
pose proof (heap_blk S4L HIx _ _ _ _ r nr HP3 ltac:(apply in_or_app; left; exact INr)) as (_ & _ & Hrlo & Hrhi & _). clia. }
apply rz_evt; [exact MOK3|].
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
step. step. step. rewrite short_flag0 by lia. step. try if_true. fold_mkR.

assert (STR3 : rw_cells rsegs m3 (sp0 - 80 + 16) [CB 24 (Z_to_bv 8 (2 * n) :: str ++ Z_to_bv 8 0 :: rest)]).
{ eapply rw_cells_recast; [exact STR2 | | cbn; rewrite ?app_nil_r; reflexivity | reflexivity].
destruct STR2 as [[WF _] _]. cbn in WF |- *. rewrite length_app in *. cbn [length] in *. lia. }
pose proof B3 as B3k. rewrite <- (firstn_skipn (Z.to_nat k) payload) in B3k. apply bytes_at_app in B3k as [_ B3k].
rewrite firstn_length_le in B3k by lia. rewrite Z2Nat.id in B3k by lia.
assert (INV3 : HINVc m3 md3 F3 fc3 errv3 (data0 + k) (size - k) (skipn (Z.to_nat k) payload)).
{ cbn [hl_segs S4L] in LOC3, LCK3.
apply (HINV_intro sp0 lo LB m0 md0 F0 ra0 s0v s1v data0 size m3 md3 F3 fc3 errv3 (data0 + k) (size - k) (skipn (Z.to_nat k) payload) _ _
PX03 VM3 FS3 (FRM3 FRM0) LOC3 LCK3 G3 ST3 SAV ERR3 SCR STR3); [| lia | lia | lia | lia].
split; [exact FD2|]. split; [exact B3k|]. split; [rewrite length_skipn; lia | lia]. }
apply evt_RZ_done.
destruct RES3 as [[-> ->] | (NZ & s & Js & Ds)].
-
eapply (seg_gettersc 0) with (s := None) (BS := []) (LK := LK3); [split; [exact INV3 | split; [cbn [app] in HP3 |- *; exact HP3 | split; [split; reflexivity | cbn; lia]]]|].
unfold KG. intros m4 md4 A4 F4 fc4 errv4 ptr4 rem4 data4 BS4 LK4 z1 zg w0 w1 w2 q1 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 (INV4 & HP4 & [Hp4 EBS4] & OD4).
unfold gstate. eapply (seg_settersc 0) with (r := JRnull) (BS := BS4) (LK := LK4); [split; [exact INV4 | split; [exact HP4 | split; [split; [reflexivity | exact EBS4] | cbn; lia]]]|].
unfold KSF. intros m5 md5 A5 F5 fc5 errv5 ptr5 rem5 data5 BS5 LK5 x1 xg e0 e1 e2 p1 c0 c1 c2 c3 c4 c5 c6 c7 e3 e4 e5 e6 SI5 STR5.
eapply seg_tail; [exact SI5 | exact STR5].
-
eapply (seg_gettersc r) with (s := Some s) (BS := RBS) (LK := LK3); [split; [exact INV3 | split; [exact HP3 | split; [split; [exact NZ | exact Js] | cbn; lia]]]|].
unfold KG. intros m4 md4 A4 F4 fc4 errv4 ptr4 rem4 data4 BS4 LK4 z1 zg w0 w1 w2 q1 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 (INV4 & HP4 & [Hp4 J4] & OD4).
unfold gstate. eapply (seg_settersc r) with (r := JRtree s) (BS := BS4) (LK := LK4); [split; [exact INV4 | split; [exact HP4 | split; [split; [exact Hp4 | exact J4] | cbn in OD4 |- *; lia]]]|].
unfold KSF. intros m5 md5 A5 F5 fc5 errv5 ptr5 rem5 data5 BS5 LK5 x1 xg e0 e1 e2 p1 c0 c1 c2 c3 c4 c5 c6 c7 e3 e4 e5 e6 SI5 STR5.
eapply seg_tail; [exact SI5 | exact STR5].
Qed.
End Ctx.

#[using="GETB GETD GETI GETI64 GETU64 GETS GETS0 GETSL GETO GETA GETT VISIT SETI SETI64 SETU64 SETB SETD CFP CRLS SETS SETSL TOKPARSE DEEP PUT PUTX"] Theorem harness_P2 : target_stmt S4L HIx 0x20e60 hglob_P.
Proof.
unfold target_stmt. intros until errv. intros HP PAY PLEN SZ D0 DSZ DLO INB LOC LCK G ST LO LOS SPA HT HT62 ERR -> RA FRM -> -> K.
pose proof (bv_unsigned_in_range 64 sp) as SPR.
rewrite <- (Z_to_bv_bv_unsigned sp).
eapply (harness_run (bv_unsigned sp) lo LB m md F fc ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 T data size payload).
all: lazymatch goal with
| |- forall ms' : machine_state, _ =>
intros ms' m' md' A' errv' gp' LK RS VM ST' PX LOC' ERR' G' HP';
rewrite Z_to_bv_bv_unsigned in RS; eapply K; [exact RS | exact VM | exact ST' | exact PX | exact LOC' | exact ERR' | exact G' | exact HP']
| |- _ => first [eassumption | cbn [hl_segs hl_tp S4L] in *; eassumption]
end.
Qed.
End HarnJoP3.

End RC__1.
