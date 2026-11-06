(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qekr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qekr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC6R.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC6R. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpFy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpFy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q63E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q63E.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnmi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnmi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qaml.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qaml. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qaf2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qaf2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnX9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Ltac c1_bytes cs := lazymatch cs with | nil => constr:(@nil byte) | C1 ?b :: ?r => let r' := c1_bytes r in constr:(b :: r') end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AHarnJo5.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (tpB tpD : Z -> Z) (dcB dcD : Z -> Z) (gsS : jshape -> Z) (gsB : Z -> Z).
Hypothesis CA : jo_callees_A HIx tpB tpD dcB dcD gsS gsB.

Definition root_of (s : option jshape) : jroot := match s with Some s' => JRtree s' | None => JRnull end.

Definition dc_w (r : jroot) (w : Z) : Z := match r with JRtree _ => w | JRstrx => 62 | JRdblx _ => 9 | JRnull => 0 end.
Hypothesis TPC : forall n, 0 <= n <= 20 -> 0 <= tpB n /\ 0 <= tpD n.
Hypothesis GSC : forall sh, sdepth sh <= 32 -> gsS sh <= 2^20 - 144.
Hypothesis GBC : forall w, 0 <= w -> 0 <= gsB w.
Hypothesis DCC : forall w, 0 <= w -> 0 <= dcB w /\ 0 <= dcD w.

Hypothesis TOTAL : forall n s w BS, 0 <= n <= 20 -> odepth s <= 32 -> 0 <= w <= 26 * (n + 1) + 64 -> (forall sh, s = Some sh -> jtx sh BS = Some (w, [])) ->
tpB n + JO_GETDBL_COSTB_A + gsB w + 2912 + dcB (dc_w (setters_root (root_of s)) w) + (1024 + 192 * w) + (1024 + 192 * w) <= TGT_BB_A_jo /\
1 + tpD n + JO_GETDBL_COSTD_A + 5 + dcD (dc_w (setters_root (root_of s)) w) + 4 <= TGT_BD_A_jo.
Section Ctx.
Variables (sp0 : word) (sp1 lo Fr : Z) (LB0 LM : list blk) (m0 : word -> option byte) (md0 : config) (F0 : bvmap 5 word) (B0 : bud).
Variables (data0 size : Z) (payload : list byte).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= sp1 - (2^20 - 144).
Hypothesis SPA1 : sp1 mod 32 = 0.
Hypothesis SP10 : sp1 + 96 <= bv_unsigned sp0.
Hypothesis HT : bv_unsigned sp0 + 32 <= hiA_top A4L HIx.
Hypothesis HBOT : hiA_bot A4L HIx <= lo.
Hypothesis PLEN : Z.of_nat (length payload) = size.
Hypothesis SZ : 0 <= size < 2^26.
Hypothesis D0 : 0 < data0.
Hypothesis DCE : data0 + size <= alloc_ceiling.
Hypothesis INB : size = 0 \/ In (data0, size) LB0.
Hypothesis FRAL : Fr mod 512 = 0.
Hypothesis FRLO : 6582272 <= Fr.
Hypothesis FRHI : Fr + 512 <= alloc_ceiling.
Hypothesis FRAPP : Fr + 512 + 8 <= A_SB \/ A_HMB <= Fr.
Variables (p : Z) (s10 s11 : word) (T : TSet).
Hypothesis BB0 : TGT_BB_A_jo <= bB B0.
Hypothesis BD0 : TGT_BD_A_jo <= bD B0.
Collection CtxAll := RC__ HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB0 BD0.

Notation GINVAc := (GINVA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size p).
Notation SINVAc := (SINVA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size p).
Notation hstateAc := (hstateA sp0 sp1 Fr p s10 s11).
Let seg_gettersc := seg_gettersA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB0 BD0 tpB tpD dcB dcD gsS gsB CA.
Let seg_settersc := seg_settersA HIx tpB tpD dcB dcD gsS gsB CA sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB0 BD0.
Let seg_tailc := seg_tailA HIx tpB tpD dcB dcD gsS gsB CA sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB0 BD0.

#[using="CtxAll CA TPC GSC GBC DCC TOTAL seg_gettersc seg_settersc seg_tailc"] Lemma seg_bodyA : forall n s m md (A : ASA A4L HIx) B F fc ptr rem data BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
0 <= n <= 20 ->
(forall sh, s = Some sh -> exists w, jtx sh BS = Some (w, []) /\ w <= 26 * (n + 1) + 64) ->
GINVAc m md A B F fc ptr rem data s BS LK (tpB n) (1 + tpD n) ->
KTA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 s10 s11 T TGT_BB_A_jo TGT_BD_A_jo ->
AJ5 A4L HIx A T md (hstateAc x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x92058 fc m).
Proof.
intros n s m md A B F fc ptr rem data BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hn WT GI K.
pose proof GI as (_ & _ & _ & OD & _).
assert (WX : exists w, 0 <= w <= 26 * (n + 1) + 64 /\ (forall sh, s = Some sh -> jtx sh BS = Some (w, []))).
{ destruct s as [sh|].
- destruct (WT sh eq_refl) as (w & JTX & WLE). exists w. split; [split; [exact (jtx_nonneg _ _ _ _ JTX) | exact WLE] | intros sh' E; injection E as <-; exact JTX].
- exists 0. split; [lia | intros sh E; discriminate]. }
destruct WX as (w & WR & WJ).
destruct (TOTAL n s w BS Hn OD WR WJ) as [TB TD]. destruct (TPC n Hn) as [TP1 TP2]. pose proof (GBC w (proj1 WR)) as GB0.
set (r0 := root_of s) in *. set (r1 := setters_root r0) in *.
assert (RD0 : rdepth r0 <= 32) by (unfold r0, root_of; destruct s as [sh|]; cbn [rdepth odepth] in *; lia).
assert (RD1 : rdepth r1 <= 32).
{ unfold r1, setters_root. pose proof (rdepth_set_double_rootA (fn_dbl_to_json_string A4F) r0).
pose proof (rdepth_set_string_rootA (set_double_root (fn_dbl_to_json_string A4F) r0)).
pose proof (rdepth_set_string_rootA (set_string_root (set_double_root (fn_dbl_to_json_string A4F) r0))). lia. }
set (wdc := dc_w r1 w) in *.
assert (WDC : 0 <= wdc <= Z.max w 62) by (unfold wdc, dc_w; destruct r1; lia).
destruct (DCC wdc ltac:(lia)) as [DC1 DC2].

assert (PCC1 : forall d CBS mX q, copy_ofA r1 d CBS wdc -> jroot_rep A4H A4F d mX CBS q -> put_any_costB d CBS <= 1024 + 192 * w).
{ intros d CBS mX q [CO WD] RRd. destruct s as [sh0|]; [| cbn in CO; contradiction].
pose proof (jtx_blk_weight _ _ _ _ (WJ sh0 eq_refl)) as BW. pose proof (nnodes_le_nblk0 sh0) as NN.
unfold wdc, r1, r0, setters_root, root_of, dc_w in CO, WD.
destruct sh0 as [|u| |h|kids|kids]; cbn [set_double_root set_string_root copy_of] in CO, WD.
all: try (subst d; cbn [put_any_costB]; unfold JO_PUTX_COSTB_A; lia).
all: try (destruct CO as (s' & -> & _); destruct WD as (w' & JTX' & LE'); pose proof (jtx_blk_weight _ _ _ _ JTX') as BW'; pose proof (nnodes_le_nblk0 s') as NN';
destruct RRd as [_ J]; cbn [put_any_costB]; pose proof (jval_length_le asegs A4F _ _ _ _ _ J); lia).

subst d. destruct RRd as [_ J]. cbn [put_any_costB]. pose proof (jval_length_le asegs A4F _ _ _ _ _ J) as LE. destruct h; cbn [nblk0 nnodes] in LE, BW; lia. }

assert (PCR1 : forall BSx mX, jroot_rep A4H A4F r1 mX BSx p -> put_any_costB r1 BSx <= 1024 + 192 * w).
{ intros BSx mX RRx. destruct s as [sh0|]; [| cbn in RRx |- *; lia].
pose proof (jtx_blk_weight _ _ _ _ (WJ sh0 eq_refl)) as BW. pose proof (nnodes_le_nblk0 sh0) as NN.
assert (TREE : forall BSy, jval asegs A4F sh0 mX BSy p 1 -> 512 * Z.of_nat (length BSy) <= 1024 + 192 * w).
{ intros BSy J. pose proof (jval_length_le asegs A4F _ _ _ _ _ J). lia. }
unfold r1, r0, setters_root, root_of in RRx |- *.
destruct sh0 as [|u| |h|kids|kids]; cbn [set_double_root set_string_root put_any_costB] in RRx |- *; unfold JO_PUTX_COSTB_A; try lia;
(destruct RRx as [_ J]; exact (TREE _ J)). }
unfold JO_GETDBL_COSTB_A, JO_GETDBL_COSTD_A in *.
eapply seg_gettersc with (gc := gsB w); [exact GB0 | | | | exact GI |].
2: unfold JO_GETDBL_COSTB_A; lia.
2: unfold JO_GETDBL_COSTD_A; lia.
{ intros sh E. exists w. split; [exact (WJ sh E)|]. split; [lia|]. split; [apply GSC; subst s; exact OD | lia]. }
intros BS1 WJ1. unfold KGA. intros m1 md1 A1 B1 F1 fc1 ptr1 rem1 data1 LK1 y1 ygp yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 (HI1 & HP1 & JO1 & OD1 & BB1 & BD1).
assert (SI1 : SINVAc w SHB0 m1 md1 A1 B1 F1 fc1 ptr1 rem1 data1 r0 BS1 LK1 (tpB n + 512 + gsB w) (1 + tpD n + 0)).
{ split; [exact HI1|]. split; [exact HP1|]. split; [exact (jopt_jroot A4H A4F s m1 BS1 p JO1)|]. split; [exact RD0|]. unfold JO_GETDBL_COSTB_A, JO_GETDBL_COSTD_A in *.
split; [lia|]. split; [lia|].

unfold r0, root_of. destruct s as [sh0|]; [| exact I]. cbn [QpFy.rootWm]. exact (WJ1 sh0 w eq_refl (WJ sh0 eq_refl)). }
eapply seg_settersc; [exact SI1 | lia | lia |].
unfold KSFA. intros m2 md2 A2 B2 F2 fc2 ptr2 rem2 data2 BS2 LK2 z1 zgp zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 SI2 STR2 SLX2.
fold r1 in SI2, SLX2.

assert (RWA : root_wA r1 m2 BS2 p wdc).
{ pose proof SI2 as (_ & _ & _ & _ & _ & _ & RWm2). unfold wdc, dc_w. clear - RWm2 SLX2.
destruct r1 as [|s1|tj1|]; cbn [root_wA QpFy.rootWm] in RWm2 |- *.
- lia.
- destruct RWm2 as [PT JT]. exists w, (@nil blk), PT. rewrite app_nil_r. split; [exact JT | lia].
- lia.
- destruct (SLX2 eq_refl) as (n2 & Hn2 & SL2). exists n2. split; [exact SL2 | lia]. }
eapply (seg_tailc w m2 md2 A2 B2 F2 fc2 ptr2 rem2 data2 r1 BS2 LK2 _ _ wdc (1024 + 192 * w) (1024 + 192 * w)); [exact SI2 | exact STR2 | exact RWA | lia | exact DC1 | exact DC2 | lia | lia | | | lia | lia |].
{ intros d CBS mX q CO RRd. exact (PCC1 d CBS mX q CO RRd). }
{ intros BSx mX RRx. exact (PCR1 BSx mX RRx). }
unfold KTA in K |- *. intros. eapply K; try eassumption; lia.
Qed.
End Ctx.

Theorem harness_A : OBL_TARGET_jo HIx.
Proof.
unfold OBL_TARGET_jo, target_A_stmt. intros until errv. intros HP BB BD PAY PLEN SZ D0 DCE INB LML LOC LCK GA ST LO HBOT LOS SPA HT S0R ERR TP RAE RA FRM A0 A1 K.
subst tp a0 a1. clear RA. unfold TGT_STACK_A_jo in LOS.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in *.
stash PAY. stash ERR.
unfold TARGET_A.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 96%nat ST.
step. stepz. do 11 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
lazymatch goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (BODY : forall (sp1 : Z) (j32 : list byte) (gap : list cell),
sp1 mod 32 = 0 -> bv_unsigned sp - 112 <= sp1 -> sp1 + 8 + Z.of_nat (cells_size gap) = bv_unsigned sp + -88 ->
stk asegs m1 lo sp1 -> rw_cells asegs m1 sp1 [CB 8 j32] -> rw_cells asegs m1 (sp1 + 8) gap ->
AJ5 A4L HIx A T md (MS (mkR ra (Z_to_bv 64 sp1) gp (Z_to_bv 64 6444320) t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 data) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x91eb0) fc None m1 (seg_rom asegs))).
{ intros sp1 j32 gap SPA1 SPLO GAPE ST1 FD1 GAP1.
assert (HP1 : HEAPAx A LB LM [] B m1 md) by (heap_nowA A4L HIx HP MU WM MI1).
unstash PAY.
assert (PAY1 : bytes_at asegs m1 data payload) by (eapply bytes_at_transport; [exact PAY | exact MU | cbn [disjoint_from]; lia]).
assert (GA1 : GA_jo m1).
{ eapply GA_jo_munch; [exact GA | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia. }
idtac.
assert (DEP0 : 0 <= dcB 0 /\ 0 <= dcD 0) by (apply DCC; lia).
eapply (seg_headA HIx tpB tpD dcB dcD gsS gsB CA) with (sp1 := sp1) (lo := lo) (LB := LB) (LM := LM) (B := B) (data := data) (size := size) (payload := payload) (j8 := j32);
[ exact HP1 | exact BB | exact BD | exact PAY1 | exact PLEN | exact SZ | exact D0 | exact DCE | exact INB | exact LOC | exact LCK | exact GA1 | exact ST1 | exact FD1
| exact LO | lia | exact HBOT | exact SPA1 | lia | exact HT | exact FRM | exact LML | | ].
{ intros n Hn. destruct (TOTAL n None 0 [] Hn ltac:(cbn; lia) ltac:(lia) ltac:(intros sh0 E0; discriminate)) as [TB TD]. destruct DEP0 as [DB DD]. destruct (TPC n Hn) as [TP1 TP2].
pose proof (GBC 0 ltac:(lia)). cbn [dc_w setters_root root_of set_string_root set_double_root] in TB, TD. unfold JO_GETDBL_COSTB_A, JO_GETDBL_COSTD_A in *. lia. }
intros Fr p n s m2 md2 A2 B2 F2 fc2 ptr2 rem2 data2 BS2 LK2 y1 ygp y5 y6 y7 b0 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 FRAL FRLO FRHI FRAPP Hn WT GI.
eapply (seg_bodyA sp sp1 lo Fr LB LM m1 md F B data size payload LO ltac:(lia) SPA1 ltac:(lia) HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s10 s11 T BB BD n s); [exact Hn | exact WT | exact GI |].
idtac.
lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FR end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR as [_ SAV]. cbn [cells_size csize Nat.add] in SAV. replace (bv_unsigned sp + -96 + Z.of_nat 8) with (bv_unsigned sp + -88) in SAV by lia.
unfold KTA. intros m3 md3 A3 B3 F3 fc3 LKf z1 zgp zt0 zt1 zt2 zs1 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zt3 zt4 zt5 zt6 PX3 VM3 FS3 FRM3 LOC3 LCK3 GA3 ST3 FD3 HP3 BB3 BD3.
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ PX3) in SAV; [| left; cbn [cells_size csize Nat.add]; lia].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ PX3) in GAP1; [| left; lia].
change (hl_segs A4H) with asegs in *.
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC3, LCK3.
rename MU into MU01. rename WM into WM01.
clear FD1 ST1 PAY1 GA1 MI1 LOC LCK GI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. step.
do 11 step.
step. step.
evt_done5.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errv3 & ERR3). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR3.
eapply (K _ m3 md3 A3 B3 errv3 zgp LKf).
- unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; [exact FS3 | intros _; exact FRM3].
- exact VM3.
- pose proof (stk_release asegs _ _ _ _ ST3 FD3 ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 8) with 8 in S1.
pose proof (stk_release asegs _ _ _ _ S1 GAP1 ltac:(lia)) as S2. rewrite GAPE in S2.
pose proof (stk_release asegs _ _ _ _ S2 SAV ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
replace (bv_unsigned sp + -88 + Z.of_nat 88) with (bv_unsigned sp) in S3 by lia. exact S3.
- eapply heap_presx_trans; [| eapply heap_presx_weaken; [exact PX3 | lia | intros b Hb; exact Hb | intros a Xa; exact Xa]].
eapply (heap_presx_of_munch A4H _ (LB ++ LM) (bv_unsigned sp) [(bv_unsigned sp - 112, bv_unsigned sp)]); [exact MU01 | exact WM01 |].
intros a Ha Hc. cbn [outside]. split; [| exact I]. destruct Hc as [Hc | [Hc | (b & Hb & Hr)]].
+ lia.
+ pose proof (hl_static_in_img A4L a Hc) as Hi'. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi'. lia.
+ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bn HP Hb) as (_ & _ & _ & Hce & _). lia.
- exact LOC3.
- exact LCK3.
- exact ERR3.
- exact GA3.
- eapply (heapA_perm A4L HIx); [exact HP3 | apply Permutation.Permutation_app_comm | apply Permutation.Permutation_refl | apply Permutation.Permutation_refl].
- exact BB3.
- exact BD3. }
assert (CASE : (bv_unsigned sp + -96) mod 32 = 0 \/ (bv_unsigned sp + -96) mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
destruct CASE as [C0 | C16].
-
rewrite C0. replace (bv_unsigned sp + -96 - 0) with (bv_unsigned sp + -96) by lia.
evt_done5.
pose proof FR as FRh.
lazymatch type of FRh with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with (([c0] ++ []) ++ rest) in FRh end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRh as [FRh _]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRh as [FD1 GAP1].
cbn [cells_size csize Nat.add] in GAP1. change (Z.of_nat 8) with 8 in GAP1.
apply (rw_cells_recast asegs _ _ _ [CB 8 (le8 (Z_to_bv 64 0))]) in FD1; [| cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
eapply (BODY (bv_unsigned sp + -96) _ []); [exact C0 | lia | cbn [cells_size]; lia | exact ST | exact FD1 | exact GAP1].
-
rewrite C16. replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) by lia.
evt_done5.
destruct (stk_carve asegs m1 lo (bv_unsigned sp + -96) 16 ST ltac:(lia)) as [ST' [junk16 FRlow]].
change (Z.of_nat 16) with 16 in ST', FRlow. replace (bv_unsigned sp + -96 - 16) with (bv_unsigned sp + -112) in ST', FRlow by lia.
pose proof FR as FRh.
lazymatch type of FRh with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FRh end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRh as [FZ _].
destruct (rw_cells_CB_cut asegs _ _ _ _ 8 FRlow ltac:(lia)) as [FD1 G8]. change (Z.of_nat 8) with 8 in G8. change (16 - 8)%nat with 8%nat in G8.
assert (GAP1 : rw_cells asegs m1 (bv_unsigned sp + -112 + 8) ([CB 8 (skipn 8 junk16)] ++ [C8 (Z_to_bv 64 0)])).
{ apply (proj2 (rw_cells_app asegs m1 _ _ _)). split; [exact G8 |]. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8.
replace (bv_unsigned sp + -112 + 8 + 8) with (bv_unsigned sp + -96) by lia. exact FZ. }
eapply (BODY (bv_unsigned sp + -112) _ ([CB 8 (skipn 8 junk16)] ++ [C8 (Z_to_bv 64 0)])); [clear - SPA C16; Z.div_mod_to_equations; lia | lia | cbn [cells_size csize Nat.add app]; lia | exact ST' | exact FD1 | exact GAP1].
Qed.
End AHarnJo5.
End RC__1.
