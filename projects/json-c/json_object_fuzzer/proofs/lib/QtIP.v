(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsTj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkRc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9kF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvsx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvsx.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLiw.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGaR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGaR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVJy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVJy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFL8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFL8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmAH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmAH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcGV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcGV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNLn.Mq0.
Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Module RC := Q6q3.
Module HI := QCcH.
Module JH := QZsi.
Module OSA := QRjH.
Module GI := QDXD.Mq3.
Module MGI := QYZ0.
Module SG := Q9kF.
Module KV := Qfya.
Module MG := QGeV.
Module MB := Qy5Y.Mq4.
Module MSU := QSui.
Module SM := QUZl.

Section Inst1.
Context {RC__ : RC.RunConsts}.
Variable L : JH.heap_layout_A.
Notation HL := (JH.hla_base L).
Notation segs := (HI.hl_segs HL).

Variable LA : ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable DL : dlayout.
Variable RE : aentry.
Variable DCo : donor_core RC.alloc_ceiling segs (at_nodeA LV segs) DL.

Variable FR0 : list (Z * Z).
Definition FRof (Lg : KV.mled) : list (Z * Z) := map civ (KV.ld_groups Lg) ++ FR0.
Definition in_regs (FR : list (Z * Z)) (x : word) : bool := existsb (fun r => zin (bv_unsigned x) r) FR.

Variable S : MGI.mng_sig.
Variable BAUX : Z.

Variable STAT : (word -> option byte) -> Prop.

Definition zblk (b : MB.block) : Z * Z := (MB.blk_addr b, MB.blk_size b).
Definition SC : Z := sec_cost kMaxChunk.

Definition HEAPA1 (k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (m : word -> option byte) (c : config) : Prop :=
exists (g : ghost) (Lg : KV.mled) (H : word -> bool) (Bc Tc Nc : Z) (s : MG.PState) (LB0 : list MB.block),

HEAPA0g L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) g LB LM FR B m c

/\ KLA LV PERM0 TMAX NMAX (fun _ => false) Lg g c H m Bc Tc Nc
/\ 0 <= k /\ Tc + k * kMaxChunk <= TMAX /\ Nc + k <= NMAX

/\ (forall r y, In r (MGI.doranges Lg) -> fst r <= bv_unsigned y < fst r + snd r -> in_regs FR0 y = true)
/\ (forall a n, In (a, n) LM -> MGI.mrange S a n /\
forall x, a <= x < a + n -> in_regs (FRof Lg) (wa x) = true /\ m (wa x) <> None)

/\ Permutation LM (map zblk LB0)
/\ MGI.mg_heap S s LB0 m
/\ SG.HSIM s Lg LB0
/\ Permutation (KV.ld_live Lg) (map MB.blk_slot LB0)
/\ List.NoDup (KV.ld_live Lg)
/\ Forall (fun b => 1 <= MB.blk_size b) LB0
/\ MGI.mg_auxv S m BAUX
/\ 25 + 8 * k <= MSU.cntm (MG.ps_m s)

/\ Forall (fun b : HI.blk => wr_at segs (mrestrict (Fof LV (FRof Lg)) m) (fst b) (snd b)
/\ (fst b + snd b <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= fst b)
/\ fst b + snd b <= RC.alloc_ceiling) (fr_ivs0 L FR)
/\ STAT m.

End Inst1.
