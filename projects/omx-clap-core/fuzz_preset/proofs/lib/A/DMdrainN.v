(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainN.v (commit 67deba317dfb, blob 7576fbbaa1b5) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA DMdrainQ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMdeq AFer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma la_cons2 : forall ly a b l, la ly (a :: b :: l) = la ly (b :: l).
Proof. intros ly a b l. unfold la. cbn [rev]. rewrite <- app_assoc. cbn [app]. destruct (rev l); reflexivity. Qed.

Lemma lcn_relink : forall ly iw m l z',
lcn ly iw m l 0 -> (l <> [] -> val_mem tfibsegs m (la ly l) 8 z') -> lcn ly iw m l z'.
Proof.
intros ly iw m l. induction l as [|b t IH]; intros z' HL HZ; [exact I|].
destruct t as [|b2 t2].
- cbn [lcn] in *. destruct HL as [Hb _]. destruct Hb as (V0 & V8 & V16 & VS). split; [|exact I].
  unfold bcell, fa. split; [| split; [exact V8 | split; [exact V16 | exact VS]]].
  pose proof (HZ ltac:(discriminate)) as V. unfold la in V. cbn [rev app] in V. exact V.
- cbn [lcn] in HL |- *. destruct HL as [Hb Ht]. split.
  + unfold fa in *. exact Hb.
  + apply IH; [exact Ht|]. intros _. rewrite <- (la_cons2 ly b b2 t2). exact (HZ ltac:(discriminate)).
Qed.

Section nm.
Variables (W : world tfibsegs) (ly : alayout) (regs1 : bvmap 5 word) (mem1 : word -> option byte).
Variable Lk : list batch.
Variable iw : chunk -> Z.
Let m1 := mrestrict (w_H W) mem1.
Let sp1 : Z := bv_unsigned (getr regs1 2).

Hypothesis HLY : layout_ok ly.
Hypothesis HBF : forall b, In b Lk ->
  ly_prim ly <= addrb ly b /\ addrb ly b + kBatchBytes <= ly_space ly + kSpaceSize /\ addrb ly b mod 8192 = 0 /\ kBatchBytes <= b_bytes b.
Hypothesis HND : List.NoDup (map b_self Lk).
Hypothesis HSUM : sum_bytes Lk <= 2 ^ 31.

Hypothesis Hsp : ly_stk_lo ly + DRSTACK <= sp1 /\ sp1 + LFRAME <= ly_stk_hi ly.
Hypothesis HAL : sp1 mod 16 = 0.
Hypothesis HPRS : forall a, sp1 - DRSTACK <= a < sp1 + LFRAME -> apresent (w_H W) mem1 a.
Hypothesis Htp : getr regs1 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs1 1).

Hypothesis R10 : getr regs1 10 = w64 A_QUAR.
Hypothesis R11 : getr regs1 11 = w64 kQuarantineMin.
Hypothesis R14 : getr regs1 14 = w64 0.
Hypothesis R15 : getr regs1 15 = w64 0.
Hypothesis R16 : getr regs1 16 = w64 (Z.of_nat (length Lk)).
Hypothesis R5 : getr regs1 5 = w64 (fa ly Lk 0).

Hypothesis CQW : val_mem tfibsegs m1 (A_QUAR + 152) 4 257.
Hypothesis CQS : val_mem tfibsegs m1 (A_QUAR + 160) 8 (Z.of_nat (length Lk)).
Hypothesis CQF : val_mem tfibsegs m1 (A_QUAR + 168) 8 (fa ly Lk 0).
Hypothesis CQL : val_mem tfibsegs m1 (A_QUAR + 176) 8 (la ly Lk).
Hypothesis CQB : val_mem tfibsegs m1 (A_QUAR + 184) 8 (sum_bytes Lk).
Hypothesis CT8 : val_mem tfibsegs m1 (sp1 + 8) 8 0.
Hypothesis CT24 : val_mem tfibsegs m1 (sp1 + 24) 8 0.
Hypothesis CLK : lcn ly iw m1 Lk 0.

Theorem deq_pre_nomerge : DMdeq.deq_pre W ly regs1 mem1 [] Lk.
Proof.
constructor.
- exact HLY.
- intros b Hb. cbn [app] in Hb. exact (HBF b Hb).
- cbn [app]. exact HND.
- cbn [app]. exact HSUM.
- exact Hsp.
- exact HAL.
- exact HPRS.
- exact Htp.
- exact Hra.
- exact R10.
- exact R11.
- cbn [length Z.of_nat]. exact R14.
- cbn [AFer.lastaddr rev]. exact R15.
- exact R16.
- rewrite <- fa_firstaddr. exact R5.
- exact CQW.
- exact CQS.
- rewrite <- fa_firstaddr. exact CQF.
- rewrite <- la_lastaddr. exact CQL.
- exact CQB.
- intros i b Hi. destruct i; discriminate.
- intros i b Hi. split.
  + exact (lcn_next ly iw m1 Lk i b CLK Hi).
  + exact (lcn_size ly iw m1 Lk 0 i b CLK Hi).
- cbn [AFer.firstaddr]. exact CT8.
- cbn [sum_bytes fold_right]. exact CT24.
Qed.
End nm.
End c.
