(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepPrfS.v (commit eb934de95d13, blob fdaaf2ae84f4) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 14 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0m AF0x AFl0 AFl2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RepIFcf RepPrfD.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

Definition runR (pc : Z) (ss : sstate) : sstate * run_status := sym_run_toN_sh tfibsegs reptbl FUEL pc ss.
Definition pin (ss : sstate) (r : bv 5) (e : sv) : sstate :=
  mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition addreg (r : YP09.region) (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).

Definition R_LOW : YP09.region := YP09.mkRegion (Some 2%nat) (- PR_STK) (-640) (- PR_STK) (-640) [].
Definition R_NB : YP09.region := YP09.mkRegion (Some 2%nat) (-640) (-512) (-640) (-512) [].
Definition R_TOP : YP09.region := YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0 [].
Definition PCONST : smem := [lit8 C_PFCB A_APPEND; lit8 C_SILENT 1].
Definition PMEM0 : smem := [R_LOW; R_NB; R_TOP] ++ PCONST.
Definition PFF : facts := mkFacts [(2%nat, mkAF (kHighMemBeg + PR_STK) kHighMemEnd 4)] [] [].
Definition SS_P0 : sstate := mkSS A_PRINTF sr_atoms PMEM0 None PFF.

Definition P1r : sstate * run_status := Eval vm_compute in runR 0x64ab8 SS_P0.

Definition P1s : sstate := Eval vm_compute in ss_after_stretch (fst P1r) (ss_mem (fst P1r)) 32 [11; 12; 13]%bv 0x67eb4.

Definition P2r : sstate * run_status := Eval vm_compute in runR A_VSNPRINTF P1s.

Definition P2c : sstate := Eval vm_compute in ss_after_call (fst P2r) (skipn 1 (ss_mem (fst P2r))) 35 0x68520.

Definition bufchunks (out : list Z) : list YP09.chunk :=
  map (fun p => YP09.mkChunk (-512 + Z.of_nat (fst p)) (CVal 1 (SLit (snd p)))) (combine (seq 0 (length out)) out).
Definition R_BUF (out : list Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-512) (-512 + Z.of_nat (length out)) 0 0 (bufchunks out).
Definition R_NUL (out : list Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-512 + Z.of_nat (length out)) (-511 + Z.of_nat (length out))
    (-512 + Z.of_nat (length out)) (-511 + Z.of_nat (length out))
    [YP09.mkChunk (-512 + Z.of_nat (length out)) (CVal 1 (SLit 0))].
Definition P3s (out : list Z) : sstate :=
  pin (addreg (R_BUF out) (addreg (R_NUL out) (addreg R_LOW P2c))) 10%bv (SLit (Z.of_nat (length out))).

Definition P3r (out : list Z) : sstate * run_status := runR A_APPEND (P3s out).
Definition P3e (out : list Z) : sstate := fst (P3r out).

Definition OUTS : list (list Z) := render1 :: map (fun c => render2 c (class_size c)) (map Z.of_nat (seq 1 31)).
Lemma OUTS_render2 : forall c, 1 <= c <= 31 -> In (render2 c (class_size c)) OUTS.
Proof.
intros c Hc. unfold OUTS. right. apply in_map_iff. exists c. split; [reflexivity|].
apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma OUTS_len : forallb (fun out => Z.of_nat (length out) <? 400) OUTS = true.
Proof. vm_compute. reflexivity. Qed.

Definition P3regs (len : Z) : list sv :=
[SLit 0; SLit 0x68554; SOff 2 (-640); SOff 3 0; SOff 4 0; SOff 36 0; SOff 37 0; SOff 38 0;
 SOff 10 0; SLit 0; SOff 2 (-512); SLit A_APPEND; SLit len; SOff 2 (-513 + len); SOff 43 0; SOff 44 0;
 SOff 45 0; SOff 46 0; SOff 2 (-512); SLit 400; SOff 20 0; SLit len; SOff 22 0; SOff 23 0;
 SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0]%nat.
Definition R_LOW3 : YP09.region := YP09.mkRegion (Some 2%nat) (- PR_STK) (-640) (- PR_STK) (-640)
 [YP09.mkChunk (-672) (CVal 8 (SOff 2 (-512))); YP09.mkChunk (-664) (CVal 8 (SLit 0));
  YP09.mkChunk (-656) (CVal 8 (SOff 10 0)); YP09.mkChunk (-648) (CVal 8 (SLit 0x68538))]%nat.
Definition R_NB3 : YP09.region := YP09.mkRegion (Some 2%nat) (-640) (-512) (-640) (-512)
 [YP09.mkChunk (-624) (CVal 8 (SLit 0)); YP09.mkChunk (-632) (CVal 8 (SLit 0));
  YP09.mkChunk (-640) (CVal 8 (SLit 0)); YP09.mkChunk (-616) (CVal 8 (SOff 2 (-56)));
  YP09.mkChunk (-608) (CVal 8 (SOff 2 (-56))); YP09.mkChunk (-600) (CVal 8 (SOff 25 0));
  YP09.mkChunk (-592) (CVal 8 (SOff 24 0)); YP09.mkChunk (-584) (CVal 8 (SOff 23 0));
  YP09.mkChunk (-576) (CVal 8 (SOff 22 0)); YP09.mkChunk (-568) (CVal 8 (SOff 21 0));
  YP09.mkChunk (-560) (CVal 8 (SOff 20 0)); YP09.mkChunk (-552) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-544) (CVal 8 (SLit 0)); YP09.mkChunk (-536) (CVal 8 (SOff 10 0));
  YP09.mkChunk (-528) (CVal 8 (SOff 2 (-56))); YP09.mkChunk (-520) (CVal 8 (SLit 0x67ec8))]%nat.
Definition R_TOP3 : YP09.region := YP09.mkRegion (Some 2%nat) (-112) 0 (-112) 0
 [YP09.mkChunk (-112) (CVal 8 (SOff 18 0)); YP09.mkChunk (-104) (CVal 8 (SOff 9 0));
  YP09.mkChunk (-96) (CVal 8 (SOff 8 0)); YP09.mkChunk (-88) (CVal 8 (SLit 0x67e78));
  YP09.mkChunk (-80) (CVal 8 (SOff 2 (-56))); YP09.mkChunk (-32) (CVal 8 (SOff 14 0));
  YP09.mkChunk (-40) (CVal 8 (SOff 13 0)); YP09.mkChunk (-48) (CVal 8 (SOff 12 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 11 0)); YP09.mkChunk (-8) (CVal 8 (SOff 17 0));
  YP09.mkChunk (-16) (CVal 8 (SOff 16 0)); YP09.mkChunk (-24) (CVal 8 (SOff 15 0));
  YP09.mkChunk (-72) (CVal 8 (SOff 1 0))]%nat.
Definition P3tail : smem := [R_LOW3; R_NB3; R_TOP3] ++ PCONST.
Definition P3end (out : list Z) : sstate :=
  mkSS A_APPEND (P3regs (Z.of_nat (length out))) (R_BUF out :: R_NUL out :: P3tail) None PFF.
Lemma P3_ends : Forall (fun out => P3r out = (P3end out, RS_running)) OUTS.
Proof. repeat (apply Forall_cons; [vm_compute; reflexivity|]). apply Forall_nil. Qed.

Definition R_CFG : YP09.region := lit8 0xa2000 0x13c9e8.
Definition R_SYSLOG : YP09.region := lit8 0x13ca28 0.
Definition CLOBP : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 28; 29; 30; 31]%bv.
Definition P4keep : smem := [R_NB3; R_TOP3].
Definition P4s (out : list Z) : sstate :=
  addreg R_SYSLOG (addreg R_CFG (addreg R_LOW (ss_after_stretch (P3end out) P4keep 51 CLOBP 0x68554))).
Definition P4S : sstate := Eval vm_compute in P4s [].
Lemma P4s_const : forall out, P4s out = P4S.
Proof. intros out. unfold P4s, P4S, P3end, ss_after_stretch. vm_compute. reflexivity. Qed.

Definition P4R : sstate * run_status := Eval vm_compute in runR 0x67e80 P4S.
Definition P4E : sstate := Eval vm_compute in fst P4R.
Lemma P4_run : runR 0x67e80 P4S = (P4E, RS_running).
Proof. vm_compute. reflexivity. Qed.

Lemma P12_pcs : snd P1r = RS_running /\ ss_pc (fst P1r) = 0x64ab8 /\ snd P2r = RS_running /\ ss_pc (fst P2r) = A_VSNPRINTF.
Proof. vm_compute. repeat split; reflexivity. Qed.
