(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_state RT_rep RT_io RT_cli RT_iclifts TopA_iodefs TopA_io F_achk Fe_icalls I_memcpyw I_pcrr I_pchead I_vprintfw I_vprintf I_vfsn6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.

Lemma rta_chkr_static : forall Σ m p n, ART RTA Σ m -> 0 < n <= 2 ^ 40 -> In (p, n) io_acc -> 0x10000 <= p -> p + n <= SEGTOP_A -> chkr m p n.
Proof.
  intros Σ m p n HA Hn Hin H1 H2.
  apply (chkr_of RTA rta_shw Σ m p n HA Hn (io_acc_at m (rta_io Σ m HA) p n Hin)). right; right; right. exact (conj H1 H2).
Qed.

Local Ltac ck := eapply rta_chkr_static; [eassumption | lia | io_in | lia | unfold SEGTOP_A; lia].

Theorem rta_np : forall Σ m, ART RTA Σ m -> rod_chk m /\ rod_chk_fp m /\ ifx_real m /\ pctx m /\ pfcells6 m.
Proof.
  intros Σ m HA. pose proof (rta_io Σ m HA) as IO.
  split. { unfold rod_chk, PFX_A, XDIG_A, NULLS_A. split; [ck|]. split; ck. }
  split. { unfold rod_chk_fp. split; [ck|]. split; [ck|]. split; [ck|]. split; [ck|]. split; ck. }
  split. { exact (cli_ro_at m 0x16c090 _ (rta_cli_ro Σ m HA) ltac:(unfold CLI_RO; cbn [In]; repeat (first [left; reflexivity | right]))). }
  split. { pose proof (rta_ic Σ m HA) as ((G2 & G1 & RM & SHC & RI) & _ & _ & _ & M2S). split; [exact M2S | split; assumption]. }
  split; [exact (proj1 (rta_pf rta_io Σ m HA))|].
  pose proof (io_ro_at m IO 0x16c0c8 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [_ V2]. apply ro_split1 in V2 as [_ V3].
  cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Pos.succ] in V3. exact V3.
Qed.
