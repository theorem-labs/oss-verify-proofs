(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_x509_san_ext_bud () : Init.string Init.list := ["Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.max"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "FFRx"].


Definition CNTx (n : Z) : Z := n / 2.
Definition PHIx (PHIp CNTp : Z -> Z) (n : Z) : Z := PHIp n + CNTp n * AVOL_CALL + (n / 2) * AVOL_CALL.
Definition FFRx (FFRp : Z -> Z -> Z) (CNTp : Z -> Z) (n d : Z) : Z := ltac2:(CDefT.buildp (gd_tbl_A_x509_san_ext_bud ()) "(0.(0.(0.A2.O4.O2.(0.O1.+1.)(1.A1.O3.O2.(2.=)))(1.(3.O2.+2.)(4.=(2.(0.O1.+1.)))))(1.(3.O2.+2.)(2.=)))")
(* [comment removed for export] *).

Lemma div2_mono : forall n n', 0 <= n <= n' -> 0 <= n / 2 <= n' / 2.
Proof. intros n n' H. split; [apply Z.div_pos; lia| apply Z.div_le_mono; lia]. Qed.
Lemma div2_sadd : forall a b, 0 <= a -> 0 <= b -> a / 2 + b / 2 <= (a + b) / 2.
Proof.
  intros a b Ha Hb. apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le a 2 ltac:(lia)). pose proof (Z.mul_div_le b 2 ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma cnt2_div : forall k x n, 2 * k <= x -> x <= n -> k <= n / 2.
Proof. intros k x n H1 H2. apply Z.div_le_lower_bound; lia. Qed.
(* [comment removed for export] *)
Lemma div2_step : forall c dl, 0 <= c -> 2 <= dl -> c / 2 + 1 <= (c + dl) / 2.
Proof.
  intros c dl Hc Hd. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le c 2 ltac:(lia)). lia.
Qed.

Lemma CNTx_mono : forall n n', 0 <= n <= n' -> 0 <= CNTx n <= CNTx n'.
Proof. intros n n' H. unfold CNTx. exact (div2_mono n n' H). Qed.
Lemma CNTx_sadd : forall a b, 0 <= a -> 0 <= b -> CNTx a + CNTx b <= CNTx (a + b).
Proof. intros a b Ha Hb. unfold CNTx. exact (div2_sadd a b Ha Hb). Qed.

Section Forms.
  Variables (PHIp : Z -> Z) (FFRp : Z -> Z -> Z) (CNTp : Z -> Z).
  Hypothesis PHIp_mono : forall n n', 0 <= n <= n' -> 0 <= PHIp n <= PHIp n'.
  Hypothesis FFRp_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRp n d <= FFRp n' d.
  Hypothesis CNTp_mono : forall n n', 0 <= n <= n' -> 0 <= CNTp n <= CNTp n'.

  #[using="PHIp_mono CNTp_mono"] Lemma PHIx_mono : forall n n', 0 <= n <= n' -> 0 <= PHIx PHIp CNTp n <= PHIx PHIp CNTp n'.
  Proof.
    intros n n' H. unfold PHIx, AVOL_CALL. pose proof (PHIp_mono n n' H). pose proof (CNTp_mono n n' H). pose proof (div2_mono n n' H). lia.
  Qed.
  #[using="FFRp_mono CNTp_mono"] Lemma FFRx_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRx FFRp CNTp n d <= FFRx FFRp CNTp n' d.
  Proof.
    intros n n' d H. unfold FFRx, fr_charge. pose proof (FFRp_mono n n' (d + 1) H). pose proof (CNTp_mono n n' H). pose proof (div2_mono n n' H).
    pose proof (Z.le_max_l 0 (d + 1 + 3)). nia.
  Qed.

  Hypothesis PHIp_sadd : forall a b, 0 <= a -> 0 <= b -> PHIp a + PHIp b <= PHIp (a + b).
  Hypothesis FFRp_sadd : forall a b d, 0 <= a -> 0 <= b -> FFRp a d + FFRp b d <= FFRp (a + b) d.
  Hypothesis CNTp_sadd : forall a b, 0 <= a -> 0 <= b -> CNTp a + CNTp b <= CNTp (a + b).

  #[using="PHIp_sadd CNTp_sadd"] Lemma PHIx_sadd : forall a b, 0 <= a -> 0 <= b -> PHIx PHIp CNTp a + PHIx PHIp CNTp b <= PHIx PHIp CNTp (a + b).
  Proof.
    intros a b Ha Hb. unfold PHIx, AVOL_CALL. pose proof (PHIp_sadd a b Ha Hb). pose proof (CNTp_sadd a b Ha Hb). pose proof (div2_sadd a b Ha Hb). lia.
  Qed.
  #[using="FFRp_sadd CNTp_sadd"] Lemma FFRx_sadd : ltac2:(CDefT.buildp (gd_tbl_A_x509_san_ext_bud ()) "Pa,$5.Pb,$5.Pd,$5.P,(6.=R3.)P,(6.=R3.)(6.(0.(7.VFFRp,VCNTp,R5.R3.)(7.VFFRp,VCNTp,R4.R3.))(7.VFFRp,VCNTp,(0.R5.R4.)R3.))")
(* [comment removed for export] *).
  Proof.
    intros a b d Ha Hb. unfold FFRx, fr_charge. pose proof (FFRp_sadd a b (d + 1) Ha Hb). pose proof (CNTp_sadd a b Ha Hb). pose proof (div2_sadd a b Ha Hb).
    pose proof (Z.le_max_l 0 (d + 1 + 3)). nia.
  Qed.
End Forms.
