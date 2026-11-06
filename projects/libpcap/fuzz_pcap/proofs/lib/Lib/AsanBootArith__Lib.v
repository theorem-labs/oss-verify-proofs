(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound.
From Stdlib Require List.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AsanBootArith.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition sbx (i : nat) (al : Z) : expr :=
  EAlu ALU_ADD (EAlu ALU_ADD (EVar i) (EMd M_MUL (ELit (-1)) (EAlu ALU_AND (EVar i) (ELit (al - 1))))) (ELit al).

Lemma land_ones_mod : forall p k, 0 <= p -> 0 <= k -> Z.land p (2 ^ k - 1) = p mod 2 ^ k.
Proof. intros p k Hp Hk. rewrite <- (Z.land_ones p k Hk). unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma sbx_val : forall E i k,
  0 <= k <= 32 ->
  bv_unsigned (ev E i) + 2 ^ k < 2 ^ 64 ->
  bv_unsigned (edenot E (sbx i (2 ^ k))) = bv_unsigned (ev E i) + 2 ^ k - bv_unsigned (ev E i) mod 2 ^ k.
Proof.
  intros E i k Hk Hnw. unfold sbx. cbn [edenot].
  set (p := bv_unsigned (ev E i)) in *. pose proof (u64_range (ev E i)) as Hp. fold p in Hp.
  rewrite u_add64, u_add64, u_mul64, u_and64, !u_lit64, two64_eq. fold p.
  assert (K32 : 2 ^ k <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small (2 ^ k - 1)) by lia.
  rewrite land_ones_mod by lia.
  set (r := p mod 2 ^ k). pose proof (Z.mod_pos_bound p (2 ^ k) ltac:(lia)) as Hr. fold r in Hr.
  assert (Hrp : r <= p) by (unfold r; apply Z.mod_le; lia).
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  nia.
Qed.

(* [comment removed for export] *)
Lemma shx_val : forall E i c,
  0 <= c -> bv_unsigned (ev E i) + c < 2 ^ 64 ->
  bv_unsigned (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c)) (ELit 3))) = (bv_unsigned (ev E i) + c) / 8.
Proof.
  intros E i c Hc Hnw. cbn [edenot]. pose proof (u64_range (ev E i)).
  rewrite u_srl64, u_add64, !u_lit64, two64_eq. rewrite (Z.mod_small c) by lia. rewrite (Z.mod_small _ (2 ^ 64)) by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shdiff_val : forall E i c m,
  0 <= c -> 8 <= m -> (bv_unsigned (ev E i) + c) mod 8 = 0 -> m mod 8 = 0 ->
  bv_unsigned (ev E i) + c + m < 2 ^ 64 ->
  bv_unsigned (edenot E
    (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c)) (ELit 3)))
                            (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit (c + m - 8))) (ELit 3))) (ELit 1)))
  = m / 8.
Proof.
  intros E i c m Hc Hm Hal Hm8 Hnw.
  change (bv_unsigned (alu64 ALU_ADD (alu64 ALU_ADD
            (mul_div M_MUL (Z_to_bv 64 (-1)) (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c)) (ELit 3))))
            (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit (c + m - 8))) (ELit 3)))) (Z_to_bv 64 1)) = m / 8).
  rewrite u_add64, u_add64, u_mul64, (shx_val E i c), (shx_val E i (c + m - 8)), !u_lit64, two64_eq by lia.
  pose proof (u64_range (ev E i)) as Hp. set (x := bv_unsigned (ev E i) + c) in *.
  replace (bv_unsigned (ev E i) + (c + m - 8)) with (x + (m - 8)) by lia.
  assert (Hx8 : x = 8 * (x / 8)) by (pose proof (Z.div_mod x 8 ltac:(lia)); lia).
  assert (Hm8b : m = 8 * (m / 8)) by (pose proof (Z.div_mod m 8 ltac:(lia)); lia).
  set (q := x / 8) in *. set (kk := m / 8) in *.
  replace ((x + (m - 8)) / 8) with (q + kk - 1)
    by (rewrite Hx8, Hm8b; replace (8 * q + (8 * kk - 8)) with ((q + kk - 1) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  nia.
Qed.

(* [comment removed for export] *)
Lemma shx_val0 : forall E i,
  bv_unsigned (edenot E (EAlu ALU_SRL (EVar i) (ELit 3))) = bv_unsigned (ev E i) / 8.
Proof.
  intros E i. cbn [edenot]. pose proof (u64_range (ev E i)).
  rewrite u_srl64, !u_lit64, two64_eq. reflexivity.
Qed.

Lemma shdiff_val0 : forall E i m,
  8 <= m -> bv_unsigned (ev E i) mod 8 = 0 -> m mod 8 = 0 ->
  bv_unsigned (ev E i) + m < 2 ^ 64 ->
  bv_unsigned (edenot E
    (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EVar i) (ELit 3)))
                            (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit (m - 8))) (ELit 3))) (ELit 1)))
  = m / 8.
Proof.
  intros E i m Hm Hal Hm8 Hnw.
  change (bv_unsigned (alu64 ALU_ADD (alu64 ALU_ADD
            (mul_div M_MUL (Z_to_bv 64 (-1)) (edenot E (EAlu ALU_SRL (EVar i) (ELit 3))))
            (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit (m - 8))) (ELit 3)))) (Z_to_bv 64 1)) = m / 8).
  rewrite u_add64, u_add64, u_mul64, (shx_val0 E i), (shx_val E i (m - 8)), !u_lit64, two64_eq by lia.
  pose proof (u64_range (ev E i)) as Hp. set (x := bv_unsigned (ev E i)) in *.
  assert (Hx8 : x = 8 * (x / 8)) by (pose proof (Z.div_mod x 8 ltac:(lia)); lia).
  assert (Hm8b : m = 8 * (m / 8)) by (pose proof (Z.div_mod m 8 ltac:(lia)); lia).
  set (q := x / 8) in *. set (kk := m / 8) in *.
  replace ((x + (m - 8)) / 8) with (q + kk - 1)
    by (rewrite Hx8, Hm8b; replace (8 * q + (8 * kk - 8)) with ((q + kk - 1) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  nia.
Qed.
Lemma shx_val_gen : forall E i c,
  0 <= bv_unsigned (ev E i) + c -> bv_unsigned (ev E i) + c < 2 ^ 64 ->
  bv_unsigned (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c)) (ELit 3))) = (bv_unsigned (ev E i) + c) / 8.
Proof.
  intros E i c Hc Hnw. cbn [edenot]. pose proof (u64_range (ev E i)).
  rewrite u_srl64, u_add64, !u_lit64, two64_eq.
  replace ((bv_unsigned (ev E i) + c mod 2 ^ 64) mod 2 ^ 64) with ((bv_unsigned (ev E i) + c) mod 2 ^ 64)
    by (rewrite Zplus_mod_idemp_r; reflexivity).
  rewrite (Z.mod_small _ (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma shsub_val : forall E i c1 c2,
  0 <= bv_unsigned (ev E i) + c1 -> c1 <= c2 -> bv_unsigned (ev E i) + c2 < 2 ^ 64 ->
  bv_unsigned (edenot E
    (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c1)) (ELit 3)))
                  (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c2)) (ELit 3))))
  = (bv_unsigned (ev E i) + c2) / 8 - (bv_unsigned (ev E i) + c1) / 8.
Proof.
  intros E i c1 c2 H1 H12 H2.
  change (bv_unsigned (alu64 ALU_ADD
            (mul_div M_MUL (Z_to_bv 64 (-1)) (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c1)) (ELit 3))))
            (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c2)) (ELit 3))))
          = (bv_unsigned (ev E i) + c2) / 8 - (bv_unsigned (ev E i) + c1) / 8).
  rewrite u_add64, u_mul64, (shx_val_gen E i c1), (shx_val_gen E i c2), !u_lit64, two64_eq by lia.
  pose proof (u64_range (ev E i)) as Hp.
  pose proof (Z.div_le_mono (bv_unsigned (ev E i) + c1) (bv_unsigned (ev E i) + c2) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (bv_unsigned (ev E i) + c1) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (bv_unsigned (ev E i) + c2) 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  set (q1 := (bv_unsigned (ev E i) + c1) / 8) in *. set (q2 := (bv_unsigned (ev E i) + c2) / 8) in *.
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  replace ((2 ^ 64 - 1) * q1) with (- q1 + q1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
  rewrite <- Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_l. replace (- q1 + q2) with (q2 - q1) by lia. apply Z.mod_small. lia.
Qed.
End AsanBootArith.

(* [comment removed for export] *)
Module AsanBootArith2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanBootArith__Lib.AsanBootArith.
Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma shr_val_gen : forall E i c k,
  0 <= k < 64 -> 0 <= bv_unsigned (ev E i) + c -> bv_unsigned (ev E i) + c < 2 ^ 64 ->
  bv_unsigned (edenot E (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c)) (ELit k))) = (bv_unsigned (ev E i) + c) / 2 ^ k.
Proof.
  intros E i c k Hk Hc Hnw. cbn [edenot]. pose proof (u64_range (ev E i)).
  rewrite u_srl64, u_add64, !u_lit64, two64_eq.
  replace ((bv_unsigned (ev E i) + c mod 2 ^ 64) mod 2 ^ 64) with ((bv_unsigned (ev E i) + c) mod 2 ^ 64)
    by (rewrite Zplus_mod_idemp_r; reflexivity).
  rewrite (Z.mod_small _ (2 ^ 64)) by lia. rewrite (Z.mod_small k (2 ^ 64)) by lia. rewrite (Z.mod_small k 64) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lin2_val : forall E i j k,
  0 <= bv_unsigned (ev E j) - bv_unsigned (ev E i) + k < 2 ^ 64 ->
  bv_unsigned (edenot E (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar i)) (EVar j)) (ELit k)))
  = bv_unsigned (ev E j) - bv_unsigned (ev E i) + k.
Proof.
  intros E i j k Hr. cbn [edenot]. pose proof (u64_range (ev E i)) as Hi. pose proof (u64_range (ev E j)) as Hj.
  rewrite !u_add64, u_mul64, !u_lit64, two64_eq.
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  replace ((2 ^ 64 - 1) * bv_unsigned (ev E i)) with (- bv_unsigned (ev E i) + bv_unsigned (ev E i) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. rewrite (Zplus_mod_idemp_l (- bv_unsigned (ev E i))), <- Zplus_mod. lia.
Qed.

Lemma lin2_val' : forall E i j k,
  0 <= bv_unsigned (ev E i) - bv_unsigned (ev E j) + k < 2 ^ 64 ->
  bv_unsigned (edenot E (EAlu ALU_ADD (EAlu ALU_ADD (EVar i) (EMd M_MUL (ELit (-1)) (EVar j))) (ELit k)))
  = bv_unsigned (ev E i) - bv_unsigned (ev E j) + k.
Proof.
  intros E i j k Hr. cbn [edenot]. pose proof (u64_range (ev E i)) as Hi. pose proof (u64_range (ev E j)) as Hj.
  rewrite !u_add64, u_mul64, !u_lit64, two64_eq.
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  replace ((2 ^ 64 - 1) * bv_unsigned (ev E j)) with (- bv_unsigned (ev E j) + bv_unsigned (ev E j) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. rewrite (Zplus_mod_idemp_r (- bv_unsigned (ev E j))), <- Zplus_mod. lia.
Qed.

(* [comment removed for export] *)
Lemma lin1_val : forall E i k,
  0 <= bv_unsigned (ev E i) + k < 2 ^ 64 ->
  bv_unsigned (edenot E (EAlu ALU_ADD (EVar i) (ELit k))) = bv_unsigned (ev E i) + k.
Proof.
  intros E i k Hr. cbn [edenot]. pose proof (u64_range (ev E i)).
  rewrite u_add64, !u_lit64, two64_eq, Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma shdiff1_val : forall E i c1 c2,
  0 <= bv_unsigned (ev E i) + c1 -> c1 <= c2 -> bv_unsigned (ev E i) + c2 < 2 ^ 64 ->
  bv_unsigned (edenot E
    (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c1)) (ELit 3)))
                            (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c2)) (ELit 3))) (ELit 1)))
  = (bv_unsigned (ev E i) + c2) / 8 - (bv_unsigned (ev E i) + c1) / 8 + 1.
Proof.
  intros E i c1 c2 H1 H12 H2.
  change (bv_unsigned (alu64 ALU_ADD (edenot E (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c1)) (ELit 3)))
                            (EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit c2)) (ELit 3)))) (Z_to_bv 64 1))
          = (bv_unsigned (ev E i) + c2) / 8 - (bv_unsigned (ev E i) + c1) / 8 + 1).
  rewrite u_add64, (shsub_val E i c1 c2), u_lit64, two64_eq by lia.
  pose proof (u64_range (ev E i)).
  pose proof (Z.div_le_mono (bv_unsigned (ev E i) + c1) (bv_unsigned (ev E i) + c2) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (bv_unsigned (ev E i) + c2) 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (bv_unsigned (ev E i) + c1) 8 ltac:(lia) ltac:(lia)).
  change (1 mod 2 ^ 64) with 1. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Section StackShadow.
  Variables (E : env) (i : nat).
  Let st := bv_unsigned (ev E i).
  Hypothesis Hlo : 0x7fff80000000 <= st.
  Hypothesis Hhi : st <= 2 ^ 47.
  Hypothesis Hal : st mod 4096 = 0.
  Definition xq : Z := (st - 8388608) / 8.
  Definition XQ : expr := EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit (-8388608))) (ELit 3).
  Definition YQ : expr := EAlu ALU_SRL (EAlu ALU_ADD (EVar i) (ELit (-8))) (ELit 3).

  #[using="Hlo Hhi Hal"] Lemma xq_range : 0xfffeff00000 <= xq <= 0xffffff00000 /\ xq mod 512 = 0 /\ st = 8 * xq + 8388608.
  Proof.
    unfold xq. pose proof (Z.div_mod st 4096 ltac:(lia)) as D. set (k := st / 4096) in *.
    replace (st - 8388608) with ((512 * k - 1048576) * 8) by lia. rewrite Z.div_mul by lia.
    split; [lia|]. split; [| lia]. replace (512 * k - 1048576) with ((k - 2048) * 512) by lia. apply Z_mod_mult.
  Qed.

  #[using="Hlo Hhi"] Lemma xq_val : bv_unsigned (edenot E XQ) = xq.
  Proof. unfold XQ, xq. apply shr_val_gen; unfold st in *; lia. Qed.

  #[using="Hlo Hhi Hal"] Lemma yq_val : bv_unsigned (edenot E YQ) = xq + 2 ^ 20 - 1.
  Proof.
    unfold YQ. rewrite (shr_val_gen E i (-8) 3) by (unfold st in *; lia). pose proof xq_range as (R & _ & S).
    fold st. rewrite S. replace (8 * xq + 8388608 + -8) with ((xq + 2 ^ 20 - 1) * 8) by lia. rewrite Z.div_mul by lia. reflexivity.
  Qed.

  #[using="Hlo Hhi Hal"] Lemma xq_add : forall c, 0 <= c -> c < 2 ^ 40 -> bv_unsigned (edenot E (EAlu ALU_ADD XQ (ELit c))) = xq + c.
  Proof.
    intros c Hc Hc2. change (bv_unsigned (alu64 ALU_ADD (edenot E XQ) (Z_to_bv 64 c)) = xq + c).
    rewrite u_add64, xq_val, u_lit64, two64_eq, (Z.mod_small c) by lia. pose proof xq_range. apply Z.mod_small. lia.
  Qed.

  #[using="Hlo Hhi Hal"] Lemma yq_add : forall c, 0 <= c -> c < 2 ^ 40 -> bv_unsigned (edenot E (EAlu ALU_ADD YQ (ELit c))) = xq + 2 ^ 20 - 1 + c.
  Proof.
    intros c Hc Hc2. change (bv_unsigned (alu64 ALU_ADD (edenot E YQ) (Z_to_bv 64 c)) = xq + 2 ^ 20 - 1 + c).
    rewrite u_add64, yq_val, u_lit64, two64_eq, (Z.mod_small c) by lia. pose proof xq_range. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hlo Hhi Hal"] Lemma xq_page : forall c, 0 <= c -> c < 2 ^ 40 ->
    bv_unsigned (edenot E (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EAlu ALU_ADD XQ (ELit c)) (ELit 12)))) = 4096 * ((xq + c) / 4096).
  Proof.
    intros c Hc Hc2. pose proof xq_range as (R & _ & _).
    change (bv_unsigned (mul_div M_MUL (Z_to_bv 64 4096) (alu64 ALU_SRL (edenot E (EAlu ALU_ADD XQ (ELit c))) (Z_to_bv 64 12))) = 4096 * ((xq + c) / 4096)).
    rewrite u_mul64, u_srl64, (xq_add c Hc Hc2), !u_lit64, two64_eq. change (4096 mod 2 ^ 64) with 4096. change (2 ^ (12 mod 2 ^ 64 mod 64)) with 4096.
    pose proof (Z.div_pos (xq + c) 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (xq + c) 4096 (2 ^ 40) ltac:(lia) ltac:(lia)).
    apply Z.mod_small. lia.
  Qed.

  #[using="Hlo Hhi Hal"] Lemma yq_page : forall c, 0 <= c -> c < 2 ^ 40 ->
    bv_unsigned (edenot E (EMd M_MUL (ELit 4096) (EAlu ALU_SRL (EAlu ALU_ADD YQ (ELit c)) (ELit 12)))) = 4096 * ((xq + 2 ^ 20 - 1 + c) / 4096).
  Proof.
    intros c Hc Hc2. pose proof xq_range as (R & _ & _).
    change (bv_unsigned (mul_div M_MUL (Z_to_bv 64 4096) (alu64 ALU_SRL (edenot E (EAlu ALU_ADD YQ (ELit c))) (Z_to_bv 64 12))) = 4096 * ((xq + 2 ^ 20 - 1 + c) / 4096)).
    rewrite u_mul64, u_srl64, (yq_add c Hc Hc2), !u_lit64, two64_eq. change (4096 mod 2 ^ 64) with 4096. change (2 ^ (12 mod 2 ^ 64 mod 64)) with 4096.
    pose proof (Z.div_pos (xq + 2 ^ 20 - 1 + c) 4096 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (xq + 2 ^ 20 - 1 + c) 4096 (2 ^ 40) ltac:(lia) ltac:(lia)).
    apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="st Hlo Hhi Hal"] Lemma s0_val : bv_unsigned (edenot E (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) XQ) YQ) (ELit 1))) = 2 ^ 20.
  Proof.
    unfold XQ, YQ. rewrite shdiff1_val by (unfold st in *; lia). pose proof xq_range as (R & _ & S). fold st. rewrite S.
    replace (8 * xq + 8388608 + -8) with ((xq + 2 ^ 20 - 1) * 8) by lia. replace (8 * xq + 8388608 + -8388608) with (xq * 8) by lia.
    rewrite !Z.div_mul by lia. lia.
  Qed.
End StackShadow.
End AsanBootArith2.

(* [comment removed for export] *)
Module AsanBootKn3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound AsanPlanCore. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Definition KZDEEP : kentry := KZero (SA (EVar 0) (- 0x800000)) (ELit 8380416).

Definition kz_deep1 (k : kentry) : kentry :=
  match k with
  | KZero (SA (EVar 0%nat) o) (ELit n) => if (o =? - 0x800000) && (8380416 <=? n) && (n <? 2 ^ 64) then KZDEEP else k
  | _ => k
  end.
Definition kz_deep (kn : list kentry) : list kentry := List.map kz_deep1 kn.

Lemma kz_deep1_sound : forall segs E M k, kentry_ok segs E M k -> kentry_ok segs E M (kz_deep1 k).
Proof.
  intros segs E M k HK. destruct k as [| a n | | | | | | | |]; try exact HK.
  destruct a as [b o]. destruct b as [|i| | | | | |]; try exact HK. destruct i as [|i]; [|exact HK].
  destruct n as [z| | | | | | |]; try exact HK. cbn [kz_deep1].
  destruct ((o =? - 0x800000) && (8380416 <=? z) && (z <? 2 ^ 64)) eqn:C; [|exact HK].
  apply andb_prop in C as [C C3]. apply andb_prop in C as [C1 C2].
  apply Z.eqb_eq in C1. apply Z.leb_le in C2. apply Z.ltb_lt in C3. subst o.
  unfold KZDEEP. cbn [kentry_ok] in *. destruct HK as [HF HZ]. unfold flat, elenZ, estart in *. cbn [a_base a_off edenot] in *.
  rewrite u_small in HF, HZ by lia. rewrite u_small by lia.
  split; [lia|]. intros i Hi. apply HZ. lia.
Qed.

Lemma kz_deep_sound : forall segs E M kn, know_ok segs E M kn -> know_ok segs E M (kz_deep kn).
Proof.
  intros segs E M kn HK. unfold know_ok, kz_deep in *. apply Forall_forall. intros k Hk.
  apply in_map_iff in Hk as (k0 & <- & Hin). apply kz_deep1_sound. exact (proj1 (Forall_forall _ _) HK k0 Hin).
Qed.

Lemma kz_deep_length : forall kn, length (kz_deep kn) = length kn.
Proof. intros. unfold kz_deep. apply length_map. Qed.
End AsanBootKn3.
