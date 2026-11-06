(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import FpLift WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibU Require Import UCode UImg UWpacket UDecode UA2u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rget_lof : forall regs (k : nat), (0 < k < 32)%nat -> rget (lof regs) k = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. intros regs k Hk. symmetry. apply rrel_getr; [apply rrel_lof | exact Hk]. Qed.

(* [comment removed for export] *)
Theorem decode_spec_u : forall regs F fc M rom (ret : word) sp p n out q max,
  getr regs 1%bv = ret -> v_jalr ret 0 = ret ->
  getr regs 2%bv = W sp -> getr regs 10%bv = W p -> getr regs 11%bv = W n ->
  getr regs 12%bv = W out -> getr regs 13%bv = W q ->
  0 <= n < 2 ^ 31 -> 0 <= p -> p + n < 2 ^ 63 -> rd_ok M p n ->
  0 <= max <= 512 -> cell USEGS M q 4 (W max) ->
  0x354000 <= sp - 160 -> sp < 2 ^ 63 -> wr_ok USEGS M (sp - 160) 160 ->
  0x354000 <= out -> out + 4 * max < 2 ^ 63 -> wr_ok USEGS M out (4 * max) ->
  0x354000 <= q -> q + 4 < 2 ^ 63 -> wr_ok USEGS M q 4 ->
  (out + 4 * max <= sp - 160 \/ sp <= out) -> (q + 4 <= sp - 160 \/ sp <= q) ->
  (n = 0 \/ 0 < p) -> out mod 4 = 0 -> q mod 4 = 0 ->
  exists regs' M',
    msteps USEGS (mkstF regs F fc (W 0x215490) M rom) (mkstF regs' F fc ret M' rom)
    /\ (getr regs' 10%bv = W 0 \/ getr regs' 10%bv = W 1)
    /\ (forall r : reg, ~ In (ridx r) KSdec -> getr regs' r = getr regs r)
    /\ (forall x, ~ dec_FP sp out q max x -> M' x = M x) /\ mem_grows M M'
    /\ (getr regs' 10%bv = W 1 -> exists w, 0 <= w <= max /\ cell USEGS M' q 4 (W w)).
Proof.
  intros regs F fc M rom ret sp p n out q max Hra Hret H2 H10 H11 H12 H13 Hn Hp Hpn Hrd Hmax Hqc Hsp Hsp2 Hfr
         Hout Hout2 Hwout Hq Hq2 Hwq Hdj1 Hdj2 Hpnz Ho4 Hq4.
  pose (Post := fun (pc' : word) (l' : regfile) (M' : mem) =>
     pc' = ret /\ same_except KSdec (lof regs) l' /\ (rget l' 10 = W 0 \/ rget l' 10 = W 1)
     /\ (rget l' 10 = W 1 -> exists w, 0 <= w <= max /\ cell USEGS M' q 4 (W w))
     /\ unch M M' (dec_FP sp out q max) /\ mem_grows M M').
  assert (HR : reach USEGS rom (W 0x215490) (lof regs) M Post).
  { eapply (decode_cps rom Post M sp p n out q max); try eassumption; try (unfold U_IMG_END; lia);
      try reflexivity;
      try (rewrite rget_lof by lia;
           match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
             let r := eval cbv in (Z.of_nat k) in
             replace (Z_to_bv 5 (Z.of_nat k)) with (Z_to_bv 5 r) by reflexivity end;
           first [ assumption
                 | match goal with H : getr _ ?r = ?v |- getr _ ?r' = ?v =>
                     replace r' with r by (apply bv_eq; reflexivity); exact H end ]).
    intros l' M' Hl' Hse Ha0 Hw HU HG. rewrite rget_lof by lia.
    replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : reg) by (apply bv_eq; reflexivity). rewrite Hra, Hret.
    apply reach_done. unfold Post. repeat split; assumption. }
  destruct (reach_exF USEGS rom _ _ F fc _ _ HR) as (pc' & regs' & l' & M' & Hms & HRR & HP).
  destruct HP as (-> & Hse & Ha0 & Hw & HU & HG).
  assert (E10 : getr regs' 10%bv = rget l' 10) by (apply (rrel_getr regs' l' 10 HRR); lia).
  exists regs', M'. split; [exact Hms|]. rewrite E10. repeat split; try assumption.
  intros r Hr. eapply same_except_getr; eassumption.
Qed.

Ltac lof_reg :=
  rewrite rget_lof by lia;
  match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
    let r := eval cbv in (Z.of_nat k) in
    replace (Z_to_bv 5 (Z.of_nat k)) with (Z_to_bv 5 r) by reflexivity end;
  match goal with H : getr _ ?r = ?v |- getr _ ?r' = ?v =>
    replace r' with r by (apply bv_eq; reflexivity); exact H end.

(* [comment removed for export] *)
Theorem a2u_loop_spec_u : forall regs F fc M rom S b len N out sb (eb : word),
  getr regs 2%bv = W (S - 2240) -> getr regs 8%bv = W S -> getr regs 19%bv = W b ->
  cell USEGS M (S - 2216) 8 (W 0) -> cell USEGS M (S - 2216 + 8) 8 (W out) -> cell USEGS M (S - 2216 + 16) 8 (W 0) ->
  cell USEGS M (S - 2216 + 24) 8 (W 0) -> cell USEGS M (S - 2216 + 32) 8 (W 16) -> cell USEGS M (S - 2216 + 40) 8 (W sb) ->
  cell USEGS M (S - 2216 + 48) 1 eb -> (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 -> 0 < sb < 2 ^ 64 ->
  0 <= len < 2 ^ 31 -> len < N -> 0 < b -> b + N < 2 ^ 63 -> rd_ok M b N ->
  M (W (b + len)) = Some (Z_to_bv 8 0) -> (b + len) / 8 * 8 + 8 <= b + N ->
  img_ok M 0x3a628 0x3a630 -> img_ok M 0x3a660 0x3a668 -> img_ok M 0x1e107 0x1e10c ->
  0x354000 <= S - 2400 -> S < 2 ^ 63 ->
  wr_ok USEGS M (S - 2400) 184 -> wr_ok USEGS M (S - 2200) 16 -> wr_ok USEGS M (S - 2160) 2048 ->
  0x354000 <= out -> out + 16 < 2 ^ 63 -> wr_ok USEGS M out 16 ->
  (out + 16 <= S - 2400 \/ S <= out) -> (b + N <= S - 2400 \/ S <= b) -> (b + N <= out \/ out + 16 <= b) ->
  S mod 8 = 0 ->
  exists regs' M',
    msteps USEGS (mkstF regs F fc (W 0x2158ec) M rom) (mkstF regs' F fc (W 0x215b8c) M' rom)
    /\ getr regs' 2%bv = getr regs 2%bv /\ getr regs' 3%bv = getr regs 3%bv
    /\ getr regs' 4%bv = getr regs 4%bv /\ getr regs' 8%bv = getr regs 8%bv
    /\ (forall x, ~ a2u_FP S out x -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros regs F fc M rom S b len N out sb eb H2 H8 H19 C0 C8 C16 C24 C32 C40 C48 Heb Hsb Hlen HlenN Hb HbN Hrd
         Hnul Hslack Hi1 Hi2 Hi3 HS HS2 Hw1 Hw2 Hw3 Hout Hout2 Hwo Hdo Hdb Hdbo HS8.
  set (B := fun i : Z => match M (W (b + i)) with Some x => x | None => Z_to_bv 8 0 end).
  assert (HB : bytes_at M b N B).
  { intros i Hi. unfold B. destruct (M (W (b + i))) as [x|] eqn:E; [reflexivity|]. exfalso. exact (Hrd i Hi E). }
  assert (HBlen : bv_unsigned (B len) = 0) by (unfold B; rewrite Hnul; reflexivity).
  pose (Post := fun (pc' : word) (l' : regfile) (M' : mem) =>
     pc' = W 0x215b8c /\ same_except KSL (lof regs) l' /\ rget l' 2 = W (S - 2240) /\ rget l' 8 = W S
     /\ unch M M' (a2u_FP S out) /\ mem_grows M M').
  assert (HR : reach USEGS rom (W 0x2158ec) (lof regs) M Post).
  { eapply (a2u_loop_cps rom Post M S b len N out sb eb B); try eassumption; try (unfold U_IMG_END; lia);
      try reflexivity; try lof_reg.
    - unfold pkt_at. repeat split; assumption.
    - intros l' M' Hl' Hse Hsp Hs0 HU HG. apply reach_done. unfold Post. repeat split; assumption. }
  destruct (reach_exF USEGS rom _ _ F fc _ _ HR) as (pc' & regs' & l' & M' & Hms & HRR & HP).
  destruct HP as (-> & Hse & Hsp & Hs0 & HU & HG).
  exists regs', M'. split; [exact Hms|].
  assert (E2 : getr regs' 2%bv = rget l' 2) by (apply (rrel_getr regs' l' 2 HRR); lia).
  assert (E8 : getr regs' 8%bv = rget l' 8) by (apply (rrel_getr regs' l' 8 HRR); lia).
  rewrite E2, E8, Hsp, Hs0, H2, H8. repeat split; try reflexivity; try assumption.
  - apply (same_except_getr KSL regs regs' l' HRR Hse). cbv. intuition discriminate.
  - apply (same_except_getr KSL regs regs' l' HRR Hse). cbv. intuition discriminate.
Qed.

Print Assumptions decode_spec_u.
Print Assumptions a2u_loop_spec_u.
