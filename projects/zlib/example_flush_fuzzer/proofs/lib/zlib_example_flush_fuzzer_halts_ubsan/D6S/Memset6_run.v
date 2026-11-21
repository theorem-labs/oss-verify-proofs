(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import Segs6 Callee6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Lemma mulhu_u32 : forall c, 0 <= c -> (c * 2 ^ 56) mod 2 ^ 64 * 4311810304 / 2 ^ 64 = (c mod 2 ^ 8) * 16843009.
Proof.
  intros c Hc.
  replace (2 ^ 64) with (2 ^ 8 * 2 ^ 56) at 1 by reflexivity.
  rewrite Z.mul_mod_distr_r by lia.
  replace (c mod 2 ^ 8 * 2 ^ 56 * 4311810304) with ((c mod 2 ^ 8 * 16843009) * 2 ^ 64) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma rep4m_r : forall r, 0 <= r < 256 -> Z_to_le_bytes 4 (r * 16843009) = repeat (Z_to_bv 8 r) 4.
Proof.
  intros r Hr. apply bytes_eqb_eq.
  exact (allb_ok 256 (fun r => bytes_eqb (Z_to_le_bytes 4 (r * 16843009)) (repeat (Z_to_bv 8 r) 4))
           ltac:(vm_compute; reflexivity) r Hr).
Qed.

Lemma rep8m_r : forall r, 0 <= r < 256 ->
  Z_to_le_bytes 8 (Z.lor (r * 16843009 * 2 ^ 32) ((r * 16843009) mod 2 ^ 32)) = repeat (Z_to_bv 8 r) 8.
Proof.
  intros r Hr. apply bytes_eqb_eq.
  exact (allb_ok 256 (fun r => bytes_eqb (Z_to_le_bytes 8 (Z.lor (r * 16843009 * 2 ^ 32) ((r * 16843009) mod 2 ^ 32))) (repeat (Z_to_bv 8 r) 8))
           ltac:(vm_compute; reflexivity) r Hr).
Qed.

Lemma rep4m : forall c, Z_to_le_bytes 4 (c mod 2 ^ 8 * 16843009) = repeat (ms_bb c) 4.
Proof. intros c. unfold ms_bb. apply rep4m_r. apply Z.mod_pos_bound. lia. Qed.

Lemma rep8m : forall c,
  Z_to_le_bytes 8 (Z.lor (c mod 2 ^ 8 * 16843009 * 2 ^ 32) ((c mod 2 ^ 8 * 16843009) mod 2 ^ 32)) = repeat (ms_bb c) 8.
Proof. intros c. unfold ms_bb. apply rep8m_r. apply Z.mod_pos_bound. lia. Qed.

Lemma lor_lt_pow2 : forall a b k, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Ha Hb. split; [apply (proj2 (Z.lor_nonneg a b)); lia|].
  destruct (Z.eq_dec a 0) as [->|Ha0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.lor_0_r; lia|].
  assert (Hp : 0 < Z.lor a b).
  { pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)) as H0. destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [|lia].
    apply Z.lor_eq_0_l in E. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) k Hp)). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; [apply (proj1 (Z.log2_lt_pow2 a k ltac:(lia))) | apply (proj1 (Z.log2_lt_pow2 b k ltac:(lia)))]; lia.
Qed.

Definition ms6_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.

Section Walk.
Variable mem : word -> option byte.
Variables (s c n : Z) (ra : word).
Hypothesis Hret : ret_ok ra.
Hypothesis Hs : 0 <= s < 2 ^ 64.
Hypothesis Hsn : s + n < 2 ^ 64.
Hypothesis Hn : 0 <= n.
Hypothesis Hc : 0 <= c < 2 ^ 64.
Hypothesis Hmap : mapped mem s n.

Local Ltac post R HR Hms Hfr HF :=
  let A := fresh "A" in
  symex_reg HR (10%bv : reg) as A;
  rewrite ?mulhu_u32 in Hms by lia;
  rewrite ?rep1, ?rep4m in Hms;
  lazymatch type of Hms with
  | msteps _ _ (mkst _ _ ?T _) =>
      let L := reify_tower T in let b := tower_base T in
      exists R, (ctower b (ms_bb c) L); split; [exact Hms|]; clear Hms HR;
      assert (HF : Forall (cst_ok s (s + n)) L)
        by (repeat first [apply Forall_nil | apply Forall_cons]; unfold cst_ok; cbn [fst snd]; lia);
      split; [ clear Hfr A
             | split; [apply ctower_same; exact HF
             | split; [intros x Hx; apply ctower_grows; exact Hx
             | split; [ exact A
             | intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity ]]]]
  end.

Local Ltac mrun dirs :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  lazymatch goal with |- context [mkst ?regs _ _ _] =>
  symex s6_segs (CFG [] [] [EVar 1%nat] [0x27cdc] []) 70%nat dirs NoReads
    [(10, EVar 32); (11, EVar 33); (12, EVar 34)]
    [(32%nat, 2 ^ 64); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64)] NoRegions
    [s; c; n] NoVals F0 F0' (mkst regs (0x27c04 : word) mem s6_rom) R HR Hfr Hms;
  [ .. | match goal with H1 : getr regs 1 = ra |- _ => rewrite H1 in Hms end;
         let HF := fresh "HF" in post R HR Hms Hfr HF ]
  end.

Lemma ms_small : forall regs, n <= 8 ->
  getr regs 1 = ra -> getr regs 10 = zw s -> getr regs 11 = zw c -> getr regs 12 = zw n ->
  exists R m', msteps s6_segs (mkst regs (0x27c04 : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ filled m' s (s + n) (ms_bb c)
    /\ same_outside mem m' s (s + n)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ getr R 10 = zw s
    /\ (forall r : reg, reg_in r ms6_clob = false -> getr R r = getr regs r).
Proof.
  intros regs Hn8 H1 H10 H11 H12. pose proof Hmap as Hm. unfold mapped in Hm.
  destruct (Z.eq_dec n 0) as [Hz|Hz].
  { mrun [true]. replace (s + n) with s by lia. apply filled_nil. }
  destruct (Z_le_gt_dec n 2).
  { mrun [false; true].
    match goal with HF : Forall _ _ |- _ => fcoverT HF [iv (s) 1; iv (s + n + -1) 1] end. }
  destruct (Z_le_gt_dec n 6).
  { mrun [false; false; true].
    match goal with HF : Forall _ _ |- _ =>
      fcoverT HF [iv (s) 1; iv (s + 1) 1; iv (s + 2) 1; iv (s + n + -3) 1; iv (s + n + -2) 1; iv (s + n + -1) 1] end. }
  mrun [false; false; false; true].
  match goal with HF : Forall _ _ |- _ =>
    fcoverT HF [iv (s) 1; iv (s + 1) 1; iv (s + 2) 1; iv (s + 3) 1;
                iv (s + n + -4) 1; iv (s + n + -3) 1; iv (s + n + -2) 1; iv (s + n + -1) 1] end.
Qed.

Lemma ms_loop : forall (C : Z), Z_to_le_bytes 8 C = repeat (ms_bb c) 8 -> 0 <= C < 2 ^ 64 ->
  forall (q : nat) (cur rem : Z) regs m,
  getr regs 1 = ra -> getr regs 11 = zw cur -> getr regs 14 = zw rem -> getr regs 13 = zw 31 -> getr regs 12 = zw C ->
  32 * Z.of_nat (S q) <= rem < 32 * Z.of_nat (S q) + 32 ->
  0 <= cur -> cur + 32 * Z.of_nat (S q) < 2 ^ 64 ->
  (forall x : word, cur <= bv_unsigned x < cur + 32 * Z.of_nat (S q) -> m x <> None) ->
  exists R m', msteps s6_segs (mkst regs (0x27cdc : word) m s6_rom) (mkst R ra m' s6_rom)
    /\ filled m' cur (cur + 32 * Z.of_nat (S q)) (ms_bb c)
    /\ (forall x : word, ~ (cur <= bv_unsigned x < cur + 32 * Z.of_nat (S q)) -> m' x = m x)
    /\ (forall x, m x <> None -> m' x <> None)
    /\ getr R 10 = getr regs 10
    /\ (forall r : reg, reg_in r [11; 14]%bv = false -> getr R r = getr regs r).
Proof.
  intros C HC8 HC. induction q as [|q IH]; intros cur rem regs m H1 H11 H14 H13 H12 Hrem Hc0 Hc1 Hmq.
  - symex s6_segs (CFG [] [] [EVar 1%nat] [] []) 12%nat [false] NoReads
      [(11, EVar 32); (14, EVar 33); (13, ELit 31); (12, EVar 34)]
      [(32%nat, 2 ^ 64); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64)] NoRegions
      [cur; rem; C] NoVals F0 F0' (mkst regs (0x27cdc : word) m s6_rom) R HR Hfr Hms.
    all: try (change (Z.of_nat 1) with 1 in *; rewrite ?Z.mod_small by lia; lia).
    all: try (apply symex_store_ok; [lia|lia|lia|]; intros x Hx; apply Hmq; change (Z.of_nat 1) with 1; lia).
    rewrite H1 in Hms. rewrite !HC8 in Hms.
    lazymatch type of Hms with
    | msteps _ _ (mkst _ _ ?T _) =>
        let L := reify_tower T in
        change T with (ctower m (ms_bb c) L) in Hms;
        assert (HF : Forall (cst_ok cur (cur + 32)) L)
          by (repeat first [apply Forall_nil | apply Forall_cons]; unfold cst_ok; cbn [fst snd]; lia)
    end.
    eexists R, _. split; [exact Hms|]. change (Z.of_nat 1) with 1. replace (cur + 32 * 1) with (cur + 32) by lia.
    split; [fcoverT HF [iv cur 8; iv (cur + 8) 8; iv (cur + 16) 8; iv (cur + 24) 8]|].
    split; [intros x Hx; apply (ctower_same _ _ _ _ _ HF); exact Hx|].
    split; [intros x Hx; apply ctower_grows; exact Hx|].
    split; [apply Hfr; reflexivity|]. intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity.
  - symex s6_segs (CFG [] [] [EVar 1%nat] [0x27cdc] []) 12%nat [true] NoReads
      [(11, EVar 32); (14, EVar 33); (13, ELit 31); (12, EVar 34)]
      [(32%nat, 2 ^ 64); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64)] NoRegions
      [cur; rem; C] NoVals F0 F0' (mkst regs (0x27cdc : word) m s6_rom) R1 HR1 Hfr1 Hms1.
    all: try (rewrite ?Z.mod_small by lia; lia).
    all: try (apply symex_store_ok; [lia|lia|lia|]; intros x Hx; apply Hmq; lia).
    symex_reg HR1 (11%bv : reg) as A11. symex_reg HR1 (14%bv : reg) as A14.
    rewrite !HC8 in Hms1.
    lazymatch type of Hms1 with
    | msteps _ _ (mkst _ _ ?T _) =>
        let L := reify_tower T in
        change T with (ctower m (ms_bb c) L) in Hms1;
        assert (HF : Forall (cst_ok cur (cur + 32)) L)
          by (repeat first [apply Forall_nil | apply Forall_cons]; unfold cst_ok; cbn [fst snd]; lia)
    end.
    lazymatch type of Hms1 with
    | msteps _ _ (mkst _ _ ?m1 _) =>
    assert (F1 : filled m1 cur (cur + 32) (ms_bb c)) by (fcoverT HF [iv cur 8; iv (cur + 8) 8; iv (cur + 16) 8; iv (cur + 24) 8]);
    assert (S1 : same_outside m m1 cur (cur + 32)) by (apply ctower_same; exact HF);
    assert (G1 : forall x, m x <> None -> m1 x <> None) by (intros x Hx; apply ctower_grows; exact Hx);
    destruct (IH (cur + 32) (rem - 32) R1 m1 ltac:(rewrite (Hfr1 1%bv eq_refl); exact H1)
                 ltac:(rewrite A11; reflexivity)
                 ltac:(rewrite A14; f_equal; lia)
                 ltac:(rewrite (Hfr1 13%bv eq_refl); exact H13)
                 ltac:(rewrite (Hfr1 12%bv eq_refl); exact H12)
                 ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(intros x Hx; apply G1; apply Hmq; lia))
      as (R2 & m2 & Hms2 & F2 & S2 & G2 & B10 & Hfr2)
    end.
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] |].
    split.
    { apply (filled_join m2 cur (cur + 32) (cur + 32) (cur + 32 * Z.of_nat (S (S q))) (ms_bb c));
        [| replace (cur + 32 * Z.of_nat (S (S q))) with (cur + 32 + 32 * Z.of_nat (S q)) by lia; exact F2 | lia].
      eapply filled_transport; [exact F1 | exact F2 |]. exact S2. }
    split.
    { intros x Hx. rewrite S2 by lia. apply S1. lia. }
    split; [intros x Hx; apply G2, G1, Hx|].
    split; [rewrite B10; apply Hfr1; reflexivity|].
    intros r Hr. rewrite (Hfr2 r Hr). apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

Local Ltac linearize :=
  change (2 ^ 2) with 4 in *;
  let K := fresh "K" in let N1 := fresh "N1" in let B := fresh "B" in let N2 := fresh "N2" in
  let q1 := fresh "q1" in let q2 := fresh "q2" in
  let EK := fresh "EK" in let EN1 := fresh "EN1" in let EB := fresh "EB" in let EN2 := fresh "EN2" in
  destruct (memset_lin_facts s n) as (K & N1 & B & N2 & q1 & q2 & EK & EN1 & EB & EN2 & LK & LN1a & LN1b & LB & LN2a & LN2b);
  rewrite <- ?EK in *; rewrite <- ?EN1 in *; rewrite <- ?EB in *; rewrite <- ?EN2 in *;
  clear EK EN1 EB EN2.

Local Ltac bigside Hm :=
  rewrite ?Z.mod_small by lia;
  first [ lia
        | split; [lia|]; split; [lia|]; apply symex_store_ok; [lia | lia | lia | intros x Hx; apply Hm; lia]
        | apply symex_store_ok; [lia | lia | lia | intros x Hx; apply Hm; lia] ].

Local Ltac tr HF F2 S2 a k :=
  let F := fresh "FT" in
  assert (F : filled _ a (a + Z.of_nat k) (ms_bb c))
    by (eapply filled_transport; [ eapply (ctower_filled _ _ _ _ _ _ _ HF); prove_In | exact F2 | exact S2 ]).

Lemma ms_big : forall regs, 8 < n ->
  getr regs 1 = ra -> getr regs 10 = zw s -> getr regs 11 = zw c -> getr regs 12 = zw n ->
  exists R m', msteps s6_segs (mkst regs (0x27c04 : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ filled m' s (s + n) (ms_bb c)
    /\ same_outside mem m' s (s + n)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ getr R 10 = zw s
    /\ (forall r : reg, reg_in r ms6_clob = false -> getr R r = getr regs r).
Proof.
  intros regs Hn8 H1 H10 H11 H12. pose proof Hmap as Hm. unfold mapped in Hm.
  destruct (Z_le_gt_dec (Z.land (n - (0 - s) mod 4) (-4)) 8) as [C1|C1].
  { symex s6_segs (CFG [] [] [EVar 1%nat] [0x27cdc] []) 70%nat [false; false; false; false; true] NoReads
      [(10, EVar 32); (11, EVar 33); (12, EVar 34)]
      [(32%nat, 2 ^ 64); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64)] NoRegions
      [s; c; n] NoVals F0 F0' (mkst regs (0x27c04 : word) mem s6_rom) R HR Hfr Hms.
    all: linearize. all: try bigside Hm.
    rewrite H1 in Hms. clear Hm.
    post R HR Hms Hfr HF.
    fcoverT HF [iv (s) 1; iv (s + 1) 1; iv (s + 2) 1; iv (s + 3) 1;
                iv (s + K) 4; iv (s + K + N1 + -4) 4;
                iv (s + n + -4) 1; iv (s + n + -3) 1; iv (s + n + -2) 1; iv (s + n + -1) 1]. }
  destruct (Z_le_gt_dec (Z.land (n - (0 - s) mod 4) (-4)) 24) as [C2|C2].
  { symex s6_segs (CFG [] [] [EVar 1%nat] [0x27cdc] []) 70%nat [false; false; false; false; false; true] NoReads
      [(10, EVar 32); (11, EVar 33); (12, EVar 34)]
      [(32%nat, 2 ^ 64); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64)] NoRegions
      [s; c; n] NoVals F0 F0' (mkst regs (0x27c04 : word) mem s6_rom) R HR Hfr Hms.
    all: linearize. all: try bigside Hm.
    rewrite H1 in Hms. clear Hm.
    post R HR Hms Hfr HF.
    fcoverT HF [iv s 1; iv (s + 1) 1; iv (s + 2) 1; iv (s + 3) 1;
                iv (s + K) 4; iv (s + K + 4) 4; iv (s + K + 8) 4;
                iv (s + K + N1 + -12) 4; iv (s + K + N1 + -8) 4; iv (s + K + N1 + -4) 4;
                iv (s + n + -4) 1; iv (s + n + -3) 1; iv (s + n + -2) 1; iv (s + n + -1) 1]. }
  destruct (Z_lt_le_dec (Z.land (n - (0 - s) mod 4) (-4) - Z.land (s + (0 - s) mod 4) 4 - 24) 32) as [C3|C3].
  {
    symex s6_segs (CFG [] [] [EVar 1%nat] [0x27cdc] []) 70%nat [false; false; false; false; false; false; true] NoReads
      [(10, EVar 32); (11, EVar 33); (12, EVar 34)]
      [(32%nat, 2 ^ 64); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64)] NoRegions
      [s; c; n] NoVals F0 F0' (mkst regs (0x27c04 : word) mem s6_rom) R HR Hfr Hms.
    all: linearize. all: try bigside Hm.
    rewrite H1 in Hms. clear Hm.
    post R HR Hms Hfr HF.
    fcoverT HF [iv s 1; iv (s + 1) 1; iv (s + 2) 1; iv (s + 3) 1;
                iv (s + K) 4; iv (s + K + 4) 4; iv (s + K + 8) 4; iv (s + K + 12) 4; iv (s + K + 16) 4;
                iv (s + K + 20) 4; iv (s + K + 24) 4;
                iv (s + K + N1 + -28) 4; iv (s + K + N1 + -24) 4; iv (s + K + N1 + -20) 4; iv (s + K + N1 + -16) 4;
                iv (s + K + N1 + -12) 4; iv (s + K + N1 + -8) 4; iv (s + K + N1 + -4) 4;
                iv (s + n + -4) 1; iv (s + n + -3) 1; iv (s + n + -2) 1; iv (s + n + -1) 1]. }
  symex s6_segs (CFG [] [] [EVar 1%nat] [0x27cdc] []) 70%nat [false; false; false; false; false; false; false] NoReads
      [(10, EVar 32); (11, EVar 33); (12, EVar 34)]
      [(32%nat, 2 ^ 64); (33%nat, 2 ^ 64); (34%nat, 2 ^ 64)] NoRegions
      [s; c; n] NoVals F0 F0' (mkst regs (0x27c04 : word) mem s6_rom) R1 HR1 Hfr1 Hms1.
  all: match goal with
       | |- exists _, _ => symex_reg HR1 (10%bv : reg) as A10; symex_reg HR1 (11%bv : reg) as A11;
                           symex_reg HR1 (12%bv : reg) as A12; symex_reg HR1 (13%bv : reg) as A13;
                           symex_reg HR1 (14%bv : reg) as A14; clear HR1
       | _ => idtac end.
  all: linearize. all: try bigside Hm.
  assert (A1 : getr R1 1 = ra) by (rewrite (Hfr1 1%bv eq_refl); exact H1).
  rewrite ?mulhu_u32 in Hms1 by lia. rewrite ?mulhu_u32 in A12 by lia.
  rewrite ?rep1, ?rep4m in Hms1.
  lazymatch type of Hms1 with
  | msteps _ _ (mkst _ _ ?T _) =>
      let L := reify_tower T in
      change T with (ctower mem (ms_bb c) L) in Hms1;
      assert (HF : Forall (cst_ok s (s + n)) L)
        by (repeat first [apply Forall_nil | apply Forall_cons]; unfold cst_ok; cbn [fst snd]; lia)
  end.
  pose proof (Z.mod_pos_bound c (2 ^ 8) ltac:(lia)) as Hc8.
  lazymatch type of Hms1 with
  | msteps _ _ (mkst _ _ ?T1 _) =>
  destruct (ms_loop _ (rep8m c)
              ltac:(apply lor_lt_pow2; [lia | pose proof (Z.mod_pos_bound (c mod 2 ^ 8 * 16843009) (2 ^ 32) ltac:(lia)); lia])
              (Z.to_nat q2 - 1) (s + K + B + 24) (N1 - B - 24) R1 T1 A1
              ltac:(rewrite A11; f_equal; lia) ltac:(rewrite A14; f_equal; lia) A13 A12
              ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(intros x Hx; apply ctower_grows; apply Hm; lia))
    as (R2 & m2 & Hms2 & F2 & S2 & G2 & B10 & Hfr2)
  end.
  exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] |].
  split.
  { tr HF F2 S2 s 1%nat. tr HF F2 S2 (s + 1) 1%nat. tr HF F2 S2 (s + 2) 1%nat. tr HF F2 S2 (s + 3) 1%nat.
    tr HF F2 S2 (s + K) 4%nat. tr HF F2 S2 (s + K + 4) 4%nat. tr HF F2 S2 (s + K + 8) 4%nat.
    tr HF F2 S2 (s + K + 12) 4%nat. tr HF F2 S2 (s + K + 16) 4%nat. tr HF F2 S2 (s + K + 20) 4%nat.
    tr HF F2 S2 (s + K + 24) 4%nat.
    tr HF F2 S2 (s + K + N1 + -28) 4%nat. tr HF F2 S2 (s + K + N1 + -24) 4%nat. tr HF F2 S2 (s + K + N1 + -20) 4%nat.
    tr HF F2 S2 (s + K + N1 + -16) 4%nat. tr HF F2 S2 (s + K + N1 + -12) 4%nat. tr HF F2 S2 (s + K + N1 + -8) 4%nat.
    tr HF F2 S2 (s + K + N1 + -4) 4%nat.
    tr HF F2 S2 (s + n + -4) 1%nat. tr HF F2 S2 (s + n + -3) 1%nat. tr HF F2 S2 (s + n + -2) 1%nat. tr HF F2 S2 (s + n + -1) 1%nat.
    fcoverT HF [iv s 1; iv (s + 1) 1; iv (s + 2) 1; iv (s + 3) 1;
                iv (s + K) 4; iv (s + K + 4) 4; iv (s + K + 8) 4; iv (s + K + 12) 4; iv (s + K + 16) 4;
                iv (s + K + 20) 4; iv (s + K + 24) 4;
                (s + K + B + 24, s + K + B + 24 + 32 * Z.of_nat (S (Z.to_nat q2 - 1)));
                iv (s + K + N1 + -28) 4; iv (s + K + N1 + -24) 4; iv (s + K + N1 + -20) 4; iv (s + K + N1 + -16) 4;
                iv (s + K + N1 + -12) 4; iv (s + K + N1 + -8) 4; iv (s + K + N1 + -4) 4;
                iv (s + n + -4) 1; iv (s + n + -3) 1; iv (s + n + -2) 1; iv (s + n + -1) 1]. }
  split.
  { intros x Hx. rewrite S2 by lia. apply (ctower_same _ _ _ _ _ HF). exact Hx. }
  split; [intros x Hx; apply G2; apply ctower_grows; exact Hx|].
  split; [rewrite B10; exact A10|].
  intros r Hr. rewrite (Hfr2 r) by (eapply reg_in_sub; [|exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.

Theorem memset_walk : forall regs,
  getr regs 1 = ra -> getr regs 10 = zw s -> getr regs 11 = zw c -> getr regs 12 = zw n ->
  exists R m', msteps s6_segs (mkst regs (0x27c04 : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ filled m' s (s + n) (ms_bb c)
    /\ same_outside mem m' s (s + n)
    /\ (forall x, mem x <> None -> m' x <> None)
    /\ getr R 10 = zw s
    /\ (forall r : reg, reg_in r ms6_clob = false -> getr R r = getr regs r).
Proof.
  intros regs H1 H10 H11 H12.
  destruct (Z_le_gt_dec n 8); [apply ms_small | apply ms_big]; assumption || lia.
Qed.
End Walk.

Theorem memset_run6_ok : memset_run6.
Proof.
  unfold memset_run6.
  intros mem regs dst c n ra Hd Hn Hdn Hc Hmap Hret H1 H10 H11 H12.
  assert (G : forall (R : bvmap 5 word) (r : reg), bv_eqb r 0%bv = false -> getr R r = reg_get R r)
    by (intros R r E; unfold getr; rewrite E; reflexivity).
  rewrite <- (G regs 1%bv eq_refl) in H1. rewrite <- (G regs 10%bv eq_refl) in H10.
  rewrite <- (G regs 11%bv eq_refl) in H11. rewrite <- (G regs 12%bv eq_refl) in H12.
  destruct (memset_walk mem dst c n ra Hret ltac:(lia) Hdn Hn Hc Hmap regs H1 H10 H11 H12)
    as (R & m' & Hms & F & S & Gr & A & Hfr).
  exists R, m'. split; [replace (zw A6_MEMSET) with (0x27c04%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [rewrite <- (G R 10%bv eq_refl); exact A|].
  split; [intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity|].
  split; [exact F|]. split; [exact S | exact Gr].
Qed.
End FXG.
