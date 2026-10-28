(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b Ba0_code_r3ef18_4052c_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Definition art_pop_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
     (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22)).


Lemma art_land_m18 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709289472 = x / 2 ^ 18 * 2 ^ 18.
Proof.
  intros x Hx. change 18446744073709289472 with (Z.shiftl (Z.ones 46) 18).
  rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 18) as [L|G].
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
    replace (i - 18 + 18) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [L2|G2].
    + replace ((0 <=? i - 18) && (i - 18 <? 46))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply Bool.andb_true_r.
    + assert (Tf : Z.testbit x i = false).
      { destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
        apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
      rewrite Tf. reflexivity.
Qed.

Lemma art_class_size_facts : forall c, 1 <= c <= 30 -> 32 <= AsanTab.class_size c <= 65536 /\ AsanTab.class_size c mod 16 = 0.
Proof.
  intros c Hc.
  assert (H : forall x, In x (map (fun i => Z.of_nat i) (seq 1 30)) -> 32 <= AsanTab.class_size x <= 65536 /\ AsanTab.class_size x mod 16 = 0).
  { intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [vm_compute; repeat split; discriminate|]). destruct Hx. }
  apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma art_class_size_small : forall c, 1 <= c <= 16 -> AsanTab.class_size c = 32 * c.
Proof. intros c Hc. unfold AsanTab.class_size. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.

(* [comment removed for export] *)
Definition art_pop_szw (c : Z) : word :=
  v_add (v_and (v_srai (Z_to_bv 64 (c * 2 ^ 63)) 63) (v_srli (v_sll (Z_to_bv 64 512) (v_srli (Z_to_bv 64 (c + -16)) 1)) 1)) (v_sll (Z_to_bv 64 512) (v_srli (Z_to_bv 64 (c + -16)) 1)).
Lemma art_pop_szw_ok : forall c, 17 <= c <= 30 -> art_pop_szw c = Z_to_bv 64 (AsanTab.class_size c).
Proof.
  intros c Hc.
  assert (E : c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  repeat (destruct E as [->|E]; [apply bv_eq; vm_compute; reflexivity|]). subst c. apply bv_eq; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Definition art_pop_c_mem (M : word -> option byte) (sp t st r m1 m2 sv mu : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) 358868) (sp - 24) 535228) (t + 2872) (m1 + 1)) (t + 2880) (m2 + 262144)) (st + 24) (sv + 262144)) (r + 48) (mu + 262144).

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_pop_a1s_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia st c r req spb au mu need : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 st -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 13 = Z_to_bv 64 r -> getr regs 14 = Z_to_bv 64 req ->
  64 <= sp -> sp < 2 ^ 64 -> 0x696000 + 64 <= sp -> 0 <= ia -> ia + 4096 <= 0x696000 -> 0 <= st < 2 ^ 64 -> 1 <= c <= 16 -> 0x696000 <= r -> r + 128 < 2 ^ 47 ->
  1 <= req <= 8 -> need = AsanTab.class_size c * req -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= au -> au <= mu -> mu < au + need -> need <= 2 ^ 18 -> mu <= 2 ^ 32 ->
  apart (sp - 64) 64 r 128 ->
  wrA M (sp - 64) 64 -> cellA M (ia + 32) 8 spb -> cellA M (r + 32) 8 au -> cellA M (r + 48) 8 mu ->
  msteps ASEGS (mkst regs (0x57894 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 2 (Z_to_bv 64 (sp - 64))) 8 (Z_to_bv 64 r)) 9 (Z_to_bv 64 st)) 11 (Z_to_bv 64 (c * 2 ^ 32))) 13 (Z_to_bv 64 au)) 18 (Z_to_bv 64 (spb + c * 2 ^ 32))) 19 (Z_to_bv 64 (au + need))) 20 (Z_to_bv 64 mu)) 21 (Z_to_bv 64 (AsanTab.class_size c))) (0x57934 : word) (art_pop_frame M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia st c r req spb au mu need H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst Hc Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' Hmu A W Cspb Cau Cmu.
  zstep F_5747c D_5747c.
  zsd F_57480 D_57480 (sp - 8) (U raw) ltac:(rewok W). zsd F_57484 D_57484 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_57488 D_57488 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_5748c D_5748c (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_57490 D_57490 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_57494 D_57494 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_57498 D_57498 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_5749c D_5749c (sp - 64) (U (getr regs 22)) ltac:(rewok W).
  fold (art_pop_frame M sp raw regs).
  zstep F_574a0 D_574a0. zstep F_574a4 D_574a4.
  assert (Cspb' : cellA (art_pop_frame M sp raw regs) (ia + 32) 8 spb) by (unfold art_pop_frame; zcell).
  zld F_574a8 D_574a8 (ia + 32) Cspb'.
  zstep F_574ac D_574ac. zstep F_574b0 D_574b0.
  zbft F_574b4 D_574b4. zstep F_574b8 D_574b8. zbft F_574bc D_574bc.
  zstep F_574c0 D_574c0.
  assert (Cau' : cellA (art_pop_frame M sp raw regs) (r + 32) 8 au) by (unfold art_pop_frame; unfold apart in A; zcell).
  assert (Cmu' : cellA (art_pop_frame M sp raw regs) (r + 48) 8 mu) by (unfold art_pop_frame; unfold apart in A; zcell).
  zld F_574c4 D_574c4 (r + 32) Cau'. zld F_574c8 D_574c8 (r + 48) Cmu'.
  replace (c * 2 ^ 5) with (AsanTab.class_size c) by (rewrite art_class_size_small by lia; lia).
  zstep F_574cc D_574cc. rewrite <- Eneed. zstep F_574d0 D_574d0. zstep F_574d4 D_574d4.
  zbtk F_574d8 D_574d8.
  zret.
Qed.

#[using="Type"] Lemma art_pop_a1b_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ia st c r req spb au mu need : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 st -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 13 = Z_to_bv 64 r -> getr regs 14 = Z_to_bv 64 req ->
  64 <= sp -> sp < 2 ^ 64 -> 0x696000 + 64 <= sp -> 0 <= ia -> ia + 4096 <= 0x696000 -> 0 <= st < 2 ^ 64 -> 17 <= c <= 30 -> 0x696000 <= r -> r + 128 < 2 ^ 47 ->
  1 <= req <= 8 -> need = AsanTab.class_size c * req -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= au -> au <= mu -> mu < au + need -> need <= 2 ^ 18 -> mu <= 2 ^ 32 ->
  apart (sp - 64) 64 r 128 ->
  wrA M (sp - 64) 64 -> cellA M (ia + 32) 8 spb -> cellA M (r + 32) 8 au -> cellA M (r + 48) 8 mu ->
  msteps ASEGS (mkst regs (0x57894 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 2 (Z_to_bv 64 (sp - 64))) 8 (Z_to_bv 64 r)) 9 (Z_to_bv 64 st)) 11 (Z_to_bv 64 (c * 2 ^ 32))) 13 (Z_to_bv 64 au)) 15 (v_srai (Z_to_bv 64 (c * 2 ^ 63)) 63)) 16 (Z_to_bv 64 (c * 2 ^ 63))) 18 (Z_to_bv 64 (spb + c * 2 ^ 32))) 19 (Z_to_bv 64 (au + need))) 20 (Z_to_bv 64 mu)) 21 (Z_to_bv 64 (AsanTab.class_size c))) (0x57934 : word) (art_pop_frame M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ia st c r req spb au mu need H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst Hc Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' Hmu A W Cspb Cau Cmu.
  zstep F_5747c D_5747c.
  zsd F_57480 D_57480 (sp - 8) (U raw) ltac:(rewok W). zsd F_57484 D_57484 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_57488 D_57488 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
  zsd F_5748c D_5748c (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_57490 D_57490 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_57494 D_57494 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zsd F_57498 D_57498 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_5749c D_5749c (sp - 64) (U (getr regs 22)) ltac:(rewok W).
  fold (art_pop_frame M sp raw regs).
  zstep F_574a0 D_574a0. zstep F_574a4 D_574a4.
  assert (Cspb' : cellA (art_pop_frame M sp raw regs) (ia + 32) 8 spb) by (unfold art_pop_frame; zcell).
  zld F_574a8 D_574a8 (ia + 32) Cspb'.
  zstep F_574ac D_574ac. zstep F_574b0 D_574b0.
  zbft F_574b4 D_574b4. zstep F_574b8 D_574b8. zbtk F_574bc D_574bc.
  zstep F_574e0 D_574e0. zstep F_574e4 D_574e4. zstep F_574e8 D_574e8. zstep F_574ec D_574ec. zstep F_574f0 D_574f0. zstep F_574f4 D_574f4.
  zstep F_574f8 D_574f8. zstep F_574fc D_574fc. zstep F_57500 D_57500.
  fold (art_pop_szw c). rewrite (art_pop_szw_ok c Hc).
  destruct (art_class_size_facts c ltac:(lia)) as [Hsz _].
  assert (Cau' : cellA (art_pop_frame M sp raw regs) (r + 32) 8 au) by (unfold art_pop_frame; unfold apart in A; zcell).
  assert (Cmu' : cellA (art_pop_frame M sp raw regs) (r + 48) 8 mu) by (unfold art_pop_frame; unfold apart in A; zcell).
  zld F_57504 D_57504 (r + 32) Cau'. zld F_57508 D_57508 (r + 48) Cmu'.
  zstep F_5750c D_5750c. rewrite <- Eneed. zstep F_57510 D_57510. zstep F_57514 D_57514.
  zbft F_57518 D_57518.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_pop_a2z_fn : forall regs (M rom : word -> option byte) (ia : Z),
  getr regs 20 = Z_to_bv 64 0 -> getr regs 10 = Z_to_bv 64 ia -> 0 <= ia -> ia + 4096 <= 0x696000 ->
  cellA M (ia + 40) 4 0xffffffff ->
  msteps ASEGS (mkst regs (0x57934 : word) M rom) (mkst (regupd (regupd regs 11 (Z_to_bv 64 18446744073709551615)) 20 (Z_to_bv 64 0)) (0x57938 : word) M rom).
Proof.
  intros regs M rom ia H20 H10 Hia Hia' Crel.
  zbtk F_5751c D_5751c.
  zlw F_576d8 D_576d8 (ia + 40) Crel.
  stepb_tk F_576dc D_576dc ltac:(rwH; reflexivity).
  zstep F_577a0 D_577a0.
  stepn F_577a4 D_577a4.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_pop_a3_fn : forall regs (M rom : word -> option byte) (ia r rb au mu need mm : Z),
  getr regs 8 = Z_to_bv 64 r -> getr regs 10 = Z_to_bv 64 ia -> getr regs 18 = Z_to_bv 64 rb -> getr regs 19 = Z_to_bv 64 (au + need) -> getr regs 20 = Z_to_bv 64 mu ->
  0 <= ia -> ia + 4096 <= 0x696000 -> 0x696000 <= r -> r + 128 < 2 ^ 47 -> 0 <= rb -> rb + 2 ^ 32 < 2 ^ 47 ->
  0 <= au -> au <= mu -> mu < au + need -> need <= 2 ^ 18 -> 0 <= mm -> mm + mu + 2 ^ 18 <= 3758096384 ->
  cellA M (r + 56) 8 mm -> cellA M (ia + 56) 1 0 ->
  msteps ASEGS (mkst regs (0x57938 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x579b4 : bv 64)%bv) 11 (Z_to_bv 64 (mu + rb))) 12 (Z_to_bv 64 262144)) 13 (Z_to_bv 64 97009)) 19 (Z_to_bv 64 262144)) 20 (Z_to_bv 64 (mu + rb))) 22 (Z_to_bv 64 ia)) (0x95bcc : word) M rom).
Proof.
  intros regs M rom ia r rb au mu need mm H8 H10 H18 H19 H20 Hia Hia' Hr Hr' Hrb Hrb' Hau Haumu Hneed Hneed' Hmm Hex Cmm Cpm.
  zstep F_57520 D_57520. zstep F_57524 D_57524. zstep F_57528 D_57528. zstep F_5752c D_5752c.
  replace (Z_to_bv 64 (au + need + (2 ^ 64 - 1 - mu))) with (Z_to_bv 64 (au + need - mu - 1)) by (apply art_zb_eq; replace (au + need + (2 ^ 64 - 1 - mu)) with (au + need - mu - 1 + 1 * 2 ^ 64) by lia; rewrite Z_mod_plus_full; reflexivity).
  stepn F_57530 D_57530. rwH. rewrite art_zb_and by lia. rewrite art_land_m18 by lia. rewrite (Z.div_small (au + need - mu - 1)) by lia. change (0 * 2 ^ 18) with 0.
  zld F_57534 D_57534 (r + 56) Cmm.
  zstep F_57538 D_57538. zstep F_5753c D_5753c. zstep F_57540 D_57540. zstep F_57544 D_57544. zstep F_57548 D_57548. zstep F_5754c D_5754c.
  zbft F_57550 D_57550.
  zlbu F_57554 D_57554 (ia + 56) Cpm.
  zstep F_57558 D_57558.
  zbtk F_5755c D_5755c.
  zstep F_57584 D_57584. zstep F_57588 D_57588. zstep F_5758c D_5758c. zstep F_57590 D_57590. zstep F_57594 D_57594.
  stepn F_57598 D_57598.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_pop_a_run : forall regs (M rom : word -> option byte) (raw : word) (sp ia st c r req spb au mu need mm : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 11 = Z_to_bv 64 st -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 13 = Z_to_bv 64 r -> getr regs 14 = Z_to_bv 64 req ->
  64 <= sp -> sp < 2 ^ 64 -> 0x696000 + 64 <= sp -> 0 <= ia -> ia + 4096 <= 0x696000 -> 0 <= st < 2 ^ 64 -> 1 <= c <= 30 -> 0x696000 <= r -> r + 128 < 2 ^ 47 ->
  1 <= req <= 8 -> need = AsanTab.class_size c * req -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= au -> au <= mu -> mu < au + need -> need <= 2 ^ 18 ->
  0 <= mm -> mm + mu + 2 ^ 18 <= 3758096384 ->
  apart (sp - 64) 64 r 128 ->
  wrA M (sp - 64) 64 -> cellA M (ia + 32) 8 spb -> cellA M (r + 32) 8 au -> cellA M (r + 48) 8 mu -> cellA M (r + 56) 8 mm -> cellA M (ia + 56) 1 0 ->
  cellA M (ia + 40) 4 0xffffffff ->
  exists regs',
    msteps ASEGS (mkst regs (0x57894 : word) M rom) (mkst regs' (0x95bcc : word) (art_pop_frame M sp raw regs) rom)
    /\ getr regs' 1 = (0x579b4 : bv 64)%bv /\ getr regs' 2 = Z_to_bv 64 (sp - 64) /\ getr regs' 8 = Z_to_bv 64 r /\ getr regs' 9 = Z_to_bv 64 st
    /\ getr regs' 11 = Z_to_bv 64 (spb + c * 2 ^ 32 + mu) /\ getr regs' 12 = Z_to_bv 64 262144 /\ getr regs' 13 = Z_to_bv 64 97009
    /\ getr regs' 18 = Z_to_bv 64 (spb + c * 2 ^ 32) /\ getr regs' 19 = Z_to_bv 64 262144 /\ getr regs' 20 = Z_to_bv 64 (spb + c * 2 ^ 32 + mu)
    /\ getr regs' 21 = Z_to_bv 64 (AsanTab.class_size c) /\ getr regs' 22 = Z_to_bv 64 ia
    /\ (forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x).
Proof.
  intros regs M rom raw sp ia st c r req spb au mu need mm H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst Hc Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed'
         Hmm Hex A W Cspb Cau Cmu Cmm Cpm Crel.
  set (MF := art_pop_frame M sp raw regs).
  assert (TF : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= sp - 64 \/ sp <= a) -> cellA M a k v -> cellA MF a k v).
  { intros a k v Ha Hak O C. unfold MF, art_pop_frame. do 8 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
  assert (Cmm' : cellA MF (r + 56) 8 mm) by (apply TF; [lia|cbn; lia|unfold apart in A; cbn; lia|exact Cmm]).
  assert (Cpm' : cellA MF (ia + 56) 1 0) by (apply TF; [lia|cbn; lia|cbn; lia|exact Cpm]).
  assert (Crel' : cellA MF (ia + 40) 4 0xffffffff) by (apply TF; [lia|cbn; lia|cbn; lia|exact Crel]).
  (* [comment removed for export] *)
  assert (S1 : exists r1, msteps ASEGS (mkst regs (0x57894 : word) M rom) (mkst r1 (0x57934 : word) MF rom)
            /\ getr r1 2 = Z_to_bv 64 (sp - 64) /\ getr r1 8 = Z_to_bv 64 r /\ getr r1 9 = Z_to_bv 64 st /\ getr r1 10 = Z_to_bv 64 ia
            /\ getr r1 18 = Z_to_bv 64 (spb + c * 2 ^ 32) /\ getr r1 19 = Z_to_bv 64 (au + need) /\ getr r1 20 = Z_to_bv 64 mu /\ getr r1 21 = Z_to_bv 64 (AsanTab.class_size c)
            /\ (forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr r1 x = getr regs x)).
  { destruct (Z_le_gt_dec c 16) as [Hs|Hb].
    - eexists. split; [exact (art_pop_a1s_fn regs M rom raw sp ia st c r req spb au mu need H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst ltac:(lia) Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' ltac:(lia) A W Cspb Cau Cmu)|].
      repeat (split; [kept_solve|]). intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; kept_solve.
    - eexists. split; [exact (art_pop_a1b_fn regs M rom raw sp ia st c r req spb au mu need H1 H2 H10 H11 H12 H13 H14 Hsp Hsp' IMG Hia Hia' Hst ltac:(lia) Hr Hr' Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' ltac:(lia) A W Cspb Cau Cmu)|].
      repeat (split; [kept_solve|]). intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; kept_solve. }
  destruct S1 as (r1 & RUN1 & A2 & A8 & A9 & A10 & A18 & A19 & A20 & A21 & K1).
  (* [comment removed for export] *)
  assert (S2 : exists r2, msteps ASEGS (mkst r1 (0x57934 : word) MF rom) (mkst r2 (0x57938 : word) MF rom)
            /\ getr r2 2 = Z_to_bv 64 (sp - 64) /\ getr r2 8 = Z_to_bv 64 r /\ getr r2 9 = Z_to_bv 64 st /\ getr r2 10 = Z_to_bv 64 ia
            /\ getr r2 18 = Z_to_bv 64 (spb + c * 2 ^ 32) /\ getr r2 19 = Z_to_bv 64 (au + need) /\ getr r2 20 = Z_to_bv 64 mu /\ getr r2 21 = Z_to_bv 64 (AsanTab.class_size c)
            /\ (forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr r1 x)).
  { destruct (Z.eq_dec mu 0) as [Ez|Nz].
    - subst mu. eexists. split; [exact (art_pop_a2z_fn r1 MF rom ia A20 A10 Hia Hia' Crel')|].
      repeat (split; [kept_solve|]). intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; kept_solve.
    - exists r1. split.
      { zbft F_5751c D_5751c. apply mst_refl. }
      repeat (split; [assumption|]). intros; reflexivity. }
  destruct S2 as (r2 & RUN2 & B2 & B8 & B9 & B10 & B18 & B19 & B20 & B21 & K2).
  pose proof (art_pop_a3_fn r2 MF rom ia r (spb + c * 2 ^ 32) au mu need mm B8 B10 B18 B19 B20 Hia Hia' Hr Hr' ltac:(lia) ltac:(lia) Hau Haumu Hneed Hneed' Hmm Hex Cmm' Cpm') as RUN3.
  eexists. split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3. }
  split; [gres; reflexivity|]. repeat (split; [kept_solve|]).
  intros x Hx. rewrite <- (K1 x Hx), <- (K2 x Hx). cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_pop_b_fn : forall regs (M rom : word -> option byte) (p : Z),
  getr regs 10 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 262144 -> 0 < p < 2 ^ 64 ->
  msteps ASEGS (mkst regs (0x579b4 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 (0x579d0 : bv 64)%bv) 10 (Z_to_bv 64 p)) 11 (Z_to_bv 64 262144)) 12 (Z_to_bv 64 250)) 14 (Z_to_bv 64 p)) (0x7ab38 : word) M rom).
Proof.
  intros regs M rom p H10 H20 H19 Hp.
  zbft F_5759c D_5759c. zstep F_575a0 D_575a0. zbft F_575a4 D_575a4.
  zstep F_575a8 D_575a8. zstep F_575ac D_575ac. zstep F_575b0 D_575b0.
  stepn F_575b4 D_575b4.
  zret.
Qed.

#[using="Type"] Lemma art_zb_divu : forall x y, 0 <= x < 2 ^ 64 -> 0 < y < 2 ^ 64 -> v_divu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof. intros x y Hx Hy. unfold v_divu. rewrite !art_u_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_pop_c_fn : forall regs (M rom : word -> option byte) (sp tp key tsd ctx t ia st r rb sz au mu nf new rem m1 m2 sv : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 st -> getr regs 18 = Z_to_bv 64 rb ->
  getr regs 19 = Z_to_bv 64 262144 -> getr regs 21 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 ia ->
  32 <= sp -> sp < 2 ^ 64 -> 0x696000 + 32 <= sp -> 0 <= ia < 2 ^ 64 -> 4096 <= st -> st + 64 < 2 ^ 64 -> (st + 24) mod 8 = 0 -> 0x696000 <= r -> r + 128 < 2 ^ 47 -> 0 <= rb < 2 ^ 64 ->
  32 <= sz <= 65536 -> 0 <= au -> au <= mu -> mu + 262144 <= 2 ^ 32 -> mu + 262144 - au = new * sz + rem -> 0 <= rem < sz -> 0 <= new -> 0 <= nf < 2 ^ 32 ->
  0 <= m1 < 2 ^ 64 -> 0 <= m2 < 2 ^ 64 -> 0 <= sv < 2 ^ 64 -> 4096 <= t -> t + 4096 < 2 ^ 64 ->
  wrA M (sp - 32) 32 -> art_tsd M tp key tsd ctx t ->
  apart (sp - 32) 32 0x13f4a0 8 -> apart (sp - 32) 32 (tp - 88) 8 -> apart (sp - 32) 32 (tsd + 8 * key) 8 -> apart (sp - 32) 32 (ctx + 152) 8 ->
  apart (sp - 32) 32 (t + 2872) 16 -> apart (sp - 32) 32 (st + 24) 8 -> apart (sp - 32) 32 r 128 -> apart (t + 2872) 16 (st + 24) 8 -> apart (t + 2872) 16 r 128 -> apart (st + 24) 8 r 128 ->
  wrA M (t + 2872) 16 -> wrA M (st + 24) 8 -> wrA M r 128 ->
  cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 -> cellA M (st + 24) 8 sv -> cellA M (r + 48) 8 mu -> cellA M (r + 32) 8 au -> cellA M (r + 16) 8 nf ->
  msteps ASEGS (mkst regs (0x579d0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x57a28 : bv 64)%bv) 2 (Z_to_bv 64 sp)) 9 (Z_to_bv 64 (nf + new))) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 r)) 12 (Z_to_bv 64 rb)) 13 (Z_to_bv 64 (nf + new))) 19 (Z_to_bv 64 new)) 20 (Z_to_bv 64 (mu + 262144 - au)))
          (0x55558 : word) (art_pop_c_mem M sp t st r m1 m2 sv mu) rom).
Proof.
  intros regs M rom sp tp key tsd ctx t ia st r rb sz au mu nf new rem m1 m2 sv H2 H4 H8 H9 H18 H19 H21 H22 Hsp Hsp' IMG Hia Hst Hst' Hst8 Hr Hr' Hrb Hsz Hau Haumu Hmu Ediv Hrem Hnew Hnf
         Hm1 Hm2 Hsv Ht Ht' W TSD A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 Wt Wst Wr C1 C2 Csv Cmu Cau Cnf.
  stepn F_575b8 D_575b8.
  zcall (art_thread_stats_fn _ _ _ _ sp tp key tsd ctx t).
  change (U (358868 : bv 64)%bv) with 358868.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (MT := X) end.
  assert (TT : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> apart (sp - 32) 32 a (Z.of_nat k) -> cellA M a k v -> cellA MT a k v).
  { intros a k v Ha Hak O C. unfold MT. unfold apart in O. do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
  assert (WT : forall a k, wrA M a k -> wrA MT a k) by (intros a k Hw; unfold MT; do 2 apply wr_Wn; exact Hw).
  assert (C1' : cellA MT (t + 2872) 8 m1) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C1]).
  assert (C2' : cellA MT (t + 2880) 8 m2) by (apply TT; [lia|cbn; lia|unfold apart in A5 |- *; cbn; lia|exact C2]).
  zld F_575bc D_575bc (t + 2872) C1'. zld F_575c0 D_575c0 (t + 2880) C2'.
  zstep F_575c4 D_575c4. zstep F_575c8 D_575c8.
  zsd F_575cc D_575cc (t + 2872) (m1 + 1) ltac:(eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
  zsd F_575d0 D_575d0 (t + 2880) (m2 + 262144) ltac:(apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wt)); lia).
  zstep F_575d4 D_575d4. zstep F_575d8 D_575d8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csv' : cellA X (st + 24) 8 sv)
     by (unfold apart in A8; do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]); apply TT; [lia|cbn; lia|unfold apart in A6 |- *; cbn; lia|exact Csv]) end.
  zamoadd_d F_575dc D_575dc (st + 24) sv 262144 Csv' ltac:(do 2 apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wst)); lia).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (MS := X) end.
  assert (TS : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> r <= a -> a + Z.of_nat k <= r + 128 -> cellA M a k v -> cellA MS a k v).
  { intros a k v Ha Hak Hlo Hhi C. unfold MS. unfold apart in A7, A9, A10. do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). apply TT; [lia|lia|unfold apart; lia|exact C]. }
  assert (Cmu' : cellA MS (r + 48) 8 mu) by (apply TS; [lia|cbn; lia|lia|cbn; lia|exact Cmu]).
  assert (Cau' : cellA MS (r + 32) 8 au) by (apply TS; [lia|cbn; lia|lia|cbn; lia|exact Cau]).
  zld F_575e0 D_575e0 (r + 48) Cmu'. zld F_575e4 D_575e4 (r + 32) Cau'.
  zstep F_575e8 D_575e8.
  zsd F_575ec D_575ec (r + 48) (mu + 262144) ltac:(unfold MS; do 3 apply wok_Wn; eapply (wr_wok _ _ _ _ (WT _ _ Wr)); lia).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cnf' : cellA X (r + 16) 8 nf)
     by (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]; apply TS; [lia|cbn; lia|lia|cbn; lia|exact Cnf]) end.
  zld F_575f0 D_575f0 (r + 16) Cnf'.
  zstep F_575f4 D_575f4.
  stepn F_575f8 D_575f8; [rewrite H21, art_u_lit by lia; lia|]. rwH. rewrite art_zb_divu by lia. replace ((mu + 262144 - au) / sz) with new by (apply (Z.div_unique_pos _ _ new rem); lia).
  zstep F_575fc D_575fc. zstep F_57600 D_57600. zstep F_57604 D_57604. zstep F_57608 D_57608.
  stepn F_5760c D_5760c.
  unfold art_pop_c_mem. subst MS MT. zret.
Qed.

End FPX.
