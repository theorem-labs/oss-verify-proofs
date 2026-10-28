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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatPopulate1_b BatPopulate2_b.
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

(* [comment removed for export] *)
Fixpoint art_carve (M : word -> option byte) (E au sz i : Z) (k : nat) : word -> option byte :=
  match k with O => M | S k' => art_carve (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) E au sz (i + 1) k' end.

Lemma art_carve_grows : forall k M E au sz i, mem_grows M (art_carve M E au sz i k).
Proof. induction k as [|k IH]; intros; cbn [art_carve]. apply mem_grows_refl. eapply mem_grows_trans; [apply Wn_grows | apply IH]. Qed.
Lemma art_carve_outside : forall k M E au sz i (x : word), 0 <= i -> 0 <= E - 4 * (i + Z.of_nat k) -> E < 2 ^ 64 ->
  ~ (E - 4 * (i + Z.of_nat k) <= bv_unsigned x < E - 4 * i) -> art_carve M E au sz i k x = M x.
Proof.
  induction k as [|k IH]; intros M E au sz i x Hi Hlo Hhi N; cbn [art_carve]. reflexivity.
  rewrite Nat2Z.inj_succ in Hlo, N. rewrite IH; [|lia|lia|lia|lia]. rewrite Wn_outside; [reflexivity|lia|cbn; lia|cbn; lia].
Qed.
Lemma cell_carve_other : forall k M E au sz i b m u, 0 <= i -> 0 <= E - 4 * (i + Z.of_nat k) -> E < 2 ^ 64 -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 ->
  apart (E - 4 * (i + Z.of_nat k)) (4 * Z.of_nat k) b (Z.of_nat m) -> cellA M b m u -> cellA (art_carve M E au sz i k) b m u.
Proof.
  induction k as [|k IH]; intros M E au sz i b m u Hi Hlo Hhi Hb Hm A C; cbn [art_carve]. exact C.
  rewrite Nat2Z.inj_succ in Hlo, A. unfold apart in A. apply IH; [lia|lia|lia|lia|lia|unfold apart; lia|].
  apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|exact C].
Qed.
(* [comment removed for export] *)
Lemma cell_carve_hit : forall k M E au sz i j, 0 <= i -> 0 <= E - 4 * (i + Z.of_nat k) -> E < 2 ^ 64 -> i <= j < i + Z.of_nat k ->
  cellA (art_carve M E au sz i k) (E - 4 * (j + 1)) 4 ((au + j * sz) / 16).
Proof.
  induction k as [|k IH]; intros M E au sz i j Hi Hlo Hhi Hj; cbn [art_carve]. lia.
  rewrite Nat2Z.inj_succ in Hlo, Hj. destruct (Z.eq_dec j i) as [->|NE].
  - apply cell_carve_other; [lia|lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; cbn; lia.
  - apply IH; lia.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_pop_loop : forall (k : nat) regs (M rom : word -> option byte) (E au sz i new : Z),
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 E -> getr regs 12 = Z_to_bv 64 (au + i * sz) -> getr regs 19 = Z_to_bv 64 new -> getr regs 21 = Z_to_bv 64 sz ->
  new = i + Z.of_nat k -> (1 <= k)%nat -> 0 <= i -> 0 <= au -> 32 <= sz <= 65536 -> au + new * sz <= 2 ^ 32 -> 0x696000 <= E - 4 * new -> E < 2 ^ 47 ->
  wrA M (E - 4 * new) (4 * Z.of_nat k) ->
  exists regs',
    msteps ASEGS (mkst regs (0x57a50 : word) M rom) (mkst regs' (0x57a70 : word) (art_carve M E au sz i k) rom)
    /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).
Proof.
  induction k as [|k IH]; intros regs M rom E au sz i new H10 H11 H12 H19 H21 Enew Hk Hi Hau Hsz Hfit Hlo Hhi W. lia.
  rewrite Nat2Z.inj_succ in Enew, W.
  assert (Hisz : 0 <= i * sz <= new * sz) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_r; lia]).
  assert (Hq : 0 <= (au + i * sz) / 16 < 2 ^ 28).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x57a50 : word) M rom) (mkst regs1 (0x57a6c : word) (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom)
            /\ getr regs1 10 = Z_to_bv 64 (i + 1) /\ getr regs1 11 = Z_to_bv 64 E /\ getr regs1 12 = Z_to_bv 64 (au + (i + 1) * sz) /\ getr regs1 19 = Z_to_bv 64 new /\ getr regs1 21 = Z_to_bv 64 sz
            /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs1 r = getr regs r)).
  { eexists. split.
    - stepn F_57638 D_57638. rwH. rewrite art_zb_srli by lia. change (2 ^ 4) with 16.
      zstep F_5763c D_5763c. zstep F_57640 D_57640. zstep F_57644 D_57644. zstep F_57648 D_57648.
      replace (Z_to_bv 64 (E + (2 ^ 64 - 1 - i) * 2 ^ 2)) with (Z_to_bv 64 (E - 4 * (i + 1)))
        by (apply art_zb_eq; replace (E + (2 ^ 64 - 1 - i) * 2 ^ 2) with (E - 4 * (i + 1) + 4 * 2 ^ 64) by lia; rewrite Z_mod_plus_full; reflexivity).
      zsw F_5764c D_5764c (E - 4 * (i + 1)) ((au + i * sz) / 16) ltac:(eapply (wr_wok _ _ _ _ W); cbn; lia).
      zstep F_57650 D_57650. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
  destruct STEP as (regs1 & RUN1 & P10 & P11 & P12 & P19 & P21 & K1).
  destruct k as [|k2].
  - cbn [art_carve]. eexists. split.
    + eapply msteps_trans; [exact RUN1|]. zbft F_57654 D_57654. apply mst_refl.
    + intros r N10 N12 N14 N15. apply K1; assumption.
  - assert (RUNb : msteps ASEGS (mkst regs1 (0x57a6c : word) (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom) (mkst regs1 (0x57a50 : word) (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom)).
    { zbtk F_57654 D_57654. apply mst_refl. }
    destruct (IH regs1 (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom E au sz (i + 1) new P10 P11 P12 P19 P21 ltac:(lia) ltac:(lia) ltac:(lia) Hau Hsz Hfit Hlo Hhi
                 ltac:(apply wr_Wn; eapply wr_sub; [exact W|lia|lia])) as (regs' & RUN2 & K2).
    exists regs'. split.
    + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNb|]. cbn [art_carve]. exact RUN2.
    + intros r N10 N12 N14 N15. rewrite K2 by assumption. apply K1; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_pop_d_fn : forall regs (M rom : word -> option byte) (r rb sz au tot free_bytes : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 tot -> getr regs 18 = Z_to_bv 64 rb -> getr regs 20 = Z_to_bv 64 free_bytes -> getr regs 21 = Z_to_bv 64 sz ->
  0x696000 <= r -> r + 128 < 2 ^ 47 -> 0 <= rb -> rb + 2 ^ 32 < 2 ^ 47 -> 32 <= sz <= 65536 -> sz <= free_bytes < 2 ^ 64 -> 0 <= au < 2 ^ 64 -> 0 <= tot < 2 ^ 32 ->
  cellA M (r + 32) 8 au ->
  msteps ASEGS (mkst regs (0x57a28 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 9 (Z_to_bv 64 (tot * 2 ^ 2))) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (rb + 3758096384 + tot * 2 ^ 2))) 12 (Z_to_bv 64 au)) 13 (Z_to_bv 64 au)) (0x57a50 : word) M rom).
Proof.
  intros regs M rom r rb sz au tot free_bytes H10 H8 H9 H18 H20 H21 Hr Hr' Hrb Hrb' Hsz Hfb Hau Htot Cau.
  zbft F_57610 D_57610.
  zld F_57614 D_57614 (r + 32) Cau.
  zbft F_57618 D_57618.
  zstep F_5761c D_5761c. zstep F_57620 D_57620. zstep F_57624 D_57624. zstep F_57628 D_57628. zstep F_5762c D_5762c. zstep F_57630 D_57630. zstep F_57634 D_57634.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_pop_e_fn : forall regs (M rom : word -> option byte) (raw : word) (sp r sz new au nf mu am mm nsz g8 g9 g18 g19 g20 g21 g22 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 8 = Z_to_bv 64 r -> getr regs 13 = Z_to_bv 64 au -> getr regs 19 = Z_to_bv 64 new -> getr regs 21 = Z_to_bv 64 sz ->
  64 <= sp -> sp < 2 ^ 64 -> 0x696000 <= r -> r + 128 < 2 ^ 47 -> 32 <= sz <= 65536 -> 0 <= new -> nsz = new * sz -> 0 <= au -> au + nsz <= mu -> mu < 2 ^ 64 -> 0 <= nf -> nf + new < 2 ^ 64 ->
  0 <= am <= mm -> mm < 2 ^ 64 -> ret_ok raw ->
  0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 -> 0 <= g20 < 2 ^ 64 -> 0 <= g21 < 2 ^ 64 -> 0 <= g22 < 2 ^ 64 ->
  apart (sp - 64) 64 r 128 -> wrA M r 128 ->
  cellA M (r + 16) 8 nf -> cellA M (r + 48) 8 mu -> cellA M (r + 40) 8 am -> cellA M (r + 56) 8 mm ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 -> cellA M (sp - 56) 8 g21 -> cellA M (sp - 64) 8 g22 ->
  msteps ASEGS (mkst regs (0x57a70 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 1)) 13 (Z_to_bv 64 am)) 14 (Z_to_bv 64 mm)) 18 (Z_to_bv 64 g18)) 19 (Z_to_bv 64 g19)) 20 (Z_to_bv 64 g20)) 21 (Z_to_bv 64 g21)) 22 (Z_to_bv 64 g22))
          raw (Wn 1 (Wn 8 (Wn 8 M (r + 16) (nf + new)) (r + 32) (au + nsz)) (r + 68) 0) rom).
Proof.
  intros regs M rom raw sp r sz new au nf mu am mm nsz g8 g9 g18 g19 g20 g21 g22 H2 H8 H13 H19 H21 Hsp Hsp' Hr Hr' Hsz Hnew Ensz Hau Haumu Hmu Hnf Hnf' Ham Hmm Hret
         Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 A Wr Cnf Cmu Cam Cmm F8 F16 F24 F32 F40 F48 F56 F64.
  zld F_57658 D_57658 (r + 16) Cnf.
  zstep F_5765c D_5765c. rewrite <- Ensz.
  zld F_57660 D_57660 (r + 48) Cmu.
  zstep F_57664 D_57664. zstep F_57668 D_57668.
  zsd F_5766c D_5766c (r + 16) (nf + new) ltac:(rewok Wr).
  zsd F_57670 D_57670 (r + 32) (au + nsz) ltac:(rewok Wr).
  zbft F_57674 D_57674.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cam' : cellA X (r + 40) 8 am) by zcell; assert (Cmm' : cellA X (r + 56) 8 mm) by zcell end.
  zld F_57678 D_57678 (r + 40) Cam'. zld F_5767c D_5767c (r + 56) Cmm'.
  zbft F_57680 D_57680.
  zsb F_57684 D_57684 (r + 68) 0 ltac:(rewok Wr).
  zstep F_57688 D_57688. zstep F_5768c D_5768c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => set (ME := X) end.
  assert (TE : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> sp - 64 <= a -> a + Z.of_nat k <= sp -> cellA M a k v -> cellA ME a k v).
  { intros a k v Ha Hak Hlo Hhi C. unfold ME. unfold apart in A. do 3 (apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|]). exact C. }
  assert (E8 : cellA ME (sp - 8) 8 (U raw)) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F8]).
  assert (E16 : cellA ME (sp - 16) 8 g8) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F16]).
  assert (E24 : cellA ME (sp - 24) 8 g9) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F24]).
  assert (E32 : cellA ME (sp - 32) 8 g18) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F32]).
  assert (E40 : cellA ME (sp - 40) 8 g19) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F40]).
  assert (E48 : cellA ME (sp - 48) 8 g20) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F48]).
  assert (E56 : cellA ME (sp - 56) 8 g21) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F56]).
  assert (E64 : cellA ME (sp - 64) 8 g22) by (apply TE; [lia|cbn; lia|lia|cbn; lia|exact F64]).
  zld F_57690 D_57690 (sp - 8) E8. zld F_57694 D_57694 (sp - 16) E16. zld F_57698 D_57698 (sp - 24) E24. zld F_5769c D_5769c (sp - 32) E32.
  zld F_576a0 D_576a0 (sp - 40) E40. zld F_576a4 D_576a4 (sp - 48) E48. zld F_576a8 D_576a8 (sp - 56) E56. zld F_576ac D_576ac (sp - 64) E64.
  rewrite !Z_to_bv_bv_unsigned.
  zstep F_576b0 D_576b0.
  stepret F_576b4 D_576b4 raw ltac:(rwH; reflexivity).
  subst ME. zret.
Qed.

End FPX.
