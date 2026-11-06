(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac Pm8ArtLeaf Pm8ArtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_5e000_5f000 .
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8ArtPopulate1 Pm8ArtPopulate2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

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

Lemma cell_carve_hit : forall k M E au sz i j, 0 <= i -> 0 <= E - 4 * (i + Z.of_nat k) -> E < 2 ^ 64 -> i <= j < i + Z.of_nat k ->
  cellA (art_carve M E au sz i k) (E - 4 * (j + 1)) 4 ((au + j * sz) / 16).
Proof.
  induction k as [|k IH]; intros M E au sz i j Hi Hlo Hhi Hj; cbn [art_carve]. lia.
  rewrite Nat2Z.inj_succ in Hlo, Hj. destruct (Z.eq_dec j i) as [->|NE].
  - apply cell_carve_other; [lia|lia|lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; cbn; lia.
  - apply IH; lia.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_pop_loop : forall (k : nat) regs (M rom : word -> option byte) (E au sz i new : Z),
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 E -> getr regs 12 = Z_to_bv 64 (au + i * sz) -> getr regs 19 = Z_to_bv 64 new -> getr regs 21 = Z_to_bv 64 sz ->
  new = i + Z.of_nat k -> (1 <= k)%nat -> 0 <= i -> 0 <= au -> 32 <= sz <= 65536 -> au + new * sz <= 2 ^ 32 -> 0x6b3000 <= E - 4 * new -> E < 2 ^ 47 ->
  wrA M (E - 4 * new) (4 * Z.of_nat k) ->
  exists regs',
    msteps ASEGS (mkst regs (0x5e8c8 : word) M rom) (mkst regs' (0x5e8e8 : word) (art_carve M E au sz i k) rom)
    /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs' r = getr regs r).
Proof.
  induction k as [|k IH]; intros regs M rom E au sz i new H10 H11 H12 H19 H21 Enew Hk Hi Hau Hsz Hfit Hlo Hhi W. lia.
  rewrite Nat2Z.inj_succ in Enew, W.
  assert (Hisz : 0 <= i * sz <= new * sz) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_r; lia]).
  assert (Hq : 0 <= (au + i * sz) / 16 < 2 ^ 28).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  assert (STEP : exists regs1, msteps ASEGS (mkst regs (0x5e8c8 : word) M rom) (mkst regs1 (0x5e8e4 : word) (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom)
            /\ getr regs1 10 = Z_to_bv 64 (i + 1) /\ getr regs1 11 = Z_to_bv 64 E /\ getr regs1 12 = Z_to_bv 64 (au + (i + 1) * sz) /\ getr regs1 19 = Z_to_bv 64 new /\ getr regs1 21 = Z_to_bv 64 sz
            /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> getr regs1 r = getr regs r)).
  { eexists. split.
    - stepn F_5e878 D_5e878. rwH. rewrite art_zb_srli by lia. change (2 ^ 4) with 16.
      zstep F_5e87c D_5e87c. zstep F_5e880 D_5e880. zstep F_5e884 D_5e884. zstep F_5e888 D_5e888.
      replace (Z_to_bv 64 (E + (2 ^ 64 - 1 - i) * 2 ^ 2)) with (Z_to_bv 64 (E - 4 * (i + 1)))
        by (apply art_zb_eq; replace (E + (2 ^ 64 - 1 - i) * 2 ^ 2) with (E - 4 * (i + 1) + 4 * 2 ^ 64) by lia; rewrite Z_mod_plus_full; reflexivity).
      zsw F_5e88c D_5e88c (E - 4 * (i + 1)) ((au + i * sz) / 16) ltac:(eapply (wr_wok _ _ _ _ W); cbn; lia).
      zstep F_5e890 D_5e890. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]). intros; kept_solve. }
  destruct STEP as (regs1 & RUN1 & P10 & P11 & P12 & P19 & P21 & K1).
  destruct k as [|k2].
  - cbn [art_carve]. eexists. split.
    + eapply msteps_trans; [exact RUN1|]. zbft F_5e894 D_5e894. apply mst_refl.
    + intros r N10 N12 N14 N15. apply K1; assumption.
  - assert (RUNb : msteps ASEGS (mkst regs1 (0x5e8e4 : word) (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom) (mkst regs1 (0x5e8c8 : word) (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom)).
    { zbtk F_5e894 D_5e894. apply mst_refl. }
    destruct (IH regs1 (Wn 4 M (E - 4 * (i + 1)) ((au + i * sz) / 16)) rom E au sz (i + 1) new P10 P11 P12 P19 P21 ltac:(lia) ltac:(lia) ltac:(lia) Hau Hsz Hfit Hlo Hhi
                 ltac:(apply wr_Wn; eapply wr_sub; [exact W|lia|lia])) as (regs' & RUN2 & K2).
    exists regs'. split.
    + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNb|]. cbn [art_carve]. exact RUN2.
    + intros r N10 N12 N14 N15. rewrite K2 by assumption. apply K1; assumption.
Qed.

Lemma art_pop_d_fn : forall regs (M rom : word -> option byte) (r rb sz au tot free_bytes : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 r -> getr regs 9 = Z_to_bv 64 tot -> getr regs 18 = Z_to_bv 64 rb -> getr regs 20 = Z_to_bv 64 free_bytes -> getr regs 21 = Z_to_bv 64 sz ->
  0x6b3000 <= r -> r + 128 < 2 ^ 47 -> 0 <= rb -> rb + 2 ^ 32 < 2 ^ 47 -> 32 <= sz <= 65536 -> sz <= free_bytes < 2 ^ 64 -> 0 <= au < 2 ^ 64 -> 0 <= tot < 2 ^ 32 ->
  cellA M (r + 32) 8 au ->
  msteps ASEGS (mkst regs (0x5e8a0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 9 (Z_to_bv 64 (tot * 2 ^ 2))) 10 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (rb + 3758096384 + tot * 2 ^ 2))) 12 (Z_to_bv 64 au)) 13 (Z_to_bv 64 au)) (0x5e8c8 : word) M rom).
Proof.
  intros regs M rom r rb sz au tot free_bytes H10 H8 H9 H18 H20 H21 Hr Hr' Hrb Hrb' Hsz Hfb Hau Htot Cau.
  zbft F_5e850 D_5e850.
  zld F_5e854 D_5e854 (r + 32) Cau.
  zbft F_5e858 D_5e858.
  zstep F_5e85c D_5e85c. zstep F_5e860 D_5e860. zstep F_5e864 D_5e864. zstep F_5e868 D_5e868. zstep F_5e86c D_5e86c. zstep F_5e870 D_5e870. zstep F_5e874 D_5e874.
  zret.
Qed.

Lemma art_pop_e_fn : forall regs (M rom : word -> option byte) (raw : word) (sp r sz new au nf mu am mm nsz g8 g9 g18 g19 g20 g21 g22 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 8 = Z_to_bv 64 r -> getr regs 13 = Z_to_bv 64 au -> getr regs 19 = Z_to_bv 64 new -> getr regs 21 = Z_to_bv 64 sz ->
  64 <= sp -> sp < 2 ^ 64 -> 0x6b3000 <= r -> r + 128 < 2 ^ 47 -> 32 <= sz <= 65536 -> 0 <= new -> nsz = new * sz -> 0 <= au -> au + nsz <= mu -> mu < 2 ^ 64 -> 0 <= nf -> nf + new < 2 ^ 64 ->
  0 <= am <= mm -> mm < 2 ^ 64 -> ret_ok raw ->
  0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 -> 0 <= g20 < 2 ^ 64 -> 0 <= g21 < 2 ^ 64 -> 0 <= g22 < 2 ^ 64 ->
  apart (sp - 64) 64 r 128 -> wrA M r 128 ->
  cellA M (r + 16) 8 nf -> cellA M (r + 48) 8 mu -> cellA M (r + 40) 8 am -> cellA M (r + 56) 8 mm ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 -> cellA M (sp - 56) 8 g21 -> cellA M (sp - 64) 8 g22 ->
  msteps ASEGS (mkst regs (0x5e8e8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) 10 (Z_to_bv 64 1)) 11 (Z_to_bv 64 1)) 13 (Z_to_bv 64 am)) 14 (Z_to_bv 64 mm)) 18 (Z_to_bv 64 g18)) 19 (Z_to_bv 64 g19)) 20 (Z_to_bv 64 g20)) 21 (Z_to_bv 64 g21)) 22 (Z_to_bv 64 g22))
          raw (Wn 1 (Wn 8 (Wn 8 M (r + 16) (nf + new)) (r + 32) (au + nsz)) (r + 68) 0) rom).
Proof.
  intros regs M rom raw sp r sz new au nf mu am mm nsz g8 g9 g18 g19 g20 g21 g22 H2 H8 H13 H19 H21 Hsp Hsp' Hr Hr' Hsz Hnew Ensz Hau Haumu Hmu Hnf Hnf' Ham Hmm Hret
         Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 A Wr Cnf Cmu Cam Cmm F8 F16 F24 F32 F40 F48 F56 F64.
  zld F_5e898 D_5e898 (r + 16) Cnf.
  zstep F_5e89c D_5e89c. rewrite <- Ensz.
  zld F_5e8a0 D_5e8a0 (r + 48) Cmu.
  zstep F_5e8a4 D_5e8a4. zstep F_5e8a8 D_5e8a8.
  zsd F_5e8ac D_5e8ac (r + 16) (nf + new) ltac:(rewok Wr).
  zsd F_5e8b0 D_5e8b0 (r + 32) (au + nsz) ltac:(rewok Wr).
  zbft F_5e8b4 D_5e8b4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cam' : cellA X (r + 40) 8 am) by zcell; assert (Cmm' : cellA X (r + 56) 8 mm) by zcell end.
  zld F_5e8b8 D_5e8b8 (r + 40) Cam'. zld F_5e8bc D_5e8bc (r + 56) Cmm'.
  zbft F_5e8c0 D_5e8c0.
  zsb F_5e8c4 D_5e8c4 (r + 68) 0 ltac:(rewok Wr).
  zstep F_5e8c8 D_5e8c8. zstep F_5e8cc D_5e8cc.
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
  zld F_5e8d0 D_5e8d0 (sp - 8) E8. zld F_5e8d4 D_5e8d4 (sp - 16) E16. zld F_5e8d8 D_5e8d8 (sp - 24) E24. zld F_5e8dc D_5e8dc (sp - 32) E32.
  zld F_5e8e0 D_5e8e0 (sp - 40) E40. zld F_5e8e4 D_5e8e4 (sp - 48) E48. zld F_5e8e8 D_5e8e8 (sp - 56) E56. zld F_5e8ec D_5e8ec (sp - 64) E64.
  rewrite !Z_to_bv_bv_unsigned.
  zstep F_5e8f0 D_5e8f0.
  stepret F_5e8f4 D_5e8f4 raw ltac:(rwH; reflexivity).
  subst ME. zret.
Qed.

End FPX.
