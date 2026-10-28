(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import X_atexit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import I_ikit I_memchrw I_memcmpw RT_iface5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ISCA_FRAME := 2176%Z (only parsing).
Notation ISCA_DEPTH := 2256%Z (only parsing).

Definition icells_sca (m : mem) : Prop :=
  ro_cells asegs m 0x16a220 [C8 (Z_to_bv 64 0x205768)]
  /\ ro_cells asegs m 0x16a230 [C8 (Z_to_bv 64 0x173c38)]
  /\ ro_cells asegs m 0x173c38 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0x174918 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x20585d [C1 (Z_to_bv 8 0)].

Lemma icells_sca_cq : forall m, icells_sca m -> icells_cq m.
Proof. intros m (_ & C2 & C3 & _ & _). exact (conj C2 C3). Qed.

Definition sca_pre (bp bq : list Z) (k : nat) : Prop :=
  forall j, (j < k)%nat -> exists x y, nth_error bp j = Some x /\ nth_error bq j = Some y /\ zlower x = zlower y /\ x <> 0.

Lemma sca_pre_0 : forall bp bq, sca_pre bp bq 0.
Proof. intros bp bq j Hj. lia. Qed.

Lemma sca_pre_S : forall bp bq k x y, sca_pre bp bq k -> nth_error bp k = Some x -> nth_error bq k = Some y -> zlower x = zlower y -> x <> 0 ->
  sca_pre bp bq (S k).
Proof.
  intros bp bq k x y HP H1 H2 HE HX j Hj. destruct (Nat.eq_dec j k) as [->|NE]; [exists x, y; auto|]. apply HP. lia.
Qed.

Lemma sca_pre_tl : forall x1 x2 bp bq k, sca_pre (x1 :: bp) (x2 :: bq) (S k) -> sca_pre bp bq k.
Proof. intros x1 x2 bp bq k HP j Hj. destruct (HP (S j) ltac:(lia)) as (x & y & E1 & E2 & HE & NZ). exists x, y. cbn in E1, E2. auto. Qed.

Lemma scase_idx_step : forall x y bp bq K, zlower x = zlower y -> x <> 0 ->
  scase_idx (x :: bp) (y :: bq) (S K) = S (scase_idx bp bq K).
Proof.
  intros x y bp bq K HE NZ. cbn [scase_idx]. rewrite HE, Z.eqb_refl. rewrite (proj2 (Z.eqb_neq _ _) NZ). reflexivity.
Qed.

Lemma scase_idx_break : forall k K bp bq x y,
  (k < K)%nat -> sca_pre bp bq k -> nth_error bp k = Some x -> nth_error bq k = Some y ->
  (zlower x <> zlower y \/ x = 0) ->
  scase_idx bp bq K = k.
Proof.
  induction k as [|k IH]; intros K bp bq x y HK HP H1 H2 HB.
  - destruct K as [|K']; [lia|]. destruct bp as [|x1 bp']; [discriminate|]. destruct bq as [|y1 bq']; [discriminate|].
    cbn in H1, H2. injection H1 as ->. injection H2 as ->. cbn [scase_idx].
    destruct HB as [HB|HB].
    + rewrite (proj2 (Z.eqb_neq _ _) HB). reflexivity.
    + rewrite HB. cbn [Z.eqb negb]. rewrite andb_false_r. reflexivity.
  - destruct K as [|K']; [lia|].
    destruct (HP 0%nat ltac:(lia)) as (z1 & z2 & Hz1 & Hz2 & HE & Hnz).
    destruct bp as [|x1 bp']; [discriminate|]. destruct bq as [|y1 bq']; [discriminate|].
    cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
    rewrite (scase_idx_step _ _ _ _ _ HE Hnz). f_equal.
    apply (IH K' bp' bq' x y); [lia| exact (sca_pre_tl _ _ _ _ _ HP)| exact H1| exact H2| exact HB].
Qed.

Lemma scase_idx_full : forall K bp bq, sca_pre bp bq K -> scase_idx bp bq K = K.
Proof.
  induction K as [|K IH]; intros bp bq HP; [destruct bp, bq; reflexivity|].
  destruct (HP 0%nat ltac:(lia)) as (z1 & z2 & Hz1 & Hz2 & HE & Hnz).
  destruct bp as [|x1 bp']; [discriminate|]. destruct bq as [|y1 bq']; [discriminate|].
  cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
  rewrite (scase_idx_step _ _ _ _ _ HE Hnz). f_equal. apply IH. exact (sca_pre_tl _ _ _ _ _ HP).
Qed.

Lemma scase_idx_ge : forall k K bp bq, (k <= K)%nat -> sca_pre bp bq k -> (k <= scase_idx bp bq K)%nat.
Proof.
  induction k as [|k IH]; intros K bp bq HK HP; [lia|].
  destruct K as [|K']; [lia|].
  destruct (HP 0%nat ltac:(lia)) as (z1 & z2 & Hz1 & Hz2 & HE & Hnz).
  destruct bp as [|x1 bp']; [discriminate|]. destruct bq as [|y1 bq']; [discriminate|].
  cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
  rewrite (scase_idx_step _ _ _ _ _ HE Hnz). specialize (IH K' bp' bq' ltac:(lia) (sca_pre_tl _ _ _ _ _ HP)). lia.
Qed.

Lemma scase_idx_le : forall K bp bq, (scase_idx bp bq K <= K)%nat.
Proof.
  induction K as [|K IH]; intros bp bq; [destruct bp, bq; cbn; lia|].
  destruct bp as [|x1 bp']; [cbn; lia|]. destruct bq as [|y1 bq']; [cbn; lia|].
  cbn [scase_idx]. destruct (_ && _); [| lia]. specialize (IH bp' bq'). lia.
Qed.

Lemma scase_res_break : forall K bp bq k x y, (k < K)%nat -> sca_pre bp bq k ->
  nth_error bp k = Some x -> nth_error bq k = Some y -> (zlower x <> zlower y \/ x = 0) ->
  scase_idx bp bq K = k /\ scase_res bp bq K = zlower x - zlower y.
Proof.
  intros K bp bq k x y HK HP H1 H2 HB.
  pose proof (scase_idx_break k K bp bq x y HK HP H1 H2 HB) as E.
  split; [exact E|]. unfold scase_res. rewrite E. rewrite (proj2 (Nat.ltb_lt _ _) HK).
  rewrite (nth_error_nth _ _ _ H1), (nth_error_nth _ _ _ H2). reflexivity.
Qed.

Lemma scase_res_full : forall K bp bq, sca_pre bp bq K -> scase_idx bp bq K = K /\ scase_res bp bq K = 0.
Proof.
  intros K bp bq HP. pose proof (scase_idx_full K bp bq HP) as E.
  split; [exact E|]. unfold scase_res. rewrite E, Nat.ltb_irrefl. reflexivity.
Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma zlower_range : forall x, 0 <= x < 256 -> 0 <= zlower x < 256.
Proof. intros x Hx. unfold zlower. destruct (_ && _) eqn:E; [apply andb_prop in E as [E1 E2]; apply Z.leb_le in E1; apply Z.leb_le in E2|]; lia. Qed.

Lemma fold_zlower : forall x, 0 <= x < 256 ->
  Z_to_bv 64 (x + Z.shiftl (Z.b2z ((x + -65) mod 18446744073709551616 <? 26)) 5) = Z_to_bv 64 (zlower x).
Proof.
  intros x Hx. f_equal. unfold zlower.
  destruct (Z_lt_le_dec x 65) as [L|GE].
  - rewrite Z.mod_eq by lia. replace ((x + -65) / 18446744073709551616) with (-1) by (Z.div_mod_to_equations; lia).
    replace (_ <? 26) with false by (symmetry; apply Z.ltb_ge; lia). replace (65 <=? x) with false by (symmetry; apply Z.leb_gt; lia).
    change (Z.shiftl (Z.b2z false) 5) with 0. cbn [andb]. lia.
  - rewrite Z.mod_small by lia. replace (65 <=? x) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
    destruct (Z_lt_le_dec 90 x) as [L2|LE2].
    + replace (_ <? 26) with false by (symmetry; apply Z.ltb_ge; lia). replace (x <=? 90) with false by (symmetry; apply Z.leb_gt; lia).
      change (Z.shiftl (Z.b2z false) 5) with 0. lia.
    + replace (_ <? 26) with true by (symmetry; apply Z.ltb_lt; lia). replace (x <=? 90) with true by (symmetry; apply Z.leb_le; lia).
      change (Z.shiftl (Z.b2z true) 5) with 32. lia.
Qed.

Lemma isca_loop : forall (r k : nat) (n p q : Z) (bp bq : list Z)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  n = Z.of_nat (k + S r) -> n < 2^26 -> 0 <= p -> 0 <= q ->
  let idx := Z.of_nat (scase_idx bp bq (Z.to_nat n)) in
  p + Z.min n (idx + 1) <= 2^47 -> q + Z.min n (idx + 1) <= 2^47 ->
  bytes_at asegs m p (map (Z_to_bv 8) bp) -> bytes_at asegs m q (map (Z_to_bv 8) bq) ->
  Forall (fun c => 0 <= c < 256) bp -> Forall (fun c => 0 <= c < 256) bq ->
  Z.min n (idx + 1) <= Z.of_nat (length bp) -> Z.min n (idx + 1) <= Z.of_nat (length bq) ->
  sca_pre bp bq k -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a0' a1' : word) (x1 x2 : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1' a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 q) (Z_to_bv 64 p) s4 s5 s6 s7 (Z_to_bv 64 x2) (Z_to_bv 64 x1) s10
                    (Z_to_bv 64 idx) t3 t4 t5 t6)
               F (Z_to_bv 64 0x6cffc) fc None m (seg_rom asegs)
      /\ 0 <= x1 < 256 /\ 0 <= x2 < 256 /\ zlower x1 - zlower x2 = scase_res bp bq (Z.to_nat n))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 q) (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (Z.of_nat k)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x6cfb8) fc None m (seg_rom asegs)).
Proof.
  induction r as [|r IH]; intros k n p q bp bq ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m
    Hn HN P0 Q0 idx PH QH BP BQ FP FQ LP LQ HP MI;
  ( pose proof (scase_idx_ge k (Z.to_nat n) bp bq ltac:(lia) HP) as GE; unfold idx in *;
    destruct (nth_error bp k) as [x|] eqn:E1; [| apply nth_error_None in E1; lia];
    destruct (nth_error bq k) as [y|] eqn:E2; [| apply nth_error_None in E2; lia];
    pose proof (proj1 (Forall_forall _ _) FP x (nth_error_In _ _ E1)) as XR;
    pose proof (proj1 (Forall_forall _ _) FQ y (nth_error_In _ _ E2)) as YR; cbv beta in XR, YR;
    pose proof (bytes_at_nth1 asegs m p (map (Z_to_bv 8) bp) k (Z_to_bv 8 x) BP ltac:(rewrite nth_error_map, E1; reflexivity)) as BX;
    pose proof (ro_C1_of_bytes m _ _ BX) as CX;
    pose proof (bytes_at_nth1 asegs m q (map (Z_to_bv 8) bq) k (Z_to_bv 8 y) BQ ltac:(rewrite nth_error_map, E2; reflexivity)) as BY;
    pose proof (ro_C1_of_bytes m _ _ BY) as CY;
    pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
    assert (EUk : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia);
    assert (EUk1 : bv_unsigned (Z_to_bv 64 (Z.of_nat k + 1)) = Z.of_nat k + 1) by (apply unsigned_lit; lia);
    assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia);
    assert (EU1 : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia);
    assert (EU2 : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia);
    assert (EUx8 : bv_unsigned (Z_to_bv 8 x) = x) by (apply unsigned_lit8; lia);
    assert (EUy8 : bv_unsigned (Z_to_bv 8 y) = y) by (apply unsigned_lit8; lia);
    assert (EUx : bv_unsigned (Z_to_bv 64 x) = x) by (apply unsigned_lit; lia);
    assert (EUy : bv_unsigned (Z_to_bv 64 y) = y) by (apply unsigned_lit; lia);
    pose proof (zlower_range x XR) as FXR; pose proof (zlower_range y YR) as FYR;
    assert (EUfx : bv_unsigned (Z_to_bv 64 (zlower x)) = zlower x) by (apply unsigned_lit; lia);
    assert (EUfy : bv_unsigned (Z_to_bv 64 (zlower y)) = zlower y) by (apply unsigned_lit; lia);
    lstep; set (pk := p + Z.of_nat k) in *; lstep;
    lstep; set (qk := q + Z.of_nat k) in *; lstep;
    cbv beta in *; rewrite ?EUx8, ?EUy8 ).
  -
    lstep. if_cases K; zify_cond K; rewrite ?EUx in K; change (bv_unsigned z64) with 0 in K.
    +
      destruct (scase_res_break (Z.to_nat n) bp bq k x y ltac:(lia) HP E1 E2 (or_intror K)) as (RI & RR).
      apply evt_done. do 2 eexists. exists x, y. rewrite RI.
      split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
    + do 8 lstep. rewrite (fold_zlower x XR), (fold_zlower y YR).
      lstep. if_cases K2; zify_cond K2; rewrite ?EUfx, ?EUfy in K2.
      *
        destruct (scase_res_break (Z.to_nat n) bp bq k x y ltac:(lia) HP E1 E2 (or_introl K2)) as (RI & RR).
        apply evt_done. do 2 eexists. exists x, y. rewrite RI.
        split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
      * pose proof (sca_pre_S bp bq k x y HP E1 E2 K2 K) as HP1.
        lstep. lstep. if_false. lstep.
        destruct (scase_res_full (Z.to_nat n) bp bq ltac:(replace (Z.to_nat n) with (S k) by lia; exact HP1)) as (RI & RR).
        apply evt_done. do 2 eexists. exists x, y. rewrite RI. replace (Z.of_nat (Z.to_nat n)) with n by lia.
        split; [reflexivity|]. split; [lia| split; [lia|]]. rewrite RR. lia.
  -
    lstep. if_cases K; zify_cond K; rewrite ?EUx in K; change (bv_unsigned z64) with 0 in K.
    +
      destruct (scase_res_break (Z.to_nat n) bp bq k x y ltac:(lia) HP E1 E2 (or_intror K)) as (RI & RR).
      apply evt_done. do 2 eexists. exists x, y. rewrite RI.
      split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
    + do 8 lstep. rewrite (fold_zlower x XR), (fold_zlower y YR).
      lstep. if_cases K2; zify_cond K2; rewrite ?EUfx, ?EUfy in K2.
      *
        destruct (scase_res_break (Z.to_nat n) bp bq k x y ltac:(lia) HP E1 E2 (or_introl K2)) as (RI & RR).
        apply evt_done. do 2 eexists. exists x, y. rewrite RI.
        split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
      * pose proof (sca_pre_S bp bq k x y HP E1 E2 K2 K) as HP1.
        lstep. lstep. if_true.
        replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
        apply (IH (S k) n p q bp bq); [lia| lia| lia| lia| cbv zeta; lia| cbv zeta; lia| exact BP| exact BQ| exact FP| exact FQ| cbv zeta; lia| cbv zeta; lia| exact HP1| exact MI].
Qed.

Lemma isca_sloop1 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x6d334) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d324) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Lemma isca_sloop2 : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) (Z_to_bv 64 e) a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x6d3fc) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 e) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d3ec) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma isca_rip1 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - ISCA_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc asegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2176)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x6d118) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2256, sp - 2176)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2176))
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d33c) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2176)) = sp + -2176) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (RO N0) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma isca_chk1 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - ISCA_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p < 2^64 -> 0 <= n -> (p + n < 2^63 \/ n = 0) ->
  chk_ok m p n -> m2s_cells m -> icells_cq m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2176)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x6d118) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2256, sp - 2176)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2176))
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 p) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d0d0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN0 (AC & QW & RO) M2S (G2 & SHC) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (Z.eq_dec n 0) as [->|NZ].
  {
    lstep. lstep. lstep. if_true. lstep. if_false. lstep.
    apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST]. }
  assert (DN : p + n < 2^63) by lia. clear DN0.
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL].
  -
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (isca_rip1 sp p n); try assumption; lia.
  -
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    lstep. if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + n + -1) with (p + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    +
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + n + -1) / 8) with ((p + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p n AC ltac:(lia) (proj1 D0)) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      *
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isca_rip1 sp p n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (isca_sloop1 (Z.to_nat ((p + n + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isca_rip1 sp p n); try assumption; lia.
    + apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Lemma isca_rip2 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - ISCA_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p -> 0 < n -> p + n < 2^63 ->
  acc asegs m p n -> rng_ok p n -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2176)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 p) s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x6d170) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2256, sp - 2176)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2176))
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d404) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2176)) = sp + -2176) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (RO N0) as (RIM & N40).
  do 3 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. if_true.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma isca_chk2 : forall (sp p n : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2176) -> lo <= sp - ISCA_DEPTH -> kHighShadowEnd + 8 <= lo -> sp < 2^63 ->
  0 <= p < 2^64 -> 0 <= n -> (p + n < 2^63 \/ n = 0) ->
  chk_ok m p n -> m2s_cells m -> icells_cq m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2176)) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 p) s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x6d170) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2256, sp - 2176)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2176))
    (MS (mkR ra (Z_to_bv 64 (sp + -2176)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d128) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN0 (AC & QW & RO) M2S (G2 & SHC) MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2256, sp - 2176)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  destruct (Z.eq_dec n 0) as [->|NZ].
  {
    lstep. lstep. lstep. if_true. lstep. if_false. lstep.
    apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST]. }
  assert (DN : p + n < 2^63) by lia. clear DN0.
  lstep. lstep.
  destruct (Z_lt_le_dec 64 n) as [BIG|SMALL].
  -
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65) by (apply unsigned_lit; lia).
    lstep. if_true. lstep. if_true.
    apply (isca_rip2 sp p n); try assumption; lia.
  -
    assert (EU65 : bv_unsigned (Z_to_bv 64 (n + -65)) = n - 65 + 2^64) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia).
    lstep. if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 11 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (p + n + -1) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + n - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + n + -1) with (p + n - 1) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    +
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (p + n + -1) / 8) with ((p + n + -1) / 8 + 2147450880) by lia.
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p n AC ltac:(lia) (proj1 D0)) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + n + -1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      *
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isca_rip2 sp p n); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (isca_sloop2 (Z.to_nat ((p + n + -1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a2' & a3' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (isca_rip2 sp p n); try assumption; lia.
    + apply evt_done. do 17 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

End WithRIP.

Lemma chk_ok_zero : forall m p n, n = 0 -> chk_ok m p n.
Proof. intros m p n ->. split; [intros i Hi; lia| split; intros Hc; lia]. Qed.

Section Tail.
Hypothesis RIP : rip_stmt.

Lemma isca_tail2 : forall (usp q kk x1 x2 : Z) (lo : Z)
    (rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
    (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc (m0 m : mem) (junk : list byte),
  stk asegs m lo (usp + -2176) -> lo <= usp - ISCA_DEPTH -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -104) [C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
  rw_cells asegs m (usp + -2176) [CB 2072 junk] ->
  munch [(usp - 2256, usp)] m0 m -> wmono asegs m0 m ->
  0 <= q < 2^64 -> 0 <= kk -> (q + kk <= 2^47 \/ kk = 0) -> 0 <= x1 < 256 -> 0 <= x2 < 256 ->
  chk_ok m q kk -> m2s_cells m -> icells_cq m -> mem_inv asegs m ->
  evt asegs (frame_post rae (Z_to_bv 64 usp) gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc (zlower x1 - zlower x2) [(usp - 2256, usp)] lo m0)
    (MS (mkR ra (Z_to_bv 64 (usp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 usp) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 q) s3 s4 (Z_to_bv 64 kk) s6 s7 (Z_to_bv 64 x2) (Z_to_bv 64 x1) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d128) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until junk. intros ST LO LOLO SPH FRs FR MU WM Q0 K0 QK X1 X2 CQ M2S ICQ MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MUl.
  pose proof M2S as (M2a & M2b & M2c). pose proof ICQ as (G2 & SHC).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2176 : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  pose proof (zlower_range x1 X1) as FX1. pose proof (zlower_range x2 X2) as FX2.
  call (isca_chk2 RIP usp q kk); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CQ| exact M2S| exact ICQ| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2176) |- _ => rename H into ST2 end.
  do 8 lstep. rewrite (fold_zlower x1 X1), (fold_zlower x2 X2).
  assert (EUf1 : bv_unsigned (Z_to_bv 64 (zlower x1)) = zlower x1) by (apply unsigned_lit; lia).
  assert (EUf2 : bv_unsigned (Z_to_bv 64 (zlower x2)) = zlower x2) by (apply unsigned_lit; lia).
  lstep. do 5 lstep. lstep. lstep. lstep. lstep. do 13 lstep. lstep.
  release_frame FR ST2 (usp + -104). release_frame FRs ST2 usp.
  lstep.
  unfold frame_post. sys_finish.
  rewrite EU. exact ST2.
Qed.

Lemma isca_tail : forall (usp p q n idx kk x1 x2 : Z) (lo : Z)
    (rae s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s10 t3 t4 t5 t6 : word) F fc (m0 m : mem) (junk : list byte),
  stk asegs m lo (usp + -2176) -> lo <= usp - ISCA_DEPTH -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  rw_cells asegs m (usp + -104) [C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae] ->
  rw_cells asegs m (usp + -2176) [CB 2072 junk] ->
  munch [(usp - 2256, usp)] m0 m -> wmono asegs m0 m ->
  0 <= p < 2^64 -> 0 <= q < 2^64 -> 0 <= n < 2^26 -> 0 <= idx <= n -> kk = Z.min n (idx + 1) -> (p + kk <= 2^47 \/ kk = 0) -> (q + kk <= 2^47 \/ kk = 0) ->
  0 <= x1 < 256 -> 0 <= x2 < 256 ->
  chk_ok m p kk -> chk_ok m q kk -> m2s_cells m -> icells_cq m -> mem_inv asegs m ->
  evt asegs (frame_post rae (Z_to_bv 64 usp) gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc (zlower x1 - zlower x2) [(usp - 2256, usp)] lo m0)
    (MS (mkR ra (Z_to_bv 64 (usp + -2176)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 q) (Z_to_bv 64 p) s4 (Z_to_bv 64 kk) s6 s7 (Z_to_bv 64 x2) (Z_to_bv 64 x1) s10 (Z_to_bv 64 idx) t3 t4 t5 t6)
        F (Z_to_bv 64 0x6d0d0) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until junk. intros ST LO LOLO SPH FRs FR MU WM P0 Q0 NR IR KK PK QK X1 X2 CP CQ M2S ICQ MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MUl.
  pose proof M2S as (M2a & M2b & M2c). pose proof ICQ as (G2 & SHC).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2176 : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUi1 : bv_unsigned (Z_to_bv 64 (idx + 1)) = idx + 1) by (apply unsigned_lit; lia).
  assert (EUq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EUnq : bv_unsigned (Z_to_bv 64 (18446744073709551615 - q)) = 18446744073709551615 - q) by (apply unsigned_lit; lia).
  call (isca_chk1 RIP usp p kk); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CP| exact M2S| exact ICQ| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2176) |- _ => rename H into ST2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CQ' : chk_ok mm q kk)
      by (destruct (Z.eq_dec kk 0) as [Kz|Knz]; [apply chk_ok_zero; exact Kz|];
          apply (chk_ok_agree m mm q kk CQ ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MUl); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S' : m2s_cells mm) by (split; [| split]; assumption);
    assert (ICQ' : icells_cq mm) by (split; assumption)
  end.
  clear CP CQ M2S ICQ.
  lstep. lstep. if_cases K; zify_cond K.
  -
    lstep. lstep. rewrite (lxor_ones64 q) by lia. lstep. if_true.
    replace (Z_to_bv 64 n) with (Z_to_bv 64 kk) by (f_equal; lia).
    eapply isca_tail2; try eassumption; lia.
  -
    lstep. rewrite (lxor_ones64 q) by lia. lstep. if_false.
    replace (Z_to_bv 64 (idx + 1)) with (Z_to_bv 64 kk) by (f_equal; lia).
    eapply isca_tail2; try eassumption; lia.
Qed.
End Tail.

Lemma bytes_at_firstn_sca : forall m A (bs : list byte) k, bytes_at asegs m A bs -> bytes_at asegs m A (firstn k bs).
Proof.
  intros m A bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma Forall_firstn_sca : forall (P : Z -> Prop) l k, Forall P l -> Forall P (firstn k l).
Proof.
  intros P l k H. revert k. induction H as [|x l Hx Hl IH]; intros k; [rewrite firstn_nil; constructor|].
  destruct k as [|k]; [constructor| cbn; constructor; [exact Hx| apply IH]].
Qed.

Lemma scase_idx_firstn : forall K bp bq j, (scase_idx bp bq K < j \/ K <= j)%nat ->
  scase_idx (firstn j bp) (firstn j bq) K = scase_idx bp bq K.
Proof.
  induction K as [|K IH]; intros bp bq j HJ; [destruct bp, bq, j; reflexivity|].
  destruct j as [|j']; [cbn in HJ; lia|].
  destruct bp as [|x1 bp']; [reflexivity|]. destruct bq as [|y1 bq']; [cbn; destruct (firstn j' bp'); reflexivity|].
  cbn [firstn scase_idx]. cbn [scase_idx] in HJ.
  destruct (_ && _); [| reflexivity]. f_equal. apply IH. lia.
Qed.

Lemma nth_firstn_lt : forall (l : list Z) j i d, (i < j)%nat -> nth i (firstn j l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros j i d Hij; [rewrite firstn_nil; reflexivity|].
  destruct j as [|j]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma sca_trunc : forall n bp bq, 0 <= n ->
  let K := Z.to_nat n in
  let j := Z.to_nat (Z.min n (Z.of_nat (scase_idx bp bq K) + 1)) in
  scase_idx (firstn j bp) (firstn j bq) K = scase_idx bp bq K
  /\ scase_res (firstn j bp) (firstn j bq) K = scase_res bp bq K.
Proof.
  intros n bp bq N0 K j.
  pose proof (scase_idx_le K bp bq) as LE.
  assert (HJ : (scase_idx bp bq K < j \/ K <= j)%nat) by (unfold j, K in *; lia).
  pose proof (scase_idx_firstn K bp bq j HJ) as EI.
  split; [exact EI|]. unfold scase_res. rewrite EI. destruct (Nat.ltb_spec (scase_idx bp bq K) K) as [LT|GE]; [| reflexivity].
  rewrite !nth_firstn_lt by (unfold j, K in *; lia). reflexivity.
Qed.

Section Top.
Hypothesis RIP : rip_stmt.

Theorem istrncasecmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p q n : Z) (bp bq : list Z) (lo : Z),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 n ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISCA_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 <= p < 2^64 -> 0 <= q < 2^64 -> 0 <= n < 2^26 ->
  bytes_at asegs m p (map (Z_to_bv 8) bp) -> bytes_at asegs m q (map (Z_to_bv 8) bq) ->
  Forall (fun c => 0 <= c < 256) bp -> Forall (fun c => 0 <= c < 256) bq ->
  let kk := Z.min n (Z.of_nat (scase_idx bp bq (Z.to_nat n)) + 1) in
  kk <= Z.of_nat (length bp) -> kk <= Z.of_nat (length bq) -> (p + kk <= 2^47 \/ kk = 0) -> (q + kk <= 2^47 \/ kk = 0) ->
  (p + kk <= lo \/ bv_unsigned sp <= p \/ kk = 0) -> (q + kk <= lo \/ bv_unsigned sp <= q \/ kk = 0) ->
  chk_ok m p kk -> chk_ok m q kk -> m2s_cells m -> icells_sca m -> mem_inv asegs m ->
  evt asegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (scase_res bp bq (Z.to_nat n))
               [(bv_unsigned sp - ISCA_DEPTH, bv_unsigned sp)] lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 e_strncasecmp) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> -> ST LO LOLO SPH P0 Q0 NR BP BQ FP FQ kk LP LQ PK QK SEPP SEPQ CP CQ M2S IC MI.
  unfold kHighShadowEnd, e_strncasecmp in *.

  destruct (sca_trunc n bp bq ltac:(lia)) as (EI & ER). rewrite <- ER. subst kk.
  set (kk := Z.min n (Z.of_nat (scase_idx bp bq (Z.to_nat n)) + 1)) in *.
  set (j := Z.to_nat kk) in *.
  set (c1 := firstn j bp) in *. set (c2 := firstn j bq) in *.
  assert (BC1 : keep (bytes_at asegs m p (map (Z_to_bv 8) c1))) by (unfold c1; rewrite <- firstn_map; apply bytes_at_firstn_sca; exact BP).
  assert (BC2 : keep (bytes_at asegs m q (map (Z_to_bv 8) c2))) by (unfold c2; rewrite <- firstn_map; apply bytes_at_firstn_sca; exact BQ).
  assert (FC1 : Forall (fun c => 0 <= c < 256) c1) by (apply Forall_firstn_sca; exact FP).
  assert (FC2 : Forall (fun c => 0 <= c < 256) c2) by (apply Forall_firstn_sca; exact FQ).
  assert (LC1 : length c1 = j) by (unfold c1; rewrite firstn_length; unfold j; lia).
  assert (LC2 : length c2 = j) by (unfold c2; rewrite firstn_length; unfold j; lia).
  assert (EKK : Z.min n (Z.of_nat (scase_idx c1 c2 (Z.to_nat n)) + 1) = kk) by (rewrite EI; reflexivity).
  clear BP BQ FP FQ ER LP LQ. clearbody c1 c2. clear EI.
  set (idx := Z.of_nat (scase_idx c1 c2 (Z.to_nat n))) in *.
  assert (IDX : 0 <= idx <= n) by (pose proof (scase_idx_le (Z.to_nat n) c1 c2); unfold idx; lia).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (GCF & G2 & SHC & AI & SSC). pose proof M2S as (M2a & M2b & M2c).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2176 : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUp : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  assert (EUi1 : bv_unsigned (Z_to_bv 64 (idx + 1)) = idx + 1) by (apply unsigned_lit; lia).
  lstep.
  carve_frame 104%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  do 16 lstep. do 4 lstep. lstep.
  call try_init_spec; [assumption| rewrite EU2176; exact ST| rewrite EU2176; lia| rewrite ?EU2176; lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2176 in H; rename H into ST2 end.
  lstep. if_false.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BM1 : bytes_at asegs mm p (map (Z_to_bv 8) c1))
      by (unfold keep in BC1; apply (bytes_at_agree asegs m mm _ _ BC1); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; rewrite length_map, LC1 in Hy; unfold j in Hy; rewrite Z2Nat.id in Hy by lia; (split; [lia| exact I]));
    assert (BM2 : bytes_at asegs mm q (map (Z_to_bv 8) c2))
      by (unfold keep in BC2; apply (bytes_at_agree asegs m mm _ _ BC2); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; rewrite length_map, LC2 in Hy; unfold j in Hy; rewrite Z2Nat.id in Hy by lia; (split; [lia| exact I]));
    assert (CP' : chk_ok mm p kk)
      by (destruct (Z.eq_dec kk 0) as [Kz|Knz]; [apply chk_ok_zero; exact Kz|];
          apply (chk_ok_agree m mm p kk CP ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (CQ' : chk_ok mm q kk)
      by (destruct (Z.eq_dec kk 0) as [Kz|Knz]; [apply chk_ok_zero; exact Kz|];
          apply (chk_ok_agree m mm q kk CQ ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S' : m2s_cells mm) by (split; [| split]; assumption);
    assert (ICQ' : icells_cq mm) by (split; assumption)
  end.
  clear BC1 BC2 CP CQ M2S IC.
  lstep. if_cases K0; zify_cond K0.
  -
    do 4 lstep. lstep. lstep. if_true. lstep. lstep. rewrite (lxor_ones64 p) by lia. lstep. lstep. lstep. if_true.
    replace (scase_res c1 c2 (Z.to_nat n)) with (zlower 0 - zlower 0)
      by (replace (Z.to_nat n) with 0%nat by lia; unfold scase_res; destruct c1, c2; reflexivity).
    eapply (isca_tail RIP usp p q n 0 n 0 0 lo); try eassumption; try lia; replace n with kk by lia; assumption.
  -
    lstep.
    eapply evt_cut.
    { apply (isca_loop (Z.to_nat n - 1) 0 n p q c1 c2); [lia| lia| lia| lia| unfold idx in *; lia| unfold idx in *; lia| exact BM1| exact BM2| exact FC1| exact FC2
        | unfold idx, j in *; lia| unfold idx, j in *; lia| apply sca_pre_0| assumption]. }
    intros ms' (a0' & a1' & xa & xb & -> & X1 & X2 & RES). rewrite <- RES. fold idx.
    assert (EUi : bv_unsigned (Z_to_bv 64 idx) = idx) by (apply unsigned_lit; lia).
    lstep. if_cases K1; zify_cond K1.
    +
      lstep. lstep. if_false. lstep. lstep. rewrite (lxor_ones64 p) by lia. lstep. lstep. lstep. if_true.
      eapply (isca_tail RIP usp p q n idx n xa xb lo); try eassumption; try lia; replace n with kk by lia; assumption.
    +
      lstep. lstep. lstep. cbv beta. lstep. lstep. lstep. if_true. lstep. lstep. if_cases K2; zify_cond K2.
      *
        lstep. lstep. rewrite (lxor_ones64 p) by lia. lstep. lstep. lstep. if_true.
        eapply (isca_tail RIP usp p q n idx n xa xb lo); try eassumption; try lia; replace n with kk by lia; assumption.
      *
        lstep. rewrite (lxor_ones64 p) by lia. lstep. lstep. lstep. if_false.
        eapply (isca_tail RIP usp p q n idx (idx + 1) xa xb lo); try eassumption; try lia; replace (idx + 1) with kk by lia; assumption.
Qed.
End Top.
