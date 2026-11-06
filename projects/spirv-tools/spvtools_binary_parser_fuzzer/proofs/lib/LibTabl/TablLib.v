(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require MemSplit SymDrive3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition branch_at (segs : list Segment) (ss : sym_state) : option (branch_cond * expr * expr) :=
  match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
  | Some w =>
      match decode_any w with
      | Some (Branch c rs1 rs2 _, _) => Some (c, sr_get (s_regs ss) rs1, sr_get (s_regs ss) rs2)
      | _ => None
      end
  | None => None
  end.

Definition jalr_at (segs : list Segment) (ss : sym_state) : bool :=
  match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
  | Some w => match decode_any w with Some (Jalr _ _ _, _) => true | _ => false end
  | None => false
  end.

Ltac scd_exact := match goal with |- ?g => match goal with H : ?T |- _ => constr_eq T g; exact H end end.

Ltac xtree HR HK fuel stops nx ds reads sctac fin kill :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch goal with
      | |- context [@mkst ?fxg R (Z_to_bv 64 ?pc) M ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops (SCR ds reads []) (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let stop := eval vm_compute in (existsb (Z.eqb (s_pc ss')) stops) in
              lazymatch stop with
              | true =>
                  xrun HR HK fuel stops (SCR ds reads []) nx;
                  [ split_scs; first [ cbn [sc_denot]; scd_exact | assumption | sctac ] | fin ]
              | false =>
                  let br := eval vm_compute in (branch_at segs ss') in
                  lazymatch br with
                  | Some (?c, ?a, ?b) =>
                      let Hb := fresh "Hbr" in
                      destruct (branch_taken c (edenot E a) (edenot E b)) eqn:Hb;
                      [ first [ solve [kill]
                              | let ds' := eval vm_compute in (ds ++ [true]) in
                                xtree HR HK fuel stops nx ds' reads sctac fin kill ]
                      | first [ solve [kill]
                              | let ds' := eval vm_compute in (ds ++ [false]) in
                                xtree HR HK fuel stops nx ds' reads sctac fin kill ] ]
                  | None =>

                      let j := eval vm_compute in (jalr_at segs ss') in
                      lazymatch j with
                      | true =>
                          xrun HR HK fuel stops (SCR ds reads []) nx;
                          [ split_scs; first [ cbn [sc_denot]; scd_exact | assumption | sctac ] | fin ]
                      | false =>
                          let p := eval vm_compute in (s_pc ss') in
                          fail 1 "xtree: executor stuck at pc" p "which is neither a stop nor a branch nor a jalr"
                      end
                  end
              end
          end
      end
    end
  end.

Lemma signed_small : forall x, 0 <= x < 2 ^ 63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_signed. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. replace (2 ^ Z.of_N 64 `div` 2) with (2 ^ 63) by reflexivity. lia.
Qed.
Lemma br_lt : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !signed_small by lia. reflexivity. Qed.
Lemma br_ge : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !signed_small by lia. reflexivity. Qed.

Ltac zify_bool H :=
  lazymatch type of H with
  | (_ =? _)%Z = true => apply Z.eqb_eq in H
  | (_ =? _)%Z = false => apply Z.eqb_neq in H
  | (_ <? _)%Z = true => apply Z.ltb_lt in H
  | (_ <? _)%Z = false => apply Z.ltb_ge in H
  | negb _ = true => apply Bool.negb_true_iff in H; zify_bool H
  | negb _ = false => apply Bool.negb_false_iff in H; zify_bool H
  end.
Ltac br_facts :=
  repeat match goal with
  | H : branch_taken _ _ _ = _ |- _ =>
      evs_in H; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu, ?br_lt, ?br_ge, ?br_eq_sxw, ?br_ne_sxw in H by lia;
      first [ zify_bool H | revert H ]
  end;
  intros.

Ltac br_kill_all := idtac; exfalso; br_facts; lia.

Ltac br_kill :=
  idtac;
  exfalso;
  lazymatch goal with
  | H : branch_taken _ _ _ = _ |- _ =>
      evs_in H; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu, ?br_lt, ?br_ge in H by lia;
      zify_bool H; lia
  end.

Definition is_ret_at (segs : list Segment) (pc : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => (bv_unsigned w =? 0x8067)%Z
  | None => false
  end.

Lemma decode_ret : decode_any (0x8067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.

Lemma ret_run : forall {fx : FPState} segs R M rom pc (ret : word),
  is_ret_at segs pc = true -> getr R 1%bv = ret -> ret_ok ret ->
  msteps segs (@mkst fx R (Z_to_bv 64 pc) M rom) (@mkst fx R ret M rom).
Proof.
  intros fx segs R M rom pc ret Hf Hra Hret. unfold is_ret_at in Hf.
  destruct (fetch_word segs (Z_to_bv 64 pc)) as [w|] eqn:E; [|discriminate].
  apply Z.eqb_eq in Hf.
  assert (Hw : w = (0x8067%bv : bv 32)) by (apply bv_eq; rewrite Hf; reflexivity). subst w.
  eapply msteps_one; [reflexivity|].
  rewrite (step_jalr_x0 segs R _ M rom _ 1%bv 0%bv ret E eq_refl decode_ret Hra).
  unfold ret_ok in Hret. change (bv_signed (0%bv : bv 12)) with 0%Z. rewrite Hret. reflexivity.
Qed.

Ltac leaf_ret Hra Hret :=
  idtac;
  lazymatch type of Hra with getr _ _ = ?retv =>
  lazymatch goal with
  | HR' : regs_ok _ _ ?R', Hms : msteps _ _ _ |- _ =>
      let Hra1 := fresh "Hra1" in
      assert (Hra1 : getr R' 1%bv = retv) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]);
      exists R'; split; [|split];
      [ eapply msteps_trans; [exact Hms|];
        eapply ret_run; [ vm_compute; reflexivity | exact Hra1 | exact Hret ]
      | exact (kept_of_syms _ _ _ R' HR' eq_refl)
      | let H10 := fresh "H10" in rreg HR' 10%bv H10; rewrite H10 ]
  end end.

Ltac lit_in H :=
  repeat match type of H with
  | context [Z_to_bv 64 ?e] =>
      lazymatch e with
      | Zpos _ => fail | Z0 => fail | Zneg _ => fail
      | _ => let v := eval vm_compute in e in change e with v in H
      end
  end.

Lemma range_cases : forall (x lo : Z) (n : nat),
  (lo <= x < lo + Z.of_nat n)%Z -> exists k, (k < n)%nat /\ x = (lo + Z.of_nat k)%Z.
Proof. intros x lo n H. exists (Z.to_nat (x - lo)). split; lia. Qed.

Ltac enum_range x lo n H :=
  let k := fresh "k" in let Hk := fresh "Hk" in let Hx := fresh "Hx" in
  destruct (range_cases x lo n H) as (k & Hk & Hx);
  subst x;
  let rec go m := lazymatch m with
    | O => exfalso; lia
    | S ?m' => destruct k as [|k]; [ clear Hk | go m' ]
    end in
  go n.

Lemma kimg_ro : forall segs (L : Layout) E M lo hi,
  ro_clear L M -> (forall a, lo <= a < hi -> ro_addr L a) -> 0 <= lo -> hi <= 2 ^ 64 ->
  kentry_ok segs E M (KImg lo hi).
Proof.
  intros segs L E M lo hi HR Hro Hlo Hhi. apply kimg_abs; [lia|lia|].
  intros i Hi. apply (ro_clear_at L M i HR); [lia|]. apply Hro. lia.
Qed.

Definition b2w (b : bool) : word := Z_to_bv 64 (if b then 1 else 0).

Lemma sltu_b2w : forall a b : word, exists t, alu64 ALU_SLTU a b = b2w t.
Proof.
  intros a b. cbn [alu64 alu]. unfold b2w.
  destruct (bv_ltu a b); [exists true|exists false]; reflexivity.
Qed.

Lemma slt_b2w : forall a b : word, exists t, alu64 ALU_SLT a b = b2w t.
Proof.
  intros a b. cbn [alu64 alu]. unfold b2w.
  destruct (bv_lts a b); [exists true|exists false]; reflexivity.
Qed.

Lemma or_b2w : forall s t, alu64 ALU_OR (b2w s) (b2w t) = b2w (s || t).
Proof. intros [|] [|]; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma and_b2w_l : forall s (y : word), exists t, alu64 ALU_AND (b2w s) y = b2w t.
Proof.
  intros s y. unfold b2w. cbn [alu64 alu]. destruct s.
  - pose proof (bv_unsigned_in_range _ y) as Hy.
    assert (H01 : Z.land 1 (bv_unsigned y) = 0 \/ Z.land 1 (bv_unsigned y) = 1).
    { rewrite Z.land_comm. change (Z.land (bv_unsigned y) 1) with (Z.land (bv_unsigned y) (Z.ones 1)).
      rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
      pose proof (Z.mod_pos_bound (bv_unsigned y) 2 ltac:(lia)). lia. }
    destruct H01 as [H0|H1]; [exists false|exists true]; apply bv_eq;
      rewrite bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod; cbn; [exact H0 | exact H1].
  - exists false. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

Lemma lit_b2w_1 : Z_to_bv 64 1 = b2w true.   Proof. reflexivity. Qed.
Lemma lit_b2w_0 : Z_to_bv 64 0 = b2w false.  Proof. reflexivity. Qed.

Lemma sx32_range : forall w, 0 <= w < 2 ^ 32 -> 0 <= TablStmts.sx32 w < 2 ^ 64.
Proof. intros w Hw. unfold TablStmts.sx32. destruct (Z.ltb_spec w (2 ^ 31)); lia. Qed.

Lemma sx32_small : forall w, 0 <= w < 2 ^ 31 -> TablStmts.sx32 w = w.
Proof. intros w Hw. unfold TablStmts.sx32. destruct (Z.ltb_spec w (2 ^ 31)); lia. Qed.

Lemma sx32_sxw : forall k, 0 <= k < 2 ^ 32 -> Z_to_bv 64 (TablStmts.sx32 k) = sxw k.
Proof.
  intros k Hk. unfold TablStmts.sx32, sxw. rewrite bv_swrap32_cases by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  destruct (Z.ltb_spec k (2 ^ 31)); [reflexivity|].
  replace (k + 2 ^ 64 - 2 ^ 32) with ((k - 2 ^ 32) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma w2_eq : forall a b, a mod 2 ^ 16 = b mod 2 ^ 16 ->
  word_to_le_bytes 2 (Z_to_bv 64 a) = word_to_le_bytes 2 (Z_to_bv 64 b).
Proof.
  intros a b H. unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  f_equal; [|f_equal]; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; nia.
Qed.

Lemma srl16_val : forall v, 0 <= v < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 v) (Z_to_bv 64 16) = Z_to_bv 64 (v / 2 ^ 16).
Proof.
  intros v Hv. apply bv_eq. cbn [alu64 alu].
  rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small v), (Z.mod_small 16), (Z.mod_small 63) by lia. change (Z.land 16 63) with 16.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.mod_small; [reflexivity|]. nia.
Qed.

Lemma zbv_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma zbv_mul : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma w_sltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
  intros a b Ha Hb. cbn [alu64 alu]. unfold bv_ltu. rewrite !u64_of_Z by lia. destruct (a <? b); reflexivity.
Qed.

Lemma w_srl : forall a s, 0 <= a < 2 ^ 64 -> 0 <= s < 64 ->
  alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 s) = Z_to_bv 64 (a / 2 ^ s).
Proof.
  intros a s Ha Hs. apply bv_eq. cbn [alu64 alu].
  rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small a), (Z.mod_small s), (Z.mod_small 63) by lia.
  replace (Z.land s 63) with s.
  2:{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.mod_small; [reflexivity|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma sxw_small : forall v, 0 <= v < 2 ^ 31 -> sxw v = Z_to_bv 64 v.
Proof. intros v Hv. unfold sxw. rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec v (2 ^ 31)); [reflexivity | lia]. Qed.

Lemma br_geu_sxw : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  branch_taken BC_GEU (sxw a) (sxw b) = negb (a <? b).
Proof.
  intros a b Ha Hb. unfold sxw. rewrite !bv_swrap32_cases by lia. cbn [branch_taken]. unfold bv_ltu.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  destruct (Z.ltb_spec a (2 ^ 31)); destruct (Z.ltb_spec b (2 ^ 31)).
  - rewrite !Z.mod_small by lia. reflexivity.
  - rewrite (Z.mod_small a) by lia. replace ((b - 2 ^ 32) mod 2 ^ 64) with (b - 2 ^ 32 + 2 ^ 64) by nia.
    destruct (Z.ltb_spec a (b - 2 ^ 32 + 2 ^ 64)); destruct (Z.ltb_spec a b); try reflexivity; lia.
  - rewrite (Z.mod_small b) by lia. replace ((a - 2 ^ 32) mod 2 ^ 64) with (a - 2 ^ 32 + 2 ^ 64) by nia.
    destruct (Z.ltb_spec (a - 2 ^ 32 + 2 ^ 64) b); destruct (Z.ltb_spec a b); try reflexivity; lia.
  - replace ((a - 2 ^ 32) mod 2 ^ 64) with (a - 2 ^ 32 + 2 ^ 64) by nia. replace ((b - 2 ^ 32) mod 2 ^ 64) with (b - 2 ^ 32 + 2 ^ 64) by nia.
    destruct (Z.ltb_spec (a - 2 ^ 32 + 2 ^ 64) (b - 2 ^ 32 + 2 ^ 64)); destruct (Z.ltb_spec a b); try reflexivity; lia.
Qed.

Lemma low32_val : forall a, bv_unsigned (low32 (Z_to_bv 64 a)) = a mod 2 ^ 32.
Proof.
  intros a. unfold low32. rewrite bv_extract_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). nia.
Qed.

Lemma aluw_add_val : forall a b,
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b))) = Z_to_bv 64 (TablStmts.sx32 ((a + b) mod 2 ^ 32)).
Proof.
  intros a b. apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned. cbn [alu32 alu]. unfold bv_signed.
  rewrite bv_add_unsigned, !low32_val, Z_to_bv_unsigned, bv_wrap64_mod.
  unfold bv_swrap, bv_half_modulus, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  rewrite <- Zplus_mod. unfold TablStmts.sx32.
  set (v := (a + b) mod 2 ^ 32). assert (Hv : 0 <= v < 2 ^ 32) by (subst v; apply Z.mod_pos_bound; lia).
  destruct (Z.ltb_spec v (2 ^ 31)); nia.
Qed.

Lemma sx32_mod16 : forall w, 0 <= w < 2 ^ 32 -> TablStmts.sx32 w mod 2 ^ 16 = w mod 2 ^ 16.
Proof. intros w Hw. unfold TablStmts.sx32. destruct (Z.ltb_spec w (2 ^ 31)); nia. Qed.

Lemma sx32_hi16 : forall w, 0 <= w < 2 ^ 32 -> (TablStmts.sx32 w / 2 ^ 16) mod 2 ^ 16 = (w / 2 ^ 16) mod 2 ^ 16.
Proof. intros w Hw. unfold TablStmts.sx32. destruct (Z.ltb_spec w (2 ^ 31)); nia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MemKit.
Variable SEGS : list Segment.

Lemma cell1_of_M : forall M a (c : byte), M (Z_to_bv 64 a) = Some c -> cellw SEGS M a 1 (bv_unsigned c).
Proof using SEGS.
  intros M a c H. unfold cellw. change (N.to_nat 1) with 1%nat.
  pose proof (bv_unsigned_in_range _ c) as X. unfold bv_modulus in X. cbn in X. split.
  - cbn. lia.
  - cbn [rdn]. rewrite H. rewrite w1_bytes_small by lia. do 2 f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma cell1_inj : forall M a c c', cellw SEGS M a 1 c -> cellw SEGS M a 1 c' -> c = c'.
Proof using SEGS.
  intros M a c c' [Hc R] [Hc' R']. change (N.to_nat 1) with 1%nat in R, R'. cbn in Hc, Hc'.
  rewrite w1_bytes_small in R by lia. rewrite w1_bytes_small in R' by lia.
  rewrite R in R'. injection R' as E.
  assert (E2 : bv_unsigned (Z_to_bv 8 c) = bv_unsigned (Z_to_bv 8 c')) by first [exact E | exact (f_equal bv_unsigned E)].
  rewrite !u8_of_Z in E2 by lia. exact E2.
Qed.

Lemma mdef_byte : forall M a n i, mdef M a n -> 0 <= i < n -> exists c : byte, M (Z_to_bv 64 (a + i)) = Some c.
Proof using.
  intros M a n i Hd Hi. specialize (Hd i Hi). destruct (M (Z_to_bv 64 (a + i))) as [c|]; [exists c; reflexivity | exfalso; exact (Hd eq_refl)].
Qed.

Lemma mdef4_fld : forall M a, mdef M a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  exists e, 0 <= e < 2 ^ 32 /\ CRep.fld SEGS M a 4 e.
Proof using SEGS.
  intros M a Hd H0 H1.
  destruct (mdef_byte M a 4 0 Hd ltac:(lia)) as [c0 E0].
  destruct (mdef_byte M a 4 1 Hd ltac:(lia)) as [c1 E1].
  destruct (mdef_byte M a 4 2 Hd ltac:(lia)) as [c2 E2].
  destruct (mdef_byte M a 4 3 Hd ltac:(lia)) as [c3 E3].
  exists (bytes_le_to_Z [c0; c1; c2; c3]).
  pose proof (PropExec.bytes_le_to_Z_bound [c0; c1; c2; c3]) as Bd.
  pose proof (bytes_le_to_Z_nonneg [c0; c1; c2; c3]) as Bn.
  cbn [length] in Bd. replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Bd by reflexivity.
  split; [lia|].
  unfold CRep.fld. rewrite (SymDrive3.word_to_le_bytes_of_lez 4 [c0; c1; c2; c3] eq_refl ltac:(lia)).
  apply rdn_pointwise; [reflexivity | rewrite u64_of_Z by lia; lia |].
  intros j Hj. rewrite u64_of_Z by lia.
  destruct j as [|[|[|[|j]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; [ | exact E1 | exact E2 | exact E3 | lia].
  rewrite Z.add_0_r in E0. rewrite Z.add_0_r. exact E0.
Qed.

Lemma fld_wbytes4 : forall M a v, 0 <= a -> a + 4 <= 2 ^ 64 ->
  CRep.fld SEGS (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 4 (Z_to_bv 64 v))) a 4 v.
Proof using SEGS.
  intros M a v H0 H1. unfold CRep.fld. apply rdn_wbytes_hit4. rewrite u64_of_Z by lia. lia.
Qed.

Lemma frame_wbytes4 : forall (F : Z -> Prop) M a (v : word), 0 <= a -> a + 4 <= 2 ^ 64 ->
  (forall x, a <= x < a + 4 -> F x) ->
  frame_eq F M (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 4 v)).
Proof using.
  intros F M a v H0 H1 HF x Hx. apply MemSplit.wbytes_outside; rewrite length_N_to_le_bytes, u64_of_Z by lia; [lia|].
  pose proof (bv_unsigned_in_range _ x) as X.
  destruct (Z.lt_ge_cases (bv_unsigned x) a); [left; lia|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (a + 4)); [|right; lia].
  exfalso. apply Hx, HF. lia.
Qed.

Lemma defined_wbytes4 : forall M a (v : word) (x : word), 0 <= a -> a + 4 <= 2 ^ 64 ->
  M x <> None -> wbytes M (Z_to_bv 64 a) (word_to_le_bytes 4 v) x <> None.
Proof using.
  intros M a v x H0 H1 Hd.
  destruct (Z.lt_ge_cases (bv_unsigned x) a) as [Hl|Hge].
  - rewrite MemSplit.wbytes_outside; [exact Hd| |left]; rewrite ?length_N_to_le_bytes, u64_of_Z by lia; lia.
  - destruct (Z.lt_ge_cases (bv_unsigned x) (a + 4)) as [Hl2|Hge2].
    + rewrite MemSplit.wbytes_inside; [discriminate| |]; rewrite length_N_to_le_bytes, u64_of_Z by lia; lia.
    + rewrite MemSplit.wbytes_outside; [exact Hd| |right]; rewrite ?length_N_to_le_bytes, u64_of_Z by lia; lia.
Qed.

Lemma fld_wbytesN : forall (n : nat) M a v, (n <= 8)%nat -> 0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 ->
  CRep.fld SEGS (wbytes M (Z_to_bv 64 a) (word_to_le_bytes n (Z_to_bv 64 v))) a n v.
Proof using SEGS.
  intros n M a v Hn H0 H1. unfold CRep.fld.
  pose proof (SeqExec.rdn_wbytes_hit SEGS (word_to_le_bytes n (Z_to_bv 64 v)) M (Z_to_bv 64 a)) as R.
  rewrite length_N_to_le_bytes in R. apply R. rewrite u64_of_Z; lia.
Qed.
Lemma fld_wbytes8 : forall M a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  CRep.fld SEGS (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v))) a 8 v.
Proof using SEGS. intros. apply (fld_wbytesN 8); cbn; lia. Qed.

Lemma frame_wbytesN : forall (F : Z -> Prop) M a (bs : list byte), 0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> F x) ->
  frame_eq F M (wbytes M (Z_to_bv 64 a) bs).
Proof using.
  intros F M a bs H0 H1 HF x Hx. apply MemSplit.wbytes_outside; rewrite u64_of_Z by lia; [lia|].
  pose proof (bv_unsigned_in_range _ x) as X.
  destruct (Z.lt_ge_cases (bv_unsigned x) a); [left; lia|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (a + Z.of_nat (length bs))); [|right; lia].
  exfalso. apply Hx, HF. lia.
Qed.
Lemma frame_wbytes8 : forall (F : Z -> Prop) M a (v : word), 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> F x) -> frame_eq F M (wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
Proof using. intros F M a v H0 H1 HF. apply frame_wbytesN; rewrite ?length_N_to_le_bytes; [lia|cbn; lia|]. intros x Hx. apply HF. cbn in Hx. lia. Qed.

Lemma defined_wbytesN : forall M a (bs : list byte) (x : word), 0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  M x <> None -> wbytes M (Z_to_bv 64 a) bs x <> None.
Proof using.
  intros M a bs x H0 H1 Hd.
  destruct (Z.lt_ge_cases (bv_unsigned x) a) as [Hl|Hge].
  - rewrite MemSplit.wbytes_outside; [exact Hd| |left]; rewrite u64_of_Z by lia; lia.
  - destruct (Z.lt_ge_cases (bv_unsigned x) (a + Z.of_nat (length bs))) as [Hl2|Hge2].
    + rewrite MemSplit.wbytes_inside; [discriminate| |]; rewrite u64_of_Z by lia; lia.
    + rewrite MemSplit.wbytes_outside; [exact Hd| |right]; rewrite u64_of_Z by lia; lia.
Qed.
Lemma defined_wbytes8 : forall M a (v : word) (x : word), 0 <= a -> a + 8 <= 2 ^ 64 ->
  M x <> None -> wbytes M (Z_to_bv 64 a) (word_to_le_bytes 8 v) x <> None.
Proof using. intros. apply defined_wbytesN; rewrite ?length_N_to_le_bytes; cbn; try lia. assumption. Qed.

Lemma mdef8_fld : forall M a, mdef M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  exists e, 0 <= e < 2 ^ 64 /\ CRep.fld SEGS M a 8 e.
Proof using SEGS.
  intros M a Hd H0 H1.
  destruct (mdef_byte M a 8 0 Hd ltac:(lia)) as [c0 E0]. destruct (mdef_byte M a 8 1 Hd ltac:(lia)) as [c1 E1].
  destruct (mdef_byte M a 8 2 Hd ltac:(lia)) as [c2 E2]. destruct (mdef_byte M a 8 3 Hd ltac:(lia)) as [c3 E3].
  destruct (mdef_byte M a 8 4 Hd ltac:(lia)) as [c4 E4]. destruct (mdef_byte M a 8 5 Hd ltac:(lia)) as [c5 E5].
  destruct (mdef_byte M a 8 6 Hd ltac:(lia)) as [c6 E6]. destruct (mdef_byte M a 8 7 Hd ltac:(lia)) as [c7 E7].
  exists (bytes_le_to_Z [c0; c1; c2; c3; c4; c5; c6; c7]).
  pose proof (PropExec.bytes_le_to_Z_bound [c0; c1; c2; c3; c4; c5; c6; c7]) as Bd.
  pose proof (bytes_le_to_Z_nonneg [c0; c1; c2; c3; c4; c5; c6; c7]) as Bn.
  cbn [length] in Bd. replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Bd by reflexivity.
  split; [lia|].
  unfold CRep.fld. rewrite (SymDrive3.word_to_le_bytes_of_lez 8 [c0; c1; c2; c3; c4; c5; c6; c7] eq_refl ltac:(lia)).
  apply rdn_pointwise; [reflexivity | rewrite u64_of_Z by lia; lia |].
  intros j Hj. rewrite u64_of_Z by lia.
  destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ];
    [ | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
  rewrite Z.add_0_r in E0. rewrite Z.add_0_r. exact E0.
Qed.
End MemKit.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition sx := TablStmts.sx32.
Lemma sx_cases : forall w, 0 <= w < 2 ^ 32 -> (w < 2 ^ 31 /\ sx w = w) \/ (2 ^ 31 <= w /\ sx w = w + 2 ^ 64 - 2 ^ 32).
Proof. intros w Hw. unfold sx, TablStmts.sx32. destruct (Z.ltb_spec w (2 ^ 31)); lia. Qed.
Lemma low32_sx : forall w, 0 <= w < 2 ^ 32 -> bv_unsigned (low32 (Z_to_bv 64 (sx w))) = w.
Proof.
  intros w Hw. unfold low32. rewrite bv_extract_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). destruct (sx_cases w Hw) as [[A ->]|[A ->]]; nia.
Qed.
Lemma low32_lit : forall k, 0 <= k < 2 ^ 32 -> bv_unsigned (low32 (Z_to_bv 64 k)) = k.
Proof.
  intros k Hk. unfold low32. rewrite bv_extract_unsigned, Z_to_bv_unsigned, bv_wrap64_mod, Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). nia.
Qed.
Lemma T4_val : forall w, 0 <= w < 2 ^ 32 ->
  bv_unsigned (sext 64 (alu32 ALU_SRL (low32 (Z_to_bv 64 (sx w))) (low32 (Z_to_bv 64 24)))) = w / 2 ^ 24.
Proof.
  intros w Hw. unfold sext. rewrite bv_sign_extend_unsigned. cbn [alu32 alu].
  unfold bv_signed. rewrite bv_shiftr_unsigned, bv_and_unsigned, low32_sx, low32_lit, Z_to_bv_unsigned by lia.
  unfold bv_wrap, bv_swrap, bv_half_modulus, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  replace (Z.land 24 (31 mod 2 ^ 32)) with 24 by reflexivity.
  rewrite Z.shiftr_div_pow2 by lia. nia.
Qed.
Lemma T1_val : forall w, 0 <= w < 2 ^ 32 ->
  bv_unsigned (sext 64 (alu32 ALU_SLL (low32 (Z_to_bv 64 (sx w))) (low32 (Z_to_bv 64 24)))) =
  (if w mod 256 <? 128 then (w mod 256) * 2 ^ 24 else (w mod 256) * 2 ^ 24 + 2 ^ 64 - 2 ^ 32).
Proof.
  intros w Hw. unfold sext. rewrite bv_sign_extend_unsigned. cbn [alu32 alu].
  unfold bv_signed. rewrite bv_shiftl_unsigned, bv_and_unsigned, low32_sx, low32_lit, Z_to_bv_unsigned by lia.
  unfold bv_wrap, bv_swrap, bv_half_modulus, bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  replace (Z.land 24 (31 mod 2 ^ 32)) with 24 by reflexivity.
  rewrite Z.shiftl_mul_pow2 by lia.

  replace ((w * 2 ^ 24) mod 2 ^ 32) with ((w mod 256) * 2 ^ 24) by nia.
  destruct (Z.ltb_spec (w mod 256) 128); nia.
Qed.
Lemma T2_val : forall w, 0 <= w < 2 ^ 32 ->
  bv_unsigned (mul_div M_MUL (Z_to_bv 64 256) (alu64 ALU_AND (Z_to_bv 64 (sx w)) (Z_to_bv 64 65280))) = 2 ^ 16 * ((w / 256) mod 256).
Proof.
  intros w Hw. cbn [mul_div alu64 alu]. rewrite bv_mul_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  pose proof (sx_cases w Hw) as C.
  rewrite (Z.mod_small (sx w)) by lia. change (65280 mod 2 ^ 64) with 65280. change (256 mod 2 ^ 64) with 256.
  rewrite land_ff00 by lia.
  replace ((sx w / 256) mod 256) with ((w / 256) mod 256) by (destruct C as [[A ->]|[A ->]]; nia).
  nia.
Qed.
Lemma T3_val : forall w, 0 <= w < 2 ^ 32 ->
  bv_unsigned (alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 (sx w)) (Z_to_bv 64 8)) (Z_to_bv 64 65280)) = 256 * ((w / 2 ^ 16) mod 256).
Proof.
  intros w Hw. cbn [alu64 alu]. rewrite bv_and_unsigned, bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  pose proof (sx_cases w Hw) as C.
  rewrite (Z.mod_small (sx w)) by lia. change (Z.land (8 mod 2 ^ 64) (63 mod 2 ^ 64)) with 8. change (65280 mod 2 ^ 64) with 65280.
  rewrite Z.shiftr_div_pow2 by lia. rewrite land_ff00 by nia.
  destruct C as [[A ->]|[A ->]]; nia.
Qed.

Lemma land_high_low : forall m k x, 0 <= m -> 0 <= k -> 0 <= x < 2 ^ m -> Z.land (2 ^ m * k) x = 0.
Proof.
  intros m k x Hm Hk Hx. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n m) as [Hlt|Hge].
  - rewrite Z.mul_comm, Z.mul_pow2_bits_low by lia. reflexivity.
  - destruct (Z.eq_dec x 0) as [->|Hx0]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    rewrite (Z.bits_above_log2 x n); [apply Bool.andb_false_r | lia |].
    apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma lor_high_low : forall m k x, 0 <= m -> 0 <= k -> 0 <= x < 2 ^ m -> Z.lor (2 ^ m * k) x = 2 ^ m * k + x.
Proof.
  intros m k x Hm Hk Hx. rewrite <- Z.lxor_lor by (apply land_high_low; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_high_low; lia.
Qed.

Lemma u_or : forall a b : word, bv_unsigned (alu64 ALU_OR a b) = Z.lor (bv_unsigned a) (bv_unsigned b).
Proof. intros a b. cbn [alu64 alu]. apply bv_or_unsigned. Qed.

Lemma fixword_swap : forall w, 0 <= w < 2 ^ 32 ->
  let X := Z_to_bv 64 (sx w) in
  exists r, 0 <= r < 2 ^ 32 /\
  alu64 ALU_OR
    (alu64 ALU_OR (sext 64 (alu32 ALU_SLL (low32 X) (low32 (Z_to_bv 64 24))))
                  (mul_div M_MUL (Z_to_bv 64 256) (alu64 ALU_AND X (Z_to_bv 64 65280))))
    (alu64 ALU_OR (alu64 ALU_AND (alu64 ALU_SRL X (Z_to_bv 64 8)) (Z_to_bv 64 65280))
                  (sext 64 (alu32 ALU_SRL (low32 X) (low32 (Z_to_bv 64 24)))))
  = Z_to_bv 64 (sx r).
Proof.
  intros w Hw X. subst X.
  set (b0 := w mod 256). set (b1 := (w / 256) mod 256). set (b2 := (w / 2 ^ 16) mod 256). set (b3 := w / 2 ^ 24).
  assert (Hb0 : 0 <= b0 < 256) by (subst b0; nia). assert (Hb1 : 0 <= b1 < 256) by (subst b1; nia).
  assert (Hb2 : 0 <= b2 < 256) by (subst b2; nia). assert (Hb3 : 0 <= b3 < 256) by (subst b3; nia).
  exists (b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3). split; [nia|].
  apply bv_eq.
  rewrite !u_or, T1_val, T2_val, T3_val, T4_val by lia. fold b0 b1 b2 b3.
  rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  assert (HT1 : exists k, 0 <= k /\ (if b0 <? 128 then b0 * 2 ^ 24 else b0 * 2 ^ 24 + 2 ^ 64 - 2 ^ 32) = 2 ^ 24 * k
                /\ (b0 < 128 /\ k = b0 \/ 128 <= b0 /\ k = b0 + 2 ^ 40 - 2 ^ 8)).
  { destruct (Z.ltb_spec b0 128); [exists b0; lia | exists (b0 + 2 ^ 40 - 2 ^ 8); lia]. }
  destruct HT1 as (k & Hk & -> & Hkc).
  replace (Z.lor (256 * b2) b3) with (256 * b2 + b3).
  2:{ change 256 with (2 ^ 8). symmetry. apply lor_high_low; lia. }
  replace (Z.lor (2 ^ 24 * k) (2 ^ 16 * b1)) with (2 ^ 24 * k + 2 ^ 16 * b1).
  2:{ symmetry. apply lor_high_low; lia. }
  replace (Z.lor (2 ^ 24 * k + 2 ^ 16 * b1) (256 * b2 + b3)) with (2 ^ 24 * k + 2 ^ 16 * b1 + (256 * b2 + b3)).
  2:{ replace (2 ^ 24 * k + 2 ^ 16 * b1) with (2 ^ 16 * (2 ^ 8 * k + b1)) by lia. symmetry. rewrite lor_high_low by lia. lia. }
  unfold sx, TablStmts.sx32. destruct (Z.ltb_spec (b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3) (2 ^ 31)); nia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
