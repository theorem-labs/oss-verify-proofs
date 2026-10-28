(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_fse_decnf_kit.
Import ListNotations.
Open Scope Z_scope.

Ltac close_fdcu := unfold FDCU; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                   split; [eassumption|]; split; [do 3 eexists; eassumption|]; split; [eassumption|]; split; [eassumption|];
                   split; [unfold bitd_cells; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Definition fc_hi (tb : list Z) (st : Z) : Z := fc_sy tb st + 256 * fc_nb tb st.

Lemma fc_hw_rd : forall m A (tb : list Z) k a, bytes_at usegs m A (map (Z_to_bv 8) tb) ->
  0 <= k -> k + 2 <= Z.of_nat (length tb) ->
  0 <= Znth k tb < 256 -> 0 <= Znth (k + 1) tb < 256 -> a = wa (A + k) ->
  ov_read_bytes usegs m a 2 = Some (le2 (Z_to_bv 64 (Znth k tb + 256 * Znth (k + 1) tb))).
Proof.
  intros m A tb k a B HS HL B0 B1 ->.
  rewrite (bytes_at_read usegs m A _ k 2 B) by (rewrite ?length_map; lia). f_equal.
  rewrite (le2_Z (Znth k tb + 256 * Znth (k + 1) tb) (Znth k tb + 256 * Znth (k + 1) tb) eq_refl). unfold ZdSeqTable.zle2.
  replace ((Znth k tb + 256 * Znth (k + 1) tb) mod 256) with (Znth k tb) by (Z.div_mod_to_equations; lia).
  replace (((Znth k tb + 256 * Znth (k + 1) tb) / 256) mod 256) with (Znth (k + 1) tb) by (Z.div_mod_to_equations; lia).
  rewrite skipn_map, firstn_map.
  unfold Znth. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  assert (LT : (S (Z.to_nat k) < length tb)%nat) by lia.
  revert LT. generalize (Z.to_nat k). clear. intros k. revert tb. induction k as [|k IH]; intros tb LT.
  - destruct tb as [|x [|y t]]; cbn [length] in LT; try lia. reflexivity.
  - destruct tb as [|x t]; cbn [length] in LT; [lia|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma fc_hi_rd : forall m A (tb : list Z) st a, bytes_at usegs m A (map (Z_to_bv 8) tb) ->
  0 <= st -> 4 * st + 4 <= Z.of_nat (length tb) ->
  0 <= fc_sy tb st < 256 -> 0 <= fc_nb tb st < 256 -> a = wa (A + 4 * st + 2) ->
  ov_read_bytes usegs m a 2 = Some (le2 (Z_to_bv 64 (fc_hi tb st))).
Proof.
  intros m A tb st a B HS HL B0 B1 ->. unfold fc_hi, fc_sy, fc_nb in *.
  replace (4 * st + 3) with (4 * st + 2 + 1) in * by lia.
  apply (fc_hw_rd m A tb (4 * st + 2)); try lia; try assumption. f_equal. lia.
Qed.

Lemma fc_hi_lt : forall tb st, 0 <= fc_sy tb st < 256 -> 0 <= fc_nb tb st <= 12 -> 0 <= fc_hi tb st < 2^15.
Proof. intros. unfold fc_hi. lia. Qed.

Lemma hi_shl : forall h, 0 <= h < 2^16 -> (h ≪ 16) mod 18446744073709551616 = h * 65536.
Proof. intros h H. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia. Qed.

Lemma hi_or : forall h x, 0 <= h -> 0 <= x < 65536 -> Z.lor (h * 65536) x = h * 65536 + x.
Proof.
  intros h x H1 H2. apply (lor_add (h * 65536) x 16); [lia | change (2^16) with 65536; lia |].
  change (2^16) with 65536. apply Z.mod_mul. lia.
Qed.

Lemma hi_nb : forall tb st, 0 <= fc_sy tb st < 256 -> 0 <= fc_nb tb st -> (fc_hi tb st * 65536) ≫ 24 = fc_nb tb st.
Proof.
  intros tb st H1 H2. rewrite Z.shiftr_div_pow2 by lia. change (2^24) with 16777216. unfold fc_hi.
  Z.div_mod_to_equations. lia.
Qed.

Lemma hi_nbx : forall tb st x, 0 <= fc_sy tb st < 256 -> 0 <= fc_nb tb st -> 0 <= x < 65536 -> (fc_hi tb st * 65536 + x) ≫ 24 = fc_nb tb st.
Proof.
  intros tb st x H1 H2 H3. rewrite Z.shiftr_div_pow2 by lia. change (2^24) with 16777216. unfold fc_hi.
  Z.div_mod_to_equations. lia.
Qed.

Lemma hi_and : forall h x, 0 <= h -> 0 <= x < 65536 -> Z.land (h * 65536 + x) 65535 = x.
Proof.
  intros h x H1 H2. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2^16) with 65536.
  rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi_nbw : forall tb st x, 0 <= fc_sy tb st < 256 -> 0 <= fc_nb tb st <= 12 -> 0 <= x < 65536 ->
  bv_swrap 32 (bv_wrap 32 (fc_hi tb st * 65536 + x) ≫ 24) = fc_nb tb st.
Proof.
  intros tb st x H1 H2 H3. rewrite srliw_val by lia. unfold fc_hi.
  rewrite Z.mod_small by lia. change (2^24) with 16777216. Z.div_mod_to_equations. lia.
Qed.

Ltac ldhi CELB DT tb st :=
  let a := cur_mem_addr in
  let RDc := fresh "RDc" in
  pose proof (fc_hi_rd _ (DT + 4) tb st a CELB ltac:(lia) ltac:(lia) ltac:(unfold fc_sy, fc_nb in *; lia) ltac:(unfold fc_sy, fc_nb in *; lia) ltac:(unfold wa; f_equal; lia)) as RDc;
  zstep; first [rewrite (zx16_u (fc_hi tb st)) by (pose proof (fc_hi_lt tb st ltac:(lia) ltac:(lia)); lia)
               | rewrite (sx16_short (fc_hi tb st)) by (pose proof (fc_hi_lt tb st ltac:(lia) ltac:(lia)); lia)]; clear RDc.
Ltac zshl :=
  repeat match goal with
  | |- context [Z.shiftl ?x ?k] => is_Zlit k; rewrite (Z.shiftl_mul_pow2 x k) by lia;
      let v := eval vm_compute in (2^k) in change (2^k) with v
  end.
Ltac zmod_small :=
  repeat match goal with
  | |- context [?x mod 18446744073709551616] => rewrite (Z.mod_small x 18446744073709551616) by lia
  | |- context [?x mod 4294967296] => rewrite (Z.mod_small x 4294967296) by lia
  end.
Ltac rnorm := zmod_small; zshl.

Ltac zb_lits :=
  repeat match goal with
  | H : context [Z.lxor ?a ?b] |- _ => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
  | H : context [Z.land ?a ?b] |- _ => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v in H
  | H : context [Z.lor ?a ?b] |- _ => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v in H
  | H : context [Z.lnot ?a] |- _ => is_Zlit a; let v := eval vm_compute in (Z.lnot a) in change (Z.lnot a) with v in H
  end.

Ltac zb_norm H :=
  repeat match type of H with
  | context [Z.shiftl ?x ?k] => is_Zlit k; rewrite (Z.shiftl_mul_pow2 x k) in H by lia;
      let v := eval vm_compute in (2^k) in change (2^k) with v in H
  | context [Z.shiftr ?x ?k] => is_Zlit k; rewrite (Z.shiftr_div_pow2 x k) in H by lia;
      let v := eval vm_compute in (2^k) in change (2^k) with v in H
  end.

Lemma lxor_lt1 : forall a b, 0 <= a -> 0 <= b -> Z.lxor a b < 1 -> a = b.
Proof.
  intros a b Ha Hb H. apply Z.lxor_eq_0_iff.
  pose proof (proj2 (Z.lxor_nonneg a b) (conj (fun _ => Hb) (fun _ => Ha))). lia.
Qed.

Lemma lxor_ge1 : forall a b, 1 <= Z.lxor a b -> a <> b.
Proof. intros a b H E. subst b. rewrite Z.lxor_nilpotent in H. lia. Qed.

Ltac zb_lx E :=
  lazymatch type of E with
  | Z.lxor ?a ?b < 1 => let E2 := fresh "E" in assert (E2 : a = b) by (apply lxor_lt1; [lia | lia | exact E]); clear E; rename E2 into E
  | 1 <= Z.lxor ?a ?b => apply lxor_ge1 in E
  | _ => try rewrite Z.lxor_eq_0_iff in E
  end.

Ltac zb_split H :=
  repeat match type of H with
  | context [Z.b2z ?c] => let E := fresh "E" in destruct c eqn:E; zify_bool E; zb_lx E; zb_norm E; cbn [Z.b2z] in H
  end.

Ltac zb_refute H := exfalso; zb_norm H; zb_split H; zb_lits; lia.

Ltac zchk := let K := fresh "K" in if_cases K; zify_cond K; [zb_refute K | clear K].
Ltac zchk2 := let K := fresh "K" in if_cases K; zify_cond K; [clear K | zb_refute K].

Ltac zflag v :=
  lazymatch goal with |- context [Z.lxor (Z.b2z ?c) 1] =>
    replace (Z.lxor (Z.b2z c) 1) with v by (let E := fresh "E" in destruct c eqn:E; zify_bool E; first [reflexivity | exfalso; lia])
  end.

Ltac zb_goal :=
  repeat match goal with |- context [Z.b2z ?c] =>
    first [ replace (Z.b2z c) with 1 by (let E := fresh "E" in destruct c eqn:E; zify_bool E; try rewrite Z.lxor_eq_0_iff in E; [reflexivity | exfalso; lia])
          | replace (Z.b2z c) with 0 by (let E := fresh "E" in destruct c eqn:E; zify_bool E; try rewrite Z.lxor_eq_0_iff in E; [exfalso; lia | reflexivity]) ]
  end.

Ltac zchk_show := let K := fresh "K" in if_cases K; zify_cond K; [let T := type of K in fail 100 T | clear K].
