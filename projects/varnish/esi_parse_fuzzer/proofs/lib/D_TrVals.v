(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive RefPl89 D_TrRuns.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_TrRuns.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition rd8 (sx : bool) (v : Z) : word := Z_to_bv 64 (extz sx 1 (bytes_le_to_Z [Z_to_bv 8 v])).

(* [comment removed for export] *)
Definition cfgF (v6 v7 : word) : word :=
  edenot (Env (fun n => match n with 6%nat => v6 | 7%nat => v7 | _ => Z_to_bv 64 0 end) (blobs_ev [])) cfgX.

Lemma cfgX_F : forall vals bl, edenot (Env (vals_ev vals) (blobs_ev bl)) cfgX = cfgF (vals_ev vals 6) (vals_ev vals 7).
Proof. intros. reflexivity. Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma in_zseq : forall n z, In z (zseq n) <-> (0 <= z < Z.of_nat n).
Proof.
  intros n z. unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.

Definition cfgv (b0 b1 : Z) : Z := (b0 + 256 * b1) mod 32768.

(* [comment removed for export] *)
Definition hiG (v6 v7 : word) : word :=
  edenot (Env (fun n => match n with 6%nat => v6 | 7%nat => v7 | _ => Z_to_bv 64 0 end) (blobs_ev []))
         (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EVar 6)) (ELit 49)).

Lemma cfgF_split : forall v6 v7, cfgF v6 v7 = alu64 ALU_OR (hiG v6 v7) v7.
Proof. intros. reflexivity. Qed.

Lemma hiG_irrel : forall v6 v7 w, hiG v6 v7 = hiG v6 w.
Proof. intros. reflexivity. Qed.

Lemma hi_tab : forallb (fun b1 => Z.eqb (bv_unsigned (hiG (rd8 true b1) (Z_to_bv 64 0))) (256 * (b1 mod 128))) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lo_tab : forallb (fun b0 => Z.eqb (bv_unsigned (rd8 false b0)) b0) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cfgF_val : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  cfgF (rd8 true b1) (rd8 false b0) = Z_to_bv 64 (cfgv b0 b1).
Proof.
  intros b0 b1 H0 H1.
  pose proof hi_tab as T. rewrite forallb_forall in T.
  specialize (T b1 (proj2 (in_zseq 256 b1) ltac:(cbn; lia))). apply Z.eqb_eq in T.
  pose proof lo_tab as L. rewrite forallb_forall in L.
  specialize (L b0 (proj2 (in_zseq 256 b0) ltac:(cbn; lia))). apply Z.eqb_eq in L.
  rewrite cfgF_split, (hiG_irrel _ _ (Z_to_bv 64 0)), alu_or. unfold v_or. rewrite T, L. f_equal.
  pose proof (Z.mod_pos_bound b1 128 ltac:(lia)) as HM.
  rewrite Z.lor_comm.
  replace (256 * (b1 mod 128)) with (Z.shiftl (b1 mod 128) 8) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
  rewrite (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.lor_shiftl8_add b0 (b1 mod 128) H0 ltac:(lia)).
  unfold cfgv.
  pose proof (Z.div_mod b1 128 ltac:(lia)) as DM.
  apply (Z.mod_unique_pos _ _ (b1 / 128)); lia.
Qed.

Lemma cfgv_range : forall b0 b1, 0 <= cfgv b0 b1 < 32768.
Proof. intros. unfold cfgv. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rd8_tab : forallb (fun v => Z.eqb (bv_unsigned (rd8 false v)) v) (zseq 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rd8_u : forall v, 0 <= v < 256 -> rd8 false v = Z_to_bv 64 v.
Proof.
  intros v Hv. pose proof rd8_tab as T. rewrite forallb_forall in T.
  specialize (T v (proj2 (in_zseq 256 v) ltac:(cbn; lia))). apply Z.eqb_eq in T. apply bv_eq. rewrite T, u_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma plen_val : forall (x c : Z), 0 <= x < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_ADD (Z_to_bv 64 x) (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 c))) (Z_to_bv 64 (-6))
  = Z_to_bv 64 (x - c - 6).
Proof.
  intros x c Hx Hc. apply bv_eq.
  change (alu64 ALU_ADD (alu64 ALU_ADD (Z_to_bv 64 x) (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 c))) (Z_to_bv 64 (-6)))
    with ((Z_to_bv 64 x + (Z_to_bv 64 (-1) * Z_to_bv 64 c)) + Z_to_bv 64 (-6))%bv.
  rewrite !bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x), (Z.mod_small c) by lia.
  change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). change ((-6) mod 2 ^ 64) with (2 ^ 64 - 6).
  rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_l.
  replace (x + (2 ^ 64 - 1) * c + (2 ^ 64 - 6)) with ((x - c - 6) + (c + 1) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma calls_val : forall v, 0 <= v < 256 ->
  alu64 ALU_ADD (alu64 ALU_AND (Z_to_bv 64 v) (Z_to_bv 64 3)) (Z_to_bv 64 1) = Z_to_bv 64 (v mod 4 + 1).
Proof. intros v Hv. rewrite alu_and3_Z by lia. apply alu_add_Z. Qed.
