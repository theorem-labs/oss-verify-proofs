(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "ineq"; "fdig"; "lin"; "dg_with_pool"; "add_new"; "ineqs_of_rels"; "ctx0"; "dg_facts"; "dg_srels"; "dg_urels"; "ineq_subsumed"; "lin_eqb"; "lin_round"; "mk_dig"; "mk_pool"; "ne_tighten"; "neq_prim"; "neqs_of"; "pool_round"; "sat_depth"; "saturate"; "@Corelib.Init.Datatypes"; "list"; "bool"; "Some"; "false"; "fst"; "nat"; "option"; "snd"; "app"; "length"; "nil"; "prod"; "true"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast"; "pcache"; "pc_ok"; "force_d"; "get_x"; "mkPC"; "pc_0"; "pc_d"; "pc_sf"; "pc_u0"; "pc_ud"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "mk_pool_f"; "pool_round_f"; "add_new_l"; "force_d_f"; "mk_dig_f"; "mk_pf_f"; "saturate_f"; "add_new_n"; "ineq_subsumed_l"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "pfacts"; "mkPF"; "mk_pf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "existsb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymDigFast"; "mk_ctx_x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObjFast"; "mk_pf_x"; "@Stdlib.ZArith.BinInt.Z"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymDigFast SymObjFast SymStepFast.
Import ListNotations.
Open Scope Z_scope.

Definition ineq_subsumed_l (pool : list ineq) (g : ineq) : bool := ltac2:(tb__ "0|1|
S3dS20S2S25A2M0G0S16S16L_;SbS19S2S25Vg;A3S19S2S25R1A3A2S40S1cS2S25R1A3S1cS2S25Vg;A3A2S18X16x2Lh;Vpool;A3").
Lemma ineq_subsumed_l_eq : ltac2:(tb__ "0|0|
S15S0A1S0S22S16S39R2R1A2SaR2R1A2A3Fg;Fpool;").
Proof.
  intros pool g. unfold ineq_subsumed_l, ineq_subsumed. rewrite existsb_lazy_eq.
  induction pool as [|h t IH]; cbn [existsb]; [reflexivity|]. rewrite IH.
  destruct (lin_eqb (fst g) (fst h)); reflexivity.
Qed.

Fixpoint add_new_l (pool fresh : list ineq) : list ineq :=
  match fresh with
  | [] => []
  | g :: rest => if ineq_subsumed_l pool g then add_new_l pool rest else g :: add_new_l (g :: pool) rest
  end.
Lemma add_new_l_eq : ltac2:(tb__ "0|1|
S15S0A1M0G0S22G0S33R1R2A2S4R1R2A2A3Fpool;Ffresh;").
Proof.
  induction fresh as [|g rest IH]; intros pool; cbn [add_new_l add_new]; [reflexivity|].
  rewrite ineq_subsumed_l_eq. destruct (ineq_subsumed pool g); rewrite IH; reflexivity.
Qed.

Fixpoint add_new_n (n : nat) (pool fresh : list ineq) {struct fresh} : list ineq :=
  match fresh with
  | [] => []
  | g :: rest =>
      match n with
      | O => []
      | S n' => if ineq_subsumed_l pool g then add_new_n n pool rest else g :: add_new_n n' (g :: pool) rest
      end
  end.
Lemma add_new_n_eq : ltac2:(tb__ "0|1|
S15S0A1M0S1aG0S22G0S38R2R1R3A3S24S0R2S4R1R3A2A3A3Fpool;Fn;Ffresh;").
Proof.
  induction fresh as [|g rest IH]; intros n pool; cbn [add_new_n add_new].
  - destruct n; reflexivity.
  - destruct n as [|n']; [reflexivity|]. rewrite ineq_subsumed_l_eq.
    destruct (ineq_subsumed pool g); [apply IH|]. cbn [firstn]. rewrite IH. reflexivity.
Qed.

Fixpoint saturate_f (n : nat) (neqs : list ineq) (news pool : list ineq) (base : list ineq) : list ineq :=
  match n with
  | O => pool
  | S n' => let fresh := add_new_n pool_cap pool (map (ne_tighten (length neqs) neqs) (combine_all news base)) in
            saturate_f n' neqs fresh (pool ++ fresh) base
  end.
Lemma saturate_f_eq : ltac2:(tb__ "0|1|
S1aS15S0A1M0G0G0G0S22G0S37R5R4R3R2R1A5S14R5R4R3R2R1A5A3Fbase;Fpool;Fnews;Fneqs;Fn;").
Proof.
  induction n as [|n IH]; intros neqs news pool base; cbn [saturate_f saturate]; [reflexivity|].
  cbv zeta. rewrite add_new_n_eq. apply IH.
Qed.

Definition pool_round_f (dg : fdig) : list ineq := ltac2:(tb__ "0|3|
S23S0S0S10S11Vdg;S7Vdg;A1M0A2A4S15S0A1M1S33S1fS0A1S23S0S0ScG0A1M2S23S0S0SfS1eS0R1A2R1A2S23S0S0G2S1dS0S5Vdg;S18S9Vdg;A1A3S5Vdg;S21S8Vdg;A1A3A3A4A4A4A2G1S23S0S0G2S37S13R2R1R1R1A5A4Tbase;Tneqs;").
Lemma pool_round_f_eq : ltac2:(tb__ "0|0|
S1S22S15S0A1S32R1A1S12R1A1A3Fdg;").
Proof. intros dg. unfold pool_round_f, pool_round. cbv zeta. rewrite add_new_l_eq, saturate_f_eq. reflexivity. Qed.

Definition mk_pool_f (dg : fdig) : list ineq := ltac2:(tb__ "0|0|
S32Vdg;A1S15S0A1S32S3Vdg;R1A2A1Tp1;").
Lemma mk_pool_f_eq : ltac2:(tb__ "0|0|
S1S22S15S0A1S31R1A1SeR1A1A3Fdg;").
Proof. intros dg. unfold mk_pool_f, mk_pool. cbv zeta. rewrite !pool_round_f_eq. reflexivity. Qed.

Definition mk_dig_f (facts : list sprop) : fdig := ltac2:(tb__ "0|0|
S3eVfacts;A1S1S3R1S31R1A1A2Tdg;").
Theorem mk_dig_f_eq : ltac2:(tb__ "0|0|
S15S26A1S22S1S35R1A1SdR1A1A3Ffacts;").
Proof. intros facts. unfold mk_dig_f, mk_dig. cbv zeta. rewrite mk_pool_f_eq, mk_ctx_x_eq. reflexivity. Qed.

Definition mk_pf_f (f : list sprop) : pfacts := ltac2:(tb__ "0|0|
S3bVf;S6Vf;A1S35Vf;A1A3").
Lemma mk_pf_f_eq : ltac2:(tb__ "0|0|
S15S26A1S22S3aS36R1A1S3cR1A1A3Ff;").
Proof. intros f. unfold mk_pf_f, mk_pf. rewrite mk_dig_f_eq. reflexivity. Qed.
Lemma mk_pf_f_eq_x : ltac2:(tb__ "0|0|
S15S26A1S22S3aS36R1A1S3fR1A1A3Ff;").
Proof. intros f. rewrite mk_pf_f_eq, mk_pf_x_eq. reflexivity. Qed.

Definition force_d_f (pc : pcache) (facts : list sprop) : pcache := ltac2:(tb__ "0|0|
S1bS1A1S27Lx;S2dVpc;A1S1Vpc;Lf;S2aVpc;Vfacts;A2S1S2bS2cVpc;A1S2eVpc;A1S17S1R1A2S17S1S3R1S31R1A1A2A2S2fVpc;A1S30Vpc;A1A6Tx;X1bx2").
Lemma force_d_f_eq : ltac2:(tb__ "0|0|
S27S15S26A1S22S27S34R2R1A2S29R2R1A2A3Ffacts;Fpc;").
Proof. intros pc facts. unfold force_d_f, force_d. destruct (pc_d pc); [reflexivity|]. cbv zeta. rewrite mk_pool_f_eq, SymDigFast.mk_pool_x_eq. reflexivity. Qed.
Lemma force_d_f_ok : ltac2:(tb__ "0|0|
S27S15S26A1S28R2R1A2S28S34R3R2A2R2A2F_;Ffacts;Fpc;").
Proof. intros pc facts H. rewrite force_d_f_eq. apply force_d_ok. exact H. Qed.
