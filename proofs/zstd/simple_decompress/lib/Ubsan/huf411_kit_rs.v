From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR.
Import ListNotations.
Open Scope Z_scope.

Lemma rsk_land3 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma rsk_srliw : forall x k, 0 <= x < 524288 -> 0 <= k -> bv_swrap 32 (bv_wrap 32 x ≫ k) = x ≫ k.
Proof.
  intros x k Hx Hk. rewrite wrap32_small by lia. apply swrap32_small.
  assert (0 <= x ≫ k) by (apply Z.shiftr_nonneg; lia).
  assert (x ≫ k <= x) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); Z.div_mod_to_equations; nia).
  lia.
Qed.

Lemma rsk_half : forall k, 0 <= k -> (2 * k) ≫ 1 = k.
Proof.
  intros k Hk. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  rewrite Z.mul_comm. apply Z.div_mul. lia.
Qed.

Lemma rsk_srliw_dbl : forall k, 0 <= k < 262144 -> bv_swrap 32 (bv_wrap 32 (2 * k) ≫ 1) = k.
Proof. intros k Hk. rewrite rsk_srliw by lia. apply rsk_half. lia. Qed.

Inductive rsk_al (x m : Z) : Prop := rsk_al_i : x mod m = 0 -> rsk_al x m.

Lemma rsk_al_e : forall x m, rsk_al x m -> x mod m = 0.
Proof. intros x m [H]. exact H. Qed.

Lemma rsk_al_add : forall x m d, 0 < m -> rsk_al x m -> d mod m = 0 -> (x + d) mod m = 0.
Proof. intros x m d Hm [H] Hd. rewrite Z.add_mod by lia. rewrite H, Hd, Z.add_0_l. apply Z.mod_0_l. lia. Qed.

Ltac rsk_unkeep :=
  repeat match goal with H : rsk_al ?x ?m |- _ =>
    lazymatch goal with _ : x mod m = 0 |- _ => fail | _ => pose proof (rsk_al_e x m H) end end.

Ltac rsk_ck K :=
  zify_cond K; exfalso;
  repeat match type of K with context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) in K by lia end;
  repeat match type of K with context [Z.land ?x 3] => rewrite (rsk_land3 x) in K by lia end;
  first [ lia | rsk_unkeep; Z.div_mod_to_equations; lia ].

Ltac rsk_chk := let K := fresh "KC" in if_cases K; [rsk_ck K | clear K].
