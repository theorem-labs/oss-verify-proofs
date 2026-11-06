(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module SV.

Ltac vc_intro :=
  unfold SG.vc_holds; cbn [SG.vc_kn SG.vc_path SG.vc_log SG.vc_src SG.vc_tgt SG.vc_facts];
  let E := fresh "E" in let m := fresh "m" in let HK := fresh "HK" in let HP := fresh "HP" in let HL := fresh "HL" in
  let HS := fresh "HS" in
  intros E m HK HP HL HS;
  unfold know_ok, scs_denot, SG.gholds in HK, HP, HS;
  repeat match goal with
    | H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; let X := fresh "X" in destruct H as [X H]
    | H : Forall _ [] |- _ => clear H
    end;
  cbn [kentry_ok sc_denot log_flat ST.g_id ST.g_args map estart elenZ a_base a_off adenot edenot] in *.

Section Mem.
Variable E : env.

Lemma md_skip : forall m a w v rest x,
  flat E a (Z.of_nat w) ->
  (bv_unsigned x < bv_unsigned (adenot E a) \/ bv_unsigned (adenot E a) + Z.of_nat w <= bv_unsigned x) ->
  mem_denot E m (SE a w v :: rest) x = mem_denot E m rest x.
Proof.
  intros m a w v rest x Hfl Hx. cbn [mem_denot]. apply wbytes_outside.
  - rewrite length_N_to_le_bytes, (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
  - rewrite length_N_to_le_bytes. exact Hx.
Qed.

Lemma md_newest : forall m a w v rest j, flat E a (Z.of_nat w) -> (j < w)%nat ->
  mem_denot E m (SE a w v :: rest) (Z_to_bv 64 (bv_unsigned (adenot E a) + Z.of_nat j))
  = Some (nth j (word_to_le_bytes w (edenot E v)) (Z_to_bv 8 0)).
Proof.
  intros m a w v rest j Hfl Hj. cbn [mem_denot]. apply wbytes_nth.
  - rewrite length_N_to_le_bytes, (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
  - rewrite length_N_to_le_bytes. exact Hj.
Qed.

Fixpoint outside_log (lg : list sentry) (x : Z) : Prop :=
  match lg with
  | [] => True
  | SE a w _ :: r => (x < estart E a \/ estart E a + Z.of_nat w <= x) /\ outside_log r x
  end.

Lemma md_outside : forall m lg x, log_flat E lg -> outside_log lg (bv_unsigned x) -> mem_denot E m lg x = m x.
Proof.
  intros m lg x. induction lg as [|[a w v] r IH]; intros Hlf Ho; [reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (_ & Hfa & Hlf). cbn [outside_log] in Ho. destruct Ho as [Ho1 Ho2].
  rewrite md_skip; [exact (IH Hlf Ho2) | exact Hfa | rewrite (flat_u E _ _ Hfa); exact Ho1].
Qed.

End Mem.

Lemma rd1_rdn : forall segs m (a : word) b, rdn segs m a 1 = Some [b] -> (match m a with Some x => Some x | None => seg_rom segs a end) = Some b.
Proof.
  intros segs m a b H. cbn [rdn] in H. destruct (match m a with Some x => Some x | None => seg_rom segs a end) as [x|]; [|discriminate].
  injection H as ->. reflexivity.
Qed.

Lemma u_alu_add : forall x y : word, bv_unsigned (alu64 ALU_ADD x y) = (bv_unsigned x + bv_unsigned y) mod 2^64.
Proof. intros x y. unfold alu64, alu. rewrite bv_add_unsigned. reflexivity. Qed.
Lemma u_alu_sub : forall x y : word, bv_unsigned (alu64 ALU_SUB x y) = (bv_unsigned x - bv_unsigned y) mod 2^64.
Proof. intros x y. unfold alu64, alu. rewrite bv_sub_unsigned. reflexivity. Qed.
Lemma u_mul : forall x y : word, bv_unsigned (mul_div M_MUL x y) = (bv_unsigned x * bv_unsigned y) mod 2^64.
Proof. intros x y. cbn [mul_div]. rewrite bv_mul_unsigned. reflexivity. Qed.
Lemma u_lit : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2^64.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lbyte (w : nat) (z : Z) (j : Z) : byte := nth (Z.to_nat j) (word_to_le_bytes w (Z_to_bv 64 z)) (Z_to_bv 8 0).

Fixpoint log_byte (kn : list kentry) (lg : list sentry) (b : expr) (d : Z) : option byte :=
  match lg with
  | [] => None
  | SE a w v :: rest =>
      if expr_eqb (a_base a) b then
        if (Z.leb (a_off a) d && Z.ltb d (a_off a + Z.of_nat w))%bool then
          match v with ELit z => Some (lbyte w z (d - a_off a)) | _ => None end
        else log_byte kn rest b d
      else if ranges_apart_x kn b d (ELit 1) (a_base a) (a_off a) (elen w) then log_byte kn rest b d else None
  end.

Fixpoint log_lit_read (kn : list kentry) (lg : list sentry) (b : expr) (k : Z) (n : nat) : option (list byte) :=
  match n with
  | O => Some []
  | S n' => match log_byte kn lg b k, log_lit_read kn lg b (k + 1) n' with
            | Some x, Some r => Some (x :: r)
            | _, _ => None
            end
  end.

Section LitRead.
Variable segs : list Segment.
Variable E : env.

Lemma log_byte_sound : forall M m kn lg b d x,
  know_ok segs E M kn -> log_flat E lg -> 0 <= bv_unsigned (edenot E b) + d < 2^64 ->
  log_byte kn lg b d = Some x -> mem_denot E m lg (Z_to_bv 64 (bv_unsigned (edenot E b) + d)) = Some x.
Proof.
  intros M m kn lg b d x HK. induction lg as [|[a w v] rest IH]; intros Hlf Hd H; [discriminate|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlf). cbn [log_byte] in H.
  pose proof (flat_u E _ _ Hfa) as Hu. destruct a as [ab ak]. unfold estart in Hu. cbn [a_base a_off] in *.
  assert (Hx : bv_unsigned (Z_to_bv 64 (bv_unsigned (edenot E b) + d)) = bv_unsigned (edenot E b) + d) by (apply u_small; lia).
  destruct (expr_eqb ab b) eqn:Hb.
  - apply expr_eqb_eq in Hb. subst ab.
    destruct (Z.leb ak d && Z.ltb d (ak + Z.of_nat w))%bool eqn:Hc.
    + apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      destruct v as [z| | | | | | |]; try discriminate H. injection H as <-.
      replace (bv_unsigned (edenot E b) + d) with (bv_unsigned (adenot E (SA b ak)) + Z.of_nat (Z.to_nat (d - ak))) by (rewrite Hu; lia).
      rewrite (md_newest E m (SA b ak) w (ELit z) rest (Z.to_nat (d - ak)) Hfa ltac:(lia)). reflexivity.
    + rewrite (md_skip E m (SA b ak) w v rest _ Hfa); [exact (IH Hlf Hd H)|].
      rewrite Hu, Hx. apply andb_false_iff in Hc as [Hc|Hc]; [apply Z.leb_gt in Hc | apply Z.ltb_ge in Hc]; lia.
  - destruct (ranges_apart_x kn b d (ELit 1) ab ak (elen w)) eqn:Ha; [|discriminate].
    pose proof (ranges_apart_x_sound segs E M kn b d (ELit 1) ab ak (elen w) HK Ha) as R.
    rewrite elenZ_lit, elenZ_elen in R by exact Hw8. unfold estart in R. cbn [a_base a_off] in R.
    rewrite (md_skip E m (SA ab ak) w v rest _ Hfa); [exact (IH Hlf Hd H)|].
    rewrite Hu, Hx. rewrite Z.mod_small in R by lia. lia.
Qed.

Lemma log_lit_read_sound : forall M m kn lg b n k bs,
  know_ok segs E M kn -> log_flat E lg -> 0 <= bv_unsigned (edenot E b) + k -> bv_unsigned (edenot E b) + k + Z.of_nat n <= 2^64 ->
  log_lit_read kn lg b k n = Some bs ->
  length bs = n /\
  forall i, (i < n)%nat -> mem_denot E m lg (Z_to_bv 64 (bv_unsigned (edenot E b) + k + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  intros M m kn lg b n. induction n as [|n IH]; intros k bs HK Hlf H0 H1 H.
  - injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [log_lit_read] in H. destruct (log_byte kn lg b k) as [x|] eqn:Hx; [|discriminate].
    destruct (log_lit_read kn lg b (k + 1) n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
    destruct (IH (k + 1) r HK Hlf ltac:(lia) ltac:(lia) Hr) as [Hlen Hall].
    split; [cbn; rewrite Hlen; reflexivity|].
    intros [|i] Hi.
    + cbn [nth]. rewrite Z.add_0_r. exact (log_byte_sound M m kn lg b k x HK Hlf ltac:(lia) Hx).
    + cbn [nth]. replace (bv_unsigned (edenot E b) + k + Z.of_nat (S i)) with (bv_unsigned (edenot E b) + (k + 1) + Z.of_nat i) by lia.
      apply Hall. lia.
Qed.

End LitRead.

End SV.
