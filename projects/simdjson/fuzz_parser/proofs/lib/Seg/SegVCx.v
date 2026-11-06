(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module SVX.

Section Pre.
Variable segs : list Segment.

Definition vc_enrich (f : list kentry -> list sidecond -> list kentry) (c : SG.vc) : SG.vc :=
  SG.VC (SG.vc_kn c ++ f (SG.vc_kn c) (SG.vc_path c)) (SG.vc_path c) (SG.vc_log c) (SG.vc_src c) (SG.vc_tgt c) (SG.vc_facts c).

Definition enrich_ok (f : list kentry -> list sidecond -> list kentry) : Prop :=
  forall E m kn path, know_ok segs E m kn -> scs_denot segs m E path -> know_ok segs E m (f kn path).

Lemma vc_enrich_holds : forall GP f, enrich_ok f -> forall c, SG.vc_holds segs GP (vc_enrich f c) -> SG.vc_holds segs GP c.
Proof.
  intros GP f Hf c H E m HK HP HL HS. unfold vc_enrich in H. cbn [SG.vc_kn SG.vc_path SG.vc_log SG.vc_src SG.vc_tgt SG.vc_facts] in H.
  apply (H E m); try assumption.
  unfold know_ok in *. apply Forall_app. split; [exact HK|]. exact (Hf E m _ _ HK HP).
Qed.

Definition gvc_enrich (f : list kentry -> list sidecond -> list kentry) (g : SG.vc -> bool) (c : SG.vc) : bool := g (vc_enrich f c).

Lemma gvc_enrich_ok : forall GP f g, enrich_ok f -> (forall c, g c = true -> SG.vc_holds segs GP c) ->
  forall c, gvc_enrich f g c = true -> SG.vc_holds segs GP c.
Proof. intros GP f g Hf Hg c H. apply (vc_enrich_holds GP f Hf). exact (Hg _ H). Qed.

(* [comment removed for export] *)
Definition enrich_seq (f1 f2 : list kentry -> list sidecond -> list kentry) (kn : list kentry) (path : list sidecond) : list kentry :=
  let k1 := f1 kn path in k1 ++ f2 (kn ++ k1) path.

Lemma enrich_seq_ok : forall f1 f2, enrich_ok f1 -> enrich_ok f2 -> enrich_ok (enrich_seq f1 f2).
Proof.
  intros f1 f2 H1 H2 E m kn path HK HP. unfold enrich_seq, know_ok in *.
  pose proof (H1 E m kn path HK HP) as K1. apply Forall_app. split; [exact K1|].
  apply H2; [apply Forall_app; split; assumption | exact HP].
Qed.

(* [comment removed for export] *)
Fixpoint esz (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esz a + esz b)
  | EExt _ _ _ a => S (esz a)
  | _ => 1%nat
  end.
Definition small_sc (n : nat) (s : sidecond) : bool := match s with SCBr _ _ a b => Nat.leb (esz a + esz b) n | _ => true end.
Definition vc_trimp (n : nat) (c : SG.vc) : SG.vc :=
  SG.VC (SG.vc_kn c) (List.filter (small_sc n) (SG.vc_path c)) (SG.vc_log c) (SG.vc_src c) (SG.vc_tgt c) (SG.vc_facts c).
Lemma vc_trimp_holds : forall GP n c, SG.vc_holds segs GP (vc_trimp n c) -> SG.vc_holds segs GP c.
Proof.
  intros GP n c H E m HK HP HL HS. unfold vc_trimp in H. cbn [SG.vc_kn SG.vc_path SG.vc_log SG.vc_src SG.vc_tgt SG.vc_facts] in H.
  apply (H E m HK); try assumption.
  unfold scs_denot in *. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _]. exact (proj1 (Forall_forall _ _) HP x Hx).
Qed.
Definition gvc_trimp (n : nat) (g : SG.vc -> bool) (c : SG.vc) : bool := g (vc_trimp n c).
Lemma gvc_trimp_ok : forall GP n g, (forall c, g c = true -> SG.vc_holds segs GP c) ->
  forall c, gvc_trimp n g c = true -> SG.vc_holds segs GP c.
Proof. intros GP n g Hg c H. apply (vc_trimp_holds GP n). exact (Hg _ H). Qed.

(* [comment removed for export] *)
Definition bal256 (k : Z) : Z := let r := k mod 256 in if Z.leb 128 r then r - 256 else r.

Definition mrespell (K : kentry) : list kentry :=
  match K with
  | KRange (EAlu ALU_AND (EAlu ALU_ADD x (ELit k)) (ELit 255)) lo hi =>
      if Z.eqb (bal256 k) k then [] else [KRange (EAlu ALU_AND (EAlu ALU_ADD x (ELit (bal256 k))) (ELit 255)) lo hi]
  | _ => []
  end.

Definition bc_enrich (kn : list kentry) (path : list sidecond) : list kentry := flat_map mrespell kn.

Lemma bal256_mod : forall k, bal256 k mod 256 = k mod 256.
Proof.
  intros k. unfold bal256. pose proof (Z.mod_pos_bound k 256 ltac:(lia)) as R.
  destruct (Z.leb 128 (k mod 256)) eqn:C.
  - replace (k mod 256 - 256) with (k mod 256 + (-1) * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_mod. lia.
  - apply Z.mod_mod. lia.
Qed.

Lemma land255_mod : forall z, Z.land z 255 = z mod 256.
Proof. intros z. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma and255_add_congr : forall E x k k', k mod 256 = k' mod 256 ->
  edenot E (EAlu ALU_AND (EAlu ALU_ADD x (ELit k)) (ELit 255)) = edenot E (EAlu ALU_AND (EAlu ALU_ADD x (ELit k')) (ELit 255)).
Proof.
  intros E x k k' Hk. cbn [edenot]. rewrite !alu_and, !alu_add. unfold v_and, v_add. f_equal.
  assert (M : forall z, z mod 2 ^ 64 mod 256 = z mod 256).
  { intros z. change (2 ^ 64) with (256 * 2 ^ 56). rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia. }
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (255 mod 2 ^ 64) with 255.
  rewrite !land255_mod. rewrite !M. set (X := bv_unsigned (edenot E x)).
  rewrite alu_add. unfold v_add. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite M. fold X. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z.add_mod X (k mod 2 ^ 64)), (Z.add_mod X (k' mod 2 ^ 64)) by lia. rewrite !M. rewrite Hk. reflexivity.
Qed.

Lemma mrespell_ok : forall E m K, kentry_ok segs E m K -> know_ok segs E m (mrespell K).
Proof.
  intros E m K H. unfold know_ok.
  destruct K as [| | | | | |e lo hi| | | ]; try constructor.
  destruct e as [| |o a b| | | | |]; try constructor. destruct o; try constructor.
  destruct a as [| |o' x kk| | | | |]; try constructor. destruct o'; try constructor.
  destruct kk as [k| | | | | | |]; try constructor. destruct b as [c| | | | | | |]; try constructor.
  destruct (Z.eqb c 255) eqn:Cc; [apply Z.eqb_eq in Cc; subst c|].
  2:{ cbn [mrespell]. destruct c as [|p|p]; try constructor; destruct p; try constructor;
      repeat match goal with p : positive |- _ => destruct p; try constructor end; discriminate. }
  cbn [mrespell]. destruct (Z.eqb (bal256 k) k); [constructor|]. constructor; [|constructor].
  cbn [kentry_ok] in *. rewrite <- (and255_add_congr E x k (bal256 k)) by (symmetry; apply bal256_mod). exact H.
Qed.

Lemma bc_enrich_ok : enrich_ok bc_enrich.
Proof.
  intros E m kn path HK _. unfold bc_enrich, know_ok in *. induction HK as [|K kn HK1 HK IH]; [constructor|].
  cbn [flat_map]. apply Forall_app. split; [apply mrespell_ok; exact HK1 | exact IH].
Qed.

End Pre.
End SVX.
