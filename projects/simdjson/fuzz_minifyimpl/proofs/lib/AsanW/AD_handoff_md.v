(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import MainExport MainFactsAsan.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg ARepInit_kit F_module_dtor_pre.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_at_def : forall (m : mem) A bs, bytes_at asegs m A bs ->
  forall x, A <= x < A + Z.of_nat (length bs) -> exists b, mrd asegs m (wa x) = Some b.
Proof.
  intros m A bs (H0 & H1 & H) x Hx. specialize (H (Z.to_nat (x - A)) ltac:(lia)).
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in H by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E; [exists b; exact H|].
  apply nth_error_None in E. lia.
Qed.
Lemma rw_cells_def : forall (m : mem) A cs, rw_cells asegs m A cs ->
  forall x, A <= x < A + Z.of_nat (cells_size cs) -> exists b, mrd asegs m (wa x) = Some b.
Proof.
  intros m A cs [[WF B] _] x Hx. eapply bytes_at_def; [exact B|]. rewrite (cells_bytes_length cs WF). exact Hx.
Qed.

(* [comment removed for export] *)
Definition f_iv (f : mfact) : option (Z * Z) :=
  match f with
  | MCell (ZLit a) w _ => Some (a, a + Z.of_nat (csize (cellw w 0)))
  | MZeroC (ZLit a) n => Some (a, a + n)
  | MZero (ZLit a) n => Some (a, a + n)
  | MFill (ZLit a) n _ => Some (a, a + n)
  | _ => None
  end.
Lemma csize_cellw : forall w v, csize (cellw w v) = csize (cellw w 0).
Proof. intros w v. do 9 (destruct w as [|w]; [reflexivity|]). reflexivity. Qed.

Lemma f_iv_def : forall V (m : mem) f lo hi, mfact_ok asegs V m f -> f_iv f = Some (lo, hi) ->
  forall x, lo <= x < hi -> exists b, mrd asegs m (wa x) = Some b.
Proof.
  intros V m f lo hi OK E x Hx. destruct f as [a w v|a n|a w v|a n|a n c|l h|a n|a n|a n]; cbn [f_iv] in E; try discriminate;
    destruct a as [z| | | | |]; try discriminate; injection E as <- <-; cbn [mfact_ok zv] in OK.
  - eapply rw_cells_def; [exact OK|]. cbn [cells_size]. rewrite csize_cellw. lia.
  - eapply rw_cells_def; [exact OK|]. cbn [cells_size csize]. lia.
  - exists (Z_to_bv 8 0). unfold mrd. replace x with (z + (x - z)) by lia. rewrite OK by lia. reflexivity.
  - exists (Z_to_bv 8 c). unfold mrd. replace x with (z + (x - z)) by lia. rewrite OK by lia. reflexivity.
Qed.

Definition ivs_of (l : list mfact) : list (Z * Z) := flat_map (fun f => match f_iv f with Some iv => [iv] | None => [] end) l.
Lemma ivs_of_def : forall V (m : mem) l, Forall (mfact_ok asegs V m) l ->
  forall iv, In iv (ivs_of l) -> forall x, fst iv <= x < snd iv -> exists b, mrd asegs m (wa x) = Some b.
Proof.
  intros V m l HF [lo hi] Hin x Hx. unfold ivs_of in Hin. apply in_flat_map in Hin as (f & Hf & Hiv).
  destruct (f_iv f) as [iv|] eqn:E; [|destruct Hiv]. destruct Hiv as [->|[]].
  eapply f_iv_def; [exact (proj1 (Forall_forall _ _) HF f Hf) | exact E | exact Hx].
Qed.

(* [comment removed for export] *)
Fixpoint cov_walk (fuel : nat) (ivs : list (Z * Z)) (lo hi : Z) : bool :=
  match fuel with
  | O => false
  | S k => if hi <=? lo then true else
           match find (fun iv => (fst iv <=? lo) && (lo <? snd iv)) ivs with
           | Some iv => cov_walk k ivs (snd iv) hi
           | None => false
           end
  end.
Lemma cov_walk_sound : forall fuel ivs lo hi, cov_walk fuel ivs lo hi = true ->
  forall x, lo <= x < hi -> exists iv, In iv ivs /\ fst iv <= x < snd iv.
Proof.
  induction fuel as [|k IH]; intros ivs lo hi H x Hx; cbn [cov_walk] in H; [discriminate|].
  destruct (Z.leb_spec0 hi lo); [lia|].
  destruct (find _ ivs) as [iv|] eqn:F; [|discriminate].
  apply find_some in F as [Hin Hc]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (Z_lt_le_dec x (snd iv)); [exists iv; split; [exact Hin| lia]|].
  apply (IH ivs (snd iv) hi H x). lia.
Qed.

(* [comment removed for export] *)
Definition wr_covb (l : list mfact) (A n : Z) : bool :=
  existsb (fun f => match f with MWr (ZLit a) k => (a <=? A) && (A + n <=? a + k) | _ => false end) l.
Lemma wr_cov : forall V (m : mem) l A n, Forall (mfact_ok asegs V m) l -> wr_covb l A n = true -> 0 <= n -> wr_at asegs m A n.
Proof.
  intros V m l A n HF H Hn. apply existsb_exists in H as (f & Hf & E). destruct f as [| | | | | |a k| |]; try discriminate.
  destruct a as [z| | | | |]; try discriminate. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as (W0 & W1 & W). cbn [zv] in *.
  split; [lia|]. split; [lia|]. intros i Hi. replace (A + i) with (z + (A - z + i)) by lia. apply W. lia.
Qed.

(* [comment removed for export] *)
Lemma def_bytes : forall (m : mem) (k : nat) A, 0 <= A -> A + Z.of_nat k <= 2^64 ->
  (forall x, A <= x < A + Z.of_nat k -> exists b, mrd asegs m (wa x) = Some b) ->
  exists j, length j = k /\ bytes_at asegs m A j.
Proof.
  intros m k. induction k as [|k IH]; intros A H0 H1 HD.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (HD A ltac:(lia)) as [b Hb].
    destruct (IH (A + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply HD; lia)) as (j & Lj & (B0 & B1 & B)).
    exists (b :: j). split; [cbn; lia|]. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + replace (A + Z.of_nat 0) with A by lia. exact Hb.
    + replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply B. cbn [length] in Hi. lia.
Qed.
Lemma def_chunk : forall (m : mem) A n, 0 <= n -> wr_at asegs m A n ->
  (forall x, A <= x < A + n -> exists b, mrd asegs m (wa x) = Some b) ->
  exists j, rw_cells asegs m A [CB (Z.to_nat n) j].
Proof.
  intros m A n Hn W HD. pose proof W as (W0 & W1 & _).
  destruct (def_bytes m (Z.to_nat n) A W0 ltac:(lia) ltac:(intros x Hx; apply HD; lia)) as (j & Lj & B).
  exists j. split; [split; [cbn; split; [exact Lj| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed.

Definition sh_okb (l : list mfact) (ivs : list (Z * Z)) (p : Z * Z) : bool :=
  (0 <=? snd p) && wr_covb l (fst p) (snd p) && cov_walk (S (length ivs)) ivs (fst p) (fst p + snd p).
Lemma sh_chunk : forall V (m : mem) l p, Forall (mfact_ok asegs V m) l -> sh_okb l (ivs_of l) p = true ->
  exists j, rw_cells asegs m (fst p) [CB (Z.to_nat (snd p)) j].
Proof.
  intros V m l [A n] HF H. unfold sh_okb in H. cbn [fst snd] in *. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply def_chunk; [exact H1 | eapply wr_cov; eassumption |].
  intros x Hx. destruct (cov_walk_sound _ _ _ _ H3 x Hx) as (iv & Hin & Hiv). eapply ivs_of_def; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition img_okb (l : list mfact) (A : Z) (cs : list cell) : bool :=
  existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (cells_size cs) <=? hi') | _ => false end) l
  && rw_bytes_b asegs A (cells_bytes cs) && (0 <=? A) && (A + Z.of_nat (cells_size cs) <=? 2^64).
Definition gd_cells (g : Z * Z * Z * Z * Z * Z * Z) : list cell :=
  let '(d, beg, sz, swr, nm, md, odr) := g in
  [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 odr)].
Definition gd_okb (l : list mfact) (g : Z * Z * Z * Z * Z * Z * Z) : bool :=
  let '(d, beg, sz, swr, nm, md, odr) := g in
  img_okb l d (gd_cells g) && img_okb l (d + 16) [C1 (Z_to_bv 8 (swr mod 256))].
Lemma img_ok : forall V (m : mem) l A cs, Forall (mfact_ok asegs V m) l -> cells_wf cs -> img_okb l A cs = true -> rw_cells asegs m A cs.
Proof.
  intros V m l A cs HF WF H. unfold img_okb in H. repeat (apply andb_prop in H as [H ?X]).
  apply Z.leb_le in X0. apply Z.leb_le in X. eapply img_chunk; eassumption.
Qed.
Lemma gd_ok : forall V (m : mem) l g, Forall (mfact_ok asegs V m) l -> gd_okb l g = true -> gdesc_t m g.
Proof.
  intros V m l [[[[[[d beg] sz] swr] nm] md] odr] HF H. unfold gd_okb in H. apply andb_prop in H as [H1 H2]. unfold gdesc_t, gdesc. split.
  - eapply (img_ok V m l d (gd_cells (d, beg, sz, swr, nm, md, odr))); [exact HF | cbn; tauto | exact H1].
  - eapply img_ok; [exact HF | cbn; tauto | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Handoff.
  Variables (V : nat -> Z) (m : mem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.

  Lemma gdesc_init : Forall (gdesc_t m) GLOBALS.
  Proof.
    apply Forall_forall. intros g Hg. apply (gd_ok V m asan_mem_facts g HM).
    revert g Hg. apply forallb_forall. vm_compute. reflexivity.
  Qed.

  Lemma godr_init : Forall (fun o => exists b, rw_cells asegs m o [C1 b]) GODRS.
  Proof.
    apply Forall_forall. intros o Ho. exists (Z_to_bv 8 1).
    assert (E : existsb (mfact_eqb (MCell (ZLit o) 1 (ZLit 1))) asan_mem_facts = true).
    { revert o Ho. apply forallb_forall. vm_compute. reflexivity. }
    exact (mfact_find asegs V m _ _ HM E).
  Qed.

  Lemma gsh_init : Forall (fun p => exists j, rw_cells asegs m (fst p) [CB (Z.to_nat (snd p)) j]) GSHADOWS.
  Proof.
    apply Forall_forall. intros p Hp. apply (sh_chunk V m asan_mem_facts p HM).
    revert p Hp. apply forallb_forall.
    change (forallb (sh_okb asan_mem_facts (ivs_of asan_mem_facts)) GSHADOWS = true). vm_compute. reflexivity.
  Qed.

  Lemma garr_init : exists j, rw_cells asegs m GARR_SH [CB (Z.to_nat (8 * Z.of_nat (length GLOBALS))) j].
  Proof.
    apply (sh_chunk V m asan_mem_facts (GARR_SH, 8 * Z.of_nat (length GLOBALS)) HM). vm_compute. reflexivity.
  Qed.
End Handoff.
End CANSEC1.
