(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Definition gm (L : mled) : Z :=
  fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (ld_groups L))
  + fold_right Z.add 0 (map (fun m : Z * Z * Z => mmap_len (snd (fst m))) (ld_metas L)).

(* [comment removed for export] *)
Definition BB (L : mled) : Z :=
  match ld_brk L with
  | BPGuard _ => 2 * PGSZ
  | _ => match ld_brkreg L with Some (_, l) => l | None => 0 end
  end.

(* [comment removed for export] *)
Definition PINB : Z := PGSZ.
#[using="Type"] Lemma PINB_nonneg : 0 <= PINB. Proof. unfold PINB, PGSZ. lia. Qed.

Definition LI (L : mled) (mo : Model) : Prop := vm_live_bytes (m_vmmaps mo) <= gm L + BB L + PINB.

#[using="Type"] Lemma live_bytes_cons e l : live_bytes (e :: l) = bv_unsigned (snd e) + live_bytes l.
Proof. destruct e; reflexivity. Qed.

#[using="Type"] Lemma live_bytes_app l1 l2 : live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; cbn; [reflexivity| rewrite IH; lia]. Qed.

#[using="Type"] Lemma live_bytes_nonneg l : 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

#[using="Type"] Lemma gm_set_brkph ph L : gm (set_brkph ph L) = gm L. Proof. reflexivity. Qed.
#[using="Type"] Lemma gm_set_brkreg v L : gm (set_brkreg v L) = gm L. Proof. reflexivity. Qed.
#[using="Type"] Lemma gm_set_live v L : gm (set_live v L) = gm L. Proof. reflexivity. Qed.
#[using="Type"] Lemma BB_set_live v L : BB (set_live v L) = BB L. Proof. reflexivity. Qed.
#[using="Type"] Lemma gm_add_group a len L : gm (set_groups ((a, len) :: ld_groups L) L) = gm L + mmap_len len.
Proof. unfold gm. cbn. lia. Qed.
#[using="Type"] Lemma gm_add_meta a len L : gm (set_metas ((a, len, 0) :: ld_metas L) L) = gm L + mmap_len len.
Proof. unfold gm. cbn. lia. Qed.
#[using="Type"] Lemma BB_set_groups v L : BB (set_groups v L) = BB L. Proof. reflexivity. Qed.
#[using="Type"] Lemma BB_set_metas v L : BB (set_metas v L) = BB L. Proof. reflexivity. Qed.

#[using="Type"] Lemma sum_map_app {A} (f : A -> Z) l1 l2 : fold_right Z.add 0 (map f (l1 ++ l2)) = fold_right Z.add 0 (map f l1) + fold_right Z.add 0 (map f l2).
Proof. induction l1 as [|x l1 IH]; cbn; [lia| rewrite IH; lia]. Qed.

#[using="Type"] Lemma gm_bump a L : gm (set_metas (map (bump_meta a) (ld_metas L)) L) = gm L.
Proof.
  unfold gm. cbn [ld_groups ld_metas set_metas]. f_equal.
  induction (ld_metas L) as [|[[b l] k] ms IH]; cbn; [reflexivity|]. rewrite IH. unfold bump_meta. destruct (b + (1 + k) * PGSZ =? a); reflexivity.
Qed.

#[using="Type"] Lemma LI_intro L mo : vm_live_bytes (m_vmmaps mo) <= gm L + BB L + PINB -> LI L mo. Proof. intros H. exact H. Qed.
#[using="Type"] Lemma LI_elim L mo : LI L mo -> vm_live_bytes (m_vmmaps mo) <= gm L + BB L + PINB. Proof. intros H. exact H. Qed.

#[using="Type"] Lemma LI_same_vm L L' mo mo' : LI L mo -> vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) -> gm L' = gm L -> BB L' = BB L -> LI L' mo'.
Proof. intros H E1 E2 E3. unfold LI, vm_live_bytes in *. rewrite E1, E2, E3. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BOUND0 (L : mled) (e : ev) (B : Z) : Prop :=
  forall z, answer_ok L e z = true -> gm (event_post L e z) + BB (event_post L e z) <= B.

(* [comment removed for export] *)
Definition GMAX : Z := 2^20.
(* [comment removed for export] *)
Definition QMAX : Z := 2^28.
Definition REQB (e : ev) (B : Z) : Prop :=
  match e with
  | EMmap _ len _ flags => (Z.land flags MAP_FIXED =? 0) = true -> mmap_len len <= QMAX
  | _ => True
  end.

Definition BOUND (L : mled) (e : ev) (B : Z) : Prop := BOUND0 L e B /\ REQB e B.

#[using="Type"] Lemma BOUND_post L e B : BOUND L e B -> forall z, answer_ok L e z = true -> gm (event_post L e z) + BB (event_post L e z) <= B.
Proof. intros [H _]. exact H. Qed.
#[using="Type"] Lemma BOUND_req L e B : BOUND L e B -> REQB e B.
Proof. intros [_ H]. exact H. Qed.

(* [comment removed for export] *)
Fixpoint qtree {R} (B : Z) (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => event_pre L e /\ BOUND L e B /\ forall z, answer_ok L e z = true -> qtree B (event_post L e z) (k z) Post
  end.

#[using="Type"] Lemma qtree_mono {R} B L (t : stree ev Z R) (P P' : mled -> R -> Prop) :
  qtree B L t P -> (forall L' r, P L' r -> P' L' r) -> qtree B L t P'.
Proof.
  revert L. induction t as [r|e k IH]; intros L H HP; cbn in *; [apply HP; exact H|].
  destruct H as (He & HB & Hk). split; [exact He|]. split; [exact HB|]. intros z Hz. apply IH; [apply Hk; exact Hz| exact HP].
Qed.

#[using="Type"] Lemma qtree_ctree_ok {R} B L (t : stree ev Z R) P : qtree B L t P -> ctree_ok L t P.
Proof.
  revert L. induction t as [r|e k IH]; intros L H; cbn in *; [exact H|].
  destruct H as (He & HB & Hk). split; [exact He|]. intros z Hz. apply IH. apply Hk. exact Hz.
Qed.

End WithCeil.
