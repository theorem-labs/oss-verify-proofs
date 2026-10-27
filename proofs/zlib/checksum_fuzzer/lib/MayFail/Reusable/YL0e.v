(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0e.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma jinv_ibind_head {A B} : forall (K : B -> TSet) (t : itree astate A) (f : A -> itree astate B),
jinv K (ibind t f) -> jinv (fun a => tset (f a) K) t.
Proof.
intros K t; induction t as [a' | q s k IH | e]; intros f Hj; cbn in *; try exact I.
destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in Hj |- *;
try (destruct Hj as [H0 H1]; split; apply IH; assumption);
try (apply IH; exact Hj).
destruct Hj as [Heq Hj]. split.
- intros z Hz. rewrite <- !tset_ibind. apply Heq. exact Hz.
- intros z Hz. apply IH. apply Hj. exact Hz.
Qed.
Lemma gtree_ibind_head {A B} : forall (G : astate -> kreq -> Prop) (t : itree astate A) (f : A -> itree astate B),
gtree G (ibind t f) -> gtree G t.
Proof.
intros G t; induction t as [a' | q s k IH | e]; intros f Hg; cbn in *; try exact I.
destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in Hg |- *;
try (destruct Hg as (G0 & H0 & H1); split; [exact G0 | split; eapply IH; eassumption]);
try (eapply IH; exact Hg).
intros z Hz. eapply IH. apply Hg. exact Hz.
Qed.
Lemma jinv_mbind_head {A B} : forall (K : B * astate -> TSet) (m : M A) (f : A -> M B) (s : astate),
jinv K (bind m f s) -> jinv (fun r => tset (let '(a, s') := r in f a s') K) (m s).
Proof. intros K m f s H. unfold bind in H. exact (jinv_ibind_head K (m s) _ H). Qed.
Lemma gtree_mbind_head {A B} : forall (G : astate -> kreq -> Prop) (m : M A) (f : A -> M B) (s : astate),
gtree G (bind m f s) -> gtree G (m s).
Proof. intros G m f s H. unfold bind in H. exact (gtree_ibind_head G (m s) _ H). Qed.
Lemma jinv_mbind_after {A B} : forall (K : B * astate -> TSet) (m : M A) (f : A -> M B) (s : astate) tr a s',
jinv K (bind m f s) -> cpath (m s) tr (a, s') -> jinv K (f a s').
Proof.
intros K m f s tr a s' H Hp. unfold bind in H.
exact (jinv_after K (m s) (fun r => let '(a, s') := r in f a s') tr (a, s') H Hp).
Qed.
Lemma gtree_mbind_after {A B} : forall (G : astate -> kreq -> Prop) (m : M A) (f : A -> M B) (s : astate) tr a s',
gtree G (bind m f s) -> cpath (m s) tr (a, s') -> gtree G (f a s').
Proof.
intros G m f s tr a s' H Hp. unfold bind in H.
exact (gtree_after G (m s) (fun r => let '(a, s') := r in f a s') tr (a, s') H Hp).
Qed.
Lemma tset_mbind' {A B} : forall (m : M A) (f : A -> M B) (s : astate) (K : B * astate -> TSet),
tset (bind m f s) K = tset (m s) (fun r => tset (let '(a, s') := r in f a s') K).
Proof. intros. apply tset_mbind. Qed.
Lemma tset_bind_eq {A B} : forall (t : itree astate (B * astate)) (m : M A) (f : A -> M B) (s : astate) (K : B * astate -> TSet),
t = bind m f s -> tset t K = tset (m s) (fun r => tset (let '(a, s') := r in f a s') K).
Proof. intros t m f s K ->. apply tset_mbind. Qed.
Lemma jinv_head_eq {A B} : forall (K : B * astate -> TSet) (t : itree astate (B * astate)) (m : M A) (f : A -> M B) (s : astate),
t = bind m f s -> jinv K t -> jinv (fun r => tset (let '(a, s') := r in f a s') K) (m s).
Proof. intros K t m f s -> H. exact (jinv_mbind_head K m f s H). Qed.
Lemma gtree_head_eq {A B} : forall (G : astate -> kreq -> Prop) (t : itree astate (B * astate)) (m : M A) (f : A -> M B) (s : astate),
t = bind m f s -> gtree G t -> gtree G (m s).
Proof. intros G t m f s -> H. exact (gtree_mbind_head G m f s H). Qed.
Lemma jinv_after_eq {A B} : forall (K : B * astate -> TSet) (t : itree astate (B * astate)) (m : M A) (f : A -> M B) (s : astate) tr a s',
t = bind m f s -> jinv K t -> cpath (m s) tr (a, s') -> jinv K (f a s').
Proof. intros K t m f s tr a s' -> H Hp. exact (jinv_mbind_after K m f s tr a s' H Hp). Qed.
Lemma gtree_after_eq {A B} : forall (G : astate -> kreq -> Prop) (t : itree astate (B * astate)) (m : M A) (f : A -> M B) (s : astate) tr a s',
t = bind m f s -> gtree G t -> cpath (m s) tr (a, s') -> gtree G (f a s').
Proof. intros G t m f s tr a s' -> H Hp. exact (gtree_mbind_after G m f s tr a s' H Hp). Qed.
Definition dir_k (p0 : option sptr) : M bool := ret (match p0 with None => false | Some _ => true end).
Lemma dir_m_eq : forall s, dir_m s = bind (malloc CAP0) dir_k s.
Proof. intros s. exact (@eq_refl _ (bind (malloc CAP0) dir_k s)). Qed.
Definition driver_tail (data : list byte) (r : rd_result) : M dleaf :=
match r with
| RdOOM => ret DL_oom
| RdRefused => ret DL_refused
| RdLoaded buf cap =>
if dlen data <? HDR_MIN then ret DL_short
else if dlen data <? HDR_MIN + config_len data then ret DL_overrun
else if payload_len data =? 0 then ret (DL_run buf cap None)
else bind (malloc (payload_len data))
(fun p => match p with
| None => ret DL_payload_fail
| Some q => ret (DL_run buf cap (Some q))
end)
end.
Definition driver_after_m1 (data : list byte) (p0 : option sptr) : M dleaf :=
match p0 with
| None => ret DL_oom
| Some b0 => bind (read_phase READ_FUEL (dlen data) CAP0 b0) (driver_tail data)
end.
Lemma driver_tree_eq : forall data, driver_tree data = bind (malloc CAP0) (driver_after_m1 data) init_state.
Proof. intros data. exact (@eq_refl _ (bind (malloc CAP0) (driver_after_m1 data) init_state)). Qed.
Definition payload_k (buf : sptr) (cap : Z) (p : option sptr) : M dleaf :=
match p with None => ret DL_payload_fail | Some q => ret (DL_run buf cap (Some q)) end.
Lemma driver_tail_loaded_eq : forall data buf cap s,
dlen data <? HDR_MIN = false -> dlen data <? HDR_MIN + config_len data = false -> payload_len data =? 0 = false ->
driver_tail data (RdLoaded buf cap) s = bind (malloc (payload_len data)) (payload_k buf cap) s.
Proof. intros data buf cap s H1 H2 H3. unfold driver_tail. rewrite H1, H2, H3. reflexivity. Qed.
End b.
