(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0p.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: kept every memory-call outcome and proved the unrestricted trace realization bridge; changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(** No memory-call outcome is excluded in the may-fail library. *)
Definition mmapclass (_ : kreq) : bool := false.
Definition canswer04 (q : kreq) (z : Z) : Prop :=
if mmapclass q then z = 1 else canswer q z.
Lemma canswer04_canswer : forall q z, canswer04 q z -> canswer q z.
Proof.
intros q z H. unfold canswer04 in H. destruct (mmapclass q) eqn:E; [|exact H].
subst z. unfold canswer. destruct q; cbn in E |- *; try discriminate; auto.
Qed.
Fixpoint cpath04 {A : Type} (t : itree astate A) (tr : list (kreq * Z)) (a : A) : Prop :=
match t, tr with
| IRet a', [] => a' = a
| IAsk q _ k, (q', z) :: tr' => q' = q /\ canswer04 q z /\ cpath04 (k z) tr' a
| _, _ => False
end.
Lemma cpath04_cpath {A} : forall (t : itree astate A) tr a, cpath04 t tr a -> cpath t tr a.
Proof. intros t tr a H. exact H. Qed.
Lemma cpath04_yields {A} : forall (t : itree astate A) tr a, cpath04 t tr a -> yields t tr a.
Proof. intros t tr a H. apply cpath_yields. apply cpath04_cpath. exact H. Qed.
Fixpoint ok04 {A : Type} (G : astate -> kreq -> Prop) (t : itree astate A) : Prop :=
match t with
| IRet _ => True
| IFail _ => True
| IAsk (KJunk p) s k => forall z, 0 <= z < 256 -> ok04 G (k z)
| IAsk q s k =>
if mmapclass q then G s q /\ ok04 G (k 1)
else if fallible q then ok04 G (k 0) /\ ok04 G (k 1)
else ok04 G (k 1)
end.
Lemma gtree_ok04 {A} : forall (G : astate -> kreq -> Prop) (t : itree astate A), gtree G t -> ok04 G t.
Proof.
induction t as [a | q s k IH | e]; intros H; cbn in *; auto.
destruct q; cbn in *; try (destruct H as (H1 & H2 & H3)); repeat split; auto.
Qed.
Lemma ok04_mono {A} : forall (G G' : astate -> kreq -> Prop) (t : itree astate A),
(forall s q, G s q -> G' s q) -> ok04 G t -> ok04 G' t.
Proof.
induction t as [a | q s k IH | e]; intros HG H; cbn in *; auto.
destruct q; cbn in *; try (destruct H as [H1 H2]); repeat split; auto;
intros z Hz; apply IH; auto.
Qed.
Lemma cpath04_ibind {A B} : forall (t : itree astate A) (f : A -> itree astate B) tr1 a tr2 b,
cpath04 t tr1 a -> cpath04 (f a) tr2 b -> cpath04 (ibind t f) (tr1 ++ tr2) b.
Proof.
induction t as [a' | q s k IH | e]; intros f [|[q' z] tr1] a tr2 b H1 H2; cbn in *; try contradiction.
- subst a'. exact H2.
- destruct H1 as (-> & Hc & H1). split; [reflexivity|]. split; [exact Hc|]. eapply IH; eauto.
Qed.
Lemma cpath04_ibind_inv {A B} : forall (t : itree astate A) (f : A -> itree astate B) tr b,
cpath04 (ibind t f) tr b -> exists tr1 a tr2, tr = tr1 ++ tr2 /\ cpath04 t tr1 a /\ cpath04 (f a) tr2 b.
Proof.
induction t as [a' | q s k IH | e]; intros f tr b H; cbn in H.
- exists [], a', tr. cbn. auto.
- destruct tr as [|[q' z] tr]; [destruct H|]. destruct H as (-> & Hc & H).
destruct (IH z f tr b H) as (tr1 & a & tr2 & -> & H1 & H2).
exists ((q, z) :: tr1), a, tr2. cbn. auto.
- destruct tr; destruct H.
Qed.
Lemma cpath04_mbind_inv {A B} : forall (m : M A) (f : A -> M B) (s : astate) tr b,
cpath04 (bind m f s) tr b ->
exists tr1 a s1 tr2, tr = tr1 ++ tr2 /\ cpath04 (m s) tr1 (a, s1) /\ cpath04 (f a s1) tr2 b.
Proof.
intros m f s tr b H. unfold bind in H. destruct (cpath04_ibind_inv _ _ _ _ H) as (tr1 & [a s1] & tr2 & -> & H1 & H2).
exists tr1, a, s1, tr2. auto.
Qed.
Lemma ok04_ibind {A B} : forall (G : astate -> kreq -> Prop) (t : itree astate A) (f : A -> itree astate B),
ok04 G t -> (forall tr a, cpath04 t tr a -> ok04 G (f a)) -> ok04 G (ibind t f).
Proof.
induction t as [a | q s k IH | e]; intros f Ht Hf; cbn in *.
- apply (Hf []). reflexivity.
- assert (REC : forall z, canswer04 q z -> ok04 G (k z) -> ok04 G (ibind (k z) f)).
{ intros z Hz Hk. apply IH; [exact Hk|]. intros tr a Hp. apply (Hf ((q, z) :: tr)). cbn. auto. }
unfold canswer04, canswer in REC.
destruct q; cbn in *;
first [ destruct Ht as [H0 H1]; split; [first [exact H0 | apply REC; auto] | apply REC; auto]
| apply REC; auto
| intros z Hz; apply REC; auto ].
- exact I.
Qed.
Lemma ok04_mbind {A B} : forall (G : astate -> kreq -> Prop) (m : M A) (f : A -> M B) (s : astate),
ok04 G (m s) -> (forall tr a s', cpath04 (m s) tr (a, s') -> ok04 G (f a s')) -> ok04 G (bind m f s).
Proof.
intros G m f s Hm Hf. unfold bind. apply ok04_ibind; [exact Hm|]. intros tr [a s'] H. apply (Hf tr). exact H.
Qed.
Section g.
Variable segs : list Segment.
Theorem mreal_SR04 {R} : forall (t : itree astate R) c (Q : R -> config -> Prop),
mreal segs c t Q -> safe t -> ok04 mgrant t ->
SR segs c (fun c' => exists r tr, cpath04 t tr r /\ Q r c').
Proof.
intros t c Q HR HS HO.
assert (Hpath : forall (u : itree astate R) tr r, cpath u tr r -> cpath04 u tr r).
{ intros u tr r H. exact H. }
eapply SR_mono; [apply (mreal_SR segs t c Q HR HS)|].
intros c' (r & tr & HP & HQ). exists r, tr. split; [apply Hpath; exact HP|exact HQ].
Qed.
End g.
Section h.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.
Theorem malloc_SR_ok :
malloc_realizes B MR ->
forall L A regs mem md n,
call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
ok04 mgrant (malloc n A) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
(fun c' => exists r tr, cpath04 (malloc n A) tr r /\ malloc_leaf B MR L A regs mem md n r c').
Proof.
intros HM L A regs mem md n Hpre Hn Hrange Hok.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
apply (mreal_SR04 segs _ _ _ (HM L A regs mem md n Hpre Hn Hrange)); [apply malloc_safe; [exact HW | lia] | exact Hok].
Qed.
Theorem free_SR_ok :
free_realizes B MR ->
forall L A regs mem md p n,
call_pre B MR L A regs mem md -> In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
ok04 mgrant (free (Some p) A) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(fun c' => exists r tr, cpath04 (free (Some p) A) tr r /\ free_leaf B MR L A regs mem md p n r c').
Proof.
intros HF L A regs mem md p n Hpre Hin Hp Hok.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
apply (mreal_SR04 segs _ _ _ (HF L A regs mem md p n Hpre Hin Hp)); [eapply free_safe; [exact HW | exact Hin] | exact Hok].
Qed.
End h.
End d.
