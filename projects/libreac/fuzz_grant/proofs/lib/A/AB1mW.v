(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YA0c.v, with its module paths changed; 76 of its 106 lines of code are new or changed and 341 lines of the source are left out. *)
(* Copied from proofs/libreac/fuzz_disco/lib/Reusable/YB1mW.v (a working branch 29ff9194385), with its
   module paths and file names changed; fuzz_grant's APG.check (lib/Reusable/YA0c.v) is the same as fuzz_disco's.
   walk runs APG.check's single-continuation steps (lc = None) and stops at the first other node; walk_ok and
   walk_step say that check gives the same result from the stop point. via_step and split_step are check's PVia and
   PSplit steps. AB1m.v uses them to check its start-up certificate in pieces that compile in parallel
   (AB1mP, AB1mA, AB1mB, AB1mC), each by vm_cast as before. walk_out and pair_out read the parts of a tuple
   equation, so that one vm_cast computes a walk once and checks several facts about its stop state. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0c YK09 YA01 YA0c.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import APG.
Section w.
Variable segs : list Segment.
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable XN : nat -> list expr -> acs -> option acs.
Variable XE : nat -> list expr -> acs -> option (Z * list spiece * acs).
Variable XB : nat -> list expr -> acs -> option (acs * acs).
Variable HS : nat -> option acs.
Variable hole_le : nat -> nat -> bool.
Variable KC : nat.
Variable bfuel : nat.
Fixpoint walk (n f : nat) (cs : acs) (p : plan) {struct n} : nat * acs * plan :=
match n with
| O => (f, cs, p)
| S n' =>
match f with
| O => (f, cs, p)
| S f' =>
match p with
| PRun stops k =>
match run_block_gc segs IT nx0 KC bfuel (stops ++ STOPS A) cs with
| Some cs' => walk n' f' cs' k
| None => (f, cs, p)
end
| PX x args k => match node_x segs A nx0 x args cs with Some cs' => walk n' f' cs' k | None => (f, cs, p) end
| PSys y k =>
if is_ecall_at segs cs then
match node_sys A nx0 y cs with Some cs' => walk n' f' cs' k | None => (f, cs, p) end
else (f, cs, p)
| PExt id args k => match XN id args cs with Some cs' => walk n' f' cs' k | None => (f, cs, p) end
| PMmap ka kb =>
if is_ecall_at segs cs then
match node_mmap2g A nx0 LIMIT cs with Some (_, csb) => walk n' f' csb kb | None => (f, cs, p) end
else (f, cs, p)
| PMmapIn ka kb kc =>
if is_ecall_at segs cs then
match node_mmapin_g A LIMIT false cs with Some (_, csb, _) => walk n' f' csb kb | None => (f, cs, p) end
else (f, cs, p)
| PDropRange b m k => walk n' f' (node_droprange cs b m) k
| PGcKeep ws k => walk n' f' (set_kn cs (kn_keep (kn cs) ws)) k
| PFresh r logc base k => match node_fresh nx0 cs r logc base with Some cs' => walk n' f' cs' k | None => (f, cs, p) end
| PBump m k => match node_bump cs m with Some cs' => walk n' f' cs' k | None => (f, cs, p) end
| _ => (f, cs, p)
end
end
end.
Lemma walk_ok : forall n f cs p,
check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel f None cs p =
let '(f', cs', p') := walk n f cs p in check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel f' None cs' p'.
Proof.
induction n as [|n IH]; intros f cs p; [reflexivity|].
destruct f as [|f]; [reflexivity|].
destruct p; cbn [walk]; try reflexivity;
repeat match goal with
| |- _ = match ?t with _ => _ end =>
lazymatch t with
| walk _ _ _ _ => fail
| match ?x with _ => _ end => let E := fresh "E" in destruct x eqn:E; cbn beta iota
end
end;
try reflexivity;
match goal with |- _ = match walk n ?f' ?c' ?k' with _ => _ end => rewrite <- (IH f' c' k') end;
clear IH; cbn [check negb];
repeat match goal with E : _ = _ |- _ => rewrite E; clear E end;
reflexivity.
Qed.
Lemma via_step : forall f cs j js lo karms k sk,
via_ok nx0 cs js lo = true ->
check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel f None js k = COk sk ->
check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel (S f) None cs (PVia j js lo karms k) =
check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel f (Some (JC j js sk (nxt cs) lo)) cs karms.
Proof. intros f cs j js lo karms k sk H1 H2. cbn [check negb]. rewrite H1. cbn beta iota. rewrite H2. reflexivity. Qed.
Lemma split_step : forall f cs e mid k1 k2 lo hi s1 s2,
expr_vars_lt nx0 e = true -> erange (kn cs) e = Some (lo, hi) -> (Z.leb lo mid && Z.ltb mid hi)%bool = true ->
check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel f None (set_kn cs (KRange e lo mid :: kn cs)) k1 = COk s1 ->
check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel f None (set_kn cs (KRange e (mid + 1) hi :: kn cs)) k2 = COk s2 ->
check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel (S f) None cs (PSplit e mid k1 k2) = COk (SCase e mid s1 s2).
Proof.
intros f cs e mid k1 k2 lo hi s1 s2 H1 H2 H3 H4 H5. cbn [check negb].
rewrite H1; cbn beta iota; rewrite H2; cbn beta iota; rewrite H3; cbn beta iota; rewrite H4; cbn beta iota; rewrite H5.
reflexivity.
Qed.
Lemma walk_step : forall n f cs p f' cs' p', walk n f cs p = (f', cs', p') ->
check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel f None cs p =
check segs IT A nx0 LIMIT XN XE XB HS hole_le KC bfuel f' None cs' p'.
Proof. intros n f cs p f' cs' p' H. rewrite (walk_ok n f cs p), H. reflexivity. Qed.
End w.
Lemma walk_out : forall (w : nat * acs * plan) (R : Type) (G : acs -> R) (f0 : nat) (p0 : plan) (r0 : R),
(fst (fst w), snd w, G (snd (fst w))) = (f0, p0, r0) ->
w = (f0, snd (fst w), p0) /\ G (snd (fst w)) = r0.
Proof.
intros [[f cs] p] R G f0 p0 r0 H. cbn in H |- *. injection H as Hf Hp Hr. subst f0 p0. split; [reflexivity | exact Hr].
Qed.
Lemma pair_out : forall (A B : Type) (a a' : A) (b b' : B), (a, b) = (a', b') -> a = a' /\ b = b'.
Proof. intros A B a a' b b' H. injection H as Ha Hb. split; assumption. Qed.
