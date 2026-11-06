(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/ACej.v; image A's file was copied from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v. The call contexts and allocation traces below are libreac/fuzz_grant's
   IMAGE B ones, read from fuzz_grant.asan-ubsan (bytes bin/ fde52226dc48, symbols unstripped/ 5a5ee7c02b4e, both
   checked against the acceptance root's SHA256SUMS; FACTS f0e6eb38667): the calls of the malloc and
   free wrappers' 4-byte jumps (0x52edc, 0x52ed8) in main, target_run and LLVMFuzzerTestOneInput, the only functions
   that call them, each trace closed under prefixes. NOT ONE pc here is shared with image A's list: A's are
   0x52dec / 0x52c8c with returns 0x80264 / 0x802b8 / 0x80544 / 0x802dc / 0x8040c / 0x805d8 and the harness's
   0x80994 / 0x80e90 / 0x8132c / 0x812a0 / 0x813b8 / 0x817d0 under 0x805ac. A copy of lib/A/ACej.v would therefore
   state plausible addresses that are not this image's traces.
   pc0 DEPENDS ON malloc_context_size, which is 30 on the original image (__asan::InitializeFlags 0x3d8d8:
   addi a1, zero, 0x1e at 0x3d968, sw a1, 0x18c(sp) at 0x3d970, cell 0xa667c), so both interceptors take the mcs > 2
   path and GetCurrentPc returns 0x53178 (malloc) / 0x53018 (free). On a toolchain-N image, where mcs is 1, the
   mcs <= 2 path returns 0x5312c / 0x52ffc instead, and every trace below would be wrong by that one entry.
   The traces are 2 or 3 entries because UnwindFast walks the frame-pointer chain: the interceptors set fp
   (addi s0, sp, 0x7f0 at 0x530d0 and at 0x52f00) and LLVMFuzzerTestOneInput sets fp (addi s0, sp, 0x120 at 0x80a78),
   while main and target_run do not.
   libunwind's DwarfFDECache::add (0x86fc8) calls those jumps too, at 0x87044 and 0x87068, and this list leaves its
   two traces out: that cache is reached only from a report of an error, which the proof shows is not reached
   (on this image fast_unwind_on_malloc is 1 by CommonFlags::SetDefaults 0x61904, and ASAN_OPTIONS is never read,
   because __sanitizer::GetEnv 0x649dc returns NULL through the sealed GOT cell 0x9d710 = 1). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[0x8c978]].
Definition TRACES_main : list (list Z) :=
[[0x53018; 0x80668];
[0x53018; 0x80798];
[0x53178; 0x805f0];
[0x53178; 0x80644]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x806fc]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x80720]].
Definition CTX_target_run : list (list Z) :=
[[0x80710]].
Definition TRACES_target_run : list (list Z) :=
[[0x53018; 0x80964];
[0x53178; 0x808d0]].
Definition CTX_emit_printf : list (list Z) :=
[[0x80948]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x80938]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x53018; 0x8180c];
[0x53018; 0x8180c; 0x80938];
[0x53018; 0x81944];
[0x53018; 0x81944; 0x80938];
[0x53018; 0x81dac];
[0x53018; 0x81dac; 0x80938];
[0x53178; 0x80db8];
[0x53178; 0x80db8; 0x80938];
[0x53178; 0x813d4];
[0x53178; 0x813d4; 0x80938];
[0x53178; 0x818b8];
[0x53178; 0x818b8; 0x80938]].
Definition Tfib_universe : list (list Z) :=
[[0x53018];
[0x53018; 0x80668];
[0x53018; 0x80798];
[0x53018; 0x80964];
[0x53018; 0x8180c];
[0x53018; 0x8180c; 0x80938];
[0x53018; 0x81944];
[0x53018; 0x81944; 0x80938];
[0x53018; 0x81dac];
[0x53018; 0x81dac; 0x80938];
[0x53178];
[0x53178; 0x805f0];
[0x53178; 0x80644];
[0x53178; 0x808d0];
[0x53178; 0x80db8];
[0x53178; 0x80db8; 0x80938];
[0x53178; 0x813d4];
[0x53178; 0x813d4; 0x80938];
[0x53178; 0x818b8];
[0x53178; 0x818b8; 0x80938]].
Fixpoint listZ_eqb (a b : list Z) : bool :=
match a, b with [], [] => true | x :: a', y :: b' => Z.eqb x y && listZ_eqb a' b' | _, _ => false end.
Fixpoint memZL (t : list Z) (l : list (list Z)) : bool :=
match l with [] => false | u :: l' => listZ_eqb t u || memZL t l' end.
Lemma listZ_eqb_eq : forall a b, listZ_eqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; destruct b as [|y b]; cbn; intros H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [exact H1 | apply IH, H2].
Qed.
Lemma memZL_In : forall t l, memZL t l = true -> In t l.
Proof.
induction l as [|u l IH]; cbn; intros H; [discriminate|].
apply Bool.orb_prop in H as [H|H]; [left; symmetry; apply listZ_eqb_eq, H | right; apply IH, H].
Qed.
Fixpoint allb {X} (f : X -> bool) (l : list X) : bool := match l with [] => true | x :: l' => f x && allb f l' end.
Lemma allb_In : forall {X} (f : X -> bool) l x, allb f l = true -> In x l -> f x = true.
Proof. induction l; cbn; intros x H Hin; [destruct Hin|]. apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; auto. Qed.
Lemma TRACES_main_U : forall t, In t TRACES_main -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_main t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_target_run_U : forall t, In t TRACES_target_run -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_LLVMFuzzerTestOneInput_U : forall t, In t TRACES_LLVMFuzzerTestOneInput -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_LLVMFuzzerTestOneInput t ltac:(vm_compute; reflexivity) H). Qed.
Fixpoint nodupZL (l : list (list Z)) : bool :=
match l with [] => true | t :: l' => negb (memZL t l') && nodupZL l' end.
Lemma memZL_false : forall t l, memZL t l = false -> ~ In t l.
Proof.
induction l as [|u l IH]; cbn; intros H Hin; [exact Hin|].
apply Bool.orb_false_elim in H as [H1 H2]. destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)].
assert (E : forall a, listZ_eqb a a = true) by (induction a; cbn; [reflexivity|]; rewrite Z.eqb_refl; assumption).
rewrite E in H1. discriminate.
Qed.
Lemma nodupZL_NoDup : forall l, nodupZL l = true -> NoDup l.
Proof.
induction l as [|t l IH]; cbn; intros H; [constructor|].
apply andb_prop in H as [H1 H2]. constructor; [apply memZL_false; destruct (memZL t l); [discriminate|reflexivity] | apply IH, H2].
Qed.
Lemma Tfib_universe_ok : universe_ok Tfib_universe.
Proof.
split; [unfold DEPOT_MAX; (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split.
- apply Forall_forall. intros t Ht.
pose proof (allb_In (fun t : list Z => (length t <=? kUnwindMax)%nat) Tfib_universe t ltac:(vm_compute; reflexivity) Ht) as H.
apply Nat.leb_le in H. exact H.
- apply nodupZL_NoDup. vm_compute. reflexivity.
Qed.
