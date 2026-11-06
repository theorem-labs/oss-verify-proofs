(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the trace universe for libreac/fuzz_decode.asan-ubsan (pin sha256 5d05689f), computed by tools/pg-reloc/718254b3f4dd/gen_traces.py (sha256 59966c88351063828f3118687401542cb3d9512b4e218916c1b930fbdc1d0a8f) over this image's audited allocator interceptor pc0s (--ipc malloc=0x52250 free=0x520f0 calloc=0x52484 --fp LLVMFuzzerTestOneInput=0x7ffac), base provenance/startup-gen/B/acej/src/B.v.txt (gen_traces' output: 26 traces, 17 call sites, 4 functions: LLVMFuzzerTestOneInput, check_round_trip, main, target_run); in cgif's YCej form with its module paths changed. The four check_round_trip tail-free traces gen_traces cannot emit are the declared override rows TRACES_check_round_trip_override (the commented block before Tfib_universe), which Tfib_universe includes; the unit is emitted by provenance/startup-gen/A/acej/acej.py (sha256 5db4ca1babf0c593537907c71d0593f120ec40857d9e947709bf197687fdcf9e) with --overrides, as image A's lib/A/ACej.v is (run: provenance/startup-gen/B/acej/run.sh). One generated definition is filtered out here, `--drop-def CTX_check_round_trip`: that name belongs to lib/B/Prog/LLVMFuzzerTestOneInput_cg.v:198, and one name carries one meaning. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x7ffac]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52250; 0x8032c];
[0x52250; 0x8032c; 0x7ffac];
[0x52250; 0x804c8];
[0x52250; 0x804c8; 0x7ffac];
[0x520f0; 0x808e8];
[0x520f0; 0x808e8; 0x7ffac];
[0x52250; 0x80978];
[0x52250; 0x80978; 0x7ffac];
[0x520f0; 0x80b70];
[0x520f0; 0x80b70; 0x7ffac];
[0x520f0; 0x80b78];
[0x520f0; 0x80b78; 0x7ffac]].
Definition TRACES_check_round_trip : list (list Z) :=
[[0x52250; 0x80dbc];
[0x52250; 0x80dcc];
[0x52484; 0x80de8];
[0x520f0; 0x80ff8];
[0x520f0; 0x81000]].
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x52250; 0x7fc64];
[0x52250; 0x7fcb8];
[0x520f0; 0x7fcdc];
[0x520f0; 0x7fe0c]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x52250; 0x7ff44];
[0x520f0; 0x7ffd8]].
(* override: four check_round_trip tail-free traces that gen_traces 59966c88 cannot emit (REPORT.md:105-114, a Theorem Labs lane 07:14Z).
   check_round_trip (0x80d54) frees its buffer with a TAIL JUMP, `j __wrap_free`, at 0x8103c (check_round_trip+0x2e8),
   measured from image B's own listing: `0x8103c: j -0x2f090` -> 0x8103c-0x2f090 = 0x51fac = __wrap_free; free's pc0 is
   0x520f0 (the GetCurrentPc return at `0x520ec: jal 0x20968` -> 0x72a54). gen_traces.py:58-59 skips a tail jump (rd != ra)
   as "not a call", so the free's trace -- its pc0 followed by check_round_trip's CALLER context -- is not built. The two
   `jal check_round_trip` sites in LLVMFuzzerTestOneInput are 0x8073c and 0x80b50 (`jal 0x80d54`), return addresses
   0x80740 and 0x80b54; RA_LLVMF is 0x7ffac. Every pc cross-checked against image B's listing by command.
   The four traces, exactly as LLVMFuzzerTestOneInput_cg.v names them (CTX_check_round_trip free-tail members):
     [0x520f0; 0x80740]
     [0x520f0; 0x80740; 0x7ffac]
     [0x520f0; 0x80b54]
     [0x520f0; 0x80b54; 0x7ffac]
   Their prefixes [0x520f0] and [0x520f0; 0x80740 ...] add nothing new to Tfib_universe beyond what is already present. *)
Definition TRACES_check_round_trip_override : list (list Z) :=
[[0x520f0; 0x80740];
[0x520f0; 0x80740; 0x7ffac];
[0x520f0; 0x80b54];
[0x520f0; 0x80b54; 0x7ffac]].
Definition Tfib_universe : list (list Z) :=
[[0x520f0];
[0x520f0; 0x7fcdc];
[0x520f0; 0x7fe0c];
[0x520f0; 0x7ffd8];
[0x520f0; 0x80740];
[0x520f0; 0x80740; 0x7ffac];
[0x520f0; 0x808e8];
[0x520f0; 0x808e8; 0x7ffac];
[0x520f0; 0x80b54];
[0x520f0; 0x80b54; 0x7ffac];
[0x520f0; 0x80b70];
[0x520f0; 0x80b70; 0x7ffac];
[0x520f0; 0x80b78];
[0x520f0; 0x80b78; 0x7ffac];
[0x520f0; 0x80ff8];
[0x520f0; 0x81000];
[0x52250];
[0x52250; 0x7fc64];
[0x52250; 0x7fcb8];
[0x52250; 0x7ff44];
[0x52250; 0x8032c];
[0x52250; 0x8032c; 0x7ffac];
[0x52250; 0x804c8];
[0x52250; 0x804c8; 0x7ffac];
[0x52250; 0x80978];
[0x52250; 0x80978; 0x7ffac];
[0x52250; 0x80dbc];
[0x52250; 0x80dcc];
[0x52484];
[0x52484; 0x80de8]].
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
Lemma TRACES_LLVMFuzzerTestOneInput_U : forall t, In t TRACES_LLVMFuzzerTestOneInput -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_LLVMFuzzerTestOneInput t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_round_trip_U : forall t, In t TRACES_check_round_trip -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_round_trip t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_main_U : forall t, In t TRACES_main -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_main t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_target_run_U : forall t, In t TRACES_target_run -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_round_trip_override_U : forall t, In t TRACES_check_round_trip_override -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_round_trip_override t ltac:(vm_compute; reflexivity) H). Qed.
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
