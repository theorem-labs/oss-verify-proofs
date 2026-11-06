(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libreac/fuzz_decode's ASan build in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v (origin/ossv/recipes c8557374ad2e); module paths changed (cgif lib/X -> lib/Reusable/X). *)
(* ACej: the trace universe of fuzz_decode's start-up certificate, image A.
   Image: the pinned fuzz_decode.asan,
   sha256 5973b76807d8d2e14b82dc6afde70a2c882923658406aeca43681719cb4e8036 (symbols from the unstripped
   twin fuzz_decode.asan, sha256
   4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2).
   CTX_<f> / TRACES_<f> and Tfib_universe below are machine-generated from that image by
   tools/pg-reloc/718254b3f4dd/gen_traces.py, sha256
   59966c88351063828f3118687401542cb3d9512b4e218916c1b930fbdc1d0a8f, run as
     gen_traces.py bin/fuzz_decode/fuzz_decode.asan unstripped/fuzz_decode/fuzz_decode.asan
       --ipc malloc=0x52204 --ipc free=0x520a4 --ipc calloc=0x52438 --fp LLVMFuzzerTestOneInput=0x7ff60
       --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm
   (26 traces, from 17 call sites in 4 functions), plus the five declared override rows of the separate
   commented block below, which that tool cannot emit. The two inputs are reassembled into this unit by
   provenance/startup-gen/A/acej/acej.py, whose control re-emits cgif's released lib/A/ACej.v byte for byte from
   cgif's own data. One generated definition is filtered out here, `--drop-def CTX_check_round_trip`:
   that name belongs to lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:196, and one name carries one meaning. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x7ff60]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52204; 0x80298];
[0x52204; 0x80298; 0x7ff60];
[0x52204; 0x80424];
[0x52204; 0x80424; 0x7ff60];
[0x520a4; 0x807a0];
[0x520a4; 0x807a0; 0x7ff60];
[0x52204; 0x80828];
[0x52204; 0x80828; 0x7ff60];
[0x520a4; 0x809f8];
[0x520a4; 0x809f8; 0x7ff60];
[0x520a4; 0x80a00];
[0x520a4; 0x80a00; 0x7ff60]].
Definition TRACES_check_round_trip : list (list Z) :=
[[0x52204; 0x80c2c];
[0x52204; 0x80c38];
[0x52438; 0x80c50];
[0x520a4; 0x80dec];
[0x520a4; 0x80df4]].
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x52204; 0x7fc18];
[0x52204; 0x7fc6c];
[0x520a4; 0x7fc90];
[0x520a4; 0x7fdc0]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x52204; 0x7fef8];
[0x520a4; 0x7ff8c]].
(* override: gen_traces 59966c88 cannot emit; check_round_trip's last free is a tail jump `j __wrap_free` and its first malloc runs on the caller's s0; each row measured from the listing at <pc> *)
(* The context the statements give check_round_trip. gen_traces printed a `CTX_check_round_trip := [[]]`
   here (it was given no --fp for this function); that name belongs to
   lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:196, so acej.py's --drop-def CTX_check_round_trip filter leaves
   it out of this unit and the statements' value is the only one under that name. The equality
   CTX_check_round_trip_stmt = CTX_check_round_trip is the composition's, not this file's.
   The tool's TRACES_check_round_trip is kept: no statement owns that name (the statements carry the
   Props dec_crt_ufix / dec_crt_uctx, not a trace list), and its five rows are the only source of four
   dec_crt_ufix members and one dec_crt_uctx member of Tfib_universe. The value:
   CTX_check_round_trip = flat_map (fun r => [[r]; [r; RA_LLVMF]]) DEC_LLVMF_RA_CRT with
   DEC_LLVMF_RA_CRT = [0x8061c; 0x809dc] and RA_LLVMF = 0x7ff60
   (lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:167, :196; lib/A/Prog/check_round_trip_cg.v:345-348
   dec_crt_uctx reads it). Measured in the image:
     0x80618: jal 0x5b0  -> 0x80bc8 check_round_trip   in LLVMFuzzerTestOneInput (0x80064, +0x5b4), ra 0x8061c
     0x809d8: jal 0x1f0  -> 0x80bc8 check_round_trip   in LLVMFuzzerTestOneInput (0x80064, +0x974), ra 0x809dc
     0x7ff5c: jal 0x108  -> 0x80064 LLVMFuzzerTestOneInput  in target_run (0x7fe94, +0xc8),      ra 0x7ff60 *)
Definition CTX_check_round_trip_stmt : list (list Z) :=
[[0x8061c];
[0x8061c; 0x7ff60];
[0x809dc];
[0x809dc; 0x7ff60]].
(* The five traces dec_crt_uctx asks of those four contexts and gen_traces does not emit:
   - the four free rows [0x520a4; c] for c in CTX_check_round_trip_stmt. check_round_trip's last free is
     0x80e2c: j -0x2eecc -> 0x51f60 __interceptor_trampoline_free / __wrap_free (entry 0x80bc8, +0x264):
     a tail jump, rd = zero, so it pushes no return address and runs on its caller's frame; gen_traces
     reads only `jal` as a call. pc0 0x520a4 is the long-branch GetCurrentPc return of __interceptor_free
     (0x520a0: jal 0x20968 -> 0x72a08 _ZN11__sanitizer10StackTrace12GetCurrentPcEv, in
     __interceptor_free 0x51f6c, +0x134; decode/PC0-SCAN.md row "__interceptor_free 0x520a0 LONG").
   - the one malloc row [0x52204; 0x80c2c; 0x7ff60]. check_round_trip's first malloc is
     0x80c28: jal -0x2ecc4 -> 0x51f64 __interceptor_trampoline_malloc / __wrap_malloc (entry 0x80bc8,
     +0x60, ra 0x80c2c = DEC_CRT_RA_MALLOC1), and 0x80c2c: mv s0, a0 sets this frame's s0 only after the
     call returns, so at the call s0 still holds the caller's frame pointer and the recorded trace carries
     the caller's spine (tl c). gen_traces extends a function's traces through one --fp FUNC=RA pair for
     every call of that function, so no --fp check_round_trip=... emits this row without corrupting the
     four rows of dec_crt_ufix. pc0 0x52204 is the long-branch GetCurrentPc return of __interceptor_malloc
     (0x52200: jal 0x20808 -> 0x72a08 _ZN11__sanitizer10StackTrace12GetCurrentPcEv, in
     __interceptor_malloc 0x5213c, +0xc4; decode/PC0-SCAN.md row "__interceptor_malloc 0x52200 LONG").
   Owner decision 07:14Z. *)
Definition TRACES_check_round_trip_override : list (list Z) :=
[[0x520a4; 0x8061c];
[0x520a4; 0x8061c; 0x7ff60];
[0x520a4; 0x809dc];
[0x520a4; 0x809dc; 0x7ff60];
[0x52204; 0x80c2c; 0x7ff60]].
Definition Tfib_universe : list (list Z) :=
[[0x520a4];
[0x520a4; 0x7fc90];
[0x520a4; 0x7fdc0];
[0x520a4; 0x7ff8c];
[0x520a4; 0x8061c];
[0x520a4; 0x8061c; 0x7ff60];
[0x520a4; 0x807a0];
[0x520a4; 0x807a0; 0x7ff60];
[0x520a4; 0x809dc];
[0x520a4; 0x809dc; 0x7ff60];
[0x520a4; 0x809f8];
[0x520a4; 0x809f8; 0x7ff60];
[0x520a4; 0x80a00];
[0x520a4; 0x80a00; 0x7ff60];
[0x520a4; 0x80dec];
[0x520a4; 0x80df4];
[0x52204];
[0x52204; 0x7fc18];
[0x52204; 0x7fc6c];
[0x52204; 0x7fef8];
[0x52204; 0x80298];
[0x52204; 0x80298; 0x7ff60];
[0x52204; 0x80424];
[0x52204; 0x80424; 0x7ff60];
[0x52204; 0x80828];
[0x52204; 0x80828; 0x7ff60];
[0x52204; 0x80c2c];
[0x52204; 0x80c2c; 0x7ff60];
[0x52204; 0x80c38];
[0x52438];
[0x52438; 0x80c50]].
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
