(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Machine-generated data computed from the task's compiled program: the calls of the memory-checking runtime's allocation entries in fuzz_preset.asan, with the traces the runtime stores. *)
(* Modified by Theorem Labs, 2026-10: GENERATED for omx-clap-core/fuzz_preset's ASan image (ELF sha256 bff8519bbe3ea0e4) by tools/startup/gen_acej.py sha256 e889984e33269a5c45fba1abede467d07dc6eef02c30c5ebcfd4b2cb22bbb622 from the PauTrlen enumeration of that image (the internal files compose.py and compose-Aprime.json) and CONFIRMED by a run: image A under qemu-riscv64 10.0.11 with gdb at StackDepotPut, every stored trace recorded (the internal file MAINAP.gdb.log; (internal path) (gdb script aprime/main-Ap.gdb sha256 9880d0dc6b1d260e from the internal file gen_gdbmain.py: break at main 0x81140 and StackDepotPut 0x73600, both from the twin's .symtab; print a1's size and the a0 frame array), input small.hdr1.bin sha256 64142c19a44b506a, qemu-riscv64 sha256 44076c56382fea0c, pin 1be0f53d96cb9d6c, twin bff8519bbe3ea0e4; 1291 puts, 26 distinct traces). Every trace the run stored is in this enumeration; the fp-keeping callers continue the walk and it stops at the first frame that does not keep its frame pointer, as the run shows. Why not pg-core's internal file gen_traces.py: with --fp for all four fp-keeping functions it still misses every trace reaching free through fuzz_free's TAIL CALL and keeps one return address per --fp function - the run stored 8 traces it lacks. Not enumerable, so not in any TRACES_<fn> and not in this fixed file: the trace the runtime STORES at tx_put's realloc, whose third word is a run-dependent fake-stack address (the run stored two different ones); that trace is the per-run half (C-TXTRACE, K0's text). Tfib_universe ALSO holds the fixed part of K0's prh_univ_closure CTX0 [] (lib/A/PRH_Base.v, clauses 1-3 and clause 4's code word, --closure-img): 92 traces at CTX0 = [[0x814dc]], from lib/A/PRH_Img.v (its pi_univ_gate 765 reproduced); 1 of them are not prefixes of an enumerated trace: [0x53c74; 0x84db0] (clause 2, tx_put RT_realloc r=0x84db0). CLAUSE 5 (--clause5; K0's approved fifth conjunct, lib/A/PRH_Base.v: forall G F c r' rt r j, prh_reach CTX0 G c -> pi_fp G = true -> pi_fp F = false -> In r' (pi_call_rets G F) -> In r (pi_ret_sites F rt) -> In (prh_trace (prh_pc0 rt) r (firstn j c)) (u_fix (as_universe B))): 92 traces, the allocator sites of each frame-pointer-less callee F of a frame-pointer caller G over G's reachable contexts, every cut, for the 13 pairs G -> F: LLVMFuzzerTestOneInput -> check_as_written, LLVMFuzzerTestOneInput -> pj_free, check_no_overread -> pj_free, check_reject_clean_starved -> pj_write, check_round_trip -> pj_free, check_round_trip -> pj_write, parse_value -> fuzz_malloc, parse_value -> parse_items, parse_value -> parse_string, round_trip_text -> pj_free, round_trip_text -> pj_write, round_trip_text -> tx_put, tx_string -> tx_put; 78 of them are not in the part above, so Tfib_fixed grows from 98 to 176 traces. THEY ARE SLACK: the s0-inheritance refusal passed (the internal file s0inherit.py: every frame-pointer-less function with an allocator site writes s0 before that site), so at each such call s0 is not G's frame pointer and no run stores these traces; they cost room only (univ_of: u_wmax = DEPOT_MAX - |Tfib_fixed|). Sources (sha256): ELF bff8519bbe3ea0e4, compose c0ea9ae381cb417e, run f5851b47fd3cd91c, donor 7e07602a3bc4c449, PRH_Img.v 31cd90ba56d587e2, AF0l.v 3187dd574db2ed1f, CfImgA.v c5a6725c5fb297ef, YG00.v ab27c0a493247f49, compress_stack_depot db79c231afa23a7d. UNIV CARRIER (--univ; a Theorem Labs lane's 12:58Z ruling, YG01 univ_of): Tfib_universe := univ_of Tfib_fixed Tfib_wild; the wild prefixes are the run-dependent stored traces cut before their run word, plus (--wild-cursor) every cursor free site's [pc_free_ra0; r], so that clause 4b holds for every word the cursor frees read, each a trace the closure demands: [0x53878; 0x87764]; [0x53878; 0x87e50]; [0x53c74; 0x84db0]. *)
(* Generator: tools/startup/gen_acej.py sha256 e889984e33269a5c45fba1abede467d07dc6eef02c30c5ebcfd4b2cb22bbb622; image sha256 bff8519bbe3ea0e4d8edf35fa48015b5846960886633a77a5e9f86cb565bd590; compose blob 70a554d4d233bb35adc63657170074364b95fd8e; run blob 744da8d5a019216505f7b955730b466a4370ead2; donor blob 48e54958dc1e04cadd7f1fd493ded40add855bd8; PRH_Img.v blob 934516a622e80a88e84dfcf16a8a973e71f254d5; AF0l.v blob dfca6bb1a8d7310c41b83079655f0bebd80d5350; CfImgA.v blob a09e896af7dc41ec85401ae572a80df2db2823d4; YG00.v blob 041c36e5ac5e6ff4b39e28b957b940e73846dcf5; compress_stack_depot blob efceea417974c71f122c4b1d18f4f1fc1b4ab2f2. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x53878; 0x8120c];
[0x53878; 0x8133c];
[0x539d8; 0x81194];
[0x539d8; 0x811e8]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x53878; 0x81508];
[0x539d8; 0x81474]].
Definition CTX_check_no_overread : list (list Z) :=
[[0x8172c; 0x814dc]].
Definition TRACES_check_no_overread : list (list Z) :=
[[0x53878; 0x81d48; 0x8172c; 0x814dc];
[0x53878; 0x81d50; 0x8172c; 0x814dc];
[0x53878; 0x81d58; 0x8172c; 0x814dc];
[0x539d8; 0x81a94; 0x8172c; 0x814dc];
[0x539d8; 0x81ad8; 0x8172c; 0x814dc];
[0x539d8; 0x81b2c; 0x8172c; 0x814dc]].
Definition CTX_check_as_written : list (list Z) :=
[[]].
Definition TRACES_check_as_written : list (list Z) :=
[[0x53878; 0x82024];
[0x53878; 0x820ac];
[0x539d8; 0x81ff8]].
Definition CTX_check_reject_clean_starved : list (list Z) :=
[[0x818d4; 0x814dc];
[0x81900; 0x814dc]].
Definition TRACES_check_reject_clean_starved : list (list Z) :=
[[0x53878; 0x82350; 0x818d4; 0x814dc];
[0x53878; 0x82350; 0x81900; 0x814dc];
[0x53878; 0x82410; 0x818d4; 0x814dc];
[0x53878; 0x82410; 0x81900; 0x814dc];
[0x53878; 0x82534; 0x818d4; 0x814dc];
[0x53878; 0x82534; 0x81900; 0x814dc]].
Definition CTX_check_round_trip : list (list Z) :=
[[0x818e8; 0x814dc]].
Definition TRACES_check_round_trip : list (list Z) :=
[[0x53878; 0x82b70; 0x818e8; 0x814dc];
[0x53878; 0x82f44; 0x818e8; 0x814dc]].
Definition CTX_round_trip_text : list (list Z) :=
[[0x82a14; 0x818e8; 0x814dc];
[0x82a34; 0x818e8; 0x814dc]].
Definition TRACES_round_trip_text : list (list Z) :=
[[0x53878; 0x84b04; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84b04; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x84b40; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84b40; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x84b48; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84b48; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x84c8c; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84c8c; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x84c94; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84c94; 0x82a34; 0x818e8; 0x814dc]].
Definition CTX_fuzz_malloc : list (list Z) :=
[[]].
Definition TRACES_fuzz_malloc : list (list Z) :=
[[0x539d8; 0x85788]].
Definition CTX_fuzz_realloc : list (list Z) :=
[[]].
Definition TRACES_fuzz_realloc : list (list Z) :=
[[0x53c74; 0x85a38]].
Definition CTX_pj_free : list (list Z) :=
[[]].
Definition TRACES_pj_free : list (list Z) :=
[[0x53878; 0x865ac];
[0x53878; 0x865e0];
[0x53878; 0x865f8];
[0x53878; 0x86614]].
Definition CTX_pj_write : list (list Z) :=
[[]].
Definition TRACES_pj_write : list (list Z) :=
[[0x53878; 0x86c74]].
Definition CTX_parse_items : list (list Z) :=
[[0x85e6c]].
Definition TRACES_parse_items : list (list Z) :=
[[0x53878; 0x87764; 0x85e6c]].
Definition CTX_parse_string : list (list Z) :=
[[0x85e6c]].
Definition TRACES_parse_string : list (list Z) :=
[[0x53878; 0x87e50; 0x85e6c]].
Definition Tfib_fixed : list (list Z) :=
[[0x53878];
[0x53878; 0x8120c];
[0x53878; 0x8133c];
[0x53878; 0x81508];
[0x53878; 0x81d48];
[0x53878; 0x81d48; 0x8172c];
[0x53878; 0x81d48; 0x8172c; 0x814dc];
[0x53878; 0x81d50];
[0x53878; 0x81d50; 0x8172c];
[0x53878; 0x81d50; 0x8172c; 0x814dc];
[0x53878; 0x81d58];
[0x53878; 0x81d58; 0x8172c];
[0x53878; 0x81d58; 0x8172c; 0x814dc];
[0x53878; 0x82024];
[0x53878; 0x82024; 0x814dc];
[0x53878; 0x820ac];
[0x53878; 0x820ac; 0x814dc];
[0x53878; 0x82350];
[0x53878; 0x82350; 0x818d4];
[0x53878; 0x82350; 0x818d4; 0x814dc];
[0x53878; 0x82350; 0x81900];
[0x53878; 0x82350; 0x81900; 0x814dc];
[0x53878; 0x82410];
[0x53878; 0x82410; 0x818d4];
[0x53878; 0x82410; 0x818d4; 0x814dc];
[0x53878; 0x82410; 0x81900];
[0x53878; 0x82410; 0x81900; 0x814dc];
[0x53878; 0x82534];
[0x53878; 0x82534; 0x818d4];
[0x53878; 0x82534; 0x818d4; 0x814dc];
[0x53878; 0x82534; 0x81900];
[0x53878; 0x82534; 0x81900; 0x814dc];
[0x53878; 0x82b70];
[0x53878; 0x82b70; 0x818e8];
[0x53878; 0x82b70; 0x818e8; 0x814dc];
[0x53878; 0x82f44];
[0x53878; 0x82f44; 0x818e8];
[0x53878; 0x82f44; 0x818e8; 0x814dc];
[0x53878; 0x84b04];
[0x53878; 0x84b04; 0x82a14];
[0x53878; 0x84b04; 0x82a14; 0x818e8];
[0x53878; 0x84b04; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84b04; 0x82a34];
[0x53878; 0x84b04; 0x82a34; 0x818e8];
[0x53878; 0x84b04; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x84b40];
[0x53878; 0x84b40; 0x82a14];
[0x53878; 0x84b40; 0x82a14; 0x818e8];
[0x53878; 0x84b40; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84b40; 0x82a34];
[0x53878; 0x84b40; 0x82a34; 0x818e8];
[0x53878; 0x84b40; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x84b48];
[0x53878; 0x84b48; 0x82a14];
[0x53878; 0x84b48; 0x82a14; 0x818e8];
[0x53878; 0x84b48; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84b48; 0x82a34];
[0x53878; 0x84b48; 0x82a34; 0x818e8];
[0x53878; 0x84b48; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x84c8c];
[0x53878; 0x84c8c; 0x82a14];
[0x53878; 0x84c8c; 0x82a14; 0x818e8];
[0x53878; 0x84c8c; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84c8c; 0x82a34];
[0x53878; 0x84c8c; 0x82a34; 0x818e8];
[0x53878; 0x84c8c; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x84c94];
[0x53878; 0x84c94; 0x82a14];
[0x53878; 0x84c94; 0x82a14; 0x818e8];
[0x53878; 0x84c94; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x84c94; 0x82a34];
[0x53878; 0x84c94; 0x82a34; 0x818e8];
[0x53878; 0x84c94; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x865ac];
[0x53878; 0x865ac; 0x814dc];
[0x53878; 0x865ac; 0x8172c];
[0x53878; 0x865ac; 0x8172c; 0x814dc];
[0x53878; 0x865ac; 0x818e8];
[0x53878; 0x865ac; 0x818e8; 0x814dc];
[0x53878; 0x865ac; 0x82a14];
[0x53878; 0x865ac; 0x82a14; 0x818e8];
[0x53878; 0x865ac; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x865ac; 0x82a34];
[0x53878; 0x865ac; 0x82a34; 0x818e8];
[0x53878; 0x865ac; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x865e0];
[0x53878; 0x865e0; 0x814dc];
[0x53878; 0x865e0; 0x8172c];
[0x53878; 0x865e0; 0x8172c; 0x814dc];
[0x53878; 0x865e0; 0x818e8];
[0x53878; 0x865e0; 0x818e8; 0x814dc];
[0x53878; 0x865e0; 0x82a14];
[0x53878; 0x865e0; 0x82a14; 0x818e8];
[0x53878; 0x865e0; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x865e0; 0x82a34];
[0x53878; 0x865e0; 0x82a34; 0x818e8];
[0x53878; 0x865e0; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x865f8];
[0x53878; 0x865f8; 0x814dc];
[0x53878; 0x865f8; 0x8172c];
[0x53878; 0x865f8; 0x8172c; 0x814dc];
[0x53878; 0x865f8; 0x818e8];
[0x53878; 0x865f8; 0x818e8; 0x814dc];
[0x53878; 0x865f8; 0x82a14];
[0x53878; 0x865f8; 0x82a14; 0x818e8];
[0x53878; 0x865f8; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x865f8; 0x82a34];
[0x53878; 0x865f8; 0x82a34; 0x818e8];
[0x53878; 0x865f8; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x86614];
[0x53878; 0x86614; 0x814dc];
[0x53878; 0x86614; 0x8172c];
[0x53878; 0x86614; 0x8172c; 0x814dc];
[0x53878; 0x86614; 0x818e8];
[0x53878; 0x86614; 0x818e8; 0x814dc];
[0x53878; 0x86614; 0x82a14];
[0x53878; 0x86614; 0x82a14; 0x818e8];
[0x53878; 0x86614; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x86614; 0x82a34];
[0x53878; 0x86614; 0x82a34; 0x818e8];
[0x53878; 0x86614; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x86c74];
[0x53878; 0x86c74; 0x818d4];
[0x53878; 0x86c74; 0x818d4; 0x814dc];
[0x53878; 0x86c74; 0x818e8];
[0x53878; 0x86c74; 0x818e8; 0x814dc];
[0x53878; 0x86c74; 0x81900];
[0x53878; 0x86c74; 0x81900; 0x814dc];
[0x53878; 0x86c74; 0x82a14];
[0x53878; 0x86c74; 0x82a14; 0x818e8];
[0x53878; 0x86c74; 0x82a14; 0x818e8; 0x814dc];
[0x53878; 0x86c74; 0x82a34];
[0x53878; 0x86c74; 0x82a34; 0x818e8];
[0x53878; 0x86c74; 0x82a34; 0x818e8; 0x814dc];
[0x53878; 0x87764];
[0x53878; 0x87764; 0x85e6c];
[0x53878; 0x87764; 0x87630];
[0x53878; 0x87e50];
[0x53878; 0x87e50; 0x85e6c];
[0x53878; 0x87e50; 0x87630];
[0x539d8];
[0x539d8; 0x81194];
[0x539d8; 0x811e8];
[0x539d8; 0x81474];
[0x539d8; 0x81a94];
[0x539d8; 0x81a94; 0x8172c];
[0x539d8; 0x81a94; 0x8172c; 0x814dc];
[0x539d8; 0x81ad8];
[0x539d8; 0x81ad8; 0x8172c];
[0x539d8; 0x81ad8; 0x8172c; 0x814dc];
[0x539d8; 0x81b2c];
[0x539d8; 0x81b2c; 0x8172c];
[0x539d8; 0x81b2c; 0x8172c; 0x814dc];
[0x539d8; 0x81ff8];
[0x539d8; 0x81ff8; 0x814dc];
[0x539d8; 0x85788];
[0x539d8; 0x85788; 0x85e6c];
[0x539d8; 0x85788; 0x87630];
[0x53c74];
[0x53c74; 0x84db0];
[0x53c74; 0x84db0; 0x82a14];
[0x53c74; 0x84db0; 0x82a14; 0x818e8];
[0x53c74; 0x84db0; 0x82a14; 0x818e8; 0x814dc];
[0x53c74; 0x84db0; 0x82a34];
[0x53c74; 0x84db0; 0x82a34; 0x818e8];
[0x53c74; 0x84db0; 0x82a34; 0x818e8; 0x814dc];
[0x53c74; 0x84db0; 0x84ad8];
[0x53c74; 0x84db0; 0x84ad8; 0x82a14];
[0x53c74; 0x84db0; 0x84ad8; 0x82a14; 0x818e8];
[0x53c74; 0x84db0; 0x84ad8; 0x82a14; 0x818e8; 0x814dc];
[0x53c74; 0x84db0; 0x84ad8; 0x82a34];
[0x53c74; 0x84db0; 0x84ad8; 0x82a34; 0x818e8];
[0x53c74; 0x84db0; 0x84ad8; 0x82a34; 0x818e8; 0x814dc];
[0x53c74; 0x84db0; 0x850b4];
[0x53c74; 0x84db0; 0x850f8];
[0x53c74; 0x85a38]].
Definition Tfib_wild : list (list Z) :=
[[0x53878; 0x87764];
[0x53878; 0x87e50];
[0x53c74; 0x84db0]].
Definition Tfib_universe : Univ := univ_of Tfib_fixed Tfib_wild.
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
Lemma TRACES_check_no_overread_U : forall t, In t TRACES_check_no_overread -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_no_overread t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_as_written_U : forall t, In t TRACES_check_as_written -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_as_written t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_reject_clean_starved_U : forall t, In t TRACES_check_reject_clean_starved -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_reject_clean_starved t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_round_trip_U : forall t, In t TRACES_check_round_trip -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_round_trip t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_round_trip_text_U : forall t, In t TRACES_round_trip_text -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_round_trip_text t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fuzz_malloc_U : forall t, In t TRACES_fuzz_malloc -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fuzz_malloc t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fuzz_realloc_U : forall t, In t TRACES_fuzz_realloc -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fuzz_realloc t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_pj_free_U : forall t, In t TRACES_pj_free -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_pj_free t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_pj_write_U : forall t, In t TRACES_pj_write -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_pj_write t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_parse_items_U : forall t, In t TRACES_parse_items -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_parse_items t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_parse_string_U : forall t, In t TRACES_parse_string -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_parse_string t ltac:(vm_compute; reflexivity) H). Qed.
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
apply univ_of_ok.
- unfold DEPOT_MAX. apply Z.leb_le. vm_compute. reflexivity.
- apply Forall_forall. intros t Ht.
pose proof (allb_In (fun t : list Z => (length t <=? kUnwindMax)%nat) Tfib_fixed t ltac:(vm_compute; reflexivity) Ht) as H.
apply Nat.leb_le in H. exact H.
- apply nodupZL_NoDup. vm_compute. reflexivity.
Qed.
