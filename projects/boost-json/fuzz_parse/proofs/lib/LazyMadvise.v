(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  Scfg SimInv ExitSim PropExec CatSim MmapSim AllocSim RelSpec
  ShapeAlg Nodes AgentNodes Gap04 RefNodes SReach AllocNodes
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem5State06in_arg37Corelib4Init5Logicj62eqj63iff37Corelib7Numbers7BinNumsl54Nposl51Z3h5LinuxProcessSemanticsfLinuxProcessSem5Monadn97outcome3h5LinuxProcessSemanticsfLinuxProcessSem5Specsr1csyscall_spec05Model0dSyscallEffect0cSyscallInput08in_sysno5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm7Madvisehhccmadvise_spec4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Syscallhm35int3235stdpp9bitvectorbdefinitionshq0bbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSem3RunhscbInjectedArm37Corelib4Init9Datatypesig74Noneig76optionhsccinjected_armig74boolig74truehhch2madvise_dontneed_b46Stdlib6ZArith6BinInt1Zim86moduloim83powhq02bvig73nilig74prodhq07Z_to_bvig74consig75falseig74listig73natig74pairn92Ok07MemCopy05event08m_vmmaps09mkEffectU0fpage_round_up_Z09page_size0atwo_pow_64hhch5madvise_dontneed_nexthhch3madvise_dontneed_okhm35w_is0im83addim82lt69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~jn3h5same_but_materialized09m_vm_lazy0h1m_vm_materialized0h2page_outside_range36Stdlib5Lists4Listkg06filter06VmMaps08m_haltedjn3aeager_used3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskjd6ms_memkjddmachine_statehsccapply_effect69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~kpf5zfillj63andim82le0bregion_free0dmaps_subtract69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~lgaeentries_nowrapkjd6ms_gprhsc9sys_inputig74Someig74andbig74negbjn37hiddenbjn3azin_rangeb79OSSVerify6Proofsaboost_jsonafuzz_parse3libbLazyMadvise8WithSegs~~~~~~lq15mzerojn3ain_rangesbjn38restricthsc5mkCfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~mh44lzokhsch0advance_past_svc69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LazyNodes~~~~~~mma6sysretmh48hid_same69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SReach~~~~~~mrc6sreachj63notkjdems_svc_pendinghsc6config0cmap_contains07vm_maps0bvm_noaccess0bvm_reserved3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypenl27Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma syscall_spec_233 : ltac2:(zQ "e0!ie!ka!kf!me!n5!q7!tf!ue!v5!hg4!hh2!hl3!hp7!hrd>1i$9>1m$7>1o@1$5$8>0@3$1$4@2$d@1$3#k0@1$a^3+u9@2$2@3$6^4^3^2@6$b@2$0^4N0@2$0^4N1@1$c@2$0^4N2^4^3^2").
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

(* [comment removed for export] *)
Lemma injected_arm_none_233 : ltac2:(zQ "50!hv8!ihf!ii7!ka!ij1@3$3@1$2$0@1$4+u9@1$1$0").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_b_int32 : ltac2:(zQ "b0!ka!me!ik1!ik9!n5!il1!hp7!io0!ioa!ip1!hrd>1w@1$9@1$1#k0>0@3$0$4@2$7@2$a@1$1#k0^1@2$8+2+i0+4@3$0$2@1$5@1$6^2$3").
Proof.
  intros w H. unfold madvise_dontneed_b, int32, abi_low32, MADV_DONTNEED. rewrite H.
  apply Z.eqb_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_outcome : ltac2:(zQ "i42!me!ip1!ip7!ipe!ka!ik1!v5!hrd!ik9!n5!q7!iq6!ir1!ir9!is2!isa!it1!kf!it9!ite!ue!hg4!iu7!iue!iv8!jg3!jh4!jhf!il1!jib!jk5!hl3!jld!jm6!jmd!io0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>6advice@1$1@1$0#k0>1i$h5>1m$h4>1o@1$a$6>0@3$4$9@2$i3@2$7@1$0#k0^6$haZ>0@3$4$5@1$hc^5$8>0@3$4$5@1$i0^7$d=2nZ$9@1$h9@2$7@1$0#k0^8=1n@1$1@1$0#k0@2$b@1$0#k0^1>0@2$i2@2$i1@2$7@1$0#k0^b^2$hb>0@3$4$5@3$he@1$h7^8^c^2$8@2$h1@6$hf^d^c^b^a^9^8@3$4@1$a$6^8@4$h2$6@6$h8@2$b@1$0#k0Z@1$2@2$3@1$1@1$0#k0@1$e@1$1@1$0#8@3$c~0@4$h0@1$1@1$0#k0@1$1@1$0#k0^d^3~1~1@1$2$h3@1$2@2$3@1$1@1$0#k0$f@3$hd^9^d^3@1$2$h6").
Proof.
  intros addr len advice i m o Hal Hadv Hlen. cbv zeta. intros Hnw Hok.
  unfold madvise_spec. rewrite (proj2 (Z.eqb_eq _ _) Hal), Hadv, Hlen. cbn [negb].
  rewrite (proj2 (Z.leb_gt _ _) Hnw). rewrite bind_get_model. cbv beta zeta. rewrite Hok.
  sys_unfold. split.
  - destruct o as [x m' evs|]; intros H; inv_sys. reflexivity.
  - intros ->. neexists 4. split; [reflexivity|]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma madvise_dontneed_next_sbm : ltac2:(zQ "50!me!ip1!ue!jib!jr2>1m$2>4addr@1$1@1$0#k0>1n@1$1@1$0#k0@2$4^3@3$3^3^2^1").
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_lazy : ltac2:(zQ "80!me!ip1!jsc!is2!ipe!ka!ue!jib>1m$6>4addr@1$1@1$0#k0>1n@1$1@1$0#k0@3$5@1$3@2$4@1$1@1$0#k0@1$1@1$0#k0@1$2@3$7^3^2^1@1$2^3").
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_materialized : ltac2:(zQ "b0!me!ip1!hrd!jt7!is2!ka!ue!jub!jib!kh3!jm6>1m$6>4addr@1$1@1$0#k0>1n@1$1@1$0#k0@3$5@1$4@1$1@1$0#k0@1$3@3$8^3^2^1@3$9@1$1@1$0#k0@2$7@2$2@1$0#k0^2@2$a@2$2@1$0#k0^2@2$2@1$0#k0^1@1$3^3").
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_vmmaps : ltac2:(zQ "70!me!iue!ip1!ka!ue!khd!jib>1m$4>4addr@1$2@1$0#k0>1n@1$2@1$0#k0@3$3$5@1$1@3$6^3^2^1@1$1^3").
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_halted : ltac2:(zQ "70!me!ip1!ki5!ii7!ka!ue!jib>1m$5>4addr@1$1@1$0#k0>1n@1$1@1$0#k0@3$4@1$3@1$1@1$0#k0@1$2@3$6^3^2^1@1$2^3").
Proof. intros [fd [maps lazy mat] io fs proc lim tm] addr n. reflexivity. Qed.

Lemma madvise_dontneed_next_eager : ltac2:(zQ "70!me!kif!ip1!ka!n5!ue!jib>1m$5>4addr@1$2@1$0#k0>1n@1$2@1$0#k0@3$3$4@1$1@3$6^3^2^1@1$1^3").
Proof. intros m addr n. apply same_but_materialized_eager. apply madvise_dontneed_next_sbm. Qed.

(* [comment removed for export] *)
Lemma apply_effect_mem_zeros_ret : ltac2:(zQ "h02!me!ip1!ip7!ipe!kn4!ir1!is2!isa!ii7!it1!ka!kne!kof!ite!iv8!kt9&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>2ms$b>1r@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0@3$a>0@1$1@1$0#k0@1$8@1$1@1$0#8@1$4@2$c^4@6$e^3@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8@3$5~0@4$9@1$1@1$0#k0@1$1@1$0#k0^2^1~1~1@1$2$d@1$2@2$3@1$1@1$0#k0$7@3$f^2^1@1$4^4").
Proof.
  intros ms r a n. cbn. apply functional_extensionality. intros x.
  unfold zfill, zmem, zeros_cover. cbn.
  destruct ((bv_unsigned a <=? bv_unsigned x)%Z && (bv_unsigned x <? bv_unsigned a + bv_unsigned n)%Z); reflexivity.
Qed.
End FPX1.

Local Lemma u64_small : ltac2:(zQ "90!me!n5!ku2!ka!ku8!jmd!ioa!iq6!hrd>1z$1>0@2$2@2$4Z^1@2$5^1@2$6+2+k0@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z. exact Hz. Qed.

(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma region_free_maps_subtract : ltac2:(zQ "b0!me!ip1!ik1!ik9!ka!n5!kue!is2!ipe!kvb!lk7>1X@1$7@2$8@1$1@1$0#k0@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>2lo$5>2hi$5>0@1$a^5>0@3$4$2@3$6^6^5^4$3@3$4$2@3$6@3$9^7^4^3^6^5$3").
Proof.
  induction X as [|[b s] X IH]; intros a n lo hi HX HF; [reflexivity|].
  apply entries_nowrap_cons in HX. destruct HX as [Hb HX]. unfold entry_nowrap, LazyLedger.hi in Hb. cbn [fst snd] in Hb.
  cbn [region_free] in HF. apply andb_true_iff in HF. destruct HF as [H1 H2].
  apply negb_true_iff in H1. unfold iv_overlap in H1.
  pose proof (word_unsigned_range b) as Rb. pose proof (word_unsigned_range s) as Rs. unfold two_pow_64 in *.
  cbn [maps_subtract]. unfold iv_subtract.
  assert (HT : region_free (maps_subtract X lo hi) a n = true) by (apply IH; assumption).
  assert (NOV : ~ ((bv_unsigned a < bv_unsigned b + bv_unsigned s) /\ (bv_unsigned b < bv_unsigned a + bv_unsigned n))%Z).
  { intros [C1 C2]. apply andb_false_iff in H1. destruct H1 as [D|D]; apply Z.ltb_ge in D; lia. }
  destruct (Z.ltb_spec (bv_unsigned b) lo) as [L1|L1]; destruct (Z.ltb_spec hi (bv_unsigned b + bv_unsigned s)) as [R1|R1];
    cbn [app region_free]; rewrite ?HT, ?andb_true_r.
  - apply andb_true_iff. split; apply negb_true_iff; unfold iv_overlap.
    + rewrite u64_small by lia.
      apply andb_false_iff. destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b + Z.min (bv_unsigned s) (lo - bv_unsigned b))); [|left; reflexivity].
      right. apply Z.ltb_ge. lia.
    + rewrite !u64_small by lia.
      apply andb_false_iff. destruct (Z.ltb_spec (bv_unsigned a) (Z.max (bv_unsigned b) hi + (bv_unsigned b + bv_unsigned s - Z.max (bv_unsigned b) hi))); [|left; reflexivity].
      right. apply Z.ltb_ge. lia.
  - apply negb_true_iff; unfold iv_overlap. rewrite u64_small by lia.
    apply andb_false_iff. destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b + Z.min (bv_unsigned s) (lo - bv_unsigned b))); [|left; reflexivity].
    right. apply Z.ltb_ge. lia.
  - apply negb_true_iff; unfold iv_overlap. rewrite !u64_small by lia.
    apply andb_false_iff. destruct (Z.ltb_spec (bv_unsigned a) (Z.max (bv_unsigned b) hi + (bv_unsigned b + bv_unsigned s - Z.max (bv_unsigned b) hi))); [|left; reflexivity].
    right. apply Z.ltb_ge. lia.
  - reflexivity.
Qed.
End FPX2.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!is2!no7@1$0$1").
Context {SC : StepCfg}.

Local Open Scope Z_scope.

Lemma in_arg0_sys_input_m : ltac2:(zQ "70!me!ip1!ka!kne!ll9!lm3!ie>2ms$3>2x8@1$1@1$0#k0@3$2@1$1@1$0#k0@2$6@3$5?4segs^2^1N0@2$4^2N0").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mzero : ltac2:(zQ "53!me!ip1!ipe!is2!ii7&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$3~0&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1L~1>1S~1>1r~0>1M~2~2") := ltac2:(zQ "d2!me!ip1!ipe!ik1!is2!ii7!ln0!ln8!lo0!lo8!lp3!iq6!hrd&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0\1L~1\1S~1\1r~0\1M>0@1$1@1$0#k0@1$5@1$1@1$0#8\1x@1$1@1$0#k0M3\0$3@1$5@1$1@1$0#8@2$7@2$a@2$c@1$0#k0^1^3@1$8@3$9^5^4^1@2$6@1$1@1$0#8@2$b@1$0#8Z@1^2^1").

(* [comment removed for export] *)
Lemma mzero_zfill : ltac2:(zQ "h13!me!ip1!hrd!is2!ii7!ipe!ka!ik1!ir9!it1!ku2!lu8!lo8!kt9!jm6!ku8!jmd&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$3~0&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1L~1>1S~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1M~2>0>1x@1$1@1$0#k0>0@2$a@2$f@2$2@1$0#k0^4@2$2@1$0#k0^1@2$h0@2$2@1$0#k0^1@2$e@2$2@1$0#k0^4@2$2@1$0#k0^3@3$6$7@3$c^7^6^2$8@3$6~2@4$b^6^5@4$9@1$1@1$0#k0@1$1@1$0#k0^4^3^2@3$d^4^3^2").
Proof.
  intros L S a n M WIN. apply functional_extensionality. intros x. unfold mzero, zfill, zmem, zin_rangeb. cbn [fst snd].
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n));
    cbn [andb]; try reflexivity.
  rewrite WIN by lia. reflexivity.
Qed.

Lemma mzero_zfill_S : ltac2:(zQ "h13!me!ip1!hrd!is2!ii7!ipe!ka!ik1!it1!ik9!ku2!lu8!lv1!kt9!jm6!ku8!jmd&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$3~0&>0@1$1@1$0#k0@1$4@1$1@1$0#8>1L~1>1S~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1M~2>0>1x@1$1@1$0#k0>0@2$a@2$f@2$2@1$0#k0^4@2$2@1$0#k0^1@2$h0@2$2@1$0#k0^1@2$e@2$2@1$0#k0^4@2$2@1$0#k0^3@3$6$7@2$c^2^6$9@3$6~2@4$b^6^5@4$8@1$1@1$0#k0@1$1@1$0#k0^4^3^2@3$d^4^3^2").
Proof.
  intros L S a n M WIN. apply mzero_zfill. intros x Hx. unfold hiddenb. rewrite (WIN x Hx).
  destruct (in_rangesb x L); reflexivity.
Qed.

Lemma lzok_after_madvise : ltac2:(zQ "i13!me!ip1!ipe!ip7!hrd!is2!ku2!ka!kne!lvf!ik1!it1!ik9!mgb!ue!mkd!iq6!ir1!isa!kn4!ml5!kof!ite!iv8!jib!lu8!mq6!lo8!lv1!mr0!jm6!ku8!jmd&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$5~0&@1$3~0>1L~1>1S~1>2Zr~1>3msF$8>2mo$e>4addr@1$1@1$0#k0>1n@1$1@1$0#k0>0@5$f?4segs^7^6^5@2$d^4^3>0>1x@1$1@1$0#k0>0@2$6@2$hf@2$4@1$0#k0^4@2$4@1$0#k0^1@2$i0@2$4@1$0#k0^1@2$he@2$4@1$0#k0^4@2$4@1$0#k0^3>0@3$7$a@3$hb^a^9^2$c@3$7$a@2$hc^3^9$c=3mo'$e@3$h8^5^4^3=4msF'$8@1$h4@2$h5^7@6$h7@2$h0@1$0#k0Z@1$3@2$2@1$1@1$0#k0@1$5@1$1@1$0#8@3$h1~0@4$b@1$1@1$0#k0@1$1@1$0#k0^5^4~2~2@1$3$h6@1$3@2$2@1$1@1$0#k0$h2@2$6@5$f?4segs^b^a^9@2$d^1^2@2$6@3$7$8@3$9^b^a^1@3$ha@3$9^b^a^8@2$h0@1$0#k0Z@4$h9^b^a@4$b@1$1@1$0#k0@1$1@1$0#k0^6^5@1$h3@3$9^b^a^8@4$hd^b^a^8^1").
Proof.
  intros L S Zr msF mo addr n Hok HZ. cbv zeta.
  destruct Hok as [HL Hinv Hh HZr HSZ HZL HLM]. cbn [cfg_model cfg_ms] in *.
  assert (Emem : ms_mem (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)])) = zfill addr n (ms_mem msF))
    by apply apply_effect_mem_zeros_ret.
  (* [comment removed for export] *)
  assert (Hhid : forall x, hiddenb L S x = true ->
                 ms_mem (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)])) x = ms_mem msF x).
  { intros x Hx. rewrite Emem. unfold zfill, zmem.
    destruct (Z.leb_spec (bv_unsigned addr) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned addr + bv_unsigned n));
      cbn [andb]; try reflexivity.
    symmetry. apply HZr; [exact Hx|]. apply HZ; [lia | exact Hx]. }
  split; [|split].
  - split; cbn [cfg_model cfg_ms].
    + exact HL.
    + destruct Hinv as [Hl Hnd Hincl Hbud]. split.
      * rewrite madvise_dontneed_next_lazy. exact Hl.
      * rewrite madvise_dontneed_next_materialized. apply NoDup_filter. exact Hnd.
      * rewrite madvise_dontneed_next_materialized. intros p Hp. apply filter_In in Hp. apply Hincl. tauto.
      * rewrite madvise_dontneed_next_eager, madvise_dontneed_next_vmmaps. exact Hbud.
    + rewrite madvise_dontneed_next_halted. exact Hh.
    + intros x Hx Hz. cbn [ms_mem advance_past_svc]. rewrite (Hhid x Hx). apply HZr; assumption.
    + exact HSZ.
    + exact HZL.
    + rewrite madvise_dontneed_next_vmmaps. exact HLM.
  - rewrite (restrict_sysret L S). cbn [eff_ret]. f_equal.
    apply functional_extensionality. intros x.
    unfold mzero. rewrite Emem.
    change (ms_mem (restrict L S msF) x) with (restrict_mem L S (ms_mem msF) x).
    unfold restrict_mem, restrict_mem_by.
    destruct (hiddenb L S x) eqn:Eh; cbn [negb]; [rewrite andb_false_r; reflexivity|]. rewrite andb_true_r.
    unfold zfill, zmem, zin_rangeb. cbn [fst snd].
    destruct ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + bv_unsigned n)); reflexivity.
  - apply hid_frame_sysret. exact Hhid.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem sreach_madvise_dontneed_lazy : ltac2:(zQ "ie2!me!ip1!ka!hrd!ik1!ik9!kne!n5!mgb!is2!ipe!ll9!iq6!ue!kue!lvf!mkd!mv5!jm6!jmd!io0!ioa!ln0!ii7!it1!ku2!mvf!kn4!ng5!nh7!khd!iue!ni1!jg3!jh4!nif!nj8!nk5!jib!lu8!mq6!lo8!lv1!jr2!mr0!ku8&@2$a@1$1@1$0#k0@1$1@1$0#k0&@1$9~0>1L~1>1S~1>2Zr~1>3msF$6>2ms$6>2mo$d>2x8@1$1@1$0#k0>1Q>0$hdP>0@5$h0?4segs^8^7^6@2$8^5^3>0@3$2$6@3$f^9^8^6^5>0@3$2@1$h7@1$1@1$0#k0@1$hc^6@2$h6@1$1@1$0#k0^4>0@3$2$7@2$3@1$0#k0^5+u9=4addr@1$1@1$0#k0@2$b^8N0=3len@1$1@1$0#k0@2$b^9N1=2nZ$7@1$i1@2$3@1$0#k0^1=1n@1$1@1$0#k0@2$c@1$0#k0^1=1h$he@1$hf^b>0@3$2$7@2$h4@2$3@1$0#k0^5$i2Z>0@3$2$7@2$h4@2$3@1$0#k0@2$b^eN2@2$h5+2+i0+4>0@1$ha@3$2@1$1@1$0#k0^6@2$c@1$0#k0Z>0@2$h3@2$h2@2$3@1$0#k0^8^6@2$h5+2+k0>0@3$2$4@3$e@1$i5^5^9^6$5>0@3$2$4@3$i0@1$i3^6^a^7$5>0@3$2$4@3$e@1$i4^7^b^8$5>0>1x@1$1@1$0#k0>0@2$h9@2$id@2$3@1$0#k0^d@2$3@1$0#k0^1@2$h3@2$3@1$0#k0^1@2$h2@2$3@1$0#k0^d^b>0@3$2$4@3$i9^ha^h9^2$5@3$2$4@2$ia^3^h9$5>0>4msF'$6=3mo'$d@3$i6^h5^e^b>0@5$h0?4segs^hb^ha^h9@2$8^2^1>0@3$2$6@3$f^hc^hb^3@3$i8^h8@2$c@1$0#k0Z@4$i7^hc^hb@4$h8@1$1@1$0#k0@1$1@1$0#k0^h0^d@1$hb^h8>0@4$ic^hd^hc^ha^4>0@2$ib^h9^4@4$h1?4segs?2SC^h8@2$8^6^5@4$h1?4segs?2SC^h3@2$8^h7^h5").
Proof.
  intros L S Zr msF ms mo x8 Q Hok Hr Hsvc Hno. cbv zeta.
  intros Hal Hadv Hlen Hnw Hrf Hmc Hna HZ Hk.
  subst ms. rewrite restrict_svc in Hsvc. rewrite !ms_gpr_restrict in *.
  set (addr := ms_gpr msF 0) in *.
  set (nZ := page_round_up_Z (bv_unsigned (ms_gpr msF 1))) in *.
  set (n := Z_to_bv 64 nZ) in *.
  ndestruct (page_round_up_n_facts (ms_gpr msF 1) Hlen
              ltac:(pose proof (word_unsigned_range addr); fold nZ; unfold two_pow_64; lia)) as (HnZpos & HnZal & Hun).
  fold nZ in HnZpos, HnZal, Hun. fold n in Hun.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs msF x8)) = 233) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite <- Hun in HZ.
  ndestruct (lzok_after_madvise L S Zr msF mo addr n Hok HZ) as (Hok' & Hvis & Hhs).
  assert (Hsp : forall o, syscall_spec (sys_input segs msF x8) mo o <->
                          o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (madvise_dontneed_next mo addr n) []).
  { intros o. rewrite (syscall_spec_233 _ mo o Hno').
    rewrite in_arg0_sys_input_m, in_arg1_sys_input', in_arg2_sys_input'.
    apply (madvise_dontneed_outcome addr (ms_gpr msF 1) (int32 (ms_gpr msF 2)) _ mo o Hal
             (madvise_dontneed_b_int32 _ Hadv) (w_is0_false _ Hlen)).
    - fold nZ. unfold two_pow_64. exact Hnw.
    - fold nZ. fold n. unfold madvise_dontneed_ok. rewrite Hrf, Hmc, Hna. reflexivity. }
  assert (Hnode : node_ok segs (mkCfg msF mo) unit (fun _ => [])
                    (fun _ => mkCfg (advance_past_svc (apply_effect msF (mkEffect (Z_to_bv 64 0) [] [(addr, n)])))
                                    (madvise_dontneed_next mo addr n))).
  { apply (node_family_noacc segs msF mo x8 unit (fun _ => mkEffect (Z_to_bv 64 0) [] [(addr, n)])
             (fun _ => madvise_dontneed_next mo addr n) (fun _ => []) _ (lzok_halted Hok) Hsvc Hsp).
    - intros []. reflexivity.
    - intros []. apply not_spurious_none. rewrite Hno'. exact injected_arm_none_233.
    - intros o Ho. exists tt. exact Ho.
    - intros []. exact (lzok_halted Hok').
    - intros []. reflexivity. }
  apply (sreach_node segs _ unit _ tt _ Hnode). intros [].
  apply (Hk _ Hok' Hvis Hhs). apply madvise_dontneed_next_sbm.
Qed.

Local Close Scope Z_scope.
End WithSegs.
(* [comment removed for export] *)
