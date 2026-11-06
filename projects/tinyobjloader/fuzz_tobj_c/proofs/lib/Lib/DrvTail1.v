(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "mul"; "pow"; "sub"; "modulo"; "to_nat"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "length"; "nat"; "app"; "Some"; "cons"; "list"; "nil"; "option"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvTail1.Tail1"; "tail1"; "L3"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "lt"; "le"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitStrs"; "strs_tail"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_mem"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "in_hwcap"; "in_uid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "rand_bytes"; "region"; "str_off"; "tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "Jinit"; "ms0"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState InitStrs InitArg1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Tail1.
Variable segs : list Segment.
Variable pc0 : N.
Variable ph : PhdrInfo.
Variable sp : word.
Variable draw : EntryDraw.
Variable inp : ProcInput.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hinp : valid_input_either inp.
Let argv := in_argv inp.
Let envp := in_envp inp.
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Hypothesis Hargc : length argv = 2%nat.

Lemma Hargc2 : (2 <= length argv)%nat. Proof using Hargc. unfold argv in *. lia. Qed.
Let JI : ltac2:(tb__ "0|0|
S21OFrho;") := ltac2:(tb__ "0|0|
S2bVsegs;Vpc0;Vph;Vsp;Vdraw;Vinp;A6").
Let STR := Z.of_nat (str_off argv envp).
Let RND := Z.of_nat (rand_off argv envp).
Let LEN := Z.of_nat (img_len argv envp).
Let ENVC := Z.of_nat (length envp).
Let A1 : Z := A1 sp inp.

Let N : Z := Z.of_nat (length argv1).
Definition L3 : Z := ltac2:(tb__ "0|0|
S6VLEN;S0S0VSTR;S2ScS9Q8A1Vargv0;A2A1A2Z1A2A2").

Definition tail1 : list byte := ltac2:(tb__ "0|1|
S1cS9Q8A1M0S1dScG0Vargv0;A2U1A2S23Vdraw;Vinp;A2A3").

Lemma A1_eq : ltac2:(tb__ "0|0|
S14S20VA1;S0S0S0SbQ40Vsp;A2VSTR;A2S2ScS9Q8A1Vargv0;A2A1A2Z1A2A3").
Proof using argv envp. reflexivity. Qed.

Lemma NU : ltac2:(tb__ "0|9|
S15S15S1Z7fff80000000SbQ40Vsp;A2M0A2S1G0Z800000000000A2A2S15S14S20VSTR;S0S0Zb8S4Z8M1Z2M2A2A2S4G1VENVC;A2A2A3S15S15S1Z0M3VENVC;A2S1VENVC;Z100A2A2S15S1S0S0S0S2ScS9Q8A1Vargv0;A2A1M4Z1M5A2VN;A2G5A2S2S2aVargv;A1A1M6A2S15S1S0VSTR;G6A2VRND;A2S15S14S20VLEN;S0VRND;Z10M7A2A3S15S3VLEN;S5G2Z16A2A2S15S1VN;Z1ffffM8A2S15S1G4G8A2S14S20S7G0G7A2G3A3A2A2A2A2A2A2A2A2A2").
Proof using A1 Hargc Hinp Hsp argv1.
  pose proof (NUMS1 sp inp Hsp Hinp Hargc2) as N1. pose proof (InitStrs.NUMS sp inp Hsp Hinp) as N2.
  assert (E : Z.of_nat (length (in_argv inp)) = 2) by (unfold argv in Hargc; rewrite Hargc; reflexivity).
  unfold STR, RND, LEN, ENVC, N in *. unfold argv0, argv1 in *. unfold argv, envp in *. rewrite E in N1. lia.
Qed.

Lemma length_tail1 : Z.of_nat (length tail1) = L3.
Proof using A1 Hargc Hinp Hsp.
  unfold tail1. rewrite length_skipn. pose proof (length_tail draw inp) as LT. pose proof NU.
  unfold L3, LEN, STR, argv0, argv, envp in *. lia.
Qed.

Lemma L3_ge : ltac2:(tb__ "0|0|
S15S1S0VN;Z11A2S19A2S3S19S5Z2Z16A2A2A2").
Proof using A1 ENVC Hargc Hinp Hsp LEN RND STR argv0 argv1. pose proof NU. unfold L3. subst LEN STR. lia. Qed.

Lemma tail1_nth : ltac2:(tb__ "0|3|
SdS14S9Q8M0A1M1S1aG1R1S18SaG0Z0A2M2A4S1aG1S1dR1S1dScG1Vargv0;A2U1A2A2S23Vdraw;Vinp;A2G2A4A3Fj;").
Proof using A1 Hargc. intros j. unfold tail1. rewrite nth_skipn. f_equal. lia. Qed.

Lemma region_tail1 : ltac2:(tb__ "0|0|
S28Vph;Vsp;Vargv;Venvp;S26Vinp;A1S25Vinp;A1Vdraw;S1dS29Vargv;Venvp;A2S1dScS9Q8A1Vargv0;A2U1A2A2S18A9").
Proof using Hargc Hinp Hsp.
  pose proof (region_tail ph sp draw inp) as R. fold argv envp in R.
  rewrite <- (firstn_skipn (length argv0 + 1) (strs_tail draw inp)) in R.
  apply region_app_r in R. rewrite length_firstn in R.
  pose proof (length_tail draw inp) as LT. pose proof NU. fold argv envp in LT.
  replace (Nat.min (length argv0 + 1) (length (strs_tail draw inp))) with (length argv0 + 1)%nat in R.
  2:{ unfold LEN, STR, argv0 in *. lia. }
  exact R.
Qed.

Lemma tail1_split : ltac2:(tb__ "0|3|
S16S11S9Q8M0A1M1A1M2G2S14G2S18SeG1SeG1Vargv1;S10G1SaG0Z0A2S12G1A1A3A3R1A3A3Lrest;A2").
Proof using Hargc.
  unfold tail1, strs_tail, argv0, argv1, argv. unfold argv in Hargc. clear - Hargc.
  assert (E : exists a0 a1, in_argv inp = [a0; a1]).
  { destruct (in_argv inp) as [|a0 [|a1 [|z l]]]; cbn in Hargc; try lia. exists a0, a1. reflexivity. }
  destruct E as (a0 & a1 & E). rewrite E. cbn [nth].
  rewrite !flatten_strings_cons. cbn [flatten_strings]. eexists.
  rewrite <- !app_assoc. rewrite skipn_app. rewrite skipn_all2 by lia.
  replace (length a0 + 1 - length a0)%nat with 1%nat by lia. cbn [skipn app]. rewrite app_nil_l. reflexivity.
Qed.

Lemma tail1_head : ltac2:(tb__ "0|3|
SdS1fR1ScS9Q8M0A1M1Vargv1;A2A2S14G1S1aG1R2S18SaG0Z0A2M2A4S1aG1R2SeG1Vargv1;S10G1G2S12G1A1A3A3G2A4A3F_;Fj;").
Proof using Hargc.
  intros j Hj. destruct tail1_split as [rest ->]. clear - Hj. apply app_nth1. rewrite length_app. cbn [length]. lia.
Qed.

Lemma tail1_firstn : ltac2:(tb__ "0|1|
S14S11S9Q8A1M0A1S1bG0ScG0Vargv1;A2S18A3Vargv1;A3").
Proof using A1 Hargc Hinp Hsp.
  apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite length_firstn. pose proof length_tail1. pose proof L3_ge. unfold N in *. lia.
  - intros j Hj. rewrite length_firstn in Hj. rewrite nth_firstn.
    destruct (Nat.ltb_spec j (length argv1)); [|lia].
    rewrite tail1_head by lia. apply app_nth1. lia.
Qed.

Lemma tail1_nul : ltac2:(tb__ "0|3|
S14S9Q8M0A1M1S1aG1ScG1Vargv1;A2S18SaG0Z0A2M2A4G2A3").
Proof using Hargc. rewrite tail1_head by (clear; lia). rewrite app_nth2 by (clear; lia). rewrite Nat.sub_diag. reflexivity. Qed.

Lemma argv1_nonul : ltac2:(tb__ "0|3|
SdS1eR1ScS9Q8M0A1M1Vargv1;A2A2S17S14G1S1aG1R2S18SaG0Z0A2M2A4G2A3A1F_;Fj;").
Proof using Hargc Hinp.
  intros j Hj. rewrite tail1_head by (clear - Hj; lia). rewrite app_nth1 by (clear - Hj; lia). intros E.
  apply (InitArg1.argv1_nonul inp Hinp Hargc2). fold argv argv1. rewrite <- E. apply nth_In. exact Hj.
Qed.

Lemma tail1_frame : ltac2:(tb__ "0|2|
S21VJI;R1A1SdS1eR1ScS9Q8M0A1M1S18A2A2S14S13G1A1S22R4SaQ40S0VA1;S2R2A1A2A2A2SfG1S1aG1R2S18SaG0Z0A2A4A2A3F_;Fj;F_;Frho;").
Proof using Hargc Hinp Hsp.
  intros rho HJ j Hj. rewrite (ji_mem _ _ _ _ _ _ _ HJ). rewrite A1_eq.
  replace (bv_unsigned sp + STR + Z.of_nat (length argv0) + 1 + Z.of_nat j)
    with (bv_unsigned sp + (Z.of_nat (str_off argv envp + (length argv0 + 1)) + Z.of_nat j)) by (unfold STR; lia).
  exact (ms0_mem_region segs pc0 ph sp draw inp Hsp Hinp _ tail1 j region_tail1 Hj).
Qed.

Lemma tail1_ms0 : ltac2:(tb__ "0|2|
SdS1eR1ScS9Q8M0A1M1S18A2A2S14S13G1A1S24S2cVsegs;Vpc0;Vph;Vsp;Vdraw;Vinp;A6SaQ40S0VA1;S2R2A1A2A2A2SfG1S1aG1R2S18SaG0Z0A2A4A2A3F_;Fj;").
Proof using Hargc Hinp Hsp.
  intros j Hj. rewrite A1_eq.
  replace (bv_unsigned sp + STR + Z.of_nat (length argv0) + 1 + Z.of_nat j)
    with (bv_unsigned sp + (Z.of_nat (str_off argv envp + (length argv0 + 1)) + Z.of_nat j)) by (unfold STR; lia).
  exact (ms0_mem_region segs pc0 ph sp draw inp Hsp Hinp _ tail1 j region_tail1 Hj).
Qed.

Lemma tail1_rand : ltac2:(tb__ "0|4|
SdS1eR1ScS9Q8M0A1M1S18A2A2S1S0SbQ40Vsp;A2VRND;A2M2S0VA1;S2R2A1A2A2S14G1S1aG1R3S18SaG0Z0A2M3A4S1aG1S8S6S0VA1;S2R3A1A2G2A2A1S27Vdraw;A1G3A4A3F_;F_;Fj;").
Proof using ENVC Hargc Hinp Hsp LEN N.
  intros j Hj Hr. pose proof NU as NU'. pose proof (InitStrs.NUMS sp inp Hsp Hinp) as N2. pose proof length_tail1 as LT1.
  rewrite tail1_nth.
  replace (j + (length argv0 + 1))%nat with (Z.to_nat (RND - STR) + Z.to_nat (A1 + Z.of_nat j - (bv_unsigned sp + RND)))%nat.
  2:{ rewrite A1_eq in Hr |- *. unfold argv0, argv, RND, STR, L3 in *. lia. }
  apply (InitStrs.tail_nth_rand sp draw inp Hsp Hinp). rewrite A1_eq in Hr |- *. unfold RND, STR, L3, LEN in *. lia.
Qed.
End Tail1.
