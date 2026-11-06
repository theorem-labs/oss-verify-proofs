(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "add"; "of_nat"; "le"; "mul"; "lt"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "length"; "list"; "pair"; "app"; "bool"; "cons"; "nil"; "Some"; "nat"; "option"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitArg1.Arg1"; "A1"; "arg1_cstr"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "cstr_result"; "CstrOk"; "CstrTooLong"; "read_cstr"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "obj_range"; "ranges_disjoint"; "mem_match"; "rm"; "smatch"; "ss_objs"; "sstate"; "valuation"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_read_byte"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "le"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitLayout"; "argv_ptrs"; "region"; "tab"; "str_off"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "word_le8"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "win_bytes_in_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.InitState"; "Jinit"; "ms0"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"; "@Stdlib.Lists.List"; "flat_map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Arg1.
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
Let uid := in_uid inp.
Let hwcap := in_hwcap inp.
Let ARGC := Z.of_nat (length argv).
Let STR := Z.of_nat (str_off argv envp).
Let LEN := Z.of_nat (img_len argv envp).
Let argv0 : list byte := nth 0 argv [].
Let argv1 : list byte := nth 1 argv [].
Let ms0 : ltac2:(tb__ "0|0|
S28") := ltac2:(tb__ "0|0|
S39Vsegs;Vpc0;Vph;Vsp;Vdraw;Vinp;A6").
Let JI : ltac2:(tb__ "0|0|
S27OFrho;") := ltac2:(tb__ "0|0|
S38Vsegs;Vpc0;Vph;Vsp;Vdraw;Vinp;A6").

Hypothesis Hargc : (2 <= length argv)%nat.

Definition A1 : Z := ltac2:(tb__ "0|0|
S0S0S0S8Q40Vsp;A2VSTR;A2S1S9S6Q8A1Vargv0;A2A1A2Z1A2").

Lemma NUMS1 : ltac2:(tb__ "0|8|
S13S13S2Z7fff80000000S8Q40Vsp;A2M0A2S2G0Z800000000000A2A2S13S14S18VSTR;S0S0Zb8S3Z8M1VARGC;A2A2S3G1S1S9SaS6Q8A1M2A1Venvp;A2A1M3A2A2A3S13S13S2Z2M4VARGC;A2S2VARGC;Z400A2A2S13S2G3Z100A2S13S2S0S0S0S1S9G2Vargv0;A2A1Z1M5A2S1S9G2Vargv1;A2A1M6A2G5A2S1S32Vargv;A1A1M7A2S13S2S0VSTR;G7A2VLEN;A2S13S4VLEN;S5G4Z16A2A2S2G6Z1ffffA2A2A2A2A2A2A2A2").
Proof using Hargc Hinp Hsp.
  pose proof (nums sp inp Hsp Hinp) as N. pose proof (LEN_bound inp Hinp) as HL.
  destruct Hinp as ((_ & _ & Hlens & _) & _ & _).
  subst argv0 argv1 ARGC STR LEN argv envp.
  destruct (in_argv inp) as [|a [|b r]] eqn:Ea; [cbn in Hargc; lia | cbn in Hargc; lia |].
  cbn [nth tab length] in *.
  apply Forall_cons_iff in Hlens as [_ Hlens]. apply Forall_cons_iff in Hlens as [Hb _].
  repeat split; try lia.
Qed.

Lemma region_arg1 : ltac2:(tb__ "0|2|
S31Vph;Vsp;Vargv;Venvp;Vuid;Vhwcap;Vdraw;S2aS33Vargv;Venvp;A2S2aS9S6Q8M0A1M1Vargv0;A2U1A2A2ScG1Vargv1;SeG1S7G0Z0A2SfG1A1A3A3A9").
Proof using ARGC Hargc LEN STR.
  pose proof (region_argv_str ph sp argv envp uid hwcap draw 1 ltac:(unfold argc; lia)) as R.
  subst argv0 argv1. destruct argv as [|a r] eqn:Ea; [cbn in Hargc; lia|].
  cbn [firstn tab nth] in R |- *. rewrite Nat.add_0_r in R. exact R.
Qed.

Lemma region_ptrs : ltac2:(tb__ "0|0|
S31Vph;Vsp;Vargv;Venvp;Vuid;Vhwcap;Vdraw;U8S3bS6Q40A1S6Q8A1S34S30Vsp;Vargv;Venvp;A3A4A9").
Proof using inp.
  pose proof (region_hdr ph sp argv envp uid hwcap draw) as R. unfold hdr_bytes in R.
  apply region_app_r in R. apply region_app_l in R. rewrite length_word_le8 in R. exact R.
Qed.

Lemma tab_first1 : ltac2:(tb__ "0|1|
S14S18S1S32S2fSaS6Q8A1M0A1U1Vargv;A3A1A1S0S1S9G0Vargv0;A2A1Z1A2A3").
Proof using Hargc envp.
  subst argv0. destruct argv as [|a r] eqn:Ea; [cbn in Hargc; lia|]. cbn [firstn tab nth]. rewrite Nat.add_0_r. lia.
Qed.

Lemma argv_ptr1 : ltac2:(tb__ "0|2|
S14S6Q40M0A1M1S2eG1U1S30Vsp;Vargv;Venvp;A3S7G0Z0A2A4S7G0S16A2A3").
Proof using Hargc Hinp Hsp.
  pose proof NUMS1 as N. pose proof tab_first1 as T.
  unfold argv_ptrs. rewrite string_addrs_nth by lia.
  unfold A1. apply bv_eq. rewrite !Z_to_bv_unsigned. f_equal.
  unfold str_base. rewrite bv_add_unsigned. unfold nat_to_word. rewrite Z_to_bv_unsigned.
  rewrite T. subst STR.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small (Z.of_nat (str_off _ _))) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Variable rho : valuation.
Hypothesis HJ : JI rho.

Lemma arg1_ptr_frame : ltac2:(tb__ "0|1|
S37Vrho;S8Q40M0Vsp;A2Z10U8S7G0S16A2A5").
Proof using HJ Hargc Hinp Hsp.
  pose proof NUMS1 as N.
  intros j Hj. rewrite (ji_mem _ _ _ _ _ _ _ HJ).
  replace (bv_unsigned sp + 16 + Z.of_nat j) with (bv_unsigned sp + (Z.of_nat 8 + Z.of_nat (8 * 1 + j))) by lia.
  subst ms0. rewrite (ms0_mem_region segs pc0 ph sp draw inp Hsp Hinp 8 (flat_map word_le8 (argv_ptrs sp argv envp)) (8 * 1 + j) region_ptrs).
  2:{ rewrite length_flat_map_le8. unfold argv_ptrs. rewrite string_addrs_fst_length. lia. }
  f_equal. rewrite nth_flat_map_le8; [| unfold argv_ptrs; rewrite string_addrs_fst_length; lia | exact Hj].
  rewrite argv_ptr1, word_le8_enc. reflexivity.
Qed.

Lemma arg1_bytes_frame : ltac2:(tb__ "0|3|
S11S2bR1S9S6Q8M0A1M1Vargv1;A2A2S14S12G1A1S23Vrho;S7Q40S0S16S1R2A1A2A2A2S10G1S2eG1R2ScG1Vargv1;SeG1S7G0Z0A2M2SfG1A1A3A3G2A4A2A3F_;Fj;").
Proof using HJ Hargc Hinp Hsp.
  pose proof NUMS1 as N.
  intros j Hj. rewrite (ji_mem _ _ _ _ _ _ _ HJ). unfold A1.
  replace (bv_unsigned sp + STR + Z.of_nat (length argv0) + 1 + Z.of_nat j)
    with (bv_unsigned sp + (Z.of_nat (str_off argv envp + (length argv0 + 1)) + Z.of_nat j)) by (subst STR; lia).
  subst ms0. rewrite (ms0_mem_region segs pc0 ph sp draw inp Hsp Hinp _ (argv1 ++ [Z_to_bv 8 0]) j region_arg1).
  2:{ rewrite length_app. cbn [length]. lia. }
  reflexivity.
Qed.

Lemma argv1_nonul : ~ In (Z_to_bv 8 0) argv1.
Proof using Hargc Hinp envp.
  destruct Hinp as ((_ & _ & _ & Hn & _) & _ & _). subst argv1 argv.
  destruct (in_argv inp) as [|a [|b r]] eqn:Ea; [cbn in Hargc; lia | cbn in Hargc; lia |].
  apply Forall_cons_iff in Hn as [_ Hn]. apply Forall_cons_iff in Hn as [Hb _]. exact Hb.
Qed.

Definition arg1_cstr : cstr_result := ltac2:(tb__ "0|0|
SdS19L_;S3aS9S6Q8A1Vargv1;A2U1000A2S1aVargv1;A1S1bXdx2").

Lemma arg1_read_cstr_mm : ltac2:(tb__ "0|0|
SaS1fA1S28S22Vsegs;Vrho;R2R1A4S2dS1fS1fS21S20Vrho;R1A2SbS18S18S16S0S0S16S1S9S6Q8A1Vargv1;A2A1A2Z1A2A4A2Lo;R3A3S14S19S1cS29R3A1S7Q40S16A2A2S17A3F_;F_;Fms;Fobjs;").
Proof using HJ Hargc Hinp Hsp.
  pose proof NUMS1 as N.
  intros objs ms Hmm Hdisj. unfold read_cstr, arg1_cstr. change path_max with 4096%nat.
  apply read_cstr_aux_string; [unfold A1; lia | unfold A1; lia | | apply argv1_nonul].
  intros j Hj.
  destruct (mem_frame_rd segs rho objs ms (Z_to_bv 64 (A1 + Z.of_nat j)) _ Hmm
             ltac:(eapply ranges_disjoint_outside; [exact Hdisj|]; rewrite Z_to_bv_small; [lia|]; rewrite mod64; unfold A1; lia)
             (arg1_bytes_frame j Hj)) as [_ Hrd].
  exact Hrd.
Qed.

Lemma arg1_read_cstr : ltac2:(tb__ "0|1|
S26SaS1eA1M0S28S1dS24Vsegs;Vrho;R4SbG0S35R3S36R2R1A2A4A4S2dS1fS1fS21S20Vrho;R1A2SbS18S18S16S0S0S16S1S9S6Q8A1Vargv1;A2A1A2Z1A2A4A2Lo;S25R5A1A3S14S19S1cS29R4A1S7Q40S16A2A2S17A3F_;F_;Fmd;Fms;Ftr;FS;").
Proof using HJ Hargc Hinp Hsp. intros S tr ms md Hsm. apply arg1_read_cstr_mm. exact (smatch_mm segs rho S tr ms md Hsm). Qed.

Lemma arg1_cstr_cases : ltac2:(tb__ "0|2|
S15S13S2bU1000M0S9S6Q8A1Vargv1;A2M1A2S14S19S17S1bA3A2S13S2cG1G0A2S14S19S17S1aVargv1;A1A3A2A2").
Proof using . unfold arg1_cstr. destruct (Nat.ltb_spec (length argv1) 4096); [right|left]; auto. Qed.

End Arg1.
