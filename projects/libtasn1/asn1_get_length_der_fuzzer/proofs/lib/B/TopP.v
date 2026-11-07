(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Trevor Hansen, 2026-11: made from YZ02: libtasn1's harness contract (B.LibP) in place of cgif_rgb_fuzzer's GIF library, theorem names and module names. *)
(* libtasn1's plain build realizes the driver's shape SPEC: cgif_rgb_fuzzer's YZ02 with libtasn1's
   harness contract (OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B.LibP) in place of cgif's GIF library. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK11 YK15 YN08 YN05 YH04.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0c YP07 YP03.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YH06 YO04 YO2f YO29
YO0x YO0i YO28 YO19 YL01 YL0e YL0o YL0f YO00 YO3i.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B Require Import LibP.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Section a.
Context {rc : YN05.RunCeil}.
Let AMH1 : forall fx : YK11.FPState, alloc_meta_hyp (fx:=fx) src2_msyms := fun fx => src2_alloc_meta (fx:=fx).
Let ASH1 : forall fx : YK11.FPState, alloc_slot_hyp (fx:=fx) src2_msyms := fun fx => src2_alloc_slot (fx:=fx).
Let MSH1 : forall fx : YK11.FPState, malloc_small_hyp (fx:=fx) src2_msyms := fun fx => src2_malloc_small (fx:=fx) (ASH1 fx).
Let NTF1 : forall fx : YK11.FPState, ntfree_hyp (fx:=fx) src2_msyms := fun fx => src2_ntfree (fx:=fx).
Let API1 : AllocAPI src2_msyms := src2_API AMH1 MSH1 NTF1.
Let LIB1 : lib_contract_all src2_msyms API1 YL0o.LIBPC YL0o.RA_LIB YL0o.EMPTY LIB_STACK_RGB := tasn1_lib_plain API1.
Lemma tasn1_plain_realizes_rc : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src2segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
realizes src2segs (init_config src2segs Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp) (SPEC inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil.
exact (src2_realizes_spec API1 (MRx_AllocExtra src2_msyms) LIB1 driver_obligations_proved sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil).
Qed.
End a.
Lemma valid_sp_window36 : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; assumption. Qed.
Theorem tasn1_plain_realizes : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src2segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
realizes src2segs (init_config src2segs Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp) (SPEC inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim.
exact (@tasn1_plain_realizes_rc (YN05.RunCeilOf (bv_unsigned sp) (valid_sp_window36 sp Hsp))
sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim (YN05.ceil_of_top_run _)).
Qed.
