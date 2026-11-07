(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Trevor Hansen, 2026-11: made from UZ02: libtasn1's harness contract (B.LibU) in place of cgif_rgb_fuzzer's GIF library, theorem names and module names. *)
(* libtasn1's UBSan build realizes the driver's shape SPEC: cgif_rgb_fuzzer's UZ02 with libtasn1's
   harness contract (OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B.LibU) in place of cgif's GIF library. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK11 YK15 YN08 YN05 UH04.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YP0c YP07 YP03.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import UH06 YO04 YO2f YO29
UO0x UO0i UO28 UO19 YL01 YL0e UL0o UL0f YO00 UO3i.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.B Require Import LibU.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Section a.
Context {rc : YN05.RunCeil}.
Let AMH1 : forall fx : YK11.FPState, alloc_meta_hyp (fx:=fx) ubs2_msyms := fun fx => ubs2_alloc_meta (fx:=fx).
Let ASH1 : forall fx : YK11.FPState, alloc_slot_hyp (fx:=fx) ubs2_msyms := fun fx => ubs2_alloc_slot (fx:=fx).
Let MSH1 : forall fx : YK11.FPState, malloc_small_hyp (fx:=fx) ubs2_msyms := fun fx => ubs2_malloc_small (fx:=fx) (ASH1 fx).
Let NTF1 : forall fx : YK11.FPState, ntfree_hyp (fx:=fx) ubs2_msyms := fun fx => ubs2_ntfree (fx:=fx).
Let API1 : AllocAPI ubs2_msyms := ubs2_API AMH1 MSH1 NTF1.
Let LIB1 : lib_contract_all ubs2_msyms API1 UL0o.LIBPC UL0o.RA_LIB UL0o.EMPTY LIB_STACK_RGB := tasn1_lib_ubsan API1.
Lemma tasn1_ubsan_realizes_rc : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk ubs2segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
YN05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
realizes ubs2segs (init_config ubs2segs Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd lim inp) (SPEC inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil.
exact (ubs2_realizes_spec API1 (MRx_AllocExtra ubs2_msyms) LIB1 driver_obligations_proved sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil).
Qed.
End a.
Lemma valid_sp_window36 : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; assumption. Qed.
Theorem tasn1_ubsan_realizes : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk ubs2segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
realizes ubs2segs (init_config ubs2segs Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd lim inp) (SPEC inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim.
exact (@tasn1_ubsan_realizes_rc (YN05.RunCeilOf (bv_unsigned sp) (valid_sp_window36 sp Hsp))
sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim (YN05.ceil_of_top_run _)).
Qed.
