(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK15 YM07 YM05 YM0b YH00 YH03.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06 YO04.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH02 YN03 YN2b YN25 YN0x YN0i YN23 YN10 YN00 YN0y YL01 YL0g YL0i YL0s YL0j YN33.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI16 YI14 YI17 YI5b YI5c YI0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI23 YI5i YI58 YN39 YI5d YI4m YI3q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN36 YI3v YI2n YI2b YI2j YI1y.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YI1b.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Lemma calls_bound : forall data, (calls data <= 4)%nat.
Proof. intros data. unfold calls. pose proof (Z.mod_pos_bound (cfg_byte data) 4 ltac:(lia)). lia. Qed.
Lemma ff_room_calls : forall data, room_calls (LS:=ff_lib_shape) (payload_len data) (calls data) DRB.
Proof.
intros data. pose proof (calls_bound data) as Hc.
assert (R : forall n k, (k <= 4)%nat -> room_calls (LS:=ff_lib_shape) n k DRB).
{ intros n k Hk.
do 5 (destruct k as [|k];
[cbn [room_calls]; repeat split; try exact I;
unfold lib_room, lib_delta, ff_lib_shape, ff_room, room; repeat split; vm_compute; try discriminate; try (intros H; discriminate H) | ]).
lia. }
apply R. exact Hc.
Qed.
Section a.
Context {rc : YM05.RunCeil}.
Let AMH1 : forall fx : YK11.FPState, alloc_meta_hyp (fx:=fx) src0_msyms := fun fx => src0_alloc_meta (fx:=fx).
Let ASH1 : forall fx : YK11.FPState, alloc_slot_hyp (fx:=fx) src0_msyms := fun fx => src0_alloc_slot (fx:=fx).
Let MSH1 : forall fx : YK11.FPState, malloc_small_hyp (fx:=fx) src0_msyms := fun fx => src0_malloc_small (fx:=fx) (ASH1 fx).
Let NTA1 : forall fx : YK11.FPState, @YN0w.ntA_hyp fx rc src0_msyms := fun fx => src0_ntA (fx:=fx).
Definition API1 : AllocAPI src0_msyms := src0_API AMH1 MSH1 NTA1.
Let IMG1 : img_laws src0_msyms (aa_MR API1) := MRx_img_laws src0_msyms src0_syms_ok.
Let MG1 : malloc_realizes_g src0_msyms (aa_MR API1) := src0_API_malloc_g AMH1 MSH1 NTA1.
Let RFC1 : forall fx : YK11.FPState, @YI23.rfc_specX fx rc API1 := fun fx => @src0_read_frameconfig_x fx rc API1 IMG1.
Let AX1 : AllocExtra src0_msyms (aa_MR API1) := MRx_AllocExtra src0_msyms.
Let FWRITE1 := fun fx : YK11.FPState => @src0_fwrite fx rc API1 IMG1 AX1.
Let FCLOSE1 := fun fx : YK11.FPState => @src0_fcloseR fx rc API1 IMG1 AX1.
Let RAWADDX1 := fun fx : YK11.FPState => @src0_rawadd_specX fx rc API1 IMG1 (FWRITE1 fx).
Let DIFFX1 := fun fx : YK11.FPState => @src0_diff fx rc API1 IMG1 (RAWADDX1 fx).
Let FLUSHX1 := fun fx : YK11.FPState => @src0_flushFrame_x fx rc API1 IMG1 (RAWADDX1 fx) (DIFFX1 fx).
Let ADDF1 : forall fx : YK11.FPState, @YI23.addframe_specX fx rc API1 := fun fx => @YI1b.src0_cgif_addframe_x fx rc API1 IMG1 (FLUSHX1 fx).
Let CLOSE1 : forall fx : YK11.FPState, @YI23.close_specX fx rc API1 := fun fx => @src0_close_specX fx rc API1 IMG1 (FWRITE1 fx) (FCLOSE1 fx) (FLUSHX1 fx).
Let RAWNEW1 := fun fx : YK11.FPState => @src0_cgif_raw_newgif_x fx rc API1 IMG1 (FWRITE1 fx).
Let MG1x := fun fx : YK11.FPState => @src0_API_malloc_g fx rc AMH1 MSH1 NTA1.
Let NEWGIF1 := fun fx : YK11.FPState => @src0_newgif_x fx rc API1 IMG1 AX1 (MG1x fx) (RAWNEW1 fx).
Let LIBX1 : @lib_contract_x_all rc ff_lib_shape src0_msyms API1 src0_sink_head YI5c.src0_sink YL0s.LIBPC YL0s.RA_LIB YL0s.EMPTY LIB_STACK
:= src0_lib_contract_x_all API1 IMG1 CLOSE1 ADDF1 RFC1 NEWGIF1.
Lemma src0_realizesX_rc : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
realizes src0segs (init_config src0segs Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp)
(SPECX (LS:=ff_lib_shape) inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil.
exact (src0_realizes_specX API1 (MRx_AllocExtra src0_msyms) LIBX1 driver_obligationsX_proved ff_room_calls sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil).
Qed.
End a.
Lemma valid_sp_window' : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; assumption. Qed.
Theorem src0_realizesX : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
realizes src0segs (init_config src0segs Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp)
(SPECX (LS:=ff_lib_shape) inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim.
exact (@src0_realizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_window' sp Hsp))
sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim (YM05.ceil_of_top_run _)).
Qed.
