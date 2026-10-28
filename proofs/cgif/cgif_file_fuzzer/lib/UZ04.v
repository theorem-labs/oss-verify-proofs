(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK15 YM07 YM05 YM0b UH00 UH03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06 YO04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH02 YN03 YN2b YN25 UN0x UN0i UN23 UN10 YN00 UN0y YL01 YL0g YL0i UL0s UL0j UN33.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI06 YI16 YI14 YI17 UI5b UI5c YI0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI23 UI5i UI58 UN39 UI5d UI4m UI3q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UN36 UI3v UI2n UI2b UI2j UI1y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require UI1b.
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
Let AMH1 : forall fx : YK11.FPState, alloc_meta_hyp (fx:=fx) ubs0_msyms := fun fx => ubs0_alloc_meta (fx:=fx).
Let ASH1 : forall fx : YK11.FPState, alloc_slot_hyp (fx:=fx) ubs0_msyms := fun fx => ubs0_alloc_slot (fx:=fx).
Let MSH1 : forall fx : YK11.FPState, malloc_small_hyp (fx:=fx) ubs0_msyms := fun fx => ubs0_malloc_small (fx:=fx) (ASH1 fx).
Let NTA1 : forall fx : YK11.FPState, @UN0w.ntA_hyp fx rc ubs0_msyms := fun fx => ubs0_ntA (fx:=fx).
Definition API1 : AllocAPI ubs0_msyms := ubs0_API AMH1 MSH1 NTA1.
Let IMG1 : img_laws ubs0_msyms (aa_MR API1) := MRx_img_laws ubs0_msyms ubs0_syms_ok.
Let MG1 : malloc_realizes_g ubs0_msyms (aa_MR API1) := ubs0_API_malloc_g AMH1 MSH1 NTA1.
Let RFC1 : forall fx : YK11.FPState, @UI23.rfc_specX fx rc API1 := fun fx => @ubs0_read_frameconfig_x fx rc API1 IMG1.
Let AX1 : AllocExtra ubs0_msyms (aa_MR API1) := MRx_AllocExtra ubs0_msyms.
Let FWRITE1 := fun fx : YK11.FPState => @ubs0_fwrite fx rc API1 IMG1 AX1.
Let FCLOSE1 := fun fx : YK11.FPState => @ubs0_fcloseR fx rc API1 IMG1 AX1.
Let RAWADDX1 := fun fx : YK11.FPState => @ubs0_rawadd_specX fx rc API1 IMG1 (FWRITE1 fx).
Let DIFFX1 := fun fx : YK11.FPState => @ubs0_diff fx rc API1 IMG1 (RAWADDX1 fx).
Let FLUSHX1 := fun fx : YK11.FPState => @ubs0_flushFrame_x fx rc API1 IMG1 (RAWADDX1 fx) (DIFFX1 fx).
Let ADDF1 : forall fx : YK11.FPState, @UI23.addframe_specX fx rc API1 := fun fx => @UI1b.ubs0_cgif_addframe_x fx rc API1 IMG1 (FLUSHX1 fx).
Let CLOSE1 : forall fx : YK11.FPState, @UI23.close_specX fx rc API1 := fun fx => @ubs0_close_specX fx rc API1 IMG1 (FWRITE1 fx) (FCLOSE1 fx) (FLUSHX1 fx).
Let RAWNEW1 := fun fx : YK11.FPState => @ubs0_cgif_raw_newgif_x fx rc API1 IMG1 (FWRITE1 fx).
Let MG1x := fun fx : YK11.FPState => @ubs0_API_malloc_g fx rc AMH1 MSH1 NTA1.
Let NEWGIF1 := fun fx : YK11.FPState => @ubs0_newgif_x fx rc API1 IMG1 AX1 (MG1x fx) (RAWNEW1 fx).
Let LIBX1 : @lib_contract_x_all rc ff_lib_shape ubs0_msyms API1 ubs0_sink_head UI5c.ubs0_sink UL0s.LIBPC UL0s.RA_LIB UL0s.EMPTY LIB_STACK
:= ubs0_lib_contract_x_all API1 IMG1 CLOSE1 ADDF1 RFC1 NEWGIF1.
Lemma ubs0_realizesX_rc : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk ubs0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
realizes ubs0segs (init_config ubs0segs Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd lim inp)
(SPECX (LS:=ff_lib_shape) inp).
Proof using.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil.
exact (ubs0_realizes_specX API1 (MRx_AllocExtra ubs0_msyms) LIBX1 driver_obligationsX_proved ff_room_calls sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil).
Qed.
End a.
Lemma valid_sp_window' : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; assumption. Qed.
Theorem ubs0_realizesX : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk ubs0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
realizes ubs0segs (init_config ubs0segs Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd lim inp)
(SPECX (LS:=ff_lib_shape) inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim.
exact (@ubs0_realizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_window' sp Hsp))
sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim (YM05.ceil_of_top_run _)).
Qed.
