(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN08 YN05 UH04.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c YP07 YP03.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH06 YO04 YO2f YO29
UO0x UO0i UO28
UO19
YL01 YL0e UL0o UL0f YO00 UO3i.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00 UI1i
UI20 UI2r UI2m UI2g UI32 UI1q UI1y UI1f UI2p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI08 YI0c UI3d
UI3h UI3i UI3b
UI4v UI4x
UI10 UI3e UI3f
UI3g UI3n UI3c
UO12 UI4q.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Section a.
Context {rc : YN05.RunCeil}.
Let AMH1 : forall fx : YK11.FPState, alloc_meta_hyp (fx:=fx) ubs2_msyms := fun fx => ubs2_alloc_meta (fx:=fx).
Let ASH1 : forall fx : YK11.FPState, alloc_slot_hyp (fx:=fx) ubs2_msyms := fun fx => ubs2_alloc_slot (fx:=fx).
Let MSH1 : forall fx : YK11.FPState, malloc_small_hyp (fx:=fx) ubs2_msyms := fun fx => ubs2_malloc_small (fx:=fx) (ASH1 fx).
Let NTF1 : forall fx : YK11.FPState, ntfree_hyp (fx:=fx) ubs2_msyms := fun fx => ubs2_ntfree (fx:=fx).
Let API1 : AllocAPI ubs2_msyms := ubs2_API AMH1 MSH1 NTF1.
Let IMG1 : img_laws ubs2_msyms (aa_MR API1) := MRx_img_laws ubs2_msyms ubs2_syms_ok.
Let RAWADD1 : forall fx : YK11.FPState, UI2r.rawadd_spec (fx:=fx) API1 :=
fun fx => ubs2_cgif_raw_addframe (fx:=fx) API1 IMG1 (ubs2_lzw (fx:=fx) API1 IMG1).
Let DIFF1 : forall fx : YK11.FPState, UI1x.diff_spec (fx:=fx) API1 :=
fun fx => ubs2_diff (fx:=fx) API1 IMG1 (RAWADD1 fx).
Let FLUSH1 : forall fx : YK11.FPState, UI20.flush_spec (fx:=fx) API1 :=
fun fx => ubs2_flushFrame (fx:=fx) API1 IMG1 (RAWADD1 fx) (DIFF1 fx).
Let CLOSE1 : forall fx : YK11.FPState, UI1i.close_spec (fx:=fx) API1 :=
fun fx => ubs2_close_spec (fx:=fx) API1 IMG1 (FLUSH1 fx).
Let NEWGIF1 : forall fx : YK11.FPState, UI1i.newgif_spec (fx:=fx) API1 :=
fun fx => ubs2_newgif_spec (fx:=fx) API1 IMG1.
Let RNEWGIF1 : forall fx : YK11.FPState, UI3d.rgb_newgif_spec (fx:=fx) API1 :=
fun fx => ubs2_rgb_newgif (fx:=fx) API1 IMG1 (NEWGIF1 fx).
Let RCLOSE1 : forall fx : YK11.FPState, UI3d.rgb_close_spec (fx:=fx) API1 :=
fun fx => ubs2_rgb_close (fx:=fx) API1 IMG1 (CLOSE1 fx).
Let ADDFG1 : forall fx : YK11.FPState, UI11.addframe_specG (fx:=fx) API1 :=
fun fx => ubs2_cgif_addframeG (fx:=fx) API1 IMG1 (FLUSH1 fx).
Let FCHT1 : forall fx : YK11.FPState, UI3d.free_cht_spec (fx:=fx) API1 := fun fx => ubs2_free_cht (fx:=fx) API1 IMG1.
Let FTREE1 : forall fx : YK11.FPState, UI3h.free_tree_spec (fx:=fx) API1 := fun fx => ubs2_free_tree (fx:=fx) API1 IMG1.
Let GETPAL1 : forall fx : YK11.FPState, UI3h.getpal_spec (fx:=fx) API1 := fun fx => ubs2_getpal (fx:=fx) API1 IMG1.
Let NTN1 : forall fx : YK11.FPState, UI3h.ntn_spec (fx:=fx) API1 := fun fx => ubs2_ntn (fx:=fx) API1 IMG1.
Let COLH1 : forall fx : YK11.FPState, UI3h.col_hash_spec (fx:=fx) API1 := fun fx => ubs2_col_hash (fx:=fx) API1 IMG1.
Let REALLOC1 : forall fx : YK11.FPState, realloc_realizes (fx:=fx) ubs2_msyms (aa_MR API1) := fun fx => ubs2_realloc (fx:=fx).
Let RADDF1 : forall fx : YK11.FPState, UI3h.rgb_addframe_spec (fx:=fx) API1 :=
fun fx => ubs2_rgb_addframe (fx:=fx) API1 IMG1 NTN1 GETPAL1 FCHT1 FTREE1 ADDFG1 COLH1 (REALLOC1 fx).
Let RA1 : (0 <= UL0o.RA_LIB < 2 ^ 64)%Z := ltac:(vm_compute; split; [intros H; discriminate H | reflexivity]).
Let RA1e : (UL0o.RA_LIB mod 2 = 0)%Z := ltac:(vm_compute; reflexivity).
Let LIB1 : lib_contract_all ubs2_msyms API1 UL0o.LIBPC UL0o.RA_LIB UL0o.EMPTY LIB_STACK_RGB :=
ubs2_rgb_LIB API1 IMG1 RNEWGIF1 RADDF1 RCLOSE1 UL0o.RA_LIB UL0o.EMPTY RA1 RA1e.
Lemma ubs2_realizes_rc : forall sp brk mbase rnd lim inp,
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
Theorem ubs2_realizes : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk ubs2segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
realizes ubs2segs (init_config ubs2segs Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase rnd lim inp) (SPEC inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim.
exact (@ubs2_realizes_rc (YN05.RunCeilOf (bv_unsigned sp) (valid_sp_window36 sp Hsp))
sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim (YN05.ceil_of_top_run _)).
Qed.
