(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0i.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_rate/lib/U/Reusable/YL0i.v, with its module paths and module names changed; 8 of its 47 lines of code are new or changed and 433 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import AllocSlots.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Definition lib_contract_x_Rc (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z))
(GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (j : nat) (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n pl T (K : lleaf -> TSet),
lib_pre_w B API stk empty L A regs mem md ra p n pl ->
RI pl j T A ->
GI j T mem ->
tb_live L A T ->
(0 < n -> ~ In (p, n) T) ->
G_img segs R mem ->
frm_zero fp_csr ->
(forall (l : lleaf) (c' : config),
(exists (fx' : FPState) L' A' regs' mem' md' T',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_post_x_R B API G (f pl) stk L A regs mem md p n l T T' L' A' regs' mem' md' /\
RI pl (S j) T' A' /\
GI (S j) T' mem') ->
crealizes B c' (K l)) ->
crealizes B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).
End d.
End c.
Definition lib_contract_x_Rc_all {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (pc ra empty stk : Z) : Prop :=
forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_x_Rc fx rc LS B API SH SK RI G R GI f j pc ra empty stk.
