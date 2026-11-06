(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset (asan image), the STATEMENTS of two FINV-stating
   donor files of the driver walk restated over the second allocator instance ARcf (lib/Reusable/YG0ncf.v), which holds
   from the allocator's initial state on (h-pre-b1 with h-mani-a8, 2026-10-28 22:44Z), with cgif's FINV replaced by
   PINV (lib/A/PresetCfnA.v) at the start-up ledger: this unit's copies lib/A/AD2a.v:386-401 (tfib_arm_argv2, the
   argv[1] open arms) and lib/A/AD23.v:269-326 (gr_refused / gr_grow, the read loop's buffer doubling).
   Closed-walk lane CwPinvA; the proofs are in PresetPinvA2aPf.v and PresetPinvA23Pf.v. Rule 24: no function is
   proved here (composition / driver layer of a port).
   Changes from the donor: AR -> ARcf at the ghost set [] (no hidden head is outstanding in the driver);
   `FINV ly (w_H W) (ms_mem ms)` -> `PresetCfnA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0`; the no-refusal premise
   of preset's TFIB_T as the predicate parameter NR (`NR inp` after `valid_fs (in_fs inp)`); the leaf hypotheses at
   their ARcf types (other lanes' predicates); cgif's AR_laws is a8's AR_laws_ok_cf (lib/Reusable/YG0lawscf.v), cited
   by the proof, so it is not a premise. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetPinvAcf.v, with its module paths changed; 61 of its 105 lines of code are new or changed and 48 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset (asan image), the STATEMENTS of two FINV-stating
   donor files of the driver walk restated over the second allocator instance ARcf (lib/Reusable/YG0ncf.v), which holds
   from the allocator's initial state on (a Theorem Labs lane with a Theorem Labs lane, 2026-10-28 22:44Z), with cgif's FINV replaced by
   PINV (lib/A/PresetCfnA.v) at the start-up ledger: this unit's copies lib/A/AD2a.v:386-401 (tfib_arm_argv2, the
   argv[1] open arms) and lib/A/AD23.v:269-326 (gr_refused / gr_grow, the read loop's buffer doubling).
   Closed-walk lane CwPinvA; the proofs are in PresetPinvA2aPf.v and PresetPinvA23Pf.v. Rule 24: no function is
   proved here (composition / driver layer of a port).
   Changes from the donor: AR -> ARcf at the ghost set [] (no hidden head is outstanding in the driver);
   `FINV ly (w_H W) (ms_mem ms)` -> `PresetCfnA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0`; the no-refusal premise
   of preset's TFIB_T as the predicate parameter NR (`NR inp` after `valid_fs (in_fs inp)`); the leaf hypotheses at
   their ARcf types (other lanes' predicates); cgif's AR_laws is a8's AR_laws_ok_cf (lib/Reusable/YG0lawscf.v), cited
   by the proof, so it is not a premise.
   MEMNORM (lane MnPrefix, a Theorem Labs lane, 2026-10-29): `YAkMemnorm.memnorm tfibsegs (ms_mem ms)` of the full overlay is a
   premise of tfib_arm_argv2_cf_A (after PINV; the composition seeds it at main from the start-up invariant) and of
   gr_grow_cf_A, and a premise of gr_grow's continuation (the read loop's invariant, port/mnloop-prefix-leaves.md
   §2.3a). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0n
YM02 YP0m YP09 YP0l YP06 YP08 YP03 YN3q YN3v YI00 YI16 YK04 YA0i YA0n YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n
YG0d YCe5 YL02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AD2j AD2i AD1t AD20
AD1v AD2h AD2f AD1w AD1x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO05 YO09 YO06 YO01 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomKeep YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD21 AD24 AD25 AD26 AD23.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetD1sitesA PresetD1preA PresetD2runA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Other lanes' predicates are cited by import: cannot_open_tfa_cf, malloc_site_tfa_cf, memcpy_site_tfa_cf,
      refused_leaf_tfa_cf (lane CwPreA, lib/A/PresetD1preA.v); drv_minv_cf, free_site_cf (lane CwSites,
      lib/A/PresetD1sitesA.v); file_arm_tfa_cf, dir_arm_tfa_cf (lane CwRunqA, lib/A/PresetD2runA.v); the pristine laws
      and block_not_xs_cf are a Theorem Labs lane's theorems (lib/Reusable/YGcfPristine.v, YGcfXs.v), cited by the proof, so none
      is a premise. gr_grow_cf_A also takes `2 ^ 26 < cf_malloc_max` (the grow's request is at most 2 ^ 26;
      lib/A/CfParamsPreset.v has 2 ^ 29 - 2 ^ 20), as cp is quantified.
      THE ROOM (parent's decision 2026-10-29 04:5xZ; resume brief design change 1): every headroom number is gone. A
      driver state carries NP S, NP the program interface's non-primary room (lib/A/PresetCfnA.v Section Variable
      iface_room_np, lane IfacePort 3f83c075b61f; its body will be a Theorem Labs lane's room_live_cf), quantified here with the
      interface's two laws, cited by name: PresetCfnA.iface_room_np_tail (NP S -> ROOM_cf_k S 2: the grow's malloc and
      free get their call room) and PresetCfnA.iface_room_np_step (NP kept across one malloc_cf and one free_cf from a
      state whose live set is at most three blocks). Both are premises until lib/A/CfRoomLivePreset.v (a Theorem Labs lane) gives
      them bodies. *)

(* ---------------------------------------------------------------------- *)
(* 2. AD2a.v:386-401 (tfib_arm_argv2), over ARcf: the argv[1] open arms. *)
Definition tfib_arm_argv2_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (LS : lib_shape) (ci : CfImg) (cp : CfParams)
(B : asyms) (NR : ProcInput -> Prop),
TfibSyms B ->
cannot_open_tfa_cf B -> file_arm_tfa_cf (LS := LS) B NR -> dir_arm_tfa_cf B ->
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (a0 p : list byte),
in_argv inp = [a0; p] ->
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_fs (in_fs inp) -> NR inp ->
st_ok tfibsegs (YP08.E0 sp (in_argv inp) (in_envp inp) xw xd) (ss_main true) (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp (in_argv inp) (in_envp inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> ARcf tfibsegs B ly init_state [] W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
(* #102 (lane StackDrv): the live real stack above the entry sp at main (the composition gives it from main's entry) *)
YGcallStackUp.astack_up_x tfibsegs ly W (bv_unsigned sp) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
srealizes tfibsegs (mkCfg ms md) (CLOSEDX_args (LS := LS) [a0; p] (in_fs inp)).

(* ---------------------------------------------------------------------- *)
(* 3. AD23.v:269-326 (gr_refused, gr_grow), over ARcf: the read loop at its buffer-full test. Quantifiers: the donor's
      Section Gr and f (AD23.v:105-121, 249-267). Changes beyond the header's: the event bound `st_nev S + 2 <= EV_MAX`
      and its continuation `st_nev S' = st_nev S + 2` are replaced by the non-primary room NP S and NP S' (section 1:
      iface_room_np_tail gives the malloc and the free their room, iface_room_np_step hands NP across both calls);
      drv_minv -> drv_minv_cf (lane CwSites), kept across the malloc and the free by a8's pristine laws
      (YGcfPristine.v); the errbuf slot `xs_placed_cf` is carried (00:29Z ruling).
      The refused arm makes no allocator call and takes no room. *)
Definition gr_refused_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms),
TfibSyms B -> refused_leaf_tfa_cf B ->
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte),
valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) ->
forall (E3 : YP0m.env) (W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate)
(pth : list byte) (pb : sptr) (buf cap : Z),
AD25.eagree sp inp xw xd a0 p E3 -> st_ok tfibsegs E3 S_G (restrict (w_H W) ms) -> AD23.gvals E3 buf cap ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md -> AI tfibsegs (w_H W) (w_A W) md -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = buf ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
m_fds md = APSG.fds3 (FdFile pth (Z_to_bv 64 cap)) -> m_fs md = in_fs inp ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
cap = 2 ^ 26 -> srealizes tfibsegs (mkCfg ms md) (diag msg_refused (in_fs inp)).

Definition gr_grow_cf_A : Prop :=
forall (fx : YK11.FPState) (rc : YM05.RunCeil) (ci : CfImg) (cp : CfParams) (B : asyms) (NP : astate -> Prop),
TfibSyms B -> PCA.iface_room_np_tail (cp := cp) NP -> PCA.iface_room_np_step (cp := cp) NP ->
2 ^ 26 < cf_malloc_max ->
malloc_site_tfa_cf B NP -> memcpy_site_tfa_cf B -> free_site_cf B NP ->
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte),
valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) ->
forall (E3 : YP0m.env) (W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate)
(pth data : list byte) (pb : sptr) (buf cap : Z),
AD25.eagree sp inp xw xd a0 p E3 -> st_ok tfibsegs E3 S_G (restrict (w_H W) ms) -> AD23.gvals E3 buf cap ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md -> AI tfibsegs (w_H W) (w_A W) md -> top_ok (bv_unsigned sp) ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = buf -> NP S -> xs_placed_cf ly S ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
m_fds md = APSG.fds3 (FdFile pth (Z_to_bv 64 cap)) -> m_fs md = in_fs inp ->
PCA.PINV (aview tfibsegs (w_H W) (ms_mem ms)) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms) ->
(* #102 (lane StackDrv): the live real stack above the entry sp, and in the continuation below *)
YGcallStackUp.astack_up_x tfibsegs ly W (bv_unsigned sp) (ms_mem ms) ->
forall (K : TSet),
cap < 2 ^ 26 -> (exists e, 0 <= e /\ cap = 2 ^ e) -> cap mod 65536 = 0 -> pb <> PNull ->
blk (w_H W) (ms_mem ms) buf cap data -> drv_minv_cf B S cap (dlen data) -> cap <= dlen data ->
(forall (W' : world tfibsegs) ms' md' ly' S' (pb' : sptr),
let ER' := E_RD (YP08.E0 sp [a0; p] (in_envp inp) xw xd) (ms_regs ms') in
st_ok tfibsegs ER' S_RD (restrict (w_H W') ms') ->
bv_unsigned (ew ER' A_BUF) = sptr_addr B ly' pb' -> bv_unsigned (ew ER' A_LEN) = cap -> bv_unsigned (ew ER' A_CAP) = 2 * cap ->
ARcf tfibsegs B ly' S' [] W' (ms_mem ms') md' -> AI tfibsegs (w_H W') (w_A W') md' -> top_ok (bv_unsigned sp) ly' ->
blocks S' = [(pb', 2 * cap)] -> pb' <> PNull -> NP S' -> xs_placed_cf ly' S' -> drv_minv_cf B S' (2 * cap) (dlen data) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W') (ms_mem ms')) (runs_main_tfa true sp [a0; p] (in_envp inp)) ->
blk (w_H W') (ms_mem ms') (sptr_addr B ly' pb') cap data ->
PCA.PINV (aview tfibsegs (w_H W') (ms_mem ms')) 0 0 ->
YAkMemnorm.memnorm tfibsegs (ms_mem ms') ->
YGcallStackUp.astack_up_x tfibsegs ly' W' (bv_unsigned sp) (ms_mem ms') ->
m_fds md' = APSG.fds3 (FdFile pth (Z_to_bv 64 cap)) -> m_fs md' = in_fs inp ->
srealizes tfibsegs (mkCfg ms' md') K) ->
srealizes tfibsegs (mkCfg ms md) K.
