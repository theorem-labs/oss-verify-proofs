(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v; 94 of its 156 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackCf.v, with its module names changed; 154 of its 182 lines of code are new or changed and 128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Prog/CF/SRCF.v, with its module paths and module names changed; 54 of its 70 lines of code are new or changed and 166 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/SlotPack3.v; 61 of its 88 lines of code are new or changed and 43 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import
  YK15 YM06 YO0j YO0m YO03 YO0f YO0g YO0x YK0i YK0o YK0s YK0h YK14 YK1b YK1a YK1i YK0n YP0n YP0m YP02 YN3f
  YO0p YO0l YO0n YO0k YO0o YL01 YL00
  YK11 YM05 YM02 YO0i YO0d YO05 YO06 YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL0g YL0i YL0k YL0s YN03 YN2b YN33
  DriverSlots DriverPack DriverPack3 YL0i_cfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import
  ZTraceSpec ZComplete ZAllocator Contract FrameAPI FrameSlotG SlotKept SlotTopR AllocPack SlotPack FrameSlotP
  SlotAgree AllocPackGSF AllocPack3 SlotPack3 FrameSlotP3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
Import ListNotations.
Open Scope Z_scope.

Definition RI_P3c (CS : list byte -> list Z) (MC : list Z) (pl : list byte) (j : nat) (T : list (Z * Z)) (A : astate)
    : Prop :=
  RI_P3 CS MC pl j T A /\ GSF A.

Section AgreeP3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.

Definition lib_post_cgp3 (cs MC : list Z) (G : list (Z * Z)) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (p n : Z) (b : pbound3) (l : lleaf) (T T' : list (Z * Z))
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  lib_post_p3 B API cs MC G stk L A regs mem md p n b l T T' L' A' regs' mem' md' /\ GSF A'.

Definition lib_contract_cgp3 (CS : list byte -> list Z) (MC : list Z) (G R : list (Z * Z))
    (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (j : nat)
    (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b T (K : lleaf -> TSet),
    lib_pre_w B API stk empty L A regs mem md ra p n pl ->
    res_ok_pack3 A b /\ GSF A ->
    pack3_entry CS MC pl T b ->
    p3_mis b = [] ->
    GI j T mem ->
    tb_live L A T ->
    (0 < n -> ~ In (p, n) T) ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    spZ regs <= TASK_SIZE ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md' T',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_cgp3 (CS pl) MC G stk L A regs mem md p n b l T T' L' A' regs' mem' md' /\
          GI (S j) T' mem') ->
       crealizes B c' (K l)) ->
    crealizes B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Hypothesis TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a).

Lemma lib_contract_x_Rc_of_cgp3 : forall CS MC G R GI j pc ra empty stk, CS_ok CS ->
  lib_contract_cgp3 CS MC G R GI j pc ra empty stk ->
  lib_contract_x_Rc B API (RI_P3c CS MC) G R GI (fun _ => []) j pc ra empty stk.
Proof using TBL.
  intros CS MC G R GI j pc ra empty stk HCS H L A regs mem md p n pl T K Hpre
    [(d & caps & Hd & Hlen & Hcap & Hres) HGs] HGI HTL HpT HR Hfrm HK.
  apply (H L A regs mem md p n pl (PB3 (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps [] MC) T K Hpre (conj Hres HGs)
    (conj (conj Hlen (conj Hcap (ex_intro _ d (conj Hd (conj eq_refl eq_refl))))) eq_refl) eq_refl HGI HTL HpT HR
    (ro_agree_of_pre_w B API TBL stk empty L A regs mem md ra p n pl Hpre)
    (lib_pre_w_sp B API stk empty L A regs mem md ra p n pl Hpre) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & [Hp HGs'] & HGI').
  destruct (lib_post_x_R_of_p3 B API (CS pl) MC G stk L A regs mem md p n _ l T T' L' A' regs' mem' md' Hp)
    as [Hp' Hres'].
  destruct (TDP_chain T T' (pb_of3 (PB3 (pb_live (TDP [] T d)) (pb_bytes (TDP [] T d)) caps [] MC)) d eq_refl eq_refl)
    as [E1 E2].
  rewrite E1, E2 in Hres'. destruct (HCS pl) as [HC1 HC2].
  apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact Hp'|]. split; [|exact HGI'].
  split; [|exact HGs'].
  exists d, (CS pl). split; [exact Hd|]. split; [exact HC1|]. split; [|exact Hres'].
  intros k Hk. split; [exact (HC2 k Hk) | lia].
Qed.

End AgreeP3.

Lemma lib_contract_x_Rc_all_of_cgp3 {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
  {SH : sink_head} {SK : sink_syms}
  (TBL : forall L A mem md, aa_MR API L A mem md -> forall a, static_owned B a -> 0 <= a < 2 ^ 64 ->
    Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> mbyte (ms_segs B) mem a = seg_rom (ms_segs B) (Z_to_bv 64 a))
  (CS : list byte -> list Z) (MC : list Z) (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
  (pc ra empty stk : Z) : CS_ok CS ->
  (forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgp3 fx rc LS B API SH SK CS MC G R GI j pc ra empty stk) ->
  lib_contract_x_Rc_all B API (RI_P3c CS MC) G R GI (fun _ => []) pc ra empty stk.
Proof.
  intros HCS H fx j Hj. exact (lib_contract_x_Rc_of_cgp3 B API TBL CS MC G R GI j pc ra empty stk HCS (H fx j Hj)).
Qed.
