(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v, with its module paths and module names changed; 305 of its 381 lines of code are new or changed and 386 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/AllocPack3Cf.v, with its module paths and module names changed; 51 of its 101 lines of code are new or changed and 331 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM05 YM02 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04 YO16 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import PlaceCap PlaceCapW YM0b YO09 YI14 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import AllocPack AllocPackGSF AllocPack3 AllocPack3Room
  ContractT Contract SlotAgree AgreeLim AgreeRoom AllocPack3Cf.
Import ListNotations.
Local Open Scope Z_scope.

Definition pack3P (OK : astate -> Prop) (RM : pbound3 -> Z -> Prop) : ResFormT := {|
  rt_R := pbound3; rt_ok := fun A b => res_ok_pack3 A b /\ OK A; rt_room := fun b n => room_pack3 b n /\ RM b n;
  rt_malloc := pb3_malloc; rt_free := pb3_free; rt_realloc := pb3_realloc |}.

Definition RM_ag (b : pbound3) (n : Z) : Prop :=
  LIVE3c (p3_cap b) (p3_mcap b) (p3_bytes b + n) + NONHEAP_CF <= SRC_LIM_MIN /\
  SLOTS2 (GALL3 (p3_cap b) (p3_mcap b)) (GMAP3 (p3_cap b) (p3_mcap b)) + 5 + KRES <=
    slot_capW (RQ2 (GALL3 (p3_cap b) (p3_mcap b)) n + PGSZ).

Definition pack3_ag_formT : ResFormT := pack3P GSF RM_ag.

Lemma room_cf_of_ag : forall md b n, SRC_LIM_MIN <= vm_limit (m_vmmaps md) ->
  rt_room pack3_ag_formT b n -> room_cf_pack3 md b n.
Proof.
  intros md b n Hl (HR & H1 & H2). split; [exact HR|]. split; [lia | exact H2].
Qed.

Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition malloc_contract_rtcf (F : ResFormT) : Prop :=
  forall L A regs mem md n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem -> getr regs 10 = Z_to_bv 64 n ->
    rt_ok F A b -> rt_room F b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
      (malloc_ret_rt B API F ALLOC_STACK L A regs mem md n b).

Definition free_contract_rtcf (F : ResFormT) : Prop :=
  forall L A regs mem md p n b,
    call_pre B MR L A regs mem md -> ro_agree segs mem ->
    In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
    rt_ok F A b ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
         (exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         rt_ok F A' (rt_free F b n p)).

Definition realloc_contract_rtcf (F : ResFormT) (pc : Z) : Prop :=
  forall L A regs mem md p k n old b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
    getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
    (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
    Z.of_nat (length old) = k ->
    rt_ok F A b -> rt_room F b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (realloc_post_rtcf B API L A regs mem md p k n old (fun q A' => rt_ok F A' (rt_realloc F b k n p q))).

Definition realloc_null_contract_rtcf (F : ResFormT) (pc : Z) : Prop :=
  forall L A regs mem md n b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 <> Z_to_bv 64 (ms_malloc B) ->
    rt_ok F A b -> rt_room F b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (malloc_ret_rt B API F REALLOC_STACK L A regs mem md n b).

Hypothesis LIM : limlaw_at SRC_LIM_MIN B API.

Lemma ag_room_cf_pre : forall L A regs mem md b n, call_pre B MR L A regs mem md ->
  rt_room pack3_ag_formT b n -> room_cf_pack3 md b n.
Proof.
  intros L A regs mem md b n (HM & _) HR. exact (room_cf_of_ag md b n (LIM L A mem md HM) HR).
Qed.

Lemma ag_room_cf_pre_k : forall K L A regs mem md b n, call_pre_k B MR K L A regs mem md ->
  rt_room pack3_ag_formT b n -> room_cf_pack3 md b n.
Proof.
  intros K L A regs mem md b n (HM & _) HR. exact (room_cf_of_ag md b n (LIM L A mem md HM) HR).
Qed.

Theorem ag_malloc_contract : pack3_malloc_contract_cf B API -> malloc_contract_rtcf pack3_ag_formT.
Proof.
  intros H L A regs mem md n b Hpre Hro Hn Hok Hroom.
  exact (H L A regs mem md n b Hpre Hro Hn Hok (ag_room_cf_pre L A regs mem md b n Hpre Hroom)).
Qed.

Theorem ag_free_contract : pack3_free_contract_cf B API -> free_contract_rtcf pack3_ag_formT.
Proof.
  intros H L A regs mem md p n b Hpre Hro Hin Hp Hok. exact (H L A regs mem md p n b Hpre Hro Hin Hp Hok).
Qed.

Theorem ag_realloc_contract : forall pc, pack3_realloc_contract_cf B API pc -> realloc_contract_rtcf pack3_ag_formT pc.
Proof.
  intros pc H L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hlen Hok Hroom.
  exact (H L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hlen Hok
    (ag_room_cf_pre_k REALLOC_STACK L A regs mem md b n Hpre Hroom)).
Qed.

Theorem ag_realloc_null_contract : forall pc, pack3_realloc_null_contract_cf B API pc ->
  realloc_null_contract_rtcf pack3_ag_formT pc.
Proof.
  intros pc H L A regs mem md n b Hpre Hro H10 H11 Hra Hok Hroom.
  exact (H L A regs mem md n b Hpre Hro H10 H11 Hra Hok (ag_room_cf_pre_k REALLOC_STACK L A regs mem md b n Hpre Hroom)).
Qed.

End W.
