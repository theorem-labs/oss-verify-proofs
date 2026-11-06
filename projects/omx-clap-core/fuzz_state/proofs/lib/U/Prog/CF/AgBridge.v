(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v; 94 of its 156 lines of code are new or changed and 400 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocPackCf.v, with its module paths and module names changed; 148 of its 172 lines of code are new or changed and 132 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/U/Prog/CF/ContractCF.v; 68 of its 104 lines of code are new or changed and 136 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Exec MState Mem Regs6ss RegisterBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract FrameAPI SlotAgree AgreeLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF FrameCF.
Local Open Scope Z_scope.

(* The allocator contracts of the cut-free universe (ContractCF, FrameCF) from the frame's cut-free contracts
   (SlotAgree.v) and the agreement room law. The frame pieces that have not reached this base are Section
   hypotheses with the texts the frame announced (AgreeCap.room_cf_of_limit33 under the budget
   law at 2^34 (zlib_limit); a Theorem Labs lane 17:02Z: realloc_contract_cf, realloc_null_contract_cf); LIMv stands for
   the law's limit. *)
Section Bridge.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.
Variable LIMv : Z.

Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> LIMv <= vm_limit (m_vmmaps md).
Hypothesis ROOM33 : forall md b n, LIMv <= vm_limit (m_vmmaps md) -> room_slots b n ->
  0 <= sb_cap b <= CAP_AG -> sb_bytes b + n <= 2 ^ 33 -> room_cf md b n.

Definition realloc_contract_cfh (pc : Z) : Prop :=
  forall L A regs mem md p k n old b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem -> In (p, k) (user_blocks A) ->
    getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
    (forall i, 0 <= i < k -> mbyte segs mem (ptr_addr L p + i) = nth_error old (Z.to_nat i)) ->
    Z.of_nat (length old) = k ->
    res_ok_slots A b -> room_cf md b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR REALLOC_STACK L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + k) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 res /\ res <> 0 /\ res mod 16 = 0 /\ fresh_block B res n /\
         (exists b1 b2 c1 c2, blocks L A = b1 ++ (ptr_addr L p, k) :: b2 /\ blocks L' A' = c1 ++ (res, n) :: c2 /\
            c1 ++ c2 = b1 ++ b2) /\
         blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (forall q k', In (q, k') (user_blocks A) -> q <> p -> In (q, k') (user_blocks A')) /\
         (forall i, 0 <= i < Z.min k n -> mbyte segs mem' (res + i) = nth_error old (Z.to_nat i)) /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_realloc b k n)).

Definition realloc_null_contract_cfh (pc : Z) : Prop :=
  forall L A regs mem md n b,
    call_pre_k B MR REALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 <> Z_to_bv 64 (ms_malloc B) ->
    res_ok_slots A b -> room_cf md b n ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (malloc_ret B API REALLOC_STACK L A regs mem md n b).

Lemma room_cf_of_ag : forall L A mem md b n, aa_MR API L A mem md -> res_ok_slots A b -> room_ag b n -> room_cf md b n.
Proof.
  intros L A mem md b n HM HR (Hr & Hc & Hb). pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  apply (ROOM33 md b n (LIMLAW L A mem md HM) Hr); [lia | unfold BYTES_AG in Hb; exact Hb].
Qed.

Lemma ag_malloc_contract : malloc_contract_cf B API -> ContractCF.malloc_contract B API.
Proof.
  intros HM L A regs mem md n b Hpre Hro H10 Hres Hroom.
  apply SR_of_SRcf. apply (HM L A regs mem md n b Hpre Hro H10 Hres).
  exact (room_cf_of_ag L A mem md b n (proj1 Hpre) Hres Hroom).
Qed.

Lemma ag_free_contract : free_contract_cf B API -> ContractCF.free_contract B API.
Proof.
  intros HF L A regs mem md p n b Hpre Hro Hin H10 Hres.
  apply SR_of_SRcf. exact (HF L A regs mem md p n b Hpre Hro Hin H10 Hres).
Qed.

Lemma ag_free_null_contract : free_null_contract_cf B -> ContractCF.free_null_contract B.
Proof.
  intros HF regs mem md H1 H2 H3 H4. apply SR_of_SRcf. exact (HF regs mem md H1 H2 H3 H4).
Qed.

Lemma ag_realloc_contract : forall pc, realloc_contract_cfh pc -> ContractCF.realloc_contract B API pc.
Proof.
  intros pc HR L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hk Hres Hroom.
  apply SR_of_SRcf. apply (HR L A regs mem md p k n old b Hpre Hro Hin H10 H11 Hold Hk Hres).
  exact (room_cf_of_ag L A mem md b n (proj1 Hpre) Hres Hroom).
Qed.

Lemma ag_realloc_null_contract : forall pc, realloc_null_contract_cfh pc -> ContractCF.realloc_null_contract B API pc.
Proof.
  intros pc HR L A regs mem md n b Hpre Hro H10 H11 Hra Hres Hroom.
  apply SR_of_SRcf. apply (HR L A regs mem md n b Hpre Hro H10 H11 Hra Hres).
  exact (room_cf_of_ag L A mem md b n (proj1 Hpre) Hres Hroom).
Qed.

Lemma ag_frame_allocator :
  FrameAPI.frame_allocator B API -> ms_calloc B = None ->
  malloc_contract_cf B API -> free_contract_cf B API -> free_null_contract_cf B ->
  (forall pc, ms_realloc B = Some pc -> realloc_contract_cfh pc /\ realloc_null_contract_cfh pc) ->
  FrameCF.frame_allocator B API.
Proof.
  intros (_ & _ & _ & _ & _ & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16) HC MC FC FNC RC.
  split; [exact (ag_malloc_contract MC)|].
  split; [exact (ag_free_contract FC)|].
  split; [exact (ag_free_null_contract FNC)|].
  split; [intros pc Hpc; destruct (RC pc Hpc) as (R1 & R2);
          exact (conj (ag_realloc_contract pc R1) (ag_realloc_null_contract pc R2))|].
  split; [intros pc Hpc; rewrite HC in Hpc; discriminate|].
  exact (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 (conj H15 H16)))))))))).
Qed.

Lemma ag_malloc_contract_r : malloc_contract_cf B API -> ContractCF.malloc_contract_r B API ContractCF.sb_form.
Proof. intros HM. apply (proj2 (malloc_contract_sb B API)). exact (ag_malloc_contract HM). Qed.

Lemma ag_free_contract_r : free_contract_cf B API -> ContractCF.free_contract_r B API ContractCF.sb_form.
Proof. intros HF. apply (proj2 (free_contract_sb B API)). exact (ag_free_contract HF). Qed.

Lemma ag_realloc_contract_r : forall pc, realloc_contract_cfh pc -> ContractCF.realloc_contract_r B API ContractCF.sb_form pc.
Proof. intros pc HR. apply (proj2 (realloc_contract_sb B API pc)). exact (ag_realloc_contract pc HR). Qed.

End Bridge.
