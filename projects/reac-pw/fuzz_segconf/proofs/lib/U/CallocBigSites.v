(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_c.v, with its module paths changed; 58 of its 72 lines of code are new or changed and 52 lines of the source are left out. *)
(* reac-pw/fuzz_segconf (UBSan): calloc_contract_big (U/CallocBigC.v) at the three calloc calls of segconf's
   LLVMFuzzerTestOneInput, and the room the calls' meters leave.

   This file proves no program function: it gives, for each consumer call site of the contract, one closed lemma
   showing that the site supplies the contract's premises with the site's literal arguments (the stream rule
   `CHECK A CONTRACT BEFORE PROVERS USE IT`); the cap side condition m * n <= CALLOC_BIG_CAP is discharged inside.
   Nothing here is an Axiom, a Parameter, an admit or an Admitted.

   The sites (UBSan image; each a 4-byte jal ra to calloc 0x172a0):
   - 0x13980: m = calloc(1, 9236) (a1 = 0x2414 by lui + addiw at 0x13974-0x13978, a0 = 1 by addi a0,zero,1 at 0x1397c);
   - 0x13e7c: tab = calloc(cap + 1, 18) (a1 = 0x12 at 0x13e74, a0 = s4 = cap + 1), 0 <= cap < 40;
   - 0x13e8c: mt = calloc(cap + 1, 20) (a1 = 0x14 at 0x13e84, a0 = s4).
   The meters: at a call the slot's meter is sb_hb b0 hb = SB (sb_live b0 + length hb) (sb_bytes b0 + the sum of hb's
   sizes) (sb_cap b0), with b0 = SB 0 0 CAPMAX at the real start (CallocBigSat.W_res) and hb the live harness blocks:
   [c] (c = malloc(16616) at 0x1396c) at 0x13980, [m; c] at 0x13e7c, [tab; m; c] at 0x13e8c. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i YM06_cf YO0d_cf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract AllocSlots AllocRoom SlotAgree CallocBigC.
Import ListNotations.
Local Open Scope Z_scope.

(* The room at the three meters, for every cap the harness allows. *)
Lemma calloc_sites_room : forall cap, 0 <= cap < 40 ->
  room_slots (SB 1 16616 CAPMAX) (1 * 9236) /\
  room_slots (SB 2 (16616 + 9236) CAPMAX) ((cap + 1) * 18) /\
  room_slots (SB 3 (16616 + 9236 + (cap + 1) * 18) CAPMAX) ((cap + 1) * 20).
Proof.
  intros cap Hc.
  split; [|split]; apply room_slots_small; cbn [sb_live sb_bytes sb_cap]; cbv [CAPMAX]; lia.
Qed.

Section Sites.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* 0x13980: m = calloc(1, 9236). *)
Lemma calloc_big_site_m : forall pc, calloc_contract_big B API pc ->
  forall L A regs mem md b,
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 9236 ->
    res_ok_slots A b -> room_slots b (1 * 9236) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => malloc_ret B API CALLOC_STACK L A regs mem md (1 * 9236) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < 1 * 9236 ->
             mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).
Proof.
  intros pc HC L A regs mem md b H1 H2 H10 H11 HR HM.
  exact (HC L A regs mem md 1 9236 b H1 H2 H10 H11 ltac:(lia) ltac:(lia) ltac:(unfold CALLOC_BIG_CAP; lia) HR HM).
Qed.

(* 0x13e7c: tab = calloc(cap + 1, 18), 0 <= cap < 40. *)
Lemma calloc_big_site_tab : forall pc, calloc_contract_big B API pc ->
  forall L A regs mem md b cap,
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 (cap + 1) -> getr regs 11 = Z_to_bv 64 18 -> 0 <= cap < 40 ->
    res_ok_slots A b -> room_slots b ((cap + 1) * 18) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => malloc_ret B API CALLOC_STACK L A regs mem md ((cap + 1) * 18) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < (cap + 1) * 18 ->
             mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).
Proof.
  intros pc HC L A regs mem md b cap H1 H2 H10 H11 Hc HR HM.
  exact (HC L A regs mem md (cap + 1) 18 b H1 H2 H10 H11 ltac:(lia) ltac:(lia)
    ltac:(unfold CALLOC_BIG_CAP; lia) HR HM).
Qed.

(* 0x13e8c: mt = calloc(cap + 1, 20), 0 <= cap < 40. *)
Lemma calloc_big_site_mt : forall pc, calloc_contract_big B API pc ->
  forall L A regs mem md b cap,
    call_pre_k B MR CALLOC_STACK L A regs mem md -> ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 (cap + 1) -> getr regs 11 = Z_to_bv 64 20 -> 0 <= cap < 40 ->
    res_ok_slots A b -> room_slots b ((cap + 1) * 20) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
      (fun c' => malloc_ret B API CALLOC_STACK L A regs mem md ((cap + 1) * 20) b c' /\
         exists ms' md', c' = mkCfg ms' md' /\
           forall i, 0 <= i < (cap + 1) * 20 ->
             mbyte segs (ms_mem ms') (bv_unsigned (getr (ms_regs ms') 10) + i) = Some (Z_to_bv 8 0)).
Proof.
  intros pc HC L A regs mem md b cap H1 H2 H10 H11 Hc HR HM.
  exact (HC L A regs mem md (cap + 1) 20 b H1 H2 H10 H11 ltac:(lia) ltac:(lia)
    ltac:(unfold CALLOC_BIG_CAP; lia) HR HM).
Qed.
End Sites.
