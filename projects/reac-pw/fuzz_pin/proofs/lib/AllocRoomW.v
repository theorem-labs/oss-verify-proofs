(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 426 of its 462 lines of code are new or changed and 500 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCut.v, with its module paths and module names changed; 70 of its 141 lines of code are new or changed and 391 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/AllocCf.v, with its module paths and module names changed; 55 of its 76 lines of code are new or changed and 120 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import PlaceCap PlaceCapW.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import AllocSI AllocGS AllocCount AllocBound AllocDepth AllocFree AllocMalloc AllocSlots.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import AllocMB AllocPack AllocPackRoom AgreeRoom AgreeLim AllocPackGSF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The slot premise of the cut-free room chain (YO0n_cf.roomcf_malloc, AllocReallocRoom.roomcf_realloc): the
   allocator's slot count against the placement policy's window cap (PlaceCapW.slot_capW), at the largest request
   of a malloc or a realloc of n bytes (the realloc's mremap length is at most one page above malloc's). *)

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma slotW_malloc : forall s n,
  SLOT_UB s + 5 + KRES <= slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area s)) ->
  SLOT_UB s + 5 + KRES <= slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area s)).
Proof.
  intros s n H.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  pose proof (slot_capW_anti (Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area s))
    (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area s)) ltac:(unfold PGSZ; lia)). lia.
Qed.

(* Slot form: a budget of at most LIM_AG = 2^39 bounds the cap (MMAX * (cap + 48) <= 2^39), and the slot count of
   any cap that small fits the window cap at every request of at most MG_REQ bytes. *)
Lemma slots_slotW : forall A b n md, WF A -> res_ok_slots A b -> room_cf md b n -> vm_limit (m_vmmaps md) <= LIM_AG ->
  SLOT_UB A + 5 + KRES <= slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area A)).
Proof.
  intros A b n md HW (HII & HSI & HGS & HNL & HNR & (MB1 & MB2) & Hnb & Hub & Hlv & Hby & Hh)
    [(Hn & Hcap & C1 & C2 & C3 & C4) Hlim] HL.
  pose proof (map_count_bound A HW HSI) as T4.
  pose proof (nareas_hand A HII) as NA1.
  destruct (shift_small A (HCAP (sb_cap b)) HII Hh C4) as [SH1 SH2].
  pose proof HII as (_ & Hsh & _ & _ & Hrt & _).
  assert (HD : hand A / METAS_PER_AREA <= HCAP (sb_cap b) / METAS_PER_AREA).
  { apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact Hh]. }
  assert (BK : brk_bytes A / PGSZ <= nareas A + 1).
  { apply Z.div_le_upper_bound; [unfold PGSZ; lia|]. unfold PGSZ in *. lia. }
  pose proof (page_round_ge (n + IB + UNIT)) as PR.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (AR : area A <= AREA_BOUND (sb_cap b)) by (unfold area, AREA_BOUND, P2; unfold PGSZ in *; lia).
  assert (SU : SLOT_UB A <= SLOTS_BOUND (sb_cap b)) by (unfold SLOT_UB, SLOTS_BOUND, NA; lia).
  assert (D0 : 0 <= HCAP (sb_cap b) / METAS_PER_AREA) by (apply Z.div_pos; unfold HCAP, METAS_PER_AREA; lia).
  assert (Hc : sb_cap b <= 65232).
  { rewrite LIM_AG_eq in HL. unfold LIVE_BOUND, AREA_BOUND, NA, P2, NONHEAP_CF in Hlim.
    unfold MMAX, PGSZ in *. lia. }
  assert (D1 : HCAP (sb_cap b) / METAS_PER_AREA <= 8396).
  { change 8396 with (HCAP 65232 / METAS_PER_AREA). apply Z.div_le_mono; [unfold METAS_PER_AREA; lia|].
    unfold HCAP. lia. }
  assert (W0 : slot_capW MG_REQ = 97614) by (vm_compute; reflexivity).
  assert (RQ : Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area A) <= MG_REQ).
  { unfold RQ_BOUND in C3. lia. }
  pose proof (slot_capW_anti (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area A)) MG_REQ
    ltac:(lia)) as SC.
  unfold SLOTS_BOUND, NA in SU. unfold KRES. lia.
Qed.

(* Pack form: the instance's cap fact rides in room_cf_pack (its third conjunct). *)
Lemma pack_slotW : forall A b n md, WF A -> res_ok_pack A b -> room_cf_pack md b n ->
  SLOT_UB A + 5 + KRES <= slot_capW (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area A)).
Proof.
  intros A b n md HW (HII & HSI & HGS & HNL & HNR & (MB1 & MB2) & HPK & HPC & HUP & Hub & HlL & HlC & Hbd & Hby & Hh)
    [(Hn & Hcap & C1 & C2 & C3 & C4) [_ HW2]].
  pose proof (mapped_pack A (pb_cap b) (pb_live b) HW HSI HPK HPC HUP HlC HlL Hbd) as T4.
  pose proof (nareas_hand A HII) as NA1.
  destruct (shift_small A (GALL (pb_cap b)) HII Hh C4) as [SH1 SH2].
  pose proof HII as (_ & Hsh & _ & _ & Hrt & _).
  assert (HD : hand A / METAS_PER_AREA <= GALL (pb_cap b) / METAS_PER_AREA).
  { apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact Hh]. }
  assert (BK : brk_bytes A / PGSZ <= nareas A + 1).
  { apply Z.div_le_upper_bound; [unfold PGSZ; lia|]. unfold PGSZ in *. lia. }
  pose proof (page_round_ge (n + IB + UNIT)) as PR.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (AR : area A <= AREA2 (GALL (pb_cap b))) by (unfold area, AREA2; unfold PGSZ in *; lia).
  assert (SU : SLOT_UB A <= SLOTS2 (GALL (pb_cap b)) (GMAP (pb_cap b))) by (unfold SLOT_UB, SLOTS2, NA2; lia).
  assert (RQ : Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area A) <= RQ2 (GALL (pb_cap b)) n + PGSZ).
  { unfold RQ2. lia. }
  pose proof (slot_capW_anti (Z.max (Z.max MMAX (page_round (n + IB + UNIT) + PGSZ)) (area A))
    (RQ2 (GALL (pb_cap b)) n + PGSZ) ltac:(lia)) as SC.
  lia.
Qed.

End A.
