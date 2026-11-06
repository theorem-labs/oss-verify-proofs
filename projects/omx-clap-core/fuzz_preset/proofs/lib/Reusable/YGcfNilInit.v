(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfNilInit.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfNilInit.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf) at the initial state.
   ARcf_nil (YGcfNil.v) at S = init_state (YG00.v:169), with its seven closed premises discharged:
   st_nev init_state = 0 < EV_MAX; mtr_ok init_state (EV_A * EV_MAX) holds numerically
   (ameter init_state = E_BASE + A_BASE = 2 ^ 30 + 2 ^ 32, plus 2 ^ 33 + VM_HEAD <= 2 ^ 39);
   Compl0 init_state (proj1 BigInv_init, YG01.v:415); st_sec_arr init_state = [];
   errb_cap_cf init_state = 0 (st_secs init_state = []); every st_secs entry is live (none exists); the errbuf
   slot's placement (no errbuf: YGcfXs.xs_placed_cf_init).
   The conversion EXPOSES class 1's shadow band (YG0ncf.v section 2b): ARcf_nil_init returns the
   entry world with the interval [cls1_band_lo_cf, cls1_band_hi_cf) allowed and visible
   (cls1_band_expose_cf, by cgif's wallow / allow_expose, YG0b.v:418-447), where ARcf holds. The
   budget arithmetic is cls1_band_fits_init_cf: the band's 469,766,144 bytes fit in the event
   credit EV_A * EV_MAX = 2 ^ 33 that A_BASE_CF carries and init_state has not spent; the room
   for the map is the room of record's init form (YGcfRoomCf.room_init_band_cf).
   No cgif file is edited. No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfNil YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0b YGcfRoomCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma mtr_ok_init : mtr_ok init_state (EV_A * EV_MAX).
Proof.
unfold mtr_ok, ameter, abudget.
replace (prim_committed init_state) with 0 by reflexivity.
replace (sec_live_bytes init_state) with 0 by reflexivity.
replace (sec_hulls init_state) with 0 by reflexivity.
replace (st_sec_reserved init_state) with 0 by reflexivity.
replace (st_nev init_state) with 0 by reflexivity.
unfold E_BASE, A_BASE, EV_A, EV_MAX, VM_HEAD, ASAN_VM_LMIN. lia.
Qed.

(* The budget arithmetic of the conversion at init: class 1's band, cls1_band_bytes_cf =
   469,766,144 bytes, fits in the event credit EV_A * EV_MAX = 2 ^ 33 that init_state has not
   spent (st_nev init_state = 0). *)
Lemma cls1_band_fits_init_cf : EV_A * st_nev init_state + cls1_band_bytes_cf <= EV_A * EV_MAX.
Proof.
replace (st_nev init_state) with 0 by reflexivity. rewrite cls1_band_bytes_cf_val. unfold EV_A, EV_MAX. lia.
Qed.

(* Exposing class 1's shadow band: cgif's wallow over [cls1_band_lo_cf, cls1_band_hi_cf), given
   the room for its cls1_band_bytes_cf bytes. The new world is wle-above the old one, keeps AI, adds
   the interval to w_A and makes the band visible. *)
Theorem cls1_band_expose_cf : forall segs (W : world segs) md ly,
layout_ok ly -> AI segs (w_H W) (w_A W) md ->
eager_used md + A_bytes (w_A W) + cls1_band_bytes_cf <= vm_limit (m_vmmaps md) ->
exists W', wle W W' /\ AI segs (w_H W') (w_A W') md /\ (forall i, In i (w_A W) -> In i (w_A W')) /\
A_bytes (w_A W') = cls1_band_bytes_cf + A_bytes (w_A W) /\ cls1_band_vis_cf ly (w_H W').
Proof.
intros segs W md ly LO HAI Hb.
destruct (cls1_band_iv_cf ly LO) as (L1 & L2 & L3 & L4 & L5).
assert (H1 : cls1_band_lo_cf ly <= cls1_band_hi_cf ly) by (rewrite cls1_band_bytes_cf_val in L3; lia).
assert (H2 : cls1_band_lo_cf ly mod page_size = 0) by (unfold page_size; exact L1).
assert (H3 : cls1_band_hi_cf ly mod page_size = 0) by (unfold page_size; exact L2).
pose proof (YG0b.allow_expose segs W md (cls1_band_lo_cf ly) (cls1_band_hi_cf ly) H1 H2 H3 HAI
  ltac:(rewrite L3; exact Hb)) as X. cbv zeta in X.
destruct X as (Wle & EA & AB & VIS & _ & AI3).
exists (YG0b.wallow segs W (cls1_band_lo_cf ly) (cls1_band_hi_cf ly) H1 H2 H3).
split; [exact Wle|]. split; [exact AI3|].
split; [intros i Hi; rewrite EA; apply in_cons; exact Hi|]. split; [rewrite AB, L3; reflexivity|].
intros a Ha. apply VIS.
assert (Ra : 0 <= a < 2 ^ 64) by (unfold cls1_band_lo_cf, cls1_band_hi_cf, kPage in L4, L5; lia).
unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
unfold cls1_band_lo_cf, cls1_band_hi_cf, kPage. lia.
Qed.

(* The conversion at init, EXPOSE form: from cgif's AR and AI at the entry world W, a world W'
   with wle W W' and AI where ARcf holds (class 1's band visible). The room for the band is the room
   of record's init form (YGcfRoomCf.room_init_band_cf) at the cf ledger; the last five premises are ALedger_cf's
   alc_lazy_in_maps at md (YGcfLazyMaps.v), the START WITNESS of the two machine cells (start_cells_cf, YG0ncf.v:
   each unit's start-up row, a Theorem Labs lane's condition (5) of field round 2), the START WITNESS of Printf's two image
   cells (start_pf_cf, field round 3) and the unit's image rows ARmcf's amc_cells_owned / amc_pf_owned carry (the
   conversion is a fresh builder). *)
Theorem ARcf_nil_init : forall segs B ly (W : world segs) mem md,
AR segs B ly init_state W mem md -> AI segs (w_H W) (w_A W) md ->
(forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true ->
 YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
start_cells_cf segs B ly init_state W mem -> start_pf_cf segs B ly W mem ->
EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B -> pf_cells_owned_t B ->
exists W', wle W W' /\ AI segs (w_H W') (w_A W') md /\ ARcf segs B ly init_state [] W' mem md.
Proof.
intros segs B ly W mem md A HAI LM CELLS PFC HO HPO.
pose proof A as (M & L & BU & _).
pose proof cls1_band_fits_init_cf as FT.
assert (LC : ALedger_cf segs ly init_state md) by (eapply ALedger_cf_of_ALedger; [exact L | reflexivity | exact LM]).
assert (HA : A_bytes (w_A W) <= abudget_cf init_state).
{ pose proof (proj1 BU) as HB. unfold abudget in HB. unfold abudget_cf.
  replace (st_nev init_state) with 0 in HB by reflexivity.
  replace (sec_hulls init_state) with 0 in HB by reflexivity.
  replace (sec_live_bytes init_state) with 0 in * by reflexivity.
  replace (prim_committed init_state) with 0 by reflexivity.
  replace (st_sec_reserved init_state) with 0 by reflexivity.
  rewrite cf_hull_init.
  replace (errb_cap_cf init_state) with 0 by reflexivity.
  replace (0 / 8) with 0 by reflexivity.
  unfold kPage, A_BASE_CF, A_BASE, EV_A, EV_MAX in *. lia. }
pose proof (YGcfRoomCf.abudget_le_kit_cf (as_universe B) init_state (wf_init_cf (as_universe B))) as HK.
assert (HA' : A_bytes (w_A W) <= YGcfRoomCf.abudget_kit_cf init_state) by lia.
pose proof (YGcfRoomCf.room_init_band_cf segs ly md (A_bytes (w_A W)) LC HA') as ROOM.
destruct (cls1_band_expose_cf segs W md ly (am_layout _ _ _ _ M) HAI ROOM) as (W' & Hs & HAI' & HI & HB & HV).
exists W'. split; [exact Hs|]. split; [exact HAI'|].
apply (ARcf_nil segs B ly init_state W W' mem md A).
- replace (st_nev init_state) with 0 by reflexivity. unfold EV_MAX. lia.
- exact mtr_ok_init.
- exact (proj1 BigInv_init).
- cbn. pose proof cf_sec_live_nonneg. lia.
- reflexivity.
- rewrite cf_hull_init. reflexivity.
- exact (YGcfXs.xs_placed_cf_init ly).
- reflexivity.
- exact FT.
- exact Hs.
- exact HI.
- rewrite HB. lia.
- exact HV.
- exact LM.
- exact (proj1 (CELLS W' Hs)).
- exact (proj2 (CELLS W' Hs)).
- exact (PFC W' Hs).
- exact HO.
- exact HPO.
Qed.

(* ROOM_cf's error-buffer conjunct at init: no control entry, so errb_size_cf is 0, and
   2 * kPage <= 2 ^ 29 <= cf_nob (cf_nob_lo). *)
Lemma ERRB_ROOM_init : ERRB_ROOM init_state.
Proof.
unfold ERRB_ROOM. replace (errb_size_cf init_state) with 0 by reflexivity.
pose proof cf_nob_lo. unfold kPage. lia.
Qed.

(* ROOM_cf's batch-class conjunct at init: nothing is mapped (reg_init). *)
Lemma batch_room_cf_init : batch_room_cf init_state.
Proof.
unfold batch_room_cf. rewrite reg_init. unfold region0. cbn [rg_mapped_user].
unfold kUserMapSize, kFreeArrayOffset. lia.
Qed.

(* ROOM_cf at init: st_sec_arr init_state = [] and 0 < cf_sec_live_max (cf_sec_live_pos). *)
Theorem ROOM_cf_init : ROOM_cf init_state.
Proof.
split; [|split; [exact ERRB_ROOM_init | exact batch_room_cf_init]].
cbn. pose proof cf_sec_live_pos. lia.
Qed.

(* The START-UP ROW of arodata_ok_cf (field round 3; YG0dcf.v, value form): every overlay byte of the hand-off memory
   at a non-owned address of aro_addr_cf (the relocation-read-only range [cf_relro_lo, cf_relro_hi) and, since part 3c,
   the report's read-only reads cf_ro_reads in the non-writable first segment) is the image's byte. It is NOT a premise
   of the conversion (arodata_ok_cf rides beside ARcf); the walks keep it from here (YGcfRodata.v). It holds because
   all five images are ET_EXEC (e_type 2: no runtime relocation writes RELRO), the hand-off memory holds no overlay byte
   there or the loader's bytes ARE the image, and every C_SILENT cell is outside the owned rows (YG0dcf.arodata_ok_cf's
   list). cgif's row (ours, from the image): its start-up band, YB01.v HS_tfib_0_kn and YB03.v
   JS_tfib_band, has no KWord in cgif's RELRO [0x9dc70, 0x9f000); part 3c: a producer must also show no KWord in
   the five cf_ro_reads ranges. reply's row is a Theorem Labs lane's, preset's row the kit owner's. With it, the unit facts errno_relro_t and
   relro_seg_t (YG0ncf.v; cgif: YGcfImgcgif.errno_relro_cgif / relro_seg_cgif). *)
Definition arodata_start_cf (segs : list Segment) (B : asyms) (mem0 : word -> option byte) : Prop :=
YG0dcf.arodata_ok_cf segs B mem0.

End I.
