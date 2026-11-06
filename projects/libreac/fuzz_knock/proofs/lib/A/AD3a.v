(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written by a Theorem Labs lane (the prover of piece S1 of fuzz_knock's StackDepot first-use chain, for another Theorem Labs lane): the statement of __sanitizer::StackStore::Store (knock asan 0x6e8f4, 73 insns) for store block 0, on the call of knock's first post-main StackDepotPut that creates the block (through StackStore::Alloc 0x6ea18, piece S2, consumed here as the Section hypothesis alloc_contract: S2's tfib_alloc_spec by name from lib/A/AD3b.v (merged here with S3's AD3c and a Theorem Labs lane's AD3d, which AD3c exports)) and on the later calls that find the block mapped. Cell-level shape frozen by a Theorem Labs lane: no kernel ARm, because Alloc bumps s_total before it calls Create and Store then writes the slot and stored_. The proof (after the statement's sections) walks Store's head to the Alloc call, applies alloc_contract through the refusable node, and walks the tail with internal_memcpy's contract (mc_ok, proved here) to Store's return.
   a Theorem Labs lane approved this statement; amendment 1 brought S3's md_takes (positive size), Create's premises md_takes md (as_store B, 32) and kHighMemBeg <= ly_stk_lo ly (carried in Store's first-use pre) and the Section hypothesis mnr_stk_ge (gone with amendment 8); amendment 2 (S1 only) bounds the slot of a later call (in_app, off the stack, off the store cells); amendment 3 added 0 <= ly_SB ly < 2 ^ 64; amendments 5 and 6 carry S3's ext_but_SB (unmapped-NB filter) and widen Store's first-use frame exclusion to SS + [0, 32) (Create writes mtx_); amendment 7 carries the VM budget premise eager_used md + A_bytes (w_A W) + kStoreBlockSize <= vm_limit (m_vmmaps md); amendment 8 takes S4 by name from a Theorem Labs lane's AD3d (mnr_stk is gone: BIC_STK = 32 + MNR_STK = 136), adds to the first-use pre what S4 asks (ivs_wf, ceil_of_top, mnr_cell_extents taken), replaces w_H W' = w_H W in the first-use post by S4's exposure (X joins w_A, w_H unchanged outside X) and states P6 with S3's placeholder layout_grow_kd ly ly'; amendment 8 note 6 (AD3c.v, carried by AD3b.v) adds S3's exact model after the grant to the first-use post, over Store's entry model; amendment 9 (a Theorem Labs lane, from a Theorem Labs lane's measurement) drops the presence premise for stored_'s 4 bytes, which no caller can supply for an image .bss byte: Store reads and writes stored_ through the reader and the writable segment. The refused arm is excluded by premise (md_room, carried from Create's pre through Alloc's): a real refusal reaches ReportMmapFailureAndDie (0x5e3f4), which ends the run.
   Amendment 11 (a Theorem Labs lane): the first-use arm's last conjunct states X fresh against every map of Store's entry model md (Forall over vm_maps (m_vmmaps md)), from S2's new last conjunct at Alloc's call model md1 = with_vm_backing (m_vm_lazy md) mat md, which keeps m_vmmaps (m_vmmaps_wvb).
   rule 24: proves function StackStore::Store (reuse search: see (internal path)). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YO0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 AF0m AF0x AB1w.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YK0g YK0v YK0x.
(* S2's statement by name (amendment 8): AD3b's tfib_alloc_spec, alloc_post and alloc_exit; S3's definitions from AD3c,
   which Require-Exports a Theorem Labs lane's AD3d (SRr_refusable, md_takes, md_room, mnr_cells, mnr_cell_extents, MNR_STK). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AD3c.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require AD3b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* knock's Store (A image, sha256 61768cf4739b..., read from the packed base c8557374's Asan_seg_001.hex; the AU twin's
   numbers come from AU's own tables):
     0x6e8f4  frame 64 (ra, s0-s5 saved); s3 := a1 (the StackTrace); s4 := size (lw 8(a1)); s5 := tag (lw 12(a1))
     0x6e924  size | tag = 0 -> return 0
     0x6e938  tag >= 256 -> 0x6e9f4 (CHECK failure); size := min(size, 255)
     0x6e94c  sd zero,0(sp) (idx := 0); sd zero,0(a2) (pack cell := 0)
     0x6e968  jal 0x6ea18 (StackStore::Alloc, a0 = this, a1 = size + 1, a2 = sp, a3 = pack; ra = 0x6e96c)
     0x6e96c  result 0 -> return 0
     0x6e97c  sd (tag << 8 | size),0(a0)          the header word of the stored trace
     0x6e988  jal 0x6232c (internal_memcpy, a0 = slot + 8, a1 = trace.trace, a2 = 8 * size)
     0x6e9a0  amoadd.w.rl on this + 0x18 + 16 * (idx >> 20)   stored_ += size + 1
     0x6e9c8  pack cell += (new stored_ = 2^20)
     0x6e9cc  return (u32) (idx + 1)
   Store calls only Alloc and internal_memcpy; MmapNoReserveOrDie is reached only inside Create. With the trace's tag 0,
   1 <= size <= 255 and F + size + 1 <= 2^20 the run stays in block 0, never takes the CHECK or the two "return 0" exits,
   and leaves the pack cell 0 when stored_ + size + 1 < 2^20. *)

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section kd.
(* The layout step, as S3 states it (AD3c.v:162-165, amendment 8): the first Put's growth is the placeholder relation
   layout_grow_kd; AD3j's kd_inst instantiates it with layout_grow (YG0f.v:99). Satisfiable: fun _ _ => True. *)
Variable layout_grow_kd : alayout -> alayout -> Prop.
Variable B : asyms.
(* S2's statement, consumed (S1 does not walk Alloc). Satisfiable: it is S2's tfib_alloc_ok (AD3b.v, Qed) under its own
   premise create_contract, which S3's tfib_blockinfo_create_ok closes under kd_grow_SB and mnr_contract MNR_STK. *)
Hypothesis alloc_contract : AD3b.tfib_alloc_spec layout_grow_kd B.

(* ===== S1: StackStore::Store(this = as_store B, trace = targ, pack = pk) for block 0. ===== *)
(* stored_ of blocks_[0] (BlockInfo {data_ 16; stored_ 24; mtx_ 28}). *)
Definition bi0_stored : Z := 24.

(* Store's exit, for the call with s_total = F and stored_ = std before, the StackTrace at targ = {trace = buf,
   size = n, tag = 0} with the frames tr, and the block-0 data_ cell holding ly_SB ly before.
   Both arms: return to ra with a0 = F + 1 (OffsetToId), callee-saved registers kept, and the EXACT depot cells after
   the call: s_total = F + n + 1, s_block0 = x, stored_ = std + n + 1, the pack cell 0; the slot at x + 8 * F holds the
   header word n (tag 0) and the n frames; presence only grows.
   First use (ly_SB ly = 0): S3's post carried through Alloc: P2-P3 for X = (x, kStoreBlockSize); P4 X present and 0
   outside the slot; exposure as S3 and S4 state it (amendment 8: X joins w_A, w_H unchanged outside X); P5 no I/O, the model takes X and keeps what it took, and the model after the call is exactly S3's (amendment 8 note 6: the
   NORESERVE grant of X on Store's entry model, up to the materialization wrapper; Store's own steps only re-wrap it),
   allocated_ = alloc + 0x800000, the mutex word 0, memory unchanged outside
   Store's band, X, SS + [0, 32) (amendment 6: every store cell is written, each final value stated) and the pack cell; P6 at cell level: ly' = set_ly_SB ly x and
   layout_grow_kd ly ly' (S3's placeholder, amendment 8); X is fresh against every map of Store's entry model (S3's P7
   through Alloc, amendment 11). No kernel ARm: Put's insertion restores it.
   Later calls (ly_SB ly <> 0): x = ly_SB ly, the layout, world and model (but for materialization) are unchanged,
   frame = Store's band, s_total, stored_, the pack cell and the slot. *)
Definition store_exit (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (pk F std alloc : Z) (tr : list Z)
  (x : Z) (ly' : alayout) (W' : world tfibsegs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  let sp := spZ regs in let SS := as_store B in let m' := mrestrict (w_H W') mem' in let n := Z.of_nat (length tr) in
  getr regs' 10 = Z_to_bv 64 (F + 1) /\ regs_preserved regs regs' /\
  val_mem tfibsegs m' (SS + s_total) 8 (F + n + 1) /\ val_mem tfibsegs m' (SS + s_block0) 8 x /\
  val_mem tfibsegs m' (SS + bi0_stored) 4 (std + n + 1) /\ val_mem tfibsegs m' pk 8 0 /\
  val_mem tfibsegs m' (x + 8 * F) 8 n /\
  (forall i, (i < length tr)%nat -> val_mem tfibsegs m' (x + 8 * F + 8 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
  ( (ly_SB ly = 0 /\
     YG0f.page_aligned x /\ in_app x kStoreBlockSize /\
     Forall (zdisjoint (x, kStoreBlockSize)) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) /\
     (forall a, aclient_byte B ly S a -> ~ in_zr a (x, kStoreBlockSize)) /\
     (forall i, 0 <= i < kStoreBlockSize -> apresent (w_H W') mem' (x + i) /\
        (~ (8 * F <= i < 8 * (F + n + 1)) -> aview tfibsegs (w_H W') mem' (x + i) = Some 0)) /\
     w_A W' = (x, x + kStoreBlockSize) :: w_A W /\
     (forall a : word, ~ (x <= bv_unsigned a < x + kStoreBlockSize) -> w_H W' a = w_H W a) /\
     same_io md md' /\
     md_takes md' (x, kStoreBlockSize) /\ (forall e, md_takes md e -> md_takes md' e) /\
     (exists mat, md' = with_vm_backing
         (m_vm_lazy (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md)) mat
         (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md)) /\
     m_vmmaps md' = m_vmmaps (YK0v.mmap_model (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md) /\
     m_vm_lazy md' = (Z_to_bv 64 x, Z_to_bv 64 kStoreBlockSize) :: m_vm_lazy md /\
     eager_used md' = eager_used md /\
     val_mem tfibsegs m' (SS + ss_alloc) 8 ((alloc + kStoreBlockSize) mod 2 ^ 64) /\
     val_mem tfibsegs m' (SS + bi0_mtx) 4 0 /\
     (forall a : word, ~ (sp - (64 + 16 + BIC_STK) <= bv_unsigned a < sp) -> ~ (x <= bv_unsigned a < x + kStoreBlockSize) ->
        ~ (SS <= bv_unsigned a < SS + 32) -> ~ (pk <= bv_unsigned a < pk + 8) -> mem' a = mem a) /\
     ly' = set_ly_SB ly x /\ layout_grow_kd ly ly' /\
     Forall (fun q => zdisjoint (x, kStoreBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_maps (m_vmmaps md)))
  \/
    (ly_SB ly <> 0 /\ x = ly_SB ly /\ ly' = ly /\ W' = W /\
     (exists mat, md' = with_vm_backing (m_vm_lazy md) mat md) /\
     (forall a : word, ~ (sp - (64 + 16 + BIC_STK) <= bv_unsigned a < sp) -> ~ (SS <= bv_unsigned a < SS + 8) ->
        ~ (SS + bi0_stored <= bv_unsigned a < SS + bi0_mtx) -> ~ (pk <= bv_unsigned a < pk + 8) ->
        ~ (x + 8 * F <= bv_unsigned a < x + 8 * (F + n + 1)) -> mem' a = mem a))).

Definition store_post (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (pk F std alloc : Z) (tr : list Z) (W' : world tfibsegs) (c' : config) : Prop :=
  exists x ly' regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
    store_exit W ly S regs mem md pk F std alloc tr x ly' W' regs' mem' md'.

(* PRE (cell level): the arguments (the StackTrace at targ with tag 0 and 1 <= n <= 255 frames at buf); s_total = F and
   stored_ = std with the run staying in block 0 and stored_ below 2^20 (so the pack cell stays 0); stored_ is given
   only as its value over the reader (amendment 9: no kernel law gives apresent for an image .bss byte;
   Store's amoadd.w at SS + 24 loads through the overlay-then-segments read, LPS RiscvSemantics.v:792-811, and stores
   through wview, which the image's writable segment answers when the overlay has no byte, LPS RiscvSemantics.v:528-540 and
   store_ok :582-590, so no presence is needed; the walk seeds the cell with the rw-window writability); the block-0 data_
   cell = ly_SB ly; on first use (ly_SB ly = 0) also Alloc's first-use pre, which Store does not change before the call
   (the mutex word 0, allocated_ = alloc, mnr_cells, room for the grant, the VM budget of amendment 7, the model map
   list well formed (ivs_wf), alloc_ceiling as alloc_top's page floor (ceil_of_top), that the model takes the callee's
   two post-ecall cells (mnr_cell_extents; these three are amendment 8's) and every extent P3 names; they read only
   m_vmmaps / m_vm_lazy and W, which Store's head walk to the Alloc call keeps: it writes only its frame and the pack
   cell); on later calls the slot is
   present, in_app, off the stack extent and off the store cells (amendment 2); the pack cell, targ and buf in the stack
   and off Store's band; Store's band of 64 + 16 + BIC_STK bytes in high memory.
   Discharge at Put's call site (today's at-main kernel facts; Put calls Store with the state it took at its entry):
   - F + n + 1 <= 2 ^ 20 (the run stays in block 0): a Theorem Labs lane's depot_store_one_block (lib/A/AD3i.v:264,
     sha256 a0db88d39624; internal record), from TfibSyms B, Wf (as_universe B) S, In tr (as_universe B) and
     F <= 32 + depot_frames S, with n := length tr.
   - 0 <= ly_SB ly < 2 ^ 64 (amendment 3): 0 while the store block is unmapped (a Theorem Labs lane's encoding); once mapped,
     knock-branch lo_app (YG0f.v:440) gives in_app (ly_SB ly) kStoreBlockSize, so 4096 <= ly_SB ly < ASAN_CEIL.
   - md_takes md (SS, 32), kHighMemBeg <= ly_stk_lo ly, md_takes's 0 < snd e (amendment 1): as cited in AD3c.v's
     header (S3): asyms_areas (YG0f.v:254) / aso_cover (YG0f.v:261) / am_static_img (YG0n.v:406) /
     al_imgcov (YG0n.v:627-628) / al_reserved (YG0n.v:609); lo_top (YG0f.v:443-445).
   - ivs_wf, ceil_of_top and the mnr_cell_extents takes (amendment 8): as cited in AD3c.v's header (S3);
     ly_stk_hi ly <= kHighMemEnd, which amendment 8 adds to Create's pre, was already a premise here.
   - the later-call slot (amendment 2): layout_ok's lo_app (YG0f.v:440: in_app (ly_SB ly) kStoreBlockSize, the SB entry
     of owned_extents), lo_disj (YG0f.v:442: (ly_SB ly, kStoreBlockSize) disjoint from the stack extent and from ly_img
     in static_extents), img_cover (AF0x.v:55: ly_img covers the image, where as_store B = TFIB_STORE lies, so the
     store cells are off SB), lo_SB_al (YG0f.v:436); the slot's presence from depot_mem_ok's range_vis of
     (ASB 0, kStoreBlockSize) (AFl0.v:65-67), SB being off the image. *)
Definition tfib_store_spec : Prop :=
  forall (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (targ buf pk F std alloc : Z) (tr : list Z),
  let H := w_H W in let m := mrestrict H mem in let sp := spZ regs in let SS := as_store B in
  let n := Z.of_nat (length tr) in
  getr regs 10 = Z_to_bv 64 SS -> getr regs 11 = Z_to_bv 64 targ -> getr regs 12 = Z_to_bv 64 pk ->
  YK0s.ret_ok (getr regs 1) ->
  val_mem tfibsegs m targ 8 buf -> val_mem tfibsegs m (targ + 8) 4 n -> val_mem tfibsegs m (targ + 12) 4 0 ->
  1 <= n <= 255 -> (forall i, (i < length tr)%nat -> val_mem tfibsegs m (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
  0 <= F -> F + n + 1 <= 2 ^ 20 -> 0 <= std -> std + n + 1 < 2 ^ 20 ->
  val_mem tfibsegs m (SS + s_total) 8 F -> val_mem tfibsegs m (SS + s_block0) 8 (ly_SB ly) -> 0 <= ly_SB ly < 2 ^ 64 ->
  val_mem tfibsegs m (SS + bi0_stored) 4 std ->
  (ly_SB ly = 0 ->
     val_mem tfibsegs m (SS + bi0_mtx) 4 0 /\ val_mem tfibsegs m (SS + ss_alloc) 8 alloc /\ mnr_cells m /\
     md_room md kStoreBlockSize /\ eager_used md + A_bytes (w_A W) + kStoreBlockSize <= vm_limit (m_vmmaps md) /\
     YK0g.ivs_wf (vm_maps (m_vmmaps md)) /\ YM05.ceil_of_top (alloc_top (m_vmmaps md)) /\
     Forall (md_takes md) mnr_cell_extents /\
     md_takes md (SS, 32) /\
     Forall (md_takes md) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) /\
     (forall a, aclient_byte B ly S a -> md_takes md (a, 1))) ->
  (ly_SB ly <> 0 -> in_app (ly_SB ly) kStoreBlockSize /\ zdisjoint (ly_SB ly, kStoreBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
     zdisjoint (ly_SB ly, kStoreBlockSize) (as_store B, 32) /\
     forall a, ly_SB ly + 8 * F <= a < ly_SB ly + 8 * (F + n + 1) -> apresent H mem a) ->
  (forall k, 0 <= k < 8 -> apresent H mem (pk + k)) ->
  ly_stk_lo ly <= pk -> pk + 8 <= ly_stk_hi ly -> (pk + 8 <= sp - (64 + 16 + BIC_STK) \/ sp <= pk) ->
  ly_stk_lo ly <= targ -> targ + 16 <= ly_stk_hi ly -> (targ + 16 <= sp - (64 + 16 + BIC_STK) \/ sp <= targ) ->
  ly_stk_lo ly <= buf -> buf + 8 * n <= ly_stk_hi ly -> (buf + 8 * n <= sp - (64 + 16 + BIC_STK) \/ sp <= buf) ->
  zdisjoint (pk, 8) (targ, 16) -> zdisjoint (pk, 8) (buf, 8 * n) ->
  sp mod 16 = 0 -> kHighMemBeg <= ly_stk_lo ly -> ly_stk_hi ly <= kHighMemEnd ->
  ly_stk_lo ly <= sp - (64 + 16 + BIC_STK) -> sp <= ly_stk_hi ly ->
  (forall a, sp - (64 + 16 + BIC_STK) <= a < sp -> apresent H mem a) ->
  SRr_refusable W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_StackStore_Store) mem (seg_rom tfibsegs)) md)
    (store_post W ly S regs mem md pk F std alloc tr).

End kd.
End g.

(* ===================== The proof of tfib_store_ok =====================
   The walk framework of AFem (the mapped-case depot proof): the symbolic runner over the fetch table tfibtbl_rtB, st_ok
   seeds built with entry_st_ok_full, run lemmas srr_run_toG / srr_run_shG / srr_branch_with, and SRr_ret_at for the
   return. Parts: head_walk (0x6e8f4 to the Alloc call; the bnez on size | tag and the size clamp), mc_ok (internal_memcpy
   0x6232c: the byte loop by induction, mc_iter), t1_ok (Alloc's return to the memcpy call and back), t2_ok (the stored_
   amoadd.w, the pack cell and the return), tail_all (t1_ok and t2_ok composed), and tfib_store_ok (the head, then
   alloc_contract through SRr_refusable_bind, then tail_all, per arm of alloc_exit). The theorem is stated again in a
   section with the same variables and hypotheses in the same order, so its closed type is the statement's. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop YI08.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 AF0l AF0m AF0x AFl0 AB1q AB1w AB1h AFel AFeq AFl3.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Definition hN : nat := 32. Definition hBUF : nat := 33.
Definition R_FR : YP09.region := YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 [].
Definition R_TG : YP09.region := YP09.mkRegion (Some 11%nat) 0 16 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff hBUF 0)); YP09.mkChunk 8 (CVal 4 (SOff hN 0)); YP09.mkChunk 12 (CVal 4 (SLit 0))].
Definition R_PK : YP09.region := YP09.mkRegion (Some 12%nat) 0 8 0 8 [].
Definition HF0 : facts := mkFacts [(2%nat, mkAF (kHighMemBeg + 64) kHighMemEnd 4); (11%nat, mkAF kHighMemBeg (kHighMemEnd - 16) 0);
  (12%nat, mkAF kHighMemBeg (kHighMemEnd - 8) 0); (hN, mkAF 1 255 0); (hBUF, mkAF 0 (2 ^ 64 - 1) 0)] [] [].
Definition S_H0 : sstate := mkSS 0x6e8f4 (sr_set sr_atoms 10%bv (SLit TFIB_STORE)) [R_FR; R_TG; R_PK] None HF0.
Definition c_nz : acond := mkAC BC_NE (SAlu ALU_OR (SOff hN 0) (SLit 0)) (SLit 0).
Lemma ext_Some : forall E k lo hi wl wh cs,
  extent_of_region E (YP09.mkRegion (Some k) lo hi wl wh cs) = (bv_unsigned (ew E k) + lo, bv_unsigned (ew E k) + hi).
Proof. reflexivity. Qed.
Lemma ext_None : forall E lo hi wl wh cs, extent_of_region E (YP09.mkRegion None lo hi wl wh cs) = (0 + lo, 0 + hi).
Proof. reflexivity. Qed.
Section rg. Context {fx : YK11.FPState}.
Lemma region_ok_ro : forall E (m : word -> option byte) k b lo hi cs,
  bv_unsigned (ew E k) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 -> Forall (YP09.chunk_ok tfibsegs E m b) cs ->
  region_ok tfibsegs E m (YP09.mkRegion (Some k) lo hi 0 0 cs).
Proof.
intros E m k b lo hi cs Hk H1 H2 Hc. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
unfold base_val. rewrite Hk. split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; lia | exact Hc].
Qed.
Lemma atoms_ok_of_Forall : forall E l, Forall (fun nf : nat * afact => afact_ok E (fst nf) (snd nf)) l -> atoms_ok E l.
Proof. intros E l H. induction H as [| [k f] l Hh Ht IH]; cbn; [exact I | split; [exact Hh | exact IH]]. Qed.
Lemma AFo : forall E k X lo hi al, ew E k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E k (mkAF lo hi al).
Proof. intros E k X lo hi al HE HX HBd HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. rewrite unsigned_lit_small by exact HX. repeat split; lia. Qed.
Lemma condZ_lit : forall E (c : branch_cond) n1 k1 z (r : bool),
branch_taken c (sv_denot E (SOff n1 k1)) (sv_denot E (SLit z)) = r ->
0 <= bv_unsigned (ew E n1) + k1 < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
match c with
| BC_EQ => (bv_unsigned (ew E n1) + k1 =? z) = r
| BC_NE => negb (bv_unsigned (ew E n1) + k1 =? z) = r
| BC_LTU => (bv_unsigned (ew E n1) + k1 <? z) = r
| BC_GEU => negb (bv_unsigned (ew E n1) + k1 <? z) = r
| _ => True
end.
Proof.
intros E c n1 k1 z r Hc H1 H2. unfold branch_taken, bv_ltu, bv_eqb in Hc. rewrite denot_SOff in Hc. cbn [sv_denot] in Hc. unfold zcanon, M64 in Hc.
rewrite unsigned_lit_small in Hc by exact H2. rewrite !Z.mod_small in Hc by assumption. destruct c; first [exact Hc | exact I].
Qed.
Lemma condZ : forall E (c : branch_cond) n1 k1 n2 k2 (r : bool),
branch_taken c (sv_denot E (SOff n1 k1)) (sv_denot E (SOff n2 k2)) = r ->
0 <= bv_unsigned (ew E n1) + k1 < 2 ^ 64 -> 0 <= bv_unsigned (ew E n2) + k2 < 2 ^ 64 ->
match c with
| BC_EQ => (bv_unsigned (ew E n1) + k1 =? bv_unsigned (ew E n2) + k2) = r
| BC_NE => negb (bv_unsigned (ew E n1) + k1 =? bv_unsigned (ew E n2) + k2) = r
| BC_LTU => (bv_unsigned (ew E n1) + k1 <? bv_unsigned (ew E n2) + k2) = r
| BC_GEU => negb (bv_unsigned (ew E n1) + k1 <? bv_unsigned (ew E n2) + k2) = r
| _ => True
end.
Proof.
intros E c n1 k1 n2 k2 r Hc H1 H2. unfold branch_taken, bv_ltu, bv_eqb in Hc. rewrite !denot_SOff in Hc. unfold zcanon, M64 in Hc.
rewrite !Z.mod_small in Hc by assumption. destruct c; first [exact Hc | exact I].
Qed.
Lemma denot_of_U : forall E e z, U E e = z -> sv_denot E e = Z_to_bv 64 z.
Proof. intros E e z H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma apresent_wr : forall (H : word -> bool) (m : word -> option byte) a, apresent H m a -> writable_at tfibsegs (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma val_mem1_byte : forall (m : word -> option byte) a (b : byte), mbyte tfibsegs m a = Some b -> val_mem tfibsegs m a 1 (bv_unsigned b).
Proof.
intros m a b Hb k Hk. destruct k as [|k]; [|lia]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hb. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma val_mem1_mbyte : forall (m : word -> option byte) a v, val_mem tfibsegs m a 1 v -> 0 <= v < 256 -> mbyte tfibsegs m a = Some (Z_to_bv 8 v).
Proof.
intros m a v Hv R. pose proof (Hv 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. rewrite H0. f_equal. f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
End rg.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (targ buf pk n : Z).
#[local] Notation H := (w_H W).
#[local] Notation m0 := (mrestrict (w_H W) mem).
#[local] Notation sp := (bv_unsigned (getr regs 2%bv)).
Hypotheses (R10 : getr regs 10%bv = Z_to_bv 64 TFIB_STORE) (R11 : getr regs 11%bv = Z_to_bv 64 targ) (R12 : getr regs 12%bv = Z_to_bv 64 pk).
Hypotheses (Tb : val_mem tfibsegs m0 targ 8 buf) (Tn : val_mem tfibsegs m0 (targ + 8) 4 n) (Tt : val_mem tfibsegs m0 (targ + 12) 4 0).
Hypotheses (Hn : 1 <= n <= 255) (Hbuf : 0 <= buf < 2 ^ 64).
Hypotheses (Hsp16 : sp mod 16 = 0) (Hsplo : kHighMemBeg + 64 <= sp) (Hsphi : sp <= kHighMemEnd)
  (Pfr : forall a, sp - 64 <= a < sp -> apresent H mem a).
Hypotheses (Htg : kHighMemBeg <= targ /\ targ + 16 <= kHighMemEnd) (Htg' : targ + 16 <= sp - 64 \/ sp <= targ).
Hypotheses (Hpk : kHighMemBeg <= pk /\ pk + 8 <= kHighMemEnd) (Hpk' : pk + 8 <= sp - 64 \/ sp <= pk)
  (Ppk : forall k, 0 <= k < 8 -> apresent H mem (pk + k)) (Dpt : zdisjoint (pk, 8) (targ, 16)).
Definition EH : env := Ereg regs [Z_to_bv 64 n; Z_to_bv 64 buf].
Lemma EH2 : ew EH 2 = getr regs 2%bv. Proof. exact (ew_Ereg_nat regs _ 2 2%bv eq_refl). Qed.
Lemma EH11 : ew EH 11 = Z_to_bv 64 targ. Proof. rewrite <- R11. exact (ew_Ereg_nat regs _ 11 11%bv eq_refl). Qed.
Lemma EH12 : ew EH 12 = Z_to_bv 64 pk. Proof. rewrite <- R12. exact (ew_Ereg_nat regs _ 12 12%bv eq_refl). Qed.
Lemma EHN : ew EH hN = Z_to_bv 64 n. Proof. reflexivity. Qed.
Lemma EHB : ew EH hBUF = Z_to_bv 64 buf. Proof. reflexivity. Qed.
Lemma SEED_H : st_ok tfibsegs EH S_H0 (restrict H (mkst regs (Z_to_bv 64 0x6e8f4) mem (seg_rom tfibsegs))).
Proof.
pose proof (u64_range (getr regs 2%bv)) as SR.
assert (U11 : bv_unsigned (ew EH 11) = targ) by (rewrite EH11; apply unsigned_lit_small; zlia).
assert (U12 : bv_unsigned (ew EH 12) = pk) by (rewrite EH12; apply unsigned_lit_small; zlia).
rewrite restrict_mkst_fx. unfold S_H0. apply (entry_st_ok_full tfibsegs).
all: try change (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 buf]) with EH.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact R10].
- vm_compute. reflexivity.
- apply Forall_cons.
  { apply (region_ok_stack tfibsegs EH m0 2 sp (-64)); [rewrite EH2; reflexivity | zlia | lia |].
    intros a Ha. apply apresent_writable; [zlia | apply Pfr; lia]. }
  apply Forall_cons.
  { unfold R_TG. apply (region_ok_ro EH m0 11 targ); [exact U11 | zlia | zlia |].
    apply Forall_cons. { eapply (chunk_ok_val tfibsegs EH m0 targ 0 8 (SOff hBUF 0) buf); [cbn [sv_denot]; rewrite EHB, unsigned_lit_small by lia; f_equal; lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Tb]. }
    apply Forall_cons. { eapply (chunk_ok_val tfibsegs EH m0 targ 8 4 (SOff hN 0) n); [cbn [sv_denot]; rewrite EHN, unsigned_lit_small by lia; f_equal; lia | cbn; lia | cbn; lia | exact Tn]. }
    apply Forall_cons. { eapply (chunk_ok_val tfibsegs EH m0 targ 12 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact Tt]. }
    apply Forall_nil. }
  apply Forall_cons.
  { apply (region_ok_window EH m0 12 pk 0 8 0 8); [exact U12 | zlia | zlia |].
    intros a Ha. replace a with (pk + (a - pk)) by lia. apply apresent_writable; [zlia | apply Ppk; lia]. }
  apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold R_FR, R_TG, R_PK. cbn [map]. rewrite !ext_Some.
  rewrite EH2, U11, U12.
  unfold zdisjoint in Dpt. cbn [fst snd] in Dpt.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [| split; exact I]. unfold HF0. cbn [f_atoms]. apply atoms_ok_of_Forall.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  + apply (AFo EH 2 sp); [rewrite EH2; symmetry; apply Z_to_bv_bv_unsigned | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
  + apply (AFo EH 11 targ _ _ _ EH11); [zlia | lia | apply Z.mod_1_r | lia].
  + apply (AFo EH 12 pk _ _ _ EH12); [zlia | lia | apply Z.mod_1_r | lia].
  + apply (AFo EH hN n _ _ _ EHN); [lia | lia | apply Z.mod_1_r | lia].
  + apply (AFo EH hBUF buf _ _ _ EHB); [lia | lia | apply Z.mod_1_r | lia].
Qed.

Lemma bne_false : forall E a b, branch_taken BC_NE (sv_denot E a) (sv_denot E b) = false -> U E a = U E b.
Proof.
intros E a b H. unfold branch_taken, bv_eqb in H. apply Bool.negb_false_iff in H. apply Z.eqb_eq in H. unfold U. exact H.
Qed.
Lemma U_or0 : forall E k v, bv_unsigned (ew E k) = v -> 0 <= v < 2 ^ 64 -> U E (SAlu ALU_OR (SOff k 0) (SLit 0)) = v.
Proof.
intros E k v Hk Hv. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite Hk.
unfold zcanon, M64. cbn [zalu_raw]. rewrite Z.add_0_r, (Z.mod_small v), (Z.mod_small 0), Z.lor_0_r by lia. apply Z.mod_small. lia.
Qed.
Definition INVH (m : word -> option byte) : Prop :=
  (forall x : word, ~ (sp - 64 <= bv_unsigned x < sp) -> ~ (pk <= bv_unsigned x < pk + 8) -> m x = mem x) /\
  mem_grows (mrestrict H mem) (mrestrict H m).
Lemma INVH_mem : INVH mem.
Proof. split; [intros x _ _; reflexivity | intros a Ha; exact Ha]. Qed.
Definition wh_ok (rs : smem) : bool :=
  forallb (fun t => win_eqb t (Some 2%nat, -64, 0) || win_eqb t (Some 12%nat, 0, 8) || (snd t <=? snd (fst t))) (windows rs).
Lemma INVH_run : forall rs (m m' : word -> option byte), INVH m -> wh_ok rs = true -> frame_of EH rs m m' ->
  mem_grows (mrestrict H m) (mrestrict H m') -> INVH m'.
Proof.
intros rs m m' [IF IG] Hw HF HG. split.
- intros x N1 N2. rewrite (HF x); [exact (IF x N1 N2)|]. intros Hin.
  destruct (in_wrange_windows EH rs _ Hin) as (b & lo & hi & Ht & Hr).
  pose proof (proj1 (forallb_forall _ _) Hw _ Ht) as X. cbn beta in X.
  apply Bool.orb_prop in X as [X|X]; [apply Bool.orb_prop in X as [X|X]|].
  + apply win_eqb_eq in X. injection X as -> -> ->. cbn [base_val] in Hr. rewrite EH2 in Hr. lia.
  + apply win_eqb_eq in X. injection X as -> -> ->. cbn [base_val] in Hr. rewrite EH12, unsigned_lit_small in Hr by zlia. lia.
  + cbn [fst snd] in X. apply Z.leb_le in X. lia.
- exact (mem_grows_trans' _ _ _ IG HG).
Qed.
Ltac invh_step HI HI' :=
  lazymatch goal with
  | HF : frame_of _ ?rs ?mold (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
    assert (HI' : INVH (ms_mem msA)) by (apply (INVH_run rs _ _ HI ltac:(vm_compute; reflexivity) HF HG)); clear HF HG HI
  end.
Definition HFACTS (rg : bvmap 5 word) (m1 : word -> option byte) : Prop :=
  getr rg 1%bv = Z_to_bv 64 0x6e96c /\ getr rg 2%bv = Z_to_bv 64 (sp - 64) /\
  getr rg 10%bv = Z_to_bv 64 TFIB_STORE /\ getr rg 11%bv = Z_to_bv 64 (n + 1) /\ getr rg 12%bv = Z_to_bv 64 (sp - 64) /\
  getr rg 13%bv = Z_to_bv 64 pk /\ getr rg 8%bv = Z_to_bv 64 pk /\ getr rg 9%bv = Z_to_bv 64 TFIB_STORE /\
  getr rg 18%bv = Z_to_bv 64 (n + 1) /\ getr rg 19%bv = Z_to_bv 64 targ /\ getr rg 20%bv = Z_to_bv 64 n /\
  getr rg 21%bv = Z_to_bv 64 0 /\
  Forall (fun r : bv 5 => getr rg r = getr regs r) [3; 4; 22; 23; 24; 25; 26; 27]%bv /\
  val_mem tfibsegs (mrestrict H m1) (sp - 64) 8 0 /\
  val_mem tfibsegs (mrestrict H m1) (sp - 56) 8 (bv_unsigned (getr regs 21%bv)) /\
  val_mem tfibsegs (mrestrict H m1) (sp - 48) 8 (bv_unsigned (getr regs 20%bv)) /\
  val_mem tfibsegs (mrestrict H m1) (sp - 40) 8 (bv_unsigned (getr regs 19%bv)) /\
  val_mem tfibsegs (mrestrict H m1) (sp - 32) 8 (bv_unsigned (getr regs 18%bv)) /\
  val_mem tfibsegs (mrestrict H m1) (sp - 24) 8 (bv_unsigned (getr regs 9%bv)) /\
  val_mem tfibsegs (mrestrict H m1) (sp - 16) 8 (bv_unsigned (getr regs 8%bv)) /\
  val_mem tfibsegs (mrestrict H m1) (sp - 8) 8 (bv_unsigned (getr regs 1%bv)) /\
  val_mem tfibsegs (mrestrict H m1) pk 8 0 /\ INVH m1.
Lemma head_walk : forall (Q : world tfibsegs -> config -> Prop),
  (forall regs1 mem1 mat, HFACTS regs1 mem1 ->
     SRr tfibsegs W (mkCfg (mkst regs1 (Z_to_bv 64 tfib_A_StackStore_Alloc) mem1 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 0x6e8f4) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros Q K. pose proof Hwx_tfa as HWX. pose proof SEED_H as HS. pose proof INVH_mem as HI.
assert (UN : bv_unsigned (ew EH 32) = n) by (exact (eq_trans (f_equal bv_unsigned EHN) (unsigned_lit_small n ltac:(lia)))).
srr_run_toG tfibtbl_rtB_ok HS 0x6ea18. invh_step HI HI1.
srr_branch_with tfibtbl_rtB_ok HS.
2:{ exfalso. apply bne_false in Hc. rewrite (U_or0 EH 32 n UN ltac:(lia)), U_SLit in Hc. unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. lia. }
srr_run_toG tfibtbl_rtB_ok HS 0x6ea18. invh_step HI1 HI2.
srr_branch_with tfibtbl_rtB_ok HS.
- srr_run_toG tfibtbl_rtB_ok HS 0x6ea18. invh_step HI2 HI3.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) EH _ _ HS eq_refl). apply K.
  assert (ER : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew EH k = getr regs r) by (intros k r Hk; exact (ew_Ereg_nat regs _ k r Hk)).
  pose proof (u64_range (getr regs 2%bv)) as SR.
  unfold HFACTS.
  split. { rreg HS (1%bv : bv 5) G. exact G. }
  split. { rreg HS (2%bv : bv 5) G. rewrite G, EH2. reflexivity. }
  split. { rreg HS (10%bv : bv 5) G. exact G. }
  split. { rreg HS (11%bv : bv 5) G. rewrite G, UN. reflexivity. }
  split. { rreg HS (12%bv : bv 5) G. rewrite G, EH2. reflexivity. }
  split. { rreg HS (13%bv : bv 5) G. rewrite G, EH12. reflexivity. }
  split. { rreg HS (8%bv : bv 5) G. rewrite G, EH12. reflexivity. }
  split. { rreg HS (9%bv : bv 5) G. exact G. }
  split. { rreg HS (18%bv : bv 5) G. rewrite G, UN. reflexivity. }
  split. { rreg HS (19%bv : bv 5) G. rewrite G, EH11. reflexivity. }
  split. { rreg HS (20%bv : bv 5) G. rewrite G. exact EHN. }
  split. { rreg HS (21%bv : bv 5) G. exact G. }
  split. { repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- getr _ ?r = _ => rreg HS r G; rewrite G; apply ER; reflexivity end. }
  split. { memv HS 0%nat 0%nat; [rewrite EH2; lia | reflexivity | lia]. }
  split. { memv HS 0%nat 1%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 2%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 3%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 4%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 5%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 6%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 7%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 2%nat 0%nat; [rewrite EH12, unsigned_lit_small by zlia; lia | reflexivity | lia]. }
  exact HI3.
- apply (condZ_lit EH BC_LTU 32 0 255 false) in Hc0; [| rewrite UN; lia | lia]. cbn beta iota in Hc0. rewrite UN, Z.add_0_r in Hc0.
  apply Z.ltb_ge in Hc0. assert (Hn255 : n = 255) by lia.
  srr_run_toG tfibtbl_rtB_ok HS 0x6ea18. invh_step HI2 HI3.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) EH _ _ HS eq_refl). apply K.
  assert (ER : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew EH k = getr regs r) by (intros k r Hk; exact (ew_Ereg_nat regs _ k r Hk)).
  pose proof (u64_range (getr regs 2%bv)) as SR.
  unfold HFACTS.
  split. { rreg HS (1%bv : bv 5) G. exact G. }
  split. { rreg HS (2%bv : bv 5) G. rewrite G, EH2. reflexivity. }
  split. { rreg HS (10%bv : bv 5) G. exact G. }
  split. { rreg HS (11%bv : bv 5) G. rewrite G, Hn255. reflexivity. }
  split. { rreg HS (12%bv : bv 5) G. rewrite G, EH2. reflexivity. }
  split. { rreg HS (13%bv : bv 5) G. rewrite G, EH12. reflexivity. }
  split. { rreg HS (8%bv : bv 5) G. rewrite G, EH12. reflexivity. }
  split. { rreg HS (9%bv : bv 5) G. exact G. }
  split. { rreg HS (18%bv : bv 5) G. rewrite G, Hn255. reflexivity. }
  split. { rreg HS (19%bv : bv 5) G. rewrite G, EH11. reflexivity. }
  split. { rreg HS (20%bv : bv 5) G. rewrite G, Hn255. reflexivity. }
  split. { rreg HS (21%bv : bv 5) G. exact G. }
  split. { repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- getr _ ?r = _ => rreg HS r G; rewrite G; apply ER; reflexivity end. }
  split. { memv HS 0%nat 0%nat; [rewrite EH2; lia | reflexivity | lia]. }
  split. { memv HS 0%nat 1%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 2%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 3%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 4%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 5%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 6%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 0%nat 7%nat; [rewrite EH2; lia | cbn [sv_denot]; rewrite Z.add_0_r, !Z_to_bv_bv_unsigned; apply ER; reflexivity | apply u64_range]. }
  split. { memv HS 2%nat 0%nat; [rewrite EH12, unsigned_lit_small by zlia; lia | reflexivity | lia]. }
  exact HI3.
Qed.
End h.

(* ===== internal_memcpy 0x6232c: a leaf byte loop; it writes only the destination and clobbers a1-a4 ===== *)
Definition MC_ENTRY : Z := 0x6232c.
Definition MC_LOOP : Z := 0x62338.
Definition S_ME : sstate := mkSS MC_ENTRY sr_atoms [] None (mkFacts [(12%nat, mkAF 1 2048 0)] [] []).
Definition mBY : nat := 32.
Definition R_S1 : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff mBY 0))].
Definition R_D1 : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 1 [].
Definition LF : facts := mkFacts [(11%nat, mkAF 0 (2 ^ 63) 0); (13%nat, mkAF 0 (2 ^ 63) 0); (12%nat, mkAF 1 (2 ^ 63) 0); (mBY, mkAF 0 255 0)] [] [].
Definition S_L : sstate := mkSS MC_LOOP sr_atoms [R_S1; R_D1] None LF.
Definition MC_REGS : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section mcs. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d s len : Z).
#[local] Notation H := (w_H W).
Hypotheses (R10 : getr regs 10%bv = Z_to_bv 64 d) (R11 : getr regs 11%bv = Z_to_bv 64 s) (R12 : getr regs 12%bv = Z_to_bv 64 len).
Hypotheses (Hlen : 1 <= len <= 2048) (Hd : 0 <= d /\ d + len < 2 ^ 63) (Hs : 0 <= s /\ s + len < 2 ^ 63) (Hds : d + len <= s \/ s + len <= d).
Hypotheses (Psrc : forall k, 0 <= k < len -> mbyte tfibsegs (mrestrict H mem) (s + k) <> None)
  (Pdst : forall k, 0 <= k < len -> apresent H mem (d + k)).
Definition INVM (j : Z) (m : word -> option byte) : Prop :=
  (forall x : word, ~ (d <= bv_unsigned x < d + j) -> m x = mem x) /\ mem_grows (mrestrict H mem) (mrestrict H m) /\
  (forall k, 0 <= k < j -> mbyte tfibsegs (mrestrict H m) (d + k) = mbyte tfibsegs (mrestrict H mem) (s + k)).
Definition MCPOST (rg : bvmap 5 word) (m : word -> option byte) : Prop :=
  Forall (fun r => getr rg r = getr regs r) MC_REGS /\ INVM len m.
Variable Q : world tfibsegs -> config -> Prop.
Hypothesis K : forall rg m mat, MCPOST rg m ->
  SRr tfibsegs W (mkCfg (mkst rg (v_jalr (getr regs 1%bv) 0) m (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) Q.
Lemma SEED_L : forall j rg m (b : byte), 0 <= j < len ->
  getr rg 11%bv = Z_to_bv 64 (s + j) -> getr rg 13%bv = Z_to_bv 64 (d + j) -> getr rg 12%bv = Z_to_bv 64 (d + len) ->
  mbyte tfibsegs (mrestrict H m) (s + j) = Some b -> apresent H m (d + j) ->
  st_ok tfibsegs (Ereg rg [Z_to_bv 64 (bv_unsigned b)]) S_L (restrict H (mkst rg (Z_to_bv 64 MC_LOOP) m (seg_rom tfibsegs))).
Proof.
intros j rg m b Hj G11 G13 G12 Hb Hp. set (E := Ereg rg [Z_to_bv 64 (bv_unsigned b)]).
pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
assert (E11 : ew E 11 = Z_to_bv 64 (s + j)) by (rewrite <- G11; exact (ew_Ereg_nat rg _ 11 11%bv eq_refl)).
assert (E13 : ew E 13 = Z_to_bv 64 (d + j)) by (rewrite <- G13; exact (ew_Ereg_nat rg _ 13 13%bv eq_refl)).
assert (E12 : ew E 12 = Z_to_bv 64 (d + len)) by (rewrite <- G12; exact (ew_Ereg_nat rg _ 12 12%bv eq_refl)).
assert (EB : ew E mBY = Z_to_bv 64 (bv_unsigned b)) by reflexivity.
assert (U11 : bv_unsigned (ew E 11) = s + j) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = d + j) by (rewrite E13; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold S_L. apply (entry_st_ok_full tfibsegs).
all: try change (Ereg rg [Z_to_bv 64 (bv_unsigned b)]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons.
  { unfold R_S1. apply (region_ok_ro E (mrestrict H m) 11 (s + j)); [exact U11 | lia | lia |].
    apply Forall_cons; [| apply Forall_nil].
    eapply (chunk_ok_val tfibsegs E (mrestrict H m) (s + j) 0 1 (SOff mBY 0) (bv_unsigned b));
      [cbn [sv_denot]; rewrite EB, unsigned_lit_small by lia; f_equal; lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact (val_mem1_byte _ _ _ Hb)]. }
  apply Forall_cons; [| apply Forall_nil].
  { apply (region_ok_window E (mrestrict H m) 13 (d + j) 0 1 0 1); [exact U13 | lia | lia |].
    intros a Ha. replace a with (d + j) by lia. exact (apresent_wr H m _ Hp). }
- apply pairwise_disjoint_of_extents. unfold R_S1, R_D1. cbn [map]. rewrite !ext_Some, U11, U13.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [| split; exact I]. unfold LF. cbn [f_atoms]. apply atoms_ok_of_Forall.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  + apply (AFo E 11 (s + j) _ _ _ E11); [lia | lia | apply Z.mod_1_r | lia].
  + apply (AFo E 13 (d + j) _ _ _ E13); [lia | lia | apply Z.mod_1_r | lia].
  + apply (AFo E 12 (d + len) _ _ _ E12); [lia | lia | apply Z.mod_1_r | lia].
  + apply (AFo E mBY (bv_unsigned b) _ _ _ EB); [lia | lia | apply Z.mod_1_r | lia].
Qed.
Definition wd_ok (rs : smem) : bool :=
  forallb (fun t => win_eqb t (Some 13%nat, 0, 1) || (snd t <=? snd (fst t))) (windows rs).
Lemma frame_D1 : forall E rs (m m1 : word -> option byte) a, frame_of E rs m m1 -> wd_ok rs = true ->
  bv_unsigned (ew E 13) = a -> forall x : word, bv_unsigned x <> a -> m1 x = m x.
Proof.
intros E rs m m1 a HF Hw H13 x Hx. apply HF. intros Hin.
destruct (in_wrange_windows E rs _ Hin) as (b & lo & hi & Ht & Hr).
pose proof (proj1 (forallb_forall _ _) Hw _ Ht) as X. cbn beta in X. apply Bool.orb_prop in X as [X|X].
- apply win_eqb_eq in X. injection X as -> -> ->. cbn [base_val] in Hr. rewrite H13 in Hr. lia.
- cbn [fst snd] in X. apply Z.leb_le in X. lia.
Qed.
Lemma mbyte_same : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof. intros m m' a E. unfold mbyte. rewrite E. reflexivity. Qed.
Lemma INVM_step : forall j (m m1 : word -> option byte), 0 <= j < len -> INVM j m ->
  (forall x : word, bv_unsigned x <> d + j -> m1 x = m x) -> mem_grows (mrestrict H m) (mrestrict H m1) ->
  mbyte tfibsegs (mrestrict H m1) (d + j) = mbyte tfibsegs (mrestrict H mem) (s + j) -> INVM (j + 1) m1.
Proof.
intros j m m1 Hj (IF & IG & IC) HF HG HB. split; [| split].
- intros x Hx. destruct (Z.eq_dec (bv_unsigned x) (d + j)) as [E|E]; [lia|]. rewrite (HF x E). apply IF. lia.
- exact (mem_grows_trans' _ _ _ IG HG).
- intros k Hk. destruct (Z.eq_dec k j) as [->|Hne]; [exact HB|].
  rewrite <- (IC k ltac:(lia)). apply mbyte_same. unfold mrestrict. rewrite (HF (Z_to_bv 64 (d + k))); [reflexivity|].
  rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma src_same : forall j m, 0 <= j < len -> INVM j m -> mbyte tfibsegs (mrestrict H m) (s + j) = mbyte tfibsegs (mrestrict H mem) (s + j).
Proof.
intros j m Hj (IF & _ & _). apply mbyte_same. unfold mrestrict. rewrite (IF (Z_to_bv 64 (s + j))); [reflexivity|].
rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma dst_present : forall j m, 0 <= j < len -> INVM j m -> apresent H m (d + j).
Proof.
intros j m Hj (IF & _ & _). destruct (Pdst j Hj) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
rewrite (IF (Z_to_bv 64 (d + j))); [exact Hb|]. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma mc_iter : forall k j rg m mat, (Z.to_nat (len - j) <= k)%nat -> 0 <= j < len ->
  getr rg 11%bv = Z_to_bv 64 (s + j) -> getr rg 13%bv = Z_to_bv 64 (d + j) -> getr rg 12%bv = Z_to_bv 64 (d + len) ->
  Forall (fun r => getr rg r = getr regs r) MC_REGS -> INVM j m ->
  SRr tfibsegs W (mkCfg (mkst rg (Z_to_bv 64 MC_LOOP) m (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) Q.
Proof.
induction k as [|k IH]; intros j rg m mat Hk Hj G11 G13 G12 GR HI; [lia|].
pose proof Hwx_tfa as HWX.
pose proof (src_same j m Hj HI) as SS0.
destruct (mbyte tfibsegs (mrestrict H mem) (s + j)) as [b|] eqn:EB; [| exfalso; exact (Psrc j Hj EB)].
pose proof (SEED_L j rg m b Hj G11 G13 G12 SS0 (dst_present j m Hj HI)) as HS.
set (E := Ereg rg [Z_to_bv 64 (bv_unsigned b)]) in HS.
assert (E11 : ew E 11 = Z_to_bv 64 (s + j)) by (rewrite <- G11; exact (ew_Ereg_nat rg _ 11 11%bv eq_refl)).
assert (E13 : ew E 13 = Z_to_bv 64 (d + j)) by (rewrite <- G13; exact (ew_Ereg_nat rg _ 13 13%bv eq_refl)).
assert (E12 : ew E 12 = Z_to_bv 64 (d + len)) by (rewrite <- G12; exact (ew_Ereg_nat rg _ 12 12%bv eq_refl)).
assert (U13 : bv_unsigned (ew E 13) = d + j) by (rewrite E13; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = d + len) by (rewrite E12; apply unsigned_lit_small; lia).
assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rg r) by (intros n r Hn; exact (ew_Ereg_nat rg _ n r Hn)).
pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
srr_runG tfibtbl_rtB_ok HS.
pose proof (frame_D1 E _ _ _ (d + j) HF ltac:(vm_compute; reflexivity) U13) as F1.
srr_branch_with tfibtbl_rtB_ok HS.
- apply (condZ E BC_NE 13 1 12 0 true) in Hc; [| lia | lia]. cbn beta iota in Hc. rewrite U13, U12 in Hc.
  apply Bool.negb_true_iff in Hc. apply Z.eqb_neq in Hc.
  srr_run_toG tfibtbl_rtB_ok HS MC_LOOP.
  pose proof (frame_D1 E _ _ _ (d + j) HF1 ltac:(vm_compute; reflexivity) U13) as F2.
  assert (HB2 : mbyte tfibsegs (mrestrict H (ms_mem ms0)) (d + j) = mbyte tfibsegs (mrestrict H mem) (s + j)).
  { rewrite EB. rewrite <- (Z_to_bv_bv_unsigned _ b). apply val_mem1_mbyte; [| lia].
    memv HS 1%nat 0%nat; [rewrite U13; lia | cbn [sv_denot]; rewrite Z.add_0_r; change (ew E 32) with (Z_to_bv 64 (bv_unsigned b)); rewrite unsigned_lit_small by lia; reflexivity | lia]. }
  assert (HI2 : INVM (j + 1) (ms_mem ms0)).
  { apply (INVM_step j m (ms_mem ms0) Hj HI); [| exact (mem_grows_trans' _ _ _ HG HG0) | exact HB2].
    intros x Hx. rewrite (F2 x Hx). exact (F1 x Hx). }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS eq_refl).
  apply (IH (j + 1) (ms_regs ms0) (ms_mem ms0) mat ltac:(lia) ltac:(lia)); [| | | | exact HI2].
  + rreg HS (11%bv : bv 5) G. rewrite G, E11, unsigned_lit_small by lia. f_equal. lia.
  + rreg HS (13%bv : bv 5) G. rewrite G, E13, unsigned_lit_small by lia. f_equal. lia.
  + rreg HS (12%bv : bv 5) G. rewrite G. exact E12.
  + rewrite Forall_forall in GR. unfold MC_REGS. repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- getr _ ?r = _ => rreg HS r G; rewrite G; transitivity (getr rg r); [apply (ER _ r); reflexivity | apply GR; cbn; tauto] end.
- apply (condZ E BC_NE 13 1 12 0 false) in Hc; [| lia | lia]. cbn beta iota in Hc. rewrite U13, U12 in Hc.
  apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc. assert (Hjl : len = j + 1) by lia.
  srr_runG tfibtbl_rtB_ok HS.
  pose proof (frame_D1 E _ _ _ (d + j) HF1 ltac:(vm_compute; reflexivity) U13) as F2.
  assert (HB2 : mbyte tfibsegs (mrestrict H (ms_mem ms0)) (d + j) = mbyte tfibsegs (mrestrict H mem) (s + j)).
  { rewrite EB. rewrite <- (Z_to_bv_bv_unsigned _ b). apply val_mem1_mbyte; [| lia].
    memv HS 1%nat 0%nat; [rewrite U13; lia | cbn [sv_denot]; rewrite Z.add_0_r; change (ew E 32) with (Z_to_bv 64 (bv_unsigned b)); rewrite unsigned_lit_small by lia; reflexivity | lia]. }
  assert (HI2 : INVM (j + 1) (ms_mem ms0)).
  { apply (INVM_step j m (ms_mem ms0) Hj HI); [| exact (mem_grows_trans' _ _ _ HG HG0) | exact HB2].
    intros x Hx. rewrite (F2 x Hx). exact (F1 x Hx). }
  rewrite Forall_forall in GR.
  apply (SRr_bind tfibsegs W _ (fun W1 c1 => SRr tfibsegs W1 c1 Q) Q); [| intros W1 c1 _ HR; exact HR].
  eapply (SRr_ret_at tfibsegs tfibtbl_rtB tfibtbl_rtB_ok HWX W); [exact HS | reflexivity | vm_compute; reflexivity |].
  intros mat'. rewrite wvb_collapse.
  assert (R1 : getr (ms_regs ms0) 1%bv = getr regs 1%bv).
  { rreg HS (1%bv : bv 5) G. rewrite G. transitivity (getr rg 1%bv); [apply (ER _ 1%bv); reflexivity | apply GR; cbn; tauto]. }
  rewrite R1. apply K. split; [| rewrite Hjl; exact HI2].
  unfold MC_REGS. repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- getr _ ?r = _ => rreg HS r G; rewrite G; transitivity (getr rg r); [apply (ER _ r); reflexivity | apply GR; cbn; tauto] end.
Qed.
Definition EM : env := Ereg regs [].
Lemma SEED_ME : st_ok tfibsegs EM S_ME (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
assert (E12 : ew EM 12 = Z_to_bv 64 len) by (rewrite <- R12; exact (ew_Ereg_nat regs _ 12 12%bv eq_refl)).
rewrite restrict_mkst_fx. unfold S_ME. apply (entry_st_ok_full tfibsegs).
all: try change (Ereg regs []) with EM.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint]. exact I.
- split; [| split; exact I]. cbn [f_atoms]. apply atoms_ok_of_Forall.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  apply (AFo EM 12 len _ _ _ E12); [lia | lia | apply Z.mod_1_r | lia].
Qed.
Lemma mc_ok : SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfibsegs)) md) Q.
Proof.
pose proof Hwx_tfa as HWX. pose proof SEED_ME as HS.
assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EM n = getr regs r) by (intros n r Hn; exact (ew_Ereg_nat regs _ n r Hn)).
assert (U12 : bv_unsigned (ew EM 12) = len) by (rewrite (ER 12%nat 12%bv eq_refl), R12; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew EM 10) = d) by (rewrite (ER 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew EM 11) = s) by (rewrite (ER 11%nat 11%bv eq_refl), R11; apply unsigned_lit_small; lia).
srr_run_toG tfibtbl_rtB_ok HS MC_LOOP.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) EM _ _ HS eq_refl).
apply (mc_iter (Z.to_nat len) 0 (ms_regs ms) (ms_mem ms) mat ltac:(lia) ltac:(lia)).
+ rreg HS (11%bv : bv 5) G. rewrite G, (ER 11%nat 11%bv eq_refl), R11. f_equal. lia.
+ rreg HS (13%bv : bv 5) G. rewrite G, (ER 10%nat 10%bv eq_refl), R10. f_equal. lia.
+ rreg HS (12%bv : bv 5) G. rewrite G, (ER 10%nat 10%bv eq_refl), (ER 12%nat 12%bv eq_refl), R10, R12. apply YI08.alu64_add_lit.
+ unfold MC_REGS. repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- getr _ ?r = _ => rreg HS r G; rewrite G; apply (ER _ r); reflexivity end.
+ split; [| split].
  * intros x _. apply HF. intros Hin. destruct (in_wrange_windows EM _ _ Hin) as (b & lo & hi & Ht & Hr). exact Ht.
  * exact HG.
  * intros k Hk. lia.
Qed.
End mcs.


(* ===== Store's tail, part 1: 0x6e96c (Alloc's return) to internal_memcpy and back to 0x6e98c ===== *)
Definition tBUF : nat := 32.
Definition R_TG1 : YP09.region := YP09.mkRegion (Some 19%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff tBUF 0))].
Definition R_SL1 : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 8 [].
Definition RG_T : list sv := sr_set (sr_set (sr_set sr_atoms 9%bv (SLit TFIB_STORE)) 18%bv (SOff 20 1)) 21%bv (SLit 0).
Definition FT1 : facts := mkFacts [(10%nat, mkAF 4096 (2 ^ 63) 0); (19%nat, mkAF kHighMemBeg (kHighMemEnd - 16) 0); (tBUF, mkAF 0 (2 ^ 63) 0); (20%nat, mkAF 1 255 0)] [] [].
Definition S_T1 : sstate := mkSS 0x6e96c RG_T [R_TG1; R_SL1] None FT1.
Definition T1REGS : list (bv 5) := [2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma frame_wins : forall E rs (m m' : word -> option byte), frame_of E rs m m' -> forall x : word,
  (forall b lo hi, In (b, lo, hi) (windows rs) -> ~ (base_val E b + lo <= bv_unsigned x < base_val E b + hi)) -> m' x = m x.
Proof.
intros E rs m m' HF x Hx. apply HF. intros Hin. destruct (in_wrange_windows E rs _ Hin) as (b & lo & hi & Ht & Hr). exact (Hx b lo hi Ht Hr).
Qed.
Section t1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (W : world tfibsegs) (rg : bvmap 5 word) (mem : word -> option byte) (md : Model) (slot targ buf n : Z).
#[local] Notation H := (w_H W).
Hypotheses (G10 : getr rg 10%bv = Z_to_bv 64 slot) (G9 : getr rg 9%bv = Z_to_bv 64 TFIB_STORE) (G18 : getr rg 18%bv = Z_to_bv 64 (n + 1))
  (G19 : getr rg 19%bv = Z_to_bv 64 targ) (G20 : getr rg 20%bv = Z_to_bv 64 n) (G21 : getr rg 21%bv = Z_to_bv 64 0).
Hypotheses (Hn : 1 <= n <= 255) (Hsl : 4096 <= slot /\ slot + 8 * (n + 1) < 2 ^ 62)
  (Htg : kHighMemBeg <= targ /\ targ + 16 <= kHighMemEnd) (Hbf : kHighMemBeg <= buf /\ buf + 8 * n <= kHighMemEnd)
  (Tb : val_mem tfibsegs (mrestrict H mem) targ 8 buf)
  (Psl : forall a, slot <= a < slot + 8 * (n + 1) -> apresent H mem a)
  (Dtg : zdisjoint (slot, 8 * (n + 1)) (targ, 16)) (Dbf : zdisjoint (slot, 8 * (n + 1)) (buf, 8 * n))
  (Psrc : forall k, 0 <= k < 8 * n -> mbyte tfibsegs (mrestrict H mem) (buf + k) <> None).
Definition ET1 : env := Ereg rg [Z_to_bv 64 buf].
Lemma ET1r : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew ET1 k = getr rg r.
Proof. intros k r Hk. exact (ew_Ereg_nat rg _ k r Hk). Qed.
Lemma SEED_T1 : st_ok tfibsegs ET1 S_T1 (restrict H (mkst rg (Z_to_bv 64 0x6e96c) mem (seg_rom tfibsegs))).
Proof.
assert (U10 : bv_unsigned (ew ET1 10) = slot) by (rewrite (ET1r 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew ET1 19) = targ) by (rewrite (ET1r 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; zlia).
assert (U20 : bv_unsigned (ew ET1 20) = n) by (rewrite (ET1r 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold S_T1, RG_T. apply (entry_st_ok_full tfibsegs).
all: try change (Ereg rg [Z_to_bv 64 buf]) with ET1.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact G9] | intros X; discriminate |] | intros X; discriminate | cbn [sv_denot]; exact G21].
  cbn [sv_denot]. rewrite U20. exact G18.
- vm_compute. reflexivity.
- apply Forall_cons.
  { unfold R_TG1. apply (region_ok_ro ET1 (mrestrict H mem) 19 targ); [exact U19 | zlia | zlia |].
    apply Forall_cons; [| apply Forall_nil].
    eapply (chunk_ok_val tfibsegs ET1 (mrestrict H mem) targ 0 8 (SOff tBUF 0) buf);
      [cbn [sv_denot]; change (ew ET1 tBUF) with (Z_to_bv 64 buf); rewrite unsigned_lit_small by zlia; f_equal; lia | cbn; zlia | cbn; lia | rewrite Z.add_0_r; exact Tb]. }
  apply Forall_cons; [| apply Forall_nil].
  { apply (region_ok_window ET1 (mrestrict H mem) 10 slot 0 8 0 8); [exact U10 | lia | lia |].
    intros a Ha. apply (apresent_wr H mem a). apply Psl. lia. }
- apply pairwise_disjoint_of_extents. unfold R_TG1, R_SL1. cbn [map]. rewrite !ext_Some, U19, U10.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold zdisjoint in Dtg. cbn [fst snd] in Dtg. repeat split; lia.
- split; [| split; exact I]. unfold FT1. cbn [f_atoms]. apply atoms_ok_of_Forall.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  + apply (AFo ET1 10 slot _ _ _ (eq_trans (ET1r 10%nat 10%bv eq_refl) G10)); [lia | lia | apply Z.mod_1_r | lia].
  + apply (AFo ET1 19 targ _ _ _ (eq_trans (ET1r 19%nat 19%bv eq_refl) G19)); [zlia | zlia | apply Z.mod_1_r | lia].
  + apply (AFo ET1 tBUF buf _ _ _ eq_refl); [zlia | zlia | apply Z.mod_1_r | lia].
  + apply (AFo ET1 20 n _ _ _ (eq_trans (ET1r 20%nat 20%bv eq_refl) G20)); [lia | lia | apply Z.mod_1_r | lia].
Qed.
Definition T1POST (rg' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  Forall (fun r => getr rg' r = getr rg r) T1REGS /\
  (forall x : word, ~ (slot <= bv_unsigned x < slot + 8 * (n + 1)) -> m' x = mem x) /\
  mem_grows (mrestrict H mem) (mrestrict H m') /\
  val_mem tfibsegs (mrestrict H m') slot 8 n /\
  (forall k, 0 <= k < 8 * n -> mbyte tfibsegs (mrestrict H m') (slot + 8 + k) = mbyte tfibsegs (mrestrict H mem) (buf + k)).
Variable Q : world tfibsegs -> config -> Prop.
Hypothesis K : forall rg' m' mat, T1POST rg' m' ->
  SRr tfibsegs W (mkCfg (mkst rg' (Z_to_bv 64 0x6e98c) m' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)) Q.
Lemma t1_ok : SRr tfibsegs W (mkCfg (mkst rg (Z_to_bv 64 0x6e96c) mem (seg_rom tfibsegs)) md) Q.
Proof.
pose proof Hwx_tfa as HWX. pose proof SEED_T1 as HS.
assert (U10 : bv_unsigned (ew ET1 10) = slot) by (rewrite (ET1r 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew ET1 20) = n) by (rewrite (ET1r 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
rewrite (same_but_materialized_wvb md md (same_but_materialized_refl md)).
srr_run_toG tfibtbl_rtB_ok HS MC_ENTRY.
assert (F1 : forall x : word, ~ (slot <= bv_unsigned x < slot + 8) -> ms_mem ms x = mem x).
{ intros x Hx. apply (frame_wins ET1 _ _ _ HF). intros b lo hi Ht. vm_compute in Ht.
  destruct Ht as [Ht|[Ht|[]]]; injection Ht as <- <- <-; cbn [base_val]; [lia | rewrite U10; lia]. }
assert (VH : val_mem tfibsegs (mrestrict H (ms_mem ms)) slot 8 n).
{ memv HS 1%nat 0%nat; [rewrite U10; lia | | lia].
  apply denot_of_U. rewrite U_zev by reflexivity. cbn [zev zalu_raw svpure]. unfold rho_of. rewrite U20.
  unfold zcanon, M64. rewrite ?Z.add_0_r, ?Z.lor_0_l. repeat rewrite (Z.mod_small n) by lia. reflexivity. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) ET1 _ _ HS eq_refl).
assert (ER : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew ET1 k = getr rg r) by exact ET1r.
apply (mc_ok W (ms_regs ms) (ms_mem ms) _ (slot + 8) buf (8 * n)).
- rreg HS (10%bv : bv 5) G. rewrite G, U10. reflexivity.
- rreg HS (11%bv : bv 5) G. rewrite G. reflexivity.
- rreg HS (12%bv : bv 5) G. rewrite G, (ER 20%nat 20%bv eq_refl), G20. rewrite YI08.alu64_sll_lit by (cbn; lia). f_equal. cbn. lia.
- lia.
- lia.
- zlia.
- unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. lia.
- intros k Hk. assert (E1 : mbyte tfibsegs (mrestrict H (ms_mem ms)) (buf + k) = mbyte tfibsegs (mrestrict H mem) (buf + k)).
  { apply mbyte_same. unfold mrestrict. rewrite (F1 (Z_to_bv 64 (buf + k))); [reflexivity|]. rewrite unsigned_lit_small by zlia.
    unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. lia. }
  rewrite E1. apply Psrc. exact Hk.
- intros k Hk. apply (apresent_grows H mem (ms_mem ms) _ HG). apply Psl. lia.
- intros rg' m' mat' (GR & IF & IG & IC). rewrite wvb_collapse.
  assert (R1 : v_jalr (getr (ms_regs ms) 1%bv) 0 = Z_to_bv 64 0x6e98c) by (rreg HS (1%bv : bv 5) G; rewrite G; vm_compute; reflexivity).
  rewrite R1. apply K. rewrite Forall_forall in GR. split; [| split; [| split; [| split]]].
  + unfold T1REGS. repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- getr _ ?r = _ => rewrite (GR r ltac:(cbn; tauto)); rreg HS r G; rewrite G;
      first [apply ER; reflexivity | rewrite G9; reflexivity | rewrite G21; reflexivity
            | rewrite G18, (ER 20%nat 20%bv eq_refl), G20, unsigned_lit_small by lia; reflexivity] end.
  + intros x Hx. rewrite (IF x ltac:(lia)). apply F1. lia.
  + exact (mem_grows_trans' _ _ _ HG IG).
  + eapply (val_mem_frame H (ms_mem ms) m'); [| exact VH]. intros k Hk. apply IF. rewrite unsigned_lit_small by lia. lia.
  + intros k Hk. rewrite (IC k Hk). apply mbyte_same. unfold mrestrict. rewrite (F1 (Z_to_bv 64 (buf + k))); [reflexivity|].
    rewrite unsigned_lit_small by zlia. unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. lia.
Qed.
End t1.


(* ===== Store's tail, part 2: 0x6e98c (internal_memcpy's return) to Store's ret ===== *)
Definition uF : nat := 32. Definition uSTD : nat := 33. Definition uRA : nat := 34. Definition uS0 : nat := 35.
Definition uS1 : nat := 36. Definition uS2 : nat := 37. Definition uS3 : nat := 38. Definition uS4 : nat := 39. Definition uS5 : nat := 40.
Definition R_FR2 : YP09.region := YP09.mkRegion (Some 2%nat) 0 64 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff uF 0)); YP09.mkChunk 8 (CVal 8 (SOff uS5 0)); YP09.mkChunk 16 (CVal 8 (SOff uS4 0));
   YP09.mkChunk 24 (CVal 8 (SOff uS3 0)); YP09.mkChunk 32 (CVal 8 (SOff uS2 0)); YP09.mkChunk 40 (CVal 8 (SOff uS1 0));
   YP09.mkChunk 48 (CVal 8 (SOff uS0 0)); YP09.mkChunk 56 (CVal 8 (SOff uRA 0))].
Definition R_STD2 : YP09.region := YP09.mkRegion None (TFIB_STORE + 24) (TFIB_STORE + 28) (TFIB_STORE + 24) (TFIB_STORE + 28)
  [YP09.mkChunk (TFIB_STORE + 24) (CVal 4 (SOff uSTD 0))].
Definition R_PK2 : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))].
Definition FT2 : facts := mkFacts [(2%nat, mkAF kHighMemBeg (kHighMemEnd - 64) 4); (8%nat, mkAF kHighMemBeg (kHighMemEnd - 8) 0);
  (20%nat, mkAF 1 255 0); (uF, mkAF 0 (2 ^ 20 - 2) 0); (uSTD, mkAF 0 (2 ^ 20 - 3) 0)] [] [].
Definition S_T2 : sstate := mkSS 0x6e98c RG_T [R_FR2; R_STD2; R_PK2] None FT2.
Definition T2KEEP : list (bv 5) := [3; 4; 22; 23; 24; 25; 26; 27]%bv.
Lemma tfibsegs_TSEGS' : tfibsegs = TSEGS. Proof. reflexivity. Qed.
Lemma rw_wr : forall (m : word -> option byte) a, 0x96000 <= a < YImgTop.IMG_TOP -> writable_at tfibsegs m a.
Proof. intros m a Ha. pose proof Ha as Hn. unfold YImgTop.IMG_TOP in Hn. unfold writable_at. rewrite tfibsegs_TSEGS'. apply tfib_rw_window. rewrite unsigned_lit_small by lia. lia. Qed.
Lemma land_m16_small : forall x, 0 <= x < 16 -> Z.land x (-16) = 0.
Proof.
intros x Hx. change (-16) with (Z.lnot (Z.ones 4)). rewrite <- Z.ldiff_land. rewrite Z.ldiff_ones_r by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by (cbn; lia). reflexivity.
Qed.
Lemma lxor_2p20 : forall a, 0 <= a < 2 ^ 20 -> Z.lxor a (2 ^ 20) = a + 2 ^ 20.
Proof.
intros a Ha. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj_0. intros i.
rewrite Z.land_spec. destruct (Z.eq_dec i 20) as [->|Hne].
- rewrite Z.pow2_bits_true by lia. rewrite Bool.andb_true_r. apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
- rewrite Z.pow2_bits_false by lia. apply Bool.andb_false_r.
Qed.
Section t2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (W : world tfibsegs) (rg : bvmap 5 word) (mem : word -> option byte) (md : Model) (sp1 pk n F std : Z) (ra0 v0 v1 v2 v3 v4 v5 : word).
#[local] Notation H := (w_H W).
#[local] Notation m0 := (mrestrict (w_H W) mem).
Hypotheses (G2 : getr rg 2%bv = Z_to_bv 64 sp1) (G8 : getr rg 8%bv = Z_to_bv 64 pk) (G9 : getr rg 9%bv = Z_to_bv 64 TFIB_STORE)
  (G18 : getr rg 18%bv = Z_to_bv 64 (n + 1)) (G20 : getr rg 20%bv = Z_to_bv 64 n) (G21 : getr rg 21%bv = Z_to_bv 64 0).
Hypotheses (Hn : 1 <= n <= 255) (HFr : 0 <= F /\ F + n + 1 <= 2 ^ 20) (Hstd : 0 <= std /\ std + n + 1 < 2 ^ 20)
  (Hsp : kHighMemBeg <= sp1 /\ sp1 + 64 <= kHighMemEnd /\ sp1 mod 16 = 0)
  (Hpk : kHighMemBeg <= pk /\ pk + 8 <= kHighMemEnd) (Dpk : pk + 8 <= sp1 \/ sp1 + 64 <= pk).
Hypotheses (V0 : val_mem tfibsegs m0 sp1 8 F) (V8 : val_mem tfibsegs m0 (sp1 + 8) 8 (bv_unsigned v5))
  (V16 : val_mem tfibsegs m0 (sp1 + 16) 8 (bv_unsigned v4)) (V24 : val_mem tfibsegs m0 (sp1 + 24) 8 (bv_unsigned v3))
  (V32 : val_mem tfibsegs m0 (sp1 + 32) 8 (bv_unsigned v2)) (V40 : val_mem tfibsegs m0 (sp1 + 40) 8 (bv_unsigned v1))
  (V48 : val_mem tfibsegs m0 (sp1 + 48) 8 (bv_unsigned v0)) (V56 : val_mem tfibsegs m0 (sp1 + 56) 8 (bv_unsigned ra0))
  (VS : val_mem tfibsegs m0 (TFIB_STORE + 24) 4 std) (VP : val_mem tfibsegs m0 pk 8 0)
  (PP : forall k, 0 <= k < 8 -> apresent H mem (pk + k)).
Definition ET2 : env := Ereg rg [Z_to_bv 64 F; Z_to_bv 64 std; ra0; v0; v1; v2; v3; v4; v5].
Lemma ET2r : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew ET2 k = getr rg r.
Proof. intros k r Hk. exact (ew_Ereg_nat rg _ k r Hk). Qed.
Lemma U2_2 : bv_unsigned (ew ET2 2) = sp1. Proof. rewrite (ET2r 2%nat 2%bv eq_refl), G2. apply unsigned_lit_small. zlia. Qed.
Lemma U2_8 : bv_unsigned (ew ET2 8) = pk. Proof. rewrite (ET2r 8%nat 8%bv eq_refl), G8. apply unsigned_lit_small. zlia. Qed.
Lemma U2_20 : bv_unsigned (ew ET2 20) = n. Proof. rewrite (ET2r 20%nat 20%bv eq_refl), G20. apply unsigned_lit_small. lia. Qed.
Lemma U2_F : bv_unsigned (ew ET2 32) = F. Proof. change (ew ET2 32) with (Z_to_bv 64 F). apply unsigned_lit_small. lia. Qed.
Lemma U2_S : bv_unsigned (ew ET2 33) = std. Proof. change (ew ET2 33) with (Z_to_bv 64 std). apply unsigned_lit_small. lia. Qed.
Lemma SEED_T2 : st_ok tfibsegs ET2 S_T2 (restrict H (mkst rg (Z_to_bv 64 0x6e98c) mem (seg_rom tfibsegs))).
Proof.
pose proof U2_2 as U2. pose proof U2_8 as U8. pose proof U2_20 as U20.
rewrite restrict_mkst_fx. unfold S_T2, RG_T. apply (entry_st_ok_full tfibsegs).
all: try change (Ereg rg [Z_to_bv 64 F; Z_to_bv 64 std; ra0; v0; v1; v2; v3; v4; v5]) with ET2.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact G9] | intros X; discriminate |] | intros X; discriminate | cbn [sv_denot]; exact G21].
  cbn [sv_denot]. rewrite U20. exact G18.
- vm_compute. reflexivity.
- apply Forall_cons.
  { unfold R_FR2. apply (region_ok_ro ET2 m0 2 sp1); [exact U2 | zlia | zlia |].
    assert (CK : forall (o : Z) (k : nat) (w : word), ew ET2 k = w -> val_mem tfibsegs m0 (sp1 + o) 8 (bv_unsigned w) ->
      YP09.chunk_ok tfibsegs ET2 m0 sp1 (YP09.mkChunk o (CVal 8 (SOff k 0)))).
    { intros o k w Hk Hv. eapply (chunk_ok_val tfibsegs ET2 m0 sp1 o 8 (SOff k 0) (bv_unsigned w));
        [cbn [sv_denot]; rewrite Hk, Z.add_0_r; reflexivity | apply u64_range | cbn; lia | exact Hv]. }
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (CK 0 uF (Z_to_bv 64 F) eq_refl). rewrite Z.add_0_r, unsigned_lit_small by lia. exact V0.
    - exact (CK 8 uS5 v5 eq_refl V8).
    - exact (CK 16 uS4 v4 eq_refl V16).
    - exact (CK 24 uS3 v3 eq_refl V24).
    - exact (CK 32 uS2 v2 eq_refl V32).
    - exact (CK 40 uS1 v1 eq_refl V40).
    - exact (CK 48 uS0 v0 eq_refl V48).
    - exact (CK 56 uRA ra0 eq_refl V56). }
  apply Forall_cons.
  { unfold region_ok, R_STD2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold TFIB_STORE; lia|]. split; [unfold TFIB_STORE; lia|]. split; [intros o Ho; apply rw_wr; unfold TFIB_STORE, YImgTop.IMG_TOP in *; lia|].
    apply Forall_cons; [| apply Forall_nil].
    eapply (chunk_ok_val tfibsegs ET2 m0 0 (TFIB_STORE + 24) 4 (SOff uSTD 0) std);
      [cbn [sv_denot]; change (ew ET2 uSTD) with (Z_to_bv 64 std); rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VS]. }
  apply Forall_cons; [| apply Forall_nil].
  { unfold region_ok, R_PK2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
    split; [zlia|]. split; [zlia|]. split; [intros o Ho; apply (apresent_wr H mem); apply PP; lia|].
    apply Forall_cons; [| apply Forall_nil].
    eapply (chunk_ok_val tfibsegs ET2 m0 pk 0 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VP]. }
- apply pairwise_disjoint_of_extents. unfold R_FR2, R_STD2, R_PK2. cbn [map]. rewrite !ext_Some, ext_None, U2, U8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold TFIB_STORE, kHighMemBeg in *. repeat split; lia.
- split; [| split; exact I]. unfold FT2. cbn [f_atoms]. apply atoms_ok_of_Forall.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  + apply (AFo ET2 2 sp1 _ _ _ (eq_trans (ET2r 2%nat 2%bv eq_refl) G2)); [zlia | zlia | change (2 ^ 4) with 16; lia | lia].
  + apply (AFo ET2 8 pk _ _ _ (eq_trans (ET2r 8%nat 8%bv eq_refl) G8)); [zlia | zlia | apply Z.mod_1_r | lia].
  + apply (AFo ET2 20 n _ _ _ (eq_trans (ET2r 20%nat 20%bv eq_refl) G20)); [lia | lia | apply Z.mod_1_r | lia].
  + apply (AFo ET2 uF F _ _ _ eq_refl); [lia | lia | apply Z.mod_1_r | lia].
  + apply (AFo ET2 uSTD std _ _ _ eq_refl); [lia | lia | apply Z.mod_1_r | lia].
Qed.
Definition T2POST (rg' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  getr rg' 10%bv = Z_to_bv 64 (F + 1) /\ getr rg' 1%bv = ra0 /\ getr rg' 2%bv = Z_to_bv 64 (sp1 + 64) /\
  getr rg' 8%bv = v0 /\ getr rg' 9%bv = v1 /\ getr rg' 18%bv = v2 /\ getr rg' 19%bv = v3 /\ getr rg' 20%bv = v4 /\ getr rg' 21%bv = v5 /\
  Forall (fun r => getr rg' r = getr rg r) T2KEEP /\
  (forall x : word, ~ (TFIB_STORE + 24 <= bv_unsigned x < TFIB_STORE + 28) -> ~ (pk <= bv_unsigned x < pk + 8) -> m' x = mem x) /\
  mem_grows (mrestrict H mem) (mrestrict H m') /\
  val_mem tfibsegs (mrestrict H m') (TFIB_STORE + 24) 4 (std + n + 1) /\ val_mem tfibsegs (mrestrict H m') pk 8 0.
Variable Q : world tfibsegs -> config -> Prop.
Hypothesis K : forall rg' m' mat, T2POST rg' m' ->
  Q W (mkCfg (mkst rg' (v_jalr ra0 0) m' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md)).
Lemma t2_ok : SRr tfibsegs W (mkCfg (mkst rg (Z_to_bv 64 0x6e98c) mem (seg_rom tfibsegs)) md) Q.
Proof.
pose proof Hwx_tfa as HWX. pose proof SEED_T2 as HS.
pose proof U2_2 as U2. pose proof U2_8 as U8. pose proof U2_20 as U20. pose proof U2_F as UF. pose proof U2_S as US.
rewrite (same_but_materialized_wvb md md (same_but_materialized_refl md)).
srr_run_toG tfibtbl_rtB_ok HS 0x6e9a0.
apply (st_ok_pin_regU ET2 _ _ 10%bv (SLit (TFIB_STORE + 24))) in HS; [| intros X; discriminate |].
2:{ pin_zev. rewrite U2_F, Z.add_0_r, (zcanon_id F) by (unfold M64; lia). change (Z.land (zcanon 16) 63) with 16.
    assert (Hy : 0 <= Z.shiftr F 16 < 16) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    remember (Z.shiftr F 16) as y eqn:Ey. clear Ey.
    assert (Hc : y = 0 \/ y = 1 \/ y = 2 \/ y = 3 \/ y = 4 \/ y = 5 \/ y = 6 \/ y = 7 \/ y = 8 \/ y = 9 \/ y = 10 \/ y = 11 \/ y = 12 \/ y = 13 \/ y = 14 \/ y = 15) by lia.
    repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]). rewrite Hc. vm_compute. reflexivity. }
srr_run_shG tfibtbl_rtB_ok HS.
lazymatch goal with
| HFa : frame_of _ _ mem (ms_mem ?msA), HGa : mem_grows _ (mrestrict _ (ms_mem ?msA)),
  HFb : frame_of _ _ (ms_mem ?msA) (ms_mem ?msB), HGb : mem_grows (mrestrict _ (ms_mem ?msA)) _ |- _ =>
  assert (FR : forall x : word, ~ (TFIB_STORE + 24 <= bv_unsigned x < TFIB_STORE + 28) -> ~ (pk <= bv_unsigned x < pk + 8) -> ms_mem msB x = mem x);
  [ intros x X1 X2; unfold TFIB_STORE in X1; rewrite (frame_wins ET2 _ _ _ HFb x), (frame_wins ET2 _ _ _ HFa x); [reflexivity | |];
    intros b lo hi Ht; vm_compute in Ht;
    repeat (destruct Ht as [Ht|Ht]; [injection Ht as <- <- <-; cbn [base_val]; rewrite ?U8; lia|]); destruct Ht
  | assert (GR : mem_grows (mrestrict H mem) (mrestrict H (ms_mem msB))) by exact (mem_grows_trans' _ _ _ HGa HGb) ]
end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtB tfibtbl_rtB_ok HWX W); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse.
assert (R1 : getr (ms_regs ms0) 1%bv = ra0) by (rreg HS (1%bv : bv 5) G; rewrite G; reflexivity).
rewrite R1. apply K.
split. { rreg HS (10%bv : bv 5) G. rewrite G, UF. reflexivity. }
split. { exact R1. }
split. { rreg HS (2%bv : bv 5) G. rewrite G, U2. reflexivity. }
split. { rreg HS (8%bv : bv 5) G. rewrite G. reflexivity. }
split. { rreg HS (9%bv : bv 5) G. rewrite G. reflexivity. }
split. { rreg HS (18%bv : bv 5) G. rewrite G. reflexivity. }
split. { rreg HS (19%bv : bv 5) G. rewrite G. reflexivity. }
split. { rreg HS (20%bv : bv 5) G. rewrite G. reflexivity. }
split. { rreg HS (21%bv : bv 5) G. rewrite G. reflexivity. }
split. { unfold T2KEEP. repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- getr _ ?r = _ => rreg HS r G; rewrite G; apply ET2r; reflexivity end. }
split. { exact FR. }
split. { exact GR. }
split.
- memv HS 1%nat 0%nat; [unfold TFIB_STORE; lia | | lia].
  apply denot_of_U. rewrite U_zev by reflexivity. cbn [zev zalu_raw svpure]. unfold rho_of. rewrite U20, US.
  rewrite Z.add_0_r, (zcanon_id (n + 1)), (zcanon_id std), (zcanon_id (n + 1 + std)) by (unfold M64; lia). lia.
- memv HS 2%nat 0%nat; [rewrite U8; lia | | lia].
  apply denot_of_U. rewrite U_zev by reflexivity. cbn [zev zalu_raw svpure]. unfold rho_of. rewrite U20, US.
  rewrite Z.add_0_r, (zcanon_id (n + 1)), (zcanon_id std), (zcanon_id (n + 1 + std)), (zcanon_id 1048576) by (unfold M64; lia).
  change 1048576 with (2 ^ 20). rewrite lxor_2p20 by lia. rewrite (zcanon_id (n + 1 + std + 2 ^ 20)) by (unfold M64; lia).
  rewrite (zcanon_id 1) by (unfold M64; lia). replace (n + 1 + std + 2 ^ 20 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  vm_compute. reflexivity.
Qed.
End t2.

Lemma val_mem_some : forall (m : word -> option byte) a (w : nat) v, val_mem tfibsegs m a w v ->
  forall j, 0 <= j < Z.of_nat w -> mbyte tfibsegs m (a + j) <> None.
Proof.
intros m a w v Hv j Hj. pose proof (Hv (Z.to_nat j) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. rewrite E. discriminate.
Qed.
Lemma val_mem_bytes : forall (m m' : word -> option byte) a a' (w : nat) v,
  (forall k, (k < w)%nat -> mbyte tfibsegs m' (a' + Z.of_nat k) = mbyte tfibsegs m (a + Z.of_nat k)) ->
  val_mem tfibsegs m a w v -> val_mem tfibsegs m' a' w v.
Proof. intros m m' a a' w v E Hv k Hk. rewrite (E k Hk). exact (Hv k Hk). Qed.
Lemma mbyte_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  H' (Z_to_bv 64 a) = H (Z_to_bv 64 a) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H H' m m' a E1 E2. unfold mbyte, mrestrict. rewrite E1, E2. reflexivity. Qed.
Lemma val_mem_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a (w : nat) v,
  (forall k, (k < w)%nat -> H' (Z_to_bv 64 (a + Z.of_nat k)) = H (Z_to_bv 64 (a + Z.of_nat k)) /\
                            m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H m) a w v -> val_mem tfibsegs (mrestrict H' m') a w v.
Proof.
intros H H' m m' a w v E. apply val_mem_bytes. intros k Hk. destruct (E k Hk) as [E1 E2]. exact (mbyte_xfer H H' m m' _ E1 E2).
Qed.

(* ===== Store's tail, composed: 0x6e96c to Store's ret ===== *)
Section ta. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variables (W : world tfibsegs) (rg : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (slot targ buf pk sp1 F std : Z) (ra0 v0 v1 v2 v3 v4 v5 : word) (tr : list Z).
#[local] Notation H := (w_H W).
#[local] Notation m0 := (mrestrict (w_H W) mem).
#[local] Notation n := (Z.of_nat (length tr)).
Hypotheses (G10 : getr rg 10%bv = Z_to_bv 64 slot) (G2 : getr rg 2%bv = Z_to_bv 64 sp1) (G8 : getr rg 8%bv = Z_to_bv 64 pk)
  (G9 : getr rg 9%bv = Z_to_bv 64 TFIB_STORE) (G18 : getr rg 18%bv = Z_to_bv 64 (n + 1))
  (G19 : getr rg 19%bv = Z_to_bv 64 targ) (G20 : getr rg 20%bv = Z_to_bv 64 n) (G21 : getr rg 21%bv = Z_to_bv 64 0).
Hypotheses (Hn : 1 <= n <= 255) (HFr : 0 <= F /\ F + n + 1 <= 2 ^ 20) (Hstd : 0 <= std /\ std + n + 1 < 2 ^ 20)
  (Hsl : 4096 <= slot /\ slot + 8 * (n + 1) < 2 ^ 62)
  (Hsp : kHighMemBeg <= sp1 /\ sp1 + 64 <= kHighMemEnd /\ sp1 mod 16 = 0)
  (Hpk : kHighMemBeg <= pk /\ pk + 8 <= kHighMemEnd) (Dpk : pk + 8 <= sp1 \/ sp1 + 64 <= pk)
  (Htg : kHighMemBeg <= targ /\ targ + 16 <= kHighMemEnd) (Hbf : kHighMemBeg <= buf /\ buf + 8 * n <= kHighMemEnd)
  (Dtg : zdisjoint (slot, 8 * (n + 1)) (targ, 16)) (Dbf : zdisjoint (slot, 8 * (n + 1)) (buf, 8 * n))
  (Dsp : zdisjoint (slot, 8 * (n + 1)) (pk, 8)) (Dss : zdisjoint (slot, 8 * (n + 1)) (TFIB_STORE, 32))
  (Dsf : zdisjoint (slot, 8 * (n + 1)) (sp1, 64)).
Hypotheses (Tb : val_mem tfibsegs m0 targ 8 buf)
  (Vbuf : forall i, (i < length tr)%nat -> val_mem tfibsegs m0 (buf + 8 * Z.of_nat i) 8 (nth i tr 0))
  (Psl : forall a, slot <= a < slot + 8 * (n + 1) -> apresent H mem a)
  (V0 : val_mem tfibsegs m0 sp1 8 F) (V8 : val_mem tfibsegs m0 (sp1 + 8) 8 (bv_unsigned v5))
  (V16 : val_mem tfibsegs m0 (sp1 + 16) 8 (bv_unsigned v4)) (V24 : val_mem tfibsegs m0 (sp1 + 24) 8 (bv_unsigned v3))
  (V32 : val_mem tfibsegs m0 (sp1 + 32) 8 (bv_unsigned v2)) (V40 : val_mem tfibsegs m0 (sp1 + 40) 8 (bv_unsigned v1))
  (V48 : val_mem tfibsegs m0 (sp1 + 48) 8 (bv_unsigned v0)) (V56 : val_mem tfibsegs m0 (sp1 + 56) 8 (bv_unsigned ra0))
  (VS : val_mem tfibsegs m0 (TFIB_STORE + 24) 4 std) (VP : val_mem tfibsegs m0 pk 8 0)
  (PP : forall k, 0 <= k < 8 -> apresent H mem (pk + k)).
Definition TPOST (W' : world tfibsegs) (c' : config) : Prop :=
  W' = W /\ exists rg3 m3 mat3, c' = mkCfg (mkst rg3 (v_jalr ra0 0) m3 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat3 md) /\
  getr rg3 10%bv = Z_to_bv 64 (F + 1) /\ getr rg3 1%bv = ra0 /\ getr rg3 2%bv = Z_to_bv 64 (sp1 + 64) /\
  getr rg3 8%bv = v0 /\ getr rg3 9%bv = v1 /\ getr rg3 18%bv = v2 /\ getr rg3 19%bv = v3 /\ getr rg3 20%bv = v4 /\ getr rg3 21%bv = v5 /\
  Forall (fun r => getr rg3 r = getr rg r) T2KEEP /\
  (forall a : word, ~ (slot <= bv_unsigned a < slot + 8 * (n + 1)) -> ~ (TFIB_STORE + 24 <= bv_unsigned a < TFIB_STORE + 28) ->
     ~ (pk <= bv_unsigned a < pk + 8) -> m3 a = mem a) /\
  mem_grows m0 (mrestrict H m3) /\
  val_mem tfibsegs (mrestrict H m3) (TFIB_STORE + 24) 4 (std + n + 1) /\ val_mem tfibsegs (mrestrict H m3) pk 8 0 /\
  val_mem tfibsegs (mrestrict H m3) slot 8 n /\
  (forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict H m3) (slot + 8 + 8 * Z.of_nat i) 8 (nth i tr 0)).
Lemma tail_all : SRr tfibsegs W (mkCfg (mkst rg (Z_to_bv 64 0x6e96c) mem (seg_rom tfibsegs)) md) TPOST.
Proof.
pose proof Dtg as Dtg'. pose proof Dbf as Dbf'. pose proof Dsp as Dsp'. pose proof Dss as Dss'. pose proof Dsf as Dsf'.
unfold zdisjoint in Dtg', Dbf', Dsp', Dss', Dsf'. cbn [fst snd] in Dtg', Dbf', Dsp', Dss', Dsf'.
(* the frame words stay off the slot: their bytes are unchanged by T1 *)
assert (FRK : forall o (w : nat) v, 0 <= o -> o + Z.of_nat w <= 64 -> val_mem tfibsegs m0 (sp1 + o) w v -> forall m2 : word -> option byte,
  (forall x : word, ~ (slot <= bv_unsigned x < slot + 8 * (n + 1)) -> m2 x = mem x) -> val_mem tfibsegs (mrestrict H m2) (sp1 + o) w v).
{ intros o w v Ho Hw Hv m2 IF. eapply (val_mem_xfer H H mem m2); [| exact Hv]. intros k Hk. split; [reflexivity|].
  apply IF. rewrite unsigned_lit_small by (clear - Ho Hw Hk Hsp; zlia). clear - Ho Hw Hk Dsf'. lia. }
eapply (@t1_ok _ _ W rg mem md slot targ buf n); try assumption.
- intros k Hk. pose proof (Vbuf (Z.to_nat (k / 8)) ltac:(apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_lt_upper_bound; lia)) as Vk.
  rewrite Z2Nat.id in Vk by (apply Z.div_pos; lia).
  replace (buf + k) with (buf + 8 * (k / 8) + k mod 8) by (pose proof (Z.div_mod k 8 ltac:(lia)); lia).
  apply (val_mem_some _ _ 8 _ Vk). pose proof (Z.mod_pos_bound k 8 ltac:(lia)). cbn. lia.
- intros rg2 m2 mat2 (GR & IF & IG & VH & IC). rewrite Forall_forall in GR.
  assert (GK : forall r : bv 5, In r T1REGS -> getr rg2 r = getr rg r) by exact GR.
  eapply (@t2_ok _ _ W rg2 m2 (with_vm_backing (m_vm_lazy md) mat2 md) sp1 pk (Z.of_nat (length tr)) F std ra0 v0 v1 v2 v3 v4 v5).
  all: try (rewrite (GK _ ltac:(cbn; tauto)); assumption).
  all: try assumption.
  + rewrite (GK 8%bv ltac:(cbn; tauto)). exact G8.
  + rewrite (GK 9%bv ltac:(cbn; tauto)). exact G9.
  + rewrite (GK 18%bv ltac:(cbn; tauto)). exact G18.
  + rewrite (GK 20%bv ltac:(cbn; tauto)). exact G20.
  + rewrite (GK 21%bv ltac:(cbn; tauto)). exact G21.
  + rewrite <- (Z.add_0_r sp1). apply (FRK 0 8%nat F); [lia | cbn; lia | rewrite Z.add_0_r; exact V0 | exact IF].
  + apply (FRK 8 8%nat _); [lia | cbn; lia | exact V8 | exact IF].
  + apply (FRK 16 8%nat _); [lia | cbn; lia | exact V16 | exact IF].
  + apply (FRK 24 8%nat _); [lia | cbn; lia | exact V24 | exact IF].
  + apply (FRK 32 8%nat _); [lia | cbn; lia | exact V32 | exact IF].
  + apply (FRK 40 8%nat _); [lia | cbn; lia | exact V40 | exact IF].
  + apply (FRK 48 8%nat _); [lia | cbn; lia | exact V48 | exact IF].
  + apply (FRK 56 8%nat _); [lia | cbn; lia | exact V56 | exact IF].
  + eapply (val_mem_xfer H H mem m2); [| exact VS]. intros k Hk. split; [reflexivity|].
    apply IF. rewrite unsigned_lit_small by (clear - Hk; unfold TFIB_STORE; lia). clear - Hk Dss'. lia.
  + eapply (val_mem_xfer H H mem m2); [| exact VP]. intros k Hk. split; [reflexivity|].
    apply IF. rewrite unsigned_lit_small by (clear - Hk Hpk; zlia). clear - Hk Dsp'. lia.
  + intros k Hk. apply (apresent_grows H mem m2 _ IG). exact (PP k Hk).
  + intros rg3 m3 mat3 (T10 & T1' & T2' & T8 & T9 & T18 & T19 & T20 & T21 & TK & TF & TG & TS & TP).
    rewrite wvb_collapse. split; [reflexivity|]. exists rg3, m3, mat3. split; [reflexivity|].
    do 9 (split; [assumption|]).
    split. { rewrite Forall_forall in TK |- *. intros r Hr. rewrite (TK r Hr). apply GK. revert Hr. unfold T2KEEP, T1REGS. cbn. tauto. }
    split. { intros a A1 A2 A3. rewrite (TF a A2 A3). apply IF. exact A1. }
    split. { exact (mem_grows_trans' _ _ _ IG TG). }
    split; [exact TS|]. split; [exact TP|]. split.
    * eapply (val_mem_xfer H H m2 m3); [| exact VH]. intros k Hk. split; [reflexivity|].
      apply TF; rewrite unsigned_lit_small by (clear - Hk Hsl; lia); clear - Hk Hsl Dss' Dsp'; unfold TFIB_STORE in *; lia.
    * intros i Hi. apply (val_mem_bytes (mrestrict H mem) (mrestrict H m3) (buf + 8 * Z.of_nat i)); [| exact (Vbuf i Hi)].
      intros k Hk. assert (Hi' : (Z.of_nat i < n)%Z) by lia.
      rewrite (mbyte_xfer H H m2 m3); [| reflexivity |].
      2:{ apply TF; rewrite unsigned_lit_small by (clear - Hk Hi' Hsl; lia); clear - Hk Hi' Hsl Dss' Dsp'; unfold TFIB_STORE in *; lia. }
      replace (slot + 8 + 8 * Z.of_nat i + Z.of_nat k) with (slot + 8 + (8 * Z.of_nat i + Z.of_nat k)) by lia.
      rewrite (IC (8 * Z.of_nat i + Z.of_nat k) ltac:(clear - Hk Hi'; lia)). f_equal. lia.
Qed.
End ta.


(* (s - 16 c) stays 16- and 8-aligned; stated with Z.mod_divide, not left to lia's mod handling. *)
Lemma mod16_sub : forall s c, s mod 16 = 0 -> (s - 16 * c) mod 16 = 0 /\ (s - 16 * c) mod 8 = 0.
Proof.
intros s c H. apply Z.mod_divide in H as [q Hq]; [|lia]. subst s.
replace (q * 16 - 16 * c) with ((q - c) * 16) by lia. split; [apply Z.mod_mul; lia|].
replace ((q - c) * 16) with ((2 * (q - c)) * 8) by lia. apply Z.mod_mul; lia.
Qed.
Lemma cs_lit : forall (r : bv 5) z, bv_unsigned r = z -> callee_saved z -> callee_saved (bv_unsigned r).
Proof. intros r z E H. rewrite E. exact H. Qed.
Lemma rp_at : forall (rg rg' : bvmap 5 word), regs_preserved rg rg' -> forall r : bv 5, callee_saved (bv_unsigned r) -> getr rg' r = getr rg r.
Proof. intros rg rg' HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hr. Qed.
Lemma bytes3_zero : forall v, 0 <= v < 2 ^ 24 -> v mod 256 = 0 -> (v / 256) mod 256 = 0 -> (v / 65536) mod 256 = 0 -> v = 0.
Proof.
intros v Hv H0 H1 H2.
assert (A2 : v / 65536 = 0) by (rewrite Z.mod_small in H2; [exact H2 | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]]).
assert (B2 : v < 65536) by (pose proof (Z.div_mod v 65536 ltac:(lia)); pose proof (Z.mod_pos_bound v 65536 ltac:(lia)); lia).
assert (A1 : v / 256 = 0) by (rewrite Z.mod_small in H1; [exact H1 | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]]).
assert (B1 : v < 256) by (pose proof (Z.div_mod v 256 ltac:(lia)); pose proof (Z.mod_pos_bound v 256 ltac:(lia)); lia).
rewrite Z.mod_small in H0 by lia. exact H0.
Qed.
Lemma le_byte_lo : forall v (k : nat), 0 <= v < 2 ^ 24 -> (k < 3)%nat ->
  YO0f.le_byte v 8 k mod 256 = (v / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
intros v k Hv Hk. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by lia.
rewrite Z.shiftr_div_pow2 by lia. apply Z.mod_mod. lia.
Qed.
Section zx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ss_off_X : forall (H : word -> bool) (m : word -> option byte) x v,
  x mod 4096 = 0 -> (forall i, 0 <= i < kStoreBlockSize -> aview tfibsegs H m (x + i) = Some 0) ->
  val_mem tfibsegs (mrestrict H m) TFIB_STORE 8 v -> 0 < v < 2 ^ 24 ->
  zdisjoint (x, kStoreBlockSize) (TFIB_STORE, 32).
Proof.
intros H m x v Hx Z0 Hv Hr. unfold zdisjoint. cbn [fst snd].
destruct (Z_le_gt_dec (x + kStoreBlockSize) TFIB_STORE) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (TFIB_STORE + 32) x) as [R|R]; [right; exact R|]. exfalso.
assert (Xin : x <= TFIB_STORE /\ TFIB_STORE + 8 <= x + kStoreBlockSize).
{ pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D. unfold TFIB_STORE, kStoreBlockSize in *. lia. }
assert (BZ : forall k : nat, (k < 3)%nat -> (v / 2 ^ (8 * Z.of_nat k)) mod 256 = 0).
{ intros k Hk. rewrite <- (le_byte_lo v k) by lia.
  pose proof (Z0 (TFIB_STORE + Z.of_nat k - x) ltac:(unfold kStoreBlockSize in *; lia)) as A.
  replace (x + (TFIB_STORE + Z.of_nat k - x)) with (TFIB_STORE + Z.of_nat k) in A by lia.
  unfold aview in A. rewrite (Hv k ltac:(lia)) in A. cbn [option_map] in A. injection A as A.
  rewrite Z_to_bv_unsigned in A. unfold bv_wrap in A. change (bv_modulus 8) with 256 in A. exact A. }
pose proof (BZ 0%nat ltac:(lia)) as B0. pose proof (BZ 1%nat ltac:(lia)) as B1. pose proof (BZ 2%nat ltac:(lia)) as B2.
cbn in B0, B1, B2. rewrite Z.div_1_r in B0.
pose proof (bytes3_zero v ltac:(lia) B0 B1 B2). lia.
Qed.
End zx.

Section cp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable layout_grow_kd : alayout -> alayout -> Prop.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis alloc_contract : AD3b.tfib_alloc_spec layout_grow_kd B.
Theorem tfib_store_ok : tfib_store_spec layout_grow_kd B.
Proof using HB alloc_contract.
intros W ly S regs mem md targ buf pk F std alloc tr. cbn zeta.
intros R10 R11 R12 Hra Tb Tn Tt Hn Vbuf HF0 HF1 Hs0 Hs1 Vtot Vblk HSB Vstd FU MP Ppk Pk1 Pk2 Pk3 Tg1 Tg2 Tg3 Bf1 Bf2 Bf3 Dpt Dpb Sp16 Lo Hi Bd1 Bd2 Pband.
assert (mnr_stk_ge : 0 <= MNR_STK) by (unfold MNR_STK; lia).
pose proof (ts_store B HB) as HSS. rewrite HSS in R10, Vtot, Vblk, Vstd, FU, MP.
unfold BIC_STK in *. unfold spZ in *.
set (n := Z.of_nat (length tr)) in *.
set (sp := bv_unsigned (getr regs 2%bv)) in *.
pose proof (u64_range (getr regs 2%bv)) as SR. fold sp in SR.
unfold SRr_refusable.
eapply (@head_walk _ _ W regs mem md targ buf pk n).
all: try fold sp.
1-7: assumption.
1: clear - Bf1 Bf2 Lo Hi Hn; zlia.
1: exact Sp16.
1: clear - Lo Bd1 mnr_stk_ge; zlia.
1: clear - Bd2 Hi; lia.
1: intros a Ha; apply Pband; clear - Ha mnr_stk_ge; lia.
1: split; clear - Tg1 Tg2 Lo Hi; lia.
1: clear - Tg3 mnr_stk_ge; lia.
1: split; clear - Pk1 Pk2 Lo Hi; lia.
1: clear - Pk3 mnr_stk_ge; lia.
1-2: assumption.
intros regs1 mem1 mat HFA. unfold HFACTS, INVH in HFA. fold sp in HFA.
destruct HFA as (A1 & A2 & A10 & A11 & A12 & A13 & A8 & A9 & A18 & A19 & A20 & A21 & AK & M0 & M8 & M16 & M24 & M32 & M40 & M48 & M56 & MP0 & INF & ING).
assert (SP1 : bv_unsigned (getr regs1 2%bv) = sp - 64) by (rewrite A2; apply unsigned_lit_small; clear - Lo Bd1 Bd2 Hi mnr_stk_ge; zlia).
(* memory below the stack (the image, the store cells, the mmap cells) is the head's input *)
assert (LOWK : forall a, 0 <= a < kHighMemBeg -> mem1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha. apply INF; rewrite unsigned_lit_small by (clear - Ha; zlia); clear - Ha Lo Bd1 Pk1 mnr_stk_ge; lia. }
assert (LOWV : forall a (w : nat) v, 0 <= a -> a + Z.of_nat w <= kHighMemBeg -> val_mem tfibsegs (mrestrict (w_H W) mem) a w v -> val_mem tfibsegs (mrestrict (w_H W) mem1) a w v).
{ intros a w v Ha Hw Hv. eapply (val_mem_frame (w_H W) mem mem1); [| exact Hv]. intros k Hk. apply LOWK. clear - Ha Hw Hk. lia. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md).
pose proof (alloc_contract W ly S regs1 mem1 md1 F (n + 1) (sp - 64) alloc) as HA. cbn zeta in HA. unfold spZ in HA. rewrite SP1 in HA.
assert (HA' : SRr_refusable W (mkCfg (mkst regs1 (Z_to_bv 64 tfib_A_StackStore_Alloc) mem1 (seg_rom tfibsegs)) md1)
  (AD3b.alloc_post layout_grow_kd B W ly S regs1 mem1 md1 F (n + 1) (sp - 64) alloc)).
{ apply HA; clear HA; unfold BIC_STK; rewrite ?HSS.
  - exact A10.
  - exact A11.
  - exact A12.
  - rewrite A1. unfold YK0s.ret_ok. vm_compute. reflexivity.
  - clear - Hn; lia.
  - exact HF0.
  - clear - HF1; lia.
  - apply LOWV; [unfold s_total, TFIB_STORE; lia | cbn; unfold s_total, TFIB_STORE, kHighMemBeg; lia | exact Vtot].
  - apply LOWV; [unfold s_block0, TFIB_STORE; lia | cbn; unfold s_block0, TFIB_STORE, kHighMemBeg; lia | exact Vblk].
  - exact HSB.
  - intros Z0. destruct (FU Z0) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    split. { apply LOWV; [unfold bi0_mtx, TFIB_STORE; lia | cbn; unfold bi0_mtx, TFIB_STORE, kHighMemBeg; lia | exact F1]. }
    split. { apply LOWV; [unfold ss_alloc, TFIB_STORE; lia | cbn; unfold ss_alloc, TFIB_STORE, kHighMemBeg; lia | exact F2]. }
    split. { destruct F3 as (C1 & C2 & C3 & (f & C4 & C5) & C6). unfold mnr_cells.
      split. { apply LOWV; [unfold MNR_PSC_GOT; lia | cbn; unfold MNR_PSC_GOT, kHighMemBeg; lia | exact C1]. }
      split. { apply LOWV; [unfold MNR_PSC; lia | cbn; unfold MNR_PSC, kHighMemBeg; lia | exact C2]. }
      split. { apply LOWV; [unfold MNR_CF_GOT; lia | cbn; unfold MNR_CF_GOT, kHighMemBeg; lia | exact C3]. }
      split. { exists f. split; [| exact C5]. apply LOWV; [unfold MNR_CF; lia | cbn; unfold MNR_CF, kHighMemBeg; lia | exact C4]. }
      apply LOWV; [unfold MNR_CF; lia | cbn; unfold MNR_CF, kHighMemBeg; lia | exact C6]. }
    split; [exact F4|]. split; [exact F5|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|].
    split; [exact F9|]. split; [exact F10|]. exact F11.
  - replace (sp - 64) with (sp - 16 * 4) by lia. exact (proj2 (mod16_sub sp 4 Sp16)).
  - clear - Bd1 mnr_stk_ge; lia.
  - clear - Bd2; lia.
  - right; lia.
  - intros k Hk. apply (apresent_grows (w_H W) mem mem1 _ ING). apply Pband. clear - Hk mnr_stk_ge; lia.
  - replace (sp - 64) with (sp - 16 * 4) by lia. exact (proj1 (mod16_sub sp 4 Sp16)).
  - exact Lo.
  - exact Hi.
  - clear - Bd1; lia.
  - clear - Bd2; lia.
  - intros a Ha. apply (apresent_grows (w_H W) mem mem1 _ ING). apply Pband. clear - Ha mnr_stk_ge; lia. }
clear HA.
eapply (SRr_refusable_bind W _ _ _ HA'). intros W2 c2 HW2 HP.
destruct HP as (x & ly' & regs' & mem' & md' & -> & AX). rewrite A1.
unfold AD3b.alloc_exit in AX. cbn zeta in AX. unfold spZ in AX. rewrite SP1, HSS in AX. unfold BIC_STK in AX.
destruct AX as (X10 & XRP & Xtot & Xidx & Xblk & XAP & ARM).
unfold s_total in Xtot. rewrite Z.add_0_r in Xtot.
assert (COM : (forall a : word, ~ (x <= bv_unsigned a < x + kStoreBlockSize) -> w_H W2 a = w_H W a) /\ (4096 <= x /\ x + kStoreBlockSize <= 2 ^ 47) /\
  zdisjoint (x, kStoreBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\ zdisjoint (x, kStoreBlockSize) (TFIB_STORE, 32) /\
  (forall a : word, ~ (sp - 64 - (16 + (32 + MNR_STK)) <= bv_unsigned a < sp - 64 + 8) -> ~ (x <= bv_unsigned a < x + kStoreBlockSize) ->
     ~ (TFIB_STORE <= bv_unsigned a < TFIB_STORE + 24) -> ~ (TFIB_STORE + 28 <= bv_unsigned a < TFIB_STORE + 32) -> mem' a = mem1 a) /\
  (forall a, x + 8 * F <= a < x + 8 * F + 8 * (n + 1) -> apresent (w_H W2) mem' a)).
{ destruct ARM as [(Z0 & PA & IA & DX & CL & P4 & WA & HW & SIO & MTK & MTK2 & PM1 & PM2 & PM3 & PM4 & VAL & VMTX & FRA & LY' & LLE & _) | (NZ & -> & -> & -> & [mat' Hmd] & FRM)].
  - split; [exact HW|]. split; [clear - IA; unfold in_app in IA; zlia|].
    assert (XK : zdisjoint (x, kStoreBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)).
    { apply (proj1 (Forall_forall _ _) DX). apply in_or_app; left. unfold ext_but_SB. apply in_or_app; right. apply in_or_app; right. cbn. tauto. }
    split; [exact XK|].
    assert (XS : zdisjoint (x, kStoreBlockSize) (TFIB_STORE, 32)).
    { apply (ss_off_X (w_H W2) mem' x (F + (n + 1))); [exact PA | intros i Hii; exact (proj2 (P4 i Hii)) | exact Xtot | clear - HF0 HF1 Hn; lia]. }
    split; [exact XS|]. split.
    + intros a B1 B2 B3 B4. apply FRA; [clear - B1 mnr_stk_ge; lia | exact B2 | unfold s_block0; clear - B3; lia | unfold bi0_mtx; clear - B4; lia | clear - B1 mnr_stk_ge; lia].
    + intros a Ha. replace a with (x + (a - x)) by lia. apply (proj1 (P4 (a - x) ltac:(clear - Ha HF0 HF1 Hn; unfold kStoreBlockSize; lia))).
  - destruct (MP NZ) as (IA & DK & DS & PS). split; [intros a _; reflexivity|]. split; [clear - IA; unfold in_app in IA; zlia|].
    split; [exact DK|]. split; [exact DS|]. split.
    + intros a B1 B2 B3 B4. apply FRM; clear - B1 B3 mnr_stk_ge; lia.
    + intros a Ha. apply XAP. apply (apresent_grows (w_H W) mem mem1 _ ING). apply PS. clear - Ha; lia. }
destruct COM as (HAG & XB & XK & XS & FRX & PSL).
pose proof XK as XK'. pose proof XS as XS'. unfold zdisjoint in XK', XS'. cbn [fst snd] in XK', XS'.
(* H agrees outside X (amendment 8); a value outside X moves from (W, m1) to (W2, m2) where m2 = m1 *)
assert (HXZ : forall a, 0 <= a < 2 ^ 64 -> (a < x \/ x + kStoreBlockSize <= a) -> w_H W2 (Z_to_bv 64 a) = w_H W (Z_to_bv 64 a)).
{ intros a Q0 Q1. apply HAG. rewrite unsigned_lit_small by exact Q0. clear - Q1. lia. }
assert (XFER : forall (m1 m2 : word -> option byte) a (w : nat) v, 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  (a + Z.of_nat w <= x \/ x + kStoreBlockSize <= a) ->
  (forall k, (k < w)%nat -> m2 (Z_to_bv 64 (a + Z.of_nat k)) = m1 (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict (w_H W) m1) a w v -> val_mem tfibsegs (mrestrict (w_H W2) m2) a w v).
{ intros m1 m2 a w v Q0 Q1 Q2 E V. apply (val_mem_xfer (w_H W) (w_H W2) m1 m2); [| exact V].
  intros k Hk. split; [apply HXZ; clear - Q0 Q1 Q2 Hk; lia | exact (E k Hk)]. }
(* the stack outside Store's band and the pack cell: unchanged since Store's entry *)
assert (BANDK : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (sp - (64 + 16 + (32 + MNR_STK)) <= a < sp) -> ~ (pk <= a < pk + 8) ->
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a S1 S2 S3. assert (A0 : 0 <= a < 2 ^ 64) by (clear - S1 Lo Hi; zlia).
  rewrite FRX by (rewrite unsigned_lit_small by exact A0; clear - S1 S2 XK' Lo mnr_stk_ge; unfold TFIB_STORE, kHighMemBeg in *; lia).
  apply INF; rewrite unsigned_lit_small by exact A0; clear - S2 S3 mnr_stk_ge; lia. }
assert (LOW24 : forall a, TFIB_STORE + 24 <= a < TFIB_STORE + 28 -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a S1. rewrite FRX by (rewrite unsigned_lit_small by (clear - S1; unfold TFIB_STORE in *; lia); clear - S1 XS' Lo Bd1 mnr_stk_ge; unfold TFIB_STORE, kHighMemBeg in *; lia).
  apply LOWK. clear - S1; unfold TFIB_STORE, kHighMemBeg in *; lia. }
assert (FRW : forall a, sp - 64 + 8 <= a < sp -> mem' (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
{ intros a S1. assert (A0 : 0 <= a < 2 ^ 64) by (clear - S1 Bd1 Bd2 Lo Hi mnr_stk_ge; zlia).
  apply FRX; rewrite unsigned_lit_small by exact A0; clear - S1 XK' Lo Bd1 Bd2 mnr_stk_ge; unfold TFIB_STORE, kHighMemBeg in *; lia. }
assert (PKW : forall k, 0 <= k < 8 -> mem' (Z_to_bv 64 (pk + k)) = mem1 (Z_to_bv 64 (pk + k))).
{ intros k Hk. assert (A0 : 0 <= pk + k < 2 ^ 64) by (clear - Hk Pk1 Pk2 Lo Hi; zlia).
  apply FRX; rewrite unsigned_lit_small by exact A0; clear - Hk Pk1 Pk2 Pk3 XK' Lo mnr_stk_ge; unfold TFIB_STORE, kHighMemBeg in *; lia. }
assert (RP : forall r : bv 5, callee_saved (bv_unsigned r) -> getr regs' r = getr regs1 r) by exact (rp_at regs1 regs' XRP).
eapply SRr_bind.
{ eapply (@tail_all _ _ W2 regs' mem' md' (x + 8 * F) targ buf pk (sp - 64) F std (getr regs 1%bv) (getr regs 8%bv) (getr regs 9%bv)
    (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv) tr).
  all: fold n.
  - exact X10.
  - rewrite (RP 2%bv (cs_lit (2%bv : bv 5) 2 eq_refl ltac:(unfold callee_saved; lia))). exact A2.
  - rewrite (RP 8%bv (cs_lit (8%bv : bv 5) 8 eq_refl ltac:(unfold callee_saved; lia))). exact A8.
  - rewrite (RP 9%bv (cs_lit (9%bv : bv 5) 9 eq_refl ltac:(unfold callee_saved; lia))). exact A9.
  - rewrite (RP 18%bv (cs_lit (18%bv : bv 5) 18 eq_refl ltac:(unfold callee_saved; lia))). exact A18.
  - rewrite (RP 19%bv (cs_lit (19%bv : bv 5) 19 eq_refl ltac:(unfold callee_saved; lia))). exact A19.
  - rewrite (RP 20%bv (cs_lit (20%bv : bv 5) 20 eq_refl ltac:(unfold callee_saved; lia))). exact A20.
  - rewrite (RP 21%bv (cs_lit (21%bv : bv 5) 21 eq_refl ltac:(unfold callee_saved; lia))). exact A21.
  - exact Hn.
  - split; [exact HF0 | exact HF1].
  - split; [exact Hs0 | exact Hs1].
  - clear - XB HF0 HF1 Hn. unfold kStoreBlockSize in XB. lia.
  - split; [clear - Lo Bd1 mnr_stk_ge; lia|]. split; [clear - Bd2 Hi; lia|]. replace (sp - 64) with (sp - 16 * 4) by lia. exact (proj1 (mod16_sub sp 4 Sp16)).
  - split; clear - Pk1 Pk2 Lo Hi; lia.
  - clear - Pk3 mnr_stk_ge; lia.
  - split; clear - Tg1 Tg2 Lo Hi; lia.
  - split; clear - Bf1 Bf2 Lo Hi; lia.
  - unfold zdisjoint; cbn [fst snd]. clear - XK' XB HF0 HF1 Hn Tg1 Tg2. unfold kStoreBlockSize in *. lia.
  - unfold zdisjoint; cbn [fst snd]. clear - XK' XB HF0 HF1 Hn Bf1 Bf2. unfold kStoreBlockSize in *. lia.
  - unfold zdisjoint; cbn [fst snd]. clear - XK' XB HF0 HF1 Hn Pk1 Pk2. unfold kStoreBlockSize in *. lia.
  - unfold zdisjoint; cbn [fst snd]. clear - XS' XB HF0 HF1 Hn. unfold kStoreBlockSize in *. lia.
  - unfold zdisjoint; cbn [fst snd]. clear - XK' XB HF0 HF1 Hn Bd1 Bd2 mnr_stk_ge. unfold kStoreBlockSize in *. lia.
  - unfold zdisjoint in Dpt; cbn [fst snd] in Dpt.
    apply (XFER mem mem' targ 8%nat buf); [clear - Tg1 Lo; zlia | clear - Tg2 Hi; zlia | clear - Tg1 Tg2 XK'; lia | | exact Tb].
    intros k Hk. apply BANDK; clear - Hk Tg1 Tg2 Tg3 Dpt mnr_stk_ge; lia.
  - intros i Hii. unfold zdisjoint in Dpb; cbn [fst snd] in Dpb.
    apply (XFER mem mem' (buf + 8 * Z.of_nat i) 8%nat (nth i tr 0));
      [clear - Bf1 Lo; zlia | clear - Hii Bf2 Hi; zlia | clear - Hii Bf1 Bf2 XK'; lia | | exact (Vbuf i Hii)].
    intros k Hk. apply BANDK; clear - Hii Hk Bf1 Bf2 Bf3 Dpb mnr_stk_ge; lia.
  - exact PSL.
  - exact Xidx.
  - replace (sp - 64 + 8) with (sp - 56) by lia.
    apply (XFER mem1 mem' (sp - 56) 8%nat _); [clear - Lo Bd1 mnr_stk_ge; zlia | clear - Bd2 Hi; zlia | clear - Bd1 Bd2 XK' mnr_stk_ge; lia | | exact M8].
    intros k Hk. apply FRW. clear - Hk; lia.
  - replace (sp - 64 + 16) with (sp - 48) by lia.
    apply (XFER mem1 mem' (sp - 48) 8%nat _); [clear - Lo Bd1 mnr_stk_ge; zlia | clear - Bd2 Hi; zlia | clear - Bd1 Bd2 XK' mnr_stk_ge; lia | | exact M16].
    intros k Hk. apply FRW. clear - Hk; lia.
  - replace (sp - 64 + 24) with (sp - 40) by lia.
    apply (XFER mem1 mem' (sp - 40) 8%nat _); [clear - Lo Bd1 mnr_stk_ge; zlia | clear - Bd2 Hi; zlia | clear - Bd1 Bd2 XK' mnr_stk_ge; lia | | exact M24].
    intros k Hk. apply FRW. clear - Hk; lia.
  - replace (sp - 64 + 32) with (sp - 32) by lia.
    apply (XFER mem1 mem' (sp - 32) 8%nat _); [clear - Lo Bd1 mnr_stk_ge; zlia | clear - Bd2 Hi; zlia | clear - Bd1 Bd2 XK' mnr_stk_ge; lia | | exact M32].
    intros k Hk. apply FRW. clear - Hk; lia.
  - replace (sp - 64 + 40) with (sp - 24) by lia.
    apply (XFER mem1 mem' (sp - 24) 8%nat _); [clear - Lo Bd1 mnr_stk_ge; zlia | clear - Bd2 Hi; zlia | clear - Bd1 Bd2 XK' mnr_stk_ge; lia | | exact M40].
    intros k Hk. apply FRW. clear - Hk; lia.
  - replace (sp - 64 + 48) with (sp - 16) by lia.
    apply (XFER mem1 mem' (sp - 16) 8%nat _); [clear - Lo Bd1 mnr_stk_ge; zlia | clear - Bd2 Hi; zlia | clear - Bd1 Bd2 XK' mnr_stk_ge; lia | | exact M48].
    intros k Hk. apply FRW. clear - Hk; lia.
  - replace (sp - 64 + 56) with (sp - 8) by lia.
    apply (XFER mem1 mem' (sp - 8) 8%nat _); [clear - Lo Bd1 mnr_stk_ge; zlia | clear - Bd2 Hi; zlia | clear - Bd1 Bd2 XK' mnr_stk_ge; lia | | exact M56].
    intros k Hk. apply FRW. clear - Hk; lia.
  - unfold bi0_stored in Vstd.
    apply (XFER mem mem' (TFIB_STORE + 24) 4%nat std); [unfold TFIB_STORE; lia | unfold TFIB_STORE; lia | clear - XS'; unfold TFIB_STORE in *; lia | | exact Vstd].
    intros k Hk. apply LOW24. clear - Hk; lia.
  - apply (XFER mem1 mem' pk 8%nat 0); [clear - Pk1 Lo; zlia | clear - Pk2 Hi; zlia | clear - Pk1 Pk2 XK'; lia | | exact MP0].
    intros k Hk. apply PKW. clear - Hk; lia.
  - intros k Hk. apply XAP. apply (apresent_grows (w_H W) mem mem1 _ ING). exact (Ppk k Hk). }
intros W3 c3 _ (-> & rg3 & m3 & mat3 & -> & T10 & T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & TK & TF & TG & TS & TP & TH & TW).
apply SRr_ret. fold n in TF, TS, TP, TH, TW.
unfold store_post. exists x, ly', rg3, m3, (with_vm_backing (m_vm_lazy md') mat3 md').
split. { unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
unfold store_exit. cbn zeta. unfold spZ, BIC_STK, bi0_stored, bi0_mtx, s_total. fold sp. rewrite HSS. fold n.
assert (TFA : forall a, ~ (x + 8 * F <= a < x + 8 * F + 8 * (n + 1)) -> ~ (TFIB_STORE + 24 <= a < TFIB_STORE + 28) -> ~ (pk <= a < pk + 8) ->
  0 <= a < 2 ^ 64 -> m3 (Z_to_bv 64 a) = mem' (Z_to_bv 64 a)).
{ intros a B1 B2 B3 B4. apply TF; rewrite unsigned_lit_small by exact B4; assumption. }
split; [exact T10|].
split.
{ rewrite Forall_forall in TK, AK. apply regs_preserved_intro.
  - rewrite T2. replace (sp - 64 + 64) with sp by lia. unfold sp. apply Z_to_bv_bv_unsigned.
  - rewrite (TK 3%bv ltac:(cbn; tauto)), (RP 3%bv (cs_lit (3%bv : bv 5) 3 eq_refl ltac:(unfold callee_saved; lia))). apply AK. cbn; tauto.
  - rewrite (TK 4%bv ltac:(cbn; tauto)), (RP 4%bv (cs_lit (4%bv : bv 5) 4 eq_refl ltac:(unfold callee_saved; lia))). apply AK. cbn; tauto.
  - exact T8.
  - exact T9.
  - exact T18.
  - exact T19.
  - exact T20.
  - exact T21.
  - rewrite (TK 22%bv ltac:(cbn; tauto)), (RP 22%bv (cs_lit (22%bv : bv 5) 22 eq_refl ltac:(unfold callee_saved; lia))). apply AK. cbn; tauto.
  - rewrite (TK 23%bv ltac:(cbn; tauto)), (RP 23%bv (cs_lit (23%bv : bv 5) 23 eq_refl ltac:(unfold callee_saved; lia))). apply AK. cbn; tauto.
  - rewrite (TK 24%bv ltac:(cbn; tauto)), (RP 24%bv (cs_lit (24%bv : bv 5) 24 eq_refl ltac:(unfold callee_saved; lia))). apply AK. cbn; tauto.
  - rewrite (TK 25%bv ltac:(cbn; tauto)), (RP 25%bv (cs_lit (25%bv : bv 5) 25 eq_refl ltac:(unfold callee_saved; lia))). apply AK. cbn; tauto.
  - rewrite (TK 26%bv ltac:(cbn; tauto)), (RP 26%bv (cs_lit (26%bv : bv 5) 26 eq_refl ltac:(unfold callee_saved; lia))). apply AK. cbn; tauto.
  - rewrite (TK 27%bv ltac:(cbn; tauto)), (RP 27%bv (cs_lit (27%bv : bv 5) 27 eq_refl ltac:(unfold callee_saved; lia))). apply AK. cbn; tauto. }
split.
{ rewrite Z.add_0_r. replace (F + n + 1) with (F + (n + 1)) by lia.
  eapply (val_mem_frame (w_H W2) mem' m3); [| exact Xtot]. intros k Hk.
  apply TFA; clear - Hk XS' XB HF0 HF1 Hn Pk1 Lo; unfold TFIB_STORE, kHighMemBeg, kStoreBlockSize in *; lia. }
split.
{ eapply (val_mem_frame (w_H W2) mem' m3); [| exact Xblk]. intros k Hk.
  apply TFA; clear - Hk XS' XB HF0 HF1 Hn Pk1 Lo; unfold s_block0, TFIB_STORE, kHighMemBeg, kStoreBlockSize in *; lia. }
split; [exact TS|]. split; [exact TP|]. split; [exact TH|].
split; [exact TW|].
split.
{ intros a Ha. apply (apresent_grows (w_H W2) mem' m3 a TG). apply XAP. exact (apresent_grows (w_H W) mem mem1 a ING Ha). }
destruct ARM as [(Z0 & PA & IA & DX & CL & P4 & WA & HW & SIO & MTK & MTK2 & PM1 & PM2 & PM3 & PM4 & VAL & VMTX & FRA & LY' & LLE & VMF) | (NZ & Ex & Ely & EW & [mat' Hmd] & FRM)].
- left.
  split; [exact Z0|]. split; [exact PA|]. split; [exact IA|]. split; [exact DX|]. split; [exact CL|].
  split.
  { intros i Hii. destruct (P4 i Hii) as [P4a P4b]. split; [exact (apresent_grows (w_H W2) mem' m3 _ TG P4a)|].
    intros Hs. rewrite (aview_same (w_H W2) mem' m3); [exact P4b|].
    apply TFA; clear - Hii Hs XS' XK' XB Pk1 Pk2; unfold TFIB_STORE, kStoreBlockSize in *; lia. }
  split; [exact WA|]. split; [exact HW|].
  split.
  { unfold md1 in SIO. revert SIO. unfold same_io. cbn. intros (S1 & S2 & S3 & S4). repeat split; congruence. }
  split; [exact MTK|].
  split; [intros e He; exact (MTK2 e He)|].
  split.
  { destruct PM1 as [mat2 EM2]. exists mat3. rewrite EM2, wvb_collapse. unfold md1. rewrite nr_wvb, wvb_collapse. reflexivity. }
  split. { rewrite m_vmmaps_wvb, PM2. unfold md1. apply mm_vmmaps_wvb. }
  split. { rewrite m_vm_lazy_wvb, PM3. unfold md1. rewrite m_vm_lazy_wvb. reflexivity. }
  split. { rewrite eu_wvb, PM4. unfold md1. apply eu_wvb. }
  split.
  { eapply (val_mem_frame (w_H W2) mem' m3); [| exact VAL]. intros k Hk.
    apply TFA; clear - Hk XS' XB HF0 HF1 Hn Pk1 Lo; unfold ss_alloc, TFIB_STORE, kHighMemBeg, kStoreBlockSize in *; lia. }
  split.
  { eapply (val_mem_frame (w_H W2) mem' m3); [| exact VMTX]. intros k Hk.
    apply TFA; clear - Hk XS' XB HF0 HF1 Hn Pk1 Lo; unfold bi0_mtx, TFIB_STORE, kHighMemBeg, kStoreBlockSize in *; lia. }
  split; [| split; [exact LY' | split; [exact LLE | unfold md1 in VMF; rewrite m_vmmaps_wvb in VMF; exact VMF]]].
  intros a B1 B2 B3 B4. pose proof (u64_range a) as AR.
  rewrite <- (Z_to_bv_bv_unsigned 64 a).
  rewrite TFA by (clear - B2 B3 B4 XB HF0 HF1 Hn AR; unfold kStoreBlockSize in *; lia).
  rewrite (Z_to_bv_bv_unsigned 64 a).
  rewrite FRX by (clear - B1 B2 B3 mnr_stk_ge; lia).
  apply INF; clear - B1 B4 mnr_stk_ge; lia.
- right. subst x ly' W2 md'. split; [exact NZ|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { exists mat3. unfold md1. rewrite !wvb_collapse. reflexivity. }
  intros a B1 B2 B3 B4 B5. pose proof (u64_range a) as AR.
  rewrite <- (Z_to_bv_bv_unsigned 64 a).
  rewrite TFA by (clear - B3 B4 B5 AR; lia).
  rewrite (Z_to_bv_bv_unsigned 64 a).
  rewrite FRM by (clear - B1 B2 mnr_stk_ge; lia).
  apply INF; clear - B1 B4 mnr_stk_ge; lia.
Qed.
End cp.
