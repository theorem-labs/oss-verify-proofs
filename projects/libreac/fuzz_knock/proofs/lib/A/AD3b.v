(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written by a Theorem Labs lane (the prover of piece S2 of fuzz_knock's StackDepot first-use chain, for another Theorem Labs lane): the statement of __sanitizer::StackStore::Alloc (knock asan 0x6ea18, 77 insns) for store block 0, on the call of knock's first post-main StackDepotPut that creates the block (it calls StackStore::BlockInfo::Create 0x6f400, piece S3, consumed here as the Section hypothesis create_contract: S3's tfib_blockinfo_create_spec, Required from lib/A/AD3c.v) and on the later calls that find the block mapped. Cell-level shape frozen by a Theorem Labs lane: no kernel ARm, because Alloc bumps s_total before it calls Create.
   a Theorem Labs lane approved this statement; amendment 1 brought S3's md_takes (positive size) and Create's premises md_takes md (as_store B, 32) and kHighMemBeg <= ly_stk_lo ly (carried in Alloc's first-use pre); amendment 3 added 0 <= ly_SB ly < 2 ^ 64 to Alloc's pre; amendments 5 and 6 (S3: ext_but_SB lists the nodes map only once mapped; Create's frame excludes the mutex word) and 7 (the VM budget premise eager_used md + A_bytes (w_A W) + kStoreBlockSize <= vm_limit (m_vmmaps md), also in Alloc's first-use pre) are carried from S3. The refused arm is excluded by premise (md_room, carried from Create's pre).
   Amendment 8 (a Theorem Labs lane): S3's statement is Required from AD3c.v (which Require-Exports a Theorem Labs lane's AD3d.v), not copied; S3's Section variable mnr_stk and hypothesis mnr_stk_ge are gone (BIC_STK = 32 + MNR_STK = 136); Alloc's first-use pre gains Create's new premises YK0g.ivs_wf (vm_maps (m_vmmaps md)), YM05.ceil_of_top (alloc_top (m_vmmaps md)) and Forall (md_takes md) mnr_cell_extents (ly_stk_hi ly <= kHighMemEnd was already a premise); the first-use post states the exposure as S3 does (w_A W' = (x, x + kStoreBlockSize) :: w_A W, w_H W' = w_H W outside X, replacing w_H W' = w_H W) with S3's model clauses, and P6 is ly' = set_ly_SB ly x /\ layout_grow_kd ly ly' (S3's placeholder relation, replacing layout_le_kd (length (st_secs S)) ly ly').
   Amendment 8 note 6 (S3, AD3c.v): the first-use post also states S3's exact model after the call, over Alloc's entry model md: md' is the NORESERVE grant YK0x.mmap_model_noreserve x kStoreBlockSize md up to the materialization wrapper, m_vmmaps md' = m_vmmaps (YK0v.mmap_model x kStoreBlockSize md), m_vm_lazy md' = (x, kStoreBlockSize) :: m_vm_lazy md, eager_used md' = eager_used md.
   The proof below the statement is Qed (tfib_alloc_ok): both arms walked over tfibtbl_rtB, the first-use arm through create_contract at 0x6eb28.
   Amendment 11 (a Theorem Labs lane): the first-use arm's last conjunct states X fresh against every map of Alloc's entry model md (Forall over vm_maps (m_vmmaps md)), from S3's new last conjunct P7 at Create's call; Alloc's steps before the call change the model only by with_vm_backing, which keeps m_vmmaps (m_vmmaps_wvb).
   rule 24: proves function StackStore::Alloc (reuse search: see (internal path)). *)
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
(* S3's statement and the S4 contract it consumes, by name (amendment 8): AD3c Require-Exports a Theorem Labs lane's AD3d. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AD3c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* knock's Alloc (A image, sha256 61768cf4739b..., read from the packed base c8557374's Asan_seg_001.hex; the AU twin's
   numbers come from AU's own tables, which differ from A's at least in the page-size GOT slot):
     0x6ea18  addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp); a5 := count; a1 := this
     0x6ea2c  amoadd.d s0,a5,(a0)          start := s_total; s_total += count (BEFORE Create is called)
     0x6ea40  start >> 20 <> (start + count - 1) >> 20 -> 0x6ea90 straddle / retry (reads and writes pack)
     0x6ea48  start >> 32 <> 0 -> return 0
     0x6ea60  sd s0,0(a2)                  *idx := start
     0x6ea6c  ld a0,16(this + 16 * (start >> 20))   data_ of blocks_[start >> 20]
     0x6ea70  data_ = 0 -> 0x6eb24: a0 := &blocks_[0]; jal 0x6f400 (BlockInfo::Create, a1 = this, ra = 0x6eb2c,
              s0 = start live across the call); 0x6eb2c j 0x6ea74
     0x6ea74  return data_ + 8 * (start mod 2^20); restore ra, s0; ret
   With F + count <= 2^20 (block 0, as the depot model's universe bound gives) the straddle path is never taken, so pack
   (a3) is never read or written. Alloc calls only Create and CheckFailed 0x6a0b0 (unreached here); it does not call
   MmapNoReserveOrDie, which is reached only inside Create. After Create returns Alloc writes no memory. *)

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Section kd.
(* The layout step, as S3 states it (AD3c.v:162-165, amendment 8): the first Put's growth is the placeholder relation
   layout_grow_kd; AD3j's kd_inst instantiates it with layout_grow (YG0f.v:99). Satisfiable: fun _ _ => True. *)
Variable layout_grow_kd : alayout -> alayout -> Prop.

(* ===== S2: StackStore::Alloc(this = as_store B, count, idx = idxp, pack) for block 0. ===== *)
Variable B : asyms.

(* Alloc's exit, for the call with s_total = F before and the block-0 data_ cell holding ly_SB ly before (a Theorem Labs lane's
   knock-branch depot_cells: 0 while the store block is not mapped, ly_SB ly once it is).
   Both arms: return to ra with a0 = x + 8 * F, callee-saved registers kept, and the EXACT depot cells after the call:
   s_total = F + count, *idx = F, s_block0 = x; presence only grows. stored_ (SS + 24 .. 28) and pack are untouched
   (by the frame).
   First use (ly_SB ly = 0): S3's post carried: P2-P4 for X = (x, kStoreBlockSize); exposure as S3 and S4 state it
   (amendment 8: X joins w_A, w_H unchanged outside X); no I/O, the model takes X and keeps what it took, and the model
   after the call is exactly S3's (amendment 8 note 6: the NORESERVE grant of X on Alloc's entry model, up to the
   materialization wrapper, which Alloc's own steps re-wrap with the same lazy list), allocated_ = alloc + 0x800000, the mutex word 0, frame = Alloc's band, X, SS + [0, 24), the mutex
   word SS + [28, 32) (amendment 6's rule: Create writes it) and the idx cell; P6 at cell level: ly' = set_ly_SB ly x and
   layout_grow_kd ly ly' (S3's placeholder, amendment 8); X is fresh against every map of Alloc's entry model (S3's P7,
   amendment 11: Alloc's steps before the call change the model only by materialization, which keeps m_vmmaps).
   No kernel ARm.
   Later calls (ly_SB ly <> 0): x = ly_SB ly, the layout, world and model (but for materialization) are unchanged,
   frame = Alloc's 16-byte frame, s_total and the idx cell. *)
Definition alloc_exit (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (F cnt idxp alloc : Z)
  (x : Z) (ly' : alayout) (W' : world tfibsegs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  let sp := spZ regs in let SS := as_store B in let m' := mrestrict (w_H W') mem' in
  getr regs' 10 = Z_to_bv 64 (x + 8 * F) /\ regs_preserved regs regs' /\
  val_mem tfibsegs m' (SS + s_total) 8 (F + cnt) /\ val_mem tfibsegs m' idxp 8 F /\
  val_mem tfibsegs m' (SS + s_block0) 8 x /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
  ( (ly_SB ly = 0 /\
     YG0f.page_aligned x /\ in_app x kStoreBlockSize /\
     Forall (zdisjoint (x, kStoreBlockSize)) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) /\
     (forall a, aclient_byte B ly S a -> ~ in_zr a (x, kStoreBlockSize)) /\
     (forall i, 0 <= i < kStoreBlockSize ->
        apresent (w_H W') mem' (x + i) /\ aview tfibsegs (w_H W') mem' (x + i) = Some 0) /\
     w_A W' = (x, x + kStoreBlockSize) :: w_A W /\
     (forall a : word, ~ (x <= bv_unsigned a < x + kStoreBlockSize) -> w_H W' a = w_H W a) /\
     same_io md md' /\ md_takes md' (x, kStoreBlockSize) /\ (forall e, md_takes md e -> md_takes md' e) /\
     (exists mat, md' = with_vm_backing
         (m_vm_lazy (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md)) mat
         (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md)) /\
     m_vmmaps md' = m_vmmaps (YK0v.mmap_model (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md) /\
     m_vm_lazy md' = (Z_to_bv 64 x, Z_to_bv 64 kStoreBlockSize) :: m_vm_lazy md /\
     eager_used md' = eager_used md /\
     val_mem tfibsegs m' (SS + ss_alloc) 8 ((alloc + kStoreBlockSize) mod 2 ^ 64) /\
     val_mem tfibsegs m' (SS + bi0_mtx) 4 0 /\
     (forall a : word, ~ (sp - (16 + BIC_STK) <= bv_unsigned a < sp) -> ~ (x <= bv_unsigned a < x + kStoreBlockSize) ->
        ~ (SS <= bv_unsigned a < SS + s_block0 + 8) -> ~ (SS + bi0_mtx <= bv_unsigned a < SS + bi0_mtx + 4) ->
        ~ (idxp <= bv_unsigned a < idxp + 8) -> mem' a = mem a) /\
     ly' = set_ly_SB ly x /\ layout_grow_kd ly ly' /\
     Forall (fun q => zdisjoint (x, kStoreBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_maps (m_vmmaps md)))
  \/
    (ly_SB ly <> 0 /\ x = ly_SB ly /\ ly' = ly /\ W' = W /\
     (exists mat, md' = with_vm_backing (m_vm_lazy md) mat md) /\
     (forall a : word, ~ (sp - 16 <= bv_unsigned a < sp) -> ~ (SS <= bv_unsigned a < SS + 8) ->
        ~ (idxp <= bv_unsigned a < idxp + 8) -> mem' a = mem a))).

Definition alloc_post (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (F cnt idxp alloc : Z) (W' : world tfibsegs) (c' : config) : Prop :=
  exists x ly' regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
    alloc_exit W ly S regs mem md F cnt idxp alloc x ly' W' regs' mem' md'.

(* PRE (cell level): the arguments; s_total = F with the run staying in block 0; the block-0 data_ cell = ly_SB ly with
   0 <= ly_SB ly < 2^64 (amendment 3: otherwise a nonzero ly_SB ly with zero low 64 bits stores 0 and Alloc calls
   Create although the mapped arm is claimed); on first use (ly_SB ly = 0) also what Create's statement asks at its
   entry, which Alloc does not change before the call: the mutex word 0, allocated_ = alloc, mnr_cells, room for the
   grant (md_room), the budget, the model map list well formed (ivs_wf), alloc_ceiling as alloc_top's page floor
   (ceil_of_top), that the model takes the callee's two post-ecall cells (mnr_cell_extents, amendment 8), the store
   cells (md_takes md (SS, 32), amendment 1) and every extent P3 names (all of them read m_vmmaps only, which Alloc's
   run keeps); the idx cell in the stack and off Alloc's band;
   the stack band of 16 + BIC_STK bytes in high memory (kHighMemBeg <= ly_stk_lo ly: no layout_ok here, since lo_app
   fails while ly_SB ly = 0; it keeps the band, the idx cell and the store cells apart).
   Discharge at Put's call site (Store passes them on): F + cnt <= 2 ^ 20 (the run stays in block 0) is a Theorem Labs lane's
   depot_alloc_one_block (lib/A/AD3i.v:279, sha256 a0db88d39624; internal record), from TfibSyms B,
   Wf (as_universe B) S, In tr (as_universe B) and F <= 32 + depot_frames S, with cnt = length tr + 1;
   0 <= ly_SB ly < 2^64 is 0 while the store block is unmapped
   (a Theorem Labs lane's encoding) and, once mapped, knock-branch lo_app gives in_app (ly_SB ly) kStoreBlockSize, so
   4096 <= ly_SB ly < ASAN_CEIL; the first-use premises Create shares are cited in AD3c.v's header (S3);
   ly_stk_hi ly <= kHighMemEnd, which amendment 8 adds to Create's pre, was already a premise here. *)
Definition tfib_alloc_spec : Prop :=
  forall (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (F cnt idxp alloc : Z),
  let H := w_H W in let m := mrestrict H mem in let sp := spZ regs in let SS := as_store B in
  getr regs 10 = Z_to_bv 64 SS -> getr regs 11 = Z_to_bv 64 cnt -> getr regs 12 = Z_to_bv 64 idxp ->
  YK0s.ret_ok (getr regs 1) ->
  1 <= cnt <= 256 -> 0 <= F -> F + cnt <= 2 ^ 20 ->
  val_mem tfibsegs m (SS + s_total) 8 F -> val_mem tfibsegs m (SS + s_block0) 8 (ly_SB ly) -> 0 <= ly_SB ly < 2 ^ 64 ->
  (ly_SB ly = 0 ->
     val_mem tfibsegs m (SS + bi0_mtx) 4 0 /\ val_mem tfibsegs m (SS + ss_alloc) 8 alloc /\ mnr_cells m /\
     md_room md kStoreBlockSize /\ eager_used md + A_bytes (w_A W) + kStoreBlockSize <= vm_limit (m_vmmaps md) /\
     YK0g.ivs_wf (vm_maps (m_vmmaps md)) /\ YM05.ceil_of_top (alloc_top (m_vmmaps md)) /\
     Forall (md_takes md) mnr_cell_extents /\
     md_takes md (SS, 32) /\
     Forall (md_takes md) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) /\
     (forall a, aclient_byte B ly S a -> md_takes md (a, 1))) ->
  idxp mod 8 = 0 -> ly_stk_lo ly <= idxp -> idxp + 8 <= ly_stk_hi ly ->
  (idxp + 8 <= sp - (16 + BIC_STK) \/ sp <= idxp) -> (forall k, 0 <= k < 8 -> apresent H mem (idxp + k)) ->
  sp mod 16 = 0 -> kHighMemBeg <= ly_stk_lo ly -> ly_stk_hi ly <= kHighMemEnd ->
  ly_stk_lo ly <= sp - (16 + BIC_STK) -> sp <= ly_stk_hi ly ->
  (forall a, sp - (16 + BIC_STK) <= a < sp -> apresent H mem a) ->
  SRr_refusable W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_StackStore_Alloc) mem (seg_rom tfibsegs)) md)
    (alloc_post W ly S regs mem md F cnt idxp alloc).

End kd.
End g.

(* ===================== The proof of tfib_alloc_ok =====================
   The walk framework of AFem (the mapped-case depot proof this branch joins): the symbolic runner over the fetch table
   tfibtbl_rtB (AB1q.v:18, which covers Store + Alloc 0x6e8f4 for 150 insns and Create 0x6f400), seeds built with
   entry_st_ok_full, register pins between runs, and SRr_ret_at at the return. The statement above is closed before
   these imports, so they cannot change how its names resolve; the theorem is restated over the same Section
   variables and hypotheses in the same order (its closed type is unchanged). *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK0h YK14 YK1b YK1a YA0o YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AB1h.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AB1q AFek AFel AFl3.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YA05 YK0x.

Definition A_ALLOC1 : Z := 0x6ea1c.
Definition A_RESUME : Z := 0x6eb2c.
Abbreviation aF := 32%nat.
Abbreviation aX := 33%nat.
(* Seed at 0x6ea1c (after addi sp,sp,-16): Alloc's frame, s_total (atom aF = F), the block-0 data_ cell (literal 0 on
   first use, atom aX = ly_SB ly when mapped) and the idx cell (base a2). *)
Definition R_AFR : YP09.region := YP09.mkRegion (Some 2%nat) 0 16 0 16 [].
Definition R_TOTA : YP09.region :=
  YP09.mkRegion None TFIB_STORE (TFIB_STORE + 8) TFIB_STORE (TFIB_STORE + 8) [YP09.mkChunk TFIB_STORE (CVal 8 (SOff aF 0))].
Definition R_BLK0 : YP09.region :=
  YP09.mkRegion None (TFIB_STORE + 16) (TFIB_STORE + 24) 0 0 [YP09.mkChunk (TFIB_STORE + 16) (CVal 8 (SLit 0))].
Definition R_BLKM : YP09.region :=
  YP09.mkRegion None (TFIB_STORE + 16) (TFIB_STORE + 24) 0 0 [YP09.mkChunk (TFIB_STORE + 16) (CVal 8 (SOff aX 0))].
Definition R_IDX : YP09.region := YP09.mkRegion (Some 12%nat) 0 8 0 8 [].
Definition AREGS : list sv := sr_set sr_atoms 10%bv (SLit TFIB_STORE).
Definition AF_fix : list (nat * afact) :=
  [(2%nat, mkAF kHighMemBeg kHighMemEnd 4); (11%nat, mkAF 1 256 0); (12%nat, mkAF kHighMemBeg (kHighMemEnd - 8) 3);
   (aF, mkAF 0 (2 ^ 20 - 1) 0)].
Definition SA0 : sstate := mkSS A_ALLOC1 AREGS [R_AFR; R_TOTA; R_BLK0; R_IDX] None (mkFacts AF_fix [] []).
Definition SAM : sstate :=
  mkSS A_ALLOC1 AREGS [R_AFR; R_TOTA; R_BLKM; R_IDX] None (mkFacts (AF_fix ++ [(aX, mkAF 1 (2 ^ 64 - 1) 0)]) [] []).
(* Seed at 0x6eb2c (Create's return): Alloc's frame read-only with the saved s0 (atom aF) and ra (atom aX). *)
Definition R_AFR3 : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff aF 0)); YP09.mkChunk 8 (CVal 8 (SOff aX 0))].
Definition SC0 : sstate :=
  mkSS A_RESUME sr_atoms [R_AFR3] None (mkFacts [(2%nat, mkAF kHighMemBeg kHighMemEnd 4); (8%nat, mkAF 0 (2 ^ 20 - 1) 0)] [] []).

Ltac red_sr :=
lazymatch goal with |- _ = U _ (sr_get ?rs ?r) => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.

Section gp0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma SRr_run_to_shG : forall tbl, table_ok tfibsegs tbl -> forall W n stop E ss ss' st ms model Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN_sh tfibsegs tbl n stop ss = (ss', st) ->
  run_postG W E ss ss' st ms model Q -> SRr tfibsegs W (mkCfg ms model) Q.
Proof.
intros tbl tbl_ok W n stop E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_to_sh tfibsegs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_of_restricted_chainG W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
End gp0.

Ltac srr_run_to_shG tblok HS stop :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let r := eval vm_compute in (sym_run_toN_sh segs tbl FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_sh segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
eapply (SRr_run_to_shG tbl tblok W FUEL stop E ss ss' st ms _ _ HS Hrun);
clear Hrun HS; cbv beta iota; srr_after_runG HS
end
end
end.

Section gp1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma denot_of_U2 : forall E e z, U E e = z -> sv_denot E e = Z_to_bv 64 z.
Proof. intros E e z H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma sp_less16 : forall x : word, alu64 ALU_ADD x (sext 64 (4080%bv : bv 12)) = Z_to_bv 64 (bv_unsigned x - 16).
Proof.
intros x. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
assert (S16 : bv_unsigned (sext 64 (4080%bv : bv 12)) = 2 ^ 64 - 16) by (vm_compute; reflexivity). rewrite S16.
replace (bv_unsigned x + (2 ^ 64 - 16)) with (bv_unsigned x - 16 + 1 * 2 ^ 64) by lia. apply Z.mod_add. lia.
Qed.
(* The node SRr_refusable asks for: Alloc's first instruction, addi sp,sp,-16 (no memory access), as an event-free node
   with one child; the walk after it is a plain SRr (the refusal is excluded by premise). *)
Lemma alloc_entry_node : forall (W : world tfibsegs) regs mem md Q,
  SRr tfibsegs W (mkCfg (mkst (regupd regs 2%bv (Z_to_bv 64 (bv_unsigned (getr regs 2%bv) - 16))) (Z_to_bv 64 A_ALLOC1) mem (seg_rom tfibsegs)) md) Q ->
  SRr_refusable W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_StackStore_Alloc) mem (seg_rom tfibsegs)) md) Q.
Proof.
intros W regs mem md Q H. unfold SRr_refusable. apply SRr_use_AI. intros HI. apply SRr_ret.
exists unit, (fun _ => mkCfg (mkst (regupd regs 2%bv (Z_to_bv 64 (bv_unsigned (getr regs 2%bv) - 16))) (Z_to_bv 64 A_ALLOC1) mem (seg_rom tfibsegs)) md),
  (fun _ => false), tt.
split; [|split; [|split; [|split]]].
- apply YA05.node_instr_noacc; [exact (AI_halted _ _ _ _ HI) | reflexivity |].
  rewrite (YK0x.stepacc_opimm_gen tfibsegs regs (Z_to_bv 64 tfib_A_StackStore_Alloc) mem (seg_rom tfibsegs) (Z_to_bv 32 0xff010113)
    ALU_ADD 2%bv 2%bv (4080%bv : bv 12)).
  + rewrite sp_less16. replace (v_addi (Z_to_bv 64 tfib_A_StackStore_Alloc) 4) with (Z_to_bv 64 A_ALLOC1) by (apply bv_eq; reflexivity).
    reflexivity.
  + apply tfibtbl_rtB_ok. vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end.
- intros i HA. exact HA.
- reflexivity.
- intros i Hi. discriminate Hi.
- intros i _. exact H.
Qed.
End gp1.

Section gp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section kdp.
Variable layout_grow_kd : alayout -> alayout -> Prop.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
(* S3's statement, consumed (S2 does not walk Create). Satisfiable: it is S3's tfib_blockinfo_create_ok (AD3c.v,
   Qed) under its own premises kd_grow_SB and mnr_contract MNR_STK. *)
Hypothesis create_contract : tfib_blockinfo_create_spec layout_grow_kd B.
Section call.
Variables (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (F cnt idxp alloc : Z).
Hypotheses (R10 : getr regs 10 = Z_to_bv 64 (as_store B)) (R11 : getr regs 11 = Z_to_bv 64 cnt)
  (R12 : getr regs 12 = Z_to_bv 64 idxp) (Hra : YK0s.ret_ok (getr regs 1)).
Hypotheses (Hcnt : 1 <= cnt <= 256) (HF0 : 0 <= F) (HF1 : F + cnt <= 2 ^ 20).
Hypotheses (VTOT : val_mem tfibsegs (mrestrict (w_H W) mem) (as_store B + s_total) 8 F)
  (VBLK : val_mem tfibsegs (mrestrict (w_H W) mem) (as_store B + s_block0) 8 (ly_SB ly)) (HSB : 0 <= ly_SB ly < 2 ^ 64).
Hypothesis HFU : ly_SB ly = 0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (as_store B + bi0_mtx) 4 0 /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (as_store B + ss_alloc) 8 alloc /\ mnr_cells (mrestrict (w_H W) mem) /\
  md_room md kStoreBlockSize /\ eager_used md + A_bytes (w_A W) + kStoreBlockSize <= vm_limit (m_vmmaps md) /\
  YK0g.ivs_wf (vm_maps (m_vmmaps md)) /\ YM05.ceil_of_top (alloc_top (m_vmmaps md)) /\
  Forall (md_takes md) mnr_cell_extents /\
  md_takes md (as_store B, 32) /\
  Forall (md_takes md) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) /\
  (forall a, aclient_byte B ly S a -> md_takes md (a, 1)).
Hypotheses (Hidx8 : idxp mod 8 = 0) (Hidxlo : ly_stk_lo ly <= idxp) (Hidxhi : idxp + 8 <= ly_stk_hi ly)
  (Hidxsp : idxp + 8 <= spZ regs - (16 + BIC_STK) \/ spZ regs <= idxp)
  (Pidx : forall k, 0 <= k < 8 -> apresent (w_H W) mem (idxp + k)).
Hypotheses (Hsp16 : spZ regs mod 16 = 0) (Hstk : kHighMemBeg <= ly_stk_lo ly) (Hstkhi : ly_stk_hi ly <= kHighMemEnd)
  (Hsplo : ly_stk_lo ly <= spZ regs - (16 + BIC_STK)) (Hsphi : spZ regs <= ly_stk_hi ly)
  (Pstk : forall a, spZ regs - (16 + BIC_STK) <= a < spZ regs -> apresent (w_H W) mem a).

Definition sp1 : Z := spZ regs - 16.
Definition regs1 : bvmap 5 word := regupd regs 2%bv (Z_to_bv 64 (bv_unsigned (getr regs 2%bv) - 16)).
Definition E0 : env := Ereg regs1 [Z_to_bv 64 F; Z_to_bv 64 (ly_SB ly)].
Definition ms0 : machine_state := mkst regs1 (Z_to_bv 64 A_ALLOC1) mem (seg_rom tfibsegs).
(* Alloc's own writes before the call: its frame, s_total and the idx cell; presence only grows. *)
Definition MREL (m : word -> option byte) : Prop :=
  (forall x : word, ~ (sp1 <= bv_unsigned x < sp1 + 16) -> ~ (TFIB_STORE <= bv_unsigned x < TFIB_STORE + 8) ->
     ~ (idxp <= bv_unsigned x < idxp + 8) -> m x = mem x) /\ mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m).

Lemma geo : as_store B = TFIB_STORE /\ 0 <= spZ regs < 2 ^ 64 /\ kHighMemBeg + 48 <= spZ regs /\ spZ regs <= kHighMemEnd /\
  sp1 mod 16 = 0 /\ kHighMemBeg <= idxp /\ idxp + 8 <= kHighMemEnd /\
  (idxp + 8 <= sp1 - BIC_STK \/ sp1 + 16 <= idxp) /\ 32 <= BIC_STK.
Proof.
pose proof (ts_store B HB) as ES. pose proof (u64_range (getr regs 2%bv)) as UR. unfold sp1, BIC_STK, MNR_STK, spZ in *.
assert (M16 : (bv_unsigned (getr regs 2%bv) - 16) mod 16 = 0).
{ pose proof Hsp16 as H16. unfold spZ in H16. apply Z.mod_divide in H16 as [q Hq]; [|lia].
  rewrite Hq. replace (q * 16 - 16) with ((q - 1) * 16) by lia. apply Z.mod_mul. lia. }
repeat split; try exact ES; try exact M16; try lia.
Qed.
Ltac geo' := pose proof geo as (ES & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8); unfold sp1, BIC_STK, MNR_STK, spZ in *;
  unfold kHighMemBeg, kHighMemEnd, TFIB_STORE, TFIB_IMG_END, YImgTop.IMG_TOP in *.

Lemma EW2 : bv_unsigned (ew E0 2) = sp1.
Proof.
unfold E0. rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl). unfold regs1. rewrite getr_same by (intros X; discriminate).
apply unsigned_lit_small. pose proof geo as (_ & G1 & G2 & _). unfold sp1, spZ in *. unfold kHighMemBeg in *. lia.
Qed.
Lemma EWr : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> r <> 2%bv -> ew E0 n = getr regs r.
Proof. intros r n Hn Hr. unfold E0. rewrite (ew_Ereg_nat regs1 _ n r Hn). unfold regs1. rewrite getr_other by exact Hr. reflexivity. Qed.
Lemma EW11 : bv_unsigned (ew E0 11) = cnt.
Proof. rewrite (EWr 11%bv 11 eq_refl ltac:(intros X; discriminate)), R11. apply unsigned_lit_small. lia. Qed.
Lemma EW12 : bv_unsigned (ew E0 12) = idxp.
Proof. rewrite (EWr 12%bv 12 eq_refl ltac:(intros X; discriminate)), R12. apply unsigned_lit_small. geo'. lia. Qed.
Lemma EW32 : bv_unsigned (ew E0 aF) = F.
Proof. change (ew E0 aF) with (Z_to_bv 64 F). apply unsigned_lit_small. lia. Qed.
Lemma EW33 : bv_unsigned (ew E0 aX) = ly_SB ly.
Proof. change (ew E0 aX) with (Z_to_bv 64 (ly_SB ly)). apply unsigned_lit_small. lia. Qed.

Lemma AFo2 : forall E k X lo hi al, ew E k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E k (mkAF lo hi al).
Proof. intros E k X lo hi al HE HX HBd HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. rewrite unsigned_lit_small by exact HX. repeat split; lia. Qed.
Lemma atoms_ok_of_Forall2 : forall E l, Forall (fun nf : nat * afact => afact_ok E (fst nf) (snd nf)) l -> atoms_ok E l.
Proof. intros E l H. induction H as [| [k f] l Hh Ht IH]; cbn; [exact I | split; [exact Hh | exact IH]]. Qed.

Lemma seed_regs : regs_ok E0 AREGS regs1.
Proof.
unfold AREGS, E0. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate |].
cbn [sv_denot]. unfold regs1. rewrite getr_other by (intros X; discriminate). rewrite R10, (ts_store B HB). reflexivity.
Qed.
Lemma seed_atoms : Forall (fun nf : nat * afact => afact_ok E0 (fst nf) (snd nf)) AF_fix.
Proof.
geo'. unfold AF_fix. apply Forall_cons.
{ apply (AFo2 E0 2%nat sp1); [| | | |lia].
  - unfold E0. rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl). unfold regs1, sp1, spZ. rewrite getr_same by (intros X; discriminate). reflexivity.
  - unfold sp1, spZ. lia.
  - unfold sp1, spZ. unfold kHighMemBeg, kHighMemEnd. lia.
  - change (2 ^ 4) with 16. exact G4. }
apply Forall_cons. { apply (AFo2 E0 11%nat cnt); [rewrite (EWr 11%bv 11 eq_refl ltac:(intros X; discriminate)); exact R11 | lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { apply (AFo2 E0 12%nat idxp); [rewrite (EWr 12%bv 12 eq_refl ltac:(intros X; discriminate)); exact R12 | lia | unfold kHighMemBeg, kHighMemEnd; lia | change (2 ^ 3) with 8; exact Hidx8 | lia]. }
apply Forall_cons. { apply (AFo2 E0 aF F); [reflexivity | lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_nil.
Qed.

Lemma reg_rgn_frame : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_AFR.
Proof.
geo'. apply (region_ok_window E0 _ 2 sp1); [exact EW2 | unfold sp1, spZ; lia | unfold sp1, spZ; lia |].
intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, YImgTop.IMG_TOP; unfold sp1, spZ in Ha; lia |]. apply Pstk. unfold sp1, spZ in Ha. lia.
Qed.
Lemma reg_rgn_idx : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_IDX.
Proof.
geo'. apply (region_ok_window E0 _ 12 idxp); [exact EW12 | lia | lia |].
intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, YImgTop.IMG_TOP; lia |].
replace a with (idxp + (a - idxp)) by lia. apply Pidx. lia.
Qed.
Lemma rw_writable2 : forall (m : word -> option byte) a, 0x96000 <= a < YImgTop.IMG_TOP -> writable_at tfibsegs m a.
Proof.
intros m a Ha. unfold writable_at. rewrite <- tsegs_tfasegs. apply tfib_rw_window. rewrite unsigned_lit_small by (unfold YImgTop.IMG_TOP in Ha; lia).
unfold YImgTop.IMG_TOP in Ha |- *. lia.
Qed.
Lemma reg_rgn_tot : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_TOTA.
Proof.
pose proof (ts_store B HB) as ES. unfold region_ok, R_TOTA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold TFIB_STORE. split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_writable2; unfold YImgTop.IMG_TOP; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E0 _ 0 TFIB_STORE 8 (SOff aF 0) F); [| cbn; lia | cbn; lia |].
- cbn [sv_denot]. rewrite EW32, Z.add_0_r. reflexivity.
- rewrite Z.add_0_l. rewrite ES in VTOT. unfold s_total in VTOT. rewrite Z.add_0_r in VTOT. exact VTOT.
Qed.
Lemma reg_rgn_blk0 : ly_SB ly = 0 -> region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_BLK0.
Proof.
intros H0. pose proof (ts_store B HB) as ES. unfold R_BLK0.
apply (region_ok_lit E0 _ (TFIB_STORE + 16) 8 0); [| cbn; lia | cbn; lia | unfold TFIB_STORE; lia | unfold TFIB_STORE; cbn; lia].
rewrite ES, H0 in VBLK. unfold s_block0 in VBLK. exact VBLK.
Qed.
Lemma reg_rgn_blkm : region_ok tfibsegs E0 (mrestrict (w_H W) mem) R_BLKM.
Proof.
pose proof (ts_store B HB) as ES. unfold region_ok, R_BLKM. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold TFIB_STORE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E0 _ 0 1508376 8 (SOff aX 0) (ly_SB ly)); [| cbn; lia | cbn; lia |].
- cbn [sv_denot]. rewrite EW33, Z.add_0_r. reflexivity.
- rewrite Z.add_0_l. rewrite ES in VBLK. unfold s_block0, TFIB_STORE in VBLK. exact VBLK.
Qed.
Lemma seed_pairs : forall rb, YP09.r_base rb = None -> YP09.r_lo rb = TFIB_STORE + 16 -> YP09.r_hi rb = TFIB_STORE + 24 ->
  pairwise_disjoint E0 [R_AFR; R_TOTA; rb; R_IDX].
Proof.
intros rb Hb Hlo Hhi. geo'. apply pairwise_disjoint_of_extents. unfold R_AFR, R_TOTA, R_IDX, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Hb, Hlo, Hhi. cbn [base_val]. rewrite EW2, EW12.
unfold TFIB_STORE. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold sp1, spZ in *. repeat split; lia.
Qed.
Lemma seed0 : ly_SB ly = 0 -> st_ok tfibsegs E0 SA0 (restrict (w_H W) ms0).
Proof.
intros H0. unfold ms0. rewrite restrict_mkst_fx. unfold SA0. unfold E0. apply (entry_st_ok_full tfibsegs).
- exact seed_regs.
- vm_compute. reflexivity.
- apply Forall_cons; [exact reg_rgn_frame|]. apply Forall_cons; [exact reg_rgn_tot|].
  apply Forall_cons; [exact (reg_rgn_blk0 H0)|]. apply Forall_cons; [exact reg_rgn_idx | apply Forall_nil].
- exact (seed_pairs R_BLK0 eq_refl eq_refl eq_refl).
- split; [| split; exact I]. cbn [f_atoms]. apply atoms_ok_of_Forall2. exact seed_atoms.
Qed.
Lemma seedM : ly_SB ly <> 0 -> st_ok tfibsegs E0 SAM (restrict (w_H W) ms0).
Proof.
intros H0. unfold ms0. rewrite restrict_mkst_fx. unfold SAM. unfold E0. apply (entry_st_ok_full tfibsegs).
- exact seed_regs.
- vm_compute. reflexivity.
- apply Forall_cons; [exact reg_rgn_frame|]. apply Forall_cons; [exact reg_rgn_tot|].
  apply Forall_cons; [exact reg_rgn_blkm|]. apply Forall_cons; [exact reg_rgn_idx | apply Forall_nil].
- exact (seed_pairs R_BLKM eq_refl eq_refl eq_refl).
- split; [| split; exact I]. cbn [f_atoms]. apply atoms_ok_of_Forall2. apply Forall_app. split; [exact seed_atoms|].
  apply Forall_cons; [| apply Forall_nil]. apply (AFo2 E0 aX (ly_SB ly)); [reflexivity | lia | lia | apply Z.mod_1_r | lia].
Qed.

Lemma inw_seed : forall a, in_wrange E0 (ss_mem SA0) a ->
  (sp1 <= a < sp1 + 16) \/ (TFIB_STORE <= a < TFIB_STORE + 8) \/ (idxp <= a < idxp + 8).
Proof.
intros a (r & Hin & Ha). cbn [ss_mem SA0] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [R_AFR R_TOTA R_BLK0 R_IDX YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
- rewrite EW2 in Ha. left. lia.
- right. left. lia.
- lia.
- rewrite EW12 in Ha. right. right. lia.
Qed.
Lemma MREL_mem : MREL mem.
Proof. split; [intros x _ _ _; reflexivity | intros x Hx; exact Hx]. Qed.
Lemma MREL_step : forall rs (m m' : word -> option byte), MREL m -> windows rs = windows (ss_mem SA0) -> frame_of E0 rs m m' ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> MREL m'.
Proof.
intros rs m m' [IF IG] Hw HF HG. split.
- intros x N1 N2 N3. rewrite (HF x); [exact (IF x N1 N2 N3)|]. intros Hx.
  apply (in_wrange_of_windows E0 rs (ss_mem SA0) _ (eq_sym Hw)) in Hx.
  destruct (inw_seed _ Hx) as [X|[X|X]]; contradiction.
- exact (mem_grows_trans' _ _ _ IG HG).
Qed.
Lemma MREL_val : forall (m : word -> option byte) a (n : nat) v, MREL m -> 0 <= a -> a + Z.of_nat n <= YImgTop.IMG_TOP ->
  (a + Z.of_nat n <= TFIB_STORE \/ TFIB_STORE + 8 <= a) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a n v -> val_mem tfibsegs (mrestrict (w_H W) m) a n v.
Proof.
intros m a n v [IF _] Ha Hn Hs Hv. apply (val_mem_frame (w_H W) mem m a n v); [| exact Hv].
intros k Hk. geo'. apply IF; rewrite unsigned_lit_small by lia; lia.
Qed.
Lemma MREL_present : forall (m : word -> option byte) a, MREL m -> apresent (w_H W) mem a -> apresent (w_H W) m a.
Proof. intros m a [_ IG] Ha. exact (apresent_grows (w_H W) mem m a IG Ha). Qed.

(* the values the pins and the exit need *)
Lemma t0F : forall E f, bv_unsigned (ew E aF) = f -> 0 <= f < 2 ^ 20 -> U E (SLit 0) = U E (SAlu ALU_SRL (SOff aF 0) (SLit 20)).
Proof.
intros E t H Ht. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small t) by lia. change (Z.land (20 mod 2 ^ 64) 63) with 20.
rewrite (shiftr_small0 t 20) by lia. reflexivity.
Qed.
Lemma t1F : forall E n f, bv_unsigned (ew E 11) = n -> bv_unsigned (ew E aF) = f -> 1 <= n -> 0 <= f -> n - 1 + f < 2 ^ 20 ->
  U E (SLit 0) = U E (SAlu ALU_SRL (SAlu ALU_ADD (SOff 11 (-1)) (SOff aF 0)) (SLit 20)).
Proof.
intros E n f H11 Hf Hn Hf0 Hs. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H11, Hf.
unfold zcanon, M64. cbn [zalu_raw]. rewrite ?Z.add_0_r. rewrite (Z.mod_small (n + -1)) by lia. rewrite (Z.mod_small f) by lia.
rewrite (Z.mod_small (n + -1 + f)) by lia. change (Z.land (20 mod 2 ^ 64) 63) with 20.
rewrite (shiftr_small0 (n + -1 + f) 20) by lia. reflexivity.
Qed.
Lemma s32F : forall E f, bv_unsigned (ew E aF) = f -> 0 <= f < 2 ^ 32 -> U E (SLit 0) = U E (SAlu ALU_SRL (SOff aF 0) (SLit 32)).
Proof.
intros E t H Ht. rewrite !U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small t) by lia. change (Z.land (32 mod 2 ^ 64) 63) with 32.
rewrite (shiftr_small0 t 32) by lia. reflexivity.
Qed.
Lemma totF : forall E n f, bv_unsigned (ew E 11) = n -> bv_unsigned (ew E aF) = f -> 0 <= n -> 0 <= f -> n + f < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 11 0) (SOff aF 0)) = Z_to_bv 64 (f + n).
Proof.
intros E n f H11 Hf Hn Hf0 Hs. apply denot_of_U2. rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite H11, Hf.
unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small n), (Z.mod_small f) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma retgen : forall E (i j : nat) a b, bv_unsigned (ew E i) = a -> bv_unsigned (ew E j) = b -> 0 <= a < 2 ^ 20 -> 0 <= b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff i 0) (SLit 3)) (SOff j 0)) = Z_to_bv 64 (b + 8 * a).
Proof.
intros E i j a b Hi Hj Ha Hb.
assert (HU : U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff i 0) (SLit 3)) (SOff j 0)) = (b + 8 * a) mod 2 ^ 64).
{ rewrite U_zev by reflexivity. cbn [zev svpure]. unfold rho_of. rewrite Hi, Hj.
  unfold zcanon, M64. cbn [zalu_raw]. rewrite !Z.add_0_r, (Z.mod_small a), (Z.mod_small b) by lia. change (Z.land (3 mod 2 ^ 64) 63) with 3.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. rewrite (Z.mod_small (a * 8)) by lia. f_equal. lia. }
transitivity (Z_to_bv 64 (U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff i 0) (SLit 3)) (SOff j 0)))).
{ unfold U. symmetry. apply Z_to_bv_bv_unsigned. }
apply Z_to_bv64_eq_mod. rewrite HU. apply Z.mod_mod. lia.
Qed.
Lemma reg_at : forall {H0 : word -> bool} E ss (ms : machine_state) (r : bv 5) n, st_ok tfibsegs E ss (restrict H0 ms) ->
  sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof. intros H0 E ss ms r n HS Hr. rewrite (st_ok_reg_denot H0 E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma cs_byb : forall z, ((z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)))%bool = true ->
  callee_saved z.
Proof.
intros z H. unfold callee_saved. repeat rewrite Bool.orb_true_iff in H. rewrite Bool.andb_true_iff in H.
rewrite !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.
Lemma val_mem_HW : forall (H1 H2 : word -> bool) (m1 m2 : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> H2 (Z_to_bv 64 (a + Z.of_nat k)) = H1 (Z_to_bv 64 (a + Z.of_nat k)) /\
     m2 (Z_to_bv 64 (a + Z.of_nat k)) = m1 (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs (mrestrict H1 m1) a n v -> val_mem tfibsegs (mrestrict H2 m2) a n v.
Proof.
intros H1 H2 m1 m2 a n v Hk Hv k Hlt. rewrite <- (Hv k Hlt). destruct (Hk k Hlt) as [E1 E2].
unfold mbyte, mrestrict. rewrite E1, E2. reflexivity.
Qed.
(* The new block avoids the store's page: [SS, SS + 32) lies in one page, X is page aligned, so either X misses the
   page or covers it; covering it would make data_ (SS + 16) read 0 by P4 while P1 says it holds x >= 4096. *)
Lemma blk_avoids_store : forall (H0 : word -> bool) (m : word -> option byte) x,
  YG0f.page_aligned x -> in_app x kStoreBlockSize ->
  val_mem tfibsegs (mrestrict H0 m) (TFIB_STORE + 16) 8 x ->
  (forall i, 0 <= i < kStoreBlockSize -> aview tfibsegs H0 m (x + i) = Some 0) ->
  forall a, TFIB_STORE <= a < TFIB_STORE + 32 -> ~ (x <= a < x + kStoreBlockSize).
Proof.
intros H0 m x Hal Hin Hv Hz a Ha Hx.
pose proof (@ASAN_CEIL_range rc) as [CR _].
unfold in_app, YG0f.page_aligned, kStoreBlockSize, kLowShadowBeg, kHighMemBeg, TFIB_STORE in *.
assert (PG : x <= 1507328 /\ 1511424 <= x + 8388608).
{ apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq]. subst x. lia. }
assert (XR : 0 <= x < 2 ^ 64) by (unfold ASAN_CEIL in *; lia).
assert (Z0 : forall k, (k < 8)%nat -> YG0f.le_byte x 8 k = 0).
{ intros k Hk. pose proof (Hv k Hk) as Vk. pose proof (Hz (1508376 + Z.of_nat k - x) ltac:(lia)) as Zk.
  replace (x + (1508376 + Z.of_nat k - x)) with (1508360 + 16 + Z.of_nat k) in Zk by lia.
  unfold aview in Zk. rewrite Vk in Zk. cbn [option_map] in Zk. injection Zk as Zk.
  rewrite Z_to_bv_unsigned in Zk. unfold bv_wrap, bv_modulus in Zk. change (2 ^ Z.of_N 8) with 256 in Zk.
  assert (LB : 0 <= YG0f.le_byte x 8 k < 256) by (unfold YG0f.le_byte; apply Z.mod_pos_bound; lia).
  rewrite Z.mod_small in Zk by exact LB. exact Zk. }
pose proof (le_bytes8_sum x XR) as Hs. cbv zeta beta in Hs.
rewrite !Z0 in Hs by lia. lia.
Qed.

Ltac mrel_step HIold HInew :=
  lazymatch goal with
  | HF0 : frame_of _ _ _ _, HG0 : mem_grows (mrestrict _ (ms_mem ?mso)) (mrestrict _ (ms_mem ?msn)) |- _ =>
    assert (HInew : MREL (ms_mem msn)) by (eapply MREL_step; [exact HIold | | exact HF0 | exact HG0]; vm_compute; reflexivity);
    clear HF0 HG0 HIold; try clear mso; try rename msn into ms
  end.

Lemma mapped_arm : ly_SB ly <> 0 -> SRr tfibsegs W (mkCfg ms0 md) (alloc_post layout_grow_kd B W ly S regs mem md F cnt idxp alloc).
Proof.
intros HM0. pose proof Hwx_tfa as HWX. pose proof (seedM HM0) as HS. pose proof MREL_mem as HI0.
pose proof EW32 as V32. pose proof EW11 as V11. pose proof EW12 as V12. pose proof EW33 as V33. pose proof EW2 as V2.
srr_run_shG tfibtbl_rtB_ok HS.
mrel_step HI0 HI1.
apply (st_ok_pin_regU E0 _ _ 5%bv (SLit 0)) in HS; [| intros X; discriminate | red_sr; apply (t0F E0 F V32); lia].
apply (st_ok_pin_regU E0 _ _ 6%bv (SLit 0)) in HS; [| intros X; discriminate | red_sr; apply (t1F E0 cnt F V11 V32); lia].
srr_run_shG tfibtbl_rtB_ok HS.
mrel_step HI1 HI2.
apply (st_ok_pin_regU E0 _ _ 10%bv (SLit 0)) in HS; [| intros X; discriminate | red_sr; apply (s32F E0 F V32); lia].
srr_run_shG tfibtbl_rtB_ok HS.
mrel_step HI2 HI3.
eapply (SRr_ret_at tfibsegs tfibtbl_rtB tfibtbl_rtB_ok HWX W); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse.
pose proof geo as (ES & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
unfold alloc_post. exists (ly_SB ly), ly, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat' md).
split.
{ assert (R1 : getr (ms_regs ms) 1%bv = getr regs 1%bv).
  { rewrite (reg_at E0 _ ms 1%bv 1 HS ltac:(vm_compute; reflexivity)). exact (EWr 1%bv 1 eq_refl ltac:(intros X; discriminate)). }
  rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
unfold alloc_exit. cbv zeta. rewrite ES.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
- rewrite (st_ok_reg_denot (w_H W) E0 _ ms 10%bv HS).
  lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.
  apply (retgen E0 32 33 F (ly_SB ly) V32 V33); lia.
- apply regs_preserved_intro.
  all: lazymatch goal with
       | |- getr (ms_regs ?m) 2%bv = getr _ 2%bv =>
           rewrite (st_ok_reg_denot (w_H W) E0 _ m 2%bv HS);
           lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end;
           cbn [sv_denot]; rewrite V2; unfold sp1, spZ;
           replace (bv_unsigned (getr regs 2%bv) - 16 + 16) with (bv_unsigned (getr regs 2%bv)) by lia; apply Z_to_bv_bv_unsigned
       | |- getr (ms_regs ?m) ?r = getr _ ?r =>
           rewrite (reg_at E0 _ m r (Z.to_nat (bv_unsigned r)) HS ltac:(vm_compute; reflexivity));
           apply EWr; [reflexivity | intros X; discriminate]
       end.
- unfold s_total. rewrite Z.add_0_r.
  memv HS 1%nat 0%nat; [unfold TFIB_STORE; lia | apply (totF E0 cnt F V11 V32); lia | lia].
- memv HS 3%nat 0%nat; [rewrite V12; lia | cbn [sv_denot]; rewrite V32, Z.add_0_r; reflexivity | lia].
- unfold s_block0. memv HS 2%nat 0%nat; [unfold TFIB_STORE; lia | cbn [sv_denot]; rewrite V33, Z.add_0_r; reflexivity | lia].
- intros a Ha. exact (MREL_present _ a HI3 Ha).
- right. refine (conj HM0 (conj eq_refl (conj eq_refl (conj eq_refl (conj (ex_intro _ mat' eq_refl) _))))).
  intros a N1 N2 N3. apply (proj1 HI3); [intros X; apply N1; unfold sp1 in X; lia | exact N2 | exact N3].
Qed.
Lemma first_use_arm : ly_SB ly = 0 -> SRr tfibsegs W (mkCfg ms0 md) (alloc_post layout_grow_kd B W ly S regs mem md F cnt idxp alloc).
Proof.
intros H0. pose proof Hwx_tfa as HWX. pose proof (seed0 H0) as HS. pose proof MREL_mem as HI0.
pose proof EW32 as V32. pose proof EW11 as V11. pose proof EW12 as V12. pose proof EW2 as V2.
pose proof geo as (ES & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
destruct (HFU H0) as (FM & FA & FC & FR & FB & FI & FCT & FE & FT & FX & FCL).
srr_run_shG tfibtbl_rtB_ok HS. mrel_step HI0 HI1.
apply (st_ok_pin_regU E0 _ _ 5%bv (SLit 0)) in HS; [| intros X; discriminate | red_sr; apply (t0F E0 F V32); lia].
apply (st_ok_pin_regU E0 _ _ 6%bv (SLit 0)) in HS; [| intros X; discriminate | red_sr; apply (t1F E0 cnt F V11 V32); lia].
srr_run_shG tfibtbl_rtB_ok HS. mrel_step HI1 HI2.
apply (st_ok_pin_regU E0 _ _ 10%bv (SLit 0)) in HS; [| intros X; discriminate | red_sr; apply (s32F E0 F V32); lia].
srr_run_to_shG tfibtbl_rtB_ok HS tfib_A_StackStore_BlockInfo_Create. mrel_step HI2 HI3.
(* at Create's entry, 0x6f400 *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msC end.
assert (SP1 : spZ (ms_regs msC) = sp1).
{ unfold spZ. rewrite (reg_at E0 _ msC 2%bv 2 HS ltac:(vm_compute; reflexivity)). exact V2. }
assert (R1c : getr (ms_regs msC) 1%bv = Z_to_bv 64 A_RESUME).
{ rewrite (st_ok_reg_denot (w_H W) E0 _ msC 1%bv HS).
  lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.
  reflexivity. }
assert (R8c : getr (ms_regs msC) 8%bv = Z_to_bv 64 F) by exact (reg_at E0 _ msC 8%bv 32 HS ltac:(vm_compute; reflexivity)).
assert (Mtot : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msC)) TFIB_STORE 8 (F + cnt)).
{ memv HS 1%nat 0%nat; [unfold TFIB_STORE; lia | apply (totF E0 cnt F V11 V32); lia | lia]. }
assert (Midx : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msC)) idxp 8 F).
{ memv HS 3%nat 0%nat; [rewrite V12; lia | cbn [sv_denot]; rewrite V32, Z.add_0_r; reflexivity | lia]. }
assert (Ms0 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msC)) sp1 8 (bv_unsigned (getr regs 8%bv))).
{ memv HS 0%nat 0%nat; [rewrite V2; lia | cbn [sv_denot]; rewrite Z.add_0_r, (EWr 8%bv 8 eq_refl ltac:(intros X; discriminate)); reflexivity | apply u64_range]. }
assert (Mra : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msC)) (sp1 + 8) 8 (bv_unsigned (getr regs 1%bv))).
{ memv HS 0%nat 1%nat; [rewrite V2; lia | cbn [sv_denot]; rewrite Z.add_0_r, (EWr 1%bv 1 eq_refl ltac:(intros X; discriminate)); reflexivity | apply u64_range]. }
pose proof HS as HSC.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ msC HS eq_refl) as Hms. rewrite Hms. clear Hms.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdc) _ => pose proof (create_contract W ly S (ms_regs msC) (ms_mem msC) mdc alloc) as HC end.
cbv zeta in HC.
eapply SRr_bind; [apply SRr_refusable_SRr; apply HC; clear HC | ].
{ exact H0. }
{ rewrite (st_ok_reg_denot (w_H W) E0 _ msC 10%bv HSC).
  lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.
  cbn [sv_denot]. rewrite ES. reflexivity. }
{ rewrite (st_ok_reg_denot (w_H W) E0 _ msC 11%bv HSC).
  lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.
  cbn [sv_denot]. rewrite ES. reflexivity. }
{ rewrite R1c. unfold YK0s.ret_ok. apply bv_eq. reflexivity. }
{ rewrite ES. unfold s_block0. memv HSC 2%nat 0%nat; [unfold TFIB_STORE; lia | cbn [sv_denot]; reflexivity | lia]. }
{ rewrite ES in FM |- *. unfold bi0_mtx in *. apply (MREL_val _ (TFIB_STORE + 28) 4 0 HI3); [unfold TFIB_STORE; lia | unfold TFIB_STORE, YImgTop.IMG_TOP; cbn; lia | right; lia | exact FM]. }
{ rewrite ES in FA |- *. unfold ss_alloc in *. apply (MREL_val _ (TFIB_STORE + 8) 8 alloc HI3); [unfold TFIB_STORE; lia | unfold TFIB_STORE, YImgTop.IMG_TOP; cbn; lia | right; lia | exact FA]. }
{ unfold mnr_cells in FC |- *. destruct FC as (C1 & C2 & C3 & (f & C4 & C5) & C6).
  refine (conj _ (conj _ (conj _ (conj (ex_intro _ f (conj _ C5)) _))));
  apply (MREL_val _ _ _ _ HI3); unfold MNR_PSC_GOT, MNR_PSC, MNR_CF_GOT, MNR_CF, TFIB_STORE, YImgTop.IMG_TOP; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; assumption. }
{ exact FR. }
{ exact FB. }
{ exact FI. }
{ exact FCT. }
{ exact FE. }
{ rewrite SP1. exact G4. }
{ exact Hstk. }
{ rewrite SP1. unfold sp1, BIC_STK, MNR_STK in *. lia. }
{ rewrite SP1. unfold sp1. lia. }
{ exact Hstkhi. }
{ intros a Ha. rewrite SP1 in Ha. apply (MREL_present _ a HI3). apply Pstk. unfold sp1, BIC_STK, MNR_STK in *. lia. }
{ exact FT. }
{ exact FX. }
{ exact FCL. }
(* Create's post *)
intros W2 c2 Hle2 HP. destruct HP as (x & regs2 & mem2 & md2 & HP). cbv zeta in HP.
destruct HP as (Hc2 & HWA & HWH & P1a & P1b & P1c & P2a & P2b & P3a & P3b & P4 & P5 & PAL & PMX & PPR & PIO & PT1 & PT2 & PM1 & PM2 & PM3 & PM4 & P6 & P7).
subst c2. rewrite R1c.
pose proof (@ASAN_CEIL_range rc) as [CR _].
assert (XR : 4096 <= x /\ x + kStoreBlockSize < 2 ^ 64) by (unfold in_app, kStoreBlockSize, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (PB : forall r : bv 5, callee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs msC) r).
{ intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (P1b _ Hr). }
assert (R2b : getr regs2 2%bv = Z_to_bv 64 sp1).
{ rewrite (PB 2%bv ltac:(unfold callee_saved; vm_compute; lia)). rewrite <- (Z_to_bv_bv_unsigned 64 (getr (ms_regs msC) 2%bv)).
  fold (spZ (ms_regs msC)). rewrite SP1. reflexivity. }
assert (R8b : getr regs2 8%bv = Z_to_bv 64 F) by (rewrite (PB 8%bv ltac:(unfold callee_saved; vm_compute; lia)); exact R8c).
assert (XS : x + kStoreBlockSize <= ly_stk_lo ly \/ ly_stk_hi ly <= x).
{ assert (Hin : In (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps)).
  { apply in_app_iff. left. unfold ext_but_SB. apply in_app_iff. right. apply in_app_iff. right. cbn. tauto. }
  pose proof (proj1 (Forall_forall _ _) P3a _ Hin) as Zd. unfold zdisjoint in Zd. cbn [fst snd] in Zd. lia. }
assert (XT : forall a, TFIB_STORE <= a < TFIB_STORE + 32 -> ~ (x <= a < x + kStoreBlockSize)).
{ apply (blk_avoids_store (w_H W2) mem2 x P2a P2b); [rewrite ES in P1c; unfold s_block0 in P1c; exact P1c | intros i Hi; exact (proj2 (P4 i Hi))]. }
assert (CF : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - BIC_STK <= a < sp1) -> ~ (x <= a < x + kStoreBlockSize) ->
  ~ (TFIB_STORE + 8 <= a < TFIB_STORE + 24) -> ~ (TFIB_STORE + 28 <= a < TFIB_STORE + 32) -> mem2 (Z_to_bv 64 a) = ms_mem msC (Z_to_bv 64 a)).
{ intros a Ha N1 N2 N3 N4. apply P5; rewrite unsigned_lit_small by lia; [rewrite SP1; exact N1 | exact N2 | | ]; rewrite ES; unfold ss_alloc, s_block0, bi0_mtx; lia. }
assert (VF : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, (k < n)%nat -> ~ (sp1 - BIC_STK <= a + Z.of_nat k < sp1) /\ ~ (x <= a + Z.of_nat k < x + kStoreBlockSize) /\
     ~ (TFIB_STORE + 8 <= a + Z.of_nat k < TFIB_STORE + 24) /\ ~ (TFIB_STORE + 28 <= a + Z.of_nat k < TFIB_STORE + 32)) ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem msC)) a n v -> val_mem tfibsegs (mrestrict (w_H W2) mem2) a n v).
{ intros a n v Ha Hn Hk Hv. apply (val_mem_HW (w_H W) (w_H W2) (ms_mem msC) mem2 a n v); [| exact Hv].
  intros k Hk'. destruct (Hk k Hk') as (N1 & N2 & N3 & N4). split.
  - apply HWH. rewrite unsigned_lit_small by lia. exact N2.
  - apply CF; [lia | exact N1 | exact N2 | exact N3 | exact N4]. }
assert (SP1R : 0 <= sp1 /\ sp1 + 16 <= 2 ^ 64) by (unfold sp1, spZ in *; unfold kHighMemBeg, kHighMemEnd in *; lia).
set (E2 := Ereg regs2 [getr regs 8%bv; getr regs 1%bv]).
assert (HS2 : st_ok tfibsegs E2 SC0 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 A_RESUME) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold SC0, E2. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| apply Forall_nil]. unfold region_ok, R_AFR3.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), R2b, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    + eapply (chunk_ok_val tfibsegs _ _ sp1 0 8 (SOff 32 0) (bv_unsigned (getr regs 8%bv))); [| apply u64_range | cbn; lia |].
      * cbn [sv_denot]. rewrite Z.add_0_r. reflexivity.
      * rewrite Z.add_0_r. apply VF; [lia | lia | | exact Ms0].
        intros k Hk. unfold sp1, spZ, BIC_STK, MNR_STK in *. unfold kHighMemBeg, kHighMemEnd, TFIB_STORE in *. repeat split; lia.
    + eapply (chunk_ok_val tfibsegs _ _ sp1 8 8 (SOff 33 0) (bv_unsigned (getr regs 1%bv))); [| apply u64_range | cbn; lia |].
      * cbn [sv_denot]. rewrite Z.add_0_r. reflexivity.
      * apply VF; [lia | lia | | exact Mra].
        intros k Hk. unfold sp1, spZ, BIC_STK, MNR_STK in *. unfold kHighMemBeg, kHighMemEnd, TFIB_STORE in *. repeat split; lia.
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [| split; exact I]. cbn [f_atoms]. apply atoms_ok_of_Forall2.
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    + apply (AFo2 _ 2%nat sp1); [rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact R2b | lia | unfold sp1, spZ in *; unfold kHighMemBeg, kHighMemEnd in *; lia | change (2 ^ 4) with 16; exact G4 | lia].
    + apply (AFo2 _ 8%nat F); [rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl); exact R8b | lia | lia | apply Z.mod_1_r | lia]. }
srr_run_shG tfibtbl_rtB_ok HS2.
pose proof (fun Hro => frame_of_read_only _ _ _ _ Hro HF) as EM3. specialize (EM3 ltac:(vm_compute; reflexivity)). cbn [ms_mem] in EM3. clear HF HG.
lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?m) => rename m into ms3 end.
eapply (SRr_ret_at tfibsegs tfibtbl_rtB tfibtbl_rtB_ok HWX W2); [exact HS2 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse.
unfold alloc_post. exists x, (set_ly_SB ly x), (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md2) mat' md2).
split.
{ assert (R1 : getr (ms_regs ms3) 1%bv = getr regs 1%bv) by exact (reg_at E2 _ ms3 1%bv 33 HS2 ltac:(vm_compute; reflexivity)).
  rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
unfold alloc_exit. cbv zeta. rewrite ES. rewrite EM3.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
- rewrite (st_ok_reg_denot (w_H W2) E2 _ ms3 10%bv HS2).
  lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.
  apply (retgen E2 8 10 F x); [| | clear -HF0 HF1 Hcnt; lia | clear -XR; unfold kStoreBlockSize in XR; lia].
  + unfold E2. rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), R8b. apply unsigned_lit_small. lia.
  + unfold E2. rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), P1a. apply unsigned_lit_small. clear -XR; unfold kStoreBlockSize in XR; lia.
- apply regs_preserved_intro.
  all: lazymatch goal with
       | |- getr (ms_regs ?m) 2%bv = _ =>
           rewrite (st_ok_reg_denot (w_H W2) E2 _ m 2%bv HS2);
           lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end;
           cbn [sv_denot]; unfold E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), R2b, unsigned_lit_small by lia;
           unfold sp1, spZ; replace (bv_unsigned (getr regs 2%bv) - 16 + 16) with (bv_unsigned (getr regs 2%bv)) by lia; apply Z_to_bv_bv_unsigned
       | |- getr (ms_regs ?m) 8%bv = _ => rewrite (reg_at E2 _ m 8%bv 32 HS2 ltac:(vm_compute; reflexivity)); reflexivity
       | |- getr (ms_regs ?m) ?r = _ =>
           rewrite (reg_at E2 _ m r (Z.to_nat (bv_unsigned r)) HS2 ltac:(vm_compute; reflexivity));
           unfold E2; rewrite (ew_Ereg_nat regs2 _ (Z.to_nat (bv_unsigned r)) r eq_refl);
           rewrite (PB r ltac:(apply cs_byb; vm_compute; reflexivity));
           rewrite (reg_at E0 _ msC r (Z.to_nat (bv_unsigned r)) HSC ltac:(vm_compute; reflexivity));
           apply EWr; [reflexivity | intros X; discriminate]
       end.
- unfold s_total. rewrite Z.add_0_r. apply VF; [unfold TFIB_STORE; lia | unfold TFIB_STORE; cbn; lia | | exact Mtot].
  intros k Hk. split; [unfold sp1, spZ, BIC_STK, MNR_STK in *; unfold kHighMemBeg, TFIB_STORE in *; lia|]. split; [apply XT; lia|]. split; lia.
- apply VF; [clear -G5; unfold kHighMemBeg in G5; lia | clear -G6; unfold kHighMemEnd in G6; lia | | exact Midx].
  intros k Hk. unfold sp1, spZ, BIC_STK, MNR_STK in *. unfold kHighMemBeg, kHighMemEnd, TFIB_STORE in *. repeat split; lia.
- rewrite ES in P1c. exact P1c.
- intros a Ha. apply PPR. exact (MREL_present _ a HI3 Ha).
- left. rewrite ES in PAL, PMX.
  refine (conj H0 (conj P2a (conj P2b (conj P3a (conj P3b (conj P4 (conj HWA (conj HWH (conj _ (conj PT1 (conj _ (conj _ (conj _ (conj _ (conj _ (conj PAL (conj PMX (conj _ (conj eq_refl (conj P6 _)))))))))))))))))))).
  + destruct PIO as (I1 & I2 & I3 & I4). exact (conj I1 (conj I2 (conj I3 I4))).
  + intros e He. exact (PT2 e He).
  + destruct PM1 as [mat2 EM2]. exists mat'. rewrite EM2, wvb_collapse.
    try rewrite nr_wvb; try rewrite wvb_collapse; reflexivity.
  + rewrite m_vmmaps_wvb, PM2. try rewrite mm_vmmaps_wvb. reflexivity.
  + rewrite m_vm_lazy_wvb, PM3. try rewrite m_vm_lazy_wvb. reflexivity.
  + rewrite eu_wvb, PM4. try rewrite eu_wvb. reflexivity.
  + intros a N1 N2 N3 N4 N5. transitivity (ms_mem msC a).
    * apply P5; [rewrite SP1; intros X; apply N1; unfold sp1 in X; lia | exact N2 | | ];
        rewrite ES; unfold ss_alloc, s_block0, bi0_mtx in *; intros X; [apply N3 | apply N4]; lia.
    * apply (proj1 HI3); [intros X; apply N1; unfold sp1 in X; unfold BIC_STK, MNR_STK in *; lia | intros X; apply N3; unfold s_block0; lia | exact N5].
  + rewrite ?m_vmmaps_wvb in P7. exact P7.
Qed.
Lemma alloc_walk : SRr_refusable W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_StackStore_Alloc) mem (seg_rom tfibsegs)) md)
  (alloc_post layout_grow_kd B W ly S regs mem md F cnt idxp alloc).
Proof.
apply alloc_entry_node. fold regs1. fold ms0.
destruct (Z.eq_dec (ly_SB ly) 0) as [H0|H0]; [exact (first_use_arm H0) | exact (mapped_arm H0)].
Qed.
End call.
Theorem tfib_alloc_ok : tfib_alloc_spec layout_grow_kd B.
Proof.
intros W ly S regs mem md F cnt idxp alloc. cbn zeta. intros. eapply alloc_walk; eassumption.
Qed.
End kdp.
End gp.
