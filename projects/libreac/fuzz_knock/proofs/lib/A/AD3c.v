(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written by a Theorem Labs lane, the S3 prover, for another Theorem Labs lane: the
   statement and proof of __sanitizer::StackStore::BlockInfo::Create (0x6f400-0x6f4b4, 45 insns, fuzz_knock.asan sha256
   61768cf4739b...) on knock's first-use path, block 0 (the store block not yet mapped), in the cell-level shape
   a Theorem Labs lane froze: P1-P5 of a Theorem Labs lane's ruling depot-NB-SB-ownership.md with X = (x, kStoreBlockSize) and
   cellX = AStore s_block0, P6 as a Theorem Labs lane's set_ly_SB plus the first Put's layout growth (layout_grow_kd), the exact cells
   Create writes, and no kernel ARm (ARm returns only after Put's insertion). The callee MmapNoReserveOrDie
   (0x647b0, a Theorem Labs lane's S4) is consumed by name: AD3d's mnr_contract at MNR_STK, closed by AD3d's mnr_holds.
   rule 24: proves function StackStore::BlockInfo::Create (reuse search: see (internal path)). *)

(* THE CODE (A image; a0 = this = &blocks_[i], a1 = store)
     0x6f400 addi sp,sp,-0x20; sd ra,0x18(sp); sd s0,0x10(sp); sd s1,8(sp); sd s2,0(sp)
     0x6f414 mv s1,a0; addi s0,a0,0xc                  s0 = &mtx_ (store + 28 for block 0)
     0x6f41c lr.w.aq / sc.w loop on the word at s0     mtx_ := 1, the word's other bytes kept
     0x6f444 andi a0,a4,0xff; bnez a0,0x6f498          held -> StaticSpinMutex::LockSlow (0x64124), not taken here
     0x6f44c ld a0,0(s1); bnez a0,0x6f478              data_ != 0 -> unlock, return data_ (not first use)
     0x6f454 addi a1,a1,8; lui a0,0x800; amoadd.d zero,a0,(a1)     allocated_ += 0x800000
     0x6f460 a1 := 0x202d2 ("StackStore"); a0 := 0x800000; jal MmapNoReserveOrDie 0x647b0 (ra 0x6f470)
     0x6f470 fence rw,w; sd a0,0(s1); fence rw,w       data_ := x
     0x6f47c sb zero,0(s0)                             mtx_ := 0
     0x6f480 restore ra/s0/s1/s2; addi sp,sp,0x20; ret (a0 = x)
   A delivered proof of another library states the same cells; this file states
   them on knock's addresses.

   THE PROOF (Section w, create_walk): the symbolic executor runs 0x6f400 -> the jal at 0x6f46c (C_SS_CALL: frame
   saved, allocated_ = alloc + 2^23, mutex word 1, a0 = 2^23, ra = 0x6f470); mnr_holds (AD3d's mnr_contract) is bound
   through SRr_refusable_bind; st_ok_after_call re-seats the state at 0x6f470 in the callee's world (H agrees with
   W's outside X, which the frame and store cells avoid by md_takes); the run to the ret at 0x6f494 writes data_ := x
   and mtx_ := 0; SRr_ret_at returns. P2's in_app comes from grant_in_app (band md_takes, P3, ceil_of_top).

   a Theorem Labs lane approved this statement; amendment 1 added md_takes's positive size, the premises
   md_takes md (as_store B, 32) and kHighMemBeg <= ly_stk_lo ly, and the Section hypothesis mnr_stk_ge.
   The refused arm is excluded by premise (md_room): a real refusal reaches ReportMmapFailureAndDie (0x5e3f4), which
   ends the run (SIGABRT), neither the normal exit nor a refused halt form.

   Where the amendment's premises come from at Put's call site (today's at-main kernel facts):
   - md_takes md (as_store B, 32): (as_store B, 32) is one of asyms_areas (YG0f.v:254), each inside one of
     as_owned_static (aso_cover, YG0f.v:261), each inside ly_img (am_static_img, YG0n.v:406); every byte of ly_img lies
     in segments_reserved (al_imgcov, YG0n.v:627-628) = vm_reserved (al_reserved, YG0n.v:609); 32 > 0.
   - kHighMemBeg <= ly_stk_lo ly: lo_top (YG0f.v:443-445), last conjunct.
   - mnr_stk_ge (amendments 1-7; amendment 8 replaces mnr_stk by AD3d's MNR_STK = 104, so it is gone).
   - md_takes's new [0 < snd e]: the fixed sizes of ext_but_SB are positive constants; the stack extent by lo_top
     (ly_stk_lo <= ly_bot < ly_top <= ly_stk_hi); ly_img by lo_img (YG0f.v:441); ly_extra by lo_extra
     (YG0f.v:447-450); sec_extents by sec_map_size n = round_up (needed_size n) kPage + kPage (YG00.v:76);
     band_maps are positive constants.
   - amendment 7, eager_used md + A_bytes (w_A W) + kStoreBlockSize <= vm_limit (m_vmmaps md): the budget
     allow_expose (YG0b.v:420-426) needs for P4's apresent over the full store block; at Put's call site it is S9's
     headroom (8 MiB against the limit), kept along the walk by commit_AI (YG0b.v:285) and vm_backing_used_le
     (YA09.v:89-93). a Theorem Labs lane measured S4's charge as + n once, so the term stays + kStoreBlockSize.

   AMENDMENT 8 (approved as drafted): S4 is consumed BY
   NAME from a Theorem Labs lane's lib/A/AD3d.v:
   Require Export AD3d; the callee's contract mnr_contract MNR_STK is closed by a Theorem Labs lane's mnr_holds (AD3d.v:1100, Qed),
   so it is no Section hypothesis. This file's copies of SRr_refusable,
   SRr_refusable_SRr, md_takes, md_room, MNR_PSC_GOT, MNR_PSC, MNR_CF_GOT, MNR_CF and mnr_cells are deleted: AD3d's
   are the same text. The stand-in tfib_mnr_spec and the Section variable
   mnr_stk (with mnr_stk_ge) are deleted: BIC_STK = 32 + MNR_STK = 136.
   - Create's post: exposure as mnr_contract states it (allow_expose YG0b.v:420-426): w_A W' = (x, x + kStoreBlockSize)
     :: w_A W and w_H W' = w_H W outside X; it replaces w_H W' = w_H W. Inside X, H is false by P4's apresent.
     P1-P6 and the cells are unchanged. Model post (note 6): exactly AD3d's model clauses (AD3d.v:189-200:
     same_io, md_takes md' X, take-preservation, and the NORESERVE model: exists mat, md' = with_vm_backing
     (m_vm_lazy NR) mat NR with NR = YK0x.mmap_model_noreserve x n md, m_vmmaps md' = m_vmmaps (mmap_model x n md),
     m_vm_lazy md' = (x, n) :: m_vm_lazy md, eager_used md' = eager_used md), carried through Create's own steps:
     Create's call and return wrap the model in with_vm_backing with its own lazy list, which keeps all four
     (wvb_collapse YA0o.v:23, nr_wvb AD3d.v:437, m_vmmaps_wvb / m_vm_lazy_wvb YK04.v:781-784).
   - Create's pre gains what mnr_contract asks that the pre did not give:
     YK0g.ivs_wf (vm_maps (m_vmmaps md)) (AD3d.v:166-170), ly_stk_hi ly <= kHighMemEnd (for the callee's
     sp <= kHighMemEnd, AD3d.v:172), Forall (md_takes md) mnr_cell_extents (AD3d.v:136, :174); and, for P2's in_app,
     YM05.ceil_of_top (alloc_top (m_vmmaps md)) (mnr_contract gives grant_ok_na_pin, 4096 <= x and freshness, not
     in_app; AD3d.v:151-153). The rest of mnr_contract's pre follows from the pre as it is (sp' = sp - 32 is the
     callee's sp; create_walk's bind):
     . md_room, the budget, the band's presence: the same premises at the same model (with_vm_backing keeps m_vmmaps).
     . AD3d.v:174 md_takes md (sp' - 104, 104): a sub-extent of TEXT's ext_but_SB stack entry (ly_stk_lo,
       ly_stk_hi - ly_stk_lo), since ly_stk_lo <= sp - BIC_STK = sp' - 104 and sp' < sp <= ly_stk_hi (takes_sub).
     . AD3d.v:172 kHighMemBeg <= sp' - 104: kHighMemBeg <= ly_stk_lo <= sp - BIC_STK = sp' - 104.
     . AD3d.v:172 sp' <= kHighMemEnd: sp' < sp <= ly_stk_hi <= kHighMemEnd.
     . TFIB_IMG_END <= sp' - 104 (not asked by AD3d): TFIB_IMG_END = 0x5f3000
       (AF0x.v:26, YImgTop.v:5) < kHighMemBeg (YG0f.v:14) <= sp' - 104.
   - Layout step: layout_le stays exactly today's; the first Put's growth is a new two-argument relation
     layout_grow with intro lemma ly_SB ly = 0 -> layout_grow ly (set_ly_SB ly sb). P6 is stated against the one
     placeholder layout_grow_kd / kd_grow_SB of that shape (AD3j's kd_inst instantiates them with layout_grow / layout_grow_SB, YG0f.v:99, :109); the
     first-use arm guard stays the cell data_ = 0 and ly_SB ly = 0.
   Discharge at Put's call site (each must also cross S7's nodes-map grant, which runs between Put's entry and here):
   - YK0g.ivs_wf (vm_maps (m_vmmaps md)): amwf / MWF at Put's entry (YG0b.v:128, amwf_MWF YG0b.v:147); across S7's
     grant by ivs_wf_cons (YK0g.v:139) for the granted interval [inference: S7's post must state it].
   - ly_stk_hi ly <= kHighMemEnd: lo_top (YG0f.v:444), as for amendment 1's kHighMemBeg <= ly_stk_lo ly.
   - Forall (md_takes md) mnr_cell_extents: both cells, 0x965c0 and 0x1300f8, lie in [0x10000, 0x5f3000), which
     vm_reserved = segments_reserved tfibsegs covers without a gap (al_reserved YG0n.v:609; AFia.v:132-133); across
     S7's grant by its take-preservation.
   - YM05.ceil_of_top (alloc_top (m_vmmaps md)): from the at-main ledger, al_top (YG0n.v:626) of ALedger, carried to
     Put; alloc_top reads only vm_init_sp (LPS State.v:2737), which a grant does not change [inference: S7's post must
     state m_vmmaps' vm_init_sp or alloc_top].

   AMENDMENT 11: the post's last conjunct P7 states X fresh against every map of Create's entry
   model, Forall (fun q => zdisjoint (x, kStoreBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_maps
   (m_vmmaps md)), so the first Put's grants are fresh against the whole model, not only the placement list. Proof:
   the vm_maps half (Forall_app) of mnr_contract's freshness over vm_reserved ++ vm_maps (tail_ok's Q5); the call's
   model is md up to with_vm_backing, which keeps m_vmmaps (wvb_vmmaps). *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0j YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0 AB1q AB1w AF0m AF0x AFl0 AFek AFel AFl3.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Export AD3d.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YK0g YK0x YK0v.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require AFem.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition SSc : Z := 0x170408.
Definition C_S : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition C_ALLOC : YP09.region := cell8 (SSc + 8) 32.
Definition C_DATA : YP09.region := YP09.mkRegion None (SSc + 16) (SSc + 24) (SSc + 16) (SSc + 24) [YP09.mkChunk (SSc + 16) (CVal 8 (SLit 0))].
Definition C_MTX : YP09.region := YP09.mkRegion None (SSc + 28) (SSc + 32) (SSc + 28) (SSc + 32) [YP09.mkChunk (SSc + 28) (CVal 4 (SLit 0))].
Definition C_REG0 : smem := [C_S; C_ALLOC; C_DATA; C_MTX].
Definition C_SR0 : list sv := sr_set (sr_set sr_atoms 10%bv (SLit (SSc + 16))) 11%bv (SLit SSc).
Definition C_FF0 : facts := mkFacts [(2%nat, mkAF (kHighMemBeg + 32) (2 ^ 64 - 16) 4); (32%nat, u64f)] [] [].
Definition C_SS0 : sstate := mkSS 0x6f400 C_SR0 C_REG0 None C_FF0.
Definition C_SS_CALL : sstate := Eval vm_compute in fst (sym_runN_sh tfibsegs tfibtbl_rtB FUEL C_SS0).
(* after the call: keep the stack frame, allocated_ and data_; the mutex keeps only its low byte (written by sb at
   0x6f47c); its other three bytes leave the windows, so the tail's frame keeps them. *)
Definition C_MTXB : YP09.region := YP09.mkRegion None (SSc + 28) (SSc + 29) (SSc + 28) (SSc + 29) [].
Definition C_RS1 : smem := Eval vm_compute in firstn 3 (ss_mem C_SS_CALL) ++ [C_MTXB].
Definition C_T1 : sstate := Eval vm_compute in ss_after_call C_SS_CALL C_RS1 33 0x6f470.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma SRr_refusable_bind : forall W c (Q R : world tfibsegs -> config -> Prop),
  SRr_refusable W c Q -> (forall W' c', wle W W' -> Q W' c' -> SRr tfibsegs W' c' R) -> SRr_refusable W c R.
Proof.
  intros W c Q R H HK. unfold SRr_refusable in *. eapply SRr_mono; [exact H|].
  intros W1 c1 Hle1 (I & nx & sp & i0 & Hn & Ht & Hs & Hz & Hk).
  exists I, nx, sp, i0. split; [exact Hn|]. split; [exact Ht|]. split; [exact Hs|]. split; [exact Hz|].
  intros i Hi. eapply SRr_bind; [exact (Hk i Hi)|].
  intros W2 c2 Hle2 HQ. apply HK; [eapply wle_trans; eassumption | exact HQ].
Qed.


(* a Theorem Labs lane's helper, verbatim (internal path:24-26). *)
Definition set_ly_SB (ly : alayout) (sb : Z) : alayout :=
ALayout (ly_prim ly) (ly_space ly) (ly_Q ly) (ly_T ly) (ly_C ly) (ly_F ly) (ly_NB ly) sb (ly_top ly)
(ly_stk_lo ly) (ly_stk_hi ly) (ly_tsd ly) (ly_tr0 ly) (ly_extra ly) (ly_D ly) (ly_vis0 ly) (ly_img ly) (ly_sec ly).

(* static_extents ly (YG0f.v:388-389) without the store block's own entry (ly_SB ly, kStoreBlockSize): the extents
   the new block must avoid. With ly_SB ly = 0 that entry is the empty extent (4096, 0) (YG0f.v:387).
   amendment 5: the nodes map's entry is listed only once it is mapped (a Theorem Labs lane's sentinel ly_NB ly = 0). *)
Definition ext_but_SB (ly : alayout) : list (Z * Z) := [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize); (ly_F ly, kFakeStackSize)] ++ (if ly_NB ly =? 0 then [] else [(ly_NB ly, kNodesBlockSize)]) ++ [(ly_C ly, 256); (ly_D ly, 4096); (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly].

Section kd.
(* PLACEHOLDER for the layout step: the first Put's growth is a new relation layout_grow ly ly' with
   intro lemma ly_SB ly = 0 -> layout_grow ly (set_ly_SB ly sb); layout_le stays exactly today's. ONE Section variable
   of that shape, which AD3j's kd_inst instantiates with layout_grow (YG0f.v:99). Satisfiable: layout_grow_kd := fun _ _ => True. *)
Variable layout_grow_kd : alayout -> alayout -> Prop.
Hypothesis kd_grow_SB : forall ly sb, ly_SB ly = 0 -> layout_grow_kd ly (set_ly_SB ly sb).
(* S4, MmapNoReserveOrDie: AD3d's mnr_contract MNR_STK, used through mnr_holds (AD3d.v:1100) in create_walk. *)
(* Create's frame (0x6f400 addi sp,sp,-0x20) above MmapNoReserveOrDie's touched band (MNR_STK = 104, AD3d.v:54). *)
Definition BIC_STK : Z := 32 + MNR_STK.
(* Cell offsets in StackStore (as_store B): allocated_ at 8, blocks_[0] = BlockInfo {data_ 16; stored_ 24; mtx_ 28}. *)
Definition ss_alloc : Z := 8.
Definition bi0_mtx : Z := 28.

(* StackStore::BlockInfo::Create(&blocks_[0], store) on the first-use path. PRE: the cells Create reads (data_ = 0,
   the mutex word 0, allocated_ = alloc), the callee's cells, the stack window, room for the grant, the budget, the
   model map list well formed, alloc_ceiling as alloc_top's page floor (for in_app), and that the model takes the
   callee's two post-ecall cells and every extent the new block must avoid; ly_SB ly = 0 (the layout step's
   placeholder guard, held by the owner).
   POST, normal exit, [exists x] (the mmap result): exposure as mnr_contract (X joins w_A, H unchanged outside X);
   P1 return x, cellX (data_) = x; P2 placement; P3 fresh; P4 zero and present; P5 frame: memory unchanged
   outside X, cellX, allocated_, the mutex word and the stack window, allocated_ = alloc + 0x800000, the mutex word
   back to 0 (s_total and stored_ untouched, by the frame), the model takes X and keeps what it took (so later fresh
   blocks and the ARm rebuild after Put can avoid X); P6 ly' = set_ly_SB ly x and layout_grow_kd ly ly' (placeholder);
   P7 X is fresh against every map of the entry model (amendment 11).
   No kernel ARm: Alloc has already bumped s_total (0x6ea2c) when it calls Create, so ARm holds neither here nor at
   Create's exit; it returns after Put's insertion. The refused arm is SRr_refusable's. *)
Definition tfib_blockinfo_create_spec (B : asyms) : Prop :=
  forall (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte)
         (md : Model) (alloc : Z),
  let H := w_H W in let m := mrestrict H mem in let sp := spZ regs in let SS := as_store B in
  ly_SB ly = 0 ->
  getr regs 10 = Z_to_bv 64 (SS + s_block0) -> getr regs 11 = Z_to_bv 64 SS -> YK0s.ret_ok (getr regs 1) ->
  val_mem tfibsegs m (SS + s_block0) 8 0 -> val_mem tfibsegs m (SS + bi0_mtx) 4 0 ->
  val_mem tfibsegs m (SS + ss_alloc) 8 alloc ->
  mnr_cells m -> md_room md kStoreBlockSize -> eager_used md + A_bytes (w_A W) + kStoreBlockSize <= vm_limit (m_vmmaps md) ->
  YK0g.ivs_wf (vm_maps (m_vmmaps md)) -> YM05.ceil_of_top (alloc_top (m_vmmaps md)) -> Forall (md_takes md) mnr_cell_extents ->
  sp mod 16 = 0 -> kHighMemBeg <= ly_stk_lo ly -> ly_stk_lo ly <= sp - BIC_STK -> sp <= ly_stk_hi ly ->
  ly_stk_hi ly <= kHighMemEnd ->
  (forall a, sp - BIC_STK <= a < sp -> apresent H mem a) ->
  md_takes md (SS, 32) ->
  Forall (md_takes md) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) ->
  (forall a, aclient_byte B ly S a -> md_takes md (a, 1)) ->
  SRr_refusable W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_StackStore_BlockInfo_Create) mem (seg_rom tfibsegs)) md)
    (fun W' c' => exists x regs' mem' md',
      let m' := mrestrict (w_H W') mem' in
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
      (* exposure *) w_A W' = (x, x + kStoreBlockSize) :: w_A W /\
               (forall a : word, ~ (x <= bv_unsigned a < x + kStoreBlockSize) -> w_H W' a = w_H W a) /\
      (* P1 *) getr regs' 10 = Z_to_bv 64 x /\ regs_preserved regs regs' /\ val_mem tfibsegs m' (SS + s_block0) 8 x /\
      (* P2 *) YG0f.page_aligned x /\ in_app x kStoreBlockSize /\
      (* P3 *) Forall (zdisjoint (x, kStoreBlockSize)) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) /\
               (forall a, aclient_byte B ly S a -> ~ in_zr a (x, kStoreBlockSize)) /\
      (* P4 *) (forall i, 0 <= i < kStoreBlockSize ->
                 apresent (w_H W') mem' (x + i) /\ aview tfibsegs (w_H W') mem' (x + i) = Some 0) /\
      (* P5 *) (forall a : word, ~ (sp - BIC_STK <= bv_unsigned a < sp) -> ~ (x <= bv_unsigned a < x + kStoreBlockSize) ->
                 ~ (SS + ss_alloc <= bv_unsigned a < SS + s_block0 + 8) -> ~ (SS + bi0_mtx <= bv_unsigned a < SS + bi0_mtx + 4) ->
                 mem' a = mem a) /\
               val_mem tfibsegs m' (SS + ss_alloc) 8 ((alloc + kStoreBlockSize) mod 2 ^ 64) /\
               val_mem tfibsegs m' (SS + bi0_mtx) 4 0 /\
               (forall a, apresent H mem a -> apresent (w_H W') mem' a) /\ same_io md md' /\
               md_takes md' (x, kStoreBlockSize) /\ (forall e, md_takes md e -> md_takes md' e) /\
      (* model, exactly (amendment 8 note 6; AD3d.v:195-200 carried through Create's steps) *)
               (exists mat, md' = with_vm_backing
                   (m_vm_lazy (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md)) mat
                   (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md)) /\
               m_vmmaps md' = m_vmmaps (YK0v.mmap_model (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md) /\
               m_vm_lazy md' = (Z_to_bv 64 x, Z_to_bv 64 kStoreBlockSize) :: m_vm_lazy md /\
               eager_used md' = eager_used md /\
      (* P6 *) layout_grow_kd ly (set_ly_SB ly x) /\
      (* P7 *) Forall (fun q => zdisjoint (x, kStoreBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_maps (m_vmmaps md))).
Section w.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variables (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (alloc : Z).
#[local] Abbreviation Hd := (w_H W).
#[local] Abbreviation m0 := (mrestrict (w_H W) mem).
#[local] Abbreviation sp := (spZ regs).
Hypothesis HSB : ly_SB ly = 0.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 (as_store B + s_block0).
Hypothesis R11 : getr regs 11 = Z_to_bv 64 (as_store B).
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis VD : val_mem tfibsegs m0 (as_store B + s_block0) 8 0.
Hypothesis VM : val_mem tfibsegs m0 (as_store B + bi0_mtx) 4 0.
Hypothesis VA : val_mem tfibsegs m0 (as_store B + ss_alloc) 8 alloc.
Hypothesis MC : mnr_cells m0.
Hypothesis RM : md_room md kStoreBlockSize.
Hypothesis HBUD : eager_used md + A_bytes (w_A W) + kStoreBlockSize <= vm_limit (m_vmmaps md).
Hypothesis HIVS : YK0g.ivs_wf (vm_maps (m_vmmaps md)).
Hypothesis HCT : YM05.ceil_of_top (alloc_top (m_vmmaps md)).
Hypothesis TMC : Forall (md_takes md) mnr_cell_extents.
Hypothesis Hsp16 : sp mod 16 = 0.
Hypothesis Hhigh : kHighMemBeg <= ly_stk_lo ly.
Hypothesis Hlo : ly_stk_lo ly <= sp - BIC_STK.
Hypothesis Hhi : sp <= ly_stk_hi ly.
Hypothesis HstkE : ly_stk_hi ly <= kHighMemEnd.
Hypothesis P_stk : forall a, sp - BIC_STK <= a < sp -> apresent Hd mem a.
Hypothesis TSS : md_takes md (as_store B, 32).
Hypothesis TEXT : Forall (md_takes md) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps).
Hypothesis TCL : forall a, aclient_byte B ly S a -> md_takes md (a, 1).

Lemma MNR_STK_pos : 0 < MNR_STK. Proof. unfold MNR_STK. lia. Qed.
Lemma ESS : as_store B = SSc. Proof. exact (ts_store B HB). Qed.
Lemma sp_range : 0 <= sp < 2 ^ 64. Proof. apply u64_range. Qed.
Lemma sp_facts : 17594333495328 <= sp - MNR_STK /\ sp <= 2 ^ 64 - 16.
Proof.
  pose proof sp_range as SR. pose proof Hhigh as HH. pose proof Hlo as HL. unfold BIC_STK in HL. unfold kHighMemBeg in HH. split; [lia|].
  pose proof Hsp16 as H16. apply Z.mod_divide in H16 as [q Hq]; [|lia]. lia.
Qed.
Definition XW : list word := [Z_to_bv 64 (alloc mod 2 ^ 64)].
Definition E0 : env := Ereg regs XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs r.
Proof. intros Hk. exact (ew_Ereg_nat regs XW k r Hk). Qed.
Lemma E2 : bv_unsigned (ew E0 2) = sp. Proof. rewrite (Er 2 2%bv eq_refl). reflexivity. Qed.
Lemma E32 : ew E0 32 = Z_to_bv 64 (alloc mod 2 ^ 64). Proof. reflexivity. Qed.

Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) C_REG0.
Proof.
  pose proof sp_facts as [SF1 SF2]. pose proof sp_range as SR. pose proof MNR_STK_pos as MP.
  pose proof ESS as ES. rewrite ES in VD, VM, VA. unfold ss_alloc, bi0_mtx, s_block0 in VD, VM, VA.
  unfold C_REG0. apply Forall_cons.
  { apply (region_ok_stack tfibsegs E0 m0 2 sp (-32) E2); [lia | lia |].
    intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, YImgTop.IMG_TOP, kHighMemBeg in *; lia|].
    apply P_stk. pose proof MNR_STK_pos. unfold BIC_STK. lia. }
  apply Forall_cons.
  { apply (AFem.region_ok_cell8 regs 0 E0 m0 (SSc + 8) 32 (alloc mod 2 ^ 64)).
    - apply (AFem.val_mem_mod64 regs 0). exact VA.
    - exact E32.
    - apply Z.mod_pos_bound. lia.
    - unfold SSc. lia.
    - unfold SSc, YImgTop.IMG_TOP. lia. }
  apply Forall_cons.
  { unfold region_ok, C_DATA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold SSc; lia|]. split; [unfold SSc; lia|].
    split; [intros o Ho; apply (AFem.rw_writable regs 0); unfold SSc, YImgTop.IMG_TOP in *; lia|].
    apply Forall_cons; [| apply Forall_nil].
    apply (chunk_ok_val tfibsegs E0 m0 0 (SSc + 16) 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_l. exact VD. }
  apply Forall_cons; [| apply Forall_nil].
  { unfold region_ok, C_MTX. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold SSc; lia|]. split; [unfold SSc; lia|].
    split; [intros o Ho; apply (AFem.rw_writable regs 0); unfold SSc, YImgTop.IMG_TOP in *; lia|].
    apply Forall_cons; [| apply Forall_nil].
    apply (chunk_ok_val tfibsegs E0 m0 0 (SSc + 28) 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_l. exact VM. }
Qed.

Lemma PAIRS0 : pairwise_disjoint E0 C_REG0.
Proof.
  pose proof sp_facts as [SF1 SF2]. pose proof sp_range as SR. pose proof MNR_STK_pos as MP.
  apply pairwise_disjoint_of_extents. unfold C_REG0, C_S, C_ALLOC, C_DATA, C_MTX, cell8, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, SSc. cbn [fst snd].
  unfold kHighMemBeg in *. repeat split; lia.
Qed.

Lemma SEED : st_ok tfibsegs E0 C_SS0 (restrict Hd (mkst regs (Z_to_bv 64 0x6f400) mem (seg_rom tfibsegs))).
Proof.
  pose proof sp_facts as [SF1 SF2]. pose proof sp_range as SR. pose proof MNR_STK_pos as MP.
  rewrite restrict_mkst_fx. unfold C_SS0, C_SR0. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; rewrite R11, ESS; reflexivity].
    apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; rewrite R10, ESS; reflexivity].
  - vm_compute. reflexivity.
  - exact REG0_ok.
  - exact PAIRS0.
  - split; [| split; exact I]. cbn [f_atoms C_FF0 atoms_ok]. split; [| split; [| exact I]].
    + apply (AFem.AFo regs 0 E0 2 sp); [rewrite (Er 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned | exact SR | unfold kHighMemBeg; lia | exact Hsp16 | lia].
    + apply (AFem.AFo regs 0 E0 32 (alloc mod 2 ^ 64)); [exact E32 | apply Z.mod_pos_bound; lia | unfold u64f; cbn; pose proof (Z.mod_pos_bound alloc (2 ^ 64) ltac:(lia)); lia | apply Z.mod_1_r | lia].
Qed.

(* the spec's post for this instance *)
Definition POST3 : world tfibsegs -> config -> Prop :=
  fun W' c' => exists x regs' mem' md',
      let m' := mrestrict (w_H W') mem' in
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
      w_A W' = (x, x + kStoreBlockSize) :: w_A W /\
      (forall a : word, ~ (x <= bv_unsigned a < x + kStoreBlockSize) -> w_H W' a = w_H W a) /\
      getr regs' 10 = Z_to_bv 64 x /\ regs_preserved regs regs' /\ val_mem tfibsegs m' (as_store B + s_block0) 8 x /\
      YG0f.page_aligned x /\ in_app x kStoreBlockSize /\
      Forall (zdisjoint (x, kStoreBlockSize)) (ext_but_SB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps) /\
      (forall a, aclient_byte B ly S a -> ~ in_zr a (x, kStoreBlockSize)) /\
      (forall i, 0 <= i < kStoreBlockSize ->
         apresent (w_H W') mem' (x + i) /\ aview tfibsegs (w_H W') mem' (x + i) = Some 0) /\
      (forall a : word, ~ (spZ regs - BIC_STK <= bv_unsigned a < spZ regs) -> ~ (x <= bv_unsigned a < x + kStoreBlockSize) ->
         ~ (as_store B + ss_alloc <= bv_unsigned a < as_store B + s_block0 + 8) ->
         ~ (as_store B + bi0_mtx <= bv_unsigned a < as_store B + bi0_mtx + 4) ->
         mem' a = mem a) /\
      val_mem tfibsegs m' (as_store B + ss_alloc) 8 ((alloc + kStoreBlockSize) mod 2 ^ 64) /\
      val_mem tfibsegs m' (as_store B + bi0_mtx) 4 0 /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\ same_io md md' /\
      md_takes md' (x, kStoreBlockSize) /\ (forall e, md_takes md e -> md_takes md' e) /\
      (exists mat, md' = with_vm_backing
          (m_vm_lazy (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md)) mat
          (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md)) /\
      m_vmmaps md' = m_vmmaps (YK0v.mmap_model (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) md) /\
      m_vm_lazy md' = (Z_to_bv 64 x, Z_to_bv 64 kStoreBlockSize) :: m_vm_lazy md /\
      eager_used md' = eager_used md /\
      layout_grow_kd ly (set_ly_SB ly x) /\
      Forall (fun q => zdisjoint (x, kStoreBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_maps (m_vmmaps md)).

Lemma win_REG0 : forall a, in_wrange E0 C_REG0 a ->
  (sp - 32 <= a < sp) \/ (SSc + 8 <= a < SSc + 24) \/ (SSc + 28 <= a < SSc + 32).
Proof.
  intros a Hw. destruct (in_wrange_windows E0 C_REG0 a Hw) as (b & lo & hi & Hin & Hr).
  vm_compute in Hin.
  destruct Hin as [Hq|[Hq|[Hq|[Hq|[]]]]]; injection Hq as <- <- <-; cbn [base_val] in Hr;
  [rewrite E2 in Hr; left; lia | right; left; unfold SSc; lia | right; left; unfold SSc; lia | right; right; unfold SSc; lia].
Qed.

Lemma frameA : forall m1 : word -> option byte, frame_of E0 C_REG0 mem m1 ->
  forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> ~ (SSc + 8 <= bv_unsigned x < SSc + 24) ->
  ~ (SSc + 28 <= bv_unsigned x < SSc + 32) -> m1 x = mem x.
Proof.
  intros m1 HF x N1 N2 N3. apply HF. intros Hw. destruct (win_REG0 _ Hw) as [Q|[Q|Q]]; [exact (N1 Q) | exact (N2 Q) | exact (N3 Q)].
Qed.

Lemma low_kept : forall m1 : word -> option byte, (forall x : word, bv_unsigned x < SSc + 8 -> m1 x = mem x) ->
  forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= SSc + 8 -> val_mem tfibsegs m0 a n v -> val_mem tfibsegs (mrestrict Hd m1) a n v.
Proof.
  intros m1 HK a n v Ha Hn Hv. apply (val_mem_frame Hd mem m1 a n v); [| exact Hv].
  intros k Hk. apply HK. rewrite unsigned_lit_small by (unfold SSc in *; lia). lia.
Qed.

Lemma mnr_cells_kept : forall m1 : word -> option byte, (forall x : word, bv_unsigned x < SSc + 8 -> m1 x = mem x) ->
  mnr_cells (mrestrict Hd m1).
Proof.
  intros m1 HK. pose proof MC as (M1 & M2 & M3 & (f & M4 & M5) & M6).
  unfold mnr_cells, MNR_PSC_GOT, MNR_PSC, MNR_CF_GOT, MNR_CF in *.
  split; [apply (low_kept m1 HK); [lia | unfold SSc; cbn; lia | exact M1]|].
  split; [apply (low_kept m1 HK); [lia | unfold SSc; cbn; lia | exact M2]|].
  split; [apply (low_kept m1 HK); [lia | unfold SSc; cbn; lia | exact M3]|].
  split; [exists f; split; [apply (low_kept m1 HK); [lia | unfold SSc; cbn; lia | exact M4] | exact M5]|].
  apply (low_kept m1 HK); [lia | unfold SSc; cbn; lia | exact M6].
Qed.

Lemma call_regs : forall ms, st_ok tfibsegs E0 C_SS_CALL (restrict Hd ms) ->
  getr (ms_regs ms) 10 = Z_to_bv 64 8388608 /\ getr (ms_regs ms) 1 = Z_to_bv 64 455792 /\ spZ (ms_regs ms) = sp - 32.
Proof.
  intros ms HS. pose proof sp_facts as [SF1 SF2]. pose proof MNR_STK_pos as MP.
  split; [rewrite (st_ok_reg_denot Hd E0 C_SS_CALL ms 10 HS); reflexivity|].
  split; [rewrite (st_ok_reg_denot Hd E0 C_SS_CALL ms 1 HS); reflexivity|].
  unfold spZ at 1. rewrite (st_ok_reg_denot Hd E0 C_SS_CALL ms 2 HS).
  change (sr_get (ss_regs C_SS_CALL) 2%bv) with (SOff 2 (-32)). cbn [sv_denot]. rewrite E2.
  apply unsigned_lit_small. lia.
Qed.

Lemma wvb_vmmaps : forall mat, m_vmmaps (with_vm_backing (m_vm_lazy md) mat md) = m_vmmaps md /\
  eager_used (with_vm_backing (m_vm_lazy md) mat md) = eager_used md.
Proof.
  intros mat. pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as F.
  destruct F as (_ & F2 & _). split; [exact F2|].
  pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as G. tauto.
Qed.

(* amendment 10: md_takes' second disjunct is page_floor (alloc_top) <= fst e, so freshness against it needs the grant
   to end at or below page_floor (alloc_top), which AD3d's grant_end_page_floor (AD3d.v:98-103) gives from page
   alignment. *)
Lemma takes_out : forall x n e a,
  Forall (fun q => zdisjoint (x, n) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) ->
  x + n <= page_floor (alloc_top (m_vmmaps md)) -> md_takes md e -> in_zr a e -> ~ (x <= a < x + n).
Proof.
  intros x n e a HD HT [[Hpos HC] | HA] Ha Hx; unfold in_zr in Ha.
  - destruct (proj1 (Exists_exists _ _) (HC a Ha)) as (q & Hq & Hqa).
    pose proof (proj1 (Forall_forall _ _) HD q Hq) as Z. unfold zdisjoint in Z. cbn [fst snd] in Z. lia.
  - lia.
Qed.

Lemma takes_zdisj : forall x n e, 0 < n ->
  Forall (fun q => zdisjoint (x, n) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) ->
  x + n <= page_floor (alloc_top (m_vmmaps md)) -> md_takes md e -> zdisjoint (x, n) e.
Proof.
  intros x n e Hn HD HT HE. unfold zdisjoint; cbn [fst snd].
  destruct HE as [[Hpos HC] | HA]; [| left; lia].
  destruct (Z_le_gt_dec (x + n) (fst e)) as [L|L]; [left; exact L|]. right.
  destruct (Z_le_gt_dec (fst e + snd e) x) as [L2|L2]; [exact L2|]. exfalso.
  apply (takes_out x n e (Z.max x (fst e)) HD HT (or_introl (conj Hpos HC))); unfold in_zr; lia.
Qed.

Definition E1 (regs2 : bvmap 5 word) : env := havoc E0 33 (map (getr regs2) CLOB).
Lemma E1_old : forall regs2 n, (n < 33)%nat -> ew (E1 regs2) n = ew E0 n.
Proof. intros regs2 n Hn. exact (ew_havoc_old E0 33 _ n Hn). Qed.
Lemma E1_a0 : forall regs2, ew (E1 regs2) 37 = getr regs2 10.
Proof. intros regs2. exact (ew_havoc_new E0 33 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(unfold CLOB; cbn; lia)). Qed.
Lemma E1_2 : forall regs2, bv_unsigned (ew (E1 regs2) 2) = sp.
Proof. intros regs2. rewrite E1_old by lia. exact E2. Qed.
Lemma fin_regE : forall regs2 (Hx : word -> bool) (m3 : machine_state) ss (r : bv 5) (n : nat),
  st_ok tfibsegs (E1 regs2) ss (restrict Hx m3) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs m3) r = ew (E1 regs2) n.
Proof.
  intros regs2 Hx m3 ss r n HS Hr. rewrite (st_ok_reg_denot Hx (E1 regs2) ss m3 r HS), Hr. cbn [sv_denot].
  rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma win_T1 : forall regs2 a, in_wrange (E1 regs2) (ss_mem C_T1) a ->
  (sp - 32 <= a < sp) \/ (SSc + 8 <= a < SSc + 24) \/ (SSc + 28 <= a < SSc + 29).
Proof.
  intros regs2 a Hw. destruct (in_wrange_windows (E1 regs2) (ss_mem C_T1) a Hw) as (b & lo & hi & Hin & Hr).
  vm_compute in Hin.
  destruct Hin as [Hq|[Hq|[Hq|[Hq|[]]]]]; injection Hq as <- <- <-; cbn [base_val] in Hr;
  [rewrite E1_2 in Hr; left; lia | right; left; unfold SSc; lia | right; left; unfold SSc; lia | right; right; unfold SSc; lia].
Qed.
Lemma kept_pt : forall E (m m' : word -> option byte) r,
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  YP09.r_lo r <= YP09.r_wlo r -> YP09.r_whi r <= YP09.r_hi r -> region_kept tfibsegs E m m' r.
Proof.
  intros E m m' r Hp H1 H2. split; intros a Ha.
  - unfold mbyte. rewrite Hp by lia. reflexivity.
  - unfold writable_at, wview. rewrite Hp by lia. tauto.
Qed.
Lemma s3_io_trans : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.
Lemma s3_io_wvb : forall l p M, same_io M (with_vm_backing l p M). Proof. intros. repeat split; reflexivity. Qed.
Lemma wvb_frame : forall M p, m_vmmaps (with_vm_backing (m_vm_lazy M) p M) = m_vmmaps M.
Proof.
  intros M p. pose proof (same_but_materialized_frame M _ (with_vm_backing_same M p)) as F.
  destruct F as (_ & F2 & _). exact F2.
Qed.
Lemma takes_wvb : forall M p e, md_takes M e -> md_takes (with_vm_backing (m_vm_lazy M) p M) e.
Proof. intros M p e H. unfold md_takes in *. rewrite wvb_frame. exact H. Qed.
Lemma takes_sub : forall M lo len lo' len', md_takes M (lo, len) -> lo <= lo' -> lo' + len' <= lo + len -> 0 < len' ->
  md_takes M (lo', len').
Proof.
  intros M lo len lo' len' [[Hp HC] | HA] H1 H2 H3; unfold md_takes; cbn [fst snd] in *.
  - left. split; [exact H3|]. intros a Ha. apply HC. unfold in_zr in *; cbn [fst snd] in *. lia.
  - right. lia.
Qed.
Lemma TSTK : md_takes md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Proof.
  apply (proj1 (Forall_forall _ _) TEXT). apply in_or_app. left. unfold ext_but_SB.
  apply in_or_app. right. apply in_or_app. right. cbn. tauto.
Qed.
(* P2's in_app from the callee's 4096 <= x, page_aligned x, P3 and x + n <= alloc_top, with the band_maps entries of
   TEXT and HCT (the steps of anon_grant_facts, YG0j.v:306-325). *)
Lemma grant_in_app : forall x, 4096 <= x -> YG0f.page_aligned x ->
  Forall (fun q => zdisjoint (x, kStoreBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q)))
    (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) -> x + kStoreBlockSize <= alloc_top (m_vmmaps md) ->
  in_app x kStoreBlockSize.
Proof.
  intros x H4 Hal HD HT.
  pose proof (grant_end_page_floor x kStoreBlockSize _ Hal ltac:(reflexivity) HT) as HTF.
  pose proof TEXT as TX. rewrite !Forall_app in TX. destruct TX as (_ & _ & _ & TB). unfold band_maps in TB.
  apply Forall_cons_iff in TB as [B1 TB]. apply Forall_cons_iff in TB as [B2 TB]. apply Forall_cons_iff in TB as [B3 _].
  assert (Hn : 0 < kStoreBlockSize) by (unfold kStoreBlockSize; lia).
  pose proof (takes_zdisj x kStoreBlockSize _ Hn HD HTF B1) as D1.
  pose proof (takes_zdisj x kStoreBlockSize _ Hn HD HTF B2) as D2.
  pose proof (takes_zdisj x kStoreBlockSize _ Hn HD HTF B3) as D3.
  assert (CE : x + kStoreBlockSize <= alloc_ceiling).
  { apply (YM05.grant_below_ceil (alloc_top (m_vmmaps md)) (x + kStoreBlockSize) HCT); [| exact HT].
    unfold YG0f.page_aligned in Hal. unfold kStoreBlockSize. rewrite Zplus_mod, Hal. reflexivity. }
  pose proof (@ASAN_CEIL_range rc) as [CR0 _].
  unfold zdisjoint in D1, D2, D3. cbn [fst snd] in D1, D2, D3. unfold in_app.
  unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASAN_CEIL in *.
  split; [exact H4|]. clear - D1 D2 D3 Hn CE CR0. lia.
Qed.

Lemma mm_vmmaps_wvb : forall (m : Model) l X (a n : word),
  m_vmmaps (YK0v.mmap_model a n (with_vm_backing l X m)) = m_vmmaps (YK0v.mmap_model a n m).
Proof. intros m l X a n. destruct m. reflexivity. Qed.
Lemma eu_wvb : forall (m : Model) X, eager_used (with_vm_backing (m_vm_lazy m) X m) = eager_used m.
Proof. intros m X. pose proof (same_but_materialized_frame m _ (with_vm_backing_same m X)) as F. tauto. Qed.

Lemma tail_ok : forall ms mat W2 x regs2 mem2 md2,
  st_ok tfibsegs E0 C_SS_CALL (restrict Hd ms) -> frame_of E0 C_REG0 mem (ms_mem ms) ->
  mem_grows (mrestrict Hd mem) (mrestrict Hd (ms_mem ms)) -> wle W W2 ->
  getr regs2 10 = Z_to_bv 64 x -> regs_preserved (ms_regs ms) regs2 ->
  YG0f.page_aligned x -> 4096 <= x ->
  Forall (fun q => zdisjoint (x, kStoreBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q)))
    (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) -> x + kStoreBlockSize <= alloc_top (m_vmmaps md) ->
  (forall i, 0 <= i < kStoreBlockSize -> apresent (w_H W2) mem2 (x + i) /\ aview tfibsegs (w_H W2) mem2 (x + i) = Some 0) ->
  w_A W2 = (x, x + kStoreBlockSize) :: w_A W ->
  (forall a : word, ~ (x <= bv_unsigned a < x + kStoreBlockSize) -> w_H W2 a = w_H W a) ->
  (forall a : word, ~ (spZ (ms_regs ms) - MNR_STK <= bv_unsigned a < spZ (ms_regs ms)) -> ~ (x <= bv_unsigned a < x + kStoreBlockSize) ->
     mem2 a = ms_mem ms a) ->
  (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W2) mem2 a) ->
  same_io (with_vm_backing (m_vm_lazy md) mat md) md2 ->
  md_takes md2 (x, kStoreBlockSize) -> (forall e, md_takes (with_vm_backing (m_vm_lazy md) mat md) e -> md_takes md2 e) ->
  (exists mat1, md2 = with_vm_backing
      (m_vm_lazy (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) (with_vm_backing (m_vm_lazy md) mat md))) mat1
      (YK0x.mmap_model_noreserve (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) (with_vm_backing (m_vm_lazy md) mat md))) ->
  m_vmmaps md2 = m_vmmaps (YK0v.mmap_model (Z_to_bv 64 x) (Z_to_bv 64 kStoreBlockSize) (with_vm_backing (m_vm_lazy md) mat md)) ->
  m_vm_lazy md2 = (Z_to_bv 64 x, Z_to_bv 64 kStoreBlockSize) :: m_vm_lazy (with_vm_backing (m_vm_lazy md) mat md) ->
  eager_used md2 = eager_used (with_vm_backing (m_vm_lazy md) mat md) ->
  SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 455792) mem2 (seg_rom tfibsegs)) md2) POST3.
Proof.
  intros ms mat W2 x regs2 mem2 md2 HS HF HG Hle Q1 Q2 Q3 Q3b Q5 Q6 Q7 QA QH Q8 Q9 Q10 Q11 Q12 QM QV QL QE.
  pose proof sp_facts as [SF1 SF2]. pose proof sp_range as SR. pose proof ESS as ES. pose proof MNR_STK_pos as MP.
  destruct (call_regs ms HS) as (C10 & C1 & Csp).
  pose proof (grant_in_app x Q3b Q3 Q5 Q6) as Q4.
  pose proof (grant_end_page_floor x kStoreBlockSize _ Q3 ltac:(reflexivity) Q6) as Q6F.
  assert (XIN : 4096 <= x /\ x + kStoreBlockSize <= 2 ^ 64).
  { pose proof (@ASAN_CEIL_range rc) as [CR _]. pose proof Q4 as [I1 I2]. split; [exact I1|].
    unfold kLowShadowBeg in I2. destruct I2 as [I2|[_ I2]]; lia. }
  (* where X is not *)
  assert (XS : forall a, sp - 32 <= a < sp -> ~ (x <= a < x + kStoreBlockSize)).
  { intros a Ha. apply (takes_out x kStoreBlockSize (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) a Q5 Q6F TSTK).
    unfold in_zr; cbn [fst snd]. unfold BIC_STK in Hlo. lia. }
  assert (XC : forall a, SSc <= a < SSc + 32 -> ~ (x <= a < x + kStoreBlockSize)).
  { intros a Ha. rewrite ES in TSS. apply (takes_out x kStoreBlockSize (SSc, 32) a Q5 Q6F TSS). unfold in_zr; cbn [fst snd]. lia. }
  assert (K2 : forall a, (sp - 32 <= a < sp) \/ (SSc + 8 <= a < SSc + 32) -> mem2 (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)).
  { intros a Ha. assert (A0 : 0 <= a < 2 ^ 64) by (unfold SSc in *; lia).
    apply Q8; rewrite unsigned_lit_small by lia.
    - rewrite Csp. unfold SSc in *; lia.
    - destruct Ha as [Ha|Ha]; [apply XS; exact Ha | apply XC; lia]. }
  assert (HW2 : forall a, (sp - 32 <= a < sp) \/ (SSc + 8 <= a < SSc + 32) -> w_H W2 (Z_to_bv 64 a) = Hd (Z_to_bv 64 a)).
  { intros a Ha. assert (A0 : 0 <= a < 2 ^ 64) by (unfold SSc in *; lia).
    apply QH. rewrite unsigned_lit_small by lia.
    destruct Ha as [Ha|Ha]; [apply XS; exact Ha | apply XC; lia]. }
  assert (V_mtxc : val_mem tfibsegs (mrestrict Hd (ms_mem ms)) (SSc + 28) 4 1).
  { memv HS 3%nat 0%nat; [unfold SSc; lia | reflexivity | lia]. }
  (* st_ok at the return address 0x6f470 *)
  assert (HS1 : st_ok tfibsegs (E1 regs2) C_T1 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 455792) mem2 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. unfold E1. change C_T1 with (ss_after_call C_SS_CALL C_RS1 33 0x6f470).
    apply (st_ok_after_call tfibsegs 33 E0 C_SS_CALL (restrict Hd ms) regs2 (mrestrict (w_H W2) mem2) C_RS1 0x6f470 HS).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - unfold C_RS1, C_SS_CALL; cbn [ss_mem app firstn].
      apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|].
      apply submem_keep; [apply subregion_refl|]. apply submem_keep; [| apply submem_nil].
      unfold subregion; cbn. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia | intros c []].
    - vm_compute; reflexivity.
    - exact Q2.
    - change (ms_mem (restrict Hd ms)) with (mrestrict Hd (ms_mem ms)). unfold C_RS1.
      repeat apply Forall_cons; try apply Forall_nil.
      all: apply kept_pt; [intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; try rewrite E2 in Ha;
        unfold mrestrict; rewrite HW2 by (unfold SSc in *; lia); rewrite K2 by (unfold SSc in *; lia); reflexivity
        | cbn; lia | cbn; lia]. }
  srr_run_shG tfibtbl_rtB_ok HS1.
  lazymatch type of HS1 with st_ok _ _ _ (restrict _ ?m3) => rename m3 into ms3 end.
  match goal with Hf : frame_of (E1 regs2) (ss_mem C_T1) _ _ |- _ => rename Hf into HF3 end.
  match goal with Hg : mem_grows (mrestrict _ mem2) _ |- _ => rename Hg into HG3 end.
  pose proof Hwx_tfa as HWX.
  eapply (SRr_ret_at tfibsegs tfibtbl_rtB tfibtbl_rtB_ok HWX W2); [exact HS1 | reflexivity | vm_compute; reflexivity |].
  intros mat'. try rewrite wvb_collapse.
  assert (R1 : getr (ms_regs ms3) 1 = getr regs 1).
  { rewrite (fin_regE regs2 _ ms3 _ 1%bv 1%nat HS1 ltac:(vm_compute; reflexivity)). rewrite E1_old by lia. exact (Er 1 1%bv eq_refl). }
  assert (A10 : getr (ms_regs ms3) 10 = Z_to_bv 64 x).
  { rewrite (fin_regE regs2 _ ms3 _ 10%bv 37%nat HS1 ltac:(vm_compute; reflexivity)). rewrite E1_a0. exact Q1. }
  assert (RP : regs_preserved regs (ms_regs ms3)).
  { apply regs_preserved_intro; lazymatch goal with |- getr _ ?r = getr regs ?r =>
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      rewrite (fin_regE regs2 _ ms3 _ r n HS1 ltac:(vm_compute; reflexivity)); rewrite E1_old by lia; exact (Er n r eq_refl) end. }
  assert (PC : v_jalr (getr (ms_regs ms3) 1) 0 = getr regs 1).
  { rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  assert (FT : forall w : word, ~ (sp - 32 <= bv_unsigned w < sp) -> ~ (SSc + 8 <= bv_unsigned w < SSc + 24) ->
    ~ (SSc + 28 <= bv_unsigned w < SSc + 29) -> ms_mem ms3 w = mem2 w).
  { intros w N1 N2 N3. apply HF3. intros Hw. destruct (win_T1 regs2 _ Hw) as [Z1|[Z1|Z1]]; [exact (N1 Z1) | exact (N2 Z1) | exact (N3 Z1)]. }
  assert (MBQ : forall a, SSc + 29 <= a < SSc + 32 ->
    mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms3)) a = mbyte tfibsegs (mrestrict Hd (ms_mem ms)) a).
  { intros a Ha. assert (A0 : 0 <= a < 2 ^ 64) by (unfold SSc in *; lia).
    unfold mbyte, mrestrict. rewrite (HW2 a) by (right; unfold SSc in *; lia).
    rewrite FT by (rewrite unsigned_lit_small by lia; unfold SSc in *; lia).
    rewrite K2 by (right; unfold SSc in *; lia). reflexivity. }
  assert (V0 : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms3)) (SSc + 28) 1 0).
  { memv HS1 3%nat 0%nat; [unfold SSc; lia | reflexivity | lia]. }
  unfold POST3. rewrite PC.
  exists x, (ms_regs ms3), (ms_mem ms3). eexists. cbv zeta.
  split; [reflexivity|].
  split; [exact QA|]. split; [exact QH|].
  rewrite ES. unfold s_block0, ss_alloc, bi0_mtx.
  split; [exact A10|]. split; [exact RP|].
  split.
  { memv HS1 2%nat 0%nat; [unfold SSc; lia | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E1_a0; exact Q1 |
      unfold kStoreBlockSize in XIN; lia]. }
  split; [exact Q3|]. split; [exact Q4|].
  split.
  { eapply Forall_impl; [| exact TEXT]. intros e He. exact (takes_zdisj x kStoreBlockSize e ltac:(unfold kStoreBlockSize; lia) Q5 Q6F He). }
  split.
  { intros a Ha Hin. unfold in_zr in Hin; cbn [fst snd] in Hin.
    exact (takes_out x kStoreBlockSize (a, 1) a Q5 Q6F (TCL a Ha) ltac:(unfold in_zr; cbn [fst snd]; lia) Hin). }
  split.
  { intros i Hi. destruct (Q7 i Hi) as [Pa Pv].
    assert (EQx : ms_mem ms3 (Z_to_bv 64 (x + i)) = mem2 (Z_to_bv 64 (x + i))).
    { assert (A0 : 0 <= x + i < 2 ^ 64) by (unfold kStoreBlockSize in *; lia).
      apply FT; rewrite unsigned_lit_small by lia; intros Z1.
      - exact (XS (x + i) Z1 ltac:(lia)).
      - exact (XC (x + i) ltac:(lia) ltac:(lia)).
      - exact (XC (x + i) ltac:(lia) ltac:(lia)). }
    split.
    - unfold apresent in Pa |- *. rewrite EQx. exact Pa.
    - unfold aview, mbyte, mrestrict in Pv |- *. rewrite EQx. exact Pv. }
  split.
  { intros a N1 N2 N3 N4. pose proof (u64_range a) as UA.
    assert (N1' : ~ (sp - 32 <= bv_unsigned a < sp)) by (unfold BIC_STK in N1; lia).
    rewrite (FT a N1' ltac:(lia) ltac:(lia)).
    rewrite (Q8 a ltac:(rewrite Csp; unfold BIC_STK in N1; lia) N2).
    apply (frameA _ HF a N1'); lia. }
  split.
  { memv HS1 1%nat 0%nat; [unfold SSc; lia | | pose proof (Z.mod_pos_bound (alloc + kStoreBlockSize) (2 ^ 64) ltac:(lia)); lia].
    cbn [sv_denot]. rewrite E1_old by lia. rewrite E32.
    rewrite unsigned_lit_small by (pose proof (Z.mod_pos_bound alloc (2 ^ 64) ltac:(lia)); lia).
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace kStoreBlockSize with 8388608 by (unfold kStoreBlockSize; reflexivity).
    rewrite Zplus_mod_idemp_l. rewrite Z.mod_mod by lia. reflexivity. }
  split.
  { intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia].
    - pose proof (V0 0%nat ltac:(lia)) as B0. rewrite B0. vm_compute. reflexivity.
    - rewrite MBQ by (cbn; lia). rewrite (V_mtxc 1%nat ltac:(lia)). vm_compute. reflexivity.
    - rewrite MBQ by (cbn; lia). rewrite (V_mtxc 2%nat ltac:(lia)). vm_compute. reflexivity.
    - rewrite MBQ by (cbn; lia). rewrite (V_mtxc 3%nat ltac:(lia)). vm_compute. reflexivity. }
  split.
  { intros a Ha. apply (apresent_grows (w_H W2) mem2 (ms_mem ms3) a HG3). apply Q9.
    apply (apresent_grows Hd mem (ms_mem ms) a HG). exact Ha. }
  split.
  { eapply s3_io_trans; [apply s3_io_wvb|]. eapply s3_io_trans; [exact Q10|].
    first [apply s3_io_wvb | eapply s3_io_trans; apply s3_io_wvb]. }
  split.
  { repeat apply takes_wvb. exact Q11. }
  split.
  { intros e He. repeat apply takes_wvb. apply Q12. apply takes_wvb. exact He. }
  split.
  { exists mat'. destruct QM as [mat1 QM]. rewrite QM, wvb_collapse, nr_wvb, wvb_collapse. reflexivity. }
  split.
  { rewrite m_vmmaps_wvb, QV. apply mm_vmmaps_wvb. }
  split.
  { rewrite m_vm_lazy_wvb, QL, m_vm_lazy_wvb. reflexivity. }
  split.
  { rewrite eu_wvb, QE. apply eu_wvb. }
  split; [apply kd_grow_SB; exact HSB|].
  exact (proj2 (proj1 (Forall_app _ _ _) Q5)).
Qed.

Lemma create_walk : SRr_refusable W (mkCfg (mkst regs (Z_to_bv 64 tfib_A_StackStore_BlockInfo_Create) mem (seg_rom tfibsegs)) md) POST3.
Proof.
  pose proof SEED as HS. pose proof sp_facts as [SF1 SF2]. pose proof sp_range as SR. pose proof MNR_STK_pos as MP.
  unfold SRr_refusable. unfold tfib_A_StackStore_BlockInfo_Create.
  srr_run_shG tfibtbl_rtB_ok HS.
  change (st_ok tfibsegs E0 C_SS_CALL (restrict Hd ms)) in HS.
  lazymatch goal with |- SRr _ ?Wx ?cx _ => change (SRr_refusable Wx cx POST3) end.
  destruct (call_regs ms HS) as (C10 & C1 & Csp).
  rewrite (st_ok_restrict_mkst tfibsegs Hd E0 C_SS_CALL ms HS eq_refl).
  change (ss_pc C_SS_CALL) with tfib_A_MmapNoReserveOrDie.
  destruct (wvb_vmmaps mat) as [VMM EGU].
  assert (KEEP : forall x : word, bv_unsigned x < SSc + 8 -> ms_mem ms x = mem x).
  { intros x Hx. apply (frameA _ HF x); unfold SSc in *; lia. }
  eapply SRr_refusable_bind.
  - apply (mnr_holds W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) kStoreBlockSize).
    + unfold argZ. rewrite (st_ok_reg_denot Hd E0 C_SS_CALL ms _ HS). vm_compute. reflexivity.
    + unfold kStoreBlockSize. lia.
    + unfold YG0f.page_aligned, kStoreBlockSize. reflexivity.
    + rewrite C1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
    + exact (mnr_cells_kept _ KEEP).
    + unfold md_room. rewrite VMM. exact RM.
    + rewrite VMM. exact HIVS.
    + rewrite VMM, EGU. exact HBUD.
    + rewrite Csp. pose proof Hsp16 as H16. rewrite Zminus_mod, H16. reflexivity.
    + rewrite Csp. unfold BIC_STK in Hlo. lia.
    + rewrite Csp. lia.
    + intros a Ha. rewrite Csp in Ha. apply (apresent_grows Hd mem (ms_mem ms) a HG). apply P_stk. unfold BIC_STK. lia.
    + rewrite Csp. apply Forall_cons.
      * apply takes_wvb. apply (takes_sub md _ _ _ _ TSTK); unfold BIC_STK in Hlo; lia.
      * eapply Forall_impl; [| exact TMC]. intros e He. apply takes_wvb. exact He.
  - intros W2 c2 Hle (x & regs2 & mem2 & md2 & Ec2 & Q1 & Q2 & Q3 & Q3b & Qg & Q5 & Q6 & Q7 & QA & QH & Q8 & Q9 & Q10 & Q11 & Q12
      & QM & QV & QL & QE).
    subst c2. rewrite C1. rewrite VMM in Q5, Q6.
    exact (tail_ok ms mat W2 x regs2 mem2 md2 HS HF HG Hle Q1 Q2 Q3 Q3b Q5 Q6 Q7 QA QH Q8 Q9 Q10 Q11 Q12 QM QV QL QE).
Qed.

End w.

Theorem tfib_blockinfo_create_ok : forall B, TfibSyms B -> tfib_blockinfo_create_spec B.
Proof using kd_grow_SB.
  intros B HB W ly S regs mem md alloc. cbv zeta. intros.
  eapply create_walk; eassumption.
Qed.
End kd.
End g.
