(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written by a Theorem Labs lane, the B2 prover, for another Theorem Labs lane. *)
(* the
   statement of the FIRST StackDepotPut (StackDepotPut 0x71e78 in fuzz_wire.asan (the donor fuzz_knock.asan's 0x70ef0), 8 insns, which tail-jumps to
   StackDepotBase<StackDepotNode,1,20>::Put 0x71e98 (donor 0x70f10), 161 insns; donor pin sha256 61768cf4739b...), the Put that
   finds the depot empty and maps both depot blocks. It composes the Theorem Labs lane's S7 (lib/A/AD3g.v
   tfib_tlm_create_nb_ok, TwoLevelMap::Create 0x7269c (donor 0x71714), the nodes block) and S1 (lib/A/AD3a.v tfib_store_ok,
   StackStore::Store 0x6f87c (donor 0x6e8f4), the store block through S2 AD3b.tfib_alloc_ok and S3 AD3c.tfib_blockinfo_create_ok) with
   a Theorem Labs lane's lib/A/AD3i.v (depot_room, depot_store_one_block). rule 24: proves function
   StackDepotBase<StackDepotNode,1,20>::Put (reused from proofs/libreac/fuzz_knock/lib/A/AD3j.v, the copy note at line 90).

   THE PATH (addresses of the donor fuzz_knock ASan image (pin sha256 61768cf4739b), not fuzz_wire.asan's; a0 = buf, a1 = length tr at StackDepotPut; disassembly of that image's .text)
     0x70ef0 StackDepotPut: a0 := &theDepot (0x180418), a1 := buf, a2 := size word, a3 := 0; j Put.
     0x70f10 Put: frame 0x70 (ra, s0-s9); the StackTrace {buf, size, tag 0} at sp + 8; size = 0 or buf = 0 -> return 0.
     0x70f68-0x71000 the hash loop (tfib_dhash, YF0p.v:15): s3 := h; bucket b1 = h mod 2^20, s2 := &tab[b1].
     0x71010 lw tab[b1] = 0 (empty depot) -> 0x71030 beqz -> 0x71088: jal lock 0x71684 at 0x7108c (lr.w / sc.w
       tab[b1] |= 0x80000000; returns the old word 0); beq 0 0 -> 0x710c0.
     0x710cc amoadd.w n_uniq_ids (as_depot + 0x400000) += 1 -> id 1; 0x710e4 idx := id >> 16 = 0; 0x710f0 ld map1_[0]
       = 0 -> 0x71188: jal TwoLevelMap::Create 0x71714 at 0x7118c (a0 = as_depot + 0x400008, a1 = 0; S7), back to
       0x710f8 with a0 = nb: node := nb + 16 * (id & 0xffff) = nb + 16.
     0x71114 jal StackDepotNode::store 0x70c08 (a0 = node, a2 = Put's sp + 8, a3 = h): node.hash := h (sd at node + 0);
       pack := 0 at its sp + 8; jal StackStore::Store 0x6e8f4 at 0x70c30 (a0 = 0x170408, a1 = Put's sp + 8, a2 = &pack;
       S1, which maps the store block through Alloc / BlockInfo::Create); node.store_id := 1 (sw at node + 12);
       pack = 0 -> return.
     0x71118 node.link := 0 (sw at node + 8); fence; 0x71124 tab[b1] := 1 (the unlock writes the new head); s0 = 0;
       return a0 = 1.
   Stack below Put's entry sp: 112 + 136 = 248 on the S7 path (Create 32 + MOD_STK 104), 112 + 32 + 64 + 16 + 136
   = 360 on the S1 path (S3's figure), 112 + 48 on the lock: all inside DEP_STK = 512 (AFl0.v:60).

   THE KERNEL (lib/Reusable). Every depot constant takes its knock branch: depot_has_trace = false (DepotCfg.v:16).
   - Before the first Put, depot_cells holds n_uniq_ids, map1_, the store total, block0, the nodes-map mutex, stored_ and
     mtx_ of blocks_[0] and allocated_ at 0 (YG0n.v:117-118).
   - After it, depot_cells holds n_uniq_ids = depot_ids S, map1_ = NB, the store total = depot_frames S, block0 = SB and
     allocated_ = kStoreBlockSize (YG0n.v:119-120).
   - ARm's am_cells holds depot_cells, which acells includes (YG0n.v:388, :137).
   - depot_ok's pre-Put branch: the hash table is 0, ly_NB = ly_SB = 0 exactly when the depot is empty, and a live chunk
     implies a stored trace (YG0n.v:210-212).
   - depot_ok's post-Put branch: both blocks are mapped and the hash table holds the depot's traces (YG0n.v:213-221).
   - owned_extents holds the empty extent (4096, 0) for an unmapped nodes or store block (YG0f.v:382-383).
   - al_perm reads perm_live (YG0n.v:611), which lists the two blocks only once they are mapped (YG0n.v:527-531).
   - aareas gives the two blocks' areas size 0 before the first Put and their block sizes after it (YG0n.v:161-162).
   - al_eager_x adds nb_eager ly (YG0n.v:609-610), which is 0 until the nodes block is mapped (YG0n.v:467).
   - am_depot_mono (YG0n.v:405): under ARm, a mapped nodes block means a stored trace (am_depot_mono_d, YG0n.v:263).
   - am_alloc_depot (YG0n.v:407): under ARm, a live chunk means a stored trace (am_alloc_depot_d, YG0n.v:265-266).
   - The first Put's layout step is layout_grow (YG0f.v:100-101), with layout_grow_NB / _SB / _trans (YG0f.v:106, :110, :114).
   - kd_inst (:2582-2597) instantiates this file's Section kd placeholders with these kernel terms.
   - The image's allocated_ row in as_const is zero-width (lib/A/AF0m.v:129), so it holds after the Put (kd_alloc_row_rev6, :1267).
   - put_zero_cells (:152-153), a premise of tfib_depot_first_put_spec (:775, :780), lists three of the zero cells above.































   tfib_depot_put_any: ONE Put lemma for every Put consumer. Same shared PRE as B2 and
   tfib_depot_spec (AFl0.v:69-79); B2's own premises under st_depot S = [] (depot_first_put_pre), tfib_depot_spec's own
   under st_depot S <> [] (layout_ok, depot_mem_ok; the case itself is the st_depot S <> [] premise that AFl0.v:74
   puts after depot_mem_ok). POST: (st_depot S = [] -> B2's post)
   /\ (st_depot S <> [] -> tfib_depot_spec's post), both verbatim (depot_first_put_post, depot_put_post). Proved by case
   on st_depot S from tfib_depot_first_put_ok and AFem.tfib_depot_ok : tfib_depot_spec B (AFem.v:1550). This unit's
   AFl0 states the st_depot S <> [] premise (AFl0.v:74, as lib/B/YFl0.v:74 does) and AFem proves that spec, so
   the non-empty case passes the case hypothesis to
   tfib_depot_ok (:2547), and depot_put_post is that spec's post at the state after the Put (:701-715). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AD3j.v (donor image sha256 61768cf4739b), with its module paths changed, names TfibSyms -> WireSyms and its addresses moved to reac-repacer/fuzz_wire's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09 YO0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v AF0m AF0x AB1w AFl0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK0v YK13 YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YK0g YF0p YA0o.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import KnBlockExt.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AD3d AD3h AD3c AD3g.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AD3a AD3b AD3i AFem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require AD3k AB13.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YP03 YO0f.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YG0b YG08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* lia on mod / div goals (B2's proof): the closure leaves Zify's flag false; set to true for this file only (Local:
   importers keep their own). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* YM04.v:37-44 redefines lia's core so that it fails on an `or` hypothesis; B2's proof restores YM03.v:179's own text
   (Local: importers keep YM04's). *)
Local Ltac YM03.lf_lia_orig ::= Zify.zify; xlia zchecker.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The static half of KnBlockExt's DZONE_at for the asan image: [stackStore, read_stage). Kept here,
   not in AB1w (output of the porting tool, which a re-port regenerates); every DZONE_at user Requires AD3j. *)
Definition tfib_dzone_lo : Z := 0x172648. (* asan stackStore, measured on the unstripped pin *)
Definition tfib_dzone_hi : Z := 0x5c2dd0. (* asan read_stage *)

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ===== The kernel's knock texts that B2 states against (lib/Reusable/YG0n.v's knock branches). ===== *)

(* YG0n.depot_cells, knock branch (YG0n.v:116-121), VERBATIM: the pre-Put branch adds the nodes-map mutex,
   blocks_[0].stored_ / mtx_ and allocated_ = 0 (d_mu = tlm_mu, s_stored0 = AD3a.bi0_stored, s_mtx0 = bi0_mtx,
   s_alloc = ss_alloc), the post-Put branch allocated_ = kStoreBlockSize. Swap: YG0n.depot_cells by depot_cells_pre
   (:298) / depot_cells_post (:307). *)
Definition depot_cells_kd (S : astate) : list acell :=
  match st_depot S with
  | [] => [ z4 (ADepot d_nuniq) 0; z8 (ADepot d_map1) 0; z8 (AStore s_total) 0; z8 (AStore s_block0) 0;
            z4 (ADepot d_mu) 0; z4 (AStore s_stored0) 0; z4 (AStore s_mtx0) 0; z8 (AStore s_alloc) 0 ]
  | _ :: _ => [ z4 (ADepot d_nuniq) (depot_ids S); c8 (ADepot d_map1) (ANB 0);
               z8 (AStore s_total) (depot_frames S); c8 (AStore s_block0) (ASB 0); z8 (AStore s_alloc) kStoreBlockSize ]
  end.

(* The NB / SB entries of YG0n.aareas, knock branch (YG0n.v:161-162), VERBATIM. Swap: aareas_post (:327). *)
Definition aareas_depot_kd (S : astate) : list (aexp * Z) :=
  [(ANB 0, match st_depot S with [] => 0 | _ :: _ => kNodesBlockSize end);
   (ASB 0, match st_depot S with [] => 0 | _ :: _ => kStoreBlockSize end)].

(* The depot / store entries of ajunk (YG0n.v:143) that Put reads or writes, as AFl0.v:68's depot_mem_ok lists them:
   n_uniq_ids' upper bytes and the nodes-map mutex word, allocated_, stored_ and mtx_ of blocks_[0]. *)
Definition depot_junk_kd : list (aexp * Z) := [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8)].

(* The cells the first Put's callees read as 0, also in depot_cells' pre-Put branch (YG0n.v:118): the nodes-map mutex word
   (TwoLevelMap::Create's lock, AD3g.v:156), stored_ (Store's stored_ += n + 1, AD3a.v:80) and mtx_ of blocks_[0]
   (BlockInfo::Create's lock, AD3c.v:195). *)
Definition put_zero_cells : list acell :=
  [ z4 (ADepot tlm_mu) 0; z4 (AStore AD3a.bi0_stored) 0; z4 (AStore bi0_mtx) 0 ].

(* The extents the two new blocks must miss (S7's P3 list, AD3g.v:160 / :172): the static extents without NB / SB
   (ext_but_NB, with ly_SB ly = 0), the extras, the secondaries and the shadow bands. *)
Definition first_put_avoid (ly : alayout) (S : astate) : list (Z * Z) :=
  ext_but_NB ly ++ ly_extra ly ++ sec_extents ly S ++ band_maps.

(* The room and budget of both depot maps at Put's entry: a Theorem Labs lane's depot_room (lib/A/AD3i.v:211-233) conclusion,
   VERBATIM with md := md and Wx := W; the caller gets it from AD3i.depot_room (AR + mroom, X := [], k := 0, or the
   walk's own X / k). *)
Definition depot_room_at (W : world tfibsegs) (md : Model) : Prop :=
  ((exists g, g mod 4096 = 0 /\ 0 < g /\ g + kNodesBlockSize <= alloc_top (m_vmmaps md) /\
      region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (Z_to_bv 64 g) (Z_to_bv 64 kNodesBlockSize) = true) /\
   eager_used md + A_bytes (w_A W) + 2 * kNodesBlockSize <= vm_limit (m_vmmaps md)) /\
  eager_used md + A_bytes (w_A W) + 3 * kNodesBlockSize + kStoreBlockSize <= vm_limit (m_vmmaps md) /\
  (forall (xw nw : word) (md' : Model) (Wx' : world tfibsegs),
    bv_unsigned nw = kNodesBlockSize ->
    vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) ->
    vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) ->
    alloc_top (m_vmmaps md) <= alloc_top (m_vmmaps md') ->
    (forall e, In e (vm_maps (m_vmmaps md')) -> e = (xw, nw) \/ In e (vm_maps (m_vmmaps md))) ->
    eager_used md' <= eager_used md + kNodesBlockSize -> A_bytes (w_A Wx') <= A_bytes (w_A W) + kNodesBlockSize ->
    (exists g, g mod 4096 = 0 /\ 0 < g /\ g + kStoreBlockSize <= alloc_top (m_vmmaps md') /\
      region_free (vm_reserved (m_vmmaps md') ++ vm_maps (m_vmmaps md')) (Z_to_bv 64 g) (Z_to_bv 64 kStoreBlockSize) = true) /\
    eager_used md' + A_bytes (w_A Wx') + kStoreBlockSize <= vm_limit (m_vmmaps md')).

(* The two knock branches of YG0n.depot_ok (YG0n.v:209-222; depot_ids / depot_traces at their knock meanings, YG00.v:402-403 /
   YG0n.v:181-182): the pre-Put branch (YG0n.v:210-212; its fourth conjunct is :212) and the post-Put
   branch. *)
Definition depot_ok_pre_text (B : asyms) (ly : alayout) (rd : reader) (S : astate) : Prop :=
  st_depot S = [] /\ (forall b, 0 <= b < d_tab_words -> rd32 rd (as_depot B + 4 * b) 0) /\
  (st_depot S = [] <-> (ly_NB ly = 0 /\ ly_SB ly = 0)) /\
  ((exists k, In k (st_chunks S)) -> st_depot S <> []).
Definition depot_ok_post_text (B : asyms) (ly : alayout) (rd : reader) (S : astate) : Prop :=
  ly_NB ly <> 0 /\ ly_SB ly <> 0 /\
  exists (heads : Z -> Z) (links : Z -> Z),
  let n := Z.of_nat (length (st_depot S)) in
  let hashes := fun id => as_dhash B (nth (Z.to_nat (id - 1)) (st_depot S) []) in
  (forall b, 0 <= b < d_tab_words -> 0 <= heads b <= n /\ rd32 rd (as_depot B + 4 * b) (heads b)) /\
  (forall id, 1 <= id <= n -> 0 <= links id < id /\
     rd64 rd (ly_NB ly + 16 * id) (hashes id mod 2 ^ 64) /\ rd32 rd (ly_NB ly + 16 * id + 8) (links id)) /\
  (forall id, 1 <= id <= n ->
     chain_has links hashes (Z.to_nat n) (heads ((hashes id mod 2 ^ 64) mod d_tab_words)) (hashes id)).

(* The knock depot_ok itself (YG0n.v:209-222), only to show the placeholder's two hypotheses satisfiable. *)
Definition depot_ok_rev5 (B : asyms) (ly : alayout) (rd : reader) (S : astate) : Prop :=
  match st_depot S with
  | [] => depot_ok_pre_text B ly rd S
  | _ :: _ => depot_ok_post_text B ly rd S
  end.
Lemma depot_ok_rev5_pre : forall B ly rd S, st_depot S = [] -> (depot_ok_rev5 B ly rd S <-> depot_ok_pre_text B ly rd S).
Proof. intros B ly rd S E. unfold depot_ok_rev5. rewrite E. tauto. Qed.
Lemma depot_ok_rev5_post : forall B ly rd S, st_depot S <> [] -> (depot_ok_rev5 B ly rd S <-> depot_ok_post_text B ly rd S).
Proof. intros B ly rd S E. unfold depot_ok_rev5. destruct (st_depot S) as [|t l]; [congruence | tauto]. Qed.

(* ===== The first Put's obligations, as facts about the post state. ===== *)
(* S' = the depot after the Put (depot_after 1 tr S), ly' the grown layout, rd' the reader after, h the trace's hash:
   both blocks mapped; the depot cells of S' (nuniq 1, map1 = ANB 0 = nb, s_total = n + 1, block0 = ASB 0 = sb);
   hash word b1 = (h mod 2^64) mod d_tab_words holds 1 and every other word 0; node 1 = (h mod 2^64, link 0) at
   nb + 16 / nb + 24; the NB / SB areas and the three junk entries visible. *)
Definition depot_first_put_facts (B : asyms) (ly' : alayout) (S' : astate) (tr : list Z) (rd' : reader) : Prop :=
  let h := as_dhash B tr mod 2 ^ 64 in
  ly_NB ly' <> 0 /\ ly_SB ly' <> 0 /\
  Forall (cell_holds B ly' rd') (depot_cells_kd S') /\
  (forall b, 0 <= b < d_tab_words -> rd32 rd' (as_depot B + 4 * b) (if b =? h mod d_tab_words then 1 else 0)) /\
  rd64 rd' (ly_NB ly' + 16) h /\ rd32 rd' (ly_NB ly' + 24) 0 /\
  Forall (range_vis B ly' rd') (depot_junk_kd ++ aareas_depot_kd S').

(* mmap_model's maps read only the model's maps (YK0v.v:99-107). *)
Lemma mmap_model_vmmaps_eq : forall a n m m', m_vmmaps m = m_vmmaps m' ->
  m_vmmaps (mmap_model a n m) = m_vmmaps (mmap_model a n m').
Proof. intros a n m m' E. unfold mmap_model. rewrite !YK0g.m_vmmaps_with_vmmaps, E. reflexivity. Qed.
Lemma sbm_vmmaps : forall m m', same_but_materialized m m' -> m_vmmaps m' = m_vmmaps m.
Proof. intros m m' E. unfold same_but_materialized in E. rewrite E. reflexivity. Qed.
Lemma sbm_lazy : forall m m', same_but_materialized m m' -> m_vm_lazy m' = m_vm_lazy m.
Proof. intros m m' E. unfold same_but_materialized in E. rewrite E. reflexivity. Qed.
Lemma sbm_io : forall m m', same_but_materialized m m' -> same_io m m'.
Proof. intros m m' E. unfold same_but_materialized in E. rewrite E. unfold same_io. repeat split; reflexivity. Qed.
Lemma sbm_trans : forall m1 m2 m3, same_but_materialized m1 m2 -> same_but_materialized m2 m3 -> same_but_materialized m1 m3.
Proof.
  intros m1 m2 m3 E1 E2. pose proof (sbm_lazy _ _ E1) as L. unfold same_but_materialized in *.
  rewrite E2 at 1. rewrite L. rewrite E1 at 1. apply YA0o.wvb_wvb.
Qed.
Lemma same_io_trans3 : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). repeat split; congruence. Qed.

(* ===== Helpers of B2's proof (tfib_depot_first_put_ok, at the end of Section kd). ===== *)
(* kept U H m H' m': off the set U every byte keeps its hiding bit and its memory byte (a walk segment's or a callee's
   frame, as the K-lemmas and S7 / S1 state it). *)
Definition kept (U : Z -> Prop) (H : word -> bool) (m : word -> option byte) (H' : word -> bool)
  (m' : word -> option byte) : Prop :=
  forall w : word, ~ U (bv_unsigned w) -> H' w = H w /\ m' w = m w.
Lemma kept_trans : forall (U1 U2 : Z -> Prop) H1 m1 H2 m2 H3 m3, kept U1 H1 m1 H2 m2 -> kept U2 H2 m2 H3 m3 ->
  kept (fun a => U1 a \/ U2 a) H1 m1 H3 m3.
Proof.
  intros U1 U2 H1 m1 H2 m2 H3 m3 K1 K2 w Hw.
  destruct (K1 w (fun X => Hw (or_introl X))) as [A1 B1]. destruct (K2 w (fun X => Hw (or_intror X))) as [A2 B2].
  split; congruence.
Qed.
Lemma kept_val : forall (U : Z -> Prop) H m H' m' a (n : nat) v, kept U H m H' m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, a <= k < a + Z.of_nat n -> ~ U k) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
  intros U H m H' m' a n v K A0 A1 NU Hv. apply (val_mem_hframe H H' m m' a n v); [| exact Hv].
  intros k Hk. apply K. rewrite YP03.unsigned_lit_small by lia. exact (NU k Hk).
Qed.
Lemma kept_aview : forall (U : Z -> Prop) H m H' m' a, kept U H m H' m' -> ~ U (a mod 2 ^ 64) ->
  aview tfibsegs H' m' a = aview tfibsegs H m a.
Proof.
  intros U H m H' m' a K NU.
  assert (E : bv_unsigned (Z_to_bv 64 a) = a mod 2 ^ 64) by (rewrite Z_to_bv_unsigned; reflexivity).
  destruct (K (Z_to_bv 64 a) ltac:(rewrite E; exact NU)) as [E1 E2].
  unfold aview, mbyte, mrestrict. rewrite E1, E2. reflexivity.
Qed.
Lemma apresent_vis : forall H m a, apresent H m a -> aview tfibsegs H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
(* every image byte reads, through the rom when memory has no byte (AB13.tfib_rom_all). *)
Lemma img_vis : forall H m a, TFIB_IMG_LO <= a < TFIB_IMG_END -> aview tfibsegs H m a <> None.
Proof.
  intros H m a Ha. pose proof (AB13.tfib_rom_all a ltac:(unfold TFIB_IMG_LO, TFIB_IMG_END in Ha; exact Ha)) as R.
  change (seg_rom tfibsegs (Z_to_bv 64 a) <> None) in R.
  unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 a)); [discriminate|].
  destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [discriminate | exfalso; exact (R eq_refl)].
Qed.
Lemma rd_of_val : forall H m a (w : nat) v k, val_mem tfibsegs (mrestrict H m) a w v -> (k < w)%nat ->
  aview tfibsegs H m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
  intros H m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal. apply AF0x.unsigned_lit_small8.
  unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma rd32_of_val : forall H m a v, val_mem tfibsegs (mrestrict H m) a 4 v -> rd32 (aview tfibsegs H m) a v.
Proof. intros H m a v Hv k Hk. exact (rd_of_val H m a 4 v k Hv Hk). Qed.
Lemma rd64_of_val : forall H m a v, val_mem tfibsegs (mrestrict H m) a 8 v -> rd64 (aview tfibsegs H m) a v.
Proof. intros H m a v Hv k Hk. exact (rd_of_val H m a 8 v k Hv Hk). Qed.
Lemma cell_of_val : forall B ly H m e (w : nat) v, val_mem tfibsegs (mrestrict H m) (aeval B ly e) w (aeval B ly v) ->
  cell_holds B ly (aview tfibsegs H m) (ACell e w (AV v)).
Proof. intros B ly H m e w v Hv k Hk. exact (rd_of_val H m _ w _ k Hv Hk). Qed.
Lemma cell_agree : forall B ly (rd rd' : reader) c,
  (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
  cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
  intros B ly rd rd' c Hag Hc. unfold cell_holds in *. destruct (c_val c) as [e|mk v]; cbv zeta in *.
  - intros k Hk. rewrite Hag by lia. exact (Hc k Hk).
  - destruct Hc as (b & Hb & Hm). exists b. split; [| exact Hm].
    rewrite <- (Z.add_0_r (aeval B ly (c_at c))), Hag by lia. rewrite Z.add_0_r. exact Hb.
Qed.
(* the StackTrace's 8-byte size word as Store reads it: size (4 bytes) and tag 0 (4 bytes). *)
Lemma val_mem_split4 : forall m a v, 0 <= v < 2 ^ 32 -> val_mem tfibsegs m a 8 v ->
  val_mem tfibsegs m a 4 v /\ val_mem tfibsegs m (a + 4) 4 0.
Proof.
  intros m a v Hv H. split.
  - intros k Hk. rewrite (H k ltac:(lia)). do 2 f_equal. unfold YO0f.le_byte.
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
    rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
  - intros k Hk. replace (a + 4 + Z.of_nat k) with (a + Z.of_nat (4 + k)) by lia. rewrite (H (4 + k)%nat ltac:(lia)).
    do 2 f_equal. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
    rewrite (Z.mod_small v (2 ^ 64)) by lia. rewrite Zmod_0_l, Z.shiftr_0_l, Z.shiftr_div_pow2 by lia.
    rewrite Z.div_small; [reflexivity|]. split; [lia|].
    apply Z.lt_le_trans with (2 ^ 32); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma val_mem_byte : forall m a (w : nat) v (k : nat), (k < w)%nat -> val_mem tfibsegs m a w v ->
  val_mem tfibsegs m (a + Z.of_nat k) 1 (YG0f.le_byte v w k).
Proof.
  intros m a w v k Hk Hv j Hj. assert (Ej : j = 0%nat) by lia. subst j. rewrite Z.add_0_r. rewrite (Hv k Hk).
  do 2 f_equal. unfold YO0f.le_byte, YG0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !Z.mod_mod by lia. reflexivity.
Qed.
Lemma b2_le_byte_mod64 : forall v k, YG0f.le_byte v 8 k = YG0f.le_byte (v mod 2 ^ 64) 8 k.
Proof. intros v k. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma b2_rp : forall rg rg' (r : bv 5) z, regs_preserved rg rg' -> bv_unsigned r = z -> callee_saved z -> getr rg' r = getr rg r.
Proof. intros rg rg' r z HP E C. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. rewrite E. exact C. Qed.
Ltac rpw RP r z := rewrite (b2_rp _ _ r z RP eq_refl ltac:(unfold callee_saved; lia)).

(* The entry facts: the empty depot's cells, the zero cells, the as_const rows S7 / S1 read. *)
Lemma b2_depot_cells : forall B ly H mem S, st_depot S = [] -> Forall (cell_holds B ly (aview tfibsegs H mem)) (depot_cells_kd S) ->
  val_mem tfibsegs (mrestrict H mem) (as_depot B + d_nuniq) 4 0 /\ val_mem tfibsegs (mrestrict H mem) (as_depot B + d_map1) 8 0 /\
  val_mem tfibsegs (mrestrict H mem) (as_store B + s_total) 8 0 /\ val_mem tfibsegs (mrestrict H mem) (as_store B + s_block0) 8 0.
Proof.
  intros B ly H mem S E F. unfold depot_cells_kd in F. rewrite E in F.
  apply Forall_cons_iff in F as [C1 F]. apply Forall_cons_iff in F as [C2 F].
  apply Forall_cons_iff in F as [C3 F]. apply Forall_cons_iff in F as [C4 _].
  unfold z4, z8, c4, c8 in C1, C2, C3, C4.
  apply AF0x.cell_holds_val_mem in C1. apply AF0x.cell_holds_val_mem in C2.
  apply AF0x.cell_holds_val_mem in C3. apply AF0x.cell_holds_val_mem in C4.
  cbn [aeval] in C1, C2, C3, C4. tauto.
Qed.
Lemma b2_zero_cells : forall B ly H mem, Forall (cell_holds B ly (aview tfibsegs H mem)) put_zero_cells ->
  val_mem tfibsegs (mrestrict H mem) (as_depot B + tlm_mu) 4 0 /\
  val_mem tfibsegs (mrestrict H mem) (as_store B + AD3a.bi0_stored) 4 0 /\
  val_mem tfibsegs (mrestrict H mem) (as_store B + bi0_mtx) 4 0.
Proof.
  intros B ly H mem F. unfold put_zero_cells in F.
  apply Forall_cons_iff in F as [C1 F]. apply Forall_cons_iff in F as [C2 F]. apply Forall_cons_iff in F as [C3 _].
  unfold z4, c4 in C1, C2, C3.
  apply AF0x.cell_holds_val_mem in C1. apply AF0x.cell_holds_val_mem in C2. apply AF0x.cell_holds_val_mem in C3.
  cbn [aeval] in C1, C2, C3. tauto.
Qed.
Lemma b2_const_val : forall B ly H mem a (w : nat) v, WireSyms B -> Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly) ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) -> val_mem tfibsegs (mrestrict H mem) a w v.
Proof.
  intros B ly H mem a w v HB HC E. apply (AF0x.cell_holds_val_mem B ly H mem (ANum a) w (ANum v)).
  apply (proj1 (Forall_forall _ _) HC). rewrite (ts_const B HB ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma b2_mod_cells : forall B ly H mem, WireSyms B -> Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly) ->
  mod_cells (mrestrict H mem) /\ mnr_cells (mrestrict H mem).
Proof.
  intros B ly H mem HB HC.
  pose proof (b2_const_val B ly H mem 0x987c8 8 0x130220 HB HC ltac:(vm_compute; reflexivity)) as C1.
  pose proof (b2_const_val B ly H mem 0x130220 8 0x1000 HB HC ltac:(vm_compute; reflexivity)) as C2.
  pose proof (b2_const_val B ly H mem 0x987d8 8 0x1322a8 HB HC ltac:(vm_compute; reflexivity)) as C3.
  pose proof (b2_const_val B ly H mem 0x1323a8 8 0x1010101 HB HC ltac:(vm_compute; reflexivity)) as C4.
  pose proof (b2_const_val B ly H mem 0x132338 8 0 HB HC ltac:(vm_compute; reflexivity)) as C5.
  pose proof (val_mem_byte _ _ 8 _ 4 ltac:(lia) C4) as C4'. change (0x1323a8 + Z.of_nat 4) with 0x1323ac in C4'.
  assert (M : mod_cells (mrestrict H mem)).
  { unfold mod_cells, MOD_PSC_GOT, MOD_PSC, MOD_CF_GOT, MOD_CF.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [| exact C5].
    exists (YG0f.le_byte 0x1010101 8 4). split; [exact C4' | vm_compute; reflexivity]. }
  split; [exact M|].
  unfold mod_cells, mnr_cells, MOD_PSC_GOT, MOD_PSC, MOD_CF_GOT, MOD_CF, MNR_PSC_GOT, MNR_PSC, MNR_CF_GOT, MNR_CF in *. exact M.
Qed.
(* the rows S7 / S1 read stay through any frame that misses [0x98000, 0x133000), the page hull of their cells (end: page_up(common_flags_dont_use + 0x105)). *)
Lemma b2_mod_cells_kept : forall (U : Z -> Prop) H m H' m', kept U H m H' m' -> (forall a, 0x98000 <= a < 0x133000 -> ~ U a) ->
  mod_cells (mrestrict H m) /\ mnr_cells (mrestrict H m) -> mod_cells (mrestrict H' m') /\ mnr_cells (mrestrict H' m').
Proof.
  intros U H m H' m' K NU [M _].
  unfold mod_cells, mnr_cells, MOD_PSC_GOT, MOD_PSC, MOD_CF_GOT, MOD_CF, MNR_PSC_GOT, MNR_PSC, MNR_CF_GOT, MNR_CF in *.
  destruct M as (C1 & C2 & C3 & (f & C4 & F4) & C5).
  assert (G : forall a n v, 0x98000 <= a -> a + Z.of_nat n <= 0x133000 ->
    val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v).
  { intros a n v A1 A2 Hv. apply (kept_val U H m H' m' a n v K); [lia | lia | intros k Hk; apply NU; lia | exact Hv]. }
  assert (R : (forall a n v, 0x98000 <= a -> a + Z.of_nat n <= 0x133000 ->
    val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v) -> True) by (intros; exact I).
  split; (split; [apply G; [lia | cbn; lia | exact C1]|]; split; [apply G; [lia | cbn; lia | exact C2]|];
          split; [apply G; [lia | cbn; lia | exact C3]|]; split; [exists f; split; [apply G; [lia | cbn; lia | exact C4] | exact F4]|];
          apply G; [lia | cbn; lia | exact C5]).
Qed.
Lemma b2_tsd_val : forall B ly H m, WireSyms B -> Forall (cell_holds B ly (aview tfibsegs H m)) (as_const B ly) ->
  ly_tsd ly mod 2 ^ 64 = TFIB_TSD.
Proof.
  intros B ly H m HB HC. rewrite (ts_const B HB) in HC.
  pose proof (proj1 (Forall_forall _ _) HC (c8 (ATp (-88)) (ATsd 0)) ltac:(unfold Tfib_const, Tfib_const_sym; cbn; tauto)) as A.
  pose proof (proj1 (Forall_forall _ _) HC (z8 (ANum 0x5d36b8) 0x5f4ab8)
    ltac:(apply in_app_iff; right; apply in_app_iff; left; unfold Tfib_const_abs; cbn; tauto)) as Bc.
  cbn [cell_holds c_at c_w c_val c8 z8 aeval] in A, Bc. rewrite (ts_tp B HB) in A. change (TFIB_TP + -88) with 6108856 in A.
  rewrite Z.add_0_r in A.
  assert (E8 : forall k, (k < 8)%nat -> YG0f.le_byte (ly_tsd ly mod 2 ^ 64) 8 k = YG0f.le_byte 6245048 8 k).
  { intros k Hk. rewrite <- b2_le_byte_mod64. specialize (A k Hk). specialize (Bc k Hk). rewrite A in Bc. injection Bc as E. exact E. }
  pose proof (AF0x.le_bytes8_sum (ly_tsd ly mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as S1. cbv beta zeta in S1.
  rewrite !E8 in S1 by lia. rewrite <- S1. vm_compute. reflexivity.
Qed.

(* Layout facts: set_ly_NB / set_ly_SB keep every address but the two blocks'. *)
Lemma b2_aclient_NB : forall B ly x S a, aclient_byte B (set_ly_NB ly x) S a <-> aclient_byte B ly S a.
Proof.
  intros B ly x S a.
  assert (E : forall p, sptr_addr B (set_ly_NB ly x) p = sptr_addr B ly p) by (intros p; destruct p; reflexivity).
  unfold aclient_byte. split; intros [(k & K1 & K2 & K3) | (cp & C1 & C2)].
  - left. exists k. rewrite E in K3. tauto.
  - right. exists cp. exact (conj C1 C2).
  - left. exists k. rewrite E. tauto.
  - right. exists cp. exact (conj C1 C2).
Qed.
Lemma b2_ext_SB_NB : forall ly x e, ly_SB ly = 0 -> In e (ext_but_SB (set_ly_NB ly x)) ->
  e = (x, kNodesBlockSize) \/ In e (ext_but_NB ly).
Proof.
  intros ly x e HS He. unfold ext_but_SB, ext_but_NB in *. rewrite HS. cbn [set_ly_NB ly_NB] in He.
  destruct (x =? 0); cbn in He |- *; intuition.
Qed.
Lemma b2_ext_NB_SB : forall ly x e, ly_SB ly = 0 -> In e (ext_but_NB ly) -> In e (ext_but_SB (set_ly_NB ly x)).
Proof.
  intros ly x e HS He. unfold ext_but_SB, ext_but_NB in *. rewrite HS in He. cbn [set_ly_NB ly_NB].
  destruct (x =? 0); cbn in He |- *; intuition.
Qed.
Lemma b2_ext_x : forall ly x, x <> 0 -> In (x, kNodesBlockSize) (ext_but_SB (set_ly_NB ly x)).
Proof.
  intros ly x Hx. unfold ext_but_SB. cbn [set_ly_NB ly_NB]. destruct (Z.eqb_spec x 0) as [E|_]; [contradiction|].
  cbn. tauto.
Qed.
Fixpoint nonbsb (e : aexp) : bool := match e with ANB _ | ASB _ => false | ASh e' => nonbsb e' | _ => true end.
Lemma aeval_nonbsb : forall B ly x sx e, nonbsb e = true -> aeval B (set_ly_SB (set_ly_NB ly x) sx) e = aeval B ly e.
Proof. intros B ly x sx e. induction e; cbn; intros Hn; try reflexivity; try discriminate Hn. rewrite (IHe Hn). reflexivity. Qed.
(* T / C / D against the stack extent and the image extent: ext_but_NB's pairwise disjointness (B2's premise). *)
Lemma b2_tcd_disj : forall ly, ly_SB ly = 0 -> pairwise zdisjoint (ext_but_NB ly) ->
  zdisjoint (ly_T ly, kThreadObjSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\ zdisjoint (ly_T ly, kThreadObjSize) (ly_img ly) /\
  zdisjoint (ly_C ly, 256) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\ zdisjoint (ly_C ly, 256) (ly_img ly) /\
  zdisjoint (ly_D ly, 4096) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\ zdisjoint (ly_D ly, 4096) (ly_img ly).
Proof.
  intros ly HS PD. unfold ext_but_NB in PD. rewrite HS in PD. cbn [Z.eqb app pairwise] in PD.
  destruct PD as (_ & _ & FT & _ & FC & FD & _).
  apply Forall_cons_iff in FT as [_ FT]. apply Forall_cons_iff in FT as [_ FT]. apply Forall_cons_iff in FT as [_ FT].
  apply Forall_cons_iff in FT as [T1 FT]. apply Forall_cons_iff in FT as [T2 _].
  apply Forall_cons_iff in FC as [_ FC]. apply Forall_cons_iff in FC as [C1 FC]. apply Forall_cons_iff in FC as [C2 _].
  apply Forall_cons_iff in FD as [D1 FD]. apply Forall_cons_iff in FD as [D2 _].
  tauto.
Qed.
(* The classifier of as_const's rows for B2's frame: image rows off the store cells and the depot cells Put writes
   (but allocated_, which as_const_g2 drops), thread / ctx / D rows inside their objects, and no NB / SB address. *)
Definition b2_wsafe (a : Z) (w : nat) : bool :=
  forallb (fun k => let y := a + Z.of_nat k in
    (TFIB_IMG_LO <=? y) && (y <? TFIB_IMG_END) && negb ((TFIB_STORE <=? y) && (y <? TFIB_STORE + 32)) &&
    negb ((TFIB_DEPOT <=? y) && (y <? TFIB_DEPOT + d_map1 + 8))) (seq 0 (Nat.max 1 w)).
Lemma b2_wsafe_sound : forall a w, b2_wsafe a w = true -> forall k, 0 <= k < Z.max 1 (Z.of_nat w) ->
  TFIB_IMG_LO <= a + k < TFIB_IMG_END /\ ~ (TFIB_STORE <= a + k < TFIB_STORE + 32) /\
  ~ (TFIB_DEPOT <= a + k < TFIB_DEPOT + d_map1 + 8).
Proof.
  intros a w H k Hk. unfold b2_wsafe in H.
  pose proof (proj1 (forallb_forall _ _) H (Z.to_nat k) ltac:(apply in_seq; lia)) as X. cbv beta zeta in X.
  rewrite Z2Nat.id in X by lia.
  apply andb_prop in X as [X X4]. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2].
  apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply negb_true_iff in X3. apply negb_true_iff in X4.
  split; [lia|]. split.
  - intros [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. rewrite A1, A2 in X3. discriminate.
  - intros [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. rewrite A1, A2 in X4. discriminate.
Qed.
Definition b2_cell_ok (c : acell) : bool :=
  nonbsb (c_at c) && match c_val c with AV e => nonbsb e | AVmask _ _ => true end &&
  match c_at c with
  | ANum a => (a =? TFIB_STORE + ss_alloc) || b2_wsafe a (c_w c)
  | ATsd o => b2_wsafe (TFIB_TSD + o) (c_w c)
  | AInst o => b2_wsafe (TFIB_INST + o) (c_w c)
  | ATp o => b2_wsafe (TFIB_TP + o) (c_w c)
  | AT o => (0 <=? o) && (o + Z.of_nat (Nat.max 1 (c_w c)) <=? kThreadObjSize)
  | AC o => (0 <=? o) && (o + Z.of_nat (Nat.max 1 (c_w c)) <=? 256)
  | AD o => (0 <=? o) && (o + Z.of_nat (Nat.max 1 (c_w c)) <=? 4096)
  | _ => false
  end.
Lemma b2_const_ok : forall ly, forallb b2_cell_ok (Tfib_const ly) = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Lemma b2_obj_off : forall base size o (w : nat) k, in_app base size -> 0 <= o -> o + Z.of_nat (Nat.max 1 w) <= size ->
  0 <= k < Z.max 1 (Z.of_nat w) -> base <= base + o + k < base + size /\ (base + o + k) mod 2 ^ 64 = base + o + k.
Proof.
  intros base size o w k Hb O1 O2 Hk. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
  rewrite Nat2Z.inj_max in O2. change (Z.of_nat 1) with 1 in O2.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Hb. split; [lia|]. apply Z.mod_small. lia.
Qed.
(* as_const without allocated_ over the grown layout, from as_const over ly and a frame U inside the stack extent, the
   depot cells Put writes, the store cells and the two new blocks. *)
Lemma b2_const_kept : forall B ly x sx (U : Z -> Prop) H m H' m',
  WireSyms B -> ly_SB ly = 0 ->
  Forall (cell_holds B ly (aview tfibsegs H m)) (as_const B ly) ->
  img_cover ly -> pairwise zdisjoint (ext_but_NB ly) ->
  Forall (fun e => in_app (fst e) (snd e)) [(ly_T ly, kThreadObjSize); (ly_C ly, 256); (ly_D ly, 4096)] ->
  kHighMemBeg <= ly_stk_lo ly -> TFIB_IMG_END <= x -> TFIB_IMG_END <= sx ->
  Forall (zdisjoint (x, kNodesBlockSize)) (ext_but_NB ly) -> Forall (zdisjoint (sx, kStoreBlockSize)) (ext_but_NB ly) ->
  kept U H m H' m' ->
  (forall a, U a -> (ly_stk_lo ly <= a < ly_stk_hi ly) \/ (TFIB_DEPOT <= a < TFIB_DEPOT + d_map1 + 8) \/
     (TFIB_STORE <= a < TFIB_STORE + 32) \/ (x <= a < x + kNodesBlockSize) \/ (sx <= a < sx + kStoreBlockSize)) ->
  forall c, In c (as_const B (set_ly_SB (set_ly_NB ly x) sx)) -> c_at c <> ANum (as_store B + ss_alloc) ->
  cell_holds B (set_ly_SB (set_ly_NB ly x) sx) (aview tfibsegs H' m') c.
Proof.
  intros B ly x sx U H m H' m' HB HSB HC IC PD TCD Hlo XI SXI DX DSX KP UB c Hc Hna.
  pose proof (b2_tsd_val B ly H m HB HC) as TSD.
  pose proof (b2_tcd_disj ly HSB PD) as (T1 & T2 & C1 & C2 & D1 & D2).
  apply Forall_cons_iff in TCD as [AT TCD]. apply Forall_cons_iff in TCD as [AC TCD]. apply Forall_cons_iff in TCD as [AD _].
  cbn [fst snd] in AT, AC, AD.
  assert (INB : forall e, In e [(ly_T ly, kThreadObjSize); (ly_C ly, 256); (ly_D ly, 4096)] -> In e (ext_but_NB ly)).
  { intros e He. unfold ext_but_NB. cbn in He |- *. intuition. }
  assert (XT := proj1 (Forall_forall _ _) DX _ (INB _ ltac:(cbn; tauto))).
  assert (XC := proj1 (Forall_forall _ _) DX _ (INB (ly_C ly, 256) ltac:(cbn; tauto))).
  assert (XD := proj1 (Forall_forall _ _) DX _ (INB (ly_D ly, 4096) ltac:(cbn; tauto))).
  assert (ST := proj1 (Forall_forall _ _) DSX _ (INB _ ltac:(cbn; tauto))).
  assert (SC := proj1 (Forall_forall _ _) DSX _ (INB (ly_C ly, 256) ltac:(cbn; tauto))).
  assert (SD := proj1 (Forall_forall _ _) DSX _ (INB (ly_D ly, 4096) ltac:(cbn; tauto))).
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
  rewrite (ts_const B HB) in HC, Hc. change (Tfib_const (set_ly_SB (set_ly_NB ly x) sx)) with (Tfib_const ly) in Hc.
  pose proof (proj1 (Forall_forall _ _) HC c Hc) as Hh.
  pose proof (proj1 (forallb_forall _ _) (b2_const_ok ly) c Hc) as OK. unfold b2_cell_ok in OK.
  apply andb_prop in OK as [OK OKa]. apply andb_prop in OK as [N1 N2].
  rewrite (ts_store B HB) in Hna.
  assert (Hh' : cell_holds B (set_ly_SB (set_ly_NB ly x) sx) (aview tfibsegs H m) c).
  { unfold cell_holds in *. rewrite (aeval_nonbsb B ly x sx _ N1).
    destruct (c_val c) as [e|mk v] eqn:EV; [| exact Hh]. rewrite (aeval_nonbsb B ly x sx _ N2). exact Hh. }
  apply (cell_agree B _ (aview tfibsegs H m) (aview tfibsegs H' m') c); [| exact Hh'].
  intros k Hk. apply (kept_aview U H m H' m' _ KP). intros HU. apply UB in HU.
  rewrite (aeval_nonbsb B ly x sx _ N1) in HU.
  clear Hh Hh' N2 HC Hc. revert HU OKa Hna N1. destruct (c_at c) as [a|o|o|o|o|o|o|o|r o|o|o|o|o|o|o|o|o|o|e];
    intros HU OKa Hna N1; cbn [aeval] in HU; try discriminate OKa.
  - (* ANum *) apply orb_true_iff in OKa as [E|W'].
    + apply Z.eqb_eq in E. subst a. exact (Hna eq_refl).
    + destruct (b2_wsafe_sound a _ W' k Hk) as (W1 & W2 & W3).
      rewrite Z.mod_small in HU by (unfold TFIB_IMG_LO, TFIB_IMG_END in W1; lia).
      clear - HU W1 W2 W3 Hlo XI SXI.
      unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, TFIB_DEPOT, TFIB_STORE, d_map1 in *. lia.
  - (* AT *) apply andb_prop in OKa as [O1 O2]. apply Z.leb_le in O1. apply Z.leb_le in O2.
    destruct (b2_obj_off _ _ o (c_w c) k AT O1 O2 Hk) as [B1 EM]. rewrite EM in HU.
    clear - HU B1 T1 T2 XT ST IC Hlo.
    unfold zdisjoint, img_cover in *. cbn [fst snd] in *.
    unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, TFIB_DEPOT, TFIB_STORE, d_map1, kThreadObjSize, kNodesBlockSize, kStoreBlockSize in *. lia.
  - (* AC *) apply andb_prop in OKa as [O1 O2]. apply Z.leb_le in O1. apply Z.leb_le in O2.
    destruct (b2_obj_off _ _ o (c_w c) k AC O1 O2 Hk) as [B1 EM]. rewrite EM in HU.
    clear - HU B1 C1 C2 XC SC IC Hlo.
    unfold zdisjoint, img_cover in *. cbn [fst snd] in *.
    unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, TFIB_DEPOT, TFIB_STORE, d_map1, kNodesBlockSize, kStoreBlockSize in *. lia.
  - (* ATsd *) destruct (b2_wsafe_sound _ _ OKa k Hk) as (W1 & W2 & W3).
    assert (E : (ly_tsd ly + o + k) mod 2 ^ 64 = TFIB_TSD + o + k).
    { replace (ly_tsd ly + o + k) with (ly_tsd ly + (o + k)) by lia. rewrite <- Zplus_mod_idemp_l, TSD.
      rewrite Z.mod_small by (unfold TFIB_IMG_LO, TFIB_IMG_END in W1; lia). lia. }
    rewrite E in HU. clear - HU W1 W2 W3 Hlo XI SXI.
    unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, TFIB_DEPOT, TFIB_STORE, d_map1 in *. lia.
  - (* AInst *) rewrite (ts_inst B HB) in HU. destruct (b2_wsafe_sound _ _ OKa k Hk) as (W1 & W2 & W3).
    rewrite Z.mod_small in HU by (unfold TFIB_IMG_LO, TFIB_IMG_END in W1; lia).
    clear - HU W1 W2 W3 Hlo XI SXI.
    unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, TFIB_DEPOT, TFIB_STORE, d_map1 in *. lia.
  - (* ATp *) rewrite (ts_tp B HB) in HU. destruct (b2_wsafe_sound _ _ OKa k Hk) as (W1 & W2 & W3).
    rewrite Z.mod_small in HU by (unfold TFIB_IMG_LO, TFIB_IMG_END in W1; lia).
    clear - HU W1 W2 W3 Hlo XI SXI.
    unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, TFIB_DEPOT, TFIB_STORE, d_map1 in *. lia.
  - (* AD *) apply andb_prop in OKa as [O1 O2]. apply Z.leb_le in O1. apply Z.leb_le in O2.
    destruct (b2_obj_off _ _ o (c_w c) k AD O1 O2 Hk) as [B1 EM]. rewrite EM in HU.
    clear - HU B1 D1 D2 XD SD IC Hlo.
    unfold zdisjoint, img_cover in *. cbn [fst snd] in *.
    unfold TFIB_IMG_LO, TFIB_IMG_END, kHighMemBeg, TFIB_DEPOT, TFIB_STORE, d_map1, kNodesBlockSize, kStoreBlockSize in *. lia.
Qed.
(* Put's callee-saved registers and frame through a callee or a walk segment. *)
Lemma b2_put_cs_pres : forall B rg rg' regs0 tr, regs_preserved rg rg' -> AD3k.put_cs B rg regs0 tr -> AD3k.put_cs B rg' regs0 tr.
Proof.
  intros B rg rg' regs0 tr RP C. unfold AD3k.put_cs in *. cbv zeta in *.
  destruct C as (C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C3 & C4 & C26 & C27).
  split; [rpw RP (18%bv : bv 5) 18; exact C18|]. split; [rpw RP (19%bv : bv 5) 19; exact C19|].
  split; [rpw RP (20%bv : bv 5) 20; exact C20|]. split; [rpw RP (21%bv : bv 5) 21; exact C21|].
  split; [rpw RP (22%bv : bv 5) 22; exact C22|]. split; [rpw RP (23%bv : bv 5) 23; exact C23|].
  split; [rpw RP (24%bv : bv 5) 24; exact C24|]. split; [rpw RP (25%bv : bv 5) 25; exact C25|].
  split; [rpw RP (3%bv : bv 5) 3; exact C3|]. split; [rpw RP (4%bv : bv 5) 4; exact C4|].
  split; [rpw RP (26%bv : bv 5) 26; exact C26|]. rpw RP (27%bv : bv 5) 27; exact C27.
Qed.
Lemma b2_put_saved_kept : forall (U : Z -> Prop) H m H' m' regs0, kept U H m H' m' -> 112 <= spZ regs0 ->
  (forall a, spZ regs0 - 112 <= a < spZ regs0 -> ~ U a) -> AD3k.put_saved H m regs0 -> AD3k.put_saved H' m' regs0.
Proof.
  intros U H m H' m' regs0 K SP NU PS. pose proof (u64_range (getr regs0 2)) as R.
  unfold AD3k.put_saved in *. cbv zeta in *. unfold spZ in *.
  destruct PS as (S1 & S8 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25).
  repeat split; (eapply kept_val; [exact K | lia | lia | intros k Hk; apply NU; lia | eassumption]).
Qed.
Lemma b2_put_frame_kept : forall (U : Z -> Prop) H m H' m' regs0 buf tr, kept U H m H' m' -> 112 <= spZ regs0 ->
  (forall a, spZ regs0 - 112 <= a < spZ regs0 -> ~ U a) -> AD3k.put_frame H m regs0 buf tr -> AD3k.put_frame H' m' regs0 buf tr.
Proof.
  intros U H m H' m' regs0 buf tr K SP NU (PS & PB & PN).
  pose proof (u64_range (getr regs0 2)) as R.
  split; [exact (b2_put_saved_kept U H m H' m' regs0 K SP NU PS)|].
  unfold spZ in *.
  split; (eapply kept_val; [exact K | lia | lia | intros k Hk; apply NU; lia | eassumption]).
Qed.
(* the model after a map: mmap_model's maps are the old ones plus the grant (YK0v.v:99-107). *)
Lemma b2_mmap_vm : forall a n m, vm_limit (m_vmmaps (mmap_model a n m)) = vm_limit (m_vmmaps m) /\
  vm_reserved (m_vmmaps (mmap_model a n m)) = vm_reserved (m_vmmaps m) /\
  alloc_top (m_vmmaps (mmap_model a n m)) = alloc_top (m_vmmaps m) /\
  vm_maps (m_vmmaps (mmap_model a n m)) = (a, n) :: vm_maps (m_vmmaps m) /\ m_vm_lazy (mmap_model a n m) = m_vm_lazy m.
Proof.
  intros a n m. unfold mmap_model, alloc_top. rewrite YK0g.m_vmmaps_with_vmmaps, YK0g.m_vm_lazy_with_vmmaps.
  repeat split; reflexivity.
Qed.
Lemma b2_eager_eq : forall m m', m_vmmaps m = m_vmmaps m' -> m_vm_lazy m = m_vm_lazy m' -> eager_used m = eager_used m'.
Proof. intros m m' E1 E2. unfold eager_used. rewrite E1, E2. reflexivity. Qed.
(* The address zones of the walk: Put's stack, the trace buffer, the bucket, the trace length; the nodes block x; the
   store block sx. *)
Definition b2_zone0 (sp lo hi buf b1 n : Z) : Prop :=
  kHighMemBeg <= lo /\ lo <= sp - DEP_STK /\ sp <= hi /\ hi <= kHighMemEnd /\ sp mod 16 = 0 /\
  lo <= buf /\ buf + 8 * 30 <= hi /\ (buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf) /\ 0 <= b1 < 2 ^ 20 /\ 1 <= n <= 30.
Definition b2_zoneX (lo hi x : Z) : Prop :=
  TFIB_IMG_END <= x /\ x + kNodesBlockSize <= 0x7fffff800000 /\ (x + kNodesBlockSize <= lo \/ hi <= x).
Definition b2_zoneY (lo hi x sx : Z) : Prop :=
  TFIB_IMG_END <= sx /\ sx + kStoreBlockSize <= 0x7fffff800000 /\ (sx + kStoreBlockSize <= lo \/ hi <= sx) /\
  (x + kNodesBlockSize <= sx \/ sx + kStoreBlockSize <= x).
(* lia on the arithmetic hypotheses only (the zones, Z / nat comparisons and equations, their boolean combinations). *)
Ltac b2_keepz := repeat match goal with
  | X : ?T |- _ => lazymatch type of T with Prop =>
      lazymatch T with
      | b2_zone0 _ _ _ _ _ _ => fail | b2_zoneX _ _ _ => fail | b2_zoneY _ _ _ _ => fail
      | (_ <= _)%Z => fail | (_ < _)%Z => fail | (_ /\ _) => fail | (_ \/ _) => fail | ~ _ => fail
      | @eq Z _ _ => fail | (_ < _)%nat => fail | (_ <= _)%nat => fail
      | _ => clear X end end end.
Ltac b2z := cbv beta in *; b2_keepz;
  unfold b2_zone0, b2_zoneX, b2_zoneY, tlm_mu, TLM_STK, BIC_STK, kHighMemBeg, kHighMemEnd, DEP_STK, TFIB_IMG_END, TFIB_IMG_LO, TFIB_DEPOT, TFIB_STORE, kNodesBlockSize, kStoreBlockSize, d_nuniq, d_map1, MOD_STK, MNR_STK, s_total, s_block0, ss_alloc, bi0_mtx, AD3a.bi0_stored, d_tab_words in *; lia.
Section kd.
(* PLACEHOLDER, the S-pieces' (AD3g.v:134-135, AD3c.v:167-168): the first Put's layout growth and its two intro lemmas,
   plus a Theorem Labs lane's layout_grow_trans (B2 composes S7's step ly -> set_ly_NB ly nb with S1's set_ly_NB ly nb -> ly').
   Satisfiable: layout_grow_kd := fun _ _ => True. Swap: a Theorem Labs lane's layout_grow, layout_grow_NB, layout_grow_SB,
   layout_grow_trans (YG0f.v:100-121). *)
Variable layout_grow_kd : alayout -> alayout -> Prop.
Hypothesis kd_grow_NB : forall ly nb, ly_NB ly = 0 -> layout_grow_kd ly (set_ly_NB ly nb).
Hypothesis kd_grow_SB : forall ly sb, ly_SB ly = 0 -> layout_grow_kd ly (set_ly_SB ly sb).
Hypothesis kd_grow_trans : forall l1 l2 l3, layout_grow_kd l1 l2 -> layout_grow_kd l2 l3 -> layout_grow_kd l1 l3.

(* PLACEHOLDER for YG0n.depot_ok (B ly rd S; YG0n.v:194), with its two branch lemmas: depot_ok_pre (YG0n.v:224) and
   depot_ok_post (YG0n.v:235), depot_pick at its knock argument. Satisfiable: depot_ok_rev5 (Qed above).
   Swap: depot_ok_kd := YG0n.depot_ok, depot_ok_pre_kd := depot_ok_pre, depot_ok_post_kd := depot_ok_post. *)
Variable depot_ok_kd : asyms -> alayout -> reader -> astate -> Prop.
Hypothesis depot_ok_pre_kd : forall B ly rd S, st_depot S = [] -> (depot_ok_kd B ly rd S <-> depot_ok_pre_text B ly rd S).
Hypothesis depot_ok_post_kd : forall B ly rd S, st_depot S <> [] -> (depot_ok_kd B ly rd S <-> depot_ok_post_text B ly rd S).

(* INTERIM: as_const without its allocated_ row (AF0m.v:129, ACell (ANum 0x172650) 0 (AV (ANum 0)), = as_store B +
   ss_alloc), which the first Put makes kStoreBlockSize (S3's post, AD3c.v:220). The row is already zero-width here and
   the kernel's depot_cells carries allocated_ (YG0n.v:118 / :120: 0 before the first Put, kStoreBlockSize after); the Variable stays,
   and kd_inst instantiates it with as_const_g2f. Satisfiable: as_const_g2 B ly := filter of as_const B ly by c_at c <> that address. *)
Variable as_const_g2 : asyms -> alayout -> list acell.
Hypothesis as_const_g2_def : forall B ly c, In c (as_const_g2 B ly) <-> In c (as_const B ly) /\ c_at c <> ANum (as_store B + ss_alloc).

(* ===== put_effect ly W md ly' W' md': what ONE StackDepot Put does to the layout,
   the world and the model.
   Left arm, no map (a Put after the first one, or no Put at all): layout and world unchanged, the model changed only in
   its materialization (same_but_materialized, YK04.v:540-541: md' = with_vm_backing (m_vm_lazy md) mat md, as
   tfib_depot_spec's post states it).
   Right arm, the first Put (B2): both blocks unmapped before (ly_NB ly = ly_SB ly = 0), mapped at nb, sb <> 0 after;
   ly' = set_ly_SB (set_ly_NB ly nb) sb with the layout step layout_grow_kd ly ly'; W grows by exactly the two blocks
   (w_A consed, w_H unchanged outside them); the model as S7 (AD3g.v:177-178) and S1 (AD3a.v:97-98) state it after
   the two maps: no I/O change, the maps of mmap_model sb (mmap_model nb md), the store block lazy.
   put_effect_refl: the left arm. put_effect_trans: left-left by wvb_wvb (YA0o.v:21), left-right / right-left because
   the right arm reads md only through m_vmmaps, m_vm_lazy and same_io, which with_vm_backing keeps; right-right is
   void (the second right arm needs ly_NB = 0, the first left nb <> 0). ===== *)
Definition put_effect (ly : alayout) (W : world tfibsegs) (md : Model) (ly' : alayout) (W' : world tfibsegs) (md' : Model) : Prop :=
  (ly' = ly /\ W' = W /\ same_but_materialized md md') \/
  (exists nb sb : Z,
     ly_NB ly = 0 /\ ly_SB ly = 0 /\ nb <> 0 /\ sb <> 0 /\
     ly' = set_ly_SB (set_ly_NB ly nb) sb /\ layout_grow_kd ly ly' /\
     w_A W' = (sb, sb + kStoreBlockSize) :: (nb, nb + kNodesBlockSize) :: w_A W /\
     (forall a : word, ~ (nb <= bv_unsigned a < nb + kNodesBlockSize) -> ~ (sb <= bv_unsigned a < sb + kStoreBlockSize) ->
        w_H W' a = w_H W a) /\
     same_io md md' /\
     m_vmmaps md' = m_vmmaps (mmap_model (Z_to_bv 64 sb) (Z_to_bv 64 kStoreBlockSize)
                               (mmap_model (Z_to_bv 64 nb) (Z_to_bv 64 kNodesBlockSize) md)) /\
     m_vm_lazy md' = (Z_to_bv 64 sb, Z_to_bv 64 kStoreBlockSize) :: m_vm_lazy md).

Lemma put_effect_refl : forall ly W md, put_effect ly W md ly W md.
Proof using.
  intros ly W md. left. split; [reflexivity|]. split; [reflexivity|]. apply same_but_materialized_refl.
Qed.

Lemma put_effect_trans : forall ly1 W1 md1 ly2 W2 md2 ly3 W3 md3,
  put_effect ly1 W1 md1 ly2 W2 md2 -> put_effect ly2 W2 md2 ly3 W3 md3 -> put_effect ly1 W1 md1 ly3 W3 md3.
Proof using.
  intros ly1 W1 md1 ly2 W2 md2 ly3 W3 md3
    [(E1 & E2 & M1) | (nb & sb & N1 & S1 & NZ & SZ & EL & LG & WA & WH & IO & VM & LZ)]
    [(E3 & E4 & M2) | (nb' & sb' & N1' & S1' & NZ' & SZ' & EL' & LG' & WA' & WH' & IO' & VM' & LZ')].
  - subst ly2 W2 ly3 W3. left. split; [reflexivity|]. split; [reflexivity|]. exact (sbm_trans _ _ _ M1 M2).
  - subst ly2 W2. right. exists nb', sb'.
    do 6 (split; [assumption|]). split; [rewrite WA'; reflexivity|]. split; [exact WH'|].
    split; [exact (same_io_trans3 _ _ _ (sbm_io _ _ M1) IO')|].
    split; [rewrite VM'; apply mmap_model_vmmaps_eq, mmap_model_vmmaps_eq, (sbm_vmmaps _ _ M1)|].
    rewrite LZ', (sbm_lazy _ _ M1). reflexivity.
  - subst ly3 W3. right. exists nb, sb.
    do 6 (split; [assumption|]). split; [exact WA|]. split; [exact WH|].
    split; [exact (same_io_trans3 _ _ _ IO (sbm_io _ _ M2))|].
    split; [rewrite (sbm_vmmaps _ _ M2); exact VM|].
    rewrite (sbm_lazy _ _ M2). exact LZ.
  - exfalso. apply NZ. rewrite EL in N1'. exact N1'.
Qed.

(* tfib_depot_spec's post (lib/A/AFl0.v:81-88) at the state after the Put (ly', W', md'): the old text with ly, W and
   the reader's world replaced by ly', W', and the model of c' by md'; its W' = W and md' = with_vm_backing (m_vm_lazy
   md) mat md are put_effect's left arm. *)
Definition depot_put_post (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (tr : list Z)
  (ly' : alayout) (W' : world tfibsegs) (md' : Model) (c' : config) : Prop :=
  let H := w_H W in let sp := bv_unsigned (getr regs 2) in
  exists z regs' mem',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
    aok S (KDepot tr) z /\
    regs_preserved regs regs' /\
    (forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ~ depot_footprint B ly' (bv_unsigned x) -> mem' x = mem x) /\
    (forall a, apresent H mem a -> apresent (w_H W') mem' a) /\
    depot_mem_ok B ly' (depot_after z tr S) (aview tfibsegs (w_H W') mem') /\
    Forall (cell_holds B ly' (aview tfibsegs (w_H W') mem')) (as_const B ly').

(* The early return of a Put on a size-0 trace (0x71ee8 beqz -> 0x720bc): a0 = 0, nothing inserted (aok's z = 0),
   nothing mapped (put_effect's left arm: ly' = ly, W' = W), memory written only in Put's frame. tfib_depot_put_any's
   empty-depot case with tr = []. *)
Definition depot_put_early (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (tr : list Z)
  (ly' : alayout) (W' : world tfibsegs) (md' : Model) (c' : config) : Prop :=
  let sp := bv_unsigned (getr regs 2) in
  ly' = ly /\ W' = W /\
  exists regs' mem',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
    aok S (KDepot tr) 0 /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_preserved regs regs' /\
    (forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> mem' x = mem x) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

(* ===== B2's post at the state after the Put (ly', W', md'), nb := ly_NB ly', sb := ly_SB ly' (the layout, world and
   model change itself is put_effect's right arm). a0 = 1 (the new id), callee-saved registers kept; the oracle
   answer z = 1 (aok); memory unchanged outside DEP_STK and the depot footprint over ly'; presence grows; as_const
   over ly' without its allocated_ row (as_const_g2, INTERIM); depot_first_put_facts and allocated_ = kStoreBlockSize; the
   post-Put depot_ok_kd over ly' / S'; the placement of both blocks; the model takes both blocks and keeps what it
   took; both blocks miss every map of the Put's entry model md (amendment 11). ===== *)
Definition depot_first_put_post (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (tr : list Z)
  (ly' : alayout) (W' : world tfibsegs) (md' : Model) (c' : config) : Prop :=
  let H := w_H W in let sp := spZ regs in let nb := ly_NB ly' in let sb := ly_SB ly' in
  let S' := depot_after 1 tr S in
  exists (regs' : bvmap 5 word) (mem' : word -> option byte),
      let rd' := aview tfibsegs (w_H W') mem' in
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
      aok S (KDepot tr) 1 /\
      getr regs' 10 = Z_to_bv 64 1 /\ regs_preserved regs regs' /\
      (* memory *)
      (forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ~ depot_footprint B ly' (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent H mem a -> apresent (w_H W') mem' a) /\
      Forall (cell_holds B ly' rd') (as_const_g2 B ly') /\
      (* the first Put's facts (depot_first_put_facts), allocated_ (a post-Put depot cell, YG0n.v:120), and the post-Put depot_ok *)
      depot_first_put_facts B ly' S' tr rd' /\
      cell_holds B ly' rd' (z8 (AStore ss_alloc) kStoreBlockSize) /\
      depot_ok_kd B ly' rd' S' /\
      (* placement *)
      YG0f.page_aligned nb /\ in_app nb kNodesBlockSize /\ YG0f.page_aligned sb /\ in_app sb kStoreBlockSize /\
      zdisjoint (nb, kNodesBlockSize) (sb, kStoreBlockSize) /\
      Forall (zdisjoint (nb, kNodesBlockSize)) (first_put_avoid ly S) /\
      Forall (zdisjoint (sb, kStoreBlockSize)) (first_put_avoid ly S) /\
      (forall a, aclient_byte B ly S a -> ~ in_zr a (nb, kNodesBlockSize) /\ ~ in_zr a (sb, kStoreBlockSize)) /\
      (* takes *)
      md_takes md' (nb, kNodesBlockSize) /\ md_takes md' (sb, kStoreBlockSize) /\
      (forall e, md_takes md e -> md_takes md' e) /\
      (* fresh against every map of md *)
      Forall (fun q => zdisjoint (nb, kNodesBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_maps (m_vmmaps md)) /\
      Forall (fun q => zdisjoint (sb, kStoreBlockSize) (bv_unsigned (fst q), bv_unsigned (snd q))) (vm_maps (m_vmmaps md)).

(* ===== B2: the first StackDepotPut(buf, length tr), the depot empty.
   PRE: the empty depot as the kernel's knock ARm (YG0n.v:380-400) states it (am_depot: depot_ok_kd, pre-Put branch; am_cells: depot_cells_kd;
   am_const), the three zero cells of put_zero_cells (:152-153), Wf / In tr /
   1 <= length tr for the counting lemmas and Put's size test, the model facts S7 / S1 need (room, ivs_wf,
   ceil_of_top, takes), img_cover, and tfib_depot_spec's register / trace / stack premises (AFl0.v:75-79) with the
   stack's high-memory bounds. POST: exists ly' md', put_effect ly W md ly' W' md' /\ depot_first_put_post at ly' W' md'
   (SRr, normal return to ra; W' is SRr's post world). ===== *)
Definition tfib_depot_first_put_spec (B : asyms) : Prop :=
  forall (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte)
         (md : Model) (buf : Z) (tr : list Z),
  let H := w_H W in let rd := aview tfibsegs H mem in let m := mrestrict H mem in let sp := spZ regs in
  st_depot S = [] -> depot_ok_kd B ly rd S -> Forall (cell_holds B ly rd) (depot_cells_kd S) ->
  Forall (cell_holds B ly rd) put_zero_cells ->
  Forall (cell_holds B ly rd) (as_const B ly) -> img_cover ly -> pairwise zdisjoint (ext_but_NB ly) ->
  Forall (fun e => in_app (fst e) (snd e)) [(ly_T ly, kThreadObjSize); (ly_C ly, 256); (ly_D ly, 4096)] ->
  Wf (as_universe B) S -> In tr (as_universe B) -> (1 <= length tr)%nat ->
  depot_room_at W md -> YK0g.ivs_wf (vm_maps (m_vmmaps md)) -> YM05.ceil_of_top (alloc_top (m_vmmaps md)) ->
  Forall (md_takes md) (first_put_avoid ly S) -> (forall a, aclient_byte B ly S a -> md_takes md (a, 1)) ->
  md_takes md (TFIB_IMG_LO, TFIB_IMG_END - TFIB_IMG_LO) ->
  getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) -> YK0s.ret_ok (getr regs 1) ->
  (forall i, (i < length tr)%nat -> val_mem tfibsegs m (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
  buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly -> buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf ->
  sp mod 16 = 0 -> kHighMemBeg <= ly_stk_lo ly -> ly_stk_hi ly <= kHighMemEnd ->
  ly_stk_lo ly <= sp - DEP_STK -> sp <= ly_stk_hi ly -> (forall a, sp - DEP_STK <= a < sp -> apresent H mem a) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
    (fun W' c' => exists (ly' : alayout) (md' : Model),
       put_effect ly W md ly' W' md' /\ depot_first_put_post B W ly S regs mem md tr ly' W' md' c').

(* B2's own premises (those tfib_depot_spec does not have), bundled for tfib_depot_put_any's empty case, in
   tfib_depot_first_put_spec's order, without 1 <= length tr (tfib_depot_put_any covers tr = [] by depot_put_early,
   Put's size-0 early return). *)
Definition depot_first_put_pre (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (mem : word -> option byte)
  (md : Model) (tr : list Z) : Prop :=
  let H := w_H W in let rd := aview tfibsegs H mem in
  depot_ok_kd B ly rd S /\ Forall (cell_holds B ly rd) (depot_cells_kd S) /\ Forall (cell_holds B ly rd) put_zero_cells /\
  pairwise zdisjoint (ext_but_NB ly) /\
  Forall (fun e => in_app (fst e) (snd e)) [(ly_T ly, kThreadObjSize); (ly_C ly, 256); (ly_D ly, 4096)] /\
  depot_room_at W md /\ YK0g.ivs_wf (vm_maps (m_vmmaps md)) /\ YM05.ceil_of_top (alloc_top (m_vmmaps md)) /\
  Forall (md_takes md) (first_put_avoid ly S) /\ (forall a, aclient_byte B ly S a -> md_takes md (a, 1)) /\
  md_takes md (TFIB_IMG_LO, TFIB_IMG_END - TFIB_IMG_LO) /\
  kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.

(* ===== Every Put, first or later (header): tfib_depot_spec's shared premises in its order (AFl0.v:73-79), B2's own
   under st_depot S = [], tfib_depot_spec's own under st_depot S <> []; the post of the arm that runs: the first Put
   (empty depot, tr <> []), the early return (empty depot, tr = []), a later Put (st_depot S <> []). ===== *)
Definition tfib_depot_put_any_spec (B : asyms) : Prop :=
  forall (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte)
         (md : Model) (buf : Z) (tr : list Z),
  let H := w_H W in let rd := aview tfibsegs H mem in let sp := bv_unsigned (getr regs 2) in
  img_cover ly -> Wf (as_universe B) S -> In tr (as_universe B) -> Forall (cell_holds B ly rd) (as_const B ly) ->
  (st_depot S = [] -> depot_first_put_pre B W ly S mem md tr) ->
  (st_depot S <> [] -> layout_ok ly /\ depot_mem_ok B ly S rd) ->
  getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
  getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
  (forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict H mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
  buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly -> buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf ->
  sp mod 16 = 0 -> ly_stk_lo ly <= sp - DEP_STK -> sp <= ly_stk_hi ly -> (forall a, sp - DEP_STK <= a < sp -> apresent H mem a) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
    (fun W' c' => exists (ly' : alayout) (md' : Model),
       put_effect ly W md ly' W' md' /\
       (st_depot S = [] -> tr <> [] -> depot_first_put_post B W ly S regs mem md tr ly' W' md' c') /\
       (st_depot S = [] -> tr = [] -> depot_put_early B W ly S regs mem md tr ly' W' md' c') /\
       (st_depot S <> [] -> depot_put_post B W ly S regs mem md tr ly' W' md' c')).

(* The size-0 early return (AD3k's K0 walk segment, to come): the run ends at ra with depot_put_early's facts. *)
Lemma depot_put_early_ok : forall B, WireSyms B ->
  forall (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte)
         (md : Model) (tr : list Z),
  let H := w_H W in let sp := bv_unsigned (getr regs 2) in
  tr = [] -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) -> YK0s.ret_ok (getr regs 1) ->
  sp mod 16 = 0 -> kHighMemBeg <= ly_stk_lo ly -> ly_stk_hi ly <= kHighMemEnd ->
  ly_stk_lo ly <= sp - DEP_STK -> sp <= ly_stk_hi ly -> (forall a, sp - DEP_STK <= a < sp -> apresent H mem a) ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
    (fun W' c' => same_but_materialized md (cfg_model c') /\
                  depot_put_early B W ly S regs mem md tr ly W' (cfg_model c') c').
Proof using.
  intros B HB W ly S regs mem md tr. cbv zeta. intros ETR R11 Hra Hsp16 HM1 HM2 Hslo Hshi Pstk. subst tr.
  apply (AD3k.put_size0 W regs mem md _ R11 Hra).
  - unfold spZ. unfold kHighMemBeg, DEP_STK in *. lia.
  - intros a Ha. apply Pstk. unfold spZ in Ha. unfold DEP_STK. lia.
  - intros regs1 mem1 mat X10 RP FR PR. apply SRr_ret. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. exists regs1, mem1.
    split; [reflexivity|]. split; [left; reflexivity|]. split; [exact X10|]. split; [exact RP|].
    split; [| exact PR]. intros w Hw. apply FR. unfold spZ, DEP_STK in *. lia.
Qed.

(* ===== first_put_layout's helpers (the kernel's owned_extents / static_extents / vis0_zones hold the empty extent
   (4096, 0) at the NB / SB positions while ly_NB ly = ly_SB ly = 0, YG0f.v:375-399). ===== *)

(* The three lists before the first Put, in the shape A ++ e1 :: e2 :: Bl with e1 = e2 = (4096, 0) the NB / SB slots;
   after it the kernel's owned_extents_set / static_extents_set / vis0_zones_set give the blocks at the same positions. *)
Lemma first_put_old : forall ly, ly_NB ly = 0 -> ly_SB ly = 0 ->
  owned_extents ly = [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize);
    (ly_F ly, kFakeStackSize)] ++ (4096, 0) :: (4096, 0) :: [(ly_C ly, 256); (ly_D ly, 4096)] /\
  static_extents ly = [(ly_prim ly, kPrimResvSize); (ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize);
    (ly_F ly, kFakeStackSize)] ++ (4096, 0) :: (4096, 0) ::
    [(ly_C ly, 256); (ly_D ly, 4096); (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly); ly_img ly] /\
  vis0_zones ly = [(ly_T ly, kThreadObjSize); (ly_F ly, kFakeStackSize)] ++ (4096, 0) :: (4096, 0) ::
    ([(ly_C ly, kCtxMapSize); (ly_D ly, 4096); (ly_Q ly, kPtrArrayResv); (ly_space ly + kRegionInfoOff, 4096); ly_img ly]
     ++ ly_extra ly).
Proof using.
  intros ly N0 S0. unfold static_extents, owned_extents, vis0_zones. rewrite N0, S0.
  split; [|split]; reflexivity.
Qed.

(* Replacing the two entries e1 e2 of A ++ e1 :: e2 :: Bl by n1 n2: Forall (P n1, P n2), and pairwise for a symmetric R
   (n1, n2 R-apart from A ++ Bl and from each other; the prefixed form for ly_extra ly ++ static_extents ly). *)
Lemma first_put_forall_swap2 {X : Type} (P : X -> Prop) (A Bl : list X) (e1 e2 n1 n2 : X) :
  Forall P (A ++ e1 :: e2 :: Bl) -> P n1 -> P n2 -> Forall P (A ++ n1 :: n2 :: Bl).
Proof using.
  intros H H1 H2. apply Forall_app in H as [HA H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [_ HB].
  apply Forall_app. split; [exact HA|]. apply Forall_cons; [exact H1|]. apply Forall_cons; [exact H2 | exact HB].
Qed.

Lemma first_put_pairwise_core {X : Type} (R : X -> X -> Prop) (Rs : forall a b, R a b -> R b a) :
  forall (A Bl : list X) (e1 e2 n1 n2 : X),
  pairwise R (A ++ e1 :: e2 :: Bl) -> Forall (R n1) (A ++ Bl) -> Forall (R n2) (A ++ Bl) -> R n1 n2 ->
  pairwise R (A ++ n1 :: n2 :: Bl).
Proof using.
  induction A as [|a A IH]; intros Bl e1 e2 n1 n2 HP F1 F2 R12; cbn [app pairwise] in *.
  - destruct HP as (_ & _ & HB). split; [apply Forall_cons; [exact R12 | exact F1]|]. split; [exact F2 | exact HB].
  - destruct HP as (Fa & HP). apply Forall_cons_iff in F1 as [R1a F1]. apply Forall_cons_iff in F2 as [R2a F2].
    split; [|exact (IH Bl e1 e2 n1 n2 HP F1 F2 R12)].
    apply Forall_app in Fa as [FaA FaB]. apply Forall_cons_iff in FaB as [_ FaB]. apply Forall_cons_iff in FaB as [_ FaB].
    apply Forall_app. split; [exact FaA|].
    apply Forall_cons; [exact (Rs _ _ R1a)|]. apply Forall_cons; [exact (Rs _ _ R2a) | exact FaB].
Qed.

Lemma first_put_pairwise_swap2 {X : Type} (R : X -> X -> Prop) (Rs : forall a b, R a b -> R b a) :
  forall (A0 A Bl : list X) (e1 e2 n1 n2 : X),
  pairwise R (A0 ++ A ++ e1 :: e2 :: Bl) -> Forall (R n1) A0 -> Forall (R n2) A0 ->
  Forall (R n1) (A ++ Bl) -> Forall (R n2) (A ++ Bl) -> R n1 n2 -> pairwise R (A0 ++ A ++ n1 :: n2 :: Bl).
Proof using.
  intros A0 A Bl e1 e2 n1 n2 HP H01 H02 H1 H2 H12. rewrite app_assoc in HP |- *.
  refine (first_put_pairwise_core R Rs (A0 ++ A) Bl e1 e2 n1 n2 HP _ _ H12);
    rewrite <- app_assoc; apply Forall_app; split; assumption.
Qed.

(* The empty slot (4096, 0) shadows no range of positive length: its window [shadow_addr 4096, shadow_addr 4095 + 1)
   is empty. *)
Lemma first_put_empty_zone : forall v : Z * Z, 0 < snd v ->
  ~ (shadow_addr (fst (4096, 0)) <= fst v /\ fst v + snd v <= shadow_addr (fst (4096, 0) + snd (4096, 0) - 1) + 1).
Proof using.
  intros v Hv [H1 H2].
  assert (E : shadow_addr (fst (4096, 0) + snd (4096, 0) - 1) + 1 = shadow_addr (fst (4096, 0))) by reflexivity.
  lia.
Qed.

(* lo_vis0's positivity: every ly_vis0 range has positive length. The cover half of lo_vis0 alone does not give it,
   and first_put_layout needs it: without it v = (shadow_addr 4096, 0) lies in the empty NB slot (4096, 0) of ly and in
   no zone of ly' when nb, sb and the other zones start away from [4096, 4103]. The kernel's knock lo_vis0 states it
   (YG0f.v:449-453, its second conjunct at :453; lo_vis0_pos :467, depot_pick True X is X in knock). *)
Lemma first_put_vis0_pos : forall ly, layout_ok ly -> Forall (fun v => 0 < snd v) (ly_vis0 ly).
Proof using.
  intros ly LO. exact (lo_vis0_pos ly LO).
Qed.

(* lo_vis0 at the grown layout, from the positivity of ly's ranges: a zone of ly that shadows a range of positive length
   is not an empty slot, so it is a zone of ly' (vis0_zones ly' is vis0_zones ly with the slots replaced). *)
Lemma first_put_vis0 : forall ly nb sb, ly_NB ly = 0 -> ly_SB ly = 0 -> nb <> 0 -> sb <> 0 ->
  Forall (fun v => 0 < snd v) (ly_vis0 ly) ->
  Forall (fun v => Exists (fun z => shadow_addr (fst z) <= fst v /\ fst v + snd v <= shadow_addr (fst z + snd z - 1) + 1)
    (vis0_zones ly)) (ly_vis0 ly) ->
  Forall (fun v => Exists (fun z => shadow_addr (fst z) <= fst v /\ fst v + snd v <= shadow_addr (fst z + snd z - 1) + 1)
    (vis0_zones (set_ly_SB (set_ly_NB ly nb) sb))) (ly_vis0 (set_ly_SB (set_ly_NB ly nb) sb)).
Proof using.
  intros ly nb sb N0 S0 NZ SZ HV V.
  destruct (first_put_old ly N0 S0) as (_ & _ & EV). rewrite EV in V.
  rewrite (vis0_zones_set (set_ly_SB (set_ly_NB ly nb) sb) NZ SZ).
  rewrite Forall_forall in HV, V |- *. intros v Hv. specialize (HV v Hv). specialize (V v Hv).
  apply Exists_exists in V as (z & Hz & Hc). apply Exists_exists. exists z. split; [|exact Hc].
  apply in_app_or in Hz as [Hz|Hz].
  { apply in_or_app; left. destruct Hz as [<-|[<-|[]]]; cbn [In]; repeat (first [left; reflexivity | right]). }
  destruct Hz as [<-|[<-|Hz]]; [exfalso; exact (first_put_empty_zone v HV Hc) .. |].
  apply in_app_or in Hz as [Hz|Hz]; [|apply in_or_app; right; exact Hz].
  apply in_or_app; left.
  destruct Hz as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

(* ===== first_put_layout: the grown layout is a layout. From layout_ok at the empty
   depot and B2's placement facts (page_aligned / in_app / disjointness of (nb, NB), (sb, SB) in depot_first_put_post);
   img_cover only reads ly_img, which the growth keeps. D1W_ok's post gains `layout_ok ly' /\ img_cover ly'` from it.
   Proved on this kernel (owned_extents_set / static_extents_set / vis0_zones_set, YG0f.v:401 / :410 / :415; lo_vis0 = cover /\ positivity,
   YG0f.v:449-453). ===== *)
Lemma first_put_layout : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (tr : list Z) (ly' : alayout) (W' : world tfibsegs) (md' : Model)
    (c' : config),
  layout_ok ly -> img_cover ly ->
  put_effect ly W md ly' W' md' -> depot_first_put_post B W ly S regs mem md tr ly' W' md' c' ->
  layout_ok ly' /\ img_cover ly'.
Proof using.
  intros B W ly S regs mem md tr ly' W' md' c' HL HI HE HP.
  destruct HE as [(-> & _ & _) | (nb & sb & N0 & S0 & NZ & SZ & -> & _)]; [split; assumption|].
  destruct HP as (regs' & mem' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PNB & ANB & PSB & ASB & DNS & FNB & FSB & _).
  assert (N1 : ly_NB (set_ly_SB (set_ly_NB ly nb) sb) <> 0) by exact NZ.
  assert (S1 : ly_SB (set_ly_SB (set_ly_NB ly nb) sb) <> 0) by exact SZ.
  (* the placement against ext_but_NB ly (no SB entry: ly_SB ly = 0) and ly_extra ly *)
  unfold first_put_avoid, ext_but_NB in FNB, FSB. rewrite S0 in FNB, FSB.
  apply Forall_app in FNB as [FNB1 FNB]. apply Forall_app in FNB as [FNB2 _].
  apply Forall_app in FSB as [FSB1 FSB]. apply Forall_app in FSB as [FSB2 _].
  destruct (first_put_old ly N0 S0) as (EO & ES & _).
  pose proof (lo_app _ HL) as A. rewrite EO in A.
  pose proof (lo_disj _ HL) as D. rewrite ES in D.
  destruct (lo_extra _ HL) as (X1 & X2 & X3). rewrite ES in X3.
  split; [|exact HI].
  constructor.
  - exact (lo_prim_al _ HL).
  - exact (lo_space_al _ HL).
  - exact (lo_space_in _ HL).
  - exact (lo_Q_al _ HL).
  - exact (lo_T_al _ HL).
  - exact (lo_F_al _ HL).
  - exact PNB.
  - exact PSB.
  - exact (lo_C_al _ HL).
  - exact (lo_tsd_al _ HL).
  - exact (lo_high _ HL).
  - rewrite (owned_extents_set _ N1 S1).
    pose proof (first_put_forall_swap2 _ _ _ _ _ (ly_NB (set_ly_SB (set_ly_NB ly nb) sb), kNodesBlockSize)
      (ly_SB (set_ly_SB (set_ly_NB ly nb) sb), kStoreBlockSize) A ANB ASB) as A'.
    exact A'.
  - exact (lo_img _ HL).
  - rewrite (static_extents_set _ N1 S1).
    pose proof (first_put_pairwise_core _ YG0s.zdisjoint_sym _ _ _ _ (ly_NB (set_ly_SB (set_ly_NB ly nb) sb), kNodesBlockSize)
      (ly_SB (set_ly_SB (set_ly_NB ly nb) sb), kStoreBlockSize) D FNB1 FSB1 DNS) as D'.
    exact D'.
  - exact (lo_top _ HL).
  - exact (lo_tr0 _ HL).
  - split; [exact X1|]. split; [exact X2|]. rewrite (static_extents_set _ N1 S1).
    pose proof (first_put_pairwise_swap2 _ YG0s.zdisjoint_sym (ly_extra ly) _ _ _ _
      (ly_NB (set_ly_SB (set_ly_NB ly nb) sb), kNodesBlockSize) (ly_SB (set_ly_SB (set_ly_NB ly nb) sb), kStoreBlockSize)
      X3 FNB2 FSB2 FNB1 FSB1 DNS) as X'.
    exact X'.
  - exact (lo_D_al _ HL).
  - exact (lo_ctx _ HL).
  - split.
    + exact (first_put_vis0 ly nb sb N0 S0 NZ SZ (first_put_vis0_pos ly HL) (lo_vis0_cover _ HL)).
    + exact (first_put_vis0_pos ly HL).
  - exact (lo_stk_ceil _ HL).
Qed.

(* ===== first_put_maps_fresh: after the first Put, every extent the Put had to avoid
   misses both new blocks, at their nb_ext / sb_ext form. Only depot_first_put_post is needed: its placement clauses
   (Forall (zdisjoint (ly_NB ly', NB)) (first_put_avoid ly S), same for SB) plus ly_NB ly' <> 0 /\ ly_SB ly' <> 0
   (depot_first_put_facts; then nb_ext ly' = (ly_NB ly', NB), KnBlockExt.nb_ext_set). Every map of md (the core's
   al_cover zone (ly_C ly, kCtxMapSize) is wider than first_put_avoid's (ly_C ly, 256)): first_put_vm_maps_fresh below
   (amendment 11). ===== *)
Lemma first_put_maps_fresh : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (tr : list Z) (ly' : alayout) (W' : world tfibsegs) (md' : Model)
    (c' : config) (e : Z * Z),
  depot_first_put_post B W ly S regs mem md tr ly' W' md' c' ->
  In e (first_put_avoid ly S) ->
  zdisjoint e (nb_ext ly') /\ zdisjoint e (sb_ext ly').
Proof using.
  intros B W ly S regs mem md tr ly' W' md' c' e HP He.
  destruct HP as (regs' & mem' & _ & _ & _ & _ & _ & _ & _ & (HN & HS & _) & _ & _ & _ & _ & _ & _ & _ & FNB & FSB & _).
  rewrite (nb_ext_set ly' HN), (sb_ext_set ly' HS).
  split; apply YG0s.zdisjoint_sym;
    [exact (proj1 (Forall_forall _ _) FNB e He) | exact (proj1 (Forall_forall _ _) FSB e He)].
Qed.

(* ===== first_put_vm_maps_fresh (amendment 11): every map of the Put's entry model md misses both new
   blocks, at their nb_ext / sb_ext form. From depot_first_put_post's freshness clauses (Forall over vm_maps (m_vmmaps md),
   from S7's and S1's posts) plus ly_NB ly' <> 0 /\ ly_SB ly' <> 0 (depot_first_put_facts; KnBlockExt.nb_ext_set /
   sb_ext_set). ===== *)
Lemma first_put_vm_maps_fresh : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (tr : list Z) (ly' : alayout) (W' : world tfibsegs) (md' : Model)
    (c' : config) (q : word * word),
  depot_first_put_post B W ly S regs mem md tr ly' W' md' c' ->
  In q (vm_maps (m_vmmaps md)) ->
  zdisjoint (bv_unsigned (fst q), bv_unsigned (snd q)) (nb_ext ly') /\
  zdisjoint (bv_unsigned (fst q), bv_unsigned (snd q)) (sb_ext ly').
Proof using.
  intros B W ly S regs mem md tr ly' W' md' c' q HP Hq.
  destruct HP as (regs' & mem' & _ & _ & _ & _ & _ & _ & _ & (HN & HS & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & VNB & VSB).
  rewrite (nb_ext_set ly' HN), (sb_ext_set ly' HS).
  split; apply YG0s.zdisjoint_sym;
    [exact (proj1 (Forall_forall _ _) VNB q Hq) | exact (proj1 (Forall_forall _ _) VSB q Hq)].
Qed.

(* PLACEHOLDERS for the kernel's two knock facts am_depot_mono_d / am_alloc_depot_d (YG0n.v:263-266), each with the intro lemma the first Put
   needs (YG0n.v:283 / :290); kd_inst (:2582) instantiates them with those terms. Satisfiable: fun _ _ _ _ => True. *)
Variable am_depot_mono_kd : asyms -> alayout -> reader -> astate -> Prop.
Hypothesis am_depot_mono_kd_intro : forall B ly rd S, ly_NB ly <> 0 -> ly_SB ly <> 0 -> st_depot S <> [] ->
  am_depot_mono_kd B ly rd S.
Variable am_alloc_depot_kd : asyms -> alayout -> reader -> astate -> Prop.
Hypothesis am_alloc_depot_kd_intro : forall B ly rd S, st_depot S <> [] ->
  cell_holds B ly rd (z8 (AStore ss_alloc) kStoreBlockSize) -> am_alloc_depot_kd B ly rd S.

(* ===== AR_but_depot B ly' S W mem md (not in AF0w's final statement, but
   a premise of AR_but_depot_grow / first_malloc_AR_sec below, so its text is part of their consumers'
   statements). The core's AR (YG0n.v:795-796) at the GROWN layout ly' for the final state of the first malloc, minus
   exactly what the first Put changes (a Theorem Labs lane's condition (a)): the depot cells (in am_cells), the NB / SB entries
   of am_areas, am_depot, the two new maps in al_cover and al_perm, and am_layout (first_put_layout gives it). It is
   stated at ly' only (condition (b): ownership through owned_core / core_extents ly', whose NB / SB slots are the new
   blocks; no old-layout field is needed). al_eager_x is kept (condition (c); the finish lemma states it at the final
   model, the depot maps' eager use from AD3i's depot_nb_not_budget_refused :324 / depot_sb_not_budget_refused :342).
   The kernel's texts: al_eager_x is the knock field (+ nb_eager ly', YG0n.v:467 / :606-610); abudget_ok is the kernel's,
   with depot_abytes in abudget (YG0n.v:470 / :686-688; abudget_ok :693).
   Field split (AR field -> here or from the Put):
   ARm  am_wf, am_universe, am_syms, am_placed, am_const_owned, am_fa, am_flags, am_shadow, am_zshadow, am_junk,
        am_client, am_zero, am_tsd, am_static_img: HERE;  am_const: HERE as as_const_g2 (allocated_ from the Put);
        am_cells: HERE but depot_cells (from the Put);  am_areas: HERE but the NB / SB entries (from the Put);
        am_depot: from the Put;  am_layout: first_put_layout.
   ALedger  al_img, al_limit, al_reserved, al_prim, al_Q, al_hs, al_sec, al_eager_x, al_band, al_secx, al_top,
        al_imgcov, al_shna: HERE;  al_cover / al_perm: HERE but the two new maps (from the Put).
   abudget_ok, amwf, ahs: HERE.
   X, the maps al_cover / al_perm leave to the Put, lists a block only when the layout maps it (perm_live's pattern,
   YG0n.v:527-531): at ly' (both mapped) it is the two blocks; at a layout before the Put (both 0) it
   is empty, so AR_but_depot's al_cover / al_perm there are AR's own. ===== *)
Definition AR_but_depot (B : asyms) (ly' : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte)
  (md : Model) : Prop :=
  let rd := aview tfibsegs (w_H W) mem in
  let X := (if ly_NB ly' =? 0 then [] else [wiv (ly_NB ly', kNodesBlockSize)]) ++
           (if ly_SB ly' =? 0 then [] else [wiv (ly_SB ly', kStoreBlockSize)]) in
  (* ARm *)
  Wf (as_universe B) S /\ universe_ok (as_universe B) /\ asyms_ok B /\ sec_placed ly' S /\
  Forall (cell_holds B ly' rd) (as_const_g2 B ly') /\ Forall (cell_owned B ly') (as_const B ly') /\
  (forall c, In c (acells B ly' S) -> ~ In c (depot_cells ly' S) -> cell_holds B ly' rd c) /\
  fa_entries_ok ly' rd S /\ fs_flags_ok ly' rd S /\ shadow_ok B ly' rd S /\ zshadow_ok B ly' rd /\
  Forall (range_vis B ly' rd) (ajunk B ly' S) /\
  (forall r, In r (aareas S) -> fst r <> ANB 0 -> fst r <> ASB 0 -> range_vis B ly' rd r) /\
  Forall (range_vis B ly' rd) (aclient S) /\ Forall (range_zero B ly' rd) (ialloc_zero B) /\
  ly_tsd ly' = as_tsd B /\ Forall (fun r => zr_sub r (ly_img ly')) (as_owned_static B ++ as_zero_shadow B) /\
  (* ALedger *)
  (forall sg, In sg tfibsegs -> fst (ly_img ly') <= Z.of_N (seg_base sg) /\
     Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly') + snd (ly_img ly')) /\
  ASAN_VM_LMIN <= vm_limit (m_vmmaps md) /\ vm_reserved (m_vmmaps md) = segments_reserved tfibsegs /\
  (exists pieces, prim_pieces_ok ly' S pieces /\ (forall p, In p pieces <-> (In (wiv p) (vm_maps (m_vmmaps md)) /\
     0 < snd p /\ ly_prim ly' <= fst p /\ fst p + snd p <= ly_prim ly' + kPrimResvSize))) /\
  In (wiv (ly_Q ly', kPtrArrayResv)) (vm_maps (m_vmmaps md)) /\
  In (wiv (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg)) (vm_maps (m_vmmaps md)) /\
  (forall e, In e (sec_extents ly' S) -> In (wiv e) (vm_maps (m_vmmaps md))) /\
  (forall e, In e (vm_maps (m_vmmaps md)) -> ~ In e X ->
     Exists (fun z => fst z <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= fst z + snd z)
       (lazy_zones ly' ++ sec_extents ly' S)) /\
  eager_used md <= E_BASE + prim_committed S + 8 * st_sec_reserved S
    + esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly' S) + nb_eager ly' /\
  (forall z, In z (perm_live ly') -> ~ In (wiv z) X -> In (wiv z) (vm_maps (m_vmmaps md))) /\
  (forall z, In z band_maps -> In (wiv z) (vm_maps (m_vmmaps md))) /\
  (forall e z, In e (sec_extents ly' S) -> In z (perm_maps ly') -> zdisjoint e z) /\
  YM05.ceil_of_top (alloc_top (m_vmmaps md)) /\
  (forall a, in_zr a (ly_img ly') -> exists e, In e (segments_reserved tfibsegs) /\
     bv_unsigned (fst e) <= a < bv_unsigned (fst e) + bv_unsigned (snd e)) /\
  (region_free (vm_noaccess (m_vmmaps md)) (w64 kLowShadowBeg) (w64 (kLowShadowEnd - kLowShadowBeg)) = true /\
   region_free (vm_noaccess (m_vmmaps md)) (w64 kHighShadowBeg) (w64 (kHighShadowEnd - kHighShadowBeg)) = true) /\
  (* the rest of AR *)
  abudget_ok tfibsegs ly' S W /\ amwf md /\ ahs B ly' S (w_H W) mem.

(* depot_footprint (AFl0.v:63) lies in a Theorem Labs lane's DZONE_at (AFjm.v:562-563;
   body written inline below and in first_malloc_AR) once both blocks are mapped: the depot
   [0x182658, 0x5c2668) and the store head [0x172648, 0x172688) lie in [0x172648, 0x5c2dd0), the two blocks are
   nb_ext / sb_ext (KnBlockExt nb_ext_set / sb_ext_set). first_malloc_AR's proof uses it to read its DZONE_at frame on
   depot_first_put_post's depot_footprint frame. *)
Lemma depot_footprint_dzone : forall B ly a, WireSyms B -> ly_NB ly <> 0 -> ly_SB ly <> 0 ->
  depot_footprint B ly a ->
  (tfib_dzone_lo <= a < tfib_dzone_hi) \/ (fst (nb_ext ly) <= a < fst (nb_ext ly) + snd (nb_ext ly)) \/
  (fst (sb_ext ly) <= a < fst (sb_ext ly) + snd (sb_ext ly)).
Proof using.
  intros B ly a HB HN HS X. rewrite (nb_ext_set ly HN), (sb_ext_set ly HS). cbn [fst snd].
  unfold depot_footprint in X. rewrite (ts_depot B HB), (ts_store B HB) in X.
  unfold TFIB_DEPOT, TFIB_STORE, d_map1, tfib_dzone_lo, tfib_dzone_hi in *.
  destruct X as [X|[X|[X|X]]].
  - left. lia.
  - right. left. exact X.
  - right. right. exact X.
  - left. lia.
Qed.

(* ----- first_malloc_AR's helpers (one per AR field the first Put fills; each with only the hypotheses it reads). ----- *)

(* Decidable equality of the kernel's cells and of map entries: first_malloc_AR splits acells / aareas / as_const / the
   maps into "the Put's own entries" and "AR_but_depot's entries" by these. *)
Lemma kd_aexp_eq_dec : forall a b : aexp, {a = b} + {a <> b}.
Proof using. decide equality; first [apply Z.eq_dec | apply Nat.eq_dec]. Qed.
Lemma kd_acell_eq_dec : forall a b : acell, {a = b} + {a <> b}.
Proof using.
  decide equality; first [apply kd_aexp_eq_dec | apply Nat.eq_dec | decide equality; first [apply kd_aexp_eq_dec | apply Z.eq_dec]].
Qed.
Lemma kd_ww_eq_dec : forall a b : word * word, {a = b} + {a <> b}.
Proof using. decide equality; apply bv_eq_dec. Qed.

(* The frame of the steps after the Put (first_malloc_AR's premise, over a Theorem Labs lane's DZONE_at ly'): the final reader
   agrees with the Put's reader on the static depot / store zone and on both new blocks. The ONLY place that reads the
   frame premise's region (a restatement as KnBlockExt.DZONE_at is convertible with FR's type here). *)
Lemma kd_frame_agree : forall (ly' : alayout) (Hf Hc : word -> bool) (memf memc : word -> option byte),
  ly_NB ly' <> 0 -> ly_SB ly' <> 0 -> in_app (ly_NB ly') kNodesBlockSize -> in_app (ly_SB ly') kStoreBlockSize ->
  (forall a : word, ((tfib_dzone_lo <= bv_unsigned a < tfib_dzone_hi) \/
                     (fst (nb_ext ly') <= bv_unsigned a < fst (nb_ext ly') + snd (nb_ext ly')) \/
                     (fst (sb_ext ly') <= bv_unsigned a < fst (sb_ext ly') + snd (sb_ext ly'))) ->
     memf a = memc a /\ Hf a = Hc a) ->
  forall x, (tfib_dzone_lo <= x < tfib_dzone_hi) \/ (ly_NB ly' <= x < ly_NB ly' + kNodesBlockSize) \/
            (ly_SB ly' <= x < ly_SB ly' + kStoreBlockSize) ->
  aview tfibsegs Hf memf x = aview tfibsegs Hc memc x.
Proof using.
  intros ly' Hf Hc memf memc HN HS IN IS FR x Hx.
  assert (Rx : 0 <= x < 2 ^ 64).
  { clear FR. pose proof ASAN_CEIL_range as [CR _].
    unfold in_app, kLowShadowBeg, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, tfib_dzone_lo, tfib_dzone_hi in *.
    destruct Hx as [Hx|[Hx|Hx]]; [lia | destruct IN as [IN1 [IN2|[IN2 IN3]]]; lia | destruct IS as [IS1 [IS2|[IS2 IS3]]]; lia]. }
  assert (Ex : bv_unsigned (Z_to_bv 64 x) = x) by (rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia); reflexivity).
  destruct (FR (Z_to_bv 64 x) ltac:(rewrite Ex, (nb_ext_set ly' HN), (sb_ext_set ly' HS); cbn [fst snd]; exact Hx))
    as [E1 E2].
  unfold aview, mbyte, mrestrict. rewrite E1, E2. reflexivity.
Qed.

(* The Put's facts (depot_first_put_facts) move from the Put's reader to any reader that agrees with it on the static zone and the two
   blocks: every byte they read (depot cells, hash words, node 1, the junk and NB / SB areas) lies there. *)
Lemma kd_facts_xfer : forall B ly' S' tr (rd rd2 : reader), WireSyms B -> st_depot S' = [tr] ->
  (forall x, (tfib_dzone_lo <= x < tfib_dzone_hi) \/ (ly_NB ly' <= x < ly_NB ly' + kNodesBlockSize) \/
             (ly_SB ly' <= x < ly_SB ly' + kStoreBlockSize) -> rd2 x = rd x) ->
  depot_first_put_facts B ly' S' tr rd -> depot_first_put_facts B ly' S' tr rd2.
Proof using.
  intros B ly' S' tr rd rd2 HB ES AG (HN & HS & DC & HT & N1 & L1 & AV).
  pose proof (ts_depot B HB) as ED. pose proof (ts_store B HB) as EST.
  split; [exact HN|]. split; [exact HS|]. split; [|split; [|split; [|split]]].
  - apply Forall_forall. intros c Hc. apply (cell_agree B ly' rd); [|exact (proj1 (Forall_forall _ _) DC c Hc)].
    intros k Hk. apply AG. left. unfold depot_cells_kd in Hc. rewrite ES in Hc. cbn [In] in Hc.
    destruct Hc as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [c_at c_w aeval z4 z8 c4 c8] in Hk |- *; rewrite ?ED, ?EST;
      unfold TFIB_DEPOT, TFIB_STORE, d_nuniq, d_map1, s_total, s_block0, s_alloc, tfib_dzone_lo, tfib_dzone_hi in *; lia.
  - intros b Hb k Hk. rewrite AG; [exact (HT b Hb k Hk)|]. left. rewrite ED.
    unfold TFIB_DEPOT, d_tab_words, tfib_dzone_lo, tfib_dzone_hi in *. lia.
  - intros k Hk. rewrite AG; [exact (N1 k Hk)|]. right. left. unfold kNodesBlockSize. lia.
  - intros k Hk. rewrite AG; [exact (L1 k Hk)|]. right. left. unfold kNodesBlockSize. lia.
  - apply Forall_forall. intros r Hr i Hi. rewrite AG; [exact (proj1 (Forall_forall _ _) AV r Hr i Hi)|].
    unfold depot_junk_kd, aareas_depot_kd in Hr. rewrite ES in Hr. cbn [In app] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd aeval] in Hi |- *; rewrite ?ED, ?EST;
      unfold TFIB_DEPOT, TFIB_STORE, d_nuniq, kNodesBlockSize, kStoreBlockSize, tfib_dzone_lo, tfib_dzone_hi in *;
      [left; lia | left; lia | left; lia | right; left; lia | right; right; lia].
Qed.

(* am_depot: knock's post-Put depot_ok (YG0n.v:213-221) from the Put's hash words and node 1, at the depot after the
   first Put (one trace): heads := 1 at the trace's bucket, 0 elsewhere; links := 0 (as depot_ok_first_put below). *)
Lemma kd_depot_ok : forall B ly' Sf tr (rd : reader), st_depot Sf = [tr] -> ly_NB ly' <> 0 -> ly_SB ly' <> 0 ->
  (forall b, 0 <= b < d_tab_words ->
     rd32 rd (as_depot B + 4 * b) (if b =? (as_dhash B tr mod 2 ^ 64) mod d_tab_words then 1 else 0)) ->
  rd64 rd (ly_NB ly' + 16) (as_dhash B tr mod 2 ^ 64) -> rd32 rd (ly_NB ly' + 24) 0 ->
  depot_ok B ly' rd Sf.
Proof using.
  intros B ly' Sf tr rd E HN HSb HT N1 L1.
  unfold depot_ok, depot_ids, depot_traces. rewrite E. cbn beta iota zeta.
  split; [exact HN|]. split; [exact HSb|].
  exists (fun b => if b =? (as_dhash B tr mod 2 ^ 64) mod d_tab_words then 1 else 0), (fun _ => 0).
  cbv beta zeta. split; [| split].
  - intros b Hb. split; [destruct (b =? _); cbn; lia | exact (HT b Hb)].
  - intros id Hid. assert (Eid : id = 1) by (cbn in Hid; lia). subst id.
    split; [lia|]. split.
    + replace (ly_NB ly' + 16 * 1) with (ly_NB ly' + 16) by lia. exact N1.
    + replace (ly_NB ly' + 16 * 1 + 8) with (ly_NB ly' + 24) by lia. exact L1.
  - intros id Hid. assert (Eid : id = 1) by (cbn in Hid; lia). subst id.
    cbn. rewrite Z.eqb_refl. cbn. split; [discriminate | left; reflexivity].
Qed.

(* am_cells: the depot cells of Sf are the Put's (st_depot Sf = st_depot S'), every other cell is AR_but_depot's. *)
Lemma kd_cells : forall B ly' Sf S' (rd : reader), st_depot Sf = st_depot S' ->
  Forall (cell_holds B ly' rd) (depot_cells_kd S') ->
  (forall c, In c (acells B ly' Sf) -> ~ In c (depot_cells ly' Sf) -> cell_holds B ly' rd c) ->
  Forall (cell_holds B ly' rd) (acells B ly' Sf).
Proof using.
  intros B ly' Sf S' rd E DC HC.
  assert (ED : depot_cells ly' Sf = depot_cells_kd S')
    by (unfold depot_cells, depot_cells_kd, depot_ids, depot_frames; rewrite E; reflexivity).
  apply Forall_forall. intros c Hc. destruct (in_dec kd_acell_eq_dec c (depot_cells ly' Sf)) as [I|N].
  - rewrite ED in I. exact (proj1 (Forall_forall _ _) DC c I).
  - exact (HC c Hc N).
Qed.

(* am_areas: after the first Put, the only aareas entries at ANB 0 / ASB 0 are the two whole blocks (aareas_post, YG0n.v:327). *)
Lemma kd_aareas_cases : forall S r, st_depot S <> [] -> In r (aareas S) ->
  (fst r <> ANB 0 /\ fst r <> ASB 0) \/ r = (ANB 0, kNodesBlockSize) \/ r = (ASB 0, kStoreBlockSize).
Proof using.
  intros S r NE Hr. rewrite aareas_post in Hr by exact NE.
  apply in_app_iff in Hr as [Hr|Hr].
  { left. apply in_flat_map in Hr as (c & _ & Hr). cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst]; split; discriminate. }
  apply in_app_iff in Hr as [Hr|Hr].
  { left. cbn [In] in Hr. destruct Hr as [<-|[]]; cbn [fst]; split; discriminate. }
  apply in_app_iff in Hr as [Hr|Hr].
  { left. apply in_flat_map in Hr as (k & _ & Hr). cbv beta in Hr. revert Hr.
    destruct (ck_beg k); cbn [In]; intros Hr; try contradiction.
    destruct Hr as [<-|[]]; cbn [fst]; split; discriminate. }
  cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  all: first [right; left; reflexivity | right; right; reflexivity | left; cbn [fst]; split; discriminate].
Qed.
Lemma kd_areas : forall B ly' Sf (rd : reader), st_depot Sf <> [] ->
  range_vis B ly' rd (ANB 0, kNodesBlockSize) -> range_vis B ly' rd (ASB 0, kStoreBlockSize) ->
  (forall r, In r (aareas Sf) -> fst r <> ANB 0 -> fst r <> ASB 0 -> range_vis B ly' rd r) ->
  Forall (range_vis B ly' rd) (aareas Sf).
Proof using.
  intros B ly' Sf rd NE VN VS HA. apply Forall_forall. intros r Hr.
  destruct (kd_aareas_cases Sf r NE Hr) as [[E1 E2]|[->| ->]]; [exact (HA r Hr E1 E2) | exact VN | exact VS].
Qed.

(* am_const, the allocated_ row (AF0m.v:129, ACell (ANum 0x172650) 0 (AV (ANum 0)), = as_store B + ss_alloc), after the
   first Put, which makes that word kStoreBlockSize (S3's post, AD3c.v:220). The step holds: the kernel's depot_cells carries
   allocated_ (YG0n.v:118 / :120, s_alloc 0 / kStoreBlockSize), and the as_const row is
   zero-width (c_w = 0), so cell_holds asks nothing of its bytes; the proof reads that width off Tfib_const by
   vm_compute (the forallb below). *)
Lemma kd_alloc_row_rev6 : forall B ly (rd : reader) c, WireSyms B -> In c (as_const B ly) ->
  c_at c = ANum (as_store B + ss_alloc) -> cell_holds B ly rd (z8 (AStore ss_alloc) kStoreBlockSize) ->
  cell_holds B ly rd c.
Proof using.
  intros B ly rd [a w v] HB Hc E _. cbn [c_at] in E. rewrite (ts_store B HB) in E. subst a.
  rewrite (ts_const B HB ly) in Hc.
  assert (K : forallb (fun c0 => match c_at c0, c_val c0 with
    | ANum z, AV _ => negb (z =? TFIB_STORE + ss_alloc) || Nat.eqb (c_w c0) 0
    | ANum z, AVmask _ _ => negb (z =? TFIB_STORE + ss_alloc)
    | _, _ => true end) (Tfib_const ly) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) K _ Hc) as Kc. cbn [c_at c_val c_w] in Kc.
  rewrite Z.eqb_refl in Kc. destruct v as [e|mk vv]; cbn [negb orb] in Kc; [|discriminate Kc].
  apply Nat.eqb_eq in Kc. subst w. unfold cell_holds. cbn [c_val c_w]. intros k Hk. lia.
Qed.
Lemma kd_const : forall B ly (rd : reader), WireSyms B ->
  Forall (cell_holds B ly rd) (as_const_g2 B ly) -> cell_holds B ly rd (z8 (AStore ss_alloc) kStoreBlockSize) ->
  Forall (cell_holds B ly rd) (as_const B ly).
Proof using as_const_g2_def.
  intros B ly rd HB G2 AL. apply Forall_forall. intros c Hc.
  destruct (kd_aexp_eq_dec (c_at c) (ANum (as_store B + ss_alloc))) as [E|E].
  - exact (kd_alloc_row_rev6 B ly rd c HB Hc E AL).
  - apply (proj1 (Forall_forall _ _) G2). apply as_const_g2_def. split; assumption.
Qed.

(* al_cover: the two new maps lie in lazy_zones ly' (NB through static_extents ly', SB through its own slot). *)
Lemma kd_cover : forall ly' Sf (md : Model),
  ly_NB ly' <> 0 -> ly_SB ly' <> 0 -> in_app (ly_NB ly') kNodesBlockSize -> in_app (ly_SB ly') kStoreBlockSize ->
  (forall e, In e (vm_maps (m_vmmaps md)) -> ~ In e [wiv (ly_NB ly', kNodesBlockSize); wiv (ly_SB ly', kStoreBlockSize)] ->
     Exists (fun z => fst z <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= fst z + snd z)
       (lazy_zones ly' ++ sec_extents ly' Sf)) ->
  forall e, In e (vm_maps (m_vmmaps md)) ->
    Exists (fun z => fst z <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= fst z + snd z)
      (lazy_zones ly' ++ sec_extents ly' Sf).
Proof using.
  intros ly' Sf md HN HS IN IS HC e He.
  destruct (in_dec kd_ww_eq_dec e [wiv (ly_NB ly', kNodesBlockSize); wiv (ly_SB ly', kStoreBlockSize)]) as [I|N];
    [|exact (HC e He N)].
  clear HC He. pose proof ASAN_CEIL_range as [CR _].
  assert (BN : 0 <= ly_NB ly' /\ ly_NB ly' + kNodesBlockSize < 2 ^ 64).
  { unfold in_app, kLowShadowBeg, kHighMemBeg, kNodesBlockSize in *. destruct IN as [IN1 [IN2|[IN2 IN3]]]; lia. }
  assert (BS : 0 <= ly_SB ly' /\ ly_SB ly' + kStoreBlockSize < 2 ^ 64).
  { unfold in_app, kLowShadowBeg, kHighMemBeg, kStoreBlockSize in *. destruct IS as [IS1 [IS2|[IS2 IS3]]]; lia. }
  apply Exists_exists. rewrite lazy_zones_set by assumption.
  destruct I as [<-|[<-|[]]].
  - exists (ly_NB ly', kNodesBlockSize). split.
    + apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. rewrite static_extents_set by assumption.
      cbn [In]. do 4 right. left. reflexivity.
    + unfold wiv, w64. cbn [fst snd].
      rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus, kNodesBlockSize in *; lia). lia.
  - exists (ly_SB ly', kStoreBlockSize). split.
    + apply in_or_app. left. apply in_or_app. left. cbn [In]. do 3 right. left. reflexivity.
    + unfold wiv, w64. cbn [fst snd].
      rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus, kStoreBlockSize in *; lia). lia.
Qed.

(* al_perm: the two new maps are mapped in the final model (given), every other live permanent map from AR_but_depot. *)
Lemma kd_perm : forall ly' (md : Model),
  In (wiv (ly_NB ly', kNodesBlockSize)) (vm_maps (m_vmmaps md)) ->
  In (wiv (ly_SB ly', kStoreBlockSize)) (vm_maps (m_vmmaps md)) ->
  (forall z, In z (perm_live ly') -> ~ In (wiv z) [wiv (ly_NB ly', kNodesBlockSize); wiv (ly_SB ly', kStoreBlockSize)] ->
     In (wiv z) (vm_maps (m_vmmaps md))) ->
  forall z, In z (perm_live ly') -> In (wiv z) (vm_maps (m_vmmaps md)).
Proof using.
  intros ly' md M1 M2 HP z Hz.
  destruct (in_dec kd_ww_eq_dec (wiv z) [wiv (ly_NB ly', kNodesBlockSize); wiv (ly_SB ly', kStoreBlockSize)])
    as [[E|[E|[]]]|N].
  - rewrite <- E. exact M1.
  - rewrite <- E. exact M2.
  - exact (HP z Hz N).
Qed.

(* The two maps of the first Put: put_effect's right arm (b2_mmap_vm); its left arm (ly' = ly) is void, ly_NB ly = 0
   against the post's ly_NB ly' <> 0. *)
Lemma kd_put_maps : forall ly W md ly' W' md', ly_NB ly = 0 -> ly_NB ly' <> 0 -> put_effect ly W md ly' W' md' ->
  In (wiv (ly_NB ly', kNodesBlockSize)) (vm_maps (m_vmmaps md')) /\
  In (wiv (ly_SB ly', kStoreBlockSize)) (vm_maps (m_vmmaps md')).
Proof using.
  intros ly W md ly' W' md' H0 HN [(E & _ & _) | (nb & sb & _ & _ & _ & _ & EL & _ & _ & _ & _ & VM & _)].
  - exfalso. apply HN. rewrite E. exact H0.
  - pose proof (b2_mmap_vm (Z_to_bv 64 sb) (Z_to_bv 64 kStoreBlockSize)
                  (mmap_model (Z_to_bv 64 nb) (Z_to_bv 64 kNodesBlockSize) md)) as (_ & _ & _ & E1 & _).
    pose proof (b2_mmap_vm (Z_to_bv 64 nb) (Z_to_bv 64 kNodesBlockSize) md) as (_ & _ & _ & E2 & _).
    assert (ENB : ly_NB ly' = nb) by (rewrite EL; reflexivity). assert (ESB : ly_SB ly' = sb) by (rewrite EL; reflexivity).
    rewrite VM, E1, E2, ENB, ESB. unfold wiv, w64. cbn [fst snd In].
    split; [right; left; reflexivity | left; reflexivity].
Qed.

(* ===== first_malloc_AR: the core's AR at the grown layout for the FINAL state of the first
   malloc (and the kernel's two knock facts am_depot_mono_d / am_alloc_depot_d), from (i) AR_but_depot at that state (malloc's finish lemma proves it)
   and (ii) the first Put's own post (put_effect's right arm and depot_first_put_post, D1W_ok's last conjunct), with
   the frame of the steps after the Put over DZONE_at ly' (body inline, convertible with
   KnBlockExt.DZONE_at tfib_dzone_lo tfib_dzone_hi ly': the static depot / store zone and the two new blocks) neither written nor hidden again, the
   depot unchanged, the two maps kept. Qed from the kd_* helpers above, kd_alloc_row_rev6 (:1267) among them. ===== *)
Lemma first_malloc_AR : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (tr : list Z) (ly' : alayout) (W' : world tfibsegs) (md' : Model)
    (c' : config) (Sf : astate) (Wf : world tfibsegs) (memf : word -> option byte) (mdf : Model),
  WireSyms B -> st_depot S = [] -> ly_NB ly = 0 -> layout_ok ly -> img_cover ly ->
  put_effect ly W md ly' W' md' -> depot_first_put_post B W ly S regs mem md tr ly' W' md' c' ->
  AR_but_depot B ly' Sf Wf memf mdf ->
  st_depot Sf = st_depot (depot_after 1 tr S) ->
  (forall a : word, ((tfib_dzone_lo <= bv_unsigned a < tfib_dzone_hi) \/
                     (fst (nb_ext ly') <= bv_unsigned a < fst (nb_ext ly') + snd (nb_ext ly')) \/
                     (fst (sb_ext ly') <= bv_unsigned a < fst (sb_ext ly') + snd (sb_ext ly'))) ->
     memf a = ms_mem (cfg_ms c') a /\ w_H Wf a = w_H W' a) ->
  (forall e, In e (vm_maps (m_vmmaps md')) -> In e (vm_maps (m_vmmaps mdf))) ->
  (forall e, In e (m_vm_lazy md') -> In e (m_vm_lazy mdf)) ->
  AR tfibsegs B ly' Sf Wf memf mdf /\
  am_depot_mono_kd B ly' (aview tfibsegs (w_H Wf) memf) Sf /\ am_alloc_depot_kd B ly' (aview tfibsegs (w_H Wf) memf) Sf.
Proof using kd_grow_NB kd_grow_SB kd_grow_trans depot_ok_pre_kd depot_ok_post_kd as_const_g2_def
  am_depot_mono_kd_intro am_alloc_depot_kd_intro.
  intros B W ly S regs mem md tr ly' W' md' c' Sf Wf memf mdf HB ES HNB0 LY IMG PE POST ABD ESf FR MM _.
  pose proof (first_put_layout B W ly S regs mem md tr ly' W' md' c' LY IMG PE POST) as [LY' _].
  unfold depot_first_put_post in POST. cbv zeta in POST.
  destruct POST as (regs' & mem' & Ec' & _ & _ & _ & _ & _ & _ & FACTS & ALLOC & _ & _ & IA1 & _ & IA2 & _).
  assert (ES' : st_depot (depot_after 1 tr S) = [tr]) by (unfold depot_after; simpl; rewrite ES; reflexivity).
  assert (ESf' : st_depot Sf = [tr]) by (rewrite ESf; exact ES').
  assert (NE : st_depot Sf <> []) by (rewrite ESf'; discriminate).
  pose proof FACTS as (HN & HS & _).
  assert (EM : ms_mem (cfg_ms c') = mem') by (rewrite Ec'; reflexivity). rewrite EM in FR.
  pose proof (kd_frame_agree ly' (w_H Wf) (w_H W') memf mem' HN HS IA1 IA2 FR) as AG. clear FR.
  pose proof (kd_facts_xfer B ly' (depot_after 1 tr S) tr _ _ HB ES' AG FACTS) as FACTSf.
  assert (ALLOCf : cell_holds B ly' (aview tfibsegs (w_H Wf) memf) (z8 (AStore ss_alloc) kStoreBlockSize)).
  { apply (cell_agree B ly' (aview tfibsegs (w_H W') mem')); [|exact ALLOC]. intros k Hk. apply AG. left.
    cbn [c_at c_w aeval z8 c8] in Hk |- *. rewrite (ts_store B HB).
    unfold TFIB_STORE, ss_alloc, tfib_dzone_lo, tfib_dzone_hi. cbn in Hk. lia. }
  clear FACTS ALLOC AG.
  destruct FACTSf as (_ & _ & DCf & HTf & N1f & L1f & AVf).
  assert (VN : range_vis B ly' (aview tfibsegs (w_H Wf) memf) (ANB 0, kNodesBlockSize)).
  { apply (proj1 (Forall_forall _ _) AVf). unfold depot_junk_kd, aareas_depot_kd. rewrite ES'. cbn [In app].
    do 3 right. left. reflexivity. }
  assert (VS : range_vis B ly' (aview tfibsegs (w_H Wf) memf) (ASB 0, kStoreBlockSize)).
  { apply (proj1 (Forall_forall _ _) AVf). unfold depot_junk_kd, aareas_depot_kd. rewrite ES'. cbn [In app].
    do 4 right. left. reflexivity. }
  destruct (kd_put_maps ly W md ly' W' md' HNB0 HN PE) as [M1 M2]. apply MM in M1, M2.
  assert (EX : (if ly_NB ly' =? 0 then [] else [wiv (ly_NB ly', kNodesBlockSize)]) ++
               (if ly_SB ly' =? 0 then [] else [wiv (ly_SB ly', kStoreBlockSize)]) =
               [wiv (ly_NB ly', kNodesBlockSize); wiv (ly_SB ly', kStoreBlockSize)])
    by (rewrite (proj2 (Z.eqb_neq _ 0) HN), (proj2 (Z.eqb_neq _ 0) HS); reflexivity).
  unfold AR_but_depot in ABD. cbv zeta in ABD. rewrite EX in ABD.
  destruct ABD as (WF & UN & SY & PL & CG2 & CO & CE & FA & FL & SH & ZS & JK & AA & CL & ZR & TSD & SI &
                   AIMG & ALIM & ARES & APRIM & AQ & AHS & ASEC & ACOV & AEX & APERM & ABAND & ASECX & ATOP & AIMGCOV &
                   ASHNA & ABUD & AMWF & AHSS).
  split; [|split].
  - unfold AR. split; [|split; [|split; [|split]]].
    + constructor.
      * exact WF.
      * exact UN.
      * exact SY.
      * exact LY'.
      * exact PL.
      * exact (kd_const B ly' _ HB CG2 ALLOCf).
      * exact CO.
      * exact (kd_cells B ly' Sf (depot_after 1 tr S) _ ESf DCf CE).
      * exact FA.
      * exact FL.
      * exact (kd_depot_ok B ly' Sf tr _ ESf' HN HS HTf N1f L1f).
      * exact SH.
      * exact ZS.
      * exact JK.
      * exact (kd_areas B ly' Sf _ NE VN VS AA).
      * exact CL.
      * exact ZR.
      * exact TSD.
      * exact SI.
    + constructor.
      * exact AIMG.
      * exact ALIM.
      * exact ARES.
      * exact APRIM.
      * exact AQ.
      * exact AHS.
      * exact ASEC.
      * exact (kd_cover ly' Sf mdf HN HS IA1 IA2 ACOV).
      * exact AEX.
      * exact (kd_perm ly' mdf M1 M2 APERM).
      * exact ABAND.
      * exact ASECX.
      * exact ATOP.
      * exact AIMGCOV.
      * exact ASHNA.
    + exact ABUD.
    + exact AMWF.
    + exact AHSS.
  - exact (am_depot_mono_kd_intro B ly' _ Sf HN HS NE).
  - exact (am_alloc_depot_kd_intro B ly' _ Sf NE ALLOCf).
Qed.

(* ===== The first-Put arm of a malloc whose walk states the final state's AR fields at its OWN layout, world and model
   (AR_but_depot_grow and first_malloc_AR_sec below).
   ly_core ly: ly with every secondary slot erased. ly_core l1 = ly_core l2 says that l1 and l2 differ at most in
   ly_sec; ly_core (set_ly_sec ly r mb) = ly_core ly holds by computation (eq_refl). ===== *)
Definition ly_core (ly : alayout) : alayout :=
  ALayout (ly_prim ly) (ly_space ly) (ly_Q ly) (ly_T ly) (ly_C ly) (ly_F ly) (ly_NB ly) (ly_SB ly) (ly_top ly)
    (ly_stk_lo ly) (ly_stk_hi ly) (ly_tsd ly) (ly_tr0 ly) (ly_extra ly) (ly_D ly) (ly_vis0 ly) (ly_img ly) (fun _ => 0).

(* Layout facts across ly_core: an address expression without ASec evaluates alike at ly and ly_core ly, and
   layout_ok reads no secondary slot. *)
Fixpoint nosec (e : aexp) : bool := match e with ASec _ _ => false | ASh e' => nosec e' | _ => true end.
Lemma aeval_ly_core : forall B ly e, nosec e = true -> aeval B (ly_core ly) e = aeval B ly e.
Proof using. intros B ly e. induction e; cbn; intros Hn; try reflexivity; try discriminate Hn. rewrite (IHe Hn). reflexivity. Qed.
Definition cell_nosec (c : acell) : bool :=
  nosec (c_at c) && match c_val c with AV e => nosec e | AVmask _ _ => true end.
Lemma cell_holds_ly_core : forall B l1 l2 rd c, ly_core l1 = ly_core l2 -> cell_nosec c = true ->
  cell_holds B l1 rd c -> cell_holds B l2 rd c.
Proof using.
  intros B l1 l2 rd c E N H. unfold cell_nosec in N. apply andb_prop in N as [N1 N2].
  assert (A : forall e, nosec e = true -> aeval B l2 e = aeval B l1 e).
  { intros e He. rewrite <- (aeval_ly_core B l1 e He), <- (aeval_ly_core B l2 e He), E. reflexivity. }
  unfold cell_holds in *. cbv zeta in *. rewrite (A _ N1).
  destruct (c_val c) as [e|mk v]; [|exact H]. rewrite (A _ N2). exact H.
Qed.
Lemma Forall_cell_holds_ly_core : forall B l1 l2 rd L, ly_core l1 = ly_core l2 -> forallb cell_nosec L = true ->
  Forall (cell_holds B l1 rd) L -> Forall (cell_holds B l2 rd) L.
Proof using.
  intros B l1 l2 rd L E N H. apply Forall_forall. intros c Hc.
  exact (cell_holds_ly_core B l1 l2 rd c E (proj1 (forallb_forall _ _) N c Hc) (proj1 (Forall_forall _ _) H c Hc)).
Qed.
Lemma ly_core_layout_ok : forall l1 l2, ly_core l1 = ly_core l2 -> layout_ok l2 -> layout_ok l1.
Proof using.
  intros l1 l2 E LO.
  assert (LO' : layout_ok (ly_core l2)) by (destruct LO; constructor; cbn; assumption).
  rewrite <- E in LO'. destruct LO'; constructor; cbn in *; assumption.
Qed.

(* The first Put's layout equation, AR_but_depot_grow's lyF premise at lyW := ly, lyF := ly' (put_effect's right arm;
   its left arm contradicts ly_NB ly = 0 and the post's ly_NB ly' <> 0). *)
Lemma put_effect_first_ly : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (tr : list Z) (ly' : alayout) (W' : world tfibsegs) (md' : Model)
    (c' : config),
  ly_NB ly = 0 -> put_effect ly W md ly' W' md' -> depot_first_put_post B W ly S regs mem md tr ly' W' md' c' ->
  ly' = set_ly_SB (set_ly_NB ly (ly_NB ly')) (ly_SB ly').
Proof using.
  intros B W ly S regs mem md tr ly' W' md' c' H0 PE POST.
  unfold depot_first_put_post in POST. cbv zeta in POST.
  destruct POST as (regs' & mem' & _ & _ & _ & _ & _ & _ & _ & FACTS & _).
  pose proof FACTS as (HN & _).
  destruct PE as [(E & _ & _) | (nb & sb & _ & _ & _ & _ & EL & _)].
  - exfalso. apply HN. rewrite E. exact H0.
  - subst ly'. reflexivity.
Qed.

(* ===== AR_but_depot_grow's helpers: what the first Put's growth (set_ly_SB (set_ly_NB l nb) sb from l with both slots
   0) keeps. ===== *)
Definition cell_nb (c : acell) : bool :=
  nonbsb (c_at c) && match c_val c with AV e => nonbsb e | AVmask _ _ => true end.
Lemma nonbsb_aoff : forall e d, nonbsb (aoff e d) = nonbsb e.
Proof using. intros e d. destruct e; reflexivity. Qed.
Lemma nonbsb_sptr : forall p, nonbsb (sptr_exp p) = true.
Proof using. intros p. destruct p; reflexivity. Qed.
Local Ltac cnb := unfold cell_nb; cbn [c_at c_val z1 z2 z4 z8 c1 c2 c4 c8];
  repeat rewrite nonbsb_aoff; repeat rewrite nonbsb_sptr; reflexivity.
Local Ltac in_cases tac := cbn [In] in *; repeat (match goal with H : _ = _ \/ _ |- _ => destruct H as [<-|H] end; [tac|]);
  try match goal with H : False |- _ => destruct H end; try match goal with H : _ = ?z |- _ => is_var z; subst z; tac end.
Local Ltac leaves := repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
  try match goal with H : False |- _ => destruct H end;
  try match goal with H : _ = ?z |- _ => is_var z; subst z end.
Local Ltac osearch := first [reflexivity | assumption | match goal with H : _ |- _ => exact H end | left; osearch | right; osearch].

(* No acells cell but the depot cells names ANB / ASB, at its address or in its value. *)
Lemma region_cells_nb : forall S x c, In c (region_cells S x) -> cell_nb c = true.
Proof using. intros S x c Hc. unfold region_cells in Hc. cbv zeta in Hc. in_cases ltac:(cnb). Qed.
Lemma cache_cells_nb : forall S x c, In c (cache_cells S x) -> cell_nb c = true.
Proof using.
  intros S x c Hc. unfold cache_cells in Hc. cbv zeta in Hc. revert Hc. destruct (st_cache_inited S); intros Hc.
  - destruct Hc as [<-|[<-|[<-|Hc]]]; [cnb..|]. apply in_map_iff in Hc as (iv & <- & _). cnb.
  - in_cases ltac:(cnb).
Qed.
Lemma chunk_cells_nb : forall k c, In c (chunk_cells k) -> cell_nb c = true.
Proof using.
  intros k c Hc. unfold chunk_cells in Hc. cbv zeta in Hc. apply in_app_iff in Hc as [Hc|Hc].
  - in_cases ltac:(cnb).
  - revert Hc. destruct (ck_rz k =? kChunkHeaderSize); intros Hc; in_cases ltac:(cnb).
Qed.
Lemma sec_cells_nb : forall S c, In c (sec_cells S) -> cell_nb c = true.
Proof using.
  intros S c Hc. unfold sec_cells in Hc. destruct Hc as [<-|[<-|[<-|Hc]]]; [cnb..|].
  apply in_app_iff in Hc as [Hc|Hc].
  - apply in_map_iff in Hc as (ir & <- & _). cnb.
  - apply in_flat_map in Hc as (k & _ & Hc). revert Hc. destruct (ck_beg k); intros Hc; in_cases ltac:(cnb).
Qed.
Lemma batch_cells_nb : forall l c, In c (batch_cells l) -> cell_nb c = true.
Proof using.
  induction l as [|b t IH]; intros c Hc; [destruct Hc|]. cbn [batch_cells] in Hc.
  destruct Hc as [<-|[<-|[<-|Hc]]].
  - unfold cell_nb. cbn [c_at c_val c8]. destruct t; reflexivity.
  - cnb.
  - cnb.
  - apply in_app_iff in Hc as [Hc|Hc]; [|exact (IH c Hc)].
    apply in_map_iff in Hc as (iv & <- & _). cnb.
Qed.
Lemma qc_cells_nb : forall root q c, nonbsb root = true -> In c (qc_cells root q) -> cell_nb c = true.
Proof using.
  intros root q c Hr Hc. unfold qc_cells in Hc. destruct Hc as [<-|[<-|[<-|[<-|Hc]]]].
  - unfold cell_nb. cbn [c_at c_val z8 c8]. rewrite Hr. reflexivity.
  - unfold cell_nb. cbn [c_at c_val c8]. rewrite nonbsb_aoff, Hr. destruct (qc_list q); reflexivity.
  - unfold cell_nb. cbn [c_at c_val c8]. rewrite nonbsb_aoff, Hr. destruct (rev (qc_list q)); reflexivity.
  - unfold cell_nb. cbn [c_at c_val z8 c8]. rewrite nonbsb_aoff, Hr. reflexivity.
  - exact (batch_cells_nb _ c Hc).
Qed.
Lemma quar_cells_nb : forall S c, In c (quar_cells S) -> cell_nb c = true.
Proof using.
  intros S c Hc. unfold quar_cells in Hc. destruct Hc as [<-|[<-|Hc]]; [cnb..|].
  apply in_app_iff in Hc as [Hc|Hc]; [exact (qc_cells_nb (AT t_qc) _ c eq_refl Hc) | exact (qc_cells_nb (AInst o_q_size) _ c eq_refl Hc)].
Qed.
Lemma fs_cells_nb : forall S c, In c (fs_cells S) -> cell_nb c = true.
Proof using.
  intros S c Hc. unfold fs_cells in Hc. destruct Hc as [<-|[<-|Hc]]; [cnb..|].
  apply in_map_iff in Hc as (iv & <- & _). cnb.
Qed.
Lemma ialloc_cells_nb : forall B S c, In c (ialloc_cells B S) -> cell_nb c = true.
Proof using.
  intros B S c Hc. unfold ialloc_cells in Hc. cbv zeta in Hc.
  in_cases ltac:(unfold cell_nb; cbn [c_at c_val z1 z8 c1 c8]; destruct (st_internal_inited S); reflexivity).
Qed.
Lemma acells_nb : forall B ly S c, In c (acells B ly S) -> ~ In c (depot_cells ly S) -> cell_nb c = true.
Proof using.
  intros B ly S c Hc ND. unfold acells in Hc. rewrite !in_app_iff in Hc.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]]].
  - apply in_flat_map in Hc as (x & _ & Hc). exact (region_cells_nb _ _ _ Hc).
  - apply in_flat_map in Hc as (x & _ & Hc). exact (cache_cells_nb _ _ _ Hc).
  - apply in_flat_map in Hc as (k & _ & Hc). exact (chunk_cells_nb _ _ Hc).
  - exact (sec_cells_nb _ _ Hc).
  - exact (quar_cells_nb _ _ Hc).
  - exact (fs_cells_nb _ _ Hc).
  - contradiction.
  - exact (ialloc_cells_nb _ _ _ Hc).
  - destruct Hc as [<-|[]]. cnb.
Qed.
(* ajunk, aclient and aareas (but the two block entries) name no ANB / ASB either. *)
Lemma ajunk_nb : forall B ly S r, WireSyms B -> In r (ajunk B ly S) -> nonbsb (fst r) = true.
Proof using.
  intros B ly S r HB Hr. unfold ajunk in Hr. destruct Hr as [<-|[<-|Hr]]; [reflexivity..|].
  rewrite !in_app_iff in Hr.
  destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[Hr|[Hr|Hr]]]]]]].
  - apply in_flat_map in Hr as (x & _ & Hr). unfold region_junk in Hr. cbv zeta in Hr.
    in_cases ltac:(cbn [fst]; rewrite ?nonbsb_aoff; reflexivity).
  - apply in_flat_map in Hr as (x & _ & Hr). unfold cache_junk in Hr. cbv zeta in Hr. in_cases ltac:(reflexivity).
  - apply in_flat_map in Hr as (k & _ & Hr). unfold chunk_junk in Hr. cbv zeta in Hr. rewrite !in_app_iff in Hr.
    destruct Hr as [Hr|[Hr|[Hr|Hr]]].
    + revert Hr. destruct (ck_rz k =? kChunkHeaderSize); intros Hr;
        in_cases ltac:(cbn [fst]; rewrite ?nonbsb_aoff, ?nonbsb_sptr; reflexivity).
    + in_cases ltac:(cbn [fst]; rewrite ?nonbsb_aoff, ?nonbsb_sptr; reflexivity).
    + revert Hr. destruct (ck_state k); intros Hr;
        in_cases ltac:(cbn [fst]; rewrite ?nonbsb_aoff, ?nonbsb_sptr; reflexivity).
    + in_cases ltac:(cbn [fst]; rewrite ?nonbsb_aoff, ?nonbsb_sptr; reflexivity).
  - unfold sec_junk in Hr. destruct Hr as [<-|[<-|[<-|Hr]]]; [reflexivity..|].
    apply in_flat_map in Hr as (k & _ & Hr). revert Hr. destruct (ck_beg k); intros Hr; in_cases ltac:(reflexivity).
  - unfold quar_junk in Hr. apply in_flat_map in Hr as (b & _ & Hr). unfold batch_junk in Hr.
    in_cases ltac:(cbn [fst]; rewrite nonbsb_aoff; reflexivity).
  - unfold thread_junk in Hr. in_cases ltac:(reflexivity).
  - in_cases ltac:(reflexivity).
  - destruct (ts_junk B HB ly r Hr) as (z & Ez & _). rewrite Ez. reflexivity.
Qed.
Lemma aclient_nb : forall S r, In r (aclient S) -> nonbsb (fst r) = true.
Proof using.
  intros S r Hr. unfold aclient in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|Hr]].
  - apply in_flat_map in Hr as (k & _ & Hr). unfold chunk_user in Hr. revert Hr. destruct (ck_state k); intros Hr;
      in_cases ltac:(apply nonbsb_sptr).
  - apply in_map_iff in Hr as (cp & <- & _). reflexivity.
  - apply in_map_iff in Hr as (cp & <- & _). reflexivity.
Qed.
Lemma aareas_nb : forall S r, In r (aareas S) -> fst r <> ANB 0 -> fst r <> ASB 0 -> nonbsb (fst r) = true.
Proof using.
  intros S r Hr N1 N2. unfold aareas in Hr. rewrite !in_app_iff in Hr. destruct Hr as [Hr|[Hr|[Hr|Hr]]].
  - apply in_flat_map in Hr as (x & _ & Hr). in_cases ltac:(reflexivity).
  - in_cases ltac:(reflexivity).
  - apply in_flat_map in Hr as (k & _ & Hr). revert Hr. destruct (ck_beg k); intros Hr; in_cases ltac:(reflexivity).
  - in_cases ltac:(first [reflexivity | exfalso; apply N1; reflexivity | exfalso; apply N2; reflexivity]).
Qed.

(* Cells and ranges without ANB / ASB keep their meaning through the growth and a reader extension. *)
Lemma cell_holds_grow : forall B l x sx (rd rd' : reader) c, rd_ext rd rd' -> cell_nb c = true ->
  cell_holds B l rd c -> cell_holds B (set_ly_SB (set_ly_NB l x) sx) rd' c.
Proof using.
  intros B l x sx rd rd' c RX N H. unfold cell_nb in N. apply andb_prop in N as [N1 N2].
  unfold cell_holds in *. cbv zeta in *. rewrite (aeval_nonbsb B l x sx _ N1).
  destruct (c_val c) as [e|mk v].
  - rewrite (aeval_nonbsb B l x sx _ N2). intros k Hk. apply RX. exact (H k Hk).
  - destruct H as (b & Hb & Hm). exists b. split; [apply RX; exact Hb | exact Hm].
Qed.
Lemma range_vis_grow : forall B l x sx (rd rd' : reader) r, rd_ext rd rd' -> nonbsb (fst r) = true ->
  range_vis B l rd r -> range_vis B (set_ly_SB (set_ly_NB l x) sx) rd' r.
Proof using.
  intros B l x sx rd rd' r RX N H i Hi. rewrite (aeval_nonbsb B l x sx _ N). specialize (H i Hi).
  destruct (rd (aeval B l (fst r) + i)) as [v|] eqn:E; [|exfalso; apply H; reflexivity].
  rewrite (RX _ _ E). discriminate.
Qed.
Lemma sptr_addr_grow : forall B l x sx p, sptr_addr B (set_ly_SB (set_ly_NB l x) sx) p = sptr_addr B l p.
Proof using. intros B l x sx p. destruct p; reflexivity. Qed.
Lemma ashadow_grow : forall B l x sx S g, ashadow B (set_ly_SB (set_ly_NB l x) sx) S g = ashadow B l S g.
Proof using.
  intros B l x sx S g.
  assert (EB : forall k, ck_base B (set_ly_SB (set_ly_NB l x) sx) k = ck_base B l k)
    by (intros k; unfold ck_base; apply sptr_addr_grow).
  assert (EF : forall L, find_chunk_at B (set_ly_SB (set_ly_NB l x) sx) L g = find_chunk_at B l L g).
  { induction L as [|k L IH]; [reflexivity|]. cbn [find_chunk_at]. rewrite EB, IH. reflexivity. }
  unfold ashadow. rewrite EF. destruct (find_chunk_at B l (st_chunks S) g) as [k|]; [rewrite EB|]; reflexivity.
Qed.
Lemma aclient_byte_grow : forall B l x sx S a, aclient_byte B (set_ly_SB (set_ly_NB l x) sx) S a <-> aclient_byte B l S a.
Proof using.
  intros B l x sx S a. pose proof (sptr_addr_grow B l x sx) as E.
  unfold aclient_byte. split; intros [(k & K1 & K2 & K3) | (cp & C1 & C2)].
  - left. exists k. rewrite E in K3. tauto.
  - right. exists cp. exact (conj C1 C2).
  - left. exists k. rewrite E. tauto.
  - right. exists cp. exact (conj C1 C2).
Qed.

(* The lists of the growth: l has both slots 0, the grown layout the two blocks. *)
Section lists.
Variables (l : alayout) (nb sb : Z).
Hypotheses (N0 : ly_NB l = 0) (S0 : ly_SB l = 0) (NZ : nb <> 0) (SZ : sb <> 0).
Lemma owned_core_grow : forall B a, owned_core B l a -> owned_core B (set_ly_SB (set_ly_NB l nb) sb) a.
Proof using N0 S0 NZ SZ.
  intros B a [H|[H|H]]; [left; exact H | right; left | right; right; exact H].
  rewrite (core_extents_set (set_ly_SB (set_ly_NB l nb) sb) NZ SZ).
  unfold core_extents in H. rewrite N0, S0 in H. cbn [Z.eqb] in H.
  apply Exists_exists in H as (z & Hz & Hin). apply Exists_exists. exists z. split; [|exact Hin].
  cbn [In] in Hz |- *.
  destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    try (exfalso; unfold in_zr in Hin; cbn [fst snd] in Hin; lia); osearch.
Qed.
Lemma lazy_zones_grow : forall z, In z (lazy_zones l) -> z = (4096, 0) \/ In z (lazy_zones (set_ly_SB (set_ly_NB l nb) sb)).
Proof using N0 S0 NZ SZ.
  intros z Hz. rewrite (lazy_zones_set (set_ly_SB (set_ly_NB l nb) sb) NZ SZ). rewrite (static_extents_set (set_ly_SB (set_ly_NB l nb) sb) NZ SZ).
  unfold lazy_zones in Hz. rewrite S0 in Hz. cbn [Z.eqb] in Hz.
  destruct (first_put_old l N0 S0) as (_ & ESt & _). rewrite ESt in Hz.
  repeat rewrite in_app_iff in Hz. repeat rewrite in_app_iff. cbn [In] in Hz |- *. leaves;
    osearch.
Qed.
Lemma perm_live_grow : forall z, In z (perm_live (set_ly_SB (set_ly_NB l nb) sb)) -> z = (nb, kNodesBlockSize) \/ z = (sb, kStoreBlockSize) \/ In z (perm_live l).
Proof using N0 S0 NZ SZ.
  intros z Hz. unfold perm_live in Hz |- *. rewrite N0, S0. cbn [Z.eqb].
  change (ly_NB (set_ly_SB (set_ly_NB l nb) sb)) with nb in Hz. change (ly_SB (set_ly_SB (set_ly_NB l nb) sb)) with sb in Hz.
  rewrite (proj2 (Z.eqb_neq _ 0) NZ), (proj2 (Z.eqb_neq _ 0) SZ) in Hz.
  repeat rewrite in_app_iff in Hz. repeat rewrite in_app_iff. cbn [In] in Hz |- *. leaves; osearch.
Qed.
Lemma perm_maps_grow : forall z, In z (perm_maps (set_ly_SB (set_ly_NB l nb) sb)) -> z = (nb, kNodesBlockSize) \/ z = (sb, kStoreBlockSize) \/ In z (perm_maps l).
Proof using N0 S0 NZ SZ.
  intros z Hz. rewrite (perm_maps_set (set_ly_SB (set_ly_NB l nb) sb) NZ SZ) in Hz. unfold perm_maps. rewrite N0, S0. cbn [Z.eqb].
  repeat rewrite in_app_iff in Hz. repeat rewrite in_app_iff. cbn [In] in Hz |- *. leaves; osearch.
Qed.
Lemma hfree_grow : forall S g, 4096 <= g -> hfree (set_ly_SB (set_ly_NB l nb) sb) S g -> hfree l S g.
Proof using N0 S0 NZ SZ.
  intros S g Hg H. unfold hfree in H |- *.
  rewrite (static_extents_set (set_ly_SB (set_ly_NB l nb) sb) NZ SZ), (vis0_zones_set (set_ly_SB (set_ly_NB l nb) sb) NZ SZ) in H.
  destruct (first_put_old l N0 S0) as (_ & ESt & EV). rewrite ESt, EV.
  apply Forall_app in H as [H1 H]. apply Forall_app in H as [H2 H3].
  apply Forall_app. split; [|apply Forall_app; split; [|exact H3]].
  - exact (first_put_forall_swap2 (fun e : Z * Z => g + 8 <= fst e \/ fst e + snd e <= g)
      [(ly_prim l, kPrimResvSize); (ly_Q l, kPtrArrayResv); (ly_T l, kThreadObjSize); (ly_F l, kFakeStackSize)]
      [(ly_C l, 256); (ly_D l, 4096); (ly_stk_lo l, ly_stk_hi l - ly_stk_lo l); ly_img l]
      (nb, kNodesBlockSize) (sb, kStoreBlockSize) (4096, 0) (4096, 0) H1 ltac:(cbn; lia) ltac:(cbn; lia)).
  - exact (first_put_forall_swap2 (fun e : Z * Z => g + 8 <= fst e \/ fst e + snd e <= g)
      [(ly_T l, kThreadObjSize); (ly_F l, kFakeStackSize)]
      ([(ly_C l, kCtxMapSize); (ly_D l, 4096); (ly_Q l, kPtrArrayResv); (ly_space l + kRegionInfoOff, 4096); ly_img l]
       ++ ly_extra l)
      (nb, kNodesBlockSize) (sb, kStoreBlockSize) (4096, 0) (4096, 0) H2 ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
End lists.

Lemma sum_count_ext_on : forall P Q l,
  (forall q x, In q l -> YK0g.B q <= x < YK0g.B q + YK0g.S q -> P x = Q x) ->
  YK0g.sum_count P l = YK0g.sum_count Q l.
Proof using.
  intros P Q l H. induction l as [|q l IH]; [reflexivity|]. cbn [YK0g.sum_count].
  rewrite IH by (intros q' x Hq' Hx; exact (H q' x (or_intror Hq') Hx)). f_equal.
  unfold YK0g.iv_count. apply YK0g.zcount_ext. intros x Hx. apply (H q x (or_introl eq_refl)).
  pose proof (YK0g.S_range q). rewrite Z2Nat.id in Hx by lia. exact Hx.
Qed.

(* ===== AR_but_depot_grow: ONE statement for every first-Put finish. The walk proves
   AR_but_depot for the final state Sf and memory memf at its own layout lyW (the Put's layout ly with at most ly_sec
   changed: lyW := ly for a primary malloc, AFj1 / AFjf / AFj2 / AFjg / AFkz; lyW := set_ly_sec ly r mb for the
   secondary one, AFjy), at the Put's entry world W and at a model mdold with the Put's entry maps (mdold :=
   with_vm_backing (m_vm_lazy md) mat md); the lemma gives it at lyF (lyW with the Put's two blocks: lyF := ly', or
   set_ly_sec ly' r mb), at the Put's post world W' and at a model mdf with the Put's post maps. Sf and memf do not
   change. Premises beyond first_malloc_AR's Put side: wle W W' and A_bytes (w_A W') <= abudget Sf (AR_wle's,
   YG0n.v:841-842). ===== *)
Lemma AR_but_depot_grow : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (tr : list Z) (ly' : alayout) (W' : world tfibsegs) (md' : Model)
    (c' : config) (Sf : astate) (memf : word -> option byte) (lyW lyF : alayout) (mdold mdf : Model),
  WireSyms B -> st_depot S = [] -> ly_NB ly = 0 -> layout_ok ly -> img_cover ly ->
  put_effect ly W md ly' W' md' -> depot_first_put_post B W ly S regs mem md tr ly' W' md' c' ->
  ly_core lyW = ly_core ly -> lyF = set_ly_SB (set_ly_NB lyW (ly_NB ly')) (ly_SB ly') ->
  m_vmmaps mdold = m_vmmaps md -> m_vm_lazy mdold = m_vm_lazy md ->
  m_vmmaps mdf = m_vmmaps md' -> m_vm_lazy mdf = m_vm_lazy md' ->
  wle W W' -> A_bytes (w_A W') <= abudget Sf ->
  AR_but_depot B lyW Sf W memf mdold ->
  AR_but_depot B lyF Sf W' memf mdf.
Proof using kd_grow_NB kd_grow_SB kd_grow_trans depot_ok_pre_kd depot_ok_post_kd as_const_g2_def
  am_depot_mono_kd_intro am_alloc_depot_kd_intro.
  intros B W ly S regs mem md tr ly' W' md' c' Sf memf lyW lyF mdold mdf HB ES HNB0 LY IMG PE POST LW LF MO1 MO2 MF1 MF2
    WLE AB ABD.
  destruct PE as [(E & _ & _) | (nb & sb & N0 & S0 & NZ & SZ & EL & _ & WA & WH & _ & VM & LZ)].
  { exfalso. destruct POST as (regs' & mem' & _ & _ & _ & _ & _ & _ & _ & (HN & _) & _). apply HN. rewrite E. exact HNB0. }
  destruct POST as (regs' & mem' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PNB & ANB & PSB & ASB & DNS & FNB & FSB & _ & _ & _ & _
    & VNB & VSB).
  subst ly'.
  change (ly_NB (set_ly_SB (set_ly_NB ly nb) sb)) with nb in *.
  change (ly_SB (set_ly_SB (set_ly_NB ly nb) sb)) with sb in *.
  subst lyF.
  (* the walk's layout lyW is ly up to its secondary slots *)
  assert (WNB : ly_NB lyW = 0) by exact (eq_trans (f_equal ly_NB LW) N0).
  assert (WSB : ly_SB lyW = 0) by exact (eq_trans (f_equal ly_SB LW) S0).
  pose proof (ly_core_layout_ok lyW ly LW LY) as LYW.
  assert (EXTW : ext_but_NB lyW = ext_but_NB ly)
    by (change (ext_but_NB (ly_core lyW) = ext_but_NB (ly_core ly)); rewrite LW; reflexivity).
  assert (XW : ly_extra lyW = ly_extra ly) by exact (f_equal ly_extra LW).
  unfold first_put_avoid in FNB, FSB. rewrite <- EXTW, <- XW in FNB, FSB.
  apply Forall_app in FNB as [FNB1 FNB]. apply Forall_app in FNB as [FNB2 _].
  apply Forall_app in FSB as [FSB1 FSB]. apply Forall_app in FSB as [FSB2 _].
  unfold ext_but_NB in FNB1, FSB1. rewrite WSB in FNB1, FSB1. cbn [Z.eqb] in FNB1, FSB1. rewrite app_nil_r in FNB1, FSB1.
  pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
  pose proof (YG0s.in_app_small _ _ ANB ltac:(unfold kNodesBlockSize; lia)) as NBR.
  pose proof (YG0s.in_app_small _ _ ASB ltac:(unfold kStoreBlockSize; lia)) as SBR.
  unfold kNodesBlockSize in NBR. unfold kStoreBlockSize in SBR.
  assert (NB4 : 4096 <= nb) by exact (proj1 ANB). assert (SB4 : 4096 <= sb) by exact (proj1 ASB).
  (* the reader only gains: wle *)
  pose proof (aview_ext tfibsegs (w_H W) (w_H W') memf (w_Hoff W) WLE) as RX.
  (* the final model: the entry maps plus both blocks, the store block lazy *)
  assert (HVM : m_vmmaps mdf = m_vmmaps (mmap_model (Z_to_bv 64 sb) (Z_to_bv 64 kStoreBlockSize)
                                           (mmap_model (Z_to_bv 64 nb) (Z_to_bv 64 kNodesBlockSize) mdold))).
  { rewrite MF1, VM. apply mmap_model_vmmaps_eq, mmap_model_vmmaps_eq. symmetry. exact MO1. }
  assert (VMF : vm_maps (m_vmmaps mdf) = wiv (sb, kStoreBlockSize) :: wiv (nb, kNodesBlockSize) :: vm_maps (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (NAF : vm_noaccess (m_vmmaps mdf) = vm_noaccess (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (LIMF : vm_limit (m_vmmaps mdf) = vm_limit (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (RESF : vm_reserved (m_vmmaps mdf) = vm_reserved (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (TOPF : alloc_top (m_vmmaps mdf) = alloc_top (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (ISPF : vm_init_sp (m_vmmaps mdf) = vm_init_sp (m_vmmaps mdold))
    by (rewrite HVM; unfold mmap_model; rewrite !YK0g.m_vmmaps_with_vmmaps; reflexivity).
  assert (LZF : m_vm_lazy mdf = wiv (sb, kStoreBlockSize) :: m_vm_lazy mdold) by (rewrite MF2, LZ, MO2; reflexivity).
  assert (INF : forall e, In e (vm_maps (m_vmmaps mdold)) -> In e (vm_maps (m_vmmaps mdf)))
    by (intros e He; rewrite VMF; right; right; exact He).
  assert (WNBb : bv_unsigned (w64 nb) = nb) by (apply YK0g.fg_lit; lia).
  assert (WSBb : bv_unsigned (w64 sb) = sb) by (apply YK0g.fg_lit; lia).
  assert (WKN : bv_unsigned (w64 kNodesBlockSize) = kNodesBlockSize) by (apply YK0g.fg_lit; unfold kNodesBlockSize; lia).
  assert (WKS : bv_unsigned (w64 kStoreBlockSize) = kStoreBlockSize) by (apply YK0g.fg_lit; unfold kStoreBlockSize; lia).
  assert (BSB0 : bv_unsigned (fst (wiv (sb, kStoreBlockSize))) = sb) by exact WSBb.
  assert (SSB0 : bv_unsigned (snd (wiv (sb, kStoreBlockSize))) = kStoreBlockSize) by exact WKS.
  assert (BNB0 : bv_unsigned (fst (wiv (nb, kNodesBlockSize))) = nb) by exact WNBb.
  assert (SNB0 : bv_unsigned (snd (wiv (nb, kNodesBlockSize))) = kNodesBlockSize) by exact WKN.
  (* X: nothing excluded at lyW, the two blocks at the grown layout *)
  assert (EXW : (if ly_NB lyW =? 0 then [] else [wiv (ly_NB lyW, kNodesBlockSize)]) ++
                (if ly_SB lyW =? 0 then [] else [wiv (ly_SB lyW, kStoreBlockSize)]) = [])
    by (rewrite WNB, WSB; reflexivity).
  assert (EXG : (if ly_NB (set_ly_SB (set_ly_NB lyW nb) sb) =? 0 then []
                 else [wiv (ly_NB (set_ly_SB (set_ly_NB lyW nb) sb), kNodesBlockSize)]) ++
                (if ly_SB (set_ly_SB (set_ly_NB lyW nb) sb) =? 0 then []
                 else [wiv (ly_SB (set_ly_SB (set_ly_NB lyW nb) sb), kStoreBlockSize)]) =
                [wiv (nb, kNodesBlockSize); wiv (sb, kStoreBlockSize)]).
  { change (ly_NB (set_ly_SB (set_ly_NB lyW nb) sb)) with nb. change (ly_SB (set_ly_SB (set_ly_NB lyW nb) sb)) with sb.
    rewrite (proj2 (Z.eqb_neq _ 0) NZ), (proj2 (Z.eqb_neq _ 0) SZ). reflexivity. }
  unfold AR_but_depot in ABD |- *. cbv zeta in ABD |- *. rewrite EXW in ABD. rewrite EXG.
  destruct ABD as (WF & UN & SY & PL & CG2 & CO & CE & FA & FL & SH & ZS & JK & AA & CL & ZR & TSD & SI &
                   AIMG & ALIM & ARES & APRIM & AQ & AHS & ASEC & ACOV & AEX & APERM & ABAND & ASECX & ATOP & AIMGCOV &
                   ASHNA & ABUD & AMWF & AHSS).
  pose proof AMWF as ((MW1 & MW2 & MW3 & MWP & MWSP) & MWPOS).
  (* every secondary extent of Sf is a map of the Put's entry model, so both blocks miss it *)
  assert (SECB : forall e, In e (sec_extents lyW Sf) ->
            zdisjoint (nb, kNodesBlockSize) e /\ zdisjoint (sb, kStoreBlockSize) e /\
            bv_unsigned (fst (wiv e)) = fst e /\ bv_unsigned (snd (wiv e)) = snd e).
  { intros e He. pose proof (ASEC e He) as Hm. rewrite MO1 in Hm.
    pose proof (proj1 (Forall_forall _ _) VNB _ Hm) as D1. pose proof (proj1 (Forall_forall _ _) VSB _ Hm) as D2.
    pose proof (proj1 (Forall_forall _ _) (YG08.sec_extents_sizes64 _ lyW Sf WF) e He) as SZe. cbv beta in SZe.
    destruct PL as [PF _]. pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & IAe & _).
    destruct (YG0s.in_app_small _ _ IAe ltac:(lia)) as [IE1 IE2].
    assert (E1 : bv_unsigned (fst (wiv e)) = fst e) by (unfold wiv, w64; cbn [fst]; apply YK0g.fg_lit; lia).
    assert (E2 : bv_unsigned (snd (wiv e)) = snd e) by (unfold wiv, w64; cbn [snd]; apply YK0g.fg_lit; lia).
    cbv beta in D1, D2. rewrite E1, E2 in D1, D2. split; [exact D1|]. split; [exact D2|]. split; [exact E1 | exact E2]. }
  split; [exact WF|]. split; [exact UN|]. split; [exact SY|].
  (* am_placed *)
  split.
  { unfold sec_placed in PL |- *. destruct PL as [PF PD]. split; [exact PF|].
    rewrite (static_extents_set (set_ly_SB (set_ly_NB lyW nb) sb) NZ SZ).
    destruct (first_put_old lyW WNB WSB) as (_ & ESt & _). rewrite ESt in PD.
    exact (first_put_pairwise_swap2 _ YG0s.zdisjoint_sym (sec_extents lyW Sf) _ _ _ _ (nb, kNodesBlockSize)
      (sb, kStoreBlockSize) PD
      (proj2 (Forall_forall _ _) (fun e He => proj1 (SECB e He)))
      (proj2 (Forall_forall _ _) (fun e He => proj1 (proj2 (SECB e He))))
      FNB1 FSB1 DNS). }
  (* am_const (as_const_g2) *)
  split.
  { apply Forall_forall. intros c Hc. apply as_const_g2_def in Hc as [Hc Hna].
    rewrite (ts_const B HB) in Hc. change (Tfib_const (set_ly_SB (set_ly_NB lyW nb) sb)) with (Tfib_const lyW) in Hc.
    pose proof (proj1 (forallb_forall _ _) (b2_const_ok lyW) c Hc) as OK. unfold b2_cell_ok in OK.
    apply andb_prop in OK as [OK _].
    assert (Hc' : In c (as_const_g2 B lyW)) by (apply as_const_g2_def; split; [rewrite (ts_const B HB); exact Hc | exact Hna]).
    exact (cell_holds_grow B lyW nb sb _ _ c RX OK (proj1 (Forall_forall _ _) CG2 c Hc')). }
  (* am_const_owned *)
  split.
  { apply Forall_forall. intros c Hc.
    rewrite (ts_const B HB) in Hc. change (Tfib_const (set_ly_SB (set_ly_NB lyW nb) sb)) with (Tfib_const lyW) in Hc.
    pose proof (proj1 (forallb_forall _ _) (b2_const_ok lyW) c Hc) as OK. unfold b2_cell_ok in OK.
    apply andb_prop in OK as [OK _]. apply andb_prop in OK as [N1 _].
    assert (Hc' : In c (as_const B lyW)) by (rewrite (ts_const B HB); exact Hc).
    pose proof (proj1 (Forall_forall _ _) CO c Hc') as Ho. intros k Hk. specialize (Ho k Hk).
    rewrite (aeval_nonbsb B lyW nb sb _ N1). exact (owned_core_grow lyW nb sb WNB WSB NZ SZ B _ Ho). }
  (* am_cells but the depot cells *)
  split.
  { intros c Hc ND. change (In c (acells B lyW Sf)) in Hc. change (~ In c (depot_cells lyW Sf)) in ND.
    exact (cell_holds_grow B lyW nb sb _ _ c RX (acells_nb B lyW Sf c Hc ND) (CE c Hc ND)). }
  (* am_fa, am_flags, am_shadow, am_zshadow *)
  split. { intros c i v Hc Hi Hv k Hk. apply RX. exact (FA c i v Hc Hi Hv k Hk). }
  split. { intros cid pos Hc Hp. apply RX. exact (FL cid pos Hc Hp). }
  split. { intros g v Hg Hv. rewrite ashadow_grow in Hv. apply RX. exact (SH g v Hg Hv). }
  split.
  { unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr.
    eapply zero_shadow_ext; [exact RX|]. exact (proj1 (Forall_forall _ _) ZS r Hr). }
  (* am_junk, am_areas but NB / SB, am_client, am_zero *)
  split.
  { assert (EJ : ajunk B (set_ly_SB (set_ly_NB lyW nb) sb) Sf = ajunk B lyW Sf)
      by (unfold ajunk; rewrite (ts_junk_ly B HB lyW (set_ly_SB (set_ly_NB lyW nb) sb)); reflexivity).
    rewrite EJ. apply Forall_forall. intros r Hr.
    exact (range_vis_grow B lyW nb sb _ _ r RX (ajunk_nb B lyW Sf r HB Hr) (proj1 (Forall_forall _ _) JK r Hr)). }
  split.
  { intros r Hr N1 N2. exact (range_vis_grow B lyW nb sb _ _ r RX (aareas_nb Sf r Hr N1 N2) (AA r Hr N1 N2)). }
  split.
  { apply Forall_forall. intros r Hr.
    exact (range_vis_grow B lyW nb sb _ _ r RX (aclient_nb Sf r Hr) (proj1 (Forall_forall _ _) CL r Hr)). }
  split.
  { apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) ZR r Hr) as Hz.
    unfold ialloc_zero in Hr. cbv zeta in Hr. destruct Hr as [<-|[<-|[]]]; intros i Hi; apply RX; exact (Hz i Hi). }
  split; [exact TSD|]. split; [exact SI|].
  (* ALedger *)
  split; [exact AIMG|]. split; [rewrite LIMF; exact ALIM|]. split; [rewrite RESF; exact ARES|].
  (* al_prim *)
  split.
  { destruct APRIM as (pieces & PP & PI). exists pieces. split; [exact PP|]. intros p.
    change (ly_prim (set_ly_SB (set_ly_NB lyW nb) sb)) with (ly_prim lyW). rewrite (PI p), VMF.
    split; [intros (Hin & H1 & H2 & H3); split; [right; right; exact Hin | tauto]|].
    intros (Hin & H1 & H2 & H3). split; [|tauto]. cbn [In] in Hin.
    pose proof (lo_high _ LYW) as HI. unfold in_high, kHighMemBeg in HI.
    pose proof (proj1 (Forall_forall _ _) FNB1 (ly_prim lyW, kPrimResvSize) ltac:(left; reflexivity)) as DP1.
    pose proof (proj1 (Forall_forall _ _) FSB1 (ly_prim lyW, kPrimResvSize) ltac:(left; reflexivity)) as DP2.
    unfold zdisjoint in DP1, DP2. cbn [fst snd] in DP1, DP2, H2, H3.
    destruct Hin as [Hin|[Hin|Hin]]; [| |exact Hin]; exfalso.
    - assert (Hf : bv_unsigned (fst (wiv (sb, kStoreBlockSize))) = bv_unsigned (fst (wiv p))) by (rewrite Hin; reflexivity).
      assert (Hs : bv_unsigned (snd (wiv (sb, kStoreBlockSize))) = bv_unsigned (snd (wiv p))) by (rewrite Hin; reflexivity).
      change (bv_unsigned (w64 sb) = bv_unsigned (w64 (fst p))) in Hf.
      change (bv_unsigned (w64 kStoreBlockSize) = bv_unsigned (w64 (snd p))) in Hs.
      rewrite WSBb, YK0g.fg_lit in Hf by (unfold kPrimResvSize in *; lia).
      rewrite WKS, YK0g.fg_lit in Hs by (unfold kPrimResvSize in *; lia).
      unfold kStoreBlockSize, kPrimResvSize in *. lia.
    - assert (Hf : bv_unsigned (fst (wiv (nb, kNodesBlockSize))) = bv_unsigned (fst (wiv p))) by (rewrite Hin; reflexivity).
      assert (Hs : bv_unsigned (snd (wiv (nb, kNodesBlockSize))) = bv_unsigned (snd (wiv p))) by (rewrite Hin; reflexivity).
      change (bv_unsigned (w64 nb) = bv_unsigned (w64 (fst p))) in Hf.
      change (bv_unsigned (w64 kNodesBlockSize) = bv_unsigned (w64 (snd p))) in Hs.
      rewrite WNBb, YK0g.fg_lit in Hf by (unfold kPrimResvSize in *; lia).
      rewrite WKN, YK0g.fg_lit in Hs by (unfold kPrimResvSize in *; lia).
      unfold kNodesBlockSize, kPrimResvSize in *. lia. }
  split; [exact (INF _ AQ)|]. split; [exact (INF _ AHS)|].
  split; [intros e He; exact (INF _ (ASEC e He))|].
  (* al_cover *)
  split.
  { intros e He NX. rewrite VMF in He. destruct He as [He|[He|He]].
    { exfalso. apply NX. rewrite <- He. right. left. reflexivity. }
    { exfalso. apply NX. rewrite <- He. left. reflexivity. }
    pose proof (ACOV e He ltac:(intros [])) as Hc. apply Exists_exists in Hc as (z & Hz & Hcz). apply Exists_exists.
    pose proof (MWPOS e He) as Pe.
    apply in_app_iff in Hz as [Hz|Hz].
    - destruct (lazy_zones_grow lyW nb sb WNB WSB NZ SZ z Hz) as [Ez|Hz'].
      + exfalso. subst z. cbn [fst snd] in Hcz. lia.
      + exists z. split; [apply in_app_iff; left; exact Hz' | exact Hcz].
    - exists z. split; [apply in_app_iff; right; exact Hz | exact Hcz]. }
  (* al_eager_x *)
  split.
  { assert (WFo : YK0g.model_ivs_wf mdold)
      by (split; [|split; [|split]]; [intros q Hq; exact (MW1 q Hq) | intros q Hq; exact (MW2 q Hq) |
                                      intros q Hq; exact (MW3 q Hq) | exact MWSP]).
    assert (BSB : YK0g.B (wiv (sb, kStoreBlockSize)) = sb) by exact WSBb.
    assert (SSB : YK0g.S (wiv (sb, kStoreBlockSize)) = kStoreBlockSize) by exact WKS.
    assert (BNB : YK0g.B (wiv (nb, kNodesBlockSize)) = nb) by exact WNBb.
    assert (SNB : YK0g.S (wiv (nb, kNodesBlockSize)) = kNodesBlockSize) by exact WKN.
    assert (WFf : YK0g.model_ivs_wf mdf).
    { split; [|split; [|split]].
      - intros q Hq. rewrite VMF in Hq. destruct Hq as [<-|[<-|Hq]]; [| |exact (MW1 q Hq)]; unfold YK0g.iv_wf;
          rewrite ?BSB, ?SSB, ?BNB, ?SNB; unfold kStoreBlockSize, kNodesBlockSize; lia.
      - intros q Hq. rewrite NAF in Hq. exact (MW2 q Hq).
      - intros q Hq. rewrite LZF in Hq. destruct Hq as [<-|Hq]; [|exact (MW3 q Hq)].
        unfold YK0g.iv_wf. rewrite BSB, SSB. unfold kStoreBlockSize; lia.
      - unfold YK06.init_sp_ok in *. rewrite ISPF. exact MWSP. }
    assert (NBE : nb_eager (set_ly_SB (set_ly_NB lyW nb) sb) = kNodesBlockSize).
    { unfold nb_eager. change (ly_NB (set_ly_SB (set_ly_NB lyW nb) sb)) with nb.
      rewrite (proj2 (Z.eqb_neq _ 0) NZ). reflexivity. }
    assert (NBW : nb_eager lyW = 0) by (unfold nb_eager; rewrite WNB; reflexivity).
    rewrite NBW in AEX. rewrite NBE.
    rewrite (YG0b.eager_used_sem _ WFf), NAF, LZF, VMF. rewrite (YG0b.eager_used_sem _ WFo) in AEX.
    change (sec_extents (set_ly_SB (set_ly_NB lyW nb) sb) Sf) with (sec_extents lyW Sf).
    set (na := vm_noaccess (m_vmmaps mdold)) in *. set (lz := m_vm_lazy mdold) in *.
    assert (CC : forall a l x, YK0g.covered (a :: l) x = (YK0g.in_iv a x || YK0g.covered l x)%bool) by reflexivity.
    (* the esec term: no secondary byte lies in the store block *)
    assert (ES2 : esec na (wiv (sb, kStoreBlockSize) :: lz) (sec_extents lyW Sf) = esec na lz (sec_extents lyW Sf)).
    { unfold esec. apply sum_count_ext_on. intros q x Hq Hx. apply in_map_iff in Hq as (e & <- & He).
      destruct (SECB e He) as (_ & D2 & E1 & E2). unfold YK0g.B, YK0g.S in Hx. rewrite E1, E2 in Hx.
      rewrite !YK0g.covered_app, CC. unfold YK0g.in_iv, YK0g.in_rng. rewrite BSB, SSB.
      unfold zdisjoint in D2. cbn [fst snd] in D2.
      replace ((sb <=? x) && (x <? sb + kStoreBlockSize))%bool with false by (symmetry; apply andb_false_iff;
        destruct D2 as [D2|D2]; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia]).
      rewrite orb_false_l. reflexivity. }
    rewrite ES2. cbn [YK0g.sum_count].
    assert (C0 : YK0g.iv_count (fun x => negb (YK0g.covered (na ++ wiv (sb, kStoreBlockSize) :: lz) x))
                   (wiv (sb, kStoreBlockSize)) = 0).
    { unfold YK0g.iv_count. rewrite BSB, SSB. apply YK0g.zcount_false. intros x Hx.
      rewrite Z2Nat.id in Hx by (unfold kStoreBlockSize; lia).
      rewrite YK0g.covered_app, CC. unfold YK0g.in_iv, YK0g.in_rng. rewrite BSB, SSB.
      replace ((sb <=? x) && (x <? sb + kStoreBlockSize))%bool with true
        by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite orb_true_l, orb_true_r. reflexivity. }
    assert (C1 : YK0g.iv_count (fun x => negb (YK0g.covered (na ++ wiv (sb, kStoreBlockSize) :: lz) x))
                   (wiv (nb, kNodesBlockSize)) <= kNodesBlockSize).
    { unfold YK0g.iv_count. rewrite SNB.
      pose proof (YK0g.zcount_le_len (fun x => negb (YK0g.covered (na ++ wiv (sb, kStoreBlockSize) :: lz) x))
        (YK0g.B (wiv (nb, kNodesBlockSize))) (Z.to_nat kNodesBlockSize)) as Hc.
      rewrite Z2Nat.id in Hc by (unfold kNodesBlockSize; lia). exact Hc. }
    assert (C2 : YK0g.sum_count (fun x => negb (YK0g.covered (na ++ wiv (sb, kStoreBlockSize) :: lz) x))
                   (vm_maps (m_vmmaps mdold))
                 <= YK0g.sum_count (fun x => negb (YK0g.covered (na ++ lz) x)) (vm_maps (m_vmmaps mdold))).
    { apply YK0g.sum_count_mono. intros x Hx. rewrite !YK0g.covered_app in *. rewrite CC in Hx.
      apply negb_true_iff in Hx. apply negb_true_iff. apply orb_false_iff in Hx as [Hx1 Hx2].
      apply orb_false_iff in Hx2 as [_ Hx2]. rewrite Hx1, Hx2. reflexivity. }
    lia. }
  (* al_perm *)
  split.
  { intros z Hz NX. destruct (perm_live_grow lyW nb sb WNB WSB NZ SZ z Hz) as [->|[->|Hz']].
    - exfalso. apply NX. left. reflexivity.
    - exfalso. apply NX. right. left. reflexivity.
    - exact (INF _ (APERM z Hz' ltac:(intros []))). }
  split; [intros z Hz; exact (INF _ (ABAND z Hz))|].
  (* al_secx *)
  split.
  { intros e z He Hz. destruct (perm_maps_grow lyW nb sb WNB WSB NZ SZ z Hz) as [->|[->|Hz']].
    - exact (YG0s.zdisjoint_sym _ _ (proj1 (SECB e He))).
    - exact (YG0s.zdisjoint_sym _ _ (proj1 (proj2 (SECB e He)))).
    - exact (ASECX e z He Hz'). }
  split; [rewrite TOPF; exact ATOP|]. split; [exact AIMGCOV|]. split; [rewrite NAF; exact ASHNA|].
  (* abudget_ok, amwf, ahs *)
  split.
  { eapply abudget_ok_transfer; [exact ABUD | reflexivity | | exact AB].
    intros i Hi. rewrite WA. right. right. exact Hi. }
  split.
  { split.
    - split; [|split; [|split; [|split]]].
      + intros q Hq. rewrite VMF in Hq. destruct Hq as [<-|[<-|Hq]]; [| |exact (MW1 q Hq)];
          rewrite ?BSB0, ?SSB0, ?BNB0, ?SNB0; unfold kStoreBlockSize, kNodesBlockSize; lia.
      + intros q Hq. rewrite NAF in Hq. exact (MW2 q Hq).
      + intros q Hq. rewrite LZF in Hq. destruct Hq as [<-|Hq]; [|exact (MW3 q Hq)].
        rewrite BSB0, SSB0. unfold kStoreBlockSize; lia.
      + rewrite VMF. cbn [pairwise]. rewrite BSB0, SSB0, BNB0, SNB0.
        split; [|split; [|exact MWP]].
        * apply Forall_cons; [cbv beta; rewrite BNB0, SNB0; unfold zdisjoint in DNS; cbn [fst snd] in DNS; lia|].
          apply Forall_forall. intros q Hq. rewrite <- MO1 in VSB.
          pose proof (proj1 (Forall_forall _ _) VSB q Hq) as D. cbv beta in D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
        * apply Forall_forall. intros q Hq. rewrite <- MO1 in VNB.
          pose proof (proj1 (Forall_forall _ _) VNB q Hq) as D. cbv beta in D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
      + unfold YK06.init_sp_ok in *. rewrite ISPF. exact MWSP.
    - intros q Hq. rewrite VMF in Hq. destruct Hq as [<-|[<-|Hq]]; [| |exact (MWPOS q Hq)];
        rewrite ?SSB0, ?SNB0; unfold kStoreBlockSize, kNodesBlockSize; lia. }
  { pose proof (ahs_hsub B lyW Sf (w_H W) (w_H W') memf WLE AHSS) as [AP AZ]. split.
    - intros a Ha NC HV. apply (AP a Ha); [intros C; apply NC; apply aclient_byte_grow; exact C | exact HV].
    - intros g Hg Happ HF. apply AZ; [exact Hg | exact Happ |].
      apply (hfree_grow lyW nb sb WNB WSB NZ SZ Sf g); [unfold in_app in Happ; lia | exact HF]. }
Qed.

(* ===== first_malloc_AR_sec: first_malloc_AR at a final layout lyF that differs
   from ly' at most in ly_sec (the secondary malloc's set_ly_sec ly' r mb, AFjy; ly_core premise by eq_refl). Every
   other premise is first_malloc_AR's, verbatim. The Put's facts at ly' move to lyF through ly_core (NB / SB fields,
   layout_ok, the depot cells, which name no secondary slot); the rest is first_malloc_AR's proof at lyF. ===== *)
Lemma first_malloc_AR_sec : forall (B : asyms) (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (tr : list Z) (ly' : alayout) (W' : world tfibsegs) (md' : Model)
    (c' : config) (Sf : astate) (Wf : world tfibsegs) (memf : word -> option byte) (mdf : Model) (lyF : alayout),
  WireSyms B -> st_depot S = [] -> ly_NB ly = 0 -> layout_ok ly -> img_cover ly ->
  put_effect ly W md ly' W' md' -> depot_first_put_post B W ly S regs mem md tr ly' W' md' c' ->
  ly_core lyF = ly_core ly' ->
  AR_but_depot B lyF Sf Wf memf mdf ->
  st_depot Sf = st_depot (depot_after 1 tr S) ->
  (forall a : word, ((tfib_dzone_lo <= bv_unsigned a < tfib_dzone_hi) \/
                     (fst (nb_ext ly') <= bv_unsigned a < fst (nb_ext ly') + snd (nb_ext ly')) \/
                     (fst (sb_ext ly') <= bv_unsigned a < fst (sb_ext ly') + snd (sb_ext ly'))) ->
     memf a = ms_mem (cfg_ms c') a /\ w_H Wf a = w_H W' a) ->
  (forall e, In e (vm_maps (m_vmmaps md')) -> In e (vm_maps (m_vmmaps mdf))) ->
  (forall e, In e (m_vm_lazy md') -> In e (m_vm_lazy mdf)) ->
  AR tfibsegs B lyF Sf Wf memf mdf /\
  am_depot_mono_kd B lyF (aview tfibsegs (w_H Wf) memf) Sf /\ am_alloc_depot_kd B lyF (aview tfibsegs (w_H Wf) memf) Sf.
Proof using kd_grow_NB kd_grow_SB kd_grow_trans depot_ok_pre_kd depot_ok_post_kd as_const_g2_def
  am_depot_mono_kd_intro am_alloc_depot_kd_intro.
  intros B W ly S regs mem md tr ly' W' md' c' Sf Wf memf mdf lyF HB ES HNB0 LY IMG PE POST EC ABD ESf FR MM _.
  pose proof (first_put_layout B W ly S regs mem md tr ly' W' md' c' LY IMG PE POST) as [LY' _].
  pose proof (ly_core_layout_ok lyF ly' EC LY') as LYF.
  assert (ENB : ly_NB lyF = ly_NB ly') by exact (f_equal ly_NB EC).
  assert (ESB : ly_SB lyF = ly_SB ly') by exact (f_equal ly_SB EC).
  unfold depot_first_put_post in POST. cbv zeta in POST.
  destruct POST as (regs' & mem' & Ec' & _ & _ & _ & _ & _ & _ & FACTS & ALLOC & _ & _ & IA1 & _ & IA2 & _).
  assert (ES' : st_depot (depot_after 1 tr S) = [tr]) by (unfold depot_after; simpl; rewrite ES; reflexivity).
  assert (ESf' : st_depot Sf = [tr]) by (rewrite ESf; exact ES').
  assert (NE : st_depot Sf <> []) by (rewrite ESf'; discriminate).
  pose proof FACTS as (HN & HS & _).
  assert (EM : ms_mem (cfg_ms c') = mem') by (rewrite Ec'; reflexivity). rewrite EM in FR.
  pose proof (kd_frame_agree ly' (w_H Wf) (w_H W') memf mem' HN HS IA1 IA2 FR) as AG. clear FR.
  pose proof (kd_facts_xfer B ly' (depot_after 1 tr S) tr _ _ HB ES' AG FACTS) as FACTSf.
  assert (ALLOCf : cell_holds B ly' (aview tfibsegs (w_H Wf) memf) (z8 (AStore ss_alloc) kStoreBlockSize)).
  { apply (cell_agree B ly' (aview tfibsegs (w_H W') mem')); [|exact ALLOC]. intros k Hk. apply AG. left.
    cbn [c_at c_w aeval z8 c8] in Hk |- *. rewrite (ts_store B HB).
    unfold TFIB_STORE, ss_alloc, tfib_dzone_lo, tfib_dzone_hi. cbn in Hk. lia. }
  clear FACTS ALLOC AG.
  destruct FACTSf as (_ & _ & DCf & HTf & N1f & L1f & AVf).
  assert (VN : range_vis B ly' (aview tfibsegs (w_H Wf) memf) (ANB 0, kNodesBlockSize)).
  { apply (proj1 (Forall_forall _ _) AVf). unfold depot_junk_kd, aareas_depot_kd. rewrite ES'. cbn [In app].
    do 3 right. left. reflexivity. }
  assert (VS : range_vis B ly' (aview tfibsegs (w_H Wf) memf) (ASB 0, kStoreBlockSize)).
  { apply (proj1 (Forall_forall _ _) AVf). unfold depot_junk_kd, aareas_depot_kd. rewrite ES'. cbn [In app].
    do 4 right. left. reflexivity. }
  destruct (kd_put_maps ly W md ly' W' md' HNB0 HN PE) as [M1 M2]. apply MM in M1, M2.
  (* the Put's facts at lyF *)
  assert (HNF : ly_NB lyF <> 0) by (rewrite ENB; exact HN).
  assert (HSF : ly_SB lyF <> 0) by (rewrite ESB; exact HS).
  assert (IA1F : in_app (ly_NB lyF) kNodesBlockSize) by (rewrite ENB; exact IA1).
  assert (IA2F : in_app (ly_SB lyF) kStoreBlockSize) by (rewrite ESB; exact IA2).
  assert (ALLOCF : cell_holds B lyF (aview tfibsegs (w_H Wf) memf) (z8 (AStore ss_alloc) kStoreBlockSize))
    by exact ALLOCf.
  assert (DCF : Forall (cell_holds B lyF (aview tfibsegs (w_H Wf) memf)) (depot_cells_kd (depot_after 1 tr S))).
  { apply (Forall_cell_holds_ly_core B ly' lyF _ _ (eq_sym EC)); [| exact DCf].
    unfold depot_cells_kd. rewrite ES'. reflexivity. }
  assert (N1F := N1f). rewrite <- ENB in N1F. assert (L1F := L1f). rewrite <- ENB in L1F.
  assert (VNF : range_vis B lyF (aview tfibsegs (w_H Wf) memf) (ANB 0, kNodesBlockSize)).
  { intros i Hi. specialize (VN i Hi). cbn [aeval fst snd] in VN |- *. rewrite ENB. exact VN. }
  assert (VSF : range_vis B lyF (aview tfibsegs (w_H Wf) memf) (ASB 0, kStoreBlockSize)).
  { intros i Hi. specialize (VS i Hi). cbn [aeval fst snd] in VS |- *. rewrite ESB. exact VS. }
  rewrite <- ENB in M1. rewrite <- ESB in M2.
  clear ALLOCf DCf N1f L1f VN VS IA1 IA2.
  assert (EX : (if ly_NB lyF =? 0 then [] else [wiv (ly_NB lyF, kNodesBlockSize)]) ++
               (if ly_SB lyF =? 0 then [] else [wiv (ly_SB lyF, kStoreBlockSize)]) =
               [wiv (ly_NB lyF, kNodesBlockSize); wiv (ly_SB lyF, kStoreBlockSize)])
    by (rewrite (proj2 (Z.eqb_neq _ 0) HNF), (proj2 (Z.eqb_neq _ 0) HSF); reflexivity).
  unfold AR_but_depot in ABD. cbv zeta in ABD. rewrite EX in ABD.
  destruct ABD as (WF & UN & SY & PL & CG2 & CO & CE & FA & FL & SH & ZS & JK & AA & CL & ZR & TSD & SI &
                   AIMG & ALIM & ARES & APRIM & AQ & AHS & ASEC & ACOV & AEX & APERM & ABAND & ASECX & ATOP & AIMGCOV &
                   ASHNA & ABUD & AMWF & AHSS).
  split; [|split].
  - unfold AR. split; [|split; [|split; [|split]]].
    + constructor.
      * exact WF.
      * exact UN.
      * exact SY.
      * exact LYF.
      * exact PL.
      * exact (kd_const B lyF _ HB CG2 ALLOCF).
      * exact CO.
      * exact (kd_cells B lyF Sf (depot_after 1 tr S) _ ESf DCF CE).
      * exact FA.
      * exact FL.
      * exact (kd_depot_ok B lyF Sf tr _ ESf' HNF HSF HTf N1F L1F).
      * exact SH.
      * exact ZS.
      * exact JK.
      * exact (kd_areas B lyF Sf _ NE VNF VSF AA).
      * exact CL.
      * exact ZR.
      * exact TSD.
      * exact SI.
    + constructor.
      * exact AIMG.
      * exact ALIM.
      * exact ARES.
      * exact APRIM.
      * exact AQ.
      * exact AHS.
      * exact ASEC.
      * exact (kd_cover lyF Sf mdf HNF HSF IA1F IA2F ACOV).
      * exact AEX.
      * exact (kd_perm lyF mdf M1 M2 APERM).
      * exact ABAND.
      * exact ASECX.
      * exact ATOP.
      * exact AIMGCOV.
      * exact ASHNA.
    + exact ABUD.
    + exact AMWF.
    + exact AHSS.
  - exact (am_depot_mono_kd_intro B lyF _ Sf HNF HSF NE).
  - exact (am_alloc_depot_kd_intro B lyF _ Sf NE ALLOCF).
Qed.

(* 'empty -> post-Put depot_ok': from an empty depot, the first Put's facts give the post-Put depot_ok (by YG0r.v:68-83 they are
   init_facts' one-trace depot fields with ly_tr0 := tr, so the proof is the one-trace depot_init, YG0r.v:212-226, true branch:
   heads := fun b => if b =? b1 then 1 else 0, links := fun _ => 0). *)
Lemma depot_ok_first_put : forall B ly' rd' S tr,
  st_depot S = [] -> depot_first_put_facts B ly' (depot_after 1 tr S) tr rd' ->
  depot_ok_kd B ly' rd' (depot_after 1 tr S).
Proof using depot_ok_post_kd.
  intros B ly' rd' S tr E (HN & HSb & _ & HT & N1 & L1 & _).
  assert (ES' : st_depot (depot_after 1 tr S) = [tr]) by (unfold depot_after; simpl; rewrite E; reflexivity).
  apply (proj2 (depot_ok_post_kd B ly' rd' (depot_after 1 tr S) ltac:(rewrite ES'; discriminate))).
  unfold depot_ok_post_text. rewrite ES'.
  split; [exact HN|]. split; [exact HSb|].
  exists (fun b => if b =? (as_dhash B tr mod 2 ^ 64) mod d_tab_words then 1 else 0), (fun _ => 0).
  cbn zeta. split; [| split].
  - intros b Hb. split; [destruct (b =? _); cbn; lia | exact (HT b Hb)].
  - intros id Hid. assert (Eid : id = 1) by (cbn in Hid; lia). subst id.
    split; [lia|]. split.
    + replace (ly_NB ly' + 16 * 1) with (ly_NB ly' + 16) by lia. exact N1.
    + replace (ly_NB ly' + 16 * 1 + 8) with (ly_NB ly' + 24) by lia. exact L1.
  - intros id Hid. assert (Eid : id = 1) by (cbn in Hid; lia). subst id.
    cbn. rewrite Z.eqb_refl. cbn. split; [discriminate | left; reflexivity].
Qed.

Theorem tfib_depot_first_put_ok : forall B, WireSyms B -> (forall t, as_dhash B t = YF0p.tfib_dhash t) ->
  tfib_depot_first_put_spec B.
Proof using kd_grow_NB kd_grow_SB kd_grow_trans depot_ok_pre_kd depot_ok_post_kd as_const_g2_def.
  clear am_depot_mono_kd_intro am_alloc_depot_kd_intro am_depot_mono_kd am_alloc_depot_kd.
  intros B HB HDH W ly S regs mem md buf tr. cbv zeta.
  intros ES DK DC PZ HC IMG PD TCD WF Htr Htr1 RM IVS CT TK TCL TI R10 R11 Hra Hw Hb8 Hblo Hbhi Hbsp Hsp16 HM1 HM2
    Hslo Hshi Pstk.
  (* ---- entry facts ---- *)
  pose proof (ts_depot B HB) as ED. pose proof (ts_store B HB) as ESS.
  pose proof (proj1 (depot_ok_pre_kd B ly _ S ES) DK) as (_ & HTAB & HLY & _).
  destruct (proj1 HLY ES) as [NB0 SB0].
  destruct (b2_depot_cells B ly (w_H W) mem S ES DC) as (NUQ0 & MAP0 & TOT0 & BLK0).
  destruct (b2_zero_cells B ly (w_H W) mem PZ) as (MU0 & STD0 & MTX0).
  pose proof (b2_mod_cells B ly (w_H W) mem HB HC) as MODC.
  assert (ALC0 : val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_STORE + ss_alloc) 8 0).
  { pose proof DC as DC'. unfold depot_cells_kd in DC'. rewrite ES in DC'.
    pose proof (proj1 (Forall_forall _ _) DC' (z8 (AStore s_alloc) 0) ltac:(cbn [In]; tauto)) as A.
    rewrite <- ESS. exact (AF0x.cell_holds_val_mem B ly (w_H W) mem (AStore s_alloc) 8 (ANum 0) A). }
  assert (TL : (length tr <= 30)%nat)
    by (pose proof (ts_universe B HB) as (_ & HU & _); exact (proj1 (Forall_forall _ _) HU tr Htr)).
  assert (TRNE : tr <> []) by (intros E; subst tr; cbn in Htr1; lia).
  pose proof (u64_range (getr regs 2)) as SPRg. fold (spZ regs) in SPRg.
  set (b1 := (YF0p.tfib_dhash tr mod 2 ^ 64) mod d_tab_words).
  assert (BR : 0 <= b1 < 2 ^ 20) by (unfold b1, d_tab_words; apply Z.mod_pos_bound; lia).
  assert (Z0 : b2_zone0 (spZ regs) (ly_stk_lo ly) (ly_stk_hi ly) buf b1 (Z.of_nat (length tr))).
  { unfold b2_zone0. clear - HM1 Hslo Hshi HM2 Hsp16 Hblo Hbhi Hbsp BR Htr1 TL. repeat split; try assumption; lia. }
  (* ---- K1: 0x70ef0 -> TwoLevelMap::Create ---- *)
  apply (AD3k.put_to_create B HB W regs mem md ly buf tr _ R10 R11 Hra Hw Hb8 Hblo Hbhi Hbsp Hsp16 HM1 HM2 Hslo Hshi Pstk
           Htr TRNE HTAB NUQ0 MAP0 HC).
  intros regs1 mem1 mat1 AC. unfold AD3k.at_create_call in AC. cbv zeta in AC. fold b1 in AC.
  destruct AC as (A1 & A2 & A10 & A11 & A8 & A9 & ACS & APF & ATAB & ANUQ & AW & AFR & APR).
  assert (SP1 : spZ regs1 = spZ regs - 112)
    by (unfold spZ at 1; rewrite A2; apply YP03.unsigned_lit_small; clear - Z0 SPRg; b2z).
  assert (KP1 : kept (fun a => (spZ regs - DEP_STK <= a < spZ regs) \/ (as_depot B + 4 * b1 <= a < as_depot B + 4 * b1 + 4) \/
                  (as_depot B + d_nuniq <= a < as_depot B + d_nuniq + 4)) (w_H W) mem (w_H W) mem1).
  { intros w Hw'. split; [reflexivity|]. apply AFR; intros X; apply Hw'; tauto. }
  (* ---- S7: TwoLevelMap::Create (the nodes block) ---- *)
  set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
  eapply SRr_bind.
  { apply (tfib_tlm_create_nb_ok layout_grow_kd kd_grow_NB B HB W ly S regs1 mem1 md1).
    - exact NB0.
    - exact A10.
    - exact A11.
    - rewrite A1. vm_compute. reflexivity.
    - apply (kept_val _ _ _ _ _ _ _ _ KP1); [b2z | b2z | intros k Hk; b2z | exact MAP0].
    - apply (kept_val _ _ _ _ _ _ _ _ KP1); [b2z | b2z | intros k Hk; b2z | exact MU0].
    - exact (proj1 (b2_mod_cells_kept _ _ _ _ _ KP1 ltac:(intros a Ha; b2z) MODC)).
    - exact (AD3g.mod_room_wvb W md mat1 kNodesBlockSize (proj1 RM)).
    - rewrite SP1. b2z.
    - exact HM1.
    - rewrite SP1. b2z.
    - rewrite SP1. b2z.
    - intros a Ha. rewrite SP1 in Ha. apply APR. apply Pstk. b2z.
    - unfold first_put_avoid in TK. eapply Forall_impl; [| exact TK]. intros e He. exact (proj2 (AD3g.md_takes_wvb _ _ _ _) He).
    - intros a Ha. exact (proj2 (AD3g.md_takes_wvb _ _ _ _) (TCL a Ha)).
    - exact (proj2 (AD3g.md_takes_wvb _ _ _ _) TI).
    - exact CT. }
  intros W1 c1 LE1 P7. destruct P7 as (x & regs2 & mem2 & md2 & P7). cbv zeta in P7.
  destruct P7 as (Hc1 & WA1 & WH1 & X10 & RP1 & XMAP & XPA & XIA & XP3 & XP3c & XP4 & XTK & XTKK & XVM & XLZ & XFR & XMU
    & XPR & XIO & XLG & XVF).
  subst c1. rewrite A1.
  assert (XSTK := proj1 (Forall_forall _ _) XP3 (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)
    ltac:(unfold ext_but_NB; rewrite SB0; cbn; tauto)).
  assert (XIM := proj1 (Forall_forall _ _) XP3 (ly_img ly) ltac:(unfold ext_but_NB; rewrite SB0; cbn; tauto)).
  assert (ZX : b2_zoneX (ly_stk_lo ly) (ly_stk_hi ly) x).
  { pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold b2_zoneX.
    clear - XSTK XIM XIA IMG CR. unfold zdisjoint, in_app, img_cover in *. cbn [fst snd] in *.
    unfold TFIB_IMG_LO, TFIB_IMG_END, kNodesBlockSize, kLowShadowBeg, kHighMemBeg in *. lia. }
  assert (XNZ : x <> 0) by b2z.
  assert (KP2 : kept (fun a => (spZ regs1 - TLM_STK <= a < spZ regs1) \/ (x <= a < x + kNodesBlockSize) \/
                  (as_depot B + d_map1 <= a < as_depot B + d_map1 + 8) \/ (as_depot B + tlm_mu <= a < as_depot B + tlm_mu + 4))
                (w_H W) mem1 (w_H W1) mem2).
  { intros w Hw'. split.
    - apply WH1. intros X. apply Hw'. tauto.
    - apply XFR; intros X; apply Hw'; tauto. }
  (* ---- K2: Create's return -> StackStore::Store ---- *)
  apply (AD3k.create_ret_to_store B HB W1 regs regs2 mem2 md2 buf x tr _).
  - rpw RP1 (2%bv : bv 5) 2. exact A2.
  - exact X10.
  - rpw RP1 (8%bv : bv 5) 8. exact A8.
  - rpw RP1 (9%bv : bv 5) 9. exact A9.
  - exact (b2_put_cs_pres B regs1 regs2 regs tr RP1 ACS).
  - apply (b2_put_frame_kept _ _ _ _ _ regs buf tr KP2); [b2z | intros a Ha; b2z | exact APF].
  - exact Hsp16.
  - b2z.
  - b2z.
  - intros a Ha. apply XPR, APR, Pstk. exact Ha.
  - exact XIA.
  - b2z.
  - b2z.
  - intros i Hi. exact (proj1 (XP4 i ltac:(unfold kNodesBlockSize; lia))).
  - intros regs3 mem3 mat3 AS. unfold AD3k.at_store_call in AS. cbv zeta in AS.
    destruct AS as (S1r & S2r & S10 & S11 & S12 & S8 & S9 & SCS & V18 & V10 & V08 & SPF & SHH & SFR & SPR).
    assert (SP3 : spZ regs3 = spZ regs - 144)
      by (unfold spZ at 1; rewrite S2r; rewrite YP03.unsigned_lit_small by (clear - Z0 SPRg; b2z); lia).
    assert (KP3 : kept (fun a => (spZ regs - DEP_STK <= a < spZ regs) \/ (x + 16 <= a < x + 24)) (w_H W1) mem2 (w_H W1) mem3).
    { intros w Hw'. split; [reflexivity|]. apply SFR; intros X; apply Hw'; tauto. }
    pose proof (kept_trans _ _ _ _ _ _ _ _ (kept_trans _ _ _ _ _ _ _ _ KP1 KP2) KP3) as KP13.
    pose proof (kept_trans _ _ _ _ _ _ _ _ KP2 KP3) as KP23.
    unfold AD3k.put_frame in SPF. cbv zeta in SPF. destruct SPF as (SPS & SPB & SPN).
    pose proof (val_mem_split4 _ _ (Z.of_nat (length tr)) ltac:(clear - Z0; b2z) SPN) as (SPN4 & SPT4).
    set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2).
    assert (MV3 : m_vmmaps md3 = m_vmmaps (mmap_model (Z_to_bv 64 x) (Z_to_bv 64 kNodesBlockSize) md)).
    { unfold md3. rewrite AD3g.wvb_vmmaps, XVM. apply mmap_model_vmmaps_eq. unfold md1. apply AD3g.wvb_vmmaps. }
    assert (ML3 : m_vm_lazy md3 = m_vm_lazy md).
    { unfold md3. rewrite AD3g.wvb_lazy, XLZ. unfold md1. apply AD3g.wvb_lazy. }
    destruct (b2_mmap_vm (Z_to_bv 64 x) (Z_to_bv 64 kNodesBlockSize) md) as (VL & VR & VT' & VMP & VLZ).
    assert (NBU : bv_unsigned (Z_to_bv 64 kNodesBlockSize) = kNodesBlockSize)
      by (apply YP03.unsigned_lit_small; unfold kNodesBlockSize; lia).
    assert (EU3 : eager_used md3 <= eager_used md + kNodesBlockSize).
    { rewrite (b2_eager_eq md3 (mmap_model (Z_to_bv 64 x) (Z_to_bv 64 kNodesBlockSize) md) MV3 ltac:(rewrite ML3, VLZ; reflexivity)).
      pose proof (mod_eager_used_mmap_le (Z_to_bv 64 x) (Z_to_bv 64 kNodesBlockSize) md) as LE. rewrite NBU in LE. exact LE. }
    assert (WA3 : A_bytes (w_A W1) <= A_bytes (w_A W) + kNodesBlockSize) by (rewrite WA1; cbn [A_bytes fst snd]; lia).
    destruct RM as (RM1 & RM2 & RM3).
    pose proof (RM3 (Z_to_bv 64 x) (Z_to_bv 64 kNodesBlockSize) md3 W1 NBU ltac:(rewrite MV3; exact VL)
      ltac:(rewrite MV3; exact VR) ltac:(rewrite MV3, VT'; lia)
      ltac:(intros e He; rewrite MV3, VMP in He; destruct He as [<-|He]; [left; reflexivity | right; exact He]) EU3 WA3)
      as (ROOM3 & BUD3).
    assert (IVS3 : YK0g.ivs_wf (vm_maps (m_vmmaps md3))).
    { rewrite MV3, VMP. apply YK0g.ivs_wf_cons; [| exact IVS]. unfold YK0g.iv_wf, YK0g.B, YK0g.S. cbn [fst snd].
      rewrite NBU, YP03.unsigned_lit_small by (clear - ZX; b2z). clear - ZX; b2z. }
    assert (CT3 : YM05.ceil_of_top (alloc_top (m_vmmaps md3))) by (rewrite MV3, VT'; exact CT).
    assert (TKM3 : forall e, md_takes md e -> md_takes md3 e).
    { intros e He. apply (proj2 (AD3g.md_takes_wvb _ _ _ _)). apply XTKK. exact (proj2 (AD3g.md_takes_wvb _ _ _ _) He). }
    assert (TKX3 : md_takes md3 (x, kNodesBlockSize)) by exact (proj2 (AD3g.md_takes_wvb _ _ _ _) XTK).
    assert (LY1lo : ly_stk_lo (set_ly_NB ly x) = ly_stk_lo ly) by reflexivity.
    assert (LY1hi : ly_stk_hi (set_ly_NB ly x) = ly_stk_hi ly) by reflexivity.
    (* ---- S1: StackStore::Store (the store block, through Alloc and BlockInfo::Create) ---- *)
    eapply SRr_bind.
    { apply AD3d.SRr_refusable_SRr.
      apply (AD3a.tfib_store_ok layout_grow_kd B HB
               (AD3b.tfib_alloc_ok layout_grow_kd B HB (tfib_blockinfo_create_ok layout_grow_kd kd_grow_SB B HB))
               W1 (set_ly_NB ly x) S regs3 mem3 md3 (spZ regs - 112 + 8) buf (spZ regs - 112 - 32 + 8) 0 0 0 tr).
      - exact S10.
      - exact S11.
      - exact S12.
      - rewrite S1r. vm_compute. reflexivity.
      - exact SPB.
      - replace (spZ regs - 112 + 8 + 8) with (spZ regs - 112 + 16) by lia. exact SPN4.
      - replace (spZ regs - 112 + 8 + 12) with (spZ regs - 112 + 16 + 4) by lia. exact SPT4.
      - clear - Z0. b2z.
      - intros i Hi. apply (kept_val _ _ _ _ _ _ _ _ KP23); [b2z | b2z | intros k Hk; b2z | exact (AW i Hi)].
      - lia.
      - exact (AD3i.depot_store_one_block B S tr 0 HB WF Htr ltac:(unfold depot_frames; rewrite ES; cbn; lia)).
      - lia.
      - clear - Z0. b2z.
      - apply (kept_val _ _ _ _ _ _ _ _ KP13); [b2z | b2z | intros k Hk; b2z | exact TOT0].
      - change (ly_SB (set_ly_NB ly x)) with (ly_SB ly). rewrite SB0.
        apply (kept_val _ _ _ _ _ _ _ _ KP13); [b2z | b2z | intros k Hk; b2z | exact BLK0].
      - change (ly_SB (set_ly_NB ly x)) with (ly_SB ly). rewrite SB0. lia.
      - apply (kept_val _ _ _ _ _ _ _ _ KP13); [b2z | b2z | intros k Hk; b2z | exact STD0].
      - intros _.
        split; [apply (kept_val _ _ _ _ _ _ _ _ KP13); [b2z | b2z | intros k Hk; b2z | exact MTX0]|].
        split; [rewrite ESS; apply (kept_val _ _ _ _ _ _ _ _ KP13); [b2z | b2z | intros k Hk; b2z | exact ALC0]|].
        split; [exact (proj2 (b2_mod_cells_kept _ _ _ _ _ KP13 ltac:(intros a Ha; b2z) MODC))|].
        split; [exact ROOM3|]. split; [exact BUD3|]. split; [exact IVS3|]. split; [exact CT3|].
        split.
        { unfold mnr_cell_extents, MNR_CF_GOT, MNR_CF. apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]];
            (apply (md_takes_sub md3 TFIB_IMG_LO (TFIB_IMG_END - TFIB_IMG_LO)); [exact (TKM3 _ TI) | b2z | b2z | b2z]). }
        split.
        { rewrite ESS. apply (md_takes_sub md3 TFIB_IMG_LO (TFIB_IMG_END - TFIB_IMG_LO)); [exact (TKM3 _ TI) | b2z | b2z | b2z]. }
        split.
        { apply Forall_forall. intros e He. apply in_app_iff in He as [He|He].
          - destruct (b2_ext_SB_NB ly x e SB0 He) as [->|He']; [exact TKX3|].
            apply TKM3. apply (proj1 (Forall_forall _ _) TK). unfold first_put_avoid. apply in_app_iff. left. exact He'.
          - apply TKM3. apply (proj1 (Forall_forall _ _) TK). unfold first_put_avoid. apply in_app_iff. right. exact He. }
        intros a Ha. apply TKM3. apply TCL. exact (proj1 (b2_aclient_NB B ly x S a) Ha).
      - intros X. exfalso. exact (X SB0).
      - intros k Hk. apply SPR, XPR, APR, Pstk. b2z.
      - b2z.
      - b2z.
      - rewrite SP3. b2z.
      - b2z.
      - b2z.
      - rewrite SP3. b2z.
      - b2z.
      - b2z.
      - rewrite SP3. b2z.
      - unfold zdisjoint. cbn [fst snd]. b2z.
      - unfold zdisjoint. cbn [fst snd]. b2z.
      - rewrite SP3. b2z.
      - exact HM1.
      - exact HM2.
      - rewrite SP3. b2z.
      - rewrite SP3. b2z.
      - intros a Ha. rewrite SP3 in Ha. apply SPR, XPR, APR, Pstk. b2z. }
    intros W2 c2 LE2 P1. destruct P1 as (sx & ly2 & regs4 & mem4 & md4 & Hc2 & SE). subst c2. rewrite S1r.
    unfold AD3a.store_exit in SE. cbv zeta in SE.
    destruct SE as (T10 & RP2 & VT & VB & VS & VPK & VH & VW & PR4 & [ARM | (NZ & _)]); [| exfalso; exact (NZ SB0)].
    destruct ARM as (_ & SPA & SIA & SP3s & SP3c & SP4 & WA2 & WH2 & IO2 & STK & STKK & _ & SVM & SLZ & _ & SALC & SMTX
      & SFR4 & EL2 & SLG & SVF).
    assert (SSTK := proj1 (Forall_forall _ _) SP3s (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)
      ltac:(apply in_app_iff; left; apply (b2_ext_NB_SB ly x _ SB0); unfold ext_but_NB; rewrite SB0; cbn; tauto)).
    assert (SIM := proj1 (Forall_forall _ _) SP3s (ly_img ly)
      ltac:(apply in_app_iff; left; apply (b2_ext_NB_SB ly x _ SB0); unfold ext_but_NB; rewrite SB0; cbn; tauto)).
    assert (SXB := proj1 (Forall_forall _ _) SP3s (x, kNodesBlockSize) ltac:(apply in_app_iff; left; apply b2_ext_x; exact XNZ)).
    assert (ZY : b2_zoneY (ly_stk_lo ly) (ly_stk_hi ly) x sx).
    { pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold b2_zoneY. clear - SSTK SIM SXB SIA IMG CR.
      unfold zdisjoint, in_app, img_cover in *. cbn [fst snd set_ly_NB ly_stk_lo ly_stk_hi] in *.
      unfold TFIB_IMG_LO, TFIB_IMG_END, kNodesBlockSize, kStoreBlockSize, kLowShadowBeg, kHighMemBeg in *. lia. }
    assert (SXNZ : sx <> 0) by b2z.
    assert (KP4 : kept (fun a => (spZ regs3 - (64 + 16 + BIC_STK) <= a < spZ regs3) \/ (sx <= a < sx + kStoreBlockSize) \/
                    (as_store B <= a < as_store B + 32) \/ (spZ regs - 112 - 32 + 8 <= a < spZ regs - 112 - 32 + 8 + 8))
                  (w_H W1) mem3 (w_H W2) mem4).
    { intros w Hw'. split; [apply WH2; intros X; apply Hw'; tauto | apply SFR4; intros X; apply Hw'; tauto]. }
    (* ---- K3: Store's return -> Put's return ---- *)
    apply (AD3k.store_ret_to_exit B HB W2 regs regs4 mem4 md4 x tr _).
    + rpw RP2 (2%bv : bv 5) 2. exact S2r.
    + exact T10.
    + rpw RP2 (8%bv : bv 5) 8. exact S8.
    + rpw RP2 (9%bv : bv 5) 9. exact S9.
    + exact (b2_put_cs_pres B regs3 regs4 regs tr RP2 SCS).
    + exact Hra.
    + apply (kept_val _ _ _ _ _ _ _ _ KP4); [b2z | b2z | intros k Hk; b2z | exact V18].
    + apply (kept_val _ _ _ _ _ _ _ _ KP4); [b2z | b2z | intros k Hk; b2z | exact V10].
    + exact VPK.
    + apply (b2_put_saved_kept _ _ _ _ _ regs KP4); [b2z | intros a Ha; b2z | exact SPS].
    + exact Hsp16.
    + b2z.
    + b2z.
    + exact XIA.
    + b2z.
    + b2z.
    + intros i Hi. apply PR4, SPR. exact (proj1 (XP4 i ltac:(unfold kNodesBlockSize; lia))).
    + intros regs5 mem5 mat5 PX. unfold AD3k.put_exit in PX. cbv zeta in PX. fold b1 in PX.
      destruct PX as (Y10 & RP5 & Y28 & Y24 & YS2 & YFR & YPR).
      assert (KP5 : kept (fun a => (x + 24 <= a < x + 32) \/ (as_depot B + 4 * b1 <= a < as_depot B + 4 * b1 + 4))
                    (w_H W2) mem4 (w_H W2) mem5).
      { intros w Hw'. split; [reflexivity | apply YFR; intros X; apply Hw'; tauto]. }
      pose proof (kept_trans _ _ _ _ _ _ _ _ KP4 KP5) as KP45.
      pose proof (kept_trans _ _ _ _ _ _ _ _ KP3 KP45) as KP35.
      pose proof (kept_trans _ _ _ _ _ _ _ _ KP2 KP35) as KP25.
      pose proof (kept_trans _ _ _ _ _ _ _ _ KP1 KP25) as KP15.
      assert (PRall : forall a, apresent (w_H W) mem a -> apresent (w_H W2) mem5 a)
        by (intros a Pa; exact (YPR a (PR4 a (SPR a (XPR a (APR a Pa)))))).
      assert (DX : Forall (zdisjoint (x, kNodesBlockSize)) (ext_but_NB ly)).
      { apply Forall_forall. intros e He. apply (proj1 (Forall_forall _ _) XP3). apply in_app_iff. left. exact He. }
      assert (DSX : Forall (zdisjoint (sx, kStoreBlockSize)) (ext_but_NB ly)).
      { apply Forall_forall. intros e He. apply (proj1 (Forall_forall _ _) SP3s). apply in_app_iff. left.
        exact (b2_ext_NB_SB ly x e SB0 He). }
      assert (ES' : st_depot (depot_after 1 tr S) = [tr]) by (unfold depot_after; simpl; rewrite ES; reflexivity).
      apply SRr_ret. subst ly2.
      set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4).
      exists (set_ly_SB (set_ly_NB ly x) sx), md5. split.
      { (* put_effect, right arm *)
        right. exists x, sx.
        split; [exact NB0|]. split; [exact SB0|]. split; [exact XNZ|]. split; [exact SXNZ|]. split; [reflexivity|].
        split; [exact (kd_grow_trans _ _ _ XLG SLG)|].
        split; [rewrite WA2, WA1; reflexivity|].
        split; [intros a N1 N2; rewrite (WH2 a N2); exact (WH1 a N1)|].
        split.
        { apply (same_io_trans3 _ md1); [exact (AD3g.same_io_wvb _ _ _)|].
          apply (same_io_trans3 _ md2); [exact XIO|].
          apply (same_io_trans3 _ md3); [exact (AD3g.same_io_wvb _ _ _)|].
          apply (same_io_trans3 _ md4); [exact IO2|].
          exact (AD3g.same_io_wvb _ _ _). }
        split.
        { unfold md5. rewrite AD3g.wvb_vmmaps, SVM. apply mmap_model_vmmaps_eq. exact MV3. }
        unfold md5. rewrite AD3g.wvb_lazy, SLZ, ML3. reflexivity. }
      (* depot_first_put_post *)
      exists regs5, mem5. cbv zeta.
      assert (ALLOC5 : cell_holds B (set_ly_SB (set_ly_NB ly x) sx) (aview tfibsegs (w_H W2) mem5)
                         (z8 (AStore ss_alloc) kStoreBlockSize)).
      { apply cell_of_val. cbn [aeval].
        replace ((0 + kStoreBlockSize) mod 2 ^ 64) with kStoreBlockSize in SALC by (unfold kStoreBlockSize; reflexivity).
        apply (kept_val _ _ _ _ _ _ _ _ KP5); [b2z | b2z | intros k Hk; b2z | exact SALC]. }
      assert (FACTS : depot_first_put_facts B (set_ly_SB (set_ly_NB ly x) sx) (depot_after 1 tr S) tr
                        (aview tfibsegs (w_H W2) mem5)).
      { unfold depot_first_put_facts. cbv zeta. rewrite HDH. fold b1.
        split; [exact XNZ|]. split; [exact SXNZ|].
        split.
        { unfold depot_cells_kd, depot_ids. rewrite ES'.
          apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [|
            apply Forall_nil]]]]].
          - apply cell_of_val. cbn [aeval]. change (Z.of_nat (length [tr])) with 1.
            apply (kept_val _ _ _ _ _ _ _ _ KP25); [b2z | b2z | intros k Hk; b2z | exact ANUQ].
          - apply cell_of_val. cbn [aeval set_ly_SB set_ly_NB ly_NB]. rewrite Z.add_0_r.
            apply (kept_val _ _ _ _ _ _ _ _ KP35); [b2z | b2z | intros k Hk; b2z | exact XMAP].
          - apply cell_of_val. cbn [aeval].
            replace (depot_frames (depot_after 1 tr S)) with (0 + Z.of_nat (length tr) + 1)
              by (unfold depot_frames; rewrite ES'; cbn [fold_right]; lia).
            apply (kept_val _ _ _ _ _ _ _ _ KP5); [b2z | b2z | intros k Hk; b2z | exact VT].
          - apply cell_of_val. cbn [aeval set_ly_SB set_ly_NB ly_SB]. rewrite Z.add_0_r.
            apply (kept_val _ _ _ _ _ _ _ _ KP5); [b2z | b2z | intros k Hk; b2z | exact VB].
          - exact ALLOC5. }
        split.
        { intros b Hb. destruct (Z.eqb_spec b b1) as [->|Nb].
          - apply rd32_of_val. exact YS2.
          - intros k Hk. rewrite (kept_aview _ _ _ _ _ _ KP15). { exact (HTAB b Hb k Hk). }
            rewrite Z.mod_small by b2z. b2z. }
        split.
        { cbn [set_ly_SB set_ly_NB ly_NB]. apply rd64_of_val. apply AD3k.kval_mem_mod64.
          apply (kept_val _ _ _ _ _ _ _ _ KP45); [b2z | b2z | intros k Hk; b2z | exact SHH]. }
        split.
        { cbn [set_ly_SB set_ly_NB ly_NB]. apply rd32_of_val. exact Y24. }
        unfold depot_junk_kd, aareas_depot_kd. rewrite ES'. cbn [app].
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [|
          apply Forall_nil]]]]].
        - intros i Hi. cbn [aeval fst snd] in Hi |- *. apply img_vis. b2z.
        - intros i Hi. cbn [aeval fst snd] in Hi |- *. apply img_vis. b2z.
        - intros i Hi. cbn [aeval fst snd] in Hi |- *. apply img_vis. b2z.
        - intros i Hi. cbn [aeval fst snd set_ly_SB set_ly_NB ly_NB] in Hi |- *. apply apresent_vis.
          replace (x + 0 + i) with (x + i) by lia. apply YPR, PR4, SPR. exact (proj1 (XP4 i Hi)).
        - intros i Hi. cbn [aeval fst snd set_ly_SB set_ly_NB ly_SB] in Hi |- *. apply apresent_vis.
          replace (sx + 0 + i) with (sx + i) by lia. apply YPR. exact (proj1 (SP4 i Hi)). }
      split; [reflexivity|].
      split; [right; split; [reflexivity | rewrite ES; reflexivity]|].
      split; [exact Y10|]. split; [exact RP5|].
      split.
      { intros w N1 N2. refine (proj2 (KP15 w _)). intros HU. cbv beta in HU.
        unfold depot_footprint in N2. cbn [set_ly_SB set_ly_NB ly_NB ly_SB] in N2.
        clear - HU N1 N2 BR SP1 SP3 ED ESS.
        unfold tlm_mu, TLM_STK, BIC_STK, DEP_STK, MOD_STK, MNR_STK, kNodesBlockSize, kStoreBlockSize, d_map1, d_nuniq,
          TFIB_DEPOT, TFIB_STORE in *.
        destruct HU as [[H|[H|H]]|[[H|[H|[H|H]]]|[[H|H]|[[H|[H|[H|H]]]|[H|H]]]]];
          first [apply N1; lia | apply N2; first [left; lia | right; left; lia | right; right; left; lia | right; right; right; lia]]. }
      split; [exact PRall|].
      split.
      { apply Forall_forall. intros c Hc. apply as_const_g2_def in Hc as [Hc Hna].
        apply (b2_const_kept B ly x sx _ _ _ _ _ HB SB0 HC IMG PD TCD HM1 (proj1 ZX) (proj1 ZY) DX DSX KP15); [| exact Hc | exact Hna].
        intros a HU. cbv beta in HU. clear - HU Z0 BR SP1 SP3 ED ESS.
        unfold b2_zone0, tlm_mu, TLM_STK, BIC_STK, DEP_STK, MOD_STK, MNR_STK, kNodesBlockSize, kStoreBlockSize, d_map1, d_nuniq,
          TFIB_DEPOT, TFIB_STORE in *.
        destruct HU as [[H|[H|H]]|[[H|[H|[H|H]]]|[[H|H]|[[H|[H|[H|H]]]|[H|H]]]]];
          first [left; lia | right; left; lia | right; right; left; lia | right; right; right; left; lia | right; right; right; right; lia]. }
      split; [exact FACTS|].
      split; [exact ALLOC5|].
      split; [exact (depot_ok_first_put B _ _ S tr ES FACTS)|].
      split; [exact XPA|]. split; [exact XIA|]. split; [exact SPA|]. split; [exact SIA|].
      split; [clear - SXB; unfold zdisjoint in *; cbn [fst snd set_ly_SB set_ly_NB ly_NB ly_SB] in *; lia|].
      split; [exact XP3|].
      split.
      { apply Forall_forall. intros e He. unfold first_put_avoid in He. apply in_app_iff in He as [He|He].
        - apply (proj1 (Forall_forall _ _) SP3s). apply in_app_iff. left. exact (b2_ext_NB_SB ly x e SB0 He).
        - apply (proj1 (Forall_forall _ _) SP3s). apply in_app_iff. right. exact He. }
      split; [intros a Ha; split; [exact (XP3c a Ha) | exact (SP3c a (proj2 (b2_aclient_NB B ly x S a) Ha))]|].
      split; [unfold md5; apply (proj2 (AD3g.md_takes_wvb _ _ _ _)); apply STKK; exact TKX3|].
      split; [unfold md5; apply (proj2 (AD3g.md_takes_wvb _ _ _ _)); exact STK|].
      split; [intros e He; unfold md5; apply (proj2 (AD3g.md_takes_wvb _ _ _ _)); apply STKK; apply TKM3; exact He|].
      (* fresh against every map of md: NB from S7 at md1 (md's maps), SB from S1 at md3 ((x, NB) :: md's maps) *)
      split.
      { unfold md1 in XVF. rewrite AD3g.wvb_vmmaps in XVF. exact XVF. }
      rewrite MV3, VMP in SVF. apply Forall_cons_iff in SVF as [_ SVF]. exact SVF.
Qed.

Theorem tfib_depot_put_any : forall B, WireSyms B -> (forall t, as_dhash B t = YF0p.tfib_dhash t) ->
  tfib_depot_put_any_spec B.
Proof using kd_grow_NB kd_grow_SB kd_grow_trans depot_ok_pre_kd depot_ok_post_kd as_const_g2_def.
  intros B HB HDH W ly S regs mem md buf tr. cbv zeta.
  intros IMG WF Htr HC PE PN R10 R11 R3 R4 Hra Hw Hb8 Hblo Hbhi Hbsp Hsp16 Hslo Hshi Pstk.
  destruct (st_depot S) as [|t l] eqn:ES.
  - destruct (PE eq_refl) as (DK & DC & PZ & XD & XA & RM & IVS & CT & TK & TCL & TI & HM1 & HM2).
    destruct tr as [|w tr'] eqn:ETR.
    + eapply SRr_mono.
      * exact (depot_put_early_ok B HB W ly S regs mem md [] eq_refl R11 Hra Hsp16 HM1 HM2 Hslo Hshi Pstk).
      * intros W' c' _ (SBM & PP). exists ly, (cfg_model c'). split.
        { left. destruct PP as (_ & EW & _). split; [reflexivity|]. split; [exact EW | exact SBM]. }
        split; [intros _ X; exfalso; exact (X eq_refl)|]. split; [intros _ _; exact PP|].
        intros X; exfalso; exact (X eq_refl).
    + rewrite <- ETR in *.
      assert (Htr1 : (1 <= length tr)%nat) by (rewrite ETR; cbn; lia).
      eapply SRr_mono.
      * exact (tfib_depot_first_put_ok B HB HDH W ly S regs mem md buf tr ES DK DC PZ HC IMG XD XA WF Htr Htr1 RM IVS CT TK
                 TCL TI R10 R11 Hra Hw Hb8 Hblo Hbhi Hbsp Hsp16 HM1 HM2 Hslo Hshi Pstk).
      * intros W' c' _ (ly' & md' & PEF & PP). exists ly', md'. split; [exact PEF|].
        split; [intros _ _; exact PP|]. split; [intros _ X; rewrite ETR in X; discriminate X|].
        intros X; exfalso; exact (X eq_refl).
  - destruct (PN ltac:(discriminate)) as (LY & DM).
    eapply SRr_mono.
    + exact (AFem.tfib_depot_ok B HB HDH W ly S regs mem md buf tr LY IMG WF Htr HC DM ltac:(rewrite ES; discriminate)
               R10 R11 R3 R4 Hra Hw Hb8 Hblo Hbhi
               Hbsp Hsp16 Hslo Hshi Pstk).
    + intros W' c' _ (EW & z & regs' & mem' & mat & Hc & AOK & RP & FR & PR & DM' & CK). subst W'.
      exists ly, (with_vm_backing (m_vm_lazy md) mat md). split.
      { left. split; [reflexivity|]. split; [reflexivity|]. reflexivity. }
      split; [intros X; discriminate X|]. split; [intros X; discriminate X|]. intros _.
      exists z, regs', mem'. exact (conj Hc (conj AOK (conj RP (conj FR (conj PR (conj DM' CK)))))).
Qed.

End kd.
End g.

(* ===== as_const_g2f: ONE concrete instance of Section kd's INTERIM Variable as_const_g2, so every
   consumer (AFix / AFjb / AFj2 / AFjg / AFij / AF0w) instantiates it with this name, never a per-file copy: as_const
   without its allocated_ row (the cell at ANum (as_store B + ss_alloc)). as_const_g2f_def is Section kd's hypothesis
   as_const_g2_def for it. ===== *)
Definition as_const_g2f (B : asyms) (ly : alayout) : list acell :=
  List.filter (fun c => negb (match c_at c with ANum a => a =? as_store B + ss_alloc | _ => false end)) (as_const B ly).

Lemma as_const_g2f_def : forall B ly c,
  In c (as_const_g2f B ly) <-> In c (as_const B ly) /\ c_at c <> ANum (as_store B + ss_alloc).
Proof using.
  intros B ly c. unfold as_const_g2f.
  assert (K : negb (match c_at c with ANum a => a =? as_store B + ss_alloc | _ => false end) = true <->
              c_at c <> ANum (as_store B + ss_alloc)).
  { destruct (c_at c); cbn [negb]; try (split; [intros _; discriminate | reflexivity]).
    match goal with |- negb (?z =? ?t) = true <-> _ => destruct (Z.eqb_spec z t) as [E|E] end; cbn [negb].
    - subst. split; [intros X; discriminate X | intros H; exfalso; exact (H eq_refl)].
    - split; [intros _ X; injection X as X; exact (E X) | reflexivity]. }
  split.
  - intros H. apply filter_In in H as [H1 H2]. split; [exact H1 | exact (proj1 K H2)].
  - intros [H1 H2]. apply filter_In. split; [exact H1 | exact (proj2 K H2)].
Qed.

(* ===== kd_inst: THE instantiation of Section kd's placeholders with the kernel's terms, in
   Section kd's order. AFj1 / AFjf (AR_but_depot_grow) and AFjy (first_malloc_AR_sec) pass all of these, AF0w (tfib_depot_put_any) the first nine, as terms and
   lemmas; each lemma below is its Hypothesis's text with the kernel term substituted.
     layout_grow_kd          := layout_grow                   (YG0f.v:100)
     kd_grow_NB              := kd_inst_grow_NB               (YG0f.v:106 layout_grow_NB)
     kd_grow_SB              := kd_inst_grow_SB               (YG0f.v:110 layout_grow_SB)
     kd_grow_trans           := kd_inst_grow_trans            (YG0f.v:114 layout_grow_trans)
     depot_ok_kd             := depot_ok                      (YG0n.v:194)
     depot_ok_pre_kd         := kd_inst_depot_ok_pre          (YG0n.v:224 depot_ok_pre)
     depot_ok_post_kd        := kd_inst_depot_ok_post         (YG0n.v:235 depot_ok_post)
     as_const_g2             := as_const_g2f                  (above)
     as_const_g2_def         := as_const_g2f_def              (above)
     am_depot_mono_kd        := am_depot_mono_d               (YG0n.v:263)
     am_depot_mono_kd_intro  := kd_inst_am_depot_mono_intro   (YG0n.v:283 am_depot_mono_d_intro)
     am_alloc_depot_kd       := am_alloc_depot_d              (YG0n.v:265)
     am_alloc_depot_kd_intro := kd_inst_am_alloc_depot_intro  (YG0n.v:290 am_alloc_depot_d_intro) ===== *)
Lemma kd_inst_grow_NB : forall ly nb, ly_NB ly = 0 -> layout_grow ly (set_ly_NB ly nb).
Proof using. exact layout_grow_NB. Qed.
Lemma kd_inst_grow_SB : forall ly sb, ly_SB ly = 0 -> layout_grow ly (set_ly_SB ly sb).
Proof using. exact layout_grow_SB. Qed.
Lemma kd_inst_grow_trans : forall l1 l2 l3, layout_grow l1 l2 -> layout_grow l2 l3 -> layout_grow l1 l3.
Proof using. exact layout_grow_trans. Qed.
Lemma kd_inst_depot_ok_pre : forall B ly rd S, st_depot S = [] -> (depot_ok B ly rd S <-> depot_ok_pre_text B ly rd S).
Proof using. intros B ly rd S E. exact (depot_ok_pre B ly rd S E). Qed.
Lemma kd_inst_depot_ok_post : forall B ly rd S, st_depot S <> [] ->
  (depot_ok B ly rd S <-> depot_ok_post_text B ly rd S).
Proof using. intros B ly rd S E. exact (depot_ok_post B ly rd S E). Qed.
Lemma kd_inst_am_depot_mono_intro : forall B ly rd S, ly_NB ly <> 0 -> ly_SB ly <> 0 -> st_depot S <> [] ->
  am_depot_mono_d B ly rd S.
Proof using. exact am_depot_mono_d_intro. Qed.
Lemma kd_inst_am_alloc_depot_intro : forall B ly rd S, st_depot S <> [] ->
  cell_holds B ly rd (z8 (AStore ss_alloc) kStoreBlockSize) -> am_alloc_depot_d B ly rd S.
Proof using. exact am_alloc_depot_d_intro. Qed.
