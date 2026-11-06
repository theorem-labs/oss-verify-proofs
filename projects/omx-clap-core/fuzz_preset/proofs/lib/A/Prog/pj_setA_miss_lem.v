(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the helper lemmas of segment MISS of pj_set's image-A' walk (fuzz_preset asan,
   A 0x8685c; lib/A/Prog/pj_setA_seg_miss.v): the grow call at +0x74 and the branch at +0x78.
   proves no function (kind: glue lemma).
   - pure: a stored 8-byte value is unique (pjmA_rd_u64_det, pjmA_hdr_det); the 8 bytes as a word (pjmA_rdword, the
     generic form of YF0x.v val_mem_rdword); the bytes of a readable range as a list (pjmA_rdb); two byte lists equal
     at two places (pjmA_garr8_eq); a duplicate-free sub-list is a permutation prefix (pjmA_perm_incl) and list
     NoDup / In bookkeeping; grow's granted trace (pjmA_gtrace); grow's footprint and harness-block footprints as
     ranges (pjmA_inFP_grow, pjmA_inFP_hbl); an object node from its header, slot blocks and member list (pjmA_node_obj);
     an order list over a permuted block list (pjmA_foR_perm); the model's capacity after one more member
     (pjmA_ncap_S, pjmA_ncap_S_pos); prh_oks of a run whose one failure is the chosen one, or of an all-granted run
     outside the failure window (pjmA_oks_chosen, pjmA_oks_granted).
   - the model run: grow's events under the empty grant list are the head of pj_set's absent-key events
     (pjmA_grow_ev, pjmA_grow_evs at cf_head = PresetReqAt.HEAD, pjmA_mfind_none, pjmA_set_grow_run: the run premise of
     grow's all-granted events from pjsA_pre's run premise; pjmA_set_grow_cons: their consumer premise, which grow's
     refused arms' exclusion clauses take, from pjsA_pre's prh_cons_from); a position bounds the class-24 count
     (pjmA_pb_of_pos, by lib/Spec/PresetRoomCounts.v counts_of_room_pos_rl); a position and a run premise of E bound the
     secondary and class-24 counts at every state along E (pjmA_pk_of_pos: tgrow_specX's two position-free count
     premises, by lib/Spec/PresetLiveSec.v live_sec / live_c24 at each prefix i + j of the run, PresetRun.pkR_base for
     the driver's at most 3 live requests, and PresetRoomCounts.iface_hruns_big above MAXB); an entry sum of both of
     grow's requests bounds the live room at each of its events (pjmA_grow_live: tgrow_specX's per-event room
     conjunct, PRH_Base.prh_live_evs, by lib/Spec/PresetLiveBytes.v blocks_bytes_zsum - the live requests
     sum to blocks_bytes - and pjmA_rm1_sum).
   - over the allocator laws (AR_laws_x at cf_head): two live blocks, a block and a frame, a struct placed by
     PRH_FnReader.v prhReader_at and a block are disjoint (pjmA_blk_disj, pjmA_frm_blk, pjmA_at_disj, pjmA_lam_off,
     pjmA_at_off, pjmA_key_off); a placed struct is off the shadow region (pjmA_at_app); a block listed twice in a
     permutation of the live blocks is impossible (pjmA_dup); what grow's block swap (prhReader_swap) keeps and adds
     (pjmA_swap_lam, pjmA_swap_blk, pjmA_swap_new, pjmA_blocks_swap); a block with a byte off a callee's footprint
     survives the call (pjmA_blk_live); the bytes of harness blocks and of a placed struct off the footprint agree
     across the call (pjmA_blks_agree, pjmA_at_agree).
   - pjsA_FAILc's obligation: what pj_free(val) keeps of the object (pjmA_free_agree); the object as a tree after it
     (pjmA_obl_node), and after a half-done grow (kids moved, keys not) freeable to the depth of the entry tree from
     its header, its slot blocks and its member list (pjmA_obl_parts, by pjmA_fd_obj). The callee journals of the
     lemmas over the allocator laws are at any world relation RJ (pj_free's and grow's at the re-hiding relation, the
     others' at wle); no lemma reads the world conjunct.
   - the `beq` step at a listing offset (pjmA_step_beq, pj_setA_seg_tail.v's step lemmas with YK11.v step_beq_tk /
     step_beq_ft).
   Numerals: 56 / 8 (LENGTH: the struct pj, a key pointer), 64 (LENGTH: 56 + 8, the bytes grow adds per slot),
   6 (the object tag), 24 / 40 / 48 (LENGTH: field offsets of grow's footprint). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0x PjpTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetLiveSec PresetLiveBounds PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA pj_setA_defs pj_setA_glue pj_setA_vis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_trans.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

(* ---- pure ---- *)
Section p.
Variable segs : list Segment.

Lemma pjmA_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact Hz.
Qed.

Lemma pjmA_val_mem_det : forall m a v v', val_mem segs m a 8 v -> val_mem segs m a 8 v' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
intros m a v v' H H' Hv Hv'.
assert (E : forall k, (k < 8)%nat -> YG0f.le_byte v 8 k = YG0f.le_byte v' 8 k).
{ intros k Hk.
  assert (A : mbyte segs m (a + Z.of_nat k) = Some (Z_to_bv 8 (YG0f.le_byte v 8 k))) by exact (H k Hk).
  assert (A' : mbyte segs m (a + Z.of_nat k) = Some (Z_to_bv 8 (YG0f.le_byte v' 8 k))) by exact (H' k Hk).
  rewrite A in A'. assert (A2 : Z_to_bv 8 (YG0f.le_byte v 8 k) = Z_to_bv 8 (YG0f.le_byte v' 8 k)) by congruence.
  apply (f_equal (fun b : bv 8 => bv_unsigned b)) in A2.
  rewrite !pjmA_u8 in A2 by (unfold YG0f.le_byte; apply Z.mod_pos_bound; lia). exact A2. }
assert (Sv : let b := fun k => YG0f.le_byte v 8 k in
  b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 * (b 6%nat
  + 256 * b 7%nat)))))) = v) by exact (YF0x.le_bytes8_sum v Hv).
assert (Sv' : let b := fun k => YG0f.le_byte v' 8 k in
  b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 * (b 6%nat
  + 256 * b 7%nat)))))) = v') by exact (YF0x.le_bytes8_sum v' Hv').
cbv beta zeta in Sv, Sv'.
rewrite !E in Sv by lia. lia.
Qed.

Lemma pjmA_rd_u64_det : forall m a v v', rd_u64 segs m a v -> rd_u64 segs m a v' -> v = v'.
Proof. intros m a v v' (R & H) (R' & H'). exact (pjmA_val_mem_det m a v v' H H' R R'). Qed.

Lemma pjmA_hdr_det : forall m p ty num str kids keys n cap ty' num' str' kids' keys' n' cap',
  pj_hdrR segs m p ty num str kids keys n cap -> pj_hdrR segs m p ty' num' str' kids' keys' n' cap' ->
  num = num' /\ str = str' /\ kids = kids' /\ keys = keys' /\ n = n' /\ cap = cap'.
Proof.
intros m p ty num str kids keys n cap ty' num' str' kids' keys' n' cap'
  (_ & _ & N & Sx & K & Y & Nn & C) (_ & _ & N' & Sx' & K' & Y' & Nn' & C').
split; [exact (pjmA_rd_u64_det _ _ _ _ N N')|]. split; [exact (pjmA_rd_u64_det _ _ _ _ Sx Sx')|].
split; [exact (pjmA_rd_u64_det _ _ _ _ K K')|]. split; [exact (pjmA_rd_u64_det _ _ _ _ Y Y')|].
split; [exact (pjmA_rd_u64_det _ _ _ _ Nn Nn') | exact (pjmA_rd_u64_det _ _ _ _ C C')].
Qed.

(* the bytes of a range as a list (0 where a byte is absent) *)
Definition pjmA_rdb (m : word -> option byte) (a : Z) (n : nat) : list Z :=
  map (fun j => match mbyte segs m (a + Z.of_nat j) with Some b => bv_unsigned b | None => 0 end) (seq 0 n).

Lemma pjmA_rdb_len : forall m a n, length (pjmA_rdb m a n) = n.
Proof. intros m a n. unfold pjmA_rdb. rewrite length_map, length_seq. reflexivity. Qed.

Lemma pjmA_rdb_garr8 : forall m a n, (forall j, (j < n)%nat -> mbyte segs m (a + Z.of_nat j) <> None) ->
  garr8 segs m a (pjmA_rdb m a n).
Proof.
intros m a n H j Hj. rewrite pjmA_rdb_len in Hj.
set (f := fun j => match mbyte segs m (a + Z.of_nat j) with Some b => bv_unsigned b | None => 0 end).
assert (E : nth j (pjmA_rdb m a n) 0 = f j).
{ unfold pjmA_rdb. fold f. rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity. }
rewrite E. unfold f. specialize (H j Hj).
destruct (mbyte segs m (a + Z.of_nat j)) as [b|] eqn:Eb; [|exfalso; exact (H eq_refl)].
pose proof (bv_unsigned_in_range _ b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
split; [|exact Rb].
intros k Hk. assert (k = 0%nat) by lia. subst k. try change (Z.of_nat 0) with 0. rewrite ?Z.add_0_r. rewrite Eb. f_equal.
assert (Hle : forall z, 0 <= z < 256 -> YG0f.le_byte z 1 0 = z).
{ intros z Hz. unfold YG0f.le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
  replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity. rewrite !Z.mod_small by lia. reflexivity. }
change (b = Z_to_bv 8 (YG0f.le_byte (bv_unsigned b) 1 0)). rewrite Hle by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma pjmA_garr8_eq : forall m m' a a' l, garr8 segs m a l -> garr8 segs m' a' l ->
  forall j, 0 <= j < Z.of_nat (length l) -> mbyte segs m' (a' + j) = mbyte segs m (a + j).
Proof.
intros m m' a a' l H H' j Hj.
destruct (H (Z.to_nat j) ltac:(lia)) as [V _]. destruct (H' (Z.to_nat j) ltac:(lia)) as [V' _].
specialize (V 0%nat ltac:(lia)). specialize (V' 0%nat ltac:(lia)).
rewrite Z2Nat.id in V, V' by lia. rewrite Z.add_0_r in V, V'. rewrite V, V'. reflexivity.
Qed.

End p.

Lemma pjmA_perm_incl : forall {A : Type} (l L : list A), List.NoDup l -> incl l L -> exists r, Permutation L (l ++ r).
Proof.
intros A l. induction l as [|x l IH]; intros L HN Hi.
- exists L. reflexivity.
- inversion HN as [|x0 l0 Hx HN']; subst.
  destruct (in_split x L (Hi x (or_introl eq_refl))) as (L1 & L2 & ->).
  destruct (IH (L1 ++ L2) HN') as (r & Hr).
  { intros y Hy. assert (Hy' : In y (L1 ++ x :: L2)) by exact (Hi y (or_intror Hy)).
    apply in_app_or in Hy'. apply in_or_app. destruct Hy' as [Hy'|[E|Hy']]; [left; exact Hy' | | right; exact Hy'].
    subst y. contradiction. }
  exists r. cbn [app]. apply (Permutation_trans (Permutation_sym (Permutation_middle L1 L2 x))).
  apply Permutation_cons; [reflexivity | exact Hr].
Qed.

Lemma pjmA_pw_cross : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y,
  YG0f.pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y H Hx Hy; [destruct Hx|].
cbn [app YG0f.pairwise] in H. destruct H as [Hf Hp]. destruct Hx as [<-|Hx].
- rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Hp Hx Hy).
Qed.

Lemma pjmA_nd : forall {A : Type} (l : list A), NoDup l -> List.NoDup l.
Proof. intros A l H. first [exact H | apply NoDup_ListNoDup; exact H]. Qed.
Lemma pjmA_nd' : forall {A : Type} (l : list A), List.NoDup l -> NoDup l.
Proof. intros A l H. first [exact H | apply NoDup_ListNoDup; exact H]. Qed.

Lemma pjmA_nodup_app : forall {A : Type} (l1 l2 : list A), List.NoDup l1 -> List.NoDup l2 ->
  (forall x, In x l1 -> ~ In x l2) -> List.NoDup (l1 ++ l2).
Proof.
intros A l1. induction l1 as [|x l1 IH]; intros l2 H1 H2 Hd; cbn [app]; [exact H2|].
inversion H1 as [|x0 l0 Hx H1']; subst. constructor.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hx Hin) | exact (Hd x (or_introl eq_refl) Hin)].
- apply IH; [exact H1' | exact H2|]. intros y Hy. apply Hd. right. exact Hy.
Qed.

Lemma pjmA_nodup_sub : forall {A : Type} (l1 l2 l3 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l3 -> incl l3 l2 ->
  List.NoDup (l1 ++ l3).
Proof.
intros A l1 l2 l3 H H3 Hi. destruct (pjmA_perm_incl l3 l2 H3 Hi) as (r & Hr).
assert (H' : List.NoDup ((l1 ++ l3) ++ r)).
{ rewrite <- app_assoc. apply (Permutation_NoDup (Permutation_app_head l1 Hr)). exact H. }
exact (NoDup_app_remove_r _ _ H').
Qed.

Lemma pjmA_old_eq : forall kids keys cap, kids_blkR kids cap ++ keys_blkR 6 keys cap =
  (if cap =? 0 then [] else [(kids, 56 * cap); (keys, 8 * cap)]).
Proof. intros kids keys cap. unfold kids_blkR, keys_blkR. destruct (cap =? 0); reflexivity. Qed.

Lemma pjmA_fst_ne : forall (L : list (Z * Z)) a k a' k', NoDup (map fst L) -> In (a, k) L -> In (a', k') L ->
  (a, k) <> (a', k') -> a <> a'.
Proof.
intros L a k a' k' HN H1 H2 Hne Ea. subst a'. apply Hne. f_equal. exact (prh_fst_unique L a k k' HN H1 H2).
Qed.

(* the generic form of YF0x.v val_mem_rdword (that one is stated at image A's segments) *)
Lemma pjmA_rdword : forall (segs : list Segment) (H : word -> bool) mem a v,
  0 <= v < 2 ^ 64 -> val_mem segs (mrestrict H mem) a 8 v -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hm. unfold rdword, aview.
assert (Bk : forall k, (k < 8)%nat ->
  mbyte segs (mrestrict H mem) (a + Z.of_nat k) = Some (Z_to_bv 8 (YG0f.le_byte v 8 k))) by (intros k Hk; exact (Hm k Hk)).
assert (R : forall k, 0 <= YG0f.le_byte v 8 k < 256) by (intros k; unfold YG0f.le_byte; apply Z.mod_pos_bound; lia).
replace a with (a + Z.of_nat 0) at 1 by lia.
replace (a + 1) with (a + Z.of_nat 1) by lia. replace (a + 2) with (a + Z.of_nat 2) by lia.
replace (a + 3) with (a + Z.of_nat 3) by lia. replace (a + 4) with (a + Z.of_nat 4) by lia.
replace (a + 5) with (a + Z.of_nat 5) by lia. replace (a + 6) with (a + Z.of_nat 6) by lia.
replace (a + 7) with (a + Z.of_nat 7) by lia.
rewrite !Bk by lia. cbn [option_map]. rewrite !pjmA_u8 by apply R.
f_equal. exact (YF0x.le_bytes8_sum v Hv).
Qed.

(* grow's granted trace (every realloc granted): nothing when n < cap, the two reallocs to cap2R cap when n = cap *)
Lemma pjmA_gtrace : forall n cap, 0 <= n <= cap ->
  PjGrammar.held (PRH_Charge.prhPg_gtrace true n cap) = (if n =? cap then 64 * (cap2R cap - cap) else 0) /\
  PjGrammar.calls (PRH_Charge.prhPg_gtrace true n cap) = (if n =? cap then 2%nat else 0%nat).
Proof.
intros n cap Hn. unfold PRH_Charge.prhPg_gtrace, PjGrammar.grow.
destruct (Z.eqb_spec n cap) as [<-|Hne].
- rewrite Nat.ltb_irrefl. unfold cap2R.
  destruct (Nat.eqb_spec (Z.to_nat n) 0) as [E0|E0].
  + assert (n = 0) by lia. subst n. cbn. split; reflexivity.
  + rewrite (proj2 (Z.eqb_neq n 0)) by lia.
    cbn [PjGrammar.jbind PjGrammar.jrealloc PjGrammar.take PjGrammar.jret fst snd app PjGrammar.held
         PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call].
    split; [lia | reflexivity].
- replace (Nat.ltb (Z.to_nat n) (Z.to_nat cap)) with true by (symmetry; apply Nat.ltb_lt; lia).
  cbn. split; reflexivity.
Qed.

(* the model's capacity after one more member (PresetReqAt.ncap is PjRoundTrip.gcap from 0): kept while there is
   room, else the realloc's cap2R *)
Lemma pjmA_ncap_S : forall m, Z.of_nat (PresetReqAt.ncap (Datatypes.S m)) =
  if Z.of_nat m <? Z.of_nat (PresetReqAt.ncap m) then Z.of_nat (PresetReqAt.ncap m)
  else cap2R (Z.of_nat (PresetReqAt.ncap m)).
Proof.
intros m. cbn [PresetReqAt.ncap]. unfold PjRoundTrip.gcap, cap2R.
destruct (Nat.ltb_spec m (PresetReqAt.ncap m)) as [H|H].
- rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  destruct (Nat.eqb_spec (PresetReqAt.ncap m) 0) as [E|E].
  + rewrite E. reflexivity.
  + rewrite (proj2 (Z.eqb_neq _ _)) by lia. lia.
Qed.

Lemma pjmA_ncap_S_pos : forall m, (0 < PresetReqAt.ncap (Datatypes.S m))%nat.
Proof.
intros m. cbn [PresetReqAt.ncap]. unfold PjRoundTrip.gcap.
destruct (Nat.ltb_spec m (PresetReqAt.ncap m)); [lia|].
destruct (Nat.eqb_spec (PresetReqAt.ncap m) 0); lia.
Qed.

(* prh_oks of a run whose c-th outcome is the CHOSEN failure (cnt + (c - 1) = fail) and every earlier one granted:
   no refusal, so g_ran_out is kept *)
Lemma pjmA_oks_chosen : forall ok cnt fail c ns most ran,
  (1 <= c)%nat -> nth (c - 1) ok true = false -> (forall i, (i < c - 1)%nat -> nth i ok true = true) ->
  cnt + Z.of_nat (c - 1) = fail -> prh_oks ok cnt fail c ns most ran ran.
Proof.
intros ok cnt fail c ns most ran Hc Hn Hb He. split; [|split; [left; reflexivity|]].
- intros i Hi Hi'. replace i with (c - 1)%nat by lia. exact Hn.
- intros i Hi Hr _. exfalso. unfold prh_refused in Hr. apply andb_prop in Hr as (H1 & H2).
  destruct (Nat.lt_ge_cases i (c - 1)) as [Hlt | Hge].
  + rewrite (Hb i Hlt) in H1. cbn in H1. discriminate H1.
  + replace i with (c - 1)%nat in H2 by lia. rewrite He, Z.eqb_refl in H2. cbn in H2. discriminate H2.
Qed.

(* prh_oks of an all-granted run outside the failure window: no failure, no refusal *)
Lemma pjmA_oks_granted : forall ok cnt fail c ns most ran,
  (forall i, (i < c)%nat -> nth i ok true = true) -> ~ (cnt <= fail < cnt + Z.of_nat c) ->
  prh_oks ok cnt fail c ns most ran ran.
Proof.
intros ok cnt fail c ns most ran Hg Hw. split; [|split; [left; reflexivity|]].
- intros i Hi He. exfalso. apply Hw. lia.
- intros i Hi Hr _. exfalso. unfold prh_refused in Hr. rewrite (Hg i Hi) in Hr. cbn in Hr. discriminate Hr.
Qed.

(* the model run: pj_set's absent-key events (PRH_FnPj.v prhPj_set_evs) begin with PjRoundTrip.grow_ev true n cap,
   which is PjGrammar.grow's trace under the empty grant list (every realloc granted), so grow's entry premise holds
   at rp_ok := [] (PRH_FnReader.v prhPg_evs_model at cf_head = HEAD) *)
Lemma pjmA_grow_ev : forall n cap, PjRoundTrip.grow_ev true n cap = snd (fst (PjGrammar.grow true n cap [])).
Proof.
intros n cap. unfold PjRoundTrip.grow_ev, PjRoundTrip.gcap, PjGrammar.grow. destruct (Nat.ltb n cap); reflexivity.
Qed.

Lemma pjmA_grow_evs : forall {cp : CfParams} n cap, 0 <= n -> 0 <= cap -> cf_head = PresetReqAt.HEAD ->
  prhPg_evs true n cap [] = PresetReqAt.rd_hevs (PjRoundTrip.grow_ev true (Z.to_nat n) (Z.to_nat cap)).
Proof. intros cp n cap Hn Hc Hhd. rewrite pjmA_grow_ev. exact (prhPg_evs_model true n cap [] Hn Hc Hhd). Qed.

Lemma pjmA_mfind_none : forall kname (ms : list (list Z * PjTree.jv)), ~ In kname (map fst ms) ->
  prhPj_mfind kname ms = None.
Proof.
intros kname ms. induction ms as [|[k u] r IH]; intros H; [reflexivity|].
cbn [prhPj_mfind]. destruct (PresetReqAt.zl_eqb k kname) eqn:E.
- exfalso. apply H. left. exact (PresetReqAtNoMiss.zl_eqb_true k kname E).
- apply IH. intros Hin. apply H. right. exact Hin.
Qed.

Lemma pjmA_set_grow_run : forall {cp : CfParams} sm x os i (ms : list (list Z * PjTree.jv)) kname n cap,
  0 <= n -> 0 <= cap -> cf_head = PresetReqAt.HEAD -> ~ In kname (map fst ms) ->
  prh_run_at sm x os i (prhPj_set_evs ms kname n cap) -> prh_run_at sm x os i (prhPg_evs true n cap []).
Proof.
intros cp sm x os i ms kname n cap Hn Hc Hhd Hni H.
unfold prhPj_set_evs in H. rewrite (pjmA_mfind_none kname ms Hni) in H.
rewrite (pjmA_grow_evs n cap Hn Hc Hhd).
unfold PresetReqAt.rd_hevs in H |- *. rewrite flat_map_app in H.
exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H)).
Qed.

(* the consumer premise of grow's all-granted events (its refused arms' exclusion clauses take it) from pjsA_pre's
   consumer premise over pj_set's absent-key events, whose head they are (PRH_Base.prh_cons_from_sub) *)
Lemma pjmA_set_grow_cons : forall {cp : CfParams} sm x os i (ms : list (list Z * PjTree.jv)) kname n cap,
  0 <= n -> 0 <= cap -> cf_head = PresetReqAt.HEAD -> ~ In kname (map fst ms) ->
  prh_cons_from sm x os i (length (prhPj_set_evs ms kname n cap)) ->
  prh_cons_from sm x os i (length (prhPg_evs true n cap [])).
Proof.
intros cp sm x os i ms kname n cap Hn Hc Hhd Hni H.
unfold prhPj_set_evs in H. rewrite (pjmA_mfind_none kname ms Hni) in H.
unfold PresetReqAt.rd_hevs in H. rewrite flat_map_app, length_app in H.
rewrite (pjmA_grow_evs n cap Hn Hc Hhd). unfold PresetReqAt.rd_hevs.
lazymatch goal with |- prh_cons_from _ _ _ _ ?k' => lazymatch type of H with prh_cons_from _ _ _ _ ?k =>
  pose proof (prh_cons_from_sub sm x os i k 0 k' ltac:(lia) H) as H' end end.
rewrite Nat.add_0_r in H'. exact H'.
Qed.

(* a model-run position bounds the class-24 count (pj_free's position-free text's PB) *)
Lemma pjmA_pb_of_pos : forall sm x os i H0 hist S, PresetRoomPos.iface_room_pos sm x os i H0 hist S -> pjsA_PB S.
Proof. intros sm x os i H0 hist S H. exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl sm x os i H0 hist S H)). Qed.

(* ---- the live counts at grow's inner calls: tgrow_specX's two position-free premises, the peak of the
   secondary and class-24 live counts along its all-granted events, from a position and a run premise (the
   header's route: the live set is the run's prefix plus at most 3 driver requests) ---- *)
(* the peak along E is bounded when every state along E is *)
Lemma pjmA_pkR_le : forall f (E : list PresetReqAt.hev) L M,
  (forall j, (j <= length E)%nat -> (PresetReqAt.cnt f (PresetReqAt.hlive_from L (firstn j E)) <= M)%nat) ->
  (PresetRun.pkR f L E <= M)%nat.
Proof.
intros f E. induction E as [|e r IH]; intros L M H; cbn [PresetRun.pkR].
- exact (H 0%nat (le_n _)).
- apply Nat.max_lub.
  + exact (H 0%nat ltac:(lia)).
  + apply IH. intros j Hj. exact (H (Datatypes.S j) ltac:(cbn [length]; lia)).
Qed.

Lemma pjmA_firstn_add : forall {A : Type} (l : list A) n m, firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
intros A l n. revert l. induction n as [|n IH]; intros l m; [reflexivity|].
destruct l as [|a l]; [destruct m; reflexivity|]. simpl. f_equal. apply IH.
Qed.

(* the states along a run premise's events are the run's own prefixes *)
Lemma pjmA_pk_state : forall sm x os i j (E : list PresetReqAt.hev), prh_run_at sm x os i E -> (j <= length E)%nat ->
  PresetReqAt.hlive_from (PresetReqAt.hlive (firstn i (PresetRun.hruns sm x os))) (firstn j E) =
  PresetReqAt.hlive (firstn (i + j) (PresetRun.hruns sm x os)).
Proof.
intros sm x os i j E HR Hj. unfold prh_run_at in HR.
rewrite <- HR, firstn_firstn, Nat.min_l by exact Hj.
unfold PresetReqAt.hlive. rewrite <- PresetReqAt.hlive_from_app, pjmA_firstn_add. reflexivity.
Qed.

Lemma pjmA_pk_of_pos : forall sm x os i H0 hist S (E : list PresetReqAt.hev),
  PresetRoomPos.iface_room_pos sm x os i H0 hist S -> prh_run_at sm x os i E ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E) <=
    PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E) <=
    PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros sm x os i H0 hist S E ((d & Hd & Hp) & _) HR.
set (L := PresetReqAt.hlive (firstn i (PresetRun.hruns sm x os))) in Hp.
assert (HB : forall f (M : Z), 0 <= M ->
  (Z.of_nat (length x) <= PresetReqAt.MAXB -> forall k,
     Z.of_nat (PresetReqAt.cnt f (PresetReqAt.hlive (firstn k (PresetRun.hruns sm x os)))) <= M) ->
  Z.of_nat (PresetRun.pkR f (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) E) <= M + 3).
{ intros f M HM0 HM.
  assert (HL : (PresetRun.pkR f L E <= Z.to_nat M)%nat).
  { apply pjmA_pkR_le. intros j Hj. unfold L. rewrite (pjmA_pk_state sm x os i j E HR Hj).
    destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [Hx|Hx].
    - specialize (HM Hx (i + j)%nat). lia.
    - rewrite (PresetRoomCounts.iface_hruns_big sm x os ltac:(lia)), firstn_nil. cbn. lia. }
  pose proof (PresetRun.pkR_mono f E _ _ (PresetReqAt.subm_perm _ _ (Permutation_sym Hp))) as H1.
  pose proof (PresetRun.pkR_base f E L d) as H2.
  assert (H3 : (PresetReqAt.cnt f d <= 3)%nat)
    by (unfold PresetReqAt.cnt; pose proof (YGcfRoomLive.rl_filter_len f d); lia).
  lia. }
split.
- pose proof (HB YGcfRoomLive.rl_sec_req PresetLiveBounds.LSEC ltac:(rewrite PresetLiveBounds.LSEC_value; lia)
    (fun Hx k => PresetLiveSec.live_sec sm x os k Hx)) as H.
  unfold PresetLiveBounds.DRV. lia.
- pose proof (HB (PresetRoom.in_cls YG00.kBatchClass) PresetLiveBounds.L24
    ltac:(rewrite PresetLiveBounds.L24_value; lia) (fun Hx k => PresetLiveSec.live_c24 sm x os k Hx)) as H.
  unfold PresetLiveBounds.DRV. lia.
Qed.

(* ---- the live room at each of grow's events: tgrow_specX's per-event conjunct (PRH_Base.prh_live_evs over
   prhPg_evs o cap cap [], at n = cap) from the entry sum `blocks_bytes S + LIVE_grow 6 cap <= LIVE_MAX`, which
   pj_set's LIVE_pj_set bounds. The entry's live requests sum to blocks_bytes S (PresetLiveBytes.blocks_bytes_zsum; PresetRoom.rs_live (YGcfRoom.room_of_cf S) is map snd (blocks S) by
   conversion), a realloc's step adds its new request and removes at most the old one, so at each event the live
   bytes plus its request lie under the sum of both requests ---- *)

Lemma pjmA_rm1_sum : forall m s, 0 <= m -> fold_right Z.add 0 (PresetReqAt.rm1 m s) <= fold_right Z.add 0 s.
Proof.
intros m s Hm. induction s as [|y r IH]; [cbn; lia|].
cbn [PresetReqAt.rm1]. destruct (Z.eqb_spec y m) as [->|Hne]; cbn [fold_right]; lia.
Qed.

Lemma pjmA_grow_live : forall {cp : CfParams} (o : bool) S cap, 0 <= cap ->
  blocks_bytes S + LIVE_grow 6 cap <= LIVE_MAX -> prh_live_evs S (prhPg_evs o cap cap []).
Proof.
intros cp o S cap Hc H. pose proof cf_head_nonneg as C0.
assert (C2 : 0 < cap2R cap) by (unfold cap2R; destruct (Z.eqb_spec cap 0); lia).
assert (H' : blocks_bytes S + (56 * cap2R cap + cf_head + (8 * cap2R cap + cf_head)) <= LIVE_MAX) by exact H.
rewrite PresetLiveBytes.blocks_bytes_zsum in H'.
change (map snd (YG01.blocks S)) with (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) in H'.
unfold PresetLiveBytes.zsum in H'. clear H.
assert (K0 : fold_right Z.add 0 (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) []) +
  prh_ev_req (prhPg_ev 56 cap) <= LIVE_MAX).
{ unfold prhPg_ev. destruct (cap =? 0); cbn [prh_ev_req PresetReqAt.hlive_from fold_left]; lia. }
assert (K1 : fold_right Z.add 0 (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
  [prhPg_ev 56 cap]) + prh_ev_req (prhPg_ev 8 cap) <= LIVE_MAX).
{ unfold prhPg_ev. destruct (Z.eqb_spec cap 0) as [E0|E0];
    cbn [prh_ev_req PresetReqAt.hlive_from fold_left PresetReqAt.hstep fold_right].
  - lia.
  - assert (Hm : 0 <= 56 * cap + cf_head) by lia.
    pose proof (pjmA_rm1_sum _ (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) Hm). lia. }
unfold prh_live_evs, prh_live_at, prhPg_evs. rewrite Z.ltb_irrefl.
intros j e Hj.
destruct o; cbn [nth andb] in Hj;
  (destruct j as [|[|j]]; cbn [nth_error] in Hj;
   [injection Hj as <-; exact K0
   |first [discriminate Hj | injection Hj as <-; exact K1]
   |destruct j; cbn in Hj; discriminate Hj]).
Qed.

(* the footprint of a list of harness blocks, as allocator ranges *)
Lemma pjmA_inFP_hbl : forall {cp : CfParams} (Y : list (Z * Z)) x, inFP (ablocks_fp (prhPj_hbl Y)) x ->
  exists a k, In (a, k) Y /\ a - cf_head <= x < a - cf_head + req_size (k + cf_head).
Proof.
intros cp Y x (r & Hr & Hx). unfold ablocks_fp, prhPj_hbl in Hr. rewrite map_map in Hr.
apply in_map_iff in Hr as ((a, k) & <- & Hin). cbn [fst snd] in Hx. exists a, k. split; [exact Hin | lia].
Qed.

Lemma pjmA_hbl_inFP : forall {cp : CfParams} (Y : list (Z * Z)) a k x, In (a, k) Y ->
  a - cf_head <= x < a - cf_head + req_size (k + cf_head) -> inFP (ablocks_fp (prhPj_hbl Y)) x.
Proof.
intros cp Y a k x Hin Hx. exists (a - cf_head, a - cf_head + req_size (k + cf_head)). split; [|cbn [fst snd]; lia].
unfold ablocks_fp, prhPj_hbl. rewrite map_map. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin].
Qed.

Lemma pjmA_hbl_in : forall {cp : CfParams} (Y : list (Z * Z)) a k, In (a, k) Y -> In (a - cf_head, k + cf_head) (prhPj_hbl Y).
Proof. intros cp Y a k Hin. unfold prhPj_hbl. exact (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Y (a, k) Hin). Qed.

Lemma pjmA_hbl_inv : forall {cp : CfParams} (Y : list (Z * Z)) b m, In (b, m) (prhPj_hbl Y) -> In (b + cf_head, m - cf_head) Y.
Proof.
intros cp Y b m Hin. unfold prhPj_hbl in Hin. apply in_map_iff in Hin as ((a, k) & E & Hin). cbn [fst snd] in E.
injection E as <- <-. replace (a - cf_head + cf_head, k + cf_head - cf_head) with (a, k) by (f_equal; lia). exact Hin.
Qed.

(* grow's footprint: two header ranges and the old slot blocks *)
Lemma pjmA_inFP_grow : forall {cp : CfParams} o (Y : list (Z * Z)) x,
  inFP ([(o + 24, o + 40); (o + 48, o + 56)] ++ ablocks_fp (prhReader_ab Y)) x ->
  (o + 24 <= x < o + 40 \/ o + 48 <= x < o + 56) \/
  exists a k, In (a, k) Y /\ a - cf_head <= x < a - cf_head + req_size (k + cf_head).
Proof.
intros cp o Y x (r & Hr & Hx). apply in_app_or in Hr as [Hr|Hr].
- left. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Hx; [left|right]; exact Hx.
- right. apply pjmA_inFP_hbl. exists r. split; [exact Hr | exact Hx].
Qed.

Lemma pjmA_swap_lam0 : forall {A : Type} (Lam Lam0 Dx : list A) x,
  Permutation Lam (Dx ++ Lam0) -> In x Lam -> ~ In x Dx -> In x Lam0.
Proof.
intros A Lam Lam0 Dx x H Hin Hn. apply (Permutation_in _ H) in Hin. apply in_app_or in Hin as [Hin|Hin];
  [contradiction | exact Hin].
Qed.

Lemma pjmA_nodup_disj : forall {A : Type} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros A l1. induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|].
cbn [app] in H. inversion H as [|y0 l0 Hy H']; subst. destruct H1 as [<-|H1].
- apply Hy. apply in_or_app. right. exact H2.
- exact (IH l2 x H' H1 H2).
Qed.

Section p2.
Variable segs : list Segment.
Lemma pjmA_agree_sub : forall m m' (X Y : Z -> Prop), pj_agreeR segs m m' X -> (forall x, Y x -> X x) ->
  pj_agreeR segs m m' Y.
Proof. intros m m' X Y H HYX x Hy. exact (H x (HYX x Hy)). Qed.
Lemma pjmA_agree_foot : forall m m' p D, pj_agreeR segs m m' (fun x => p <= x < p + 56) ->
  pj_agreeR segs m m' (fun x => exists b, In b D /\ pj_holdsR b x) -> pj_agreeR segs m m' (pj_footR p D).
Proof. intros m m' p D H1 H2 x [Hx|Hx]; [exact (H1 x Hx) | exact (H2 x Hx)]. Qed.
Lemma pjmA_node_nodup : forall (m : word -> option byte) lblk p t D, pj_nodeR segs m lblk p t D ->
  NoDup D /\ pj_apartR D p.
Proof. intros m lblk p t D H. destruct t; cbn [pj_nodeR] in H; destruct H as (H1 & H2 & _); split; assumption. Qed.
(* an object node from its header, its slot blocks and its member list *)
Lemma pjmA_node_obj : forall m lblk o num kids keys n cap (ms : list (list Z * PjTree.jv)) Di D,
  pj_hdrR segs m o 6 num 0 kids keys n cap -> n = Z.of_nat (length ms) -> n <= cap ->
  (cap = 0 /\ kids = 0 /\ keys = 0 \/ 0 < cap /\ lblk kids (56 * cap) /\ lblk keys (8 * cap)) ->
  NoDup D -> pj_apartR D o -> D = (if cap =? 0 then [] else [(kids, 56 * cap); (keys, 8 * cap)]) ++ Di ->
  pj_memsR segs m lblk (pj_nodeR segs m lblk) kids keys ms Di ->
  pj_nodeR segs m lblk o (PjTree.JObj ms) D.
Proof.
intros m lblk o num kids keys n cap ms Di D Hh En Hnc Hcap HN HA ED HM. cbn [pj_nodeR PjTree.tag].
split; [exact HN|]. split; [exact HA|]. exists num, 0, kids, keys, n, cap.
split; [exact Hh|]. split; [reflexivity|]. split; [exact En|]. split; [exact Hnc|]. split; [exact Hcap|].
exists Di. split; [exact ED | exact HM].
Qed.
(* an order list over a permuted block list (pj_oshapeR reads its block list up to permutation only) *)
Lemma pjmA_foR_perm : forall m lblk d p (D D' F : list (Z * Z)),
  PRH_PjOrder.pj_foR segs m lblk d p D F -> Permutation D D' -> PRH_PjOrder.pj_foR segs m lblk d p D' F.
Proof.
intros m lblk d p D D' F H HP.
assert (K : forall Pi, PRH_PjOrder.pj_oshapeR segs m lblk Pi p D F -> PRH_PjOrder.pj_oshapeR segs m lblk Pi p D' F).
{ intros Pi (HN & HA & HR). split; [|split].
  - assert (HN' : List.NoDup D')
      by (apply (Permutation_NoDup HP); first [exact HN | apply NoDup_ListNoDup; exact HN]).
    first [exact HN' | apply NoDup_ListNoDup; exact HN'].
  - intros b x Hb. apply HA. exact (Permutation_in _ (Permutation_sym HP) Hb).
  - destruct HR as (ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi & Hh & H1 & H2 & H3 & HP0 & H4).
    exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi.
    split; [exact Hh|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    split; [exact (Permutation_trans (Permutation_sym HP) HP0) | exact H4]. }
destruct d as [|d]; cbn [PRH_PjOrder.pj_foR] in H |- *; exact (K _ H).
Qed.
End p2.

(* ---- over the allocator laws ---- *)
Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the callee's journal at a world relation RJ (inferred from the journal argument at every use) *)
Context {RJ : world SEGS -> world SEGS -> Prop}.
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RJ).

Lemma pjmA_lam_blk : forall ly S Hp W mem Lam peak cnt fail ran most own a k,
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk & Hab & _).
split; [exact Hk | exact Hab].
Qed.

Lemma pjmA_req_eq : forall k, 0 < k -> req_size k = k.
Proof. intros k Hk. unfold req_size. destruct (Z.eqb_spec k 0); lia. Qed.

(* two distinct live blocks are disjoint *)
Lemma pjmA_blk_disj : forall ly S Hp W mem md b m b' m' x,
  ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> In (b', m') (ablocks B ly S) -> (b, m) <> (b', m') ->
  b <= x < b + req_size m -> ~ (b' <= x < b' + req_size m').
Proof.
intros ly S Hp W mem md b m b' m' x HAR H1 H2 Hne Hx Hx'.
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b m b' m' HAR H1 H2 Hne) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* a live block and a live fake frame are disjoint *)
Lemma pjmA_frm_blk : forall ly S Hp W mem md b m cid pos x,
  ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  b <= x < b + req_size m -> ~ (frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid).
Proof.
intros ly S Hp W mem md b m cid pos x HAR Hb Hf Hx Hx'.
destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as [Hpw _].
pose proof (pjmA_pw_cross zdisjoint _ _ (b, req_size m) (frame_addr ly cid pos, fs_frame_bytes cid) Hpw
  (in_map (fun b => (fst b, req_size (snd b))) _ (b, m) Hb)
  (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos) Hf)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* a block listed twice in a permutation of the live blocks: impossible *)
Lemma pjmA_dup : forall ly S Hp W mem md (L1 L2 : list (Z * Z)) x,
  ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (L1 ++ L2) -> In x L1 -> In x L2 -> 0 <= snd x -> False.
Proof.
intros ly S Hp W mem md L1 L2 x HAR HP H1 H2 Hx.
destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as [Hpw _].
apply pairwise_app_l in Hpw as [Hpw _].
assert (Hpw' : YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (L1 ++ L2)))
  by exact (prh_pw_perm zdisjoint _ _ prh_zdisjoint_sym (Permutation_map _ HP) Hpw).
rewrite map_app in Hpw'.
pose proof (pjmA_pw_cross zdisjoint _ _ _ _ Hpw' (in_map (fun b => (fst b, req_size (snd b))) _ x H1)
  (in_map (fun b => (fst b, req_size (snd b))) _ x H2)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. pose proof (pjsA_req (snd x) Hx) as (_ & R1 & _). lia.
Qed.

(* a struct placed by prhReader_at, whose containers live on and differ from a live block, is off that block *)
Lemma pjmA_at_disj : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) e p
    ly2 S2 Hp2 W2 mem2 md2 b0 m0,
  ARx ly S Hp W mem md -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p 56 -> YM05.alloc_ceiling <= spZ regs ->
  frames S2 = frames S -> (forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos) ->
  In (b0, m0) (ablocks B ly2 S2) ->
  (forall a k, In (a, k) Lam -> a <= p -> p + 56 <= a + k ->
     In (a - cf_head, k + cf_head) (ablocks B ly2 S2) /\ (a - cf_head, k + cf_head) <> (b0, m0)) ->
  (forall b m, In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam -> b <= p -> p + 56 <= b + m ->
     In (b, m) (ablocks B ly2 S2) /\ (b, m) <> (b0, m0)) ->
  forall x, p <= x < p + 56 -> ~ (b0 <= x < b0 + req_size m0).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e p ly2 S2 Hp2 W2 mem2 md2 b0 m0
  HAR HAR2 HL Hat Hsp Efr Efa Hb0 HSL HSB x Hx Hx0.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hbm & HnL & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
- destruct (HSL a k Hin H1 H2) as (Hab2 & Hne).
  destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk0 & _).
  pose proof (pjsA_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
  apply (pjmA_blk_disj ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ x HAR2 Hab2 Hb0 Hne); [lia | exact Hx0].
- destruct (HSB b m Hbm HnL H1 H2) as (Hbm2 & Hne).
  pose proof (pjsA_req m ltac:(lia)) as (Rm & _).
  apply (pjmA_blk_disj ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ x HAR2 Hbm2 Hb0 Hne); [lia | exact Hx0].
- rewrite <- Efr in Hcp. rewrite <- Efa in H1, H2.
  apply (pjmA_frm_blk ly2 S2 Hp2 W2 mem2 md2 b0 m0 cid pos x HAR2 Hb0 Hcp Hx0). lia.
- destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b0 m0 HAR2 Hb0) as (_ & _ & Hcl & _). lia.
Qed.

(* a block with a byte off the callee's footprint is live after the call *)
Lemma pjmA_blk_live : forall STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n x,
  AJ STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> p <= x < p + req_size n -> ~ inFP FP x -> In (p, n) (ablocks B ly' S').
Proof.
intros STK sp FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n x HJ Hin Hx Hf.
pose proof (ajxR_gone HJ) as Hgone.
assert (Hdec : forall u v : Z * Z, {u = v} + {u <> v}).
{ intros [u1 u2] [v1 v2]. destruct (Z.eq_dec u1 v1) as [E1|E1]; destruct (Z.eq_dec u2 v2) as [E2|E2];
  [left; subst; reflexivity | right; congruence | right; congruence | right; congruence]. }
destruct (in_dec Hdec (p, n) (ablocks B ly' S')) as [H|H]; [exact H|].
exfalso. apply Hf. replace x with (p + (x - p)) by lia. apply (Hgone p n (x - p) Hin H). lia.
Qed.

(* the bytes of harness blocks whose user bytes are off the callee's footprint agree across the call *)
Lemma pjmA_blks_agree : forall ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly' S' Hp' W' mem' md' k1
    (X : list (Z * Z)),
  AJ STK1 sp FP1 ly S Hp W mem md [] ly' S' Hp' W' mem' md' k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a k, In (a, k) X -> In (a, k) Lam) ->
  (forall b x, In b X -> pj_holdsR b x -> ~ inFP FP1 x) ->
  pj_agreeR SEGS (rdW W mem) (rdW W' mem') (fun x => exists b, In b X /\ pj_holdsR b x).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly' S' Hp' W' mem' md' k1 X HJ HL HX HF x ((a, k) & Hb & Hx).
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_blk HJ) as F2.
pose proof (HF (a, k) x Hb Hx) as Hnf.
unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL (HX a k Hb)) as (Hk0 & Hab).
pose proof (pjmA_req_eq (k + @cf_head cp) ltac:(lia)) as Rq.
assert (Hab2 : In (a - cf_head, k + cf_head) (ablocks B ly' S'))
  by (apply (pjmA_blk_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x HJ Hab); [rewrite Rq; lia | exact Hnf]).
destruct (alx_blocks SEGS B ARx LAWS ly' S' Hp' W' mem' md' _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hpo & _).
split.
- apply (mbyte_of_aview SEGS). replace x with (a - cf_head + (x - (a - cf_head))) by lia.
  apply (F2 _ _ _ Hab Hab2); [rewrite Rq; lia|]. replace (a - cf_head + (x - (a - cf_head))) with x by lia. exact Hnf.
- intros _. apply (apresent_writable SEGS). apply (proj1 (Hpo x ltac:(rewrite Rq; lia))).
Qed.

(* the bytes of a struct placed by prhReader_at, off the callee's footprint, agree across the call; on the caller's
   real stack by the call rule's extension clause *)
Lemma pjmA_at_agree : forall ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly' S' Hp' W' mem' md' k1
    (regs : bvmap 5 word) e p,
  AJ STK1 sp FP1 ly S Hp W mem md [] ly' S' Hp' W' mem' md' k1 ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p 56 ->
  (forall x, p <= x < p + 56 -> ~ inFP FP1 x) ->
  (forall x, spZ regs <= x < spZ regs + e -> ~ inFP FP1 x -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  (forall x, spZ regs <= x < spZ regs + e -> apresent (w_H W') mem' x) ->
  pj_agreeR SEGS (rdW W mem) (rdW W' mem') (fun x => p <= x < p + 56).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own STK1 sp FP1 ly' S' Hp' W' mem' md' k1 regs e p HJ HL Hat HF HX HPR x Hx.
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_frs HJ) as Hfr. pose proof (ajxR_blk HJ) as F2. pose proof (ajxR_frm HJ) as F4.
specialize (HF x Hx).
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hbm & _ & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
- destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk0 & Hab).
  pose proof (pjmA_req_eq (k + @cf_head cp) ltac:(lia)) as Rq.
  assert (Hab2 : In (a - cf_head, k + cf_head) (ablocks B ly' S'))
    by (apply (pjmA_blk_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x HJ Hab); [rewrite Rq; lia | exact HF]).
  destruct (alx_blocks SEGS B ARx LAWS ly' S' Hp' W' mem' md' _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hpo & _).
  split.
  + apply (mbyte_of_aview SEGS). replace x with (a - cf_head + (x - (a - cf_head))) by lia.
    apply (F2 _ _ _ Hab Hab2); [rewrite Rq; lia|]. replace (a - cf_head + (x - (a - cf_head))) with x by lia. exact HF.
  + intros _. apply (apresent_writable SEGS). apply (proj1 (Hpo x ltac:(rewrite Rq; lia))).
- pose proof (pjmA_req_eq m ltac:(lia)) as Rm.
  assert (Hbm2 : In (b, m) (ablocks B ly' S'))
    by (apply (pjmA_blk_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x HJ Hbm); [rewrite Rm; lia | exact HF]).
  destruct (alx_blocks SEGS B ARx LAWS ly' S' Hp' W' mem' md' _ _ HAR2 Hbm2) as (_ & _ & _ & _ & Hpo & _).
  split.
  + apply (mbyte_of_aview SEGS). replace x with (b + (x - b)) by lia.
    apply (F2 _ _ _ Hbm Hbm2); [rewrite Rm; lia|]. replace (b + (x - b)) with x by lia. exact HF.
  + intros _. apply (apresent_writable SEGS). apply (proj1 (Hpo x ltac:(rewrite Rm; lia))).
- assert (Efa : forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos).
  { intros cid' pos'. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  rewrite app_nil_l in Hfr.
  assert (Hcp2 : In (cid, pos) (frames S')) by (rewrite Hfr; exact Hcp).
  destruct (alx_frames SEGS B ARx LAWS ly' S' Hp' W' mem' md' cid pos HAR2 Hcp2) as (_ & _ & Hfpo & _).
  rewrite Efa in Hfpo.
  split.
  + apply (mbyte_of_aview SEGS). apply (F4 cid pos x Hcp); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HF].
  + intros _. apply (apresent_writable SEGS). apply (proj1 (Hfpo x ltac:(lia))).
- split.
  + apply (mbyte_of_aview SEGS). apply HX; [lia | exact HF].
  + intros _. apply (apresent_writable SEGS). apply HPR. lia.
Qed.

(* the bytes of a harness block are present *)
Lemma pjmA_lam_some : forall ly S Hp W mem md Lam peak cnt fail ran most own a k j,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam ->
  0 <= j < k -> mbyte SEGS (rdW W mem) (a + j) <> None.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k j HAR HL Hin Hj.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk0 & Hab).
pose proof (pjmA_req_eq (k + @cf_head cp) ltac:(lia)) as Rq.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & _ & Hpo & _).
rewrite Rq in Hpo.
pose proof (aview_some_of_apresent SEGS _ _ _ (proj1 (Hpo (a + j) ltac:(lia)))) as Hs.
unfold aview in Hs. intros E. rewrite E in Hs. exact (Hs eq_refl).
Qed.

(* the harness blocks of the ledger are distinct live blocks: the rest of the live blocks *)
Lemma pjmA_blocks_other : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  exists other, Permutation (ablocks B ly S) (prhPj_hbl Lam ++ other).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own HL. apply pjmA_perm_incl.
- pose proof HL as (_ & HN & _). apply pjmA_nd. unfold prhPj_hbl. exact (prh_nodup_blocks cf_head Lam HN).
- intros [b m] Hb. apply pjmA_hbl_inv in Hb.
  destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own _ _ HL Hb) as (_ & Hab).
  replace (b, m) with (b + cf_head - cf_head, m - cf_head + cf_head) by (f_equal; lia). exact Hab.
Qed.

(* the ledger holds the object's and the value's blocks, disjoint *)
Lemma pjmA_perm_lam : forall (Lam D Dw : list (Z * Z)), NoDup D -> NoDup Dw -> (forall bk, In bk Dw -> ~ In bk D) ->
  (forall a k, In (a, k) D -> In (a, k) Lam) -> (forall a k, In (a, k) Dw -> In (a, k) Lam) ->
  exists Lr, Permutation Lam (D ++ Dw ++ Lr).
Proof.
intros Lam D Dw HD HDw Hdis HL HLw.
destruct (pjmA_perm_incl (D ++ Dw) Lam) as (Lr & HP).
- apply pjmA_nodup_app; [apply pjmA_nd; exact HD | apply pjmA_nd; exact HDw|]. intros x Hx Hx'. exact (Hdis x Hx' Hx).
- intros [a k] Hx. apply in_app_or in Hx as [Hx|Hx]; [exact (HL a k Hx) | exact (HLw a k Hx)].
- exists Lr. rewrite <- app_assoc in HP. exact HP.
Qed.

(* grow's block swap (PRH_FnReader.v prhReader_swap): what stays *)
Lemma pjmA_swap_lam : forall (Lam Lam2 Lam0 Dx Dn : list (Z * Z)) a k,
  Permutation Lam (Dx ++ Lam0) -> Permutation Lam2 (Dn ++ Lam0) -> In (a, k) Lam -> ~ In (a, k) Dx -> In (a, k) Lam2.
Proof.
intros Lam Lam2 Lam0 Dx Dn a k H1 H2 Hin Hn. apply (Permutation_in _ (Permutation_sym H2)). apply in_or_app. right.
apply (Permutation_in _ H1) in Hin. apply in_app_or in Hin as [Hin|Hin]; [contradiction | exact Hin].
Qed.

Lemma pjmA_swap_blk : forall ly S ly2 S2 Hp2 W2 mem2 md2 (Lam Lam2 Lam0 Dx Dn bl : list (Z * Z)) b m,
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  Permutation Lam (Dx ++ Lam0) -> Permutation Lam2 (Dn ++ Lam0) ->
  Permutation (ablocks B ly S) (prhPj_hbl Dx ++ bl) -> Permutation (ablocks B ly2 S2) (prhPj_hbl Dn ++ bl) ->
  In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam -> 0 <= m ->
  In (b, m) (ablocks B ly2 S2) /\ ~ In (b + cf_head, m - cf_head) Lam2.
Proof.
intros ly S ly2 S2 Hp2 W2 mem2 md2 Lam Lam2 Lam0 Dx Dn bl b m HAR2 H1 H2 H3 H4 Hin Hn Hm.
assert (Hbl : In (b, m) bl).
{ apply (Permutation_in _ H3) in Hin. apply in_app_or in Hin as [Hin|Hin]; [|exact Hin].
  exfalso. apply Hn. apply (Permutation_in _ (Permutation_sym H1)). apply in_or_app. left. exact (pjmA_hbl_inv Dx b m Hin). }
split; [apply (Permutation_in _ (Permutation_sym H4)); apply in_or_app; right; exact Hbl|].
intros Hin2. apply (Permutation_in _ H2) in Hin2. apply in_app_or in Hin2 as [Hin2|Hin2].
- apply (pjmA_dup ly2 S2 Hp2 W2 mem2 md2 (prhPj_hbl Dn) bl (b, m) HAR2 H4); [|exact Hbl | exact Hm].
  pose proof (pjmA_hbl_in Dn _ _ Hin2) as E.
  replace (b + cf_head - cf_head, m - cf_head + cf_head) with (b, m) in E by (f_equal; lia). exact E.
- apply Hn. apply (Permutation_in _ (Permutation_sym H1)). apply in_or_app. right. exact Hin2.
Qed.

Lemma pjmA_swap_new : forall ly S ly2 S2 Hp2 W2 mem2 md2 (Dx Dn bl : list (Z * Z)) a k,
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  Permutation (ablocks B ly S) (prhPj_hbl Dx ++ bl) -> Permutation (ablocks B ly2 S2) (prhPj_hbl Dn ++ bl) ->
  In (a, k) Dn -> ~ In (a, k) Dx -> 0 <= k + cf_head ->
  ~ In (a - cf_head, k + cf_head) (ablocks B ly S).
Proof.
intros ly S ly2 S2 Hp2 W2 mem2 md2 Dx Dn bl a k HAR2 H3 H4 Hin Hnx Hk Hab.
apply (Permutation_in _ H3) in Hab. apply in_app_or in Hab as [Hab|Hab].
- apply pjmA_hbl_inv in Hab.
  replace (a - cf_head + cf_head, k + cf_head - cf_head) with (a, k) in Hab by (f_equal; lia). exact (Hnx Hab).
- exact (pjmA_dup ly2 S2 Hp2 W2 mem2 md2 (prhPj_hbl Dn) bl _ HAR2 H4 (pjmA_hbl_in Dn a k Hin) Hab Hk).
Qed.

(* the object pj_free reads: freeable to the depth of its tree from its header, its kids block, its keys block (or
   none) and its members *)
Lemma pjmA_fd_obj : forall (m : word -> option byte) lblk o num kids keys n cap
    (ms : list (list Z * PjTree.jv)) Di Do kk Dy,
  pj_hdrR SEGS m o 6 num 0 kids keys n cap ->
  n = Z.of_nat (length ms) -> lblk kids kk -> 56 * n <= kk ->
  (keys = 0 /\ ms = [] /\ Dy = [] \/ exists ky, lblk keys ky /\ 8 * n <= ky /\ Dy = [(keys, ky)]) ->
  pj_memsR SEGS m lblk (pj_nodeR SEGS m lblk) kids keys ms Di ->
  NoDup Do -> pj_apartR Do o -> Permutation Do ((kids, kk) :: Dy ++ Di) ->
  pj_fdR SEGS m lblk (PjTree.depth (PjTree.JObj ms)) o Do.
Proof.
intros m lblk o num kids keys n cap ms Di Do kk Dy Hh En Hk Hkk Hy HM HN HA HP.
remember (PjTree.depth (PjTree.JObj ms)) as dm eqn:Edm.
destruct dm as [|d']; [cbn [PjTree.depth] in Edm; discriminate Edm|].
cbn [pj_fdR]. unfold pj_fshapeR.
split; [exact HN|]. split; [exact HA|].
destruct Hy as [(Ey & Em & ED) | (ky & Hky & Hky8 & ED)].
- subst ms Dy. cbn [pj_memsR] in HM. subst Di. cbn [length] in En. subst n.
  exists 6, num, 0, kids, keys, 0, cap, false, [], [(kids, kk)], [], [].
  split; [exact Hh|]. split; [left; split; reflexivity|].
  split; [right; exists kk; split; [exact Hk | split; [lia | reflexivity]]|].
  split; [left; split; [exact Ey | split; reflexivity]|].
  split; [cbn [app] in HP |- *; exact HP|]. cbv beta. reflexivity.
- exists 6, num, 0, kids, keys, n, cap, true, [], [(kids, kk)], [(keys, ky)], Di.
  split; [exact Hh|]. split; [left; split; reflexivity|].
  split; [right; exists kk; split; [exact Hk | split; [exact Hkk | reflexivity]]|].
  split; [right; split; [reflexivity | exists ky; split; [exact Hky | split; [exact Hky8 | reflexivity]]]|].
  split; [subst Dy; cbn [app] in HP |- *; exact HP|].
  cbv beta. rewrite En, Nat2Z.id. apply (PjpTree.pjg_mems_pf SEGS m lblk (pj_nodeR SEGS m lblk)); [|exact HM].
  intros a u D1 (nm & Hu) HP1.
  apply (PjpTree.pjg_fd_mono SEGS m lblk (PjTree.depth u)); [|exact (PjpTree.pjg_node_fd SEGS u m lblk a D1 HP1)].
  pose proof (PjTree.depth_member ms nm u Hu). lia.
Qed.

(* a harness block's user bytes are off every other harness block of the ledger *)
Lemma pjmA_lam_off : forall ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> In (a', k') Lam -> (a', k') <> (a, k) -> a' <= x < a' + k' ->
  ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head)).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k a' k' x HAR HL Hin Hin' Hne Hx.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk0 & Hab).
destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a' k' HL Hin') as (Hk0' & Hab').
pose proof (pjsA_req (k' + @cf_head cp) ltac:(lia)) as (Rq' & _).
apply (pjmA_blk_disj ly S Hp W mem md _ _ _ _ x HAR Hab' Hab); [|lia].
intros E. injection E as E1 E2. apply Hne. f_equal; lia.
Qed.

(* a struct placed by prhReader_at and off a harness block's user bytes is off its whole allocator block *)
Lemma pjmA_at_off : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) e p a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p 56 -> YM05.alloc_ceiling <= spZ regs ->
  In (a, k) Lam -> (forall x, p <= x < p + 56 -> ~ (a <= x < a + k)) ->
  forall x, p <= x < p + 56 -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head)).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e p a k HAR HL Hat Hsp Hin Hoff.
destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk0 & Hab).
apply (pjmA_at_disj ly S Hp W mem md Lam peak cnt fail ran most own regs e p ly S Hp W mem md _ _ HAR HAR HL Hat Hsp eq_refl
  (fun _ _ => eq_refl) Hab).
- intros a' k' Hin' H1 H2. destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a' k' HL Hin') as (_ & Hab').
  split; [exact Hab'|]. intros E. injection E as E1 E2. apply (Hoff p ltac:(lia)). lia.
- intros b m Hbm HnL H1 H2. split; [exact Hbm|]. intros E. injection E as E1 E2. apply HnL.
  replace (b + cf_head, m - cf_head) with (a, k) by (f_equal; lia). exact Hin.
Qed.

(* the key (kept_at) and off a harness block's user bytes is off its whole allocator block *)
Lemma pjmA_key_off : forall ly S Hp W mem md Lam peak cnt fail ran most own p n a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  kept_at (PA := PA) B Lam p n -> 0 < n ->
  In (a, k) Lam -> (forall x, p <= x < p + n -> ~ (a <= x < a + k)) ->
  forall x, p <= x < p + n -> ~ (a - cf_head <= x < a - cf_head + req_size (k + cf_head)).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p n a k HAR HL Hka Hn Hin Hoff x Hx.
destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk0 & Hab).
destruct Hka as [(b & m & Hbm & H1 & H2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]].
- apply (pjmA_lam_off ly S Hp W mem md Lam peak cnt fail ran most own a k b m x HAR HL Hin Hbm); [|lia].
  intros E. injection E as E1 E2. subst b m. exact (Hoff p ltac:(lia) ltac:(lia)).
- intros Hx'. destruct (Hro x Hx) as (Hr & _).
  exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HAR Hab Hx' (pjsA_ro_img x Hr)).
- intros Hx'. destruct (Hro x Hx) as (Hr & _).
  exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ x HAR Hab Hx' (pjsA_ro_img x Hr)).
Qed.

(* the bytes of a placed struct are application bytes, off the shadow region *)
Lemma pjmA_at_app : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs : bvmap 5 word) e p,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e p 56 -> YM05.alloc_ceiling <= spZ regs ->
  forall x, p <= x < p + 56 -> x < kLowShadowBeg \/ kHighMemBeg <= x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs e p HAR HL Hat Hsp x Hx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hbm & _ & H1 & H2) | [(cid & pos & Hcp & H1 & H2) | (H1 & H2)]]].
- destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk0 & Hab).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & Happ & _).
  pose proof (pjsA_req (k + @cf_head cp) ltac:(lia)) as (Rq & _).
  pose proof (in_app_addr _ _ x Happ ltac:(lia)) as (_ & Hx'). lia.
- destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hbm) as (_ & _ & _ & Happ & _).
  pose proof (pjsA_req m ltac:(lia)) as (Rm & _).
  pose proof (in_app_addr _ _ x Happ ltac:(lia)) as (_ & Hx'). lia.
- destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hcp) as (_ & _ & Happ).
  pose proof (in_app_addr _ _ x Happ ltac:(lia)) as (_ & Hx'). lia.
- right. unfold kHighMemBeg. lia.
Qed.

Lemma pjmA_lam_writable : forall ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> a <= x < a + k -> writable_at SEGS (rdW W mem) x.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k x HAR HL Hin Hx.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (pjmA_lam_blk ly S Hp W mem Lam peak cnt fail ran most own a k HL Hin) as (Hk0 & Hab).
pose proof (pjmA_req_eq (k + @cf_head cp) ltac:(lia)) as Rq.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & _ & Hpo & _).
rewrite Rq in Hpo. apply (apresent_writable SEGS). exact (proj1 (Hpo x ltac:(lia))).
Qed.

(* the ledger's block split across grow's swap *)
Lemma pjmA_blocks_swap : forall ly S ly2 S2 (Lam Lam2 Lam0 Dx Dn bl other : list (Z * Z)),
  Permutation Lam (Dx ++ Lam0) -> Permutation Lam2 (Dn ++ Lam0) ->
  Permutation (ablocks B ly S) (prhPj_hbl Dx ++ bl) -> Permutation (ablocks B ly2 S2) (prhPj_hbl Dn ++ bl) ->
  Permutation (ablocks B ly S) (prhPj_hbl Lam ++ other) ->
  Permutation (ablocks B ly2 S2) (prhPj_hbl Lam2 ++ other).
Proof.
intros ly S ly2 S2 Lam Lam2 Lam0 Dx Dn bl other H1 H2 H3 H4 H5.
assert (E1 : Permutation (prhPj_hbl Lam) (prhPj_hbl Dx ++ prhPj_hbl Lam0))
  by (unfold prhPj_hbl; rewrite <- map_app; apply Permutation_map; exact H1).
assert (E2 : Permutation (prhPj_hbl Lam2) (prhPj_hbl Dn ++ prhPj_hbl Lam0))
  by (unfold prhPj_hbl; rewrite <- map_app; apply Permutation_map; exact H2).
assert (Ebl : Permutation bl (prhPj_hbl Lam0 ++ other)).
{ apply (Permutation_app_inv_l (prhPj_hbl Dx)). rewrite app_assoc.
  apply (Permutation_trans (Permutation_sym H3)). apply (Permutation_trans H5).
  apply Permutation_app_tail. exact E1. }
apply (Permutation_trans H4). apply (Permutation_trans (Permutation_app_head _ Ebl)).
rewrite app_assoc. apply Permutation_app_tail. apply Permutation_sym. exact E2.
Qed.


(* what pj_free(val) keeps of the object's footprint (pjsA_FAILc's obligation): its header by the caller window's
   extension clause or its block, its blocks by the block clause; pj_free writes val's header and val's blocks *)
Lemma pjmA_free_agree : forall dd en ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 (X : list (Z * Z))
    md0 ly3 S3 Hp3 W3 mem3 md3 k3,
  YM05.alloc_ceiling <= jsA_sp0 en -> 0 <= STK_pj_free dd ->
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  prhReader_at B ly2 S2 Lam2 (jsA_regs en) (jsA_d en) (jsA_o en) 56 ->
  (forall a k, In (a, k) X -> In (a, k) Lam2) -> (forall a k, In (a, k) (jsA_Dw en) -> In (a, k) Lam2) ->
  (forall bk, In bk (jsA_Dw en) -> ~ In bk X) -> pj_apartR (jsA_Dw en) (jsA_o en) ->
  (forall x, jsA_w en <= x < jsA_w en + 56 -> ~ pj_footR (jsA_o en) X x) ->
  AJ (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en)
     ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) ly2 S2 Hp2 W2 mem2 md0 [] ly3 S3 Hp3 W3 mem3 md3 k3 ->
  (forall a, jsA_sp1 en <= a < jsA_sp0 en + jsA_d en ->
     ~ inFP ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) a ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  pj_agreeR SEGS (rdW W2 mem2) (rdW W3 mem3) (pj_footR (jsA_o en) X).
Proof.
intros dd en ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 X md0 ly3 S3 Hp3 W3 mem3 md3 k3
  Hsp HSTKF HAR HL Hat HXL HDwL HDis HApw HWO' HJf HXf.
pose proof (ajxR_pres HJf) as HPf.
apply (pjmA_agree_foot SEGS).
- apply (pjmA_at_agree ly2 S2 Hp2 W2 mem2 md0 Lam2 peak2 cnt2 fail2 ran2 most2 own2 _ _ _ ly3 S3 Hp3 W3 mem3 md3 k3
    (jsA_regs en) (jsA_d en) (jsA_o en) HJf HL Hat).
  + intros x Hx Hin. apply inFP_cons in Hin as [Hin|Hin].
    * apply (HWO' x Hin). left. exact Hx.
    * destruct (pjmA_inFP_hbl _ _ Hin) as (a & k & Ha & Hr).
      exact (pjmA_at_off ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 (jsA_regs en) (jsA_d en) (jsA_o en) a k
        HAR HL Hat Hsp (HDwL a k Ha) (fun y Hy Hy' => HApw (a, k) y Ha Hy' Hy) x Hx Hr).
  + intros x Hx Hn. apply HXf; [unfold jsA_sp1, jsA_sp0, PJSA_FR in *; lia | exact Hn].
  + intros x Hx. apply HPf. unfold jsA_sp0 in *. lia.
- apply (pjmA_blks_agree ly2 S2 Hp2 W2 mem2 md0 Lam2 peak2 cnt2 fail2 ran2 most2 own2 _ _ _ ly3 S3 Hp3 W3 mem3 md3 k3 X HJf HL HXL).
  intros [a k] x Hb Hx Hin. apply inFP_cons in Hin as [Hin|Hin].
  + apply (HWO' x Hin). right. exists (a, k). split; [exact Hb | exact Hx].
  + destruct (pjmA_inFP_hbl _ _ Hin) as (a' & k' & Ha' & Hr).
    apply (pjmA_lam_off ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 a' k' a k x HAR HL (HDwL a' k' Ha') (HXL a k Hb));
      [| exact Hx | exact Hr].
    intros E. apply (HDis (a', k') Ha'). rewrite <- E. exact Hb.
Qed.

(* the object as a whole tree across pj_free(val) *)
Lemma pjmA_obl_node : forall dd en ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 md0 ly3 S3 Hp3 W3 mem3 md3 k3
    Lam3 Lr t D,
  YM05.alloc_ceiling <= jsA_sp0 en -> 0 <= STK_pj_free dd ->
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  prhReader_at B ly2 S2 Lam2 (jsA_regs en) (jsA_d en) (jsA_o en) 56 ->
  (forall a k, In (a, k) D -> In (a, k) Lam2) -> (forall a k, In (a, k) (jsA_Dw en) -> In (a, k) Lam2) ->
  (forall bk, In bk (jsA_Dw en) -> ~ In bk D) -> pj_apartR (jsA_Dw en) (jsA_o en) ->
  (forall x, jsA_w en <= x < jsA_w en + 56 -> ~ pj_footR (jsA_o en) D x) ->
  AJ (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en)
     ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) ly2 S2 Hp2 W2 mem2 md0 [] ly3 S3 Hp3 W3 mem3 md3 k3 ->
  (forall a, jsA_sp1 en <= a < jsA_sp0 en + jsA_d en ->
     ~ inFP ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) a ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam2) (jsA_o en) t D -> Permutation Lam3 (D ++ Lr) ->
  pj_nodeR SEGS (rdW W3 mem3) (prh_lin Lam3) (jsA_o en) t D.
Proof.
intros dd en ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 md0 ly3 S3 Hp3 W3 mem3 md3 k3 Lam3 Lr t D
  Hsp HSTKF HAR HL Hat HXL HDwL HDis HApw HWO' HJf HXf HN HP3.
apply (pjst_node_frame SEGS t (rdW W2 mem2) (rdW W3 mem3) (prh_lin Lam2) (prh_lin Lam3) (jsA_o en) D HN).
- exact (pjmA_free_agree dd en ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 D md0 ly3 S3 Hp3 W3 mem3 md3 k3
    Hsp HSTKF HAR HL Hat HXL HDwL HDis HApw HWO' HJf HXf).
- intros a k H. apply (Permutation_in _ (Permutation_sym HP3)). apply in_or_app. left. exact H.
Qed.

(* the object after a half-done grow (kids moved, keys not), from its header and members, freeable after
   pj_free(val) *)
Lemma pjmA_obl_parts : forall dd en ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 md0 ly3 S3 Hp3 W3 mem3 md3 k3
    Lam3 Lr num kid keys n cap kk (ms : list (list Z * PjTree.jv)) Di Do,
  YM05.alloc_ceiling <= jsA_sp0 en -> 0 <= STK_pj_free dd ->
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  prhReader_at B ly2 S2 Lam2 (jsA_regs en) (jsA_d en) (jsA_o en) 56 ->
  (forall a k, In (a, k) Do -> In (a, k) Lam2) -> (forall a k, In (a, k) (jsA_Dw en) -> In (a, k) Lam2) ->
  (forall bk, In bk (jsA_Dw en) -> ~ In bk Do) -> pj_apartR (jsA_Dw en) (jsA_o en) ->
  (forall x, jsA_w en <= x < jsA_w en + 56 -> ~ pj_footR (jsA_o en) Do x) ->
  AJ (STK_pj_free dd + (48 + jsA_d en)) (jsA_sp0 en + jsA_d en)
     ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) ly2 S2 Hp2 W2 mem2 md0 [] ly3 S3 Hp3 W3 mem3 md3 k3 ->
  (forall a, jsA_sp1 en <= a < jsA_sp0 en + jsA_d en ->
     ~ inFP ((jsA_w en, jsA_w en + 56) :: ablocks_fp (prhPj_hbl (jsA_Dw en))) a ->
     aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  pj_hdrR SEGS (rdW W2 mem2) (jsA_o en) 6 num 0 kid keys n cap ->
  pj_memsR SEGS (rdW W2 mem2) (prh_lin Lam2) (pj_nodeR SEGS (rdW W2 mem2) (prh_lin Lam2)) kid keys ms Di ->
  n = Z.of_nat (length ms) -> n <= cap -> (cap = 0 -> keys = 0) -> 56 * n <= kk ->
  Do = (kid, kk) :: keys_blkR 6 keys cap ++ Di -> NoDup Do -> pj_apartR Do (jsA_o en) ->
  Permutation Lam3 (Do ++ Lr) ->
  pj_fdR SEGS (rdW W3 mem3) (prh_lin Lam3) (PjTree.depth (PjTree.JObj ms)) (jsA_o en) Do.
Proof.
intros dd en ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 md0 ly3 S3 Hp3 W3 mem3 md3 k3 Lam3 Lr
  num kid keys n cap kk ms Di Do Hsp HSTKF HAR HL Hat HXL HDwL HDis HApw HWO' HJf HXf Hh HM En Hnc Hk0 Hkk ED HN HA HP3.
pose proof (pjmA_free_agree dd en ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 Do md0 ly3 S3 Hp3 W3 mem3 md3 k3
  Hsp HSTKF HAR HL Hat HXL HDwL HDis HApw HWO' HJf HXf) as HAG.
assert (HL3 : forall a k, In (a, k) Do -> prh_lin Lam3 a k)
  by (intros a k H; apply (Permutation_in _ (Permutation_sym HP3)); apply in_or_app; left; exact H).
assert (Hn0 : 0 <= n) by lia.
apply (pjmA_fd_obj (rdW W3 mem3) (prh_lin Lam3) (jsA_o en) num kid keys n cap ms Di Do kk (keys_blkR 6 keys cap)).
- apply (pj_hdrR_frame SEGS (rdW W2 mem2)); [exact Hh|]. apply (pjmA_agree_sub SEGS _ _ _ _ HAG). intros x Hx. left. exact Hx.
- exact En.
- apply HL3. rewrite ED. left. reflexivity.
- exact Hkk.
- destruct (Z.eq_dec cap 0) as [E0|E0].
  + left. split; [exact (Hk0 E0)|]. split.
    * destruct ms as [|mb ms']; [reflexivity | cbn [length] in En; lia].
    * subst cap. reflexivity.
  + right. exists (8 * cap).
    assert (Ek : keys_blkR 6 keys cap = [(keys, 8 * cap)]) by (unfold keys_blkR; rewrite (proj2 (Z.eqb_neq cap 0) E0); reflexivity).
    split; [apply HL3; rewrite ED; right; rewrite Ek; left; reflexivity|]. split; [lia | exact Ek].
- apply (pjst_mems_frame SEGS ms (rdW W2 mem2) (rdW W3 mem3) (prh_lin Lam2) (prh_lin Lam3) kid keys Di HM).
  + apply (pjmA_agree_sub SEGS _ _ _ _ HAG). intros x [Hx|[Hx|(b & Hb & Hx)]].
    * right. exists (kid, kk). split; [rewrite ED; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
    * right. destruct (Z.eq_dec cap 0) as [E0|E0]; [lia|].
      exists (keys, 8 * cap). split; [|unfold pj_holdsR; cbn [fst snd]; lia].
      rewrite ED. right. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq cap 0) E0). left. reflexivity.
    * right. exists b. split; [rewrite ED; right; apply in_or_app; right; exact Hb | exact Hx].
  + intros a k H. apply HL3. rewrite ED. right. apply in_or_app. right. exact H.
- exact HN.
- exact HA.
- rewrite ED. reflexivity.
Qed.

End q.

(* one concrete `beq` step at a listing offset (pj_setA_seg_tail.v's step lemmas, with YK11.v step_beq_tk /
   step_beq_ft) *)
Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Lemma pjmA_step_beq : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rs1 rs2 : bv 5) (imm : bv 13),
  clookup (@pa_tbl _ A_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx regs
     (if c_eq (getr regs rs1) (getr regs rs2) then btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm)
      else v_addi (Z_to_bv 64 (BASE + k)) 4) mem (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rs1 rs2 imm Hl Hd HK.
destruct (c_eq (getr regs rs1) (getr regs rs2)) eqn:Hc; try rewrite Hc in HK.
- eapply (SRr_step SEGS (@pa_wx _ A_prog_listing PA) W); [reflexivity | |].
  + rewrite (restrict_mkst_fx (fx := fx)).
    exact (step_beq_tk (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
      (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok (PI := PA) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate))
      Hd Hc).
  + intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
    cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
- eapply (SRr_step SEGS (@pa_wx _ A_prog_listing PA) W); [reflexivity | |].
  + rewrite (restrict_mkst_fx (fx := fx)).
    exact (step_beq_ft (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
      (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok (PI := PA) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate))
      Hd Hc).
  + intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
    cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.
End st.
