(* fuzz_preset, slice S5b (the S3 walk, a Theorem Labs lane): the ONE `vrd_inode -> pj_fdR` lemma every res = -1 exit of
   parse_items' loop needs for vrd_iexit_a (a Theorem Labs lane's assignment, 2026-10-29: the S3 walk writes it once; IelemB, the Ival walk,
   IproD, IelemE and PI-key cite it).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). A shape lemma over VrdIElem.v's boundary predicates.
   THE VIEW. The conclusion is at the position's own view: rdW (ip_W P) (ip_mem P) = mrestrict (w_H (ip_W P))
   (ip_mem P), the memory the position's vrd_inode is stated over; nothing moves memory here.
   THE PIECES, and which premise supplies each:
   - the header, the kids / keys arrays (prh_lin (ip_Lam P)), the member / item trees and D's split: vrd_inode E P []
     (VrdIElem.v), turned into pj_fshapeR by VrdFrame.v's vrd_fd_mems (object) / vrd_fd_items (array), each element a
     complete tree freeable to its depth (vrd_nodefd_all);
   - the depth: MAXD - d = S (MAXD - S d), since the cursor's depth word d + 1 is at most 32 (vrd_icur's pj_in_okR,
     its last conjunct), and every element's depth is at most MAXD - S d (vrd_imodel);
   - NoDup (ip_D P): the LEDGER's NoDup over the position's Lam (vrd_icur's prh_ledger, second conjunct), through
     rd_ledger_move's Permutation Lam' (D ++ Lam) (vrd_imodel, third conjunct);
   - pj_apartR (ip_D P) v: rd_pre's node facts (vrd_ient_ok): prhPv_node's prhReader_at gives the node's home at
     the entry (a harness block of the entry ledger, an allocator block, a fake frame, or the caller window), the
     window case is excluded by rd_pre's `v + 56 <= sp \/ sp + e <= v`; each D block is a NEW allocator block
     (rd_blocks_move: not in the entry's ablocks, in the position's), so it is disjoint from the home block by
     sep_blocks_x and from the home frame by AR_laws_x's alx_sep (frame addresses kept by the journal's layout_le).
   The empty node (cap = 0) is the same construction with no element (IproD's vrd_hdr_fd needs a header with every
   field zero; here the header is vrd_inode's, so it is not used).
   SET: a working branch on ival db50bd6cd2f / ielem da5334ad793; texts on walkkit-next 0afb3f76c28
   (S5b preset-tree-at-2026-10-29T08-47-11Z.tsv (sha256 5a6e8ee53536; internal record)). A-only: B sites not measured.
   The kit's CUT (lane RBase, a working branch 7cdbb61b5fa0, PRH_FnParse.v f0d92dcec7e9): DW -> CW, and the
   ORDERED twins every exit of the loop needs for the post's new conjuncts (FREEORD-NONE, CAP):
   vrd_inode_fo_core / vrd_inode_fo (vrd_inode + the batch kit order list -> pj_free's ordered list pj_foR at S nn, its
   requests the accumulator af followed by the container's arrays PresetReqAt.arrz o cap), vrd_arrz_blk (the arrays'
   requests), and vrd_inode_ncap (vrd_inode + the members' caps + cap = ncap n -> pj_ncapR of the container).
   Numerals: 56 / 8 (LENGTH: node, key slot), 32 (DERIVED: MAXD), 6 / 5 (the object / array tags). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame VrdIElem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section F.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.

(* the D blocks are apart from the node: each is a NEW allocator block, the node lives in an entry block or frame *)
Lemma vrd_inode_apart : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_ijrn B ARx SK E P -> pj_apartR (ip_D P) (ie_v E).
Proof.
  intros CTX CTX0 CW E P HEN HJN.
  pose proof HJN as ((HAR & Hlay & _) & _ & _ & _ & _ & HBM & _).
  pose proof HBM as (HnotE & HPab & HPfr & _).
  pose proof Hlay as (_ & _ & _ & _ & _ & HFl & _).
  pose proof HEN as (_ & _ & _ & _ & HRD & _).
  pose proof HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPV & _ & _ & Hwin & HLE & _).
  pose proof HPV as (_ & _ & _ & _ & Hat & _).
  pose proof (@cf_head_nonneg cp) as Hch.
  intros [a' k'] x Hb Hx Hvx. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  assert (HB' : In (a' - cf_head, k' + cf_head) (ablocks B (ip_ly P) (ip_S P))).
  { apply (Permutation_in _ (Permutation_sym HPab)). apply in_or_app. left. unfold prhReader_ab.
    exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) _ (a', k') Hb). }
  pose proof (HnotE a' k' Hb) as HnE.
  destruct (req_size_pos (k' + cf_head)) as [_ Hr']; [lia|].
  destruct Hat as [(a & k & HinL & Ha1 & Ha2) | [(b & m & Hab & _ & Hb1 & Hb2) | [(cid & pos & Hfr & Hf1 & Hf2) | Hw]]].
  - (* a harness block of the entry ledger *)
    pose proof HLE as (_ & _ & HHB & _). rewrite Forall_forall in HHB.
    destruct (HHB _ HinL) as (Hk0 & HabE & _). cbn [fst snd] in Hk0, HabE.
    assert (HabP : In (a - cf_head, k + cf_head) (ablocks B (ip_ly P) (ip_S P)))
      by (apply (Permutation_in _ (Permutation_sym HPab)); apply in_or_app; right; exact HabE).
    assert (Hne : (a' - cf_head, k' + cf_head) <> (a - cf_head, k + cf_head))
      by (intros Heq; apply HnE; rewrite Heq; exact HabE).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR HB' HabP Hne) as Hz.
    destruct (req_size_pos (k + cf_head)) as [_ Hr]; [lia|].
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
  - (* an allocator block of the entry *)
    assert (HbP : In (b, m) (ablocks B (ip_ly P) (ip_S P)))
      by (apply (Permutation_in _ (Permutation_sym HPab)); apply in_or_app; right; exact Hab).
    assert (Hne : (a' - cf_head, k' + cf_head) <> (b, m)) by (intros Heq; apply HnE; rewrite Heq; exact Hab).
    pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR HB' HbP Hne) as Hz.
    destruct (req_size_pos m) as [_ Hr]; [lia|].
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
  - (* a fake frame of the entry: still a frame of the position, at the same address *)
    assert (HfP : In (cid, pos) (frames (ip_S P))) by (apply (Permutation_in _ (Permutation_sym HPfr)); exact Hfr).
    destruct (alx_sep SEGS B ARx LAWS _ _ _ _ _ _ HAR) as [Hq _].
    pose proof (pairwise_In _ _ _ _ _ _ eq_refl Hq
                  (in_map (fun b => (fst b, req_size (snd b))) _ _ HB')
                  (in_map (fun f => (frame_addr (ip_ly P) (fst f) (snd f), fs_frame_bytes (fst f))) _ _ HfP)) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. unfold frame_addr in Hz, Hf1, Hf2. rewrite HFl in Hz. lia.
  - (* the caller window: excluded by rd_pre *)
    lia.
Qed.

(* ==== the refused node is freeable to MAXD - d, at the position's own view ====
   The core form takes only what it reads: the node, the cursor's depth word (pj_in_okR's last conjunct), the
   ledger's NoDup, the position's rd_ledger_move (Permutation Lam (D ++ entry Lam)) and the elements' depth. It is
   the form an exit after an ALLOCATION FAILURE cites, where vrd_imodel's `ok = repeat true ..` no longer holds. *)
Lemma vrd_inode_fd_core : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_inode E P [] -> vrd_ijrn B ARx SK E P ->
  pj_in_okR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ie_q E) (ie_text E) (ie_len E) (ip_p P) (Z.of_nat (ie_d E) + 1) (ie_tb E) ->
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
    (ie_most E) (ie_own E) ->
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P)
    (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) ->
  Forall (fun m => (PjTree.depth (snd m) <= PjGrammar.MAXD - S (ie_d E))%nat) (ip_acc P) ->
  pj_fdR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) (PjGrammar.MAXD - ie_d E) (ie_v E) (ip_D P).
Proof.
  intros CTX CTX0 CW E P HEN HND HJN Hin Hled HLM HDep.
  pose proof HND as (Hhdr & Hnc & Hcap & Hc0 & Hlin & Hlen & (Di & HPerm & HTree) & _ & _ & _ & _ & Hkz).
  pose proof Hin as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd32).
  (* NoDup, from the ledger *)
  assert (HNd : List.NoDup (ip_D P)).
  { pose proof HLM as (_ & _ & _ & HPL & _). pose proof Hled as (_ & HNL & _).
    assert (HNL' : List.NoDup (map fst (ip_Lam P))) by (first [exact HNL | apply NoDup_ListNoDup; exact HNL]).
    apply (Permutation_map fst) in HPL. pose proof (Permutation_NoDup HPL HNL') as H. rewrite map_app in H.
    apply NoDup_app_remove_r in H. exact (NoDup_map_inv _ _ H). }
  pose proof (vrd_inode_apart CTX CTX0 CW E P HEN HJN) as Happ.
  (* the depth *)
  assert (Hd : (ie_d E < PjGrammar.MAXD)%nat) by (unfold PjGrammar.MAXD; lia).
  replace (PjGrammar.MAXD - ie_d E)%nat with (S (PjGrammar.MAXD - S (ie_d E))) by lia.
  set (k := (PjGrammar.MAXD - S (ie_d E))%nat) in *.
  assert (Hnl : Z.to_nat (ip_n P) = length (rev (ip_acc P))) by (rewrite length_rev; lia).
  cbn [pj_fdR]. split; [first [exact HNd | apply NoDup_ListNoDup; exact HNd]|]. split; [exact Happ|].
  destruct (ie_o E) eqn:Ho.
  - (* an object *)
    destruct (Z.eq_dec (ip_cap P) 0) as [Hc | Hc].
    + destruct (Hc0 Hc) as [Hk0 Hy0].
      assert (Hn0 : ip_n P = 0) by lia.
      assert (Ha0 : ip_acc P = []) by (destruct (ip_acc P); [reflexivity | cbn [length] in Hlen; lia]).
      rewrite Ha0 in HTree. cbn [rev pj_memsR] in HTree. subst Di.
      exists 6, 0, 0, (ip_kids P), (ip_keys P), (ip_n P), (ip_cap P), false, [], [], [], [].
      split; [exact Hhdr|]. split; [left; split; reflexivity|].
      split; [left; split; [exact Hk0 | split; [exact Hn0 | reflexivity]]|].
      split; [left; split; [exact Hy0 | split; reflexivity]|].
      split; [unfold kids_blkR, keys_blkR in HPerm; rewrite Hc in HPerm; cbn in HPerm; rewrite HPerm; apply Permutation_refl|].
      rewrite Hn0. reflexivity.
    + assert (Hcp : 0 < ip_cap P) by lia.
      destruct (Hlin Hcp) as [Hlk Hly].
      exists 6, 0, 0, (ip_kids P), (ip_keys P), (ip_n P), (ip_cap P), true, [],
        [(ip_kids P, 56 * ip_cap P)], [(ip_keys P, 8 * ip_cap P)], Di.
      split; [exact Hhdr|]. split; [left; split; reflexivity|].
      split; [right; exists (56 * ip_cap P); split; [exact Hlk | split; [lia | reflexivity]]|].
      split; [right; split; [reflexivity|]; exists (8 * ip_cap P); split; [exact (Hly eq_refl) | split; [lia | reflexivity]]|].
      split.
      { unfold kids_blkR, keys_blkR in HPerm. destruct (Z.eqb_spec (ip_cap P) 0); [lia|]. cbn in HPerm.
        exact HPerm. }
      rewrite Hnl.
      apply (vrd_fd_mems SEGS (rev (ip_acc P))).
      * apply Forall_forall. intros mm _. apply vrd_nodefd_all.
      * exact HTree.
      * apply Forall_rev. exact HDep.
  - (* an array *)
    pose proof (Hkz eq_refl) as Hy0.
    destruct (Z.eq_dec (ip_cap P) 0) as [Hc | Hc].
    + destruct (Hc0 Hc) as [Hk0 _].
      assert (Hn0 : ip_n P = 0) by lia.
      assert (Ha0 : ip_acc P = []) by (destruct (ip_acc P); [reflexivity | cbn [length] in Hlen; lia]).
      rewrite Ha0 in HTree. cbn [rev map pj_itemsR] in HTree. subst Di.
      exists 5, 0, 0, (ip_kids P), (ip_keys P), (ip_n P), (ip_cap P), false, [], [], [], [].
      split; [exact Hhdr|]. split; [left; split; reflexivity|].
      split; [left; split; [exact Hk0 | split; [exact Hn0 | reflexivity]]|].
      split; [left; split; [exact Hy0 | split; reflexivity]|].
      split; [unfold kids_blkR, keys_blkR in HPerm; rewrite Hc in HPerm; cbn in HPerm; rewrite HPerm; apply Permutation_refl|].
      rewrite Hn0. reflexivity.
    + assert (Hcp : 0 < ip_cap P) by lia.
      destruct (Hlin Hcp) as [Hlk _].
      exists 5, 0, 0, (ip_kids P), (ip_keys P), (ip_n P), (ip_cap P), false, [],
        [(ip_kids P, 56 * ip_cap P)], [], Di.
      split; [exact Hhdr|]. split; [left; split; reflexivity|].
      split; [right; exists (56 * ip_cap P); split; [exact Hlk | split; [lia | reflexivity]]|].
      split; [left; split; [exact Hy0 | split; reflexivity]|].
      split.
      { unfold kids_blkR, keys_blkR in HPerm. destruct (Z.eqb_spec (ip_cap P) 0); [lia|]. cbn in HPerm.
        exact HPerm. }
      rewrite Hnl, <- (length_map snd (rev (ip_acc P))).
      apply (vrd_fd_items SEGS (map snd (rev (ip_acc P)))).
      * apply Forall_forall. intros u _. apply vrd_nodefd_all.
      * exact HTree.
      * apply Forall_map. apply Forall_rev. exact HDep.
Qed.

Lemma vrd_inode_fd : forall CTX CTX0 CW E P,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_inode E P [] -> vrd_icur B E P -> vrd_ijrn B ARx SK E P ->
  vrd_imodel E P ->
  pj_fdR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) (PjGrammar.MAXD - ie_d E) (ie_v E) (ip_D P).
Proof.
  intros CTX CTX0 CW E P HEN HND HCU HJN HMD.
  pose proof HCU as (Hin & _ & _ & _ & Hled & _).
  pose proof HMD as (_ & _ & HLM & _ & _ & _ & HDep & _).
  exact (vrd_inode_fd_core CTX CTX0 CW E P HEN HND HJN Hin Hled HLM HDep).
Qed.


(* ==== THE KIT'S CUT: the ORDERED and CAPACITY twins of the exits ==== *)

(* the container's arrays' requests are the model's PresetReqAt.arrz (the head is the model's) *)
Lemma vrd_arrz_blk : forall (o : bool) kids keys cap, 0 <= cap -> cf_head = PresetReqAt.HEAD ->
  map (fun b => snd b + cf_head) (kids_blkR kids cap ++ keys_blkR (if o then 6 else 5) keys cap) =
  PresetReqAt.arrz o (Z.to_nat cap).
Proof.
  intros o kids keys cap Hc Hh. unfold kids_blkR, keys_blkR, PresetReqAt.arrz.
  destruct (Z.eqb_spec cap 0) as [->|Hne]; [reflexivity|].
  destruct (Z.to_nat cap) as [|c'] eqn:Ec; [lia|].
  assert (Hcz : Z.of_nat (S c') = cap) by (rewrite <- Ec; apply Z2Nat.id; lia).
  rewrite !Nat2Z.inj_mul, Hcz. change (Z.of_nat 56) with 56. change (Z.of_nat 8) with 8.
  destruct o; cbn [orb negb Z.eqb Pos.eqb map app snd]; rewrite Hh; reflexivity.
Qed.

(* THE ORDERED SHAPE OF THE OPEN CONTAINER at a position (the core form, as vrd_inode_fd_core's premises): pj_free's
   order list of the node is the completed slots' list (the batch kit order list, at the depth bound nn of the members) then
   the arrays, at depth S nn; its requests are af then PresetReqAt.arrz o cap *)
Lemma vrd_inode_fo_core : forall CTX CTX0 CW E P af nn,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_inode E P [] -> vrd_ijrn B ARx SK E P ->
  prh_ledger B (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P)
    (ie_most E) (ie_own E) ->
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P)
    (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) ->
  vrd_iforder E P [] af -> cf_head = PresetReqAt.HEAD ->
  Forall (fun mb => (PjTree.depth (snd mb) <= nn)%nat) (ip_acc P) ->
  exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) (S nn) (ie_v E) (ip_D P) F /\
    map (fun b => snd b + cf_head) F = af ++ PresetReqAt.arrz (ie_o E) (Z.to_nat (ip_cap P)).
Proof.
  intros CTX CTX0 CW E P af nn HEN HND HJN Hled HLM HFO Hh Hdep.
  pose proof HND as (Hhdr & Hnc & Hcap & Hc0 & Hlin & Hlen & _ & _ & _ & _ & _ & Hkz).
  destruct (HFO Hh nn Hdep) as (Di & Facc & HPerm & HOI & Hmap).
  (* NoDup, from the ledger *)
  assert (HNd : List.NoDup (ip_D P)).
  { pose proof HLM as (_ & _ & _ & HPL & _). pose proof Hled as (_ & HNL & _).
    assert (HNL' : List.NoDup (map fst (ip_Lam P))) by (first [exact HNL | apply NoDup_ListNoDup; exact HNL]).
    apply (Permutation_map fst) in HPL. pose proof (Permutation_NoDup HPL HNL') as H. rewrite map_app in H.
    apply NoDup_app_remove_r in H. exact (NoDup_map_inv _ _ H). }
  pose proof (vrd_inode_apart CTX CTX0 CW E P HEN HJN) as Happ.
  exists (Facc ++ kids_blkR (ip_kids P) (ip_cap P) ++ keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ []).
  split.
  2: { rewrite app_nil_r, map_app, Hmap, (vrd_arrz_blk (ie_o E) (ip_kids P) (ip_keys P) (ip_cap P)) by lia.
       reflexivity. }
  cbn [PRH_PjOrder.pj_foR]. unfold PRH_PjOrder.pj_oshapeR.
  split; [first [exact HNd | apply NoDup_ListNoDup; exact HNd]|]. split; [exact Happ|].
  rewrite app_nil_l in HPerm.
  destruct (Z.eq_dec (ip_cap P) 0) as [Hc | Hc].
  - (* the empty container: no array, no slot *)
    assert (Hn0 : ip_n P = 0) by lia.
    assert (HnN : Z.to_nat (ip_n P) = 0%nat) by lia.
    rewrite HnN in HOI. cbn [PRH_PjOrder.pf_oitemsR] in HOI. destruct HOI as [-> ->].
    assert (Ek : kids_blkR (ip_kids P) (ip_cap P) = []) by (unfold kids_blkR; rewrite Hc; reflexivity).
    assert (Ey : keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) = [])
      by (unfold keys_blkR; rewrite Hc; reflexivity).
    rewrite Ek, Ey in HPerm |- *.
    destruct (Hc0 Hc) as [Hk0 Hy0].
    exists (if ie_o E then 6 else 5), 0, 0, (ip_kids P), (ip_keys P), (ip_n P), (ip_cap P), false, [], [], [], [], [].
    split; [exact Hhdr|]. split; [left; split; reflexivity|].
    split; [left; split; [exact Hk0 | split; [exact Hn0 | reflexivity]]|].
    split; [left; split; [exact Hy0 | split; reflexivity]|].
    split; [exact HPerm|]. split; [cbv beta; rewrite HnN; cbn [PRH_PjOrder.pf_oitemsR]; split; reflexivity|].
    reflexivity.
  - assert (Hcp : 0 < ip_cap P) by lia.
    destruct (Hlin Hcp) as [Hlk Hly].
    assert (Ek : kids_blkR (ip_kids P) (ip_cap P) = [(ip_kids P, 56 * ip_cap P)])
      by (unfold kids_blkR; destruct (Z.eqb_spec (ip_cap P) 0); [lia | reflexivity]).
    rewrite Ek in HPerm |- *.
    destruct (ie_o E) eqn:Ho.
    + assert (Ey : keys_blkR 6 (ip_keys P) (ip_cap P) = [(ip_keys P, 8 * ip_cap P)])
        by (unfold keys_blkR; destruct (Z.eqb_spec (ip_cap P) 0); [lia | reflexivity]).
      rewrite Ey in HPerm |- *.
      exists 6, 0, 0, (ip_kids P), (ip_keys P), (ip_n P), (ip_cap P), true, [],
        [(ip_kids P, 56 * ip_cap P)], [(ip_keys P, 8 * ip_cap P)], Di, Facc.
      split; [exact Hhdr|]. split; [left; split; reflexivity|].
      split; [right; exists (56 * ip_cap P); split; [exact Hlk | split; [lia | reflexivity]]|].
      split; [right; split; [reflexivity|]; exists (8 * ip_cap P); split; [exact (Hly eq_refl) | split; [lia | reflexivity]]|].
      split; [exact HPerm|]. split; [exact HOI | reflexivity].
    + assert (Ey : keys_blkR 5 (ip_keys P) (ip_cap P) = [])
        by (unfold keys_blkR; destruct (ip_cap P =? 0); reflexivity).
      rewrite Ey in HPerm |- *.
      exists 5, 0, 0, (ip_kids P), (ip_keys P), (ip_n P), (ip_cap P), false, [],
        [(ip_kids P, 56 * ip_cap P)], [], Di, Facc.
      split; [exact Hhdr|]. split; [left; split; reflexivity|].
      split; [right; exists (56 * ip_cap P); split; [exact Hlk | split; [lia | reflexivity]]|].
      split; [left; split; [exact (Hkz eq_refl) | split; reflexivity]|].
      split; [exact HPerm|]. split; [exact HOI | reflexivity].
Qed.

(* the same from a position's vrd_icur and vrd_imodel (the form a granted position cites) *)
Lemma vrd_inode_fo : forall CTX CTX0 CW E P af nn,
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_inode E P [] -> vrd_icur B E P -> vrd_ijrn B ARx SK E P ->
  vrd_imodel E P -> vrd_iforder E P [] af -> cf_head = PresetReqAt.HEAD ->
  Forall (fun mb => (PjTree.depth (snd mb) <= nn)%nat) (ip_acc P) ->
  exists F, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (prh_lin (ip_Lam P)) (S nn) (ie_v E) (ip_D P) F /\
    map (fun b => snd b + cf_head) F = af ++ PresetReqAt.arrz (ie_o E) (Z.to_nat (ip_cap P)).
Proof.
  intros CTX CTX0 CW E P af nn HEN HND HCU HJN HMD HFO Hh Hdep.
  pose proof HCU as (_ & _ & _ & _ & Hled & _).
  pose proof HMD as (_ & _ & HLM & _).
  exact (vrd_inode_fo_core CTX CTX0 CW E P af nn HEN HND HJN Hled HLM HFO Hh Hdep).
Qed.

(* THE CONTAINER'S CAPACITY (CAP): the node's header cap is ncap of its count and every member's tree has its caps *)
Lemma vrd_inode_ncap : forall E P,
  vrd_inode E P [] -> vrd_incaps E P -> ip_cap P = Z.of_nat (PresetReqAt.ncap (Z.to_nat (ip_n P))) ->
  pj_ncapR SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (ie_v E) (PjGrammar.mk (ie_o E) (rev (ip_acc P))).
Proof.
  intros E P HND HNC Hcap.
  pose proof HND as (Hhdr & Hnc & _ & _ & _ & Hlen & _).
  pose proof Hhdr as (_ & _ & _ & _ & Hk24 & _ & _ & Hc48).
  assert (Hlr : Z.to_nat (ip_n P) = length (rev (ip_acc P))) by (rewrite length_rev; lia).
  unfold vrd_incaps in HNC. unfold PjGrammar.mk.
  destruct (ie_o E); cbn [pj_ncapR].
  - split; [rewrite <- Hlr, <- Hcap; exact Hc48|].
    exists (ip_kids P). split; [exact Hk24|]. apply vrd_kids_let. exact HNC.
  - split; [rewrite length_map, <- Hlr, <- Hcap; exact Hc48|].
    exists (ip_kids P). split; [exact Hk24|]. apply vrd_kids_snd. exact HNC.
Qed.

(* THE BATCH KIT'S LAYER ACROSS A STEP THAT MOVES NOTHING (RItems' request for the key / value steps): the same node, slots,
   members and block list at a later position whose reader keeps the bytes of every block the position owns (what a
   callee's journal keeps off its footprint, or a store keeps off its bytes) and whose ledger still holds them *)
Lemma vrd_k1_keep : forall E P P2 Dx af,
  ip_kids P2 = ip_kids P -> ip_keys P2 = ip_keys P -> ip_n P2 = ip_n P -> ip_cap P2 = ip_cap P ->
  ip_acc P2 = ip_acc P -> ip_D P2 = ip_D P ->
  (forall x k, In (x, k) (ip_D P) -> prh_lin (ip_Lam P2) x k) ->
  rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P2)) (ip_mem P2)) (rd_blk (ip_D P)) ->
  vrd_inode E P Dx -> vrd_incaps E P -> vrd_iforder E P Dx af ->
  vrd_incaps E P2 /\ vrd_iforder E P2 Dx af.
Proof.
  intros E P P2 Dx af Ek Ey En Ec Ea ED HLk HK HND HNC HFO.
  pose proof HND as (_ & Hnc & _ & _ & _ & Hlen & (Di & HDp & Hsub) & _).
  assert (HinD : forall b, In b (Dx ++ kids_blkR (ip_kids P) (ip_cap P) ++
                               keys_blkR (if ie_o E then 6 else 5) (ip_keys P) (ip_cap P) ++ Di) -> In b (ip_D P))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HDp) Hb)).
  (* the slot array, the key slots and the members' blocks are bytes of the position's blocks *)
  assert (Hkr : forall x, ip_kids P <= x < ip_kids P + 56 * ip_n P -> rd_blk (ip_D P) x).
  { intros x Hx. apply (rd_blk_in (ip_D P) (ip_kids P, 56 * ip_cap P)); [|cbn [fst snd]; lia].
    apply HinD. apply in_or_app. right. apply in_or_app. left. unfold kids_blkR.
    rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). left. reflexivity. }
  assert (Hyr : ie_o E = true -> forall x, ip_keys P <= x < ip_keys P + 8 * ip_n P -> rd_blk (ip_D P) x).
  { intros Ho x Hx. apply (rd_blk_in (ip_D P) (ip_keys P, 8 * ip_cap P)); [|cbn [fst snd]; lia].
    apply HinD. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. unfold keys_blkR. rewrite Ho.
    rewrite (proj2 (Z.eqb_neq (ip_cap P) 0) ltac:(lia)). left. reflexivity. }
  assert (HDir : forall x, rd_blk Di x -> rd_blk (ip_D P) x).
  { intros x Hx. apply (rd_blk_sub Di); [|exact Hx]. intros b Hb. apply HinD.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
  assert (Hln : Z.of_nat (length (rev (ip_acc P))) = ip_n P) by (rewrite length_rev; exact Hlen).
  split.
  - unfold vrd_incaps in HNC |- *. rewrite Ea, Ek.
    assert (HK' : rd_keep SEGS (mrestrict (w_H (ip_W P)) (ip_mem P)) (mrestrict (w_H (ip_W P2)) (ip_mem P2))
                    (fun z => ip_kids P <= z < ip_kids P + 56 * Z.of_nat (length (rev (ip_acc P))) \/ rd_blk Di z)).
    { eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz]; [apply Hkr; lia | exact (HDir z Hz)]. }
    revert Hsub. destruct (ie_o E); intros Hsub.
    + exact (vrd_ncaps_keep_mems SEGS (rev (ip_acc P)) _ _ _ (ip_kids P) (ip_keys P) Di Hsub HNC HK').
    + exact (vrd_ncaps_keep_items SEGS (rev (ip_acc P)) _ _ _ (ip_kids P) Di Hsub HNC HK').
  - intros Hh nn Hnn. rewrite Ea in Hnn.
    destruct (HFO Hh nn Hnn) as (Di' & Facc & HP & HOI & Hm).
    exists Di', Facc. rewrite ED, Ek, Ey, Ec, En. split; [exact HP|]. split; [|exact Hm].
    assert (HinD' : forall b, In b Di' -> In b (ip_D P)).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym HP)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hb. }
    apply (PRH_PjOrder.pf_oitemsR_frame SEGS nn _ _ _ _ (ie_o E) (ip_kids P) (ip_keys P) (Z.to_nat (ip_n P)) Di' Facc
             HOI).
    + intros x k Hin. exact (HLk x k (HinD' _ Hin)).
    + apply (vrd_agree_of_keep SEGS). eapply rd_keep_mono; [exact HK|].
      intros y Hy'. unfold PRH_PjOrder.pf_ofoot in Hy'. destruct Hy' as [Hy | [(Hks & Hy) | (b & Hb & Hy)]].
      * apply Hkr. lia.
      * apply (Hyr Hks). lia.
      * exact (rd_blk_in (ip_D P) b y (HinD' _ Hb) Hy).
Qed.
End F.

Print Assumptions vrd_inode_fd.
Print Assumptions vrd_inode_fo.
Print Assumptions vrd_inode_ncap.
Print Assumptions vrd_k1_keep.
