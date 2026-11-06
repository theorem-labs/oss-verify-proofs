(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, cf layer field round 3; integrator ReallocPrimary).
   rule 24: no function proved (kind: frame corollaries of the leaf posts' raw frames).
   The keep of arodata_ok_cf (YG0dcf.v, value form: an overlay byte at a non-owned address of aro_addr_cf, the
   relocation-read-only range [cf_relro_lo, cf_relro_hi) and the report's read-only reads cf_ro_reads (part 3c), is the
   image's byte) at seven leaf posts: malloc_leaf_cf,
   malloc_cf_null_post, malloc_leaf_cf_w, free_leaf_cf, strndup_leaf_cf (YG0dcf.v) and rwalk_leaf_cf, refill_leaf_core_cf
   (YGcfInstRefill.v). Each keep is a STANDALONE corollary of its post's raw frame (Main 2026-10-30, option (a)): no
   post statement and no producer changes, and arodata_ok_cf is carried beside ARcf, never in it.
   Why the raw frames give it: a non-owned RELRO byte lies in the image window (relro_seg_t with ALedger_cf's
   alc_img), which layout_ok and sec_placed keep apart from every owned extent and secondary, xs_placed_cf keeps apart
   from the errbuf, and whose addresses are below every shadow range and every stack window; errno is apart from RELRO
   by the unit row errno_relro_t; a freed block is a client block at the entry state and a new block one at the result
   (client_byte_not_img_cf). The new block of malloc / strndup is not named in their posts, so those keeps take the
   model fact that the result names it (BLK premise below); free's comes from afree_realizes_cf's own premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP09 YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG YGcfMallocCompose YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstRefill.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section S.
Variable segs : list Segment.
Variable B : asyms.

(* A new block named by the result is a client block there, so it misses the image window. *)
Lemma relro_not_block_cf : forall ly S Hp rd (p : sptr) n a, ARmcf B ly S Hp rd ->
  (exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n) ->
  in_zr a (ly_img ly) -> ~ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof.
intros ly S Hp rd p n a M (k & Hk & Hst & Hu & Hq) I Hb. subst p n.
apply (client_byte_not_img_cf B ly S Hp rd a M); [|exact I].
left. exists k. split; [exact Hk|]. split; [exact Hst|]. unfold ck_n. split; lia.
Qed.

Lemma blocks_chunk_cf : forall S p n, In (p, n) (blocks S) ->
  exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n.
Proof.
intros S p n H. unfold blocks in H. apply in_map_iff in H as (k & E & Hk). apply filter_In in Hk as [Hk Ha].
injection E as E1 E2. exists k. split; [exact Hk|]. split; [|split; assumption].
unfold is_alloc in Ha. destruct (ck_state k); [reflexivity | discriminate Ha].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seven keeps.  BLK: the model fact that the result names the new block (malloc_cf / the strndup tree's malloc). *)
Lemma malloc_leaf_arodata_cf : forall ly S Hp W regs mem md n ch r W' c',
  acall_pre_cf segs B ly S Hp W regs mem md ch -> relro_seg_t segs -> errno_relro_t B ->
  (fst r <> PNull -> exists k, In k (st_chunks (snd r)) /\ ck_state k = CAllocated /\ ck_user k = fst r /\ ck_req k = n) ->
  malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ (arodata_ok_cf segs B mem -> arodata_ok_cf segs B mem').
Proof.
intros ly S Hp W regs mem md n ch r W' c' PRE RS ER BLK
  (ly' & regs' & mem' & md' & Hc & (A' & _) & _ & _ & _ & _ & _ & RAW).
exists regs', mem', md'. split; [exact Hc|]. destruct PRE as (A & _ & _ & STK & _).
apply (arodata_keep_cf segs B ly S Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ ascratch B ASTACK regs a \/
     ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) \/
      Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|[[NN Hb]|X]]]].
  + exact (NA X).
  + exact (NA' X).
  + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 A)) STK ER Ha R X).
  + exact (relro_not_block_cf ly' (snd r) Hp _ (fst r) n a (proj1 A') (BLK NN) I' Hb).
  + apply Exists_app in X as [X|X]; [exact (NX X) | exact (NX' X)].
- intros x NX. apply RAW; intros Y; apply NX; tauto.
Qed.

Lemma malloc_null_arodata_cf : forall ly S Hp W regs mem md n ch r W' c',
  acall_pre_cf segs B ly S Hp W regs mem md ch -> relro_seg_t segs -> errno_relro_t B ->
  malloc_cf_null_post segs B ly S Hp W regs mem md n r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ (arodata_ok_cf segs B mem -> arodata_ok_cf segs B mem').
Proof.
intros ly S Hp W regs mem md n ch r W' c' PRE RS ER
  (_ & ly' & regs' & mem' & md' & Hc & (A' & _) & _ & _ & _ & _ & _ & _ & _ & _ & RAW).
exists regs', mem', md'. split; [exact Hc|]. destruct PRE as (A & _ & _ & STK & _).
apply (arodata_keep_cf segs B ly S Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ ascratch B ASTACK regs a \/
     Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r))) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|X]]].
  + exact (NA X).
  + exact (NA' X).
  + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 A)) STK ER Ha R X).
  + apply Exists_app in X as [X|X]; [exact (NX X) | exact (NX' X)].
- intros x NX. apply RAW; intros Y; apply NX; tauto.
Qed.

Lemma malloc_leaf_w_arodata_cf : forall stk ly S Hp W regs mem md n ch r W' c',
  acall_pre_cf_w segs B stk ly S Hp W regs mem md ch -> relro_seg_t segs -> errno_relro_t B ->
  (fst r <> PNull -> exists k, In k (st_chunks (snd r)) /\ ck_state k = CAllocated /\ ck_user k = fst r /\ ck_req k = n) ->
  malloc_leaf_cf_w segs B stk ly S Hp W regs mem md n r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ (arodata_ok_cf segs B mem -> arodata_ok_cf segs B mem').
Proof.
intros stk ly S Hp W regs mem md n ch r W' c' PRE RS ER BLK
  (ly' & regs' & mem' & md' & Hc & (A' & _) & _ & _ & _ & _ & _ & RAW).
exists regs', mem', md'. split; [exact Hc|]. destruct PRE as (A & _ & _ & STK & _).
apply (arodata_keep_cf segs B ly S Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ ascratch B stk regs a \/
     ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n) \/
      Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|[[NN Hb]|X]]]].
  + exact (NA X).
  + exact (NA' X).
  + exact (relro_not_scratch_cf B ly stk regs a (amc_layout _ _ _ _ _ (proj1 A)) STK ER Ha R X).
  + exact (relro_not_block_cf ly' (snd r) Hp _ (fst r) n a (proj1 A') (BLK NN) I' Hb).
  + apply Exists_app in X as [X|X]; [exact (NX X) | exact (NX' X)].
- intros x NX. apply RAW; intros Y; apply NX; tauto.
Qed.

(* free: the freed block is a block of the entry state (afree_realizes_cf's premise). *)
Lemma free_leaf_arodata_cf : forall ly S Hp W regs mem md p n ch r W' c',
  acall_pre_cf segs B ly S Hp W regs mem md ch -> relro_seg_t segs -> errno_relro_t B ->
  (p = PNull \/ In (p, n) (blocks S)) ->
  free_leaf_cf segs B ly S Hp W regs mem md p n r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ (arodata_ok_cf segs B mem -> arodata_ok_cf segs B mem').
Proof.
intros ly S Hp W regs mem md p n ch r W' c' PRE RS ER HP
  (ly' & regs' & mem' & md' & Hc & (A' & _) & _ & _ & RAW).
exists regs', mem', md'. split; [exact Hc|]. destruct PRE as (A & _ & _ & STK & _).
apply (arodata_keep_cf segs B ly S Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ ascratch B ASTACK regs a \/
     (p <> PNull /\ sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|[NN Hb]]]].
  + exact (NA X).
  + exact (NA' X).
  + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 A)) STK ER Ha R X).
  + destruct HP as [HP|HP]; [exact (NN HP)|].
    exact (relro_not_block_cf ly S Hp _ p n a (proj1 A) (blocks_chunk_cf S p n HP) I Hb).
- intros x NX. apply RAW; intros Y; apply NX; tauto.
Qed.

Lemma strndup_leaf_arodata_cf : forall ly S Hp W regs mem md x k ch r W' c',
  acall_pre_cf segs B ly S Hp W regs mem md ch -> relro_seg_t segs -> errno_relro_t B ->
  (fst r <> PNull -> exists kk, In kk (st_chunks (snd r)) /\ ck_state kk = CAllocated /\ ck_user kk = fst r /\
     ck_req kk = k + 1) ->
  strndup_leaf_cf segs B ly S Hp W regs mem md x k r W' c' ->
  exists regs' mem' md', c' = cfg_at segs (raZ regs) regs' mem' md' /\ (arodata_ok_cf segs B mem -> arodata_ok_cf segs B mem').
Proof.
intros ly S Hp W regs mem md x k ch r W' c' PRE RS ER BLK
  (ly' & regs' & mem' & md' & Hc & (A' & _) & _ & _ & _ & _ & _ & _ & RAW).
exists regs', mem', md'. split; [exact Hc|]. destruct PRE as (A & _ & _ & STK & _).
apply (arodata_keep_cf segs B ly S Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ ascratch B ASTACK regs a \/
     ((fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size (k + 1)) \/
      Exists (in_zr a) (xs_cf ly S ++ xs_cf ly' (snd r)))) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|[[NN Hb]|X]]]].
  + exact (NA X).
  + exact (NA' X).
  + exact (relro_not_scratch_cf B ly ASTACK regs a (amc_layout _ _ _ _ _ (proj1 A)) STK ER Ha R X).
  + exact (relro_not_block_cf ly' (snd r) Hp _ (fst r) (k + 1) a (proj1 A') (BLK NN) I' Hb).
  + apply Exists_app in X as [X|X]; [exact (NX X) | exact (NX' X)].
- intros w NX. apply RAW; intros Y; apply NX; tauto.
Qed.
End S.

Section F. Context {IM : AImg} {AG : AGImg}.
Variable B : asyms.

(* The refill walk's leaf: its raw frame excepts AOX_cf (aowned or the errbuf extent) at both ends and the refill's
   stack window. *)
Lemma rwalk_leaf_arodata_cf : forall Hp ly S0 cl W regs mem md r W' c',
  ARcf im_segs B ly S0 Hp W mem md -> ly_stk_lo ly + REP_STACK <= spZ regs -> relro_seg_t im_segs ->
  rwalk_leaf_cf B Hp ly S0 cl W regs mem md r W' c' ->
  exists regs' mem' md', c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  (arodata_ok_cf im_segs B mem -> arodata_ok_cf im_segs B mem').
Proof.
intros Hp ly S0 cl W regs mem md r W' c' A STK RS (ly' & regs' & mem' & md' & Hc & A' & _ & _ & _ & _ & _ & _ & _ & _ & RAW & _).
exists regs', mem', md'. split; [exact Hc|].
apply (arodata_keep_cf im_segs B ly S0 Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => AOX_cf B ly S0 a \/ AOX_cf B ly' (snd r) a \/ (spZ regs - REP_STACK <= a < spZ regs)) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|X]].
  + destruct X as [X|X]; [exact (NA X) | exact (NX X)].
  + destruct X as [X|X]; [exact (NA' X) | exact (NX' X)].
  + pose proof (lo_top _ (amc_layout _ _ _ _ _ (proj1 A))) as (_ & _ & _ & _ & _ & _ & T7).
    unfold kHighMemBeg, kImgEnd in *. lia.
- intros x NX. apply RAW; intros Y; apply NX; tauto.
Qed.

(* The refill's machine leaf: its raw frame excepts aowned at both ends, the window REP_W c and refill_exc_cf (AOX_cf
   at either end). *)
Lemma refill_leaf_core_arodata_cf : forall Hp ly S c W regs mem md r W' c',
  ARcf im_segs B ly S Hp W mem md -> ly_stk_lo ly + REP_W c <= spZ regs -> relro_seg_t im_segs ->
  refill_leaf_core_cf B Hp ly S c W regs mem md r W' c' ->
  exists regs' mem' md', c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
  (arodata_ok_cf im_segs B mem -> arodata_ok_cf im_segs B mem').
Proof.
intros Hp ly S c W regs mem md r W' c' A STK RS
  (ly' & regs' & mem' & md' & Hc & (A' & _) & _ & _ & _ & _ & _ & _ & RAW & _).
exists regs', mem', md'. split; [exact Hc|].
apply (arodata_keep_cf im_segs B ly S Hp W mem md ly' (snd r) Hp W' mem' md'
  (fun a => aowned B ly S a \/ aowned B ly' (snd r) a \/ (spZ regs - REP_W c <= a < spZ regs) \/
     refill_exc_cf B c ly S ly' (snd r) a) A A' RS).
- intros a Ha NO R I I' NA NA' NX NX' [X|[X|[X|(_ & X)]]].
  + exact (NA X).
  + exact (NA' X).
  + pose proof (lo_top _ (amc_layout _ _ _ _ _ (proj1 A))) as (_ & _ & _ & _ & _ & _ & T7).
    unfold kHighMemBeg, kImgEnd in *. lia.
  + destruct X as [[X|X]|[X|X]]; [exact (NA X) | exact (NX X) | exact (NA' X) | exact (NX' X)].
- intros x NX. apply RAW; intros Y; apply NX; tauto.
Qed.
End F.
End R.
