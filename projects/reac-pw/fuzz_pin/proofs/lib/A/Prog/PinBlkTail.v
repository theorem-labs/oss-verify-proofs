(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/Prog/IdentBlkTail.v at origin/ossv/recipes 6ebe35ba632, with its module paths changed to reac-pw/fuzz_pin; no other change (the file names no address, no listing and no symbol). *)
(* The bytes of a heap block's last granule are present: what the runtime wrappers ask of a string that ends
   inside a heap block.

   `astrlen_realizes` (lib/A/Rt/StrlenDef.v:46), `amemchr_realizes` (lib/A/Rt/MemchrDef.v) and `tcheck_str_spec`
   (lib/A/Prog/check_str.v:79) each need, besides the string's own bytes, that every byte between the NUL and the
   end of the NUL's 8-byte word is readable: the interceptor's word loop reads the whole word that holds the NUL.
   `AR_blocks_law` (lib/Reusable/YG0d.v:423) gives presence only on [p, p + req_size n), and a block's requested
   size need not be a multiple of 8, so that word can run past the block's last byte.

   It does not run past what the allocator mapped: a chunk's extent covers its redzone, the rounded-up user size
   (`rounded_size`, a multiple of 8) and, for a secondary chunk, a second redzone; the bytes between the user
   bytes and the end of the extent are `chunk_junk`, and `ARm`'s `am_junk` says every one of them is readable.
   `blk_tail_present` below is that fact in the shape the three contracts consume. It names no address, no
   listing and no symbol of either build, so lib/B takes this same file.

   Proof: `In_ablocks` (YG0s.v:562) gives the chunk; inside [p, p + req_size n) the byte is a client byte
   (`am_client` over `chunk_user`), beyond it the byte is in the chunk's tail junk range
   (`am_junk` over the last entry of `chunk_junk`), whose length is `ck_extent k - ck_rz k - ck_n k`;
   `class_id_ok` (YG0a.v:57) for a primary chunk and `round_up_ge` for a secondary one bound the word's end by
   `p + ck_extent k - ck_rz k`. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0s YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b and others switch lia's division handling off; this file's arithmetic is all division and modulo. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* The user bytes of an allocated chunk and the junk bytes after them, to the end of its extent, are readable. *)
Lemma blk_chunk_vis : forall ly S (W : world segs) mem md k a,
AR segs B ly S W mem md -> In k (st_chunks S) -> ck_state k = CAllocated ->
sptr_addr B ly (ck_user k) <= a < sptr_addr B ly (ck_user k) - ck_rz k + ck_extent k ->
aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md k a HAR Hin Hal Ha.
pose proof (proj1 HAR) as HM.
pose proof (am_wf _ _ _ _ HM) as HWf.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ HWf) k Hin) as Hck.
pose proof Hck as (Hreq & Hbeg).
(* the chunk's base, and the user pointer above it *)
assert (Hprim : match ck_beg k with PPrim _ | PSec _ _ => True | _ => False end)
by (destruct (ck_beg k); cbn in Hbeg |- *; first [exact I | exact Hbeg]).
assert (Hu : sptr_addr B ly (ck_user k) = sptr_addr B ly (ck_beg k) + ck_rz k)
by (unfold ck_user; exact (sptr_addr_padd B ly (ck_beg k) (ck_rz k) Hprim)).
destruct (Z_lt_le_dec a (sptr_addr B ly (ck_user k) + ck_n k)) as [Hin1 | Hin2].
- (* a client byte of the chunk *)
  pose proof (am_client _ _ _ _ HM) as HC.
  assert (Hel : In (sptr_exp (ck_user k), ck_n k) (aclient S)).
  { unfold aclient. apply in_or_app. left. apply in_flat_map. exists k. split; [exact Hin|].
    unfold chunk_user. rewrite Hal. left. reflexivity. }
  pose proof (proj1 (Forall_forall _ _) HC _ Hel) as HV.
  specialize (HV (a - sptr_addr B ly (ck_user k))). cbn [fst snd] in HV.
  change (aeval B ly (sptr_exp (ck_user k))) with (sptr_addr B ly (ck_user k)) in HV.
  replace (sptr_addr B ly (ck_user k) + (a - sptr_addr B ly (ck_user k))) with a in HV by lia.
  apply HV. lia.
- (* a junk byte after the user bytes *)
  pose proof (am_junk _ _ _ _ HM) as HJ.
  assert (Hel : In (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k) (ajunk B ly S)).
  { unfold ajunk. right. right.
    apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. apply in_flat_map.
    exists k. split; [exact Hin|]. unfold chunk_junk. rewrite Hal.
    destruct (ck_rz k =? kChunkHeaderSize); cbn [app In]; tauto. }
  pose proof (proj1 (Forall_forall _ _) HJ _ Hel) as HV.
  specialize (HV (a - (sptr_addr B ly (ck_user k) + ck_n k))). cbn [fst snd] in HV.
  assert (Hev : aeval B ly (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k))
              = sptr_addr B ly (ck_beg k) + (ck_rz k + ck_n k)).
  { rewrite aeval_aoff; [reflexivity|]. destruct (ck_beg k); cbn in Hbeg |- *; try discriminate;
    try (exfalso; exact Hbeg). }
  rewrite Hev in HV.
  replace (sptr_addr B ly (ck_beg k) + (ck_rz k + ck_n k)
           + (a - (sptr_addr B ly (ck_user k) + ck_n k))) with a in HV by lia.
  apply HV. lia.
Qed.

(* A chunk's extent leaves room for the rounded-up user size above its redzone. *)
Lemma blk_extent_room : forall S k, chunk_ok S k ->
ck_rz k + rounded_size (ck_req k) <= ck_extent k.
Proof.
intros S k (Hreq & Hbeg).
pose proof (rz_size_bounds (ck_req k)) as [Hrz _].
pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [Hrs Hrsm].
unfold ck_rz, ck_extent, ck_n in *.
destruct (ck_beg k) as [| off | r off | cid pos] eqn:Ebeg; cbn in Hbeg; try (exfalso; exact Hbeg).
- (* primary: the class the chunk sits in is at least its needed size *)
  destruct Hbeg as (Hfp & _ & _).
  assert (HkM : needed_primary (ck_req k) <= kMaxSize)
  by (unfold from_primary in Hfp; apply Z.leb_le in Hfp; exact Hfp).
  assert (Hns : needed_size (ck_req k) = needed_primary (ck_req k))
  by (unfold needed_size; rewrite Hfp; reflexivity).
  pose proof (needed_primary_bounds (ck_req k) ltac:(lia)) as (_ & Hnp & _).
  pose proof (class_id_ok (needed_size (ck_req k)) ltac:(rewrite Hns; lia)) as [_ Hcs].
  rewrite Hfp. unfold chunk_class. rewrite Hns in Hcs |- *.
  assert (Hnp2 : needed_primary (ck_req k) = rounded_size (ck_req k) + rz_size (ck_req k)) by reflexivity.
  lia.
- (* secondary: the mapped size rounds the needed size up to a page, and the needed size has two redzones *)
  destruct Hbeg as (Hfp & _ & _). rewrite Hfp.
  assert (Hns : needed_size (ck_req k) = needed_primary (ck_req k) + rz_size (ck_req k))
  by (unfold needed_size; rewrite Hfp; reflexivity).
  pose proof (round_up_ge (needed_size (ck_req k)) kPage ltac:(unfold kPage; lia)) as [[Hru _] _].
  unfold sec_map_size. unfold needed_primary in Hns. lia.
Qed.

(* The bytes between a heap byte and the end of its 8-byte word are readable.
   The three wrapper contracts take this at x = p, j = k (the NUL's index). *)
Lemma blk_tail_present : forall ly S (W : world segs) mem md p n j a,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 <= j < req_size n ->
p + j < a < p + j - (p + j) mod 8 + 8 ->
aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md p n j a HAR Hin Hj Ha.
destruct (proj1 (In_ablocks B ly S p n) Hin) as (k & Hk & Hal & Hu & Hreq).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp0 & _).
pose proof (proj1 HAR) as HM.
pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf _ _ _ _ HM)) k Hk) as Hck.
pose proof (proj1 Hck) as Hq.
pose proof (blk_extent_room S k Hck) as Hroom.
pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [Hrs Hrsm].
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & _ & Hrq).
rewrite <- Hreq in Hj.
(* the end of the word that holds p + j lies inside the rounded-up user size *)
assert (Hp8 : p mod 8 = 0) by lia.
assert (Hmod : (p + j) mod 8 = j mod 8)
by (rewrite Z.add_mod by lia; rewrite Hp8, Z.add_0_l, Z.mod_mod by lia; reflexivity).
assert (Hru : p + j - (p + j) mod 8 + 8 <= p + rounded_size (ck_req k)).
{ rewrite Hmod.
  pose proof (Z.div_mod j 8 ltac:(lia)). pose proof (Z.mod_pos_bound j 8 ltac:(lia)).
  pose proof (Z.div_mod (rounded_size (ck_req k)) 8 ltac:(lia)). lia. }
apply (blk_chunk_vis ly S W mem md k a HAR Hk Hal).
rewrite Hu. lia.
Qed.
End c.
End b.
