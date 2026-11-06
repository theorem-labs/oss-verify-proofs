(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* fs's string kit: a C string carried across a program call in U form, for every fs walk that keeps a string across a
   call (ALLOC fuzz_strdup first; FSW_K imports this file by path, a Theorem Labs lane 21:40Z). The callee's journal runs over the
   memories with U's shadow bytes read as 0 (FSH_Gen.v afn_preU / fpostU), so the string is carried on that reading and
   moved back to the machine's memory by cstr_ok_unpoison / cstr_ok_poison.
   - cstr_ok_kept_tbl: the table arms of FSH_Rt.cstr_kept (FS_RO_STRS, FS_SN_FMTS) at any ARU state, from
     IMG : fs_img_facts (the table's bytes are image bytes, outside every live block, so none of their shadow is U's).
   - cstr_ok_kept_blkU: the block arm, over a journal that keeps the block and leaves the string out of its footprint
     (the bytes by the journal's block clause; the shadow by AR_shadow_law at the new state, whose block_shadow gives a
     block's last granule the shadow byte size mod 8 and which range_addressable_of_block's saddr_ok accepts byte by
     byte, so a block whose size is not a multiple of 8 is covered; the tail word by block_word_tail_vis).
   - cstr_ok_keptU: both, over FSH_Rt.cstr_kept; cstr_kept_kept: the home itself.
   STABLE NAMES AND STATEMENTS (other lanes import them).
   Ported from: a Theorem Labs lane's lib/A/FMW_kitS.v:21-114 (cstr_ok_kept, cstr_ok_kept_blk, cstr_kept_kept, shadow_hull_vis_sub,
   word_end_mono) and lib/A/FMW_kit.v:113-168 (block_word_tail_vis, fmw_word_end_le, fmw_extent_mod8), a working branch,
   restated in fs's U form. Renamed fmw_* -> fsk_*; fm's cstr_ok carries a 32-bit clause, fs's (S0
   7dd4849273a FSH_Gen.v cstr_ok) a length bound and amem_range over len + 8: the conjunct pattern follows fs's.
   fsk_segs_img is FSW_K.fs_segs_img restated (same proof) so that this file does not import FSW_K, which imports it.
   No Section hypothesis: IMG is a premise of the lemmas that use it. Rule 24: no function proved here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* every loaded byte of fs.asan lies below FS_IMG_END (FSW_K.fs_segs_img, restated) *)
Lemma fsk_segs_img : forall a, in_img tfibsegs a -> 0 <= a < FS_IMG_END.
Proof.
intros a (sg & Hin & Hr).
assert (Hb : forallb (fun s => (0 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? FS_IMG_END))
  tfibsegs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as H. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* ---- arithmetic (port of FMW_kitS.v:21-38 and FMW_kit.v:113-121) ---- *)
(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma shadow_hull_vis_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
assert (M1 : (2147450880 + x / 8) / 8 <= (2147450880 + x' / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1); lia).
assert (M2 : (2147450880 + (x' + n' - 1) / 8) / 8 <= (2147450880 + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
lia.
Qed.
(* the 8-byte word end is monotone *)
Lemma word_end_mono : forall x y, x <= y -> x - x mod 8 + 8 <= y - y mod 8 + 8.
Proof.
intros x y H. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
(* the 8-byte word end of a byte below an 8-aligned end stays at or below that end *)
Lemma fsk_word_end_le : forall x base ext, base mod 16 = 0 -> ext mod 8 = 0 -> x < base + ext ->
  x - x mod 8 + 8 <= base + ext.
Proof.
intros x base ext H1 H2 H3.
pose proof (Z.div_mod base 16 ltac:(lia)) as D1. pose proof (Z.div_mod ext 8 ltac:(lia)) as D2.
pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
lia.
Qed.
(* a chunk's extent is whole 8-byte words: primary class_size mod 32 = 0, secondary a page multiple less a page (YG0a.v) *)
Lemma fsk_extent_mod8 : forall k, 0 <= ck_req k -> ck_extent k mod 8 = 0.
Proof.
intros k Hq. unfold ck_extent. destruct (from_primary (ck_req k)) eqn:Ep.
- pose proof (primary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & H32 & _).
  set (c := class_size (chunk_class (ck_req k))) in *.
  pose proof (Z.div_mod c 32 ltac:(lia)) as D. pose proof (Z.div_mod c 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as R8. lia.
- pose proof (secondary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & _ & HP & _).
  set (s := sec_map_size (ck_req k)) in *. unfold kPage in *.
  pose proof (Z.div_mod s 4096 ltac:(lia)) as D. pose proof (Z.div_mod (s - 4096) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (s - 4096) 8 ltac:(lia)) as R8. lia.
Qed.

(* fs's read-only strings and formats are image bytes (vm_compute over FS_RO_STRS / FS_SN_FMTS and tfibsegs) *)
Definition seg_covers (p n : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? p) && (p + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs.
Lemma seg_covers_img : forall p n a, seg_covers p n = true -> p <= a < p + n -> in_img tfibsegs a.
Proof.
intros p n a H Ha. unfold seg_covers in H. apply existsb_exists in H as (s & Hs & Hss).
apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
Lemma fs_ro_strs_img : forall p l a, In (p, l) FS_RO_STRS -> p <= a < p + Z.of_nat (length l) + 1 -> in_img tfibsegs a.
Proof.
intros p l a Hin Ha.
assert (Hb : forallb (fun r : Z * list Z => seg_covers (fst r) (Z.of_nat (length (snd r)) + 1)) FS_RO_STRS = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb (p, l) Hin) as H. cbn [fst snd] in H.
exact (seg_covers_img _ _ a H ltac:(lia)).
Qed.
Lemma fs_sn_fmts_img : forall p ps a, In (p, ps) FS_SN_FMTS ->
  p <= a < p + Z.of_nat (length (fmt_bytes ps)) + 1 -> in_img tfibsegs a.
Proof.
intros p ps a Hin Ha.
assert (Hb : forallb (fun r : Z * list fpiece => seg_covers (fst r) (Z.of_nat (length (fmt_bytes (snd r))) + 1))
  FS_SN_FMTS = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb (p, ps) Hin) as H. cbn [fst snd] in H.
exact (seg_covers_img _ _ a H ltac:(lia)).
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- moving between the machine's memory and its unpoisoned reading (U form) ---- *)
(* a byte the unpoisoned reading shows is shown by the machine's memory too: U's shadow bytes read 0xf7 there *)
Lemma aview_unpoison_vis : forall U (W : world tfibsegs) m a, upoisoned tfibsegs W m U ->
  aview tfibsegs (w_H W) (unpoison U m) a <> None -> aview tfibsegs (w_H W) m a <> None.
Proof.
intros U W m a PO Hv. rewrite aview_mod in Hv |- *.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (a' := a mod 2 ^ 64) in *. clearbody a'.
destruct (in_ush U a') eqn:E.
- rewrite (PO a' E). discriminate.
- rewrite (aview_unpoison_out tfibsegs (w_H W) U m a') in Hv; [exact Hv | rewrite (wz a' Ha); exact E].
Qed.
Lemma aview_poison_vis : forall U (W : world tfibsegs) m a,
  aview tfibsegs (w_H W) m a <> None -> aview tfibsegs (w_H W) (unpoison U m) a <> None.
Proof.
intros U W m a Hv. rewrite aview_mod in Hv |- *.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (a' := a mod 2 ^ 64) in *. clearbody a'.
destruct (w_H W (Z_to_bv 64 a')) eqn:Hh.
- rewrite (aview_hidden_same tfibsegs (w_H W) (unpoison U m) m a' Hh). exact Hv.
- destruct (in_ush U a') eqn:E.
  + rewrite (aview_vis_byte tfibsegs (w_H W) (unpoison U m) a' (Z_to_bv 8 0) Hh); [discriminate|].
    apply unpoison_in. rewrite (wz a' Ha). exact E.
  + rewrite (aview_unpoison_out tfibsegs (w_H W) U m a'); [exact Hv | rewrite (wz a' Ha); exact E].
Qed.
(* a shadow byte outside U reads the same both ways *)
Lemma aview_unpoison_sh : forall U (W : world tfibsegs) m s, 0 <= s < 2 ^ 64 -> in_ush U s = false ->
  aview tfibsegs (w_H W) (unpoison U m) s = aview tfibsegs (w_H W) m s.
Proof. intros U W m s Hs E. apply (aview_unpoison_out tfibsegs). rewrite (wz s Hs). exact E. Qed.
(* an addressable byte's shadow byte is not user-poisoned (its value is < 8, U's read 0xf7) *)
Lemma ush_off_addressable : forall U (W : world tfibsegs) m p n x, upoisoned tfibsegs W m U ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF p n -> p <= x < p + n -> in_ush U (shadow_addr x) = false.
Proof.
intros U W m p n x PO Hra Hx. destruct (in_ush U (shadow_addr x)) eqn:E; [|reflexivity]. exfalso.
destruct (Hra x Hx) as (v & Hv & Hok). change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hv.
rewrite (PO _ E) in Hv. injection Hv as <-. unfold saddr_ok in Hok. lia.
Qed.
(* an application byte (below the shadow, or in high memory) is no user-poisoned shadow byte *)
Lemma unpoison_app : forall ly S U (W : world tfibsegs) m md a, ARU tfibsegs B ly S U W m md ->
  0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a ->
  unpoison U m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros ly S U W m md a H Ha Happ. apply unpoison_out. rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
destruct (ush_facts tfibsegs B ly S U W m md a H E) as (_ & L1 & L2). lia.
Qed.
Lemma mbyte_unpoison_app : forall ly S U (W : world tfibsegs) m md a, ARU tfibsegs B ly S U W m md ->
  0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a ->
  mbyte tfibsegs (mrestrict (w_H W) (unpoison U m)) a = mbyte tfibsegs (mrestrict (w_H W) m) a.
Proof.
intros ly S U W m md a H Ha Happ. unfold mbyte, mrestrict.
destruct (w_H W (Z_to_bv 64 a)); [reflexivity|]. rewrite (unpoison_app ly S U W m md a H Ha Happ). reflexivity.
Qed.

(* cstr_ok read on the unpoisoned memory is cstr_ok on the machine's memory when no shadow byte of the string is U's *)
Lemma cstr_ok_unpoison : forall ly S U (W : world tfibsegs) m md p l, ARU tfibsegs B ly S U W m md ->
  (forall x, p <= x < p + Z.of_nat (length l) + 1 -> in_ush U (shadow_addr x) = false) ->
  cstr_ok tfibsegs W (unpoison U m) p l -> cstr_ok tfibsegs W m p l.
Proof.
intros ly S U W m md p l H Hsh ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof H as (_ & _ & PO).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  symmetry. apply (mbyte_unpoison_app ly S U W m md a H); unfold amem_range, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ intros x Hx. destruct (Hra x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hv |- *.
  rewrite <- (aview_unpoison_sh U W m (shadow_addr x)); [exact Hv | | exact (Hsh x ltac:(lia))].
  unfold shadow_addr, SHADOW_OFF. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia. }
split.
{ intros s Hs. exact (aview_unpoison_vis U W m s PO (Hhv s Hs)). }
intros a Ha. exact (aview_unpoison_vis U W m a PO (Htl a Ha)).
Qed.
Lemma cstr_ok_poison : forall ly S U (W : world tfibsegs) m md p l, ARU tfibsegs B ly S U W m md ->
  cstr_ok tfibsegs W m p l -> cstr_ok tfibsegs W (unpoison U m) p l.
Proof.
intros ly S U W m md p l H ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof H as (_ & _ & PO).
assert (Hsh : forall x, p <= x < p + Z.of_nat (length l) + 1 -> in_ush U (shadow_addr x) = false)
  by (intros x Hx; exact (ush_off_addressable U W m p _ x PO Hra ltac:(lia))).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_unpoison_app ly S U W m md a H); unfold amem_range, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ intros x Hx. destruct (Hra x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hv |- *.
  rewrite (aview_unpoison_sh U W m (shadow_addr x)); [exact Hv | | exact (Hsh x ltac:(lia))].
  unfold shadow_addr, SHADOW_OFF. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia. }
split.
{ intros s Hs. exact (aview_poison_vis U W m s (Hhv s Hs)). }
intros a Ha. exact (aview_poison_vis U W m a (Htl a Ha)).
Qed.

(* ---- a live heap block is visible from its start to the end of the 8-byte word holding its last byte (port of
   FMW_kit.v:137-168: the block bytes by al_blocks, the bytes after it by ARm am_junk over the chunk's tail junk) ---- *)
Lemma block_word_tail_vis : forall ly S (W : world tfibsegs) mem md b m,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 < m ->
  forall a, b <= a < (b + m - 1) - (b + m - 1) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros ly S W mem md b m HAR Hin Hm a Ha.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (Z_lt_le_dec a (b + m)) as [Hlt | Hge].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  apply (aview_some_of_apresent tfibsegs). exact (proj1 (Hpres a ltac:(lia))).
- destruct HAR as (M & _).
  apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & Hb16 & Huser & _ & _ & Hreq & Hext & _).
  rewrite Hn, Hrq in Hext.
  assert (Hcn : ck_n k = m) by (unfold ck_n; rewrite Hn; exact Hrq).
  pose proof (fsk_extent_mod8 k ltac:(lia)) as Hx8.
  pose proof (fsk_word_end_le (b + m - 1) (ck_base B ly k) (ck_extent k) Hb16 Hx8 ltac:(lia)) as Hend.
  pose proof (am_junk B ly S _ M) as HJ. rewrite Forall_forall in HJ.
  specialize (HJ (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k)).
  unfold range_vis in HJ. cbn [fst snd] in HJ.
  assert (NSH : forall e', sptr_exp (ck_beg k) <> ASh e') by (intros e'; destruct (ck_beg k); cbn; discriminate).
  rewrite (aeval_aoff B ly (sptr_exp (ck_beg k)) (ck_rz k + ck_n k) NSH) in HJ.
  assert (Eb : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
  replace a with (aeval B ly (sptr_exp (ck_beg k)) + (ck_rz k + ck_n k) + (a - (b + m))) by lia.
  apply HJ; [|lia].
  unfold ajunk. apply in_cons. apply in_cons.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_eq.
Qed.

(* ---- a string in a live block, carried over a journal (port of FMW_kitS.v:46-69): the bytes by the journal's
   block clause, the shadow by AR's block_shadow / shadow hull at the new state (AR_shadow_law; a block whose size is
   not a multiple of 8 has its last granule's shadow byte = size mod 8, which range_addressable_of_block's
   saddr_ok accepts byte by byte), the tail word by block_word_tail_vis. Generic in the journal's memories. ---- *)
Lemma cstr_ok_kept_blk : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> ~ inFP FP a) ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin Hin' Hb Hbm HnF
  ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b) Hin Hin'); [rewrite Hrq; lia | replace (b + (a - b)) with a by lia; apply HnF; lia]. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly' S' W' mem' md' b m p _ HAR' Hin' Hb). rewrite Hrq. lia. }
split.
{ destruct (al_shadow _ _ LAWS ly' S' W' mem' md' b m HAR' Hin') as (_ & Hhv').
  apply (shadow_hull_vis_sub _ b (req_size m) p _ Hhv' Hb); rewrite ?Hrq; lia. }
intros a Ha. apply (block_word_tail_vis ly' S' W' mem' md' b m HAR' Hin' Hm).
pose proof (word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.

(* the block arm in U form: the caller's journal runs over `unpoison U mem` .. `unpoison U' mem'`; the string's shadow
   bytes are not U's (it is addressable at the start, U's read 0xf7), and every range of U' is one of U or misses the
   string, so the string reads the same on the machine's memory at both ends *)
Lemma cstr_ok_kept_blkU : forall STK sp0 FP ly S U W mem md own ly' S' U' W' mem' md' k p l b m,
  ARU tfibsegs B ly S U W mem md ->
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' k ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> ~ inFP FP a) ->
  (forall r, In r U' -> In r U \/ fst r + snd r <= p \/ p + Z.of_nat (length l) + 1 <= fst r) ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S U W mem md own ly' S' U' W' mem' md' k p l b m H HJ OK' PO' Hin Hin' Hb Hbm HnF HU' Hc.
pose proof H as (_ & _ & PO).
pose proof Hc as (_ & _ & _ & _ & _ & Hra & _).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJ) | split; [exact OK' | exact PO']]).
pose proof (cstr_ok_poison ly S U W mem md p l H Hc) as Hc0.
pose proof (cstr_ok_kept_blk STK sp0 FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' k p l b m
  HJ Hin Hin' Hb Hbm HnF Hc0) as Hc1.
apply (cstr_ok_unpoison ly' S' U' W' mem' md' p l HARU'); [|exact Hc1].
intros x Hx. destruct (in_ush U' (shadow_addr x)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as (r & Hr & Hrs).
destruct (HU' r Hr) as [HrU | Hout].
- assert (E0 : in_ush U (shadow_addr x) = true) by (apply in_ush_spec; exists r; split; [exact HrU | exact Hrs]).
  rewrite (ush_off_addressable U W mem p _ x PO Hra ltac:(lia)) in E0. discriminate E0.
- destruct (upoison_ok_In B ly' S' U' r OK' Hr) as (A8 & L8 & M8 & _).
  destruct r as [q z]. cbn [fst snd] in *.
  apply Z.mod_divide in A8 as [a8 Ha8]; [|lia]. apply Z.mod_divide in M8 as [z8 Hz8]; [|lia]. subst q z.
  unfold shadow_addr in Hrs. rewrite !Z.div_mul in Hrs by lia.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
Qed.

(* the table arms (port of FMW_kitS.v:73-90's read-only arms): fs_img_facts re-derives cstr_ok at any ARU state for a
   string of FS_RO_STRS or a format of FS_SN_FMTS; the table's bytes are image bytes, outside every live block, so no
   shadow byte of theirs is U's *)
Lemma cstr_ok_kept_tbl : forall ly' S' U' (W' : world tfibsegs) mem' md' p l,
  fs_img_facts tfibsegs B -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem') ->
  (In (p, l) FS_RO_STRS \/ (exists ps, In (p, ps) FS_SN_FMTS /\ l = fmt_bytes ps)) ->
  cstr_ok tfibsegs W' mem' p l.
Proof.
intros ly' S' U' W' mem' md' p l IMG H HRO Harm.
pose proof H as (HAR & _ & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HROu : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') (unpoison U' mem'))).
{ intros a Hro Ho He. assert (Hb : 0 <= a < SHADOW_OFF).
  { destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [|unfold FS_RLO, FS_RHI, SHADOW_OFF in *; lia].
    pose proof (fsk_segs_img a (ex_intro _ sg (conj Hsg Hr))) as Hl. unfold FS_IMG_END, SHADOW_OFF in *. lia. }
  rewrite (aview_at tfibsegs (w_H W') (unpoison U' mem') mem' a); [exact (HRO a Hro Ho He)|].
  apply (unpoison_app ly' S' U' W' mem' md' a H); unfold SHADOW_OFF in *; lia. }
assert (Himg : forall a, p <= a < p + Z.of_nat (length l) + 1 -> in_img tfibsegs a).
{ destruct Harm as [Hs | (ps & Hf & ->)]; [exact (fun a => fs_ro_strs_img p l a Hs) | exact (fun a => fs_sn_fmts_img p ps a Hf)]. }
assert (Hc : cstr_ok tfibsegs W' (unpoison U' mem') p l).
{ destruct (proj2 IMG ly' S' W' (unpoison U' mem') md' HAR HROu) as (_ & _ & HS & HF).
  destruct Harm as [Hs | (ps & Hf & ->)].
  - exact (proj1 (proj1 (Forall_forall _ _) HS (p, l) Hs)).
  - exact (proj1 (HF p ps Hf)). }
apply (cstr_ok_unpoison ly' S' U' W' mem' md' p l H); [|exact Hc].
intros x Hx. pose proof (fsk_segs_img x (Himg x Hx)) as Hxl. unfold FS_IMG_END in Hxl.
pose proof (ARU_shadow_out_block tfibsegs B ly' S' U' W' mem' md' x H ltac:(lia)) as E.
rewrite (wz (shadow_addr x)) in E; [apply E|].
- intros q n Hq Hqx. exact (blk_img tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' q n x HAR Hq Hqx (Himg x Hx)).
- unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8). pose proof (Z.div_le_upper_bound x 8 (2 ^ 61)). lia.
Qed.

(* the home itself after a call that keeps every live block (port of FMW_kitS.v:93-100), over S0's cstr_kept with the
   poisoned-range set: every range of the new U' is one of U (which the block arm's string already avoids) or misses
   the string *)
Lemma cstr_kept_kept : forall ly S (U : list (Z * Z)) ly' S' (U' : list (Z * Z)) p l,
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  (forall r, In r U' -> In r U \/ fst r + snd r <= p \/ p + Z.of_nat (length l) + 1 <= fst r) ->
  cstr_kept B ly S U p l ->
  cstr_kept B ly' S' U' p l.
Proof.
intros ly S U ly' S' U' p l Hinc HU' [(b & m & Hin & H1 & H2 & HD) | Himg].
- left. exists b, m. split; [exact (Hinc _ Hin)|]. split; [exact H1|]. split; [exact H2|].
  intros r Hr. destruct (HU' r Hr) as [HrU | [Hd | Hd]]; [exact (HD r HrU) | right; exact Hd | left; exact Hd].
- right. exact Himg.
Qed.

(* cstr_ok of a kept string after a program call (port of FMW_kitS.v:73-90 in U form): the block arm by
   cstr_ok_kept_blkU (the footprint misses every block, the new ranges of U' miss the string), the table arms by
   cstr_ok_kept_tbl at the new state *)
Lemma cstr_ok_keptU : forall STK sp0 FP ly S U W mem md own ly' S' U' W' mem' md' k p l,
  fs_img_facts tfibsegs B ->
  ARU tfibsegs B ly S U W mem md ->
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' k ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  (forall a, inFP FP a -> in_img tfibsegs a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem') ->
  cstr_kept B ly S U p l ->
  (forall r, In r U' -> In r U \/ fst r + snd r <= p \/ p + Z.of_nat (length l) + 1 <= fst r) ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S U W mem md own ly' S' U' W' mem' md' k p l IMG H HJ OK' PO' Hinc HFP HRO' Hk HU' Hc.
pose proof HJ as (HAR' & _).
destruct Hk as [(b & m & Hin & Hb & Hbm & HD) | Htbl].
- (* the block arm's own conjunct HD: the string misses every range of U; so every range of U' misses it *)
  assert (HU2 : forall r, In r U' -> In r U \/ fst r + snd r <= p \/ p + Z.of_nat (length l) + 1 <= fst r).
  { intros r Hr. destruct (HU' r Hr) as [HrU | Hd]; [right | right; exact Hd].
    destruct (HD r HrU) as [Hd | Hd]; [right; exact Hd | left; exact Hd]. }
  apply (cstr_ok_kept_blkU STK sp0 FP ly S U W mem md own ly' S' U' W' mem' md' k p l b m H HJ OK' PO' Hin
    (Hinc _ Hin) Hb Hbm); [| exact HU2 | exact Hc].
  intros a Ha Hf. apply (blk_img tfibsegs B LAWS ly' S' W' (unpoison U' mem') md' b m a HAR' (Hinc _ Hin));
    [| exact (HFP a Hf)].
  assert (req_size m = m) as -> by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
- exact (cstr_ok_kept_tbl ly' S' U' W' mem' md' p l IMG
    (conj HAR' (conj OK' PO')) HRO' Htbl).
Qed.
End s.
