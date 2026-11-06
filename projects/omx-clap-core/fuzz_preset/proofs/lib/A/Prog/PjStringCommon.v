(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the IMAGE-FREE pieces of pj_string's walks (fuzz_preset), ONE copy for image A
   (lib/A/Prog, slice S6) and image B (lib/B/Prog/pj_string_*.v): the node bytes pjs_bytes, the two tree predicates
   the text's post asks of them, and what fuzz_strdup's post keeps. Generic over the program listing {L} and its image
   facts {PA : PAImg L}; no lib/B import. proves no function (kind: glue lemmas).
   MOVED, statements unchanged, from h-rw-man-5's image-B lane at origin/cold/h-rw-man-5-b-pjstring eb3168fa754
   (lib/B/Prog/...; blobs pj_string_defs.v 5fceaf024172, pj_string_glue.v 86013eff7ee9, pj_string_seg_call.v
   1b23b24e9410):
     pjs_bytes (Definition)  pj_string_defs.v:190-191
     zc (Ltac)               pj_string_glue.v:40
     pjs_bytes_len           pj_string_glue.v:44-45
     pjs_bytes_0             pj_string_glue.v:46-47
     pjs_bytes_range         pj_string_glue.v:48-56
     pjs_bytes_nth           pj_string_glue.v:58-64
     pjs_le_byte_1_0         pj_string_glue.v:66-71
     pjs_val_of_garr8        pj_string_glue.v:73-83
     pjs_le_byte_0           pj_string_glue.v:84-85
     pjs_hdr                 pj_string_glue.v:88-117
     pjs_node_str            pj_string_glue.v:120-132
     pjs_fd0                 pj_string_glue.v:135-143
     pjs1_app_disj           pj_string_seg_call.v:81-90
     pjs1_fsb8               pj_string_seg_call.v:93-102
     pjs1_val_keep           pj_string_seg_call.v:145-152
     pjs1_garr8_keep         pj_string_seg_call.v:153-159
     pjs1_hblock_kept        pj_string_seg_call.v:162-171
     pjs1_heads              pj_string_seg_call.v:174-181
     pjs1_blocks             pj_string_seg_call.v:184-201
   MOVED SECOND, statements and proofs unchanged, from h-rw-man-5's segment C2 (lib/B/Prog/pj_string_seg_ep.v blob
   e3ec811117c7, byte-identical at origin/cold/h-rw-man-5-b-pjstring-rb 09795a156cae and b251eef6c02):
     PJS2_A0 (Definition)    pj_string_seg_ep.v:70-71
     pjs2_a0                 pj_string_seg_ep.v:77-86
     pjs2_blocks_kept        pj_string_seg_ep.v:200-208
     pjs2_hull_bounds        pj_string_seg_ep.v:210-224
     pjs2_post_keep          pj_string_seg_ep.v:226-267
     pjs2_mbyte_word         pj_string_seg_ep.v:269-271 (pjs2_full uses it)
     pjs2_bytes_final        pj_string_seg_ep.v:273-306
     pjs2_full               pj_string_seg_ep.v:308-327
   Section tail: image B's PA := PI_prog_B and SEGS / PST over it become {L} {PA} / pa_segs and {PI : PrhImg}'s
   prh_pst; the statements' text is unchanged. B is the leading explicit argument of pjs2_blocks_kept and
   pjs2_post_keep, as in the source (its Section ep's B).
   The only change for the generic form: image B's `PA := PI_prog_B` / `SEGS := @pa_segs _ B_prog_listing PA` and its
   instance prh_img_B become the Section's {L} {PA} / pa_segs and {PI : PrhImg}. Section call's B, ARx and LAWS stay
   Section variables, as in the source; outside the Section they are the leading explicit arguments of
   pjs1_hblock_kept (B), pjs1_heads (B) and pjs1_blocks (B ARx LAWS).
   Section hypothesis: AR_laws_x pa_segs B ARx cf_head (the kit's laws).
   Numerals: 56 / 16 / 8 / 4 (LENGTH: node, field offsets, word); 4 (the JStr tag, PjTree.tag); 64 / 32 / 2
   (LENGTH: fs_frame_bytes' base and halvings). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
(* a closed range goal 0 <= x < y, by computation *)
Ltac zc := split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.

(* v's 56 bytes after the memset and the type store: type 4, every other byte 0 but the str word at v + 16 *)
Definition pjs_bytes (str : Z) : list Z := [4; 0; 0; 0] ++ repeat 0 12 ++ map (fun k => le_byte str 8 k) (seq 0 8) ++
  repeat 0 32.

(* ---- the node bytes ---- *)
Lemma pjs_bytes_len : forall str, length (pjs_bytes str) = 56%nat.
Proof. intros str. reflexivity. Qed.
Lemma pjs_bytes_0 : pjs_bytes 0 = [4; 0; 0; 0] ++ repeat 0 52.
Proof. vm_compute. reflexivity. Qed.
Lemma pjs_bytes_range : forall str, Forall (fun b => 0 <= b < 256) (pjs_bytes str).
Proof.
intros str. unfold pjs_bytes. rewrite !Forall_app.
split; [apply Forall_forall; intros x Hx; cbn [In] in Hx; lia|].
split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|].
split; [|apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia].
apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (k & <- & _). unfold le_byte.
apply Z.mod_pos_bound. lia.
Qed.
(* the byte at offset i of the node *)
Lemma pjs_bytes_nth : forall str (i : nat), (i < 56)%nat ->
  nth i (pjs_bytes str) 0 =
  if (i =? 0)%nat then 4 else if ((16 <=? i) && (i <? 24))%nat then le_byte str 8 (i - 16) else 0.
Proof.
intros str i Hi.
do 56 (destruct i as [|i]; [reflexivity|]). exfalso. lia.
Qed.
(* a byte value read back at width 1 *)
Lemma pjs_le_byte_1_0 : forall z, 0 <= z < 256 -> le_byte z 1 0 = z.
Proof.
intros z Hz. unfold le_byte.
assert (E0 : 8 * Z.of_nat 0 = 0) by reflexivity. assert (E1 : 2 ^ (8 * Z.of_nat 1) = 256) by reflexivity.
rewrite E0, E1, Z.shiftr_0_r. rewrite (Z.mod_small z 256) by lia. rewrite (Z.mod_small z 256) by lia. reflexivity.
Qed.
(* a value read from a byte array, at a byte offset *)
Lemma pjs_val_of_garr8 : forall (segs : list Segment) m a l (off n : nat) v,
  garr8 segs m a l -> (off + n <= length l)%nat ->
  (forall k, (k < n)%nat -> nth (off + k) l 0 = le_byte v n k) ->
  val_mem segs m (a + Z.of_nat off) n v.
Proof.
intros segs m a l off n v Hg Hlen Hk k Hkn.
destruct (Hg (off + k)%nat ltac:(lia)) as [Hv Hr].
specialize (Hv 0%nat ltac:(lia)). rewrite (Hk k Hkn) in Hv, Hr.
replace (a + Z.of_nat off + Z.of_nat k) with (a + Z.of_nat (off + k) + Z.of_nat 0) by lia.
rewrite Hv. f_equal. f_equal. apply pjs_le_byte_1_0. exact Hr.
Qed.
Lemma pjs_le_byte_0 : forall n k, le_byte 0 n k = 0.
Proof. intros n k. unfold le_byte. rewrite Zmod_0_l, Z.shiftr_0_l, Zmod_0_l. reflexivity. Qed.

(* the header the node bytes give: type 4, str at +16, every other field 0 *)
Lemma pjs_hdr : forall (segs : list Segment) m v str, 0 <= str < 2 ^ 64 ->
  garr8 segs m v (pjs_bytes str) -> pj_rwR segs m v -> pj_hdrR segs m v 4 0 str 0 0 0 0.
Proof.
intros segs m v str Hstr Hg Hrw.
assert (V : forall (off n : nat) x, (off + n <= 56)%nat ->
  (forall k, (k < n)%nat -> nth (off + k) (pjs_bytes str) 0 = le_byte x n k) ->
  val_mem segs m (v + Z.of_nat off) n x).
{ intros off n x Hl Hk. apply (pjs_val_of_garr8 segs m v (pjs_bytes str) off n x Hg); [rewrite pjs_bytes_len; exact Hl | exact Hk]. }
assert (Z0 : forall off, (off + 8 <= 56)%nat -> (off + 8 <= 16 \/ 24 <= off)%nat -> (1 <= off)%nat ->
  val_mem segs m (v + Z.of_nat off) 8 0).
{ intros off Hl Ho H1. apply V; [exact Hl|]. intros k Hk. rewrite pjs_bytes_nth by lia. rewrite pjs_le_byte_0.
  destruct (Nat.eqb_spec (off + k) 0); [lia|].
  destruct ((16 <=? off + k)%nat && (off + k <? 24)%nat)%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. lia. }
assert (T : val_mem segs m v 4 4).
{ assert (H0 : val_mem segs m (v + Z.of_nat 0) 4 4).
  { apply V; [lia|]. intros k Hk. rewrite pjs_bytes_nth by lia. do 4 (destruct k as [|k]; [reflexivity|]). lia. }
  change (v + Z.of_nat 0) with (v + 0) in H0. rewrite Z.add_0_r in H0. exact H0. }
assert (STR : val_mem segs m (v + 16) 8 str).
{ apply (V 16%nat 8%nat str); [lia|].
  intros k Hk. rewrite pjs_bytes_nth by lia. do 8 (destruct k as [|k]; [reflexivity|]). lia. }
split; [exact Hrw|].
split; [split; [zc | exact T]|].
split; [split; [zc | exact (Z0 8%nat ltac:(lia) ltac:(lia) ltac:(lia))]|].
split; [split; [exact Hstr | exact STR]|].
split; [split; [zc | exact (Z0 24%nat ltac:(lia) ltac:(lia) ltac:(lia))]|].
split; [split; [zc | exact (Z0 32%nat ltac:(lia) ltac:(lia) ltac:(lia))]|].
split; [split; [zc | exact (Z0 40%nat ltac:(lia) ltac:(lia) ltac:(lia))]|].
split; [zc | exact (Z0 48%nat ltac:(lia) ltac:(lia) ltac:(lia))].
Qed.

(* The success post: the string node over its one block *)
Lemma pjs_node_str : forall (segs : list Segment) m lblk v a k cs,
  pj_hdrR segs m v 4 0 a 0 0 0 0 -> pj_cstrR segs m lblk a k cs ->
  (forall x, a <= x < a + k -> ~ (v <= x < v + 56)) ->
  pj_nodeR segs m lblk v (PjTree.JStr cs) [(a, k)].
Proof.
intros segs m lblk v a k cs Hh Hc Hap. cbn [pj_nodeR].
refine (conj _ (conj _ _)).
{ first [ apply NoDup_singleton | constructor; [intros Hin; inversion Hin | constructor] ]. }
{ intros b x Hb Hx. destruct Hb as [<- | []]. unfold pj_holdsR in Hx. cbn [fst snd] in Hx. exact (Hap x Hx). }
exists 0, a, 0, 0, 0, 0. split; [exact Hh|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
exists k. split; [exact Hc | reflexivity].
Qed.

(* The failure post: v freeable to depth 0 with no block *)
Lemma pjs_fd0 : forall (segs : list Segment) m lblk v,
  pj_hdrR segs m v 4 0 0 0 0 0 0 -> pj_fdR segs m lblk 0 v [].
Proof.
intros segs m lblk v Hh. cbn [pj_fdR]. unfold pj_fshapeR.
split; [constructor|]. split; [intros b x [] |].
exists 4, 0, 0, 0, 0, 0, 0, false, [], [], [], []. split; [exact Hh|].
split; [left; split; reflexivity|]. split; [left; repeat split; reflexivity|].
split; [left; repeat split; reflexivity|]. split; [apply Permutation_refl|]. split; reflexivity.
Qed.

(* the old blocks of a list with one block appended are each apart from it *)
Lemma pjs1_app_disj : forall (l : list (Z * Z)) x y,
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (l ++ [x])) -> In y l ->
  zdisjoint (fst y, req_size (snd y)) (fst x, req_size (snd x)).
Proof.
intros l x y. induction l as [|z l IH]; intros Hp Hy; [destruct Hy|].
cbn [app map pairwise] in Hp. destruct Hp as [HF Hp].
destruct Hy as [<- | Hy]; [|exact (IH Hp Hy)].
rewrite Forall_forall in HF. apply HF. apply in_map_iff. exists x. split; [reflexivity|].
apply in_or_app. right. left. reflexivity.
Qed.

(* a fake frame that holds a node (56 bytes) has a size class cid >= 0, so its size is a multiple of 8 *)
Lemma pjs1_fsb8 : forall cid, 56 <= fs_frame_bytes cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. destruct (Z_lt_le_dec cid 0) as [Hn | Hp].
- exfalso. unfold fs_frame_bytes in H. rewrite Z.shiftl_div_pow2 in H by lia.
  assert (H2 : 2 ^ 1 <= 2 ^ (- cid)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 1) with 2 in H2.
  assert (H3 : 64 / 2 ^ (- cid) <= 64 / 2) by (apply Z.div_le_compat_l; lia).
  change (64 / 2) with 32 in H3. lia.
- unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
  replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring. apply Z_mod_mult.
Qed.

Section call. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* bytes ride through a change that keeps their views (pj_parse_seg_ent.v pje_val_keep / pje_garr8_keep) *)
Lemma pjs1_val_keep : forall (W W' : world SEGS) m m' a (n : nat) v, val_mem SEGS (mrestrict (w_H W) m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v Hv Hk k Hkn. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)).
- exact (Hv k Hkn).
- apply Hk. lia.
Qed.
Lemma pjs1_garr8_keep : forall (W W' : world SEGS) m m' a l, garr8 SEGS (mrestrict (w_H W) m) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (mrestrict (w_H W') m') a l.
Proof.
intros W W' m m' a l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pjs1_val_keep W W' m m' _ 1 _ Hv). intros x Hx. apply Hk. cbn [Z.of_nat] in Hx. lia.
Qed.

(* the harness blocks of the entry ledger stay harness blocks across fuzz_strdup (its ledger lists them) *)
Lemma pjs1_hblock_kept : forall n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 a k,
  prh_alloc_post (PA := PA) B n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 -> In (a, k) Lam ->
  In (a - cf_head, k + cf_head) (ablocks B ly2 S2) /\ In (a - cf_head) Hp2.
Proof.
intros n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 a k HP Hin.
destruct HP as [(_ & _ & _ & _ & HL) | [(_ & _ & _ & _ & _ & _ & HL) | (_ & _ & _ & _ & _ & _ & _ & _ & _ & HL)]].
- destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HL Hin) as (_ & Hab & Hhp & _). auto.
- destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HL Hin) as (_ & Hab & Hhp & _). auto.
- destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HL (or_intror Hin)) as (_ & Hab & Hhp & _). auto.
Qed.

(* the heads hidden after fuzz_strdup: the entry's, and on success the new block's *)
Lemma pjs1_heads : forall n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2,
  prh_alloc_post (PA := PA) B n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 ->
  forall h, In h Hp2 -> In h Hp \/ (res <> 0 /\ h = res - cf_head).
Proof.
intros n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 HP h Hh.
destruct HP as [(_ & _ & -> & _) | [(_ & _ & -> & _) | (_ & Hr & _ & _ & -> & _)]]; [left; exact Hh | left; exact Hh|].
pose proof cf_head_nonneg. destruct Hh as [<- | Hh]; [right; split; [lia | reflexivity] | left; exact Hh].
Qed.

(* the entry's blocks are blocks after fuzz_strdup; on success the new block, apart from each of them *)
Lemma pjs1_blocks : forall n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 md2,
  prh_alloc_post (PA := PA) B n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 ->
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  (forall b, In b (ablocks B ly S) -> In b (ablocks B ly2 S2)) /\
  (res <> 0 -> In (res - cf_head, n + cf_head) (ablocks B ly2 S2) /\
     forall b, In b (ablocks B ly S) -> zdisjoint (fst b, req_size (snd b)) (res - cf_head, req_size (n + cf_head))).
Proof.
intros n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 md2 HP HAR2.
destruct HP as [(_ & Hr & _ & E & _) | [(_ & Hr & _ & E & _) | (_ & _ & _ & _ & _ & E & _)]].
- split; [intros b Hb; rewrite E; exact Hb | intros Hn; exfalso; exact (Hn Hr)].
- split; [intros b Hb; rewrite E; exact Hb | intros Hn; exfalso; exact (Hn Hr)].
- assert (Hin : In (res - cf_head, n + cf_head) (ablocks B ly2 S2))
    by (rewrite E; apply in_or_app; right; left; reflexivity).
  split; [intros b Hb; rewrite E; apply in_or_app; left; exact Hb|].
  intros _. split; [exact Hin|]. intros b Hb.
  destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hin) as (_ & _ & _ & _ & _ & Hpw).
  rewrite E in Hpw. exact (pjs1_app_disj _ (res - cf_head, n + cf_head) b Hpw Hb).
Qed.
End call.

(* ======== the tail of pj_string: MOVED (statements and proofs unchanged) from h-rw-man-5's image-B segment C2,
   lib/B/Prog/pj_string_seg_ep.v (blob e3ec811117c7, origin/cold/h-rw-man-5-b-pjstring-rb 09795a156cae = b251eef6c02) ======== *)
(* a0 after `snez a1, a0; addi a1, a1, -1; mv a0, a1`, as the engine leaves it *)
Definition PJS2_A0 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 10 0)) (SLit (-1))) (SLit 0).

Lemma pjs2_a0 : forall E res, ew E 10 = Z_to_bv 64 res -> 0 <= res < 2 ^ 64 ->
  sv_denot E PJS2_A0 = w64 (if res =? 0 then -1 else 0).
Proof.
intros E res H10 Hr. apply bv_eq. change (bv_unsigned (sv_denot E PJS2_A0)) with (U E PJS2_A0). unfold PJS2_A0.
rewrite !U_SAlu, !U_SLit, (U_atom E 10 res H10 Hr). cbn [zalu_raw].
destruct (Z.eqb_spec res 0) as [-> | Hn].
- vm_compute. reflexivity.
- replace (zcanon 0 <? res) with true by (symmetry; apply Z.ltb_lt; unfold zcanon, M64; rewrite Z.mod_0_l by lia; lia).
  vm_compute. reflexivity.
Qed.

Section tail. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PA).
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the allocator blocks of the entry survive fuzz_strdup (its three arms keep them, the third one appends) *)
Lemma pjs2_blocks_kept : forall n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2,
  prh_alloc_post (PA := PA) B n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 ->
  forall b, In b (ablocks B ly S) -> In b (ablocks B ly2 S2).
Proof.
intros n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 HP b Hb.
destruct HP as [(_ & _ & _ & E & _) | [(_ & _ & _ & E & _) | (_ & _ & _ & _ & _ & E & _)]]; rewrite E;
  [exact Hb | exact Hb | apply in_or_app; left; exact Hb].
Qed.

(* the shadow hull of an application range below kHighMemEnd lies in the shadow region (pj_parse_seg_ent.v
   pje_hull_bounds) *)
Lemma pjs2_hull_bounds : forall x n s, 0 <= x -> 0 < n -> x + n <= kHighMemEnd ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighShadowEnd.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr, kLowMemEnd, kHighShadowEnd, kHighMemEnd, SHADOW_OFF in *.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
assert (P3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *.
lia.
Qed.

(* prh_alloc_post rides through a memory change that keeps every byte the post reads *)
Lemma pjs2_post_keep : forall n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 mem3,
  prh_alloc_post (PA := PA) B n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 ->
  (res = 0 -> forall a, aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  (res <> 0 -> 0 <= res /\ res + n <= kHighMemEnd) ->
  (res <> 0 -> forall a, (Exists (in_zr a) prh_pst \/ (exists x k i, In (x, k) ((res, n) :: Lam) /\ 0 <= i < 8 /\
       a = x - cf_head + i) \/ (res <= a < res + n) \/ (kLowMemEnd <= a < kHighShadowEnd)) ->
     aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  prh_alloc_post (PA := PA) B n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem3.
Proof.
intros n ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 mem3 HP K0 KB K1.
destruct HP as [(Hc & Hr & EHp & Eab & HL) | [(Hc & Hr & EHp & Eab & Hnull & Herr & HL) |
  (Hc & Hr4 & Hr16 & Hnin & EHp & Eab & Hra & Hhull & Hbytes & HL)]].
- left. pose proof (K0 Hr) as K.
  split; [exact Hc|]. split; [exact Hr|]. split; [exact EHp|]. split; [exact Eab|].
  apply (prh_ledger_kept_aview B ly2 S2 Hp2 W2 mem2 ly2 S2 Hp2 W2 mem3 _ _ _ _ _ _ _ HL);
    [intros a _; apply K | intros a k i _ _; apply K | intros a k _ H; exact H | apply Permutation_refl].
- right; left. pose proof (K0 Hr) as K.
  split; [exact Hc|]. split; [exact Hr|]. split; [exact EHp|]. split; [exact Eab|]. split; [exact Hnull|].
  split; [intros k Hk; rewrite K; exact (Herr k Hk)|].
  apply (prh_ledger_kept_aview B ly2 S2 Hp2 W2 mem2 ly2 S2 Hp2 W2 mem3 _ _ _ _ _ _ _ HL);
    [intros a _; apply K | intros a k i _ _; apply K | intros a k _ H; exact H | apply Permutation_refl].
- right; right. pose proof cf_head_nonneg as Hh0. assert (Hr0 : res <> 0) by lia.
  pose proof (K1 Hr0) as K. destruct (KB Hr0) as (Hres0 & Hresn).
  split; [exact Hc|]. split; [exact Hr4|]. split; [exact Hr16|]. split; [exact Hnin|]. split; [exact EHp|].
  split; [exact Eab|].
  split.
  { eapply range_addressable_agree; [|exact Hra]. intros x Hx. apply K. right; right; right.
    unfold shadow_of_addr. pose proof (shadow_addr_bounds x ltac:(lia)) as Sb. unfold shadow_addr in Sb. exact Sb. }
  split.
  { intros Hn s Hs. rewrite K; [exact (Hhull Hn s Hs)|]. right; right; right.
    exact (pjs2_hull_bounds res n s ltac:(lia) Hn ltac:(lia) Hs). }
  split.
  { destruct Hbytes as (l & Hl & Hg). exists l. split; [exact Hl|].
    unfold bytes_at in *. apply (garr8R_frame SEGS (rdW W2 mem2) (rdW W2 mem3) res l Hg).
    intros x Hx. apply (mbyte_of_aview SEGS). apply K. right; right; left. lia. }
  apply (prh_ledger_kept_aview B ly2 S2 Hp2 W2 mem2 ly2 S2 Hp2 W2 mem3 _ _ _ _ _ _ _ HL).
  + intros a Ha. apply K. left. exact Ha.
  + intros a k i Hin Hi. apply K. right; left. exists a, k, i. auto.
  + intros a k _ H. exact H.
  + apply Permutation_refl.
Qed.

(* a byte of the view is the byte of its 64-bit address *)
Lemma pjs2_mbyte_word : forall m (b : Z), mbyte SEGS m b = mbyte SEGS m (bv_unsigned (Z_to_bv 64 b)).
Proof. intros m b. unfold mbyte. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* the node's bytes after the run: the cut's bytes with the str word res *)
Lemma pjs2_bytes_final : forall (W : world SEGS) mem mem3 v res,
  garr8 SEGS (rdW W mem) v (pjs_bytes 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a) ->
  val_mem SEGS (rdW W mem3) (v + 16) 8 res -> 0 <= v -> v + 56 <= 2 ^ 64 ->
  garr8 SEGS (rdW W mem3) v (pjs_bytes res).
Proof.
intros W mem mem3 v res HB K VS Hv0 Hv1 j Hj. rewrite pjs_bytes_len in Hj.
split; [|apply (proj1 (Forall_forall _ _) (pjs_bytes_range res)); apply nth_In; rewrite pjs_bytes_len; exact Hj].
intros k Hk. assert (Ek : k = 0%nat) by lia. subst k.
destruct (Nat.leb_spec 16 j) as [H16 | H16]; [destruct (Nat.ltb_spec j 24) as [H24 | H24]|].
- (* the str word *)
  specialize (VS (j - 16)%nat ltac:(lia)).
  replace (v + Z.of_nat j + Z.of_nat 0) with (v + 16 + Z.of_nat (j - 16)) by lia. rewrite VS.
  rewrite pjs_bytes_nth by lia.
  replace (j =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
  replace ((16 <=? j) && (j <? 24))%nat with true
    by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  rewrite pjs_le_byte_1_0; [reflexivity|]. unfold le_byte. apply Z.mod_pos_bound. lia.
- (* past the str word: the cut's byte *)
  destruct (HB j ltac:(rewrite pjs_bytes_len; lia)) as [Hv _].
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem3); [|apply K; lia].
  rewrite (Hv 0%nat ltac:(lia)). rewrite !pjs_bytes_nth by lia.
  replace ((16 <=? j) && (j <? 24))%nat with false
    by (symmetry; apply andb_false_intro2; apply Nat.ltb_ge; lia).
  reflexivity.
- (* below the str word: the cut's byte *)
  destruct (HB j ltac:(rewrite pjs_bytes_len; lia)) as [Hv _].
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem3); [|apply K; lia].
  rewrite (Hv 0%nat ltac:(lia)). rewrite !pjs_bytes_nth by lia.
  replace ((16 <=? j) && (j <? 24))%nat with false
    by (symmetry; apply andb_false_intro1; apply Nat.leb_gt; lia).
  reflexivity.
Qed.

(* res = 0: the run stored 0 over the zero str word, so the view is the cut's everywhere *)
Lemma pjs2_full : forall (W : world SEGS) mem mem3 v,
  (forall x : word, ~ (v + 16 <= bv_unsigned x < v + 24) -> mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem x) ->
  garr8 SEGS (rdW W mem) v (pjs_bytes 0) -> garr8 SEGS (rdW W mem3) v (pjs_bytes 0) ->
  forall a, aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a.
Proof.
intros W mem mem3 v KW B0 B3 a. unfold aview. f_equal.
rewrite (pjs2_mbyte_word (rdW W mem3) a), (pjs2_mbyte_word (rdW W mem) a).
set (y := bv_unsigned (Z_to_bv 64 a)).
assert (Hy : 0 <= y < 2 ^ 64) by (unfold y; apply u64_range).
destruct (Z_le_dec (v + 16) y) as [H1 | H1]; [destruct (Z_lt_dec y (v + 24)) as [H2 | H2]|].
- set (j := Z.to_nat (y - v)).
  destruct (B3 j ltac:(rewrite pjs_bytes_len; unfold j; lia)) as [V3 _].
  destruct (B0 j ltac:(rewrite pjs_bytes_len; unfold j; lia)) as [V0 _].
  specialize (V3 0%nat ltac:(lia)). specialize (V0 0%nat ltac:(lia)).
  replace (v + Z.of_nat j + Z.of_nat 0) with y in V3, V0 by (unfold j; lia).
  rewrite V3, V0. reflexivity.
- unfold mbyte. rewrite (KW (Z_to_bv 64 y)); [reflexivity|]. rewrite unsigned_lit_small by lia. lia.
- unfold mbyte. rewrite (KW (Z_to_bv 64 y)); [reflexivity|]. rewrite unsigned_lit_small by lia. lia.
Qed.
End tail.
