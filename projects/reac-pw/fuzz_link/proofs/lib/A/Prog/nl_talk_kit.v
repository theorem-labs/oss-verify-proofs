(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/AS/AsanPlanSound.v; 357 of its 407 lines of code are new or changed and 4673 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (fuzz_link.asan): THE IMAGE-FREE KIT of nl_talk's image-A walk (0x88974, contract
   lib/A/Prog/nl_talk_c.v). It holds no instruction, no symbolic-engine term and no walk: the model's case lemmas
   (link_spec's exchange talk_core, chunk_loop, msg_scan, attr_scan, kind_scan, one case at a time) and the byte
   algebra of the receive buffer, which the walk reads its bytes and its model with.

   It ports the plain build's lib/Prog/nt_lem.v and lib/Prog/nt_scan.v. Those are over
   the plain image's `rsegs` / `bytes_at` / `u8arr` and are not importable here. Their pure statements are kept
   unchanged in content, with the prefix `nt_`; their memory statements are restated over image A's segments `segs`
   and link_amem.v's views `abytes` / `val_mem` / `au16_at`.

   Section 1: the arithmetic of the walk's instructions: the ranges of rd32 / rd16, NLMSG_ALIGN and RTA_ALIGN as the
              code computes them (`and a0, a0, s4` with s4 = 0x1fffc at +0x410 and +0x464; `addi 3; srliw 2; slli 2`
              at +0x258..+0x260), and the sign extension of the 4-byte load of an NLMSG_ERROR code (+0x4d8
              `lw s11, 0(a0)`).
   Section 2: the model, one case at a time (plain nt_lem.v section 3, nt_scan.v sections 1 and 2).
   Section 3: g_nl's fields across a call: the chunk queue depends only on [0, NK_NEXT), the request ring only on
              [NK_SENT, NK_N_SENT + 4) (plain nt_lem.v section 2, without its memory parts).
   Section 4: the receive buffer. A chunk c at the front of the buffer's bytes (`abytes segs m buf (c ++ rest)`):
              its 4- and 2-byte loads as `val_mem` facts, an attribute's three facts copy_attr's Pre takes
              (lib/A/Prog/copy_attr_c.v copy_attr_apre), and the cut of a chunk out of the buffer's bytes.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI04 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The arithmetic of the walk's instructions
   ========================================================================== *)

Lemma nt_rd32_range : forall c off, 0 <= off -> off + 4 <= Z.of_nat (length c) -> 0 <= rd32 c off < 2 ^ 32.
Proof.
  intros c off H0 H1. unfold rd32, rdn.
  pose proof (bytes_le_to_Z_nonneg (slice c off 4)) as N.
  pose proof (bytes_le_to_Z_bound (slice c off 4)) as B.
  rewrite lw_slice_length in B by lia. change (8 * Z.of_nat (Z.to_nat 4)) with 32 in B. lia.
Qed.

Lemma nt_rd16_range : forall c off, 0 <= off -> off + 2 <= Z.of_nat (length c) -> 0 <= rd16 c off < 2 ^ 16.
Proof.
  intros c off H0 H1. unfold rd16, rdn.
  pose proof (bytes_le_to_Z_nonneg (slice c off 2)) as N.
  pose proof (bytes_le_to_Z_bound (slice c off 2)) as B.
  rewrite lw_slice_length in B by lia. change (8 * Z.of_nat (Z.to_nat 2)) with 16 in B. lia.
Qed.

Lemma nt_nl_align_ge : forall l, 0 <= l -> l <= nl_align l <= l + 3.
Proof. exact nl_align_le. Qed.

(* RTA_ALIGN of a 16-bit length, as `and a0, a0, s4` with s4 = 0x1fffc computes it (+0x410, +0x464) *)
Lemma nt_nl_align_land : forall l, 0 <= l <= 65535 -> Z.land (l + 3) 131068 = nl_align l.
Proof.
  intros l Hl. unfold nl_align.
  replace 131068 with (Z.land (Z.ones 17) (Z.lnot (Z.ones 2))) by reflexivity.
  rewrite Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by (change (2 ^ 17) with 131072; lia).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. ring.
Qed.

(* NLMSG_ALIGN as `addi 3; srliw 2; slli 2` computes it (+0x258..+0x260), over the values of the three results *)
Lemma nt_srliw_align : forall ml, 0 <= ml <= 4096 ->
  Z.shiftl (bv_swrap 32 (Z.shiftr (bv_wrap 32 (ml + 3)) 2) mod 18446744073709551616) 2 = nl_align ml.
Proof.
  intros ml H.
  assert (D : 0 <= (ml + 3) / 4 <= 1025) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (E1 : bv_wrap 32 (ml + 3) = ml + 3).
  { unfold bv_wrap. replace (bv_modulus 32) with (2 ^ 32) by reflexivity. apply Z.mod_small. lia. }
  rewrite E1, Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  assert (E2 : bv_swrap 32 ((ml + 3) / 4) = (ml + 3) / 4).
  { unfold bv_swrap, bv_wrap. replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
    replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
    rewrite Z.mod_small by lia. lia. }
  rewrite E2, Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  unfold nl_align. ring.
Qed.

(* the same three instructions as YK11's register values (v_addi, v_srliw, v_slli) *)
Lemma nt_srliw_align' : forall ml, 0 <= ml <= 4096 ->
  v_slli (v_srliw (v_addi (Z_to_bv 64 ml) 3) 2) 2 = Z_to_bv 64 (nl_align ml).
Proof.
  intros ml H. unfold v_slli, v_srliw, v_addi. f_equal. rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 ml) by (change (bv_modulus 64) with 18446744073709551616; lia).
  rewrite (bv_wrap_small 64 (ml + 3)) by (change (bv_modulus 64) with 18446744073709551616; lia).
  exact (nt_srliw_align ml H).
Qed.

(* bv_swrap 32 of a 32-bit value, on each side of 2 ^ 31 *)
Lemma nt_swrap32_lo : forall v, 0 <= v < 2 ^ 31 -> bv_swrap 32 v = v.
Proof.
  intros v Hv. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma nt_swrap32_hi : forall v, 2 ^ 31 <= v < 2 ^ 32 -> bv_swrap 32 v = v - 2 ^ 32.
Proof.
  intros v Hv. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  replace (v + 2 ^ 31) with ((v - 2 ^ 31) + 1 * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* the int32 reading of a 4-byte field is its 32-bit sign wrap *)
Lemma nt_rd32s_swrap : forall c off, 0 <= off -> off + 4 <= Z.of_nat (length c) ->
  bv_swrap 32 (rd32 c off) = rd32s c off.
Proof.
  intros c off H0 H1. pose proof (nt_rd32_range c off H0 H1) as R.
  unfold rd32s. cbv zeta.
  destruct (Z.ltb_spec (rd32 c off) (2 ^ 31)) as [L|L].
  - rewrite (nt_swrap32_lo (rd32 c off)) by lia. reflexivity.
  - rewrite (nt_swrap32_hi (rd32 c off)) by lia. reflexivity.
Qed.

Lemma nt_signed64 : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x H. unfold bv_signed. rewrite Z_to_bv_unsigned. rewrite bv_swrap_wrap'.
  apply bv_swrap_small. replace (bv_half_modulus 64) with (2 ^ 63) by reflexivity. lia.
Qed.

(* the sign extension of the 4-byte load of an NLMSG_ERROR code (+0x4d8 `lw s11, 0(a0)`), as the signed value of
   the register *)
Lemma nt_rd32s_of_rd32 : forall c off, 0 <= off -> off + 4 <= Z.of_nat (length c) ->
  bv_signed (Z_to_bv 64 (bv_swrap 32 (rd32 c off))) = rd32s c off.
Proof.
  intros c off H0 H1. pose proof (nt_rd32_range c off H0 H1) as R.
  rewrite <- (nt_rd32s_swrap c off H0 H1). apply nt_signed64.
  destruct (Z.lt_ge_cases (rd32 c off) (2 ^ 31)) as [L|L];
    [rewrite nt_swrap32_lo by lia | rewrite nt_swrap32_hi by lia]; lia.
Qed.

(* the same load as the register itself: YK11's step_lw writes `v_lw v` for the loaded word v, and a word whose low
   32 bits are the field's 4 bytes is all the lemma asks *)
Lemma nt_rd32s_of_rd32' : forall c off (w : word), 0 <= off -> off + 4 <= Z.of_nat (length c) ->
  bv_unsigned w mod 2 ^ 32 = rd32 c off -> v_lw w = w64 (rd32s c off).
Proof.
  intros c off w H0 H1 Hw. unfold v_lw, w64. f_equal.
  rewrite <- (nt_rd32s_swrap c off H0 H1), <- Hw.
  rewrite <- (bv_swrap_wrap' 32 (bv_unsigned w)). reflexivity.
Qed.

(* and as the symbolic engine's `SExt true 32` denotes it (sext 64 of the low 32 bits; YK11 b_lw_val) *)
Lemma nt_rd32s_of_rd32'' : forall c off (w : word), 0 <= off -> off + 4 <= Z.of_nat (length c) ->
  bv_unsigned w mod 2 ^ 32 = rd32 c off -> sext 64 (bv_extract 0 32 w) = w64 (rd32s c off).
Proof. intros c off w H0 H1 Hw. rewrite b_lw_val. exact (nt_rd32s_of_rd32' c off w H0 H1 Hw). Qed.

(* ==========================================================================
   2. The model, one case at a time
   ========================================================================== *)

Lemma nt_talk_sock : forall K, k_sock K <> 0 ->
  talk_rc_lib K = - k_sock K /\ talk_attrs K = no_attrs /\
  talk_after K = Kst (k_chunks K) (k_next K) (k_end K) 0 (k_send K) /\ talk_owes K = false.
Proof.
  intros K H. unfold talk_rc_lib, talk_attrs, talk_after, talk_core, talk_owes.
  replace (k_sock K =? 0) with false by (symmetry; apply Z.eqb_neq; exact H). cbn. repeat split.
Qed.

Lemma nt_talk_send : forall K, k_sock K = 0 -> k_send K <> 0 ->
  talk_rc_lib K = - k_send K /\ talk_attrs K = no_attrs /\
  talk_after K = Kst (k_chunks K) (k_next K) (k_end K) 0 0 /\ talk_owes K = false.
Proof.
  intros K H1 H2. unfold talk_rc_lib, talk_attrs, talk_after, talk_core, talk_owes.
  rewrite H1. replace (k_send K =? 0) with false by (symmetry; apply Z.eqb_neq; exact H2). cbn. repeat split.
Qed.

(* the answer of a chunk walk, as the exchange turns it into a code and attributes *)
Definition nt_nlv_rc (v : nlv) (e : Z) : Z :=
  match v with NlNone => - e | NlShort => - E_IO | NlErr code => code | NlLink _ => 0 end.
Definition nt_nlv_attrs (v : nlv) : attrs :=
  match v with NlLink a => a | _ => no_attrs end.

Lemma nt_talk_loop : forall K, k_sock K = 0 -> k_send K = 0 ->
  let r := chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K) in
  talk_rc_lib K = nt_nlv_rc (fst r) (k_end K) /\ talk_attrs K = nt_nlv_attrs (fst r) /\
  talk_after K = Kst (k_chunks K) (snd r) (k_end K) 0 0 /\ talk_owes K = true.
Proof.
  intros K H1 H2 r. unfold talk_rc_lib, talk_attrs, talk_after, talk_core, talk_owes.
  rewrite H1, H2. cbn [Z.eqb negb andb]. fold r. destruct r as [v j]. cbn [fst snd].
  destruct v; cbn; repeat split.
Qed.

Lemma nt_chunk_loop_step : forall f cs i c, nth_error cs i = Some c -> chunk_walk c = NlNone ->
  chunk_loop (S f) cs i = chunk_loop f cs (S i).
Proof. intros f cs i c E W. cbn [chunk_loop]. rewrite E, W. reflexivity. Qed.

Lemma nt_chunk_loop_hit : forall f cs i c, nth_error cs i = Some c -> chunk_walk c <> NlNone ->
  chunk_loop (S f) cs i = (chunk_walk c, S i).
Proof.
  intros f cs i c E W. cbn [chunk_loop]. rewrite E.
  destruct (chunk_walk c); [contradiction|reflexivity..].
Qed.

Lemma nt_chunk_loop_end : forall f cs i, nth_error cs i = None -> chunk_loop f cs i = (NlNone, i).
Proof. intros [|f] cs i E; cbn [chunk_loop]; [reflexivity|]. rewrite E. reflexivity. Qed.

(* ---- the message walk of one chunk (plain nt_scan.v section 1) ---- *)

Lemma nt_msg_none : forall (c : list byte) f off left, 16 <= left ->
  (rd32 c off <? 16) || (left <? rd32 c off) = true -> msg_scan (S f) c off left = NlNone.
Proof.
  intros c f off left H E. cbn [msg_scan]. unfold NL_HDR.
  replace (left <? 16) with false by (symmetry; apply Z.ltb_ge; lia). rewrite E. reflexivity.
Qed.

Lemma nt_msg_err : forall (c : list byte) f off left, 16 <= left -> 16 <= rd32 c off <= left ->
  rd16 c (off + 4) = 2 ->
  msg_scan (S f) c off left = if rd32 c off <? 36 then NlShort else NlErr (rd32s c (off + 16)).
Proof.
  intros c f off left H1 H2 H3. cbn [msg_scan]. unfold NL_HDR, NL_ERROR, NL_ERR_BODY.
  replace (left <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd32 c off <? 16) || (left <? rd32 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  rewrite H3. reflexivity.
Qed.

Lemma nt_msg_link : forall (c : list byte) f off left, 16 <= left -> 16 <= rd32 c off <= left ->
  rd16 c (off + 4) = 16 ->
  msg_scan (S f) c off left = NlLink (attr_scan f c (off + 32) (rd32 c off - 32) no_attrs).
Proof.
  intros c f off left H1 H2 H3. cbn [msg_scan]. unfold NL_HDR, NL_ERROR, RTM_NEWLINK, IFI_LEN.
  replace (left <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd32 c off <? 16) || (left <? rd32 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  rewrite H3. cbn. f_equal. f_equal; lia.
Qed.

Lemma nt_msg_skip : forall (c : list byte) f off left, 16 <= left -> 16 <= rd32 c off <= left ->
  rd16 c (off + 4) <> 2 -> rd16 c (off + 4) <> 16 ->
  msg_scan (S f) c off left =
    msg_scan f c (off + nl_align (rd32 c off)) (left - nl_align (rd32 c off)).
Proof.
  intros c f off left H1 H2 H3 H4. cbn [msg_scan]. unfold NL_HDR, NL_ERROR, RTM_NEWLINK.
  replace (left <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd32 c off <? 16) || (left <? rd32 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  replace (rd16 c (off + 4) =? 2) with false by (symmetry; apply Z.eqb_neq; exact H3).
  replace (rd16 c (off + 4) =? 16) with false by (symmetry; apply Z.eqb_neq; exact H4).
  reflexivity.
Qed.

(* what the message walk hands the failure exit: a short NLMSG_ERROR answers -EIO, a long one its code *)
Definition nt_is_err (v : nlv) (rc : Z) : Prop := (v = NlShort /\ rc = - E_IO) \/ v = NlErr rc.

(* ---- link_spec's two attribute walks, one step at a time (plain nt_scan.v section 2) ---- *)

Lemma nt_ks_small : forall {c : list byte} g off left k, left < 4 -> kind_scan g c off left k = k.
Proof.
  intros c [|g] off left k H; [reflexivity|]. cbn [kind_scan]. unfold RTA_HDR.
  replace (left <? 4) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma nt_ks_stop : forall {c : list byte} g off left k, 4 <= left ->
  (rd16 c off <? 4) || (left <? rd16 c off) = true -> kind_scan (S g) c off left k = k.
Proof.
  intros c g off left k H E. cbn [kind_scan]. unfold RTA_HDR.
  replace (left <? 4) with false by (symmetry; apply Z.ltb_ge; lia). rewrite E. reflexivity.
Qed.

Lemma nt_ks_step : forall {c : list byte} g off left k, 4 <= left -> 4 <= rd16 c off <= left ->
  kind_scan (S g) c off left k =
    kind_scan g c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (if rd16 c (off + 2) =? 1 then Some (slice c (off + 4) (rd16 c off - 4)) else k).
Proof.
  intros c g off left k H1 H2. cbn [kind_scan]. unfold RTA_HDR, INFO_KIND.
  replace (left <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd16 c off <? 4) || (left <? rd16 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma nt_as_small : forall {c : list byte} f off left a, left < 4 -> attr_scan f c off left a = a.
Proof.
  intros c [|f] off left a H; [reflexivity|]. cbn [attr_scan]. unfold RTA_HDR.
  replace (left <? 4) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma nt_as_stop : forall {c : list byte} f off left a, 4 <= left ->
  (rd16 c off <? 4) || (left <? rd16 c off) = true -> attr_scan (S f) c off left a = a.
Proof.
  intros c f off left a H E. cbn [attr_scan]. unfold RTA_HDR.
  replace (left <? 4) with false by (symmetry; apply Z.ltb_ge; lia). rewrite E. reflexivity.
Qed.

Lemma nt_as_step : forall {c : list byte} f off left a, 4 <= left -> 4 <= rd16 c off <= left ->
  attr_scan (S f) c off left a =
    attr_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (if rd16 c (off + 2) =? 20 then Attrs (a_kind a) (Some (slice c (off + 4) (rd16 c off - 4)))
       else if rd16 c (off + 2) =? 18
            then Attrs (kind_scan f c (off + 4) (rd16 c off - 4) (a_kind a)) (a_alias a)
            else a).
Proof.
  intros c f off left a H1 H2. cbn [attr_scan]. unfold RTA_HDR, IFLA_IFALIAS, IFLA_LINKINFO.
  replace (left <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd16 c off <? 4) || (left <? rd16 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* ==========================================================================
   3. g_nl's fields across a call: the byte ranges each field view depends on
   ========================================================================== *)

Lemma nt_slice_slice : forall (bs : list byte) a k o n, 0 <= a -> 0 <= k -> 0 <= o -> 0 <= n ->
  a <= o -> o + n <= a + k -> slice bs o n = slice (slice bs a k) (o - a) n.
Proof.
  intros bs a k o n Ha Hk Ho Hn H1 H2. unfold slice.
  rewrite skipn_firstn_comm, skipn_skipn, firstn_firstn.
  replace (Z.to_nat (o - a) + Z.to_nat a)%nat with (Z.to_nat o) by lia.
  replace (Nat.min (Z.to_nat n) (Z.to_nat k - Z.to_nat (o - a))) with (Z.to_nat n) by lia.
  reflexivity.
Qed.

(* two byte lists that agree on [a, a + k) agree on every slice inside it *)
Lemma nt_slice_sub_eq : forall (bs bs' : list byte) a k o n, 0 <= a -> 0 <= k -> 0 <= o -> 0 <= n ->
  a <= o -> o + n <= a + k -> slice bs' a k = slice bs a k -> slice bs' o n = slice bs o n.
Proof.
  intros bs bs' a k o n Ha Hk Ho Hn H1 H2 E.
  rewrite (nt_slice_slice bs' a k o n), (nt_slice_slice bs a k o n) by lia. rewrite E. reflexivity.
Qed.

Lemma nt_rdn_sub_eq : forall (bs bs' : list byte) a k o n, 0 <= a -> 0 <= k -> 0 <= o -> 0 <= n ->
  a <= o -> o + n <= a + k -> slice bs' a k = slice bs a k -> rdn bs' o n = rdn bs o n.
Proof.
  intros bs bs' a k o n Ha Hk Ho Hn H1 H2 E. unfold rdn.
  rewrite (nt_slice_sub_eq bs bs' a k o n Ha Hk Ho Hn H1 H2 E). reflexivity.
Qed.

(* the chunk queue depends only on [0, NK_NEXT) *)
Lemma nt_nk_chunks_keep : forall bs bs', nlk_wf bs ->
  slice bs' 0 NK_NEXT = slice bs 0 NK_NEXT -> nk_chunks bs' = nk_chunks bs.
Proof.
  intros bs bs' WF E. destruct WF as (Hn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  unfold NL_CHUNKS, NL_CHUNK_MAX in *.
  assert (EN : nk_n_chunks bs' = nk_n_chunks bs).
  { unfold nk_n_chunks, fld_u32.
    apply (nt_rdn_sub_eq bs bs' 0 NK_NEXT); unfold NK_N_CHUNKS, NK_NEXT; lia || exact E. }
  unfold nk_chunks. rewrite EN. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  assert (Hi' : 0 <= Z.of_nat i < nk_n_chunks bs) by lia.
  assert (EL : fld_u64 bs' (NK_CHUNK_LEN + 8 * Z.of_nat i) = fld_u64 bs (NK_CHUNK_LEN + 8 * Z.of_nat i)).
  { unfold fld_u64.
    apply (nt_rdn_sub_eq bs bs' 0 NK_NEXT); unfold NK_CHUNK_LEN, NK_NEXT; lia || exact E. }
  specialize (HL (Z.of_nat i) Hi').
  unfold nk_chunk. rewrite EL.
  apply (nt_slice_sub_eq bs bs' 0 NK_NEXT); unfold NK_CHUNK, NK_NEXT, NL_CHUNK_MAX in *; lia || exact E.
Qed.

(* the request ring depends only on [NK_SENT, NK_N_SENT + 4) *)
Lemma nt_nk_sent_keep : forall bs bs', nlk_wf bs ->
  slice bs' NK_SENT (NK_N_SENT + 4 - NK_SENT) = slice bs NK_SENT (NK_N_SENT + 4 - NK_SENT) ->
  nk_sent bs' = nk_sent bs.
Proof.
  intros bs bs' WF E. destruct WF as (_ & _ & Hn & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL).
  unfold NL_SENT_MAX, NL_SENT_LEN in *.
  assert (EN : nk_n_sent bs' = nk_n_sent bs).
  { unfold nk_n_sent, fld_u32.
    apply (nt_rdn_sub_eq bs bs' NK_SENT (NK_N_SENT + 4 - NK_SENT)); unfold NK_SENT, NK_N_SENT; lia || exact E. }
  unfold nk_sent. rewrite EN. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  assert (Hi' : 0 <= Z.of_nat i < nk_n_sent bs) by lia.
  assert (EL : fld_u64 bs' (NK_SENT_LEN + 8 * Z.of_nat i) = fld_u64 bs (NK_SENT_LEN + 8 * Z.of_nat i)).
  { unfold fld_u64.
    apply (nt_rdn_sub_eq bs bs' NK_SENT (NK_N_SENT + 4 - NK_SENT));
      unfold NK_SENT_LEN, NK_SENT, NK_N_SENT; lia || exact E. }
  specialize (HL (Z.of_nat i) Hi').
  unfold nk_sent_one. rewrite EL.
  apply (nt_slice_sub_eq bs bs' NK_SENT (NK_N_SENT + 4 - NK_SENT));
    unfold NK_SENT, NK_N_SENT, NL_SENT_LEN in *; lia || exact E.
Qed.

Lemma nt_nk_sent_len : forall bs, nlk_wf bs -> nk_n_sent bs = Z.of_nat (length (nk_sent bs)).
Proof.
  intros bs WF. destruct WF as (_ & _ & Hn & _). unfold nk_sent. rewrite length_map, length_seq. lia.
Qed.

Lemma nt_nk_chunks_length : forall bs, nlk_wf bs -> Z.of_nat (length (nk_chunks bs)) = nk_n_chunks bs.
Proof.
  intros bs WF. destruct WF as (Hn & _). unfold nk_chunks. rewrite length_map, length_seq. lia.
Qed.

Lemma nt_nk_chunks_nth : forall bs i, 0 <= i < nk_n_chunks bs ->
  nth_error (nk_chunks bs) (Z.to_nat i) = Some (nk_chunk bs i).
Proof.
  intros bs i Hi. unfold nk_chunks. rewrite nth_error_map, nth_error_seq.
  replace (Z.to_nat i <? Z.to_nat (nk_n_chunks bs))%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma nt_nk_chunks_none : forall bs i, 0 <= nk_n_chunks bs -> nk_n_chunks bs <= i ->
  nth_error (nk_chunks bs) (Z.to_nat i) = None.
Proof.
  intros bs i H0 Hi. apply nth_error_None. unfold nk_chunks. rewrite length_map, length_seq. lia.
Qed.

Lemma nt_nk_chunk_len : forall bs i, nlk_wf bs -> 0 <= i < nk_n_chunks bs ->
  (length (nk_chunk bs i) <= 4096)%nat.
Proof.
  intros bs i WF Hi. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  specialize (HL i Hi). unfold NL_CHUNK_MAX in HL. unfold nk_chunk, slice. rewrite length_firstn. lia.
Qed.

(* ==========================================================================
   4. The receive buffer
   ========================================================================== *)

(* ---- the byte algebra under it (no image) ---- *)

Lemma nt_bytes_cons : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

(* the k-th byte of a list is the k-th little-endian byte of its value: the bridge from `abytes` (bytes by index)
   to `val_mem` (bytes of a value); lw_bytes_of_vals (LinkWalk.v) is the converse *)
Lemma nt_le_byte_nth : forall (l : list byte) k, (k < length l)%nat ->
  nth_error l k = Some (Z_to_bv 8 (le_byte (bytes_le_to_Z l) (length l) k)).
Proof.
  induction l as [|b l IH]; intros k Hk; [cbn in Hk; lia|].
  pose proof (bytes_le_to_Z_nonneg l) as N. pose proof (bytes_le_to_Z_bound l) as Bd.
  pose proof (u8_range b) as Rb.
  assert (Hv : 0 <= bytes_le_to_Z (b :: l) < 2 ^ (8 * Z.of_nat (length (b :: l))))
    by (split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]).
  destruct k as [|k].
  - cbn [nth_error]. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
    unfold le_byte. rewrite Z.mul_0_r, Z.shiftr_0_r.
    rewrite (Z.mod_small (bytes_le_to_Z (b :: l))) by exact Hv.
    rewrite nt_bytes_cons. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_mod by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
  - cbn [nth_error]. cbn [length] in Hk. rewrite (IH k ltac:(lia)). f_equal. f_equal.
    assert (Hk2 : 0 < 2 ^ (8 * Z.of_nat k)) by (apply Z.pow_pos_nonneg; lia).
    unfold le_byte.
    rewrite (Z.mod_small (bytes_le_to_Z l)) by lia.
    rewrite (Z.mod_small (bytes_le_to_Z (b :: l))) by exact Hv.
    rewrite !Z.shiftr_div_pow2 by lia.
    replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite <- Z.div_div by lia.
    rewrite nt_bytes_cons. rewrite Z.div_add by lia.
    rewrite (Z.div_small (bv_unsigned b) 256) by lia. rewrite Z.add_0_l. reflexivity.
Qed.

Section b.
Variable segs : list Segment.

(* the n bytes of a chunk at off, at buf + off *)
Lemma nt_abytes_slice : forall m buf c rest off n, abytes segs m buf (c ++ rest) ->
  0 <= off -> 0 <= n -> off + n <= Z.of_nat (length c) -> abytes segs m (buf + off) (slice c off n).
Proof.
  intros m buf c rest off n Hb H0 H1 H2. unfold abytes in Hb |- *. destruct Hb as (Hb0 & Hbl & Hnth).
  rewrite length_app in Hbl. rewrite lw_slice_length by lia.
  split; [lia|]. split; [lia|].
  intros i Hi. rewrite lw_slice_nth by lia.
  specialize (Hnth (Z.to_nat off + i)%nat ltac:(rewrite length_app; lia)).
  rewrite nth_error_app1 in Hnth by lia.
  replace (buf + off + Z.of_nat i) with (buf + Z.of_nat (Z.to_nat off + i)) by lia. exact Hnth.
Qed.

(* a load of n bytes inside the chunk reads rdn *)
Lemma nt_read_n : forall m buf c rest off (n : nat), abytes segs m buf (c ++ rest) -> 0 <= off ->
  off + Z.of_nat n <= Z.of_nat (length c) -> val_mem segs m (buf + off) n (rdn c off (Z.of_nat n)).
Proof.
  intros m buf c rest off n Hb H0 H1 k Hk.
  unfold abytes in Hb. destruct Hb as (_ & _ & Hnth).
  assert (Hl : length (slice c off (Z.of_nat n)) = n) by (rewrite lw_slice_length by lia; lia).
  pose proof (nt_le_byte_nth (slice c off (Z.of_nat n)) k ltac:(lia)) as E.
  rewrite Hl in E. rewrite lw_slice_nth in E by lia.
  specialize (Hnth (Z.to_nat off + k)%nat ltac:(rewrite length_app; lia)).
  rewrite nth_error_app1 in Hnth by lia.
  replace (buf + off + Z.of_nat k) with (buf + Z.of_nat (Z.to_nat off + k)) by lia.
  rewrite Hnth, E. reflexivity.
Qed.

Lemma nt_read4 : forall m buf c rest off, abytes segs m buf (c ++ rest) -> 0 <= off ->
  off + 4 <= Z.of_nat (length c) -> val_mem segs m (buf + off) 4 (rd32 c off).
Proof. intros m buf c rest off Hb H0 H1. exact (nt_read_n m buf c rest off 4 Hb H0 H1). Qed.

Lemma nt_read2 : forall m buf c rest off, abytes segs m buf (c ++ rest) -> 0 <= off ->
  off + 2 <= Z.of_nat (length c) -> val_mem segs m (buf + off) 2 (rd16 c off).
Proof. intros m buf c rest off Hb H0 H1. exact (nt_read_n m buf c rest off 2 Hb H0 H1). Qed.

(* the three facts copy_attr's Pre takes about the attribute at a0 = buf + off (copy_attr_apre: `au16_at m a l`,
   `abytes m (a + RTA_HDR) pay`, `length pay = l - RTA_HDR`), for the two call sites +0x38c and +0x3f4 *)
Lemma nt_attr_pre_bytes : forall m buf c rest off, abytes segs m buf (c ++ rest) -> 0 <= off ->
  RTA_HDR <= rd16 c off -> off + rd16 c off <= Z.of_nat (length c) ->
  au16_at segs m (buf + off) (rd16 c off) /\
  abytes segs m (buf + off + RTA_HDR) (slice c (off + RTA_HDR) (rd16 c off - RTA_HDR)) /\
  Z.of_nat (length (slice c (off + RTA_HDR) (rd16 c off - RTA_HDR))) = rd16 c off - RTA_HDR.
Proof.
  intros m buf c rest off Hb H0 H1 H2. unfold RTA_HDR in *.
  split; [exact (nt_read2 m buf c rest off Hb H0 ltac:(lia))|].
  split.
  - replace (buf + off + 4) with (buf + (off + 4)) by lia.
    apply (nt_abytes_slice m buf c rest); [exact Hb | lia | lia | lia].
  - rewrite lw_slice_length by lia. lia.
Qed.

(* the chunk recv answered, cut out of the buffer's bytes *)
Lemma nt_buf_split : forall m buf bs n, abytes segs m buf bs -> 0 <= n -> n <= Z.of_nat (length bs) ->
  exists c rest, bs = c ++ rest /\ Z.of_nat (length c) = n.
Proof.
  intros m buf bs n _ H0 H1. exists (firstn (Z.to_nat n) bs), (skipn (Z.to_nat n) bs).
  split; [symmetry; apply firstn_skipn|]. rewrite length_firstn. lia.
Qed.
End b.

About nt_talk_loop. Print Assumptions nt_talk_loop.
About nt_read4. Print Assumptions nt_read4.
About nt_attr_pre_bytes. Print Assumptions nt_attr_pre_bytes.
About nt_as_step. Print Assumptions nt_as_step.
