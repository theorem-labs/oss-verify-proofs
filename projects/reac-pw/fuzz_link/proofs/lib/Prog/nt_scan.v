(* reac-pw/fuzz_link, PLAIN build: the three inner loops of nl_talk (reac_link_alias.c:61-88) on the
   plain image, each against link_spec's ONE netlink walk (msg_scan, attr_scan, kind_scan).

   - msg_loop: 0x160e0..0x1610c, the walk over the messages of one chunk (no call, no store).
   - info_loop: 0x161dc..0x16214, the walk over the attributes inside one IFLA_LINKINFO; it calls
     copy_attr on the kind buffer for each IFLA_INFO_KIND.
   - attr_loop: 0x16194..0x1622c, the walk over the attributes of the first RTM_NEWLINK; it calls
     copy_attr on the alias buffer for each IFLA_IFALIAS and runs info_loop for each IFLA_LINKINFO.
   Each loop is stated at its head with the machine state and the walk it computes, and hands its
   exits to continuations, so nl_talk.v composes them with the receive loop and the exit. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_str mk_marks mk_leaf mk_call
  nt_lem copy_attr_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
Local Open Scope Z_scope.

(* ==========================================================================
   0. Register values the walk meets
   ========================================================================== *)

Lemma zx32_wz : forall x, 0 <= x < 2 ^ 32 -> zx32 (wz x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma zx16_wz : forall x, 0 <= x < 2 ^ 16 -> zx16 (wz x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx16, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma sgn_lit : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x H. unfold bv_signed. rewrite Z_to_bv_unsigned. rewrite bv_swrap_wrap.
  apply bv_swrap_small. replace (bv_half_modulus 64) with (2 ^ 63) by reflexivity. lia.
Qed.

(* NLMSG_ALIGN as `addi 3; srliw 2; slli 2` computes it *)
Lemma srliw_align : forall ml, 0 <= ml <= 4096 ->
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
  unfold nl_align. lia.
Qed.

(* ==========================================================================
   1. The message walk of one chunk
   ========================================================================== *)

Section Msg.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf : Z) (c rest : list byte)
          (Q : machine_state -> Prop).
Hypothesis BUF : bytes_at rsegs m buf (c ++ rest).
Hypothesis LC : (length c <= 4096)%nat.
Hypothesis LR : buf + 16384 <= 2 ^ 63.
Hypothesis B0 : 0 < buf.

Local Notation ST pc a0 a1 a2 a3 s5 s6 s7 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma msg_none : forall f off left, 16 <= left ->
  (rd32 c off <? 16) || (left <? rd32 c off) = true -> msg_scan (S f) c off left = NlNone.
Proof.
  intros f off left H E. cbn [msg_scan]. unfold NL_HDR.
  replace (left <? 16) with false by (symmetry; apply Z.ltb_ge; lia). rewrite E. reflexivity.
Qed.

Lemma msg_err : forall f off left, 16 <= left -> 16 <= rd32 c off <= left -> rd16 c (off + 4) = 2 ->
  msg_scan (S f) c off left = if rd32 c off <? 36 then NlShort else NlErr (rd32s c (off + 16)).
Proof.
  intros f off left H1 H2 H3. cbn [msg_scan]. unfold NL_HDR, NL_ERROR, NL_ERR_BODY.
  replace (left <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd32 c off <? 16) || (left <? rd32 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  rewrite H3. reflexivity.
Qed.

Lemma msg_link : forall f off left, 16 <= left -> 16 <= rd32 c off <= left -> rd16 c (off + 4) = 16 ->
  msg_scan (S f) c off left = NlLink (attr_scan f c (off + 32) (rd32 c off - 32) no_attrs).
Proof.
  intros f off left H1 H2 H3. cbn [msg_scan]. unfold NL_HDR, NL_ERROR, RTM_NEWLINK, IFI_LEN.
  replace (left <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd32 c off <? 16) || (left <? rd32 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  rewrite H3. cbn. f_equal. f_equal; lia.
Qed.

Lemma msg_skip : forall f off left, 16 <= left -> 16 <= rd32 c off <= left -> rd16 c (off + 4) <> 2 ->
  rd16 c (off + 4) <> 16 ->
  msg_scan (S f) c off left =
    msg_scan f c (off + nl_align (rd32 c off)) (left - nl_align (rd32 c off)).
Proof.
  intros f off left H1 H2 H3 H4. cbn [msg_scan]. unfold NL_HDR, NL_ERROR, RTM_NEWLINK.
  replace (left <? 16) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd32 c off <? 16) || (left <? rd32 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  replace (rd16 c (off + 4) =? 2) with false by (symmetry; apply Z.eqb_neq; exact H3).
  replace (rd16 c (off + 4) =? 16) with false by (symmetry; apply Z.eqb_neq; exact H4).
  reflexivity.
Qed.

Definition is_err (v : nlv) (rc : Z) : Prop := (v = NlShort /\ rc = - E_IO) \/ v = NlErr rc.

Lemma msg_loop : forall n off left a2 a3,
  (Z.to_nat left < n)%nat -> 16 <= left -> 0 <= off -> off + left = Z.of_nat (length c) ->
  (msg_scan n c off left = NlNone -> forall a0' a1' a2' a3',
     evt rsegs Q (ST 0x16110 a0' a1' a2' a3' (Z_to_bv 64 16) (Z_to_bv 64 2) (Z_to_bv 64 15))) ->
  (forall rc, is_err (msg_scan n c off left) rc -> forall a0' a1' a2' a3',
     evt rsegs Q (ST 0x1623c a0' a1' a2' a3' (Z_to_bv 64 16) (Z_to_bv 64 rc) (Z_to_bv 64 15))) ->
  (forall f off' ml, msg_scan n c off left = NlLink (attr_scan f c (off' + 32) (ml - 32) no_attrs) ->
     (Z.to_nat (ml - 32) < f)%nat -> 0 <= off' -> 16 <= ml -> off' + ml <= Z.of_nat (length c) ->
     forall a0' a3',
     evt rsegs Q (ST 0x16170 a0' (Z_to_bv 64 (buf + off')) (Z_to_bv 64 ml) a3'
                     (Z_to_bv 64 16) (Z_to_bv 64 2) (Z_to_bv 64 15))) ->
  evt rsegs Q (ST 0x160e0 (Z_to_bv 64 left) (Z_to_bv 64 (buf + off)) a2 a3
                  (Z_to_bv 64 16) (Z_to_bv 64 2) (Z_to_bv 64 15)).
Proof.
  induction n as [|f IH]; intros off left a2 a3 HN H16 H0 HL KN KE KL; [lia|].
  pose proof (read4_chunk m buf c rest off BUF H0 ltac:(lia)) as RD4.
  pose proof (read2_chunk m buf c rest (off + 4) BUF ltac:(lia) ltac:(lia)) as RD2.
  pose proof (rd32_range c off ltac:(lia) ltac:(lia)) as R32.
  pose proof (rd16_range c (off + 4) ltac:(lia) ltac:(lia)) as R16.
  zstep. rewrite zx32_wz by lia.
  zstep. if_cases K1; zify_cond K1.
  { apply KN. apply msg_none; [lia|]. apply orb_true_iff. left. apply Z.ltb_lt. lia. }
  zstep. if_cases K2; zify_cond K2.
  { apply KN. apply msg_none; [lia|]. apply orb_true_iff. right. apply Z.ltb_lt. lia. }
  zstep. rewrite zx16_wz by lia.
  zstep. if_cases K3; zify_cond K3.
  { apply (KL f off (rd32 c off)); [apply msg_link; lia | lia | lia | lia | lia]. }
  zstep. if_cases K4; zify_cond K4.
  { rewrite (msg_err f off left) in KE by lia.
    pose proof (read4_chunk m buf c rest (off + 16)) as RD5.
    zstep. zstep. if_cases K6; zify_cond K6.
    - specialize (RD5 BUF ltac:(lia) ltac:(lia)).
      zstep. rewrite sx32_rd32 by lia.
      apply KE. right. replace (rd32 c off <? 36) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - zstep. zstep.
      apply KE. left. replace (rd32 c off <? 36) with true by (symmetry; apply Z.ltb_lt; lia).
      split; reflexivity. }
  rewrite (msg_skip f off left) in KN, KE, KL by lia.
  zstep. zstep. zstep. zstep. zstep.
  rewrite srliw_align by lia.
  pose proof (nl_align_ge (rd32 c off) ltac:(lia)) as AL.
  zstep. if_cases K5; zify_cond K5.
  { replace (buf + off + nl_align (rd32 c off)) with (buf + (off + nl_align (rd32 c off))) by lia.
    rewrite (Z.mod_small (nl_align (rd32 c off))) by lia.
    try rewrite sgn_lit in K5 by lia.
    apply (IH (off + nl_align (rd32 c off)) (left - nl_align (rd32 c off))); try lia; assumption. }
  apply KN. destruct f as [|f]; [reflexivity|]. cbn [msg_scan]. unfold NL_HDR.
  try rewrite sgn_lit in K5 by lia.
  replace (left - nl_align (rd32 c off) <? 16) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

End Msg.

(* ==========================================================================
   2. The attribute walks: the context they run in
   ========================================================================== *)

(* a buffer that holds the text of the last attribute written into it, or is untouched since the
   entry memory m0 *)
Definition bufst (m0 m : word -> option byte) (b n : Z) (o : option (list byte)) : Prop :=
  (b <> 0 -> 1 <= n -> exists junk, rw_cells rsegs m b [CB (Z.to_nat n) junk]) /\
  match o with
  | Some pay => b <> 0 -> 1 <= n -> cstr_at m b (cut_text pay n)
  | None => b <> 0 -> forall s, Z.of_nat (length s) < n -> cstr_at m0 b s -> cstr_at m b s
  end.

Lemma disjoint_from_sub : forall W a n n', disjoint_from W a n -> 0 <= n' <= n -> disjoint_from W a n'.
Proof.
  induction W as [|[l h] W IH]; intros a n n' D H; [exact I|].
  cbn in D |- *. destruct D as [D1 D2]. split; [lia | exact (IH a n n' D2 H)].
Qed.

Lemma cstr_keep : forall W m m' b s n, cstr_at m b s -> munch W m m' -> disjoint_from W b n ->
  Z.of_nat (length s) < n -> cstr_at m' b s.
Proof.
  intros W m m' b s n [B N] MU D L. split; [|exact N].
  apply (bytes_at_transport rsegs W m m'); [exact B | exact MU |].
  apply (disjoint_from_sub W b n); [exact D|]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma bufst_keep : forall m0 m m' b n o W, bufst m0 m b n o -> munch W m m' -> wmono rsegs m m' ->
  (b <> 0 -> 1 <= n -> disjoint_from W b n) -> bufst m0 m' b n o.
Proof.
  intros m0 m m' b n o W [R S] MU WM D. split.
  - intros Hb Hn. destruct (R Hb Hn) as [junk RC]. exists junk.
    apply (rw_cells_transport rsegs W m m'); [exact RC | exact MU | exact WM |].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (D Hb Hn).
  - destruct o as [pay|].
    + intros Hb Hn. apply (cstr_keep W m m' b _ n (S Hb Hn) MU (D Hb Hn)).
      pose proof (cut_text_len pay n Hn). lia.
    + intros Hb s Hs H0. assert (Hn : 1 <= n) by lia.
      apply (cstr_keep W m m' b s n (S Hb s Hs H0) MU (D Hb Hn) Hs).
Qed.

Lemma disj_shift : forall W a n k n', disjoint_from W a n -> 0 <= k -> 0 <= n' -> k + n' <= n ->
  disjoint_from W (a + k) n'.
Proof.
  induction W as [|[l h] W IH]; intros a n k n' D H1 H2 H3; [exact I|].
  cbn in D |- *. destruct D as [D1 D2]. split; [lia | exact (IH a n k n' D2 H1 H2 H3)].
Qed.

(* ---- link_spec's two attribute walks, one step at a time ---- *)

Lemma ks_small : forall {c : list byte} g off left k, left < 4 -> kind_scan g c off left k = k.
Proof. intros c [|g] off left k H; [reflexivity|]. cbn [kind_scan]. unfold RTA_HDR.
  replace (left <? 4) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma ks_stop : forall {c : list byte} g off left k, 4 <= left ->
  (rd16 c off <? 4) || (left <? rd16 c off) = true -> kind_scan (S g) c off left k = k.
Proof. intros c g off left k H E. cbn [kind_scan]. unfold RTA_HDR.
  replace (left <? 4) with false by (symmetry; apply Z.ltb_ge; lia). rewrite E. reflexivity. Qed.

Lemma ks_step : forall {c : list byte} g off left k, 4 <= left -> 4 <= rd16 c off <= left ->
  kind_scan (S g) c off left k =
    kind_scan g c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (if rd16 c (off + 2) =? 1 then Some (slice c (off + 4) (rd16 c off - 4)) else k).
Proof. intros c g off left k H1 H2. cbn [kind_scan]. unfold RTA_HDR, INFO_KIND.
  replace (left <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd16 c off <? 4) || (left <? rd16 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma as_small : forall {c : list byte} f off left a, left < 4 -> attr_scan f c off left a = a.
Proof. intros c [|f] off left a H; [reflexivity|]. cbn [attr_scan]. unfold RTA_HDR.
  replace (left <? 4) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. Qed.

Lemma as_stop : forall {c : list byte} f off left a, 4 <= left ->
  (rd16 c off <? 4) || (left <? rd16 c off) = true -> attr_scan (S f) c off left a = a.
Proof. intros c f off left a H E. cbn [attr_scan]. unfold RTA_HDR.
  replace (left <? 4) with false by (symmetry; apply Z.ltb_ge; lia). rewrite E. reflexivity. Qed.

Lemma as_step : forall {c : list byte} f off left a, 4 <= left -> 4 <= rd16 c off <= left ->
  attr_scan (S f) c off left a =
    attr_scan f c (off + nl_align (rd16 c off)) (left - nl_align (rd16 c off))
      (if rd16 c (off + 2) =? 20 then Attrs (a_kind a) (Some (slice c (off + 4) (rd16 c off - 4)))
       else if rd16 c (off + 2) =? 18
            then Attrs (kind_scan f c (off + 4) (rd16 c off - 4) (a_kind a)) (a_alias a)
            else a).
Proof. intros c f off left a H1 H2. cbn [attr_scan]. unfold RTA_HDR, IFLA_IFALIAS, IFLA_LINKINFO.
  replace (left <? 4) with false by (symmetry; apply Z.ltb_ge; lia).
  replace ((rd16 c off <? 4) || (left <? rd16 c off)) with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia). reflexivity. Qed.

Section Scan.
(* The entry memory and the footprint nl_talk's contract allows; the frame base fb = sp4; the
   receive buffer at fb + 24 holding the chunk c; the two buffers and their caps (as words, the
   values the walk passes to copy_attr); g_nl's bytes, which no attribute walk changes; errno. *)
Variables (m0 : word -> option byte) (W0 : list ivl) (lo : Z) (sp4 : word)
          (kindw kcw aliasw acw : word) (j0 : list byte) (SV : list cell)
          (c rest : list byte) (kbs : list byte) (errno : Z)
          (Q : machine_state -> Prop).
Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).

Hypothesis QX : q_ext Q.
Hypothesis LO : 0 <= lo /\ lo + 80 <= bv_unsigned sp4.
Hypothesis SPB : bv_unsigned sp4 + 16512 < 2 ^ 63.
Hypothesis LCR : Z.of_nat (length (c ++ rest)) = 16384.
Hypothesis LC : (length c <= 4096)%nat.
(* the buffers lie apart from the frame window [fb - 80, fb + 16512), from g_nl and from each other *)
Hypothesis KSEP : bv_unsigned kindw <> 0 -> 1 <= bv_unsigned kcw ->
  apart (bv_unsigned kindw) (bv_unsigned kcw) (bv_unsigned sp4 - 80) 16592 /\
  apart_gnl (bv_unsigned kindw) (bv_unsigned kcw).
Hypothesis ASEP : bv_unsigned aliasw <> 0 -> 1 <= bv_unsigned acw ->
  apart (bv_unsigned aliasw) (bv_unsigned acw) (bv_unsigned sp4 - 80) 16592 /\
  apart_gnl (bv_unsigned aliasw) (bv_unsigned acw).
Hypothesis KASEP : bv_unsigned kindw <> 0 -> 1 <= bv_unsigned kcw ->
  bv_unsigned aliasw <> 0 -> 1 <= bv_unsigned acw ->
  apart (bv_unsigned kindw) (bv_unsigned kcw) (bv_unsigned aliasw) (bv_unsigned acw).
Hypothesis GSEP : apart_gnl (bv_unsigned sp4 - 80) 16592.
(* the footprint covers every write a copy_attr call makes *)
Hypothesis WFR : forall x, outside W0 x -> outside [(bv_unsigned sp4 - 80, bv_unsigned sp4)] x.
Hypothesis WK : forall x, outside W0 x -> bv_unsigned kindw <> 0 -> outside [(bv_unsigned kindw, bv_unsigned kindw + bv_unsigned kcw)] x.
Hypothesis WA : forall x, outside W0 x -> bv_unsigned aliasw <> 0 -> outside [(bv_unsigned aliasw, bv_unsigned aliasw + bv_unsigned acw)] x.


Definition ainv (m : word -> option byte) (ok oa : option (list byte)) : Prop :=
  mem_inv rsegs m /\ wmono rsegs m0 m /\ munch W0 m0 m /\ stk rsegs m lo (bv_unsigned sp4) /\
  rw_cells rsegs m (bv_unsigned sp4) [CB 16 j0; C8 acw] /\
  bytes_at rsegs m (bv_unsigned sp4 + 24) (c ++ rest) /\ wr_at rsegs m (bv_unsigned sp4 + 24) 16384 /\
  rw_cells rsegs m (bv_unsigned sp4 + 16408) SV /\ cells_size SV = 104%nat /\
  nlk_at m kbs /\ wr_at rsegs m errno 4 /\
  bufst m0 m (bv_unsigned kindw) (bv_unsigned kcw) ok /\ bufst m0 m (bv_unsigned aliasw) (bv_unsigned acw) oa.


(* what a copy_attr call on the kind buffer leaves *)
Lemma ainv_kind : forall m m' ok oa pay,
  ainv m ok oa ->
  munch [(bv_unsigned sp4 - 80, bv_unsigned sp4); (bv_unsigned kindw, bv_unsigned kindw + bv_unsigned kcw)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp4) ->
  (bv_unsigned kindw = 0 -> m' = m) ->
  (bv_unsigned kcw = 0 -> munch [(bv_unsigned sp4 - 80, bv_unsigned sp4)] m m') ->
  (bv_unsigned kindw <> 0 -> 1 <= bv_unsigned kcw -> cstr_at m' (bv_unsigned kindw) (cut_text pay (bv_unsigned kcw))) ->
  (bv_unsigned kindw <> 0 -> 1 <= bv_unsigned kcw ->
     exists junk, rw_cells rsegs m' (bv_unsigned kindw) [CB (Z.to_nat (bv_unsigned kcw)) junk]) ->
  ainv m' (Some pay) oa.
Proof.
  intros m m' ok oa pay (MI & WM0 & MU0 & ST & FA & BB & BW & FS & SVS & NK & EW & BK & BA)
    MU WM MI' ST' K0 N0 CS RC.
  destruct (Z.eq_dec (bv_unsigned kindw) 0) as [Hk|Hk].
  { specialize (K0 Hk). subst m'.
    repeat (split; [assumption|]). split; [split; intros; contradiction|]. exact BA. }
  pose proof (bv_unsigned_in_range 64 sp4) as RS. unfold bv_modulus in RS.
  destruct LO as [LO0 LO1].
  (* the footprint actually written: the copy_attr frame, and the kind buffer when kc >= 1 *)
  assert (MUW : exists W, munch W m m' /\ (forall x, outside W0 x -> outside W x) /\
                  disjoint_from W (bv_unsigned sp4) 16512 /\ disjoint_from W A_G_NL NK_SIZE /\
                  (bv_unsigned aliasw <> 0 -> 1 <= bv_unsigned acw ->
                     disjoint_from W (bv_unsigned aliasw) (bv_unsigned acw))).
  { destruct (Z.eq_dec (bv_unsigned kcw) 0) as [Hc|Hc].
    - exists [(bv_unsigned sp4 - 80, bv_unsigned sp4)]. split; [exact (N0 Hc)|].
      split; [exact WFR|]. cbn [disjoint_from].
      split; [split; [lia | exact I]|]. split; [split; [unfold apart_gnl in GSEP; lia | exact I]|].
      intros Ha Hac. destruct (ASEP Ha Hac) as [AP _]. unfold apart in AP. split; [lia | exact I].
    - pose proof (bv_unsigned_in_range 64 kcw) as RK. unfold bv_modulus in RK.
      destruct (KSEP Hk ltac:(lia)) as [KP KG]. unfold apart in KP. unfold apart_gnl in KG, GSEP.
      exists [(bv_unsigned sp4 - 80, bv_unsigned sp4); (bv_unsigned kindw, bv_unsigned kindw + bv_unsigned kcw)].
      split; [exact MU|].
      split; [intros x Hx; pose proof (WFR x Hx) as H1; pose proof (WK x Hx Hk) as H2; cbn in H1, H2 |- *; tauto|].
      cbn [disjoint_from].
      split; [split; [lia | split; [lia | exact I]]|].
      split; [split; [lia | split; [lia | exact I]]|].
      intros Ha Hac. destruct (ASEP Ha Hac) as [AP _]. unfold apart in AP.
      pose proof (KASEP Hk ltac:(lia) Ha Hac) as KA. unfold apart in KA.
      split; [lia | split; [lia | exact I]]. }
  destruct MUW as (W & MUm & SUB & DFR & DGN & DAL).
  unfold ainv. split; [exact MI'|]. split; [exact (wmono_trans rsegs _ _ _ WM0 WM)|].
  split; [exact (munch_trans _ _ _ _ MU0 (munch_weaken _ _ _ _ SUB MUm))|].
  split; [exact ST'|].
  split; [apply (rw_cells_transport rsegs W m m'); [exact FA | exact MUm | exact WM |];
          cbn [cells_size csize Nat.add]; apply (disjoint_from_sub W _ 16512); [exact DFR | lia]|].
  split; [apply (bytes_at_transport rsegs W m m'); [exact BB | exact MUm |];
          rewrite LCR; apply (disj_shift W _ 16512 24 16384 DFR); lia|].
  split; [exact (wr_at_transport rsegs _ _ _ _ BW WM)|].
  split; [apply (rw_cells_transport rsegs W m m'); [exact FS | exact MUm | exact WM |];
          rewrite SVS; apply (disj_shift W _ 16512 16408 (Z.of_nat 104) DFR); lia|].
  split; [exact SVS|].
  split; [destruct NK as [NK NL]; split; [|exact NL];
          apply (u8arr_transport rsegs W m m'); [exact NK | exact MUm | exact WM | rewrite NL; exact DGN]|].
  split; [exact (wr_at_transport rsegs _ _ _ _ EW WM)|].
  split; [split; [exact RC | exact CS]|].
  exact (bufst_keep m0 m m' _ _ oa W BA MUm WM DAL).
Qed.

(* what a copy_attr call on the alias buffer leaves *)
Lemma ainv_alias : forall m m' ok oa pay,
  ainv m ok oa ->
  munch [(bv_unsigned sp4 - 80, bv_unsigned sp4); (bv_unsigned aliasw, bv_unsigned aliasw + bv_unsigned acw)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp4) ->
  (bv_unsigned aliasw = 0 -> m' = m) ->
  (bv_unsigned acw = 0 -> munch [(bv_unsigned sp4 - 80, bv_unsigned sp4)] m m') ->
  (bv_unsigned aliasw <> 0 -> 1 <= bv_unsigned acw -> cstr_at m' (bv_unsigned aliasw) (cut_text pay (bv_unsigned acw))) ->
  (bv_unsigned aliasw <> 0 -> 1 <= bv_unsigned acw ->
     exists junk, rw_cells rsegs m' (bv_unsigned aliasw) [CB (Z.to_nat (bv_unsigned acw)) junk]) ->
  ainv m' ok (Some pay).
Proof.
  intros m m' ok oa pay (MI & WM0 & MU0 & ST & FA & BB & BW & FS & SVS & NK & EW & BK & BA)
    MU WM MI' ST' K0 N0 CS RC.
  destruct (Z.eq_dec (bv_unsigned aliasw) 0) as [Hk|Hk].
  { specialize (K0 Hk). subst m'.
    repeat (split; [assumption|]). split; intros; contradiction. }
  pose proof (bv_unsigned_in_range 64 sp4) as RS. unfold bv_modulus in RS.
  destruct LO as [LO0 LO1].
  assert (MUW : exists W, munch W m m' /\ (forall x, outside W0 x -> outside W x) /\
                  disjoint_from W (bv_unsigned sp4) 16512 /\ disjoint_from W A_G_NL NK_SIZE /\
                  (bv_unsigned kindw <> 0 -> 1 <= bv_unsigned kcw ->
                     disjoint_from W (bv_unsigned kindw) (bv_unsigned kcw))).
  { destruct (Z.eq_dec (bv_unsigned acw) 0) as [Hc|Hc].
    - exists [(bv_unsigned sp4 - 80, bv_unsigned sp4)]. split; [exact (N0 Hc)|].
      split; [exact WFR|]. cbn [disjoint_from].
      split; [split; [lia | exact I]|]. split; [split; [unfold apart_gnl in GSEP; lia | exact I]|].
      intros Ha Hac. destruct (KSEP Ha Hac) as [AP _]. unfold apart in AP. split; [lia | exact I].
    - pose proof (bv_unsigned_in_range 64 acw) as RK. unfold bv_modulus in RK.
      destruct (ASEP Hk ltac:(lia)) as [KP KG]. unfold apart in KP. unfold apart_gnl in KG, GSEP.
      exists [(bv_unsigned sp4 - 80, bv_unsigned sp4); (bv_unsigned aliasw, bv_unsigned aliasw + bv_unsigned acw)].
      split; [exact MU|].
      split; [intros x Hx; pose proof (WFR x Hx) as H1; pose proof (WA x Hx Hk) as H2; cbn in H1, H2 |- *; tauto|].
      cbn [disjoint_from].
      split; [split; [lia | split; [lia | exact I]]|].
      split; [split; [lia | split; [lia | exact I]]|].
      intros Ha Hac. destruct (KSEP Ha Hac) as [AP _]. unfold apart in AP.
      pose proof (KASEP Ha Hac Hk ltac:(lia)) as KA. unfold apart in KA.
      split; [lia | split; [lia | exact I]]. }
  destruct MUW as (W & MUm & SUB & DFR & DGN & DKI).
  unfold ainv. split; [exact MI'|]. split; [exact (wmono_trans rsegs _ _ _ WM0 WM)|].
  split; [exact (munch_trans _ _ _ _ MU0 (munch_weaken _ _ _ _ SUB MUm))|].
  split; [exact ST'|].
  split; [apply (rw_cells_transport rsegs W m m'); [exact FA | exact MUm | exact WM |];
          cbn [cells_size csize Nat.add]; apply (disjoint_from_sub W _ 16512); [exact DFR | lia]|].
  split; [apply (bytes_at_transport rsegs W m m'); [exact BB | exact MUm |];
          rewrite LCR; apply (disj_shift W _ 16512 24 16384 DFR); lia|].
  split; [exact (wr_at_transport rsegs _ _ _ _ BW WM)|].
  split; [apply (rw_cells_transport rsegs W m m'); [exact FS | exact MUm | exact WM |];
          rewrite SVS; apply (disj_shift W _ 16512 16408 (Z.of_nat 104) DFR); lia|].
  split; [exact SVS|].
  split; [destruct NK as [NK NL]; split; [|exact NL];
          apply (u8arr_transport rsegs W m m'); [exact NK | exact MUm | exact WM | rewrite NL; exact DGN]|].
  split; [exact (wr_at_transport rsegs _ _ _ _ EW WM)|].
  split; [exact (bufst_keep m0 m m' _ _ ok W BK MUm WM DKI)|].
  split; [exact RC | exact CS].
Qed.

(* the copy_attr contract's Pre at a call on an attribute of the chunk *)
Definition nt_ca_pre := ltac:(let t := eval cbv delta [copy_attr_contract] in copy_attr_contract in
                               lazymatch t with leaf _ _ ?P _ _ => exact P end).
Definition nt_ca_post := ltac:(let t := eval cbv delta [copy_attr_contract] in copy_attr_contract in
                                lazymatch t with leaf _ _ _ _ ?P => exact P end).
Lemma nt_ca_post_ext : post_ext nt_ca_post.
Proof. intros r1 r2 m q1 q2 m' E _ H. unfold nt_ca_post, arg, spZ in *. rewrite <- !E. exact H. Qed.

Lemma copy_pre : forall m ok oa off (outw nw : word)
    (ra t0 t1 t2 s1 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  ainv m ok oa -> 0 <= off -> 4 <= rd16 c off -> off + rd16 c off <= Z.of_nat (length c) ->
  (outw = kindw /\ nw = kcw) \/ (outw = aliasw /\ nw = acw) ->
  nt_ca_pre (mkR ra sp4 gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp4 + 24 + off)) outw nw a3 a4 a5 a6 a7
               aliasw kcw kindw s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m.
Proof.
  intros m ok oa off outw nw ra t0 t1 t2 s1 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (MI & WM0 & MU0 & ST & FA & BB & BW & FS & SVS & NK & EW & BK & BA) H0 H4 HL HO.
  pose proof (bv_unsigned_in_range 64 sp4) as RS. unfold bv_modulus in RS.
  pose proof (rd16_range c off H0 ltac:(lia)) as R16.
  unfold nt_ca_pre. rewrite mkR_a0, mkR_a1, mkR_a2, mkR_sp.
  rewrite unsigned_lit by lia.
  exists (rd16 c off), (slice c (off + 4) (rd16 c off - 4)).
  split; [unfold u16_at; rewrite <- slice_le2 by lia;
          exact (bytes_at_chunk_slice m _ c rest off 2 BB H0 ltac:(lia) ltac:(lia))|].
  split; [unfold RTA_HDR; lia|].
  split; [unfold RTA_HDR; replace (bv_unsigned sp4 + 24 + off + 4) with (bv_unsigned sp4 + 24 + (off + 4)) by lia;
          exact (bytes_at_chunk_slice m _ c rest (off + 4) (rd16 c off - 4) BB ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [unfold RTA_HDR; rewrite slice_length by lia; lia|].
  split; [lia|]. split; [unfold RTA_HDR; lia|].
  split; [right; lia|].
  intros Ho Hn. unfold apart_frame. rewrite mkR_sp.
  destruct HO as [[-> ->]|[-> ->]].
  - destruct (KSEP Ho Hn) as [KP _]. unfold apart in KP. destruct BK as [RK _].
    split; [lia|]. split; [unfold RTA_HDR; lia|]. exact (RK Ho Hn).
  - destruct (ASEP Ho Hn) as [KP _]. unfold apart in KP. destruct BA as [RA _].
    split; [lia|]. split; [unfold RTA_HDR; lia|]. exact (RA Ho Hn).
Qed.

Lemma attr_facts : forall m ok oa off, ainv m ok oa -> 0 <= off -> 4 <= rd16 c off ->
  off + rd16 c off <= Z.of_nat (length c) ->
  u16_at m (bv_unsigned sp4 + 24 + off) (rd16 c off) /\
  bytes_at rsegs m (bv_unsigned sp4 + 24 + off + RTA_HDR) (slice c (off + 4) (rd16 c off - 4)) /\
  Z.of_nat (length (slice c (off + 4) (rd16 c off - 4))) = rd16 c off - RTA_HDR.
Proof.
  intros m ok oa off (MI & WM0 & MU0 & ST & FA & BB & BW & FS & SVS & NK & EW & BK & BA) H0 H4 HL.
  pose proof (rd16_range c off H0 ltac:(lia)) as R16.
  split; [unfold u16_at; rewrite <- slice_le2 by lia;
          exact (bytes_at_chunk_slice m _ c rest off 2 BB H0 ltac:(lia) ltac:(lia))|].
  split; [unfold RTA_HDR; replace (bv_unsigned sp4 + 24 + off + 4) with (bv_unsigned sp4 + 24 + (off + 4)) by lia;
          exact (bytes_at_chunk_slice m _ c rest (off + 4) (rd16 c off - 4) BB ltac:(lia) ltac:(lia) ltac:(lia))|].
  unfold RTA_HDR. rewrite slice_length by lia. lia.
Qed.


(* ---- the walk over one IFLA_LINKINFO (0x161dc .. 0x16214) ---- *)

Local Notation STI pc ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 t3 t4 t5 t6 m :=
  (MS (mkR ra sp4 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 aliasw kcw kindw s5 s6 s7
           (Z_to_bv 64 4) (Z_to_bv 64 131068) (Z_to_bv 64 3) (Z_to_bv 64 1) t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma info_loop : copy_attr_contract -> forall g ioff ileft k oa m
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 : word),
  (Z.to_nat ileft < g)%nat -> 4 <= ileft -> 0 <= ioff -> ioff + ileft <= Z.of_nat (length c) ->
  ainv m k oa ->
  (forall m' (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word),
     ainv m' (kind_scan g c ioff ileft k) oa ->
     evt rsegs Q (STI 0x16218 ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5 s6' s7 t3' t4' t5' t6' m')) ->
  evt rsegs Q (STI 0x161dc ra t0 t1 t2 (Z_to_bv 64 ileft) a0 a1 a2 a3 a4 a5 a6 a7 s5
                   (Z_to_bv 64 (bv_unsigned sp4 + 24 + ioff)) s7 t3 t4 t5 t6 m).
Proof.
  intros HCA g. induction g as [|g IH]; intros ioff ileft k oa m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7
    t3 t4 t5 t6 HN H4 H0 HL AI K; [lia|].
  pose proof AI as (MI & WM0 & MU0 & ST & FA & BB & BW & FS & SVS & NK & EW & BK & BA).
  pose proof (bv_unsigned_in_range 64 sp4) as RS. unfold bv_modulus in RS.
  pose proof (read2_chunk m _ c rest ioff BB H0 ltac:(lia)) as RD1.
  pose proof (read2_chunk m _ c rest (ioff + 2) BB ltac:(lia) ltac:(lia)) as RD2.
  pose proof (rd16_range c ioff H0 ltac:(lia)) as R1.
  pose proof (rd16_range c (ioff + 2) ltac:(lia) ltac:(lia)) as R2.
  zstep. rewrite zx16_wz by lia.
  zstep. if_cases K1; zify_cond K1.
  { rewrite (ks_stop g ioff ileft k) in K by (try lia; apply orb_true_iff; left; apply Z.ltb_lt; lia).
    apply K. exact AI. }
  zstep. if_cases K2; zify_cond K2.
  { rewrite (ks_stop g ioff ileft k) in K by (try lia; apply orb_true_iff; right; apply Z.ltb_lt; lia).
    apply K. exact AI. }
  rewrite (ks_step g ioff ileft k) in K by lia.
  set (l := rd16 c ioff) in *. set (al := nl_align l) in *.
  pose proof (nl_align_ge l ltac:(lia)) as AL. fold al in AL.
  (* 0x16204: the step to the next attribute, shared by both arms *)
  assert (STEP : forall m1 k1 (ra1 t01 t11 t21 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 : word),
    ainv m1 k1 oa ->
    (forall m' (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word),
       ainv m' (kind_scan g c (ioff + al) (ileft - al) k1) oa ->
       evt rsegs Q (STI 0x16218 ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5 s6' s7 t3' t4' t5' t6' m')) ->
    evt rsegs Q (STI 0x16204 ra1 t01 t11 t21 (Z_to_bv 64 ileft) (Z_to_bv 64 l) a11 a21 a31 a41 a51 a61 a71 s5
                     (Z_to_bv 64 (bv_unsigned sp4 + 24 + ioff)) s7 t31 t41 t51 t61 m1)).
  { intros m1 k1 ra1 t01 t11 t21 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 AI1 K1'.
    zstep. zstep. rewrite nl_align_land by lia. fold al.
    zstep. rewrite (bv_swrap_small 32 (ileft - al))
      by (replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity; lia).
    zstep. zstep. if_cases K5; zify_cond K5.
    - try rewrite sgn_lit in K5 by lia.
      replace (bv_unsigned sp4 + 24 + ioff + al) with (bv_unsigned sp4 + 24 + (ioff + al)) by lia.
      apply (IH (ioff + al) (ileft - al) k1 oa m1); [lia | lia | lia | lia | exact AI1 | exact K1'].
    - try rewrite sgn_lit in K5 by lia.
      apply K1'. rewrite ks_small by lia. exact AI1. }
  zstep. rewrite zx16_wz by lia.
  zstep. if_cases K3; zify_cond K3.
  { (* not an IFLA_INFO_KIND: straight to the step *)
    replace (rd16 c (ioff + 2) =? 1) with false in K by (symmetry; apply Z.eqb_neq; lia).
    exact (STEP m k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AI K). }
  (* an IFLA_INFO_KIND: copy_attr(i, kind, kind_n), then the step *)
  replace (rd16 c (ioff + 2) =? 1) with true in K by (symmetry; apply Z.eqb_eq; lia).
  zstep. zstep. zstep. zstep.
  eapply (leaf_call COPY_ATTR 80 _ _ _ HCA nt_ca_post_ext Q QX).
  { eapply copy_pre; [exact AI | exact H0 | lia | lia | left; split; reflexivity]. }
  { exact MI. }
  { exact ST. }
  { lia. }
  { lia. }
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST' PO.
  cbv beta in MU, PO. rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_sp in MU, PO.
  destruct PO as (PN & PZ & PC & PR).
  rewrite ret_pc_even by (lia || reflexivity).
  destruct (attr_facts m k oa ioff AI H0 ltac:(lia) ltac:(lia)) as (U16 & BP & LP).
  assert (AI' : ainv m' (Some (slice c (ioff + 4) (l - 4))) oa).
  { apply (ainv_kind m m' k oa _ AI MU WM MI' ST' PN PZ); [|exact PR].
    intros Hk Hc. specialize (PC Hk Hc l (slice c (ioff + 4) (l - 4))).
    rewrite mkR_a0, unsigned_lit in PC by lia.
    exact (PC U16 ltac:(unfold RTA_HDR; lia) BP LP). }
  pose proof AI' as (MI2 & WM2 & MU2 & ST2 & FA2 & BB2 & BW2 & FS2 & SVS2 & NK2 & EW2 & BK2 & BA2).
  pose proof (read2_chunk m' _ c rest ioff BB2 H0 ltac:(lia)) as RD3.
  zstep. rewrite zx16_wz by lia.
  exact (STEP m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AI' K).
Qed.

(* ---- the walk over the attributes of the first RTM_NEWLINK (0x16194 .. 0x1622c) ---- *)

Lemma attr_loop : copy_attr_contract -> forall f aoff aleft a m
    (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 : word),
  (Z.to_nat aleft < f)%nat -> 4 <= aleft -> 0 <= aoff -> aoff + aleft <= Z.of_nat (length c) ->
  ainv m (a_kind a) (a_alias a) ->
  (forall m' (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word),
     ainv m' (a_kind (attr_scan f c aoff aleft a)) (a_alias (attr_scan f c aoff aleft a)) ->
     evt rsegs Q (STI 0x1623c ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 0) s7'
                     t3' t4' t5' t6' m')) ->
  evt rsegs Q (STI 0x16194 ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (bv_unsigned sp4 + 24 + aoff)) s6 (Z_to_bv 64 aleft) t3 t4 t5 t6 m).
Proof.
  intros HCA f. induction f as [|f IH]; intros aoff aleft a m ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6
    t3 t4 t5 t6 HN H4 H0 HL AI K; [lia|].
  pose proof AI as (MI & WM0 & MU0 & ST & FA & BB & BW & FS & SVS & NK & EW & BK & BA).
  pose proof (bv_unsigned_in_range 64 sp4) as RS. unfold bv_modulus in RS.
  pose proof (read2_chunk m _ c rest aoff BB H0 ltac:(lia)) as RD1.
  pose proof (read2_chunk m _ c rest (aoff + 2) BB ltac:(lia) ltac:(lia)) as RD2.
  pose proof (rd16_range c aoff H0 ltac:(lia)) as R1.
  pose proof (rd16_range c (aoff + 2) ltac:(lia) ltac:(lia)) as R2.
  zstep. rewrite zx16_wz by lia.
  zstep.
  zstep. if_cases K1; zify_cond K1.
  { rewrite (as_stop f aoff aleft a) in K by (try lia; apply orb_true_iff; left; apply Z.ltb_lt; lia).
    apply K. exact AI. }
  zstep. if_cases K2; zify_cond K2.
  { rewrite (as_stop f aoff aleft a) in K by (try lia; apply orb_true_iff; right; apply Z.ltb_lt; lia).
    apply K. exact AI. }
  rewrite (as_step f aoff aleft a) in K by lia.
  set (l := rd16 c aoff) in *. set (al := nl_align l) in *.
  pose proof (nl_align_ge l ltac:(lia)) as AL. fold al in AL.
  (* 0x16218: the step to the next attribute, shared by the three arms *)
  assert (STEP : forall m1 a1 (ra1 t01 t11 t21 s11 a01 a11 a21 a31 a41 a51 a61 a71 s61 t31 t41 t51 t61 : word),
    ainv m1 (a_kind a1) (a_alias a1) ->
    (forall m' (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word),
       ainv m' (a_kind (attr_scan f c (aoff + al) (aleft - al) a1))
               (a_alias (attr_scan f c (aoff + al) (aleft - al) a1)) ->
       evt rsegs Q (STI 0x1623c ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 0) s7'
                       t3' t4' t5' t6' m')) ->
    evt rsegs Q (STI 0x16218 ra1 t01 t11 t21 s11 a01 a11 a21 a31 a41 a51 a61 a71
                     (Z_to_bv 64 (bv_unsigned sp4 + 24 + aoff)) s61 (Z_to_bv 64 aleft) t31 t41 t51 t61 m1)).
  { intros m1 a1' ra1 t01 t11 t21 s11 a01 a11 a21 a31 a41 a51 a61 a71 s61 t31 t41 t51 t61 AI1 K1'.
    pose proof AI1 as (MI1 & WM1 & MU1 & ST1 & FA1 & BB1 & BW1 & FS1 & SVS1 & NK1 & EW1 & BK1 & BA1).
    pose proof (read2_chunk m1 _ c rest aoff BB1 H0 ltac:(lia)) as RD3.
    zstep. rewrite zx16_wz by lia.
    zstep. zstep. rewrite nl_align_land by lia. change (nl_align (rd16 c aoff)) with al.
    zstep. try rewrite (Z.mod_small al) by lia.
    rewrite (bv_swrap_small 32 (aleft - al))
      by (replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity; lia).
    zstep. zstep. if_cases K5; zify_cond K5.
    - try rewrite sgn_lit in K5 by lia.
      replace (bv_unsigned sp4 + 24 + aoff + al) with (bv_unsigned sp4 + 24 + (aoff + al)) by lia.
      apply (IH (aoff + al) (aleft - al) a1' m1); [lia | lia | lia | lia | exact AI1 | exact K1'].
    - try rewrite sgn_lit in K5 by lia.
      zstep. zstep. apply K1'. rewrite as_small by lia. exact AI1. }
  zstep. rewrite zx16_wz by lia.
  zstep. zstep. if_cases K3; zify_cond K3.
  { (* IFLA_LINKINFO: the walk over its attributes, then the step *)
    replace (rd16 c (aoff + 2) =? 20) with false in K by (symmetry; apply Z.eqb_neq; lia).
    replace (rd16 c (aoff + 2) =? 18) with true in K by (symmetry; apply Z.eqb_eq; lia).
    zstep. zstep. if_cases K4; zify_cond K4.
    { (* fewer than 8 bytes: no inner attribute *)
      rewrite (ks_small f (aoff + 4) (l - 4) (a_kind a)) in K by lia.
      apply (STEP m a); [exact AI|]. destruct a as [ka aa]. exact K. }
    zstep. zstep.
    rewrite (bv_swrap_small 32 (l + -4)) by (replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity; lia).
    replace (l + -4) with (l - 4) by lia.
    replace (bv_unsigned sp4 + 24 + aoff + 4) with (bv_unsigned sp4 + 24 + (aoff + 4)) by lia.
    apply (info_loop HCA f (aoff + 4) (l - 4) (a_kind a) (a_alias a) m); [lia | lia | lia | lia | exact AI |].
    intros m' ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' AI'.
    apply (STEP m' (Attrs (kind_scan f c (aoff + 4) (l - 4) (a_kind a)) (a_alias a))); [exact AI' | exact K]. }
  zstep. zstep. if_cases K4; zify_cond K4.
  { (* another attribute: the step *)
    replace (rd16 c (aoff + 2) =? 20) with false in K by (symmetry; apply Z.eqb_neq; lia).
    replace (rd16 c (aoff + 2) =? 18) with false in K by (symmetry; apply Z.eqb_neq; lia).
    exact (STEP m a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AI K). }
  (* IFLA_IFALIAS: copy_attr(a, alias, alias_n), then the step *)
  replace (rd16 c (aoff + 2) =? 20) with true in K by (symmetry; apply Z.eqb_eq; lia).
  zstep. zstep. zstep. zstep.
  eapply (leaf_call COPY_ATTR 80 _ _ _ HCA nt_ca_post_ext Q QX).
  { eapply copy_pre; [exact AI | exact H0 | lia | lia | right; split; reflexivity]. }
  { exact MI. }
  { exact ST. }
  { lia. }
  { lia. }
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI' ST' PO.
  cbv beta in MU, PO. rewrite ?mkR_a0, ?mkR_a1, ?mkR_a2, ?mkR_sp in MU, PO.
  destruct PO as (PN & PZ & PC & PR).
  rewrite ret_pc_even by (lia || reflexivity).
  destruct (attr_facts m _ _ aoff AI H0 ltac:(lia) ltac:(lia)) as (U16 & BP & LP).
  assert (AI' : ainv m' (a_kind a) (Some (slice c (aoff + 4) (l - 4)))).
  { apply (ainv_alias m m' _ _ _ AI MU WM MI' ST' PN PZ); [|exact PR].
    intros Hk Hc. specialize (PC Hk Hc l (slice c (aoff + 4) (l - 4))).
    rewrite mkR_a0, unsigned_lit in PC by lia.
    exact (PC U16 ltac:(unfold RTA_HDR; lia) BP LP). }
  zstep.
  apply (STEP m' (Attrs (a_kind a) (Some (slice c (aoff + 4) (l - 4))))); [exact AI' | exact K].
Qed.

End Scan.
