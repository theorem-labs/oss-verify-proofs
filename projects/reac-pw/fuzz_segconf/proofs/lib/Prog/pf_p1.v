(** reac_segconf_parse_file (plain build, image 3776ca44d75c), piece P1 of family F3: the entry, the setup and the
    return (reac_segconf_parse_file_pieces_c.v S_P1 = H_DONE /\ ((forall n, H_HEAD n) -> H_DONE -> H_ENTRY)), from
    the contract of snprintf (snprintf_c.v). Written new.

    Code (plain binary):
      0x14cbc        addi sp, sp, -0x3d0; sd ra, s0-s11 at sp + 0x3c8 .. 0x368
      0x14cf4-0x14d18 a3 = label, s2 = text, s0 = c, s1 = 0x3000, s3 = c + 0x40e0 (&gen), s4 = c + 0x4080 (reading),
                     a0 = 0x2c80; 0x14d1c bnez a3 (else a3 = "reac-pw.conf" 0x10463); 0x14d28 s5 = c + 0x2c80 (&n)
      0x14d3c        snprintf(c->reading, 96, "%s" 0x104e0, label)
      0x14d40-0x14d48 c->gen++; 0x14d4c beqz s2 (the text is not NULL: reader_pre)
      0x14d50-0x14d64 the slots sp + 0x30 / 0x28 / 0x20, lbu *text, cur_name = 16 zero bytes
      0x14d68        beqz *text -> DONE 0x1550c
      0x14d6c-0x14dc0 the loop constants and the slots sp + 8 / 0x40 / 0x38 / 0x18 / 0x10; HEAD 0x14dc4
      DONE 0x1550c   ld a0, 0x30(sp); lw a0, 0(a0); j 0x1551c; restores; addi sp; ret
    The cuts' posts are relative to the memory, F and fc at the cut; [pf1_weaken] brings them back to the entry's
    (the contract's W holds every write: the frame, c->reading and c->gen, and the cuts' own W). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_query_facts pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_parse_file_pieces_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists and bytes *)
Lemma pf1_zb_zs : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [map]. rewrite sq_byte_lit, IH. reflexivity. Qed.

Lemma pf1_zs_zb : forall l : list Z, Forall (fun x => 0 <= x < 256) l -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. inversion H as [|? ? Hx Hl]; subst.
  cbn [map]. rewrite (IH Hl). f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. lia.
Qed.

Lemma pf1_zs_range : forall bs : list byte, Forall (fun x => 0 <= x < 256) (map bv_unsigned bs).
Proof.
  intros bs. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (b & <- & _). apply sq_byte_range.
Qed.

Lemma pf1_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma pf1_Forall_firstn : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; [constructor|].
  destruct l as [|x l]; [constructor|]. inversion H; subst. cbn [firstn]. constructor; auto.
Qed.

Lemma pf1_in_firstn : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Lemma pf1_app_split : forall (l : list byte) k, (k <= length l)%nat -> exists l1 l2, l = l1 ++ l2 /\ length l1 = k.
Proof.
  intros l k H. exists (firstn k l), (skipn k l). split; [symmetry; apply firstn_skipn | rewrite length_firstn; lia].
Qed.

Lemma pf1_lab_cases : forall lab : option (list Z), (exists l, lab = Some l) \/ lab = None.
Proof. intros [l|]; [left; exists l; reflexivity | right; reflexivity]. Qed.

Lemma pf1_dj_mono : forall W a n n', disjoint_from W a n -> 0 <= n' <= n -> disjoint_from W a n'.
Proof.
  induction W as [|[x y] W IH]; cbn [disjoint_from]; intros a n n' H Hn; [exact I|].
  destruct H as [H1 H2]. split; [lia | eapply IH; eauto].
Qed.

(** The text bound 65535 (a nat numeral lia does not read). *)
Lemma pf1_le65535 : forall n : nat, (n <= 65535)%nat -> Z.of_nat n <= 65535.
Proof.
  intros n H. apply Nat2Z.inj_le in H. replace (Z.of_nat 65535) with 65535 in H by (vm_compute; reflexivity). exact H.
Qed.

Lemma pf1_span : forall a s, Z.of_nat (length s) + 1 <= cstr_span a s <= Z.of_nat (length s) + 8.
Proof.
  intros a s. unfold cstr_span.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia.
Qed.

(** The fields of the 16616 bytes of c, split at the reading field: P (16512 bytes), the field (96), gen (4), the
    tail (4). *)
Lemma pf1_fld_app_l : forall (l1 l2 : list byte) off n, (off + n <= length l1)%nat -> fld off n (l1 ++ l2) = fld off n l1.
Proof.
  intros l1 l2 off n H. unfold fld. rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length l1 - off))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma pf1_fld_app_r : forall (l1 l2 : list byte) off n, (length l1 <= off)%nat ->
  fld off n (l1 ++ l2) = fld (off - length l1) n l2.
Proof. intros l1 l2 off n H. unfold fld. rewrite skipn_app, (skipn_all2 l1) by lia. reflexivity. Qed.

Lemma pf1_fld_full : forall (l : list byte) off n, off = 0%nat -> length l = n -> fld off n l = l.
Proof. intros l off n -> <-. unfold fld. rewrite skipn_O. apply firstn_all. Qed.

Lemma pf1_fld_lo : forall (P A B : list byte) off n, (off + n <= length P)%nat -> fld off n (P ++ A) = fld off n (P ++ B).
Proof. intros. rewrite !pf1_fld_app_l by lia. reflexivity. Qed.

Lemma pf1_fld_rd : forall (P Y G Q : list byte), Z.of_nat (length P) = 16512 -> length Y = 96%nat ->
  fld (Z.to_nat 16512) (Z.to_nat 96) (P ++ Y ++ G ++ Q) = Y.
Proof.
  intros P Y G Q LP LY. rewrite pf1_fld_app_r by lia. rewrite pf1_fld_app_l by lia. apply pf1_fld_full; lia.
Qed.

Lemma pf1_fld_gen : forall (P Y G Q : list byte), Z.of_nat (length P) = 16512 -> length Y = 96%nat ->
  length G = 4%nat -> fld (Z.to_nat 16608) (Z.to_nat 4) (P ++ Y ++ G ++ Q) = G.
Proof.
  intros P Y G Q LP LY LG. rewrite pf1_fld_app_r by lia. rewrite pf1_fld_app_r by lia.
  rewrite pf1_fld_app_l by lia. apply pf1_fld_full; lia.
Qed.

Lemma pf1_fld_at : forall (P' G Q : list byte), Z.of_nat (length P') = 16608 -> length G = 4%nat ->
  fld (Z.to_nat 16608) (Z.to_nat 4) (P' ++ G ++ Q) = G.
Proof. intros P' G Q LP LG. rewrite pf1_fld_app_r by lia. rewrite pf1_fld_app_l by lia. apply pf1_fld_full; lia. Qed.

Ltac pf1_rcn := unfold RC_N, RC_REFUSAL, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN, SEG_C_SIZE in *.

(** snprintf's text at c->reading: the reading field holds it, every other field is the old one. *)
Lemma pf1_enc_reading : forall rc P R G Q Tw, rconf_enc rc (P ++ R ++ G ++ Q) ->
  Z.of_nat (length P) = 16512 -> length R = 96%nat -> length G = 4%nat -> length Q = 4%nat ->
  (length Tw < 96)%nat -> ~ In 0 Tw -> Forall (fun x => 0 <= x < 256) Tw ->
  rconf_enc (RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc) Tw (rc_gen rc))
    ((P ++ pf_bytes (Tw ++ [0]) ++ skipn (S (length Tw)) R) ++ G ++ Q).
Proof.
  intros rc P R G Q Tw (HL & HS & HSeg & HN & HR & HRef & HNR & HRd & HOv & HRead & HG) LP LR LG LQ LT NT BT.
  set (X := pf_bytes (Tw ++ [0]) ++ skipn (S (length Tw)) R).
  assert (LX : length X = 96%nat).
  { unfold X, pf_bytes. rewrite length_app, length_map, length_app, length_skipn. cbn [length]. lia. }
  rewrite <- app_assoc.
  unfold rconf_enc, fldz in *. cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen]. pf1_rcn.
  rewrite !length_app in HL.
  split; [rewrite !length_app; lia|].
  split; [exact HS|].
  split; [intros i Hi; rewrite (pf1_fld_lo P _ (R ++ G ++ Q)) by lia; exact (HSeg i Hi)|].
  split; [rewrite (pf1_fld_lo P _ (R ++ G ++ Q)) by lia; exact HN|].
  split; [exact HR|].
  split; [intros i Hi; rewrite (pf1_fld_lo P _ (R ++ G ++ Q)) by lia; exact (HRef i Hi)|].
  split; [rewrite (pf1_fld_lo P _ (R ++ G ++ Q)) by lia; exact HNR|].
  split; [rewrite (pf1_fld_lo P _ (R ++ G ++ Q)) by lia; exact HRd|].
  split; [rewrite (pf1_fld_lo P _ (R ++ G ++ Q)) by lia; exact HOv|].
  split.
  - rewrite (pf1_fld_rd P X G Q LP LX). unfold cstr_enc.
    split; [exact LX|]. split; [exact LT|]. split; [exact NT|].
    unfold X, zs, pf_bytes. rewrite map_app, pf1_zs_zb.
    + rewrite firstn_app, length_app. cbn [length].
      replace (S (length Tw) - (length Tw + 1))%nat with 0%nat by lia.
      rewrite firstn_O, app_nil_r. apply firstn_all2. rewrite length_app. cbn [length]. lia.
    + apply Forall_app. split; [exact BT | constructor; [lia | constructor]].
  - rewrite (pf1_fld_gen P X G Q LP LX LG). rewrite (pf1_fld_gen P R G Q LP LR LG) in HG. exact HG.
Qed.

(** c->gen++: the gen field holds gen + 1, every other field is the old one. *)
Lemma pf1_enc_gen : forall rcA P' G Q, rconf_enc rcA (P' ++ G ++ Q) ->
  Z.of_nat (length P') = 16608 -> length G = 4%nat -> length Q = 4%nat -> rc_gen rcA + 1 < 2 ^ 32 ->
  rconf_enc (RConf (rc_seg rcA) (rc_refusal rcA) (rc_refused rcA) (rc_overflow rcA) (rc_reading rcA) (rc_gen rcA + 1))
    (P' ++ le4 (Z_to_bv 64 (rc_gen rcA + 1)) ++ Q).
Proof.
  intros rcA P' G Q (HL & HS & HSeg & HN & HR & HRef & HNR & HRd & HOv & HRead & HG) LP LG LQ Hg.
  unfold rconf_enc, fldz in *. cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen]. pf1_rcn.
  rewrite !length_app in HL.
  split; [rewrite !length_app, length_le4; lia|].
  split; [exact HS|].
  split; [intros i Hi; rewrite (pf1_fld_lo P' _ (G ++ Q)) by lia; exact (HSeg i Hi)|].
  split; [rewrite (pf1_fld_lo P' _ (G ++ Q)) by lia; exact HN|].
  split; [exact HR|].
  split; [intros i Hi; rewrite (pf1_fld_lo P' _ (G ++ Q)) by lia; exact (HRef i Hi)|].
  split; [rewrite (pf1_fld_lo P' _ (G ++ Q)) by lia; exact HNR|].
  split; [rewrite (pf1_fld_lo P' _ (G ++ Q)) by lia; exact HRd|].
  split; [rewrite (pf1_fld_lo P' _ (G ++ Q)) by lia; exact HOv|].
  split; [rewrite (pf1_fld_lo P' _ (G ++ Q)) by lia; exact HRead|].
  rewrite (pf1_fld_at P' G Q LP LG) in HG. rewrite (pf1_fld_at P' _ Q LP (length_le4 _)).
  destruct HG as [HG0 _]. split; [lia | reflexivity].
Qed.

(** The spine's reading: snprintf(reading, 96, "%s", l) stores the first 95 bytes of l. *)
Lemma pf1_F_s : F_s = [37; 115].
Proof. vm_compute. reflexivity. Qed.

Lemma pf1_reading : forall L, ~ In 0 L -> snprintf_s 96 F_s [AS L] = firstn (Z.to_nat (96 - 1)) (L ++ []).
Proof.
  intros L HL. unfold snprintf_s. rewrite pf1_F_s. change (fmt [37; 115] [AS L]) with (cut_nul L ++ []).
  rewrite cut_nul_id by exact HL. reflexivity.
Qed.

Lemma pf1_rpf_snd : forall rc s lab,
  snd (r_parse_file rc s lab) = Z.of_nat (length (rc_seg (fst (r_parse_file rc s lab)))).
Proof. intros rc s lab. rewrite (L_parse_start_holds rc s lab). reflexivity. Qed.

(** ** Memory *)
Lemma pf1_cstr_munch : forall W m m' a s, cstr_at rsegs m a s -> munch W m m' ->
  disjoint_from W a (cstr_span a s) -> cstr_at rsegs m' a s.
Proof.
  intros W m m' a s (bs & sl & B & Hz & Hn & Hsl) MU D.
  set (k := (- (a + Z.of_nat (length s) + 1)) mod 8) in *.
  assert (Hk : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
  assert (Hlen : length bs = length s) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  exists bs, (firstn (Z.to_nat k) sl). split; [|split; [exact Hz|split; [exact Hn|]]].
  - apply (bytes_at_transport rsegs W m m' a).
    + rewrite <- (firstn_skipn (Z.to_nat k) sl) in B.
      replace (bs ++ ZERO :: firstn (Z.to_nat k) sl ++ skipn (Z.to_nat k) sl)
        with ((bs ++ ZERO :: firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl) in B
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in B. exact (proj1 B).
    + exact MU.
    + eapply pf1_dj_mono; [exact D|]. unfold cstr_span. fold k.
      rewrite length_app. cbn [length]. rewrite length_firstn, Hlen. lia.
  - rewrite length_firstn. lia.
Qed.

Lemma pf1_rconf_munch : forall W m m' c rc, rconf_at rsegs m c rc -> munch W m m' ->
  disjoint_from W c SEG_C_SIZE -> rconf_at rsegs m' c rc.
Proof.
  intros W m m' c rc (bs & B & E) MU D. exists bs. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L. exact D.
Qed.

Lemma pf1_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi);
    [right; intros [H' _]; lia | left; split; [lia | exact H] ..].
Qed.

Lemma pf1_task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd rsegs m x <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU P x b Hx.
  destruct (pf1_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (T x b Hx).
  - specialize (P x Ho). unfold mrd in P. destruct (m x) as [b0|] eqn:E.
    + exact (T x b0 E).
    + left. intros Hf. apply P. exact (MemNorm.seg_rom_unmapped rsegs x Hf).
Qed.

(** The reserved segments of the image (page-rounded PT_LOADs) and the blocks no one of them covers. *)
Definition PF1_RES : list (Z * Z) := [(0x10000, 0x3000); (0x13000, 0xd000); (0x20000, 0x2000); (0x22000, 0x32000)].

Lemma pf1_res_eq : map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs) = PF1_RES.
Proof. vm_compute. reflexivity. Qed.

Lemma pf1_segs_eq : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs = PF1_RES.
Proof. vm_compute. reflexivity. Qed.

Lemma pf1_noimg_res : forall c n, blk_noimg rsegs c n -> forall B Sz, In (B, Sz) PF1_RES ->
  forall i, 0 <= i < n -> ~ (B <= c + i < B + Sz).
Proof.
  intros c n H B Sz Hin i Hi. rewrite <- pf1_res_eq in Hin. apply in_map_iff in Hin as (s & Es & Hs).
  injection Es as E1 E2. specialize (H i Hi s Hs). rewrite E1, E2 in H. exact H.
Qed.

Lemma pf1_noimg_sub : forall c N a n, blk_noimg rsegs c N -> c <= a -> a + n <= c + N -> blk_noimg rsegs a n.
Proof.
  intros c N a n H H1 H2 i Hi s Hs. replace (a + i) with (c + (a - c + i)) by lia. apply H; [lia | exact Hs].
Qed.

Lemma pf1_noimg_disj : forall c N B Sz p k q l, blk_noimg rsegs c N -> In (B, Sz) PF1_RES ->
  B <= p -> p + k <= B + Sz -> 0 < k -> c <= q -> q + l <= c + N -> 0 < l -> q + l <= p \/ p + k <= q.
Proof.
  intros c N B Sz p k q l H Hin H1 H2 Hk H3 H4 Hl.
  destruct (Z_le_dec (q + l) p) as [?|Hqp]; [left; lia|]. destruct (Z_le_dec (p + k) q) as [?|Hpq]; [right; lia|].
  exfalso. apply (pf1_noimg_res c N H B Sz Hin (Z.max p q - c)); lia.
Qed.

Lemma pf1_fs_some : forall (sl : list Segment) a n, 0 < n -> find_segment sl a n <> None ->
  exists sg, In sg sl /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  induction sl as [|sg rest IH]; intros a n Hn H; [cbn [find_segment] in H; contradiction|].
  revert H. cbn [find_segment].
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) a) as [Hb1|Hb1]; cbn [andb];
    [destruct (Z.leb_spec (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) as [Hb2|Hb2]; cbn [andb] |]; intros H.
  - exists sg. split; [left; reflexivity | lia].
  - destruct (IH a n Hn H) as (s & Hs & Hr). exists s. split; [right; exact Hs | exact Hr].
  - destruct (IH a n Hn H) as (s & Hs & Hr). exists s. split; [right; exact Hs | exact Hr].
Qed.

Lemma pf1_res_none : forall x, (forall B Sz, In (B, Sz) PF1_RES -> ~ (B <= x < B + Sz)) ->
  find_segment rsegs x 1 = None.
Proof.
  intros x H. destruct (find_segment rsegs x 1) eqn:E; [|reflexivity]. exfalso.
  assert (Hs : find_segment rsegs x 1 <> None) by congruence.
  destruct (pf1_fs_some rsegs x 1 ltac:(lia) Hs) as (sg & Hin & Hr).
  apply (H (Z.of_N (seg_base sg)) (Z.of_N (seg_size sg))); [|exact Hr].
  rewrite <- pf1_segs_eq. apply in_map_iff. exists sg. split; [reflexivity | exact Hin].
Qed.

(** A present byte of such a block is in the overlay, so it is writable. *)
Lemma pf1_wr_at_block : forall m a bs, bytes_at rsegs m a bs -> blk_noimg rsegs a (Z.of_nat (length bs)) ->
  wr_at rsegs m a (Z.of_nat (length bs)).
Proof.
  intros m a bs (H0 & H1 & H) Hni. split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hr : mrd rsegs m (wa (a + i)) <> None).
  { replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. rewrite H by lia.
    intros C. apply nth_error_None in C. lia. }
  unfold mrd in Hr. unfold wview. destruct (m (wa (a + i))) as [b|]; [discriminate|].
  exfalso. apply Hr. apply (MemNorm.seg_rom_unmapped rsegs). apply pf1_res_none.
  intros B Sz Hin. unfold wa. rewrite unsigned_lit by lia. exact (pf1_noimg_res a _ Hni B Sz Hin i Hi).
Qed.

Lemma pf1_wr_at_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) Ha Hn Hl. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

(** printf's guard cells and the box-model table lie in the image: a write apart from them keeps them. *)
Lemma pf1_ssp_munch : forall W m m', ssp_ok m -> munch W m m' ->
  disjoint_from W 0x21818 8 -> disjoint_from W 0x52e80 8 -> ssp_ok m'.
Proof.
  intros W m m' (G1 & g & G2) MU D1 D2. unfold ssp_ok, SA, SEG_PLAIN in *. cbn [sa_got_guard sa_guard] in *.
  split; [|exists g].
  - eapply bytes_at_transport; [exact G1 | exact MU |]. rewrite length_le8. exact D1.
  - eapply bytes_at_transport; [exact G2 | exact MU |]. rewrite length_le8. exact D2.
Qed.

Lemma pf1_cat_munch : forall W m m', cat_img rsegs m (sa_catalogue SA) -> munch W m m' ->
  disjoint_from W 0x20ad0 CAT_BYTES -> cat_img rsegs m' (sa_catalogue SA).
Proof.
  intros W m m' CAT MU D a Ha. rewrite <- (CAT a Ha). unfold mrd.
  unfold SA, SEG_PLAIN in Ha. cbn [sa_catalogue] in Ha. unfold CAT_BYTES in *.
  assert (Q : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  rewrite Q. reflexivity.
Qed.

(** Bytes of a run of cells of a frame. *)
Lemma pf1_rw_sub : forall m A cs k j a bs, rw_cells rsegs m A cs ->
  a = A + Z.of_nat (cells_size (firstn k cs)) -> bs = cells_bytes (firstn j (skipn k cs)) -> bytes_at rsegs m a bs.
Proof.
  intros m A cs k j a bs [[Hwf Hb] _] -> ->.
  rewrite <- (firstn_skipn k cs) in Hwf, Hb. rewrite cells_bytes_app in Hb. apply cells_wf_app in Hwf as [W1 W2].
  apply bytes_at_app in Hb as [_ Hb]. rewrite cells_bytes_length in Hb by exact W1.
  rewrite <- (firstn_skipn j (skipn k cs)) in Hb. rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb _].
  exact Hb.
Qed.

(** `lw; addi 1; sw` of a u32 field holding r stores the bytes of r + 1. *)
Lemma pf1_le4_eqm : forall x y : word, bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32 -> le4 x = le4 y.
Proof.
  intros x y H. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned x) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned y) 32) by lia. rewrite H. reflexivity.
Qed.

Lemma pf1_le4_inc : forall r, 0 <= r < 2 ^ 32 ->
  le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 r)) + 1)) = le4 (Z_to_bv 64 (r + 1)).
Proof.
  intros r Hr. apply pf1_le4_eqm. unfold sx32. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma pf1_read_all : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs B. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) B ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. rewrite Z.add_0_r in R. change (skipn 0 bs) with bs in R.
  rewrite firstn_all in R. exact R.
Qed.

Lemma pf1_nm0 : forall m a, bytes_at rsegs m a (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ []) -> pf_nm_at m a [].
Proof.
  intros m a B. exists (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0) ++ []). split; [exact B|].
  unfold cstr_enc. split; [reflexivity|]. split; [cbn [length]; lia|]. split; [intros []|]. vm_compute. reflexivity.
Qed.

(** The first byte of a C string, as `lbu` reads it. *)
Lemma pf1_byte0 : forall m a s, cstr_at rsegs m a s ->
  ov_read_bytes rsegs m (wa a) 1 = Some [Z_to_bv 8 (hd0 s)] /\ 0 <= hd0 s < 256 /\ (hd0 s = 0 <-> s = []).
Proof.
  intros m a s (bs & sl & B & Hz & Hn & Hsl).
  pose proof (bytes_at_read rsegs m a _ 0 1 B ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia)) as R.
  rewrite Z.add_0_r in R.
  destruct bs as [|b bs].
  - unfold zs in Hz. cbn [map] in Hz. subst s. cbn [app skipn firstn Z.to_nat] in R.
    split; [exact R|]. cbn [hd0]. split; [lia | tauto].
  - unfold zs in Hz. cbn [map] in Hz. subst s. cbn [app skipn firstn Z.to_nat] in R. cbn [hd0].
    rewrite sq_byte_lit. split; [exact R|]. split; [apply sq_byte_range|].
    split; [intros E; exfalso; apply Hn; left; exact E | intros E; discriminate E].
Qed.

(** The two strings in .rodata the setup reads. *)
Lemma pf1_label_ro : ro_bytes_b rsegs STR_BASE (zb S_base ++ [ZERO]) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pf1_label_at : forall m, mem_inv rsegs m -> cstr_at rsegs m STR_BASE S_base.
Proof.
  intros m MI. exists (zb S_base), [].
  assert (LB : length (zb S_base ++ [ZERO]) = 13%nat) by (vm_compute; reflexivity).
  split; [|split; [vm_compute; reflexivity | split]].
  - apply (ro_bytes_at rsegs m); [exact MI | unfold STR_BASE; lia | rewrite LB; unfold STR_BASE; lia |].
    apply ro_bytes_b_sound. exact pf1_label_ro.
  - intros H. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H.
  - apply Z.leb_le. vm_compute. reflexivity.
Qed.

Lemma pf1_label_span : cstr_span STR_BASE S_base = 13.
Proof. vm_compute. reflexivity. Qed.

Lemma pf1_label_len : length S_base = 12%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma pf1_fmt_ro : ro_bytes_b rsegs PF_STR_S (pf_bytes ([37; 115] ++ [0])) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pf1_fmt_at : forall m a, mem_inv rsegs m -> a = PF_STR_S -> bytes_at rsegs m a (pf_bytes ([37; 115] ++ [0])).
Proof.
  intros m a MI ->.
  apply (ro_bytes_at rsegs m); [exact MI | unfold PF_STR_S; lia |
    change (Z.of_nat (length (pf_bytes ([37; 115] ++ [0])))) with 3; unfold PF_STR_S; lia |].
  apply ro_bytes_b_sound. exact pf1_fmt_ro.
Qed.

(** The %s argument of snprintf: the C string L at r with the slack printf's strnlen reads. *)
Lemma pf1_arg_ptr : forall m r L lo' S D n, cstr_at rsegs m r L -> 0 < r ->
  apart r (cstr_span r L) lo' S -> apart r (cstr_span r L) D (D + n) ->
  exists slack : list byte,
    bytes_at rsegs m r (pf_bytes (L ++ [0]) ++ slack) /\
    (- (r + Z.of_nat (length L) + 1)) mod 8 <= Z.of_nat (length slack) /\ 0 < r /\
    (r + Z.of_nat (length L) + 1 + Z.of_nat (length slack) <= lo' \/ S <= r) /\
    (r + Z.of_nat (length L) + 1 + Z.of_nat (length slack) <= D \/ D + n <= r).
Proof.
  intros m r L lo' S D n (bs & sl & B & Hz & Hn & Hsl) Hr A1 A2.
  set (k := (- (r + Z.of_nat (length L) + 1)) mod 8) in *.
  assert (Hk : 0 <= k < 8) by (subst k; apply Z.mod_pos_bound; lia).
  exists (firstn (Z.to_nat k) sl).
  assert (LF : Z.of_nat (length (firstn (Z.to_nat k) sl)) = k) by (rewrite length_firstn; lia).
  assert (EB : pf_bytes (L ++ [0]) = bs ++ [ZERO]).
  { unfold pf_bytes. rewrite map_app, <- Hz. unfold zs. rewrite pf1_zb_zs. reflexivity. }
  split.
  - rewrite EB, <- app_assoc. cbn [app]. rewrite <- (firstn_skipn (Z.to_nat k) sl) in B.
    replace (bs ++ ZERO :: firstn (Z.to_nat k) sl ++ skipn (Z.to_nat k) sl)
      with ((bs ++ ZERO :: firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl) in B
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in B. exact (proj1 B).
  - unfold apart, cstr_span in A1, A2. fold k in A1, A2. rewrite LF. split; [lia|]. split; [exact Hr|]. split; lia.
Qed.

Lemma pf1_cstr_bytes : forall m a L, cstr_at rsegs m a L -> Forall (fun x => 0 < x < 256) L /\ ~ In 0 L.
Proof.
  intros m a L (bs & sl & _ & Hz & Hn & _). split; [|exact Hn].
  apply Forall_forall. intros x Hx. pose proof (pf1_zs_range bs) as R. rewrite Forall_forall in R.
  unfold zs in Hz. rewrite <- Hz in Hx. specialize (R x Hx). split; [|lia].
  destruct (Z.eq_dec x 0) as [->|]; [|lia]. exfalso. apply Hn. rewrite <- Hz. exact Hx.
Qed.

(** ** P1's exit DONE (0x1550c): c->n through the slot sp + 0x30, the restores, `ret`. *)
Lemma pf1_done : H_DONE.
Proof.
  unfold H_DONE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v c rc
    ENV RC SLOT.
  pose proof ENV as (C0 & C16 & APc & NI & PE & CAT & STK & MI & SV).
  destruct PE as (FRM & TM & SSP & IL & SPH). destruct STK as (ST & DEP & SP16 & NR).
  destruct v as [vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11].
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2 ^ 64) in Rsp.
  pose proof (Z_to_bv_bv_unsigned sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in DEP, SPH, ST, NR.
  unfold PF_NSLOT in SLOT. unfold PF_SAVE in SV. unfold apart, SEG_C_SIZE in APc.
  pose proof RC as (bs & BC & HE).
  pose proof (bytes_at_bound _ _ _ _ BC) as BBc. destruct (sq_rconf_len rc bs HE) as [HLb HLs].
  pose proof (sq_rc_n rsegs m c bs rc BC HE) as RN. unfold RC_N in RN.
  assert (RO1 : ro_cells rsegs m (Sp + 48) [C8 (Z_to_bv 64 (c + 11392))]).
  { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact SLOT. }
  assert (RO2 : ro_cells rsegs m (Sp + 872)
                  [C8 vs11; C8 vs10; C8 vs9; C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1;
                   C8 vs0; C8 vra]).
  { split; [cbn; tauto|]. exact SV. }
  clear SLOT SV BC.
  (* 0x1550c ld a0, 0x30(sp); 0x15510 lw a0, 0(a0): c->n *)
  zstep. zstep.
  rewrite sq_sx32 by lia.
  (* 0x15514 j; the 13 restores; addi sp; ret *)
  do 16 zstep.
  apply evt_done. unfold pf_ret, ret_post_fp.
  rewrite unsigned_lit by lia.
  do 17 eexists.
  split; [reflexivity|].
  split; [exact FRM|]. split; [intros k Hk; reflexivity|]. split; [apply munch_refl|].
  split; [apply wmono_refl|]. split; [exact MI|]. split; [exact TM|].
  split; [unfold PARSE_FILE_FRAME; rewrite unsigned_lit by lia; exact ST|]. exact RC.
Qed.

(** ** ENTRY (0x14cbc) to HEAD or DONE *)
Section Entry.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo Sp c t lp : Z) (rc : rconf) (s : list Z) (lab : option (list Z)).
Hypothesis HSN : snprintf_contract.
Hypothesis HHEAD : forall n, H_HEAD n.
Hypothesis HDONE : H_DONE.
Hypothesis HPRE : reac_segconf_parse_file_pre m0 fc Sp lo c t lp rc s lab.
Hypothesis HSp : 0 <= Sp < 2 ^ 64.
Hypothesis Hc : 0 <= c < 2 ^ 64.
Hypothesis Ht : 0 <= t < 2 ^ 64.
Hypothesis Hlp : 0 <= lp < 2 ^ 64.

Definition pf1_v : pf_sv := PFSv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
Definition pf1_lab : list Z := match lab with Some l => l | None => S_base end.
(** Every byte the function writes: the contract's W with the numbers. *)
Definition pf1_W : list ivl := [(Sp - 7008, Sp); (c, c + 11396); (c + 11912, c + 13524); (c + 16512, c + 16612)].
Definition pf1_post : machine_state -> Prop :=
  ret_post_fp ra (Z_to_bv 64 Sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (snd (r_parse_file rc s lab)) m0
    ((Sp - PARSE_FILE_STACK, Sp) :: RC_PARSE_W c) lo (fun m' => rconf_at rsegs m' c (fst (r_parse_file rc s lab))).

Ltac pf1_nums :=
  pose proof HPRE as ((PC0 & PC16 & PRC & PAPc & PNI & PG1 & PR1 & PO1 & PT0 & PCS & PLS & PAPt & PAPtc & PPE &
                       PCAT & PSTK & PMI) & POL & PLB);
  pose proof PPE as (PFRM & PTM & PSSP & PIL & PSPH);
  pose proof PSTK as (PST & PDEP & PSP16 & PNR);
  unfold SA, SEG_PLAIN in PIL; cbn [sa_img_end] in PIL;
  unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in PDEP;
  unfold apart, SEG_C_SIZE in PAPc, PAPt, PAPtc;
  pose proof PRC as (pbs & PBC & PHE);
  pose proof (bytes_at_bound _ _ _ _ PBC) as PBBc;
  destruct (sq_rconf_len rc pbs PHE) as [PHL PHLs];
  pose proof (proj1 PST) as PLO0.

(** The cuts' post, relative to a cut's memory, F and fc, gives the contract's post. *)
Lemma pf1_weaken : forall mk Fk rcf ms',
  munch pf1_W m0 mk -> wmono rsegs m0 mk -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Fk k = reg_get F k) ->
  rcf = fst (r_parse_file rc s lab) ->
  pf_ret pf1_v (Z_to_bv 64 (Sp + -976)) gp tp Fk mk lo c rcf ms' -> pf1_post ms'.
Proof.
  intros mk Fk rcf ms' MU WM FF Hr PO.
  pf1_nums.
  unfold pf_ret, ret_post_fp in PO. rewrite unsigned_lit in PO by lia.
  replace (Sp + -976 + PARSE_FILE_FRAME) with Sp in PO by (unfold PARSE_FILE_FRAME; lia).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' &
                  E & FRM & FF' & MU' & WM' & MI' & TM' & ST' & Q).
  unfold pf1_post, ret_post_fp.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m'.
  split; [rewrite E, (pf1_rpf_snd rc s lab), <- Hr; reflexivity|].
  split; [exact FRM|].
  split; [intros k Hk; rewrite (FF' k Hk); exact (FF k Hk)|].
  split.
  { apply (munch_trans _ m0 mk m'); [|exact MU'].
    apply (munch_weaken pf1_W); [|exact MU].
    unfold sub_fp, pf1_W, RC_PARSE_W, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K, RC_N, RC_REFUSAL,
      RC_OVERFLOW, RC_READING, RC_GEN.
    intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & H4 & _).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact MI'|]. split; [exact TM'|].
  split; [rewrite unsigned_lit in ST' by lia; rewrite unsigned_lit by lia; exact ST'|].
  rewrite Hr in Q. exact Q.
Qed.

(** Every byte the function may write was present at the entry (the stack region and c's block). *)
Lemma pf1_pres : forall x : word, ~ outside pf1_W (bv_unsigned x) -> mrd rsegs m0 x <> None.
Proof.
  intros x Hx. pf1_nums. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
  assert (E : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_bv_unsigned).
  unfold pf1_W in Hx. cbn [outside] in Hx.
  assert (CR : (Sp - 7008 <= bv_unsigned x < Sp) \/ (c <= bv_unsigned x < c + 16616)).
  { destruct (Z_le_dec (Sp - 7008) (bv_unsigned x)); destruct (Z_lt_dec (bv_unsigned x) Sp);
      destruct (Z_le_dec c (bv_unsigned x)); destruct (Z_lt_dec (bv_unsigned x) (c + 16616));
      try (left; lia); try (right; lia); exfalso; apply Hx; repeat split; lia. }
  destruct CR as [H1|H1].
  - destruct PST as (_ & _ & STa). destruct (STa (bv_unsigned x) ltac:(lia)) as [_ (b & Hb)].
    rewrite E in Hb. rewrite Hb. discriminate.
  - destruct PBC as (_ & _ & Bb). rewrite <- E.
    replace (bv_unsigned x) with (c + Z.of_nat (Z.to_nat (bv_unsigned x - c))) by lia.
    rewrite Bb by lia. intros C. apply nth_error_None in C. lia.
Qed.

(** A range of a reserved segment below the stack region is apart from every range of W. *)
Lemma pf1_dj_img : forall B Sz p k, In (B, Sz) PF1_RES -> B <= p -> p + k <= B + Sz -> 0 < k ->
  p + k <= 341736 -> disjoint_from pf1_W p k.
Proof.
  intros B Sz p k Hin H1 H2 Hk Hp. pf1_nums. unfold pf1_W. cbn [disjoint_from].
  pose proof (pf1_noimg_disj c 16616 B Sz p k c 11396 PNI Hin H1 H2 Hk ltac:(lia) ltac:(lia) ltac:(lia)) as D1.
  pose proof (pf1_noimg_disj c 16616 B Sz p k (c + 11912) 1612 PNI Hin H1 H2 Hk ltac:(lia) ltac:(lia) ltac:(lia))
    as D2.
  pose proof (pf1_noimg_disj c 16616 B Sz p k (c + 16512) 100 PNI Hin H1 H2 Hk ltac:(lia) ltac:(lia) ltac:(lia))
    as D3.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(** pf_env at a cut whose writes are in W, with the frame back in the stack region. *)
Lemma pf1_env : forall m fc2, saved_at rsegs m (Sp + -976 + PF_SAVE) (sv_list pf1_v) -> stk rsegs m lo Sp ->
  munch pf1_W m0 m -> mem_inv rsegs m -> frm0 fc2 -> pf_env m fc2 (Sp + -976) lo c pf1_v.
Proof.
  intros m fc2 SV ST MU MI FRM. pf1_nums.
  unfold pf_env. replace (Sp + -976 + PARSE_FILE_FRAME) with Sp by (unfold PARSE_FILE_FRAME; lia).
  split; [exact PC0|]. split; [exact PC16|]. split; [unfold apart, SEG_C_SIZE; exact PAPc|]. split; [exact PNI|].
  split.
  { split; [exact FRM|]. split; [exact (pf1_task_mem_munch _ m0 m PTM MU pf1_pres)|].
    split.
    - apply (pf1_ssp_munch _ m0 m PSSP MU).
      + apply (pf1_dj_img 0x20000 0x2000); [unfold PF1_RES; cbn [In]; right; right; left; reflexivity | lia..].
      + apply (pf1_dj_img 0x22000 0x32000);
          [unfold PF1_RES; cbn [In]; right; right; right; left; reflexivity | lia..].
    - split; [unfold SA, SEG_PLAIN; cbn [sa_img_end]; lia | exact PSPH]. }
  split.
  { apply (pf1_cat_munch _ m0 m PCAT MU). unfold CAT_BYTES.
    apply (pf1_dj_img 0x20000 0x2000); [unfold PF1_RES; cbn [In]; right; right; left; reflexivity | lia..]. }
  split.
  { split; [exact ST|]. split; [unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K; lia|].
    split; [exact PSP16 | exact PNR]. }
  split; [exact MI | exact SV].
Qed.

(** pf_text at a cut whose writes are in W. *)
Lemma pf1_text : forall m, munch pf1_W m0 m -> pf_text m (Sp + -976) lo c t s.
Proof.
  intros m MU. pf1_nums. unfold pf_text. replace (Sp + -976 + PARSE_FILE_FRAME) with Sp by (unfold PARSE_FILE_FRAME; lia).
  split; [exact PT0|]. split.
  - eapply pf1_cstr_munch; [exact PCS | exact MU |]. pose proof (pf1_span t s). unfold pf1_W. cbn [disjoint_from].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
  - split; [exact PLS|]. split; [unfold apart; exact PAPt|]. unfold apart, SEG_C_SIZE. exact PAPtc.
Qed.

(** From 0x14d40, after snprintf: c->gen++, the text test, the slots, cur_name, then DONE or HEAD. *)
Lemma pf1_after : forall (m2 : word -> option byte) (Ft : bvmap 5 word) (fc2 : bv 32) (j : list byte)
    (P' G Q : list byte) (t0 t1 t2 x10 x11 x12 x13 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rw_cells rsegs m2 (Sp + -976)
    [CB 872 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m2 lo (Sp + -976) -> munch pf1_W m0 m2 -> wmono rsegs m0 m2 -> mem_inv rsegs m2 -> frm0 fc2 ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
  bytes_at rsegs m2 c P' -> bytes_at rsegs m2 (c + 16608) G -> bytes_at rsegs m2 (c + 16612) Q ->
  Z.of_nat (length P') = 16608 -> length G = 4%nat -> length Q = 4%nat ->
  G = le4 (Z_to_bv 64 (rc_gen rc)) ->
  rconf_enc (RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc) (snprintf_s 96 F_s [AS pf1_lab])
               (rc_gen rc)) (P' ++ G ++ Q) ->
  evt rsegs pf1_post
    (MS (mkR (Z_to_bv 64 0x14d40) (Z_to_bv 64 (Sp + -976)) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 12288) x10 x11
             x12 x13 a4 a5 a6 a7 (Z_to_bv 64 t) (Z_to_bv 64 (c + 16608)) (Z_to_bv 64 (c + 16512))
             (Z_to_bv 64 (c + 11392)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Ft (Z_to_bv 64 0x14d40) fc2 None m2 (seg_rom rsegs)).
Proof.
  intros m2 Ft fc2 j P' G Q t0 t1 t2 x10 x11 x12 x13 a4 a5 a6 a7 t3 t4 t5 t6 FR ST MU WM MI FRM FF BP BG BQ
    LP' LG LQ EG ENC.
  pf1_nums.
  assert (WC : wr_at rsegs m2 c 16616).
  { apply (wr_at_transport rsegs m0 m2 c 16616); [|exact WM].
    pose proof (pf1_wr_at_block m0 c pbs PBC) as W0. rewrite PHL in W0. apply W0. exact PNI. }
  clear PBC PST.
  unfold pf1_W in MU.
  assert (RD : ov_read_bytes rsegs m2 (wa (c + 16608)) 4 = Some (le4 (Z_to_bv 64 (rc_gen rc)))).
  { rewrite <- EG. pose proof (pf1_read_all m2 _ G BG) as R. rewrite LG in R. exact R. }
  assert (Hg : 0 <= rc_gen rc < 2 ^ 32).
  { destruct ENC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG). cbn [rc_gen] in HG. exact (proj1 HG). }
  (* 0x14d40 lw a0, 0(s3); addi a0, a0, 1; 0x14d48 sw a0, 0(s3): c->gen++ *)
  zstep. zstep.
  pose proof (wr_at_store_ok rsegs m2 c 16616 16608 4 WC ltac:(lia) ltac:(lia)) as SO.
  clear RD BG.
  step.
  pose proof (bytes_at_write_same rsegs m2 (c + 16608)
                (le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 (rc_gen rc))) + 1))) ltac:(lia)
                ltac:(rewrite length_le4; lia)) as BG3.
  rewrite (pf1_le4_inc (rc_gen rc)) in BG3 |- * by lia.
  store_done.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  assert (RC3 : rconf_at rsegs m3 c (pf_start rc lab)).
  { exists (P' ++ le4 (Z_to_bv 64 (rc_gen rc + 1)) ++ Q). split.
    - apply bytes_at_app. split; [exact BP|]. apply bytes_at_app. rewrite length_le4. split.
      + replace (c + Z.of_nat (length P')) with (c + 16608) by lia. exact BG3.
      + replace (c + Z.of_nat (length P') + Z.of_nat 4) with (c + 16612) by lia. exact BQ.
    - exact (pf1_enc_gen _ P' G Q ENC LP' LG LQ PG1). }
  clear BP BG3 BQ ENC.
  pose proof (munch_refl [(Sp + -976, Sp)] m3) as MU3.
  (* 0x14d4c beqz s2: the text is not NULL *)
  zstep. rewrite ?sq_eqb_lit by lia. if_false.
  (* 0x14d50 .. 0x14d58: the slots sp + 0x30, 0x28, 0x20 *)
  do 3 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
  assert (CS4 : cstr_at rsegs m4 t s).
  { eapply pf1_cstr_munch; [exact PCS | exact MU |]. pose proof (pf1_span t s). cbn [disjoint_from].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  destruct (pf1_byte0 m4 t s CS4) as (RB & HB0 & HBs). clear CS4.
  (* 0x14d5c lbu a0, 0(s2); 0x14d60 / 0x14d64 cur_name = 16 zero bytes; 0x14d68 beqz a0 *)
  zstep. clear RB. zstep. zstep.
  zstep. rewrite ?pf1_u8 by lia. rewrite ?sq_eqb_lit by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
  destruct (Z.eqb_spec (hd0 s) 0) as [H0 | H0]; cbv iota.
  - (* the text is empty: DONE *)
    assert (Es : s = []) by (apply HBs; exact H0).
    pose proof (stk_release rsegs m5 lo _ _ ST FR ltac:(lia)) as STS.
    cbn [cells_size csize Nat.add] in STS. replace (Sp + -976 + Z.of_nat 976) with Sp in STS by lia.
    assert (SV : saved_at rsegs m5 (Sp + -976 + PF_SAVE) (sv_list pf1_v)).
    { unfold saved_at. eapply (pf1_rw_sub _ _ _ 7 13);
        [exact FR | cbn [firstn cells_size csize Nat.add]; unfold PF_SAVE; lia | reflexivity]. }
    assert (SL : bytes_at rsegs m5 (Sp + -976 + PF_NSLOT) (le8 (Z_to_bv 64 (c + RC_N)))).
    { eapply (pf1_rw_sub _ _ _ 3 1); [exact FR | cbn [firstn cells_size csize Nat.add]; unfold PF_NSLOT; lia |].
      cbn [firstn skipn cells_bytes cbytes]. rewrite app_nil_r. reflexivity. }
    assert (RC5 : rconf_at rsegs m5 c (pf_start rc lab)).
    { apply (pf1_rconf_munch _ m3 m5 _ _ RC3 MU3). cbn [disjoint_from]. unfold SEG_C_SIZE. split; [lia | exact I]. }
    pose proof (pf1_env m5 fc2 SV STS MU MI FRM) as ENV.
    pose proof HDONE as HD. unfold H_DONE in HD.
    eapply evt_mono.
    { eapply HD with (lo := lo) (v := pf1_v) (c := c) (rc := pf_start rc lab); rewrite ?unsigned_lit by lia;
        [exact ENV | exact RC5 | exact SL]. }
    intros ms' HP. eapply pf1_weaken; [exact MU | exact WM | exact FF | | exact HP].
    rewrite Es, L_parse_start_holds. reflexivity.
  - (* a first line: HEAD *)
    assert (Hs : (0 < length s)%nat).
    { destruct (Nat.eq_dec (length s) 0) as [E|E]; [apply length_zero_iff_nil in E; exfalso; apply H0, HBs, E | lia]. }
    (* 0x14d6c .. 0x14dc0: the loop constants and the slots sp + 8, 0x40, 0x38, 0x18, 0x10 *)
    do 22 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m6 end.
    pose proof (stk_release rsegs m6 lo _ _ ST FR ltac:(lia)) as STS.
    cbn [cells_size csize Nat.add] in STS. replace (Sp + -976 + Z.of_nat 976) with Sp in STS by lia.
    assert (SV : saved_at rsegs m6 (Sp + -976 + PF_SAVE) (sv_list pf1_v)).
    { unfold saved_at. eapply (pf1_rw_sub _ _ _ 12 13);
        [exact FR | cbn [firstn cells_size csize Nat.add]; unfold PF_SAVE; lia | reflexivity]. }
    assert (SP8 : pf_spill m6 (Sp + -976) c).
    { unfold pf_spill, saved_at. eapply (pf1_rw_sub _ _ _ 1 8);
        [exact FR | cbn [firstn cells_size csize Nat.add]; lia | reflexivity]. }
    assert (NM : pf_nm_at m6 (Sp + -976 + PF_NAMEBUF) []).
    { apply pf1_nm0. eapply (pf1_rw_sub _ _ _ 10 2);
        [exact FR | cbn [firstn cells_size csize Nat.add]; unfold PF_NAMEBUF; lia | reflexivity]. }
    assert (RC6 : rconf_at rsegs m6 c (pf_start rc lab)).
    { apply (pf1_rconf_munch _ m3 m6 _ _ RC3 MU3). cbn [disjoint_from]. unfold SEG_C_SIZE. split; [lia | exact I]. }
    assert (CS6 : cstr_at rsegs m6 t s).
    { eapply pf1_cstr_munch; [exact PCS | exact MU |]. pose proof (pf1_span t s). cbn [disjoint_from].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    pose proof (pf1_env m6 fc2 SV STS MU MI FRM) as ENV.
    pose proof (pf1_text m6 MU) as TXT.
    pose proof (HHEAD (length s)) as HH. unfold H_HEAD in HH.
    eapply evt_mono.
    { eapply HH with (lo := lo) (v := pf1_v) (c := c) (t := t) (s := s) (rc := pf_start rc lab) (cur := None)
        (nm := []) (o := 0%nat) (ln := 0) (d := []); rewrite ?unsigned_lit by lia.
      - split; [exact ENV|]. split; [exact TXT|]. split; [exact SP8|]. split; [exact (pf_lctx_start s)|].
        change (skipn 0 s) with s. replace (t + Z.of_nat 0) with t by lia. exact CS6.
      - split; [exact RC6|]. split; [exact I|]. split; [exact NM|].
        apply pf_cnt_start; [exact PR1 | exact PO1 | change (skipn 0 s) with s; first [exact PLS | lia]].
      - exact Hs.
      - change (skipn 0 s) with s. lia.
      - unfold pf_regs. repeat split; first [reflexivity | f_equal; lia].
      - reflexivity.
      - reflexivity. }
    intros ms' HP. eapply pf1_weaken; [exact MU | exact WM | exact FF | | exact HP].
    rewrite L_parse_start_holds. reflexivity.
Qed.

(** At 0x14d28, the label in a3: s5 = &c->n, then snprintf(c->reading, 96, "%s", label). *)
Lemma pf1_call : forall (m1 : word -> option byte) (j : list byte) (LP : Z)
    (t0 t1 t2 x11 x12 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  rw_cells rsegs m1 (Sp + -976)
    [CB 872 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo (Sp + -976) -> munch [(Sp + -976, Sp)] m0 m1 -> wmono rsegs m0 m1 -> mem_inv rsegs m1 ->
  0 < LP < 2 ^ 64 -> cstr_at rsegs m1 LP pf1_lab -> (length pf1_lab <= 65535)%nat ->
  apart LP (cstr_span LP pf1_lab) lo Sp -> apart LP (cstr_span LP pf1_lab) (c + 16512) (c + 16608) ->
  evt rsegs pf1_post
    (MS (mkR ra (Z_to_bv 64 (Sp + -976)) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 12288) (Z_to_bv 64 11392) x11 x12
             (Z_to_bv 64 LP) a4 a5 a6 a7 (Z_to_bv 64 t) (Z_to_bv 64 (c + 16608)) (Z_to_bv 64 (c + 16512))
             s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14d28) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 j LP t0 t1 t2 x11 x12 a4 a5 a6 a7 t3 t4 t5 t6 FR ST MUF WM MI HLP HL HLL A1 A2.
  pf1_nums.
  assert (Hcb : c + 16616 <= 2 ^ 64) by lia.
  assert (WC : wr_at rsegs m1 c 16616).
  { apply (wr_at_transport rsegs m0 m1 c 16616); [|exact WM].
    pose proof (pf1_wr_at_block m0 c pbs PBC) as W0. rewrite PHL in W0. apply W0. exact PNI. }
  (* printf's machine at the call: the frame's bytes were present at the entry *)
  assert (PRES : forall x : word, ~ outside [(Sp + -976, Sp)] (bv_unsigned x) -> mrd rsegs m0 x <> None).
  { intros x Hx. apply pf1_pres. intros Ho. apply Hx. unfold pf1_W in Ho. cbn [outside] in Ho |- *.
    destruct Ho as (H1 & _). split; [lia | exact I]. }
  assert (TM1 : MemNorm.task_mem rsegs m1) by exact (pf1_task_mem_munch _ m0 m1 PTM MUF PRES).
  assert (SSP1 : ssp_ok m1).
  { apply (pf1_ssp_munch _ m0 m1 PSSP MUF); cbn [disjoint_from]; (split; [lia | exact I]). }
  destruct SSP1 as [G1 (g & G2)]. unfold SA, SEG_PLAIN in G1, G2. cbn [sa_got_guard sa_guard] in G1, G2.
  (* c's bytes: P (16512), the reading field R (96), gen GG (4), the tail Q (4) *)
  destruct (pf1_app_split pbs (Z.to_nat 16512)) as (P & T1 & EQ1 & LP1); [lia|]. subst pbs.
  rewrite length_app in PHL.
  destruct (pf1_app_split T1 96) as (R & T2 & EQ2 & LR); [lia|]. subst T1.
  rewrite length_app in PHL.
  destruct (pf1_app_split T2 4) as (GG & Q & EQ3 & LG); [lia|]. subst T2.
  rewrite length_app in PHL.
  assert (LQ : length Q = 4%nat) by lia.
  assert (LPl : Z.of_nat (length P) = 16512) by lia.
  assert (EG : GG = le4 (Z_to_bv 64 (rc_gen rc))).
  { pose proof PHE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG). unfold fldz, RC_GEN in HG.
    rewrite (pf1_fld_gen P R GG Q LPl LR LG) in HG. exact (proj2 HG). }
  apply bytes_at_app in PBC as [BP BT]. rewrite LPl in BT.
  apply bytes_at_app in BT as [BR BT]. rewrite LR in BT.
  apply bytes_at_app in BT as [BG BQ]. rewrite LG in BQ.
  replace (c + 16512 + Z.of_nat 96) with (c + 16608) in BG, BQ by lia.
  replace (c + 16608 + Z.of_nat 4) with (c + 16612) in BQ by lia.
  assert (DJF : forall a n, 0 <= n -> (a + n <= lo \/ Sp <= a) -> disjoint_from [(Sp + -976, Sp)] a n).
  { intros a n Hn H. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (BP1 : bytes_at rsegs m1 c P)
    by (apply (bytes_at_transport rsegs _ m0 m1 _ _ BP MUF); apply DJF; lia).
  assert (BR1 : bytes_at rsegs m1 (c + 16512) R)
    by (apply (bytes_at_transport rsegs _ m0 m1 _ _ BR MUF); apply DJF; lia).
  assert (BG1 : bytes_at rsegs m1 (c + 16608) GG)
    by (apply (bytes_at_transport rsegs _ m0 m1 _ _ BG MUF); apply DJF; lia).
  assert (BQ1 : bytes_at rsegs m1 (c + 16612) Q)
    by (apply (bytes_at_transport rsegs _ m0 m1 _ _ BQ MUF); apply DJF; lia).
  clear BP BR BG BQ DJF.
  destruct (stk_split rsegs m1 lo (Sp - 7008) (Sp + -976) ST ltac:(lia)) as [STlo STf].
  destruct (pf1_cstr_bytes m1 LP pf1_lab HL) as [HLb HLn].
  (* 0x14d28 add s5; auipc a0; addi a2; li a1, 0x60; mv a0, s4; 0x14d3c jal snprintf *)
  do 6 zstep.
  eapply evt_cut.
  { eapply HSN with (lo := Sp - 7008) (canary := g) (fmt := [37; 115]) (ps := [Ps]) (args := [APtr pf1_lab])
      (T := pf1_lab ++ []) (junk := R); rewrite ?unsigned_lit by lia.
    - apply pf1_fmt_at; [exact MI | reflexivity].
    - unfold snprintf_c.RO_LO; lia.
    - unfold RO_END; cbn [length]; lia.
    - reflexivity.
    - cbn [pf_args_ok pf_arg_ok]. rewrite ?unsigned_lit by lia. split; [split; [exact HLb|] | exact I].
      apply pf1_arg_ptr; [exact HL | lia | | ]; unfold apart in *; pose proof (pf1_span LP pf1_lab); lia.
    - reflexivity.
    - split; [split; [cbn; split; [exact LR | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BR1] |].
      cbn [cells_size csize]. apply (pf1_wr_at_sub m1 c 16616); [exact WC | lia | lia | lia].
    - lia.
    - pose proof (pf1_le65535 _ HLL). rewrite app_nil_r. lia.
    - lia.
    - lia.
    - exact (pf1_noimg_sub c 16616 (c + 16512) 96 PNI ltac:(lia) ltac:(lia)).
    - exact STf.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - lia.
    - exact PFRM.
    - exact MI.
    - exact TM1.
    - exact G1.
    - exact G2. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc2 & m2 &
                  E & MU2 & WM2 & MI2 & TM2 & FRM2 & FF2 & ST2 & BT).
  subst ms'.
  rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in BT by lia.
  replace (ret_pc (Z_to_bv 64 85312)) with (Z_to_bv 64 85312) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite <- (pf1_reading pf1_lab HLn) in MU2, BT.
  set (Tw := snprintf_s 96 F_s [AS pf1_lab]) in *.
  assert (LTw : (length Tw < 96)%nat).
  { unfold Tw. rewrite pf1_reading by exact HLn. rewrite length_firstn. lia. }
  assert (NTw : ~ In 0 Tw).
  { unfold Tw. rewrite pf1_reading by exact HLn. intros Hin. apply HLn. rewrite app_nil_r in Hin.
    exact (pf1_in_firstn _ _ _ Hin). }
  assert (BTw : Forall (fun x => 0 <= x < 256) Tw).
  { unfold Tw. rewrite pf1_reading by exact HLn. apply pf1_Forall_firstn. rewrite app_nil_r.
    eapply Forall_impl; [|exact HLb]. intros x Hx. cbv beta in Hx |- *. lia. }
  assert (BRt : bytes_at rsegs m1 (c + 16512 + Z.of_nat (S (length Tw))) (skipn (S (length Tw)) R)).
  { rewrite <- (firstn_skipn (S (length Tw)) R) in BR1. apply bytes_at_app in BR1 as [_ B].
    rewrite length_firstn, Nat.min_l in B by lia. exact B. }
  assert (DJ2 : forall a n, 0 <= n -> (a + n <= Sp - 7008 \/ Sp + -976 <= a) ->
    (a + n <= c + 16512 \/ c + 16512 + Z.of_nat (length Tw) + 1 <= a) ->
    disjoint_from [(Sp - 7008, Sp + -976); (c + 16512, c + 16512 + Z.of_nat (length Tw) + 1)] a n).
  { intros a n Hn H1 H2. cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
  assert (BP2 : bytes_at rsegs m2 c P)
    by (apply (bytes_at_transport rsegs _ m1 m2 _ _ BP1 MU2); apply DJ2; lia).
  assert (BRt2 : bytes_at rsegs m2 (c + 16512 + Z.of_nat (S (length Tw))) (skipn (S (length Tw)) R))
    by (apply (bytes_at_transport rsegs _ m1 m2 _ _ BRt MU2); apply DJ2; rewrite ?length_skipn; lia).
  assert (BG2 : bytes_at rsegs m2 (c + 16608) GG)
    by (apply (bytes_at_transport rsegs _ m1 m2 _ _ BG1 MU2); apply DJ2; lia).
  assert (BQ2 : bytes_at rsegs m2 (c + 16612) Q)
    by (apply (bytes_at_transport rsegs _ m1 m2 _ _ BQ1 MU2); apply DJ2; lia).
  assert (FR2 : rw_cells rsegs m2 (Sp + -976)
    [CB 872 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2). cbn [cells_size csize Nat.add]. apply DJ2; lia. }
  assert (STlo2 : stk rsegs m2 lo (Sp - 7008)).
  { apply (stk_transport_disjoint rsegs _ m1 m2 lo (Sp - 7008) STlo MU2 WM2). apply DJ2; lia. }
  pose proof (stk_merge rsegs m2 lo (Sp - 7008) (Sp + -976) STlo2 ST2 ltac:(lia)) as ST3.
  assert (MU02 : munch pf1_W m0 m2).
  { apply (munch_trans pf1_W m0 m1 m2).
    - apply (munch_weaken [(Sp + -976, Sp)] pf1_W); [|exact MUF]. unfold sub_fp, pf1_W. intros x Hx.
      cbn [outside] in Hx |- *. destruct Hx as (H1 & _). split; [lia | exact I].
    - eapply (munch_weaken _ pf1_W m1 m2); [|exact MU2]. unfold sub_fp, pf1_W. intros x Hx. cbn [outside] in Hx |- *.
      destruct Hx as (H1 & H2 & H3 & H4 & _). split; [lia|]. split; [lia | exact I]. }
  set (X := pf_bytes (Tw ++ [0]) ++ skipn (S (length Tw)) R).
  assert (LX : length X = 96%nat).
  { unfold X, pf_bytes. rewrite length_app, length_map, length_app, length_skipn. cbn [length]. lia. }
  assert (BPX : bytes_at rsegs m2 c (P ++ X)).
  { apply bytes_at_app. split; [exact BP2|]. rewrite LPl. unfold X. apply bytes_at_app. split; [exact BT|].
    replace (c + 16512 + Z.of_nat (length (pf_bytes (Tw ++ [0])))) with (c + 16512 + Z.of_nat (S (length Tw)))
      by (unfold pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
    exact BRt2. }
  pose proof (pf1_enc_reading rc P R GG Q Tw PHE LPl LR LG LQ LTw NTw BTw) as ENC. fold X in ENC.
  eapply (pf1_after m2 Ft fc2 j (P ++ X) GG Q);
    [exact FR2 | exact ST3 | exact MU02 | exact (wmono_trans rsegs _ _ _ WM WM2) | exact MI2 | exact FRM2 | exact FF2 |
     exact BPX | exact BG2 | exact BQ2 | rewrite length_app; lia | exact LG | exact LQ | exact EG | exact ENC].
Qed.

Lemma pf1_body : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs pf1_post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 t) (Z_to_bv 64 lp) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_SEGCONF_PARSE_FILE) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6. unfold REAC_SEGCONF_PARSE_FILE.
  pf1_nums.
  pose proof (munch_refl [(Sp + -976, Sp)] m0) as MUF. pose proof (wmono_refl rsegs m0) as WM.
  pose proof PST as ST. pose proof PMI as MI.
  clear PBC PST PMI.
  (* 0x14cbc addi sp, sp, -0x3d0; the 13 saves; 0x14cf4 .. 0x14d1c: a3, s2, s0, s1, s3, s4, a0, bnez a3 *)
  zstep. carve_frame 976%nat ST.
  do 13 zstep.
  do 11 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  rewrite sq_eqb_lit by lia.
  destruct (pf1_lab_cases lab) as [(l & El) | El].
  - (* a label: bnez a3 taken, a3 = the label *)
    pose proof POL as OL. rewrite El in OL. destruct OL as [Hlp0 HLc].
    pose proof PLB as LB. rewrite El in LB. destruct LB as (LL & AL1 & AL2).
    replace (lp =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hlp0). cbn [negb]. cbv iota.
    assert (EL : pf1_lab = l) by (unfold pf1_lab; rewrite El; reflexivity).
    eapply (pf1_call m1 _ lp); [exact FR | exact ST | exact MUF | exact WM | exact MI | lia | | | |]; rewrite EL.
    + eapply pf1_cstr_munch; [exact HLc | exact MUF |]. pose proof (pf1_span lp l). unfold apart in AL1.
      cbn [disjoint_from]. split; [lia | exact I].
    + exact LL.
    + pose proof (pf1_span lp l). unfold apart in *. lia.
    + pose proof (pf1_span lp l). unfold apart, RC_READING in *. lia.
  - (* no label: 0x14d20 auipc a1; addi a3 = "reac-pw.conf" *)
    pose proof POL as OL. rewrite El in OL. cbn [ocstr_at] in OL.
    rewrite OL. cbn [Z.eqb negb]. cbv iota.
    zstep. zstep.
    assert (EL : pf1_lab = S_base) by (unfold pf1_lab; rewrite El; reflexivity).
    eapply (pf1_call m1 _ STR_BASE);
      [exact FR | exact ST | exact MUF | exact WM | exact MI | unfold STR_BASE; lia | | | |]; rewrite EL.
    + exact (pf1_label_at m1 MI).
    + rewrite pf1_label_len. apply Nat.leb_le. reflexivity.
    + rewrite pf1_label_span. unfold apart, STR_BASE. lia.
    + rewrite pf1_label_span. unfold apart.
      pose proof (pf1_noimg_disj c 16616 0x10000 0x3000 STR_BASE 13 (c + 16512) 96 PNI
                    ltac:(unfold PF1_RES; cbn [In]; left; reflexivity) ltac:(unfold STR_BASE; lia)
                    ltac:(unfold STR_BASE; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as D.
      lia.
Qed.

End Entry.

(** ** The piece *)
Theorem pf_p1_holds : snprintf_contract -> S_P1.
Proof.
  intros HSN. split; [exact pf1_done|].
  intros HHEAD HDONE. unfold H_ENTRY, reac_segconf_parse_file_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo rc s
    lab PRE.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  change (bv_modulus 64) with (2 ^ 64) in Rsp, Ra0, Ra1, Ra2.
  pose proof (Z_to_bv_bv_unsigned sp) as Esp. pose proof (Z_to_bv_bv_unsigned a0) as Ea0.
  pose proof (Z_to_bv_bv_unsigned a1) as Ea1. pose proof (Z_to_bv_bv_unsigned a2) as Ea2.
  set (Sp := bv_unsigned sp) in *. set (c := bv_unsigned a0) in *. set (t := bv_unsigned a1) in *.
  set (lp := bv_unsigned a2) in *.
  rewrite <- Esp, <- Ea0, <- Ea1, <- Ea2. clearbody Sp c t lp. clear Esp Ea0 Ea1 Ea2.
  eapply pf1_body; eassumption.
Qed.
