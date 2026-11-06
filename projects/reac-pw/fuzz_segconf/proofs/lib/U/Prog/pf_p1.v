(** Piece P1 of reac_segconf_parse_file (UBSan build, image 1696d6c34ffd, function at 0x15248): the entry, the
    setup before the line loop, and the return. Proof of [S_P1] of lib/U/Prog/reac_segconf_parse_file_pieces_c.v
    from [snprintf_contract] (lib/U/Prog/snprintf_c.v, SNPRINTF = 0x19a14). Written new.

    Code (UBSan binary):
      0x15248  addi sp,sp,-0x420; ra at sp+0x418, s0..s11 at sp+0x410 .. 0x3b8; `sd a0,0x90(sp)` (c's slot)
      0x15284  beqz a0 -> unimp 0x15c7c      (reader_pre: c <> 0)
      0x15290  bnez (a0 & 7) -> unimp        (reader_pre: c mod 16 = 0)
      0x152b8  s1 = c + 0x40e0 (&c->gen); 0x152bc s3 = c + 0x4080 (&c->reading)
      0x152c0  bnez a3 -> 0x152cc            (a3 = label, else "reac-pw.conf" at 0x10463)
      0x152d0  s4 = c + 0x2c80 (&c->n); 0x152d8 a2 = "%s" at 0x104e0; a1 = 96; a0 = &c->reading
      0x152e4  jal 0x19a14 snprintf(c->reading, 96, "%s", label ? label : "reac-pw.conf")
      0x152e8  c->gen++                      (lw / addi / sw through s1)
      0x152f4  beqz s2 -> 0x15c3c            (the NULL-text path; the premise gives text <> NULL)
      0x152f8  the spill slots sp+0x58 (&c->n), 0x50 (&c->reading), 0x38 (&c->gen)
      0x15304  lbu a0,0(s2)                  (the text's first byte)
      0x15308  sd zero,0x3a8(sp); 0x1530c sd zero,0x3b0(sp)   (cur_name = "")
      0x15310  beqz a0 -> 0x15c30 DONE       (an empty text: no line)
      0x15314  s3 = 0 (lineno); 0x15318 sd zero,0x88(sp) (cur = NULL); the rest of pf_spill and pf_regs
      0x153a8  HEAD
      0x15c30  DONE: ld a0,0x58(sp); lw a0,0(a0) (c->n); the 13 restores; addi sp,sp,0x420; ret
    In this build the slot sp+0x58 that DONE reads is set at 0x152f8, before the entry test at 0x15310, so both
    paths into DONE have it (the pieces file's H_DONE asks for that slot alone).

    The traps at 0x15284 and 0x15290 fall through by reader_pre (c <> 0, c mod 16 = 0); no other check is in P1.
    The pure facts come from lib/Prog/pfA_facts.v, never as premises of [pf_p1_holds]. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Image Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import
  pin_spec seg_spec seg_query_facts pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import printf_facts_c snprintf_c seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import
  refuse_c reac_segconf_parse_file_c reac_segconf_parse_file_pieces_c.
Import ListNotations.
Open Scope Z_scope.

(** * Generic facts *)

Lemma p1u_Forall_firstn : forall {A} (P : A -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n. induction n as [|n IH]; intros l H; [constructor|].
  destruct l as [|x l]; [constructor|]. inversion H; subst. cbn [firstn]. constructor; auto.
Qed.

Lemma p1u_byte_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Lemma p1u_zs_zb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  unfold zs, zb. induction l as [|x l IH]; intros H; [reflexivity|].
  inversion H as [|? ? Hx Hl]; subst. cbn [map]. f_equal; [apply p1u_byte_lit; exact Hx | exact (IH Hl)].
Qed.

Lemma p1u_zs_app : forall l1 l2, zs (l1 ++ l2) = zs l1 ++ zs l2.
Proof. intros. unfold zs. apply map_app. Qed.
Lemma p1u_length_zb : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma p1u_length_pfb : forall l, length (pf_bytes l) = length l.
Proof. intros. unfold pf_bytes. apply length_map. Qed.

Lemma p1u_app_split : forall {A} (l : list A) k, (k <= length l)%nat ->
  exists l1 l2, l = l1 ++ l2 /\ length l1 = k.
Proof.
  intros A l k H. exists (firstn k l), (skipn k l).
  split; [symmetry; apply firstn_skipn | rewrite length_firstn; lia].
Qed.

Lemma p1u_hd0_nz : forall l : list Z, ~ In 0 l -> (hd0 l = 0 <-> l = []).
Proof.
  intros [|x l] H; cbn [hd0].
  - split; intros _; reflexivity.
  - split; [intros E; exfalso; apply H; left; exact E | intros E; discriminate E].
Qed.

Lemma p1u_disjoint_sub : forall W a n a' n',
  disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; cbn [disjoint_from]; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2)].
Qed.

(** The bytes [off, off + n) of a concatenation. *)
Lemma p1u_fld_app_l : forall (l1 l2 : list byte) off n, (off + n <= length l1)%nat ->
  fld off n (l1 ++ l2) = fld off n l1.
Proof.
  intros l1 l2 off n H. unfold fld. rewrite skipn_app, firstn_app, length_skipn.
  replace (n - (length l1 - off))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
Qed.
Lemma p1u_fld_app_r : forall (l1 l2 : list byte) off n, (length l1 <= off)%nat ->
  fld off n (l1 ++ l2) = fld (off - length l1) n l2.
Proof. intros l1 l2 off n H. unfold fld. rewrite skipn_app, (skipn_all2 l1) by lia. reflexivity. Qed.
Lemma p1u_fld_full : forall (l : list byte) off n, off = 0%nat -> length l = n -> fld off n l = l.
Proof. intros l off n -> <-. unfold fld. rewrite skipn_O. apply firstn_all. Qed.

Ltac p1u_fsimp :=
  repeat first [ rewrite p1u_fld_app_l by (rewrite ?length_app, ?length_le4, ?p1u_length_zb; cbn [length]; lia)
               | rewrite p1u_fld_app_r by (rewrite ?length_app, ?length_le4, ?p1u_length_zb; cbn [length]; lia) ].

Ltac p1u_fmatch H :=
  revert H; p1u_fsimp; intros H;
  try (match type of H with context [fld ?o1 ?n ?L] =>
         match goal with |- context [fld ?o2 n L] =>
           replace o2 with o1 by (rewrite ?length_app, ?length_le4, ?p1u_length_zb; cbn [length]; lia) end end);
  exact H.

Lemma p1u_u32_le4 : forall v, 0 <= v < 2 ^ 32 -> u32_enc v (le4 (Z_to_bv 64 v)).
Proof. intros v H. split; [exact H | reflexivity]. Qed.

(** * The image (UBSan 1696d6c34ffd): the four reserved segments
    The PT_LOADs are [0x10000, 0x1229c), [0x1329c, 0x20430), [0x21430, 0x23000), [0x231c8, 0x54088); page-rounded
    they reserve [0x10000, 0x13000), [0x13000, 0x21000), [0x21000, 0x23000) and [0x23000, 0x55000), which cover
    [0x10000, 0x55000) with no gap. *)

Lemma p1u_res_cover : forall (a k : Z),
  existsb (fun sg : word * word => (bv_unsigned (fst sg) <=? a) &&
            (a + k <=? bv_unsigned (fst sg) + bv_unsigned (snd sg))) (segments_reserved rsegs) = true ->
  forall b n, blk_noimg rsegs b n -> forall i, 0 <= i < n -> ~ (a <= b + i < a + k).
Proof.
  intros a k HE b n HB i Hi Hc.
  apply existsb_exists in HE as (sg & Hin & Hcc). apply andb_true_iff in Hcc as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2.
  exact (HB i Hi sg Hin ltac:(lia)).
Qed.

Lemma p1u_cov_ro : existsb (fun sg : word * word => (bv_unsigned (fst sg) <=? 0x10000) &&
    (0x10000 + 0x3000 <=? bv_unsigned (fst sg) + bv_unsigned (snd sg))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma p1u_cov_tx : existsb (fun sg : word * word => (bv_unsigned (fst sg) <=? 0x13000) &&
    (0x13000 + 0xe000 <=? bv_unsigned (fst sg) + bv_unsigned (snd sg))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma p1u_cov_rw : existsb (fun sg : word * word => (bv_unsigned (fst sg) <=? 0x21000) &&
    (0x21000 + 0x2000 <=? bv_unsigned (fst sg) + bv_unsigned (snd sg))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma p1u_cov_bss : existsb (fun sg : word * word => (bv_unsigned (fst sg) <=? 0x23000) &&
    (0x23000 + 0x32000 <=? bv_unsigned (fst sg) + bv_unsigned (snd sg))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

(** A block that covers no image byte lies wholly outside [0x10000, 0x55000). *)
Lemma p1u_blk_out : forall b n, blk_noimg rsegs b n -> forall i, 0 <= i < n -> ~ (0x10000 <= b + i < 0x55000).
Proof.
  intros b n H i Hi Hc.
  destruct (Z_lt_le_dec (b + i) 0x13000) as [?|?];
    [exact (p1u_res_cover 0x10000 0x3000 p1u_cov_ro b n H i Hi ltac:(lia))|].
  destruct (Z_lt_le_dec (b + i) 0x21000) as [?|?];
    [exact (p1u_res_cover 0x13000 0xe000 p1u_cov_tx b n H i Hi ltac:(lia))|].
  destruct (Z_lt_le_dec (b + i) 0x23000) as [?|?];
    [exact (p1u_res_cover 0x21000 0x2000 p1u_cov_rw b n H i Hi ltac:(lia))|].
  exact (p1u_res_cover 0x23000 0x32000 p1u_cov_bss b n H i Hi ltac:(lia)).
Qed.

(** Hence a range of the block is apart from any range of the image. *)
Lemma p1u_apart_img : forall b n q r p k, blk_noimg rsegs b n ->
  0 < r -> b <= q -> q + r <= b + n -> 0 < k -> 0x10000 <= p -> p + k <= 0x55000 ->
  q + r <= p \/ p + k <= q.
Proof.
  intros b n q r p k HB Hr H1 H2 Hk Hp1 Hp2.
  destruct (Z_le_dec (q + r) p) as [?|?]; [left; lia|].
  destruct (Z_le_dec (p + k) q) as [?|?]; [right; lia|]. exfalso.
  apply (p1u_blk_out b n HB (Z.max p q - b)); lia.
Qed.

Lemma p1u_find_segment_in : forall segs a n sg, find_segment segs a n = Some sg ->
  In sg segs /\ Z.of_N (seg_base sg) <= a /\ a + n <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  induction segs as [|sg0 segs IH]; intros a n sg E; cbn [find_segment] in E; [discriminate|].
  match type of E with context [if ?cnd then _ else _] => destruct cnd eqn:C end.
  - injection E as <-. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    split; [left; reflexivity | lia].
  - destruct (IH a n sg E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Lemma p1u_segs_span : forallb (fun sg => (0x10000 <=? Z.of_N (seg_base sg)) &&
    (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 0x55000)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma p1u_find_none : forall x, ~ (0x10000 <= x < 0x55000) -> find_segment rsegs x 1 = None.
Proof.
  intros x H. destruct (find_segment rsegs x 1) as [sg|] eqn:E; [|reflexivity]. exfalso.
  destruct (p1u_find_segment_in rsegs x 1 sg E) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ _) p1u_segs_span sg Hin) as Hs.
  apply andb_true_iff in Hs as [S1 S2]. apply Z.leb_le in S1. apply Z.leb_le in S2. lia.
Qed.

(** A present byte of such a block is in the overlay, so it is writable. *)
Lemma p1u_wr_block : forall m a bs, bytes_at rsegs m a bs -> blk_noimg rsegs a (Z.of_nat (length bs)) ->
  wr_at rsegs m a (Z.of_nat (length bs)).
Proof.
  intros m a bs HB Hni. pose proof HB as (H0 & H1 & H).
  split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hr : mrd rsegs m (wa (a + i)) <> None).
  { replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. rewrite H by lia.
    intros C. apply nth_error_None in C. lia. }
  unfold mrd in Hr. unfold wview. destruct (m (wa (a + i))) as [b|]; [discriminate|].
  exfalso. apply Hr. apply (MemNorm.seg_rom_unmapped rsegs). apply p1u_find_none.
  unfold wa. rewrite unsigned_lit by lia. exact (p1u_blk_out a _ Hni i Hi).
Qed.

Lemma p1u_wr_at_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) Ha Hn Hl. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma p1u_noimg_sub : forall b N a n, blk_noimg rsegs b N -> b <= a -> a + n <= b + N -> blk_noimg rsegs a n.
Proof.
  intros b N a n H H1 H2 i Hi sg Hs. replace (a + i) with (b + (a - b + i)) by lia. apply H; [lia | exact Hs].
Qed.

Lemma p1u_img_free : forall b N a n, blk_noimg rsegs b N -> b <= a -> a + n <= b + N -> pf_img_free a n.
Proof. intros b N a n H H1 H2. exact (p1u_noimg_sub b N a n H H1 H2). Qed.

(** * Reads and writes of the reader block and the frame *)

Lemma p1u_ld8 : forall m a (v : word), bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. pose proof (length_le8 v) as Lv.
  pose proof (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia) ltac:(lia)) as R.
  replace (a + 0) with a in R by lia.
  rewrite R. first [reflexivity | f_equal; change (Z.to_nat 0) with 0%nat; rewrite skipn_O;
                                  apply firstn_all2; lia].
Qed.

Lemma p1u_ld4 : forall m a (v : word), bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. pose proof (length_le4 v) as Lv.
  pose proof (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia) ltac:(lia)) as R.
  replace (a + 0) with a in R by lia.
  rewrite R. first [reflexivity | f_equal; change (Z.to_nat 0) with 0%nat; rewrite skipn_O;
                                  apply firstn_all2; lia].
Qed.

Lemma p1u_saved_nth : forall ws m a k (w : word), saved_at rsegs m a ws -> nth_error ws k = Some w ->
  bytes_at rsegs m (a + 8 * Z.of_nat k) (le8 w).
Proof.
  induction ws as [|w0 ws IH]; intros m a k w H E; [destruct k; discriminate E|].
  unfold saved_at in H. cbn [map concat] in H. apply bytes_at_app in H as [H1 H2].
  pose proof (length_le8 w0) as Lw.
  replace (a + Z.of_nat (length (le8 w0))) with (a + Z.of_nat 8) in H2 by lia.
  destruct k as [|k]; cbn [nth_error] in E.
  - injection E as <-. replace (a + 8 * Z.of_nat 0) with a by lia. exact H1.
  - replace (a + 8 * Z.of_nat (S k)) with (a + Z.of_nat 8 + 8 * Z.of_nat k) by lia.
    exact (IH m (a + Z.of_nat 8) k w H2 E).
Qed.

Lemma p1u_saved_read : forall ws m a k (w : word) (b : Z), saved_at rsegs m a ws -> nth_error ws k = Some w ->
  b = a + 8 * Z.of_nat k -> ov_read_bytes rsegs m (wa b) 8 = Some (le8 w).
Proof. intros ws m a k w b H E ->. apply p1u_ld8. exact (p1u_saved_nth ws m a k w H E). Qed.

Lemma p1u_cell_bytes : forall m A cs k cl, rw_cells rsegs m A cs -> cell_at cs k = Some cl ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes cl).
Proof.
  intros m A cs k cl [H1 _] E.
  destruct (cell_at_split cs k cl (C8 (Z_to_bv 64 0)) E) as (pre & post & Ecs & Hk & _).
  destruct H1 as [Hwf Hb]. rewrite Ecs in Hwf, Hb.
  apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ B].
  rewrite (cells_bytes_length pre W1), Hk in B.
  cbn [cells_bytes] in B. apply bytes_at_app in B as [B _]. exact B.
Qed.

Lemma p1u_glue8 : forall m a b (v : word) l, b = a + 8 ->
  bytes_at rsegs m a (le8 v) -> bytes_at rsegs m b l -> bytes_at rsegs m a (le8 v ++ l).
Proof.
  intros m a b v l -> H1 H2. pose proof (length_le8 v) as Lv. apply bytes_at_app. split; [exact H1|].
  replace (a + Z.of_nat (length (le8 v))) with (a + 8) by lia. exact H2.
Qed.

(** * The spine's start state *)

Lemma p1u_start_fields : forall rc0 lab,
  rc_seg (pf_start rc0 lab) = rc_seg rc0 /\ rc_refusal (pf_start rc0 lab) = rc_refusal rc0 /\
  rc_refused (pf_start rc0 lab) = rc_refused rc0 /\ rc_overflow (pf_start rc0 lab) = rc_overflow rc0 /\
  rc_gen (pf_start rc0 lab) = rc_gen rc0 + 1 /\
  rc_reading (pf_start rc0 lab) = snprintf_s 96 F_s [AS (match lab with Some l => l | None => S_base end)].
Proof. intros rc0 lab. unfold pf_start. cbn. repeat split. Qed.

(** The new block bytes: the reading field and the gen counter replaced, everything else kept. *)
Lemma p1u_enc_start : forall rc0 rd BP BR BG BQ BR' G',
  rconf_enc rc0 (BP ++ BR ++ BG ++ BQ) ->
  Z.of_nat (length BP) = 16512 -> length BR = 96%nat -> length BG = 4%nat -> Z.of_nat (length BQ) = 4 ->
  length BR' = 96%nat -> G' = le4 (Z_to_bv 64 (rc_gen rc0 + 1)) ->
  cstr_enc 96 rd BR' -> 0 <= rc_gen rc0 + 1 < 2 ^ 32 ->
  rconf_enc (RConf (rc_seg rc0) (rc_refusal rc0) (rc_refused rc0) (rc_overflow rc0) rd (rc_gen rc0 + 1))
            (BP ++ BR' ++ G' ++ BQ).
Proof.
  intros rc0 rd BP BR BG BQ BR' G' HE LP LR LG LQ LR' EG CE HG.
  destruct HE as (HL & HLS & Hseg & Hn & Hrl & Hrf & Hnref & Hrefd & Hov & Hrd & Hgen).
  rewrite !length_app in HL. unfold SEG_C_SIZE in HL.
  unfold rconf_enc, fldz in *.
  cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
  unfold RC_N, RC_NREF, RC_REFUSED, RC_OVERFLOW, RC_READING, RC_GEN, RC_REFUSAL, SEG_C_SIZE in *.
  split; [rewrite !length_app, EG, length_le4; lia|].
  split; [exact HLS|].
  split; [intros i Hi; specialize (Hseg i Hi); p1u_fmatch Hseg|].
  split; [p1u_fmatch Hn|].
  split; [exact Hrl|].
  split; [intros i Hi; specialize (Hrf i Hi); p1u_fmatch Hrf|].
  split; [p1u_fmatch Hnref|].
  split; [p1u_fmatch Hrefd|].
  split; [p1u_fmatch Hov|].
  split.
  { p1u_fsimp. rewrite p1u_fld_full by (first [reflexivity | lia]). exact CE. }
  { p1u_fsimp. rewrite EG. p1u_fsimp. rewrite p1u_fld_full by (first [reflexivity | lia]).
    apply p1u_u32_le4. lia. }
Qed.

(** * The C string facts the snprintf call needs *)

Lemma p1u_cstr_bytes : forall m a l, cstr_at rsegs m a l -> Forall (fun x => 0 < x < 256) l.
Proof.
  intros m a l (bs & sl & _ & Hz & Hn & _). apply Forall_forall. intros x Hx.
  assert (Hr : 0 <= x < 256).
  { rewrite <- Hz in Hx. unfold zs in Hx. apply in_map_iff in Hx as (b & <- & _).
    pose proof (sq_byte_range b). lia. }
  destruct (Z.eq_dec x 0) as [->|Hne]; [exfalso; exact (Hn Hx) | lia].
Qed.

Lemma p1u_cstr_hd : forall m a l, cstr_at rsegs m a l ->
  ov_read_bytes rsegs m (wa a) 1 = Some [Z_to_bv 8 (hd0 l)].
Proof.
  intros m a l (bs & sl & B & Hz & Hn & _).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  destruct bs as [|b bs']; cbn [app] in B.
  - pose proof (bytes_at_read rsegs m a _ 0 1 B ltac:(lia) ltac:(cbn [length]; lia)) as R.
    rewrite R, <- Hz. reflexivity.
  - pose proof (bytes_at_read rsegs m a _ 0 1 B ltac:(lia) ltac:(cbn [length]; lia)) as R.
    rewrite R, <- Hz. unfold zs. cbn [map hd0]. rewrite sq_byte_lit. reflexivity.
Qed.

Lemma p1u_cstr_hd_range : forall m a l, cstr_at rsegs m a l -> 0 <= hd0 l < 256.
Proof.
  intros m a l (bs & sl & _ & Hz & _). rewrite <- Hz. destruct bs as [|b bs']; unfold zs; cbn [map hd0].
  - lia.
  - apply sq_byte_range.
Qed.

(** The C string at a, as snprintf reads a %s argument. *)
Lemma p1u_zb_zs : forall bs : list byte, zb (zs bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  unfold zb, zs in *. cbn [map]. f_equal; [apply sq_byte_lit | exact IH].
Qed.

Lemma p1u_arg_bytes : forall m a l, cstr_at rsegs m a l ->
  exists slack : list byte,
    bytes_at rsegs m a (pf_bytes (l ++ [0]) ++ slack) /\
    (- (a + Z.of_nat (length l) + 1)) mod 8 <= Z.of_nat (length slack) /\
    Z.of_nat (length l) + 1 + Z.of_nat (length slack) <= Z.of_nat (length l) + 8.
Proof.
  intros m a l (bs & sl & B & Hz & Hn & Hsl).
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length l) + 1)) 8 ltac:(lia)) as MB.
  set (k := Z.to_nat ((- (a + Z.of_nat (length l) + 1)) mod 8)) in *.
  assert (Hk : Z.of_nat k = (- (a + Z.of_nat (length l) + 1)) mod 8) by (unfold k; lia).
  assert (Lbs : length bs = length l) by (rewrite <- Hz; unfold zs; symmetry; apply length_map).
  assert (Lk : length (firstn k sl) = k) by (rewrite length_firstn; lia).
  assert (EB : pf_bytes (l ++ [0]) = bs ++ [ZERO]).
  { change (pf_bytes (l ++ [0])) with (zb (l ++ [0])). rewrite <- Hz.
    unfold zb. rewrite map_app. cbn [map]. f_equal. all: try reflexivity.
    change (map (Z_to_bv 8) (zs bs)) with (zb (zs bs)). apply p1u_zb_zs. }
  exists (firstn k sl).
  split; [|split; [rewrite Lk; lia | rewrite Lk; lia]].
  rewrite EB, <- app_assoc. cbn [app].
  rewrite <- (firstn_skipn k sl) in B.
  replace (bs ++ ZERO :: firstn k sl ++ skipn k sl) with ((bs ++ ZERO :: firstn k sl) ++ skipn k sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B as [B _]. exact B.
Qed.

(** * The read-only strings P1 names *)

Lemma p1u_ro_str : forall m a l, mem_inv rsegs m -> 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
  ro_bytes_b rsegs a l = true -> bytes_at rsegs m a l.
Proof. intros m a l MI H0 H1 H. apply ro_bytes_at; auto. apply ro_bytes_b_sound. exact H. Qed.

Definition P1U_FMT : Z := 0x104e0.          (* "%s" *)

Lemma p1u_fmt_len : length (pf_bytes (F_s ++ [0])) = 3%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma p1u_fmt_at : forall m, mem_inv rsegs m -> bytes_at rsegs m P1U_FMT (pf_bytes (F_s ++ [0])).
Proof.
  intros m MI. pose proof p1u_fmt_len as L3.
  apply p1u_ro_str; [exact MI | unfold P1U_FMT; lia | unfold P1U_FMT; lia | vm_compute; reflexivity].
Qed.

Lemma p1u_fmt_parse : pf_parse F_s = Some [Ps].
Proof. vm_compute. reflexivity. Qed.

Lemma p1u_base_len : length S_base = 12%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma p1u_base_zlen : length (zb S_base ++ [ZERO]) = 13%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma p1u_base_at : forall m, mem_inv rsegs m -> cstr_at rsegs m STR_BASE S_base.
Proof.
  intros m MI. pose proof p1u_base_len as L12. pose proof p1u_base_zlen as L13.
  exists (zb S_base), [].
  split; [apply p1u_ro_str; [exact MI | unfold STR_BASE; lia | unfold STR_BASE; lia
                            | vm_compute; reflexivity]|].
  split; [vm_compute; reflexivity|].
  split; [apply nulfree_forallb; vm_compute; reflexivity|].
  rewrite L12. cbn [length]. unfold STR_BASE. Z.div_mod_to_equations. lia.
Qed.
(** * Word facts the walk uses *)

(** `andi a0,a0,7` on a 16-aligned pointer. *)
Lemma p1u_andi7 : forall x, 0 <= x < 2 ^ 64 -> x mod 16 = 0 ->
  Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = 0.
Proof.
  intros x Hx H. rewrite unsigned_lit by lia. change 7 with (Z.ones 3).
  rewrite Z.land_ones by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma p1u_andi7z : forall x, 0 <= x -> x mod 16 = 0 -> Z.land x 7 = 0.
Proof.
  intros x Hx H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

(** The 96-byte field after snprintf wrote w and its NUL into its head. *)
Lemma p1u_cstr_enc_sn : forall (w : list Z) (rest : list byte),
  Forall (fun x => 0 <= x < 256) w -> ~ In 0 w ->
  (length w < 96)%nat -> length (pf_bytes (w ++ [0]) ++ rest) = 96%nat ->
  cstr_enc 96 w (pf_bytes (w ++ [0]) ++ rest).
Proof.
  intros w rest HF HN HL HLen. split; [exact HLen|]. split; [exact HL|]. split; [exact HN|].
  rewrite p1u_zs_app.
  replace (zs (pf_bytes (w ++ [0]))) with (w ++ [0]).
  2: { change (pf_bytes (w ++ [0])) with (zb (w ++ [0])). symmetry. apply p1u_zs_zb.
       apply Forall_app. split; [exact HF | constructor; [lia | constructor]]. }
  replace (S (length w)) with (length (w ++ [0])) by (rewrite length_app; cbn [length]; lia).
  apply firstn_app_exact.
Qed.

(** The 13 saved registers, read out of the frame's cells. *)
Lemma p1u_saved13_cells : forall m A cs (k : nat) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : word),
  rw_cells rsegs m A cs ->
  cell_at cs k = Some (C8 w0) -> cell_at cs (k + 8) = Some (C8 w1) ->
  cell_at cs (k + 16) = Some (C8 w2) -> cell_at cs (k + 24) = Some (C8 w3) ->
  cell_at cs (k + 32) = Some (C8 w4) -> cell_at cs (k + 40) = Some (C8 w5) ->
  cell_at cs (k + 48) = Some (C8 w6) -> cell_at cs (k + 56) = Some (C8 w7) ->
  cell_at cs (k + 64) = Some (C8 w8) -> cell_at cs (k + 72) = Some (C8 w9) ->
  cell_at cs (k + 80) = Some (C8 w10) -> cell_at cs (k + 88) = Some (C8 w11) ->
  cell_at cs (k + 96) = Some (C8 w12) ->
  saved_at rsegs m (A + Z.of_nat k) [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12].
Proof.
  intros m A cs k w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 FR E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12.
  repeat match goal with
  | H : cell_at cs ?kk = Some (C8 ?w) |- _ =>
      apply (p1u_cell_bytes m A cs kk (C8 w) FR) in H; cbn [cbytes] in H
  end.
  unfold saved_at. cbn [map concat].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 8)) w0); [lia | exact E0 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 16)) w1); [lia | exact E1 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 24)) w2); [lia | exact E2 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 32)) w3); [lia | exact E3 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 40)) w4); [lia | exact E4 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 48)) w5); [lia | exact E5 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 56)) w6); [lia | exact E6 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 64)) w7); [lia | exact E7 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 72)) w8); [lia | exact E8 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 80)) w9); [lia | exact E9 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 88)) w10); [lia | exact E10 |].
  apply (p1u_glue8 m _ (A + Z.of_nat (k + 96)) w11); [lia | exact E11 |].
  rewrite app_nil_r. exact E12.
Qed.

Lemma p1u_notz : forall x, 0 <= x < 2 ^ 64 -> Z_to_bv 64 (Z.lxor x 18446744073709551615) = pf_not x.
Proof.
  intros x Hx. unfold pf_not. rewrite zb_lxor_ones by lia.
  apply Z_to_bv_eqm. replace (18446744073709551615 - x) with ((- x - 1) + 1 * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(** A run of 8-byte cells, read as consecutive saved words. *)
Lemma p1u_saved_cells : forall ws m A cs (k : nat),
  rw_cells rsegs m A cs ->
  (forall j w, nth_error ws j = Some w -> cell_at cs (k + 8 * j)%nat = Some (C8 w)) ->
  0 <= A + Z.of_nat k -> A + Z.of_nat k + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  saved_at rsegs m (A + Z.of_nat k) ws.
Proof.
  induction ws as [|w ws IH]; intros m A cs k FR H H0 H1.
  - unfold saved_at. cbn [map concat]. apply bytes_at_nil. cbn [length] in H1. lia.
  - unfold saved_at. cbn [map concat]. apply bytes_at_app. split.
    + specialize (H 0%nat w eq_refl). replace (k + 8 * 0)%nat with k in H by lia.
      exact (p1u_cell_bytes m A cs k (C8 w) FR H).
    + pose proof (length_le8 w) as L8.
      replace (A + Z.of_nat k + Z.of_nat (length (le8 w))) with (A + Z.of_nat (k + 8)) by lia.
      apply (IH m A cs (k + 8)%nat FR).
      * intros j w' E. specialize (H (S j) w' E).
        replace (k + 8 + 8 * j)%nat with (k + 8 * S j)%nat by lia. exact H.
      * lia.
      * cbn [length] in H1. lia.
Qed.
Lemma p1u_split_z : forall {A} (l : list A) (k : Z), 0 <= k -> k <= Z.of_nat (length l) ->
  exists l1 l2, l = l1 ++ l2 /\ Z.of_nat (length l1) = k.
Proof.
  intros A l k Hk Hle. exists (firstn (Z.to_nat k) l), (skipn (Z.to_nat k) l).
  split; [symmetry; apply firstn_skipn|]. rewrite length_firstn. lia.
Qed.

Lemma p1u_fs_len : length F_s = 2%nat.
Proof. vm_compute. reflexivity. Qed.

(** `not rd,rs` as the step leaves it: the frame's ~x word. *)
Lemma p1u_not : forall x, 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615) = pf_not x.
Proof.
  intros x Hx. unfold pf_not. rewrite (unsigned_lit x) by lia. rewrite zb_lxor_ones by lia.
  apply Z_to_bv_eqm. replace (18446744073709551615 - x) with ((- x - 1) + 1 * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma p1u_le4_eqm : forall x y : word, bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32 -> le4 x = le4 y.
Proof.
  intros x y H. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned x) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned y) 32) by lia. rewrite H. reflexivity.
Qed.

(** `lw` then `addi 1` then `sw` on a u32 counter. *)
Lemma p1u_le4_inc : forall g, 0 <= g < 2 ^ 32 ->
  le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 g)) + 1)) = le4 (Z_to_bv 64 (g + 1)).
Proof.
  intros g Hg. apply p1u_le4_eqm. unfold sx32. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

(** The first byte of a C string: its first character, or its NUL (the `lbu` of the entry test). *)
Lemma p1u_cstr_first : forall m p l, cstr_at rsegs m p l ->
  exists b : byte, ov_read_bytes rsegs m (wa (p + Z.of_nat 0)) 1 = Some [b] /\
    (l = [] -> bv_unsigned b = 0) /\ (l <> [] -> bv_unsigned b <> 0).
Proof.
  intros m p l (bs & sl & HB & Hz & Hnz & _).
  destruct bs as [|b0 bs].
  - exists ZERO. rewrite (bytes_at_ov_read rsegs m p _ 0 1 HB) by (cbn; lia). cbn.
    split; [first [reflexivity | trivial]|]. split; [intros _; first [reflexivity | trivial]|].
    intros Hs. exfalso. apply Hs. rewrite <- Hz. reflexivity.
  - exists b0. rewrite (bytes_at_ov_read rsegs m p _ 0 1 HB) by (cbn; lia). cbn.
    split; [first [reflexivity | trivial]|].
    split; [intros Hs; rewrite <- Hz in Hs; discriminate Hs|].
    intros _ E. apply Hnz. rewrite <- Hz. cbn. left. exact E.
Qed.

(** A write apart from the string's read span keeps it. *)
Lemma p1u_cstr_munch : forall W ma mb a l, cstr_at rsegs ma a l -> munch W ma mb ->
  disjoint_from W a (cstr_span a l) -> cstr_at rsegs mb a l.
Proof.
  intros W ma mb a l (bs & sl & B & Hz & Hn & Hsl) MU D.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length l) + 1)) 8 ltac:(lia)) as MB.
  set (k := Z.to_nat ((- (a + Z.of_nat (length l) + 1)) mod 8)) in *.
  assert (Hk : Z.of_nat k = (- (a + Z.of_nat (length l) + 1)) mod 8) by (unfold k; lia).
  assert (Lbs : length bs = length l) by (rewrite <- Hz; unfold zs; symmetry; apply length_map).
  assert (Lk : length (firstn k sl) = k) by (rewrite length_firstn; lia).
  exists bs, (firstn k sl). split; [|split; [exact Hz | split; [exact Hn | rewrite Lk; lia]]].
  rewrite <- (firstn_skipn k sl) in B.
  replace (bs ++ ZERO :: firstn k sl ++ skipn k sl) with ((bs ++ ZERO :: firstn k sl) ++ skipn k sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B as [B _].
  eapply bytes_at_transport; [exact B | exact MU |].
  eapply p1u_disjoint_sub; [exact D | lia |].
  rewrite length_app. cbn [length]. rewrite Lk, Lbs. unfold cstr_span. lia.
Qed.

Lemma p1u_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[a b] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros [_ H']; exact (H H')].
  destruct (Z_le_dec a x); destruct (Z_lt_dec x b);
    [right; intros [H' _]; lia | left; split; [lia | exact H] ..].
Qed.

(** Writes inside a footprint whose bytes were all present keep MemNorm's normal form. *)
Lemma p1u_task_munch : forall W ma mb, MemNorm.task_mem rsegs ma -> munch W ma mb ->
  (forall x : word, ~ outside W (bv_unsigned x) -> mrd rsegs ma x <> None) ->
  MemNorm.task_mem rsegs mb.
Proof.
  intros W ma mb T MU P x b Hx.
  destruct (p1u_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - rewrite (MU x Ho) in Hx. exact (T x b Hx).
  - specialize (P x Ho). unfold mrd in P. destruct (ma x) as [b0|] eqn:E.
    + exact (T x b0 E).
    + left. intros Hf. apply P. exact (MemNorm.seg_rom_unmapped rsegs x Hf).
Qed.


(** * DONE (0x15c30, the return) *)

Lemma p1u_done : H_DONE.
Proof.
  unfold H_DONE, PF_PC_DONE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo v c rc ENV RC NSLOT.
  pose proof (bv_unsigned_in_range 64 sp) as RS. change (bv_modulus 64) with (2 ^ 64) in RS.
  pose proof (Z_to_bv_bv_unsigned sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  destruct ENV as (Hc0 & Hc16 & APc & IMGc & PENV & CAT & STK & MI & SV).
  destruct PENV as (FRM & TM & SSP & HIMG & HSPhi).
  destruct STK as (ST & HDEP & HSP16 & HNR).
  unfold PARSE_FILE_FRAME, PF_NSLOT, PF_SAVE, RC_N in *.
  destruct RC as (bs & BC & HENC).
  destruct (sq_rconf_len rc bs HENC) as [LBS LSEG].
  pose proof (p1u_ld8 m (Sp + 88) _ NSLOT) as RD0.
  pose proof (sq_rc_n rsegs m c bs rc BC HENC) as RDN. unfold RC_N in RDN.
  pose proof (p1u_saved_read _ m _ 0%nat (sv_s11 v) (Sp + 952) SV eq_refl ltac:(lia)) as L00.
  pose proof (p1u_saved_read _ m _ 1%nat (sv_s10 v) (Sp + 960) SV eq_refl ltac:(lia)) as L01.
  pose proof (p1u_saved_read _ m _ 2%nat (sv_s9 v) (Sp + 968) SV eq_refl ltac:(lia)) as L02.
  pose proof (p1u_saved_read _ m _ 3%nat (sv_s8 v) (Sp + 976) SV eq_refl ltac:(lia)) as L03.
  pose proof (p1u_saved_read _ m _ 4%nat (sv_s7 v) (Sp + 984) SV eq_refl ltac:(lia)) as L04.
  pose proof (p1u_saved_read _ m _ 5%nat (sv_s6 v) (Sp + 992) SV eq_refl ltac:(lia)) as L05.
  pose proof (p1u_saved_read _ m _ 6%nat (sv_s5 v) (Sp + 1000) SV eq_refl ltac:(lia)) as L06.
  pose proof (p1u_saved_read _ m _ 7%nat (sv_s4 v) (Sp + 1008) SV eq_refl ltac:(lia)) as L07.
  pose proof (p1u_saved_read _ m _ 8%nat (sv_s3 v) (Sp + 1016) SV eq_refl ltac:(lia)) as L08.
  pose proof (p1u_saved_read _ m _ 9%nat (sv_s2 v) (Sp + 1024) SV eq_refl ltac:(lia)) as L09.
  pose proof (p1u_saved_read _ m _ 10%nat (sv_s1 v) (Sp + 1032) SV eq_refl ltac:(lia)) as L10.
  pose proof (p1u_saved_read _ m _ 11%nat (sv_s0 v) (Sp + 1040) SV eq_refl ltac:(lia)) as L11.
  pose proof (p1u_saved_read _ m _ 12%nat (sv_ra v) (Sp + 1048) SV eq_refl ltac:(lia)) as L12.
  clear SV NSLOT.
  do 3 zstep.
  rewrite (sq_sx32 (Z.of_nat (length (rc_seg rc)))) by lia.
  do 15 zstep.
  apply evt_done. unfold pf_ret, ret_post_fp, PARSE_FILE_FRAME.
  rewrite (unsigned_lit Sp) by lia.
  do 17 eexists.
  split; [reflexivity|].
  split; [exact FRM|].
  split; [intros k Hk; reflexivity|].
  split; [apply munch_refl|].
  split; [apply wmono_refl|].
  split; [exact MI|].
  split; [exact TM|].
  split; [rewrite unsigned_lit by lia; exact ST|].
  exists bs. split; [exact BC | exact HENC].
Qed.

(** * ENTRY (0x15248): the prologue, the snprintf call, the setup, and the two exits *)

Section Entry.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte) (lo c tx lp S : Z) (rc : rconf) (s : list Z) (lab : option (list Z)).
Hypothesis HSN : snprintf_contract.
Hypothesis HH : forall n, H_HEAD n.
Hypothesis HD : H_DONE.
Hypothesis PRE : reac_segconf_parse_file_pre m fc S lo c tx lp rc s lab.
Hypothesis RS : 0 <= S < 2 ^ 64.
Hypothesis Rc : 0 <= c < 2 ^ 64.
Hypothesis Rt : 0 <= tx < 2 ^ 64.
Hypothesis Rlp : 0 <= lp < 2 ^ 64.

Definition vv : pf_sv := PFSv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
Definition rcf : rconf := fst (fst (r_lines (pf_start rc lab, None, []) 0 (lines s))).
Definition Wpf : list ivl := ((S - PARSE_FILE_STACK, S) :: RC_PARSE_W c).
Definition Post : machine_state -> Prop :=
  ret_post_fp ra (Z_to_bv 64 S) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
    (Z.of_nat (length (rc_seg rcf))) m Wpf lo (fun m' => rconf_at rsegs m' c rcf).

(** The numbers of the frame: the stack is deep enough and above the image. *)
Lemma p1u_Sbig : 0 <= lo /\ 0x54088 <= lo /\ lo + 7088 <= S /\ 7088 <= S /\ S < 2 ^ 63.
Proof.
  destruct PRE as (RPRE & _).
  destruct RPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PENV & _ & STK & _).
  destruct PENV as (_ & _ & _ & HIMG & HSPhi). destruct STK as (ST & HDEP & _ & _).
  unfold SA, SEG_UBSAN in HIMG. cbn [sa_img_end] in HIMG.
  unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in HDEP.
  pose proof (proj1 ST) as Hlo.
  repeat split; lia.
Qed.

(** The post of a cut, weakened to the function's post. *)
Lemma p1u_weaken : forall (m4 : word -> option byte) (F' : bvmap 5 word) (ms' : machine_state),
  munch Wpf m m4 -> wmono rsegs m m4 ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
  pf_ret vv (Z_to_bv 64 (S - PARSE_FILE_FRAME)) gp tp F' m4 lo c rcf ms' -> Post ms'.
Proof.
  intros m4 F' ms' MU WM FK PO.
  pose proof p1u_Sbig as (HB1 & HB2 & HB3 & HB4 & HB5).
  unfold pf_ret, ret_post_fp, PARSE_FILE_FRAME in PO. rewrite unsigned_lit in PO by lia.
  replace (S - 1056 + 1056) with S in PO by lia.
  unfold Post, ret_post_fp, vv in *. cbn [sv_ra sv_s0 sv_s1 sv_s2 sv_s3 sv_s4 sv_s5 sv_s6 sv_s7 sv_s8 sv_s9
    sv_s10 sv_s11] in PO.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F2 & fc2 & m5
                  & E & FRM2 & FK2 & MU2 & WM2 & MI2 & TM2 & ST2 & Q2).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, F2, fc2, m5.
  split; [exact E|].
  split; [exact FRM2|].
  split; [intros k Hk; rewrite (FK2 k Hk); exact (FK k Hk)|].
  split; [eapply munch_trans; [exact MU|]; unfold Wpf; exact MU2|].
  split; [eapply wmono_trans; [exact WM | exact WM2]|].
  split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2 | exact Q2].
Qed.

Lemma p1u_entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 tx) (Z_to_bv 64 lp)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_SEGCONF_PARSE_FILE) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6. unfold REAC_SEGCONF_PARSE_FILE.
  destruct PRE as (RPRE & OLAB & LABF).
  destruct RPRE as (Hc0 & Hc16 & RC0 & APc & IMGc & Hgen & Href & Hovf & Ht0 & CS & LS & APt & APtc & PENV
                    & CAT & STK & MI).
  destruct PENV as (FRM & TM & SSP & HIMG & HSPhi).
  destruct STK as (ST & HDEP & HSP16 & HNR).
  unfold SA, SEG_UBSAN in HIMG. cbn [sa_img_end] in HIMG.
  unfold PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in HDEP.
  unfold apart, SEG_C_SIZE in APc, APt, APtc, IMGc.
  destruct RC0 as (bs & BC & HENC).
  destruct (sq_rconf_len rc bs HENC) as [LBS LSEG].
  assert (LSz : Z.of_nat (length s) <= 65535).
  { apply Nat2Z.inj_le in LS. assert (E : Z.of_nat 65535%nat = 65535) by reflexivity.
    rewrite E in LS. exact LS. }
  pose proof (munch_refl [(S - 7088, S); (c + 16512, c + 16612)] m) as MU.
  pose proof (munch_refl [(S - 7088, S)] m) as MUF.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof p1u_Sbig as (HB1 & HB2 & HB3 & HB4 & HB5).
  pose proof (bytes_at_bound rsegs m c bs BC) as BBc. rewrite LBS in BBc.
  (* every byte the function writes was present at entry *)
  assert (PRES : forall x : word, ~ outside [(S - 7088, S); (c + 16512, c + 16612)] (bv_unsigned x) ->
                   mrd rsegs m x <> None).
  { intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as Rx.
    change (bv_modulus 64) with (2 ^ 64) in Rx.
    assert (E : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_bv_unsigned).
    destruct (Z_lt_dec (bv_unsigned x) S) as [Hlt|Hge].
    - destruct (Z_le_dec (S - 7088) (bv_unsigned x)) as [Hle|Hgt].
      + destruct ST as (_ & _ & STa). destruct (STa (bv_unsigned x) ltac:(lia)) as [_ (b & Hb)].
        rewrite E in Hb. rewrite Hb. discriminate.
      + assert (Hc : c <= bv_unsigned x < c + 16616) by lia.
        destruct BC as (_ & _ & Bb). rewrite <- E.
        replace (bv_unsigned x) with (c + Z.of_nat (Z.to_nat (bv_unsigned x - c))) by lia.
        rewrite Bb by lia. intros C. apply nth_error_None in C. lia.
    - assert (Hc : c <= bv_unsigned x < c + 16616) by lia.
      destruct BC as (_ & _ & Bb). rewrite <- E.
      replace (bv_unsigned x) with (c + Z.of_nat (Z.to_nat (bv_unsigned x - c))) by lia.
      rewrite Bb by lia. intros C. apply nth_error_None in C. lia. }
  (* the guard and catalogue cells, and the label string, are apart from what P1 writes *)
  assert (DJG : forall p k, 0x10000 <= p -> 0 < k -> p + k <= 0x54088 ->
                  disjoint_from [(S - 7088, S); (c + 16512, c + 16612)] p k).
  { intros p k Hp1 Hk Hp2.
    pose proof (p1u_apart_img c 16616 (c + 16512) 100 p k IMGc ltac:(lia) ltac:(lia) ltac:(lia) Hk Hp1
                  ltac:(lia)) as D.
    cbn [disjoint_from]. repeat split; (exact I || lia). }
  zstep. carve_frame 1056%nat ST.
  do 15 zstep.
  rewrite sq_eqb_lit by lia. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  do 2 zstep.
  rewrite p1u_andi7z by lia.
  zstep.
  rewrite sq_eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  do 11 zstep.
  destruct (stk_split rsegs m1 lo (S - 7088) (S + -1056) ST ltac:(lia)) as [STlo STcall].
  destruct SSP as (SG1 & gcan & SG2). unfold SA, SEG_UBSAN in SG1, SG2.
  cbn [sa_got_guard sa_guard] in SG1, SG2.
  assert (MID : forall (xa1 : word) (Lp : Z) (lstr : list Z),
            cstr_at rsegs m1 Lp lstr -> 0 < Lp < 2 ^ 64 -> Z.of_nat (length lstr) <= 65535 ->
            (Lp + (Z.of_nat (length lstr) + 8) <= lo \/ S <= Lp) ->
            (Lp + (Z.of_nat (length lstr) + 8) <= c + 16512 \/ c + 16608 <= Lp) ->
            lstr = match lab with Some l => l | None => S_base end ->
            evt rsegs Post
              (MS (mkR ra (Z_to_bv 64 (S + -1056)) gp tp t0 t1 t2 (Z_to_bv 64 12288)
                       (Z_to_bv 64 (c + 16608)) (Z_to_bv 64 11392) xa1 (Z_to_bv 64 16608)
                       (Z_to_bv 64 Lp) (Z_to_bv 64 c) a5 a6 a7 (Z_to_bv 64 tx) (Z_to_bv 64 (c + 16512))
                       s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x152cc) fc None m1 (seg_rom rsegs))).
  { intros xa1 Lp lstr LCS LNZ LLen LAPs LAPc ELS.
    clear MUF.
    pose proof BC as BCfull.
    assert (WRC : wr_at rsegs m1 c 16616).
    { rewrite <- LBS. apply (p1u_wr_block m1 c bs BCfull). rewrite LBS. exact IMGc. }
    destruct (p1u_split_z bs 16512 ltac:(lia) ltac:(lia)) as (BP & R1 & EB1 & LBP).
    rewrite EB1 in BCfull, HENC, LBS. rewrite length_app in LBS.
    destruct (p1u_split_z R1 96 ltac:(lia) ltac:(lia)) as (BR & R2 & EB2 & LBR).
    rewrite EB2 in BCfull, HENC, LBS. rewrite length_app in LBS.
    destruct (p1u_split_z R2 4 ltac:(lia) ltac:(lia)) as (BG & BQ & EB3 & LBG).
    rewrite EB3 in BCfull, HENC, LBS. rewrite length_app in LBS.
    assert (LBQ : Z.of_nat (length BQ) = 4) by lia.
    apply bytes_at_app in BCfull as [BCP BCr].
    replace (c + Z.of_nat (length BP)) with (c + 16512) in BCr by lia.
    apply bytes_at_app in BCr as [BCR BCg].
    replace (c + 16512 + Z.of_nat (length BR)) with (c + 16608) in BCg by lia.
    apply bytes_at_app in BCg as [BCG BCQ].
    replace (c + 16608 + Z.of_nat (length BG)) with (c + 16612) in BCQ by lia.
    assert (EFG : fldz RC_GEN 4 (BP ++ BR ++ BG ++ BQ) = BG).
    { unfold fldz, RC_GEN. p1u_fsimp. apply p1u_fld_full; lia. }
    assert (HG : 0 <= rc_gen rc < 2 ^ 32 /\ BG = le4 (Z_to_bv 64 (rc_gen rc))).
    { destruct HENC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [Hg1 Hg2]).
      rewrite EFG in Hg2. split; [exact Hg1 | exact Hg2]. }
    destruct HG as [HGR EBG].
    do 7 zstep.
    pose proof HSN as HSN'. unfold snprintf_contract in HSN'. cbv zeta in HSN'.
    eapply evt_cut.
    { eapply HSN' with (lo := S - 7088) (fmt := F_s) (ps := [Ps]) (args := [APtr lstr]) (T := lstr)
                      (junk := BR);
        rewrite ?unsigned_lit by lia.
      - pose proof (p1u_fmt_at m1 MI) as HF. unfold P1U_FMT in HF. exact HF.
      - unfold RO_LO. lia.
      - pose proof p1u_fs_len as L2. unfold RO_END. lia.
      - exact p1u_fmt_parse.
      - cbn [pf_args_ok pf_arg_ok]. rewrite ?unsigned_lit by lia.
        split; [|exact I].
        split; [exact (p1u_cstr_bytes m1 Lp lstr LCS)|].
        destruct (p1u_arg_bytes m1 Lp lstr LCS) as (slk & BSL & HS1 & HS2).
        exists slk. split; [exact BSL|]. split; [exact HS1|]. split; [lia|]. split; lia.
      - cbn. rewrite ?app_nil_r. reflexivity.
      - split; [split|].
        + cbn [cells_wf cell_wf]. split; [lia | exact I].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BCR.
        + cbn [cells_size csize]. eapply p1u_wr_at_sub; [exact WRC | lia | lia | lia].
      - lia.
      - lia.
      - lia.
      - lia.
      - apply (p1u_img_free c 16616); [exact IMGc | lia | lia].
      - exact STcall.
      - unfold SNPRINTF_K. lia.
      - unfold IMG_END. lia.
      - lia.
      - exact FRM.
      - exact MI.
      - eapply p1u_task_munch; [exact TM | exact MU | exact PRES].
      - unfold GOT_GUARD, GUARD. eapply bytes_at_transport; [exact SG1 | exact MU |].
        pose proof (length_le8 (Z_to_bv 64 342048)) as L8.
        replace (Z.of_nat (length (le8 (Z_to_bv 64 342048)))) with 8 by lia.
        apply DJG; lia.
      - unfold GUARD. eapply bytes_at_transport; [exact SG2 | exact MU |].
        pose proof (length_le8 gcan) as L8.
        replace (Z.of_nat (length (le8 gcan))) with 8 by lia.
        apply DJG; lia. }
    intros ms2 PO2.
    unfold printf_post in PO2.
    destruct PO2 as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & F2 & fc2
                     & m2 & E2 & MU2 & WM2 & MI2 & TM2 & FRM2 & FK2 & ST2 & BRW).
    subst ms2.
    rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia.
    rewrite ?unsigned_lit in BRW by lia.
    replace (ret_pc (Z_to_bv 64 86760)) with (Z_to_bv 64 86760)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (LNL : ~ In 0 lstr) by (destruct LCS as (? & ? & ? & ? & HN & _); exact HN).
    assert (LFA : Forall (fun x => 0 <= x < 256) lstr).
    { eapply Forall_impl; [|exact (p1u_cstr_bytes m1 Lp lstr LCS)]. cbn. intros a Ha. lia. }
    set (Tw := firstn (Z.to_nat (96 - 1)) lstr) in *.
    assert (LTw : (length Tw <= 95)%nat) by (unfold Tw; rewrite length_firstn; lia).
    assert (TwN : ~ In 0 Tw) by (unfold Tw; apply nulfree_firstn; exact LNL).
    assert (TwF : Forall (fun x => 0 <= x < 256) Tw) by (unfold Tw; apply p1u_Forall_firstn; exact LFA).
    (* the tail of the reading field that snprintf did not touch *)
    destruct (p1u_split_z BR (Z.of_nat (length Tw) + 1) ltac:(lia) ltac:(lia)) as (BR1 & BR2 & EBR & LBR1).
    assert (LBR2 : Z.of_nat (length BR2) = 95 - Z.of_nat (length Tw)).
    { pose proof LBR as LBRc. rewrite EBR, length_app in LBRc. lia. }
    rewrite EBR in BCR. apply bytes_at_app in BCR as [BCR1 BCR2].
    replace (c + 16512 + Z.of_nat (length BR1)) with (c + 16512 + (Z.of_nat (length Tw) + 1)) in BCR2 by lia.
    (* the footprint of the whole piece, and what it keeps *)
    assert (MUW : munch [(S - 7088, S); (c + 16512, c + 16612)] m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
      unfold sub_fp. intros x Hx. cbn [outside] in Hx |- *.
      destruct Hx as (H1 & H2 & _). repeat split; (exact I || lia). }
    assert (DJ2 : forall a n, (a + n <= S - 7088 \/ S + -1056 <= a) ->
                    (a + n <= c + 16512 \/ c + 16512 + Z.of_nat (length Tw) + 1 <= a) ->
                    disjoint_from [(S - 7088, S + -1056);
                                   (c + 16512, c + 16512 + Z.of_nat (length Tw) + 1)] a n).
    { intros a n H1 H2. cbn [disjoint_from]. repeat split; (exact I || lia). }
    assert (BCP2 : bytes_at rsegs m2 c BP).
    { eapply bytes_at_transport; [exact BCP | exact MU2 |]. apply DJ2; lia. }
    assert (BCG2 : bytes_at rsegs m2 (c + 16608) BG).
    { eapply bytes_at_transport; [exact BCG | exact MU2 |]. apply DJ2; lia. }
    assert (BCQ2 : bytes_at rsegs m2 (c + 16612) BQ).
    { eapply bytes_at_transport; [exact BCQ | exact MU2 |]. apply DJ2; lia. }
    assert (BCR22 : bytes_at rsegs m2 (c + 16512 + (Z.of_nat (length Tw) + 1)) BR2).
    { eapply bytes_at_transport; [exact BCR2 | exact MU2 |]. apply DJ2; lia. }
    assert (FR2 : rw_cells rsegs m2 (S + -1056)
      [CB 144 (firstn 144 (firstn 952 (firstn 960 (firstn 968 (firstn 976 (firstn 984 (firstn 992
        (firstn 1000 (firstn 1008 (firstn 1016 (firstn 1024 (firstn 1032 (firstn 1040 (firstn 1048 junk))))))))))))));
       C8 (Z_to_bv 64 c);
       CB 800 (skipn 152 (firstn 952 (firstn 960 (firstn 968 (firstn 976 (firstn 984 (firstn 992
        (firstn 1000 (firstn 1008 (firstn 1016 (firstn 1024 (firstn 1032 (firstn 1040 (firstn 1048 junk))))))))))))));
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 |].
      cbn [cells_size csize Nat.add]. apply DJ2; lia. }
    clear FR.
    assert (STlo2 : stk rsegs m2 lo (S - 7088)).
    { eapply stk_transport_disjoint; [exact STlo | exact MU2 | exact WM2 |]. apply DJ2; lia. }
    assert (CS2 : cstr_at rsegs m2 tx s).
    { eapply p1u_cstr_munch; [exact CS | exact MUW |].
      unfold cstr_span in APtc |- *.
      cbn [disjoint_from]. repeat split; (exact I || lia). }
    assert (SSP2 : ssp_ok m2).
    { split; [|exists gcan].
      - unfold SA, SEG_UBSAN. cbn [sa_got_guard sa_guard].
        eapply bytes_at_transport; [exact SG1 | exact MUW |].
        pose proof (length_le8 (Z_to_bv 64 342048)) as L8.
        replace (Z.of_nat (length (le8 (Z_to_bv 64 342048)))) with 8 by lia. apply DJG; lia.
      - unfold SA, SEG_UBSAN. cbn [sa_guard].
        eapply bytes_at_transport; [exact SG2 | exact MUW |].
        pose proof (length_le8 gcan) as L8.
        replace (Z.of_nat (length (le8 gcan))) with 8 by lia. apply DJG; lia. }
    assert (CAT2 : cat_img rsegs m2 (sa_catalogue SA)).
    { intros a Ha. rewrite <- (CAT a Ha). unfold mrd.
      unfold SA, SEG_UBSAN in Ha. cbn [sa_catalogue] in Ha. unfold CAT_BYTES in Ha.
      assert (Q : m2 (wa a) = m (wa a)).
      { apply MUW. rewrite wa_unsigned by lia. eapply disjoint_outside; [|exact Ha].
        apply DJG; lia. }
      rewrite Q. reflexivity. }
    assert (WMW : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
    pose proof (wr_at_transport rsegs m1 m2 c 16616 WRC WM2) as WRC2.
    pose proof (wr_at_store_ok rsegs m2 c 16616 16608 4%nat WRC2 ltac:(lia) ltac:(lia)) as SOK.
    clear MU MU2 WM WM2 DJ2 BCR1 BCR2 BCP BCG BCQ.
    assert (LTwB : Z.of_nat (length (pf_bytes (Tw ++ [0]))) = Z.of_nat (length Tw) + 1)
      by (rewrite p1u_length_pfb, length_app; cbn [length]; lia).
    (* c->gen++ *)
    pose proof (p1u_ld4 m2 (c + 16608) (Z_to_bv 64 (rc_gen rc)) ltac:(rewrite <- EBG; exact BCG2)) as RDG.
    do 2 zstep.
    zstep.
    pose proof (bytes_at_write_same rsegs m2 (c + 16608)
                  (le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 (rc_gen rc))) + 1))) ltac:(lia)
                  ltac:(pose proof (length_le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 (rc_gen rc))) + 1)));
                        lia)) as BGN.
    rewrite (p1u_le4_inc (rc_gen rc)) in BGN |- * by lia.
    store_done.
    (* the reader block now holds the spine's start state *)
    assert (ERD : snprintf_s 96 F_s [AS lstr] = Tw).
    { unfold snprintf_s, Tw. rewrite fmt_s1, cut_nul_id by exact LNL. reflexivity. }
    assert (ENC0 : rconf_enc (pf_start rc lab)
                     (BP ++ (pf_bytes (Tw ++ [0]) ++ BR2) ++ le4 (Z_to_bv 64 (rc_gen rc + 1)) ++ BQ)).
    { unfold pf_start. rewrite <- ELS, ERD.
      apply (p1u_enc_start rc Tw BP BR BG BQ _ _ HENC); try lia.
      - rewrite length_app; lia.
      - reflexivity.
      - apply p1u_cstr_enc_sn; [exact TwF | exact TwN | lia | rewrite length_app; lia]. }
    clear CS2 SSP2 CAT2 TM2 HENC.
    (* the text is not NULL: 0x152f4 is not taken *)
    zstep.
    rewrite sq_eqb_lit by lia. replace (tx =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    do 3 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CSx : cstr_at rsegs mm tx s) by
        (eapply p1u_cstr_munch; [exact CS | exact MUW |];
         unfold cstr_span in APtc |- *; cbn [disjoint_from]; repeat split; (exact I || lia))
    end.
    destruct (p1u_cstr_first _ tx s CSx) as (tb & RDT & TB0 & TB1).
    assert (HB0 : bv_unsigned tb = 0 -> s = []).
    { intros E. destruct (list_eq_dec Z.eq_dec s []) as [He|Hne]; [exact He|].
      exfalso. exact (TB1 Hne E). }
    pose proof (bv_unsigned_in_range 8 tb) as RTB. change (bv_modulus 8) with 256 in RTB.
    do 3 zstep.
    (* the environment at the two exits, from the frame that is now in place *)
    assert (ENVX : forall (mm : word -> option byte) (csx : list cell) (fcx : bv 32),
              rw_cells rsegs mm (S + -1056) csx ->
              (Z.of_nat (cells_size csx) = 1056) ->
              cell_at csx 952%nat = Some (C8 s11) -> cell_at csx 960%nat = Some (C8 s10) ->
              cell_at csx 968%nat = Some (C8 s9) -> cell_at csx 976%nat = Some (C8 s8) ->
              cell_at csx 984%nat = Some (C8 s7) -> cell_at csx 992%nat = Some (C8 s6) ->
              cell_at csx 1000%nat = Some (C8 s5) -> cell_at csx 1008%nat = Some (C8 s4) ->
              cell_at csx 1016%nat = Some (C8 s3) -> cell_at csx 1024%nat = Some (C8 s2) ->
              cell_at csx 1032%nat = Some (C8 s1) -> cell_at csx 1040%nat = Some (C8 s0) ->
              cell_at csx 1048%nat = Some (C8 ra) ->
              munch [(S - 7088, S); (c + 16512, c + 16612)] m mm ->
              stk rsegs mm lo (S - 7088) -> stk rsegs mm (S - 7088) (S + -1056) ->
              mem_inv rsegs mm -> frm0 fcx ->
              pf_env mm fcx (S + -1056) lo c vv).
    { intros mm csx fcx FRx LSZ C952 C960 C968 C976 C984 C992 C1000 C1008 C1016 C1024 C1032 C1040 C1048
             MUx STa STb MIx FRMx.
      assert (STfr : stk rsegs mm (S + -1056) S).
      { pose proof (stk_of_rw_cells rsegs mm _ _ FRx) as H. replace (S + -1056 + Z.of_nat (cells_size csx))
          with S in H by lia. exact H. }
      assert (STfull : stk rsegs mm lo S)
        by (eapply stk_merge; [eapply stk_merge; [exact STa | exact STb | lia] | exact STfr | lia]).
      unfold pf_env, PARSE_FILE_FRAME, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, SEG_C_SIZE, apart.
      split; [exact Hc0|]. split; [exact Hc16|]. split; [lia|]. split; [exact IMGc|].
      split.
      { unfold printf_env. split; [exact FRMx|].
        split; [eapply p1u_task_munch; [exact TM | exact MUx | exact PRES]|].
        split.
        { split; [|exists gcan].
          - unfold SA, SEG_UBSAN. cbn [sa_got_guard sa_guard].
            eapply bytes_at_transport; [exact SG1 | exact MUx |].
            pose proof (length_le8 (Z_to_bv 64 342048)) as L8.
            replace (Z.of_nat (length (le8 (Z_to_bv 64 342048)))) with 8 by lia. apply DJG; lia.
          - unfold SA, SEG_UBSAN. cbn [sa_guard].
            eapply bytes_at_transport; [exact SG2 | exact MUx |].
            pose proof (length_le8 gcan) as L8.
            replace (Z.of_nat (length (le8 gcan))) with 8 by lia. apply DJG; lia. }
        unfold SA, SEG_UBSAN. cbn [sa_img_end]. split; lia. }
      split.
      { intros a Ha. rewrite <- (CAT a Ha). unfold mrd.
        unfold SA, SEG_UBSAN in Ha. cbn [sa_catalogue] in Ha. unfold CAT_BYTES in Ha.
        assert (Q : mm (wa a) = m (wa a)).
        { apply MUx. rewrite wa_unsigned by lia. eapply disjoint_outside; [|exact Ha]. apply DJG; lia. }
        rewrite Q. reflexivity. }
      split.
      { unfold PARSE_FILE_FRAME. replace (S + -1056 + 1056) with S by lia.
        split; [exact STfull|]. split; [lia|]. split; [exact HSP16|].
        intros a Ha. exact (HNR a Ha). }
      split; [exact MIx|].
      unfold PF_SAVE, vv, sv_list. cbn [sv_s11 sv_s10 sv_s9 sv_s8 sv_s7 sv_s6 sv_s5 sv_s4 sv_s3 sv_s2
        sv_s1 sv_s0 sv_ra].
      replace (S + -1056 + 952) with (S + -1056 + Z.of_nat 952%nat) by lia.
      eapply (p1u_saved13_cells mm (S + -1056) csx 952%nat); try eassumption. }
    zstep.
    rewrite sq_eqb_lit by lia.
    destruct (Z.eqb_spec (bv_unsigned tb) 0) as [EZ|ENZ]; cbv iota.
    - (* the text is empty: DONE at 0x15c30 *)
      assert (ES : s = []) by (apply HB0; exact EZ).
      assert (Ercf : rcf = pf_start rc lab) by (unfold rcf; rewrite ES; reflexivity).
      eapply evt_mono.
      { eapply HD.
        - rewrite unsigned_lit by lia. eapply ENVX; try eassumption;
            try (cells_cbv; reflexivity); try (cbn [cells_size csize Nat.add]; reflexivity).
        - exists (BP ++ (pf_bytes (Tw ++ [0]) ++ BR2)
            ++ le4 (Z_to_bv 64 (rc_gen rc + 1)) ++ BQ).
          split; [|exact ENC0].
          apply bytes_at_app. split; [exact BCP2|].
          replace (c + Z.of_nat (length BP)) with (c + 16512) by lia.
          apply bytes_at_app. split.
          * apply bytes_at_app. split; [exact BRW|].
            replace (c + 16512 + Z.of_nat (length (pf_bytes (Tw ++ [0])))) with
                    (c + 16512 + (Z.of_nat (length Tw) + 1)) by lia.
            exact BCR22.
          * replace (c + 16512 + Z.of_nat (length (pf_bytes (Tw ++ [0]) ++ BR2))) with (c + 16608)
              by (rewrite length_app; lia).
            apply bytes_at_app. split; [exact BGN|].
            pose proof (length_le4 (Z_to_bv 64 (rc_gen rc + 1))) as L4.
            replace (c + 16608 + Z.of_nat (length (le4 (Z_to_bv 64 (rc_gen rc + 1))))) with (c + 16612) by lia.
            exact BCQ2.
        - rewrite unsigned_lit by lia. unfold PF_NSLOT, RC_N.
          replace (S + -1056 + 88) with (S + -1056 + Z.of_nat 88%nat) by lia.
          pose proof (p1u_cell_bytes _ _ _ 88%nat _ FR2 ltac:(cells_cbv; reflexivity)) as H88.
          cbn [cbytes] in H88. exact H88. }
      intros ms' PO'. eapply p1u_weaken; [| exact WMW | | ].
      + eapply munch_weaken; [|exact MUW]. unfold sub_fp, Wpf, RC_PARSE_W, RC_N, RC_REFUSAL,
          RC_OVERFLOW, RC_READING, RC_GEN, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K.
        intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & H4 & _).
        split; [lia|]. split; [lia | exact I].
      + intros k Hk. exact (FK2 k Hk).
      + rewrite Ercf. exact PO'.
    - (* a line follows: HEAD at 0x153a8 *)
      assert (HNE : s <> []) by (intros ES; apply ENZ; apply TB0; exact ES).
      do 37 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (CSh : cstr_at rsegs mm tx s) by
          (eapply p1u_cstr_munch; [exact CS | exact MUW |];
           unfold cstr_span in APtc |- *; cbn [disjoint_from]; repeat split; (exact I || lia))
      end.
      assert (HLS : (0 < length s)%nat)
        by (destruct s as [|x0 s0']; [exfalso; apply HNE; reflexivity | cbn [length]; lia]).
      eapply evt_mono.
      { pose proof (HH (length (skipn 0 s))) as HHn. unfold H_HEAD in HHn.
        eapply HHn with (cur := None) (nm := []) (rc := pf_start rc lab) (o := 0%nat) (ln := 0) (d := []).
        - split.
          { rewrite unsigned_lit by lia. eapply ENVX; try eassumption;
              try (cells_cbv; reflexivity); try (cbn [cells_size csize Nat.add]; reflexivity). }
          split.
          { rewrite unsigned_lit by lia. unfold pf_text, PARSE_FILE_FRAME, apart, SEG_C_SIZE.
            split; [exact Ht0|]. split; [exact CSh|]. split; [exact LS|]. split; [lia | exact APtc]. }
          split.
          { rewrite unsigned_lit by lia.
            unfold pf_spill, PF_CSLOT, RC_OVERFLOW, PF_LOWM, PF_LOW, RC_GEN, RC_READING, RC_N, PF_BUF,
              PF_STR_LONG, PF_STR_BLANKS.
            replace (S + -1056 + 400) with (S + -656) by lia.
            replace (S + -1056 + 160) with (S + -896) by lia.
            replace (S + -1056 + 424) with (S + -632) by lia.
            rewrite <- !p1u_notz by lia.
            split.
            { replace (S + -1056 + 16) with (S + -1056 + Z.of_nat 16%nat) by lia.
              eapply (p1u_saved_cells _ _ _ _ 16%nat FR2); [| lia | cbn [length]; lia].
              intros j w E.
              do 10 (destruct j as [|j]; cbn [nth_error] in E;
                     [injection E as <-; cbn [Nat.mul Nat.add]; cells_cbv; reflexivity|]).
              destruct j; cbn [nth_error] in E; discriminate E. }
            split.
            { replace (S + -1056 + 112) with (S + -1056 + Z.of_nat 112%nat) by lia.
              eapply (p1u_saved_cells _ _ _ _ 112%nat FR2); [| lia | cbn [length]; lia].
              intros j w E.
              do 3 (destruct j as [|j]; cbn [nth_error] in E;
                    [injection E as <-; cbn [Nat.mul Nat.add]; cells_cbv; reflexivity|]).
              destruct j; cbn [nth_error] in E; discriminate E. }
            replace (S + -1056 + 144) with (S + -1056 + Z.of_nat 144%nat) by lia.
            pose proof (p1u_cell_bytes _ _ _ 144%nat _ FR2 ltac:(cells_cbv; reflexivity)) as H144.
            cbn [cbytes] in H144. exact H144. }
          split; [exact (pf_lctx_start s)|].
          replace (tx + Z.of_nat 0) with tx by lia. exact CSh.
        - rewrite unsigned_lit by lia. unfold pf_state, PF_NAMEBUF.
          split.
          { exists (BP ++ (pf_bytes (Tw ++ [0]) ++ BR2) ++ le4 (Z_to_bv 64 (rc_gen rc + 1)) ++ BQ).
            split; [|exact ENC0].
            apply bytes_at_app. split; [exact BCP2|].
            replace (c + Z.of_nat (length BP)) with (c + 16512) by lia.
            apply bytes_at_app. split.
            * apply bytes_at_app. split; [exact BRW|].
              replace (c + 16512 + Z.of_nat (length (pf_bytes (Tw ++ [0])))) with
                      (c + 16512 + (Z.of_nat (length Tw) + 1)) by lia.
              exact BCR22.
            * replace (c + 16512 + Z.of_nat (length (pf_bytes (Tw ++ [0]) ++ BR2))) with (c + 16608)
                by (rewrite length_app; lia).
              apply bytes_at_app. split; [exact BGN|].
              pose proof (length_le4 (Z_to_bv 64 (rc_gen rc + 1))) as L4.
              replace (c + 16608 + Z.of_nat (length (le4 (Z_to_bv 64 (rc_gen rc + 1))))) with (c + 16612) by lia.
              exact BCQ2. }
          split; [exact I|].
          split.
          { exists (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0)). split.
            - apply (p1u_glue8 _ _ (S + -1056 + 944)); [lia| |].
              + replace (S + -1056 + 936) with (S + -1056 + Z.of_nat 936%nat) by lia.
                pose proof (p1u_cell_bytes _ _ _ 936%nat _ FR2 ltac:(cells_cbv; reflexivity)) as H936.
                cbn [cbytes] in H936. exact H936.
              + replace (S + -1056 + 944) with (S + -1056 + Z.of_nat 944%nat) by lia.
                pose proof (p1u_cell_bytes _ _ _ 944%nat _ FR2 ltac:(cells_cbv; reflexivity)) as H944.
                cbn [cbytes] in H944. exact H944.
            - split; [vm_compute; reflexivity|]. split; [cbn [length]; lia|].
              split; [intros []|]. vm_compute. reflexivity. }
          apply pf_cnt_start; [exact Href | exact Hovf |].
          cbn [skipn]. exact LS.
        - exact HLS.
        - cbn [skipn]. apply Nat.le_refl.
        - unfold pf_regs. split; [f_equal; lia|]. repeat split.
        - rewrite unsigned_lit by lia. unfold pf_curslot, PF_CURSLOT, pf_cur_ptr.
          replace (S + -1056 + 136) with (S + -1056 + Z.of_nat 136%nat) by lia.
          pose proof (p1u_cell_bytes _ _ _ 136%nat _ FR2 ltac:(cells_cbv; reflexivity)) as H136.
          cbn [cbytes] in H136. exact H136. }
      intros ms' PO'. unfold pf_fin in PO'. cbn [fst] in PO'.
      eapply p1u_weaken; [| exact WMW | | ].
      + eapply munch_weaken; [|exact MUW]. unfold sub_fp, Wpf, RC_PARSE_W, RC_N, RC_REFUSAL,
          RC_OVERFLOW, RC_READING, RC_GEN, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K.
        intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & H4 & _).
        split; [lia|]. split; [lia | exact I].
      + intros k Hk. exact (FK2 k Hk).
      + exact PO'. }
  (* the label dispatch at 0x152c0 *)
  zstep.
  rewrite sq_eqb_lit by lia.
  destruct lab as [l|] eqn:El.
  - destruct OLAB as [Hlp0 OCS].
    replace (lp =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
    destruct LABF as (LL & LA1 & LA2).
    assert (LLz : Z.of_nat (length l) <= 65535).
    { apply Nat2Z.inj_le in LL. assert (E : Z.of_nat 65535%nat = 65535) by reflexivity.
      rewrite E in LL. exact LL. }
    unfold apart, RC_READING in LA1, LA2.
    apply (MID _ lp l); try lia; try reflexivity.
    eapply p1u_cstr_munch; [exact OCS | exact MUF |].
    unfold cstr_span. cbn [disjoint_from]. repeat split; (exact I || lia).
  - replace (lp =? 0) with true by (symmetry; apply Z.eqb_eq; exact OLAB). cbn [negb]. cbv iota.
    do 2 zstep.
    pose proof p1u_base_len as LB12.
    apply (MID _ STR_BASE S_base); unfold STR_BASE; try lia; try reflexivity;
      [ apply p1u_base_at; exact MI
      | pose proof (p1u_apart_img c 16616 (c + 16512) 100 66659 20 IMGc ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(lia) ltac:(lia)) as D; lia ].
Qed.

End Entry.

Theorem pf_p1_holds : snprintf_contract -> S_P1.
Proof.
  intros HSN. split; [exact p1u_done|].
  intros HH HD. unfold H_ENTRY, reac_segconf_parse_file_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo rc s lab PRE.
  pose proof (bv_unsigned_in_range 64 sp) as RS. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  change (bv_modulus 64) with (2 ^ 64) in RS, Ra0, Ra1, Ra2.
  rewrite (L_parse_start_holds rc s lab). cbn [fst snd].
  pose proof (Z_to_bv_bv_unsigned sp) as Esp. pose proof (Z_to_bv_bv_unsigned a0) as Ea0.
  pose proof (Z_to_bv_bv_unsigned a1) as Ea1. pose proof (Z_to_bv_bv_unsigned a2) as Ea2.
  set (SS := bv_unsigned sp) in *. set (cc := bv_unsigned a0) in *.
  set (txx := bv_unsigned a1) in *. set (lpp := bv_unsigned a2) in *.
  rewrite <- Esp, <- Ea0, <- Ea1, <- Ea2. clearbody SS cc txx lpp.
  exact (p1u_entry ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo cc txx lpp SS rc s lab
           HSN HH HD PRE RS Ra0 Ra1 Ra2 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Qed.
