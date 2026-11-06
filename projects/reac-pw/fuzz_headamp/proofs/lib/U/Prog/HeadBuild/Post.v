(** The end of the inlined pod builder of LLVMFuzzerTestOneInput (UBSan image, 0x13fbc -> 0x140e0): the top size
    word (pod.h:440), the corruption (pod.h:441-448) and the length the duplicate is asked for (fuzz.h:73). The
    UBSan checks on the way are not taken: the cursor's (`cursor + 1 <=u 1`, 0x13fe8, 0x14010, 0x14028, 0x14040,
    0x14090), and the two on buf[off + k] (`off + k >= 16384`, 0x140ac, and `~pp <u off + k`, 0x140b4).
    [post_holds] is the statement HeadBuild/Cut.v fixes for this piece.

    The walk is proved backwards from its end: [tail_ok] (0x140d8, the length in a0 and the postcondition),
    [corr_wr_ok] (0x140cc, pp->corrupt = 1), [loop_ok] (0x1407c, the copy loop, by induction on its counter),
    [mid_ok] (0x13fdc, the tests that decide whether the record is corrupted at all) and [top_ok] (0x13fbc, the
    four byte stores of the top size word). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c
  reac_headamp_prop_parse_result_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import Facts Cut.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** ** Words *)
(** `seqz a0,s3` for a length that is not 0. *)
Lemma sltiu1_pos : forall z, 0 < z < 2^64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z H. unfold v_sltiu. rewrite (unsigned_lit z) by lia.
  replace (bv_wrap 64 1) with 1 by reflexivity.
  rewrite (proj2 (Z.ltb_ge z 1)) by lia. reflexivity.
Qed.

(** `remu` of two words that fit, the divisor not 0. *)
Lemma remu_lit : forall X D : Z, 0 <= X < 2^64 -> 0 < D < 2^64 ->
  mul_div M_REMU (Z_to_bv 64 X) (Z_to_bv 64 D) = Z_to_bv 64 (X mod D).
Proof.
  intros X D HX HD.
  change (mul_div M_REMU (Z_to_bv 64 X) (Z_to_bv 64 D))
    with (if (bv_unsigned (Z_to_bv 64 D) =? 0)%Z then Z_to_bv 64 X else bv_modu (Z_to_bv 64 X) (Z_to_bv 64 D)).
  rewrite (unsigned_lit D) by lia. rewrite (proj2 (Z.eqb_neq D 0)) by lia.
  apply bv_eq. rewrite bv_modu_unsigned. rewrite (unsigned_lit X) by lia. rewrite (unsigned_lit D) by lia.
  pose proof (Z.mod_pos_bound X D ltac:(lia)) as HM.
  rewrite (unsigned_lit (X mod D)) by lia. reflexivity.
Qed.

(** ~pp as an unsigned word (the cell sp + 0x18, the bound of the pointer-overflow check). *)
Lemma lnot_unsigned : forall p, 0 <= p < 2^64 -> bv_unsigned (Z_to_bv 64 (Z.lnot p)) = 2^64 - 1 - p.
Proof.
  intros p Hp. rewrite unsigned_lit_wrap.
  replace (Z.lnot p) with (- p - 1) by (rewrite Z.lnot_eq_pred_opp; lia).
  rewrite (umod_neg (- p - 1)) by lia. lia.
Qed.

(** `srli t0,a6,14` of an index below 16384. *)
Lemma shr14_small : forall z, 0 <= z < 16384 -> Z.shiftr z 14 = 0.
Proof.
  intros z Hz. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2^14) with 16384. lia.
Qed.

(** ** Bytes *)
Lemma byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma le1_zxb : forall b : byte, le1 (zxb b) = [b].
Proof. intros b. unfold zxb. rewrite le1_lit. f_equal. apply byte_self. Qed.

Lemma le4_lit32 : forall x, le4 (Z_to_bv 64 x) = le32 x.
Proof. intros x. unfold le4, le32. rewrite unsigned_lit_wrap. apply Z_to_le_bytes_mod. cbn. lia. Qed.

(** A byte masked by 0xf / 0x7. *)
Lemma land15 : forall b : byte, Z.land (bv_unsigned (zxb b)) 15 = bv_unsigned b mod 16.
Proof.
  intros b. pose proof (byte_range b). unfold zxb. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  change 15 with (Z.ones 4). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma land7 : forall b : byte, Z.land (bv_unsigned (zxb b)) 7 = bv_unsigned b mod 8.
Proof.
  intros b. pose proof (byte_range b). unfold zxb. rewrite (unsigned_lit (bv_unsigned b)) by lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

(** The two bytes of the offset, low byte first (`slli a3,a3,8 ; or a3,a3,a4`). *)
Lemma or16 : forall (xlo xhi : byte),
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb xhi)) 8))) (bv_unsigned (zxb xlo))
  = bv_unsigned xlo + 256 * bv_unsigned xhi.
Proof.
  intros xlo xhi. pose proof (byte_range xlo). pose proof (byte_range xhi). unfold zxb.
  rewrite (unsigned_lit (bv_unsigned xhi)) by lia. rewrite (unsigned_lit (bv_unsigned xlo)) by lia.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned xhi) 8))
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
  rewrite Z.lor_comm, lor_low_shiftl by lia. lia.
Qed.

(** ** Lists *)
Lemma overwrite_nil : forall (l : list byte) o, overwrite l o [] = l.
Proof. intros l o. unfold overwrite. cbn [app length]. rewrite Nat.add_0_r. apply firstn_skipn. Qed.

Lemma overwrite4 : forall (l : list byte) b0 b1 b2 b3, (4 <= length l)%nat ->
  overwrite (overwrite (overwrite (overwrite l (Z.to_nat 0) [b0]) (Z.to_nat 1) [b1]) (Z.to_nat 2) [b2])
            (Z.to_nat 3) [b3]
  = overwrite l 0%nat [b0; b1; b2; b3].
Proof.
  intros l b0 b1 b2 b3 H.
  destruct l as [|a0 [|a1 [|a2 [|a3 l]]]]; cbn [length] in H; try lia. reflexivity.
Qed.

Lemma ovr_snoc : forall (l bs : list byte) (o i : Z) (x : byte),
  0 <= o -> i = o + Z.of_nat (length bs) -> (Z.to_nat o + length bs + 1 <= length l)%nat ->
  overwrite (overwrite l (Z.to_nat o) bs) (Z.to_nat i) [x] = overwrite l (Z.to_nat o) (bs ++ [x]).
Proof.
  intros l bs o i x Ho -> Hl.
  replace (Z.to_nat (o + Z.of_nat (length bs))) with (Z.to_nat o + length bs)%nat by lia.
  apply overwrite_adj. cbn [length]. lia.
Qed.

Lemma app_snoc : forall (l t : list byte) (x : byte), l ++ x :: t = (l ++ [x]) ++ t.
Proof. intros l t x. rewrite <- app_assoc. reflexivity. Qed.

(** ** The cursor's reads *)
Lemma fuzz_u8s_cons : forall n (x : byte) (l : list byte),
  fst (fuzz_u8s (S n) (x :: l)) = x :: fst (fuzz_u8s n l).
Proof.
  intros n x l. cbn [fuzz_u8s fuzz_u8]. destruct (fuzz_u8s n l) as [bs r]. cbn [fst].
  f_equal. apply byte_self.
Qed.

Lemma fuzz_u8s_nil : forall n, fst (fuzz_u8s (S n) []) = Z_to_bv 8 0 :: fst (fuzz_u8s n []).
Proof. intros n. cbn [fuzz_u8s fuzz_u8]. destruct (fuzz_u8s n []) as [bs r]. reflexivity. Qed.

Lemma min0_nat : forall a z, a = 0 -> Z.to_nat (Z.min a z) = 0%nat.
Proof. intros a z ->. lia. Qed.

(** ** The corruption step, once its tests are decided *)
Lemma corr_test_true : forall c len, c mod 16 = 15 -> 8 < len -> (c mod 16 =? 15) && (8 <? len) = true.
Proof. intros c len Hc Hl. rewrite Hc. apply andb_true_intro. split; [reflexivity | apply Z.ltb_lt; lia]. Qed.

Lemma corr_none_nil : forall len, fst (corr_step len []) = None.
Proof. intros len. reflexivity. Qed.

Lemma corr_none : forall len (c : byte) (r1 : list byte), bv_unsigned c mod 16 <> 15 \/ len <= 8 ->
  fst (corr_step len (c :: r1)) = None.
Proof.
  intros len c r1 H. unfold corr_step. cbn [fuzz_u8].
  replace ((bv_unsigned c mod 16 =? 15) && (8 <? len)) with false; [reflexivity|].
  symmetry. apply andb_false_iff.
  destruct H as [H|H]; [left; apply Z.eqb_neq; exact H | right; apply Z.ltb_ge; lia].
Qed.

(** Fewer than four bytes left: the offset reads what is there, the count reads 0, no byte is written. *)
Lemma corr_short : forall len (c : byte) (r1 : list byte), (length r1 <= 2)%nat ->
  bv_unsigned c mod 16 = 15 -> 8 < len ->
  fst (corr_step len (c :: r1)) = Some (8 + fst (fuzz_u16 r1) mod (len - 8), []).
Proof.
  intros len c r1 Hl Hc H8.
  destruct r1 as [|x1 [|x2 [|x3 r]]]; cbn [length] in Hl; try lia;
    unfold corr_step; cbn [fuzz_u8 fuzz_u16]; rewrite (corr_test_true _ _ Hc H8); cbv beta iota zeta;
    rewrite min0_nat by reflexivity; reflexivity.
Qed.

(** Four bytes or more: the offset, the count, and the bytes the loop copies. *)
Lemma corr_some4 : forall len (c x1 x2 x3 : byte) (r4 : list byte),
  bv_unsigned c mod 16 = 15 -> 8 < len ->
  fst (corr_step len (c :: x1 :: x2 :: x3 :: r4)) =
  Some (8 + (bv_unsigned x1 + 256 * bv_unsigned x2) mod (len - 8),
        fst (fuzz_u8s (Z.to_nat (Z.min (bv_unsigned x3 mod 8)
                                       (len - (8 + (bv_unsigned x1 + 256 * bv_unsigned x2) mod (len - 8)))))
               r4)).
Proof.
  intros len c x1 x2 x3 r4 Hc H8. unfold corr_step. cbn [fuzz_u8 fuzz_u16].
  rewrite (corr_test_true _ _ Hc H8). cbv beta iota zeta.
  destruct (fuzz_u8s _ r4) as [bs r5]. reflexivity.
Qed.

Lemma off_bound : forall len o, 8 < len -> 8 <= 8 + o mod (len - 8) < len.
Proof. intros len o H. pose proof (Z.mod_pos_bound o (len - 8) ltac:(lia)). lia. Qed.

(** ** The block's image in this piece: the object's bytes, the fields of the record, the corrupt flag *)
Definition imgc (sh : Z) (ps : list (Z * pval)) (b : list byte) (c : bool) : list byte :=
  pp_image b (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
    (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) c.

Lemma pc_image_imgc : forall sh ps,
  pc_image (PbCut sh ps None) = imgc sh ps (pc_buf (PbCut sh ps None)) false.
Proof.
  intros sh ps. unfold pc_image, imgc. cbn [pc_shape pc_props]. rewrite (pc_ents_final sh ps None).
  reflexivity.
Qed.

Lemma pp_bytes_none : forall sh ps,
  pp_bytes (PodRec sh ps None) = imgc sh ps (pod_encode (PodRec sh ps None)) false.
Proof. reflexivity. Qed.

Lemma pp_bytes_some : forall sh ps off bs,
  pp_bytes (PodRec sh ps (Some (off, bs)))
  = imgc sh ps (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs) true.
Proof. reflexivity. Qed.

Lemma buf_none : forall sh ps, buf (PodRec sh ps None) = pod_encode (PodRec sh ps None).
Proof. reflexivity. Qed.

Lemma buf_some : forall sh ps off bs,
  buf (PodRec sh ps (Some (off, bs))) = overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs.
Proof. reflexivity. Qed.

Lemma imgc_patch : forall sh ps b o x c, (o + length x <= length b)%nat ->
  imgc sh ps (overwrite b o x) c = overwrite (imgc sh ps b c) o x.
Proof. intros sh ps b o x c H. unfold imgc. apply pp_image_patch. exact H. Qed.

(** What a state the property loop can reach gives about the object's bytes. *)
Lemma wf_facts : forall sh ps, pc_wf sh ps ->
  8 <= Z.of_nat (length (pc_buf (PbCut sh ps None))) <= 5440 /\
  length (pod_encode (PodRec sh ps None)) = length (pc_buf (PbCut sh ps None)) /\
  (length (ents (PodRec sh ps None)) <= 32)%nat /\
  Forall (fun e => (length (e_body e) <= 96)%nat) (ents (PodRec sh ps None)).
Proof.
  intros sh ps (Hs & Hk & He & Hl).
  assert (Hv : Forall (fun kv => pval_wf (snd kv)) ps)
    by (eapply Forall_impl; [|exact Hk]; intros kv (_ & H); exact H).
  destruct (pc_buf_len_none sh ps Hv He) as (HB & HD).
  assert (H4 : (4 <= length (pc_buf (PbCut sh ps None)))%nat).
  { unfold pc_buf. cbn [pc_shape pc_props pc_open]. rewrite length_app, length_le32. lia. }
  assert (HPE : length (pod_encode (PodRec sh ps None)) = length (pc_buf (PbCut sh ps None))).
  { rewrite <- (pc_buf_top sh ps). apply length_overwrite. rewrite length_le32. lia. }
  assert (HR : pod_rec_wf (PodRec sh ps None)).
  { unfold pod_rec_wf. cbn [p_shape p_props p_corr].
    split; [exact Hs|]. split; [exact Hk|]. split; [exact He|]. split; [exact Hl|].
    split; [rewrite HPE; lia | exact I]. }
  destruct (ents_wf (PodRec sh ps None) HR) as (HE1 & HE2).
  split; [|split; [exact HPE | split; [exact HE1|]]].
  - destruct HD as (c & Hc). lia.
  - eapply Forall_impl; [|exact HE2]. intros e (_ & Hb & Hsz). lia.
Qed.

(** pp->corrupt = 1 (pod.h:447). *)
Lemma imgc_corrupt : forall sh ps b, pc_wf sh ps -> Z.of_nat (length b) <= POD_BUF_MAX ->
  overwrite (imgc sh ps b false) (Z.to_nat OFF_CORRUPT) (le32 1) = imgc sh ps b true.
Proof.
  intros sh ps b Hwf Hb. destruct (wf_facts sh ps Hwf) as (_ & _ & HE1 & HE2).
  change (le32 1) with (le32 (Z.b2z true)). unfold imgc.
  exact (pp_image_corrupt b _ _ _ _ false Hb HE1 HE2 true).
Qed.

Section Post.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo cap : Z).
Hypothesis HOK : BOK sp rest src pp lo.

(** The bounds of the block, of the input and of the frame. *)
Lemma bnds : 0 < pp /\ pp + 19744 <= lo /\ 0 <= lo /\ lo + 512 <= bv_unsigned sp /\
             bv_unsigned sp + 472 <= 2^64 /\ 0 < src /\ src + Z.of_nat (length rest) <= lo.
Proof.
  destruct HOK as (H1 & H2 & H3 & _ & H5 & H6 & H7 & H8 & _ & _).
  unfold POD_PROPS, MID_STACK, PARSE_STACK, FRAME_LOCALS in *. lia.
Qed.

Ltac pplia := unfold POD_PROPS, POD_LEN_OFF, POD_NENT_OFF, OFF_LEN, OFF_CORRUPT, POD_BUF_MAX,
                     MID_STACK, PARSE_STACK, FRAME_LOCALS in *; lia.

(** The memory this piece carries: the block, the input, the frame, and the six cells it reads or hands on. *)
Definition MP (Ib : list byte) (m1 : word -> option byte) : Prop :=
  MBr sp m rest src pp lo Ib m1 /\
  cell8 m1 (bv_unsigned sp + 0x10) fl /\ cell8 m1 (bv_unsigned sp + 0x18) (Z.lnot pp) /\
  cell8 m1 (bv_unsigned sp + 0x70) pp /\ cell8 m1 (bv_unsigned sp + 0x68) (pp + POD_NENT_OFF) /\
  cell8 m1 (bv_unsigned sp + 0x78) (pp + POD_LEN_OFF) /\ cell8 m1 (bv_unsigned sp + 0x8) cap.

Lemma MP_len : forall Ib m1, MP Ib m1 -> Z.of_nat (length Ib) = POD_PROPS.
Proof. intros Ib m1 (MB & _). destruct (MBr_bounds _ _ _ _ _ _ _ _ MB) as (_ & _ & H). exact H. Qed.

(** A store into the block keeps it. *)
Lemma MP_store_w : forall Ib m1 (w : word) (o : Z) bs, MP Ib m1 -> w = Z_to_bv 64 (pp + o) -> 0 <= o ->
  o + Z.of_nat (length bs) <= POD_PROPS ->
  MP (overwrite Ib (Z.to_nat o) bs) (write_to_mem m1 w bs).
Proof.
  intros Ib m1 w o bs HMP -> Ho Hl.
  pose proof (MP_len Ib m1 HMP) as HL.
  destruct HMP as (MB & C1 & C2 & C3 & C4 & C5 & C6).
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  change (Z_to_bv 64 (pp + o)) with (wa (pp + o)).
  split; [eapply MBr_pp_store; [exact HOK | exact MB | exact Ho | lia]|].
  unfold cell8 in *. unfold POD_PROPS in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  all: eapply bytes_at_write_other; [eassumption | lia | lia | right; lia].
Qed.

Lemma MP_ok_w : forall Ib m1 (w : word) (o : Z) (j : nat), MP Ib m1 -> w = Z_to_bv 64 (pp + o) -> 0 <= o ->
  o + Z.of_nat j <= POD_PROPS -> store_ok rsegs m1 w j = true.
Proof. intros Ib m1 w o j (MB & _) -> Ho Hj. eapply MBr_pp_ok; [exact MB | exact Ho | exact Hj]. Qed.

(** The length word of the block, as the code reloads it. *)
Lemma MP_len_read : forall sh ps b c m1, MP (imgc sh ps b c) m1 -> Z.of_nat (length b) <= POD_BUF_MAX ->
  ov_read_bytes rsegs m1 (Z_to_bv 64 (pp + POD_LEN_OFF)) 8 = Some (le8 (Z_to_bv 64 (Z.of_nat (length b)))).
Proof.
  intros sh ps b c m1 HMP Hb.
  pose proof (MP_len _ _ HMP) as HL. destruct HMP as (MB & _).
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + OFF_LEN)) 8
               = Some (firstn 8 (skipn (Z.to_nat OFF_LEN) (imgc sh ps b c))))
    by (eapply MBr_read; [exact MB | unfold OFF_LEN; lia | unfold OFF_LEN, POD_PROPS in *; lia]).
  unfold imgc in HR. rewrite pp_image_slice_len in HR by exact Hb.
  rewrite le8_lit64. change (Z_to_bv 64 (pp + POD_LEN_OFF)) with (wa (pp + OFF_LEN)). exact HR.
Qed.

(** ** The input the cursor still has *)
Lemma cur_facts : forall r, suffix rest r ->
  src <= cur rest src r /\ cur rest src r + Z.of_nat (length r) = src + Z.of_nat (length rest).
Proof. intros r (k & Hk & ->). unfold cur. rewrite length_skipn. lia. Qed.

Lemma suffix_skipn : forall r j, suffix rest r -> suffix rest (skipn j r).
Proof.
  intros r j (k & Hk & ->). rewrite skipn_skipn. exists (Nat.min (j + k) (length rest)). split; [lia|].
  destruct (Nat.le_gt_cases (j + k) (length rest)) as [H|H].
  - rewrite Nat.min_l by lia. reflexivity.
  - rewrite Nat.min_r by lia. rewrite !skipn_all2 by lia. reflexivity.
Qed.

(** A byte of the input at a given distance from the cursor. *)
Lemma cur_read : forall Ib m1 (r rr : list byte) (x : byte) (i : nat) (z : Z),
  MP Ib m1 -> suffix rest r -> skipn i r = x :: rr -> z = cur rest src r + Z.of_nat i ->
  ov_read_bytes rsegs m1 (wa z) 1 = Some [x].
Proof.
  intros Ib m1 r rr x i z (MB & _) (k & Hk & Hr) Hs ->.
  assert (Hki : skipn (k + i)%nat rest = x :: rr).
  { rewrite Nat.add_comm, <- skipn_skipn, <- Hr. exact Hs. }
  replace (cur rest src r + Z.of_nat i) with (src + Z.of_nat (k + i)%nat)
    by (unfold cur; rewrite Hr, length_skipn; lia).
  eapply MBr_byte; [exact MB | exact Hki].
Qed.

(** ** Tactics of this walk *)
(** A branch decided by its condition: the words are literals in range, the test is arithmetic. *)
Ltac solve_br :=
  unfold c_eq, c_ltu, bv_eqb, bv_ltu; cbn [length] in *;
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 (Z.lnot ?p))] => rewrite (lnot_unsigned p) by lia
         | |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia
         end;
  rewrite ?negb_true_iff, ?negb_false_iff;
  first [ reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia ].

Ltac br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_br]
  end.

(** The memory after a store at pp + o: the block's image overwritten, the memory named again. *)
Ltac mp_store H o :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?w ?bs) _) =>
      let H' := fresh "HMP" in
      pose proof (MP_store_w _ mm w o bs H) as H';
      specialize (H' ltac:(f_equal; pplia) ltac:(pplia)
                         ltac:(rewrite ?length_le1, ?length_le4, ?length_le8; cbn [length]; pplia));
      clear H; rename H' into H;
      let m' := fresh "m" in
      set (m' := write_to_mem mm w bs) in *; clearbody m'
  end.

(** ** 0x140d8: the length the duplicate is asked for (fuzz.h:73), and the postcondition *)
Lemma tail_ok : forall sh ps (co : option (Z * list byte))
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  MP (pp_bytes (PodRec sh ps co)) m1 ->
  s3 = Z_to_bv 64 (Z.of_nat (length (buf (PodRec sh ps co)))) ->
  0 < Z.of_nat (length (buf (PodRec sh ps co))) < 2^64 ->
  evt rsegs (QBrec sp gp tp F fc m fl pp lo cap (PodRec sh ps co))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140d8) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh ps co ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 m1
    HMP -> HL.
  (* 0x140d8 seqz a0,s3 ; 0x140dc add a0,s3,a0 *)
  step. rewrite (sltiu1_pos _ HL). step.
  apply evt_done. cbv beta delta [QBrec].
  destruct HMP as ((HI & _ & _ & _ & MU & WM & MI & ST & _) & C10 & _ & C70 & C68 & C78 & C8).
  do 25 eexists. split; [reflexivity|].
  split; [exact HI|]. split; [exact C10|]. split; [exact C70|]. split; [exact C68|].
  split; [exact C78|]. split; [exact C8|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(** The same end for a record the corruption left alone. *)
Lemma tail_none : forall sh ps
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  pc_wf sh ps -> MP (imgc sh ps (pod_encode (PodRec sh ps None)) false) m1 ->
  s3 = Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None)))) ->
  evt rsegs (QBrec sp gp tp F fc m fl pp lo cap (PodRec sh ps None))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140d8) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh ps ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 m1
    Hwf HMP ->.
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & _ & _).
  eapply tail_ok.
  - rewrite pp_bytes_none. exact HMP.
  - f_equal. rewrite buf_none, HL2. reflexivity.
  - rewrite buf_none, HL2. lia.
Qed.

(** ** 0x140cc: pp->corrupt = 1 (pod.h:447), len reloaded *)
Lemma corr_wr_ok : forall sh ps (off : Z) (bs : list byte)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  pc_wf sh ps ->
  MP (imgc sh ps (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs) false) m1 ->
  0 <= off -> (Z.to_nat off + length bs <= length (pod_encode (PodRec sh ps None)))%nat ->
  a0 = Z_to_bv 64 1 ->
  evt rsegs (QBrec sp gp tp F fc m fl pp lo cap (PodRec sh ps (Some (off, bs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140cc) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh ps off bs ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 m1
    Hwf HMP Ho Hlen ->.
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2).
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  assert (Hbl : length (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs)
                = length (pc_buf (PbCut sh ps None)))
    by (rewrite length_overwrite by exact Hlen; exact HL2).
  assert (HRD : ov_read_bytes rsegs m1 (Z_to_bv 64 (pp + POD_LEN_OFF)) 8
                = Some (le8 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))))).
  { rewrite <- Hbl. apply (MP_len_read sh ps _ false m1 HMP). rewrite Hbl. pplia. }
  pose proof HMP as (_ & _ & _ & _ & C68 & _).
  pose proof (cell8_read m1 _ _ C68) as HR68.
  (* 0x140cc ld s3,0(s7) ; 0x140d0 ld a1,0x68(sp) *)
  step. clear HRD. step. clear HR68.
  assert (HS : store_ok rsegs m1 (Z_to_bv 64 (pp + POD_NENT_OFF + 4)) 4 = true)
    by (apply (MP_ok_w _ m1 _ OFF_CORRUPT 4%nat HMP); [f_equal; pplia | pplia | pplia]).
  (* 0x140d4 sw a0,4(a1) *)
  step. clear HS.
  mp_store HMP OFF_CORRUPT.
  rewrite le4_lit32 in HMP.
  rewrite (imgc_corrupt sh ps _ Hwf) in HMP by (rewrite Hbl; pplia).
  eapply tail_ok.
  - rewrite pp_bytes_some. exact HMP.
  - f_equal. rewrite buf_some, Hbl. reflexivity.
  - rewrite buf_some, Hbl. lia.
Qed.

(** A corruption that writes no byte. *)
Lemma corr_wr_nil : forall sh ps (o : Z)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  pc_wf sh ps -> MP (imgc sh ps (pod_encode (PodRec sh ps None)) false) m1 ->
  8 < Z.of_nat (length (pc_buf (PbCut sh ps None))) -> a0 = Z_to_bv 64 1 ->
  evt rsegs (QBrec sp gp tp F fc m fl pp lo cap
               (PodRec sh ps (Some (8 + o mod (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8), []))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x140cc) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh ps o ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 m1
    Hwf HMP H8 Ha0.
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & _ & _).
  pose proof (off_bound _ o H8) as Ho.
  set (M := o mod (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8)) in *. clearbody M.
  eapply corr_wr_ok; [exact Hwf | rewrite overwrite_nil; exact HMP | lia | cbn [length]; lia | exact Ha0].
Qed.

(** ** 0x1407c: the copy loop (pod.h:445-446), by induction on the counter n & 7 the code keeps in a1 *)
Lemma loop_ok : forall (cnt : nat) sh ps (off N : Z) (bsk rr : list byte)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  pc_wf sh ps -> suffix rest rr ->
  MP (imgc sh ps (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bsk) false) m1 ->
  8 <= off -> off + Z.of_nat (length bsk) <= Z.of_nat (length (pc_buf (PbCut sh ps None))) ->
  N = Z.min (Z.of_nat cnt) (Z.of_nat (length (pc_buf (PbCut sh ps None))) - (off + Z.of_nat (length bsk))) ->
  (0 < cnt)%nat -> (cnt <= 7)%nat ->
  a0 = Z_to_bv 64 1 -> a1 = Z_to_bv 64 (Z.of_nat cnt) -> a2 = Z_to_bv 64 (Z.of_nat (length bsk)) ->
  a3 = Z_to_bv 64 off -> a4 = Z_to_bv 64 (Z.of_nat (length rr)) -> a5 = Z_to_bv 64 1 ->
  s6 = Z_to_bv 64 (cur rest src rr) ->
  evt rsegs (QBrec sp gp tp F fc m fl pp lo cap
               (PodRec sh ps (Some (off, bsk ++ fst (fuzz_u8s (Z.to_nat N) rr)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1407c) fc None m1 (seg_rom rsegs)).
Proof.
  induction cnt as [|cnt IH];
    intros sh ps off N bsk rr ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 m1
      Hwf Hsuf HMP Hoff Hle HN Hcnt Hc7 -> -> -> -> -> -> ->; [lia|].
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2).
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (cur_facts rr Hsuf) as (Hc1 & Hc2).
  assert (Hbl : length (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bsk)
                = length (pc_buf (PbCut sh ps None)))
    by (rewrite length_overwrite by lia; exact HL2).
  assert (HRD : ov_read_bytes rsegs m1 (Z_to_bv 64 (pp + POD_LEN_OFF)) 8
                = Some (le8 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))))).
  { rewrite <- Hbl. apply (MP_len_read sh ps _ false m1 HMP). rewrite Hbl. pplia. }
  (* 0x1407c ld a7,0(s7) ; 0x14080 add a6,a3,a2 ; 0x14084 bgeu a6,a7: the end of the object *)
  step. clear HRD. step. step.
  destruct (Z_le_gt_dec (Z.of_nat (length (pc_buf (PbCut sh ps None)))) (off + Z.of_nat (length bsk)))
    as [Hstop|Hgo].
  { br true.
    replace (Z.to_nat N) with 0%nat by lia. cbn [fuzz_u8s fst]. rewrite app_nil_r.
    eapply corr_wr_ok; [exact Hwf | exact HMP | lia | lia | reflexivity]. }
  br false.
  pose proof HMP as (_ & _ & C18 & _ & _).
  assert (HSok : store_ok rsegs m1 (Z_to_bv 64 (pp + (off + Z.of_nat (length bsk)))) 1 = true)
    by (apply (MP_ok_w _ m1 _ (off + Z.of_nat (length bsk)) 1%nat HMP); [reflexivity | lia | pplia]).
  (* The rest of the iteration, from 0x140a8 with the byte read (or 0 at the end of the input) in a7. *)
  assert (K : forall (x : byte) (rr2 : list byte) (t0' a4' a7' s6' : word),
             le1 a7' = [x] ->
             fst (fuzz_u8s (Z.to_nat N) rr) = x :: fst (fuzz_u8s (Z.to_nat (N - 1)) rr2) ->
             suffix rest rr2 -> a4' = Z_to_bv 64 (Z.of_nat (length rr2)) ->
             s6' = Z_to_bv 64 (cur rest src rr2) ->
             evt rsegs (QBrec sp gp tp F fc m fl pp lo cap
                          (PodRec sh ps (Some (off, bsk ++ fst (fuzz_u8s (Z.to_nat N) rr)))))
               (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 (Z.of_nat (S cnt)))
                        (Z_to_bv 64 (Z.of_nat (length bsk))) (Z_to_bv 64 off) a4' (Z_to_bv 64 1)
                        (Z_to_bv 64 (off + Z.of_nat (length bsk))) a7' s2 s3 s4 s5 s6'
                        (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x140a8) fc None m1 (seg_rom rsegs))).
  { intros x rr2 t0' a4' a7' s6' Hx Hfz Hsuf2 -> ->.
    (* 0x140a8 srli t0,a6,14 ; 0x140ac bnez t0: off + k < 16384, not taken *)
    step.
    rewrite (unsigned_lit (off + Z.of_nat (length bsk))) by lia.
    rewrite (shr14_small (off + Z.of_nat (length bsk))) by lia.
    step. br false.
    (* 0x140b0 ld t0,0x18(sp) ; 0x140b4 bltu t0,a6: off + k <= ~pp, not taken *)
    pose proof (cell8_read m1 _ _ C18) as HR18.
    step. clear HR18. step. br false.
    (* 0x140b8 add a6,s8,a6 ; 0x140bc addi a1,a1,-1 ; 0x140c0 sb a7,0(a6) *)
    step. step. step. clear HSok.
    mp_store HMP (off + Z.of_nat (length bsk)).
    rewrite Hx in HMP.
    rewrite <- imgc_patch in HMP by (rewrite Hbl; cbn [length]; lia).
    rewrite (ovr_snoc (pod_encode (PodRec sh ps None)) bsk off (off + Z.of_nat (length bsk)) x
               ltac:(lia) eq_refl ltac:(rewrite HL2; lia)) in HMP.
    (* 0x140c4 addi a2,a2,1 ; 0x140c8 bnez a1 *)
    step. step.
    rewrite Hfz, app_snoc.
    destruct cnt as [|cnt'].
    - br false.
      replace (Z.to_nat (N - 1)) with 0%nat by lia. cbn [fuzz_u8s fst]. rewrite app_nil_r.
      eapply corr_wr_ok; [exact Hwf | exact HMP | lia | rewrite length_app; cbn [length]; lia | reflexivity].
    - br true.
      eapply IH; [ exact Hwf | exact Hsuf2 | exact HMP | lia | rewrite length_app; cbn [length]; lia
                 | rewrite length_app; cbn [length]; lia | lia | lia | reflexivity | f_equal; lia
                 | f_equal; rewrite length_app; cbn [length]; lia | reflexivity | reflexivity | reflexivity
                 | reflexivity ]. }
  (* 0x14088 beqz a4: the input is used up, or not *)
  step.
  destruct rr as [|x rr'].
  - br true.
    (* 0x140a4 mv a7,zero *)
    step.
    eapply (K (Z_to_bv 8 0) []).
    + apply le1_lit.
    + replace (Z.to_nat N) with (S (Z.to_nat (N - 1))) by lia. apply fuzz_u8s_nil.
    + exact Hsuf.
    + reflexivity.
    + reflexivity.
  - br false.
    (* 0x1408c addi t0,s6,1 ; 0x14090 bgeu a5,t0: the cursor's check, not taken *)
    step. step. br false.
    (* 0x14094 lbu a7,0(s6) ; addi a4,a4,-1 ; mv s6,t0 ; j 0x140a8 *)
    assert (HRX : ov_read_bytes rsegs m1 (wa (cur rest src (x :: rr'))) 1 = Some [x])
      by (eapply cur_read with (i := 0%nat); [exact HMP | exact Hsuf | reflexivity | lia]).
    step. clear HRX. step. step. step.
    eapply (K x rr').
    + apply le1_zxb.
    + replace (Z.to_nat N) with (S (Z.to_nat (N - 1))) by lia. apply fuzz_u8s_cons.
    + exact (suffix_skipn (x :: rr') 1 Hsuf).
    + f_equal. cbn [length]. lia.
    + f_equal. unfold cur. cbn [length]. lia.
Qed.

(** ** 0x13fdc: the tests of pod.h:442-444 and the reads of the offset and the count *)
Lemma mid_ok : forall sh ps (r : list byte)
  (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  pc_wf sh ps -> suffix rest r ->
  MP (imgc sh ps (pod_encode (PodRec sh ps None)) false) m1 ->
  s2 = Z_to_bv 64 (Z.of_nat (length r)) -> s3 = Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None)))) ->
  s6 = Z_to_bv 64 (cur rest src r) ->
  evt rsegs (QBrec sp gp tp F fc m fl pp lo cap
               (PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             (Z_to_bv 64 (pp + POD_LEN_OFF)) (Z_to_bv 64 pp) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13fdc) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh ps r ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 m1
    Hwf Hsuf HMP -> -> ->.
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2).
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (cur_facts r Hsuf) as (Hc1 & Hc2).
  (* 0x13fdc beqz s2: no input left, no corruption *)
  step.
  destruct r as [|c r1].
  { br true. rewrite corr_none_nil. eapply tail_none; [exact Hwf | exact HMP | reflexivity]. }
  br false.
  (* 0x13fe0 addi a1,s6,1 ; addi a0,zero,1 ; bgeu a0,a1: the cursor's check, not taken *)
  step. step. step. br false.
  (* 0x13fec lbu a0,0(s6) ; andi a0,a0,15 ; addi a2,zero,15 ; bne a0,a2 *)
  assert (HRC : ov_read_bytes rsegs m1 (wa (cur rest src (c :: r1))) 1 = Some [c])
    by (eapply cur_read with (i := 0%nat); [exact HMP | exact Hsuf | reflexivity | lia]).
  step. clear HRC. step. rewrite land15. step. step.
  pose proof (byte_range c) as Hcr.
  destruct (Z.eq_dec (bv_unsigned c mod 16) 15) as [Hc15|Hc15]; cycle 1.
  { br true. rewrite (corr_none _ c r1 (or_introl Hc15)).
    eapply tail_none; [exact Hwf | exact HMP | reflexivity]. }
  br false.
  (* 0x13ffc addi a0,zero,9 ; bltu s3,a0: len = 8, no corruption *)
  step. step.
  destruct (Z_lt_ge_dec (Z.of_nat (length (pc_buf (PbCut sh ps None)))) 9) as [H8|H8].
  { br true. rewrite (corr_none (Z.of_nat (length (pc_buf (PbCut sh ps None)))) c r1 ltac:(right; lia)).
    eapply tail_none; [exact Hwf | exact HMP | reflexivity]. }
  br false.
  (* 0x14004 addi a0,zero,1 ; beq s2,a0: one byte only *)
  step. step.
  destruct r1 as [|x1 r2].
  { br true. rewrite (corr_short (Z.of_nat (length (pc_buf (PbCut sh ps None)))) c [] ltac:(cbn [length]; lia) Hc15 ltac:(lia)).
    eapply corr_wr_nil; [exact Hwf | exact HMP | lia | reflexivity]. }
  br false.
  (* 0x1400c addi a1,a1,1 ; bgeu a0,a1 *)
  step. step. br false.
  (* 0x14014 addi a1,zero,2 ; beq s2,a1: two bytes *)
  step. step.
  destruct r2 as [|x2 r3].
  { br true. rewrite (corr_short (Z.of_nat (length (pc_buf (PbCut sh ps None)))) c [x1] ltac:(cbn [length]; lia) Hc15 ltac:(lia)).
    eapply corr_wr_nil; [exact Hwf | exact HMP | lia | reflexivity]. }
  br false.
  (* 0x1401c addi a1,s6,2 ; addi a1,a1,1 ; addi a2,zero,1 ; bgeu a2,a1 *)
  step. step. step. step. br false.
  (* 0x1402c addi a1,zero,3 ; beq s2,a1: three bytes *)
  step. step.
  destruct r3 as [|x3 r4].
  { br true. rewrite (corr_short (Z.of_nat (length (pc_buf (PbCut sh ps None)))) c [x1; x2] ltac:(cbn [length]; lia) Hc15 ltac:(lia)).
    eapply corr_wr_nil; [exact Hwf | exact HMP | lia | reflexivity]. }
  br false.
  (* 0x14034 addi a1,s6,3 ; addi a2,a1,1 ; addi a3,zero,1 ; bgeu a3,a2 *)
  step. step. step. step. br false.
  (* 0x14044 lbu a1,0(a1) ; andi a1,a1,7 ; beqz a1: the count n & 7 *)
  assert (HR3 : ov_read_bytes rsegs m1 (wa (cur rest src (c :: x1 :: x2 :: x3 :: r4) + 3)) 1 = Some [x3])
    by (eapply cur_read with (i := 3%nat); [exact HMP | exact Hsuf | reflexivity | lia]).
  step. clear HR3. step. rewrite land7. step.
  rewrite (corr_some4 (Z.of_nat (length (pc_buf (PbCut sh ps None)))) c x1 x2 x3 r4 Hc15 ltac:(lia)).
  pose proof (byte_range x1) as Hx1. pose proof (byte_range x2) as Hx2. pose proof (byte_range x3) as Hx3.
  destruct (Z.eq_dec (bv_unsigned x3 mod 8) 0) as [Hz|Hz].
  { br true. rewrite (min0_nat _ _ Hz). cbn [fuzz_u8s fst].
    eapply corr_wr_nil; [exact Hwf | exact HMP | lia | reflexivity]. }
  br false.
  (* 0x14050 mv a2,zero ; lbu a3,2(s6) ; lbu a4,1(s6) ; slli a3,a3,8 ; or a3,a3,a4: the offset o *)
  assert (HR2 : ov_read_bytes rsegs m1 (wa (cur rest src (c :: x1 :: x2 :: x3 :: r4) + 2)) 1 = Some [x2])
    by (eapply cur_read with (i := 2%nat); [exact HMP | exact Hsuf | reflexivity | lia]).
  step. step. clear HR2.
  assert (HR1 : ov_read_bytes rsegs m1 (wa (cur rest src (c :: x1 :: x2 :: x3 :: r4) + 1)) 1 = Some [x1])
    by (eapply cur_read with (i := 1%nat); [exact HMP | exact Hsuf | reflexivity | lia]).
  step. clear HR1. step. step. rewrite or16.
  (* 0x14064 addi s3,s3,-8 ; addi a4,s2,-4 ; addi s6,s6,4 ; remu a3,a3,s3 ; addi a3,a3,8 ; addi a5,zero,1 *)
  step. step. step. step.
  rewrite (remu_lit (bv_unsigned x1 + 256 * bv_unsigned x2) (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8))
    by lia.
  step. step.
  replace (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8)
    with (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8) by lia.
  pose proof (off_bound (Z.of_nat (length (pc_buf (PbCut sh ps None)))) (bv_unsigned x1 + 256 * bv_unsigned x2)
                ltac:(lia)) as Hoff.
  set (M := (bv_unsigned x1 + 256 * bv_unsigned x2) mod (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8))
    in *.
  clearbody M.
  assert (Hsuf4 : suffix rest r4) by exact (suffix_skipn _ 4 Hsuf).
  eapply (loop_ok (Z.to_nat (bv_unsigned x3 mod 8)) sh ps _ _ [] r4).
  - exact Hwf.
  - exact Hsuf4.
  - rewrite overwrite_nil. exact HMP.
  - lia.
  - cbn [length]. lia.
  - cbn [length]. lia.
  - lia.
  - lia.
  - reflexivity.
  - f_equal. lia.
  - reflexivity.
  - f_equal. lia.
  - f_equal. cbn [length]. lia.
  - reflexivity.
  - f_equal. unfold cur. cbn [length]. lia.
Qed.

(** ** 0x13fbc: the top size word buf[0..4) = le32 (len - 8) (pod.h:440) *)
Lemma top_ok : forall sh ps (r : list byte) (ms : machine_state),
  POSTH sp gp tp F fc m rest fl src pp lo cap sh ps r ms ->
  evt rsegs (QBrec sp gp tp F fc m fl pp lo cap
               (PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r)))) ms.
Proof.
  intros sh ps r ms (ra & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s9 & s10
                     & s11 & t3 & t4 & t5 & t6 & m1 & Ems & MB & C10 & C18 & C70 & C68 & C78 & C8 & Hsuf & Hwf).
  subst ms.
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2).
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  assert (HMP : MP (imgc sh ps (pc_buf (PbCut sh ps None)) false) m1).
  { rewrite <- pc_image_imgc. split; [exact MB|]. split; [exact C10|]. split; [exact C18|].
    split; [exact C70|]. split; [exact C68|]. split; [exact C78 | exact C8]. }
  clear MB C10 C18 C70 C68 C78 C8.
  pose proof (MP_len _ _ HMP) as HLB.
  (* 0x13fbc addi a0,s3,-8 ; srli a1,a0,24 ; srli a2,a0,16 ; srli a3,a0,8 *)
  step. step. step. step.
  rewrite (unsigned_lit (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8)) by lia.
  (* 0x13fcc sb a0,0(s8) ; sb a3,1(s8) ; sb a2,2(s8) ; sb a1,3(s8) *)
  pose proof (MP_ok_w _ m1 (Z_to_bv 64 pp) 0 1%nat HMP ltac:(f_equal; lia) ltac:(lia) ltac:(pplia)) as HS.
  step. clear HS. mp_store HMP 0.
  pose proof (MP_ok_w _ _ (Z_to_bv 64 (pp + 1)) 1 1%nat HMP eq_refl ltac:(lia) ltac:(pplia)) as HS.
  step. clear HS. mp_store HMP 1.
  pose proof (MP_ok_w _ _ (Z_to_bv 64 (pp + 2)) 2 1%nat HMP eq_refl ltac:(lia) ltac:(pplia)) as HS.
  step. clear HS. mp_store HMP 2.
  pose proof (MP_ok_w _ _ (Z_to_bv 64 (pp + 3)) 3 1%nat HMP eq_refl ltac:(lia) ltac:(pplia)) as HS.
  step. clear HS. mp_store HMP 3.
  rewrite !le1_lit in HMP.
  rewrite overwrite4 in HMP by pplia.
  replace (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8)
    with (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8) in HMP by lia.
  rewrite <- le32_split in HMP.
  rewrite <- imgc_patch in HMP by (rewrite length_le32; lia).
  rewrite pc_buf_top in HMP.
  eapply mid_ok; [exact Hwf | exact Hsuf | exact HMP | reflexivity | reflexivity | reflexivity].
Qed.

End Post.

Theorem post_holds : forall sp gp tp F fc m rest fl src pp lo cap, S_post sp gp tp F fc m rest fl src pp lo cap.
Proof.
  intros sp gp tp F fc m rest fl src pp lo cap HOK sh ps r ms HP.
  eapply top_ok; eassumption.
Qed.
