(** The end of the inlined pod builder of LLVMFuzzerTestOneInput (plain image, 0x14114 -> 0x141e0): the top size
    word (pod.h:440), the corruption (pod.h:441-448) and the length the duplicate is asked for (fuzz.h:73).
    [post_holds] is the statement RateBuild/Cut.v fixes for this piece. Ported from reac-pw/fuzz_role's
    Prog/RoleBuild/Post.v at rate's registers (pp in s1, the length in
    s4, the cursor in s5) and frame cells: the store of pp->corrupt reloads &pp->n_ent from the cell sp + 0x70
    (0x141d0), and the header registers s2 s6 s7 s9 s10 s11 and the cells 0x28, 0x70, 0x80, 0xb0 reach the end as
    they are at 0x14114.

    The walk is written backwards from the end: [tail_ok] (0x141d8, the length in a0 and the postcondition),
    [corr_wr_ok] (0x141cc, pp->corrupt = 1), [loop_ok] (0x14190, the copy loop, by induction on the counter),
    [mid_ok] (0x14134, the four tests that decide whether the record is corrupted at all) and [top_ok] (0x14114,
    the four byte stores of the top size word). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog.RateBuild Require Import Facts Cut.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** ** Branch conditions of literal words *)
Lemma eqb_T : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a = b ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros a b Ha Hb H. rewrite bv_eqb_lit, !(Z.mod_small _ (2^64)) by lia. apply Z.eqb_eq. exact H. Qed.

Lemma eqb_F : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a <> b ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros a b Ha Hb H. rewrite bv_eqb_lit, !(Z.mod_small _ (2^64)) by lia. apply Z.eqb_neq. exact H. Qed.

Lemma ltu_T : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a < b ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros a b Ha Hb H. rewrite bv_ltu_lit, !(Z.mod_small _ (2^64)) by lia. apply Z.ltb_lt. exact H. Qed.

Lemma ltu_F : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> b <= a ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros a b Ha Hb H. rewrite bv_ltu_lit, !(Z.mod_small _ (2^64)) by lia. apply Z.ltb_ge. exact H. Qed.

Lemma nb_T : forall b : bool, b = false -> negb b = true.
Proof. intros b ->. reflexivity. Qed.
Lemma nb_F : forall b : bool, b = true -> negb b = false.
Proof. intros b ->. reflexivity. Qed.

(** `seqz a0,s4` for a length that is not 0. *)
Lemma sltiu1_pos : forall z, 0 < z < 2^64 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 0.
Proof.
  intros z H. unfold v_sltiu. rewrite (unsigned_lit z) by lia.
  replace (bv_wrap 64 1) with 1 by reflexivity.
  rewrite (proj2 (Z.ltb_ge z 1)) by lia. reflexivity.
Qed.

(** `remu` of two words that fit. *)
Lemma remu_lit : forall X D : Z, 0 <= X < 2^64 -> 0 < D < 2^64 ->
  Sem.mul_div Instr.M_REMU (Z_to_bv 64 X) (Z_to_bv 64 D) = Z_to_bv 64 (X mod D).
Proof.
  intros X D HX HD.
  change (Sem.mul_div Instr.M_REMU (Z_to_bv 64 X) (Z_to_bv 64 D))
    with (if (bv_unsigned (Z_to_bv 64 D) =? 0) then Z_to_bv 64 X else bv_modu (Z_to_bv 64 X) (Z_to_bv 64 D)).
  rewrite (unsigned_lit D) by lia. rewrite (proj2 (Z.eqb_neq D 0)) by lia.
  apply bv_eq. rewrite bv_modu_unsigned, !(unsigned_lit _) by lia. reflexivity.
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

(** The two bytes of the offset, low byte first. *)
Lemma lor_shift_bytes : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.lor (Z.shiftl b 8) a = a + 256 * b.
Proof. intros a b Ha Hb. rewrite Z.lor_comm, lor_low_shiftl by lia. lia. Qed.

Lemma or16 : forall (xlo xhi : byte),
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb xhi)) 8))) (bv_unsigned (zxb xlo))
  = bv_unsigned xlo + 256 * bv_unsigned xhi.
Proof.
  intros xlo xhi. pose proof (byte_range xlo). pose proof (byte_range xhi). unfold zxb.
  rewrite (unsigned_lit (bv_unsigned xhi)) by lia. rewrite (unsigned_lit (bv_unsigned xlo)) by lia.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned xhi) 8))
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
  apply lor_shift_bytes; lia.
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

(** ** The corruption step, once its test has been decided *)
Lemma corr_none_nil : forall len, fst (corr_step len []) = None.
Proof.
  intros len. unfold corr_step. cbn [fuzz_u8].
  replace ((0 mod 16 =? 15) && (8 <? len)) with false by reflexivity. reflexivity.
Qed.

Lemma corr_none : forall len (c : byte) (r1 : list byte), bv_unsigned c mod 16 <> 15 \/ len <= 8 ->
  fst (corr_step len (c :: r1)) = None.
Proof.
  intros len c r1 H. unfold corr_step. cbn [fuzz_u8].
  replace ((bv_unsigned c mod 16 =? 15) && (8 <? len)) with false; [reflexivity|].
  symmetry. apply andb_false_iff. destruct H as [H|H]; [left; apply Z.eqb_neq; exact H | right; apply Z.ltb_ge; lia].
Qed.

Lemma corr_some : forall len (c : byte) (r1 : list byte), bv_unsigned c mod 16 = 15 -> 8 < len ->
  fst (corr_step len (c :: r1)) =
  Some (8 + fst (fuzz_u16 r1) mod (len - 8),
        fst (fuzz_u8s (Z.to_nat (Z.min (fst (fuzz_u8 (skipn 2 r1)) mod 8)
                                       (len - (8 + fst (fuzz_u16 r1) mod (len - 8))))) (skipn 1 (skipn 2 r1)))).
Proof.
  intros len c r1 Hc Hl. unfold corr_step. cbn [fuzz_u8].
  rewrite Hc. replace ((15 =? 15) && (8 <? len)) with true
    by (symmetry; apply andb_true_intro; split; [reflexivity | apply Z.ltb_lt; lia]).
  cbv iota beta.
  rewrite (surjective_pairing (fuzz_u16 r1)). cbv iota beta. rewrite fuzz_u16_rest.
  rewrite (surjective_pairing (fuzz_u8 (skipn 2 r1))). cbv iota beta. rewrite (fuzz_u8_spec (skipn 2 r1)).
  cbn [snd]. cbv zeta.
  rewrite (surjective_pairing (fuzz_u8s _ _)). cbv iota beta. reflexivity.
Qed.

(** The corruption writes no byte when fewer than four bytes are left (the count byte reads 0). *)
Lemma corr_empty_tail : forall (r1 : list byte), (length r1 <= 2)%nat ->
  fst (fuzz_u8 (skipn 2 r1)) = 0.
Proof. intros r1 H. rewrite skipn_all2 by lia. reflexivity. Qed.

(** ** The record the piece ends with *)
Lemma pod_encode_co : forall sh ps co, pod_encode (PodRec sh ps co) = pod_encode (PodRec sh ps None).
Proof. intros sh ps co. reflexivity. Qed.

Lemma pp_bytes_of : forall sh ps co,
  pp_bytes (PodRec sh ps co)
  = pp_image (buf (PodRec sh ps co)) (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
      (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) (corrupt (PodRec sh ps co)).
Proof. intros sh ps co. reflexivity. Qed.

Lemma pc_image_of : forall sh ps,
  pc_image (PbCut sh ps None)
  = pp_image (pc_buf (PbCut sh ps None)) (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
      (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false.
Proof. intros sh ps. reflexivity. Qed.

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
    split; [rewrite HPE; destruct HD as (c & Hc); lia | exact I]. }
  destruct (ents_wf (PodRec sh ps None) HR) as (HE1 & HE2).
  split; [|split; [exact HPE | split; [exact HE1|]]].
  - destruct HD as (c & Hc). lia.
  - eapply Forall_impl; [|exact HE2]. intros e (_ & Hb & Hsz). lia.
Qed.

(** ** The block's image under the three writes of this piece *)
(** The top size word (pod.h:440): the object as [pod_encode] writes it. *)
Lemma img_top : forall sh ps, pc_wf sh ps ->
  overwrite (pp_image (pc_buf (PbCut sh ps None)) (is_props (PodRec sh ps None))
               (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
               (ents (PodRec sh ps None)) false)
            0%nat (le32 (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8))
  = pp_image (pod_encode (PodRec sh ps None)) (is_props (PodRec sh ps None))
      (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
      (ents (PodRec sh ps None)) false.
Proof.
  intros sh ps Hwf. destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & _ & _).
  rewrite <- pp_image_patch by (rewrite length_le32; lia).
  f_equal. apply pc_buf_top.
Qed.

(** One byte of the corruption (pod.h:446), inside the object and then inside the block. *)
Lemma img_step : forall sh ps (off i : Z) (bsk : list byte) (x : byte),
  Z.of_nat (length (pod_encode (PodRec sh ps None))) <= POD_BUF_MAX ->
  0 <= off -> i = off + Z.of_nat (length bsk) ->
  (Z.to_nat off + length bsk + 1 <= length (pod_encode (PodRec sh ps None)))%nat ->
  overwrite (pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bsk)
               (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
               (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false)
            (Z.to_nat i) [x]
  = pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (bsk ++ [x]))
      (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
      (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false.
Proof.
  intros sh ps off i bsk x Hb Ho -> Hl.
  rewrite <- pp_image_patch by (rewrite length_overwrite by lia; cbn [length]; lia).
  f_equal. apply ovr_snoc; [lia | reflexivity | lia].
Qed.

(** pp->corrupt = 1 (pod.h:447). *)
Lemma img_corrupt : forall sh ps, pc_wf sh ps -> forall (b : list byte),
  Z.of_nat (length b) <= POD_BUF_MAX ->
  overwrite (pp_image b (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
               (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false)
            (Z.to_nat OFF_CORRUPT) (le4 (Z_to_bv 64 1))
  = pp_image b (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
      (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) true.
Proof.
  intros sh ps Hwf b Hb. destruct (wf_facts sh ps Hwf) as (_ & _ & HE1 & HE2).
  rewrite le4_lit32. replace (le32 1) with (le32 (Z.b2z true)) by reflexivity.
  apply (pp_image_corrupt b _ _ _ _ false Hb HE1 HE2 true).
Qed.

Section Post.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl mask buflen b3 b4 b5 b6 src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.

(** The bounds of the block, of the input and of the frame. *)
Lemma bnds : 0 < pp /\ pp + POD_PROPS <= lo /\ 0 <= lo /\ lo + MID_STACK <= bv_unsigned sp /\
             bv_unsigned sp + FRAME_LOCALS <= 2^64 /\ 0 < src /\ src + Z.of_nat (length rest) <= lo.
Proof. destruct HOK as (H1 & H2 & H3 & _ & H5 & H6 & H7 & H8 & _ & _). repeat split; assumption. Qed.

Ltac pplia := unfold POD_PROPS, POD_LEN_OFF, POD_NENT_OFF, OFF_LEN, OFF_CORRUPT, POD_BUF_MAX,
                     MID_STACK, FRAME_LOCALS in *; lia.

(** The memory this piece carries: the block, the input, the frame, and the four cells the end keeps (b6 << 8,
    &pp->n_ent, pp, &pp->len). *)
Definition MP (Ib : list byte) (m1 : word -> option byte) : Prop :=
  MBr sp m rest src pp lo Ib m1 /\ cell8 m1 (bv_unsigned sp + 0x28) (b6 * 256) /\
  cell8 m1 (bv_unsigned sp + 0x70) (pp + POD_NENT_OFF) /\ cell8 m1 (bv_unsigned sp + 0x80) pp /\
  cell8 m1 (bv_unsigned sp + 0xb0) (pp + POD_LEN_OFF).

Lemma MP_len_block : forall Ib m1, MP Ib m1 -> Z.of_nat (length Ib) = POD_PROPS.
Proof.
  intros Ib m1 (MB & _ & _ & _ & _). pose proof MB as MB'. apply MBr_bounds in MB'.
  destruct MB' as (_ & _ & H). exact H.
Qed.

(** A store into the block keeps it. *)
Lemma MP_store : forall Ib m1 (o : Z) bs, MP Ib m1 -> 0 <= o -> (Z.to_nat o + length bs <= length Ib)%nat ->
  MP (overwrite Ib (Z.to_nat o) bs) (write_to_mem m1 (wa (pp + o)) bs).
Proof.
  intros Ib m1 o bs HMP Ho Hlen. pose proof HMP as (MB & C1 & C2 & C3 & C4).
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (MP_len_block Ib m1 HMP) as HL.
  unfold MP, cell8 in *.
  split; [eapply MBr_pp_store; first [exact HOK | exact MB | lia]|].
  split; [eapply bytes_at_write_other; first [exact C1 | rewrite length_le8; pplia | pplia]|].
  split; [eapply bytes_at_write_other; first [exact C2 | rewrite length_le8; pplia | pplia]|].
  split; [eapply bytes_at_write_other; first [exact C3 | rewrite length_le8; pplia | pplia]|].
  eapply bytes_at_write_other; first [exact C4 | rewrite length_le8; pplia | pplia].
Qed.

Lemma MP_store_at : forall Ib m1 (a o : Z) bs, MP Ib m1 -> a = pp + o -> 0 <= o ->
  (Z.to_nat o + length bs <= length Ib)%nat ->
  MP (overwrite Ib (Z.to_nat o) bs) (write_to_mem m1 (Z_to_bv 64 a) bs).
Proof. intros Ib m1 a o bs HMP -> Ho Hl. exact (MP_store Ib m1 o bs HMP Ho Hl). Qed.

Lemma MP_store_ok : forall (o : Z) (j : nat) Ib m1 (a : Z), MP Ib m1 -> a = pp + o -> 0 <= o ->
  o + Z.of_nat j <= POD_PROPS -> store_ok rsegs m1 (Z_to_bv 64 a) j = true.
Proof.
  intros o j Ib m1 a (MB & _ & _ & _ & _) -> Ho Hj.
  change (Z_to_bv 64 (pp + o)) with (wa (pp + o)). eapply MBr_pp_ok; first [exact MB | lia].
Qed.

(** The length word of the object, as the loop reloads it. *)
Lemma MP_len_read : forall b isp hasp pst es corr m1, MP (pp_image b isp hasp pst es corr) m1 ->
  Z.of_nat (length b) <= POD_BUF_MAX ->
  ov_read_bytes rsegs m1 (wa (pp + POD_LEN_OFF)) 8 = Some (le8 (Z_to_bv 64 (Z.of_nat (length b)))).
Proof.
  intros b isp hasp pst es corr m1 HMP Hb. pose proof HMP as (MB & _ & _ & _ & _).
  pose proof (MP_len_block _ _ HMP) as HL.
  assert (HR : ov_read_bytes rsegs m1 (wa (pp + OFF_LEN)) 8
               = Some (firstn 8 (skipn (Z.to_nat OFF_LEN) (pp_image b isp hasp pst es corr))))
    by (eapply MBr_read; first [exact MB | pplia]).
  replace (pp + POD_LEN_OFF) with (pp + OFF_LEN) by pplia.
  rewrite HR, (pp_image_slice_len b isp hasp pst es corr Hb), le8_lit64. reflexivity.
Qed.

(** ** The input the cursor still has *)
Lemma suffix_len : forall r, suffix rest r -> (length r <= length rest)%nat.
Proof. intros r (k & Hk & ->). rewrite length_skipn. lia. Qed.

Lemma suffix_skipn : forall r j, suffix rest r -> suffix rest (skipn j r).
Proof.
  intros r j (k & Hk & ->). rewrite skipn_skipn. exists (Nat.min (j + k) (length rest)). split; [lia|].
  destruct (Nat.le_gt_cases (j + k) (length rest)) as [H|H].
  - rewrite Nat.min_l by lia. reflexivity.
  - rewrite Nat.min_r by lia. rewrite !skipn_all2 by lia. reflexivity.
Qed.

Lemma cur_bounds : forall r, suffix rest r -> 0 < cur rest src r /\ cur rest src r + 1 < 2^64.
Proof.
  intros r Hs. pose proof (suffix_len r Hs) as Hl. pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  unfold cur. pplia.
Qed.

Lemma cur_skip : forall r j (z : Z), (j <= length r)%nat -> z = cur rest src r + Z.of_nat j ->
  cur rest src (skipn j r) = z.
Proof. intros r j z Hj ->. unfold cur. rewrite length_skipn. lia. Qed.

(** The cursor after one byte, and after the four the offset and the count take. *)
Lemma cur_cons : forall (x : byte) (rr : list byte), cur rest src (x :: rr) + 1 = cur rest src rr.
Proof. intros x rr. unfold cur. cbn [length]. lia. Qed.

Lemma cur_skip4 : forall (c x1 x2 x3 : byte) (r4 : list byte),
  cur rest src (c :: x1 :: x2 :: x3 :: r4) + 4 = cur rest src r4.
Proof. intros c x1 x2 x3 r4. unfold cur. cbn [length]. lia. Qed.

(** A byte of the input at a given distance from the cursor. *)
Lemma cur_read : forall Ib m1 (r rr : list byte) (x : byte) (i : nat) (z : Z),
  MP Ib m1 -> suffix rest r -> skipn i r = x :: rr -> z = cur rest src r + Z.of_nat i ->
  ov_read_bytes rsegs m1 (wa z) 1 = Some [x].
Proof.
  intros Ib m1 r rr x i z (MB & _ & _ & _ & _) (k & Hk & Hr) Hs ->.
  assert (Hki : skipn (k + i)%nat rest = x :: rr).
  { rewrite Nat.add_comm, <- skipn_skipn, <- Hr. exact Hs. }
  replace (cur rest src r + Z.of_nat i) with (src + Z.of_nat (k + i)%nat)
    by (unfold cur; rewrite Hr, length_skipn; lia).
  eapply MBr_byte; first [exact MB | exact Hki].
Qed.

(** ** 0x141d8: the length the duplicate is asked for, and the postcondition *)
Lemma tail_ok : forall sh ps (co : option (Z * list byte)) (Ib : list byte) (Lz : Z)
  (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  MP Ib m1 -> Ib = pp_bytes (PodRec sh ps co) -> Lz = Z.of_nat (length (buf (PodRec sh ps co))) ->
  0 < Lz < 2^64 ->
  evt rsegs (QBrec sp gp tp F fc m fl mask buflen b3 b4 b5 b6 pp lo (PodRec sh ps co))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pp) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (b4 * 256)) s3
             (Z_to_bv 64 Lz) s5 (Z_to_bv 64 fl) (Z_to_bv 64 b3) s8 (Z_to_bv 64 mask) (Z_to_bv 64 buflen)
             (Z_to_bv 64 b5) t3 t4 t5 t6)
        F (Z_to_bv 64 0x141d8) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh ps co Ib Lz ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 t3 t4 t5 t6 m1
    (MB & C28 & C70 & C80 & Cb0) -> -> HL.
  destruct MB as (HI & HLb & HW & HR & MU & WM & MI & ST & TB).
  (* 0x141d8 seqz a0,s4 ; 0x141dc add a0,s4,a0 *)
  step. step.
  rewrite (sltiu1_pos _ HL).
  replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity.
  rewrite Z.add_0_r.
  apply evt_done. unfold QBrec. do 20 eexists.
  split; [reflexivity|].
  split; [exact HI|]. split; [exact C28|]. split; [exact C70|]. split; [exact C80|]. split; [exact Cb0|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST].
Qed.

(** The branch conditions of this piece: every test compares two words that fit. *)
Ltac cnlia := try (cbn [length] in * ); lia.
Ltac cond1 := first [ apply eqb_T; cnlia | apply eqb_F; cnlia
                    | apply ltu_T; cnlia | apply ltu_F; cnlia ].
Ltac cond0 := first [ cond1 | apply nb_T; cond1 | apply nb_F; cond1 | reflexivity ].
Ltac br_true :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "Hbr" in assert (H : c = true) by cond0; rewrite H; cbv iota; clear H
  end.
Ltac br_false :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let H := fresh "Hbr" in assert (H : c = false) by cond0; rewrite H; cbv iota; clear H
  end.

(** ** 0x141cc: pp->corrupt = 1 *)
Lemma corr_wr_ok : forall sh ps (off : Z) (bs : list byte) (Lz : Z)
  (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 t3 t4 t5 t6 : word)
  (m1 : word -> option byte),
  pc_wf sh ps ->
  MP (pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs)
        (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
        (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false) m1 ->
  0 <= off -> (Z.to_nat off + length bs <= length (pod_encode (PodRec sh ps None)))%nat ->
  Lz = Z.of_nat (length (pc_buf (PbCut sh ps None))) ->
  evt rsegs (QBrec sp gp tp F fc m fl mask buflen b3 b4 b5 b6 pp lo (PodRec sh ps (Some (off, bs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pp) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (b4 * 256)) s3
             (Z_to_bv 64 Lz) s5 (Z_to_bv 64 fl) (Z_to_bv 64 b3) s8 (Z_to_bv 64 mask) (Z_to_bv 64 buflen)
             (Z_to_bv 64 b5) t3 t4 t5 t6)
        F (Z_to_bv 64 0x141cc) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh ps off bs Lz ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s8 t3 t4 t5 t6 m1
    Hwf HMP Ho Hlen ->.
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2).
  pose proof (MP_len_block _ _ HMP) as HLB.
  assert (Hbl : length (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bs)
                = length (pod_encode (PodRec sh ps None))) by (apply length_overwrite; exact Hlen).
  assert (HS : store_ok rsegs m1 (Z_to_bv 64 (pp + POD_NENT_OFF + 4)) 4 = true)
    by (eapply (MP_store_ok (POD_NENT_OFF + 4) 4); first [exact HMP | pplia]).
  pose proof HMP as (_ & _ & C70 & _ & _).
  (* 0x141cc addi a0,zero,1 *)
  step.
  (* 0x141d0 ld a1,0x70(sp) : &pp->n_ent from its frame cell *)
  pose proof (cell8_read m1 _ _ C70) as HR70. step. clear HR70 C70.
  (* 0x141d4 sw a0,4(a1) *)
  step.
  pose proof (MP_store_at _ _ (pp + POD_NENT_OFF + 4) OFF_CORRUPT (le4 (Z_to_bv 64 1)) HMP
                ltac:(pplia) ltac:(pplia) ltac:(rewrite length_le4; pplia)) as HMP2.
  rewrite (img_corrupt sh ps Hwf) in HMP2 by (rewrite Hbl; pplia).
  clear HMP HS.
  eapply tail_ok; [exact HMP2 | rewrite pp_bytes_of; reflexivity | | lia].
  cbn [buf p_corr]. rewrite pod_encode_co, length_overwrite by exact Hlen. lia.
Qed.

(** ** 0x14190: the copy loop (pod.h:445-446), by induction on the counter the code keeps *)
Lemma loop_ok : forall (cnt : nat) sh ps (off N : Z) (bsk rr : list byte)
  (ra t0 t1 t2 s0 a4 a5 a7 s3 s4 s8 t3 t4 t5 t6 : word) (m1 : word -> option byte),
  pc_wf sh ps -> suffix rest rr ->
  MP (pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bsk)
        (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
        (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false) m1 ->
  8 <= off -> off + Z.of_nat (length bsk) <= Z.of_nat (length (pc_buf (PbCut sh ps None))) ->
  N = Z.min (Z.of_nat cnt) (Z.of_nat (length (pc_buf (PbCut sh ps None))) - (off + Z.of_nat (length bsk))) ->
  (0 < cnt)%nat -> (cnt <= 7)%nat ->
  evt rsegs (QBrec sp gp tp F fc m fl mask buflen b3 b4 b5 b6 pp lo
               (PodRec sh ps (Some (off, bsk ++ fst (fuzz_u8s (Z.to_nat N) rr)))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 pp)
             (Z_to_bv 64 (Z.of_nat cnt)) (Z_to_bv 64 (Z.of_nat (length bsk))) (Z_to_bv 64 off)
             (Z_to_bv 64 (Z.of_nat (length rr))) a4 a5 (Z_to_bv 64 (pp + POD_LEN_OFF)) a7
             (Z_to_bv 64 (b4 * 256)) s3 s4 (Z_to_bv 64 (cur rest src rr))
             (Z_to_bv 64 fl) (Z_to_bv 64 b3) s8 (Z_to_bv 64 mask) (Z_to_bv 64 buflen) (Z_to_bv 64 b5)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14190) fc None m1 (seg_rom rsegs)).
Proof.
  induction cnt as [|cnt IH];
    intros sh ps off N bsk rr ra t0 t1 t2 s0 a4 a5 a7 s3 s4 s8 t3 t4 t5 t6 m1
      Hwf Hsuf HMP Hoff Hle HN Hcnt Hcnt7; [lia|].
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2).
  pose proof (MP_len_block _ _ HMP) as HLB.
  pose proof (suffix_len rr Hsuf) as Hrl.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (cur_bounds rr Hsuf) as (Hc1 & Hc2).
  assert (Hrest : Z.of_nat (length rest) + 1 < 2^64) by pplia.
  assert (Hbl : length (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) bsk)
                = length (pod_encode (PodRec sh ps None))) by (apply length_overwrite; lia).
  assert (HRD : ov_read_bytes rsegs m1 (wa (pp + POD_LEN_OFF)) 8
                = Some (le8 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))))).
  { rewrite <- HL2, <- Hbl. eapply MP_len_read; [exact HMP | rewrite Hbl; pplia]. }
  (* 0x14190 ld s4,0(a6) ; 0x14194 add a4,a2,a1 ; 0x14198 bgeu a4,s4 *)
  step. step. step.
  destruct (Z.le_gt_cases (Z.of_nat (length (pc_buf (PbCut sh ps None)))) (off + Z.of_nat (length bsk)))
    as [Hstop|Hgo].
  { (* the object has no room left: the model copies nothing more either *)
    br_true.
    replace (Z.to_nat N) with 0%nat by lia. cbn [fuzz_u8s fst]. rewrite app_nil_r.
    eapply corr_wr_ok; first [exact Hwf | exact HMP | lia | reflexivity]. }
  br_false.
  assert (HN1 : 1 <= N) by lia.
  assert (HSok : store_ok rsegs m1 (Z_to_bv 64 (pp + (off + Z.of_nat (length bsk)))) 1 = true)
    by (eapply (MP_store_ok (off + Z.of_nat (length bsk)) 1); first [exact HMP | pplia]).
  clear HRD.
  (* 0x1419c beqz a3 *)
  step. destruct rr as [|x rr'].
  - (* no input byte is left: the model reads 0 as well *)
    br_true.
    (* 0x141b0 mv a5,zero ; 0x141b4 add a4,s1,a4 ; 0x141b8 addi a0,a0,-1 ; 0x141bc sb a5,0(a4) *)
    step. step. step. step.
    rewrite le1_lit.
    pose proof (MP_store_at _ _ (pp + (off + Z.of_nat (length bsk))) (off + Z.of_nat (length bsk))
                  [Z_to_bv 8 0] HMP ltac:(lia) ltac:(lia) ltac:(cbn [length]; pplia)) as HMP2.
    rewrite (img_step sh ps off (off + Z.of_nat (length bsk)) bsk (Z_to_bv 8 0)) in HMP2
      by (first [reflexivity | rewrite HL2; pplia | pplia]).
    clear HMP HSok.
    revert HMP2.
    generalize (write_to_mem m1 (Z_to_bv 64 (pp + (off + Z.of_nat (length bsk)))) [Z_to_bv 8 0]) as m2.
    intros m2 HMP2. clear m1.
    (* 0x141c0 addi a1,a1,1 ; 0x141c4 bnez a0 *)
    step. step.
    replace (Z.of_nat (length bsk) + 1) with (Z.of_nat (length (bsk ++ [Z_to_bv 8 0])))
      by (rewrite length_app; cbn [length]; lia).
    replace (Z.to_nat N) with (S (Z.to_nat (N - 1))) by lia.
    rewrite fuzz_u8s_nil, app_snoc.
    destruct cnt as [|cnt'].
    + (* the counter has run out *)
      replace (Z.of_nat 1 + -1) with 0 by reflexivity. br_false.
      replace (Z.to_nat (N - 1)) with 0%nat by lia. cbn [fuzz_u8s fst]. rewrite app_nil_r.
      assert (HRD2 : ov_read_bytes rsegs m2 (wa (pp + POD_LEN_OFF)) 8
                     = Some (le8 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))))).
      { rewrite <- HL2, <- (length_overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off)
                              (bsk ++ [Z_to_bv 8 0])) by (rewrite length_app; cbn [length]; lia).
        eapply MP_len_read;
          [exact HMP2 | rewrite length_overwrite by (rewrite length_app; cbn [length]; lia); pplia]. }
      (* 0x141c8 ld s4,0(a6) *)
      step. clear HRD2.
      eapply corr_wr_ok;
        first [exact Hwf | exact HMP2 | lia | reflexivity | rewrite length_app; cbn [length]; lia].
    + (* one more turn *)
      replace (Z.of_nat (S (S cnt')) + -1) with (Z.of_nat (S cnt')) by lia. br_true.
      eapply IH;
        first [exact Hwf | exact Hsuf | exact HMP2 | lia | rewrite length_app; cbn [length]; lia].
  - (* a byte of the input is left *)
    br_false.
    assert (HRX : ov_read_bytes rsegs m1 (wa (cur rest src (x :: rr'))) 1 = Some [x])
      by (eapply cur_read with (i := 0%nat); first [exact HMP | exact Hsuf | reflexivity | lia]).
    (* 0x141a0 lbu a5,0(s5) ; addi s5,s5,1 ; addi a3,a3,-1 ; j 0x141b4 *)
    step. clear HRX. step. step. step.
    (* 0x141b4 add a4,s1,a4 ; 0x141b8 addi a0,a0,-1 ; 0x141bc sb a5,0(a4) *)
    step. step. step.
    rewrite le1_zxb.
    pose proof (MP_store_at _ _ (pp + (off + Z.of_nat (length bsk))) (off + Z.of_nat (length bsk))
                  [x] HMP ltac:(lia) ltac:(lia) ltac:(cbn [length]; pplia)) as HMP2.
    rewrite (img_step sh ps off (off + Z.of_nat (length bsk)) bsk x) in HMP2
      by (first [reflexivity | rewrite HL2; pplia | pplia]).
    clear HMP HSok.
    revert HMP2.
    generalize (write_to_mem m1 (Z_to_bv 64 (pp + (off + Z.of_nat (length bsk)))) [x]) as m2.
    intros m2 HMP2. clear m1.
    (* 0x141c0 addi a1,a1,1 ; 0x141c4 bnez a0 *)
    step. step.
    replace (Z.of_nat (length bsk) + 1) with (Z.of_nat (length (bsk ++ [x])))
      by (rewrite length_app; cbn [length]; lia).
    replace (Z.of_nat (length (x :: rr')) + -1) with (Z.of_nat (length rr')) by (cbn [length]; lia).
    rewrite (cur_cons x rr').
    replace (Z.to_nat N) with (S (Z.to_nat (N - 1))) by lia.
    rewrite fuzz_u8s_cons, app_snoc.
    assert (Hsuf' : suffix rest rr')
      by (apply (suffix_skipn (x :: rr') 1) in Hsuf; cbn [skipn] in Hsuf; exact Hsuf).
    destruct cnt as [|cnt'].
    + replace (Z.of_nat 1 + -1) with 0 by reflexivity. br_false.
      replace (Z.to_nat (N - 1)) with 0%nat by lia. cbn [fuzz_u8s fst]. rewrite app_nil_r.
      assert (HRD2 : ov_read_bytes rsegs m2 (wa (pp + POD_LEN_OFF)) 8
                     = Some (le8 (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))))).
      { rewrite <- HL2, <- (length_overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off)
                              (bsk ++ [x])) by (rewrite length_app; cbn [length]; lia).
        eapply MP_len_read;
          [exact HMP2 | rewrite length_overwrite by (rewrite length_app; cbn [length]; lia); pplia]. }
      (* 0x141c8 ld s4,0(a6) *)
      step. clear HRD2.
      eapply corr_wr_ok;
        first [exact Hwf | exact HMP2 | lia | reflexivity | rewrite length_app; cbn [length]; lia].
    + replace (Z.of_nat (S (S cnt')) + -1) with (Z.of_nat (S cnt')) by lia. br_true.
      eapply IH;
        first [exact Hwf | exact Hsuf' | exact HMP2 | lia | rewrite length_app; cbn [length]; lia].
Qed.

(** ** 0x14134: the tests of pod.h:442-444 that decide whether the record is corrupted *)
Lemma mid_ok : forall sh ps (r : list byte)
  (ra t0 t2 s0 a0 a1 a2 a3 a4 a5 a7 s3 s8 t3 t4 t5 t6 : word) (m1 : word -> option byte),
  pc_wf sh ps -> suffix rest r ->
  MP (pp_image (pod_encode (PodRec sh ps None))
        (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
        (params_struct (PodRec sh ps None)) (ents (PodRec sh ps None)) false) m1 ->
  evt rsegs (QBrec sp gp tp F fc m fl mask buflen b3 b4 b5 b6 pp lo
               (PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r))))
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (Z.of_nat (length r))) t2 s0 (Z_to_bv 64 pp) a0 a1 a2 a3 a4 a5
             (Z_to_bv 64 (pp + POD_LEN_OFF)) a7 (Z_to_bv 64 (b4 * 256)) s3
             (Z_to_bv 64 (Z.of_nat (length (pc_buf (PbCut sh ps None))))) (Z_to_bv 64 (cur rest src r))
             (Z_to_bv 64 fl) (Z_to_bv 64 b3) s8 (Z_to_bv 64 mask) (Z_to_bv 64 buflen) (Z_to_bv 64 b5)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14134) fc None m1 (seg_rom rsegs)).
Proof.
  intros sh ps r ra t0 t2 s0 a0 a1 a2 a3 a4 a5 a7 s3 s8 t3 t4 t5 t6 m1 Hwf Hsuf HMP.
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2).
  pose proof (MP_len_block _ _ HMP) as HLB.
  pose proof (suffix_len r Hsuf) as Hrl.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof (cur_bounds r Hsuf) as (Hc1 & Hc2).
  assert (Hrest : Z.of_nat (length rest) < 2^64) by pplia.
  destruct r as [|c r1].
  { (* no input byte: the record is not corrupted *)
    step. br_true. rewrite corr_none_nil.
    eapply tail_ok;
      [exact HMP | rewrite pp_bytes_of; reflexivity | cbn [buf p_corr]; rewrite HL2; reflexivity | lia]. }
  (* 0x14134 beqz t1 : a byte is left *)
  step. br_false.
  assert (HRC : ov_read_bytes rsegs m1 (wa (cur rest src (c :: r1))) 1 = Some [c])
    by (eapply cur_read with (i := 0%nat); first [exact HMP | exact Hsuf | reflexivity | lia]).
  (* 0x14138 lbu a0,0(s5) ; 0x1413c andi a0,a0,0xf ; 0x14140 addi a1,zero,0xf ; 0x14144 bne a0,a1 *)
  step. clear HRC. step. rewrite land15. step. step.
  pose proof (byte_range c) as Hcr.
  pose proof (Z.mod_pos_bound (bv_unsigned c) 16 ltac:(lia)) as Hcm.
  destruct (Z.eq_dec (bv_unsigned c mod 16) 15) as [Hc15|Hc15]; cycle 1.
  { br_true. rewrite (corr_none _ c r1 (or_introl Hc15)).
    eapply tail_ok;
      [exact HMP | rewrite pp_bytes_of; reflexivity | cbn [buf p_corr]; rewrite HL2; reflexivity | lia]. }
  br_false.
  (* 0x14148 addi a0,zero,8 ; 0x1414c bgeu a0,s4 *)
  step. step.
  destruct (Z.le_gt_cases (Z.of_nat (length (pc_buf (PbCut sh ps None)))) 8) as [H8|H8].
  { br_true.
    assert (Hd8 : bv_unsigned c mod 16 <> 15 \/ Z.of_nat (length (pc_buf (PbCut sh ps None))) <= 8)
      by (right; exact H8).
    rewrite (corr_none _ c r1 Hd8).
    eapply tail_ok;
      [exact HMP | rewrite pp_bytes_of; reflexivity | cbn [buf p_corr]; rewrite HL2; reflexivity | lia]. }
  br_false.
  rewrite (corr_some (Z.of_nat (length (pc_buf (PbCut sh ps None)))) c r1 Hc15 ltac:(lia)).
  set (LL := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
  pose proof (fuzz_u16_range r1) as Ho16.
  assert (Hmod : 0 <= fst (fuzz_u16 r1) mod (LL - 8) < LL - 8) by (apply Z.mod_pos_bound; lia).
  assert (HOFF : 8 <= 8 + fst (fuzz_u16 r1) mod (LL - 8) < LL) by lia.
  (* 0x14150 addi a0,zero,3 ; 0x14154 bltu t1,a0 *)
  step. step.
  destruct (Nat.le_gt_cases (length r1) 2) as [Hr1|Hr1].
  { (* fewer than four bytes: the count byte reads 0, so no byte is written *)
    assert (Hempty : fst (fuzz_u8s (Z.to_nat (Z.min (fst (fuzz_u8 (skipn 2 r1)) mod 8)
                              (LL - (8 + fst (fuzz_u16 r1) mod (LL - 8)))))
                            (skipn 1 (skipn 2 r1))) = []).
    { rewrite (corr_empty_tail r1 Hr1). replace (0 mod 8) with 0 by reflexivity.
      replace (Z.to_nat (Z.min 0 (LL - (8 + fst (fuzz_u16 r1) mod (LL - 8))))) with 0%nat by lia.
      reflexivity. }
    rewrite Hempty.
    destruct (Nat.lt_ge_cases (length (c :: r1)) 3) as [Hlt|Hge].
    - br_true.
      eapply corr_wr_ok;
        first [exact Hwf | lia | reflexivity | rewrite overwrite_nil; exact HMP | cbn [length]; lia].
    - br_false. step. br_true.
      eapply corr_wr_ok;
        first [exact Hwf | lia | reflexivity | rewrite overwrite_nil; exact HMP | cbn [length]; lia]. }
  br_false.
  (* 0x14158 beq t1,a0 *)
  step. br_false.
  (* four bytes are left: the offset and the count *)
  destruct r1 as [|x1 [|x2 [|x3 r4]]]; cbn [length] in Hr1; try lia.
  assert (HR3 : ov_read_bytes rsegs m1 (wa (cur rest src (c :: x1 :: x2 :: x3 :: r4) + 3)) 1 = Some [x3])
    by (eapply cur_read with (i := 3%nat); first [exact HMP | exact Hsuf | reflexivity | lia]).
  (* 0x1415c lbu a0,3(s5) ; 0x14160 andi a0,a0,7 ; 0x14164 beqz a0 *)
  step. clear HR3. step. rewrite land7. step.
  pose proof (byte_range x3) as Hx3.
  pose proof (Z.mod_pos_bound (bv_unsigned x3) 8 ltac:(lia)) as Hn8.
  cbn [skipn] in *. cbn [fuzz_u8 fst] in *.
  destruct (Z.eq_dec (bv_unsigned x3 mod 8) 0) as [Hz|Hz].
  { br_true. rewrite Hz.
    replace (Z.to_nat (Z.min 0 (LL - (8 + fst (fuzz_u16 (x1 :: x2 :: x3 :: r4)) mod (LL - 8)))))
      with 0%nat by lia. cbn [fuzz_u8s fst].
    eapply corr_wr_ok;
      first [exact Hwf | lia | reflexivity | rewrite overwrite_nil; exact HMP | cbn [length]; lia]. }
  br_false.
  assert (HR1 : ov_read_bytes rsegs m1 (wa (cur rest src (c :: x1 :: x2 :: x3 :: r4) + 1)) 1 = Some [x1])
    by (eapply cur_read with (i := 1%nat); first [exact HMP | exact Hsuf | reflexivity | lia]).
  assert (HR2 : ov_read_bytes rsegs m1 (wa (cur rest src (c :: x1 :: x2 :: x3 :: r4) + 2)) 1 = Some [x2])
    by (eapply cur_read with (i := 2%nat); first [exact HMP | exact Hsuf | reflexivity | lia]).
  (* 0x14168 mv a1,zero ; 0x1416c lbu a2,2(s5) ; 0x14170 lbu a3,1(s5) ; 0x14174 slli a2,a2,8 ;
     0x14178 or a2,a2,a3 *)
  step. step. clear HR2. step. clear HR1. step. step.
  rewrite or16.
  pose proof (byte_range x1) as Hx1. pose proof (byte_range x2) as Hx2.
  (* 0x1417c addi s4,s4,-8 ; 0x14180 addi s5,s5,4 ; 0x14184 remu a2,a2,s4 ; 0x14188 addi a2,a2,8 ;
     0x1418c addi a3,t1,-4 *)
  step. step. step.
  rewrite (remu_lit (bv_unsigned x1 + 256 * bv_unsigned x2) (LL + -8) ltac:(lia) ltac:(lia)).
  step. step.
  replace (fst (fuzz_u16 (x1 :: x2 :: x3 :: r4))) with (bv_unsigned x1 + 256 * bv_unsigned x2) in *
    by reflexivity.
  replace (LL + -8) with (LL - 8) by lia.
  replace ((bv_unsigned x1 + 256 * bv_unsigned x2) mod (LL - 8) + 8)
    with (8 + (bv_unsigned x1 + 256 * bv_unsigned x2) mod (LL - 8)) by lia.
  replace (Z.of_nat (length (c :: x1 :: x2 :: x3 :: r4)) + -4) with (Z.of_nat (length r4))
    by (cbn [length]; lia).
  rewrite (cur_skip4 c x1 x2 x3 r4).
  assert (Hn8e : exists n8 : nat, bv_unsigned x3 mod 8 = Z.of_nat n8 /\ (0 < n8)%nat /\ (n8 <= 7)%nat)
    by (exists (Z.to_nat (bv_unsigned x3 mod 8)); repeat split; lia).
  destruct Hn8e as (n8 & Hn8e & Hn8p & Hn8b). rewrite Hn8e in *.
  assert (Hsuf4 : suffix rest r4)
    by (apply (suffix_skipn (c :: x1 :: x2 :: x3 :: r4) 4) in Hsuf; cbn [skipn] in Hsuf; exact Hsuf).
  eapply (loop_ok n8 sh ps (8 + (bv_unsigned x1 + 256 * bv_unsigned x2) mod (LL - 8))
            (Z.min (Z.of_nat n8) (LL - (8 + (bv_unsigned x1 + 256 * bv_unsigned x2) mod (LL - 8)))) [] r4);
    first [exact Hwf | exact Hsuf4 | lia
          | rewrite overwrite_nil; exact HMP
          | change (Z.of_nat (length (@nil byte))) with 0; lia].
Qed.

(** ** 0x14114: the top size word (pod.h:440) *)
Lemma top_ok : forall sh ps (r : list byte) (ms : machine_state),
  POSTH sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo sh ps r ms ->
  evt rsegs (QBrec sp gp tp F fc m fl mask buflen b3 b4 b5 b6 pp lo
               (PodRec sh ps (fst (corr_step (Z.of_nat (length (pc_buf (PbCut sh ps None)))) r)))) ms.
Proof.
  intros sh ps r ms (ra & t0 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a7 & s3 & s8 & t3 & t4 & t5 & t6
                     & m1 & Ems & MB & C28 & C70 & C80 & Cb0 & Hsuf & Hwf).
  subst ms.
  destruct (wf_facts sh ps Hwf) as (HL1 & HL2 & HE1 & HE2).
  assert (HMP : MP (pc_image (PbCut sh ps None)) m1)
    by (split; [exact MB | split; [exact C28 | split; [exact C70 | split; [exact C80 | exact Cb0]]]]).
  rewrite pc_image_of in HMP.
  pose proof (MP_len_block _ _ HMP) as HLB.
  pose proof bnds as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  (* 0x14114 addi a0,s4,-8 ; srli a1,a0,24 ; srli a2,a0,16 ; srli a3,a0,8 *)
  step. step. step. step.
  rewrite (unsigned_lit (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8)) by lia.
  assert (HS0 : store_ok rsegs m1 (Z_to_bv 64 pp) 1 = true)
    by (eapply (MP_store_ok 0 1); first [exact HMP | pplia]).
  (* 0x14124 sb a0,0(s1) *)
  step. rewrite le1_lit.
  pose proof (MP_store_at _ _ pp 0
                [Z_to_bv 8 (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8)] HMP
                ltac:(lia) ltac:(lia) ltac:(cbn [length]; pplia)) as H1.
  clear HS0. pose proof (MP_len_block _ _ H1) as HB1.
  assert (HS1 : store_ok rsegs _ (Z_to_bv 64 (pp + 1)) 1 = true)
    by (eapply (MP_store_ok 1 1); first [exact H1 | pplia]).
  (* 0x14128 sb a3,1(s1) *)
  step. rewrite le1_lit.
  pose proof (MP_store_at _ _ (pp + 1) 1
                [Z_to_bv 8 (Z.shiftr (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8) 8)] H1
                ltac:(lia) ltac:(lia) ltac:(cbn [length]; pplia)) as H2.
  clear HS1 H1 HB1. pose proof (MP_len_block _ _ H2) as HB2.
  assert (HS2 : store_ok rsegs _ (Z_to_bv 64 (pp + 2)) 1 = true)
    by (eapply (MP_store_ok 2 1); first [exact H2 | pplia]).
  (* 0x1412c sb a2,2(s1) *)
  step. rewrite le1_lit.
  pose proof (MP_store_at _ _ (pp + 2) 2
                [Z_to_bv 8 (Z.shiftr (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8) 16)] H2
                ltac:(lia) ltac:(lia) ltac:(cbn [length]; pplia)) as H3.
  clear HS2 H2 HB2. pose proof (MP_len_block _ _ H3) as HB3.
  assert (HS3 : store_ok rsegs _ (Z_to_bv 64 (pp + 3)) 1 = true)
    by (eapply (MP_store_ok 3 1); first [exact H3 | pplia]).
  (* 0x14130 sb a1,3(s1) *)
  step. rewrite le1_lit.
  pose proof (MP_store_at _ _ (pp + 3) 3
                [Z_to_bv 8 (Z.shiftr (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8) 24)] H3
                ltac:(lia) ltac:(lia) ltac:(cbn [length]; pplia)) as H4.
  clear HS3 H3 HB3.
  rewrite overwrite4 in H4 by (cbn [length]; pplia).
  rewrite <- le32_split in H4.
  replace (Z.of_nat (length (pc_buf (PbCut sh ps None))) + -8)
    with (Z.of_nat (length (pc_buf (PbCut sh ps None))) - 8) in H4 by lia.
  rewrite (img_top sh ps Hwf) in H4.
  eapply mid_ok; first [exact Hwf | exact Hsuf | exact H4].
Qed.

End Post.

Theorem post_holds : forall sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo,
  Cut.S_post sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo.
Proof.
  intros sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo HOK sh ps r ms HP.
  exact (top_ok sp gp tp F fc m rest fl mask buflen b3 b4 b5 b6 src pp lo HOK sh ps r ms HP).
Qed.
