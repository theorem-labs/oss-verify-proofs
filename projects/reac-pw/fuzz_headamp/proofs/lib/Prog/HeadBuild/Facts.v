(** The memory a walk of the inlined pod builder of LLVMFuzzerTestOneInput (plain image, pod.h:382-449) carries,
    and the facts its pieces share: the 19744 bytes of the first block as one list, the input bytes, the frame's
    stack window, the .data.rel.ro pointer tables, and the obligations of the builder's stores and calls.

    [MBr I m1] says the block holds I (19744 bytes, writable), the input bytes are still where the cursor's base
    says, only the frame's locals, the callees' stack below sp and the block have changed since the builder's entry
    memory, every byte present then is present now, and the tables read as the image writes them. The builder's
    stores and its calls to memset, memcpy and strlen keep it; a store into the block replaces the bytes it writes.

    Also here: the capacity test the compiler kept (pod.h:177) is false for every length the builder reaches, and
    the list algebra of the stores (four byte stores of a 32-bit put are one four-byte overwrite). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists: prefixes, a write inside a list, two adjacent writes *)
Lemma upd_overwrite : forall (l : list byte) k bs, upd_bytes l k bs = overwrite l k bs.
Proof. reflexivity. Qed.

Lemma firstn_app_le : forall (A B : list byte) n, (n <= length A)%nat -> firstn n (A ++ B) = firstn n A.
Proof.
  intros A B n H. rewrite firstn_app. replace (n - length A)%nat with 0%nat by lia. cbn [firstn].
  apply app_nil_r.
Qed.

Lemma skipn_app_le : forall (A B : list byte) k, (k <= length A)%nat -> skipn k (A ++ B) = skipn k A ++ B.
Proof.
  intros A B k H. rewrite skipn_app. replace (k - length A)%nat with 0%nat by lia. cbn [skipn]. reflexivity.
Qed.

Lemma split3 : forall (l : list byte) o n, (o + n <= length l)%nat ->
  l = firstn o l ++ firstn n (skipn o l) ++ skipn (o + n) l /\
  length (firstn o l) = o /\ length (firstn n (skipn o l)) = n.
Proof.
  intros l o n H.
  assert (E : skipn (o + n) l = skipn n (skipn o l)) by (rewrite skipn_skipn; f_equal; lia).
  split; [|split].
  - rewrite E, (firstn_skipn n (skipn o l)), (firstn_skipn o l). reflexivity.
  - rewrite length_firstn. lia.
  - rewrite length_firstn, length_skipn. lia.
Qed.

Lemma overwrite_len : forall (l bs : list byte) k, (k + length bs <= length l)%nat ->
  length (overwrite l k bs) = length l.
Proof. intros l bs k H. rewrite <- upd_overwrite. apply upd_bytes_length. exact H. Qed.

Lemma overwrite_adj_split : forall (A X Y C x y : list byte),
  length x = length X -> length y = length Y ->
  overwrite (overwrite (A ++ X ++ Y ++ C) (length A) x) (length A + length x)%nat y
  = overwrite (A ++ X ++ Y ++ C) (length A) (x ++ y).
Proof.
  intros A X Y C x y LX LY.
  rewrite (overwrite_mid A X (Y ++ C) x ltac:(lia)).
  replace (A ++ x ++ Y ++ C) with ((A ++ x) ++ Y ++ C) by (rewrite <- app_assoc; reflexivity).
  replace (length A + length x)%nat with (length (A ++ x)) by (rewrite length_app; lia).
  rewrite (overwrite_mid (A ++ x) Y C y ltac:(lia)).
  replace (A ++ X ++ Y ++ C) with (A ++ (X ++ Y) ++ C) by (rewrite <- app_assoc; reflexivity).
  rewrite (overwrite_mid A (X ++ Y) C (x ++ y) ltac:(rewrite !length_app; lia)).
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma list_split4 : forall (l : list byte) o nx ny, (o + nx + ny <= length l)%nat ->
  l = firstn o l ++ firstn nx (skipn o l) ++ firstn ny (skipn (o + nx) l) ++ skipn (o + nx + ny) l.
Proof.
  intros l o nx ny H.
  transitivity (firstn o l ++ skipn o l); [symmetry; apply firstn_skipn|]. f_equal.
  transitivity (firstn nx (skipn o l) ++ skipn nx (skipn o l)); [symmetry; apply firstn_skipn|]. f_equal.
  rewrite skipn_skipn. replace (nx + o)%nat with (o + nx)%nat by lia.
  transitivity (firstn ny (skipn (o + nx) l) ++ skipn ny (skipn (o + nx) l));
    [symmetry; apply firstn_skipn|]. f_equal.
  rewrite skipn_skipn. f_equal. lia.
Qed.

Lemma overwrite_adj : forall (l x y : list byte) o,
  (o + length x + length y <= length l)%nat ->
  overwrite (overwrite l o x) (o + length x)%nat y = overwrite l o (x ++ y).
Proof.
  intros l x y o H.
  set (A := firstn o l). set (X := firstn (length x) (skipn o l)).
  set (Y := firstn (length y) (skipn (o + length x) l)). set (C := skipn (o + length x + length y) l).
  assert (LA : length A = o) by (subst A; rewrite length_firstn; lia).
  assert (LX : length x = length X) by (subst X; rewrite length_firstn, length_skipn; lia).
  assert (LY : length y = length Y) by (subst Y; rewrite length_firstn, length_skipn; lia).
  assert (El : l = A ++ X ++ Y ++ C) by (subst A X Y C; apply list_split4; exact H).
  clearbody A X Y C.
  rewrite El, <- LA. exact (overwrite_adj_split A X Y C x y LX LY).
Qed.

(** ** Unsigned comparisons of literal words *)
Lemma umod_id : forall z, 0 <= z < 2^64 -> z mod 2^64 = z.
Proof. intros z H. apply Z.mod_small. exact H. Qed.
Lemma umod_neg : forall z, -2^64 <= z < 0 -> z mod 2^64 = z + 2^64.
Proof. intros z H. rewrite <- (Z.mod_add z 1 (2^64)) by lia. apply Z.mod_small. lia. Qed.

Lemma bv_ltu_lit : forall a b, bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb (a mod 2^64) (b mod 2^64).
Proof. intros a b. unfold bv_ltu. rewrite !unsigned_lit_wrap. reflexivity. Qed.

Lemma bv_eqb_lit : forall a b, bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb (a mod 2^64) (b mod 2^64).
Proof. intros a b. unfold bv_eqb. rewrite !unsigned_lit_wrap. reflexivity. Qed.

(** pod_put's capacity test (pod.h:177) as the compiler kept it, `len + (-0x3ffd) <u -0x4001`: false for every
    length below 16381, so the put always happens. *)
Lemma put_cap_dead : forall L, 0 <= L <= 16380 ->
  bv_ltu (Z_to_bv 64 (L + -16381)) (Z_to_bv 64 (-16385)) = false.
Proof.
  intros L HL. rewrite bv_ltu_lit, (umod_neg (L + -16381)) by lia. rewrite (umod_neg (-16385)) by lia.
  apply Z.ltb_ge. lia.
Qed.

(** The same test in its `0x4000 <u len` form (the pad's memset and the inlined pod_write_ent). *)
Lemma put_cap_dead' : forall L, 0 <= L <= 16384 -> bv_ltu (Z_to_bv 64 16384) (Z_to_bv 64 L) = false.
Proof. intros L HL. rewrite bv_ltu_lit, !umod_id by lia. apply Z.ltb_ge. lia. Qed.

(** ** The image: where its bytes are, and where it has none *)
Definition rom_some (a : Z) : bool := match seg_rom rsegs (wa a) with Some _ => true | None => false end.

Lemma rom_range : forall base n, forallb (fun j => rom_some (base + Z.of_nat j)) (seq 0 n) = true ->
  forall a, base <= a < base + Z.of_nat n -> seg_rom rsegs (wa a) <> None.
Proof.
  intros base n H a Ha. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - base)) ltac:(apply in_seq; lia)). unfold rom_some in H.
  replace (base + Z.of_nat (Z.to_nat (a - base))) with a in H by lia.
  destruct (seg_rom rsegs (wa a)); [discriminate | discriminate H].
Qed.

(** The two absolute-pointer tables of .data.rel.ro the builder reads (vocab and odd_ch). *)
Lemma relro_rom : forall a, RELRO_TBL <= a < RELRO_TBL_END -> seg_rom rsegs (wa a) <> None.
Proof.
  intros a Ha. apply (rom_range RELRO_TBL 184); [vm_compute; reflexivity|].
  unfold RELRO_TBL, RELRO_TBL_END in *. lia.
Qed.

Lemma rom_apart : forall X Y U V,
  (forall a, X <= a < Y -> seg_rom rsegs (wa a) = None) ->
  (forall a, U <= a < V -> seg_rom rsegs (wa a) <> None) ->
  forall a, U <= a < V -> ~ (X <= a < Y).
Proof. intros X Y U V H1 H2 a Ha Hx. exact (H2 a Ha (H1 a Hx)). Qed.

Lemma wr_at_sub : forall m a n b k, wr_at rsegs m a n -> a <= b -> b + k <= a + n -> 0 <= k ->
  wr_at rsegs m b k.
Proof.
  intros m a n b k (H1 & H2 & H) Hb Hk Hk0. split; [lia|]. split; [lia|].
  intros i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply H. lia.
Qed.

Lemma stk_wr : forall m x y, stk rsegs m x y -> x <= y -> wr_at rsegs m x (y - x).
Proof.
  intros m x y (H1 & H2 & H) Hxy. split; [lia|]. split; [lia|].
  intros i Hi. apply (H (x + i) ltac:(lia)).
Qed.

(** A write is a munch of its own range. *)
Lemma munch_of_write : forall m1 (a : Z) bs, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  munch [(a, a + Z.of_nat (length bs))] m1 (write_to_mem m1 (wa a) bs).
Proof.
  intros m1 a bs Ha Hl. apply munch_write; [apply munch_refl | exact Ha | exact Hl|].
  cbn [inside]. left. lia.
Qed.

(** A write inside a list of bytes, seen through a call that changed only that range. *)
Lemma bytes_at_patch : forall m1 m2 (A o : Z) Ib bs,
  bytes_at rsegs m1 A Ib -> munch [(A + o, A + o + Z.of_nat (length bs))] m1 m2 ->
  bytes_at rsegs m2 (A + o) bs -> 0 <= o -> (Z.to_nat o + length bs <= length Ib)%nat ->
  bytes_at rsegs m2 A (overwrite Ib (Z.to_nat o) bs).
Proof.
  intros m1 m2 A o Ib bs HI MU HB Ho Hlen.
  destruct (split3 Ib (Z.to_nat o) (length bs) Hlen) as (EI & LA & LB).
  set (Px := firstn (Z.to_nat o) Ib) in *. set (Mx := firstn (length bs) (skipn (Z.to_nat o) Ib)) in *.
  set (Sx := skipn (Z.to_nat o + length bs) Ib) in *.
  assert (EO : overwrite Ib (Z.to_nat o) bs = Px ++ bs ++ Sx) by reflexivity.
  rewrite EO. rewrite EI in HI. apply bytes_at_app in HI as [HP HI2].
  rewrite LA in HI2. apply bytes_at_app in HI2 as [HM HS]. rewrite LB in HS.
  apply bytes_at_app. split.
  - apply (bytes_at_transport rsegs _ m1 m2 _ _ HP MU). cbn [disjoint_from]. rewrite LA.
    split; [lia | exact I].
  - rewrite LA. apply bytes_at_app. split.
    + replace (A + Z.of_nat (Z.to_nat o)) with (A + o) by lia. exact HB.
    + apply (bytes_at_transport rsegs _ m1 m2 _ _ HS MU). cbn [disjoint_from]. split; [lia | exact I].
Qed.

(** ** The bytes a store writes *)
(** A byte store of a literal word. *)
Lemma le1_lit : forall x, le1 (Z_to_bv 64 x) = [Z_to_bv 8 x].
Proof.
  intros x. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. apply mod_mod8_of_modw. lia.
Qed.

(** An 8-byte store of a literal word writes the field [le64] holds. *)
Lemma le8_lit64 : forall x, le8 (Z_to_bv 64 x) = le64 x.
Proof.
  intros x. rewrite <- store_bytes_8. unfold le64. rewrite unsigned_lit_wrap.
  apply Z_to_le_bytes_mod. cbn. lia.
Qed.

(** The four bytes a 32-bit put stores (the value, then its three shifts). *)
Lemma le32_split : forall v,
  le32 v = [Z_to_bv 8 v; Z_to_bv 8 (Z.shiftr v 8); Z_to_bv 8 (Z.shiftr v 16); Z_to_bv 8 (Z.shiftr v 24)].
Proof.
  intros v. unfold le32. cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. reflexivity.
Qed.

Lemma le32_of_stores : forall v,
  le1 (Z_to_bv 64 v) ++ le1 (Z_to_bv 64 (Z.shiftr v 8))
  ++ le1 (Z_to_bv 64 (Z.shiftr v 16)) ++ le1 (Z_to_bv 64 (Z.shiftr v 24)) = le32 v.
Proof. intros v. rewrite !le1_lit, le32_split. reflexivity. Qed.

(** A single block cell holds exactly its bytes. *)
Lemma rw_cells_CB_bytes : forall m1 A n bs, rw_cells rsegs m1 A [CB n bs] -> bytes_at rsegs m1 A bs.
Proof.
  intros m1 A n bs [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.

(** ** The block's image while the length field lags behind the buffer *)
(** The header writes buf and pp->len in the compiler's order, so between them the length field is not yet the
    buffer's length; [pp_at] names that image. *)
Definition pp_at (b : list byte) (ln : Z) (isp hasp pst : bool) (es : list ent) (corr : bool) : list byte :=
  b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))) ++ le64 ln ++ pp_tail isp hasp pst es corr.

Lemma pp_at_image : forall b isp hasp pst es corr,
  pp_at b (Z.of_nat (length b)) isp hasp pst es corr = pp_image b isp hasp pst es corr.
Proof. reflexivity. Qed.

Lemma pp_at_zeros : forall n isp hasp pst es corr, Z.of_nat n <= POD_BUF_MAX ->
  pp_at (zeros n) 0 isp hasp pst es corr = pp_image [] isp hasp pst es corr.
Proof.
  intros n isp hasp pst es corr Hn. unfold pp_at. rewrite pp_image_tail. cbn [length Z.of_nat app].
  rewrite length_zeros, app_assoc, <- zeros_app.
  f_equal. f_equal. unfold POD_BUF_MAX in *. lia.
Qed.

Lemma pp_at_patch : forall b ln o x isp hasp pst es corr, (o + length x <= length b)%nat ->
  pp_at (overwrite b o x) ln isp hasp pst es corr = overwrite (pp_at b ln isp hasp pst es corr) o x.
Proof.
  intros b ln o x isp hasp pst es corr H. unfold pp_at. rewrite overwrite_len by exact H.
  rewrite overwrite_app_l by exact H. reflexivity.
Qed.

Lemma pp_at_len : forall b ln ln' isp hasp pst es corr, Z.of_nat (length b) <= POD_BUF_MAX ->
  overwrite (pp_at b ln isp hasp pst es corr) (Z.to_nat OFF_LEN) (le64 ln')
  = pp_at b ln' isp hasp pst es corr.
Proof.
  intros b ln ln' isp hasp pst es corr Hb.
  assert (E : forall k, pp_at b k isp hasp pst es corr
              = (b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b)))) ++ le64 k
                ++ pp_tail isp hasp pst es corr)
    by (intros k; unfold pp_at; rewrite <- !app_assoc; reflexivity).
  rewrite !E.
  replace (Z.to_nat OFF_LEN) with (length (b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b)))))
    by (rewrite length_app, length_zeros; unfold POD_BUF_MAX, OFF_LEN in *; lia).
  rewrite overwrite_mid by (rewrite !length_le64; reflexivity). reflexivity.
Qed.

Lemma pp_at_is_props : forall b ln isp isp' hasp pst es corr, Z.of_nat (length b) <= POD_BUF_MAX ->
  overwrite (pp_at b ln isp hasp pst es corr) (Z.to_nat OFF_IS_PROPS) (le32 (Z.b2z isp'))
  = pp_at b ln isp' hasp pst es corr.
Proof.
  intros b ln isp isp' hasp pst es corr Hb.
  assert (E : forall i, pp_at b ln i hasp pst es corr
              = (b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))) ++ le64 ln) ++ le32 (Z.b2z i)
                ++ (le32 (Z.b2z hasp) ++ le32 (Z.b2z pst)
                    ++ flat_map ent_mem es ++ zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es))))
                    ++ le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4)).
  { intros i. unfold pp_at, pp_tail. rewrite <- !app_assoc. reflexivity. }
  rewrite !E.
  replace (Z.to_nat OFF_IS_PROPS)
    with (length (b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))) ++ le64 ln))
    by (rewrite !length_app, length_zeros, length_le64; unfold POD_BUF_MAX, OFF_IS_PROPS in *; lia).
  rewrite overwrite_mid by (rewrite !length_le32; reflexivity). reflexivity.
Qed.

(** ** Slices of the block's image (Pod/Layout.v [pp_image]) *)
Lemma pp_image_slice_len : forall b isp hasp pst es corr, Z.of_nat (length b) <= POD_BUF_MAX ->
  firstn 8 (skipn (Z.to_nat OFF_LEN) (pp_image b isp hasp pst es corr)) = le64 (Z.of_nat (length b)).
Proof.
  intros b isp hasp pst es corr Hb.
  assert (E : pp_image b isp hasp pst es corr
              = (b ++ zeros (Z.to_nat (POD_BUF_MAX - Z.of_nat (length b))))
                ++ (le64 (Z.of_nat (length b)) ++ pp_tail isp hasp pst es corr))
    by (rewrite pp_image_tail, <- app_assoc; reflexivity).
  rewrite E, (skipn_app_eq _ _ (Z.to_nat OFF_LEN))
    by (rewrite length_app, length_zeros; unfold POD_BUF_MAX, OFF_LEN in *; lia).
  apply firstn_app_eq. reflexivity.
Qed.

Lemma pp_image_slice_buf : forall b isp hasp pst es corr k n, (k + n <= length b)%nat ->
  firstn n (skipn k (pp_image b isp hasp pst es corr)) = firstn n (skipn k b).
Proof.
  intros b isp hasp pst es corr k n H. rewrite pp_image_tail.
  rewrite skipn_app_le by lia. rewrite firstn_app_le by (rewrite length_skipn; lia). reflexivity.
Qed.

Lemma pp_image_slice_nent : forall b isp hasp pst es corr, Z.of_nat (length b) <= POD_BUF_MAX ->
  (length es <= 32)%nat -> Forall (fun e => (length (e_body e) <= 96)%nat) es ->
  firstn 4 (skipn (Z.to_nat OFF_N_ENT) (pp_image b isp hasp pst es corr)) = le32 (Z.of_nat (length es)).
Proof.
  intros b isp hasp pst es corr Hb He Hs.
  assert (E : pp_image b isp hasp pst es corr
              = (pp_head b isp hasp pst ++ flat_map ent_mem es
                 ++ zeros (Z.to_nat (ENT_SIZE * (POD_ENT_MAX - Z.of_nat (length es)))))
                ++ (le32 (Z.of_nat (length es)) ++ le32 (Z.b2z corr) ++ zeros 4))
    by (rewrite pp_image_head, <- !app_assoc; reflexivity).
  rewrite E, (skipn_app_eq _ _ (Z.to_nat OFF_N_ENT)).
  - apply firstn_app_eq. reflexivity.
  - rewrite !length_app, length_zeros, length_flat_ent_mem by exact Hs.
    pose proof (length_pp_head b isp hasp pst Hb) as LP.
    unfold ENT_SIZE, POD_ENT_MAX, OFF_N_ENT, OFF_ENT in *. lia.
Qed.

(** ** The builder's memory *)
Section Build.
Variables (sp : word) (m : word -> option byte) (rest : list byte) (src pp lo : Z).

(** The bounds every piece of the walk uses: the block and the input below the stack region, apart from each
    other, neither of them in the image. *)
Definition BOK : Prop :=
  0 < src /\ src + Z.of_nat (length rest) <= lo /\ pp + POD_PROPS <= lo /\
  (src + Z.of_nat (length rest) <= pp \/ pp + POD_PROPS <= src) /\
  lo + MID_STACK <= bv_unsigned sp /\ 0 <= lo /\ bv_unsigned sp + FRAME_LOCALS <= 2^64 /\ 0 < pp /\
  (forall a, pp <= a < pp + POD_PROPS -> seg_rom rsegs (wa a) = None) /\
  (forall a, lo <= a < bv_unsigned sp + FRAME_LOCALS -> seg_rom rsegs (wa a) = None).

Hypothesis HOK : BOK.

Definition W0 : list (Z * Z) :=
  [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS); (pp, pp + POD_PROPS)].

Definition tblr (m1 : word -> option byte) : Prop :=
  forall a, RELRO_TBL <= a < RELRO_TBL_END -> mrd rsegs m1 (wa a) = seg_rom rsegs (wa a).

Definition MBr (Ib : list byte) (m1 : word -> option byte) : Prop :=
  bytes_at rsegs m1 pp Ib /\ Z.of_nat (length Ib) = POD_PROPS /\
  wr_at rsegs m1 pp POD_PROPS /\
  bytes_at rsegs m1 src rest /\
  munch W0 m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
  stk rsegs m1 lo (bv_unsigned sp + FRAME_LOCALS) /\ tblr m1.

(** The tables are in the image, the block and the stack region are not, so they are apart. *)
Lemma relro_out_pp : forall a, RELRO_TBL <= a < RELRO_TBL_END -> ~ (pp <= a < pp + POD_PROPS).
Proof.
  destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & HR & _).
  exact (rom_apart pp (pp + POD_PROPS) RELRO_TBL RELRO_TBL_END HR relro_rom).
Qed.

Lemma relro_out_frame : forall a, RELRO_TBL <= a < RELRO_TBL_END ->
  ~ (bv_unsigned sp - MID_STACK <= a < bv_unsigned sp + FRAME_LOCALS).
Proof.
  destruct HOK as (_ & _ & _ & _ & HM & _ & _ & _ & _ & HR).
  intros a Ha Hx. apply (rom_apart lo (bv_unsigned sp + FRAME_LOCALS) RELRO_TBL RELRO_TBL_END HR relro_rom a Ha).
  lia.
Qed.

Lemma relro_out_W0 : forall a, RELRO_TBL <= a < RELRO_TBL_END -> outside W0 a.
Proof.
  intros a Ha. cbn [outside]. split; [exact (relro_out_frame a Ha)|].
  split; [exact (relro_out_pp a Ha) | exact I].
Qed.

Lemma MBr_bounds : forall Ib m1, MBr Ib m1 ->
  0 <= pp /\ pp + POD_PROPS <= 2^64 /\ Z.of_nat (length Ib) = POD_PROPS.
Proof. intros Ib m1 (_ & HL & HW & _). destruct HW as (A & B & _). split; [lia | split; lia]. Qed.

(** ** The obligations of a store *)
Lemma MBr_pp_ok : forall Ib m1 (o : Z) (j : nat), MBr Ib m1 -> 0 <= o -> o + Z.of_nat j <= POD_PROPS ->
  store_ok rsegs m1 (wa (pp + o)) j = true.
Proof.
  intros Ib m1 o j (_ & _ & HW & _) Ho Hj. exact (wr_at_store_ok rsegs m1 pp POD_PROPS o j HW Ho Hj).
Qed.

Lemma MBr_stk_ok : forall Ib m1 (a : Z) (j : nat), MBr Ib m1 -> lo <= a ->
  a + Z.of_nat j <= bv_unsigned sp + FRAME_LOCALS -> store_ok rsegs m1 (wa a) j = true.
Proof.
  intros Ib m1 a j (_ & _ & _ & _ & _ & _ & _ & HS & _) Ha Hj.
  destruct HOK as (_ & _ & _ & _ & HM & HL & _).
  pose proof (stk_wr m1 lo (bv_unsigned sp + FRAME_LOCALS) HS ltac:(lia)) as HW.
  pose proof (wr_at_store_ok rsegs m1 lo (bv_unsigned sp + FRAME_LOCALS - lo) (a - lo) j HW
                ltac:(lia) ltac:(lia)) as X.
  replace (lo + (a - lo)) with a in X by lia. exact X.
Qed.

(** ** A store into the block *)
Lemma MBr_pp_store : forall Ib m1 (o : Z) bs, MBr Ib m1 -> 0 <= o ->
  (Z.to_nat o + length bs <= length Ib)%nat ->
  MBr (overwrite Ib (Z.to_nat o) bs) (write_to_mem m1 (wa (pp + o)) bs).
Proof.
  intros Ib m1 o bs MB Ho Hlen.
  pose proof MB as (HI & HL & HW & HR & MU & WM & MI & HS & HT).
  pose proof (MBr_bounds Ib m1 MB) as (B1 & B2 & B3).
  destruct HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & HROM & HSROM).
  assert (Hbound : o + Z.of_nat (length bs) <= POD_PROPS) by lia.
  assert (HOKst : store_ok rsegs m1 (wa (pp + o)) (length bs) = true)
    by (apply (MBr_pp_ok Ib m1 o (length bs) MB Ho); lia).
  assert (MW : munch [(pp + o, pp + o + Z.of_nat (length bs))] m1 (write_to_mem m1 (wa (pp + o)) bs))
    by (apply munch_of_write; lia).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - rewrite <- upd_overwrite. apply bytes_at_write_inside; [exact HI | exact Ho | exact Hlen].
  - rewrite overwrite_len by exact Hlen. exact HL.
  - apply wr_at_write. exact HW.
  - apply (bytes_at_write_other rsegs m1 (pp + o) bs src rest HR); [lia | lia | lia].
  - apply munch_write; [exact MU | lia | lia |]. cbn [inside]. right. left. lia.
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HOKst].
  - apply stk_write; [exact HS | lia | lia].
  - intros a Ha. unfold mrd. rewrite (MW (wa a)).
    + exact (HT a Ha).
    + rewrite (wa_unsigned a) by (unfold RELRO_TBL, RELRO_TBL_END in *; lia).
      cbn [outside]. pose proof (relro_out_pp a Ha). split; [lia | exact I].
Qed.

(** ** A store into the frame's locals or a callee's stack *)
Lemma MBr_stk_store : forall Ib m1 (a : Z) bs, MBr Ib m1 ->
  lo <= a -> bv_unsigned sp - MID_STACK <= a -> a + Z.of_nat (length bs) <= bv_unsigned sp + FRAME_LOCALS ->
  MBr Ib (write_to_mem m1 (wa a) bs).
Proof.
  intros Ib m1 a bs MB Ha1 Ha2 Ha3.
  pose proof MB as (HI & HL & HW & HR & MU & WM & MI & HS & HT).
  pose proof (MBr_bounds Ib m1 MB) as (B1 & B2 & B3).
  destruct HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & HROM & HSROM).
  assert (HOKst : store_ok rsegs m1 (wa a) (length bs) = true)
    by (apply (MBr_stk_ok Ib m1 a (length bs) MB Ha1); lia).
  assert (MW : munch [(a, a + Z.of_nat (length bs))] m1 (write_to_mem m1 (wa a) bs))
    by (apply munch_of_write; lia).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - apply (bytes_at_write_other rsegs m1 a bs pp Ib HI); [lia | lia | lia].
  - exact HL.
  - apply wr_at_write. exact HW.
  - apply (bytes_at_write_other rsegs m1 a bs src rest HR); [lia | lia | lia].
  - apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HOKst].
  - apply stk_write; [exact HS | lia | lia].
  - intros x Hx. unfold mrd. rewrite (MW (wa x)).
    + exact (HT x Hx).
    + rewrite (wa_unsigned x) by (unfold RELRO_TBL, RELRO_TBL_END in *; lia).
      cbn [outside]. pose proof (relro_out_frame x Hx). split; [lia | exact I].
Qed.

(** ** A call that writes only inside the frame's locals and the callees' stack *)
Lemma MBr_call : forall Ib m1 m2 W, MBr Ib m1 ->
  munch W m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  stk rsegs m2 lo (bv_unsigned sp + FRAME_LOCALS) ->
  sub_fp W [(bv_unsigned sp - MID_STACK, bv_unsigned sp + FRAME_LOCALS)] ->
  disjoint_from W pp POD_PROPS -> disjoint_from W src (Z.of_nat (length rest)) ->
  MBr Ib m2.
Proof.
  intros Ib m1 m2 W MB MU2 WM2 MI2 ST2 SUB DPP DSRC.
  pose proof MB as (HI & HL & HW & HR & MU & WM & MI & HS & HT).
  assert (SUB0 : sub_fp W W0).
  { unfold sub_fp, W0 in *. intros x Hx. apply SUB. cbn [outside] in *.
    destruct Hx as (H1 & _). split; [exact H1 | exact I]. }
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - apply (bytes_at_transport rsegs W m1 m2 _ _ HI MU2). rewrite HL. exact DPP.
  - exact HL.
  - exact (wr_at_transport rsegs m1 m2 _ _ HW WM2).
  - exact (bytes_at_transport rsegs W m1 m2 _ _ HR MU2 DSRC).
  - apply (munch_trans W0 m m1 m2 MU). exact (munch_weaken W W0 m1 m2 SUB0 MU2).
  - exact (wmono_trans rsegs m m1 m2 WM WM2).
  - exact MI2.
  - exact ST2.
  - intros a Ha. unfold mrd. rewrite (MU2 (wa a)).
    + exact (HT a Ha).
    + rewrite (wa_unsigned a) by (unfold RELRO_TBL, RELRO_TBL_END in *; lia).
      apply SUB0. exact (relro_out_W0 a Ha).
Qed.

(** ** A call that writes a range of the block (the memsets and the memcpy of the buffer) *)
Lemma MBr_call_pp : forall Ib m1 m2 (o n : Z) bs, MBr Ib m1 ->
  munch [(pp + o, pp + o + n)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  bytes_at rsegs m2 (pp + o) bs -> Z.of_nat (length bs) = n -> 0 <= o -> o + n <= POD_PROPS ->
  MBr (overwrite Ib (Z.to_nat o) bs) m2.
Proof.
  intros Ib m1 m2 o n bs MB MU2 WM2 MI2 HB Hn Ho Hon.
  pose proof MB as (HI & HL & HW & HR & MU & WM & MI & HS & HT).
  pose proof (MBr_bounds Ib m1 MB) as (B1 & B2 & B3).
  destruct HOK as (HS0 & HS1 & HP1 & HDJ & HM1 & HL0 & HSP & HPP & HROM & HSROM).
  assert (Hlen : (Z.to_nat o + length bs <= length Ib)%nat) by lia.
  assert (MU2' : munch [(pp + o, pp + o + Z.of_nat (length bs))] m1 m2) by (rewrite Hn; exact MU2).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - exact (bytes_at_patch m1 m2 pp o Ib bs HI MU2' HB Ho Hlen).
  - rewrite overwrite_len by exact Hlen. exact HL.
  - exact (wr_at_transport rsegs m1 m2 _ _ HW WM2).
  - apply (bytes_at_transport rsegs _ m1 m2 _ _ HR MU2). cbn [disjoint_from]. split; [lia | exact I].
  - apply (munch_trans W0 m m1 m2 MU).
    apply (munch_weaken [(pp + o, pp + o + n)] W0 m1 m2); [|exact MU2].
    unfold sub_fp, W0. cbn [outside]. intros x (H1 & H2 & _). split; [lia | exact I].
  - exact (wmono_trans rsegs m m1 m2 WM WM2).
  - exact MI2.
  - apply (stk_transport_disjoint rsegs _ m1 m2 _ _ HS MU2 WM2).
    cbn [disjoint_from]. split; [lia | exact I].
  - intros a Ha. unfold mrd. rewrite (MU2 (wa a)).
    + exact (HT a Ha).
    + rewrite (wa_unsigned a) by (unfold RELRO_TBL, RELRO_TBL_END in *; lia).
      cbn [outside]. pose proof (relro_out_pp a Ha). split; [lia | exact I].
Qed.

(** ** Reads *)
Lemma MBr_read : forall Ib m1 (o : Z) (n : nat), MBr Ib m1 -> 0 <= o -> (Z.to_nat o + n <= length Ib)%nat ->
  ov_read_bytes rsegs m1 (wa (pp + o)) n = Some (firstn n (skipn (Z.to_nat o) Ib)).
Proof.
  intros Ib m1 o n (HI & _) Ho Hn. exact (bytes_at_read rsegs m1 pp Ib o n HI Ho Hn).
Qed.

Lemma MBr_pp_bytes : forall Ib m1 (o : Z) (n : nat), MBr Ib m1 -> 0 <= o ->
  (Z.to_nat o + n <= length Ib)%nat ->
  bytes_at rsegs m1 (pp + o) (firstn n (skipn (Z.to_nat o) Ib)).
Proof.
  intros Ib m1 o n (HI & _) Ho Hn.
  destruct (split3 Ib (Z.to_nat o) n Hn) as (EI & LA & LB).
  rewrite EI in HI. apply bytes_at_app in HI as [_ HI2]. rewrite LA in HI2.
  apply bytes_at_app in HI2 as [HM _]. replace (pp + o) with (pp + Z.of_nat (Z.to_nat o)) by lia. exact HM.
Qed.

(** The block's bytes as a cell a leaf contract takes. *)
Lemma MBr_pp_cells : forall Ib m1 (o : Z) (n : nat), MBr Ib m1 -> 0 <= o ->
  (Z.to_nat o + n <= length Ib)%nat ->
  rw_cells rsegs m1 (pp + o) [CB n (firstn n (skipn (Z.to_nat o) Ib))].
Proof.
  intros Ib m1 o n MB Ho Hn. pose proof (MBr_pp_bytes Ib m1 o n MB Ho Hn) as HB.
  pose proof (MBr_bounds Ib m1 MB) as (B1 & B2 & B3).
  pose proof MB as (_ & _ & HW & _).
  assert (Hl : length (firstn n (skipn (Z.to_nat o) Ib)) = n)
    by (rewrite length_firstn, length_skipn; lia).
  split.
  - split; [cbn; split; [exact Hl | exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    apply (wr_at_sub m1 pp POD_PROPS (pp + o) (Z.of_nat n) HW); lia.
Qed.

(** The input is still at its base, so every suffix is where the cursor says. *)
Lemma MBr_rest : forall I m1 (k : nat), MBr I m1 -> (k <= length rest)%nat ->
  bytes_at rsegs m1 (src + Z.of_nat k) (skipn k rest).
Proof.
  intros I m1 k (_ & _ & _ & HR & _) Hk.
  rewrite <- (firstn_skipn k rest) in HR. apply bytes_at_app in HR as [_ HS].
  rewrite length_firstn in HS. replace (Nat.min k (length rest)) with k in HS by lia. exact HS.
Qed.

Lemma MBr_byte : forall I m1 (k : nat) (x : byte) (r : list byte), MBr I m1 ->
  skipn k rest = x :: r -> ov_read_bytes rsegs m1 (wa (src + Z.of_nat k)) 1 = Some [x].
Proof.
  intros I m1 k x r MB Hk.
  assert (Hle : (k <= length rest)%nat).
  { destruct (Nat.le_gt_cases k (length rest)) as [H|H]; [exact H|].
    rewrite skipn_all2 in Hk by lia. discriminate. }
  pose proof (MBr_rest I m1 k MB Hle) as HS. rewrite Hk in HS.
  pose proof (bytes_at_read rsegs m1 (src + Z.of_nat k) (x :: r) 0 1 HS ltac:(lia) ltac:(cbn; lia)) as HR.
  rewrite Z.add_0_r in HR. exact HR.
Qed.

End Build.

(** A frame cell read. *)
Lemma cell8_read : forall (m1 : word -> option byte) (a v : Z),
  bytes_at rsegs m1 a (le8 (Z_to_bv 64 v)) ->
  ov_read_bytes rsegs m1 (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m1 a v HB.
  pose proof (bytes_at_read rsegs m1 a _ 0 8 HB ltac:(lia) ltac:(rewrite length_le8; cbn; lia)) as HR.
  rewrite Z.add_0_r in HR. cbn [Z.to_nat skipn] in HR. rewrite HR. f_equal.
  all: try (rewrite firstn_all2 by (rewrite length_le8; lia)). all: try reflexivity.
Qed.

(** A store into the frame at an address the semantics may leave in any convertible form (the store at sp
    itself keeps sp, not a literal sum). *)
Lemma MBr_stk_store_w : forall sp m rest src pp lo, BOK sp rest src pp lo ->
  forall Ib m1 (w : word) (a : Z) bs, MBr sp m rest src pp lo Ib m1 -> w = wa a ->
  lo <= a -> bv_unsigned sp - MID_STACK <= a -> a + Z.of_nat (length bs) <= bv_unsigned sp + FRAME_LOCALS ->
  MBr sp m rest src pp lo Ib (write_to_mem m1 w bs) /\
  bytes_at rsegs (write_to_mem m1 w bs) a bs /\
  store_ok rsegs m1 w (length bs) = true.
Proof.
  intros spv mv restv srcv ppv lov HK Ib m1 w a bs MB -> H1 H2 H3.
  pose proof HK as (_ & _ & _ & _ & _ & HL0 & HSP & _).
  split; [exact (MBr_stk_store spv mv restv srcv ppv lov HK Ib m1 a bs MB H1 H2 H3)|].
  split.
  - apply bytes_at_write_same; unfold FRAME_LOCALS in *; lia.
  - exact (MBr_stk_ok spv mv restv srcv ppv lov HK Ib m1 a (length bs) MB H1 H3).
Qed.

(** A store at an address the semantics leaves as a word, not a literal sum. *)
Lemma bytes_at_write_other_w : forall m (w : word) bs c cs, bytes_at rsegs m c cs ->
  (bv_unsigned w + Z.of_nat (length bs) <= 2^64)%Z ->
  (c + Z.of_nat (length cs) <= bv_unsigned w \/ bv_unsigned w + Z.of_nat (length bs) <= c)%Z ->
  bytes_at rsegs (write_to_mem m w bs) c cs.
Proof.
  intros m w bs c cs HB HR2 HD. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (Z.of_N 64) with 64%Z in R.
  rewrite <- (Z_to_bv_lit_self w).
  apply (bytes_at_write_other rsegs m (bv_unsigned w) bs c cs HB); lia.
Qed.

(** A store into the block at an address the semantics may leave in any convertible form. *)
Lemma MBr_pp_store_w : forall sp m rest src pp lo, BOK sp rest src pp lo ->
  forall Ib m1 (w : word) (o : Z) bs, MBr sp m rest src pp lo Ib m1 -> w = wa (pp + o) -> (0 <= o)%Z ->
  (Z.to_nat o + length bs <= length Ib)%nat ->
  MBr sp m rest src pp lo (overwrite Ib (Z.to_nat o) bs) (write_to_mem m1 w bs) /\
  store_ok rsegs m1 w (length bs) = true.
Proof.
  intros spv mv restv srcv ppv lov HK Ib m1 w o bs MB -> Ho Hlen.
  pose proof (MBr_bounds spv mv restv srcv ppv lov Ib m1 MB) as (B1 & B2 & B3).
  split; [exact (MBr_pp_store spv mv restv srcv ppv lov HK Ib m1 o bs MB Ho Hlen)|].
  exact (MBr_pp_ok spv mv restv srcv ppv lov Ib m1 o (length bs) MB Ho ltac:(lia)).
Qed.

(** Zeros at the end of the written buffer are the block's own zeros. *)
Lemma pp_at_trim : forall b k ln isp hasp pst es corr,
  (Z.of_nat (length b + k) <= POD_BUF_MAX)%Z ->
  pp_at (b ++ zeros k) ln isp hasp pst es corr = pp_at b ln isp hasp pst es corr.
Proof.
  intros b k ln isp hasp pst es corr H. unfold pp_at. rewrite length_app, length_zeros.
  rewrite <- !app_assoc. f_equal. rewrite app_assoc, <- zeros_app. f_equal. f_equal.
  unfold POD_BUF_MAX in *. lia.
Qed.

Lemma MBr_stk_ok_w : forall sp m rest src pp lo, BOK sp rest src pp lo ->
  forall Ib m1 (w : word) (a : Z) (j : nat), MBr sp m rest src pp lo Ib m1 -> w = wa a ->
  lo <= a -> a + Z.of_nat j <= bv_unsigned sp + FRAME_LOCALS -> store_ok rsegs m1 w j = true.
Proof.
  intros spv mv restv srcv ppv lov HK Ib m1 w a j MB -> H1 H2.
  exact (MBr_stk_ok spv mv restv srcv ppv lov HK Ib m1 a j MB H1 H2).
Qed.
