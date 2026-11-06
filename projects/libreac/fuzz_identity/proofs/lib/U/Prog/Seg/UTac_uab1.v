From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require MState Exec Regs6ss RegisterBridge Step ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma t_res_top :
  forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 21) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma t_segs_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 20) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma t_fs_none : forall (l : list Segment) top a n,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) l = true -> top <= a -> 0 < n ->
  find_segment l a n = None.
Proof.
  induction l as [|s l IH]; intros top a n H Ha Hn; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  match goal with |- context [if ?c then _ else _] => destruct c eqn:E end.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - apply IH with top; assumption.
Qed.

Lemma t_fs_in : forall (l : list Segment) a n seg, find_segment l a n = Some seg ->
  In seg l /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. lia.
  - destruct (IH a n seg H) as (Hi & H1 & H2). split; [right; exact Hi|]. lia.
Qed.

Lemma t_wr_present : forall (m : word -> option byte) a, 2 ^ 20 <= a < 2 ^ 64 ->
  writable_at rsegs m a -> present m a.
Proof.
  intros m a Ha. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite MState.unsigned_lit by lia.
  rewrite (t_fs_none rsegs (2 ^ 20) a 1 t_segs_top) by lia.
  intros W. exfalso. apply W. reflexivity.
Qed.

Lemma t_ro_hi : forall a, 2 ^ 20 <= a < 2 ^ 64 -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold Mem.ro_addr. rewrite MState.unsigned_lit by lia.
  rewrite (t_fs_none rsegs (2 ^ 20) a 1 t_segs_top) by lia. reflexivity.
Qed.

Lemma t_ro_hi_w : forall a : word, 2 ^ 20 <= bv_unsigned a -> Mem.ro_addr rsegs a = false.
Proof.
  intros a Ha. pose proof (bv_unsigned_in_range 64 a) as R. unfold bv_modulus in R. cbn in R.
  rewrite <- (Step.Z_to_bv_lit_self a). apply t_ro_hi. lia.
Qed.

Lemma t_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. exact MState.unsigned_lit. Qed.

Lemma t_munch_eq : forall W (m m' : word -> option byte) x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof. intros W m m' x H R O. apply H. rewrite t_unsigned by exact R. exact O. Qed.

Lemma t_mbyte_munch : forall s W m m' x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  mbyte s m' x = mbyte s m x.
Proof. intros s W m m' x H R O. unfold mbyte. rewrite (t_munch_eq W m m' x H R O). reflexivity. Qed.

Lemma t_wr_munch : forall s W m m' x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  (writable_at s m x <-> writable_at s m' x).
Proof. intros s W m m' x H R O. unfold writable_at, wview. rewrite (t_munch_eq W m m' x H R O). tauto. Qed.

Lemma t_bytes_at_eq : forall s m m' a bs, bytes_at s m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte s m' (a + i) = mbyte s m (a + i)) ->
  bytes_at s m' a bs.
Proof.
  intros s m m' a bs (H1 & H2 & H) E. split; [exact H1|]. split; [exact H2|].
  intros i Hi. change (mbyte s m' (a + Z.of_nat i) = nth_error bs i).
  rewrite E by lia. exact (H i Hi).
Qed.

Lemma t_mbyte_bytes_at : forall s m a bs i, bytes_at s m a bs -> (i < length bs)%nat ->
  mbyte s m (a + Z.of_nat i) = nth_error bs i.
Proof. intros s m a bs i (_ & _ & H) Hi. exact (H i Hi). Qed.

Lemma t_pairwise_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros X R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - destruct H as [Hx Hl]. split; [|exact (IH Hl)].
    intros y Hy. apply Hx. apply (Permutation_in y (Permutation_sym HP) Hy).
  - destruct H as [Hy [Hx Hl]]. split; [|split].
    + intros z [<-|Hz]; [apply Hs; apply Hy; left; reflexivity | apply Hx; exact Hz].
    + intros z Hz. apply Hy. right. exact Hz.
    + exact Hl.
  - exact (IH2 (IH1 H)).
Qed.

Lemma t_pairwise_app : forall {X} (R : X -> X -> Prop) h b u v,
  pairwise R (h ++ b) -> In u h -> In v b -> R u v.
Proof.
  intros X R h. induction h as [|x h IH]; intros b u v H Hu Hv; [destruct Hu|].
  destruct H as [Hx Hl]. destruct Hu as [<-|Hu].
  - apply Hx. apply in_or_app. right. exact Hv.
  - exact (IH b u v Hl Hu Hv).
Qed.

Lemma t_rd_sym : forall x y, ranges_disjoint x y -> ranges_disjoint y x.
Proof. intros [a n] [b k]. unfold ranges_disjoint. cbn. lia. Qed.

Lemma t_perm_disj : forall l h b q k a n, pairwise ranges_disjoint l -> Permutation l (h ++ b) ->
  In (q, k) h -> In (a, n) b -> forall i j, 0 <= i < k -> 0 <= j < n -> q + i <> a + j.
Proof.
  intros l h b q k a n HP HL Hq Ha i j Hi Hj.
  pose proof (t_pairwise_app _ h b _ _ (t_pairwise_perm _ t_rd_sym l _ HL HP) Hq Ha) as D.
  unfold ranges_disjoint in D. cbn in D. lia.
Qed.

Lemma t_perm_rd : forall l h b u v, pairwise ranges_disjoint l -> Permutation l (h ++ b) ->
  In u h -> In v b -> ranges_disjoint u v.
Proof. intros l h b u v HP HL Hu Hv. exact (t_pairwise_app _ h b _ _ (t_pairwise_perm _ t_rd_sym l _ HL HP) Hu Hv). Qed.

Lemma t_bytes_munch : forall s W m m' a bs, bytes_at s m a bs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> outside W (a + i)) -> bytes_at s m' a bs.
Proof.
  intros s W m m' a bs H HM HO. pose proof H as (H1 & H2 & _). apply (t_bytes_at_eq s m); [exact H|].
  intros i Hi. apply (t_mbyte_munch s W); [exact HM | lia | exact (HO i Hi)].
Qed.

Lemma t_mb1 : forall s lo hi m m' a, munch [(lo, hi)] m m' -> 0 <= a < 2 ^ 64 -> a < lo \/ hi <= a ->
  mbyte s m' a = mbyte s m a.
Proof. intros s lo hi m m' a H R O. apply (t_mbyte_munch s _ m m' a H R). cbn. split; [lia | exact I]. Qed.

Lemma t_ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 z).
Proof. intros z Hz H. apply ret_ok_even. rewrite t_unsigned by exact Hz. exact H. Qed.

Lemma t_ret_pc : forall k, YK0s.ret_ok k -> MState.ret_pc k = k.
Proof. exact KindBGlue.kb_ret_pc. Qed.

Lemma t_inb_past : forall inp j, nlen inp <= j -> inb inp j = 0.
Proof.
  intros inp j H. unfold inb, RcIdentModel.nthb. rewrite nth_overflow by (unfold nlen in H; lia). reflexivity.
Qed.

Lemma t_bz_range : forall b : byte, 0 <= RcIdentModel.bz b < 256.
Proof. exact bz_range. Qed.

Lemma t_raw_div : forall lo hi, 0 <= lo < 256 -> 0 <= hi -> (lo + 256 * hi) / 16384 = hi / 64.
Proof.
  intros lo hi H1 H2. change 16384 with (256 * 64). rewrite <- Z.div_div by lia.
  replace (lo + 256 * hi) with (lo + hi * 256) by ring. rewrite Z.div_add by lia.
  rewrite (Z.div_small lo 256) by lia. reflexivity.
Qed.

Lemma t_signed : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite ZBridge.zb_signed. rewrite t_unsigned by lia.
  destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.

Lemma t_nth_firstn : forall (l : list byte) n j, (j < n)%nat -> nth_error (firstn n l) j = nth_error l j.
Proof.
  induction l as [|x l IH]; intros [|n] [|j] H; cbn; try reflexivity; try lia. apply IH. lia.
Qed.

Lemma t_nth_skipn : forall (l : list byte) n j, nth_error (skipn n l) j = nth_error l (n + j).
Proof. induction l as [|x l IH]; intros [|n] j; cbn; try reflexivity; [destruct j; reflexivity | apply IH]. Qed.

Lemma t_nth_seq : forall s k i, (i < k)%nat -> nth_error (seq s k) i = Some (s + i)%nat.
Proof.
  intros s k. revert s. induction k as [|k IH]; intros s i Hi; [lia|].
  destruct i as [|i]; cbn; [f_equal; lia|]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma t_present_rw_cells : forall (m : word -> option byte) a (k : nat), 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> present m (a + i)) ->
  exists junk, rw_cells rsegs m a [Cells.CB k junk].
Proof.
  intros m a k Ha Hk H.
  exists (map (fun i => match m (Mem.wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 k)).
  assert (L : length (map (fun i => match m (Mem.wa (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end)
                         (seq 0 k)) = k) by (rewrite length_map, length_seq; reflexivity).
  split; [split|].
  - cbn. split; [exact L | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact Ha|]. split; [rewrite L; exact Hk|].
    intros i Hi. rewrite L in Hi.
    destruct (H (Z.of_nat i) ltac:(lia)) as [b E].
    rewrite (map_nth_error _ _ _ (t_nth_seq 0 k i Hi)). cbn [Nat.add].
    unfold Mem.mrd. unfold Mem.wa. rewrite E. reflexivity.
  - split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct (H i ltac:(lia)) as [b E]. unfold wview, Mem.wa. rewrite E. discriminate.
Qed.

Lemma t_rw_cells_rel : forall m m0 a cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 a _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 a _ HR Hw).
Qed.

Lemma t_rw_cells_norm : forall m a cs, ro_agree rsegs m -> rw_cells rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> Mem.ro_addr rsegs (Z_to_bv 64 (a + i)) = false) ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs RO [[Hwf Hb] Hw] Hro. split; [split; [exact Hwf|]|].
  - exact (bytes_at_normalize rsegs m a _ RO Hb).
  - exact (wr_at_norm rsegs m (normalize rsegs m) a _ (mem_rel_normalize rsegs m RO) Hw Hro).
Qed.

Lemma t_rw_cells_of : forall m a bs, bytes_at rsegs m a bs -> wr_at rsegs m a (Z.of_nat (length bs)) ->
  rw_cells rsegs m a [Cells.CB (length bs) bs].
Proof.
  intros m a bs Hb Hw. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma t_cb_bytes : forall m a k bs, rw_cells rsegs m a [Cells.CB k bs] -> bytes_at rsegs m a bs.
Proof. intros m a k bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma t_getr_R : forall {fx : FPState} (R : bvmap 5 word) (r : bv 5), bv_eqb r 0 = false ->
  getr R r = Sem.reg_get R r.
Proof. intros fx R r H. unfold getr. rewrite H. reflexivity. Qed.

Lemma t_cs_regs : forall {fx : FPState} regs regs' R, (forall r, getr regs' r = getr R r) ->
  (forall r, callee_saved r -> Sem.reg_get R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
  intros fx regs regs' R HG HC r Hr. rewrite HG. rewrite t_getr_R; [exact (HC r Hr)|].
  unfold callee_saved in Hr. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia.
Qed.

Lemma t_hwb_len : forall inp i, length (rec_hwb inp i) = 8%nat.
Proof.
  intros inp i. unfold rec_hwb. induction i as [|i IH]; cbn [rec_hw]; [reflexivity|].
  destruct ((rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? rec_k inp i)) eqn:E; [|exact IH].
  apply andb_prop in E as [_ E]. apply Z.leb_le in E.
  rewrite length_firstn, rec_pl_length. lia.
Qed.

Lemma t_addr_range : forall inp i, 0 <= rec_addr inp i < 65536.
Proof.
  intros inp i. unfold rec_addr, rec_raw, h_raw, h_lo, h_hi. pose proof (inb_range inp (rec_c inp i)).
  pose proof (inb_range inp (rec_c inp i + 1)). unfold pick, RcIdentModel.ADDR_FIRMWARE,
    RcIdentModel.ADDR_REAC_VERSION, RcIdentModel.ADDR_MODEL_NAME.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Section Slot.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma ff_segs : ms_segs B = rsegs.
Proof using All. destruct FF as (H & _). exact H. Qed.

Lemma ff_malloc : ms_malloc B = 0x15ab4.
Proof using All. destruct FF as (_ & _ & H & _). exact H. Qed.

Lemma ff_free : ms_free B = 0x15974.
Proof using All. destruct FF as (_ & _ & _ & H & _). exact H. Qed.

Lemma ff_errno : errno_addr B = 0x304b0 - 164.
Proof using All.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & HE & _).
  unfold errno_addr. rewrite HT, HE. reflexivity.
Qed.

Lemma ff_tp : ms_tp B = 0x304b0.
Proof using All.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & _). exact HT.
Qed.

Lemma ff_alloc : frame_allocator B (APIf rc).
Proof using All.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & H). exact (H rc fx).
Qed.

Lemma ff_relro : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof using All.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma ff_laws : MR_laws B (aa_MR (APIf rc)).
Proof using All. exact (aa_laws (APIf rc)). Qed.

Lemma ff_ax : AllocExtra B (aa_MR (APIf rc)).
Proof using All.
  pose proof ff_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma ff_bw : blocks_writable B (APIf rc).
Proof using All.
  pose proof ff_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma t_img_lt : forall a, in_img B a -> 0 <= a < 2 ^ 21.
Proof using All.
  intros a (_ & s & Hin & H1 & H2). rewrite ff_segs in Hin.
  pose proof (proj1 (forallb_forall _ _) t_res_top s Hin) as T. apply Z.leb_le in T.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma t_in_img_data : forall a, 131072 <= a < 331776 -> in_img B a.
Proof using All.
  intros a Ha. unfold in_img. rewrite ff_segs. split; [discriminate|].
  exists (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)). split.
  - apply nth_In. vm_compute. lia.
  - assert (E1 : bv_unsigned (fst (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0))) = 131072)
      by (vm_compute; reflexivity).
    assert (E2 : bv_unsigned (snd (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0))) = 200704)
      by (vm_compute; reflexivity).
    rewrite E1, E2. lia.
Qed.

Lemma t_in_img_of_seg : forall a seg, 0 <= a -> find_segment rsegs a 1 = Some seg -> in_img B a.
Proof using All.
  intros a seg Ha F. destruct (t_fs_in _ _ _ _ F) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) t_segs_top seg Hin) as T. apply Z.leb_le in T.
  unfold in_img. rewrite ff_segs. split; [intro E; rewrite E in Hin; destruct Hin|].
  exists (segment_reservation seg). split; [apply in_map; exact Hin|].
  unfold segment_reservation, page_round_down_Z, page_round_up_Z. cbn [fst snd].
  change page_size with 4096.
  pose proof (N2Z.is_nonneg (seg_base seg)) as P1. pose proof (N2Z.is_nonneg (seg_size seg)) as P2.
  set (bs := Z.of_N (seg_base seg)) in *. set (sz := Z.of_N (seg_size seg)) in *.
  pose proof (Z.mul_div_le bs 4096 ltac:(lia)) as D1.
  pose proof (Z.div_pos bs 4096 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.mul_div_le (bs + sz + 4096 - 1) 4096 ltac:(lia)) as D3.
  pose proof (Z.mul_succ_div_gt (bs + sz + 4096 - 1) 4096 ltac:(lia)) as D4.
  rewrite !t_unsigned by lia. lia.
Qed.

Lemma t_present_out : forall (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img B a ->
  writable_at rsegs m a -> present m a.
Proof using All.
  intros m a Ha NI. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite t_unsigned by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F.
  - exfalso. apply NI. eapply t_in_img_of_seg; [lia | exact F].
  - intros W. exfalso. apply W. reflexivity.
Qed.

Lemma t_ro_img : forall a : word, Mem.ro_addr rsegs a = true -> in_img B (bv_unsigned a).
Proof using All.
  intros a E. unfold Mem.ro_addr in E.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:F; [|discriminate].
  eapply t_in_img_of_seg; [apply bv_unsigned_in_range | exact F].
Qed.

Lemma t_owned_low : forall L A mem md a, aa_MR (APIf rc) L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling.
Proof using All. intros L A mem md a HM Ho. exact (mr_owned_low B _ ff_laws L A mem md a HM Ho). Qed.

Lemma t_block : forall L A mem md q k i, aa_MR (APIf rc) L A mem md -> In (q, k) (blocks L A) -> 0 <= i < k ->
  present mem (q + i) /\ 4096 <= q /\ q + k <= alloc_ceiling /\ ~ owned B L A (q + i) /\ ~ in_img B (q + i) /\
  writable_at rsegs mem (q + i).
Proof using All.
  intros L A mem md q k i HM Hin Hi.
  pose proof (ff_bw L A mem md q k i HM Hin Hi) as W. rewrite ff_segs in W.
  unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn in E. injection E as <- <-.
  destruct (mr_blocks B _ ff_laws L A mem md p k' i HM Hp Hi) as (H1 & H2 & H3 & H4).
  pose proof (ax_blocks_img ff_ax L A mem md p k' i HM Hp Hi) as H5.
  repeat split; assumption.
Qed.

Lemma t_img_not_owned : forall L A mem md a, aa_MR (APIf rc) L A mem md -> in_img B a -> ~ static_owned B a ->
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ owned B L A a.
Proof using All.
  intros L A mem md a HM Hi Hs Hc [Ho|Ho]; [| exact (Hs Ho)].
  exact (Hc (ax_img ff_ax L A mem md a HM Hi Ho)).
Qed.

Lemma t_md : forall L A mem md, aa_MR (APIf rc) L A mem md -> m_halted md = None /\ m_vm_lazy md = [].
Proof using All.
  intros L A mem md H. destruct (mr_model _ _ ff_laws _ _ _ _ H) as (H1 & H2 & _). split; assumption.
Qed.

Lemma ff_vals : ms_guard B = 0x50720 /\ ms_got_guard B = 0x1f138 /\ ms_ctx B = 0x507b8 /\
  ms_lock B = 0x507b0 /\ ms_libc B = 0x50740 /\ ms_size_classes B = 0x10678 /\ ms_small_cnt B = 0x106d8 /\
  ms_med_cnt B = 0x106f3 /\ ms_debruijn B = 0x10658 /\
  @sk_ofl_head SH = 0x50b70 /\ @sk_ofl_lock SK = 0x50b68 /\ @sk_threaded SK = 0x50741.
Proof using All.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & _ & _ & _
    & H20 & H21 & H22 & _).
  repeat split; assumption.
Qed.

Lemma t_env : forall a, (@sk_threaded SK = a \/ (@sk_ofl_lock SK <= a < @sk_ofl_lock SK + 4) \/
    (@sk_ofl_head SH <= a < @sk_ofl_head SH + 8)) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof using All.
  intros a Ha. pose proof ff_vals as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12).
  pose proof ff_errno as E. unfold static_owned, CTX_SIZE, vml_lo, vml_len.
  rewrite (ff_vmlock_u _ _ _ _ _ _ _ FF), (ff_dbl_u _ _ _ _ _ _ _ FF), Z.max_id. rewrite E, V1, V2, V3, V4, V5, V6, V7, V8, V9.
  rewrite V10, V11, V12 in Ha.
  split; [apply t_in_img_data; lia | lia].
Qed.

Lemma t_sink : forall mem mem' md md', sink_none B mem md -> m_fds md' = m_fds md ->
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  sink_none B mem' md'.
Proof using All.
  intros mem mem' md md' ((H1 & H2) & H3 & H4) Hf E.
  assert (E' : forall a, (@sk_threaded SK = a \/ (@sk_ofl_lock SK <= a < @sk_ofl_lock SK + 4) \/
    (@sk_ofl_head SH <= a < @sk_ofl_head SH + 8)) -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a).
  { intros a Ha. destruct (t_env a Ha) as (X1 & X2 & X3 & X4). exact (E a X1 X2 X3 X4). }
  split; [split|split].
  - intros k Hk. rewrite E' by (left; cbn in Hk; lia). exact (H1 k Hk).
  - intros k Hk. rewrite E' by (right; left; cbn in Hk; lia). exact (H2 k Hk).
  - intros k Hk. rewrite E' by (right; right; lia). exact (H3 k Hk).
  - rewrite Hf. exact H4.
Qed.

Lemma FR_regs : forall g km hb L A regs regs' mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem md.
Proof using All.
  intros g km hb L A regs regs' mem md (H1 & H2 & H3 & H4 & HR) E2 E3 E4.
  split; [exact H1|]. split; [rewrite E2; exact H2|]. split; [rewrite E3; exact H3|].
  split; [rewrite E4; exact H4|]. exact HR.
Qed.

Lemma FR_mem : forall g km hb L A regs mem md mem' W,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (g_S g - SLOT_K <= x < g_S g - 104) ->
     (forall q k, In (q, k) hb -> ~ (q <= x < q + k)) -> outside W x) ->
  FR B APIf ra empty g km hb L A regs mem' md.
Proof using All.
  intros g km hb L A regs mem md mem' W HFR HP HM HW HO.
  pose proof ff_segs as SEG. pose proof ff_errno as ERR. pose proof alloc_ceiling_value as AC.
  destruct HFR as (HGV & SP & GP & TP & SAV & STK & MIm & REL & HMR & HWF & HBD & INIT & HMD & F1 & F2 & F3
    & ERRW & SINK & RES & WIN).
  pose proof HGV as (Gn & Gp & Gblk & GS16 & GSK & GS47 & GROOM & GRSP & GRTP & _).
  unfold SLOT_K, SLOT_STACK in *.
  assert (HBIN : forall q k, In (q, k) hb -> In (q, k) (blocks L A)).
  { intros q k H. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact H. }
  assert (HBX : forall q k x, In (q, k) hb -> q <= x < q + k ->
     4096 <= x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L A x).
  { intros q k x Hq Hx. destruct (t_block L A mem md q k (x - q) HMR (HBIN q k Hq) ltac:(lia))
      as (_ & B2 & B3 & B4 & B5 & _).
    replace (q + (x - q)) with x in * by ring. split; [lia|]. split; assumption. }
  assert (OLOW : forall x, 0 <= x < alloc_ceiling -> (forall q k, In (q, k) hb -> ~ (q <= x < q + k)) ->
     outside W x) by (intros x Hx Hn; apply HO; [lia | lia | exact Hn]).
  assert (OIMG : forall x, in_img B x -> outside W x).
  { intros x Hx. pose proof (t_img_lt x Hx). apply OLOW; [lia|].
    intros q k Hq Hr. destruct (HBX q k x Hq Hr) as (_ & NI & _). exact (NI Hx). }
  assert (OOWN : forall x, owned B L A x -> outside W x).
  { intros x Hx. pose proof (t_owned_low L A mem md x HMR Hx). apply OLOW; [lia|].
    intros q k Hq Hr. destruct (HBX q k x Hq Hr) as (_ & _ & NO). exact (NO Hx). }
  assert (OUP : forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (g_S g - 65536 <= x < g_S g - 104) -> outside W x).
  { intros x Hx Hn. apply HO; [lia | exact Hn |]. intros q k Hq Hr. destruct (HBX q k x Hq Hr). lia. }
  assert (EQ : forall x, outside W x -> 0 <= x < 2 ^ 64 ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
     (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Ho Hx. split; [exact (t_mbyte_munch _ W mem mem' x HM Hx Ho) | exact (t_wr_munch _ W mem mem' x HM Hx Ho)]. }
  assert (WM : forall x, writable_at (ms_segs B) mem x -> writable_at (ms_segs B) mem' x).
  { intros x Hx. unfold writable_at in *. rewrite SEG in *. apply HW. exact Hx. }
  assert (HMR' : aa_MR (APIf rc) L A mem' md).
  { destruct (mr_model _ _ ff_laws _ _ _ _ HMR) as (Hh & Hl & Hmat).
    apply (mr_frame B _ ff_laws L A mem mem' md md HMR).
    - intros a Ho. pose proof (t_owned_low L A mem md a HMR Ho).
      exact (proj1 (EQ a (OOWN a Ho) ltac:(lia))).
    - intros a Ho [b Hb]. pose proof (t_owned_low L A mem md a HMR Ho).
      exists b. rewrite (t_munch_eq W mem mem' a HM ltac:(lia) (OOWN a Ho)). exact Hb.
    - intros p n i Hin Hi.
      assert (Hb : In (ptr_addr L p, n) (blocks L A)) by (apply in_map_iff; exists (p, n); split; [reflexivity | exact Hin]).
      destruct (t_block L A mem md _ _ i HMR Hb Hi) as (_ & B2 & B3 & _ & B5 & B6).
      apply (t_present_out mem' (ptr_addr L p + i) ltac:(lia) B5).
      unfold writable_at. apply HW. exact B6.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HGV|]. split; [exact SP|]. split; [exact GP|]. split; [exact TP|].
  split.
  { apply (t_bytes_at_eq _ mem); [exact SAV|]. intros i Hi.
    assert (Hl : Z.of_nat (length (saved_bytes ra g)) = 104) by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite SEG in EQ. apply (EQ (g_S g - 104 + i)); [apply OUP; lia | lia]. }
  split.
  { destruct STK as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha. unfold SLOT_K, SLOT_STACK in Ha.
    assert (Wa : writable_at rsegs mem' a) by (rewrite <- SEG; apply WM; rewrite SEG; exact (proj1 (S3 a Ha))).
    split; [exact Wa|]. destruct (t_wr_present mem' a ltac:(lia) Wa) as [b Hb].
    exists b. unfold Mem.mrd, Mem.wa. rewrite Hb. reflexivity. }
  split.
  { intros a Hra. unfold MI in *. rewrite <- (MIm a Hra). unfold Mem.mrd.
    rewrite SEG in Hra. pose proof (t_ro_img a Hra) as Hi.
    rewrite <- (Step.Z_to_bv_lit_self a). rewrite (t_munch_eq W mem mem' (bv_unsigned a) HM
      (bv_unsigned_in_range 64 a) (OIMG _ Hi)). reflexivity. }
  split.
  { intros a Ha. destruct (ff_relro a Ha) as (Hi & _). rewrite <- (REL a Ha).
    pose proof (t_img_lt a Hi). exact (proj1 (EQ a (OIMG a Hi) ltac:(lia))). }
  split; [exact HMR'|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact INIT|]. split; [exact HMD|].
  split.
  { intros a Ha Hs He. unfold SLOT_K, SLOT_STACK in Hs. destruct (F1 a Ha Hs He) as [E1 E2].
    destruct (EQ a (OUP a Ha ltac:(lia)) ltac:(lia)) as [E3 E4]. split; [congruence | tauto]. }
  split.
  { intros a Hi Hs Hc He. destruct (F2 a Hi Hs Hc He) as [E1 E2]. pose proof (t_img_lt a Hi).
    destruct (EQ a (OIMG a Hi) ltac:(lia)) as [E3 E4]. split; [congruence | tauto]. }
  split.
  { intros a k i Hin Hi. rewrite <- (F3 a k i Hin Hi).
    assert (Hb : In (a, k) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
    destruct (t_block L A mem md a k i HMR Hb Hi) as (_ & B2 & B3 & _).
    apply (EQ (a + i)); [|lia]. apply OLOW; [lia|]. intros q k' Hq Hr.
    exact (t_perm_disj _ hb _ q k' a k (mr_blocks_disjoint B _ ff_laws L A mem md HMR) HP Hq Hin (a + i - q) i
      ltac:(lia) Hi ltac:(lia)). }
  split; [intros a Ha; apply WM; exact (ERRW a Ha)|].
  split.
  { apply (t_sink mem mem' md md SINK eq_refl). intros a Hi _ _ _. pose proof (t_img_lt a Hi).
    exact (proj1 (EQ a (OIMG a Hi) ltac:(lia))). }
  split; [exact RES|].
  intros a Ha. unfold SLOT_K, SLOT_STACK in Ha. apply WM. exact (WIN a Ha).
Qed.

Lemma t_spz : forall g km hb L A regs regs1 mem md,
  FR B APIf ra empty g km hb L A regs mem md -> getr regs1 2 = getr regs 2 -> spZ regs1 = g_S g - 384.
Proof using All.
  intros g km hb L A regs regs1 mem md (HGV & SP & _) E2. pose proof HGV as (_ & _ & _ & _ & GSK & GS47 & _).
  pose proof alloc_ceiling_value as AC. unfold SLOT_K, SLOT_STACK in GSK.
  unfold spZ. rewrite E2, SP. unfold fsp, SLOT_FRAME. apply t_unsigned. lia.
Qed.

Lemma CP_of_FR : forall g km hb L A regs regs1 mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  getr regs1 2 = getr regs 2 -> getr regs1 4 = getr regs 4 -> YK0s.ret_ok (getr regs1 1) ->
  call_pre B (aa_MR (APIf rc)) L A regs1 mem md.
Proof using All.
  intros g km hb L A regs regs1 mem md HFR E2 E4 HRA.
  pose proof (t_spz g km hb L A regs regs1 mem md HFR E2) as SPZ.
  destruct HFR as (HGV & SP & GP & TP & SAV & STK & MIm & REL & HMR & HWF & HBD & INIT & HMD & F1 & F2 & F3
    & ERRW & SINK & RES & WIN).
  pose proof HGV as (Gn & Gp & Gblk & GS16 & GSK & GS47 & GROOM & GRSP & GRTP & _).
  pose proof alloc_ceiling_value as AC. unfold SLOT_K, SLOT_STACK in *.
  unfold call_pre. rewrite SPZ. unfold ALLOC_STACK.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HRA|].
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply WIN; lia|].
  split; [rewrite E4, TP, GRTP; reflexivity|].
  split; [exact ERRW|].
  intros H. rewrite INIT in H. discriminate.
Qed.

Lemma CPk_of_FR : forall K g km hb L A regs regs1 mem md, 0 <= K <= 8208 ->
  FR B APIf ra empty g km hb L A regs mem md ->
  getr regs1 2 = getr regs 2 -> getr regs1 4 = getr regs 4 -> YK0s.ret_ok (getr regs1 1) ->
  call_pre_k B (aa_MR (APIf rc)) K L A regs1 mem md.
Proof using All.
  intros K g km hb L A regs regs1 mem md HK HFR E2 E4 HRA.
  pose proof (t_spz g km hb L A regs regs1 mem md HFR E2) as SPZ.
  destruct HFR as (HGV & SP & GP & TP & SAV & STK & MIm & REL & HMR & HWF & HBD & INIT & HMD & F1 & F2 & F3
    & ERRW & SINK & RES & WIN).
  pose proof HGV as (Gn & Gp & Gblk & GS16 & GSK & GS47 & GROOM & GRSP & GRTP & _).
  pose proof alloc_ceiling_value as AC. unfold SLOT_K, SLOT_STACK in *.
  unfold call_pre_k. rewrite SPZ.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HRA|].
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply WIN; lia|].
  split; [rewrite E4, TP, GRTP; reflexivity|].
  split; [exact ERRW|].
  intros H. rewrite INIT in H. discriminate.
Qed.

Lemma FR_malloc : forall g km hb L A regs regs1 mem md n c',
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs1 2 = getr regs 2 -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  malloc_ret B (APIf rc) ALLOC_STACK L A regs1 mem md n (sb_hb (g_b g) hb) c' ->
  exists L' A' regs' mem' md' res,
    c' = mkCfg (mkst regs' (getr regs1 1) mem' (seg_rom (ms_segs B))) md' /\
    FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md' /\
    Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g)) /\
    regs_preserved regs1 regs' /\ getr regs' 10 = Z_to_bv 64 res /\
    res <> 0 /\ res mod 16 = 0 /\ fresh_block B res n /\
    (forall a, fsp g <= a < g_S g -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) /\
    (forall q k i, In (q, k) hb -> 0 <= i < k -> mbyte (ms_segs B) mem' (q + i) = mbyte (ms_segs B) mem (q + i)).
Proof using All.
  intros g km hb L A regs regs1 mem md n c' HFR HP E2 E3 E4 HMret.
  pose proof (t_spz g km hb L A regs regs1 mem md HFR E2) as SPZ.
  pose proof ff_segs as SEG. pose proof ff_errno as ERR. pose proof alloc_ceiling_value as AC.
  destruct HMret as (L' & A' & R2 & mem' & md' & res & -> & POST & R10 & NZ & AL & FRESH & BLK & KEPT & RO'
    & GK & UB & INIT' & LEN & RES').
  destruct POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & (vm' & HMD') & HFRAME & HBLKS & HSCR).
  destruct BLK as (b1 & b2 & BL1 & BL2).
  destruct HFR as (HGV & SP & GP & TP & SAV & STK & MIm & REL & HMR & HWF & HBD & INIT & HMD & F1 & F2 & F3
    & ERRW & SINK & RES & WIN).
  pose proof HGV as (Gn & Gp & Gblk & GS16 & GSK & GS47 & GROOM & GRSP & GRTP & _).
  unfold SLOT_K, SLOT_STACK in *.
  assert (HBIN : forall q k, In (q, k) hb -> In (q, k) (blocks L A)).
  { intros q k H. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact H. }
  assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho;
      [pose proof (t_owned_low L A mem md a HMR Ho) | pose proof (t_owned_low L' A' mem' md' a HMR' Ho)]; lia. }
  assert (UPEQ : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 384 - 8192 <= a < g_S g - 384) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hs He. destruct (NOWN a (proj1 Ha)) as [N1 N2].
    apply HFRAME; [left; exact Ha | exact N1 | exact N2 | | intros F; exact F].
    unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK. intros [X|X]; [lia | exact (He X)]. }
  assert (IMGEQ : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Hi Hs Hc He. pose proof (t_img_lt a Hi).
    apply HFRAME; [right; exact Hi | exact (t_img_not_owned L A mem md a HMR Hi Hs Hc)
      | exact (t_img_not_owned L' A' mem' md' a HMR' Hi Hs Hc) | | intros F; exact F].
    unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK. intros [X|X]; [lia | exact (He X)]. }
  assert (WM' : forall a, g_S g - 65536 <= a < g_S g -> writable_at (ms_segs B) mem' a).
  { intros a Ha. rewrite ERR in UPEQ.
    destruct (Z_lt_le_dec a (g_S g - 384)) as [Hl|Hl]; [destruct (Z_lt_le_dec a (g_S g - 384 - 8192)) as [Hl'|Hl']|].
    - apply (proj1 (proj2 (UPEQ a ltac:(lia) ltac:(lia) ltac:(lia)))). apply WIN. lia.
    - apply HSCR. unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK. left. lia.
    - apply (proj1 (proj2 (UPEQ a ltac:(lia) ltac:(lia) ltac:(lia)))). apply WIN. lia. }
  exists L', A', R2, mem', md', res. split; [reflexivity|].
  split.
  { split; [exact HGV|].
    split; [etransitivity; [exact (HPRES 2 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E2|]; exact SP|].
    split; [etransitivity; [exact (HPRES 3 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E3|]; exact GP|].
    split; [etransitivity; [exact (HPRES 4 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E4|]; exact TP|].
    split.
    { apply (t_bytes_at_eq _ mem); [exact SAV|]. intros i Hi.
      assert (Hl : Z.of_nat (length (saved_bytes ra g)) = 104)
        by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
      rewrite <- SEG. rewrite ERR in UPEQ. apply (UPEQ (g_S g - 104 + i)); lia. }
    split.
    { destruct STK as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha.
      unfold SLOT_K, SLOT_STACK in Ha.
      assert (Wa : writable_at rsegs mem' a) by (rewrite <- SEG; apply WM'; lia).
      split; [exact Wa|]. destruct (t_wr_present mem' a ltac:(lia) Wa) as [bb Hb].
      exists bb. unfold Mem.mrd, Mem.wa. rewrite Hb. reflexivity. }
    split; [exact RO'|].
    split.
    { intros a Ha. destruct (ff_relro a Ha) as (Hi & Hs & Hc & He). rewrite <- (REL a Ha).
      exact (proj1 (IMGEQ a Hi Hs Hc He)). }
    split; [exact HMR'|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact INIT'|].
    split.
    { destruct HMD as (vm & ->). exists vm'. rewrite HMD'. apply YI06.with_vmmaps_twice. }
    split.
    { intros a Ha Hs He. unfold SLOT_K, SLOT_STACK in Hs. destruct (F1 a Ha Hs He) as [X1 X2].
      destruct (UPEQ a Ha ltac:(lia) He) as [X3 X4]. split; [congruence | tauto]. }
    split.
    { intros a Hi Hs Hc He. destruct (F2 a Hi Hs Hc He) as [X1 X2].
      destruct (IMGEQ a Hi Hs Hc He) as [X3 X4]. split; [congruence | tauto]. }
    split.
    { intros a k i Hin Hi. rewrite <- (F3 a k i Hin Hi).
      assert (Hb : In (a, k) (blocks L A))
        by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
      exact (KEPT a k i Hb (fun F => F) Hi). }
    split; [intros a Ha; apply HSCR; right; exact Ha|].
    split.
    { apply (t_sink mem mem' md md' SINK); [rewrite HMD'; reflexivity|].
      intros a Hi Hs Hc He. exact (proj1 (IMGEQ a Hi Hs Hc He)). }
    split; [exact (resb_malloc (g_b g) (km + 1) hb (hb ++ [(res, n)]) A' res n
                     (Permutation_sym (Permutation_cons_append hb (res, n))) RES')|].
    intros a Ha. unfold SLOT_K, SLOT_STACK in Ha. apply WM'. lia. }
  split.
  { rewrite BL1. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
    rewrite <- BL2. eapply Permutation_trans; [apply perm_skip; exact HP|].
    rewrite <- app_assoc. cbn [app]. apply Permutation_middle. }
  split; [exact HPRES|]. split; [exact R10|]. split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|].
  split.
  { intros a Ha. unfold fsp, SLOT_FRAME in Ha. rewrite ERR in UPEQ. exact (proj1 (UPEQ a ltac:(lia) ltac:(lia) ltac:(lia))). }
  intros q k i Hq Hi. exact (KEPT q k i (HBIN q k Hq) (fun F => F) Hi).
Qed.

Lemma FR_mallocK : forall K g km hb L A regs regs1 mem md n c', 0 <= K <= 8208 ->
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs1 2 = getr regs 2 -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  malloc_ret B (APIf rc) K L A regs1 mem md n (sb_hb (g_b g) hb) c' ->
  exists L' A' regs' mem' md' res,
    c' = mkCfg (mkst regs' (getr regs1 1) mem' (seg_rom (ms_segs B))) md' /\
    FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md' /\
    Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g)) /\
    regs_preserved regs1 regs' /\ getr regs' 10 = Z_to_bv 64 res /\
    res <> 0 /\ res mod 16 = 0 /\ fresh_block B res n /\
    (forall a, fsp g <= a < g_S g -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) /\
    (forall q k i, In (q, k) hb -> 0 <= i < k -> mbyte (ms_segs B) mem' (q + i) = mbyte (ms_segs B) mem (q + i)).
Proof using All.
  intros K g km hb L A regs regs1 mem md n c' HK HFR HP E2 E3 E4 HMret.
  pose proof (t_spz g km hb L A regs regs1 mem md HFR E2) as SPZ.
  pose proof ff_segs as SEG. pose proof ff_errno as ERR. pose proof alloc_ceiling_value as AC.
  destruct HMret as (L' & A' & R2 & mem' & md' & res & -> & POST & R10 & NZ & AL & FRESH & BLK & KEPT & RO'
    & GK & UB & INIT' & LEN & RES').
  destruct POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & (vm' & HMD') & HFRAME & HBLKS & HSCR).
  destruct BLK as (b1 & b2 & BL1 & BL2).
  destruct HFR as (HGV & SP & GP & TP & SAV & STK & MIm & REL & HMR & HWF & HBD & INIT & HMD & F1 & F2 & F3
    & ERRW & SINK & RES & WIN).
  pose proof HGV as (Gn & Gp & Gblk & GS16 & GSK & GS47 & GROOM & GRSP & GRTP & _).
  unfold SLOT_K, SLOT_STACK in *.
  assert (HBIN : forall q k, In (q, k) hb -> In (q, k) (blocks L A)).
  { intros q k H. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact H. }
  assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho;
      [pose proof (t_owned_low L A mem md a HMR Ho) | pose proof (t_owned_low L' A' mem' md' a HMR' Ho)]; lia. }
  assert (UPEQ : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 384 - K <= a < g_S g - 384) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hs He. destruct (NOWN a (proj1 Ha)) as [N1 N2].
    apply HFRAME; [left; exact Ha | exact N1 | exact N2 | | intros F; exact F].
    unfold scratch_k. rewrite SPZ. intros [X|X]; [lia | exact (He X)]. }
  assert (IMGEQ : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Hi Hs Hc He. pose proof (t_img_lt a Hi).
    apply HFRAME; [right; exact Hi | exact (t_img_not_owned L A mem md a HMR Hi Hs Hc)
      | exact (t_img_not_owned L' A' mem' md' a HMR' Hi Hs Hc) | | intros F; exact F].
    unfold scratch_k. rewrite SPZ. intros [X|X]; [lia | exact (He X)]. }
  assert (WM' : forall a, g_S g - 65536 <= a < g_S g -> writable_at (ms_segs B) mem' a).
  { intros a Ha. rewrite ERR in UPEQ.
    destruct (Z_lt_le_dec a (g_S g - 384)) as [Hl|Hl]; [destruct (Z_lt_le_dec a (g_S g - 384 - K)) as [Hl'|Hl']|].
    - apply (proj1 (proj2 (UPEQ a ltac:(lia) ltac:(lia) ltac:(lia)))). apply WIN. lia.
    - apply HSCR. unfold scratch_k. rewrite SPZ. left. lia.
    - apply (proj1 (proj2 (UPEQ a ltac:(lia) ltac:(lia) ltac:(lia)))). apply WIN. lia. }
  exists L', A', R2, mem', md', res. split; [reflexivity|].
  split.
  { split; [exact HGV|].
    split; [etransitivity; [exact (HPRES 2 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E2|]; exact SP|].
    split; [etransitivity; [exact (HPRES 3 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E3|]; exact GP|].
    split; [etransitivity; [exact (HPRES 4 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E4|]; exact TP|].
    split.
    { apply (t_bytes_at_eq _ mem); [exact SAV|]. intros i Hi.
      assert (Hl : Z.of_nat (length (saved_bytes ra g)) = 104)
        by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
      rewrite <- SEG. rewrite ERR in UPEQ. apply (UPEQ (g_S g - 104 + i)); lia. }
    split.
    { destruct STK as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha.
      unfold SLOT_K, SLOT_STACK in Ha.
      assert (Wa : writable_at rsegs mem' a) by (rewrite <- SEG; apply WM'; lia).
      split; [exact Wa|]. destruct (t_wr_present mem' a ltac:(lia) Wa) as [bb Hb].
      exists bb. unfold Mem.mrd, Mem.wa. rewrite Hb. reflexivity. }
    split; [exact RO'|].
    split.
    { intros a Ha. destruct (ff_relro a Ha) as (Hi & Hs & Hc & He). rewrite <- (REL a Ha).
      exact (proj1 (IMGEQ a Hi Hs Hc He)). }
    split; [exact HMR'|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact INIT'|].
    split.
    { destruct HMD as (vm & ->). exists vm'. rewrite HMD'. apply YI06.with_vmmaps_twice. }
    split.
    { intros a Ha Hs He. unfold SLOT_K, SLOT_STACK in Hs. destruct (F1 a Ha Hs He) as [X1 X2].
      destruct (UPEQ a Ha ltac:(lia) He) as [X3 X4]. split; [congruence | tauto]. }
    split.
    { intros a Hi Hs Hc He. destruct (F2 a Hi Hs Hc He) as [X1 X2].
      destruct (IMGEQ a Hi Hs Hc He) as [X3 X4]. split; [congruence | tauto]. }
    split.
    { intros a k i Hin Hi. rewrite <- (F3 a k i Hin Hi).
      assert (Hb : In (a, k) (blocks L A))
        by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
      exact (KEPT a k i Hb (fun F => F) Hi). }
    split; [intros a Ha; apply HSCR; right; exact Ha|].
    split.
    { apply (t_sink mem mem' md md' SINK); [rewrite HMD'; reflexivity|].
      intros a Hi Hs Hc He. exact (proj1 (IMGEQ a Hi Hs Hc He)). }
    split; [exact (resb_malloc (g_b g) (km + 1) hb (hb ++ [(res, n)]) A' res n
                     (Permutation_sym (Permutation_cons_append hb (res, n))) RES')|].
    intros a Ha. unfold SLOT_K, SLOT_STACK in Ha. apply WM'. lia. }
  split.
  { rewrite BL1. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
    rewrite <- BL2. eapply Permutation_trans; [apply perm_skip; exact HP|].
    rewrite <- app_assoc. cbn [app]. apply Permutation_middle. }
  split; [exact HPRES|]. split; [exact R10|]. split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|].
  split.
  { intros a Ha. unfold fsp, SLOT_FRAME in Ha. rewrite ERR in UPEQ. exact (proj1 (UPEQ a ltac:(lia) ltac:(lia) ltac:(lia))). }
  intros q k i Hq Hi. exact (KEPT q k i (HBIN q k Hq) (fun F => F) Hi).
Qed.

Lemma t_payload : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  forall j, 0 <= j < g_n g ->
  ov_read_bytes rsegs mem (Mem.wa (g_p g + j)) 1 = Some [RcIdentModel.nthb (g_in g) (Z.to_nat j)].
Proof using All.
  intros g km hb L A regs mem md HFR HP j Hj.
  destruct HFR as (HGV & SP & GP & TP & SAV & STK & MIm & REL & HMR & HWF & HBD & INIT & HMD & F1 & F2 & F3
    & ERRW & SINK & RES & WIN).
  destruct HGV as (Gn & Gp & Gblk & _).
  destruct Gp as [[Hn0 _] | [Hn Hin]]; [lia|].
  assert (Hb : In (g_p g, g_n g) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
  destruct (t_block L A mem md _ _ j HMR Hb Hj) as (_ & B2 & B3 & _).
  pose proof alloc_ceiling_lt.
  assert (E : mbyte rsegs mem (g_p g + j) = Some (RcIdentModel.nthb (g_in g) (Z.to_nat j))).
  { rewrite <- ff_segs. rewrite (F3 _ _ j Hin Hj). unfold g_n, nlen in Hj.
    rewrite (Gblk j ltac:(lia)). unfold RcIdentModel.nthb. apply nth_error_nth'. lia. }
  replace (g_p g + j) with (g_p g + j + 0) by ring.
  rewrite (bytes_at_read rsegs mem (g_p g + j) [RcIdentModel.nthb (g_in g) (Z.to_nat j)] 0 1);
    [reflexivity | | lia | cbn; lia].
  split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
  change (mbyte rsegs mem (g_p g + j + Z.of_nat 0) = Some (RcIdentModel.nthb (g_in g) (Z.to_nat j))).
  replace (g_p g + j + Z.of_nat 0) with (g_p g + j) by lia. exact E.
Qed.

Lemma t_stack_keep : forall g mem mem' a bs,
  (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
  bytes_at rsegs mem a bs -> fsp g <= a -> a + Z.of_nat (length bs) <= g_S g -> bytes_at rsegs mem' a bs.
Proof using All.
  intros g mem mem' a bs H Hb H1 H2. apply (t_bytes_at_eq _ mem); [exact Hb|].
  intros i Hi. rewrite <- ff_segs. apply H. lia.
Qed.

Lemma t_block_range : forall L A mem md q k, aa_MR (APIf rc) L A mem md -> In (q, k) (blocks L A) ->
  4096 <= q /\ q + k <= alloc_ceiling.
Proof using All.
  intros L A mem md q k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn in E. injection E as <- <-. exact (mr_blocks_range B _ ff_laws L A mem md p k' HM Hp).
Qed.

Lemma t_ro_out : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> Mem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof using All.
  intros a Ha NI. destruct (Mem.ro_addr rsegs (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply NI. pose proof (t_ro_img _ E) as H. rewrite t_unsigned in H by lia. exact H.
Qed.

Lemma t_payload_mbyte : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  forall j, 0 <= j < g_n g -> mbyte rsegs mem (g_p g + j) = Some (RcIdentModel.nthb (g_in g) (Z.to_nat j)).
Proof using All.
  intros g km hb L A regs mem md HFR HP j Hj.
  destruct HFR as (HGV & SP & GP & TP & SAV & STK & MIm & REL & HMR & HWF & HBD & INIT & HMD & F1 & F2 & F3
    & ERRW & SINK & RES & WIN).
  destruct HGV as (Gn & Gp & Gblk & _).
  destruct Gp as [[Hn0 _] | [Hn Hin]]; [lia|].
  rewrite <- ff_segs. rewrite (F3 _ _ j Hin Hj). unfold g_n, nlen in Hj.
  rewrite (Gblk j ltac:(lia)). unfold RcIdentModel.nthb. apply nth_error_nth'. lia.
Qed.

Lemma t_pbnd : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 <= g_p g /\ g_p g + g_n g < 2 ^ 47.
Proof using All.
  intros g km hb L A regs mem md HFR HP.
  pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & EMP & EMP2 & _).
  destruct HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  destruct HGV as (Gn & Gp & _).
  pose proof alloc_ceiling_lt as AC.
  destruct Gp as [[Hn0 Hp0] | [Hn1 Hin]]; [rewrite Hp0, Hn0; lia|].
  assert (Hb : In (g_p g, g_n g) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
  destruct (t_block_range L A mem md _ _ HMR Hb). lia.
Qed.

Lemma t_payload_bytes : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  forall off len, 0 <= off -> 0 <= len -> off + len <= g_n g ->
  bytes_at rsegs mem (g_p g + off) (firstn (Z.to_nat len) (skipn (Z.to_nat off) (g_in g))).
Proof using All.
  intros g km hb L A regs mem md HFR HP off len Ho Hl Hn.
  pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & EMP & EMP2 & _).
  pose proof (t_payload_mbyte g km hb L A regs mem md HFR HP) as PAY.
  destruct HFR as (HGV & SP & GP & TP & SAV & STK & MIm & REL & HMR & HWF & HBD & INIT & HMD & F1 & F2 & F3
    & ERRW & SINK & RES & WIN).
  destruct HGV as (Gn & Gp & Gblk & _).
  assert (LEN : length (firstn (Z.to_nat len) (skipn (Z.to_nat off) (g_in g))) = Z.to_nat len).
  { rewrite length_firstn, length_skipn. unfold g_n, nlen in Hn. lia. }
  pose proof alloc_ceiling_lt as AC.
  assert (BND : 0 <= g_p g /\ g_p g + g_n g <= 2 ^ 64).
  { destruct Gp as [[Hn0 Hp0] | [Hn1 Hin]]; [rewrite Hp0; lia|].
    assert (Hb : In (g_p g, g_n g) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
    destruct (t_block_range L A mem md _ _ HMR Hb). lia. }
  split; [lia|]. split; [rewrite LEN; lia|]. intros j Hj. rewrite LEN in Hj.
  change (mbyte rsegs mem (g_p g + off + Z.of_nat j) =
    nth_error (firstn (Z.to_nat len) (skipn (Z.to_nat off) (g_in g))) j).
  replace (g_p g + off + Z.of_nat j) with (g_p g + (off + Z.of_nat j)) by ring.
  rewrite (PAY (off + Z.of_nat j) ltac:(lia)).
  rewrite t_nth_firstn by lia. rewrite t_nth_skipn. unfold RcIdentModel.nthb.
  replace (Z.to_nat (off + Z.of_nat j)) with (Z.to_nat off + j)%nat by lia.
  symmetry. apply nth_error_nth'. unfold g_n, nlen in Hn. lia.
Qed.

Lemma t_REC_keep : forall g i regs regs' m m', REC g i regs m -> getr regs' 9 = getr regs 9 ->
  (forall a, fsp g + 24 <= a < fsp g + 56 \/ fsp g + 128 <= a < fsp g + 140 -> mbyte rsegs m' a = mbyte rsegs m a) ->
  REC g i regs' m'.
Proof.
  intros g i regs regs' m m' (H1 & H2 & H3 & H4 & (H5 & H6 & H7) & H8) E M.
  unfold NRb, G24, HWb, EVb, q64, u32 in *.
  split; [exact H1|]. split; [rewrite E; exact H2|].
  split; [apply (t_bytes_at_eq _ m); [exact H3|]; intros j Hj; rewrite length_le8 in Hj; apply M; unfold spk in *; lia|].
  split; [apply (t_bytes_at_eq _ m); [exact H4|]; intros j Hj; rewrite length_le8 in Hj; apply M; unfold spk in *; lia|].
  split; [split; [|split]|].
  - apply (t_bytes_at_eq _ m); [exact H5|]; intros j Hj; rewrite length_le8 in Hj; apply M; unfold spk in *; lia.
  - apply (t_bytes_at_eq _ m); [exact H6|]; intros j Hj; rewrite length_le4 in Hj; apply M; unfold spk in *; lia.
  - apply (t_bytes_at_eq _ m); [exact H7|]; intros j Hj; rewrite t_hwb_len in Hj; apply M; unfold spk in *; lia.
  - apply (t_bytes_at_eq _ m); [exact H8|]; intros j Hj; rewrite length_le8 in Hj; apply M; unfold spk in *; lia.
Qed.

Lemma t_B03_keep : forall g i pl regs regs' m m', B03 g i pl regs m ->
  (forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  (forall a, fsp g + 24 <= a < fsp g + 56 \/ fsp g + 128 <= a < fsp g + 140 \/ pl <= a < pl + rec_k (g_in g) i ->
     mbyte rsegs m' a = mbyte rsegs m a) ->
  B03 g i pl regs' m'.
Proof.
  intros g i pl regs regs' m m' ((HR & H22 & H20 & H26) & H21 & HPL) CS M.
  split; [split; [|split; [|split]]|split].
  - apply (t_REC_keep g i regs regs' m m' HR (CS 9 ltac:(unfold callee_saved; lia))). intros a Ha. apply M. lia.
  - etransitivity; [exact (CS 22 ltac:(unfold callee_saved; lia))|]. exact H22.
  - etransitivity; [exact (CS 20 ltac:(unfold callee_saved; lia))|]. exact H20.
  - etransitivity; [exact (CS 26 ltac:(unfold callee_saved; lia))|]. exact H26.
  - etransitivity; [exact (CS 21 ltac:(unfold callee_saved; lia))|]. exact H21.
  - unfold PLB in *. apply (t_bytes_at_eq _ m); [exact HPL|]. intros j Hj. rewrite rec_pl_length in Hj. apply M. lia.
Qed.

Lemma t_keep_at : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs m' x = mbyte rsegs m x) -> bytes_at rsegs m' a bs.
Proof. intros m m' a bs H M. apply (t_bytes_at_eq _ m); [exact H|]. intros j Hj. apply M. lia. Qed.

Lemma t_run_norm : forall regs pc mem md L A (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  aa_MR (APIf rc) L A mem md -> ro_agree rsegs mem ->
  Exec.evt rsegs (fun ms => exists R pc' m0, ms = MState.MS R fp_regs pc' fp_csr None m0 (seg_rom rsegs) /\
      forall mem', mem_rel rsegs mem' m0 -> ro_same rsegs mem mem' -> K R pc' mem')
    (MState.MS (KindBGlue.rmk regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     Rz (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof using All.
  intros regs pc mem md L A K P HM Hro HE HK.
  destruct (t_md L A mem md HM) as [Hh Hz].
  apply (kb_run_rz B regs pc mem md K P Hh Hz); [|exact HK].
  rewrite ff_segs.
  eapply Exec.evt_mono; [exact (evt_normalize rsegs _ _ _ _ _ _ _ _ wx_apart_rsegs Hro HE)|].
  intros s (s0 & (R & pc' & m0 & E & HQ) & Hrel & Hsame). subst s0.
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  exists R, pc', (ms_mem s). split.
  - destruct s. cbn in *. subst. reflexivity.
  - apply HQ; assumption.
Qed.

End Slot.
