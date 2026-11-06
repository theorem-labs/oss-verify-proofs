(** m_file (UBSan build, image 1696d6c34ffd, 0x14268): the sub-piece S_MFU_KMOD of S_MF_LINE (the cuts are in
    U/Prog/mfu_cuts.v, the shared call lemmas in U/Prog/mfu_kit.v), the "model" arm of m_key's
    dispatch chain, from the cut KMODEL 0x146c0 to the cut KIGN 0x1477c or to the tail 0x146b4:

      0x146c0-0x146d0  k = 0xa0(sp); ieq(k, kl, "model" 0x10811)              (mfu_ieq, mfu_lits)
      0x146d4          a miss (ieq k S_model = false) jumps to KIGN 0x1477c
      0x146d8-0x146e8  v = 0x90(sp); fold(v, vl, low = sp + 0x48, 24)         (U/Prog/fold_c.v; frame scratch)
      0x146ec-0x146f8  ln = |h_fold v 24|; fuzz_catalogue_row(low, ln)        (U/Prog/fuzz_catalogue_row_c.v)
      0x146fc          NULL (cat_row low = None): m_refuse(c, line + 1) 0x147c4, then 0x14660 s6 = 0x1ff,
                       0x14688 s4 = 1, the tail                               (mfu_refuse, mfu_tail)
      0x14700-0x1470c  g = 0x30(sp); the alignment trap g & 3 is dead (g = c + 256 gi, c 16-aligned); s6 = 0x1ff
      0x14710-0x14720  memcpy(g + 0x24, low, ln + 1)                          (U/Prog/memcpy_c.v)
      0x14724-0x1472c  s4 = 1; g->model_set = 1 (`sw` 0x14728); the tail       (mfu_tail)

    After the two block writes the block holds m_upd mc gi (ms_with_model low) (the field setters of
    Prog/mfp_mconf.v), which is mk_disp's model branch (Prog/mfu_facts.v; ieq k S_role = false is the cut's
    premise). The lemmas prefixed [kmd_] are this file's own; they are build-independent except for the
    memory ones, which are stated over this build's [rsegs]. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_tok_bridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import mfu_facts mfp_facts mfp_mconf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c mfu_cuts mfu_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import m_refuse_c ieq_c fold_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import fuzz_catalogue_row_c memcpy_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists, bytes and the model *)

Lemma kmd_map_firstn : forall {A B} (f : A -> B) n l, map f (firstn n l) = firstn n (map f l).
Proof.
  intros A B f. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma kmd_map_skipn : forall {A B} (f : A -> B) n l, map f (skipn n l) = skipn n (map f l).
Proof.
  intros A B f. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH.
Qed.

Lemma kmd_zs_sub : forall (b : list byte) o n, zs (firstn n (skipn o b)) = firstn n (skipn o (zs b)).
Proof. intros b o n. unfold zs. rewrite kmd_map_firstn, kmd_map_skipn. reflexivity. Qed.

Lemma kmd_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma kmd_zs_range : forall b : list byte, Forall (fun x => 0 <= x < 256) (zs b).
Proof.
  intros b. apply Forall_forall. intros x HI. unfold zs in HI.
  apply in_map_iff in HI. destruct HI as (y & Hy & _). rewrite <- Hy. apply kmd_byte_range.
Qed.

Lemma kmd_in_firstn : forall {A} (x : A) n l, In x (firstn n l) -> In x l.
Proof. intros A x n l H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Lemma kmd_in_skipn : forall {A} (x : A) n l, In x (skipn n l) -> In x l.
Proof. intros A x n l H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H. Qed.

Lemma kmd_sub_nulfree : forall (l : list Z) o n, ~ In 0 l -> ~ In 0 (firstn n (skipn o l)).
Proof. intros l o n H HI. apply H, (kmd_in_skipn _ o), (kmd_in_firstn _ n), HI. Qed.

Lemma kmd_sub_range : forall (l : list Z) o n, Forall (fun x => 0 <= x < 256) l ->
  Forall (fun x => 0 <= x < 256) (firstn n (skipn o l)).
Proof.
  intros l o n H. rewrite Forall_forall in H |- *. intros x HI.
  apply H, (kmd_in_skipn _ o), (kmd_in_firstn _ n), HI.
Qed.

Lemma kmd_zs_zb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  intros l. unfold zs, zb. rewrite map_map.
  induction l as [|x l IH]; intros H; cbn [map]; [reflexivity|].
  pose proof (Forall_inv H) as Hx. cbn beta in Hx.
  f_equal; [| apply IH; exact (Forall_inv_tail H)].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma kmd_zb_app : forall l1 l2, zb (l1 ++ l2) = zb l1 ++ zb l2.
Proof. intros l1 l2. unfold zb. apply map_app. Qed.

Lemma kmd_upd_nth_ext : forall {A} (f g : A -> A) i l, (forall x, f x = g x) -> upd_nth i f l = upd_nth i g l.
Proof.
  intros A f g. induction i as [|i IH]; intros [|x l] H; cbn; try reflexivity.
  - rewrite H. reflexivity.
  - f_equal. apply IH. exact H.
Qed.

Lemma kmd_upd_nth_comp : forall {A} (f g : A -> A) i l,
  upd_nth i g (upd_nth i f l) = upd_nth i (fun x => g (f x)) l.
Proof.
  intros A f g. induction i as [|i IH]; intros [|x l]; cbn; try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma kmd_model_comp : forall low g, ms_set_model_set true (ms_set_model low g) = ms_with_model low g.
Proof. intros low g. unfold ms_set_model_set, ms_set_model, ms_with_model. reflexivity. Qed.

Lemma kmd_m_upd_model : forall mc i low,
  m_upd (m_upd mc i (ms_set_model low)) i (ms_set_model_set true) = m_upd mc i (ms_with_model low).
Proof.
  intros mc i low. unfold m_upd, m_set_segs.
  cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
  rewrite kmd_upd_nth_comp. f_equal.
  all: try (apply kmd_upd_nth_ext; intros x; apply kmd_model_comp).
Qed.

Lemma kmd_land3 : forall t, t mod 16 = 0 -> Z.land t 3 = 0.
Proof.
  intros t H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
  Z.div_mod_to_equations. lia.
Qed.

(** One interval of a footprint inside another: the shape every [sub_fp] goal of the walk reduces to. *)
Lemma kmd_out_sub : forall a b a' b' x, ~ (a' <= x < b') -> a' <= a -> b <= b' -> ~ (a <= x < b).
Proof. intros a b a' b' x H H1 H2 HX. apply H. lia. Qed.

Lemma kmd_row_go_lt : forall toks t i j, row_go toks t i = Some j -> (i <= j < i + length toks)%nat.
Proof.
  induction toks as [|w r IH]; intros t i j E; cbn [row_go length] in E |- *; [discriminate E|].
  destruct ((length w =? length t)%nat && leqb w t).
  - injection E as E. lia.
  - apply IH in E. lia.
Qed.

Lemma kmd_cat_row_lt : forall t i, cat_row t = Some i -> (i < 11)%nat.
Proof.
  intros t i E. unfold cat_row in E. apply kmd_row_go_lt in E.
  assert (L : length cat_toks = 11%nat) by reflexivity. lia.
Qed.

(** ** Memory *)

Lemma kmd_cell_rd : forall m a v, cell8 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold cell8 in H.
  replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a _ 0 8 H) by (rewrite length_le8; lia).
  all: cbn [skipn]; try reflexivity.
Qed.

Lemma kmd_cell_mv : forall (W : list ivl) m m' a v,
  cell8 m a v -> munch W m m' -> disjoint_from W a 8 -> cell8 m' a v.
Proof.
  intros W m m' a v H MU HD. unfold cell8 in *.
  eapply bytes_at_transport; [exact H | exact MU |]. rewrite length_le8. exact HD.
Qed.

Lemma kmd_bat_sub : forall m a (l : list byte) k n, bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. destruct H as [H _].
  exact H.
Qed.

Lemma kmd_wr_sub : forall m a n b k, wr_at rsegs m a n -> a <= b -> 0 <= k -> b + k <= a + n ->
  wr_at rsegs m b k.
Proof.
  intros m a n b k H Hb Hk Hn. destruct H as (H0 & H1 & H).
  split; [lia|]. split; [lia|].
  intros i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply H. lia.
Qed.

Lemma kmd_stk_wr : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi ->
  wr_at rsegs m a n.
Proof.
  intros m lo hi a n H Ha Hn Hh. destruct H as (H0 & H1 & H).
  split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma kmd_mrd_out : forall (W : list ivl) m m' a, munch W m m' -> outside W (bv_unsigned a) ->
  mrd rsegs m' a = mrd rsegs m a.
Proof. intros W m m' a MU HO. unfold mrd. rewrite (MU a HO). reflexivity. Qed.

(** A write that fills [a, a + n) with bytes keeps the stack region present. *)
Lemma kmd_stk_fill : forall m m' lo hi a n bs,
  stk rsegs m lo hi -> munch [(a, a + n)] m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' a bs -> Z.of_nat (length bs) = n ->
  (forall x, lo <= x < hi -> seg_rom rsegs (wa x) = None) ->
  stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a n bs HS MU WM HB HLn HR.
  eapply (stk_transport rsegs [(a, a + n)] m m' lo hi HS MU WM).
  intros x Hx.
  destruct (Z.leb_spec0 a x) as [H1|H1]; [|left; cbn [outside]; split; [lia|exact I]].
  destruct (Z.ltb_spec0 x (a + n)) as [H2|H2]; [|left; cbn [outside]; split; [lia|exact I]].
  right. destruct HB as (HA & HL & HF).
  assert (HI : (Z.to_nat (x - a) < length bs)%nat) by lia.
  specialize (HF _ HI).
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in HF by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:EB; [|apply nth_error_None in EB; lia].
  exists b. unfold mrd in HF. destruct (m' (wa x)) as [b'|] eqn:EM; [congruence|].
  rewrite (HR x Hx) in HF. discriminate HF.
Qed.

(** task_mem survives a write inside a stack region that has no image byte. *)
Lemma kmd_task_below : forall (W : list ivl) m m' lo hi,
  MemNorm.task_mem rsegs m -> stk rsegs m lo hi ->
  (forall x, lo <= x < hi -> seg_rom rsegs (wa x) = None) ->
  munch W m m' -> (forall x : Z, outside W x \/ lo <= x < hi) ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' lo hi HT HS HR MU HW a b E.
  destruct (HW (bv_unsigned a)) as [HO | HI].
  - rewrite (MU a HO) in E. exact (HT a b E).
  - pose proof (HR (bv_unsigned a) HI) as HN. unfold wa in HN. rewrite Z_to_bv_lit_self in HN.
    destruct HS as (_ & _ & HS). destruct (HS (bv_unsigned a) HI) as (_ & b' & HB).
    unfold wa in HB. rewrite Z_to_bv_lit_self in HB. unfold mrd in HB.
    destruct (m a) as [b''|] eqn:EM.
    + exact (HT a b'' EM).
    + rewrite HN in HB. discriminate HB.
Qed.

(** The cut's post is stated over the cut's memory; a post over a later memory of the same footprint gives it. *)
Lemma kmd_post_base : forall (ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word)
    (F : bvmap 5 word) (m m1 : word -> option byte) (W : list ivl) (lo : Z)
    (Q : (word -> option byte) -> Prop) (ms : machine_state),
  munch W m m1 -> wmono rsegs m m1 ->
  ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m1 W lo Q ms ->
  ret_void_fp ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m W lo Q ms.
Proof.
  intros ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m m1 W lo Q ms MU WM HP.
  destruct HP as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m' &
    E & FRM & FEQ & MU' & WM' & MI & TM & ST & HQ).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, F', fc', m'.
  split; [exact E|]. split; [exact FRM|]. split; [exact FEQ|].
  split; [eapply munch_trans; [exact MU | exact MU']|].
  split; [eapply wmono_trans; [exact WM | exact WM']|].
  split; [exact MI|]. split; [exact TM|]. split; [exact ST|]. exact HQ.
Qed.

(** The loop facts of the cut's memory move to a memory that differs from it only inside [lo, sp): every callee
    of this piece before the block writes keeps the frame and the block. *)
Lemma kmd_loop_below :
  forall m m' fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11,
  m_file_loop m fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  munch [(lo, sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo sp0 ->
  m_file_loop m' fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m m' fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 HL MU WM MI ST.
  pose proof HL as HLc.
  destruct HLc as (ESP & SAV & CL8 & CL10 & CL18 & CL20 & CL28 & CL30 & HC0 & HC16 & HNI & HMC & HWR & HSL &
    HAPC & HCUR & HK0 & HLN0 & HLN1 & HR32 & HO32 & HP0 & HPNI & HCS & HAPP & HAPPC & HPE & HCAT & HWD & HSTK & HMI).
  pose proof HSTK as HSTKc. destruct HSTKc as (STK0 & SDEP & SMOD & SROM).
  pose proof HPE as HPEc. destruct HPEc as (FRM & TM & SSP & IMGE & SP63).
  assert (N2 : sp + 272 = sp0) by (unfold M_FILE_FRAME in ESP; lia).
  assert (N1 : lo + 6224 <= sp0) by (unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in SDEP; lia).
  assert (N3 : c + 9240 <= lo \/ sp0 <= c) by (unfold apart, SEG_M_SIZE in HAPC; lia).
  assert (N4 : p + Z.of_nat (length rest) + 8 <= lo \/ sp0 <= p) by (unfold apart in HAPP; lia).
  assert (NIMG : 0x54088 <= lo) by (unfold SA, SEG_UBSAN in IMGE; cbn [sa_img_end] in IMGE; lia).
  assert (DJA : forall a n, sp <= a -> disjoint_from [(lo, sp)] a n).
  { intros a n Ha. cbn [disjoint_from]. split; [lia|exact I]. }
  assert (DJC : forall n, 0 <= n -> n <= 9236 -> disjoint_from [(lo, sp)] c n).
  { intros n H1 H2. cbn [disjoint_from]. split; [lia|exact I]. }
  assert (DJLOW : forall a n, 0 <= a -> a + n <= 0x54088 -> disjoint_from [(lo, sp)] a n).
  { intros a n H1 H2. cbn [disjoint_from]. split; [lia|exact I]. }
  unfold m_file_loop.
  split; [exact ESP|].
  split.
  { unfold saved_at in SAV |- *. eapply bytes_at_transport; [exact SAV | exact MU |].
    apply DJA. unfold M_FILE_SAVE. lia. }
  split.
  { eapply kmd_cell_mv; [exact CL8 | exact MU | apply DJA; lia]. }
  split.
  { eapply kmd_cell_mv; [exact CL10 | exact MU | apply DJA; lia]. }
  split.
  { eapply kmd_cell_mv; [exact CL18 | exact MU | apply DJA; lia]. }
  split.
  { eapply kmd_cell_mv; [exact CL20 | exact MU | apply DJA; lia]. }
  split.
  { eapply kmd_cell_mv; [exact CL28 | exact MU | apply DJA; lia]. }
  split.
  { eapply kmd_cell_mv; [exact CL30 | exact MU | apply DJA; lia]. }
  split; [exact HC0|].
  split; [exact HC16|].
  split; [exact HNI|].
  split.
  { destruct HMC as (bsx & HBx & HEx).
    assert (HLx : Z.of_nat (length bsx) = SEG_M_SIZE) by (destruct HEx as (HH & _); exact HH).
    exists bsx. split; [|exact HEx].
    eapply bytes_at_transport; [exact HBx | exact MU |]. apply DJC; unfold SEG_M_SIZE in HLx |- *; lia. }
  split.
  { eapply wr_at_transport; [exact HWR | exact WM]. }
  split.
  { destruct HSL as (sl & HBsl & HLsl).
    assert (C8m : c mod 8 = 0) by (Z.div_mod_to_equations; lia).
    assert (E4 : (- (c + SEG_M_SIZE)) mod 8 = 4) by (unfold SEG_M_SIZE; Z.div_mod_to_equations; lia).
    rewrite E4 in HLsl.
    exists (firstn 4 sl). split.
    - eapply bytes_at_transport; [ | exact MU | ].
      + rewrite <- (firstn_skipn 4 sl) in HBsl. apply bytes_at_app in HBsl. exact (proj1 HBsl).
      + assert (Hl4 : Z.of_nat (length (firstn 4 sl)) <= 4) by (rewrite length_firstn; lia).
        cbn [disjoint_from]. split; [unfold SEG_M_SIZE; lia | exact I].
    - rewrite E4, length_firstn. lia. }
  split; [exact HAPC|].
  split; [exact HCUR|].
  split; [exact HK0|].
  split; [exact HLN0|].
  split; [exact HLN1|].
  split; [exact HR32|].
  split; [exact HO32|].
  split; [exact HP0|].
  split; [exact HPNI|].
  split.
  { destruct (cstr_cut rsegs m p rest HCS) as (bs1 & sl1 & HB1 & HZ1 & HN1 & HNB1 & HLB1 & HSL1 & HSL2).
    exists bs1, sl1. split; [|split; [exact HZ1 | split; [exact HN1 | ]]].
    - eapply bytes_at_transport; [exact HB1 | exact MU |].
      cbn [disjoint_from]. split; [|exact I]. rewrite length_app. cbn [length]. lia.
    - rewrite HLB1 in HSL1. exact HSL1. }
  split; [exact HAPP|].
  split; [exact HAPPC|].
  split.
  { split; [exact FRM|]. split.
    - eapply (kmd_task_below [(lo, sp)] m m' lo sp0); [exact TM | exact STK0 | exact SROM | exact MU |].
      intros x. cbn [outside].
      destruct (Z.leb_spec0 lo x) as [H1|H1]; [|left; split; [lia|exact I]].
      destruct (Z.ltb_spec0 x sp) as [H2|H2]; [right; lia|left; split; [lia|exact I]].
    - destruct SSP as (SSP1 & g & SSP2).
      split; [|split; [exact IMGE | exact SP63]].
      split.
      + eapply bytes_at_transport; [exact SSP1 | exact MU |]. rewrite length_le8.
        apply DJLOW; unfold SA, SEG_UBSAN; cbn [sa_got_guard]; lia.
      + exists g. eapply bytes_at_transport; [exact SSP2 | exact MU |]. rewrite length_le8.
        apply DJLOW; unfold SA, SEG_UBSAN; cbn [sa_guard]; lia. }
  split.
  { intros a Ha.
    assert (HB : 0x21468 <= a < 0x21468 + 3256).
    { unfold SA, SEG_UBSAN, CAT_BYTES in Ha. cbn [sa_catalogue] in Ha. exact Ha. }
    rewrite (kmd_mrd_out [(lo, sp)] m m' (wa a) MU); [apply HCAT; exact Ha|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
  split.
  { intros a Ha. unfold M_KEY_WORDS in Ha.
    rewrite (kmd_mrd_out [(lo, sp)] m m' (wa a) MU); [apply HWD; unfold M_KEY_WORDS; exact Ha|].
    rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
  split.
  { split; [exact ST|]. split; [exact SDEP|]. split; [exact SMOD|]. exact SROM. }
  exact MI.
Qed.

(** ** The walk: KMODEL 0x146c0 -> KIGN 0x1477c or the tail 0x146b4 *)

Lemma mfu_kmod_holds :
  ieq_contract -> fold_contract -> fuzz_catalogue_row_contract -> memcpy_contract -> m_refuse_contract ->
  S_MFU_KMOD.
Proof.
  intros HIEQ HFOLD HFCR HMEMCPY HREF n HT HKIGN.
  unfold H_MFU_KMODEL, H_MFU_KAT, MFU_PC_KMODEL.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m0 lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc gi k0 rest ok kl ov vl k v
         HRN HRNE HL HREGS ES6 ES5 HKC HVC HPCD HKV HMISS.
  clear HPCD.
  destruct HREGS as (ES0 & ES2 & ES3 & ES7 & ES8 & ES9 & ES10 & ES11).
  destruct HKV as (HOK & HOV & HKF & HVF).
  subst s0 s2 s3 s5 s6 s7 s8 s9 s10 s11.
  pose proof HL as HLc.
  destruct HLc as (ESP & SAV & CL8 & CL10 & CL18 & CL20 & CL28 & CL30 & HC0 & HC16 & HNI & HMC & HWR & HSL &
    HAPC & HCUR & HK0 & HLN0 & HLN1 & HR32 & HO32 & HP0 & HPNI & HCS & HAPP & HAPPC & HPE & HCAT & HWD & HSTK & HMI).
  pose proof HSTK as HSTKc. destruct HSTKc as (STK0 & SDEP & SMOD & SROM).
  pose proof HPE as HPEc. destruct HPEc as (FRM & TM & SSP & IMGE & SP63).
  pose proof (u64_range sp) as RSP. pose proof (u64_range sp0) as RSP0.
  assert (N2 : bv_unsigned sp + 272 = bv_unsigned sp0) by (unfold M_FILE_FRAME in ESP; lia).
  assert (N1 : lo + 6224 <= bv_unsigned sp0) by (unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in SDEP; lia).
  assert (N3 : c + 9240 <= lo \/ bv_unsigned sp0 <= c) by (unfold apart, SEG_M_SIZE in HAPC; lia).
  assert (N4 : p + Z.of_nat (length rest) + 8 <= lo \/ bv_unsigned sp0 <= p) by (unfold apart in HAPP; lia).
  assert (NIMG : 0x54088 <= lo) by (unfold SA, SEG_UBSAN in IMGE; cbn [sa_img_end] in IMGE; lia).
  assert (CBND : 0 <= c /\ c + 9236 <= 2 ^ 64).
  { destruct HMC as (bsx & HBx & HEx). pose proof (bytes_at_bound rsegs m0 c bsx HBx) as HB.
    destruct HEx as (HLen & _). unfold SEG_M_SIZE in HLen. lia. }
  assert (HGI : (gi < length (mc_seg mc))%nat) by (unfold cur_ok in HCUR; exact HCUR).
  assert (HNSEG : (length (mc_seg mc) <= 32)%nat).
  { destruct HMC as (bsx & _ & HEx). destruct (mconf_enc_bounds false mc bsx HEx) as (_ & HH & _). exact HH. }
  (* the text of the line *)
  destruct HCS as (bts & slk & HBF & HZS & HNUL & HSLK).
  assert (HBB : bytes_at rsegs m0 p bts) by (apply bytes_at_app in HBF; exact (proj1 HBF)).
  assert (HLBS : length bts = length rest) by (rewrite <- HZS; unfold zs; rewrite length_map; reflexivity).
  assert (HRL : (length (mf_line rest) <= length rest)%nat).
  { destruct (mf_line_rest rest) as [[_ E2] | [_ [_ E2]]]; lia. }
  assert (HPB : 0 < p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 64).
  { pose proof (bytes_at_bound rsegs m0 p _ HBF) as HB. rewrite length_app in HB. cbn [length] in HB. lia. }
  assert (HRANGE : Forall (fun x => 0 <= x < 256) rest) by (rewrite <- HZS; apply kmd_zs_range).
  assert (HBK : bytes_at rsegs m0 (p + Z.of_nat ok) (firstn kl (skipn ok bts)))
    by (apply kmd_bat_sub; [exact HBB | lia]).
  assert (HZK : zs (firstn kl (skipn ok bts)) = k) by (rewrite kmd_zs_sub, HZS; exact HKF).
  assert (HLK : length (firstn kl (skipn ok bts)) = kl) by (rewrite length_firstn, length_skipn; lia).
  assert (HBV : bytes_at rsegs m0 (p + Z.of_nat ov) (firstn vl (skipn ov bts)))
    by (apply kmd_bat_sub; [exact HBB | lia]).
  assert (HZV : zs (firstn vl (skipn ov bts)) = v) by (rewrite kmd_zs_sub, HZS; exact HVF).
  assert (HLV : length (firstn vl (skipn ov bts)) = vl) by (rewrite length_firstn, length_skipn; lia).
  pose proof (Forall_inv HMISS) as EROLE. cbn beta in EROLE.
  destruct (mfu_lits m0 HMI) as (_ & _ & LMOD & _).
  assert (ECUR : cur_ptr c (Some gi) = c + 256 * Z.of_nat gi) by reflexivity.
  assert (LSAV : Z.of_nat (length (concat (map le8
                   [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0]))) = 104)
    by (cbn [map concat]; rewrite !length_app, !length_le8; cbn [length]; lia).
  (* 0x146c0  ld a0, 0xa0(sp); 0x146c4-0x146cc the literal "model" and kl; 0x146d0 jal ieq *)
  pose proof (kmd_cell_rd m0 _ _ HKC) as RD0.
  do 5 step.
  eapply (mfu_ieq HIEQ) with (l := firstn kl (skipn ok bts)) (w := S_model).
  - exact HL.
  - eapply mfu_mid_init. exact HL.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. exact HBK.
  - rewrite unsigned_lit by lia. rewrite HLK. reflexivity.
  - rewrite unsigned_lit by lia. rewrite HLK. unfold apart. lia.
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. exact LMOD.
  - rewrite unsigned_lit by lia. unfold snprintf_c.RO_LO. lia.
  - rewrite unsigned_lit by lia.
    assert (LM : Z.of_nat (length S_model) = 5) by (vm_compute; reflexivity).
    unfold SA, SEG_UBSAN. cbn [sa_ro_end]. lia.
  - intros m1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MID1 MU1 WM1.
    rewrite ret_pc_even by (try lia; reflexivity).
    rewrite HZK.
    pose proof MID1 as MID1c. destruct MID1c as (MM1 & WW1 & MI1 & ST1 & MC1).
    destruct (ieq k S_model) eqn:EM; cbn [b2z].
    + (* the key is "model" *)
      step. if_false.
      (* 0x146d8  v = 0x90(sp); 0x146dc-0x146e4 low = sp + 0x48, cap 24; 0x146e8 jal fold *)
      assert (HVC1 : cell8 m1 (bv_unsigned sp + 0x90) (p + Z.of_nat ov)).
      { eapply kmd_cell_mv; [exact HVC | exact MU1 |].
        unfold IEQ_STACK. cbn [disjoint_from]. split; [lia | exact I]. }
      assert (HBV1 : bytes_at rsegs m1 (p + Z.of_nat ov) (firstn vl (skipn ov bts))).
      { eapply bytes_at_transport; [exact HBV | exact MU1 |].
        unfold IEQ_STACK. cbn [disjoint_from]. rewrite HLV. split; [lia | exact I]. }
      assert (STKSP1 : stk rsegs m1 lo (bv_unsigned sp)).
      { destruct (stk_split rsegs m1 lo (bv_unsigned sp) (bv_unsigned sp0) ST1 ltac:(lia)) as [HH _]. exact HH. }
      assert (SPM16 : bv_unsigned sp mod 16 = 0) by (Z.div_mod_to_equations; lia).
      assert (EFO : fold_out (firstn vl (skipn ov bts)) (bv_unsigned (Z_to_bv 64 24)) = h_fold v 24)
        by (unfold fold_out; rewrite HZV; reflexivity).
      assert (HLOWL : (length (h_fold v 24) <= 23)%nat) by (rewrite h_fold_length; lia).
      assert (HLOWP : ~ In 0 (h_fold v 24) /\ Forall (fun x => 0 <= x < 256) (h_fold v 24)).
      { apply h_fold_props.
        - rewrite <- HVF. apply kmd_sub_nulfree. exact HNUL.
        - rewrite <- HVF. apply kmd_sub_range. exact HRANGE. }
      assert (EZB : zb (h_fold v 24 ++ [0]) = zb (h_fold v 24) ++ [ZERO]) by (unfold zb, ZERO; apply map_app).
      assert (LNB : Z.of_nat (length (zb (h_fold v 24) ++ [ZERO])) = Z.of_nat (length (h_fold v 24)) + 1).
      { unfold zb. rewrite length_app, length_map. cbn [length]. lia. }
      pose proof (kmd_cell_rd m1 _ _ HVC1) as RD1.
      do 5 step.
      eapply evt_cut.
      { eapply HFOLD with (lo := lo) (l := firstn vl (skipn ov bts)).
        unfold fold_pre. rewrite !EFO. rewrite !unsigned_lit by lia.
        split; [lia|].
        split; [lia|].
        split; [exact HBV1|].
        split; [rewrite HLV; reflexivity|].
        split; [unfold apart; lia|].
        split; [eapply (kmd_stk_wr m1 lo (bv_unsigned sp0)); [exact ST1 | lia | lia | lia]|].
        split; [unfold apart; lia|].
        split; [unfold apart; lia|].
        split.
        - split; [exact STKSP1|]. split; [unfold FOLD_STACK; lia|].
          split; [exact SPM16 | intros a Ha; apply SROM; lia].
        - exact MI1. }
      intros ms' POST.
      destruct POST as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m2 & -> &
        MU2 & WM2 & MI2 & ST2 & HB2).
      rewrite ret_pc_even by (try lia; reflexivity).
      rewrite !EFO in MU2. rewrite !EFO in HB2. rewrite !EFO.
      rewrite unsigned_lit in MU2 by lia. rewrite unsigned_lit in HB2 by lia.
      replace (bv_unsigned sp + 72 + Z.of_nat (length (h_fold v 24)) + 1)
         with (bv_unsigned sp + 72 + (Z.of_nat (length (h_fold v 24)) + 1)) in MU2 by lia.
      assert (HBSB : bytes_at rsegs m2 (bv_unsigned sp + 0x48) (zb (h_fold v 24))).
      { pose proof HB2 as HB2c. rewrite EZB in HB2c. apply bytes_at_app in HB2c. exact (proj1 HB2c). }
      assert (MUS2 : munch [(bv_unsigned sp - 5952, bv_unsigned sp);
                            (bv_unsigned sp + 0x48, bv_unsigned sp + 0x60)] m0 m2).
      { eapply munch_trans.
        - eapply munch_weaken; [|exact MU1]. unfold sub_fp, IEQ_STACK. cbn [outside].
          intros x (X1 & X2 & _). split; [eapply kmd_out_sub; [exact X1 | lia | lia] | exact I].
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside].
          intros x (X1 & X2 & _). split; [eapply kmd_out_sub; [exact X2 | lia | lia] | exact I]. }
      assert (MID2 : mfu_mid m0 m2 (bv_unsigned sp0) lo c k0 mc false).
      { split; [|split; [|split; [|split]]].
        - eapply munch_weaken; [|exact MUS2].
          unfold sub_fp, mfu_W, M_FILE_W, M_FILE_STACK, M_FILE_FRAME, PRINTF_K. cbn [app outside].
          intros x (X1 & _).
          split; [eapply kmd_out_sub; [exact X1 | lia | lia]|].
          split; [eapply kmd_out_sub; [exact X1 | lia | lia] | exact I].
        - eapply wmono_trans; [exact WW1 | exact WM2].
        - exact MI2.
        - eapply (kmd_stk_fill m1 m2 lo (bv_unsigned sp0) (bv_unsigned sp + 0x48)
                    (Z.of_nat (length (h_fold v 24)) + 1) (zb (h_fold v 24 ++ [0])));
            [exact ST1 | exact MU2 | exact WM2 | exact HB2 | | intros x Hx; apply SROM; lia].
          rewrite EZB. exact LNB.
        - eapply mconf_atp_transport; [exact MC1 | exact MU2 |].
          cbn [disjoint_from]. split; [unfold SEG_M_SIZE; lia | exact I]. }
      (* 0x146ec-0x146f8  ln = a0; fuzz_catalogue_row(low, ln) *)
      do 4 step.
      assert (HCAT2 : forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES ->
                 mrd rsegs m2 (wa a) = seg_rom rsegs (wa a)).
      { intros a Ha. unfold FUZZ_CATALOGUE, CAT_BYTES in Ha.
        rewrite (kmd_mrd_out _ m0 m2 (wa a) MUS2);
          [apply HCAT; unfold SA, SEG_UBSAN; cbn [sa_catalogue]; unfold CAT_BYTES; lia|].
        rewrite wa_unsigned by lia. cbn [outside]. split; [lia | split; [lia | exact I]]. }
      eapply evt_cut.
      { eapply HFCR with (sb := zb (h_fold v 24)) (lo := lo).
        - rewrite unsigned_lit by lia. exact HBSB.
        - rewrite unsigned_lit by lia. unfold zb. rewrite length_map. reflexivity.
        - exact ST2.
        - unfold FCR_STACK. lia.
        - intros a Ha. apply SROM. lia.
        - rewrite unsigned_lit by lia. right. lia.
        - exact HCAT2.
        - exact MI2. }
      intros ms' POST.
      destruct POST as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m3 & -> &
        MU3 & WM3 & MI3 & ST3).
      rewrite ret_pc_even by (try lia; reflexivity).
      assert (MUS3 : munch [(bv_unsigned sp - 5952, bv_unsigned sp);
                            (bv_unsigned sp + 0x48, bv_unsigned sp + 0x60)] m0 m3).
      { eapply munch_trans; [exact MUS2|].
        eapply munch_weaken; [|exact MU3]. unfold sub_fp, FCR_STACK. cbn [outside].
        intros x (X1 & X2 & _). split; [eapply kmd_out_sub; [exact X1 | lia | lia] | exact I]. }
      assert (MID3 : mfu_mid m0 m3 (bv_unsigned sp0) lo c k0 mc false).
      { eapply mfu_stack_call with (d := 48).
        - exact HL.
        - exact MID2.
        - unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K. lia.
        - unfold FCR_STACK in MU3. exact MU3.
        - exact WM3.
        - exact MI3.
        - destruct (stk_split rsegs m3 lo (bv_unsigned sp - 48) (bv_unsigned sp) ST3 ltac:(lia)) as [_ HH].
          exact HH. }
      pose proof MID3 as MID3c. destruct MID3c as (MM3 & WW3 & MI3' & ST3' & MC3).
      assert (ERP : row_ptr FUZZ_CATALOGUE (zb (h_fold v 24)) = cat_ptr FUZZ_CATALOGUE (cat_row (h_fold v 24))).
      { rewrite (row_ptr_by_token FUZZ_CATALOGUE (zb (h_fold v 24))).
        - unfold by_token. rewrite (kmd_zs_zb _ (proj2 HLOWP)), (cut_nul_id _ (proj1 HLOWP)). reflexivity.
        - rewrite (kmd_zs_zb _ (proj2 HLOWP)). exact (proj1 HLOWP). }
      rewrite ERP.
      destruct (cat_row (h_fold v 24)) as [ri|] eqn:ECR; cbn [cat_ptr].
      * (* the catalogue has the row: memcpy(g + 0x24, low, ln + 1), g->model_set = 1, the tail *)
        pose proof (kmd_cat_row_lt _ _ ECR) as HRI.
        unfold FUZZ_CATALOGUE, CAT_ROW.
        step. if_cases K; cbv iota.
        { exfalso. zify_cond K. lia. }
        assert (CL30N : cell8 m3 (bv_unsigned sp + 0x30) (c + 256 * Z.of_nat gi)).
        { eapply kmd_cell_mv; [ | exact MUS3 | ].
          - rewrite <- ECUR. exact CL30.
          - cbn [disjoint_from]. split; [lia | split; [lia | exact I]]. }
        pose proof (kmd_cell_rd m3 _ _ CL30N) as RD2.
        step. step.
        rewrite (unsigned_lit (c + 256 * Z.of_nat gi)) by lia.
        rewrite (kmd_land3 (c + 256 * Z.of_nat gi)) by (Z.div_mod_to_equations; lia).
        step. step. if_false.
        do 5 step.
        assert (HBSRC : bytes_at rsegs m3 (bv_unsigned sp + 0x48) (zb (h_fold v 24 ++ [0]))).
        { eapply bytes_at_transport; [exact HB2 | exact MU3 |].
          unfold FCR_STACK. cbn [disjoint_from]. rewrite EZB, LNB. split; [lia | exact I]. }
        assert (HWR3 : wr_at rsegs m3 c SEG_M_SIZE) by (eapply wr_at_transport; [exact HWR | exact WW3]).
        destruct (mconf_atp_bytes rsegs false m3 c mc MC3) as (blk & HBLK & HENC & HBLKL).
        assert (HBLZ : Z.of_nat (length blk) = 9236) by (rewrite HBLKL; vm_compute; reflexivity).
        assert (HJUNK : rw_cells rsegs m3 (c + 256 * Z.of_nat gi + 36)
                  [CB (S (length (h_fold v 24)))
                      (firstn (S (length (h_fold v 24))) (skipn (256 * gi + 36) blk))]).
        { split.
          - split.
            + cbn [cells_wf cell_wf]. split; [|exact I]. rewrite length_firstn, length_skipn.
              clear - HBLZ HGI HNSEG HLOWL. lia.
            + cbn [cells_bytes cbytes]. rewrite app_nil_r.
              replace (c + 256 * Z.of_nat gi + 36) with (c + Z.of_nat (256 * gi + 36)) by lia.
              apply kmd_bat_sub; [exact HBLK | lia].
          - cbn [cells_size csize]. rewrite Nat.add_0_r.
            eapply kmd_wr_sub; [exact HWR3 | lia | lia | unfold SEG_M_SIZE; lia]. }
        eapply evt_cut.
        { eapply HMEMCPY with (src := zb (h_fold v 24 ++ [0]))
            (junk := firstn (S (length (h_fold v 24))) (skipn (256 * gi + 36) blk)).
          - rewrite unsigned_lit by lia. exact HBSRC.
          - rewrite !unsigned_lit by lia. rewrite EZB.
            unfold zb. rewrite length_app, length_map. cbn [length]. lia.
          - rewrite !unsigned_lit by lia.
            replace (Z.to_nat (Z.of_nat (length (h_fold v 24)) + 1)) with (S (length (h_fold v 24))) by lia.
            exact HJUNK.
          - rewrite !unsigned_lit by lia. destruct N3 as [NA|NA]; [right|left]; lia.
          - exact MI3. }
        intros ms' POST.
        destruct POST as (w0' & w1' & w2' & w3' & w4' & w5' & w6' & w7' & w8' & w9' & w10' & w11' & w12' & w13' &
          m4 & -> & MU4 & WM4 & MI4 & HDST & HSRC).
        rewrite ret_pc_even by (try lia; reflexivity).
        rewrite !unsigned_lit in MU4 by lia.
        rewrite !unsigned_lit in HDST by lia.
        replace (Z.to_nat (Z.of_nat (length (h_fold v 24)) + 1)) with (S (length (h_fold v 24))) in HDST by lia.
        assert (HBDST : bytes_at rsegs m4 (c + 256 * Z.of_nat gi + 36) (zb (h_fold v 24) ++ [ZERO])).
        { destruct HDST as [[_ HH] _]. cbn [cells_bytes cbytes] in HH. rewrite app_nil_r in HH.
          rewrite EZB in HH. exact HH. }
        assert (MC4 : mconf_atp rsegs false m4 c (m_upd mc gi (ms_set_model (h_fold v 24)))).
        { eapply (mconf_atp_upd rsegs false false m3 m4 c mc _ (c + 256 * Z.of_nat gi + 36)
                    (zb (h_fold v 24) ++ [ZERO])).
          - exact MC3.
          - exact MU4.
          - intros x Hx Hout. rewrite LNB. cbn [outside] in Hout.
            destruct (Z.leb_spec0 (c + 256 * Z.of_nat gi + 36) x) as [H1|H1].
            + destruct (Z.ltb_spec0 x (c + 256 * Z.of_nat gi + 36 +
                          (Z.of_nat (length (h_fold v 24)) + 1))) as [H2|H2].
              * lia.
              * exfalso. apply Hout. split; [lia | exact I].
            + exfalso. apply Hout. split; [lia | exact I].
          - exact HBDST.
          - lia.
          - rewrite LNB. unfold SEG_M_SIZE. lia.
          - intros bs HE.
            replace (Z.to_nat (c + 256 * Z.of_nat gi + 36 - c)) with (256 * gi + Z.to_nat MS_MODEL)%nat
              by (unfold MS_MODEL; lia).
            apply (mconf_enc_seg false mc bs gi (ms_set_model (h_fold v 24)) (Z.to_nat MS_MODEL)
                     (zb (h_fold v 24) ++ [ZERO]) HE HGI).
            + unfold MS_MODEL. unfold zb. rewrite length_app, length_map. cbn [length]. lia.
            + intros fb Hfb. apply mseg_enc_model;
                [exact Hfb | lia | exact (proj1 HLOWP) | exact (proj2 HLOWP)]. }
        step.
        assert (HWR4 : wr_at rsegs m4 c SEG_M_SIZE) by (eapply wr_at_transport; [exact HWR3 | exact WM4]).
        pose proof (wr_at_store_ok rsegs m4 c SEG_M_SIZE (256 * Z.of_nat gi + 32) 4 HWR4
                      ltac:(lia) ltac:(unfold SEG_M_SIZE; lia)) as HS4.
        step.
        match goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?A _) _) =>
            replace A with (wa (c + 256 * Z.of_nat gi + 32)) by (unfold wa; f_equal; lia)
        end.
        assert (ESEGL : length (mc_seg (m_upd mc gi (ms_with_model (h_fold v 24)))) = length (mc_seg mc)).
        { unfold m_upd, m_set_segs. cbn [mc_seg]. apply upd_nth_length. }
        assert (MC5 : mconf_atp rsegs false
                        (write_to_mem m4 (wa (c + 256 * Z.of_nat gi + 32)) (le4 (Z_to_bv 64 1)))
                        c (m_upd mc gi (ms_with_model (h_fold v 24)))).
        { rewrite <- kmd_m_upd_model.
          eapply (mconf_atp_store rsegs false false m4 c (m_upd mc gi (ms_set_model (h_fold v 24)))
                    _ (c + 256 * Z.of_nat gi + 32) (le4 (Z_to_bv 64 1))).
          - exact MC4.
          - lia.
          - rewrite length_le4. unfold SEG_M_SIZE. lia.
          - intros bs HE.
            replace (Z.to_nat (c + 256 * Z.of_nat gi + 32 - c)) with (256 * gi + Z.to_nat MS_MODEL_SET)%nat
              by (unfold MS_MODEL_SET; lia).
            apply (mconf_enc_seg false (m_upd mc gi (ms_set_model (h_fold v 24))) bs gi
                     (ms_set_model_set true) (Z.to_nat MS_MODEL_SET) (le4 (Z_to_bv 64 1)) HE).
            + unfold m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length. exact HGI.
            + unfold MS_MODEL_SET. rewrite length_le4. lia.
            + intros fb Hfb. exact (mseg_enc_model_set _ fb true Hfb). }
        assert (MUB4 : munch [(bv_unsigned sp - 5952, bv_unsigned sp);
                              (bv_unsigned sp + 0x48, bv_unsigned sp + 0x60);
                              (c + 256 * Z.of_nat gi, c + 256 * Z.of_nat gi + 256)] m0 m4).
        { eapply munch_trans.
          - eapply munch_weaken; [|exact MUS3]. unfold sub_fp. cbn [outside].
            intros x (X1 & X2 & X3 & _). split; [exact X1 | split; [exact X2 | exact I]].
          - eapply munch_weaken; [|exact MU4]. unfold sub_fp. cbn [outside].
            intros x (X1 & X2 & X3 & _).
            split; [eapply kmd_out_sub; [exact X3 | lia | lia] | exact I]. }
        assert (MUB5 : munch [(bv_unsigned sp - 5952, bv_unsigned sp);
                              (bv_unsigned sp + 0x48, bv_unsigned sp + 0x60);
                              (c + 256 * Z.of_nat gi, c + 256 * Z.of_nat gi + 256)] m0
                          (write_to_mem m4 (wa (c + 256 * Z.of_nat gi + 32)) (le4 (Z_to_bv 64 1)))).
        { eapply munch_write; [exact MUB4 | lia | rewrite length_le4; lia |].
          rewrite length_le4. cbn [inside]. right. right. left. lia. }
        assert (STK5 : stk rsegs (write_to_mem m4 (wa (c + 256 * Z.of_nat gi + 32)) (le4 (Z_to_bv 64 1)))
                         lo (bv_unsigned sp0)).
        { apply stk_write; [ | lia | rewrite length_le4; lia].
          eapply stk_transport_disjoint; [exact ST3' | exact MU4 | exact WM4 |].
          cbn [disjoint_from]. split; [lia | exact I]. }
        assert (MI5 : mem_inv rsegs
                        (write_to_mem m4 (wa (c + 256 * Z.of_nat gi + 32)) (le4 (Z_to_bv 64 1)))).
        { apply mem_inv_store; [exact MI4|]. rewrite length_le4.
          replace (wa (c + 256 * Z.of_nat gi + 32)) with (wa (c + (256 * Z.of_nat gi + 32)))
            by (unfold wa; f_equal; lia).
          exact HS4. }
        assert (MID5 : mfu_mid m0 (write_to_mem m4 (wa (c + 256 * Z.of_nat gi + 32)) (le4 (Z_to_bv 64 1)))
                         (bv_unsigned sp0) lo c k0 (m_upd mc gi (ms_with_model (h_fold v 24))) false).
        { split; [|split; [|split; [|split]]].
          - eapply munch_weaken; [|exact MUB5].
            unfold sub_fp, mfu_W, M_FILE_W, M_FILE_STACK, M_FILE_FRAME, PRINTF_K. cbn [app outside].
            intros x (X1 & X2 & _). rewrite ESEGL in X2. unfold mseg_addr, MSEG_SIZE in X2.
            split; [eapply kmd_out_sub; [exact X1 | lia | lia]|].
            split; [eapply kmd_out_sub; [exact X1 | lia | lia]|].
            split; [eapply kmd_out_sub; [exact X2 | lia | lia] | exact I].
          - apply wmono_write. eapply wmono_trans; [exact WW3 | exact WM4].
          - exact MI5.
          - exact STK5.
          - exact MC5. }
        step.
        assert (EDISP : mk_disp mc gi k v (line + 1) = m_upd mc gi (ms_with_model (h_fold v 24))).
        { unfold mk_disp. rewrite EROLE, EM. cbv zeta. rewrite ECR. reflexivity. }
        rewrite EDISP.
        assert (DJB : forall a nn, bv_unsigned sp <= a -> a + nn <= bv_unsigned sp0 ->
                   (a + nn <= bv_unsigned sp + 0x48 \/ bv_unsigned sp + 0x60 <= a) ->
                   disjoint_from [(bv_unsigned sp - 5952, bv_unsigned sp);
                                  (bv_unsigned sp + 0x48, bv_unsigned sp + 0x60);
                                  (c + 256 * Z.of_nat gi, c + 256 * Z.of_nat gi + 256)] a nn).
        { intros a nn H1 H2 H3. cbn [disjoint_from]. split; [lia|]. split; [lia|].
          split; [|exact I]. lia. }
        eapply mfu_tail.
        -- exact HT.
        -- exact HRN.
        -- exact HRNE.
        -- exact HL.
        -- exact MID5.
        -- unfold saved_at in SAV |- *. eapply bytes_at_transport; [exact SAV | exact MUB5 |].
           rewrite LSAV. apply DJB;
             [unfold M_FILE_SAVE; lia | unfold M_FILE_SAVE; lia | right; unfold M_FILE_SAVE; lia].
        -- eapply kmd_cell_mv; [exact CL8 | exact MUB5 | apply DJB; [lia | lia | left; lia]].
        -- eapply kmd_cell_mv; [exact CL10 | exact MUB5 | apply DJB; [lia | lia | left; lia]].
        -- eapply kmd_cell_mv; [exact CL18 | exact MUB5 | apply DJB; [lia | lia | left; lia]].
        -- eapply kmd_cell_mv; [exact CL20 | exact MUB5 | apply DJB; [lia | lia | left; lia]].
        -- eapply kmd_cell_mv; [exact CL28 | exact MUB5 | apply DJB; [lia | lia | left; lia]].
        -- eapply kmd_cell_mv; [exact CL30 | exact MUB5 | apply DJB; [lia | lia | left; lia]].
        -- apply m_upd_grows.
        -- unfold cur_ok. rewrite ESEGL. exact HGI.
        -- unfold m_upd, m_set_segs. cbn [mc_refused]. lia.
        -- unfold m_upd, m_set_segs. cbn [mc_overflow]. lia.
        -- exact FRM.
        -- intros kk _. reflexivity.
        -- unfold m_file_regs. repeat split; reflexivity.
      * (* no row: m_refuse(c, line + 1) 0x147c4, then 0x14660 / 0x14688 and the tail *)
        step. if_true.
        do 3 step.
        eapply (mfu_refuse HREF).
        -- exact HL.
        -- exact HRNE.
        -- exact MID3.
        -- apply mf_grows_refl.
        -- reflexivity.
        -- exact FRM.
        -- rewrite unsigned_lit by lia. reflexivity.
        -- rewrite unsigned_lit by lia. reflexivity.
        -- intros m4 F4 fc4 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MID4 MU4 WM4 FRM4 FEQ4.
           rewrite ret_pc_even by (try lia; reflexivity).
           do 5 step.
           assert (EDISP : mk_disp mc gi k v (line + 1) = m_refuse mc (line + 1) false).
           { unfold mk_disp. rewrite EROLE, EM. cbv zeta. rewrite ECR. reflexivity. }
           rewrite EDISP.
           assert (SUBR : sub_fp (m_refuse_W (bv_unsigned sp) c mc)
                     [(bv_unsigned sp - 5952, bv_unsigned sp);
                      (bv_unsigned sp + 0x48, bv_unsigned sp + 0x60); (c, c + 9236)]).
           { unfold sub_fp, m_refuse_W, M_REFUSE_STACK, PRINTF_K, kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT,
                    MC_REFUSED.
             intros x Hx. cbn [outside] in Hx. destruct Hx as (X1 & X2 & X3 & _).
             assert (HKB : 0 <= Z.of_nat (length (mc_kept mc))) by lia.
             destruct (Z.of_nat (length (mc_kept mc)) <? 8) eqn:EK; cbn [outside app].
             - apply Z.ltb_lt in EK.
               split; [eapply kmd_out_sub; [exact X1 | lia | lia]|].
               split; [eapply kmd_out_sub; [exact X3 | lia | lia]|].
               split; [eapply kmd_out_sub; [exact X3 | lia | lia]|].
               split; [eapply kmd_out_sub; [exact X3 | lia | lia] | exact I].
             - split; [eapply kmd_out_sub; [exact X1 | lia | lia]|].
               split; [eapply kmd_out_sub; [exact X3 | lia | lia] | exact I]. }
           assert (MUB4 : munch [(bv_unsigned sp - 5952, bv_unsigned sp);
                                 (bv_unsigned sp + 0x48, bv_unsigned sp + 0x60); (c, c + 9236)] m0 m4).
           { eapply munch_trans.
             - eapply munch_weaken; [|exact MUS3]. unfold sub_fp. cbn [outside].
               intros x (X1 & X2 & X3 & _).
               split; [exact X1 | split; [exact X2 | exact I]].
             - eapply munch_weaken; [exact SUBR | exact MU4]. }
           assert (DJB : forall a nn, bv_unsigned sp <= a -> a + nn <= bv_unsigned sp0 ->
                      (a + nn <= bv_unsigned sp + 0x48 \/ bv_unsigned sp + 0x60 <= a) ->
                      disjoint_from [(bv_unsigned sp - 5952, bv_unsigned sp);
                                     (bv_unsigned sp + 0x48, bv_unsigned sp + 0x60); (c, c + 9236)] a nn).
           { intros a nn H1 H2 H3. cbn [disjoint_from]. split; [lia|]. split; [lia|].
             split; [|exact I]. lia. }
           eapply mfu_tail.
           ++ exact HT.
           ++ exact HRN.
           ++ exact HRNE.
           ++ exact HL.
           ++ exact MID4.
           ++ unfold saved_at in SAV |- *. eapply bytes_at_transport; [exact SAV | exact MUB4 |].
              rewrite LSAV. apply DJB;
                [unfold M_FILE_SAVE; lia | unfold M_FILE_SAVE; lia | right; unfold M_FILE_SAVE; lia].
           ++ eapply kmd_cell_mv; [exact CL8 | exact MUB4 | apply DJB; [lia | lia | left; lia]].
           ++ eapply kmd_cell_mv; [exact CL10 | exact MUB4 | apply DJB; [lia | lia | left; lia]].
           ++ eapply kmd_cell_mv; [exact CL18 | exact MUB4 | apply DJB; [lia | lia | left; lia]].
           ++ eapply kmd_cell_mv; [exact CL20 | exact MUB4 | apply DJB; [lia | lia | left; lia]].
           ++ eapply kmd_cell_mv; [exact CL28 | exact MUB4 | apply DJB; [lia | lia | left; lia]].
           ++ eapply kmd_cell_mv; [exact CL30 | exact MUB4 | apply DJB; [lia | lia | left; lia]].
           ++ apply m_refuse_grows.
           ++ unfold cur_ok. destruct (m_refuse_sizes mc (line + 1) false) as [EE _]. rewrite EE. exact HGI.
           ++ unfold m_refuse. cbn [mc_refused]. lia.
           ++ unfold m_refuse. cbn [mc_overflow]. lia.
           ++ exact FRM4.
           ++ exact FEQ4.
           ++ unfold m_file_regs. repeat split; reflexivity.
    + (* a miss: the cut KIGN 0x1477c *)
      step. if_true.
      eapply evt_mono.
      * unfold H_MFU_KIGN, H_MFU_KAT, MFU_PC_KIGN, MFU_PC_KDISP in HKIGN.
        eapply HKIGN.
        -- exact HRN.
        -- exact HRNE.
        -- eapply kmd_loop_below; [exact HL | | exact WW1 | exact MI1 | exact ST1].
           eapply munch_weaken; [|exact MU1]. unfold sub_fp, IEQ_STACK. cbn [outside].
           intros x (X1 & _). split; [lia | exact I].
        -- unfold mfu_lregs. repeat split; reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- eapply kmd_cell_mv; [exact HKC | exact MU1 |].
           unfold IEQ_STACK. cbn [disjoint_from]. split; [lia | exact I].
        -- eapply kmd_cell_mv; [exact HVC | exact MU1 |].
           unfold IEQ_STACK. cbn [disjoint_from]. split; [lia | exact I].
        -- intros HX. discriminate HX.
        -- unfold mfu_kv. split; [exact HOK|]. split; [exact HOV|]. split; [exact HKF | exact HVF].
        -- constructor; [exact EROLE|]. constructor; [exact EM|]. constructor.
      * intros ms HP. eapply kmd_post_base; [ | exact WM1 | exact HP].
        eapply munch_weaken; [|exact MU1].
        unfold sub_fp, M_FILE_W, M_FILE_STACK, M_FILE_FRAME, PRINTF_K, IEQ_STACK. cbn [outside].
        intros x (X1 & _). split; [lia | exact I].
Qed.
