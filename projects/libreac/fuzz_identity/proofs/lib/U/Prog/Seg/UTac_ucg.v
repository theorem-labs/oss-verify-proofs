From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotInv write_uint_c reac_identity_fw_str_c
  reac_identity_reac_ver_str_c put_dec_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(bsz, z8, zlen, fw_res, fw_out, id_VER, ver_res,
  ver_out, HWT_ADDR).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.write_uint_c(write_uint_dg, write_uint_lsd, write_uint_D,
  write_uint_n).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_fw_str_c(FW, L, reac_identity_fw_str_c3,
  reac_identity_fw_str_c3_len, reac_identity_fw_str_c3_nz, reac_identity_fw_str_dec_h, reac_identity_fw_str_dec_f).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_reac_ver_str_c(reac_ver_str_VER,
  reac_ver_str_LV, reac_ver_str_DEC2).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU check_str_c put_dec_c
  reac_identity_fw_str_c reac_identity_reac_ver_str_c reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_box_family_of_c buf_of_c buf_of.
Import ListNotations.
Open Scope Z_scope.

Lemma uf_canon_mkst : forall {fx : lib.Reusable.YK11.FPState} (regs : bvmap 5 word) (pc : word) (mem ro : word -> option byte),
  canonical_register_state (lib.Reusable.YK11.mkst regs pc mem ro) = MS (mkR_of regs) fp_regs pc fp_csr None mem ro.
Proof. reflexivity. Qed.

Lemma uf_eqv_mkst : forall {fx : lib.Reusable.YK11.FPState} (R : bvmap 5 word) (pc : word) (m ro : word -> option byte) ms',
  ms_eqv (MS R fp_regs pc fp_csr None m ro) ms' -> exists R', ms' = lib.Reusable.YK11.mkst R' pc m ro /\ xregs_eqv R R'.
Proof.
  intros fx R pc m ro [R' F' pc' svc' rv' fc' m' ro'] (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  cbn in HF, Hpc, Hsvc, Hrv, Hfc, Hm, Hro. subst. exists R'. split; [reflexivity | exact HR].
Qed.

Lemma uf_getr_x : forall (R R' : bvmap 5 word) (r : bv 5),
  xregs_eqv R R' -> is_x0 r = false -> lib.Reusable.YK11.getr R' r = reg_get R r.
Proof.
  intros R R' r H H0. unfold lib.Reusable.YK11.getr.
  match goal with |- (if ?b then _ else _) = _ => replace b with false by (symmetry; exact H0) end.
  symmetry. apply H. exact H0.
Qed.

Lemma uf_getr_reg : forall (regs : bvmap 5 word) (r : bv 5), is_x0 r = false -> lib.Reusable.YK11.getr regs r = reg_get regs r.
Proof.
  intros regs r H0. unfold lib.Reusable.YK11.getr.
  match goal with |- (if ?b then _ else _) = _ => replace b with false by (symmetry; exact H0) end.
  reflexivity.
Qed.

Lemma uf_ret_pc_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz He. apply ret_pc_even; assumption. Qed.

Lemma uf_with_vm : forall a b m, with_vmmaps a (with_vmmaps b m) = with_vmmaps a m.
Proof. intros a b m. reflexivity. Qed.

Lemma uf_bytes_same : forall segs (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
  bytes_at segs m a bs -> bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i Hi. unfold mrd, wa. rewrite H by lia. apply H3. exact Hi.
Qed.

Lemma uf_bytes_mbyte : forall segs (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  bytes_at segs m a bs -> bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs H (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i Hi. specialize (H (Z.of_nat i) ltac:(lia)).
  change (mbyte segs m' (a + Z.of_nat i) = nth_error bs i). rewrite H.
  change (mrd segs m (wa (a + Z.of_nat i)) = nth_error bs i). apply H3. exact Hi.
Qed.

Lemma uf_fs_in : forall (l : list Segment) x n s, find_segment l x n = Some s ->
  In s l /\ Z.of_N (seg_base s) <= x /\ x + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction l as [|s0 l IH]; intros x n s E; cbn [find_segment] in E; [discriminate|].
  cbv zeta in E. revert E. match goal with |- (if ?k then _ else _) = _ -> _ => destruct k eqn:C end; intros E.
  - injection E as <-. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1, C2. split; [left; reflexivity | lia].
  - destruct (IH x n s E) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x51000.

Lemma uf_fs_bound : forall x s, find_segment rsegs x 1 = Some s -> IMG_LO <= x < IMG_HI.
Proof.
  intros x s E. destruct (uf_fs_in rsegs x 1 s E) as (Hin & H1 & H2).
  assert (H : forallb (fun s => (IMG_LO <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? IMG_HI))
            rsegs = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). apply andb_prop in H as [H3 H4].
  apply Z.leb_le in H3, H4. lia.
Qed.

Lemma uf_fs_none : forall x, (x < IMG_LO \/ IMG_HI <= x) -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|reflexivity].
  exfalso. pose proof (uf_fs_bound x s E). lia.
Qed.

Lemma uf_wview_none : forall (m : word -> option byte) (w : word),
  find_segment rsegs (bv_unsigned w) 1 = None -> wview rsegs m w <> None -> exists b, m w = Some b.
Proof.
  intros m w Hf Hw. unfold wview in Hw. destruct (m w) as [b|]; [exists b; reflexivity|].
  rewrite Hf in Hw. exfalso. apply Hw. reflexivity.
Qed.

Lemma uf_ro_lt : forall w : word, Mem.ro_addr rsegs w = true -> IMG_LO <= bv_unsigned w < IMG_HI.
Proof.
  intros w H. unfold Mem.ro_addr in H. destruct (find_segment rsegs (bv_unsigned w) 1) as [s|] eqn:E; [|discriminate].
  exact (uf_fs_bound _ s E).
Qed.

Section T.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma uf_segs : ms_segs B = rsegs.
Proof. exact (proj1 FF). Qed.

Lemma uf_malloc_pc : ms_malloc B = 0x15ab4.
Proof. destruct FF as (_ & _ & H & _). exact H. Qed.

Lemma uf_free_pc : ms_free B = 0x15974.
Proof. destruct FF as (_ & _ & _ & H & _). exact H. Qed.

Lemma uf_alloc : @frame_allocator rc fx B (APIf rc).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & H). exact (H rc fx).
Qed.

Lemma uf_relro_img : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & H & _). exact H.
Qed.

Lemma uf_errno : errno_addr B = 0x3040c.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Hoff & _).
  unfold errno_addr. rewrite Htp, Hoff. reflexivity.
Qed.

Lemma uf_ctx : ms_ctx B = 0x507b8.
Proof. destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma uf_ceil : forall a, errno_addr B <= a < errno_addr B + 4 -> a < alloc_ceiling.
Proof.
  destruct FF as (_ & _ & _ & _ & _ & _ & H & _). intros a Ha. specialize (H rc). lia.
Qed.

Let API := APIf rc.
Let MR := aa_MR API.

Lemma uf_laws : MR_laws B MR.
Proof. exact (aa_laws API). Qed.

Lemma uf_ax : AllocExtra B MR.
Proof.
  destruct uf_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H.
Qed.

Lemma uf_img_lt : forall a, in_img B a -> IMG_LO <= a < IMG_HI.
Proof.
  intros a [_ (s & Hin & Ha)]. rewrite uf_segs in Hin.
  assert (H : forallb (fun s => (IMG_LO <=? bv_unsigned (fst s)) && (bv_unsigned (fst s) + bv_unsigned (snd s) <=? IMG_HI))
            (segments_reserved rsegs) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1, H2. lia.
Qed.

Lemma uf_fs_img : forall x s, find_segment rsegs x 1 = Some s -> in_img B x.
Proof.
  intros x s E. destruct (uf_fs_in rsegs x 1 s E) as (Hin & H1 & H2).
  assert (H : forallb (fun s => let r := segment_reservation s in
                 (bv_unsigned (fst r) <=? Z.of_N (seg_base s)) &&
                 (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst r) + bv_unsigned (snd r))) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). cbv zeta in H. apply andb_prop in H as [H3 H4].
  apply Z.leb_le in H3, H4.
  split; [rewrite uf_segs; discriminate|].
  exists (segment_reservation s). split; [rewrite uf_segs; unfold segments_reserved; apply in_map; exact Hin | lia].
Qed.

Lemma uf_noimg_fs : forall x, ~ in_img B x -> find_segment rsegs x 1 = None.
Proof.
  intros x H. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|reflexivity].
  exfalso. exact (H (uf_fs_img x s E)).
Qed.

Lemma uf_ro_img : forall w : word, Mem.ro_addr rsegs w = true -> in_img B (bv_unsigned w).
Proof.
  intros w H. unfold Mem.ro_addr in H. destruct (find_segment rsegs (bv_unsigned w) 1) as [s|] eqn:E; [|discriminate].
  exact (uf_fs_img _ s E).
Qed.

Lemma uf_ur : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Lemma uf_img_hi : forall a, 0x20000 <= a < 0x51000 -> in_img B a.
Proof.
  intros a Ha. split; [rewrite uf_segs; discriminate|].
  exists (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)). rewrite uf_segs. split.
  - apply nth_In. vm_compute. lia.
  - assert (E1 : bv_unsigned (fst (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0))) = 0x20000)
      by (vm_compute; reflexivity).
    assert (E2 : bv_unsigned (snd (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0))) = 0x31000)
      by (vm_compute; reflexivity).
    rewrite E1, E2. lia.
Qed.

Definition sink_addr (a : Z) : Prop := a = 0x50741 \/ (0x50b68 <= a < 0x50b6c) \/ (0x50b70 <= a < 0x50b78).

Lemma uf_sink_ok : forall a, sink_addr a ->
  0 <= a < 2 ^ 64 /\ in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. pose proof uf_errno as Er. unfold sink_addr in Ha.
  pose proof FF as FF0.
  destruct FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & LIBK & DELTA & ALLOC).
  split; [lia|]. split; [apply uf_img_hi; lia|].
  split; [unfold static_owned, vml_lo, vml_len; rewrite LCK, LIBC, GOT, GUA, DBR, SCL, SMC, MDC;
          rewrite (ff_vmlock_u _ _ _ _ _ _ _ FF0), (ff_dbl_u _ _ _ _ _ _ _ FF0), Z.max_id; lia|].
  rewrite CTX, Er. unfold CTX_SIZE. lia.
Qed.

Lemma uf_sink_tr : forall (mem mem' : word -> option byte) md md',
  (forall a, sink_addr a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  m_fds md' = m_fds md -> sink_none B mem md -> sink_none B mem' md'.
Proof.
  intros mem mem' md md' H Hf ((Ht & Hl) & Hh & Hn).
  destruct FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & LIBK & DELTA & ALLOC).
  split; [split|split].
  - intros k Hk. rewrite H; [apply Ht; exact Hk|]. unfold sink_addr. rewrite THR. lia.
  - intros k Hk. rewrite H; [apply Hl; exact Hk|]. unfold sink_addr. rewrite OFL. lia.
  - intros k Hk. rewrite H; [apply Hh; exact Hk|]. unfold sink_addr. rewrite OFH. lia.
  - rewrite Hf. exact Hn.
Qed.

Lemma uf_pw_perm : forall {X : Type} (R : X -> X -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros X R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - destruct H as [H1 H2]. split; [|apply IH; exact H2].
    intros y Hy. apply H1. apply (Permutation_in _ (Permutation_sym HP)). exact Hy.
  - destruct H as [H1 [H2 H3]]. split.
    + intros z [<-|Hz]; [apply Hs; apply H1; left; reflexivity | apply H2; exact Hz].
    + split; [intros z Hz; apply H1; right; exact Hz | exact H3].
  - apply IH2. apply IH1. exact H.
Qed.

Lemma uf_pw_app : forall {X : Type} (R : X -> X -> Prop) l1 l2, pairwise R (l1 ++ l2) ->
  forall x y, In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; intros l2 H x y Hx Hy; [destruct Hx|].
  destruct H as [H1 H2]. destruct Hx as [<-|Hx].
  - apply H1. apply in_or_app. right. exact Hy.
  - exact (IH l2 H2 x y Hx Hy).
Qed.

Definition in_hb (hb : list (Z * Z)) (x : Z) : Prop := exists a k, In (a, k) hb /\ a <= x < a + k.
Definition kreg (g : ghost) (hb : list (Z * Z)) (x : Z) : Prop :=
  (g_S g - SLOT_K <= x < g_S g - 104) \/ in_hb hb x.

Lemma uf_blk_of : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hp | reflexivity].
Qed.

Lemma uf_blk_facts : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present mem (a + i) /\ 4096 <= a /\ a + k <= alloc_ceiling /\ ~ owned B L A (a + i) /\ ~ in_img B (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. destruct (uf_blk_of L A a k Hin) as (p & Hp & <-).
  destruct (mr_blocks B MR uf_laws L A mem md p k i HM Hp Hi) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  exact (ax_blocks_img uf_ax L A mem md p k i HM Hp Hi).
Qed.

Lemma uf_hb_facts : forall L A mem md hb B0 x, MR L A mem md -> Permutation (blocks L A) (hb ++ B0) -> in_hb hb x ->
  present mem x /\ 4096 <= x < alloc_ceiling /\ ~ owned B L A x /\ ~ in_img B x.
Proof.
  intros L A mem md hb B0 x HM HP (a & k & Hin & Hx).
  assert (Hb : In (a, k) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
  destruct (uf_blk_facts L A mem md a k (x - a) HM Hb ltac:(lia)) as (H1 & H2 & H3 & H4 & H5).
  replace (a + (x - a)) with x in * by lia. split; [exact H1|]. split; [lia|]. split; assumption.
Qed.

Lemma uf_b0_facts : forall L A mem md hb B0 a k i, MR L A mem md -> Permutation (blocks L A) (hb ++ B0) ->
  In (a, k) B0 -> 0 <= i < k -> 4096 <= a /\ a + i < alloc_ceiling /\ ~ in_hb hb (a + i).
Proof.
  intros L A mem md hb B0 a k i HM HP Hin Hi.
  assert (Hb : In (a, k) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
  destruct (uf_blk_facts L A mem md a k i HM Hb Hi) as (_ & H2 & H3 & _).
  split; [lia|]. split; [lia|].
  intros (a' & k' & Hin' & Hx).
  pose proof (mr_blocks_disjoint B MR uf_laws L A mem md HM) as Hpw.
  pose proof (uf_pw_perm ranges_disjoint ltac:(intros u v; unfold ranges_disjoint; lia) _ _ HP Hpw) as Hpw'.
  pose proof (uf_pw_app ranges_disjoint hb B0 Hpw' (a', k') (a, k) Hin' Hin) as Hd.
  unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma uf_FR_kA : forall g km hb L A regs mem md regs' mem',
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ kreg g hb x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  wmono rsegs mem mem' ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' HF HP E2 E3 E4 HU HW.
  pose proof uf_segs as SEG.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & HPB).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  assert (HK : SLOT_K = 65536) by reflexivity.
  assert (NK : forall x, kreg g hb x -> ~ in_img B x /\ x < g_S g - 104 /\ ~ owned B L A x /\ 0 <= x < 2 ^ 64 /\
                 (x < alloc_ceiling \/ g_S g - SLOT_K <= x)).
  { intros x [Hx|Hx].
    - split; [intros Hi; apply uf_img_lt in Hi; unfold IMG_HI in Hi; lia|].
      split; [lia|]. split; [intros Ho; pose proof (mr_owned_low B MR uf_laws L A mem md x HMR Ho); lia|]. lia.
    - destruct (uf_hb_facts L A mem md hb _ x HMR HP Hx) as (_ & H2 & H3 & H4).
      split; [exact H4|]. split; [lia|]. split; [exact H3|]. lia. }
  assert (SAME : forall x, 0 <= x < 2 ^ 64 -> ~ kreg g hb x ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
     (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx Hk. unfold mbyte, writable_at, wview. rewrite (HU x Hx Hk). tauto. }
  assert (PRES : forall x, 0 <= x < 2 ^ 64 -> ~ in_img B x -> wview rsegs mem (Z_to_bv 64 x) <> None ->
     exists b, mem' (Z_to_bv 64 x) = Some b).
  { intros x Hx Hi Hw. apply uf_wview_none; [rewrite (unsigned_lit x Hx); exact (uf_noimg_fs x Hi) | apply HW; exact Hw]. }
  split; [exact HGV|].
  split; [rewrite E2; exact Hsp|]. split; [rewrite E3; exact Hgp|]. split; [rewrite E4; exact Htp|].
  split.
  { apply (uf_bytes_same rsegs mem mem'); [|exact Hsv].
    intros i Hi. unfold saved_bytes in Hi. rewrite ?length_app, ?length_le8 in Hi. cbn in Hi.
    apply HU; [lia|]. intros Hk. destruct (NK _ Hk) as (_ & H2 & _). lia. }
  split.
  { destruct Hstk as (Hs1 & Hs2 & Hs3). split; [exact Hs1|]. split; [exact Hs2|].
    intros a Ha. destruct (Hs3 a Ha) as [Hw _].
    assert (Hw' : wview rsegs mem' (wa a) <> None) by (apply HW; exact Hw).
    split; [exact Hw'|].
    destruct (uf_wview_none mem' (wa a) ltac:(rewrite wa_unsigned by lia; apply uf_fs_none; unfold IMG_HI; lia) Hw')
      as (b & Hb).
    exists b. unfold mrd. rewrite Hb. reflexivity. }
  split.
  { intros w Hro. pose proof Hro as Hro'. rewrite SEG in Hro'. pose proof (uf_ro_img w Hro') as Hi.
    assert (E : mem' w = mem w).
    { rewrite <- (Z_to_bv_bv_unsigned w). apply HU; [exact (uf_ur w)|]. intros Hk. exact (proj1 (NK _ Hk) Hi). }
    unfold mrd. rewrite E. exact (HMI w Hro). }
  split.
  { intros a Ha. destruct (uf_relro_img a Ha) as (Hi & _).
    pose proof (uf_img_lt a Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    destruct (SAME a ltac:(lia) ltac:(intros Hk; exact (proj1 (NK _ Hk) Hi))) as [E _].
    rewrite E. exact (Hrel a Ha). }
  destruct (mr_model B MR uf_laws L A mem md HMR) as (Hh & Hl & Hm).
  split.
  { apply (mr_frame B MR uf_laws L A mem mem' md md HMR).
    - intros a Ho. pose proof (mr_owned_low B MR uf_laws L A mem md a HMR Ho).
      apply (SAME a ltac:(lia)). intros Hk. exact (proj1 (proj2 (proj2 (NK _ Hk))) Ho).
    - intros a Ho (b & Hb). pose proof (mr_owned_low B MR uf_laws L A mem md a HMR Ho).
      exists b. rewrite (HU a ltac:(lia)); [exact Hb|]. intros Hk. exact (proj1 (proj2 (proj2 (NK _ Hk))) Ho).
    - intros p n i Hin Hi. destruct (mr_blocks B MR uf_laws L A mem md p n i HMR Hin Hi) as ((b & Hb) & H2 & H3 & _).
      pose proof (ax_blocks_img uf_ax L A mem md p n i HMR Hin Hi) as Hni.
      unfold present. apply (PRES (ptr_addr L p + i) ltac:(lia) Hni). unfold wview. rewrite Hb. discriminate.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|]. split; [exact Hmd|].
  split.
  { intros a Ha Hw He. destruct (Hhi a Ha Hw He) as [E1 E2'].
    assert (Hnk : ~ kreg g hb a).
    { intros Hk. destruct (NK _ Hk) as (_ & H1 & _ & _ & [H|H]); [lia|]. apply Hw. lia. }
    destruct (SAME a ltac:(lia) Hnk) as [M3 M4].
    split; [rewrite M3; exact E1 | tauto]. }
  split.
  { intros a Hi Hs Hc He. destruct (Himg a Hi Hs Hc He) as [E1 E2'].
    pose proof (uf_img_lt a Hi) as Hl'. unfold IMG_LO, IMG_HI in Hl'.
    destruct (SAME a ltac:(lia) ltac:(intros Hk; exact (proj1 (NK _ Hk) Hi))) as [M3 M4].
    split; [rewrite M3; exact E1 | tauto]. }
  split.
  { intros a k i Hin Hi. rewrite <- (HB0 a k i Hin Hi).
    destruct (uf_b0_facts L A mem md hb _ a k i HMR HP Hin Hi) as (H0 & H1 & H2).
    exact (proj1 (SAME (a + i) ltac:(lia) ltac:(intros [Hk|Hk]; [lia | exact (H2 Hk)]))). }
  split; [intros a Ha; unfold writable_at; rewrite SEG; apply HW; rewrite <- SEG; exact (Her a Ha)|].
  split.
  { apply (uf_sink_tr mem mem' md md); [| reflexivity | exact Hsk].
    intros a Ha. destruct (uf_sink_ok a Ha) as (Hr & Hi & _).
    exact (proj1 (SAME a Hr ltac:(intros Hk; exact (proj1 (NK _ Hk) Hi)))). }
  split; [exact HRS|].
  intros a Ha. unfold writable_at. rewrite SEG. apply HW. rewrite <- SEG. exact (Hwin a Ha).
Qed.

Lemma uf_errc : errno_addr B + 4 <= alloc_ceiling.
Proof. destruct FF as (_ & _ & _ & _ & _ & _ & H & _). exact (H rc). Qed.

Lemma uf_noimg_hi : forall a, IMG_HI <= a -> ~ in_img B a.
Proof. intros a Ha Hi. apply uf_img_lt in Hi. lia. Qed.

Lemma uf_spZ : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  spZ regs = g_S g - 384.
Proof.
  intros g km hb L A regs mem md HF. destruct HF as (HGV & Hsp & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  unfold spZ. rewrite Hsp. unfold fsp, SLOT_FRAME. apply unsigned_lit. unfold SLOT_K, SLOT_STACK in HSc. lia.
Qed.

Lemma uf_FR_callk : forall K0 g km hb L A regs mem md E L' A' regs' mem' md' km' hb',
  ALLOC_STACK <= K0 <= ALLOC_STACK + 16 ->
  FR B APIf ra empty g km hb L A regs mem md ->
  call_post_k B MR K0 L A regs mem md E L' A' regs' mem' md' ->
  (forall a, E a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
     mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
  ro_agree (ms_segs B) mem' -> st_init_done A' = true -> RESB (g_b g) km' hb' A' ->
  FR B APIf ra empty g km' hb' L' A' regs' mem' md'.
Proof.
  intros K0 g km hb L A regs mem md E L' A' regs' mem' md' km' hb' HK0 HF HC HE HB0' HRO' HIN' HRS'.
  unfold ALLOC_STACK in HK0.
  pose proof uf_segs as SEG. pose proof (uf_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & HPB).
  destruct HC as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & FR' & UB' & SC').
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  assert (HK : SLOT_K = 65536) by reflexivity.
  pose proof uf_errc as ERC.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> (alloc_ceiling <= a \/ in_img B a) ->
     ~ (g_S g - 384 - K0 <= a < g_S g - 384) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
     (in_img B a -> ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE)) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Hr Ha Hs He Hc. apply FR'.
    - destruct Ha as [Ha|Ha]; [left; lia | right; exact Ha].
    - intros Ho. pose proof (mr_owned_low B MR uf_laws L A mem md a HMR Ho) as Hlow.
      destruct Ha as [Ha|Ha]; [lia|]. destruct (Hc Ha) as [Hs1 Hc1].
      destruct Ho as [Ho|Ho]; [exact (Hc1 (ax_img uf_ax L A mem md a HMR Ha Ho)) | exact (Hs1 Ho)].
    - intros Ho. pose proof (mr_owned_low B MR uf_laws L' A' mem' md' a MR' Ho) as Hlow.
      destruct Ha as [Ha|Ha]; [lia|]. destruct (Hc Ha) as [Hs1 Hc1].
      destruct Ho as [Ho|Ho]; [exact (Hc1 (ax_img uf_ax L' A' mem' md' a MR' Ha Ho)) | exact (Hs1 Ho)].
    - unfold scratch_k. rewrite SPZ. lia.
    - intros HEa. destruct (HE a HEa) as [H1 H2]. destruct Ha as [Ha|Ha]; [lia | exact (H2 Ha)]. }
  assert (KST : forall a, g_S g - 65536 <= a < g_S g -> ~ (g_S g - 384 - K0 <= a < g_S g - 384) ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hs. apply KEEP; [lia | left; lia | exact Hs | lia |].
    intros Hi. exfalso. exact (uf_noimg_hi a ltac:(unfold IMG_HI; lia) Hi). }
  assert (SCR : forall a, g_S g - 384 - K0 <= a < g_S g - 384 -> writable_at (ms_segs B) mem' a).
  { intros a Ha. apply SC'. unfold scratch_k. rewrite SPZ. left. lia. }
  split; [exact HGV|].
  split; [etransitivity; [exact (RP' 2 ltac:(unfold callee_saved; lia))|]; exact Hsp|].
  split; [etransitivity; [exact (RP' 3 ltac:(unfold callee_saved; lia))|]; exact Hgp|].
  split; [etransitivity; [exact (RP' 4 ltac:(unfold callee_saved; lia))|]; exact Htp|].
  split.
  { apply (uf_bytes_mbyte rsegs mem mem'); [|exact Hsv].
    intros i Hi. unfold saved_bytes in Hi. rewrite ?length_app, ?length_le8 in Hi. cbn in Hi.
    rewrite <- SEG. apply KST; lia. }
  split.
  { destruct Hstk as (Hs1 & Hs2 & Hs3). split; [exact Hs1|]. split; [exact Hs2|].
    intros a Ha.
    assert (Hd : (g_S g - 384 - K0 <= a < g_S g - 384) \/ ~ (g_S g - 384 - K0 <= a < g_S g - 384)) by lia.
    destruct Hd as [Hd|Hd].
    - pose proof (SCR a Hd) as W. unfold writable_at in W. rewrite SEG in W. split; [exact W|].
      destruct (uf_wview_none mem' (wa a) ltac:(rewrite wa_unsigned by lia; apply uf_fs_none; unfold IMG_HI; lia) W)
        as (b & Hb).
      exists b. unfold mrd. rewrite Hb. reflexivity.
    - destruct (Hs3 a Ha) as [Hw (b & Hb)].
      destruct (KST a ltac:(lia) Hd) as [M1 M2]. rewrite SEG in M1, M2.
      split.
      + change (writable_at rsegs mem' a). apply M2. exact Hw.
      + exists b. change (mbyte rsegs mem' a = Some b). rewrite M1. exact Hb. }
  split; [exact HRO'|].
  split.
  { intros a Ha. destruct (uf_relro_img a Ha) as (Hi & Hs & Hc & He).
    pose proof (uf_img_lt a Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    destruct (KEEP a ltac:(lia) (or_intror Hi) ltac:(lia) He ltac:(intros _; split; assumption)) as [M1 _].
    rewrite M1. exact (Hrel a Ha). }
  split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact HIN'|].
  split; [destruct Hmd as (vm & Emd0); exists vm'; rewrite Emd, Emd0; reflexivity|].
  split.
  { intros a Ha Hw He. destruct (Hhi a Ha Hw He) as [E1 E2].
    destruct (KEEP a ltac:(lia) ltac:(left; lia) ltac:(lia) He
      ltac:(intros Hi'; exfalso; exact (uf_noimg_hi a ltac:(unfold IMG_HI; lia) Hi'))) as [M1 M2].
    split; [rewrite M1; exact E1 | tauto]. }
  split.
  { intros a Hi Hs Hc He. destruct (Himg a Hi Hs Hc He) as [E1 E2].
    pose proof (uf_img_lt a Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    destruct (KEEP a ltac:(lia) (or_intror Hi) ltac:(lia) He ltac:(intros _; split; assumption)) as [M1 M2].
    split; [rewrite M1; exact E1 | tauto]. }
  split; [intros a k i Hin Hi; rewrite (HB0' a k i Hin Hi); exact (HB0 a k i Hin Hi)|].
  split; [intros a Ha; apply SC'; unfold scratch_k; right; exact Ha|].
  split.
  { apply (uf_sink_tr mem mem' md md'); [| rewrite Emd; reflexivity | exact Hsk].
    intros a Ha. destruct (uf_sink_ok a Ha) as (Hr & Hi & Hs & Hc & He).
    pose proof (uf_img_lt a Hi) as Hl. unfold IMG_LO, IMG_HI in Hl.
    exact (proj1 (KEEP a Hr (or_intror Hi) ltac:(lia) He ltac:(intros _; split; assumption))). }
  split; [exact HRS'|].
  intros a Ha.
  assert (Hd : (g_S g - 384 - K0 <= a < g_S g - 384) \/ ~ (g_S g - 384 - K0 <= a < g_S g - 384)) by lia.
  destruct Hd as [Hd|Hd]; [exact (SCR a Hd)|].
  destruct (KST a ltac:(lia) Hd) as [_ M2]. apply M2. exact (Hwin a Ha).
Qed.

Lemma uf_FR_call : forall g km hb L A regs mem md E L' A' regs' mem' md' km' hb',
  FR B APIf ra empty g km hb L A regs mem md ->
  call_post_k B MR ALLOC_STACK L A regs mem md E L' A' regs' mem' md' ->
  (forall a, E a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (forall a k i, In (a, k) (blocks (g_L g) (g_A g)) -> 0 <= i < k ->
     mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
  ro_agree (ms_segs B) mem' -> st_init_done A' = true -> RESB (g_b g) km' hb' A' ->
  FR B APIf ra empty g km' hb' L' A' regs' mem' md'.
Proof.
  intros g km hb L A regs mem md E L' A' regs' mem' md' km' hb'.
  apply uf_FR_callk. unfold ALLOC_STACK. lia.
Qed.

Lemma uf_call_pre : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  lib.Reusable.YK0s.ret_ok (getr regs 1) -> call_pre B MR L A regs mem md.
Proof.
  intros g km hb L A regs mem md HF HRA. pose proof (uf_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & HPB).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  unfold SLOT_K, SLOT_STACK in *.
  unfold call_pre. rewrite SPZ. unfold ALLOC_STACK.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HRA|].
  split; [Z.div_mod_to_equations; lia|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply Hwin; lia|].
  split; [rewrite Htp; exact HgT|].
  split; [exact Her|].
  intros H0. rewrite HIN in H0. discriminate.
Qed.

Lemma uf_malloc_step : forall g km hb L A regs mem md n P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 24 -> 0 <= n <= 2 ^ 20 ->
  lib.Reusable.YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 n ->
  (forall L' A' regs' mem' md' res,
     FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 res -> res <> 0 ->
     (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
     Rz (ms_segs B) (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') P) ->
  Rz (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md n P HF HP Hlen Hhb Hn HRA H10 HK.
  pose proof (uf_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  pose proof (uf_call_pre _ _ _ _ _ _ _ _ HF HRA) as CP.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & HPB).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC. pose proof uf_errc as ERC.
  pose proof (rz_room_of L A mem md (g_b g) (Z.of_nat (length hb)) (hb_bytes hb) n HMR Hroom ltac:(lia) Hhb Hn)
    as ROOM.
  eapply rz_bind; [exact (rz_malloc L A regs mem md n (sb_hb (g_b g) hb) CP HMI H10 HRS ROOM)|].
  intros c' (L' & A' & regs' & mem' & md' & res & -> & HC & R10 & Hr0 & Hr16 & Hfr & (b1 & b2 & Eb' & Eb) & Hkept
    & HRO' & HGK & HUB & HIN' & HLEN & HRES').
  assert (HP' : Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g))).
  { rewrite Eb', <- app_assoc. cbn [app].
    apply Permutation_trans with ((res, n) :: (b1 ++ b2)); [apply Permutation_sym, Permutation_middle|].
    rewrite <- Eb. apply Permutation_trans with ((res, n) :: hb ++ blocks (g_L g) (g_A g)); [apply perm_skip; exact HP|].
    apply Permutation_middle. }
  assert (HF' : FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md').
  { apply (uf_FR_call g km hb L A regs mem md (fun _ => False) L' A' regs' mem' md' (km + 1) (hb ++ [(res, n)]) HF HC).
    - intros a [].
    - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
    - exact HRO'.
    - exact HIN'.
    - exact (resb_malloc (g_b g) (km + 1) hb (hb ++ [(res, n)]) A' res n
               (Permutation_sym (Permutation_cons_append hb (res, n))) HRES'). }
  destruct HC as (_ & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  apply (HK L' A' regs' mem' md' res HF' HP' RP' R10 Hr0).
  - intros x Hx. unfold fsp, SLOT_FRAME in Hx. unfold SLOT_K, SLOT_STACK in HSc. apply FR'.
    + left. lia.
    + intros Ho. pose proof (mr_owned_low B MR uf_laws L A mem md x HMR Ho). lia.
    + intros Ho. destruct HF' as (_ & _ & _ & _ & _ & _ & _ & _ & HMR' & _).
      pose proof (mr_owned_low B MR uf_laws L' A' mem' md' x HMR' Ho). lia.
    + unfold scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
    + intros [].
  - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
Qed.

Lemma uf_bufof_step : forall g km hb L A regs mem md c P,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 24 -> 0 <= c <= 2 ^ 20 ->
  lib.Reusable.YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 c ->
  (forall L' A' regs' mem' md' res,
     FR B APIf ra empty g (km + 1) (hb ++ [(res, bsz c)]) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb ++ [(res, bsz c)]) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' -> getr regs' 10 = Z_to_bv 64 res -> res <> 0 ->
     (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)) ->
     Rz (ms_segs B) (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') P) ->
  Rz (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 U.Prog.buf_of_c.BUF_OF) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb L A regs mem md c P HF HP Hlen Hhb Hc HRA H10 HK.
  pose proof (uf_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & HPB).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC. pose proof uf_errc as ERC.
  assert (CP : call_pre_k B MR (U.Prog.buf_of_c.BUF_OF_FRAME + ALLOC_STACK) L A regs mem md).
  { unfold SLOT_K, SLOT_STACK in *. unfold call_pre_k. rewrite SPZ.
    unfold U.Prog.buf_of_c.BUF_OF_FRAME, ALLOC_STACK.
    split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HRA|].
    split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|].
    split; [intros a Ha; apply Hwin; lia|].
    split; [rewrite Htp; exact HgT|].
    split; [exact Her|].
    intros H0. rewrite HIN in H0. discriminate. }
  pose proof (rz_room_of L A mem md (g_b g) (Z.of_nat (length hb)) (hb_bytes hb) (Z.max c 1) HMR Hroom ltac:(lia)
    Hhb ltac:(lia)) as ROOM.
  eapply rz_bind.
  { exact (U.Prog.buf_of.buf_of_holds B (APIf rc) L A regs mem md c (sb_hb (g_b g) hb) uf_segs uf_malloc_pc ERC CP HMI H10 ltac:(lia) HRS ROOM). }
  intros c' (L' & A' & regs' & mem' & md' & res & -> & HC & R10 & Hr0 & Hr16 & Hfr & (b1 & b2 & Eb' & Eb) & Hkept
    & HRO' & HGK & HUB & HIN' & HLEN & HRES').
  change (Z.max c 1) with (bsz c) in Eb', HRES'.
  assert (HP' : Permutation (blocks L' A') ((hb ++ [(res, bsz c)]) ++ blocks (g_L g) (g_A g))).
  { rewrite Eb', <- app_assoc. cbn [app].
    apply Permutation_trans with ((res, bsz c) :: (b1 ++ b2)); [apply Permutation_sym, Permutation_middle|].
    rewrite <- Eb. apply Permutation_trans with ((res, bsz c) :: hb ++ blocks (g_L g) (g_A g));
      [apply perm_skip; exact HP|].
    apply Permutation_middle. }
  assert (HF' : FR B APIf ra empty g (km + 1) (hb ++ [(res, bsz c)]) L' A' regs' mem' md').
  { apply (uf_FR_callk (U.Prog.buf_of_c.BUF_OF_FRAME + ALLOC_STACK) g km hb L A regs mem md (fun _ => False)
             L' A' regs' mem' md' (km + 1) (hb ++ [(res, bsz c)])); [| exact HF | exact HC | | | | |].
    - unfold U.Prog.buf_of_c.BUF_OF_FRAME. lia.
    - intros a [].
    - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
      apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
    - exact HRO'.
    - exact HIN'.
    - exact (resb_malloc (g_b g) (km + 1) hb (hb ++ [(res, bsz c)]) A' res (bsz c)
               (Permutation_sym (Permutation_cons_append hb (res, bsz c))) HRES'). }
  destruct HC as (_ & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  apply (HK L' A' regs' mem' md' res HF' HP' RP' R10 Hr0).
  - intros x Hx. unfold fsp, SLOT_FRAME in Hx. unfold SLOT_K, SLOT_STACK in HSc. apply FR'.
    + left. lia.
    + intros Ho. pose proof (mr_owned_low B MR uf_laws L A mem md x HMR Ho). lia.
    + intros Ho. destruct HF' as (_ & _ & _ & _ & _ & _ & _ & _ & HMR' & _).
      pose proof (mr_owned_low B MR uf_laws L' A' mem' md' x HMR' Ho). lia.
    + unfold scratch_k. rewrite SPZ. unfold U.Prog.buf_of_c.BUF_OF_FRAME, ALLOC_STACK. lia.
    + intros [].
  - intros a k i Hin Hi. apply (Hkept a k i); [|intros []|exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
Qed.

Lemma uf_free_step : forall g km hb1 a n hb2 L A regs mem md P,
  FR B APIf ra empty g km (hb1 ++ (a, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (a, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  0 < n <= MMAP_THRESHOLD ->
  lib.Reusable.YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 a ->
  (forall L' A' regs' mem' md',
     FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs regs' ->
     (forall x, fsp g <= x < g_S g -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
     Rz (ms_segs B) (mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md') P) ->
  Rz (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros g km hb1 a n hb2 L A regs mem md P HF HP Hn HRA H10 HK.
  pose proof (uf_spZ _ _ _ _ _ _ _ _ HF) as SPZ.
  pose proof (uf_call_pre _ _ _ _ _ _ _ _ HF HRA) as CP.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (Hn0 & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & HPB).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC. pose proof uf_errc as ERC.
  pose proof (Permutation_sym (Permutation_middle hb1 hb2 (a, n))) as HPm.
  assert (Hab : In (a, n) (blocks L A)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  destruct (uf_blk_of L A a n Hab) as (p & Hp & Epa).
  eapply rz_bind;
    [exact (rz_free L A regs mem md p n (sb_hb (g_b g) (hb1 ++ (a, n) :: hb2)) CP HMI Hp ltac:(rewrite Epa; exact H10) HRS)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & HC & (b1 & b2 & Eb & Eb') & Hkept & HRO' & HGK & HUB & HINi & HLEN
    & HRES').
  rewrite Epa in Eb, Hkept, HC.
  apply call_post_k_alloc in HC.
  assert (HP' : Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g))).
  { rewrite Eb', <- app_assoc. apply (Permutation_app_inv _ _ _ _ (a, n)).
    rewrite <- Eb. rewrite <- app_assoc in HP. cbn [app] in HP. exact HP. }
  assert (HF' : FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md').
  { apply (uf_FR_call g km (hb1 ++ (a, n) :: hb2) L A regs mem md _ L' A' regs' mem' md' km (hb1 ++ hb2) HF HC).
    - intros x Hx. destruct (uf_blk_facts L A mem md a n (x - a) HMR Hab ltac:(lia)) as (_ & H2 & H3 & _ & H5).
      replace (a + (x - a)) with x in H5 by lia. split; [lia | exact H5].
    - intros a' k i Hin Hi. apply (Hkept a' k i); [| | exact Hi].
      + apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hin.
      + intros Ea. subst a'.
        destruct (uf_b0_facts L A mem md _ _ a k i HMR HP Hin Hi) as (_ & _ & Hnh).
        destruct (uf_b0_facts L A mem md _ _ a k 0 HMR HP Hin ltac:(lia)) as (_ & _ & Hnh0).
        apply Hnh0. exists a, n. split; [apply in_or_app; right; left; reflexivity | lia].
    - exact HRO'.
    - exact (HINi HIN).
    - apply (resb_free (g_b g) km (hb1 ++ (a, n) :: hb2) (hb1 ++ hb2) A' a n HPm).
      exact HRES'. }
  destruct HC as (_ & _ & _ & _ & _ & RP' & _ & FR' & _ & _).
  apply (HK L' A' regs' mem' md' HF' HP' RP').
  intros x Hx. unfold fsp, SLOT_FRAME in Hx. unfold SLOT_K, SLOT_STACK in HSc. apply FR'.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low B MR uf_laws L A mem md x HMR Ho). lia.
  - intros Ho. destruct HF' as (_ & _ & _ & _ & _ & _ & _ & _ & HMR' & _).
    pose proof (mr_owned_low B MR uf_laws L' A' mem' md' x HMR' Ho). lia.
  - unfold scratch, scratch_k. rewrite SPZ. unfold ALLOC_STACK. lia.
  - cbn. destruct (uf_blk_facts L A mem md a n 0 HMR Hab ltac:(lia)) as (_ & H2 & H3 & _). lia.
Qed.

Lemma uf_kA_run : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m' regs' mem', Q R pc' m' -> xregs_eqv R regs' -> mem_rel rsegs mem' m' -> ro_same rsegs mem mem' ->
     Rz (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HRO HE HK.
  pose proof uf_segs as SEG.
  eapply (rz_evt_canon (ms_segs B) (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [| exact Hh | exact Hl |].
  - rewrite uf_canon_mkst. rewrite SEG. apply (evt_normalize rsegs); [exact wx_apart_rsegs | rewrite <- SEG; exact HRO |].
    exact HE.
  - intros ms' (can & (s0 & (R & pc' & m' & -> & HQ) & Hrel & Hsame) & Heq).
    destruct can as [cR cF cpc csvc cres cfc cmem crom].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & Hmr). cbn in E1, E2, E3, E4, E5, E6, E7, Hmr, Hsame.
    subst cR cF cpc csvc cres cfc crom.
    destruct (uf_eqv_mkst R pc' cmem (seg_rom rsegs) ms' Heq) as (R' & -> & XR).
    rewrite <- SEG. apply (HK R pc' m' R' cmem HQ XR Hmr Hsame).
Qed.

Lemma uf_stk_norm : forall m lo hi, stk rsegs m lo hi -> IMG_HI <= lo -> stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H3) Hlo. split; [exact H1|]. split; [exact H2|].
  intros a Ha. assert (Hro : Mem.ro_addr rsegs (wa a) = false).
  { unfold Mem.ro_addr. rewrite wa_unsigned by lia. rewrite uf_fs_none by lia. reflexivity. }
  assert (E : normalize rsegs m (wa a) = m (wa a)) by (unfold normalize; rewrite Hro; reflexivity).
  destruct (H3 a Ha) as [Hw (b & Hb)]. unfold wview, mrd in *. rewrite E. split; [exact Hw | exists b; exact Hb].
Qed.

Lemma uf_outside : forall (P : Z -> Prop) W x, (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> P y) -> ~ P x ->
  outside W x.
Proof.
  intros P W x H Hx. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  split; [intros Hr; exact (Hx (H lo hi x (or_introl eq_refl) Hr))|].
  apply IH. intros lo' hi' y Hin Hy. exact (H lo' hi' y (or_intror Hin) Hy).
Qed.

Lemma uf_munch_unch : forall (P : Z -> Prop) W (mem mem' : word -> option byte),
  munch W mem mem' -> (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> P y) ->
  forall x, 0 <= x < 2 ^ 64 -> ~ P x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof.
  intros P W mem mem' Hm HW x Hx HP. apply Hm. rewrite unsigned_lit by exact Hx. exact (uf_outside P W x HW HP).
Qed.

Lemma uf_kA_run0 : forall (regs : bvmap 5 word) pc mem md (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\ Q R pc' m')
    (MS (mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' m' regs', Q R pc' m' -> xregs_eqv R regs' ->
     Rz (ms_segs B) (mkCfg (mkst regs' pc' m' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md Q P Hh Hl HE HK.
  pose proof uf_segs as SEG.
  eapply (rz_evt_canon (ms_segs B) (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [| exact Hh | exact Hl |].
  - rewrite uf_canon_mkst. rewrite SEG. exact HE.
  - intros ms' (can & (R & pc' & m' & -> & HQ) & Heq).
    destruct (uf_eqv_mkst R pc' m' (seg_rom rsegs) ms' Heq) as (R' & -> & XR).
    rewrite <- SEG. exact (HK R pc' m' R' HQ XR).
Qed.

Lemma uf_FR_munch : forall g km hb L A regs mem md regs' mem' W,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> kreg g hb y) ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' W HF HP E2 E3 E4 Hm Hw HW.
  apply (uf_FR_kA g km hb L A regs mem md regs' mem' HF HP E2 E3 E4); [|exact Hw].
  exact (uf_munch_unch (kreg g hb) W mem mem' Hm HW).
Qed.

Lemma uf_hb_low : forall g km hb L A regs mem md x,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> in_hb hb x ->
  4096 <= x < alloc_ceiling /\ x + SLOT_K < g_S g.
Proof.
  intros g km hb L A regs mem md x HF HP Hx.
  destruct HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof HGV as (_ & _ & _ & _ & HSc & _).
  destruct (uf_hb_facts L A mem md hb _ x HMR HP Hx) as (_ & H2 & _). split; [exact H2 | lia].
Qed.

Lemma uf_hb_blk : forall g km hb L A regs mem md a k,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (a, k) hb ->
  (forall i, 0 <= i < k -> writable_at (ms_segs B) mem (a + i) /\ present mem (a + i) /\ ~ in_img B (a + i)) /\
  4096 <= a /\ a + k <= alloc_ceiling /\ a mod 16 = 0.
Proof.
  intros g km hb L A regs mem md a k HF HP Hin.
  destruct HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  assert (Hb : In (a, k) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
  destruct (uf_blk_of L A a k Hb) as (p & Hp & Ea).
  destruct (mr_blocks_range B MR uf_laws L A mem md p k HMR Hp) as (R1 & R2).
  pose proof (mr_blocks_aligned B MR uf_laws L A mem md p k HMR Hp) as Hal.
  rewrite Ea in R1, R2, Hal.
  destruct uf_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BW & _).
  split; [|split; [exact R1 | split; [exact R2 | exact Hal]]].
  intros i Hi. destruct (uf_blk_facts L A mem md a k i HMR Hb Hi) as (H1 & _ & _ & _ & H5).
  split; [exact (BW L A mem md a k i HMR Hb Hi)|]. split; assumption.
Qed.

Lemma uf_hb_in1 : forall a k y, a <= y < a + k -> in_hb [(a, k)] y.
Proof. intros a k y H. exists a, k. split; [left; reflexivity | exact H]. Qed.

End T.

Lemma uf_FReq_munch : forall g W (mem mem' : word -> option byte), munch W mem mem' ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> y < fsp g \/ g_S g <= y) -> 0 <= fsp g -> g_S g <= 2 ^ 64 ->
  forall x, fsp g <= x < g_S g -> mbyte rsegs mem' x = mbyte rsegs mem x.
Proof.
  intros g W mem mem' Hm HW H0 H1 x Hx. unfold mbyte.
  rewrite (uf_munch_unch (fun y => y < fsp g \/ g_S g <= y) W mem mem' Hm HW x ltac:(lia) ltac:(cbv beta; lia)).
  reflexivity.
Qed.

Lemma uf_nowrite : forall (mem mem' : word -> option byte),
  mem_rel rsegs mem' (normalize rsegs mem) -> ro_same rsegs mem mem' -> forall w, mem' w = mem w.
Proof.
  intros mem mem' Hr Hs w. destruct (Mem.ro_addr rsegs w) eqn:E.
  - exact (Hs w E).
  - rewrite <- (mem_rel_rw rsegs mem' (normalize rsegs mem) w Hr E). unfold normalize. rewrite E. reflexivity.
Qed.

Lemma uf_wmono_eq : forall (mem mem' : word -> option byte), (forall w, mem' w = mem w) -> wmono rsegs mem mem'.
Proof. intros mem mem' H x Hx. unfold wview in *. rewrite H. exact Hx. Qed.

Definition CSeq (regs regs' : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition FReq (g : ghost) (mem mem' : word -> option byte) : Prop :=
  forall x, fsp g <= x < g_S g -> mbyte rsegs mem' x = mbyte rsegs mem x.

Lemma uf_CSeq_trans : forall r1 r2 r3, CSeq r1 r2 -> CSeq r2 r3 -> CSeq r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma uf_CSeq_pres : forall r1 r2, regs_preserved r1 r2 -> CSeq r1 r2.
Proof. intros r1 r2 H. exact H. Qed.

Lemma uf_FReq_trans : forall g m1 m2 m3, FReq g m1 m2 -> FReq g m2 m3 -> FReq g m1 m3.
Proof. intros g m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

Lemma uf_FReq_eq : forall g (m1 m2 : word -> option byte), (forall w, m2 w = m1 w) -> FReq g m1 m2.
Proof. intros g m1 m2 H x Hx. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma uf_fbytes : forall g (mem mem' : word -> option byte) k l, FReq g mem mem' ->
  0 <= k -> k + Z.of_nat (length l) <= SLOT_FRAME -> bytes_at rsegs mem (spk g k) l -> bytes_at rsegs mem' (spk g k) l.
Proof.
  intros g mem mem' k l H Hk Hl Hb. apply (uf_bytes_mbyte rsegs mem mem'); [|exact Hb].
  intros i Hi. apply H. unfold spk, fsp, SLOT_FRAME in *. lia.
Qed.

Lemma uf_q64_tr : forall g mem mem' k v, FReq g mem mem' -> 0 <= k <= SLOT_FRAME - 8 ->
  q64 mem (spk g k) v -> q64 mem' (spk g k) v.
Proof. intros g mem mem' k v H Hk Hb. apply (uf_fbytes g mem mem' k); [exact H | lia | rewrite length_le8; lia | exact Hb]. Qed.

Lemma uf_TID_tr : forall g mem mem', FReq g mem mem' -> TID g mem -> TID g mem'.
Proof.
  intros g mem mem' H (H1 & H2). split.
  - apply (uf_q64_tr g mem mem' 24); [exact H | unfold SLOT_FRAME; lia | exact H1].
  - unfold IDb in *. apply (uf_fbytes g mem mem' 146); [exact H | lia | | exact H2].
    rewrite rec_id_length. unfold SLOT_FRAME, RcIdentModel.ID_SIZE. lia.
Qed.

Ltac uf_cs CS k := etransitivity; [exact (CS k ltac:(unfold callee_saved; lia))|].

Lemma uf_TL_tr : forall g regs regs' mem mem', CSeq regs regs' -> FReq g mem mem' -> TL g regs mem -> TL g regs' mem'.
Proof.
  intros g regs regs' mem mem' C F (H24 & H9 & H56 & H48 & H25 & H27 & H19).
  split; [uf_cs C 24; exact H24|]. split; [uf_cs C 9; exact H9|].
  split; [apply (uf_q64_tr g mem mem' 56); [exact F | unfold SLOT_FRAME; lia | exact H56]|].
  split; [apply (uf_q64_tr g mem mem' 48); [exact F | unfold SLOT_FRAME; lia | exact H48]|].
  split; [uf_cs C 25; exact H25|]. split; [uf_cs C 27; exact H27|]. uf_cs C 19; exact H19.
Qed.

Ltac uf_cs_split r Hr :=
  unfold callee_saved in Hr;
  let Hr' := fresh "Hr" in
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]]].

Lemma uf_bsz_seqz : forall cap, 0 <= cap < 2 ^ 64 ->
  Z_to_bv 64 (cap + bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 cap) 1)) = Z_to_bv 64 (bsz cap).
Proof.
  intros cap Hc. unfold PropExec.v_sltiu. rewrite (unsigned_lit cap) by exact Hc. change (bv_wrap 64 1) with 1.
  unfold bsz. destruct (Z.ltb_spec cap 1) as [H|H].
  - rewrite (unsigned_lit 1) by lia. f_equal. lia.
  - rewrite (unsigned_lit 0) by lia. f_equal. lia.
Qed.

Lemma uf_eqb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite (unsigned_lit x Hx), (unsigned_lit y Hy). reflexivity. Qed.

Lemma uf_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite (unsigned_lit x Hx), (unsigned_lit y Hy). reflexivity. Qed.

Lemma uf_lts : forall x y, -2 ^ 63 <= x < 2 ^ 63 -> -2 ^ 63 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma uf_byte_eq : forall (b : byte) z, z mod 256 = bv_unsigned b -> Z_to_bv 8 z = b.
Proof.
  intros b z H. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  exact H.
Qed.

Lemma uf_bz_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H. Qed.

Lemma uf_le2 : forall b0 b1 : byte,
  le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1)) = [b0; b1].
Proof.
  intros b0 b1. pose proof (uf_bz_range b0). pose proof (uf_bz_range b1).
  unfold le2. rewrite (unsigned_lit _) by lia. cbn [Z_to_le_bytes].
  f_equal; [apply uf_byte_eq; Z.div_mod_to_equations; lia|]. f_equal.
  apply uf_byte_eq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. Z.div_mod_to_equations; lia.
Qed.

Lemma uf_firstn2 : forall (l : list byte) k, (S k < length l)%nat ->
  firstn 2 (skipn k l) = [RcIdentModel.nthb l k; RcIdentModel.nthb l (S k)].
Proof.
  intros l. induction l as [|x l IH]; intros [|k] Hk; cbn in *; try lia.
  - destruct l as [|y l]; cbn in *; [lia | reflexivity].
  - apply IH. lia.
Qed.

Lemma uf_rd2 : forall m a l k, bytes_at rsegs m a l -> 0 <= k -> (S (Z.to_nat k) < length l)%nat ->
  ov_read_bytes rsegs m (wa (a + k)) 2 =
  Some (le2 (Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb l (Z.to_nat k)) +
                         256 * RcIdentModel.bz (RcIdentModel.nthb l (S (Z.to_nat k)))))).
Proof.
  intros m a l k H Hk Hl. rewrite (bytes_at_read rsegs m a l k 2 H Hk) by lia.
  rewrite uf_firstn2 by lia. unfold RcIdentModel.bz. rewrite uf_le2. reflexivity.
Qed.

Lemma uf_zx16 : forall v, 0 <= v < 2 ^ 16 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof. intros v Hv. unfold zx16. rewrite (unsigned_lit v) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma uf_lor8 : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 hi)) 8))) (bv_unsigned (Z_to_bv 64 lo))) =
  Z_to_bv 64 (lo + 256 * hi).
Proof.
  intros lo hi Hl Hh. rewrite (unsigned_lit hi) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite (unsigned_lit (hi * 256)) by lia. rewrite (unsigned_lit lo) by lia.
  rewrite (U.KindBGlue.kb_lor_low (hi * 256) lo 8) by (try lia; change (2 ^ 8) with 256; Z.div_mod_to_equations; lia).
  f_equal. lia.
Qed.

Definition KP (l : list Z) (regs regs' : bvmap 5 word) : Prop :=
  forall k, In k l -> getr regs' (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k).

Ltac uf_kp XR regs :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; cbn [In] in Hk;
  repeat (destruct Hk as [<-|Hk];
          [rewrite (uf_getr_x _ _ _ XR) by reflexivity; rewrite (uf_getr_reg regs) by reflexivity; reflexivity|]);
  destruct Hk.

Ltac uf_in := cbn [In]; repeat (first [left; reflexivity | right]).

Ltac uf_k KP k := etransitivity; [exact (KP k ltac:(uf_in))|].

Lemma uf_TL_kp : forall g regs regs' mem mem', KP [9; 19; 24; 25; 27] regs regs' -> FReq g mem mem' ->
  TL g regs mem -> TL g regs' mem'.
Proof.
  intros g regs regs' mem mem' C F (H24 & H9 & H56 & H48 & H25 & H27 & H19).
  split; [uf_k C 24; exact H24|]. split; [uf_k C 9; exact H9|].
  split; [apply (uf_q64_tr g mem mem' 56); [exact F | unfold SLOT_FRAME; lia | exact H56]|].
  split; [apply (uf_q64_tr g mem mem' 48); [exact F | unfold SLOT_FRAME; lia | exact H48]|].
  split; [uf_k C 25; exact H25|]. split; [uf_k C 27; exact H27|]. uf_k C 19; exact H19.
Qed.

Lemma uf_KP_CSeq : forall regs regs1, KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1 ->
  CSeq regs regs1.
Proof. intros regs regs1 H r Hr. uf_cs_split r Hr; apply H; uf_in. Qed.

Lemma uf_lsd_len : forall k x, (Datatypes.length (write_uint_lsd k x) <= k)%nat.
Proof.
  induction k as [|k IH]; intros x; cbn [write_uint_lsd Datatypes.length]; [lia|].
  destruct (x <? 10); cbn [Datatypes.length]; [lia|]. specialize (IH (x / 10)). lia.
Qed.

Lemma uf_LV_le : forall ma mi pa, 0 <= reac_ver_str_LV ma mi pa <= 16.
Proof.
  intros ma mi pa. unfold reac_ver_str_LV, reac_ver_str_VER, reac_ver_str_DEC2, write_uint_D.
  rewrite !length_app, !length_rev. cbn [Datatypes.length].
  pose proof (uf_lsd_len 5 ma). pose proof (uf_lsd_len 5 mi). pose proof (uf_lsd_len 5 pa).
  destruct (pa <? 10); cbn [Datatypes.length]; try rewrite length_rev; lia.
Qed.

Lemma uf_dg_nz : forall x, 0 <= x < 10 -> bv_unsigned (write_uint_dg x) <> 0.
Proof.
  intros x Hx. unfold write_uint_dg. rewrite Z_to_bv_unsigned.
  change (bv_wrap 8 (48 + x)) with ((48 + x) mod 2 ^ 8). rewrite Z.mod_small by lia. lia.
Qed.

Lemma uf_lsd_nz : forall k v b, In b (write_uint_lsd k v) -> bv_unsigned b <> 0.
Proof.
  induction k as [|k IH]; intros v b H; cbn [write_uint_lsd] in H; [destruct H|].
  destruct H as [<-|H]; [apply uf_dg_nz; apply Z.mod_pos_bound; lia|].
  destruct (v <? 10); [destruct H | exact (IH _ _ H)].
Qed.

Lemma uf_VER_nz : forall ma mi pa, 0 <= pa -> forall b, In b (reac_ver_str_VER ma mi pa) -> bv_unsigned b <> 0.
Proof.
  intros ma mi pa Hp b H. unfold reac_ver_str_VER, reac_ver_str_DEC2, write_uint_D in H.
  apply in_app_or in H. destruct H as [H|H]; [rewrite <- in_rev in H; exact (uf_lsd_nz _ _ _ H)|].
  apply in_app_or in H. destruct H as [H|H].
  { destruct H as [<-|[]]. intros Hc. vm_compute in Hc. discriminate Hc. }
  apply in_app_or in H. destruct H as [H|H]; [rewrite <- in_rev in H; exact (uf_lsd_nz _ _ _ H)|].
  destruct (Z.ltb_spec pa 10) as [Hl|Hl].
  - destruct H as [<-|[<-|[]]]; apply uf_dg_nz; lia.
  - rewrite <- in_rev in H. exact (uf_lsd_nz _ _ _ H).
Qed.

Lemma uf_bytes_munch1 : forall lo hi (m m' : word -> option byte) a bs, munch [(lo, hi)] m m' ->
  (a + Z.of_nat (length bs) <= lo \/ hi <= a) -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros lo hi m m' a bs H Hd HB. pose proof HB as (B1 & B2 & _).
  apply (uf_bytes_same rsegs m m' a bs); [|exact HB]. intros i Hi. apply H.
  rewrite unsigned_lit by lia. cbn [outside]. split; [lia | exact I].
Qed.

Lemma uf_bytes_munchP : forall (P : Z -> Prop) W (m m' : word -> option byte) a bs, munch W m m' ->
  (forall lo hi y, In (lo, hi) W -> lo <= y < hi -> P y) ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ P (a + i)) -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros P W m m' a bs MU HW HN HB. pose proof HB as (B1 & B2 & _).
  apply (uf_bytes_same rsegs m m' a bs); [|exact HB]. intros i Hi.
  apply (uf_munch_unch P W m m' MU HW); [lia | exact (HN i Hi)].
Qed.

Definition FRout (g : ghost) (W : list (Z * Z)) : Prop :=
  forall lo hi y, In (lo, hi) W -> lo <= y < hi ->
    ~ (spk g 24 <= y < spk g 32) /\ ~ (spk g 48 <= y < spk g 64) /\ ~ (spk g 146 <= y < spk g 184).

Lemma uf_TID_munch : forall g W (m m' : word -> option byte), munch W m m' -> FRout g W -> TID g m -> TID g m'.
Proof.
  intros g W m m' MU HW (H1 & H2). split.
  - unfold G24, q64 in *. apply (uf_bytes_munchP _ W m m' _ _ MU HW); [|exact H1].
    intros i Hi. rewrite length_le8 in Hi. intros (C1 & _). apply C1. unfold spk. lia.
  - unfold IDb in *. apply (uf_bytes_munchP _ W m m' _ _ MU HW); [|exact H2].
    intros i Hi. rewrite rec_id_length in Hi. unfold RcIdentModel.ID_SIZE in Hi. intros (_ & _ & C3). apply C3.
    unfold spk in *. lia.
Qed.

Lemma uf_TL_munch : forall g W regs regs' (m m' : word -> option byte), KP [9; 19; 24; 25; 27] regs regs' ->
  munch W m m' -> FRout g W -> TL g regs m -> TL g regs' m'.
Proof.
  intros g W regs regs' m m' C MU HW (H24 & H9 & H56 & H48 & H25 & H27 & H19).
  split; [uf_k C 24; exact H24|]. split; [uf_k C 9; exact H9|].
  split.
  { unfold q64 in *. apply (uf_bytes_munchP _ W m m' _ _ MU HW); [|exact H56].
    intros i Hi. rewrite length_le8 in Hi. intros (_ & C2 & _). apply C2. unfold spk in *. lia. }
  split.
  { unfold q64 in *. apply (uf_bytes_munchP _ W m m' _ _ MU HW); [|exact H48].
    intros i Hi. rewrite length_le8 in Hi. intros (_ & C2 & _). apply C2. unfold spk in *. lia. }
  split; [uf_k C 25; exact H25|]. split; [uf_k C 27; exact H27|]. uf_k C 19; exact H19.
Qed.

Fixpoint uf_rd_list (mem : word -> option byte) (a : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => (match mem (Z_to_bv 64 a) with Some b => b | None => z8 end) :: uf_rd_list mem (a + 1) k'
  end.

Lemma uf_rd_list_len : forall mem k a, length (uf_rd_list mem a k) = k.
Proof. intros mem k. induction k as [|k IH]; intros a; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma uf_rd_list_nth : forall mem k a j, (j < k)%nat ->
  nth_error (uf_rd_list mem a k) j =
  Some (match mem (Z_to_bv 64 (a + Z.of_nat j)) with Some b => b | None => z8 end).
Proof.
  intros mem k. induction k as [|k IH]; intros a j Hj; [lia|].
  destruct j as [|j]; cbn [uf_rd_list nth_error].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. reflexivity.
Qed.

Lemma uf_check_str_call : check_str_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (r o c lo : Z) (str slack : list byte) (Q : machine_state -> Prop),
  ro_agree rsegs m ->
  -2^31 <= r < 2^31 -> a0 = Z_to_bv 64 r -> 0 <= o < 2^64 -> a1 = Z_to_bv 64 o ->
  0 <= c < 2^64 -> a2 = Z_to_bv 64 c ->
  (0 <= r -> check_str_ok m sp r o c str slack) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_STR_FRAME <= bv_unsigned sp -> IMG_HI <= lo ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [(bv_unsigned sp - CHECK_STR_FRAME, bv_unsigned sp)] m m' -> wmono rsegs m m' -> ro_agree rsegs m' ->
     Exec.evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  Exec.evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 CHECK_STR) fc None m (seg_rom rsegs)).
Proof.
  intros CS ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m r o c lo str slack Q Hro Hr E0 Ho E1 Hc E2 OK ST HL HI K.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_rsegs Hro).
    eapply CS with (str := str) (slack := slack) (lo := lo);
      [exact Hr | exact E0 | exact Ho | exact E1 | exact Hc | exact E2 | | | exact HL |
      apply mem_inv_normalize].
    - intros H0. destruct (OK H0) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      split; [exact Q1|]. split; [exact Q2|]. split; [apply bytes_at_normalize; assumption|].
      split; [exact Q4|]. split; [exact Q5 | exact Q6].
    - apply uf_stk_norm; assumption. }
  intros s (s0' & PO & REL & SAME).
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    -> & MU & WM & _ & _).
  destruct s as [R' F' pc' svc' rv' fc' mm ro'].
  destruct REL as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hro' & HM). cbn in HR, HF, Hpc, Hsvc, Hrv, Hfc, Hro', HM.
  cbn in SAME. subst.
  apply K.
  - exact (munch_rel rsegs _ m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME MU).
  - exact (wmono_rel rsegs m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME WM).
  - exact (ro_agree_same rsegs m mm Hro SAME).
Qed.

Lemma uf_wr_norm : forall m a n, IMG_HI <= a -> a + n <= 2 ^ 64 -> wr_at rsegs m a n ->
  wr_at rsegs (normalize rsegs m) a n.
Proof.
  intros m a n Ha Hn (H1 & H2 & H). split; [lia|]. split; [lia|]. intros i Hi.
  assert (Hro : Mem.ro_addr rsegs (wa (a + i)) = false).
  { unfold Mem.ro_addr. rewrite wa_unsigned by lia. rewrite uf_fs_none by lia. reflexivity. }
  unfold wview, normalize. rewrite Hro. apply H. exact Hi.
Qed.

Lemma uf_wr_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' ->
  wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma uf_ro_write : forall m a bs, ro_agree rsegs m -> IMG_HI <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ro_agree rsegs (write_to_mem m (wa a) bs).
Proof.
  intros m a bs H Ha Hl w Hw. pose proof (uf_ro_lt w Hw) as Hlt. unfold IMG_LO, IMG_HI in *.
  unfold mrd. rewrite write_to_mem_spec by lia.
  destruct (_ && _)%bool eqn:E; [apply andb_prop in E as [E1 _]; apply Z.leb_le in E1; lia|].
  exact (H w Hw).
Qed.

Lemma uf_put_dec_call : put_dec_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b p v mn : Z) (N : word)
         (Q : machine_state -> Prop),
    a0 = Z_to_bv 64 b -> 0 <= b -> a1 = Z_to_bv 64 p -> bv_unsigned a2 mod 2^32 = v ->
    (bv_unsigned a2 < 2^32 \/ 10 <= v) ->
    a3 = Z_to_bv 64 mn -> 0 <= mn <= 10 ->
    bytes_at rsegs m p (le8 N) -> wr_at rsegs m p 8 -> p mod 8 = 0 ->
    wr_at rsegs m (b + bv_unsigned N) (dec_len v mn) ->
    ro_agree rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PUT_DEC_FRAME <= bv_unsigned sp -> IMG_HI <= lo ->
    IMG_HI <= p -> p + 8 <= 2 ^ 64 -> IMG_HI <= b + bv_unsigned N -> b + bv_unsigned N + dec_len v mn <= 2 ^ 64 ->
    (p + 8 <= b + bv_unsigned N \/ b + bv_unsigned N + dec_len v mn <= p) ->
    (p + 8 <= bv_unsigned sp - PUT_DEC_FRAME \/ bv_unsigned sp <= p) ->
    (b + bv_unsigned N + dec_len v mn <= bv_unsigned sp - PUT_DEC_FRAME \/ bv_unsigned sp <= b + bv_unsigned N) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       munch [(bv_unsigned sp - PUT_DEC_FRAME, bv_unsigned sp); (p, p + 8);
              (b + bv_unsigned N, b + bv_unsigned N + dec_len v mn)] m m' ->
       wmono rsegs m m' -> ro_agree rsegs m' ->
       bytes_at rsegs m' (b + bv_unsigned N) (DEC v mn) ->
       bytes_at rsegs m' p (le8 (Z_to_bv 64 (bv_unsigned N + dec_len v mn))) ->
       Exec.evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    Exec.evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 PUT_DEC) fc None m (seg_rom rsegs)).
Proof.
  intros PD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo b p v mn N Q E0 Hb0 E1 E2 E2' E3 Hmn HP HWP Hp8 HWB HRO HST HLO HLT HPL HPH HBL HBH D1 D2 D3 K.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_rsegs HRO).
    eapply PD; try eassumption.
    - apply bytes_at_normalize; assumption.
    - apply uf_wr_norm; [lia | lia | exact HWP].
    - apply uf_wr_norm; [lia | lia | exact HWB].
    - apply mem_inv_normalize.
    - apply uf_stk_norm; assumption. }
  intros s (s0' & PO & REL & SAME).
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    -> & MU & WM & _ & _ & HD & HN).
  destruct s as [R' F' pc' svc' rv' fc' mm ro'].
  destruct REL as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hro' & HM). cbn in HR, HF, Hpc, Hsvc, Hrv, Hfc, Hro', HM.
  cbn in SAME. subst.
  apply K.
  - exact (munch_rel rsegs _ m _ mm m0' (mem_rel_normalize rsegs m HRO) HM SAME MU).
  - exact (wmono_rel rsegs m _ mm m0' (mem_rel_normalize rsegs m HRO) HM SAME WM).
  - exact (ro_agree_same rsegs m mm HRO SAME).
  - exact (proj2 (bytes_at_rel rsegs mm m0' _ _ HM) HD).
  - exact (proj2 (bytes_at_rel rsegs mm m0' _ _ HM) HN).
Qed.

Lemma uf_div1000 : forall v, 0 <= v < 65536 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64
    (Z.shiftl (bv_unsigned (Z_to_bv 64 v)) 48))) 51)) * 8389))) 20) = Z_to_bv 64 (v / 1000).
Proof.
  intros v Hv.
  rewrite (unsigned_lit v) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (v * 2 ^ 48)) by lia. rewrite !Z.shiftr_div_pow2 by lia.
  replace (v * 2 ^ 48 / 2 ^ 51) with (v / 8)
    by (change (2 ^ 51) with (2 ^ 48 * 8); rewrite <- Z.div_div by lia; rewrite Z.div_mul by lia; reflexivity).
  rewrite (unsigned_lit (v / 8)) by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (v / 8 * 8389)) by (Z.div_mod_to_equations; lia).
  f_equal.
  apply Z.eqb_eq.
  apply (z_all_spec (fun x => (x / 8 * 8389 / 2 ^ 20 =? x / 1000)) (Z.to_nat 65536) 0
           ltac:(vm_compute; reflexivity) v).
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma uf_dec1_len : forall h, 0 <= h < 66 -> 1 <= dec_len h 1 <= 2.
Proof.
  intros h Hh. unfold dec_len. rewrite reac_identity_fw_str_dec_h by lia.
  destruct (10 <=? h); cbn [app Datatypes.length]; lia.
Qed.

Lemma uf_dec3_len : forall f, 0 <= f < 1000 -> dec_len f 3 = 3.
Proof. intros f Hf. unfold dec_len. rewrite reac_identity_fw_str_dec_f by lia. reflexivity. Qed.

Lemma uf_mod1000 : forall v, 0 <= v < 65536 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) -
    bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (v / 1000)) * 1000))))) 65535) = Z_to_bv 64 (v mod 1000).
Proof.
  intros v Hv.
  rewrite (unsigned_lit v) by lia.
  rewrite (unsigned_lit (v / 1000)) by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (v / 1000 * 1000)) by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (v - v / 1000 * 1000)) by (Z.div_mod_to_equations; lia).
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. f_equal.
  Z.div_mod_to_equations. lia.
Qed.

Lemma uf_le1_dot : le1 (Z_to_bv 64 46) = [dot].
Proof. unfold le1, dot, RcIdentModel.zb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma uf_rd_q64 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 H) by (rewrite ?length_le8; lia).
  cbn [Z.to_nat skipn]. rewrite <- (length_le8 v) at 1. rewrite firstn_all. reflexivity.
Qed.

Ltac uf_subfp := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [outside] in *; repeat split; lia.

Section T2.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma uf_FReq_hb : forall g km hb L A regs mem md (mem' : word -> option byte),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ in_hb hb x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  FReq g mem mem'.
Proof.
  intros g km hb L A regs mem md mem' HF HP HU x Hx.
  pose proof HF as (HGV & _). pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK in *.
  unfold mbyte. rewrite HU; [reflexivity | lia |].
  intros Hh. pose proof (uf_hb_low B APIf ra empty FF g km hb L A regs mem md x HF HP Hh) as (_ & H2).
  unfold SLOT_K, SLOT_STACK in H2. lia.
Qed.

Lemma uf_FR_hb : forall g km hb L A regs mem md regs' (mem' : word -> option byte),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  KP [2; 3; 4] regs regs' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ in_hb hb x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  wmono rsegs mem mem' ->
  FR B APIf ra empty g km hb L A regs' mem' md.
Proof.
  intros g km hb L A regs mem md regs' mem' HF HP C HU HW.
  apply (uf_FR_kA B APIf ra empty FF g km hb L A regs mem md regs' mem' HF HP).
  - exact (C 2 ltac:(uf_in)).
  - exact (C 3 ltac:(uf_in)).
  - exact (C 4 ltac:(uf_in)).
  - intros x Hx Hk. apply HU; [exact Hx|]. intros Hh. apply Hk. right. exact Hh.
  - exact HW.
Qed.

Lemma uf_slack : forall L A mem md p n s, aa_MR (APIf rc) L A mem md -> In (p, n) (blocks L A) ->
  cstr mem p s -> Z.of_nat (length s) + 1 <= n ->
  exists slack, bytes_at rsegs mem p (s ++ z8 :: slack) /\
    (- (p + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
    p + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= alloc_ceiling.
Proof.
  intros L A mem md p n s HM Hin HC Hn.
  assert (HSL : block_slack_present B (APIf rc)).
  { destruct (uf_alloc B APIf ra empty FF) as (_ & _ & _ & _ & _ & H & _). exact H. }
  destruct (uf_blk_facts B APIf ra empty FF L A mem md p n 0 HM Hin ltac:(lia)) as (_ & B1 & B2 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as [AC1 AC2].
  set (x := p + Z.of_nat (length s) + 1).
  set (e := 8 * ((p + n + 7) / 8)).
  assert (He1 : p + n <= e) by (unfold e; Z.div_mod_to_equations; lia).
  assert (He2 : e <= alloc_ceiling) by (unfold e; Z.div_mod_to_equations; lia).
  assert (PR : forall a, x <= a < e -> present mem a).
  { intros a Ha. destruct (Z_lt_le_dec a (p + n)) as [Hlt|Hge].
    - replace a with (p + (a - p)) by lia.
      exact (proj1 (uf_blk_facts B APIf ra empty FF L A mem md p n (a - p) HM Hin ltac:(unfold x in Ha; lia))).
    - exact (HSL L A mem md p n a HM Hin ltac:(unfold e in Ha; lia)). }
  exists (uf_rd_list mem x (Z.to_nat (e - x))). rewrite uf_rd_list_len.
  destruct HC as (C1 & C2 & C3). rewrite length_app in C2. cbn [length] in C2.
  split; [| split; [fold x; Z.div_mod_to_equations; lia | fold x; lia]].
  split; [lia|]. split; [rewrite length_app; cbn [length]; rewrite uf_rd_list_len; lia|].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite uf_rd_list_len in Hi.
  replace (s ++ z8 :: uf_rd_list mem x (Z.to_nat (e - x))) with ((s ++ [z8]) ++ uf_rd_list mem x (Z.to_nat (e - x)))
    by (rewrite <- app_assoc; reflexivity).
  destruct (Nat.lt_ge_cases i (length s + 1)) as [Hl|Hl].
  - rewrite nth_error_app1 by (rewrite length_app; cbn [length]; lia). apply C3. rewrite length_app. cbn. lia.
  - rewrite nth_error_app2 by (rewrite length_app; cbn [length]; lia). rewrite length_app. cbn [length].
    rewrite uf_rd_list_nth by lia.
    destruct (PR (p + Z.of_nat i) ltac:(unfold x; lia)) as [b Hb].
    replace (x + Z.of_nat (i - (length s + 1))) with (p + Z.of_nat i) by (unfold x; lia).
    unfold mrd, wa. rewrite Hb. reflexivity.
Qed.

Lemma uf_stk_fsp : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  stk rsegs mem (g_S g - SLOT_K) (fsp g) /\ IMG_HI <= g_S g - SLOT_K /\ g_S g - SLOT_K + 8192 <= fsp g /\
  fsp g + 384 = g_S g /\ alloc_ceiling + SLOT_K <= g_S g /\ g_S g <= 2 ^ 47 /\ SLOT_K = 65536 /\
  getr regs 2 = Z_to_bv 64 (fsp g).
Proof.
  intros g km hb L A regs mem md HF.
  pose proof HF as (HGV & Hsp & _ & _ & _ & Hstk & _). pose proof HGV as (_ & _ & _ & _ & HSc & HS47 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC. assert (HK : SLOT_K = 65536) by reflexivity.
  unfold fsp, SLOT_FRAME, IMG_HI in *.
  split; [exact (proj1 (stk_split rsegs mem _ (g_S g - 384) _ Hstk ltac:(lia)))|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HSc|]. split; [exact HS47|]. split; [exact HK|].
  exact Hsp.
Qed.

End T2.

Fixpoint uf_ro_chk (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => Mem.ro_addr rsegs (Z_to_bv 64 a) &&
              match seg_rom rsegs (Z_to_bv 64 a) with Some b' => bv_eqb b' b | None => false end &&
              uf_ro_chk (a + 1) r
  end.

Lemma uf_ro_chk_ok : forall bs a, uf_ro_chk a bs = true -> forall i, (i < length bs)%nat ->
  Mem.ro_addr rsegs (Z_to_bv 64 (a + Z.of_nat i)) = true /\
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b r IH]; intros a H i Hi; cbn [Datatypes.length] in Hi; [lia|].
  cbn [uf_ro_chk] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct i as [|i].
  - rewrite Z.add_0_r. split; [exact H1|]. cbn [nth_error]. revert H2.
    destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b'|]; intros H2; [|discriminate H2].
    f_equal. apply bv_eq. unfold bv_eqb in H2. apply Z.eqb_eq. exact H2.
  - destruct (IH (a + 1) H3 i ltac:(lia)) as [E1 E2].
    replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. split; [exact E1 | exact E2].
Qed.

Lemma uf_ro_chk_bytes : forall m a bs, ro_agree rsegs m -> uf_ro_chk a bs = true -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at rsegs m a bs.
Proof.
  intros m a bs HR H Ha Hl. split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  destruct (uf_ro_chk_ok bs a H i Hi) as [E1 E2]. unfold wa. rewrite (HR _ E1). exact E2.
Qed.

Definition uf_rom_list (a : Z) (k : nat) : list byte :=
  map (fun i => match seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) with Some b => b | None => z8 end) (seq 0 k).

Lemma uf_rom_list_len : forall a k, length (uf_rom_list a k) = k.
Proof. intros a k. unfold uf_rom_list. rewrite length_map, length_seq. reflexivity. Qed.

Lemma uf_ro_agree_norm : forall m, ro_agree rsegs (normalize rsegs m).
Proof. intros m a H. unfold mrd, normalize. rewrite H. reflexivity. Qed.

Lemma uf_bn_cstr : forall m lo hi a s, ro_agree rsegs m ->
  uf_ro_chk a (bn_bytes s ++ Z_to_bv 8 0 ::
    uf_rom_list (a + Z.of_nat (length s) + 1) (Z.to_nat ((- (a + Z.of_nat (length s) + 1)) mod 8))) = true ->
  forallb (fun c => (0 <? c) && (c <? 256)) s = true ->
  0 <= a -> (length s <= 16)%nat -> a + 32 <= lo -> lo <= 2 ^ 64 -> bn_cstr m lo hi a s.
Proof.
  intros m lo hi a s HR HC HF Ha Hs Hlo Hlo2.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as HM.
  split.
  { apply Forall_forall. intros c Hc. rewrite forallb_forall in HF. specialize (HF c Hc).
    apply andb_prop in HF as [H1 H2]. apply Z.ltb_lt in H1, H2. lia. }
  exists (uf_rom_list (a + Z.of_nat (length s) + 1) (Z.to_nat ((- (a + Z.of_nat (length s) + 1)) mod 8))).
  split.
  { apply (uf_ro_chk_bytes m a _ HR HC Ha). rewrite length_app. cbn [Datatypes.length].
    rewrite uf_rom_list_len. unfold bn_bytes. rewrite length_map. lia. }
  rewrite uf_rom_list_len. split; [lia|].
  cbn [disjoint_from]. split; [left; lia | exact I].
Qed.

Lemma uf_bn_lit : forall m lo hi a s, ro_agree rsegs m -> uf_ro_chk a (bn_bytes (s ++ [0])) = true ->
  0 <= a -> (length s <= 16)%nat -> a + 32 <= lo -> lo <= 2 ^ 64 -> bn_lit m lo hi a s.
Proof.
  intros m lo hi a s HR HC Ha Hs Hlo Hlo2. split.
  - apply (uf_ro_chk_bytes m a _ HR HC Ha). unfold bn_bytes. rewrite length_map, length_app. cbn [Datatypes.length].
    lia.
  - cbn [disjoint_from]. split; [left; lia | exact I].
Qed.

Lemma uf_bn_image : forall m lo hi, ro_agree rsegs m ->
  bytes_at rsegs m BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3)) ->
  IMG_HI <= lo <= 2 ^ 64 -> bn_image m lo hi.
Proof.
  intros m lo hi HR HT Hlo. unfold IMG_HI in Hlo. unfold bn_image.
  split; [exact HT|].
  split; [cbn [disjoint_from]; split; [left; unfold BN_TS; lia | exact I]|].
  split; [apply uf_bn_cstr; [exact HR | vm_compute; reflexivity | vm_compute; reflexivity | unfold BN_S1; lia |
                             cbn; lia | unfold BN_S1; lia | lia]|].
  split; [apply uf_bn_cstr; [exact HR | vm_compute; reflexivity | vm_compute; reflexivity | unfold BN_S2; lia |
                             cbn; lia | unfold BN_S2; lia | lia]|].
  split; [apply uf_bn_cstr; [exact HR | vm_compute; reflexivity | vm_compute; reflexivity | unfold BN_S3; lia |
                             cbn; lia | unfold BN_S3; lia | lia]|].
  split; [apply uf_bn_cstr; [exact HR | vm_compute; reflexivity | vm_compute; reflexivity | unfold BN_REAC; lia |
                             cbn; lia | unfold BN_REAC; lia | lia]|].
  split; [apply uf_bn_lit; [exact HR | vm_compute; reflexivity | unfold BN_PAREN; lia | cbn; lia |
                            unfold BN_PAREN; lia | lia]|].
  split; [apply uf_bn_lit; [exact HR | vm_compute; reflexivity | unfold BN_IN; lia | cbn; lia |
                            unfold BN_IN; lia | lia]|].
  apply uf_bn_lit; [exact HR | vm_compute; reflexivity | unfold BN_OUT; lia | cbn; lia | unfold BN_OUT; lia | lia].
Qed.

Lemma uf_bn_accept_0 : forall f sd i o nl t tl d dl,
  bn_accept f sd i o (bv_unsigned (Z_to_bv 64 0)) nl t tl d dl = false.
Proof. intros. unfold bn_accept, bn_args_ok. reflexivity. Qed.

Lemma uf_bn_args_0 : forall nl t tl d dl i o, bn_args_ok (bv_unsigned (Z_to_bv 64 0)) nl t tl d dl i o = false.
Proof. intros. unfold bn_args_ok. reflexivity. Qed.

Lemma uf_said : forall h a, 0 <= h < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (PropExec.v_sltiu (Z_to_bv 64 h) 1) + -1)))
    (bv_unsigned (Z_to_bv 64 a))) = Z_to_bv 64 (if h =? 0 then 0 else a).
Proof.
  intros h a Hh Ha. unfold PropExec.v_sltiu. rewrite (unsigned_lit h) by lia. change (bv_wrap 64 1) with 1.
  rewrite (unsigned_lit a) by lia.
  destruct (Z.ltb_spec h 1) as [H|H].
  - assert (h = 0) by lia. subst h. rewrite Z.eqb_refl.
    assert (E : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) + -1)) = 0) by (vm_compute; reflexivity).
    rewrite E, Z.land_0_l. reflexivity.
  - destruct (Z.eqb_spec h 0) as [E0|E0]; [lia|].
    assert (E : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1)) = Z.ones 64) by (vm_compute; reflexivity).
    rewrite E, Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma uf_box_name_call : reac_box_name_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo f i o : Z) (display display_len : word)
         (sd : list Z) (Q : machine_state -> Prop),
    ro_agree rsegs m ->
    a0 = Z_to_bv 64 f -> -2^31 <= f < 2^31 ->
    a2 = Z_to_bv 64 i -> -2^31 <= i < 2^31 ->
    a3 = Z_to_bv 64 o -> -2^31 <= o < 2^31 ->
    bytes_at rsegs m (bv_unsigned sp) (le8 display ++ le8 display_len) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BN_K <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 -> IMG_HI <= lo ->
    bytes_at rsegs m BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3)) ->
    (bn_args_ok (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                (bv_unsigned display) (bv_unsigned display_len) i o = true ->
       bn_said (normalize rsegs m) (bv_unsigned sp - BN_K) (bv_unsigned sp) (bv_unsigned a1) sd /\
       bn_bufs (normalize rsegs m) (bv_unsigned sp - BN_K) (bv_unsigned sp) (bv_unsigned a4) (bv_unsigned a5)
               (bv_unsigned a6) (bv_unsigned a7) (bv_unsigned display) (bv_unsigned display_len)) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       wmono rsegs m m' -> ro_agree rsegs m' ->
       (if bn_accept f sd i o (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                     (bv_unsigned display) (bv_unsigned display_len)
        then a0' = Z_to_bv 64 0 /\
             munch [(bv_unsigned sp - BN_K, bv_unsigned sp);
                    (bv_unsigned a4, bv_unsigned a4 + Z.of_nat (length (bn_NM f sd i o)) + 1);
                    (bv_unsigned a6, bv_unsigned a6 + Z.of_nat (length (bn_TK (bn_NM f sd i o))) + 1);
                    (bv_unsigned display,
                     bv_unsigned display + Z.of_nat (length (bn_DP (bn_NM f sd i o) i o)) + 1)] m m' /\
             bytes_at rsegs m' (bv_unsigned a4) (bn_bytes (bn_NM f sd i o ++ [0])) /\
             bytes_at rsegs m' (bv_unsigned a6) (bn_bytes (bn_TK (bn_NM f sd i o) ++ [0])) /\
             bytes_at rsegs m' (bv_unsigned display) (bn_bytes (bn_DP (bn_NM f sd i o) i o ++ [0]))
        else a0' = Z_to_bv 64 (-1) /\ munch [(bv_unsigned sp - BN_K, bv_unsigned sp)] m m') ->
       Exec.evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
    Exec.evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 REAC_BOX_NAME) fc None m (seg_rom rsegs)).
Proof.
  intros BN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo f i o display display_len sd Q HRO E0 Hf E2 Hi E3 Ho HD ST HL Hal HLO HT ARGS K.
  pose proof (bv_unsigned_in_range 64 sp) as Hsp. unfold bv_modulus in Hsp.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_rsegs HRO).
    eapply BN; [exact E0 | exact Hf | exact E2 | exact Hi | exact E3 | exact Ho | | | exact HL | exact Hal | | exact ARGS |
                apply mem_inv_normalize].
    - apply bytes_at_normalize; assumption.
    - apply uf_stk_norm; assumption.
    - apply uf_bn_image; [apply uf_ro_agree_norm | apply bytes_at_normalize; assumption |].
      unfold BN_K in *. lia. }
  intros s (s0' & PO & REL & SAME).
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    -> & WM & _ & _ & HIF).
  destruct s as [R' F' pc' svc' rv' fc' mm ro'].
  destruct REL as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hro' & HM). cbn in HR, HF, Hpc, Hsvc, Hrv, Hfc, Hro', HM.
  cbn in SAME. subst.
  pose proof (mem_rel_normalize rsegs m HRO) as MR0.
  apply K.
  - exact (wmono_rel rsegs m _ mm m0' MR0 HM SAME WM).
  - exact (ro_agree_same rsegs m mm HRO SAME).
  - revert HIF.
    destruct (bn_accept f sd i o (bv_unsigned a4) (bv_unsigned a5) (bv_unsigned a6) (bv_unsigned a7)
                        (bv_unsigned display) (bv_unsigned display_len)); intros HIF.
    + destruct HIF as (E0' & MU & B1 & B2 & B3).
      split; [exact E0'|]. split; [exact (munch_rel rsegs _ m _ mm m0' MR0 HM SAME MU)|].
      split; [exact (proj2 (bytes_at_rel rsegs mm m0' _ _ HM) B1)|].
      split; [exact (proj2 (bytes_at_rel rsegs mm m0' _ _ HM) B2)|].
      exact (proj2 (bytes_at_rel rsegs mm m0' _ _ HM) B3).
    + destruct HIF as (E0' & MU).
      split; [exact E0' | exact (munch_rel rsegs _ m _ mm m0' MR0 HM SAME MU)].
Qed.

Lemma uf_FAM_range : forall idb, 0 <= FAM idb <= 3.
Proof.
  intros idb. unfold FAM, lib.Prog.reac_box_family_of_c.FAMOF_FAM.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma uf_nfam_range : forall inp, 0 <= n_fam inp <= 127.
Proof.
  intros inp. unfold n_fam. destruct (128 <=? t_fam_raw inp).
  - pose proof (inb_range inp (cT inp + 0)) as R.
    replace (Z.land (t_fam_raw inp) 127) with (t_fam_raw inp mod 128)
      by (change 127 with (Z.ones 7); rewrite Z.land_ones by lia; reflexivity).
    pose proof (Z.mod_pos_bound (t_fam_raw inp) 128 ltac:(lia)). lia.
  - pose proof (uf_FAM_range (idT inp)). lia.
Qed.

Fixpoint uf_rel_chk (a : Z) (bs : list byte) : bool :=
  match bs with
  | [] => true
  | b :: r => match seg_rom rsegs (Z_to_bv 64 a) with Some b' => bv_eqb b' b | None => false end &&
              uf_rel_chk (a + 1) r
  end.

Lemma uf_rel_chk_ok : forall bs a, uf_rel_chk a bs = true -> forall i, (i < length bs)%nat ->
  seg_rom rsegs (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  induction bs as [|b r IH]; intros a H i Hi; cbn [Datatypes.length] in Hi; [lia|].
  cbn [uf_rel_chk] in H. apply andb_prop in H as [H2 H3].
  destruct i as [|i].
  - rewrite Z.add_0_r. cbn [nth_error]. revert H2.
    destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b'|]; intros H2; [|discriminate H2].
    f_equal. apply bv_eq. unfold bv_eqb in H2. apply Z.eqb_eq. exact H2.
  - replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. exact (IH (a + 1) H3 i ltac:(lia)).
Qed.

Lemma uf_bn_ts_chk : uf_rel_chk BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3))
  = true.
Proof. vm_compute. reflexivity. Qed.

Section T3.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.

Lemma uf_bn_ts : forall mem, relro B mem ->
  bytes_at rsegs mem BN_TS (le8 (Z_to_bv 64 BN_S1) ++ le8 (Z_to_bv 64 BN_S2) ++ le8 (Z_to_bv 64 BN_S3)).
Proof.
  intros mem Hr. split; [unfold BN_TS; lia|].
  split; [rewrite !length_app, !length_le8; unfold BN_TS; lia|].
  intros i Hi. rewrite !length_app, !length_le8 in Hi.
  assert (Hg : in_globals frame_RELRO (BN_TS + Z.of_nat i)).
  { exists 0x1e3c8, 3440. split; [left; reflexivity | unfold BN_TS; lia]. }
  pose proof (Hr _ Hg) as E. rewrite (uf_segs B APIf ra empty FF) in E.
  transitivity (mbyte rsegs mem (BN_TS + Z.of_nat i)); [reflexivity|]. rewrite E.
  apply (uf_rel_chk_ok _ BN_TS uf_bn_ts_chk). rewrite !length_app, !length_le8. lia.
Qed.

End T3.

Lemma uf_famof_call : U.Prog.reac_box_family_of_c.reac_box_family_of_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo a : Z) (idb : list byte) (Q : machine_state -> Prop),
  ro_agree rsegs m -> a0 = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> IMG_HI <= lo ->
  (a = 0 \/ (bytes_at rsegs m a idb /\ length idb = 38%nat /\ a mod 2 = 0 /\
             (a + 38 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= a))) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' -> wmono rsegs m m' -> ro_agree rsegs m' ->
     Exec.evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                          (Z_to_bv 64 (lib.Prog.reac_box_family_of_c.FAMOF_FAM a idb)) a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  Exec.evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 U.Prog.reac_box_family_of_c.REAC_BOX_FAMILY_OF) fc None m
                       (seg_rom rsegs)).
Proof.
  intros FO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo a idb Q Hro E0 Ha ST HL HI ARG K.
  subst a0.
  eapply evt_cut.
  { eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) wx_apart_rsegs Hro).
    eapply FO with (lo := lo) (idb := idb);
      [apply uf_stk_norm; assumption | unfold U.Prog.reac_box_family_of_c.REAC_BOX_FAMILY_OF_FRAME; lia |
       apply mem_inv_normalize |].
    rewrite unsigned_lit by exact Ha. destruct ARG as [A0|(B1 & B2 & B3 & B4)]; [left; exact A0|right].
    split; [apply bytes_at_normalize; assumption|]. split; [exact B2|]. split; [exact B3|].
    unfold U.Prog.reac_box_family_of_c.REAC_BOX_FAMILY_OF_FRAME. exact B4. }
  intros s (s0' & PO & REL & SAME).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    -> & MU & WM & _ & _).
  destruct s as [R' F' pc' svc' rv' fc' mm ro'].
  destruct REL as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hro' & HM). cbn in HR, HF, Hpc, Hsvc, Hrv, Hfc, Hro', HM.
  cbn in SAME. subst.
  rewrite unsigned_lit by exact Ha.
  unfold U.Prog.reac_box_family_of_c.REAC_BOX_FAMILY_OF_FRAME in MU.
  apply K.
  - exact (munch_rel rsegs _ m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME MU).
  - exact (wmono_rel rsegs m _ mm m0' (mem_rel_normalize rsegs m Hro) HM SAME WM).
  - exact (ro_agree_same rsegs m mm Hro SAME).
Qed.

Lemma uf_nowrite0 : forall (mem mem' m' : word -> option byte),
  mem_rel rsegs mem' m' -> ro_same rsegs mem mem' -> munch [] (normalize rsegs mem) m' -> forall w, mem' w = mem w.
Proof.
  intros mem mem' m' Hr Hs Hm w. destruct (Mem.ro_addr rsegs w) eqn:E.
  - exact (Hs w E).
  - rewrite <- (mem_rel_rw rsegs mem' m' w Hr E). rewrite (Hm w I). unfold normalize. rewrite E. reflexivity.
Qed.

Lemma uf_bveq_nz : forall v, -2 ^ 63 <= v < 2 ^ 63 -> v <> 0 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv H. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.eqb_neq.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small 0) by lia.
  destruct (Z_lt_le_dec v 0); [rewrite Z.mod_eq by lia; Z.div_mod_to_equations; lia | rewrite Z.mod_small; lia].
Qed.
