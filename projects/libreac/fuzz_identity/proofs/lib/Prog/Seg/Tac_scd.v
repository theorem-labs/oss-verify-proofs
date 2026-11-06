From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame Image.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP URzKP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_family_of_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require MState Exec.
Import ListNotations.
Open Scope Z_scope.

Lemma sc_outside1 : forall lo hi x, outside [(lo, hi)] x <-> ~ (lo <= x < hi).
Proof. intros lo hi x. cbn. tauto. Qed.

Lemma sc_munch_widen : forall lo hi lo' hi' m m',
  munch [(lo, hi)] m m' -> lo' <= lo -> hi <= hi' -> munch [(lo', hi')] m m'.
Proof.
  intros lo hi lo' hi' m m' H H1 H2 x Hx. apply H. apply sc_outside1.
  apply sc_outside1 in Hx. lia.
Qed.

Lemma sc_munch_nil : forall W m m', munch [] m m' -> munch W m m'.
Proof. intros W m m' H x _. apply H. exact I. Qed.

Lemma sc_munch_trans : forall W m1 m2 m3, munch W m1 m2 -> munch W m2 m3 -> munch W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

Lemma sc_mbyte_eq : forall segs (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte segs m' a = mbyte segs m a.
Proof. intros segs m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.

Lemma sc_wr_eq : forall segs (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at segs m a <-> writable_at segs m' a).
Proof. intros segs m m' a H. unfold writable_at, wview. rewrite H. tauto. Qed.

Lemma sc_ba_keep : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i))) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). unfold mrd, wa. rewrite (Hk (Z.of_nat i)) by lia. reflexivity.
Qed.

Lemma sc_ba_munch : forall segs W m m' a bs, bytes_at segs m a bs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> outside W (a + i)) -> bytes_at segs m' a bs.
Proof.
  intros segs W m m' a bs H HM HO. pose proof (bytes_at_bound segs m a bs H) as HB.
  apply (sc_ba_keep segs m); [exact H|]. intros i Hi. apply HM.
  rewrite MState.unsigned_lit by lia. apply HO. exact Hi.
Qed.

Lemma sc_img_bytes : forall m a bs, ro_agree rsegs m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  ro_bytes_b rsegs a bs = true -> bytes_at rsegs m a bs.
Proof.
  intros m a bs Hra Ha Hl Hb. pose proof (ro_bytes_b_sound rsegs bs a Hb) as H.
  split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
  destruct (nth_error bs i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  destruct (ro_bytes_nth rsegs bs a i b H E) as [H1 H2]. rewrite (Hra _ H2). exact H1.
Qed.

Lemma sc_ovr : forall m a bs, bytes_at rsegs m a bs ->
  ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof (bytes_at_ov_read rsegs m a bs 0 (length bs) H ltac:(lia)) as E.
  change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E. cbn [skipn] in E. rewrite firstn_all in E. exact E.
Qed.

Lemma sc_le8_len : forall v : word, length (le8 v) = 8%nat.
Proof. intros v. apply length_le8. Qed.

Lemma sc_q64_ovr : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof. intros m a v H. unfold q64 in H. pose proof (sc_ovr m a _ H) as E. rewrite sc_le8_len in E. exact E. Qed.

Lemma sc_ba_above : forall segs m m' lo hi a bs, bytes_at segs m a bs -> munch [(lo, hi)] m m' -> hi <= a ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' lo hi a bs H HM Ha. apply (sc_ba_munch segs [(lo, hi)] m m' a bs H HM).
  intros i Hi. apply sc_outside1. lia.
Qed.

Lemma sc_back : forall mem m0 mem' W, ro_agree rsegs mem ->
  munch W (normalize rsegs mem) m0 -> wmono rsegs (normalize rsegs mem) m0 ->
  mem_rel rsegs mem' m0 -> ro_same rsegs mem mem' ->
  munch W mem mem' /\ wmono rsegs mem mem'.
Proof.
  intros mem m0 mem' W Hro HM HW HR Hs. pose proof (mem_rel_normalize rsegs mem Hro) as HN. split.
  - exact (munch_rel rsegs W mem (normalize rsegs mem) mem' m0 HN HR Hs HM).
  - exact (wmono_rel rsegs mem (normalize rsegs mem) mem' m0 HN HR Hs HW).
Qed.

Lemma sc_famof_nz : forall id idb, id <> 0 ->
  reac_box_family_of_c.FAMOF_FAM id idb = reac_box_family_of_c.FAMOF_FAM 1 idb.
Proof. intros id idb H. unfold reac_box_family_of_c.FAMOF_FAM. destruct (Z.eqb_spec id 0); [contradiction | reflexivity]. Qed.

Lemma sc_CB_mem : forall g regs m m' lo hi, CB g regs m -> munch [(lo, hi)] m m' -> hi <= fsp g -> CB g regs m'.
Proof.
  intros g regs m m' lo hi (H1 & H2 & H3 & (W1 & W2 & W3) & H5 & H6) HM Hh.
  unfold CB, HWb, NRb, G16, q64, u32, IDb, spk in *.
  split; [exact H1|]. split; [apply (sc_ba_above _ m m' lo hi); [exact H2 | exact HM | lia]|].
  split; [apply (sc_ba_above _ m m' lo hi); [exact H3 | exact HM | lia]|].
  split; [split; [|split]|split; [exact H5|]]; apply (sc_ba_above _ m m' lo hi); try lia; assumption.
Qed.

Lemma sc_CB_regs : forall g regs regs' m, CB g regs m ->
  getr regs' 20 = getr regs 20 -> getr regs' 26 = getr regs 26 -> CB g regs' m.
Proof.
  intros g regs regs' m (H1 & H2 & H3 & H4 & (C1 & C2 & C3) & H6) E20 E26.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [|exact H6].
  split; [exact C1|]. rewrite E20, E26. split; assumption.
Qed.

Lemma sc_rec_hwb_len : forall inp i, length (rec_hwb inp i) = 8%nat.
Proof.
  intros inp i.
  assert (H : match rec_hw inp i with Some h => length h = 8%nat | None => True end).
  { induction i as [|i IH]; cbn [rec_hw]; [exact I|].
    destruct ((rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? rec_k inp i)) eqn:E; [|exact IH].
    apply andb_true_iff in E as [_ E]. apply Z.leb_le in E.
    rewrite length_firstn, rec_pl_length. lia. }
  unfold rec_hwb. destruct (rec_hw inp i); [exact H | reflexivity].
Qed.

Section TacScd.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma sc_segs : ms_segs B = rsegs.
Proof using FF. destruct FF as [H _]. exact H. Qed.

Lemma sc_img : img_low B.
Proof using FF.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite sc_segs. vm_compute. reflexivity.
  - pose proof alloc_ceiling_val. lia.
Qed.

Lemma sc_seg_low : forall x seg, find_segment rsegs x 1 = Some seg -> 0 <= x < alloc_ceiling.
Proof using FF. intros x seg H. destruct sc_img as [_ HI]. rewrite sc_segs in HI. exact (HI x seg H). Qed.

Lemma sc_img_low : forall a, in_img B a -> 0 <= a < alloc_ceiling.
Proof using FF. intros a H. destruct sc_img as [HI _]. exact (HI a H). Qed.

Lemma sc_ro_low : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < alloc_ceiling.
Proof using FF.
  intros a H. unfold ro_addr in H. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  exact (proj2 (sc_seg_low _ seg E)).
Qed.

Lemma sc_hi_noseg : forall a : word, alloc_ceiling <= bv_unsigned a -> find_segment rsegs (bv_unsigned a) 1 = None.
Proof using FF.
  intros a H. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  pose proof (sc_seg_low _ seg E). lia.
Qed.

Lemma sc_stk_norm : forall m lo hi, stk rsegs m lo hi -> alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  stk rsegs (normalize rsegs m) lo hi.
Proof using FF.
  intros m lo hi (H1 & H2 & H) Hl Hh. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (Hr : ro_addr rsegs (wa a) = false).
  { destruct (ro_addr rsegs (wa a)) eqn:E; [|reflexivity]. pose proof (sc_ro_low _ E) as X.
    unfold wa in X. rewrite MState.unsigned_lit in X by lia. lia. }
  destruct (H a Ha) as (Hw & b & Hb). unfold wview, mrd, normalize in *. rewrite Hr. split; [exact Hw|]. exists b. exact Hb.
Qed.

Lemma sc_FR_regs : forall g km hb L A regs regs' mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  FR B APIf ra empty g km hb L A regs' mem md.
Proof.
  intros g km hb L A regs regs' mem md (H1 & H2 & H3 & H4 & H) E2 E3 E4.
  split; [exact H1|]. rewrite E2, E3, E4. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. exact H.
Qed.

Lemma sc_FR_frame : forall g km hb L A regs mem md mem',
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  munch [(g_S g - SLOT_K, g_S g - 104)] mem mem' ->
  wmono rsegs mem mem' ->
  FR B APIf ra empty g km hb L A regs mem' md.
Proof using FF.
  intros g km hb L A regs mem md mem' HF HP HM HW.
  pose proof sc_segs as ES.
  pose proof FF as (_ & _ & _ & _ & _ & _ & HERR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTP & HEO & _ &
                    HOH & HOL & HTH & _ & _ & _ & _ & HRL & _).
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn & Hp & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  pose proof alloc_ceiling_val as Hc. pose proof (HERR rc) as Herrc.
  unfold FR. unfold SLOT_K, SLOT_STACK in *.
  assert (Hout : forall a, 0 <= a < 2 ^ 64 -> a < g_S g - 65536 \/ g_S g - 104 <= a ->
                 mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hx. apply HM. rewrite MState.unsigned_lit by exact Ha. apply sc_outside1. lia. }
  assert (Hlow : forall a, 0 <= a < alloc_ceiling -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a))
    by (intros a Ha; apply Hout; lia).
  assert (HE0 : 0 <= errno_addr B) by (unfold errno_addr; rewrite HTP, HEO; lia).
  split; [exact HGV|]. split; [exact Hsp|]. split; [exact Hgp|]. split; [exact Htp|].
  split.
  { apply (sc_ba_keep rsegs mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. apply Hout; lia. }
  split.
  { destruct Hstk as (S1 & S2 & SH0). split; [exact S1|]. split; [exact S2|]. intros a Ha.
    destruct (SH0 a Ha) as (Hw & _).
    assert (Hu : bv_unsigned (wa a) = a) by (unfold wa; apply MState.unsigned_lit; lia).
    pose proof (HW (wa a) Hw) as Hw'. split; [exact Hw'|].
    assert (Hns : find_segment rsegs (bv_unsigned (wa a)) 1 = None) by (apply sc_hi_noseg; lia).
    unfold wview in Hw'. rewrite Hns in Hw'. unfold mrd.
    destruct (mem' (wa a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw'; reflexivity]. }
  split.
  { unfold MI in *. intros a Ha. rewrite <- (HMI a Ha). unfold mrd.
    pose proof Ha as Ha'. rewrite ES in Ha'.
    pose proof (sc_ro_low a Ha') as X. pose proof (bv_unsigned_in_range 64 a) as R.
    change (bv_modulus 64) with (2 ^ 64) in R.
    rewrite (HM a); [reflexivity|]. apply sc_outside1. lia. }
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (HRL a Ha) as (Hi & _). pose proof (sc_img_low a Hi). apply sc_mbyte_eq. apply Hlow. lia. }
  assert (Hcond : forall x, 0 <= x < alloc_ceiling ->
      (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
      outside [(g_S g - 65536, g_S g - 104)] x) by (intros x Hx _; apply sc_outside1; lia).
  split; [exact (kb_MR_A B (APIf rc) L A mem mem' md _ HMR HM Hcond)|].
  split; [exact HWF|]. split; [exact Hbd|]. split; [exact Hin|]. split; [exact Hmd|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [E1 E2].
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply Hout; lia).
    rewrite (sc_mbyte_eq _ mem mem' a Hx). split; [exact E1|].
    rewrite E2. apply sc_wr_eq. exact Hx. }
  split.
  { intros a Ha H1 H2 H3. destruct (Himg a Ha H1 H2 H3) as [E1 E2]. pose proof (sc_img_low a Ha).
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) by (apply Hlow; lia).
    rewrite (sc_mbyte_eq _ mem mem' a Hx). split; [exact E1|].
    rewrite E2. apply sc_wr_eq. exact Hx. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi).
    apply (kb_blocks_munch B (APIf rc) L A mem mem' md _ HMR HM Hcond a k i); [|exact Hi].
    apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hak. }
  split.
  { intros a Ha. apply (sc_wr_eq _ mem mem' a); [apply Hlow; lia | exact (Herr a Ha)]. }
  split.
  { unfold sink_none, closed_stdio_env in *. destruct Hsink as ((V1 & V2) & V3 & V4).
    split; [split|]; [| |split; [|exact V4]].
    - intros k Hk. rewrite <- (V1 k Hk). apply sc_mbyte_eq. apply Hlow. rewrite HTH. lia.
    - intros k Hk. rewrite <- (V2 k Hk). apply sc_mbyte_eq. apply Hlow. rewrite HOL. lia.
    - intros k Hk. rewrite <- (V3 k Hk). apply sc_mbyte_eq. apply Hlow. rewrite HOH. lia. }
  split; [exact HRES|].
  intros a Ha. pose proof (Hwr a Ha) as X. unfold writable_at in *. rewrite ES in X |- *. apply HW. exact X.
Qed.

Lemma sc_after_call : forall g km hb L A regs mem md mem' F,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  munch [(fsp g - F, fsp g)] mem mem' -> wmono rsegs mem mem' -> 0 <= F <= 16000 ->
  FR B APIf ra empty g km hb L A regs mem' md.
Proof using FF.
  intros g km hb L A regs mem md mem' F HF HP HM HW HFr.
  apply (sc_FR_frame g km hb L A regs mem md mem' HF HP); [|exact HW].
  apply (sc_munch_widen _ _ _ _ _ _ HM); unfold fsp, SLOT_FRAME, SLOT_K, SLOT_STACK; lia.
Qed.

Lemma sc_fr_facts : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  ro_agree rsegs mem /\ stk rsegs (normalize rsegs mem) (g_S g - 65536) (fsp g) /\
  bv_unsigned (Z_to_bv 64 (fsp g)) = fsp g /\ alloc_ceiling + 65536 <= g_S g /\ g_S g <= 2 ^ 47 /\
  fsp g = g_S g - 368 /\ getr regs 2 = Z_to_bv 64 (fsp g).
Proof using FF.
  intros g km hb L A regs mem md HF.
  destruct HF as (HGV & Hsp & _ & _ & _ & Hstk & HMI & _).
  pose proof HGV as (_ & _ & _ & _ & HSK & HS47 & _).
  pose proof alloc_ceiling_val as Hc.
  unfold SLOT_K, SLOT_STACK in *.
  assert (Ef : fsp g = g_S g - 368) by (unfold fsp, SLOT_FRAME; lia).
  split; [unfold MI in HMI; rewrite sc_segs in HMI; exact HMI|].
  split.
  { apply sc_stk_norm; [|lia|lia]. destruct (stk_split rsegs mem _ (fsp g) _ Hstk) as [H _]; [lia|exact H]. }
  split; [apply MState.unsigned_lit; lia|].
  split; [lia|]. split; [lia|]. split; [exact Ef|exact Hsp].
Qed.

Lemma sc_blk_range : forall L A mem md p n, aa_MR (APIf rc) L A mem md -> In (p, n) (blocks L A) ->
  4096 <= p /\ p + n <= alloc_ceiling.
Proof.
  intros L A mem md p n HM Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q k] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst p k.
  exact (mr_blocks_range _ _ (aa_laws (APIf rc)) L A mem md q n HM Hq).
Qed.

Lemma sc_input : forall g km hb L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  bytes_at rsegs mem (g_p g) (g_in g) /\ 0 <= g_p g /\ g_p g + g_n g <= alloc_ceiling.
Proof using FF.
  intros g km hb L A regs mem md HF HP.
  pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & _ & _ & HEM & _).
  destruct HF as (HGV & _ & _ & _ & _ & _ & _ & _ & HMR & _ & _ & _ & _ & _ & _ & Hblk & _).
  pose proof HGV as (Hn & Hp & Hbd & _).
  pose proof alloc_ceiling_val as Hc.
  destruct Hp as [(Hn0 & Hpe) | (Hnp & Hin)].
  - assert (Hnil : g_in g = []) by (unfold g_n, nlen in Hn0; destruct (g_in g); [reflexivity | cbn in Hn0; lia]).
    rewrite Hnil, Hn0, Hpe, HEM.
    split; [|lia].
    split; [lia|]. split; [cbn [length]; lia | intros i Hi; cbn [length] in Hi; exfalso; lia].
  - assert (HinL : In (g_p g, g_n g) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
    destruct (sc_blk_range L A mem md _ _ HMR HinL) as [R1 R2].
    split; [|lia].
    split; [lia|]. split; [unfold g_n, nlen in R2; lia|].
    intros i Hi. unfold blk_data in Hbd.
    assert (Hi' : 0 <= Z.of_nat i < g_n g) by (unfold g_n, nlen; lia).
    pose proof (Hblk _ _ (Z.of_nat i) Hin Hi') as E. pose proof (Hbd (Z.of_nat i) ltac:(unfold g_n, nlen in Hi'; lia)) as E'.
    rewrite Nat2Z.id in E'. rewrite <- E', <- E. rewrite sc_segs. reflexivity.
Qed.

Lemma sc_cut : forall g pc km hb (P : bvmap 5 word -> (word -> option byte) -> Prop) L A regs mem md,
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  P regs mem ->
  CUTST B APIf ra empty g pc km hb P (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs B))) md).
Proof. intros. exists L, A, regs, mem, md. split; [reflexivity|]. split; [assumption|]. split; assumption. Qed.

Lemma sc_run : forall regs pc mem md L A (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  aa_MR (APIf rc) L A mem md ->
  Exec.evt rsegs (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
      K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     Rz (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof using FF.
  intros regs pc mem md L A K P HM HE HK.
  destruct (kb_md B (APIf rc) L A mem md HM) as [Hh Hz].
  apply (kb_run_rz B regs pc mem md K P Hh Hz); [rewrite sc_segs; exact HE | exact HK].
Qed.

Lemma sc_run_norm : forall regs pc mem md L A (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) P,
  aa_MR (APIf rc) L A mem md -> ro_agree rsegs mem ->
  Exec.evt rsegs (fun ms => exists R pc' m0, ms = MState.MS R fp_regs pc' fp_csr None m0 (seg_rom rsegs) /\
      forall mem', mem_rel rsegs mem' m0 -> ro_same rsegs mem mem' -> K R pc' mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' mem' regs', K R pc' mem' -> (forall r, getr regs' r = getr R r) ->
     Rz (ms_segs B) (mkCfg (mkst regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  Rz (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof using FF.
  intros regs pc mem md L A K P HM Hro HE HK.
  apply (sc_run regs pc mem md L A K P HM); [|exact HK].
  eapply Exec.evt_mono; [exact (evt_normalize rsegs _ _ _ _ _ _ _ _ wx_apart_rsegs Hro HE)|].
  intros s (s0 & (R & pc' & m0 & E & HQ) & Hrel & Hsame). subst s0.
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  exists R, pc', (ms_mem s). split.
  - destruct s. cbn in *. subst. reflexivity.
  - apply HQ; assumption.
Qed.

End TacScd.
