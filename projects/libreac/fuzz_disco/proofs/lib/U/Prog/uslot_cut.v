From Stdlib Require Import ZArith List Bool Lia Permutation.
From Stdlib Require Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Reusable Require YN0d YH02 YI04.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0 Contract FrameAPI KindBGlue AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require MState Mem Frame Exec Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_norm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import SlotAgree AgreeLift.
Import ListNotations.
Open Scope Z_scope.

Fixpoint hb_bytes (hb : list (Z * Z)) : Z :=
  match hb with [] => 0 | x :: l => snd x + hb_bytes l end.

Definition sb_hb (b0 : sbound) (hb : list (Z * Z)) : sbound :=
  SB (sb_live b0 + Z.of_nat (length hb)) (sb_bytes b0 + hb_bytes hb) (sb_cap b0).

Lemma sb_hb_nil : forall b0, sb_hb b0 [] = b0.
Proof. intros [l y c]. unfold sb_hb. cbn. f_equal; lia. Qed.

Lemma sb_hb_cons : forall b0 x hb, sb_hb b0 (x :: hb) = sb_malloc (sb_hb b0 hb) (snd x).
Proof. intros [l y c] [a n] hb. unfold sb_hb, sb_malloc. cbn [length hb_bytes sb_live sb_bytes sb_cap snd]. f_equal; lia. Qed.

Lemma sb_hb_free : forall b0 x hb, sb_free (sb_hb b0 (x :: hb)) (snd x) = sb_hb b0 hb.
Proof. intros b0 x hb. rewrite sb_hb_cons. apply sb_free_malloc. Qed.

Lemma in_img_lo : forall B a, ms_segs B = rsegs -> in_img B a -> IMG_LO <= a < IMG_HI.
Proof.
  intros B a HS H. apply (YN0d.in_img_img1 a). unfold in_img in *. rewrite HS in H. exact H.
Qed.

Lemma in_img_hi : forall B a, ms_segs B = rsegs -> IMG_LO <= a < IMG_HI -> in_img B a.
Proof.
  intros B a HS H. pose proof (YN0d.in_img1_img a H) as H'. unfold in_img in *. rewrite HS. exact H'.
Qed.

Lemma blocks_in : forall L A p n, In (p, n) (user_blocks A) -> In (ptr_addr L p, n) (blocks L A).
Proof. intros L A p n H. unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact H]. Qed.

Lemma in_blocks : forall L A a n, In (a, n) (blocks L A) -> exists p, In (p, n) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a n H. unfold blocks in H. apply in_map_iff in H as ([p n'] & E & Hp).
  cbn in E. injection E as E1 E2. subst. exists p. split; [exact Hp | reflexivity].
Qed.

Lemma pairwise_perm : forall {X} (R : X -> X -> Prop), (forall x y, R x y -> R y x) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros X R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - cbn in H |- *. destruct H as [H1 H2]. split; [|exact (IH H2)].
    intros y Hy. apply H1. apply (Permutation_in y (Permutation_sym HP) Hy).
  - cbn in H |- *. destruct H as [H1 [H2 H3]].
    split; [intros z [<-|Hz]; [apply Hs, H1; left; reflexivity | apply H2, Hz]|].
    split; [intros z Hz; apply H1; right; exact Hz | exact H3].
  - exact (IH2 (IH1 H)).
Qed.

Lemma pairwise_app : forall {X} (R : X -> X -> Prop) l1 l2 x y, pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y H Hx Hy; [destruct Hx|].
  cbn in H. destruct H as [H1 H2]. destruct Hx as [<-|Hx].
  - apply H1. apply in_or_app. right. exact Hy.
  - exact (IH l2 x y H2 Hx Hy).
Qed.

Section Cut.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables (K S : Z) (L0 : layout) (A0 : astate) (mem0 : word -> option byte) (md0 : Model) (b0 : sbound).
Hypothesis HSEGS : ms_segs B = rsegs.
Hypothesis HAX : AllocExtra B (aa_MR API).
Hypothesis HKS : alloc_ceiling + K <= S.
Hypothesis HK : 0 <= K.
Hypothesis HS : S <= 2 ^ 47.
Hypothesis HTHR : @sk_threaded SK = 0x51cb0 + 1.
Hypothesis HLOCK : @sk_ofl_lock SK = 0x520d8.
Hypothesis HHEAD : @sk_ofl_head SH = 0x520e0.
Hypothesis HFA : forall fx : FPState, @frame_allocator rc fx B API.
Hypothesis HMAL : ms_malloc B = 0x17aec.
Hypothesis HFRE : ms_free B = 0x179ac.
Hypothesis HLK : ms_lock B = 0x51d20.
Hypothesis HLIBC : ms_libc B = 0x51cb0.
Hypothesis HGG : ms_got_guard B = 0x206a0.
Hypothesis HGD : ms_guard B = 0x51c90.
Hypothesis HCTX : ms_ctx B = 0x51d28.
Hypothesis HTP : ms_tp B = 0x31a20.
Hypothesis HERR : ms_errno_off B = -164.
Hypothesis HVML : ms_vmlock B = None.
Hypothesis HDBL : ms_debruijn_len B = 32.
Hypothesis HDB : ms_debruijn B = 0x10600.
Hypothesis HSC : ms_size_classes B = 0x10620.
Hypothesis HSMC : ms_small_cnt B = 0x10680.
Hypothesis HMDC : ms_med_cnt B = 0x1069b.
Hypothesis MCF : forall fx : FPState, @malloc_contract_cf fx rc B API.
Hypothesis FCF : forall fx : FPState, @free_contract_cf fx rc B API.
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).
Let MR := aa_MR API.

Definition slot_fr (hb : list (Z * Z)) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  slot_sofar B API K S L0 A0 mem0 md0 L A mem md /\ MemNorm.ro_agree rsegs mem /\
  Permutation (blocks L A) (hb ++ blocks L0 A0) /\ res_ok_slots A (sb_hb b0 hb).

Definition slot_cut (pc : Z) (hb : list (Z * Z)) (P : bvmap 5 word -> (word -> option byte) -> Prop) (c : config) : Prop :=
  exists (fx' : FPState) L A regs mem md m0,
    c = mkCfg (@mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md /\ frm_zero (@fp_csr fx') /\
    slot_fr hb L A mem md /\ MemNorm.mem_rel_cj rsegs mem m0 /\ P regs m0.

Definition W_ok (hb : list (Z * Z)) (W : list (Z * Z)) : Prop :=
  forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> (S - K <= x < S) \/ exists a n, In (a, n) hb /\ a <= x < a + n.

Lemma ceil_hi : IMG_HI < alloc_ceiling.
Proof. pose proof alloc_ceiling_val. unfold IMG_HI. lia. Qed.

Lemma fr_outside : forall hb W x, W_ok hb W -> 0 <= x < alloc_ceiling ->
  (forall a n, In (a, n) hb -> a <= x < a + n -> False) -> Frame.outside W x.
Proof.
  intros hb W x HW Hx Hn.
  destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|].
  exfalso. pose proof alloc_ceiling_lt. destruct (HW x ltac:(lia) Ho) as [Hs|(a & n & Hin & Ha)]; [lia|].
  exact (Hn a n Hin Ha).
Qed.

Lemma hb_block : forall hb L A a n, Permutation (blocks L A) (hb ++ blocks L0 A0) -> In (a, n) hb ->
  exists p, In (p, n) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros hb L A a n HP Hin. apply in_blocks. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
Qed.

Lemma hb_not_owned : forall hb L A mem md a n x, MR L A mem md -> Permutation (blocks L A) (hb ++ blocks L0 A0) ->
  In (a, n) hb -> a <= x < a + n -> ~ owned B L A x /\ ~ in_img B x /\ 4096 <= a /\ a + n <= alloc_ceiling.
Proof.
  intros hb L A mem md a n x HM HP Hin Hx.
  destruct (hb_block hb L A a n HP Hin) as (p & Hp & <-).
  destruct (mr_blocks _ _ (aa_laws API) L A mem md p n (x - ptr_addr L p) HM Hp ltac:(lia)) as (_ & H1 & H2 & H3).
  replace (ptr_addr L p + (x - ptr_addr L p)) with x in H3 by lia.
  split; [exact H3|]. split; [|lia].
  pose proof (ax_blocks_img HAX L A mem md p n (x - ptr_addr L p) HM Hp ltac:(lia)) as H4.
  replace (ptr_addr L p + (x - ptr_addr L p)) with x in H4 by lia. exact H4.
Qed.

Lemma seg_in_range : forall s a, In s rsegs -> Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s) ->
  IMG_LO <= a < IMG_HI.
Proof.
  intros s a Hin Ha. pose proof rsegs_range as R. rewrite forallb_forall in R. specialize (R s Hin).
  apply andb_prop in R as [R1 R2]. apply Z.leb_le in R1. apply Z.leb_le in R2. lia.
Qed.

Lemma hb_disj : forall hb L A mem md a n q k x, MR L A mem md -> Permutation (blocks L A) (hb ++ blocks L0 A0) ->
  In (a, n) hb -> In (q, k) (blocks L0 A0) -> a <= x < a + n -> q <= x < q + k -> False.
Proof.
  intros hb L A mem md a n q k x HM HP Ha Hq Hx1 Hx2.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L A mem md HM) as D.
  apply (pairwise_perm ranges_disjoint) with (l' := hb ++ blocks L0 A0) in D;
    [| intros [u v] [u' v'] H; unfold ranges_disjoint in *; cbn in *; lia | exact HP].
  pose proof (pairwise_app ranges_disjoint hb (blocks L0 A0) (a, n) (q, k) D Ha Hq) as E.
  unfold ranges_disjoint in E. cbn in E. lia.
Qed.

Lemma FR_write : forall hb L A mem mem' md W,
  slot_fr hb L A mem md -> W_ok hb W -> Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' ->
  MemNorm.ro_agree rsegs mem' -> slot_fr hb L A mem' md.
Proof.
  intros hb L A mem mem' md W (SO & RO & HP & HR) HW MU WM RO'.
  destruct SO as (HM & HWF & HB & HID & HVM & HHI & HIMG & HBLK & HSTK & HSINK & HROD).
  pose proof alloc_ceiling_lt as Hc. pose proof ceil_hi as Hch.
  assert (UNCH : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx Ho. apply MU. rewrite MState.unsigned_lit by lia. exact Ho. }
  assert (MB : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x ->
            mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
            (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx Ho. unfold mbyte, writable_at, wview. rewrite (UNCH x Hx Ho). tauto. }
  assert (IMGO : forall x, in_img B x -> Frame.outside W x).
  { intros x Hx. pose proof (in_img_lo B x HSEGS Hx) as Hr. unfold IMG_LO, IMG_HI in Hr.
    apply (fr_outside hb W x HW); [unfold IMG_HI in Hch; lia|].
    intros a n Hin Ha. destruct (hb_not_owned hb L A mem md a n x HM HP Hin Ha) as (_ & H & _). exact (H Hx). }
  assert (IMGR : forall x, IMG_LO <= x < IMG_HI -> Frame.outside W x).
  { intros x Hx. apply IMGO. exact (in_img_hi B x HSEGS Hx). }
  split; [|split; [exact RO'|split; [exact HP|exact HR]]].
  split.
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    apply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
      apply MB; [lia|]. apply (fr_outside hb W a HW); [lia|].
      intros a' n' Hin Ha. destruct (hb_not_owned hb L A mem md a' n' a HM HP Hin Ha) as (Hno & _). exact (Hno Ho).
    - intros a Ho (b & Hb). pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
      exists b. rewrite UNCH; [exact Hb | lia |]. apply (fr_outside hb W a HW); [lia|].
      intros a' n' Hin Ha. destruct (hb_not_owned hb L A mem md a' n' a HM HP Hin Ha) as (Hno & _). exact (Hno Ho).
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as ((b & Hb) & H1 & H2 & _).
      destruct (kb_outside_dec W (ptr_addr L p + i)) as [Ho|Ho].
      + exists b. rewrite UNCH; [exact Hb | lia | exact Ho].
      + pose proof (ax_blocks_img HAX L A mem md p n i HM Hin Hi) as NI.
        assert (NS : nseg (bv_unsigned (Z_to_bv 64 (ptr_addr L p + i)))).
        { rewrite MState.unsigned_lit by lia. unfold nseg.
          destruct (Z_lt_le_dec (ptr_addr L p + i) IMG_LO); [left; exact l|].
          destruct (Z_lt_le_dec (ptr_addr L p + i) IMG_HI); [|right; exact l0].
          exfalso. apply NI. apply (in_img_hi B _ HSEGS). lia. }
        assert (WV : wview rsegs mem (Z_to_bv 64 (ptr_addr L p + i)) <> None) by (unfold wview; rewrite Hb; discriminate).
        pose proof (WM _ WV) as WV'. rewrite (wview_nseg mem' _ NS) in WV'.
        destruct (mem' (Z_to_bv 64 (ptr_addr L p + i))) as [b'|] eqn:E; [exists b'; exact E | contradiction].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HWF|]. split; [exact HB|]. split; [exact HID|]. split; [exact HVM|].
  split.
  { intros a Ha Hs He. destruct (HHI a Ha Hs He) as [E1 E2]. pose proof alloc_ceiling_val as Hcv.
    assert (Ho : Frame.outside W a).
    { destruct (kb_outside_dec W a) as [Ho|Ho]; [exact Ho|]. exfalso.
      destruct (HW a ltac:(lia) Ho) as [Hs'|(a' & n' & Hin & Ha')]; [exact (Hs Hs')|].
      destruct (hb_not_owned hb L A mem md a' n' a HM HP Hin Ha') as (_ & _ & _ & H). lia. }
    destruct (MB a ltac:(lia) Ho) as [M1 M2]. rewrite M1. split; [exact E1 | tauto]. }
  split.
  { intros a Ha H1 H2 H3. destruct (HIMG a Ha H1 H2 H3) as [E1 E2].
    pose proof (in_img_lo B a HSEGS Ha) as Hr. unfold IMG_LO, IMG_HI in Hr.
    destruct (MB a ltac:(lia) (IMGO a Ha)) as [M1 M2]. rewrite M1. split; [exact E1 | tauto]. }
  split.
  { intros q k i Hq Hi. rewrite <- (HBLK q k i Hq Hi).
    assert (Hq' : In (ptr_addr L0 q, k) (blocks L A)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply blocks_in. exact Hq. }
    destruct (in_blocks L A _ _ Hq') as (p & Hp & Ep).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p k i HM Hp Hi) as (_ & H1 & H2 & _). rewrite Ep in H1, H2.
    apply MB; [lia|]. apply (fr_outside hb W _ HW); [lia|].
    intros a n Hin Ha. apply (hb_disj hb L A mem md a n (ptr_addr L0 q) k (ptr_addr L0 q + i) HM HP Hin); [|exact Ha|lia].
    apply blocks_in. exact Hq. }
  split.
  { intros a Ha. pose proof (HSTK a Ha) as Hw. unfold writable_at in *. rewrite HSEGS in *. exact (WM _ Hw). }
  split.
  { destruct HSINK as ((T1 & T2) & W1 & F1). split; [split|split; [|exact F1]].
    - intros k0 Hk. rewrite (proj1 (MB (@sk_threaded SK + Z.of_nat k0) ltac:(rewrite HTHR; lia)
        (IMGR (@sk_threaded SK + Z.of_nat k0) ltac:(rewrite HTHR; unfold IMG_LO, IMG_HI; lia)))).
      apply T1. exact Hk.
    - intros k0 Hk. rewrite (proj1 (MB (@sk_ofl_lock SK + Z.of_nat k0) ltac:(rewrite HLOCK; lia)
        (IMGR (@sk_ofl_lock SK + Z.of_nat k0) ltac:(rewrite HLOCK; unfold IMG_LO, IMG_HI; lia)))).
      apply T2. exact Hk.
    - intros k0 Hk. rewrite (proj1 (MB (@sk_ofl_head SH + Z.of_nat k0) ltac:(rewrite HHEAD; lia)
        (IMGR (@sk_ofl_head SH + Z.of_nat k0) ltac:(rewrite HHEAD; unfold IMG_LO, IMG_HI; lia)))).
      apply W1. exact Hk. }
  { intros a ((s & Hs & Hw & Ha) & Hns). rewrite <- (HROD a).
    - rewrite HSEGS in Hs. pose proof (seg_in_range s a Hs Ha) as Hr. unfold IMG_LO, IMG_HI in Hr.
      apply MB; [lia|]. apply IMGR. unfold IMG_LO, IMG_HI. lia.
    - split; [exists s; split; [exact Hs | split; assumption] | exact Hns]. }
Qed.

Definition cut_post (hb : list (Z * Z)) (Q : bvmap 5 word -> word -> bvmap 5 word -> bv 32 -> (word -> option byte) -> Prop)
    (c' : config) : Prop :=
  exists (fx'' : FPState) L A regs' mem' md m0' R pc',
    c' = mkCfg (@mkst fx'' regs' pc' mem' (seg_rom rsegs)) md /\ frm_zero (@fp_csr fx'') /\
    slot_fr hb L A mem' md /\ MemNorm.mem_rel_cj rsegs mem' m0' /\
    (forall r, getr regs' r = getr R r) /\ Q R pc' (@fp_regs fx'') (@fp_csr fx'') m0'.

Lemma cut_run : forall pc hb P W (Q : bvmap 5 word -> word -> bvmap 5 word -> bv 32 -> (word -> option byte) -> Prop) c,
  slot_cut pc hb P c -> W_ok hb W ->
  (forall (fx' : FPState) regs m0, frm_zero (@fp_csr fx') -> MemNorm.mem_inv_cj rsegs m0 -> P regs m0 ->
     Exec.evt rsegs (fun ms => exists R F' pc' fc' m0', ms = MState.MS R F' pc' fc' None m0' (seg_rom rsegs) /\
                      frm_zero fc' /\ Frame.munch W m0 m0' /\ Frame.wmono rsegs m0 m0' /\ Q R pc' F' fc' m0')
       (MState.MS (rmk regs) (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None m0 (seg_rom rsegs))) ->
  SR rsegs c (cut_post hb Q).
Proof.
  intros pc hb P W Q c (fx' & L & A & regs & mem & md & m0 & -> & Hfrm & HFR & HREL & HP) HW HEV.
  pose proof (HEV fx' regs m0 Hfrm (mem_inv_cj_rel mem m0 HREL) HP) as E0.
  pose proof (MemNorm.evt_rel_MS_cj rsegs _ (rmk regs) (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None mem m0
    (seg_rom rsegs) wx_apart_rsegs HREL E0) as E1.
  pose proof HFR as (HSO & HRO & HPM & HRES).
  pose proof HSO as (HM & _).
  destruct (kb_md B API L A mem md HM) as [Hh Hl].
  eapply (evt_SR_canon rsegs (@mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) _ md); [exact E1 | exact Hh | exact Hl |].
  intros ms' (can & (s0 & (R & F' & pc' & fc' & m0' & Es0 & Hfc & MU & WM & HQ) & Hrel & Hsame) & Heqv).
  subst s0.
  destruct Hrel as (Er & Ef & Epc & Esv & Ers & Efc & Erom & Emem).
  destruct Heqv as (Rq & Fq & Pq & Sq & RSq & FCq & Mq & ROq).
  destruct can as [cr cf cpc csv crs cfc cm cro]. destruct ms' as [r' f' p' sv' rs' fc'' m' ro'].
  cbn in Er, Ef, Epc, Esv, Ers, Efc, Erom, Emem, Rq, Fq, Pq, Sq, RSq, FCq, Mq, ROq, Hsame.
  subst cr cf cpc csv crs cfc cro. subst f' p' sv' rs' fc'' ro' cm.
  apply SR_ret.
  exists (mkFP F' fc'), L, A, r', m', md, m0', R, pc'.
  split; [reflexivity|]. split; [exact Hfc|].
  split.
  { apply (FR_write hb L A mem m' md W HFR HW).
    - exact (MemNorm.munch_rel_cj rsegs W mem m0 m' m0' HREL Emem Hsame MU).
    - exact (MemNorm.wmono_rel_cj rsegs mem m0 m' m0' HREL Emem Hsame WM).
    - exact (MemNorm.ro_agree_same_cj rsegs mem m' HRO Hsame). }
  split; [exact Emem|]. split; [exact (kb_getr_eqv R r' Rq)|]. exact HQ.
Qed.

Lemma vm_vm : forall a b m, with_vmmaps a (with_vmmaps b m) = with_vmmaps a m.
Proof. intros a b [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma fds_vm : forall a m, m_fds (with_vmmaps a m) = m_fds m.
Proof. intros a [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma rsegs_wr : forallb (fun s => if seg_writable s then 0x20000 <=? Z.of_N (seg_base s)
  else Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x20000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ro_img_addr : forall s a, In s rsegs -> seg_writable s = false ->
  Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> Mem.ro_addr rsegs (Z_to_bv 64 a) = true.
Proof.
  intros s a Hin Hw Ha. pose proof (seg_in_range s a Hin Ha) as Hr. unfold IMG_LO, IMG_HI in Hr.
  unfold Mem.ro_addr. rewrite MState.unsigned_lit by lia.
  destruct (find_segment rsegs a 1) as [s'|] eqn:E.
  - destruct (kb_find_segment rsegs a 1 s' E) as (Hin' & H1 & H2).
    pose proof rsegs_wr as R. rewrite forallb_forall in R.
    pose proof (R s Hin) as R1. pose proof (R s' Hin') as R2. rewrite Hw in R1.
    destruct (seg_writable s'); [|reflexivity].
    apply Z.leb_le in R1. apply Z.leb_le in R2. lia.
  - exfalso. exact (MemNorm.find_segment_some rsegs s a 1 Hin ltac:(lia) ltac:(lia) E).
Qed.

Lemma rodata_of_ro : forall mem, MemNorm.ro_agree rsegs mem -> rodata_ok B mem.
Proof.
  intros mem H a ((s & Hs & Hw & Ha) & _). rewrite HSEGS in *.
  exact (H (Z_to_bv 64 a) (ro_img_addr s a Hs Hw Ha)).
Qed.

Definition sink_at (a : Z) : Prop := a = 0x51cb1 \/ 0x520d8 <= a < 0x520e8.

Lemma sink_img : forall a, sink_at a -> in_img B a.
Proof. intros a H. apply (in_img_hi B a HSEGS). unfold sink_at, IMG_LO, IMG_HI in *. lia. Qed.

Lemma sink_unowned : forall L A mem md a, MR L A mem md -> sink_at a -> ~ owned B L A a.
Proof.
  intros L A mem md a HM H [Ho|Ho].
  - pose proof (ax_img HAX L A mem md a HM (sink_img a H) Ho) as E. rewrite HCTX in E.
    unfold CTX_SIZE, sink_at in *. lia.
  - revert Ho. unfold static_owned, vml_lo, vml_len. rewrite HLK, HLIBC, HGG, HGD, HDB, HSC, HSMC, HMDC, HVML, HDBL.
    cbv beta iota. unfold sink_at in H. lia.
Qed.

Lemma sink_keep : forall mem mem' md md', sink_none B mem md ->
  (forall a, sink_at a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  m_fds md' = m_fds md -> sink_none B mem' md'.
Proof.
  intros mem mem' md md' ((T1 & T2) & W1 & F1) H Hf. split; [split|split].
  - intros k Hk. rewrite H by (unfold sink_at; rewrite HTHR; lia). apply T1. exact Hk.
  - intros k Hk. rewrite H by (unfold sink_at; rewrite HLOCK; lia). apply T2. exact Hk.
  - intros k Hk. rewrite H by (unfold sink_at; rewrite HHEAD; lia). apply W1. exact Hk.
  - unfold sink_path in *. rewrite Hf. exact F1.
Qed.

Lemma stk_sp : forall regs X, getr regs 2 = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> spZ regs = X.
Proof. intros regs X H HX. unfold spZ. rewrite H. apply MState.unsigned_lit. exact HX. Qed.

Lemma nseg_high : forall a, alloc_ceiling <= a -> nseg a.
Proof. intros a H. pose proof ceil_hi. right. lia. Qed.

Lemma nseg_blk : forall a, 0 <= a -> ~ in_img B a -> nseg a.
Proof.
  intros a Ha H. unfold nseg. destruct (Z_lt_le_dec a IMG_LO); [left; exact l|].
  destruct (Z_lt_le_dec a IMG_HI); [|right; exact l0]. exfalso. apply H. apply (in_img_hi B a HSEGS). lia.
Qed.

Lemma raw_of_mbyte : forall m m' a, nseg a -> 0 <= a < 2 ^ 64 ->
  mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m m' a Hn Ha H. unfold mbyte in H. rewrite HSEGS in H.
  assert (E : seg_rom rsegs (Z_to_bv 64 a) = None).
  { apply MemNorm.seg_rom_unmapped. rewrite MState.unsigned_lit by lia. exact (nseg_find a Hn). }
  rewrite E in H. destruct (m' (Z_to_bv 64 a)), (m (Z_to_bv 64 a)); congruence.
Qed.

Lemma blocks_perm_add : forall hb L A L' A' res n b1 b2,
  Permutation (blocks L A) (hb ++ blocks L0 A0) ->
  blocks L' A' = b1 ++ (res, n) :: b2 -> blocks L A = b1 ++ b2 ->
  Permutation (blocks L' A') (((res, n) :: hb) ++ blocks L0 A0).
Proof.
  intros hb L A L' A' res n b1 b2 HP E1 E2. rewrite E1. cbn [app].
  apply (Permutation_trans (Permutation_sym (Permutation_middle b1 b2 (res, n)))).
  apply perm_skip. rewrite <- E2. exact HP.
Qed.

Lemma blocks_perm_del : forall hb L A L' A' a n b1 b2,
  Permutation (blocks L A) (((a, n) :: hb) ++ blocks L0 A0) ->
  blocks L A = b1 ++ (a, n) :: b2 -> blocks L' A' = b1 ++ b2 ->
  Permutation (blocks L' A') (hb ++ blocks L0 A0).
Proof.
  intros hb L A L' A' a n b1 b2 HP E1 E2. rewrite E2. rewrite E1 in HP. cbn [app] in HP.
  apply (Permutation_cons_inv (a := (a, n))).
  apply (Permutation_trans (Permutation_middle b1 b2 (a, n))). exact HP.
Qed.

Definition malloc_post (hb : list (Z * Z)) (P : bvmap 5 word -> (word -> option byte) -> Prop) (n X : Z) (c' : config) : Prop :=
  exists (fx'' : FPState) L' A' regs regs' mem' md' m0 m0' res,
    c' = mkCfg (@mkst fx'' regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\ frm_zero (@fp_csr fx'') /\
    P regs m0 /\ slot_fr ((res, n) :: hb) L' A' mem' md' /\ MemNorm.mem_rel_cj rsegs mem' m0' /\
    regs_preserved regs regs' /\ getr regs' 10 = Z_to_bv 64 res /\
    4096 <= res /\ res mod 16 = 0 /\ res + n <= alloc_ceiling /\ (forall i, 0 <= i < n -> ~ in_img B (res + i)) /\
    (exists bs, Step.rw_cells rsegs m0' res [Cells.CB (Z.to_nat n) bs]) /\
    agree m0 m0' X (S - X) /\ (forall a k, In (a, k) (hb ++ blocks L0 A0) -> agree m0 m0' a k).

Lemma cut_malloc : forall hb P n X c,
  slot_cut 0x17aec hb P c ->
  (forall regs m0, P regs m0 -> YK0s.ret_ok (getr regs 1) /\ getr regs 10 = Z_to_bv 64 n /\
     getr regs 2 = Z_to_bv 64 X /\ getr regs 4 = Z_to_bv 64 (ms_tp B)) ->
  X mod 16 = 0 -> S - K + ALLOC_STACK <= X <= S -> 0 <= n -> room_slots (sb_hb b0 hb) n ->
  SR rsegs c (malloc_post hb P n X).
Proof.
  intros hb P n X c (fx' & L & A & regs & mem & md & m0 & -> & Hfrm & HFR & HREL & HP) HPR HX16 HXr Hn0 Hroom.
  destruct (HPR regs m0 HP) as (Hra & H10 & H2 & H4).
  pose proof HFR as (HSO & HRO & HPM & HRES).
  pose proof HSO as (HM & HWF & HB & HID & (vm & HVMd) & HHI & HIMG & HBLK & HSTK & HSINK & HROD).
  pose proof alloc_ceiling_val as Hcv. pose proof alloc_ceiling_lt as Hcl. unfold ALLOC_STACK in HXr.
  assert (Hsp : spZ regs = X) by (apply stk_sp; [exact H2 | lia]).
  destruct (HFA fx') as (MAL & _).
  assert (PRE : call_pre B (aa_MR API) L A regs mem md).
  { unfold call_pre. rewrite Hsp. split; [exact HM|]. split; [exact HWF|]. split; [exact HB|].
    split; [exact Hra|]. split; [exact HX16|]. split; [unfold ALLOC_STACK; lia|]. split; [lia|].
    split; [intros a Ha; apply HSTK; left; unfold ALLOC_STACK in Ha; lia|].
    split; [exact H4|]. split; [intros a Ha; apply HSTK; right; exact Ha|].
    intros E. rewrite HID in E. discriminate. }
  pose proof (MAL L A regs mem md n (sb_hb b0 hb) PRE ltac:(rewrite HSEGS; exact HRO) H10 HRES Hroom) as E.
  rewrite HSEGS, HMAL in E. eapply SR_mono; [exact E|].
  intros c' (L' & A' & regs' & mem' & md' & res & -> & CP & R10 & Rnz & R16 & (F1 & F2 & F3) &
             (b1 & b2 & EB1 & EB2) & BK & RO' & GK & UB & ID' & RG & RES').
  rewrite HSEGS in RO'.
  destruct CP as (MR' & WF' & B' & LLE & PADDR & RP & (vm' & EMD) & HIGH & UBK & SCR).
  unfold scratch_k in HIGH, SCR. rewrite Hsp in HIGH, SCR.
  assert (HOW : forall a, owned B L A a -> a < alloc_ceiling)
    by (intros a Ho; exact (proj2 (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho))).
  assert (HOW' : forall a, owned B L' A' a -> a < alloc_ceiling)
    by (intros a Ho; exact (proj2 (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ MR' Ho))).
  assert (HIMGU : forall L1 A1 mem1 md1 a, aa_MR API L1 A1 mem1 md1 -> in_img B a -> ~ static_owned B a ->
            ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ owned B L1 A1 a).
  { intros L1 A1 mem1 md1 a HM1 Ha Hs Hc [Ho|Ho]; [exact (Hc (ax_img HAX L1 A1 mem1 md1 a HM1 Ha Ho)) | exact (Hs Ho)]. }
  assert (KEEPH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (X - 8192 <= a < X) ->
            mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
            (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hs. apply HIGH; [left; lia | intros Ho; pose proof (HOW a Ho); lia |
      intros Ho; pose proof (HOW' a Ho); lia | | tauto].
    intros [Hs'|He]; [unfold ALLOC_STACK in Hs'; lia|]. unfold errno_addr in He. rewrite HTP, HERR in He. lia. }
  assert (BR : forall a k, In (a, k) (hb ++ blocks L0 A0) -> 4096 <= a /\ a + k <= alloc_ceiling).
  { intros a k Hin. destruct (in_blocks L A a k (Permutation_in _ (Permutation_sym HPM) Hin)) as (p & Hp & Ep).
    subst a. exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HM Hp). }
  assert (KEEPB : forall a k i, In (a, k) (hb ++ blocks L0 A0) -> 0 <= i < k ->
            mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i) /\ ~ in_img B (a + i)).
  { intros a k i Hin Hi.
    destruct (in_blocks L A a k (Permutation_in _ (Permutation_sym HPM) Hin)) as (p & Hp & Ep).
    pose proof (ax_blocks_img HAX L A mem md p k i HM Hp Hi) as NI. subst a.
    split; [exact (UBK p k i Hp (UB p k Hp) Hi) | exact NI]. }
  exists fx', L', A', regs, regs', mem', md', m0, (MemNorm.normalize_cj rsegs mem'), res.
  split; [rewrite HSEGS; reflexivity|]. split; [exact Hfrm|]. split; [exact HP|].
  assert (REL' : MemNorm.mem_rel_cj rsegs mem' (MemNorm.normalize_cj rsegs mem'))
    by exact (MemNorm.mem_rel_cj_normalize rsegs mem' RO').
  split.
  { split; [|split; [exact RO'|split; [exact (blocks_perm_add hb L A L' A' res n b1 b2 HPM EB1 EB2)|]]].
    2: { rewrite sb_hb_cons. exact RES'. }
    split; [exact MR'|]. split; [exact WF'|]. split; [exact B'|]. split; [exact ID'|].
    split; [exists vm'; rewrite EMD, HVMd; apply vm_vm|].
    split.
    { intros a Ha Hs He. destruct (HHI a Ha Hs He) as [E1 E2].
      destruct (HIGH a ltac:(left; lia) ltac:(intros Ho; pose proof (HOW a Ho); lia)
                  ltac:(intros Ho; pose proof (HOW' a Ho); lia) ltac:(intros [Hs'|He']; [apply Hs; unfold ALLOC_STACK in Hs'; lia | exact (He He')])
                  ltac:(tauto)) as [M1 M2].
      rewrite M1. split; [exact E1 | tauto]. }
    split.
    { intros a Ha Hs Hc He. destruct (HIMG a Ha Hs Hc He) as [E1 E2].
      pose proof (in_img_lo B a HSEGS Ha) as Hr. pose proof ceil_hi.
      destruct (HIGH a ltac:(right; exact Ha) (HIMGU L A mem md a HM Ha Hs Hc) (HIMGU L' A' mem' md' a MR' Ha Hs Hc)
                  ltac:(intros [Hs'|He']; [unfold ALLOC_STACK in Hs'; lia | exact (He He')]) ltac:(tauto)) as [M1 M2].
      rewrite M1. split; [exact E1 | tauto]. }
    split.
    { intros q k i Hq Hi. rewrite <- (HBLK q k i Hq Hi).
      apply (proj1 (KEEPB (ptr_addr L0 q) k i ltac:(apply in_or_app; right; apply blocks_in; exact Hq) Hi)). }
    split.
    { intros a Ha. destruct Ha as [Ha|Ha]; [|apply SCR; right; exact Ha].
      destruct (Z_lt_le_dec a (X - 8192)) as [Hl|Hl].
      - apply (proj2 (KEEPH a ltac:(lia) ltac:(lia))). apply HSTK. left. exact Ha.
      - destruct (Z_lt_le_dec a X) as [Hl2|Hl2]; [apply SCR; left; unfold ALLOC_STACK; lia|].
        apply (proj2 (KEEPH a ltac:(lia) ltac:(lia))). apply HSTK. left. exact Ha. }
    split.
    { apply (sink_keep mem mem' md md' HSINK); [|rewrite EMD; apply fds_vm].
      intros a Ha. pose proof (sink_img a Ha) as HI.
      destruct (HIGH a ltac:(right; exact HI) (sink_unowned L A mem md a HM Ha) (sink_unowned L' A' mem' md' a MR' Ha)
                  ltac:(intros [Hs'|He']; [unfold sink_at, ALLOC_STACK in *; lia | unfold errno_addr, sink_at in *; rewrite HTP, HERR in He'; lia])
                  ltac:(tauto)) as [M1 _].
      exact M1. }
    exact (rodata_of_ro mem' RO'). }
  split; [exact REL'|]. split; [exact RP|]. split; [exact R10|].
  split; [exact F1|]. split; [exact R16|]. split; [exact F2|]. split; [exact F3|].
  split.
  { destruct (in_blocks L' A' res n ltac:(rewrite EB1; apply in_or_app; right; left; reflexivity)) as (q & Hq & Eq).
    apply rwc_present; [lia | lia | exact Hn0 |].
    intros i Hi. split; [apply nseg_blk; [lia | exact (F3 i Hi)]|].
    rewrite (norm_nseg mem' _ (res + i) REL') by (try (apply nseg_blk; [lia | exact (F3 i Hi)]); unfold TASK_SIZE; lia).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i MR' Hq Hi) as ((bb & Hbb) & _). rewrite Eq in Hbb.
    unfold Mem.wa. rewrite Hbb. discriminate. }
  split.
  { apply (agree_rel mem m0 mem' _ X (S - X) HREL REL'); [lia | unfold TASK_SIZE; lia | intros a Ha; apply nseg_high; lia|].
    intros i Hi. unfold Mem.wa. apply (raw_of_mbyte mem mem' (X + i)); [apply nseg_high; lia | lia |].
    exact (proj1 (KEEPH (X + i) ltac:(lia) ltac:(lia))). }
  intros a k Hin. destruct (BR a k Hin) as [Ba Bb].
  apply (agree_rel mem m0 mem' _ a k HREL REL'); [lia | unfold TASK_SIZE; lia | |].
  - intros x Hx. apply nseg_blk; [lia|]. replace x with (a + (x - a)) by lia.
    exact (proj2 (KEEPB a k (x - a) Hin ltac:(lia))).
  - intros i Hi. unfold Mem.wa. apply (raw_of_mbyte mem mem' (a + i));
      [apply nseg_blk; [lia | exact (proj2 (KEEPB a k i Hin Hi))] | lia | exact (proj1 (KEEPB a k i Hin Hi))].
Qed.

Definition free_post (hb : list (Z * Z)) (P : bvmap 5 word -> (word -> option byte) -> Prop) (X : Z) (c' : config) : Prop :=
  exists (fx'' : FPState) L' A' regs regs' mem' md' m0 m0',
    c' = mkCfg (@mkst fx'' regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\ frm_zero (@fp_csr fx'') /\
    P regs m0 /\ slot_fr hb L' A' mem' md' /\ MemNorm.mem_rel_cj rsegs mem' m0' /\
    regs_preserved regs regs' /\
    agree m0 m0' X (S - X) /\ (forall a k, In (a, k) (hb ++ blocks L0 A0) -> agree m0 m0' a k).

Lemma cut_free : forall a n hb P X c,
  slot_cut 0x179ac ((a, n) :: hb) P c ->
  (forall regs m0, P regs m0 -> YK0s.ret_ok (getr regs 1) /\ getr regs 10 = Z_to_bv 64 a /\
     getr regs 2 = Z_to_bv 64 X /\ getr regs 4 = Z_to_bv 64 (ms_tp B)) ->
  X mod 16 = 0 -> S - K + ALLOC_STACK <= X <= S ->
  SR rsegs c (free_post hb P X).
Proof.
  intros a n hb P X c (fx' & L & A & regs & mem & md & m0 & -> & Hfrm & HFR & HREL & HP) HPR HX16 HXr.
  destruct (HPR regs m0 HP) as (Hra & H10 & H2 & H4).
  pose proof HFR as (HSO & HRO & HPM & HRES).
  pose proof HSO as (HM & HWF & HB & HID & (vm & HVMd) & HHI & HIMG & HBLK & HSTK & HSINK & HROD).
  pose proof alloc_ceiling_val as Hcv. pose proof alloc_ceiling_lt as Hcl. unfold ALLOC_STACK in HXr.
  assert (Hsp : spZ regs = X) by (apply stk_sp; [exact H2 | lia]).
  destruct (HFA fx') as (_ & FRE & _ & _ & _ & _ & _ & _ & BND & _).
  destruct (hb_block ((a, n) :: hb) L A a n HPM ltac:(left; reflexivity)) as (p & Hp & Ep).
  assert (PRE : call_pre B (aa_MR API) L A regs mem md).
  { unfold call_pre. rewrite Hsp. split; [exact HM|]. split; [exact HWF|]. split; [exact HB|].
    split; [exact Hra|]. split; [exact HX16|]. split; [unfold ALLOC_STACK; lia|]. split; [lia|].
    split; [intros a' Ha; apply HSTK; left; unfold ALLOC_STACK in Ha; lia|].
    split; [exact H4|]. split; [intros a' Ha; apply HSTK; right; exact Ha|].
    intros E. rewrite HID in E. discriminate. }
  pose proof (FRE L A regs mem md p n (sb_hb b0 ((a, n) :: hb)) PRE ltac:(rewrite HSEGS; exact HRO) Hp
    ltac:(rewrite Ep; exact H10) HRES) as E.
  rewrite HSEGS, HFRE in E. eapply SR_mono; [exact E|].
  intros c' (L' & A' & regs' & mem' & md' & -> & CP & (b1 & b2 & EB1 & EB2) & BK & RO' & GK & UB & ID' & RG & RES').
  try rewrite HSEGS in RO'. rewrite Ep in EB1, CP.
  apply call_post_k_alloc in CP.
  destruct CP as (MR' & WF' & B' & LLE & PADDR & RP & (vm' & EMD) & HIGH & UBK & SCR).
  unfold scratch in HIGH, SCR. rewrite Hsp in HIGH, SCR.
  pose proof (hb_not_owned ((a, n) :: hb) L A mem md a n) as HBA.
  assert (HOW : forall a', owned B L A a' -> a' < alloc_ceiling)
    by (intros a' Ho; exact (proj2 (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho))).
  assert (HOW' : forall a', owned B L' A' a' -> a' < alloc_ceiling)
    by (intros a' Ho; exact (proj2 (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ MR' Ho))).
  assert (HIMGU : forall L1 A1 mem1 md1 a', aa_MR API L1 A1 mem1 md1 -> in_img B a' -> ~ static_owned B a' ->
            ~ (ms_ctx B <= a' < ms_ctx B + CTX_SIZE) -> ~ owned B L1 A1 a').
  { intros L1 A1 mem1 md1 a' HM1 Ha Hs Hc [Ho|Ho]; [exact (Hc (ax_img HAX L1 A1 mem1 md1 a' HM1 Ha Ho)) | exact (Hs Ho)]. }
  assert (HAR : 4096 <= a /\ a + n <= alloc_ceiling) by (rewrite <- Ep; exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp)).
  assert (EIMG : forall a', a <= a' < a + n -> ~ in_img B a').
  { intros a' Ha. destruct (HBA a' HM HPM ltac:(left; reflexivity) Ha) as (_ & H & _). exact H. }
  assert (KEEPH : forall a', alloc_ceiling <= a' < 2 ^ 64 -> ~ (X - 8192 <= a' < X) ->
            mbyte (ms_segs B) mem' a' = mbyte (ms_segs B) mem a' /\
            (writable_at (ms_segs B) mem a' <-> writable_at (ms_segs B) mem' a')).
  { intros a' Ha Hs. apply HIGH; [left; lia | intros Ho; pose proof (HOW a' Ho); lia |
      intros Ho; pose proof (HOW' a' Ho); lia | | lia].
    intros [Hs'|He]; [unfold ALLOC_STACK in Hs'; lia|]. unfold errno_addr in He. rewrite HTP, HERR in He. lia. }
  assert (BR : forall a' k, In (a', k) (hb ++ blocks L0 A0) -> 4096 <= a' /\ a' + k <= alloc_ceiling).
  { intros a' k Hin. destruct (in_blocks L A a' k (Permutation_in _ (Permutation_sym HPM) (in_cons _ _ _ Hin))) as (q & Hq & Eq).
    subst a'. exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq). }
  assert (NDA : forall a' k, In (a', k) (hb ++ blocks L0 A0) -> a' <> a).
  { intros a' k Hin Ea. pose proof (BND L A mem md HM) as ND. apply NoDup_ListNoDup in ND.
    apply (Permutation_map fst) in HPM. apply (Permutation_NoDup HPM) in ND.
    cbn [map app] in ND. inversion ND as [|? ? Hni _]. apply Hni. subst a'.
    apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin]. }
  assert (KEEPB : forall a' k i, In (a', k) (hb ++ blocks L0 A0) -> 0 <= i < k ->
            mbyte (ms_segs B) mem' (a' + i) = mbyte (ms_segs B) mem (a' + i) /\ ~ in_img B (a' + i)).
  { intros a' k i Hin Hi.
    destruct (in_blocks L A a' k (Permutation_in _ (Permutation_sym HPM) (in_cons _ _ _ Hin))) as (q & Hq & Eq).
    pose proof (ax_blocks_img HAX L A mem md q k i HM Hq Hi) as NI. subst a'.
    assert (Hqp : q <> p) by (intros ->; exact (NDA _ k Hin Ep)).
    split; [exact (UBK q k i Hq (UB q k Hq Hqp) Hi) | exact NI]. }
  exists fx', L', A', regs, regs', mem', md', m0, (MemNorm.normalize_cj rsegs mem').
  split; [try rewrite HSEGS; reflexivity|]. split; [exact Hfrm|]. split; [exact HP|].
  assert (REL' : MemNorm.mem_rel_cj rsegs mem' (MemNorm.normalize_cj rsegs mem'))
    by exact (MemNorm.mem_rel_cj_normalize rsegs mem' RO').
  split.
  { split; [|split; [exact RO'|split; [exact (blocks_perm_del hb L A L' A' a n b1 b2 HPM EB1 EB2)|]]].
    2: { rewrite <- (sb_hb_free b0 (a, n) hb). exact RES'. }
    split; [exact MR'|]. split; [exact WF'|]. split; [exact B'|]. split; [exact (ID' HID)|].
    split; [exists vm'; rewrite EMD, HVMd; apply vm_vm|].
    split.
    { intros a' Ha Hs He. destruct (HHI a' Ha Hs He) as [E1 E2].
      destruct (HIGH a' ltac:(left; lia) ltac:(intros Ho; pose proof (HOW a' Ho); lia)
                  ltac:(intros Ho; pose proof (HOW' a' Ho); lia)
                  ltac:(intros [Hs'|He']; [apply Hs; unfold ALLOC_STACK in Hs'; lia | exact (He He')])
                  ltac:(lia)) as [M1 M2].
      rewrite M1. split; [exact E1 | tauto]. }
    split.
    { intros a' Ha Hs Hc He. destruct (HIMG a' Ha Hs Hc He) as [E1 E2].
      pose proof (in_img_lo B a' HSEGS Ha) as Hr. pose proof ceil_hi.
      destruct (HIGH a' ltac:(right; exact Ha) (HIMGU L A mem md a' HM Ha Hs Hc) (HIMGU L' A' mem' md' a' MR' Ha Hs Hc)
                  ltac:(intros [Hs'|He']; [unfold ALLOC_STACK in Hs'; lia | exact (He He')])
                  ltac:(intros Hx; exact (EIMG a' Hx Ha))) as [M1 M2].
      rewrite M1. split; [exact E1 | tauto]. }
    split.
    { intros q k i Hq Hi. rewrite <- (HBLK q k i Hq Hi).
      apply (proj1 (KEEPB (ptr_addr L0 q) k i ltac:(apply in_or_app; right; apply blocks_in; exact Hq) Hi)). }
    split.
    { intros a' Ha. destruct Ha as [Ha|Ha]; [|apply SCR; right; exact Ha].
      destruct (Z_lt_le_dec a' (X - 8192)) as [Hl|Hl].
      - apply (proj2 (KEEPH a' ltac:(lia) ltac:(lia))). apply HSTK. left. exact Ha.
      - destruct (Z_lt_le_dec a' X) as [Hl2|Hl2]; [apply SCR; left; unfold ALLOC_STACK; lia|].
        apply (proj2 (KEEPH a' ltac:(lia) ltac:(lia))). apply HSTK. left. exact Ha. }
    split.
    { apply (sink_keep mem mem' md md' HSINK); [|rewrite EMD; apply fds_vm].
      intros a' Ha. pose proof (sink_img a' Ha) as HI.
      destruct (HIGH a' ltac:(right; exact HI) (sink_unowned L A mem md a' HM Ha) (sink_unowned L' A' mem' md' a' MR' Ha)
                  ltac:(intros [Hs'|He']; [unfold sink_at, ALLOC_STACK in *; lia | unfold errno_addr, sink_at in *; rewrite HTP, HERR in He'; lia])
                  ltac:(intros Hx; exact (EIMG a' Hx HI))) as [M1 _].
      exact M1. }
    exact (rodata_of_ro mem' RO'). }
  split; [exact REL'|]. split; [exact RP|].
  split.
  { apply (agree_rel mem m0 mem' _ X (S - X) HREL REL'); [lia | unfold TASK_SIZE; lia | intros a' Ha; apply nseg_high; lia|].
    intros i Hi. unfold Mem.wa. apply (raw_of_mbyte mem mem' (X + i)); [apply nseg_high; lia | lia |].
    exact (proj1 (KEEPH (X + i) ltac:(lia) ltac:(lia))). }
  intros a' k Hin. destruct (BR a' k Hin) as [Ba Bb].
  apply (agree_rel mem m0 mem' _ a' k HREL REL'); [lia | unfold TASK_SIZE; lia | |].
  - intros x Hx. apply nseg_blk; [lia|]. replace x with (a' + (x - a')) by lia.
    exact (proj2 (KEEPB a' k (x - a') Hin ltac:(lia))).
  - intros i Hi. unfold Mem.wa. apply (raw_of_mbyte mem mem' (a' + i));
      [apply nseg_blk; [lia | exact (proj2 (KEEPB a' k i Hin Hi))] | lia | exact (proj1 (KEEPB a' k i Hin Hi))].
Qed.

Definition room_ag (b : sbound) (n : Z) : Prop :=
  room_slots b n /\ 0 <= sb_cap b <= CAP_AG /\ sb_bytes b + n <= 2 ^ 29.

Lemma room_cf_of : forall L A mem md b n, aa_MR API L A mem md -> room_ag b n -> room_cf md b n.
Proof using LIMLAW.
  intros L A mem md b n HM (H1 & H2 & H3). exact (room_cf_of_limit md b n (LIMLAW L A mem md HM) H1 H2 H3).
Qed.

Lemma evt_SRcf_canon_r : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt rsegs Q (RegisterBridge.canonical_register_state ms) -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', (exists can, Q can /\ Regs6ss.ms_eqv can ms') -> SRcf B (mkCfg ms' md) P) ->
  SRcf B (mkCfg ms md) P.
Proof using HSEGS.
  intros ms Q md P HE. rewrite <- HSEGS in HE. exact (evt_SRcf_canon B ms Q md P HE).
Qed.

Lemma SRcf_loop : forall (W : Type) (m : W -> nat) (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SRcf B c (fun c' => Q c' \/ exists w', (m w' < m w)%nat /\ P w' c')) ->
  forall w c, P w c -> SRcf B c Q.
Proof using.
  intros W m P Q Hb w.
  induction w as [w IH] using (well_founded_induction (Wf_nat.well_founded_ltof W m)).
  intros c HP T HKt. apply (Hb w c HP T). intros c' [HQ | (w' & Hlt & HP')].
  - exact (HKt c' HQ).
  - exact (IH w' Hlt c' HP' T HKt).
Qed.

Lemma cut_run_cf : forall pc hb P W (Q : bvmap 5 word -> word -> bvmap 5 word -> bv 32 -> (word -> option byte) -> Prop) c,
  slot_cut pc hb P c -> W_ok hb W ->
  (forall (fx' : FPState) regs m0, frm_zero (@fp_csr fx') -> MemNorm.mem_inv_cj rsegs m0 -> P regs m0 ->
     Exec.evt rsegs (fun ms => exists R F' pc' fc' m0', ms = MState.MS R F' pc' fc' None m0' (seg_rom rsegs) /\
                      frm_zero fc' /\ Frame.munch W m0 m0' /\ Frame.wmono rsegs m0 m0' /\ Q R pc' F' fc' m0')
       (MState.MS (rmk regs) (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None m0 (seg_rom rsegs))) ->
  SRcf B c (cut_post hb Q).
Proof.
  intros pc hb P W Q c (fx' & L & A & regs & mem & md & m0 & -> & Hfrm & HFR & HREL & HP) HW HEV.
  pose proof (HEV fx' regs m0 Hfrm (mem_inv_cj_rel mem m0 HREL) HP) as E0.
  pose proof (MemNorm.evt_rel_MS_cj rsegs _ (rmk regs) (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None mem m0
    (seg_rom rsegs) wx_apart_rsegs HREL E0) as E1.
  pose proof HFR as (HSO & HRO & HPM & HRES).
  pose proof HSO as (HM & _).
  destruct (kb_md B API L A mem md HM) as [Hh Hl].
  eapply (evt_SRcf_canon_r (@mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) _ md); [exact E1 | exact Hh | exact Hl |].
  intros ms' (can & (s0 & (R & F' & pc' & fc' & m0' & Es0 & Hfc & MU & WM & HQ) & Hrel & Hsame) & Heqv).
  subst s0.
  destruct Hrel as (Er & Ef & Epc & Esv & Ers & Efc & Erom & Emem).
  destruct Heqv as (Rq & Fq & Pq & Sq & RSq & FCq & Mq & ROq).
  destruct can as [cr cf cpc csv crs cfc cm cro]. destruct ms' as [r' f' p' sv' rs' fc'' m' ro'].
  cbn in Er, Ef, Epc, Esv, Ers, Efc, Erom, Emem, Rq, Fq, Pq, Sq, RSq, FCq, Mq, ROq, Hsame.
  subst cr cf cpc csv crs cfc cro. subst f' p' sv' rs' fc'' ro' cm.
  apply SRcf_ret.
  exists (mkFP F' fc'), L, A, r', m', md, m0', R, pc'.
  split; [reflexivity|]. split; [exact Hfc|].
  split.
  { apply (FR_write hb L A mem m' md W HFR HW).
    - exact (MemNorm.munch_rel_cj rsegs W mem m0 m' m0' HREL Emem Hsame MU).
    - exact (MemNorm.wmono_rel_cj rsegs mem m0 m' m0' HREL Emem Hsame WM).
    - exact (MemNorm.ro_agree_same_cj rsegs mem m' HRO Hsame). }
  split; [exact Emem|]. split; [exact (kb_getr_eqv R r' Rq)|]. exact HQ.
Qed.

Lemma cut_malloc_cf : forall hb P n X c,
  slot_cut 0x17aec hb P c ->
  (forall regs m0, P regs m0 -> YK0s.ret_ok (getr regs 1) /\ getr regs 10 = Z_to_bv 64 n /\
     getr regs 2 = Z_to_bv 64 X /\ getr regs 4 = Z_to_bv 64 (ms_tp B)) ->
  X mod 16 = 0 -> S - K + ALLOC_STACK <= X <= S -> 0 <= n -> room_ag (sb_hb b0 hb) n ->
  SRcf B c (malloc_post hb P n X).
Proof.
  intros hb P n X c (fx' & L & A & regs & mem & md & m0 & -> & Hfrm & HFR & HREL & HP) HPR HX16 HXr Hn0 Hroom.
  destruct (HPR regs m0 HP) as (Hra & H10 & H2 & H4).
  pose proof HFR as (HSO & HRO & HPM & HRES).
  pose proof HSO as (HM & HWF & HB & HID & (vm & HVMd) & HHI & HIMG & HBLK & HSTK & HSINK & HROD).
  pose proof alloc_ceiling_val as Hcv. pose proof alloc_ceiling_lt as Hcl. unfold ALLOC_STACK in HXr.
  assert (Hsp : spZ regs = X) by (apply stk_sp; [exact H2 | lia]).
  pose proof (MCF fx') as MAL.
  assert (PRE : call_pre B (aa_MR API) L A regs mem md).
  { unfold call_pre. rewrite Hsp. split; [exact HM|]. split; [exact HWF|]. split; [exact HB|].
    split; [exact Hra|]. split; [exact HX16|]. split; [unfold ALLOC_STACK; lia|]. split; [lia|].
    split; [intros a Ha; apply HSTK; left; unfold ALLOC_STACK in Ha; lia|].
    split; [exact H4|]. split; [intros a Ha; apply HSTK; right; exact Ha|].
    intros E. rewrite HID in E. discriminate. }
  pose proof (MAL L A regs mem md n (sb_hb b0 hb) PRE ltac:(rewrite HSEGS; exact HRO) H10 HRES (room_cf_of L A mem md _ n HM Hroom)) as E.
  rewrite HSEGS, HMAL in E. eapply SRcf_mono; [exact E|].
  intros c' (L' & A' & regs' & mem' & md' & res & -> & CP & R10 & Rnz & R16 & (F1 & F2 & F3) &
             (b1 & b2 & EB1 & EB2) & BK & RO' & GK & UB & ID' & RG & RES').
  rewrite HSEGS in RO'.
  destruct CP as (MR' & WF' & B' & LLE & PADDR & RP & (vm' & EMD) & HIGH & UBK & SCR).
  unfold scratch_k in HIGH, SCR. rewrite Hsp in HIGH, SCR.
  assert (HOW : forall a, owned B L A a -> a < alloc_ceiling)
    by (intros a Ho; exact (proj2 (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho))).
  assert (HOW' : forall a, owned B L' A' a -> a < alloc_ceiling)
    by (intros a Ho; exact (proj2 (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ MR' Ho))).
  assert (HIMGU : forall L1 A1 mem1 md1 a, aa_MR API L1 A1 mem1 md1 -> in_img B a -> ~ static_owned B a ->
            ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ owned B L1 A1 a).
  { intros L1 A1 mem1 md1 a HM1 Ha Hs Hc [Ho|Ho]; [exact (Hc (ax_img HAX L1 A1 mem1 md1 a HM1 Ha Ho)) | exact (Hs Ho)]. }
  assert (KEEPH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (X - 8192 <= a < X) ->
            mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
            (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hs. apply HIGH; [left; lia | intros Ho; pose proof (HOW a Ho); lia |
      intros Ho; pose proof (HOW' a Ho); lia | | tauto].
    intros [Hs'|He]; [unfold ALLOC_STACK in Hs'; lia|]. unfold errno_addr in He. rewrite HTP, HERR in He. lia. }
  assert (BR : forall a k, In (a, k) (hb ++ blocks L0 A0) -> 4096 <= a /\ a + k <= alloc_ceiling).
  { intros a k Hin. destruct (in_blocks L A a k (Permutation_in _ (Permutation_sym HPM) Hin)) as (p & Hp & Ep).
    subst a. exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HM Hp). }
  assert (KEEPB : forall a k i, In (a, k) (hb ++ blocks L0 A0) -> 0 <= i < k ->
            mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i) /\ ~ in_img B (a + i)).
  { intros a k i Hin Hi.
    destruct (in_blocks L A a k (Permutation_in _ (Permutation_sym HPM) Hin)) as (p & Hp & Ep).
    pose proof (ax_blocks_img HAX L A mem md p k i HM Hp Hi) as NI. subst a.
    split; [exact (UBK p k i Hp (UB p k Hp) Hi) | exact NI]. }
  exists fx', L', A', regs, regs', mem', md', m0, (MemNorm.normalize_cj rsegs mem'), res.
  split; [rewrite HSEGS; reflexivity|]. split; [exact Hfrm|]. split; [exact HP|].
  assert (REL' : MemNorm.mem_rel_cj rsegs mem' (MemNorm.normalize_cj rsegs mem'))
    by exact (MemNorm.mem_rel_cj_normalize rsegs mem' RO').
  split.
  { split; [|split; [exact RO'|split; [exact (blocks_perm_add hb L A L' A' res n b1 b2 HPM EB1 EB2)|]]].
    2: { rewrite sb_hb_cons. exact RES'. }
    split; [exact MR'|]. split; [exact WF'|]. split; [exact B'|]. split; [exact ID'|].
    split; [exists vm'; rewrite EMD, HVMd; apply vm_vm|].
    split.
    { intros a Ha Hs He. destruct (HHI a Ha Hs He) as [E1 E2].
      destruct (HIGH a ltac:(left; lia) ltac:(intros Ho; pose proof (HOW a Ho); lia)
                  ltac:(intros Ho; pose proof (HOW' a Ho); lia) ltac:(intros [Hs'|He']; [apply Hs; unfold ALLOC_STACK in Hs'; lia | exact (He He')])
                  ltac:(tauto)) as [M1 M2].
      rewrite M1. split; [exact E1 | tauto]. }
    split.
    { intros a Ha Hs Hc He. destruct (HIMG a Ha Hs Hc He) as [E1 E2].
      pose proof (in_img_lo B a HSEGS Ha) as Hr. pose proof ceil_hi.
      destruct (HIGH a ltac:(right; exact Ha) (HIMGU L A mem md a HM Ha Hs Hc) (HIMGU L' A' mem' md' a MR' Ha Hs Hc)
                  ltac:(intros [Hs'|He']; [unfold ALLOC_STACK in Hs'; lia | exact (He He')]) ltac:(tauto)) as [M1 M2].
      rewrite M1. split; [exact E1 | tauto]. }
    split.
    { intros q k i Hq Hi. rewrite <- (HBLK q k i Hq Hi).
      apply (proj1 (KEEPB (ptr_addr L0 q) k i ltac:(apply in_or_app; right; apply blocks_in; exact Hq) Hi)). }
    split.
    { intros a Ha. destruct Ha as [Ha|Ha]; [|apply SCR; right; exact Ha].
      destruct (Z_lt_le_dec a (X - 8192)) as [Hl|Hl].
      - apply (proj2 (KEEPH a ltac:(lia) ltac:(lia))). apply HSTK. left. exact Ha.
      - destruct (Z_lt_le_dec a X) as [Hl2|Hl2]; [apply SCR; left; unfold ALLOC_STACK; lia|].
        apply (proj2 (KEEPH a ltac:(lia) ltac:(lia))). apply HSTK. left. exact Ha. }
    split.
    { apply (sink_keep mem mem' md md' HSINK); [|rewrite EMD; apply fds_vm].
      intros a Ha. pose proof (sink_img a Ha) as HI.
      destruct (HIGH a ltac:(right; exact HI) (sink_unowned L A mem md a HM Ha) (sink_unowned L' A' mem' md' a MR' Ha)
                  ltac:(intros [Hs'|He']; [unfold sink_at, ALLOC_STACK in *; lia | unfold errno_addr, sink_at in *; rewrite HTP, HERR in He'; lia])
                  ltac:(tauto)) as [M1 _].
      exact M1. }
    exact (rodata_of_ro mem' RO'). }
  split; [exact REL'|]. split; [exact RP|]. split; [exact R10|].
  split; [exact F1|]. split; [exact R16|]. split; [exact F2|]. split; [exact F3|].
  split.
  { destruct (in_blocks L' A' res n ltac:(rewrite EB1; apply in_or_app; right; left; reflexivity)) as (q & Hq & Eq).
    apply rwc_present; [lia | lia | exact Hn0 |].
    intros i Hi. split; [apply nseg_blk; [lia | exact (F3 i Hi)]|].
    rewrite (norm_nseg mem' _ (res + i) REL') by (try (apply nseg_blk; [lia | exact (F3 i Hi)]); unfold TASK_SIZE; lia).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i MR' Hq Hi) as ((bb & Hbb) & _). rewrite Eq in Hbb.
    unfold Mem.wa. rewrite Hbb. discriminate. }
  split.
  { apply (agree_rel mem m0 mem' _ X (S - X) HREL REL'); [lia | unfold TASK_SIZE; lia | intros a Ha; apply nseg_high; lia|].
    intros i Hi. unfold Mem.wa. apply (raw_of_mbyte mem mem' (X + i)); [apply nseg_high; lia | lia |].
    exact (proj1 (KEEPH (X + i) ltac:(lia) ltac:(lia))). }
  intros a k Hin. destruct (BR a k Hin) as [Ba Bb].
  apply (agree_rel mem m0 mem' _ a k HREL REL'); [lia | unfold TASK_SIZE; lia | |].
  - intros x Hx. apply nseg_blk; [lia|]. replace x with (a + (x - a)) by lia.
    exact (proj2 (KEEPB a k (x - a) Hin ltac:(lia))).
  - intros i Hi. unfold Mem.wa. apply (raw_of_mbyte mem mem' (a + i));
      [apply nseg_blk; [lia | exact (proj2 (KEEPB a k i Hin Hi))] | lia | exact (proj1 (KEEPB a k i Hin Hi))].
Qed.

Lemma cut_free_cf : forall a n hb P X c,
  slot_cut 0x179ac ((a, n) :: hb) P c ->
  (forall regs m0, P regs m0 -> YK0s.ret_ok (getr regs 1) /\ getr regs 10 = Z_to_bv 64 a /\
     getr regs 2 = Z_to_bv 64 X /\ getr regs 4 = Z_to_bv 64 (ms_tp B)) ->
  X mod 16 = 0 -> S - K + ALLOC_STACK <= X <= S ->
  SRcf B c (free_post hb P X).
Proof.
  intros a n hb P X c (fx' & L & A & regs & mem & md & m0 & -> & Hfrm & HFR & HREL & HP) HPR HX16 HXr.
  destruct (HPR regs m0 HP) as (Hra & H10 & H2 & H4).
  pose proof HFR as (HSO & HRO & HPM & HRES).
  pose proof HSO as (HM & HWF & HB & HID & (vm & HVMd) & HHI & HIMG & HBLK & HSTK & HSINK & HROD).
  pose proof alloc_ceiling_val as Hcv. pose proof alloc_ceiling_lt as Hcl. unfold ALLOC_STACK in HXr.
  assert (Hsp : spZ regs = X) by (apply stk_sp; [exact H2 | lia]).
  destruct (HFA fx') as (_ & _ & _ & _ & _ & _ & _ & _ & BND & _). pose proof (FCF fx') as FRE.
  destruct (hb_block ((a, n) :: hb) L A a n HPM ltac:(left; reflexivity)) as (p & Hp & Ep).
  assert (PRE : call_pre B (aa_MR API) L A regs mem md).
  { unfold call_pre. rewrite Hsp. split; [exact HM|]. split; [exact HWF|]. split; [exact HB|].
    split; [exact Hra|]. split; [exact HX16|]. split; [unfold ALLOC_STACK; lia|]. split; [lia|].
    split; [intros a' Ha; apply HSTK; left; unfold ALLOC_STACK in Ha; lia|].
    split; [exact H4|]. split; [intros a' Ha; apply HSTK; right; exact Ha|].
    intros E. rewrite HID in E. discriminate. }
  pose proof (FRE L A regs mem md p n (sb_hb b0 ((a, n) :: hb)) PRE ltac:(rewrite HSEGS; exact HRO) Hp
    ltac:(rewrite Ep; exact H10) HRES) as E.
  rewrite HSEGS, HFRE in E. eapply SRcf_mono; [exact E|].
  intros c' (L' & A' & regs' & mem' & md' & -> & CP & (b1 & b2 & EB1 & EB2) & BK & RO' & GK & UB & ID' & RG & RES').
  try rewrite HSEGS in RO'. rewrite Ep in EB1, CP.
  apply call_post_k_alloc in CP.
  destruct CP as (MR' & WF' & B' & LLE & PADDR & RP & (vm' & EMD) & HIGH & UBK & SCR).
  unfold scratch in HIGH, SCR. rewrite Hsp in HIGH, SCR.
  pose proof (hb_not_owned ((a, n) :: hb) L A mem md a n) as HBA.
  assert (HOW : forall a', owned B L A a' -> a' < alloc_ceiling)
    by (intros a' Ho; exact (proj2 (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho))).
  assert (HOW' : forall a', owned B L' A' a' -> a' < alloc_ceiling)
    by (intros a' Ho; exact (proj2 (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ MR' Ho))).
  assert (HIMGU : forall L1 A1 mem1 md1 a', aa_MR API L1 A1 mem1 md1 -> in_img B a' -> ~ static_owned B a' ->
            ~ (ms_ctx B <= a' < ms_ctx B + CTX_SIZE) -> ~ owned B L1 A1 a').
  { intros L1 A1 mem1 md1 a' HM1 Ha Hs Hc [Ho|Ho]; [exact (Hc (ax_img HAX L1 A1 mem1 md1 a' HM1 Ha Ho)) | exact (Hs Ho)]. }
  assert (HAR : 4096 <= a /\ a + n <= alloc_ceiling) by (rewrite <- Ep; exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp)).
  assert (EIMG : forall a', a <= a' < a + n -> ~ in_img B a').
  { intros a' Ha. destruct (HBA a' HM HPM ltac:(left; reflexivity) Ha) as (_ & H & _). exact H. }
  assert (KEEPH : forall a', alloc_ceiling <= a' < 2 ^ 64 -> ~ (X - 8192 <= a' < X) ->
            mbyte (ms_segs B) mem' a' = mbyte (ms_segs B) mem a' /\
            (writable_at (ms_segs B) mem a' <-> writable_at (ms_segs B) mem' a')).
  { intros a' Ha Hs. apply HIGH; [left; lia | intros Ho; pose proof (HOW a' Ho); lia |
      intros Ho; pose proof (HOW' a' Ho); lia | | lia].
    intros [Hs'|He]; [unfold ALLOC_STACK in Hs'; lia|]. unfold errno_addr in He. rewrite HTP, HERR in He. lia. }
  assert (BR : forall a' k, In (a', k) (hb ++ blocks L0 A0) -> 4096 <= a' /\ a' + k <= alloc_ceiling).
  { intros a' k Hin. destruct (in_blocks L A a' k (Permutation_in _ (Permutation_sym HPM) (in_cons _ _ _ Hin))) as (q & Hq & Eq).
    subst a'. exact (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq). }
  assert (NDA : forall a' k, In (a', k) (hb ++ blocks L0 A0) -> a' <> a).
  { intros a' k Hin Ea. pose proof (BND L A mem md HM) as ND. apply NoDup_ListNoDup in ND.
    apply (Permutation_map fst) in HPM. apply (Permutation_NoDup HPM) in ND.
    cbn [map app] in ND. inversion ND as [|? ? Hni _]. apply Hni. subst a'.
    apply in_map_iff. exists (a, k). split; [reflexivity | exact Hin]. }
  assert (KEEPB : forall a' k i, In (a', k) (hb ++ blocks L0 A0) -> 0 <= i < k ->
            mbyte (ms_segs B) mem' (a' + i) = mbyte (ms_segs B) mem (a' + i) /\ ~ in_img B (a' + i)).
  { intros a' k i Hin Hi.
    destruct (in_blocks L A a' k (Permutation_in _ (Permutation_sym HPM) (in_cons _ _ _ Hin))) as (q & Hq & Eq).
    pose proof (ax_blocks_img HAX L A mem md q k i HM Hq Hi) as NI. subst a'.
    assert (Hqp : q <> p) by (intros ->; exact (NDA _ k Hin Ep)).
    split; [exact (UBK q k i Hq (UB q k Hq Hqp) Hi) | exact NI]. }
  exists fx', L', A', regs, regs', mem', md', m0, (MemNorm.normalize_cj rsegs mem').
  split; [try rewrite HSEGS; reflexivity|]. split; [exact Hfrm|]. split; [exact HP|].
  assert (REL' : MemNorm.mem_rel_cj rsegs mem' (MemNorm.normalize_cj rsegs mem'))
    by exact (MemNorm.mem_rel_cj_normalize rsegs mem' RO').
  split.
  { split; [|split; [exact RO'|split; [exact (blocks_perm_del hb L A L' A' a n b1 b2 HPM EB1 EB2)|]]].
    2: { rewrite <- (sb_hb_free b0 (a, n) hb). exact RES'. }
    split; [exact MR'|]. split; [exact WF'|]. split; [exact B'|]. split; [exact (ID' HID)|].
    split; [exists vm'; rewrite EMD, HVMd; apply vm_vm|].
    split.
    { intros a' Ha Hs He. destruct (HHI a' Ha Hs He) as [E1 E2].
      destruct (HIGH a' ltac:(left; lia) ltac:(intros Ho; pose proof (HOW a' Ho); lia)
                  ltac:(intros Ho; pose proof (HOW' a' Ho); lia)
                  ltac:(intros [Hs'|He']; [apply Hs; unfold ALLOC_STACK in Hs'; lia | exact (He He')])
                  ltac:(lia)) as [M1 M2].
      rewrite M1. split; [exact E1 | tauto]. }
    split.
    { intros a' Ha Hs Hc He. destruct (HIMG a' Ha Hs Hc He) as [E1 E2].
      pose proof (in_img_lo B a' HSEGS Ha) as Hr. pose proof ceil_hi.
      destruct (HIGH a' ltac:(right; exact Ha) (HIMGU L A mem md a' HM Ha Hs Hc) (HIMGU L' A' mem' md' a' MR' Ha Hs Hc)
                  ltac:(intros [Hs'|He']; [unfold ALLOC_STACK in Hs'; lia | exact (He He')])
                  ltac:(intros Hx; exact (EIMG a' Hx Ha))) as [M1 M2].
      rewrite M1. split; [exact E1 | tauto]. }
    split.
    { intros q k i Hq Hi. rewrite <- (HBLK q k i Hq Hi).
      apply (proj1 (KEEPB (ptr_addr L0 q) k i ltac:(apply in_or_app; right; apply blocks_in; exact Hq) Hi)). }
    split.
    { intros a' Ha. destruct Ha as [Ha|Ha]; [|apply SCR; right; exact Ha].
      destruct (Z_lt_le_dec a' (X - 8192)) as [Hl|Hl].
      - apply (proj2 (KEEPH a' ltac:(lia) ltac:(lia))). apply HSTK. left. exact Ha.
      - destruct (Z_lt_le_dec a' X) as [Hl2|Hl2]; [apply SCR; left; unfold ALLOC_STACK; lia|].
        apply (proj2 (KEEPH a' ltac:(lia) ltac:(lia))). apply HSTK. left. exact Ha. }
    split.
    { apply (sink_keep mem mem' md md' HSINK); [|rewrite EMD; apply fds_vm].
      intros a' Ha. pose proof (sink_img a' Ha) as HI.
      destruct (HIGH a' ltac:(right; exact HI) (sink_unowned L A mem md a' HM Ha) (sink_unowned L' A' mem' md' a' MR' Ha)
                  ltac:(intros [Hs'|He']; [unfold sink_at, ALLOC_STACK in *; lia | unfold errno_addr, sink_at in *; rewrite HTP, HERR in He'; lia])
                  ltac:(intros Hx; exact (EIMG a' Hx HI))) as [M1 _].
      exact M1. }
    exact (rodata_of_ro mem' RO'). }
  split; [exact REL'|]. split; [exact RP|].
  split.
  { apply (agree_rel mem m0 mem' _ X (S - X) HREL REL'); [lia | unfold TASK_SIZE; lia | intros a' Ha; apply nseg_high; lia|].
    intros i Hi. unfold Mem.wa. apply (raw_of_mbyte mem mem' (X + i)); [apply nseg_high; lia | lia |].
    exact (proj1 (KEEPH (X + i) ltac:(lia) ltac:(lia))). }
  intros a' k Hin. destruct (BR a' k Hin) as [Ba Bb].
  apply (agree_rel mem m0 mem' _ a' k HREL REL'); [lia | unfold TASK_SIZE; lia | |].
  - intros x Hx. apply nseg_blk; [lia|]. replace x with (a' + (x - a')) by lia.
    exact (proj2 (KEEPB a' k (x - a') Hin ltac:(lia))).
  - intros i Hi. unfold Mem.wa. apply (raw_of_mbyte mem mem' (a' + i));
      [apply nseg_blk; [lia | exact (proj2 (KEEPB a' k i Hin Hi))] | lia | exact (proj1 (KEEPB a' k i Hin Hi))].
Qed.

End Cut.
