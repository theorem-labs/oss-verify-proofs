(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the evt bridge of its SR frame
   (S-FR items 3 and 5).

   - lfr_run: an evt walk of a config's view (LFr.lcanon: the registers as they are, the memory through
     MemNorm.normalize_cj) is an SR step of the config itself (Contract.evt_SR + MemNorm.evt_normalize_cj);
   - lfr_own: the frame relation LFR survives a segment's own writes (the regions LDefs.own_w names);
   - cut_evt: a segment from the cut at pc (CUT) whose post carries LDefs.seg_fp ends in the cut at pc'.

   Shapes ported from libreac/fuzz_boxreg lib/Prog/LLVMFuzzerTestOneInput_fr.v (llvm_run_norm_cj, lf_fr_evt)
   and libreac/fuzz_pcap lib/Prog/Slot/PTac.v (ss_FR_kr, ss_hb_facts, ss_pw_perm); every constant is link's
   (LFr.LFF, the plain image). *)
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Generic facts: ms_eqv, pairwise, blocks
   ========================================================================== *)

Lemma lfr_xregs_trans : forall R1 R2 R3,
  Regs6ss.xregs_eqv R1 R2 -> Regs6ss.xregs_eqv R2 R3 -> Regs6ss.xregs_eqv R1 R3.
Proof. intros R1 R2 R3 H1 H2 r Hr. rewrite (H1 r Hr). exact (H2 r Hr). Qed.

Lemma lfr_ms_eqv_trans : forall a b c, Regs6ss.ms_eqv a b -> Regs6ss.ms_eqv b c -> Regs6ss.ms_eqv a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [exact (lfr_xregs_trans _ _ _ A1 B1)|].
  split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [congruence|]. split; congruence.
Qed.

(* a state ms_eqv-related to an MS state is that MS state with its own registers *)
Lemma lfr_eqv_MS : forall R F pc fc rv m ro ms,
  Regs6ss.ms_eqv (MS R F pc fc rv m ro) ms -> ms = MS (ms_regs ms) F pc fc rv m ro.
Proof.
  intros R F pc fc rv m ro [r f p s v c mm rr] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *. subst. reflexivity.
Qed.

Lemma lfr_pw_perm : forall {X : Type} (R : X -> X -> Prop), (forall a b, R a b -> R b a) ->
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

Lemma lfr_pw_app : forall {X : Type} (R : X -> X -> Prop) l1 l2, pairwise R (l1 ++ l2) ->
  forall x y, In x l1 -> In y l2 -> R x y.
Proof.
  intros X R l1. induction l1 as [|a l1 IH]; intros l2 H x y Hx Hy; [destruct Hx|].
  destruct H as [H1 H2]. destruct Hx as [<-|Hx].
  - apply H1. apply in_or_app. right. exact Hy.
  - exact (IH l2 H2 x y Hx Hy).
Qed.

(* two distinct members of a pairwise list are related one way or the other *)
Lemma lfr_pw_in2 : forall {X : Type} (R : X -> X -> Prop) l x y, pairwise R l ->
  In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros X R l. induction l as [|a l IH]; intros x y H Hx Hy Hne; [destruct Hx|].
  destruct H as [H1 H2]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso. exact (Hne eq_refl).
  - left. exact (H1 y Hy).
  - right. exact (H1 x Hx).
  - exact (IH x y H2 Hx Hy Hne).
Qed.

Lemma lfr_blk_of : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn [fst snd] in E. injection E as E1 E2. subst. exists p. split; [exact Hp | reflexivity].
Qed.

(* ==========================================================================
   2. The image bytes a segment writes (LDefs.own_w): g_nl, g_names, long_alias (one stretch
      [0x31b80, 0x74525)) and errno [0x75564, 0x75568); the three FILE heads
   ========================================================================== *)

Definition lfr_iw (x : Z) : Prop := (0x31b80 <= x < 0x74525) \/ (0x75564 <= x < 0x75568).

Definition lfr_rng_img (lo hi : Z) : bool :=
  existsb (fun s => (bv_unsigned (fst s) <=? lo) && (hi <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs).

Lemma lfr_chk_g : lfr_rng_img 0x31b80 0x74525 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lfr_chk_e : lfr_rng_img 0x75564 0x75568 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lfr_chk_h1 : lfr_rng_img 0x74528 0x74530 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lfr_chk_h2 : lfr_rng_img 0x75530 0x75538 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lfr_chk_h3 : lfr_rng_img 0x95cc8 0x95cd0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lfr_iw_glob : forall x, 0x31b80 <= x < 0x74525 -> in_globals llvm_G x.
Proof.
  intros x Hx. unfold in_globals, llvm_G.
  destruct (Z_lt_dec x 0x741f8) as [H1|H1]; [|destruct (Z_lt_dec x 0x743f8) as [H2|H2]].
  - exists 0x31b80, 271992. split; [right; left; reflexivity | lia].
  - exists 0x741f8, 512. split; [right; right; left; reflexivity | lia].
  - exists 0x743f8, 301. split; [right; right; right; left; reflexivity | lia].
Qed.

Lemma lfr_own_iw : forall S hp x, own_w S hp x ->
  (S - 65536 <= x < S) \/ lfr_iw x \/ in_tb hp x.
Proof.
  intros S hp x Hw. unfold own_w in Hw.
  unfold SLOT_STACK_Z, A_G_NL, NK_SIZE, A_G_NAMES, G_NAMES_SIZE, A_LONG_ALIAS, LONG_ALIAS_SIZE,
    A_ERRNO, A_TP, ERRNO_TP_OFF in Hw.
  destruct Hw as [H|[H|[H|[H|[H|H]]]]].
  - left. exact H.
  - right. left. left. lia.
  - right. left. left. lia.
  - right. left. left. lia.
  - right. left. right. lia.
  - right. right. exact H.
Qed.

Section LR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Lemma lfr_img_rng : forall lo hi, lfr_rng_img lo hi = true -> forall a, lo <= a < hi -> in_img B a.
Proof.
  intros lo hi H a Ha. unfold lfr_rng_img in H. apply existsb_exists in H as (s & Hs & E).
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  unfold in_img. rewrite (lff_segs B API FF). split; [exact lfr_rsegs_nonnil|].
  exists s. split; [exact Hs | lia].
Qed.

Lemma lfr_iw_facts : forall x, lfr_iw x ->
  in_img B x /\ ~ static_owned B x /\ ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE) /\ x < LF_TOP.
Proof.
  intros x Hx.
  pose proof FF as (SEG & _ & _ & _ & _ & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP & EOFF
    & REP & VML & DBL & _).
  split; [destruct Hx as [Hx|Hx]; [exact (lfr_img_rng _ _ lfr_chk_g x Hx) | exact (lfr_img_rng _ _ lfr_chk_e x Hx)]|].
  unfold lfr_iw in Hx.
  split.
  { intros Hs. unfold static_owned, vml_lo, vml_len in Hs.
    rewrite LCK, LIBC, GOT, GUA, DBR, SCL, SMC, MDC, VML, DBL in Hs. cbv iota in Hs. lia. }
  split; [rewrite CTX; unfold CTX_SIZE; lia | unfold LF_TOP; lia].
Qed.

(* ==========================================================================
   3. The bridge: an evt walk of the view is an SR step of the config
   ========================================================================== *)

Lemma lfr_run : forall (fx' : YK11.FPState) regs pc mem md (Q : machine_state -> Prop) (K : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (lcanon fx' regs pc mem) ->
  (forall ms, Q ms -> exists R F pc' fc m', ms = MS R F pc' fc None m' (seg_rom rsegs)) ->
  (forall R F pc' fc m0', Q (MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall m', mem_rel_cj rsegs m' m0' -> cj_same rsegs mem m' ->
     SR rsegs (mkCfg (@YK11.mkst (mkFP F fc) R pc' m' (seg_rom rsegs)) md) K) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) K.
Proof.
  intros fx' regs pc mem md Q K Hh Hl Hro HE Hform HK.
  apply (evt_SR rsegs _ (fun s => exists s0, Q s0 /\ ms_rel_cj rsegs s s0 /\ cj_same rsegs mem (ms_mem s)) md K);
    [| exact Hh | exact Hl |].
  - change (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom rsegs))
      with (MS regs (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None mem (seg_rom rsegs)).
    apply evt_normalize_cj; [exact wx_apart_rsegs | exact Hro | exact HE].
  - intros ms' (s0 & HQ & Hrel & Hsame).
    destruct (Hform s0 HQ) as (R & F & pc' & fc & m0' & ->).
    destruct ms' as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *. subst.
    exact (HK _ _ _ _ _ HQ _ E8 Hsame).
Qed.

(* ==========================================================================
   4. The frame relation survives the slot's own writes
   ========================================================================== *)

Lemma lfr_own : forall g hb T hp L A mem md mem' W,
  LFR B API g hb T L A mem md ->
  (forall t, In t hp -> In t hb /\ ~ In t T) ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> own_w (lg_S g) hp x) ->
  LFR B API g hb T L A mem' md.
Proof.
  intros g hb T hp L A mem md mem' W HL Hhp MU WM MI' Hown.
  pose proof FF as (SEG & _ & _ & _ & _ & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP & EOFF
    & REP & VML & DBL & OFH & OFL & THR & CTXRO & ALLOC).
  pose proof (lff_errno B API FF) as ER.
  destruct (ALLOC YK11.fx0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EUN & _ & _ & AX & _).
  pose proof (aa_laws API) as LAWS.
  pose proof HL as (HGV & HMR & HWF & HBD & HID & Hmd & Hhi & Himg & Hb0 & Hstw & Herw & Hgd & Hro & Hres & HP
    & Hkept & Hgi).
  pose proof HGV as ((Hpre & _) & _ & Htb & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & HSc & HS63 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  assert (HSl : YM05.alloc_ceiling + 65536 <= lg_S g) by exact HSc.
  assert (HSh : lg_S g < 2 ^ 63) by exact HS63.
  (* the blocks of L A: present, in the heap below the ceiling, not the allocator's, outside the image *)
  assert (BLK : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
     present mem (a + i) /\ 4096 <= a /\ a + k <= YM05.alloc_ceiling /\ ~ owned B L A (a + i) /\ ~ in_img B (a + i)).
  { intros a k i Hin Hi. destruct (lfr_blk_of L A a k Hin) as (p & Hp & <-).
    destruct (mr_blocks B (aa_MR API) LAWS L A mem md p k i HMR Hp Hi) as (H1 & H2 & H3 & H4).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
    exact (ax_blocks_img AX L A mem md p k i HMR Hp Hi). }
  (* a byte of the blocks hp the segment holds *)
  assert (HPB : forall x, in_tb hp x -> x < YM05.alloc_ceiling /\ ~ owned B L A x /\ ~ in_img B x).
  { intros x (a & k & Hin & Hx). destruct (Hhp _ Hin) as [Hhb _].
    assert (Hb : In (a, k) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hhb).
    destruct (BLK a k (x - a) Hb ltac:(lia)) as (_ & H2 & H3 & H4 & H5).
    replace (a + (x - a)) with x in H4, H5 by lia.
    split; [lia|]. split; [exact H4 | exact H5]. }
  (* the kept set T: blocks of L A *)
  assert (TB : forall t, In t T -> In t (blocks L A)).
  { intros t Ht. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app.
    destruct Htb as [_ Htb].
    destruct Hkept as [(_ & ET) | (_ & [ET | (f0 & ET & Hf0)])]; subst T.
    - right. exact (Htb t Ht).
    - destruct Ht.
    - left. destruct Ht as [<- | []]. exact Hf0. }
  assert (HOUT : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (lg_S g - 65536 <= x < lg_S g) \/ lfr_iw x \/ in_tb hp x).
  { intros x Hx NO. exact (lfr_own_iw _ _ _ (Hown x Hx NO)). }
  assert (EQ : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
     (writable_at (ms_segs B) mem x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx O. pose proof (lfr_munch_at W mem mem' x MU Hx O) as E.
    unfold mbyte, writable_at, wview. rewrite E. split; [reflexivity | tauto]. }
  assert (WM' : forall x, writable_at (ms_segs B) mem x -> writable_at (ms_segs B) mem' x).
  { intros x Hw. unfold writable_at in *. rewrite SEG in *. apply WM. exact Hw. }
  unfold LFR.
  split; [exact HGV|].
  split.
  { destruct (mr_model B (aa_MR API) LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
    apply (mr_frame B (aa_MR API) LAWS L A mem mem' md md HMR); [| | | reflexivity | exact Hh | exact Hl | exact Hmat].
    - intros a Ho. pose proof (mr_owned_low B (aa_MR API) LAWS _ _ _ _ a HMR Ho) as Ha.
      destruct (lfr_outside_dec W a) as [O|NO]; [exact (proj1 (EQ a ltac:(lia) O))|].
      exfalso. destruct (HOUT a ltac:(lia) NO) as [Hs|[Hw|Hb]].
      + lia.
      + destruct (lfr_iw_facts a Hw) as (Hi & Hs & Hc & _). destruct Ho as [Ho|Ho];
          [exact (Hc (ax_img AX L A mem md a HMR Hi Ho)) | exact (Hs Ho)].
      + exact (proj1 (proj2 (HPB a Hb)) Ho).
    - intros a Ho [bb Hb]. pose proof (mr_owned_low B (aa_MR API) LAWS _ _ _ _ a HMR Ho) as Ha.
      destruct (lfr_outside_dec W a) as [O|NO].
      + exists bb. rewrite (lfr_munch_at W mem mem' a MU ltac:(lia) O). exact Hb.
      + exfalso. destruct (HOUT a ltac:(lia) NO) as [Hs|[Hw|Hb']].
        * lia.
        * destruct (lfr_iw_facts a Hw) as (Hi & Hs & Hc & _). destruct Ho as [Ho|Ho];
            [exact (Hc (ax_img AX L A mem md a HMR Hi Ho)) | exact (Hs Ho)].
        * exact (proj1 (proj2 (HPB a Hb')) Ho).
    - intros p n i Hin Hi.
      destruct (mr_blocks B (aa_MR API) LAWS L A mem md p n i HMR Hin Hi) as (Hpr & H1 & H2 & _).
      pose proof (ax_blocks_img AX L A mem md p n i HMR Hin Hi) as Hni.
      apply (lfr_present_of_writable B mem' _ SEG Hni ltac:(lia)).
      rewrite <- SEG. apply WM'. apply YL01.present_writable. exact Hpr. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HID|]. split; [exact Hmd|].
  split.
  { intros a Ha Hns. destruct (lfr_outside_dec W a) as [O|NO].
    - destruct (EQ a ltac:(lia) O) as [E1 E2]. destruct (Hhi a Ha Hns) as [F1 F2].
      split; [rewrite E1; exact F1 | tauto].
    - exfalso. destruct (HOUT a ltac:(lia) NO) as [Hs|[Hw|Hb]].
      + apply Hns. unfold SLOT_STACK. exact Hs.
      + destruct (lfr_iw_facts a Hw) as (_ & _ & _ & Ht). unfold LF_TOP in Ht. lia.
      + destruct (HPB a Hb) as (Hlo & _). lia. }
  split.
  { intros a Hli Hng. pose proof Hli as (Hi & _ & _ & He).
    pose proof (lfr_in_img_top B a SEG Hi) as Ht. unfold LF_TOP in Ht.
    destruct (lfr_outside_dec W a) as [O|NO].
    - destruct (EQ a ltac:(lia) O) as [E1 E2]. destruct (Himg a Hli Hng) as [F1 F2].
      split; [rewrite E1; exact F1 | tauto].
    - exfalso. destruct (HOUT a ltac:(lia) NO) as [Hs|[Hw|Hb]].
      + lia.
      + destruct Hw as [Hw|Hw].
        * exact (Hng (lfr_iw_glob a Hw)).
        * apply He. rewrite ER. unfold A_ERRNO, A_TP, ERRNO_TP_OFF. lia.
      + exact (proj2 (proj2 (HPB a Hb)) Hi). }
  split.
  { intros a k i Hin HnT Hi. rewrite <- (Hb0 a k i Hin HnT Hi).
    assert (Hb : In (a, k) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
    destruct (BLK a k i Hb Hi) as (_ & H1 & H2 & _ & H5).
    destruct (lfr_outside_dec W (a + i)) as [O|NO].
    - exact (proj1 (EQ (a + i) ltac:(lia) O)).
    - exfalso. destruct (HOUT (a + i) ltac:(lia) NO) as [Hs|[Hw|Hb']].
      + lia.
      + exact (H5 (proj1 (lfr_iw_facts _ Hw))).
      + destruct Hb' as (a' & k' & Hin' & Hx). destruct (Hhp _ Hin') as [Hhb _].
        pose proof (mr_blocks_disjoint B (aa_MR API) LAWS L A mem md HMR) as Hpw.
        pose proof (lfr_pw_perm ranges_disjoint ltac:(intros u v Huv; unfold ranges_disjoint in *; lia)
          _ _ HP Hpw) as Hpw'.
        pose proof (lfr_pw_app ranges_disjoint hb _ Hpw' (a', k') (a, k) Hhb Hin) as Hd.
        unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. lia. }
  split; [intros a Ha; apply WM'; exact (Hstw a Ha)|].
  split; [intros a Ha; apply WM'; exact (Herw a Ha)|].
  split.
  { intros i Hi. rewrite <- (Hgd i Hi). rewrite GOT.
    destruct (lfr_outside_dec W (0x208d8 + i)) as [O|NO].
    - exact (proj1 (EQ (0x208d8 + i) ltac:(lia) O)).
    - exfalso. destruct (HOUT (0x208d8 + i) ltac:(lia) NO) as [Hs|[Hw|Hb]].
      + lia.
      + unfold lfr_iw in Hw. lia.
      + apply (proj1 (proj2 (HPB _ Hb))). right. unfold static_owned. rewrite GOT. lia. }
  split; [rewrite SEG; exact MI'|].
  split; [exact Hres|]. split; [exact HP|]. split; [exact Hkept|].
  assert (HD : forall x, mf_head_addr link_mf x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x).
  { intros x Hx.
    assert (Hr : (0x74528 <= x < 0x74530) \/ (0x75530 <= x < 0x75538) \/ (0x95cc8 <= x < 0x95cd0)).
    { unfold mf_head_addr, link_mf in Hx. cbn [mf_sink_addr mf_say_addr] in Hx. rewrite OFH in Hx. lia. }
    assert (Hi : in_img B x).
    { destruct Hr as [R|[R|R]];
        [exact (lfr_img_rng _ _ lfr_chk_h1 x R) | exact (lfr_img_rng _ _ lfr_chk_h2 x R)
        | exact (lfr_img_rng _ _ lfr_chk_h3 x R)]. }
    pose proof (lfr_in_img_top B x SEG Hi) as Ht. unfold LF_TOP in Ht.
    destruct (lfr_outside_dec W x) as [O|NO]; [exact (proj1 (EQ x ltac:(lia) O))|].
    exfalso. destruct (HOUT x ltac:(lia) NO) as [Hs|[Hw|Hb]].
    + lia.
    + unfold lfr_iw in Hw. lia.
    + exact (proj2 (proj2 (HPB x Hb)) Hi). }
  destruct Hgi as [(Hh0 & HT) | (f & Hhf & HT & Hmf)].
  - left. split; [exact (mf_heads_frame B link_mf mem mem' 0 HD Hh0) | exact HT].
  - right. exists f. split; [exact (mf_heads_frame B link_mf mem mem' f HD Hhf)|]. split; [exact HT|].
    apply (memfile_at_frame B link_mf mem mem' f); [|exact Hmf].
    intros x Hx.
    assert (HfT : In (f, MF_BLOCK) T) by (rewrite HT; left; reflexivity).
    pose proof (TB _ HfT) as HfB.
    destruct (BLK f MF_BLOCK (x - f) HfB ltac:(unfold MF_BLOCK, MF_ZEROED in *; lia)) as (_ & H1 & H2 & _ & H5).
    replace (f + (x - f)) with x in H5 by lia.
    destruct (lfr_outside_dec W x) as [O|NO];
      [exact (proj1 (EQ x ltac:(unfold MF_BLOCK, MF_ZEROED in *; lia) O))|].
    exfalso. destruct (HOUT x ltac:(unfold MF_BLOCK, MF_ZEROED in *; lia) NO) as [Hs|[Hw|Hb]].
    + unfold MF_BLOCK, MF_ZEROED in *. lia.
    + exact (H5 (proj1 (lfr_iw_facts x Hw))).
    + destruct Hb as (a' & k' & Hin' & Hx'). destruct (Hhp _ Hin') as [Hhb HnT].
      assert (Hb' : In (a', k') (blocks L A))
        by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hhb).
      assert (Hne : (a', k') <> (f, MF_BLOCK)) by (intros E; rewrite E in HnT; exact (HnT HfT)).
      destruct (lfr_pw_in2 ranges_disjoint (blocks L A) _ _ (mr_blocks_disjoint B (aa_MR API) LAWS L A mem md HMR)
        Hb' HfB Hne) as [Hd|Hd];
        unfold ranges_disjoint in Hd; cbn [fst snd] in Hd; unfold MF_BLOCK, MF_ZEROED in *; lia.
Qed.

(* ==========================================================================
   5. cut_evt: a segment from a cut to the next (S-FR item 5)
   ========================================================================== *)

Lemma cut_lgv : forall g pc hb T P c, CUT B API g pc hb T P c -> LGV B API g.
Proof. intros g pc hb T P c (fx' & L & A & regs & mem & md & _ & _ & (HGV & _) & _). exact HGV. Qed.

Lemma cut_evt : forall g pc hb T hp (P : machine_state -> Prop) pc' (P' : machine_state -> Prop) c,
  CUT B API g pc hb T P c ->
  (forall t, In t hp -> In t hb /\ ~ In t T) ->
  (forall ms, P ms -> evt rsegs (eqv_cl (fun ms' => P' ms' /\ seg_fp (lg_S g) hp (ms_mem ms) (ms_mem ms'))) ms) ->
  (forall ms', P' ms' -> exists R F fc m, ms' = MS R F (Z_to_bv 64 pc') fc None m (seg_rom rsegs) /\ frm0 fc) ->
  SR (ms_segs B) c (CUT B API g pc' hb T P').
Proof.
  intros g pc hb T hp P pc' P' c HC Hhp Hseg Hform.
  pose proof (lff_segs B API FF) as SEG.
  apply (cut_open B API g pc hb T P c _ HC).
  intros fx' L A regs mem md Hf HL (c0 & HP0 & Heq0).
  pose proof HL as (_ & HMR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
  destruct (mr_model B (aa_MR API) (aa_laws API) L A mem md HMR) as (Hh & Hl & _).
  rewrite SEG in Hro |- *.
  refine (lfr_run fx' regs pc mem md
    (fun a => exists c1, eqv_cl (fun ms' => P' ms' /\ seg_fp (lg_S g) hp (ms_mem c0) (ms_mem ms')) c1 /\
       Regs6ss.ms_eqv c1 a)
    _ Hh Hl Hro _ _ _).
  - exact (RegisterBridge.evt_register_transport rsegs _ c0 _ Heq0 (Hseg c0 HP0)).
  - intros ms (c1 & (c2 & (HP2 & _) & E21) & E1).
    destruct (Hform c2 HP2) as (R & F & fc & m & -> & _).
    pose proof (lfr_ms_eqv_trans _ _ _ E21 E1) as E.
    exists (ms_regs ms), F, (Z_to_bv 64 pc'), fc, m. exact (lfr_eqv_MS _ _ _ _ _ _ _ ms E).
  - intros R F pc1 fc m0' (c1 & (c2 & (HP2 & Hfp) & E21) & E1) m' Hrel' Hsame.
    pose proof (lfr_ms_eqv_trans _ _ _ E21 E1) as E.
    destruct (Hform c2 HP2) as (R2 & F2 & fc2 & m2 & E2 & Hfz). subst c2.
    pose proof E as (_ & EF & Epc & _ & _ & Efc & Em & _).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in EF, Epc, Efc, Em.
    subst F2 pc1 fc2 m2.
    destruct Hfp as (W & MU0 & WM0 & Hown).
    pose proof Heq0 as (_ & _ & _ & _ & _ & _ & Em0 & _).
    change (ms_mem c0 = normalize_cj rsegs mem) in Em0.
    assert (MU1 : Frame.munch W (normalize_cj rsegs mem) m0') by (rewrite <- Em0; exact MU0).
    assert (WM1 : Frame.wmono rsegs (normalize_cj rsegs mem) m0') by (rewrite <- Em0; exact WM0).
    pose proof (mem_rel_cj_normalize rsegs mem Hro) as HR0.
    pose proof (munch_rel_cj rsegs W mem (normalize_cj rsegs mem) m' m0' HR0 Hrel' Hsame MU1) as MU.
    pose proof (wmono_rel_cj rsegs mem (normalize_cj rsegs mem) m' m0' HR0 Hrel' Hsame WM1) as WM.
    pose proof (ro_agree_same_cj rsegs mem m' Hro Hsame) as MI'.
    pose proof (lfr_own g hb T hp L A mem md m' W HL Hhp MU WM MI' Hown) as HL'.
    apply SR_ret.
    rewrite <- SEG.
    apply (cut_close B API (mkFP F fc) g pc' hb T P' L A R m' md); [exact Hfz | exact HL' |].
    assert (Hn : normalize_cj rsegs m' = m0') by (extensionality a; symmetry; exact (proj1 Hrel' a)).
    unfold lcanon. rewrite Hn.
    exists (MS R2 F (Z_to_bv 64 pc') fc None m0' (seg_rom rsegs)). split; [exact HP2 | exact E].
Qed.

(* cut_evt with a disjunctive end: a segment that ends at one of two cut points (an arm's tail: the next
   loop head or the exit; E0 / E2 of the entry) *)
Lemma cut_evt_or : forall g pc hb T hp (P : machine_state -> Prop) pc1 (P1 : machine_state -> Prop)
    pc2 (P2 : machine_state -> Prop) c,
  CUT B API g pc hb T P c ->
  (forall t, In t hp -> In t hb /\ ~ In t T) ->
  (forall ms, P ms ->
     evt rsegs (eqv_cl (fun ms' => (P1 ms' \/ P2 ms') /\ seg_fp (lg_S g) hp (ms_mem ms) (ms_mem ms'))) ms) ->
  (forall ms', P1 ms' -> exists R F fc m, ms' = MS R F (Z_to_bv 64 pc1) fc None m (seg_rom rsegs) /\ frm0 fc) ->
  (forall ms', P2 ms' -> exists R F fc m, ms' = MS R F (Z_to_bv 64 pc2) fc None m (seg_rom rsegs) /\ frm0 fc) ->
  SR (ms_segs B) c (fun c' => CUT B API g pc1 hb T P1 c' \/ CUT B API g pc2 hb T P2 c').
Proof.
  intros g pc hb T hp P pc1 P1 pc2 P2 c HC Hhp Hseg Hf1 Hf2.
  pose proof (lff_segs B API FF) as SEG.
  apply (cut_open B API g pc hb T P c _ HC).
  intros fx' L A regs mem md Hf HL (c0 & HP0 & Heq0).
  pose proof HL as (_ & HMR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
  destruct (mr_model B (aa_MR API) (aa_laws API) L A mem md HMR) as (Hh & Hl & _).
  rewrite SEG in Hro |- *.
  refine (lfr_run fx' regs pc mem md
    (fun a => exists c1, eqv_cl (fun ms' => (P1 ms' \/ P2 ms') /\ seg_fp (lg_S g) hp (ms_mem c0) (ms_mem ms')) c1 /\
       Regs6ss.ms_eqv c1 a)
    _ Hh Hl Hro _ _ _).
  - exact (RegisterBridge.evt_register_transport rsegs _ c0 _ Heq0 (Hseg c0 HP0)).
  - intros ms (c1 & (c2 & (HP2 & _) & E21) & E1).
    pose proof (lfr_ms_eqv_trans _ _ _ E21 E1) as E.
    destruct HP2 as [HP2 | HP2];
      [destruct (Hf1 c2 HP2) as (R & F & fc & m & -> & _) | destruct (Hf2 c2 HP2) as (R & F & fc & m & -> & _)];
      exists (ms_regs ms), F; eexists; exists fc, m; exact (lfr_eqv_MS _ _ _ _ _ _ _ ms E).
  - intros R F pcx fc m0' (c1 & (c2 & (HP2 & Hfp) & E21) & E1) m' Hrel' Hsame.
    pose proof (lfr_ms_eqv_trans _ _ _ E21 E1) as E.
    pose proof E as (_ & _ & _ & _ & _ & _ & Emc & _).
    cbn [ms_mem MS] in Emc.
    destruct Hfp as (W & MU0 & WM0 & Hown). rewrite Emc in MU0, WM0.
    pose proof Heq0 as (_ & _ & _ & _ & _ & _ & Em0 & _).
    change (ms_mem c0 = normalize_cj rsegs mem) in Em0.
    assert (MU1 : Frame.munch W (normalize_cj rsegs mem) m0') by (rewrite <- Em0; exact MU0).
    assert (WM1 : Frame.wmono rsegs (normalize_cj rsegs mem) m0') by (rewrite <- Em0; exact WM0).
    pose proof (mem_rel_cj_normalize rsegs mem Hro) as HR0.
    pose proof (munch_rel_cj rsegs W mem (normalize_cj rsegs mem) m' m0' HR0 Hrel' Hsame MU1) as MU.
    pose proof (wmono_rel_cj rsegs mem (normalize_cj rsegs mem) m' m0' HR0 Hrel' Hsame WM1) as WM.
    pose proof (ro_agree_same_cj rsegs mem m' Hro Hsame) as MI'.
    pose proof (lfr_own g hb T hp L A mem md m' W HL Hhp MU WM MI' Hown) as HL'.
    assert (Hn : normalize_cj rsegs m' = m0') by (extensionality a; symmetry; exact (proj1 Hrel' a)).
    apply SR_ret.
    rewrite <- SEG.
    destruct HP2 as [HP2 | HP2].
    + destruct (Hf1 c2 HP2) as (R2 & F2 & fc2 & m2 & E2 & Hfz). subst c2.
      pose proof E as (_ & EF & Epc & _ & _ & Efc & Em & _).
      cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in EF, Epc, Efc, Em.
      subst F2 pcx fc2 m2.
      left. apply (cut_close B API (mkFP F fc) g pc1 hb T P1 L A R m' md); [exact Hfz | exact HL' |].
      unfold lcanon. rewrite Hn.
      exists (MS R2 F (Z_to_bv 64 pc1) fc None m0' (seg_rom rsegs)). split; [exact HP2 | exact E].
    + destruct (Hf2 c2 HP2) as (R2 & F2 & fc2 & m2 & E2 & Hfz). subst c2.
      pose proof E as (_ & EF & Epc & _ & _ & Efc & Em & _).
      cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in EF, Epc, Efc, Em.
      subst F2 pcx fc2 m2.
      right. apply (cut_close B API (mkFP F fc) g pc2 hb T P2 L A R m' md); [exact Hfz | exact HL' |].
      unfold lcanon. rewrite Hn.
      exists (MS R2 F (Z_to_bv 64 pc2) fc None m0' (seg_rom rsegs)). split; [exact HP2 | exact E].
Qed.

End LR.

Print Assumptions lfr_run.
Print Assumptions lfr_own.
Print Assumptions cut_evt.
Print Assumptions cut_evt_or.
