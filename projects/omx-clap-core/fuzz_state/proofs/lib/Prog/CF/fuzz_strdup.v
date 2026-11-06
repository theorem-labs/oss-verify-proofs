From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Step Cells.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import fuzz_malloc_c fuzz_strdup_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require strlen_c memcpy_c StrdupFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

Ltac sd_cs tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [tac .. |];
  let Hr' := fresh "Hr" in
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; tac.

Lemma sd_page_round_ge : forall x, x <= page_round x.
Proof.
  intros x. unfold page_round, PGSZ.
  pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma sd_uns64 : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma sd_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sd_segs_low : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 47) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sd_bytes_prefix : forall segs m a bs k, Mem.bytes_at segs m a bs -> Mem.bytes_at segs m a (firstn k bs).
Proof.
  intros segs m a bs k H. rewrite <- (firstn_skipn k bs) in H.
  exact (proj1 (proj1 (Mem.bytes_at_app segs m a _ _) H)).
Qed.

Lemma sd_pairwise_mid : forall {T} (R : T -> T -> Prop) b1 z b2, YO0f.pairwise R (b1 ++ z :: b2) ->
  (forall y, In y (b1 ++ b2) -> R z y \/ R y z).
Proof.
  intros T R b1; induction b1 as [|x t IH]; intros z b2 H y Hy; cbn in *.
  - destruct H as [H1 _]. left. apply H1, Hy.
  - destruct H as [H1 H2]. destruct Hy as [<-|Hy].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH z b2 H2 y Hy).
Qed.

Lemma sd_stk_norm : forall m lo hi, Frame.stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> Mem.ro_addr rsegs (Mem.wa a) = false) -> Frame.stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hr. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). specialize (Hr a Ha).
  unfold wview, Mem.mrd, normalize in *. cbv beta. rewrite Hr. split; [exact Hw | exists b; exact Hb].
Qed.

Lemma sd_stk_present : forall m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> present m a /\ Mem.ro_addr rsegs (Mem.wa a) = false) ->
  Frame.stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi H1 H2 H. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as ((b & Hb) & Hr).
  assert (E : normalize rsegs m (Mem.wa a) = Some b) by (unfold normalize; cbv beta; rewrite Hr; exact Hb).
  unfold wview, Mem.mrd. rewrite E. split; [discriminate | exists b; reflexivity].
Qed.

Section SD.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis HERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis HSTR : strlen_c.strlen_contract.
Hypothesis HMC : memcpy_c.memcpy_contract.
Hypothesis HFM : fuzz_malloc_contract B API F.

Lemma sd_img : img_low B.
Proof using HSEG.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite HSEG. vm_compute. reflexivity.
  - pose proof alloc_ceiling_value. lia.
Qed.

Lemma sd_seg_img : forall x seg, find_segment (ms_segs B) x 1 = Some seg -> in_img B x.
Proof using HSEG.
  intros x seg Hf. destruct (kb_find_segment (ms_segs B) x 1 seg Hf) as (Hin & Hlo & Hhi).
  pose proof sd_segs_low as HL. rewrite <- HSEG in HL. rewrite forallb_forall in HL.
  specialize (HL seg Hin). apply Z.leb_le in HL.
  split; [intros E; rewrite E in Hin; destruct Hin|].
  exists (segment_reservation seg). split; [unfold segments_reserved; apply in_map; exact Hin|].
  unfold segment_reservation, page_round_down_Z, page_round_up_Z, page_size. cbv zeta. cbn [fst snd].
  assert (E1 : 0 <= Z.of_N (seg_base seg) / 4096 * 4096 <= Z.of_N (seg_base seg)) by (Z.div_mod_to_equations; lia).
  assert (E2 : Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=
               (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) + 4096 - 1) / 4096 * 4096 < 2 ^ 48)
    by (Z.div_mod_to_equations; lia).
  rewrite !MState.unsigned_lit by lia. lia.
Qed.

Lemma sd_ro_img : forall a, 0 <= a < 2 ^ 64 -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> in_img B a.
Proof using HSEG.
  intros a Ha H. unfold Mem.ro_addr in H. rewrite MState.unsigned_lit in H by exact Ha.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:Hf; [|discriminate H].
  exact (sd_seg_img a seg Hf).
Qed.

Lemma sd_ro_low : forall a, 0 <= a < 2 ^ 64 -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = true -> a < alloc_ceiling.
Proof using HSEG.
  intros a Ha H. pose proof (proj1 sd_img a (sd_ro_img a Ha H)). lia.
Qed.

Lemma sd_present_of_wview : forall m (x : word), wview (ms_segs B) m x <> None -> ~ in_img B (bv_unsigned x) ->
  m x <> None.
Proof using HSEG.
  intros m x Hw Hi E. apply Hw. unfold wview. rewrite E.
  destruct (find_segment (ms_segs B) (bv_unsigned x) 1) as [seg|] eqn:Hf; [|reflexivity].
  exfalso. exact (Hi (sd_seg_img _ seg Hf)).
Qed.

Lemma sd_bytes_frame : forall m m' a bs, Mem.bytes_at (ms_segs B) m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  Mem.bytes_at (ms_segs B) m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) Hm. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). exact (Hm (Z.of_nat i) ltac:(lia)).
Qed.

Lemma sd_ledger_frame : forall L A m m' Lam peak cnt fail,
  ledger B L A m Lam peak cnt fail ->
  (forall a, alloc_statics a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 -> mbyte (ms_segs B) m' (a - 16 + i) = mbyte (ms_segs B) m (a - 16 + i)) ->
  ledger B L A m' Lam peak cnt fail.
Proof.
  intros L A m m' Lam peak cnt fail HL Hs Hh. unfold ledger, alloc_words in HL |- *.
  destruct HL as ((W1 & W2 & W3 & W4) & H1 & H2 & H3 & H4 & HF).
  split; [|split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 |]]]]].
  - split; [|split; [|split]].
    + apply (word_mem_frame (ms_segs B) m m' G_LIVE _ W1). intros k Hk. apply Hs.
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
    + apply (word_mem_frame (ms_segs B) m m' G_PEAK _ W2). intros k Hk. apply Hs.
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
    + apply (word_mem_frame (ms_segs B) m m' G_COUNT _ W3). intros k Hk. apply Hs.
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
    + apply (word_mem_frame (ms_segs B) m m' G_FAIL _ W4). intros k Hk. apply Hs.
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
  - rewrite Forall_forall in HF |- *. intros [a k] Hin. destruct (HF _ Hin) as (Hk & Hb & Hw & Hi).
    cbn [fst snd] in *. unfold lblock.
    split; [exact Hk|]. split; [exact Hb|]. split; [|exact Hi].
    apply (word_mem_frame (ms_segs B) m m' (a - 16) k Hw). intros k0 Hk0. exact (Hh a k k0 Hin Hk0).
Qed.

Lemma sd_lam_blk : forall L A mem Lam peak cnt fail a k, ledger B L A mem Lam peak cnt fail -> In (a, k) Lam ->
  0 <= k /\ In (a - 16, k + 16) (blocks L A).
Proof.
  intros L A mem Lam peak cnt fail a k (_ & _ & _ & _ & _ & HF) Hin. rewrite Forall_forall in HF.
  destruct (HF _ Hin) as (Hk & Hb & _). split; assumption.
Qed.

Lemma sd_blocks_user : forall L A p k, In (p, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = p.
Proof.
  intros L A p k Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q k'] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst k'.
  exists q. split; [exact Hq | exact E1].
Qed.

Lemma sd_user_blocks_in : forall L A q k, In (q, k) (user_blocks A) -> In (ptr_addr L q, k) (blocks L A).
Proof. intros L A q k H. unfold blocks. apply in_map_iff. exists (q, k). split; [reflexivity | exact H]. Qed.

Lemma sd_blk_range : forall L A mem md p k, aa_MR API L A mem md -> In (p, k) (blocks L A) ->
  4096 <= p /\ p + k <= alloc_ceiling.
Proof.
  intros L A mem md p k HM Hin. destruct (sd_blocks_user L A p k Hin) as (q & Hq & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L A mem md q k HM Hq).
Qed.

Lemma sd_old_new : forall L A L' A' m md b1 b2 r k, aa_MR API L' A' m md ->
  blocks L' A' = b1 ++ (r, k) :: b2 -> blocks L A = b1 ++ b2 ->
  forall a k', In (a, k') (blocks L A) -> a + k' <= r \/ r + k <= a.
Proof.
  intros L A L' A' m md b1 b2 r k HM Hbl' Hbl a k' Hin.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L' A' m md HM) as Hd. rewrite Hbl' in Hd.
  rewrite Hbl in Hin. destruct (sd_pairwise_mid _ b1 (r, k) b2 Hd _ Hin) as [D|D];
    unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
Qed.

Lemma sd_mid_shrink : forall K sp L A mem md (E E' : Z -> Prop) L' A' mem' md',
  kb_mid B API K sp L A mem md E L' A' mem' md' ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> E a -> E' a) ->
  kb_mid B API K sp L A mem md E' L' A' mem' md'.
Proof.
  intros K sp L A mem md E E' L' A' mem' md' (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) HE.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H7|]. split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho Ho' Hs He. apply H8; [exact Ha | exact Ho | exact Ho' | exact Hs |].
  intros Hx. exact (He (HE a Ha Hx)).
Qed.

Lemma sd_norm_post : forall (Q : machine_state -> Prop) m ms,
  (forall s0, Q s0 -> exists R pc m0, s0 = MState.MS R fp_regs pc fp_csr None m0 (seg_rom rsegs)) ->
  (exists s0, Q s0 /\ ms_rel rsegs ms s0 /\ ro_same rsegs m (ms_mem ms)) ->
  exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\
    (exists s0, Q s0 /\ ms_rel rsegs (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs)) s0 /\
       ro_same rsegs m mem').
Proof.
  intros Q m ms HS (s0 & HQ & Hrel & Hsame).
  destruct (HS s0 HQ) as (R & pc & m0 & ->).
  destruct ms as [R' F' pc' svc' rv' fc' m' ro'].
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MState.MS] in *. subst.
  exists R, pc, m'. split; [reflexivity|]. exists (MState.MS R fp_regs pc fp_csr None m0 (seg_rom rsegs)).
  split; [exact HQ|]. split; [|exact Hsame].
  refine (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl _))))))).
  exact HR.
Qed.

Theorem fuzz_strdup_holds : fuzz_strdup_contract B API F.
Proof using HSEG HERR HSTR HMC HFM.
  unfold fuzz_strdup_contract.
  intros L A regs mem md s cs slack b Lam peak cnt fail Hpre Ha0 Hbs Hnz Hal Hnw Hloc HL Hro Hres Hroom HN.
  pose proof sd_img as HIL.
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  assert (HAS : ALLOC_STACK = 8192) by reflexivity.
  set (SP := spZ regs) in *.
  assert (ES' : spZ regs = SP) by reflexivity.
  assert (ES : bv_unsigned (getr regs 2) = SP) by reflexivity.
  rewrite ES in Hnw, Hloc.
  assert (Hsp : getr regs 2 = Z_to_bv 64 SP) by (unfold SP, spZ; symmetry; apply Step.Z_to_bv_lit_self).
  set (N := Z.of_nat (length cs)) in *.
  assert (EN : N = Z.of_nat (length cs)) by reflexivity.
  pose proof (Mem.bytes_at_bound _ mem s _ Hbs) as HBb. rewrite length_app in HBb. cbn [length] in HBb.
  set (r := (- (s + N + 1)) mod 8) in *.
  assert (Hr : 0 <= r < 8) by (unfold r; apply Z.mod_pos_bound; lia).
  set (sl := firstn (Z.to_nat r) slack).
  assert (Hsl : Z.of_nat (length sl) = r) by (unfold sl; rewrite firstn_length_le by lia; lia).
  assert (HD : s + N + 1 + r <= SP - 8256 \/ SP <= s).
  { destruct (Z_lt_le_dec s SP) as [h|h]; [left|right; exact h].
    assert (Hz : s + N < SP - 8256).
    { destruct (Z_lt_le_dec (s + N) (SP - 8256)) as [h2|h2]; [exact h2|]. exfalso.
      apply (Hnw (Z.min (s + N) (SP - 1))); [lia|]. rewrite HAS. lia. }
    unfold r. Z.div_mod_to_equations. lia. }
  assert (Hbs2 : Mem.bytes_at (ms_segs B) mem s (cs ++ Z_to_bv 8 0 :: sl)).
  { replace (cs ++ Z_to_bv 8 0 :: sl) with (firstn (length cs + Datatypes.S (Z.to_nat r)) (cs ++ Z_to_bv 8 0 :: slack)).
    - apply sd_bytes_prefix. exact Hbs.
    - rewrite firstn_app, firstn_all2 by lia. f_equal.
      replace (length cs + Datatypes.S (Z.to_nat r) - length cs)%nat with (Datatypes.S (Z.to_nat r)) by lia. reflexivity. }
  assert (Hcs0 : Mem.bytes_at (ms_segs B) mem s (cs ++ [Z_to_bv 8 0])).
  { replace (cs ++ [Z_to_bv 8 0]) with (firstn (length cs + 1) (cs ++ Z_to_bv 8 0 :: slack)).
    - apply sd_bytes_prefix. exact Hbs.
    - rewrite firstn_app, firstn_all2 by lia. f_equal.
      replace (length cs + 1 - length cs)%nat with 1%nat by lia. reflexivity. }
  assert (Hro' : ro_agree rsegs mem) by (rewrite <- HSEG; exact Hro).
  assert (HK : Frame.stk (ms_segs B) mem (SP - (ALLOC_STACK + 64)) SP)
    by (apply (kb_stk B API HIL _ L A regs mem md Hpre); lia).
  assert (HK32 : Frame.stk rsegs (normalize rsegs mem) (SP + -32) SP).
  { apply sd_stk_norm.
    - destruct (Frame.stk_split _ mem _ (SP + -32) SP HK ltac:(lia)) as [_ H]. rewrite <- HSEG. exact H.
    - intros a Ha. destruct (Mem.ro_addr rsegs (Mem.wa a)) eqn:E; [|reflexivity]. exfalso.
      rewrite <- HSEG in E. pose proof (sd_ro_low a ltac:(lia) E). lia. }
  assert (Hwmk : forall a, (spZ regs - (ALLOC_STACK + 64) <= a < spZ regs) \/ (errno_addr B <= a < errno_addr B + 4) ->
      writable_at (ms_segs B) mem a) by (intros a [Ha|Ha]; [apply Hstk; exact Ha | apply Herr; exact Ha]).
  destruct (kb_md B API L A mem md HMR) as (Hh & Hz).
  apply (kb_run B regs _ mem md
    (fun R pc' mem' => exists s0, StrdupFacts.sd1_post (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 8)
        (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
        (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) fp_regs fp_csr (normalize rsegs mem) SP s N s0 /\
      ms_rel rsegs (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs)) s0 /\ ro_same rsegs mem mem') _ Hh Hz).
  { unfold rmk. rewrite Hsp, Ha0, HSEG. unfold FUZZ_STRDUP.
    eapply Exec.evt_mono.
    - eapply (evt_normalize rsegs); [exact sd_wx | exact Hro' |].
      apply (StrdupFacts.sd1 (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15)
        (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
        (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
        (getr regs 30) (getr regs 31) fp_regs fp_csr (normalize rsegs mem) SP s cs sl).
      + exact HSTR.
      + lia.
      + lia.
      + exact HK32.
      + apply bytes_at_normalize; [exact Hro' | rewrite <- HSEG; exact Hbs2].
      + exact Hnz.
      + rewrite Hsl. exact (Z.le_refl r).
      + lia.
      + apply mem_inv_normalize.
    - intros ms Hp. apply (sd_norm_post _ mem ms); [|exact Hp].
      intros s0 Hs0. exact (StrdupFacts.sd1_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s0 Hs0). }
  intros R pc1 mem1 regs1 HK1 Hg1.
  destruct HK1 as (s0 & Hp & Hrel & Hsame1).
  destruct Hp as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0 &
                  HM0 & HW0 & HI0 & HB8 & HB16 & HB24 & E0).
  subst s0.
  destruct Hrel as (ER & _ & EP & _ & _ & _ & _ & HR1).
  cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, HR1. subst R pc1.
  assert (HRn : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; exact Hro').
  assert (HM1 : Frame.munch [(SP + -32, SP)] mem mem1) by exact (munch_rel rsegs _ mem _ mem1 m0 HRn HR1 Hsame1 HM0).
  assert (HW1r : Frame.wmono rsegs mem mem1) by exact (wmono_rel rsegs mem _ mem1 m0 HRn HR1 Hsame1 HW0).
  assert (HW1 : Frame.wmono (ms_segs B) mem mem1) by (rewrite HSEG; exact HW1r).
  assert (Hro1r : ro_agree rsegs mem1) by exact (ro_agree_same rsegs mem mem1 Hro' Hsame1).
  assert (B8 : Mem.bytes_at rsegs mem1 (SP + -8) (Mem.le8 (getr regs 1)))
    by exact (proj2 (bytes_at_rel rsegs mem1 m0 _ _ HR1) HB8).
  assert (B16 : Mem.bytes_at rsegs mem1 (SP + -16) (Mem.le8 (getr regs 8)))
    by exact (proj2 (bytes_at_rel rsegs mem1 m0 _ _ HR1) HB16).
  assert (B24 : Mem.bytes_at rsegs mem1 (SP + -24) (Mem.le8 (getr regs 9)))
    by exact (proj2 (bytes_at_rel rsegs mem1 m0 _ _ HR1) HB24).
  clear HM0 HW0 HI0 HB8 HB16 HB24.
  assert (Hcond : forall x, 0 <= x < alloc_ceiling ->
      (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
      Frame.outside [(SP + -32, SP)] x) by (intros x Hx _; cbn [Frame.outside]; split; [lia | exact I]).
  assert (HMR1 : aa_MR API L A mem1 md) by exact (kb_MR_A B API L A mem mem1 md _ HMR HM1 Hcond).
  assert (Hkeep1 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
      mbyte (ms_segs B) mem1 (a + i) = mbyte (ms_segs B) mem (a + i))
    by exact (kb_blocks_munch B API L A mem mem1 md _ HMR HM1 Hcond).
  assert (Hout1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SP + -32 <= a < SP) ->
      mbyte (ms_segs B) mem1 a = mbyte (ms_segs B) mem a).
  { intros a Ha Hn. apply (KindBGlue.mbyte_munch (ms_segs B) _ mem mem1 a HM1 Ha).
    cbn [Frame.outside]. split; [exact Hn | exact I]. }
  assert (HL1 : ledger B L A mem1 Lam peak cnt fail).
  { apply (sd_ledger_frame L A mem mem1 Lam peak cnt fail HL).
    - intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. apply Hout1; lia.
    - intros a k i Hin Hi. destruct (sd_lam_blk L A mem Lam peak cnt fail a k HL Hin) as (Hk & Hb).
      destruct (sd_blk_range L A mem md _ _ HMR Hb). apply Hout1; lia. }
  assert (Hgk1 : forall i, 0 <= i < 8 ->
      mbyte (ms_segs B) mem1 (ms_got_guard B + i) = mbyte (ms_segs B) mem (ms_got_guard B + i)).
  { intros i Hi. assert (Ho : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
    pose proof (mr_owned_low _ _ (aa_laws API) L A mem md _ HMR Ho). apply Hout1; lia. }
  assert (Hlibc1 : forall i, 0 <= i < 8 ->
      mbyte (ms_segs B) mem1 (ms_libc B + 8 + i) = mbyte (ms_segs B) mem (ms_libc B + 8 + i)).
  { intros i Hi. assert (Ho : owned B L A (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
    pose proof (mr_owned_low _ _ (aa_laws API) L A mem md _ HMR Ho). apply Hout1; lia. }
  assert (G1 : getr regs1 1 = Z_to_bv 64 0x14190) by (rewrite Hg1; reflexivity).
  assert (G2 : getr regs1 2 = Z_to_bv 64 (SP + -32)) by (rewrite Hg1; reflexivity).
  assert (G8 : getr regs1 8 = Z_to_bv 64 s) by (rewrite Hg1; reflexivity).
  assert (G9 : getr regs1 9 = Z_to_bv 64 (N + 1)) by (rewrite Hg1; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (N + 1)) by (rewrite Hg1; reflexivity).
  assert (Hs1 : spZ regs1 = SP - 32) by (unfold spZ; rewrite G2, sd_uns64, Z.mod_small by lia; lia).
  eapply SR_bind; [apply (HFM L A regs1 mem1 md (N + 1) b Lam peak cnt fail) |].
  { eapply (kb_pre_A B API (ALLOC_STACK + 64) 32 (ALLOC_STACK + 32) L A regs mem md regs1 mem1);
      [exact Hpre | lia | lia | lia | rewrite Hs1; reflexivity | | rewrite Hg1; reflexivity | | exact HM1 | exact HW1 | |
       exact Hcond].
    - rewrite Hs1. replace (SP - 32) with (SP + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
    - rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
    - intros x Hx Hs. cbn [Frame.outside]. split; [lia | exact I]. }
  { exact G10. }
  { lia. }
  { exact HL1. }
  { rewrite HSEG. exact Hro1r. }
  { exact Hres. }
  { replace (N + 1 + 16) with (N + 17) by lia. exact Hroom. }
  { lia. }
  intros c2 Hc2.
  destruct Hc2 as (L' & A' & regs2 & m2 & md' & res & -> & Hro2 & Hgk2 & Hinit & Hlc2 & Hpost & Hreg & Hr0 & Hkeep2 &
                   Hub & Harm).
  pose proof Hpost as (HMR2 & HWF2 & Hbd2 & Hle2 & Hptr2 & Hp12 & (vm' & Emd) & Hfr2 & Hblk2 & Hscr2).
  assert (Hro2r : ro_agree rsegs m2) by (rewrite <- HSEG; exact Hro2).
  assert (Hrc : res <= alloc_ceiling).
  { destruct Harm as [(_ & -> & _) | (_ & _ & _ & _ & _ & _ & _ & (b1 & b2 & Hbl' & _) & _)]; [lia|].
    assert (Hin : In (res - 16, N + 1 + 16) (blocks L' A')) by (rewrite Hbl'; apply in_or_app; right; left; reflexivity).
    destruct (sd_blk_range L' A' m2 md' _ _ HMR2 Hin). lia. }
  assert (Hfs : forall a, SP + -32 <= a < 2 ^ 64 ->
      mbyte (ms_segs B) m2 a = mbyte (ms_segs B) mem1 a /\
      (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha. apply Hfr2.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem1 md a HMR1 Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L' A' m2 md' a HMR2 Ho). lia.
    - unfold scratch_k. rewrite Hs1. lia.
    - unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia. }
  assert (Hsb : forall a v, SP + -32 <= a -> a + 8 <= SP -> Mem.bytes_at rsegs mem1 a (Mem.le8 v) ->
      Mem.bytes_at rsegs m2 a (Mem.le8 v)).
  { intros a v Ha1 Ha2 Hb. rewrite <- HSEG in Hb |- *. apply (sd_bytes_frame mem1 m2 a _ Hb).
    intros i Hi. rewrite Mem.length_le8 in Hi. apply Hfs. lia. }
  pose proof (Hsb (SP + -8) _ ltac:(lia) ltac:(lia) B8) as C8.
  pose proof (Hsb (SP + -16) _ ltac:(lia) ltac:(lia) B16) as C16.
  pose proof (Hsb (SP + -24) _ ltac:(lia) ltac:(lia) B24) as C24.
  assert (G2' : getr regs2 2 = Z_to_bv 64 (SP + -32)) by (rewrite <- G2; apply (Hp12 2); unfold callee_saved; lia).
  assert (G8' : getr regs2 8 = Z_to_bv 64 s) by (rewrite <- G8; apply (Hp12 8); unfold callee_saved; lia).
  assert (G9' : getr regs2 9 = Z_to_bv 64 (N + 1)) by (rewrite <- G9; apply (Hp12 9); unfold callee_saved; lia).
  rewrite G1.
  destruct (kb_md B API L' A' m2 md' HMR2) as (Hh2 & Hz2).
  destruct Harm as [(Hcf & -> & HLe & HAe & Hmde & Hresb & Hwo & Hbl & HL2) |
                    (Hcf & Hrnz & Hr16 & Hres' & Hrst & Hrimg & Hnin & (b1 & b2 & Hbl' & Hbl) & HL2)].
  - apply (kb_run B regs2 _ m2 md'
      (fun R pc' mem' => StrdupFacts.sd2n_post (getr regs 1) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6)
         (getr regs2 7) (getr regs 8) (getr regs 9) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14)
         (getr regs2 15) (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19) (getr regs2 20) (getr regs2 21)
         (getr regs2 22) (getr regs2 23) (getr regs2 24) (getr regs2 25) (getr regs2 26) (getr regs2 27) (getr regs2 28)
         (getr regs2 29) (getr regs2 30) (getr regs2 31) fp_regs fp_csr m2 SP
         (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs))) _ Hh2 Hz2).
    { unfold rmk. rewrite G2', Hr0, HSEG.
      eapply Exec.evt_mono.
      - apply (StrdupFacts.sd2n (getr regs2 1) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7)
          (getr regs2 8) (getr regs2 9) (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14) (getr regs2 15)
          (getr regs2 16) (getr regs2 17) (getr regs2 18) (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22)
          (getr regs2 23) (getr regs2 24) (getr regs2 25) (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29)
          (getr regs2 30) (getr regs2 31) (getr regs 1) (getr regs 8) (getr regs 9) fp_regs fp_csr m2 SP);
          [lia | lia | exact C8 | exact C16 | exact C24].
      - intros ms Hp. pose proof Hp as E. unfold StrdupFacts.sd2n_post in E. subst ms.
        do 3 eexists. split; [reflexivity | exact Hp]. }
    intros R pc3 mem3 regs3 HK3 Hg3.
    unfold StrdupFacts.sd2n_post in HK3.
    pose proof (f_equal ms_regs HK3) as ER. pose proof (f_equal ms_pc_val HK3) as EP. pose proof (f_equal ms_mem HK3) as EM.
    cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM. subst R pc3 mem3. clear HK3.
    apply SR_ret. exists L', A', regs3, m2, md', 0.
    rewrite (kb_ret_pc _ Hra).
    split; [reflexivity|].
    split; [exact Hro2|].
    split; [intros i Hi; rewrite (Hgk2 i Hi); exact (Hgk1 i Hi)|].
    split; [exact Hinit|].
    split; [intros Hd i Hi; rewrite (Hlc2 Hd i Hi); exact (Hlibc1 i Hi)|].
    split.
    { apply (kb_post B API).
      - apply (kb_mid_E B API _ _ _ _ _ _ (fun a => False \/ alloc_writes 0 a)); [|intros a [[]|Ha]; exact Ha].
        eapply (kb_mid_seqAX B API).
        + eapply (kb_mid_A B API HIL); [exact HMR | exact HWF | exact Hbd | exact Hwmk | exact HM1 | exact HW1 | |
            exact Hcond].
          intros x Hx Hs He. cbn [Frame.outside]. split; [lia | exact I].
        + exact (proj1 (kb_mid_call B API _ L A regs1 mem1 md _ L' A' regs2 m2 md' Hpost)).
        + rewrite Hs1. lia.
        + rewrite Hs1. lia.
        + lia.
        + lia.
        + rewrite Hs1. intros a Ha1 Ha2. unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
      - sd_cs ltac:(rewrite Hg3; first
          [ reflexivity
          | exact (eq_sym Hsp)
          | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
              transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
              rewrite (Hp12 k ltac:(unfold callee_saved; lia)), Hg1; reflexivity end ]). }
    split; [exact Hreg|].
    split; [rewrite Hg3; reflexivity|].
    split; [intros a k i Hin Ha Hi; rewrite (Hkeep2 a k i Hin Ha Hi); exact (Hkeep1 a k i Hin Hi)|].
    split; [exact Hub|].
    left. split; [exact Hcf|]. split; [reflexivity|]. split; [exact HLe|]. split; [exact HAe|]. split; [exact Hmde|].
    split; [exact Hresb|].
    split.
    { intros a Ha Hn. rewrite ES in Hn.
      rewrite (Hwo a Ha).
      - apply Hout1; [exact Ha|]. intros Hx. apply Hn. right. lia.
      - rewrite G2, sd_uns64, Z.mod_small by lia. intros [Hx|Hx]; apply Hn; [left; exact Hx | right; lia]. }
    split; [exact Hbl|]. exact HL2.
  - assert (Hnb : In (res - 16, N + 1 + 16) (blocks L' A')) by (rewrite Hbl'; apply in_or_app; right; left; reflexivity).
    destruct (sd_blocks_user L' A' _ _ Hnb) as (q & Hq & Eq).
    assert (Hpres : forall i, 0 <= i < N + 1 + 16 -> present m2 (res - 16 + i) /\ ~ owned B L' A' (res - 16 + i)).
    { intros i Hi. destruct (mr_blocks _ _ (aa_laws API) L' A' m2 md' q (N + 1 + 16) i HMR2 Hq Hi) as (P1 & _ & _ & P4).
      rewrite Eq in P1, P4. split; assumption. }
    destruct (sd_blk_range L' A' m2 md' _ _ HMR2 Hnb) as (Hrl & Hrh).
    assert (Hold : forall a k, In (a, k) (blocks L A) -> a + k <= res - 16 \/ res - 16 + (N + 1 + 16) <= a)
      by exact (sd_old_new L A L' A' m2 md' b1 b2 (res - 16) (N + 1 + 16) HMR2 Hbl' Hbl).
    assert (Hcs2 : forall i, 0 <= i < N + 1 ->
        mbyte (ms_segs B) m2 (s + i) = mbyte (ms_segs B) mem (s + i) /\ ~ (res - 16 <= s + i < res + (N + 1))).
    { intros i Hi. destruct (Hloc (s + i) ltac:(lia)) as [Hst | [Hrd | (p & k & Hin & Hpk)]].
      - split; [|lia]. rewrite (proj1 (Hfs (s + i) ltac:(lia))). apply Hout1; lia.
      - split.
        + change (Mem.mrd (ms_segs B) m2 (Z_to_bv 64 (s + i)) = Mem.mrd (ms_segs B) mem (Z_to_bv 64 (s + i))).
          rewrite (Hro2 _ Hrd), (Hro _ Hrd). reflexivity.
        + intros Hx. apply (Hrimg (s + i - (res - 16))); [lia|].
          replace (res - 16 + (s + i - (res - 16))) with (s + i) by lia. apply sd_ro_img; [lia | exact Hrd].
      - pose proof (sd_blk_range L A mem md p k HMR Hin) as Hpr. pose proof (Hold p k Hin). split; [|lia].
        replace (s + i) with (p + (s + i - p)) by lia.
        rewrite (Hkeep2 p k (s + i - p) Hin ltac:(lia) ltac:(lia)). exact (Hkeep1 p k (s + i - p) Hin ltac:(lia)). }
    assert (Hsrc : Mem.bytes_at rsegs (normalize rsegs m2) s (cs ++ [Z_to_bv 8 0])).
    { apply bytes_at_normalize; [exact Hro2r|]. rewrite <- HSEG. apply (sd_bytes_frame mem m2 s _ Hcs0).
      intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. exact (proj1 (Hcs2 i ltac:(lia))). }
    assert (Hdj : s + (N + 1) <= res \/ res + (N + 1) <= s).
    { destruct (Z_le_gt_dec (s + (N + 1)) res) as [h|h]; [left; exact h|].
      destruct (Z_le_gt_dec (res + (N + 1)) s) as [h'|h']; [right; exact h'|]. exfalso.
      apply (proj2 (Hcs2 (Z.max s res - s) ltac:(lia))). lia. }
    assert (Hstkn : Frame.stk rsegs (normalize rsegs m2) res (res + (N + 1))).
    { apply sd_stk_present; [lia | lia |]. intros a Ha. destruct (Hpres (a - (res - 16)) ltac:(lia)) as (Hp & _).
      replace (res - 16 + (a - (res - 16))) with a in Hp by lia. split; [exact Hp|].
      destruct (Mem.ro_addr rsegs (Mem.wa a)) eqn:E; [|reflexivity]. exfalso.
      apply (Hrimg (a - (res - 16))); [lia|]. replace (res - 16 + (a - (res - 16))) with a by lia.
      apply sd_ro_img; [lia | rewrite HSEG; exact E]. }
    destruct (Frame.stk_carve rsegs _ res (res + (N + 1)) (Z.to_nat (N + 1)) Hstkn ltac:(lia)) as (_ & junk & Hjunk).
    replace (res + (N + 1) - Z.of_nat (Z.to_nat (N + 1))) with res in Hjunk by lia.
    apply (kb_run B regs2 _ m2 md'
      (fun R pc' mem' => exists s0, StrdupFacts.sd2c_post (getr regs 1) (getr regs2 3) (getr regs2 4) (getr regs 8)
         (getr regs 9) (getr regs2 18) (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23)
         (getr regs2 24) (getr regs2 25) (getr regs2 26) (getr regs2 27) fp_regs fp_csr (normalize rsegs m2) SP res (N + 1)
         (cs ++ [Z_to_bv 8 0]) s0 /\
         ms_rel rsegs (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs)) s0 /\ ro_same rsegs m2 mem') _ Hh2 Hz2).
    { unfold rmk. rewrite G2', G8', G9', Hr0, HSEG.
      eapply Exec.evt_mono.
      - eapply (evt_normalize rsegs); [exact sd_wx | exact Hro2r |].
        apply (StrdupFacts.sd2c (getr regs2 1) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7)
          (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17)
          (getr regs2 18) (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24)
          (getr regs2 25) (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)
          (getr regs 1) (getr regs 8) (getr regs 9) fp_regs fp_csr (normalize rsegs m2) SP s res (N + 1)
          (cs ++ [Z_to_bv 8 0]) junk).
        + exact HMC.
        + lia.
        + lia.
        + lia.
        + lia.
        + lia.
        + lia.
        + lia.
        + rewrite length_app. cbn [length]. lia.
        + apply bytes_at_normalize; [exact Hro2r | exact C8].
        + apply bytes_at_normalize; [exact Hro2r | exact C16].
        + apply bytes_at_normalize; [exact Hro2r | exact C24].
        + exact Hsrc.
        + exact Hjunk.
        + exact Hdj.
        + apply mem_inv_normalize.
      - intros ms Hp. apply (sd_norm_post _ m2 ms); [|exact Hp].
        intros s0 Hs0. exact (StrdupFacts.sd2c_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s0 Hs0). }
    intros R pc3 mem3 regs3 HK3 Hg3.
    destruct HK3 as (s0 & Hp & Hrel & Hsame3).
    destruct Hp as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m0' &
                    HM3 & HW3 & HI3 & HB3 & E3).
    subst s0.
    destruct Hrel as (ER & _ & EP & _ & _ & _ & _ & HR3).
    cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, HR3. subst R pc3.
    assert (HRn2 : mem_rel rsegs m2 (normalize rsegs m2)) by (apply mem_rel_normalize; exact Hro2r).
    assert (HM3' : Frame.munch [(res, res + (N + 1))] m2 mem3)
      by exact (munch_rel rsegs _ m2 _ mem3 m0' HRn2 HR3 Hsame3 HM3).
    assert (HW3r : Frame.wmono rsegs m2 mem3) by exact (wmono_rel rsegs m2 _ mem3 m0' HRn2 HR3 Hsame3 HW3).
    assert (HB3' : Mem.bytes_at rsegs mem3 res (cs ++ [Z_to_bv 8 0]))
      by exact (proj2 (bytes_at_rel rsegs mem3 m0' _ _ HR3) HB3).
    assert (Hro3 : ro_agree rsegs mem3) by exact (ro_agree_same rsegs m2 mem3 Hro2r Hsame3).
    clear HM3 HW3 HI3 HB3.
    assert (Hin3 : forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + (N + 1)) ->
        mbyte (ms_segs B) mem3 a = mbyte (ms_segs B) m2 a).
    { intros a Ha Hn. apply (KindBGlue.mbyte_munch (ms_segs B) _ m2 mem3 a HM3' Ha).
      cbn [Frame.outside]. split; [exact Hn | exact I]. }
    assert (HP3 : forall x, m2 x <> None -> mem3 x <> None).
    { intros x Hx. destruct (kb_outside_dec [(res, res + (N + 1))] (bv_unsigned x)) as [Ho|Ho].
      - rewrite (HM3' x Ho). exact Hx.
      - apply sd_present_of_wview.
        + rewrite HSEG. apply HW3r. unfold wview. destruct (m2 x) as [b0|] eqn:Ex; [discriminate | congruence].
        + cbn [Frame.outside] in Ho. intros Hi. apply (Hrimg (bv_unsigned x - (res - 16))); [lia|].
          replace (res - 16 + (bv_unsigned x - (res - 16))) with (bv_unsigned x) by lia. exact Hi. }
    apply SR_ret. exists L', A', regs3, mem3, md', res.
    rewrite (kb_ret_pc _ Hra).
    split; [reflexivity|].
    split; [rewrite HSEG; exact Hro3|].
    split.
    { intros i Hi. assert (Ho : owned B L' A' (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
      assert (Hn : ~ (res <= ms_got_guard B + i < res + (N + 1))).
      { intros Hx. apply (proj2 (Hpres (ms_got_guard B + i - (res - 16)) ltac:(lia))).
        replace (res - 16 + (ms_got_guard B + i - (res - 16))) with (ms_got_guard B + i) by lia. exact Ho. }
      pose proof (mr_owned_low _ _ (aa_laws API) L' A' m2 md' _ HMR2 Ho) as Hlo.
      rewrite (Hin3 (ms_got_guard B + i) ltac:(lia) Hn), (Hgk2 i Hi). exact (Hgk1 i Hi). }
    split; [exact Hinit|].
    split.
    { intros Hd i Hi. assert (Ho : owned B L' A' (ms_libc B + 8 + i)) by (right; unfold static_owned; right; right; left; lia).
      assert (Hn : ~ (res <= ms_libc B + 8 + i < res + (N + 1))).
      { intros Hx. apply (proj2 (Hpres (ms_libc B + 8 + i - (res - 16)) ltac:(lia))).
        replace (res - 16 + (ms_libc B + 8 + i - (res - 16))) with (ms_libc B + 8 + i) by lia. exact Ho. }
      pose proof (mr_owned_low _ _ (aa_laws API) L' A' m2 md' _ HMR2 Ho) as Hlo.
      rewrite (Hin3 (ms_libc B + 8 + i) ltac:(lia) Hn), (Hlc2 Hd i Hi). exact (Hlibc1 i Hi). }
    split.
    { apply (kb_post B API).
      - apply (sd_mid_shrink _ _ _ _ _ _ (fun a => (False \/ alloc_writes res a) \/ (res <= a < res + (N + 1)))).
        + eapply (kb_mid_tail B API HIL).
          * eapply (kb_mid_seqAX B API).
            -- eapply (kb_mid_A B API HIL); [exact HMR | exact HWF | exact Hbd | exact Hwmk | exact HM1 | exact HW1 | |
                 exact Hcond].
               intros x Hx Hs He. cbn [Frame.outside]. split; [lia | exact I].
            -- exact (proj1 (kb_mid_call B API _ L A regs1 mem1 md _ L' A' regs2 m2 md' Hpost)).
            -- rewrite Hs1. lia.
            -- rewrite Hs1. lia.
            -- lia.
            -- lia.
            -- rewrite Hs1. intros a Ha1 Ha2. unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. lia.
          * exact HM3'.
          * rewrite HSEG. exact HW3r.
          * exact HP3.
          * intros x Hx Hs He. cbn [Frame.outside]. split; [exact He | exact I].
          * intros x Hx Ho. cbn [Frame.outside]. split; [|exact I]. intros Hb.
            apply (proj2 (Hpres (x - (res - 16)) ltac:(lia))). replace (res - 16 + (x - (res - 16))) with x by lia.
            exact Ho.
          * intros p k i Hp _ Hi. pose proof (Hold _ _ (sd_user_blocks_in L A p k Hp)).
            cbn [Frame.outside]. split; [lia | exact I].
        + intros a Ha [[[]|Hw]|Hb]; [exact Hw|]. exfalso. destruct Ha as [Ha|Ha]; [lia|].
          apply (Hrimg (a - (res - 16))); [lia|]. replace (res - 16 + (a - (res - 16))) with a by lia. exact Ha.
      - sd_cs ltac:(rewrite Hg3; first
          [ reflexivity
          | exact (eq_sym Hsp)
          | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
              transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
              rewrite (Hp12 k ltac:(unfold callee_saved; lia)), Hg1; reflexivity end ]). }
    split; [exact Hreg|].
    split; [rewrite Hg3; reflexivity|].
    split.
    { intros a k i Hin Ha Hi. pose proof (Hold a k Hin). pose proof (sd_blk_range L A mem md a k HMR Hin).
      rewrite (Hin3 (a + i) ltac:(lia) ltac:(lia)), (Hkeep2 a k i Hin Ha Hi). exact (Hkeep1 a k i Hin Hi). }
    split; [exact Hub|].
    right. split; [exact Hcf|]. split; [exact Hrnz|]. split; [exact Hr16|].
    split; [replace (N + 17) with (N + 1 + 16) by lia; exact Hres'|].
    split; [exact Hrst|]. split; [exact Hrimg|]. split; [exact Hnin|].
    split; [rewrite HSEG; exact HB3'|].
    split; [exists b1, b2; split; [replace (N + 17) with (N + 1 + 16) by lia; exact Hbl' | exact Hbl]|].
    replace (lsum Lam + N + 1) with (lsum Lam + (N + 1)) by lia.
    apply (sd_ledger_frame L' A' m2 mem3 _ _ _ _ HL2).
    + intros a Ha. apply Hin3; [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha; lia|].
      intros Hx. apply (Hrst (a - (res - 16))); [lia|]. replace (res - 16 + (a - (res - 16))) with a by lia. exact Ha.
    + intros a k i Hin Hi. destruct Hin as [E|Hin].
      * injection E as <- <-. apply Hin3; lia.
      * destruct (sd_lam_blk L A mem Lam peak cnt fail a k HL Hin) as (Hk & Hb).
        pose proof (Hold _ _ Hb). pose proof (sd_blk_range L A mem md _ _ HMR Hb). apply Hin3; lia.
Qed.

End SD.
