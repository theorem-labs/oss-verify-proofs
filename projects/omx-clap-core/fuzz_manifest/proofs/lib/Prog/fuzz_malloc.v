From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require MState Mem Frame Exec Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger GIInit fuzz_malloc_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require MallocRuns.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require FrameAPI.
Import ListNotations.
Local Open Scope Z_scope.

Ltac cs_cases tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [tac .. |];
  let Hr' := fresh "Hr" in
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; tac.

Ltac out3 := cbn [Frame.outside]; refine (conj _ (conj _ (conj _ I))); lia.

Lemma page_round_ge : forall x, x <= page_round x.
Proof.
  intros x. unfold page_round, PGSZ.
  pose proof (Z.div_mod (x + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma uns64 : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma not_out : forall W a, ~ Frame.outside W a -> exists lo hi, In (lo, hi) W /\ lo <= a < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros a H; cbn in H; [exfalso; exact (H I)|].
  destruct (Z_lt_le_dec a lo) as [h1|h1]; [|destruct (Z_lt_le_dec a hi) as [h2|h2]].
  - destruct (IH a) as (lo' & hi' & Hin & Hb).
    + intros Ho. apply H. split; [lia | exact Ho].
    + exists lo', hi'. split; [right; exact Hin | exact Hb].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH a) as (lo' & hi' & Hin & Hb).
    + intros Ho. apply H. split; [lia | exact Ho].
    + exists lo', hi'. split; [right; exact Hin | exact Hb].
Qed.

Lemma in_G : forall x, (0x2f370 <= x < 0x2f388 \/ 0x1f0f8 <= x < 0x1f100) -> in_globals omx_G x.
Proof.
  intros x Hx. unfold in_globals. destruct Hx as [Hx|Hx].
  - destruct (Z_lt_le_dec x 0x2f378) as [h1|h1].
    + exists G_LIVE, 8. split; [apply in_eq | unfold G_LIVE; lia].
    + destruct (Z_lt_le_dec x 0x2f380) as [h2|h2].
      * exists G_PEAK, 8. split; [apply in_cons, in_eq | unfold G_PEAK; lia].
      * exists G_COUNT, 8. split; [apply in_cons, in_cons, in_eq | unfold G_COUNT; lia].
  - exists G_FAIL, 8. split; [apply in_cons, in_cons, in_cons, in_eq | unfold G_FAIL; lia].
Qed.

Section FM.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis HMAL : ms_malloc B = 0x14ce0.
Hypothesis HERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis HG : globals_free B API omx_G.
Hypothesis MALLOC : malloc_contract B API.

Lemma fm_img : img_low B.
Proof.
  apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite HSEG. vm_compute. reflexivity.
  - pose proof alloc_ceiling_value. lia.
Qed.

Lemma res_ok_up : forall A b k, res_ok_slots A b -> room_slots b k -> res_ok_slots A (sb_malloc b k).
Proof.
  intros A b k (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) (Hk & Hl & _).
  unfold res_ok_slots, sb_malloc. cbn [sb_live sb_bytes sb_cap].
  do 6 (split; [assumption|]). lia.
Qed.

Lemma lsum_nonneg : forall L A mem Lam, Forall (fun ak => lblock B L A mem (fst ak) (snd ak)) Lam -> 0 <= lsum Lam.
Proof.
  intros L A mem Lam H. induction H as [|[a k] t Hx Ht IH]; cbn [lsum]; [lia|].
  destruct Hx as (Hk & _). cbn [snd] in Hk. lia.
Qed.

Lemma blocks_user : forall L A p k, In (p, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = p.
Proof.
  intros L A p k Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q k'] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst k'.
  exists q. split; [exact Hq | exact E1].
Qed.

Lemma user_blocks_in : forall L A q k, In (q, k) (user_blocks A) -> In (ptr_addr L q, k) (blocks L A).
Proof. intros L A q k H. unfold blocks. apply in_map_iff. exists (q, k). split; [reflexivity | exact H]. Qed.

Lemma blk_range : forall L A mem md p k, aa_MR API L A mem md -> In (p, k) (blocks L A) ->
  4096 <= p /\ p + k <= alloc_ceiling.
Proof.
  intros L A mem md p k HM Hin. destruct (blocks_user L A p k Hin) as (q & Hq & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L A mem md q k HM Hq).
Qed.

Lemma word_mem_some : forall m a v x, word_mem (ms_segs B) m a v -> a <= x < a + 8 -> mbyte (ms_segs B) m x <> None.
Proof.
  intros m a v x H Hx. pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as E.
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia. rewrite E. discriminate.
Qed.

Lemma glob_img : forall x, in_globals omx_G x -> in_img B x.
Proof. intros x Hx. exact (proj1 (HG x Hx)). Qed.

Lemma glob_free_at : forall L A mem md x, aa_MR API L A mem md -> in_globals omx_G x ->
  (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) -> False.
Proof.
  intros L A mem md x HM Hx Ho. destruct (HG x Hx) as (_ & _ & _ & _ & Hm).
  destruct (Hm L A mem md HM) as (Hno & Hnb).
  destruct Ho as [Ho | (p & n & Hp & Hpx)]; [exact (Hno Ho) | exact (Hnb p n Hp Hpx)].
Qed.

Lemma avoid_gen : forall L A mem md W x, aa_MR API L A mem md ->
  (forall lo hi, In (lo, hi) W -> alloc_ceiling <= lo \/ (forall y, lo <= y < hi -> in_globals omx_G y)) ->
  0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
  Frame.outside W x.
Proof.
  intros L A mem md W x HM HW Hx Ho. apply kb_outside. intros lo hi Hin Hlh.
  destruct (HW lo hi Hin) as [Hl | Hg]; [lia | exact (glob_free_at L A mem md x HM (Hg x Hlh) Ho)].
Qed.

Lemma wr_W : forall W m, (forall a, 0 <= a < 2 ^ 64 -> (exists lo hi, In (lo, hi) W /\ lo <= a < hi) ->
    writable_at (ms_segs B) m a) ->
  forall x : word, ~ Frame.outside W (bv_unsigned x) -> wview (ms_segs B) m x <> None.
Proof.
  intros W m H x Hx. pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  specialize (H (bv_unsigned x) Hr (not_out W _ Hx)). unfold writable_at in H.
  rewrite Step.Z_to_bv_lit_self in H. exact H.
Qed.

Lemma bytes_frame : forall m m' a bs, Mem.bytes_at (ms_segs B) m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  Mem.bytes_at (ms_segs B) m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) Hm. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). exact (Hm (Z.of_nat i) ltac:(lia)).
Qed.

Lemma wr_frame : forall m a n, (forall i, 0 <= i < n -> writable_at (ms_segs B) m (a + i)) -> 0 <= a -> a + n <= 2 ^ 64 ->
  Mem.wr_at (ms_segs B) m a n.
Proof. intros m a n H H0 H1. split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (H i Hi). Qed.

Lemma present_mrd : forall m a, present m a -> exists b, Mem.mrd (ms_segs B) m (Mem.wa a) = Some b.
Proof. intros m a (b & Hb). exists b. unfold Mem.mrd, Mem.wa. rewrite Hb. reflexivity. Qed.

Lemma present_wr : forall m a, present m a -> writable_at (ms_segs B) m a.
Proof. intros m a (b & Hb). unfold writable_at, wview. rewrite Hb. discriminate. Qed.

Lemma seg_in_img : forall x seg, find_segment (ms_segs B) x 1 = Some seg -> in_img B x.
Proof.
  intros x seg E. destruct (kb_find_segment _ x 1 seg E) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun rr => (bv_unsigned (fst rr) <=? Z.of_N (seg_base s)) &&
      (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst rr) + bv_unsigned (snd rr)))
      (segments_reserved (ms_segs B))) (ms_segs B) = true) by (rewrite HSEG; vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C. destruct C as (rr & Hr & Hc).
  apply andb_prop in Hc as (Hc1 & Hc2). apply Z.leb_le in Hc1, Hc2.
  split; [intros E'; rewrite E' in Hin; destruct Hin | exists rr; split; [exact Hr | lia]].
Qed.

Lemma ro_false_seg : forall a, 0 <= a < 2 ^ 64 ->
  (exists seg, find_segment (ms_segs B) a 1 = Some seg /\ seg_writable seg = true) ->
  Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros a Ha (seg & E & Hw). unfold Mem.ro_addr. rewrite uns64, Z.mod_small by lia. rewrite E, Hw. reflexivity.
Qed.

Lemma ro_false_notimg : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hn. unfold Mem.ro_addr. rewrite uns64, Z.mod_small by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; exact (Hn (seg_in_img a seg E)) | reflexivity].
Qed.

Lemma ro_false_low : img_low B -> forall a, alloc_ceiling <= a < 2 ^ 64 -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros HIL a Ha. pose proof alloc_ceiling_value. unfold Mem.ro_addr. rewrite uns64, Z.mod_small by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; pose proof (proj2 HIL a seg E); lia | reflexivity].
Qed.

Lemma ro_agree_munch : forall W m m', ro_agree (ms_segs B) m -> Frame.munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside W a -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false) ->
  ro_agree (ms_segs B) m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold Mem.mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (HW (bv_unsigned a) Hr Ho) as E. rewrite Step.Z_to_bv_lit_self in E. congruence.
Qed.

Lemma guard_owned : forall L A x, ms_got_guard B <= x < ms_got_guard B + 8 -> owned B L A x.
Proof. intros L A x H. right. unfold static_owned. right; right; right; right; left. exact H. Qed.

Lemma libc8_owned : forall L A x, ms_libc B + 8 <= x < ms_libc B + 16 -> owned B L A x.
Proof. intros L A x H. right. unfold static_owned. right; right; left. exact H. Qed.

Theorem fuzz_malloc_holds : fuzz_malloc_contract B API.
Proof.
  unfold fuzz_malloc_contract.
  intros L A regs mem md n b Lam peak cnt fail Hpre Ha0 Hn0 HL Hro Hres Hroom.
  pose proof fm_img as HIL.
  pose proof Hpre as (HMR & HWF & Hbd & Hra & Hsp16 & Hspc & Hsp63 & Hstk & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hceil.
  assert (HAS : ALLOC_STACK = 8192) by reflexivity.
  set (S := spZ regs) in *.
  assert (Hsp : getr regs 2 = Z_to_bv 64 S) by (unfold S, spZ; symmetry; apply Step.Z_to_bv_lit_self).
  assert (Hn : n + 16 <= 2 ^ 30).
  { pose proof (room_slots_req b (n + 16) Hroom) as Hpr. pose proof (page_round_ge (n + 16 + IB + UNIT)).
    unfold IB, UNIT, MG_REQ, PGSZ in *. lia. }
  pose proof HL as (HW0 & Hpk & Hc & Hf & HND & HFL).
  pose proof HW0 as (HLv & HPk & HCt & HFl).
  pose proof (lsum_nonneg L A mem Lam HFL) as Hls.
  assert (HK : Frame.stk (ms_segs B) mem (S - (ALLOC_STACK + 32)) S)
    by (apply (kb_stk B API HIL _ L A regs mem md Hpre); lia).
  assert (HK32 : Frame.stk rsegs mem (S + -32) S).
  { destruct (Frame.stk_split _ mem _ (S + -32) S HK ltac:(lia)) as [_ H]. rewrite <- HSEG. exact H. }
  assert (BC : Mem.bytes_at rsegs mem 0x2f380 (Mem.le8 (Z_to_bv 64 cnt)))
    by (rewrite <- HSEG; apply word_mem_le8; [exact HCt | lia | lia | lia]).
  assert (WC : Mem.wr_at rsegs mem 0x2f380 8)
    by (rewrite <- HSEG; apply (globals_wr_at B API omx_G mem 0x2f380 cnt HG); [intros k Hk; apply in_G; lia | exact HCt]).
  assert (BF : Mem.bytes_at rsegs mem 0x1f0f8 (Mem.le8 (Z_to_bv 64 fail)))
    by (rewrite <- HSEG; apply word_mem_le8; [exact HFl | lia | lia | lia]).
  assert (WF : Mem.wr_at rsegs mem 0x1f0f8 8)
    by (rewrite <- HSEG; apply (globals_wr_at B API omx_G mem 0x1f0f8 fail HG); [intros k Hk; apply in_G; lia | exact HFl]).
  assert (Hwrm : forall a, S + -32 <= a < S -> writable_at (ms_segs B) mem a) by (intros a Ha; apply Hstk; lia).
  apply (kb_run B regs _ mem md
    (fun R pc' mem' => MallocRuns.seg1_post (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
       (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17)
       (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
       (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
       fp_regs fp_csr mem S n cnt fail (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs)))).
  { exact (proj1 (kb_md B API L A mem md HMR)). }
  { exact (proj2 (kb_md B API L A mem md HMR)). }
  { unfold rmk. rewrite Hsp, Ha0, HSEG. unfold FUZZ_MALLOC.
    eapply Exec.evt_mono.
    - apply (MallocRuns.seg1 (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
        (getr regs 8) (getr regs 9) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15)
        (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
        (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29)
        (getr regs 30) (getr regs 31) fp_regs fp_csr mem S n cnt fail); try assumption; lia.
    - intros ms Hp. pose proof Hp as (a1' & a2' & a3' & m' & _ & _ & _ & Harm).
      destruct Harm as [(_ & _ & E) | [(_ & _ & _ & E) | (_ & _ & _ & _ & _ & _ & E)]]; subst ms;
        do 3 eexists; (split; [reflexivity | exact Hp]). }
  intros R pc1 mem1 regs1 HK1 Hg1.
  destruct HK1 as (a1' & a2' & a3' & m1 & HM1 & HW1 & HC1 & Harm).
  rewrite <- HSEG in HW1, HC1.
  assert (Hcond2 : forall x, 0 <= x < alloc_ceiling ->
      (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
      Frame.outside [(S + -32, S); (0x2f380, 0x2f388); (0x1f0f8, 0x1f100)] x).
  { intros x Hx Ho. apply (avoid_gen L A mem md _ x HMR); [| exact Hx | exact Ho].
    intros lo hi Hin. cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-;
      [left; lia | right; intros y Hy; apply in_G; lia ..]. }
  assert (Hrog : forall a, in_globals omx_G a -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (HG a Ha) as (_ & Hl & Hs & _). pose proof alloc_ceiling_lt. apply ro_false_seg; [lia | exact Hs]. }
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (ro_agree_munch _ mem m1 Hro HM1). intros a Ha Ho. destruct (not_out _ _ Ho) as (lo & hi & Hin & Hb).
    cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
    - apply (ro_false_low HIL). lia.
    - apply Hrog, in_G. lia.
    - apply Hrog, in_G. lia. }
  assert (Hgk1 : forall i, 0 <= i < 8 -> mbyte (ms_segs B) m1 (ms_got_guard B + i) = mbyte (ms_segs B) mem (ms_got_guard B + i)).
  { intros i Hi. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md _ HMR (guard_owned L A (ms_got_guard B + i) ltac:(lia))) as Hlow.
    eapply (mbyte_munch (ms_segs B) _ mem m1); [exact HM1 | pose proof alloc_ceiling_lt; lia |].
    apply Hcond2; [exact Hlow | left; apply guard_owned; lia]. }
  assert (HMR1 : aa_MR API L A m1 md) by exact (kb_MR_A B API L A mem m1 md _ HMR HM1 Hcond2).
  assert (Hkeep1 : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
      mbyte (ms_segs B) m1 (a + i) = mbyte (ms_segs B) mem (a + i))
    by exact (kb_blocks_munch B API L A mem m1 md _ HMR HM1 Hcond2).
  assert (Hlv1 : word_mem (ms_segs B) m1 G_LIVE (lsum Lam))
    by (apply (kb_word_munch (ms_segs B) mem m1 _ G_LIVE (lsum Lam) HLv HM1); intros k Hk; unfold G_LIVE; split; [lia | out3]).
  assert (Hpk1 : word_mem (ms_segs B) m1 G_PEAK peak)
    by (apply (kb_word_munch (ms_segs B) mem m1 _ G_PEAK peak HPk HM1); intros k Hk; unfold G_PEAK; split; [lia | out3]).
  assert (Hct1 : word_mem (ms_segs B) m1 G_COUNT ((cnt + 1) mod 2 ^ 64)).
  { pose proof (bytes_at_le8_word (ms_segs B) m1 0x2f380 _ HC1) as H. rewrite uns64 in H. exact H. }
  assert (Hwmk : forall a, (S - (ALLOC_STACK + 32) <= a < S) \/ (errno_addr B <= a < errno_addr B + 4) ->
      writable_at (ms_segs B) mem a) by (intros a [Ha|Ha]; [apply Hstk; exact Ha | apply Herr; exact Ha]).
  assert (Hlblk1 : forall L2 A2 m2, (forall a k, In (a, k) (blocks L A) -> In (a, k) (blocks L2 A2)) ->
      (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte (ms_segs B) m2 (a + i) = mbyte (ms_segs B) mem (a + i)) ->
      Forall (fun ak => lblock B L2 A2 m2 (fst ak) (snd ak)) Lam).
  { intros L2 A2 m2 Hsub Hkm. eapply Forall_impl; [|exact HFL]. intros [a k] (Hk & Hin & Hw & Himg). cbn [fst snd] in *.
    split; [exact Hk|]. split; [exact (Hsub _ _ Hin)|]. split; [|exact Himg].
    apply (word_mem_frame (ms_segs B) mem m2 (a - 16) k Hw). intros k0 Hk0.
    exact (Hkm (a - 16) (k + 16) k0 Hin ltac:(lia)). }
  destruct Harm as [(Hcf & HF1 & E) | [(Hcf & Hbig & HF1 & E) | (Hcf & Hsmall & HF1 & HS8 & HS16 & HS24 & E)]].
  - rewrite <- HSEG in HF1.
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM. subst R pc1 mem1. clear E.
    apply SR_ret. exists L, A, regs1, m1, md, 0.
    rewrite (kb_ret_pc _ Hra).
    split; [reflexivity|].
    split; [exact Hro1|]. split; [exact Hgk1|].
    split; [tauto|].
    split.
    { intros _ i Hi.
      pose proof (mr_owned_low _ _ (aa_laws API) L A mem md _ HMR (libc8_owned L A (ms_libc B + 8 + i) ltac:(lia))) as Hlow.
      eapply (mbyte_munch (ms_segs B) _ mem m1); [exact HM1 | pose proof alloc_ceiling_lt; lia |].
      apply Hcond2; [exact Hlow | left; apply libc8_owned; lia]. }
    split.
    { apply (kb_post B API).
      - eapply (kb_mid_A B API HIL); [exact HMR | exact HWF | exact Hbd | exact Hwmk | exact HM1 | exact HW1 | | exact Hcond2].
        intros x Hx Hs He. unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in He. out3.
      - cs_cases ltac:(rewrite Hg1; first [reflexivity | exact (eq_sym Hsp)]). }
    split; [lia|].
    split; [rewrite Hg1; reflexivity|].
    split; [apply res_ok_up; [exact Hres | exact Hroom]|].
    split; [intros a k i Hin _ Hi; exact (Hkeep1 a k i Hin Hi)|].
    split; [intros q k Hq _; exact Hq|].
    left. split; [exact Hcf|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hres|].
    split.
    { intros a Ha Hw. change (bv_unsigned (getr regs 2)) with S in Hw.
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hw.
      eapply (mbyte_munch (ms_segs B) _ mem m1); [exact HM1 | lia | out3]. }
    split; [reflexivity|].
    split; [split; [exact Hlv1|]; split; [exact Hpk1|]; split; [exact Hct1|]|].
    + pose proof (bytes_at_le8_word (ms_segs B) m1 0x1f0f8 _ HF1) as H. rewrite uns64, Z.mod_small in H by lia. exact H.
    + split; [lia|]. split; [pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64)); lia|]. split; [lia|].
      split; [exact HND|]. apply Hlblk1; [tauto | exact Hkeep1].
  - exfalso. lia.
  - rewrite <- HSEG in HF1, HS8, HS16, HS24.
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM. subst R pc1 mem1. clear E.
    assert (G1 : getr regs1 1 = Z_to_bv 64 0x13adc) by (rewrite Hg1; reflexivity).
    assert (G2 : getr regs1 2 = Z_to_bv 64 (S + -32)) by (rewrite Hg1; reflexivity).
    assert (G8 : getr regs1 8 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
    assert (G9 : getr regs1 9 = Z_to_bv 64 0x2f370) by (rewrite Hg1; reflexivity).
    assert (G10 : getr regs1 10 = Z_to_bv 64 (n + 16)) by (rewrite Hg1; reflexivity).
    assert (Hs1 : spZ regs1 = S - 32) by (unfold spZ; rewrite G2, uns64, Z.mod_small by lia; lia).
    rewrite <- HMAL.
    eapply SR_bind; [apply (MALLOC L A regs1 m1 md (n + 16) b) | ].
    2: exact Hro1.
    { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
      eapply (kb_pre_A B API (ALLOC_STACK + 32) 32 ALLOC_STACK L A regs mem md regs1 m1);
        [exact Hpre | lia | lia | lia | rewrite Hs1; reflexivity | | rewrite Hg1; reflexivity | | exact HM1 | exact HW1 | | exact Hcond2].
      - rewrite Hs1. replace (S - 32) with (S + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
      - rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
      - intros x Hx Hs. out3. }
    { exact G10. }
    { exact Hres. }
    { exact Hroom. }
    intros c2 Hc2.
    destruct Hc2 as (L' & A' & regs2 & m2 & md' & r & -> & Hpost & Hr0 & Hrnz & Hr16 & Hfresh & (b1 & b2 & Hbl' & Hbl) &
                     Hkept & Hro2 & Hgk2 & Hub & Hinit & Hreg & Hres').
    pose proof Hpost as (HMR2 & HWF2 & Hbd2 & Hle2 & Hptr2 & Hp12 & (vm' & Emd) & Hfr2 & Hblk2 & Hscr2).
    destruct Hfresh as (Hr4096 & Hrceil & Hrimg).
    assert (Hnb : In (r, n + 16) (blocks L' A')) by (rewrite Hbl'; apply in_or_app; right; left; reflexivity).
    destruct (blocks_user L' A' r (n + 16) Hnb) as (q & Hq & Eq).
    assert (Hpres : forall i, 0 <= i < n + 16 -> present m2 (r + i) /\ ~ owned B L' A' (r + i)).
    { intros i Hi. destruct (mr_blocks _ _ (aa_laws API) L' A' m2 md' q (n + 16) i HMR2 Hq Hi) as (P1 & _ & _ & P4).
      rewrite Eq in P1, P4. split; assumption. }
    assert (Hfs : forall a, S + -32 <= a < S ->
        mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\ (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
    { intros a Ha. apply Hfr2.
      - left. lia.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A m1 md a HMR1 Ho). lia.
      - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) L' A' m2 md' a HMR2 Ho). lia.
      - unfold scratch_k. rewrite Hs1. lia.
      - tauto. }
    assert (Hwm1 : forall a, S + -32 <= a < S -> writable_at (ms_segs B) m1 a) by (intros a Ha; apply HW1, Hwrm; exact Ha).
    assert (Hwm2 : forall a, S + -32 <= a < S -> writable_at (ms_segs B) m2 a)
      by (intros a Ha; apply (proj2 (Hfs a Ha)), Hwm1; exact Ha).
    assert (Hg12 : forall a, in_globals omx_G a -> mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a).
    { intros a Ha. apply (kb_post_globals B API omx_G ALLOC_STACK L A regs1 m1 md (fun _ => False) L' A' regs2 m2 md' a
        HG HMR1 Hpost); [rewrite Hs1; lia | exact Ha | tauto]. }
    assert (Hw12 : forall a v, word_mem (ms_segs B) m1 a v -> (forall k, 0 <= k < 8 -> in_globals omx_G (a + k)) ->
        word_mem (ms_segs B) m2 a v).
    { intros a v Hw Hk. apply (word_mem_frame (ms_segs B) m1 m2 a v Hw). intros k Hk0. apply Hg12, Hk, Hk0. }
    assert (Hlv2 : word_mem (ms_segs B) m2 G_LIVE (lsum Lam)) by (apply Hw12; [exact Hlv1 | intros k Hk; apply in_G; unfold G_LIVE; lia]).
    assert (Hpk2 : word_mem (ms_segs B) m2 G_PEAK peak) by (apply Hw12; [exact Hpk1 | intros k Hk; apply in_G; unfold G_PEAK; lia]).
    assert (Hct2 : word_mem (ms_segs B) m2 G_COUNT ((cnt + 1) mod 2 ^ 64))
      by (apply Hw12; [exact Hct1 | intros k Hk; apply in_G; unfold G_COUNT; lia]).
    assert (Hfl1 : word_mem (ms_segs B) m1 G_FAIL fail).
    { pose proof (bytes_at_le8_word (ms_segs B) m1 0x1f0f8 _ HF1) as H. rewrite uns64, Z.mod_small in H by lia. exact H. }
    assert (Hfl2 : word_mem (ms_segs B) m2 G_FAIL fail) by (apply Hw12; [exact Hfl1 | intros k Hk; apply in_G; unfold G_FAIL; lia]).
    assert (Hsb : forall a v, S + -32 <= a -> a + 8 <= S -> Mem.bytes_at (ms_segs B) m1 a (Mem.le8 v) ->
        Mem.bytes_at rsegs m2 a (Mem.le8 v) /\ Mem.wr_at rsegs m2 a 8).
    { intros a v Ha1 Ha2 Hb. rewrite <- HSEG. split.
      - apply (bytes_frame m1 m2 a _ Hb). intros i Hi. rewrite Mem.length_le8 in Hi. apply Hfs. lia.
      - apply wr_frame; [intros i Hi; apply Hwm2; lia | lia | lia]. }
    destruct (Hsb (S + -8) _ ltac:(lia) ltac:(lia) HS8) as (B8 & W8).
    destruct (Hsb (S + -16) _ ltac:(lia) ltac:(lia) HS16) as (B16 & W16).
    destruct (Hsb (S + -24) _ ltac:(lia) ltac:(lia) HS24) as (B24 & W24).
    assert (Hlam : lsum Lam + n + 16 <= alloc_ceiling - 4096 /\ ~ In (r + 16) (map fst Lam)).
    { apply (MallocRuns.lam_room b1 b2 r n Lam 4096 alloc_ceiling).
      - rewrite <- Hbl'. exact (mr_blocks_disjoint _ _ (aa_laws API) L' A' m2 md' HMR2).
      - rewrite <- Hbl'. intros [p k] Hin. exact (blk_range L' A' m2 md' p k HMR2 Hin).
      - lia.
      - exact Hn0.
      - exact HND.
      - eapply Forall_impl; [|exact HFL]. intros [a k] (Hk & Hin & _). cbn [fst snd] in *. rewrite <- Hbl. split; assumption. }
    destruct Hlam as (Hlam & Hnin).
    assert (Hhd : forall lo hi, (forall y, lo <= y < hi -> in_globals omx_G y) -> lo < hi -> r + 8 <= lo \/ hi <= r).
    { intros lo hi Hg Hlh. destruct (Z_le_gt_dec (r + 8) lo) as [h|h]; [left; exact h|].
      destruct (Z_le_gt_dec hi r) as [h'|h']; [right; exact h'|]. exfalso.
      apply (Hrimg (Z.max r lo - r)); [lia|]. replace (r + (Z.max r lo - r)) with (Z.max r lo) by lia.
      apply glob_img, Hg. lia. }
    pose proof (Hhd 0x2f370 0x2f388 ltac:(intros y Hy; apply in_G; lia) ltac:(lia)) as Hhs.
    pose proof (Hhd 0x1f0f8 0x1f100 ltac:(intros y Hy; apply in_G; lia) ltac:(lia)) as Hhf.
    assert (Hstk2 : Frame.stk rsegs m2 r (r + 8)).
    { rewrite <- HSEG. split; [lia|]. split; [lia|]. intros a Ha.
      destruct (Hpres (a - r) ltac:(lia)) as (Hp & _). replace (r + (a - r)) with a in Hp by lia.
      split; [exact (present_wr m2 a Hp) | exact (present_mrd m2 a Hp)]. }
    assert (G2' : getr regs2 2 = Z_to_bv 64 (S + -32)) by (rewrite <- G2; apply (Hp12 2); unfold callee_saved; lia).
    assert (G8' : getr regs2 8 = Z_to_bv 64 n) by (rewrite <- G8; apply (Hp12 8); unfold callee_saved; lia).
    assert (G9' : getr regs2 9 = Z_to_bv 64 0x2f370) by (rewrite <- G9; apply (Hp12 9); unfold callee_saved; lia).
    rewrite G1.
    destruct (kb_md B API L' A' m2 md' HMR2) as (Hh2 & Hz2).
    apply (kb_run B regs2 _ m2 md'
      (fun R pc' mem' => MallocRuns.seg2_post (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7)
         (getr regs2 17) (getr regs2 18) (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23)
         (getr regs2 24) (getr regs2 25) (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30)
         (getr regs2 31) fp_regs fp_csr m2 S n r (lsum Lam) peak (getr regs 1) (getr regs 8) (getr regs 9)
         (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs))) _ Hh2 Hz2).
    { unfold rmk. rewrite G2', G8', G9', Hr0, HSEG.
      eapply Exec.evt_mono.
      - apply (MallocRuns.seg2 (getr regs2 1) (getr regs2 3) (getr regs2 4) (getr regs2 5) (getr regs2 6) (getr regs2 7)
          (getr regs2 11) (getr regs2 12) (getr regs2 13) (getr regs2 14) (getr regs2 15) (getr regs2 16) (getr regs2 17)
          (getr regs2 18) (getr regs2 19) (getr regs2 20) (getr regs2 21) (getr regs2 22) (getr regs2 23) (getr regs2 24)
          (getr regs2 25) (getr regs2 26) (getr regs2 27) (getr regs2 28) (getr regs2 29) (getr regs2 30) (getr regs2 31)
          fp_regs fp_csr m2 S n r (lsum Lam) peak (getr regs 1) (getr regs 8) (getr regs 9)); try assumption; try lia.
        + rewrite <- HSEG. apply word_mem_le8; [exact Hlv2 | lia | lia | lia].
        + rewrite <- HSEG. apply (globals_wr_at B API omx_G m2 _ (lsum Lam) HG); [intros k Hk; apply in_G; lia | exact Hlv2].
        + rewrite <- HSEG. apply word_mem_le8; [exact Hpk2 | lia | lia | lia].
        + rewrite <- HSEG. apply (globals_wr_at B API omx_G m2 _ peak HG); [intros k Hk; apply in_G; lia | exact Hpk2].
      - intros ms Hp. pose proof Hp as (c1 & c2 & c3 & c4 & c5 & c6 & m' & _ & _ & _ & _ & _ & _ & E). subst ms.
        do 3 eexists. split; [reflexivity | exact Hp]. }
    intros R pc3 mem3 regs3 HK3 Hg3.
    destruct HK3 as (c1 & c2 & c3 & c4 & c5 & c6 & m3 & HM3 & HW3 & HP3 & HH3 & HL3 & HPk3 & E).
    rewrite <- HSEG in HW3, HH3, HL3, HPk3.
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MState.MS] in ER, EP, EM. subst R pc3 mem3. clear E.
    assert (Hold : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
        0 <= a + i < 2 ^ 64 /\ Frame.outside [(S + -32, S); (r, r + 8); (0x2f370, 0x2f380)] (a + i)).
    { intros a k i Hin Hi. pose proof (blk_range L A mem md a k HMR Hin) as Hrg. split; [lia|].
      apply kb_outside. intros lo hi Hw Hx. cbn in Hw. destruct Hw as [E|[E|[E|[]]]]; injection E as <- <-.
      - lia.
      - pose proof (mr_blocks_disjoint _ _ (aa_laws API) L' A' m2 md' HMR2) as Hd. rewrite Hbl' in Hd.
        destruct (MallocRuns.pairwise_mid _ b1 (r, n + 16) b2 Hd) as (Hz & _).
        rewrite Hbl in Hin. destruct (Hz _ Hin) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
      - apply (glob_free_at L A mem md (a + i) HMR); [apply in_G; lia | right; exists a, k; split; [exact Hin | lia]]. }
    assert (Hkeep : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
        mbyte (ms_segs B) m3 (a + i) = mbyte (ms_segs B) mem (a + i)).
    { intros a k i Hin Hi. destruct (Hold a k i Hin Hi) as (Hr & Ho).
      rewrite (mbyte_munch (ms_segs B) _ m2 m3 (a + i) HM3 Hr Ho).
      rewrite (Hkept a k i Hin ltac:(tauto) Hi). exact (Hkeep1 a k i Hin Hi). }
    assert (Hsub : forall a k, In (a, k) (blocks L A) -> In (a, k) (blocks L' A')).
    { intros a k Hin. rewrite Hbl in Hin. rewrite Hbl'. apply in_app_or in Hin. apply in_or_app.
      destruct Hin as [Hin|Hin]; [left; exact Hin | right; right; exact Hin]. }
    assert (Hout3 : forall a v, word_mem (ms_segs B) m2 a v -> (0x2f380 <= a \/ a + 8 <= 0x2f370) -> a + 8 <= r \/ r + 8 <= a ->
        0 <= a -> a + 8 <= S + -32 -> word_mem (ms_segs B) m3 a v).
    { intros a v Hw H1 H2 H3 H4. apply (kb_word_munch (ms_segs B) m2 m3 _ a v Hw HM3). intros k Hk. split; [lia | out3]. }
    assert (Hown3 : forall x, 0 <= x < alloc_ceiling -> owned B L' A' x ->
        Frame.outside [(S + -32, S); (r, r + 8); (0x2f370, 0x2f380)] x).
    { intros x Hx Ho. apply kb_outside. intros lo hi Hw Hb. cbn in Hw. destruct Hw as [E|[E|[E|[]]]]; injection E as <- <-.
      - lia.
      - destruct (Hpres (x - r) ltac:(lia)) as (_ & Hno). replace (r + (x - r)) with x in Hno by lia. exact (Hno Ho).
      - exact (glob_free_at L' A' m2 md' x HMR2 ltac:(apply in_G; lia) (or_introl Ho)). }
    apply SR_ret. exists L', A', regs3, m3, md', (r + 16).
    rewrite (kb_ret_pc _ Hra).
    split; [reflexivity|].
    split.
    { apply (ro_agree_munch _ m2 m3 Hro2 HM3). intros a Ha Ho. destruct (not_out _ _ Ho) as (lo & hi & Hin & Hb).
      cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
      - apply (ro_false_low HIL). lia.
      - apply ro_false_notimg; [lia|]. replace a with (r + (a - r)) by lia. apply Hrimg. lia.
      - apply Hrog, in_G. lia. }
    split.
    { intros i Hi. rewrite <- (Hgk1 i Hi), <- (Hgk2 i Hi).
      pose proof (mr_owned_low _ _ (aa_laws API) L' A' m2 md' _ HMR2 (guard_owned L' A' (ms_got_guard B + i) ltac:(lia))) as Hlow.
      eapply (mbyte_munch (ms_segs B) _ m2 m3); [exact HM3 | pose proof alloc_ceiling_lt; lia |].
      apply Hown3; [exact Hlow | apply guard_owned; lia]. }
    split; [intros _; exact Hinit|].
    split; [intros Hf0; rewrite Hinit in Hf0; discriminate|].
    split.
    { apply (kb_post B API).
      - apply (kb_mid_E B API _ _ _ _ _ _ (fun a => (alloc_writes (r + 16) a \/ False) \/ alloc_writes (r + 16) a)); [|tauto].
        eapply (kb_mid_tail B API HIL).
        + eapply (kb_mid_seqAX B API).
          * eapply (kb_mid_A B API HIL); [exact HMR | exact HWF | exact Hbd | exact Hwmk | exact HM1 | exact HW1 | | exact Hcond2].
            intros x Hx Hs He. unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in He. out3.
          * exact (proj1 (kb_mid_call B API ALLOC_STACK L A regs1 m1 md (fun _ => False) L' A' regs2 m2 md' Hpost)).
          * rewrite Hs1. lia.
          * rewrite Hs1. lia.
          * lia.
          * lia.
          * intros a _ _. tauto.
        + exact HM3.
        + exact HW3.
        + exact HP3.
        + intros x Hx Hs He. unfold alloc_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in He. out3.
        + exact Hown3.
        + intros p k i Hp _ Hi. exact (proj2 (Hold _ _ i (user_blocks_in L A p k Hp) Hi)).
      - cs_cases ltac:(rewrite Hg3; first
          [ reflexivity
          | exact (eq_sym Hsp)
          | match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
              transitivity (getr regs2 (Z_to_bv 5 k)); [reflexivity|];
              rewrite (Hp12 k ltac:(unfold callee_saved; lia)), Hg1; reflexivity end ]). }
    split; [exact Hreg|].
    split; [rewrite Hg3; reflexivity|].
    split; [exact Hres'|].
    split; [intros a k i Hin _ Hi; exact (Hkeep a k i Hin Hi)|].
    split; [intros q0 k Hq0 _; exact (Hub q0 k Hq0)|].
    right. split; [exact Hcf|]. split; [lia|].
    split; [replace (r + 16) with (r + 1 * 16) by lia; rewrite Z_mod_plus_full; exact Hr16|].
    split.
    { intros i Hi Hs. apply (Hrimg i Hi). replace (r + i) with (r + 16 - 16 + i) by lia.
      apply glob_img, in_G. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hs. lia. }
    split; [intros i Hi; replace (r + 16 - 16 + i) with (r + i) by lia; exact (Hrimg i Hi)|].
    split; [exact Hnin|].
    split; [exists b1, b2; replace (r + 16 - 16) with r by lia; split; [exact Hbl' | exact Hbl]|].
    assert (Hsum : (lsum Lam + n) mod 2 ^ 64 = lsum Lam + n) by (apply Z.mod_small; pose proof alloc_ceiling_lt; lia).
    rewrite Hsum in HL3, HPk3.
    split.
    { split; [|split; [|split]].
      - cbn [lsum]. pose proof (bytes_at_le8_word (ms_segs B) m3 _ _ HL3) as H. rewrite uns64, Z.mod_small in H by lia.
        replace (n + lsum Lam) with (lsum Lam + n) by lia. exact H.
      - pose proof (bytes_at_le8_word (ms_segs B) m3 _ _ HPk3) as H. rewrite uns64, Z.mod_small in H by lia. exact H.
      - apply (Hout3 _ _ Hct2); unfold G_COUNT; lia.
      - apply (Hout3 _ _ Hfl2); unfold G_FAIL; lia. }
    split; [cbn [lsum]; lia|].
    split; [pose proof (Z.mod_pos_bound (cnt + 1) (2 ^ 64)); lia|].
    split; [lia|].
    split.
    { apply (proj2 (NoDup_ListNoDup _)). cbn [map fst]. constructor; [exact Hnin|]. apply (proj1 (NoDup_ListNoDup _)). exact HND. }
    constructor.
    + cbn [fst snd]. split; [lia|]. split; [replace (r + 16 - 16) with r by lia; exact Hnb|].
      replace (r + 16 - 16) with r by lia. split; [|exact Hrimg].
      pose proof (bytes_at_le8_word (ms_segs B) m3 _ _ HH3) as H. rewrite uns64, Z.mod_small in H by lia. exact H.
    + apply Hlblk1; [exact Hsub | exact Hkeep].
Qed.

End FM.

Lemma omx_globals_free : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs ->
  YL01.AllocExtra B (aa_MR API) ->
  (forall L A mem md a, aa_MR API L A mem md -> in_globals FrameAPI.frame_G a -> ~ owned B L A a) ->
  (forall a, in_globals FrameAPI.frame_G a -> in_img B a /\ ~ static_owned B a /\
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4)) ->
  globals_free B API omx_G.
Proof.
  intros fx rc B API HSEG AX Hown Hfg a Ha.
  assert (Hr : 0x2f370 <= a < 0x2f388 \/ 0x1f0f8 <= a < 0x1f100).
  { destruct Ha as (lo & len & Hin & Hb). cbn in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hb; lia. }
  assert (Hf : in_globals FrameAPI.frame_G a).
  { unfold in_globals, FrameAPI.frame_G. destruct Hr as [Hr|Hr].
    - exists 0x2f370, 24. split; [right; left; reflexivity | lia].
    - exists 0x1f0f8, 8. split; [left; reflexivity | lia]. }
  destruct (Hfg a Hf) as (Himg & _ & _ & Herr).
  assert (HIL : img_low B).
  { apply (img_low_of_check B 140735332483072).
    - unfold img_check. rewrite HSEG. vm_compute. reflexivity.
    - pose proof alloc_ceiling_value. lia. }
  split; [exact Himg|]. split; [exact (proj1 HIL a Himg)|]. split.
  { assert (C : forallb (fun i => match find_segment rsegs (0x2f370 + Z.of_nat i) 1 with
                                  | Some s => seg_writable s | None => false end) (seq 0 24) = true /\
                forallb (fun i => match find_segment rsegs (0x1f0f8 + Z.of_nat i) 1 with
                                  | Some s => seg_writable s | None => false end) (seq 0 8) = true)
      by (split; vm_compute; reflexivity).
    destruct C as (C1 & C2). rewrite forallb_forall in C1, C2. rewrite HSEG.
    destruct Hr as [Hr|Hr].
    - specialize (C1 (Z.to_nat (a - 0x2f370)) ltac:(apply in_seq; lia)).
      replace (0x2f370 + Z.of_nat (Z.to_nat (a - 0x2f370))) with a in C1 by lia.
      destruct (find_segment rsegs a 1) as [s|]; [exists s; split; [reflexivity | exact C1] | discriminate].
    - specialize (C2 (Z.to_nat (a - 0x1f0f8)) ltac:(apply in_seq; lia)).
      replace (0x1f0f8 + Z.of_nat (Z.to_nat (a - 0x1f0f8))) with a in C2 by lia.
      destruct (find_segment rsegs a 1) as [s|]; [exists s; split; [reflexivity | exact C2] | discriminate]. }
  split; [exact Herr|].
  intros L A mem md HM. split; [exact (Hown L A mem md a HM Hf)|].
  intros p n Hp Hpa. destruct (blocks_user L A p n Hp) as (q & Hq & Eq).
  apply (YL01.ax_blocks_img AX L A mem md q n (a - p) HM Hq ltac:(lia)).
  rewrite Eq. replace (p + (a - p)) with a by lia. exact Himg.
Qed.
