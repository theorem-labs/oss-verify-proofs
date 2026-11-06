From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 MemNorm KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes TxRet PjWriteHyp
round_trip_text_c check_round_trip_c fuzz_free_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma crt_vm2 : forall vm1 vm2 md, with_vmmaps vm2 (with_vmmaps vm1 md) = with_vmmaps vm2 md.
Proof. intros vm1 vm2 md. destruct md. reflexivity. Qed.

Section Tr.
Variable sg : list Segment.

Lemma crt_mbyte_mrd : forall m a, mbyte sg m a = mrd sg m (wa a).
Proof. reflexivity. Qed.

Lemma crt_bytes_frame : forall m m' a bs, bytes_at sg m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte sg m' (a + i) = mbyte sg m (a + i)) -> bytes_at sg m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (E (Z.of_nat i) ltac:(lia)) as Ei. rewrite !crt_mbyte_mrd in Ei. rewrite Ei. exact (H i Hi).
Qed.

Lemma crt_wr_frame : forall m m' a n, wr_at sg m a n ->
  (forall i, 0 <= i < n -> writable_at sg m (a + i) -> writable_at sg m' (a + i)) -> wr_at sg m' a n.
Proof.
  intros m m' a n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (E i Hi (H i Hi)).
Qed.

Lemma crt_stk_frame : forall m m' lo hi, stk sg m lo hi ->
  (forall a, lo <= a < hi -> mbyte sg m' a = mbyte sg m a /\ (writable_at sg m a -> writable_at sg m' a)) ->
  stk sg m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W [b R]]. destruct (E a Ha) as [Eb Ew]. split; [exact (Ew W)|].
  exists b. rewrite <- crt_mbyte_mrd in R |- *. rewrite Eb. exact R.
Qed.

Lemma crt_rw_frame : forall m m' A cs, rw_cells sg m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     mbyte sg m' (A + i) = mbyte sg m (A + i) /\ (writable_at sg m (A + i) -> writable_at sg m' (A + i))) ->
  rw_cells sg m' A cs.
Proof.
  intros m m' A cs [[Hwf HB] HW] E. split; [split; [exact Hwf|]|].
  - apply (crt_bytes_frame m); [exact HB|]. intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf.
    exact (proj1 (E i Hi)).
  - apply (crt_wr_frame m); [exact HW|]. intros i Hi. exact (proj2 (E i Hi)).
Qed.

Lemma crt_raw : forall (m m' : word -> option byte) a, mbyte sg m' a = mbyte sg m a ->
  seg_rom sg (Z_to_bv 64 a) = None -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m m' a. unfold mbyte.
  destruct (m' (Z_to_bv 64 a)) as [b'|], (m (Z_to_bv 64 a)) as [b|]; intros H R; rewrite ?R in H; congruence.
Qed.

End Tr.

Definition crt_cover (sl : list Segment) : bool :=
  forallb (fun g => existsb (fun r => (bv_unsigned (fst r) <=? Z.of_N (seg_base g)) &&
    (Z.of_N (seg_base g) + Z.of_N (seg_size g) <=? bv_unsigned (fst r) + bv_unsigned (snd r)))
    (segments_reserved sl)) sl.

Lemma crt_cover_rsegs : crt_cover rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section G.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition cwin (sp K a : Z) : Prop := (sp - K <= a < sp) \/ (errno_addr B <= a < errno_addr B + 4).

Definition cstep (sp K : Z) (E : Z -> Prop) (G : Z -> Z -> Prop)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\
  (st_init_done A = true -> st_init_done A' = true) /\
  (forall a k, In (a, k) (blocks L A) -> ~ G a k -> In (a, k) (blocks L' A')) /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ cwin sp K a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a, in_img B a -> (forall L0 A0 mem0 md0, MR L0 A0 mem0 md0 -> ~ owned B L0 A0 a) ->
     ~ cwin sp K a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall a k i, In (a, k) (blocks L A) -> ~ G a k -> 0 <= i < k -> ~ E (a + i) ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) /\
  (forall a, cwin sp K a -> writable_at segs mem' a).

Definition NoG : Z -> Z -> Prop := fun _ _ => False.

Lemma cwin_dec : forall sp K a, cwin sp K a \/ ~ cwin sp K a.
Proof. intros sp K a. unfold cwin. lia. Qed.

Lemma cstep_refl : forall sp K E G L A mem md,
  MR L A mem md -> WF A -> bounded A -> (forall a, cwin sp K a -> writable_at segs mem a) ->
  cstep sp K E G L A mem md L A mem md.
Proof.
  intros sp K E G L A mem md HM HW HB HS.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [tauto|].
  split; [intros; assumption|]. split; [exists (m_vmmaps md); symmetry; apply kb_vm_id|].
  split; [intros; split; [reflexivity | tauto]|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|]. exact HS.
Qed.

Lemma cstep_trans : forall sp K Eo L A mem md L1 A1 mem1 md1 sp2 K2 E2 G2 L2 A2 mem2 md2,
  cstep sp K Eo NoG L A mem md L1 A1 mem1 md1 ->
  cstep sp2 K2 E2 G2 L1 A1 mem1 md1 L2 A2 mem2 md2 ->
  sp - K <= sp2 - K2 -> sp2 <= sp -> alloc_ceiling <= sp - K -> sp <= 2 ^ 64 ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> E2 a -> (sp - K <= a < sp) \/ Eo a) ->
  (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> E2 (a + i) -> Eo (a + i)) ->
  (forall a k, In (a, k) (blocks L A) -> ~ G2 a k) ->
  (forall a, sp - K <= a < sp -> E2 a \/ ~ E2 a) ->
  (forall a, sp - K <= a < sp -> E2 a -> writable_at segs mem2 a) ->
  cstep sp K Eo NoG L A mem md L2 A2 mem2 md2.
Proof.
  intros sp K Eo L A mem md L1 A1 mem1 md1 sp2 K2 E2 G2 L2 A2 mem2 md2
    (M1 & W1 & B1 & I1 & P1 & V1 & F1 & J1 & K1 & S1) (M2 & W2 & B2 & I2 & P2 & V2 & F2 & J2 & K2' & S2)
    H1 H2 H3 H4 HE HEB HG HDE HEW.
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|]. split; [tauto|].
  split; [intros a k Hin _; apply P2; [apply P1; [exact Hin | intros []] | apply (HG a k Hin)]|].
  split; [destruct V1 as [v1 ->]; destruct V2 as [v2 ->]; exists v2; apply crt_vm2|].
  assert (Hw : forall a, ~ cwin sp K a -> ~ cwin sp2 K2 a).
  { intros a Ha Hb. apply Ha. destruct Hb as [Hb|Hb]; [left; lia | right; exact Hb]. }
  split.
  { intros a Ha Hc He.
    destruct (F1 a Ha Hc He) as [E1 R1].
    assert (He2 : ~ E2 a) by (intros X; destruct (HE a (or_introl Ha) X) as [Y|Y]; [apply Hc; left; exact Y | exact (He Y)]).
    destruct (F2 a Ha (Hw a Hc) He2) as [E2' R2]. split; [congruence | tauto]. }
  split.
  { intros a Ha Ho Hc He.
    destruct (J1 a Ha Ho Hc He) as [E1 R1].
    assert (He2 : ~ E2 a) by (intros X; destruct (HE a (or_intror Ha) X) as [Y|Y]; [apply Hc; left; exact Y | exact (He Y)]).
    destruct (J2 a Ha Ho (Hw a Hc) He2) as [E2' R2]. split; [congruence | tauto]. }
  split.
  { intros a k i Hin _ Hi He.
    rewrite <- (K1 a k i Hin ltac:(intros []) Hi He).
    apply (K2' a k i); [apply P1; [exact Hin | intros []] | apply (HG a k Hin) | exact Hi |].
    intros X. exact (He (HEB a k i Hin Hi X)). }
  intros a Ha.
  destruct (cwin_dec sp2 K2 a) as [Hc|Hc]; [exact (S2 a Hc)|].
  destruct Ha as [Ha|Ha]; [|exfalso; apply Hc; right; exact Ha].
  destruct (HDE a Ha) as [He|He]; [exact (HEW a Ha He)|].
  apply (proj2 (F2 a ltac:(lia) Hc He)). apply S1. left. exact Ha.
Qed.

Lemma rpost_cstep : forall K L A regs mem md E gone L' A' regs' mem' md',
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  cstep (spZ regs) K E gone L A mem md L' A' mem' md' /\ regs_preserved regs regs'.
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md'
    (HM & HW & HB & HL & HI & _ & _ & HU & HP & HR & HV & HF & HJ & HK & HS).
  split; [|exact HR].
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HI|].
  split.
  { intros a k Hin Hg. unfold blocks in Hin |- *. apply in_map_iff in Hin as ([p n] & E1 & Hp).
    cbn [fst snd] in E1. injection E1 as E1 E2. subst a n.
    apply in_map_iff. exists (p, k). cbn [fst snd].
    pose proof (HU p k Hp Hg) as Hp'. rewrite (HP p k Hp Hp'). split; [reflexivity | exact Hp']. }
  split; [exact HV|]. split; [exact HF|]. split; [exact HJ|].
  split.
  { intros a k i Hin Hg Hi He. unfold blocks in Hin. apply in_map_iff in Hin as ([p n] & E1 & Hp).
    cbn [fst snd] in E1. injection E1 as E1 E2. subst a n.
    exact (HK p k i Hp (HU p k Hp Hg) Hi He). }
  exact HS.
Qed.

Lemma rtt_cstep : forall K regs E L A mem md L' A' regs' mem' md',
  rtt_rel B API K regs E L A mem md L' A' regs' mem' md' ->
  cstep (spZ regs) K E NoG L A mem md L' A' mem' md' /\ regs_preserved regs regs'.
Proof.
  intros K regs E L A mem md L' A' regs' mem' md' (HM & HW & HB & HI & HP & HR & HV & HF & HJ & HK & HS).
  split; [|exact HR].
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HI|].
  split; [intros a k Hin _; exact (HP a k Hin)|].
  split; [exact HV|]. split; [exact HF|]. split; [exact HJ|].
  split; [intros a k i Hin _ Hi He; exact (HK a k i Hin Hi He)|].
  exact HS.
Qed.

Lemma cstep_rtt : forall K regs E L A mem md L' A' regs' mem' md',
  cstep (spZ regs) K E NoG L A mem md L' A' mem' md' -> regs_preserved regs regs' ->
  rtt_rel B API K regs E L A mem md L' A' regs' mem' md'.
Proof.
  intros K regs E L A mem md L' A' regs' mem' md' (HM & HW & HB & HI & HP & HV & HF & HJ & HK & HS) HR.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HI|].
  split; [intros a k Hin; exact (HP a k Hin ltac:(intros []))|].
  split; [exact HR|]. split; [exact HV|]. split; [exact HF|]. split; [exact HJ|].
  split; [intros a k i Hin Hi He; exact (HK a k i Hin ltac:(intros []) Hi He)|].
  exact HS.
Qed.

Lemma crt_pw_in2 : forall (R : Z * Z -> Z * Z -> Prop) l x y, pairwise R l -> In x l -> In y l -> x <> y ->
  R x y \/ R y x.
Proof.
  induction l as [|z l IH]; intros x y H Hx Hy Hne; cbn in *; [contradiction|].
  destruct H as [Hz H]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - left. exact (Hz y Hy).
  - right. exact (Hz x Hx).
  - exact (IH x y H Hx Hy Hne).
Qed.

Lemma crt_blk_disj : forall L A mem md a k a' k', MR L A mem md ->
  In (a, k) (blocks L A) -> In (a', k') (blocks L A) -> (a, k) <> (a', k') -> a + k <= a' \/ a' + k' <= a.
Proof.
  intros L A mem md a k a' k' HM H1 H2 Hne.
  destruct (crt_pw_in2 _ _ _ _ (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) H1 H2 Hne) as [X|X];
    unfold ranges_disjoint in X; cbn [fst snd] in X; lia.
Qed.

Lemma ff_cstep : forall L A regs mem md p k L' A' regs' mem' md',
  MR L A mem md -> (p = 0 \/ In (p - 16, k + 16) (blocks L A)) -> 0 <= k ->
  (st_init_done A = true -> st_init_done A' = true) ->
  call_post_k B MR ALLOC_STACK L A regs mem md (free_writes p k) L' A' regs' mem' md' ->
  keeps B L A mem mem' (p - 16) -> ublocks_kept L A A' (p - 16, k + 16) ->
  cstep (spZ regs) ALLOC_STACK (free_writes p k) (fun a n => a = p - 16 /\ n = k + 16) L A mem md L' A' mem' md' /\
  regs_preserved regs regs'.
Proof.
  intros L A regs mem md p k L' A' regs' mem' md' HM0 Hp Hk HI (HM & HW & HB & HL & HP & HR & HV & HF & HK & HS) HKp HU.
  split; [|exact HR].
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HI|].
  split.
  { intros a n Hin Hg. unfold blocks in Hin |- *. apply in_map_iff in Hin as ([q n'] & E1 & Hq).
    cbn [fst snd] in E1. injection E1 as E1 E2. subst a n'.
    assert (Hq' : In (q, n) (user_blocks A')).
    { apply HU; [exact Hq|]. intros X. injection X as X1 X2. exact (Hg (conj X1 X2)). }
    apply in_map_iff. exists (q, n). cbn [fst snd]. rewrite (HP q n Hq Hq'). split; [reflexivity | exact Hq']. }
  split; [exact HV|].
  split.
  { intros a Ha Hc He. apply HF; [left; exact Ha | | | exact Hc | exact He].
    - intro Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM0 Ho). lia.
    - intro Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia. }
  split.
  { intros a Ha Ho Hc He. apply HF; [right; exact Ha | apply (Ho _ _ _ _ HM0) | apply (Ho _ _ _ _ HM) | exact Hc | exact He]. }
  split.
  { intros a n i Hin Hg Hi _.
    destruct (Z.eq_dec a (p - 16)) as [Ea|Ea]; [|exact (HKp a n i Hin Ea Hi)].
    exfalso. subst a. destruct Hp as [Hp|Hp].
    - subst p. unfold blocks in Hin. apply in_map_iff in Hin as ([q n'] & E1 & Hq). cbn [fst snd] in E1.
      injection E1 as E1 E2. subst n'. pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM0 Hq). lia.
    - assert (Hne : (p - 16, n) <> (p - 16, k + 16)) by (intros X; injection X as X; exact (Hg (conj eq_refl X))).
      destruct (crt_blk_disj L A mem md _ _ _ _ HM0 Hin Hp Hne); lia. }
  exact HS.
Qed.

Lemma cstep_munch : forall sp K E G L A mem md L1 A1 mem1 md1 mem2 W,
  img_low B -> alloc_ceiling <= sp - K ->
  cstep sp K E G L A mem md L1 A1 mem1 md1 ->
  Frame.munch W mem1 mem2 -> Frame.wmono segs mem1 mem2 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - K <= x < sp) -> Frame.outside W x) ->
  cstep sp K E G L A mem md L1 A1 mem2 md1.
Proof.
  intros sp K E G L A mem md L1 A1 mem1 md1 mem2 W [HI0 HI1] HK0
    (HM & HW & HB & HI & HP & HV & HF & HJ & HK & HS) Hm Hw HO.
  pose proof alloc_ceiling_value as Hc.
  assert (HM2 : MR L1 A1 mem2 md1).
  { apply (kb_MR_A B API L1 A1 mem1 mem2 md1 W HM Hm). intros x Hx _. apply HO; lia. }
  split; [exact HM2|]. split; [exact HW|]. split; [exact HB|]. split; [exact HI|]. split; [exact HP|].
  split; [exact HV|].
  split.
  { intros a Ha Hc' He. destruct (HF a Ha Hc' He) as [E1 R1].
    assert (Ho : Frame.outside W a).
    { apply HO. - split; lia. - intros X. apply Hc'. unfold cwin. left. exact X. }
    rewrite (mbyte_munch segs W mem1 mem2 a Hm ltac:(lia) Ho).
    split; [exact E1|]. rewrite R1. exact (writable_munch segs W mem1 mem2 a Hm ltac:(lia) Ho). }
  split.
  { intros a Ha Hown Hc' He. destruct (HJ a Ha Hown Hc' He) as [E1 R1].
    pose proof (HI0 a Ha) as Ha'.
    assert (Ho : Frame.outside W a) by (apply HO; lia).
    rewrite (mbyte_munch segs W mem1 mem2 a Hm ltac:(lia) Ho).
    split; [exact E1|]. rewrite R1. exact (writable_munch segs W mem1 mem2 a Hm ltac:(lia) Ho). }
  split.
  { intros a k i Hin Hg Hi He. rewrite <- (HK a k i Hin Hg Hi He).
    pose proof (HP a k Hin Hg) as Hin1.
    unfold blocks in Hin1. apply in_map_iff in Hin1 as ([q n] & E1 & Hq). cbn [fst snd] in E1.
    injection E1 as E1 E2. subst n.
    destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq) as [R1 R2]. rewrite E1 in R1, R2.
    apply (mbyte_munch segs W mem1 mem2 (a + i) Hm ltac:(lia)). apply HO; lia. }
  intros a Ha. apply Hw. exact (HS a Ha).
Qed.

Lemma crt_noseg : ms_segs B = rsegs -> forall x, 0 <= x < 2 ^ 64 -> ~ in_img B x ->
  seg_rom segs (Z_to_bv 64 x) = None.
Proof.
  intros HS x Hx Hn. apply seg_rom_unmapped. rewrite unsigned_lit by exact Hx.
  destruct (find_segment segs x 1) as [g|] eqn:F; [|reflexivity]. exfalso. apply Hn.
  destruct (kb_find_segment segs x 1 g F) as (Hin & H1 & H2).
  pose proof crt_cover_rsegs as C. unfold crt_cover in C. unfold segs in Hin. rewrite HS in Hin.
  rewrite forallb_forall in C. specialize (C g Hin).
  apply existsb_exists in C as (r & Hr & Hc). apply andb_prop in Hc as [Ha Hb]. apply Z.leb_le in Ha, Hb.
  unfold in_img. rewrite HS. split; [intros E; rewrite E in Hin; destruct Hin|]. exists r. split; [exact Hr|]. lia.
Qed.

Lemma crt_noseg_hi : img_low B -> forall x, alloc_ceiling <= x < 2 ^ 64 -> seg_rom segs (Z_to_bv 64 x) = None.
Proof.
  intros [_ HI] x Hx. pose proof alloc_ceiling_value. apply seg_rom_unmapped. rewrite unsigned_lit by lia.
  destruct (find_segment segs x 1) as [g|] eqn:F; [|reflexivity]. destruct (HI x g F). lia.
Qed.

Lemma crt_img_low : ms_segs B = rsegs -> img_low B.
Proof.
  intros HS. apply (img_low_of_check B 0x100000).
  - unfold img_check. rewrite HS. vm_compute. reflexivity.
  - pose proof alloc_ceiling_value. lia.
Qed.

Lemma cstep_pj_node : forall sp K E G L A mem md L' A' mem' md' Lam peak cnt fail p t D lblk,
  ms_segs B = rsegs -> img_low B ->
  cstep sp K E G L A mem md L' A' mem' md' ->
  ledger B L A mem Lam peak cnt fail -> (forall bk, In bk D -> In bk Lam) ->
  pj_node segs mem (lin Lam) p t D -> (forall a k, In (a, k) D -> lblk a k) ->
  alloc_ceiling <= p -> p + 56 <= 2 ^ 64 ->
  (forall a, p <= a < p + 56 -> ~ cwin sp K a /\ ~ E a) ->
  (forall a k, In (a, k) D -> ~ G (a - 16) (k + 16) /\ forall i, 0 <= i < k -> ~ E (a + i)) ->
  pj_node segs mem' lblk p t D.
Proof.
  intros sp K E G L A mem md L' A' mem' md' Lam peak cnt fail p t D lblk HS HIL HC HL HD HN HLb Hp1 Hp2 HP HDb.
  destruct HC as (HM & _ & _ & _ & _ & _ & HF & _ & HK & _).
  apply (pj_node_frame segs t mem (lin Lam) mem' lblk p D HN HLb).
  intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx. cbn in Rx.
  rewrite <- (wa_of_var x (bv_unsigned x) eq_refl). unfold wa.
  remember (bv_unsigned x) as a eqn:Ea. clear Ea.
  destruct Hx as [Hx|([ba bk] & Hb & Hx)].
  - destruct (HP a Hx) as [H1 H2]. apply (crt_raw segs); [exact (proj1 (HF a ltac:(lia) H1 H2))|].
    apply crt_noseg_hi; [exact HIL | lia].
  - unfold pj_holds in Hx. cbn [fst snd] in Hx.
    destruct HL as (_ & _ & _ & _ & _ & HF'). rewrite Forall_forall in HF'.
    destruct (HF' (ba, bk) (HD _ Hb)) as (Hk0 & Hin & _ & Himg). cbn [fst snd] in Hk0, Hin, Himg.
    destruct (HDb ba bk Hb) as [Hg He].
    pose proof (HK (ba - 16) (bk + 16) (a - ba + 16) Hin Hg ltac:(lia)) as R.
    replace (ba - 16 + (a - ba + 16)) with a in R by lia.
    apply (crt_raw segs); [apply R; replace a with (ba + (a - ba)) by lia; apply He; lia|].
    apply (crt_noseg HS a ltac:(lia)). replace a with (ba - 16 + (a - ba + 16)) by lia. apply Himg. lia.
Qed.

Lemma cstep_rw : forall sp K E G L A mem md L' A' mem' md' a cs,
  cstep sp K E G L A mem md L' A' mem' md' ->
  alloc_ceiling <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat (cells_size cs) -> ~ cwin sp K x /\ ~ E x) ->
  rw_cells segs mem a cs -> rw_cells segs mem' a cs.
Proof.
  intros sp K E G L A mem md L' A' mem' md' a cs (_ & _ & _ & _ & _ & _ & HF & _) H1 H2 H3 HR.
  apply (crt_rw_frame segs mem); [exact HR|]. intros i Hi. destruct (H3 (a + i) ltac:(lia)) as [X Y].
  destruct (HF (a + i) ltac:(lia) X Y) as [E1 E2]. split; [exact E1 | apply E2].
Qed.

Lemma cstep_stk : forall sp K E G L A mem md L' A' mem' md' lo hi,
  cstep sp K E G L A mem md L' A' mem' md' ->
  alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall x, lo <= x < hi -> ~ cwin sp K x /\ ~ E x) ->
  stk segs mem lo hi -> stk segs mem' lo hi.
Proof.
  intros sp K E G L A mem md L' A' mem' md' lo hi (_ & _ & _ & _ & _ & _ & HF & _) H1 H2 H3 HR.
  apply (crt_stk_frame segs mem); [exact HR|]. intros x Hx. destruct (H3 x Hx) as [X Y].
  destruct (HF x ltac:(lia) X Y) as [E1 E2]. split; [exact E1 | apply E2].
Qed.

Lemma crt_word_munch : forall mem mem' W a v, word_mem segs mem a v -> Frame.munch W mem mem' ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (forall k, 0 <= k < 8 -> Frame.outside W (a + k)) -> word_mem segs mem' a v.
Proof.
  intros mem mem' W a v H Hm H0 H1 HO k Hk. rewrite (mbyte_munch segs W mem mem'); [exact (H k Hk) | exact Hm | lia |].
  apply HO. lia.
Qed.

Lemma ledger_munch : forall L A mem md mem' Lam peak cnt fail W,
  MR L A mem md -> ledger B L A mem Lam peak cnt fail -> Frame.munch W mem mem' ->
  (forall x, 0 <= x < alloc_ceiling -> Frame.outside W x) ->
  ledger B L A mem' Lam peak cnt fail.
Proof.
  intros L A mem md mem' Lam peak cnt fail W HM HL Hm HO.
  pose proof alloc_ceiling_value as Hc. pose proof HL as HL0.
  destruct HL as ((W1 & W2 & W3 & W4) & H1 & H2 & H3 & H4 & H5).
  assert (Hs : forall a v, word_mem segs mem a v -> 0 <= a -> a + 8 <= alloc_ceiling -> word_mem segs mem' a v).
  { intros a v Hw Ha Hb. apply (crt_word_munch mem mem' W a v Hw Hm Ha ltac:(lia)). intros k Hk. apply HO. lia. }
  split; [|split; [exact H1|split; [exact H2|split; [exact H3|split; [exact H4|]]]]].
  - unfold alloc_words, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
    split; [apply Hs; [exact W1 | lia | lia]|]. split; [apply Hs; [exact W2 | lia | lia]|].
    split; [apply Hs; [exact W3 | lia | lia] | apply Hs; [exact W4 | lia | lia]].
  - rewrite Forall_forall in H5 |- *. intros [a k] Hin. destruct (H5 (a, k) Hin) as (Hk & Hb & Hw & Hi).
    cbn [fst snd] in *. split; [exact Hk|]. split; [exact Hb|]. split; [|exact Hi].
    destruct (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL0 Hin) as (R1 & R2 & R3).
    apply Hs; [exact Hw | lia | lia].
Qed.

Lemma rd_cells_of : forall L A mem md, AllocExtra B (aa_MR API) -> MR L A mem md -> ro_agree segs mem -> rd_cells B mem.
Proof.
  intros L A mem md AX HM HR. destruct (ax_statics AX L A mem md HM) as (H1 & (g & _ & H2) & _).
  split; [exact HR|]. split; [exact H1 | exists g; exact H2].
Qed.

End G.
