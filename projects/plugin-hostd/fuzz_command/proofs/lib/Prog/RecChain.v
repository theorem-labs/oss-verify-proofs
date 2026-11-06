From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import MState Mem Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YP09 YO0i YO0f YO0d YO0o YM05 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO10 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecKindB rec_calls_free_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sptr_eqd : forall p q : sptr, {p = q} + {p <> q}.
Proof. decide equality; first [apply Z.eq_dec | apply Nat.eq_dec]. Defined.

Definition not_at (p : sptr) (x : sptr * Z) : bool := if sptr_eqd (fst x) p then false else true.

Lemma filter_all : forall (u : list (sptr * Z)) p, (forall y, In y u -> fst y <> p) -> List.filter (not_at p) u = u.
Proof.
  induction u as [|y u IH]; intros p H; [reflexivity|].
  change (List.filter (not_at p) (y :: u)) with (if not_at p y then y :: List.filter (not_at p) u else List.filter (not_at p) u).
  unfold not_at at 1.
  destruct (sptr_eqd (fst y) p) as [E|E]; cbv beta iota; [exfalso; exact (H y (or_introl eq_refl) E)|].
  f_equal. apply IH. intros z Hz. apply H. right. exact Hz.
Qed.

Lemma count_not_at : forall (u : list (sptr * Z)) p n, List.NoDup (map fst u) -> In (p, n) u ->
  (length (List.filter (not_at p) u) + 1 = length u)%nat.
Proof.
  induction u as [|y u IH]; intros p n ND Hin; [destruct Hin|].
  cbn [map] in ND. apply List.NoDup_cons_iff in ND as [Hy ND].
  change (List.filter (not_at p) (y :: u)) with (if not_at p y then y :: List.filter (not_at p) u else List.filter (not_at p) u).
  unfold not_at at 1.
  destruct (sptr_eqd (fst y) p) as [E|E]; cbv beta iota; cbn [length].
  - rewrite filter_all; [lia|]. intros z Hz E'. apply Hy. rewrite E, <- E'. apply in_map. exact Hz.
  - destruct Hin as [Ey|Hin]; [subst y; cbn in E; congruence|].
    pose proof (IH p n ND Hin). lia.
Qed.

Lemma nodup_key : forall (u : list (sptr * Z)) p k n, List.NoDup (map fst u) -> In (p, k) u -> In (p, n) u -> k = n.
Proof.
  induction u as [|[q m] u IH]; intros p k n ND H1 H2; [destruct H1|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as [Hq ND].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - congruence.
  - exfalso. assert (Eq : q = p) by congruence. subst q. apply Hq. change p with (fst (p, n)). apply in_map. exact H2.
  - exfalso. assert (Eq : q = p) by congruence. subst q. apply Hq. change p with (fst (p, k)). apply in_map. exact H1.
  - exact (IH p k n ND H1 H2).
Qed.

Lemma ub_shrink : forall (u u' : list (sptr * Z)) p n,
  List.NoDup (map fst u) -> List.NoDup (map fst u') -> In (p, n) u -> (length u' + 1 = length u)%nat ->
  (forall q k, In (q, k) u -> q <> p -> In (q, k) u') -> forall x, In x u' -> In x u /\ fst x <> p.
Proof.
  intros u u' p n ND ND' Hin HL HK x Hx.
  assert (INC : incl (List.filter (not_at p) u) u').
  { intros [q k] Hy. apply List.filter_In in Hy as [Hy Hf]. unfold not_at in Hf. cbn [fst] in Hf.
    destruct (sptr_eqd q p) as [E|E]; [discriminate|]. exact (HK q k Hy E). }
  assert (NDf : List.NoDup (List.filter (not_at p) u)) by (apply List.NoDup_filter; exact (List.NoDup_map_inv _ _ ND)).
  pose proof (count_not_at u p n ND Hin) as C.
  assert (INC' : incl u' (List.filter (not_at p) u)) by (apply List.NoDup_length_incl; [exact NDf | lia | exact INC]).
  apply INC' in Hx. apply List.filter_In in Hx as [Hx Hf]. split; [exact Hx|].
  unfold not_at in Hf. destruct (sptr_eqd (fst x) p) as [E|E]; [discriminate | exact E].
Qed.

Lemma perm_free_step : forall (b1 b2 F : list (Z * Z)) x,
  Permutation ((b1 ++ x :: b2) ++ F) ((b1 ++ b2) ++ F ++ [x]).
Proof.
  intros b1 b2 F x. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
  rewrite app_assoc. apply Permutation_cons_append.
Qed.

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn; [left; exact I|].
  destruct (IH x) as [H|H]; destruct (Z.le_gt_cases lo x) as [Q1|Q1]; destruct (Z.lt_ge_cases x hi) as [Q2|Q2];
    first [ left; split; [lia | exact H] | right; intros [Ha Hb]; first [lia | contradiction] ].
Qed.

Lemma fg_iff : forall a, in_globals frame_G a <-> 0x33d10 <= a < 0x33d10 + 1020.
Proof.
  intros a. unfold in_globals, frame_G. split.
  - intros (lo & len & [E|[]] & H). injection E as <- <-. exact H.
  - intros H. exists 0x33d10, 1020. split; [left; reflexivity | exact H].
Qed.

Lemma fg_rw : forall a, in_globals frame_G a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. apply fg_iff in Ha.
  assert (H : forallb (fun i => negb (ro_addr rsegs (Z_to_bv 64 (0x33d10 + Z.of_nat i)))) (seq 0 1020) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat (a - 0x33d10)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (0x33d10 + (a - 0x33d10)) with a in H by lia.
  destruct (ro_addr rsegs (Z_to_bv 64 a)); [discriminate | reflexivity].
Qed.

Lemma hi_rw : forall a, 2 ^ 20 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite unsigned_lit by lia.
  rewrite (find_segment_none_above rsegs (2 ^ 20) a 1 rsegs_top) by lia. reflexivity.
Qed.

Section Chain.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis ERRNO : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22a68.

Definition hi_img (a : Z) : Prop := (alloc_ceiling <= a < 2 ^ 64) \/ in_img B a.

Definition errw (a : Z) : Prop := errno_addr B <= a < errno_addr B + 4.

Definition fchain (S K : Z) (E : Z -> Prop) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (b : sbound) (F : list (Z * Z)) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
  MR Lc Ac memc mdc /\ WF Ac /\ bounded Ac /\
  layout_le A L Lc /\ (length (st_regions A) <= length (st_regions Ac))%nat /\
  (st_init_done A = true -> st_init_done Ac = true) /\
  (exists vm, mdc = with_vmmaps vm md) /\
  (forall x, In x (user_blocks Ac) -> In x (user_blocks A)) /\
  (forall p n, In (p, n) (user_blocks Ac) -> ptr_addr Lc p = ptr_addr L p) /\
  (forall p n, In (p, n) (user_blocks A) -> ~ In (ptr_addr L p, n) F -> In (p, n) (user_blocks Ac)) /\
  Permutation (blocks L A) (blocks Lc Ac ++ F) /\
  (forall p n i, In (p, n) (user_blocks Ac) -> 0 <= i < n ->
     mbyte (ms_segs B) memc (ptr_addr L p + i) = mbyte (ms_segs B) mem (ptr_addr L p + i)) /\
  (forall a, hi_img a -> ~ owned B L A a -> ~ (S - K <= a < S) -> ~ errw a -> ~ E a ->
     mbyte (ms_segs B) memc a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) memc a)) /\
  (forall a, S - K <= a < S \/ errw a -> writable_at (ms_segs B) memc a) /\
  ro_agree (ms_segs B) memc /\ guard_kept B mem memc /\
  res_ok_slots Ac (rfree_b b F).

Lemma own_img : forall L A m md L' A' m' md' a, MR L A m md -> MR L' A' m' md' -> in_img B a ->
  ~ owned B L A a -> ~ owned B L' A' a.
Proof using CTX AX.
  intros L A m md L' A' m' md' a HM HM' Hi Hn [Ho|Ho].
  - apply Hn. apply (CTX L A m md a HM). exact (ax_img AX L' A' m' md' a HM' Hi Ho).
  - apply Hn. right. exact Ho.
Qed.

Lemma own_any : forall L A m md L' A' m' md' a, MR L A m md -> MR L' A' m' md' -> hi_img a ->
  ~ owned B L A a -> ~ owned B L' A' a.
Proof using CTX AX.
  intros L A m md L' A' m' md' a HM HM' [Ha|Ha] Hn.
  - intros Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
  - exact (own_img L A m md L' A' m' md' a HM HM' Ha Hn).
Qed.

Lemma hi_img_range : forall a, hi_img a -> 0 <= a < 2 ^ 64.
Proof using SEGS.
  intros a [Ha|Ha]; [pose proof alloc_ceiling_val; lia|]. pose proof (in_img_low B SEGS a Ha). lia.
Qed.

Lemma block_not_img : forall L A m md q k i, MR L A m md -> In (q, k) (blocks L A) -> 0 <= i < k -> ~ in_img B (q + i).
Proof using AX.
  intros L A m md q k i HM Hin Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn in E. injection E as <- <-. exact (ax_blocks_img AX L A m md p k' i HM Hp Hi).
Qed.

Lemma block_not_hi_img : forall L A m md q k a, MR L A m md -> In (q, k) (blocks L A) -> q <= a < q + k ->
  hi_img a -> False.
Proof using AX.
  intros L A m md q k a HM Hin Hr [Ha|Ha].
  - pose proof (block_facts B _ (aa_laws API) L A m md q k (a - q) HM Hin ltac:(lia)). lia.
  - apply (block_not_img L A m md q k (a - q) HM Hin ltac:(lia)). replace (q + (a - q)) with a by lia. exact Ha.
Qed.

Lemma fchain_init : forall S K E L A regs mem md b,
  call_pre_k B MR K L A regs mem md -> ro_agree (ms_segs B) mem -> res_ok_slots A b -> spZ regs = S ->
  fchain S K E L A mem md b [] L A mem md.
Proof.
  intros S K E L A regs mem md b (HM & HW & HB & _ & _ & _ & _ & HWS & _ & HERR & _) HRO HRES <-.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [apply layout_le_refl|].
  split; [lia|]. split; [tauto|]. split; [exists (m_vmmaps md); apply YI04.with_vmmaps_self|].
  split; [intros x Hx; exact Hx|]. split; [intros; reflexivity|]. split; [intros p n Hp _; exact Hp|].
  split; [rewrite app_nil_r; apply Permutation_refl|].
  split; [intros; reflexivity|]. split; [intros; split; [reflexivity | tauto]|].
  split; [intros a [Ha|Ha]; [apply HWS; exact Ha | apply HERR; exact Ha]|].
  split; [exact HRO|]. split; [intros i _; reflexivity|]. exact HRES.
Qed.

Lemma fchain_free : forall S K E L A mem md b F Lc Ac regs_c memc mdc p n L2 A2 regs2 mem2 md2,
  MR L A mem md -> alloc_ceiling + K <= S -> S <= 2 ^ 64 ->
  fchain S K E L A mem md b F Lc Ac memc mdc ->
  In (p, n) (user_blocks Ac) ->
  S - K <= spZ regs_c - ALLOC_STACK -> spZ regs_c <= S ->
  call_post B MR Lc Ac regs_c memc mdc (fun a => ptr_addr Lc p <= a < ptr_addr Lc p + n) L2 A2 regs2 mem2 md2 ->
  (exists b1 b2, blocks Lc Ac = b1 ++ (ptr_addr Lc p, n) :: b2 /\ blocks L2 A2 = b1 ++ b2) ->
  ro_agree (ms_segs B) mem2 -> guard_kept B memc mem2 ->
  (forall q k, In (q, k) (user_blocks Ac) -> q <> p -> In (q, k) (user_blocks A2)) ->
  (st_init_done Ac = true -> st_init_done A2 = true) ->
  (length (st_regions Ac) <= length (st_regions A2))%nat ->
  res_ok_slots A2 (sb_free (rfree_b b F) n) ->
  fchain S K E L A mem md b (F ++ [(ptr_addr L p, n)]) L2 A2 mem2 md2.
Proof using CTX AX ERRNO.
  intros S K E L A mem md b F Lc Ac regs_c memc mdc p n L2 A2 regs2 mem2 md2 HM0 HK HS
    (HMc & HWc & HBc & HLE & HRG & HINIT & (vm & Hvm) & HSUB & HPTR & HKEEP & HPERM & HBYTES & HFRAME & HSCR & HRO & HGK & HRES)
    Hin Hlo Hhi (HM2 & HW2 & HB2 & HLE2 & HSTAB & _ & (vm2 & Hvm2) & HFR2 & HKB2 & HSCR2)
    (b1 & b2 & EB1 & EB2) HRO2 HGK2 HK2 HI2 HRG2 HRES2.
  pose proof alloc_ceiling_val as AC.
  assert (LEN : (length (user_blocks A2) + 1 = length (user_blocks Ac))%nat).
  { pose proof (f_equal (@length _) EB1) as L1. pose proof (f_equal (@length _) EB2) as L2'.
    unfold blocks in L1, L2'. rewrite length_map in L1, L2'. rewrite length_app in L1, L2'. cbn [length] in L1. lia. }
  pose proof (ub_shrink _ _ p n (YO10.user_block_ptrs_NoDup Ac HWc) (YO10.user_block_ptrs_NoDup A2 HW2) Hin LEN HK2) as SHR.
  pose proof (HPTR p n Hin) as PA.
  assert (INB : In (ptr_addr Lc p, n) (blocks Lc Ac)) by (rewrite EB1; apply in_or_app; right; left; reflexivity).
  split; [exact HM2|]. split; [exact HW2|]. split; [exact HB2|].
  split.
  { destruct HLE as (E1 & E2 & E3 & E4). destruct HLE2 as (F1 & F2 & F3 & F4).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite F4 by lia. apply E4. exact Hr. }
  split; [lia|]. split; [tauto|].
  split; [exists vm2; rewrite Hvm2, Hvm; apply YI04.with_vmmaps_twice|].
  split; [intros x Hx; apply HSUB; exact (proj1 (SHR x Hx))|].
  split.
  { intros q k Hq. destruct (SHR (q, k) Hq) as [Hc _]. rewrite (HSTAB q k Hc Hq). exact (HPTR q k Hc). }
  split.
  { intros q k Hq Hnf.
    assert (Hc : In (q, k) (user_blocks Ac)) by (apply HKEEP; [exact Hq | intros H; apply Hnf; apply in_or_app; left; exact H]).
    apply HK2; [exact Hc|]. intros ->.
    rewrite (nodup_key _ p k n (YO10.user_block_ptrs_NoDup Ac HWc) Hc Hin) in Hnf.
    apply Hnf. apply in_or_app. right. left. reflexivity. }
  split.
  { eapply Permutation_trans; [exact HPERM|]. rewrite EB1, EB2, PA. apply perm_free_step. }
  split.
  { intros q k i H2 Hi. destruct (SHR (q, k) H2) as [Hc _].
    pose proof (HKB2 q k i Hc H2 Hi) as Eb. rewrite (HPTR q k Hc) in Eb. rewrite Eb. exact (HBYTES q k i Hc Hi). }
  split.
  { intros a Ha Hno Hs He HE. destruct (HFRAME a Ha Hno Hs He HE) as [E1 E2].
    assert (Hnc : ~ owned B Lc Ac a) by exact (own_any L A mem md Lc Ac memc mdc a HM0 HMc Ha Hno).
    assert (Hn2 : ~ owned B L2 A2 a) by exact (own_any L A mem md L2 A2 mem2 md2 a HM0 HM2 Ha Hno).
    assert (Hns : ~ scratch B regs_c a) by (unfold scratch; intros [H|H]; [apply Hs; unfold ALLOC_STACK in *; lia | exact (He H)]).
    assert (Hnf : ~ (ptr_addr Lc p <= a < ptr_addr Lc p + n)) by (intros Hr; exact (block_not_hi_img Lc Ac memc mdc _ _ a HMc INB Hr Ha)).
    destruct (HFR2 a Ha Hnc Hn2 Hns Hnf) as [F1 F2]. split; [congruence | tauto]. }
  split.
  { intros a Ha.
    destruct (Z_le_gt_dec (spZ regs_c - ALLOC_STACK) a) as [D1|D1];
      [destruct (Z_lt_ge_dec a (spZ regs_c)) as [D2|D2]|].
    - apply HSCR2. left. lia.
    - destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
      assert (Hh : alloc_ceiling <= a < 2 ^ 64) by lia.
      assert (Hn1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho); lia).
      assert (Hn2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho); lia).
      assert (Hns : ~ scratch B regs_c a) by (unfold scratch; intros [H|H]; [lia | unfold errw in *; lia]).
      assert (Hnf : ~ (ptr_addr Lc p <= a < ptr_addr Lc p + n))
        by (intros Hr; exact (block_not_hi_img Lc Ac memc mdc _ _ a HMc INB Hr (or_introl Hh))).
      apply (proj2 (HFR2 a (or_introl Hh) Hn1 Hn2 Hns Hnf)). apply HSCR. left. exact Ha.
    - destruct Ha as [Ha|Ha]; [|apply HSCR2; right; exact Ha].
      assert (Hh : alloc_ceiling <= a < 2 ^ 64) by (unfold ALLOC_STACK in *; lia).
      assert (Hn1 : ~ owned B Lc Ac a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho); lia).
      assert (Hn2 : ~ owned B L2 A2 a) by (intros Ho; pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho); lia).
      assert (Hns : ~ scratch B regs_c a) by (unfold scratch; intros [H|H]; [lia | unfold errw in *; lia]).
      assert (Hnf : ~ (ptr_addr Lc p <= a < ptr_addr Lc p + n))
        by (intros Hr; exact (block_not_hi_img Lc Ac memc mdc _ _ a HMc INB Hr (or_introl Hh))).
      apply (proj2 (HFR2 a (or_introl Hh) Hn1 Hn2 Hns Hnf)). apply HSCR. left. exact Ha. }
  split; [exact HRO2|]. split; [intros i Hi; rewrite (HGK2 i Hi); exact (HGK i Hi)|].
  unfold rfree_b. rewrite fold_left_app. exact HRES2.
Qed.

Lemma fchain_own : forall S K E L A mem md b F Lc Ac memc mdc m' W,
  fchain S K E L A mem md b F Lc Ac memc mdc ->
  munch W memc m' -> wmono (ms_segs B) memc m' ->
  alloc_ceiling + K <= S -> S <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     (S - K <= a < S) \/ (E a /\ (alloc_ceiling <= a \/ in_globals frame_G a))) ->
  fchain S K E L A mem md b F Lc Ac m' mdc.
Proof using SEGS AX GOWN GFACT GOTG.
  intros S K E L A mem md b F Lc Ac memc mdc m' W
    (HMc & HWc & HBc & HLE & HRG & HINIT & HVM & HSUB & HPTR & HKEEP & HPERM & HBYTES & HFRAME & HSCR & HRO & HGK & HRES)
    MU WM HK HS HW.
  pose proof alloc_ceiling_val as AC.
  assert (OUTL : forall a, 0 <= a < alloc_ceiling -> ~ in_globals frame_G a -> outside W a).
  { intros a Ha Hg. destruct (outside_dec W a) as [O|O]; [exact O|].
    destruct (HW a ltac:(lia) O) as [H|(_ & [H|H])]; [lia | lia | contradiction]. }
  assert (OUTB : forall q k i, In (q, k) (blocks Lc Ac) -> 0 <= i < k -> outside W (q + i)).
  { intros q k i Hin Hi. pose proof (block_facts B _ (aa_laws API) Lc Ac memc mdc q k i HMc Hin Hi) as (_ & H1 & H2 & _).
    apply OUTL; [lia|]. intros Hg. apply (block_not_img Lc Ac memc mdc q k i HMc Hin Hi). exact (proj1 (GFACT _ Hg)). }
  assert (OUTO : forall a, owned B Lc Ac a -> outside W a).
  { intros a Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho). apply OUTL; [lia|].
    intros Hg. exact (GOWN _ _ _ _ a HMc Hg Ho). }
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HMc) as (Hh & Hl & Hmat).
  split.
  { eapply (mr_frame B _ (aa_laws API) Lc Ac memc m' mdc mdc HMc).
    - intros a Ho. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho).
      apply (munch_mbyte _ W memc m'); [exact MU | lia | exact (OUTO a Ho)].
    - intros a Ho Hp. pose proof (owned_low B _ (aa_laws API) _ _ _ _ a HMc Ho).
      apply (munch_present W memc m'); [exact MU | lia | exact (OUTO a Ho) | exact Hp].
    - intros p n i Hin Hi.
      assert (Hb : In (ptr_addr Lc p, n) (blocks Lc Ac)) by (unfold blocks; apply in_map_iff; exists (p, n); auto).
      pose proof (block_facts B _ (aa_laws API) _ _ _ _ _ _ i HMc Hb Hi) as (Hp & H1 & H2 & _).
      apply (munch_present W memc m'); [exact MU | lia | exact (OUTB _ _ i Hb Hi) | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HWc|]. split; [exact HBc|]. split; [exact HLE|]. split; [exact HRG|]. split; [exact HINIT|].
  split; [exact HVM|]. split; [exact HSUB|]. split; [exact HPTR|]. split; [exact HKEEP|]. split; [exact HPERM|].
  split.
  { intros p n i Hin Hi.
    assert (Hb : In (ptr_addr Lc p, n) (blocks Lc Ac)) by (unfold blocks; apply in_map_iff; exists (p, n); auto).
    pose proof (block_facts B _ (aa_laws API) _ _ _ _ _ _ i HMc Hb Hi) as (_ & H1 & H2 & _).
    rewrite <- (HPTR p n Hin).
    rewrite (munch_mbyte _ W memc m' (ptr_addr Lc p + i) MU ltac:(lia) (OUTB _ _ i Hb Hi)).
    rewrite (HPTR p n Hin). exact (HBYTES p n i Hin Hi). }
  split.
  { intros a Ha Hno Hs He HE. pose proof (hi_img_range a Ha) as R.
    assert (O : outside W a).
    { destruct (outside_dec W a) as [O|O]; [exact O|]. exfalso.
      destruct (HW a R O) as [H|(H & _)]; [exact (Hs H) | exact (HE H)]. }
    destruct (HFRAME a Ha Hno Hs He HE) as [E1 E2].
    split; [rewrite (munch_mbyte _ W memc m' a MU R O); exact E1|].
    rewrite E2. exact (munch_writable _ W memc m' a MU R O). }
  split; [intros a Ha; apply WM; exact (HSCR a Ha)|].
  split.
  { intros x Hro. unfold mrd.
    destruct (outside_dec W (bv_unsigned x)) as [O|O].
    - rewrite (MU x O). exact (HRO x Hro).
    - exfalso. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
      rewrite SEGS in Hro.
      destruct (HW (bv_unsigned x) ltac:(cbn in R; lia) O) as [H|(_ & [H|H])].
      + rewrite <- (Z_to_bv_bv_unsigned x) in Hro. rewrite (hi_rw (bv_unsigned x)) in Hro by lia. discriminate.
      + rewrite <- (Z_to_bv_bv_unsigned x) in Hro. rewrite (hi_rw (bv_unsigned x)) in Hro by (cbn in R; lia). discriminate.
      + rewrite <- (Z_to_bv_bv_unsigned x) in Hro. rewrite (fg_rw (bv_unsigned x) H) in Hro. discriminate. }
  split.
  { intros i Hi. rewrite <- (HGK i Hi). rewrite GOTG.
    apply (munch_mbyte _ W memc m'); [exact MU | lia|]. apply OUTL; [lia|]. rewrite fg_iff. lia. }
  exact HRES.
Qed.

Lemma fchain_post : forall S K E L A regs mem md b F L' A' regs' mem' md',
  spZ regs = S ->
  fchain S K E L A mem md b F L' A' mem' md' ->
  regs_preserved regs regs' ->
  call_post_k B MR K L A regs mem md E L' A' regs' mem' md' /\
  Permutation (blocks L A) (blocks L' A' ++ F) /\
  blocks_kept B L A mem mem' (fun a => In a (map fst F)) /\
  (forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) F -> In (q, k) (user_blocks A')) /\
  (forall x, In x (user_blocks A') -> In x (user_blocks A)) /\
  ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
  (st_init_done A = true -> st_init_done A' = true) /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  res_ok_slots A' (rfree_b b F).
Proof.
  intros S K E L A regs mem md b F L' A' regs' mem' md' HS
    (HMc & HWc & HBc & HLE & HRG & HINIT & HVM & HSUB & HPTR & HKEEP & HPERM & HBYTES & HFRAME & HSCR & HRO & HGK & HRES)
    HREGS.
  split.
  { split; [exact HMc|]. split; [exact HWc|]. split; [exact HBc|]. split; [exact HLE|].
    split; [intros p n _ H2; exact (HPTR p n H2)|]. split; [exact HREGS|]. split; [exact HVM|].
    split.
    { intros a Ha Hno _ Hs HE. apply HFRAME; [exact Ha | exact Hno | | | exact HE].
      - intros H. apply Hs. unfold scratch_k. left. rewrite HS. exact H.
      - intros H. apply Hs. unfold scratch_k. right. exact H. }
    split; [intros p n i _ H2 Hi; exact (HBYTES p n i H2 Hi)|].
    intros a [Ha|Ha]; apply HSCR; [left; rewrite <- HS; exact Ha | right; exact Ha]. }
  split; [exact HPERM|].
  split.
  { intros a k i Hin Hng Hi. unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq).
    cbn in Eq. injection Eq as <- <-.
    assert (Hng' : ~ In (ptr_addr L q, k') F) by (intros H; apply Hng; exact (in_map fst F _ H)).
    exact (HBYTES q k' i (HKEEP q k' Hq Hng') Hi). }
  split; [exact HKEEP|]. split; [exact HSUB|]. split; [exact HRO|]. split; [exact HGK|].
  split; [exact HINIT|]. split; [exact HRG|]. exact HRES.
Qed.

End Chain.
