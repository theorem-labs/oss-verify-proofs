From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require MState Mem Frame Exec Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require ReallocRuns.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rf_in_drop : forall {X} (l1 l2 : list X) x y, In x (l1 ++ y :: l2) -> x <> y -> In x (l1 ++ l2).
Proof.
  intros X l1 l2 x y H Hne. apply in_app_or in H. apply in_or_app.
  destruct H as [H|[H|H]]; [left; exact H | congruence | right; exact H].
Qed.

Lemma rf_in_mid : forall {X} (l1 l2 : list X) x y, In x (l1 ++ l2) -> In x (l1 ++ y :: l2).
Proof.
  intros X l1 l2 x y H. apply in_app_or in H. apply in_or_app.
  destruct H as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma rf_nodup_mid : forall (l1 l2 : list (Z * Z)) p k,
  NoDup (map fst (l1 ++ (p, k) :: l2)) -> NoDup (map fst (l1 ++ l2)) /\ ~ In p (map fst (l1 ++ l2)).
Proof.
  intros l1 l2 p k H. apply NoDup_ListNoDup in H. rewrite map_app in H |- *. cbn [map fst] in H.
  split; [apply NoDup_ListNoDup; exact (NoDup_remove_1 _ _ _ H) | exact (NoDup_remove_2 _ _ _ H)].
Qed.

Lemma rf_lsum_app : forall l1 l2, lsum (l1 ++ l2) = lsum l1 + lsum l2.
Proof. induction l1 as [|[a k] t IH]; intros l2; cbn [app lsum]; [lia|]. rewrite IH. lia. Qed.

Lemma rf_lsum_nonneg : forall l, Forall (fun ak => 0 <= snd ak) l -> 0 <= lsum l.
Proof.
  induction l as [|[a k] t IH]; intros H; cbn [lsum]; [lia|].
  inversion H as [|? ? H1 H2]; subst. cbn [snd] in H1. specialize (IH H2). lia.
Qed.

Lemma rf_sep : forall (P : Z -> Prop) a n lo len, 0 < n -> 0 < len ->
  (forall x, lo <= x < lo + len -> P x) -> (forall i, 0 <= i < n -> ~ P (a + i)) -> a + n <= lo \/ lo + len <= a.
Proof.
  intros P a n lo len Hn Hl HP HN.
  destruct (Z_le_gt_dec (a + n) lo) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (lo + len) a) as [H'|H']; [right; exact H'|].
  exfalso. apply (HN (Z.max a lo - a)); [lia|]. replace (a + (Z.max a lo - a)) with (Z.max a lo) by lia. apply HP. lia.
Qed.

Lemma rf_nodup_fst : forall (l : list (sptr * Z)) x a b, NoDup (map fst l) -> In (x, a) l -> In (x, b) l -> a = b.
Proof.
  intros l x a b HN. apply NoDup_ListNoDup in HN. revert x a b HN.
  induction l as [|[y c] t IH]; intros x a b HN Ha Hb; [destruct Ha|].
  cbn [map fst] in HN. apply List.NoDup_cons_iff in HN as [Hn HN].
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - congruence.
  - exfalso. apply Hn. apply in_map_iff. exists (x, b). split; [|exact Hb]. cbn. congruence.
  - exfalso. apply Hn. apply in_map_iff. exists (x, a). split; [|exact Ha]. cbn. congruence.
  - exact (IH x a b HN Ha Hb).
Qed.

Lemma rf_page_round_ge : forall x, 0 <= x -> x <= page_round x.
Proof. intros x Hx. unfold page_round, PGSZ. Z.div_mod_to_equations. lia. Qed.

Lemma rf_not_out : forall W a, ~ Frame.outside W a -> exists lo hi, In (lo, hi) W /\ lo <= a < hi.
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

(* An entry of G that covers [lo, hi) whole, found by vm_compute over the list, so that rf_in_G does not depend on how
   the generated omx_G list orders or merges the alloc.c cells. *)
Definition rf_covers (G : list (Z * Z)) (lo hi : Z) : bool :=
  existsb (fun e => (fst e <=? lo) && (hi <=? fst e + snd e)) G.

Lemma rf_covers_in : forall G lo hi x, rf_covers G lo hi = true -> lo <= x < hi -> in_globals G x.
Proof.
  intros G lo hi x H Hx. unfold rf_covers in H. apply existsb_exists in H. destruct H as ([l k] & Hin & Hc).
  apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2. cbn [fst snd] in *.
  exists l, k. split; [exact Hin | lia].
Qed.

(* #102 ubsan twin 27566683 symtab: g_ran_out 0x35258 (1 byte, 7 padding bytes), g_live 0x35260, g_peak 0x35268,
   g_count 0x35270, g_fail_at 0x24fd8 (8 bytes each). *)
Lemma rf_in_G : forall x, (0x35258 <= x < 0x35278 \/ 0x24fd8 <= x < 0x24fe0) -> in_globals omx_G x.
Proof.
  intros x [Hx|Hx].
  - destruct (Z_lt_le_dec x 0x35260); [|destruct (Z_lt_le_dec x 0x35268); [|destruct (Z_lt_le_dec x 0x35270)]].
    + apply (rf_covers_in omx_G 0x35258 0x35260); [vm_compute; reflexivity | lia].
    + apply (rf_covers_in omx_G 0x35260 0x35268); [vm_compute; reflexivity | lia].
    + apply (rf_covers_in omx_G 0x35268 0x35270); [vm_compute; reflexivity | lia].
    + apply (rf_covers_in omx_G 0x35270 0x35278); [vm_compute; reflexivity | lia].
  - apply (rf_covers_in omx_G 0x24fd8 0x24fe0); [vm_compute; reflexivity | lia].
Qed.

Lemma rf_statics_G : forall a, alloc_statics a -> in_globals omx_G a.
Proof. intros a H. apply rf_in_G. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in H. lia. Qed.

Ltac rf_cs_cases tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold callee_saved in Hr;
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [tac .. |];
  let Hr' := fresh "Hr" in
  assert (Hr' : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    by lia;
  destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; tac.

Ltac rf_out := cbn [Frame.outside]; repeat split; lia.

Section Facts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Lemma rf_ro_in_img : forall C, img_check B C = true -> C + 4096 <= 2 ^ 64 ->
  forall x : word, Mem.ro_addr segs x = true -> in_img B (bv_unsigned x).
Proof.
  intros C H HC x Hx. unfold img_check in H. apply andb_prop in H as [H1 _]. rewrite forallb_forall in H1.
  unfold Mem.ro_addr in Hx. destruct (find_segment segs (bv_unsigned x) 1) as [seg|] eqn:F; [|discriminate].
  destruct (kb_find_segment segs _ _ _ F) as (Hin & Hlo & Hhi).
  specialize (H1 seg Hin). apply Z.leb_le in H1.
  change segs with (ms_segs B) in Hin.
  split; [intros E; rewrite E in Hin; destruct Hin|].
  exists (segment_reservation seg). split; [unfold segments_reserved; apply in_map; exact Hin|].
  pose proof (N2Z.is_nonneg (seg_base seg)). pose proof (N2Z.is_nonneg (seg_size seg)).
  unfold segment_reservation, page_round_down_Z, page_round_up_Z, page_size. cbn [fst snd].
  rewrite !MState.unsigned_lit by (Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. lia.
Qed.

Lemma rf_bytes_frame : forall m m' a bs, Mem.bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  Mem.bytes_at segs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H3) H. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). exact (H (Z.of_nat i) ltac:(lia)).
Qed.

Lemma rf_word_frame : forall m m' a v, word_mem segs m a v ->
  (forall i, 0 <= i < 8 -> mbyte segs m' (a + i) = mbyte segs m (a + i)) -> word_mem segs m' a v.
Proof. intros m m' a v Hw H k Hk. rewrite H by lia. exact (Hw k Hk). Qed.

Lemma rf_word_hd8 : forall m a v, word_mem segs m a v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  Mem.bytes_at segs m a (ReallocRuns.hd8 v).
Proof.
  intros m a v Hw Ha Hb.
  assert (E : forall k, (k < 8)%nat -> Mem.mrd segs m (Mem.wa (a + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte v 8 k)))
    by exact Hw.
  split; [exact Ha|]. split; [cbn [length ReallocRuns.hd8]; lia|].
  intros i Hi. cbn [length ReallocRuns.hd8] in Hi.
  do 8 (destruct i as [|i]; [rewrite E by lia; reflexivity |]). lia.
Qed.

Lemma rf_bytes_word : forall m a v, Mem.bytes_at segs m a (Mem.le8 (Z_to_bv 64 v)) -> word_mem segs m a (v mod 2 ^ 64).
Proof.
  intros m a v H. pose proof (bytes_at_le8_word segs m a _ H) as W. rewrite MState.unsigned_lit_wrap in W. exact W.
Qed.

Lemma rf_word_bytes : forall m a v, word_mem segs m a v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  Mem.bytes_at segs m a (Mem.le8 (Z_to_bv 64 v)).
Proof. intros m a v Hw Hv Ha Hb. exact (word_mem_le8 segs m a v Hw Hv Ha Hb). Qed.

Lemma rf_wr_at : forall m a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> writable_at segs m (a + i)) -> Mem.wr_at segs m a n.
Proof. intros m a n Ha Hn H. split; [exact Ha|]. split; [exact Hn|]. intros i Hi. exact (H i Hi). Qed.

Lemma rf_stk_present : forall m a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> present m (a + i)) -> Frame.stk segs m a (a + n).
Proof.
  intros m a n Ha Hn H. split; [exact Ha|]. split; [exact Hn|]. intros x Hx.
  destruct (H (x - a) ltac:(lia)) as (b & Hb). replace (a + (x - a)) with x in Hb by lia.
  unfold wview, Mem.mrd, Mem.wa. rewrite Hb. split; [discriminate | exists b; reflexivity].
Qed.

Lemma rf_present_some : forall m a, present m a -> mbyte segs m a <> None.
Proof. intros m a (b & Hb). unfold mbyte. rewrite Hb. discriminate. Qed.

Lemma rf_bytes_list : forall m a n, 0 <= n -> (forall i, 0 <= i < n -> mbyte segs m (a + i) <> None) ->
  exists l, Z.of_nat (length l) = n /\ forall i, 0 <= i < n -> mbyte segs m (a + i) = nth_error l (Z.to_nat i).
Proof.
  intros m a n Hn H. rewrite <- (Z2Nat.id n) in H |- * by exact Hn. clear Hn.
  induction (Z.to_nat n) as [|j IH].
  - exists []. split; [reflexivity | intros i Hi; lia].
  - assert (IH' : forall i, 0 <= i < Z.of_nat j -> mbyte segs m (a + i) <> None) by (intros i Hi; apply H; lia).
    destruct (IH IH') as (l & Hl & Hi).
    destruct (mbyte segs m (a + Z.of_nat j)) as [c|] eqn:E; [|exfalso; exact (H (Z.of_nat j) ltac:(lia) E)].
    exists (l ++ [c]). rewrite length_app. cbn [length]. split; [lia|].
    intros i Hi'. destruct (Z.eq_dec i (Z.of_nat j)) as [->|Hne].
    + rewrite nth_error_app2 by lia. rewrite Nat2Z.id. replace (j - length l)%nat with 0%nat by lia. exact E.
    + rewrite nth_error_app1 by lia. apply Hi. lia.
Qed.

Lemma rf_kb_mid_tail2 : img_low B -> forall K sp L A mem md E1 L' A' mem1 md' mem' W (E2 : Z -> Prop),
  kb_mid B API K sp L A mem md E1 L' A' mem1 md' ->
  Frame.munch W mem1 mem' -> Frame.wmono (ms_segs B) mem1 mem' -> (forall x, mem1 x <> None -> mem' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - K <= x < sp) -> ~ E2 x -> Frame.outside W x) ->
  (forall x, 0 <= x < alloc_ceiling -> owned B L' A' x -> Frame.outside W x) ->
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
     mbyte (ms_segs B) mem' (ptr_addr L p + i) = mbyte (ms_segs B) mem1 (ptr_addr L p + i)) ->
  kb_mid B API K sp L A mem md (fun a => E1 a \/ E2 a) L' A' mem' md'.
Proof.
  intros [HI _] K sp L A mem md E1 L' A' mem1 md' mem' W E2 (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1 & S1)
    Hm Hw Hp HE HO HB.
  pose proof alloc_ceiling_lt as Hc. pose proof alloc_ceiling_val as Hc'.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ M1) as (Hh & Hl & Hmat).
  split.
  { apply (mr_frame _ _ (aa_laws API) L' A' mem1 mem' md' md' M1).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho).
      apply (KindBGlue.mbyte_munch (ms_segs B) W); [exact Hm | lia | apply HO; [lia | exact Ho]].
    - intros a Ho Hpr. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho).
      apply (present_munch W mem1); [exact Hm | lia | apply HO; [lia | exact Ho] | exact Hpr].
    - intros q n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q n i M1 Hin Hi) as ((b & Hb) & _).
      destruct (mem' (Z_to_bv 64 (ptr_addr L' q + i))) as [b'|] eqn:E; [exists b'; exact E|].
      exfalso. apply (Hp (Z_to_bv 64 (ptr_addr L' q + i))); [rewrite Hb; discriminate | exact E].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact W1|]. split; [exact B1|]. split; [exact Y1|]. split; [exact P1|]. split; [exact D1|].
  split.
  { intros a Ha Ho Ho' Hs He.
    assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | apply HI in Ha; lia]).
    destruct (F1 a Ha Ho Ho' ltac:(tauto) ltac:(tauto)) as [E1a E1w].
    assert (Hout : Frame.outside W a) by (apply HE; [exact Hr | tauto | tauto]).
    split.
    - rewrite (KindBGlue.mbyte_munch (ms_segs B) W mem1 mem' a Hm Hr Hout). exact E1a.
    - rewrite E1w. exact (writable_munch (ms_segs B) W mem1 mem' a Hm Hr Hout). }
  split.
  { intros p n i Hin Hin' Hi. rewrite (HB p n i Hin Hin' Hi). exact (K1 p n i Hin Hin' Hi). }
  intros a Ha. unfold writable_at. apply Hw. exact (S1 a Ha).
Qed.

Lemma rf_blocks_user : forall L A p k, In (p, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = p.
Proof.
  intros L A p k Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q k'] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst k'.
  exists q. split; [exact Hq | exact E1].
Qed.

Lemma rf_user_blocks_in : forall L A q k, In (q, k) (user_blocks A) -> In (ptr_addr L q, k) (blocks L A).
Proof. intros L A q k H. unfold blocks. apply in_map_iff. exists (q, k). split; [reflexivity | exact H]. Qed.

Lemma rf_blk_range : forall L A mem md p k, MR L A mem md -> In (p, k) (blocks L A) ->
  4096 <= p /\ p + k <= alloc_ceiling.
Proof.
  intros L A mem md p k HM Hin. destruct (rf_blocks_user L A p k Hin) as (q & Hq & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L A mem md q k HM Hq).
Qed.

Lemma rf_present_mrd : forall m a, present m a -> exists b, Mem.mrd segs m (Mem.wa a) = Some b.
Proof. intros m a (b & Hb). exists b. unfold Mem.mrd, Mem.wa. rewrite Hb. reflexivity. Qed.

Lemma rf_present_wr : forall m a, present m a -> writable_at segs m a.
Proof. intros m a (b & Hb). unfold writable_at, wview. rewrite Hb. discriminate. Qed.

Lemma rf_ro_agree_munch : forall W m m', ro_agree segs m -> Frame.munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside W a -> Mem.ro_addr segs (Z_to_bv 64 a) = false) ->
  ro_agree segs m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold Mem.mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (HW (bv_unsigned a) Hr Ho) as E. rewrite Step.Z_to_bv_lit_self in E. congruence.
Qed.

Lemma rf_guard_owned : forall L A x, ms_got_guard B <= x < ms_got_guard B + 8 -> owned B L A x.
Proof. intros L A x H. right. unfold static_owned. right; right; right; right; left. exact H. Qed.

Lemma rf_libc_owned : forall L A x, ms_libc B + 8 <= x < ms_libc B + 16 -> owned B L A x.
Proof. intros L A x H. right. unfold static_owned. right; right; left. exact H. Qed.

End Facts.

Section Facts2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis HG : globals_free B API omx_G.

Lemma rf_check : img_check B 140735332483072 = true.
Proof. unfold img_check. rewrite HSEG. vm_compute. reflexivity. Qed.

Lemma rf_img : img_low B.
Proof. apply (img_low_of_check B 140735332483072); [exact rf_check | pose proof alloc_ceiling_value; lia]. Qed.

Lemma rf_glob_img : forall x, in_globals omx_G x -> in_img B x.
Proof. intros x Hx. exact (proj1 (HG x Hx)). Qed.

Lemma rf_glob_free_at : forall L A mem md x, aa_MR API L A mem md -> in_globals omx_G x ->
  (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) -> False.
Proof.
  intros L A mem md x HM Hx Ho. destruct (HG x Hx) as (_ & _ & _ & _ & Hm).
  destruct (Hm L A mem md HM) as (Hno & Hnb).
  destruct Ho as [Ho | (p & n & Hp & Hpx)]; [exact (Hno Ho) | exact (Hnb p n Hp Hpx)].
Qed.

Lemma rf_avoid : forall L A mem md W x, aa_MR API L A mem md ->
  (forall lo hi, In (lo, hi) W -> alloc_ceiling <= lo \/ (forall y, lo <= y < hi -> in_globals omx_G y)) ->
  0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
  Frame.outside W x.
Proof.
  intros L A mem md W x HM HW Hx Ho. apply kb_outside. intros lo hi Hin Hlh.
  destruct (HW lo hi Hin) as [Hl | Hg]; [lia | exact (rf_glob_free_at L A mem md x HM (Hg x Hlh) Ho)].
Qed.

Lemma rf_ro_false_glob : forall a, in_globals omx_G a -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. destruct (HG a Ha) as (_ & Hl & (seg & E & Hw) & _). pose proof alloc_ceiling_lt.
  unfold Mem.ro_addr. rewrite MState.unsigned_lit by lia. rewrite E, Hw. reflexivity.
Qed.

Lemma rf_ro_false_notimg : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hn. destruct (Mem.ro_addr (ms_segs B) (Z_to_bv 64 a)) eqn:E; [|reflexivity].
  exfalso. apply Hn. pose proof (rf_ro_in_img B 140735332483072 rf_check ltac:(lia) _ E) as H.
  rewrite MState.unsigned_lit in H by lia. exact H.
Qed.

Lemma rf_ro_false_low : forall a, alloc_ceiling <= a < 2 ^ 64 -> Mem.ro_addr (ms_segs B) (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof alloc_ceiling_value. destruct rf_img as [_ HI]. unfold Mem.ro_addr. rewrite MState.unsigned_lit by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; pose proof (HI a seg E); lia | reflexivity].
Qed.

End Facts2.
