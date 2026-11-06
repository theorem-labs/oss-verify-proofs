From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 KindBGlue FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes tx_put_c RttDefs round_trip_text_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.

Lemma rg_vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof using SEG AX FG. intros v1 v2 [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma rg_word : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof using SEG AX FG.
  intros x. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R.
Qed.

Lemma rg_conv : forall m m' (x : word),
  mbyte segs m' (bv_unsigned x) = mbyte segs m (bv_unsigned x) ->
  (writable_at segs m (bv_unsigned x) -> writable_at segs m' (bv_unsigned x)) ->
  Mem.mrd segs m' x = Mem.mrd segs m x /\ (wview segs m x <> None -> wview segs m' x <> None).
Proof using SEG AX FG.
  intros m m' x H1 H2. unfold mbyte, writable_at in *. rewrite !Z_to_bv_bv_unsigned in *.
  split; [exact H1 | exact H2].
Qed.

Lemma rg_blk_in : forall L A a k, In (a, k) (blocks L A) -> exists q, In (q, k) (user_blocks A) /\ ptr_addr L q = a.
Proof using SEG AX FG.
  intros L A a k Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q n] & Eq & Hq). cbn [fst snd] in Eq. injection Eq as E1 E2. subst n.
  exists q. split; [exact Hq | exact E1].
Qed.

Lemma rg_blk_of : forall L A q k, In (q, k) (user_blocks A) -> In (ptr_addr L q, k) (blocks L A).
Proof using SEG AX FG. intros L A q k H. unfold blocks. apply in_map_iff. exists (q, k). split; [reflexivity | exact H]. Qed.

Lemma rg_blk : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present mem (a + i) /\ 4096 <= a /\ a + k <= alloc_ceiling /\ ~ owned B L A (a + i).
Proof using SEG AX FG.
  intros L A mem md a k i HM Hin Hi. destruct (rg_blk_in L A a k Hin) as (q & Hq & <-).
  exact (mr_blocks _ _ (aa_laws API) L A mem md q k i HM Hq Hi).
Qed.

Lemma rg_pairwise_in : forall {T : Type} (R : T -> T -> Prop) (l : list T) x y,
  YO0f.pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof using SEG AX FG.
  intros T R l. induction l as [|h l IH]; intros x y Hp Hx Hy Hne; cbn in *; [contradiction|].
  destruct Hp as [Hh Hp]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - left. exact (Hh y Hy).
  - right. exact (Hh x Hx).
  - exact (IH x y Hp Hx Hy Hne).
Qed.

Lemma in_img_lt : forall a, in_img B a -> 0 <= a < 2 ^ 40.
Proof using SEG AX FG.
  intros a [_ (r & Hr & H1)]. rewrite SEG in Hr.
  assert (Eb : forallb (fun r => bv_unsigned (fst r) + bv_unsigned (snd r) <=? 2 ^ 40) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Eb. specialize (Eb r Hr). apply Z.leb_le in Eb.
  pose proof (bv_unsigned_in_range _ (fst r)). lia.
Qed.

Lemma rg_img_range : forall lo hi,
  existsb (fun s => (bv_unsigned (fst s) <=? lo) && (hi <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs) = true ->
  forall a, lo <= a < hi -> in_img B a.
Proof using SEG AX FG.
  intros lo hi Eb a Ha.
  assert (NE : match rsegs with [] => false | _ :: _ => true end = true) by (vm_compute; reflexivity).
  apply existsb_exists in Eb. destruct Eb as (s & Hs & Hb).
  apply andb_true_iff in Hb. destruct Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split.
  - rewrite SEG. intros N. rewrite N in NE. cbn in NE. discriminate NE.
  - exists s. split; [rewrite SEG; exact Hs | lia].
Qed.

(* #102: the four alloc.c words are LedgerCells' GL_ cells (Ledger's G_LIVE .. G_FAIL are the GL_ names); frame_G =
   LedgerCells.GL_runs = [(GL_FAIL, 16); (GL_OWN_RAN_OUT, 40)] (FrameAPI.v at cold/h-rw-pre-4-rw102-ent bfd74483ce6c).
   g_live / g_peak / g_count sit in the second run, g_fail_at in the first. *)
Lemma statics_img : forall a, alloc_statics a -> in_img B a /\ never_owned B API a.
Proof using SEG AX FG.
  intros a Ha. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. split.
  - destruct Ha as [H|[H|[H|H]]].
    + apply (rg_img_range GL_OWN_RAN_OUT (GL_OWN_RAN_OUT + 40)); [vm_compute; reflexivity | unfold GL_OWN_RAN_OUT; lia].
    + apply (rg_img_range GL_OWN_RAN_OUT (GL_OWN_RAN_OUT + 40)); [vm_compute; reflexivity | unfold GL_OWN_RAN_OUT; lia].
    + apply (rg_img_range GL_OWN_RAN_OUT (GL_OWN_RAN_OUT + 40)); [vm_compute; reflexivity | unfold GL_OWN_RAN_OUT; lia].
    + apply (rg_img_range GL_FAIL (GL_FAIL + 8)); [vm_compute; reflexivity | unfold GL_FAIL; lia].
  - unfold never_owned. intros L0 A0 mem0 md0 HM. apply (FG L0 A0 mem0 md0 a HM).
    unfold in_globals, frame_G, GL_runs. destruct Ha as [H|[H|[H|H]]].
    + exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | unfold GL_OWN_RAN_OUT; lia].
    + exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | unfold GL_OWN_RAN_OUT; lia].
    + exists GL_OWN_RAN_OUT, 40. split; [right; left; reflexivity | unfold GL_OWN_RAN_OUT; lia].
    + exists GL_FAIL, 16. split; [left; reflexivity | unfold GL_FAIL; lia].
Qed.

(* #102: the errno cell is read from strtod_c.STRTOD_ERRNO by name (the image's tp - 164, FrameAPI's ms_tp / ms_errno_off),
   not restated as a literal. *)
Lemma errno_img : errno_addr B = strtod_c.STRTOD_ERRNO -> forall i, 0 <= i < 4 -> in_img B (errno_addr B + i).
Proof using SEG AX FG.
  intros He i Hi. rewrite He.
  apply (rg_img_range strtod_c.STRTOD_ERRNO (strtod_c.STRTOD_ERRNO + 4)); [vm_compute; reflexivity | lia].
Qed.

Lemma rstep_refl : forall K S E g L A mem md,
  MR L A mem md -> WF A -> bounded A -> (forall a, rwin B K S a -> writable_at segs mem a) ->
  rstep B API K S E g L A mem md L A mem md.
Proof using SEG AX FG.
  intros K S E g L A mem md HM HWF HB HS.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HB|]. split; [tauto|].
  split; [intros a k Hin _ _; exact Hin|].
  split; [exists (m_vmmaps md); symmetry; apply kb_vm_id|].
  split; [intros a _ _ _; split; [reflexivity | tauto]|].
  split; [intros a _ _ _ _; split; [reflexivity | tauto]|].
  split; [intros a k i _ _ _ _; reflexivity|].
  exact HS.
Qed.

Lemma rstep_seq : forall K S E1 E2 g1 g2 L A mem md L1 A1 mem1 md1 L2 A2 mem2 md2,
  rstep B API K S E1 g1 L A mem md L1 A1 mem1 md1 ->
  rstep B API K S E2 g2 L1 A1 mem1 md1 L2 A2 mem2 md2 ->
  (forall a k, In (a, k) (blocks L A) -> 0 < k -> ~ g1 a -> ~ g2 a) ->
  rstep B API K S (fun x => E1 x \/ E2 x) g1 L A mem md L2 A2 mem2 md2.
Proof using SEG AX FG.
  intros K S E1 E2 g1 g2 L A mem md L1 A1 mem1 md1 L2 A2 mem2 md2
    (M1 & W1 & B1 & I1 & K1 & D1 & F1 & G1 & U1 & S1) (M2 & W2 & B2 & I2 & K2 & D2 & F2 & G2 & U2 & S2) Hg.
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split; [intros H; exact (I2 (I1 H))|].
  split; [intros a k Hin Hk Hn; exact (K2 a k (K1 a k Hin Hk Hn) Hk (Hg a k Hin Hk Hn))|].
  split; [destruct D1 as (v1 & ->); destruct D2 as (v2 & ->); exists v2; apply rg_vm_twice|].
  split.
  { intros a Ha Hs He. destruct (F1 a Ha Hs (fun h => He (or_introl h))) as [X1 Y1].
    destruct (F2 a Ha Hs (fun h => He (or_intror h))) as [X2 Y2]. split; [congruence | tauto]. }
  split.
  { intros a Hi Hn Hs He. destruct (G1 a Hi Hn Hs (fun h => He (or_introl h))) as [X1 Y1].
    destruct (G2 a Hi Hn Hs (fun h => He (or_intror h))) as [X2 Y2]. split; [congruence | tauto]. }
  split.
  { intros a k i Hin Hn Hi He. assert (Hk : 0 < k) by lia.
    rewrite (U2 a k i (K1 a k Hin Hk Hn) (Hg a k Hin Hk Hn) Hi (fun h => He (or_intror h))).
    exact (U1 a k i Hin Hn Hi (fun h => He (or_introl h))). }
  exact S2.
Qed.

Lemma rstep_E : forall K S (E E' g g' : Z -> Prop) L A mem md L' A' mem' md',
  rstep B API K S E g L A mem md L' A' mem' md' -> (forall a, E a -> E' a) -> (forall a, g a -> g' a) ->
  rstep B API K S E' g' L A mem md L' A' mem' md'.
Proof using SEG AX FG.
  intros K S E E' g g' L A mem md L' A' mem' md' (M & W & Bd & Hd & Kb & D & F & G & U & Sw) HE Hg.
  split; [exact M|]. split; [exact W|]. split; [exact Bd|]. split; [exact Hd|].
  split; [intros a k Hin Hk Hn; exact (Kb a k Hin Hk (fun h => Hn (Hg a h)))|].
  split; [exact D|].
  split; [intros a Ha Hs He; exact (F a Ha Hs (fun h => He (HE a h)))|].
  split; [intros a Hi Hn Hs He; exact (G a Hi Hn Hs (fun h => He (HE a h)))|].
  split; [intros a k i Hin Hn Hi He; exact (U a k i Hin (fun h => Hn (Hg a h)) Hi (fun h => He (HE _ h)))|].
  exact Sw.
Qed.

Lemma rstep_widen : forall Kc Sc K S E g L A mem md L' A' mem' md',
  rstep B API Kc Sc E g L A mem md L' A' mem' md' ->
  S - K <= Sc - Kc -> Sc <= S ->
  alloc_ceiling <= S - K -> S <= 2 ^ 64 ->
  (forall a, rwin B K S a -> writable_at segs mem a) ->
  (forall a, S - K <= a < S -> ~ (Sc - Kc <= a < Sc) -> E a -> writable_at segs mem' a) ->
  rstep B API K S E g L A mem md L' A' mem' md'.
Proof using SEG AX FG.
  intros Kc Sc K S E g L A mem md L' A' mem' md' (M & W & Bd & Hd & Kb & D & F & G & U & Sw) H1 H2 Hc Hs HS HE.
  assert (Sub : forall a, rwin B Kc Sc a -> rwin B K S a).
  { unfold rwin. intros a [Ha|Ha]; [left; lia | right; exact Ha]. }
  split; [exact M|]. split; [exact W|]. split; [exact Bd|]. split; [exact Hd|]. split; [exact Kb|]. split; [exact D|].
  split; [intros a Ha Hn He; exact (F a Ha (fun h => Hn (Sub a h)) He)|].
  split; [intros a Hi Ho Hn He; exact (G a Hi Ho (fun h => Hn (Sub a h)) He)|].
  split; [exact U|].
  intros a Ha.
  assert (D2 : rwin B Kc Sc a \/ ~ rwin B Kc Sc a) by (unfold rwin; lia).
  destruct D2 as [D2|D2]; [exact (Sw a D2)|].
  assert (Ha2 : S - K <= a < S) by (unfold rwin in Ha, D2; lia).
  assert (Hn2 : ~ (Sc - Kc <= a < Sc)) by (unfold rwin in D2; lia).
  unfold writable_at. intros Hw.
  assert (NE : ~ E a) by (intros He; exact (HE a Ha2 Hn2 He Hw)).
  destruct (F a ltac:(lia) D2 NE) as [_ Wi].
  exact (proj1 Wi (HS a Ha) Hw).
Qed.

Lemma rstep_E_drop : forall K S (E E' g : Z -> Prop) L A mem md L' A' mem' md',
  rstep B API K S E g L A mem md L' A' mem' md' ->
  MR L A mem md -> alloc_ceiling <= S - K -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  (forall a, E a -> E' a \/ rwin B K S a \/
     (0 <= a < alloc_ceiling /\ ~ in_img B a /\ forall b k, In (b, k) (blocks L A) -> ~ g b -> ~ (b <= a < b + k))) ->
  rstep B API K S E' g L A mem md L' A' mem' md'.
Proof using SEG AX FG.
  intros K S E E' g L A mem md L' A' mem' md' (M & W & Bd & Hd & Kb & D & F & G & U & Sw) HM Hc Herr HD.
  split; [exact M|]. split; [exact W|]. split; [exact Bd|]. split; [exact Hd|]. split; [exact Kb|]. split; [exact D|].
  split.
  { intros a Ha Hs He'. apply F; [exact Ha | exact Hs |]. intros He.
    destruct (HD a He) as [X|[X|(X1 & _)]]; [exact (He' X) | exact (Hs X) | lia]. }
  split.
  { intros a Hi Hno Hs He'. apply G; [exact Hi | exact Hno | exact Hs |]. intros He.
    destruct (HD a He) as [X|[X|(_ & X2 & _)]]; [exact (He' X) | exact (Hs X) | exact (X2 Hi)]. }
  split.
  { intros b k i Hin Hn Hi He'. apply (U b k i Hin Hn Hi). intros He.
    destruct (HD _ He) as [X|[X|(_ & _ & X3)]].
    - exact (He' X).
    - destruct (rg_blk L A mem md b k i HM Hin Hi) as (_ & H1 & H2 & _).
      unfold rwin in X. destruct X as [X|X]; [lia|].
      destruct (rg_blk_in L A b k Hin) as (q & Hq & Eq).
      apply (ax_blocks_img AX L A mem md q k i HM Hq Hi). rewrite Eq.
      replace (b + i) with (errno_addr B + (b + i - errno_addr B)) by lia.
      apply errno_img; [exact Herr | lia].
    - exact (X3 b k Hin Hn ltac:(lia)). }
  exact Sw.
Qed.

Lemma rstep_of_rpost : forall K L A regs mem md E gone L' A' regs' mem' md',
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  rstep B API K (spZ regs) E (fun a => exists n, gone a n) L A mem md L' A' mem' md'.
Proof using SEG AX FG.
  intros K L A regs mem md E gone L' A' regs' mem' md'
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H5|].
  split.
  { intros a k Hin Hk Hg. destruct (rg_blk_in L A a k Hin) as (q & Hq & <-).
    assert (Hq' : In (q, k) (user_blocks A')) by (apply H8; [exact Hq | intros h; apply Hg; exists k; exact h]).
    rewrite <- (H9 q k Hq Hq'). apply rg_blk_of. exact Hq'. }
  split; [exact H11|].
  split; [exact H12|].
  split; [exact H13|].
  split.
  { intros a k i Hin Hg Hi He. destruct (rg_blk_in L A a k Hin) as (q & Hq & <-).
    assert (Hq' : In (q, k) (user_blocks A')) by (apply H8; [exact Hq | intros h; apply Hg; exists k; exact h]).
    exact (H14 q k i Hq Hq' Hi He). }
  exact H15.
Qed.

Lemma rstep_of_call_post_k : forall K L A regs mem md E (g : Z -> Prop) L' A' regs' mem' md',
  MR L A mem md ->
  call_post_k B MR K L A regs mem md E L' A' regs' mem' md' ->
  (st_init_done A = true -> st_init_done A' = true) ->
  (forall a k, In (a, k) (blocks L A) -> 0 < k -> ~ g a -> In (a, k) (blocks L' A')) ->
  (forall a k i, In (a, k) (blocks L A) -> ~ g a -> 0 <= i < k -> ~ E (a + i) ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
  rstep B API K (spZ regs) E g L A mem md L' A' mem' md'.
Proof using SEG AX FG.
  intros K L A regs mem md E g L' A' regs' mem' md' HM
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10) HI HK HU.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact HI|]. split; [exact HK|].
  split; [exact H7|].
  split.
  { intros a Ha Hs He. apply H8; [left; exact Ha | | | exact Hs | exact He].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ho). lia. }
  split.
  { intros a Hi Hn Hs He.
    apply H8; [right; exact Hi | exact (Hn L A mem md HM) | exact (Hn L' A' mem' md' H1) | exact Hs | exact He]. }
  split; [exact HU|].
  exact H10.
Qed.

Lemma rstep_of_tx_frame : forall K regs E (g : Z -> Prop) L A mem md L' A' mem' md',
  MR L A mem md ->
  tx_frame B API K regs E L A mem md L' A' mem' md' ->
  (st_init_done A = true -> st_init_done A' = true) ->
  (forall a k, In (a, k) (blocks L A) -> 0 < k -> ~ g a -> In (a, k) (blocks L' A')) ->
  (forall a k i, In (a, k) (blocks L A) -> ~ g a -> 0 <= i < k -> ~ E (a + i) ->
     mbyte segs mem' (a + i) = mbyte segs mem (a + i)) ->
  rstep B API K (spZ regs) E g L A mem md L' A' mem' md'.
Proof using SEG AX FG.
  intros K regs E g L A mem md L' A' mem' md' HM
    (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) HI HK HU.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact HI|]. split; [exact HK|].
  split; [exact H7|].
  split.
  { intros a Ha Hs He. apply H8; [left; exact Ha | | | exact Hs | exact He].
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H1 Ho). lia. }
  split.
  { intros a Hi Hn Hs He.
    apply H8; [right; exact Hi | exact (Hn L A mem md HM) | exact (Hn L' A' mem' md' H1) | exact Hs | exact He]. }
  split; [exact HU|].
  exact H10.
Qed.

Lemma rstep_of_munch : forall K S E g L A mem mem' md W,
  MR L A mem md -> WF A -> bounded A ->
  (forall a, rwin B K S a -> writable_at segs mem a) ->
  Frame.munch W mem mem' -> Frame.wmono segs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x -> rwin B K S x \/ E x) ->
  (forall x, 0 <= x < alloc_ceiling -> (owned B L A x \/ exists p n, In (p, n) (blocks L A) /\ p <= x < p + n) ->
     Frame.outside W x) ->
  rstep B API K S E g L A mem md L A mem' md.
Proof using SEG AX FG.
  intros K S E g L A mem mem' md W HM HWF HB HS Hm Hw HW HO.
  pose proof YM05.alloc_ceiling_lt as Hc. pose proof YM05.alloc_ceiling_value as Hc'.
  assert (Out : forall x, 0 <= x < 2 ^ 64 -> ~ rwin B K S x -> ~ E x -> Frame.outside W x).
  { intros x Hx Hs He. destruct (kb_outside_dec W x) as [H|H]; [exact H|]. exfalso.
    destruct (HW x Hx H) as [H'|H']; [exact (Hs H') | exact (He H')]. }
  assert (HMR : aa_MR API L A mem' md).
  { destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    apply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
      apply (mbyte_munch segs W); [exact Hm | lia | apply HO; [lia | left; exact Ho]].
    - intros a Ho Hp. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho).
      apply (present_munch W mem); [exact Hm | lia | apply HO; [lia | left; exact Ho] | exact Hp].
    - intros p n i Hin Hi.
      destruct (rg_blk L A mem md (ptr_addr L p) n i HM (rg_blk_of L A p n Hin) Hi) as (Hp & H1 & H2 & _).
      apply (present_munch W mem); [exact Hm | lia | | exact Hp].
      apply HO; [lia|]. right. exists (ptr_addr L p), n. split; [apply rg_blk_of; exact Hin | lia].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HB|]. split; [tauto|].
  split; [intros a k Hin _ _; exact Hin|].
  split; [exists (m_vmmaps md); symmetry; apply kb_vm_id|].
  split.
  { intros a Ha Hs He. assert (Ha' : 0 <= a < 2 ^ 64) by lia. pose proof (Out a Ha' Hs He) as Ho.
    split; [exact (mbyte_munch segs W mem mem' a Hm Ha' Ho) | exact (writable_munch segs W mem mem' a Hm Ha' Ho)]. }
  split.
  { intros a Hi _ Hs He. pose proof (in_img_lt a Hi) as Ha. assert (Ha' : 0 <= a < 2 ^ 64) by lia.
    pose proof (Out a Ha' Hs He) as Ho.
    split; [exact (mbyte_munch segs W mem mem' a Hm Ha' Ho) | exact (writable_munch segs W mem mem' a Hm Ha' Ho)]. }
  split.
  { intros a k i Hin _ Hi _. destruct (rg_blk L A mem md a k i HM Hin Hi) as (_ & H1 & H2 & _).
    apply (mbyte_munch segs W); [exact Hm | lia |]. apply HO; [lia|]. right. exists a, k. split; [exact Hin | lia]. }
  intros a Ha. unfold writable_at. apply Hw. exact (HS a Ha).
Qed.

Lemma ledger_rstep : forall K S E g L A mem md L' A' mem' md' Lam peak cnt fail,
  MR L A mem md ->
  ledger B L A mem Lam peak cnt fail ->
  rstep B API K S E g L A mem md L' A' mem' md' ->
  (forall a, alloc_statics a -> ~ rwin B K S a /\ ~ E a) ->
  (forall a k, In (a, k) Lam -> ~ g (a - 16) /\ forall i, - 16 <= i < k -> ~ E (a + i)) ->
  ledger B L' A' mem' Lam peak cnt fail.
Proof using SEG AX FG.
  intros K S E g L A mem md L' A' mem' md' Lam peak cnt fail HM ((W1 & W2 & W3 & W4) & R1 & R2 & R3 & ND & FB)
    (M & Wf & Bd & Hd & Kb & Dm & F & G & U & Sw) HS HL.
  assert (St : forall a v, word_mem segs mem a v -> (forall k, 0 <= k < 8 -> alloc_statics (a + k)) ->
                 word_mem segs mem' a v).
  { intros a v Hw Ha. apply (word_mem_frame segs mem); [exact Hw|]. intros k Hk.
    destruct (statics_img (a + k) (Ha k Hk)) as [Hi Hn]. destruct (HS (a + k) (Ha k Hk)) as [Hr He].
    exact (proj1 (G (a + k) Hi Hn Hr He)). }
  split.
  { split; [apply St; [exact W1 | intros k Hk; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia]|].
    split; [apply St; [exact W2 | intros k Hk; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia]|].
    split; [apply St; [exact W3 | intros k Hk; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia]|].
    apply St; [exact W4 | intros k Hk; unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia]. }
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact ND|].
  rewrite Forall_forall in FB |- *. intros [a k] Hin. specialize (FB _ Hin). cbn [fst snd] in FB |- *.
  destruct FB as (Hk & Hb & Hw & Hi). destruct (HL a k Hin) as [Hg HE].
  split; [exact Hk|]. split; [apply Kb; [exact Hb | lia | exact Hg]|]. split; [|exact Hi].
  apply (word_mem_frame segs mem); [exact Hw|]. intros j Hj.
  apply (U (a - 16) (k + 16) j Hb Hg); [lia|].
  replace (a - 16 + j) with (a + (j - 16)) by lia. apply HE. lia.
Qed.

Lemma rg_bytes : forall m m' a bs, Mem.bytes_at segs m a bs ->
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> Mem.mrd segs m' x = Mem.mrd segs m x) ->
  Mem.bytes_at segs m' a bs.
Proof using SEG AX FG.
  intros m m' a bs (Ha & Hl & H) Ex. split; [lia|]. split; [lia|].
  intros i Hi. rewrite Ex; [exact (H i Hi)|]. rewrite Mem.wa_unsigned by lia. lia.
Qed.

Lemma rg_stk : forall m m' lo hi, Frame.stk segs m lo hi ->
  (forall x : word, lo <= bv_unsigned x < hi ->
     Mem.mrd segs m' x = Mem.mrd segs m x /\ (wview segs m x <> None -> wview segs m' x <> None)) ->
  Frame.stk segs m' lo hi.
Proof using SEG AX FG.
  intros m m' lo hi (H1 & H2 & H) Ex. split; [lia|]. split; [lia|].
  intros a Ha. destruct (Ex (Mem.wa a)) as [E1 E2]; [rewrite Mem.wa_unsigned by lia; lia|].
  destruct (H a Ha) as [Wv [b R]]. split; [exact (E2 Wv)|]. exists b. exact (eq_trans E1 R).
Qed.

Lemma rg_u64 : forall m m' a v, pj_u64 segs m a v ->
  (forall x : word, a <= bv_unsigned x < a + 8 -> Mem.mrd segs m' x = Mem.mrd segs m x) -> pj_u64 segs m' a v.
Proof using SEG AX FG.
  intros m m' a v (Hv & Hb) Ex. split; [exact Hv|]. apply (rg_bytes m m'); [exact Hb|].
  intros x Hx. apply Ex. rewrite Mem.length_le8 in Hx. lia.
Qed.

Lemma rg_hdr : forall m m' p ty num str kids keys n cap,
  pj_hdr segs m p ty num str kids keys n cap ->
  (forall x : word, p <= bv_unsigned x < p + 56 ->
     Mem.mrd segs m' x = Mem.mrd segs m x /\ (wview segs m x <> None -> wview segs m' x <> None)) ->
  pj_hdr segs m' p ty num str kids keys n cap.
Proof using SEG AX FG.
  intros m m' p ty num str kids keys n cap
    ((Ha & Hs) & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)) Ex.
  assert (Fb : forall a bs, Mem.bytes_at segs m a bs -> p <= a -> a + Z.of_nat (length bs) <= p + 56 ->
                 Mem.bytes_at segs m' a bs).
  { intros a bs Bs Hpa Hab. apply (rg_bytes m m'); [exact Bs|]. intros x Hx. exact (proj1 (Ex x ltac:(lia))). }
  split; [split; [exact Ha | exact (rg_stk m m' p (p + 56) Hs Ex)]|].
  split; [split; [exact T0 | apply Fb; [exact T1 | lia | rewrite Mem.length_le4; lia]]|].
  split; [split; [exact N0 | apply Fb; [exact N1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact S0 | apply Fb; [exact S1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact K0 | apply Fb; [exact K1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact Y0 | apply Fb; [exact Y1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [split; [exact C0 | apply Fb; [exact C1 | lia | rewrite Mem.length_le8; lia]]|].
  split; [exact P0 | apply Fb; [exact P1 | lia | rewrite Mem.length_le8; lia]].
Qed.

Lemma rg_cstr : forall m lblk m' lblk' a k s,
  pj_cstr segs m lblk a k s -> (lblk a k -> lblk' a k) ->
  (forall x : word, pj_holds (a, k) (bv_unsigned x) -> Mem.mrd segs m' x = Mem.mrd segs m x) ->
  pj_cstr segs m' lblk' a k s.
Proof using SEG AX FG.
  intros m lblk m' lblk' a k s (Hl & Hk & Hf & Hb) Hl' Ex.
  split; [exact (Hl' Hl)|]. split; [exact Hk|]. split; [exact Hf|].
  apply (rg_bytes m m'); [exact Hb|]. intros x Hx. apply Ex. unfold pj_holds; cbn [fst snd].
  rewrite length_map, length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma rg_node_frame : forall t m lblk m' lblk' p D,
  pj_node segs m lblk p t D ->
  (forall a k, In (a, k) D -> lblk a k -> lblk' a k) ->
  (forall x : word, pj_foot p D (bv_unsigned x) ->
     Mem.mrd segs m' x = Mem.mrd segs m x /\ (wview segs m x <> None -> wview segs m' x <> None)) ->
  pj_node segs m' lblk' p t D.
Proof using SEG AX FG.
  intros t. induction t as [| | | txt bits | s | items IH | members IH] using jv_ind';
    intros m lblk m' lblk' p D H HL HM; cbn [pj_node] in H |- *;
    destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
    (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap;
    (split; [apply (rg_hdr m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]).
  - exact Hb.
  - exact Hb.
  - exact Hb.
  - destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (rg_cstr m lblk m' lblk'); [exact Hc | intros Hl; apply HL; [subst D; left; reflexivity | exact Hl] |].
    intros x Hx. refine (proj1 (HM x _)). right. exists (str, k). split; [subst D; left; reflexivity | exact Hx].
  - destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
    split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
    exists k. split; [|exact ED].
    apply (rg_cstr m lblk m' lblk'); [exact Hc | intros Hl; apply HL; [subst D; left; reflexivity | exact Hl] |].
    intros x Hx. refine (proj1 (HM x _)). right. exists (str, k). split; [subst D; left; reflexivity | exact Hx].
  - destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left; reflexivity. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    split; [destruct Hcap as [Hcap|(Hp & L0)];
            [left; exact Hcap | right; split; [exact Hp | apply HL; [apply (Hin Hp) | exact L0]]]|].
    exists Di. split; [exact ED|].
    apply (pj_items_mono (pj_node segs m lblk) (pj_node segs m' lblk')); [|exact Hi].
    intros i u D1 Hil Hu Hinc HP.
    assert (Hp : 0 < cap) by lia.
    rewrite Forall_forall in IH.
    apply (IH u Hu m lblk m' lblk' _ D1 HP).
    + intros a k Hak Hl. apply HL; [apply HDi; apply Hinc; exact Hak | exact Hl].
    + intros x Hx. apply HM. destruct Hx as [Hx|(b & Hb & Hx)].
      * right. exists (kids, 56 * cap). split; [apply (Hin Hp) | unfold pj_holds; cbn [fst snd]; lia].
      * right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hx].
  - destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
    split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
    assert (Hin : 0 < cap -> In (kids, 56 * cap) D /\ In (keys, 8 * cap) D).
    { intros Hp. subst D. rewrite (proj2 (Z.eqb_neq cap 0)) by lia.
      split; [left; reflexivity | right; left; reflexivity]. }
    assert (HDi : forall b, In b Di -> In b D) by (intros b Hb; subst D; apply in_or_app; right; exact Hb).
    split; [destruct Hcap as [Hcap|(Hp & L0 & L1)];
            [left; exact Hcap | right; split; [exact Hp|];
             split; [apply HL; [apply (proj1 (Hin Hp)) | exact L0] | apply HL; [apply (proj2 (Hin Hp)) | exact L1]]]|].
    exists Di. split; [exact ED|].
    apply (pj_mems_mono segs m lblk m' lblk' (pj_node segs m lblk) (pj_node segs m' lblk')); [|exact Hi].
    intros i nm u x k D1 Hil Hu Hxk Hinc Hx Hcs HP.
    assert (Hp : 0 < cap) by lia.
    split; [|split].
    + apply (rg_u64 m m'); [exact Hx|]. intros y Hy. refine (proj1 (HM y _)). right. exists (keys, 8 * cap).
      split; [apply (proj2 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
    + apply (rg_cstr m lblk m' lblk'); [exact Hcs | intros Hl; apply HL; [apply HDi; exact Hxk | exact Hl] |].
      intros y Hy. refine (proj1 (HM y _)). right. exists (x, k). split; [apply HDi; exact Hxk | exact Hy].
    + rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
      apply (IH m lblk m' lblk' _ D1 HP).
      * intros a k' Hak Hl. apply HL; [apply HDi; apply Hinc; exact Hak | exact Hl].
      * intros y Hy. apply HM. destruct Hy as [Hy|(b & Hb & Hy)].
        -- right. exists (kids, 56 * cap). split; [apply (proj1 (Hin Hp)) | unfold pj_holds; cbn [fst snd]; lia].
        -- right. exists b. split; [apply HDi; apply Hinc; exact Hb | exact Hy].
Qed.

Lemma pj_node_rstep : forall K S E g L A mem md L' A' mem' md' Lam Lam' peak cnt fail p t D,
  MR L A mem md -> ledger B L A mem Lam peak cnt fail ->
  pj_node segs mem (lin Lam) p t D -> (forall bk, In bk D -> In bk Lam) ->
  rstep B API K S E g L A mem md L' A' mem' md' ->
  alloc_ceiling <= p -> p + 56 <= 2 ^ 64 ->
  (forall i, 0 <= i < 56 -> ~ rwin B K S (p + i) /\ ~ E (p + i)) ->
  (forall a k, In (a, k) D -> ~ g (a - 16) /\ forall i, 0 <= i < k -> ~ E (a + i)) ->
  (forall bk, In bk Lam -> In bk Lam') ->
  pj_node segs mem' (lin Lam') p t D.
Proof using SEG AX FG.
  intros K S E g L A mem md L' A' mem' md' Lam Lam' peak cnt fail p t D HM HL HP HD
    (M & Wf & Bd & Hd & Kb & Dm & F & G & U & Sw) Hp1 Hp2 HS HE HLL.
  apply (rg_node_frame t mem (lin Lam) mem' (lin Lam') p D HP).
  - intros a k _ Hl. apply HLL. exact Hl.
  - intros x Hx. pose proof (rg_word x) as Rx. destruct Hx as [Hx|(b & Hb & Hx)].
    + destruct (HS (bv_unsigned x - p) ltac:(lia)) as [Hr He].
      replace (p + (bv_unsigned x - p)) with (bv_unsigned x) in Hr, He by lia.
      destruct (F (bv_unsigned x) ltac:(lia) Hr He) as [E1 E2].
      apply rg_conv; [exact E1 | exact (proj1 E2)].
    + destruct b as [a k]. unfold pj_holds in Hx. cbn [fst snd] in Hx.
      destruct (HE a k Hb) as [Hg Hn].
      destruct HL as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
      destruct (FB (a, k) (HD _ Hb)) as (Hk & Hblk & _ & _). cbn [fst snd] in Hk, Hblk.
      pose proof (Kb (a - 16) (k + 16) Hblk ltac:(lia) Hg) as Hblk'.
      pose proof (Hn (bv_unsigned x - a) ltac:(lia)) as Hn'.
      replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hn' by lia.
      pose proof (U (a - 16) (k + 16) (bv_unsigned x - a + 16) Hblk Hg ltac:(lia)) as Ub.
      replace (a - 16 + (bv_unsigned x - a + 16)) with (bv_unsigned x) in Ub by lia.
      apply rg_conv; [exact (Ub Hn')|]. intros _.
      destruct (rg_blk L' A' mem' md' (a - 16) (k + 16) (bv_unsigned x - a + 16) M Hblk' ltac:(lia)) as (Pr & _).
      replace (a - 16 + (bv_unsigned x - a + 16)) with (bv_unsigned x) in Pr by lia.
      exact (present_writable B mem' (bv_unsigned x) Pr).
Qed.

Lemma pj_node_mrd : forall t m m' (lb : Z -> Z -> Prop) p D,
  pj_node segs m lb p t D ->
  (forall x : word, pj_foot p D (bv_unsigned x) ->
     Mem.mrd segs m' x = Mem.mrd segs m x /\ (wview segs m x <> None -> wview segs m' x <> None)) ->
  pj_node segs m' lb p t D.
Proof using SEG AX FG.
  intros t m m' lb p D H HM. exact (rg_node_frame t m lb m' lb p D H (fun a k _ h => h) HM).
Qed.

Lemma pj_node_normalize : forall m (lb : Z -> Z -> Prop) p t D,
  ro_agree segs m -> pj_node segs m lb p t D ->
  (forall x, pj_foot p D x -> Mem.ro_addr segs (Z_to_bv 64 x) = false) ->
  pj_node segs (normalize segs m) lb p t D.
Proof using SEG AX FG.
  intros m lb p t D HA H Hro. apply (pj_node_mrd t m (normalize segs m) lb p D H).
  intros x Hx. pose proof (mem_rel_normalize segs m HA) as HR.
  assert (Er : Mem.ro_addr segs x = false) by (rewrite <- (Z_to_bv_bv_unsigned _ x); apply Hro; exact Hx).
  split; [exact (eq_sym (mrd_rel segs m (normalize segs m) x HR))|].
  intros Wv. rewrite (wview_rel_rw segs m (normalize segs m) x HR Er). exact Wv.
Qed.

Lemma pj_node_unnormalize : forall m m0 (lb : Z -> Z -> Prop) p t D,
  mem_rel segs m m0 -> pj_node segs m0 lb p t D -> pj_node segs m lb p t D.
Proof using SEG AX FG.
  intros m m0 lb p t D HR H. apply (pj_node_mrd t m0 m lb p D H).
  intros x _. split; [exact (mrd_rel segs m m0 x HR)|].
  intros Wv. rewrite <- (wview_rel_rw segs m m0 x HR (ro_false_of_wview segs m m0 x HR Wv)). exact Wv.
Qed.

Lemma rd_cells_of_MR : forall L A mem md, MR L A mem md -> ro_agree segs mem -> rd_cells B mem.
Proof using SEG AX FG.
  intros L A mem md HM HR. destruct (ax_statics AX L A mem md HM) as (Hg & (g & _ & Hw) & _).
  split; [exact HR|]. split; [exact Hg|]. exists g. exact Hw.
Qed.

Lemma call_pre_k_mid : forall K0 L0 A0 regs0 mem0 md0 E L A mem md regs Kc f,
  call_pre_k B MR K0 L0 A0 regs0 mem0 md0 ->
  rstep B API K0 (spZ regs0) E (fun _ => False) L0 A0 mem0 md0 L A mem md ->
  st_init_done A = true ->
  spZ regs = spZ regs0 - f -> spZ regs mod 16 = 0 -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs 1) ->
  0 <= f -> 0 <= Kc -> f + Kc <= K0 ->
  call_pre_k B MR Kc L A regs mem md.
Proof using SEG AX FG.
  intros K0 L0 A0 regs0 mem0 md0 E L A mem md regs Kc f (_ & _ & _ & _ & _ & Hlo & Hhi & _ & Htp & _ & _)
    (M & Wf & Bd & _ & _ & _ & _ & _ & _ & Sw) Hd Hsp Hal Htp1 Hra Hf HKc HfK.
  split; [exact M|]. split; [exact Wf|]. split; [exact Bd|]. split; [exact Hra|]. split; [exact Hal|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply Sw; unfold rwin; left; lia|].
  split; [rewrite Htp1; exact Htp|].
  split; [intros a Ha; apply Sw; unfold rwin; right; exact Ha|].
  intros Hn. rewrite Hd in Hn. discriminate.
Qed.

Lemma reader_env_mid : forall K0 L0 A0 regs0 mem0 md0 E L A mem md regs Kc f,
  reader_env B API K0 L0 A0 regs0 mem0 md0 ->
  rstep B API K0 (spZ regs0) E (fun _ => False) L0 A0 mem0 md0 L A mem md ->
  st_init_done A = true -> rd_cells B mem -> frm_zero fp_csr ->
  spZ regs = spZ regs0 - f -> spZ regs mod 16 = 0 -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs 1) ->
  0 <= f -> 0 <= Kc -> f + Kc <= K0 ->
  reader_env B API Kc L A regs mem md.
Proof using SEG AX FG.
  intros K0 L0 A0 regs0 mem0 md0 E L A mem md regs Kc f (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)
    HR Hd Hc Hz Hsp Hal Htp Hra Hf HKc HfK.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact (call_pre_k_mid K0 L0 A0 regs0 mem0 md0 E L A mem md regs Kc f H6 HR Hd Hsp Hal Htp Hra Hf HKc HfK)|].
  split; [lia|]. split; [lia|]. split; [exact Hz | exact Hc].
Qed.

Lemma rtt_rel_of_rstep : forall K L A regs mem md E L' A' regs' mem' md',
  rstep B API K (spZ regs) E (fun _ => False) L A mem md L' A' mem' md' -> regs_preserved regs regs' ->
  (forall a k, In (a, k) (blocks L A) -> k <= 0 -> In (a, k) (blocks L' A')) ->
  rtt_rel B API K regs E L A mem md L' A' regs' mem' md'.
Proof using SEG AX FG.
  intros K L A regs mem md E L' A' regs' mem' md' (M & W & Bd & Hd & Kb & D & F & G & U & Sw) HR HZ.
  split; [exact M|]. split; [exact W|]. split; [exact Bd|]. split; [exact Hd|].
  split; [intros a k Hin; destruct (Z_lt_le_dec 0 k) as [Hk|Hk]; [exact (Kb a k Hin Hk (fun h => h)) | exact (HZ a k Hin Hk)]|].
  split; [exact HR|]. split; [exact D|]. split; [exact F|]. split; [exact G|].
  split; [intros a k i Hin Hi He; exact (U a k i Hin (fun h => h) Hi He)|].
  exact Sw.
Qed.

Lemma blocks_same_addr : forall L A mem md a k1 k2,
  MR L A mem md -> In (a, k1) (blocks L A) -> In (a, k2) (blocks L A) -> 0 < k1 -> 0 < k2 -> k1 = k2.
Proof using SEG AX FG.
  intros L A mem md a k1 k2 HM H1 H2 Hk1 Hk2. destruct (Z.eq_dec k1 k2) as [Ek|Nk]; [exact Ek|]. exfalso.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as Hp.
  destruct (rg_pairwise_in YO0f.ranges_disjoint (blocks L A) (a, k1) (a, k2) Hp H1 H2
              ltac:(intros Q; apply Nk; congruence)) as [Q|Q];
    unfold YO0f.ranges_disjoint in Q; cbn [fst snd] in Q; lia.
Qed.

Lemma blocks_apart : forall L A mem md a k b n x,
  MR L A mem md -> In (a, k) (blocks L A) -> In (b, n) (blocks L A) -> a <> b ->
  a <= x < a + k -> ~ (b <= x < b + n).
Proof using SEG AX FG.
  intros L A mem md a k b n x HM H1 H2 Hab Hx Hy.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) as Hp.
  destruct (rg_pairwise_in YO0f.ranges_disjoint (blocks L A) (a, k) (b, n) Hp H1 H2
              ltac:(intros Q; apply Hab; congruence)) as [Q|Q];
    unfold YO0f.ranges_disjoint in Q; cbn [fst snd] in Q; lia.
Qed.

End G.
