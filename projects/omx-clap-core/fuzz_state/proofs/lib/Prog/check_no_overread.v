From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import memcpy_c memset_c bcmp_c past_nul_c past_nul.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import check_no_overread_blocks check_no_overread_cmp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import MemNorm.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL01 YI04 YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger LedgerFacts KindBGlue HState HStateRoom
  WriterSpec fuzz_free_c preset_base64_decode_c check_no_overread_c check_reject_clean_starved.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpecFacts HsKindB.
Import ListNotations.
Local Open Scope Z_scope.

Definition xin (E : list (Z * Z)) (y : Z * Z) : bool :=
  existsb (fun e => (fst e =? fst y) && (snd e =? snd y)) E.

Lemma xin_iff : forall E y, xin E y = true <-> In y E.
Proof.
  intros E [a k]. unfold xin. rewrite existsb_exists. split.
  - intros ([a' k'] & Hin & H). cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
    apply Z.eqb_eq in H1, H2. subst. exact Hin.
  - intros H. exists (a, k). split; [exact H|]. cbn. rewrite !Z.eqb_refl. reflexivity.
Qed.

Lemma xin_false : forall E y, ~ In y E -> xin E y = false.
Proof. intros E y H. destruct (xin E y) eqn:X; [exfalso; apply H; apply xin_iff; exact X | reflexivity]. Qed.

Definition BK (base E cur : list (Z * Z)) : Prop :=
  List.filter (fun y => negb (xin E y)) cur = base /\ incl E cur /\ List.NoDup E.

Lemma bk_base : forall base E cur y, BK base E cur -> In y base -> In y cur /\ ~ In y E.
Proof.
  intros base E cur y (HF & _ & _) Hy. rewrite <- HF in Hy. apply filter_In in Hy as [H1 H2].
  split; [exact H1|]. intros HE. apply xin_iff in HE. rewrite HE in H2. discriminate.
Qed.

Lemma bk_ins : forall base E c1 c2 x, BK base E (c1 ++ c2) -> ~ In x (c1 ++ c2) -> BK base (x :: E) (c1 ++ x :: c2).
Proof.
  intros base E c1 c2 x (HF & HI & HN) Hx. split; [|split].
  - rewrite filter_app. cbn [List.filter]. unfold xin at 2. cbn [existsb]. rewrite !Z.eqb_refl. cbn [andb orb negb].
    rewrite <- filter_app. rewrite <- HF. apply filter_ext_in. intros y Hy.
    unfold xin at 1. cbn [existsb]. fold (xin E y).
    destruct ((fst x =? fst y) && (snd x =? snd y)) eqn:Q; [|reflexivity].
    exfalso. apply andb_prop in Q as [Q1 Q2]. apply Z.eqb_eq in Q1, Q2. apply Hx.
    destruct x, y. cbn in Q1, Q2. subst. exact Hy.
  - intros y [<-|Hy]; [apply in_or_app; right; left; reflexivity|].
    apply HI in Hy. apply in_app_or in Hy as [Hy|Hy]; apply in_or_app; [left; exact Hy | right; right; exact Hy].
  - constructor; [|exact HN]. intros H. exact (Hx (HI x H)).
Qed.

Lemma bk_rem : forall base e1 e2 d1 d2 x, BK base (e1 ++ x :: e2) (d1 ++ x :: d2) -> ~ In x (d1 ++ d2) ->
  BK base (e1 ++ e2) (d1 ++ d2).
Proof.
  intros base e1 e2 d1 d2 x (HF & HI & HN) Hx.
  assert (Xx : xin (e1 ++ x :: e2) x = true) by (apply xin_iff; apply in_or_app; right; left; reflexivity).
  split; [|split].
  - rewrite <- HF. symmetry. rewrite filter_app. cbn [List.filter]. rewrite Xx. cbn [negb]. rewrite <- filter_app.
    apply filter_ext_in. intros y Hy. f_equal. symmetry.
    destruct (xin (e1 ++ e2) y) eqn:X1; destruct (xin (e1 ++ x :: e2) y) eqn:X2; try reflexivity.
    + exfalso. apply xin_iff in X1. apply Bool.not_true_iff_false in X2. apply X2. apply xin_iff.
      apply in_app_or in X1 as [X1|X1]; apply in_or_app; [left; exact X1 | right; right; exact X1].
    + exfalso. apply xin_iff in X2. apply Bool.not_true_iff_false in X1. apply X1. apply xin_iff.
      apply in_app_or in X2 as [X2|[<-|X2]]; [apply in_or_app; left; exact X2 | exfalso; exact (Hx Hy) |
        apply in_or_app; right; exact X2].
  - intros y Hy. assert (Hy' : In y (e1 ++ x :: e2)).
    { apply in_app_or in Hy as [Hy|Hy]; apply in_or_app; [left; exact Hy | right; right; exact Hy]. }
    pose proof (HI y Hy') as H. apply in_app_or in H as [H|[<-|H]]; [apply in_or_app; left; exact H | |
      apply in_or_app; right; exact H].
    exfalso. exact (NoDup_remove_2 _ _ _ HN Hy).
  - exact (NoDup_remove_1 _ _ _ HN).
Qed.

Lemma bk_nil : forall cur, BK cur [] cur.
Proof.
  intros cur. split; [|split; [intros y [] | constructor]].
  induction cur as [|y cur IH]; [reflexivity|]. cbn [List.filter]. change (negb (xin [] y)) with true. cbv iota.
  rewrite IH. reflexivity.
Qed.

Lemma bk_final : forall base cur, BK base [] cur -> cur = base.
Proof.
  intros base cur (HF & _ & _). rewrite <- HF. clear HF.
  induction cur as [|y cur IH]; [reflexivity|]. cbn [List.filter]. change (negb (xin [] y)) with true. cbv iota.
  rewrite <- IH. reflexivity.
Qed.

Lemma pw_two : forall {X : Type} (R : X -> X -> Prop) l x y, pairwise R l -> In x l -> In y l -> x <> y ->
  R x y \/ R y x.
Proof.
  intros X R l. induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|].
  destruct H as [Hz H]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso. exact (Hne eq_refl).
  - left. exact (Hz y Hy).
  - right. exact (Hz x Hx).
  - exact (IH x y H Hx Hy Hne).
Qed.

Lemma pw_notin : forall c1 c2 x, pairwise ranges_disjoint (c1 ++ x :: c2) -> 0 < snd x -> ~ In x (c1 ++ c2).
Proof.
  intros c1 c2 x H Hk Hin. destruct (pn_pairwise_mid _ _ _ _ _ H Hin) as [D|D]; unfold ranges_disjoint in D; lia.
Qed.

Lemma lam_rm : forall (L0 l1 l2 pre post : list (Z * Z)) q k, List.NoDup (map fst L0) ->
  L0 = l1 ++ (q, k) :: l2 -> L0 = pre ++ (q, k) :: post -> l1 ++ l2 = pre ++ post.
Proof.
  intros L0 l1. revert L0. induction l1 as [|x l1 IH]; intros L0 l2 pre post q k ND E1 E2;
    rewrite E1 in ND, E2; clear E1 L0; destruct pre as [|y pre]; cbn [app map] in *.
  - injection E2 as E2. exact E2.
  - injection E2 as Ey E2. subst y. exfalso. apply NoDup_cons_iff in ND as [Hn _]. cbn [fst] in Hn.
    apply Hn. rewrite E2, map_app. apply in_or_app. right. left. reflexivity.
  - injection E2 as Ex E2. subst x. exfalso. apply NoDup_cons_iff in ND as [Hn _]. cbn [fst] in Hn.
    apply Hn. rewrite map_app. apply in_or_app. right. left. reflexivity.
  - injection E2 as Ex E2. subst y. f_equal. apply NoDup_cons_iff in ND as [_ ND'].
    exact (IH (l1 ++ (q, k) :: l2) l2 pre post q k ND' eq_refl E2).
Qed.

Lemma six_len : forall six, (length (six_bytes six) * 4 <= length six * 3)%nat.
Proof.
  fix IH 1. intros [|a [|b [|c [|e r]]]]; cbn [six_bytes length]; try lia.
  specialize (IH r). lia.
Qed.

Lemma dec_len : forall tb bs, b64_dec tb = Some bs -> (length bs * 4 <= length tb * 3)%nat.
Proof.
  intros tb bs H. unfold b64_dec in H.
  destruct (b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
  destruct ((pad <=? 2) && six_tail_ok six); [|discriminate]. injection H as <-.
  destruct (WriterSpecFacts.scan_inv tb 0 [] six pad E) as [H1 _]. cbn [length] in H1.
  pose proof (six_len six). lia.
Qed.

Lemma fst_uniq : forall {X Y : Type} (l : list (X * Y)) x a c,
  List.NoDup (map fst l) -> In (x, a) l -> In (x, c) l -> a = c.
Proof.
  intros X Y l. induction l as [|[y e] l IH]; intros x a c ND Ha Hc; [destruct Ha|].
  cbn [map fst] in ND. inversion ND as [|? ? Hn ND']; subst.
  destruct Ha as [Ea|Ha]; destruct Hc as [Ec|Hc].
  - inversion Ea; inversion Ec; subst; reflexivity.
  - inversion Ea; subst. exfalso. apply Hn. apply (in_map fst) in Hc. exact Hc.
  - inversion Ec; subst. exfalso. apply Hn. apply (in_map fst) in Ha. exact Ha.
  - exact (IH x a c ND' Ha Hc).
Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma kb_mid_W : forall K sp L A mem md (E E' : Z -> Prop) L' A' mem' md',
  kb_mid B API K sp L A mem md E L' A' mem' md' ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (sp - K <= a < sp) -> E a -> E' a) ->
  kb_mid B API K sp L A mem md E' L' A' mem' md'.
Proof.
  intros K sp L A mem md E E' L' A' mem' md' (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) HE.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H7|]. split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho Ho' Hs He'. apply H8; [exact Ha | exact Ho | exact Ho' | exact Hs |].
  intros He. apply He'. apply HE; [exact Ha | intros Hx; apply Hs; left; exact Hx | exact He].
Qed.

Lemma ub_conv : forall Lc Ac A' g base, ublocks_kept Lc Ac A' g -> ~ In g base ->
  forall q k, In (q, k) (user_blocks Ac) -> In (ptr_addr Lc q, k) base -> In (q, k) (user_blocks A').
Proof. intros Lc Ac A' g base UB Hg q k Hq Hb. apply (UB q k Hq). intros E. apply Hg. rewrite <- E. exact Hb. Qed.

Lemma ub_free : forall Lc Ac A' p n, WF Ac -> In (p, n) (user_blocks Ac) ->
  (forall q k, In (q, k) (user_blocks Ac) -> q <> p -> In (q, k) (user_blocks A')) ->
  ublocks_kept Lc Ac A' (ptr_addr Lc p, n).
Proof.
  intros Lc Ac A' p n HW Hp H q k Hq Hne. apply (H q k Hq). intros ->. apply Hne.
  pose proof (YO10.user_block_ptrs_NoDup Ac HW) as ND.
  rewrite (fst_uniq _ p k n ND Hq Hp). reflexivity.
Qed.

Lemma kp_conv : forall Lc Ac mem mem' md g base E, keeps B Lc Ac mem mem' g -> MR Lc Ac mem md ->
  BK base E (blocks Lc Ac) -> (g = 0 \/ exists kx, In (g, kx) E /\ 0 < kx) ->
  forall a k i, In (a, k) base -> 0 <= i < k -> mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i).
Proof.
  intros Lc Ac mem mem' md g base E KP HM HB Hg a k i Hin Hi.
  destruct (bk_base _ _ _ _ HB Hin) as [Hc HnE].
  destruct (Z.eq_dec a g) as [->|Hne]; [|exact (KP a k i Hc Hne Hi)].
  exfalso. destruct Hg as [-> | (kx & Hx & Hkx)].
  - pose proof (HsKindB.block_low B API Lc Ac mem md 0 k 0 HM Hc ltac:(lia)). lia.
  - destruct HB as (_ & HI & _). pose proof (HI _ Hx) as Hxc.
    assert (Hne : (g, k) <> (g, kx)) by (intros E'; apply HnE; rewrite E'; exact Hx).
    destruct (pw_two _ _ _ _ (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM) Hc Hxc Hne) as [D|D];
      unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
Qed.

Lemma led_post : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] ->
  forall Kc Lc Ac Rc memc mdc Ec L' A' R' mem' md' Lam p c f,
  ledger B Lc Ac memc Lam p c f -> MR Lc Ac memc mdc ->
  call_post_k B MR Kc Lc Ac Rc memc mdc Ec L' A' R' mem' md' -> alloc_ceiling + Kc <= spZ Rc ->
  (forall x, alloc_statics x -> ~ Ec x) ->
  (forall a k, In (a, k) Lam -> In (a - 16, k + 16) (blocks L' A')) ->
  (forall a k j, In (a, k) Lam -> 0 <= j < 8 -> mbyte (ms_segs B) mem' (a - 16 + j) = mbyte (ms_segs B) memc (a - 16 + j)) ->
  ledger B L' A' mem' Lam p c f.
Proof.
  intros GF Kc Lc Ac Rc memc mdc Ec L' A' R' mem' md' Lam p c f LG HM CP HK HS HB HH.
  pose proof CP as (HM' & _ & _ & _ & _ & _ & _ & HF & _).
  apply (ledger_frame B Lc Ac L' A' memc mem' Lam p c f LG HB).
  intros x [Hx | (a & k & Hin & Hx)].
  - assert (Hg : in_globals [(G_FAIL, 8); (G_LIVE, 24)] x).
    { unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. unfold in_globals, G_LIVE, G_FAIL.
      destruct Hx as [Hx|[Hx|[Hx|Hx]]];
        [exists 0x33450, 24 | exists 0x33450, 24 | exists 0x33450, 24 | exists 0x231e0, 8];
        (split; [cbn; tauto | lia]). }
    destruct (GF x Hg) as (Hi & Hr & _ & He & Ho).
    destruct (Ho _ _ _ _ HM) as [Hn _]. destruct (Ho _ _ _ _ HM') as [Hn' _].
    apply (proj1 (HF x (or_intror Hi) Hn Hn' ltac:(unfold scratch_k; lia) (HS x Hx))).
  - replace x with (a - 16 + (x - (a - 16))) by lia. apply (HH a k); [exact Hin | lia].
Qed.

Lemma cs_saved : forall R1 R2 k, regs_preserved R1 R2 -> (k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ 18 <= k <= 27) ->
  getr R2 (Z_to_bv 5 k) = getr R1 (Z_to_bv 5 k).
Proof. intros R1 R2 k H Hk. apply H. unfold callee_saved. lia. Qed.

End S.

Definition cno_cells (regs : bvmap 5 word) : list cell :=
  [C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
   C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)].

Ltac cno_k k :=
  let H := fresh in
  assert (H : k = 3 \/ k = 4 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia;
  destruct H as [->|[->|[->|[->|[->|[->| ->]]]]]].

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GF : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)].
Hypothesis AX : YL01.AllocExtra B MR.
Hypothesis CO : ctx_owned B API.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (Lam : list (Z * Z)) (peak cnt : Z).
Hypothesis PRE : call_pre_k B MR CNO_STK L A regs mem md.
Hypothesis LG0 : ledger B L A mem Lam peak cnt (2 ^ 64 - 1).

(* The state at a call or return point of check_no_overread, relative to its entry state: E lists the blocks the
   function has allocated and not yet freed, Lamc the ledger's live list. *)
Definition CI (E : list (Z * Z)) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
    (Lamc : list (Z * Z)) (peakc cntc : Z) : Prop :=
  kb_mid B API CNO_STK (spZ regs) L A mem md alloc_statics Lc Ac memc mdc /\
  ro_agree rsegs memc /\ guard_kept B mem memc /\
  (length (st_regions A) <= length (st_regions Ac))%nat /\
  ublocks_kept L A Ac (0, 0) /\
  BK (blocks L A) E (blocks Lc Ac) /\
  Forall (fun e => forall i, 0 <= i < snd e -> ~ in_img B (fst e + i)) E /\
  ledger B Lc Ac memc Lamc peakc cntc (2 ^ 64 - 1) /\ peak <= peakc /\
  Step.rw_cells rsegs memc (spZ regs - 64) (cno_cells regs).

(* The callee-saved registers inside the frame. *)
Definition RS (R : bvmap 5 word) (x8 x9 x18 x19 x20 x21 : word) : Prop :=
  getr R 2 = Z_to_bv 64 (spZ regs - 96) /\ getr R 8 = x8 /\ getr R 9 = x9 /\ getr R 18 = x18 /\
  getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\
  (forall k, k = 3 \/ k = 4 \/ 23 <= k <= 27 -> getr R (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)).

Lemma cno_IL : img_low B.
Proof.
  pose proof alloc_ceiling_val.
  apply (img_low_of_check B 0x55000); [unfold img_check; rewrite SEG; vm_compute; reflexivity | lia].
Qed.

Lemma cno_sp : alloc_ceiling + 9216 <= spZ regs /\ spZ regs < 2 ^ 63 /\ spZ regs mod 16 = 0.
Proof. pose proof PRE as (_ & _ & _ & _ & H16 & HAC & H63 & _). unfold CNO_STK, ALLOC_STACK in HAC. auto. Qed.

Lemma RS_pres : forall R R' x8 x9 x18 x19 x20 x21, regs_preserved R R' -> RS R x8 x9 x18 x19 x20 x21 ->
  RS R' x8 x9 x18 x19 x20 x21.
Proof.
  intros R R' x8 x9 x18 x19 x20 x21 HP (Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QG).
  split; [rewrite <- Q2; exact (HP 2 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- Q8; exact (HP 8 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- Q9; exact (HP 9 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- Q18; exact (HP 18 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- Q19; exact (HP 19 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- Q20; exact (HP 20 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- Q21; exact (HP 21 ltac:(unfold callee_saved; lia))|].
  intros k Hk. rewrite <- (QG k Hk). exact (HP k ltac:(unfold callee_saved; lia)).
Qed.

Lemma RS_mk : forall R0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  (forall k, k = 3 \/ k = 4 \/ 23 <= k <= 27 -> getr R0 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)) ->
  sp = Z_to_bv 64 (spZ regs - 96) -> gp = getr R0 3 -> tp = getr R0 4 -> s7 = getr R0 23 -> s8 = getr R0 24 ->
  s9 = getr R0 25 -> s10 = getr R0 26 -> s11 = getr R0 27 ->
  RS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
    s0 s1 s2 s3 s4 s5.
Proof.
  intros R0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    QG Esp Egp Etp E7 E8 E9 E10 E11.
  subst sp gp tp s7 s8 s9 s10 s11.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  intros k Hk. rewrite <- (QG k Hk). cno_k k; reflexivity.
Qed.

Lemma cno_base_pos : forall a k, In (a, k) (blocks L A) -> 4096 <= a.
Proof.
  intros a k Hin. pose proof PRE as (HM & _).
  destruct (HsKindB.in_blocks L A a k Hin) as (p & Hp & ->).
  exact (proj1 (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HM Hp)).
Qed.

Lemma cno_pre : forall E Lc Ac memc mdc Lamc peakc cntc regsc K,
  CI E Lc Ac memc mdc Lamc peakc cntc -> st_init_done Ac = true ->
  getr regsc 2 = Z_to_bv 64 (spZ regs - 96) -> getr regsc 4 = getr regs 4 -> YK0s.ret_ok (getr regsc 1) ->
  0 <= K -> K + 96 <= CNO_STK ->
  spZ regsc = spZ regs - 96 /\ call_pre_k B MR K Lc Ac regsc memc mdc.
Proof.
  intros E Lc Ac memc mdc Lamc peakc cntc regsc K (MID & _) INIT R2 R4 R1 HK HK2.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  pose proof MID as (HMc & HWFc & HBDc & _ & _ & _ & _ & _ & S).
  pose proof alloc_ceiling_val as Hacv.
  unfold CNO_STK, ALLOC_STACK in *.
  assert (SP : spZ regsc = spZ regs - 96).
  { unfold spZ at 1. rewrite R2, MState.unsigned_lit by lia. reflexivity. }
  split; [exact SP|].
  split; [exact HMc|]. split; [exact HWFc|]. split; [exact HBDc|]. split; [exact R1|].
  split; [rewrite SP; Z.div_mod_to_equations; lia|].
  split; [rewrite SP; lia|]. split; [rewrite SP; lia|].
  split; [intros a Ha; apply S; left; rewrite SP in Ha; lia|].
  split; [rewrite R4; exact HTP|].
  split; [intros a Ha; apply S; right; exact Ha|].
  intros Hf. rewrite INIT in Hf. discriminate.
Qed.

Lemma cno_ub_keep : forall Lc Ac memc mdc A',
  kb_mid B API CNO_STK (spZ regs) L A mem md alloc_statics Lc Ac memc mdc -> ublocks_kept L A Ac (0, 0) ->
  (forall q k, In (q, k) (user_blocks Ac) -> In (ptr_addr Lc q, k) (blocks L A) -> In (q, k) (user_blocks A')) ->
  ublocks_kept L A A' (0, 0).
Proof.
  intros Lc Ac memc mdc A' MID UB H q k Hq Hne.
  pose proof MID as (_ & _ & _ & _ & PA & _).
  pose proof (UB q k Hq Hne) as Hq'.
  apply (H q k Hq'). rewrite (PA q k Hq Hq'). unfold blocks. apply in_map_iff. exists (q, k).
  split; [reflexivity | exact Hq].
Qed.

Lemma cno_ub_gone : forall Lc Ac A' g, ublocks_kept Lc Ac A' g -> ~ In g (blocks L A) ->
  forall q k, In (q, k) (user_blocks Ac) -> In (ptr_addr Lc q, k) (blocks L A) -> In (q, k) (user_blocks A').
Proof. intros Lc Ac A' g UB Hg q k Hq Hb. apply (UB q k Hq). intros E. apply Hg. rewrite <- E. exact Hb. Qed.

Lemma cno_zero_notin : forall k, ~ In (0, k) (blocks L A).
Proof. intros k H. pose proof (cno_base_pos 0 k H). lia. Qed.

(* After a call from the frame: the accumulated kb_mid, the guard, the region count and the saved cells. *)
Lemma cno_seq : forall Lc Ac memc mdc regsc K E' L' A' regs' mem' md',
  kb_mid B API CNO_STK (spZ regs) L A mem md alloc_statics Lc Ac memc mdc ->
  (length (st_regions A) <= length (st_regions Ac))%nat -> ublocks_kept L A Ac (0, 0) ->
  guard_kept B mem memc -> Step.rw_cells rsegs memc (spZ regs - 64) (cno_cells regs) ->
  call_post_k B MR K Lc Ac regsc memc mdc E' L' A' regs' mem' md' ->
  spZ regsc = spZ regs - 96 -> 0 <= K -> K + 96 <= CNO_STK ->
  (length (st_regions Ac) <= length (st_regions A'))%nat -> guard_kept B memc mem' ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (spZ regs - CNO_STK <= a < spZ regs) -> E' a ->
     alloc_statics a) ->
  (forall a, spZ regs - CNO_STK <= a < spZ regs -> E' a -> spZ regs - 96 <= a /\ mbyte rsegs mem' a <> None) ->
  (forall a, spZ regs - 64 <= a < spZ regs -> ~ E' a) ->
  kb_mid B API CNO_STK (spZ regs) L A mem md alloc_statics L' A' mem' md' /\
  guard_kept B mem mem' /\ (length (st_regions A) <= length (st_regions A'))%nat /\
  Step.rw_cells rsegs mem' (spZ regs - 64) (cno_cells regs).
Proof.
  intros Lc Ac memc mdc regsc K E' L' A' regs' mem' md' MID LEN UB GK FR CP SP HK HK2 LEN' GK' HE HN HF.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  unfold CNO_STK, ALLOC_STACK in *.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP) as [MD _].
  pose proof MID as (HMc & _).
  pose proof CP as (HM' & _ & _ & _ & _ & _ & _ & HFR & _).
  assert (HI : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 96 - K <= a < spZ regs - 96) -> ~ E' a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) memc a /\
     (writable_at (ms_segs B) memc a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hn He. apply HFR.
    - left. exact Ha.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HMc Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
    - unfold scratch_k. rewrite SP. lia.
    - exact He. }
  split.
  { apply (kb_mid_W B API _ _ _ _ _ _ (fun a => alloc_statics a \/ E' a)).
    - apply (check_reject_clean_starved.crs_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID MD).
      + rewrite SP. lia.
      + rewrite SP. lia.
      + lia.
      + exact LEN.
      + intros p n Hp _. apply (UB p n Hp). intros Ex. injection Ex as E1 _.
        pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp). lia.
      + intros a Ha Ho _.
        exact (check_reject_clean_starved.crs_own_mid B API AX CO L A mem md Lc Ac memc mdc a HM HMc Ha Ho).
      + intros a Ha Hn Her Hw. rewrite SP in Hn.
        rewrite SEG in Hw |- *.
        apply (proj2 (check_reject_clean_starved.crs_wr_hi mem' a ltac:(lia))). intros Hnone.
        assert (He : ~ E' a).
        { intros He. destruct (HN a ltac:(lia) He) as [_ Hs]. exact (Hs Hnone). }
        destruct (HI a ltac:(lia) ltac:(lia) He) as [Hb _]. rewrite SEG in Hb. rewrite Hb in Hnone.
        exact (proj1 (check_reject_clean_starved.crs_wr_hi memc a ltac:(lia)) Hw Hnone).
    - intros a Ha Hn [Hs|He]; [exact Hs | exact (HE a Ha Hn He)]. }
  split; [intros i Hi; rewrite (GK' i Hi); exact (GK i Hi)|].
  split; [lia|].
  apply (HsKindB.rw_cells_keep memc mem' _ _ FR). intros a Ha. cbn [cno_cells cells_size csize Nat.add] in Ha.
  rewrite <- SEG. apply HI; [lia | lia | apply HF; lia].
Qed.

(* A machine stretch that writes the frame's scratch words and blocks the function allocated. *)
Lemma cno_ci_munch : forall E Lc Ac memc mdc Lamc peakc cntc W m',
  CI E Lc Ac memc mdc Lamc peakc cntc ->
  Frame.munch W memc m' -> Frame.wmono rsegs memc m' -> ro_agree rsegs m' ->
  (forall x, ~ Frame.outside W x -> (spZ regs - 96 <= x < spZ regs - 64) \/
     exists a k, In (a, k) E /\ a <= x < a + k /\ forall a' k', In (a', k') Lamc -> (a' - 16, k' + 16) <> (a, k)) ->
  CI E Lc Ac m' mdc Lamc peakc cntc.
Proof.
  intros E Lc Ac memc mdc Lamc peakc cntc W m' (MID & RAc & GKc & LENc & UBc & BKc & FEc & LGc & PKc & FRc)
    MU WM RA' HW.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  unfold CNO_STK, ALLOC_STACK in HAC.
  pose proof MID as (HMc & HWFc & _ & _ & PAc & _).
  pose proof BKc as (BKF & INCL & ND).
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HMc) as DJ.
  pose proof FEc as FEc'. rewrite Forall_forall in FEc'.
  assert (EB : forall a k x, In (a, k) E -> a <= x < a + k ->
      x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lc Ac x).
  { intros a k x Hin Hx. pose proof (INCL _ Hin) as Hb.
    destruct (HsKindB.in_blocks Lc Ac a k Hb) as (p & Hp & Ea).
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p k (x - a) HMc Hp ltac:(lia)) as (_ & _ & R2 & NO).
    rewrite <- Ea in NO, R2. replace (a + (x - a)) with x in NO by lia.
    split; [lia|]. split; [|exact NO].
    replace x with (a + (x - a)) by lia. apply (FEc' _ Hin). cbn [snd]. lia. }
  assert (DB : forall a k a' k' x, In (a, k) (blocks Lc Ac) -> In (a', k') (blocks Lc Ac) -> (a, k) <> (a', k') ->
      a <= x < a + k -> ~ (a' <= x < a' + k')).
  { intros a k a' k' x H1 H2 Hne Hx Hx'.
    destruct (pw_two _ _ _ _ DJ H1 H2 Hne) as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  assert (OUT : forall x, ~ (spZ regs - 96 <= x < spZ regs - 64) ->
      (forall a k, In (a, k) E -> ~ (a <= x < a + k)) -> Frame.outside W x).
  { intros x H1 H2. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso.
    destruct (HW x Ho) as [Hs | (a & k & Hin & Hak & _)]; [exact (H1 Hs) | exact (H2 a k Hin Hak)]. }
  assert (GS : forall x, alloc_statics x -> in_img B x /\ x < alloc_ceiling).
  { intros x Hx.
    assert (Hg : in_globals [(G_FAIL, 8); (G_LIVE, 24)] x).
    { unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. unfold in_globals, G_LIVE, G_FAIL.
      destruct Hx as [Hx|[Hx|[Hx|Hx]]];
        [exists 0x33450, 24 | exists 0x33450, 24 | exists 0x33450, 24 | exists 0x231e0, 8];
        (split; [cbn; tauto | lia]). }
    destruct (GF x Hg) as (Hi & Hr & _). split; [exact Hi | lia]. }
  split.
  { apply (kb_mid_W B API _ _ _ _ _ _ (fun x => alloc_statics x \/ exists a k, In (a, k) E /\ a <= x < a + k)).
    - apply (kb_mid_tail B API cno_IL CNO_STK (spZ regs) L A mem md alloc_statics Lc Ac memc mdc m' W
        (fun x => exists a k, In (a, k) E /\ a <= x < a + k) MID MU).
      + rewrite SEG. exact WM.
      + intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Ho|Ho]; [rewrite (MU x Ho); exact Hx|].
        apply (past_nul.pn_wview_none rsegs m' x).
        * destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
          destruct (HW _ Ho) as [Hs | (a & k & Hin & Hak & _)].
          -- rewrite check_reject_clean_starved.crs_fs_hi in F by lia. discriminate.
          -- exact (proj1 (proj2 (EB a k _ Hin Hak)) (past_nul.pn_seg_img B SEG _ _ F)).
        * apply WM. apply past_nul.pn_wview_some. exact Hx.
      + intros x Hx Hs He. apply OUT; [unfold CNO_STK, ALLOC_STACK in Hs; lia |].
        intros a k Hin Hak. apply He. exists a, k. split; [exact Hin | exact Hak].
      + intros x Hx Ho. apply OUT; [lia |]. intros a k Hin Hak. exact (proj2 (proj2 (EB a k x Hin Hak)) Ho).
      + intros p n i Hp Hp' Hi.
        assert (Hb : In (ptr_addr L p, n) (blocks L A)).
        { unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hp]. }
        pose proof (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hp Hi) as (_ & R1 & R2 & _).
        apply OUT; [lia |]. intros a k Hin Hak.
        destruct (bk_base _ _ _ _ BKc Hb) as [Hc Hne].
        assert (Hneq : (a, k) <> (ptr_addr L p, n)) by (intros Eq; apply Hne; rewrite <- Eq; exact Hin).
        exact (DB a k (ptr_addr L p) n (ptr_addr L p + i) (INCL _ Hin) Hc Hneq Hak ltac:(lia)).
    - intros a Ha Hn [Hs | (a' & k' & Hin & Hak)]; [exact Hs|]. exfalso.
      destruct (EB a' k' a Hin Hak) as (H1 & H2 & _). destruct Ha as [Ha|Ha]; [lia | exact (H2 Ha)]. }
  split; [exact RA'|].
  split.
  { intros i Hi. rewrite <- (GKc i Hi).
    assert (Ho : owned B Lc Ac (ms_got_guard B + i)) by (right; unfold static_owned; right; right; right; right; left; lia).
    pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HMc Ho) as Hlo.
    apply (mbyte_munch (ms_segs B) W memc m' _ MU); [lia|].
    apply OUT; [lia |]. intros a k Hin Hak. exact (proj2 (proj2 (EB a k _ Hin Hak)) Ho). }
  split; [exact LENc|]. split; [exact UBc|]. split; [exact BKc|]. split; [exact FEc|].
  split.
  { pose proof LGc as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
    apply (ledger_frame B Lc Ac Lc Ac memc m' Lamc peakc cntc (2 ^ 64 - 1) LGc).
    - intros a k Hin. exact (proj1 (proj2 (LF (a, k) Hin))).
    - intros x [Hx | (a & k & Hin & Hx)].
      + destruct (GS x Hx) as [Hi Hlo].
        apply (mbyte_munch (ms_segs B) W memc m' x MU); [unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx; lia|].
        apply OUT; [lia|]. intros a k Hin Hak. exact (proj1 (proj2 (EB a k x Hin Hak)) Hi).
      + pose proof (proj1 (proj2 (LF (a, k) Hin))) as Hb. cbn [fst snd] in Hb.
        pose proof (LF (a, k) Hin) as (Hk0 & _). cbn [fst snd] in Hk0.
        pose proof (HsKindB.block_low B API Lc Ac memc mdc (a - 16) (k + 16) (x - (a - 16)) HMc Hb ltac:(lia)) as Bl.
        apply (mbyte_munch (ms_segs B) W memc m' x MU); [lia|].
        destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso.
        destruct (HW x Ho) as [Hs | (a2 & k2 & Hin2 & Hx2 & Hne2)]; [lia|].
        exact (DB (a - 16) (k + 16) a2 k2 x Hb (INCL _ Hin2) (fun Eq => Hne2 a k Hin Eq) ltac:(lia) Hx2). }
  split; [exact PKc|].
  apply (HsKindB.rw_cells_keep memc m' _ _ FRc). intros a Ha. cbn [cno_cells cells_size csize Nat.add] in Ha.
  assert (Ho : Frame.outside W a).
  { apply OUT; [lia|]. intros a' k' Hin Hak. pose proof (EB a' k' a Hin Hak). lia. }
  split; [exact (mbyte_munch rsegs W memc m' a MU ltac:(lia) Ho) | exact (writable_munch rsegs W memc m' a MU ltac:(lia) Ho)].
Qed.

Lemma cno_GS : forall x, alloc_statics x -> in_img B x /\ 0 <= x < alloc_ceiling.
Proof.
  intros x Hx.
  assert (Hg : in_globals [(G_FAIL, 8); (G_LIVE, 24)] x).
  { unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. unfold in_globals, G_LIVE, G_FAIL.
    destruct Hx as [Hx|[Hx|[Hx|Hx]]];
      [exists 0x33450, 24 | exists 0x33450, 24 | exists 0x33450, 24 | exists 0x231e0, 8];
      (split; [cbn; tauto | lia]). }
  destruct (GF x Hg) as (Hi & Hr & _). split; [exact Hi | exact Hr].
Qed.

Lemma cno_in_rm : forall (b1 b2 : list (Z * Z)) x y, In y (b1 ++ x :: b2) -> y <> x -> In y (b1 ++ b2).
Proof.
  intros b1 b2 x y H Hne. apply in_app_or in H as [H|[H|H]]; apply in_or_app;
    [left; exact H | exfalso; exact (Hne (eq_sym H)) | right; exact H].
Qed.

Lemma cno_pn : past_nul_contract B API ->
  forall E Lc Ac regsc memc mdc Lamc peakc cntc d c (db : list byte) b (P : config -> Prop),
  CI E Lc Ac memc mdc Lamc peakc cntc ->
  call_pre_k B MR (ALLOC_STACK + PAST_NUL_FRAME) Lc Ac regsc memc mdc -> spZ regsc = spZ regs - 96 ->
  getr regsc 10 = Z_to_bv 64 d -> getr regsc 11 = Z_to_bv 64 (Z.of_nat (length db)) -> getr regsc 12 = Z_to_bv 64 c ->
  0 <= c < 2 ^ 64 -> Z.of_nat (length db) <= 3 * 2 ^ 20 ->
  (forall i, 0 <= i < Z.of_nat (length db) -> mbyte (ms_segs B) memc (d + i) = nth_error db (Z.to_nat i)) ->
  (0 < Z.of_nat (length db) ->
     exists pd k, In (pd, k) (blocks Lc Ac) /\ pd <= d /\ d + Z.of_nat (length db) <= pd + k) ->
  res_ok_slots Ac b -> room_slots b (Z.of_nat (length db) + 18) ->
  (forall L' A' regs' mem' md' res,
     regs_preserved regsc regs' -> st_init_done A' = true -> getr regs' 10 = Z_to_bv 64 res ->
     4096 <= res -> res + (Z.of_nat (length db) + 18) <= alloc_ceiling ->
     CI ((res, Z.of_nat (length db) + 18) :: E) L' A' mem' md' Lamc peakc cntc ->
     res_ok_slots A' (sb_malloc b (Z.of_nat (length db) + 18)) ->
     keeps B Lc Ac memc mem' 0 ->
     (forall i, 0 <= i < Z.of_nat (length db) + 18 ->
        mbyte (ms_segs B) mem' (res + i) = nth_error (pn_copy db c) (Z.to_nat i)) ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PAST_NUL) memc (seg_rom (ms_segs B))) mdc) P.
Proof.
  intros PN E Lc Ac regsc memc mdc Lamc peakc cntc d c db b P CIc PREc SPc R10 R11 R12 Hc Hn DB DBLK RES ROOM K.
  pose proof CIc as (MID & RAc & GKc & LENc & UBc & BKc & FEc & LGc & PKc & FRc).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof cno_sp as (HAC & H63 & H16).
  pose proof MID as (HMc & _).
  eapply SR_bind.
  { apply (PN Lc Ac regsc memc mdc d (Z.of_nat (length db)) c db b Lamc peakc cntc (2 ^ 64 - 1) PREc).
    - rewrite SEG. exact RAc.
    - exact R10.
    - exact R11.
    - exact R12.
    - exact Hc.
    - lia.
    - reflexivity.
    - exact DB.
    - exact DBLK.
    - exact LGc.
    - exact RES.
    - exact ROOM. }
  intros c' (L' & A' & regs' & mem' & md' & res & -> & CP & RA' & GK' & INIT' & LEN' & R10' & Hr0 & Hr16 & FB &
    (b1 & b2 & BL' & BL) & KP & UB' & CPY & LG' & RES').
  pose proof CP as (HM' & _ & _ & _ & _ & RP & _).
  pose proof FB as (FB1 & FB2 & FB3).
  assert (HE : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (spZ regs - CNO_STK <= a < spZ regs) ->
     res <= a < res + Z.of_nat (length db) + 18 -> alloc_statics a).
  { intros a Ha _ Hx. exfalso. destruct Ha as [Ha|Ha]; [lia|].
    apply (FB3 (a - res)); [lia|]. replace (res + (a - res)) with a by lia. exact Ha. }
  assert (HN : forall a, spZ regs - CNO_STK <= a < spZ regs -> res <= a < res + Z.of_nat (length db) + 18 ->
     spZ regs - 96 <= a /\ mbyte rsegs mem' a <> None).
  { intros a Ha Hx. exfalso. unfold CNO_STK, ALLOC_STACK in Ha. lia. }
  assert (HF : forall a, spZ regs - 64 <= a < spZ regs -> ~ (res <= a < res + Z.of_nat (length db) + 18)).
  { intros a Ha Hx. lia. }
  destruct (cno_seq Lc Ac memc mdc regsc (ALLOC_STACK + PAST_NUL_FRAME) _ L' A' regs' mem' md' MID LENc UBc GKc FRc
    CP SPc ltac:(unfold ALLOC_STACK, PAST_NUL_FRAME; lia) ltac:(unfold CNO_STK, ALLOC_STACK, PAST_NUL_FRAME; lia)
    LEN' GK' HE HN HF) as (MID' & GK'' & LEN'' & FR').
  apply (K L' A' regs' mem' md' res RP INIT' R10' ltac:(lia) FB2).
  - split; [exact MID'|]. split; [rewrite <- SEG; exact RA'|]. split; [exact GK''|]. split; [exact LEN''|].
    split; [apply (cno_ub_keep Lc Ac memc mdc A' MID UBc); exact (cno_ub_gone Lc Ac A' (0, 0) UB' (cno_zero_notin 0))|].
    split.
    { rewrite BL'. apply bk_ins; [rewrite <- BL; exact BKc|].
      apply pw_notin; [rewrite <- BL'; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') | cbn [snd]; lia]. }
    split; [constructor; [cbn [fst snd]; exact FB3 | exact FEc]|].
    split; [exact LG'|]. split; [exact PKc | exact FR'].
  - exact RES'.
  - exact KP.
  - exact CPY.
Qed.

Lemma cno_malloc : malloc_contract B API -> ms_malloc B = 0x16594 ->
  forall E Lc Ac regsc memc mdc Lamc peakc cntc nn b (P : config -> Prop),
  CI E Lc Ac memc mdc Lamc peakc cntc ->
  call_pre_k B MR ALLOC_STACK Lc Ac regsc memc mdc -> spZ regsc = spZ regs - 96 ->
  getr regsc 10 = Z_to_bv 64 nn -> 0 < nn ->
  res_ok_slots Ac b -> room_slots b nn ->
  (forall L' A' regs' mem' md' w,
     regs_preserved regsc regs' -> st_init_done A' = true -> getr regs' 10 = Z_to_bv 64 w ->
     4096 <= w -> w + nn <= alloc_ceiling ->
     CI ((w, nn) :: E) L' A' mem' md' Lamc peakc cntc -> res_ok_slots A' (sb_malloc b nn) ->
     keeps B Lc Ac memc mem' 0 ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 0x16594) memc (seg_rom (ms_segs B))) mdc) P.
Proof.
  intros MALLOC MAL E Lc Ac regsc memc mdc Lamc peakc cntc nn b P CIc PREc SPc R10 Hnn RES ROOM K.
  pose proof CIc as (MID & RAc & GKc & LENc & UBc & BKc & FEc & LGc & PKc & FRc).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof cno_sp as (HAC & H63 & H16).
  pose proof MID as (HMc & _).
  rewrite <- MAL.
  eapply SR_bind.
  { apply (MALLOC Lc Ac regsc memc mdc nn b).
    - apply (proj2 (call_pre_k_alloc B MR Lc Ac regsc memc mdc)). exact PREc.
    - rewrite SEG. exact RAc.
    - exact R10.
    - exact RES.
    - exact ROOM. }
  intros c1 (L' & A' & regs' & mem' & md' & w & -> & CP & R10' & Hw0 & Hw16 & FB & (b1 & b2 & BL' & BL) &
    BKP & RA' & GK' & UB' & INIT' & LEN' & RES').
  pose proof CP as (HM' & _ & _ & _ & _ & RP & _).
  pose proof FB as (FB1 & FB2 & FB3).
  assert (HE : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (spZ regs - CNO_STK <= a < spZ regs) ->
     False -> alloc_statics a) by (intros a _ _ []).
  assert (HN : forall a, spZ regs - CNO_STK <= a < spZ regs -> False -> spZ regs - 96 <= a /\ mbyte rsegs mem' a <> None)
    by (intros a _ []).
  assert (HF : forall a, spZ regs - 64 <= a < spZ regs -> ~ False) by (intros a _ []).
  destruct (cno_seq Lc Ac memc mdc regsc ALLOC_STACK _ L' A' regs' mem' md' MID LENc UBc GKc FRc CP SPc
    ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia) LEN' GK' HE HN HF)
    as (MID' & GK'' & LEN'' & FR').
  assert (KP : keeps B Lc Ac memc mem' 0) by (intros a k i Hin _ Hi; exact (BKP a k i Hin (fun x => x) Hi)).
  pose proof LGc as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  apply (K L' A' regs' mem' md' w RP INIT' R10' FB1 FB2).
  - split; [exact MID'|]. split; [rewrite <- SEG; exact RA'|]. split; [exact GK''|]. split; [exact LEN''|].
    split; [apply (cno_ub_keep Lc Ac memc mdc A' MID UBc); intros q k Hq _; exact (UB' q k Hq)|].
    split.
    { rewrite BL'. apply bk_ins; [rewrite <- BL; exact BKc|].
      apply pw_notin; [rewrite <- BL'; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') | cbn [snd]; lia]. }
    split; [constructor; [cbn [fst snd]; exact FB3 | exact FEc]|].
    split.
    { apply (led_post B API GF ALLOC_STACK Lc Ac regsc memc mdc (fun _ => False) L' A' regs' mem' md' Lamc peakc cntc
        (2 ^ 64 - 1) LGc HMc CP).
      - rewrite SPc. unfold ALLOC_STACK. lia.
      - intros x _ [].
      - intros a k Hin. pose proof (proj1 (proj2 (LF (a, k) Hin))) as Hb. cbn [fst snd] in Hb.
        rewrite BL'. apply past_nul.pn_in_mid. rewrite <- BL. exact Hb.
      - intros a k j Hin Hj. pose proof (LF (a, k) Hin) as (Hk0 & Hb & _). cbn [fst snd] in Hk0, Hb.
        exact (BKP (a - 16) (k + 16) j Hb (fun x => x) ltac:(lia)). }
    split; [exact PKc | exact FR'].
  - exact RES'.
  - exact KP.
Qed.

Lemma cno_free : free_contract B API -> ms_free B = 0x16454 ->
  forall E1 E2 Lc Ac regsc memc mdc peakc cntc a k b (P : config -> Prop),
  CI (E1 ++ (a, k) :: E2) Lc Ac memc mdc Lam peakc cntc ->
  call_pre_k B MR ALLOC_STACK Lc Ac regsc memc mdc -> spZ regsc = spZ regs - 96 ->
  getr regsc 10 = Z_to_bv 64 a -> 0 < k ->
  res_ok_slots Ac b ->
  (forall L' A' regs' mem' md',
     regs_preserved regsc regs' -> (st_init_done Ac = true -> st_init_done A' = true) ->
     CI (E1 ++ E2) L' A' mem' md' Lam peakc cntc -> res_ok_slots A' (sb_free b k) ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 0x16454) memc (seg_rom (ms_segs B))) mdc) P.
Proof.
  intros FREE FRE E1 E2 Lc Ac regsc memc mdc peakc cntc a k b P CIc PREc SPc R10 Hk RES K.
  pose proof CIc as (MID & RAc & GKc & LENc & UBc & BKc & FEc & LGc & PKc & FRc).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof cno_sp as (HAC & H63 & H16).
  pose proof MID as (HMc & HWFc & _).
  pose proof BKc as (_ & INCL & _).
  assert (Hx : In (a, k) (E1 ++ (a, k) :: E2)) by (apply in_or_app; right; left; reflexivity).
  pose proof (INCL _ Hx) as Hab.
  destruct (HsKindB.in_blocks Lc Ac a k Hab) as (p & Hp & Ea).
  pose proof FEc as FEc'. rewrite Forall_forall in FEc'. pose proof (FEc' _ Hx) as NIa. cbn [fst snd] in NIa.
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HMc Hp) as Rp. rewrite <- Ea in Rp.
  rewrite <- FRE.
  eapply SR_bind.
  { apply (FREE Lc Ac regsc memc mdc p k b).
    - apply (proj2 (call_pre_k_alloc B MR Lc Ac regsc memc mdc)). exact PREc.
    - rewrite SEG. exact RAc.
    - exact Hp.
    - rewrite R10, Ea. reflexivity.
    - exact RES. }
  intros c1 (L' & A' & regs' & mem' & md' & -> & CP & (b1 & b2 & BL & BL') & BKP & RA' & GK' & UB' & INIT' & LEN' &
    RES').
  apply call_post_k_alloc in CP.
  pose proof CP as (HM' & _ & _ & _ & _ & RP & _).
  rewrite <- Ea in BL, BKP.
  assert (HE : forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ (spZ regs - CNO_STK <= x < spZ regs) ->
     ptr_addr Lc p <= x < ptr_addr Lc p + k -> alloc_statics x).
  { intros x Hx1 _ Hx2. exfalso. rewrite <- Ea in Hx2. destruct Hx1 as [Hx1|Hx1]; [lia|].
    apply (NIa (x - a)); [lia|]. replace (a + (x - a)) with x by lia. exact Hx1. }
  assert (HN : forall x, spZ regs - CNO_STK <= x < spZ regs -> ptr_addr Lc p <= x < ptr_addr Lc p + k ->
     spZ regs - 96 <= x /\ mbyte rsegs mem' x <> None).
  { intros x Hx1 Hx2. exfalso. rewrite <- Ea in Hx2. unfold CNO_STK, ALLOC_STACK in Hx1. lia. }
  assert (HF : forall x, spZ regs - 64 <= x < spZ regs -> ~ (ptr_addr Lc p <= x < ptr_addr Lc p + k)).
  { intros x Hx1 Hx2. rewrite <- Ea in Hx2. lia. }
  destruct (cno_seq Lc Ac memc mdc regsc ALLOC_STACK _ L' A' regs' mem' md' MID LENc UBc GKc FRc CP SPc
    ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia) LEN' GK' HE HN HF)
    as (MID' & GK'' & LEN'' & FR').
  assert (DJ : pairwise ranges_disjoint (b1 ++ (a, k) :: b2)).
  { rewrite <- BL. exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HMc). }
  assert (NB : ~ In (a, k) (blocks L A)) by (intros Hb; exact (proj2 (bk_base _ _ _ _ BKc Hb) Hx)).
  pose proof LG0 as (_ & _ & _ & _ & _ & LF0). rewrite Forall_forall in LF0.
  pose proof LGc as (_ & _ & _ & _ & _ & LF). rewrite Forall_forall in LF.
  assert (LB : forall a' k', In (a', k') Lam -> In (a' - 16, k' + 16) (blocks Lc Ac) /\ (a' - 16, k' + 16) <> (a, k)).
  { intros a' k' Hin. pose proof (proj1 (proj2 (LF0 (a', k') Hin))) as Hb. cbn [fst snd] in Hb.
    destruct (bk_base _ _ _ _ BKc Hb) as [Hc Hne]. split; [exact Hc|]. intros Eq. apply Hne. rewrite Eq. exact Hx. }
  apply (K L' A' regs' mem' md' RP INIT').
  - split; [exact MID'|]. split; [rewrite <- SEG; exact RA'|]. split; [exact GK''|]. split; [exact LEN''|].
    split.
    { apply (cno_ub_keep Lc Ac memc mdc A' MID UBc).
      apply (cno_ub_gone Lc Ac A' (ptr_addr Lc p, k)); [|rewrite <- Ea; exact NB].
      exact (ub_free Lc Ac A' p k HWFc Hp UB'). }
    split.
    { rewrite BL'. apply (bk_rem _ E1 E2 b1 b2 (a, k)); [rewrite <- BL; exact BKc|].
      exact (pw_notin b1 b2 (a, k) DJ ltac:(cbn [snd]; lia)). }
    split; [apply Forall_app in FEc as [F1 F2]; inversion F2; apply Forall_app; split; assumption|].
    split.
    { apply (led_post B API GF ALLOC_STACK Lc Ac regsc memc mdc _ L' A' regs' mem' md' Lam peakc cntc
        (2 ^ 64 - 1) LGc HMc CP).
      - rewrite SPc. unfold ALLOC_STACK. lia.
      - intros x Hs Hx2. rewrite <- Ea in Hx2. destruct (cno_GS x Hs) as [Hi _].
        apply (NIa (x - a)); [lia|]. replace (a + (x - a)) with x by lia. exact Hi.
      - intros a' k' Hin. destruct (LB a' k' Hin) as [Hc Hne]. rewrite BL'. rewrite BL in Hc.
        exact (cno_in_rm b1 b2 (a, k) _ Hc Hne).
      - intros a' k' j Hin Hj. destruct (LB a' k' Hin) as [Hc Hne].
        pose proof (LF0 (a', k') Hin) as (Hk0 & _). cbn [fst snd] in Hk0.
        apply (BKP (a' - 16) (k' + 16) j Hc); [|lia]. cbv beta. intros Eq.
        rewrite BL in Hc.
        destruct (pw_two _ _ _ _ DJ Hc (in_or_app b1 ((a, k) :: b2) (a, k) (or_intror (or_introl eq_refl))) Hne)
          as [D|D];
          unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    split; [exact PKc | exact FR'].
  - exact RES'.
Qed.

Lemma cno_ffree : fuzz_free_contract B API sb_form ->
  forall E1 E2 Lc Ac regsc memc mdc l1 l2 peakc cntc p k b (P : config -> Prop),
  CI (E1 ++ (p - 16, k + 16) :: E2) Lc Ac memc mdc (l1 ++ (p, k) :: l2) peakc cntc ->
  call_pre_k B MR ALLOC_STACK Lc Ac regsc memc mdc -> spZ regsc = spZ regs - 96 ->
  getr regsc 10 = Z_to_bv 64 p -> res_ok_slots Ac b ->
  (forall L' A' regs' mem' md',
     regs_preserved regsc regs' -> (st_init_done Ac = true -> st_init_done A' = true) ->
     CI (E1 ++ E2) L' A' mem' md' (l1 ++ l2) peakc cntc -> res_ok_slots A' (sb_free b (k + 16)) ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 FUZZ_FREE) memc (seg_rom (ms_segs B))) mdc) P.
Proof.
  intros FF E1 E2 Lc Ac regsc memc mdc l1 l2 peakc cntc p k b P CIc PREc SPc R10 RES K.
  pose proof CIc as (MID & RAc & GKc & LENc & UBc & BKc & FEc & LGc & PKc & FRc).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof cno_sp as (HAC & H63 & H16).
  pose proof MID as (HMc & HWFc & _).
  assert (Hx : In (p - 16, k + 16) (E1 ++ (p - 16, k + 16) :: E2)) by (apply in_or_app; right; left; reflexivity).
  assert (HinL : In (p, k) (l1 ++ (p, k) :: l2)) by (apply in_or_app; right; left; reflexivity).
  destruct (ledger_block_range B API Lc Ac memc mdc _ _ _ _ p k HMc LGc HinL) as (Rp1 & Rp2 & Rp3).
  pose proof LGc as (_ & _ & _ & _ & NDL & LF).
  pose proof (proj1 (Forall_forall _ _) LF (p, k) HinL) as (Hk0 & _). cbn [fst snd] in Hk0.
  eapply SR_bind.
  { apply (FF Lc Ac regsc memc mdc p k b (l1 ++ (p, k) :: l2) peakc cntc (2 ^ 64 - 1) PREc R10 LGc).
    - rewrite SEG. exact RAc.
    - right. exact HinL.
    - exact RES. }
  intros c1 (L' & A' & regs' & mem' & md' & -> & RA' & GK' & INIT' & _ & CP & LEN' & KP & UB' & ARMS).
  destruct ARMS as [(Hp0 & _) | (_ & (b1 & b2 & BL & BL') & (l1' & l2' & EL & LG') & RES')]; [lia|].
  pose proof CP as (HM' & _ & _ & _ & _ & RP & _).
  assert (NI : forall x, p - 16 <= x < p + k -> ~ in_img B x).
  { intros x Hx1. replace x with (p + (x - p)) by lia.
    exact (ledger_block_not_img B Lc Ac memc _ _ _ _ p k (x - p) LGc HinL ltac:(lia)). }
  assert (HE : forall x, (alloc_ceiling <= x < 2 ^ 64 \/ in_img B x) -> ~ (spZ regs - CNO_STK <= x < spZ regs) ->
     free_writes p k x -> alloc_statics x).
  { intros x Hx1 _ [Hl | (_ & Hx2)]; [left; exact Hl|]. exfalso.
    destruct Hx1 as [Hx1|Hx1]; [lia | exact (NI x Hx2 Hx1)]. }
  assert (HN : forall x, spZ regs - CNO_STK <= x < spZ regs -> free_writes p k x ->
     spZ regs - 96 <= x /\ mbyte rsegs mem' x <> None).
  { intros x Hx1 Hx2. exfalso. unfold CNO_STK, ALLOC_STACK in Hx1.
    destruct Hx2 as [Hl | (_ & Hx2)]; [unfold G_LIVE in Hl; lia | lia]. }
  assert (HF : forall x, spZ regs - 64 <= x < spZ regs -> ~ free_writes p k x).
  { intros x Hx1 [Hl | (_ & Hx2)]; [unfold G_LIVE in Hl; lia | lia]. }
  destruct (cno_seq Lc Ac memc mdc regsc ALLOC_STACK _ L' A' regs' mem' md' MID LENc UBc GKc FRc CP SPc
    ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia) LEN' GK' HE HN HF)
    as (MID' & GK'' & LEN'' & FR').
  assert (DJ : pairwise ranges_disjoint (b1 ++ (p - 16, k + 16) :: b2)).
  { rewrite <- BL. exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HMc). }
  assert (NB : ~ In (p - 16, k + 16) (blocks L A)) by (intros Hb; exact (proj2 (bk_base _ _ _ _ BKc Hb) Hx)).
  apply (K L' A' regs' mem' md' RP INIT').
  - split; [exact MID'|]. split; [rewrite <- SEG; exact RA'|]. split; [exact GK''|]. split; [exact LEN''|].
    split; [apply (cno_ub_keep Lc Ac memc mdc A' MID UBc); exact (cno_ub_gone Lc Ac A' _ UB' NB)|].
    split.
    { rewrite BL'. apply (bk_rem _ E1 E2 b1 b2 (p - 16, k + 16)); [rewrite <- BL; exact BKc|].
      exact (pw_notin b1 b2 _ DJ ltac:(cbn [snd]; lia)). }
    split; [apply Forall_app in FEc as [F1 F2]; inversion F2; apply Forall_app; split; assumption|].
    split; [rewrite (lam_rm (l1 ++ (p, k) :: l2) l1 l2 l1' l2' p k (proj1 (NoDup_ListNoDup _) NDL) eq_refl EL);
      exact LG'|].
    split; [exact PKc | exact FR'].
  - exact RES'.
Qed.

Lemma cno_ffree0 : fuzz_free_contract B API sb_form ->
  forall E Lc Ac regsc memc mdc Lamc peakc cntc b (P : config -> Prop),
  CI E Lc Ac memc mdc Lamc peakc cntc -> call_pre_k B MR ALLOC_STACK Lc Ac regsc memc mdc ->
  getr regsc 10 = Z_to_bv 64 0 -> res_ok_slots Ac b ->
  SR (ms_segs B) (mkCfg (mkst regsc (getr regsc 1) memc (seg_rom (ms_segs B))) mdc) P ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 FUZZ_FREE) memc (seg_rom (ms_segs B))) mdc) P.
Proof.
  intros FF E Lc Ac regsc memc mdc Lamc peakc cntc b P CIc PREc R10 RES K.
  pose proof CIc as (_ & RAc & _ & _ & _ & _ & _ & LGc & _).
  eapply SR_bind.
  { apply (FF Lc Ac regsc memc mdc 0 0 b Lamc peakc cntc (2 ^ 64 - 1) PREc R10 LGc).
    - rewrite SEG. exact RAc.
    - left. split; reflexivity.
    - exact RES. }
  intros c1 (L' & A' & regs' & mem' & md' & -> & _ & _ & _ & _ & _ & _ & _ & _ & ARMS).
  destruct ARMS as [(_ & -> & -> & -> & -> & -> & _) | (Hp & _)]; [exact K | exfalso; exact (Hp eq_refl)].
Qed.

Lemma cno_dec : preset_base64_decode_contract B API sb_form ->
  forall E Lc Ac regsc memc mdc Lamc peakc cntc text off (db slack : list byte) pt kt b (P : config -> Prop),
  CI E Lc Ac memc mdc Lamc peakc cntc ->
  call_pre_k B MR DEC_STACK Lc Ac regsc memc mdc -> spZ regsc = spZ regs - 96 ->
  getr regsc 10 = Z_to_bv 64 text -> getr regsc 11 = Z_to_bv 64 (spZ regs - 96 + off) ->
  (off = 8 \/ off = 16 \/ off = 24) ->
  Mem.bytes_at rsegs memc text (db ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) db ->
  (7 <= length slack)%nat -> Z.of_nat (length db) <= 3 * 2 ^ 20 ->
  In (pt, kt) E -> pt <= text -> text + Z.of_nat (length db) + 1 <= pt + kt ->
  cntc + 1 < 2 ^ 63 ->
  res_ok_slots Ac b -> room_slots b (Z.of_nat (length db) / 4 * 3 + 3 + 16) ->
  (forall L' A' regs' mem' md',
     regs_preserved regsc regs' -> (st_init_done Ac = true -> st_init_done A' = true) ->
     keeps B Lc Ac memc mem' 0 ->
     (forall a, spZ regs - 96 <= a < spZ regs -> ~ (spZ regs - 96 + off <= a < spZ regs - 96 + off + 8) ->
        mbyte rsegs mem' a = mbyte rsegs memc a) ->
     ((b64_dec (zs db) = None /\ getr regs' 10 = Z_to_bv 64 0 /\
       CI E L' A' mem' md' Lamc (Z.max peakc (lsum Lamc + (Z.of_nat (length db) / 4 * 3 + 3))) (cntc + 1) /\
       res_ok_slots A' (sb_free (sb_malloc b (Z.of_nat (length db) / 4 * 3 + 3 + 16))
         (Z.of_nat (length db) / 4 * 3 + 3 + 16))) \/
      (exists bs q, b64_dec (zs db) = Some bs /\ getr regs' 10 = Z_to_bv 64 q /\ 4112 <= q /\ q < 2 ^ 47 /\
       CI ((q - 16, Z.of_nat (length db) / 4 * 3 + 3 + 16) :: E) L' A' mem' md'
         ((q, Z.of_nat (length db) / 4 * 3 + 3) :: Lamc)
         (Z.max peakc (lsum Lamc + (Z.of_nat (length db) / 4 * 3 + 3))) (cntc + 1) /\
       Mem.bytes_at rsegs mem' q (map (Z_to_bv 8) bs) /\
       Mem.bytes_at rsegs mem' (spZ regs - 96 + off) (Mem.le8 (Z_to_bv 64 (Z.of_nat (length bs)))) /\
       res_ok_slots A' (sb_malloc b (Z.of_nat (length db) / 4 * 3 + 3 + 16)))) ->
     SR (ms_segs B) (mkCfg (mkst regs' (getr regsc 1) mem' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PRESET_BASE64_DECODE) memc (seg_rom (ms_segs B))) mdc) P.
Proof.
  intros DEC E Lc Ac regsc memc mdc Lamc peakc cntc text off db slack pt kt b P CIc PREc SPc R10 R11 Hoff TB NZ SL
    TBL HE0 Hpt1 Hpt2 Hc1 RES ROOM K.
  pose proof CIc as (MID & RAc & GKc & LENc & UBc & BKc & FEc & LGc & PKc & FRc).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof cno_sp as (HAC & H63 & H16).
  pose proof MID as (HMc & _ & _ & _ & _ & _ & _ & _ & Sc).
  pose proof BKc as (_ & INCL & _).
  pose proof (INCL _ HE0) as Hptb.
  pose proof (HsKindB.block_low B API Lc Ac memc mdc pt kt 0 HMc Hptb ltac:(lia)) as Bp0.
  pose proof (HsKindB.block_low B API Lc Ac memc mdc pt kt (kt - 1) HMc Hptb ltac:(lia)) as Bp1.
  pose proof LGc as (_ & _ & Hc0 & _).
  assert (EZ : Z.of_nat (length (zs db)) = Z.of_nat (length db)).
  { rewrite check_reject_clean_starved.crs_zs_len. reflexivity. }
  eapply SR_bind.
  { apply (DEC Lc Ac regsc memc mdc text (spZ regs - 96 + off) (zs db) slack b Lamc peakc cntc (2 ^ 64 - 1) SEG ERR).
    - rewrite SEG. exact RAc.
    - exact PREc.
    - exact R10.
    - exact R11.
    - exact (check_reject_clean_starved.crs_zs_nz db NZ).
    - exact (check_reject_clean_starved.crs_zs_bytes db).
    - rewrite EZ. lia.
    - rewrite map_app, check_reject_clean_starved.crs_map_zs. cbn [map]. rewrite <- app_assoc. cbn [app].
      rewrite SEG. exact TB.
    - rewrite EZ. pose proof (Z.mod_pos_bound (- (text + Z.of_nat (length db) + 1)) 8 ltac:(lia)). lia.
    - right. right. right. rewrite EZ. exists pt, kt. split; [exact Hptb | lia].
    - lia.
    - Z.div_mod_to_equations. lia.
    - intros i Hi. apply Sc. left. unfold CNO_STK, ALLOC_STACK. lia.
    - right. rewrite EZ. lia.
    - exact LGc.
    - exact RES.
    - unfold dec_size. rewrite EZ. exact ROOM. }
  intros c' (L' & A' & regs' & mem' & md' & q & -> & RA' & GK' & INIT' & CP & LEN' & KP & TXT & ARMS).
  replace (dec_size (zs db)) with (Z.of_nat (length db) / 4 * 3 + 3) in * by (unfold dec_size; rewrite EZ; reflexivity).
  pose proof CP as (HM' & _ & _ & _ & _ & RP & _ & HFR & _).
  assert (QB : q <> 0 -> forall x, q - 16 <= x < q + (Z.of_nat (length db) / 4 * 3 + 3) ->
      x < alloc_ceiling /\ ~ in_img B x).
  { intros Hq x Hx.
    destruct ARMS as [(Hf & _) | [(_ & _ & _ & Hq2 & Hni & _) |
      (bs & _ & _ & _ & _ & _ & _ & _ & Hni & (b1 & b2 & BL' & _) & _)]].
    - lia.
    - split; [lia|]. replace x with (q - 16 + (x - (q - 16))) by lia. apply Hni. lia.
    - assert (Hin : In (q - 16, Z.of_nat (length db) / 4 * 3 + 3 + 16) (blocks L' A')).
      { rewrite BL'. apply in_or_app. right. left. reflexivity. }
      pose proof (HsKindB.block_low B API L' A' mem' md' _ _ (x - (q - 16)) HM' Hin ltac:(lia)) as Bl.
      split; [lia|]. replace x with (q - 16 + (x - (q - 16))) by lia. apply Hni. lia. }
  assert (LP : forall i, 0 <= i < 8 -> mbyte rsegs mem' (spZ regs - 96 + off + i) <> None).
  { intros i Hi.
    assert (Hpres : mbyte rsegs memc (spZ regs - 96 + off + i) <> None).
    { apply (proj1 (check_reject_clean_starved.crs_wr_hi memc (spZ regs - 96 + off + i) ltac:(lia))).
      rewrite <- SEG. apply Sc. left.
      unfold CNO_STK, ALLOC_STACK. lia. }
    destruct ARMS as [(Hf & _) | [(_ & _ & _ & _ & _ & _ & _ & _ & LPs & _) |
      (bs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BLP & _)]].
    - lia.
    - rewrite <- SEG in Hpres |- *. rewrite (LPs i Hi). exact Hpres.
    - destruct BLP as (_ & _ & HB). rewrite SEG in HB.
      pose proof (HB (Z.to_nat i) ltac:(rewrite Mem.length_le8; lia)) as Hb.
      rewrite Z2Nat.id in Hb by lia.
      change (Mem.mrd rsegs mem' (Mem.wa (spZ regs - 96 + off + i)) <> None).
      rewrite Hb. apply nth_error_Some. rewrite Mem.length_le8. lia. }
  assert (HE : forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ (spZ regs - CNO_STK <= a < spZ regs) ->
     dec_writes q (Z.of_nat (length db) / 4 * 3 + 3) (spZ regs - 96 + off) a -> alloc_statics a).
  { intros a Ha Hn [Hs | [(Hq & Hx) | Hx]]; [exact Hs | exfalso | exfalso].
    - destruct (QB Hq a Hx) as [Q1 Q2]. destruct Ha as [Ha|Ha]; [lia | exact (Q2 Ha)].
    - apply Hn. unfold CNO_STK, ALLOC_STACK. lia. }
  assert (HN : forall a, spZ regs - CNO_STK <= a < spZ regs ->
     dec_writes q (Z.of_nat (length db) / 4 * 3 + 3) (spZ regs - 96 + off) a ->
     spZ regs - 96 <= a /\ mbyte rsegs mem' a <> None).
  { intros a Ha [Hs | [(Hq & Hx) | Hx]].
    - exfalso. destruct (cno_GS a Hs). unfold CNO_STK, ALLOC_STACK in Ha. lia.
    - exfalso. destruct (QB Hq a Hx). unfold CNO_STK, ALLOC_STACK in Ha. lia.
    - split; [lia|]. replace a with (spZ regs - 96 + off + (a - (spZ regs - 96 + off))) by lia. apply LP. lia. }
  assert (HF : forall a, spZ regs - 64 <= a < spZ regs ->
     ~ dec_writes q (Z.of_nat (length db) / 4 * 3 + 3) (spZ regs - 96 + off) a).
  { intros a Ha [Hs | [(Hq & Hx) | Hx]]; [destruct (cno_GS a Hs); lia | destruct (QB Hq a Hx); lia | lia]. }
  destruct (cno_seq Lc Ac memc mdc regsc DEC_STACK _ L' A' regs' mem' md' MID LENc UBc GKc FRc CP SPc
    ltac:(unfold DEC_STACK, ALLOC_STACK; lia) ltac:(unfold CNO_STK, DEC_STACK, ALLOC_STACK; lia) LEN' GK' HE HN HF)
    as (MID' & GK'' & LEN'' & FR').
  assert (STK : forall a, spZ regs - 96 <= a < spZ regs -> ~ (spZ regs - 96 + off <= a < spZ regs - 96 + off + 8) ->
     mbyte rsegs mem' a = mbyte rsegs memc a).
  { intros a Ha Hn. rewrite <- SEG. apply HFR.
    - left. lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HMc Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
    - unfold scratch_k. rewrite SPc. lia.
    - intros [Hs | [(Hq & Hx) | Hx]]; [destruct (cno_GS a Hs); lia | destruct (QB Hq a Hx); lia | lia]. }
  destruct ARMS as [(Hf & _) | [(_ & Hd & Hq & Hq2 & Hni & R10' & BL & UB' & LPs & LG' & RES') |
    (bs & _ & Hd & Hq & R10' & Hq16 & Hqn & Hns & Hni & (b1 & b2 & BL' & BL) & UB' & LG' & BQ & BLP & RES')]].
  - lia.
  - apply (K L' A' regs' mem' md' RP INIT' KP STK). left.
    split; [exact Hd|]. split; [exact R10'|].
    split; [|exact RES'].
    split; [exact MID'|]. split; [rewrite <- SEG; exact RA'|]. split; [exact GK''|]. split; [exact LEN''|].
    split; [apply (cno_ub_keep Lc Ac memc mdc A' MID UBc); exact (cno_ub_gone Lc Ac A' (0, 0) UB' (cno_zero_notin 0))|].
    split; [rewrite BL; exact BKc|]. split; [exact FEc|].
    split; [rewrite Z.mod_small in LG' by lia; exact LG'|].
    split; [lia | exact FR'].
  - assert (Hqin : In (q, Z.of_nat (length db) / 4 * 3 + 3) ((q, Z.of_nat (length db) / 4 * 3 + 3) :: Lamc))
      by (left; reflexivity).
    rewrite Z.mod_small in LG' by lia.
    destruct (ledger_block_range B API L' A' mem' md' _ _ _ _ _ _ HM' LG' Hqin) as (Rq1 & Rq2 & Rq3).
    apply (K L' A' regs' mem' md' RP INIT' KP STK). right. exists bs, q.
    split; [exact Hd|]. split; [exact R10'|]. split; [lia|]. split; [lia|].
    split.
    + split; [exact MID'|]. split; [rewrite <- SEG; exact RA'|]. split; [exact GK''|]. split; [exact LEN''|].
      split; [apply (cno_ub_keep Lc Ac memc mdc A' MID UBc); exact (cno_ub_gone Lc Ac A' (0, 0) UB' (cno_zero_notin 0))|].
      split.
      { rewrite BL'. apply bk_ins; [rewrite <- BL; exact BKc|].
        apply pw_notin; [rewrite <- BL'; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM') | cbn [snd]; lia]. }
      split; [constructor; [cbn [fst snd]; exact Hni | exact FEc]|].
      split; [exact LG'|].
      split; [lia | exact FR'].
    + split; [rewrite SEG in BQ; exact BQ|]. split; [rewrite SEG in BLP; exact BLP | exact RES'].
Qed.

Lemma RS_getr : forall R R' x8 x9 x18 x19 x20 x21, (forall r, getr R' r = getr R r) ->
  RS R x8 x9 x18 x19 x20 x21 -> RS R' x8 x9 x18 x19 x20 x21.
Proof. intros R R' x8 x9 x18 x19 x20 x21 HG. apply RS_pres. intros r _. apply HG. Qed.

Lemma cno_bytes_keep : forall m m' a bs, Mem.bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  Mem.bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) K. split; [exact H1|]. split; [exact H2|].
  intros i Hi. pose proof (K (Z.of_nat i) ltac:(lia)) as Ki.
  change (Mem.mrd rsegs m' (Mem.wa (a + Z.of_nat i)) = Mem.mrd rsegs m (Mem.wa (a + Z.of_nat i))) in Ki.
  rewrite Ki. exact (H i Hi).
Qed.

Lemma cno_bytes_of : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m (a + i) = nth_error bs (Z.to_nat i)) ->
  Mem.bytes_at rsegs m a bs.
Proof.
  intros m a bs H1 H2 H. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  pose proof (H (Z.of_nat i) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb. exact Hb.
Qed.

Lemma cno_lens : forall m a v, Mem.bytes_at rsegs m a (Mem.le8 v) -> Mem.bytes_at rsegs m (a + 8) (Mem.le8 v) ->
  Mem.bytes_at rsegs m (a + 16) (Mem.le8 v) -> Mem.wr_at rsegs m a 24 ->
  Step.rw_cells rsegs m a [C8 v; C8 v; C8 v].
Proof.
  intros m a v B0 B8 B16 W. split; [split; [cbn; tauto|] | exact W].
  cbn [cells_bytes cbytes]. apply Mem.bytes_at_app. split; [exact B0|].
  rewrite Mem.length_le8. replace (a + Z.of_nat 8) with (a + 8) by lia.
  apply Mem.bytes_at_app. split; [exact B8|].
  rewrite Mem.length_le8, app_nil_r. replace (a + 8 + Z.of_nat 8) with (a + 16) by lia. exact B16.
Qed.

Lemma cno_wr : forall E Lc Ac memc mdc Lamc peakc cntc a n, CI E Lc Ac memc mdc Lamc peakc cntc ->
  spZ regs - CNO_STK <= a -> a + n <= spZ regs -> 0 <= n -> Mem.wr_at rsegs memc a n.
Proof.
  intros E Lc Ac memc mdc Lamc peakc cntc a n ((_ & _ & _ & _ & _ & _ & _ & _ & S) & _) H1 H2 Hn.
  pose proof cno_sp as (HAC & H63 & _). pose proof alloc_ceiling_val. unfold CNO_STK, ALLOC_STACK in *.
  split; [lia|]. split; [lia|]. intros i Hi. rewrite <- SEG.
  assert (Hw : writable_at (ms_segs B) memc (a + i)) by (apply S; left; lia). exact Hw.
Qed.

Lemma cno_blk_wr : forall Lc Ac memc mdc a k, aa_MR API Lc Ac memc mdc -> In (a, k) (blocks Lc Ac) ->
  Mem.wr_at rsegs memc a k.
Proof.
  intros Lc Ac memc mdc a k HM Hin. destruct (HsKindB.in_blocks Lc Ac a k Hin) as (p & Hp & ->).
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HM Hp) as R. pose proof alloc_ceiling_lt.
  split; [lia|]. split; [lia|]. intros i Hi.
  destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p k i HM Hp Hi) as ((b & Hb) & _).
  unfold wview, Mem.wa. rewrite Hb. discriminate.
Qed.

Definition cno_post (bf : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md' peak',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
    call_post_k B MR CNO_STK L A regs mem md alloc_statics L' A' regs' mem' md' /\
    (st_init_done A = true -> st_init_done A' = true) /\
    blocks L' A' = blocks L A /\
    keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
    peak <= peak' /\
    ledger B L' A' mem' Lam peak' (cnt + 3) (2 ^ 64 - 1) /\
    res_ok_slots A' bf.

(* free of the three buffers and the epilogue *)
Lemma cno_frees : free_contract B API -> ms_free B = 0x16454 ->
  forall Lc Ac regsc memc mdc peakc r1 r2 w N b x8 x19 x20 x21,
  CI [(w, N); (r2, N); (r1, N)] Lc Ac memc mdc Lam peakc (cnt + 3) -> st_init_done Ac = true -> 0 < N ->
  getr regsc 1 = Z_to_bv 64 0x13584 -> getr regsc 10 = Z_to_bv 64 r1 ->
  RS regsc x8 (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 x20 x21 ->
  res_ok_slots Ac b ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 0x16454) memc (seg_rom (ms_segs B))) mdc)
    (cno_post (sb_free (sb_free (sb_free b N) N) N)).
Proof.
  intros FREE FRE Lc Ac regsc memc mdc peakc r1 r2 w N b x8 x19 x20 x21 CIc INIT HN R1 R10 RSc RES.
  pose proof cno_sp as (HAC & H63 & H16). pose proof alloc_ceiling_val as Hacv.
  pose proof PRE as (_ & _ & _ & HRA & _).
  pose proof RSc as (Q2 & _ & _ & _ & _ & _ & _ & QG).
  destruct (cno_pre _ _ _ _ _ _ _ _ regsc ALLOC_STACK CIc INIT Q2 (QG 4 ltac:(lia))
    ltac:(rewrite R1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia))
    as [SP PREc].
  apply (cno_free FREE FRE [(w, N); (r2, N)] [] Lc Ac regsc memc mdc peakc (cnt + 3) r1 N b _ CIc PREc SP R10 HN RES).
  intros L1 A1 regs1 mem1 md1 RP1 INIT1 CI1 RES1. specialize (INIT1 INIT).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP1 RSc) as RS1.
  pose proof CI1 as ((HM1 & _) & _).
  rewrite R1.
  eapply (kb_run B regs1 (Z_to_bv 64 0x13584) mem1 md1
    (fun R pc' m' => RS R x8 (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 x20 x21 /\ getr R 1 = Z_to_bv 64 0x1358c /\
       getr R 10 = Z_to_bv 64 r2 /\ pc' = Z_to_bv 64 0x16454 /\ m' = mem1));
    [exact (proj1 (kb_md B API _ _ _ _ HM1)) | exact (proj2 (kb_md B API _ _ _ _ HM1)) | |].
  { rewrite SEG. unfold rmk. destruct RS1 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21.
    eapply Exec.evt_mono; [apply cno_s10|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs1); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR2 pc2 mem2 regs2 (RS2 & R2_1 & R2_10 & -> & ->) HG2.
  apply (RS_getr _ _ _ _ _ _ _ _ HG2) in RS2. rewrite <- HG2 in R2_1, R2_10.
  pose proof RS2 as (Q2b & _ & _ & _ & _ & _ & _ & QGb).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs2 ALLOC_STACK CI1 INIT1 Q2b (QGb 4 ltac:(lia))
    ltac:(rewrite R2_1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia))
    as [SP2 PRE2].
  apply (cno_free FREE FRE [(w, N)] [] L1 A1 regs2 mem1 md1 peakc (cnt + 3) r2 N _ _ CI1 PRE2 SP2 R2_10 HN RES1).
  intros L3 A3 regs3 mem3 md3 RP3 INIT3 CI3 RES3. specialize (INIT3 INIT1).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP3 RS2) as RS3.
  pose proof CI3 as ((HM3 & _) & _).
  rewrite R2_1.
  eapply (kb_run B regs3 (Z_to_bv 64 0x1358c) mem3 md3
    (fun R pc' m' => RS R x8 (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 x20 x21 /\ getr R 1 = Z_to_bv 64 0x13594 /\
       getr R 10 = Z_to_bv 64 w /\ pc' = Z_to_bv 64 0x16454 /\ m' = mem3));
    [exact (proj1 (kb_md B API _ _ _ _ HM3)) | exact (proj2 (kb_md B API _ _ _ _ HM3)) | |].
  { rewrite SEG. unfold rmk. destruct RS3 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21.
    eapply Exec.evt_mono; [apply cno_s11|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs3); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR4 pc4 mem4 regs4 (RS4 & R4_1 & R4_10 & -> & ->) HG4.
  apply (RS_getr _ _ _ _ _ _ _ _ HG4) in RS4. rewrite <- HG4 in R4_1, R4_10.
  pose proof RS4 as (Q2c & _ & _ & _ & _ & _ & _ & QGc).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs4 ALLOC_STACK CI3 INIT3 Q2c (QGc 4 ltac:(lia))
    ltac:(rewrite R4_1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia))
    as [SP4 PRE4].
  apply (cno_free FREE FRE [] [] L3 A3 regs4 mem3 md3 peakc (cnt + 3) w N _ _ CI3 PRE4 SP4 R4_10 HN RES3).
  intros L5 A5 regs5 mem5 md5 RP5 INIT5 CI5 RES5. specialize (INIT5 INIT3).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP5 RS4) as RS5.
  pose proof CI5 as (MID5 & RA5 & GK5 & LEN5 & UB5 & BK5 & FE5 & LG5 & PK5 & FR5).
  pose proof MID5 as (HM5 & _).
  rewrite R4_1.
  eapply (kb_run B regs5 (Z_to_bv 64 0x13594) mem5 md5
    (fun R pc' m' => regs_preserved regs R /\ pc' = ret_pc (getr regs 1) /\ m' = mem5));
    [exact (proj1 (kb_md B API _ _ _ _ HM5)) | exact (proj2 (kb_md B API _ _ _ _ HM5)) | |].
  { rewrite SEG. unfold rmk. destruct RS5 as (P2 & _ & _ & _ & _ & _ & _ & PG). rewrite P2.
    eapply Exec.evt_mono.
    - eapply cno_epi with (xra := getr regs 1) (xs0 := getr regs 8) (xs1 := getr regs 9) (xs2 := getr regs 18)
        (xs3 := getr regs 19) (xs4 := getr regs 20) (xs5 := getr regs 21) (xs6 := getr regs 22).
      rewrite MState.unsigned_lit by lia. replace (spZ regs - 96 + 32) with (spZ regs - 64) by lia. exact FR5.
    - intros ms' ->. do 3 eexists. split; [reflexivity|].
      split; [|split; reflexivity].
      apply check_reject_clean_starved.crs_rp;
        [ rewrite MState.unsigned_lit by lia; replace (spZ regs - 96 + 96) with (spZ regs) by lia; unfold spZ;
          apply Z_to_bv_bv_unsigned
        | exact (PG 3 ltac:(lia)) | exact (PG 4 ltac:(lia)) | reflexivity | reflexivity | reflexivity | reflexivity
        | reflexivity | reflexivity | reflexivity | exact (PG 23 ltac:(lia)) | exact (PG 24 ltac:(lia))
        | exact (PG 25 ltac:(lia)) | exact (PG 26 ltac:(lia)) | exact (PG 27 ltac:(lia)) ]. }
  intros RR6 pc6 mem6 regs6 (RPR & -> & ->) HG6.
  apply SR_ret. unfold cno_post. exists L5, A5, regs6, mem5, md5, peakc.
  split; [rewrite (kb_ret_pc _ HRA); reflexivity|].
  split; [rewrite SEG; exact RA5|].
  split; [exact GK5|].
  split; [apply (kb_post B API); [exact MID5 | exact (kb_preserved_getr _ _ _ RPR HG6)]|].
  split; [intros _; exact INIT5|].
  split; [exact (bk_final _ _ BK5)|].
  split; [exact (check_reject_clean_starved.crs_keep_of_mid B API _ _ _ _ _ _ _ _ _ _ _ MID5 UB5)|].
  split; [exact UB5|].
  split; [exact PK5|]. split; [exact LG5 | exact RES5].
Qed.

(* fuzz_free of the three decoded buffers, then the frees *)
Lemma cno_ff_some : fuzz_free_contract B API sb_form -> free_contract B API -> ms_free B = 0x16454 ->
  forall Lc Ac regsc memc mdc peakc r1 r2 w N q1 q2 q3 M b x19,
  CI [(q3 - 16, M + 16); (q2 - 16, M + 16); (q1 - 16, M + 16); (w, N); (r2, N); (r1, N)] Lc Ac memc mdc
     ((q3, M) :: (q2, M) :: (q1, M) :: Lam) peakc (cnt + 3) -> st_init_done Ac = true -> 0 < N ->
  getr regsc 1 = Z_to_bv 64 0x1356c -> getr regsc 10 = Z_to_bv 64 q1 ->
  RS regsc (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 (Z_to_bv 64 q2) (Z_to_bv 64 q3) ->
  res_ok_slots Ac b ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 FUZZ_FREE) memc (seg_rom (ms_segs B))) mdc)
    (cno_post (sb_free (sb_free (sb_free (sb_free (sb_free (sb_free b (M + 16)) (M + 16)) (M + 16)) N) N) N)).
Proof.
  intros FF FREE FRE Lc Ac regsc memc mdc peakc r1 r2 w N q1 q2 q3 M b x19 CIc INIT HN R1 R10 RSc RES.
  pose proof cno_sp as (HAC & H63 & H16). pose proof alloc_ceiling_val as Hacv.
  pose proof RSc as (Q2 & _ & _ & _ & _ & _ & _ & QG).
  destruct (cno_pre _ _ _ _ _ _ _ _ regsc ALLOC_STACK CIc INIT Q2 (QG 4 ltac:(lia))
    ltac:(rewrite R1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia))
    as [SP PREc].
  apply (cno_ffree FF [(q3 - 16, M + 16); (q2 - 16, M + 16)] [(w, N); (r2, N); (r1, N)] Lc Ac regsc memc mdc
    [(q3, M); (q2, M)] Lam peakc (cnt + 3) q1 M b _ CIc PREc SP R10 RES).
  intros L1 A1 regs1 mem1 md1 RP1 INIT1 CI1 RES1. specialize (INIT1 INIT).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP1 RSc) as RS1.
  pose proof CI1 as ((HM1 & _) & _).
  rewrite R1.
  eapply (kb_run B regs1 (Z_to_bv 64 0x1356c) mem1 md1
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 (Z_to_bv 64 q2) (Z_to_bv 64 q3) /\
       getr R 1 = Z_to_bv 64 0x13574 /\ getr R 10 = Z_to_bv 64 q2 /\ pc' = Z_to_bv 64 0x141c4 /\ m' = mem1));
    [exact (proj1 (kb_md B API _ _ _ _ HM1)) | exact (proj2 (kb_md B API _ _ _ _ HM1)) | |].
  { rewrite SEG. unfold rmk. destruct RS1 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21.
    eapply Exec.evt_mono; [apply cno_s7|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs1); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR2 pc2 mem2 regs2 (RS2 & R2_1 & R2_10 & -> & ->) HG2.
  apply (RS_getr _ _ _ _ _ _ _ _ HG2) in RS2. rewrite <- HG2 in R2_1, R2_10.
  pose proof RS2 as (Q2b & _ & _ & _ & _ & _ & _ & QGb).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs2 ALLOC_STACK CI1 INIT1 Q2b (QGb 4 ltac:(lia))
    ltac:(rewrite R2_1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia))
    as [SP2 PRE2].
  change (Z_to_bv 64 0x141c4) with (Z_to_bv 64 FUZZ_FREE).
  apply (cno_ffree FF [(q3 - 16, M + 16)] [(w, N); (r2, N); (r1, N)] L1 A1 regs2 mem1 md1
    [(q3, M)] Lam peakc (cnt + 3) q2 M _ _ CI1 PRE2 SP2 R2_10 RES1).
  intros L3 A3 regs3 mem3 md3 RP3 INIT3 CI3 RES3. specialize (INIT3 INIT1).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP3 RS2) as RS3.
  pose proof CI3 as ((HM3 & _) & _).
  rewrite R2_1.
  eapply (kb_run B regs3 (Z_to_bv 64 0x13574) mem3 md3
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 (Z_to_bv 64 q2) (Z_to_bv 64 q3) /\
       getr R 1 = Z_to_bv 64 0x1357c /\ getr R 10 = Z_to_bv 64 q3 /\ pc' = Z_to_bv 64 0x141c4 /\ m' = mem3));
    [exact (proj1 (kb_md B API _ _ _ _ HM3)) | exact (proj2 (kb_md B API _ _ _ _ HM3)) | |].
  { rewrite SEG. unfold rmk. destruct RS3 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21.
    eapply Exec.evt_mono; [apply cno_s8|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs3); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR4 pc4 mem4 regs4 (RS4 & R4_1 & R4_10 & -> & ->) HG4.
  apply (RS_getr _ _ _ _ _ _ _ _ HG4) in RS4. rewrite <- HG4 in R4_1, R4_10.
  pose proof RS4 as (Q2c & _ & _ & _ & _ & _ & _ & QGc).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs4 ALLOC_STACK CI3 INIT3 Q2c (QGc 4 ltac:(lia))
    ltac:(rewrite R4_1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia))
    as [SP4 PRE4].
  change (Z_to_bv 64 0x141c4) with (Z_to_bv 64 FUZZ_FREE).
  apply (cno_ffree FF [] [(w, N); (r2, N); (r1, N)] L3 A3 regs4 mem3 md3
    [] Lam peakc (cnt + 3) q3 M _ _ CI3 PRE4 SP4 R4_10 RES3).
  intros L5 A5 regs5 mem5 md5 RP5 INIT5 CI5 RES5. specialize (INIT5 INIT3).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP5 RS4) as RS5.
  pose proof CI5 as ((HM5 & _) & _).
  rewrite R4_1.
  eapply (kb_run B regs5 (Z_to_bv 64 0x1357c) mem5 md5
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 (Z_to_bv 64 q2) (Z_to_bv 64 q3) /\
       getr R 1 = Z_to_bv 64 0x13584 /\ getr R 10 = Z_to_bv 64 r1 /\ pc' = Z_to_bv 64 0x16454 /\ m' = mem5));
    [exact (proj1 (kb_md B API _ _ _ _ HM5)) | exact (proj2 (kb_md B API _ _ _ _ HM5)) | |].
  { rewrite SEG. unfold rmk. destruct RS5 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21.
    eapply Exec.evt_mono; [apply cno_s9|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs5); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR6 pc6 mem6 regs6 (RS6 & R6_1 & R6_10 & -> & ->) HG6.
  apply (RS_getr _ _ _ _ _ _ _ _ HG6) in RS6. rewrite <- HG6 in R6_1, R6_10.
  exact (cno_frees FREE FRE L5 A5 regs6 mem5 md5 peakc r1 r2 w N _ _ _ _ _ CI5 INIT5 HN R6_1 R6_10 RS6 RES5).
Qed.

Lemma cno_ff_none : fuzz_free_contract B API sb_form -> free_contract B API -> ms_free B = 0x16454 ->
  forall Lc Ac regsc memc mdc peakc r1 r2 w N b x19,
  CI [(w, N); (r2, N); (r1, N)] Lc Ac memc mdc Lam peakc (cnt + 3) -> st_init_done Ac = true -> 0 < N ->
  getr regsc 1 = Z_to_bv 64 0x1356c -> getr regsc 10 = Z_to_bv 64 0 ->
  RS regsc (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 (Z_to_bv 64 0) (Z_to_bv 64 0) ->
  res_ok_slots Ac b ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 FUZZ_FREE) memc (seg_rom (ms_segs B))) mdc)
    (cno_post (sb_free (sb_free (sb_free b N) N) N)).
Proof.
  intros FF FREE FRE Lc Ac regsc memc mdc peakc r1 r2 w N b x19 CIc INIT HN R1 R10 RSc RES.
  pose proof cno_sp as (HAC & H63 & H16). pose proof alloc_ceiling_val as Hacv.
  pose proof CIc as ((HMc & _) & _).
  pose proof RSc as (Q2 & _ & _ & _ & _ & _ & _ & QG).
  destruct (cno_pre _ _ _ _ _ _ _ _ regsc ALLOC_STACK CIc INIT Q2 (QG 4 ltac:(lia))
    ltac:(rewrite R1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia))
    as [SP PREc].
  apply (cno_ffree0 FF _ _ _ _ _ _ _ _ _ b _ CIc PREc R10 RES).
  rewrite R1.
  eapply (kb_run B regsc (Z_to_bv 64 0x1356c) memc mdc
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 (Z_to_bv 64 0) (Z_to_bv 64 0) /\
       getr R 1 = Z_to_bv 64 0x13574 /\ getr R 10 = Z_to_bv 64 0 /\ pc' = Z_to_bv 64 0x141c4 /\ m' = memc));
    [exact (proj1 (kb_md B API _ _ _ _ HMc)) | exact (proj2 (kb_md B API _ _ _ _ HMc)) | |].
  { rewrite SEG. unfold rmk. destruct RSc as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21.
    eapply Exec.evt_mono; [apply cno_s7|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regsc); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR2 pc2 mem2 regs2 (RS2 & R2_1 & R2_10 & -> & ->) HG2.
  apply (RS_getr _ _ _ _ _ _ _ _ HG2) in RS2. rewrite <- HG2 in R2_1, R2_10.
  pose proof RS2 as (Q2b & _ & _ & _ & _ & _ & _ & QGb).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs2 ALLOC_STACK CIc INIT Q2b (QGb 4 ltac:(lia))
    ltac:(rewrite R2_1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia))
    as [SP2 PRE2].
  change (Z_to_bv 64 0x141c4) with (Z_to_bv 64 FUZZ_FREE).
  apply (cno_ffree0 FF _ _ _ _ _ _ _ _ _ b _ CIc PRE2 R2_10 RES).
  rewrite R2_1.
  eapply (kb_run B regs2 (Z_to_bv 64 0x13574) memc mdc
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 (Z_to_bv 64 0) (Z_to_bv 64 0) /\
       getr R 1 = Z_to_bv 64 0x1357c /\ getr R 10 = Z_to_bv 64 0 /\ pc' = Z_to_bv 64 0x141c4 /\ m' = memc));
    [exact (proj1 (kb_md B API _ _ _ _ HMc)) | exact (proj2 (kb_md B API _ _ _ _ HMc)) | |].
  { rewrite SEG. unfold rmk. destruct RS2 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21.
    eapply Exec.evt_mono; [apply cno_s8|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs2); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR4 pc4 mem4 regs4 (RS4 & R4_1 & R4_10 & -> & ->) HG4.
  apply (RS_getr _ _ _ _ _ _ _ _ HG4) in RS4. rewrite <- HG4 in R4_1, R4_10.
  pose proof RS4 as (Q2c & _ & _ & _ & _ & _ & _ & QGc).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs4 ALLOC_STACK CIc INIT Q2c (QGc 4 ltac:(lia))
    ltac:(rewrite R4_1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(unfold CNO_STK, ALLOC_STACK; lia))
    as [SP4 PRE4].
  change (Z_to_bv 64 0x141c4) with (Z_to_bv 64 FUZZ_FREE).
  apply (cno_ffree0 FF _ _ _ _ _ _ _ _ _ b _ CIc PRE4 R4_10 RES).
  rewrite R4_1.
  eapply (kb_run B regs4 (Z_to_bv 64 0x1357c) memc mdc
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 (Z_to_bv 64 0) (Z_to_bv 64 0) /\
       getr R 1 = Z_to_bv 64 0x13584 /\ getr R 10 = Z_to_bv 64 r1 /\ pc' = Z_to_bv 64 0x16454 /\ m' = memc));
    [exact (proj1 (kb_md B API _ _ _ _ HMc)) | exact (proj2 (kb_md B API _ _ _ _ HMc)) | |].
  { rewrite SEG. unfold rmk. destruct RS4 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21.
    eapply Exec.evt_mono; [apply cno_s9|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs4); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR6 pc6 mem6 regs6 (RS6 & R6_1 & R6_10 & -> & ->) HG6.
  apply (RS_getr _ _ _ _ _ _ _ _ HG6) in RS6. rewrite <- HG6 in R6_1, R6_10.
  exact (cno_frees FREE FRE Lc Ac regs6 memc mdc peakc r1 r2 w N _ _ _ _ _ CIc INIT HN R6_1 R6_10 RS6 RES).
Qed.

Lemma cno_not_out2 : forall lo1 hi1 lo2 hi2 x, ~ Frame.outside [(lo1, hi1); (lo2, hi2)] x ->
  lo1 <= x < hi1 \/ lo2 <= x < hi2.
Proof.
  intros lo1 hi1 lo2 hi2 x H. cbn [Frame.outside] in H.
  destruct (Z_le_gt_dec lo1 x); destruct (Z_lt_ge_dec x hi1); destruct (Z_le_gt_dec lo2 x);
    destruct (Z_lt_ge_dec x hi2); try (left; lia); try (right; lia);
    exfalso; apply H; (split; [lia|]); (split; [lia | exact I]).
Qed.

Lemma cno_ro_hi : forall m m' lo hi, ro_agree rsegs m -> Frame.munch [(lo, hi)] m m' -> 0x55000 <= lo ->
  ro_agree rsegs m'.
Proof.
  intros m m' lo hi RA MU Hlo a Ha. unfold Mem.mrd. rewrite (MU a); [exact (RA a Ha)|].
  cbn [Frame.outside]. split; [|exact I]. intros [H1 H2]. unfold Mem.ro_addr in Ha.
  rewrite (HsKindB.find_segment_above rsegs 0x55000 (bv_unsigned a) 1 HsKindB.rsegs_top) in Ha by lia.
  discriminate.
Qed.

Lemma cno_ci_ext : forall E Lc Ac memc mdc Lamc peakc cntc m', CI E Lc Ac memc mdc Lamc peakc cntc ->
  (forall x, m' x = memc x) -> CI E Lc Ac m' mdc Lamc peakc cntc.
Proof.
  intros E Lc Ac memc mdc Lamc peakc cntc m' CIc EQ.
  pose proof CIc as (_ & RAc & _).
  apply (cno_ci_munch E Lc Ac memc mdc Lamc peakc cntc [] m' CIc).
  - intros x _. exact (EQ x).
  - intros x Hx. unfold wview in *. rewrite EQ. exact Hx.
  - intros a Ha. unfold Mem.mrd. rewrite EQ. exact (RAc a Ha).
  - intros x Hx. exfalso. apply Hx. exact I.
Qed.

Lemma cno_keep0 : forall E Lc Ac memc mdc Lamc peakc cntc, CI E Lc Ac memc mdc Lamc peakc cntc ->
  keeps B L A mem memc 0.
Proof.
  intros E Lc Ac memc mdc Lamc peakc cntc (MID & _ & _ & _ & UB & _).
  exact (check_reject_clean_starved.crs_keep_of_mid B API _ _ _ _ _ _ _ _ _ _ _ MID UB).
Qed.

Lemma cno_keep_bytes : forall Lc Ac m m' a k t bs, keeps B Lc Ac m m' 0 -> In (a, k) (blocks Lc Ac) ->
  Mem.bytes_at rsegs m t bs -> a <> 0 -> a <= t -> t + Z.of_nat (length bs) <= a + k -> Mem.bytes_at rsegs m' t bs.
Proof.
  intros Lc Ac m m' a k t bs KP Hin BS Ha H1 H2. apply (cno_bytes_keep m m' t bs BS). intros i Hi. rewrite <- SEG.
  replace (t + i) with (a + (t - a + i)) by lia. apply (KP a k (t - a + i) Hin Ha). lia.
Qed.

Lemma cno_E_disj : forall E Lc Ac memc mdc Lamc peakc cntc a k a' k', CI E Lc Ac memc mdc Lamc peakc cntc ->
  In (a, k) E -> In (a', k') E -> (a, k) <> (a', k') -> a + k <= a' \/ a' + k' <= a.
Proof.
  intros E Lc Ac memc mdc Lamc peakc cntc a k a' k' ((HMc & _) & _ & _ & _ & _ & (_ & INCL & _) & _) H1 H2 Hne.
  destruct (pw_two _ _ _ _ (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HMc) (INCL _ H1) (INCL _ H2) Hne) as [D|D];
    unfold ranges_disjoint in D; cbn [fst snd] in D; lia.
Qed.

Lemma cno_nd3 : forall {X : Type} (x y z : X), List.NoDup [x; y; z] -> x <> y /\ x <> z /\ y <> z.
Proof.
  intros X x y z ND. apply NoDup_cons_iff in ND as [H1 ND]. apply NoDup_cons_iff in ND as [H2 _].
  split; [intros ->; apply H1; left; reflexivity|]. split; [intros ->; apply H1; right; left; reflexivity|].
  intros ->. apply H2. left. reflexivity.
Qed.

(* second and third decode, the comparison and the frees, when the text decodes *)
Lemma cno_rest_some : preset_base64_decode_contract B API sb_form -> bcmp_contract -> fuzz_free_contract B API sb_form ->
  free_contract B API -> ms_free B = 0x16454 ->
  forall (db : list byte) bs M N L1 A1 regs1 mem1 md1 peak1 r1 r2 w q1 b1 x19 x20 x21,
  M = Z.of_nat (length db) / 4 * 3 + 3 -> N = Z.of_nat (length db) + 18 ->
  b64_dec (zs db) = Some bs -> ~ In (Z_to_bv 8 0) db -> Z.of_nat (length db) <= 3 * 2 ^ 20 -> cnt + 3 < 2 ^ 63 ->
  CI [(q1 - 16, M + 16); (w, N); (r2, N); (r1, N)] L1 A1 mem1 md1 ((q1, M) :: Lam) peak1 (cnt + 1) ->
  st_init_done A1 = true -> getr regs1 10 = Z_to_bv 64 q1 -> 4112 <= q1 < 2 ^ 47 ->
  RS regs1 (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 x20 x21 ->
  Mem.bytes_at rsegs mem1 q1 (map (Z_to_bv 8) bs) ->
  Mem.bytes_at rsegs mem1 (spZ regs - 96 + 24) (Mem.le8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
  Mem.bytes_at rsegs mem1 r2 (pn_copy db 66) ->
  Mem.bytes_at rsegs mem1 w (db ++ repeat (Z_to_bv 8 0) 18) ->
  res_ok_slots A1 b1 -> room_slots b1 (M + 16) -> room_slots (sb_malloc b1 (M + 16)) (M + 16) ->
  SR (ms_segs B) (mkCfg (mkst regs1 (Z_to_bv 64 0x134e4) mem1 (seg_rom (ms_segs B))) md1)
    (cno_post (sb_free (sb_free (sb_free (sb_free (sb_free (sb_free
       (sb_malloc (sb_malloc b1 (M + 16)) (M + 16)) (M + 16)) (M + 16)) (M + 16)) N) N) N)).
Proof.
  intros DEC BCMP FF FREE FRE db bs M N L1 A1 regs1 mem1 md1 peak1 r1 r2 w q1 b1 x19 x20 x21 EM EN DB NZ DBL HC
    CI1 INIT1 R1_10 Hq1 RS1 BQ1 BL1 BR2 BW RES1 RM2 RM3.
  subst M N.
  pose proof cno_sp as (HAC & H63 & H16). pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof CI1 as ((HM1 & _) & _ & _ & _ & _ & (_ & INCL1 & _) & _).
  pose proof (dec_len _ _ DB) as DL. rewrite check_reject_clean_starved.crs_zs_len in DL.
  assert (LBS : Z.of_nat (length bs) <= Z.of_nat (length db) / 4 * 3 + 3) by (Z.div_mod_to_equations; lia).
  assert (Hwb : In (w, Z.of_nat (length db) + 18) (blocks L1 A1)) by (apply INCL1; right; left; reflexivity).
  pose proof (HsKindB.block_low B API L1 A1 mem1 md1 w _ 0 HM1 Hwb ltac:(lia)) as Bw.
  assert (Hq1b : In (q1 - 16, Z.of_nat (length db) / 4 * 3 + 3 + 16) (blocks L1 A1))
    by (apply INCL1; left; reflexivity).
  (* to the second decode *)
  eapply (kb_run B regs1 (Z_to_bv 64 0x134e4) mem1 md1
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) (Z_to_bv 64 q1) x20 x21 /\
       getr R 1 = Z_to_bv 64 0x134f4 /\ getr R 10 = Z_to_bv 64 r2 /\
       getr R 11 = Z_to_bv 64 (spZ regs - 96 + 16) /\ pc' = Z_to_bv 64 0x14e90 /\ m' = mem1));
    [exact (proj1 (kb_md B API _ _ _ _ HM1)) | exact (proj2 (kb_md B API _ _ _ _ HM1)) | |].
  { rewrite SEG. unfold rmk. destruct RS1 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21, R1_10.
    eapply Exec.evt_mono; [apply cno_s4|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs1); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [f_equal; rewrite MState.unsigned_lit by lia; reflexivity|]. split; reflexivity. }
  intros RR2 pc2 mem2 regs2 (RS2 & R2_1 & R2_10 & R2_11 & -> & ->) HG2.
  apply (RS_getr _ _ _ _ _ _ _ _ HG2) in RS2. rewrite <- HG2 in R2_1, R2_10, R2_11.
  pose proof RS2 as (Q2 & _ & _ & _ & _ & _ & _ & QG).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs2 DEC_STACK CI1 INIT1 Q2 (QG 4 ltac:(lia))
    ltac:(rewrite R2_1; vm_compute; reflexivity) ltac:(unfold DEC_STACK, ALLOC_STACK; lia)
    ltac:(unfold CNO_STK, DEC_STACK, ALLOC_STACK; lia)) as [SP2 PRE2].
  change (Z_to_bv 64 0x14e90) with (Z_to_bv 64 PRESET_BASE64_DECODE).
  apply (cno_dec DEC _ _ _ _ _ _ _ _ _ r2 16 db ([Z_to_bv 8 (66 mod 256); Z_to_bv 8 65] ++ repeat (Z_to_bv 8 0) 15)
    r2 (Z.of_nat (length db) + 18) _ _ CI1 PRE2 SP2 R2_10 R2_11 ltac:(lia) BR2 NZ
    ltac:(rewrite length_app, repeat_length; cbn [length]; lia) DBL ltac:(right; right; left; reflexivity)
    ltac:(lia) ltac:(lia) ltac:(lia) RES1 RM2).
  intros L2 A2 regs3 mem3 md2 RP3 INIT2 KP2 STK2
    [(DN & _) | (bs2 & q2 & DS2 & R3_10 & Hq2 & Hq2' & CI2 & BQ2 & BL2 & RES2)];
    [rewrite DB in DN; discriminate|].
  rewrite DB in DS2. injection DS2 as <-. specialize (INIT2 INIT1).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP3 RS2) as RS3.
  pose proof CI2 as ((HM2 & _) & _ & _ & _ & _ & (_ & INCL2 & _) & _).
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP2 Hq1b BQ1 ltac:(lia) ltac:(lia) ltac:(rewrite length_map; lia)) as BQ1b.
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP2 Hwb BW ltac:(lia) ltac:(lia)
    ltac:(rewrite length_app, repeat_length; lia)) as BWb.
  assert (BL1b : Mem.bytes_at rsegs mem3 (spZ regs - 96 + 24) (Mem.le8 (Z_to_bv 64 (Z.of_nat (length bs))))).
  { apply (cno_bytes_keep mem1 mem3 _ _ BL1). intros i Hi. rewrite Mem.length_le8 in Hi. apply STK2; lia. }
  (* to the third decode *)
  rewrite R2_1.
  eapply (kb_run B regs3 (Z_to_bv 64 0x134f4) mem3 md2
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) (Z_to_bv 64 q1) (Z_to_bv 64 q2) x21 /\
       getr R 1 = Z_to_bv 64 0x13504 /\ getr R 10 = Z_to_bv 64 w /\
       getr R 11 = Z_to_bv 64 (spZ regs - 96 + 8) /\ pc' = Z_to_bv 64 0x14e90 /\ m' = mem3));
    [exact (proj1 (kb_md B API _ _ _ _ HM2)) | exact (proj2 (kb_md B API _ _ _ _ HM2)) | |].
  { rewrite SEG. unfold rmk. destruct RS3 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21, R3_10.
    eapply Exec.evt_mono; [apply cno_s5|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs3); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [f_equal; rewrite MState.unsigned_lit by lia; reflexivity|]. split; reflexivity. }
  intros RR4 pc4 mem4 regs4 (RS4 & R4_1 & R4_10 & R4_11 & -> & ->) HG4.
  apply (RS_getr _ _ _ _ _ _ _ _ HG4) in RS4. rewrite <- HG4 in R4_1, R4_10, R4_11.
  pose proof RS4 as (Q4 & _ & _ & _ & _ & _ & _ & QG4).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs4 DEC_STACK CI2 INIT2 Q4 (QG4 4 ltac:(lia))
    ltac:(rewrite R4_1; vm_compute; reflexivity) ltac:(unfold DEC_STACK, ALLOC_STACK; lia)
    ltac:(unfold CNO_STK, DEC_STACK, ALLOC_STACK; lia)) as [SP4 PRE4].
  change (Z_to_bv 64 0x14e90) with (Z_to_bv 64 PRESET_BASE64_DECODE).
  apply (cno_dec DEC _ _ _ _ _ _ _ _ _ w 8 db (repeat (Z_to_bv 8 0) 17)
    w (Z.of_nat (length db) + 18) _ _ CI2 PRE4 SP4 R4_10 R4_11 ltac:(lia) BWb NZ
    ltac:(rewrite repeat_length; lia) DBL ltac:(right; right; left; reflexivity)
    ltac:(lia) ltac:(lia) ltac:(lia) RES2 RM3).
  intros L3 A3 regs5 mem5 md3 RP5 INIT3 KP3 STK3
    [(DN & _) | (bs3 & q3 & DS3 & R5_10 & Hq3 & Hq3' & CI3 & BQ3 & BL3 & RES3)];
    [rewrite DB in DN; discriminate|].
  rewrite DB in DS3. injection DS3 as <-. specialize (INIT3 INIT2).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP5 RS4) as RS5.
  pose proof CI3 as ((HM3 & _) & RA3 & _).
  assert (Hq1c : In (q1 - 16, Z.of_nat (length db) / 4 * 3 + 3 + 16) (blocks L2 A2))
    by (apply INCL2; right; left; reflexivity).
  assert (Hq2c : In (q2 - 16, Z.of_nat (length db) / 4 * 3 + 3 + 16) (blocks L2 A2))
    by (apply INCL2; left; reflexivity).
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP3 Hq1c BQ1b ltac:(lia) ltac:(lia) ltac:(rewrite length_map; lia))
    as BQ1c.
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP3 Hq2c BQ2 ltac:(lia) ltac:(lia) ltac:(rewrite length_map; lia))
    as BQ2c.
  assert (BL1c : Mem.bytes_at rsegs mem5 (spZ regs - 96 + 24) (Mem.le8 (Z_to_bv 64 (Z.of_nat (length bs))))).
  { apply (cno_bytes_keep mem3 mem5 _ _ BL1b). intros i Hi. rewrite Mem.length_le8 in Hi. apply STK3; lia. }
  assert (BL2c : Mem.bytes_at rsegs mem5 (spZ regs - 96 + 16) (Mem.le8 (Z_to_bv 64 (Z.of_nat (length bs))))).
  { apply (cno_bytes_keep mem3 mem5 _ _ BL2). intros i Hi. rewrite Mem.length_le8 in Hi. apply STK3; lia. }
  (* the comparison, up to the first fuzz_free *)
  rewrite R4_1.
  eapply (kb_run B regs5 (Z_to_bv 64 0x13504) mem5 md3
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) (Z_to_bv 64 q1) (Z_to_bv 64 q2)
         (Z_to_bv 64 q3) /\
       getr R 1 = Z_to_bv 64 0x1356c /\ getr R 10 = Z_to_bv 64 q1 /\ pc' = Z_to_bv 64 0x141c4 /\
       (forall x, m' x = mem5 x)));
    [exact (proj1 (kb_md B API _ _ _ _ HM3)) | exact (proj2 (kb_md B API _ _ _ _ HM3)) | |].
  { rewrite SEG. unfold rmk. destruct RS5 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21, R5_10.
    eapply Exec.evt_mono.
    - eapply cno_cmp_some_r with (q1 := q1) (q2 := q2) (q3 := q3) (len := Z.of_nat (length bs))
        (xs := map (Z_to_bv 8) bs);
        [exact BCMP | reflexivity | reflexivity | reflexivity | lia | lia | lia | rewrite length_map; reflexivity | lia
        | rewrite MState.unsigned_lit by lia; lia | rewrite MState.unsigned_lit by lia; lia | | exact BQ1c
        | exact BQ2c | exact BQ3 | exact RA3].
      rewrite MState.unsigned_lit by lia. apply cno_lens.
      + exact BL3.
      + replace (spZ regs - 96 + 8 + 8) with (spZ regs - 96 + 16) by lia. exact BL2c.
      + replace (spZ regs - 96 + 8 + 16) with (spZ regs - 96 + 24) by lia. exact BL1c.
      + apply (cno_wr _ _ _ _ _ _ _ _ _ _ CI3); unfold CNO_STK, ALLOC_STACK; lia.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & -> & EQ).
      do 3 eexists. split; [reflexivity|].
      split; [apply (RS_mk regs5); [exact PG | reflexivity ..]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact EQ]. }
  intros RR6 pc6 mem6 regs6 (RS6 & R6_1 & R6_10 & -> & EQ6) HG6.
  apply (RS_getr _ _ _ _ _ _ _ _ HG6) in RS6. rewrite <- HG6 in R6_1, R6_10.
  pose proof (cno_ci_ext _ _ _ _ _ _ _ _ mem6 CI3 EQ6) as CI6.
  replace (cnt + 1 + 1 + 1) with (cnt + 3) in CI6 by lia.
  change (Z_to_bv 64 0x141c4) with (Z_to_bv 64 FUZZ_FREE).
  exact (cno_ff_some FF FREE FRE L3 A3 regs6 mem6 md3 _ r1 r2 w _ q1 q2 q3 _ _ _ CI6 INIT3 ltac:(lia) R6_1 R6_10 RS6
    RES3).
Qed.

(* second and third decode, the comparison and the frees, when the text does not decode *)
Lemma cno_rest_none : preset_base64_decode_contract B API sb_form -> fuzz_free_contract B API sb_form ->
  free_contract B API -> ms_free B = 0x16454 ->
  forall (db : list byte) M N L1 A1 regs1 mem1 md1 peak1 r1 r2 w b1 x19 x20 x21,
  M = Z.of_nat (length db) / 4 * 3 + 3 -> N = Z.of_nat (length db) + 18 ->
  b64_dec (zs db) = None -> ~ In (Z_to_bv 8 0) db -> Z.of_nat (length db) <= 3 * 2 ^ 20 -> cnt + 3 < 2 ^ 63 ->
  CI [(w, N); (r2, N); (r1, N)] L1 A1 mem1 md1 Lam peak1 (cnt + 1) ->
  st_init_done A1 = true -> getr regs1 10 = Z_to_bv 64 0 ->
  RS regs1 (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) x19 x20 x21 ->
  Mem.bytes_at rsegs mem1 r2 (pn_copy db 66) ->
  Mem.bytes_at rsegs mem1 w (db ++ repeat (Z_to_bv 8 0) 18) ->
  res_ok_slots A1 b1 -> room_slots b1 (M + 16) -> room_slots (sb_free (sb_malloc b1 (M + 16)) (M + 16)) (M + 16) ->
  SR (ms_segs B) (mkCfg (mkst regs1 (Z_to_bv 64 0x134e4) mem1 (seg_rom (ms_segs B))) md1)
    (cno_post (sb_free (sb_free (sb_free
       (sb_free (sb_malloc (sb_free (sb_malloc b1 (M + 16)) (M + 16)) (M + 16)) (M + 16)) N) N) N)).
Proof.
  intros DEC FF FREE FRE db M N L1 A1 regs1 mem1 md1 peak1 r1 r2 w b1 x19 x20 x21 EM EN DB NZ DBL HC
    CI1 INIT1 R1_10 RS1 BR2 BW RES1 RM2 RM3.
  subst M N.
  pose proof cno_sp as (HAC & H63 & H16). pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof CI1 as ((HM1 & _) & _ & _ & _ & _ & (_ & INCL1 & _) & _).
  assert (Hwb : In (w, Z.of_nat (length db) + 18) (blocks L1 A1)) by (apply INCL1; left; reflexivity).
  pose proof (HsKindB.block_low B API L1 A1 mem1 md1 w _ 0 HM1 Hwb ltac:(lia)) as Bw.
  eapply (kb_run B regs1 (Z_to_bv 64 0x134e4) mem1 md1
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) (Z_to_bv 64 0) x20 x21 /\
       getr R 1 = Z_to_bv 64 0x134f4 /\ getr R 10 = Z_to_bv 64 r2 /\
       getr R 11 = Z_to_bv 64 (spZ regs - 96 + 16) /\ pc' = Z_to_bv 64 0x14e90 /\ m' = mem1));
    [exact (proj1 (kb_md B API _ _ _ _ HM1)) | exact (proj2 (kb_md B API _ _ _ _ HM1)) | |].
  { rewrite SEG. unfold rmk. destruct RS1 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21, R1_10.
    eapply Exec.evt_mono; [apply cno_s4|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs1); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [f_equal; rewrite MState.unsigned_lit by lia; reflexivity|]. split; reflexivity. }
  intros RR2 pc2 mem2 regs2 (RS2 & R2_1 & R2_10 & R2_11 & -> & ->) HG2.
  apply (RS_getr _ _ _ _ _ _ _ _ HG2) in RS2. rewrite <- HG2 in R2_1, R2_10, R2_11.
  pose proof RS2 as (Q2 & _ & _ & _ & _ & _ & _ & QG).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs2 DEC_STACK CI1 INIT1 Q2 (QG 4 ltac:(lia))
    ltac:(rewrite R2_1; vm_compute; reflexivity) ltac:(unfold DEC_STACK, ALLOC_STACK; lia)
    ltac:(unfold CNO_STK, DEC_STACK, ALLOC_STACK; lia)) as [SP2 PRE2].
  change (Z_to_bv 64 0x14e90) with (Z_to_bv 64 PRESET_BASE64_DECODE).
  apply (cno_dec DEC _ _ _ _ _ _ _ _ _ r2 16 db ([Z_to_bv 8 (66 mod 256); Z_to_bv 8 65] ++ repeat (Z_to_bv 8 0) 15)
    r2 (Z.of_nat (length db) + 18) _ _ CI1 PRE2 SP2 R2_10 R2_11 ltac:(lia) BR2 NZ
    ltac:(rewrite length_app, repeat_length; cbn [length]; lia) DBL ltac:(right; left; reflexivity)
    ltac:(lia) ltac:(lia) ltac:(lia) RES1 RM2).
  intros L2 A2 regs3 mem3 md2 RP3 INIT2 KP2 STK2
    [(_ & R3_10 & CI2 & RES2) | (bs2 & q2 & DS2 & _)]; [|rewrite DB in DS2; discriminate].
  specialize (INIT2 INIT1).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP3 RS2) as RS3.
  pose proof CI2 as ((HM2 & _) & _).
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP2 Hwb BW ltac:(lia) ltac:(lia)
    ltac:(rewrite length_app, repeat_length; lia)) as BWb.
  rewrite R2_1.
  eapply (kb_run B regs3 (Z_to_bv 64 0x134f4) mem3 md2
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) (Z_to_bv 64 0) (Z_to_bv 64 0) x21 /\
       getr R 1 = Z_to_bv 64 0x13504 /\ getr R 10 = Z_to_bv 64 w /\
       getr R 11 = Z_to_bv 64 (spZ regs - 96 + 8) /\ pc' = Z_to_bv 64 0x14e90 /\ m' = mem3));
    [exact (proj1 (kb_md B API _ _ _ _ HM2)) | exact (proj2 (kb_md B API _ _ _ _ HM2)) | |].
  { rewrite SEG. unfold rmk. destruct RS3 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21, R3_10.
    eapply Exec.evt_mono; [apply cno_s5|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs3); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [f_equal; rewrite MState.unsigned_lit by lia; reflexivity|]. split; reflexivity. }
  intros RR4 pc4 mem4 regs4 (RS4 & R4_1 & R4_10 & R4_11 & -> & ->) HG4.
  apply (RS_getr _ _ _ _ _ _ _ _ HG4) in RS4. rewrite <- HG4 in R4_1, R4_10, R4_11.
  pose proof RS4 as (Q4 & _ & _ & _ & _ & _ & _ & QG4).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs4 DEC_STACK CI2 INIT2 Q4 (QG4 4 ltac:(lia))
    ltac:(rewrite R4_1; vm_compute; reflexivity) ltac:(unfold DEC_STACK, ALLOC_STACK; lia)
    ltac:(unfold CNO_STK, DEC_STACK, ALLOC_STACK; lia)) as [SP4 PRE4].
  change (Z_to_bv 64 0x14e90) with (Z_to_bv 64 PRESET_BASE64_DECODE).
  apply (cno_dec DEC _ _ _ _ _ _ _ _ _ w 8 db (repeat (Z_to_bv 8 0) 17)
    w (Z.of_nat (length db) + 18) _ _ CI2 PRE4 SP4 R4_10 R4_11 ltac:(lia) BWb NZ
    ltac:(rewrite repeat_length; lia) DBL ltac:(left; reflexivity)
    ltac:(lia) ltac:(lia) ltac:(lia) RES2 RM3).
  intros L3 A3 regs5 mem5 md3 RP5 INIT3 KP3 STK3
    [(_ & R5_10 & CI3 & RES3) | (bs3 & q3 & DS3 & _)]; [|rewrite DB in DS3; discriminate].
  specialize (INIT3 INIT2).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP5 RS4) as RS5.
  pose proof CI3 as ((HM3 & _) & _).
  rewrite R4_1.
  eapply (kb_run B regs5 (Z_to_bv 64 0x13504) mem5 md3
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w) (Z_to_bv 64 0) (Z_to_bv 64 0)
         (Z_to_bv 64 0) /\
       getr R 1 = Z_to_bv 64 0x1356c /\ getr R 10 = Z_to_bv 64 0 /\ pc' = Z_to_bv 64 0x141c4 /\ m' = mem5));
    [exact (proj1 (kb_md B API _ _ _ _ HM3)) | exact (proj2 (kb_md B API _ _ _ _ HM3)) | |].
  { rewrite SEG. unfold rmk. destruct RS5 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21, R5_10.
    eapply Exec.evt_mono; [apply cno_cmp_none; reflexivity|].
    intros ms' (a1' & ->). do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs5); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR6 pc6 mem6 regs6 (RS6 & R6_1 & R6_10 & -> & ->) HG6.
  apply (RS_getr _ _ _ _ _ _ _ _ HG6) in RS6. rewrite <- HG6 in R6_1, R6_10.
  replace (cnt + 1 + 1 + 1) with (cnt + 3) in CI3 by lia.
  change (Z_to_bv 64 0x141c4) with (Z_to_bv 64 FUZZ_FREE).
  exact (cno_ff_none FF FREE FRE L3 A3 regs6 mem5 md3 _ r1 r2 w _ _ _ CI3 INIT3 ltac:(lia) R6_1 R6_10 RS6 RES3).
Qed.

Lemma cno_main : past_nul_contract B API -> malloc_contract B API -> ms_malloc B = 0x16594 ->
  memcpy_contract -> memset_contract -> preset_base64_decode_contract B API sb_form -> bcmp_contract ->
  fuzz_free_contract B API sb_form -> free_contract B API -> ms_free B = 0x16454 ->
  forall d (db : list byte) bnd,
  getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length db)) ->
  Mem.bytes_at (ms_segs B) mem d db -> ~ In (Z_to_bv 8 0) db -> Z.of_nat (length db) <= 3 * 2 ^ 20 ->
  (0 < Z.of_nat (length db) ->
     exists pd k, In (pd, k) (blocks L A) /\ pd <= d /\ d + Z.of_nat (length db) <= pd + k) ->
  cnt + 3 < 2 ^ 63 -> ro_agree (ms_segs B) mem -> res_ok_slots A bnd ->
  hs_room bnd (nor_ops (Z.of_nat (length db)) (opt_ok (b64_dec (zs db)))) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (seg_rom (ms_segs B))) md)
    (cno_post (hs_rb bnd (nor_ops (Z.of_nat (length db)) (opt_ok (b64_dec (zs db)))))).
Proof.
  intros PN MALLOC MAL MEMCPY MEMSET DEC BCMP FF FREE FRE d db bnd R10 R11 DB NZ DBL DBLK HC RA ROK ROOM.
  pose proof cno_sp as (HAC & H63 & H16). pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof PRE as (HM & HWF & HBD & HRA & _ & _ & _ & HWS & HTP & HER & _).
  pose proof LG0 as (_ & _ & Hc0 & _).
  destruct (kb_md B API L A mem md HM) as [Hh Hl0].
  assert (STK : Frame.stk rsegs mem (spZ regs - 9216) (spZ regs)).
  { pose proof (kb_stk B API cno_IL CNO_STK L A regs mem md PRE ltac:(unfold CNO_STK, ALLOC_STACK; lia)) as K.
    rewrite SEG in K. unfold CNO_STK, ALLOC_STACK in K. exact K. }
  assert (RA0 : ro_agree rsegs mem) by (rewrite <- SEG; exact RA).
  assert (PNL : forall c, length (pn_copy db c) = (length db + 18)%nat).
  { intros c. unfold pn_copy. rewrite !length_app, repeat_length. cbn [length]. lia. }
  assert (DBm : forall m', (forall i, 0 <= i < Z.of_nat (length db) ->
       mbyte (ms_segs B) m' (d + i) = mbyte (ms_segs B) mem (d + i)) ->
     forall i, 0 <= i < Z.of_nat (length db) -> mbyte (ms_segs B) m' (d + i) = nth_error db (Z.to_nat i)).
  { intros m' Hm i Hi. rewrite (Hm i Hi). destruct DB as (_ & _ & HB).
    pose proof (HB (Z.to_nat i) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia. exact Hb. }
  assert (DBk : forall E Lc Ac memc mdc Lamc peakc cntc, CI E Lc Ac memc mdc Lamc peakc cntc ->
     forall i, 0 <= i < Z.of_nat (length db) -> mbyte (ms_segs B) memc (d + i) = nth_error db (Z.to_nat i)).
  { intros E Lc Ac memc mdc Lamc peakc cntc CIc. apply DBm. intros i Hi.
    destruct (DBLK ltac:(lia)) as (pd & k & Hin & H1 & H2).
    pose proof (cno_base_pos _ _ Hin).
    replace (d + i) with (pd + (d - pd + i)) by lia.
    exact (cno_keep0 _ _ _ _ _ _ _ _ CIc pd k (d - pd + i) Hin ltac:(lia) ltac:(lia)). }
  unfold nor_ops in ROOM |- *. cbn [app hs_room hs_rb] in ROOM |- *.
  destruct ROOM as (RM1 & RM2 & RM3 & ROOM).
  (* prologue, up to the first past_nul *)
  eapply (kb_run B regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem md
    (fun R pc' m' => RS R (getr regs 8) (getr regs 9) (getr regs 18) (Z_to_bv 64 (Z.of_nat (length db)))
         (Z_to_bv 64 d) (getr regs 21) /\
       getr R 1 = Z_to_bv 64 0x13474 /\ getr R 10 = Z_to_bv 64 d /\
       getr R 11 = Z_to_bv 64 (Z.of_nat (length db)) /\ getr R 12 = Z_to_bv 64 65 /\
       pc' = Z_to_bv 64 0x13e38 /\ Step.rw_cells rsegs m' (spZ regs - 64) (cno_cells regs) /\
       Frame.munch [(spZ regs - 96, spZ regs)] mem m' /\ Frame.wmono rsegs mem m'));
    [exact Hh | exact Hl0 | |].
  { rewrite SEG. unfold CHECK_NO_OVERREAD, rmk. rewrite R10, R11. eapply Exec.evt_mono.
    - eapply cno_pro; [exact STK | unfold spZ in *; lia].
    - intros ms' (m' & -> & FR & MU & WM). do 3 eexists. split; [reflexivity|].
      split; [apply (RS_mk regs); [intros k _; reflexivity | f_equal; unfold spZ; lia | reflexivity ..]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [unfold spZ; replace (bv_unsigned (getr regs 2) - 64) with (bv_unsigned (getr regs 2) + -64) by lia;
        exact FR|].
      split; [unfold spZ; replace (bv_unsigned (getr regs 2) - 96) with (bv_unsigned (getr regs 2) + -96) by lia;
        exact MU | exact WM]. }
  intros RR1 pc1 mem1 regs1 (RS1 & R1_1 & R1_10 & R1_11 & R1_12 & -> & FR1 & MU1 & WM1) HG1.
  apply (RS_getr _ _ _ _ _ _ _ _ HG1) in RS1. rewrite <- HG1 in R1_1, R1_10, R1_11, R1_12.
  pose proof RS1 as (Q1_2 & _ & _ & _ & _ & _ & _ & QG1).
  assert (SP1 : spZ regs1 = spZ regs - 96) by (unfold spZ at 1; rewrite Q1_2, MState.unsigned_lit by lia; reflexivity).
  assert (OUT1 : forall x, 0 <= x < alloc_ceiling -> Frame.outside [(spZ regs - 96, spZ regs)] x)
    by (intros x Hx; apply outside_one; lia).
  assert (CI0 : CI [] L A mem1 md Lam peak cnt).
  { split.
    { apply (kb_mid_A B API cno_IL CNO_STK (spZ regs) L A mem md mem1 [(spZ regs - 96, spZ regs)] alloc_statics
        HM HWF HBD).
      - intros a [Ha|Ha]; [apply HWS; exact Ha | apply HER; exact Ha].
      - exact MU1.
      - rewrite SEG. exact WM1.
      - intros x Hx Hs _. apply outside_one. unfold CNO_STK, ALLOC_STACK in Hs. lia.
      - intros x Hx _. apply outside_one. lia. }
    split; [exact (cno_ro_hi mem mem1 _ _ RA0 MU1 ltac:(lia))|].
    split.
    { intros i Hi.
      assert (Ho : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; right; right; right; right; left; lia).
      pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho) as Hlo.
      apply (mbyte_munch (ms_segs B) _ mem mem1 _ MU1); [lia | apply outside_one; lia]. }
    split; [lia|]. split; [intros q k Hq _; exact Hq|]. split; [apply bk_nil|]. split; [constructor|].
    split; [exact (HsKindB.ledger_munch B API L A mem md mem1 _ Lam peak cnt _ HM LG0 MU1 OUT1)|].
    split; [lia | exact FR1]. }
  assert (PRE1 : call_pre_k B MR (ALLOC_STACK + PAST_NUL_FRAME) L A regs1 mem1 md).
  { apply (kb_pre_A B API CNO_STK 96 (ALLOC_STACK + PAST_NUL_FRAME) L A regs mem md regs1 mem1
      [(spZ regs - 96, spZ regs)] PRE).
    - lia.
    - unfold ALLOC_STACK, PAST_NUL_FRAME. lia.
    - unfold CNO_STK, ALLOC_STACK, PAST_NUL_FRAME. lia.
    - exact SP1.
    - rewrite SP1. Z.div_mod_to_equations. lia.
    - exact (QG1 4 ltac:(lia)).
    - rewrite R1_1. vm_compute. reflexivity.
    - exact MU1.
    - rewrite SEG. exact WM1.
    - intros x Hx Hx'. apply outside_one. lia.
    - intros x Hx _. apply outside_one. lia. }
  change (Z_to_bv 64 0x13e38) with (Z_to_bv 64 PAST_NUL).
  (* past_nul (d, n, 'A') *)
  apply (cno_pn PN [] L A regs1 mem1 md Lam peak cnt d 65 db bnd _ CI0 PRE1 SP1 R1_10 R1_11 R1_12 ltac:(lia) DBL
    (DBk _ _ _ _ _ _ _ _ CI0) DBLK ROK RM1).
  intros L1 A1 regs2 mem2 md1 r1 RP2 INIT1 R2_10 Hr1 Hr1' CI1 RES1 KP1 CPY1.
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP2 RS1) as RS2.
  pose proof CI1 as ((HM1 & _) & _ & _ & _ & _ & (_ & INCL1 & _) & _).
  assert (Hr1b : In (r1, Z.of_nat (length db) + 18) (blocks L1 A1)) by (apply INCL1; left; reflexivity).
  assert (BR1 : Mem.bytes_at rsegs mem2 r1 (pn_copy db 65)).
  { apply cno_bytes_of; [lia | rewrite PNL; lia |]. intros i Hi. rewrite <- SEG. apply CPY1. rewrite PNL in Hi. lia. }
  rewrite R1_1.
  eapply (kb_run B regs2 (Z_to_bv 64 0x13474) mem2 md1
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (getr regs 9) (getr regs 18) (Z_to_bv 64 (Z.of_nat (length db)))
         (Z_to_bv 64 d) (getr regs 21) /\
       getr R 1 = Z_to_bv 64 0x13488 /\ getr R 10 = Z_to_bv 64 d /\
       getr R 11 = Z_to_bv 64 (Z.of_nat (length db)) /\ getr R 12 = Z_to_bv 64 66 /\
       pc' = Z_to_bv 64 0x13e38 /\ m' = mem2));
    [exact (proj1 (kb_md B API _ _ _ _ HM1)) | exact (proj2 (kb_md B API _ _ _ _ HM1)) | |].
  { rewrite SEG. unfold rmk. destruct RS2 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21, R2_10.
    eapply Exec.evt_mono; [apply cno_s1|]. intros ms' ->. do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs2); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; reflexivity. }
  intros RR3 pc3 mem3 regs3 (RS3 & R3_1 & R3_10 & R3_11 & R3_12 & -> & ->) HG3.
  apply (RS_getr _ _ _ _ _ _ _ _ HG3) in RS3. rewrite <- HG3 in R3_1, R3_10, R3_11, R3_12.
  pose proof RS3 as (Q3_2 & _ & _ & _ & _ & _ & _ & QG3).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs3 (ALLOC_STACK + PAST_NUL_FRAME) CI1 INIT1 Q3_2 (QG3 4 ltac:(lia))
    ltac:(rewrite R3_1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK, PAST_NUL_FRAME; lia)
    ltac:(unfold CNO_STK, ALLOC_STACK, PAST_NUL_FRAME; lia)) as [SP3 PRE3].
  assert (DBLK1 : 0 < Z.of_nat (length db) ->
      exists pd k, In (pd, k) (blocks L1 A1) /\ pd <= d /\ d + Z.of_nat (length db) <= pd + k).
  { intros Hn. destruct (DBLK Hn) as (pd & k & Hin & H1 & H2). exists pd, k. split; [|lia].
    pose proof CI1 as (_ & _ & _ & _ & _ & BK1 & _). exact (proj1 (bk_base _ _ _ _ BK1 Hin)). }
  change (Z_to_bv 64 0x13e38) with (Z_to_bv 64 PAST_NUL).
  (* past_nul (d, n, 'B') *)
  apply (cno_pn PN _ _ _ _ _ _ _ _ _ d 66 db _ _ CI1 PRE3 SP3 R3_10 R3_11 R3_12 ltac:(lia) DBL
    (DBk _ _ _ _ _ _ _ _ CI1) DBLK1 RES1 RM2).
  intros L2 A2 regs4 mem4 md2 r2 RP4 INIT2 R4_10 Hr2 Hr2' CI2 RES2 KP2 CPY2.
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP4 RS3) as RS4.
  pose proof CI2 as ((HM2 & _) & _ & _ & _ & _ & (_ & INCL2 & _) & _).
  assert (Hr2b : In (r2, Z.of_nat (length db) + 18) (blocks L2 A2)) by (apply INCL2; left; reflexivity).
  assert (Hr1c : In (r1, Z.of_nat (length db) + 18) (blocks L2 A2)) by (apply INCL2; right; left; reflexivity).
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP2 Hr1b BR1 ltac:(lia) ltac:(lia) ltac:(rewrite PNL; lia)) as BR1b.
  assert (BR2 : Mem.bytes_at rsegs mem4 r2 (pn_copy db 66)).
  { apply cno_bytes_of; [lia | rewrite PNL; lia |]. intros i Hi. rewrite <- SEG. apply CPY2. rewrite PNL in Hi. lia. }
  (* to malloc (n + 18) *)
  rewrite R3_1.
  eapply (kb_run B regs4 (Z_to_bv 64 0x13488) mem4 md2
    (fun R pc' m' => RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (getr regs 18) (Z_to_bv 64 (Z.of_nat (length db)))
         (Z_to_bv 64 d) (Z_to_bv 64 (Z.of_nat (length db) + 18)) /\
       getr R 1 = Z_to_bv 64 0x13498 /\ getr R 10 = Z_to_bv 64 (Z.of_nat (length db) + 18) /\
       pc' = Z_to_bv 64 0x16594 /\ m' = mem4));
    [exact (proj1 (kb_md B API _ _ _ _ HM2)) | exact (proj2 (kb_md B API _ _ _ _ HM2)) | |].
  { rewrite SEG. unfold rmk. destruct RS4 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21, R4_10.
    eapply Exec.evt_mono; [apply cno_s2|]. intros ms' ->.
    rewrite (MState.unsigned_lit (Z.of_nat (length db))) by lia.
    do 3 eexists. split; [reflexivity|].
    split; [apply (RS_mk regs4); [exact PG | reflexivity ..]|].
    split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
  intros RR5 pc5 mem5 regs5 (RS5 & R5_1 & R5_10 & -> & ->) HG5.
  apply (RS_getr _ _ _ _ _ _ _ _ HG5) in RS5. rewrite <- HG5 in R5_1, R5_10.
  pose proof RS5 as (Q5_2 & _ & _ & _ & _ & _ & _ & QG5).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs5 ALLOC_STACK CI2 INIT2 Q5_2 (QG5 4 ltac:(lia))
    ltac:(rewrite R5_1; vm_compute; reflexivity) ltac:(unfold ALLOC_STACK; lia)
    ltac:(unfold CNO_STK, ALLOC_STACK; lia)) as [SP5 PRE5].
  apply (cno_malloc MALLOC MAL _ _ _ _ _ _ _ _ _ (Z.of_nat (length db) + 18) _ _ CI2 PRE5 SP5 R5_10 ltac:(lia)
    RES2 RM3).
  intros L3 A3 regs6 mem6 md3 w RP6 INIT3 R6_10 Hw Hw' CI3 RES3 KP3.
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP6 RS5) as RS6.
  pose proof CI3 as ((HM3 & _) & _ & _ & _ & _ & (_ & INCL3 & ND3) & FE3 & _).
  destruct (cno_nd3 _ _ _ ND3) as (Nwr2 & Nwr1 & Nr2r1).
  assert (Hwb : In (w, Z.of_nat (length db) + 18) (blocks L3 A3)) by (apply INCL3; left; reflexivity).
  assert (Hr2c : In (r2, Z.of_nat (length db) + 18) (blocks L3 A3)) by (apply INCL3; right; left; reflexivity).
  assert (Hr1d : In (r1, Z.of_nat (length db) + 18) (blocks L3 A3)) by (apply INCL3; right; right; left; reflexivity).
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP3 Hr1c BR1b ltac:(lia) ltac:(lia) ltac:(rewrite PNL; lia)) as BR1c.
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP3 Hr2b BR2 ltac:(lia) ltac:(lia) ltac:(rewrite PNL; lia)) as BR2c.
  pose proof (cno_E_disj _ _ _ _ _ _ _ _ r1 (Z.of_nat (length db) + 18) w (Z.of_nat (length db) + 18) CI3
    (or_intror (or_intror (or_introl eq_refl))) (or_introl eq_refl) (fun Eq => Nwr1 (eq_sym Eq))) as DJ1.
  pose proof (cno_E_disj _ _ _ _ _ _ _ _ r2 (Z.of_nat (length db) + 18) w (Z.of_nat (length db) + 18) CI3
    (or_intror (or_introl eq_refl)) (or_introl eq_refl) (fun Eq => Nwr2 (eq_sym Eq))) as DJ2.
  (* the third buffer: copy, zero tail; up to the first decode *)
  destruct (past_nul.pn_rw_sub mem6 (spZ regs - 96 + 8) 24 (spZ regs - 96 + 8) 24
    (cno_wr _ _ _ _ _ _ _ _ (spZ regs - 96 + 8) 24 CI3 ltac:(unfold CNO_STK, ALLOC_STACK; lia) ltac:(lia) ltac:(lia))
    ltac:(lia) ltac:(lia)) as [j0 J0].
  pose proof (cno_blk_wr _ _ _ _ _ _ HM3 Hwb) as WRw.
  assert (HRO : forall i, 0 <= i < Z.of_nat (length db) + 18 -> Mem.ro_addr rsegs (Mem.wa (w + i)) = false).
  { intros i Hi. unfold Mem.ro_addr. rewrite Mem.wa_unsigned by lia.
    destruct (find_segment rsegs (w + i) 1) as [seg|] eqn:F; [|reflexivity]. exfalso.
    rewrite Forall_forall in FE3. apply (FE3 _ (or_introl eq_refl) i ltac:(cbn [snd]; lia)).
    exact (past_nul.pn_seg_img B SEG _ _ F). }
  assert (HD : 0 < Z.of_nat (length db) -> Mem.bytes_at rsegs mem6 d db /\
      (d + Z.of_nat (length db) <= w \/ w + Z.of_nat (length db) + 18 <= d)).
  { intros Hn. destruct (DBLK Hn) as (pd & k & Hin & H1 & H2).
    pose proof CI3 as (_ & _ & _ & _ & _ & BK3 & _).
    destruct (bk_base _ _ _ _ BK3 Hin) as [Hc Hne].
    split.
    - apply cno_bytes_of; [pose proof (cno_base_pos _ _ Hin); lia | pose proof (HsKindB.block_low B API L3 A3 mem6 md3 pd k (k - 1) HM3 Hc ltac:(lia)); lia |].
      intros i Hi. rewrite <- SEG. exact (DBk _ _ _ _ _ _ _ _ CI3 i Hi).
    - assert (Hneq : (pd, k) <> (w, Z.of_nat (length db) + 18)) by (intros Eq; apply Hne; rewrite Eq; left; reflexivity).
      destruct (pw_two _ _ _ _ (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM3) Hc Hwb Hneq) as [D|D];
        unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
  pose proof CI3 as (_ & RA6 & _).
  rewrite R5_1.
  eapply (kb_run B regs6 (Z_to_bv 64 0x13498) mem6 md3
    (fun R pc' m' => (exists x21, RS R (Z_to_bv 64 r1) (Z_to_bv 64 r2) (Z_to_bv 64 w)
         (Z_to_bv 64 (Z.of_nat (length db))) (Z_to_bv 64 d) x21) /\
       getr R 1 = Z_to_bv 64 0x134e4 /\ getr R 10 = Z_to_bv 64 r1 /\
       getr R 11 = Z_to_bv 64 (spZ regs - 96 + 24) /\ pc' = Z_to_bv 64 0x14e90 /\
       Frame.munch [(w, w + Z.of_nat (length db) + 18); (spZ regs - 96 + 8, spZ regs - 96 + 32)] mem6 m' /\
       Frame.wmono rsegs mem6 m' /\ ro_agree rsegs m' /\ Mem.bytes_at rsegs m' w (db ++ repeat (Z_to_bv 8 0) 18)));
    [exact (proj1 (kb_md B API _ _ _ _ HM3)) | exact (proj2 (kb_md B API _ _ _ _ HM3)) | |].
  { rewrite SEG. unfold rmk. destruct RS6 as (P2 & P8 & P9 & P18 & P19 & P20 & P21 & PG).
    rewrite P2, P8, P9, P18, P19, P20, P21, R6_10.
    eapply Exec.evt_mono.
    - eapply cno_cz_r with (res := w) (n := Z.of_nat (length db)) (d := d) (db := db) (j0 := j0);
        [exact MEMCPY | exact MEMSET | | exact WRw | reflexivity | reflexivity | reflexivity | reflexivity | lia
        | reflexivity | lia | rewrite MState.unsigned_lit by lia; lia | rewrite MState.unsigned_lit by lia; lia
        | rewrite MState.unsigned_lit by lia; lia | exact HRO | exact HD | exact RA6].
      rewrite MState.unsigned_lit by lia. exact J0.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & -> & MU & WM & RA' & BY).
      do 3 eexists. split; [reflexivity|].
      split; [eexists; apply (RS_mk regs6); [exact PG | reflexivity ..]|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [f_equal; rewrite MState.unsigned_lit by lia; reflexivity|]. split; [reflexivity|].
      rewrite MState.unsigned_lit in MU by lia.
      split; [exact MU|]. split; [exact WM|]. split; [exact RA' | exact BY]. }
  intros RR7 pc7 mem7 regs7 ((x21 & RS7) & R7_1 & R7_10 & R7_11 & -> & MU7 & WM7 & RA7 & BW7) HG7.
  apply (RS_getr _ _ _ _ _ _ _ _ HG7) in RS7. rewrite <- HG7 in R7_1, R7_10, R7_11.
  assert (CI4 : CI [(w, Z.of_nat (length db) + 18); (r2, Z.of_nat (length db) + 18); (r1, Z.of_nat (length db) + 18)]
      L3 A3 mem7 md3 Lam peak cnt).
  { apply (cno_ci_munch _ _ _ _ _ _ _ _ _ _ CI3 MU7 WM7 RA7).
    intros x Hx. destruct (cno_not_out2 _ _ _ _ _ Hx) as [Hx1|Hx1]; [right | left; lia].
    exists w, (Z.of_nat (length db) + 18). split; [left; reflexivity|]. split; [lia|].
    intros a' k' Hin Eq.
    pose proof LG0 as (_ & _ & _ & _ & _ & LF0). rewrite Forall_forall in LF0.
    pose proof (proj1 (proj2 (LF0 (a', k') Hin))) as Hb. cbn [fst snd] in Hb. rewrite Eq in Hb.
    pose proof CI3 as (_ & _ & _ & _ & _ & BK3 & _). exact (proj2 (bk_base _ _ _ _ BK3 Hb) (or_introl eq_refl)). }
  assert (BR1d : Mem.bytes_at rsegs mem7 r1 (pn_copy db 65)).
  { apply (Frame.bytes_at_transport rsegs _ mem6 mem7 r1 _ BR1c MU7). rewrite PNL. cbn [Frame.disjoint_from].
    split; [lia | split; [lia | exact I]]. }
  assert (BR2d : Mem.bytes_at rsegs mem7 r2 (pn_copy db 66)).
  { apply (Frame.bytes_at_transport rsegs _ mem6 mem7 r2 _ BR2c MU7). rewrite PNL. cbn [Frame.disjoint_from].
    split; [lia | split; [lia | exact I]]. }
  pose proof RS7 as (Q7_2 & _ & _ & _ & _ & _ & _ & QG7).
  destruct (cno_pre _ _ _ _ _ _ _ _ regs7 DEC_STACK CI4 INIT3 Q7_2 (QG7 4 ltac:(lia))
    ltac:(rewrite R7_1; vm_compute; reflexivity) ltac:(unfold DEC_STACK, ALLOC_STACK; lia)
    ltac:(unfold CNO_STK, DEC_STACK, ALLOC_STACK; lia)) as [SP7 PRE7].
  assert (RM4 : room_slots (sb_malloc (sb_malloc (sb_malloc bnd (Z.of_nat (length db) + 18))
      (Z.of_nat (length db) + 18)) (Z.of_nat (length db) + 18)) (Z.of_nat (length db) / 4 * 3 + 3 + 16)).
  { destruct (b64_dec (zs db)); cbn [opt_ok dec_ops app hs_room] in ROOM; exact (proj1 ROOM). }
  change (Z_to_bv 64 0x14e90) with (Z_to_bv 64 PRESET_BASE64_DECODE).
  (* the first decode *)
  apply (cno_dec DEC _ _ _ _ _ _ _ _ _ r1 24 db ([Z_to_bv 8 (65 mod 256); Z_to_bv 8 65] ++ repeat (Z_to_bv 8 0) 15)
    r1 (Z.of_nat (length db) + 18) _ _ CI4 PRE7 SP7 R7_10 R7_11 ltac:(lia) BR1d NZ
    ltac:(rewrite length_app, repeat_length; cbn [length]; lia) DBL ltac:(right; right; left; reflexivity)
    ltac:(lia) ltac:(lia) ltac:(lia) RES3 RM4).
  intros L4 A4 regs8 mem8 md4 RP8 INIT4 KP4 STK4 ARMS. specialize (INIT4 INIT3).
  pose proof (RS_pres _ _ _ _ _ _ _ _ RP8 RS7) as RS8.
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP4 Hr2c BR2d ltac:(lia) ltac:(lia) ltac:(rewrite PNL; lia)) as BR2e.
  pose proof (cno_keep_bytes _ _ _ _ _ _ _ _ KP4 Hwb BW7 ltac:(lia) ltac:(lia)
    ltac:(rewrite length_app, repeat_length; lia)) as BWe.
  rewrite R7_1.
  destruct ARMS as [(Dn & R8_10 & CI5 & RES4) | (bs & q1 & Ds & R8_10 & Hq1 & Hq1' & CI5 & BQ1 & BL1 & RES4)].
  - rewrite Dn in ROOM |- *. cbn [opt_ok dec_ops dec_free_ops app hs_room hs_rb] in ROOM |- *.
    destruct ROOM as (_ & RM5 & RM6 & _).
    exact (cno_rest_none DEC FF FREE FRE db _ _ L4 A4 regs8 mem8 md4 _ r1 r2 w _ _ _ _ eq_refl eq_refl Dn NZ DBL HC
      CI5 INIT4 R8_10 RS8 BR2e BWe RES4 RM5 RM6).
  - rewrite Ds in ROOM |- *. cbn [opt_ok dec_ops dec_free_ops app hs_room hs_rb] in ROOM |- *.
    destruct ROOM as (_ & RM5 & RM6 & _).
    exact (cno_rest_some DEC BCMP FF FREE FRE db bs _ _ L4 A4 regs8 mem8 md4 _ r1 r2 w q1 _ _ _ _ eq_refl eq_refl Ds NZ
      DBL HC CI5 INIT4 R8_10 (conj Hq1 Hq1') RS8 BQ1 BL1 BR2e BWe RES4 RM5 RM6).
Qed.

End C.

(* Every block the function makes is given back: the bound returns. *)
Lemma cno_nor_rb : forall b n ok, hs_rb b (nor_ops n ok) = b.
Proof.
  intros [l y c] n [|]; unfold nor_ops, dec_ops, dec_free_ops; cbn [app hs_rb];
    unfold sb_malloc, sb_free; cbn [sb_live sb_bytes sb_cap]; f_equal; lia.
Qed.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Theorem check_no_overread_holds :
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B MR -> ctx_owned B API ->
  past_nul_contract B API -> malloc_contract B API -> memcpy_contract -> memset_contract ->
  preset_base64_decode_contract B API sb_form -> bcmp_contract -> fuzz_free_contract B API sb_form ->
  free_contract B API ->
  check_no_overread_contract B API.
Proof.
  intros SEG MAL FRE ERR GF AX CO PN MALLOC MEMCPY MEMSET DEC BCMP FF FREE.
  unfold check_no_overread_contract.
  intros L A regs mem md d db bnd Lam peak cnt PRE R10 R11 DB NZ DBL DBLK NW LG HC RA ROK ROOM.
  pose proof (cno_main B API SEG ERR GF AX CO L A regs mem md Lam peak cnt PRE LG PN MALLOC MAL MEMCPY MEMSET DEC BCMP FF
    FREE FRE d db bnd R10 R11 DB NZ DBL DBLK HC RA ROK ROOM) as H.
  rewrite cno_nor_rb in H. exact H.
Qed.

End T.
