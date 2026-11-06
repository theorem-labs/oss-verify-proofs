From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec strlen_c bcmp_c check_as_written_runs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpecFacts.
Import ListNotations.
Open Scope Z_scope.

(* check_as_written (check_2, plain, 0x135ec): the four machine runs of check_as_written_runs.v joined by the
   contracts of malloc (two calls), free (a call and the tail call) and the strlen and bcmp contracts inside the runs. *)

Lemma caw_six_len : forall six, Z.of_nat (length (six_bytes six)) <= Z.of_nat (length six) / 4 * 3 + 2.
Proof.
  fix IH 1. intros [|a [|b [|c [|d r]]]]; cbn [six_bytes length]; try (Z.div_mod_to_equations; lia).
  specialize (IH r). Z.div_mod_to_equations. lia.
Qed.

Lemma caw_dec_len : forall tb bs, b64_dec tb = Some bs -> Z.of_nat (length bs) <= Z.of_nat (length tb) / 4 * 3 + 2.
Proof.
  intros tb bs H. unfold b64_dec in H.
  destruct (b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
  destruct ((pad <=? 2) && six_tail_ok six); [|discriminate]. injection H as <-.
  destruct (WriterSpecFacts.scan_inv tb 0 [] six pad E) as [H1 _]. cbn [length] in H1.
  pose proof (caw_six_len six). Z.div_mod_to_equations. lia.
Qed.

Lemma caw_slack : forall segs m a r, 0 <= a -> a + Z.of_nat r <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat r -> exists b, mrd segs m (wa (a + i)) = Some b) ->
  exists bs, length bs = r /\ bytes_at segs m a bs.
Proof.
  intros segs m a r. revert a. induction r as [|r IH]; intros a H0 H1 H.
  - exists []. split; [reflexivity|]. apply bytes_at_nil. lia.
  - destruct (H 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & Hbs).
    { intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn [length]; rewrite Hl; reflexivity|].
    change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
    + split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. exact Hb.
    + cbn [length]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact Hbs.
Qed.

Lemma caw_bytes_keep : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mrd segs m' (wa (a + i)) = mrd segs m (wa (a + i))) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (H1 & H2 & H) K. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite K by lia. exact (H i Hi).
Qed.

Lemma caw_not_out2 : forall lo1 hi1 lo2 hi2 x, ~ outside [(lo1, hi1); (lo2, hi2)] x ->
  lo1 <= x < hi1 \/ lo2 <= x < hi2.
Proof.
  intros lo1 hi1 lo2 hi2 x H. cbn [outside] in H.
  destruct (Z_le_gt_dec lo1 x); destruct (Z_lt_ge_dec x hi1); destruct (Z_le_gt_dec lo2 x);
    destruct (Z_lt_ge_dec x hi2); try (left; lia); try (right; lia);
    exfalso; apply H; (split; [lia|]); (split; [lia | exact I]).
Qed.

Lemma caw_align : forall x, x + (- x) mod 8 = 8 * ((x + 7) / 8).
Proof. intros x. Z.div_mod_to_equations. lia. Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL01 YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger KindBGlue HState check_as_written_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB past_nul check_reject_clean_starved.
Local Open Scope Z_scope.

Lemma caw_mbyte_eq : forall segs (m m' : word -> option byte) a, (forall x, m' x = m x) ->
  mbyte segs m' a = mbyte segs m a.
Proof. intros segs m m' a E. unfold mbyte. rewrite E. reflexivity. Qed.

Lemma caw_mid_uniq : forall (l1 l2 r1 r2 : list (Z * Z)) x, pairwise ranges_disjoint (l1 ++ x :: l2) -> 0 < snd x ->
  l1 ++ x :: l2 = r1 ++ x :: r2 -> l1 ++ l2 = r1 ++ r2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 r1 r2 x P Hx E; destruct r1 as [|z r1]; cbn [app] in *.
  - injection E as E. exact E.
  - injection E as E1 E2. subst z. exfalso. destruct P as [P _].
    specialize (P x ltac:(rewrite E2; apply in_or_app; right; left; reflexivity)). unfold ranges_disjoint in P. lia.
  - injection E as E1 E2. subst y. exfalso. destruct P as [P _].
    specialize (P x ltac:(apply in_or_app; right; left; reflexivity)). unfold ranges_disjoint in P. lia.
  - injection E as E1 E2. subst z. f_equal. exact (IH l2 r1 r2 x (proj2 P) Hx E2).
Qed.

Lemma caw_fst_unique : forall {X Y : Type} (l : list (X * Y)) x a c,
  List.NoDup (map fst l) -> In (x, a) l -> In (x, c) l -> a = c.
Proof.
  intros X Y l. induction l as [|[y d] l IH]; intros x a c ND Ha Hc; [destruct Ha|].
  cbn [map fst] in ND. inversion ND as [|? ? Hn ND']; subst.
  destruct Ha as [Ea|Ha]; destruct Hc as [Ec|Hc].
  - inversion Ea; inversion Ec; subst; reflexivity.
  - inversion Ea; subst. exfalso. apply Hn. apply (in_map fst) in Hc. exact Hc.
  - inversion Ec; subst. exfalso. apply Hn. apply (in_map fst) in Ha. exact Ha.
  - exact (IH x a c ND' Ha Hc).
Qed.

Ltac caw_k k :=
  let H := fresh in
  assert (H : k = 3 \/ k = 4 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia;
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]].

Section Q.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Lemma caw_blk : forall L A mem md a k, MR L A mem md -> In (a, k) (blocks L A) ->
  Mem.wr_at rsegs mem a k /\ (forall x, a <= x < a + k -> ~ owned B L A x) /\ 4096 <= a /\ a + k <= alloc_ceiling.
Proof.
  intros L A mem md a k HM Hin. destruct (HsKindB.in_blocks L A a k Hin) as (q & Hq & ->).
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq) as RNG. pose proof alloc_ceiling_lt as Hc.
  split; [|split; [|exact RNG]].
  - split; [lia|]. split; [lia|]. intros i Hi.
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k i HM Hq Hi) as ((bb & Hb) & _).
    unfold wview, Mem.wa. rewrite Hb. discriminate.
  - intros x Hx. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k (x - ptr_addr L q) HM Hq ltac:(lia)) as (_ & _ & _ & No).
    replace (ptr_addr L q + (x - ptr_addr L q)) with x in No by lia. exact No.
Qed.

Lemma caw_post_hi : errno_addr B + 4 <= alloc_ceiling ->
  forall K L A regs mem md (E : Z -> Prop) L' A' regs' mem' md' a,
  MR L A mem md -> call_post_k B MR K L A regs mem md E L' A' regs' mem' md' ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> ~ E a ->
  mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
  (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros ERR K L A regs mem md E L' A' regs' mem' md' a HM CP Ha Hs He.
  pose proof CP as (HM' & _ & _ & _ & _ & _ & _ & HF & _).
  apply HF; [left; exact Ha | | | | exact He].
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
  - unfold scratch_k. lia.
Qed.

Lemma caw_mid_eq : img_low B -> forall K sp L A mem md E L' A' mem' md' (mem'' : word -> option byte),
  kb_mid B API K sp L A mem md E L' A' mem' md' -> (forall x, mem'' x = mem' x) ->
  kb_mid B API K sp L A mem md E L' A' mem'' md'.
Proof.
  intros IL K sp L A mem md E L' A' mem' md' mem'' M EQ.
  apply (kb_mid_E B API _ _ _ _ _ _ (fun a => E a \/ False)); [|intros a [Ha|[]]; exact Ha].
  apply (kb_mid_tail B API IL K sp L A mem md E L' A' mem' md' mem'' [] (fun _ => False) M).
  - intros x _. exact (EQ x).
  - intros x Hx. unfold wview in *. rewrite EQ. exact Hx.
  - intros x Hx. rewrite EQ. exact Hx.
  - intros. exact I.
  - intros. exact I.
  - intros. exact I.
Qed.

Lemma caw_ro_heap : ms_segs B = rsegs -> forall m m' W, ro_agree rsegs m -> Frame.munch W m m' ->
  (forall x, ~ Frame.outside W x -> ~ in_img B x) -> ro_agree rsegs m'.
Proof.
  intros SEG m m' W RA MU HW a Ha. unfold Mem.mrd. rewrite (MU a); [exact (RA a Ha)|].
  destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. exfalso. apply (HW _ Ho).
  unfold Mem.ro_addr in Ha. destruct (find_segment rsegs (bv_unsigned a) 1) as [seg|] eqn:F; [|discriminate].
  exact (past_nul.pn_seg_img B SEG _ _ F).
Qed.

Lemma caw_ledger : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] ->
  forall L A mem md L' A' mem' Lam peak cnt fail,
  MR L A mem md -> ledger B L A mem Lam peak cnt fail -> blocks L' A' = blocks L A -> keeps B L A mem mem' 0 ->
  (forall x, in_globals [(G_FAIL, 8); (G_LIVE, 24)] x -> mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x) ->
  ledger B L' A' mem' Lam peak cnt fail.
Proof.
  intros GF L A mem md L' A' mem' Lam peak cnt fail HM LG BL KP KG.
  assert (WK : forall a v, (forall k, 0 <= k < 8 -> in_globals [(G_FAIL, 8); (G_LIVE, 24)] (a + k)) ->
     word_mem (ms_segs B) mem a v -> word_mem (ms_segs B) mem' a v).
  { intros a v Hg Hw. apply (word_mem_frame (ms_segs B) mem mem' a v Hw). intros k Hk. apply KG. exact (Hg k Hk). }
  destruct LG as (AW & L1 & L2 & L3 & ND & FA). destruct AW as (W1 & W2 & W3 & W4).
  split.
  { split; [eapply WK; [|exact W1]; intros k Hk; exists G_LIVE, 24; split; [right; left; reflexivity | unfold G_LIVE; lia]|].
    split; [eapply WK; [|exact W2]; intros k Hk; exists G_LIVE, 24;
      split; [right; left; reflexivity | unfold G_LIVE, G_PEAK; lia]|].
    split; [eapply WK; [|exact W3]; intros k Hk; exists G_LIVE, 24;
      split; [right; left; reflexivity | unfold G_LIVE, G_COUNT; lia]|].
    eapply WK; [|exact W4]; intros k Hk; exists G_FAIL, 8; split; [left; reflexivity | lia]. }
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact ND|].
  eapply Forall_impl; [|exact FA]. intros [a k] (Hk & Hin & Hw & Hni). cbn [fst snd] in *.
  split; [exact Hk|]. split; [rewrite BL; exact Hin|]. split; [|exact Hni].
  pose proof (HsKindB.block_low B API L A mem md (a - 16) (k + 16) 0 HM Hin ltac:(lia)) as B0.
  apply (word_mem_frame (ms_segs B) mem mem' (a - 16) k Hw). intros j Hj.
  exact (KP (a - 16) (k + 16) j Hin ltac:(lia) ltac:(lia)).
Qed.

End Q.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Theorem check_as_written_holds :
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B MR -> ctx_owned B API ->
  block_slack_present B API ->
  strlen_contract -> bcmp_contract -> malloc_contract B API -> free_contract B API ->
  check_as_written_contract B API.
Proof.
  intros SEG MAL FRE ERR GF AX CO BSP SLEN BCMP MALLOC FREE.
  unfold check_as_written_contract.
  intros L A regs mem md t tb slack bd l bnd Lam peak cnt fail PRE R10 R11 R12 TB NZ SL TBL NW TBLK CAW BDL LG RA ROK
    RM1 RM2.
  unfold b64_alloc_bound in *.
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  assert (EK : ALLOC_STACK + CAW_FRAME = 8240) by reflexivity.
  assert (EA : ALLOC_STACK = 8192) by reflexivity.
  rewrite EK in HAC.
  destruct (kb_md B API L A mem md HM) as [Hh Hl0].
  assert (IL : img_low B).
  { apply (img_low_of_check B 0x55000); [unfold img_check; rewrite SEG; vm_compute; reflexivity | lia]. }
  assert (STK : Frame.stk rsegs mem (spZ regs - 8240) (spZ regs)).
  { pose proof (kb_stk B API IL (ALLOC_STACK + CAW_FRAME) L A regs mem md PRE ltac:(rewrite EK; lia)) as K.
    rewrite SEG, EK in K. exact K. }
  assert (RA0 : ro_agree rsegs mem) by (rewrite <- SEG; exact RA).
  pose proof TBLK as (pt & kt & Hpt & Hpt1 & Hpt2).
  pose proof (Mem.bytes_at_bound _ _ _ _ TB) as TBB. rewrite length_app in TBB. cbn [length] in TBB.
  destruct (caw_blk B API L A mem md pt kt HM Hpt) as (_ & _ & BKR1 & BKR2).
  assert (TW : t + Z.of_nat (length tb) + 1 + Z.of_nat (length slack) <= spZ regs - 8240).
  { destruct (check_reject_clean_starved.crs_window (spZ regs) (ALLOC_STACK + CAW_FRAME) t
      (t + Z.of_nat (length tb) + 1 + Z.of_nat (length slack)) NW ltac:(lia) ltac:(rewrite EK; lia)) as [H|H];
      rewrite EK in *; lia. }
  assert (HLB : 0 <= l < 2 ^ 64 /\ 0 <= bd < 2 ^ 64).
  { destruct CAW as [(_ & BD0 & L0) | (bs & DEC & BDN & EL & _)]; [rewrite BD0, L0; lia|].
    pose proof (caw_dec_len _ _ DEC) as DL. unfold zs in DL. rewrite length_map in DL.
    destruct (BDL BDN) as (kb & Hkb & _).
    pose proof LG as (_ & _ & _ & _ & _ & LGF). rewrite Forall_forall in LGF.
    destruct (LGF (bd, kb) Hkb) as (Hk0 & Hinb & _). cbn [fst snd] in Hk0, Hinb.
    destruct (caw_blk B API L A mem md _ _ HM Hinb) as (_ & _ & Rb1 & Rb2). lia. }
  assert (TB0 : Mem.bytes_at rsegs mem t (tb ++ [Z_to_bv 8 0])).
  { pose proof TB as TB'. rewrite SEG in TB'.
    replace (tb ++ Z_to_bv 8 0 :: slack) with ((tb ++ [Z_to_bv 8 0]) ++ slack) in TB'
      by (rewrite <- app_assoc; reflexivity).
    apply Mem.bytes_at_app in TB'. exact (proj1 TB'). }
  (* run 1: prologue and strlen, up to the first malloc call *)
  eapply (kb_run B regs (Z_to_bv 64 CHECK_AS_WRITTEN) mem md
    (fun R pc' m' => getr R 1 = Z_to_bv 64 0x13628 /\ getr R 2 = Z_to_bv 64 (spZ regs + -48) /\
       getr R 8 = getr regs 12 /\ getr R 9 = getr regs 11 /\
       getr R 10 = Z_to_bv 64 (Z.of_nat (length tb) / 4 * 3 + 3) /\
       getr R 18 = getr regs 18 /\ getr R 19 = getr regs 10 /\
       (forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr R (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)) /\
       pc' = Z_to_bv 64 0x16594 /\
       (exists junk, Step.rw_cells rsegs m' (spZ regs + -48)
         [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]) /\
       Frame.munch [(spZ regs + -48, spZ regs)] mem m' /\ Frame.wmono rsegs mem m'));
    [exact Hh | exact Hl0 | |].
  { rewrite SEG. unfold CHECK_AS_WRITTEN, rmk. eapply Exec.evt_mono.
    - eapply (run1 SLEN) with (lo := spZ regs - 8240) (tb := tb) (slack := slack).
      + exact STK.
      + unfold spZ in *. lia.
      + lia.
      + rewrite R10, MState.unsigned_lit by lia. rewrite SEG in TB. exact TB.
      + exact NZ.
      + rewrite R10, MState.unsigned_lit by lia. exact SL.
      + rewrite R10, MState.unsigned_lit by lia. lia.
      + lia.
      + exact RA0.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & junk & -> & FR & MU & WM).
      do 3 eexists. split; [reflexivity|].
      do 7 (split; [reflexivity|]).
      split; [intros k Hk; caw_k k; reflexivity|].
      split; [reflexivity|].
      split; [exists junk; exact FR|].
      split; [exact MU | exact WM]. }
  intros RR1 pc1 mem1 regs1 (R1_1 & R1_2 & R1_8 & R1_9 & R1_10 & R1_18 & R1_19 & R1_S & -> & (junk & FR1) & MU1 & WM1) HG1.
  rewrite <- HG1 in R1_1, R1_2, R1_8, R1_9, R1_10, R1_18, R1_19.
  assert (S1 : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs1 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k))
    by (intros k Hk; rewrite HG1; exact (R1_S k Hk)).
  clear R1_S.
  assert (SP1 : spZ regs1 = spZ regs - 48).
  { unfold spZ at 1. rewrite R1_2, MState.unsigned_lit by lia. lia. }
  assert (MU1' : Frame.munch [(spZ regs - 48, spZ regs)] mem mem1).
  { replace (spZ regs - 48) with (spZ regs + -48) by lia. exact MU1. }
  assert (PRE1 : call_pre_k B MR ALLOC_STACK L A regs1 mem1 md).
  { apply (kb_pre_A B API (ALLOC_STACK + CAW_FRAME) 48 ALLOC_STACK L A regs mem md regs1 mem1
      [(spZ regs - 48, spZ regs)] PRE).
    - lia.
    - lia.
    - lia.
    - exact SP1.
    - rewrite SP1. Z.div_mod_to_equations. lia.
    - exact (S1 4 ltac:(lia)).
    - rewrite R1_1. vm_compute. reflexivity.
    - exact MU1'.
    - rewrite SEG. exact WM1.
    - intros x Hx Hx'. apply outside_one. lia.
    - intros x Hx Ho. apply outside_one. lia. }
  assert (RA1 : ro_agree rsegs mem1) by exact (cw_ro_agree_hi mem mem1 _ _ RA0 MU1 ltac:(lia)).
  (* malloc (n / 4 * 3 + 3) *)
  rewrite <- MAL.
  eapply SR_bind.
  { apply (MALLOC L A regs1 mem1 md (Z.of_nat (length tb) / 4 * 3 + 3) bnd).
    - apply (proj2 (call_pre_k_alloc B MR L A regs1 mem1 md)). exact PRE1.
    - rewrite SEG. exact RA1.
    - exact R1_10.
    - exact ROK.
    - exact RM1. }
  intros c1 (L1 & A1 & regs2 & mem2 & md1 & w & -> & CP1 & R2_10 & Hw0 & Hw16 & FBw & (b1 & b2 & BL1' & BL1) &
    BK1 & RA2 & GK2 & UB1 & INIT1 & LEN1 & RES1).
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP1) as [MD1 RP1].
  pose proof CP1 as (HM2 & HWF2 & HBD2 & _ & HPA1 & _ & _ & _ & _ & _).
  rewrite SEG in RA2.
  assert (INW : In (w, Z.of_nat (length tb) / 4 * 3 + 3) (blocks L1 A1)).
  { rewrite BL1'. apply in_or_app. right. left. reflexivity. }
  destruct (caw_blk B API L1 A1 mem2 md1 _ _ HM2 INW) as (_ & _ & Rw1 & Rw2).
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM2) as DISJ1. rewrite BL1' in DISJ1.
  assert (OLDw : forall a k, In (a, k) (blocks L A) -> a + k <= w \/ w + (Z.of_nat (length tb) / 4 * 3 + 3) <= a).
  { intros a k Hin. rewrite BL1 in Hin. destruct (past_nul.pn_pairwise_mid _ _ _ _ _ DISJ1 Hin) as [Hd|Hd];
      unfold ranges_disjoint in Hd; cbn [fst snd] in Hd; lia. }
  assert (SUB1 : forall y, In y (blocks L A) -> In y (blocks L1 A1)).
  { intros y Hy. rewrite BL1'. rewrite BL1 in Hy. exact (past_nul.pn_in_mid _ _ _ _ Hy). }
  assert (MA1 : kb_mid B API (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md (fun _ => False) L A mem1 md).
  { apply (kb_mid_A B API IL (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md mem1 [(spZ regs - 48, spZ regs)]
      (fun _ => False) HM HWF HBD).
    - intros a [Ha|Ha]; [apply HWS; exact Ha | apply HER; exact Ha].
    - exact MU1'.
    - rewrite SEG. exact WM1.
    - intros x Hx Hs _. apply outside_one. rewrite EK in Hs. lia.
    - intros x Hx _. apply outside_one. lia. }
  assert (M1 : kb_mid B API (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md (fun a => False \/ False) L1 A1 mem2 md1).
  { apply (kb_mid_seqAX B API _ _ _ _ _ _ _ _ ALLOC_STACK (spZ regs1) (fun _ => False) _ _ _ _ MA1 MD1); lia. }
  assert (FR2 : Step.rw_cells rsegs mem2 (spZ regs + -48)
      [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (check_reject_clean_starved.crs_rw_keep mem1 mem2 (spZ regs + -48) _ ltac:(lia) FR1). intros a Ha.
    cbn [cells_size csize Nat.add] in Ha. rewrite <- SEG.
    exact (proj1 (caw_post_hi B API ERR _ _ _ _ _ _ _ _ _ _ _ _ a (proj1 PRE1) CP1 ltac:(lia) ltac:(rewrite SP1; lia)
      ltac:(cbv beta; tauto))). }
  assert (S2 : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs2 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)).
  { intros k Hk. rewrite (RP1 k ltac:(unfold callee_saved; lia)). exact (S1 k Hk). }
  assert (Q2_2 : getr regs2 2 = Z_to_bv 64 (spZ regs + -48)).
  { rewrite <- R1_2. exact (RP1 2 ltac:(unfold callee_saved; lia)). }
  assert (Q2_8 : getr regs2 8 = Z_to_bv 64 l).
  { rewrite <- R12, <- R1_8. exact (RP1 8 ltac:(unfold callee_saved; lia)). }
  assert (Q2_9 : getr regs2 9 = Z_to_bv 64 bd).
  { rewrite <- R11, <- R1_9. exact (RP1 9 ltac:(unfold callee_saved; lia)). }
  assert (Q2_18 : getr regs2 18 = getr regs 18).
  { rewrite <- R1_18. exact (RP1 18 ltac:(unfold callee_saved; lia)). }
  assert (Q2_19 : getr regs2 19 = Z_to_bv 64 t).
  { rewrite <- R10, <- R1_19. exact (RP1 19 ltac:(unfold callee_saved; lia)). }
  (* the text and an alignment slack are readable in mem2: the text lies in its block, the slack in the block or
     in the block's slack *)
  assert (KP2 : keeps B L A mem mem2 0).
  { exact (check_reject_clean_starved.crs_keep_of_mid B API _ _ _ _ _ _ _ _ _ _ _ M1 (fun q k H _ => UB1 q k H)). }
  pose proof (caw_align (t + Z.of_nat (length tb) + 1)) as AL.
  pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length tb) + 1)) 8 ltac:(lia)) as Hr.
  assert (AL2 : 8 * ((t + Z.of_nat (length tb) + 1 + 7) / 8) <= 8 * ((pt + kt + 7) / 8)).
  { apply Z.mul_le_mono_nonneg_l; [lia | apply Z.div_le_mono; lia]. }
  assert (SLK2 : exists slk, length slk = Z.to_nat ((- (t + Z.of_nat (length tb) + 1)) mod 8) /\
      Mem.bytes_at rsegs mem2 (t + Z.of_nat (length tb) + 1) slk).
  { apply caw_slack; [lia | lia |].
    intros i Hi. rewrite Z2Nat.id in Hi by lia.
    remember (t + Z.of_nat (length tb) + 1 + i) as x eqn:Ex.
    destruct (Z_lt_le_dec x (pt + kt)) as [Hx|Hx].
    - pose proof TB as (_ & _ & HB).
      destruct (nth_error (tb ++ Z_to_bv 8 0 :: slack) (Z.to_nat (x - t))) as [b|] eqn:Eb.
      2: { apply nth_error_None in Eb. rewrite length_app in Eb. cbn [length] in Eb. lia. }
      pose proof (HB (Z.to_nat (x - t)) ltac:(rewrite length_app; cbn [length]; lia)) as HBx.
      rewrite Eb, Z2Nat.id in HBx by lia. replace (t + (x - t)) with x in HBx by lia.
      assert (E2 : mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem x).
      { replace x with (pt + (x - pt)) by lia. exact (KP2 pt kt (x - pt) Hpt ltac:(lia) ltac:(lia)). }
      exists b. change (Mem.mrd rsegs mem2 (Mem.wa x)) with (mbyte rsegs mem2 x). rewrite <- SEG, E2. exact HBx.
    - destruct (BSP L1 A1 mem2 md1 pt kt x HM2 (SUB1 _ Hpt) ltac:(lia)) as [b Hb].
      exists b. unfold Mem.mrd, Mem.wa. rewrite Hb. reflexivity. }
  destruct SLK2 as (slk & Hslk & BS2).
  assert (TB2 : Mem.bytes_at rsegs mem2 t (tb ++ Z_to_bv 8 0 :: slk)).
  { replace (tb ++ Z_to_bv 8 0 :: slk) with ((tb ++ [Z_to_bv 8 0]) ++ slk) by (rewrite <- app_assoc; reflexivity).
    apply Mem.bytes_at_app. split.
    - apply (caw_bytes_keep rsegs mem mem2 t _ TB0). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
      change (mbyte rsegs mem2 (t + i) = mbyte rsegs mem (t + i)).
      rewrite <- SEG. replace (t + i) with (pt + (t + i - pt)) by lia.
      exact (KP2 pt kt (t + i - pt) Hpt ltac:(lia) ltac:(lia)).
    - rewrite length_app. cbn [length].
      replace (t + Z.of_nat (length tb + 1)) with (t + Z.of_nat (length tb) + 1) by lia. exact BS2. }
  (* run 2: strlen again, up to the second malloc call *)
  rewrite R1_1.
  eapply (kb_run B regs2 (Z_to_bv 64 0x13628) mem2 md1
    (fun R pc' m' => getr R 1 = Z_to_bv 64 0x13644 /\ getr R 2 = getr regs2 2 /\ getr R 8 = getr regs2 8 /\
       getr R 9 = getr regs2 9 /\ getr R 10 = Z_to_bv 64 (Z.max (Z.of_nat (length tb)) 1) /\
       getr R 18 = Z_to_bv 64 w /\ getr R 19 = getr regs2 19 /\
       (forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr R (Z_to_bv 5 k) = getr regs2 (Z_to_bv 5 k)) /\
       pc' = Z_to_bv 64 0x16594 /\ (forall x, m' x = mem2 x)));
    [exact (proj1 (kb_md B API _ _ _ _ HM2)) | exact (proj2 (kb_md B API _ _ _ _ HM2)) | |].
  { rewrite SEG. unfold rmk. rewrite R2_10. eapply Exec.evt_mono.
    - eapply (run2 SLEN) with (w := w) (tb := tb) (slack := slk).
      + lia.
      + rewrite Q2_19, MState.unsigned_lit by lia. exact TB2.
      + exact NZ.
      + rewrite Q2_19, MState.unsigned_lit by lia. rewrite Hslk. lia.
      + lia.
      + exact RA2.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & -> & EQ).
      do 3 eexists. split; [reflexivity|].
      do 7 (split; [reflexivity|]).
      split; [intros k Hk; caw_k k; reflexivity|].
      split; [reflexivity | exact EQ]. }
  intros RR3 pc3 mem3 regs3 (R3_1 & R3_2 & R3_8 & R3_9 & R3_10 & R3_18 & R3_19 & R3_S & -> & EQ3) HG3.
  rewrite <- HG3 in R3_1, R3_2, R3_8, R3_9, R3_10, R3_18, R3_19.
  assert (S3 : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs3 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k))
    by (intros k Hk; rewrite HG3, (R3_S k Hk); exact (S2 k Hk)).
  clear R3_S.
  assert (SP3 : spZ regs3 = spZ regs - 48).
  { unfold spZ at 1. rewrite R3_2, Q2_2, MState.unsigned_lit by lia. lia. }
  assert (M1e : kb_mid B API (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md (fun a => False \/ False) L1 A1 mem3 md1)
    by exact (caw_mid_eq B API IL _ _ _ _ _ _ _ _ _ _ _ _ M1 EQ3).
  pose proof M1e as (HM3 & _ & _ & _ & _ & _ & _ & _ & S1w).
  assert (PRE3 : call_pre_k B MR ALLOC_STACK L1 A1 regs3 mem3 md1).
  { unfold call_pre_k.
    split; [exact HM3|]. split; [exact HWF2|]. split; [exact HBD2|].
    split; [rewrite R3_1; vm_compute; reflexivity|].
    split; [rewrite SP3; Z.div_mod_to_equations; lia|].
    split; [rewrite SP3; lia|].
    split; [rewrite SP3; lia|].
    split; [intros a Ha; apply S1w; left; rewrite SP3 in Ha; rewrite EK; lia|].
    split; [transitivity (getr regs 4); [exact (S3 4 ltac:(lia)) | exact HTP]|].
    split; [intros a Ha; apply S1w; right; exact Ha|].
    intros Hf. rewrite INIT1 in Hf. discriminate. }
  assert (RA3 : ro_agree rsegs mem3) by exact (cw_ro_agree_eq mem2 mem3 EQ3 RA2).
  (* malloc (max n 1) *)
  rewrite <- MAL.
  eapply SR_bind.
  { apply (MALLOC L1 A1 regs3 mem3 md1 (Z.max (Z.of_nat (length tb)) 1)
      (sb_malloc bnd (Z.of_nat (length tb) / 4 * 3 + 3))).
    - apply (proj2 (call_pre_k_alloc B MR L1 A1 regs3 mem3 md1)). exact PRE3.
    - rewrite SEG. exact RA3.
    - exact R3_10.
    - exact RES1.
    - exact RM2. }
  intros cf2 (L2 & A2 & regs4 & mem4 & md2 & s & -> & CP2 & R4_10 & Hs0 & Hs16 & FBs & (c1 & c2 & BL2' & BL2) &
    BK2 & RA4 & GK4 & UB2 & INIT2 & LEN2 & RES2).
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP2) as [MD2 RP2].
  pose proof CP2 as (HM4 & HWF4 & HBD4 & _ & HPA2 & _ & _ & _ & _ & _).
  rewrite SEG in RA4.
  assert (INS : In (s, Z.max (Z.of_nat (length tb)) 1) (blocks L2 A2)).
  { rewrite BL2'. apply in_or_app. right. left. reflexivity. }
  destruct (caw_blk B API L2 A2 mem4 md2 _ _ HM4 INS) as (WRs & NOWs & Rs1 & Rs2).
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM4) as DISJ2. rewrite BL2' in DISJ2.
  assert (SUB2 : forall y, In y (blocks L1 A1) -> In y (blocks L2 A2)).
  { intros y Hy. rewrite BL2'. rewrite BL2 in Hy. exact (past_nul.pn_in_mid _ _ _ _ Hy). }
  assert (OLDs1 : forall a k, In (a, k) (blocks L1 A1) -> a + k <= s \/ s + Z.max (Z.of_nat (length tb)) 1 <= a).
  { intros a k Hin. rewrite BL2 in Hin. destruct (past_nul.pn_pairwise_mid _ _ _ _ _ DISJ2 Hin) as [Hd|Hd];
      unfold ranges_disjoint in Hd; cbn [fst snd] in Hd; lia. }
  assert (OLDs : forall a k, In (a, k) (blocks L A) -> a + k <= s \/ s + Z.max (Z.of_nat (length tb)) 1 <= a).
  { intros a k Hin. exact (OLDs1 a k (SUB1 _ Hin)). }
  pose proof (OLDs1 _ _ INW) as WSd.
  destruct (caw_blk B API L2 A2 mem4 md2 _ _ HM4 (SUB2 _ INW)) as (WRw4 & NOWw4 & _ & _).
  assert (S4 : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs4 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)).
  { intros k Hk. rewrite (RP2 k ltac:(unfold callee_saved; lia)). exact (S3 k Hk). }
  assert (Q4_2 : getr regs4 2 = Z_to_bv 64 (spZ regs + -48)).
  { rewrite <- Q2_2, <- R3_2. exact (RP2 2 ltac:(unfold callee_saved; lia)). }
  assert (Q4_8 : getr regs4 8 = Z_to_bv 64 l).
  { rewrite <- Q2_8, <- R3_8. exact (RP2 8 ltac:(unfold callee_saved; lia)). }
  assert (Q4_9 : getr regs4 9 = Z_to_bv 64 bd).
  { rewrite <- Q2_9, <- R3_9. exact (RP2 9 ltac:(unfold callee_saved; lia)). }
  assert (Q4_18 : getr regs4 18 = Z_to_bv 64 w).
  { rewrite <- R3_18. exact (RP2 18 ltac:(unfold callee_saved; lia)). }
  assert (Q4_19 : getr regs4 19 = Z_to_bv 64 t).
  { rewrite <- Q2_19, <- R3_19. exact (RP2 19 ltac:(unfold callee_saved; lia)). }
  assert (M2 : kb_mid B API (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md
      (fun a => (False \/ False) \/ False) L2 A2 mem4 md2).
  { apply (check_reject_clean_starved.crs_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1e MD2).
    - rewrite SP3. lia.
    - rewrite SP3. lia.
    - rewrite EK. lia.
    - exact LEN1.
    - intros p n Hp _. exact (UB1 p n Hp).
    - intros a Ha Ho _.
      exact (check_reject_clean_starved.crs_own_mid B API AX CO L A mem md L1 A1 mem3 md1 a HM HM3 Ha Ho).
    - intros a Ha Hn He Hw. rewrite SP3 in Hn. rewrite EK in Ha.
      exact (proj1 (proj2 (caw_post_hi B API ERR _ _ _ _ _ _ _ _ _ _ _ _ a HM3 CP2 ltac:(lia)
        ltac:(rewrite SP3; lia) ltac:(cbv beta; tauto))) Hw). }
  assert (UBA2 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A2)).
  { intros q k H. exact (UB2 q k (UB1 q k H)). }
  assert (KP4 : keeps B L A mem mem4 0).
  { exact (check_reject_clean_starved.crs_keep_of_mid B API _ _ _ _ _ _ _ _ _ _ _ M2 (fun q k H _ => UBA2 q k H)). }
  assert (TB4 : Mem.bytes_at rsegs mem4 t (tb ++ [Z_to_bv 8 0])).
  { apply (caw_bytes_keep rsegs mem mem4 t _ TB0). intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    change (mbyte rsegs mem4 (t + i) = mbyte rsegs mem (t + i)).
    rewrite <- SEG. replace (t + i) with (pt + (t + i - pt)) by lia.
    exact (KP4 pt kt (t + i - pt) Hpt ltac:(lia) ltac:(lia)). }
  destruct (past_nul.pn_rw_sub mem4 w (Z.of_nat (length tb) / 4 * 3 + 3) w
    (Z.to_nat (Z.of_nat (length tb) / 4 * 3 + 3)) WRw4 ltac:(lia) ltac:(lia)) as [junkw WW].
  destruct (past_nul.pn_rw_sub mem4 s (Z.max (Z.of_nat (length tb)) 1) s
    (Z.to_nat (Z.max (Z.of_nat (length tb)) 1)) WRs ltac:(lia) ltac:(lia)) as [junks WS4].
  (* run 3: the decoding loop, up to the free of the six-bit buffer *)
  rewrite R3_1.
  eapply (kb_run B regs4 (Z_to_bv 64 0x13644) mem4 md2
    (fun R pc' m' => getr R 1 = Z_to_bv 64 0x13824 /\ getr R 2 = getr regs4 2 /\ getr R 8 = getr regs4 8 /\
       getr R 9 = getr regs4 9 /\ getr R 10 = Z_to_bv 64 s /\ getr R 18 = Z_to_bv 64 w /\
       (forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr R (Z_to_bv 5 k) = getr regs4 (Z_to_bv 5 k)) /\
       pc' = Z_to_bv 64 0x16454 /\
       Frame.munch [(s, s + Z.max (Z.of_nat (length tb)) 1); (w, w + (Z.of_nat (length tb) / 4 * 3 + 3))] mem4 m' /\
       Frame.wmono rsegs mem4 m' /\
       match b64_dec (zs tb) with
       | Some bs => getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ Mem.bytes_at rsegs m' w (bz bs)
       | None => getr R 19 = Z_to_bv 64 (2 ^ 64 - 1)
       end));
    [exact (proj1 (kb_md B API _ _ _ _ HM4)) | exact (proj2 (kb_md B API _ _ _ _ HM4)) | |].
  { rewrite SEG. unfold rmk. rewrite R4_10, Q4_18, Q4_19. eapply Exec.evt_mono.
    - eapply run3 with (t := t) (want := w) (six := s) (n := Z.of_nat (length tb)) (tb := tb) (junkw := junkw)
        (junks := junks).
      + reflexivity.
      + lia.
      + lia.
      + exact NZ.
      + exact TB4.
      + exact WW.
      + exact WS4.
      + lia.
      + destruct (OLDs pt kt Hpt); lia.
      + destruct (OLDw pt kt Hpt); lia.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & r & m' & -> & MU & WM &
        _ & RS).
      do 3 eexists. split; [reflexivity|].
      do 6 (split; [reflexivity|]).
      split; [intros k Hk; caw_k k; reflexivity|].
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      change (zs tb) with (map (fun b : byte => bv_unsigned b) tb). revert RS.
      destruct (b64_dec (map (fun b : byte => bv_unsigned b) tb)) as [bs|]; intros RS;
        [destruct RS as [Er RB]; split; [exact Er | exact RB] | exact RS]. }
  intros RR5 pc5 mem5 regs5 (R5_1 & R5_2 & R5_8 & R5_9 & R5_10 & R5_18 & R5_S & -> & MU5 & WM5 & RS5) HG5.
  rewrite <- HG5 in R5_1, R5_2, R5_8, R5_9, R5_10, R5_18, RS5.
  assert (S5 : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs5 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k))
    by (intros k Hk; rewrite HG5, (R5_S k Hk); exact (S4 k Hk)).
  clear R5_S.
  assert (SP5 : spZ regs5 = spZ regs - 48).
  { unfold spZ at 1. rewrite R5_2, Q4_2, MState.unsigned_lit by lia. lia. }
  assert (NIMG : forall x, ~ Frame.outside [(s, s + Z.max (Z.of_nat (length tb)) 1);
      (w, w + (Z.of_nat (length tb) / 4 * 3 + 3))] x -> ~ in_img B x).
  { intros x Hx. destruct (caw_not_out2 _ _ _ _ x Hx) as [Hx'|Hx'].
    - pose proof FBs as (_ & _ & FI). replace x with (s + (x - s)) by lia. apply FI. lia.
    - pose proof FBw as (_ & _ & FI). replace x with (w + (x - w)) by lia. apply FI. lia. }
  assert (M3 : kb_mid B API (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md
      (fun a => ((False \/ False) \/ False) \/
         (s <= a < s + Z.max (Z.of_nat (length tb)) 1 \/ w <= a < w + (Z.of_nat (length tb) / 4 * 3 + 3)))
      L2 A2 mem5 md2).
  { apply (kb_mid_tail B API IL (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md _ L2 A2 mem4 md2 mem5 _
      (fun a => s <= a < s + Z.max (Z.of_nat (length tb)) 1 \/ w <= a < w + (Z.of_nat (length tb) / 4 * 3 + 3))
      M2 MU5).
    - rewrite SEG. exact WM5.
    - intros x Hx.
      destruct (kb_outside_dec [(s, s + Z.max (Z.of_nat (length tb)) 1);
        (w, w + (Z.of_nat (length tb) / 4 * 3 + 3))] (bv_unsigned x)) as [Ho|Ho].
      + rewrite (MU5 x Ho). exact Hx.
      + apply (past_nul.pn_wview_none rsegs mem5 x).
        * destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:F; [|reflexivity].
          exfalso. exact (NIMG _ Ho (past_nul.pn_seg_img B SEG _ _ F)).
        * apply WM5. apply past_nul.pn_wview_some. exact Hx.
    - intros x Hx _ He. apply kb_outside. intros lo hi Hin Hlh. apply He.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
    - intros x Hx Ho. apply kb_outside. intros lo hi Hin Hlh.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; [exact (NOWs x Hlh Ho) | exact (NOWw4 x Hlh Ho)].
    - intros p n i Hp Hp2 Hi. apply kb_outside. intros lo hi Hin Hlh.
      assert (Hin' : In (ptr_addr L p, n) (blocks L A)).
      { unfold blocks. apply in_map_iff. exists (p, n). split; [reflexivity | exact Hp]. }
      destruct (OLDs _ _ Hin'); destruct (OLDw _ _ Hin'); destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
  pose proof M3 as (HM5 & _ & _ & _ & PA3 & _ & _ & _ & S3w).
  assert (RA5 : ro_agree rsegs mem5) by exact (caw_ro_heap B SEG mem4 mem5 _ RA4 MU5 NIMG).
  assert (PRE5 : call_pre_k B MR ALLOC_STACK L2 A2 regs5 mem5 md2).
  { unfold call_pre_k.
    split; [exact HM5|]. split; [exact HWF4|]. split; [exact HBD4|].
    split; [rewrite R5_1; vm_compute; reflexivity|].
    split; [rewrite SP5; Z.div_mod_to_equations; lia|].
    split; [rewrite SP5; lia|].
    split; [rewrite SP5; lia|].
    split; [intros a Ha; apply S3w; left; rewrite SP5 in Ha; rewrite EK; lia|].
    split; [transitivity (getr regs 4); [exact (S5 4 ltac:(lia)) | exact HTP]|].
    split; [intros a Ha; apply S3w; right; exact Ha|].
    intros Hf. rewrite INIT2 in Hf. discriminate. }
  (* free (six-bit buffer) *)
  destruct (HsKindB.in_blocks L2 A2 _ _ INS) as (qs & Hqs & Eqs).
  replace (Z_to_bv 64 0x16454) with (Z_to_bv 64 (ms_free B)) by (rewrite FRE; reflexivity).
  eapply SR_bind.
  { apply (FREE L2 A2 regs5 mem5 md2 qs (Z.max (Z.of_nat (length tb)) 1)
      (sb_malloc (sb_malloc bnd (Z.of_nat (length tb) / 4 * 3 + 3)) (Z.max (Z.of_nat (length tb)) 1))).
    - apply (proj2 (call_pre_k_alloc B MR L2 A2 regs5 mem5 md2)). exact PRE5.
    - rewrite SEG. exact RA5.
    - exact Hqs.
    - rewrite R5_10, <- Eqs. reflexivity.
    - exact RES2. }
  intros c3 (L3 & A3 & regs6 & mem6 & md3 & -> & CP3 & (d1 & d2 & BL3 & BL3') & BK3 & RA6 & GK6 & UB3 & INIT3 &
    LEN3 & RES3).
  apply call_post_k_alloc in CP3.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP3) as [MD3 RP3].
  pose proof CP3 as (HM6 & HWF6 & HBD6 & _ & HPA3 & _ & _ & _ & _ & _).
  rewrite SEG in RA6.
  assert (S6 : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs6 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k)).
  { intros k Hk. rewrite (RP3 k ltac:(unfold callee_saved; lia)). exact (S5 k Hk). }
  assert (Q6_2 : getr regs6 2 = Z_to_bv 64 (spZ regs + -48)).
  { rewrite <- Q4_2, <- R5_2. exact (RP3 2 ltac:(unfold callee_saved; lia)). }
  assert (Q6_8 : getr regs6 8 = Z_to_bv 64 l).
  { rewrite <- Q4_8, <- R5_8. exact (RP3 8 ltac:(unfold callee_saved; lia)). }
  assert (Q6_9 : getr regs6 9 = Z_to_bv 64 bd).
  { rewrite <- Q4_9, <- R5_9. exact (RP3 9 ltac:(unfold callee_saved; lia)). }
  assert (Q6_18 : getr regs6 18 = Z_to_bv 64 w).
  { rewrite <- R5_18. exact (RP3 18 ltac:(unfold callee_saved; lia)). }
  assert (Q6_19 : getr regs6 19 = getr regs5 19) by exact (RP3 19 ltac:(unfold callee_saved; lia)).
  assert (M4 : kb_mid B API (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md
      (fun a => (((False \/ False) \/ False) \/
         (s <= a < s + Z.max (Z.of_nat (length tb)) 1 \/ w <= a < w + (Z.of_nat (length tb) / 4 * 3 + 3))) \/
         (ptr_addr L2 qs <= a < ptr_addr L2 qs + Z.max (Z.of_nat (length tb)) 1)) L3 A3 mem6 md3).
  { apply (check_reject_clean_starved.crs_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M3 MD3).
    - rewrite SP5. lia.
    - rewrite SP5. lia.
    - rewrite EK. lia.
    - lia.
    - intros p n Hp _. exact (UBA2 p n Hp).
    - intros a Ha Ho _.
      exact (check_reject_clean_starved.crs_own_mid B API AX CO L A mem md L2 A2 mem5 md2 a HM HM5 Ha Ho).
    - intros a Ha Hn He Hw. rewrite SP5 in Hn. rewrite EK in Ha.
      exact (proj1 (proj2 (caw_post_hi B API ERR _ _ _ _ _ _ _ _ _ _ _ _ a HM5 CP3 ltac:(lia)
        ltac:(rewrite SP5; lia) ltac:(cbv beta; rewrite <- Eqs; lia))) Hw). }
  assert (NEs : forall q k, In (q, k) (user_blocks A) -> q <> qs).
  { intros q k Hq Eq. subst q.
    pose proof (caw_fst_unique _ qs k (Z.max (Z.of_nat (length tb)) 1) (YO10.user_block_ptrs_NoDup A2 HWF4)
      (UBA2 _ _ Hq) Hqs) as Ek.
    assert (Hin : In (ptr_addr L qs, k) (blocks L A)).
    { unfold blocks. apply in_map_iff. exists (qs, k). split; [reflexivity | exact Hq]. }
    pose proof (PA3 qs k Hq (UBA2 _ _ Hq)) as Ea. rewrite <- Eqs in Ea.
    destruct (OLDs _ _ Hin); lia. }
  assert (UBA3 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A3)).
  { intros q k Hq. exact (UB3 q k (UBA2 q k Hq) (NEs q k Hq)). }
  assert (KP6 : keeps B L A mem mem6 0).
  { exact (check_reject_clean_starved.crs_keep_of_mid B API _ _ _ _ _ _ _ _ _ _ _ M4 (fun q k H _ => UBA3 q k H)). }
  assert (FR6 : Step.rw_cells rsegs mem6 (spZ regs + -48)
      [CB 8 junk; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { pose proof (cw_rw_eq mem2 mem3 _ _ EQ3 FR2) as FR3.
    apply (check_reject_clean_starved.crs_rw_keep mem3 mem6 (spZ regs + -48) _ ltac:(lia) FR3). intros a Ha.
    cbn [cells_size csize Nat.add] in Ha. rewrite <- SEG.
    rewrite (proj1 (caw_post_hi B API ERR _ _ _ _ _ _ _ _ _ _ _ _ a HM5 CP3 ltac:(lia) ltac:(rewrite SP5; lia)
      ltac:(cbv beta; rewrite <- Eqs; lia))).
    rewrite (mbyte_munch (ms_segs B) _ mem4 mem5 a MU5 ltac:(lia)).
    2: { apply kb_outside. intros lo hi Hin Hlh. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
    exact (proj1 (caw_post_hi B API ERR _ _ _ _ _ _ _ _ _ _ _ _ a HM3 CP2 ltac:(lia) ltac:(rewrite SP3; lia)
      ltac:(cbv beta; tauto))). }
  assert (CASE : (bd = 0 /\ getr regs6 19 = Z_to_bv 64 (2 ^ 64 - 1)) \/
     (exists bs, bd <> 0 /\ l = Z.of_nat (length bs) /\ l < 2 ^ 64 - 1 /\ getr regs6 19 = Z_to_bv 64 l /\
        Mem.bytes_at rsegs mem6 bd (map (Z_to_bv 8) bs) /\ Mem.bytes_at rsegs mem6 w (map (Z_to_bv 8) bs))).
  { rewrite Q6_19. destruct CAW as [(DEC & BD0 & L0) | (bs & DEC & BDN & EL & BBS)]; rewrite DEC in RS5.
    - left. split; [exact BD0 | exact RS5].
    - right. destruct RS5 as [R19 BW]. exists bs.
      pose proof (caw_dec_len _ _ DEC) as DL. unfold zs in DL. rewrite length_map in DL.
      split; [exact BDN|]. split; [exact EL|]. split; [lia|]. split; [rewrite R19, EL; reflexivity|].
      split.
      + destruct (BDL BDN) as (kb & Hkb & Hlk).
        pose proof LG as (_ & _ & _ & _ & _ & LGF). rewrite Forall_forall in LGF.
        destruct (LGF (bd, kb) Hkb) as (Hk0 & Hinb & _). cbn [fst snd] in Hk0, Hinb.
        destruct (caw_blk B API L A mem md _ _ HM Hinb) as (_ & _ & Rb1 & _).
        rewrite SEG in BBS. apply (caw_bytes_keep rsegs mem mem6 bd _ BBS). intros i Hi.
        unfold bz in Hi. rewrite length_map in Hi.
        change (mbyte rsegs mem6 (bd + i) = mbyte rsegs mem (bd + i)). rewrite <- SEG.
        replace (bd + i) with (bd - 16 + (i + 16)) by lia.
        exact (KP6 (bd - 16) (kb + 16) (i + 16) Hinb ltac:(lia) ltac:(lia)).
      + apply (caw_bytes_keep rsegs mem5 mem6 w _ BW). intros i Hi. unfold bz in Hi. rewrite length_map in Hi.
        change (mbyte rsegs mem6 (w + i) = mbyte rsegs mem5 (w + i)). rewrite <- SEG.
        apply (BK3 w _ i (SUB2 _ INW)); [cbv beta; rewrite <- Eqs; lia | lia]. }
  (* run 4: the comparison (bcmp) and the epilogue, up to the tail call of free *)
  rewrite R5_1.
  eapply (kb_run B regs6 (Z_to_bv 64 0x13824) mem6 md3
    (fun R pc' m' => getr R 1 = getr regs 1 /\ getr R 2 = getr regs 2 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 10 = Z_to_bv 64 w /\ getr R 18 = getr regs 18 /\ getr R 19 = getr regs 19 /\
       (forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr R (Z_to_bv 5 k) = getr regs6 (Z_to_bv 5 k)) /\
       pc' = Z_to_bv 64 0x16454 /\ (forall x, m' x = mem6 x)));
    [exact (proj1 (kb_md B API _ _ _ _ HM6)) | exact (proj2 (kb_md B API _ _ _ _ HM6)) | |].
  { rewrite SEG. unfold rmk. rewrite Q6_8, Q6_9, Q6_18. eapply Exec.evt_mono.
    - eapply (run4 BCMP) with (l := l) (bd := bd) (w := w) (junk := junk) (xra := getr regs 1) (xs0 := getr regs 8)
        (xs1 := getr regs 9) (xs2 := getr regs 18) (xs3 := getr regs 19).
      + rewrite Q6_2, MState.unsigned_lit by lia. exact FR6.
      + lia.
      + lia.
      + lia.
      + exact CASE.
      + exact RA6.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & -> & EQ).
      do 3 eexists. split; [reflexivity|].
      split; [reflexivity|].
      split.
      { transitivity (Z_to_bv 64 (bv_unsigned (getr regs6 2) + 48)); [reflexivity|].
        rewrite Q6_2, MState.unsigned_lit by lia. replace (spZ regs + -48 + 48) with (spZ regs) by lia.
        unfold spZ. apply Z_to_bv_bv_unsigned. }
      do 5 (split; [reflexivity|]).
      split; [intros k Hk; caw_k k; reflexivity|].
      split; [reflexivity | exact EQ]. }
  intros RR7 pc7 mem7 regs7 (R7_1 & R7_2 & R7_8 & R7_9 & R7_10 & R7_18 & R7_19 & R7_S & -> & EQ7) HG7.
  rewrite <- HG7 in R7_1, R7_2, R7_8, R7_9, R7_10, R7_18, R7_19.
  assert (S7 : forall k, k = 3 \/ k = 4 \/ 20 <= k <= 27 -> getr regs7 (Z_to_bv 5 k) = getr regs (Z_to_bv 5 k))
    by (intros k Hk; rewrite HG7, (R7_S k Hk); exact (S6 k Hk)).
  clear R7_S.
  assert (SP7 : spZ regs7 = spZ regs) by (unfold spZ at 1; rewrite R7_2; reflexivity).
  assert (RP7 : regs_preserved regs regs7).
  { intros k Hk. unfold callee_saved in Hk.
    destruct Hk as [-> | [-> | [-> | [-> | [-> | Hk]]]]];
      [exact R7_2 | exact (S7 3 ltac:(lia)) | exact (S7 4 ltac:(lia)) | exact R7_8 | exact R7_9 |].
    assert (Hk' : k = 18 \/ k = 19 \/ 20 <= k <= 27) by lia.
    destruct Hk' as [-> | [-> | Hk']]; [exact R7_18 | exact R7_19 | exact (S7 k ltac:(lia))]. }
  assert (M4e : kb_mid B API (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md
      (fun a => (((False \/ False) \/ False) \/
         (s <= a < s + Z.max (Z.of_nat (length tb)) 1 \/ w <= a < w + (Z.of_nat (length tb) / 4 * 3 + 3))) \/
         (ptr_addr L2 qs <= a < ptr_addr L2 qs + Z.max (Z.of_nat (length tb)) 1)) L3 A3 mem7 md3)
    by exact (caw_mid_eq B API IL _ _ _ _ _ _ _ _ _ _ _ _ M4 EQ7).
  pose proof M4e as (HM7 & _ & _ & _ & PA4 & _ & _ & _ & S4w).
  assert (PRE7 : call_pre_k B MR ALLOC_STACK L3 A3 regs7 mem7 md3).
  { unfold call_pre_k.
    split; [exact HM7|]. split; [exact HWF6|]. split; [exact HBD6|].
    split; [rewrite R7_1; exact HRA|].
    split; [rewrite SP7; exact H16|].
    split; [rewrite SP7; lia|].
    split; [rewrite SP7; exact H63|].
    split; [intros a Ha; apply S4w; left; rewrite SP7 in Ha; rewrite EK; lia|].
    split; [transitivity (getr regs 4); [exact (S7 4 ltac:(lia)) | exact HTP]|].
    split; [intros a Ha; apply S4w; right; exact Ha|].
    intros Hf. rewrite (INIT3 INIT2) in Hf. discriminate. }
  assert (RA7 : ro_agree rsegs mem7) by exact (cw_ro_agree_eq mem6 mem7 EQ7 RA6).
  destruct (HsKindB.in_blocks L1 A1 _ _ INW) as (qw & Hqw & Eqw).
  assert (Hqw2 : In (qw, Z.of_nat (length tb) / 4 * 3 + 3) (user_blocks A2)) by exact (UB2 _ _ Hqw).
  assert (Ew2 : ptr_addr L2 qw = w) by (rewrite (HPA2 _ _ Hqw Hqw2); symmetry; exact Eqw).
  assert (NEw : qw <> qs).
  { intros E. subst qw. rewrite <- Eqs in Ew2. lia. }
  assert (Hqw3 : In (qw, Z.of_nat (length tb) / 4 * 3 + 3) (user_blocks A3)) by exact (UB3 _ _ Hqw2 NEw).
  assert (Ew3 : ptr_addr L3 qw = w) by (rewrite (HPA3 _ _ Hqw2 Hqw3); exact Ew2).
  (* tail call: free (decoded buffer) *)
  replace (Z_to_bv 64 0x16454) with (Z_to_bv 64 (ms_free B)) by (rewrite FRE; reflexivity).
  eapply SR_mono.
  { apply (FREE L3 A3 regs7 mem7 md3 qw (Z.of_nat (length tb) / 4 * 3 + 3)
      (sb_free (sb_malloc (sb_malloc bnd (Z.of_nat (length tb) / 4 * 3 + 3)) (Z.max (Z.of_nat (length tb)) 1))
        (Z.max (Z.of_nat (length tb)) 1))).
    - apply (proj2 (call_pre_k_alloc B MR L3 A3 regs7 mem7 md3)). exact PRE7.
    - rewrite SEG. exact RA7.
    - exact Hqw3.
    - rewrite R7_10, Ew3. reflexivity.
    - exact RES3. }
  intros c4 (L4 & A4 & regs8 & mem8 & md4 & -> & CP4 & (e1 & e2 & BL4 & BL4') & BK4 & RA8 & GK8 & UB4 & INIT4 &
    LEN4 & RES4).
  apply call_post_k_alloc in CP4.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ CP4) as [MD4 RP4].
  pose proof CP4 as (HM8 & _).
  assert (MF : kb_mid B API (ALLOC_STACK + CAW_FRAME) (spZ regs) L A mem md
      (fun a => w <= a < w + (Z.of_nat (length tb) / 4 * 3 + 3) \/ s <= a < s + Z.max (Z.of_nat (length tb)) 1)
      L4 A4 mem8 md4).
  { eapply (check_reject_clean_starved.crs_mid_E B API).
    - eapply (check_reject_clean_starved.crs_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M4e MD4).
      + rewrite SP7. lia.
      + rewrite SP7. lia.
      + rewrite EK. lia.
      + lia.
      + intros p n Hp _. exact (UBA3 p n Hp).
      + intros a Ha Ho _.
        exact (check_reject_clean_starved.crs_own_mid B API AX CO L A mem md L3 A3 mem7 md3 a HM HM7 Ha Ho).
      + intros a Ha Hn He Hw. rewrite SP7 in Hn. rewrite EK in Ha.
        exact (proj1 (proj2 (caw_post_hi B API ERR _ _ _ _ _ _ _ _ _ _ _ _ a HM7 CP4 ltac:(lia)
          ltac:(rewrite SP7; lia) ltac:(cbv beta; rewrite Ew3; lia))) Hw).
    - intros a _ Ha. cbv beta in Ha. rewrite Ew3, <- Eqs in Ha. lia. }
  assert (NEw' : forall q k, In (q, k) (user_blocks A) -> q <> qw).
  { intros q k Hq E. subst q.
    pose proof (caw_fst_unique _ qw k (Z.of_nat (length tb) / 4 * 3 + 3) (YO10.user_block_ptrs_NoDup A3 HWF6)
      (UBA3 _ _ Hq) Hqw3) as Ek.
    assert (Hin : In (ptr_addr L qw, k) (blocks L A)).
    { unfold blocks. apply in_map_iff. exists (qw, k). split; [reflexivity | exact Hq]. }
    pose proof (PA4 qw k Hq (UBA3 _ _ Hq)) as Ea. rewrite Ew3 in Ea.
    destruct (OLDw _ _ Hin); lia. }
  assert (UBF : ublocks_kept L A A4 (0, 0)).
  { intros q k Hq _. exact (UB4 q k (UBA3 q k Hq) (NEw' q k Hq)). }
  assert (BL3E : blocks L3 A3 = blocks L1 A1).
  { rewrite BL3', BL2. symmetry.
    apply (caw_mid_uniq c1 c2 d1 d2 (s, Z.max (Z.of_nat (length tb)) 1)); [exact DISJ2 | cbn [snd]; lia |].
    rewrite <- BL2', BL3, <- Eqs. reflexivity. }
  assert (BLF : blocks L4 A4 = blocks L A).
  { rewrite BL4', BL1. symmetry.
    apply (caw_mid_uniq b1 b2 e1 e2 (w, Z.of_nat (length tb) / 4 * 3 + 3)); [exact DISJ1 | cbn [snd]; lia |].
    rewrite <- BL1', <- BL3E, BL4, Ew3. reflexivity. }
  assert (KPF : keeps B L A mem mem8 0).
  { exact (check_reject_clean_starved.crs_keep_of_mid B API _ _ _ _ _ _ _ _ _ _ _ MF UBF). }
  assert (KGF : forall x, in_globals [(G_FAIL, 8); (G_LIVE, 24)] x ->
      mbyte (ms_segs B) mem8 x = mbyte (ms_segs B) mem x).
  { intros x Hx. destruct (GF x Hx) as (Hi & Hxr & _ & He & Ho).
    destruct (Ho L A mem md HM) as [Hn _]. destruct (Ho L4 A4 mem8 md4 HM8) as [Hn' _].
    pose proof MF as (_ & _ & _ & _ & _ & _ & F7 & _).
    refine (proj1 (F7 x (or_intror Hi) Hn Hn' _ _)).
    - intros [Hs|Hs]; [lia | exact (He Hs)].
    - cbv beta. intros [Hw|Hs].
      + pose proof FBw as (_ & _ & FI). apply (FI (x - w)); [lia|]. replace (w + (x - w)) with x by lia. exact Hi.
      + pose proof FBs as (_ & _ & FI). apply (FI (x - s)); [lia|]. replace (s + (x - s)) with x by lia. exact Hi. }
  assert (GKF : guard_kept B mem mem8).
  { intros i Hi.
    assert (Ho : forall L A, owned B L A (ms_got_guard B + i)).
    { intros. right. unfold static_owned. right; right; right; right; left. lia. }
    pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM (Ho L A)) as Hlo.
    rewrite (GK8 i Hi), (caw_mbyte_eq _ mem6 mem7 _ EQ7), (GK6 i Hi).
    rewrite (mbyte_munch (ms_segs B) _ mem4 mem5 (ms_got_guard B + i) MU5 ltac:(lia)).
    2: { apply kb_outside. intros lo hi Hin Hlh. destruct Hin as [E|[E|[]]]; injection E as <- <-;
         [exact (NOWs _ Hlh (Ho L2 A2)) | exact (NOWw4 _ Hlh (Ho L2 A2))]. }
    rewrite (GK4 i Hi), (caw_mbyte_eq _ mem2 mem3 _ EQ3), (GK2 i Hi).
    exact (mbyte_munch (ms_segs B) _ mem mem1 (ms_got_guard B + i) MU1' ltac:(lia) ltac:(apply outside_one; lia)). }
  exists L4, A4, regs8, mem8, md4, w, s.
  split; [rewrite R7_1; reflexivity|].
  split; [exact RA8|].
  split; [exact GKF|].
  split; [exact (INIT4 (INIT3 INIT2))|].
  split; [exact FBw|]. split; [exact FBs|].
  split; [exact OLDw|]. split; [exact OLDs|].
  split; [apply (kb_post B API); [exact MF | exact (kb_preserved_trans _ _ _ RP7 RP4)]|].
  split; [exact BLF|].
  split; [exact KPF|].
  split; [exact UBF|].
  split; [exact (caw_ledger B API GF L A mem md L4 A4 mem8 Lam peak cnt fail HM LG BLF KPF KGF)|].
  rewrite !sb_free_malloc in RES4. exact RES4.
Qed.

End P.
