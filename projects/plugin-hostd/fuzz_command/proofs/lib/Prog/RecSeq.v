From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK14 YP09 YO0i YO0f YO0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0o YO0u YO0x YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Lemma outside_dec : forall W a, outside W a \/ ~ outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a; cbn; [left; exact I|].
  destruct (IH a) as [H|H]; [|right; tauto].
  destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi); [right; lia | left; split; [lia | exact H] ..].
Qed.

Lemma spz_eq_dec : forall x y : sptr * Z, {x = y} + {x <> y}.
Proof.
  intros [[r o] n] [[r' o'] n']. destruct (Nat.eq_dec r r'); [|right; congruence].
  destruct (Z.eq_dec o o'); [|right; congruence]. destruct (Z.eq_dec n n'); [left; congruence | right; congruence].
Defined.

Lemma with_vmmaps_self' : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma with_vmmaps_twice' : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma ptr_addr_stable : forall A L L' p n, WF A -> In (p, n) (user_blocks A) -> layout_le A L L' ->
  ptr_addr L' p = ptr_addr L p.
Proof.
  intros A L L' p n HW Hin (_ & _ & _ & HR).
  destruct (user_blocks_frame A p n HW Hin) as (g & am & idx & fr & Hu & _ & _ & _ & _ & ->).
  pose proof (used_group_prid_lt [] None U0 A g am HW Hu) as Hlt.
  unfold ptr_addr, loc_addr, frame_ptr, slot_start.
  pose proof (prid_padd (padd (am_mem am) (UNIT + stride_of am * idx)) (UNIT * fr_off fr)) as P1.
  pose proof (prid_padd (am_mem am) (UNIT + stride_of am * idx)) as P2.
  destruct (padd (padd (am_mem am) (UNIT + stride_of am * idx)) (UNIT * fr_off fr)) as [r o].
  cbn [prid] in P1. rewrite P1, P2 in *. rewrite (HR (prid (am_mem am)) Hlt). reflexivity.
Qed.

Lemma layout_le_trans : forall A A1 L L1 L2, layout_le A L L1 -> layout_le A1 L1 L2 ->
  (length (st_regions A) <= length (st_regions A1))%nat -> layout_le A L L2.
Proof.
  intros A A1 L L1 L2 (C1 & S1 & B1 & R1) (C2 & S2 & B2 & R2) Hl.
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  intros r Hr. rewrite (R2 r ltac:(lia)). exact (R1 r Hr).
Qed.

Section Seq.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTXO : forall L A mem md a, MR L A mem md -> ms_ctx B <= a < ms_ctx B + CTX_SIZE -> owned B L A a.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Let segs := ms_segs B.

Definition free_a (a : Z) : Prop :=
  alloc_ceiling <= a < 2 ^ 64 \/ (in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE)).

Lemma free_a_not_owned : forall L A mem md a, MR L A mem md -> free_a a -> ~ owned B L A a.
Proof using LAWS AX.
  intros L A mem md a HM [Ha | (Hi & Hs & Hc)] Ho.
  - pose proof (mr_owned_low B MR LAWS L A mem md a HM Ho). lia.
  - destruct Ho as [Ho|Ho]; [|exact (Hs Ho)]. exact (Hc (ax_img AX L A mem md a HM Hi Ho)).
Qed.

Lemma free_a_of_owned : forall L A mem md a, MR L A mem md ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> free_a a.
Proof using CTXO.
  intros L A mem md a HM [Ha|Hi] Hn; [left; exact Ha|]. right. split; [exact Hi|].
  split; [intros Hs; apply Hn; right; exact Hs|]. intros Hc. exact (Hn (CTXO L A mem md a HM Hc)).
Qed.

Lemma free_a_range : forall a, free_a a -> 0 <= a < 2 ^ 64.
Proof using SEGS.
  intros a [Ha | (Hi & _)]; [pose proof alloc_ceiling_val; lia|]. pose proof (in_img_low B SEGS a Hi). lia.
Qed.

Definition rjr (K S : Z) (E : Z -> Prop) (gone : Z * Z -> Prop)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
  MR Lc Ac memc mdc /\ WF A /\ WF Ac /\ bounded Ac /\ layout_le A L Lc /\
  (length (st_regions A) <= length (st_regions Ac))%nat /\
  (exists vm', mdc = with_vmmaps vm' md) /\
  alloc_ceiling + K <= S /\ 0 <= K /\ S < 2 ^ 63 /\
  (forall a, free_a a -> ~ (S - K <= a < S) -> ~ (errno_addr B <= a < errno_addr B + 4) -> ~ E a ->
     mbyte segs memc a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs memc a)) /\
  (forall p n, In (p, n) (user_blocks A) -> ~ In (p, n) (user_blocks Ac) -> gone (ptr_addr L p, n)) /\
  (forall p n i, In (p, n) (user_blocks A) -> ~ gone (ptr_addr L p, n) -> 0 <= i < n ->
     mbyte segs memc (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, (S - K <= a < S) \/ (errno_addr B <= a < errno_addr B + 4) -> writable_at segs memc a) /\
  (st_init_done Ac = false -> auxv_pre B (ly_sec Lc) S memc).

Lemma rjr_init : forall K E gone L A regs mem md,
  call_pre_k B MR K L A regs mem md -> 0 <= K ->
  rjr K (spZ regs) E gone L A mem md L A mem md.
Proof.
  intros K E gone L A regs mem md (HM & HW & HB & _ & _ & HC & H63 & HWS & _ & HER & HAUX) HK.
  split; [exact HM|]. split; [exact HW|]. split; [exact HW|]. split; [exact HB|].
  split; [apply layout_le_refl|]. split; [lia|].
  split; [exists (m_vmmaps md); apply with_vmmaps_self'|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a _ _ _ _; split; [reflexivity | tauto]|].
  split; [intros p n H1 H2; contradiction|].
  split; [intros; reflexivity|].
  split; [intros a [H|H]; [apply HWS; lia | apply HER; exact H]|].
  exact HAUX.
Qed.

Lemma rjr_bounds : forall K S E gone L A mem md Lc Ac memc mdc,
  rjr K S E gone L A mem md Lc Ac memc mdc -> alloc_ceiling + K <= S /\ 0 <= K /\ S < 2 ^ 63.
Proof. intros K S E gone L A mem md Lc Ac memc mdc R. destruct R as (_ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _). auto. Qed.

Lemma rjr_in_cur : forall K S E gone L A mem md Lc Ac memc mdc p n,
  rjr K S E gone L A mem md Lc Ac memc mdc -> In (p, n) (user_blocks A) -> ~ gone (ptr_addr L p, n) ->
  In (p, n) (user_blocks Ac).
Proof.
  intros K S E gone L A mem md Lc Ac memc mdc p n R Hin Hg.
  destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RM & _).
  destruct (In_dec spz_eq_dec (p, n) (user_blocks Ac)) as [H|H]; [exact H|]. exfalso. exact (Hg (RM p n Hin H)).
Qed.

Lemma rjr_munch : forall K S E gone L A mem md Lc Ac memc mdc memc' W,
  rjr K S E gone L A mem md Lc Ac memc mdc ->
  munch W memc memc' -> wmono segs memc memc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> free_a a -> (S - K <= a < S) \/ E a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> ~ owned B Lc Ac a) ->
  (forall a, S <= a < 2 ^ 64 -> outside W a) ->
  (forall p n i, In (p, n) (user_blocks A) -> ~ gone (ptr_addr L p, n) -> 0 <= i < n -> outside W (ptr_addr L p + i)) ->
  (forall p n i, In (p, n) (user_blocks Ac) -> 0 <= i < n -> present memc' (ptr_addr Lc p + i)) ->
  rjr K S E gone L A mem md Lc Ac memc' mdc.
Proof using SEGS LAWS.
  intros K S E gone L A mem md Lc Ac memc mdc memc' W R MU WM HW HO HS HB HP.
  pose proof R as R0.
  destruct R as (HM & HWA & HW' & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  assert (OWN : forall a, owned B Lc Ac a -> outside W a).
  { intros a Ho. destruct (mr_owned_low B MR LAWS Lc Ac memc mdc a HM Ho) as [Ha1 Ha2].
    pose proof alloc_ceiling_val as AC0.
    destruct (outside_dec W a) as [Hw|Hw]; [exact Hw|]. exfalso. exact (HO a ltac:(lia) Hw Ho). }
  destruct (mr_model B MR LAWS Lc Ac memc mdc HM) as (Hh & Hl & Hmat).
  split.
  { eapply (mr_frame B MR LAWS Lc Ac memc memc' mdc mdc HM).
    - intros a Ho. destruct (mr_owned_low B MR LAWS Lc Ac memc mdc a HM Ho).
      pose proof alloc_ceiling_val as AC0. apply (munch_mbyte _ _ _ _ _ MU); [lia | exact (OWN a Ho)].
    - intros a Ho Hp. destruct (mr_owned_low B MR LAWS Lc Ac memc mdc a HM Ho).
      pose proof alloc_ceiling_val as AC0. apply (munch_present _ _ _ _ MU); [lia | exact (OWN a Ho) | exact Hp].
    - exact HP.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact HWA|]. split; [exact HW'|]. split; [exact HBd|]. split; [exact HL|]. split; [exact HLen|].
  split; [exact HV|]. split; [exact HK1|]. split; [exact HK2|]. split; [exact HK3|].
  split.
  { intros a Hf Hw He HE. pose proof (free_a_range a Hf) as Ra.
    assert (OW : outside W a).
    { destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a Ra H Hf); contradiction. }
    destruct (HF a Hf Hw He HE) as [E1 E2].
    split; [rewrite (munch_mbyte _ _ _ _ _ MU Ra OW); exact E1|].
    rewrite E2. apply (munch_writable _ _ _ _ _ MU Ra OW). }
  split; [exact HRM|].
  split.
  { intros p n i Hin Hg Hi.
    pose proof (rjr_in_cur K S E gone L A mem md Lc Ac memc mdc p n R0 Hin Hg) as Hc.
    destruct (mr_blocks B MR LAWS Lc Ac memc mdc p n i HM Hc Hi) as (_ & H4 & H5 & _).
    rewrite (ptr_addr_stable A L Lc p n HWA Hin HL) in H4, H5. pose proof alloc_ceiling_val as AC0.
    rewrite (munch_mbyte _ _ _ _ (ptr_addr L p + i) MU ltac:(lia) (HB p n i Hin Hg Hi)). exact (HKP p n i Hin Hg Hi). }
  split; [intros a Ha; apply WM; exact (HSC a Ha)|].
  intros Hi. destruct (HAX Hi) as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
  exists av, ar.
  assert (LIB : forall k, (k < 8)%nat -> 0 <= ms_libc B + 8 + Z.of_nat k < 2 ^ 64 /\ outside W (ms_libc B + 8 + Z.of_nat k)).
  { intros k Hk. assert (Ho : owned B Lc Ac (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
    destruct (mr_owned_low B MR LAWS Lc Ac memc mdc _ HM Ho). pose proof alloc_ceiling_val as AC0.
    split; [lia | exact (OWN _ Ho)]. }
  split; [exact (word_mem_munch _ _ _ _ _ _ MU LIB W1)|].
  split; [intros k Hk; apply (word_mem_munch _ _ _ _ _ _ MU); [|exact (W2 k Hk)]; intros k' Hk'; split; [lia | apply HS; lia]|].
  split; [apply (word_mem_munch _ _ _ _ _ _ MU); [|exact W3]; intros k' Hk'; split; [lia | apply HS; lia]|].
  split; [apply (word_mem_munch _ _ _ _ _ _ MU); [|exact W4]; intros k' Hk'; split; [lia | apply HS; lia]|].
  lia.
Qed.

Lemma call_post_k_rec : forall stk L A regs mem md E L' A' regs' mem' md',
  call_post_k B MR stk L A regs mem md E L' A' regs' mem' md' ->
  call_post_rec B MR stk L A regs mem md E (fun _ => False) L' A' regs' mem' md'.
Proof.
  intros stk L A regs mem md E L' A' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  repeat (split; [eassumption|]). split; [intros p n i Hp Hp' _ Hi; exact (H9 p n i Hp Hp' Hi)|]. exact H10.
Qed.

Lemma rjr_post : forall K S E gone L A mem md Lc Ac memc mdc Kc regs_c Ec exc Ln An regs_n memn mdn,
  rjr K S E gone L A mem md Lc Ac memc mdc ->
  call_post_rec B MR Kc Lc Ac regs_c memc mdc Ec exc Ln An regs_n memn mdn ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S ->
  (forall a, Ec a -> free_a a -> E a /\ ~ (S - K <= a < S)) ->
  (forall p n, In (p, n) (user_blocks A) -> ~ gone (ptr_addr L p, n) -> 0 < n -> ~ exc (ptr_addr L p)) ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks Ac) -> ~ In (p, n) (user_blocks An) ->
     gone (ptr_addr L p, n)) ->
  (length (st_regions Ac) <= length (st_regions An))%nat ->
  (st_init_done An = false -> auxv_pre B (ly_sec Ln) S memn) ->
  rjr K S E gone L A mem md Ln An memn mdn.
Proof using SEGS LAWS AX ERRNO_LOW.
  intros K S E gone L A mem md Lc Ac memc mdc Kc regs_c Ec exc Ln An regs_n memn mdn R P Hlo Hhi HE HX HRm HLn HAuxn.
  pose proof R as R0.
  destruct R as (HM & HWA & HW' & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  destruct P as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
  assert (DOM : forall a, free_a a -> alloc_ceiling <= a < 2 ^ 64 \/ in_img B a)
    by (intros a [H|(H & _)]; [left; exact H | right; exact H]).
  assert (STEP : forall a, free_a a -> ~ scratch_k B Kc regs_c a -> ~ Ec a ->
            mbyte segs memn a = mbyte segs memc a /\ (writable_at segs memc a <-> writable_at segs memn a)).
  { intros a Hf NS NE. exact (PF a (DOM a Hf) (free_a_not_owned Lc Ac memc mdc a HM Hf)
                                  (free_a_not_owned Ln An memn mdn a PM Hf) NS NE). }
  split; [exact PM|]. split; [exact HWA|]. split; [exact PW|]. split; [exact PB|].
  split; [exact (layout_le_trans A Ac L Lc Ln HL PL HLen)|]. split; [lia|].
  split; [destruct HV as [v1 ->]; destruct PV as [v2 ->]; exists v2; apply with_vmmaps_twice'|].
  split; [exact HK1|]. split; [exact HK2|]. split; [exact HK3|].
  split.
  { intros a Hf Hw He HE'.
    destruct (HF a Hf Hw He HE') as [E1 E2].
    assert (NS : ~ scratch_k B Kc regs_c a) by (unfold scratch_k; intros [H|H]; [lia | exact (He H)]).
    assert (NE : ~ Ec a) by (intros H; exact (HE' (proj1 (HE a H Hf)))).
    destruct (STEP a Hf NS NE) as [F1 F2].
    split; [rewrite F1; exact E1 | rewrite E2; exact F2]. }
  split.
  { intros p n Hin Hn. destruct (In_dec spz_eq_dec (p, n) (user_blocks Ac)) as [Hc|Hc].
    - exact (HRm p n Hin Hc Hn).
    - exact (HRM p n Hin Hc). }
  split.
  { intros p n i Hin Hg Hi.
    pose proof (rjr_in_cur K S E gone L A mem md Lc Ac memc mdc p n R0 Hin Hg) as Hc.
    assert (Hn : In (p, n) (user_blocks An)).
    { destruct (In_dec spz_eq_dec (p, n) (user_blocks An)) as [H|H]; [exact H|]. exfalso. exact (Hg (HRm p n Hin Hc H)). }
    pose proof (ptr_addr_stable A L Lc p n HWA Hin HL) as EA.
    assert (NX : ~ exc (ptr_addr Lc p)) by (rewrite EA; exact (HX p n Hin Hg ltac:(lia))).
    transitivity (mbyte segs memc (ptr_addr L p + i)); [|exact (HKP p n i Hin Hg Hi)].
    rewrite <- EA. exact (PK p n i Hc Hn NX Hi). }
  split.
  { intros a [Ha|Ha].
    - destruct (Z_lt_ge_dec a (spZ regs_c - Kc)) as [D1|D1];
        [|destruct (Z_lt_ge_dec a (spZ regs_c)) as [D2|D2]; [apply PS; left; lia|]].
      + assert (Hf : free_a a) by (left; pose proof alloc_ceiling_val; lia).
        assert (NS : ~ scratch_k B Kc regs_c a) by (unfold scratch_k; intros [H|H]; [lia | pose proof ERRNO_LOW; lia]).
        assert (NE : ~ Ec a) by (intros H; exact (proj2 (HE a H Hf) Ha)).
        apply (proj2 (STEP a Hf NS NE)). apply HSC. left. exact Ha.
      + assert (Hf : free_a a) by (left; pose proof alloc_ceiling_val; lia).
        assert (NS : ~ scratch_k B Kc regs_c a) by (unfold scratch_k; intros [H|H]; [lia | pose proof ERRNO_LOW; lia]).
        assert (NE : ~ Ec a) by (intros H; exact (proj2 (HE a H Hf) Ha)).
        apply (proj2 (STEP a Hf NS NE)). apply HSC. left. exact Ha.
    - apply PS. right. exact Ha. }
  exact HAuxn.
Qed.

Lemma call_pre_k_of_rjr : forall K S E gone L A mem md Lc Ac memc mdc Kc regs_c,
  rjr K S E gone L A mem md Lc Ac memc mdc ->
  YK0s.ret_ok (getr regs_c 1) -> spZ regs_c mod 16 = 0 -> 0 <= Kc ->
  S - K <= spZ regs_c - Kc -> spZ regs_c <= S -> getr regs_c 4 = Z_to_bv 64 (ms_tp B) ->
  call_pre_k B MR Kc Lc Ac regs_c memc mdc.
Proof.
  intros K S E gone L A mem md Lc Ac memc mdc Kc regs_c R Hra Hal HKc Hlo Hhi Htp.
  destruct R as (HM & HWA & HW' & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  split; [exact HM|]. split; [exact HW'|]. split; [exact HBd|]. split; [exact Hra|]. split; [exact Hal|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; apply HSC; left; lia|].
  split; [exact Htp|].
  split; [intros a Ha; apply HSC; right; exact Ha|].
  intros Hi. exact (auxv_pre_mono B _ S (spZ regs_c) memc Hhi (HAX Hi)).
Qed.

Lemma rjr_final : forall K E gone excl L A regs mem md L' A' regs' mem' md',
  call_pre_k B MR K L A regs mem md ->
  rjr K (spZ regs) E gone L A mem md L' A' mem' md' ->
  regs_preserved regs regs' ->
  (forall a n, gone (a, n) -> excl a) ->
  call_post_rec B MR K L A regs mem md E excl L' A' regs' mem' md'.
Proof using CTXO.
  intros K E gone excl L A regs mem md L' A' regs' mem' md' PRE R RP GX.
  destruct PRE as (PM & _).
  destruct R as (HM & HWA & HW' & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  split; [exact HM|]. split; [exact HW'|]. split; [exact HBd|]. split; [exact HL|].
  split; [intros p n Hp _; exact (ptr_addr_stable A L L' p n HWA Hp HL)|].
  split; [exact RP|]. split; [exact HV|].
  split.
  { intros a Hd Ho _ NS NE. apply HF; [exact (free_a_of_owned L A mem md a PM Hd Ho) | | | exact NE];
      intros H; apply NS; unfold scratch_k; [left | right]; exact H. }
  split.
  { intros p n i Hp _ NX Hi. apply (HKP p n i Hp); [|exact Hi]. intros G. exact (NX (GX _ _ G)). }
  intros a Ha. apply HSC. unfold scratch_k in Ha. exact Ha.
Qed.

Lemma rjr_others_kept : forall K S E gone L A mem md L' A' mem' md' (O : list (Z * Z)),
  rjr K S E gone L A mem md L' A' mem' md' ->
  (forall pn, gone pn -> In pn O) ->
  others_kept segs L A mem L' A' mem' O.
Proof.
  intros K S E gone L A mem md L' A' mem' md' O R GO p k Hp Hn.
  assert (Hg : ~ gone (ptr_addr L p, k)) by (intros G; exact (Hn (GO _ G))).
  pose proof (rjr_in_cur K S E gone L A mem md L' A' mem' md' p k R Hp Hg) as Hc.
  destruct R as (HM & HWA & HW' & HBd & HL & HLen & HV & HK1 & HK2 & HK3 & HF & HRM & HKP & HSC & HAX).
  split; [exact Hc|]. split; [exact (ptr_addr_stable A L L' p k HWA Hp HL)|].
  intros i Hi. exact (HKP p k i Hp Hg Hi).
Qed.

End Seq.
