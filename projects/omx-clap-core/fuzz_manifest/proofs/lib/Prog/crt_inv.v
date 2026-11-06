From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import MState Mem Frame Cells Step Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger ManifestB KindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import crt_lib.
Import ListNotations.
Local Open Scope Z_scope.

Section W.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis AX : YL01.AllocExtra B MR.
Hypothesis CTX : ManifestB.ctx_owned B MR.
Hypothesis SFA : statics_facts B.
Hypothesis SF : statics_free B MR.
Hypothesis SNE : statics_noerrno B.
Hypothesis ERR : errno_low B.
Hypothesis GS : guard_syms B.

Lemma rsegs_ne : rsegs <> [].
Proof. intros E. pose proof rsegs_reserved as R. rewrite E in R. discriminate R. Qed.

Lemma img_cover : forall a, 0x10000 <= a < 0x50000 -> in_img B a.
Proof.
  intros a Ha. unfold in_img. rewrite SEG. split; [exact rsegs_ne|].
  assert (C : 0x10000 <= a < 0x12000 \/ 0x12000 <= a < 0x1e000 \/ 0x1e000 <= a < 0x1f000 \/ 0x1f000 <= a < 0x50000) by lia.
  destruct C as [C|[C|[C|C]]];
    [ destruct (reserved_in 0x10000 0x2000 ltac:(cbn; tauto)) as (s & Hs & E1 & E2)
    | destruct (reserved_in 0x12000 0xc000 ltac:(cbn; tauto)) as (s & Hs & E1 & E2)
    | destruct (reserved_in 0x1e000 0x1000 ltac:(cbn; tauto)) as (s & Hs & E1 & E2)
    | destruct (reserved_in 0x1f000 0x31000 ltac:(cbn; tauto)) as (s & Hs & E1 & E2) ];
    exists s; rewrite E1, E2; (split; [exact Hs | lia]).
Qed.

Lemma off_img : forall x, ~ in_img B x -> x < 0x10000 \/ 0x50000 <= x.
Proof.
  intros x H. destruct (Z_lt_le_dec x 0x10000) as [H1|H1]; [left; exact H1|].
  destruct (Z_lt_le_dec x 0x50000) as [H2|H2]; [|right; exact H2]. exfalso. apply H, img_cover. lia.
Qed.

Lemma blk_off : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (a + i) /\ 4096 <= a + i < alloc_ceiling.
Proof.
  intros L A mem md a k i HM Hin Hi. split; [|exact (blocks_low B API L A mem md _ k i HM Hin Hi)].
  destruct (in_blocks L A a k Hin) as (p & Hp & ->).
  exact (YL01.ax_blocks_img AX L A mem md p k i HM Hp Hi).
Qed.

Lemma blk_present : forall L A mem md a k i, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= i < k ->
  present mem (a + i) /\ ~ owned B L A (a + i).
Proof.
  intros L A mem md a k i HM Hin Hi. destruct (in_blocks L A a k Hin) as (p & Hp & ->).
  destruct (mr_blocks _ _ (aa_laws API) L A mem md p k i HM Hp Hi) as (P & _ & _ & O). auto.
Qed.

Lemma blk_rw : forall L A mem md a k, MR L A mem md -> In (a, k) (blocks L A) -> 0 <= k ->
  exists junk, rw_cells rsegs mem a [CB (Z.to_nat k) junk].
Proof.
  intros L A mem md a k HM Hin Hk. destruct (in_blocks L A a k Hin) as (p & Hp & E).
  pose proof (mr_blocks_range _ _ (aa_laws API) L A mem md p k HM Hp) as R. rewrite <- E in R.
  pose proof alloc_ceiling_val as Hlt.
  apply present_rw_cells; [lia | lia | lia |].
  intros i Hi. exact (proj1 (blk_present L A mem md a k i HM Hin Hi)).
Qed.

Lemma owned_stable : forall L A m md L' A' m' md' a, MR L A m md -> MR L' A' m' md' ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> owned B L A a -> owned B L' A' a.
Proof.
  intros L A m md L' A' m' md' a H H' Hr Ho.
  pose proof (mr_owned_low _ _ (aa_laws API) L A m md a H Ho) as Hl.
  destruct Hr as [Hr|Hr]; [lia|].
  destruct Ho as [Ho|Ho]; [|right; exact Ho].
  apply (CTX L' A' m' md'); [exact H'|]. exact (YL01.ax_img AX L A m md a H Hr Ho).
Qed.

Definition crt_inv (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (blk : list (Z * Z)) (L1 : layout) (A1 : astate) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  MR L1 A1 mem1 md1 /\ WF A1 /\ bounded A1 /\ st_init_done A1 = true /\
  (exists vm, md1 = with_vmmaps vm md) /\
  (exists b1 b2, blocks L1 A1 = b1 ++ blk ++ b2 /\ blocks L A = b1 ++ b2) /\
  (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs mem1 (a + i) = mbyte rsegs mem (a + i)) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ scratch_k B K regs a ->
     ~ stat_writes a -> mbyte rsegs mem1 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem1 a)) /\
  (forall a, scratch_k B K regs a -> writable_at rsegs mem1 a) /\
  ro_agree rsegs mem1 /\ guard_kept B mem mem1.

Lemma inv_init : forall K L A regs mem md, call_pre_k B MR K L A regs mem md -> st_init_done A = true ->
  ro_agree rsegs mem -> crt_inv K L A regs mem md [] L A mem md.
Proof.
  intros K L A regs mem md PRE INIT MI.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact INIT|].
  split; [exists (m_vmmaps md); apply wvm_self|].
  split; [exists [], (blocks L A); split; reflexivity|].
  split; [intros; reflexivity|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [|split; [exact MI | intros i Hi; reflexivity]].
  intros a [Ha|Ha]; rewrite <- SEG; [apply HWS; exact Ha | apply HER; exact Ha].
Qed.

Lemma in_mid : forall (b1 c b2 : list (Z * Z)) x, In x (b1 ++ b2) -> In x (b1 ++ c ++ b2).
Proof.
  intros b1 c b2 x H. apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H|].
  right. apply in_or_app. right. exact H.
Qed.

Lemma not_stat_high : forall a, alloc_ceiling <= a -> ~ stat_writes a.
Proof. intros a Ha Hs. pose proof alloc_ceiling_val as Hac. unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in Hs. lia. Qed.

Lemma inv_bpost : forall K L A regs mem md blk L1 A1 mem1 md1 regs1 K1 L2 A2 regs2 mem2 md2,
  crt_inv K L A regs mem md blk L1 A1 mem1 md1 -> MR L A mem md ->
  alloc_ceiling + K <= spZ regs ->
  spZ regs - K <= spZ regs1 - K1 -> spZ regs1 <= spZ regs ->
  bpost B MR K1 stat_writes L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 ->
  st_init_done A2 = true ->
  crt_inv K L A regs mem md blk L2 A2 mem2 md2.
Proof.
  intros K L A regs mem md blk L1 A1 mem1 md1 regs1 K1 L2 A2 regs2 mem2 md2 IV HM0 HAC Hk1 Hk2 BP INIT.
  destruct IV as (HM1 & _ & _ & _ & (vm & Emd) & (b1 & b2 & Eb1 & Eb0) & Hbb & Hfr & Hsc & _ & GK1).
  destruct BP as (HM2 & HWF2 & HBD2 & _ & (vm2 & Emd2) & Ebl & Hbb2 & Hfr2 & Hsc2 & MI2 & GK2).
  rewrite SEG in Hbb2, Hfr2, Hsc2, MI2.
  split; [exact HM2|]. split; [exact HWF2|]. split; [exact HBD2|]. split; [exact INIT|].
  split; [exists vm2; rewrite Emd2, Emd; apply wvm_twice|].
  split; [exists b1, b2; rewrite Ebl; split; [exact Eb1 | exact Eb0]|].
  split.
  { intros a k i Hin Hi. rewrite (Hbb2 a k i); [exact (Hbb a k i Hin Hi) | | exact Hi].
    rewrite Eb1. apply in_mid. rewrite <- Eb0. exact Hin. }
  split.
  { intros a Hr Ho Hs Hw.
    assert (Ho1 : ~ owned B L1 A1 a) by (intros O; apply Ho; exact (owned_stable _ _ _ _ _ _ _ _ a HM1 HM0 Hr O)).
    assert (Ho2 : ~ owned B L2 A2 a) by (intros O; apply Ho; exact (owned_stable _ _ _ _ _ _ _ _ a HM2 HM0 Hr O)).
    assert (Hs1 : ~ scratch_k B K1 regs1 a) by (intros [S|S]; apply Hs; [left; lia | right; exact S]).
    destruct (Hfr2 a Hr Ho1 Ho2 Hs1 Hw) as [E1 W1]. destruct (Hfr a Hr Ho Hs Hw) as [E0 W0].
    split; [rewrite E1; exact E0 | rewrite W0; exact W1]. }
  split; [|split; [exact MI2 | intros i Hi; rewrite (GK2 i Hi); exact (GK1 i Hi)]].
  intros a Hs.
  assert (D : scratch_k B K1 regs1 a \/ (spZ regs - K <= a < spZ regs /\ ~ scratch_k B K1 regs1 a)).
  { destruct Hs as [Hs|Hs]; [|left; right; exact Hs].
    destruct (Z_lt_le_dec a (spZ regs1 - K1)) as [Hlo|Hlo];
      [| destruct (Z_lt_le_dec a (spZ regs1)) as [Hhi|Hhi]; [left; left; lia|]];
      (right; split; [exact Hs|]; intros [S|S]; [lia | unfold errno_low in ERR; pose proof alloc_ceiling_val; lia]). }
  destruct D as [D|[D1 D2]]; [exact (Hsc2 a D)|].
  pose proof alloc_ceiling_val as Hacv.
  pose proof (zr_word (getr regs 2)) as Z. unfold inr64 in Z. unfold spZ in *.
  assert (Hr : alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) by (left; lia).
  assert (Ho1 : ~ owned B L1 A1 a) by (intros O; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 O); lia).
  assert (Ho2 : ~ owned B L2 A2 a) by (intros O; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 O); lia).
  destruct (Hfr2 a Hr Ho1 Ho2 D2 (not_stat_high a ltac:(lia))) as [_ W1].
  apply W1. apply Hsc. left. exact D1.
Qed.

Lemma blk_in : forall L1 A1 b1 blk b2 a k, blocks L1 A1 = b1 ++ blk ++ b2 -> In (a, k) blk -> In (a, k) (blocks L1 A1).
Proof. intros L1 A1 b1 blk b2 a k E H. rewrite E. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma inv_munch : forall K L A regs mem md blk L1 A1 mem1 md1 mem2 W,
  crt_inv K L A regs mem md blk L1 A1 mem1 md1 ->
  munch W mem1 mem2 -> wmono rsegs mem1 mem2 -> ro_agree rsegs mem2 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x ->
     (spZ regs - K <= x < spZ regs) \/ exists a k, In (a, k) blk /\ a <= x < a + k) ->
  alloc_ceiling + K <= spZ regs ->
  crt_inv K L A regs mem md blk L1 A1 mem2 md1.
Proof.
  intros K L A regs mem md blk L1 A1 mem1 md1 mem2 W IV MU WM MI2 HW HAC.
  destruct IV as (HM1 & HWF & HBD & INIT & Hmd & (b1 & b2 & Eb1 & Eb0) & Hbb & Hfr & Hsc & _ & GK1).
  pose proof alloc_ceiling_val as Hacv.
  assert (OW : forall x, 0 <= x < 2 ^ 64 -> x < alloc_ceiling -> ~ outside W x ->
            exists a k, In (a, k) (blocks L1 A1) /\ In (a, k) blk /\ a <= x < a + k).
  { intros x Hx Hl Ho. destruct (HW x Hx Ho) as [S|(a & k & Hin & Hr)]; [lia|].
    exists a, k. split; [exact (blk_in L1 A1 b1 blk b2 a k Eb1 Hin)|]. auto. }
  assert (OWN : forall a, owned B L1 A1 a -> outside W a).
  { intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 Ho) as Hl.
    destruct (outside_dec W a) as [O|O]; [exact O|]. exfalso.
    destruct (OW a ltac:(lia) ltac:(lia) O) as (a' & k' & Hin & _ & Hr).
    apply (proj2 (blk_present L1 A1 mem1 md1 a' k' (a - a') HM1 Hin ltac:(lia))).
    replace (a' + (a - a')) with a by lia. exact Ho. }
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & Hm).
  split.
  { eapply (mr_frame _ _ (aa_laws API) L1 A1 mem1 mem2 md1 md1 HM1).
    - intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 Ho).
      apply (mbyte_munch _ W); [exact MU | lia | exact (OWN a Ho)].
    - intros a Ho Hp. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 Ho).
      apply (present_munch W mem1); [exact MU | lia | exact (OWN a Ho) | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) L1 A1 mem1 md1 p n i HM1 Hin Hi) as (Hp & H1 & H2 & _).
      destruct (outside_dec W (ptr_addr L1 p + i)) as [O|O].
      + apply (present_munch W mem1); [exact MU | lia | exact O | exact Hp].
      + apply writable_off_present; [lia | |].
        * apply off_img. exact (YL01.ax_blocks_img AX L1 A1 mem1 md1 p n i HM1 Hin Hi).
        * apply WM. pose proof (present_writable B mem1 _ Hp) as PW. unfold writable_at in PW. rewrite SEG in PW. exact PW.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact INIT|]. split; [exact Hmd|].
  split; [exists b1, b2; split; [exact Eb1 | exact Eb0]|].
  split.
  { intros a k i Hin Hi. rewrite <- (Hbb a k i Hin Hi).
    assert (Hin1 : In (a, k) (blocks L1 A1)) by (rewrite Eb1; apply in_mid; rewrite <- Eb0; exact Hin).
    destruct (blk_off L1 A1 mem1 md1 a k i HM1 Hin1 Hi) as [_ Hr].
    apply (mbyte_munch _ W); [exact MU | lia |].
    destruct (outside_dec W (a + i)) as [O|O]; [exact O|]. exfalso.
    destruct (HW (a + i) ltac:(lia) O) as [S|(a' & k' & Hin' & Hr')]; [lia|].
    pose proof (mr_blocks_disjoint _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as PD. rewrite Eb1 in PD.
    pose proof (pairwise_mid b1 blk b2 PD (a, k) (a', k') ltac:(rewrite <- Eb0; exact Hin) Hin') as D.
    unfold ranges_disjoint in D. cbn in D. lia. }
  split.
  { intros a Hr Ho Hs Hw. destruct (Hfr a Hr Ho Hs Hw) as [E0 W0].
    assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B SEG a Hr); lia]).
    assert (O : outside W a).
    { destruct (outside_dec W a) as [O|O]; [exact O|]. exfalso.
      destruct (HW a Ha O) as [S|(a' & k' & Hin' & Hr')]; [apply Hs; left; exact S|].
      destruct (blk_off L1 A1 mem1 md1 a' k' (a - a') HM1 (blk_in L1 A1 b1 blk b2 a' k' Eb1 Hin') ltac:(lia)) as [NI LO].
      replace (a' + (a - a')) with a in NI, LO by lia.
      destruct Hr as [Hr|Hr]; [lia | exact (NI Hr)]. }
    split.
    - rewrite (mbyte_munch _ W mem1 mem2 a MU Ha O). exact E0.
    - rewrite W0. exact (writable_munch _ W mem1 mem2 a MU Ha O). }
  split; [intros a Hs; apply WM; exact (Hsc a Hs)|].
  split; [exact MI2|].
  intros i Hi. unfold guard_kept in *. rewrite <- (GK1 i Hi). destruct GS as [G1 _]. rewrite G1 in *.
  apply (mbyte_munch _ W); [exact MU | lia |].
  destruct (outside_dec W (0x1e0b8 + i)) as [O|O]; [exact O|]. exfalso.
  destruct (HW (0x1e0b8 + i) ltac:(lia) O) as [S|(a' & k' & Hin' & Hr')]; [lia|].
  destruct (blk_off L1 A1 mem1 md1 a' k' (0x1e0b8 + i - a') HM1 (blk_in L1 A1 b1 blk b2 a' k' Eb1 Hin') ltac:(lia)) as [NI _].
  apply NI. apply img_cover. lia.
Qed.

Lemma frame_scr_step : forall K L A regs mem md L1 A1 mem1 md1 regs1 (E : Z -> Prop) L2 A2 mem2 md2,
  MR L A mem md -> MR L1 A1 mem1 md1 -> MR L2 A2 mem2 md2 -> alloc_ceiling + K <= spZ regs ->
  spZ regs - K <= spZ regs1 - ALLOC_STACK -> spZ regs1 <= spZ regs ->
  (forall a, E a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L1 A1 a -> ~ owned B L2 A2 a ->
     ~ scratch B regs1 a -> ~ E a ->
     mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\
     (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)) ->
  (forall a, scratch B regs1 a -> writable_at (ms_segs B) mem2 a) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ scratch_k B K regs a ->
     ~ stat_writes a -> mbyte rsegs mem1 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem1 a)) ->
  (forall a, scratch_k B K regs a -> writable_at rsegs mem1 a) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ scratch_k B K regs a ->
     ~ stat_writes a -> mbyte rsegs mem2 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem2 a)) /\
  (forall a, scratch_k B K regs a -> writable_at rsegs mem2 a).
Proof.
  intros K L A regs mem md L1 A1 mem1 md1 regs1 E L2 A2 mem2 md2 HM0 HM1 HM2 HAC Hk1 Hk2 HE Hfr2 Hsc2 Hfr Hsc.
  rewrite SEG in Hfr2, Hsc2. pose proof alloc_ceiling_val as Hacv.
  split.
  { intros a Hr Ho Hs Hw.
    assert (Ho1 : ~ owned B L1 A1 a) by (intros O; apply Ho; exact (owned_stable _ _ _ _ _ _ _ _ a HM1 HM0 Hr O)).
    assert (Ho2 : ~ owned B L2 A2 a) by (intros O; apply Ho; exact (owned_stable _ _ _ _ _ _ _ _ a HM2 HM0 Hr O)).
    assert (Hs1 : ~ scratch B regs1 a) by (intros [S|S]; apply Hs; [left; unfold ALLOC_STACK in *; lia | right; exact S]).
    assert (HnE : ~ E a) by (intros He; destruct (HE a He) as [H1 H2]; destruct Hr as [Hr|Hr]; [lia | exact (H2 Hr)]).
    destruct (Hfr2 a Hr Ho1 Ho2 Hs1 HnE) as [E1 W1]. destruct (Hfr a Hr Ho Hs Hw) as [E0 W0].
    split; [rewrite E1; exact E0 | rewrite W0; exact W1]. }
  intros a Hs.
  assert (D : scratch B regs1 a \/ (spZ regs - K <= a < spZ regs /\ ~ scratch B regs1 a)).
  { destruct Hs as [Hs|Hs]; [|left; right; exact Hs].
    destruct (Z_lt_le_dec a (spZ regs1 - ALLOC_STACK)) as [Hlo|Hlo];
      [| destruct (Z_lt_le_dec a (spZ regs1)) as [Hhi|Hhi]; [left; left; lia|]];
      (right; split; [exact Hs|]; intros [S|S]; [lia | unfold errno_low in ERR; lia]). }
  destruct D as [D|[D1 D2]]; [exact (Hsc2 a D)|].
  pose proof (zr_word (getr regs 2)) as Z. unfold inr64 in Z. unfold spZ in *.
  assert (Hr : alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) by (left; lia).
  assert (Ho1 : ~ owned B L1 A1 a) by (intros O; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 O); lia).
  assert (Ho2 : ~ owned B L2 A2 a) by (intros O; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 O); lia).
  assert (HnE : ~ E a) by (intros He; destruct (HE a He); lia).
  destruct (Hfr2 a Hr Ho1 Ho2 D2 HnE) as [_ W1].
  apply W1. apply Hsc. left. exact D1.
Qed.

Lemma inv_malloc : forall K L A regs mem md L1 A1 mem1 md1 regs1 L2 A2 regs2 mem2 md2 res sz,
  crt_inv K L A regs mem md [] L1 A1 mem1 md1 -> MR L A mem md -> alloc_ceiling + K <= spZ regs ->
  spZ regs - K <= spZ regs1 - ALLOC_STACK -> spZ regs1 <= spZ regs ->
  call_post B MR L1 A1 regs1 mem1 md1 (fun _ => False) L2 A2 regs2 mem2 md2 ->
  (exists b1 b2, blocks L2 A2 = b1 ++ (res, sz) :: b2 /\ blocks L1 A1 = b1 ++ b2) ->
  (forall a k i, In (a, k) (blocks L1 A1) -> 0 <= i < k ->
     mbyte (ms_segs B) mem2 (a + i) = mbyte (ms_segs B) mem1 (a + i)) ->
  ro_agree rsegs mem2 -> guard_kept B mem1 mem2 -> st_init_done A2 = true ->
  crt_inv K L A regs mem md [(res, sz)] L2 A2 mem2 md2.
Proof.
  intros K L A regs mem md L1 A1 mem1 md1 regs1 L2 A2 regs2 mem2 md2 res sz IV HM0 HAC Hk1 Hk2 CP
    (c1 & c2 & Ec2 & Ec1) KB MI2 GK2 INIT.
  destruct IV as (HM1 & _ & _ & _ & (vm & Emd) & (b1 & b2 & Eb1 & Eb0) & Hbb & Hfr & Hsc & _ & GK1).
  destruct CP as (HM2 & HWF2 & HBD2 & _ & _ & _ & (vm2 & Emd2) & Hfr2 & _ & Hsc2).
  rewrite SEG in KB.
  assert (EL : blocks L1 A1 = blocks L A) by (rewrite Eb1, Eb0; reflexivity).
  destruct (frame_scr_step K L A regs mem md L1 A1 mem1 md1 regs1 (fun _ => False) L2 A2 mem2 md2
    HM0 HM1 HM2 HAC Hk1 Hk2 ltac:(intros a []) Hfr2 Hsc2 Hfr Hsc) as [F S].
  split; [exact HM2|]. split; [exact HWF2|]. split; [exact HBD2|]. split; [exact INIT|].
  split; [exists vm2; rewrite Emd2, Emd; apply wvm_twice|].
  split; [exists c1, c2; split; [exact Ec2 | rewrite <- EL; exact Ec1]|].
  split; [intros a k i Hin Hi; rewrite (KB a k i ltac:(rewrite EL; exact Hin) Hi); exact (Hbb a k i Hin Hi)|].
  split; [exact F|]. split; [exact S|]. split; [exact MI2|].
  intros i Hi. rewrite (GK2 i Hi). exact (GK1 i Hi).
Qed.

Lemma inv_free : forall K L A regs mem md L1 A1 mem1 md1 regs1 L2 A2 regs2 mem2 md2 res sz,
  crt_inv K L A regs mem md [(res, sz)] L1 A1 mem1 md1 -> MR L A mem md -> alloc_ceiling + K <= spZ regs ->
  spZ regs - K <= spZ regs1 - ALLOC_STACK -> spZ regs1 <= spZ regs -> 0 < sz ->
  call_post B MR L1 A1 regs1 mem1 md1 (fun a => res <= a < res + sz) L2 A2 regs2 mem2 md2 ->
  (exists b1 b2, blocks L1 A1 = b1 ++ (res, sz) :: b2 /\ blocks L2 A2 = b1 ++ b2) ->
  (forall a k i, In (a, k) (blocks L1 A1) -> a <> res -> 0 <= i < k ->
     mbyte (ms_segs B) mem2 (a + i) = mbyte (ms_segs B) mem1 (a + i)) ->
  ro_agree rsegs mem2 -> guard_kept B mem1 mem2 -> st_init_done A2 = true ->
  crt_inv K L A regs mem md [] L2 A2 mem2 md2.
Proof.
  intros K L A regs mem md L1 A1 mem1 md1 regs1 L2 A2 regs2 mem2 md2 res sz IV HM0 HAC Hk1 Hk2 Hsz CP
    (c1 & c2 & Ec1 & Ec2) KB MI2 GK2 INIT.
  destruct IV as (HM1 & _ & _ & _ & (vm & Emd) & (b1 & b2 & Eb1 & Eb0) & Hbb & Hfr & Hsc & _ & GK1).
  destruct CP as (HM2 & HWF2 & HBD2 & _ & _ & _ & (vm2 & Emd2) & Hfr2 & _ & Hsc2).
  rewrite SEG in KB.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as PD.
  assert (Hres : forall x, res <= x < res + sz -> x < alloc_ceiling /\ ~ in_img B x).
  { intros x Hx. destruct (blk_off L1 A1 mem1 md1 res sz (x - res) HM1 (blk_in L1 A1 b1 [(res, sz)] b2 res sz Eb1 (or_introl eq_refl)) ltac:(lia)) as [NI LO].
    replace (res + (x - res)) with x in NI, LO by lia. split; [lia | exact NI]. }
  destruct (frame_scr_step K L A regs mem md L1 A1 mem1 md1 regs1 (fun a => res <= a < res + sz) L2 A2 mem2 md2
    HM0 HM1 HM2 HAC Hk1 Hk2 Hres Hfr2 Hsc2 Hfr Hsc) as [F S].
  assert (EQ : b1 = c1 /\ b2 = c2).
  { cbn in Eb1. rewrite Eb1 in PD.
    destruct (pairwise_notin b1 b2 (res, sz) PD Hsz) as [N1 _].
    rewrite Eb1 in Ec1. pose proof PD as PD2. rewrite Ec1 in PD2.
    destruct (pairwise_notin c1 c2 (res, sz) PD2 Hsz) as [N2 _].
    exact (app_cons_unique b1 b2 c1 c2 (res, sz) N1 N2 Ec1). }
  destruct EQ as [<- <-].
  split; [exact HM2|]. split; [exact HWF2|]. split; [exact HBD2|]. split; [exact INIT|].
  split; [exists vm2; rewrite Emd2, Emd; apply wvm_twice|].
  split; [exists b1, b2; split; [exact Ec2 | exact Eb0]|].
  split.
  { intros a k i Hin Hi. rewrite <- (Hbb a k i Hin Hi).
    apply (KB a k i); [rewrite Eb1; apply in_mid; rewrite <- Eb0; exact Hin | | exact Hi].
    rewrite Eb1 in PD.
    pose proof (pairwise_mid b1 [(res, sz)] b2 PD (a, k) (res, sz) ltac:(rewrite <- Eb0; exact Hin) (or_introl eq_refl)) as D.
    unfold ranges_disjoint in D. cbn in D. lia. }
  split; [exact F|]. split; [exact S|]. split; [exact MI2|].
  intros i Hi. rewrite (GK2 i Hi). exact (GK1 i Hi).
Qed.

Lemma bpost_of_inv : forall K L A regs mem md L1 A1 regs1 mem1 md1,
  crt_inv K L A regs mem md [] L1 A1 mem1 md1 -> regs_preserved regs regs1 ->
  bpost B MR K stat_writes L A regs mem md L1 A1 regs1 mem1 md1.
Proof.
  intros K L A regs mem md L1 A1 regs1 mem1 md1 IV RP.
  destruct IV as (HM1 & HWF & HBD & _ & Hmd & (b1 & b2 & Eb1 & Eb0) & Hbb & Hfr & Hsc & MI1 & GK1).
  split; [exact HM1|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact RP|]. split; [exact Hmd|].
  split; [rewrite Eb1, Eb0; reflexivity|].
  rewrite SEG.
  split; [exact Hbb|].
  split; [intros a Hr Ho _ Hs Hw; exact (Hfr a Hr Ho Hs Hw)|].
  split; [exact Hsc|]. split; [exact MI1 | exact GK1].
Qed.

End W.
