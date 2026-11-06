From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestModel ManifestMem ManifestB names_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_no_overread_c check_no_overread_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import slot_steps_c.
Local Open Scope Z_scope.

Definition SLK : Z := 65536.

Lemma strnlen_range : forall k buf, 0 <= k -> 0 <= strnlen_res k buf <= k.
Proof.
  intros k buf Hk. unfold strnlen_res. destruct (find_byte 0 (firstn (Z.to_nat k) buf)) as [i|] eqn:E; [|lia].
  destruct (find_byte_Some _ _ _ E) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

Lemma strnlen_nz : forall k buf, 0 <= k ->
  Forall (fun b => bv_unsigned b <> 0) (firstn (Z.to_nat (strnlen_res k buf)) buf).
Proof.
  intros k buf Hk. apply Forall_forall. intros x Hx. apply In_nth_error in Hx as (j & Hj).
  assert (Hjl : (j < length (firstn (Z.to_nat (strnlen_res k buf)) buf))%nat)
    by (apply nth_error_Some; rewrite Hj; discriminate).
  rewrite length_firstn in Hjl. rewrite nth_error_firstn in Hj.
  destruct (Nat.ltb_spec j (Z.to_nat (strnlen_res k buf))) as [Hlt|]; [|discriminate].
  pose proof (strnlen_range k buf Hk) as R.
  assert (Hk' : nth_error (firstn (Z.to_nat k) buf) j = Some x)
    by (rewrite nth_error_firstn; destruct (Nat.ltb_spec j (Z.to_nat k)); [exact Hj | lia]).
  unfold strnlen_res in Hlt. destruct (find_byte 0 (firstn (Z.to_nat k) buf)) as [i|] eqn:E.
  - destruct (find_byte_Some _ _ _ E) as (_ & _ & Hmin). apply (Hmin j x); [lia | exact Hk'].
  - exact (find_byte_None _ _ E j x Hk').
Qed.

Lemma strnlen_len : forall k buf, 0 <= k <= Z.of_nat (length buf) ->
  Z.of_nat (length (firstn (Z.to_nat (strnlen_res k buf)) buf)) = strnlen_res k buf.
Proof.
  intros k buf Hk. pose proof (strnlen_range k buf ltac:(lia)) as R.
  rewrite length_firstn. lia.
Qed.

Lemma sl_k_range : forall pl, 0 <= sl_k pl /\ sl_s pl + sl_k pl <= Z.of_nat (length pl) /\ sl_k pl <= 255.
Proof.
  intros [|b pl]; cbn [sl_k sl_s length]; [lia|].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma sl_s_range : forall pl, (sl_s pl = 0 /\ pl = []) \/ (sl_s pl = 1 /\ pl <> []).
Proof. intros [|b pl]; [left | right]; split; try reflexivity; discriminate. Qed.

Lemma sl_ubuf_len : forall pl, Z.of_nat (length (sl_ubuf pl)) = sl_k pl.
Proof.
  intros pl. pose proof (sl_k_range pl) as (R1 & R2 & _). pose proof (sl_s_range pl) as S.
  unfold sl_ubuf. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma sl_tbuf_len : forall pl, Z.of_nat (length (sl_tbuf pl)) = Z.of_nat (length pl) - sl_s pl - sl_k pl.
Proof.
  intros pl. pose proof (sl_k_range pl) as (R1 & R2 & _). pose proof (sl_s_range pl) as S.
  unfold sl_tbuf. rewrite length_skipn. lia.
Qed.

Lemma sl_un_range : forall pl, 0 <= sl_un pl <= sl_k pl.
Proof. intros pl. apply strnlen_range. apply sl_k_range. Qed.

Lemma sl_tn_range : forall pl, 0 <= sl_tn pl <= Z.of_nat (length (sl_tbuf pl)).
Proof. intros pl. apply strnlen_range. lia. Qed.

Lemma sl_ub_len : forall pl, Z.of_nat (length (sl_ub pl)) = sl_un pl.
Proof. intros pl. apply strnlen_len. rewrite sl_ubuf_len. pose proof (sl_k_range pl). lia. Qed.

Lemma sl_tb_len : forall pl, Z.of_nat (length (sl_tb pl)) = sl_tn pl.
Proof. intros pl. apply strnlen_len. lia. Qed.

Lemma sl_ub_nz : forall pl, Forall (fun b => bv_unsigned b <> 0) (sl_ub pl).
Proof. intros pl. apply strnlen_nz. apply sl_k_range. Qed.

Lemma sl_tb_nz : forall pl, Forall (fun b => bv_unsigned b <> 0) (sl_tb pl).
Proof. intros pl. apply strnlen_nz. lia. Qed.

Lemma bytes_at_skip_first : forall segs m a bs (x y : nat), bytes_at segs m a bs -> (x + y <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat x) (firstn y (skipn x bs)).
Proof.
  intros segs m a bs x y H Hl.
  rewrite <- (firstn_skipn x bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn y (skipn x bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma sl_ub_bytes : forall segs m p pl, bytes_at segs m p pl -> bytes_at segs m (sl_uri p pl) (sl_ub pl).
Proof.
  intros segs m p pl H. pose proof (sl_k_range pl) as (R1 & R2 & _). pose proof (sl_un_range pl) as U.
  pose proof (sl_s_range pl) as S.
  unfold sl_ub, sl_ubuf, sl_uri. rewrite firstn_firstn, Nat.min_l by lia.
  replace (p + sl_s pl) with (p + Z.of_nat (Z.to_nat (sl_s pl))) by lia.
  apply bytes_at_skip_first; [exact H | lia].
Qed.

Lemma sl_tb_bytes : forall segs m p pl, bytes_at segs m p pl -> bytes_at segs m (sl_text p pl) (sl_tb pl).
Proof.
  intros segs m p pl H. pose proof (sl_k_range pl) as (R1 & R2 & _). pose proof (sl_tn_range pl) as U.
  pose proof (sl_s_range pl) as S. rewrite sl_tbuf_len in U.
  unfold sl_tb, sl_tbuf, sl_text.
  replace (p + sl_s pl + sl_k pl) with (p + Z.of_nat (Z.to_nat (sl_s pl + sl_k pl))) by lia.
  apply bytes_at_skip_first; [exact H | lia].
Qed.

Section KI.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.

Definition kinv (K : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop :=
  MR L A mem md /\ WF A /\ bounded A /\
  (exists vm, md = with_vmmaps vm md0) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ static_owned B a ->
     ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) -> ~ scratch_k B K regs0 a -> ~ stat_writes a ->
     mbyte rsegs mem a = mbyte rsegs mem0 a /\ (writable_at rsegs mem0 a <-> writable_at rsegs mem a)) /\
  (forall a, scratch_k B K regs0 a -> writable_at rsegs mem a) /\
  (forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k -> mbyte rsegs mem (a + i) = mbyte rsegs mem0 (a + i)) /\
  (forall x, In x (blocks L0 A0) -> In x (blocks L A)) /\
  ro_agree rsegs mem.

Lemma kinv_init : forall K L A regs mem md, MR L A mem md -> WF A -> bounded A ->
  (forall a, spZ regs - K <= a < spZ regs -> writable_at (ms_segs B) mem a) ->
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at (ms_segs B) mem a) ->
  ro_agree rsegs mem -> kinv K L A regs mem md L A mem md.
Proof.
  intros K L A regs mem md HM HWF HBD HWS HER HMI.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|].
  split; [exists (m_vmmaps md); apply with_vmmaps_self'|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros a [Ha|Ha]; rewrite <- HS; [apply HWS | apply HER]; exact Ha|].
  split; [intros; reflexivity|]. split; [intros x Hx; exact Hx|]. exact HMI.
Qed.

Lemma kinv_kindA : forall K L0 A0 regs0 mem0 md0 L A mem md mem' W,
  kinv K L0 A0 regs0 mem0 md0 L A mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  alloc_ceiling + K <= spZ regs0 ->
  (forall x, 0 <= x < 2 ^ 64 -> outside W x \/ (spZ regs0 - K <= x < spZ regs0) \/
     (exists r n, In (r, n) (blocks L A) /\ ~ In (r, n) (blocks L0 A0) /\ r <= x < r + n /\ present mem' x)) ->
  kinv K L0 A0 regs0 mem0 md0 L A mem' md.
Proof.
  intros K L0 A0 regs0 mem0 md0 L A mem md mem' W (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI) MU WM MI' HK CLS.
  pose proof alloc_ceiling_val as Hac.
  assert (OWN : forall a, owned B L A a -> 0 <= a < alloc_ceiling /\ outside W a).
  { intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md a HM Ho) as Hl. split; [exact Hl|].
    destruct (CLS a ltac:(lia)) as [Hout | [Hst | (r & n & Hin & _ & Hr & _)]]; [exact Hout | lia |].
    exfalso. destruct (in_blocks L A r n Hin) as (p & Hp & ->).
    destruct (mr_blocks _ _ (aa_laws API) L A mem md p n (a - ptr_addr L p) HM Hp ltac:(lia)) as (_ & _ & _ & Hno).
    replace (ptr_addr L p + (a - ptr_addr L p)) with a in Hno by lia. exact (Hno Ho). }
  split.
  { destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & Hm).
    eapply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
    - intros a Ho. destruct (OWN a Ho) as [Hl0 Hout]. apply (mbyte_munch _ W); [exact MU | lia | exact Hout].
    - intros a Ho Hp. destruct (OWN a Ho) as [Hl0 Hout]. apply (present_munch W mem); [exact MU | lia | exact Hout | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) L A mem md p n i HM Hin Hi) as (Hp & H1 & H2 & _).
      destruct (CLS (ptr_addr L p + i) ltac:(lia)) as [Hout | [Hst | (r & k & _ & _ & _ & Hpr)]].
      + apply (present_munch W mem); [exact MU | lia | exact Hout | exact Hp].
      + lia.
      + exact Hpr.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  split; [exact HWF|]. split; [exact HBD|]. split; [exact HMD|].
  split.
  { intros a Hr Hs Hc Hsc Hst. destruct (HFR a Hr Hs Hc Hsc Hst) as [E1 E2].
    assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B HS a Hr); lia]).
    destruct (CLS a Ha) as [Hout | [Hstk | (r & n & Hin & _ & Hrn & _)]].
    - split.
      + rewrite (mbyte_munch _ W mem mem' a MU Ha Hout). exact E1.
      + rewrite E2. apply (writable_munch _ W mem mem' a MU Ha Hout).
    - exfalso. apply Hsc. left. exact Hstk.
    - exfalso. pose proof (blocks_low B API L A mem md r n (a - r) HM Hin ltac:(lia)) as Hlow.
      pose proof (block_not_img B API AX L A mem md r n (a - r) HM Hin ltac:(lia)) as Hni.
      replace (r + (a - r)) with a in Hlow, Hni by lia. destruct Hr as [Hr|Hr]; [lia | exact (Hni Hr)]. }
  split; [intros a Hs; apply WM; apply HSC; exact Hs|].
  split.
  { intros a k i Hin Hi. rewrite <- (HB0 a k i Hin Hi).
    pose proof (HP0 _ Hin) as Hin'.
    pose proof (blocks_low B API L A mem md a k i HM Hin' Hi) as Hlow.
    destruct (CLS (a + i) ltac:(lia)) as [Hout | [Hstk | (r & n & Hrin & Hrn0 & Hrn & _)]].
    - apply (mbyte_munch _ W); [exact MU | lia | exact Hout].
    - lia.
    - exfalso. assert (Hne : (a, k) <> (r, n)) by (intros E; rewrite E in Hin; exact (Hrn0 Hin)).
      destruct (blocks_sep B API L A mem md (a, k) (r, n) HM Hin' Hrin Hne) as [D|D]; cbn in D; lia. }
  split; [exact HP0 | exact MI'].
Qed.

Lemma kinv_step : forall K L0 A0 regs0 mem0 md0 L A mem md L' A' mem' md' (Kc spc : Z) (E : Z -> Prop),
  kinv K L0 A0 regs0 mem0 md0 L A mem md ->
  MR L' A' mem' md' -> WF A' -> bounded A' -> (exists vm', md' = with_vmmaps vm' md) ->
  spZ regs0 - K <= spc - Kc -> spc <= spZ regs0 -> alloc_ceiling + K <= spZ regs0 ->
  (forall a, E a -> (a < alloc_ceiling /\ ~ in_img B a) \/ stat_writes a) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
     ~ (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4) -> ~ E a ->
     mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a)) ->
  (forall a, (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4) -> writable_at rsegs mem' a) ->
  (forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k -> mbyte rsegs mem' (a + i) = mbyte rsegs mem (a + i)) ->
  (forall x, In x (blocks L0 A0) -> In x (blocks L' A')) ->
  ro_agree rsegs mem' ->
  kinv K L0 A0 regs0 mem0 md0 L' A' mem' md'.
Proof.
  intros K L0 A0 regs0 mem0 md0 L A mem md L' A' mem' md' Kc spc E
    (HM & HWF & HBD & (vm & HMD) & HFR & HSC & HB0 & HP0 & HMI) HM' HWF' HBD' (vm' & HMD') Hk1 Hk2 HK HE
    FR SC B0 P0 MI'.
  pose proof alloc_ceiling_val as Hac.
  assert (HSW : forall a, stat_writes a -> a < alloc_ceiling) by (unfold stat_writes, G_LIVE, G_COUNT, G_FAIL; lia).
  split; [exact HM'|]. split; [exact HWF'|]. split; [exact HBD'|].
  split; [exists vm'; rewrite HMD', HMD; apply with_vmmaps_twice'|].
  split.
  { intros a Hr Hs Hc Hsc Hst. destruct (HFR a Hr Hs Hc Hsc Hst) as [E1 E2].
    assert (Hn1 : ~ owned B L A a) by (exact (not_owned_any B API AX L A mem md a HM Hr Hs Hc)).
    assert (Hn2 : ~ owned B L' A' a) by (exact (not_owned_any B API AX L' A' mem' md' a HM' Hr Hs Hc)).
    assert (Hn3 : ~ (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4)).
    { intros [H|H]; apply Hsc; unfold scratch_k, spZ in *; [left; lia | right; exact H]. }
    assert (Hn4 : ~ E a).
    { intros He. destruct (HE a He) as [(H1 & H2)|H]; [destruct Hr as [Hr|Hr]; [lia | exact (H2 Hr)] | exact (Hst H)]. }
    destruct (FR a Hr Hn1 Hn2 Hn3 Hn4) as [F1 F2].
    split; [rewrite F1; exact E1 | rewrite E2; exact F2]. }
  split.
  { intros a Hs.
    assert (D : (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4) \/
                ~ (spc - Kc <= a < spc \/ errno_addr B <= a < errno_addr B + 4)).
    { destruct (Z.le_gt_cases (spc - Kc) a); destruct (Z.lt_ge_cases a spc);
        destruct (Z.le_gt_cases (errno_addr B) a); destruct (Z.lt_ge_cases a (errno_addr B + 4));
        first [left; lia | right; lia]. }
    destruct D as [D|D]; [exact (SC a D)|].
    destruct Hs as [Hs|Hs]; [|exfalso; apply D; right; exact Hs].
    unfold spZ in Hs, HK.
    pose proof (zr_word (getr regs0 2)) as R. unfold inr64 in R.
    assert (Hr : alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) by (left; lia).
    assert (Hn1 : ~ owned B L A a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho); lia).
    assert (Hn2 : ~ owned B L' A' a) by (intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho); lia).
    assert (Hn4 : ~ E a) by (intros He; destruct (HE a He) as [(H1 & _)|H]; [lia | pose proof (HSW a H); lia]).
    destruct (FR a Hr Hn1 Hn2 D Hn4) as [_ F2]. apply F2. apply HSC. left. unfold spZ. exact Hs. }
  split.
  { intros a k i Hin Hi. rewrite (B0 a k i Hin Hi). exact (HB0 a k i Hin Hi). }
  split; [exact P0 | exact MI'].
Qed.

Lemma kinv_MR : forall K L0 A0 regs0 mem0 md0 L A m md, kinv K L0 A0 regs0 mem0 md0 L A m md -> MR L A m md.
Proof. intros K L0 A0 regs0 mem0 md0 L A m md (H & _). exact H. Qed.

Lemma kinv_md : forall K L0 A0 regs0 mem0 md0 L A m md, kinv K L0 A0 regs0 mem0 md0 L A m md ->
  m_halted md = None /\ m_vm_lazy md = [].
Proof.
  intros K L0 A0 regs0 mem0 md0 L A m md (H & _).
  destruct (mr_model _ _ (aa_laws API) L A m md H) as (H1 & H2 & _). auto.
Qed.

Lemma kinv_mi : forall K L0 A0 regs0 mem0 md0 L A m md, kinv K L0 A0 regs0 mem0 md0 L A m md -> ro_agree rsegs m.
Proof. intros K L0 A0 regs0 mem0 md0 L A m md (_ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma kinv_inc : forall K L0 A0 regs0 mem0 md0 L A m md, kinv K L0 A0 regs0 mem0 md0 L A m md ->
  forall x, In x (blocks L0 A0) -> In x (blocks L A).
Proof. intros K L0 A0 regs0 mem0 md0 L A m md (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma kinv_b0 : forall K L0 A0 regs0 mem0 md0 L A m md, kinv K L0 A0 regs0 mem0 md0 L A m md ->
  forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k -> mbyte rsegs m (a + i) = mbyte rsegs mem0 (a + i).
Proof. intros K L0 A0 regs0 mem0 md0 L A m md (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma kinv_sc : forall K L0 A0 regs0 mem0 md0 L A m md, kinv K L0 A0 regs0 mem0 md0 L A m md ->
  forall a, scratch_k B K regs0 a -> writable_at rsegs m a.
Proof. intros K L0 A0 regs0 mem0 md0 L A m md (_ & _ & _ & _ & _ & H & _). exact H. Qed.

End KI.

Lemma sl_statics_low : forall a, alloc_statics a -> 0 <= a < 0x50000.
Proof. intros a H. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in H. lia. Qed.

Section SG.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.
Hypothesis SF : statics_facts B.
Hypothesis SFR : statics_free B MR.
Hypothesis ERR : errno_low B.
Hypothesis SNE : statics_noerrno B.
Hypothesis MSO : malloc_syms_omx B.
Hypothesis MALLOC : forall fx' : FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : FPState, @free_contract fx' rc B API.

Ltac kq := unfold SLK, ALLOC_STACK in *; lia.

Lemma sl_block_range : forall L A m md r n, MR L A m md -> In (r, n) (blocks L A) ->
  4096 <= r /\ r + n <= alloc_ceiling.
Proof.
  intros L A m md r n HM Hin. destruct (in_blocks L A r n Hin) as (p & Hp & ->).
  exact (mr_blocks_range _ _ (aa_laws API) L A m md p n HM Hp).
Qed.

Lemma sl_cp_keep : forall L A regs mem md E L' A' regs' mem' md',
  MR L A mem md -> call_post B MR L A regs mem md E L' A' regs' mem' md' ->
  alloc_ceiling <= spZ regs - ALLOC_STACK ->
  forall a, (spZ regs <= a < 2 ^ 64 \/ alloc_statics a) -> ~ E a ->
    mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a).
Proof.
  intros L A regs mem md E L' A' regs' mem' md' HM CP HK a Ha HE.
  pose proof alloc_ceiling_val as Hac. unfold errno_low in ERR.
  destruct CP as (HM' & _ & _ & _ & _ & _ & _ & HFR & _).
  rewrite <- HS. apply HFR.
  - destruct Ha as [Ha|Ha]; [left; kq | right; exact (proj1 (SF a Ha))].
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho).
    destruct Ha as [Ha|Ha]; [kq | exact (SFR L A mem md a HM Ha Ho)].
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho).
    destruct Ha as [Ha|Ha]; [kq | exact (SFR L' A' mem' md' a HM' Ha Ho)].
  - unfold scratch. intros [Hs|Hs].
    + destruct Ha as [Ha|Ha]; [lia | pose proof (sl_statics_low a Ha); kq].
    + destruct Ha as [Ha|Ha]; [kq | exact (SNE a Ha Hs)].
  - exact HE.
Qed.

Lemma sl_pre_k : forall Kc L0 A0 regs0 mem0 md0 L A R m md,
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  0 <= Kc -> Kc + 64 <= SLK ->
  call_pre_k B MR Kc L A R m md.
Proof.
  intros Kc L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP HK0 HK1.
  pose proof J as (HM & HWF & HBD & _ & _ & HSC & _).
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact RA|].
  split; [rewrite SPR; Z.div_mod_to_equations; lia|]. split; [rewrite SPR; lia|]. split; [lia|].
  split; [intros a Ha; rewrite HS; apply HSC; left; lia|].
  split; [exact TP|]. split; [intros a Ha; rewrite HS; apply HSC; right; exact Ha|].
  intros H. rewrite INIT in H. discriminate.
Qed.

Lemma sl_malloc_call : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md n bnd (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 n -> 0 < n -> res_ok_slots A bnd -> room_slots bnd n ->
  (forall L' A' R' m' md' res,
     regs_preserved R R' -> getr R' 10 = Z_to_bv 64 res ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> st_init_done A' = true ->
     res_ok_slots A' (sb_malloc bnd n) -> 4096 <= res -> res + n <= alloc_ceiling ->
     (exists junk, rw_cells rsegs (normalize rsegs m') res [CB (Z.to_nat n) junk]) ->
     In (res, n) (blocks L' A') -> ~ In (res, n) (blocks L A) -> rmb (res, n) (blocks L' A') = blocks L A ->
     (forall x, In x (blocks L A) -> In x (blocks L' A')) ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, (spZ R <= a < 2 ^ 64 \/ alloc_statics a) ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     SR (ms_segs B) (mkCfg (@mkst f R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x14f8c) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md n bnd P J INIT HAC H16 H63 SPR RA TP N10 Hn RES ROOM K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  replace (Z_to_bv 64 0x14f8c) with (Z_to_bv 64 (ms_malloc B)) by (rewrite (proj1 MSO); reflexivity).
  eapply SR_bind; [apply (MALLOC f L A R m md n bnd); [| rewrite HS; exact HMI | exact N10 | exact RES | exact ROOM] |].
  { apply (proj2 (call_pre_k_alloc B MR L A R m md)).
    apply (sl_pre_k ALLOC_STACK L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq. }
  intros c' (L' & A' & R' & m' & md' & res & -> & CP & R10 & Hnz & H16' & (H4096 & HRC & HNI) & (b1 & b2 & E1 & E2) &
             BK0 & MI & GK & UB & INIT' & LEN & RES').
  apply (proj2 (call_post_k_alloc B MR _ _ _ _ _ _ _ _ _ _ _)) in CP.
  pose proof CP as (HM' & HWF' & HBD' & HLE & HST & RP & HMD' & HFR' & HKP & HSC').
  assert (BK : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)).
  { intros a k i Hin Hi. rewrite <- HS. exact (BK0 a k i Hin (fun x => x) Hi). }
  rewrite HS in HFR', HSC', MI.
  assert (NIN' : ~ In (res, n) (b1 ++ b2)) by exact (fresh_notin B API L' A' m' md' b1 b2 res n HM' E1 Hn).
  assert (INC : forall x, In x (blocks L A) -> In x (blocks L' A')).
  { intros x Hx. rewrite E2 in Hx. rewrite E1. apply in_app_iff in Hx. apply in_app_iff.
    destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx]. }
  assert (INR : In (res, n) (blocks L' A')) by (rewrite E1; apply in_app_iff; right; left; reflexivity).
  destruct (sl_block_range L' A' m' md' res n HM' INR) as [_ RNG].
  apply (K L' A' R' m' md' res RP R10).
  - apply (kinv_step B API AX SLK L0 A0 regs0 mem0 md0 L A m md L' A' m' md' ALLOC_STACK (spZ R) (fun _ => False)
             J HM' HWF' HBD' HMD').
    + kq.
    + kq.
    + kq.
    + intros a [].
    + intros a Hr H1 H2 H3 H4. apply HFR'; assumption.
    + intros a Ha. apply HSC'. exact Ha.
    + intros a k i Hin Hi. exact (BK a k i (HP0 _ Hin) Hi).
    + intros x Hx. apply INC. exact (HP0 x Hx).
    + exact MI.
  - exact INIT'.
  - exact RES'.
  - exact H4096.
  - exact RNG.
  - destruct (rw_cells_of_present m' res n ltac:(lia) ltac:(lia) ltac:(lia)) as (junk & RW).
    { intros i Hi. destruct (in_blocks L' A' res n INR) as (p & Hp & Ep).
      destruct (mr_blocks _ _ (aa_laws API) L' A' m' md' p n i HM' Hp Hi) as (Pr & _). rewrite <- Ep in Pr. exact Pr. }
    exists junk. apply (rw_cells_norm m' res _ MI RW). intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_false_not_img B HS); [apply HNI; lia | lia].
  - exact INR.
  - rewrite E2. exact NIN'.
  - rewrite E1, E2. apply rmb_ins. exact NIN'.
  - exact INC.
  - exact BK.
  - intros a Ha. apply (sl_cp_keep L A R m md (fun _ => False) L' A' R' m' md' HM CP); [kq | exact Ha | intros []].
Qed.

Lemma sl_free_call : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md r n bnd (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 r -> In (r, n) (blocks L A) -> ~ In (r, n) (blocks L0 A0) -> 0 < n ->
  res_ok_slots A bnd ->
  (forall L' A' R' m' md',
     regs_preserved R R' -> kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> st_init_done A' = true ->
     res_ok_slots A' (sb_free bnd n) -> blocks L' A' = rmb (r, n) (blocks L A) ->
     (forall a k i, In (a, k) (blocks L A) -> a <> r -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, (spZ R <= a < 2 ^ 64 \/ alloc_statics a) ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     SR (ms_segs B) (mkCfg (@mkst f R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x14e4c) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md r n bnd P J INIT HAC H16 H63 SPR RA TP R10 Hin NIN0 Hn RES K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (in_blocks L A r n Hin) as (p & Hp & Er).
  destruct (sl_block_range L A m md r n HM Hin) as [RL RH].
  replace (Z_to_bv 64 0x14e4c) with (Z_to_bv 64 (ms_free B)) by (rewrite (proj2 MSO); reflexivity).
  eapply SR_bind; [apply (FREE f L A R m md p n bnd); [| rewrite HS; exact HMI | exact Hp | rewrite <- Er; exact R10 | exact RES] |].
  { apply (proj2 (call_pre_k_alloc B MR L A R m md)).
    apply (sl_pre_k ALLOC_STACK L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq. }
  intros c' (L' & A' & R' & m' & md' & -> & CP & (b1 & b2 & E1 & E2) & BK0 & MI & GK & UB & INIT' & LEN & RES').
  rewrite <- Er in CP, E1, BK0.
  pose proof CP as (HM' & HWF' & HBD' & HLE & HST & RP & HMD' & HFR' & HKP & HSC').
  assert (BK : forall a k i, In (a, k) (blocks L A) -> a <> r -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)).
  { intros a k i Ha Hne Hi. rewrite <- HS. exact (BK0 a k i Ha Hne Hi). }
  rewrite HS in HFR', HSC', MI.
  assert (NIN' : ~ In (r, n) (b1 ++ b2)) by exact (fresh_notin B API L A m md b1 b2 r n HM E1 Hn).
  assert (EB : blocks L' A' = rmb (r, n) (blocks L A)) by (rewrite E2, E1; symmetry; apply rmb_ins; exact NIN').
  assert (NE0 : forall a k i, In (a, k) (blocks L0 A0) -> 0 <= i < k -> a <> r).
  { intros a k i Ha Hi Ear. subst a.
    assert (Hne : (r, k) <> (r, n)) by (intros E; rewrite E in Ha; exact (NIN0 Ha)).
    destruct (blocks_sep B API L A m md (r, k) (r, n) HM (HP0 _ Ha) Hin Hne) as [D|D]; cbn in D; lia. }
  apply (K L' A' R' m' md' RP).
  - apply (kinv_step B API AX SLK L0 A0 regs0 mem0 md0 L A m md L' A' m' md' ALLOC_STACK (spZ R)
             (fun a => r <= a < r + n) J HM' HWF' HBD' HMD').
    + kq.
    + kq.
    + kq.
    + intros a Ha. left. split; [lia|].
      pose proof (block_not_img B API AX L A m md r n (a - r) HM Hin ltac:(lia)) as Hni.
      replace (r + (a - r)) with a in Hni by lia. exact Hni.
    + intros a Hr H1 H2 H3 H4. apply HFR'; assumption.
    + intros a Ha. apply HSC'. exact Ha.
    + intros a k i Ha Hi. exact (BK a k i (HP0 _ Ha) (NE0 a k i Ha Hi) Hi).
    + intros x Hx. rewrite EB. destruct x as [a k]. apply rmb_in; [exact (HP0 _ Hx)|].
      intros E. rewrite E in Hx. exact (NIN0 Hx).
    + exact MI.
  - exact (INIT' INIT).
  - exact RES'.
  - exact EB.
  - exact BK.
  - intros a Ha. apply (sl_cp_keep L A R m md _ L' A' R' m' md' HM CP); [kq | exact Ha |].
    intros He. cbv beta in He. destruct Ha as [Ha|Ha]; [kq|]. pose proof (sl_statics_low a Ha).
    pose proof (block_not_img B API AX L A m md r n (a - r) HM Hin ltac:(lia)) as Hni.
    replace (r + (a - r)) with a in Hni by lia. exact (Hni (proj1 (SF a Ha))).
Qed.

Lemma sl_bpost : forall L0 A0 regs0 mem0 md0 L A R m md Kc L' A' R' m' md',
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md ->
  bpost B MR Kc stat_writes L A R m md L' A' R' m' md' ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 < 2 ^ 63 ->
  spZ R = spZ regs0 - 64 -> 0 <= Kc -> Kc + 64 <= SLK ->
  kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' /\ regs_preserved R R' /\ blocks L' A' = blocks L A /\
  (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) /\
  (forall a, spZ R <= a < 2 ^ 64 ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) /\
  ro_agree rsegs m'.
Proof.
  intros L0 A0 regs0 mem0 md0 L A R m md Kc L' A' R' m' md' J BP HAC H63 SPR HK0 HK1.
  pose proof alloc_ceiling_val as Hacv. unfold errno_low in ERR.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  pose proof BP as (HM' & HWF' & HBD' & RP & HMD' & HBL & HBB & HFR' & HSC' & MI' & _).
  rewrite HS in HBB, HFR', HSC', MI'.
  split.
  { apply (kinv_step B API AX SLK L0 A0 regs0 mem0 md0 L A m md L' A' m' md' Kc (spZ R) stat_writes
             J HM' HWF' HBD' HMD').
    + lia.
    + lia.
    + lia.
    + intros a Ha. right. exact Ha.
    + intros a Hr H1 H2 H3 H4. apply HFR'; assumption.
    + intros a Ha. apply HSC'. exact Ha.
    + intros a k i Ha Hi. exact (HBB a k i (HP0 _ Ha) Hi).
    + intros x Hx. rewrite HBL. exact (HP0 x Hx).
    + exact MI'. }
  split; [exact RP|]. split; [exact HBL|]. split; [exact HBB|].
  split; [|exact MI'].
  intros a Ha. apply HFR'.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM' Ho). lia.
  - unfold scratch_k. intros [Hs|Hs]; lia.
  - unfold stat_writes, G_LIVE, G_COUNT, G_FAIL. lia.
Qed.

Lemma sl_slack : block_slack_present B API -> forall L A m md a n bs,
  MR L A m md -> In (a, n) (blocks L A) -> bytes_at rsegs m a (bs ++ [Z_to_bv 8 0]) ->
  Z.of_nat (length bs) + 1 = n -> Forall (fun b => bv_unsigned b <> 0) bs ->
  exists sl, cstr_at m a bs sl /\ a + n + Z.of_nat (length sl) <= 8 * ((a + n + 7) / 8).
Proof.
  intros BSP L A m md a n bs HM Hin Hb Hn NZ.
  pose proof alloc_ceiling_val as Hacv.
  destruct (sl_block_range L A m md a n HM Hin) as [R1 R2].
  set (k := (- (a + n)) mod 8).
  assert (Hk : 0 <= k < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hk2 : a + n + k = 8 * ((a + n + 7) / 8)) by (unfold k; Z.div_mod_to_equations; lia).
  destruct (rw_cells_of_present m (a + n) k ltac:(lia) ltac:(lia) ltac:(lia)) as (junk & RW).
  { intros i Hi. apply (BSP L A m md a n (a + n + i) HM Hin). lia. }
  destruct RW as [[[Hlj _] Hj] _]. cbn [cells_bytes cbytes] in Hj. rewrite app_nil_r in Hj.
  exists junk. split.
  - split; [|split; [exact NZ|]].
    + replace (bs ++ Z_to_bv 8 0 :: junk) with ((bs ++ [Z_to_bv 8 0]) ++ junk) by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact Hb|]. rewrite length_app. cbn [length].
      replace (a + Z.of_nat (length bs + 1)) with (a + n) by lia. exact Hj.
    + rewrite Hlj. fold k. replace (- (a + Z.of_nat (length bs) + 1)) with (- (a + n)) by lia. fold k. lia.
  - rewrite Hlj. lia.
Qed.

Lemma sl_off_statics : forall L A m md r n len, MR L A m md -> In (r, n) (blocks L A) -> 0 < n ->
  0 <= len -> r + len <= 8 * ((r + n + 7) / 8) -> off_statics r len.
Proof.
  intros L A m md r n len HM Hin Hn0 Hl Hs.
  assert (NI : forall a, r <= a < r + n -> ~ alloc_statics a).
  { intros a Ha Hst. pose proof (block_not_img B API AX L A m md r n (a - r) HM Hin ltac:(lia)) as Hni.
    replace (r + (a - r)) with a in Hni by lia. exact (Hni (proj1 (SF a Hst))). }
  unfold off_statics, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *. split.
  - destruct (Z_le_gt_dec (r + len) 0x2f620) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (0x2f630 + 8) r) as [H2|H2]; [right; exact H2|].
    exfalso. destruct (Z_le_gt_dec (r + n) 0x2f620) as [H3|H3].
    + Z.div_mod_to_equations. lia.
    + apply (NI (Z.max r 0x2f620)); lia.
  - destruct (Z_le_gt_dec (r + len) 0x1f3a8) as [H|H]; [left; exact H|].
    destruct (Z_le_gt_dec (0x1f3a8 + 8) r) as [H2|H2]; [right; exact H2|].
    exfalso. destruct (Z_le_gt_dec (r + n) 0x1f3a8) as [H3|H3].
    + Z.div_mod_to_equations. lia.
    + apply (NI (Z.max r 0x1f3a8)); lia.
Qed.

End SG.
