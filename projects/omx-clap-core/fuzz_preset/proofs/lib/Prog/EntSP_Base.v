From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c EntryDefs EntrySR EntBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require strtod_c
  fuzz_alloc_peak_c fuzz_alloc_count_c fuzz_alloc_live_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma esp_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity. Qed.

Lemma esp_sp : forall regs0 regs : bvmap 5 word, getr regs 2 = Z_to_bv 64 (spZ regs0 - 112) -> 112 <= spZ regs0 ->
  spZ regs = spZ regs0 - 112.
Proof.
  intros regs0 regs H Hs. unfold spZ at 1. rewrite H. apply esp_uns.
  pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as R. unfold spZ in *.
  change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.

Lemma esp_node_rw : forall segs m L p t D, pj_node segs m L p t D -> pj_rw segs m p.
Proof.
  intros segs m L p t D H. destruct t; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & (Hrw & _) & _); exact Hrw.
Qed.

Lemma esp_rw_wr : forall segs m p a, pj_rw segs m p -> p <= a < p + 56 -> writable_at segs m a.
Proof. intros segs m p a (_ & _ & _ & H) Ha. exact (proj1 (H a Ha)). Qed.

Lemma esp_mrd : forall s m a b, m (Z_to_bv 64 a) = Some b -> EMem.mrd s m (EMem.wa a) = Some b.
Proof. intros s m a b H. unfold EMem.mrd, EMem.wa. rewrite H. reflexivity. Qed.

Lemma esp_stk_norm : forall m lo hi, EFrame.stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> EMem.ro_addr rsegs (EMem.wa a) = false) ->
  EFrame.stk rsegs (MemNorm.normalize rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) Hr. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hw & b0 & Hb). specialize (Hr a Ha).
  unfold wview, EMem.mrd, MemNorm.normalize in *. cbv beta. rewrite Hr. split; [exact Hw | exists b0; exact Hb].
Qed.

Lemma esp_zero_keep : forall s m m' p, pj_zero s m p ->
  (forall a, p <= a < p + 56 -> mbyte s m' a = mbyte s m a /\ (writable_at s m a -> writable_at s m' a)) ->
  pj_zero s m' p.
Proof.
  intros s m m' p ((H8 & H1 & H2 & H) & B1 & B2 & Hb) HK.
  split.
  - split; [exact H8|]. split; [exact H1|]. split; [exact H2|].
    intros a Ha. destruct (HK a Ha) as (E1 & E2). destruct (H a Ha) as (W & b & Hr).
    split; [exact (E2 W)|]. exists b. transitivity (mbyte s m a); [exact E1 | exact Hr].
  - split; [exact B1|]. split; [exact B2|]. intros i Hi.
    rewrite <- (Hb i Hi). destruct (HK (p + Z.of_nat i)) as (E1 & _); [rewrite repeat_length in Hi; lia|].
    exact E1.
Qed.

Section B.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.
#[local] Set Default Proof Using "All".

(* generic image facts, as the cno_* lemmas of check_no_overread_calls (moved here so that the entry's closure does
   not hold the check_no_overread walk) *)
Lemma esp_seg_in_img : forall x seg, find_segment (ms_segs B) x 1 = Some seg -> in_img B x.
Proof.
  intros x seg E. destruct (kb_find_segment _ x 1 seg E) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun rr => (bv_unsigned (fst rr) <=? Z.of_N (seg_base s)) &&
      (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst rr) + bv_unsigned (snd rr)))
      (segments_reserved (ms_segs B))) (ms_segs B) = true) by (rewrite HSEG; vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C. destruct C as (rr & Hr & Hc).
  apply andb_prop in Hc as (Hc1 & Hc2). apply Z.leb_le in Hc1, Hc2.
  split; [intros E'; rewrite E' in Hin; destruct Hin | exists rr; split; [exact Hr | lia]].
Qed.

Lemma esp_present_of_writable : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a ->
  writable_at (ms_segs B) m a -> present m a.
Proof.
  intros m a Ha Hn W. unfold writable_at, wview in W. unfold present.
  destruct (m (Z_to_bv 64 a)) as [x|] eqn:E; [exists x; reflexivity|]. exfalso.
  rewrite esp_uns in W by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:Ef; [|apply W; reflexivity].
  exact (Hn (esp_seg_in_img a seg Ef)).
Qed.

Lemma esp_ro_false : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> EMem.ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hn. unfold EMem.ro_addr. rewrite esp_uns by lia. rewrite <- HSEG.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; exact (Hn (esp_seg_in_img a seg E)) | reflexivity].
Qed.

Lemma esp_ro_agree_munch : forall W m m', MemNorm.ro_agree rsegs m -> EFrame.munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ EFrame.outside W a -> ~ in_img B a) -> MemNorm.ro_agree rsegs m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold EMem.mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (esp_ro_false (bv_unsigned a) Hr (HW _ Hr Ho)) as E. rewrite Z_to_bv_bv_unsigned in E. congruence.
Qed.

Lemma esp_frame : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  alloc_ceiling + stk <= spZ regs0 /\ spZ regs0 <= 2 ^ 47 /\ spZ regs0 mod 16 = 0 /\ 14176 <= stk /\
  n = ent_n pl /\ 0 <= cnt0 <= 3 * 2 ^ 60.
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    ((PRE & HN & _ & _ & _ & _ & _ & SP47) & _ & _ & _ & SLK & _ & _ & _ & LED & CNT & HJ & _).
  destruct PRE as (_ & _ & _ & _ & _ & SP16 & SPC & _).
  pose proof LED as (_ & _ & HC & _).
  assert (HJ' : Z.of_nat j <= 3) by lia.
  unfold SLOT_K in SLK. unfold ent_n.
  split; [exact SPC|]. split; [exact SP47|]. split; [exact SP16|]. split; [exact SLK|]. split; [exact HN|]. nia.
Qed.

Lemma esp_stk : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd a,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  spZ regs0 - stk <= a < spZ regs0 ->
  writable_at segs mem a /\ present mem a /\ ~ owned B L A a /\ ~ alloc_statics a /\
  ~ (errno_addr B <= a < errno_addr B + 4) /\ ~ in_img B a /\ EMem.ro_addr rsegs (EMem.wa a) = false.
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd a ENT INV Ha.
  pose proof (esp_frame stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT) as (SPC & SP47 & _).
  pose proof ENT as (_ & SYMS & _).
  pose proof INV as (RS & _).
  pose proof RS as (MRc & _ & _ & _ & _ & _ & _ & _ & _ & WRc).
  pose proof alloc_ceiling_val as HCV.
  pose proof (ent_errno B SYMS) as ERRB.
  pose proof (ent_img_low B HSEG) as (HIL & _).
  assert (HNI : ~ in_img B a) by (intros Hi; pose proof (HIL a Hi); lia).
  assert (W : writable_at segs mem a) by (apply WRc; left; lia).
  split; [exact W|].
  split; [exact (esp_present_of_writable mem a ltac:(lia) HNI W)|].
  split; [intros Ho; pose proof (mr_owned_low B (aa_MR API) (aa_laws API) L A mem md a MRc Ho); lia|].
  split; [intros Hs; pose proof (ent_statics_lo a Hs); lia|].
  split; [rewrite ERRB; unfold strtod_c.STRTOD_ERRNO; lia|].
  split; [exact HNI|].
  exact (esp_ro_false a ltac:(lia) HNI).
Qed.

Lemma esp_stk_rng : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd lo hi,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  spZ regs0 - stk <= lo -> hi <= spZ regs0 ->
  EFrame.stk segs mem lo hi.
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd lo hi ENT INV H1 H2.
  pose proof (esp_frame stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT) as (SPC & SP47 & _).
  pose proof alloc_ceiling_val as HCV.
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (esp_stk stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd a
    ENT INV ltac:(lia)) as (W & (b & Hb) & _).
  split; [exact W|]. exists b. exact (esp_mrd segs mem a b Hb).
Qed.

Lemma esp_out_rw : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  pj_rw segs mem (spZ regs0 - 112).
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd ENT INV.
  pose proof (esp_frame stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT) as (SPC & SP47 & SP16 & SLK & _).
  split; [Z.div_mod_to_equations; lia|].
  exact (esp_stk_rng stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd
    (spZ regs0 - 112) (spZ regs0 - 112 + 56) ENT INV ltac:(lia) ltac:(lia)).
Qed.

Lemma esp_rplace : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd regs,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  spZ regs = spZ regs0 - 112 ->
  rplace B L A Lam regs mem (spZ regs0 - 112).
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd regs ENT INV HSP.
  pose proof (esp_frame stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT) as (SPC & SP47 & SP16 & SLK & _).
  pose proof INV as (_ & _ & INIT & _).
  split; [left; rewrite HSP; lia|].
  split; [intros _ Hf; congruence|].
  intros i Hi.
  destruct (esp_stk stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd
    (spZ regs0 - 112 + i) ENT INV ltac:(lia)) as (_ & _ & H1 & H2 & H3 & H4 & _).
  tauto.
Qed.

Lemma esp_pay : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  empty = 0x34780 ->
  0 < p /\ p + n <= alloc_ceiling /\ EMem.bytes_at segs mem p pl /\
  (0 < n -> In (p, n) (blocks L A)) /\
  (forall i, 0 <= i < n -> ~ owned B L A (p + i) /\ ~ alloc_statics (p + i) /\
     ~ (errno_addr B <= p + i < errno_addr B + 4) /\ ~ in_img B (p + i)).
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd ENT INV EMP.
  pose proof ENT as ((PRE & HN & BD & _) & SYMS & _).
  pose proof PRE as (MR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PAY & _).
  pose proof INV as (RS & Z0 & _ & _ & _ & _ & _ & PAY0 & _).
  pose proof RS as (MRc & _ & _ & _ & KBc & _).
  pose proof alloc_ceiling_val as HCV.
  pose proof (ent_errno B SYMS) as ERRB.
  assert (HB : 0 < p /\ p + n <= alloc_ceiling /\ (0 < n -> In (p, n) (blocks L A))).
  { destruct PAY as [(Hn & Hp)|(Hn & q & Hq & Hp)].
    - subst. split; [lia|]. split; [lia|]. intros H. lia.
    - pose proof (rg_blk_of B API HSEG AX FG L0 A0 q n Hq) as Hb. rewrite Hp in Hb.
      destruct (rg_blk B API HSEG AX FG L0 A0 mem0 md0 p n 0 MR0 Hb ltac:(lia)) as (_ & H1 & H2 & _).
      split; [lia|]. split; [lia|]. intros _. exact (KBc p n Hb Hn (fun h => h)). }
  destruct HB as (Hp0 & Hpn & HBL).
  split; [exact Hp0|]. split; [exact Hpn|].
  split.
  { split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (PAY0 (Z.of_nat i) ltac:(lia)) as E1.
    pose proof (BD (Z.of_nat i) ltac:(lia)) as E2. rewrite Nat2Z.id in E2.
    transitivity (mbyte segs mem0 (p + Z.of_nat i)); [exact E1 | exact E2]. }
  split; [exact HBL|].
  intros i Hi. assert (Hin : In (p, n) (blocks L A)) by (apply HBL; lia).
  destruct (rg_blk B API HSEG AX FG L A mem md p n i MRc Hin Hi) as (_ & _ & _ & Hno).
  destruct (rg_blk_in B API HSEG AX FG L A p n Hin) as (q & Hq & Eq).
  assert (HNI : ~ in_img B (p + i)) by (rewrite <- Eq; exact (ax_blocks_img AX L A mem md q n i MRc Hq Hi)).
  split; [exact Hno|].
  split; [intros Hs; exact (HNI (proj1 (statics_img B API HSEG AX FG _ Hs)))|].
  split; [|exact HNI].
  intros He. apply HNI. replace (p + i) with (errno_addr B + (p + i - errno_addr B)) by lia.
  apply (errno_img B API HSEG AX FG ERRB). lia.
Qed.

Lemma esp_led : forall L A mem Lam peak cnt fail,
  ledger B L A mem Lam peak cnt fail -> 0 <= peak ->
  EMem.bytes_at rsegs mem fuzz_alloc_peak_c.G_PEAK (EMem.le8 (Z_to_bv 64 peak)) /\
  EMem.bytes_at rsegs mem fuzz_alloc_count_c.G_COUNT (EMem.le8 (Z_to_bv 64 cnt)) /\
  (Lam = [] -> EMem.bytes_at rsegs mem fuzz_alloc_live_c.G_LIVE (EMem.le8 (Z_to_bv 64 0))).
Proof.
  intros L A mem Lam peak cnt fail ((W1 & W2 & W3 & W4) & HP & HC & _) H0. rewrite <- HSEG.
  split; [apply (word_mem_le8 (ms_segs B)); [exact W2 | lia | unfold fuzz_alloc_peak_c.G_PEAK; lia
          | unfold fuzz_alloc_peak_c.G_PEAK; lia]|].
  split; [apply (word_mem_le8 (ms_segs B)); [exact W3 | lia | unfold fuzz_alloc_count_c.G_COUNT; lia
          | unfold fuzz_alloc_count_c.G_COUNT; lia]|].
  intros ->. apply (word_mem_le8 (ms_segs B)); [exact W1 | lia | unfold fuzz_alloc_live_c.G_LIVE; lia
    | unfold fuzz_alloc_live_c.G_LIVE; lia].
Qed.

Lemma esp_kAn : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] -> MemNorm.ro_agree rsegs mem1 ->
  EExec.evt rsegs Q (EMS.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None (MemNorm.normalize rsegs mem1)
    (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = EMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' m0 regs', Q (EMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m0 (seg_rom rsegs)) ->
     MemNorm.mem_rel rsegs mem' m0 -> MemNorm.ro_same rsegs mem1 mem' ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz Hro HE HS HK.
  apply (ent_kA B HSEG fx1 regs1 pc mem1 md1
    (fun s => exists s0, Q s0 /\ MemNorm.ms_rel rsegs s s0 /\ MemNorm.ro_same rsegs mem1 (ms_mem s)) P Hh Hz).
  - eapply (MemNorm.evt_normalize rsegs); [vm_compute; reflexivity | exact Hro | exact HE].
  - intros ms' (s0 & HQ & Hrel & Hsame). destruct (HS s0 HQ) as (R & pc0 & m0 & ->).
    destruct ms' as [R' F' pc'' svc' rv' fc' m' ro'].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem EMS.MS] in *. subst.
    exists R, pc0, m'. reflexivity.
  - intros R pc' mem' regs' (s0 & HQ & Hrel & Hsame) HGr.
    destruct (HS s0 HQ) as (R0 & pc0 & m0 & E0). subst s0.
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem EMS.MS] in *.
    subst R0 pc0.
    exact (HK R pc' mem' m0 regs' HQ HR Hsame HGr).
Qed.

Lemma esp_munch_inv : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd mem' W K,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  0 <= K -> 112 + K <= stk ->
  EFrame.munch W mem mem' -> EFrame.wmono (ms_segs B) mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ EFrame.outside W x -> spZ regs0 - 112 - K <= x < spZ regs0 - 56) ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem' md Lam peak cnt bnd.
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd mem' W K
    ENT INV HK0 HK1 MU WM HW.
  pose proof (esp_frame stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ENT) as (SPC & SP47 & SP16 & SLK & _).
  pose proof ENT as (_ & SYMS & _).
  pose proof INV as (RS & Z0 & INIT & RD & FRM & LED & RES & _).
  pose proof RS as (MRc & WFc & BDc & _ & _ & _ & _ & _ & _ & WRc).
  pose proof alloc_ceiling_val as HCV.
  pose proof (ent_errno B SYMS) as ERRB.
  pose proof (ent_img_low B HSEG) as (HIL & _).
  set (S := spZ regs0) in *.
  assert (ST : rstep B API K (S - 112) (fun x => S - 112 <= x < S - 56) (fun _ => False) L A mem md L A mem' md).
  { apply (rstep_of_munch B API HSEG AX FG K (S - 112) (fun x => S - 112 <= x < S - 56) (fun _ => False)
      L A mem mem' md W MRc WFc BDc).
    - intros a [Ha|Ha]; apply WRc; [left; lia | right; exact Ha].
    - exact MU.
    - exact WM.
    - intros x Hx Hn. pose proof (HW x Hx Hn) as Hr.
      destruct (Z_lt_le_dec x (S - 112)) as [H3|H3]; [left; left; lia | right; lia].
    - intros x Hx _. destruct (kb_outside_dec W x) as [Ho|Hn]; [exact Ho|].
      pose proof (HW x ltac:(lia) Hn). lia. }
  assert (RA2 : MemNorm.ro_agree rsegs mem').
  { apply (esp_ro_agree_munch W mem mem'); [rewrite <- HSEG; exact (proj1 RD) | exact MU |].
    intros a Ha Hn Hi. pose proof (HW a Ha Hn). pose proof (HIL a Hi). lia. }
  rewrite <- HSEG in RA2.
  apply (ent_after B API F HSEG FA stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak
    cnt bnd K _ _ fx1 L A mem' md Lam peak cnt bnd ENT INV ST HK0 HK1).
  - intros a Ha. right. left. exact Ha.
  - intros a Ha _. exact (WM _ (WRc a ltac:(left; lia))).
  - intros a k _ _ [].
  - intros a k Hin _. exact Hin.
  - exact RA2.
  - exact FRM.
  - apply (ledger_rstep B API HSEG AX FG K (S - 112) _ _ L A mem md L A mem' md Lam peak cnt (2 ^ 64 - 1) MRc LED ST).
    + intros a Ha. pose proof (ent_statics_lo a Ha) as Hl.
      unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha.
      split; [unfold rwin; rewrite ERRB; unfold strtod_c.STRTOD_ERRNO; lia | lia].
    + intros a k Hin.
      destruct (ledger_block_range B API L A mem md Lam peak cnt (2 ^ 64 - 1) a k MRc LED Hin) as (H1 & H2 & _).
      split; [intros [] | intros i Hi; lia].
  - exact RES.
Qed.

End B.
