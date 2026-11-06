From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger ManifestModel ManifestMem ManifestB names_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import check_no_overread_c check_no_overread_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import check_reject_clean_starved_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import slot_steps_c slot_glue slot_img.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require KindB.
Local Open Scope Z_scope.

Lemma rel_eqv_s : forall R F pc fc m0 ro s ms', ms_rel rsegs s (MS R F pc fc None m0 ro) -> ms_eqv s ms' ->
  ms_eqv (MS R F pc fc None (ms_mem s) ro) ms' /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros R F pc fc m0 ro [R' F' pc' svc' rv' fc' m' ro'] ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) E.
  cbn in *. subst. split; [exact E | exact H8].
Qed.

Lemma preserved_of_saved_s : forall R0 R,
  saved_regs R (getr R0 2) (getr R0 3) (getr R0 4) (getr R0 8) (getr R0 9) (getr R0 18) (getr R0 19)
    (getr R0 20) (getr R0 21) (getr R0 22) (getr R0 23) (getr R0 24) (getr R0 25) (getr R0 26) (getr R0 27) ->
  regs_preserved R0 R.
Proof.
  intros R0 R (H2 & H3 & H4 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27) r Hr.
  unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct C as [C|C]; [subst r; assumption|]). subst r. assumption.
Qed.

Lemma sp_stage : forall R S gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  saved_regs R (Z_to_bv 64 (S + -64)) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  64 <= S < 2 ^ 64 -> spZ R = S - 64 /\ getr R 4 = tp.
Proof.
  intros R S gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (H2 & H3 & H4 & _) Hr.
  split; [unfold spZ; rewrite H2; rewrite unsigned_lit by lia; lia | exact H4].
Qed.

Lemma frame_keep_s : forall m m' X cs lo, rw_cells rsegs m X cs -> lo <= X ->
  (forall a, lo <= a < 2 ^ 64 -> mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
  rw_cells rsegs m' X cs.
Proof.
  intros m m' X cs lo H Hlo K. apply (rw_cells_keep m m' X cs H). intros a Ha.
  pose proof (rw_cells_bound rsegs m X cs H). apply K. lia.
Qed.

Lemma blocks_of_user : forall L A q k, In (q, k) (user_blocks A) -> In (ptr_addr L q, k) (blocks L A).
Proof. intros L A q k H. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ H). Qed.

Definition gw_b (a : Z) : bool :=
  match wview rsegs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end.

Lemma gw_writable : forall m a, gw_b a = true -> writable_at rsegs m a.
Proof.
  intros m a H. unfold writable_at. unfold gw_b in H.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
  - unfold wview. rewrite E. simpl. discriminate.
  - replace (wview rsegs m (Z_to_bv 64 a)) with (wview rsegs (fun _ => None) (Z_to_bv 64 a)).
    + revert H. destruct (wview rsegs (fun _ => None) (Z_to_bv 64 a)) as [b'|]; intros H; simpl in H;
        [discriminate | discriminate H].
    + unfold wview. rewrite E. reflexivity.
Qed.

Lemma globals_writable : forall m a, (0x2f370 <= a < 0x2f388 \/ 0x1f0f8 <= a < 0x1f100) -> writable_at rsegs m a.
Proof.
  intros m a Ha. apply gw_writable. destruct Ha as [Ha|Ha].
  - apply (range_b gw_b 0x2f370 24%nat); [vm_compute; reflexivity | lia].
  - apply (range_b gw_b 0x1f0f8 8%nat); [vm_compute; reflexivity | lia].
Qed.

Lemma rt_used_le : forall u k fuel, (rt_used u k fuel <= fuel)%nat.
Proof.
  intros u k fuel. revert k. induction fuel as [|fuel IH]; intros k; cbn [rt_used]; [lia|].
  specialize (IH (S k)).
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Lemma rt_calls_bound : forall u : list byte, 0 <= rt_calls (zbytes u) <= 3 + 4 * Z.of_nat (length u).
Proof.
  intros u. unfold rt_calls, rt_nk. destruct (zbytes u) as [|z zs] eqn:E; [lia|].
  pose proof (rt_used_le (z :: zs) 1 (length (z :: zs))) as H.
  assert (Hl : length (z :: zs) = length u) by (rewrite <- E; unfold zbytes; apply length_map).
  lia.
Qed.

Lemma slack_eq : forall s (tb ts : list byte), Z.of_nat (length ts) = (- (s + Z.of_nat (length tb) + 1)) mod 8 ->
  s + Z.of_nat (length tb + 1 + length ts) = 8 * ((s + (Z.of_nat (length tb) + 1) + 7) / 8).
Proof. intros s tb ts H. Z.div_mod_to_equations. lia. Qed.

Section KB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.
Hypothesis SF : statics_facts B.
Hypothesis SFR : statics_free B MR.
Hypothesis ERR : errno_low B.
Hypothesis CNO : forall fx' : FPState, @check_no_overread_contract fx' rc B API.
Hypothesis NAMES : forall fx' : FPState, @names_contract fx' rc B API.
Hypothesis STARVED : forall fx' : FPState, @check_reject_clean_starved_contract fx' rc B API.
Hypothesis CRT : forall fx' : FPState, @check_round_trip_contract fx' rc B API.

Ltac kq := unfold SLK, CNO_K, CHECK_REJECT_CLEAN_STARVED_K, CRT_K, NAMES_K, READINGS_KB, ALLOC_STACK in *; lia.

Lemma kinv_kindS : forall K L0 A0 regs0 mem0 md0 L A mem md mem' W,
  kinv B API K L0 A0 regs0 mem0 md0 L A mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  alloc_ceiling + K <= spZ regs0 ->
  (forall x, 0 <= x < 2 ^ 64 -> outside W x \/ (spZ regs0 - K <= x < spZ regs0) \/ stat_writes x \/
     (exists r n, In (r, n) (blocks L A) /\ ~ In (r, n) (blocks L0 A0) /\ r <= x < r + n /\ present mem' x)) ->
  kinv B API K L0 A0 regs0 mem0 md0 L A mem' md.
Proof.
  intros K L0 A0 regs0 mem0 md0 L A mem md mem' W J MU WM MI' HK CLS.
  pose proof alloc_ceiling_val as Hac.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  assert (SWS : forall a, stat_writes a -> alloc_statics a).
  { unfold stat_writes, alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL. intros a Ha. lia. }
  assert (OWN : forall a, owned B L A a -> 0 <= a < alloc_ceiling /\ outside W a).
  { intros a Ho. pose proof (mr_owned_low _ _ (aa_laws API) L A mem md a HM Ho) as Hl. split; [exact Hl|].
    destruct (CLS a ltac:(lia)) as [Hout | [Hst | [Hsw | (r & n & Hin & _ & Hr & _)]]]; [exact Hout | lia | |].
    - exfalso. exact (SFR L A mem md a HM (SWS a Hsw) Ho).
    - exfalso. destruct (in_blocks L A r n Hin) as (p & Hp & ->).
      destruct (mr_blocks _ _ (aa_laws API) L A mem md p n (a - ptr_addr L p) HM Hp ltac:(lia)) as (_ & _ & _ & Hno).
      replace (ptr_addr L p + (a - ptr_addr L p)) with a in Hno by lia. exact (Hno Ho). }
  assert (HM' : MR L A mem' md).
  { destruct (mr_model _ _ (aa_laws API) L A mem md HM) as (Hh & Hl & Hm).
    eapply (mr_frame _ _ (aa_laws API) L A mem mem' md md HM).
    - intros a Ho. destruct (OWN a Ho) as [Hl0 Hout]. apply (mbyte_munch _ W); [exact MU | lia | exact Hout].
    - intros a Ho Hp. destruct (OWN a Ho) as [Hl0 Hout]. apply (present_munch W mem); [exact MU | lia | exact Hout | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks _ _ (aa_laws API) L A mem md p n i HM Hin Hi) as (Hp & H1 & H2 & _).
      destruct (CLS (ptr_addr L p + i) ltac:(lia)) as [Hout | [Hst | [Hsw | (r & k & _ & _ & _ & Hpr)]]].
      + apply (present_munch W mem); [exact MU | lia | exact Hout | exact Hp].
      + lia.
      + exfalso. exact (ax_blocks_img AX L A mem md p n i HM Hin Hi (proj1 (SF _ (SWS _ Hsw)))).
      + exact Hpr.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  apply (kinv_step B API AX K L0 A0 regs0 mem0 md0 L A mem md L A mem' md K (spZ regs0) stat_writes
           J HM' HWF HBD (ex_intro _ (m_vmmaps md) (with_vmmaps_self' md))).
  - lia.
  - lia.
  - exact HK.
  - intros a Ha. right. exact Ha.
  - intros a Hr Ho1 Ho2 Hsc Hsw.
    assert (Ha : 0 <= a < 2 ^ 64) by (destruct Hr as [Hr|Hr]; [lia | pose proof (in_img_low B HS a Hr); lia]).
    destruct (CLS a Ha) as [Hout | [Hst | [Hs2 | (r & n & Hin & _ & Hrn & _)]]].
    + split.
      * exact (mbyte_munch _ W mem mem' a MU Ha Hout).
      * exact (writable_munch _ W mem mem' a MU Ha Hout).
    + exfalso. apply Hsc. left. exact Hst.
    + exfalso. exact (Hsw Hs2).
    + exfalso. pose proof (blocks_low B API L A mem md r n (a - r) HM Hin ltac:(lia)) as Hlow.
      pose proof (block_not_img B API AX L A mem md r n (a - r) HM Hin ltac:(lia)) as Hni.
      replace (r + (a - r)) with a in Hlow, Hni by lia. destruct Hr as [Hr|Hr]; [lia | exact (Hni Hr)].
  - intros a Ha. apply WM. apply HSC. exact Ha.
  - intros a k i Hin Hi.
    pose proof (HP0 _ Hin) as Hin'.
    pose proof (blocks_low B API L A mem md a k i HM Hin' Hi) as Hlow.
    destruct (CLS (a + i) ltac:(lia)) as [Hout | [Hstk | [Hsw | (r & n & Hrin & Hrn0 & Hrn & _)]]].
    + apply (mbyte_munch _ W); [exact MU | lia | exact Hout].
    + lia.
    + exfalso. exact (block_not_img B API AX L A mem md a k i HM Hin' Hi (proj1 (SF _ (SWS _ Hsw)))).
    + exfalso. assert (Hne : (a, k) <> (r, n)) by (intros E; rewrite E in Hin; exact (Hrn0 Hin)).
      destruct (blocks_sep B API L A mem md (a, k) (r, n) HM Hin' Hrin Hne) as [D|D]; cbn in D; lia.
  - exact HP0.
  - exact MI'.
Qed.

Lemma kinv_copy : forall L0 A0 regs0 mem0 md0 L A m md m' r n bs,
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> munch [(r, r + n)] m m' -> wmono rsegs m m' -> ro_agree rsegs m' ->
  alloc_ceiling + SLK <= spZ regs0 -> In (r, n) (blocks L A) -> ~ In (r, n) (blocks L0 A0) ->
  bytes_at rsegs m' r bs -> Z.of_nat (length bs) = n -> kinv B API SLK L0 A0 regs0 mem0 md0 L A m' md.
Proof.
  intros L0 A0 regs0 mem0 md0 L A m md m' r n bs J MU WM MI HAC Hin NIN Hb Hl.
  apply (kinv_kindA B API HS AX SLK L0 A0 regs0 mem0 md0 L A m md m' [(r, r + n)] J MU WM MI HAC).
  intros x Hx. destruct (Z.lt_ge_cases x r) as [H1|H1]; [left; apply outside_one; lia|].
  destruct (Z.lt_ge_cases x (r + n)) as [H2|H2]; [|left; apply outside_one; lia].
  right; right. exists r, n. split; [exact Hin|]. split; [exact NIN|]. split; [lia|].
  pose proof (block_not_img B API AX L A m md r n (x - r) (kinv_MR _ _ _ _ _ _ _ _ _ _ _ _ J) Hin ltac:(lia)) as Hni.
  replace x with (r + (x - r)) by lia.
  apply (present_of_bytes B HS m' r bs (x - r) Hb); [lia | exact Hni].
Qed.

Lemma payload_now_k : forall L0 A0 regs0 mem0 md0 L A m md p bs,
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> bytes_at rsegs mem0 p bs ->
  in_blk (blocks L0 A0) p (Z.of_nat (length bs)) -> bytes_at rsegs m p bs.
Proof.
  intros L0 A0 regs0 mem0 md0 L A m md p bs J Hb IB.
  destruct IB as [E0|(a & k & Hin & H1 & H2)].
  - destruct bs as [|x bs]; [|cbn in E0; lia].
    destruct Hb as (Ha & Hl & _). apply bytes_at_nil. cbn in Hl. lia.
  - apply (bytes_at_mbyte mem0 m p bs Hb). intros i Hi.
    replace (p + i) with (a + (p - a + i)) by lia.
    apply (kinv_b0 _ _ _ _ _ _ _ _ _ _ _ _ J a k (p - a + i) Hin). lia.
Qed.

Lemma sl_cno_call : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md bnd (ub tb : list byte) pk ct
    (uri text : Z) (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true -> frm_zero (@fp_csr f) ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 -> spZ regs0 <= TASK_SIZE ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 uri -> getr R 12 = Z_to_bv 64 text -> 0 <= uri < 2 ^ 64 -> 0 <= text < 2 ^ 64 ->
  getr R 11 = Z_to_bv 64 (Z.of_nat (length ub)) -> getr R 13 = Z_to_bv 64 (Z.of_nat (length tb)) ->
  bytes_at rsegs m uri ub -> bytes_at rsegs m text tb ->
  Forall (fun x => bv_unsigned x <> 0) ub -> Forall (fun x => bv_unsigned x <> 0) tb ->
  (length ub <= 255)%nat -> Z.of_nat (length tb) <= 2 ^ 22 ->
  in_blk (blocks L A) uri (Z.of_nat (length ub)) -> in_blk (blocks L A) text (Z.of_nat (length tb)) ->
  alloc_words B m 0 pk ct (2 ^ 64 - 1) -> 0 <= pk < 2 ^ 64 -> 0 <= ct -> ct + 2 < 2 ^ 63 ->
  res_ok_slots A bnd -> sb_live bnd + 5 <= sb_cap bnd <= CAPMAX -> 0 <= sb_bytes bnd ->
  sb_bytes bnd + (3 * Z.of_nat (length ub) + 2 * Z.of_nat (length tb) + 91) <= 2 ^ 40 ->
  (forall (f' : FPState) L' A' R' m' md' pk' ct',
     frm_zero (@fp_csr f') -> st_init_done A' = true -> regs_preserved R R' ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> blocks L' A' = blocks L A ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, spZ R <= a < 2 ^ 64 ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     alloc_words B m' 0 pk' ct' (2 ^ 64 - 1) -> 0 <= pk' < 2 ^ 64 -> ct <= ct' <= ct + 2 ->
     res_ok_slots A' bnd ->
     SR (ms_segs B) (mkCfg (@mkst f' R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x13060) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md bnd ub tb pk ct uri text P
    J INIT FRM HAC H16 H63 TSZ SPR RA TP R10 R12 RU RT R11 R13 BU BT NZU NZT LU LT IBU IBT AW PK C0 C1
    RES CAP BY0 BYQ K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  assert (UU : bv_unsigned (getr R 10) = uri) by (rewrite R10; apply unsigned_lit; lia).
  assert (UT : bv_unsigned (getr R 12) = text) by (rewrite R12; apply unsigned_lit; lia).
  assert (US : bv_unsigned (getr R 2) = spZ regs0 - 64) by exact SPR.
  eapply SR_bind.
  { apply (CNO f L A R m md bnd ub tb [] pk ct (2 ^ 64 - 1)).
    - exact HS.
    - apply (sl_pre_k B API HS CNO_K L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq.
    - exact INIT.
    - rewrite US. lia.
    - exact FRM.
    - exact HMI.
    - exact R11.
    - exact R13.
    - rewrite UU. exact BU.
    - rewrite UT. exact BT.
    - exact NZU.
    - exact NZT.
    - exact LU.
    - exact LT.
    - rewrite UU. exact IBU.
    - rewrite UT. exact IBT.
    - exact (img_strings_ro m HMI).
    - unfold ledger. cbn [lsum map]. split; [exact AW|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; constructor.
    - unfold quiet. split; [reflexivity | lia].
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' (f' & L' & A' & R' & m' & md' & -> & FRM' & INIT' & BP & _ & _ & ARMS & RES').
  destruct (sl_bpost B API HS AX ERR L0 A0 regs0 mem0 md0 L A R m md CNO_K L' A' R' m' md' J BP HAC H63 SPR
              ltac:(kq) ltac:(kq)) as (J' & RP & BL & BB & KP & MI').
  destruct ARMS as [(_ & LG) | (_ & LG)]; destruct LG as (AW' & PK' & CT' & _); cbn [lsum] in AW', PK'.
  - exact (K f' L' A' R' m' md' pk ct FRM' INIT' RP J' BL BB KP AW' ltac:(lia) ltac:(lia) RES').
  - exact (K f' L' A' R' m' md' _ (ct + 2) FRM' INIT' RP J' BL BB KP AW' ltac:(lia) ltac:(lia) RES').
Qed.

Lemma sl_names_call : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md bnd (tb ts ub us : list byte) pk ct
    (ta ua : Z) (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true -> frm_zero (@fp_csr f) ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 -> spZ regs0 <= TASK_SIZE ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 ta -> getr R 11 = Z_to_bv 64 ua ->
  cstr_at m ta tb ts -> Z.of_nat (length ts) = (- (ta + Z.of_nat (length tb) + 1)) mod 8 ->
  cstr_at m ua ub us -> Z.of_nat (length us) = (- (ua + Z.of_nat (length ub) + 1)) mod 8 ->
  In (ta, Z.of_nat (length tb) + 1) (blocks L A) -> In (ua, Z.of_nat (length ub) + 1) (blocks L A) ->
  (length ub <= 255)%nat ->
  alloc_words B m 0 pk ct (2 ^ 64 - 1) -> 0 <= pk < 2 ^ 64 -> 0 <= ct -> ct + 1 < 2 ^ 63 ->
  res_ok_slots A bnd -> sb_live bnd + 1 <= sb_cap bnd <= CAPMAX -> 0 <= sb_bytes bnd ->
  sb_bytes bnd + (Z.of_nat (length ub) + 19) <= 2 ^ 40 ->
  (forall (f' : FPState) L' A' R' m' md' pk' ct',
     frm_zero (@fp_csr f') -> st_init_done A' = true -> regs_preserved R R' ->
     getr R' 10 = Z_to_bv 64 (names (zbytes tb) (zbytes ub)) ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> blocks L' A' = blocks L A ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, spZ R <= a < 2 ^ 64 ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     (exists ts', cstr_at m' ta tb ts') -> (exists us', cstr_at m' ua ub us') ->
     alloc_words B m' 0 pk' ct' (2 ^ 64 - 1) ->
     ((ub = [] /\ pk' = pk) \/ (ub <> [] /\ pk' = Z.max pk (Z.of_nat (length ub) + 3))) -> ct <= ct' <= ct + 1 ->
     res_ok_slots A' bnd ->
     SR (ms_segs B) (mkCfg (@mkst f' R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x13c1c) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md bnd tb ts ub us pk ct ta ua P
    J INIT FRM HAC H16 H63 TSZ SPR RA TP R10 R11 CT LTS CU LUS INT INU LU AW PK C0 C1 RES CAP BY0 BYQ K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (sl_block_range B API L A m md ta _ HM INT) as [TL TH].
  destruct (sl_block_range B API L A m md ua _ HM INU) as [UL UH].
  assert (UT : bv_unsigned (getr R 10) = ta) by (rewrite R10; apply unsigned_lit; lia).
  assert (UU : bv_unsigned (getr R 11) = ua) by (rewrite R11; apply unsigned_lit; lia).
  assert (US : bv_unsigned (getr R 2) = spZ regs0 - 64) by exact SPR.
  pose proof (slack_eq ta tb ts LTS) as ST. pose proof (slack_eq ua ub us LUS) as SU.
  eapply SR_bind.
  { apply (NAMES f L A R m md bnd tb ts ub us [] pk ct (2 ^ 64 - 1)).
    - exact HS.
    - apply (sl_pre_k B API HS NAMES_K L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq.
    - exact INIT.
    - rewrite US. lia.
    - exact FRM.
    - exact HMI.
    - destruct (ax_statics AX L A m md HM) as (G0 & (g & _ & Wg) & _). split; [exact G0 | exists g; exact Wg].
    - rewrite UT. exact CT.
    - rewrite UU. exact CU.
    - rewrite UT. left. exists ta, (Z.of_nat (length tb) + 1). split; [exact INT | lia].
    - rewrite UU. left. exists ua, (Z.of_nat (length ub) + 1). split; [exact INU | lia].
    - rewrite UT. exact TL.
    - rewrite UU. exact UL.
    - lia.
    - exact LU.
    - exact (img_strings_ro m HMI).
    - unfold off_stack. rewrite US, UT. left. rewrite ST. Z.div_mod_to_equations. kq.
    - unfold off_stack. rewrite US, UU. left. rewrite SU. Z.div_mod_to_equations. kq.
    - unfold off_stack, PREFIX_LC_STR. rewrite US. left. kq.
    - unfold off_stack, PREFIX_UC_STR. rewrite US. left. kq.
    - unfold off_stack, FMT_WHOLE_STR. rewrite US. left. kq.
    - rewrite UT. apply (sl_off_statics B API AX SF L A m md ta (Z.of_nat (length tb) + 1) _ HM INT); [lia | lia |].
      rewrite ST. lia.
    - rewrite UU. apply (sl_off_statics B API AX SF L A m md ua (Z.of_nat (length ub) + 1) _ HM INU); [lia | lia |].
      rewrite SU. lia.
    - unfold ledger. cbn [lsum map]. split; [exact AW|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; constructor.
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' (f' & L' & A' & R' & m' & md' & res & -> & FRM' & INIT' & BP & R10' & CT' & CU' & ARMS & RES').
  rewrite UT in CT'. rewrite UU in CU'.
  destruct (sl_bpost B API HS AX ERR L0 A0 regs0 mem0 md0 L A R m md NAMES_K L' A' R' m' md' J BP HAC H63 SPR
              ltac:(kq) ltac:(kq)) as (J' & RP & BL & BB & KP & MI').
  destruct ARMS as [(Eub & Er & LG') | [(_ & Ecf & _) | (Nub & Ncf & Er & LG')]].
  - subst ub res. destruct LG' as (AW' & PK' & CT0 & _). cbn [lsum] in AW'.
    exact (K f' L' A' R' m' md' pk ct FRM' INIT' RP ltac:(rewrite R10'; reflexivity) J' BL BB KP CT' CU' AW'
             (or_introl (conj eq_refl eq_refl)) ltac:(lia) RES').
  - lia.
  - subst res. rewrite (Z.mod_small (ct + 1) (2 ^ 64)) in LG' by lia.
    destruct LG' as (AW' & PK' & CT0 & _). cbn [lsum] in AW'.
    exact (K f' L' A' R' m' md' _ (ct + 1) FRM' INIT' RP R10' J' BL BB KP CT' CU' AW'
             (or_intror (conj Nub eq_refl)) ltac:(lia) RES').
Qed.

Lemma sl_starved_call : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md bnd (tb ts ub us : list byte) pk ct
    (ta ua : Z) (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true -> frm_zero (@fp_csr f) ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 -> spZ regs0 <= TASK_SIZE ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 ta -> getr R 11 = Z_to_bv 64 ua ->
  cstr_at m ta tb ts -> Z.of_nat (length ts) = (- (ta + Z.of_nat (length tb) + 1)) mod 8 ->
  cstr_at m ua ub us -> Z.of_nat (length us) = (- (ua + Z.of_nat (length ub) + 1)) mod 8 ->
  In (ta, Z.of_nat (length tb) + 1) (blocks L A) -> In (ua, Z.of_nat (length ub) + 1) (blocks L A) ->
  (length ub <= 255)%nat ->
  alloc_words B m 0 pk ct (2 ^ 64 - 1) -> 0 <= pk < 2 ^ 64 -> 0 <= ct -> ct + 1 < 2 ^ 63 ->
  res_ok_slots A bnd -> sb_live bnd + 1 <= sb_cap bnd <= CAPMAX -> 0 <= sb_bytes bnd ->
  sb_bytes bnd + (Z.of_nat (length ub) + 19) <= 2 ^ 40 ->
  (forall (f' : FPState) L' A' R' m' md' ct',
     frm_zero (@fp_csr f') -> st_init_done A' = true -> regs_preserved R R' ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> blocks L' A' = blocks L A ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, spZ R <= a < 2 ^ 64 ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     (exists ts', cstr_at m' ta tb ts') -> (exists us', cstr_at m' ua ub us') ->
     alloc_words B m' 0 pk ct' (2 ^ 64 - 1) -> ct <= ct' <= ct + 1 ->
     res_ok_slots A' bnd ->
     SR (ms_segs B) (mkCfg (@mkst f' R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x13298) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md bnd tb ts ub us pk ct ta ua P
    J INIT FRM HAC H16 H63 TSZ SPR RA TP R10 R11 CT LTS CU LUS INT INU LU AW PK C0 C1 RES CAP BY0 BYQ K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (sl_block_range B API L A m md ta _ HM INT) as [TL TH].
  destruct (sl_block_range B API L A m md ua _ HM INU) as [UL UH].
  assert (UT : bv_unsigned (getr R 10) = ta) by (rewrite R10; apply unsigned_lit; lia).
  assert (UU : bv_unsigned (getr R 11) = ua) by (rewrite R11; apply unsigned_lit; lia).
  assert (US : bv_unsigned (getr R 2) = spZ regs0 - 64) by exact SPR.
  pose proof (slack_eq ta tb ts LTS) as ST. pose proof (slack_eq ua ub us LUS) as SU.
  eapply SR_bind.
  { apply (STARVED f L A R m md bnd tb ts ub us [] pk ct (2 ^ 64 - 1)).
    - exact HS.
    - apply (sl_pre_k B API HS CHECK_REJECT_CLEAN_STARVED_K L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR
               RA TP); kq.
    - exact INIT.
    - rewrite US. lia.
    - exact FRM.
    - exact HMI.
    - destruct (ax_statics AX L A m md HM) as (G0 & (g & _ & Wg) & _). split; [exact G0 | exists g; exact Wg].
    - rewrite UT. exact CT.
    - rewrite UU. exact CU.
    - rewrite UT. left. exists ta, (Z.of_nat (length tb) + 1). split; [exact INT | lia].
    - rewrite UU. left. exists ua, (Z.of_nat (length ub) + 1). split; [exact INU | lia].
    - rewrite UT. exact TL.
    - rewrite UU. exact UL.
    - lia.
    - exact LU.
    - exact (img_strings_ro m HMI).
    - unfold off_stack. rewrite US, UT. left. rewrite ST. Z.div_mod_to_equations. kq.
    - unfold off_stack. rewrite US, UU. left. rewrite SU. Z.div_mod_to_equations. kq.
    - rewrite UT. apply (sl_off_statics B API AX SF L A m md ta (Z.of_nat (length tb) + 1) _ HM INT); [lia | lia |].
      rewrite ST. lia.
    - rewrite UU. apply (sl_off_statics B API AX SF L A m md ua (Z.of_nat (length ub) + 1) _ HM INU); [lia | lia |].
      rewrite SU. lia.
    - unfold ledger. cbn [lsum map]. split; [exact AW|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; constructor.
    - unfold quiet. split; [reflexivity | lia].
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' (f' & L' & A' & R' & m' & md' & -> & FRM' & INIT' & BP & CT' & CU' & ARMS & RES').
  rewrite UT in CT'. rewrite UU in CU'.
  destruct (sl_bpost B API HS AX ERR L0 A0 regs0 mem0 md0 L A R m md CHECK_REJECT_CLEAN_STARVED_K L' A' R' m' md'
              J BP HAC H63 SPR ltac:(kq) ltac:(kq)) as (J' & RP & BL & BB & KP & MI').
  destruct ARMS as [(_ & LG) | (_ & LG)]; destruct LG as (AW' & PK' & CT0 & _); cbn [lsum] in AW'.
  - exact (K f' L' A' R' m' md' ct FRM' INIT' RP J' BL BB KP CT' CU' AW' ltac:(lia) RES').
  - exact (K f' L' A' R' m' md' (ct + 1) FRM' INIT' RP J' BL BB KP CT' CU' AW' ltac:(lia) RES').
Qed.

Lemma sl_crt_call : forall (f : FPState) L0 A0 regs0 mem0 md0 L A R m md bnd (ub us : list byte) pk ct
    (ua : Z) (P : config -> Prop),
  kinv B API SLK L0 A0 regs0 mem0 md0 L A m md -> st_init_done A = true -> frm_zero (@fp_csr f) ->
  alloc_ceiling + SLK <= spZ regs0 -> spZ regs0 mod 16 = 0 -> spZ regs0 < 2 ^ 63 -> spZ regs0 <= TASK_SIZE ->
  spZ R = spZ regs0 - 64 -> YK0s.ret_ok (getr R 1) -> getr R 4 = Z_to_bv 64 (ms_tp B) ->
  getr R 10 = Z_to_bv 64 ua ->
  cstr_at m ua ub us -> In (ua, Z.of_nat (length ub) + 1) (blocks L A) -> (length ub <= 255)%nat ->
  alloc_words B m 0 pk ct (2 ^ 64 - 1) -> 0 <= pk < 2 ^ 64 -> 0 <= ct -> ct + 1019 < 2 ^ 63 ->
  res_ok_slots A bnd -> sb_live bnd + 2 <= sb_cap bnd <= CAPMAX -> 0 <= sb_bytes bnd ->
  sb_bytes bnd + (4 * Z.of_nat (length ub) + 83) <= 2 ^ 40 ->
  (forall (f' : FPState) L' A' R' m' md' pk' ct',
     frm_zero (@fp_csr f') -> st_init_done A' = true -> regs_preserved R R' ->
     kinv B API SLK L0 A0 regs0 mem0 md0 L' A' m' md' -> blocks L' A' = blocks L A ->
     (forall a k i, In (a, k) (blocks L A) -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
     (forall a, spZ R <= a < 2 ^ 64 ->
        mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
     alloc_words B m' 0 pk' ct' (2 ^ 64 - 1) -> 0 <= pk' < 2 ^ 64 -> ct <= ct' <= ct + 1023 ->
     res_ok_slots A' bnd ->
     SR (ms_segs B) (mkCfg (@mkst f' R' (getr R 1) m' (seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x132f4) m (seg_rom (ms_segs B))) md) P.
Proof.
  intros f L0 A0 regs0 mem0 md0 L A R m md bnd ub us pk ct ua P
    J INIT FRM HAC H16 H63 TSZ SPR RA TP R10 CU INU LU AW PK C0 C1 RES CAP BY0 BYQ K.
  pose proof alloc_ceiling_val as Hacv.
  pose proof J as (HM & HWF & HBD & HMD & HFR & HSC & HB0 & HP0 & HMI).
  destruct (sl_block_range B API L A m md ua _ HM INU) as [UL UH].
  assert (UU : bv_unsigned (getr R 10) = ua) by (rewrite R10; apply unsigned_lit; lia).
  assert (US : bv_unsigned (getr R 2) = spZ regs0 - 64) by exact SPR.
  eapply SR_bind.
  { apply (CRT f L A R m md bnd ub us [] pk ct (2 ^ 64 - 1)).
    - exact HS.
    - apply (sl_pre_k B API HS CRT_K L0 A0 regs0 mem0 md0 L A R m md J INIT HAC H16 H63 SPR RA TP); kq.
    - exact INIT.
    - rewrite US. lia.
    - exact FRM.
    - exact HMI.
    - destruct (ax_statics AX L A m md HM) as (G0 & (g & _ & Wg) & _). split; [exact G0 | exists g; exact Wg].
    - rewrite UU. exact CU.
    - rewrite UU. exists ua, (Z.of_nat (length ub) + 1). split; [exact INU | lia].
    - exact LU.
    - exact (img_strings_ro m HMI).
    - exact (crt_strings_ro m HMI).
    - unfold ledger. cbn [lsum map]. split; [exact AW|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; constructor.
    - unfold quiet. split; [reflexivity | lia].
    - exact RES.
    - exact CAP.
    - exact BY0.
    - exact BYQ. }
  intros c' (f' & L' & A' & R' & m' & md' & -> & FRM' & INIT' & BP & _ & LG & RES').
  destruct (sl_bpost B API HS AX ERR L0 A0 regs0 mem0 md0 L A R m md CRT_K L' A' R' m' md' J BP HAC H63 SPR
              ltac:(kq) ltac:(kq)) as (J' & RP & BL & BB & KP & MI').
  destruct LG as (AW' & PK' & CT0 & _). cbn [lsum] in AW', PK'.
  pose proof (rt_calls_bound ub) as RB.
  exact (K f' L' A' R' m' md' _ _ FRM' INIT' RP J' BL BB KP AW' ltac:(lia) ltac:(lia) RES').
Qed.

End KB.
