From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YM05 YL0i YL01 YL00 YL0g YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import Ledger ManifestModel ManifestMem ManifestB names_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_no_overread_c check_no_overread_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import check_reject_clean_starved_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import memchr_c memcpy_c fuzz_alloc_live_c
fuzz_alloc_peak_reset_c fuzz_alloc_peak_c check_bounded_alloc_c check_as_written_c check_reject_clean_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import slot_steps_c slot_glue slot_img slot_kb
StatementUbsan slot_c ManifestFF.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require slot_sa slot_sb slot_sc KindB.
Ltac gu := unfold Ledger.G_LIVE, Ledger.G_PEAK, Ledger.G_COUNT, Ledger.G_FAIL in *.

Local Open Scope Z_scope.

Lemma sl_frame_size : forall j v5 v4 v3 v2 v1 v0 vra, cells_size (sl_frame j v5 v4 v3 v2 v1 v0 vra) = 64%nat.
Proof. reflexivity. Qed.

Lemma sl_frame_munch : forall m m' W X j v5 v4 v3 v2 v1 v0 vra,
  rw_cells rsegs m X (sl_frame j v5 v4 v3 v2 v1 v0 vra) -> munch W m m' ->
  (forall x, X <= x < X + 64 -> outside W x) -> rw_cells rsegs m' X (sl_frame j v5 v4 v3 v2 v1 v0 vra).
Proof.
  intros m m' W X j v5 v4 v3 v2 v1 v0 vra H MU Ho.
  pose proof (rw_cells_bound rsegs m X _ H) as Bd. rewrite sl_frame_size in Bd.
  apply (rw_cells_keep m m' X _ H). rewrite sl_frame_size. intros a Ha. split.
  - apply (mbyte_munch rsegs W m m' a MU); [lia | apply Ho; lia].
  - apply (writable_munch rsegs W m m' a MU); [lia | apply Ho; lia].
Qed.

Lemma sl_bytes_munch : forall m m' W a bs, bytes_at rsegs m a bs -> munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' W a bs H MU Ho. apply (bytes_at_mbyte m m' a bs H). intros i Hi.
  destruct H as (H0 & H1 & _). apply (mbyte_munch rsegs W m m' (a + i) MU); [lia | apply Ho; lia].
Qed.

Lemma sl_cstr_munch : forall m m' W a bs sl, cstr_at m a bs sl -> munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs + 1 + length sl) -> outside W x) -> cstr_at m' a bs sl.
Proof.
  intros m m' W a bs sl (Hb & Hn & Hm) MU Ho. split; [|split; assumption].
  apply (sl_bytes_munch m m' W a _ Hb MU). intros x Hx. apply Ho.
  rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma sl_bytes_keep : forall m m' p bs bl n, bytes_at rsegs m p bs -> In (p, n) bl -> Z.of_nat (length bs) <= n ->
  (forall a k i, In (a, k) bl -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' p bs.
Proof.
  intros m m' p bs bl n Hb Hin Hl BK. apply (bytes_at_mbyte m m' p bs Hb). intros i Hi.
  apply (BK p n i Hin). lia.
Qed.

Lemma sl_cstr_keep : forall m m' p bs sl bl n, cstr_at m p bs sl -> In (p, n) bl ->
  Z.of_nat (length bs + 1 + length sl) <= n ->
  (forall a k i, In (a, k) bl -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  cstr_at m' p bs sl.
Proof.
  intros m m' p bs sl bl n (Hb & Hn & Hm) Hin Hl BK. split; [|split; assumption].
  apply (sl_bytes_keep m m' p _ bl n Hb Hin); [|exact BK]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma sl_aw_keep : forall B m m' live pk ct fl, ms_segs B = rsegs ->
  (forall a, alloc_statics a -> mbyte rsegs m' a = mbyte rsegs m a) ->
  alloc_words B m live pk ct fl -> alloc_words B m' live pk ct fl.
Proof.
  intros B m m' live pk ct fl HS H (W1 & W2 & W3 & W4). unfold alloc_words, word_mem in *. rewrite HS in *.
  split; [|split; [|split]]; intros k Hk;
    (rewrite H; [auto | unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia]).
Qed.

Lemma sl_aw_munch : forall B m m' W live pk ct fl, ms_segs B = rsegs -> alloc_words B m live pk ct fl ->
  munch W m m' -> (forall x, alloc_statics x -> outside W x) -> alloc_words B m' live pk ct fl.
Proof.
  intros B m m' W live pk ct fl HS AW MU Ho. apply (sl_aw_keep B m m' live pk ct fl HS); [|exact AW].
  intros a Ha. pose proof (sl_statics_low a Ha).
  apply (mbyte_munch rsegs W m m' a MU); [lia | exact (Ho a Ha)].
Qed.

Lemma sl_bytes_blk : forall B m p pl, ms_segs B = rsegs -> blk_data B m p pl -> 0 <= p ->
  p + Z.of_nat (length pl) <= 2 ^ 64 -> bytes_at rsegs m p pl.
Proof.
  intros B m p pl HS H H0 H1. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite mrd_mbyte. rewrite <- HS. rewrite (H (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma sl_GI : forall B m j pk ct ct0, alloc_words B m 0 pk ct (2 ^ 64 - 1) -> 0 <= pk < 2 ^ 64 ->
  0 <= ct0 <= Z.of_nat j * 2 ^ 60 -> ct0 <= ct <= ct0 + 1027 -> (j < 4)%nat -> omx_GI B (S j) m.
Proof.
  intros B m j pk ct ct0 AW PK C0 C1 Hj. unfold omx_GI. exists pk, ct. split; [exact AW|]. split; [exact PK|].
  rewrite Nat2Z.inj_succ. assert (Z.of_nat j <= 3) by lia. lia.
Qed.

Lemma sl_len0 : forall bs : list byte, Z.of_nat (length (bs ++ [Z_to_bv 8 0])) = Z.of_nat (length bs) + 1.
Proof. intros bs. rewrite length_app. cbn [length]. lia. Qed.

Lemma sl_free2 : forall b n1 n2, sb_free (sb_free (sb_malloc (sb_malloc b n1) n2) n1) n2 = b.
Proof. intros [l y c] n1 n2. unfold sb_free, sb_malloc. cbn. f_equal; lia. Qed.

Lemma sl_ceil8 : forall x c, x <= c -> c mod 4096 = 0 -> 8 * ((x + 7) / 8) <= c.
Proof. intros x c H1 H2. Z.div_mod_to_equations. lia. Qed.

Ltac sbl := unfold sb_malloc, sb_free in *; cbn [sb_live sb_bytes sb_cap] in *; unfold CAPMAX in *; lia.

Section D.
Context {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis SF : statics_facts B.

Lemma sl_disj : forall L A m md bl p len r n, aa_MR API L A m md ->
  in_blk bl p len -> (forall x, In x bl -> In x (blocks L A)) ->
  In (r, n) (blocks L A) -> ~ In (r, n) bl -> len = 0 \/ p + len <= r \/ r + n <= p.
Proof.
  intros L A m md bl p len r n HM IB INC Hin NIN.
  destruct IB as [->|(a & k & Ha & H1 & H2)]; [left; reflexivity|]. right.
  assert (Hne : (a, k) <> (r, n)) by (intros E; rewrite E in Ha; exact (NIN Ha)).
  destruct (blocks_sep B API L A m md (a, k) (r, n) HM (INC _ Ha) Hin Hne) as [D|D]; cbn in D; lia.
Qed.

Lemma sl_statics_out : forall L A m md r n x, aa_MR API L A m md -> In (r, n) (blocks L A) -> alloc_statics x ->
  x < r \/ r + n <= x.
Proof.
  intros L A m md r n x HM Hin Hs.
  destruct (Z.lt_ge_cases x r) as [H1|H1]; [left; exact H1|].
  destruct (Z.lt_ge_cases x (r + n)) as [H2|H2]; [|right; exact H2]. exfalso.
  pose proof (block_not_img B API AX L A m md r n (x - r) HM Hin ltac:(lia)) as Hn.
  replace (r + (x - r)) with x in Hn by lia. exact (Hn (proj1 (SF x Hs))).
Qed.

End D.

Section P.
Context {fx : FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (ra empty : Z).
Hypothesis FF : frame_facts B API LS SH SK ra empty.

Lemma sl_post : forall L0 A0 regs0 mem0 md0 p n b L A regs mem md,
  kinv B (API rc) SLK L0 A0 regs0 mem0 md0 L A mem md -> st_init_done A = true ->
  alloc_ceiling + SLK <= spZ regs0 ->
  getr regs 10 = Z_to_bv 64 0 -> regs_preserved regs0 regs ->
  Fs.fs_sorted (m_fs md0) = true -> sink_none B mem0 md0 -> res_ok_slots A b ->
  (n = 0 \/ (0 < n /\ exists q, In (q, n) (user_blocks A0) /\ ptr_addr L0 q = p)) ->
  @lib_post_g rc LS B (API rc) SH SK manifest_G SLOT_STACK L0 A0 regs0 mem0 md0 p n b (LL 0 (m_fs md0) [])
    L A regs mem md.
Proof.
  intros L0 A0 regs0 mem0 md0 p n b L A regs mem md J INIT HAC H10 RP HFS (Henv & Hhead & Hnm) RES HP.
  pose proof FF as (HS & _ & _ & _ & _ & _ & _ & HGU & HGG & HCTX & HLK & HLC & HSZ & HSM & HMED & HDB & HTPv & HEO & _ &
    HVM & HDBL & HSH & HSL & HST & _ & _ & _ & _ & _ & _ & HDEL & _ & _).
  pose proof J as (HM & HWF & HBD & (vm & HMD) & HFR & HSC & HB0 & HP0 & HMI).
  pose proof alloc_ceiling_val as Hacv.
  assert (V0 : vml_len B = 0) by (unfold vml_len; rewrite HVM; reflexivity).
  assert (NSO : forall a, static_owned B a -> a < 0x50000).
  { intros a Ha. unfold static_owned in Ha. rewrite V0, HGU, HGG, HLK, HLC, HSZ, HSM, HMED, HDB, HDBL in Ha. lia. }
  assert (NSW : forall a, stat_writes a -> in_globals manifest_G a).
  { intros a Ha. unfold stat_writes in Ha. unfold in_globals, manifest_G. gu.
    destruct Ha as [Ha|Ha]; [exists 0x2f620, 24; split; [left; reflexivity | lia] |
      exists 0x1f3a8, 8; split; [right; left; reflexivity | lia]]. }
  assert (Fr : forall a, (0x4fdc8 <= a < 0x4fdd0 \/ a = 0x4f999 \/ 0x4fdc0 <= a < 0x4fdc4) ->
    mbyte rsegs mem a = mbyte rsegs mem0 a).
  { intros a Ha. apply (HFR a).
    - right. exact (sink_cells_img B HS a Ha).
    - intros Hs. unfold static_owned in Hs. rewrite V0, HGU, HGG, HLK, HLC, HSZ, HSM, HMED, HDB, HDBL in Hs. lia.
    - rewrite HCTX. unfold CTX_SIZE. lia.
    - unfold scratch_k. intros [Hs|Hs].
      + pose proof (sink_cells_img B HS a Ha) as Hi. pose proof (in_img_low B HS a Hi). unfold SLK in *. lia.
      + unfold errno_addr in Hs. rewrite HTPv, HEO in Hs. lia.
    - unfold stat_writes. gu. lia. }
  assert (LOW : forall a, in_img B a -> a < spZ regs0 - SLK) by (intros a Ha; pose proof (in_img_low B HS a Ha); lia).
  unfold lib_post_g. rewrite HS in *.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact INIT|].
  split; [exact H10|]. split; [exact RP|].
  split.
  { exists vm, (m_fds md0), (m_statpins md0). cbn [ll_fs]. split; [|intros; reflexivity].
    rewrite HMD. apply with_vmmaps_os_upd. }
  split.
  { intros q k Hq. pose proof (HP0 _ (blocks_of_user L0 A0 q k Hq)) as Hb.
    destruct (in_blocks L A _ k Hb) as (q' & Hq' & E). exists q'. split; [exact Hq' | symmetry; exact E]. }
  split.
  { intros a Ha Hs. apply (HFR a (or_introl Ha)).
    - intros Ho. pose proof (NSO a Ho). lia.
    - rewrite HCTX. unfold CTX_SIZE. lia.
    - unfold scratch_k, SLK. unfold lib_scratch, SLOT_STACK in Hs. exact Hs.
    - intros Hw. unfold stat_writes in Hw. gu. lia. }
  split.
  { intros a Hi Hs Hc He Hg. apply (HFR a (or_intror Hi) Hs Hc).
    - unfold scratch_k. intros [Hk|Hk]; [pose proof (LOW a Hi); lia | exact (He Hk)].
    - intros Hw. exact (Hg (NSW a Hw)). }
  split.
  { intros a Ha. unfold in_globals, manifest_G in Ha. gu. destruct Ha as (lo & len & Hin & Hr).
    assert (Hg : 0x2f620 <= a < 0x2f638 \/ 0x1f3a8 <= a < 0x1f3b0).
    { cbn in Hin. destruct Hin as [E|[E|[]]]; inversion E; subst; lia. }
    split; intros _; apply globals_writable; exact Hg. }
  split.
  { intros q k i Hq _ Hi. exact (HB0 _ k i (blocks_of_user L0 A0 q k Hq) Hi). }
  split.
  { intros a Ha. apply HSC. unfold scratch_k, SLK. unfold lib_scratch, SLOT_STACK in Ha. exact Ha. }
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HFS|].
  split.
  { unfold sink_none, closed_stdio_env in *. destruct Henv as [Ht Hl].
    unfold YI04.val_mem, word_mem in *. rewrite HS in *.
    split; [split|split].
    - intros k Hk. rewrite Fr; [apply Ht; exact Hk|]. rewrite HST. lia.
    - intros k Hk. rewrite Fr; [apply Hl; exact Hk|]. rewrite HSL. lia.
    - intros k Hk. rewrite Fr; [apply Hhead; exact Hk|]. rewrite HSH. lia.
    - rewrite HMD, with_vmmaps_os_upd, os_upd_fds. exact Hnm. }
  split; [exact HMI|]. split; [rewrite HDEL; exact RES|].
  intros i Hi. destruct HP as [Hn0|(_ & q & Hq & Hpq)]; [lia|].
  subst p. exact (HB0 _ n i (blocks_of_user L0 A0 q n Hq) Hi).
Qed.

End P.

Section M.
Hypothesis MEMCHR : memchr_contract.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis LIVE : fuzz_alloc_live_contract.
Hypothesis RESET : fuzz_alloc_peak_reset_contract.
Hypothesis PEAK : fuzz_alloc_peak_contract.
Hypothesis CBA : check_bounded_alloc_contract.
Hypothesis CAW : check_as_written_contract.
Hypothesis CRC : check_reject_clean_contract.
Hypothesis KBC : kindb_callees.
Context {fx : FPState} {rc : lib.Reusable.YM05.RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (ra empty : Z).
Hypothesis FF : frame_facts B API LS SH SK ra empty.

Ltac rok H := rewrite H; apply ret_ok_even; vm_compute; reflexivity.

Lemma slot_body : forall j, (j < 4)%nat ->
  @lib_contract_g fx rc LS B (API rc) SH SK manifest_G frame_RELRO (omx_GI B) j ENTRY ra empty SLOT_STACK.
Proof.
  intros j Hj L A regs mem md p n pl b K PREX GI0 _ MI0 TSZ FRM KC.
  pose proof FF as (HS & RAE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & HEMP & _ & _ & _ & _ & HLIBK & _ & HROOM & _).
  pose proof (ff_alloc_extra B API LS SH SK ra empty FF) as AX.
  pose proof (ff_statics_facts B API LS SH SK ra empty FF) as SF.
  pose proof (ff_statics_free B API LS SH SK ra empty FF) as SFR.
  pose proof (ff_errno_low B API LS SH SK ra empty FF) as ERR.
  pose proof (ff_statics_noerrno B API LS SH SK ra empty FF) as SNE.
  pose proof (ff_malloc_syms_omx B API LS SH SK ra empty FF) as MSO.
  pose proof (ff_block_slack_present B API LS SH SK ra empty FF) as BSP.
  assert (MALLOC : forall fx' : FPState, @malloc_contract fx' rc B (API rc)) by (intros fx'; eapply ff_malloc; exact FF).
  assert (FREE : forall fx' : FPState, @free_contract fx' rc B (API rc)) by (intros fx'; eapply ff_free; exact FF).
  destruct KBC as (KCNO & KNAM & KSTV & KCRT).
  assert (CNO : forall fx' : FPState, @check_no_overread_contract fx' rc B (API rc))
    by (intros fx'; exact (KCNO B API LS SH SK ra empty FF rc fx')).
  assert (NAMES : forall fx' : FPState, @names_contract fx' rc B (API rc))
    by (intros fx'; exact (KNAM B API LS SH SK ra empty FF rc fx')).
  assert (STARVED : forall fx' : FPState, @check_reject_clean_starved_contract fx' rc B (API rc))
    by (intros fx'; exact (KSTV B API LS SH SK ra empty FF rc fx')).
  assert (CRT : forall fx' : FPState, @check_round_trip_contract fx' rc B (API rc))
    by (intros fx'; exact (KCRT B API LS SH SK ra empty FF rc fx')).
  clear KCNO KNAM KSTV KCRT.
  destruct PREX as (PRE & HN & BLK & RES & ROOMb & SNK & FDL & HFS & SP47).
  destruct PRE as (HM & HWF & HBD & INIT & HRA & H16 & HAC & H63 & HWS & HTP & HER & R10 & R11 & HP & RODATA).
  destruct (HROOM b n ROOMb) as (BL64 & BBY & BCAP).
  assert (CAPv : sb_cap b = 296960) by (rewrite BCAP; reflexivity). clear BCAP HROOM ROOMb.
  destruct GI0 as (pk0 & ct0 & AW0 & PK0 & CT0 & CT1).
  unfold SLOT_STACK in HAC, HWS.
  assert (HAC' : alloc_ceiling + SLK <= spZ regs) by (unfold SLK; lia).
  pose proof alloc_ceiling_val as Hacv.
  rewrite HS in MI0.
  pose proof (zr_word (getr regs 2)) as Rsp. unfold inr64 in Rsp. change (bv_unsigned (getr regs 2)) with (spZ regs) in Rsp.
  assert (HPp : n = 0 \/ (0 < n /\ exists q, In (q, n) (user_blocks A) /\ ptr_addr L q = p)).
  { destruct HP as [(E0 & _)|(H0 & Hq)]; [left; exact E0 | right; split; [exact H0 | exact Hq]]. }
  assert (ROra : YK0s.ret_ok (getr regs 1)).
  { rewrite HRA. apply ret_ok_even. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia. }
  rewrite HLIBK.
  eapply SR_realizes; cycle 1. { intros c' Hc'. exact (KC _ c' Hc'). }
  pose proof (sl_k_range pl) as (K0 & K1 & K2).
  pose proof (sl_un_range pl) as UNR. pose proof (sl_tn_range pl) as TNR. rewrite sl_tbuf_len in TNR.
  pose proof (sl_ub_len pl) as UBL. pose proof (sl_tb_len pl) as TBL.
  assert (S01 : 0 <= sl_s pl <= 1) by (destruct (sl_s_range pl) as [(E & _)|(E & _)]; lia).
  assert (EURI : sl_uri p pl = p + sl_s pl) by reflexivity.
  assert (ETXT : sl_text p pl = p + sl_s pl + sl_k pl) by reflexivity.
  assert (PL0 : 4096 <= p /\ p + Z.of_nat (length pl) <= alloc_ceiling /\
    (Z.of_nat (length pl) = 0 \/ In (p, Z.of_nat (length pl)) (blocks L A))).
  { destruct HP as [(E0 & Ep) | (Hn0 & q & Hq & Ep)].
    - rewrite Ep, HEMP. rewrite E0 in HN. split; [lia|]. split; [lia|]. left; lia.
    - pose proof (blocks_of_user L A q n Hq) as Hb. rewrite Ep, HN in Hb.
      destruct (sl_block_range B (API rc) L A mem md p _ HM Hb) as [H1 H2]. split; [lia|]. split; [lia|]. right; exact Hb. }
  destruct PL0 as (P4096 & PHI & PB).
  assert (IBU : in_blk (blocks L A) (sl_uri p pl) (Z.of_nat (length (sl_ub pl)))).
  { destruct PB as [E|Hb]; [left; lia | right; exists p, (Z.of_nat (length pl)); split; [exact Hb | lia]]. }
  assert (IBT : in_blk (blocks L A) (sl_text p pl) (Z.of_nat (length (sl_tb pl)))).
  { destruct PB as [E|Hb]; [left; lia | right; exists p, (Z.of_nat (length pl)); split; [exact Hb | lia]]. }
  assert (BP : bytes_at rsegs mem p pl) by (apply (sl_bytes_blk B mem p pl HS BLK); lia).
  pose proof (sl_ub_bytes rsegs mem p pl BP) as BU0.
  pose proof (sl_tb_bytes rsegs mem p pl BP) as BT0.
  assert (J0 : kinv B (API rc) SLK L A regs mem md L A mem md).
  { apply (kinv_init B (API rc) HS SLK L A regs mem md HM HWF HBD); [| exact HER | exact MI0].
    intros a Ha. apply HWS. unfold SLK in Ha. lia. }
  destruct (kinv_md _ _ _ _ _ _ _ _ _ _ _ _ J0) as [Hh0 Hl0].
  assert (STK0 : stk rsegs mem (spZ regs - SLK) (spZ regs)).
  { apply stk_of_writable; [unfold SLK; lia | lia |]. intros a Ha. rewrite <- HS. apply HWS. unfold SLK in Ha. lia. }
  clear BLK HWS HER HP.
  eapply evt_SR_canon; [ | exact Hh0 | exact Hl0 | ].
  { rewrite canon_mkst. rewrite HS. unfold mkR_of.
    apply evt_normalize; [exact rsegs_wx | exact MI0 |].
    apply (slot_sa.sl_s0 MEMCHR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize rsegs mem)
             (spZ regs - SLK) p pl).
    - exact R10.
    - rewrite <- HN. exact R11.
    - exact P4096.
    - lia.
    - exact (bytes_at_normalize rsegs mem p pl MI0 BP).
    - change (bv_unsigned (reg_get regs 2)) with (spZ regs). left. unfold SLK in HAC'. lia.
    - exact (mem_inv_normalize rsegs mem).
    - change (bv_unsigned (reg_get regs 2)) with (spZ regs). apply (stk_norm mem _ _ MI0); [unfold SLK; lia | exact STK0].
    - change (bv_unsigned (reg_get regs 2)) with (spZ regs). unfold SLK; lia. }
  intros ms1 (can & (s0 & Q0 & REL & ROS) & EQV).
  destruct Q0 as [(TNB & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n & Es0 &
                   MU1n & WM1n & _ & _)
                 |(TNS & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & j1 & m1n & Es0 & FRn & MU1n &
                   WM1n & _ & _)];
    subst s0; destruct (rel_eqv_s _ _ _ _ _ _ _ _ REL EQV) as [EQV' HREL]; clear REL EQV;
    set (m1 := ms_mem can) in *;
    destruct (norm_back mem m1n m1 _ MI0 HREL ROS MU1n WM1n) as (MU1 & WM1 & MI1).
  - apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV1 & RA1 & A01 & _).
    clear XR. set (R1 := ms_regs ms1) in *.
    change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *.
    assert (J1 : kinv B (API rc) SLK L A regs mem md L A m1 md).
    { apply (kinv_kindA B (API rc) HS AX SLK L A regs mem md L A mem md m1 _ J0 MU1 WM1 MI1 HAC').
      intros x Hx. destruct (Z.lt_ge_cases x (spZ regs - 64)) as [X1|X1]; [left; apply outside_one; lia|].
      destruct (Z.lt_ge_cases x (spZ regs)) as [X2|X2]; [right; left; unfold SLK; lia | left; apply outside_one; lia]. }
    assert (AW1 : alloc_words B m1 0 pk0 ct0 (2 ^ 64 - 1)).
    { apply (sl_aw_munch B mem m1 _ 0 pk0 ct0 (2 ^ 64 - 1) HS AW0 MU1). intros x Hx.
      pose proof (sl_statics_low x Hx). apply outside_one. lia. }
    change (reg_get regs 1) with (getr regs 1).
    rewrite (KindB.ret_pc_ok _ ROra). rewrite HRA.
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply SR_ret. cbv beta. exists fx, L, A, R1, m1, md.
    split; [reflexivity|]. split; [exact FRM|]. split.
    + apply (sl_post B API ra empty FF L A regs mem md p n b L A R1 m1 md J1 INIT HAC' A01).
      * apply preserved_of_saved_s. exact SV1.
      * exact HFS.
      * exact SNK.
      * exact RES.
      * exact HPp.
    + apply (sl_GI B m1 j pk0 ct0 ct0 AW1 PK0); [lia | lia | exact Hj].
  - pose proof (rw_cells_rel m1 m1n _ _ HREL FRn) as FR1. clear FRn HREL ROS MU1n WM1n R10 R11.
    apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
    pose proof (getr_eqv _ _ XR) as GX.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV1 & RA1 & A01 & A11).
    clear XR. set (R1 := ms_regs ms1) in *.
    assert (A21 : getr R1 12 = Z_to_bv 64 (sl_text p pl)) by (rewrite <- GX; reflexivity).
    assert (A31 : getr R1 13 = Z_to_bv 64 (sl_tn pl)) by (rewrite <- GX; reflexivity).
    clear GX.
    change (bv_unsigned (reg_get regs 2)) with (spZ regs) in *.
    assert (J1 : kinv B (API rc) SLK L A regs mem md L A m1 md).
    { apply (kinv_kindA B (API rc) HS AX SLK L A regs mem md L A mem md m1 _ J0 MU1 WM1 MI1 HAC').
      intros x Hx. destruct (Z.lt_ge_cases x (spZ regs - 64)) as [X1|X1]; [left; apply outside_one; lia|].
      destruct (Z.lt_ge_cases x (spZ regs)) as [X2|X2]; [right; left; unfold SLK; lia | left; apply outside_one; lia]. }
    assert (AW1 : alloc_words B m1 0 pk0 ct0 (2 ^ 64 - 1)).
    { apply (sl_aw_munch B mem m1 _ 0 pk0 ct0 (2 ^ 64 - 1) HS AW0 MU1). intros x Hx.
      pose proof (sl_statics_low x Hx). apply outside_one. lia. }
    clear J0 MU1 WM1 AW0 STK0 Hh0 Hl0.
    destruct (sp_stage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV1 ltac:(lia)) as [SP1 TP1].
    change (reg_get regs 4) with (getr regs 4) in TP1. rewrite HTP in TP1.
    assert (RO1 : YK0s.ret_ok (getr R1 1)) by (rok RA1).
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply (sl_cno_call B (API rc) HS AX ERR CNO fx L A regs mem md L A R1 m1 md b (sl_ub pl) (sl_tb pl) pk0 ct0
             (sl_uri p pl) (sl_text p pl) _ J1 INIT FRM HAC' H16 H63 TSZ SP1 RO1 TP1 A01 A21 ltac:(lia) ltac:(lia)
             ltac:(rewrite UBL; exact A11) ltac:(rewrite TBL; exact A31)
             (payload_now_k B (API rc) L A regs mem md L A m1 md _ _ J1 BU0 IBU)
             (payload_now_k B (API rc) L A regs mem md L A m1 md _ _ J1 BT0 IBT)
             (sl_ub_nz pl) (sl_tb_nz pl) ltac:(lia) ltac:(lia) IBU IBT AW1 PK0 ltac:(lia) ltac:(lia) RES
             ltac:(sbl) ltac:(sbl) ltac:(sbl)).
    intros f2 L2 A2 R2 m2 md2 pk2 ct2 FRM2 INIT2 RP2 J2 BL2 BK2 KP2 AW2 PK2 CT2 RES2.
    pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV1 RP2) as SV2.
    pose proof (frame_keep_s m1 m2 _ _ (spZ R1) FR1 ltac:(lia) KP2) as FR2.
    clear FR1 KP2 SV1 RP2 J1 MI1 BK2 AW1 A01 A11 A21 A31 TP1 SP1 RO1.
    destruct (kinv_md _ _ _ _ _ _ _ _ _ _ _ _ J2) as [Hh2 Hl2].
    rewrite RA1.
    eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
    { rewrite (canon_saved f2 R2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV2). rewrite HS.
      apply (slot_sc.sl_s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (sl_un pl));
        [reflexivity | lia]. }
    intros ms3 (can3 & (x3 & Ecan) & EQV). subst can3.
    apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV3 & RA3 & A03 & _).
    clear XR SV2 Hh2 Hl2. set (R3 := ms_regs ms3) in *.
    destruct (sp_stage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV3 ltac:(lia)) as [SP3 TP3].
    change (reg_get regs 4) with (getr regs 4) in TP3. rewrite HTP in TP3.
    assert (RO3 : YK0s.ret_ok (getr R3 1)) by (rok RA3).
    assert (RMU : room_slots b (sl_un pl + 1)) by (apply room_slots_small; sbl).
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply (sl_malloc_call B (API rc) HS AX SF SFR ERR SNE MSO MALLOC f2 L A regs mem md L2 A2 R3 m2 md2 (sl_un pl + 1) b _
             J2 INIT2 HAC' H16 H63 SP3 RO3 TP3 A03 ltac:(lia) RES2 RMU).
    intros L4 A4 R4 m4 md4 ua RP4 U10 J4 INIT4 RES4 U4096 URNG (ju & RWU) INU NINU RMBU INC4 BK4 KP4.
    rewrite BL2 in INC4, NINU, RMBU.
    pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV3 RP4) as SV4.
    pose proof (frame_keep_s m2 m4 _ _ (spZ R3) FR2 ltac:(lia) (fun a Ha => KP4 a (or_introl Ha))) as FR4.
    pose proof (sl_aw_keep B m2 m4 0 pk2 ct2 (2 ^ 64 - 1) HS (fun a Ha => proj1 (KP4 a (or_intror Ha))) AW2) as AW4.
    clear FR2 KP4 SV3 RP4 J2 BK4 AW2 A03 TP3 SP3 RO3 RMU.
    destruct (kinv_md _ _ _ _ _ _ _ _ _ _ _ _ J4) as [Hh4 Hl4].
    pose proof (kinv_mi _ _ _ _ _ _ _ _ _ _ _ _ J4) as MI4.
    pose proof (kinv_MR _ _ _ _ _ _ _ _ _ _ _ _ J4) as HM4.
    rewrite RA3.
    eapply evt_SR_canon; [ | exact Hh4 | exact Hl4 | ].
    { rewrite (canon_saved f2 R4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV4). rewrite HS.
      apply evt_normalize; [exact rsegs_wx | exact MI4 |].
      apply (slot_sb.sl_s2 MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize rsegs m4)
               ua (sl_un pl) (sl_tn pl) (sl_uri p pl) (sl_ub pl) ju).
      - exact U10.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact U4096.
      - lia.
      - lia.
      - lia.
      - exact UBL.
      - exact (bytes_at_normalize rsegs m4 _ _ MI4 (payload_now_k B (API rc) L A regs mem md L4 A4 m4 md4 _ _ J4 BU0 IBU)).
      - destruct (sl_disj B (API rc) L4 A4 m4 md4 (blocks L A) _ _ _ _ HM4 IBU INC4 INU NINU) as [D|D];
          rewrite UBL in D; lia.
      - exact RWU.
      - exact (mem_inv_normalize rsegs m4). }
    intros ms5 (can5 & (s0 & (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5n & Es0 & CPUn & MU5n & WM5n & _) &
      REL & ROS) & EQV). subst s0.
    destruct (rel_eqv_s _ _ _ _ _ _ _ _ REL EQV) as [EQV' HREL]. clear REL EQV.
    set (m5 := ms_mem can5) in *.
    destruct (norm_back m4 m5n m5 _ MI4 HREL ROS MU5n WM5n) as (MU5 & WM5 & MI5).
    pose proof (proj2 (bytes_at_rel rsegs m5 m5n _ _ HREL) CPUn) as CPU.
    clear HREL ROS MU5n WM5n CPUn.
    apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV5 & RA5 & A05 & _).
    clear XR. set (R5 := ms_regs ms5) in *.
    pose proof (kinv_copy B (API rc) HS AX L A regs mem md L4 A4 m4 md4 m5 ua (sl_un pl + 1) _ J4 MU5 WM5 MI5 HAC'
                  INU NINU CPU ltac:(rewrite sl_len0, UBL; lia)) as J5.
    pose proof (sl_frame_munch m4 m5 _ _ _ _ _ _ _ _ _ _ FR4 MU5 ltac:(intros xx Hxx; apply outside_one; lia)) as FR5.
    pose proof (sl_aw_munch B m4 m5 _ 0 pk2 ct2 (2 ^ 64 - 1) HS AW4 MU5
                  ltac:(intros xx Hxx; apply outside_one;
                        exact (sl_statics_out B (API rc) AX SF L4 A4 m4 md4 ua (sl_un pl + 1) xx HM4 INU Hxx))) as AW5.
    clear FR4 AW4 MU5 WM5 J4 RWU SV4 Hh4 Hl4 MI4 HM4.
    destruct (sp_stage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV5 ltac:(lia)) as [SP5 TP5].
    change (reg_get regs 4) with (getr regs 4) in TP5. rewrite HTP in TP5.
    assert (RO5 : YK0s.ret_ok (getr R5 1)) by (rok RA5).
    assert (RMT : room_slots (sb_malloc b (sl_un pl + 1)) (sl_tn pl + 1)) by (apply room_slots_big; sbl).
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply (sl_malloc_call B (API rc) HS AX SF SFR ERR SNE MSO MALLOC f2 L A regs mem md L4 A4 R5 m5 md4 (sl_tn pl + 1)
             (sb_malloc b (sl_un pl + 1)) _ J5 INIT4 HAC' H16 H63 SP5 RO5 TP5 A05 ltac:(lia) RES4 RMT).
    intros L6 A6 R6 m6 md6 ta RP6 T10 J6 INIT6 RES6 T4096 TRNG (jt & RWT) INT NINT RMBT INC6 BK6 KP6.
    pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV5 RP6) as SV6.
    pose proof (frame_keep_s m5 m6 _ _ (spZ R5) FR5 ltac:(lia) (fun a Ha => KP6 a (or_introl Ha))) as FR6.
    pose proof (sl_aw_keep B m5 m6 0 pk2 ct2 (2 ^ 64 - 1) HS (fun a Ha => proj1 (KP6 a (or_intror Ha))) AW5) as AW6.
    pose proof (sl_bytes_keep m5 m6 ua _ (blocks L4 A4) (sl_un pl + 1) CPU INU ltac:(rewrite sl_len0, UBL; lia) BK6)
      as CPU6.
    assert (NINT0 : ~ In (ta, sl_tn pl + 1) (blocks L A)) by (intros H; exact (NINT (INC4 _ H))).
    assert (NEut : (ua, sl_un pl + 1) <> (ta, sl_tn pl + 1)) by (intros E; rewrite <- E in NINT; exact (NINT INU)).
    pose proof (INC6 _ INU) as INU6.
    assert (INC0 : forall y, In y (blocks L A) -> In y (blocks L6 A6)) by (intros y Hy; exact (INC6 y (INC4 y Hy))).
    clear FR5 KP6 SV5 RP6 J5 BK6 AW5 CPU A05 TP5 SP5 RO5 RMT MI5.
    destruct (kinv_md _ _ _ _ _ _ _ _ _ _ _ _ J6) as [Hh6 Hl6].
    pose proof (kinv_mi _ _ _ _ _ _ _ _ _ _ _ _ J6) as MI6.
    pose proof (kinv_MR _ _ _ _ _ _ _ _ _ _ _ _ J6) as HM6.
    pose proof (sl_off_statics B (API rc) AX SF L6 A6 m6 md6 ta (sl_tn pl + 1) (sl_tn pl + 1) HM6 INT ltac:(lia)
                  ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as OFT.
    pose proof (sl_off_statics B (API rc) AX SF L6 A6 m6 md6 ua (sl_un pl + 1) (sl_un pl + 1) HM6 INU6 ltac:(lia)
                  ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as OFU.
    unfold off_statics in OFT, OFU. gu.
    pose proof (blocks_sep B (API rc) L6 A6 m6 md6 _ _ HM6 INU6 INT NEut) as DUT. cbn [fst snd] in DUT.
    rewrite RA5.
    eapply evt_SR_canon; [ | exact Hh6 | exact Hl6 | ].
    { rewrite (canon_saved f2 R6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV6). rewrite HS.
      apply evt_normalize; [exact rsegs_wx | exact MI6 |].
      apply (slot_sb.sl_s3 MEMCPY LIVE RESET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               (normalize rsegs m6) ta (sl_tn pl) (sl_text p pl) (Z_to_bv 64 0) (sl_tb pl) jt).
      - exact T10.
      - reflexivity.
      - reflexivity.
      - exact T4096.
      - lia.
      - lia.
      - lia.
      - exact TBL.
      - exact (bytes_at_normalize rsegs m6 _ _ MI6 (payload_now_k B (API rc) L A regs mem md L6 A6 m6 md6 _ _ J6 BT0 IBT)).
      - destruct (sl_disj B (API rc) L6 A6 m6 md6 (blocks L A) _ _ _ _ HM6 IBT INC0 INT NINT0) as [D|D];
          rewrite TBL in D; lia.
      - exact RWT.
      - apply (bytes_at_normalize rsegs m6 _ _ MI6). destruct AW6 as (W1 & _). rewrite <- HS.
        exact (KindB.word_mem_bytes _ m6 Ledger.G_LIVE 0 ltac:(lia) ltac:(gu; lia) ltac:(gu; lia) W1).
      - split; [lia|]. split; [lia|]. intros i Hi. apply (globals_writable (normalize rsegs m6) (0x2f628 + i)). lia.
      - exact (mem_inv_normalize rsegs m6). }
    intros ms7 (can7 & (s0 & (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7n & Es0 & CPTn & PKn & MU7n & WM7n & _) &
      REL & ROS) & EQV). subst s0.
    destruct (rel_eqv_s _ _ _ _ _ _ _ _ REL EQV) as [EQV' HREL]. clear REL EQV.
    set (m7 := ms_mem can7) in *.
    destruct (norm_back m6 m7n m7 _ MI6 HREL ROS MU7n WM7n) as (MU7 & WM7 & MI7).
    pose proof (proj2 (bytes_at_rel rsegs m7 m7n _ _ HREL) CPTn) as CPT.
    pose proof (proj2 (bytes_at_rel rsegs m7 m7n _ _ HREL) PKn) as PK7.
    clear HREL ROS MU7n WM7n CPTn PKn.
    apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV7 & RA7 & A07 & A17).
    clear XR. set (R7 := ms_regs ms7) in *.
    assert (J7 : kinv B (API rc) SLK L A regs mem md L6 A6 m7 md6).
    { apply (kinv_kindS B (API rc) HS AX SF SFR SLK L A regs mem md L6 A6 m6 md6 m7 _ J6 MU7 WM7 MI7 HAC').
      intros y Hy.
      assert (Cy : (0x2f628 <= y < 0x2f630) \/ (ta <= y < ta + (sl_tn pl + 1)) \/
                   ((y < 0x2f628 \/ 0x2f630 <= y) /\ (y < ta \/ ta + (sl_tn pl + 1) <= y))) by lia.
      destruct Cy as [Cy|[Cy|Cy]].
      - right; right; left. unfold stat_writes. gu. lia.
      - right; right; right. exists ta, (sl_tn pl + 1). split; [exact INT|]. split; [exact NINT0|]. split; [lia|].
        pose proof (block_not_img B (API rc) AX L6 A6 m6 md6 ta _ (y - ta) HM6 INT ltac:(lia)) as Hni.
        replace y with (ta + (y - ta)) by lia.
        apply (present_of_bytes B HS m7 ta _ (y - ta) CPT); [rewrite sl_len0, TBL; lia | exact Hni].
      - left. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    pose proof (sl_frame_munch m6 m7 _ _ _ _ _ _ _ _ _ _ FR6 MU7
                  ltac:(intros xx Hxx; cbn [outside]; split; [lia|]; split; [lia | exact I])) as FR7.
    assert (AW7 : alloc_words B m7 0 0 ct2 (2 ^ 64 - 1)).
    { destruct AW6 as (W1 & W2 & W3 & W4). unfold alloc_words.
      split; [|split; [|split]].
      - apply (word_mem_munch _ _ m6 m7 _ _ MU7); [gu; lia | gu; lia | | exact W1].
        intros xx Hxx. gu. cbn [outside]. split; [lia|]. split; [lia | exact I].
      - apply (KindB.bytes_word_mem _ m7 _ 0 ltac:(lia)). rewrite HS. exact PK7.
      - apply (word_mem_munch _ _ m6 m7 _ _ MU7); [gu; lia | gu; lia | | exact W3].
        intros xx Hxx. gu. cbn [outside]. split; [lia|]. split; [lia | exact I].
      - apply (word_mem_munch _ _ m6 m7 _ _ MU7); [gu; lia | gu; lia | | exact W4].
        intros xx Hxx. gu. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    pose proof (sl_bytes_munch m6 m7 _ ua _ CPU6 MU7
                  ltac:(intros xx Hxx; rewrite sl_len0, UBL in Hxx; cbn [outside]; split; [lia|]; split; [lia | exact I]))
      as CPU7.
    clear FR6 AW6 MU7 WM7 J6 RWT SV6 Hh6 Hl6 MI6 PK7 CPU6.
    pose proof (kinv_MR _ _ _ _ _ _ _ _ _ _ _ _ J7) as HM7.
    destruct (sp_stage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV7 ltac:(lia)) as [SP7 TP7].
    change (reg_get regs 4) with (getr regs 4) in TP7. rewrite HTP in TP7.
    assert (RO7 : YK0s.ret_ok (getr R7 1)) by (rok RA7).
    destruct (sl_slack B (API rc) BSP L6 A6 m7 md6 ta (sl_tn pl + 1) (sl_tb pl) HM7 INT CPT ltac:(lia) (sl_tb_nz pl))
      as (tsl & CT7 & _).
    destruct (KindB.cstr_trim m7 ta (sl_tb pl) tsl CT7) as (ts & CT & CTL). clear CT7.
    destruct (sl_slack B (API rc) BSP L6 A6 m7 md6 ua (sl_un pl + 1) (sl_ub pl) HM7 INU6 CPU7 ltac:(lia) (sl_ub_nz pl))
      as (usl & CU7 & _).
    destruct (KindB.cstr_trim m7 ua (sl_ub pl) usl CU7) as (us & CU & CUL). clear CU7.
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply (sl_names_call B (API rc) HS AX SF ERR NAMES f2 L A regs mem md L6 A6 R7 m7 md6
             (sb_malloc (sb_malloc b (sl_un pl + 1)) (sl_tn pl + 1)) (sl_tb pl) ts (sl_ub pl) us 0 ct2 ta ua _
             J7 INIT6 FRM2 HAC' H16 H63 TSZ SP7 RO7 TP7 A07 A17 CT CTL CU CUL
             ltac:(rewrite TBL; exact INT) ltac:(rewrite UBL; exact INU6) ltac:(lia) AW7 ltac:(lia) ltac:(lia)
             ltac:(lia) RES6 ltac:(sbl) ltac:(sbl) ltac:(sbl)).
    intros f8 L8 A8 R8 m8 md8 pk8 ct8 FRM8 INIT8 RP8 N10 J8 BL8 BK8 KP8 (ts8 & CT8) (us8 & CU8) AW8 PKC8 CT8b RES8.
    pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV7 RP8) as SV8.
    pose proof (frame_keep_s m7 m8 _ _ (spZ R7) FR7 ltac:(lia) KP8) as FR8.
    destruct (KindB.cstr_trim m8 ta _ ts8 CT8) as (ts' & CT8' & CTL8). clear CT8.
    destruct (KindB.cstr_trim m8 ua _ us8 CU8) as (us' & CU8' & CUL8). clear CU8.
    assert (PK8 : 0 <= pk8 <= sl_un pl + 3) by (destruct PKC8 as [(_ & E)|(_ & E)]; rewrite E; lia).
    clear FR7 KP8 SV7 RP8 J7 BK8 AW7 CT CU CTL CUL A07 A17 TP7 SP7 RO7 MI7 HM7 CPT CPU7 PKC8.
    destruct (kinv_md _ _ _ _ _ _ _ _ _ _ _ _ J8) as [Hh8 Hl8].
    pose proof (kinv_mi _ _ _ _ _ _ _ _ _ _ _ _ J8) as MI8.
    pose proof (kinv_MR _ _ _ _ _ _ _ _ _ _ _ _ J8) as HM8.
    assert (USP : bv_unsigned (Z_to_bv 64 (spZ regs + -64)) = spZ regs - 64) by (apply unsigned_lit; lia).
    assert (TSE : ta + Z.of_nat (length (sl_tb pl) + 1 + length ts') <= alloc_ceiling).
    { rewrite (slack_eq ta _ _ CTL8).
      pose proof (sl_ceil8 (ta + (Z.of_nat (length (sl_tb pl)) + 1)) alloc_ceiling ltac:(lia) (proj2 Hacv)). lia. }
    assert (USE : ua + Z.of_nat (length (sl_ub pl) + 1 + length us') <= alloc_ceiling).
    { rewrite (slack_eq ua _ _ CUL8).
      pose proof (sl_ceil8 (ua + (Z.of_nat (length (sl_ub pl)) + 1)) alloc_ceiling ltac:(lia) (proj2 Hacv)). lia. }
    rewrite RA7.
    eapply evt_SR_canon; [ | exact Hh8 | exact Hl8 | ].
    { rewrite (canon_saved f8 R8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV8). rewrite HS.
      apply evt_normalize; [exact rsegs_wx | exact MI8 |].
      apply (slot_sc.sl_s4 PEAK CBA CAW CRC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               (normalize rsegs m8) (spZ regs - SLK) (sl_un pl) ua ta (Z_to_bv 64 0) (Z_to_bv 64 pk8)
               (sl_tb pl) ts' (sl_ub pl) us').
      - exact N10.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact UBL.
      - lia.
      - apply (bytes_at_normalize rsegs m8 _ _ MI8). destruct AW8 as (_ & W2 & _). rewrite <- HS.
        exact (KindB.word_mem_bytes _ m8 Ledger.G_PEAK pk8 ltac:(lia) ltac:(gu; lia) ltac:(gu; lia) W2).
      - apply (bytes_at_normalize rsegs m8 _ _ MI8). destruct AW8 as (W1 & _). rewrite <- HS.
        exact (KindB.word_mem_bytes _ m8 Ledger.G_LIVE 0 ltac:(lia) ltac:(gu; lia) ltac:(gu; lia) W1).
      - rewrite !unsigned_lit by lia. lia.
      - exact (KindB.cstr_normalize m8 ta _ _ MI8 CT8').
      - exact (KindB.cstr_normalize m8 ua _ _ MI8 CU8').
      - exact T4096.
      - exact U4096.
      - lia.
      - apply (bytes_at_normalize rsegs m8 _ _ MI8). apply (ro_agree_bytes m8 _ _ MI8). vm_compute. reflexivity.
      - exact (mem_inv_normalize rsegs m8).
      - rewrite USP. apply (stk_norm m8 _ _ MI8); [unfold SLK; lia |].
        apply stk_of_writable; [unfold SLK; lia | lia |]. intros a Ha.
        apply (kinv_sc _ _ _ _ _ _ _ _ _ _ _ _ J8). unfold scratch_k. left. lia.
      - rewrite USP. unfold SLK; lia.
      - rewrite USP. lia.
      - unfold off_stack. rewrite USP. left. lia.
      - unfold off_stack. rewrite USP. left. lia.
      - unfold off_stack. rewrite USP. left. lia. }
    intros ms9 (can9 & (s0 & (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9n & Es0 & MU9n & WM9n & _ & _) &
      REL & ROS) & EQV). subst s0.
    destruct (rel_eqv_s _ _ _ _ _ _ _ _ REL EQV) as [EQV' HREL]. clear REL EQV.
    set (m9 := ms_mem can9) in *.
    destruct (norm_back m8 m9n m9 _ MI8 HREL ROS MU9n WM9n) as (MU9 & WM9 & MI9).
    clear HREL ROS MU9n WM9n. rewrite USP in MU9.
    apply eqv_shape in EQV' as [Ems XR]. rewrite Ems. clear Ems.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV9 & RA9 & A09 & A19).
    clear XR. set (R9 := ms_regs ms9) in *.
    assert (J9 : kinv B (API rc) SLK L A regs mem md L8 A8 m9 md8).
    { apply (kinv_kindA B (API rc) HS AX SLK L A regs mem md L8 A8 m8 md8 m9 _ J8 MU9 WM9 MI9 HAC').
      intros y Hy. destruct (Z.lt_ge_cases y (spZ regs - 64 - 288)) as [X1|X1]; [left; apply outside_one; lia|].
      destruct (Z.lt_ge_cases y (spZ regs - 64)) as [X2|X2]; [right; left; unfold SLK; lia | left; apply outside_one; lia]. }
    pose proof (sl_frame_munch m8 m9 _ _ _ _ _ _ _ _ _ _ FR8 MU9 ltac:(intros xx Hxx; apply outside_one; lia)) as FR9.
    pose proof (sl_aw_munch B m8 m9 _ 0 pk8 ct8 (2 ^ 64 - 1) HS AW8 MU9
                  ltac:(intros xx Hxx; pose proof (sl_statics_low xx Hxx); apply outside_one; lia)) as AW9.
    pose proof (sl_cstr_munch m8 m9 _ ta _ _ CT8' MU9 ltac:(intros xx Hxx; apply outside_one; lia)) as CT9.
    pose proof (sl_cstr_munch m8 m9 _ ua _ _ CU8' MU9 ltac:(intros xx Hxx; apply outside_one; lia)) as CU9.
    clear FR8 AW8 MU9 WM9 J8 SV8 Hh8 Hl8 MI8 HM8 CT8' CU8'.
    destruct (sp_stage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV9 ltac:(lia)) as [SP9 TP9].
    change (reg_get regs 4) with (getr regs 4) in TP9. rewrite HTP in TP9.
    assert (RO9 : YK0s.ret_ok (getr R9 1)) by (rok RA9).
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply (sl_starved_call B (API rc) HS AX SF ERR STARVED f8 L A regs mem md L8 A8 R9 m9 md8
             (sb_malloc (sb_malloc b (sl_un pl + 1)) (sl_tn pl + 1)) (sl_tb pl) ts' (sl_ub pl) us' pk8 ct8 ta ua _
             J9 INIT8 FRM8 HAC' H16 H63 TSZ SP9 RO9 TP9 A09 A19 CT9 CTL8 CU9 CUL8
             ltac:(rewrite BL8, TBL; exact INT) ltac:(rewrite BL8, UBL; exact INU6) ltac:(lia) AW9 ltac:(lia) ltac:(lia)
             ltac:(lia) RES8 ltac:(sbl) ltac:(sbl) ltac:(sbl)).
    intros f10 L10 A10 R10 m10 md10 ct10 FRM10 INIT10 RP10 J10 BL10 BK10 KP10 (ts10 & CT10) (us10 & CU10) AW10 CT10b
      RES10.
    pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV9 RP10) as SV10.
    pose proof (frame_keep_s m9 m10 _ _ (spZ R9) FR9 ltac:(lia) KP10) as FR10.
    clear FR9 KP10 SV9 RP10 J9 BK10 AW9 CT9 CU9 CT10 A09 A19 TP9 SP9 RO9 MI9.
    destruct (kinv_md _ _ _ _ _ _ _ _ _ _ _ _ J10) as [Hh10 Hl10].
    rewrite RA9.
    eapply evt_SR_canon; [ | exact Hh10 | exact Hl10 | ].
    { rewrite (canon_saved f10 R10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV10). rewrite HS.
      apply (slot_sc.sl_s5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). }
    intros ms11 (can11 & Ecan & EQV). subst can11.
    apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV11 & RA11 & A011 & _).
    clear XR SV10 Hh10 Hl10. set (R11 := ms_regs ms11) in *.
    destruct (sp_stage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV11 ltac:(lia)) as [SP11 TP11].
    change (reg_get regs 4) with (getr regs 4) in TP11. rewrite HTP in TP11.
    assert (RO11 : YK0s.ret_ok (getr R11 1)) by (rok RA11).
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply (sl_crt_call B (API rc) HS AX ERR CRT f10 L A regs mem md L10 A10 R11 m10 md10
             (sb_malloc (sb_malloc b (sl_un pl + 1)) (sl_tn pl + 1)) (sl_ub pl) us10 pk8 ct10 ua _
             J10 INIT10 FRM10 HAC' H16 H63 TSZ SP11 RO11 TP11 A011 CU10
             ltac:(rewrite BL10, BL8, UBL; exact INU6) ltac:(lia) AW10 ltac:(lia) ltac:(lia) ltac:(lia) RES10
             ltac:(sbl) ltac:(sbl) ltac:(sbl)).
    intros f12 L12 A12 R12 m12 md12 pk12 ct12 FRM12 INIT12 RP12 J12 BL12 BK12 KP12 AW12 PK12 CT12b RES12.
    pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV11 RP12) as SV12.
    pose proof (frame_keep_s m10 m12 _ _ (spZ R11) FR10 ltac:(lia) KP12) as FR12.
    clear FR10 KP12 SV11 RP12 J10 BK12 AW10 CU10 A011 TP11 SP11 RO11.
    destruct (kinv_md _ _ _ _ _ _ _ _ _ _ _ _ J12) as [Hh12 Hl12].
    rewrite RA11.
    eapply evt_SR_canon; [ | exact Hh12 | exact Hl12 | ].
    { rewrite (canon_saved f12 R12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV12). rewrite HS.
      apply (slot_sc.sl_s6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). }
    intros ms13 (can13 & Ecan & EQV). subst can13.
    apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV13 & RA13 & A013 & _).
    clear XR SV12 Hh12 Hl12. set (R13 := ms_regs ms13) in *.
    destruct (sp_stage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV13 ltac:(lia)) as [SP13 TP13].
    change (reg_get regs 4) with (getr regs 4) in TP13. rewrite HTP in TP13.
    assert (RO13 : YK0s.ret_ok (getr R13 1)) by (rok RA13).
    assert (INU12 : In (ua, sl_un pl + 1) (blocks L12 A12)) by (rewrite BL12, BL10, BL8; exact INU6).
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply (sl_free_call B (API rc) HS AX SF SFR ERR SNE MSO FREE f12 L A regs mem md L12 A12 R13 m12 md12 ua
             (sl_un pl + 1) (sb_malloc (sb_malloc b (sl_un pl + 1)) (sl_tn pl + 1)) _ J12 INIT12 HAC' H16 H63 SP13 RO13
             TP13 A013 INU12 NINU ltac:(lia) RES12).
    intros L14 A14 R14 m14 md14 RP14 J14 INIT14 RES14 BL14 BK14 KP14.
    pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV13 RP14) as SV14.
    pose proof (frame_keep_s m12 m14 _ _ (spZ R13) FR12 ltac:(lia) (fun a Ha => KP14 a (or_introl Ha))) as FR14.
    pose proof (sl_aw_keep B m12 m14 0 pk12 ct12 (2 ^ 64 - 1) HS (fun a Ha => proj1 (KP14 a (or_intror Ha))) AW12) as AW14.
    assert (INT14 : In (ta, sl_tn pl + 1) (blocks L14 A14)).
    { rewrite BL14, BL12, BL10, BL8. apply rmb_in; [exact INT | intros E; apply NEut; symmetry; exact E]. }
    clear FR12 KP14 SV13 RP14 J12 BK14 AW12 A013 TP13 SP13 RO13 INU12.
    destruct (kinv_md _ _ _ _ _ _ _ _ _ _ _ _ J14) as [Hh14 Hl14].
    rewrite RA13.
    eapply evt_SR_canon; [ | exact Hh14 | exact Hl14 | ].
    { rewrite (canon_saved f12 R14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV14). rewrite HS.
      apply (slot_sc.sl_s7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). }
    intros ms15 (can15 & Ecan & EQV). subst can15.
    apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV15 & RA15 & A015 & _).
    clear XR SV14 Hh14 Hl14. set (R15 := ms_regs ms15) in *.
    destruct (sp_stage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV15 ltac:(lia)) as [SP15 TP15].
    change (reg_get regs 4) with (getr regs 4) in TP15. rewrite HTP in TP15.
    assert (RO15 : YK0s.ret_ok (getr R15 1)) by (rok RA15).
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply (sl_free_call B (API rc) HS AX SF SFR ERR SNE MSO FREE f12 L A regs mem md L14 A14 R15 m14 md14 ta
             (sl_tn pl + 1) (sb_free (sb_malloc (sb_malloc b (sl_un pl + 1)) (sl_tn pl + 1)) (sl_un pl + 1)) _
             J14 INIT14 HAC' H16 H63 SP15 RO15 TP15 A015 INT14 NINT0 ltac:(lia) RES14).
    intros L16 A16 R16 m16 md16 RP16 J16 INIT16 RES16 BL16 BK16 KP16.
    pose proof (saved_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV15 RP16) as SV16.
    pose proof (frame_keep_s m14 m16 _ _ (spZ R15) FR14 ltac:(lia) (fun a Ha => KP16 a (or_introl Ha))) as FR16.
    pose proof (sl_aw_keep B m14 m16 0 pk12 ct12 (2 ^ 64 - 1) HS (fun a Ha => proj1 (KP16 a (or_intror Ha))) AW14) as AW16.
    clear FR14 KP16 SV15 RP16 J14 BK16 AW14 A015 TP15 SP15 RO15 INT14.
    destruct (kinv_md _ _ _ _ _ _ _ _ _ _ _ _ J16) as [Hh16 Hl16].
    rewrite RA15.
    eapply evt_SR_canon; [ | exact Hh16 | exact Hl16 | ].
    { rewrite (canon_saved f12 R16 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SV16). rewrite HS.
      eapply (slot_sa.sl_s8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      rewrite USP. exact FR16. }
    intros ms17 (can17 & Ecan & EQV). subst can17.
    apply eqv_shape in EQV as [Ems XR]. rewrite Ems. clear Ems.
    destruct (saved_of_eqv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as (SV17 & RA17 & A017 & _).
    clear XR SV16 Hh16 Hl16. set (R17 := ms_regs ms17) in *.
    assert (ESP : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (spZ regs + -64)) + 64) = getr regs 2).
    { rewrite USP. replace (spZ regs - 64 + 64) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
    rewrite ESP in SV17.
    change (reg_get regs 1) with (getr regs 1).
    rewrite (KindB.ret_pc_ok _ ROra). rewrite HRA.
    try replace (PropExec.seg_rom rsegs) with (seg_rom (ms_segs B)) by (rewrite HS; reflexivity).
    apply SR_ret. cbv beta. exists f12, L16, A16, R17, m16, md16.
    split; [reflexivity|]. split; [exact FRM12|]. split.
    + apply (sl_post B API ra empty FF L A regs mem md p n b L16 A16 R17 m16 md16 J16 INIT16 HAC' A017).
      * apply preserved_of_saved_s. exact SV17.
      * exact HFS.
      * exact SNK.
      * rewrite sl_free2 in RES16. exact RES16.
      * exact HPp.
    + apply (sl_GI B m16 j pk12 ct12 ct0 AW16 PK12); [lia | lia | exact Hj].
Qed.

End M.

Theorem slot_fill_of : memchr_contract -> memcpy_contract -> fuzz_alloc_live_contract ->
  fuzz_alloc_peak_reset_contract -> fuzz_alloc_peak_contract -> check_bounded_alloc_contract ->
  check_as_written_contract -> check_reject_clean_contract -> kindb_callees -> slot_fill.
Proof.
  intros MEMCHR MEMCPY LIVE RESET PEAK CBA CAW CRC KBC B API LS SH SK ra empty FF rc fx j Hj.
  eapply slot_body; eassumption.
Qed.
