From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YL01 YO0x YO0u.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import tx_put_c TxRet TxGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import TxCalls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Abbreviation alloc_ceiling := YM05.alloc_ceiling.

Lemma ub_region : forall s p n, WF s -> In (p, n) (user_blocks s) -> (prid p < length (st_regions s))%nat.
Proof.
  intros s p n HW Hin.
  destruct (YO0x.user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & _ & _ & _ & _ & ->).
  pose proof (YO0u.used_group_prid_lt [] None U0 s g am HW Hu) as H.
  assert (E : forall q d, prid (padd q d) = prid q) by (intros [r o] d; reflexivity).
  unfold frame_ptr, slot_start. rewrite !E. exact H.
Qed.

Lemma ptr_stable : forall A L L' p k, WF A -> layout_le A L L' -> In (p, k) (user_blocks A) ->
  ptr_addr L' p = ptr_addr L p.
Proof.
  intros A L L' p k HW (_ & _ & _ & HR) Hin. pose proof (ub_region A p k HW Hin) as Hr.
  unfold ptr_addr, loc_addr. destruct p as [r o]. cbn in Hr |- *. rewrite (HR r Hr). reflexivity.
Qed.

Lemma spZ_range : forall regs, 0 <= spZ regs < 2 ^ 64.
Proof. intros regs. unfold spZ. exact (bv_unsigned_in_range 64 (YK11.getr regs 2)). Qed.

Lemma not_outside1 : forall lo hi a, ~ outside [(lo, hi)] a -> lo <= a < hi.
Proof.
  intros lo hi a H. cbn [outside] in H.
  destruct (Z_le_gt_dec lo a) as [H1|H1]; [destruct (Z_lt_ge_dec a hi) as [H2|H2]; [lia|] |];
    exfalso; apply H; split; try exact I; lia.
Qed.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRB : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
#[local] Set Default Proof Using "All".

Lemma owned_low : forall L A mem md a, aa_MR API L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling.
Proof. intros L A mem md a M O. exact (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M O). Qed.

Lemma not_owned_mid : forall L1 A1 m1 md1 L2 A2 m2 md2 a,
  aa_MR API L1 A1 m1 md1 -> aa_MR API L2 A2 m2 md2 ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L2 A2 a -> ~ owned B L1 A1 a.
Proof.
  intros L1 A1 m1 md1 L2 A2 m2 md2 a M1 M2 Ha N2 O.
  destruct Ha as [Ha|Ha].
  - pose proof (owned_low _ _ _ _ _ M1 O). lia.
  - destruct O as [O|O].
    + apply N2. apply (CTX L2 A2 m2 md2 a M2). exact (YL01.ax_img AX L1 A1 m1 md1 a M1 Ha O).
    + apply N2. right. exact O.
Qed.

Lemma inv_low : forall L A mem md b len cap txt x, aa_MR API L A mem md -> tx_inv B L A mem b len cap txt ->
  b <= x < b + cap -> 4096 <= x < alloc_ceiling /\ ~ in_img B x.
Proof.
  intros L A mem md b len cap txt x M (_ & [(C & _ & _) | (Cp & Hin & _ & _ & NI)]) Hx; [lia|].
  destruct (in_blocks _ _ _ _ Hin) as (p & Hp & Ep).
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ _ _ M Hp) as [H1 H2]. rewrite Ep in H1, H2.
  split; [lia|]. replace x with (b + (x - b)) by lia. apply NI. lia.
Qed.

Lemma inv_range : forall L A mem md b len cap txt, aa_MR API L A mem md -> tx_inv B L A mem b len cap txt ->
  0 <= b < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ 0 <= cap < 2 ^ 64 /\ b + cap <= alloc_ceiling.
Proof.
  intros L A mem md b len cap txt M (TL & [(C & B0 & L0) | (Cp & Hin & LC & _ & _)]).
  - subst. pose proof YM05.alloc_ceiling_value. lia.
  - destruct (in_blocks _ _ _ _ Hin) as (p & Hp & Ep).
    destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ _ _ M Hp) as [H1 H2]. rewrite Ep in H1, H2.
    pose proof YM05.alloc_ceiling_value. lia.
Qed.

Lemma scratch_or : forall stk regs a, scratch_k B stk regs a \/ ~ scratch_k B stk regs a.
Proof. intros stk regs a. unfold scratch_k. lia. Qed.

Variable F : ResForm.

Lemma tx_relx_widen : forall stk regs stk1 regs1 t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j,
  aa_MR API L A mem md -> tx_inv B L A mem b0 len0 cap0 txt ->
  alloc_ceiling + stk <= spZ regs -> spZ regs <= t ->
  (forall a, scratch_k B stk regs a -> writable_at (ms_segs B) mem a) ->
  (forall a, scratch_k B stk1 regs1 a -> scratch_k B stk regs a) ->
  tx_relx B API F stk1 regs1 t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j ->
  tx_relx B API F stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j.
Proof.
  intros stk regs stk1 regs1 t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j M0 INV0 SPK SPT WIN SUB R.
  destruct R as ((M1 & W1 & BD1 & LL1 & PT1 & VM1 & FR1 & UB1 & SC1) & REST).
  pose proof REST as (_ & _ & _ & _ & _ & _ & INV1 & _).
  pose proof (spZ_range regs) as SPR.
  split; [|exact REST].
  split; [exact M1|]. split; [exact W1|]. split; [exact BD1|]. split; [exact LL1|]. split; [exact PT1|].
  split; [exact VM1|].
  split.
  { intros a Ha O0 O1 S E. apply FR1; [exact Ha | exact O0 | exact O1 | intros X; exact (S (SUB a X)) | exact E]. }
  split; [exact UB1|].
  intros a S. destruct (scratch_or stk1 regs1 a) as [S1|S1]; [exact (SC1 a S1)|].
  assert (Ha : spZ regs - stk <= a < spZ regs) by (unfold scratch_k in S, S1; lia).
  edestruct (FR1 a) as [_ WQ];
    [ left; lia
    | intros O; pose proof (owned_low _ _ _ _ _ M0 O); lia
    | intros O; pose proof (owned_low _ _ _ _ _ M1 O); lia
    | exact S1
    | unfold tx_writes; intros [X|[X|X]];
      [ lia
      | pose proof (inv_low _ _ _ _ _ _ _ _ a M0 INV0 X); lia
      | pose proof (inv_low _ _ _ _ _ _ _ _ a M1 INV1 X); lia ]
    | ].
  apply WQ. apply WIN. exact S.
Qed.

Lemma tx_relx_comp : forall stk regs t b0 len0 cap0 txt add1 add2 bnd L A mem md
    L1 A1 mem1 md1 b1 cap1 j1 L2 A2 mem2 md2 b2 cap2 j2,
  aa_MR API L A mem md -> tx_inv B L A mem b0 len0 cap0 txt ->
  tx_relx B API F stk regs t b0 len0 cap0 txt add1 bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  tx_relx B API F stk regs t b1 (len0 + Z.of_nat (length add1)) cap1 (txt ++ add1) add2 (tx_fold F bnd len0 cap0 j1)
    L1 A1 mem1 md1 L2 A2 mem2 md2 b2 cap2 j2 ->
  tx_relx B API F stk regs t b0 len0 cap0 txt (add1 ++ add2) bnd L A mem md L2 A2 mem2 md2 b2 cap2 (j1 ++ j2).
Proof.
  intros stk regs t b0 len0 cap0 txt add1 add2 bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 L2 A2 mem2 md2 b2 cap2 j2
    M0 INV0 R1 R2.
  pose proof (aa_laws API) as LAWS. pose proof (mr_wf _ _ LAWS _ _ _ _ M0) as W0.
  destruct R1 as ((M1 & W1 & BD1 & LL1 & PT1 & (vm1 & MD1) & FR1 & UB1 & SC1) & LEN1 & BK1 & PS1 & FS1 & TR1 & TW1 &
                  INV1 & RA1 & GK1 & IN1 & ZS1 & CF1 & RES1).
  destruct R2 as ((M2 & W2 & BD2 & LL2 & PT2 & (vm2 & MD2) & FR2 & UB2 & SC2) & LEN2 & BK2 & PS2 & FS2 & TR2 & TW2 &
                  INV2 & RA2 & GK2 & IN2 & ZS2 & CF2 & RES2).
  assert (KEEP : forall a k i, In (a, k) (blocks L A) -> a <> b0 -> 0 <= i < k ->
            mbyte (ms_segs B) mem2 (a + i) = mbyte (ms_segs B) mem (a + i)).
  { intros a k i Hin Hne Hi.
    assert (P1 : (a, k) <> (b0, cap0)) by (intros X; apply Hne; congruence).
    destruct (PS1 a k Hin P1) as [Hin1 _].
    pose proof (FS1 a k Hin ltac:(lia) Hne) as Hne1.
    rewrite (BK2 a k i Hin1 Hne1 Hi). exact (BK1 a k i Hin Hne Hi). }
  assert (LL : layout_le A L L2) by (eapply layout_le_trans; [exact LL1 | exact LL2 | exact LEN1]).
  split.
  { split; [exact M2|]. split; [exact W2|]. split; [exact BD2|]. split; [exact LL|].
    split; [intros p k Hin _; exact (ptr_stable A L L2 p k W0 LL Hin)|].
    split; [exists vm2; rewrite MD2, MD1; apply with_vmmaps_twice|].
    split.
    { intros a Ha O0 O2 S E.
      assert (O1 : ~ owned B L1 A1 a) by exact (not_owned_mid _ _ _ _ _ _ _ _ a M1 M2 Ha O2).
      assert (NB1 : ~ (b1 <= a < b1 + cap1)).
      { intros X. destruct (inv_low _ _ _ _ _ _ _ _ a M1 INV1 X) as [X1 X2].
        destruct Ha as [Ha|Ha]; [lia | exact (X2 Ha)]. }
      edestruct (FR1 a Ha O0 O1 S) as [E1 V1]; [unfold tx_writes in *; tauto|].
      edestruct (FR2 a Ha O1 O2 S) as [E2 V2]; [unfold tx_writes in *; tauto|].
      split; [rewrite E2; exact E1 | tauto]. }
    split.
    { intros p k i Hin0 Hin2 Hi E.
      pose proof (user_in_blocks L A p k Hin0) as HB.
      destruct (Z.eq_dec (ptr_addr L p) b0) as [Eq|Ne]; [|exact (KEEP _ k i HB Ne Hi)].
      exfalso. apply E. unfold tx_writes. right. left.
      destruct INV0 as (_ & [(C0 & B0 & _) | (Cp & Hin & _)]).
      - destruct (mr_blocks_range _ _ LAWS _ _ _ _ _ _ M0 Hin0). lia.
      - destruct (Z.eq_dec k cap0) as [Ek|Nk]; [lia|]. exfalso. rewrite Eq in HB.
        destruct (pairwise_in _ _ _ _ (mr_blocks_disjoint _ _ LAWS _ _ _ _ M0) HB Hin
                    ltac:(intros X; apply Nk; congruence))
          as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    exact SC2. }
  split; [lia|].
  split; [intros a k i Hin Hne Hi; exact (KEEP a k i Hin Hne Hi)|].
  split.
  { intros a k Hin Hne. destruct (PS1 a k Hin Hne) as [Hin1 Hne1]. exact (PS2 a k Hin1 Hne1). }
  split.
  { intros a k Hin Hk Hne.
    assert (P1 : (a, k) <> (b0, cap0)) by (intros X; apply Hne; congruence).
    destruct (PS1 a k Hin P1) as [Hin1 _].
    exact (FS2 a k Hin1 Hk (FS1 a k Hin Hk Hne)). }
  assert (LN : len0 + Z.of_nat (length (add1 ++ add2)) = len0 + Z.of_nat (length add1) + Z.of_nat (length add2))
    by (rewrite length_app; lia).
  rewrite LN, app_assoc.
  split; [exact TR2|]. split; [exact TW2|]. split; [exact INV2|]. split; [exact RA2|].
  split; [intros i Hi; rewrite (GK2 i Hi); exact (GK1 i Hi)|].
  split; [exact IN2|]. split; [rewrite zsum_app, length_app; lia|].
  split; [rewrite tx_capf_app, ZS1, <- CF1; exact CF2|].
  rewrite tx_fold_app, ZS1, <- CF1. exact RES2.
Qed.

Lemma tx_rel_trans : forall stk regs stk1 regs1 stk2 regs2 t b0 len0 cap0 txt add1 add2 ks2 bnd L A mem md
    L1 A1 mem1 md1 b1 cap1 j1 L2 A2 mem2 md2,
  aa_MR API L A mem md -> tx_inv B L A mem b0 len0 cap0 txt ->
  alloc_ceiling + stk <= spZ regs -> spZ regs <= t ->
  (forall a, scratch_k B stk regs a -> writable_at (ms_segs B) mem a) ->
  (forall a, scratch_k B stk1 regs1 a -> scratch_k B stk regs a) ->
  (forall a, scratch_k B stk2 regs2 a -> scratch_k B stk regs a) ->
  tx_relx B API F stk1 regs1 t b0 len0 cap0 txt add1 bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  tx_rel B API F stk2 regs2 t b1 (len0 + Z.of_nat (length add1)) cap1 (txt ++ add1) add2 ks2 (tx_fold F bnd len0 cap0 j1)
    L1 A1 mem1 md1 L2 A2 mem2 md2 ->
  tx_rel B API F stk regs t b0 len0 cap0 txt (add1 ++ add2) (j1 ++ ks2) bnd L A mem md L2 A2 mem2 md2.
Proof.
  intros stk regs stk1 regs1 stk2 regs2 t b0 len0 cap0 txt add1 add2 ks2 bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1
    L2 A2 mem2 md2 M0 INV0 SPK SPT WIN SUB1 SUB2 R1 (b2 & cap2 & R2).
  assert (R1' : tx_relx B API F stk regs t b0 len0 cap0 txt add1 bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1)
    by (eapply (tx_relx_widen stk regs stk1 regs1); eassumption).
  pose proof R1' as ((M1 & _ & _ & _ & _ & _ & _ & _ & SC1) & _ & _ & _ & _ & _ & _ & INV1 & _).
  exists b2, cap2.
  eapply tx_relx_comp; [exact M0 | exact INV0 | exact R1' |].
  eapply (tx_relx_widen stk regs stk2 regs2); [exact M1 | exact INV1 | exact SPK | exact SPT | exact SC1 | exact SUB2 | exact R2].
Qed.

Lemma tx_relx_above : forall a stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j,
  aa_MR API L A mem md -> tx_inv B L A mem b0 len0 cap0 txt ->
  tx_relx B API F stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ scratch_k B stk regs a -> ~ (t <= a < t + 24) ->
  mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
  (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros a stk regs t b0 len0 cap0 txt add bnd L A mem md L' A' mem' md' b1 cap1 j M0 INV0 R Ha S T.
  destruct R as ((M1 & _ & _ & _ & _ & _ & FR & _ & _) & _ & _ & _ & _ & _ & _ & INV1 & _).
  apply FR;
    [ left; exact Ha
    | intros O; pose proof (owned_low _ _ _ _ _ M0 O); lia
    | intros O; pose proof (owned_low _ _ _ _ _ M1 O); lia
    | exact S | ].
  unfold tx_writes. intros [X|[X|X]];
    [ exact (T X)
    | pose proof (inv_low _ _ _ _ _ _ _ _ a M0 INV0 X); lia
    | pose proof (inv_low _ _ _ _ _ _ _ _ a M1 INV1 X); lia ].
Qed.

Lemma tx_call : forall stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1
    stk1 regs1 pc1 add ks2 (Q : layout -> astate -> (word -> option byte) -> Prop) (P : config -> Prop),
  aa_MR API L A mem md -> tx_inv B L A mem b0 len0 cap0 txt ->
  alloc_ceiling + stk <= spZ regs -> spZ regs <= t ->
  (forall a, scratch_k B stk regs a -> writable_at (ms_segs B) mem a) ->
  tx_relx B API F stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  alloc_ceiling <= spZ regs1 -> (forall a, scratch_k B stk1 regs1 a -> scratch_k B stk regs a) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs1 pc1 mem1 (YK11.seg_rom (ms_segs B))) md1)
    (tx_ret B API F stk1 L1 A1 regs1 mem1 md1 t b1 (len0 + Z.of_nat (length acc)) cap1 (txt ++ acc) add ks2 (tx_fold F bnd len0 cap0 j1) Q) ->
  (forall L2 A2 regs2 mem2 md2, regs_preserved regs1 regs2 ->
     tx_rel B API F stk regs t b0 len0 cap0 txt (acc ++ add) (j1 ++ ks2) bnd L A mem md L2 A2 mem2 md2 -> Q L2 A2 mem2 ->
     (forall a, spZ regs1 <= a < 2 ^ 64 -> ~ (t <= a < t + 24) ->
        mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\
        (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)) ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs2 (YK11.getr regs1 1) mem2 (YK11.seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs1 pc1 mem1 (YK11.seg_rom (ms_segs B))) md1) P.
Proof.
  intros stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 stk1 regs1 pc1 add ks2 Q P
    M0 INV0 SPK SPT WIN R1 SP1 SUB HS K.
  eapply SR_bind; [exact HS|].
  intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & RP & (b2 & cap2 & R2) & HQ).
  pose proof R1 as ((M1 & _ & _ & _ & _ & _ & _ & _ & _) & _ & _ & _ & _ & _ & _ & INV1 & _).
  apply (K L2 A2 regs2 mem2 md2 RP); [| exact HQ |].
  - eapply (tx_rel_trans stk regs stk regs stk1 regs1);
      [exact M0 | exact INV0 | exact SPK | exact SPT | exact WIN | intros a X; exact X | exact SUB | exact R1 |].
    exists b2, cap2. exact R2.
  - intros a Ha T. pose proof (spZ_range regs1).
    edestruct (tx_relx_above a) as [E W];
      [exact M1 | exact INV1 | exact R2 | lia | unfold scratch_k; lia | exact T |].
    split; [exact E | tauto].
Qed.

Lemma tx_put_ret : tx_put_contract B API F ->
  forall L A regs mem md (t s n b0 len0 cap0 : Z) (txt src : list byte) (bnd : rf_R F),
    call_pre_k B (aa_MR API) TX_STACK L A regs mem md -> st_init_done A = true -> ro_agree (ms_segs B) mem ->
    YK11.getr regs 10 = Z_to_bv 64 t -> YK11.getr regs 11 = Z_to_bv 64 s -> YK11.getr regs 12 = Z_to_bv 64 n ->
    spZ regs <= t -> t + 24 <= 2 ^ 64 -> t mod 8 = 0 ->
    (forall i, 0 <= i < 24 -> writable_at (ms_segs B) mem (t + i)) ->
    0 <= b0 < 2 ^ 64 -> 0 <= len0 < 2 ^ 64 -> 0 <= cap0 < 2 ^ 64 ->
    text_rec B mem t b0 len0 cap0 ->
    tx_inv B L A mem b0 len0 cap0 txt ->
    0 <= s < 2 ^ 64 -> 0 <= n -> s + n <= 2 ^ 64 ->
    mbytes B mem s src -> Z.of_nat (length src) = n ->
    (forall i, 0 <= i < n ->
       ~ (t <= s + i < t + 24) /\ ~ (spZ regs - TX_STACK <= s + i < spZ regs) /\ ~ (b0 <= s + i < b0 + cap0) /\
       (len0 + n + 1 <= cap0 \/ spZ regs <= s + i \/ Mem.ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true \/
        exists a k, In (a, k) (blocks L A) /\ a <> b0 /\ a <= s + i < a + k)) ->
    len0 + n + 1 <= 2 ^ 28 ->
    rf_ok F A bnd -> (cap0 < len0 + n + 1 -> rf_room F bnd (2 * (len0 + n + 1))) ->
    SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 TX_PUT) mem (YK11.seg_rom (ms_segs B))) md)
      (tx_ret B API F TX_STACK L A regs mem md t b0 len0 cap0 txt src [n] bnd (fun _ _ _ => True)).
Proof.
  intros TXP L A regs mem md t s n b0 len0 cap0 txt src bnd PRE INIT RA R10 R11 R12 Tlo Thi Tal TW Rb Rl Rc REC INV
    Sr Sn Shi SRC SL SP NEED RES ROOM.
  eapply SR_mono;
    [exact (TXP L A regs mem md t s n b0 len0 cap0 txt src bnd PRE INIT RA R10 R11 R12 Tlo Thi Tal TW Rb Rl Rc REC INV
              Sr Sn Shi SRC SL SP NEED RES ROOM)|].
  intros c' (L' & A' & regs' & mem' & md' & b1 & cap1 & bnd' & -> & FR & RP & BK & TR & TW' & INV' & _ & RA' & GK & IN &
             LEN & RES' & ARMS).
  exists L', A', regs', mem', md'. split; [reflexivity|]. split; [exact RP|]. split; [|exact I].
  destruct ARMS as [(FIT & -> & -> & -> & -> & -> & ->) | (GROW & EC & AL & EB & bl1 & bl2 & bm1 & bm2 & E1 & E2 & E3)].
  - exists b0, cap0. unfold tx_relx. rewrite SL.
    split; [exact FR|]. split; [exact LEN|]. split; [exact BK|].
    split; [intros a k Hin Hne; split; assumption|].
    split; [intros a k Hin Hk Hne; exact Hne|].
    split; [exact TR|]. split; [exact TW'|]. split; [exact INV'|]. split; [exact RA'|]. split; [exact GK|].
    split; [exact IN|]. split; [cbn [zsum]; lia|].
    split; [cbn [tx_capf]; unfold tx_cap1; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity|].
    cbn [tx_fold]. unfold tx_next. rewrite (proj2 (Z.leb_le _ _)) by lia. exact RES'.
  - exists b1, cap1. unfold tx_relx. rewrite SL.
    split; [exact FR|]. split; [exact LEN|]. split; [exact BK|].
    destruct FR as (M' & _).
    pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M') as PW. rewrite E1 in PW.
    assert (PC : 0 < cap1) by lia.
    assert (OLD : forall a k, In (a, k) (blocks L A) -> (a, k) <> (b0, cap0) -> In (a, k) (bm1 ++ bm2)).
    { intros a k Hin Hne. rewrite E2. destruct E3 as [(C0 & E3)|(C0 & E3)]; rewrite E3 in Hin; [exact Hin|].
      apply in_app_or in Hin. apply in_or_app. destruct Hin as [H|[H|H]]; [left; exact H | | right; exact H].
      exfalso. apply Hne. symmetry. exact H. }
    split.
    { intros a k Hin Hne. pose proof (OLD a k Hin Hne) as Hin'.
      split.
      - rewrite E1. apply in_app_or in Hin'. apply in_or_app.
        destruct Hin' as [H|H]; [left; exact H | right; right; exact H].
      - intros X. injection X as Xa Xk. subst a k.
        destruct (pairwise_mid _ _ _ _ _ PW Hin') as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    split.
    { intros a k Hin Hk Hne X. subst a.
      assert (Hin' : In (b1, k) (bm1 ++ bm2)).
      { apply OLD; [exact Hin|]. intros X. apply Hne. congruence. }
      destruct (pairwise_mid _ _ _ _ _ PW Hin') as [D|D]; unfold ranges_disjoint in D; cbn [fst snd] in D; lia. }
    split; [exact TR|]. split; [exact TW'|]. split; [exact INV'|]. split; [exact RA'|]. split; [exact GK|].
    split; [exact IN|]. split; [cbn [zsum]; lia|].
    split; [cbn [tx_capf]; unfold tx_cap1; rewrite (proj2 (Z.leb_gt _ _)) by lia; lia|].
    subst bnd'. cbn [tx_fold]. unfold tx_next. rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite <- EC. exact RES'.
Qed.

Lemma tx_rel_frame : forall stk regs t b0 len0 cap0 txt bnd L A mem md mem' lo hi,
  aa_MR API L A mem md -> WF A -> bounded A -> st_init_done A = true ->
  munch [(lo, hi)] mem mem' -> wmono rsegs mem mem' -> ro_agree (ms_segs B) mem' ->
  (forall a, lo <= a < hi -> alloc_ceiling <= a /\ spZ regs - stk <= a < spZ regs) ->
  spZ regs <= t -> t + 24 <= 2 ^ 64 ->
  text_rec B mem t b0 len0 cap0 -> (forall i, 0 <= i < 24 -> writable_at (ms_segs B) mem (t + i)) ->
  tx_inv B L A mem b0 len0 cap0 txt -> rf_ok F A bnd ->
  (forall a, scratch_k B stk regs a -> writable_at (ms_segs B) mem a) ->
  tx_relx B API F stk regs t b0 len0 cap0 txt [] bnd L A mem md L A mem' md b0 cap0 [].
Proof.
  intros stk regs t b0 len0 cap0 txt bnd L A mem md mem' lo hi M0 W0 BD0 IN MU WM RA' LOHI SPT Thi TR TW INV RES WIN.
  pose proof (spZ_range regs) as SPR. pose proof YM05.alloc_ceiling_value as ACL.
  assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
            mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
            (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hn. apply (munch_byte B _ _ _ _ MU Ha). cbn [outside]. split; [exact Hn | exact I]. }
  assert (LOW : forall a, 0 <= a < alloc_ceiling ->
            mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
            (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha. apply OUT; [lia|]. intros X. destruct (LOHI a X). lia. }
  assert (MR' : aa_MR API L A mem' md).
  { apply (mr_store B API SEGS L A mem mem' md _ M0 MU WM).
    - intros a Ho. apply not_outside1 in Ho. destruct (LOHI a Ho). split; [lia | left; lia].
    - intros a Ho. pose proof (owned_low _ _ _ _ _ M0 Ho). cbn [outside]. split; [|exact I].
      intros X. destruct (LOHI a X). lia. }
  assert (BLK : forall a k i, In (a, k) (blocks L A) -> 0 <= i < k ->
            mbyte (ms_segs B) mem' (a + i) = mbyte (ms_segs B) mem (a + i)).
  { intros a k i Hin Hi. destruct (in_blocks _ _ _ _ Hin) as (p & Hp & <-).
    destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ _ _ M0 Hp). apply LOW. lia. }
  unfold tx_relx. cbn [length Z.of_nat]. rewrite !Z.add_0_r, app_nil_r.
  split.
  { split; [exact MR'|]. split; [exact W0|]. split; [exact BD0|]. split; [apply layout_le_refl|].
    split; [intros; reflexivity|]. split; [exists (m_vmmaps md); apply vm_id|].
    split.
    { intros a Ha _ _ S _.
      assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | apply (in_img_range B SEGS) in Ha; lia]).
      apply OUT; [exact Hr|]. intros X. apply S. unfold scratch_k. left. destruct (LOHI a X). lia. }
    split.
    { intros p k i Hin _ Hi _. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ _ _ M0 Hin). apply LOW. lia. }
    intros a S. apply (wmono_writable B SEGS mem mem' a WM). exact (WIN a S). }
  split; [lia|].
  split; [intros a k i Hin _ Hi; exact (BLK a k i Hin Hi)|].
  split; [intros a k Hin Hne; split; [exact Hin | exact Hne]|].
  split; [intros a k Hin _ Hne; exact Hne|].
  assert (TL24 : forall b l c, Z.of_nat (length (Mem.le8 (Z_to_bv 64 b) ++ Mem.le8 (Z_to_bv 64 l) ++ Mem.le8 (Z_to_bv 64 c))) = 24)
    by (intros; rewrite !length_app, !Mem.length_le8; reflexivity).
  split.
  { destruct TR as (TR & T28 & TF). split; [|split; [exact T28|]].
    - apply (mbytes_same B mem); [exact TR|]. intros i Hi. rewrite TL24 in Hi.
      apply OUT; [lia|]. intros X. destruct (LOHI _ X). lia.
    - apply (mbytes_same B mem); [exact TF|]. intros i Hi. rewrite Mem.length_le4 in Hi. cbn in Hi.
      apply OUT; [lia|]. intros X. destruct (LOHI _ X). lia. }
  split.
  { intros i Hi. apply (proj1 (proj2 (OUT (t + i) ltac:(lia) ltac:(intros X; destruct (LOHI _ X); lia)))).
    exact (TW i Hi). }
  split.
  { destruct INV as (TL & [C|(Cp & Hin & LC & TX & NI)]); split; [exact TL | left; exact C | exact TL |].
    right. split; [exact Cp|]. split; [exact Hin|]. split; [exact LC|]. split; [|exact NI].
    apply (mbytes_same B mem); [exact TX|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (BLK b0 cap0 i Hin). lia. }
  split; [exact RA'|].
  split.
  { intros i Hi. assert (HO : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
    pose proof (owned_low _ _ _ _ _ M0 HO). apply LOW. lia. }
  split; [exact IN|]. split; [reflexivity|]. split; [reflexivity|]. exact RES.
Qed.

Lemma tx_start_facts : forall stk L A regs mem md t b0 len0 cap0 txt bnd ns need,
  tx_start B API F stk L A regs mem md t b0 len0 cap0 txt bnd ns need ->
  aa_MR API L A mem md /\ WF A /\ bounded A /\ alloc_ceiling + stk <= spZ regs /\ spZ regs <= t /\
  (forall a, scratch_k B stk regs a -> writable_at (ms_segs B) mem a) /\ tx_inv B L A mem b0 len0 cap0 txt.
Proof.
  intros stk L A regs mem md t b0 len0 cap0 txt bnd ns need
    ((M & W & BD & _ & _ & SPK & _ & WIN & _ & ERRW & _) & _ & _ & _ & SPT & _ & _ & _ & _ & _ & _ & _ & INV & _).
  split; [exact M|]. split; [exact W|]. split; [exact BD|]. split; [exact SPK|]. split; [exact SPT|].
  split; [|exact INV]. intros a [S|S]; [apply WIN | apply ERRW]; exact S.
Qed.

Lemma tx_rel_start : forall stk L A regs mem md t b0 len0 cap0 txt bnd ns need,
  tx_start B API F stk L A regs mem md t b0 len0 cap0 txt bnd ns need ->
  tx_relx B API F stk regs t b0 len0 cap0 txt [] bnd L A mem md L A mem md b0 cap0 [].
Proof.
  intros stk L A regs mem md t b0 len0 cap0 txt bnd ns need ST.
  pose proof (tx_start_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (M & W & BD & SPK & SPT & WIN & INV).
  destruct ST as (_ & IN & RA & _ & _ & Thi & _ & TW & _ & _ & _ & TR & _ & _ & RES & _).
  apply (tx_rel_frame stk regs t b0 len0 cap0 txt bnd L A mem md mem 0 0); try assumption.
  - apply munch_refl.
  - apply wmono_refl.
  - intros a X. lia.
Qed.

Lemma tx_start_next : forall stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1 b1 cap1 j1
    stk2 regs2 ns2 rest need2,
  tx_start B API F stk L A regs mem md t b0 len0 cap0 txt bnd ns need ->
  tx_relx B API F stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  ns = j1 ++ ns2 ++ rest ->
  spZ regs - stk <= spZ regs2 - stk2 -> spZ regs2 <= spZ regs -> spZ regs2 mod 16 = 0 ->
  YK0s.ret_ok (YK11.getr regs2 1) -> YK11.getr regs2 4 = YK11.getr regs 4 -> YK11.getr regs2 10 = Z_to_bv 64 t ->
  0 <= need2 <= need ->
  tx_start B API F stk2 L1 A1 regs2 mem1 md1 t b1 (len0 + Z.of_nat (length acc)) cap1 (txt ++ acc)
    (tx_fold F bnd len0 cap0 j1) ns2 need2.
Proof.
  intros stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1 b1 cap1 j1 stk2 regs2 ns2 rest need2
    ST R ENS S1 S2 AL RET TP R10 HN.
  destruct ST as ((M & W & BD & _ & _ & SPK & SP63 & WIN & TP0 & ERRW & _) & _ & _ & _ & SPT & Thi & Tal & _ & _ & _ & _ & _ &
                  _ & NEED & _ & ROOM).
  destruct R as ((M1 & W1 & BD1 & _ & _ & _ & _ & _ & SC1) & _ & _ & _ & _ & TR1 & TW1 & INV1 & RA1 & _ & IN1 & ZS1 & CF1 & RES1).
  destruct (inv_range _ _ _ _ _ _ _ _ M1 INV1) as (Rb & Rl & Rc & _).
  split.
  { split; [exact M1|]. split; [exact W1|]. split; [exact BD1|]. split; [exact RET|]. split; [exact AL|].
    split; [lia|]. split; [lia|].
    split; [intros a Ha; apply SC1; unfold scratch_k; left; lia|].
    split; [rewrite TP; exact TP0|].
    split; [intros a Ha; apply SC1; unfold scratch_k; right; exact Ha|].
    intros H. congruence. }
  split; [exact IN1|]. split; [exact RA1|]. split; [exact R10|]. split; [lia|]. split; [exact Thi|]. split; [exact Tal|].
  split; [exact TW1|]. split; [exact Rb|]. split; [exact Rl|]. split; [exact Rc|]. split; [exact TR1|].
  split; [exact INV1|]. split; [lia|]. split; [exact RES1|].
  subst ns. rewrite <- ZS1, CF1. exact (tx_rooms_mid F j1 ns2 rest bnd len0 cap0 ROOM).
Qed.

Lemma tx_put_call : tx_put_contract B API F ->
  forall stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1 b1 cap1 j1 regs1 s n src rest
    (P : config -> Prop),
  tx_start B API F stk L A regs mem md t b0 len0 cap0 txt bnd ns need ->
  tx_relx B API F stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 ->
  ns = j1 ++ [n] ++ rest ->
  spZ regs - stk <= spZ regs1 - TX_STACK -> spZ regs1 <= spZ regs -> spZ regs1 mod 16 = 0 ->
  YK0s.ret_ok (YK11.getr regs1 1) -> YK11.getr regs1 4 = YK11.getr regs 4 -> YK11.getr regs1 10 = Z_to_bv 64 t ->
  YK11.getr regs1 11 = Z_to_bv 64 s -> YK11.getr regs1 12 = Z_to_bv 64 n ->
  0 <= s < 2 ^ 64 -> 0 <= n -> s + n <= 2 ^ 64 -> mbytes B mem1 s src -> Z.of_nat (length src) = n ->
  (forall i, 0 <= i < n ->
     ~ (t <= s + i < t + 24) /\ ~ (spZ regs1 - TX_STACK <= s + i < spZ regs1) /\ ~ (b1 <= s + i < b1 + cap1) /\
     (len0 + Z.of_nat (length acc) + n + 1 <= cap1 \/ spZ regs1 <= s + i \/
      Mem.ro_addr (ms_segs B) (Z_to_bv 64 (s + i)) = true \/
      exists a k, In (a, k) (blocks L1 A1) /\ a <> b1 /\ a <= s + i < a + k)) ->
  len0 + Z.of_nat (length acc) + n + 1 <= need ->
  (forall L2 A2 regs2 mem2 md2, regs_preserved regs1 regs2 ->
     tx_rel B API F stk regs t b0 len0 cap0 txt (acc ++ src) (j1 ++ [n]) bnd L A mem md L2 A2 mem2 md2 ->
     (forall a, spZ regs1 <= a < 2 ^ 64 -> ~ (t <= a < t + 24) ->
        mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem1 a /\
        (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem2 a)) ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs2 (YK11.getr regs1 1) mem2 (YK11.seg_rom (ms_segs B))) md2) P) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs1 (Z_to_bv 64 TX_PUT) mem1 (YK11.seg_rom (ms_segs B))) md1) P.
Proof.
  intros TXP stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1 b1 cap1 j1 regs1 s n src rest P
    ST R ENS S1 S2 AL RET TP R10 R11 R12 Sr Sn Shi SRC SL SP HN K.
  pose proof (tx_start_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST) as (M0 & W0 & BD0 & SPK & SPT & WIN & INV0).
  pose proof (proj1 INV0) as TL0.
  assert (TXS : 0 <= TX_STACK) by (unfold TX_STACK, REALLOC_STACK, ALLOC_STACK; lia).
  pose proof (tx_start_next stk L A regs mem md t b0 len0 cap0 txt bnd ns need acc L1 A1 mem1 md1 b1 cap1 j1 TX_STACK regs1
                [n] rest (len0 + Z.of_nat (length acc) + n + 1) ST R ENS S1 S2 AL RET TP R10 ltac:(lia)) as ST1.
  destruct ST1 as (PRE1 & INIT1 & RA1 & _ & Tlo1 & Thi1 & Tal1 & TW1 & Rb1 & Rl1 & Rc1 & REC1 & INV1 & NEED1 & RES1 & ROOM1).
  eapply (tx_call stk regs t b0 len0 cap0 txt acc bnd L A mem md L1 A1 mem1 md1 b1 cap1 j1 TX_STACK regs1 _ src [n]
            (fun _ _ _ => True) P M0 INV0 SPK SPT WIN R).
  - lia.
  - intros a [X|X]; [left; lia | right; exact X].
  - apply (tx_put_ret TXP L1 A1 regs1 mem1 md1 t s n b1 (len0 + Z.of_nat (length acc)) cap1 (txt ++ acc) src
             (tx_fold F bnd len0 cap0 j1)
             PRE1 INIT1 RA1 R10 R11 R12 Tlo1 Thi1 Tal1 TW1 Rb1 Rl1 Rc1 REC1 INV1 Sr Sn Shi SRC SL SP);
      [lia | exact RES1 | exact (proj1 ROOM1)].
  - intros L2 A2 regs2 mem2 md2 RP REL _ KEEP. exact (K L2 A2 regs2 mem2 md2 RP REL KEEP).
Qed.

Lemma tx_ret_end : forall stk L A regs mem md t b0 len0 cap0 txt add ks bnd
    (Q : layout -> astate -> (word -> option byte) -> Prop) L' A' regs' mem' md',
  tx_rel B API F stk regs t b0 len0 cap0 txt add ks bnd L A mem md L' A' mem' md' -> regs_preserved regs regs' ->
  Q L' A' mem' ->
  tx_ret B API F stk L A regs mem md t b0 len0 cap0 txt add ks bnd Q
    (mkCfg (YK11.mkst regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md').
Proof.
  intros stk L A regs mem md t b0 len0 cap0 txt add ks bnd Q L' A' regs' mem' md' R RP HQ.
  exists L', A', regs', mem', md'. split; [reflexivity|]. split; [exact RP|]. split; [exact R | exact HQ].
Qed.

End C.
