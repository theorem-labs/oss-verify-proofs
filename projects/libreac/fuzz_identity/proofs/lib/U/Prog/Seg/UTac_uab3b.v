From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame Image.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU buf_of_c buf_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uabj UTac_uab1.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import ListNotations.
Open Scope Z_scope.

Lemma fb_nodup_eq : forall (l : list (sptr * Z)) p k n, List.NoDup (map fst l) -> In (p, k) l -> In (p, n) l -> k = n.
Proof.
  induction l as [|[q m] l IH]; intros p k n ND H1 H2; [destruct H1|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as [Hq ND].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - injection E1 as E1a E1b. injection E2 as E2a E2b. congruence.
  - injection E1 as E1a E1b. subst. exfalso. apply Hq. apply in_map_iff. exists (p, n). split; [reflexivity | exact H2].
  - injection E2 as E2a E2b. subst. exfalso. apply Hq. apply in_map_iff. exists (p, k). split; [reflexivity | exact H1].
  - exact (IH p k n ND H1 H2).
Qed.

Lemma fb_keep : forall (m m' : word -> option byte) lo a bs,
  (forall x, lo <= x < 2 ^ 64 -> mbyte rsegs m' x = mbyte rsegs m x) -> lo <= a ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo a bs H Ha (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros j Hj.
  specialize (H3 j Hj). specialize (H (a + Z.of_nat j) ltac:(lia)).
  change (mrd rsegs m' (wa (a + Z.of_nat j))) with (mbyte rsegs m' (a + Z.of_nat j)). rewrite H.
  exact H3.
Qed.

Lemma fb_addiw : forall z, 0 <= z < 2 ^ 31 - 1 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 1) = z + 1.
Proof.
  intros z Hz. rewrite MState.unsigned_lit by lia. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma fb_getr : forall {fx : FPState} (R : bvmap 5 word) (r : bv 5), bv_eqb r 0 = false -> getr R r = Sem.reg_get R r.
Proof. intros fx R r H. unfold getr. rewrite H. reflexivity. Qed.

Ltac fb_arith := apply bv_eq; rewrite ?bv_add_unsigned, ?bv_sub_unsigned, ?Z_to_bv_unsigned; unfold bv_wrap;
  rewrite ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r; f_equal; lia.

Lemma fb_B03_keep : forall g i pl regs regs' m m', B03 g i pl regs m ->
  getr regs' 9 = getr regs 9 -> getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 26 = getr regs 26 ->
  (forall a, fsp g + 24 <= a < fsp g + 56 \/ fsp g + 128 <= a < fsp g + 140 \/ pl <= a < pl + rec_k (g_in g) i ->
     mbyte rsegs m' a = mbyte rsegs m a) ->
  B03 g i pl regs' m'.
Proof.
  intros g i pl regs regs' m m' ((HR & H22 & H20 & H26) & H21 & HPL) E9 E20 E21 E22 E26 M.
  split; [split; [|split; [|split]]|split].
  - apply (t_REC_keep g i regs regs' m m' HR E9). intros a Ha. apply M. lia.
  - rewrite E22. exact H22.
  - rewrite E20. exact H20.
  - rewrite E26. exact H26.
  - rewrite E21. exact H21.
  - unfold PLB in *. apply (t_bytes_at_eq _ m); [exact HPL|]. intros j Hj. rewrite rec_pl_length in Hj. apply M. lia.
Qed.

Ltac fb_cs RP HG r := etransitivity; [exact (RP r ltac:(unfold callee_saved; lia))|]; rewrite HG; reflexivity.

Lemma fb_pw_mid : forall (l1 l2 : list (Z * Z)) x y, pairwise ranges_disjoint (l1 ++ x :: l2) -> In y (l1 ++ l2) ->
  ranges_disjoint x y.
Proof.
  induction l1 as [|z l1 IH]; intros l2 x y H Hy; cbn in H, Hy.
  - destruct H as [H _]. exact (H y Hy).
  - destruct H as [H1 H2]. destruct Hy as [<-|Hy].
    + apply sj_rd_sym. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH l2 x y H2 Hy).
Qed.

Lemma ua_not : forall x, 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
  intros x Hx. rewrite (MState.unsigned_lit x) by lia. f_equal. change 18446744073709551615 with (Z.ones 64).
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros k Hk. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases k 64) as [Hk64|Hk64].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x k); reflexivity.
    - rewrite Z.ones_spec_high by lia.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [rewrite Z.bits_0; reflexivity|].
      rewrite (Z.bits_above_log2 x k); [reflexivity | lia |].
      assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia. }
  rewrite E, Z.land_ones by lia. rewrite Z.lnot_eq_pred_opp. unfold Z.pred.
  symmetry. apply (Z.mod_unique _ _ (-1)); [left; lia | lia].
Qed.

Lemma ua_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

Section TacFB.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Local Abbreviation API := (APIf rc).
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR (APIf rc)).

Lemma fb_FR_free : forall g km hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2,
  FR B APIf ra empty g km (hb1 ++ (ptr_addr L p, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (ptr_addr L p, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) -> 0 <= n ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  call_post B MR L A regs_c mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' ->
  blocks L A = b1 ++ (ptr_addr L p, n) :: b2 -> blocks L' A' = b1 ++ b2 ->
  blocks_kept B L A mem mem' (fun a => a = ptr_addr L p) ->
  (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) ->
  ro_agree segs mem' ->
  (st_init_done A = true -> st_init_done A' = true) ->
  res_ok_slots A' (sb_free (sb_hb (g_b g) (hb1 ++ (ptr_addr L p, n) :: hb2)) n) ->
  FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' /\
  Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) /\
  (forall a, fsp g <= a < 2 ^ 64 -> mbyte segs mem' a = mbyte segs mem a) /\
  (forall q k j, In (q, k) (hb1 ++ hb2) -> 0 <= j < k -> mbyte segs mem' (q + j) = mbyte segs mem (q + j)).
Proof.
  intros g km hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn Hn E2 E3 E4
    POST EB EB' KEPT UBK RO' INIT RES'.
  pose proof (sj_segs B APIf ra empty FF) as ES.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn0 & Hp0 & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0).
  destruct POST as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & MEM & UB & SCW).
  pose proof alloc_ceiling_value as HAC. pose proof (sj_errno_ceil B APIf ra empty FF) as HEC. pose proof (sj_errno_val B APIf ra empty FF) as HEV.
  unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 384).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply sj_unsigned. lia. }
  pose proof (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HMR Hpn) as [Hp1 Hp2].
  assert (HEimg : forall a, ptr_addr L p <= a < ptr_addr L p + n -> ~ in_img B a).
  { intros a Ha. replace a with (ptr_addr L p + (a - ptr_addr L p)) by lia.
    apply (ax_blocks_img (sj_ax B APIf ra empty FF) L A mem md p n); [exact HMR | exact Hpn | lia]. }
  assert (HOW : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> owned B L0 A0 a -> a < alloc_ceiling).
  { intros L0 A0 m0 md0 a H Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H Ho). lia. }
  assert (HI : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
      ~ (errno_addr B <= a < errno_addr B + 4) ->
      mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)).
  { intros a Ha H1 H2 H3. pose proof ((sj_img_lt B APIf ra empty FF) a Ha) as Hl. apply MEM.
    - right. exact Ha.
    - intros [Ho|Ho]; [exact (H2 (ax_img (sj_ax B APIf ra empty FF) L A mem md a HMR Ha Ho)) | exact (H1 Ho)].
    - intros [Ho|Ho]; [exact (H2 (ax_img (sj_ax B APIf ra empty FF) L' A' mem' md' a MR' Ha Ho)) | exact (H1 Ho)].
    - unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - intros He. exact (HEimg a He Ha). }
  assert (HH : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 384 - 8192 <= a < g_S g - 384) ->
      mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)).
  { intros a Ha Hs. apply MEM.
    - left. exact Ha.
    - intros Ho. pose proof (HOW _ _ _ _ a HMR Ho). lia.
    - intros Ho. pose proof (HOW _ _ _ _ a MR' Ho). lia.
    - unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - lia. }
  assert (HWR : forall a, g_S g - 65536 <= a < g_S g -> writable_at segs mem' a).
  { intros a Ha. destruct (Z_lt_le_dec a (g_S g - 384 - 8192)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec a (g_S g - 384)) as [Hl2|Hl2]].
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia.
    - apply SCW. unfold scratch. rewrite HSP. unfold ALLOC_STACK. lia.
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia. }
  assert (HPW : pairwise ranges_disjoint (hb1 ++ (ptr_addr L p, n) :: hb2 ++ blocks (g_L g) (g_A g))).
  { rewrite app_comm_cons, app_assoc. apply (sj_pairwise_perm _ _ sj_rd_sym (blocks L A)); [exact HP|].
    exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HMR). }
  pose proof HPW as HPW0. apply sj_pw_app in HPW. destruct HPW as [HPW _].
  assert (STK : forall a, fsp g <= a < 2 ^ 64 -> mbyte segs mem' a = mbyte segs mem a).
  { intros a Ha. unfold fsp, SLOT_FRAME in Ha. exact (proj1 (HH a ltac:(lia) ltac:(lia))). }
  split; [|split; [|split; [exact STK|]]].
  3:{ intros q k j Hq Hj.
      assert (Hin' : In (q, k) (blocks L A)).
      { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left.
        apply in_app_or in Hq as [Hq|Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq]. }
      destruct (Z.eq_dec q (ptr_addr L p)) as [Eq|Nq].
      2:{ exact (KEPT q k j Hin' Nq Hj). }
      destruct (sj_in_blocks L A q k Hin') as (q' & Hq' & Eq').
      destruct (sptr_eq_dec q' p) as [->|Nq'].
      - pose proof (fb_nodup_eq _ p k n (OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable.YO10.user_block_ptrs_NoDup A HWF) Hq' Hpn) as Ek.
        assert (Hy : In (q, k) (hb1 ++ hb2 ++ blocks (g_L g) (g_A g))).
        { apply in_app_or in Hq as [Hq|Hq]; apply in_or_app; [left; exact Hq | right; apply in_or_app; left; exact Hq]. }
        pose proof (fb_pw_mid _ _ _ _ HPW0 Hy) as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
        exfalso. lia.
      - rewrite <- Eq'. exact (UB q' k j Hq' (UBK q' k Hq' Nq') Hj). }
  2:{ rewrite EB'. rewrite <- app_assoc. apply (Permutation_app_inv b1 b2 hb1 (hb2 ++ blocks (g_L g) (g_A g))
        (ptr_addr L p, n)). rewrite <- EB. rewrite app_comm_cons, app_assoc. exact HP. }
  unfold FR, RESB, SLOT_K, SLOT_STACK.
  split; [exact HGV|].
  split; [etransitivity; [exact (RP' 2 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E2|]; exact Hsp|].
  split; [etransitivity; [exact (RP' 3 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E3|]; exact Hgp|].
  split; [etransitivity; [exact (RP' 4 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E4|]; exact Htp|].
  split.
  { apply (sj_ba_mbyte mem); [exact Hsav|]. intros i Hi.
    assert (Hl : length (saved_bytes ra g) = 104%nat)
      by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
    rewrite Hl in Hi. rewrite <- ES. exact (proj1 (HH (g_S g - 104 + i) ltac:(lia) ltac:(lia))). }
  split; [apply (sj_stk_of_wr B APIf ra empty FF); [lia | lia | lia | intros a Ha; rewrite <- ES; apply HWR; exact Ha]|].
  split; [exact RO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct ((sj_relro_img B APIf ra empty FF) a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact (INIT Hin)|].
  split; [destruct Hmd as (vm & ->); exists vm'; rewrite Emd; reflexivity|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [F1 F2]. destruct (HH a Ha ltac:(lia)) as [G1 G2].
    rewrite G1. split; [exact F1|]. tauto. }
  split.
  { intros a Ha H1 H2 H3. destruct (Himg a Ha H1 H2 H3) as [F1 F2]. destruct (HI a Ha H1 H2 H3) as [G1 G2].
    rewrite G1. split; [exact F1|]. tauto. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi).
    assert (Hin' : In (a, k) (blocks L A))
      by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hak).
    destruct (Z.eq_dec a (ptr_addr L p)) as [Ea|Na].
    2:{ unfold blocks_kept in KEPT. exact (KEPT a k i Hin' Na Hi). }
    pose proof (HPW (a, k) ltac:(apply in_or_app; right; exact Hak)) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D.
    destruct (sj_in_blocks L A a k Hin') as (q & Hq & Eq).
    destruct (sptr_eq_dec q p) as [->|Nq].
    - pose proof (fb_nodup_eq _ p k n (OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable.YO10.user_block_ptrs_NoDup A HWF) Hq Hpn). exfalso. lia.
    - rewrite <- Eq. exact (UB q k i Hq (UBK q k Hq Nq) Hi). }
  split; [intros a Ha; apply SCW; unfold scratch; right; exact Ha|].
  split.
  { apply ((sj_sink_frame B APIf ra empty FF) mem mem' md md'); [|rewrite Emd; reflexivity | exact Hsink].
    intros a Ha. destruct ((sj_sink_addr B APIf ra empty FF) a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact (resb_free (g_b g) km (hb1 ++ (ptr_addr L p, n) :: hb2) (hb1 ++ hb2) A' (ptr_addr L p) n
                   (Permutation_sym (Permutation_middle hb1 hb2 (ptr_addr L p, n))) RES')|].
  intros a Ha. apply HWR. exact Ha.
Qed.

Lemma fb_free_call : forall g km hb1 hb2 L A regs mem md regs_c p n (Q : config -> Prop),
  FR B APIf ra empty g km (hb1 ++ (ptr_addr L p, n) :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ (ptr_addr L p, n) :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In (p, n) (user_blocks A) -> 0 <= n ->
  getr regs_c 2 = getr regs 2 -> getr regs_c 3 = getr regs 3 -> getr regs_c 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs_c 1) -> getr regs_c 10 = Z_to_bv 64 (ptr_addr L p) ->
  (forall L' A' regs' mem' md', FR B APIf ra empty g km (hb1 ++ hb2) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb1 ++ hb2) ++ blocks (g_L g) (g_A g)) -> regs_preserved regs_c regs' ->
     (forall a, fsp g <= a < 2 ^ 64 -> mbyte segs mem' a = mbyte segs mem a) ->
     (forall q k j, In (q, k) (hb1 ++ hb2) -> 0 <= j < k -> mbyte segs mem' (q + j) = mbyte segs mem (q + j)) ->
     Rz segs (mkCfg (mkst regs' (getr regs_c 1) mem' (seg_rom segs)) md') Q) ->
  Rz segs (mkCfg (mkst regs_c (Z_to_bv 64 0x15974) mem (seg_rom segs)) md) Q.
Proof.
  intros g km hb1 hb2 L A regs mem md regs_c p n Q HF HP Hpn Hn E2 E3 E4 Hra H10 K.
  pose proof ((sj_call_pre B APIf ra empty) g km _ L A regs mem md regs_c HF E2 E4 Hra) as CP.
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  rewrite <- (sj_free B APIf ra empty FF).
  eapply rz_bind; [exact (rz_free L A regs_c mem md p n (sb_hb (g_b g) (hb1 ++ (ptr_addr L p, n) :: hb2))
                            CP HMI Hpn H10 Hb)|].
  intros c' (L' & A' & regs' & mem' & md' & -> & POST & (b1 & b2 & EB & EB') & KEPT & RO' & _ & UBK & INIT & _ & RES').
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (fb_FR_free g km hb1 hb2 L A regs mem md regs_c p n L' A' regs' mem' md' b1 b2 HF HP Hpn Hn E2 E3 E4
    POST EB EB' KEPT UBK RO' INIT RES') as (HF' & HP' & STK & HBK).
  exact (K L' A' regs' mem' md' HF' HP' RP' STK HBK).
Qed.

Lemma fb_malloc_call : forall g km hb L A regs mem md regs1 n (Q : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs1 2 = getr regs 2 -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs1 1) -> getr regs1 10 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 20 -> (length hb <= 16)%nat ->
  0 <= hb_bytes hb <= 2 ^ 24 ->
  (forall L' A' regs' mem' md' res,
     FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs1 regs' -> getr regs' 10 = Z_to_bv 64 res ->
     (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
     (forall q k j, In (q, k) hb -> 0 <= j < k -> mbyte rsegs mem' (q + j) = mbyte rsegs mem (q + j)) ->
     Rz segs (mkCfg (mkst regs' (getr regs1 1) mem' (seg_rom segs)) md') Q) ->
  Rz segs (mkCfg (mkst regs1 (Z_to_bv 64 0x15ab4) mem (seg_rom segs)) md) Q.
Proof.
  intros g km hb L A regs mem md regs1 n Q HF HP E2 E3 E4 Hra H10 Hn Hlen Hbytes K.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRES & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & GROOM & _).
  rewrite <- (ff_malloc B APIf ra empty FF).
  eapply rz_bind; [apply (rz_malloc L A regs1 mem md n (sb_hb (g_b g) hb)) |].
  - exact (CP_of_FR B APIf ra empty FF g _ _ L A regs regs1 mem md HF E2 E4 Hra).
  - exact HMI.
  - exact H10.
  - exact HRES.
  - exact (rz_room_of L A mem md (g_b g) (Z.of_nat (length hb)) (hb_bytes hb) n HMR GROOM ltac:(lia) Hbytes Hn).
  - intros c' HMret.
    destruct (FR_malloc B APIf ra empty FF g _ _ L A regs regs1 mem md _ c' HF HP E2 E3 E4 HMret)
      as (L' & A' & R2 & mem' & md' & res & -> & HF' & HP' & HPRES & R10 & _ & _ & _ & STK & HBK).
    rewrite (sj_segs B APIf ra empty FF) in STK, HBK.
    exact (K L' A' R2 mem' md' res HF' HP' HPRES R10 STK HBK).
Qed.

Lemma fb_bufof_call : forall g km hb L A regs mem md regs1 n (Q : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  getr regs1 2 = getr regs 2 -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
  YK0s.ret_ok (getr regs1 1) -> getr regs1 10 = Z_to_bv 64 n -> 1 <= n <= 2 ^ 20 -> (length hb <= 16)%nat ->
  0 <= hb_bytes hb <= 2 ^ 24 ->
  (forall L' A' regs' mem' md' res,
     FR B APIf ra empty g (km + 1) (hb ++ [(res, n)]) L' A' regs' mem' md' ->
     Permutation (blocks L' A') ((hb ++ [(res, n)]) ++ blocks (g_L g) (g_A g)) ->
     regs_preserved regs1 regs' -> getr regs' 10 = Z_to_bv 64 res ->
     (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
     (forall q k j, In (q, k) hb -> 0 <= j < k -> mbyte rsegs mem' (q + j) = mbyte rsegs mem (q + j)) ->
     Rz segs (mkCfg (mkst regs' (getr regs1 1) mem' (seg_rom segs)) md') Q) ->
  Rz segs (mkCfg (mkst regs1 (Z_to_bv 64 0x140f0) mem (seg_rom segs)) md) Q.
Proof.
  intros g km hb L A regs mem md regs1 n Q HF HP E2 E3 E4 Hra H10 Hn Hlen Hbytes K.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HMR & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRES & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & GROOM & _).
  assert (EMX : Z.max n 1 = n) by lia.
  eapply rz_bind; [apply (buf_of_holds B (APIf rc) L A regs1 mem md n (sb_hb (g_b g) hb)) |].
  - exact (ff_segs B APIf ra empty FF).
  - exact (ff_malloc B APIf ra empty FF).
  - exact (sj_errno_ceil B APIf ra empty FF).
  - exact (CPk_of_FR B APIf ra empty FF (BUF_OF_FRAME + ALLOC_STACK) g _ _ L A regs regs1 mem md
      ltac:(unfold BUF_OF_FRAME, ALLOC_STACK; lia) HF E2 E4 Hra).
  - exact HMI.
  - exact H10.
  - lia.
  - exact HRES.
  - rewrite EMX. exact (rz_room_of L A mem md (g_b g) (Z.of_nat (length hb)) (hb_bytes hb) n HMR GROOM ltac:(lia)
      Hbytes ltac:(lia)).
  - intros c' HMret. rewrite EMX in HMret.
    assert (HM' : malloc_ret B API (BUF_OF_FRAME + ALLOC_STACK) L A regs1 mem md n (sb_hb (g_b g) hb) c')
      by exact HMret.
    destruct (FR_mallocK B APIf ra empty FF (BUF_OF_FRAME + ALLOC_STACK) g _ _ L A regs regs1 mem md _ c'
      ltac:(unfold BUF_OF_FRAME, ALLOC_STACK; lia) HF HP E2 E3 E4 HM')
      as (L' & A' & R2 & mem' & md' & res & -> & HF' & HP' & HPRES & R10 & _ & _ & _ & STK & HBK).
    rewrite (sj_segs B APIf ra empty FF) in STK, HBK.
    exact (K L' A' R2 mem' md' res HF' HP' HPRES R10 STK HBK).
Qed.

End TacFB.
