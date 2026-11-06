From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require MState Mem Frame Exec Cells Step FP.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import check_braid_c check_round_trip_c crt_glue
  crt_segs crt_seg4 reac_braid_encode_exact_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import check_round_trip LLVMFuzzerTestOneInput_cfb fd_segments_ccf check_round_trip_ccf crt_glue_cg.
Import ListNotations.
Local Open Scope Z_scope.

Section CRT.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = 0x14df4.
Hypothesis FREEPC : ms_free B = 0x14cb4.
Hypothesis CALPC : ms_calloc B = Some 0x14b7c.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract_ag B API.
Hypothesis CALLOC : calloc_contract_ag B API 0x14b7c.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis ENC : reac_braid_encode_exact_contract.
Hypothesis BCMP : bcmp_contract.

Lemma cr_blk_cf : forall Lk Ak mk mdk P n, aa_MR API Lk Ak mk mdk -> In (P, n) (blocks Lk Ak) ->
  4096 <= P /\ P + n <= alloc_ceiling /\ P mod 16 = 0 /\
  forall i, 0 <= i < n -> present mk (P + i) /\ ~ in_img B (P + i) /\ ~ owned B Lk Ak (P + i).
Proof.
  intros Lk Ak mk mdk P n HM Hin.
  destruct (crt_bu Lk Ak P n Hin) as (p & Hp & <-).
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp) as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  split; [exact (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ p n HM Hp)|].
  intros i Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hp Hi) as (Hpr & _ & _ & Hno).
  split; [exact Hpr|]. split; [exact (ax_blocks_img AX Lk Ak mk mdk p n i HM Hp Hi) | exact Hno].
Qed.

Lemma cr_cells_norm_cf : img_low B -> forall m A cs, Step.rw_cells (ms_segs B) m A cs -> ro_agree (ms_segs B) m ->
  alloc_ceiling <= A -> Step.rw_cells (ms_segs B) (normalize (ms_segs B) m) A cs.
Proof.
  intros HI m A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wn & Hw)] Hro HA.
  pose proof (mem_rel_normalize (ms_segs B) m Hro) as HR.
  pose proof (Cells.cells_bytes_length cs Hwf) as LN.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi. rewrite <- (Hb i Hi).
    symmetry. apply (mrd_rel (ms_segs B) m _ _ HR).
  - split; [exact Wa|]. split; [exact Wn|]. intros i Hi.
    assert (Hra : Mem.ro_addr (ms_segs B) (Mem.wa (A + i)) = false)
      by (apply (crt_ro_false_cf B); [lia | apply (crt_fs_high_cf B HI); lia]).
    rewrite (wview_rel_rw (ms_segs B) m _ _ HR Hra). exact (Hw i Hi).
Qed.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (audio pcm nch ns : Z) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CRT_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 audio.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 pcm.
Hypothesis R12 : getr regs 12 = Z_to_bv 64 nch.
Hypothesis R13 : getr regs 13 = Z_to_bv 64 ns.
Hypothesis EV : Z.even nch = true.
Hypothesis NCH : 2 <= nch <= 127.
Hypothesis NS : 1 <= ns <= 12.
Hypothesis KB : 3 * nch * ns <= 1440.
Hypothesis AU : 0 < audio < 2 ^ 63.
Hypothesis PCM : 0 < pcm < 2 ^ 63.
Hypothesis IBA : in_block L A audio (3 * nch * ns).
Hypothesis IBP : in_block L A pcm (3 * nch * ns).
Hypothesis BM : braid_map mem audio pcm nch ns.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : (sb_live b + 3 <= sb_cap b <= CAP_AG /\ 128 <= sb_cap b) /\ 0 <= sb_bytes b /\ sb_bytes b + 7 * nch * ns + 8 * nch <= 2 ^ 29.

Definition cr_inv_cf (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  kb_mid B API CRT_STACK (spZ regs) L A mem md (fun _ => False) L' A' m' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A')) /\
  ro_agree (ms_segs B) m' /\ guard_kept B mem m'.

Definition cr_keep_cf (r : bvmap 5 word) : Prop :=
  getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4.

Definition cr_frame_cf (m' : word -> option byte) : Prop :=
  Step.rw_cells rsegs m' (spZ regs - 112) [Cells.C8 (Z_to_bv 64 audio); Cells.C8 (getr regs 27);
    Cells.C8 (getr regs 26); Cells.C8 (getr regs 25); Cells.C8 (getr regs 24); Cells.C8 (getr regs 23);
    Cells.C8 (getr regs 22); Cells.C8 (getr regs 21); Cells.C8 (getr regs 20); Cells.C8 (getr regs 19);
    Cells.C8 (getr regs 18); Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)].

Definition cr_final_cf (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CRT_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    st_init_done A' = true.

Lemma cr_pre_cf : forall Lk Ak mk mdk regsk f K1,
  cr_inv_cf Lk Ak mk mdk -> spZ regsk = spZ regs - f -> 0 <= f -> 0 <= K1 -> f + K1 <= CRT_STACK ->
  spZ regsk mod 16 = 0 -> getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) -> st_init_done Ak = true ->
  call_pre_k B (aa_MR API) K1 Lk Ak regsk mk mdk.
Proof.
  intros Lk Ak mk mdk regsk f K1 ((M1 & W1 & B1 & _ & _ & _ & _ & _ & S1) & _) Hsp Hf HK1 HfK H16 H4 Hra Hinit.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _ & Htp & _).
  refine (conj M1 (conj W1 (conj B1 (conj Hra (conj H16 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - lia.
  - lia.
  - intros a Ha. apply S1. left. lia.
  - rewrite H4. exact Htp.
  - intros a Ha. apply S1. right. exact Ha.
  - intros E. rewrite Hinit in E. discriminate.
Qed.

Lemma cr_inv_call_cf : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cr_inv_cf Lk Ak mk mdk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regs - CRT_STACK <= spZ regsk - K2 -> spZ regsk <= spZ regs ->
  (forall a, E2 a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (length (st_regions Ak) <= length (st_regions A2))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A2)) ->
  ro_agree (ms_segs B) m2 -> guard_kept B mk m2 ->
  cr_inv_cf L2 A2 m2 md2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 (I1 & I2 & I3 & I4 & I5) Hpost H1 H2 HE HL HU Hro Hg.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost) as [Hmid _].
  split.
  { apply (crt_drop_cf B API _ _ _ _ _ _ (fun a => False \/ E2 a)).
    - eapply (crt_seq_cf B API AX CT); [exact HM | exact I1 | exact Hmid | lia | lia | lia | lia | | exact I2 | exact I3].
      intros a Ha _ He. destruct (HE a He) as [Ha' _]. lia.
    - intros a [[]|He]. exact (HE a He). }
  split; [lia|]. split; [exact HU|]. split; [exact Hro|].
  intros i Hi. rewrite (Hg i Hi). exact (I5 i Hi).
Qed.

Lemma cr_inv_A_cf : forall Lk Ak mk mdk mk' W,
  cr_inv_cf Lk Ak mk mdk ->
  Frame.munch W mk mk' -> Frame.wmono (ms_segs B) mk mk' -> (forall x, mk x <> None -> mk' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CRT_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lk Ak x /\
      forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ptr_addr L p + i <> x)) ->
  ro_agree (ms_segs B) mk' ->
  cr_inv_cf Lk Ak mk' mdk.
Proof.
  intros Lk Ak mk mdk mk' W (I1 & I2 & I3 & I4 & I5) Hm Hw Hp HW Hro.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (crt_img_low_cf B SEGS) as HIL.
  pose proof I1 as (M1 & _).
  split.
  { apply (crt_drop_cf B API _ _ _ _ _ _
      (fun x => False \/ (0 <= x < 2 ^ 64 /\ ~ Frame.outside W x /\ ~ (spZ regs - CRT_STACK <= x < spZ regs)))).
    - apply (kb_mid_tail B API HIL _ _ _ _ _ _ _ Lk Ak mk mdk mk' W); [exact I1 | exact Hm | exact Hw | exact Hp | | |].
      + intros x Hx Hs He. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. apply He. tauto.
      + intros x Hx Ho. destruct (kb_outside_dec W x) as [Hout|Hout]; [exact Hout|]. exfalso.
        destruct (HW x ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
      + intros p n i Hin Hin' Hi. destruct (kb_outside_dec W (ptr_addr L p + i)) as [Hout|Hout]; [exact Hout|].
        exfalso. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hin) as [Hr1 Hr2].
        destruct (HW (ptr_addr L p + i) ltac:(lia) Hout) as [Hs | (_ & _ & _ & H4)];
          [lia | exact (H4 p n i Hin Hi eq_refl)].
    - intros x [[]|(Hx & Ho & Hs)].
      destruct (HW x Hx Ho) as [H|(H1 & H2 & _)]; [contradiction | split; assumption]. }
  split; [exact I2|]. split; [exact I3|]. split; [exact Hro|].
  intros i Hi. rewrite <- (I5 i Hi).
  assert (Ho : owned B Lk Ak (ms_got_guard B + i))
    by (right; unfold static_owned; right; right; right; right; left; lia).
  pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho) as Hr.
  apply (mbyte_munch (ms_segs B) W mk mk'); [exact Hm | lia |].
  destruct (kb_outside_dec W (ms_got_guard B + i)) as [Hout|Hout]; [exact Hout|]. exfalso.
  destruct (HW (ms_got_guard B + i) ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
Qed.

Lemma cr_free_keep_cf : forall Lk Ak mk mdk p n,
  cr_inv_cf Lk Ak mk mdk -> In (p, n) (user_blocks Ak) -> 0 < n ->
  (forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr Lk p, n) y) ->
  forall q k, In (q, k) (user_blocks A) -> q <> p.
Proof.
  intros Lk Ak mk mdk p n ((M1 & W1 & _ & _ & P1 & _) & _ & I3 & _) Hp Hn HD q k Hq Eq. subst q.
  pose proof (I3 p k Hq) as Hpk.
  pose proof (user_block_ptrs_NoDup Ak W1) as ND.
  pose proof (crt_fst_unique _ p k n ND Hpk Hp) as Ek. subst k.
  pose proof (HD _ (crt_ub L A p n Hq)) as D.
  rewrite (P1 p n Hq Hpk) in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma cr_old_in_cf : forall Lk Ak mk mdk, cr_inv_cf Lk Ak mk mdk -> forall y, In y (blocks L A) -> In y (blocks Lk Ak).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & P1 & _) & _ & I3 & _) [a k] Hy.
  destruct (crt_bu L A a k Hy) as (p & Hp & <-).
  pose proof (I3 p k Hp) as Hp'. rewrite <- (P1 p k Hp Hp'). exact (crt_ub Lk Ak p k Hp').
Qed.

Lemma cr_frame_call_cf : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cr_inv_cf Lk Ak mk mdk -> cr_frame_cf mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 112 -> (forall a, E2 a -> a < alloc_ceiling) ->
  cr_frame_cf m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 ((M1 & _) & _) FR Hpost Hsp HE.
  pose proof Hpost as (M2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  unfold cr_frame_cf in *. rewrite <- SEGS in FR |- *.
  apply (crt_cells_mb B mk m2 _ _ FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 112 in Hi.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hr : alloc_ceiling <= spZ regs - 112 + i < 2 ^ 64) by lia.
  destruct (Hfr (spZ regs - 112 + i)) as [E W].
  - left. exact Hr.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - unfold scratch_k. lia.
  - intros He. pose proof (HE _ He). lia.
  - split; [exact E | intros Hw; apply W; exact Hw].
Qed.

Lemma cr_inv_kept_cf : forall Lk Ak mk mdk, cr_inv_cf Lk Ak mk mdk -> blocks_kept B L A mem mk (fun _ => False).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & K1 & _) & _ & I3 & _) a k i Hin _ Hi.
  destruct (crt_bu L A a k Hin) as (p & Hp & <-). exact (K1 p k i Hp (I3 p k Hp) Hi).
Qed.

Lemma cr_keep_pres_cf : forall r r', cr_keep_cf r -> regs_preserved r r' -> cr_keep_cf r'.
Proof.
  intros r r' (K3 & K4) Hp. split.
  - transitivity (getr r 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
Qed.

Lemma cr_heap_E_cf : forall Lk Ak mk mdk p n, aa_MR API Lk Ak mk mdk -> In (p, n) (user_blocks Ak) ->
  forall a, ptr_addr Lk p <= a < ptr_addr Lk p + n -> a < alloc_ceiling /\ ~ in_img B a.
Proof.
  intros Lk Ak mk mdk p n HMk Hp a Ha.
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p _ HMk Hp) as [Hr1 Hr2].
  split; [lia|]. replace a with (ptr_addr Lk p + (a - ptr_addr Lk p)) by lia.
  exact (ax_blocks_img AX Lk Ak mk mdk p n (a - ptr_addr Lk p) HMk Hp ltac:(lia)).
Qed.

Lemma cr_ph6_cf : forall (fx7 : FPState) L5 A5 regs10 m10 md5 P c1 c2,
  frm_zero (@fp_csr fx7) ->
  cr_inv_cf L5 A5 m10 md5 -> st_init_done A5 = true ->
  blocks L5 A5 = c1 ++ (P, 4 * (nch * ns)) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A5 (sb_malloc b (4 * (nch * ns))) ->
  getr regs10 2 = Z_to_bv 64 (spZ regs - 112) -> getr regs10 8 = Z_to_bv 64 P -> cr_keep_cf regs10 ->
  cr_frame_cf m10 ->
  SRcf B (mkCfg (@mkst fx7 regs10 (Z_to_bv 64 0x136ac) m10 (seg_rom (ms_segs B))) md5) cr_final_cf.
Proof.
  intros fx7 L5 A5 regs10 m10 md5 P c1 c2 Hfrm I Hinit Hb5 Hb0 Hres G2 G8 GK FR. unfold cr_frame_cf in FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hk : 0 < nch * ns) by nia.
  pose proof I as ((M5 & W5 & B5 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L5 A5 m10 md5 M5) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs10 2) = spZ regs - 112) by (rewrite G2; apply MState.unsigned_lit; lia).
  eapply (crt_runA_cf (fx := fx7) B SEGS regs10 _ m10 md5); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply crt_seg6. rewrite USP. exact FR. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs11 -> Hg11. cbn [MState.MS ms_pc_val ms_mem].
  assert (G11a : getr regs11 1 = getr regs 1) by (rewrite Hg11; reflexivity).
  assert (G11b : getr regs11 2 = Z_to_bv 64 (bv_unsigned (getr regs10 2) + 112)) by (rewrite Hg11; reflexivity).
  rewrite USP in G11b. replace (spZ regs - 112 + 112) with (spZ regs) in G11b by lia.
  assert (G11c : getr regs11 4 = getr regs 4) by (rewrite Hg11; exact (proj2 GK)).
  assert (G11d : getr regs11 10 = Z_to_bv 64 P) by (rewrite Hg11; exact G8).
  assert (S11 : spZ regs11 = spZ regs) by (unfold spZ at 1; rewrite G11b; apply MState.unsigned_lit; lia).
  assert (P11 : regs_preserved regs regs11).
  { destruct GK as (K3 & K4).
    assert (Hs : getr regs11 2 = getr regs 2) by (rewrite G11b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg11; first [reflexivity | exact K3 | exact K4]]. }
  destruct (crt_bu L5 A5 P _ ltac:(rewrite Hb5; apply crt_in_mid)) as (p & Hp & Ep).
  assert (Hpre11 : call_pre B (aa_MR API) L5 A5 regs11 m10 md5).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L5 A5 regs11 m10 md5)).
    apply (cr_pre_cf L5 A5 m10 md5 regs11 0 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia | rewrite S11; exact H16 | exact G11c | rewrite G11a; exact Hra
      | exact Hinit]. }
  replace (Z_to_bv 64 CRT_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L5 A5 regs11 m10 md5 p (4 * (nch * ns)) (sb_malloc b (4 * (nch * ns))) Hpre11 I4 Hp).
    - rewrite G11d, Ep. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  rewrite Ep in Hd1.
  assert (PW5 : pairwise ranges_disjoint (c1 ++ (P, 4 * (nch * ns)) :: c2))
    by (rewrite <- Hb5; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M5)).
  assert (ND5 : ~ In (P, 4 * (nch * ns)) (c1 ++ c2)) by (apply (crt_notin c1 c2 _ PW5); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (crt_rm (P, 4 * (nch * ns)) c1 c2 d1 d2 ND5). rewrite <- Hb5. exact Hd1. }
  assert (HD5 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L5 p, 4 * (nch * ns)) y).
  { intros y Hy. rewrite Ep. apply (crt_pw_mid c1 c2 _ y PW5). rewrite <- Hb0. exact Hy. }
  assert (HU6 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A6)).
  { intros q k Hq. apply Hub6; [exact (I3 q k Hq) | exact (cr_free_keep_cf L5 A5 m10 md5 p _ I Hp ltac:(lia) HD5 q k Hq)]. }
  assert (I6 : cr_inv_cf L6 A6 m12 md6).
  { apply (cr_inv_call_cf L5 A5 m10 md5 regs11 ALLOC_STACK _ L6 A6 regs12 m12 md6 I Hpost);
      [rewrite S11, HK0; unfold ALLOC_STACK; lia | lia | exact (cr_heap_E_cf L5 A5 m10 md5 p _ M5 Hp) | exact Hlen6
      | exact HU6 | exact Hro6 | exact Hgk6]. }
  apply (SRcf_ret B). exists fx7, L6, A6, regs12, m12, md6.
  split; [rewrite G11a; reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    exact (kb_preserved_trans _ _ _ P11 (proj2 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost))). }
  split; [exact Hb6|].
  split; [exact (cr_inv_kept_cf _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | exact (Hinit6 Hinit)].
Qed.

Lemma cr_ph5_cf : forall (fx7 : FPState) L4 A4 regs8 m8 md4 P Q c1 c2 e1 e2,
  frm_zero (@fp_csr fx7) ->
  cr_inv_cf L4 A4 m8 md4 -> st_init_done A4 = true ->
  blocks L4 A4 = e1 ++ (Q, 8 * nch) :: e2 -> e1 ++ e2 = c1 ++ (P, 4 * (nch * ns)) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A4 (sb_malloc (sb_malloc b (4 * (nch * ns))) (8 * nch)) ->
  getr regs8 2 = Z_to_bv 64 (spZ regs - 112) -> getr regs8 8 = Z_to_bv 64 P -> getr regs8 19 = Z_to_bv 64 Q ->
  cr_keep_cf regs8 -> cr_frame_cf m8 ->
  SRcf B (mkCfg (@mkst fx7 regs8 (Z_to_bv 64 0x136a4) m8 (seg_rom (ms_segs B))) md4) cr_final_cf.
Proof.
  intros fx7 L4 A4 regs8 m8 md4 P Q c1 c2 e1 e2 Hfrm I Hinit Hb4 He Hb0 Hres G2 G8 G19 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hk : 0 < nch * ns) by nia.
  pose proof I as ((M4 & W4 & B4 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L4 A4 m8 md4 M4) as [Hh Hlz].
  eapply (crt_runA_cf (fx := fx7) B SEGS regs8 _ m8 md4); [exact Hh | exact Hlz | | |].
  { unfold rmk. apply crt_seg5. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs9 -> Hg9. cbn [MState.MS ms_pc_val ms_mem].
  assert (G9a : getr regs9 1 = Z_to_bv 64 0x136ac) by (rewrite Hg9; reflexivity).
  assert (G9b : getr regs9 2 = Z_to_bv 64 (spZ regs - 112)) by (rewrite Hg9; exact G2).
  assert (G9c : getr regs9 4 = getr regs 4) by (rewrite Hg9; exact (proj2 GK)).
  assert (G9d : getr regs9 10 = Z_to_bv 64 Q) by (rewrite Hg9; exact G19).
  assert (G9e : getr regs9 8 = Z_to_bv 64 P) by (rewrite Hg9; exact G8).
  assert (K9 : cr_keep_cf regs9).
  { destruct GK as (K3 & K4). split; rewrite Hg9; first [exact K3 | exact K4]. }
  assert (S9 : spZ regs9 = spZ regs - 112) by (unfold spZ at 1; rewrite G9b; apply MState.unsigned_lit; lia).
  destruct (crt_bu L4 A4 Q _ ltac:(rewrite Hb4; apply crt_in_mid)) as (q & Hq & Eq).
  assert (Hpre9 : call_pre B (aa_MR API) L4 A4 regs9 m8 md4).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L4 A4 regs9 m8 md4)).
    apply (cr_pre_cf L4 A4 m8 md4 regs9 112 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S9; replace (spZ regs - 112) with (spZ regs + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact G9c | rewrite G9a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity | exact Hinit]. }
  replace (Z_to_bv 64 CRT_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L4 A4 regs9 m8 md4 q (8 * nch) (sb_malloc (sb_malloc b (4 * (nch * ns))) (8 * nch))
      Hpre9 I4 Hq).
    - rewrite G9d, Eq. reflexivity.
    - exact Hres. }
  intros c' (L5 & A5 & regs10 & m10 & md5 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro5 & Hgk5 & Hub5 &
    Hinit5 & Hlen5 & Hres5).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp10 & _).
  rewrite Eq in Hd1.
  assert (PW4 : pairwise ranges_disjoint (e1 ++ (Q, 8 * nch) :: e2))
    by (rewrite <- Hb4; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M4)).
  assert (ND4 : ~ In (Q, 8 * nch) (e1 ++ e2)) by (apply (crt_notin e1 e2 _ PW4); cbn; lia).
  assert (Hb5 : blocks L5 A5 = c1 ++ (P, 4 * (nch * ns)) :: c2).
  { rewrite Hd2, <- He. symmetry. apply (crt_rm (Q, 8 * nch) e1 e2 d1 d2 ND4). rewrite <- Hb4. exact Hd1. }
  assert (HD4 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L4 q, 8 * nch) y).
  { intros y Hy. rewrite Eq. apply (crt_pw_mid e1 e2 _ y PW4). rewrite He. apply crt_in_ins. rewrite <- Hb0. exact Hy. }
  assert (HU5 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A5)).
  { intros q' k Hq'. apply Hub5; [exact (I3 q' k Hq') | exact (cr_free_keep_cf L4 A4 m8 md4 q _ I Hq ltac:(lia) HD4 q' k Hq')]. }
  assert (I5' : cr_inv_cf L5 A5 m10 md5).
  { apply (cr_inv_call_cf L4 A4 m8 md4 regs9 ALLOC_STACK _ L5 A5 regs10 m10 md5 I Hpost);
      [rewrite S9, HK0; unfold ALLOC_STACK; lia | lia | exact (cr_heap_E_cf L4 A4 m8 md4 q _ M4 Hq) | exact Hlen5
      | exact HU5 | exact Hro5 | exact Hgk5]. }
  assert (FR5 : cr_frame_cf m10).
  { apply (cr_frame_call_cf L4 A4 m8 md4 regs9 ALLOC_STACK _ L5 A5 regs10 m10 md5 I FR Hpost); [lia |].
    intros a Ha. exact (proj1 (cr_heap_E_cf L4 A4 m8 md4 q _ M4 Hq a Ha)). }
  rewrite G9a.
  apply (cr_ph6_cf fx7 L5 A5 regs10 m10 md5 P c1 c2 Hfrm I5' (Hinit5 Hinit) Hb5 Hb0).
  - rewrite sb_free_malloc in Hres5. exact Hres5.
  - transitivity (getr regs9 2); [apply (Hp10 2); unfold callee_saved; lia | exact G9b].
  - transitivity (getr regs9 8); [apply (Hp10 8); unfold callee_saved; lia | exact G9e].
  - exact (cr_keep_pres_cf regs9 regs10 K9 Hp10).
  - exact FR5.
Qed.

Lemma cr_ph4_cf : forall (fx7 : FPState) L3 A3 regs7 m7 md3 P Q O c1 c2 e1 e2 g1 g2,
  frm_zero (@fp_csr fx7) ->
  cr_inv_cf L3 A3 m7 md3 -> st_init_done A3 = true ->
  blocks L3 A3 = g1 ++ (O, 3 * (nch * ns)) :: g2 -> g1 ++ g2 = e1 ++ (Q, 8 * nch) :: e2 ->
  e1 ++ e2 = c1 ++ (P, 4 * (nch * ns)) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A3 (sb_malloc (sb_malloc (sb_malloc b (4 * (nch * ns))) (8 * nch)) (3 * (nch * ns))) ->
  getr regs7 1 = Z_to_bv 64 0x136a4 -> getr regs7 2 = Z_to_bv 64 (spZ regs - 112) ->
  getr regs7 8 = Z_to_bv 64 P -> getr regs7 10 = Z_to_bv 64 O -> getr regs7 19 = Z_to_bv 64 Q ->
  cr_keep_cf regs7 -> cr_frame_cf m7 ->
  SRcf B (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 CRT_FREE) m7 (seg_rom (ms_segs B))) md3) cr_final_cf.
Proof.
  intros fx7 L3 A3 regs7 m7 md3 P Q O c1 c2 e1 e2 g1 g2 Hfrm I Hinit Hb3 Hg He Hb0 Hres G1 G2 G8 G10 G19 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hk : 0 < nch * ns) by nia.
  pose proof I as ((M3 & W3 & B3 & _) & I2 & I3 & I4 & I5).
  assert (S7 : spZ regs7 = spZ regs - 112) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  destruct (crt_bu L3 A3 O _ ltac:(rewrite Hb3; apply crt_in_mid)) as (o & Ho & Eo).
  assert (Hpre7 : call_pre B (aa_MR API) L3 A3 regs7 m7 md3).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L3 A3 regs7 m7 md3)).
    apply (cr_pre_cf L3 A3 m7 md3 regs7 112 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S7; replace (spZ regs - 112) with (spZ regs + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj2 GK) | rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  replace (Z_to_bv 64 CRT_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L3 A3 regs7 m7 md3 o (3 * (nch * ns))
      (sb_malloc (sb_malloc (sb_malloc b (4 * (nch * ns))) (8 * nch)) (3 * (nch * ns))) Hpre7 I4 Ho).
    - rewrite G10, Eo. reflexivity.
    - exact Hres. }
  intros c' (L4 & A4 & regs8 & m8 & md4 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro4 & Hgk4 & Hub4 &
    Hinit4 & Hlen4 & Hres4).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp8 & _).
  rewrite Eo in Hd1.
  assert (PW3 : pairwise ranges_disjoint (g1 ++ (O, 3 * (nch * ns)) :: g2))
    by (rewrite <- Hb3; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M3)).
  assert (ND3 : ~ In (O, 3 * (nch * ns)) (g1 ++ g2)) by (apply (crt_notin g1 g2 _ PW3); cbn; lia).
  assert (Hb4 : blocks L4 A4 = e1 ++ (Q, 8 * nch) :: e2).
  { rewrite Hd2, <- Hg. symmetry. apply (crt_rm (O, 3 * (nch * ns)) g1 g2 d1 d2 ND3). rewrite <- Hb3. exact Hd1. }
  assert (HD3 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L3 o, 3 * (nch * ns)) y).
  { intros y Hy. rewrite Eo. apply (crt_pw_mid g1 g2 _ y PW3). rewrite Hg. apply crt_in_ins. rewrite He.
    apply crt_in_ins. rewrite <- Hb0. exact Hy. }
  assert (HU4 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A4)).
  { intros q' k Hq'. apply Hub4; [exact (I3 q' k Hq') | exact (cr_free_keep_cf L3 A3 m7 md3 o _ I Ho ltac:(lia) HD3 q' k Hq')]. }
  assert (I4' : cr_inv_cf L4 A4 m8 md4).
  { apply (cr_inv_call_cf L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8 md4 I Hpost);
      [rewrite S7, HK0; unfold ALLOC_STACK; lia | lia | exact (cr_heap_E_cf L3 A3 m7 md3 o _ M3 Ho) | exact Hlen4
      | exact HU4 | exact Hro4 | exact Hgk4]. }
  assert (FR4 : cr_frame_cf m8).
  { apply (cr_frame_call_cf L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8 md4 I FR Hpost); [lia |].
    intros a Ha. exact (proj1 (cr_heap_E_cf L3 A3 m7 md3 o _ M3 Ho a Ha)). }
  rewrite G1.
  apply (cr_ph5_cf fx7 L4 A4 regs8 m8 md4 P Q c1 c2 e1 e2 Hfrm I4' (Hinit4 Hinit) Hb4 He Hb0).
  - rewrite sb_free_malloc in Hres4. exact Hres4.
  - transitivity (getr regs7 2); [apply (Hp8 2); unfold callee_saved; lia | exact G2].
  - transitivity (getr regs7 8); [apply (Hp8 8); unfold callee_saved; lia | exact G8].
  - transitivity (getr regs7 19); [apply (Hp8 19); unfold callee_saved; lia | exact G19].
  - exact (cr_keep_pres_cf regs7 regs8 GK Hp8).
  - exact FR4.
Qed.

Lemma cr_ph3_cf : forall L3 A3 regs6 m6 md3 P Q O c1 c2 e1 e2 g1 g2,
  cr_inv_cf L3 A3 m6 md3 -> st_init_done A3 = true ->
  blocks L3 A3 = g1 ++ (O, 3 * (nch * ns)) :: g2 -> g1 ++ g2 = e1 ++ (Q, 8 * nch) :: e2 ->
  e1 ++ e2 = c1 ++ (P, 4 * (nch * ns)) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A3 (sb_malloc (sb_malloc (sb_malloc b (4 * (nch * ns))) (8 * nch)) (3 * (nch * ns))) ->
  getr regs6 2 = Z_to_bv 64 (spZ regs - 112) -> getr regs6 8 = Z_to_bv 64 P ->
  getr regs6 10 = Z_to_bv 64 O -> getr regs6 18 = Z_to_bv 64 (3 * (nch * ns)) -> getr regs6 19 = Z_to_bv 64 Q ->
  getr regs6 20 = Z_to_bv 64 ns -> getr regs6 21 = Z_to_bv 64 nch -> getr regs6 22 = Z_to_bv 64 pcm ->
  cr_keep_cf regs6 -> cr_frame_cf m6 ->
  SRcf B (mkCfg (mkst regs6 (Z_to_bv 64 0x13564) m6 (seg_rom (ms_segs B))) md3) cr_final_cf.
Proof.
  intros L3 A3 regs6 m6 md3 P Q O c1 c2 e1 e2 g1 g2 I Hinit Hb3 Hg He Hb0 Hres G2 G8 G10 G18 G19 G20 G21 G22
    GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hk : 0 < nch * ns) by nia.
  assert (HE2 : nch mod 2 = 0) by (rewrite Zmod_even, EV; reflexivity).
  pose proof I as ((M3 & W3 & B3 & _ & _ & _ & _ & _ & S3) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L3 A3 m6 md3 M3) as [Hh Hlz].
  pose proof (crt_img_low_cf B SEGS) as HIL.
  assert (S6 : spZ regs6 = spZ regs - 112) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (Hro' : ro_agree rsegs m6) by (rewrite <- SEGS; exact I4).
  assert (PW3 : pairwise ranges_disjoint (g1 ++ (O, 3 * (nch * ns)) :: g2))
    by (rewrite <- Hb3; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M3)).
  assert (PWg : pairwise ranges_disjoint (e1 ++ (Q, 8 * nch) :: e2)) by (rewrite <- Hg; exact (crt_pw_del g1 g2 _ PW3)).
  assert (PWe : pairwise ranges_disjoint (c1 ++ (P, 4 * (nch * ns)) :: c2))
    by (rewrite <- He; exact (crt_pw_del e1 e2 _ PWg)).
  assert (InO : In (O, 3 * (nch * ns)) (blocks L3 A3)) by (rewrite Hb3; apply crt_in_mid).
  assert (InQg : In (Q, 8 * nch) (g1 ++ g2)) by (rewrite Hg; apply crt_in_mid).
  assert (InPe : In (P, 4 * (nch * ns)) (e1 ++ e2)) by (rewrite He; apply crt_in_mid).
  assert (InPg : In (P, 4 * (nch * ns)) (g1 ++ g2)) by (rewrite Hg; apply crt_in_ins; exact InPe).
  assert (InQ : In (Q, 8 * nch) (blocks L3 A3)) by (rewrite Hb3; apply crt_in_ins; exact InQg).
  assert (InP : In (P, 4 * (nch * ns)) (blocks L3 A3)) by (rewrite Hb3; apply crt_in_ins; exact InPg).
  assert (Hold : forall y, In y (blocks L A) -> In y (c1 ++ c2) /\ In y (e1 ++ e2) /\ In y (g1 ++ g2)).
  { intros y Hy. rewrite Hb0 in Hy.
    assert (Y2 : In y (e1 ++ e2)) by (rewrite He; apply crt_in_ins; exact Hy).
    split; [exact Hy|]. split; [exact Y2|]. rewrite Hg. apply crt_in_ins. exact Y2. }
  destruct (cr_blk_cf L3 A3 m6 md3 O _ M3 InO) as (HO1 & HO2 & _ & HOi).
  destruct (cr_blk_cf L3 A3 m6 md3 Q _ M3 InQ) as (HQ1 & HQ2 & HQ3 & HQi).
  destruct (cr_blk_cf L3 A3 m6 md3 P _ M3 InP) as (HP1 & HP2 & HP3 & HPi).
  pose proof IBA as (qa & ka & Hqa & Ha1 & Ha2).
  pose proof IBP as (qp & kp & Hqp & Hp1 & Hp2).
  destruct (cr_blk_cf L A mem md qa ka HM Hqa) as (HA1 & HA2 & _).
  destruct (cr_blk_cf L A mem md qp kp HM Hqp) as (HC1 & HC2 & _).
  destruct (Hold _ Hqa) as (Ac & Ae & Ag).
  destruct (Hold _ Hqp) as (Cc & Ce & Cg).
  pose proof (cr_pw _ _ _ _ _ _ PW3 InQg) as DOQ.
  pose proof (cr_pw _ _ _ _ _ _ PW3 InPg) as DOP.
  pose proof (cr_pw _ _ _ _ _ _ PW3 Ag) as DOA.
  pose proof (cr_pw _ _ _ _ _ _ PWg InPe) as DQP.
  pose proof (cr_pw _ _ _ _ _ _ PWg Ae) as DQA.
  pose proof (cr_pw _ _ _ _ _ _ PWg Ce) as DQC.
  pose proof (cr_pw _ _ _ _ _ _ PWe Ac) as DPA.
  pose proof (cr_pw _ _ _ _ _ _ PWe Cc) as DPC.
  assert (WP : Mem.wr_at rsegs (normalize rsegs m6) P (4 * nch * ns)).
  { rewrite <- SEGS. replace (4 * nch * ns) with (4 * (nch * ns)) by ring.
    apply (crt_wr_norm_cf B SEGS m6); [exact I4 | lia | lia |].
    intros i Hi. destruct (HPi i Hi) as (X1 & X2 & _). split; assumption. }
  assert (WQ : Mem.wr_at rsegs (normalize rsegs m6) Q (8 * nch)).
  { rewrite <- SEGS. apply (crt_wr_norm_cf B SEGS m6); [exact I4 | lia | lia |].
    intros i Hi. destruct (HQi i Hi) as (X1 & X2 & _). split; assumption. }
  assert (WO : Mem.wr_at rsegs (normalize rsegs m6) O (3 * nch * ns)).
  { rewrite <- SEGS. replace (3 * nch * ns) with (3 * (nch * ns)) by ring.
    apply (crt_wr_norm_cf B SEGS m6); [exact I4 | lia | lia |].
    intros i Hi. destruct (HOi i Hi) as (X1 & X2 & _). split; assumption. }
  assert (ST : Frame.stk rsegs (normalize rsegs m6) (bv_unsigned (getr regs6 2) - 112) (bv_unsigned (getr regs6 2))).
  { change (bv_unsigned (getr regs6 2)) with (spZ regs6). rewrite S6, <- SEGS.
    apply (crt_stk_norm_cf B HIL); [| exact I4 | lia].
    apply (crt_stk_cf B HIL); [lia | lia |]. intros a Ha. apply S3. left. lia. }
  assert (BM6 : braid_map (normalize rsegs m6) audio pcm nch ns).
  { pose proof (cr_inv_kept_cf L3 A3 m6 md3 I) as KP.
    apply (crt_bm_frame mem _ audio pcm nch ns BM EV ltac:(lia) ltac:(lia)); intros i Hi;
      rewrite <- (mrd_rel rsegs m6 (normalize rsegs m6) _ (mem_rel_normalize rsegs m6 Hro')).
    - pose proof (KP qa ka (audio - qa + i) Hqa (fun H => H) ltac:(lia)) as E.
      replace (qa + (audio - qa + i)) with (audio + i) in E by ring. rewrite SEGS in E. exact E.
    - pose proof (KP qp kp (pcm - qp + i) Hqp (fun H => H) ltac:(lia)) as E.
      replace (qp + (pcm - qp + i)) with (pcm + i) in E by ring. rewrite SEGS in E. exact E. }
  assert (FRN : Step.rw_cells rsegs (normalize rsegs m6) (bv_unsigned (getr regs6 2))
    [Cells.C8 (Z_to_bv 64 audio); Cells.C8 (getr regs 27); Cells.C8 (getr regs 26); Cells.C8 (getr regs 25);
     Cells.C8 (getr regs 24); Cells.C8 (getr regs 23); Cells.C8 (getr regs 22); Cells.C8 (getr regs 21);
     Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18); Cells.C8 (getr regs 9);
     Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)]).
  { change (bv_unsigned (getr regs6 2)) with (spZ regs6). rewrite S6, <- SEGS.
    apply (cr_cells_norm_cf HIL); [| exact I4 | lia]. unfold cr_frame_cf in FR. rewrite SEGS. exact FR. }
  assert (AP : crt_apart P Q O pcm audio nch ns (bv_unsigned (getr regs6 2))).
  { change (bv_unsigned (getr regs6 2)) with (spZ regs6). rewrite S6. unfold crt_apart.
    repeat split; lia. }
  eapply (crt_runN_cf B SEGS regs6 _ m6 md3); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G8, G10, G18, G19, G20, G21, G22.
    eapply (crt_seg4 ENC BCMP) with (audio := audio); first [eassumption | exact (mem_inv_normalize rsegs m6) | exact FRM | lia]. }
  { intros ms (t0' & t1' & t2' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s8' & s9' & s10' & s11' & t3' & t4' &
      t5' & t6' & F' & fc' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (t0' & t1' & t2' & s1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s8' & s9' & s10' & s11' &
    t3' & t4' & t5' & t6' & F' & fc' & m' & -> & Hfc & MU & WM & _) Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  change (bv_unsigned (getr regs6 2)) with (spZ regs6) in MU. rewrite S6 in MU.
  set (W := [(spZ regs - 112 - 112, spZ regs - 112); (P, P + 4 * nch * ns); (Q, Q + 8 * nch);
    (O, O + 3 * nch * ns)]) in MU.
  pose proof (mem_rel_normalize rsegs m6 Hro') as HR6.
  pose proof (munch_rel rsegs _ m6 _ (ms_mem ms) m' HR6 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m6 _ (ms_mem ms) m' HR6 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m6 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m6 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (crt_pres_cf B m6 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (cr_not_out4 _ _ _ _ _ _ _ _ _ Hout) as [Hs|[Hs|[Hs|Hs]]].
    - apply (crt_fs_high_cf B HIL). lia.
    - apply (crt_fs_none_cf B SEGS). destruct (HPi (bv_unsigned x - P) ltac:(lia)) as (_ & Hn & _).
      replace (P + (bv_unsigned x - P)) with (bv_unsigned x) in Hn by ring. exact Hn.
    - apply (crt_fs_none_cf B SEGS). destruct (HQi (bv_unsigned x - Q) ltac:(lia)) as (_ & Hn & _).
      replace (Q + (bv_unsigned x - Q)) with (bv_unsigned x) in Hn by ring. exact Hn.
    - apply (crt_fs_none_cf B SEGS). destruct (HOi (bv_unsigned x - O) ltac:(lia)) as (_ & Hn & _).
      replace (O + (bv_unsigned x - O)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CRT_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L3 A3 x /\
      forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. destruct (cr_not_out4 _ _ _ _ _ _ _ _ _ Hout) as [Hs|[Hs|[Hs|Hs]]].
    - left. lia.
    - right. destruct (HPi (x - P) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (P + (x - P)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p n i Hp Hi E. destruct (Hold _ (crt_ub L A p n Hp)) as (Y1 & _ & _).
      pose proof (cr_pw _ _ _ _ _ _ PWe Y1). lia.
    - right. destruct (HQi (x - Q) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (Q + (x - Q)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p n i Hp Hi E. destruct (Hold _ (crt_ub L A p n Hp)) as (_ & Y2 & _).
      pose proof (cr_pw _ _ _ _ _ _ PWg Y2). lia.
    - right. destruct (HOi (x - O) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (O + (x - O)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p n i Hp Hi E. destruct (Hold _ (crt_ub L A p n Hp)) as (_ & _ & Y3).
      pose proof (cr_pw _ _ _ _ _ _ PW3 Y3). lia. }
  pose proof (cr_inv_A_cf L3 A3 m6 md3 (ms_mem ms) W I MU7 WM7 PRES HWW RO7) as I7.
  assert (FR7 : cr_frame_cf (ms_mem ms)).
  { unfold cr_frame_cf in FR |- *. rewrite <- SEGS in FR |- *.
    apply (crt_cells_keep_cf B m6 (ms_mem ms) _ _ FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 112 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  destruct GK as (K3 & K4).
  apply (cr_ph4_cf (mkFP F' fc') L3 A3 regs7 (ms_mem ms) md3 P Q O c1 c2 e1 e2 g1 g2 Hfc I7 Hinit Hb3 Hg He Hb0 Hres);
    [rewrite Hg7; reflexivity | rewrite Hg7; exact G2 | rewrite Hg7; reflexivity | rewrite Hg7; reflexivity
    | rewrite Hg7; reflexivity | | exact FR7].
  split; rewrite Hg7; first [exact K3 | exact K4].
Qed.

Lemma cr_ph3c_cf : forall L2 A2 regs4 m4 md2 P Q c1 c2 e1 e2,
  cr_inv_cf L2 A2 m4 md2 -> st_init_done A2 = true ->
  blocks L2 A2 = e1 ++ (Q, 8 * nch) :: e2 -> e1 ++ e2 = c1 ++ (P, 4 * (nch * ns)) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A2 (sb_malloc (sb_malloc b (4 * (nch * ns))) (8 * nch)) ->
  getr regs4 2 = Z_to_bv 64 (spZ regs - 112) -> getr regs4 8 = Z_to_bv 64 P ->
  getr regs4 10 = Z_to_bv 64 Q -> getr regs4 18 = Z_to_bv 64 (3 * (nch * ns)) ->
  getr regs4 20 = Z_to_bv 64 ns -> getr regs4 21 = Z_to_bv 64 nch -> getr regs4 22 = Z_to_bv 64 pcm ->
  getr regs4 23 = Z_to_bv 64 (nch * ns) -> cr_keep_cf regs4 -> cr_frame_cf m4 ->
  SRcf B (mkCfg (mkst regs4 (Z_to_bv 64 0x1354c) m4 (seg_rom (ms_segs B))) md2) cr_final_cf.
Proof.
  intros L2 A2 regs4 m4 md2 P Q c1 c2 e1 e2 I Hinit Hb2 He Hb0 Hres G2 G8 G10 G18 G20 G21 G22 G23 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hk : 0 < nch * ns) by nia.
  pose proof I as ((M2 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L2 A2 m4 md2 M2) as [Hh Hlz].
  eapply (crt_runA_cf B SEGS regs4 _ m4 md2); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite G23. apply crt_seg3. lia. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs5 -> Hg5. cbn [MState.MS ms_pc_val ms_mem].
  assert (G5a : getr regs5 1 = Z_to_bv 64 0x13564) by (rewrite Hg5; reflexivity).
  assert (G5b : getr regs5 2 = Z_to_bv 64 (spZ regs - 112)) by (rewrite Hg5; exact G2).
  assert (G5c : getr regs5 10 = Z_to_bv 64 (3 * (nch * ns))) by (rewrite Hg5; exact G18).
  assert (G5d : getr regs5 11 = Z_to_bv 64 1) by (rewrite Hg5; reflexivity).
  assert (G5e : getr regs5 8 = Z_to_bv 64 P) by (rewrite Hg5; exact G8).
  assert (G5g : getr regs5 18 = Z_to_bv 64 (3 * (nch * ns))) by (rewrite Hg5; exact G18).
  assert (G5h : getr regs5 19 = Z_to_bv 64 Q) by (rewrite Hg5; exact G10).
  assert (G5i : getr regs5 20 = Z_to_bv 64 ns) by (rewrite Hg5; exact G20).
  assert (G5j : getr regs5 21 = Z_to_bv 64 nch) by (rewrite Hg5; exact G21).
  assert (G5k : getr regs5 22 = Z_to_bv 64 pcm) by (rewrite Hg5; exact G22).
  assert (K5 : cr_keep_cf regs5).
  { destruct GK as (K3 & K4). split; rewrite Hg5; first [exact K3 | exact K4]. }
  assert (S5 : spZ regs5 = spZ regs - 112) by (unfold spZ at 1; rewrite G5b; apply MState.unsigned_lit; lia).
  assert (Hpre5 : call_pre_k B (aa_MR API) CALLOC_STACK L2 A2 regs5 m4 md2).
  { apply (cr_pre_cf L2 A2 m4 md2 regs5 112 CALLOC_STACK I); [lia | lia | unfold CALLOC_STACK, ALLOC_STACK; lia
      | rewrite HK0; unfold CALLOC_STACK, ALLOC_STACK; lia
      | rewrite S5; replace (spZ regs - 112) with (spZ regs + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj2 K5) | rewrite G5a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  assert (Hroom : room_ag (sb_malloc (sb_malloc b (4 * (nch * ns))) (8 * nch)) (3 * (nch * ns) * 1)).
  { apply room_ag_gen; cbn [sb_malloc sb_live sb_cap sb_bytes]; lia. }
  unfold CRT_CALLOC.
  eapply (SRcf_bind B).
  { apply (CALLOC L2 A2 regs5 m4 md2 (3 * (nch * ns)) 1 (sb_malloc (sb_malloc b (4 * (nch * ns))) (8 * nch))
      Hpre5 I4 G5c G5d); [lia | lia | lia | exact CALPC | exact Hres | exact Hroom]. }
  intros c' ((L3 & A3 & regs6 & m6 & md3 & res & -> & Hpost & G6 & _ & _ & _ & (d1 & d2 & Hb3 & Hb2') & _ & Hro3 &
    Hgk3 & HU3 & Hinit3 & Hlen3 & Hres3) & _).
  rewrite Z.mul_1_r in Hb3, Hres3.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp6 & _).
  assert (I3' : cr_inv_cf L3 A3 m6 md3).
  { apply (cr_inv_call_cf L2 A2 m4 md2 regs5 CALLOC_STACK _ L3 A3 regs6 m6 md3 I Hpost);
      [rewrite S5, HK0; unfold CALLOC_STACK, ALLOC_STACK; lia | lia | intros a [] | exact Hlen3
      | intros q k Hq; exact (HU3 q k (I3 q k Hq)) | exact Hro3 | exact Hgk3]. }
  assert (FR3 : cr_frame_cf m6).
  { apply (cr_frame_call_cf L2 A2 m4 md2 regs5 CALLOC_STACK _ L3 A3 regs6 m6 md3 I FR Hpost); [lia | intros a []]. }
  rewrite G5a.
  apply (cr_ph3_cf L3 A3 regs6 m6 md3 P Q res c1 c2 e1 e2 d1 d2 I3' Hinit3 Hb3).
  - rewrite <- Hb2'. exact Hb2.
  - exact He.
  - exact Hb0.
  - exact Hres3.
  - transitivity (getr regs5 2); [apply (Hp6 2); unfold callee_saved; lia | exact G5b].
  - transitivity (getr regs5 8); [apply (Hp6 8); unfold callee_saved; lia | exact G5e].
  - exact G6.
  - transitivity (getr regs5 18); [apply (Hp6 18); unfold callee_saved; lia | exact G5g].
  - transitivity (getr regs5 19); [apply (Hp6 19); unfold callee_saved; lia | exact G5h].
  - transitivity (getr regs5 20); [apply (Hp6 20); unfold callee_saved; lia | exact G5i].
  - transitivity (getr regs5 21); [apply (Hp6 21); unfold callee_saved; lia | exact G5j].
  - transitivity (getr regs5 22); [apply (Hp6 22); unfold callee_saved; lia | exact G5k].
  - exact (cr_keep_pres_cf regs5 regs6 K5 Hp6).
  - exact FR3.
Qed.

Lemma cr_ph2m_cf : forall L1 A1 regs2 m2 md1 P c1 c2,
  cr_inv_cf L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (P, 4 * (nch * ns)) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc b (4 * (nch * ns))) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 112) -> getr regs2 10 = Z_to_bv 64 P ->
  getr regs2 18 = Z_to_bv 64 (3 * (nch * ns)) -> getr regs2 20 = Z_to_bv 64 ns -> getr regs2 21 = Z_to_bv 64 nch ->
  getr regs2 22 = Z_to_bv 64 pcm -> getr regs2 23 = Z_to_bv 64 (nch * ns) -> cr_keep_cf regs2 -> cr_frame_cf m2 ->
  SRcf B (mkCfg (mkst regs2 (Z_to_bv 64 0x13540) m2 (seg_rom (ms_segs B))) md1) cr_final_cf.
Proof.
  intros L1 A1 regs2 m2 md1 P c1 c2 I Hinit Hb1 Hb0 Hres G2 G10 G18 G20 G21 G22 G23 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hk : 0 < nch * ns) by nia.
  pose proof I as ((M1 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  eapply (crt_runA_cf B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite G21. apply crt_seg2. lia. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs3 -> Hg3. cbn [MState.MS ms_pc_val ms_mem].
  assert (G3a : getr regs3 1 = Z_to_bv 64 0x1354c) by (rewrite Hg3; reflexivity).
  assert (G3b : getr regs3 2 = Z_to_bv 64 (spZ regs - 112)) by (rewrite Hg3; exact G2).
  assert (G3c : getr regs3 10 = Z_to_bv 64 (8 * nch)) by (rewrite Hg3; reflexivity).
  assert (G3d : getr regs3 8 = Z_to_bv 64 P) by (rewrite Hg3; exact G10).
  assert (G3f : getr regs3 18 = Z_to_bv 64 (3 * (nch * ns))) by (rewrite Hg3; exact G18).
  assert (G3g : getr regs3 20 = Z_to_bv 64 ns) by (rewrite Hg3; exact G20).
  assert (G3h : getr regs3 21 = Z_to_bv 64 nch) by (rewrite Hg3; reflexivity).
  assert (G3i : getr regs3 22 = Z_to_bv 64 pcm) by (rewrite Hg3; exact G22).
  assert (G3j : getr regs3 23 = Z_to_bv 64 (nch * ns)) by (rewrite Hg3; exact G23).
  assert (K3 : cr_keep_cf regs3).
  { destruct GK as (K3 & K4). split; rewrite Hg3; first [exact K3 | exact K4]. }
  assert (S3 : spZ regs3 = spZ regs - 112) by (unfold spZ at 1; rewrite G3b; apply MState.unsigned_lit; lia).
  assert (Hpre3 : call_pre B (aa_MR API) L1 A1 regs3 m2 md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs3 m2 md1)).
    apply (cr_pre_cf L1 A1 m2 md1 regs3 112 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S3; replace (spZ regs - 112) with (spZ regs + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj2 K3) | rewrite G3a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  assert (Hroom : room_ag (sb_malloc b (4 * (nch * ns))) (8 * nch)).
  { apply room_ag_gen; cbn [sb_malloc sb_live sb_cap sb_bytes]; lia. }
  replace (Z_to_bv 64 CRT_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply (SRcf_bind B).
  { exact (MALLOC L1 A1 regs3 m2 md1 (8 * nch) (sb_malloc b (4 * (nch * ns))) Hpre3 I4 G3c Hres Hroom). }
  intros c' (L2 & A2 & regs4 & m4 & md2 & res & -> & Hpost & G4 & _ & _ & _ & (d1 & d2 & Hb2 & Hb1') & _ & Hro2 &
    Hgk2 & HU2 & Hinit2 & Hlen2 & Hres2).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp4 & _).
  assert (I2' : cr_inv_cf L2 A2 m4 md2).
  { apply (cr_inv_call_cf L1 A1 m2 md1 regs3 ALLOC_STACK _ L2 A2 regs4 m4 md2 I Hpost);
      [rewrite S3, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen2
      | intros q k Hq; exact (HU2 q k (I3 q k Hq)) | exact Hro2 | exact Hgk2]. }
  assert (FR2 : cr_frame_cf m4).
  { apply (cr_frame_call_cf L1 A1 m2 md1 regs3 ALLOC_STACK _ L2 A2 regs4 m4 md2 I FR Hpost); [lia | intros a []]. }
  rewrite G3a.
  apply (cr_ph3c_cf L2 A2 regs4 m4 md2 P res c1 c2 d1 d2 I2' Hinit2 Hb2).
  - rewrite <- Hb1'. exact Hb1.
  - exact Hb0.
  - exact Hres2.
  - transitivity (getr regs3 2); [apply (Hp4 2); unfold callee_saved; lia | exact G3b].
  - transitivity (getr regs3 8); [apply (Hp4 8); unfold callee_saved; lia | exact G3d].
  - exact G4.
  - transitivity (getr regs3 18); [apply (Hp4 18); unfold callee_saved; lia | exact G3f].
  - transitivity (getr regs3 20); [apply (Hp4 20); unfold callee_saved; lia | exact G3g].
  - transitivity (getr regs3 21); [apply (Hp4 21); unfold callee_saved; lia | exact G3h].
  - transitivity (getr regs3 22); [apply (Hp4 22); unfold callee_saved; lia | exact G3i].
  - transitivity (getr regs3 23); [apply (Hp4 23); unfold callee_saved; lia | exact G3j].
  - exact (cr_keep_pres_cf regs3 regs4 K3 Hp4).
  - exact FR2.
Qed.

Lemma cr_entry_cf :
  SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom (ms_segs B))) md) cr_final_cf.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hk : 0 < nch * ns) by nia.
  pose proof (crt_img_low_cf B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (I0 : cr_inv_cf L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p n Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs mem (spZ regs - CRT_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CRT_STACK L A regs mem md PRE ltac:(lia))).
  eapply (crt_runA_cf B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite R10, R11, R12, R13. eapply crt_seg1; [exact ST | unfold spZ; lia | lia | lia | lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x13540) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 112)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (4 * (nch * ns))) by (rewrite Hg1; reflexivity).
  assert (G1e : getr regs1 18 = Z_to_bv 64 (3 * (nch * ns))) by (rewrite Hg1; reflexivity).
  assert (G1f : getr regs1 20 = Z_to_bv 64 ns) by (rewrite Hg1; reflexivity).
  assert (G1g : getr regs1 21 = Z_to_bv 64 nch) by (rewrite Hg1; reflexivity).
  assert (G1h : getr regs1 22 = Z_to_bv 64 pcm) by (rewrite Hg1; reflexivity).
  assert (G1i : getr regs1 23 = Z_to_bv 64 (nch * ns)) by (rewrite Hg1; reflexivity).
  assert (K1 : cr_keep_cf regs1) by (split; rewrite Hg1; reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 112) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 112, spZ regs)] x -> spZ regs - 112 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (crt_ro_munch_cf B _ mem m1 RO MU). intros a Ha Ho. apply (crt_fs_high_cf B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : cr_inv_cf L A m1 md).
  { apply (cr_inv_A_cf L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 112, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (crt_pres_cf B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (crt_fs_high_cf B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (FR1' : cr_frame_cf m1) by exact FR1.
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CRT_STACK 112 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 112, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 112) with (spZ regs + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (Hroom : room_ag b (4 * (nch * ns))) by (apply room_ag_gen; lia).
  replace (Z_to_bv 64 CRT_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply (SRcf_bind B).
  { exact (MALLOC L A regs1 m1 md (4 * (nch * ns)) b Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : cr_inv_cf L1 A1 m2 md1).
  { apply (cr_inv_call_cf L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : cr_frame_cf m2).
  { apply (cr_frame_call_cf L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1' Hpost); [lia | intros a []]. }
  rewrite G1a.
  apply (cr_ph2m_cf L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 Hres1).
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - exact G2.
  - transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1e].
  - transitivity (getr regs1 20); [apply (Hp2 20); unfold callee_saved; lia | exact G1f].
  - transitivity (getr regs1 21); [apply (Hp2 21); unfold callee_saved; lia | exact G1g].
  - transitivity (getr regs1 22); [apply (Hp2 22); unfold callee_saved; lia | exact G1h].
  - transitivity (getr regs1 23); [apply (Hp2 23); unfold callee_saved; lia | exact G1i].
  - exact (cr_keep_pres_cf regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem check_round_trip_holds_cf : check_round_trip_contract_cf B API.
Proof.
  intros L A regs mem md audio pcm nch ns b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18.
  eapply cr_entry_cf; eassumption.
Qed.
End CRT.
