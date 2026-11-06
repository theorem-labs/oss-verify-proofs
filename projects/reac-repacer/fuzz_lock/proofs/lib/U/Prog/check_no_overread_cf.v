(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/check_no_overread_cg.v, with its module paths, module names, addresses and numbers changed; 437 of its 666 lines of code are new or changed and 302 lines of the source are left out. *)
(* Crash-free walk of fuzz_lock's harness function check_no_overread (fuzz_lock.c:120-141) in fuzz_lock.ubsan,
   0x12d2c, against check_no_overread_contract_cf (lib/U/Prog/check_no_overread_ccf.v), in the form of
   libreac/fuzz_decode's lib/U/Prog/check_round_trip_cg.v: the walk of lib/U/Prog/check_no_overread.v with SRcf in
   place of SR (crt_runA_cf / crt_runN_cf / SRcf_bind / SRcf_ret, lib/U/Prog/cno_glue_cf.v and lib/U/AgreeLift.v)
   and the crash-free allocator contracts (malloc_contract_ag, free_contract_cf). The Exec.evt walks
   (lib/U/Prog/cno_segs.v) are the same. Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i YL01 YL00 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import memcpy_c rp_lock_lookup_c
  check_no_overread_c check_no_overread_ccf cno_glue cno_glue_cf cno_segs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cn_pw_in : forall (l : list (Z * Z)) x y, pairwise ranges_disjoint l -> In x l -> In y l -> x <> y ->
  ranges_disjoint x y.
Proof.
  induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|]. cbn in H. destruct H as [Hz H].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - congruence.
  - exact (Hz y Hy).
  - pose proof (Hz x Hx) as D. unfold ranges_disjoint in *. lia.
  - exact (IH x y H Hx Hy Hne).
Qed.

Lemma cn_not_out3 : forall a1 b1 a2 b2 a3 b3 x,
  ~ Frame.outside [(a1, b1); (a2, b2); (a3, b3)] x -> (a1 <= x < b1) \/ (a2 <= x < b2) \/ (a3 <= x < b3).
Proof. intros a1 b1 a2 b2 a3 b3 x H. cbn [Frame.outside] in H. lia. Qed.

Section CNO.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = CNO_MALLOC.
Hypothesis FREEPC : ms_free B = CNO_FREE.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract_ag B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis MC : memcpy_contract.
Hypothesis RP : rp_lock_lookup_contract.

Lemma cn_blk : forall Lk Ak mk mdk p k, aa_MR API Lk Ak mk mdk -> In (p, k) (blocks Lk Ak) ->
  4096 <= p /\ p + k <= alloc_ceiling /\ p mod 16 = 0 /\
  forall i, 0 <= i < k -> present mk (p + i) /\ ~ in_img B (p + i) /\ ~ owned B Lk Ak (p + i).
Proof.
  intros Lk Ak mk mdk p k HM Hin.
  destruct (crt_bu Lk Ak p k Hin) as (q & Hq & <-).
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q k HM Hq) as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  split; [exact (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ q k HM Hq)|].
  intros i Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ q k i HM Hq Hi) as (Hpr & _ & _ & Hno).
  split; [exact Hpr|]. split; [exact (ax_blocks_img AX Lk Ak mk mdk q k i HM Hq Hi) | exact Hno].
Qed.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (t n pa rate : Z) (T P SL : list byte) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CNO_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 t.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis R12 : getr regs 12 = Z_to_bv 64 pa.
Hypothesis R13 : getr regs 13 = Z_to_bv 64 rate.
Hypothesis HN : 0 <= n < 2 ^ 26.
Hypothesis HT : Z.of_nat (length T) = n.
Hypothesis Ht : 0 < t < 2 ^ 63.
Hypothesis IBT : in_block L A t n.
Hypothesis BDT : blk_data B mem t T.
Hypothesis HPA : spZ regs <= pa.
Hypothesis H8 : pa mod 8 = 0.
Hypothesis HPA2 : pa + 16 <= 2 ^ 63.
Hypothesis HPL : length (P ++ Z_to_bv 8 0 :: SL) = 16%nat.
Hypothesis NP : ~ In (Z_to_bv 8 0) P.
Hypothesis BDP : blk_data B mem pa (P ++ Z_to_bv 8 0 :: SL).
Hypothesis HR : 0 <= rate < 2 ^ 64.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : (sb_live b + 2 <= sb_cap b <= CAP_AG /\ 128 <= sb_cap b) /\ 0 <= sb_bytes b /\
  sb_bytes b + 2 * (n + 1) <= 2 ^ 29.

Lemma cn_sp0 : 0 <= spZ regs.
Proof.
  unfold spZ. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  lia.
Qed.

Definition cn_inv (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  kb_mid B API CNO_STACK (spZ regs) L A mem md (fun _ => False) L' A' m' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')) /\
  ro_agree (ms_segs B) m' /\ guard_kept B mem m'.

(* gp, tp and s6-s11, which check_no_overread leaves alone *)
Definition cn_keep (r : bvmap 5 word) : Prop :=
  getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\
  getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

(* the frame of 64 bytes: s5, s4, s3, s2, s1, s0, ra above 8 bytes of padding *)
Definition cn_frame (m' : word -> option byte) : Prop :=
  exists junk, Step.rw_cells rsegs m' (spZ regs - 64) [Cells.CB 8 junk; Cells.C8 (getr regs 21);
    Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18); Cells.C8 (getr regs 9);
    Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)].

Definition cn_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CNO_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    st_init_done A' = true.

Lemma cn_pre : forall Lk Ak mk mdk regsk f K1,
  cn_inv Lk Ak mk mdk -> spZ regsk = spZ regs - f -> 0 <= f -> 0 <= K1 -> f + K1 <= CNO_STACK ->
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

Lemma cn_inv_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cn_inv Lk Ak mk mdk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regs - CNO_STACK <= spZ regsk - K2 -> spZ regsk <= spZ regs ->
  (forall a, E2 a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (length (st_regions Ak) <= length (st_regions A2))%nat ->
  (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A2)) ->
  ro_agree (ms_segs B) m2 -> guard_kept B mk m2 ->
  cn_inv L2 A2 m2 md2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 (I1 & I2 & I3 & I4 & I5) Hpost H1 H2 HE HL HU Hro Hg.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost) as [Hmid _].
  split.
  { apply (crt_drop B API _ _ _ _ _ _ (fun a => False \/ E2 a)).
    - eapply (crt_seq B API AX CT); [exact HM | exact I1 | exact Hmid | lia | lia | lia | lia | | exact I2 | exact I3].
      intros a Ha _ He. destruct (HE a He) as [Ha' _]. lia.
    - intros a [[]|He]. exact (HE a He). }
  split; [lia|]. split; [exact HU|]. split; [exact Hro|].
  intros i Hi. rewrite (Hg i Hi). exact (I5 i Hi).
Qed.

Lemma cn_inv_A : forall Lk Ak mk mdk mk' W,
  cn_inv Lk Ak mk mdk ->
  Frame.munch W mk mk' -> Frame.wmono (ms_segs B) mk mk' -> (forall x, mk x <> None -> mk' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CNO_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lk Ak x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)) ->
  ro_agree (ms_segs B) mk' ->
  cn_inv Lk Ak mk' mdk.
Proof.
  intros Lk Ak mk mdk mk' W (I1 & I2 & I3 & I4 & I5) Hm Hw Hp HW Hro.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (crt_img_low B SEGS) as HIL.
  pose proof I1 as (M1 & _).
  split.
  { apply (crt_drop B API _ _ _ _ _ _
      (fun x => False \/ (0 <= x < 2 ^ 64 /\ ~ Frame.outside W x /\ ~ (spZ regs - CNO_STACK <= x < spZ regs)))).
    - apply (kb_mid_tail B API HIL _ _ _ _ _ _ _ Lk Ak mk mdk mk' W); [exact I1 | exact Hm | exact Hw | exact Hp | | |].
      + intros x Hx Hs He. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. apply He. tauto.
      + intros x Hx Ho. destruct (kb_outside_dec W x) as [Hout|Hout]; [exact Hout|]. exfalso.
        destruct (HW x ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
      + intros p k i Hin Hin' Hi. destruct (kb_outside_dec W (ptr_addr L p + i)) as [Hout|Hout]; [exact Hout|].
        exfalso. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HM Hin) as [Hr1 Hr2].
        destruct (HW (ptr_addr L p + i) ltac:(lia) Hout) as [Hs | (_ & _ & _ & H4)];
          [lia | exact (H4 p k i Hin Hi eq_refl)].
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

Lemma cn_free_keep : forall Lk Ak mk mdk p k,
  cn_inv Lk Ak mk mdk -> In (p, k) (user_blocks Ak) -> 0 < k ->
  (forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr Lk p, k) y) ->
  forall q k', In (q, k') (user_blocks A) -> q <> p.
Proof.
  intros Lk Ak mk mdk p k ((M1 & W1 & _ & _ & P1 & _) & _ & I3 & _) Hp Hk HD q k' Hq Eq. subst q.
  pose proof (I3 p k' Hq) as Hpk.
  pose proof (user_block_ptrs_NoDup Ak W1) as ND.
  pose proof (crt_fst_unique _ p k' k ND Hpk Hp) as Ek. subst k'.
  pose proof (HD _ (crt_ub L A p k Hq)) as D.
  rewrite (P1 p k Hq Hpk) in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma cn_frame_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cn_inv Lk Ak mk mdk -> cn_frame mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 64 -> (forall a, E2 a -> a < alloc_ceiling) ->
  cn_frame m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 ((M1 & _) & _) (junk & FR) Hpost Hsp HE.
  pose proof Hpost as (M2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  exists junk. rewrite <- SEGS in FR |- *.
  apply (crt_cells_mb B mk m2 _ _ FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 64 in Hi.
  assert (HK0 : CNO_STACK = 8256) by reflexivity.
  assert (Hr : alloc_ceiling <= spZ regs - 64 + i < 2 ^ 64) by lia.
  destruct (Hfr (spZ regs - 64 + i)) as [E W].
  - left. exact Hr.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - unfold scratch_k. lia.
  - intros He. pose proof (HE _ He). lia.
  - split; [exact E | intros Hw; apply W; exact Hw].
Qed.

Lemma cn_inv_kept : forall Lk Ak mk mdk, cn_inv Lk Ak mk mdk -> blocks_kept B L A mem mk (fun _ => False).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & K1 & _) & _ & I3 & _) a k i Hin _ Hi.
  destruct (crt_bu L A a k Hin) as (p & Hp & <-). exact (K1 p k i Hp (I3 p k Hp) Hi).
Qed.

Lemma cn_keep_pres : forall r r', cn_keep r -> regs_preserved r r' -> cn_keep r'.
Proof.
  intros r r' (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27) Hp.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - transitivity (getr r 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
  - transitivity (getr r 22); [apply (Hp 22); unfold callee_saved; lia | exact K22].
  - transitivity (getr r 23); [apply (Hp 23); unfold callee_saved; lia | exact K23].
  - transitivity (getr r 24); [apply (Hp 24); unfold callee_saved; lia | exact K24].
  - transitivity (getr r 25); [apply (Hp 25); unfold callee_saved; lia | exact K25].
  - transitivity (getr r 26); [apply (Hp 26); unfold callee_saved; lia | exact K26].
  - transitivity (getr r 27); [apply (Hp 27); unfold callee_saved; lia | exact K27].
Qed.

Lemma cn_heap_E : forall Lk Ak mk mdk p k, aa_MR API Lk Ak mk mdk -> In (p, k) (user_blocks Ak) ->
  forall a, ptr_addr Lk p <= a < ptr_addr Lk p + k -> a < alloc_ceiling /\ ~ in_img B a.
Proof.
  intros Lk Ak mk mdk p k HMk Hp a Ha.
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p _ HMk Hp) as [Hr1 Hr2].
  split; [lia|]. replace a with (ptr_addr Lk p + (a - ptr_addr Lk p)) by lia.
  exact (ax_blocks_img AX Lk Ak mk mdk p k (a - ptr_addr Lk p) HMk Hp ltac:(lia)).
Qed.

(* 0x12e04: the epilogue, free(b) as a tail call, and the return *)
Lemma cn_ph5 : forall (fx7 : FPState) L5 A5 regs10 m10 md5 xb,
  frm_zero (@fp_csr fx7) ->
  cn_inv L5 A5 m10 md5 -> st_init_done A5 = true ->
  In (xb, n + 1) (blocks L5 A5) -> remove cno_zz_dec (xb, n + 1) (blocks L5 A5) = blocks L A ->
  res_ok_slots A5 (sb_malloc b (n + 1)) ->
  getr regs10 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs10 19 = Z_to_bv 64 xb -> cn_keep regs10 ->
  cn_frame m10 ->
  SRcf B (mkCfg (@mkst fx7 regs10 (Z_to_bv 64 0x12e04) m10 (seg_rom (ms_segs B))) md5) cn_final.
Proof.
  intros fx7 L5 A5 regs10 m10 md5 xb Hfrm I Hinit Hin5 Hrm Hres G2 G19 GK (junk & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8256) by reflexivity.
  pose proof cn_sp0 as Hsp0.
  pose proof I as ((M5 & W5 & B5 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L5 A5 m10 md5 M5) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs10 2) = spZ regs - 64) by (rewrite G2; apply MState.unsigned_lit; lia).
  eapply (crt_runA_cf (fx := fx7) B SEGS regs10 _ m10 md5); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply cn_seg4. rewrite USP. exact FR. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs11 -> Hg11. cbn [MState.MS ms_pc_val ms_mem].
  assert (G11a : getr regs11 1 = getr regs 1) by (rewrite Hg11; reflexivity).
  assert (G11b : getr regs11 2 = Z_to_bv 64 (bv_unsigned (getr regs10 2) + 64)) by (rewrite Hg11; reflexivity).
  rewrite USP in G11b. replace (spZ regs - 64 + 64) with (spZ regs) in G11b by lia.
  assert (G11c : getr regs11 4 = getr regs 4) by (rewrite Hg11; exact (proj1 (proj2 GK))).
  assert (G11d : getr regs11 10 = Z_to_bv 64 xb) by (rewrite Hg11; exact G19).
  assert (S11 : spZ regs11 = spZ regs) by (unfold spZ at 1; rewrite G11b; apply MState.unsigned_lit; lia).
  assert (P11 : regs_preserved regs regs11).
  { destruct GK as (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27).
    assert (Hs : getr regs11 2 = getr regs 2) by (rewrite G11b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg11; first [reflexivity | exact K3 | exact K4 | exact K22 | exact K23 | exact K24
        | exact K25 | exact K26 | exact K27]]. }
  destruct (crt_bu L5 A5 xb _ Hin5) as (p & Hp & Ep).
  assert (Hpre11 : call_pre B (aa_MR API) L5 A5 regs11 m10 md5).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L5 A5 regs11 m10 md5)).
    apply (cn_pre L5 A5 m10 md5 regs11 0 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia | rewrite S11; exact H16 | exact G11c | rewrite G11a; exact Hra
      | exact Hinit]. }
  replace (Z_to_bv 64 CNO_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L5 A5 regs11 m10 md5 p (n + 1) (sb_malloc b (n + 1)) Hpre11 I4 Hp).
    - rewrite G11d, Ep. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  rewrite Ep in Hd1.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M5) as PW5.
  assert (PW5' : pairwise ranges_disjoint (d1 ++ (xb, n + 1) :: d2)) by (rewrite <- Hd1; exact PW5).
  assert (ND5 : ~ In (xb, n + 1) (d1 ++ d2)) by (apply (crt_notin d1 d2 _ PW5'); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, <- Hrm, Hd1. symmetry. exact (cno_rm_mid d1 d2 _ ND5). }
  assert (HD5 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L5 p, n + 1) y).
  { intros y Hy. rewrite Ep. rewrite <- Hrm in Hy. apply in_remove in Hy as [Hy Hne].
    exact (cn_pw_in _ _ _ PW5 Hin5 Hy (not_eq_sym Hne)). }
  assert (HU6 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A6)).
  { intros q k Hq. apply Hub6; [exact (I3 q k Hq) | exact (cn_free_keep L5 A5 m10 md5 p _ I Hp ltac:(lia) HD5 q k Hq)]. }
  assert (I6 : cn_inv L6 A6 m12 md6).
  { apply (cn_inv_call L5 A5 m10 md5 regs11 ALLOC_STACK _ L6 A6 regs12 m12 md6 I Hpost);
      [rewrite S11, HK0; unfold ALLOC_STACK; lia | lia | exact (cn_heap_E L5 A5 m10 md5 p _ M5 Hp) | exact Hlen6
      | exact HU6 | exact Hro6 | exact Hgk6]. }
  apply (SRcf_ret B). exists fx7, L6, A6, regs12, m12, md6.
  split; [rewrite G11a; reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    exact (kb_preserved_trans _ _ _ P11 (proj2 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost))). }
  split; [exact Hb6|].
  split; [exact (cn_inv_kept _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | exact (Hinit6 Hinit)].
Qed.

(* the first free: free(a) *)
Lemma cn_ph4 : forall (fx7 : FPState) L3 A3 regs7 m7 md3 xa xb,
  frm_zero (@fp_csr fx7) ->
  cn_inv L3 A3 m7 md3 -> st_init_done A3 = true ->
  In (xa, n + 1) (blocks L3 A3) -> In (xb, n + 1) (blocks L3 A3) -> xa <> xb ->
  remove cno_zz_dec (xb, n + 1) (remove cno_zz_dec (xa, n + 1) (blocks L3 A3)) = blocks L A ->
  res_ok_slots A3 (sb_malloc (sb_malloc b (n + 1)) (n + 1)) ->
  getr regs7 1 = Z_to_bv 64 0x12e04 -> getr regs7 2 = Z_to_bv 64 (spZ regs - 64) ->
  getr regs7 10 = Z_to_bv 64 xa -> getr regs7 19 = Z_to_bv 64 xb ->
  cn_keep regs7 -> cn_frame m7 ->
  SRcf B (mkCfg (@mkst fx7 regs7 (Z_to_bv 64 CNO_FREE) m7 (seg_rom (ms_segs B))) md3) cn_final.
Proof.
  intros fx7 L3 A3 regs7 m7 md3 xa xb Hfrm I Hinit Hina Hinb Hab Hrm Hres G1 G2 G10 G19 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8256) by reflexivity.
  pose proof cn_sp0 as Hsp0.
  pose proof I as ((M3 & W3 & B3 & _) & I2 & I3 & I4 & I5).
  assert (S7 : spZ regs7 = spZ regs - 64) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  destruct (crt_bu L3 A3 xa _ Hina) as (o & Ho & Eo).
  assert (Hpre7 : call_pre B (aa_MR API) L3 A3 regs7 m7 md3).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L3 A3 regs7 m7 md3)).
    apply (cn_pre L3 A3 m7 md3 regs7 64 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S7; replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 GK)) | rewrite G1; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  replace (Z_to_bv 64 CNO_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply (SRcf_bind B).
  { apply (FREE fx7 L3 A3 regs7 m7 md3 o (n + 1) (sb_malloc (sb_malloc b (n + 1)) (n + 1)) Hpre7 I4 Ho).
    - rewrite G10, Eo. reflexivity.
    - exact Hres. }
  intros c' (L4 & A4 & regs8 & m8 & md4 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro4 & Hgk4 & Hub4 &
    Hinit4 & Hlen4 & Hres4).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp8 & _).
  rewrite Eo in Hd1.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M3) as PW3.
  assert (PW3' : pairwise ranges_disjoint (d1 ++ (xa, n + 1) :: d2)) by (rewrite <- Hd1; exact PW3).
  assert (ND3 : ~ In (xa, n + 1) (d1 ++ d2)) by (apply (crt_notin d1 d2 _ PW3'); cbn; lia).
  assert (Hb4 : blocks L4 A4 = remove cno_zz_dec (xa, n + 1) (blocks L3 A3)).
  { rewrite Hd2, Hd1. symmetry. exact (cno_rm_mid d1 d2 _ ND3). }
  assert (HD3 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L3 o, n + 1) y).
  { intros y Hy. rewrite Eo. rewrite <- Hrm in Hy. apply in_remove in Hy as [Hy _].
    apply in_remove in Hy as [Hy Hne]. exact (cn_pw_in _ _ _ PW3 Hina Hy (not_eq_sym Hne)). }
  assert (HU4 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A4)).
  { intros q' k Hq'. apply Hub4; [exact (I3 q' k Hq') | exact (cn_free_keep L3 A3 m7 md3 o _ I Ho ltac:(lia) HD3 q' k Hq')]. }
  assert (I4' : cn_inv L4 A4 m8 md4).
  { apply (cn_inv_call L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8 md4 I Hpost);
      [rewrite S7, HK0; unfold ALLOC_STACK; lia | lia | exact (cn_heap_E L3 A3 m7 md3 o _ M3 Ho) | exact Hlen4
      | exact HU4 | exact Hro4 | exact Hgk4]. }
  assert (FR4 : cn_frame m8).
  { apply (cn_frame_call L3 A3 m7 md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8 md4 I FR Hpost); [lia |].
    intros a Ha. exact (proj1 (cn_heap_E L3 A3 m7 md3 o _ M3 Ho a Ha)). }
  rewrite G1.
  apply (cn_ph5 fx7 L4 A4 regs8 m8 md4 xb Hfrm I4' (Hinit4 Hinit)).
  - rewrite Hb4. apply in_in_remove; [intros E; injection E as E; congruence | exact Hinb].
  - rewrite Hb4. exact Hrm.
  - rewrite sb_free_malloc in Hres4. exact Hres4.
  - transitivity (getr regs7 2); [apply (Hp8 2); unfold callee_saved; lia | exact G2].
  - transitivity (getr regs7 19); [apply (Hp8 19); unfold callee_saved; lia | exact G19].
  - exact (cn_keep_pres regs7 regs8 GK Hp8).
  - exact FR4.
Qed.

(* 0x12d74: the NULL checks, the two copies, the overflow checks, the stores past their ends and the two lookups *)
Lemma cn_ph3 : forall L3 A3 regs6 m6 md3 xa xb,
  cn_inv L3 A3 m6 md3 -> st_init_done A3 = true ->
  In (xa, n + 1) (blocks L3 A3) -> In (xb, n + 1) (blocks L3 A3) -> xa <> xb ->
  remove cno_zz_dec (xb, n + 1) (remove cno_zz_dec (xa, n + 1) (blocks L3 A3)) = blocks L A ->
  res_ok_slots A3 (sb_malloc (sb_malloc b (n + 1)) (n + 1)) ->
  getr regs6 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs6 8 = Z_to_bv 64 rate -> getr regs6 9 = Z_to_bv 64 xa ->
  getr regs6 10 = Z_to_bv 64 xb -> getr regs6 18 = Z_to_bv 64 pa -> getr regs6 20 = Z_to_bv 64 n ->
  getr regs6 21 = Z_to_bv 64 t -> cn_keep regs6 -> cn_frame m6 ->
  SRcf B (mkCfg (mkst regs6 (Z_to_bv 64 0x12d74) m6 (seg_rom (ms_segs B))) md3) cn_final.
Proof.
  intros L3 A3 regs6 m6 md3 xa xb I Hinit Hina Hinb Hab Hrm Hres G2 G8 G9 G10 G18 G20 G21 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8256) by reflexivity.
  pose proof cn_sp0 as Hsp0.
  pose proof I as ((M3 & W3 & B3 & _ & _ & _ & F3 & _ & S3) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L3 A3 m6 md3 M3) as [Hh Hlz].
  pose proof (crt_img_low B SEGS) as HIL.
  assert (S6 : spZ regs6 = spZ regs - 64) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (USP : bv_unsigned (getr regs6 2) = spZ regs - 64) by exact S6.
  assert (Hro' : ro_agree rsegs m6) by (rewrite <- SEGS; exact I4).
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M3) as PW3.
  destruct (cn_blk L3 A3 m6 md3 xa _ M3 Hina) as (HA1 & HA2 & _ & HAi).
  destruct (cn_blk L3 A3 m6 md3 xb _ M3 Hinb) as (HB1 & HB2 & _ & HBi).
  assert (Hold : forall y, In y (blocks L A) -> In y (blocks L3 A3) /\ y <> (xa, n + 1) /\ y <> (xb, n + 1)).
  { intros y Hy. rewrite <- Hrm in Hy. apply in_remove in Hy as [Hy Hnb]. apply in_remove in Hy as [Hy Hna]. auto. }
  assert (DAB : ranges_disjoint (xa, n + 1) (xb, n + 1)).
  { apply (cn_pw_in _ _ _ PW3 Hina Hinb). intros E. injection E as E. exact (Hab E). }
  pose proof IBT as (qt & kt & Hqt & Ht1 & Ht2).
  destruct (cn_blk L A mem md qt kt HM Hqt) as (HT1 & HT2 & _).
  destruct (Hold _ Hqt) as (Tq & Tna & Tnb).
  pose proof (cn_pw_in _ _ _ PW3 Tq Hina Tna) as DTA.
  pose proof (cn_pw_in _ _ _ PW3 Tq Hinb Tnb) as DTB.
  unfold ranges_disjoint in DAB, DTA, DTB. cbn [fst snd] in DAB, DTA, DTB.
  (* the facts of the walk, on the normalized memory *)
  assert (SA : Frame.stk rsegs (normalize rsegs m6) xa (xa + n + 1)).
  { rewrite <- SEGS. replace (xa + n + 1) with (xa + (n + 1)) by ring.
    apply (cno_stk_blk B SEGS m6); [exact I4 | lia | lia |].
    intros i Hi. destruct (HAi i Hi) as (X1 & X2 & _). split; assumption. }
  assert (SB : Frame.stk rsegs (normalize rsegs m6) xb (xb + n + 1)).
  { rewrite <- SEGS. replace (xb + n + 1) with (xb + (n + 1)) by ring.
    apply (cno_stk_blk B SEGS m6); [exact I4 | lia | lia |].
    intros i Hi. destruct (HBi i Hi) as (X1 & X2 & _). split; assumption. }
  assert (ST : Frame.stk rsegs (normalize rsegs m6) (bv_unsigned (getr regs6 2) - 160) (bv_unsigned (getr regs6 2))).
  { rewrite USP, <- SEGS.
    apply (crt_stk_norm B HIL); [| exact I4 | lia].
    apply (crt_stk B HIL); [lia | lia |]. intros a Ha. apply S3. left. lia. }
  assert (TB : Mem.bytes_at rsegs (normalize rsegs m6) t T).
  { rewrite <- SEGS. apply (cno_bytes_norm B m6); [exact I4 | lia | lia |].
    intros i Hi. pose proof (cn_inv_kept L3 A3 m6 md3 I) as KP.
    pose proof (KP qt kt (t - qt + i) Hqt (fun H => H) ltac:(lia)) as E.
    replace (qt + (t - qt + i)) with (t + i) in E by ring. rewrite E. exact (BDT i Hi). }
  assert (PB : Mem.bytes_at rsegs (normalize rsegs m6) pa (P ++ Z_to_bv 8 0 :: SL)).
  { rewrite <- SEGS. apply (cno_bytes_norm B m6); [exact I4 | lia | rewrite HPL; lia |].
    intros i Hi. assert (Hi' := Hi). rewrite HPL in Hi'.
    destruct (F3 (pa + i)) as [E _].
    - left. lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M3 Ho). lia.
    - lia.
    - intros [].
    - rewrite E. exact (BDP i Hi). }
  eapply (crt_runN_cf B SEGS regs6 _ m6 md3); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G8, G9, G10, G18, G20, G21.
    eapply cno_segs.cn_seg3 with (T := T) (P := P) (SL := SL);
      first [eassumption | exact (mem_inv_normalize rsegs m6) | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU & WM & _) Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HRel). cbn [ms_mem MState.MS] in HRel.
  rewrite USP in MU.
  set (W := [(spZ regs - 64 - 160, spZ regs - 64); (xa, xa + n + 1); (xb, xb + n + 1)]) in MU.
  pose proof (mem_rel_normalize rsegs m6 Hro') as HR6.
  pose proof (munch_rel rsegs _ m6 _ (ms_mem ms) m' HR6 HRel Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m6 _ (ms_mem ms) m' HR6 HRel Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m6 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m6 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (crt_pres B m6 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (cn_not_out3 _ _ _ _ _ _ _ Hout) as [Hs|[Hs|Hs]].
    - apply (crt_fs_high B HIL). lia.
    - apply (crt_fs_none B SEGS). destruct (HAi (bv_unsigned x - xa) ltac:(lia)) as (_ & Hn & _).
      replace (xa + (bv_unsigned x - xa)) with (bv_unsigned x) in Hn by ring. exact Hn.
    - apply (crt_fs_none B SEGS). destruct (HBi (bv_unsigned x - xb) ltac:(lia)) as (_ & Hn & _).
      replace (xb + (bv_unsigned x - xb)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CNO_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L3 A3 x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. destruct (cn_not_out3 _ _ _ _ _ _ _ Hout) as [Hs|[Hs|Hs]].
    - left. lia.
    - right. destruct (HAi (x - xa) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (xa + (x - xa)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p k i Hp Hi E. destruct (Hold _ (crt_ub L A p k Hp)) as (Y1 & Y2 & _).
      pose proof (cn_pw_in _ _ _ PW3 Y1 Hina Y2) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
    - right. destruct (HBi (x - xb) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (xb + (x - xb)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p k i Hp Hi E. destruct (Hold _ (crt_ub L A p k Hp)) as (Y1 & _ & Y3).
      pose proof (cn_pw_in _ _ _ PW3 Y1 Hinb Y3) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
  pose proof (cn_inv_A L3 A3 m6 md3 (ms_mem ms) W I MU7 WM7 PRES HWW RO7) as I7.
  assert (FR7 : cn_frame (ms_mem ms)).
  { destruct FR as (junk & FRc). exists junk. rewrite <- SEGS in FRc |- *.
    apply (crt_cells_keep B m6 (ms_mem ms) _ _ FRc). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 64 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  destruct GK as (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27).
  apply (cn_ph4 _ L3 A3 regs7 (ms_mem ms) md3 xa xb);
    [exact FRM | exact I7 | exact Hinit | exact Hina | exact Hinb | exact Hab | exact Hrm | exact Hres
    | rewrite Hg7; reflexivity | rewrite Hg7; exact G2 | rewrite Hg7; reflexivity | rewrite Hg7; reflexivity | | exact FR7].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); rewrite Hg7;
    first [exact K3 | exact K4 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27].
Qed.

(* 0x12d68: a in s1, then b = malloc(n + 1) *)
Lemma cn_ph2 : forall L1 A1 regs2 m2 md1 xa d1 d2,
  cn_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = d1 ++ (xa, n + 1) :: d2 -> blocks L A = d1 ++ d2 ->
  res_ok_slots A1 (sb_malloc b (n + 1)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 64) -> getr regs2 8 = Z_to_bv 64 rate -> getr regs2 10 = Z_to_bv 64 xa ->
  getr regs2 18 = Z_to_bv 64 pa -> getr regs2 19 = Z_to_bv 64 (n + 1) -> getr regs2 20 = Z_to_bv 64 n ->
  getr regs2 21 = Z_to_bv 64 t -> cn_keep regs2 -> cn_frame m2 ->
  SRcf B (mkCfg (mkst regs2 (Z_to_bv 64 0x12d68) m2 (seg_rom (ms_segs B))) md1) cn_final.
Proof.
  intros L1 A1 regs2 m2 md1 xa d1 d2 I Hinit Hb1 Hb0 Hres G2 G8 G10 G18 G19 G20 G21 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8256) by reflexivity.
  pose proof cn_sp0 as Hsp0.
  pose proof I as ((M1 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  eapply (crt_runA_cf B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | | |].
  { unfold rmk. apply cn_seg2. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs3 -> Hg3. cbn [MState.MS ms_pc_val ms_mem].
  assert (G3a : getr regs3 1 = Z_to_bv 64 0x12d74) by (rewrite Hg3; reflexivity).
  assert (G3b : getr regs3 2 = Z_to_bv 64 (spZ regs - 64)) by (rewrite Hg3; exact G2).
  assert (G3c : getr regs3 10 = Z_to_bv 64 (n + 1)) by (rewrite Hg3; exact G19).
  assert (G3d : getr regs3 8 = Z_to_bv 64 rate) by (rewrite Hg3; exact G8).
  assert (G3e : getr regs3 9 = Z_to_bv 64 xa) by (rewrite Hg3; exact G10).
  assert (G3f : getr regs3 18 = Z_to_bv 64 pa) by (rewrite Hg3; exact G18).
  assert (G3g : getr regs3 20 = Z_to_bv 64 n) by (rewrite Hg3; exact G20).
  assert (G3h : getr regs3 21 = Z_to_bv 64 t) by (rewrite Hg3; exact G21).
  assert (K3 : cn_keep regs3).
  { destruct GK as (K3 & K4 & K22 & K23 & K24 & K25 & K26 & K27).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); rewrite Hg3;
      first [exact K3 | exact K4 | exact K22 | exact K23 | exact K24 | exact K25 | exact K26 | exact K27]. }
  assert (S3 : spZ regs3 = spZ regs - 64) by (unfold spZ at 1; rewrite G3b; apply MState.unsigned_lit; lia).
  assert (Hpre3 : call_pre B (aa_MR API) L1 A1 regs3 m2 md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs3 m2 md1)).
    apply (cn_pre L1 A1 m2 md1 regs3 64 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S3; replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 K3)) | rewrite G3a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  assert (Hroom : room_ag (sb_malloc b (n + 1)) (n + 1)).
  { apply room_ag_big; cbn [sb_malloc sb_live sb_cap sb_bytes]; lia. }
  replace (Z_to_bv 64 CNO_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply (SRcf_bind B).
  { exact (MALLOC L1 A1 regs3 m2 md1 (n + 1) (sb_malloc b (n + 1)) Hpre3 I4 G3c Hres Hroom). }
  intros c' (L2 & A2 & regs4 & m4 & md2 & xb & -> & Hpost & G4 & _ & _ & _ & (e1 & e2 & Hb2 & Hb1') & _ & Hro2 &
    Hgk2 & HU2 & Hinit2 & Hlen2 & Hres2).
  pose proof Hpost as (M2 & _ & _ & _ & _ & Hp4 & _).
  assert (I2' : cn_inv L2 A2 m4 md2).
  { apply (cn_inv_call L1 A1 m2 md1 regs3 ALLOC_STACK _ L2 A2 regs4 m4 md2 I Hpost);
      [rewrite S3, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen2
      | intros q k Hq; exact (HU2 q k (I3 q k Hq)) | exact Hro2 | exact Hgk2]. }
  assert (FR2 : cn_frame m4).
  { apply (cn_frame_call L1 A1 m2 md1 regs3 ALLOC_STACK _ L2 A2 regs4 m4 md2 I FR Hpost); [lia | intros a []]. }
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1) as PW1.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M2) as PW2.
  rewrite Hb1 in PW1. rewrite Hb2 in PW2.
  assert (NA : ~ In (xa, n + 1) (d1 ++ d2)) by (apply (crt_notin d1 d2 _ PW1); cbn; lia).
  assert (NB : ~ In (xb, n + 1) (e1 ++ e2)) by (apply (crt_notin e1 e2 _ PW2); cbn; lia).
  assert (InA1 : In (xa, n + 1) (e1 ++ e2)) by (rewrite <- Hb1', Hb1; apply crt_in_mid).
  assert (Hab : xa <> xb) by (intros E; subst xb; exact (NB InA1)).
  rewrite G3a.
  apply (cn_ph3 L2 A2 regs4 m4 md2 xa xb I2' Hinit2).
  - rewrite Hb2. apply crt_in_ins. exact InA1.
  - rewrite Hb2. apply crt_in_mid.
  - exact Hab.
  - rewrite remove_remove_comm, Hb2, (cno_rm_mid e1 e2 _ NB), <- Hb1', Hb1, (cno_rm_mid d1 d2 _ NA).
    exact (eq_sym Hb0).
  - exact Hres2.
  - transitivity (getr regs3 2); [apply (Hp4 2); unfold callee_saved; lia | exact G3b].
  - transitivity (getr regs3 8); [apply (Hp4 8); unfold callee_saved; lia | exact G3d].
  - transitivity (getr regs3 9); [apply (Hp4 9); unfold callee_saved; lia | exact G3e].
  - exact G4.
  - transitivity (getr regs3 18); [apply (Hp4 18); unfold callee_saved; lia | exact G3f].
  - transitivity (getr regs3 20); [apply (Hp4 20); unfold callee_saved; lia | exact G3g].
  - transitivity (getr regs3 21); [apply (Hp4 21); unfold callee_saved; lia | exact G3h].
  - exact (cn_keep_pres regs3 regs4 K3 Hp4).
  - exact FR2.
Qed.

(* 0x12d2c: the prologue and a = malloc(n + 1) *)
Lemma cn_entry :
  SRcf B (mkCfg (mkst regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (seg_rom (ms_segs B))) md) cn_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CNO_STACK = 8256) by reflexivity.
  pose proof cn_sp0 as Hsp0.
  pose proof (crt_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (I0 : cn_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p k Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs mem (spZ regs - CNO_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CNO_STACK L A regs mem md PRE ltac:(lia))).
  eapply (crt_runA_cf B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite R10, R11, R12, R13. eapply cn_seg1; [exact ST | unfold spZ; lia | lia | lia | lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x12d68) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 64)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (n + 1)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 8 = Z_to_bv 64 rate) by (rewrite Hg1; reflexivity).
  assert (G1e : getr regs1 18 = Z_to_bv 64 pa) by (rewrite Hg1; reflexivity).
  assert (G1f : getr regs1 19 = Z_to_bv 64 (n + 1)) by (rewrite Hg1; reflexivity).
  assert (G1g : getr regs1 20 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G1h : getr regs1 21 = Z_to_bv 64 t) by (rewrite Hg1; reflexivity).
  assert (K1 : cn_keep regs1)
    by (refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); rewrite Hg1; reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 64) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 64, spZ regs)] x -> spZ regs - 64 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (crt_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (crt_fs_high B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : cn_inv L A m1 md).
  { apply (cn_inv_A L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 64, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (crt_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (crt_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (FR1' : cn_frame m1) by (exists junk; exact FR1).
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CNO_STACK 64 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 64, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (Hroom : room_ag b (n + 1)) by (apply room_ag_big; lia).
  replace (Z_to_bv 64 CNO_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply (SRcf_bind B).
  { exact (MALLOC L A regs1 m1 md (n + 1) b Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & xa & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : cn_inv L1 A1 m2 md1).
  { apply (cn_inv_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : cn_frame m2).
  { apply (cn_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1' Hpost); [lia | intros a []]. }
  rewrite G1a.
  apply (cn_ph2 L1 A1 regs2 m2 md1 xa d1 d2 I1' Hinit1 Hb1 Hb0 Hres1).
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - transitivity (getr regs1 8); [apply (Hp2 8); unfold callee_saved; lia | exact G1d].
  - exact G2.
  - transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1e].
  - transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1f].
  - transitivity (getr regs1 20); [apply (Hp2 20); unfold callee_saved; lia | exact G1g].
  - transitivity (getr regs1 21); [apply (Hp2 21); unfold callee_saved; lia | exact G1h].
  - exact (cn_keep_pres regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem check_no_overread_holds_cf : check_no_overread_contract_cf B API.
Proof.
  intros L A regs mem md t n pa rate T P SL b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20
    H21.
  eapply cn_entry; eassumption.
Qed.

End CNO.
