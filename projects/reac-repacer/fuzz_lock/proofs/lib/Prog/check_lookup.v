(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_no_overread.v, with its module paths, module names, addresses and numbers changed; 357 of its 512 lines of code are new or changed and 697 lines of the source are left out. *)
(* Walk of fuzz_lock's harness function check_lookup (fuzz_lock.c:143-179) in fuzz_lock.plain, 0x12da0, against
   check_lookup_contract, in the form of libreac/fuzz_decode's lib/Prog/check_round_trip.v. The copy c holds the n bytes
   T of t, so rp_lock_lookup returns lock_lookup T P rate (rp_lock_lookup_contract); the inlined [expected] returns
   the same value (check_lookup_exp_holds, 0x12e28 -> 0x130d0), so abort is unreachable; free(c) is a tail call.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05 YL0i YL01 YL00 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Spec Require Import LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import memcpy_c rp_lock_lookup_c bcmp_c
  check_no_overread_c check_lookup_c cno_glue cl_segs.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cl_pw_in : forall (l : list (Z * Z)) x y, pairwise ranges_disjoint l -> In x l -> In y l -> x <> y ->
  ranges_disjoint x y.
Proof.
  induction l as [|z l IH]; intros x y H Hx Hy Hne; [destruct Hx|]. cbn in H. destruct H as [Hz H].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - congruence.
  - exact (Hz y Hy).
  - pose proof (Hz x Hx) as D. unfold ranges_disjoint in *. lia.
  - exact (IH x y H Hx Hy Hne).
Qed.

Lemma cl_not_out2 : forall a1 b1 a2 b2 x,
  ~ Frame.outside [(a1, b1); (a2, b2)] x -> (a1 <= x < b1) \/ (a2 <= x < b2).
Proof. intros a1 b1 a2 b2 x H. cbn [Frame.outside] in H. lia. Qed.

Lemma cl_sz_range : forall n, 0 <= n -> n <= cl_sz n <= n + 1 /\ 1 <= cl_sz n.
Proof. intros n Hn. unfold cl_sz. destruct (Z.eqb_spec n 0); lia. Qed.

Section CL.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = CL_MALLOC.
Hypothesis FREEPC : ms_free B = CL_FREE.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : malloc_contract B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MC : memcpy_contract.
Hypothesis RP : rp_lock_lookup_contract.
Hypothesis BC : bcmp_contract.
Lemma cl_blk : forall Lk Ak mk mdk p k, aa_MR API Lk Ak mk mdk -> In (p, k) (blocks Lk Ak) ->
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
  (t n pa kp rate : Z) (T P SL : list byte) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CL_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 t.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis R12 : getr regs 12 = Z_to_bv 64 pa.
Hypothesis R13 : getr regs 13 = Z_to_bv 64 kp.
Hypothesis R14 : getr regs 14 = Z_to_bv 64 rate.
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
Hypothesis HK : Z.of_nat (length P) = kp.
Hypothesis BDP : blk_data B mem pa (P ++ Z_to_bv 8 0 :: SL).
Hypothesis HR : 0 <= rate < 2 ^ 64.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : sb_live b + 1 <= sb_cap b <= CAPMAX /\ 0 <= sb_bytes b /\ sb_bytes b + (n + 1) <= 2 ^ 40.

Local Notation SZ := (cl_sz n).

Lemma cl_sp0 : 0 <= spZ regs.
Proof.
  unfold spZ. pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  lia.
Qed.

Definition cl_inv (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  kb_mid B API CL_STACK (spZ regs) L A mem md (fun _ => False) L' A' m' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')) /\
  ro_agree (ms_segs B) m' /\ guard_kept B mem m'.

(* gp and tp, which check_lookup leaves alone; its frame restores s0-s11 and ra *)
Definition cl_keep (r : bvmap 5 word) : Prop := getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4.

(* the saved registers of the frame of 176 bytes: s11 .. s0, ra at sp - 104 .. sp - 8 *)
Definition cl_frame (m' : word -> option byte) : Prop :=
  Step.rw_cells rsegs m' (spZ regs - 104) [Cells.C8 (getr regs 27); Cells.C8 (getr regs 26);
    Cells.C8 (getr regs 25); Cells.C8 (getr regs 24); Cells.C8 (getr regs 23); Cells.C8 (getr regs 22);
    Cells.C8 (getr regs 21); Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18);
    Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)].

Definition cl_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CL_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    st_init_done A' = true.

Lemma cl_pre : forall Lk Ak mk mdk regsk f K1,
  cl_inv Lk Ak mk mdk -> spZ regsk = spZ regs - f -> 0 <= f -> 0 <= K1 -> f + K1 <= CL_STACK ->
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

Lemma cl_inv_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cl_inv Lk Ak mk mdk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regs - CL_STACK <= spZ regsk - K2 -> spZ regsk <= spZ regs ->
  (forall a, E2 a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (length (st_regions Ak) <= length (st_regions A2))%nat ->
  (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A2)) ->
  ro_agree (ms_segs B) m2 -> guard_kept B mk m2 ->
  cl_inv L2 A2 m2 md2.
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

Lemma cl_inv_A : forall Lk Ak mk mdk mk' W,
  cl_inv Lk Ak mk mdk ->
  Frame.munch W mk mk' -> Frame.wmono (ms_segs B) mk mk' -> (forall x, mk x <> None -> mk' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CL_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lk Ak x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)) ->
  ro_agree (ms_segs B) mk' ->
  cl_inv Lk Ak mk' mdk.
Proof.
  intros Lk Ak mk mdk mk' W (I1 & I2 & I3 & I4 & I5) Hm Hw Hp HW Hro.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (crt_img_low B SEGS) as HIL.
  pose proof I1 as (M1 & _).
  split.
  { apply (crt_drop B API _ _ _ _ _ _
      (fun x => False \/ (0 <= x < 2 ^ 64 /\ ~ Frame.outside W x /\ ~ (spZ regs - CL_STACK <= x < spZ regs)))).
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

Lemma cl_free_keep : forall Lk Ak mk mdk p k,
  cl_inv Lk Ak mk mdk -> In (p, k) (user_blocks Ak) -> 0 < k ->
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

Lemma cl_frame_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cl_inv Lk Ak mk mdk -> cl_frame mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 104 -> (forall a, E2 a -> a < alloc_ceiling) ->
  cl_frame m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 ((M1 & _) & _) FR Hpost Hsp HE.
  pose proof Hpost as (M2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  unfold cl_frame in *. rewrite <- SEGS in FR |- *.
  apply (crt_cells_mb B mk m2 _ _ FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 104 in Hi.
  assert (HK0 : CL_STACK = 8368) by reflexivity.
  assert (Hr : alloc_ceiling <= spZ regs - 104 + i < 2 ^ 64) by lia.
  destruct (Hfr (spZ regs - 104 + i)) as [E W].
  - left. exact Hr.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - unfold scratch_k. lia.
  - intros He. pose proof (HE _ He). lia.
  - split; [exact E | intros Hw; apply W; exact Hw].
Qed.

Lemma cl_inv_kept : forall Lk Ak mk mdk, cl_inv Lk Ak mk mdk -> blocks_kept B L A mem mk (fun _ => False).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & K1 & _) & _ & I3 & _) a k i Hin _ Hi.
  destruct (crt_bu L A a k Hin) as (p & Hp & <-). exact (K1 p k i Hp (I3 p k Hp) Hi).
Qed.

Lemma cl_keep_pres : forall r r', cl_keep r -> regs_preserved r r' -> cl_keep r'.
Proof.
  intros r r' (K3 & K4) Hp. split.
  - transitivity (getr r 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
Qed.

Lemma cl_heap_E : forall Lk Ak mk mdk p k, aa_MR API Lk Ak mk mdk -> In (p, k) (user_blocks Ak) ->
  forall a, ptr_addr Lk p <= a < ptr_addr Lk p + k -> a < alloc_ceiling /\ ~ in_img B a.
Proof.
  intros Lk Ak mk mdk p k HMk Hp a Ha.
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p _ HMk Hp) as [Hr1 Hr2].
  split; [lia|]. replace a with (ptr_addr Lk p + (a - ptr_addr Lk p)) by lia.
  exact (ax_blocks_img AX Lk Ak mk mdk p k (a - ptr_addr Lk p) HMk Hp ltac:(lia)).
Qed.

(* 0x130d4: the epilogue, free(c) as a tail call, and the return *)
Lemma cl_ph5 : forall (fx7 : FPState) L5 A5 regs10 m10 md5 c,
  frm_zero (@fp_csr fx7) ->
  cl_inv L5 A5 m10 md5 -> st_init_done A5 = true ->
  In (c, SZ) (blocks L5 A5) -> remove cno_zz_dec (c, SZ) (blocks L5 A5) = blocks L A ->
  res_ok_slots A5 (sb_malloc b SZ) ->
  getr regs10 2 = Z_to_bv 64 (spZ regs - 176) -> getr regs10 8 = Z_to_bv 64 c -> cl_keep regs10 ->
  cl_frame m10 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs10 (Z_to_bv 64 0x130d4) m10 (seg_rom (ms_segs B))) md5) cl_final.
Proof.
  intros fx7 L5 A5 regs10 m10 md5 c Hfrm I Hinit Hin5 Hrm Hres G2 G8 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CL_STACK = 8368) by reflexivity.
  pose proof cl_sp0 as Hsp0.
  pose proof (cl_sz_range n ltac:(lia)) as HSZ.
  pose proof I as ((M5 & W5 & B5 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L5 A5 m10 md5 M5) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs10 2) = spZ regs - 176) by (rewrite G2; apply MState.unsigned_lit; lia).
  eapply (crt_runA (fx := fx7) B SEGS regs10 _ m10 md5); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply cl_seg4. rewrite USP. replace (spZ regs - 176 + 72) with (spZ regs - 104) by lia. exact FR. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs11 -> Hg11. cbn [MState.MS ms_pc_val ms_mem].
  assert (G11a : getr regs11 1 = getr regs 1) by (rewrite Hg11; reflexivity).
  assert (G11b : getr regs11 2 = Z_to_bv 64 (bv_unsigned (getr regs10 2) + 176)) by (rewrite Hg11; reflexivity).
  rewrite USP in G11b. replace (spZ regs - 176 + 176) with (spZ regs) in G11b by lia.
  assert (G11c : getr regs11 4 = getr regs 4) by (rewrite Hg11; exact (proj2 GK)).
  assert (G11d : getr regs11 10 = Z_to_bv 64 c) by (rewrite Hg11; exact G8).
  assert (S11 : spZ regs11 = spZ regs) by (unfold spZ at 1; rewrite G11b; apply MState.unsigned_lit; lia).
  assert (P11 : regs_preserved regs regs11).
  { destruct GK as (K3 & K4).
    assert (Hs : getr regs11 2 = getr regs 2) by (rewrite G11b; unfold spZ; apply Z_to_bv_bv_unsigned).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact Hs | rewrite Hg11; first [reflexivity | exact K3 | exact K4]]. }
  destruct (crt_bu L5 A5 c _ Hin5) as (p & Hp & Ep).
  assert (Hpre11 : call_pre B (aa_MR API) L5 A5 regs11 m10 md5).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L5 A5 regs11 m10 md5)).
    apply (cl_pre L5 A5 m10 md5 regs11 0 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia | rewrite S11; exact H16 | exact G11c | rewrite G11a; exact Hra
      | exact Hinit]. }
  replace (Z_to_bv 64 CL_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx7 L5 A5 regs11 m10 md5 p SZ (sb_malloc b SZ) Hpre11 I4 Hp).
    - rewrite G11d, Ep. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  rewrite Ep in Hd1.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M5) as PW5.
  assert (PW5' : pairwise ranges_disjoint (d1 ++ (c, SZ) :: d2)) by (rewrite <- Hd1; exact PW5).
  assert (ND5 : ~ In (c, SZ) (d1 ++ d2)) by (apply (crt_notin d1 d2 _ PW5'); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, <- Hrm, Hd1. symmetry. exact (cno_rm_mid d1 d2 _ ND5). }
  assert (HD5 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L5 p, SZ) y).
  { intros y Hy. rewrite Ep. rewrite <- Hrm in Hy. apply in_remove in Hy as [Hy Hne].
    exact (cl_pw_in _ _ _ PW5 Hin5 Hy (not_eq_sym Hne)). }
  assert (HU6 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A6)).
  { intros q k' Hq. apply Hub6; [exact (I3 q k' Hq) | exact (cl_free_keep L5 A5 m10 md5 p _ I Hp ltac:(lia) HD5 q k' Hq)]. }
  assert (I6 : cl_inv L6 A6 m12 md6).
  { apply (cl_inv_call L5 A5 m10 md5 regs11 ALLOC_STACK _ L6 A6 regs12 m12 md6 I Hpost);
      [rewrite S11, HK0; unfold ALLOC_STACK; lia | lia | exact (cl_heap_E L5 A5 m10 md5 p _ M5 Hp) | exact Hlen6
      | exact HU6 | exact Hro6 | exact Hgk6]. }
  apply SR_ret. exists fx7, L6, A6, regs12, m12, md6.
  split; [rewrite G11a; reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    exact (kb_preserved_trans _ _ _ P11 (proj2 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost))). }
  split; [exact Hb6|].
  split; [exact (cl_inv_kept _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | exact (Hinit6 Hinit)].
Qed.

(* 0x12df8: the NULL check, the copy, got = rp_lock_lookup(c, n, port, rate), want = expected(..), got = want *)
Lemma cl_ph3 : forall L3 A3 regs6 m6 md3 c,
  cl_inv L3 A3 m6 md3 -> st_init_done A3 = true ->
  In (c, SZ) (blocks L3 A3) -> remove cno_zz_dec (c, SZ) (blocks L3 A3) = blocks L A ->
  res_ok_slots A3 (sb_malloc b SZ) ->
  getr regs6 2 = Z_to_bv 64 (spZ regs - 176) -> getr regs6 9 = Z_to_bv 64 rate -> getr regs6 10 = Z_to_bv 64 c ->
  getr regs6 18 = Z_to_bv 64 kp -> getr regs6 19 = Z_to_bv 64 pa -> getr regs6 20 = Z_to_bv 64 n ->
  getr regs6 21 = Z_to_bv 64 t -> cl_keep regs6 -> cl_frame m6 ->
  SR (ms_segs B) (mkCfg (mkst regs6 (Z_to_bv 64 0x12df8) m6 (seg_rom (ms_segs B))) md3) cl_final.
Proof.
  intros L3 A3 regs6 m6 md3 c I Hinit Hinc Hrm Hres G2 G9 G10 G18 G19 G20 G21 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CL_STACK = 8368) by reflexivity.
  pose proof cl_sp0 as Hsp0.
  pose proof (cl_sz_range n ltac:(lia)) as HSZ.
  pose proof I as ((M3 & W3 & B3 & _ & _ & _ & F3 & _ & S3) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L3 A3 m6 md3 M3) as [Hh Hlz].
  pose proof (crt_img_low B SEGS) as HIL.
  assert (USP : bv_unsigned (getr regs6 2) = spZ regs - 176) by (rewrite G2; apply MState.unsigned_lit; lia).
  assert (Hro' : ro_agree rsegs m6) by (rewrite <- SEGS; exact I4).
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M3) as PW3.
  destruct (cl_blk L3 A3 m6 md3 c _ M3 Hinc) as (HC1 & HC2 & _ & HCi).
  assert (Hold : forall y, In y (blocks L A) -> In y (blocks L3 A3) /\ y <> (c, SZ)).
  { intros y Hy. rewrite <- Hrm in Hy. apply in_remove in Hy as [Hy Hne]. auto. }
  pose proof IBT as (qt & kt & Hqt & Ht1 & Ht2).
  destruct (cl_blk L A mem md qt kt HM Hqt) as (HT1 & HT2 & _).
  destruct (Hold _ Hqt) as (Tq & Tnc).
  pose proof (cl_pw_in _ _ _ PW3 Tq Hinc Tnc) as DTC.
  unfold ranges_disjoint in DTC. cbn [fst snd] in DTC.
  (* the facts of the walk, on the normalized memory *)
  assert (SC : Frame.stk rsegs (normalize rsegs m6) c (c + SZ)).
  { rewrite <- SEGS. apply (cno_stk_blk B SEGS m6); [exact I4 | lia | lia |].
    intros i Hi. destruct (HCi i Hi) as (X1 & X2 & _). split; assumption. }
  destruct (Frame.stk_split rsegs _ c (c + Z.of_nat (length T)) (c + SZ) SC ltac:(lia)) as [SCn _].
  assert (ST : Frame.stk rsegs (normalize rsegs m6) (spZ regs - 176 - 176) (spZ regs - 104)).
  { rewrite <- SEGS. apply (crt_stk_norm B HIL); [| exact I4 | lia].
    apply (crt_stk B HIL); [lia | lia |]. intros a Ha. apply S3. left. lia. }
  destruct (Frame.stk_split rsegs _ (spZ regs - 176 - 176) (spZ regs - 176) (spZ regs - 104) ST ltac:(lia))
    as [ST1 ST2].
  destruct (Frame.stk_carve rsegs _ (spZ regs - 176) (spZ regs - 104) 72 ST2 ltac:(lia)) as [_ [J72 CJ]].
  replace (spZ regs - 104 - Z.of_nat 72) with (spZ regs - 176) in CJ by lia.
  assert (TB : Mem.bytes_at rsegs (normalize rsegs m6) t T).
  { rewrite <- SEGS. apply (cno_bytes_norm B m6); [exact I4 | lia | lia |].
    intros i Hi. pose proof (cl_inv_kept L3 A3 m6 md3 I) as KP.
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
  eapply (crt_runN B SEGS regs6 _ m6 md3); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G2, G9, G10, G18, G19, G20, G21. rewrite <- HK, <- HT.
    eapply cl_m3 with (T := T) (P := P) (SL := SL) (spf := spZ regs - 176) (J := J72);
      first [eassumption | exact (mem_inv_normalize rsegs m6) | lia]. }
  { intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s8' & s9' & s10' & s11' &
      t3' & t4' & t5' & t6' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs7 (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s8' & s9' & s10' &
    s11' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & _) Hrel Hsame Hg7.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HRel). cbn [ms_mem MState.MS] in HRel.
  set (W := [(spZ regs - 176 - 176, spZ regs - 176 + 72); (c, c + Z.of_nat (length T))]) in MU.
  pose proof (mem_rel_normalize rsegs m6 Hro') as HR6.
  pose proof (munch_rel rsegs _ m6 _ (ms_mem ms) m' HR6 HRel Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m6 _ (ms_mem ms) m' HR6 HRel Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m6 (ms_mem ms) Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m6 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (crt_pres B m6 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (cl_not_out2 _ _ _ _ _ Hout) as [Hs|Hs].
    - apply (crt_fs_high B HIL). lia.
    - apply (crt_fs_none B SEGS). destruct (HCi (bv_unsigned x - c) ltac:(lia)) as (_ & Hn & _).
      replace (c + (bv_unsigned x - c)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (HWW : forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CL_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B L3 A3 x /\
      forall p k i, In (p, k) (user_blocks A) -> 0 <= i < k -> ptr_addr L p + i <> x)).
  { intros x Hx Hout. destruct (cl_not_out2 _ _ _ _ _ Hout) as [Hs|Hs].
    - left. lia.
    - right. destruct (HCi (x - c) ltac:(lia)) as (_ & Hn1 & Hn2).
      replace (c + (x - c)) with x in Hn1, Hn2 by ring.
      split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
      intros p k' i Hp Hi E. destruct (Hold _ (crt_ub L A p k' Hp)) as (Y1 & Y2).
      pose proof (cl_pw_in _ _ _ PW3 Y1 Hinc Y2) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
  pose proof (cl_inv_A L3 A3 m6 md3 (ms_mem ms) W I MU7 WM7 PRES HWW RO7) as I7.
  assert (FR7 : cl_frame (ms_mem ms)).
  { unfold cl_frame in *. rewrite <- SEGS in FR |- *.
    apply (crt_cells_keep B m6 (ms_mem ms) _ _ FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 104 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. unfold W. cbn [Frame.outside]. repeat split; lia. }
  destruct GK as (K3 & K4).
  apply (cl_ph5 _ L3 A3 regs7 (ms_mem ms) md3 c);
    [exact FRM | exact I7 | exact Hinit | exact Hinc | exact Hrm | exact Hres
    | rewrite Hg7; reflexivity | rewrite Hg7; reflexivity | | exact FR7].
  split; rewrite Hg7; [exact K3 | exact K4].
Qed.

(* 0x12da0: the prologue and c = malloc(n ? n : 1) *)
Lemma cl_entry :
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CHECK_LOOKUP) mem (seg_rom (ms_segs B))) md) cl_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CL_STACK = 8368) by reflexivity.
  pose proof cl_sp0 as Hsp0.
  pose proof (cl_sz_range n ltac:(lia)) as HSZ.
  assert (HP15 : (length P <= 15)%nat) by (rewrite length_app in HPL; cbn [length] in HPL; lia).
  pose proof (crt_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (I0 : cl_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p k Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs mem (spZ regs - CL_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CL_STACK L A regs mem md PRE ltac:(lia))).
  eapply (crt_runA B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite R10, R11, R12, R13, R14.
    eapply cl_seg1; [exact ST | unfold spZ; lia | lia | lia | lia | lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & _).
    repeat split; reflexivity. }
  intros ms regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> &
    MU & WM & FR1) Hg1.
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x12df8) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 176)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 SZ) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 9 = Z_to_bv 64 rate) by (rewrite Hg1; reflexivity).
  assert (G1e : getr regs1 18 = Z_to_bv 64 kp) by (rewrite Hg1; reflexivity).
  assert (G1f : getr regs1 19 = Z_to_bv 64 pa) by (rewrite Hg1; reflexivity).
  assert (G1g : getr regs1 20 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G1h : getr regs1 21 = Z_to_bv 64 t) by (rewrite Hg1; reflexivity).
  assert (K1 : cl_keep regs1) by (split; rewrite Hg1; reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 176) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 176, spZ regs)] x -> spZ regs - 176 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (crt_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (crt_fs_high B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : cl_inv L A m1 md).
  { apply (cl_inv_A L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 176, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (crt_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (crt_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (FR1' : cl_frame m1) by exact FR1.
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CL_STACK 176 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 176, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 176) with (spZ regs + (-11) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (Hroom : room_slots b SZ) by (apply room_slots_big; lia).
  replace (Z_to_bv 64 CL_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply SR_bind.
  { exact (MALLOC L A regs1 m1 md SZ b Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & c & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (M2 & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : cl_inv L1 A1 m2 md1).
  { apply (cl_inv_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : cl_frame m2).
  { apply (cl_frame_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1' Hpost); [lia | intros a []]. }
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M2) as PW2. rewrite Hb1 in PW2.
  assert (NC : ~ In (c, SZ) (d1 ++ d2)) by (apply (crt_notin d1 d2 _ PW2); cbn; lia).
  rewrite G1a.
  apply (cl_ph3 L1 A1 regs2 m2 md1 c I1' Hinit1).
  - rewrite Hb1. apply crt_in_mid.
  - rewrite Hb1, (cno_rm_mid d1 d2 _ NC). exact (eq_sym Hb0).
  - exact Hres1.
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - transitivity (getr regs1 9); [apply (Hp2 9); unfold callee_saved; lia | exact G1d].
  - exact G2.
  - transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1e].
  - transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1f].
  - transitivity (getr regs1 20); [apply (Hp2 20); unfold callee_saved; lia | exact G1g].
  - transitivity (getr regs1 21); [apply (Hp2 21); unfold callee_saved; lia | exact G1h].
  - exact (cl_keep_pres regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem check_lookup_holds : check_lookup_contract B API.
Proof.
  intros L A regs mem md t n pa kp rate T P SL b _. intros.
  eapply cl_entry; eassumption.
Qed.

End CL.
