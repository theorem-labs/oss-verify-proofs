(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_egress/lib/U/Prog/check_inject_cg.v, with its module paths, module names, addresses and numbers changed; 701 of its 911 lines of code are new or changed and 500 lines of the source are left out. *)
(* The walk of check_round_trip in fuzz_frame.plain at the level of SR: the instruction segments
   of crt_defs.v (section hypotheses here) joined with the contracts of malloc and free. The
   phases, from the end: cr_fout (0x134d0: free of out, the epilogue), cr_fwant (0x134c8: free
   of want), cr_shy (0x13464: the segment of shy, free of shy), cr_mid (0x130c0: the segment
   crt_mid, then free of want or malloc of shy), cr_ph2 (0x130b0: malloc of want), cr_entry
   (0x13058: the prologue, malloc of out). The form of libreac/fuzz_decode's
   lib/Prog/check_round_trip.v.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YM05 YL0i YL01 YL00 YO10.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import check_parse_fields_c check_round_trip_c
  crt_glue crt_defs memset_c memcpy_c bcmp_c diginet_frame_build_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cr_pw : forall (l1 l2 : list (Z * Z)) a n c k, pairwise ranges_disjoint (l1 ++ (a, n) :: l2) ->
  In (c, k) (l1 ++ l2) -> a + n <= c \/ c + k <= a.
Proof. intros l1 l2 a n c k H Hi. exact (crt_pw_mid l1 l2 (a, n) (c, k) H Hi). Qed.

Lemma cr_not_out3 : forall a1 b1 a2 b2 a3 b3 x,
  ~ Frame.outside [(a1, b1); (a2, b2); (a3, b3)] x -> (a1 <= x < b1) \/ (a2 <= x < b2) \/ (a3 <= x < b3).
Proof. intros a1 b1 a2 b2 a3 b3 x H. cbn [Frame.outside] in H. lia. Qed.

Lemma cr_not_out2 : forall a1 b1 a2 b2 x,
  ~ Frame.outside [(a1, b1); (a2, b2)] x -> (a1 <= x < b1) \/ (a2 <= x < b2).
Proof. intros a1 b1 a2 b2 x H. cbn [Frame.outside] in H. lia. Qed.

Lemma cr_mbyte_mrd : forall segs m a, mbyte segs m a = Mem.mrd segs m (Mem.wa a).
Proof. reflexivity. Qed.

Lemma cr_cells_rel : forall m m0 A cs, mem_rel rsegs m m0 ->
  Step.rw_cells rsegs m0 A cs -> Step.rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m m0 A _ HR) Hb)] |].
  exact (wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

Lemma cr_cb_len : forall segs m A k j cs, Step.rw_cells segs m A (Cells.CB k j :: cs) -> length j = k.
Proof. intros segs m A k j cs [[Hwf _] _]. cbn in Hwf. tauto. Qed.

Section CRT.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALPC : ms_malloc B = CRT_MALLOC.
Hypothesis FREEPC : ms_free B = CRT_FREE.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MEMSET : memset_contract.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis BUILD : diginet_frame_build_contract.
Hypothesis SEG1 : crt_seg1_stmt.
Hypothesis SEG2 : crt_seg2_stmt.
Hypothesis MID : crt_mid_stmt.
Hypothesis SHY : crt_shy_stmt.
Hypothesis SEGF1 : crt_segf1_stmt.
Hypothesis SEGF2 : crt_segf2_stmt.
Hypothesis SEGX : crt_segx_stmt.

Lemma cr_blk : forall Lk Ak mk mdk P n, aa_MR API Lk Ak mk mdk -> In (P, n) (blocks Lk Ak) ->
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

Lemma cr_stk_heap : forall Lk Ak mk mdk P k, aa_MR API Lk Ak mk mdk -> In (P, k) (blocks Lk Ak) ->
  Frame.stk rsegs (normalize rsegs mk) P (P + k).
Proof.
  intros Lk Ak mk mdk P k HM Hin. pose proof alloc_ceiling_value as Hc.
  destruct (cr_blk Lk Ak mk mdk P k HM Hin) as (H1 & H2 & _ & Hi).
  split; [lia|]. split; [lia|]. intros a Ha.
  destruct (Hi (a - P) ltac:(lia)) as ((bb & Hb) & Hn & _).
  replace (P + (a - P)) with a in Hb, Hn by ring.
  assert (Hr : Mem.ro_addr rsegs (Mem.wa a) = false).
  { rewrite <- SEGS. apply (crt_ro_false B); [lia | exact (crt_fs_none B SEGS a Hn)]. }
  assert (E : normalize rsegs mk (Mem.wa a) = Some bb) by (unfold normalize; rewrite Hr; exact Hb).
  split.
  - unfold wview. rewrite E. discriminate.
  - exists bb. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (w buf : Z) (b : list byte) (sb : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CRT_STACK L A regs mem md.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 w.
Hypothesis FC0 : fr_code b = 0.
Hypothesis LEN : Z.of_nat (length b) < 2 ^ 26.
Hypothesis BUF : 0 < buf < 2 ^ 64.
Hypothesis IB : in_block L A buf (Z.of_nat (length b)).
Hypothesis BD : blk_data B mem buf b.
Hypothesis SPW : spZ regs <= w.
Hypothesis W80 : w + 80 <= 2 ^ 63.
Hypothesis WB : blk_data B mem w (spec_bytes buf b).
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A sb.
Hypothesis ROOM : sb_live sb + 3 <= sb_cap sb <= CAPMAX /\ 0 <= sb_bytes sb /\
  sb_bytes sb + 3 * crt_len b <= 2 ^ 40.

Lemma cr_n : 60 <= crt_len b /\ crt_len b <= 2 ^ 26 + 30 /\
  30 + Z.of_nat (length (fr_body b)) <= Z.of_nat (length b).
Proof.
  destruct (fr_body_len_ok b FC0) as (H1 & H2 & H3).
  pose proof (length_fr_body b FC0) as E.
  assert (E' : Z.of_nat (length (fr_body b)) = fr_body_len b) by (rewrite E; lia).
  unfold crt_len, frame_len. rewrite E'. lia.
Qed.

Definition cr_inv (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  kb_mid B API CRT_STACK (spZ regs) L A mem md (fun _ => False) L' A' m' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A')) /\
  ro_agree (ms_segs B) m' /\ guard_kept B mem m'.

Definition cr_keep (r : bvmap 5 word) : Prop := getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4.

Definition cr_sv : list Cells.cell :=
  crt_saved (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27).

Definition cr_frame0 (m' : word -> option byte) : Prop :=
  exists j, Step.rw_cells rsegs m' (spZ regs - 144) (Cells.CB 40 j :: cr_sv).

Definition cr_frame1 (m' : word -> option byte) : Prop :=
  exists j, Step.rw_cells rsegs m' (spZ regs - 144) (Cells.CB 28 j :: Cells.CB 12 (crt_hb b) :: cr_sv).

Definition cr_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_k B (aa_MR API) CRT_STACK L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' sb /\
    st_init_done A' = true.

Lemma cr_pre : forall Lk Ak mk mdk regsk f K1,
  cr_inv Lk Ak mk mdk -> spZ regsk = spZ regs - f -> 0 <= f -> 0 <= K1 -> f + K1 <= CRT_STACK ->
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

Lemma cr_inv_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cr_inv Lk Ak mk mdk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regs - CRT_STACK <= spZ regsk - K2 -> spZ regsk <= spZ regs ->
  (forall a, E2 a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (length (st_regions Ak) <= length (st_regions A2))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A2)) ->
  ro_agree (ms_segs B) m2 -> guard_kept B mk m2 ->
  cr_inv L2 A2 m2 md2.
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

Lemma cr_inv_A : forall Lk Ak mk mdk mk' W,
  cr_inv Lk Ak mk mdk ->
  Frame.munch W mk mk' -> Frame.wmono (ms_segs B) mk mk' -> (forall x, mk x <> None -> mk' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CRT_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lk Ak x /\
      forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ptr_addr L p + i <> x)) ->
  ro_agree (ms_segs B) mk' ->
  cr_inv Lk Ak mk' mdk.
Proof.
  intros Lk Ak mk mdk mk' W (I1 & I2 & I3 & I4 & I5) Hm Hw Hp HW Hro.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (crt_img_low B SEGS) as HIL.
  pose proof I1 as (M1 & _).
  split.
  { apply (crt_drop B API _ _ _ _ _ _
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

Lemma cr_free_keep : forall Lk Ak mk mdk p n,
  cr_inv Lk Ak mk mdk -> In (p, n) (user_blocks Ak) -> 0 < n ->
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

Lemma cr_inv_kept : forall Lk Ak mk mdk, cr_inv Lk Ak mk mdk -> blocks_kept B L A mem mk (fun _ => False).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & K1 & _) & _ & I3 & _) a k i Hin _ Hi.
  destruct (crt_bu L A a k Hin) as (p & Hp & <-). exact (K1 p k i Hp (I3 p k Hp) Hi).
Qed.

Lemma cr_heap_E : forall Lk Ak mk mdk p n, aa_MR API Lk Ak mk mdk -> In (p, n) (user_blocks Ak) ->
  forall a, ptr_addr Lk p <= a < ptr_addr Lk p + n -> a < alloc_ceiling /\ ~ in_img B a.
Proof.
  intros Lk Ak mk mdk p n HMk Hp a Ha.
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p _ HMk Hp) as [Hr1 Hr2].
  split; [lia|]. replace a with (ptr_addr Lk p + (a - ptr_addr Lk p)) by lia.
  exact (ax_blocks_img AX Lk Ak mk mdk p n (a - ptr_addr Lk p) HMk Hp ltac:(lia)).
Qed.

Lemma cr_keep_pres : forall r r', cr_keep r -> regs_preserved r r' -> cr_keep r'.
Proof.
  intros r r' (K3 & K4) Hp. split.
  - transitivity (getr r 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
Qed.

(* The cells of the frame (144 bytes at the entry sp - 144) stay across a call of malloc or free. *)
Lemma cr_cells_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2 cs,
  cr_inv Lk Ak mk mdk -> Step.rw_cells rsegs mk (spZ regs - 144) cs -> Cells.cells_size cs = 144%nat ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 144 -> (forall a, E2 a -> a < alloc_ceiling) ->
  Step.rw_cells rsegs m2 (spZ regs - 144) cs.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 cs ((M1 & _) & _) FR Hsz Hpost Hsp HE.
  pose proof Hpost as (M2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  rewrite <- SEGS in FR |- *.
  apply (crt_cells_mb B mk m2 _ _ FR). intros i Hi. rewrite Hsz in Hi. change (Z.of_nat 144) with 144 in Hi.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hr : alloc_ceiling <= spZ regs - 144 + i < 2 ^ 64) by lia.
  destruct (Hfr (spZ regs - 144 + i)) as [E W].
  - left. exact Hr.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - unfold scratch_k. lia.
  - intros He. pose proof (HE _ He). lia.
  - split; [exact E | intros Hw; apply W; exact Hw].
Qed.

Lemma cr_cells_norm : forall mk cs, ro_agree (ms_segs B) mk ->
  Step.rw_cells rsegs mk (spZ regs - 144) cs -> Cells.cells_size cs = 144%nat ->
  Step.rw_cells rsegs (normalize rsegs mk) (spZ regs - 144) cs.
Proof.
  intros mk cs Hro [[Hwf Hb] Hw] Hsz.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  pose proof (crt_img_low B SEGS) as HIL.
  rewrite SEGS in Hro.
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs mk _ _ Hro Hb)] |].
  apply (wr_at_norm rsegs mk (normalize rsegs mk)); [exact (mem_rel_normalize rsegs mk Hro) | exact Hw |].
  intros i Hi. rewrite Hsz in Hi. change (Z.of_nat 144) with 144 in Hi.
  rewrite <- SEGS. apply (crt_ro_false B); [lia | apply (crt_fs_high B HIL); lia].
Qed.

Lemma cr_w_cells : forall Lk Ak mk mdk, cr_inv Lk Ak mk mdk ->
  Step.ro_cells rsegs (normalize rsegs mk) w (spec_cells buf b).
Proof.
  intros Lk Ak mk mdk ((M1 & _ & _ & _ & _ & _ & F1 & _) & _ & _ & Hro & _).
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  assert (Hwf : Cells.cells_wf (spec_cells buf b)) by (cbn; repeat split).
  assert (HL : length (Cells.cells_bytes (spec_cells buf b)) = 80%nat)
    by (rewrite (Cells.cells_bytes_length _ Hwf); reflexivity).
  split; [exact Hwf|]. rewrite SEGS in Hro. apply (bytes_at_normalize rsegs mk _ _ Hro).
  split; [lia|]. split; [rewrite HL; lia|]. intros i Hi. rewrite HL in Hi.
  assert (Hw : mbyte (ms_segs B) mk (w + Z.of_nat i) = mbyte (ms_segs B) mem (w + Z.of_nat i)).
  { apply (F1 (w + Z.of_nat i)).
    - left. lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
    - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
    - lia.
    - intros []. }
  rewrite (WB (Z.of_nat i)) in Hw by (unfold spec_bytes; rewrite HL; lia).
  rewrite Nat2Z.id in Hw. unfold spec_bytes in Hw. rewrite SEGS, cr_mbyte_mrd in Hw. exact Hw.
Qed.

Lemma cr_buf_bytes : forall Lk Ak mk mdk, cr_inv Lk Ak mk mdk -> Mem.bytes_at rsegs (normalize rsegs mk) buf b.
Proof.
  intros Lk Ak mk mdk I.
  pose proof PRE as (HM & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (cr_inv_kept Lk Ak mk mdk I) as KP.
  pose proof I as (_ & _ & _ & Hro & _).
  destruct IB as (q & k & Hq & Hq1 & Hq2).
  destruct (cr_blk L A mem md q k HM Hq) as (HQ1 & HQ2 & _).
  rewrite SEGS in Hro. apply (bytes_at_normalize rsegs mk _ _ Hro).
  split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (KP q k (buf - q + Z.of_nat i) Hq (fun H => H) ltac:(lia)) as E.
  replace (q + (buf - q + Z.of_nat i)) with (buf + Z.of_nat i) in E by ring.
  rewrite (BD (Z.of_nat i)) in E by lia. rewrite Nat2Z.id in E. rewrite SEGS, cr_mbyte_mrd in E. exact E.
Qed.

Lemma cr_stack_norm : forall Lk Ak mk mdk, cr_inv Lk Ak mk mdk ->
  Frame.stk rsegs (normalize rsegs mk) (spZ regs - 384) (spZ regs - 144).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & _ & S3) & _ & _ & I4 & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  pose proof (crt_img_low B SEGS) as HIL.
  rewrite <- SEGS. apply (crt_stk_norm B HIL); [| exact I4 | lia].
  apply (crt_stk B HIL); [lia | lia |]. intros a Ha. apply S3. left. lia.
Qed.

(* After a segment run on the normalized memory (crt_runN), with its writes W in the scratch below
   the entry sp or in blocks that are not the caller's. *)
Lemma cr_seg_inv : forall Lk Ak mk mdk mk' m0' W,
  cr_inv Lk Ak mk mdk ->
  mem_rel rsegs mk' m0' -> ro_same rsegs mk mk' ->
  Frame.munch W (normalize rsegs mk) m0' -> Frame.wmono rsegs (normalize rsegs mk) m0' ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CRT_STACK <= x < spZ regs) \/
     exists P k, In (P, k) (blocks Lk Ak) /\ (forall y, In y (blocks L A) -> ranges_disjoint (P, k) y) /\
       P <= x < P + k) ->
  cr_inv Lk Ak mk' mdk /\ Frame.munch W mk mk'.
Proof.
  intros Lk Ak mk mdk mk' m0' W I HR Hsame MU WM HW.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (crt_img_low B SEGS) as HIL.
  pose proof I as ((M1 & _) & _ & _ & Hro & _).
  assert (Hro' : ro_agree rsegs mk) by (rewrite <- SEGS; exact Hro).
  pose proof (mem_rel_normalize rsegs mk Hro') as HR6.
  pose proof (munch_rel rsegs _ mk _ mk' m0' HR6 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs mk _ mk' m0' HR6 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs mk mk' Hro' Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  split; [|exact MU7].
  apply (cr_inv_A Lk Ak mk mdk mk' W I MU7 WM7); [| | exact RO7].
  - intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (crt_pres B mk mk' x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (HW (bv_unsigned x) Hr Hout) as [Hs | (P & k & Hin & _ & Hx2)].
    + apply (crt_fs_high B HIL). lia.
    + apply (crt_fs_none B SEGS). destruct (cr_blk Lk Ak mk mdk P k M1 Hin) as (_ & _ & _ & Hi).
      destruct (Hi (bv_unsigned x - P) ltac:(lia)) as (_ & Hn & _).
      replace (P + (bv_unsigned x - P)) with (bv_unsigned x) in Hn by ring. exact Hn.
  - intros x Hx Hout. destruct (HW x Hx Hout) as [Hs | (P & k & Hin & HD & Hx2)]; [left; exact Hs | right].
    destruct (cr_blk Lk Ak mk mdk P k M1 Hin) as (_ & H2 & _ & Hi).
    destruct (Hi (x - P) ltac:(lia)) as (_ & Hn1 & Hn2).
    replace (P + (x - P)) with x in Hn1, Hn2 by ring.
    split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
    intros p n i Hp Hi' E. pose proof (HD _ (crt_ub L A p n Hp)) as D. unfold ranges_disjoint in D.
    cbn [fst snd] in D. lia.
Qed.

(** * 0x134d0: free of out, then the epilogue *)

Lemma cr_fout : forall (fx7 : FPState) L5 A5 regs10 m10 md5 O c1 c2,
  frm_zero (@fp_csr fx7) ->
  cr_inv L5 A5 m10 md5 -> st_init_done A5 = true ->
  blocks L5 A5 = c1 ++ (O, crt_len b) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A5 (sb_malloc sb (crt_len b)) ->
  getr regs10 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs10 22 = Z_to_bv 64 O -> cr_keep regs10 ->
  cr_frame1 m10 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs10 (Z_to_bv 64 0x134d0) m10 (seg_rom (ms_segs B))) md5) cr_final.
Proof.
  intros fx7 L5 A5 regs10 m10 md5 O c1 c2 Hfrm I Hinit Hb5 Hb0 Hres G2 G22 GK (j & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  pose proof cr_n as (Hn1 & Hn2 & _).
  pose proof I as ((M5 & W5 & B5 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L5 A5 m10 md5 M5) as [Hh Hlz].
  eapply (crt_runA (fx := fx7) B SEGS regs10 _ m10 md5); [exact Hh | exact Hlz | | |].
  { unfold rmk. apply SEGF2. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs11 -> Hg11. cbn [MState.MS ms_pc_val ms_mem].
  assert (G11a : getr regs11 1 = Z_to_bv 64 0x134d8) by (rewrite Hg11; reflexivity).
  assert (G11b : getr regs11 2 = Z_to_bv 64 (spZ regs - 144)) by (rewrite Hg11; exact G2).
  assert (G11c : getr regs11 10 = Z_to_bv 64 O) by (rewrite Hg11; exact G22).
  assert (K11 : cr_keep regs11) by (destruct GK as (K3 & K4); split; rewrite Hg11; assumption).
  assert (S11 : spZ regs11 = spZ regs - 144) by (unfold spZ at 1; rewrite G11b; apply MState.unsigned_lit; lia).
  destruct (crt_bu L5 A5 O _ ltac:(rewrite Hb5; apply crt_in_mid)) as (p & Hp & Ep).
  assert (Hpre11 : call_pre B (aa_MR API) L5 A5 regs11 m10 md5).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L5 A5 regs11 m10 md5)).
    apply (cr_pre L5 A5 m10 md5 regs11 144 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S11; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj2 K11) | rewrite G11a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity | exact Hinit]. }
  replace (Z_to_bv 64 CRT_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx7 L5 A5 regs11 m10 md5 p (crt_len b) (sb_malloc sb (crt_len b)) Hpre11 I4 Hp).
    - rewrite G11c, Ep. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp12 & _).
  rewrite Ep in Hd1.
  assert (PW5 : pairwise ranges_disjoint (c1 ++ (O, crt_len b) :: c2))
    by (rewrite <- Hb5; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M5)).
  assert (ND5 : ~ In (O, crt_len b) (c1 ++ c2)) by (apply (crt_notin c1 c2 _ PW5); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite Hd2, Hb0. symmetry. apply (crt_rm (O, crt_len b) c1 c2 d1 d2 ND5). rewrite <- Hb5. exact Hd1. }
  assert (HD5 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L5 p, crt_len b) y).
  { intros y Hy. rewrite Ep. apply (crt_pw_mid c1 c2 _ y PW5). rewrite <- Hb0. exact Hy. }
  assert (HU6 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A6)).
  { intros q k Hq. apply Hub6; [exact (I3 q k Hq) | exact (cr_free_keep L5 A5 m10 md5 p _ I Hp ltac:(lia) HD5 q k Hq)]. }
  assert (I6 : cr_inv L6 A6 m12 md6).
  { apply (cr_inv_call L5 A5 m10 md5 regs11 ALLOC_STACK _ L6 A6 regs12 m12 md6 I Hpost);
      [rewrite S11, HK0; unfold ALLOC_STACK; lia | lia | exact (cr_heap_E L5 A5 m10 md5 p _ M5 Hp) | exact Hlen6
      | exact HU6 | exact Hro6 | exact Hgk6]. }
  assert (FR6 : Step.rw_cells rsegs m12 (spZ regs - 144) (Cells.CB 28 j :: Cells.CB 12 (crt_hb b) :: cr_sv)).
  { apply (cr_cells_call L5 A5 m10 md5 regs11 ALLOC_STACK _ L6 A6 regs12 m12 md6 _ I FR eq_refl Hpost); [lia |].
    intros a Ha. exact (proj1 (cr_heap_E L5 A5 m10 md5 p _ M5 Hp a Ha)). }
  assert (G12b : getr regs12 2 = Z_to_bv 64 (spZ regs - 144))
    by (transitivity (getr regs11 2); [apply (Hp12 2); unfold callee_saved; lia | exact G11b]).
  assert (U12 : bv_unsigned (getr regs12 2) = spZ regs - 144) by (rewrite G12b; apply MState.unsigned_lit; lia).
  assert (K12 : cr_keep regs12) by exact (cr_keep_pres regs11 regs12 K11 Hp12).
  pose proof I6 as ((M6 & _) & _).
  destruct (kb_md B API L6 A6 m12 md6 M6) as [Hh6 Hlz6].
  rewrite G11a.
  eapply (crt_runA (fx := fx7) B SEGS regs12 _ m12 md6); [exact Hh6 | exact Hlz6 | | |].
  { unfold rmk. pose proof SEGX as SX. unfold crt_segx_stmt in SX. eapply SX. rewrite U12. exact FR6. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs13 -> Hg13. cbn [MState.MS ms_pc_val ms_mem].
  rewrite (kb_ret_pc (getr regs 1) Hra).
  apply SR_ret. exists fx7, L6, A6, regs13, m12, md6.
  split; [reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I6 as (I6a & _). apply (kb_post B API); [exact I6a|].
    destruct K12 as (K3 & K4).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      rewrite Hg13; try reflexivity.
    - cbn. rewrite U12. replace (spZ regs - 144 + 144) with (spZ regs) by lia. apply Z_to_bv_bv_unsigned.
    - exact K3.
    - exact K4. }
  split; [exact Hb6|].
  split; [exact (cr_inv_kept _ _ _ _ I6)|].
  destruct I6 as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [rewrite sb_free_malloc in Hres6; exact Hres6 | exact (Hinit6 Hinit)].
Qed.

(** * 0x134c8: free of want *)

Lemma cr_fwant : forall (fx7 : FPState) L4 A4 regs8 m8 md4 O Wt c1 c2 e1 e2,
  frm_zero (@fp_csr fx7) ->
  cr_inv L4 A4 m8 md4 -> st_init_done A4 = true ->
  blocks L4 A4 = e1 ++ (Wt, crt_len b) :: e2 -> e1 ++ e2 = c1 ++ (O, crt_len b) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A4 (sb_malloc (sb_malloc sb (crt_len b)) (crt_len b)) ->
  getr regs8 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs8 9 = Z_to_bv 64 Wt -> getr regs8 22 = Z_to_bv 64 O ->
  cr_keep regs8 -> cr_frame1 m8 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs8 (Z_to_bv 64 0x134c8) m8 (seg_rom (ms_segs B))) md4) cr_final.
Proof.
  intros fx7 L4 A4 regs8 m8 md4 O Wt c1 c2 e1 e2 Hfrm I Hinit Hb4 He Hb0 Hres G2 G9 G22 GK (j & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  pose proof cr_n as (Hn1 & Hn2 & _).
  pose proof I as ((M4 & W4 & B4 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L4 A4 m8 md4 M4) as [Hh Hlz].
  eapply (crt_runA (fx := fx7) B SEGS regs8 _ m8 md4); [exact Hh | exact Hlz | | |].
  { unfold rmk. apply SEGF1. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs9 -> Hg9. cbn [MState.MS ms_pc_val ms_mem].
  assert (G9a : getr regs9 1 = Z_to_bv 64 0x134d0) by (rewrite Hg9; reflexivity).
  assert (G9b : getr regs9 2 = Z_to_bv 64 (spZ regs - 144)) by (rewrite Hg9; exact G2).
  assert (G9d : getr regs9 10 = Z_to_bv 64 Wt) by (rewrite Hg9; exact G9).
  assert (G9e : getr regs9 22 = Z_to_bv 64 O) by (rewrite Hg9; exact G22).
  assert (K9 : cr_keep regs9) by (destruct GK as (K3 & K4); split; rewrite Hg9; assumption).
  assert (S9 : spZ regs9 = spZ regs - 144) by (unfold spZ at 1; rewrite G9b; apply MState.unsigned_lit; lia).
  destruct (crt_bu L4 A4 Wt _ ltac:(rewrite Hb4; apply crt_in_mid)) as (q & Hq & Eq).
  assert (Hpre9 : call_pre B (aa_MR API) L4 A4 regs9 m8 md4).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L4 A4 regs9 m8 md4)).
    apply (cr_pre L4 A4 m8 md4 regs9 144 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S9; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj2 K9) | rewrite G9a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity | exact Hinit]. }
  replace (Z_to_bv 64 CRT_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx7 L4 A4 regs9 m8 md4 q (crt_len b) (sb_malloc (sb_malloc sb (crt_len b)) (crt_len b))
      Hpre9 I4 Hq).
    - rewrite G9d, Eq. reflexivity.
    - exact Hres. }
  intros c' (L5 & A5 & regs10 & m10 & md5 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro5 & Hgk5 & Hub5 &
    Hinit5 & Hlen5 & Hres5).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp10 & _).
  rewrite Eq in Hd1.
  assert (PW4 : pairwise ranges_disjoint (e1 ++ (Wt, crt_len b) :: e2))
    by (rewrite <- Hb4; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M4)).
  assert (ND4 : ~ In (Wt, crt_len b) (e1 ++ e2)) by (apply (crt_notin e1 e2 _ PW4); cbn; lia).
  assert (Hb5 : blocks L5 A5 = c1 ++ (O, crt_len b) :: c2).
  { rewrite Hd2, <- He. symmetry. apply (crt_rm (Wt, crt_len b) e1 e2 d1 d2 ND4). rewrite <- Hb4. exact Hd1. }
  assert (HD4 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L4 q, crt_len b) y).
  { intros y Hy. rewrite Eq. apply (crt_pw_mid e1 e2 _ y PW4). rewrite He. apply crt_in_ins. rewrite <- Hb0. exact Hy. }
  assert (HU5 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A5)).
  { intros q' k Hq'. apply Hub5; [exact (I3 q' k Hq') | exact (cr_free_keep L4 A4 m8 md4 q _ I Hq ltac:(lia) HD4 q' k Hq')]. }
  assert (I5' : cr_inv L5 A5 m10 md5).
  { apply (cr_inv_call L4 A4 m8 md4 regs9 ALLOC_STACK _ L5 A5 regs10 m10 md5 I Hpost);
      [rewrite S9, HK0; unfold ALLOC_STACK; lia | lia | exact (cr_heap_E L4 A4 m8 md4 q _ M4 Hq) | exact Hlen5
      | exact HU5 | exact Hro5 | exact Hgk5]. }
  assert (FR5 : cr_frame1 m10).
  { exists j. apply (cr_cells_call L4 A4 m8 md4 regs9 ALLOC_STACK _ L5 A5 regs10 m10 md5 _ I FR eq_refl Hpost); [lia |].
    intros a Ha. exact (proj1 (cr_heap_E L4 A4 m8 md4 q _ M4 Hq a Ha)). }
  rewrite G9a.
  apply (cr_fout fx7 L5 A5 regs10 m10 md5 O c1 c2 Hfrm I5' (Hinit5 Hinit) Hb5 Hb0).
  - rewrite sb_free_malloc in Hres5. exact Hres5.
  - transitivity (getr regs9 2); [apply (Hp10 2); unfold callee_saved; lia | exact G9b].
  - transitivity (getr regs9 22); [apply (Hp10 22); unfold callee_saved; lia | exact G9e].
  - exact (cr_keep_pres regs9 regs10 K9 Hp10).
  - exact FR5.
Qed.

(** * 0x13464: the segment of shy, then free of shy *)

Lemma cr_shy : forall (fx7 : FPState) L3 A3 regs6 m6 md3 S O Wt c1 c2 e1 e2 g1 g2,
  frm_zero (@fp_csr fx7) -> crt_ok b = true ->
  cr_inv L3 A3 m6 md3 -> st_init_done A3 = true ->
  blocks L3 A3 = g1 ++ (S, crt_len b - 1) :: g2 -> g1 ++ g2 = e1 ++ (Wt, crt_len b) :: e2 ->
  e1 ++ e2 = c1 ++ (O, crt_len b) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A3 (sb_malloc (sb_malloc (sb_malloc sb (crt_len b)) (crt_len b)) (crt_len b - 1)) ->
  getr regs6 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs6 9 = Z_to_bv 64 Wt -> getr regs6 10 = Z_to_bv 64 S ->
  getr regs6 18 = Z_to_bv 64 w -> getr regs6 19 = Z_to_bv 64 (crt_len b - 1) -> getr regs6 22 = Z_to_bv 64 O ->
  cr_keep regs6 -> cr_frame1 m6 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs6 (Z_to_bv 64 0x13464) m6 (seg_rom (ms_segs B))) md3) cr_final.
Proof.
  intros fx7 L3 A3 regs6 m6 md3 S O Wt c1 c2 e1 e2 g1 g2 Hfrm Hok I Hinit Hb3 Hg He Hb0 Hres G2 G9 G10 G18 G19
    G22 GK (j & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  pose proof cr_n as (Hn1 & Hn2 & Hn3).
  pose proof I as ((M3 & W3 & B3 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L3 A3 m6 md3 M3) as [Hh Hlz].
  assert (Hro' : ro_agree rsegs m6) by (rewrite <- SEGS; exact I4).
  assert (USP : bv_unsigned (getr regs6 2) = spZ regs - 144) by (rewrite G2; apply MState.unsigned_lit; lia).
  assert (PW3 : pairwise ranges_disjoint (g1 ++ (S, crt_len b - 1) :: g2))
    by (rewrite <- Hb3; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M3)).
  assert (InS : In (S, crt_len b - 1) (blocks L3 A3)) by (rewrite Hb3; apply crt_in_mid).
  assert (Hold : forall y, In y (blocks L A) -> In y (g1 ++ g2)).
  { intros y Hy. rewrite Hb0 in Hy. rewrite Hg. apply crt_in_ins. rewrite He. apply crt_in_ins. exact Hy. }
  assert (HDS : forall y, In y (blocks L A) -> ranges_disjoint (S, crt_len b - 1) y).
  { intros y Hy. exact (crt_pw_mid g1 g2 _ y PW3 (Hold y Hy)). }
  destruct (cr_blk L3 A3 m6 md3 S _ M3 InS) as (HS1 & HS2 & _ & HSi).
  pose proof IB as (qa & ka & Hqa & Ha1 & Ha2).
  destruct (cr_blk L A mem md qa ka HM Hqa) as (HA1 & HA2 & _).
  pose proof (HDS _ Hqa) as DSA. unfold ranges_disjoint in DSA. cbn [fst snd] in DSA.
  eapply (crt_runN (fx := fx7) B SEGS regs6 _ m6 md3); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G9, G10, G18, G19, G22. pose proof SHY as SH. unfold crt_shy_stmt in SH.
    eapply (SH MEMSET BUILD) with (buf := buf) (b := b) (j := j) (sv := cr_sv).
    - exact FC0.
    - exact LEN.
    - reflexivity.
    - exact Hok.
    - rewrite USP. unfold crt_lay_shy. lia.
    - exact (cr_w_cells L3 A3 m6 md3 I).
    - exact (cr_buf_bytes L3 A3 m6 md3 I).
    - exact (cr_stk_heap L3 A3 m6 md3 S _ M3 InS).
    - rewrite USP. replace (spZ regs - 144 - 240) with (spZ regs - 384) by lia. exact (cr_stack_norm L3 A3 m6 md3 I).
    - reflexivity.
    - rewrite USP. apply (cr_cells_norm m6 _ I4 FR). reflexivity.
    - exact (mem_inv_normalize rsegs m6). }
  { intros ms Hq. do 24 destruct Hq as [? Hq]. destruct Hq as [-> _]. repeat split; reflexivity. }
  intros ms s0 regs7 Hq Hrel Hsame Hg7.
  do 24 destruct Hq as [? Hq]. destruct Hq as (E & MU & WM & MI & FR'). subst s0.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  cbn [ms_fregs ms_fcsr ms_pc_val MState.MS].
  rewrite USP in MU, FR'.
  destruct (cr_seg_inv L3 A3 m6 md3 (ms_mem ms) _ _ I HR Hsame MU WM) as [I7 _].
  { intros y Hy Hout. destruct (cr_not_out2 _ _ _ _ _ Hout) as [Hs|Hs].
    - left. lia.
    - right. exists S, (crt_len b - 1). split; [exact InS|]. split; [exact HDS | lia]. }
  pose proof (cr_cells_rel (ms_mem ms) _ _ _ HR FR') as FR7.
  assert (G7a : getr regs7 1 = Z_to_bv 64 0x134c8) by (rewrite Hg7; reflexivity).
  assert (G7b : getr regs7 2 = Z_to_bv 64 (spZ regs - 144)) by (rewrite Hg7; exact G2).
  assert (G7c : getr regs7 10 = Z_to_bv 64 S) by (rewrite Hg7; reflexivity).
  assert (G7d : getr regs7 9 = Z_to_bv 64 Wt) by (rewrite Hg7; reflexivity).
  assert (G7e : getr regs7 22 = Z_to_bv 64 O) by (rewrite Hg7; reflexivity).
  assert (K7 : cr_keep regs7) by (destruct GK as (K3 & K4); split; rewrite Hg7; assumption).
  assert (S7 : spZ regs7 = spZ regs - 144) by (unfold spZ at 1; rewrite G7b; apply MState.unsigned_lit; lia).
  set (fx8 := mkFP (@fp_regs fx7) (@fp_csr fx7)).
  assert (Hfrm8 : frm_zero (@fp_csr fx8)) by exact Hfrm.
  pose proof I7 as ((M7 & _) & _ & I73 & I74 & _).
  destruct (crt_bu L3 A3 S _ InS) as (s & Hs & Es).
  assert (Hpre7 : call_pre B (aa_MR API) L3 A3 regs7 (ms_mem ms) md3).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L3 A3 regs7 (ms_mem ms) md3)).
    apply (cr_pre L3 A3 (ms_mem ms) md3 regs7 144 ALLOC_STACK I7); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S7; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj2 K7) | rewrite G7a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity | exact Hinit]. }
  replace (Z_to_bv 64 CRT_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE fx8 L3 A3 regs7 (ms_mem ms) md3 s (crt_len b - 1)
      (sb_malloc (sb_malloc (sb_malloc sb (crt_len b)) (crt_len b)) (crt_len b - 1)) Hpre7 I74 Hs).
    - rewrite G7c, Es. reflexivity.
    - exact Hres. }
  intros c' (L4 & A4 & regs8 & m8 & md4 & -> & Hpost & (d1 & d2 & Hd1 & Hd2) & Hkept & Hro4 & Hgk4 & Hub4 &
    Hinit4 & Hlen4 & Hres4).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp8 & _).
  rewrite Es in Hd1.
  assert (ND3 : ~ In (S, crt_len b - 1) (g1 ++ g2)) by (apply (crt_notin g1 g2 _ PW3); cbn; lia).
  assert (Hb4 : blocks L4 A4 = e1 ++ (Wt, crt_len b) :: e2).
  { rewrite Hd2, <- Hg. symmetry. apply (crt_rm (S, crt_len b - 1) g1 g2 d1 d2 ND3). rewrite <- Hb3. exact Hd1. }
  assert (HD3 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L3 s, crt_len b - 1) y).
  { intros y Hy. rewrite Es. exact (HDS y Hy). }
  assert (HU4 : forall q' k, In (q', k) (user_blocks A) -> In (q', k) (user_blocks A4)).
  { intros q' k Hq'. apply Hub4;
      [exact (I73 q' k Hq') | exact (cr_free_keep L3 A3 (ms_mem ms) md3 s _ I7 Hs ltac:(lia) HD3 q' k Hq')]. }
  assert (I4' : cr_inv L4 A4 m8 md4).
  { apply (cr_inv_call L3 A3 (ms_mem ms) md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8 md4 I7 Hpost);
      [rewrite S7, HK0; unfold ALLOC_STACK; lia | lia | exact (cr_heap_E L3 A3 (ms_mem ms) md3 s _ M7 Hs)
      | exact Hlen4 | exact HU4 | exact Hro4 | exact Hgk4]. }
  assert (FR4 : cr_frame1 m8).
  { exists j. apply (cr_cells_call L3 A3 (ms_mem ms) md3 regs7 ALLOC_STACK _ L4 A4 regs8 m8 md4 _ I7 FR7 eq_refl
      Hpost); [lia |].
    intros a Ha. exact (proj1 (cr_heap_E L3 A3 (ms_mem ms) md3 s _ M7 Hs a Ha)). }
  rewrite G7a.
  apply (cr_fwant fx8 L4 A4 regs8 m8 md4 O Wt c1 c2 e1 e2 Hfrm8 I4' (Hinit4 Hinit) Hb4 He Hb0).
  - rewrite sb_free_malloc in Hres4. exact Hres4.
  - transitivity (getr regs7 2); [apply (Hp8 2); unfold callee_saved; lia | exact G7b].
  - transitivity (getr regs7 9); [apply (Hp8 9); unfold callee_saved; lia | exact G7d].
  - transitivity (getr regs7 22); [apply (Hp8 22); unfold callee_saved; lia | exact G7e].
  - exact (cr_keep_pres regs7 regs8 K7 Hp8).
  - exact FR4.
Qed.

(** * 0x130c0: the segment crt_mid, then free of want or malloc of shy *)

Lemma cr_mid : forall L2 A2 regs4 m4 md2 O Wt c1 c2 e1 e2,
  cr_inv L2 A2 m4 md2 -> st_init_done A2 = true ->
  blocks L2 A2 = e1 ++ (Wt, crt_len b) :: e2 -> e1 ++ e2 = c1 ++ (O, crt_len b) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A2 (sb_malloc (sb_malloc sb (crt_len b)) (crt_len b)) ->
  getr regs4 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs4 10 = Z_to_bv 64 Wt ->
  getr regs4 18 = Z_to_bv 64 w -> getr regs4 19 = Z_to_bv 64 (crt_len b) -> getr regs4 22 = Z_to_bv 64 O ->
  cr_keep regs4 -> cr_frame0 m4 ->
  SR (ms_segs B) (mkCfg (mkst regs4 (Z_to_bv 64 0x130c0) m4 (seg_rom (ms_segs B))) md2) cr_final.
Proof.
  intros L2 A2 regs4 m4 md2 O Wt c1 c2 e1 e2 I Hinit Hb2 He Hb0 Hres G2 G10 G18 G19 G22 GK (j & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  pose proof cr_n as (Hn1 & Hn2 & Hn3).
  pose proof I as ((M2 & W2 & B2 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L2 A2 m4 md2 M2) as [Hh Hlz].
  assert (Hro' : ro_agree rsegs m4) by (rewrite <- SEGS; exact I4).
  assert (USP : bv_unsigned (getr regs4 2) = spZ regs - 144) by (rewrite G2; apply MState.unsigned_lit; lia).
  assert (PW2 : pairwise ranges_disjoint (e1 ++ (Wt, crt_len b) :: e2))
    by (rewrite <- Hb2; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M2)).
  assert (PWe : pairwise ranges_disjoint (c1 ++ (O, crt_len b) :: c2))
    by (rewrite <- He; exact (crt_pw_del e1 e2 _ PW2)).
  assert (InW : In (Wt, crt_len b) (blocks L2 A2)) by (rewrite Hb2; apply crt_in_mid).
  assert (InOe : In (O, crt_len b) (e1 ++ e2)) by (rewrite He; apply crt_in_mid).
  assert (InO : In (O, crt_len b) (blocks L2 A2)) by (rewrite Hb2; apply crt_in_ins; exact InOe).
  assert (Hold : forall y, In y (blocks L A) -> In y (c1 ++ c2) /\ In y (e1 ++ e2)).
  { intros y Hy. rewrite Hb0 in Hy. split; [exact Hy|]. rewrite He. apply crt_in_ins. exact Hy. }
  assert (HDO : forall y, In y (blocks L A) -> ranges_disjoint (O, crt_len b) y).
  { intros y Hy. exact (crt_pw_mid c1 c2 _ y PWe (proj1 (Hold y Hy))). }
  assert (HDW : forall y, In y (blocks L A) -> ranges_disjoint (Wt, crt_len b) y).
  { intros y Hy. exact (crt_pw_mid e1 e2 _ y PW2 (proj2 (Hold y Hy))). }
  destruct (cr_blk L2 A2 m4 md2 O _ M2 InO) as (HO1 & HO2 & _).
  destruct (cr_blk L2 A2 m4 md2 Wt _ M2 InW) as (HW1 & HW2 & _).
  pose proof (cr_pw _ _ _ _ _ _ PW2 InOe) as DWO.
  pose proof IB as (qa & ka & Hqa & Ha1 & Ha2).
  destruct (cr_blk L A mem md qa ka HM Hqa) as (HA1 & HA2 & _).
  pose proof (HDO _ Hqa) as DOA. unfold ranges_disjoint in DOA. cbn [fst snd] in DOA.
  pose proof (HDW _ Hqa) as DWA. unfold ranges_disjoint in DWA. cbn [fst snd] in DWA.
  eapply (crt_runN B SEGS regs4 _ m4 md2); [exact Hh | exact Hlz | exact Hro' | | |].
  { unfold rmk. rewrite G10, G18, G19, G22. pose proof MID as MD. unfold crt_mid_stmt in MD.
    eapply (MD MEMSET MEMCPY BCMP BUILD) with (buf := buf) (b := b) (j := j) (sv := cr_sv).
    - exact FC0.
    - exact LEN.
    - reflexivity.
    - rewrite USP. unfold crt_lay. lia.
    - exact (cr_w_cells L2 A2 m4 md2 I).
    - exact (cr_buf_bytes L2 A2 m4 md2 I).
    - exact (cr_stk_heap L2 A2 m4 md2 O _ M2 InO).
    - exact (cr_stk_heap L2 A2 m4 md2 Wt _ M2 InW).
    - rewrite USP. replace (spZ regs - 144 - 240) with (spZ regs - 384) by lia. exact (cr_stack_norm L2 A2 m4 md2 I).
    - exact (cr_cb_len _ _ _ _ _ _ FR).
    - reflexivity.
    - rewrite USP. apply (cr_cells_norm m4 _ I4 FR). reflexivity.
    - exact (mem_inv_normalize rsegs m4). }
  { intros ms Hq. do 28 destruct Hq as [? Hq]. destruct Hq as [-> _]. repeat split; reflexivity. }
  intros ms s0 regs5 Hq Hrel Hsame Hg5.
  destruct Hq as (ra' & t0' & t1' & t2' & s0' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s4' & s5' &
    s7' & s8' & s9' & s10' & s11' & t3' & t4' & t5' & t6' & pc' & j' & m' & E & Hpath & MU & WM & MI & FR').
  subst s0.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  cbn [ms_fregs ms_fcsr ms_pc_val MState.MS].
  rewrite USP in MU, FR'.
  destruct (cr_seg_inv L2 A2 m4 md2 (ms_mem ms) _ _ I HR Hsame MU WM) as [I5' _].
  { intros y Hy Hout. destruct (cr_not_out3 _ _ _ _ _ _ _ Hout) as [Hs|[Hs|Hs]].
    - left. lia.
    - right. exists O, (crt_len b). split; [exact InO|]. split; [exact HDO | lia].
    - right. exists Wt, (crt_len b). split; [exact InW|]. split; [exact HDW | lia]. }
  assert (FR5 : cr_frame1 (ms_mem ms)) by (exists j'; exact (cr_cells_rel (ms_mem ms) _ _ _ HR FR')).
  assert (G5b : getr regs5 2 = Z_to_bv 64 (spZ regs - 144)) by (rewrite Hg5; exact G2).
  assert (G5s1 : getr regs5 9 = Z_to_bv 64 Wt) by (rewrite Hg5; reflexivity).
  assert (G5s2 : getr regs5 18 = Z_to_bv 64 w) by (rewrite Hg5; reflexivity).
  assert (G5s6 : getr regs5 22 = Z_to_bv 64 O) by (rewrite Hg5; reflexivity).
  assert (K5 : cr_keep regs5) by (destruct GK as (K3 & K4); split; rewrite Hg5; assumption).
  assert (S5 : spZ regs5 = spZ regs - 144) by (unfold spZ at 1; rewrite G5b; apply MState.unsigned_lit; lia).
  set (fx8 := mkFP (@fp_regs fx) (@fp_csr fx)).
  assert (Hfrm8 : frm_zero (@fp_csr fx8)) by exact FRM.
  destruct Hpath as [(Hok & ->) | (Hok & -> & -> & -> & ->)].
  - exact (cr_fwant fx8 L2 A2 regs5 (ms_mem ms) md2 O Wt c1 c2 e1 e2 Hfrm8 I5' Hinit Hb2 He Hb0 Hres G5b G5s1
      G5s6 K5 FR5).
  - assert (G5a : getr regs5 1 = Z_to_bv 64 0x13464) by (rewrite Hg5; reflexivity).
    assert (G5a0 : getr regs5 10 = Z_to_bv 64 (crt_len b - 1)) by (rewrite Hg5; reflexivity).
    assert (G5s3 : getr regs5 19 = Z_to_bv 64 (crt_len b - 1)) by (rewrite Hg5; reflexivity).
    pose proof I5' as (_ & _ & _ & I54 & _).
    assert (Hpre5 : call_pre B (aa_MR API) L2 A2 regs5 (ms_mem ms) md2).
    { apply (proj2 (call_pre_k_alloc B (aa_MR API) L2 A2 regs5 (ms_mem ms) md2)).
      apply (cr_pre L2 A2 (ms_mem ms) md2 regs5 144 ALLOC_STACK I5'); [lia | lia | unfold ALLOC_STACK; lia
        | rewrite HK0; unfold ALLOC_STACK; lia
        | rewrite S5; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact H16
        | exact (proj2 K5) | rewrite G5a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity | exact Hinit]. }
    assert (Hroom : room_slots (sb_malloc (sb_malloc sb (crt_len b)) (crt_len b)) (crt_len b - 1)).
    { destruct ROOM as (R1 & R2 & R3).
      apply room_slots_big; cbn [sb_malloc sb_live sb_cap sb_bytes]; lia. }
    replace (Z_to_bv 64 CRT_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
    eapply SR_bind.
    { exact (MALLOC fx8 L2 A2 regs5 (ms_mem ms) md2 (crt_len b - 1) (sb_malloc (sb_malloc sb (crt_len b)) (crt_len b))
        Hpre5 I54 G5a0 Hres Hroom). }
    intros c' (L3 & A3 & regs6 & m6 & md3 & res & -> & Hpost & G6 & _ & _ & _ & (d1 & d2 & Hb3 & Hb2') & _ & Hro3 &
      Hgk3 & HU3 & Hinit3 & Hlen3 & Hres3).
    pose proof Hpost as (_ & _ & _ & _ & _ & Hp6 & _).
    assert (I3' : cr_inv L3 A3 m6 md3).
    { apply (cr_inv_call L2 A2 (ms_mem ms) md2 regs5 ALLOC_STACK _ L3 A3 regs6 m6 md3 I5' Hpost);
        [rewrite S5, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen3
        | intros q k Hq; exact (HU3 q k (I3 q k Hq)) | exact Hro3 | exact Hgk3]. }
    assert (FR6 : cr_frame1 m6).
    { destruct FR5 as (j5 & FR5). exists j5.
      apply (cr_cells_call L2 A2 (ms_mem ms) md2 regs5 ALLOC_STACK _ L3 A3 regs6 m6 md3 _ I5' FR5 eq_refl Hpost);
        [lia | intros a []]. }
    rewrite G5a.
    apply (cr_shy fx8 L3 A3 regs6 m6 md3 res O Wt c1 c2 e1 e2 d1 d2 Hfrm8 Hok I3' Hinit3 Hb3).
    + rewrite <- Hb2'. exact Hb2.
    + exact He.
    + exact Hb0.
    + exact Hres3.
    + transitivity (getr regs5 2); [apply (Hp6 2); unfold callee_saved; lia | exact G5b].
    + transitivity (getr regs5 9); [apply (Hp6 9); unfold callee_saved; lia | exact G5s1].
    + exact G6.
    + transitivity (getr regs5 18); [apply (Hp6 18); unfold callee_saved; lia | exact G5s2].
    + transitivity (getr regs5 19); [apply (Hp6 19); unfold callee_saved; lia | exact G5s3].
    + transitivity (getr regs5 22); [apply (Hp6 22); unfold callee_saved; lia | exact G5s6].
    + exact (cr_keep_pres regs5 regs6 K5 Hp6).
    + exact FR6.
Qed.

(** * 0x130b0: malloc of want *)

Lemma cr_ph2 : forall L1 A1 regs2 m2 md1 O c1 c2,
  cr_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = c1 ++ (O, crt_len b) :: c2 -> blocks L A = c1 ++ c2 ->
  res_ok_slots A1 (sb_malloc sb (crt_len b)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs2 10 = Z_to_bv 64 O ->
  getr regs2 18 = Z_to_bv 64 w -> getr regs2 19 = Z_to_bv 64 (crt_len b) ->
  cr_keep regs2 -> cr_frame0 m2 ->
  SR (ms_segs B) (mkCfg (mkst regs2 (Z_to_bv 64 0x130b0) m2 (seg_rom (ms_segs B))) md1) cr_final.
Proof.
  intros L1 A1 regs2 m2 md1 O c1 c2 I Hinit Hb1 Hb0 Hres G2 G10 G18 G19 GK (j & FR).
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  pose proof cr_n as (Hn1 & Hn2 & _).
  pose proof I as ((M1 & _) & I2 & I3 & I4 & I5).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  assert (InO : In (O, crt_len b) (blocks L1 A1)) by (rewrite Hb1; apply crt_in_mid).
  destruct (cr_blk L1 A1 m2 md1 O _ M1 InO) as (HO1 & HO2 & _).
  eapply (crt_runA B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite G10. pose proof SEG2 as S2. unfold crt_seg2_stmt in S2. eapply S2. lia. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs3 -> Hg3. cbn [MState.MS ms_pc_val ms_mem].
  assert (G3a : getr regs3 1 = Z_to_bv 64 0x130c0) by (rewrite Hg3; reflexivity).
  assert (G3b : getr regs3 2 = Z_to_bv 64 (spZ regs - 144)) by (rewrite Hg3; exact G2).
  assert (G3c : getr regs3 10 = Z_to_bv 64 (crt_len b)) by (rewrite Hg3; exact G19).
  assert (G3d : getr regs3 18 = Z_to_bv 64 w) by (rewrite Hg3; exact G18).
  assert (G3e : getr regs3 19 = Z_to_bv 64 (crt_len b)) by (rewrite Hg3; exact G19).
  assert (G3f : getr regs3 22 = Z_to_bv 64 O) by (rewrite Hg3; reflexivity).
  assert (K3 : cr_keep regs3) by (destruct GK as (K3 & K4); split; rewrite Hg3; assumption).
  assert (S3 : spZ regs3 = spZ regs - 144) by (unfold spZ at 1; rewrite G3b; apply MState.unsigned_lit; lia).
  assert (Hpre3 : call_pre B (aa_MR API) L1 A1 regs3 m2 md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs3 m2 md1)).
    apply (cr_pre L1 A1 m2 md1 regs3 144 ALLOC_STACK I); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S3; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj2 K3) | rewrite G3a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity | exact Hinit]. }
  assert (Hroom : room_slots (sb_malloc sb (crt_len b)) (crt_len b)).
  { destruct ROOM as (R1 & R2 & R3). apply room_slots_big; cbn [sb_malloc sb_live sb_cap sb_bytes]; lia. }
  replace (Z_to_bv 64 CRT_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply SR_bind.
  { exact (MALLOC fx L1 A1 regs3 m2 md1 (crt_len b) (sb_malloc sb (crt_len b)) Hpre3 I4 G3c Hres Hroom). }
  intros c' (L2 & A2 & regs4 & m4 & md2 & res & -> & Hpost & G4 & _ & _ & _ & (d1 & d2 & Hb2 & Hb1') & _ & Hro2 &
    Hgk2 & HU2 & Hinit2 & Hlen2 & Hres2).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp4 & _).
  assert (I2' : cr_inv L2 A2 m4 md2).
  { apply (cr_inv_call L1 A1 m2 md1 regs3 ALLOC_STACK _ L2 A2 regs4 m4 md2 I Hpost);
      [rewrite S3, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen2
      | intros q k Hq; exact (HU2 q k (I3 q k Hq)) | exact Hro2 | exact Hgk2]. }
  assert (FR2 : cr_frame0 m4).
  { exists j. apply (cr_cells_call L1 A1 m2 md1 regs3 ALLOC_STACK _ L2 A2 regs4 m4 md2 _ I FR eq_refl Hpost);
      [lia | intros a []]. }
  rewrite G3a.
  apply (cr_mid L2 A2 regs4 m4 md2 O res c1 c2 d1 d2 I2' Hinit2 Hb2).
  - rewrite <- Hb1'. exact Hb1.
  - exact Hb0.
  - exact Hres2.
  - transitivity (getr regs3 2); [apply (Hp4 2); unfold callee_saved; lia | exact G3b].
  - exact G4.
  - transitivity (getr regs3 18); [apply (Hp4 18); unfold callee_saved; lia | exact G3d].
  - transitivity (getr regs3 19); [apply (Hp4 19); unfold callee_saved; lia | exact G3e].
  - transitivity (getr regs3 22); [apply (Hp4 22); unfold callee_saved; lia | exact G3f].
  - exact (cr_keep_pres regs3 regs4 K3 Hp4).
  - exact FR2.
Qed.

(** * 0x13058: the prologue and malloc of out *)

Lemma cr_entry :
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom (ms_segs B))) md) cr_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CRT_STACK = 8336) by reflexivity.
  pose proof cr_n as (Hn1 & Hn2 & _).
  pose proof (crt_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (I0 : cr_inv L A mem md).
  { split.
    { apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p n Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs mem (spZ regs - CRT_STACK) (spZ regs))
    by (rewrite <- SEGS; exact (kb_stk B API HIL CRT_STACK L A regs mem md PRE ltac:(lia))).
  assert (WC : Step.ro_cells rsegs mem w (spec_cells buf b)).
  { assert (Hwf : Cells.cells_wf (spec_cells buf b)) by (cbn; repeat split).
    assert (HL : length (Cells.cells_bytes (spec_cells buf b)) = 80%nat)
      by (rewrite (Cells.cells_bytes_length _ Hwf); reflexivity).
    split; [exact Hwf|]. split; [lia|]. split; [rewrite HL; lia|]. intros i Hi. rewrite HL in Hi.
    pose proof (WB (Z.of_nat i)) as E. unfold spec_bytes in E. rewrite HL in E.
    rewrite <- SEGS, <- cr_mbyte_mrd, E by lia. rewrite Nat2Z.id. reflexivity. }
  eapply (crt_runA B SEGS regs _ mem md); [exact Hh | exact Hlz | | |].
  { unfold rmk. rewrite R10. pose proof SEG1 as S1. unfold crt_seg1_stmt in S1.
    eapply S1; [exact ST | unfold spZ in Hlo |- *; lia | exact FC0 | exact LEN | unfold spZ in SPW; lia | exact WC]. }
  { intros ms Hq. do 16 destruct Hq as [? Hq]. destruct Hq as [-> _]. repeat split; reflexivity. }
  intros ms regs1 Hq Hg1.
  destruct Hq as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & ->
    & MU & WM & FR1).
  cbn [MState.MS ms_pc_val ms_mem].
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x130b0) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 144)) by (rewrite Hg1; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (crt_len b)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 18 = Z_to_bv 64 w) by (rewrite Hg1; reflexivity).
  assert (G1e : getr regs1 19 = Z_to_bv 64 (crt_len b)) by (rewrite Hg1; reflexivity).
  assert (K1 : cr_keep regs1) by (split; rewrite Hg1; reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 144) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (Hout : forall x, ~ Frame.outside [(spZ regs - 144, spZ regs)] x -> spZ regs - 144 <= x < spZ regs)
    by (intros x Hx; cbn [Frame.outside] in Hx; lia).
  assert (WM' : Frame.wmono (ms_segs B) mem m1) by (rewrite SEGS; exact WM).
  assert (Hro1 : ro_agree (ms_segs B) m1).
  { apply (crt_ro_munch B _ mem m1 RO MU). intros a Ha Ho. apply (crt_fs_high B HIL). pose proof (Hout a Ho). lia. }
  assert (I1 : cr_inv L A m1 md).
  { apply (cr_inv_A L A mem md m1 _ I0 MU WM').
    - intros x Hx. destruct (kb_outside_dec [(spZ regs - 144, spZ regs)] (bv_unsigned x)) as [Ho|Ho];
        [rewrite (MU x Ho); exact Hx|].
      apply (crt_pres B mem m1 x); [| exact (WM' x) | exact Hx].
      apply (crt_fs_high B HIL). pose proof (Hout _ Ho). lia.
    - intros x _ Ho. left. pose proof (Hout x Ho). lia.
    - exact Hro1. }
  assert (FR1' : cr_frame0 m1) by (exists junk; exact FR1).
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 m1 md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 m1 md)).
    apply (kb_pre_A B API CRT_STACK 144 ALLOC_STACK L A regs mem md regs1 m1 [(spZ regs - 144, spZ regs)] PRE);
      [lia | unfold ALLOC_STACK; lia | rewrite HK0; unfold ALLOC_STACK; lia | exact S1
      | rewrite S1; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | rewrite Hg1; reflexivity | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact MU | exact WM' | |].
    - intros x _ Hx. cbn [Frame.outside]. split; [lia | exact I].
    - intros x Hx _. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (Hroom : room_slots sb (crt_len b)).
  { destruct ROOM as (R1 & R2 & R3). apply room_slots_big; lia. }
  replace (Z_to_bv 64 CRT_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply SR_bind.
  { exact (MALLOC fx L A regs1 m1 md (crt_len b) sb Hpre1 Hro1 G1c RES Hroom). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & res & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & _ & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I1' : cr_inv L1 A1 m2 md1).
  { apply (cr_inv_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : cr_frame0 m2).
  { exists junk. apply (cr_cells_call L A m1 md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 _ I1 FR1 eq_refl Hpost);
      [lia | intros a []]. }
  rewrite G1a.
  apply (cr_ph2 L1 A1 regs2 m2 md1 res d1 d2 I1' Hinit1 Hb1 Hb0 Hres1).
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - exact G2.
  - transitivity (getr regs1 18); [apply (Hp2 18); unfold callee_saved; lia | exact G1d].
  - transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1e].
  - exact (cr_keep_pres regs1 regs2 K1 Hp2).
  - exact FR2.
Qed.

End Body.

Theorem crt_holds : check_round_trip_contract B API.
Proof.
  intros L A regs mem md w buf b sb _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
  eapply cr_entry; eassumption.
Qed.
End CRT.
