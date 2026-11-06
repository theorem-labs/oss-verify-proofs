(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c. *)
(* Modified by Theorem Labs: for reac-repacer/fuzz_uci. Sections G / G2 are
   libreac/fuzz_decode's released lib/Prog/crt_glue.v with its module paths changed and its one decode-specific
   import (check_braid_c, for braid_map) dropped. Section Body is the invariant layer of that release's
   lib/Prog/check_round_trip.v `Section Body` (cr_inv, cr_pre, cr_inv_call, cr_inv_A, cr_inv_kept, cr_heap_E,
   cr_free_keep, cr_old_in, cr_frame_call), with the one change that the function's own stack size is the section
   variable K instead of decode's CRT_STACK, and with cr_frame_call generalised from decode's fixed frame cell list
   to any (base, cells): so fuzz_uci's check_no_overread and check_value, whose frames differ, share one copy. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/CheckGlue.v, with its module paths and module names changed; 464 of its 559 lines of code are new or changed and 396 lines of the source are left out. *)
(* check_copy walk, fuzz_wire ubsan 6e91fe0b5555 0x13550..0x136d8 (fuzz_wire.c:184-210); new. Form: libreac/fuzz_decode's
   check_round_trip.v (recipes 25e3d17bdb5). The SR run: cc_entry runs cc_segA on the normalized memory (ccg_runN; the
   leaf contracts need mem_inv) up to malloc, MALLOC, then cc_ph_B runs cc_front up to free, FREE, then cc_ph_end runs
   the epilogue and returns. cc_inv keeps, against the entry state, cc_glue.v's cc_mid with the block at c released,
   region / user-block growth, ro_agree and guard_kept; cc_frame the saved ra / s0..s4; cc_keep gp, tp, s5..s11.
   Callees are named Section hypotheses: MALLOC, FREE (Contract.v's malloc_contract / free_contract), CU
   (rp_copy_untag_c.v), MEMCPY (memcpy_c.v), BCMP (bcmp_c.v); and the allocator facts the check_round_trip.v form takes
   (SEGS, AX, CT, ERR, MALPC, FREEPC). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require MState Mem Frame Exec Regs6ss RegisterBridge Cells Step Arr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import rp_copy_untag_c FuzzDup memcpy_c bcmp_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import cc_glue check_copy_c cc_segs.
Import ListNotations.
Local Open Scope Z_scope.

Section CC.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CT : ctx_owned B API.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis MALPC : ms_malloc B = CC_MALLOC.
Hypothesis FREEPC : ms_free B = CC_FREE.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis CU : rp_copy_untag_contract.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis BCMP : bcmp_contract.

Lemma cc_blk : forall Lk Ak mk mdk P n, aa_MR API Lk Ak mk mdk -> In (P, n) (blocks Lk Ak) ->
  4096 <= P /\ P + n <= alloc_ceiling /\ P mod 16 = 0 /\
  forall i, 0 <= i < n -> present mk (P + i) /\ ~ in_img B (P + i) /\ ~ owned B Lk Ak (P + i).
Proof.
  intros Lk Ak mk mdk P n HM Hin.
  destruct (ccg_bu Lk Ak P n Hin) as (p & Hp & <-).
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp) as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  split; [exact (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ p n HM Hp)|].
  intros i Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hp Hi) as (Hpr & _ & _ & Hno).
  split; [exact Hpr|]. split; [exact (ax_blocks_img AX Lk Ak mk mdk p n i HM Hp Hi) | exact Hno].
Qed.

Lemma cc_heap_E : forall Lk Ak mk mdk P n, aa_MR API Lk Ak mk mdk -> In (P, n) (blocks Lk Ak) ->
  forall a, P <= a < P + n -> a < alloc_ceiling /\ ~ in_img B a.
Proof.
  intros Lk Ak mk mdk P n HM Hin a Ha. destruct (cc_blk Lk Ak mk mdk P n HM Hin) as (H1 & H2 & _ & H4).
  split; [lia|]. replace a with (P + (a - P)) by lia. exact (proj1 (proj2 (H4 (a - P) ltac:(lia)))).
Qed.

(* the normalized-memory facts the leaf contracts need, back in the real memory *)
Lemma cc_bytes_rel : forall m m0 a bs, mem_rel (ms_segs B) m m0 -> Mem.bytes_at (ms_segs B) m0 a bs ->
  Mem.bytes_at (ms_segs B) m a bs.
Proof.
  intros m m0 a bs HR (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite (mrd_rel (ms_segs B) m m0 _ HR). exact (H i Hi).
Qed.

Lemma cc_bytes_norm : forall m a bs, ro_agree (ms_segs B) m -> Mem.bytes_at (ms_segs B) m a bs ->
  Mem.bytes_at (ms_segs B) (normalize (ms_segs B) m) a bs.
Proof.
  intros m a bs Hro (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (mrd_rel (ms_segs B) m _ _ (mem_rel_normalize _ m Hro)). exact (H i Hi).
Qed.

Lemma cc_cells_rel : img_low B -> forall m m0 a cs, mem_rel (ms_segs B) m m0 -> Step.rw_cells (ms_segs B) m0 a cs ->
  alloc_ceiling <= a -> Step.rw_cells (ms_segs B) m a cs.
Proof.
  intros HI m m0 a cs HR [[Hwf (Ha & Hl & Hb)] (Wa & Wn & Hw)] Hc.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi. rewrite (mrd_rel (ms_segs B) m m0 _ HR). exact (Hb i Hi).
  - split; [exact Wa|]. split; [exact Wn|]. intros i Hi.
    assert (Hra : Mem.ro_addr (ms_segs B) (Mem.wa (a + i)) = false)
      by (apply ccg_ro_false; [lia | apply (ccg_fs_high B HI); lia]).
    rewrite <- (wview_rel_rw (ms_segs B) m m0 _ HR Hra). exact (Hw i Hi).
Qed.

Section Body.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (c f n kc : Z) (bs : list byte) (b : sbound).
Hypothesis PRE : call_pre_k B (aa_MR API) CC_STACK L A regs mem md.
Hypothesis INIT : st_init_done A = true.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 c.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 f.
Hypothesis R12 : getr regs 12 = Z_to_bv 64 n.
Hypothesis HN : n <= 1600.
Hypothesis HL : Z.of_nat (length bs) = n.
Hypothesis INC : In (c, kc) (blocks L A).
Hypothesis NKC : n <= kc.
Hypothesis INF : exists qf kf, In (qf, kf) (blocks L A) /\ qf <> c /\ qf <= f /\ f + n <= qf + kf.
Hypothesis BC0 : Mem.bytes_at (ms_segs B) mem c bs.
Hypothesis BF0 : Mem.bytes_at (ms_segs B) mem f bs.
Hypothesis RO : ro_agree (ms_segs B) mem.
Hypothesis FRM : frm_zero fp_csr.
Hypothesis RES : res_ok_slots A b.
Hypothesis ROOM : room_slots b (fuzz_dup_size n).

Definition cc_inv (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  cc_mid B API CC_STACK (spZ regs) L A mem md (fun a => a = c) (fun _ => False) L' A' m' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')) /\
  ro_agree (ms_segs B) m' /\ guard_kept B mem m'.

Definition cc_keep (r : bvmap 5 word) : Prop :=
  getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\
  getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\
  getr r 27 = getr regs 27.

Definition cc_frame (m' : word -> option byte) : Prop :=
  Step.rw_cells rsegs m' (spZ regs - 48) [Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18);
    Cells.C8 (getr regs 9); Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)].

Definition cc_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    call_post_x B API CC_STACK L A regs mem md (fun a => a = c) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 (copy_untag_result n bs) /\
    Mem.bytes_at (ms_segs B) mem' c (cu_bytes n bs) /\
    blocks L' A' = blocks L A /\
    blocks_kept B L A mem mem' (fun a => a = c) /\
    guard_kept B mem mem' /\
    ro_agree (ms_segs B) mem' /\
    res_ok_slots A' b /\
    st_init_done A' = true.

Lemma cc_pre : forall Lk Ak mk mdk regsk g K1,
  cc_inv Lk Ak mk mdk -> spZ regsk = spZ regs - g -> 0 <= g -> 0 <= K1 -> g + K1 <= CC_STACK ->
  spZ regsk mod 16 = 0 -> getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) -> st_init_done Ak = true ->
  call_pre_k B (aa_MR API) K1 Lk Ak regsk mk mdk.
Proof.
  intros Lk Ak mk mdk regsk g K1 ((M1 & W1 & B1 & _ & _ & _ & _ & _ & S1) & _) Hsp Hg HK1 HgK H16 H4 Hra Hinit.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _ & Htp & _).
  refine (conj M1 (conj W1 (conj B1 (conj Hra (conj H16 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - lia.
  - lia.
  - intros a Ha. apply S1. left. lia.
  - rewrite H4. exact Htp.
  - intros a Ha. apply S1. right. exact Ha.
  - intros E. rewrite Hinit in E. discriminate.
Qed.

Lemma cc_inv_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cc_inv Lk Ak mk mdk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regs - CC_STACK <= spZ regsk - K2 -> spZ regsk <= spZ regs ->
  (forall a, E2 a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (length (st_regions Ak) <= length (st_regions A2))%nat ->
  (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A2)) ->
  ro_agree (ms_segs B) m2 -> guard_kept B mk m2 ->
  cc_inv L2 A2 m2 md2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 (I1 & I2 & I3 & I4 & I5) Hpost H1 H2 HE HL' HU Hro Hg.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost) as [Hmid _].
  split.
  { apply (cc_drop B API _ _ _ _ _ _ _ (fun a => False \/ E2 a)).
    - eapply (cc_seq B API AX CT); [exact HM | exact I1 | exact Hmid | lia | lia | lia | lia | | exact I2 | exact I3].
      intros a Ha _ He. destruct (HE a He) as [Ha' _]. lia.
    - intros a [[]|He]. exact (HE a He). }
  split; [lia|]. split; [exact HU|]. split; [exact Hro|].
  intros i Hi. rewrite (Hg i Hi). exact (I5 i Hi).
Qed.

Lemma cc_inv_A : forall Lk Ak mk mdk mk' W,
  cc_inv Lk Ak mk mdk ->
  Frame.munch W mk mk' -> Frame.wmono (ms_segs B) mk mk' -> (forall x, mk x <> None -> mk' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - CC_STACK <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lk Ak x /\
      forall p k i, In (p, k) (user_blocks A) -> ptr_addr L p <> c -> 0 <= i < k -> ptr_addr L p + i <> x)) ->
  ro_agree (ms_segs B) mk' ->
  cc_inv Lk Ak mk' mdk.
Proof.
  intros Lk Ak mk mdk mk' W (I1 & I2 & I3 & I4 & I5) Hm Hw Hp HW Hro.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (ccg_img_low B SEGS) as HIL.
  pose proof I1 as (M1 & _).
  split.
  { apply (cc_drop B API _ _ _ _ _ _ _
      (fun x => False \/ (0 <= x < 2 ^ 64 /\ ~ Frame.outside W x /\ ~ (spZ regs - CC_STACK <= x < spZ regs)))).
    - apply (cc_tail B API HIL _ _ _ _ _ _ _ _ Lk Ak mk mdk mk' W); [exact I1 | exact Hm | exact Hw | exact Hp | | |].
      + intros x Hx Hs He. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. apply He. tauto.
      + intros x Hx Ho. destruct (kb_outside_dec W x) as [Hout|Hout]; [exact Hout|]. exfalso.
        destruct (HW x ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
      + intros p k i Hin Hin' Hgo Hi. destruct (kb_outside_dec W (ptr_addr L p + i)) as [Hout|Hout]; [exact Hout|].
        exfalso. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p k HM Hin) as [Hr1 Hr2].
        destruct (HW (ptr_addr L p + i) ltac:(lia) Hout) as [Hs | (_ & _ & _ & H4)];
          [lia | exact (H4 p k i Hin Hgo Hi eq_refl)].
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

Lemma cc_old_in : forall Lk Ak mk mdk, cc_inv Lk Ak mk mdk -> forall y, In y (blocks L A) -> In y (blocks Lk Ak).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & P1 & _) & _ & I3 & _) [a k] Hy.
  destruct (ccg_bu L A a k Hy) as (p & Hp & <-).
  pose proof (I3 p k Hp) as Hp'. rewrite <- (P1 p k Hp Hp'). exact (ccg_ub Lk Ak p k Hp').
Qed.

Lemma cc_free_keep : forall Lk Ak mk mdk p k,
  cc_inv Lk Ak mk mdk -> In (p, k) (user_blocks Ak) -> 0 < k ->
  (forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr Lk p, k) y) ->
  forall q k', In (q, k') (user_blocks A) -> q <> p.
Proof.
  intros Lk Ak mk mdk p k ((M1 & W1 & _ & _ & P1 & _) & _ & I3 & _) Hp Hk HD q k' Hq Eq. subst q.
  pose proof (I3 p k' Hq) as Hpk.
  pose proof (YO10.user_block_ptrs_NoDup Ak W1) as ND.
  pose proof (ccg_fst_unique _ p k' k ND Hpk Hp) as Ek. subst k'.
  pose proof (HD _ (ccg_ub L A p k Hq)) as D.
  rewrite (P1 p k Hq Hpk) in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma cc_frame_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cc_inv Lk Ak mk mdk -> cc_frame mk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regsk <= spZ regs - 48 -> (forall a, E2 a -> a < alloc_ceiling) ->
  cc_frame m2.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 ((M1 & _) & _) FR Hpost Hsp HE.
  pose proof Hpost as (M2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  unfold cc_frame in *. rewrite <- SEGS in FR |- *.
  apply (ccg_cells_mb B mk m2 _ _ FR). intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
  assert (HK0 : CC_STACK = 8240) by reflexivity. pose proof ERR as Herr.
  assert (Hr : alloc_ceiling <= spZ regs - 48 + i < 2 ^ 64) by lia.
  destruct (Hfr (spZ regs - 48 + i)) as [E W].
  - left. exact Hr.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - unfold scratch_k. lia.
  - intros He. pose proof (HE _ He). lia.
  - split; [exact E | intros Hw; apply W; exact Hw].
Qed.

Lemma cc_inv_kept : forall Lk Ak mk mdk, cc_inv Lk Ak mk mdk -> blocks_kept B L A mem mk (fun a => a = c).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & K1 & _) & _ & I3 & _) a k i Hin Hg Hi.
  destruct (ccg_bu L A a k Hin) as (p & Hp & <-). exact (K1 p k i Hp (I3 p k Hp) Hg Hi).
Qed.

Lemma cc_keep_pres : forall r r', cc_keep r -> regs_preserved r r' -> cc_keep r'.
Proof.
  intros r r' (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27) Hp.
  unfold cc_keep.
  repeat split.
  - transitivity (getr r 3); [apply (Hp 3); unfold callee_saved; lia | exact K3].
  - transitivity (getr r 4); [apply (Hp 4); unfold callee_saved; lia | exact K4].
  - transitivity (getr r 21); [apply (Hp 21); unfold callee_saved; lia | exact K21].
  - transitivity (getr r 22); [apply (Hp 22); unfold callee_saved; lia | exact K22].
  - transitivity (getr r 23); [apply (Hp 23); unfold callee_saved; lia | exact K23].
  - transitivity (getr r 24); [apply (Hp 24); unfold callee_saved; lia | exact K24].
  - transitivity (getr r 25); [apply (Hp 25); unfold callee_saved; lia | exact K25].
  - transitivity (getr r 26); [apply (Hp 26); unfold callee_saved; lia | exact K26].
  - transitivity (getr r 27); [apply (Hp 27); unfold callee_saved; lia | exact K27].
Qed.


Lemma cc_ph_end : forall (fx7 : FPState) L6 A6 regs12 m12 md6,
  frm_zero (@fp_csr fx7) -> cc_inv L6 A6 m12 md6 -> blocks L6 A6 = blocks L A ->
  Mem.bytes_at (ms_segs B) m12 c (cu_bytes n bs) -> res_ok_slots A6 b -> st_init_done A6 = true ->
  getr regs12 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs12 8 = Z_to_bv 64 (copy_untag_result n bs) ->
  cc_keep regs12 -> cc_frame m12 ->
  SR (ms_segs B) (mkCfg (@mkst fx7 regs12 (Z_to_bv 64 0x136ac) m12 (seg_rom (ms_segs B))) md6) cc_final.
Proof.
  intros fx7 L6 A6 regs12 m12 md6 Hfrm I Hb6 BC6 Hres Hinit G2 G8 GK FR.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc.
  assert (HK0 : CC_STACK = 8240) by reflexivity.
  pose proof I as ((M6 & _) & _).
  destruct (kb_md B API L6 A6 m12 md6 M6) as [Hh Hlz].
  assert (USP : bv_unsigned (getr regs12 2) = spZ regs - 48) by (rewrite G2; apply MState.unsigned_lit; lia).
  eapply (ccg_runA (fx := fx7) B SEGS regs12 _ m12 md6); [exact Hh | exact Hlz | | |].
  { unfold rmk. eapply cc_seg_epi. rewrite USP. unfold cc_frame in FR. exact FR. }
  { intros ms ->. repeat split; reflexivity. }
  intros ms regs13 -> Hg13. cbn [MState.MS ms_pc_val ms_mem].
  assert (G13a : getr regs13 1 = getr regs 1) by (rewrite Hg13; reflexivity).
  assert (G13b : getr regs13 2 = getr regs 2).
  { rewrite Hg13. cbn. rewrite USP. replace (spZ regs - 48 + 48) with (spZ regs) by lia. apply Z_to_bv_bv_unsigned. }
  assert (G13c : getr regs13 10 = Z_to_bv 64 (copy_untag_result n bs)) by (rewrite Hg13; exact G8).
  assert (P13 : regs_preserved regs regs13).
  { destruct GK as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      first [exact G13b | rewrite Hg13; first [reflexivity | exact K3 | exact K4 | exact K21 | exact K22 | exact K23
        | exact K24 | exact K25 | exact K26 | exact K27]]. }
  rewrite (kb_ret_pc _ Hra).
  apply SR_ret. exists fx7, L6, A6, regs13, m12, md6.
  split; [reflexivity|].
  split; [exact Hfrm|].
  split.
  { destruct I as ((M & W & Bd & Y & P & D & F1 & K1 & S1) & _).
    split; [exact M|]. split; [exact W|]. split; [exact Bd|]. split; [exact Y|]. split; [exact P|].
    split; [exact P13|]. split; [exact D|].
    split; [intros a Ha Ho Ho' Hs; exact (F1 a Ha Ho Ho' Hs (fun H => H))|].
    split; [exact K1 | exact S1]. }
  split; [exact G13c|].
  split; [exact BC6|].
  split; [exact Hb6|].
  split; [exact (cc_inv_kept _ _ _ _ I)|].
  destruct I as (_ & _ & _ & Hro' & Hg').
  split; [exact Hg'|]. split; [exact Hro'|].
  split; [exact Hres | exact Hinit].
Qed.

Lemma cc_ph_B : forall (fx1 : FPState) L1 A1 regs2 m2 md1 u d1 d2,
  frm_zero (@fp_csr fx1) -> cc_inv L1 A1 m2 md1 -> st_init_done A1 = true ->
  blocks L1 A1 = d1 ++ (u, fuzz_dup_size n) :: d2 -> blocks L A = d1 ++ d2 ->
  res_ok_slots A1 (sb_malloc b (fuzz_dup_size n)) ->
  getr regs2 2 = Z_to_bv 64 (spZ regs - 48) -> getr regs2 8 = Z_to_bv 64 (copy_untag_result n bs) ->
  getr regs2 9 = Z_to_bv 64 c -> getr regs2 10 = Z_to_bv 64 u -> getr regs2 19 = Z_to_bv 64 n ->
  getr regs2 20 = Z_to_bv 64 f ->
  cc_keep regs2 -> cc_frame m2 ->
  Mem.bytes_at (ms_segs B) m2 c (cu_bytes n bs) -> Mem.bytes_at (ms_segs B) m2 f bs ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 0x13590) m2 (seg_rom (ms_segs B))) md1) cc_final.
Proof.
  intros fx1 L1 A1 regs2 m2 md1 u d1 d2 Hfrm I Hinit Hb1 Hb0 Hres G2 G8 G9 G10 G19 G20 GK FR BC2 BF2.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc. pose proof ERR as Herr'.
  assert (HK0 : CC_STACK = 8240) by reflexivity.
  pose proof I as ((M1 & _) & _ & I3 & I4 & _).
  destruct (kb_md B API L1 A1 m2 md1 M1) as [Hh Hlz].
  pose proof (ccg_img_low B SEGS) as HIL.
  assert (HN0 : 0 <= n) by lia.
  pose proof (fds_cases n HN0) as (DS1 & DS2 & DS3).
  assert (InU : In (u, fuzz_dup_size n) (blocks L1 A1)) by (rewrite Hb1; apply ccg_in_mid).
  destruct (cc_blk L1 A1 m2 md1 u _ M1 InU) as (HU1 & HU2 & _ & HUi).
  assert (PW1 : pairwise ranges_disjoint (d1 ++ (u, fuzz_dup_size n) :: d2))
    by (rewrite <- Hb1; exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ M1)).
  destruct (cc_blk L A mem md c kc HM INC) as (HC1 & HC2 & _ & _).
  destruct INF as (qf & kf & Hqf & Hqfc & Hf1 & Hf2).
  destruct (cc_blk L A mem md qf kf HM Hqf) as (HF1 & HF2 & _ & _).
  assert (DUC : ranges_disjoint (u, fuzz_dup_size n) (c, kc))
    by (apply (ccg_pw_mid d1 d2 _ _ PW1); rewrite <- Hb0; exact INC).
  assert (DUF : ranges_disjoint (u, fuzz_dup_size n) (qf, kf))
    by (apply (ccg_pw_mid d1 d2 _ _ PW1); rewrite <- Hb0; exact Hqf).
  unfold ranges_disjoint in DUC, DUF. cbn [fst snd] in DUC, DUF.
  assert (S2 : spZ regs2 = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; lia).
  assert (RO2 : ro_agree rsegs m2) by (rewrite <- SEGS; exact I4).
  pose proof (mem_rel_normalize rsegs m2 RO2) as HR2.
  assert (BCn : Mem.bytes_at rsegs (normalize rsegs m2) c (cu_bytes n bs))
    by (rewrite <- SEGS; apply cc_bytes_norm; [exact I4 | exact BC2]).
  assert (BFn : Mem.bytes_at rsegs (normalize rsegs m2) f bs)
    by (rewrite <- SEGS; apply cc_bytes_norm; [exact I4 | exact BF2]).
  assert (STU : Frame.stk rsegs (normalize rsegs m2) u (u + fuzz_dup_size n)).
  { rewrite <- SEGS. apply (ccg_blk_stk B SEGS m2 u _ I4); [lia | lia |].
    intros i Hi. destruct (HUi i Hi) as (X1 & X2 & _). split; assumption. }
  destruct (Frame.stk_carve rsegs (normalize rsegs m2) u (u + fuzz_dup_size n) (Z.to_nat (fuzz_dup_size n)) STU
    ltac:(lia)) as [_ (junk & WUn)].
  replace (u + fuzz_dup_size n - Z.of_nat (Z.to_nat (fuzz_dup_size n))) with u in WUn by lia.
  eapply (ccg_runN B SEGS regs2 _ m2 md1); [exact Hh | exact Hlz | exact RO2 | | |].
  { unfold rmk. rewrite G8, G9, G10, G19, G20.
    eapply cc_front with (m := normalize rsegs m2) (c := c) (f := f) (n := n) (u := u) (bs := bs) (junk := junk).
    all: first [exact MEMCPY | exact BCMP | exact BCn | exact BFn | exact WUn | exact (mem_inv_normalize rsegs m2)
               | exact HL | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs3 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
    MU & WM & _) Hrel Hsame Hg3.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  pose proof (munch_rel rsegs _ m2 _ (ms_mem ms) m' HR2 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs m2 _ (ms_mem ms) m' HR2 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs m2 (ms_mem ms) RO2 Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (PRES : forall x, m2 x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec [(u, u + fuzz_dup_size n)] (bv_unsigned x)) as [Hout|Hout];
      [rewrite (MU7 x Hout); exact Hx|].
    apply (ccg_pres B m2 (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    cbn [Frame.outside] in Hout.
    apply (ccg_fs_none B SEGS). destruct (HUi (bv_unsigned x - u) ltac:(lia)) as (_ & Hn & _).
    replace (u + (bv_unsigned x - u)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (I3' : cc_inv L1 A1 (ms_mem ms) md1).
  { apply (cc_inv_A L1 A1 m2 md1 (ms_mem ms) [(u, u + fuzz_dup_size n)] I MU7 WM7 PRES); [|exact RO7].
    intros x Hx Hout. cbn [Frame.outside] in Hout. right.
    destruct (HUi (x - u) ltac:(lia)) as (_ & Hn1 & Hn2).
    replace (u + (x - u)) with x in Hn1, Hn2 by ring.
    split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
    intros p k i Hp _ Hi E. pose proof (ccg_pw_mid d1 d2 _ _ PW1 ltac:(rewrite <- Hb0; exact (ccg_ub L A p k Hp))) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
  assert (FR3 : cc_frame (ms_mem ms)).
  { unfold cc_frame in *. rewrite <- SEGS. apply (ccg_cells_keep B m2 (ms_mem ms)); [rewrite SEGS; exact FR|].
    intros i Hi. change (Z.of_nat (Cells.cells_size _)) with 48 in Hi.
    apply MU7. rewrite MState.unsigned_lit by lia. cbn [Frame.outside]. split; [lia | exact Logic.I]. }
  assert (BC3 : Mem.bytes_at (ms_segs B) (ms_mem ms) c (cu_bytes n bs)).
  { rewrite SEGS in BC2 |- *. apply (Frame.bytes_at_transport rsegs _ _ _ _ _ BC2 MU7).
    cbn [Frame.disjoint_from]. rewrite cu_bytes_len by exact HL. rewrite HL. lia. }
  cbn [MState.MS ms_pc_val ms_fregs ms_fcsr ms_regs] in *.
  assert (G3a : getr regs3 1 = Z_to_bv 64 0x136ac) by (rewrite Hg3; reflexivity).
  assert (G3b : getr regs3 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg3; exact G2).
  assert (G3c : getr regs3 10 = Z_to_bv 64 u) by (rewrite Hg3; reflexivity).
  assert (G3d : getr regs3 8 = Z_to_bv 64 (copy_untag_result n bs)) by (rewrite Hg3; reflexivity).
  assert (K3 : cc_keep regs3).
  { destruct GK as (K3 & K4 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
    unfold cc_keep; repeat split; rewrite Hg3; assumption. }
  assert (S3 : spZ regs3 = spZ regs - 48) by (unfold spZ at 1; rewrite G3b; apply MState.unsigned_lit; lia).
  destruct (ccg_bu L1 A1 u _ InU) as (p & Hp & Ep).
  assert (Hpre3 : call_pre B (aa_MR API) L1 A1 regs3 (ms_mem ms) md1).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L1 A1 regs3 (ms_mem ms) md1)).
    apply (cc_pre L1 A1 (ms_mem ms) md1 regs3 48 ALLOC_STACK I3'); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S3; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 K3)) | rewrite G3a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact Hinit]. }
  replace (Z_to_bv 64 CC_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite FREEPC; reflexivity).
  eapply SR_bind.
  { apply (FREE (mkFP fp_regs fp_csr) L1 A1 regs3 (ms_mem ms) md1 p (fuzz_dup_size n) (sb_malloc b (fuzz_dup_size n))
      Hpre3 RO7 Hp).
    - rewrite G3c, Ep. reflexivity.
    - exact Hres. }
  intros c' (L6 & A6 & regs12 & m12 & md6 & -> & Hpost & (e1 & e2 & He1 & He2) & Hkept & Hro6 & Hgk6 & Hub6 &
    Hinit6 & Hlen6 & Hres6).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp12 & _).
  rewrite Ep in He1, Hkept.
  assert (ND1 : ~ In (u, fuzz_dup_size n) (d1 ++ d2)) by (apply (ccg_notin d1 d2 _ PW1); cbn; lia).
  assert (Hb6 : blocks L6 A6 = blocks L A).
  { rewrite He2, Hb0. symmetry. apply (ccg_rm (u, fuzz_dup_size n) d1 d2 e1 e2 ND1). rewrite <- Hb1. exact He1. }
  assert (HD1 : forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr L1 p, fuzz_dup_size n) y).
  { intros y Hy. rewrite Ep. apply (ccg_pw_mid d1 d2 _ y PW1). rewrite <- Hb0. exact Hy. }
  assert (HU6 : forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A6)).
  { intros q k Hq. apply Hub6; [exact (I3 q k Hq)
      | exact (cc_free_keep L1 A1 (ms_mem ms) md1 p _ I3' Hp ltac:(lia) HD1 q k Hq)]. }
  assert (I6 : cc_inv L6 A6 m12 md6).
  { apply (cc_inv_call L1 A1 (ms_mem ms) md1 regs3 ALLOC_STACK _ L6 A6 regs12 m12 md6 I3' Hpost);
      [rewrite S3, HK0; unfold ALLOC_STACK; lia | lia | | exact Hlen6 | exact HU6 | exact Hro6 | exact Hgk6].
    intros a Ha. rewrite Ep in Ha. exact (cc_heap_E L1 A1 m2 md1 u _ M1 InU a Ha). }
  assert (FR6 : cc_frame m12).
  { apply (cc_frame_call L1 A1 (ms_mem ms) md1 regs3 ALLOC_STACK _ L6 A6 regs12 m12 md6 I3' FR3 Hpost); [lia|].
    intros a Ha. rewrite Ep in Ha. lia. }
  assert (BC6 : Mem.bytes_at (ms_segs B) m12 c (cu_bytes n bs)).
  { apply (ccg_bytes_mb B (ms_mem ms) m12 c _ BC3). intros i Hi. rewrite cu_bytes_len in Hi by exact HL.
    apply (Hkept c kc i (cc_old_in L1 A1 m2 md1 I (c, kc) INC)); lia. }
  rewrite G3a.
  apply (cc_ph_end (mkFP fp_regs fp_csr) L6 A6 regs12 m12 md6); [exact Hfrm | exact I6 | exact Hb6 | exact BC6
    | rewrite sb_free_malloc in Hres6; exact Hres6 | exact (Hinit6 Hinit) | | | | exact FR6].
  - transitivity (getr regs3 2); [apply (Hp12 2); unfold callee_saved; lia | exact G3b].
  - transitivity (getr regs3 8); [apply (Hp12 8); unfold callee_saved; lia | exact G3d].
  - exact (cc_keep_pres regs3 regs12 K3 Hp12).
Qed.

Lemma cc_entry :
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 CHECK_COPY) mem (seg_rom (ms_segs B))) md) cc_final.
Proof.
  pose proof PRE as (HM & HWF & HB & Hra & H16 & Hlo & Hhi & HW & Htp & Herr & Haux).
  pose proof alloc_ceiling_value as Hc. pose proof ERR as Herr'.
  assert (HK0 : CC_STACK = 8240) by reflexivity.
  pose proof (ccg_img_low B SEGS) as HIL.
  destruct (kb_md B API L A mem md HM) as [Hh Hlz].
  assert (HN0 : 0 <= n) by lia.
  pose proof (fds_cases n HN0) as (DS1 & DS2 & DS3).
  destruct (cc_blk L A mem md c kc HM INC) as (HC1 & HC2 & _ & HCi).
  destruct INF as (qf & kf & Hqf & Hqfc & Hf1 & Hf2).
  destruct (cc_blk L A mem md qf kf HM Hqf) as (HF1 & HF2 & _ & _).
  assert (PW0 : pairwise ranges_disjoint (blocks L A)) by exact (mr_blocks_disjoint _ _ (aa_laws API) _ _ _ _ HM).
  pose proof (ccg_pw_two _ _ _ PW0 INC Hqf ltac:(cbn; congruence)) as DCF.
  unfold ranges_disjoint in DCF. cbn [fst snd] in DCF.
  assert (RO0 : ro_agree rsegs mem) by (rewrite <- SEGS; exact RO).
  pose proof (mem_rel_normalize rsegs mem RO0) as HR0.
  assert (I0 : cc_inv L A mem md).
  { split.
    { apply cc_of_kb. apply (kb_mid_refl B API); [exact HM | exact HWF | exact HB |].
      intros a [Ha|Ha]; [exact (HW a Ha) | exact (Herr a Ha)]. }
    split; [lia|]. split; [intros p k Hp; exact Hp|]. split; [exact RO|]. intros i Hi. reflexivity. }
  assert (ST : Frame.stk rsegs (normalize rsegs mem) (spZ regs - CC_STACK) (spZ regs)).
  { rewrite <- SEGS. apply (ccg_stk_norm B HIL); [exact (kb_stk B API HIL CC_STACK L A regs mem md PRE ltac:(lia))
      | exact RO | lia]. }
  assert (CBn : Arr.u8arr rsegs (normalize rsegs mem) c bs).
  { split.
    - rewrite <- SEGS. apply cc_bytes_norm; [exact RO | exact BC0].
    - rewrite <- SEGS. apply (ccg_wr_norm B SEGS mem c _ RO); [lia | lia |]. intros i Hi.
      destruct (HCi i ltac:(lia)) as (X1 & X2 & _). split; assumption. }
  eapply (ccg_runN B SEGS regs _ mem md); [exact Hh | exact Hlz | exact RO0 | | |].
  { unfold rmk. rewrite R10, R11, R12.
    eapply (cc_segA CU); [exact ST | unfold spZ in *; lia | exact (mem_inv_normalize rsegs mem) | lia | exact HL
      | exact CBn | lia | unfold spZ in *; lia | lia]. }
  { intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
    repeat split; reflexivity. }
  intros ms s0 regs1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n & -> &
    MU & WM & _ & FR1 & BC1) Hrel Hsame Hg1.
  destruct Hrel as (_ & _ & _ & _ & _ & _ & _ & HR). cbn [ms_mem MState.MS] in HR.
  change (bv_unsigned (getr regs 2)) with (spZ regs) in MU, FR1.
  set (W := (spZ regs - 80, spZ regs) :: cu_footprint c n bs) in MU.
  pose proof (munch_rel rsegs _ mem _ (ms_mem ms) m1n HR0 HR Hsame MU) as MU7.
  pose proof (wmono_rel rsegs mem _ (ms_mem ms) m1n HR0 HR Hsame WM) as WM7.
  pose proof (ro_agree_same rsegs mem (ms_mem ms) RO0 Hsame) as RO7.
  rewrite <- SEGS in WM7, RO7.
  assert (HWin : forall x, ~ Frame.outside W x -> (spZ regs - 80 <= x < spZ regs) \/ (c + 12 <= x < c + n - 4 /\ 50 <= n)).
  { intros x Hx. unfold W, cu_footprint in Hx. destruct (cu_moves n bs) eqn:E.
    - unfold cu_moves in E. apply andb_prop in E as [E _]. apply Z.leb_le in E. cbn [Frame.outside] in Hx. lia.
    - cbn [Frame.outside] in Hx. lia. }
  assert (PRES : forall x, mem x <> None -> ms_mem ms x <> None).
  { intros x Hx. destruct (kb_outside_dec W (bv_unsigned x)) as [Hout|Hout]; [rewrite (MU7 x Hout); exact Hx|].
    apply (ccg_pres B mem (ms_mem ms) x); [| exact (WM7 x) | exact Hx].
    pose proof (bv_unsigned_in_range 64 x) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    destruct (HWin _ Hout) as [Hs | (Hs & _)].
    - apply (ccg_fs_high B HIL). lia.
    - apply (ccg_fs_none B SEGS). destruct (HCi (bv_unsigned x - c) ltac:(lia)) as (_ & Hn & _).
      replace (c + (bv_unsigned x - c)) with (bv_unsigned x) in Hn by ring. exact Hn. }
  assert (I1 : cc_inv L A (ms_mem ms) md).
  { apply (cc_inv_A L A mem md (ms_mem ms) W I0 MU7 WM7 PRES); [|exact RO7].
    intros x Hx Hout. destruct (HWin x Hout) as [Hs | (Hs & H50)]; [left; lia | right].
    destruct (HCi (x - c) ltac:(lia)) as (_ & Hn1 & Hn2).
    replace (c + (x - c)) with x in Hn1, Hn2 by ring.
    split; [lia|]. split; [exact Hn1|]. split; [exact Hn2|].
    intros p k i Hp Hpc Hi E.
    pose proof (ccg_pw_two _ _ _ PW0 INC (ccg_ub L A p k Hp) ltac:(cbn [fst]; intros E'; apply Hpc; symmetry; exact E')) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. lia. }
  cbn [MState.MS ms_pc_val ms_fregs ms_fcsr ms_regs] in *.
  assert (USP : bv_unsigned (getr regs 2) + -48 = spZ regs - 48) by (unfold spZ; lia).
  assert (G1a : getr regs1 1 = Z_to_bv 64 0x13590) by (rewrite Hg1; reflexivity).
  assert (G1b : getr regs1 2 = Z_to_bv 64 (spZ regs - 48)) by (rewrite Hg1; cbn; rewrite USP; reflexivity).
  assert (G1c : getr regs1 10 = Z_to_bv 64 (fuzz_dup_size n)) by (rewrite Hg1; reflexivity).
  assert (G1d : getr regs1 8 = Z_to_bv 64 (copy_untag_result n bs)) by (rewrite Hg1; reflexivity).
  assert (G1e : getr regs1 9 = Z_to_bv 64 c) by (rewrite Hg1; reflexivity).
  assert (G1f : getr regs1 19 = Z_to_bv 64 n) by (rewrite Hg1; reflexivity).
  assert (G1g : getr regs1 20 = Z_to_bv 64 f) by (rewrite Hg1; reflexivity).
  assert (K1 : cc_keep regs1) by (unfold cc_keep; repeat split; rewrite Hg1; reflexivity).
  assert (S1 : spZ regs1 = spZ regs - 48) by (unfold spZ at 1; rewrite G1b; apply MState.unsigned_lit; lia).
  assert (FR1' : cc_frame (ms_mem ms)).
  { unfold cc_frame. rewrite <- SEGS. apply (cc_cells_rel HIL (ms_mem ms) m1n); [rewrite SEGS; exact HR | | lia].
    rewrite SEGS. replace (spZ regs - 48) with (spZ regs + -48) by lia. exact FR1. }
  assert (BC1' : Mem.bytes_at (ms_segs B) (ms_mem ms) c (cu_bytes n bs)).
  { apply (cc_bytes_rel (ms_mem ms) m1n); rewrite SEGS; [exact HR | exact BC1]. }
  assert (BF1' : Mem.bytes_at (ms_segs B) (ms_mem ms) f bs).
  { rewrite SEGS in BF0 |- *. apply (Frame.bytes_at_transport rsegs _ _ _ _ _ BF0 MU7).
    unfold W, cu_footprint. destruct (cu_moves n bs); cbn [Frame.disjoint_from]; rewrite HL; lia. }
  assert (Hpre1 : call_pre B (aa_MR API) L A regs1 (ms_mem ms) md).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L A regs1 (ms_mem ms) md)).
    apply (cc_pre L A (ms_mem ms) md regs1 48 ALLOC_STACK I1); [lia | lia | unfold ALLOC_STACK; lia
      | rewrite HK0; unfold ALLOC_STACK; lia
      | rewrite S1; replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia; rewrite Z_mod_plus_full; exact H16
      | exact (proj1 (proj2 K1)) | rewrite G1a; unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity
      | exact INIT]. }
  replace (Z_to_bv 64 CC_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MALPC; reflexivity).
  eapply SR_bind.
  { exact (MALLOC (mkFP fp_regs fp_csr) L A regs1 (ms_mem ms) md (fuzz_dup_size n) b Hpre1 RO7 G1c RES ROOM). }
  intros c' (L1 & A1 & regs2 & m2 & md1 & u & -> & Hpost & G2 & _ & _ & _ & (d1 & d2 & Hb1 & Hb0) & Hkept & Hro2 &
    Hgk2 & HU1 & Hinit1 & Hlen1 & Hres1).
  pose proof Hpost as (_ & _ & _ & _ & _ & Hp2 & _).
  assert (I2 : cc_inv L1 A1 m2 md1).
  { apply (cc_inv_call L A (ms_mem ms) md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 Hpost);
      [rewrite S1, HK0; unfold ALLOC_STACK; lia | lia | intros a [] | exact Hlen1 | exact HU1 | exact Hro2
      | exact Hgk2]. }
  assert (FR2 : cc_frame m2).
  { apply (cc_frame_call L A (ms_mem ms) md regs1 ALLOC_STACK _ L1 A1 regs2 m2 md1 I1 FR1' Hpost); [lia | intros a []]. }
  assert (BC2 : Mem.bytes_at (ms_segs B) m2 c (cu_bytes n bs)).
  { apply (ccg_bytes_mb B (ms_mem ms) m2 c _ BC1'). intros i Hi. rewrite cu_bytes_len in Hi by exact HL.
    apply (Hkept c kc i INC); [intros [] | lia]. }
  assert (BF2 : Mem.bytes_at (ms_segs B) m2 f bs).
  { apply (ccg_bytes_mb B (ms_mem ms) m2 f _ BF1'). intros i Hi.
    replace (f + i) with (qf + (f - qf + i)) by ring.
    apply (Hkept qf kf (f - qf + i) Hqf); [intros [] | lia]. }
  rewrite G1a.
  apply (cc_ph_B (mkFP fp_regs fp_csr) L1 A1 regs2 m2 md1 u d1 d2); [exact FRM | exact I2 | exact Hinit1 | exact Hb1
    | exact Hb0 | exact Hres1 | | | | exact G2 | | | | exact FR2 | exact BC2 | exact BF2].
  - transitivity (getr regs1 2); [apply (Hp2 2); unfold callee_saved; lia | exact G1b].
  - transitivity (getr regs1 8); [apply (Hp2 8); unfold callee_saved; lia | exact G1d].
  - transitivity (getr regs1 9); [apply (Hp2 9); unfold callee_saved; lia | exact G1e].
  - transitivity (getr regs1 19); [apply (Hp2 19); unfold callee_saved; lia | exact G1f].
  - transitivity (getr regs1 20); [apply (Hp2 20); unfold callee_saved; lia | exact G1g].
  - exact (cc_keep_pres regs1 regs2 K1 Hp2).
Qed.

End Body.

Theorem check_copy_holds : check_copy_contract B API.
Proof.
  intros L A regs mem md c f n kc bs b _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
  eapply cc_entry; eassumption.
Qed.

End CC.

