(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame Arr Tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Local Open Scope Z_scope.

Section A.
Context {HCEIL : HasCeiling}.
Variable segs : list Segment.
Variable AI : alloc_if segs.
Notation L := (ai_L segs AI).
Notation K := (ai_K segs AI).
Notation BL := (list (block K)).
Notation mem := (word -> option byte).

Definition client_range (LB : BL) (SP A n : Z) : Prop :=
  forall a, A <= a < A + n -> client_addr AI LB SP a.

#[using="Type"] Lemma client_range_above : forall LB SP A n, SP <= A -> client_range LB SP A n.
Proof. intros LB SP A n H a Ha. left. lia. Qed.

#[using="Type"] Lemma client_range_block : forall LB SP A n (b : block K),
  In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> client_range LB SP A n.
Proof.
  intros LB SP A n b HIN H1 H2 a Ha. right; right. exists b. split; [exact HIN|]. lia.
Qed.

#[using="Type"] Lemma client_range_static : forall LB SP A n lo hi,
  al_client_static L lo hi -> lo <= A -> A + n <= hi -> client_range LB SP A n.
Proof.
  intros LB SP A n lo hi HS H1 H2 a Ha. right; left. exists lo, hi. split; [exact HS|]. lia.
Qed.

#[using="Type"] Lemma heap_pres_bytes_at : forall LB SP m m' A bs,
  heap_pres AI LB SP m m' -> bytes_at segs m A bs -> client_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at segs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma heap_pres_wr_at : forall LB SP m m' A n,
  heap_pres AI LB SP m m' -> wr_at segs m A n -> client_range LB SP A n -> wr_at segs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma heap_pres_rw_cells : forall LB SP m m' A cs,
  heap_pres AI LB SP m m' -> rw_cells segs m A cs -> client_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply heap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply heap_pres_wr_at; eauto.
Qed.

#[using="Type"] Lemma heap_pres_weaken : forall LB LB' SP SP' m m',
  heap_pres AI LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> heap_pres AI LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

#[using="Type"] Lemma heap_pres_of_munch : forall LB SP W m m',
  munch W m m' -> wmono segs m m' ->
  (forall a, 0 <= a < 2^64 -> client_addr AI LB SP a -> outside W a) ->
  heap_pres AI LB SP m m'.
Proof.
  intros LB SP W m m' MU WM HO a Ha Hc. split.
  - unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia.
    unfold wa. apply E. apply HO; assumption.
  - intros Hw. apply WM. exact Hw.
Qed.

#[using="Type"] Lemma lb_remove_sub : forall k (LB : BL) b, In b (lb_remove (ai_K_eqb segs AI) k LB) -> In b LB.
Proof.
  induction LB as [|b0 LB IH]; intros b H; [exact H|].
  unfold lb_remove in *. rewrite list.filter_cons in H. destruct (decide _) as [D|D].
  - destruct H as [->|H]; [left; reflexivity| right; apply IH; exact H].
  - right. apply IH. exact H.
Qed.

#[using="Type"] Lemma lb_remove_neq : forall k (LB : BL) b, In b (lb_remove (ai_K_eqb segs AI) k LB) -> blk_id b <> k.
Proof.
  induction LB as [|b0 LB IH]; intros b H; [destruct H|].
  unfold lb_remove in *. rewrite list.filter_cons in H. destruct (decide _) as [D|D].
  - destruct H as [->|H]; [| apply IH; exact H].
    intros E. apply Is_true_true_1 in D. rewrite <- E in D.
    destruct (ai_K_eqb segs AI (blk_id b) (blk_id b)) eqn:Q; [discriminate|].
    pose proof (proj2 (ai_K_eqb_eq segs AI (blk_id b) (blk_id b)) eq_refl). congruence.
  - apply IH. exact H.
Qed.

Record layout_ok : Prop := mkLO {
  lo_static_img : forall lo hi, al_client_static L lo hi -> exists w, In w (al_img L) /\ fst w <= lo /\ hi <= snd w;
  lo_errno_img : exists w, In w (al_img L) /\ fst w <= al_errno L /\ al_errno L + 4 <= snd w;
  lo_img_ceiling : forall w, In w (al_img L) -> snd w <= alloc_ceiling;
  lo_errno_pos : 0 <= al_errno L
}.

Definition seg_ok (LB : BL) (SP : Z) (W : list ivl) : Prop :=
  Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
                    \/ (forall a, fst iv <= a < snd iv -> ~ client_addr AI LB SP a)) W.

#[using="Type"] Lemma outside_of_forall : forall W a,
  Forall (fun iv : ivl => ~ (fst iv <= a < snd iv)) W -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a H; cbn; [exact I|].
  inversion H as [|x l H1 H2]; subst. cbn in H1. split; [exact H1| apply IH; exact H2].
Qed.

#[using="Type"] Lemma heap_pres_seg : forall s LB0 LB SP W m0 m m',
  layout_ok -> RHEAP segs AI s LB0 m0 -> (forall b, In b LB -> In b LB0) ->
  munch W m m' -> wmono segs m m' -> seg_ok LB SP W ->
  heap_pres AI LB SP m m'.
Proof.
  intros s LB0 LB SP W m0 m m' LO HR HSUB MU WM OK.
  eapply heap_pres_of_munch; [exact MU| exact WM|].
  intros a Ha Hc. apply outside_of_forall. unfold seg_ok in OK.
  eapply Forall_impl; [| exact OK]. cbn. intros [lo' hi'] [[H1 H2]|H3]; cbn in *.
  - destruct Hc as [Hc|[(lo & hi & Hst & Hr)|(b & Hb & Hr)]].
    + lia.
    + destruct (lo_static_img LO lo hi Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling LO w Hw). lia.
    + destruct (ai_block_range segs AI s LB0 m0 b HR (HSUB b Hb)) as (_ & _ & _ & Hc' & _). lia.
  - intros Hr. exact (H3 a Hr Hc).
Qed.

#[using="Type"] Lemma fresh_block_not_client : forall s LB' LB (b : block K) SP m a,
  layout_ok -> RHEAP segs AI s LB' m -> In b LB' -> (forall b0, In b0 LB -> In b0 LB' /\ b0 <> b) ->
  alloc_ceiling <= SP ->
  blk_addr b <= a < blk_addr b + blk_size b -> ~ client_addr AI LB SP a.
Proof.
  intros s LB' LB b SP m a LO HR HIN HSUB HSP Hr [Hc|[(lo & hi & Hst & Hl)|(b0 & Hb0 & Hr0)]].
  - destruct (ai_block_range segs AI s LB' m b HR HIN) as (_ & _ & _ & Hc' & _). lia.
  - destruct (lo_static_img LO lo hi Hst) as (w & Hw & W1 & W2).
    destruct (ai_block_range segs AI s LB' m b HR HIN) as (_ & _ & _ & _ & HF).
    rewrite Forall_forall in HF. specialize (HF w Hw). lia.
  - destruct (HSUB b0 Hb0) as [HIN0 NE].
    pose proof (ai_blocks_disjoint segs AI s LB' m b0 b HR HIN0 HIN NE). lia.
Qed.

#[using="Type"] Lemma fresh_block_disjoint_errno : forall s LB (b : block K) m,
  layout_ok -> RHEAP segs AI s LB m -> In b LB ->
  al_errno L + 4 <= blk_addr b \/ blk_addr b + blk_size b <= al_errno L.
Proof.
  intros s LB b m LO HR HIN. destruct (lo_errno_img LO) as (w & Hw & W1 & W2).
  destruct (ai_block_range segs AI s LB m b HR HIN) as (_ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. specialize (HF w Hw). lia.
Qed.

Definition hpx (W : list ivl) (LB : BL) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> client_addr AI LB SP a -> outside W a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma hpx_refl : forall W LB SP m, hpx W LB SP m m.
Proof. intros W LB SP m a _ _ _; auto. Qed.

#[using="Type"] Lemma hpx_trans : forall W LB SP m1 m2 m3, hpx W LB SP m1 m2 -> hpx W LB SP m2 m3 -> hpx W LB SP m1 m3.
Proof.
  intros W LB SP m1 m2 m3 H1 H2 a Ha Hc Ho. destruct (H1 a Ha Hc Ho) as [E1 W1]. destruct (H2 a Ha Hc Ho) as [E2 W2].
  split; [congruence| auto].
Qed.

#[using="Type"] Lemma hpx_of_heap_pres : forall W LB SP m m', heap_pres AI LB SP m m' -> hpx W LB SP m m'.
Proof. intros W LB SP m m' H a Ha Hc _. apply H; assumption. Qed.

#[using="Type"] Lemma heap_pres_of_hpx : forall W LB SP m m',
  hpx W LB SP m m' -> (forall a, 0 <= a < 2^64 -> client_addr AI LB SP a -> outside W a) -> heap_pres AI LB SP m m'.
Proof. intros W LB SP m m' H HO a Ha Hc. apply H; auto. Qed.

#[using="Type"] Lemma hpx_weaken : forall W W' LB LB' SP SP' m m',
  hpx W LB SP m m' -> sub_fp W W' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> hpx W' LB' SP' m m'.
Proof.
  intros W W' LB LB' SP SP' m m' H HW HS HL a Ha Hc Ho. apply H; [exact Ha| | apply HW; exact Ho].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

#[using="Type"] Lemma hpx_seg : forall s LB0 LB SP W W0 m0 m m',
  layout_ok -> RHEAP segs AI s LB0 m0 -> (forall b, In b LB -> In b LB0) ->
  munch W0 m m' -> wmono segs m m' ->
  Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
                    \/ (forall a, fst iv <= a < snd iv -> ~ client_addr AI LB SP a)
                    \/ inside W (fst iv) (snd iv - fst iv)) W0 ->
  hpx W LB SP m m'.
Proof.
  intros s LB0 LB SP W W0 m0 m m' LO HR HSUB MU WM OK a Ha Hc Ho. split; [| intros Hw; apply WM; exact Hw].
  unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia.
  unfold wa. apply E. apply outside_of_forall.
  eapply Forall_impl; [| exact OK]. cbn. intros [lo' hi'] [[H1 H2]|[H3|H4]]; cbn in *.
  - destruct Hc as [Hc|[(lo & hi & Hst & Hr)|(b & Hb & Hr)]].
    + lia.
    + destruct (lo_static_img LO lo hi Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling LO w Hw). lia.
    + destruct (ai_block_range segs AI s LB0 m0 b HR (HSUB b Hb)) as (_ & _ & _ & Hc' & _). lia.
  - intros Hr. exact (H3 a Hr Hc).
  - intros Hr. apply (inside_not_outside W lo' (hi' - lo') a H4); [lia| exact Ho].
Qed.

#[using="Type"] Lemma hpx_bytes_at : forall W LB SP m m' A bs,
  hpx W LB SP m m' -> bytes_at segs m A bs -> client_range LB SP A (Z.of_nat (length bs)) ->
  disjoint_from W A (Z.of_nat (length bs)) -> bytes_at segs m' A bs.
Proof.
  intros W LB SP m m' A bs HP (H0 & H1 & HB) HR HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia) ltac:(eapply disjoint_outside; [exact HD| lia])) as [E _].
  rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma hpx_wr_at : forall W LB SP m m' A n,
  hpx W LB SP m m' -> wr_at segs m A n -> client_range LB SP A n -> disjoint_from W A n -> wr_at segs m' A n.
Proof.
  intros W LB SP m m' A n HP (H0 & H1 & HW) HR HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia) ltac:(eapply disjoint_outside; [exact HD| lia])) as [_ Wv].
  apply Wv. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma hpx_rw_cells : forall W LB SP m m' A cs,
  hpx W LB SP m m' -> rw_cells segs m A cs -> client_range LB SP A (Z.of_nat (cells_size cs)) ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof.
  intros W LB SP m m' A cs HP [[Hwf HB] HW] HR HD. split; [split; [exact Hwf|]|].
  - eapply hpx_bytes_at; eauto; rewrite cells_bytes_length by assumption; assumption.
  - eapply hpx_wr_at; eauto.
Qed.

Definition lb_keep (ok : option K) (LB : BL) : BL :=
  match ok with None => LB | Some k => lb_remove (ai_K_eqb segs AI) k LB end.

#[using="Type"] Lemma lb_keep_sub : forall ok LB b, In b (lb_keep ok LB) -> In b LB.
Proof. intros [k|] LB b H; cbn in H; [eapply lb_remove_sub; exact H| exact H]. Qed.

Definition orealloc_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (LB : BL) (ok : option K) (sz n lo B : Z) (old : list byte) (m : mem)
    : ai_PS segs AI -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp (Z_to_bv 64 (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ ( (a0 = Z_to_bv 64 0 /\ LB' = LB /\ alloc_frame AI sp lo B m m' LB /\ RHEAP segs AI s' LB m')
       \/ (exists k' A' junk, a0 = Z_to_bv 64 A'
             /\ LB' = (k', A', n) :: lb_keep ok LB
             /\ block_range AI A' n
             /\ alloc_frame AI sp lo B m m' (lb_keep ok LB)
             /\ RHEAP segs AI s' LB' m'
             /\ rw_cells segs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n sz)) old ++ junk)]) ).

#[using="Type"] Lemma orealloc_spec : forall (AC : alloc_contracts AI)
    (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : ai_PS segs AI) (LB : BL) (ok : option K) (A sz n lo B : Z)
    (old : list byte) (errv : word),
  RHEAP segs AI s LB m ->
  match ok with None => A = 0 /\ sz = 0 /\ old = [] | Some k => In (k, A, sz) LB /\ rw_cells segs m A [CB (Z.to_nat sz) old] end ->
  RENV segs AI m B -> bv_unsigned sp <= B ->
  stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
  rw_cells segs m (al_errno L) [C4 errv] ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  SREACH AI (orealloc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB ok sz n lo B old m)
    (MS (mkR ra sp gp (Z_to_bv 64 (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (al_realloc_pc L)) fc None m (seg_rom segs))
    s LB.
Proof.
  intros until errv. intros HR OK HE SPB ST CEIL LO ERR MI -> -> HN.
  destruct ok as [k|].
  - destruct OK as [HIN BLK].
    eapply sreach_mono. { eapply (ac_realloc segs AI AC); eauto. }
    intros s' LB' ms' P. exact P.
  - destruct OK as (-> & -> & ->).
    eapply sreach_mono. { eapply (ac_realloc_null segs AI AC); eauto. }
    intros s' LB' ms' P. unfold malloc_post in P. unfold orealloc_post. destruct_exs P. destruct P as (-> & AF & CASES).
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    destruct CASES as [(-> & -> & HR')|(k & A' & junk & -> & -> & BR & HR' & BLK)].
    + left. auto.
    + right. exists k, A', junk. cbn [lb_keep]. repeat (split; [first [reflexivity| assumption]|]).
      rewrite Z.min_r by lia. cbn. exact BLK.
Qed.

Definition src_ok (LBK : BL) (SP SRC n : Z) (src : list byte) : Prop :=
  client_range LBK SP SRC n
  \/ ((forall m, mem_inv segs m -> bytes_at segs m SRC src)
      /\ exists lo hi, In (lo, hi) (al_img L) /\ lo <= SRC /\ SRC + n <= hi).

#[using="Type"] Lemma src_ok_client : forall LBK SP SRC n src, client_range LBK SP SRC n -> src_ok LBK SP SRC n src.
Proof. intros; left; assumption. Qed.

#[using="Type"] Lemma src_ok_weaken : forall LBK LBK' SP SP' SRC n src,
  src_ok LBK SP SRC n src -> SP' <= SP -> (forall b, In b LBK -> In b LBK') -> src_ok LBK' SP' SRC n src.
Proof.
  intros LBK LBK' SP SP' SRC n src [CR|RO] HS HL; [left| right; exact RO].
  intros a Ha. destruct (CR a Ha) as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

#[using="Type"] Lemma src_ok_pres : forall LBK SP SRC n src m m',
  src_ok LBK SP SRC n src -> Z.of_nat (length src) = n -> heap_pres AI LBK SP m m' -> mem_inv segs m' ->
  bytes_at segs m SRC src -> bytes_at segs m' SRC src.
Proof.
  intros LBK SP SRC n src m m' [CR|[RO _]] LEN HP MI B.
  - eapply heap_pres_bytes_at; [exact HP| exact B| rewrite LEN; exact CR].
  - apply RO. exact MI.
Qed.

#[using="Type"] Lemma src_ok_fresh : forall LBK SP SRC n src s LBx mx (b : block K),
  layout_ok -> src_ok LBK SP SRC n src -> RHEAP segs AI s LBx mx -> In b LBx ->
  (forall b0, In b0 LBK -> In b0 LBx /\ b0 <> b) -> alloc_ceiling <= SP -> 0 < n -> 0 < blk_size b ->
  SRC + n <= blk_addr b \/ blk_addr b + blk_size b <= SRC.
Proof.
  intros LBK SP SRC n src s LBx mx b LO SO HR HIN SUB CE N0 SZ.
  destruct (ai_block_range segs AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & RF).
  destruct SO as [CR|(_ & lo & hi & Hw & H1 & H2)].
  - destruct (Z.lt_ge_cases (SRC + n) (blk_addr b + 1)) as [|G1]; [lia|].
    destruct (Z.lt_ge_cases (blk_addr b + blk_size b) (SRC + 1)) as [|G2]; [lia|].
    exfalso. destruct (Z.lt_ge_cases SRC (blk_addr b)).
    + apply (fresh_block_not_client s LBx LBK b SP mx (blk_addr b) LO HR HIN SUB CE); [lia|]. apply CR. lia.
    + apply (fresh_block_not_client s LBx LBK b SP mx SRC LO HR HIN SUB CE); [lia|]. apply CR. lia.
  - rewrite Forall_forall in RF. specialize (RF (lo, hi) Hw). cbn in RF. lia.
Qed.
End A.

Arguments src_ok {HCEIL segs} AI LBK SP SRC n src.

Arguments client_range {HCEIL segs} AI LB SP A n.
Arguments layout_ok {HCEIL segs} AI.
Arguments seg_ok {HCEIL segs} AI LB SP W.
Arguments hpx {HCEIL segs} AI W LB SP m m'.
Arguments lb_keep {HCEIL segs} AI ok LB.
Arguments orealloc_post {HCEIL segs} AI.
