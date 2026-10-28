(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_membuffer_assign H_obj H_freelist HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition ListAddTail_entry := 0x160ec%Z.
Ltac sstep := step; fix_lit_store.

Definition lhead_cells (first last size : Z) : list cell :=
  [C8 (wz 0); C8 (wz first); C8 (wz 0); C8 (wz last); C8 (wz 0); C8 (wz 0); C8 (wz size)].

Notation AFRc m q j s1 s0 ra := (rw_cells rsegs m q [CB 8 j; C8 s1; C8 s0; C8 ra]).

Lemma aseg1 : forall (lo L IT : Z) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  (0 < L /\ L + 96 < 2^64)%Z -> (0 <= IT < 2^64)%Z -> (L mod 8 = 0)%Z ->
  evt rsegs (fun ms' => exists m' j,
      ms' = MS (mkR (wz 0x16118) (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz L) (wz IT) (wz (L + 56)) (wz IT) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz FreeListAlloc_entry) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -32) /\ AFRc m' (bv_unsigned sp + -32) j s1 s0 ra)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz L) (wz IT) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ListAddTail_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI LR ITR AL. unfold ListAddTail_entry, FreeListAlloc_entry.
  pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST. do 4 sstep.
  uwalk_lia_to 0x16104%Z. ub_align.
  uwalk_lia_to 0x16114%Z. step.
  apply evt_done. eexists _, _. split; [reflexivity|]. repeat (split; [eassumption|]). exact FR.
Qed.

Lemma aseg2a : forall (lo : Z) (j : list byte) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x8 x9
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -32) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  AFRc m (bv_unsigned sp + -32) j s1 s0 ra ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs) /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 x8 x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16118) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. if_cases K0; zify_cond K0; [| exfalso; lia]. cbn [Z.eqb] in *.
  do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Definition link_post (lo L IT N first last size : Z) (lastnode : option (Z * Z)) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch ((bv_unsigned sp - 32, bv_unsigned sp) :: (L, L + 56) :: (N, N + 24)
              :: match lastnode with None => [] | Some (pl, il) => [(last, last + 24)] end)%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' L (lhead_cells (match lastnode with None => N | Some _ => first end) N (size + 1))
    /\ rw_cells rsegs m' N (node_cells last (L + 24) IT)
    /\ match lastnode with None => True | Some (pl, il) => rw_cells rsegs m' last (node_cells pl N il) end.

Lemma aseg2b : forall (lo L IT N first last size : Z) (lastnode : option (Z * Z)) (j nj : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -32) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  AFRc m (bv_unsigned sp + -32) j s1 s0 ra ->
  rw_cells rsegs m L (lhead_cells first last size) -> (bv_unsigned sp <= L)%Z -> (L + 96 < 2^64)%Z ->
  (0 <= first < 2^64)%Z -> (0 <= size /\ size + 1 < 2^63)%Z -> (0 <= IT < 2^64)%Z ->
  rw_cells rsegs m N [CB 24 nj] -> (16 <= N)%Z -> (N + 24 <= lo)%Z -> (N mod 8 = 0)%Z -> (L mod 8 = 0)%Z ->
  match lastnode with
  | None => last = L
  | Some (pl, il) => rw_cells rsegs m last (node_cells pl (L + 24) il) /\ (16 <= last)%Z /\ (last + 24 <= lo)%Z /\ (last mod 8 = 0)%Z
                     /\ (N + 24 <= last \/ last + 24 <= N)%Z /\ (0 <= pl < 2^64)%Z /\ (0 <= il < 2^64)%Z
  end ->
  evt rsegs (link_post lo L IT N first last size lastnode ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (MS (mkR x1 (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz L) (wz IT) (wz N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16118) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR LC LLO LHI FR0 SZ ITR NC N16 NHI NAL AL LASTH. unfold lhead_cells, node_cells in *.
  pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl ((bv_unsigned sp - 32, bv_unsigned sp) :: (L, L + 56) :: (N, N + 24)
              :: match lastnode with None => [] | Some (pl, il) => [(last, last + 24)] end)%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply (rw_cells_split_CB rsegs m N [] 24 nj [] [8; 8; 8]%nat) in NC; [| reflexivity]. cbn [app mk_CB_cells] in NC.
  destruct lastnode as [[pl il]|].
  - destruct LASTH as (LNC & L16 & LHI2 & LAL & DJ & PLR & ILR). cbn [munch] in MU.
    uwalk_ub_to 0x16158%Z. step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
    uwalk_ub_to 0x16170%Z. release_frame FR ST (bv_unsigned sp). step.
    apply evt_done. unfold link_post, lhead_cells, node_cells. do 4 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  - subst last. cbn [munch] in MU.
    uwalk_ub_to 0x16158%Z. step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
    uwalk_ub_to 0x16170%Z. release_frame FR ST (bv_unsigned sp). step.
    apply evt_done. unfold link_post, lhead_cells, node_cells. do 4 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact I.
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Hypothesis LOK : layout_ok AI.
  Hypothesis MALPC : al_malloc_pc L_ = 0x180f0.
  Notation bsub := (bsub AI).
  Notation dlseg := (dlseg AI).
  Notation hd_addr := (hd_addr AI).
  Notation last_addr := (last_addr AI).

  Definition ListAddTail_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB LBK : list BLK) (ns : list (BLK * Z)) (L IT fk lo B : Z) (m : mem) : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (ns' : list (BLK * Z)),
      ms' = MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L_) [C4 errv'])
      /\ hpx AI [(L, L + 56)] LBK (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m' /\ bsub LBK LB' /\ bsub (map fst ns') LB' /\ NoDup (map blk_id (map fst ns' ++ LBK))
      /\ rw_cells rsegs m' L (lhead_cells (hd_addr ns' (L + 24)) (last_addr ns' L) (zlength ns'))
      /\ rw_cells rsegs m' (L + 56) (fl_cells 0 fk)
      /\ dlseg m' ns' L (L + 24)
      /\ ((r = 0 /\ ns' = ns /\ LB' = LB) \/ (exists k, r <> 0 /\ ns' = ns ++ [((k, r, 24), IT)] /\ LB' = (k, r, 24) :: LB)).

  #[using="AC LOK MALPC"] Theorem ListAddTail_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (LBK : list BLK) (ns : list (BLK * Z)) (L IT fk lo B : Z) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 32 - al_stack L_)%Z -> (0 <= al_stack L_)%Z ->
    rw_cells rsegs m (al_errno L_) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m L (lhead_cells (hd_addr ns (L + 24)) (last_addr ns L) (zlength ns)) ->
    rw_cells rsegs m (L + 56) (fl_cells 0 fk) -> dlseg m ns L (L + 24) ->
    (bv_unsigned sp <= L)%Z -> (L + 96 <= B)%Z -> (zlength ns < 2^40)%Z -> (0 <= IT < 2^64)%Z ->
    bsub (map fst ns) LB -> bsub LBK LB -> NoDup (map blk_id (map fst ns ++ LBK)) ->
    (L mod 8 = 0)%Z -> a0 = wz L -> a1 = wz IT ->
    SREACH AI (ListAddTail_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB LBK ns L IT fk lo B m)
      (MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ListAddTail_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI LC FLC DL LLO LB96 LEN ITR NSUB KSUB ND AL -> ->.
    pose proof (word_lt64 sp) as SPR. unfold zlength in *.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (ASUB : bsub (map fst ns ++ LBK) LB) by (apply (bsub_app AI); split; assumption).

    assert (NF : forall b it, In (b, it) ns -> In b LB /\ blk_size b = 24 /\ (16 <= blk_addr b)%Z /\ (blk_addr b + 24 <= alloc_ceiling)%Z).
    { intros b it H. assert (Hb : In b LB) by (apply NSUB; apply (in_map fst _ _ H)).
      destruct (dlseg_facts AI _ _ _ _ _ _ DL H) as (SZ & _). destruct (ai_block_range rsegs AI _ _ _ _ HR Hb) as (R1 & R2 & _ & R4 & _).
      rewrite SZ in R4. split; [exact Hb|]. split; [exact SZ|]. split; [Z.div_mod_to_equations; lia| lia]. }
    assert (FIRSTR : (0 <= hd_addr ns (L + 24) < 2^64)%Z).
    { destruct ns as [|[b it] ns']; cbn; [lia|]. destruct (NF b it (or_introl eq_refl)) as (_ & _ & ? & ?). lia. }
    eapply sreach_evt. { eapply (aseg1 lo L IT); try eassumption; lia. }
    intros ms' (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ LC MU1 WM1 ltac:(cbn; lia)) as LC1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ FLC MU1 WM1 ltac:(cbn; lia)) as FLC1.
    assert (DL1 : dlseg m1 ns L (L + 24)).
    { eapply (dlseg_transport AI); [exact DL| exact MU1| exact WM1|]. intros b it H. destruct (NF b it H) as (_ & _ & ? & ?). cbn. lia. }
    assert (HP1 : hpx AI [(L, L + 56)]%Z LBK (bv_unsigned sp) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact KSUB| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    clear MU1 WM1.

    eapply sreach_bind.
    { eapply (FreeListAlloc_spec AI AC MALPC) with (lo := lo) (B := B); try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption; reflexivity. }
    intros sx2 LB2 ms2 P. unfold malloc_post in P. destruct_exs P. destruct P as (-> & AF & CASES).
    destruct AF as (MI2 & ST2 & HE2 & [e2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    replace (ret_pc (Z_to_bv 64 0x16118)) with (Z_to_bv 64 0x16118) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
    pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF LC1 ltac:(apply client_range_above; cbn; lia)) as LC2.
    pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FLC1 ltac:(apply client_range_above; cbn; lia)) as FLC2.
    assert (DL2 : dlseg m2 ns L (L + 24)).
    { eapply (dlseg_heap_pres AI); [exact DL1| exact HPF|]. intros b it H. destruct (NF b it H) as (Hb & _). exact Hb. }
    assert (HP2 : hpx AI [(L, L + 56)]%Z LBK (bv_unsigned sp) m m2).
    { eapply (hpx_trans rsegs AI); [exact HP1|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| exact KSUB]. }
    destruct CASES as [(-> & -> & HR2)|(k & N & junk & -> & -> & BR & HR2 & NBLK)].
    -
      eapply sreach_evt. { eapply (aseg2a lo j); try eassumption; lia. }
      intros ms' [-> ST3]. apply sreach_ret. unfold ListAddTail_post.
      do 15 eexists. exists 0, ns. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST3|]. split; [exact HE2|]. split; [eexists; exact ERR2|]. split; [exact HP2|].
      split; [exact HR2|]. split; [exact KSUB|]. split; [exact NSUB|]. split; [exact ND|]. split; [exact LC2|]. split; [exact FLC2|]. split; [exact DL2|].
      left. repeat split; reflexivity.
    -
      destruct BR as (U1 & U2 & U3 & U4 & U5).
      assert (NAL : (N mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
      assert (NEW : In (k, N, 24) ((k, N, 24) :: LB)) by (left; reflexivity).
      assert (ND2 : NoDup (map blk_id ((k, N, 24) :: (map fst ns ++ LBK)))) by (eapply (fresh_nodup AI); [exact HR2| exact ASUB| exact ND]).

      assert (NDJ : forall b it, In (b, it) ns -> (N + 24 <= blk_addr b \/ blk_addr b + 24 <= N)%Z).
      { intros b it H. destruct (NF b it H) as (Hb & SZ & _).
        assert (NE : (k, N, 24) <> b).
        { intros <-. cbn in ND2. inversion ND2 as [|x_ l_ NI X_]; subst. apply NI. apply base.list_elem_of_In. change k with (blk_id (k, N, 24)). apply in_map. apply in_or_app. left. exact (in_map fst _ _ H). }
        destruct (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR2 NEW (or_intror Hb) NE) as [D|D]; cbn in D; rewrite ?SZ in D; lia. }

      destruct (list.list_eq_nil_dec ns) as [->|NNE].
      +
        cbn [H_obj.hd_addr H_obj.last_addr zlength length Z.of_nat] in LC2.
        eapply sreach_evt. { eapply (aseg2b lo L IT N (L + 24) L 0 None j junk); try eassumption; try LiaTuning.alia; try reflexivity. }
        intros ms' P. unfold link_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & LC3 & NC3 & _). cbn [munch app] in MU3.
        pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR2 NEW) as DE. cbn in DE.
        pose proof (rw_cells_transport rsegs _ m2 _ _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
        pose proof (rw_cells_transport rsegs _ m2 _ _ _ FLC2 MU3 WM3 ltac:(cbn; lia)) as FLC3.
        apply sreach_ret. unfold ListAddTail_post.
        do 15 eexists. exists N, [((k, N, 24), IT)]. split; [reflexivity|].
        split; [exact MI3|]. split; [exact ST3|]. split.
        { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|].
          constructor. { left. cbn. lia. } constructor. { left. cbn. lia. } constructor; [| constructor].
          right; right; right. exists (k, N, 24). split; [exact NEW|]. cbn. lia. }
        split; [eexists; exact ERR3|]. split.
        { eapply (hpx_trans rsegs AI); [exact HP2|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| intros b Hb; right; apply KSUB; exact Hb| exact MU3| exact WM3|].
          constructor. { left. cbn. lia. } constructor. { right; right. cbn. lia. } constructor; [| constructor].
          right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI _ _ LBK (k, N, 24)); [exact LOK| exact HR2| exact NEW| | lia| cbn; lia].
          intros b0 Hb0. split; [right; apply KSUB; exact Hb0|]. intros ->.
          cbn in ND2. inversion ND2 as [|x_ l_ NI X_]; subst. apply NI. apply base.list_elem_of_In. change k with (blk_id (k, N, 24)). apply in_map. first [exact Hb0| apply in_or_app; right; exact Hb0]. }
        split. { eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3|].
          constructor. { left. cbn. lia. } constructor. { left. cbn. lia. } constructor; [| constructor].
          right; right; right. exists (k, N, 24). split; [exact NEW|]. cbn. lia. }
        split. { intros b Hb. right. apply KSUB. exact Hb. }
        split. { intros b [<-|[]]. exact NEW. }
        split. { cbn. cbn in ND2. exact ND2. }
        split; [exact LC3|]. split; [exact FLC3|]. split.
        { cbn. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact NC3| exact I]. }
        right. exists k. split; [lia|]. split; reflexivity.
      + destruct (exists_last NNE) as (ns0 & [bl itl] & E).
        pose proof DL2 as DLx. rewrite E in DLx. destruct (dlseg_last_cells AI _ _ _ _ _ _ DLx) as (LNC & BSZ & BNZ & BNT). clear DLx.
        assert (HBL : In (bl, itl) ns) by (rewrite E; apply in_or_app; right; left; reflexivity).
        destruct (NF bl itl HBL) as (BIN & _ & B16 & BHI2).
        assert (BAL : (blk_addr bl mod 8 = 0)%Z).
        { destruct (ai_block_range rsegs AI _ _ _ _ HR BIN) as (_ & Q2 & _). Z.div_mod_to_equations. lia. }
        assert (LADDR : last_addr ns L = blk_addr bl) by (rewrite E, (last_addr_app AI); reflexivity).
        rewrite LADDR in LC2.

        assert (PLR : forall nsx pv, (0 <= pv < 2^64)%Z -> (forall b it, In (b, it) nsx -> In (b, it) ns) -> (0 <= last_addr nsx pv < 2^64)%Z).
        { induction nsx as [|[b0 it0] nsx IH]; intros pv Hpv Hsub; cbn; [exact Hpv|]. apply IH.
          - destruct (NF b0 it0 (Hsub _ _ (or_introl eq_refl))) as (_ & _ & ? & ?). lia.
          - intros b1 it1 H1. apply Hsub. right. exact H1. }
        assert (PL0 : (0 <= last_addr ns0 L < 2^64)%Z).
        { apply PLR; [lia|]. intros b0 it0 H0. rewrite E. apply in_or_app. left. exact H0. }
        destruct (dlseg_facts AI _ _ _ _ _ _ DL2 HBL) as (_ & _ & _ & ITLR).
        eapply sreach_evt.
        { eapply (aseg2b lo L IT N (hd_addr ns (L + 24)) (blk_addr bl) (Z.of_nat (length ns)) (Some (last_addr ns0 L, itl)) j junk); try eassumption; try LiaTuning.alia.
          split; [exact LNC|]. split; [lia|]. split; [lia|]. split; [exact BAL|]. split; [exact (NDJ bl itl HBL)|]. split; [exact PL0| exact ITLR]. }
        intros ms' P. unfold link_post in P. destruct_exs P. destruct P as (-> & MU3 & WM3 & MI3 & ST3 & LC3 & NC3 & LASTC). cbn [munch app] in MU3.
        lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
        pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR2 NEW) as DE. cbn in DE.
        pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR BIN) as DEB. cbn in DEB. rewrite BSZ in DEB.
        pose proof (rw_cells_transport rsegs _ m2 _ _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
        pose proof (rw_cells_transport rsegs _ m2 _ _ _ FLC2 MU3 WM3 ltac:(cbn; lia)) as FLC3.

        assert (PRE : forall b0 it0, In (b0, it0) ns0 -> b0 <> bl /\ In (b0, it0) ns).
        { intros b0 it0 H0. assert (H0' : In (b0, it0) ns) by (rewrite E; apply in_or_app; left; exact H0). split; [| exact H0'].
          intros ->. pose proof ND as NDn. rewrite E, !map_app in NDn. cbn in NDn. rewrite <- app_assoc in NDn. apply list.NoDup_app in NDn.
          destruct NDn as (_ & DJn & _). apply (DJn (blk_id bl)). { apply base.list_elem_of_In. apply in_map. exact (in_map fst _ _ H0). } left. }
        assert (DL3 : dlseg m3 (ns ++ [((k, N, 24), IT)]) L (L + 24)).
        { eapply (dlseg_snoc AI); [exact DL2| exact MU3| exact WM3| | | rewrite LADDR; exact NC3| reflexivity| cbn; lia| cbn; lia| exact ITR].
          - intros b0 it0 H0. rewrite E, removelast_app in H0 by congruence. cbn [removelast] in H0. rewrite app_nil_r in H0.
            destruct (PRE b0 it0 H0) as [NE0 H0']. destruct (NF b0 it0 H0') as (B0IN & B0SZ & B016 & B0HI).
            pose proof (NDJ b0 it0 H0') as DJ0.
            destruct (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR B0IN BIN NE0) as [D|D]; cbn in D |- *; rewrite ?B0SZ, ?BSZ in D; lia.
          - intros ns0' bl' itl' E'. rewrite E in E'. apply app_inj_tail in E'. destruct E' as [-> E2]. injection E2 as -> ->. exact LASTC. }
        apply sreach_ret. unfold ListAddTail_post.
        do 15 eexists. exists N, (ns ++ [((k, N, 24), IT)]). split; [reflexivity|].
        split; [exact MI3|]. split; [exact ST3|]. split.
        { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|].
          constructor. { left. cbn. lia. } constructor. { left. cbn. lia. } constructor.
          { right; right; right. exists (k, N, 24). split; [exact NEW|]. cbn. lia. } constructor; [| constructor].
          right; right; right. exists bl. split; [right; exact BIN|]. rewrite BSZ. cbn. lia. }
        split; [eexists; exact ERR3|]. split.
        { eapply (hpx_trans rsegs AI); [exact HP2|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| intros b Hb; right; apply KSUB; exact Hb| exact MU3| exact WM3|].
          constructor. { left. cbn. lia. } constructor. { right; right. cbn. lia. } constructor.
          { right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI _ _ LBK (k, N, 24)); [exact LOK| exact HR2| exact NEW| | lia| cbn; lia].
            intros b0 Hb0. split; [right; apply KSUB; exact Hb0|]. intros ->.
            cbn in ND2. inversion ND2 as [|x_ l_ NI X_]; subst. apply NI. apply base.list_elem_of_In. change k with (blk_id (k, N, 24)). apply in_map. first [exact Hb0| apply in_or_app; right; exact Hb0]. }
          constructor; [| constructor].
          right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI _ _ LBK bl); [exact LOK| exact HR2| right; exact BIN| | lia| rewrite BSZ; cbn; lia].
          intros b0 Hb0. split; [right; apply KSUB; exact Hb0|]. intros ->.
          rewrite map_app in ND. apply list.NoDup_app in ND. destruct ND as (_ & DJn & _). apply (DJn (blk_id bl)).
          - apply base.list_elem_of_In. apply in_map. exact (in_map fst _ _ HBL).
          - apply base.list_elem_of_In. apply in_map. exact Hb0. }
        split. { eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3|].
          constructor. { left. cbn. lia. } constructor. { left. cbn. lia. } constructor.
          { right; right; right. exists (k, N, 24). split; [exact NEW|]. cbn. lia. } constructor; [| constructor].
          right; right; right. exists bl. split; [right; exact BIN|]. rewrite BSZ. cbn. lia. }
        split. { intros b Hb. right. apply KSUB. exact Hb. }
        split. { intros b Hb. rewrite map_app in Hb. apply in_app_or in Hb. destruct Hb as [Hb|[<-|[]]]; [right; apply NSUB; exact Hb| exact NEW]. }
        split. { rewrite !map_app, <- app_assoc. cbn [map app blk_id fst]. change (fst (fst (k, N, 24))) with k.
                 cbn in ND2. rewrite !map_app in ND2. inversion ND2 as [|x_ l_ NI X_]; subst.
                 apply list.NoDup_app in X_. destruct X_ as (Y1 & Y2 & Y3).
                 apply list.NoDup_app. split; [exact Y1|]. split.
                 - intros y Hy [->|Hy2]%list.elem_of_cons. { apply NI. apply list.elem_of_app. left. exact Hy. } exact (Y2 y Hy Hy2).
                 - constructor; [| exact Y3]. intros Hk. apply NI. apply list.elem_of_app. right. exact Hk. }
        split. { rewrite (hd_addr_app AI) by exact NNE. rewrite (last_addr_app AI). cbn [H_obj.last_addr]. unfold zlength. rewrite length_app. cbn [length].
                 rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. exact LC3. }
        split; [exact FLC3|]. split; [exact DL3|].
        right. exists k. split; [lia|]. split; reflexivity.
  Qed.
End W.
