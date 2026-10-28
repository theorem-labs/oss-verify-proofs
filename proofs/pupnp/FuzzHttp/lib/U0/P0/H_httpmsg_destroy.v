(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_membuffer_assign H_membuffer_destroy H_obj H_freelist H_httpheader_free H_ListAddTail H_ListDestroy HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition httpmsg_destroy_entry := 0x140b0%Z.
Ltac sstep := step; fix_lit_store.
Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.

Lemma mseg_A : forall (lo P meth : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] -> (bv_unsigned sp <= P)%Z -> (P + 504 < 2^64)%Z -> (0 < P)%Z -> (P mod 8 = 0)%Z ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x140e8) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz P) s1 (wz (P + 288)) (wz 1) (wz (P + 288)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ListDestroy_entry) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -16) /\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
      /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz httpmsg_destroy_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI IC PLO PHI PNZ PAL. unfold httpmsg_destroy_entry, ListDestroy_entry.
  pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  ub_null. ub_align. zstep. zstep. zstep. lit_branch.
  carve_frame 16%nat ST. sstep. sstep. sstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact IC.
Qed.

Lemma mseg_B : forall (P : Z) ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  (0 <= P /\ P + 504 < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x140f0) sp gp tp t0 t1 t2 (wz P) s1 (wz (P + 400)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz membuffer_destroy_entry) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x140e8) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros PR. unfold membuffer_destroy_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. apply evt_done. reflexivity.
Qed.

Lemma mseg_C : forall (P : Z) ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  (0 <= P /\ P + 504 < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x140f8) sp gp tp t0 t1 t2 (wz P) s1 (wz (P + 232)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz membuffer_destroy_entry) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x140f0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros PR. unfold membuffer_destroy_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. apply evt_done. reflexivity.
Qed.

Lemma mseg_D : forall (P U : Z) ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  mem_inv rsegs m -> rw_cells rsegs m (P + 432) [C8 (wz U)] -> (0 <= P /\ P + 504 < 2^64)%Z -> (0 <= U < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x14100) sp gp tp t0 t1 t2 (wz P) s1 (wz U) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x17fb0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x140f8) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI UC PR UR. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. apply evt_done. reflexivity.
Qed.

Lemma mseg_E : forall (lo P meth : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -16) -> (lo + 16 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
  rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] -> (bv_unsigned sp <= P)%Z -> (P + 504 < 2^64)%Z ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(P, P + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' P [C4 (wz 0); C4 (wz meth)])
    (MS (mkR x1 (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x14100) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR IC PLO PHI. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [(P, P + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  sstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact IC.
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation lbrm k LB := (lb_remove (ai_K_eqb rsegs AI) k LB).
  Hypothesis LOK : layout_ok AI.
  Hypothesis FREEPC : al_free_pc L_ = 0x17fb0.
  Notation bsub := (bsub AI).
  Notation dlseg := (dlseg AI).
  Notation hd_addr := (hd_addr AI).
  Notation last_addr := (last_addr AI).
  Notation hdrs_mem := (hdrs_mem AI).
  Notation hdrs_blocks := (hdrs_blocks AI).

  Definition mbo (A cap : Z) (MBb : list BLK) : Prop :=
    match MBb with [] => A = 0 | [b] => b = (blk_id b, A, cap + 1) | _ => False end.
  Definition ubo (U : Z) (UB : list BLK) : Prop :=
    match UB with [] => U = 0 | [b] => blk_addr b = U /\ U <> 0 | _ => False end.

  Definition mbo_destroy_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LBK : list BLK) (MB lo B : Z) (m : mem) : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L_) [C4 errv'])
      /\ hpx AI [(MB, MB + 32)] LBK (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m' /\ bsub LBK LB'
      /\ rw_cells rsegs m' MB (mbuf_cells 0 0 0).

  #[using="AC LOK FREEPC"] Lemma mbo_destroy : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (LBK MBb : list BLK) (MB A len cap lo B : Z) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 16 - al_stack L_)%Z -> (0 <= al_stack L_)%Z ->
    rw_cells rsegs m (al_errno L_) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m MB (mbuf_cells A len cap) -> (bv_unsigned sp <= MB)%Z -> (MB + 32 <= B)%Z -> (B < 2^64)%Z -> (MB mod 8 = 0)%Z ->
    mbo A cap MBb -> bsub (MBb ++ LBK) LB -> NoDup (map blk_id (MBb ++ LBK)) ->
    a0 = wz MB ->
    SREACH AI (mbo_destroy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK MB lo B m)
      (MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz membuffer_destroy_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB ST CEIL LO STK ERR MI MBC MBLO MBB BHI MBAL MBO SUB ND ->.
    apply (bsub_app AI) in SUB. destruct SUB as [SUB1 SUB2].
    assert (CASE : exists LBrest, ((A = 0 /\ LBrest = LB) \/ (exists k, In (k, A, cap + 1) LB /\ LBrest = lbrm k LB)) /\ bsub LBK LBrest).
    { destruct MBb as [|b [|b' ?]]; cbn in MBO; [| | destruct MBO].
      - exists LB. split; [left; auto| exact SUB2].
      - exists (lbrm (blk_id b) LB). split.
        + right. exists (blk_id b). split; [| reflexivity]. rewrite <- MBO. apply SUB1. left. reflexivity.
        + eapply (bsub_remove AI); [| exact ND]. intros y [<-|Hy]; [apply SUB1; left; reflexivity| apply SUB2; exact Hy]. }
    destruct CASE as (LBrest & CASE & KSUB).
    eapply sreach_mono.
    { eapply (membuffer_destroy_spec AI AC LOK FREEPC) with (lo := lo) (B := B) (LBrest := LBrest); try eassumption; try reflexivity; try lia.
      apply (mbloc_stack rsegs AI); lia. }
    intros s' LB' ms' Q. unfold membuffer_destroy_post in Q. unfold mbo_destroy_post. destruct_exs Q.
    destruct Q as (-> & Q1 & Q2 & Q3 & Q4 & Q5 & -> & Q7 & Q8).
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split.
    { eapply (hpx_weaken rsegs AI); [exact Q5| intros y Hy; exact Hy| lia| exact KSUB]. }
    split; [exact Q7|]. split; [exact KSUB| exact Q8].
  Qed.

  Definition httpmsg_destroy_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LBK : list BLK) (P meth fcmp U lo B : Z) (m : mem) : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L_) [C4 errv'])
      /\ hpx AI [(P, P + 440)] LBK (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m' /\ bsub LBK LB'
      /\ rw_cells rsegs m' P [C4 (wz 0); C4 (wz meth)]
      /\ rw_cells rsegs m' (P + 288) (lhead_cells (P + 312) (P + 288) 0) /\ rw_cells rsegs m' (P + 344) (fl_cells 0 0)
      /\ FFc m' (P + 288) httpheader_free_entry fcmp
      /\ rw_cells rsegs m' (P + 400) (mbuf_cells 0 0 0) /\ rw_cells rsegs m' (P + 232) (mbuf_cells 0 0 0)
      /\ rw_cells rsegs m' (P + 432) [C8 (wz U)].

  #[using="AC LOK FREEPC"] Theorem httpmsg_destroy_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (LBK MBb SBb UB : list BLK) (ns : list (BLK * Z)) (hs : list (hdr AI))
      (P meth fcmp Am lm cm As ls cs U lo B : Z) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 112 - al_stack L_)%Z -> (0 <= al_stack L_)%Z ->
    rw_cells rsegs m (al_errno L_) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] -> (0 <= meth < 2^32)%Z ->
    rw_cells rsegs m (P + 288) (lhead_cells (hd_addr ns (P + 312)) (last_addr ns (P + 288)) (zlength ns)) ->
    rw_cells rsegs m (P + 344) (fl_cells 0 0) -> FFc m (P + 288) httpheader_free_entry fcmp ->
    dlseg m ns (P + 288) (P + 312) -> hdrs_mem m hs -> map snd ns = map (hA AI) hs -> (zlength ns < 2^40)%Z -> (0 <= fcmp < 2^64)%Z ->
    rw_cells rsegs m (P + 400) (mbuf_cells Am lm cm) -> mbo Am cm MBb -> (0 <= lm /\ 0 <= cm)%Z ->
    rw_cells rsegs m (P + 232) (mbuf_cells As ls cs) -> mbo As cs SBb -> (0 <= ls /\ 0 <= cs)%Z ->
    rw_cells rsegs m (P + 432) [C8 (wz U)] -> ubo U UB ->
    (bv_unsigned sp <= P)%Z -> (P + 504 <= B)%Z -> (P mod 8 = 0)%Z ->
    bsub (map fst ns ++ hdrs_blocks hs ++ MBb ++ SBb ++ UB ++ LBK) LB ->
    NoDup (map blk_id (map fst ns ++ hdrs_blocks hs ++ MBb ++ SBb ++ UB ++ LBK)) ->
    a0 = wz P ->
    SREACH AI (httpmsg_destroy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK P meth fcmp U lo B m)
      (MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz httpmsg_destroy_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI IC METH LC FLC FF DL HS ITEMS LEN FCMP MBC MBO MR SBC SBO SR UC UBO PLO PB PAL ASUB ND ->.
    pose proof (word_lt64 sp) as SPR.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.

    eapply sreach_evt. { eapply (mseg_A lo P meth); try eassumption; lia. }
    intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & IC1).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }

    assert (BR : forall b, In b LB -> (0 < blk_addr b)%Z /\ (0 <= blk_size b)%Z /\ (blk_addr b + blk_size b <= alloc_ceiling)%Z).
    { intros b Hb. destruct (ai_block_range rsegs AI _ _ _ _ HR Hb) as (R1 & _ & R3 & R4 & _). auto. }
    pose proof ASUB as ASUB0. pose proof ND as ND0.
    apply (bsub_app AI) in ASUB. destruct ASUB as [NSUB REST]. apply (bsub_app AI) in REST. destruct REST as [HSUB KSUB1].
    Ltac tr H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn; lia].
    assert (ERR1 : rw_cells rsegs m1 (al_errno L_) [C4 errv]) by (tr ERR MU1 WM1).
    assert (LC1 : rw_cells rsegs m1 (P + 288) (lhead_cells (hd_addr ns (P + 312)) (last_addr ns (P + 288)) (zlength ns))) by (tr LC MU1 WM1).
    assert (FLC1 : rw_cells rsegs m1 (P + 344) (fl_cells 0 0)) by (tr FLC MU1 WM1).
    assert (FF1 : FFc m1 (P + 288) httpheader_free_entry fcmp) by (tr FF MU1 WM1).
    assert (MBC1 : rw_cells rsegs m1 (P + 400) (mbuf_cells Am lm cm)) by (tr MBC MU1 WM1).
    assert (SBC1 : rw_cells rsegs m1 (P + 232) (mbuf_cells As ls cs)) by (tr SBC MU1 WM1).
    assert (UC1 : rw_cells rsegs m1 (P + 432) [C8 (wz U)]) by (tr UC MU1 WM1).
    assert (DL1 : dlseg m1 ns (P + 288) (P + 312)).
    { eapply (dlseg_transport AI); [exact DL| exact MU1| exact WM1|]. intros b it H.
      pose proof (in_map fst _ _ H) as H'. cbn [fst] in H'. destruct (BR b (NSUB _ H')) as (? & ? & ?). cbn. lia. }
    assert (HS1 : hdrs_mem m1 hs).
    { eapply (hdrs_mem_transport AI); [exact HS| exact MU1| exact WM1|]. intros h0 A n Hh HA.
      destruct (hregion_block AI h0 A n HA) as [k Hk]. destruct (BR _ (HSUB _ (in_hdrs_blocks AI _ _ _ Hh Hk))) as (? & ? & ?). cbn in *. lia. }
    assert (HP1 : hpx AI [(P, P + 440)]%Z LBK (bv_unsigned sp) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| | exact MU1| exact WM1|].
      - intros b Hb. apply ASUB0. rewrite !in_app_iff. LiaTuning.ctauto.
      - constructor; [| constructor]. left. cbn. lia. }
    clear MU1 WM1.

    eapply sreach_bind.
    { replace (P + 344)%Z with (P + 288 + 56)%Z in FLC1 by lia.
      eapply (ListDestroy_spec AI AC LOK FREEPC) with (lo := lo) (B := B) (L := P + 288) (LBK := MBb ++ SBb ++ UB ++ LBK) (ns := ns) (hs := hs);
        try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption; try reflexivity.
      replace (P + 288 + 24)%Z with (P + 312)%Z by lia. exact LC1.
      all: replace (P + 288 + 24)%Z with (P + 312)%Z by lia; exact DL1. }
    intros sx2 LB2 ms2 Q. unfold ListDestroy_post in Q. destruct_exs Q.
    destruct Q as (-> & MI2 & ST2 & HE2 & [e2 ERR2] & HP2 & HR2 & KSUB2 & LC2 & FLC2 & FF2).
    rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HP2 by lia.
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    replace (ret_pc (Z_to_bv 64 0x140e8)) with (Z_to_bv 64 0x140e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    replace (P + 288 + 24)%Z with (P + 312)%Z in LC2 by lia. replace (P + 288 + 56)%Z with (P + 344)%Z in FLC2 by lia.
    Ltac trh H HP := eapply (hpx_rw_cells rsegs AI); [exact HP| exact H| apply client_range_above; lia| cbn; lia].
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (trh FR1 HP2).
    assert (IC2 : rw_cells rsegs m2 P [C4 (wz 1); C4 (wz meth)]) by (trh IC1 HP2).
    assert (MBC2 : rw_cells rsegs m2 (P + 400) (mbuf_cells Am lm cm)) by (trh MBC1 HP2).
    assert (SBC2 : rw_cells rsegs m2 (P + 232) (mbuf_cells As ls cs)) by (trh SBC1 HP2).
    assert (UC2 : rw_cells rsegs m2 (P + 432) [C8 (wz U)]) by (trh UC1 HP2).
    assert (HP02 : hpx AI [(P, P + 440)]%Z LBK (bv_unsigned sp) m m2).
    { eapply (hpx_trans rsegs AI); [exact HP1|]. eapply (hpx_weaken rsegs AI); [exact HP2| | lia|].
      - unfold sub_fp. cbn. intros y [Hy _]. lia.
      - intros b Hb. rewrite !in_app_iff. LiaTuning.ctauto. }
    clear HP1 HP2 FR1 IC1 MBC1 SBC1 UC1 LC1 FLC1 FF1 DL1 HS1 HR1 HE1 ERR1 MI1 ST1.
    pose proof ND0 as NDt. apply nd_app in NDt. destruct NDt as (_ & _ & NDt). apply nd_app in NDt. destruct NDt as (_ & _ & NDt).

    eapply sreach_evt. { eapply (mseg_B P); lia. } intros ms' ->.
    eapply sreach_bind.
    { eapply (mbo_destroy) with (lo := lo) (B := B) (MBb := MBb) (LBK := SBb ++ UB ++ LBK) (MB := P + 400) (A := Am) (len := lm) (cap := cm);
        try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption; reflexivity. }
    intros sx3 LB3 ms3 Q. unfold mbo_destroy_post in Q. destruct_exs Q.
    destruct Q as (-> & MI3 & ST3 & HE3 & [e3 ERR3] & HP3 & HR3 & KSUB3 & MBC3).
    rewrite ?unsigned_lit in ST3 by lia. rewrite ?unsigned_lit in HP3 by lia.
    lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
    replace (ret_pc (Z_to_bv 64 0x140f0)) with (Z_to_bv 64 0x140f0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (trh FR2 HP3).
    assert (IC3 : rw_cells rsegs m3 P [C4 (wz 1); C4 (wz meth)]) by (trh IC2 HP3).
    assert (SBC3 : rw_cells rsegs m3 (P + 232) (mbuf_cells As ls cs)) by (trh SBC2 HP3).
    assert (UC3 : rw_cells rsegs m3 (P + 432) [C8 (wz U)]) by (trh UC2 HP3).
    assert (LC3 : rw_cells rsegs m3 (P + 288) (lhead_cells (P + 312) (P + 288) 0)) by (trh LC2 HP3).
    assert (FLC3 : rw_cells rsegs m3 (P + 344) (fl_cells 0 0)) by (trh FLC2 HP3).
    assert (FF3 : FFc m3 (P + 288) httpheader_free_entry fcmp) by (trh FF2 HP3).
    assert (HP03 : hpx AI [(P, P + 440)]%Z LBK (bv_unsigned sp) m m3).
    { eapply (hpx_trans rsegs AI); [exact HP02|]. eapply (hpx_weaken rsegs AI); [exact HP3| | lia|].
      - unfold sub_fp. cbn. intros y [Hy _]. lia.
      - intros b Hb. rewrite !in_app_iff. LiaTuning.ctauto. }
    clear HP02 HP3 FR2 IC2 MBC2 SBC2 UC2 LC2 FLC2 FF2 HR2 HE2 ERR2 MI2 ST2 KSUB2.
    apply nd_app in NDt. destruct NDt as (_ & _ & NDt).

    eapply sreach_evt. { eapply (mseg_C P); lia. } intros ms' ->.
    eapply sreach_bind.
    { eapply (mbo_destroy) with (lo := lo) (B := B) (MBb := SBb) (LBK := UB ++ LBK) (MB := P + 232) (A := As) (len := ls) (cap := cs);
        try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption; reflexivity. }
    intros sx4 LB4 ms4 Q. unfold mbo_destroy_post in Q. destruct_exs Q.
    destruct Q as (-> & MI4 & ST4 & HE4 & [e4 ERR4] & HP4 & HR4 & KSUB4 & SBC4).
    rewrite ?unsigned_lit in ST4 by lia. rewrite ?unsigned_lit in HP4 by lia.
    lazymatch type of MI4 with mem_inv _ ?mm => rename mm into m4 end.
    replace (ret_pc (Z_to_bv 64 0x140f8)) with (Z_to_bv 64 0x140f8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -16) [C8 s0; C8 ra]) by (trh FR3 HP4).
    assert (IC4 : rw_cells rsegs m4 P [C4 (wz 1); C4 (wz meth)]) by (trh IC3 HP4).
    assert (MBC4 : rw_cells rsegs m4 (P + 400) (mbuf_cells 0 0 0)) by (trh MBC3 HP4).
    assert (UC4 : rw_cells rsegs m4 (P + 432) [C8 (wz U)]) by (trh UC3 HP4).
    assert (LC4 : rw_cells rsegs m4 (P + 288) (lhead_cells (P + 312) (P + 288) 0)) by (trh LC3 HP4).
    assert (FLC4 : rw_cells rsegs m4 (P + 344) (fl_cells 0 0)) by (trh FLC3 HP4).
    assert (FF4 : FFc m4 (P + 288) httpheader_free_entry fcmp) by (trh FF3 HP4).
    assert (HP04 : hpx AI [(P, P + 440)]%Z LBK (bv_unsigned sp) m m4).
    { eapply (hpx_trans rsegs AI); [exact HP03|]. eapply (hpx_weaken rsegs AI); [exact HP4| | lia|].
      - unfold sub_fp. cbn. intros y [Hy _]. lia.
      - intros b Hb. rewrite !in_app_iff. LiaTuning.ctauto. }
    clear HP03 HP4 FR3 IC3 MBC3 SBC3 UC3 LC3 FLC3 FF3 HR3 HE3 ERR3 MI3 ST3 KSUB3.
    apply nd_app in NDt. destruct NDt as (_ & JU & NDt).

    assert (TAIL : forall sx m5 (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) e5,
      mem_inv rsegs m5 -> stk rsegs m5 lo (bv_unsigned sp + -16) -> RENV rsegs AI m5 B -> rw_cells rsegs m5 (al_errno L_) [C4 e5] ->
      (exists LB5, RHEAP rsegs AI sx LB5 m5 /\ bsub LBK LB5 /\ forall P0, SREACH AI P0 = SREACH AI P0) ->
      forall LB5, RHEAP rsegs AI sx LB5 m5 -> bsub LBK LB5 ->
      rw_cells rsegs m5 (bv_unsigned sp + -16) [C8 s0; C8 ra] -> rw_cells rsegs m5 P [C4 (wz 1); C4 (wz meth)] ->
      rw_cells rsegs m5 (P + 400) (mbuf_cells 0 0 0) -> rw_cells rsegs m5 (P + 232) (mbuf_cells 0 0 0) -> rw_cells rsegs m5 (P + 432) [C8 (wz U)] ->
      rw_cells rsegs m5 (P + 288) (lhead_cells (P + 312) (P + 288) 0) -> rw_cells rsegs m5 (P + 344) (fl_cells 0 0) -> FFc m5 (P + 288) httpheader_free_entry fcmp ->
      hpx AI [(P, P + 440)]%Z LBK (bv_unsigned sp) m m5 ->
      SREACH AI (httpmsg_destroy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK P meth fcmp U lo B m)
        (MS (mkR (wz 0x14100) (wz (bv_unsigned sp + -16)) gp (wz (al_tp L_)) t0' t1' t2' (wz P) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (wz 0x14100) fc None m5 (seg_rom rsegs)) sx LB5).
    { intros until e5. intros MI5 ST5 HE5 ERR5 _ LB5 HR5 KSUB5 FR5 IC5 MBC5 SBC5 UC5 LC5 FLC5 FF5 HP5.
      eapply sreach_evt. { eapply (mseg_E lo P meth); try eassumption; lia. }
      intros ms' (m6 & -> & MU6 & WM6 & MI6 & ST6 & IC6).
      apply sreach_ret. unfold httpmsg_destroy_post.
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MI6|]. split; [exact ST6|]. split.
      { eapply (ai_env_frame rsegs AI); [exact HR5| exact HE5| exact MU6| exact WM6|]. constructor; [| constructor]. left. cbn. lia. }
      split. { eexists. tr ERR5 MU6 WM6. } split.
      { eapply (hpx_trans rsegs AI); [exact HP5|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR5| exact KSUB5| exact MU6| exact WM6|].
        constructor; [| constructor]. right; right. cbn. lia. }
      split. { eapply (ai_heap_frame rsegs AI); [exact HR5| exact MU6| exact WM6|]. constructor; [| constructor]. left. cbn. lia. }
      split; [exact KSUB5|]. split; [exact IC6|].
      split; [tr LC5 MU6 WM6|]. split; [tr FLC5 MU6 WM6|]. split; [tr FF5 MU6 WM6|]. split; [tr MBC5 MU6 WM6|]. split; [tr SBC5 MU6 WM6| tr UC5 MU6 WM6]. }

    pose proof (word_lt64 (wz U)) as UR0.
    assert (UR : (0 <= U < 2^64)%Z).
    { destruct UB as [|b [|b' ?]]; cbn in UBO; [lia| | destruct UBO]. destruct UBO as [<- _].
      destruct (BR b (ASUB0 b ltac:(rewrite !in_app_iff; cbn; LiaTuning.ctauto))) as (? & ? & ?). lia. }
    eapply sreach_evt. { eapply (mseg_D P U); try eassumption; lia. } intros ms' ->.
    apply (bsub_app AI) in KSUB4. destruct KSUB4 as [USUB KSUB].
    destruct UB as [|b [|b' ?]]; cbn in UBO; [| | destruct UBO].
    -
      subst U. eapply sreach_evt. { rewrite <- FREEPC. eapply (ac_free_null rsegs AI AC). reflexivity. }
      intros ms' Q. destruct_exs Q. subst ms'.
      replace (ret_pc (Z_to_bv 64 0x14100)) with (Z_to_bv 64 0x14100) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply TAIL; try eassumption. exists LB4. split; [exact HR4|]. split; [exact KSUB| reflexivity].
    - destruct UBO as [EU UNZ].
      eapply sreach_bind.
      { rewrite <- FREEPC. eapply (ac_free rsegs AI AC) with (lo := lo) (B := B) (k := blk_id b) (n := blk_size b);
          try eassumption; rewrite ?unsigned_lit by lia; try lia; try eassumption.
        - replace (blk_id b, U, blk_size b) with b by (destruct b as [[? ?] ?]; cbn in EU |- *; subst; reflexivity). apply USUB. left. reflexivity.
        - reflexivity. }
      intros sx5 LB5 ms5 Q. unfold free_post in Q. destruct_exs Q. destruct Q as (-> & AF & -> & HR5).
      destruct AF as (MI5 & ST5 & HE5 & [e5 ERR5] & HPF). rewrite ?unsigned_lit in ST5 by lia. rewrite ?unsigned_lit in HPF by lia.
      lazymatch type of MI5 with mem_inv _ ?mm => rename mm into m5 end.
      replace (ret_pc (Z_to_bv 64 0x14100)) with (Z_to_bv 64 0x14100) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KSUB5 : bsub LBK (lbrm (blk_id b) LB4)).
      { eapply (bsub_remove AI); [| exact NDt]. intros y [<-|Hy]; [apply USUB; left; reflexivity| apply KSUB; exact Hy]. }
      Ltac trp H HPF := eapply (heap_pres_rw_cells rsegs AI); [exact HPF| exact H| apply client_range_above; cbn; lia].
      eapply TAIL; try eassumption.
      + exists (lbrm (blk_id b) LB4). split; [exact HR5|]. split; [exact KSUB5| reflexivity].
      + trp FR4 HPF. + trp IC4 HPF. + trp MBC4 HPF. + trp SBC4 HPF. + trp UC4 HPF. + trp LC4 HPF. + trp FLC4 HPF. + trp FF4 HPF.
      + eapply (hpx_trans rsegs AI); [exact HP04|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| exact KSUB5].
  Qed.
End W.
