(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF SReach AllocSpec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_membuffer_assign H_obj HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition FreeListFree_entry := 0x1641c%Z.
Definition FreeListDestroy_entry := 0x1648c%Z.
Definition FreeListAlloc_entry := 0x163cc%Z.
Ltac sstep := step; fix_lit_store.
Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.

Definition fl_cells (flh fk : Z) : list cell := [C8 (wz flh); C8 (wz 24); C4 (wz 100); C4 (wz fk)].

Definition ffseg1_post (lo FL N flh fk : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' =>
    (fk + 1 < 100 /\ exists a1 a2 a3 a4 (j1 j2 : word) m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs)
       /\ munch [(FL, FL + 24); (N, N + 24)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ rw_cells rsegs m' FL (fl_cells N (fk + 1))
       /\ rw_cells rsegs m' N [C8 (wz flh); C8 j1; C8 j2])
    \/ (100 <= fk + 1 /\ exists a2 a3 a4 m' (j : list byte),
       ms' = MS (mkR (wz 0x16470) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 (wz N) (wz N) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz 0x17fb0) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
       /\ stk rsegs m' lo (bv_unsigned sp + -16)
       /\ rw_cells rsegs m' (bv_unsigned sp + -16) [CB 8 j; C8 ra]).

Lemma ffseg1 : forall (lo FL N flh fk : Z) (n1 n2 n3 : word) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m FL (fl_cells flh fk) -> (bv_unsigned sp <= FL)%Z -> (FL + 24 < 2^64)%Z -> (0 <= fk <= 99)%Z -> (0 <= flh < 2^64)%Z ->
  rw_cells rsegs m N [C8 n1; C8 n2; C8 n3] -> (16 <= N)%Z -> (N + 24 <= lo)%Z ->
  (FL mod 8 = 0)%Z -> (N mod 8 = 0)%Z ->
  evt rsegs (ffseg1_post lo FL N flh fk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz FL) (wz N) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FreeListFree_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FLC FLLO FLHI FK FLH NC N16 NHI AL NAL. unfold FreeListFree_entry, fl_cells in *.
  pose proof (word_lt64 sp) as SPB.
  uwalk_lia_to 0x16424%Z. ub_align.
  uwalk_lia_to 0x16434%Z. step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
  uwalk_lia_to 0x1643c%Z. ucstep. if_cases K2; zify_cond K2. all: rewrite ?signed_lit in K2 by lia.
  -
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST. uwalk_lia_to 0x1646c%Z. step.
    apply evt_done. unfold ffseg1_post. right. split; [lia|]. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat (split; [eassumption|]). exact FR.
  -
    pose proof (munch_refl [(FL, FL + 24); (N, N + 24)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    uwalk_ub_to 0x1645c%Z. step.
    apply evt_done. unfold ffseg1_post, fl_cells. left. split; [lia|]. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
Qed.

Lemma ffseg2 : forall (lo : Z) (j : list byte) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -16) -> (lo + 16 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -16) [CB 8 j; C8 ra] ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs) /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x16470) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evt_done. split; [reflexivity| exact ST].
Qed.

Notation DFRc m q j s1 s0 ra := (rw_cells rsegs m q [CB 8 j; C8 s1; C8 s0; C8 ra]).

Lemma fdsegA : forall (lo FL flh fk : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m FL (fl_cells flh fk) -> (bv_unsigned sp <= FL)%Z -> (FL + 24 < 2^64)%Z -> (0 <= flh < 2^64)%Z ->
  (FL mod 8 = 0)%Z -> (flh mod 8 = 0)%Z ->
  evt rsegs (fun ms' => exists m' j a1',
      ms' = MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz FL) s1 (wz flh) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if flh =? 0 then 0x164d0 else 0x164bc)) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -32) /\ DFRc m' (bv_unsigned sp + -32) j s1 s0 ra
      /\ rw_cells rsegs m' FL (fl_cells flh fk))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FreeListDestroy_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FLC FLLO FLHI FLH AL HAL. unfold FreeListDestroy_entry, fl_cells in *.
  pose proof (word_lt64 sp) as SPB. pose proof (rw_cells_bound rsegs _ _ _ FLC) as FB0. cbn [cells_size csize Nat.add] in FB0.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST. do 4 sstep.
  uwalk_lia_to 0x164a4%Z. ub_align.
  uwalk_lia_to 0x164b0%Z. step. if_cases K1; zify_cond K1.
  - replace (flh =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  - uwalk_ub_to 0x164bc%Z.
    replace (flh =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. do 3 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
Qed.

Lemma fdsegB : forall (N nx : Z) (j1 j2 : word) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  mem_inv rsegs m -> rw_cells rsegs m N [C8 (wz nx); C8 j1; C8 j2] -> (0 < N /\ N + 24 < 2^64)%Z -> (0 <= nx < 2^64)%Z ->
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x164c4) sp gp tp t0 t1 t2 s0 (wz nx) (wz N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz 0x17fb0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x164bc) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI NC NR NX.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep. apply evt_done. reflexivity.
Qed.

Lemma fdsegC : forall (FL hd fk nx : Z) ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  mem_inv rsegs m -> rw_cells rsegs m FL (fl_cells hd fk) -> (0 < FL /\ FL + 24 < 2^64)%Z -> (0 <= nx < 2^64)%Z ->
  (nx mod 8 = 0)%Z ->
  evt rsegs (fun ms' => exists m' a1',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz FL) (wz nx) (wz nx) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if nx =? 0 then 0x164d0 else 0x164bc)) fc None m' (seg_rom rsegs)
      /\ munch [(FL, FL + 24)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' FL (fl_cells nx fk))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz FL) (wz nx) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x164c4) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI FLC FR NX NAL. unfold fl_cells in *.
  pose proof (munch_refl [(FL, FL + 24)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  sstep. zstep. step. if_cases K1; zify_cond K1.
  - uwalk_ub_to 0x164bc%Z.
    replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  - replace (nx =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
Qed.

Lemma fdsegD : forall (lo FL hd fk : Z) (j : list byte) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x9
    (F : bvmap 5 word) fc m,
  stk rsegs m lo (bv_unsigned sp + -32) -> (lo + 32 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  DFRc m (bv_unsigned sp + -32) j s1 s0 ra ->
  rw_cells rsegs m FL (fl_cells hd fk) -> (bv_unsigned sp <= FL)%Z -> (FL + 24 < 2^64)%Z ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (FL, FL + 24)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' FL (fl_cells hd 0))
    (MS (mkR x1 (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz FL) x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x164d0) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST LO LO0 MI FR FLC FLLO FLHI. unfold fl_cells in *. pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (FL, FL + 24)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. sstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evt_done. eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation lbrm k LB := (lb_remove (ai_K_eqb rsegs AI) k LB).
  Hypothesis LOK : layout_ok AI.
  Hypothesis MALPC : al_malloc_pc L = 0x180f0.
  Hypothesis FREEPC : al_free_pc L = 0x17fb0.
  Notation flseg := (flseg AI).
  Notation bsub := (bsub AI).

  #[using="Type"] Lemma flseg_heap_pres : forall FB N (LBK : list BLK) SP m m',
    flseg m FB N -> heap_pres AI LBK SP m m' -> (forall b, In b FB -> In b LBK) -> flseg m' FB N.
  Proof.
    induction FB as [|b FB IH]; intros N LBK SP m m' FLS HP SUB; cbn [H_obj.flseg] in *; [exact FLS|].
    destruct FLS as (NZ & Eb & nx & j1 & j2 & NC & FLS'). split; [exact NZ|]. split; [exact Eb|]. exists nx, j1, j2. split.
    - eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact NC|].
      eapply client_range_block; [apply SUB; left; reflexivity| rewrite Eb; cbn; lia| rewrite Eb; cbn; lia].
    - eapply IH; [exact FLS'| exact HP|]. intros b0 Hb0. apply SUB. right. exact Hb0.
  Qed.

  Definition FreeListFree_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list BLK) (k : K) (FL N lo B : Z) (FB : list BLK) (m : mem)
      : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (flh' fk' : Z) (FB' : list BLK),
      ms' = MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L) [C4 errv'])
      /\ hpx AI [(FL, FL + 24)] (lbrm k LB) (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m' /\ (forall b, In b (lbrm k LB) -> In b LB')
      /\ rw_cells rsegs m' FL (fl_cells flh' fk') /\ flseg m' FB' flh' /\ fk' = Z.of_nat (length FB') /\ (fk' <= 99)%Z
      /\ bsub FB' LB' /\ NoDup (map blk_id FB')
      /\ ((LB' = LB /\ FB' = (k, N, 24) :: FB) \/ (LB' = lbrm k LB /\ FB' = FB)).

  #[using="AC LOK FREEPC"] Theorem FreeListFree_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (k : K) (FL N flh fk lo B : Z) (FB : list BLK) (n1 n2 n3 errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 16 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m FL (fl_cells flh fk) -> (bv_unsigned sp <= FL)%Z -> (FL + 24 <= B)%Z ->
    flseg m FB flh -> fk = Z.of_nat (length FB) -> (fk <= 99)%Z -> bsub FB LB ->
    In (k, N, 24) LB -> rw_cells rsegs m N [C8 n1; C8 n2; C8 n3] -> NoDup (map blk_id ((k, N, 24) :: FB)) ->
    (FL mod 8 = 0)%Z -> a0 = wz FL -> a1 = wz N ->
    SREACH AI (FreeListFree_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB k FL N lo B FB m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz FreeListFree_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI FLC FLLO FLB FLS FK FK99 FSUB HIN NC ND AL -> ->.
    pose proof (word_lt64 sp) as SPR.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (ai_block_range rsegs AI s LB m _ HR HIN) as (R1 & R2 & _ & R4 & _). cbn in R1, R2, R4.
    pose proof (fresh_block_disjoint_errno rsegs AI _ _ _ _ LOK HR HIN) as DE. cbn in DE.
    assert (FLH : (0 <= flh < 2^64)%Z).
    { destruct FB as [|b FB']; cbn [H_obj.flseg] in FLS. { subst flh. lia. }
      destruct FLS as (_ & Eb & _). pose proof (FSUB b (or_introl eq_refl)) as Hb. rewrite Eb in Hb.
      destruct (ai_block_range rsegs AI s LB m _ HR Hb) as (Q1 & _ & _ & Q4 & _). cbn in Q1, Q4. lia. }
    assert (SUBR : forall b, In b (lbrm k LB) -> In b LB) by (intros b Hb; eapply lb_remove_sub; exact Hb).

    assert (FBD : forall b, In b FB -> blk_size b = 24 /\ (N + 24 <= blk_addr b \/ blk_addr b + 24 <= N)%Z /\ In b (lbrm k LB)
                                     /\ (0 < blk_addr b)%Z /\ (blk_addr b + 24 <= alloc_ceiling)%Z).
    { intros b Hb.
      assert (NE : (k, N, 24) <> b) by (eapply (nodup_in_neq AI [(k, N, 24)] FB); [exact ND| left; reflexivity| exact Hb]).
      assert (SZ : blk_size b = 24).
      { clear - FLS Hb. revert flh FLS. induction FB as [|b0 FB IH]; intros flh FLS; [destruct Hb|]. cbn [H_obj.flseg] in FLS.
        destruct FLS as (_ & Eb & nx & j1 & j2 & _ & FLS'). destruct Hb as [<-|Hb]; [rewrite Eb; reflexivity| eapply IH; eauto]. }
      pose proof (FSUB b Hb) as HbL. destruct (ai_block_range rsegs AI s LB m _ HR HbL) as (Q1 & _ & _ & Q4 & _). rewrite SZ in Q4.
      split; [exact SZ|]. split; [| split; [| split; [exact Q1| exact Q4]]].
      - pose proof (ai_blocks_disjoint rsegs AI s LB m _ _ HR HIN HbL NE) as D. cbn in D. rewrite SZ in D. lia.
      - apply (in_lb_remove AI); [exact HbL|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
        intros E. apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact Hb. }
    eapply sreach_evt. { eapply (ffseg1 lo FL N flh fk n1 n2 n3); try eassumption; try LiaTuning.alia. all: Z.div_mod_to_equations; lia. }
    intros ms' [(LT & a1' & a2' & a3' & a4' & j1 & j2 & m1 & -> & MU1 & WM1 & MI1 & FLC1 & NC1)|(GE & a2' & a3' & a4' & m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1)].
    -
      apply sreach_ret. unfold FreeListFree_post.
      do 15 eexists. exists N, (fk + 1)%Z, ((k, N, 24) :: FB). split; [reflexivity|].
      split; [exact MI1|]. split. { eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn; lia]. }
      split. { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|].
        constructor. { left. cbn. lia. } constructor; [| constructor]. right; right; right. exists (k, N, 24). split; [exact HIN|]. cbn. lia. }
      split. { eexists. eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| cbn; lia]. }
      split. { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUBR| exact MU1| exact WM1|].
        constructor. { right; right. cbn. lia. } constructor; [| constructor].
        right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR| exact HIN| | lia| cbn; lia].
        intros b0 Hb0. split; [apply SUBR; exact Hb0|]. intros ->. exact (lb_remove_neq rsegs AI _ _ _ Hb0 eq_refl). }
      split. { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|].
        constructor. { left. cbn. lia. } constructor; [| constructor]. right; right; right. exists (k, N, 24). split; [exact HIN|]. cbn. lia. }
      split; [exact SUBR|]. split; [exact FLC1|]. split.
      { cbn [H_obj.flseg]. split; [lia|]. split; [reflexivity|]. exists flh, j1, j2. split; [exact NC1|].
        eapply (flseg_transport AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb. destruct (FBD b Hb) as (_ & D & _ & Q1 & Q4). cbn. lia. }
      split; [cbn; lia|]. split; [cbn; lia|]. split. { intros b [<-|Hb]; [exact HIN| apply FSUB; exact Hb]. } split; [exact ND|].
      left. split; reflexivity.
    -
      assert (HR1 : RHEAP rsegs AI s LB m1).
      { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      assert (HE1 : RENV rsegs AI m1 B).
      { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
      pose proof (rw_cells_transport rsegs _ m m1 _ _ FLC MU1 WM1 ltac:(cbn; lia)) as FLC1.
      assert (FL1 : flseg m1 FB flh).
      { eapply (flseg_transport AI); [exact FLS| exact MU1| exact WM1|]. intros b Hb. destruct (FBD b Hb) as (_ & D & _ & Q1 & Q4). cbn. lia. }
      assert (HP1 : hpx AI [(FL, FL + 24)]%Z (lbrm k LB) (bv_unsigned sp) m m1).
      { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUBR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
      eapply sreach_bind.
      { rewrite <- FREEPC. eapply (ac_free rsegs AI AC) with (lo := lo) (B := B); try eassumption; try reflexivity;
          rewrite ?unsigned_lit by lia; try lia; try eassumption. }
      intros s' LB' ms'' POST. unfold free_post in POST. destruct_exs POST. destruct POST as (-> & AF & -> & HR2).
      destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      replace (ret_pc (Z_to_bv 64 0x16470)) with (Z_to_bv 64 0x16470) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR1 ltac:(apply client_range_above; cbn; lia)) as FR2.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FLC1 ltac:(apply client_range_above; unfold fl_cells; cbn; lia)) as FLC2.
      assert (FL2 : flseg m2 FB flh).
      { clear - FL1 HPF FBD. revert flh FL1. induction FB as [|b FB IH]; intros flh FL1; cbn [H_obj.flseg] in *; [exact FL1|].
        destruct FL1 as (NZ & Eb & nx & j1 & j2 & NCb & FLS'). split; [exact NZ|]. split; [exact Eb|]. exists nx, j1, j2. split.
        - eapply (heap_pres_rw_cells rsegs AI); [exact HPF| exact NCb|]. destruct (FBD b (or_introl eq_refl)) as (_ & _ & Hb & _).
          eapply client_range_block; [exact Hb| rewrite Eb; cbn; lia| rewrite Eb; cbn; lia].
        - apply IH; [| exact FLS']. intros b0 Hb0. apply FBD. right. exact Hb0. }
      eapply sreach_evt. { eapply (ffseg2 lo j); try eassumption; lia. }
      intros ms' [-> ST3]. apply sreach_ret. unfold FreeListFree_post.
      do 15 eexists. exists flh, fk, FB. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST3|]. split; [exact HE2|]. split; [eexists; exact ERR2|]. split.
      { eapply (hpx_trans rsegs AI); [exact HP1|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| auto]. }
      split; [exact HR2|]. split; [auto|]. split; [exact FLC2|]. split; [exact FL2|]. split; [exact FK|]. split; [lia|].
      split. { intros b Hb. destruct (FBD b Hb) as (_ & _ & X & _). exact X. } split. { cbn in ND. inversion ND; assumption. }
      right. split; reflexivity.
  Qed.

  Definition FreeListDestroy_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LBK : list BLK) (FL lo B : Z) (m : mem) : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ RENV rsegs AI m' B
      /\ (exists errv', rw_cells rsegs m' (al_errno L) [C4 errv'])
      /\ hpx AI [(FL, FL + 24)] LBK (bv_unsigned sp) m m'
      /\ RHEAP rsegs AI s' LB' m' /\ bsub LBK LB'
      /\ rw_cells rsegs m' FL (fl_cells 0 0).

  #[using="AC LOK FREEPC"] Lemma fld_loop : forall (FB : list BLK) (N : Z) ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x9
      (F : bvmap 5 word) fc (m0 m : mem) s LB (LBK : list BLK) (FL fk lo B : Z) (j : list byte) (errv : word),
    flseg m FB N -> N <> 0 -> bsub FB LB -> bsub LBK LB -> NoDup (map blk_id (FB ++ LBK)) ->
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp + -32) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 32 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    DFRc m (bv_unsigned sp + -32) j s1 s0 ra ->
    rw_cells rsegs m FL (fl_cells N fk) -> (bv_unsigned sp <= FL)%Z -> (FL + 24 <= B)%Z -> (0 <= fk < 2^31)%Z ->
    hpx AI [(FL, FL + 24)]%Z LBK (bv_unsigned sp) m0 m ->
    SREACH AI (FreeListDestroy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK FL lo B m0)
      (MS (mkR x1 (wz (bv_unsigned sp + -32)) gp (wz (al_tp L)) t0 t1 t2 (wz FL) x9 (wz N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x164bc) fc None m (seg_rom rsegs)) s LB.
  Proof.
    induction FB as [|b FB IH]; intros until errv; intros FLS NZ FSUB KSUB ND HR HE SPB BHI ST CEIL LO STK ERR MI FR FLC FLLO FLB FK HP0.
    { cbn [H_obj.flseg] in FLS. exfalso. exact (NZ FLS). }
    cbn [H_obj.flseg] in FLS. destruct FLS as (_ & Eb & nx & j1 & j2 & NC & FLS').
    pose proof (word_lt64 sp) as SPR.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    pose proof (FSUB b (or_introl eq_refl)) as HIN. rewrite Eb in HIN.
    destruct (ai_block_range rsegs AI s LB m _ HR HIN) as (R1 & R2 & _ & R4 & _). cbn in R1, R2, R4.
    assert (NXR : (0 <= nx < 2^64)%Z).
    { destruct FB as [|b' FB']; cbn [H_obj.flseg] in FLS'. { subst nx. lia. }
      destruct FLS' as (_ & Eb' & _). pose proof (FSUB b' (or_intror (or_introl eq_refl))) as Hb'. rewrite Eb' in Hb'.
      destruct (ai_block_range rsegs AI s LB m _ HR Hb') as (Q1 & _ & _ & Q4 & _). cbn in Q1, Q4. lia. }
    assert (NXA : (nx mod 8 = 0)%Z).
    { destruct FB as [|b' FB']; cbn [H_obj.flseg] in FLS'. { subst nx. reflexivity. }
      destruct FLS' as (_ & Eb' & _). pose proof (FSUB b' (or_intror (or_introl eq_refl))) as Hb'. rewrite Eb' in Hb'.
      destruct (ai_block_range rsegs AI s LB m _ HR Hb') as (_ & Q2 & _). cbn in Q2. Z.div_mod_to_equations. lia. }

    assert (KEEP : forall b0, In b0 (FB ++ LBK) -> In b0 (lbrm (blk_id b) LB)).
    { intros b0 Hb0. apply (in_lb_remove AI).
      - apply in_app_or in Hb0. destruct Hb0 as [H|H]; [apply FSUB; right; exact H| apply KSUB; exact H].
      - cbn in ND. inversion ND as [|x l NI ND']; subst. intros E. apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact Hb0. }
    eapply sreach_evt. { eapply (fdsegB N nx j1 j2); try eassumption; lia. }
    intros ms' ->.
    eapply sreach_bind.
    { rewrite <- FREEPC. eapply (ac_free rsegs AI AC) with (lo := lo) (B := B); try eassumption; try reflexivity;
        rewrite ?unsigned_lit by lia; try lia; try eassumption. }
    intros s' LB' ms'' POST. unfold free_post in POST. destruct_exs POST. destruct POST as (-> & AF & -> & HR2).
    destruct AF as (MI2 & ST2 & HE2 & [errv2 ERR2] & HPF). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in HPF by lia.
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    replace (ret_pc (Z_to_bv 64 0x164c4)) with (Z_to_bv 64 0x164c4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FR ltac:(apply client_range_above; cbn; lia)) as FR2.
    pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF FLC ltac:(apply client_range_above; unfold fl_cells; cbn; lia)) as FLC2.
    assert (HP2 : hpx AI [(FL, FL + 24)]%Z LBK (bv_unsigned sp) m0 m2).
    { eapply (hpx_trans rsegs AI); [exact HP0|]. apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia|].
      intros b0 Hb0. apply KEEP. apply in_or_app. right. exact Hb0. }
    assert (FLS2 : flseg m2 FB nx).
    { eapply flseg_heap_pres; [exact FLS'| exact HPF|]. intros b0 Hb0. apply KEEP. apply in_or_app. left. exact Hb0. }
    assert (ND2 : NoDup (map blk_id (FB ++ LBK))) by (cbn in ND; inversion ND; assumption).
    eapply sreach_evt. { eapply (fdsegC FL N fk nx); try eassumption; lia. }
    intros ms' (m3 & a1x & -> & MU3 & WM3 & MI3 & FLC3).
    assert (HR3 : RHEAP rsegs AI s' (lbrm (blk_id b) LB) m3).
    { eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE3 : RENV rsegs AI m3 B).
    { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|]. constructor; [| constructor]. left. cbn. lia. }
    pose proof (rw_cells_transport rsegs _ m2 m3 _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
    pose proof (rw_cells_transport rsegs _ m2 m3 _ _ FR2 MU3 WM3 ltac:(cbn; lia)) as FR3.
    assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -32)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]).
    assert (FLS3 : flseg m3 FB nx).
    { eapply (flseg_transport AI); [exact FLS2| exact MU3| exact WM3|]. intros b0 Hb0.
      pose proof (KEEP b0 ltac:(apply in_or_app; left; exact Hb0)) as Hk. apply (lb_remove_sub rsegs AI) in Hk.
      destruct (ai_block_range rsegs AI s LB m _ HR Hk) as (Q1 & _ & Q3 & Q4 & _). cbn in Q1, Q3, Q4 |- *. lia. }
    assert (HP3 : hpx AI [(FL, FL + 24)]%Z LBK (bv_unsigned sp) m0 m3).
    { eapply (hpx_trans rsegs AI); [exact HP2|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| | exact MU3| exact WM3|].
      - intros b0 Hb0. apply KEEP. apply in_or_app. right. exact Hb0.
      - constructor; [| constructor]. right; right. cbn. lia. }
    destruct (Z.eqb_spec nx 0) as [NX0|NX1].
    -
      eapply sreach_evt. { eapply (fdsegD lo FL nx fk j); try eassumption; lia. }
      intros ms' (m4 & -> & MU4 & WM4 & MI4 & ST4 & FLC4).
      pose proof (rw_cells_transport rsegs _ m3 m4 _ _ ERR3 MU4 WM4 ltac:(cbn; lia)) as ERR4.
      apply sreach_ret. unfold FreeListDestroy_post. subst nx.
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MI4|]. split; [exact ST4|]. split.
      { eapply (ai_env_frame rsegs AI); [exact HR3| exact HE3| exact MU4| exact WM4|].
        constructor. { left. cbn. lia. } constructor; [| constructor]. left. cbn. lia. }
      split; [eexists; exact ERR4|]. split.
      { eapply (hpx_trans rsegs AI); [exact HP3|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR3| | exact MU4| exact WM4|].
        - intros b0 Hb0. apply KEEP. apply in_or_app. right. exact Hb0.
        - constructor. { left. cbn. lia. } constructor; [| constructor]. right; right. cbn. lia. }
      split. { eapply (ai_heap_frame rsegs AI); [exact HR3| exact MU4| exact WM4|]. constructor. { left. cbn. lia. } constructor; [| constructor]. left. cbn. lia. }
      split; [| exact FLC4]. intros b0 Hb0. apply KEEP. apply in_or_app. right. exact Hb0.
    -
      eapply (IH nx); try eassumption; try LiaTuning.alia.
      + intros b0 Hb0. apply KEEP. apply in_or_app. left. exact Hb0.
      + intros b0 Hb0. apply KEEP. apply in_or_app. right. exact Hb0.
  Qed.

  #[using="AC LOK FREEPC"] Theorem FreeListDestroy_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (LBK FB : list BLK) (FL flh fk lo B : Z) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z -> (B < 2^64)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - 32 - al_stack L)%Z -> (0 <= al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m FL (fl_cells flh fk) -> (bv_unsigned sp <= FL)%Z -> (FL + 24 <= B)%Z -> (0 <= fk < 2^31)%Z ->
    flseg m FB flh -> bsub FB LB -> bsub LBK LB -> NoDup (map blk_id (FB ++ LBK)) ->
    (FL mod 8 = 0)%Z -> a0 = wz FL ->
    SREACH AI (FreeListDestroy_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LBK FL lo B m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz FreeListDestroy_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB BHI ST CEIL LO STK ERR MI FLC FLLO FLB FK FLS FSUB KSUB ND AL ->.
    pose proof (word_lt64 sp) as SPR.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (FLH : (0 <= flh < 2^64)%Z).
    { destruct FB as [|b FB']; cbn [H_obj.flseg] in FLS. { subst flh. lia. }
      destruct FLS as (_ & Eb & _). pose proof (FSUB b (or_introl eq_refl)) as Hb. rewrite Eb in Hb.
      destruct (ai_block_range rsegs AI s LB m _ HR Hb) as (Q1 & _ & _ & Q4 & _). cbn in Q1, Q4. lia. }
    assert (FHA : (flh mod 8 = 0)%Z).
    { destruct FB as [|b FB']; cbn [H_obj.flseg] in FLS. { subst flh. reflexivity. }
      destruct FLS as (_ & Eb & _). pose proof (FSUB b (or_introl eq_refl)) as Hb. rewrite Eb in Hb.
      destruct (ai_block_range rsegs AI s LB m _ HR Hb) as (_ & Q2 & _). cbn in Q2. Z.div_mod_to_equations. lia. }
    eapply sreach_evt. { eapply (fdsegA lo FL flh fk); try eassumption; lia. }
    intros ms' (m1 & j & a1x & -> & MU1 & WM1 & MI1 & ST1 & FR1 & FLC1).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    assert (FLS1 : flseg m1 FB flh).
    { eapply (flseg_transport AI); [exact FLS| exact MU1| exact WM1|]. intros b0 Hb0. pose proof (FSUB b0 Hb0) as Hk.
      destruct (flseg_shape AI _ _ _ _ FLS Hb0) as [Eb0 _].
      destruct (ai_block_range rsegs AI s LB m _ HR Hk) as (Q1 & _ & Q3 & Q4 & _). rewrite Eb0 in Q4. cbn in Q1, Q3, Q4 |- *. lia. }
    assert (HP1 : hpx AI [(FL, FL + 24)]%Z LBK (bv_unsigned sp) m m1).
    { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact KSUB| exact MU1| exact WM1|]. constructor; [| constructor]. left. cbn. lia. }
    destruct (Z.eqb_spec flh 0) as [F0|F1].
    -
      eapply sreach_evt. { eapply (fdsegD lo FL flh fk j); try eassumption; lia. }
      intros ms' (m4 & -> & MU4 & WM4 & MI4 & ST4 & FLC4).
      pose proof (rw_cells_transport rsegs _ m1 m4 _ _ ERR1 MU4 WM4 ltac:(cbn; lia)) as ERR4.
      apply sreach_ret. unfold FreeListDestroy_post. subst flh.
      repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
      split; [exact MI4|]. split; [exact ST4|]. split.
      { eapply (ai_env_frame rsegs AI); [exact HR1| exact HE1| exact MU4| exact WM4|].
        constructor. { left. cbn. lia. } constructor; [| constructor]. left. cbn. lia. }
      split; [eexists; exact ERR4|]. split.
      { eapply (hpx_trans rsegs AI); [exact HP1|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR1| exact KSUB| exact MU4| exact WM4|].
        constructor. { left. cbn. lia. } constructor; [| constructor]. right; right. cbn. lia. }
      split. { eapply (ai_heap_frame rsegs AI); [exact HR1| exact MU4| exact WM4|]. constructor. { left. cbn. lia. } constructor; [| constructor]. left. cbn. lia. }
      split; [exact KSUB| exact FLC4].
    - eapply (fld_loop FB flh); try eassumption; try LiaTuning.alia.
  Qed.

  #[using="Type"] Lemma flaseg : forall (FL fk : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m FL (fl_cells 0 fk) -> (0 < FL /\ FL + 24 < 2^64)%Z -> (FL mod 8 = 0)%Z ->
    evt rsegs (fun ms' => exists a1', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 24) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (wz 0x180f0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz FreeListAlloc_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI FLC FLR AL. unfold FreeListAlloc_entry. unfold fl_cells in FLC.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    uwalk_ub_to 0x16414%Z. step.
    apply evt_done. eexists. reflexivity.
  Qed.

  #[using="AC MALPC"] Theorem FreeListAlloc_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc m s LB (FL fk lo B : Z) (errv : word),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> (bv_unsigned sp <= B)%Z ->
    stk rsegs m lo (bv_unsigned sp) -> (alloc_ceiling <= lo)%Z -> (lo <= bv_unsigned sp - al_stack L)%Z ->
    rw_cells rsegs m (al_errno L) [C4 errv] -> mem_inv rsegs m ->
    rw_cells rsegs m FL (fl_cells 0 fk) -> (0 < FL /\ FL + 24 < 2^64)%Z -> (FL mod 8 = 0)%Z ->
    a0 = wz FL ->
    SREACH AI (malloc_post AI ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB 24 lo B m)
      (MS (mkR ra sp gp (wz (al_tp L)) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz FreeListAlloc_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until errv. intros HR HE SPB ST CEIL LO ERR MI FLC FLR AL ->.
    eapply sreach_evt. { eapply (flaseg FL fk); eassumption. }
    intros ms' [a1' ->]. rewrite <- MALPC. eapply (ac_malloc rsegs AI AC); try eassumption; try reflexivity; lia.
  Qed.
End W.
