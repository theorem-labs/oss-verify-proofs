(* op_read (fuzz_link.c:677-700), plain image: segments S4 and S5 of the arm, after the first free.

     S4  0x13f68  mv a0, s4 ; jal free                -> c0_cut_fa (free (alias) at 0x173d4, ra 0x13f70)
     S5  0x13f70  ld s7, 0x20(sp) ; addi s8, zero, 0xab ; bltu s5, s11, L_EXIT
         0x13f7c  j L_TAIL
         0x1406c  ld s2, 0x48(sp) ; addiw s11, s11, 1 ; bnez s2, L_LH
         0x14078  j L_EXIT                                -> lh_ms E (i + 1) gp \/ ex_ms E gp

   Neither segment calls a function or writes memory, so each post carries `seg_fp` with the empty
   window. Every address is read from the plain image (link/ct/dis/plain/LLVMFuzzerTestOneInput.s,
   lines 457-462 and 522-525). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC0Defs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Helpers
   ========================================================================== *)

(* a segment that writes nothing stays in every footprint (the empty window) *)
Lemma c0t_seg_fp_refl : forall (S : Z) (hp : list (Z * Z)) (m : word -> option byte), seg_fp S hp m m.
Proof.
  intros S hp m. exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
  intros x _ Ho. exfalso. apply Ho. exact I.
Qed.

(* addiw s11, s11, 1 on the operation counter *)
Lemma c0t_addiw1 : forall i, 0 <= i <= 46 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 i) + 1)) = Z_to_bv 64 (i + 1).
Proof.
  intros i Hi. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

(* the arm's frame as lh_mem states it: the 40 + 216 bytes after wa are one 256-byte cell again *)
Lemma c0t_frame_lh : forall E P N wa wk m, c0_frame E P N wa wk m ->
  exists j0 j1 j2 nc, rw_cells rsegs m (e_S E - SLOT_FRAME) (lh_cells (e_md E) (e_mk E) P nc j0 j1 j2).
Proof.
  intros E P N wa wk m (j0 & j2 & FR). unfold c0_cells in FR.
  pose proof (rw_cells_merge rsegs m (e_S E - SLOT_FRAME)
    [CB 8 j0; C8 (wz A_ODD); C8 (wz (e_md E + MD_MARK)); C8 (wz A_EMPTY); C8 (wz (e_mk E));
     C8 (wz A_G_NAMES); C8 (wz A_JT); C8 (wz GNL42); C8 (wz P); C8 (wz N); CB 40 wa]
    [CB 40 wk; CB 216 j2] [] FR) as M.
  exists j0, wa, (cells_bytes [CB 40 wk; CB 216 j2]), N. exact M.
Qed.

(* the arm's frame as ex_ms states it: one 376-byte cell *)
Lemma c0t_frame_ex : forall E P N wa wk m, c0_frame E P N wa wk m ->
  exists j, rw_cells rsegs m (e_S E - SLOT_FRAME) [CB 376 j].
Proof.
  intros E P N wa wk m (j0 & j2 & FR). exact (rw_cells_forget rsegs m _ _ FR).
Qed.

(* ==========================================================================
   2. S4: 0x13f68 -> the call free (alias) at 0x173d4, ra 0x13f70
   ========================================================================== *)

Lemma c0_s4 : forall E i gp P N ac A kbs mbs gbs ms,
  lenv_ok E -> c0_ret_fk E i gp P N ac A kbs mbs gbs ms ->
  evt rsegs (eqv_cl (fun ms' => c0_cut_fa E i gp P N ac A kbs mbs gbs ms' /\
                                seg_fp (e_S E) (c0_hpA E ac A) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp P N ac A kbs mbs gbs ms HE H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s7 & s8
    & t3 & t4 & t5 & t6 & F & fc & m & wa & wk & EQ & FC & Hi & Hac & HN & HA & HO & HOC
    & HA0 & HA1 & HF & HB).
  subst ms. cbn [ms_mem].
  unfold C0_RA_FK, wz.
  step. step.
  apply evt_done. apply c0_eqv_intro. split; [| exact (c0t_seg_fp_refl _ _ _)].
  unfold c0_cut_fa. do 18 eexists. exists F, fc, m, wa, wk.
  split; [reflexivity|].
  exact (conj FC (conj Hi (conj Hac (conj HN (conj HA (conj HO (conj HOC (conj HA0 (conj HA1
           (conj HF HB)))))))))).
Qed.

(* ==========================================================================
   3. S5: 0x13f70 -> the loop head of operation i + 1, or L_EXIT
   ========================================================================== *)

Lemma c0_s5 : forall E i gp P N kbs mbs gbs ms,
  lenv_ok E -> c0_ret_fa E i gp P N kbs mbs gbs ms ->
  evt rsegs (eqv_cl (fun ms' => ((i < 47 /\ lh_ms E (i + 1) gp ms') \/ ex_ms E gp ms') /\
                                seg_fp (e_S E) (c0_hp2 E) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp P N kbs mbs gbs ms HE H.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s7 & s8
    & t3 & t4 & t5 & t6 & F & fc & m & wa & wk & EQ & FC & Hi & HN & HO & HOC & HF & HB).
  subst ms. cbn [ms_mem].
  pose proof HF as (j0 & j2 & FR).
  pose proof HB as (SV & NA & NW & IT & NO & NM & GN & OD & PRo & LA & TX & IP & MA & MW & KA & KW
    & KR & CU & ER & GD & MI & TM & ST).
  assert (HN26 : N < 2 ^ 26).
  { pose proof CU as (_ & k & Hk & _ & HNk).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & HL & _). lia. }
  pose proof (c0t_frame_lh E P N wa wk m HF) as FL.
  unfold c0_cells, wz in FR.
  unfold C0_RA_FA, wz.
  (* 0x13f70 ld s7, 0x20(sp) ; 0x13f74 addi s8, zero, 0xab ; 0x13f78 bltu s5, s11 *)
  step. step. step.
  if_cases HC; zify_cond HC; rewrite ?unsigned_lit in HC by lia.
  - (* 46 < i: the loop is over, L_EXIT *)
    destruct (c0t_frame_ex E P N wa wk m HF) as (jx & FX).
    apply evt_done. apply c0_eqv_intro. split; [right | exact (c0t_seg_fp_refl _ _ _)].
    unfold ex_ms. do 26 eexists. exists F, fc, m, jx.
    split; [reflexivity|].
    exact (conj FC (conj FX (conj SV (conj ER (conj GD (conj LA (conj MI (conj TM ST)))))))).
  - (* 0x13f7c j L_TAIL ; 0x1406c ld s2, 0x48(sp) ; addiw s11, s11, 1 ; bnez s2, L_LH *)
    step. step. step.
    rewrite (c0t_addiw1 i) by lia.
    step.
    if_cases HZ; zify_cond HZ; rewrite ?unsigned_lit in HZ by lia.
    + (* N <> 0: the loop head of operation i + 1 *)
      apply evt_done. apply c0_eqv_intro. split; [left; split; [lia|] | exact (c0t_seg_fp_refl _ _ _)].
      unfold lh_ms. do 18 eexists. exists F, fc, m, P, N, kbs, mbs, gbs.
      split; [reflexivity|].
      split; [exact FC|]. split; [lia|]. split; [lia|].
      split; [| exact (conj MI (conj TM ST))].
      unfold lh_mem.
      refine (conj FL (conj SV (conj NA (conj NW (conj IT (conj NO (conj NM (conj HOC (conj _
        (conj GN (conj OD (conj PRo (conj LA (conj TX (conj IP (conj MA (conj MW (conj KA (conj KW
        (conj KR (conj CU (conj ER GD)))))))))))))))))))))); lia.
    + (* N = 0: 0x14078 j L_EXIT *)
      step.
      destruct (c0t_frame_ex E P N wa wk m HF) as (jx & FX).
      apply evt_done. apply c0_eqv_intro. split; [right | exact (c0t_seg_fp_refl _ _ _)].
      unfold ex_ms. do 26 eexists. exists F, fc, m, jx.
      split; [reflexivity|].
      exact (conj FC (conj FX (conj SV (conj ER (conj GD (conj LA (conj MI (conj TM ST)))))))).
Qed.
