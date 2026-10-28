From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs Atp_kitu El_defs El_acc_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd Str_tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).

Section Acc.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Lemma acc_3c74c_spec : forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (q node r : Z) (jr : list byte),
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m -> mem_inv usegs m -> frm0 fc ->
    stk usegs m (ae_lo E) q -> ae_lo E <= q - 32 -> q <= node -> node + 16 <= ae_B E -> q <= ae_DOC E ->
    rw_cells usegs m r [CB 24 jr] -> q <= r -> r + 24 <= ae_B E ->
    evt usegs (acc_post_r 32 r ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (ae_lo E) m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 r) (Z_to_bv 64 node) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3c74c) fc None m (seg_rom usegs)).
  Proof.
    intros until jr. intros AI ROOT HEAP MI FRM ST LOQ QN NB QD RC QR RB.
    destruct (acc_facts E OK s m HEAP) as ((T0 & TH & T8) & (S0 & SH) & (NR & SNR) & (CEIL & DB & B63 & D8) & TIR & EL).
    destruct AI as (TAPEB & SBUFB & PTRB & DOCC). unfold el_root in ROOT.
    pose proof alloc_ceiling_range as CR. assert (LO0 : 0 <= ae_lo E) by lia.
    pose proof (length_map (Z_to_bv 64) (ae_tws E)) as LMT. pose proof (length_map (Z_to_bv 8) (ae_sbs E)) as LMS. clear PTRB.
    pose proof (munch_refl ([(q - 32, q); (r, r + 24)])%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

    apply (rw_cells_split_CB usegs _ _ [] 24 jr [] [8; 8; 4; 4]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
    step. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step.
    astep. step. if_lia.
    step. zstep. rewrite (land7_mod8 (ae_DOC E) ltac:(lia) D8). step. if_lia.
    step. astep. step. step. acc_tix E (0x3c780)%Z.
    pose proof (tape_read_type _ (ae_TAPE E) (ae_tws E) 1 TAPEB ltac:(lia) TIR) as RDB.
    astep. step. step. if_cases K; zify_cond K; clear K.
    - step. if_lia. step. lstep. lstep. lstep.
      astep. astep. astep. step. release_frame FR ST q. step. acc_fin_r.
    - step. if_lia. astep. astep. lstep. lstep. lstep. step.
      astep. astep. astep. step. release_frame FR ST q. step. acc_fin_r.
  Qed.
End Acc.
End WithCeiling0.
