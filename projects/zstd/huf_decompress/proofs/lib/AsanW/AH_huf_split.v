(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer HufHarness.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface
     AH_huf_kit AH_huf_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AH_huf_split () := "C59OSSVerify5KrLib4Spec5ProgA3AStC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness;fuzz_mallocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec5ProgA<new_handlerAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness7dt_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9dbuf_sizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW<AH_huf_split8fz_restAC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec<AsanProgDeps3APS00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec<AsanProgDeps9amalloc_MC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec<AsanProgDeps:AAllocAsanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness=PRODUCER_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7Harness9WKSP_SIZEC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.

Definition PC_HMA : Z := 0x80108.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fz_restA (producer dt wksp dBuf : option AsanCtrl.aptr) : MA Z :=
  Harness.free_opt afree_M dt ;;; Harness.free_opt afree_M wksp ;;; Harness.free_opt afree_M dBuf ;;;
  Harness.free_opt afree_M producer ;;; mret 0.

Lemma fuzz_oneA_split_huf : forall pl,
  fuzz_oneA AAllocAsan pl =
  (producer <- Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) PRODUCER_SIZE ;;
   dt <- Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) (dt_size pl) ;;
   wksp <- Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) WKSP_SIZE ;;
   dBuf <- Harness.fuzz_malloc amalloc_M (new_handlerA AAllocAsan) (dbuf_size pl) ;;
   fz_restA producer dt wksp dBuf).
Proof.
ltac2:(KReplay.run1 (kr_t_AH_huf_split ()) ["CANSEC1"] "h04dBufh12dth22plh38producerh44wkspp;1p;2p;5p;4g0000R0p4p711g000cR1p4p710p8g001TR2p4p70R3g002KR4p4p7210p8P3g003HR5p4p7210p8P3p1004=p4p710p8g004Zj1<TP0j1;TP1j24Tg005:j13Tg005\j1:TP4j51Tg006Xj17Tg007Qj15Tg008Lj46Tg009Lj28TP5j59Tg009fR5P2g00:bR4f1R1f0R0D1p=2P5f2R3g00;bR6P1P0D9p=0%<6g00<@R7#;/46%32R6P5P2P4%:7R7g00=AD1%71,27P5P2P4P7g00>@D1f3R4#5,27P4P3P1P0C6X06506X46506X16506X3630'8W2o"). Qed.

Section State.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)
  Definition hMA_state (L : alayout) (RNG0 : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (s : APS) (LB : list ablock) (D : Z) (pl : list Z) (lo : Z) (m0 : amem)
      (producer dt wksp dBuf : option AsanCtrl.aptr) (s' : APS) (RNG1 : footprint) (ms : machine_state) : Prop :=
    exists (pP pd pw : AsanCtrl.aptr) (P DT W DST : Z) (LBd : list ablock) (f1 f2 f3 f4 f5 : Z) (j0 jdt : list byte)
           (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : amem),
      producer = Some pP /\ dt = Some pd /\ wksp = Some pw
      /\ ((dBuf = None /\ DST = 0 /\ hp_dbuf (huf_draws pl (zlen pl)) = 0 /\ LBd = [])
          \/ (exists pb, dBuf = Some pb /\ LBd = [HB pb DST (hp_dbuf (huf_draws pl (zlen pl)))]
                         /\ 0 < hp_dbuf (huf_draws pl (zlen pl)) /\ ablock_range DST (hp_dbuf (huf_draws pl (zlen pl)))))
      /\ ms = MS (mkR (Z_to_bv 64 PC_HMA) (Z_to_bv 64 (bv_unsigned sp - 128)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 D)
                      (Z_to_bv 64 DST) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 f5) (Z_to_bv 64 (hp_mtl (huf_draws pl (zlen pl)))) (Z_to_bv 64 DT)
                      (Z_to_bv 64 (hp_dbuf (huf_draws pl (zlen pl)))) (Z_to_bv 64 W) (Z_to_bv 64 ASHOFF)
                      (Z_to_bv 64 f1) (Z_to_bv 64 f2) (Z_to_bv 64 f3) (Z_to_bv 64 f4) t3 t4 t5 t6)
                 FR (Z_to_bv 64 PC_HMA) fc None m (seg_rom asegs)
      /\ 0 <= f1 <= 1 /\ 0 <= f2 <= 1 /\ 0 <= f3 <= 1 /\ 0 <= f4 <= 1 /\ 0 <= f5 <= 1
      (* [comment removed for export] *)
      /\ AHEAP AI L RNG1 (aps_m s') (LBd ++ HB pw W 8704 :: HB pd DT (DT_BYTES (hp_mtl (huf_draws pl (zlen pl))))
                                          :: HB pP P PRODUCER_SIZE :: LB) m
      /\ aps_rest s' = aps_rest s /\ fp_le RNG0 RNG1
      /\ magree asegs (aclient_addr CI LB (bv_unsigned sp)) m0 m
      /\ ablock_range P PRODUCER_SIZE /\ ablock_range DT (DT_BYTES (hp_mtl (huf_draws pl (zlen pl)))) /\ ablock_range W 8704
      (* [comment removed for export] *)
      /\ rw_cells asegs m DT [CB (Z.to_nat (DT_BYTES (hp_mtl (huf_draws pl (zlen pl))))) jdt]
      /\ prod_atA m P D (hp_rest (huf_draws pl (zlen pl)))
      /\ bytes_at asegs m D (map (Z_to_bv 8) pl)
      (* [comment removed for export] *)
      /\ rw_cells asegs m (bv_unsigned sp - 128)
           [CB 8 j0; C8 (Z_to_bv 64 (hp_streams (huf_draws pl (zlen pl)))); C8 (Z_to_bv 64 (hp_symbols (huf_draws pl (zlen pl))))]
      /\ rw_cells asegs m (bv_unsigned sp + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
      /\ stk asegs m lo (bv_unsigned sp - 128)
      /\ mem_inv asegs m.
End State.
End CANSEC1.
