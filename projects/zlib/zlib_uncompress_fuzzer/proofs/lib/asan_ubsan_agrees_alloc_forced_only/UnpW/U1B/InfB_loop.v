(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import U2BObj U2BClient U2BIface InfBBase InfBKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Export InfB_loop0.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.U1B Require Import InfB_loopA InfB_loopB.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BKit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section S.
  Variable AI : AMallocIface.
  Variables (L : alayout) (RNG : footprint) (stA : astate) (LB : list ablock).
  Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32) (POST : machine_state -> Prop).
  Variables (LBc : list ablock) (m0 : amem) (payload : list Z) (fw : Z -> Z) (saved fk fksh : list cell).

  Notation KDISPB cx ly B := (KDISP cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation KLV cx ly := (KLEAVE cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh).
  Notation KALLB cx ly B := (KALL cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh B).
  Notation ARMSOK cx ly := (arms_ok AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly).

  Section Step.
  Hypothesis PAYR : Forall (fun c => 0 <= c < 256) payload.

  Lemma kdisp_step : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> ARMSOK cx ly -> KDISPB cx ly B -> KDISPB cx ly (B + 1).
  Proof.
    intros cx ly B CTX PLEN KL ARMS KD. unfold KDISP. intros until m. intros SI ME ARR VIS HID.
    pose proof SI as (_ & _ & _ & MO). pose proof (reach_cases _ (proj1 MO)) as CASES. clear MO.
    assert (AB : modesA (t_mode st) \/ modesB (t_mode st)) by (unfold modesA, modesB; clear - CASES; tauto).
    destruct AB as [PA|PB].
    - eapply (kdisp_step_A AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh PAYR cx ly B CTX PLEN KL ARMS KD); eassumption.
    - eapply (kdisp_step_B AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh PAYR cx ly B CTX PLEN KL ARMS KD); eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma loop_nat : forall cx ly (k : nat), inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> ARMSOK cx ly -> KDISPB cx ly (Z.of_nat k).
  Proof.
    intros cx ly k CTX PLEN KL ARMS. induction k as [|k IH].
    - unfold KDISP. intros until m. intros SI ME. exfalso. pose proof (meas_nonneg _ _ _ _ SI). cbn [Z.of_nat] in ME. lia.
    - rewrite Nat2Z.inj_succ. apply kdisp_step; assumption.
  Qed.

  Theorem loop_kdisp : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> ARMSOK cx ly -> KDISPB cx ly B.
  Proof. intros cx ly B CTX PLEN KL ARMS. apply (kdisp_mono AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly (Z.of_nat (Z.to_nat B))); [lia| apply loop_nat; assumption]. Qed.

  Theorem loop_kall : forall cx ly B, inf_ctx cx ly AI RNG LB -> Z.of_nat (length payload) = c_n cx -> KLV cx ly -> ARMSOK cx ly -> KALLB cx ly B.
  Proof. intros cx ly B CTX PLEN KL ARMS. apply kall_of_kdisp; [exact CTX| exact PLEN| exact KL| apply loop_kdisp; assumption]. Qed.
  End Step.
End S.
End CANSEC1.
