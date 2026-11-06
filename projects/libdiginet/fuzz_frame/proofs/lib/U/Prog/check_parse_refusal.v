(* proves the UBSan contract of check_parse_refusal (U/Prog/check_parse_refusal_c.v) by a walk of fuzz_frame.ubsan. *)
(* Walk of check_parse_refusal (fuzz/fuzz_frame.c:34-63 at 835f336c) in fuzz_frame.ubsan,
   0x13010..0x13058. The UBSan alignment check at 0x13014 (w & 7, trap at 0x13058) is not
   taken: w mod 8 = 0. Then r (a0) and w->code (the word at a1) are both fr_code b, one of 0,
   -2, -3, -4 (DgnSpec.fr_code_cases). For each of the four values the eight tests at
   0x13020..0x13044 are closed terms, and none of them branches to the abort path at 0x1304c.
   The function returns at 0x13048 with no stack frame, so it writes no memory.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import CheckStackU check_parse_refusal_c.
Import ListNotations.
Open Scope Z_scope.

(* The low three bits of an 8-aligned address. *)
Lemma cpr_land7 : forall w, w mod 8 = 0 -> Z.land w 7 = 0.
Proof. intros w H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

(* Decide a branch whose condition is a closed term. *)
Ltac brc := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

Theorem check_parse_refusal_holds : check_parse_refusal_contract.
Proof.
  unfold check_parse_refusal_contract, CHECK_PARSE_REFUSAL, U_CPR_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m w lo b
    AL RO DW ST LO MI.
  pose proof (ro_cells_bound _ _ _ _ RO) as Wb. cbn [cells_size csize Nat.add] in Wb.
  pose proof (cpr_land7 w AL) as HA.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x13010 andi a2, a1, 7; 0x13014 bnez a2 -> trap: not taken *)
  do 2 step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false; [cbv iota | symmetry]
  end.
  2: { unfold_cond; try change (bv_wrap 64 7) with 7; rewrite ?(unsigned_lit w) by lia; rewrite HA;
       vm_compute; reflexivity. }
  destruct (fr_code_cases b) as [E|[E|[E|E]]]; rewrite E in *.
  all: do 2 step.
  all: repeat first [ brc | step ].
  all: apply evt_done; do 16 eexists; split; [reflexivity|].
  all: refine (conj _ (conj _ (conj _ _))); eassumption.
Qed.
