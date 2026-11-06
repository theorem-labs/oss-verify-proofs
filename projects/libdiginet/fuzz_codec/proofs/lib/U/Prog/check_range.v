From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_chk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img codec_chk
  bcmp_c check_range_c.
Import ListNotations.
Open Scope Z_scope.

(** As in the plain image, with the alignment test of k (andi a0, a0, 7; bnez to the trap 0x154e4) after
    the prologue; the premise k mod 8 = 0 rules the trap out. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* At 0x154c4: lw a0, 0x8c(s0); bne s1, a0 to abort (rc <> want_rc: excluded by the premise); ld ra, s0, s1;
   addi sp; ret. *)
Ltac range_tail k sp FR ST :=
  step; rewrite (sx32_small (k_want_rc k)) by lia;
  step;
  let K2 := fresh "K" in
  if_cases K2; rewrite ?chk_s64_eqb in K2 by lia; zify_bool K2;
  [ exfalso; lia
  | step; step; step; step; release_frame FR ST (bv_unsigned sp); step; finish ].

Theorem check_range_holds : bcmp_contract -> check_range_contract.
Proof.
  intros HBC. unfold bcmp_contract, BCMP in HBC.
  unfold check_range_contract, check_range_pre, CHECK_RANGE, CHECK_RANGE_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo k [HC [HW [HA [HSP [HMI [ST [LO [HOUT HRC]]]]]]]].
  pose proof (cells_at_wf rsegs m _ _ HC) as HWF.
  cbn [kcall_cells cells_wf cell_wf] in HWF.
  destruct HWF as (_ & Lpad & _ & _ & _ & _ & _ & _ & Lbytes & _ & _ & Lbef & Lout & _ & Lwant & _).
  pose proof (chk_cells_at_cb rsegs m _ _ 108 32 (k_out k) HC eq_refl) as HOb.
  pose proof (chk_cells_at_cb rsegs m _ _ 76 32 (k_before k) HC eq_refl) as HBb.
  change (Z.of_nat 108) with 108 in HOb. change (Z.of_nat 76) with 76 in HBb.
  change (cells_at rsegs m (bv_unsigned a0) (kcall_cells k))
    with (ro_cells rsegs m (bv_unsigned a0) (kcall_cells k)) in HC.
  pose proof (cells_at_bound rsegs m _ _ HC) as HB.
  cbn [kcall_cells cells_size csize Nat.add] in HB.
  unfold kcall_cells in HC.
  unfold kcall_wf in HW.
  destruct HW as (Wk & _ & _ & _ & Wb & _ & _ & _ & Wrc & Wwrc & _).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & Hhi & _).
  assert (MU : munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  carve_frame 32%nat ST.
  (* addi sp; sd ra; sd s0; sd s1; mv s0, a0 *)
  step. step. step. step. step.
  (* andi a0, a0, 7; bnez a0 -> trap 0x154e4: k mod 8 = 0 makes a0 = 0 *)
  step. step.
  if_cases K0.
  { exfalso. rewrite chk_land7, HA, bv_eqb_refl in K0 by lia. discriminate K0. }
  (* lw s1, 0x48(s0) *)
  step. rewrite (sx32_small (k_rc k)) by lia.
  (* beqz s1, 0x154c4 *)
  step.
  if_cases K1; rewrite ?chk_s64_eqb in K1 by lia; zify_bool K1.
  - range_tail k sp FR ST.
  - (* rc <> 0: addi a0, s0, 0x6c; addi a1, s0, 0x4c; addi a2, zero, 0x20; jal bcmp *)
    step. step. step. step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply HBC with (ls := k_out k) (rs := k_before k) (v := 0) | post_call rsegs mm ]
    end.
    1, 2: rewrite unsigned_lit by lia; eassumption.
    1: { rewrite unsigned_lit by lia. change (Z.to_nat 32) with 32%nat.
         apply chk_memcmp_eq_u; [lia | lia | rewrite (HOUT K1); reflexivity]. }
    1: eassumption.
    (* bnez a0: bcmp returned 0 *)
    step.
    if_cases K3.
    { exfalso. rewrite ?bv_eqb_refl in K3. discriminate K3. }
    range_tail k sp FR ST.
Qed.
