From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_chk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_img codec_chk
  bcmp_c check_bytes_c.
Import ListNotations.
Open Scope Z_scope.

(** As in the plain image, with the alignment test of k (andi a0, a0, 7; bnez to the trap 0x15548) after
    the prologue; the premise k mod 8 = 0 rules the trap out. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Definition kc_pre (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_kind k)); CB 4 (k_pad k); C8 (Z_to_bv 64 (k_p k)); C8 (Z_to_bv 64 (k_desk k));
   C4 (Z_to_bv 64 (k_a k)); C4 (Z_to_bv 64 (k_b k)); C4 (Z_to_bv 64 (k_c k)); C4 (Z_to_bv 64 (k_delta k));
   CB 24 (k_bytes k); C8 (Z_to_bv 64 (k_n k)); C4 (Z_to_bv 64 (k_rc k)); CB 32 (k_before k)].
Definition kc_post (k : kcall) : list cell :=
  [C4 (Z_to_bv 64 (k_want_rc k)); CB 24 (k_want k); C8 (Z_to_bv 64 (k_want_len k));
   C4 (Z_to_bv 64 (k_want_key k)); C4 (Z_to_bv 64 (k_want_display k))].
Lemma kc_split : forall k, kcall_cells k = kc_pre k ++ CB 32 (k_out k) :: kc_post k.
Proof. reflexivity. Qed.

Lemma to_ro : forall m A cs, cells_at rsegs m A cs -> ro_cells rsegs m A cs.
Proof. intros m A cs H. exact H. Qed.

(* The taken branch of a bne whose two registers are the same value. *)
Ltac neq_refute K := exfalso; rewrite bv_eqb_refl in K; discriminate K.

Theorem check_bytes_holds : bcmp_contract -> check_bytes_contract.
Proof.
  intros HBC. unfold bcmp_contract, BCMP in HBC.
  unfold check_bytes_contract, check_bytes_pre, CHECK_BYTES, CHECK_BYTES_DEPTH.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo k [HC [HW [HA [HSP [HMI [ST [LO [HLEN [HL24 [HFIRST [HKEY HDISP]]]]]]]]]]].
  pose proof (cells_at_wf rsegs m _ _ HC) as HWF.
  cbn [kcall_cells cells_wf cell_wf] in HWF.
  destruct HWF as (_ & Lpad & _ & _ & _ & _ & _ & _ & Lbytes & _ & _ & Lbef & Lout & _ & Lwant & _).
  pose proof (chk_cells_at_cb rsegs m _ _ 108 32 (k_out k) HC eq_refl) as HOb.
  pose proof (chk_cells_at_cb rsegs m _ _ 144 24 (k_want k) HC eq_refl) as HWb.
  change (Z.of_nat 108) with 108 in HOb. change (Z.of_nat 144) with 144 in HWb.
  pose proof (cells_at_bound rsegs m _ _ HC) as HB.
  cbn [kcall_cells cells_size csize Nat.add] in HB.
  rewrite kc_split in HC.
  apply (chk_cells_at_replace rsegs m _ (kc_pre k) (CB 32 (k_out k)) (chk_out_cells (k_out k)) (kc_post k)) in HC;
    [ | exact (proj1 (chk_out_cells_ok _ Lout)) | exact (proj2 (chk_out_cells_ok _ Lout)) ].
  apply to_ro in HC.
  unfold kc_pre, kc_post, chk_out_cells in HC. cbn [app] in HC.
  unfold cmd_len, cmd_key, cmd_display, b8 in *.
  unfold kcall_wf in HW.
  destruct HW as (Wk & _ & _ & _ & Wb & _ & _ & _ & Wrc & Wwrc & Wwl & Wwk & Wwd).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & Hhi & _).
  assert (MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  (* addi sp; sd ra; sd s0; mv s0, a0 *)
  step. step. step. step.
  (* andi a0, a0, 7; bnez a0 -> trap 0x15548: k mod 8 = 0 makes a0 = 0 *)
  step. step.
  if_cases K0.
  { exfalso. rewrite chk_land7, HA, bv_eqb_refl in K0 by lia. discriminate K0. }
  (* lbu a2, 0x84(s0); ld a0, 0xa8(s0); bne a0, a2: out.len = want_len *)
  step. step. unfold zxb. rewrite <- HLEN. step.
  if_cases K1; [ neq_refute K1 | ].
  (* addi a0, s0, 0x6c; addi a1, s0, 0x90; jal bcmp (a2 = out.len) *)
  step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply HBC with (ls := k_out k) (rs := k_want k) (v := 0) | post_call rsegs mm ]
  end.
  1, 2: rewrite unsigned_lit by lia; eassumption.
  1: { rewrite (unsigned_lit (k_want_len k)) by lia. apply chk_memcmp_eq_u; [lia | lia | exact HFIRST]. }
  1: eassumption.
  (* bnez a0: bcmp returned 0 *)
  step.
  if_cases K2; [ neq_refute K2 | ].
  (* lw a0, 0x88(s0); lw a1, 0xb0(s0); bne a0, a1: out.key = want_key *)
  step. step. rewrite HKEY. step.
  if_cases K3; [ neq_refute K3 | ].
  (* lbu a0, 0x85(s0); lw a1, 0xb4(s0); bne a1, a0: out.display = want_display *)
  step. step. unfold zxb. rewrite HDISP, (sx32_small (k_want_display k)) by lia. step.
  if_cases K4; [ neq_refute K4 | ].
  (* ld ra; ld s0; addi sp, sp, 0x10; ret *)
  step. step. step.
  release_frame FR ST (bv_unsigned sp).
  step. finish.
Qed.
