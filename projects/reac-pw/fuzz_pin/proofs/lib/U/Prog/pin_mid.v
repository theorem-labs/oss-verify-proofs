(** pin_mid_contract of U/Prog/LLVMFuzzerTestOneInput_c.v (the UBSan middle segment [0x12d50, 0x12e24) of
    LLVMFuzzerTestOneInput), from the UBSan callee contracts. The walk is in U/Prog/PinMid/: Head.v (malloc's
    return, memcpy, phi[k] = 0, strlen), Want.v (the scan, fuzz_catalogue_row, want_label), Tail.v
    (reac_box_pin_parse, check_known, check_row, check_label); Facts.v holds the carried memory facts. The UBSan
    checks of the segment (0x12d70, 0x12d90, 0x12e7c, 0x12e94, 0x12ea0) are shown not taken on the way. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import memcpy_c strlen_c fuzz_catalogue_row_c
  reac_box_pin_parse_c check_known_c check_row_c check_label_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.PinMid Require Import Facts Head.
Import ListNotations.
Open Scope Z_scope.

Theorem pin_mid_holds : memcpy_c.memcpy_contract -> strlen_c.strlen_contract ->
  fuzz_catalogue_row_c.fuzz_catalogue_row_contract -> reac_box_pin_parse_c.reac_box_pin_parse_contract ->
  check_known_c.check_known_contract -> check_row_c.check_row_contract -> check_label_c.check_label_contract ->
  pin_mid_contract.
Proof.
  intros MCPY STRL FCR PARSE CK CR CL. unfold pin_mid_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m s junk slack fl src phi lo can
         Ha0 Hphi0 Hs2 Hs1 Hs3 HFL HNUL HSRC HRW HRN HSLB HSLM HDJS ST HLO HSPA HWR HSN HDJ HCAT HGOT HGU HMI.
  set (K := Z.of_nat (length s)) in *.
  pose proof (rw_cells_bound rsegs m phi _ HRW) as BRW. cbn [cells_size csize] in BRW.
  pose proof (bytes_at_bound rsegs m _ _ HSLB) as BSL.
  pose proof ST as (HLO0 & _ & _).
  pose proof HWR as (_ & HWR2 & _).
  assert (HRO : rom_out sp phi K) by (apply (rom_out_of sp phi K lo); assumption).
  assert (HMI0 : minv sp phi K lo can m m).
  { split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact HMI|]. split; [exact ST|].
    split; [exact HCAT|]. split; [exact HGOT|]. split; [exact HGU | exact HWR]. }
  unfold MID_STACK, MID_OUT in *.
  assert (HK : Z.of_nat (length s) = K) by reflexivity.
  assert (HPHI : 0 < phi) by lia.
  assert (HPB : phi + K + 1 + Z.of_nat (length slack) <= 2^64) by lia.
  assert (HSP : bv_unsigned sp + 24 <= 2^64) by lia.
  clearbody K.
  eapply evt_mono.
  { eapply (mid_entry sp gp tp s6 s7 s8 s9 s10 s11 F fc m s slack junk fl phi K lo src can); eassumption. }
  intros ms' H. exact H.
Qed.
