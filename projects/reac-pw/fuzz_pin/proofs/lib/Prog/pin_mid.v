(** The middle segment of reac-pw/fuzz_pin's LLVMFuzzerTestOneInput (plain), [0x12d1c, 0x12de4): pin_mid_contract
    (Prog/LLVMFuzzerTestOneInput_c.v) from the contracts of its callees. The walk is Prog/PinMid/Walk.v (head_ok:
    memcpy, the NUL, strlen; scan_ok: the scan `tok`; cat_ok: fuzz_catalogue_row and want_label; tail_ok: the out
    cells, reac_box_pin_parse and the three checks), its facts Prog/PinMid/Facts.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec memcpy_c strlen_c fuzz_catalogue_row_c
  reac_box_pin_parse_c check_known_c check_row_c check_label_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.PinMid Require Import Facts Walk.
Import ListNotations.
Open Scope Z_scope.

Theorem pin_mid_holds : memcpy_c.memcpy_contract -> strlen_c.strlen_contract ->
  fuzz_catalogue_row_c.fuzz_catalogue_row_contract -> reac_box_pin_parse_c.reac_box_pin_parse_contract ->
  check_known_c.check_known_contract -> check_row_c.check_row_contract -> check_label_c.check_label_contract ->
  pin_mid_contract.
Proof.
  intros MCPY STRL FCR PARSE CKN CKR CKL. unfold pin_mid_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m s junk slack fl src phi lo can -> HPHI0 -> -> -> HFL HNN HSRC HBLK HBROM HSLKB HSLKL HDJ ST HLO HSPA
         HWR HSROM HSEP HTB HGOT HGRD HMI.
  pose proof (rw_cells_bound rsegs m phi _ HBLK) as BB. cbn [cells_size csize] in BB.
  pose proof (bytes_at_bound rsegs m _ slack HSLKB) as BSL.
  pose proof ST as (HLO0 & _ & _).
  pose proof HWR as (_ & HSPT & _). unfold MID_OUT in HSPT.
  unfold MID_STACK in HLO.
  eapply mid_ok; try eassumption; lia.
Qed.
