From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import bcmp_c check_csv_c ccsv_lem ccsv_loop ccsv_tail.
Import ListNotations.
Open Scope Z_scope.

(** check_csv of the plain image (0x14734, 84 instructions), from bcmp_contract, walked with Lib/Tac.v and
    Lib/Step.v. The prologue (0x14734 .. 0x14784) saves ra and s0-s4 at sp + 0x30 .. sp + 0x5f of the 96-byte frame
    and sets up the loop registers; the outer loop (ccsv_loop.v, with ccsv_pass.v for a set bit) leaves
    want = csv_list mask at sp + 8 and n = |csv_list mask| in a7; the tail (ccsv_tail.v) checks len = n, then
    buf[0] = 0x5a (buflen = 0) or bcmp(buf, want, c) = 0 and buf[c] = 0 with c = min(len, buflen - 1), and returns.
    The abort at 0x14880 is not reached. *)

Theorem check_csv_holds : bcmp_contract -> check_csv_contract.
Proof.
  intros BC. unfold check_csv_contract, CHECK_CSV, CHECK_CSV_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv zeta. intros HL HN HB0 HB1 HBS ST LO NI MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (proj1 ST) as Hlo.
  pose proof (Z_to_bv_lit_self sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  pose proof (munch_refl [(Sp - 96, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat ST.
  (* 0x14734 .. 0x14784: addi sp, sp, -0x60; sd ra, s0-s4; mv s1, a2; mv s0, a0; a0 = a7 = 0; a2 = sp - 1; a4 = 3;
     t1 = 0x10648; t2 = 0x66666667; a5 = 10; a6 = 18; t0 = sp + 8; t3 = 0x2c *)
  do 21 step.
  lazymatch goal with
  | H : rw_cells _ _ _ (CB 48 ?J :: ?post) |- _ =>
      apply (rw_cells_split_CB _ _ _ [] 48 J post [8%nat; 40%nat]) in H; [ | reflexivity ];
      cbn [app mk_CB_cells] in H
  end.
  eapply (ccsv_loop ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a2 a1 a3 F fc Sp lo m);
    [ lia | lia | exact FR | exact MU | exact WM | exact MI | exact ST | ].
  intros m' dj' wj' z18 z19 z20 z29 z30 z31 FR' MU' WM' MI' ST'.
  eapply (ccsv_tail ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a2 a1 a3 F fc Sp lo m);
    [ lia | lia | exact BC | exact HL | exact HN | exact HB0 | exact HB1 | exact HBS | lia
    | exact FR' | exact MU' | exact WM' | exact MI' | exact ST' ].
Qed.
