(** The loop passes of check_csv in the UBSan image (0x148d8 .. 0x14990), one lemma per pass: a clear bit skips to
    0x1498c (a0 + 1); a set bit writes the five digits of closed_list[i] into d (the digit loop 0x148f8 .. 0x14938,
    by `mul 0x66666667; srai 34`), a ',' at want[n] when n > 0 (0x1493c .. 0x14950) and the digits back into want
    (the reverse copy 0x14958 .. 0x14984). The rate is a literal per pass, so every value is a literal and each trap
    test (0x148f8 k = 8, 0x14940 n > 39, 0x14964 k > 8, 0x14968 n = 40) is decided false by computation. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import ccsv_lemmas.
Import ListNotations.
Open Scope Z_scope.

(** A clear bit: srlw, andi, beqz (taken), addi a0, bne. *)
Ltac skip_pass :=
  unfold pass_spec, hd_st;
  intros Q Sp lo m0 m ra gp tp s0 s1 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 F fc sv Hlo HK Hhi B HM K;
  step; step; step; bit_br B; step; step; br; eapply K; exact HM.

Lemma ccsv_skip0 : forall P n, pass_spec 0 n 1 n 0x148d8 P P false.
Proof. intros P n. skip_pass. Qed.

Lemma ccsv_skip1 : forall P n, pass_spec 1 n 2 n 0x148d8 P P false.
Proof. intros P n. skip_pass. Qed.

Lemma ccsv_skip2 : forall P n, pass_spec 2 n 3 n 0x14994 P P false.
Proof. intros P n. skip_pass. Qed.

(** A set bit: the bit test, every instruction up to the next head (or the tail after pass 2), then want's first
    n' bytes are csv_bytes P'. *)
Ltac set_pass pc' n' P' :=
  unfold pass_spec, hd_st;
  intros Q Sp lo m0 m ra gp tp s0 s1 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 F fc sv Hlo HK Hhi B HM K;
  destruct HM as (j0 & dj & wj & FR & ST & MU & WM & MI); unfold_P FR;
  step; step; step; bit_br B;
  run_to pc';
  close_pass K FR n' P'.

Lemma ccsv_set0 : pass_spec 0 0 1 5 0x148d8 [] CSV_44K1 true.
Proof. set_pass 0x148d8 5%nat CSV_44K1. Qed.

Lemma ccsv_set1a : pass_spec 1 0 2 5 0x148d8 [] CSV_48K true.
Proof. set_pass 0x148d8 5%nat CSV_48K. Qed.

Lemma ccsv_set1b : pass_spec 1 5 2 11 0x148d8 CSV_44K1 (CSV_44K1 ++ [44] ++ CSV_48K) true.
Proof. set_pass 0x148d8 11%nat (CSV_44K1 ++ [44] ++ CSV_48K). Qed.

Lemma ccsv_set2a : pass_spec 2 0 3 5 0x14994 [] CSV_96K true.
Proof. set_pass 0x14994 5%nat CSV_96K. Qed.

Lemma ccsv_set2b : pass_spec 2 5 3 11 0x14994 CSV_44K1 (CSV_44K1 ++ [44] ++ CSV_96K) true.
Proof. set_pass 0x14994 11%nat (CSV_44K1 ++ [44] ++ CSV_96K). Qed.

Lemma ccsv_set2c : pass_spec 2 5 3 11 0x14994 CSV_48K (CSV_48K ++ [44] ++ CSV_96K) true.
Proof. set_pass 0x14994 11%nat (CSV_48K ++ [44] ++ CSV_96K). Qed.

Lemma ccsv_set2d : pass_spec 2 11 3 17 0x14994 (CSV_44K1 ++ [44] ++ CSV_48K)
  (CSV_44K1 ++ [44] ++ CSV_48K ++ [44] ++ CSV_96K) true.
Proof. set_pass 0x14994 17%nat (CSV_44K1 ++ [44] ++ CSV_48K ++ [44] ++ CSV_96K). Qed.
