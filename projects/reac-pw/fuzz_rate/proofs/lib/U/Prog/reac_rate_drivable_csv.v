From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import printf_facts_c snprintf_c memcpy_c reac_rate_drivable_csv_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import dcsv_lib dcsv_defs dcsv_entry dcsv_pass dcsv_exit.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_drivable_csv of the UBSan image (0x14dcc, 114 instructions) against its contract
    (U/Prog/reac_rate_drivable_csv_c.v), from snprintf_contract and memcpy_contract: the entry
    (U/Prog/dcsv_entry.v), three passes of the loop (U/Prog/dcsv_pass.v: the compare chain, the bit test, snprintf,
    memcpy and the NUL for a set bit) and the exit (U/Prog/dcsv_exit.v: buflen = 0, or memcpy of min(len, buflen - 1)
    bytes and the NUL, then the epilogue). The five trap branches to the `unimp` at 0x14f90 are not taken. *)

Section Main.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mask : word) (S0 lo n buf : Z)
  (m0 : word -> option byte) (canary : word) (junk : list byte) (F0 : bvmap 5 word).
Hypothesis HK : lo + 6112 <= S0.
Hypothesis HI : 0x50cc8 <= lo.
Hypothesis H63 : S0 < 2^63.
Hypothesis Hn : 0 <= n <= 23.
Hypothesis HB0 : 0 < n -> 0 < buf /\ (buf + n <= lo \/ S0 <= buf).
Hypothesis HBR : 0 < n -> rw_cells rsegs m0 buf [CB (Z.to_nat n) junk].
Hypothesis TK0 : MemNorm.task_mem rsegs m0.
Hypothesis ST0 : stk rsegs m0 lo S0.
Hypothesis SNP : snprintf_contract.
Hypothesis MCP : memcpy_contract.

Local Abbreviation SV := (dsv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Local Abbreviation OK := (dok S0 lo n buf mask SV m0 canary junk F0).
Local Abbreviation ST := (dst gp tp mask S0).
Local Abbreviation POST := (dpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 m0 lo S0 buf n
                          (csv_list (bv_unsigned mask))).

(** The loop: from the head of pass i (i <= 3; at i = 3 the fall-through of `bnez s6`, 0x14efc) to the return. *)
Lemma dcsv_loop : forall (k i : nat) len r6 r9 m F fc
    (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  k = (3 - i)%nat -> (i <= 3)%nat -> OK i len r6 r9 m F fc ->
  evt rsegs POST (ST (if Nat.ltb i 3 then 0x14e5c else 0x14efc) len r6 r9 F fc m x1 x5 x6 x7 (Z_to_bv 64 96000)
                     x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
  assert (HBL : 0 < n -> buf + n <= lo \/ S0 <= buf) by (intros H; exact (proj2 (HB0 H))).
  assert (Hsv : cells_size SV = 104%nat) by apply dsv_size.
  induction k as [|k IH];
    intros i len r6 r9 m F fc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hk Hi OKi.
  - assert (E3 : i = 3%nat) by lia. subst i. cbn [Nat.ltb Nat.leb].
    eapply dcsv_exit; eassumption.
  - assert (Hi3 : (i < 3)%nat) by lia.
    replace (Nat.ltb i 3) with true by (symmetry; apply Nat.ltb_lt; exact Hi3).
    pose proof OKi as (_ & _ & E9 & DM & _). pose proof DM as (_ & _ & _ & _ & MI & _).
    eapply dcsv_chain; try eassumption.
    eapply dcsv_pass; try eassumption.
    unfold dnext.
    intros pc len' r6' r9' m' F' fc' y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HPC OK'.
    replace pc with (if Nat.ltb (S i) 3 then 0x14e5c else 0x14efc).
    2: { destruct HPC as [[H1 H2]|[H1 H2]]; subst pc;
           [rewrite (proj2 (Nat.ltb_lt _ _) H1) | rewrite H1]; reflexivity. }
    eapply IH; [lia | lia | exact OK'].
Qed.

Lemma dcsv_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
  mem_inv rsegs m0 -> frm0 fc ->
  bytes_at rsegs m0 GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m0 GUARD (le8 canary) ->
  evt rsegs POST (MS (mkR ra (Z_to_bv 64 S0) gp tp t0 t1 t2 s0 s1 mask (Z_to_bv 64 buf) (Z_to_bv 64 n) a3 a4 a5 a6
                          a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F0 (Z_to_bv 64 0x14dcc) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc MI FC GG GD.
  eapply dcsv_entry; try eassumption.
  intros len r6 r9 m F fc' x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 OK0.
  eapply (dcsv_loop 3 0); [reflexivity | lia | exact OK0].
Qed.

End Main.

Theorem reac_rate_drivable_csv_holds : snprintf_contract -> memcpy_contract -> reac_rate_drivable_csv_contract.
Proof.
  intros SNP MCP. unfold reac_rate_drivable_csv_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    canary junk.
  cbv zeta. intros Hn HB ST HK HIMG HS63 FC MI TK GG GD.
  unfold DCSV_K, DCSV_F, SNPRINTF_K, IMG_END in *.
  pose proof (bv_unsigned_in_range 64 a2) as R2. change (bv_modulus 64) with (2^64) in R2.
  apply (evt_eq _ _ _ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp)) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (bv_unsigned a1))
                             (Z_to_bv 64 (bv_unsigned a2)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 REAC_RATE_DRIVABLE_CSV) fc None m (seg_rom rsegs)));
    [rewrite !Z_to_bv_bv_unsigned; reflexivity|].
  unfold REAC_RATE_DRIVABLE_CSV.
  eapply evt_mono.
  - eapply dcsv_main with (lo := lo) (canary := canary) (junk := junk); try eassumption.
    all: first [ lia
               | intros H; destruct (HB H) as (H1 & _ & H3); split; assumption
               | intros H; destruct (HB H) as (_ & H2 & _); exact H2 ].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m'
                & E & R).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m'.
    split; [rewrite E, Z_to_bv_bv_unsigned; reflexivity | exact R].
Qed.
