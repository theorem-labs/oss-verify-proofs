From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import printf_facts_c snprintf_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import reac_rate_drivable_csv_c dcsv_walk.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** reac_rate_drivable_csv of the plain image (0x14a78, 99 instructions) against its contract
    (Prog/reac_rate_drivable_csv_c.v), from snprintf_contract and memcpy_contract. The walk is Prog/dcsv_walk.v
    ([dc_main]: entry, the three passes of the loop, the exit), with the memory and image lemmas of Prog/dcsv_lem.v;
    here the argument registers become the integers the walk takes (S = sp, mask = a0, buf = a1, n = a2). *)
Theorem reac_rate_drivable_csv_holds : snprintf_contract -> memcpy_contract -> reac_rate_drivable_csv_contract.
Proof.
  intros SNP MCP. unfold reac_rate_drivable_csv_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo canary junk.
  cbv zeta.
  intros Hn HB ST HK HIMG HS63 FC MI TK GG GD.
  unfold DCSV_K, DCSV_F, SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. pose proof (bv_unsigned_in_range 64 sp) as RS.
  change (bv_modulus 64) with (2^64) in R0, R1, R2, RS.
  apply (evt_eq _ _ _ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned a0))
                             (Z_to_bv 64 (bv_unsigned a1)) (Z_to_bv 64 (bv_unsigned a2)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                             s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 REAC_RATE_DRIVABLE_CSV) fc None m (seg_rom rsegs)));
    [rewrite !Z_to_bv_bv_unsigned; reflexivity|].
  unfold REAC_RATE_DRIVABLE_CSV.
  eapply evt_mono.
  { eapply dc_main with (lo := lo) (canary := canary) (junk := junk); first [assumption | lia]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m' & E & R).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m'.
  split; [rewrite E, Z_to_bv_bv_unsigned; reflexivity | exact R].
Qed.
