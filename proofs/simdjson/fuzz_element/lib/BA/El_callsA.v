From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA.
Import ListNotations.
Open Scope Z_scope.

Definition ATIX_FN_A : Z := 0xb3880.
Definition ATKEY_FN_A : Z := 0xb3b58.
Definition ATKCI_FN_A : Z := 0xb3f64.
Definition EL_CALL_NEED_A : Z := 128 + RT_STACK.

Definition el_callpreA (RT : rt_sig) (E : aenvA) (Σ : rts RT) (m : mem) (q out node i : Z) (jo : list byte) : Prop :=
  rw_cells asegs m node [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] /\ 0 < node /\ node + 16 <= ae_lo E /\ node mod 8 = 0
  /\ fobj RT Σ m node 16
  /\ rw_cells asegs m out [CB 24 jo] /\ q <= out /\ out + 24 <= ae_hi E /\ out mod 8 = 0
  /\ ART RT Σ m /\ mem_inv asegs m /\ stk asegs m (ae_lo E) q /\ ae_lo E + EL_CALL_NEED_A <= q /\ q mod 16 = 0.

Definition atix_entry (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 : word) (out node idx : Z)
    (a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV) t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 node) (Z_to_bv 64 idx) a3
          a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 ATIX_FN_A) fc None m (seg_rom asegs).

Definition el_atix_cpsA (RT : rt_sig) (E : aenvA) : Prop :=
  forall (Σ : rts RT) PMc (d : nat) (i j idx q out node : Z)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    fdfs_only PMc -> mat_stable PMc -> a_live RT Σ E -> AINV_A E m ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E - 1 -> 0 <= idx < 2^64 ->
    el_callpreA RT E Σ m q out node i jo -> frm0 fc ->
    cps_f (ASTA RT Σ PMc (eq (atix_entry ra q gp t0 t1 t2 s0 s1 out node idx a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)))
      (lvl_postA RT E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m 0).

Definition el_atkey_cpsA (RT : rt_sig) (E : aenvA) (pc : Z) : Prop :=
  forall (Σ : rts RT) PMc (d : nat) (key : list Z) (i j q out node P : Z)
         (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo : list byte),
    fdfs_only PMc -> mat_stable PMc -> a_live RT Σ E -> AINV_A E m -> ptr_atA E P key ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d i j -> 0 <= i -> j <= ae_n E - 1 ->
    el_callpreA RT E Σ m q out node i jo -> frm0 fc ->
    cps_f (ASTA RT Σ PMc (eq (lvl_entry pc ra q gp t0 t1 t2 s0 s1 out node P (zlength key)
                                      a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)))
      (lvl_postA RT E Σ PMc ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 out m 0).
