From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import printf_facts_c snprintf_c snprintf_stk_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import tj_lemmas.
Import ListNotations.
Open Scope Z_scope.

Ltac tj_post_conv :=
  let ms' := fresh "ms'" in let E := fresh "E" in let R := fresh "R" in
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc'
              & m' & E & R);
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F', fc', m';
  split; [rewrite E, Z_to_bv_bv_unsigned; reflexivity | exact R].

Theorem reac_disco_table_json_holds :
  snprintf_contract -> snprintf_stk_contract -> reac_box_name_contract -> reac_disco_table_json_contract.
Proof.
  intros SNP SNK BOX. unfold reac_disco_table_json_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
    T junk.
  cbv zeta.
  intros HT LT Ht0 Ht8 TOK HtS Hcap HB ST HK HIMG HS63 HS16 BNT GG GD FC MI TK.
  unfold GOT_GUARD, GUARD, BN_TS, IMG_END in *.
  change TJ_K with 6240 in HK.
  pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. pose proof (bv_unsigned_in_range 64 a3) as R3.
  pose proof (bv_unsigned_in_range 64 sp) as RS. change (bv_modulus 64) with (2^64) in R0, R1, R2, R3, RS.
  apply (evt_eq _ _ _ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned a0))
                             (Z_to_bv 64 (bv_unsigned a1)) (Z_to_bv 64 (bv_unsigned a2)) (Z_to_bv 64 (bv_unsigned a3))
                             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 REAC_DISCO_TABLE_JSON) fc None m (seg_rom rsegs)));
    [rewrite !Z_to_bv_bv_unsigned; reflexivity|].
  unfold REAC_DISCO_TABLE_JSON.
  destruct (Z_lt_le_dec (bv_unsigned a3) 3) as [C3|C3].
  - eapply evt_mono; [eapply tj_small with (lo := lo) (T := T); first [exact C3 | exact ST | exact FC | exact MI | assumption | lia]
                     | tj_post_conv].
  - destruct (HB C3) as (Hb0 & RB & Hbl & Hbt & Hbi).
    pose proof (rwc_stk _ _ _ _ RB) as SB. rewrite Z2Nat.id in SB by lia.
    pose proof SB as (_ & Hb64 & _).
    pose proof (img_free_out _ _ Hbi ltac:(lia)) as Hbo.
    eapply evt_mono; [eapply tj_main with (lo := lo) (T := T) (canary := canary); first [exact HT | exact BNT | exact GG | exact GD | exact FC | exact MI
                                             | assumption | lia]
                     | tj_post_conv].
Qed.
