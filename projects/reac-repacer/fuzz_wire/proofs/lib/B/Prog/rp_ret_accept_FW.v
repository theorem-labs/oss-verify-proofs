(* The footprint walk of reac-repacer/fuzz_wire's rp_ret_accept in image B, against the frozen
   lib/B/Prog/rp_ret_accept_F_c.v rp_ret_accept_contract_F (= wire_rp_ret_accept_holds_stmt). The script is
   libreac/fuzz_decode's released lib/B/Prog/reac_frame_is_reac_F_nosh.v reac_frame_is_reac_holds_F_nosh (recipes
   commit 48907dc7e8ca) with its first two tests turned round: reac_frame_is_reac tests f == NULL first (returning 0)
   and n < 14 second, rp_ret_accept tests n < 14 first (returning 0) and then TRAPS on f == NULL, so the walk splits on
   n < 14 only and steps over the null check with `if_false` from the premise `bv_unsigned a0 <> 0`, which holds under
   `14 <= n`. From the load of f[12] on, the two codes are one instruction for one instruction, except that
   rp_ret_accept computes its result in a0 directly (`seqz a0, a0`; `mv a0, zero`) where reac_frame_is_reac goes
   through a2, so its two return paths take one step fewer. The GOT word and the cell are image B's (624760 = 0x98878
   and 657400 = 0xa07f8); the post names every temporary register, as the frozen contract states it. The form of the
   file is reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_FW.v (recipes commit 0295462466b2): StepF's step, one rng
   fact per access, the shadow loads read from the `addressable` premise. *)
(* rp_ret_accept of fuzz_wire.asan-ubsan (objdump of record sha256 440b9550f4f5; entry 0x80ee0, 0xa4 bytes):
     0x80ee0 `addi sp, sp, -0x10`, 0x80ee4 `sd ra, 8(sp)`;
     0x80ee8 `addi a2, zero, 0xe`, 0x80eec `bltu a1, a2, 0x80f54`: n < 14 goes to 0x80f54 `mv a0, zero`;
     0x80ef0 `beqz a0, 0x80f64`, 0x80ef4 `addi a1, zero, -0xc`, 0x80ef8 `bgeu a0, a1, 0x80f64` (UBSan; `unimp` at
     0x80f64): a0 <> 0 and f + 14 <= APPMEM_END make both fall through;
     0x80efc `auipc a1, 0x18`, 0x80f00 `ld a1, -0x684(a1)` (the GOT word 0x98878), 0x80f04 `ld a2, 0(a1)` (the shadow
     base in 0xa07f8);
     0x80f08 .. 0x80f18: the shadow byte k12 of f + 12, `bnez a3, 0x80f68`; the check 0x80f68 / 0x80f6c returns because
     (f + 12) mod 8 < k12 when k12 <> 0 (`addressable`), so the report call at 0x80f74 is never reached;
     0x80f1c `lbu a1, 0(a1)` (f[12]), 0x80f20 `addi a3, zero, 0x88`, 0x80f24 `bne a1, a3, 0x80f54` (f[12] <> 0x88: 0);
     0x80f28 `addi a1, zero, -0xe`, 0x80f2c `bltu a1, a0, 0x80f64` (UBSan): falls through as above;
     0x80f30 .. 0x80f40: the shadow byte k13 of f + 13, `bnez a1, 0x80f78`; the check 0x80f78 / 0x80f7c returns likewise,
     the report call at 0x80f80 is never reached;
     0x80f44 `lbu a0, 0(a0)` (f[13]), 0x80f48 `addi a0, a0, -0x19`, 0x80f4c `seqz a0, a0`, 0x80f50 `j 0x80f58`;
     0x80f58 `ld ra, 8(sp)`, 0x80f5c `addi sp, sp, 0x10`, 0x80f60 `ret`. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof rp_ret_accept_c rp_ret_accept_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ret_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ret_accept_c.

Theorem rp_ret_accept_holds_F : rp_ret_accept_contract_F.
Proof.
  unfold rp_ret_accept_contract_F, RP_RET_ACCEPT, RP_RET_ACCEPT_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    ST HLO APS1 APS2 HB RFR HR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  carve_frame 16%nat ST.
  (* addi sp, sp, -16; sd ra, 8(sp); addi a2, zero, 14; bltu a1, a2 *)
  step. step. step. step. if_cases HL.
  - (* n < 14: mv a0, zero; ld ra; addi sp; ret *)
    zify_cond HL.
    assert (W : PRA.ret_accept_result (bv_unsigned a1) bs = 0).
    { unfold PRA.ret_accept_result. rewrite (proj2 (Z.ltb_lt _ _) HL). reflexivity. }
    do 4 step. apply evtF_done. rewrite W. do 15 eexists. split; [reflexivity|]. split; [eassumption|].
    split; [eassumption|]. release_frame FR ST (bv_unsigned sp). exact ST.
  - zify_cond HL.
    destruct (HB HL) as (LEN & NZ & BA & D0 & CELLS & DG & DS & ADR).
    destruct (HR HL) as (RGC & RCK & RBUF & RSH).
    clear HB HR.
    destruct CELLS as (CK & GCK & _).
    destruct ADR as (P0 & N0 & PE & AB).
    destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
    destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
    unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K, shadow_ok in *.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APS1, APS2.
    rewrite Z.add_0_r in APP12, MK12, SK12.
    replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in APP13, MK13, SK13 by lia.
    assert (DV : (bv_unsigned a0 + 12) / 8 <= (bv_unsigned a0 + 13) / 8) by (apply Z.div_le_mono; lia).
    match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
    pose proof BA as (BA0 & BA1 & _).
    pose proof (bytes_tp m m0 _ _ 624760 (le8 (wa 657400)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
    pose proof (bytes_tp m m0 _ _ 657400 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
    assert (RDG : ov_read_bytes rsegs m0 (wa 624760) 8 = Some (le8 (wa 657400))).
    { replace (wa 624760) with (wa (624760 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m0 624760 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    assert (RDS : ov_read_bytes rsegs m0 (wa 657400) 8 = Some (le8 (wa 2147450880))).
    { replace (wa 657400) with (wa (657400 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m0 657400 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as M12.
    pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as M13.
    pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
    pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
    change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
    (* the UBSan checks of f: `beqz a0` and `bgeu a0, a1` (a1 = -12) fall through *)
    step. if_false.
    step. step. if_false.
    (* the shadow base through its GOT word *)
    step. step. step.
    (* f + 12: its shadow byte and check *)
    step. gen_addi a0 w12 U12.
    assert (RW12 : ExecF.rng RNG (bv_unsigned w12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
    step. gen_shr w12 g12 G12.
    rewrite U12 in G12.
    step. gen_addi g12 h12 H12.
    assert (RH12 : ExecF.rng RNG (bv_unsigned h12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RSH); lia).
    pose proof (rdw0 m0 h12 _ _ M12 ltac:(lia)) as R. step. clear R.
    step.
    pose proof (Z.mod_pos_bound (bv_unsigned a0 + 12) 8 ltac:(lia)) as MB12.
    pose proof (Z.mod_pos_bound (bv_unsigned a0 + 13) 8 ltac:(lia)) as MB13.
    destruct SK12 as [C|[C Cu]].
    1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k12) 0) ltac:(lia)); cbn [negb]; step; step;
       rewrite land7, U12, (lts_low ((bv_unsigned a0 + 12) mod 8) k12 MB12), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    all: remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
    all: remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
    (* f[12]; addi a3, zero, 0x88; bne a1, a3 *)
    all: pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R; step; clear R.
    all: step; step; if_cases HC; zify_cond HC; rewrite zxb_u in HC.
    (* f[12] <> 0x88: mv a0, zero; ld ra; addi sp; ret *)
    1, 3: assert (W : PRA.ret_accept_result (bv_unsigned a1) bs = 0)
            by (unfold PRA.ret_accept_result, PRA.ret_byte; rewrite <- E12;
                rewrite (proj2 (Z.ltb_ge _ _) HL), (proj2 (Z.eqb_neq _ _) HC);
                reflexivity);
          do 4 step; apply evtF_done; rewrite W; do 15 eexists; split; [reflexivity|]; split; [eassumption|];
          split; [eassumption|]; release_frame FR ST (bv_unsigned sp); exact ST.
    (* the UBSan check `bltu a1, a0` (a1 = -14) falls through *)
    all: step; step; if_false.
    (* f + 13: its shadow byte and check *)
    all: step; gen_addi a0 w13 U13.
    all: assert (RW13 : ExecF.rng RNG (bv_unsigned w13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
    all: step; gen_shr w13 g13 G13.
    all: rewrite U13 in G13.
    all: step; gen_addi g13 h13 H13.
    all: assert (RH13 : ExecF.rng RNG (bv_unsigned h13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RSH); lia).
    all: pose proof (rdw0 m0 h13 _ _ M13 ltac:(lia)) as R; step; clear R.
    all: step.
    all: destruct SK13 as [C'|[C' Cu']].
    1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
    all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k13) 0) ltac:(lia)); cbn [negb]; step; step;
       rewrite land7, U13, (lts_low ((bv_unsigned a0 + 13) mod 8) k13 MB13), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
    (* f[13]; addi a0, a0, -25; seqz a0, a0; j; ld ra; addi sp; ret *)
    all: pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R; step; clear R.
    all: do 6 step; apply evtF_done.
    all: assert (A0 : v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b13) + -25)) 1
                   = Z_to_bv 64 (PRA.ret_accept_result (bv_unsigned a1) bs)) by
           (unfold v_sltiu, PRA.ret_accept_result, PRA.ret_byte, zxb; rewrite <- E12, <- E13, zxb_u;
            rewrite (proj2 (Z.ltb_ge _ _) HL), HC;
            pose proof (byte_range b13) as X13;
            destruct (Z.eq_dec (bv_unsigned b13) 25) as [E|E];
            [ rewrite E; vm_compute; reflexivity
            | rewrite (proj2 (Z.eqb_neq _ _) E), andb_false_r;
              rewrite unsigned_lit_wrap; change (bv_wrap 64 1) with 1;
              replace ((bv_unsigned b13 + -25) mod 2 ^ 64 <? 1) with false; [reflexivity|];
              symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia ]).
    all: rewrite A0; do 15 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
    all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.

(* The statement of the footprint walk, as the close takes it. *)
Theorem wire_rp_ret_accept_holds : wire_rp_ret_accept_holds_stmt.
Proof. exact rp_ret_accept_holds_F. Qed.
