(* The footprint walk of reac-repacer/fuzz_wire's rp_ret_accept in image A, against the frozen
   lib/A/Prog/rp_ret_accept_F_c.v rp_ret_accept_contract_F (so it proves wire_rp_ret_accept_holds_stmt). It is
   libreac/fuzz_decode's released footprint walk of reac_frame_is_reac (lib/A/Prog/reac_frame_is_reac_F.v and its
   _F_nosh twin, which drops the shadow_rw premise as this contract does), step for step, with two changes the code
   makes: rp_ret_accept has no `beqz a0` null test (only the `bltu` of n against 14), and it computes its result in a0
   itself (decode's goes through a2 and a final `mv a0, a2`), so each return path is one step shorter. StepF's step;
   one rng fact per access.
   rp_ret_accept of fuzz_wire.asan (entry 0x80fe0, 0x8c bytes; DIS of image A):
     +0x0  `addi sp, sp, -0x10`; +0x4 `sd ra, 8(sp)`; +0x8 `li a2, 14`; +0xc `bltu a1, a2` to +0x60;
     +0x10 `auipc a1, 0x17`; +0x14 `ld a1, 0x7f8(a1)` (the GOT word 0x987e8 = GOT_CELL_K); +0x18 `ld a2, 0(a1)` (the
           shadow base cell 0xa0778 = CELL_K, holding ASAN_K);
     +0x1c `addi a1, a0, 12`; +0x20 `srli a3, a1, 3`; +0x24 `add a3, a3, a2`; +0x28 `lb a3, 0(a3)` (the shadow byte of
           a0 + 12); +0x2c `bnez a3` to +0x70 (`andi a4, a1, 7`; `blt a4, a3` back to +0x30, else
           `jal __asan_report_load1` at +0x7c);
     +0x30 `lbu a1, 0(a1)`; +0x34 `li a3, 136`; +0x38 `bne a1, a3` to +0x60;
     +0x3c `addi a0, a0, 13`; +0x40 `srli a1, a0, 3`; +0x44 `add a1, a1, a2`; +0x48 `lb a1, 0(a1)` (the shadow byte of
           a0 + 13); +0x4c `bnez a1` to +0x80 (`andi a2, a0, 7`; `blt a2, a1` back to +0x50, else
           `jal __asan_report_load1` at +0x88);
     +0x50 `lbu a0, 0(a0)`; +0x54 `addi a0, a0, -25`; +0x58 `seqz a0, a0`; +0x5c `j` to +0x64;
     +0x60 `li a0, 0`;
     +0x64 `ld ra, 8(sp)`; +0x68 `addi sp, sp, 0x10`; +0x6c `ret`.
   When n >= 14, the premise `addressable m (a0 + 12) 2` gives each shadow byte k with k = 0 or (a mod 8 < k <= 7), so
   each check either falls through or returns from the partial-granule test, and no report call is reached. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof rp_ret_accept_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import rp_ret_accept_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ret_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ret_accept_c.

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of the buffer [a, a + n) (decode's
   is_reac_shadow_byte_rng). *)
Lemma rpa_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Theorem rp_ret_accept_holds_F : rp_ret_accept_contract_F.
Proof.
  unfold rp_ret_accept_contract_F, RP_RET_ACCEPT, RP_RET_ACCEPT_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    lo ST HLO HB RFR RGOT RCELL RBUF RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  carve_frame 16%nat ST.
  (* addi sp; sd ra; li a2, 14; bltu a1, a2 *)
  step. step. step. step. if_cases HL.
  - zify_cond HL.
    assert (W : PRA.ret_accept_result (bv_unsigned a1) bs = 0).
    { unfold PRA.ret_accept_result. rewrite (proj2 (Z.ltb_lt _ _) HL). reflexivity. }
    (* li a0, 0; ld ra; addi sp; ret *)
    do 4 step. apply evtF_done. rewrite W. do 5 eexists. split; [reflexivity|]. split; [eassumption|].
    split; [eassumption|]. release_frame FR ST (bv_unsigned sp). exact ST.
  - zify_cond HL.
    specialize (RGOT HL). specialize (RCELL HL). specialize (RBUF HL). specialize (RSH HL).
    pose proof (rpa_shadow_byte_rng RNG (bv_unsigned a0 + 12) 2 0 ltac:(lia) RSH) as RS12.
    pose proof (rpa_shadow_byte_rng RNG (bv_unsigned a0 + 12) 2 1 ltac:(lia) RSH) as RS13.
    rewrite Z.add_0_r in RS12.
    replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in RS13 by lia.
    clear RSH.
    destruct (HB HL) as (LEN & BA & D0 & APS1 & APS2 & CELLS & DG & DS & ADR).
    destruct CELLS as (CK & GCK & _).
    destruct ADR as (P0 & N0 & PE & AB).
    destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
    destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
    unfold off_stk, GOT_CELL_K, CELL_K, ASAN_K, shadow_addr, shadow_ok in *.
    unfold ASAN_K in RS12, RS13.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APS1, APS2.
    rewrite Z.add_0_r in APP12, MK12, SK12.
    replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in APP13, MK13, SK13 by lia.
    match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
    pose proof BA as (BA0 & BA1 & _).
    pose proof (bytes_tp m m0 _ _ 624616 (le8 (wa 657272)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
    pose proof (bytes_tp m m0 _ _ 657272 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
    assert (RDG : ov_read_bytes rsegs m0 (wa 624616) 8 = Some (le8 (wa 657272))).
    { replace (wa 624616) with (wa (624616 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m0 624616 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    assert (RDS : ov_read_bytes rsegs m0 (wa 657272) 8 = Some (le8 (wa 2147450880))).
    { replace (wa 657272) with (wa (657272 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m0 657272 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as M12.
    pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as M13.
    pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
    pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
      (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
    change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
    (* auipc; ld (the GOT word); ld (the shadow base) *)
    step. step. step.
    step. gen_addi a0 w12 U12.
    pose proof (rng_sub' _ _ _ (bv_unsigned w12) 1 RBUF ltac:(lia)) as RW12.
    step. gen_shr w12 g12 G12.
    rewrite U12 in G12.
    step. gen_addi g12 h12 H12.
    pose proof (rng_sub' _ _ _ (bv_unsigned h12) 1 RS12 ltac:(lia)) as RH12.
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
    all: pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R; step; clear R.
    (* li a3, 136; bne a1, a3 *)
    all: step; step; if_cases HC; zify_cond HC; rewrite zxb_u in HC.
    1, 3: assert (W : PRA.ret_accept_result (bv_unsigned a1) bs = 0)
            by (unfold PRA.ret_accept_result, PRA.ret_byte; rewrite <- E12;
                rewrite (proj2 (Z.ltb_ge _ _) HL), (proj2 (Z.eqb_neq _ _) HC);
                reflexivity);
          do 4 step; apply evtF_done; rewrite W; do 5 eexists; split; [reflexivity|]; split; [eassumption|];
          split; [eassumption|]; release_frame FR ST (bv_unsigned sp); exact ST.
    all: step; gen_addi a0 w13 U13.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned w13) 1 RBUF ltac:(lia)) as RW13.
    all: step; gen_shr w13 g13 G13.
    all: rewrite U13 in G13.
    all: step; gen_addi g13 h13 H13.
    all: pose proof (rng_sub' _ _ _ (bv_unsigned h13) 1 RS13 ltac:(lia)) as RH13.
    all: pose proof (rdw0 m0 h13 _ _ M13 ltac:(lia)) as R; step; clear R.
    all: step.
    all: destruct SK13 as [C'|[C' Cu']].
    1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
    all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k13) 0) ltac:(lia)); cbn [negb]; step; step;
       rewrite land7, U13, (lts_low ((bv_unsigned a0 + 13) mod 8) k13 MB13), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
    all: pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R; step; clear R.
    (* addi a0, a0, -25; seqz a0, a0; j; ld ra; addi sp; ret *)
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
    all: rewrite A0; do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
    all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.
