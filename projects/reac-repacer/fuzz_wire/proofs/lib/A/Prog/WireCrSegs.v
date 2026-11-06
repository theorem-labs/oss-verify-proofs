(* WireCrSegs: the footprint (ExecF.evtF) runs of the two straight-line segments of reac-repacer/fuzz_wire's check_ret in
   image A (fuzz_wire.asan 0x80154 = wire_sigma WS_check_ret), stepped by lib/Lib/StepF.v, in the form of
   reac-repacer/fuzz_uci's lib/A/Prog/UciCvSegs.v (cv_seg1_F, cv_end_F, its register tactics) with the frame-byte
   reads of lib/A/Prog/rp_ret_accept_FW.v:
     cr_seg1_F  entry -> the call of rp_ret_accept (ra = CR_RET): the 0x10-byte frame (s0 at 0(sp), ra at 8(sp)),
                then want = n >= 14 && f[12] == 0x88 && f[13] == 0x19 into s0 (when n >= 14 through the shadow base
                GOT_CELL_K -> CELL_K and the shadow bytes of f + 12 and f + 13), a0 = f and a1 = n untouched;
     cr_seg2_F  CR_RET -> the return: the property test `bne a0, s0` not taken (a0 = s0), ra and s0 reloaded from
                the frame, sp += 0x10, `ret`.
   The code (DIS of image A, 0x80154 .. 0x801fc):
     +0x0  `addi sp, sp, -0x10`; +0x4 `sd ra, 8(sp)`; +0x8 `sd s0, 0(sp)`; +0xc `li a2, 14`; +0x10 `bltu a1, a2` to +0x64;
     +0x14 `auipc a2, 0x18`; +0x18 `ld a2, 0x680(a2)` (GOT_CELL_K 0x987e8); +0x1c `ld a3, 0(a2)` (CELL_K 0xa0778);
     +0x20 `addi a2, a0, 12`; +0x24 `srli a4, a2, 3`; +0x28 `add a4, a4, a3`; +0x2c `lb a4, 0(a4)`; +0x30 `bnez a4` to
           +0x88 (`andi a5, a2, 7`; `blt a5, a4` back to +0x34, else `jal __asan_report_load1` at +0x94);
     +0x34 `lbu a2, 0(a2)`; +0x38 `li a4, 136`; +0x3c `bne a2, a4` to +0x64;
     +0x40 `addi a2, a0, 13`; +0x44 `srli a4, a2, 3`; +0x48 `add a3, a4, a3`; +0x4c `lb a3, 0(a3)`; +0x50 `bnez a3` to
           +0x98 (`andi a4, a2, 7`; `blt a4, a3` back to +0x54, else `jal __asan_report_load1` at +0xa4);
     +0x54 `lbu a2, 0(a2)`; +0x58 `addi a2, a2, -25`; +0x5c `seqz s0, a2`; +0x60 `j` to +0x68; +0x64 `li s0, 0`;
     +0x68 `jal rp_ret_accept` (0x80fe0);
     +0x6c `bne a0, s0` to +0x80 (`jal __asan_handle_no_return`; `jal abort`); +0x70 `ld ra, 8(sp)`; +0x74
           `ld s0, 0(sp)`; +0x78 `addi sp, sp, 0x10`; +0x7c `ret`.
   The report branches are refuted by `addressable m (a0 + 12) 2`, as in the leaf's walk. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof rp_ret_accept_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ret_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ret_accept_c.

(* The entry (symbol check_ret of the unstripped twin), the return address of its one call (`jal rp_ret_accept` at
   +0x68), and its frame (`addi sp, sp, -0x10` at the entry). *)
Definition CR_ENTRY : Z := 0x80154.
Definition CR_RET : Z := 0x801c0.
Definition CR_FR : Z := 16.

Ltac wcs_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac wcs_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac wcs_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac wcs_w := wcs_shift; wcs_usub; wcs_shift; wcs_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac wcs_ms := first [ reflexivity | f_equal; wcs_regs; try wcs_w ].

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of [a, a + n). *)
Lemma cr_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* ---- cr_seg1_F: CR_ENTRY -> rp_ret_accept (ra = CR_RET), s0 = want ---- *)
Lemma cr_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + CR_FR <= bv_unsigned sp ->
    (14 <= bv_unsigned a1 ->
       (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       bv_unsigned a0 + 14 <= bv_unsigned sp - CR_FR /\
       app_mem (bv_unsigned sp - CR_FR) /\ app_mem (bv_unsigned sp - 1) /\
       asan_cells m /\ GOT_CELL_K + 8 <= bv_unsigned sp - CR_FR /\ CELL_K + 8 <= bv_unsigned sp - CR_FR /\
       addressable m (bv_unsigned a0 + 12) 2) ->
    ExecF.rng RNG (bv_unsigned sp - CR_FR) CR_FR ->
    (14 <= bv_unsigned a1 -> ExecF.rng RNG GOT_CELL_K 8) ->
    (14 <= bv_unsigned a1 -> ExecF.rng RNG CELL_K 8) ->
    (14 <= bv_unsigned a1 -> ExecF.rng RNG (bv_unsigned a0 + 12) 2) ->
    (14 <= bv_unsigned a1 ->
       ExecF.rng RNG (shadow_addr (bv_unsigned a0 + 12))
         (shadow_addr (bv_unsigned a0 + 12 + 2 - 1) - shadow_addr (bv_unsigned a0 + 12) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a2' a3' a4' a5' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 CR_RET) (Z_to_bv 64 (bv_unsigned sp - CR_FR)) gp tp t0 t1 t2
                       (Z_to_bv 64 (PRA.ret_accept_result (bv_unsigned a1) bs)) s1 a0 a1 a2' a3' a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RP_RET_ACCEPT) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CR_FR, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned sp - CR_FR) [C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CR_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    lo ST HLO HB RFR RGOT RCELL RBUF RSH.
  unfold CR_ENTRY, CR_RET, RP_RET_ACCEPT, CR_FR in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  carve_frame 16%nat ST.
  (* addi sp; sd ra; sd s0; li a2, 14; bltu a1, a2 *)
  step. step. step. step. step. if_cases HL.
  - zify_cond HL.
    assert (W : PRA.ret_accept_result (bv_unsigned a1) bs = 0).
    { unfold PRA.ret_accept_result. rewrite (proj2 (Z.ltb_lt _ _) HL). reflexivity. }
    (* li s0, 0; jal rp_ret_accept *)
    do 2 step. apply evtF_done. rewrite W. do 5 eexists. split; [wcs_ms|]. split; [eassumption|].
    split; [eassumption|]. exact FR.
  - zify_cond HL.
    specialize (RGOT HL). specialize (RCELL HL). specialize (RBUF HL). specialize (RSH HL).
    pose proof (cr_shadow_byte_rng RNG (bv_unsigned a0 + 12) 2 0 ltac:(lia) RSH) as RS12.
    pose proof (cr_shadow_byte_rng RNG (bv_unsigned a0 + 12) 2 1 ltac:(lia) RSH) as RS13.
    rewrite Z.add_0_r in RS12.
    replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in RS13 by lia.
    clear RSH.
    destruct (HB HL) as (LEN & BA & D0 & APS1 & APS2 & CELLS & DG & DS & ADR).
    destruct CELLS as (CK & GCK & _).
    destruct ADR as (P0 & N0 & PE & AB).
    destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
    destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
    unfold GOT_CELL_K, CELL_K, ASAN_K, shadow_addr, shadow_ok in *.
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
    (* li a4, 136; bne a2, a4 *)
    all: step; step; if_cases HC; zify_cond HC; rewrite zxb_u in HC.
    1, 3: assert (W : PRA.ret_accept_result (bv_unsigned a1) bs = 0)
            by (unfold PRA.ret_accept_result, PRA.ret_byte; rewrite <- E12;
                rewrite (proj2 (Z.ltb_ge _ _) HL), (proj2 (Z.eqb_neq _ _) HC);
                reflexivity);
          do 2 step; apply evtF_done; rewrite W; do 5 eexists; split; [wcs_ms|]; split; [eassumption|];
          split; [eassumption|]; exact FR.
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
    (* addi a2, a2, -25; seqz s0, a2; j; jal rp_ret_accept *)
    all: do 4 step; apply evtF_done.
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
    all: rewrite A0; do 5 eexists; split; [wcs_ms|]; split; [eassumption|]; split; [eassumption|].
    all: exact FR.
Qed.

(* ---- cr_seg2_F: CR_RET with a0 = s0 -> the return to the caller's ra ---- *)
Lemma cr_seg2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) [C8 c0; C8 cra] ->
    bv_unsigned sp + CR_FR < 2 ^ 64 ->
    ExecF.rng RNG (bv_unsigned sp) CR_FR ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + CR_FR)) gp tp t0 t1 t2 c0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CR_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    c0 cra FR HSP RFR.
  unfold CR_RET, CR_FR in *.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  step. if_false.
  do 4 step.
  apply evtF_done. f_equal.
Qed.
