(* The footprint walk of reac-repacer/fuzz_wire's rp_counter in image B, against the frozen lib/B/Prog/rp_counter_F_c.v
   rp_counter_contract_F (= wire_rp_counter_holds_stmt). The script is libreac/fuzz_decode's released
   lib/B/Prog/reac_frame_counter_F_nosh.v reac_frame_counter_holds_F_nosh (recipes commit 48907dc7e8ca) step for step:
   rp_counter's code is reac_frame_counter's without its two last arithmetic instructions (`slli a0, a0, 0x30` /
   `srli a0, a0, 0x30`, its uint16_t return), so the walk takes two steps fewer before the return and reads the result
   of the `or` directly (lor_bytes16_z below, the Z form of AsanKAProof.v lor_bytes16); the GOT word and the cell are
   image B's (624760 = 0x98878 and 657400 = 0xa07f8), and the post names every temporary register, as the frozen
   contract states it. The form of the file is reac-repacer/fuzz_uci's lib/B/Prog/rp_hot_clamp_FW.v (recipes commit
   0295462466b2): StepF's step, one rng fact per access, the shadow loads read from the `addressable` premise. *)
(* rp_counter of fuzz_wire.asan-ubsan (objdump of record sha256 440b9550f4f5; entry 0x81314, 0x8c bytes):
     0x81314 `addi sp, sp, -0x10`, 0x81318 `sd ra, 8(sp)`;
     0x8131c `beqz a0, 0x8137c`, 0x81320 `addi a1, zero, -0xf`, 0x81324 `bltu a1, a0, 0x8137c`,
     0x81328 `bgeu a0, a1, 0x8137c` (UBSan; `unimp` at 0x8137c): a0 <> 0 and f + 16 <= APPMEM_END make all three fall
     through;
     0x8132c `auipc a1, 0x17`, 0x81330 `ld a1, 0x54c(a1)` (the GOT word 0x98878), 0x81334 `ld a2, 0(a1)` (the shadow
     base in 0xa07f8);
     0x81338 .. 0x81348: the shadow byte k14 of f + 14, `bnez a3, 0x81380`; the check 0x81380 `andi a4, a1, 7`,
     0x81384 `blt a4, a3, 0x8134c` returns because (f + 14) mod 8 < k14 when k14 <> 0 (`addressable`), so the report
     call at 0x8138c is never reached;
     0x8134c .. 0x81360: the shadow byte k15 of f + 15, 0x8135c `lbu a0, 14(a0)`, `bnez a2, 0x81390`; the check
     0x81390 / 0x81394 returns likewise, the report call at 0x8139c is never reached;
     0x81364 `lbu a1, 0(a1)`, 0x81368 `slli a1, a1, 8`, 0x8136c `or a0, a1, a0`;
     0x81370 `ld ra, 8(sp)`, 0x81374 `addi sp, sp, 0x10`, 0x81378 `ret`. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof rp_counter_c rp_counter_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_counter_c.

(* the value `or a0, a1, a0` leaves after `slli a1, a1, 8` of two zero-extended bytes *)
Lemma lor_bytes16_z : forall x y : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned y) 8))) (bv_unsigned x) = bv_unsigned x + 256 * bv_unsigned y.
Proof.
  intros x y. pose proof (byte_range x). pose proof (byte_range y).
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned y) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. reflexivity.
Qed.

Theorem rp_counter_holds_F : rp_counter_contract_F.
Proof.
  unfold rp_counter_contract_F, RP_COUNTER, RP_COUNTER_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    LEN NZ BA ST HLO D0 APS1 APS2 CELLS DG DS ADR RFR RGC RCK RBUF RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  assert (DV : (bv_unsigned a0 + 14) / 8 <= (bv_unsigned a0 + 15) / 8) by (apply Z.div_le_mono; lia).
  destruct CELLS as (CK & GCK & _).
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP14 & k14 & MK14 & SK14).
  destruct (AB 1 ltac:(lia)) as (APP15 & k15 & MK15 & SK15).
  unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K, shadow_ok in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP14, APP15, APS1, APS2.
  rewrite Z.add_0_r in APP14, MK14, SK14.
  replace (bv_unsigned a0 + 14 + 1) with (bv_unsigned a0 + 15) in APP15, MK15, SK15 by lia.
  pose proof BA as (BA0 & BA1 & _).
  pose proof (conj BA (conj CK GCK)) as PK. clear BA CK GCK.
  carve_frame 16%nat ST.
  step. step.
  destruct PK as (BA & CK & GCK).
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  pose proof (bytes_tp m m0 _ _ 624760 (le8 (wa 657400)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
  pose proof (bytes_tp m m0 _ _ 657400 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 624760) 8 = Some (le8 (wa 657400))).
  { replace (wa 624760) with (wa (624760 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 624760 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 657400) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 657400) with (wa (657400 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 657400 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 14) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK14) as M14.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 15) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK15) as M15.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 14) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 14 BA ltac:(lia))) as F14.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 15) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 15 BA ltac:(lia))) as F15.
  change (Z.of_nat 14) with 14 in F14. change (Z.of_nat 15) with 15 in F15.
  remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
  remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 14) 8 ltac:(lia)) as MB14.
  pose proof (Z.mod_pos_bound (bv_unsigned a0 + 15) 8 ltac:(lia)) as MB15.
  (* the UBSan checks of f: `beqz a0`, `bltu a1, a0`, `bgeu a0, a1` (a1 = -15) fall through *)
  step. if_false. step. step. if_false. step. if_false.
  (* the shadow base through its GOT word *)
  step. step. step.
  (* f + 14: its shadow byte and check *)
  step. gen_addi a0 w14 U14.
  step. gen_shr w14 g14 G14. rewrite U14 in G14.
  step. gen_addi g14 h14 H14.
  pose proof (rdw0 m0 h14 _ _ M14 ltac:(lia)) as R. step. clear R.
  step.
  destruct SK14 as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k14) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U14, (lts_low ((bv_unsigned a0 + 14) mod 8) k14 MB14), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  (* f + 15: its shadow byte and check, and the load of f[14] between them *)
  all: step; gen_addi a0 w15 U15.
  all: step; gen_shr w15 g15 G15.
  all: rewrite U15 in G15.
  all: step; gen_addi g15 h15 H15.
  all: pose proof (rdw0 m0 h15 _ _ M15 ltac:(lia)) as R; step; clear R.
  all: pose proof (rdw m0 a0 14 _ _ F14 ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct SK15 as [C'|[C' Cu']].
  1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
  all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k15) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U15, (lts_low ((bv_unsigned a0 + 15) mod 8) k15 MB15), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
  (* f[15]; `slli`, `or`; `ld ra`, `addi sp`, `ret` *)
  all: pose proof (rdw0 m0 w15 _ _ F15 ltac:(lia)) as R; step; clear R.
  all: do 5 step; apply evtF_done.
  all: unfold zxb; rewrite !zxb_u, lor_bytes16_z.
  all: replace (bv_unsigned b14 + 256 * bv_unsigned b15) with (PRC.counter_result bs)
         by (unfold PRC.counter_result, PRC.counter_byte; rewrite <- E14, <- E15; reflexivity).
  all: do 15 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|].
  all: release_frame FR ST (bv_unsigned sp); exact ST.
Qed.

(* The statement of the footprint walk, as the close takes it. *)
Theorem wire_rp_counter_holds : wire_rp_counter_holds_stmt.
Proof. exact rp_counter_holds_F. Qed.
