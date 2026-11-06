(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 203 of its 237 lines of code are new or changed and 430 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/B/Prog/WireCcnBSegs.v, with its module paths and numbers changed; 124 of its 190 lines of code are new or changed and 171 lines of the source are left out. *)
(* WireCkSegs: the footprint (ExecF.evtF) runs of the three straight-line segments of reac-repacer/fuzz_wire's
   check_counter in image A (fuzz_wire.asan 0x80660 = wire_sigma WS_check_counter), stepped by lib/Lib/StepF.v, in the
   form of reac-repacer/fuzz_uci's lib/A/Prog/UciCvSegs.v (cv_seg1_F, cv_end_F, its register tactics) with the
   frame-byte reads of lib/A/Prog/rp_counter_FW.v:
     ck_short_F  entry with n < 18 -> the return: the frame is written and read back, nothing else;
     ck_seg1_F   entry with n >= 18 -> the call of rp_counter (ra = CK_RET): the 0x20-byte frame (s1 at 8(sp), s0 at
                 0x10(sp), ra at 0x18(sp)), s0 := f, s1 := the shadow base (GOT_CELL_K -> CELL_K), a0 := f;
     ck_seg2_F   CK_RET with a0 = the counter -> the return: the shadow bytes of f + 14 and f + 15 and the two frame
                 bytes, the property test `bne a0, a1` not taken, the frame reloaded, sp += 0x20, `ret`.
   The code (DIS of image A, 0x80660 .. 0x80708):
     +0x0  `addi sp, sp, -0x20`; +0x4 `sd ra, 24(sp)`; +0x8 `sd s0, 16(sp)`; +0xc `sd s1, 8(sp)`; +0x10 `li a2, 18`;
           +0x14 `bltu a1, a2` to +0x6c;
     +0x18 `mv s0, a0`; +0x1c `auipc a0, 0x18`; +0x20 `ld a0, 0x16c(a0)` (GOT_CELL_K 0x987e8); +0x24 `ld s1, 0(a0)`
           (CELL_K 0xa0778); +0x28 `mv a0, s0`; +0x2c `jal rp_counter` (0x812f4);
     +0x30 `addi a1, s0, 14`; +0x34 `srli a2, a1, 3`; +0x38 `add a2, a2, s1`; +0x3c `lb a2, 0(a2)`; +0x40 `bnez a2` to
           +0x80 (`andi a3, a1, 7`; `blt a3, a2` back to +0x44, else `jal __asan_report_load1` at +0x8c);
     +0x44 `addi a1, s0, 15`; +0x48 `srli a2, a1, 3`; +0x4c `add a2, a2, s1`; +0x50 `lb a3, 0(a2)`; +0x54
           `lbu a2, 14(s0)`; +0x58 `bnez a3` to +0x90 (`andi a4, a1, 7`; `blt a4, a3` back to +0x5c, else
           `jal __asan_report_load1` at +0x9c);
     +0x5c `lbu a1, 0(a1)`; +0x60 `slli a1, a1, 8`; +0x64 `or a1, a1, a2`; +0x68 `bne a0, a1` to +0xa0
           (`jal __asan_handle_no_return`; `jal abort`);
     +0x6c `ld ra, 24(sp)`; +0x70 `ld s0, 16(sp)`; +0x74 `ld s1, 8(sp)`; +0x78 `addi sp, sp, 0x20`; +0x7c `ret`.
   The report branches are refuted by `addressable m (f + 14) 2`, as in the leaf's walk. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof rp_counter_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_counter_c.
Import ListNotations.
Open Scope Z_scope.
Module PRC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_counter_c.

(* The entry (symbol check_counter of the unstripped twin), the return address of its one call (`jal rp_counter` at
   +0x2c), and its frame (`addi sp, sp, -0x20` at the entry). *)
Definition CK_ENTRY : Z := 0x80660.
Definition CK_RET : Z := 0x80690.
Definition CK_FR : Z := 32.

Ltac wks_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac wks_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac wks_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac wks_w := wks_shift; wks_usub; wks_shift; wks_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac wks_ms := first [ reflexivity | f_equal; wks_regs; try wks_w ].

(* A whole byte string read at once (fuzz_uci's lib/A/Prog/UciCvSegs.v cv_rd_all). *)
Lemma ck_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of [a, a + n). *)
Lemma ck_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

(* ---- ck_short_F: CK_ENTRY with n < 18 -> the return (no call, no frame byte read) ---- *)
Lemma ck_short_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + CK_FR <= bv_unsigned sp ->
    bv_unsigned a1 < 18 ->
    ExecF.rng RNG (bv_unsigned sp - CK_FR) CK_FR ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CK_FR, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CK_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo ST HLO HN RFR.
  unfold CK_ENTRY, CK_FR in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  carve_frame 32%nat ST.
  (* addi sp; sd ra; sd s0; sd s1; li a2, 18; bltu a1, a2 (taken) *)
  do 6 step. if_true.
  (* ld ra; ld s0; ld s1; addi sp; ret *)
  do 5 step.
  apply evtF_done. do 2 eexists. split; [wks_ms|]. split; [eassumption|]. split; [eassumption|].
  release_frame FR ST (bv_unsigned sp). exact ST.
Qed.

(* ---- ck_seg1_F: CK_ENTRY with n >= 18 -> rp_counter (ra = CK_RET) ---- *)
Lemma ck_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + CK_FR <= bv_unsigned sp ->
    18 <= bv_unsigned a1 ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    CELL_K + 8 <= bv_unsigned sp - CK_FR ->
    ExecF.rng RNG (bv_unsigned sp - CK_FR) CK_FR ->
    ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (jb : list byte) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 CK_RET) (Z_to_bv 64 (bv_unsigned sp - CK_FR)) gp tp t0 t1 t2 a0
                       (Z_to_bv 64 ASAN_K) a0 a1 (Z_to_bv 64 18) a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 RP_COUNTER) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CK_FR, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (bv_unsigned sp - CK_FR) [CB 8 jb; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CK_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo ST HLO HN GCK CK HLOW RFR RGC RCK.
  unfold CK_ENTRY, CK_RET, RP_COUNTER, CK_FR in *.
  unfold GOT_CELL_K in RGC, GCK, HLOW. unfold CELL_K in RCK, GCK, CK, HLOW. unfold ASAN_K in CK.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  carve_frame 32%nat ST.
  (* addi sp; sd ra; sd s0; sd s1; li a2, 18; bltu a1, a2 (not taken); mv s0, a0 *)
  do 6 step. if_false. step.
  (* the stores moved the two cell facts to the new memory *)
  pose proof (ck_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (ck_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  (* auipc; ld (the GOT word); ld (the shadow base); mv a0, s0; jal rp_counter *)
  do 5 step.
  apply evtF_done. do 2 eexists. split; [wks_ms|]. split; [eassumption|]. split; [eassumption|].
  exact FR.
Qed.

(* ---- ck_seg2_F: CK_RET with a0 = the counter -> the return ---- *)
Lemma ck_seg2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 f a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs jb : list byte) (c1 c0 cra : word),
    (16 <= length bs)%nat -> bytes_at rsegs m (bv_unsigned f) bs ->
    rw_cells rsegs m (bv_unsigned sp) [CB 8 jb; C8 c1; C8 c0; C8 cra] ->
    bv_unsigned sp + CK_FR < 2 ^ 64 ->
    bv_unsigned f + 16 <= bv_unsigned sp \/ bv_unsigned sp + CK_FR <= bv_unsigned f ->
    addressable m (bv_unsigned f + 14) 2 ->
    ExecF.rng RNG (bv_unsigned sp) CK_FR ->
    ExecF.rng RNG (bv_unsigned f + 14) 2 ->
    ExecF.rng RNG (shadow_addr (bv_unsigned f + 14))
      (shadow_addr (bv_unsigned f + 14 + 2 - 1) - shadow_addr (bv_unsigned f + 14) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' a2' a3' a4' : word),
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + CK_FR)) gp tp t0 t1 t2 c0 c1
                       (Z_to_bv 64 (PRC.counter_result bs)) a1' a2' a3' a4' a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 f (Z_to_bv 64 ASAN_K) (Z_to_bv 64 (PRC.counter_result bs)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CK_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 f a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    jb c1 c0 cra LEN BA FR HSP HOFF ADR RFR RBUF RSH.
  unfold CK_RET, CK_FR in *.
  pose proof (ck_shadow_byte_rng RNG (bv_unsigned f + 14) 2 0 ltac:(lia) RSH) as RS14.
  pose proof (ck_shadow_byte_rng RNG (bv_unsigned f + 14) 2 1 ltac:(lia) RSH) as RS15.
  rewrite Z.add_0_r in RS14.
  replace (bv_unsigned f + 14 + 1) with (bv_unsigned f + 15) in RS15 by lia.
  clear RSH.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 f) as Rf. unfold bv_modulus in Rf. change (2 ^ Z.of_N 64) with (2^64) in Rf.
  destruct ADR as (P0 & N0 & PE & AB).
  destruct (AB 0 ltac:(lia)) as (APP14 & k14 & MK14 & SK14).
  destruct (AB 1 ltac:(lia)) as (APP15 & k15 & MK15 & SK15).
  unfold ASAN_K, shadow_addr, shadow_ok in *.
  unfold ASAN_K in RS14, RS15, MK14, MK15.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP14, APP15.
  rewrite Z.add_0_r in APP14, MK14, SK14.
  replace (bv_unsigned f + 14 + 1) with (bv_unsigned f + 15) in APP15, MK15, SK15 by lia.
  pose proof (bytes_nth m _ bs 14 BA ltac:(lia)) as F14.
  pose proof (bytes_nth m _ bs 15 BA ltac:(lia)) as F15.
  change (Z.of_nat 14) with 14 in F14. change (Z.of_nat 15) with 15 in F15.
  remember (nth 14 bs (Z_to_bv 8 0)) as b14 eqn:E14.
  remember (nth 15 bs (Z_to_bv 8 0)) as b15 eqn:E15.
  pose proof (Z.mod_pos_bound (bv_unsigned f + 14) 8 ltac:(lia)) as MB14.
  pose proof (Z.mod_pos_bound (bv_unsigned f + 15) 8 ltac:(lia)) as MB15.
  (* addi a1, s0, 14; srli; add; lb *)
  step. gen_addi f w14 U14.
  step. gen_shr w14 g14 G14. rewrite U14 in G14.
  step. gen_addi g14 h14 H14.
  try rewrite (unsigned_lit 2147450880) in H14 by lia.
  pose proof (rng_sub' _ _ _ (bv_unsigned h14) 1 RS14 ltac:(lia)) as RH14.
  pose proof (rdw0 m h14 _ _ MK14 ltac:(lia)) as R. step. clear R.
  step.
  destruct SK14 as [C|[C Cu]].
  1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
  2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k14) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U14, (lts_low ((bv_unsigned f + 14) mod 8) k14 MB14), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
  all: step; gen_addi f w15 U15.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned w15) 1 RBUF ltac:(lia)) as RW15.
  all: step; gen_shr w15 g15 G15.
  all: rewrite U15 in G15.
  all: step; gen_addi g15 h15 H15.
  all: try rewrite (unsigned_lit 2147450880) in H15 by lia.
  all: pose proof (rng_sub' _ _ _ (bv_unsigned h15) 1 RS15 ltac:(lia)) as RH15.
  all: pose proof (rdw0 m h15 _ _ MK15 ltac:(lia)) as R; step; clear R.
  all: pose proof (rdw m f 14 _ _ F14 ltac:(lia)) as R; step; clear R.
  all: step.
  all: destruct SK15 as [C'|[C' Cu']].
  1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
  all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k15) 0) ltac:(lia)); cbn [negb]; step; step;
     rewrite land7, U15, (lts_low ((bv_unsigned f + 15) mod 8) k15 MB15), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
  all: pose proof (rdw0 m w15 _ _ F15 ltac:(lia)) as R; step; clear R.
  (* slli a1, a1, 8; or a1, a1, a2; bne a0, a1 (not taken) *)
  all: pose proof (byte_range b14) as X14; pose proof (byte_range b15) as X15.
  all: do 2 step.
  all: assert (EV : Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b15)) 8)))
                                      (bv_unsigned (zxb b14)))
                    = Z_to_bv 64 (PRC.counter_result bs))
         by (unfold zxb; rewrite !zxb_u; apply bv_eq; rewrite lor_bytes16;
             unfold PRC.counter_result, PRC.counter_byte; rewrite <- E14, <- E15;
             rewrite unsigned_lit by lia; reflexivity).
  all: rewrite EV.
  all: step; if_false.
  (* ld ra; ld s0; ld s1; addi sp; ret *)
  all: do 5 step.
  all: apply evtF_done; do 4 eexists; wks_ms.
Qed.
