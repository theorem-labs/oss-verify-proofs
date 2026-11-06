(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Import SFModel.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require Import Prelim FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require Import G_memset G_memcpy G_fwritex.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require StoreCache.
Import OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Import StoreCache. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Import NElim. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition pad_prog (B got_ssp B_memset B_fwritex B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 104%Z
  (PNode 52%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 3792 4
        (PJ_Store_SZ8_nnn 4 2 1 296 4
        (PJ_Store_SZ8_nnn 8 2 8 288 4
        (PJ_Store_SZ8_nnn 12 2 9 280 4
        (PJ_Store_SZ8_nnn 16 2 18 272 4
        (PJ_Store_SZ8_nnn 20 2 19 264 4
        (PJ_OpImm_ALU_ADD_nnn 24 8 10 0 4
        (PJ_Auipc_nt 28 10 (hi20 (got_ssp - (B + 28))) 4
        (PJ_Load_SZ8_true_nnt 32 18 10 (lo12 (got_ssp - (B + 28))) 4
        (PJ_Load_SZ8_true_nnn 36 10 18 0 4
        (PJ_Store_SZ8_nnn 40 2 10 256 4
        (PJ_Branch_BC_GE_nnn 44 13 12 124 4
        (PJ_Lui_nn 48 10 18 4 nil))))))))))))))
    (PLeaf
        (PJ_Op_ALU_AND_nnn 52 10 14 10 4
        (PJ_Branch_BC_NE_nnn 56 10 0 112 4
        (PJ_Op32_ALU_SUB_nnn 60 9 12 13 4
        (PJ_OpImm_ALU_ADD_nnn 64 19 0 256 4
        (PJ_OpImm_ALU_ADD_nnn 68 12 9 0 4
        (PJ_Branch_BC_LTU_nnn 72 9 19 8 4
        (PJ_OpImm_ALU_ADD_nnn 76 12 0 256 4
        (PJ_OpImm_ALU_ADD_nnn 80 10 2 0 4
        (PJ_Jal_nt 84 1 (jimm21 (B_memset - (B + 84))) 4
        (PJ_Branch_BC_LTU_nnn 88 9 19 52 4
        (PJ_OpImm_ALU_ADD_nnn 92 19 0 255 4
        (PJ_Jal_nn 96 0 12 4
        (PJ_OpImm32_nnn 100 9 9 3840 4 nil)))))))))))))))
  (PNode 156%Z
    (PLeaf
        (PJ_Branch_BC_GEU_nnn 104 19 9 36 4
        (PJ_Load_SZ1_false_nnn 108 10 8 0 4
        (PJ_OpImm_ALU_AND_nnn 112 10 10 32 4
        (PJ_Branch_BC_NE_nnn 116 10 0 8176 4
        (PJ_OpImm_ALU_ADD_nnn 120 10 2 0 4
        (PJ_OpImm_ALU_ADD_nnn 124 11 0 256 4
        (PJ_OpImm_ALU_ADD_nnn 128 12 8 0 4
        (PJ_Jal_nt 132 1 (jimm21 (B_fwritex - (B + 132))) 4
        (PJ_Jal_nn 136 0 2097116 4
        (PJ_Load_SZ1_false_nnn 140 10 8 0 4
        (PJ_OpImm_ALU_AND_nnn 144 10 10 32 4
        (PJ_Branch_BC_NE_nnn 148 10 0 20 4
        (PJ_OpImm_ALU_ADD_nnn 152 10 2 0 4 nil))))))))))))))
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 156 11 9 0 4
        (PJ_OpImm_ALU_ADD_nnn 160 12 8 0 4
        (PJ_Jal_nt 164 1 (jimm21 (B_fwritex - (B + 164))) 4
        (PJ_Load_SZ8_true_nnn 168 10 18 0 4
        (PJ_Load_SZ8_true_nnn 172 11 2 256 4
        (PJ_Branch_BC_NE_nnn 176 10 11 32 4
        (PJ_Load_SZ8_true_nnn 180 1 2 296 4
        (PJ_Load_SZ8_true_nnn 184 8 2 288 4
        (PJ_Load_SZ8_true_nnn 188 9 2 280 4
        (PJ_Load_SZ8_true_nnn 192 18 2 272 4
        (PJ_Load_SZ8_true_nnn 196 19 2 264 4
        (PJ_OpImm_ALU_ADD_nnn 200 2 2 304 4
        (PJ_Jalr_nnn 204 0 1 0 4
        (PJ_Jal_nt 208 1 (jimm21 (B_stack_chk_fail - (B + 208))) 4 nil)))))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m. (* [comment removed for export] *) Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mem_after_store ::= mem_after_store_cached. Local Ltac addr_eq_tac ::= addr_eq_tac_cached. Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM. Local Ltac disjoint_goal ::= cbn [disjoint_from fst snd]; simpl_sizes_goal; disjoint_split.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_pad (IMG : RImg) := pad_prog (sym 0x19668) (sym 0x22e18) (sym 0x21738) (sym 0x17d50) (sym 0x15f04).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_pad : CodeAtT img_segs (sym 0x19668) (PROGAT_CODE_pad IMG)}.
  Context {RB_pad : RelCode (sym 0x19668) 212}.
  Context {RN_B_memset_19668 : RelNear (sym 0x19668) (sym 0x21738)}.
  Context {RN_B_fwritex_19668 : RelNear (sym 0x19668) (sym 0x17d50)}.
  Context {RN_B_stack_chk_fail_19668 : RelNear (sym 0x19668) (sym 0x15f04)}.
  Context {RS_got_ssp : RelSym (sym 0x22e18)}.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {SPEC_memset : memset_contract}.
  Context {SPEC_fwritex_call : fwritex_call_c}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Collection ImgHyps := IMG CODE_pad RB_pad RN_B_memset_19668 RN_B_fwritex_19668 RN_B_stack_chk_fail_19668 RS_got_ssp RS_34288 rp_34288 SPEC_memset SPEC_fwritex_call RL0_0 rl0_0.



Definition pad_entry := (sym 0x19668)%Z.

(* [comment removed for export] *)
Definition got_ssp := (sym 0x22e18)%Z.
Definition ssp_guard := (sym 0x34288)%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells img_segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells img_segs m ssp_guard [C8 canary].

(* [comment removed for export] *)
Definition pad_n (w l fl : Z) : Z :=
  if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0)%Z || (w <=? l)%Z then 0 else w - l.

Lemma pad_model : forall o c w l fl, (w - l < 256)%Z ->
  pad o c w l fl = Some (o ++ zrepeat c (pad_n w l fl)).
Proof.
  intros o c w l fl H. unfold pad, pad_n.
  destruct (negb _ || _); [cbn; now rewrite app_nil_r|].
  change PAD_FUEL with (S 63). cbn [pad_loop].
  destruct (Z.leb_spec0 256 (w - l)); [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D C N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(D, D + N)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ rw_cells img_segs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Lemma memset_callZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte),
  rw_cells img_segs m D [CB (Z.to_nat N) junk] ->
  mem_inv img_segs m ->
  (0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 2^64)%Z -> (0 <= N < 2^64)%Z ->
  evt img_segs (memset_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21738)) fc None m (seg_rom img_segs)).
Proof.
  intros until junk. intros DST MI Hq HD HC HN.
  assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
  assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (SPEC_memset ra (Z_to_bv 64 q)); rewrite ?Ed, ?En; eauto. }
  intros ms' P. unfold memset_post in P. rewrite !Ed, !Ec, !En in P. exact P.
Qed.

Lemma rw_cells_bytes_at' : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.

Definition pad_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned sp - 368, bv_unsigned sp);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (bv_unsigned sp - 368) (bv_unsigned sp)
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.

(* [comment removed for export] *)
Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

Lemma pad_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
  wfile m (bv_unsigned a0) fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk img_segs m (bv_unsigned sp - 368) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 368)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned sp <= B)%Z ->
  evt img_segs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x19668)) fc None m (seg_rom img_segs)).
Proof.
  intros until canary. intros WF (GOT & SSP) ST MI HC HW HL HFL HWL ROOM GLO AF AB.
  pose proof WF as WF0. (nelim WF 7%nat; intros FC BUF FLG LBF Bpos Bhi SEPfb).
  pose_word_ranges.
  set (Fp := bv_unsigned a0) in *. replace a0 with (Z_to_bv 64 Fp) by (unfold Fp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof (rw_cells_bound _ _ _ _ FC) as BF. cbn [cells_size csize Nat.add length] in BF.
  pose proof (rw_cells_bound _ _ _ _ BUF) as BB. cbn [cells_size csize Nat.add] in BB. rewrite Nat.add_0_r, Nat2Z.inj_add in BB.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp);
                          (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL);
                          (Fp + 40, Fp + 48)]%Z m) as MU.
  pose proof (wmono_refl img_segs m) as WM.
  unfold FILE_cells in FC.
  carve_frame 304%nat ST.
  do 6 zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  assert (EXIT : forall m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 (n : Z) pad256,
    n = pad_n W L FL ->
    mem_inv img_segs m1 ->
    rw_cells img_segs m1 (bv_unsigned sp + -304) [CB 256 pad256; C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk img_segs m1 (bv_unsigned sp - 368) (bv_unsigned sp + -304) ->
    munch [(bv_unsigned sp - 368, bv_unsigned sp); (B + Z.of_nat (length content), B + Z.of_nat (length content) + pad_n W L FL); (Fp + 40, Fp + 48)]%Z m m1 ->
    wmono img_segs m m1 ->
    wfile m1 Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk) ->
    rw_cells img_segs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells img_segs m1 ssp_guard [C8 canary] ->
    evt img_segs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -304)) gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (sym 0x34288)) x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x19668 + 168)) fc None m1 (seg_rom img_segs))).
  { intros until pad256. intros Hn MI1 FR1 ST1 MU1 WM1 WF1 GOT1 SSP1. unfold got_ssp, ssp_guard in GOT1, SSP1.
    zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    { exfalso. clear -Kc. apply Kc. reflexivity. }
    do 6 zstep. zstep. release_frame FR1 ST1 (bv_unsigned sp).
    apply evt_done. unfold pad_post.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [ ms_eq | ].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
    split; [rewrite <- Hn; exact WF1 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT1 | exact SSP1]]. }
  (* [comment removed for export] *)
  Ltac mk_wfile FC BUF FLG LBF := split; [exact FC|]; split; [exact BUF|]; split; [exact FLG|]; split; [exact LBF|]; split; [lia|]; split; lia.
  assert (PN0 : (W <= L \/ Z.land FL 73728 <> 0)%Z -> pad_n W L FL = 0%Z).
  { intros HH. unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
    destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
  zstep. if_cases Kw; zify_cond Kw; rewrite !signed_of_Z in Kw by lia.
  - (* [comment removed for export] *)
    eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
    rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
  - zstep. zstep. zstep. if_cases Kf; zify_cond Kf.
    + (* [comment removed for export] *)
      eapply EXIT; [ reflexivity | exact MI | exact FR | exact ST | exact MU | exact WM | | exact GOT | exact SSP ].
      rewrite PN0 by lia. rewrite !Z2Nat.inj_0. cbn [repeat]. rewrite skipn_O, app_nil_r. mk_wfile FC BUF FLG LBF.
    + assert (PN : pad_n W L FL = (W - L)%Z).
      { unfold pad_n, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z.
        destruct (Z.eqb_spec (Z.land FL 73728) 0); destruct (Z.leb_spec0 W L); cbn; lia. }
      rewrite PN in *. set (N := (W - L)%Z) in *.
      zstep. rewrite Z_to_bv_swrap32, (sext32_small (W - L)) by lia. fold N.
      zstep. zstep. zstep. if_cases Kn; zify_cond Kn.
      2:{ exfalso. revert Kn. rewrite ?unsigned_lit by lia. lia. }
      (* [comment removed for export] *)
      apply (rw_cells_split_CB img_segs _ _ [] 256 _ [C8 canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] [Z.to_nat N; 256 - Z.to_nat N]%nat) in FR; [ | cbn; lia ].
      cbn [mk_CB_cells app] in FR.
      apply (proj1 (rw_cells_app img_segs _ _ [_] _)) in FR. destruct FR as [FRa FRb].
      cbn [cells_size csize] in FRb. rewrite Nat.add_0_r, Z2Nat.id in FRb by lia.
      zstep. zstep. call memset_callZ.
      1:{ exact FRa. } 1:{ hyp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
      rewrite (Z.mod_small C 256) in * by lia.
      match goal with MSC : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename MSC into FRa end.
      zstep. if_cases Kn2; zify_cond Kn2.
      2:{ exfalso. revert Kn2. rewrite ?unsigned_lit by lia. lia. }
      zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
      { exfalso. exact (Ke FLG). }
      zstep. zstep. zstep. zstep.
      pose proof (rw_cells_bytes_at' _ _ _ _ FRa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
      (* [comment removed for export] *)
      set (bsP := repeat (Z_to_bv 8 C) (Z.to_nat N)) in *.
      assert (LbsP : length bsP = Z.to_nat N) by (subst bsP; apply repeat_length).
      set (nc := length content) in *. set (nj := length junk) in *.
      (* [comment removed for export] *)
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
        eapply evt_cut;
        [ eapply SPEC_fwritex_call;
          [ mk_wfile FC BUF FLG LBF
          | exact SRC
          | rewrite LbsP, Z2Nat.id by lia; reflexivity
          | rewrite LbsP; lia
          | replace (bv_unsigned sp + -304 - 64)%Z with (bv_unsigned sp - 368)%Z by lia; exact ST
          | hyp
          | lia | lia | lia | lia | lia | lia | lia | lia | lia ]
        | post_call segs m ]
      end.
      match goal with X : stk _ _ (bv_unsigned sp + -304 - 64)%Z _ |- _ =>
        replace (bv_unsigned sp + -304 - 64)%Z with (bv_unsigned sp - 368)%Z in X by lia end.
      match goal with X : wfile _ _ _ _ _ _ _ _ (skipn (length _) _) |- _ => rewrite LbsP in X end.
      match goal with X : rw_cells _ _ (bv_unsigned sp + -304)%Z [CB (Z.to_nat N) _] |- _ => rename X into FRa' end.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of FRb with rw_cells _ _ _ (?c2 :: ?rest) =>
        assert (FR : rw_cells img_segs mm (bv_unsigned sp + -304) ([] ++ [CB (Z.to_nat N) bsP; c2] ++ rest));
        [ cbn [app]; apply (proj2 (rw_cells_app img_segs _ _ [_] _)); split; [ exact FRa' |];
          cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact FRb
        | apply rw_cells_merge in FR; cbn [cells_size cells_bytes csize cbytes app Nat.add] in FR;
          rewrite app_nil_r in FR; replace (Z.to_nat N + (256 - Z.to_nat N + 0))%nat with 256%nat in FR by lia ]
      end end.
      unfold bsP in *. eapply EXIT; [ reflexivity | hyp | exact FR | hyp | hyp | hyp | hyp | unfold got_ssp, ssp_guard; hyp | unfold ssp_guard; hyp ].
Qed.

(* [comment removed for export] *)
Definition pad_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
  wfile m (bv_unsigned a0) fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk img_segs m (bv_unsigned sp - 368) (bv_unsigned sp) ->
  mem_inv img_segs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 368)%Z ->
  (bv_unsigned sp <= bv_unsigned a0)%Z -> (bv_unsigned sp <= B)%Z ->
  evt img_segs (pad_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (bv_unsigned a0) fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x19668)) fc None m (seg_rom img_segs)).
Lemma pad_contract_ok : pad_contract.
Proof. exact pad_spec. Qed.


(* [comment removed for export] *)
Definition pad_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word)
    (C n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - 368, q);
              (B + Z.of_nat (length content), B + Z.of_nat (length content) + n);
              (Fp + 40, Fp + 48)]%Z m m'
    /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - 368) q
    /\ wfile m' Fp fl0 j1 j2 lbfw B (content ++ repeat (Z_to_bv 8 C) (Z.to_nat n)) (skipn (Z.to_nat n) junk)
    /\ ssp_cells m' canary.

Lemma pad_call : forall ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q Fp C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
  wfile m Fp fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk img_segs m (q - 368) q ->
  mem_inv img_segs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= q - 368)%Z -> (q < 2^64)%Z ->
  (q <= Fp < 2^64)%Z -> (q <= B)%Z ->
  evt img_segs (pad_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x19668)) fc None m (seg_rom img_segs)).
Proof.
  intros until canary. intros WF SSP ST MI HC HW HL HFL HWL ROOM GLO Hq HF HB.
  unfold ssp_guard in GLO.
  assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 Fp) = Fp) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (pad_spec ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp)); rewrite ?Eq, ?Ef; eauto; unfold ssp_guard; lia. }
  intros ms' P. unfold pad_post in P. rewrite !Eq, !Ef in P. exact P.
Qed.

(* [comment removed for export] *)
Definition pad_call_c : Prop := forall ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q Fp C W L FL : Z)
    (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (B : Z) (content junk : list byte) (canary : word),
  wfile m Fp fl0 j1 j2 lbfw B content junk ->
  ssp_cells m canary ->
  stk img_segs m (q - 368) q ->
  mem_inv img_segs m ->
  (0 <= C < 256)%Z -> (-2^31 <= W < 2^31)%Z -> (0 <= L < 2^31)%Z -> (0 <= FL < 2^32)%Z ->
  (W - L < 256)%Z ->
  (pad_n W L FL <= Z.of_nat (length junk))%Z ->
  (ssp_guard + 8 <= q - 368)%Z -> (q < 2^64)%Z ->
  (q <= Fp < 2^64)%Z -> (q <= B)%Z ->
  evt img_segs (pad_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               Fp fl0 j1 j2 lbfw B content junk canary C (pad_n W L FL) m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 C) (Z_to_bv 64 W) (Z_to_bv 64 L) (Z_to_bv 64 FL) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x19668)) fc None m (seg_rom img_segs)).
Lemma pad_call_c_ok : pad_call_c.
Proof. exact pad_call. Qed.


End Img.
(* [comment removed for export] *)
Ltac hyp := lazymatch goal with |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end end.

(* [comment removed for export] *)
Existing Class pad_contract.
Existing Class pad_call_c.
