(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 216 of its 246 lines of code are new or changed and 434 lines of the source are left out. *)
(* WireCrBSegs: the footprint (ExecF.evtF) runs of the straight-line segments of reac-repacer/fuzz_wire's check_ret in
   image B (fuzz_wire.asan-ubsan 0x7ff2c = wire_sigma WS_check_ret; objdump of record sha256 440b9550f4f5), stepped by
   lib/Lib/StepF.v, in the form of reac-repacer/fuzz_uci's lib/B/Prog/UciCvBSegs.v (recipes commit 0295462466b2; its
   frame-word helpers copied), the shadow checks stepped as in this unit's lib/B/Prog/rp_ret_accept_FW.v:
     cr_seg1_F  entry -> the call of rp_ret_accept (`jal` at +0x78, return address +0x7c): the 0x10-byte frame (ra, s0
                at 8(sp), 0(sp)); when n < 14 `bltu a1, a2` (a2 = 14) goes to +0x74 `mv s0, zero`; otherwise the UBSan
                checks of f + 12 / f + 13 (not taken), the shadow checks and loads of f[12] and, when f[12] = 0x88,
                f[13], so that s0 = want = ret_accept_result n bs (no report call reached);
     cr_seg2_F  +0x7c -> the return: the property test `bne a0, s0` not taken (a0 = rp_ret_accept's result = want),
                the frame read back, `ret`. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require rp_ret_accept_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ret_accept_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module PRA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ret_accept_c.

(* ---- the cut points (offsets from the entry, read from the pinned image's code) ---- *)
Definition CR_ENTRY : Z := wire_sigma WS_check_ret.
Definition CR_AT (off : Z) : Z := CR_ENTRY + off.
(* the return address of the call of rp_ret_accept (`jal` at +0x78) *)
Definition CR_RET : Z := CR_AT 0x7c.
Definition CR_LEAF : Z := wire_sigma WS_rp_ret_accept.

(* ---- helpers (UciCvBSegs.v cv_le_bytes_to_Z .. cv_rd_all, copied) ---- *)

Lemma cr_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma cr_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply cr_le_bytes_to_Z.
Qed.

Fixpoint cr_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: cr_c8s n' (skipn 8 bs)
  end.

Lemma cr_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (cr_c8s n bs) /\ cells_bytes (cr_c8s n bs) = bs /\ cells_size (cr_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [cr_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite cr_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma cr_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (cr_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (cr_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 16 bytes, read as 2 words. *)
Lemma cr_frame_words : forall m A bs, rw_cells rsegs m A [CB 16 bs] ->
  exists v0 v8 : word, rw_cells rsegs m A [C8 v0; C8 v8].
Proof.
  intros m A bs H. apply (cr_rw_c8s rsegs m A 2 bs) in H. cbn [cr_c8s] in H. do 2 eexists. exact H.
Qed.

Lemma cr_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

Ltac cr_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cr_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cr_w := cr_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac cr_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
Ltac cr_lit X := let v := eval vm_compute in X in change X with v.
Ltac cr_lits :=
  repeat match goal with
  | |- context [CR_RET] => cr_lit CR_RET
  | |- context [CR_LEAF] => cr_lit CR_LEAF
  | |- context [CR_AT ?o] => cr_lit (CR_AT o)
  | |- context [CR_ENTRY] => cr_lit CR_ENTRY
  end.

(* ---- cr_seg1_F: entry -> rp_ret_accept (ra = CR_RET), s0 = want ---- *)
Lemma cr_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 fw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    ExecF.rng RNG (bv_unsigned sp - 16) 16 ->
    (14 <= bv_unsigned a1 ->
       (14 <= length bs)%nat /\
       bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) /\ bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) /\
       CELL_K + 8 <= bv_unsigned sp - 16 /\
       off_stk sp 16 (bv_unsigned fw + 12) 2 /\
       app_mem (bv_unsigned sp - 16) /\ app_mem (bv_unsigned sp - 1) /\
       addressable m (bv_unsigned fw + 12) 2 /\
       mrd rsegs m (wa (bv_unsigned fw + 12)) = Some (nth 12 bs (Z_to_bv 8 0)) /\
       mrd rsegs m (wa (bv_unsigned fw + 13)) = Some (nth 13 bs (Z_to_bv 8 0)) /\
       ExecF.rng RNG GOT_CELL_K 8 /\ ExecF.rng RNG CELL_K 8 /\
       ExecF.rng RNG (bv_unsigned fw + 12) 2 /\
       ExecF.rng RNG (shadow_addr (bv_unsigned fw + 12))
         (shadow_addr (bv_unsigned fw + 13) - shadow_addr (bv_unsigned fw + 12) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (m1 : word -> option byte) (v0 a2' a3' a4' a5' : word),
         ms' = MS (mkR (Z_to_bv 64 CR_RET) (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2
                    (Z_to_bv 64 (PRA.ret_accept_result (bv_unsigned a1) bs)) s1 fw a1 a2' a3' a4' a5' a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CR_LEAF) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 fw a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CR_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 fw a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    ST LO RFR HB.
  cr_lits.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (bv_unsigned_in_range 64 fw) as Rf. unfold bv_modulus in Rf. change (2 ^ Z.of_N 64) with (2^64) in Rf.
  pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn. change (2 ^ Z.of_N 64) with (2^64) in Rn.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  destruct (cr_frame_words _ _ _ FR) as (v0 & v8 & FR'). clear FR. rename FR' into FR.
  (* addi sp; sd ra; sd s0; li a2, 14; bltu a1, a2 *)
  do 4 step. step. if_cases HL.
  - (* n < 14: want = 0 *)
    zify_cond HL.
    assert (W : PRA.ret_accept_result (bv_unsigned a1) bs = 0).
    { unfold PRA.ret_accept_result. rewrite (proj2 (Z.ltb_lt _ _) HL). reflexivity. }
    rewrite W.
    do 2 step.
    cr_memF ltac:(fun mm => apply evtF_done; exists mm, v0; do 4 eexists).
    replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia.
    split; [|split; [exact MU|split; [exact WM|exact FR]]].
    f_equal; cr_regs; try cr_w.
  - zify_cond HL.
    destruct (HB ltac:(lia)) as (LEN & GCK & CK & HLOW & D0 & APS1 & APS2 & ADR & F12 & F13 & RGC & RCK & RBUF & RSH).
    unfold GOT_CELL_K in RGC, GCK, HLOW. unfold CELL_K in RCK, GCK, CK, HLOW.
    destruct ADR as (P0 & N0 & PE & AB).
    destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
    destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
    unfold off_stk in D0.
    unfold shadow_addr, ASAN_K, shadow_ok in *.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, PE, APS1, APS2.
    rewrite Z.add_0_r in APP12, MK12, SK12.
    replace (bv_unsigned fw + 12 + 1) with (bv_unsigned fw + 13) in APP13, MK13, SK13 by lia.
    assert (DV : (bv_unsigned fw + 12) / 8 <= (bv_unsigned fw + 13) / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.mod_pos_bound (bv_unsigned fw + 12) 8 ltac:(lia)) as MB12.
    pose proof (Z.mod_pos_bound (bv_unsigned fw + 13) 8 ltac:(lia)) as MB13.
    remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
    remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
    (* the frame write moved the cells, the two bytes and their shadow bytes to m1 *)
    pose proof (bytes_tp m m1 _ _ 624760 (le8 (wa 657400)) MU ltac:(rewrite length_le8; lia) GCK) as GCK1.
    pose proof (bytes_tp m m1 _ _ 657400 (le8 (wa 2147450880)) MU ltac:(rewrite length_le8; lia) CK) as CK1.
    pose proof (mrd_tp m m1 _ _ (bv_unsigned fw + 12) _ MU ltac:(lia) ltac:(lia) F12) as F12'.
    pose proof (mrd_tp m m1 _ _ (bv_unsigned fw + 13) _ MU ltac:(lia) ltac:(lia) F13) as F13'.
    pose proof (mrd_tp m m1 _ _ ((bv_unsigned fw + 12) / 8 + 2147450880) _ MU
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as MK12'.
    pose proof (mrd_tp m m1 _ _ ((bv_unsigned fw + 13) / 8 + 2147450880) _ MU
      ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as MK13'.
    (* the UBSan check of f + 12: `bgeu a0, a2` (a2 = -12) falls through *)
    step. step. if_false.
    (* the shadow base through its GOT word *)
    pose proof (cr_rd_all _ _ _ GCK1) as RDG. rewrite length_le8 in RDG.
    pose proof (cr_rd_all _ _ _ CK1) as RDS. rewrite length_le8 in RDS.
    do 3 step.
    (* f + 12: its shadow byte and check *)
    step. gen_addi fw w12 U12.
    step. gen_shr w12 g12 G12. rewrite U12 in G12.
    step. gen_addi g12 h12 H12.
    pose proof (rdw0 m1 h12 _ _ MK12' ltac:(lia)) as R. step. clear R.
    step.
    destruct SK12 as [C|[C Cu]].
    1: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb].
    2: rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k12) 0) ltac:(lia)); cbn [negb]; step; step;
       rewrite land7, U12, (lts_low ((bv_unsigned fw + 12) mod 8) k12 MB12), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    (* f[12]; li a4, 0x88; bne a2, a4 *)
    all: pose proof (rdw0 m1 w12 _ _ F12' ltac:(lia)) as R; step; clear R.
    all: step; step; if_cases HC; zify_cond HC; rewrite zxb_u in HC.
    (* f[12] <> 0x88: want = 0 *)
    1, 3: assert (W : PRA.ret_accept_result (bv_unsigned a1) bs = 0)
            by (unfold PRA.ret_accept_result, PRA.ret_byte; rewrite <- E12;
                rewrite (proj2 (Z.ltb_ge _ _) HL), (proj2 (Z.eqb_neq _ _) HC); reflexivity);
          rewrite W; do 2 step;
          cr_memF ltac:(fun mm => apply evtF_done; exists mm, v0; do 4 eexists);
          (replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia);
          (split; [|split; [exact MU|split; [exact WM|exact FR]]]);
          f_equal; cr_regs; try cr_w.
    (* the UBSan check of f + 13: `bltu a2, a0` (a2 = -14) falls through *)
    all: step; step; if_false.
    (* f + 13: its shadow byte and check *)
    all: step; gen_addi fw w13 U13.
    all: step; gen_shr w13 g13 G13.
    all: rewrite U13 in G13.
    all: step; gen_addi g13 h13 H13.
    all: pose proof (rdw0 m1 h13 _ _ MK13' ltac:(lia)) as R; step; clear R.
    all: step.
    all: destruct SK13 as [C'|[C' Cu']].
    1, 3: rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C'); cbn [negb].
    all: try (rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k13) 0) ltac:(lia)); cbn [negb]; step; step;
       rewrite land7, U13, (lts_low ((bv_unsigned fw + 13) mod 8) k13 MB13), (proj2 (Z.ltb_lt _ _) C'); cbn [negb]).
    (* f[13]; addi a2, a2, -25; seqz s0, a2; j; jal rp_ret_accept *)
    all: pose proof (rdw0 m1 w13 _ _ F13' ltac:(lia)) as R; step; clear R.
    all: do 2 step.
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
    all: rewrite A0.
    all: do 2 step.
    all: cr_memF ltac:(fun mm => apply evtF_done; exists mm, v0; do 4 eexists).
    all: replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia.
    all: split; [|split; [exact MU|split; [exact WM|exact FR]]].
    all: f_equal; cr_regs; try cr_w.
Qed.

(* ---- cr_seg2_F: CR_RET -> the return ---- *)
Lemma cr_seg2_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v : Z) (c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) [C8 c0; C8 cra] ->
    bv_unsigned sp + 16 < 2 ^ 64 ->
    ExecF.rng RNG (bv_unsigned sp) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 16)) gp tp t0 t1 t2 c0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 v) s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CR_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v c0 cra FR HSP RFR.
  cr_lits.
  pose proof (rw_cells_bound _ _ _ _ FR) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  (* bne a0, s0 (not taken); ld ra; ld s0; addi sp; ret *)
  step. if_false.
  do 4 step.
  apply evtF_done. f_equal.
Qed.
