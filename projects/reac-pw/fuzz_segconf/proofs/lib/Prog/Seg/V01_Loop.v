(* Segment V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): the loop of the inline
   m_declared (fuzz_segconf.c:356, head 0x13d64, `continue` join 0x13d74, latch 0x13d80).
   - v01_join: JOIN after turn i (0x13d74 `addi s2,s2,1`; 0x13d78 `addi s9,s9,-0x100`; 0x13d7c `addi s1,s1,0x100`;
     0x13d80 `blt s2,s4`) goes to LOOP at turn i + 1 when i + 1 < m->n, else (0x13d84 `j 0x13f04`) to TAIL, where
     V01_RES = (added, T) since no segment is left (m_decl_go [] T cap added = (added, T)).
   - v01_loop: with SPLIT (V01_Split.v) and ADD (V01_Add.v), every LOOP state reaches TAIL: induction on the turns
     left (m->n - i).
   Part of the proof of LLVMFuzzerTestOneInput: this file is part of segment V01 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import V01_Inv.
Import ListNotations.
Open Scope Z_scope.

Lemma v01l_weq : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

Ltac v01l_weq :=
  first [ reflexivity
        | apply v01l_weq; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

(* Two states with equal registers, field for field. *)
Lemma v01l_mkR_eq : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 -> x8 = y8 -> x9 = y9 -> x10 = y10 -> x11 = y11 -> x12 = y12 -> x13 = y13 -> x14 = y14 -> x15 = y15 -> x16 = y16 -> x17 = y17 -> x18 = y18 -> x19 = y19 -> x20 = y20 -> x21 = y21 -> x22 = y22 -> x23 = y23 -> x24 = y24 -> x25 = y25 -> x26 = y26 -> x27 = y27 -> x28 = y28 -> x29 = y29 -> x30 = y30 -> x31 = y31 ->
  mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 = mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31.
Proof. intros; subst; reflexivity. Qed.

Ltac v01l_st_eq := unfold v01_loop_st, v01_tail_st, vst; f_equal; try (apply v01l_mkR_eq; v01l_weq); try v01l_weq.

(* blt on two small non-negative values. *)
Lemma v01l_lts : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  destruct (Z.ltb_spec a (2 ^ 63)); [|lia]. destruct (Z.ltb_spec b (2 ^ 63)); [|lia]. reflexivity.
Qed.

(* At most 32 segments (mconf_enc). *)
Lemma v01l_nsegs : forall inp c mm m0, v01_base inp c mm m0 -> (length (v_segs inp) <= 32)%nat.
Proof. intros inp c mm m0 (_ & (bs & _ & (_ & H & _)) & _). exact H. Qed.

Lemma v01l_skipn_nil : forall {A} (l : list A) k, (length l <= k)%nat -> skipn k l = [].
Proof. intros A l k H. apply skipn_all2. exact H. Qed.

Lemma v01l_sub_succ : forall a i n, (a - i <= Nat.succ n)%nat -> (a - Nat.succ i <= n)%nat.
Proof. intros a i n H. rewrite Nat.sub_succ_r. apply Nat.le_pred_le_succ. exact H. Qed.

Lemma v01_join : forall inp S c mm tab mt m0 gp tp F fc Q i,
  v01_geo inp S c mm tab mt -> v01_base inp c mm m0 ->
  K_tail inp S c mm tab mt m0 gp tp F fc Q ->
  ((Nat.succ i < length (v_segs inp))%nat -> K_loop_at inp S c mm tab mt m0 gp tp F fc Q (Nat.succ i)) ->
  K_join_at inp S c mm tab mt m0 gp tp F fc Q i.
Proof.
  intros inp S c mm tab mt m0 gp tp F fc Q i GEO BASE KT KL.
  intros T added ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 m (Hi & (Hadd & Hmod) & MEM & MT & FRM & VB).
  pose proof (v01l_nsegs inp c mm m0 BASE) as N32.
  assert (HiZ : Z.of_nat i < Z.of_nat (length (v_segs inp))) by (apply Nat2Z.inj_lt; exact Hi).
  assert (N32Z : Z.of_nat (length (v_segs inp)) <= 32) by (apply (Nat2Z.inj_le _ 32); exact N32).
  pose proof GEO as (_ & _ & _ & _ & _ & _ & _ & _ & Hm4096 & HmS & _).
  unfold SEG_M_SIZE in HmS.
  unfold v01_loop_st, vst, v_nsegs.
  (* 0x13d74 addi s2,s2,1 ; 0x13d78 addi s9,s9,-0x100 ; 0x13d7c addi s1,s1,0x100 *)
  do 3 zstep.
  (* 0x13d80 blt s2,s4 *)
  zstep.
  rewrite (v01l_lts (Z.of_nat i + 1) (Z.of_nat (length (v_segs inp)))) by lia.
  destruct (Z_lt_le_dec (Z.of_nat i + 1) (Z.of_nat (length (v_segs inp)))) as [HltZ|HgeZ].
  - rewrite (proj2 (Z.ltb_lt (Z.of_nat i + 1) (Z.of_nat (length (v_segs inp))))) by exact HltZ. cbv iota.
    assert (Hlt : (Nat.succ i < length (v_segs inp))%nat)
      by (apply Nat2Z.inj_lt; rewrite Nat2Z.inj_succ; exact HltZ).
    replace (Z_to_bv 64 (mm + 256 * Z.of_nat i + 256)) with (Z_to_bv 64 (mm + 256 * Z.of_nat (Nat.succ i)))
      by (f_equal; rewrite Nat2Z.inj_succ; unfold Z.succ; lia).
    replace (Z_to_bv 64 (- (mm + 256 * Z.of_nat i) + -256)) with (Z_to_bv 64 (- (mm + 256 * Z.of_nat (Nat.succ i))))
      by (f_equal; rewrite Nat2Z.inj_succ; unfold Z.succ; lia).
    replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (Nat.succ i)))
      by (f_equal; rewrite Nat2Z.inj_succ; unfold Z.succ; lia).
    eapply (KL Hlt T added).
    split; [exact Hlt|]. split; [split; [exact Hadd | exact Hmod]|].
    split; [exact MEM|]. split; [exact MT|]. split; [exact FRM | exact VB].
  - rewrite (proj2 (Z.ltb_ge (Z.of_nat i + 1) (Z.of_nat (length (v_segs inp))))) by exact HgeZ. cbv iota.
    assert (Hsk : skipn (Nat.succ i) (v_segs inp) = []).
    { apply v01l_skipn_nil. apply Nat2Z.inj_le. rewrite Nat2Z.inj_succ. unfold Z.succ. exact HgeZ. }
    rewrite Hsk in Hmod. cbn [m_decl_go] in Hmod.
    (* 0x13d84 j 0x13f04 *)
    zstep.
    assert (EL : Z.of_nat (length T) = Z.of_nat (length (snd (V01_RES inp)))) by (rewrite <- Hmod; reflexivity).
    rewrite EL.
    eapply KT.
    unfold v01_tail_mem. rewrite <- Hmod. cbn [fst snd].
    split; [exact MEM|]. split; [exact MT|].
    destruct FRM as (w00 & w08 & w38 & FRM).
    exists w00, w08, (Z_to_bv 64 V01_MASK), w38. exact FRM.
Qed.

Lemma v01_loop : v01_split_stmt -> v01_add_stmt -> v01_loop_stmt.
Proof.
  intros SPL ADD inp S c mm tab mt m0 gp tp F fc Q GEO BASE KT.
  assert (H : forall n i, (length (v_segs inp) - i <= n)%nat -> K_loop_at inp S c mm tab mt m0 gp tp F fc Q i).
  { induction n as [|n IH]; intros i Hn.
    - intros T added ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 t3 t4 t5 t6 m (Hi & _). exfalso.
      apply Nat.le_0_r in Hn. apply Nat.sub_0_le in Hn.
      exact (Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ Hi Hn)).
    - apply (SPL inp S c mm tab mt m0 gp tp F fc Q i GEO BASE).
      + apply (v01_join inp S c mm tab mt m0 gp tp F fc Q i GEO BASE KT).
        intros Hlt. apply IH. exact (v01l_sub_succ _ _ _ Hn).
      + apply (ADD inp S c mm tab mt m0 gp tp F fc Q i GEO BASE).
        * apply (v01_join inp S c mm tab mt m0 gp tp F fc Q i GEO BASE KT).
          intros Hlt. apply IH. exact (v01l_sub_succ _ _ _ Hn).
        * exact KT. }
  intros i. apply (H (length (v_segs inp)) i). apply Nat.le_sub_l.
Qed.
