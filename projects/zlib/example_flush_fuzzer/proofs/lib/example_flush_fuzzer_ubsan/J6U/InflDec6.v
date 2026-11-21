(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma DECODE_k_S : forall k p index need s c r,
  DECODE_k (S k) p index need (mkW s c r)
  = if need (code_at s p (index (ir_hold r))) <=? ir_bits r
    then ARun (code_at s p (index (ir_hold r))) (mkW s c r)
    else (PULLBYTE ;; DECODE_k k p index need)%am (mkW s c r).
Proof.
  intros. cbn [DECODE_k abind HOLD gr gs w_r w_s].
  destruct (need (code_at s p (index (ir_hold r))) <=? ir_bits r); reflexivity.
Qed.
Lemma pull_decode_eq : forall k p index need s c r,
  (PULLBYTE ;; DECODE_k k p index need)%am (mkW s c r)
  = if ir_have r =? 0 then ALeave (mkW s c r) else DECODE_k k p index need (mkW s c (pullr c r)).
Proof. intros. unfold abind. rewrite PULLBYTE_eq. destruct (ir_have r =? 0); reflexivity. Qed.

Section DecLoop.
  Variable v : icv.
  Variables (s : inflate_state) (c : icall).
  Variables (p : codeptr) (index need : Z -> Z) (NB pcH pcE : Z).
  Variables (JS JE : iregs -> bvmap 5 word -> Prop).
  Local Abbreviation NI := (cv_NI v). Local Abbreviation NO := (cv_NO v).
  Local Abbreviation ent h := (code_at s p (index h)).

  Hypothesis C : ictx v.
  Hypothesis HNB : 0 <= NB <= 48.
  Hypothesis Hneed : forall h, 0 <= h -> need (ent h) <= NB.
  Hypothesis CI : CINV NI NO c.
  Hypothesis STEP_H : forall r R M,
    LMEM v (mkW s c r) M -> JS r R -> RINV NI NO r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    ir_bits r + 8 < need (ent (ir_hold (pull1 c r))) ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pcH) M s6u_rom)
               /\ JS (pull1 c r) R1.
  Hypothesis STEP_E : forall r R M,
    LMEM v (mkW s c r) M -> JS r R -> RINV NI NO r -> 0 < ir_have r -> ir_bits r + 8 < 64 ->
    need (ent (ir_hold (pull1 c r))) <= ir_bits r + 8 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pcE) M s6u_rom)
               /\ JE (pull1 c r) R1.
  Hypothesis DRY : forall r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS r R -> RINV NI NO r -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.

  Lemma dec_loop : forall k r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS r R -> RINV NI NO r ->
    ir_bits r < need (ent (ir_hold r)) -> NB < ir_bits r + 8 * Z.of_nat k ->
    match (PULLBYTE ;; DECODE_k k p index need)%am (mkW s c r) with
    | ARun here w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pcE) M s6u_rom)
        /\ JE r1 R1 /\ RINV NI NO r1 /\ same5 r r1
        /\ here = ent (ir_hold r1) /\ need here <= ir_bits r1 < NB + 8
        /\ LMEM v (mkW s c r1) M /\ RETC v (mkW s c r1) M
    | ALeave w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 pcH) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
        /\ LREG_leave v (mkW s c r1) R1 /\ RINV NI NO r1 /\ same5 r r1 /\ ir_have r1 = 0
        /\ ir_bits r1 < need (ent (ir_hold r1))
        /\ LMEM v (mkW s c r1) M /\ RETC v (mkW s c r1) M
    | ARet _ _ => False
    end.
  Proof.
    pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
    induction k as [|k IH]; intros r R M HM HRC HJ HR Hb Hk.
    { exfalso. cbn in Hk. pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R10 & R11). pose proof (Hneed (ir_hold r) ltac:(lia)). lia. }
    rewrite pull_decode_eq.
    pose proof HR as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11').
    pose proof (Hneed (ir_hold r) ltac:(lia)) as NB0.
    destruct (Z.eqb_spec (ir_have r) 0) as [Hz|Hz].
    - destruct (DRY r R M HM HRC HJ HR Hz) as (R1 & Hms & HL).
      exists r, R1. split; [reflexivity|]. split; [exact Hms|]. split; [exact HL|]. split; [exact HR|].
      split; [apply same5_refl|]. split; [exact Hz|]. split; [exact Hb|]. split; [exact HM | exact HRC].
    - destruct (pull1_RINV NI NO s c r ltac:(lia) ltac:(lia) HR CI ltac:(lia) ltac:(lia)) as [Ep HR1].
      rewrite Ep.
      assert (HM1 : LMEM v (mkW s c (pull1 c r)) M) by (apply (LMEM_regs v s c r c (pull1 c r) M HM); reflexivity).
      assert (HRC1 : RETC v (mkW s c (pull1 c r)) M) by (eapply RETC_regs; [exact HRC | reflexivity]).
      assert (S5 : same5 r (pull1 c r)) by (repeat split; reflexivity).
      assert (Hh1 : 0 <= ir_hold (pull1 c r)).
      { cbn. pose proof CI as (Cil & _ & _ & _ & _ & _ & _ & _ & Cinb & _).
        pose proof (Cinb (ir_next r) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia)). nia. }
      pose proof (Hneed (ir_hold (pull1 c r)) Hh1) as NB1.
      rewrite DECODE_k_S. change (ir_bits (pull1 c r)) with (ir_bits r + 8).
      destruct (Z.leb_spec (need (ent (ir_hold (pull1 c r)))) (ir_bits r + 8)) as [LE|GT].
      + destruct (STEP_E r R M HM HJ HR ltac:(lia) ltac:(lia) LE) as (R1 & Hms1 & HJ1).
        exists (pull1 c r), R1. split; [reflexivity|]. split; [exact Hms1|]. split; [exact HJ1|]. split; [exact HR1|].
        split; [exact S5|]. split; [reflexivity|]. split; [change (ir_bits (pull1 c r)) with (ir_bits r + 8); lia|]. split; [exact HM1 | exact HRC1].
      + destruct (STEP_H r R M HM HJ HR ltac:(lia) ltac:(lia) ltac:(lia)) as (R1 & Hms1 & HJ1).
        specialize (IH (pull1 c r) R1 M HM1 HRC1 HJ1 HR1 ltac:(change (ir_bits (pull1 c r)) with (ir_bits r + 8); lia) ltac:(change (ir_bits (pull1 c r)) with (ir_bits r + 8); cbn [Z.of_nat] in Hk |- *; lia)).
        destruct ((PULLBYTE ;; DECODE_k k p index need)%am (mkW s c (pull1 c r))) as [here w2 | w2 | rc w2]; [| | exact IH].
        * destruct IH as (r2 & R2 & -> & Hms2 & HJ2 & HR2 & S2 & E2 & B2 & HM2 & HRC2). exists r2, R2.
          split; [reflexivity|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HJ2|]. split; [exact HR2|].
          split; [exact (same5_trans _ _ _ S5 S2)|]. split; [exact E2|]. split; [exact B2|]. split; [exact HM2 | exact HRC2].
        * destruct IH as (r2 & R2 & -> & Hms2 & HL2 & HR2 & S2 & Z2 & B2 & HM2 & HRC2). exists r2, R2.
          split; [reflexivity|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HL2|]. split; [exact HR2|].
          split; [exact (same5_trans _ _ _ S5 S2)|]. split; [exact Z2|]. split; [exact B2|]. split; [exact HM2 | exact HRC2].
  Qed.
End DecLoop.


Lemma testbit_high64 : forall h m, 0 <= h < 2 ^ 64 -> 64 <= m -> Z.testbit h m = false.
Proof.
  intros h m Hh Hm. destruct (Z.eq_dec h 0) as [->|NZ]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [| lia]. apply (proj1 (Z.log2_lt_pow2 h 64 ltac:(lia))). lia.
Qed.
Lemma mask_exec : forall h e, 0 <= h < 2 ^ 64 -> 0 <= e < 32 ->
  Z.land h (Z.lxor (zaluw ALU_SLL (-1) e) (-1)) = h mod 2 ^ e.
Proof.
  intros h e Hh He. rewrite zaluw_sll_m1 by lia.
  replace (2 ^ 64 - 2 ^ e) with (Z.ldiff (Z.ones 64) (Z.ones e)).
  2:{ rewrite <- Z.sub_nocarry_ldiff.
      - unfold Z.ones. rewrite !Z.shiftl_1_l. lia.
      - apply Z.bits_inj'. intros m Hm. rewrite Z.ldiff_spec, Z.bits_0.
        destruct (Z_lt_le_dec m e); [| rewrite (Z.ones_spec_high e m) by lia; reflexivity].
        rewrite (Z.ones_spec_low e m), (Z.ones_spec_low 64 m) by lia. reflexivity. }
  rewrite Z.lxor_m1_r. rewrite <- Z.ldiff_land.
  rewrite <- (Z.land_ones h e) by lia.
  apply Z.bits_inj'. intros m Hm. rewrite Z.ldiff_spec, Z.ldiff_spec, Z.land_spec.
  destruct (Z_lt_le_dec m e).
  - rewrite (Z.ones_spec_low e m), (Z.ones_spec_low 64 m) by lia. cbn. rewrite andb_true_r. reflexivity.
  - rewrite (Z.ones_spec_high e m) by lia. destruct (Z_lt_le_dec m 64).
    + rewrite (Z.ones_spec_low 64 m) by lia. cbn. rewrite andb_false_r. reflexivity.
    + rewrite (Z.ones_spec_high 64 m) by lia. rewrite (testbit_high64 h m) by lia. reflexivity.
Qed.



Definition ctab6 (v : icv) (p : codeptr) : Z := codeptr_addr 75438 77486 (cv_S v) p.
Definition cofs_ok (p : codeptr) : Prop := match p with CDyn ofs => 0 <= ofs <= 1444 | _ => True end.

Lemma ctab6_cells : forall v s c r M p, ictx v -> LMEM v (mkW s c r) M -> cofs_ok p ->
  cells s6u_segs M (ctab6 v p) 4 4 (cext p) (cat (is_codes s) p).
Proof.
  intros v s c r M p C HM Hp. destruct p as [ofs| |]; cbn [ctab6 codeptr_addr cext cat] in *.
  - pose proof (cells_shift s6u_segs M (cv_S v + 1384) 4%nat 1444 (arr_get (is_codes s)) ofs (lm_codes _ _ _ HM) Hp) as X.
    intros i Hi. exact (X i Hi).
  - apply lenfix6_cells. exact (lm_rod _ _ _ HM).
  - apply distfix6_cells. exact (lm_rod _ _ _ HM).
Qed.

Lemma ctab6_range : forall v p, ictx v -> cofs_ok p -> 0 < ctab6 v p /\ ctab6 v p + 4 * cext p < 2 ^ 63.
Proof.
  intros v p C Hp. pose proof (ic_S _ C) as CS.
  destruct p as [ofs| |]; cbn [ctab6 codeptr_addr cext cofs_ok] in *; lia.
Qed.


Lemma idx1_exec : forall h b bits n,
  0 <= bits -> bits + 8 <= 64 -> 0 <= h < 2 ^ bits -> 0 <= b < 256 -> 0 <= n <= 32 ->
  Z.land (Z.ones n) (zalu ALU_SLL b bits + h) = BITSv (h + b * 2 ^ bits) n.
Proof.
  intros h b bits n Hb0 Hb64 Hh Hby Hn.
  pose proof (pull_hold_lt h b bits Hh Hb0 Hby) as P.
  assert (2 ^ (bits + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite zalu_sll_small by lia. rewrite Z.land_comm, BITSv_land by lia. f_equal. lia.
Qed.
Lemma idx0_exec : forall h n, 0 <= h -> 0 <= n <= 32 -> Z.land (Z.ones n) h = BITSv h n.
Proof. intros h n Hh Hn. rewrite Z.land_comm, BITSv_land by lia. reflexivity. Qed.

Lemma ones_range15 : forall n, 1 <= n <= 15 -> 0 <= Z.ones n < 2 ^ 15.
Proof.
  intros n Hn. unfold Z.ones. rewrite Z.shiftl_1_l.
  pose proof (Z.pow_le_mono_r 2 n 15 ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 n ltac:(lia) ltac:(lia)). cbn; lia.
Qed.

End FXG.
Ltac tab_read TAB J :=
  lazymatch type of TAB with cells _ ?m ?A 4 4%nat ?n ?f =>
    lazymatch goal with
    | |- exists bs, rdn _ _ (zw ?a) 1 = Some bs /\ bytes_le_to_Z bs = code_bits _ =>
        apply (ctab_read_bits s6u_segs m A n f J a TAB); [| lia]
    | |- exists bs, rdn _ _ (zw ?a) 1 = Some bs /\ bytes_le_to_Z bs = code_op _ =>
        apply (ctab_read_op s6u_segs m A n f J a TAB); [| lia]
    | |- exists bs, rdn _ _ (zw ?a) 2 = Some bs /\ bytes_le_to_Z bs = code_val _ =>
        apply (ctab_read_val s6u_segs m A n f J a TAB); [| lia]
    end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma idx2_core : forall H m k val,
  0 <= H -> 0 <= m <= 15 -> 0 <= k <= 15 -> 0 <= val < 2 ^ 16 ->
  ((zaluw ALU_SRL (Z.land H (Z.ones m)) k + val) * 2 ^ 32) mod 2 ^ 64 / 2 ^ 30 = 4 * (val + Z.shiftr (BITSv H m) k).
Proof.
  intros H m k val HH Hm Hk Hv.
  rewrite Z.land_ones by lia. rewrite BITSv_land, Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound H (2 ^ m) ltac:(apply Z.pow_pos_nonneg; lia)) as B.
  assert (P15 : 2 ^ m <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  rewrite zaluw_srl_small by (cbn in P15 |- *; lia).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as Pk.
  assert (D : 0 <= H mod 2 ^ m / 2 ^ k <= H mod 2 ^ m).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite Z.mod_small by (cbn in P15 |- *; lia).
  change (2 ^ 32) with (4 * 2 ^ 30). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.
Lemma idx2_pull : forall h b bits m k val,
  0 <= bits -> bits + 8 <= 64 -> 0 <= h < 2 ^ bits -> 0 <= b < 256 -> 0 <= m <= 15 -> 0 <= k <= 15 -> 0 <= val < 2 ^ 16 ->
  ((zaluw ALU_SRL (Z.land (zalu ALU_SLL b bits + h) (Z.ones m)) k + val) * 2 ^ 32) mod 2 ^ 64 / 2 ^ 30
  = 4 * (val + Z.shiftr (BITSv (h + b * 2 ^ bits) m) k).
Proof.
  intros h b bits m k val Hb0 Hb64 Hh Hby Hm Hk Hv.
  pose proof (pull_hold_lt h b bits Hh Hb0 Hby) as P.
  assert (2 ^ (bits + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite zalu_sll_small by lia. replace (b * 2 ^ bits + h) with (h + b * 2 ^ bits) by lia.
  apply idx2_core; lia.
Qed.

Lemma mask_reg : forall n, 0 <= n < 32 -> zw (Z.lxor (zaluw ALU_SLL (-1) n) (-1)) = zw (Z.ones n).
Proof.
  intros n Hn. rewrite zaluw_sll_m1 by lia. rewrite Z.lxor_m1_r. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
  apply zw_eqm. rewrite <- (Z.mod_add _ 1) by lia. f_equal. unfold Z.pred. lia.
Qed.

Lemma idx2_probe : forall H m k val,
  0 <= H < 2 ^ 64 -> 0 <= m <= 15 -> 0 <= k <= 15 -> 0 <= val < 2 ^ 16 ->
  ((zaluw ALU_SRL (Z.land H (Z.lxor (zaluw ALU_SLL (-1) m) (-1))) k + val) * 2 ^ 32) mod 2 ^ 64 / 2 ^ 30
  = 4 * (val + Z.shiftr (BITSv H m) k).
Proof.
  intros H m k val HH Hm Hk Hv. rewrite mask_exec by lia. rewrite <- (Z.land_ones H m) by lia. apply idx2_core; lia.
Qed.

Lemma idx0_probe : forall h n, 0 <= h < 2 ^ 64 -> 0 <= n < 32 ->
  Z.land (Z.lxor (zaluw ALU_SLL (-1) n) (-1)) h = BITSv h n.
Proof. intros h n Hh Hn. rewrite Z.land_comm, mask_exec by lia. rewrite BITSv_land, Z.land_ones by lia. reflexivity. Qed.


Definition LFIXc (v : icv) (R : bvmap 5 word) : Prop :=
  getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (cv_ZP v)
  /\ getr R 1 = zw 16209 /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.
Lemma LFIX_LFIXc : forall v R, LFIX v R -> LFIXc v R.
Proof. intros v R HF. unfold LFIX in HF. destruct HF as (G2 & G27 & G13 & G8 & G11 & G1 & G3 & G4). unfold LFIXc. repeat split; assumption. Qed.
End FXG.
Ltac open_fixc HF :=
  let X := fresh in pose proof HF as X; unfold LFIXc, INF_FRAME in X; destruct X as (G2 & G27 & G8 & G1 & G3 & G4).
Ltac lfixc_close Hfr HR :=
  unfold LFIXc, INF_FRAME;
  repeat match goal with |- _ /\ _ => split end;
  lazymatch goal with |- getr _ ?n = _ =>
    first [ rewrite (Hfr n eq_refl); assumption
          | let G := fresh "G" in symex_reg HR n as G; rewrite G; first [ reflexivity | assumption | apply zw_neg_mod | f_equal; lia ]
          | match goal with |- ?G => idtac "LFIXc LEFT" G end ]
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition clo (v : Z) : Z := v mod 65536.
Definition cent (v : Z) : Z := v mod 4294967296.
Lemma clo_range : forall v, 0 <= clo v < 65536.
Proof. intros v. unfold clo. apply Z.mod_pos_bound. lia. Qed.
Lemma cent_range : forall v, 0 <= cent v < 4294967296.
Proof. intros v. unfold cent. apply Z.mod_pos_bound. lia. Qed.
Lemma cent_reasm : forall v, Z.lor (code_val v * 2 ^ 16) (clo v) = cent v.
Proof.
  intros v. unfold clo, cent. rewrite code_val_eq.
  assert (D : Z.land (v / 65536 mod 65536 * 2 ^ 16) (v mod 65536) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 16) as [L|G].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - change 65536 with (2 ^ 16) at 3. rewrite (Z.mod_pow2_bits_high v 16 n) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D.
  change 4294967296 with (65536 * 65536). rewrite Z.rem_mul_r by lia.
  change (2 ^ 16) with 65536. lia.
Qed.
Lemma cent_bits : forall v, (cent v / 2 ^ 8) mod 2 ^ 8 = code_bits v.
Proof.
  intros v. unfold cent. rewrite code_bits_eq. apply Z.bits_inj'. intros n Hn.
  change 256 with (2 ^ 8). change 4294967296 with (2 ^ 32).
  destruct (Z_lt_le_dec n 8) as [L|G].
  - rewrite !Z.mod_pow2_bits_low, !Z.div_pow2_bits by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma cent_op : forall v, cent v mod 2 ^ 8 = code_op v.
Proof.
  intros v. unfold cent. rewrite code_op_eq. apply Z.bits_inj'. intros n Hn. change 256 with (2 ^ 8). change 4294967296 with (2 ^ 32).
  destruct (Z_lt_le_dec n 8) as [L|G].
  - rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma cent_val : forall v, cent v / 2 ^ 16 = code_val v.
Proof.
  intros v. unfold cent. rewrite code_val_eq. apply Z.bits_inj'. intros n Hn. change 65536 with (2 ^ 16). change 4294967296 with (2 ^ 32).
  rewrite Z.div_pow2_bits by lia.
  destruct (Z_lt_le_dec n 16) as [L|G].
  - rewrite !Z.mod_pow2_bits_low, Z.div_pow2_bits by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Section Halves.
  Variable segs : list Segment.
  Lemma code_read_lo16 : forall m (A : Z) v,
    cell segs m A 4 v -> exists bs, rdn segs m (zw A) 2 = Some bs /\ bytes_le_to_Z bs = clo v.
  Proof.
    intros m A v Hc. unfold cell in Hc.
    exists (firstn 2 (Z_to_le_bytes 4 v)). split.
    - exact (rdn_firstn segs m 4 (zw A) _ 2 Hc ltac:(lia)).
    - rewrite firstn_Z_to_le_bytes by lia. rewrite bytes_le_to_Z_of_Z. reflexivity.
  Qed.
  Lemma ctab_read_lo16 : forall m A n f i a,
    cells segs m A 4 4 n f -> 0 <= i < n -> a = A + 4 * i ->
    exists bs, rdn segs m (zw a) 2 = Some bs /\ bytes_le_to_Z bs = clo (f i).
  Proof. intros m A n f i a Hc Hi ->. apply code_read_lo16. exact (Hc i Hi). Qed.
End Halves.

End FXG.
Ltac tab_read2 TAB J :=
  lazymatch type of TAB with cells _ ?m ?A 4 4%nat ?n ?f =>
    lazymatch goal with
    | |- exists bs, rdn _ _ (zw ?a) 2 = Some bs /\ bytes_le_to_Z bs = clo _ =>
        apply (ctab_read_lo16 s6u_segs m A n f J a TAB); [| lia]
    | |- exists bs, rdn _ _ (zw ?a) 2 = Some bs /\ bytes_le_to_Z bs = code_val _ =>
        apply (ctab_read_val s6u_segs m A n f J a TAB); [| lia]
    | |- exists bs, rdn _ _ (zw ?a) 1 = Some bs /\ bytes_le_to_Z bs = code_bits _ =>
        apply (ctab_read_bits s6u_segs m A n f J a TAB); [| lia]
    | |- exists bs, rdn _ _ (zw ?a) 1 = Some bs /\ bytes_le_to_Z bs = code_op _ =>
        apply (ctab_read_op s6u_segs m A n f J a TAB); [| lia]
    end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma cent_shr8 : forall v, cent v / 2 ^ 8 = code_bits v + 2 ^ 8 * code_val v.
Proof.
  intros v. rewrite <- cent_bits, <- cent_val.
  change (2 ^ 16) with (2 ^ 8 * 2 ^ 8). rewrite <- (Z.div_div (cent v) (2 ^ 8) (2 ^ 8)) by lia.
  pose proof (Z.div_mod (cent v / 2 ^ 8) (2 ^ 8) ltac:(lia)). lia.
Qed.
Lemma cent_shr8_range : forall v, 0 <= cent v / 2 ^ 8 < 2 ^ 24.
Proof. intros v. pose proof (cent_range v). split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]]. cbn in *. lia. Qed.
Lemma cent_bits_mod : forall v k, 0 <= k <= 8 -> (cent v / 2 ^ 8) mod 2 ^ k = code_bits v mod 2 ^ k.
Proof.
  intros v k Hk. rewrite cent_shr8.
  replace (2 ^ 8 * code_val v) with ((2 ^ (8 - k) * code_val v) * 2 ^ k)
    by (rewrite (Z.mul_comm (2 ^ (8 - k) * code_val v)), Z.mul_assoc, <- Z.pow_add_r by lia; f_equal; f_equal; lia).
  rewrite Z.mod_add by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
Lemma cent_bits5 : forall v, code_bits v < 32 -> (cent v / 2 ^ 8) mod 2 ^ 5 = code_bits v.
Proof. intros v H. rewrite cent_bits_mod by lia. apply Z.mod_small. pose proof (code_bits_range v). lia. Qed.
Lemma cent_bits6 : forall v, code_bits v < 64 -> (cent v / 2 ^ 8) mod 2 ^ 6 = code_bits v.
Proof. intros v H. rewrite cent_bits_mod by lia. apply Z.mod_small. pose proof (code_bits_range v). lia. Qed.

Lemma zalu_srl_mod : forall a b, zalu ALU_SRL a b = zalu ALU_SRL a (b mod 2 ^ 6).
Proof. intros a b. unfold zalu. rewrite !zw_srl. change (2 ^ 6) with 64. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma srl_cent : forall h v, 0 <= h < 2 ^ 64 -> code_bits v < 64 -> zalu ALU_SRL h (cent v / 2 ^ 8) = h / 2 ^ code_bits v.
Proof.
  intros h v Hh Hb. rewrite zalu_srl_mod, cent_bits6 by exact Hb. pose proof (code_bits_range v).
  apply zalu_srl_small; lia.
Qed.

Lemma land_zero_bits : forall x m, (forall n, 0 <= n -> Z.testbit m n = true -> Z.testbit x n = false) -> Z.land x m = 0.
Proof.
  intros x m H. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.testbit m n) eqn:E; [| apply Bool.andb_false_r]. rewrite (H n Hn E). reflexivity.
Qed.
Lemma testbit_window : forall c a w n, 0 <= a -> 0 <= w -> 0 < c < 2 ^ w -> 0 <= n ->
  Z.testbit (c * 2 ^ a) n = true -> a <= n < a + w.
Proof.
  intros c a w n Ha Hw Hc Hn T.
  destruct (Z_lt_le_dec n a) as [L|G].
  - rewrite Z.mul_pow2_bits_low in T by lia. discriminate T.
  - rewrite Z.mul_pow2_bits in T by lia. split; [exact G|].
    destruct (Z_lt_le_dec (n - a) w) as [L2|G2]; [lia|]. exfalso.
    rewrite Z.bits_above_log2 in T; [discriminate T | lia |].
    pose proof (proj1 (Z.log2_lt_pow2 c w ltac:(lia)) ltac:(lia)). lia.
Qed.
Lemma testbit_lowfield : forall b q k n, 0 <= b < 2 ^ k -> 0 <= k <= 8 -> 0 <= q -> k <= n < 8 -> Z.testbit (b + 2 ^ 8 * q) n = false.
Proof.
  intros b q k n Hb Hk Hq Hn.
  rewrite <- (Z.mod_pow2_bits_low _ 8) by lia.
  replace ((b + 2 ^ 8 * q) mod 2 ^ 8) with b.
  - destruct (Z.eq_dec b 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    pose proof (proj1 (Z.log2_lt_pow2 b k ltac:(lia)) ltac:(lia)). lia.
  - rewrite Z.mul_comm, Z.mod_add by lia. symmetry. apply Z.mod_small. 
    pose proof (Z.pow_le_mono_r 2 k 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma land192_cent : forall v, code_bits v < 64 -> Z.land (cent v / 2 ^ 8) 192 = 0.
Proof.
  intros v Hb. pose proof (code_bits_range v) as R. pose proof (code_val_range v) as V. rewrite cent_shr8.
  apply land_zero_bits. intros n Hn T. change 192 with (3 * 2 ^ 6) in T.
  pose proof (testbit_window 3 6 2 n ltac:(lia) ltac:(lia) ltac:(cbn; lia) Hn T) as W.
  apply (testbit_lowfield (code_bits v) (code_val v) 6 n); cbn in *; lia.
Qed.
Lemma land57344_cent : forall v, code_bits v < 32 -> Z.land (cent v) 57344 = 0.
Proof.
  intros v Hb. pose proof (code_bits_range v) as R. pose proof (code_val_range v) as V. pose proof (cent_range v) as CR.
  apply land_zero_bits. intros n Hn T. change 57344 with (7 * 2 ^ 13) in T.
  pose proof (testbit_window 7 13 3 n ltac:(lia) ltac:(lia) ltac:(cbn; lia) Hn T) as W.
  replace n with ((n - 8) + 8) by lia. rewrite <- Z.div_pow2_bits by lia. rewrite cent_shr8.
  apply (testbit_lowfield (code_bits v) (code_val v) 5 (n - 8)); cbn in *; lia.
Qed.

Lemma idx2_core_w : forall H m k val,
  0 <= H -> 0 <= m <= 15 -> 0 <= k <= 15 -> 0 <= val < 2 ^ 16 ->
  (zaluw ALU_SRL (Z.land H (Z.ones m)) k + val) mod 2 ^ 32 = val + Z.shiftr (BITSv H m) k.
Proof.
  intros H m k val HH Hm Hk Hv. pose proof (idx2_core H m k val HH Hm Hk Hv) as E.
  change (2 ^ 64) with (2 ^ 32 * 2 ^ 32) in E. rewrite Z.mul_mod_distr_r in E by lia.
  change (2 ^ 32) with (4 * 2 ^ 30) in E at 2. rewrite Z.mul_assoc, Z.div_mul in E by lia. lia.
Qed.
Lemma idx2_pull_w : forall h b bits m k val,
  0 <= bits -> bits + 8 <= 64 -> 0 <= h < 2 ^ bits -> 0 <= b < 256 -> 0 <= m <= 15 -> 0 <= k <= 15 -> 0 <= val < 2 ^ 16 ->
  (zaluw ALU_SRL (Z.land (zalu ALU_SLL b bits + h) (Z.ones m)) k + val) mod 2 ^ 32 = val + Z.shiftr (BITSv (h + b * 2 ^ bits) m) k.
Proof.
  intros h b bits m k val Hb0 Hb64 Hh Hby Hm Hk Hv.
  pose proof (pull_hold_lt h b bits Hh Hb0 Hby) as P.
  assert (2 ^ (bits + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite zalu_sll_small by lia. replace (b * 2 ^ bits + h) with (h + b * 2 ^ bits) by lia.
  apply idx2_core_w; lia.
Qed.
Lemma idx2_probe_w : forall H m k val,
  0 <= H < 2 ^ 64 -> 0 <= m <= 15 -> 0 <= k <= 15 -> 0 <= val < 2 ^ 16 ->
  (zaluw ALU_SRL (Z.land H (Z.lxor (zaluw ALU_SLL (-1) m) (-1))) k + val) mod 2 ^ 32 = val + Z.shiftr (BITSv H m) k.
Proof.
  intros H m k val HH Hm Hk Hv. rewrite mask_exec by lia. rewrite <- (Z.land_ones H m) by lia. apply idx2_core_w; lia.
Qed.
End FXG.
