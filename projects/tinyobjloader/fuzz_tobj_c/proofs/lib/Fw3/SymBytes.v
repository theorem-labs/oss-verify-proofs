(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "byte_ok"; "beval"; "cells_bytes"; "BLit"; "byte_of"; "find_cover"; "bexp_eqb"; "bor"; "@Corelib.Init.Datatypes"; "bool"; "Some"; "option"; "nat"; "false"; "list"; "true"; "pair"; "prod"; "None"; "andb"; "length"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_or"; "bv_wrap"; "@Stdlib.ZArith.BinInt.Z"; "le"; "testbit"; "add"; "modulo"; "lt"; "land"; "pow"; "eqb"; "to_nat"; "mul"; "of_N"; "of_nat"; "ltb"; "div"; "lor"; "shiftl"; "shiftr"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "cell"; "valuation"; "sv"; "eval"; "soff"; "ob_base"; "ob_cells"; "obj_holds"; "sobj"; "obj_hi_of"; "obj_lo_of"; "obj_wf"; "enc_bytes"; "ext_low"; "rd_bytes"; "rl"; "SLBytes"; "SLit"; "c_off"; "c_val"; "c_width"; "mkCell"; "rd"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_read_byte"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@Corelib.Init.Peano"; "lt"; "le"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SRL"; "ALU_SLL"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "low32"; "alu32"; "@Stdlib.Lists.List"; "In"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "le_bytes_to_word"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "read_bytes_aux"; "read_bytes_map"; "read_u64"; "@LinuxProcessSemantics.Riscv.Prelude"; "sext"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "same_atoms"; "snorm"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundM SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive bexp := BLit (z : Z) | BSrc (l : positive) (i : Z).

Definition beval (rho : valuation) (b : bexp) : byte := ltac2:(tb__ "0|2|
S6S1cQ8M0A1M1Lb;Vb;S0S1dG0R1A2Lz;S1S0S4bG1S28R1A1S41Vrho;R2A2S1dG0Z0A2A4Li;Ll;X6x2").

Definition bexp_eqb (a b : bexp) : bool := ltac2:(tb__ "0|2|
S6SfLa;Va;S0S6SfLb;M0Vb;S0S27S23R2Z100M1A2S23R1G1A2A2Ly;S1S0S13Li;Ll;X6x2Lx;S1S0G0Vb;S0S13Lz;S1S0S19S5dR4R2A2S27R3R1A2A2Li';Ll';X6x2Li;Ll;X6x2").

Definition bor (a b : bexp) : option bexp := ltac2:(tb__ "0|8|
S6S11S6A1M0La;Va;S0S6G0Lb;M1Vb;S0S10S6SaS2eS23R2Z100M2A2S23R1G2A2M3A2A1A2Ly;S1S0SfG0L_;M4S27S23R3G2A2Z0M5A2S10S6Vb;A2S18S6A1M6Xfx2Li;Ll;X6x2Lx;S1S0G1Vb;S0G4S27G3G5A2S10S6Va;A2M7G6Xfx2Ly;S1S0G4SdVa;Vb;A2G7G6Xfx2Li0;Ll0;X6x2Li;Ll;X6x2").

Fixpoint byte_of (e : sv) (t : nat) {struct e} : option bexp :=
  match e with
  | SLit z => Some (BLit (Z.shiftr (z mod 2 ^ 64) (8 * Z.of_nat t) mod 256))
  | SLBytes l (SLit i0) k =>
      let i := i0 mod 2 ^ 64 in
      if (0 <=? i) && (0 <=? k) && (k <=? 8) then
        Some (if Z.of_nat t <? k then BSrc l (i + Z.of_nat t) else BLit 0)
      else None
  | SLBytes _ _ _ => None
  | SExt sgn w a =>
      if (8 * (Z.of_nat t + 1) <=? Z.of_N w) && (Z.of_N w <=? 64) then byte_of a t
      else if negb sgn && (Z.of_N w <=? 8 * Z.of_nat t) && (Z.of_N w <=? 64) then Some (BLit 0)
      else None
  | SAlu ALU_SRL a (SLit s) =>
      let s' := Z.land (s mod 2 ^ 64) 63 in
      if s' mod 8 =? 0 then
        (if Z.of_nat t + s' / 8 <? 8 then byte_of a (t + Z.to_nat (s' / 8)) else Some (BLit 0))
      else None
  | SAlu ALU_SLL a (SLit s) =>
      let s' := Z.land (s mod 2 ^ 64) 63 in
      if s' mod 8 =? 0 then
        (if Z.of_nat t <? s' / 8 then Some (BLit 0) else byte_of a (t - Z.to_nat (s' / 8)))
      else None
  | SAluW ALU_SRL a (SLit s) =>
      let s' := Z.land ((s mod 2 ^ 64) mod 2 ^ 32) 31 in
      if (s' mod 8 =? 0) && (Z.of_nat t <? 4) then
        (if Z.of_nat t + s' / 8 <? 4 then byte_of a (t + Z.to_nat (s' / 8)) else Some (BLit 0))
      else None
  | SAlu ALU_OR a b =>
      match byte_of a t, byte_of b t with
      | Some x, Some y => bor x y
      | _, _ => None
      end
  | _ => None
  end.

Lemma u8_range : ltac2:(tb__ "0|2|
S1cQ8M0A1S4S20Z0S1bG0R1A2M1A2S24G1Z100A2A2Fb;").
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma testbit_u8 : ltac2:(tb__ "0|1|
S0S0S4S20Z0R1A2S24R1Z8A2A2S3SfS21S1bQ8M0S1dG0R3A2A2R2A2S21R3R2A2A3F_;Fj;Fz;").
Proof.
  intros z j Hj. rewrite Z_to_bv_unsigned. apply bv_wrap_spec_low. cbn. lia.
Qed.

Lemma testbit_u8_high : ltac2:(tb__ "0|1|
S1cQ8M0A1S0S20Z8R1A2S3SfS21S1bG0R3A2R2A2S13A3F_;Fj;Fb;").
Proof.
  intros b j Hj. pose proof (u8_range b). apply (testbit_high_small _ 8); lia.
Qed.

Lemma testbit_u64_high : ltac2:(tb__ "0|1|
S1cQ40M0A1S0S20Z40R1A2S3SfS21S1bG0R3A2R2A2S13A3F_;Fj;Fw;").
Proof.
  intros w j Hj. pose proof (urange w). apply (testbit_high_small _ 64); lia.
Qed.

Lemma land63 : ltac2:(tb__ "0|1|
S0S4S20Z0S25R1Z3fA2M0A2S24G0Z40A2A2Fx;").
Proof. intros x. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma land31 : ltac2:(tb__ "0|1|
S0S4S20Z0S25R1Z1fA2M0A2S24G0Z20A2A2Fx;").
Proof. intros x. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Definition byte_ok (rho : valuation) (v : word) (t : nat) (b : bexp) : Prop := ltac2:(tb__ "0|1|
S0S4S20Z0R1A2S24R1Z8M0A2A2S3SfS21S1bQ40Vv;A2S22S29G0S2bVt;A1A2R2A2A2S21S1bQ8S8Vrho;Vb;A2A2R2A2A3F_;Fj;").

Lemma byte_ok_lit0 : ltac2:(tb__ "0|3|
S33S1cQ40M0A1S12S0S4S20Z0M1R1A2S24R1Z8M2A2A2S3SfS21S1bG0R4A2S22S29G2S2bR3A1A2R2A2A2S13A3F_;Fj;S7R4R3R2SaG1A1A4F_;Ft;Fv;Frho;").
Proof. intros rho v t H j Hj. rewrite (H j Hj). cbn. rewrite Z.bits_0. reflexivity. Qed.

Lemma bor_sound : ltac2:(tb__ "0|2|
S33S1cQ40M0A1M1G1S12S6S6S6S7R7R6R4R3A4S7R8R6R5R3A4S3S11S6A1SeR5R4A2S10S6R3A2A3S7RaS1eG0R9R8A3R7R4A4F_;F_;F_;Fr;Fy;Fx;Ft;Fvb;Fva;Frho;").
Proof.
  intros rho va vb t x y r Hx Hy Hb j Hj.
  rewrite bv_or_unsigned, Z.lor_spec, (Hx j Hj), (Hy j Hj).
  unfold bor in Hb.
  destruct x as [xz|xl xi], y as [yz|yl yi].
  - inversion Hb; subst. cbn [beval]. rewrite !testbit_u8 by lia. rewrite Z.lor_spec.
    rewrite <- (Z.mod_pow2_bits_low xz 8 j) by lia. rewrite <- (Z.mod_pow2_bits_low yz 8 j) by lia. reflexivity.
  - destruct (xz mod 256 =? 0) eqn:E; [|discriminate]. inversion Hb; subst. apply Z.eqb_eq in E.
    cbn [beval]. rewrite testbit_u8 by lia. rewrite <- (Z.mod_pow2_bits_low xz 8 j) by lia.
    change (2 ^ 8) with 256. rewrite E, Z.bits_0. reflexivity.
  - destruct (yz mod 256 =? 0) eqn:E; [|discriminate]. inversion Hb; subst. apply Z.eqb_eq in E.
    cbn [beval]. rewrite (testbit_u8 yz) by lia. rewrite <- (Z.mod_pow2_bits_low yz 8 j) by lia.
    change (2 ^ 8) with 256. rewrite E, Z.bits_0, Bool.orb_false_r. reflexivity.
  - destruct (bexp_eqb (BSrc xl xi) (BSrc yl yi)) eqn:E; [|discriminate]. inversion Hb; subst.
    cbn in E. apply andb_prop in E as [E1 E2]. apply Pos.eqb_eq in E1. apply Z.eqb_eq in E2. subst.
    apply Bool.orb_diag.
Qed.

Lemma testbit_ext_low : ltac2:(tb__ "0|1|
SfS2S1cQ40M0A1S0S4S20Z0R1A2S24R1S2aR3A1A2A2S20S2aR4A1Z40A2S3SfS21S1bG0S3fR6R5R4A3A2R3A2S21S1bG0R4A2R3A2A3F_;F_;Fp;Fv;Fw;Fsgn;").
Proof.
  intros sgn w v p Hp Hw. unfold ext_low. destruct sgn.
  - unfold sext. rewrite bv_sign_extend_unsigned. rewrite bv_wrap_spec_low by (cbn; lia).
    unfold bv_signed. rewrite bv_swrap_spec by lia.
    rewrite bv_extract_unsigned, Z.shiftr_0_r.
    destruct (bool_decide (p < Z.of_N w - 1)) eqn:E.
    + apply bool_decide_eq_true in E. rewrite bv_wrap_spec_low by lia. reflexivity.
    + apply bool_decide_eq_false in E. rewrite bv_wrap_spec_low by lia. f_equal. lia.
  - unfold zext. rewrite bv_zero_extend_unsigned'. rewrite bv_wrap_spec_low by (cbn; lia).
    rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_spec_low. lia.
Qed.

Lemma testbit_zext_high : ltac2:(tb__ "0|1|
S2S1cQ40M0A1S0S20S2aR3A1R1A2S3SfS21S1bG0S3fS13R4R3A3A2R2A2S13A3F_;Fp;Fv;Fw;").
Proof.
  intros w v p Hp. unfold ext_low, zext. rewrite bv_zero_extend_unsigned'.
  destruct (Z.lt_ge_cases p 64).
  - rewrite bv_wrap_spec_low by (cbn; lia). rewrite bv_extract_unsigned. apply bv_wrap_spec_high. lia.
  - apply bv_wrap_spec_high. cbn. lia.
Qed.

Lemma srl_unsigned : ltac2:(tb__ "0|1|
S1cQ40M0A1S0S3S0S1bG0S51S4fR2S1dG0R1A2A3A2S30S1bG0R2A2S25S23R1S26Z2Z40A2A2Z3fA2A2A3Fs;Fv;").
Proof.
  intros v s. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64. change (63 mod 2 ^ 64) with 63. reflexivity.
Qed.

Lemma sll_unsigned : ltac2:(tb__ "0|1|
S1cQ40M0A1S0S3S0S1bG0S51S50R2S1dG0R1A2A3A2S1fG0S2fS1bG0R2A2S25S23R1S26Z2Z40A2A2Z3fA2A2A2A3Fs;Fv;").
Proof.
  intros v s. cbn [alu64 alu]. rewrite bv_shiftl_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap at 2 3. rewrite two64. change (63 mod 2 ^ 64) with 63. reflexivity.
Qed.

Lemma srlw_testbit : ltac2:(tb__ "0|4|
S1cQ40M0A1S0S0S4S20Z0R1A2S24R1Z20M1A2A2S3SfS21S1bG0S5aQ20G0S53S4fS52R4A1S52S1dG0R3A2A1A3A3A2R2A2S25S23S23R3S26Z2M2Z40A2A2S26G2G1A2A2Z1fA2S0SfSfL_;S2cS22R3R1A2M3G1A2S21S1bG0R5A2G3A2S13Xfx2Ts';A3F_;Fp;Fs;Fv;").
Proof.
  intros v s p Hp. cbv zeta.
  set (s' := Z.land ((s mod 2 ^ 64) mod 2 ^ 32) 31). pose proof (land31 ((s mod 2 ^ 64) mod 2 ^ 32)) as Hs'. fold s' in Hs'.
  unfold sext. rewrite bv_sign_extend_unsigned. rewrite bv_wrap_spec_low by (cbn; lia).
  unfold bv_signed. rewrite bv_swrap_spec by lia.
  assert (E : forall q, 0 <= q < 32 ->
            Z.testbit (bv_unsigned (alu32 ALU_SRL (low32 v) (low32 (Z_to_bv 64 s)))) q
            = if q + s' <? 32 then Z.testbit (bv_unsigned v) (q + s') else false).
  { intros q Hq. cbn [alu32 alu]. rewrite bv_shiftr_unsigned, bv_and_unsigned.
    unfold low32. rewrite !bv_extract_unsigned, !Z.shiftr_0_r, !Z_to_bv_unsigned.
    replace (Z.land (bv_wrap 32 (bv_wrap 64 s)) (bv_wrap 32 31)) with s'.
    2:{ unfold s', bv_wrap. rewrite two64. change (bv_modulus 32) with (2 ^ 32). reflexivity. }
    rewrite Z.shiftr_spec by lia.
    destruct (Z.ltb_spec (q + s') 32).
    - apply bv_wrap_spec_low. lia.
    - apply bv_wrap_spec_high. cbn. lia. }
  destruct (bool_decide (p < Z.of_N 32 - 1)) eqn:Eb.
  - apply E. lia.
  - apply bool_decide_eq_false in Eb. cbn in Eb. replace p with 31 by lia. apply (E 31). lia.
Qed.

Lemma nth_error_firstn_lt : forall {A} (l : list A) n t, (t < n)%nat -> nth_error (firstn n l) t = nth_error l t.
Proof.
  intros A l. induction l as [|x l IH]; intros n t Ht.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. cbn [firstn]. destruct t as [|t]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma nth_error_firstn_ge : forall {A} (l : list A) n t, (n <= t)%nat -> nth_error (firstn n l) t = None.
Proof.
  intros A l n t H. apply (proj2 (nth_error_None _ _)). rewrite length_firstn. lia.
Qed.

Lemma nth_error_skipn' : forall {A} (l : list A) (i q : nat), nth_error (skipn i l) q = nth_error l (i + q).
Proof.
  intros A l. induction l as [|x l IH]; intros i q.
  - rewrite skipn_nil. destruct q as [|q]; [destruct (i + 0)%nat; reflexivity | destruct (i + S q)%nat; reflexivity].
  - destruct i as [|i]; [reflexivity|]. cbn. apply IH.
Qed.

Lemma slbytes_testbit : ltac2:(tb__ "0|4|
S33S1S0S0S0S23R3S26Z2Z40A2A2S0S20Z0M0R1A2S4S20G0R4A2M1S20R4Z8M2A2A2G1S3SfS21S1bQ40S35R9S42R8S43R7A1R6A3A2A2R5A2SfSfL_;S2cR5S29G2R6A2A2S21S1bQ8M3S4bS1cG3A1S55S28R4A1S28S2dR5G2A2A1A2S41R9R8A2S1dG3G0A2A4A2S23R5G2A2A2S13Xfx2A3F_;F_;F_;Ti;Fp;Fk;Fi0;Fl;Frho;").
Proof.
  intros rho l i0 k p i Hi Hk Hp. cbn [eval]. rewrite lit_unsigned. fold i.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned.
  destruct (Z.lt_ge_cases p 64).
  2:{ rewrite bv_wrap_spec_high by (cbn; lia). destruct (Z.ltb_spec p (8 * k)); [lia|reflexivity]. }
  rewrite bv_wrap_spec_low by (cbn; lia).
  rewrite bytes_le_to_Z_spec' by lia. unfold sublist.
  destruct (Z.ltb_spec p (8 * k)).
  - assert (Ht : (Z.to_nat (p / 8) < Z.to_nat k)%nat).
    { apply Z2Nat.inj_lt; [apply Z.div_pos; lia|lia|]. apply Z.div_lt_upper_bound; lia. }
    rewrite nth_error_firstn_lt by exact Ht. rewrite nth_error_skipn'.
    destruct (nth_error (rl rho l) (Z.to_nat i + Z.to_nat (p / 8))) as [b|] eqn:E.
    + rewrite (nth_error_nth _ _ _ E). reflexivity.
    + rewrite (nth_overflow _ _ (proj1 (nth_error_None _ _) E)). cbn. rewrite Z.bits_0. reflexivity.
  - rewrite nth_error_firstn_ge; [reflexivity|].
    apply Nat2Z.inj_le. rewrite !Z2Nat.id by (try apply Z.div_pos; lia). apply Z.div_le_lower_bound; lia.
Qed.

Theorem byte_of_sound : ltac2:(tb__ "0|0|
S33S34S12S6S4dR2U8A2S3S11S6A1SbR4R3A2S10S6R2A2A3S7R6S35R6R5A2R4R3A4F_;F_;Fb;Ft;Fe;Frho;").
Proof.
  intros rho e. induction e; intros t b Ht Hb; try discriminate.
  -   cbn [byte_of] in Hb. inversion Hb; subst. intros j Hj. cbn [eval beval].
    rewrite testbit_u8 by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
    rewrite Z.mod_pow2_bits_low; [|lia]. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low; [|lia].
    rewrite Z.shiftr_spec; [|lia]. rewrite Z.mod_pow2_bits_low; [|lia]. f_equal. lia.
  -   destruct op; try discriminate; cbn [byte_of] in Hb.
    +   destruct e2 as [s| | | | | | |]; try discriminate.
      pose proof (land63 (s mod 2 ^ 64)) as Hs. set (s' := Z.land (s mod 2 ^ 64) 63) in *.
      destruct (s' mod 8 =? 0) eqn:E8; [|discriminate]. apply Z.eqb_eq in E8.
      intros j Hj. cbn [eval]. rewrite sll_unsigned. fold s'.
      rewrite bv_wrap_spec_low by (cbn; lia).
      destruct (Z.ltb_spec (Z.of_nat t) (s' / 8)).
      * inversion Hb; subst. rewrite Z.shiftl_spec_low by lia. cbn. rewrite Z.bits_0. reflexivity.
      * rewrite Z.shiftl_spec_high by lia.
        pose proof (IHe1 (t - Z.to_nat (s' / 8))%nat b ltac:(lia) Hb j Hj) as IH. rewrite <- IH. f_equal.
        rewrite Nat2Z.inj_sub by lia. rewrite Z2Nat.id by lia. lia.
    +   destruct e2 as [s| | | | | | |]; try discriminate.
      pose proof (land63 (s mod 2 ^ 64)) as Hs. set (s' := Z.land (s mod 2 ^ 64) 63) in *.
      destruct (s' mod 8 =? 0) eqn:E8; [|discriminate]. apply Z.eqb_eq in E8.
      intros j Hj. cbn [eval]. rewrite srl_unsigned. fold s'. rewrite Z.shiftr_spec by lia.
      destruct (Z.ltb_spec (Z.of_nat t + s' / 8) 8).
      * pose proof (IHe1 (t + Z.to_nat (s' / 8))%nat b ltac:(lia) Hb j Hj) as IH. rewrite <- IH. f_equal.
        rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia.
      * inversion Hb; subst. rewrite testbit_u64_high by lia. cbn. rewrite Z.bits_0. reflexivity.
    +   destruct (byte_of e1 t) as [x|] eqn:E1; [|discriminate].
      destruct (byte_of e2 t) as [y|] eqn:E2; [|discriminate].
      cbn [eval]. change (alu64 ALU_OR (eval rho e1) (eval rho e2)) with (bv_or (eval rho e1) (eval rho e2)).
      eapply bor_sound; [eapply IHe1; eauto | eapply IHe2; eauto | exact Hb].
  -   destruct op; try discriminate. cbn [byte_of] in Hb.
    destruct e2 as [s| | | | | | |]; try discriminate.
    pose proof (land31 ((s mod 2 ^ 64) mod 2 ^ 32)) as Hs. set (s' := Z.land ((s mod 2 ^ 64) mod 2 ^ 32) 31) in *.
    destruct ((s' mod 8 =? 0) && (Z.of_nat t <? 4))%bool eqn:E; [|discriminate].
    apply andb_prop in E as [E8 E4]. apply Z.eqb_eq in E8. apply Z.ltb_lt in E4.
    intros j Hj. cbn [eval]. rewrite srlw_testbit by lia. cbv zeta. fold s'.
    destruct (Z.ltb_spec (Z.of_nat t + s' / 8) 4).
    + pose proof (IHe1 (t + Z.to_nat (s' / 8))%nat b ltac:(lia) Hb j Hj) as IH.
      destruct (Z.ltb_spec (8 * Z.of_nat t + j + s') 32); [|lia].
      rewrite <- IH. f_equal. rewrite Nat2Z.inj_add, Z2Nat.id by lia. lia.
    + inversion Hb; subst. destruct (Z.ltb_spec (8 * Z.of_nat t + j + s') 32); [lia|].
      cbn. rewrite Z.bits_0. reflexivity.
  -   cbn [byte_of] in Hb.
    destruct ((8 * (Z.of_nat t + 1) <=? Z.of_N w) && (Z.of_N w <=? 64))%bool eqn:E.
    + apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
      intros j Hj. cbn [eval]. rewrite testbit_ext_low by lia. exact (IHe t b Ht Hb j Hj).
    + destruct (negb sgn && (Z.of_N w <=? 8 * Z.of_nat t) && (Z.of_N w <=? 64))%bool eqn:E'; [|discriminate].
      apply andb_prop in E' as [E' E3]. apply andb_prop in E' as [En E2]. apply Z.leb_le in E2.
      destruct sgn; [discriminate|]. inversion Hb; subst.
      intros j Hj. cbn [eval beval]. rewrite testbit_zext_high by lia. rewrite Z.bits_0. reflexivity.
  -   cbn [byte_of] in Hb.
    lazymatch goal with |- byte_ok _ (eval _ (SLBytes ?l ?i ?k)) _ _ => destruct i as [i0| | | | | | |]; try discriminate end. cbv zeta in Hb.
    set (i := i0 mod 2 ^ 64) in *.
    destruct ((0 <=? i) && (0 <=? k) && (k <=? 8))%bool eqn:E; [|discriminate].
    apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.leb_le in E3.
    inversion Hb; subst. intros j Hj. rewrite slbytes_testbit by lia. fold i.
    replace ((8 * Z.of_nat t + j) / 8) with (Z.of_nat t).
    2:{ symmetry. rewrite Z.mul_comm. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
    replace ((8 * Z.of_nat t + j) mod 8) with j.
    2:{ symmetry. rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
    destruct (Z.ltb_spec (Z.of_nat t) k).
    + destruct (Z.ltb_spec (8 * Z.of_nat t + j) (8 * k)); [|lia].
      cbn [beval]. f_equal. f_equal. f_equal. lia.
    + destruct (Z.ltb_spec (8 * Z.of_nat t + j) (8 * k)); [lia|].
      cbn [beval]. rewrite Z.bits_0. reflexivity.
Qed.

Fixpoint find_cover (cells : list cell) (pe : sv) (q : Z) : option (cell * Z) :=
  match cells with
  | [] => None
  | c :: rest =>
      match same_atoms (c_off c) pe with
      | Some dc => let d := snorm dc in
                   if (d <=? q) && (q <? d + c_width c) then Some (c, q - d) else find_cover rest pe q
      | None => find_cover rest pe q
      end
  end.

Fixpoint cells_bytes (cells : list cell) (pe : sv) (q : Z) (n : nat) : option (list bexp) :=
  match n with
  | O => Some []
  | S n' =>
      match find_cover cells pe q with
      | Some (c, t) =>
          match byte_of (c_val c) (Z.to_nat t), cells_bytes cells pe (q + 1) n' with
          | Some b, Some rest => Some (b :: rest)
          | _, _ => None
          end
      | None => None
      end
  end.

Lemma find_cover_spec : ltac2:(tb__ "0|2|
S14S32A1S34S0S32S0S3S11S17S32S0A2M0A1ScR5R4R3A3S10G0S16S32S0R2R1A4A2A3S5S0S0S4S54S32R4R7A3S4S3S11S0A1S5bS44R4A1R6A2S10S0R1A2A3S4S4S20S5cR1A1M1R5A2S24R5S22G1S46R4A1A2A2A2S3S0R3S31R5G1A2A3A2A2A2Ldc;A2F_;Ft;Fc;Fq;Fpe;Fcells;").
Proof.
  induction cells as [|x rest IH]; intros pe q c t H; cbn in H; [discriminate|].
  destruct (same_atoms (c_off x) pe) as [dc|] eqn:Es.
  - destruct ((snorm dc <=? q) && (q <? snorm dc + c_width x))%bool eqn:E.
    + inversion H; subst. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      exists dc. split; [left; reflexivity|]. split; [exact Es|]. lia.
    + destruct (IH pe q c t H) as (dc' & Hin & Hs & Hr & Ht). exists dc'. split; [right; exact Hin|]. auto.
  - destruct (IH pe q c t H) as (dc' & Hin & Hs & Hr & Ht). exists dc'. split; [right; exact Hin|]. auto.
Qed.

Lemma byte_ok_enc : ltac2:(tb__ "0|2|
S33S1cQ40A1S12S6S12S7R5R4R3R2A4S4dR4R2A2S4eR3U8A2S3S1cQ8M0A1M1S4bG1R6S3eR4R7A2S1dG0Z0A2A4S8R8R5A2A3F_;F_;F_;Fk;Fb;Ft;Fv;Frho;").
Proof.
  intros rho v t b k Hok Ht Hk. unfold enc_bytes. rewrite Z_to_le_bytes_nth by exact Ht.
  rewrite <- (Z_to_bv_bv_unsigned 8 (beval rho b)). apply Z_to_bv8_eq_bits. intros i Hi.
  rewrite Z.shiftr_spec by lia. rewrite <- (Hok i Hi). f_equal. lia.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma cell_byte_rd : ltac2:(tb__ "0|4|
S33S49S3aS1S32S34S0S0S6S39Vsegs;R9R8R7A4S3SfS3dR7R8A2S15A3S4S20S3cRbR9A2S36RbR6A2M0A2S20G0S3bRbR9A2A2A2S3S11S17S32S0A2M1A1ScS38RaA1R7R6A3S10G1S16S32S0R8R5A4A2A3S3S11S6A1SbS45R9A1S28R6A1A2S10S6R5A2A3S3S11S1cQ8A1M2A1S48RdS1dQ40M3S22S22S1bG3S35ReS37RcA1A2A2S36ReR9A2A2R8A2A2A2S10G2S8ReR6A2A2A3F_;F_;F_;F_;F_;Fb;Ft;Fq;Fpe;Fc;Fn;Fo;Fms;Frho;").
Proof using .
  intros rho ms o n c pe q t b Ho Hwf Hpe Hf Hb.
  destruct (find_cover_spec _ _ _ _ _ Hf) as (dc & Hin & Hsa & Hr & ->).
  pose proof Ho as (Hbnd & _ & Hcells & _ & _).
  destruct (obj_wf_cell _ _ _ Hwf Hin) as (C3 & C4 & _ & _).
  pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (C1 & C2 & Hc).
  unfold obj_lo_of, obj_hi_of in *.
  assert (E : soff rho (c_off c) = soff rho pe + snorm dc).
  { eapply soff_diff_lit; [exact Hsa | | | apply (proj2 (proj2 (proj2 Hbnd)))]; lia. }
  pose proof (rd_bytes_nth ms (Z.to_nat (c_width c)) _ _ (Z.to_nat (q - snorm dc)) Hc ltac:(lia)
                ltac:(rewrite oaddr_unsigned by lia; lia)) as R.
  rewrite oaddr_unsigned in R by lia.
  replace (bv_unsigned (eval rho (ob_base o)) + soff rho (c_off c) + Z.of_nat (Z.to_nat (q - snorm dc)))
    with (bv_unsigned (eval rho (ob_base o)) + soff rho pe + q) in R by lia.
  rewrite R. f_equal. eapply byte_ok_enc; [|lia|lia].
  apply byte_of_sound; [lia | exact Hb].
Qed.

Theorem cells_bytes_sound : ltac2:(tb__ "0|5|
S33S49S3aS1S34S0S12S14S6A1M0S39Vsegs;R8R7R6A4S3SfS3dR6R7A2S15A3S4S20S3cRaR8A2S36RaR6A2M1A2S20G1S3bRaR8A2A2A2S3S11G0A1S9S38R9A1R7R6R5A4S10G0R4A2A3S3S11S14S1cQ8A1M2A1M3A1S40RbS1dQ40M4S22S22S1bG4S35RcS37RaA1A2A2S36RcR8A2A2R7A2A2R6A3S10G3S4cS6G2S8RcA1R5A4A2A3F_;F_;F_;F_;Fbl;Fk;Fq;Fpe;Fn;Fo;Fms;Frho;").
Proof using .
  intros rho ms o n pe q k. revert q. induction k as [|k IH]; intros q bl Ho Hwf Hpe Hcb.
  - cbn in Hcb. inversion Hcb. reflexivity.
  - cbn [cells_bytes] in Hcb.
    destruct (find_cover (ob_cells o) pe q) as [[c t]|] eqn:Hf; [|discriminate].
    destruct (byte_of (c_val c) (Z.to_nat t)) as [b|] eqn:Hb; [|discriminate].
    destruct (cells_bytes (ob_cells o) pe (q + 1) k) as [rest|] eqn:Hrest; [|discriminate].
    inversion Hcb; subst. cbn [rd_bytes map].
    rewrite (cell_byte_rd rho ms o n c pe q t b Ho Hwf Hpe Hf Hb).
    destruct (find_cover_spec _ _ _ _ _ Hf) as (dc & Hin & Hsa & Hr & _).
    pose proof Ho as (Hbnd & _ & Hcells & _ & _).
    pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (C1 & C2 & _). unfold obj_lo_of, obj_hi_of in *.
    assert (E : soff rho (c_off c) = soff rho pe + snorm dc).
    { eapply soff_diff_lit; [exact Hsa | | | apply (proj2 (proj2 (proj2 Hbnd)))]; lia. }
    replace (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + soff rho pe + q) + 1)%bv
      with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + soff rho pe + (q + 1))).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
        change (bv_unsigned (1%bv : bv 64)) with 1. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    rewrite (IH (q + 1) rest Ho Hwf Hpe Hrest). reflexivity.
Qed.

Lemma cells_bytes_length : ltac2:(tb__ "0|1|
S14S32A1S34S0S12S14S6A1M0S3S11G0A1S9R5R4R3R2A4S10G0R1A2A3S3S12S1aS6R2A2R3A3F_;Fbl;Fk;Fq;Fpe;Fcells;").
Proof using .
  intros cells pe q k. revert q. induction k as [|k IH]; intros q bl H; cbn [cells_bytes] in H.
  - inversion H. reflexivity.
  - destruct (find_cover cells pe q) as [[c t]|]; [|discriminate]. destruct (byte_of _ _); [|discriminate].
    destruct (cells_bytes cells pe (q + 1) k) eqn:E; [|discriminate]. inversion H. cbn. f_equal. eapply IH. eauto.
Qed.

Lemma rd_bytes_read_aux : ltac2:(tb__ "0|0|
S49S1cQ40A1S12S3S11S14S1cQ8A1A1A1S57S4aR3A1R2R1A3S40R3R2R1A3A3Fk;Fa;Fms;").
Proof using .
  intros ms a k. revert a. induction k as [|k IH]; intros a; [reflexivity|].
  cbn [read_bytes_aux rd_bytes]. unfold rd. rewrite IH.
  destruct (ms_read_byte ms a); [|reflexivity]. destruct (rd_bytes ms (a + 1)%bv k); reflexivity.
Qed.

Lemma cells_read_bytes_map : ltac2:(tb__ "0|7|
S33S49S3aS1S34S0S12S14S6A1M0S1cQ40M1A1M2G2S39Vsegs;RaR9R8A4S3SfS3dR8R9A2S15A3S4S20S3cRcRaA2S36RcR8A2M3A2S20G3S3bRcRaA2A2A2S3S11G0A1S9S38RbA1R9R8R7A4S10G0R6A2A3S3S0S1bG1R6A2M4S22S22S1bG1S35ReS37RcA1A2A2S36ReRaA2A2R9A2A3S3S0G4S2bR9A1A3S3S11S14S1cQ8A1M5A1M6A1S58S4aRfA1R8R7A3S10G6S4cS6G5S8R10A1R9A4A2A3F_;F_;F_;F_;F_;F_;Flen;Fa;Fbl;Fk;Fq;Fpe;Fn;Fo;Fms;Frho;").
Proof using .
  intros rho ms o n pe q k bl a len Ho Hwf Hpe Hcb Ha Hlen.
  rewrite read_bytes_map_eq; unfold word_to_nat. rewrite rd_bytes_read_aux, Hlen, Nat2Z.id.
  replace a with (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + soff rho pe + q)) by (rewrite <- Ha; apply Z_to_bv_bv_unsigned).
  eapply cells_bytes_sound; eauto.
Qed.

Lemma le_word_enc8 : ltac2:(tb__ "0|1|
S1cQ40A1M0S3G0S56S3eU8R1A2A1R1A3Fw;").
Proof using .
  intros w. unfold le_bytes_to_word, enc_bytes. pose proof (urange w).
  rewrite bytes_le_to_Z_Z_to_le_bytes by lia. change (8 * Z.of_nat 8) with 64.
  rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma cell_read_u64 : ltac2:(tb__ "0|2|
S33S49S3aS34S34S1cQ40M0A1M1S39Vsegs;R6R5R4A4S54S32S47R4Z8R3A3S38R5A1A3S3S0S1bG0R3A2S22S1bG0S35R8S37R6A1A2A2S36R8R5A2A2A3S3S11G1A1S59S4aR8A1R4A2S10G1S35R9R5A2A2A3F_;F_;F_;Fa;Fv;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off v a Ho Hin Ha.
  pose proof Ho as (Hbnd & _ & Hcells & _ & _).
  pose proof (proj1 (Forall_forall _ _) Hcells _ Hin) as (C1 & C2 & Hc). cbn [c_off c_width c_val] in C1, C2, Hc.
  unfold read_u64; rewrite read_bytes_map_eq; unfold word_to_nat. rewrite rd_bytes_read_aux.
  change (Z.to_nat (bv_unsigned (Z_to_bv 64 8))) with 8%nat.
  replace a with (oaddr rho (ob_base o) (soff rho off)) by (unfold oaddr; rewrite <- Ha; apply Z_to_bv_bv_unsigned).
  change (Z.to_nat 8) with 8%nat in Hc. rewrite Hc. f_equal. apply le_word_enc8.
Qed.

End WithSegs.
