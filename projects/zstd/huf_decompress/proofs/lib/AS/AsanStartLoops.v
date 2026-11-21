(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (12 recorded proofs replaced by written proofs (u_lit, v_addi_lit, btgt_lit and 9 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanStartLoops () := "C46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7bv_wrapI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib2AS>AsanStartLoops5u_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanStartLoops:v_addi_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4btgtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib2AS8PropExec4c_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums8positive01C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00C47Corelib4Init3Nat3addK45stdpp9bitvector;definitions2bv01I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib2AS8PropExec6regupdC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanStartLoops8env_postC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib2AS8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z7add_0_rK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib2AS7SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec7step_ldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec9step_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic9False_indC59OSSVerify5KrLib2AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib2AS5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Peano2ltC45stdpp9bitvector;definitions4BvWfK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib2AS8PropExec<c_eq_0_falseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_bne_tkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelc59OSSVerify5KrLib2AS>AsanStartLoops8btgt_litC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses3injI47Corelib4Init9Datatypes3nat00c59OSSVerify5KrLib2AS>AsanStartLoops>asanreflect_fxC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addc59OSSVerify5KrLib2AS>AsanStartLoops:signed12_0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z8inj_succC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib2AS>AsanStartLoops:signed12_8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c59OSSVerify5KrLib2AS>AsanStartLoops;signed13_m8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanStartLoops7cellrelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib2AS7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExec<wbytes_belowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExec<wbytes_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib2AS7CatExec7byte_atC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib2AS8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat5Nat2Z6inj_leC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib2AS7StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing5PExpr04c59OSSVerify5KrLib2AS>AsanStartLoops7pn_postC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanStartLoops:cellrel_rdC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec8step_lbuC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanStartLoops8c_eq_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7CatExec;byte_at_lenC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List9nth_skipnC56Stdlib5Arith8PeanoNat3Nat7add_0_rC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8app_nth1C59OSSVerify5KrLib2AS7CatExec>nth_lt_byte_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List6nth_InC46Stdlib5Lists4List;skipn_skipnc59OSSVerify5KrLib2AS>AsanStartLoops6byte_uC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepc59OSSVerify5KrLib2AS>AsanStartLoops>cellrel_wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpc59OSSVerify5KrLib2AS>AsanStartLoops:cellrel_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS7SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxc59OSSVerify5KrLib2AS>AsanStartLoops;signed12_m1C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c59OSSVerify5KrLib2AS>AsanStartLoops:signed12_1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS>AsanStartLoops<signed13_m12C1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. Qed.

Lemma v_addi_lit : forall a k, 0 <= a < 2 ^ 64 -> v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold v_addi. rewrite u_lit by lia. reflexivity. Qed.

Lemma btgt_lit : forall a k, 0 <= a < 2 ^ 64 -> btgt (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k Ha. unfold btgt. apply v_addi_lit. exact Ha. Qed.

Lemma c_eq_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.eqb a b.
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_lit by lia. reflexivity. Qed.

Lemma reg_neq : forall a b : Z, 0 <= a < 32 -> 0 <= b < 32 -> a <> b -> (Z_to_bv 5 a : reg) <> Z_to_bv 5 b.
Proof.
  intros a b Ha Hb Hne Heq. apply (f_equal bv_unsigned) in Heq.
  rewrite !Z_to_bv_unsigned in Heq. unfold bv_wrap in Heq. change (bv_modulus 5) with 32 in Heq.
  rewrite !Z.mod_small in Heq by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac rif :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?u else ?v] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let c := eval vm_compute in (bv_eqb a b) in
              lazymatch c with
              | true => change (if bv_eqb a b then u else v) with u
              | false => change (if bv_eqb a b then u else v) with v
              end
          end
      end
  end.

(* [comment removed for export] *)
Ltac pc_is v :=
  lazymatch goal with
  | |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
  end.

(* [comment removed for export] *)
Lemma signed12_0 : bv_signed (0 : bv 12) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) [] "p;2g00>Hj20Tg00Edg00FB'0o"). Qed.
Lemma signed12_1 : bv_signed (1 : bv 12) = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) [] "p;1p;2g002ej11Tg00>Hj20Tg00Edg00F`#1'0o"). Qed.
Lemma signed12_8 : bv_signed (8 : bv 12) = 8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) [] "p;1p;2g002@j10Tg002ej12Tg00>Hj21Tg00Edg00F`#0#0#0#2'1o"). Qed.
Lemma signed12_m1 : bv_signed (4095 : bv 12) = -1.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) [] "p;1p;2g00Snj11Tg00>Hj20Tg00Edg00F`#1'0o"). Qed.
Lemma signed13_m8 : bv_signed (8184 : bv 13) = -8.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) [] "p;1p;2g002@j10Tg00Snj12Tg00>Hj21Tg00Edg00F`#0#0#0#2'1o"). Qed.
Lemma signed13_m12 : bv_signed (8180 : bv 13) = -12.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanStartLoops ()) [] "p;1p;2g00Q[j13Tg002@j10Tg00Snj12Tg00>Hj21Tg00Edg00F`#3#0#0#2'1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EnvLoop.
  Variable SEGS : list Segment.
  Variable x : Z.
  Variables w1 w2 w3 : bv 32.
  Hypothesis Hx : 0 <= x /\ x + 12 < 2 ^ 64.
  Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 x) = Some w1.
  Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w2.
  Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w3.
  Hypothesis E1 : is_ecall w1 = false.
  Hypothesis E2 : is_ecall w2 = false.
  Hypothesis E3 : is_ecall w3 = false.
  Hypothesis D1 : decode_any w1 = Some (Load SZ8 true 10 9 0, 4%Z).
  Hypothesis D2 : decode_any w2 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
  Hypothesis D3 : decode_any w3 = Some (Branch BC_NE 10 0 8184, 4%Z).

  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Variable e : Z.
  Variable envc : nat.
  Variable ptr : nat -> word.
  Hypothesis He : 0 <= e /\ e + 8 * Z.of_nat envc + 16 < 2 ^ 64.
  Hypothesis Rk : forall k, (k < envc)%nat ->
    rdn SEGS M (Z_to_bv 64 (e + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (ptr k))
    /\ bv_unsigned (ptr k) <> 0.
  Hypothesis Rn : rdn SEGS M (Z_to_bv 64 (e + 8 * Z.of_nat envc)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Definition env_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 9 = Z_to_bv 64 (e + 8 * Z.of_nat envc + 8)
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ regs_agree (fun r => r = 9%bv \/ r = 10%bv) regs regs'.

  Lemma env_loop : forall n k regs,
    (k + n = envc)%nat ->
    getr regs 9 = Z_to_bv 64 (e + 8 * Z.of_nat k) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 12)) M rom)
      /\ env_post regs regs'.
  Proof.
    induction n as [|n IH]; intros k regs Hkn H9.
    - (* [comment removed for export] *)
      assert (k = envc) by lia. subst k.
      eexists. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (Z_to_bv 64 0) F1 E1 D1).
          - rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rn.
          - apply bytes_le_to_Z_8. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
        rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
        rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_ft SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
          rewrite getr_zero. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
      + split; [|split].
        * rewrite getr_same by reg_neq_tac. reflexivity.
        * rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac. reflexivity.
        * intros r Hr. rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
    - assert (Hk : (k < envc)%nat) by lia.
      destruct (Rk k Hk) as [Rd Hnz].
      destruct (IH (S k) (regupd (regupd regs 10 (ptr k)) 9 (Z_to_bv 64 (e + 8 * Z.of_nat (S k)))) ltac:(lia)) as [regs' [Hms Hpost]].
      { rewrite getr_same by reg_neq_tac. reflexivity. }
      exists regs'. split.
      + eapply mst_step; [reflexivity| |].
        { eapply (step_ld SEGS regs _ M rom w1 10 9 0 _ (ptr k) F1 E1 D1).
          - rewrite H9, signed12_0, v_addi_lit by lia. rewrite Z.add_0_r. exact Rd.
          - apply bytes_le_to_Z_8. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        eapply mst_step; [reflexivity| |].
        { eapply (step_addi SEGS _ _ M rom w2 9 9 8 F2 E2 D2). }
        rif. rewrite v_addi_lit by lia. pc_is (x + 8). rewrite signed12_8.
        rewrite getr_other by reg_neq_tac. rewrite H9, v_addi_lit by lia.
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_tk SEGS _ _ M rom w3 10 0 8184 F3 E3 D3).
          rewrite getr_other by reg_neq_tac. rewrite getr_same by reg_neq_tac.
          rewrite getr_zero. apply c_eq_0_false. exact Hnz. }
        rewrite signed13_m8, btgt_lit by lia. pc_is x.
        replace (e + 8 * Z.of_nat k + 8) with (e + 8 * Z.of_nat (S k)) by lia.
        exact Hms.
      + destruct Hpost as (P9 & P10 & Pag). split; [exact P9|]. split; [exact P10|].
        intros r Hr. rewrite (Pag r Hr). rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
  Qed.
End EnvLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PnLoop.
  Variable SEGS : list Segment.
  Variable x : Z.            (* [comment removed for export] *)
  Variables w0 w1 w2 w3 w4 : bv 32.
  Hypothesis Hx : 8 <= x /\ x + 12 < 2 ^ 64.
  Hypothesis F0 : fetch_word SEGS (Z_to_bv 64 (x - 8)) = Some w0.
  Hypothesis F1 : fetch_word SEGS (Z_to_bv 64 (x - 4)) = Some w1.
  Hypothesis F2 : fetch_word SEGS (Z_to_bv 64 x) = Some w2.
  Hypothesis F3 : fetch_word SEGS (Z_to_bv 64 (x + 4)) = Some w3.
  Hypothesis F4 : fetch_word SEGS (Z_to_bv 64 (x + 8)) = Some w4.
  Hypothesis E0 : is_ecall w0 = false.
  Hypothesis E1 : is_ecall w1 = false.
  Hypothesis E2 : is_ecall w2 = false.
  Hypothesis E3 : is_ecall w3 = false.
  Hypothesis E4 : is_ecall w4 = false.
  Hypothesis D0 : decode_any w0 = Some (Store SZ8 10 11 0, 4%Z).
  Hypothesis D1 : decode_any w1 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis D2 : decode_any w2 = Some (Load SZ1 false 13 11 4095, 4%Z).
  Hypothesis D3 : decode_any w3 = Some (Branch BC_EQ 13 12 8180, 4%Z).
  Hypothesis D4 : decode_any w4 = Some (Branch BC_NE 13 0 8180, 4%Z).

  Variable M0 : word -> option byte.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Variable p pn : Z.
  Variable s : list byte.
  Hypothesis Hp : 0 <= p /\ p + 8 <= 2 ^ 64.
  Hypothesis Hpn : 0 <= pn /\ pn + Z.of_nat (length s) + 2 < 2 ^ 64.
  Hypothesis Hapart : p + 8 <= pn \/ pn + Z.of_nat (length s) + 1 <= p.
  Hypothesis Hnz : ~ In (Z_to_bv 8 0) s.
  Hypothesis Hrd : forall j, (j <= length s)%nat ->
    rdn SEGS M0 (Z_to_bv 64 (pn + Z.of_nat j)) 1 = Some [byte_at s j].
  Hypothesis Hst : store_ok SEGS M0 (Z_to_bv 64 p) 8 = true.

  (* [comment removed for export] *)
  Definition cellrel (M : word -> option byte) : Prop :=
    (forall a : word, bv_unsigned a < p \/ p + 8 <= bv_unsigned a -> M a = M0 a) /\ mem_grows M0 M.

  Lemma cellrel_refl : cellrel M0.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma cellrel_wbytes : forall M (v : word), cellrel M -> cellrel (wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 v)).
  Proof.
    intros M v [H1 H2]. split.
    - intros a Ha. rewrite <- (H1 a Ha).
      destruct Ha as [Ha|Ha].
      + apply wbytes_below; rewrite ?length_N_to_le_bytes, u_lit by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
      + apply wbytes_above. rewrite length_N_to_le_bytes, u_lit by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - eapply mem_grows_trans; [exact H2 | apply wbytes_grows].
  Qed.

  Lemma cellrel_rd : forall M j, cellrel M -> (j <= length s)%nat ->
    rdn SEGS M (Z_to_bv 64 (pn + Z.of_nat j)) 1 = Some [byte_at s j].
  Proof.
    intros M j [H1 _] Hj. rewrite <- (Hrd j Hj). apply rdn_ext.
    - rewrite u_lit by lia. change (Z.of_nat 1) with 1. lia.
    - intros y Hy. rewrite u_lit in Hy by lia. change (Z.of_nat 1) with 1 in Hy. apply H1. lia.
  Qed.

  Lemma cellrel_st : forall M, cellrel M -> store_ok SEGS M (Z_to_bv 64 p) 8 = true.
  Proof. intros M [_ H2]. eapply store_ok_mono; [exact H2 | exact Hst]. Qed.

  Definition pn_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 11 = Z_to_bv 64 (pn + Z.of_nat (length s) + 1)
    /\ getr regs' 13 = Z_to_bv 64 0
    /\ regs_agree (fun r => r = 11%bv \/ r = 13%bv) regs regs'.

  Lemma byte_u : forall b : byte, 0 <= bv_unsigned b < 256.
  Proof. intros b. pose proof (u8_range b). lia. Qed.

  Lemma pn_loop : forall l2 j regs M,
    skipn j s = l2 -> (j <= length s)%nat ->
    getr regs 10 = Z_to_bv 64 p ->
    getr regs 11 = Z_to_bv 64 (pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    cellrel M ->
    exists regs' M',
      msteps SEGS (mkst regs (Z_to_bv 64 x) M rom) (mkst regs' (Z_to_bv 64 (x + 12)) M' rom)
      /\ pn_post regs regs' /\ cellrel M'.
  Proof.
    induction l2 as [|b l2 IH]; intros j regs M Hskip Hj H10 H11 H12 HM.
    - (* [comment removed for export] *)
      assert (Hjl : j = length s).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      subst j.
      exists (regupd regs 13 (Z_to_bv 64 (bv_unsigned (byte_at s (length s))))), M. split; [|split; [|exact HM]].
      + eapply mst_step; [reflexivity| |].
        { eapply (step_lbu SEGS regs _ M rom w2 13 11 4095 (byte_at s (length s)) F2 E2 D2).
          rewrite H11, signed12_m1, v_addi_lit by lia.
          replace (pn + Z.of_nat (length s) + 1 + -1) with (pn + Z.of_nat (length s)) by lia.
          apply cellrel_rd; [exact HM | lia]. }
        rif. rewrite v_addi_lit by lia. pc_is (x + 4).
        rewrite byte_at_len. change (bv_unsigned (Z_to_bv 8 0)) with 0.
        eapply mst_step; [reflexivity| |].
        { eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
          rewrite getr_same by reg_neq_tac. rewrite getr_other by reg_neq_tac.
          rewrite H12. rewrite c_eq_lit by lia. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 8).
        eapply mst_step; [reflexivity| |].
        { eapply (step_bne_ft SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
          rewrite getr_same by reg_neq_tac. rewrite getr_zero. rewrite c_eq_lit by lia. reflexivity. }
        rewrite v_addi_lit by lia. pc_is (x + 12). apply mst_refl.
      + split; [|split].
        * rewrite getr_other by reg_neq_tac. exact H11.
        * rewrite getr_same by reg_neq_tac. rewrite byte_at_len. reflexivity.
        * intros r Hr. rewrite getr_other; [reflexivity|]. intros ->. apply Hr. auto.
    - assert (Hjlt : (j < length s)%nat).
      { pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
      assert (Hb : byte_at s j = b).
      { unfold byte_at. rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
      assert (Hbnz : bv_unsigned b <> 0).
      { intros Hb0. apply Hnz. rewrite <- Hb in Hb0. rewrite nth_lt_byte_at in Hb0 by lia.
        replace (Z_to_bv 8 0) with (nth j s (Z_to_bv 8 0)); [apply nth_In; lia|].
        apply bv_eq. rewrite Hb0. reflexivity. }
      assert (Hskip' : skipn (S j) s = l2).
      { replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
      pose proof (byte_u b) as Hbu.
      (* [comment removed for export] *)
      set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned b))).
      assert (S1 : RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 x) M rom) = MachineOk (mkst regs1 (Z_to_bv 64 (x + 4)) M rom)).
      { erewrite (step_lbu SEGS regs _ M rom w2 13 11 4095 b F2 E2 D2).
        - rif. rewrite v_addi_lit by lia. reflexivity.
        - rewrite H11, signed12_m1, v_addi_lit by lia.
          replace (pn + Z.of_nat j + 1 + -1) with (pn + Z.of_nat j) by lia. rewrite <- Hb.
          apply cellrel_rd; [exact HM | lia]. }
      assert (G13 : getr regs1 13 = Z_to_bv 64 (bv_unsigned b)) by (unfold regs1; rewrite getr_same by reg_neq_tac; reflexivity).
      assert (G10 : getr regs1 10 = Z_to_bv 64 p) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H10).
      assert (G11 : getr regs1 11 = Z_to_bv 64 (pn + Z.of_nat j + 1)) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H11).
      assert (G12 : getr regs1 12 = Z_to_bv 64 47) by (unfold regs1; rewrite getr_other by reg_neq_tac; exact H12).
      destruct (Z.eqb (bv_unsigned b) 47) eqn:Eb.
      + (* [comment removed for export] *)
        set (M1 := wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 (pn + Z.of_nat j + 1)))).
        set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
        assert (HM1 : cellrel M1) by (unfold M1; apply cellrel_wbytes; exact HM).
        destruct (IH (S j) regs2 M1 Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
        { unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
        { exact HM1. }
        exists regs', M'. split; [|split; [|exact HM']].
        * eapply mst_step; [reflexivity | exact S1 |].
          eapply mst_step; [reflexivity| |].
          { eapply (step_beq_tk SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
            rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
          rewrite signed13_m12, btgt_lit by lia. pc_is (x - 8).
          eapply mst_step; [reflexivity| |].
          { eapply (step_sd_at SEGS regs1 _ M rom w0 10 11 0 (Z_to_bv 64 p) _ F0 E0 D0).
            - rewrite G10, signed12_0, v_addi_lit by lia. f_equal. lia.
            - exact G11.
            - apply cellrel_st. exact HM. }
          fold M1. rewrite v_addi_lit by lia. pc_is (x - 4).
          eapply mst_step; [reflexivity| |].
          { eapply (step_addi SEGS regs1 _ M1 rom w1 11 11 1 F1 E1 D1). }
          rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
          replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
          exact Hms.
        * destruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
          intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
          rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
      + (* [comment removed for export] *)
        set (regs2 := regupd regs1 11 (Z_to_bv 64 (pn + Z.of_nat (S j) + 1))).
        destruct (IH (S j) regs2 M Hskip' ltac:(lia)) as (regs' & M' & Hms & Hpost & HM').
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G10. }
        { unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity. }
        { unfold regs2. rewrite getr_other by reg_neq_tac. exact G12. }
        { exact HM. }
        exists regs', M'. split; [|split; [|exact HM']].
        * eapply mst_step; [reflexivity | exact S1 |].
          eapply mst_step; [reflexivity| |].
          { eapply (step_beq_ft SEGS _ _ M rom w3 13 12 8180 F3 E3 D3).
            rewrite G13, G12. rewrite c_eq_lit by lia. exact Eb. }
          rewrite v_addi_lit by lia. pc_is (x + 8).
          eapply mst_step; [reflexivity| |].
          { eapply (step_bne_tk SEGS _ _ M rom w4 13 0 8180 F4 E4 D4).
            rewrite G13, getr_zero. apply c_eq_0_false. rewrite u_lit by lia. exact Hbnz. }
          rewrite signed13_m12, btgt_lit by lia. pc_is (x - 4).
          eapply mst_step; [reflexivity| |].
          { eapply (step_addi SEGS regs1 _ M rom w1 11 11 1 F1 E1 D1). }
          rif. rewrite G11, signed12_1, !v_addi_lit by lia. pc_is x.
          replace (pn + Z.of_nat j + 1 + 1) with (pn + Z.of_nat (S j) + 1) by lia.
          exact Hms.
        * destruct Hpost as (P11 & P13 & Pag). split; [exact P11|]. split; [exact P13|].
          intros r Hr. rewrite (Pag r Hr). unfold regs2, regs1.
          rewrite !getr_other; [reflexivity| |]; intros ->; apply Hr; auto.
  Qed.
End PnLoop.
