(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import SumsLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import Sums_code.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import PropExec.
Ltac2 kr_t_AsanIMemcpy () := "C69OSSVerify5KrLib2K52AS7SumsLib7code_atC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K52AS5Hoare3at_C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC69OSSVerify5KrLib2K52AS5Hoare6ret_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2K52AS7SumsLib4memkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC69OSSVerify5KrLib2K52AS5Hoare:regs_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K52AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K52AS7SumsLib2b_C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K52AS8PropExec6regupdC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib2K52AS8PropExec6v_addiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K52AS7SumsLib6mc_lbuC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC69OSSVerify5KrLib2K52AS8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec9getr_sameC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7SumsLib8sb_val_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7SumsLib5mc_sbC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC69OSSVerify5KrLib2K52AS8PropExec4c_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr07C69OSSVerify5KrLib2K52AS7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52AS6CatSim6msteps01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK69OSSVerify5KrLib2K52AS6CatSim6msteps02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS5Hoare7at_addiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K52AS5Hoare?regs_agree_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS5Hoare>regs_agree_updC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC69OSSVerify5KrLib2K52AS8PropExec4btgtC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K52AS8PropExec;step_bne_tkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS5Hoare@regs_agree_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS<RefMemcpyLib:runs_transC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K52AS8PropExec4mkstC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K52AS8PropExec9step_addiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib2K55ASB02;AsanIMemcpy>asanreflect_fxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7SumsLib>asanreflect_fxC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C69OSSVerify5KrLib2K55ASB029Sums_code7W_6f670C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7D_6f670C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7W_6f674C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7D_6f674C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib2K55ASB02;AsanIMemcpy=imemcpy_wordsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K55ASB029Sums_code7W_6f65cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7W_6f660C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7W_6f664C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7W_6f668C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7W_6f66cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7W_6f678C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7W_6f67cC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00c69OSSVerify5KrLib2K55ASB02;AsanIMemcpy<imemcpy_clobC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7D_6f668C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7D_6f66cC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums8positive00C69OSSVerify5KrLib2K55ASB029Sums_code7D_6f678C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7D_6f67cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C69OSSVerify5KrLib2K52AS7SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec5v_addC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7SumsLib8v_add_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7SeqExec;step_add_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS5Hoare4at_0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib2K55ASB02;AsanIMemcpy<imemcpy_loopC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS7SumsLib6memk_nC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC69OSSVerify5KrLib2K55ASB029Sums_code7D_6f65cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7D_6f660C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB029Sums_code7D_6f664C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relC35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1C59OSSVerify5KrImgITgt_bilateral_fuzzer_both1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02;AsanIMemcpyBasan_imemcpy_entryC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K52AS7SumsLib4cpyH00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02;AsanIMemcpy;imemcpy_runC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02;AsanIMemcpyAasan_imemcpy_codeC1?~~~~~~~~~~~~~~~".  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition imemcpy_words : list (bv 32) :=
  [W_6f65c; W_6f660; W_6f664; W_6f668; W_6f66c; W_6f670; W_6f674; W_6f678; W_6f67c].

(* [comment removed for export] *)
Definition imemcpy_clob : list reg := [11; 12; 13; 14].

Section IMEMCPY.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 imemcpy_words.
  Hypothesis HOK : cpyH segs mem0 dst src n bs.

  #[local] Abbreviation MK := (memk mem0 dst bs).
  #[local] Abbreviation B := (b_ bs).
  #[local] Abbreviation CL := (fun r => In r imemcpy_clob).
  Let Hn0 : (0 <= n)%Z := cHn _ _ _ _ _ _ HOK.
  Let Hnws : (bv_unsigned src + n < 2 ^ 64)%Z := cHnws _ _ _ _ _ _ HOK.
  Let Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z := cHnwd _ _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemcpy_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply (mc_lbu _ _ _ _ _ _ HOK) with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
      | step_simpl]; vn.
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply (mc_sb _ _ _ _ _ _ HOK) with (k := kk);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
        | gres; rwH; reflexivity | apply sb_val_b | lia | lia]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Lemma imemcpy_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = at_ dst n ->
    (0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 12) (MK k) rom) (mkst regs' ret (MK n) rom)
      /\ regs_agree CL regs regs'.
Proof.
    get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - 
      eexists. split.
      + mlbu C12 D_6f668 k.                       
        msb C16 D_6f66c k.                        
        an C20 D_6f670.                           
        an C24 D_6f674.                           
        ab_ft C28 D_6f678 ltac:(condz).           
        aret C32 D_6f67c ret.
        replace (k + 1)%Z with n by lia. apply mst_refl.
      + unfold imemcpy_clob. solve_regs_agree.
    - 
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C12 D_6f668 k.
          msb C16 D_6f66c k.
          an C20 D_6f670.
          an C24 D_6f674.
          ab_tk C28 D_6f678 ltac:(condz).         
          apply mst_refl.
        * post. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  Theorem imemcpy_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ regs_agree CL regs regs'.
Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
    rewrite <- (memk_n _ _ _ _ _ _ HOK). change mem0 with (MK 0).
    destruct (Z.eq_dec n 0) as [Hz|Hnz].
    - 
      eexists. split.
      + ab_tk C0 D_6f65c ltac:(condz).            
        aret C32 D_6f67c ret.
        rewrite Hz. apply mst_refl.
      + apply regs_agree_refl.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 12) (MK 0) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
                         /\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_ft C0 D_6f65c ltac:(condz).          
          av C4 D_6f660 (at_ dst n) ltac:(apply v_add_at; lia).  
          an C8 D_6f664.                          
          apply mst_refl.
        * post; rewrite ?at_0; try reflexivity. unfold imemcpy_clob. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (imemcpy_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMCPY.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.leptonica.bilateral_fuzzer.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition asan_imemcpy_entry : word := 0x79970.

Lemma asan_imemcpy_code :
  code_at AsanUbsan.M.loaded_segments asan_imemcpy_entry 0 imemcpy_words.
Proof. unfold imemcpy_words. code_at_vm. Qed.

Theorem asan_imemcpy : forall mem0 (dst src : word) n bs rom regs (ret : word),
  cpyH AsanUbsan.M.loaded_segments mem0 dst src n bs ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs asan_imemcpy_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
    /\ regs_agree (fun r => In r imemcpy_clob) regs regs'.
Proof.
  intros mem0 dst src n bs rom regs ret HOK.
  rewrite <- (at_0 asan_imemcpy_entry).
  apply (imemcpy_run _ _ mem0 dst src n bs rom asan_imemcpy_code HOK).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
