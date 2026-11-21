(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (memset_summary, ms_entry_eq, memset_summary_lit and 1 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import MemsetLib.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanMemset_code AsanMemset1.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From Stdlib Require Import Zify.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanMemset () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib2AS8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib2AS8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib2AS5Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS5Hoare4at_0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib2AS9MemsetLib5cbyteC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatC59OSSVerify5KrLib2AS7CatExec6wbytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib2AS9MemsetLib5cfillC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib9cfill_nilC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib8ms_agreeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6eq_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00C59OSSVerify5KrLib2AS;AsanMemset17A_exit0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegI47Corelib4Init9Datatypes4list00I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib2AS;AsanMemset17A_exit2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset12L2C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InK47Corelib4Init5Logic2or01C46Stdlib5Lists4List4inclC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib2AS9MemsetLib@cfill_full_chainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset17A_exit6C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset12L6C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset17A_exit8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset12L8C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C59OSSVerify5KrLib2AS;AsanMemset16A_contC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib2AS9MemsetLib>neg_mod4_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib9negw_and3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_subwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec6v_andiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib2AS9MemsetLib7andi_m4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset16B_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset12LBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib>ms_agree_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset16B_contC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib3c32C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C59OSSVerify5KrLib2AS;AsanMemset16C_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset12LCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib=ms_agree_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset16C_contC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib<andi_4_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset16D_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset12LDC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib2AS;AsanMemset16D_contC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset15E_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib3c64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z8le_0_subC56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundC56Stdlib6ZArith4Znat5Z2Nat2idC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC59OSSVerify5KrLib2AS;AsanMemset18loop_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanMemset17ret_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS6CatSim6msteps00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib2AS9MemsetLib8ms_chainC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib2AS6CatSim<msteps_transC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01c59OSSVerify5KrLib2AS:AsanMemset>asanreflect_fxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgGTgt_huf_decompress_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib2AS;AsanMemset1>asanreflect_fxC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic5False00C59OSSVerify5KrLib2AS?AsanMemset_code7ms_baseC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C45stdpp9bitvector;definitions5bv_eqI47Corelib7Numbers7BinNums1N00c59OSSVerify5KrLib2AS:AsanMemset8ms_entryC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib2AS5Hoare6ret_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AsanMemset>memset_summaryC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2AS:AsanMemset;ms_entry_eqC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib2AS<RefMemcpyLib5keepsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MemsetLib>ms_agree_keepsC1?~~~~~~~~~~~~~~~".
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate; Zify.zify_post_hook; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
#[local] Ltac solve_incl :=
  let x := fresh "x" in let H := fresh "H" in
  intros x H; cbn [In] in H;
  repeat (destruct H as [<-|H]; [cbn [In]; repeat first [left; reflexivity | right] |]);
  destruct H.

Section Summary.
  Variable mem0 : word -> option byte.
  Variables d cv ret : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok MSEGS mem0 d (Z.to_nat n) = true.
  Hypothesis Hret : ret_ok ret.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).
  #[local] Abbreviation PC o := (Z_to_bv 64 (ms_base + o)).

  (* [comment removed for export] *)
  #[local] Ltac cover L' :=
    apply (cfill_full_chain mem0 d n (cbyte cv) Hn Hnw _ L');
    [ unfold L2, L6, L8, LB, LC, LD; solve_incl
    | cbn [ms_chain]; lia ].

  Theorem memset_summary : forall regs,
    getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = Z_to_bv 64 n -> getr regs 1 = ret ->
    exists regs',
      msteps MSEGS (mkst regs (Z_to_bv 64 ms_base) mem0 rom)
                   (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
      /\ getr regs' 10 = d /\ ms_agree regs regs'.
  Proof.
    intros regs H10 H11 H12 H1.
    pose proof (u64_range d) as Hd.
    rewrite <- (at_0 d) in H10.
    replace (Z_to_bv 64 ms_base) with (PC 0) by (f_equal; lia).
    replace (mkst regs (PC 0) mem0 rom) with (mkst regs (PC 0) (CF []) rom) by (rewrite cfill_nil; reflexivity).
    (* [comment removed for export] *)
    assert (FIN : forall regs' (M : word -> option byte),
              M = wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n)) ->
              msteps MSEGS (mkst regs (PC 0) (CF []) rom) (mkst regs' ret M rom) ->
              getr regs' 10 = at_ d 0 -> ms_agree regs regs' ->
              exists regs'',
                msteps MSEGS (mkst regs (PC 0) (CF []) rom)
                       (mkst regs'' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) rom)
                /\ getr regs'' 10 = d /\ ms_agree regs regs'').
    { intros regs' M -> RUN P10 AG. exists regs'. rewrite at_0 in P10. auto. }
    destruct (Z.lt_ge_cases n 9) as [Hsmall|Hn9].
    { (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      { destruct (A_exit0 mem0 d cv ret n rom Hn Hret regs H10 H11 H12 H1 Hz) as (r1 & RUN & P10 & AG).
        eapply (FIN r1); try eassumption.
        rewrite cfill_nil. rewrite Hz. reflexivity. }
      destruct (Z.lt_ge_cases n 3) as [H3|H3].
      { destruct (A_exit2 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
        eapply (FIN r1); try eassumption. cover ([(0,1); (n-1,1)]%Z). }
      destruct (Z.lt_ge_cases n 7) as [H7|H7].
      { destruct (A_exit6 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
        eapply (FIN r1); try eassumption. cover ([(0,1); (1,1); (2,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
      destruct (A_exit8 mem0 d cv ret n rom Hn Hnw Hok Hret regs H10 H11 H12 H1 ltac:(lia)) as (r1 & RUN & P10 & AG).
      eapply (FIN r1); try eassumption.
      cover ([(0,1); (1,1); (2,1); (3,1); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    (* [comment removed for export] *)
    destruct (A_cont mem0 d cv ret n rom Hn Hnw Hok regs H10 H11 H12 H1 Hn9)
      as (r1 & RUN1 & Q10 & Q11 & Q12 & Q13 & Q15 & Q1 & AG1).
    (* [comment removed for export] *)
    set (k := ((- bv_unsigned d) mod 4)%Z).
    pose proof (neg_mod4_range (bv_unsigned d)) as Hk. fold k in Hk.
    pose proof (negw_and3 d) as Hkv. fold k in Hkv.
    set (n1 := (n - k - (n - k) mod 4)%Z).
    set (m1 := ((n - k) / 4)%Z).
    pose proof (Z.div_mod (n - k) 4 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)) as Hmb.
    assert (Hm1 : (4 * m1 = n1)%Z) by (subst n1 m1; lia).
    assert (Hn1 : (n - k - 3 <= n1 <= n - k)%Z) by (subst n1; lia).
    pose proof (andi_m4 (n - k) ltac:(lia)) as Hn1v. fold n1 in Hn1v.
    clearbody n1 m1. clear Hdm Hmb.
    destruct (Z.lt_ge_cases n1 9) as [HB|HB].
    { (* [comment removed for export] *)
      destruct (B_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
        as (r2 & RUN2 & P10 & AG2).
      eapply (FIN r2); [| eapply msteps_trans; [exact RUN1 | exact RUN2] | exact P10 | eapply ms_agree_trans; eassumption].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+n1-4,4); (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    destruct (B_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 Hkv Hn1v r1 Q10 Q11 Q12 Q13 Q15 Q1 Hn9 HB)
      as (r2 & RUN2 & S10 & S11 & S12 & S13 & S14 & S1 & AG2).
    destruct (Z.lt_ge_cases n1 25) as [HC|HC].
    { destruct (C_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 ltac:(lia) HC)
        as (r3 & RUN3 & P10 & AG3).
      eapply (FIN r3); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]
                       | exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
              (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    destruct (C_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 r2 S10 S11 S12 S13 S14 S1 Hn9 HC)
      as (r3 & RUN3 & T10 & T11 & T12 & T13 & T14 & T1 & AG3).
    destruct (andi_4_cases (at_ d k)) as (s4 & Hs4v & Hs4).
    destruct (Z.lt_ge_cases (n1 - s4 - 24) 32) as [HD|HD].
    { destruct (D_exit mem0 d cv ret n rom Hnw Hok Hret k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
        as (r4 & RUN4 & P10 & AG4).
      eapply (FIN r4); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
                            eapply msteps_trans; [exact RUN3 | exact RUN4]]]
                       | exact P10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
      cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
              (k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
              (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z). }
    destruct (D_cont mem0 d cv ret n rom Hnw Hok k n1 Hk Hn1 s4 Hs4 Hs4v r3 T10 T11 T12 T13 T14 T1 Hn9 ltac:(lia) HD)
      as (r4 & RUN4 & U10 & U11 & U12 & U14 & U15 & U1 & AG4).
    destruct (E_run mem0 d cv ret n rom k n1 s4 Hs4 r4 (LD n k n1 s4) U10 U11 U12 U14 U15 U1 Hn9 ltac:(lia))
      as (r5 & RUN5 & V10 & V11 & V12 & V13 & V14 & V1 & AG5).
    (* [comment removed for export] *)
    set (r := (n1 - s4 - 24)%Z) in *.
    set (q := Z.to_nat (r / 32 - 1)).
    assert (Hq : (32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 1) + 32)%Z).
    { subst q. rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod r 32 ltac:(lia)). pose proof (Z.mod_pos_bound r 32 ltac:(lia)). lia. }
    destruct (loop_run mem0 d cv ret n rom Hnw Hok q r5 (LD n k n1 s4) (k + s4 + 24)%Z r
                V10 V11 V12 V13 V14 V1 ltac:(lia) ltac:(lia) Hq)
      as (r6 & RUN6 & W10 & W1 & AG6).
    destruct (ret_run ret rom Hret r6 (CF (((k + s4 + 24)%Z, (32 * (Z.of_nat q + 1))%Z) :: LD n k n1 s4)) W1)
      as (r7 & RUN7 & ->).
    eapply (FIN r6); [| eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 |
                          eapply msteps_trans; [exact RUN3 | eapply msteps_trans; [exact RUN4 |
                          eapply msteps_trans; [exact RUN5 | eapply msteps_trans; [exact RUN6 | exact RUN7]]]]]]
                     | exact W10 | repeat (eapply ms_agree_trans; [eassumption|]); first [assumption | apply ms_agree_refl]].
    cover ([(0,1); (1,1); (2,1); (3,1); (k,4); (k+4,4); (k+8,4); (k+12,4); (k+16,4); (k+20,4); (k+24,4);
            (k+s4+24, 32 * (Z.of_nat q + 1));
            (k+n1-28,4); (k+n1-24,4); (k+n1-20,4); (k+n1-16,4); (k+n1-12,4); (k+n1-8,4); (k+n1-4,4);
            (n-4,1); (n-3,1); (n-2,1); (n-1,1)]%Z).
  Qed.

End Summary.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_entry : word := ltac:(let l := word_lit (Z_to_bv 64 ms_base) in exact l).

Lemma ms_entry_eq : Z_to_bv 64 ms_base = ms_entry.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Corollary memset_summary_lit :
  ltac:(let T := type of memset_summary in
        let l := eval cbv delta [ms_entry] in ms_entry in
        lazymatch T with
        | context C [Z_to_bv 64 ms_base] => let T' := context C [l] in exact T'
        end).
Proof.
  pose proof memset_summary as H. rewrite ms_entry_eq in H. exact H.
Qed.

(* [comment removed for export] *)
Corollary memset_summary_w : forall (mem0 : word -> option byte) (d cv ret nw : word) (rom : word -> option byte) regs,
  (bv_unsigned d + bv_unsigned nw < 2 ^ 64)%Z ->
  store_ok MSEGS mem0 d (Z.to_nat (bv_unsigned nw)) = true ->
  ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = cv -> getr regs 12 = nw -> getr regs 1 = ret ->
  exists regs',
    msteps MSEGS (mkst regs ms_entry mem0 rom)
                 (mkst regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat (bv_unsigned nw)))) rom)
    /\ getr regs' 10 = d /\ ms_agree regs regs' /\ keeps regs regs'.
Proof.
  intros mem0 d cv ret nw rom regs Hnw Hok Hret H10 H11 H12 H1.
  pose proof (u64_range nw) as Hr.
  destruct (memset_summary mem0 d cv ret (bv_unsigned nw) rom ltac:(lia) Hnw Hok Hret regs H10 H11
              ltac:(rewrite Z_to_bv_bv_unsigned; exact H12) H1) as (regs' & RUN & P10 & AG).
  exists regs'. rewrite <- ms_entry_eq. repeat split; try assumption. apply ms_agree_keeps, AG.
Qed.
