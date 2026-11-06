(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec FP Step.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Bi_fpkit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_fpkit2 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem6frm_ofC4ELinuxProcessSemantics5Riscv3Fpu>rmode_of_fieldK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics5Riscv3Sem9fp_formatK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics5Riscv3Sem5freadC4ELinuxProcessSemantics5Riscv3Fpu9fp_to_intC56Stdlib6ZArith6BinInt1Z3eqbC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics5Riscv7Prelude4sextC4ELinuxProcessSemantics5Riscv3Sem4c_pcC45stdpp9bitvector;definitions6bv_addC4ELinuxProcessSemantics5Riscv3Sem7with_pcC4ELinuxProcessSemantics5Riscv3Sem6accrueK4ELinuxProcessSemantics5Riscv3Sem3eff02C4ELinuxProcessSemantics5Riscv3Sem4fgetC4ELinuxProcessSemantics5Riscv3Sem7unbox_sI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init5Logic8eq_ind_rK4ELinuxProcessSemantics5Riscv5Instr5instr0QC4ELinuxProcessSemantics5Riscv3Sem4execc69OSSVerify5KrLib2K53A239Bi_fpkit28fcvt_w_sC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem4rsetK4ELinuxProcessSemantics5Riscv3Sem3eff01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv3Fpu6fflags00I4ELinuxProcessSemantics5Riscv3Sem3eff00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv3Fpu5rmode00K4ELinuxProcessSemantics5Riscv5Instr4ffmt01K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4bool00C4ELinuxProcessSemantics5Riscv3Fpu:fmt_singleK4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty01K4ELinuxProcessSemantics5Riscv5Instr7fcvt_ty05".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition fcvt_w_s (md : rmode) (a : word) : word :=
  sext 64 (Z_to_bv 32 (fst (fp_to_int fmt_single md true 32 (bv_unsigned (unbox_s a))))).
Lemma exec_fcvt_w_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_W FC_S rd rs1 rm) c =
  EDone (rset rd (fcvt_w_s md (fget c rs1)) (accrue (snd (fp_to_int fmt_single md true 32 (bv_unsigned (unbox_s (fget c rs1))))) (with_pc (c_pc c + sz) c))).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_fpkit2 ()) [] "p'0h01Hh11ch21fi001fh32mdi012mdh41oh51pi021ph62rdh72rmh83rs1h92szh:1zi031zi042fli051vi061xp;1p;2p;3p;5p;4p;6g0000j18Tg000Uj1>Tg0013j1ATg001Vj1@Tg002;R0j1YTg002]j27Tg003Gj1KTg0040j2=Tg004aj2ETg005Cj3DTg005]j1NTg006Ij1?Tg006gj3BTg007Oj5:Tg008;j2VTg008Xj24Tg009>j39Tg009ij15Tg00:Pj33Tg00;5j26Tg00;_j22Tg00<Hj1ITg00=0j2HTg00=Wj1FTg00>AR1j2STg00>aj4RTg00?Aj2QTg00?[j1CTg00@Dj2GTg00@dj2JTg00ABj6MTg00A`j5OTg00BLj3PTg00C3j2LTg00D1j3TTg00DXj1UTg00E@j3XTg00E]j3WTf2R2f1R3f0R43T#Up=0g00F:R5g00FXR6;X4p=;AW564p=<g00GCR7?D34p=1g00GkR8#8R9#8#8#8#8R:#8#>R;#AR<%@9R9#>#AR=%@8R8#>R>#Ag00HPg00I9R?%Y?R@17>2%K3'=1E?43DP@1E?3P0P?P7P4P1P5P6P7g00IcRA#NRBP4g00JNRC%?:RDf4REf6RF7BAD:f9RGg00JnP<1VDD%>:R:14:379;R<14;3n0100000020000RH%5Ff:RI53;/6F,24RJ30n2001106000120105104f3RK#5f7RL53;/6KRM#In10110600021010100g00KNRNP2PCPDf5RO,HK#F,7:D:RP#;,4:99:;%<P/2M50F'1X4@PNP3PCPD1H2ERN#F,7:D:R@1S56P1P5P6P1P5P6P7P4A0G<Jn2001106000120105104%;4,4:99:;%<4%5Ef8RJ53;/6ER<'250L'1P4P5P6P3P4CRRM#;,4:99:;%<M%5Lf;53;/6L'250I,Q7X26X:5P3P4O2n2001102000120103100b5P1P5P6P7PBP3PCPDAB2AED:124<90LHn2001106000120105104%;@,4:99:;%<@%52=3;F/62R@'2RL50OR<'1e17>KR>%C2,7:%?9R9'G%@8#?R8'J'=P4EMP0P?P7%C@,7:/G9/J8,=>P1P5P6P7PBP4PCPDABKAOD:%5O=3;G/6O,2490JHn2001106000120105104RJ%I@RHn10110600021010100/1<eP0P?P7%K@,=>PJPHn10110600021010100/1<eg00L;g00LiPOPEPKDO=PF2RF/1<e1L3N=0OL,1FeW0W3W1W7X8=W6W9o"). Qed.

Ltac fp_lit t :=
  lazymatch t with context [reg_get] => fail "fp_lit: open FP term" | _ => idtac end;
  let z := eval vm_compute in (bv_unsigned t) in
  let E := fresh "FPE" in
  assert (E : t = Z_to_bv 64 z) by (vm_compute; reflexivity);
  rewrite !E; clear E.

(* [comment removed for export] *)
Ltac exec_pre i ::=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fma ?op FMT_D ?rd ?rs1 ?rs2 ?rs3 ?rm => let H := rm_proof rm c in rewrite (exec_fma_d sz op rd rs1 rs2 rs3 rm c _ H)
    | Fma ?op FMT_S ?rd ?rs1 ?rs2 ?rs3 ?rm => let H := rm_proof rm c in rewrite (exec_fma_s sz op rd rs1 rs2 rs3 rm c _ H)
    | Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
    | Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
    | Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv zeta
    | Fcvt FC_W FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_s sz rd rs1 rm c _ H)
    | Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
    | Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
    | Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
    | Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
    | Csr ?op ?rd ?rs1 ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
            simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | CsrI ?op ?rd ?uimm ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv zeta;
            let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
            try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | _ => idtac
    end
  end;
  (* [comment removed for export] *)
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.
