(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
  MemSplit StartupAux ZStores.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_ClsTac () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib7CatExec6wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C49OSSVerify5KrLib7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC49OSSVerify5KrLib7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[export] Existing Instance fx0.

Ltac pin :=
  repeat match goal with
         | H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
         end.

Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

Ltac zlit :=
  repeat match goal with
         | |- context [Z_to_bv 64 ?z] =>
             lazymatch z with
             | Z0 => fail | Zpos _ => fail | Zneg _ => fail
             | _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
             end
         end.

Ltac len_rw :=
  repeat match goal with
         | |- context [length (word_to_le_bytes ?n ?v)] => rewrite (length_N_to_le_bytes n v)
         | |- context [length (zeros ?n)] => rewrite (length_zeros n)
         | |- context [length (repeat ?x ?n)] => rewrite (repeat_length x n)
         end.

Ltac region_side :=
  unfold win_lo;
  match goal with |- context [stack_max_size] => rewrite ?stack_max_size_val | _ => idtac end;
  len_rw;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

Ltac addr_norm :=
  gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

Ltac vclose_fin :=
  first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
        | apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
  gres; pin; imm_norm;
  first [ reflexivity
        | unfold v_addi, v_add; unorm; zlit; vclose_fin
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

Ltac with_mem_hidden tac :=
  lazymatch goal with
  | |- msteps _ (mkst _ _ ?m _) _ =>
      let M := fresh "MEMH" in set (M := m); tac (); subst M
  | |- _ => tac ()
  end.

Ltac sn F D := with_mem_hidden ltac:(fun _ => stepn F D; pin).
Ltac sv F D v := stepiv F D v vclose.

Ltac stepb_tk F D tac := with_mem_hidden ltac:(fun _ => WalkTac.stepb_tk F D tac).
Ltac stepb_ft F D tac := with_mem_hidden ltac:(fun _ => WalkTac.stepb_ft F D tac).

Ltac blit :=
  repeat match goal with
         | |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
             lazymatch z with
             | Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
             | Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
                         change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
             end
         end.

Ltac push_store :=
  blit;
  first [ rewrite wbytes_cmem_win by region_side
        | rewrite wbytes_cmem_data by region_side
        | idtac ].

Ltac stw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | vclose | vclose | reflexivity | oktac ]
    end
  | step_simpl; push_store ].

Ltac ok_sub Hok :=
  store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
  rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

Ltac ok_win HJ :=
  apply store_ok_cmem_win; [ repeat apply wfJ_wbytes; exact HJ | region_side | region_side ].

Ltac ok_data :=
  apply store_ok_cmem_data;
  lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

Ltac ld_step F D bsv vv rdtac valtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 true _ _ _, _) => eapply step_lh with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ2 false _ _ _, _) => eapply step_lhu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac | valtac ]
  | step_simpl ]; vnorm; pin.

Ltac lb_step F D bb rdtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac ]
  | step_simpl ]; vnorm; pin.

Lemma rdn_wbytes_out_Z : forall segs bs m (zb za : Z) n,
  (0 <= za < 2^64 /\ za + Z.of_nat n <= 2^64 /\ 0 <= zb < 2^64 /\
   zb + Z.of_nat (length bs) <= 2^64 /\
   (za + Z.of_nat n <= zb \/ zb + Z.of_nat (length bs) <= za))%Z ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
ltac2:(KReplay.run1 (kr_t_ClsTac ()) [] "h01Hh14__x1h22H0h32H1h42H2h57__arithh66__sat1h76__sat2h84cstrh95cstr0h:4__ffh;8__varmaph<5__with=4__x2h>1zh?2Hah@4__x3hA4__x4hB3HanhC2HbhD3HbnhE2HdhF2bshG1mhH1nhI4segshJ2zahK2zbp;1p;2p;3p;4p;7p;6p;9p;8g0000j1MTg000Pj1;Tg0015j1QTg001Sj1OTg0026j1WTg002Xj1RTg0036j2_Tg003Sj22Tg003oR0j2?Tg004Jj20Tg004fj24Tg005Lj3GTg006?j47Tg0070j3@Tg007Jj1:Tg007jj29Tg008Gj2LTg0091j2KTg009Qj1PTg00:6j2^Tg00:^j3]Tg00;Bj1\Tg00;bj2ATg00<@j1[Tg00<^j4JTg00=<j1ZTg00=Zj1YTg00>Ej2FTg00>hj3NTg00?Kj1XTg00@0j7jTg00@Tj1iTg00A6j2hTg00AXj2gTg00B2j2fTg00B^j3eTg00C=j4cTg00Coj2UTg00DRj3bTg00E5j4STg00E`j3TTg00FSj6HTg00G1l9aTg00Glj2VTg00HFj7dTg00Hjj8`Tg00INR1f0R2'0p=1f1R3%:2'9p=3f2R4,011232'?p=81K32#:,94p=6f3R5/041032'Vp=51?32,?4p==1043/?2p=B1943/02p=<1K32#:p=D1043/V2p=Cg00IlR6P3g00JJP2CSp=IP3g00K1R7g00KPR8P8g00L0R9P2g00LPFdp=>P5P7P8P8P9P4P3P2G`p=Eg00M0#Mg00MoR:#;R;#;R<#;R=#Q#OR>#MR?%;=#;#;R=#QR@#O%W>[g00NT%13RA%R;RB%R=R='_RC,23RD'?1332RE/0CA844CRFf4RG964>RH/0CPEP4PHP3C53=3=P0PF1343RFA855Cf5RH965>RE/0CPFP5PEP4C53=7BC%W?R?f7RE14@Gf6RF5GH14@5RIP4C7PEPHPIP4C73@P2A8GGC13HGRIA8FFCf8RJ96F>RK/0CPIPFPKPHC53=7BCP013FHRK/0CA8EECf9RI96E>RL/0CPKPEPLPFC53=f;RL14@Jf:RK5GI14@ERMPFC7PLPIPMPFC75@?P2%:E=<JCA8KKCf<RE96K>RM/0C13IJPKPMPIC53=P0A8LLCf=RM96L>RJ13KIPLPJPKC57BCf?RJ14@Ef>RN5GM14@LRLPKC7PJPMPLPKC75@?P2A8MMCf@RK96N>RL13MEPNPLPMC57BCP0fARL96J>RE/0C13NMPJPEPNC5fCRE14@KfBRO5GL14@JRJPNC7PEPLPJPNC75@?P21D>E=<LC13LKfDRK,D>=<OL7COfFR?fERJPK14@ERP14@ORQPLP6PO%:ORL,92RR14@K,L@RK1D>?RS=<K23CX>6P6PE19ELP2192SRSPEC5X>61K>JRK#PRT%:K#1RK%PORU%1LRL1^B=RV121B%1=121C[[RW%1BRXg00O3RYA]B=3UW?R=%1C\Y^?XRXP0fGRY#1RZ12YCR[13Y?R\fHR]fJR^96]>R_PYC5PIfI#1RY12^CR`P0%1^RaP`fKRb/3^R^fLRcfNRd96c>RePbC5PJ%1cRffM/2CRgg00OORh#\Ri%MhRhP6P61A6GP4%[6RjCJP31A65CJ%Z6Rk%Y6RlPlP7P8P8P91F6:R71F6;5N6R;%X:,F6R:'I,>l1F6<9N6:/I7,>lFjR:%i8R8P:CE1hl9R9P2P4g00P;R:g00P[R<'g1f24=@:<dAe613CcR<b:b;b<X16X=6X@6XA61923R:A<4527C41934RmA<5G37C5[^16^=6^@6^A6P2fR,D>R>fPR5%:dRdfORGPMO5b5W4W3P3P2O2n2001000000121000000W2W0P3P2O2n2001000000121000000b6b7b9b81L@PRPPTPKPUPLPVPWP=PXP0PZP[%1]PIP0PaP`PfPJPiPh1A63RMPkPl1U61/I7,>lR1P8P1CEP9P<b:b;b<X16R1%12PA[^16RAP2P5PFO2b5X4gX3fP3P2O2n2001000000120000000X2`X0YP3P2O2n2001000000120000000b6b7b9b8PTPKPUPLPVPWP=PXP0PZP[12]CPIP0PaP`12cCPJPiPhPMPkPlP6P7g00Q;1U6B=b6@RBCS,>lR7P8P7CEP9P<b:b;b<X16R7122CPD[^16RDP2P5PHO2b5X4gX3fP3P2O2n2001000000120000000X2`X0YP3P2O2n2001000000121000000b6b7b9b85TERHEH1L@QRQPTPKPUPLPVPWP=PXP0PZP[PZPIP0PaP`%1bPJP1PAP2PGP4O2b5X4gX3fP3P2O2n2001000000120000000X2`X0YP3P2O2n2001000000120000000b6b7b9b8PTPKPUPLPVPWP=PXP0PZP[P[PIP0PaP`12bCPJP7PDP2PGP3O2b5X4gX3fP3P2O2n2001000000120000000X2`X0YP3P2O2n2001000000121000000b6b7b9b85TORDEHP6PO10RCX>6PTPKPUPLPVPWP=PXP0PZP[10\CPIP0PaP`10^CPJPiPhP61A64P3PjCJPkPl1I;B,>lRlP8PlCEP9P<b:b;b<X16X=6R<10:C10mC[^16^=6RmP2PdPGP?O3b5X4gX3fP3P2O2n2001000000120000000X2`X0YP3P2O2n2001000000121000000b6b7b9b8PQPDEHP6PE10SCX>6PTPKPUPLPVPWP=PXP0PZP[10_CPIP0PaP`10eCPJP<PmP2P>P5PNO3b5X4gX3fP3P2O2n2001000000120000000X2`X0YP3P2O2n2001000000121000000b6b7b9b8PPPHEHM9aWEWDP3P2O2n2001000000121000000W0WCP3P2O2n2001000000121000000W0WBP3P2O2n2001000000121000000W0W?P3P2O2n2001000000121000000W0WHXJ6XK6WGWFWIo"). Qed.

Ltac len_simpl :=
  len_rw; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul Pos.add Pos.mul].

Ltac peel :=
  repeat first [ rewrite rdn_wbytes_out_Z by (len_simpl; lia)
               | rewrite rdn_wbytes_out by region_side ].

Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

Ltac rd_hit8 :=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; unorm; lia.

Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
  repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

Ltac incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
  eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
  cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

Ltac carry Hag H r T :=
  pose proof (Hag r ltac:(notin_list)) as T;
  repeat first [ rewrite getr_same in T by reg_neq_tac | rewrite getr_other in T by reg_neq_tac ];
  rewrite ?H in T.

Ltac ra_chain :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; ra_chain
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
          end ].

Definition bwd (segs : list Segment) (G : machine_state -> Prop) : Prop :=
  forall st st', msteps segs st st' -> G st' -> G st.

Ltac gsteps HG := eapply HG.
