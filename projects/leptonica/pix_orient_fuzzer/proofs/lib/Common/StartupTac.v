(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Export
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim
  MemSplit StartupAux ZStores.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_StartupTac () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init9Datatypes3orbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6leb_leC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib6Common7StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2or00C46Stdlib4Bool4Bool8orb_propK46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Common7CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_ltI59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6CatSim<msteps_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common:StartupTac3bwdC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac pin :=
  repeat match goal with
         | H : getr ?rs ?r = _ |- context [getr ?rs ?r] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with
             | context [Z_to_bv 64 _] => fail
             | _ => rewrite (u_Z2bv z) by lia
             end
         end.

(* [comment removed for export] *)
Ltac zlit :=
  repeat match goal with
         | |- context [Z_to_bv 64 ?z] =>
             lazymatch z with
             | Z0 => fail | Zpos _ => fail | Zneg _ => fail
             | _ => check_closed_term z; let z' := eval vm_compute in z in change z with z'
             end
         end.

(* [comment removed for export] *)
Ltac region_side :=
  unfold win_lo; rewrite ?stack_max_size_val, ?length_N_to_le_bytes, ?length_zeros, ?repeat_length;
  cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add Nat.mul]; imm_norm; unorm; lia.

(* [comment removed for export] *)
Ltac addr_norm :=
  gres; pin; imm_norm; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; zlit.

(* [comment removed for export] *)
Ltac vclose_fin :=
  first [ reflexivity | f_equal; lia | apply at_self | symmetry; apply at_self
        | apply Z_to_bv_u_eq; lia | apply Z_to_bv_u_eq_sym; lia | bveq ].
Ltac vclose :=
  gres; pin; imm_norm;
  first [ reflexivity
        | unfold v_addi, v_add; unorm; zlit; vclose_fin
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; first [ reflexivity | vclose_fin ]
        | rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; unfold v_addi, v_add; unorm; zlit; vclose_fin ].

(* [comment removed for export] *)
Ltac sn F D := stepn F D; pin.
Ltac sv F D v := stepiv F D v vclose.

(* [comment removed for export] *)
Ltac blit :=
  repeat match goal with
         | |- context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] =>
             lazymatch z with
             | Z0 => change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 0)
             | Zpos _ => let z' := eval vm_compute in (z mod 256)%Z in
                         change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 z')
             end
         end.

(* [comment removed for export] *)
Ltac push_store :=
  blit;
  first [ rewrite wbytes_cmem_win by region_side
        | rewrite wbytes_cmem_data by region_side
        | idtac ].

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac ok_sub Hok :=
  store_ok_peel; eapply store_ok_sub; [ | exact Hok | | ];
  rewrite ?length_N_to_le_bytes, ?length_zeros; unorm; lia.

(* [comment removed for export] *)
Ltac ok_win HJ :=
  apply store_ok_cmem_win; [ repeat apply wfJ_wbytes; exact HJ | region_side | region_side ].

(* [comment removed for export] *)
Ltac ok_data :=
  apply store_ok_cmem_data;
  lazymatch goal with |- ?g => check_closed_term g; vm_compute; reflexivity end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac lb_step F D bb rdtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) => eapply step_lbu with (b := bb)
    | decode_any _ = Some (Load SZ1 true _ _ _, _) => eapply step_lb with (b := bb)
    end;
    [ exact F | reflexivity | exact D | addr_norm; rdtac ]
  | step_simpl ]; vnorm; pin.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_wbytes_out_off : forall segs bs m (s k k' : Z) (n : nat),
  (2^33 <= s)%Z -> (s <= 2^63)%Z ->
  ((0 <=? k')%Z && (k' <=? 2^32)%Z && (0 <=? k)%Z && (k <=? 2^32)%Z && (Z.of_nat (length bs) <=? 2^32)%Z &&
   (Z.of_nat n <=? 2^32)%Z && ((k' + Z.of_nat n <=? k)%Z || (k + Z.of_nat (length bs) <=? k')%Z))%bool = true ->
  rdn segs (wbytes m (Z_to_bv 64 (s - k')) bs) (Z_to_bv 64 (s - k)) n = rdn segs m (Z_to_bv 64 (s - k)) n.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupTac ()) [] "h02Hbh11Hh24__x1h34__x2h42Hah57__arithh67__sat10h77__sat11h87__sat12h96__sat7h:6__sat8h;6__sat9h<4cstrh=5cstr0h>4__x3h?4__x4h@4__ffhA8__varmaphB5__withC7__sat13hD7__sat14hE1zhF1mhG1nhH2H0hI2H1hJ2H2hK2H3hL2H4hM2H5hN2H6hO3HorhP2E1hQ2E2hR3Hs1hS3Hs2hT2bshU1khV2k'hW1shX4segsp%0p;1p;2p;3p;4p;6p;9p;7p;8g0000j1^Tg000Pj1LTg0015j1TTg001Sj1cTg0026j1jTg002Xj1QTg0036j1KTg003[j2[Tg0048j23Tg004Tj20Tg0051j14Tg005Qj2ZTg005nj2BTg006Lj3ITg006oR0j2JTg007Jj3MTg008Dj49Tg009<j3<Tg009Vj2>Tg00:6j2kTg00:Vj26Tg00;3j1DTg00;Xj2WTg00<@j2HTg00<\j3VTg00=@j1UTg00=_j2NTg00>Hj3OTg00?1j2bTg00?]j1{Tg00@=j3aTg00@]j2`Tg00A;j1zTg00AYj4_Tg00B7j1yTg00BUj1xTg00C@j2]Tg00Ccj2hTg00DFj3\Tg00Dij1vTg00EKj3gTg00Enj2uTg00FPj2tTg00Fjj2sTg00GVj3rTg00H5j4qTg00Hgj4fTg00IRj3eTg00JLj2RTg00K2j2STg00K\j2@Tg00L9S00j2XTg00LSj3oTg00Loj3dTg00MRj3nTg00Mlj3mTg00NFj6YTg00Ndl9lTg00Ofj7iTg00PJj8wTg00PnR1f1R2'0f0R3'Bp=P1013p=2f2R4/B2/B3p=E1>23#4p=;f3R51042'B/B3p=F1@42/03p=Ag00QLR61B23g00QlR73<p==A<637p=51623,R4p=8%42/03p=G1023=<67p=71313p=1P4g00RLR8g00RkR9P9g00SKR:g00SkR;P2g00TIP3Cfg00U0R<Fip=?P5P8P9P9P:P4P2P3Gwp=:P2P8P9P9P:P3P<Fip=p1@42/33p=Cg00UP#^g00VOR<#LR8#LS01#LR=#T#cR>#^R?%L=R=#LR@#LRA#TRB#c%j>[g00W4%Q8RC%K=R=#QRD'[RE/35f4RF%K<S02#K#K#K#KRG#QRH,[CRI'3%Q@RJ,[CRK,05,P5%2FRL10FKRM3Ef7RN,;>ROPK%44RP/0KCFAA5PFAAFO5'Z'=1BLMf5RM#2RL10MKRO3Ef8RP,;>RQPK%45RR/0KCFRSAAFRMAAMQF'ZRQ;I3%5S%5Q'JP0f6RQ#29ELOPQPKf9RO,;>RL/0KCF%4FRS/0K'=AAMSQAAQLM'Z#5%j?R?f;RLA8BPQf:RS5MOA8BPNRRPMC9PLPOPRPMC93<P3%2NPNPK%2PCFPPPK1>>L/GKCF1GQK'=%4N=APOf<RN,;>=AOP'Z#5%2OPOPK%2SRRCF10SKRTf=RU,>>/GK3ERV1GPKRP;I2%5V%5P'JP01BRT%2L10LK3Ef>RT,>>/GK'=%4O/7Kf@RRA8BULf?RL5MTA8BUNRPPSC9PRPTPPPSC95<?P310NK,PN%2U10UK3E1>>R/GK'=%4N/7K10TK,PT%2LRT10LKRN3ERPfBRV,>>/GKRW;I2%5P%5W'JP0%2R9ETN10RK'=fCRN,;>/7KfERTA8BVRfDRR5MNfARW98BVRPPLC9PTPNPPPLC95<?P3%2WPWPK%2VCF10VK'=fFRP,;>/7K%2NPNPK%2RRXCFRY10RKRZ;I2%5Y%5Z'JP01BXZ%2T'=17TKfJRZfHRXfGRY=8BTfIRT3MA8BYPR[PRC9PZPXP[PRC95<?P310PK,PP%2Y'=10XKRR#51PXRRR%2TR[;I2%5R%5['JP010TK,=[%2Z#5fOR[fMRRfLR\=8BZfNRZ3MfKR]98B\R\PTC9P[PRP\PTC95<?P3%2]10]K'=%2RR]#5RT10RKRR=I]2%5R,JTP0%2Z#517ZKfTRTfRRRfQR]=8B[fSR\3MfPR^98B]R_PZC9PTPRP_PZC95<?P3%2^#517]KP017231342[R013231742R][1354\]1k23P2n2001000000120000000XF;XG;R]P0^F;^G;R0P3P1P\P4O3%1\P]P0P3fUR\PKP5O313\KP]P0P3P1fXR\PSO3%1\P]P0P3fZR\PKPWO313\KP]P0P3f_R\,;>RSPKPXO313SKP]P0P3f\#4RSPKP[O313SKf`RS/6\R[fbRX,>>R^#DR?%4^#1R^f^RZ#DR_%4Z#1RZ1WCHRR1H1CRT%1H1H1I[[R`%1CRag00WSRbAVCH2UW4RH%1I\b^4aRc1WCDRd%1D1H1E[\TReAVCD2VbX4aRD%1E\b^4aRf1WCJRg%1J1H1K[\TRhAVCJ2VbX4aRJ%1K\b^4aRig00WoRjg00X[Rk#URl#URm,N;1N;l1N;k5O;Rk5O;S03g00Y:Rl'b%{jRn3aRo%^jRpP;1`;4P2%z;S04C_Rq%y;Rr%x;Rs1];8R81h;CRt%T@5\;R@5?s%v9R9Ps%T=9\;t1];<R<5?sP91h;1R=Ag;<8Ru5?sC:C:1us:R:P3P41t671s34#5dAr;12CqR7b@bAbBX2;X3;R6132K13E21645RE#1[[^2;^3;RvP3fhRwfiRxPUfeRyO4b5b9b:b;b6b7b8b=b<P?P^P_PZPRP`PHPcPdPePDPfPgPhPJPi%QARA,WCRZ%1A1[CAR_,H1[\TRTAVCA2VbX4aRA%1_\b^4aRaPoPpPqPrPsA?s=8RqP9Ps%TG9\;t9?s<S05P9P;Pug00YfA\;tBRtCf,psC:C:P:P7b@bAbBX2;X3;RG%12132I1HE_[[^2;^3;REP3fjRofkRbPWffRWO4b5b9b:b;b6b7b8bCbDb=b<3e1RB[,SB=<;[faR[/6\RCfcR1,>>R^#DR?%4^#1R^%D\Rz%4\R{#1R|PRP`PHPcPdPePDPfPgPhPJPiP6PvP3PwPoPVPWO4b5b9b:b;b6b7b8b=b<P?P^PzP|PRP`PHPcPdPePDPfPgPhPJPiPZPTPAPaPGPEP3PoflREPPfgRPO4b5b9b:b;b6b7b8bCbDb=b<3e1RBC,SB=<;CPyfdRCP116XSRG,RBR|16X[Rz,RBR^P\P;Pz%4SR\,@3R?A8B1[,SBRV'31;>yRv=CV3'XXE;P;PG161XRV?C\31@3vR6/3V'XXE;AAS{[R{1>>CRV#4R}=A[SR~fW3o%5{%5~'XQ001@[\/7X1@Xv/7[16C1Rv%4[R[16CXR~3C1;>WR{=C~v'XP31@X[/71P]P0P3%41,@CR[PyP2O313[y16PWRW%4C16PyRP3CR[1>>xRx#4R~=CPWRP%DxS00%1~S06%DyS07%4y#1S08PRP`PHPcPdPePDPfPgPhPJPiPnPpP;P;1`;FP4Q04C_P21`;5C_R~PrPsQ01,];RxQ02,];RW5d;=?s8P9Ad;uWRuAg;<x5?sC:P:P7b@bAbBX2;X3;X>;X?;S02AC5421624162F7C5[^2;^3;^>;^?;S01P3fnS04fmR<#4foR8fpRvPOO5b5b9b:b;b6b7b8b=b<3nb1bHW1P3O11@1{/7XP]P0P31;>w,@yRyPCP2O313yCQ00Q06Q07Q08PRP`PHPcPdPePDPfPgPhPJPiQ02Q01P3P8fr,;>Q04PvPOO5b5b9b:b;b6b7b8b=b<9m[Pb1bHW1P3O1n200100000021100011000bO1SB|R|P3EY1SB^R^P2EYP;Pz13?_XE;%DVRV%1}R}%DSRS%1\R\PRP`PHPcPdPePDPfPgPhPJPiPZPTPAPa%UmRm#U,N;R?1N;m=O;k5O;/bl=ajnPpP~PrPsA?sW@RWP9PsPqP9PsA?s=xRxP9PsQ05P9A?sutC:RuC:C:C:P:P7b@bAbBX2;X3;X>;X?;134KRK%14%1M135I16FM?CQ_[RQ[[[^2;^3;^>;^?;P3Pb%4oPEP<PUPNPYPwO8b5b9b:b;b6b7b8bCbDb=b<P^P2EYP;PG136_XE;PVP}PSP\PRP`PHPcPdPePDPfPgPhPJPiPZPTPAPaQ039O;?/bl=ajnPpP~PrPsPWP9PsPxP9PsPqP9PuC:C:C:P:P7b@bAbBX2;X3;X>;X?;%1F%15PQ[[\K^2;^3;^>;^?;P3PE1;>8PbP<PLPNPYPwO8b5b9b:b;b6b7b8bCbDb=b<P|P3EYM9lbQbPbNb1bMb1bLb1bKb1bJb1bIb1WJWIP2P3O2n2001000000121000000b0WKW0P2P3O2n2001000000121000000b0WLW0P2P3O2n2001000000121000000b0WMW0P2P3O2n2001000000121000000b0WNW0P2P3O2n2001000000121000000b0WOW0P2P3O2n2001000000121000000b0W0WSWRWGXV;XU;XW;WFWTWXo"). Qed.

Lemma rdn_wbytes_out_off0 : forall segs bs m (s k : Z) (n : nat),
  (2^33 <= s)%Z -> (s <= 2^63)%Z ->
  ((0 <=? k)%Z && (k <=? 2^32)%Z && (Z.of_nat (length bs) <=? 2^32)%Z && (Z.of_nat n <=? k)%Z && (Z.of_nat n <=? 2^32)%Z)%bool = true ->
  rdn segs (wbytes m (Z_to_bv 64 s) bs) (Z_to_bv 64 (s - k)) n = rdn segs m (Z_to_bv 64 (s - k)) n.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupTac ()) [] "h04__x1h14__x2h22Hah32Hbh47__arithh54__ffh67__sat10h77__sat11h86__sat6h96__sat7h:6__sat8h;6__sat9h<8__varmaph=5__with>4cstrh?5cstr0h@1HhA7__sat12hB7__sat13hC4__x3hD1zhE1mhF1nhG2H1hH2H2hI2H3hJ2H4hK2H5hL2E1hM2E2hN3Hs1hO3Hs2hP2bshQ1khR1shS4segsp;1p;2p;3p;4p;6p;9p;7p;8g0000j1VTg000Pj1ATg0015j1ITg001Sj1YTg0026j1bTg002Xj1GTg0036j1CTg003[j2LTg0048j20Tg004Tj21Tg0051j12Tg006Lj3OTg006oR0j2MTg00JLj25Tg007Jj3QTg00:Vj2:Tg008Dj4>Tg009<j3<Tg00:6j2gTg009Vj2ETg00;3j1BTg00;Xj2KTg00<@j2?Tg00<\j3JTg00=@j1ZTg00=_j2STg00>Hj3XTg00?1j2fTg00?]j1eTg00@=j3dTg00@]j2RTg00A;j1tTg00AYj4cTg00B7j1sTg00BUj1rTg00C@j2WTg00Ccj2aTg00DFj3PTg00Dij1qTg00EKj3pTg00Enj2oTg00FPj2nTg00Fjj2mTg00GVj3lTg00H5j4kTg00Hgj4TTg00IRj3^Tg00K2j2HTg00K\j29Tg00L9j2]Tg00Loj3_Tg00MRj3jTg00NFj6NTg00Ndl9iTg005nj2UTg00Ofj7\Tg00PJj8hTg00PnR1f0R2'1p=@f2R3f1R4'E#2/12p=;1U34/U2p==g00QLR5g00QlR67<2p=41114/U2p=D1142=<56p=8%24/12p=[1E42#2p=F1012p=3P3g00RLR7g00RkR8P8g00SKR9g00SkR:P4g00TIP2CTg00U0R;F\p=7f3R<P7P8P8P9P3P4P2Ghp=6P4P7P8P8P9P2P;F\p=`g00UP#Vg00VOR;#AR7#A#AR=#I#YR>#VR?%A=R=#AR@#ARA#IRB#Y%b>[g00W4%G7RC%C=R=#GRD'LRE/03%C;RF#C#C#C#CRG#GRH,LCRI,0<%@<%G@RJ,LCRK,1<f6RL=;>K3=%23RM/1<11MK3=#4f4RM11MK'Df7RN=;>K%2<RO/1M3=RP11OKRO;O2%4P%4O'MP0f5RO11OK'Df8RP=;>K%2MRQ/1O3=#418QK%b?R?f:RQ15BNf9RR5QP1:NL,5BRSPOC>PQPPPSPOC>3<P211NK,DNA;>QK1[LN3=#4%2N/8K%@R11RKf<RN=;>K3=RL1[PRRP;O4%4L%4P'MP0%@Q11QKf=RP=;>K3=#4%2R/8Qf?RR15BNf>RL5QPf;,:N,5BROPQC>PRPPPOPQC>5<?P2%@N11NKA;>RK3=#4%2N/8P11LK,DLRLfARN=;>KRO;O4%4L%4O'MP011RK,DR#4fBRO,F>/8KfDRL15BNfCRS5QOf@,:N,5BRTPRC>PLPOPTPRC>5<?P211NK,DN#4fERT,F>/8K%@SRO11SKRU;O4%4O%4U'MP0%@L#418LKfIRUfGROfFRV,5BfHRW3Q1:VT,5BRTPLC>PUPOPTPLC>5<?P2%@V#418OKP018421034R0[RO10421834RV[10<3\V1g42P4n2001000000120000000XE:XF:RVPO^E:^F:ROP2P1PUP3O3%3UPVPOP2fKRUPKP<O310UKPVPOP2fPRU,F>R?PKPQO310?KPVPOP2fN#2R?fORQPNO310?QPVPOP2%2URUPKPWO310UKfSRUfRRW':ROfURV,E>RQ#BR?%2Q#3RQ%BWRL%2W#3RW1KCHRT1?1CRX%3H1?1I[[RY%3CRZg00WSR[AJCH4UW2RH%3I\[^2ZR\1KCDR]%3D1?1E[\XR^AJCD4V[X2ZRD%3E\[^2ZR_1KCJR`%3J1?1K[\XRaAJCJ4V[X2ZRJ%3K\[^2ZRbg00WoRcg00X[Rd#ZRe#Z,S:1S:e1S:d5X:5X:g00Y:'f%ecRd3dRe%VcRcP:1R:3RfP4%t:CcRg%s:Rh%r:Ri1W:7R71a:CRj%I@5P:57iR@%q8R8Pi%I=9P:j1W:;R;57iR=P81a:1RkAp:;7Rl57iC6C61oi9R9P2P31n561m23#4dAl:14CkR6b5b<b=X0:X1:104KRK10E41:3<R5#3[[^0:^1:P2f[Rmf\RnPRfYO4b4b8b9b:b;b6b7b?b>P?PQPLPWPTPYPHP\P]P^PDP_P`PaPJPb%GARA,KCRW%3A1LCARL,?1[\XRXAJCA4V[X2ZRA%3L\[^2ZRZPePcPgPhPiA7ik7P8Pi%IG9P:j97i;RGP8P:Plg00YfR[AP:jBRjCT,`iC6C6P9P6b5b<b=X0:X1:%34RC104IR11?5L[[^0:^1:P2f]RQf^R?PSfZRSO4b4b8b9b:b;b6b7bAbBb?b>3^15BO,HB=<:OfTROfVRo,E>Rp#BRq%2p#3Rp%BURr%2URs#3RtPTPYPHP\P]P^PDP_P`PaPJPbPdPc1R:4RuPhPiP=P8A7ik;C6P9P6b5b<b=X0:10E2PC[^0:P2PQPSO2b4b8b9b:b;b6b7b?b>PqPpPrPtPTPYPHP\P]P^PDP_P`PaPJPbPWPXPAPZPdPcPuPhPiPGP8P:P;P[PjCT,`iC6P9P6b5b<b=X0:102I1?4L[^0:P2f_RIPmO2b4b8b9b:b;b6b7bAbBb?b>3^15BO,HB=<:OfXRmfWR[Po15BVRu1:VORt,5BRrPUP:Pt%2ORU,92Rp15Bo,HBRq'01F>mRm,9q/02']XD:P:PV1:oVRo/9U/02192mRm/0o']XD:19ts/0V1E>[R[#2Rs,9V/0t%B[R[%3sRs%BORO%3URUPTPYPHP\P]P^PDP_P`PaPJPbPdPcP:PfP41R:<CcRfPhPi1W:FRF=7i7RdP8A_:lFRF=7i;C6P9P6b5b<b=X0:X1:XC:1:43/9</04\0^0:^1:^C:P2%2nPQP?PPO4b4b8b9b:b;b6b7b?b>3j1HBuRuP2EN1HBrRrP4ENP:Pt10pLXD:P[PsPOPUPTPYPHP\P]P^PDP_P`PaPJPbPWPXPAPZPePcPfPhPiPdP8PiPGP8A7iFjC6C6P9P6b5b<b=X0:X1:XC:195M/0L\1\0^0:^1:^C:P2%2?PIf`RIPRPnO5b4b8b9b:b;b6b7bAbBb?b>PrP4ENP:PV10mLXD:P[PsPOPUPTPYPHP\P]P^PDP_P`PaPJPbPWPXPAPZPePcPgPhPiP@P8PiPGP8A_:;7=7ijC6C6P9P6b5b<b=X0:X1:193</0L\1\K^0:^1:P2fb,F>PIPNPnO4b4b8b9b:b;b6b7bAbBb?b>PuP2ENM9ibMbLbKb@bJb@bIb@bHb@bGb@WHWGP4P2O2n2001000000121000000b3WIW3P4P2O2n2001000000121000000b3WJW3P4P2O2n2001000000121000000b3WKW3P4P2O2n2001000000121000000b3W3WOWNWFXQ:XR:WEWPWSo"). Qed.

Lemma rdn_wbytes_out_lit : forall segs bs m (za zb : Z) (n : nat),
  ((0 <=? zb)%Z && (zb <? 2^64)%Z && (zb + Z.of_nat (length bs) <=? 2^64)%Z && (0 <=? za)%Z && (za <? 2^64)%Z && (za + Z.of_nat n <=? 2^64)%Z &&
   ((za + Z.of_nat n <=? zb)%Z || (zb + Z.of_nat (length bs) <=? za)%Z))%bool = true ->
  rdn segs (wbytes m (Z_to_bv 64 zb) bs) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
ltac2:(KReplay.run1 (kr_t_StartupTac ()) [] "h02Hbh11Hh27__arithh36__sat7h46__sat8h54__x1h64cstrh75cstr0h81mh91nh:4__ffh;8__varmaph<5__with=4__x2h>1zh?2H0h@2H1hA2H2hB2H3hC2H4hD2H5hE2H6hF2HahG3HorhH4__x3hI2E1hJ2E2hK2bshL4segshM2zahN2zbp;1p;2p;3p;4p;6p;9p;7p;8g0000j1RTg000Pj1GTg0015j1\Tg001Sj1UTg0026j1^Tg002Xj1[Tg003[j2kTg00ZMj21Tg004Tj25Tg005Qj2MTg005nj2DTg006Lj3ETg006oR0j2HTg00JLj27Tg007Jj3FTg008Dj4:Tg009<j3>Tg0051j14Tg0048j22Tg00:6j2cTg00<@j2?Tg00Zjj2bTg009Vj2CTg00;3j1ATg00;Xj2aTg00<\j3`Tg00?]j1_Tg00@]j2PTg00B7j1vTg00BUj1uTg00Ccj2]Tg00C@j2TTg00Dij1tTg00Enj2sTg00FPj2rTg00Fjj2qTg00GVj3pTg00H5j4oTg00DFj3nTg00Hgj4ZTg00IRj3YTg00K2j2QTg00K\j29Tg00L9R1j2LTg00LSj3jTg00AYj4WTg00Loj3iTg0036j1lTg00MRj3hTg00Mlj3mTg00NFj6JTg00A;j1gTg00Ndl9fTg00Ofj7eTg00PJj8dTg00PnR2f1R3'5f0R4'Dp=Kf2R51C34#4'9p=@1524p=31D53/D4p=6%44,93p=Bg00QLR61D34g00QlR73>p=<A>647p=0f3R81C53#4'9/54p=;1953/54p=I1534=>67p==1134,D5p=V1224p=8g00SkR9P3g00TIP4CZp=SP3g00RLR:g00RkR;P;g00SKR<P4g00U0Fep=NP8P:P;P;P<P5P3P4Gdp=O1C34#4p=Xg00UP#Rg00VOR:#GR=#G#GR>#\#UR?#RR@%G>#G#GR>#\RA#U%^?[g00W4%[=RB%[>R>'kRC,13,K3f4RD9@3?RE/5C%35RF36115CRG1B54RH/5C3615H315E5'M'<1DFGf5RG9@5?RF/5C%38RE36118CRH1B83RI/5C36RJ15I515F8'MRF;E4%0J%0F'HP0f6RF9@8?RJ/5C96EH%3D11DC361BD5RH/5C'<15H815JD'M#0%^@R@f8RJ17ADf7RH5FF17AGREP8C:PJPFPEP8C:3>P4%3G11GCPGP?PJPCC;36%3F11FC36%4D=IFC'<%4G=IHFPFP?f9RDPHC;'M#0%3H11HCPHP?f:REPCC;36%3JRI11JCRK36RL%4F=IJCRF;E3%0L%0F'HP01DIKPJP?f;RKPCC;%3D3611DC'<1BDH/=Cf=RI17ADf<RF5FK17AERLPJC:PIPKPLPJC:5>@P411EC,KEPEP?PIPCC;%3K3611KC'<1BFE/=C11FC,KFPFP?f?RFPCC;%3IRK36RJ11ICRL;E3%0J%0L'HP0PIP?f@RJPCC;96KLf>RL#3'<11LC#0fBRK17ALfARM5FJ17AFRNPIC:PKPJPNPIC:5>@P4%3F11FCPFP?PKPCC;36%3J'<11MCRF#0%3MPMP?fDRNPCC;76FRF%3KRO;E3%0F%0O'HP0AVOKCPKP?fEROPCC;'<fCRF#3#0fGRP17AFfFRF5FO17ANRQPKC:PPPOPQPKC:5>@P411NC,KNPNP?PPPCC;'<%3FRN#0AVNFCRNPFP?fIRFPCC;RK;E3%0N%0K'HP0%3P11PC'<fJRK9@P?/=CfLRNfHRQ,7AfKRO5FK17AFRRPPC:PNPKPRPPC:5>@P4%3F11FC'<fMRF9@K?/=C%3ORK11OCRO;E3%0K%0O'HP0%3N#011NC#0fQROfORK17AFfP3FfNRF,7ARPPNC:POPKPPPNC:5>@P4%3F#011KC#0P01=341253[RF12341=53R@[1285\@1c34P3n2001000000120000000X89X99R@PF^89^99RFP4P2POP5O3%8OP01134#01?53[R01?341153#0RO[1?85\O1b34P3n2001000000120000000X89X99ROP0^89^99R0P4fSRNPCP8O31?NCP@PFP4fUfXRN7@?RPPCPEO312PCP@PFP4P2PNPMO3%8NPOP0P4fZR0PCPQO31?0CP@PFP4f\RQ/B0R0PCPKO3120Cf]R0f_RK,C?RO#ARN%4O#8RO%AQRM%4Q#8RQ1aB>RP1?2B%8>1?2C[[RE%8BRRg00WSRSA`B>3UWFR>%8C\S^FRRRg00WoRS#_RT%RSRS1P93RU%v9RV%u9RW1]921T9:RX'S,NWRY%t;R;PYCO1sW<R<P4P51r671q45#0dAp923CoR2b:b;b<X59R7%84%83[^59R6P4fbRYPDO2b2b3b4b7b6PNPOPMPQPPPEP>PRPTPSPUPVPWP9PXg00Yf1]9B=n9ARBCZ,NWRUP;PUCOP<P2b:b;b<X59RU1?4C1?3C[^59RQP4PYPHO2b2b3b4b7b63Y17A0,QA=>90RMf`RO,C?RN#ARD%4N#8RN%A0RZ%40R[#8R\PPPEP>PRP7P6P4PYPJO2b2b3b4b7b6PDPNPZP\PPPEP>PRPUPQP4PYPLO2b2b3b4b7b65Y0PMPYfaRMPOf^RL,7ARQ17AKRUP0P9PK%4LR0,94R\1QAURU'21X?YRZ,9U/24'LX>9P9PL19O0RN/24194ZRD/2O'LX>9AIK[LR[1C?MRJ#4R6=ILKR7fW3j%0[%07'LP11=NK19KZ/=O1BMKRZ/2OfcRN9@O?R1/2M'LP41=ZOP@PFP41BNMRZPYP3O312ZYfdRZ%4YRO'9/2NR7ff,C?R[#4R],9N/2ZR^%A[R[%8]R_%ANR`%4N#8RaPPPEP>PRPTPSP91P95RbP31P98CWPVPW1T9=9i9XRX%l:,T9'S,NWR:P;P:COP<P2b:b;b<X59X=9XH9R:1943R=/251935R5/28[^59^=9^H9R8P4fhRcfg#4fiRdPGO4b2b3b4b7b63hb1b?W1P4O11=1MP@PFP4fe9@Y?RYPNP3O312YNP[P_P`PaPPPEP>PRP:P8P4Pdfk,X?PcPGO4b2b3b4b7b69m7^b1b?W1P4O1n200100000021100011000bG1QAQRQP4EJPUP3EJP9PK12\CX>9%AJRJ%86R6%ALR\%80R0PPPEP>PRPTPSP9PbP3%g9CWPVPW1SXB,NWRWP;PWCOP<P2b:b;b<X59X=9R212=C125C[^59^=9R5P4POPZPHO3b2b3b4b7b6PUP3EJP9PL12DCX>9PJP6P\P0PPPEP>PRP2P5P4P]PNPIO3b2b3b4b7b6PQP4EJM9fbJbIbEb1bDb1bCb1bBb1bAb1b@b1WAW@P3P4O2n2001000000121000000b0WBW0P3P4O2n2001000000121000000b0WCW0P3P4O2n2001000000121000000b0WDW0P3P4O2n2001000000121000000b0WEW0P3P4O2n2001000000121000000b0WGW0P3P4O2n2001000000121000000b0W0W9XN9XM9W8WKWLo"). Qed.

Ltac peel_zc z := lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
(* [comment removed for export] *)
Ltac addr_lin :=
  repeat match goal with
  | |- context [Z_to_bv 64 (bv_unsigned ?s - ?a + ?b)%Z] =>
      peel_zc a; peel_zc b; let c := eval vm_compute in (a - b)%Z in
      lazymatch c with
      | Zneg _ => let c' := eval vm_compute in (b - a)%Z in replace (bv_unsigned s - a + b)%Z with (bv_unsigned s + c')%Z by lia
      | _ => replace (bv_unsigned s - a + b)%Z with (bv_unsigned s - c)%Z by lia
      end
  | |- context [Z_to_bv 64 (bv_unsigned ?s - ?a - ?b)%Z] =>
      peel_zc a; peel_zc b; let c := eval vm_compute in (a + b)%Z in replace (bv_unsigned s - a - b)%Z with (bv_unsigned s - c)%Z by lia
  | |- context [Z_to_bv 64 (bv_unsigned ?s + ?a - ?b)%Z] =>
      peel_zc a; peel_zc b; let c := eval vm_compute in (b - a)%Z in
      lazymatch c with
      | Zneg _ => let c' := eval vm_compute in (a - b)%Z in replace (bv_unsigned s + a - b)%Z with (bv_unsigned s + c')%Z by lia
      | _ => replace (bv_unsigned s + a - b)%Z with (bv_unsigned s - c)%Z by lia
      end
  | |- context [Z_to_bv 64 (bv_unsigned ?s + ?a + ?b)%Z] =>
      peel_zc a; peel_zc b; let c := eval vm_compute in (a + b)%Z in replace (bv_unsigned s + a + b)%Z with (bv_unsigned s + c)%Z by lia
  end.
Ltac peel_bool := cbn [length word_to_le_bytes Z_to_le_bytes zeros repeat app Datatypes.length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add];
                  lazymatch goal with |- ?g => check_closed_term g end; vm_compute; reflexivity.
Ltac peel_generic :=
  repeat (lazymatch goal with
          | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
              tryif constr_eq a b then fail else
              first [ rewrite rdn_wbytes_out_lit by peel_bool
                    | rewrite rdn_wbytes_out by region_side ]
          end).
Ltac peel :=
  addr_lin;
  lazymatch goal with
  | |- rdn _ _ (Z_to_bv 64 (?s - _)%Z) _ = _ =>
      let L := fresh "PEEL_lo" in let H := fresh "PEEL_hi" in
      tryif (assert (L : (2^33 <= s)%Z) by lia; assert (H : (s <= 2^63)%Z) by lia) then
        (repeat (lazymatch goal with
                 | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
                     tryif constr_eq a b then fail else
                     first [ rewrite rdn_wbytes_out_off by (first [exact L | exact H | peel_bool])
                           | rewrite rdn_wbytes_out_off0 by (first [exact L | exact H | peel_bool])
                           | rewrite rdn_wbytes_out_lit by peel_bool
                           | rewrite rdn_wbytes_out by region_side ]
                 end); clear L H)
      else peel_generic
  | |- _ => peel_generic
  end.

(* [comment removed for export] *)
Ltac rd_img L := addr_norm; rewrite rdn_cmem_data by region_side; peel; exact L.

(* [comment removed for export] *)
Ltac rd_hit8 :=
  addr_norm; peel;
  lazymatch goal with |- rdn _ (wbytes _ ?a' _) ?a _ = _ =>
    first [ constr_eq a a' | replace a with a' by (first [f_equal; lia | bveq]) ] end;
  apply rdn_wbytes_hit8; unorm; lia.

(* [comment removed for export] *)
Ltac in_list := cbn [In]; repeat first [ left; reflexivity | right ].
Ltac solve_regs_agree :=
  repeat (apply regs_agree_upd; [ in_list | ]); apply regs_agree_refl.

(* [comment removed for export] *)
Ltac incl_list :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
Ltac regs_agree_weaken Hag :=
  eapply regs_agree_mono; [| exact Hag]; incl_list.

Ltac notin_list :=
  cbn [In]; intros HH; repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH.

(* [comment removed for export] *)
Ltac carry Hag H r T :=
  pose proof (Hag r ltac:(notin_list)) as T;
  gres_loop_in T;          (* [comment removed for export] *)
  rewrite ?H in T.

(* [comment removed for export] *)
Ltac ra_chain :=
  first [ apply regs_agree_refl
        | apply regs_agree_upd; [ in_list | ]; ra_chain
        | match goal with
          | Hag : regs_agree _ _ ?r |- regs_agree _ _ ?r =>
              eapply regs_agree_trans; [ | regs_agree_weaken Hag ]; ra_chain
          end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition bwd (segs : list Segment) (G : machine_state -> Prop) : Prop :=
  forall st st', msteps segs st st' -> G st' -> G st.

Lemma bwd_msteps : forall segs tgt, bwd segs (fun st => msteps segs st tgt).
Proof.
ltac2:(KReplay.run1 (kr_t_StartupTac ()) [] "h02sth12H1h22H2h34segsh43st'h53tgtp;1p;3p;6p;2g0000j13Tg00[Jj30Tg00\Ej62Tg00]Dj21Tg00UP#3g00^>R0f3R1f1R2f0R330f4R4?021f5P1f2R1P4P2P3E2W2W1X40X00A0132X00,12eW5W3o"). Qed.

(* [comment removed for export] *)
Ltac gsteps HG := eapply HG.
