(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import StrFun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_merge.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Str_tac () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02c69OSSVerify5KrLib2K52PG7Str_tac8ld_factsC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K54Spec6StrFun:window_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib2K53Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic7f_equalC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing5PExpr04C69OSSVerify5KrLib2K53Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec6StrFun:window_subC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC69OSSVerify5KrLib2K53Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec6StrFun6copiedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52PG7Str_tac8st_factsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic8iff_reflC69OSSVerify5KrLib2K54Spec6StrFun@u8arr_store_ok_nC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC69OSSVerify5KrLib2K53Lib3Mem9upd_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c69OSSVerify5KrLib2K52PG7Str_tac;mc_store_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame5munchC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC69OSSVerify5KrLib2K53Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec6StrFunAu8arr_write_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54Spec6StrFun;copied_updZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53Lib5Frame6insideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
Ltac name_list xs L :=
  lazymatch type of L with
  | length _ = O => destruct xs; [clear L | cbn in L; discriminate]
  | length _ = S _ => let x := fresh "x" in let xs' := fresh "xs" in
      destruct xs as [|x xs']; [cbn in L; discriminate | cbn in L; apply Nat.succ_inj in L; name_list xs' L]
  end.

(* [comment removed for export] *)
Ltac window base k HW :=
  lazymatch goal with SRC : bytes_at ?segs ?m ?S ?src |- _ =>
    let xs := fresh "xs" in let L := fresh "L" in
    destruct (window_ex src base k ltac:(lia)) as [xs [HW L]]; name_list xs L
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac woff base c :=
  let cz := eval vm_compute in (Z.of_nat c) in
  lazymatch cz with 0%Z => base | _ => constr:((base + cz)%Z) end.

(* [comment removed for export] *)
Ltac anorm REG imm :=
  lazymatch REG with
  | Z_to_bv 64 ?E =>
      let E' :=
        lazymatch imm with
        | 0%Z => E
        | _ => lazymatch E with
               | Z.add ?x ?a =>
                   let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
                   lazymatch isl with
                   | true => let s := eval vm_compute in (a + imm)%Z in
                             lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
                   | false => constr:(Z.add E imm)
                   end
               | _ => constr:(Z.add E imm)
               end
        end in
      constr:(Z_to_bv 64 E')
  | _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
  end.

Ltac cur_mem_addr :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Load _ _ _ ?rs ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    | Some (Store _ ?rs _ ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    end end end.

(* [comment removed for export] *)
Ltac addr_tac :=
  unfold wa;
  first [ reflexivity
        | f_equal; lia
        | lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
            replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

(* [comment removed for export] *)
Definition ld_facts (base : Z) (c j kw : nat) (i : Z) : Prop :=
  (0 <= base)%Z /\ (c + j <= kw)%nat /\ (i = base + Z.of_nat c)%Z.

Lemma mc_read1 : forall segs m S src kw base xsw c i a b,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  ld_facts base c 1 kw i -> nth_error xsw c = Some b -> a = wa (S + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
ltac2:(KReplay.run1 (kr_t_Str_tac ()) [] "h04__x1h14__x2h21Hh33Hc0h47__arithh54__ffh68__varmaph75__with84__x3h94cstrh:5cstr0h;2HWh<2Hah=2Hbh>2Hch?2Hih@2HnhA1ShB3SRChC1ahD1bhE4basehF1chG1ihH2kwhI1mhJ1ohK4segshL3srchM3xswp;1p;4p;3p;5p;2p;:p;6p;;p;<p;Bp;7p;8g0000j1FTg000Pj16Tg0015j1JTg001Sj1HTg0026j1OTg002Xj4mTg003Pj1MTg0040j3_Tg004Nj3]Tg004mj30Tg005Gj1@Tg005fj5WTg006aj29Tg0078R0j28Tg007RR1j11Tg0082R2j22Tg008OR3j2LTg008jj37Tg009Hj25Tg009jj1CTg00:\j4QTg00;aj1KTg00<Aj3BTg00<aR4j2^Tg00=9R5j2ITg00=Uj2;Tg00=oj1[Tg00>MR6j2ATg00>ij4XTg00?Pj1>Tg00@5j2GTg00@Sj1VTg00A1j4PTg00AOj1UTg00Amj1TTg00BXj2?Tg00C;j2STg00C^j3RTg00DAj1qTg00Dcj4ETg00ENj2pTg00F0j2oTg00F\j3lTg00G;j4kTg00Gmj4iTg00HXl:hTg00IVj6gTg00J2j2<Tg00J[j1fTg00K9j2eTg00KZj3dTg00LCj3DTg00Llj2cTg00MXj1bTg00N=l;aTg00O6l<NTg00O[lBjTg00PAj7`Tg00Pej8nTg00QIR7f0R8'Ap=3g00QgR9g00RFR:P4P1P5g00Rdf5R5f4R4f3R;f2R<f1R=P8M<Np=\P9P9P9P:P:P:g00SFP1P1P1P2g00SfP5P4P;P<P=P8MBjp=ZP9P:P0P1P6g00TIP5P4P;P<P=P8M<Np=YP:P=g00TkP8CEp==P=g00URR6g00V1R1P1g00VQR0P8g00W1F`p=4P;P6P1P1P0P<P=P8Gnp=:g00WQ#Fg00XPR6#6R2#6#6R>#6#6#6#J#HR?%J>#HR>#OR@[%F>RAf:RBf9RCf8RDf7RECmf6RF#M=_>D9]>E=0A5PEP5g00Y5RG#@RHPDP4DWP3%3D19FH/8C%1F,2D90:5'LA7>DE15>450@f=R4/2E#C90?F%OAR5f@RIf?RJPEPHCQ%K>RK9B>F,5A30[[P8%3B19CHf<RL'8f;RM%1C'290:D'LP319BH/84%1B,2L90:CA7>LM15>D50@fARD/2M#C90?BfDRCfCR3PMPHCQAB>BK,5A505[[P819LH/8J%14,2J90:Lf>R597>J15>M50@12C5#C90?4fGRKfFRBfERNPCPJP4P5PLP@A7>DI%MI97>N=0@8XJ@PCPDfBR@P3PIPJPMPE1^I3%1IRE%13RJ'IPIPE1;:ERLP3PJ1;:JR5E\19IHRO/83%[6RP,2ERQ/AJRRPOPQPIPEPLPHPP1;:PEZP3PJP5EYP;CXR5PR%>C%1CRC#3%>@%1@#3g00YTR@#KRJ%F@RLP:1G:<REP=%V:CP%U:RI%T:RQ1?:6RO1S:P5R:1?:2R2'=,4Q%q1R1P:POg00Z@P2CE,4QC:1pQ0R0P8P<g00ZgRSg00[GRT';1o8<=0STdAl:7=CkRTb5b6b7X0:X1:128P/A=1I=<[^0:^1:P8%1KPCP;O3b4b:b9b3CiP<M:h15>4P=EgP5PR%>D%1D#3%>N%1N#3%@HRN#@,<:%f6,e:1<:N5d:1<:H1<:G5D:5D:5D:g00[g'c=B@JPLP:PEP=1G:;CPPIPQ1S:7R7%b6,?:R6'=,4QP1PQP:POg00\SAR:26CE,4QP1PQ1=72,4QP11=7O,4QC:C:C:P0PTb5b6b7X0:X1:X8:%3<12<;90:=%3;R;P;[[[^0:^1:^8:P8PCPBP3P<PFPMO6b4b:b9b3P8M;aW<W@W?W>P=P8O2n2001000000121000000W2W=P=P8O2n2001000000121000000W2W;WBXD>XC?XG:XF9XMAXE:XH9WLXA:WIWKo"). Qed.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
  ld_facts base c 4 kw i -> a = wa (S + i) ->
  exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Str_tac ()) [] "h04__x1h14__x2h24__x3h34__p1h44__p2h54__x4h64__x5h74__x6h81nh92HWh:2H3h;3HL0h<3Hc0h=7__arithh>4__ffh?4__p3h@8__varmaphA5__withB4__x7hC4cstrhD5cstr0hE5cstr1hF5cstr2hG1whH2z3hI1HhJ2H4hK2L0hL1xhM2z4hN2H5hO4__p4hP4__x8hQ4__x9hR1ahS1mhT2z5hU2H6hV2HLhW3HW0hX2HbhY2HchZ2Hih[1Lh\1Sh]3SRCh^4baseh_1ch`1iha2kwhb4segshc3srchd3xswhe1yhf2z6p%0p&0p;1p;4p;3p;2p;5p;6p;9p;;p;<p;Bp;7p;8g0000j1{Tg000Pj1STg0015k109Tg001Sj1~Tg0026k10?Tg002Xk40XTg003PR0j1LTg0040j3ITg004Nj3TTg004mj33k10>Tg00]:j21k10OTg005Gj1@Tg005fk50]Tg006aj2FTg0078R1j2ETg007RR2j10Tg0082R3j22Tg009jj1[Tg00:\j4cTg009Hk208Tg008OR4j2:Tg00]Zj2wTg00^4k60NTg00^Qj2GTg00^hk303Tg00IVj6xTg00_Jj2fTg00_ak300Tg00>MR5j25Tg00=ok10@Tg00>ij4_Tg00`Bk20ZTg00`ek30YTg00aBj2ATg00a_R6j2VTg00?Pj1QTg00b<k20;Tg00=9j2eTg00J[k10WTg00K9k20VTg00KZj3dTg00J2k20:Tg00;ak10UTg00@Sk10STg00AOk10RTg00Amk10QTg00MXj1mTg00DAk10PTg00BXk207Tg00b^k306Tg00C;k205Tg00ENk20MTg00=Uk202Tg00F0k20LTg00F\k30KTg00G;k40JTg00Gmj4tTg00cAm90GTg00d>m;0FTg00e<j6rTg00eZj4}Tg00f5k40ETg00fOk20DTg00flm<0ITg00O[lBzTg00O6m<01Tg00gQk20CTg00h3j2qTg00LCj3kTg00Llj2nTg00<Aj3aTg00@5k20BTg00A1k40ATg00Dcj4]Tg00hMk60TTg00PAj7YTg00i1j7|Tg00C^k30\Tg00Pej8yTg00iUk70[Tg00QgR7f1R8f0R933p=7g00QIR:/59p=9f2R;g00RFR<?389':p=\A3<89p==20D:9p=4202<9p=6P<P7P<P<P0f4R0P2f3R=g00j9P;P8P9N<0Ip=iP7P7P7P<P<P<g00SFP2P2P2P3g00Sff5R3P0P=P;P8P9MBzp=bP7P<P1P2P5g00TIP3P0P=P;P8P9N<01p=gP7P<P9P2P8P;P=P0P3f6R5f7R1f8R>N<01p=pP7P7P7P<P<P<g00jfP2P2P2P5g00kFP3P0P=P;P8P9MBzp>0=P7P7P7P<P<P<g00kmP2P2P2P6g00lMP3P0P=P;P8P9MBzp>0<20C:9p=U1e:9p=?A3<9:p=PA3<=;,:0158:/:9'qp=NA3<;8,:=/q9p=O20:<9p=>Ak<899k<;p=8Ak<89p=;g00YTR6g00[gR2,n;1n82=a693ap=^20B<9p=JP<P;P8P9H0Ap=<207<9p=HP<P8g00Z@P9C]p=lP8g00URR?g00V1R@P@g00VQRAP9J0Tp=WP=P?P@P@PAP;P?P@P@PAP8g00W1RBFYP9F|p=RP<P8g00\SRCP9C]p=CP=P?P@P@PAP;P8P?P@P@PAP9PBFYF|p=ZP;P?P@P@PAP<P8PCP9C]PBFYp=KP;P?P@P@PAP8P9F|p>04B0\<89p=DP;P?P@P@PAP<P8g00TkRCP9C]PBFYp=vP3P?P@P@PAP0P?P@P@PAP<P=PCP;C]PBFYP8P9Gyp=BP0P?P@P@PAP=P?P@P@PAP;PBFYP8P9Gyp=jP3P?P@P@PAP0P?P@P@PAP=P;K0[P8P9Gyp=M1:;8/q9p>0HA3<9:,:8p=o159:p=u1n82=a69p=`P<P8PCP9C]p=hAk<89/n2p=sAa6899a6;p=Xg00WQ#{g00XPR2#SRC#SR?#SRB#S#S#S$09#~RD&09B#~RE$0?[%{ERFf9RGP>P1P5H0X%L3=IE19TE5=3F011E3/71P1P3g00Y5RH#@RI#@RJ#@RK#@RLP>P0I0]P4%9>1F5L/EG%05,2>7\3f<RM/25#[93D3&0?FRNf@ROf?RPP1PLCc208F9RQ33f:RR9IEG9TEL93F911E9/7LRS':':XGF,wF[P9%9R1FGL/EMf;RT%0G'27\>P41FRLf=R4'E%0R,2M,=G12OR#[93DGfDRUfCRVPTPLCc=3NQf>RW9IE49TEL93F9/:S':XGF,wF[P91FML/EP%04,2P,=M12V4#[93DMPD12UW#[fHRXfGRYP8PLCc=3NQfARZfBR[5IE9TEL93F9/:SS00':XGF,wFXRDPFP7&0OE%LZRS=IEV9TE[R\POPTJ0N11E\11EO'7P7%L[R\=IEUR]9TEV,1E11E[R^,79X87P911E],GVR_B03EV]Ex11EZ,7_P7%LVR_fER]5IE,1E1G]911EVR`'7X87P911E]Ra/f_RbB00E_]Ex1GUb/7^P7P`fFR^11EYRb%L]R_'f'G/79X87P9P]P4Ex11E^%LU'f,G]/7]1F_^Rc/Eb%4]Rd%0^Re'2Rf%0bRg'5PcPfP_PdP9XL<Rd%49XL<R_P]P]%6]DiP^Pe%6eRfEbPbPg%6gEg1FVLRc/E^%0VRh&0@?Ri'2Rj/5eRkPcPjPVPh%6hS01PLPi%6iRjEbP^PePfEgP5C_Pk17aY%0aRk%0YRf'=Re&0>7S02&0><Rc%08%09'=178920Z8940YXe7XL7RlPaPk%6kPYPf%6fM9pPPC_PefIRe,1ERf%LYRk'fRa,GXRm/7X%0XRn%0fRo%4YS03'A#4'V/=nRpQ02PcPlPm1A89#4XS<X8<S04PoP_PYO1RmO2Rq,VnPXPn%6nRrPaPqQ04PfPo%6oPkPmPdP_PYPY%6YDiK0=J0<PXPnPrM9pP;C_Pp%Qb%9gfKRg,1ERb#Q%0b#9%QX%9nfLRn#Q%0nS05#9%Un%?n%4nRbPnPn%PbDNfMS06#4P<fPRp,1E#0S07/A9Rr#U%?r%4rRmPrPr%PmDNfQRm,1E#0/A8#4P<%0mRm00;91em91Vm9RrPm159m?\r9COfRS08#0/V8P<p-0Rr%@LS09#>Rk%>LRo%>KRK&0W2-0V<Rf%>JRJ5d<Rq%>IRI383820:<HRH,;q98koA8koH1;KI98ko&0U6Ra3^3^%{6R6%J3S0:&0S<Rs7<5%J0Rt7<;%J5S0;?<5s?<=s7<8&0R<Ru&0Q<RvPvPvPv%HCRw%m?#HRx'l1Wv>CRPv1WvGS0<Pv%HBRB/CxCZ&0P@R@PvPvPv1WvRS0=Pv%m2Ry#HRz207<2R2606<,CxCZ1WvTS0>205<:R{9KvxS0?604vP@PvPvP{%Sy#HR|P@PvPv1CBwP@PvPv205<iRB,D|PwP@1D2w=vvzEBDjEBEMEM20MvARAP9P;g00ZgR}g00[GR~+0220L9;=3}~dB0K<:8H0JR:b>b@bAX0<X1<X2<X5<X6<X7<X3rX4rX?rWO1e83A\10380H5PGP51A=81oR5CO%931=10121iS0@/531235/51[[[[[^0<^1<^2<^5<^6<^7<^3r^4r^?r^OrP9fU,1E#0R~/A3R}#u%?}fTS0A#0R},5=1=8}P=P8PmP~P}P3P;P0P>PTP4O?b=bTbNbMbJbHb:bFbEbDbCbWb;b<Ctb9b9b9b91FS[/E`PFPXPY12^O#[PLCc=3NQQ00':XGF%LPRQ=IEURS9TELR}PYP^12]P#[PLCc208F}53NAIEOZ9TEL93F}S0011E}S0B/7LS0C':PYP^P]PUPPPLP41F\VRY11EUR}'E%4[/2h%0}RN'5R~PYP_P[O1RY/2hP\PYPdP_P[P[%6[DiPVPhQ01EbP}PN%6NS01EgP9C_S0DP~1FZLS0E/EU%0ZRh/2iRY%0UR\'5RmQ0EPYPZPh%6hPLPiPjEbPUP\%6\EgP0C_S0EPm17`]%0`R\%0]Rh'=RYQ02PcPlP`P\%6\P]Ph%6hM9pP4C_S0FPY%Q}S0G%9NS0H11EXRX#QS0I%0X#9S0J%Q]S0K%9hRh%QeR]%0e#9RX%Ue%?e%4eR\PePe%P\DNfJR\#4P<1;IHR`98Kq/`aP6%J;%J=7<8PuPvPvP{PzP@PvPv1Dwz,C2P@PvPvP{PwP@Avv{2EBDjEBPAP:b>b@bAX0<X1<X2<%9;12;=,=8%9=RqPq[[[^0<^1<^2<P9%0\PnPeP0PMPZO6b=bHb:bFbEbDbCb;b<bK1FQLRe/E}%4PRn/2iR\/5NPeP\PQPnPdP_PPPP%6PDiS0LPLPiPjEbP}PNQ01EgQ0DP~Q0EPmQ0FPYQ0GQ0HQ0IQ0JQ0KPhP]PX%U^S0M%?^%4^R_P^P^%P_DNS0NQ03P<%Ug%?gS0O%4gR_Pg%ugR^/o_COPbP<Q09#@Rb#>R_9d<fRd1;JH98oK78kR\%@bRb#>ReA8KJ`98dkRd';1;e\=^da3^P6Q0;9<t;Q0:%J1R`7<=7<8PuPvPvPvPv1l{zAKv|zCRPvPv1hz{AKv|{CRP@PvPvPvQ0<Pv%H?R?,C2CZPvQ0=Pv1C2{CZP@PvPvP{%mCRC#HRqP@PvPv1DqB%my#HRyP@PvPv1D|yPwP@PvPv1Dzq,C?P@1D2B=vvwDjEBEBEBEMEMPAP:b>b@bAX0<X1<X2<X5<X6<X7<XB<X3rX4r%?;P3P;P;%P3DNP>P8P01oG8CO%95Q0@/5G12GR/53121G,=>125i/51[[[[[[^0<^1<^2<^5<^6<^7<^B<^3r^4rP9P^Q0OfOR^#0P8Q05PgfNRgQ07P=P;P0P5PRPTPWO?b=bMbJbHb:bFbEbDbCb;b<bKCtN90GQ00Q0CPUPZP[PVPOPLPPPMP1P=P;N;0FP711ESS0C,GL179LX87P71f}QRO1GL9/7LX871GLOS00/7L1ANn#4RV,ViRZ/=iQ02PcPlQ00PZPLPiPjPOPVQ04P}PNQ01PQPnQ0LK0=J0<PLPiPjM9pQ0DP~Q0EPmQ0FPYQ0GQ0HQ0IQ0JQ0KPhP]PXQ0MQ0NQ03P<Q06,1E#0/A9RX#U%?X%4XR]PXPX%P]DN11Eg#0/A8#4P<20;i91ei91Vi9RgPi159i?\g9CO1Vi8P<%U^%?^Rg%4^R]P^%u^RX/o]CO%4pP<%@bRb#@R]#@Rh#>RY9d<fRm1;KJ98ko78eRo%>bRb1;_H'sR_%@h#>Rh1;JI98kK98meRm';%>]9d<fR]Ad<feRf;8dRd,;Y1;eH,sbRbA8]f\R]1sfHRf1;Y]1;ho/`a9X__9^dm9Xbb'`9Xff7Xf'`7Xb3^7X_'`P6%JG?<5s9<t;%J>?<3s?<=`7<8PuPvPvPvPv1l{wAKvqwCRPvPv1hw{AKvq{CRP@PvPvPvPv%SC#HRC,lBAKv2BRuCRPvPv1hCBAKv2CCRP@PvPvPvQ0>PvB06<yxR2,CCCZPvPv1h2{AKvC{CRP@PvPvPv1WvMPv1CxzCZ1Wv4Q0?604vP@PvPvP{P?P@PvPv1D?BP|P@PvPv1Dq|PyP@PvPv1Dw?,CzP@PuDjEBEBEBEMEMEMEMPAP:b>b@bAX0<X1<X2<X5<X6<X7<XB<XP<XQ<X3rX4rX?r%?8P0P8P8%P0DN1eiGP8Pi15Gi?\8GCOPTPR1A>GR:P:%PRR:DNP4PRP31:W:CO%9112>i/5R12RT/5M12>R,=G1=>i[[[[[[[[^0<^1<^2<^5<^6<^7<^B<^P<^Q<^3r^4r^?rP9PXPgQ0A,1E#0Rg/A1#?P3P1PgfS#0P8%0pP^Q08P=P;P0P5P>PRPWPPP[ODb=bfbUbTbNbMbJbHb:bFbEbDbCb;b<bKCtQ0CB00EQUErQ0BB03ELSErC}C}H0Eb[P4P9ErWIWZWYP8P9O2n2001000000121000000WIWXP8P9O2n2001000000121000000WIWVW9W]XRDX`<X_7XdFX^<Xa7WcX\<WSWbo"). Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
  ((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
   (S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
  u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
  firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Str_tac ()) [] "h01Hh11xh24__x1h32H2h42L0h54LEN0h67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<4__x3h=4__x4h>4cstrh?5cstr0h@5cstr1hA1nhB1yhC2z2hD1DhE3DSThF2HPhG2HahH2HkhI1LhJ3LENhK1PhL1ShM2_HhN3_H0hO3_H1hP3_H2hQ3_H3hR3_H4hS1ahT4basehU2bshV1chW1khX2kwhY2m1hZ4segsh[3srch\3xswp&0p;1p;4p;3p;2p;8p;<p;6p;7p;;g0000j1OTg000Pj1FTg0015j1]Tg001Sj1XTg0026k107Tg00m0k403Tg003PR0j1;Tg00mej3sTg00]:j24Tg004Nj3BTg004mj33j1YTg0040j3WTg00n_j8eTg0082j20Tg009jj1=Tg00oZj4CTg006aj2GTg0078j2ITg00=oj1_Tg010Zj2oTg007RR1j11Tg00>MR2j22Tg00fOj2HTg00`Bj2iTg00`ej3hTg00>ij4fTg00?Pj1UTg00gQk206Tg00=9j2dTg008OR3j2:Tg00h3j2STg00;ak105Tg00@5j2RTg00AOk104Tg00Amk102Tg00C;k201Tg00BXj2LTg00DAj1~Tg00ENj2}Tg00=Uj2aTg00F0j2{Tg00F\j3zTg00G;j4yTg0117j1xTg00O6l<ZTg005Gj1NTg00J2j2JTg00J[j1tTg00K9j2rTg00KZj3qTg00LCj3TTg00Llj2[Tg00<Aj3^Tg00@Sj1pTg00A1j4`Tg00hMj6uTg00MXj1vTg00Dcj4PTg00iUj7nTg00C^j3mTg00Gmj4|Tg00e<j6bTg011Ul;lTg00fll<cTg00PAk700Tg00Pej8kTg00i1j7jTg00QgR4f1R5f0R633p=@g00ZgR7g00[GR8736p=>g00QIR9/26p=5%16,05p=8g00RFR:?356p=6f2R;1256':p=Qf5R<f4R='0f3R>'212;5'S/:6p=712;5/:6p=<1295/:6p=91:56,:;p=D10;5/26p=?1a:6p=AP:P4P:P:P0P=P1P>g00j9P;P5P6M<cp=gP4P:P6P1P5P;P>P=P<f6R0f7R?f8R@M<Zp=VP:P5g00TkP6CPp=KP5g00URRAg00V1RBPBg00VQRCP6g00W1K00p=EP>PAPBPBPCP;P5P6Gkp=MP4P:P:P:P1P1P<P=P>P;P5P6M<cp=wP;PAPBPBPCP5P6Fjp=\g00WQ#Og00XPR1#FRD#FRE#FRF#F#F#FRG#]#XRH%]F#XRF$07[%OFRIf=RJf<RKf:RLP5H03f9RM%;>7s;P314F>14FL'@%;=RN=BF>ABFNL53If;RN,4F%;K'@%;L=WFK9BFN=3IMf@ROf?RPf>RQPNPMP@PKP?Ge10O@#=93H0fDR@fCRMP?PLCC#>[[[[P614F<14FK'@%;?R?=BF0ABF?J53I14FQ%;P'@%;J=WFP9BFQ=3IKPMfBR?fAR<PQPKPNPPPLGeP3%5PRR1GJK/IO18PJ,6N18NKP@P?PM10M?RJP@%5MRS%_D%_G'oRG7QJE77<?,9N3D10@K#=93HLfHRKfGRJPNPQCC#>[P6%5<1GOP/IM%1ORN,0?,6Q18QPfERTPJPTfFRU10UTRVPJ%5URW?QVGE73<,9Q3DP31G<O/I@18M<,6P10PNPKPUPJ10JURNPK%5JR<?QNGE77<U7DR10KO#=93HQfLROfKRRPPP?CC#>[P61GM?/IU%1@RP,0U,6?%5?18?MfIRNPRPNfJRV10VNRXPR12XG,9VE73<3DP318JT,6MA?MPVPOPVPR10RVRPPO12PG,9RE75DS10O@#=93H?fPR?fOR@PMPUCC#>[P6%1JRM,0N,6TfMRT9?UMP@PTfNRM10MTRSP@12SG,9ME75DWP3P<18JKP?PMP@10@MR<P?12<G,9@E77<M10?K#=93HUfTRUfSRKPJPVCC#>[P6%5N18VRfQR<PKP<fRRW10W<RSPK12SG,9WE73<P3%1O=?RWPUPWPK10KWR3PU123G,9KE710UO#=93HVfXROfWR3PRPMCC#>[P6%1M=?TUP3fURUfVRR10RURUP312UG,9RE7103@#=93HTf[fZRUPOP@P?P<PMPT14FRRR%;3RT'@%1RRM1H93RG'6RS%Y4RP%Y:RX%15%16RY'61@561i563hXB4X14RZPRPM%AMPT1H96X1:RMP3O1P6X1:R[PMP3P3%A3DgRMM9VPJCfR\PS14F?R]14F3R3'@%1]R^%13R_'6R`PPPXPZP]P^%A^P3P_%A_M9VPVCfRVP`%UKR_%1K#5RK14FWR3#UR^%13#5R314FURU#UR]%1U#5RUf\RZ-069RX1d9Z1H9ZRP/6Z':A3:P99<Z9'SRZf],H9RPP:g00YTRa$05Rb%OaRc1R:5&04:Rd&02:Re201:9Rf1L:1Rg'K,EeRh%~BRiPhCM1}eCRhP6P;1a781{6;#>dAz:95CyR8b7b9b:X2:%56%55[^2:P6POPQO2b6bCb3b@b?b>b4b5P4PR%1W=?<YXA4RWP4PTPW18?<R<%1TR?'212<GP:P:P2P[P21256#xXB:X1:P<P<%A<P?PGP[P[%AYX14PTPGPMEwM<ZP\PSPVP`P_PKP^P3P]PUPXPZPPP:p-0RPg00Y5RZ#NRX#NRU#N,J:%t1,r:1J:U5q:1J:X1J:Z5T:5T:RZ5T:g00[gRX'[1[ZX=^ab5^aPcP:P:1R:=P;%p:C`P51R:>C`PdPePePAPBPBPCPePAPBPBPCP0EuP:%v1,L:R1g00\SR01L:ERECP,Ee5\e1KEf,EeP:P1P0PfCP,Ee5\eFnPiPe1L:D9m:gRg/KE,EePi1Kg1,EeCMCMPhP8b7b9b:X2:X;:X<:X=:W816;>,:=A3:;99<>9'SA?5;=A?;>=[[^2:^;:^<:^=:^8PP6f_RP,d9PPP5fY#1POP;PLO7b6bCb3b@b?b>b4b5C|PRPJEb14F@PNEbP6M;lWGWRWHP5P6O2n2001000000121000000W0WFP5P6O2n2001000000121000000W0WQP5P6O2n2001000000121000000W0WPP5P6O2n2001000000121000000W0WOP5P6O2n2001000000121000000W0WNWJWMWIP5P6O2n2001000000121000000W0WEXSHXUIXK:XW4XV4X\IXT:XX4W[XA:XD:XL:WYWZo"). Qed.

Lemma mc_store : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
  bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
  mem_inv segs m1 -> munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
  length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P ->
  xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
  bytes_at segs (write_to_mem m1 a xs) S src /\
  u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
  copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
  mem_inv segs (write_to_mem m1 a xs) /\ munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
  wmono segs m0 (write_to_mem m1 a xs).
Proof.
ltac2:(KReplay.run1 (kr_t_Str_tac ()) [] "h04__x1h16__sat7h24__x2h34__x3h44__x4h54__x5h61Hh72H5h83Hc0h93Hl0h:4LEN0h;4Lbs0h<7__arithh=4__ffh>8__varmaph?5__with@4cstrhA5cstr0hB5cstr1hC5cstr2hD5cstr3hE5cstr4hF1nhG2z5hH6__sat6hI1xhJ4__p1hK4__x6hL2HahM3SOKhN4__p2hO4__p3hP6__sat8hQ4__x7hR1ahS1khT2xshU1yhV2CPhW1DhX2D0hY3DSThZ2Dnh[2H6h\2HPh]3HPbh^2HWh_2Hbh`2Hcha2Hkhb2Hlhc3Hxshd3LENhe3Lbshf2MIhg2MUhh1Phi1Shj3SEPhk3SRChl2WMhm4basehn2bsho1chp2kwhq1mhr2m0hs2m1ht4segshu3srchv3xswhw2z6p%0p&0p;1p;4p;2p;3p;8p;Dp;6p;<p;:p;9p;;p;7p;Bg0000k102Tg000Pj1VTg0015k10=Tg001Sk105Tg0026k10{Tg002Xk400Tg00m0j4yTg012Yj2sTg013Pk20YTg0082R0j20Tg00;ak103Tg0140j3}Tg003PR1j16Tg004mj3=k10?Tg00n_k80`Tg006aj2GTg0078R2j2LTg00=ok10:Tg010Zk20ZTg014gj3ETg015kj3@Tg007RR3j13Tg00>MS00j22Tg00]:j2<Tg004Nj3\Tg016dk30fTg00oZj4nTg008OR4j21Tg00eZj4lTg017?mD0bTg00e<j6Zk70jTg009jj1{Tg018=j3zTg00`Bk20_Tg00`ek30^Tg00>ij4jTg00?Pj1[Tg00gQk20;Tg00h3j2CTg0194k20]Tg019\k30\Tg01:@k20[Tg00=Uj2iTg005Gj1TTg00J2k209Tg00@Sk10XTg00AOk10WTg00Amk10VTg00C;k208Tg00DAk10UTg00BXk207Tg00MXj1hTg00ENk20TTg00F0k20STg00F\k30RTg00G;k40PTg01:ak30OTg0117k10NTg01;Dk40MTg00O6l<pTg01;gk30JTg01<Mk60ITg00Gmk40GTg01=5m:0yTg00J[k10xTg00K9k20wTg00KZk30vTg01>9m90uTg0040j3~Tg00d>m;0tTg01?>k80sTg00IVk60rTg01@=k60qTg01A:k30pTg01ATk30mTg01BLm90lTg01CIk60kTg00mek30DTg01DFk40BTg00<Aj3mTg00O[mB0CTg00fOk20iTg00flm<0ETg00=9k20hTg00LCj3|Tg00Llk20FTg00@5k20nTg00A1k40oTg00Dcj4cTg00PAk701Tg00C^k30ATg00Pej8kTg00hMk60eTg00i1k70dTg00iUk70cTf2R5f1R6f0R7#640Dp=tg00RFR8P8P6P7H0Bp>0Qf4R9f3R:;m5?z67p>0zg00QgR;1<56;=7p=AA~5679\9:p>0@g00QIR</27p=4%37,06p=:A=867p=51267,15p=rf5R=/09/2:1256'C/17p=?1256/17p=>12<6/17p=u1167,15p=_f6R>A~5679\9:7==p=H1067#{9=:5p=PP8P8P5P6H0B=m:7p=Ff7R?/s>Az=9:A}567'1'1p=RP?P>P=P9Cy%66:0D:5/17'1p=KP9P:P5P6H00/17p=J12<51267'1p=Q1056/27p=;1256/C7p=]A=;67p=fA\5679=9:p>0gg00ZgS01g00[GR@7=7p=bP>P=P9P:P5P6P7ClClp=d1067#{p>0a1i87p=7P;P8P7P3P6P5P:P9P=P>P?f8RAM<pp=xP;P;P;P8P8P8g00SFP3P3P3P0g00SfP=P9P:P5P6P7NB0Cp>0>P;P8P2P3Q00g00TIP=P9P:P5P6P7M<pp>0<20i<7p=MP8P;P8P8P1P9P3P:g00j9P5P6P7N<0Ep=w20h<7p=UA=87<p=e20987p=WA|8679|85p=Xg00YTR1g00[gR2-0F6;m7p=D20n87p=YP8P5P6P7H0op=820787p=NP5g00URRBg00V1RCPCg00VQRDP8P6g00TkREP7Ccg00W1RFK01p=9B0A867p=OP5PBPCPCPDP8P6g00\SRGP7CcPFK01p=IP8P6PEP7Ccp>06P9PBPCPCPDP:PBPCPCPDP5PFK01P6P7Gkp=BP>PBPCPCPDP=P9P:PBPCPCPDP5P6P7GkGkp=`A|867p=^P8P6PGP7Ccp=qP8B0A856PEP7Ccp=gP;P8P8P8P3P3P=P9P:P5P6P7N<0Ep>0LP8P8P8P8P8P8P0P7P6P5P0P:P9P=P>P?PAf9R0NB0Cp>0K20F72p>0HAm167p>04P6PBPCPCPDP7J0ep=vP5PBPCPCPDP6P7K0dp=SP5PBPCPCPDP6P7K0cp=aP:PBPCPCPDP5P6P7Gkp=og00WQ$02g00XPRB#VR2#VS02#VS03#V#V#VR3$0=S04$05REQ03$0=$05RG$0{[S05Q05&02GRFf?RHf=RIf<RJP0H00f@RKf>RLPJP:Cyf;RM?t9=fBRN/sK20Y88RO10HL-0QH&03ORPPNfARQI0zfDRRfCRS;}N%6KRT9AGHPGPHPG%6LPKI0@==FIPRPSPNPHPIPJPKPML0`P4%4KRU1GLI/LQ1:KL,5J1:JIfERVPSPR10RSRWPV%4RRX&0:2RY&0:3R3+0ZRZ7rWE?7>S,uJ3_PFPMPGPLPGPHPKFHAAGJHPEPJfGRJPHCPfLRMfJRW?EILR[fIR\fFR]PMP[fHR^A@HTLRTP]PT%3QRT,0KR_PMP[POP^10^JR`PPCFfKRaP[PMPaP[GRGKDJ[[[P7%4N1GQK/LR10ST,5H1:HKP^P]PJ10J]RTP^%4JR[?rTZE?7>],uH3_P41GNQ/LV1:RN,5KP\PJP^P`P\%4^RT?r`ZE?9>_J7_UPFPHPGPNPGPSPRFHAAGKSPEPKPaPSCPfPRHfNRU?EQNR_fMR`PWPHP_PM%6R=@SNRNPWPN%3VRN,0RRbPHP_POPM10MaRcPPCFfORdP_PHPdP_GRGKDJ[[[P71GRS/LJ10JN,5S%4S1:SRPMPWPa10aWRNPMAQaNZE?7>W3_P41:^],5R12baP`PaPMPcP`AQMcZE?5_XPFPSPGP]PGPJP^FHAAGRJPEPRPdPJCPfTRRfRRS?EV]RXfQRcPUPRPXPH%6^=@J]RbPUPb1:^\RbPRPXPOPH10HdRNPPCFfSR_PXPRP_PXGRGKDJ[[[P7%3^RX,0W,5]A;JXUPHPUPd10dURXPHAQdXZE?5_[P4PTPcPdPHPNPcAQHNZE?9>bdPFPJPGPWPGPaPMFHAAG^aPEP^P_PaCPfXR^fVRb?E\WRNfURTPSP^PNPR%6M=@aWR[PSP[1:M`R[P^PNPOPR10R_RXPPCFfWRePNP^PePNGRGKDJ[[[P7%4W1:aMPRPSP_10_SRWPRAQ_WZE?7>SP412[_PTP_PRPXPTAQRXZE?PFPaPGPUPGPdPHFHAAGMdPEPMPePdCPf\RMfZRX?E`UR[fYRWPbPMP[P^%6H=@dURNPbPN1:HcPMP[POP^10^eRNPPCFf[RfP[PMPfP[GRGKDJ[[[P7%3d=;UTP^PbPe10ebRUP^AQeUZE?P410We12NW7]^AQ^NZPFPdPGPSPGP_PRFHAAGH_PEPHPfP_CPf`RHf^RN?EcSRUf]R[PXPHPUPM%6R=@_SRgPXPg1:RTPHPUPOPM10MfRgPPCFf_RhPUPHPhPUGRGKDJ[[[P710fWA;XWf7]XA;fXZ,ufP4%4MR412gZPFP_PGPbPGPeP^FHAAGRePEPRPhPeCPfdRgfbRU?ETbRifaRjPNPgPiPH%6^=@ebRkPNPk1:^WPgPiPOPH10HhPPCFfcRkPiPgPkPiGRGKDJ[[[P7%4NA;hNZPFPbPGPWPGPXPfFHAAGeXPEPePUPXCP1<GXRi1<GjRl'fRmPF%6fRn=\GXPGPnPjI0g<0fTPmP;P[fiRmfgRnPXP7Cn#bXF;fhRoffRpfeRqPgPkPUPjPHPhPNP[PMPfPWPePbPSPc%4H1GN[/LjRS1:HN,5MRr%3[=;MkRs10qk10gkRt/2q7]gRu%4gRv12tZRt'1Rw'1Rx'1Ry,14Rz'1R{'1P`PSP{P\PrPzPVP4PyPQPsPxPIPuPwP0PvPtP=P9ClFdFdFdP6ND0bPiP5EZPoPpPWPiCn#bPE20aq[RifjRtPoP71<GMRvCn#bfkRwAEm6[RuPoPqPwPuPn%6hS06=@N[S07PqQ07%3HRI,0hPwPuPOPn10npPPCFPtPuPwPtPuGRGKDJ]MXREPmPnPi1<GfCn#bPt10pNRf#{S08=EoMRiPnPgH00PtPiPp%6NS09=@[MRuCyS0:1:Nh9tguS0;1stiS0<POPp10pqS0=PPCFS0>?zmiS0?A}tmiS0@'1S0A'1S0B'1S0C'1PtPoPfPMPnPgPX1<G[Ri1<GgRP'f%3iRO%3PRu'5Rx&0?;Rs&0?8RQ%36%37Ry'51f6720_6740^XU;XI;R4PiPO%7ORVPPPu%7uM9xP5CjS0DPx1fiH15OIRuPsPQP4PiPOPVPHPI%7IM9xP=CjS0EPu1GUjRI/Lq%3URV%3jRz'0Rr%3qR\'2R{PIPrPUPV%7VPjPz%7zJ0>PqP\%7\J0<P`CjS0FP{1<GnR`%6oR\'f%3`Rz%Mo'5RVPsPQP4P`Pz%7zP\%M7XI8S0GPoO1P7XI8R\Q0GPoPo%7oDwM9xPeCjS0HPV%[kS0I%3k#4S0J%[lS0K%3l#4S0L1<GkRl#[S0M%3l#4S0N1<GwRl#[S0O%3l#4S0P%[oS0Q%3o#4S0RflRl#[S0S%3l#4S0TfoRz-0;<S0U%Uz%MzR`/5z'1%e`9>z<'CS0VfpR`#MS0WP820]Y3S0X%UYR4%43%UZ[RQ[S0Y%4YRsg01DfRrB0\Y36UWLS0Z%4Z\r^LsS0[P6g01EB20[<Y'iP4eO1S0\PQg00Y5R4#TS0]#TS0^#TRs#TS0_#WS0`%WsS0a20984S0b3XS0c&031R4'D&021S0d%Y9S0e&0X8R1785S0f%Y:786&0W8S0g&0V8Rs2088<RrQ02#NR359sS0h&0UCRCPs2078BRI99srS0iPCPs%N2RS99srS0jPCPs%hBR|#NR}/O3S0k9IsSPCPsPs206r}PC1OISR~99srDBF`F`20TsDS0lP7P5Q01/i@20S75#bdB0R8<6H0PS01b=b>b?X08X28X38X48%4:S0m%46S0nQ0m10=>R@,59%4>%4@[[[[[^08^28^38^48P7%3`frfnRDfvS0oP?PJP_PePhO9b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;S0pQ0DPxQ0EPuQ0FP{Q0HPVQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WP8Q0XQ0YQ0ZQ0[Q0\PQQ0aQ0^#WS0^Q0]#WS0]Q0b'^3XS0q/D4Q0dQ0e9815%Y=S0r981:S0s786Q0gPsPs%V|#NS0t,q}PCPsPs%h|#NR|2088YQ0460O8RY5gIPCPsPsQ0t=gS|PC1O~}S0t=9sYDBDBDBQ0lQ01b=b>b?X08X28X38X48X58155:A;6=ZA;:=>10:9S04/0=S0u/2Z[[[^08^28^38^48^58P7fuS0v%3zS0w1<Gl#3S0xPDQ0oPLP]PdO8b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;S0yP;%6qR]10oy10nhRlA;lOo3]XF;%3]S0z,0nS0{/2fRl%3vRO,0fS0|/2nRz'C%MqS0},0nRZ/2fRY/CzPlPzPYPzP8P8Q00P\Q001267$0NXU8XI8Q0{PZP\P\P\P8P8g01Eh1067H0M#7Xq8XF8PnPn%7nQ0zQ0}P\P\%7yXI;P]Q0}P\Q0GPqPq%7qDwS0zJ0LN:0KPfPf%7fM<pp-0Rn/iz:0JzzJ0IQ0DPxQ0EPuQ0FP{Q0HPVQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WP8Q0XQ0YQ0ZQ0[Q0\PQQ0_#TRz#TRZ#T#W%WZRZ%WzRzQ0q'^3X$0HRYQ0c,^zQ0`Q0^Q0]'^5XZ/D4'D-04Y+04Q0d%Y>S0]?891?851%Y??8=1?8:1786Q0gPs1vs0S0cQ02#h#NRY9IsS5SsA9sYrAIsSr5Ss5asPCPs%h2#NR2Q03#NRl5IsPCPs1OIY=9s}1O}Y=9sI5asPCPs1O3l=9sYPCPsQ0hPCQ0k99s~Q0k/O2=9sI5asCoF`F`Q0lQ01b=b>b?X08X28X38X48X58XK8XQ8XJn156>,1?12><S0k%e6'1'C15=>105AA;9A57]9A;>A0%4?S0h10?ARYA;Y0=5]@[[[[[^08^28^38^48^58^K8^Q8^JnP7Q0v#UQ0vQ0wQ0xPDQ0oP9fwRYP=PLPaPdP_O=b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;H0GPPPREZN:0yQ0:Q0CPtPoPpP[PNPMPWQ0DPxQ0EPuQ0FP{Q0HPVQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WP8Q0XQ0YQ0ZQ0[Q0\PQP4Q0d%Y6Q0gPsQ0iPCQ0iCoQ0lQ01b=b>b?X08%47Q0n[^08P7PDP_O2b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;S0nP;PPQ06/Gi/L7XF;RWP;P]PWQ09/GvS0i/L]%MNS0C/0ORWQ0}'2Q0iPWQ09Q0CP\Q0GPNPN%7NDwPvPO%7OJ0>P]Q0}Q0zJ0<Q0DPxQ0EPuQ0FP{Q0HPVQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WP820;<t%Ut%MtR]/5t'1%e]9>t<'C%MwP8Q0XQ0YQ0ZQ0[Q0\PQ&0xB-0w8Q0`60v8RBQ0q5XzRw,^ZQ0aQ0^Q0b3XR]9XzBRB1^ZB/D4'D,Dw'DQ0dQ0]?8>1?851Q0eQ0r78:786Q0gPs1vsAAIsI25SsQ0cAIsIr5Ss5asPCPsf:,vsAIs}l5SsA9slrAIs}r5Ss5asPCPsPs1qS|PCPsPsAg2|lPCPsPs206r2PCA9s~}DBDBDBF`Q0lQ01b=b>b?X08X28X38X48X58XK8XJnXNnXOn157:,1>%e7,1?'C15:>R2,10Q0k%e:'1'CA;>?AQ0h12@?[[\2[[^08^28^38^48^58^K8^Jn^Nn^OnP7%UY12`<%U`PYfq#3P`P>1<GD#3P9P=P?PKPcPTO>b<bPb1bPbwb[bGb7bEbDbCbBbAb@b:b8b9b;H0GPPPREZRRPiP5EZN90uQ0;Q0BP;PvQ0710hy5tqXS;PgP[PNPMP^Q0nP;PhQ06=~GqRq9\G7==F[XF;PFPGPhPGPHPjI0@A\GHq==F7XTFPgPjPUPkPHPhPNP_PdPaPJN;0tPMP=EZPvP9EZPRL0sPhP9J0rQ0<Q0APtPoQ08PMPeP7J0qQ0?Q0@Q0>PmPoPfPMPbQ0pQ0yQ0|Q0='29>pfg01FLQ0DPxQ0EPuQ0FP{Q0HPVQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UQ0VQ0WP8Q0XQ0YQ0ZQ0[Q0\PQ1D]4Q0dQ0fQ0s786Q0gPsPs1q}|PCPsPsAgS|3PCPsQ0jPCA9sI~Q0t1OI359s5SsCoDBDBQ0lQ01b=b>b?X08X28X38X48X581559A;5=9Q0mQ04Q0u10:>'25>:[[[^08^28^38^48^58P7Q0wQ0vQ0xPDQ0oPLPdP_O8b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;40pQ0>@0mfOeN90lPtPmPoQ08PMPTJ0kClFdFdWMPXP5P7K0jbMbeWLWbWcWZWXP6P7O2n2001000000121000000W6WjP6P7O2n2001000000121000000W6WaP6P7O2n2001000000121000000W6W\P6P7O2n2001000000121000000W6W]P6P7O2n2001000000121000000W6W`P6P7O2n2001000000121000000W6W_P6P7O2n2001000000121000000W6W^WdWlWgWfWVWYWkXREXTFXnFXh8XS;Xo;XvFXm8Xp;WuXF8XW8Xi8WsWrWto"). Qed.

(* [comment removed for export] *)
Ltac ld1 HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in
    pose proof (mc_read1 segs m S src k base xs c i a _ SRC HW
                  ltac:(unfold ld_facts; lia) ltac:(reflexivity) ltac:(addr_tac)) as RD;
    zstep; try clear RD;
    lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end
  end end.

(* [comment removed for export] *)
Ltac ld4 HW c w :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in let Ew := fresh "E" w in let Lw := fresh "L" w in
    destruct (mc_read4 segs m S src k base xs c i a SRC HW ltac:(reflexivity) ltac:(unfold ld_facts; lia) ltac:(addr_tac))
      as [w [RD [Ew Lw]]];
    cbn [firstn skipn] in Ew;
    zstep; try clear RD
  end end.

(* [comment removed for export] *)
Ltac zify_bytes :=
  repeat match goal with
  | |- context [bv_unsigned ?b] =>
      lazymatch type of b with
      | byte => pose proof (byte_range b); generalize dependent (bv_unsigned b); intros
      end
  end.
Ltac solve_le K :=
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first [ apply le4_of_mod32; [reflexivity|] | apply le1_of_mod8 ];
  cbn [map le_val]; rewrite ?unsigned_lit_wrap; rewrite ?lw_unsigned4;
  zify_bytes;
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?bv_swrap32_eq, ?bv_wrap32_eq by lia;
  lazymatch K with
  | 0%Z => idtac
  | _ => first [ rewrite (lor_add _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
               | rewrite (lor_add' _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ] ]
  end;
  Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
                lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.
(* [comment removed for export] *)
Ltac by_le K :=
  symmetry;
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first
    [ lazymatch goal with
      | |- le4 (Z_to_bv 64 (Z.lor (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _) _)) = _ =>
          lazymatch k with 24%Z => apply merge_a24 | 16%Z => apply merge_a16 | 8%Z => apply merge_a8 end
      | |- le4 (Z_to_bv 64 (Z.lor _ (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _))) = _ =>
          lazymatch k with 24%Z => apply merge_r24 | 16%Z => apply merge_r16 | 8%Z => apply merge_r8 end
      | |- le1 (Z_to_bv 64 (Z.shiftr _ ?k)) = _ =>
          lazymatch k with 8%Z => apply lwb1 | 16%Z => apply lwb2 end
      | |- le1 (sext _ _) = _ => apply lwb0
      end
    | solve_le K ].

(* [comment removed for export] *)
Ltac cst_core HW c k bytes_tac SF :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
  let kz := eval vm_compute in (Z.of_nat k) in
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
     replace bs0 with xs by bytes_tac;
     let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
                 ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
       as (SRC' & DST' & CP' & MI' & MU' & WM');
     change (Z.of_nat k) with kz in CP';
     clear SRC DST CP MI MU WM SF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
  end end.

(* [comment removed for export] *)
Ltac cst HW c k bytes_tac :=
  lazymatch goal with SF : st_facts _ _ _ _ c k _ _ |- _ => cst_core HW c k bytes_tac SF end.

(* [comment removed for export] *)
Ltac st HW c k bytes_tac :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
    let a := cur_mem_addr in
    let SF := fresh "SF" in let SOK := fresh "SOK" in
    assert (SF : st_facts S D n base c k kw P) by (unfold st_facts; lia);
    pose proof (mc_store_ok segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
    zstep; [ cst_core HW c k bytes_tac SF | .. ]
  end end.
Ltac st1 HW c := st HW c 1%nat by_byte.
Ltac st4 HW c := st HW c 4%nat by_lw.

(* [comment removed for export] *)
Ltac by_win HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
    first [ rewrite (window_sub src xs base k c 4 _ HW) by lia
          | symmetry; rewrite (window_sub src xs base k c 4 _ HW) by lia ];
    cbn [firstn skipn]; first [ assumption | symmetry; assumption | reflexivity ]
  end.

(* [comment removed for export] *)
Ltac cp_norm P' :=
  lazymatch goal with CP : copied ?src ?bs (Z.to_nat ?P) |- _ => replace (Z.to_nat P) with (Z.to_nat P') in CP by lia end.

(* [comment removed for export] *)
Definition mc_inv (segs : list MemImageType.Segment) (S D : Z) (src : list byte) (W : list ivl)
    (m0 m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
  bytes_at segs m1 S src /\ u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
  mem_inv segs m1 /\ munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

(* [comment removed for export] *)
Ltac inv_tac :=
  lazymatch goal with
  | |- mc_inv _ _ _ _ _ _ _ _ _ =>
      split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
      lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
        first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
  end.

(* [comment removed for export] *)
Ltac use_side :=
  first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
  try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
  try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Tactic Notation "use" uconstr(L) := eapply L; use_side.

(* [comment removed for export] *)
Ltac finish2 :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac mc_fin :=
  lazymatch goal with
  | DST : u8arr _ ?m1 _ ?bs, CP : copied ?src ?bs (Z.to_nat ?P), L : length ?src = _ |- _ =>
      let E := fresh "E" in
      pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
      apply rw_cells_of_u8arr in DST; rewrite L in DST
  end;
  finish2.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac lstep := zstep; fix_lit_store.
