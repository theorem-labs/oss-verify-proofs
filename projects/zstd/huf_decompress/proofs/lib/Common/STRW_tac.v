(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_merge.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_STRW_tac () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02c59OSSVerify5KrLib6Common8STRW_tac8ld_factsC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Common6StrFun:window_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib3Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic7f_equalC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun:window_subC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun6copiedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8STRW_tac8st_factsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib6Common6StrFun@u8arr_store_ok_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib3Mem9upd_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib6Common8STRW_tac;mc_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFunAu8arr_write_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun;copied_updZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00".
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
ltac2:(KReplay.run1 (kr_t_STRW_tac ()) [] "h04__x1h14__x2h21Hh33Hc0h47__arithh54__ffh68__varmaph75__with84__x3h94cstrh:5cstr0h;2HWh<2Hah=2Hbh>2Hch?2Hih@2HnhA1ShB3SRChC1ahD1bhE4basehF1chG1ihH2kwhI1mhJ1ohK4segshL3srchM3xswp;1p;4p;3p;5p;2p;:p;6p;;p;<p;Bp;7p;8g0000j1FTg000Pj16Tg0015j1JTg001Sj1HTg0026j1OTg002Xj4mTg003Mj1MTg003mj3_Tg004Kj3]Tg004jj30Tg005Dj1@Tg005cj5WTg006`j29Tg0077R0j28Tg007QR1j11Tg0081R2j22Tg008NR3j2LTg008ij37Tg009Gj25Tg009ij1CTg00:Xj4QTg00;]j1KTg00<=j3BTg00<]R4j2^Tg00=5R5j2ITg00=Qj2;Tg00=kj1[Tg00>IR6j2ATg00>ej4XTg00?Lj1>Tg00@1j2GTg00@Oj1VTg00@mj4PTg00AKj1UTg00Aij1TTg00BTj2?Tg00C7j2STg00CZj3RTg00D=j1qTg00D_j4ETg00EJj2pTg00Elj2oTg00FXj3lTg00G7j4kTg00Gij4iTg00HTl:hTg00IQj6gTg00Imj2<Tg00JVj1fTg00K4j2eTg00KUj3dTg00L>j3DTg00Lgj2cTg00MSj1bTg00N8l;aTg00Nnl<NTg00OSlBjTg00P9j7`Tg00P]j8nTg00QAR7f0R8'Ap=3g00Q_R9g00R>R:P4P1P5g00R\f5R5f4R4f3R;f2R<f1R=P8M<Np=\P9P9P9P:P:P:g00S>P1P1P1P2g00S^P5P4P;P<P=P8MBjp=ZP9P:P0P1P6g00TAP5P4P;P<P=P8M<Np=YP:P=g00TcP8CEp==P=g00UJR6g00UiR1P1g00VIR0P8g00ViF`p=4P;P6P1P1P0P<P=P8Gnp=:g00WI#Fg00XHR6#6R2#6#6R>#6#6#6#J#HR?%J>#HR>#OR@[%F>RAf:RBf9RCf8RDf7RECmf6RF#M=_>D9]>E=0A5PEP5g00XmRG#@RHPDP4DWP3%3D19FH/8C%1F,2D90:5'LA7>DE15>450@f=R4/2E#C90?F%OAR5f@RIf?RJPEPHCQ%K>RK9B>F,5A30[[P8%3B19CHf<RL'8f;RM%1C'290:D'LP319BH/84%1B,2L90:CA7>LM15>D50@fARD/2M#C90?BfDRCfCR3PMPHCQAB>BK,5A505[[P819LH/8J%14,2J90:Lf>R597>J15>M50@12C5#C90?4fGRKfFRBfERNPCPJP4P5PLP@A7>DI%MI97>N=0@8XJ@PCPDfBR@P3PIPJPMPE1^I3%1IRE%13RJ'IPIPE1;:ERLP3PJ1;:JR5E\19IHRO/83%[6RP,2ERQ/AJRRPOPQPIPEPLPHPP1;:PEZP3PJP5EYP;CXR5PR%>C%1CRC#3%>@%1@#3g00YLR@#KRJ%F@RLP:1G:<REP=%V:CP%U:RI%T:RQ1?:6RO1S:P5R:1?:2R2'=,4Q%q1R1P:POg00Z8P2CE,4QC:1pQ0R0P8P<g00Z_RSg00[?RT';1o8<=0STdAl:7=CkRTb5b6b7X0:X1:128P/A=1I=<[^0:^1:P8%1KPCP;O3b4b:b9b3CiP<M:h15>4P=EgP5PR%>D%1D#3%>N%1N#3%@HRN#@,<:%f6,e:1<:N5d:1<:H1<:G5D:5D:5D:g00[_'c=B@JPLP:PEP=1G:;CPPIPQ1S:7R7%b6,?:R6'=,4QP1PQP:POg00\KAR:26CE,4QP1PQ1=72,4QP11=7O,4QC:C:C:P0PTb5b6b7X0:X1:X8:%3<12<;90:=%3;R;P;[[[^0:^1:^8:P8PCPBP3P<PFPMO6b4b:b9b3P8M;aW<W@W?W>P=P8O2n2001000000121000000W2W=P=P8O2n2001000000121000000W2W;WBXD>XC?XG:XF9XMAXE:XH9WLXA:WIWKo"). Qed.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
  ld_facts base c 4 kw i -> a = wa (S + i) ->
  exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_STRW_tac ()) [] "h04__x1h14__x2h24__x3h34__p1h44__p2h54__x4h64__x5h74__x6h81nh92HWh:2H3h;3HL0h<3Hc0h=7__arithh>4__ffh?4__p3h@8__varmaphA5__withB4__x7hC4cstrhD5cstr0hE5cstr1hF5cstr2hG1whH2z3hI1HhJ2H4hK2L0hL1xhM2z4hN2H5hO4__p4hP4__x8hQ4__x9hR1ahS1mhT2z5hU2H6hV2HLhW3HW0hX2HbhY2HchZ2Hih[1Lh\1Sh]3SRCh^4baseh_1ch`1iha2kwhb4segshc3srchd3xswhe1yhf2z6p%0p&0p;1p;4p;3p;2p;5p;6p;9p;;p;<p;Bp;7p;8g0000j1{Tg000Pj1STg0015k109Tg001Sj1~Tg0026k10?Tg002Xk40XTg003MR0j1LTg003mj3ITg004Kj3TTg004jj33k10>Tg00]2j21k10OTg005Dj1@Tg005ck50]Tg006`j2FTg0077R1j2ETg007QR2j10Tg0081R3j22Tg009ij1[Tg00:Xj4cTg009Gk208Tg008NR4j2:Tg00]Rj2wTg00]lk60NTg00^Ij2GTg00^`k303Tg00IQj6xTg00_Bj2fTg00_Yk300Tg00>IR5j25Tg00=kk10@Tg00>ej4_Tg00`:k20ZTg00`]k30YTg00a:j2ATg00aWR6j2VTg00?Lj1QTg00b4k20;Tg00=5j2eTg00JVk10WTg00K4k20VTg00KUj3dTg00Imk20:Tg00;]k10UTg00@Ok10STg00AKk10RTg00Aik10QTg00MSj1mTg00D=k10PTg00BTk207Tg00bVk306Tg00C7k205Tg00EJk20MTg00=Qk202Tg00Elk20LTg00FXk30KTg00G7k40JTg00Gij4tTg00c9m90GTg00d3m;0FTg00e0j6rTg00eNj4}Tg00eik40ETg00fCk20DTg00f`m<0ITg00OSlBzTg00Nnm<01Tg00gEk20CTg00ggj2qTg00L>j3kTg00Lgj2nTg00<=j3aTg00@1k20BTg00@mk40ATg00D_j4]Tg00hAk60TTg00P9j7YTg00hej7|Tg00CZk30\Tg00P]j8yTg00iIk70[Tg00Q_R7f1R8f0R933p=7g00QAR:/59p=9f2R;g00R>R<?389':p=\A3<89p==20D:9p=4202<9p=6P<P7P<P<P0f4R0P2f3R=g00imP;P8P9N<0Ip=iP7P7P7P<P<P<g00S>P2P2P2P3g00S^f5R3P0P=P;P8P9MBzp=bP7P<P1P2P5g00TAP3P0P=P;P8P9N<01p=gP7P<P9P2P8P;P=P0P3f6R5f7R1f8R>N<01p=pP7P7P7P<P<P<g00jZP2P2P2P5g00k:P3P0P=P;P8P9MBzp>0=P7P7P7P<P<P<g00kaP2P2P2P6g00lAP3P0P=P;P8P9MBzp>0<20C:9p=U1e:9p=?A3<9:p=PA3<=;,:0158:/:9'qp=NA3<;8,:=/q9p=O20:<9p=>Ak<899k<;p=8Ak<89p=;g00YLR6g00[_R2,n;1n82=a693ap=^20B<9p=JP<P;P8P9H0Ap=<207<9p=HP<P8g00Z8P9C]p=lP8g00UJR?g00UiR@P@g00VIRAP9J0Tp=WP=P?P@P@PAP;P?P@P@PAP8g00ViRBFYP9F|p=RP<P8g00\KRCP9C]p=CP=P?P@P@PAP;P8P?P@P@PAP9PBFYF|p=ZP;P?P@P@PAP<P8PCP9C]PBFYp=KP;P?P@P@PAP8P9F|p>04B0\<89p=DP;P?P@P@PAP<P8g00TcRCP9C]PBFYp=vP3P?P@P@PAP0P?P@P@PAP<P=PCP;C]PBFYP8P9Gyp=BP0P?P@P@PAP=P?P@P@PAP;PBFYP8P9Gyp=jP3P?P@P@PAP0P?P@P@PAP=P;K0[P8P9Gyp=M1:;8/q9p>0HA3<9:,:8p=o159:p=u1n82=a69p=`P<P8PCP9C]p=hAk<89/n2p=sAa6899a6;p=Xg00WI#{g00XHR2#SRC#SR?#SRB#S#S#S$09#~RD&09B#~RE$0?[%{ERFf9RGP>P1P5H0X%L3=IE19TE5=3F011E3/71P1P3g00XmRH#@RI#@RJ#@RK#@RLP>P0I0]P4%9>1F5L/EG%05,2>7\3f<RM/25#[93D3&0?FRNf@ROf?RPP1PLCc208F9RQ33f:RR9IEG9TEL93F911E9/7LRS':':XGF,wF[P9%9R1FGL/EMf;RT%0G'27\>P41FRLf=R4'E%0R,2M,=G12OR#[93DGfDRUfCRVPTPLCc=3NQf>RW9IE49TEL93F9/:S':XGF,wF[P91FML/EP%04,2P,=M12V4#[93DMPD12UW#[fHRXfGRYP8PLCc=3NQfARZfBR[5IE9TEL93F9/:SS00':XGF,wFXRDPFP7&0OE%LZRS=IEV9TE[R\POPTJ0N11E\11EO'7P7%L[R\=IEUR]9TEV,1E11E[R^,79X87P911E],GVR_B03EV]Ex11EZ,7_P7%LVR_fER]5IE,1E1G]911EVR`'7X87P911E]Ra/f_RbB00E_]Ex1GUb/7^P7P`fFR^11EYRb%L]R_'f'G/79X87P9P]P4Ex11E^%LU'f,G]/7]1F_^Rc/Eb%4]Rd%0^Re'2Rf%0bRg'5PcPfP_PdP9XL<Rd%49XL<R_P]P]%6]DiP^Pe%6eRfEbPbPg%6gEg1FVLRc/E^%0VRh&0@?Ri'2Rj/5eRkPcPjPVPh%6hS01PLPi%6iRjEbP^PePfEgP5C_Pk17aY%0aRk%0YRf'=Re&0>7S02&0><Rc%08%09'=178920Z8940YXe7XL7RlPaPk%6kPYPf%6fM9pPPC_PefIRe,1ERf%LYRk'fRa,GXRm/7X%0XRn%0fRo%4YS03'A#4'V/=nRpQ02PcPlPm1A89#4XS<X8<S04PoP_PYO1RmO2Rq,VnPXPn%6nRrPaPqQ04PfPo%6oPkPmPdP_PYPY%6YDiK0=J0<PXPnPrM9pP;C_Pp%Qb%9gfKRg,1ERb#Q%0b#9%QX%9nfLRn#Q%0nS05#9%Un%?n%4nRbPnPn%PbDNfMS06#4P<fPRp,1E#0S07/A9Rr#U%?r%4rRmPrPr%PmDNfQRm,1E#0/A8#4P<%0mRm00;91em91Vm9RrPm159m?\r9COfRS08#0/V8P<p-0Rr%@LS09#>Rk%>LRo%>KRK&0W2-0V<Rf%>JRJ5d<Rq%>IRI383820:<HRH,;q98koA8koH1;KI98ko&0U6Ra3^3^%{6R6%J3S0:&0S<Rs7<5%J0Rt7<;%J5S0;?<5s?<=s7<8&0R<Ru&0Q<RvPvPvPv%HCRw%m?#HRx'l1Wv>CRPv1WvGS0<Pv%HBRB/CxCZ&0P@R@PvPvPv1WvRS0=Pv%m2Ry#HRz207<2R2606<,CxCZ1WvTS0>205<:R{9KvxS0?604vP@PvPvP{%Sy#HR|P@PvPv1CBwP@PvPv205<iRB,D|PwP@1D2w=vvzEBDjEBEMEM20MvARAP9P;g00Z_R}g00[?R~+0220L9;=3}~dB0K<:8H0JR:b>b@bAX0<X1<X2<X5<X6<X7<X3rX4rX?rWO1e83A\10380H5PGP51A=81oR5CO%931=10121iS0@/531235/51[[[[[^0<^1<^2<^5<^6<^7<^3r^4r^?r^OrP9fU,1E#0R~/A3R}#u%?}fTS0A#0R},5=1=8}P=P8PmP~P}P3P;P0P>PTP4O?b=bTbNbMbJbHb:bFbEbDbCbWb;b<Ctb9b9b9b91FS[/E`PFPXPY12^O#[PLCc=3NQQ00':XGF%LPRQ=IEURS9TELR}PYP^12]P#[PLCc208F}53NAIEOZ9TEL93F}S0011E}S0B/7LS0C':PYP^P]PUPPPLP41F\VRY11EUR}'E%4[/2h%0}RN'5R~PYP_P[O1RY/2hP\PYPdP_P[P[%6[DiPVPhQ01EbP}PN%6NS01EgP9C_S0DP~1FZLS0E/EU%0ZRh/2iRY%0UR\'5RmQ0EPYPZPh%6hPLPiPjEbPUP\%6\EgP0C_S0EPm17`]%0`R\%0]Rh'=RYQ02PcPlP`P\%6\P]Ph%6hM9pP4C_S0FPY%Q}S0G%9NS0H11EXRX#QS0I%0X#9S0J%Q]S0K%9hRh%QeR]%0e#9RX%Ue%?e%4eR\PePe%P\DNfJR\#4P<1;IHR`98Kq/`aP6%J;%J=7<8PuPvPvP{PzP@PvPv1Dwz,C2P@PvPvP{PwP@Avv{2EBDjEBPAP:b>b@bAX0<X1<X2<%9;12;=,=8%9=RqPq[[[^0<^1<^2<P9%0\PnPeP0PMPZO6b=bHb:bFbEbDbCb;b<bK1FQLRe/E}%4PRn/2iR\/5NPeP\PQPnPdP_PPPP%6PDiS0LPLPiPjEbP}PNQ01EgQ0DP~Q0EPmQ0FPYQ0GQ0HQ0IQ0JQ0KPhP]PX%U^S0M%?^%4^R_P^P^%P_DNS0NQ03P<%Ug%?gS0O%4gR_Pg%ugR^/o_COPbP<Q09#@Rb#>R_9d<fRd1;JH98oK78kR\%@bRb#>ReA8KJ`98dkRd';1;e\=^da3^P6Q0;9<t;Q0:%J1R`7<=7<8PuPvPvPvPv1l{zAKv|zCRPvPv1hz{AKv|{CRP@PvPvPvQ0<Pv%H?R?,C2CZPvQ0=Pv1C2{CZP@PvPvP{%mCRC#HRqP@PvPv1DqB%my#HRyP@PvPv1D|yPwP@PvPv1Dzq,C?P@1D2B=vvwDjEBEBEBEMEMPAP:b>b@bAX0<X1<X2<X5<X6<X7<XB<X3rX4r%?;P3P;P;%P3DNP>P8P01oG8CO%95Q0@/5G12GR/53121G,=>125i/51[[[[[[^0<^1<^2<^5<^6<^7<^B<^3r^4rP9P^Q0OfOR^#0P8Q05PgfNRgQ07P=P;P0P5PRPTPWO?b=bMbJbHb:bFbEbDbCb;b<bKCtN90GQ00Q0CPUPZP[PVPOPLPPPMP1P=P;N;0FP711ESS0C,GL179LX87P71f}QRO1GL9/7LX871GLOS00/7L1ANn#4RV,ViRZ/=iQ02PcPlQ00PZPLPiPjPOPVQ04P}PNQ01PQPnQ0LK0=J0<PLPiPjM9pQ0DP~Q0EPmQ0FPYQ0GQ0HQ0IQ0JQ0KPhP]PXQ0MQ0NQ03P<Q06,1E#0/A9RX#U%?X%4XR]PXPX%P]DN11Eg#0/A8#4P<20;i91ei91Vi9RgPi159i?\g9CO1Vi8P<%U^%?^Rg%4^R]P^%u^RX/o]CO%4pP<%@bRb#@R]#@Rh#>RY9d<fRm1;KJ98ko78eRo%>bRb1;_H'sR_%@h#>Rh1;JI98kK98meRm';%>]9d<fR]Ad<feRf;8dRd,;Y1;eH,sbRbA8]f\R]1sfHRf1;Y]1;ho/`a9X__9^dm9Xbb'`9Xff7Xf'`7Xb3^7X_'`P6%JG?<5s9<t;%J>?<3s?<=`7<8PuPvPvPvPv1l{wAKvqwCRPvPv1hw{AKvq{CRP@PvPvPvPv%SC#HRC,lBAKv2BRuCRPvPv1hCBAKv2CCRP@PvPvPvQ0>PvB06<yxR2,CCCZPvPv1h2{AKvC{CRP@PvPvPv1WvMPv1CxzCZ1Wv4Q0?604vP@PvPvP{P?P@PvPv1D?BP|P@PvPv1Dq|PyP@PvPv1Dw?,CzP@PuDjEBEBEBEMEMEMEMPAP:b>b@bAX0<X1<X2<X5<X6<X7<XB<XP<XQ<X3rX4rX?r%?8P0P8P8%P0DN1eiGP8Pi15Gi?\8GCOPTPR1A>GR:P:%PRR:DNP4PRP31:W:CO%9112>i/5R12RT/5M12>R,=G1=>i[[[[[[[[^0<^1<^2<^5<^6<^7<^B<^P<^Q<^3r^4r^?rP9PXPgQ0A,1E#0Rg/A1#?P3P1PgfS#0P8%0pP^Q08P=P;P0P5P>PRPWPPP[ODb=bfbUbTbNbMbJbHb:bFbEbDbCb;b<bKCtQ0CB00EQUErQ0BB03ELSErC}C}H0Eb[P4P9ErWIWZWYP8P9O2n2001000000121000000WIWXP8P9O2n2001000000121000000WIWVW9W]XRDX`<X_7XdFX^<Xa7WcX\<WSWbo"). Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
  ((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
   (S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
  u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
  firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
ltac2:(KReplay.run1 (kr_t_STRW_tac ()) [] "h01Hh11xh24__x1h32H2h42L0h54LEN0h67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<4__x3h=4__x4h>4cstrh?5cstr0h@5cstr1hA1nhB1yhC2z2hD1DhE3DSThF2HPhG2HahH2HkhI1LhJ3LENhK1PhL1ShM2_HhN3_H0hO3_H1hP3_H2hQ3_H3hR3_H4hS1ahT4basehU2bshV1chW1khX2kwhY2m1hZ4segsh[3srch\3xswp&0p;1p;4p;3p;2p;8p;<p;6p;7p;;g0000j1OTg000Pj1FTg0015j1]Tg001Sj1XTg0026k107Tg00ldk403Tg003MR0j1;Tg00mVj3sTg00]2j24Tg004Kj3BTg004jj33j1YTg003mj3WTg00nOj8eTg0081j20Tg009ij1=Tg00oLj4CTg006`j2GTg0077j2ITg00=kj1_Tg010Lj2oTg007QR1j11Tg00>IR2j22Tg00fCj2HTg00`:j2iTg00`]j3hTg00>ej4fTg00?Lj1UTg00gEk206Tg00=5j2dTg008NR3j2:Tg00ggj2STg00;]k105Tg00@1j2RTg00AKk104Tg00Aik102Tg00C7k201Tg00BTj2LTg00D=j1~Tg00EJj2}Tg00=Qj2aTg00Elj2{Tg00FXj3zTg00G7j4yTg010ij1xTg00Nnl<ZTg005Dj1NTg00Imj2JTg00JVj1tTg00K4j2rTg00KUj3qTg00L>j3TTg00Lgj2[Tg00<=j3^Tg00@Oj1pTg00@mj4`Tg00hAj6uTg00MSj1vTg00D_j4PTg00iIj7nTg00CZj3mTg00Gij4|Tg00e0j6bTg011Gl;lTg00f`l<cTg00P9k700Tg00P]j8kTg00hej7jTg00Q_R4f1R5f0R633p=@g00Z_R7g00[?R8736p=>g00QAR9/26p=5%16,05p=8g00R>R:?356p=6f2R;1256':p=Qf5R<f4R='0f3R>'212;5'S/:6p=712;5/:6p=<1295/:6p=91:56,:;p=D10;5/26p=?1a:6p=AP:P4P:P:P0P=P1P>g00imP;P5P6M<cp=gP4P:P6P1P5P;P>P=P<f6R0f7R?f8R@M<Zp=VP:P5g00TcP6CPp=KP5g00UJRAg00UiRBPBg00VIRCP6g00ViK00p=EP>PAPBPBPCP;P5P6Gkp=MP4P:P:P:P1P1P<P=P>P;P5P6M<cp=wP;PAPBPBPCP5P6Fjp=\g00WI#Og00XHR1#FRD#FRE#FRF#F#F#FRG#]#XRH%]F#XRF$07[%OFRIf=RJf<RKf:RLP5H03f9RM%;>7s;P314F>14FL'@%;=RN=BF>ABFNL53If;RN,4F%;K'@%;L=WFK9BFN=3IMf@ROf?RPf>RQPNPMP@PKP?Ge10O@#=93H0fDR@fCRMP?PLCC#>[[[[P614F<14FK'@%;?R?=BF0ABF?J53I14FQ%;P'@%;J=WFP9BFQ=3IKPMfBR?fAR<PQPKPNPPPLGeP3%5PRR1GJK/IO18PJ,6N18NKP@P?PM10M?RJP@%5MRS%_D%_G'oRG7QJE77<?,9N3D10@K#=93HLfHRKfGRJPNPQCC#>[P6%5<1GOP/IM%1ORN,0?,6Q18QPfERTPJPTfFRU10UTRVPJ%5URW?QVGE73<,9Q3DP31G<O/I@18M<,6P10PNPKPUPJ10JURNPK%5JR<?QNGE77<U7DR10KO#=93HQfLROfKRRPPP?CC#>[P61GM?/IU%1@RP,0U,6?%5?18?MfIRNPRPNfJRV10VNRXPR12XG,9VE73<3DP318JT,6MA?MPVPOPVPR10RVRPPO12PG,9RE75DS10O@#=93H?fPR?fOR@PMPUCC#>[P6%1JRM,0N,6TfMRT9?UMP@PTfNRM10MTRSP@12SG,9ME75DWP3P<18JKP?PMP@10@MR<P?12<G,9@E77<M10?K#=93HUfTRUfSRKPJPVCC#>[P6%5N18VRfQR<PKP<fRRW10W<RSPK12SG,9WE73<P3%1O=?RWPUPWPK10KWR3PU123G,9KE710UO#=93HVfXROfWR3PRPMCC#>[P6%1M=?TUP3fURUfVRR10RURUP312UG,9RE7103@#=93HTf[fZRUPOP@P?P<PMPT14FRRR%;3RT'@%1RRM1H93RG'6RS%Y4RP%Y:RX%15%16RY'61@561i563hXB4X14RZPRPM%AMPT1H96X1:RMP3O1P6X1:R[PMP3P3%A3DgRMM9VPJCfR\PS14F?R]14F3R3'@%1]R^%13R_'6R`PPPXPZP]P^%A^P3P_%A_M9VPVCfRVP`%UKR_%1K#5RK14FWR3#UR^%13#5R314FURU#UR]%1U#5RUf\RZ-069RX1d9Z1H9ZRP/6Z':A3:P99<Z9'SRZf],H9RPP:g00YLRa$05Rb%OaRc1R:5&04:Rd&02:Re201:9Rf1L:1Rg'K,EeRh%~BRiPhCM1}eCRhP6P;1a781{6;#>dAz:95CyR8b7b9b:X2:%56%55[^2:P6POPQO2b6bCb3b@b?b>b4b5P4PR%1W=?<YXA4RWP4PTPW18?<R<%1TR?'212<GP:P:P2P[P21256#xXB:X1:P<P<%A<P?PGP[P[%AYX14PTPGPMEwM<ZP\PSPVP`P_PKP^P3P]PUPXPZPPP:p-0RPg00XmRZ#NRX#NRU#N,J:%t1,r:1J:U5q:1J:X1J:Z5T:5T:RZ5T:g00[_RX'[1[ZX=^ab5^aPcP:P:1R:=P;%p:C`P51R:>C`PdPePePAPBPBPCPePAPBPBPCP0EuP:%v1,L:R1g00\KR01L:ERECP,Ee5\e1KEf,EeP:P1P0PfCP,Ee5\eFnPiPe1L:D9m:gRg/KE,EePi1Kg1,EeCMCMPhP8b7b9b:X2:X;:X<:X=:W816;>,:=A3:;99<>9'SA?5;=A?;>=[[^2:^;:^<:^=:^8PP6f_RP,d9PPP5fY#1POP;PLO7b6bCb3b@b?b>b4b5C|PRPJEb14F@PNEbP6M;lWGWRWHP5P6O2n2001000000121000000W0WFP5P6O2n2001000000121000000W0WQP5P6O2n2001000000121000000W0WPP5P6O2n2001000000121000000W0WOP5P6O2n2001000000121000000W0WNWJWMWIP5P6O2n2001000000121000000W0WEXSHXUIXK:XW4XV4X\IXT:XX4W[XA:XD:XL:WYWZo"). Qed.

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
ltac2:(KReplay.run1 (kr_t_STRW_tac ()) [] "h04__x1h14__x2h24__x3h34__x4h44__x5h51Hh62H5h73Hc0h83Hl0h94LEN0h:4Lbs0h;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@5cstr0hA5cstr1hB5cstr2hC5cstr3hD5cstr4hE1nhF2z5hG1xhH4__p1hI4__x6hJ2HahK3SOKhL4__p2hM4__p3hN6__sat7hO4__x7hP1ahQ1khR2xshS1yhT2CPhU1DhV2D0hW3DSThX2DnhY2H6hZ2HPh[3HPbh\2HWh]2Hbh^2Hch_2Hkh`2Hlha3Hxshb3LENhc3Lbshd2MIhe2MUhf1Phg1Shh3SEPhi3SRChj2WMhk6__sat6hl4basehm2bshn1cho2kwhp1mhq2m0hr2m1hs4segsht3srchu3xswhv2z6p%0p%1p&0p;1p;4p;2p;3p;8p;Dp;6p;<p;:p;9p;;p;7p;Bg0000k102Tg000Pj1VTg0015k109Tg001Sk105Tg0026k10{Tg002Xk400Tg00ldj4yTg012Jj2tTg013>k20YTg0081R0j20Tg00;]k103Tg013^j3}Tg003MR1j18Tg004jj3=k10?Tg00nOk80`Tg006`j2HTg0077R2j2JTg00=kk10;Tg010Lk20]Tg014Rj3DTg015Vj3ATg007QR3j13Tg00>IS00j22Tg00]2j2<Tg004Kj3\Tg016Lk30fTg00oLj4nTg008NR4j21Tg00eNj4lTg016gmD0bTg00e0j6Yk70jTg009ij1{Tg017gj3zTg00`:k20_Tg00`]k30^Tg00>ej4jTg00?Lj1[Tg00gEk20<Tg00ggj2CTg005Dj1STg00Imk20:Tg00@Ok10\Tg00AKk10[Tg00Aik10ZTg00C7k208Tg00D=k10XTg00BTk207Tg00MSj1iTg00EJk20WTg00=Qj2hTg00Elk20VTg00FXk30UTg00G7k40TTg018[k30RTg010ik10QTg019>k40PTg00Nnl<pTg019ak30KTg01:Gk60LTg01:ok20JTg01;Wk30ITg01<;k20NTg00Gik40GTg01<\m:0yTg00JVk10xTg00K4k20wTg00KUk30vTg01=]m90uTg003mj3~Tg00d3m;0tTg01>ak80sTg00IQk60rTg01?_k60qTg01@Yk30pTg01A3k30mTg01Ahm90lTg01Bbk60kTg00mVk30DTg01C\k40BTg00<=j3mTg00OSmB0CTg00fCk20iTg00f`m<0ETg00=5k20hTg00L>j3|Tg00Lgk20FTg00@1k20nTg00@mk40oTg00D_j4cTg00P9k701Tg00CZk30ATg00P]j8kTg00hAk60eTg00hek70dTg00iIk70cTf2R5f1R6f0R7#840Dp=wg00R>R8P8P6P7H0Bp>0Sf4R9f3R:;m5?z67p>0zg00Q_R;1<56;=7p=BA~5679\9:p>0@g00QAR</27p=4%37,06p=:A=867p=51267,15p=sf5R=/09/2:1256'C/17p=>1256/17p=?12<6/17p=u1167,15p=Zf6R>A~5679\9:7==p=O1067#{9=:5p=QP8P8P5P6H0B=m:7p=@f7R?/t>Az=9:A}567'1'1p=GP?P>P=P9Cy%86:0D:5/17'1p=MP9P:P5P6H00/17p=K12<51267'1p=I1056/27p=;1256/C7p=]A=;67p=eA\5679=9:p>0gg00Z_S01g00[?S027=7p=`P>P=P9P:P5P6P7ClClp=d1067#{p>0a1h87p=7P;P8P7P3P6P5P:P9P=P>P?f8R@M<pp=xP;P;P;P8P8P8g00S>P3P3P3P0g00S^P=P9P:P5P6P7NB0Cp>0>P;P8P2P3Q00g00TAP=P9P:P5P6P7M<pp>0=20i<7p=NP8P;P8P8P1P9P3P:g00imP5P6P7N<0Ep=v20h<7p=UA=87<p=b20:87p=TA|8679|85p=Wg00YLR1g00[_R2-0F6;m7p=E20n87p=_P8P5P6P7H0op=620787p=LP5g00UJRAg00UiRBPBg00VIRCP8P6g00TcRDP7Ccg00ViREK01p=9B0A867p=RP5PAPBPBPCP8P6g00\KRFP7CcPEK01p=PP8P6PDP7Ccp>06P9PAPBPBPCP:PAPBPBPCP5PEK01P6P7Gkp=FP>PAPBPBPCP=P9P:PAPBPBPCP5P6P7GkGkp=aA|867p=^P8P6PFP7Ccp=qP8B0A856PDP7Ccp=gP;P8P8P8P3P3P=P9P:P5P6P7N<0Ep>0OP8P8P8P8P8P8P0P7P6P5P0P:P9P=P>P?P@f9R0NB0Cp>0M20F72p>0HAm167p>04P6PAPBPBPCP7J0ep=rP5PAPBPBPCP6P7K0dp=XP5PAPBPBPCP6P7K0cp=fP:PAPBPBPCP5P6P7Gkp=og00WI$02g00XHS03#VRA#VS04#VS05#V#V#VR2$09S06$05R3Q05$09$05RD$0{[S07Q07&02DRFf?REf=RGf<RHP0H00f@RIf>RJPHP:Cyf;S08?w9=fBRK/tI20Y88RL10EJ-0SE&03LRMPKfARNI0zfDROfCRP;}K%8IRQ9BDEPDPEPD%8JPII0@==FGPOPPPKPEPGPHPIQ08L0`P4%4IRR1HJG/JN1:IJ,5H1:HGfERSPPPO10OPRTPS%4ORU&0;ARV&0;2R2+0]RW7sTE>7?P,uH3ZPFQ08PDPJPDPEPIFOABDHEP3PHfGRHPECQfLRTfJRX?DGJRYfIRZfFR[PTPYfHR\AAEQJRQP[PQ%3NRQ,0IR]PTPYPLP\10\HR^PMC@fKR_PYPTP_PYGGGMDK[[[P7%4K1HNI/JO10PQ,5E1:EIP\P[PH10H[RQP\%4HRY?sQWE>7?[,uE3ZP41HKN/JS1:OK,5IPZPHP\P^PZ%4\RQ?s^WE>9?]H7ZRPFPEPDPKPDPPPOFOABDIPP3PIP_PPCQfPRIfNRE?DNKRRfMR]PXPIPRPT%8O=APKRKPXPK%3SRK,0OR^PIPRPLPT10T_R`PMC@fORaPRPIPaPRGGGMDK[[[P71HOP/JH10HK,5P%4P1:POPTPXP_10_XRKPTAI_KWE>7?X3ZP41:\[,5O12^_P]P_PTP`P]AIT`WE>5ZUPFPPPDP[PDPHP\FOABDOHP3POPaPHCQfTRUfRR`?DS[R^fQRKPEPUP^PI%8\=AH[RRPEPR1:\ZRRPUP^PLPI10IaRbPMC@fSRcP^PUPcP^GGGMDK[[[P7%3\R^,0X,5[A;H^EPIPEPa10aER^PIAIa^WE>5ZYP4PQPKPaPIPbPKAIIbWE>9?RaPFPHPDPXPDP_PTFOABD\_P3P\PcP_CQfXR\fVRR?DZXRbfURQP`P\PbPU%8T=A_XRYP`PY1:T]RYP\PbPLPU10UcR^PMC@fWR[PbP\P[PbGGGMDK[[[P7%4X1:_TPUP`Pc10c`RXPUAIcXWE>7?`P412YcPQPcPUP^PQAIU^WE>PFP_PDPEPDPaPIFOABDTaP3PTP[PaCQf\R^fZRY?D]ERXfYRbPRP^PXP\%8I=AaERdPRPd1:IKP^PXPLP\10\[RdPMC@f[RePXP^PePXGGGMDK[[[P7%3a=;EQP\PRP[10[RRXP\AI[XWE>P410b[12db7]\AI\dWPFPaPDP`PDPcPUFOABDIcP3PIPePcCQf`Rdf^RX?DK`Rff]RgPYPdPfP^%8U=Ac`RhPYPh1:UQPdPfPLP^10^eRhPMC@f_RiPfPdPiPfGGGMDK[[[P710ebA;Ybe7]YA;eYW,ueP4%4^R412hWPFPcPDPRPDP[P\FOABDU[P3PUPiP[CQfdRhfbRf?DQRRjfaRkPXPhPjPd%8\=A[RRlPXPl1:\bPhPjPLPd10diPMC@fcRlPjPhPlPjGGGMDK[[[P7%4XA;iXWPFPRPDPbPDPYPeFOABD[YP3P[PfPYCQ1<DYRj1<DkRm'eRnPF%8eRo=\DYPDPoPkI0g<0fQPnP;PgfiRnfgRoPYP7Cn#`XE;fhRpffRqfeRrPhPlPfPkPdPiPXPgP^PePbP[PRP`PK%4d1HXg/JkRK1:dX,5^Rs%3g=;^lRt10rl10hlRu/2r7]hRv%4hRw12uWRu'1Rx'1Ry'1Rz,14R{'1R|'1P]PKP|PZPsP{PSP4PzPNPtPyPGPvPxP0PwPuP=P9ClFdFdFdP6ND0bPjP5EYPpPqPbPjCn#`P320argRjfjRuPpP71<D^RwCn#`fkRxADn6gRvPpPrPxPvPo%8iS09=AXgS0:PrQ0:%3dRy,0iPxPvPLPo10oqPMC@PuPvPxPuPvGGGMDK]KXP3PnPoPj1<DeCn#`Pu10qXRe#{S0;=Dp^RjPoPhH00PuPjPq%8XS0<=Ag^RvCyS0=1:Xi9whvS0>1tujS0?PLPq10qrS0@PMC@S0A?znjS0BA}unjS0C'1S0D'1S0E'1S0F'1PuPpPeP^PoPhPY1<DgRj1<DhRM'e%3jRL%3MRv'5Rt&0?;RN&0?8Rz%36%37R4'51e6720_6740^XS;XG;RSPjPL%7LR{PMPv%7vM9xP5CjS0GPt1ejd15LyRvPNPzPSPjPLP{PdPy%7yM9xP=CjS0HPv1HfkRy/Jr%3fR{%3kRs'0RZ%3rR|'2RKPyPZPfP{%7{PkPs%7sJ0>PrP|%7|J0=P]CjS0IPK1<DoR]%8pR|'e%3]Rs%Np'5R{PNPzPSP]Ps%7sP|%N7XG8S0JPpO1P7XG8R|Q0JPpPp%7pDvM9xP[CjS0KP{%[lS0L%3l#4S0M%[mS0N%3m#4S0O1<DlRm#[S0P%3m#4S0Q1<DxRm#[S0R%3mS0S#4S0T%[pS0U%3p#4S0VflS0W#[S0XQ0W#3S0Y#4S0ZfoRm-0<<S0[%Um%NmRs/5m'1%bs9?m<'CS0\fp#NS0]P8g00XmRs#SS0^#SS0_#SR]#SS0`#TS0a%T]S0b20:8sS0c3WS0d&031Rs'E&021S0e%_9S0f&0\8R1765S0g%_:766&0[8S0h&0Z8R]2088<RSQ04#LRz59]S0i&0XBRBP]Q03-078RN99]SS0jPBP]%LARZ99]SS0kPBP]Q03#iRy#LR}/RzS0l9P]ZPBP]P]206S}PB1RNZR~99]SDFFaFa20W]CS0mP7P5Q01Q02'h20V75#`dB0U8<6H0TS02b<b=b>X08X18X28X38%4:S01%46S0nQ0110=>RC,59%4>%4C[[[[[^08^18^28^38P7fmS0o#3PmPxfsS0pP9POPIPUP^O9b;bFb6bDbCbBbAb@b?b9b7b8b:S0qQ0GPtQ0HPvQ0IPKQ0KP{Q0LQ0MQ0NQ0OQ0PQ0QQ0RQ0TQ0UQ0VQ0XQ0ZQ0[Q0\Q0]P8Q0bQ0_#TS0_Q0^#TS0^Q0c'^3WS0r/EsQ0eQ0f9615%_=S0s961:S0t766Q0hP]P]%Vy#LS0u,q}PBP]P]%iy#LRy2088VQ0660R8RO5gNPBP]P]Q0u=gZyPB1R~}S0u=9]ODFDFDFQ0mQ02b<b=b>X08X18X28X38X48155:A;6=WA;:=>10:9S06/0=S0v/2W[[[^08^18^28^38^48P7frS0wQ0Y1<Dn#3S0xPxQ0pQ08PPPTO8b;bFb6bDbCbBbAb@b?b9b7b8b:S0yP;%8rRP10p410oiROA;OLp3]XE;%3PS0z,0oS0{/2eS0|%3wRO,0eS0}/2oRL'C%NrS0~,0oS10/2eS11/CLQ0|PLQ11PLP8P8Q00P|Q001267$0QXS8XG8Q0{Q10P|P|P|P8P8g01D<1067H0P#7Xp8XE8PoPo%7oQ0zQ0~P|P|%74XG;PPQ0~P|Q0JPrPr%7rDvS0zJ0ON:0MPePe%7eM<pp-0Ro/hL:0KLLJ0LQ0GPtQ0HPvQ0IPKQ0KP{Q0LQ0MQ0NQ0OQ0PQ0QQ0RQ0TQ0UQ0VQ0XQ0ZQ0[Q0\Q0]P820JV2%UVS10%42%UW[S0{[%4VS00g01D`RLB0IV26UWJQ00%4W\L]JP6g01E<20N<V'hQ10eO1Q0{Q0`#SRV#SRL#S#T%TLRL%TVRVQ0r'^3W$0HRWQ0d,^VQ0aQ0_Q0^'^5WL/Es'E-04W+04Q0e%_>S0^?691?651%_??6=1?6:1766Q0hP]1r]0S0dQ04#i#LRW9P]Z5X]A9]WSAP]ZS5X]5f]PBP]%iA#LRAQ05#LR25P]PBP]1RNW=9]}1R}W=9]N5f]PBP]1Rz2=9]WPBP]Q0iPBQ0l99]~Q0l/RA=9]N5f]CoFaFaQ0mQ02b<b=b>X08X18X28X38X48XI8XO8XHo156>,1?12><S0l%b6'1'C15=>105@A;9@57]9A;>@0%4?S0i10?@RWA;W0=5]C[[[[[^08^18^28^38^48^I8^O8^HoP7fuRW#UPW%3mQ0W,<D#3fnRmfvP9fwP=PJP_PaPcO=b;bNbkbNbFb6bDbCbBbAb@b?b9b7b8b:H0GPMPUEYN:0yQ0=Q0FPuPpPqPgPXP^PbQ0GPtQ0HPvQ0IPKQ0KP{Q0LQ0MQ0NQ0OQ0PQ0QQ0RQ0TQ0UQ0VQ0XQ0ZQ0[Q0\Q0]P8PsQ0e%_6Q0hP]Q0jPBQ0jCoQ0mQ02b<b=b>X08%47Q0n[^08P7PxPIO2b;bFb6bDbCbBbAb@b?b9b7b8b:S0nP;PMQ09/Hj/J7XE;RbP;PPPbQ0</HwRb/JP%NXRJ/0ORWQ0~'2PbPWQ0<PJP|Q0JPXPX%7XDvPwPO%7OJ0>PPQ0~Q0zJ0=Q0GPtQ0HPvQ0IPKQ0KP{Q0LQ0MQ0NQ0OQ0PQ0QQ0RQ0TQ0UQ0VQ0XQ0ZQ0[Q0\Q0]P820<<u%Uu%NuRP/5u'1%bP9?u<'C%NxP8Q03$0x-0w8Q0a60v8RPQ0r5WVR|,^LQ0bQ0_Q0c3WRJ9WVPRP1^LP/Es'E,E|'EQ0eQ0^?6>1?651Q0fQ0s76:766Q0hP]1r]@AP]NA5X]Q0dAP]NS5X]5f]PBP]f:,r]AP]}25X]A9]2SAP]}S5X]5f]PBP]P]1qZyPBP]P]AgAy2PBP]P]206SAPBA9]~}DFDFDFFaQ0mQ02b<b=b>X08X18X28X38X48XI8XHoXLoXMo157:,1>%b7,1?'C15:>RA,10Q0l%b:'1'CA;>?@Q0i12C?[[\A[[^08^18^28^38^48^I8^Ho^Lo^MoP7ftRo#UQ0o/2<Q0o#UPo%3mQ0oP:Q0SP6P5P9PGPEP`O>b;bvbYbFb6bDbCbBbAb@b?b9b7b8b:H0GPMPUEYRUPjP5EYN90uQ0>Q0EP;PwQ0:10i45wrXQ;PhPgPXP^P\Q0nP;PiQ09=~DrRr9\D7==FgXE;PFPDPiPDPdPkI0@A\Ddr==F7XRFPhPkPfPlPdPiPXPcPaP_PHN;0tP^P=EYPwP9EYPUL0sPiP9J0rQ0?Q0DPuPpQ0;P^P[P7J0qQ0BQ0CQ0APnPpPeP^PRQ0qQ0yQ0}Q0@'29?qeg01EbQ0GPtQ0HPvQ0IPKQ0KP{Q0LQ0MQ0NQ0OQ0PQ0QQ0RQ0TQ0UQ0VQ0XQ0ZQ0[Q0\Q0]P81EJsQ0eQ0gQ0t766Q0hP]P]1q}yPBP]P]AgZyzPBP]Q0kPBA9]N~Q0u1RNz59]5X]CoDFDFQ0mQ02b<b=b>X08X18X28X38X481559A;5=9Q01Q06Q0v10:>'25?:[[[^08^18^28^38^48P7Q0YQ0wQ0xPxQ0pQ08PTPIO8b;bFb6bDbCbBbAb@b?b9b7b8b:40pQ0A@0meOeN90lPuPnPpQ0;P^PQJ0kClFdFdWKPYP5P7K0jbKbcWJW`WaWXWVP6P7O2n2001000000121000000W5WhP6P7O2n2001000000121000000W5W_P6P7O2n2001000000121000000W5WZP6P7O2n2001000000121000000W5W[P6P7O2n2001000000121000000W5W^P6P7O2n2001000000121000000W5W]P6P7O2n2001000000121000000W5W\WbWjWeWdWTWWWiXP3XRFXmFXf8XQ;Xn;XuFXl8Xo;WtXE8XU8Xg8WrWqWso"). Qed.

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
