(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import StrFun.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import STRW_merge.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_TSTRW_tac () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9TSTRW_tac8ld_factsC13~~~C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6StrFun:window_nthC13~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums8positive01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr9u8ro_readC13~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic7f_equalC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing5PExpr04C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem=bytes_at_readC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6StrFun:window_subC13~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6StrFun6copiedC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9TSTRW_tac8st_factsC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic8iff_reflC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6StrFun@u8arr_store_ok_nC13~~~I47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5wmonoC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem9upd_bytesC13~~~C47Corelib4Init5Logic5proj1c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9TSTRW_tac;mc_store_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemDbytes_at_write_otherC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6StrFunAu8arr_write_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6StrFun;copied_updZC13~~~K47Corelib4Init5Logic2or01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame6insideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;munch_writeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame;wmono_writeC13~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic5False00".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
ltac2:(KReplay.run1 (kr_t_TSTRW_tac ()) [] "h04__x1h14__x2h21Hh33Hc0h47__arithh54__ffh68__varmaph75__with84__x3h94cstrh:5cstr0h;2HWh<2Hah=2Hbh>2Hch?2Hih@2HnhA1ShB3SRChC1ahD1bhE4basehF1chG1ihH2kwhI1mhJ1ohK4segshL3srchM3xswp;1p;4p;3p;5p;2p;:p;6p;;p;<p;Bp;7p;8g0000j1FTg000Pj16Tg0015j1JTg001Sj1HTg0026j1OTg002Xj4mTg003fj1MTg004Fj3_Tg004dj3]Tg005Cj30Tg005]j1@Tg006<j5WTg007Ij29Tg007`R0j28Tg008:R1j11Tg008ZR2j22Tg0097R3j2LTg009Rj37Tg00:0j25Tg00:Rj1CTg00;Zj4QTg00<_j1KTg00=?j3BTg00=_R4j2^Tg00>7R5j2ITg00>Sj2;Tg00>mj1[Tg00?KR6j2ATg00?gj4XTg00@Nj1>Tg00A3j2GTg00AQj1VTg00Aoj4PTg00BMj1UTg00Bkj1TTg00CVj2?Tg00D9j2STg00D\j3RTg00E?j1qTg00Eaj4ETg00FLj2pTg00Fnj2oTg00GZj3lTg00H9j4kTg00Hkj4iTg00IVl:hTg00Jjj6gTg00KFj2<Tg00Koj1fTg00LMj2eTg00Lnj3dTg00MWj3DTg00N@j2cTg00Nlj1bTg00OQl;aTg00P`l<NTg00QElBjTg00Qkj7`Tg00ROj8nTg00S3R7f0R8'Ap=3g00SQR9g00T0R:P4P1P5g00TNf5R5f4R4f3R;f2R<f1R=P8M<Np=\P9P9P9P:P:P:g00U0P1P1P1P2g00UPP5P4P;P<P=P8MBjp=ZP9P:P0P1P6g00V3P5P4P;P<P=P8M<Np=YP:P=g00VUP8CEp==P=g00W<R6g00W[R1P1g00X;R0P8g00X[F`p=4P;P6P1P1P0P<P=P8Gnp=:g00Y;#Fg00Z:R6#6R2#6#6R>#6#6#6#J#HR?%J>#HR>#OR@[%F>RAf:RBf9RCf8RDf7RECmf6RF#M=_>D9]>E=0A5PEP5g00Z_RG#@RHPDP4DWP3%3D19FH/8C%1F,2D90:5'LA7>DE15>450@f=R4/2E#C90?F%OAR5f@RIf?RJPEPHCQ%K>RK9B>F,5A30[[P8%3B19CHf<RL'8f;RM%1C'290:D'LP319BH/84%1B,2L90:CA7>LM15>D50@fARD/2M#C90?BfDRCfCR3PMPHCQAB>BK,5A505[[P819LH/8J%14,2J90:Lf>R597>J15>M50@12C5#C90?4fGRKfFRBfERNPCPJP4P5PLP@A7>DI%MI97>N=0@8XJ@PCPDfBR@P3PIPJPMPE1^I3%1IRE%13RJ'IPIPE1;:ERLP3PJ1;:JR5E\19IHRO/83%[6RP,2ERQ/AJRRPOPQPIPEPLPHPP1;:PEZP3PJP5EYP;CXR5PR%>C%1CRC#3%>@%1@#3g00[>R@#KRJ%F@RLP:1G:<REP=%V:CP%U:RI%T:RQ1?:6RO1S:P5R:1?:2R2'=,4Q%q1R1P:POg00[jP2CE,4QC:1pQ0R0P8P<g00\QRSg00]1RT';1o8<=0STdAl:7=CkRTb5b6b7X0:X1:128P/A=1I=<[^0:^1:P8%1KPCP;O3b4b:b9b3CiP<M:h15>4P=EgP5PR%>D%1D#3%>N%1N#3%@HRN#@,<:%f6,e:1<:N5d:1<:H1<:G5D:5D:5D:g00]Q'c=B@JPLP:PEP=1G:;CPPIPQ1S:7R7%b6,?:R6'=,4QP1PQP:POg00^=AR:26CE,4QP1PQ1=72,4QP11=7O,4QC:C:C:P0PTb5b6b7X0:X1:X8:%3<12<;90:=%3;R;P;[[[^0:^1:^8:P8PCPBP3P<PFPMO6b4b:b9b3P8M;aW<W@W?W>P=P8O2n2001000000121000000W2W=P=P8O2n2001000000121000000W2W;WBXD>XC?XG:XF9XMAXE:XH9WLXA:WIWKo"). Qed.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
  ld_facts base c 4 kw i -> a = wa (S + i) ->
  exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_TSTRW_tac ()) [] "h04__x1h14__x2h24__x3h34__p1h44__p2h54__x4h64__x5h74__x6h81nh92HWh:2H3h;3HL0h<3Hc0h=7__arithh>4__ffh?4__p3h@8__varmaphA5__withB4__x7hC4cstrhD5cstr0hE5cstr1hF5cstr2hG1whH2z3hI1HhJ2H4hK2L0hL1xhM2z4hN2H5hO4__p4hP4__x8hQ4__x9hR1ahS1mhT2z5hU2H6hV2HLhW3HW0hX2HbhY2HchZ2Hih[1Lh\1Sh]3SRCh^4baseh_1ch`1iha2kwhb4segshc3srchd3xswhe1yhf2z6p%0p&0p;1p;4p;3p;2p;5p;6p;9p;;p;<p;Bp;7p;8g0000j1{Tg000Pj1STg0015k109Tg001Sj1~Tg0026k10?Tg002Xk40XTg003fR0j1LTg004Fj3ITg004dj3TTg005Cj33k10>Tg00^dj21k10OTg005]j1@Tg006<k50]Tg007Ij2FTg007`R1j2ETg008:R2j10Tg008ZR3j22Tg00:Rj1[Tg00;Zj4cTg00:0k208Tg0097R4j2:Tg00_Dj2wTg00_^k60NTg00`;j2GTg00`Rk303Tg00Jjj6xTg00a4j2fTg00aKk300Tg00?KR5j25Tg00>mk10@Tg00?gj4_Tg00alk20ZTg00bOk30YTg00blj2ATg00cIR6j2VTg00@Nj1QTg00cfk20;Tg00>7j2eTg00Kok10WTg00LMk20VTg00Lnj3dTg00KFk20:Tg00<_k10UTg00AQk10STg00BMk10RTg00Bkk10QTg00Nlj1mTg00E?k10PTg00CVk207Tg00dHk306Tg00D9k205Tg00FLk20MTg00>Sk202Tg00Fnk20LTg00GZk30KTg00H9k40JTg00Hkj4tTg00dkm90GTg00f>m;0FTg00gRj6rTg00h0j4}Tg00hKk40ETg00hek20DTg00iBm<0ITg00QElBzTg00P`m<01Tg00igk20CTg00jIj2qTg00MWj3kTg00N@j2nTg00=?j3aTg00A3k20BTg00Aok40ATg00Eaj4]Tg00jck60TTg00Qkj7YTg00kGj7|Tg00D\k30\Tg00ROj8yTg00kkk70[Tg00SQR7f1R8f0R933p=7g00S3R:/59p=9f2R;g00T0R<?389':p=\A3<89p==20D:9p=4202<9p=6P<P7P<P<P0f4R0P2f3R=g00lOP;P8P9N<0Ip=iP7P7P7P<P<P<g00U0P2P2P2P3g00UPf5R3P0P=P;P8P9MBzp=bP7P<P1P2P5g00V3P3P0P=P;P8P9N<01p=gP7P<P9P2P8P;P=P0P3f6R5f7R1f8R>N<01p=pP7P7P7P<P<P<g00m<P2P2P2P5g00m\P3P0P=P;P8P9MBzp>0=P7P7P7P<P<P<g00nCP2P2P2P6g00ncP3P0P=P;P8P9MBzp>0<20C:9p=U1e:9p=?A3<9:p=PA3<=;,:0158:/:9'qp=NA3<;8,:=/q9p=O20:<9p=>Ak<899k<;p=8Ak<89p=;g00[>R6g00]QR2,n;1n82=a693ap=^20B<9p=JP<P;P8P9H0Ap=<207<9p=HP<P8g00[jP9C]p=lP8g00W<R?g00W[R@P@g00X;RAP9J0Tp=WP=P?P@P@PAP;P?P@P@PAP8g00X[RBFYP9F|p=RP<P8g00^=RCP9C]p=CP=P?P@P@PAP;P8P?P@P@PAP9PBFYF|p=ZP;P?P@P@PAP<P8PCP9C]PBFYp=KP;P?P@P@PAP8P9F|p>04B0\<89p=DP;P?P@P@PAP<P8g00VURCP9C]PBFYp=vP3P?P@P@PAP0P?P@P@PAP<P=PCP;C]PBFYP8P9Gyp=BP0P?P@P@PAP=P?P@P@PAP;PBFYP8P9Gyp=jP3P?P@P@PAP0P?P@P@PAP=P;K0[P8P9Gyp=M1:;8/q9p>0HA3<9:,:8p=o159:p=u1n82=a69p=`P<P8PCP9C]p=hAk<89/n2p=sAa6899a6;p=Xg00Y;#{g00Z:R2#SRC#SR?#SRB#S#S#S$09#~RD&09B#~RE$0?[%{ERFf9RGP>P1P5H0X%L3=IE19TE5=3F011E3/71P1P3g00Z_RH#@RI#@RJ#@RK#@RLP>P0I0]P4%9>1F5L/EG%05,2>7\3f<RM/25#[93D3&0?FRNf@ROf?RPP1PLCc208F9RQ33f:RR9IEG9TEL93F911E9/7LRS':':XGF,wF[P9%9R1FGL/EMf;RT%0G'27\>P41FRLf=R4'E%0R,2M,=G12OR#[93DGfDRUfCRVPTPLCc=3NQf>RW9IE49TEL93F9/:S':XGF,wF[P91FML/EP%04,2P,=M12V4#[93DMPD12UW#[fHRXfGRYP8PLCc=3NQfARZfBR[5IE9TEL93F9/:SS00':XGF,wFXRDPFP7&0OE%LZRS=IEV9TE[R\POPTJ0N11E\11EO'7P7%L[R\=IEUR]9TEV,1E11E[R^,79X87P911E],GVR_B03EV]Ex11EZ,7_P7%LVR_fER]5IE,1E1G]911EVR`'7X87P911E]Ra/f_RbB00E_]Ex1GUb/7^P7P`fFR^11EYRb%L]R_'f'G/79X87P9P]P4Ex11E^%LU'f,G]/7]1F_^Rc/Eb%4]Rd%0^Re'2Rf%0bRg'5PcPfP_PdP9XL<Rd%49XL<R_P]P]%6]DiP^Pe%6eRfEbPbPg%6gEg1FVLRc/E^%0VRh&0@?Ri'2Rj/5eRkPcPjPVPh%6hS01PLPi%6iRjEbP^PePfEgP5C_Pk17aY%0aRk%0YRf'=Re&0>7S02&0><Rc%08%09'=178920Z8940YXe7XL7RlPaPk%6kPYPf%6fM9pPPC_PefIRe,1ERf%LYRk'fRa,GXRm/7X%0XRn%0fRo%4YS03'A#4'V/=nRpQ02PcPlPm1A89#4XS<X8<S04PoP_PYO1RmO2Rq,VnPXPn%6nRrPaPqQ04PfPo%6oPkPmPdP_PYPY%6YDiK0=J0<PXPnPrM9pP;C_Pp%Qb%9gfKRg,1ERb#Q%0b#9%QX%9nfLRn#Q%0nS05#9%Un%?n%4nRbPnPn%PbDNfMS06#4P<fPRp,1E#0S07/A9Rr#U%?r%4rRmPrPr%PmDNfQRm,1E#0/A8#4P<%0mRm00;91em91Vm9RrPm159m?\r9COfRS08#0/V8P<p-0Rr%@LS09#>Rk%>LRo%>KRK&0W2-0V<Rf%>JRJ5d<Rq%>IRI383820:<HRH,;q98koA8koH1;KI98ko&0U6Ra3^3^%{6R6%J3S0:&0S<Rs7<5%J0Rt7<;%J5S0;?<5s?<=s7<8&0R<Ru&0Q<RvPvPvPv%HCRw%m?#HRx'l1Wv>CRPv1WvGS0<Pv%HBRB/CxCZ&0P@R@PvPvPv1WvRS0=Pv%m2Ry#HRz207<2R2606<,CxCZ1WvTS0>205<:R{9KvxS0?604vP@PvPvP{%Sy#HR|P@PvPv1CBwP@PvPv205<iRB,D|PwP@1D2w=vvzEBDjEBEMEM20MvARAP9P;g00\QR}g00]1R~+0220L9;=3}~dB0K<:8H0JR:b>b@bAX0<X1<X2<X5<X6<X7<X3rX4rX?rWO1e83A\10380H5PGP51A=81oR5CO%931=10121iS0@/531235/51[[[[[^0<^1<^2<^5<^6<^7<^3r^4r^?r^OrP9fU,1E#0R~/A3R}#u%?}fTS0A#0R},5=1=8}P=P8PmP~P}P3P;P0P>PTP4O?b=bTbNbMbJbHb:bFbEbDbCbWb;b<Ctb9b9b9b91FS[/E`PFPXPY12^O#[PLCc=3NQQ00':XGF%LPRQ=IEURS9TELR}PYP^12]P#[PLCc208F}53NAIEOZ9TEL93F}S0011E}S0B/7LS0C':PYP^P]PUPPPLP41F\VRY11EUR}'E%4[/2h%0}RN'5R~PYP_P[O1RY/2hP\PYPdP_P[P[%6[DiPVPhQ01EbP}PN%6NS01EgP9C_S0DP~1FZLS0E/EU%0ZRh/2iRY%0UR\'5RmQ0EPYPZPh%6hPLPiPjEbPUP\%6\EgP0C_S0EPm17`]%0`R\%0]Rh'=RYQ02PcPlP`P\%6\P]Ph%6hM9pP4C_S0FPY%Q}S0G%9NS0H11EXRX#QS0I%0X#9S0J%Q]S0K%9hRh%QeR]%0e#9RX%Ue%?e%4eR\PePe%P\DNfJR\#4P<1;IHR`98Kq/`aP6%J;%J=7<8PuPvPvP{PzP@PvPv1Dwz,C2P@PvPvP{PwP@Avv{2EBDjEBPAP:b>b@bAX0<X1<X2<%9;12;=,=8%9=RqPq[[[^0<^1<^2<P9%0\PnPeP0PMPZO6b=bHb:bFbEbDbCb;b<bK1FQLRe/E}%4PRn/2iR\/5NPeP\PQPnPdP_PPPP%6PDiS0LPLPiPjEbP}PNQ01EgQ0DP~Q0EPmQ0FPYQ0GQ0HQ0IQ0JQ0KPhP]PX%U^S0M%?^%4^R_P^P^%P_DNS0NQ03P<%Ug%?gS0O%4gR_Pg%ugR^/o_COPbP<Q09#@Rb#>R_9d<fRd1;JH98oK78kR\%@bRb#>ReA8KJ`98dkRd';1;e\=^da3^P6Q0;9<t;Q0:%J1R`7<=7<8PuPvPvPvPv1l{zAKv|zCRPvPv1hz{AKv|{CRP@PvPvPvQ0<Pv%H?R?,C2CZPvQ0=Pv1C2{CZP@PvPvP{%mCRC#HRqP@PvPv1DqB%my#HRyP@PvPv1D|yPwP@PvPv1Dzq,C?P@1D2B=vvwDjEBEBEBEMEMPAP:b>b@bAX0<X1<X2<X5<X6<X7<XB<X3rX4r%?;P3P;P;%P3DNP>P8P01oG8CO%95Q0@/5G12GR/53121G,=>125i/51[[[[[[^0<^1<^2<^5<^6<^7<^B<^3r^4rP9P^Q0OfOR^#0P8Q05PgfNRgQ07P=P;P0P5PRPTPWO?b=bMbJbHb:bFbEbDbCb;b<bKCtN90GQ00Q0CPUPZP[PVPOPLPPPMP1P=P;N;0FP711ESS0C,GL179LX87P71f}QRO1GL9/7LX871GLOS00/7L1ANn#4RV,ViRZ/=iQ02PcPlQ00PZPLPiPjPOPVQ04P}PNQ01PQPnQ0LK0=J0<PLPiPjM9pQ0DP~Q0EPmQ0FPYQ0GQ0HQ0IQ0JQ0KPhP]PXQ0MQ0NQ03P<Q06,1E#0/A9RX#U%?X%4XR]PXPX%P]DN11Eg#0/A8#4P<20;i91ei91Vi9RgPi159i?\g9CO1Vi8P<%U^%?^Rg%4^R]P^%u^RX/o]CO%4pP<%@bRb#@R]#@Rh#>RY9d<fRm1;KJ98ko78eRo%>bRb1;_H'sR_%@h#>Rh1;JI98kK98meRm';%>]9d<fR]Ad<feRf;8dRd,;Y1;eH,sbRbA8]f\R]1sfHRf1;Y]1;ho/`a9X__9^dm9Xbb'`9Xff7Xf'`7Xb3^7X_'`P6%JG?<5s9<t;%J>?<3s?<=`7<8PuPvPvPvPv1l{wAKvqwCRPvPv1hw{AKvq{CRP@PvPvPvPv%SC#HRC,lBAKv2BRuCRPvPv1hCBAKv2CCRP@PvPvPvQ0>PvB06<yxR2,CCCZPvPv1h2{AKvC{CRP@PvPvPv1WvMPv1CxzCZ1Wv4Q0?604vP@PvPvP{P?P@PvPv1D?BP|P@PvPv1Dq|PyP@PvPv1Dw?,CzP@PuDjEBEBEBEMEMEMEMPAP:b>b@bAX0<X1<X2<X5<X6<X7<XB<XP<XQ<X3rX4rX?r%?8P0P8P8%P0DN1eiGP8Pi15Gi?\8GCOPTPR1A>GR:P:%PRR:DNP4PRP31:W:CO%9112>i/5R12RT/5M12>R,=G1=>i[[[[[[[[^0<^1<^2<^5<^6<^7<^B<^P<^Q<^3r^4r^?rP9PXPgQ0A,1E#0Rg/A1#?P3P1PgfS#0P8%0pP^Q08P=P;P0P5P>PRPWPPP[ODb=bfbUbTbNbMbJbHb:bFbEbDbCb;b<bKCtQ0CB00EQUErQ0BB03ELSErC}C}H0Eb[P4P9ErWIWZWYP8P9O2n2001000000121000000WIWXP8P9O2n2001000000121000000WIWVW9W]XRDX`<X_7XdFX^<Xa7WcX\<WSWbo"). Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
  ((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
   (S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
  u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
  firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
ltac2:(KReplay.run1 (kr_t_TSTRW_tac ()) [] "h01Hh11xh24__x1h32H2h42L0h54LEN0h67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<4__x3h=4__x4h>4cstrh?5cstr0h@5cstr1hA1nhB1yhC2z2hD1DhE3DSThF2HPhG2HahH2HkhI1LhJ3LENhK1PhL1ShM2_HhN3_H0hO3_H1hP3_H2hQ3_H3hR3_H4hS1ahT4basehU2bshV1chW1khX2kwhY2m1hZ4segsh[3srch\3xswp&0p;1p;4p;3p;2p;8p;<p;6p;7p;;g0000j1OTg000Pj1FTg0015j1]Tg001Sj1XTg0026k107Tg00oFk403Tg003fR0j1;Tg010Qj3sTg00^dj24Tg004dj3BTg005Cj33j1YTg004Fj3WTg011aj8eTg008Zj20Tg00:Rj1=Tg012nj4CTg007Ij2GTg007`j2ITg00>mj1_Tg013nj2oTg008:R1j11Tg00?KR2j22Tg00hej2HTg00alj2iTg00bOj3hTg00?gj4fTg00@Nj1UTg00igk206Tg00>7j2dTg0097R3j2:Tg00jIj2STg00<_k105Tg00A3j2RTg00BMk104Tg00Bkk102Tg00D9k201Tg00CVj2LTg00E?j1~Tg00FLj2}Tg00>Sj2aTg00Fnj2{Tg00GZj3zTg00H9j4yTg014Kj1xTg00P`l<ZTg005]j1NTg00KFj2JTg00Koj1tTg00LMj2rTg00Lnj3qTg00MWj3TTg00N@j2[Tg00=?j3^Tg00AQj1pTg00Aoj4`Tg00jcj6uTg00Nlj1vTg00Eaj4PTg00kkj7nTg00D\j3mTg00Hkj4|Tg00gRj6bTg014il;lTg00iBl<cTg00Qkk700Tg00ROj8kTg00kGj7jTg00SQR4f1R5f0R633p=@g00\QR7g00]1R8736p=>g00S3R9/26p=5%16,05p=8g00T0R:?356p=6f2R;1256':p=Qf5R<f4R='0f3R>'212;5'S/:6p=712;5/:6p=<1295/:6p=91:56,:;p=D10;5/26p=?1a:6p=AP:P4P:P:P0P=P1P>g00lOP;P5P6M<cp=gP4P:P6P1P5P;P>P=P<f6R0f7R?f8R@M<Zp=VP:P5g00VUP6CPp=KP5g00W<RAg00W[RBPBg00X;RCP6g00X[K00p=EP>PAPBPBPCP;P5P6Gkp=MP4P:P:P:P1P1P<P=P>P;P5P6M<cp=wP;PAPBPBPCP5P6Fjp=\g00Y;#Og00Z:R1#FRD#FRE#FRF#F#F#FRG#]#XRH%]F#XRF$07[%OFRIf=RJf<RKf:RLP5H03f9RM%;>7s;P314F>14FL'@%;=RN=BF>ABFNL53If;RN,4F%;K'@%;L=WFK9BFN=3IMf@ROf?RPf>RQPNPMP@PKP?Ge10O@#=93H0fDR@fCRMP?PLCC#>[[[[P614F<14FK'@%;?R?=BF0ABF?J53I14FQ%;P'@%;J=WFP9BFQ=3IKPMfBR?fAR<PQPKPNPPPLGeP3%5PRR1GJK/IO18PJ,6N18NKP@P?PM10M?RJP@%5MRS%_D%_G'oRG7QJE77<?,9N3D10@K#=93HLfHRKfGRJPNPQCC#>[P6%5<1GOP/IM%1ORN,0?,6Q18QPfERTPJPTfFRU10UTRVPJ%5URW?QVGE73<,9Q3DP31G<O/I@18M<,6P10PNPKPUPJ10JURNPK%5JR<?QNGE77<U7DR10KO#=93HQfLROfKRRPPP?CC#>[P61GM?/IU%1@RP,0U,6?%5?18?MfIRNPRPNfJRV10VNRXPR12XG,9VE73<3DP318JT,6MA?MPVPOPVPR10RVRPPO12PG,9RE75DS10O@#=93H?fPR?fOR@PMPUCC#>[P6%1JRM,0N,6TfMRT9?UMP@PTfNRM10MTRSP@12SG,9ME75DWP3P<18JKP?PMP@10@MR<P?12<G,9@E77<M10?K#=93HUfTRUfSRKPJPVCC#>[P6%5N18VRfQR<PKP<fRRW10W<RSPK12SG,9WE73<P3%1O=?RWPUPWPK10KWR3PU123G,9KE710UO#=93HVfXROfWR3PRPMCC#>[P6%1M=?TUP3fURUfVRR10RURUP312UG,9RE7103@#=93HTf[fZRUPOP@P?P<PMPT14FRRR%;3RT'@%1RRM1H93RG'6RS%Y4RP%Y:RX%15%16RY'61@561i563hXB4X14RZPRPM%AMPT1H96X1:RMP3O1P6X1:R[PMP3P3%A3DgRMM9VPJCfR\PS14F?R]14F3R3'@%1]R^%13R_'6R`PPPXPZP]P^%A^P3P_%A_M9VPVCfRVP`%UKR_%1K#5RK14FWR3#UR^%13#5R314FURU#UR]%1U#5RUf\RZ-069RX1d9Z1H9ZRP/6Z':A3:P99<Z9'SRZf],H9RPP:g00[>Ra$05Rb%OaRc1R:5&04:Rd&02:Re201:9Rf1L:1Rg'K,EeRh%~BRiPhCM1}eCRhP6P;1a781{6;#>dAz:95CyR8b7b9b:X2:%56%55[^2:P6POPQO2b6bCb3b@b?b>b4b5P4PR%1W=?<YXA4RWP4PTPW18?<R<%1TR?'212<GP:P:P2P[P21256#xXB:X1:P<P<%A<P?PGP[P[%AYX14PTPGPMEwM<ZP\PSPVP`P_PKP^P3P]PUPXPZPPP:p-0RPg00Z_RZ#NRX#NRU#N,J:%t1,r:1J:U5q:1J:X1J:Z5T:5T:RZ5T:g00]QRX'[1[ZX=^ab5^aPcP:P:1R:=P;%p:C`P51R:>C`PdPePePAPBPBPCPePAPBPBPCP0EuP:%v1,L:R1g00^=R01L:ERECP,Ee5\e1KEf,EeP:P1P0PfCP,Ee5\eFnPiPe1L:D9m:gRg/KE,EePi1Kg1,EeCMCMPhP8b7b9b:X2:X;:X<:X=:W816;>,:=A3:;99<>9'SA?5;=A?;>=[[^2:^;:^<:^=:^8PP6f_RP,d9PPP5fY#1POP;PLO7b6bCb3b@b?b>b4b5C|PRPJEb14F@PNEbP6M;lWGWRWHP5P6O2n2001000000121000000W0WFP5P6O2n2001000000121000000W0WQP5P6O2n2001000000121000000W0WPP5P6O2n2001000000121000000W0WOP5P6O2n2001000000121000000W0WNWJWMWIP5P6O2n2001000000121000000W0WEXSHXUIXK:XW4XV4X\IXT:XX4W[XA:XD:XL:WYWZo"). Qed.

Lemma mc_store : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
  bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
  munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
  length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P ->
  xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
  bytes_at segs (write_to_mem m1 a xs) S src /\
  u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
  copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
  munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
  wmono segs m0 (write_to_mem m1 a xs).
Proof.
ltac2:(KReplay.run1 (kr_t_TSTRW_tac ()) [] "h04__x1h16__sat7h24__x2h34__x3h44__x4h54__x5h61Hh72H5h83Hc0h93Hl0h:4LEN0h;4Lbs0h<7__arithh=4__ffh>8__varmaph?5__with@4cstrhA5cstr0hB5cstr1hC5cstr2hD5cstr3hE5cstr4hF1nhG2z5hH6__sat6hI1xhJ4__p1hK4__x6hL2HahM3SOKhN4__p2hO4__p3hP6__sat8hQ4__x7hR1ahS1khT2xshU1yhV2CPhW1DhX2D0hY3DSThZ2Dnh[2H6h\2HPh]3HPbh^2HWh_2Hbh`2Hcha2Hkhb2Hlhc3Hxshd3LENhe3Lbshf2MUhg1Phh1Shi3SEPhj3SRChk2WMhl4basehm2bshn1cho2kwhp1mhq2m0hr2m1hs4segsht3srchu3xswhv2z6p%0p&0p;1p;4p;2p;3p;8p;Dp;6p;<p;:p;9p;;p;7p;Bg0000k101Tg000Pj1XTg0015k10;Tg001Sk105Tg0026k10yTg002Xk400Tg00oFj4wTg016Ck20ZTg008ZR0j20Tg00<_k104Tg016cj3@Tg003fR1j16Tg005Cj3=k10?Tg011ak80aTg007Ij2NTg007`R2j2KTg00>mk10:Tg013nk20YTg0180j3DTg0194j3ATg008:R3j11Tg00?KS00j22Tg00^dj2<Tg004dj3_Tg01:Ck30gTg012nj4lTg0097R4j23Tg00h0j4{Tg01:^mD0bTg00gRj6^k70lTg00:Rj1zTg01;nj3yTg00alk20^Tg00bOk30]Tg00?gj4jTg00@Nj1\Tg00igk20<Tg00jIj2BTg01=;k20\Tg01=ck30[Tg01>Gk20XTg00>Sj2iTg005]j1UTg00KFk209Tg00AQk10WTg00BMk10VTg00Bkk10UTg00D9k208Tg00E?k10TTg00CVk207Tg00Nlj1mTg00FLk20RTg00Fnk20QTg00GZk30PTg00H9k40OTg01>hk30KTg014Kk10JTg01?Kk40ITg00P`l<oTg01?nk30FTg01@Tk60MTg00Hkk402Tg01A<m:0xTg00Kok10wTg00LMk20vTg00Lnk30uTg01BVm90tTg004Fj3xTg00f>m;0sTg01D1k80rTg00Jjk60qTg01EFk30pTg01E`k30oTg01Fnm90nTg01HAk60mTg010Qk30BTg01ITj4}Tg00=?j3gTg00QEmB0ATg00hek20hTg00iBm<0DTg00>7k20jTg00MWj3|Tg00N@k20CTg00A3k20kTg00Aok40fTg00Eaj4cTg00Qkj7~Tg00D\k30ETg00ROj8kTg00jck60eTg00kGk70dTg00kkk70cTf2R5f1R6f0R7#640Bp=sg00T0R8P8P6P7C}p>0Sf4R9f3R:;g5?y67p>0Gg00SQR;1<56;=7p=FAx5679_9:p>0@g00S3R</27p=4%17,06p=:A=867p=51267,35p=rf5R=/09/2:1256'B/37p=?1256/37p=>12<6/37p=p1367,35p=[f6R>Ax5679_9:7==p=H1067#z9=:5p=LP8P8P=P9C}=g>:?y56/37p=Pf7R?P>P=P9Cw%66:0B:5/37'3p=RP9P:P5P6H00/37p=M12<51267'3p=Q1056/27p=;1256/B7p=]A=;67p=fA_5679=9:p>0ig00\QS01g00]1R@7=7p=eP>P=P9P:P5P6P7C{C{p=d1067#zp>0`P8P8P5P6C}=g:7p>0_1i87p=8P;P8P7P3P6P5P:P9P=P>P?f8RAM<op=vP;P;P;P8P8P8g00U0P3P3P3P0g00UPP=P9P:P5P6P7NB0Ap>0>P;P8P2P3Q00g00V3P=P9P:P5P6P7M<op>0=20h<7p=IP8P;P8P8P1P9P3P:g00lOP5P6P7N<0Dp=u20j<7p=VA=87<p=a20987p=TA|8679|85p=Wg00[>R1g00]QR2-0C6;g7p=C20k87p=ZP8P5P6P7H0fp=720787p=JP5g00W<RBg00W[RCPCg00X;RDP8P6g00VUREP7Ccg00X[RFF~p=9B0E867p=GP5PBPCPCPDP8P6g00^=RGP7CcPFF~p=OP8P6PEP7Ccp>06P9PBPCPCPDP:PBPCPCPDP5PFF~P6P7Gkp=EP>PBPCPCPDP=P9P:PBPCPCPDP5P6P7GkGkp=`A|867p=YP8P6PGP7Ccp=nP8B0E856PEP7Ccp=hP;P8P8P8P3P3P=P9P:P5P6P7N<0Dp>0HP8P8P8P8P8P8P0P7P6P5P0P:P9P=P>P?PAf9R0NB0Ap>0L20C72p>0NAg167p>03P6PBPCPCPDP7J0ep=tP5PBPCPCPDP6P7K0dp=SP5PBPCPCPDP6P7K0cp=bP:PBPCPCPDP5P6P7Gkp=qg00Y;$01g00Z:RB#XR2#XR3#XS02#X#X#XRE$0;S03$05RGQ02$0;$05RF$0y[S04Q04&01FRHf?RIf=RJf<RKP0H00f@RLf>RMPKP:Cwf;RN?s9=20Z88RO10MJ-0SM&04ORPfARQPLI0GfCRRfBRS;@Q%6IRT9FFMPFPMPF%6JPII0@==HKPRPSPQPMPKPNPIf:S05L0aP4%4IRU1NJK/KL1:IJ,5N1:NKfDRVPSPR10RSRWPV%4RRX&0:2RY&0:ERE+0YRZ7rWE?7>S,pN3[PHQ05PFPJPFPMPIFHAFFNMPGPNfFRNPMCLfKRWfIR[?DKJRKfHR\fER]PWPKfGR^AAMTJRTP]PT%1LRT,0IR_POP^10^NR`PPfJRaPKA@WaKFPGRDM[[[P7%4Q1NLI/KR10ST,5M1:MIP^P]PN10N]RTP^%4NRK?rTZE?7>],pM3[P41NQL/KV1:RQ,5IP\PNP^P`P\%4^RT?r`ZE?9>_N7[UPHPMPFPQPFPSPRFHAFFISPGPIPaPSCLfORIfMRU?DLQR_fLR`P[PIP_PW%6R=ASQRbP[Pb%1VRb,0RRcPOPW10WaRdPPfNReP_A@Ie_FPGRDM[[[P71NRS/KN10Nb,5S%4S1:SRPWP[Pa10a[RbPWAQabZE?7>[3[P41:^],5R12caP`PaPWPdP`AQWdZE?5[XPHPSPFP]PFPNP^FHAFFRNPGPRPePNCLfSRRfQRS?DV]RVfPRXPUPRPVPI%6^=AN]RdPUPd1:^\RdPOPI10IeRcPPfRRbPVA@RbVFPGRDM[[[P7%1^RV,0[,5]A;NVUPIPUPe10eURVPIAQeVZE?5[KP4PTPXPePIPcPXAQIcZE?9>dePHPNPFP[PFPaPWFHAFF^aPGP^PbPaCLfWRdfURc?D\[R\fTRTPSPdP\PR%6W=Aa[RKPSPK1:W`RKPOPR10RbRVPPfVR_P\A@d_\FPGRDM[[[P7%4[1:aWPRPSPb10bSR\PRAQb\ZE?7>SP412KbPTPbPRPVPTAQRVZE?PHPaPFPUPFPePIFHAFFWePGPWP_PeCLf[RafYRV?D`UR`fXRKPcPaP`Pd%6I=AeUR\PcP\1:IXPOPd10d_R\PPfZRfP`A@af`FPGRDM[[[P7%1e=;UTPdPcP_10_cR`PdAQ_`ZE?P410K_12\K7]dAQd\ZPHPePFPSPFPbPRFHAFFIbPGPIPfPbCLf_Ref]R\?DXSRXf\R`PVPePXPa%6R=AbSRgPVPg1:RTPOPa10afRgPPf^RhPXA@ehXFPGRDM[[[P710fKA;VKf7]VA;fVZ,pfP4%4aR412gZPHPbPFPcPFP_PdFHAFFR_PGPRPhP_CLfcRgfaRX?DTcRif`RjP\PgPiPe%6d=A_cRkP\Pk1:dKPOPe10ehPPfbRkPiA@gkiFPGRDM[[[P7%4\A;h\ZPHPcPFPKPFPVPfFHAFF_VPGP_PXPVCL1<FVRi1<FjRl'fRmPH%6fRn=_FVPFPnPjI0i<0gTPmP;P`fhRmffRnPVP7Cl#eXF;fgRofeRpfdRqPgPkPXPjPePhP\P`PaPfPKP_PcPbPS%4e1N\`/KjRb1:e\,5aRr%1`=;akRs10qk10gkRt/2q7]gRu%4gRv12tZRt'3Rw'3Rx'3Ry,34Rz'3R{'3PUPbP{P[PrPzP]P4PyPQPsPxPJPuPwP0PvPtP=P9C{FdFdFdP6ND0bPiP5E^PoPpPKPiCl#ePG20`q`RifiRtPoP71<FaRvCl#efjRwADm6`RuPoPqPwPuPn%6hS06=A\`S07PqQ07%1eRJ,0hPOPn10npPPPtPuA@wtuFPGRDM]MXRGPmPnPi1<FfCl#ePt10p\Rf#zS08=DoaRiPnPgH00PtPiPp%6\S09=A`aRuCwS0:1:\h9sguS0;POPp10pqS0<PPH0_S0=?ymiS0>A@tmiS0?'3S0@'3S0A'3PtPoPfPaPnPgPV1<F`Ri1<FgRP'f%1iRO%1PRu'5Rx&0?;Rs&0?8RQ%16%17Ry'51f6720^6740]XU;XI;R4PiPO%8OR]PPPu%8uM9vP5CjS0BPx1fie15OJRuPsPQP4PiPOP]PePJ%8JM9vP=CjS0CPu1NXjRJ/Kq%1XR]%1jRz'0Rr%1qR['2R{PJPrPXP]%8]PjPz%8zJ0>PqP[%8[J0=PUCjS0DP{1<FnRU%6oR['f%1URz%Io'5R]PsPQP4PUPz%8zP[%I7XI8S0EPoO1P7XI8R[Q0EPoPo%8oDuM9vPdCjS0FP]%\kS0G%1k#4S0H%\lS0I%1l#4S0J1<FkRl#\S0K%1l#4S0L1<FwRl#\S0M%1l#4S0N%\oS0O%1o#4S0PfkRl#\S0Q%1l#4S0RfnRz-0<<S0S%Vz%IzRU/5z'3%aU9>z<'BS0TfoRU#IS0UP820\YES0V%VYR4%4E%VZ[RQ[S0W%4YRsg01J4RrB0[YE6UWLS0X%4Z\r^LsS0YP6g01JP20X<Y'iP4eO1S0ZPQg00Z_R4#US0[#US0\#URs#US0]#TS0^%TsS0_20984S0`3WS0a&041R4'C&011S0b%Z9S0c&0W8R1775S0d%Z:776&0V8S0e&0U8Rs2088<Rr%J3RE59sS0f&0TCRCPs2078BRJ99srS0gPCPs%J2Rb99srS0hPCPs%mBR|#JR}/GES0i9OsbPCPsPs206r}PC1GJbR~99srDEF`F`20RsDS0jP7P5Q01/i@20Q75#edB0P8<6H0OS01b=b>b?X08X28X38X48%4:S0k%46S0lQ0k10=>R@,59%4>%4@[[[[[^08^28^38^48P7%1UfqfmRDfuS0mP?P^PRPdPeO9b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;S0nQ0BPxQ0CPuQ0DP{Q0FP]Q0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UP8Q0VQ0WQ0XQ0YQ0ZPQQ0_Q0\#TS0\Q0[#TS0[Q0`'Y3WS0o/C4Q0bQ0c9715%Z=S0p971:S0q776Q0ePsPs%X|#JS0r,n}PCPsPs%m|#JR|2088YQ0360K8RY5hJPCPsPsQ0r=hb|PC1G~}S0r=9sYDEDEDEQ0jQ01b=b>b?X08X28X38X48X58155:A;6=ZA;:=>10:9S03/0=S0s/2Z[[[^08^28^38^48^58P7ftS0t%1zS0u1<Fl#1S0vPDQ0mPMPNPIO8b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;S0wP;%6qRN10oy10nhRlA;lOo3]XF;%1NS0x,0nS0y/2fRl%1vRO,0fS0z/2nRz'B%IqRZ,0nS0{/2fRY/BzPlPzPYPzP8P8Q00P[Q001267$0JXU8XI8Q0yQ0{P[P[P[P8P8g01K61067H0I#8Xp8XF8PnPn%8nQ0xPZP[P[%8yXI;PNPZP[Q0EPqPq%8qDuS0xJ0HN:0LPfPf%8fM<op-0Rn/iz:0FzzJ0MQ0BPxQ0CPuQ0DP{Q0FP]Q0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UP8Q0VQ0WQ0XQ0YQ0ZPQQ0]#URz#URY#U#T%TYRY%TzRzQ0o'Y3W$0NRlQ0a,YzQ0^Q0\Q0['Y5WY/C4'C-03l+03Q0b%Z>S0[?791?751%Z??7=1?7:1776Q0ePs1ts0S0a%m3#JR39Osb5SsA9s3rAOsbr5Ss5bsPCPs%m2#JR2Q02#JRl5OsPCPs1GJ3=9s}1G}3=9sJ5bsPCPs1GEl=9s3PCPsQ0fPCQ0i99s~Q0i/G2=9sJ5bsCqF`F`Q0jQ01b=b>b?X08X28X38X48X58XK8XQ8XJn156>,3?12><S0i%a6'3'B15=>105AA;9A57]9A;>A0%4?S0f10?AR3A;30=5]@[[[[[^08^28^38^48^58^K8^Q8^JnP7Q0t#VQ0tQ0uQ0vPDQ0mP9fvR3P=PMPWPIPRO=b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;H02PPPTE^N:0xQ0:Q0APtPoPpP`P\PaPKQ0BPxQ0CPuQ0DP{Q0FP]Q0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UP8Q0VQ0WQ0XQ0YQ0ZPQP4Q0b%Z6Q0ePsQ0gPCQ0gCqQ0jQ01b=b>b?X08%47Q0l[^08P7PDPRO2b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;S0lP;PPQ06/Ni/K7XF;RKP;PNPKQ09/NvS0g/KN%I\S0A/0ORK/2ZQ0gPKQ09Q0AP[Q0EP\P\%8\DuPvPO%8OJ0>PNPZQ0xJ0=Q0BPxQ0CPuQ0DP{Q0FP]Q0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UP820<<t%Vt%ItRZ/5t'3%aZ9>t<'B%IwP8Q0VQ0WQ0XQ0YQ0ZPQ&0wB-0v8Q0^60u8RBQ0o5WzRw,YYQ0_Q0\Q0`3WRZ9WzBRB1YYB/C4'C,Cw'CQ0bQ0[?7>1?751Q0cQ0p77:776Q0ePs1tsAAOsJ25SsQ0aAOsJr5Ss5bsPCPsQ05,tsAOs}l5SsA9slrAOs}r5Ss5bsPCPsPs1nb|PCPsPsAh2|lPCPsPs206r2PCA9s~}DEDEDEF`Q0jQ01b=b>b?X08X28X38X48X58XK8XJnXNnXOn157:,3>%a7,3?'B15:>R2,30Q0i%a:'3'BA;>?AQ0f12@?[[\2[[^08^28^38^48^58^K8^Jn^Nn^OnP7%V312U<%VUP3fp#1PUP>1<FD#1P9P=P?PLPSPcO>b<bPb1bPbvb[bGb7bEbDbCbBbAb@b:b8b9b;H02PPPTE^RTPiP5E^N90tQ0;Q0@P;PvQ0710hy5sqXS;PgP`P\PaPdQ0lP;PhQ06=xFqRq9_F7==H`XF;PHPFPhPFPePjI0@A_Feq==H7XTHPgPjPXPkPePhP\PRPIPWP^N;0sPaP=E^PvP9E^PTL0rPhP9J0qQ0>Q0?Q0=PmPoPfPaP_Q0nQ0wQ0zQ0<'29>pfg01KZQ0BPxQ0CPuQ0DP{Q0FP]Q0GQ0HQ0IQ0JQ0KQ0LQ0MQ0NQ0OQ0PQ0QQ0RQ0SQ0TQ0UP8Q0VQ0WQ0XQ0YQ0ZPQ1CZ4Q0bQ0dQ0q776Q0ePsPs1n}|PCPsPsAhb|EPCPsQ0hPCA9sJ~Q0r1GJE59s5SsCqDEDEQ0jQ01b=b>b?X08X28X38X48X581559A;5=9Q0kQ03Q0s10:>'25>:[[[^08^28^38^48^58P7Q0uQ0tQ0vPDQ0mPMPIPRO8b<b1bHb1bGb7bEbDbCbBbAb@b:b8b9b;40pQ0=@0ofOeN90nPtPmPoQ08PaPcJ0mFdFdWMPVP5P7K0lbMbeWLWbWcWZWXP6P7O2n2001000000121000000W6WiP6P7O2n2001000000121000000W6WaP6P7O2n2001000000121000000W6W\P6P7O2n2001000000121000000W6W]P6P7O2n2001000000121000000W6W`P6P7O2n2001000000121000000W6W_P6P7O2n2001000000121000000W6W^WdWkWfWVWYWjXRGXTHXmHXg8XS;Xn;XuHXl8Xo;WtXF8XW8Xh8WrWqWso"). Qed.

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
    MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
     replace bs0 with xs by bytes_tac;
     let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
     let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MU WM LEN HW SF
                 ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
       as (SRC' & DST' & CP' & MU' & WM');
     change (Z.of_nat k) with kz in CP';
     clear SRC DST CP MU WM SF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
     rename MU' into MU; rename WM' into WM
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
  munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MU & WM).

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
