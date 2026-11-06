(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec StepTac.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control Ltac1 Array.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RdnPeelKit () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6of_natc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:RdnPeelKit6wch_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:RdnPeelKit7wchainZC13~~~C45stdpp9bitvector;definitions7Z_to_bvC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec6wbytesC13~~~C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StepTac6u_Z2bvC13~~~C47Corelib4Init5Logic8eq_ind_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec>rdn_wbytes_outC13~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205".
Import ListNotations.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Fixpoint wchainZ (m : word -> option byte) (ws : list (Z * list byte)) : word -> option byte :=
  match ws with
  | [] => m
  | (x, bs) :: r => wbytes (wchainZ m r) (Z_to_bv 64 x) bs
  end.

Fixpoint wch_ok (y : Z) (n : nat) (ws : list (Z * list byte)) : Prop :=
  match ws with
  | [] => True
  | (x, bs) :: r =>
      (0 <= x < 2 ^ 64 /\ x + Z.of_nat (length bs) <= 2 ^ 64 /\ (y + Z.of_nat n <= x \/ x + Z.of_nat (length bs) <= y))
      /\ wch_ok y n r
  end.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)
Lemma rdn_wchainZ_out : forall segs m ws y n,
  0 <= y < 2 ^ 64 -> y + Z.of_nat n <= 2 ^ 64 -> wch_ok y n ws ->
  rdn segs (wchainZ m ws) (Z_to_bv 64 y) n = rdn segs m (Z_to_bv 64 y) n.
Proof.
ltac2:(KReplay.run1 (kr_t_RdnPeelKit ()) ["FPX_1"] "p'0h01Hh12IHh22H0h32H1h42H2h57__arithh66__sat1h76__sat2h84__x1h94cstrh:5cstr0h;1zi001zh<2Hah=4__ffh>8__varmaph?5__with@2wshA2HdhB2HrhC2HxhD3HxlhE2HyhF3HynhG1ahH2bshI1li011lhJ1mhK1nhL1ohM1rhN4segshO1xhP1yi021pp;1p;2p;3p;4p;6p;9p;5p;7p;8g0000j1CTg000Pj1<Tg0015j1KTg001Sj1ITg0026j1RTg002XR0j2_Tg0038j1LTg003Vj2[Tg0043j22Tg004OR1j24Tg004jj1?Tg005Jj38Tg006Vj27Tg007cj23Tg008Ij45Tg009Pj2QTg009jj1MTg00:Jj3BTg00:jj2;Tg00;Jj21Tg00;fj3@Tg00<oj2=Tg00=Lj2ETg00>6j1JTg00>[j2YTg00?Cj3XTg00?gj2WTg00@Ej1VTg00@cj1UTg00ANj2HTg00B1j2TTg00BTj4GTg00C?j1gTg00Caj2fTg00DCj2eTg00Doj3DTg00EIj3dTg00Ehj4cTg00FZj3bTg00G=j3OTg00HFj6>Tg00Hdl9^Tg00J5j4NTg00JUj5]Tg00K7j2`Tg00KQj7aTg00L5j8\Tg00LYR2f0R3'1p=0f2R4f1R5'=/13p=Af5R6f4R7f3R8P4P5C5;D3p=9%?3,=5p=61145/`3p=:1;53#?p=FP8P4P5P3C59D67p=ZP5g00M7R9g00MVR:P:g00N6R;P3g00NVFap=PP8P9P:P:P;P4P5P3G\p=Sg00O6#Cg00P5R9#<R<#<#<R=#<#<#<R>#KR?#I%K=#IR=#R[g00PZR@%C=RA'_RB#CRCg00Q8%05RD%L<R<%L>R>'[RE,25RF'4%?5=A4EPBA8783%RARGf8RHf7RI/7513?6RJP7PHPIPJP7C5E9[X@Cg00QWRKPIf6RL13?7RMP8C5RN,QGU%MBRO9884PGPI17LOPMP8PNE9[eP0P@PAA8L63PGf:R0f9RN/7513?IRMPLP0PNPMPLC5E9[ABB4598ILPGf;RMABB84,7013?HROPIPMP0POPIC5E9[[^ICP3A8NH3PGf=ROf<RP/7513?0RQPNPOPPPQPNC5E9[%08128E'41;=4,68RQ/1E160N11Q07:8'4'4A80N5'4P1%07127E'41;=8,67RQ/1E16M011QM7:7'4'4A8M04PGf?RQf>RR/78?@J713?PRJPMPQPRPJPMC5E9P3%0L12LE'41;=6,6LR6/1E16OP116O7:L'4'4P1%0I12IE'41;=L,6IR6/1E16RO116R7:I'4A8QRLPGfCR6fBRJ/7I13?N;@Hf@RH,3?RSPQP6PJPSPQC5E9[P3%0N12NE'41;=N,60RT/1EfARU/6H11TU7:0'4P11;=0,6MRT/1E16JU11TJ7:MA86J0PGfGRJfFRT/7M13?O;@PfDRV,3?RWP6PJPTPWP6C5E9[P31F=P=AOEfER6/6V1F=O=AR67:RA8T6OPGfJRWfIRX/7RRY13?JRZPTC5PGP3fKPWfHR[,3?PJEZXLGPOP3O1PWA@YSQPZPTC5PWPQPYPSPZPTP@PJ%?JRY,=3R\13?U,E?RU1F=HR]=AU33:X;@P@PH1=[Y1=3]R]/1[7:3X;@P51E?SRS1;=QRQ#JR=%?Q#0RQ%JJR[%0YRY1Y<>RU122<%0>122E[[R^%0<R_AX<>5VKW<R>%0E\K^<_R_P1%0VRK12VER`%06P0%0TRT12JERaP1fORb#0Rc12bERb%0XfMRdfQ#0RefRRf/2ERgPXPPO1RPPGfVRhfURi/7WfS,3?RWPfPhPiPWPfC5E9Rfg00R3RW#MRh%CWRW1W@5Rj%V@Rk%U@RlP@1H@2g00R_1T@9R9CG,PlRm%g:R:PmCS1fl;R;P3P4g00SFRmg00SfRn'Q1e34=DmndAd@25CcR2b=b>b?X8@Rn%03PD[^8@RDP3fNRmPIO2b5b1W4W3P5P3O2n2001000000120000000W2W0P5P3O2n2001000000120000000b6b7b:b9P=PQP[PYPUP^P>P_P1PKP`126EP0P1PcPb12XEPdPPPfPhPWPjPkPlP@P9g00TF1H@<=b@?CG,PlRlP:PlCSP;P2b=b>b?X8@R2123EPF[^8@RFP3PmPLO2b5b1X4gX3eP5P3O2n2001000000121000000X2aX0TP5P3O2n2001000000121000000b6b7b:b95OHRLE>1E?ZRZP=PQP[PYPUP^P>P_P1PKP`fLRm#0P0P1PcPbfPR;#0PdPPPfPnPDP3PiP8O2b5b1X4gX3eP5P3O2n2001000000120000000X2aX0TP5P3O2n2001000000120000000b6b7b:b9P=PQP[PYPUP^P>P_P1PKP`12mEP0P1PcPb12;EPdPPPfP2PFP3PiP4O2b5b1X4gX3eP5P3O2n2001000000121000000X2aX0TP5P3O2n2001000000121000000b6b7b:b95OJRTE>P@PJ11\EX;@PVPZPTE>P@PH11]EX;@P4PSPLE>M9^E>WBWAWDP5P3O2n2001000000121000000W0WCP5P3O2n2001000000121000000W0P5P3O2n2001000000121000000W0P@PAP8P4CN=BB5980NPGPRP@PAP7P8CN=BB4,7O13?MRMP0PRPOPMP0C5E9[eW1XMCXHAXO@P5P3O2n2001102000121100101XGBP7D]WFWEWKXP@W@WJWNo"). Qed.
End FPX_1.

(* [comment removed for export] *)
Ltac2 rec chain_split (m : constr) (b : constr) : constr * constr :=
  match Constr.Unsafe.kind m with
  | Constr.Unsafe.App h args =>
      if Bool.and (Constr.equal h '@wbytes) (Int.equal (Array.length args) 3) then
        let a := Array.get args 1 in
        if Constr.equal a b then ('(@nil (Z * list byte)), m)
        else
          match Constr.Unsafe.kind a with
          | Constr.Unsafe.App ha aargs =>
              if Bool.and (Constr.equal ha '@Z_to_bv) (Int.equal (Array.length aargs) 2) then
                if Constr.equal (Array.get aargs 0) '64%N then
                  let x := Array.get aargs 1 in
                  let bs := Array.get args 2 in
                  let (r, base) := chain_split (Array.get args 0) b in
                  ('(@cons (Z * list byte) ($x, $bs) $r), base)
                else ('(@nil (Z * list byte)), m)
              else ('(@nil (Z * list byte)), m)
          | _ => ('(@nil (Z * list byte)), m)
          end
      else ('(@nil (Z * list byte)), m)
  | _ => ('(@nil (Z * list byte)), m)
  end.

Ltac wch_solve side :=
  lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split; [ side | wch_solve side ]
  end.

(* [comment removed for export] *)
Ltac2 rdn_peel_many (side : Ltac1.t) : unit :=
  lazy_match! Control.goal () with
  | @eq _ (rdn ?segs ?m (Z_to_bv 64 ?y) ?n) _ =>
      let b := '(Z_to_bv 64 $y) in
      let (ws, base) := chain_split m b in
      lazy_match! ws with
      | nil => Control.zero (Tactic_failure None)
      | _ =>
          ltac1:(segs m base ws y n side |-
                 change_no_check m with (wchainZ base ws);
                 rewrite (rdn_wchainZ_out segs base ws y n); [ | side | side | cbn [wch_ok]; wch_solve side ])
            (Ltac1.of_constr segs) (Ltac1.of_constr m) (Ltac1.of_constr base) (Ltac1.of_constr ws) (Ltac1.of_constr y) (Ltac1.of_constr n) side
      end
  end.
Ltac rdn_peel_many side := let f := ltac2:(side |- Control.enter (fun () => rdn_peel_many side)) in f side.
