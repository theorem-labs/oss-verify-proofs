(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit LeptB_guard.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptC_leaf () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list01K69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells7cell_wfC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib3Mem3le4C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions7bv_wrapC4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesI47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib2K53B239LeptL_kitBle_bytes_roundtripC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib3MemAZ_to_le_bytes_modC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib2K53B239LeptC_kit?rw_cells_recellC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic3and00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.


(* [comment removed for export] *)
Lemma cb4_c4 : forall (m : mem) A bs, rw_cells asegs m A [CB 4 bs] -> exists w : word, rw_cells asegs m A [C4 w].
Proof.
ltac2:(KReplay.run1 (kr_t_LeptC_leaf ()) [] "h01xh12H0h21mh31nh41yh51Ah61Hh71Lh82L0h92_Hh:3_H0h;3_H1h<7__arithh=4__ffh>8__varmaph?5__with@2bshA4cstrhB1lhC1whD1zp;1p;2p;4p;3p;6p;<p;7p;8p;Bg0000j16Tg000Uj1STg0013j1OTg001Vj1ZTg0028j1HTg002Xj1BTg0037j1DTg003Wj1<Tg004Oj14Tg005Lj2=Tg0062j4RTg006lj18Tg007hR0j12Tg008Hj4@Tg009=j1ATg00:7j1;Tg00;4j4FTg00;lj2ETg00<dj1NTg00=]j4`Tg00>8j1]Tg00>kj2Kj1\Tg00?Hj29Tg00?bj2[Tg00@Hj2:Tg00AEj31j1JTg00A_j2ITg00B?j1YTg00CGj6XTg00Ccj1?Tg00DAj2WTg00D^j2VTg00E>R1j2CTg00E[R2j2>Tg00F7j1UTg00FUj4TTg00G8l<PTg00G]j2uTg00H@j3tTg00H]j4sTg00IDj1pTg00Iij1nTg00JGj1mTg00Jej1lTg00KPj2GTg00L3j3jTg00LVj4iTg00MAj7gTg00Mej2fTg00NGj2eTg00O3j3dTg00ORj4cTg00PDj4hTg00Poj4bTg00R0j6MTg00RNj2kTg00S8j2aTg00Sgj8QTg00TDj8oTg00UIj4_Tg00Ucj3LTg00VCj4^Tg00W<l<qTg00WalBrTg00XGR3f2R4f1R5'Ef0R63Lp=0g00Y?R7P4P5P6C^p=5AL356p=3g00Z7R8/96p=7g00ZUR9P8P8P8P0P0f5R:f4R;f3R<P4P5P6M<qp=wP8P8P8P8P8P8P1P6P5P4P1P<P;P:f6R1f7R=f8R>f9R?MBrp=vg00[4#6R@#6RA#6RB#6#6#6RC#SRD#ORE%SB#ORF#Z[%HFRGg00[Y#B#B#B#BRH%D3R37069545PE%<6/3395;<XCE%45,=DP6A0H5395<4g00\8REP7P;P<A0H43RICRP7P;P<%8I#2C@%4<,=D#</3395:;P6P7P1P:A0H;3CRPEA0H:3R:#AP7P=P1%;:CFP7P>P=A0H13#8#2C@%4=,=D#</3395?>[P6A0H=3#APE1EH>#N%A3R>P7f;REf:R=A0H?3#;CFP7f<R?PE1EH=R=/33#8#2C@f=R1%4E,=D#</3375?[[P6%N=P7f>R=P1A0H?3#;CFP7f?R7P=A0H13#8#2C@f@P7A0H=3R?%4=RE,=DR:#</33R3P1g00\SR1P1g00\oR1P1C`%A3ePGPG%]:R1,KF1KF=%DFR;P;PGPG\GRI%\FRJPJP1P=PI\G/9JP81[DERJ1:H6=1G7XD8PG1:HEA1G67XBGP91IF=RI%47,:6=1G7X39%Y=PHP<EX%?@%?CRC'W,VE,:HPHPEPC%?BRB%2HR@'CRK/>C%?ARA,CBRL/>CRMP8P8P2P6X08RNP21>56#UX48X08PKPLPNPNPNP8P8g00]K1C56CT#7X28X38PBPB%7BP@PAPNPN%26RN#7X09PHPA%7AR@EwM:vPCPC%7CM<PA19IH%2IRL=18ARKP9P8%J9P0%J8%25=18NA19561u563tX49X09PIPL%7LPHPAP@M<PP<CsPK1IF7R7#pg00]oRF%27'>g00^MR7#D%H7%n8%m8%l8R7g00_9g00_XRKPKg00`8RKP81G8B1G8A5j8g00`X1G8CCig00a?Fg1f7KP6P4g00a_RKg00b?R7'91e64=1K7dAd8F5Ccb=b>b?PMP6b<bAb8ChCbEM1:HJ=1G=e1kD:1aDEEMA1G1=eGQ19G;GQ%;3%;?51Ge%8?,99GoW;W:X9>W7P5P6O2n2001000000121000000W1P5P6O2n2001000000121000000W1P5P6O2n2001000000121000000b1C_W6W@X58W2o"). Qed.


(* [comment removed for export] *)
Ltac frame_release_g RT AF GP MST Σ0 fr k SZ PF AGF PFS usp lo pcafter ivt pft getacl pre :=
  cps_stop;
  art_now RT AF ivt;
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx pft end;
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    let FRSc := fresh "FRSc" in
    assert (FRSc : rt_frames RT S = (fr, k) :: rt_frames RT Σ0)
      by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
    let S2 := fresh "S2" in let fl := fresh "fl" in let FLC := fresh "FLC" in let FLN := fresh "FLN" in let FL0 := fresh "FL0" in
    let FLHI := fresh "FLHI" in let FLP := fresh "FLP" in let REL := fresh "REL" in
    destruct (af_frame_release RT AF S mm fr k _ A FRSc) as (S2 & fl & FLC & FLN & FL0 & FLHI & FLP & REL);
    change (fs_size k) with SZ in FLP;
    let off := eval vm_compute in (SZ - 8)%Z in replace (fr + SZ - 8)%Z with (fr + off)%Z in FLP by lia;
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in FLHI end; unfold STACK_WIN in FLHI;
    (* [comment removed for export] *)
    repeat match goal with
    | IN : In (?b, ?kk) _ |- _ =>
        lazymatch goal with
        | _ : fl < b \/ b + kk <= fl |- _ => fail
        | _ => let FA := fresh "FLA" in
               assert (FA : fl < b \/ b + kk <= fl)
                 by (apply (flag_apart _ _ fl b (b + kk) FLN); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                     right; right; left; exists b, kk; split; [solve [in_live_tac] | lia])
        end
    end;
    let LHs := fresh "LHs" in let SSPs := fresh "SSPs" in
    lazymatch goal with LHx : LIBH mm |- _ => pose proof LHx as LHs; hide LHs end;
    lazymatch goal with SSPx : io_ssp mm |- _ => pose proof SSPx as SSPs; hide SSPs end;
    pre fl FLN;
    walk_to AF MST [(fl, fl + 1)] [pcafter];
    cps_stop;
    lazymatch goal with MUx : munch [(fl, fl + 1)] mm ?m', WMx : wmono asegs mm ?m', FLC' : rw_cells asegs ?m' fl _ |- _ =>
      let ART2 := fresh "ART2" in let FRS2 := fresh "FRS2" in let LV2 := fresh "LV2" in let SP2 := fresh "SP2" in
      let CR2 := fresh "CR2" in let AL2 := fresh "AL2" in let AM2 := fresh "AM2" in let AGS := fresh "AGS" in
      destruct (REL m' MUx WMx FLC') as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2);
      assert (AGS : agree_on client_static mm m')
        by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply MUx; cbn [outside]; split; [| exact I];
            let Hin := fresh "Hin" in intros Hin; apply FLN; replace fl with (bv_unsigned a) by lia; right; left; exact Ha);
      unfold hid in LHs, SSPs;
      let LH2 := fresh "LH" in let SSP2 := fresh "SSP" in
      assert (LH2 : LIBH m') by (exact (LIBH_agree RT GP client_static mm m' LHs AGS (fun a Ha => Ha)));
      assert (SSP2 : io_ssp m') by (exact (io_ssp_agree RT GP client_static S2 mm m' SSPs ART2 AGS (fun a Ha => Ha)));
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [| exact I]; let Hin := fresh "Hin" in intros Hin;
        lazymatch type of Hx with PF ?z =>
          apply (flag_not_client _ _ (rt_live RT Σ0) (rt_frames RT Σ0) fl lo usp FLN ltac:(lia) ltac:(lia));
          [ first [ solve [live_sub_tac] | solve [live_add_tac] ] | solve [frames_sub_tac] | replace fl with z by lia; getacl Hx ] end);
      apply (cps_ASTA_switch RT _ S2 _ _ _ AL2 AM2);
      clear REL LHs SSPs FLC FLN AGS
    end
  end.
