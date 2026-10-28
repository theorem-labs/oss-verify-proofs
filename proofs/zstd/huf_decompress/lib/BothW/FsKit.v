(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABytes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_FsKit () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okI47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlK47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5BothW5FsKit5dc_atC56Stdlib6ZArith6BinInt1Z6to_natK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission3Lib3Tac7sum_natC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission5BothW6ABytes<rw_cells_appC47Corelib4Init5Logic5proj1C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega5Tauto8GFormula05C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib3Tac>rw_cells_mergeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC46Stdlib5Lists4List9app_nil_rC56Stdlib6ZArith4Znat5Z2Nat7inj_addI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04c5ARocqVerifyHarness?AgentSubmission5BothW5FsKit8dc_splitK46Stdlib9micromega5Tauto8GFormula03c5ARocqVerifyHarness?AgentSubmission5BothW5FsKit7dc_takeK47Corelib7Numbers7BinNums1Z02K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission5BothW6ABytes8c8_of_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission5BothW6ABytes:c8c8_of_CBK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells7cell_wfC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_recastC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith4Znat5Nat2Z8inj_succI47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission3Lib5CellsBcells_bytes_lengthC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith4Znat5Nat2Z2idC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses3injC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib3Mem;wa_unsignedC5ARocqVerifyHarness?AgentSubmission5BothW4BImgAref_wview_overlayK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indI47Corelib4Init5Peano2le00C46Stdlib5Lists4List:length_appC56Stdlib5Arith8PeanoNat3Nat6eq_decI47Corelib4Init6Specif7sumbool00C47Corelib4Init3Nat3subC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC46Stdlib5Lists4List>nth_error_app2C46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses:impl_morphC46Stdlib5Lists4List>nth_error_app1C47Corelib4Init9Datatypes7nat_indC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC46Stdlib5Lists4List>nth_error_NoneC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib6ZArith4Znat5Nat2Z6inj_leC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic2or02c5ARocqVerifyHarness?AgentSubmission5BothW5FsKit:dc_at_any2C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics;memory_readC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses8or_morphC5ARocqVerifyHarness?AgentSubmission5BothW4BImgDref_memory_read_noneI47Corelib7Numbers7BinNums1N00c5ARocqVerifyHarness?AgentSubmission5BothW5FsKit<seg_rom_highC56Stdlib6ZArith6BinInt1Z7add_0_rc5ARocqVerifyHarness?AgentSubmission5BothW5FsKit8mrd_high".
Import ListNotations.
Open Scope Z_scope.

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac lit_in H :=
  repeat match type of H with
  | context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H
  | context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
  | context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v in H
  end.
Ltac lit_goal :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  end.

(* [comment removed for export] *)
Ltac addr_diff_g E A :=
  let k := addr_diff E A in
  let ok := eval vm_compute in (Z.ltb k 65536) in
  lazymatch ok with true => k end.

Ltac solve_load_g :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_store_g :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_g E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv beta iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv beta iota
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Lemma disjoint_from_sub : forall W A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' ->
  disjoint_from W A' n'.
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "p'0h01Ah12A'h21nh32n'h41Hh51Wh62H1h72H2h82H3h94__x1h:4__x2h;4__x3h<4__x4h=4__x5h>4__x6h?1Dh@2IHhA7__arithhB4__ffhC8__varmaphD5__withE1ahF2hihG1lhH2loi001pi011zp;1p;3p;2p;4p;5p;7p;8p10000p4p710R0p1000Mp4p710p8P0p1000ip4p710R0p8p1001Gp4p710P0p8g001bj1DTg002Bj31Tg003>j20Tg003Zj22Tg0047j1ETg004Wj35Tg0057j4@Tg005Wj23Tg0061R0j2OTg006Lj19Tg006kj28Tg007Tj3:Tg008=j2CTg008ij2>Tg009Gj4=Tg009ej1VTg00:Cj1UTg00:aj1TTg00;Lj27Tg00;oj1<Tg00<Tj3ATg00=7j1BTg00=\j1PTg00>>j2NTg00>`j2LTg00?:j2KTg00?fj3JTg00@@j3ITg00@_j4HTg00AQj4MTg00Alj5GTg00BNj4QTg00C9j7RTg00C]j7FTg00DAj8STg00DeR1f1R2g00ECf0R3CQp=4P2g00EjR4g00FIR5P5g00FiR6P3g00GIFRp=6f2R7P4P5P5P6P2P3FFp=?f3R8P4P5P5P6P7P2P3GSp=;g00GiR4#DR9P4f4R:?18710:7R;1287f5R</2:'0R=g00H[R>/08R?f8R@?1<:[[[[^31^11^21^01RAX59%E4RB?187g00I9A1B<:eX8?X7=X6;W4X31X11X21X01g00IUP1P1f6RB=54<?187f:RCf9RD554?1<:\?\=\;[^31^11^21^01\A^G9P3P1P1f7REPBC@=54<?187P012EBf;R0'010CE'3A1DEB12B<f<RF'0100B'3A1CB<'OP812D@RGf=RH'010FD'3A1FCDf?RI,0Gf>/0D'3A1HD@g00J5RHg00JaRG#9RJ#9RK#9RL,81181KRK181G5:15:1g00K@RG'C%9L,81181J9:1K5:1/CG%EH55H35%DHP1P11>1:P71>1BC=P2P11>1<P8%V1C=C=%U1%T1RHg00KlRG,71RK%<GRJ,715A1RL%BJ,71RM%BGRG#<,715A1RN'4,6H%P5R5PH14MK,6HP5PH171GRG,4N,6H%<J,71RJ/4M,6H5?HP514LG,6H14JK,6H5?HC;C;C;1NH6P3P7g00LQRHg00M1R6'L1K37=JH6dAI1>2CHbBbCbDX91X:1X;1X<1X=1X>1123212:<'010<212BE/0:10<B'3128:/0<10B8'3[[[^91^:1^;1^<1^=1^>1P3P0PFPIf@PDPCPBPEP7O9bAPFP0PCPDP@P3PBP<P:O8CMW4W?P2P3O2n2001000000121000000P1P1P0PCC@=54D?1<:eX8?X7=X6;W4X31X11X21X01X@AX59XF1XH1P2P3O2n2001100000121101101XE4P3DGW5o"). Qed.

(* [comment removed for export] *)
Definition dc_at (m : word -> option byte) (A n : Z) : Prop :=
  exists bs, rw_cells bsegs m A [CB (Z.to_nat n) bs].

Lemma dc_split : forall m A a b, dc_at m A (a + b) -> 0 <= a -> 0 <= b ->
  dc_at m A a /\ dc_at m (A + a) b.
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "p'0h02H2h14__x1h22bsh31xi001xh42H0h52H1h67__arithh74__ffh88__varmaph95__with:4__x2h;4__x3h<4__x4h=4__x5h>1Ah?1Hh@2HahA2HbhB1ahC1bhD1mhE1nhF1yhG1zhH2z0hI2z1hJ2z2p&0p;1p;2p;3p;<p;4p;:p;5p;6p;Bp;7p;8g00;oj1HTg00MQj1lTg00Moj1cTg00NRj1qTg003ZR0j22Tg00O4j3>Tg001bj1fTg00OjR1j13Tg00PJj2ETg0047j1VTg003>j2ATg0061R2j21Tg004Wj3@Tg00Q?j2kTg00?fj3Jj1hTg00QVR3j1?Tg00R6k209Tg00RYk305Tg00>`j2NTg00S6l<wTg00S[j2ZTg005Wj2KTg00T=j1nTg00T[j2mTg006Lj18Tg00U<j3UTg006kj2aTg008ij2`Tg009ek10@Tg009Gj4_Tg00:Ck10?Tg00:ak10>Tg00Uek20=Tg00;Lj2OTg00=\k10;Tg00=7j1gTg00<Tj3[Tg00>>k20:Tg00?:k208Tg00@@k307Tg00@_k406Tg00VHk404Tg00W3k103Tg00Wgm:02Tg00Xek200Tg00Y]j3STg00Z:j3DTg00ZXj1XTg00[Qj5}Tg00\Oj4|Tg00\jR4j2zTg00]Jj1{Tg000Mj6bTg00]nj3RTg00^Mj2vTg00^kj4dTg00AQk401Tg00_Ej4WTg00`;j2uTg00`Xl<tTg00a=lBiTg00acj2sTg007Tj3PTg008=j2eTg00BNj4]Tg00C9j7rTg00b?j7pTg00C]j7oTg00DAk80<Tg00bcR5f3R6f2R7g00cXR8f1R9f0R:3@CWp=Tg00H[R;/u:p=7g00DeR<?J9:p=6P<g00dMR=P<P<P1f4R1P3P6g00dlP7P9P:M<tp=YP=P=P=P<P<P<P4P3P3P3P0g00eYR>P6P7P9g00JaR?P;P:MBip=~P=P=P=P<P<P<P4P3P3P3P0P>f5R>P1P6P7P9P:MBip=y1s;:p=B1A:;p=CAJ<:;p=L1a<:p=<AP<9:9P<7p=QAP<9:p=5g00K@R0,e:p>0AAP<9:/e0p=4g00J5R0A@09:7@7p=9P<P9g00f<P:C]p=^P9g00EjR4g00FIR@P@g00FiRAP:g00GIFrp=0P<P9g00fcP:C]p==P7P4P@P@PAP9P:Fpp=IP<P9g00ECP:C]p=GP7P4P@P@PAP9P:Fop=\P6P4P@P@PAP7P9P:L0<p=FP5P7P9P:CWp=MAR679,E1=@8:p=;P5P61279P:CWp=:AR79:,E6p=x1E79=@8:p=jg00KlR4#HRB#HRC#HRD#H#H#H#l#c%lD#cRD#q[129:9>67g00gJ%fDREP>P11267#3/E:%V8RFCTX2E1A;6RGf7RHf6RI;>>12I>=>H1'1\G[P:PHPI12>1#3/E:PFCT1A;IRGP5f:RJf9RKPFf8RL/2HRM#3RNP6PF%3LRO%3HRP%V=5@=5@=RQP71kP?RR,kORS=J=N%7LRT%7HRU/2;RV'2RW%7MRX'6P=P<%h=P3%h<%?9%?:R3'6AJ=9:2099:405XF=X3=PSPWPOPTP:X3<RT%7:X3<RWPLPL1N<LDYPRPVPPPUPTPWPHPH1N<HDY1N<;C~EyPNPXPTPWPMPM1N<MDYM<w1Z;M%BM16XM'1%CM%LX'1'K12KL#7P<1Z;K%BK%7KRX/6K'1%CK%LX'1'K%7JP<f<RX,Z;%BX%7XRM/6X'1%CX%LM'1'Kf=RM#7P<%n4,m<RW%8?RT#8RU#8RP#8RV#8RR#8RS#8RY#<RZ5U<R[%<RRR9U<W%<PRP1a<?R\3QR]'5R^$0AR_AU<WPRP/5\RW,5R,4ZR`%<VRV=QRW,4Z%8Y#<RY%<SRS/5V'414Y^%<TRT/5\9QRP,4Z15VT,4SRT15S],4[%<URU/5\9QRP,4Z15VU,4YRY%V0RU79Y3999`_99TT79T393939%f0R0P<P<1`<1P7&0@<RTC_P9P<1`<>P6PTC_C_&0?<RT&0><R`20=<;R_1O<CRC'^,0`1O<4RY/=C,0`5I`1GC_,0`1=Y_,0`5I`5\`&0;@R@P`%gB,O<RV,^_,0`1O<BRB/=V,0`5I`1GV_,0`1=B_,0`5I`5\`P@P`A[<CVRZ,^_,0`%g4,O<R4/=Z,0`5I`1GZ_,0`1=4_,0`5I`5\`P@P`1G_V,0`P@P`1G_C,0`P@A[<B_9[<Y/=4,0`CFCFCFCFCF20:`ARAP:P7g00LQR4g00M1RB'N208:7=J4BdB07<;9H06RBb7b8b9X1<X:<X;<X<<X=<%B616:6'1%C6%L:'1'K%B>167>'1%C>%L7'1'K12>IR4#B1614'1%C4%L1'1'K1A;HR412I;,2>/6H\4[[[[^1<^:<^;<^<<^=<P:f>R4f?RCP>P6P9P7P1PIPHPLO:b6bJb0bIb5bHb4H04&03Q=J=NeN:02200Q6=S8F9S8F9MJKf;RQ%3KRNPDPNP1PFD;RIPOPDPOADDN1PFD;R15S87MJ%3JROPDPOP>PFD;R79MXQRVPXPQ%X7#?PNPDPNADDO>PFD;ROC:R>'1[AMQJIPQPJ%XI#?P1C:'1RNAS87O9MXQ[P5PQPJPIP1D}P:C|PNP2PVP>A>MXQ12XQ=>MJ'1P:P4PM%3XRXPDPXPHCxPFCTPCP4%3MRMPDPMPLPFD;#X#?PXPDPXADDMLPFD;C:P=%34R4/z?fAR?f@RLP3P4PDP4%3CR3=DDJPFD;RJC:XE=P:P4%{4EbPLPC%?4PMPDPMADD4KPFD;C:P<%?3fBR4P?P:%3LRM=DDQ9RD3R==j3FC:XG<P:PCPUP01`<9PTP`1G_Y,0`R`P@P`CFPAPBb7b8b9X1<1A;:1A;9[^1<P:PLPKO2b6,vCEbP?PLPCPJC:A>4?L12?L=>4CPEfCRCP4%3?/E:PFCTX2EARDMQP6CdPEPCP4P?AjM:FC:X2EP=P:CdH01b0b0W0W5P9P:O2n2001000000121000000b0b0XAGW@W?X2EP9P:O2n2001000000121100000W4XC<XB<X><WDo"). Qed.

Lemma dc_merge : forall m A a b, dc_at m A a -> dc_at m (A + a) b -> 0 <= a -> 0 <= b -> dc_at m A (a + b).
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "p'0h01Mh11Hh21Ah37__arithh42bsh51mh61nh74__x1h83cs1h93cs2h:1lh;4segsh<2H1h=2H2h>2Hah?2Hbh@4__ffhA8__varmaphB5__withC1ahD1bhE3bs1hF3bs2hG1zi001xp;1p;3p;2p;4p;5p;7p;8p;6g00;oj1:Tg00MQj1ITg00Moj1GTg00NRj1QTg00O4j3=Tg001bj1?Tg00Ojj11Tg0047j1ATg003Zj22Tg003>j2;Tg00_Ej46Tg00ZXj19Tg00QVj1<Tg0061R0j2HTg00[Qj5_Tg008ij2^Tg00:Cj1]Tg00:aj1\Tg00Uej2[Tg00;Lj2ZTg00BNj4YTg00C9j7XTg00=\j1WTg00DAj8VTg00>>j2UTg00>`j2TTg00?:j2RTg00?fj3PTg00@@j3OTg00@_j4NTg00^Mj2MTg000ij6@Tg00\jj2ETg00]Jj1FTg00AQj4LTg00gdj6STg00h_j1>Tg00iYj2KTg000Mj6DTg00PJj2CTg00Y]j37Tg00Q?j28Tg00j7j4aTg00^kj4`Tg004Wj3BTg00bcR1f4R2f3R3g00cXR4f2R5f1R6'Cf0R73BC6p=5A7467p=01C56=B47p=3P1P5P6P7C6p=4AB467p=Jg00KlR8#:#:#:R9#:#:#:#I#G%I9#GR9#Q[R:g00DeR;A=356g00gJR<%?9R=f5R>P2%13P7%A4R?D5X4=1223==>5g00H[R@/;2RAf8RBf7RCf6RD/2>3=\A[[P7PCPD%1>P7P?D512CD==B>P<P=f:R<f9RA/2B%1CP7P?D5X4=1;@BREf<RFf;RG12<A3=\E[P7PF12G<%1AP7P?D51;@GREg00jZ#?RH%?4RIP0P2P3P51067C6P>P2P3P5C6P>P2%95#<,23P6C6'HR0[P2P3P5P6C6P2P3%96#<,25P7C6'HP>P2P31056C6[RJPDP>P21035C6\0P2P3P5P6P7D_P7n2001000000120000000X9IW8X2;X5:W;PJ^9I^8I^2;^5:^;HP7P1f@RHf?R:f>RJ#1R0?3A?RKf=RL#1RM?32?R2A4H:K%9K#<,2:=4H2RNPBg00dMROP0fARP%<7,2HA30>?R>34X6OP;PJ12H7=4P>XG;P3%<0g00J5RQ#A%?Q1^;6%];%\;RQg00EjRRg00FIRSPSg00FiRTPQPRPSPSPTP;1[;@g00EC1Z;8CYg00GIFXR8%WSP8GV1UQTP7P5g00LQRTg00M1RQ'T1R75=PTQdAO;@6CNb@bAbBX7;RQ1;@71;@6[^7;R@P7P:P3O2b3,MJE@g00JaRT,E0%F0E@PNeCLO6b1A3MB?%1F?33?'094:JP1PHP:P?10K2R2P?ES102?,0?94H:%1:R2?3<?/0>R>#9%>>;3?,0?94PH[PI10>?fBRK10?774PfCR1%1PR3?3F?%1HRM?3C?'0RN#9%>N;3?,0?74K[X:IP7P>1K4>ED10?>94PH1CMGRG/J?A32D?R2'0RD#9%>D;3?,0?94KP[P7P5O1PKPP1JG2R2#9%>2P?D5P=%A9979CfDR2P1%1KRG183T'8A79L7P?D5X:=P7PC1K9CEDP1PK18MT,83A79FCP?D5PO1E3TfERTP2%11RF/87A79JARJP?D5X6OP7P3%F3EDP2P118G3A79LBP?D5P=fFRLPT1221#1P7P?D5X4=PJPO18FGPLPTP7A79:<P?D5X6OP7121K#1P1PKPQP@P7P2PBO2b3PQP@P7P1PCO2b3CaE@C`b0b0b0b0b0b1X?EW>W=XF=P6P7O2n2001000000121100000W1W<XE=P6P7O2n2001000000121100000W1XD;XC;W2W5o"). Qed.

Lemma dc_take : forall m A n k, dc_at m A n -> 0 <= k <= n -> dc_at m A k /\ dc_at m (A + k) (n - k).
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "h04__x1h14__p1h24__x2h37__arithh44__ffh58__varmaph65__with71Ah81Hh92H0h:2Hkh;1kh<1mh=1nh>1zp;1p;3p;2p;4p;6p;7p;8g00;oj11Tg00MQj1?Tg00Moj1:Tg00NRj1DTg00O4j3@Tg003>j20Tg0061j26Tg00kYj22Tg0047j1GTg001bj1ETg008ij2=Tg009ej1BTg009Gj4ATg00:Cj1VTg00:aj1UTg00;Lj2>Tg00l6j3TTg00<Tj3STg00BNj48Tg00>>j2MTg00>`j2LTg00?:j2KTg00?fj34Tg00@@j3JTg00@_j4FTg003Zj25Tg000Mj6HTg00Uej2ITg00=\j1CTg00lYj7NTg00C9j7OTg00mRj6PTg00b?j7QTg00DAj8RTf1R0g00EjR1g00FIR2P2g00FiR3f0R4g00GIFOp=3g00DeR5P0g00ECP4C8p=7P0P1P2P2P3P4EPp=9f2R6P1P2P2P3P0P4FQp=;f3R7P1P2P2P3P6P0P4GRp=<g00KlR1#1R8#1#1R9#1#1#1#?#:%?9#:#D[A@760g00H[R9/00R:1006'6f5f4R;P61276R<g00J5R=#GR>%E=R=P51=56P0%B5CAR?%V5R@%U5RAP51>51R1g00fc1>58R8AT518RB5S5C8'31MA3R3P4P6g00LQRCg00M1RD'L1K46=4CDdAJ590CFRDb4b5b6X05X251240,509454^05^25P4P7P;O2b3156<9457P5P;f7f6;@4X>5P612;7,57P4EHb9p-0R<P>P=1=50P@PA1I59RC/71,3ARE19A75;A%C2R2PEC<P3PDb4b5b6X05W11094/60P:[^05^1<P4107;P7P0O3b3P>P=P?P@PA19A;1781,3A5;AP217CB,3AC<P3PDb4b5b6X05X25X1<1004,661206,09[^05^25^1<P41097P7P;P0O4b3FNW:W8X;5X=5X75W<o"). Qed.
(* [comment removed for export] *)
Lemma dc_sub : forall m A n B k, dc_at m A n -> A <= B -> 0 <= k -> B + k <= A + n -> dc_at m B k.
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "h04__x1h14__x2h24__x3h34__x4h47__arithh54__ffh68__varmaph75__with81Dh92_Hh:1ah;1Ah<1Bh=2D'h>1Hh?2H0h@2H1hA2H2hB2H3hC1khD1mhE1nhF1zp;1p;3p;2p;4p;6p;7p;8g00;oj16Tg00MQj1FTg00Moj1CTg00NRj1KTg00O4j33Tg003>j22Tg003Zj21Tg00kYj20Tg006Lj1<Tg006kj2>Tg007Tj3ATg008=j2ITg0047j1HTg004Wj3[Tg001bj1XTg008ij2@Tg009ej1VTg009Gj4?Tg00:Cj1UTg00:aj1STg00;Lj29Tg00<Tj38Tg00=7j1RTg00=\j1QTg00Uej2PTg00l6j3;Tg00>>j2MTg00>`j2LTg00?:j2JTg00?fj3=Tg00@@j3NTg00@_j4OTg0061R0j2:Tg00n6j6ETg00BNj4DTg000ij6ZTg00C9j7GTg00b?j7YTg00DAj8WTf2R1g00EjR2g00FIR3P3g00FiR4g00DeR5f1R6g00ECf0R7CDg00GIR8FGp=4P1P2P3P3P4P6P7FYp=Bf3R9P2P3P3P4P1P6P7GWp=710679391p=5P6P2P3P3P4P7P8FGp=Tg00KlR8#6R2#6R:#6R;#6#6#6#F#C%F;#C#K[f4R;?39112;1g00H[R</21R=11;9f6R>f5R?'1'2f8R@f7RAP>10?ARBP9g00J5RCg00JaRD#<#<RE#<,>51>5E1>5D5A55A5g00K@'I%HCRD3[%XCRCP5P51@5;P1%V5REC?P61@59C?RF%U5RG%S5RH1958RI195:R:5851952R2%R8,95R858554H%Q3R3PH1P5<RJ=4H:P3PHA4H2IP3A;5I2RK94HJA4HK85BHC7C7C71MH4R4P7P1g00LQRLg00M1RM'L1J71==LMdAN5<6CORMb5b6b7X05X15X25X3511791161'212<;1291109;RL,2<12L?':[[[^05^15^25^35P7P?PAP@P>P6P1P9O7b4EEA3@ABP@11ABP>PBC5':P0f9RB10>@RL73@PB11@LPAPLC5f:RL?3A>P7f;RAPLP@PLC5f<R>10BARN,1APLPNC5PDPCP51@51P6PEC?PGP5PIg00fcA852KCD,THP4PMb5b6b7X05X151076,169=57^05^15P7f=RKPAO2b410L>,1>9=5LP510AKRL,1Kf?REf>RN,0>,0KRO737XF5P6PAP7EZPNPAP>PLC5PEP>POPAP7PDPCPFPGPHA858IA85:254HP3PHA4HJIRJP3A;58:9;5294HI9BHJC7C7P4PMb5b6b7X05X15X25X3511171196'212<610;?,09,21,:=[[^05^15^25^35P7PEPKPNP>P@PBO6b4EEA3E>APE11>APOPAC5':P0f@R0?3K>P011K>10KE,0NP>C5fAR>?3NKP7fBRK?3ENfC110E100K,0>PEC5P6W9W=P6P7O2n2001000000120000000b:b8b?W8W9P6P7O2n2001000000121000000b:WBWAW@W>XC5X<5XE5X;5WDo"). Qed.

Lemma c8_of_dc : forall m A, dc_at m A 8 -> exists w : word, rw_cells bsegs m A [C8 w].
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "p'0h01wh12H0h22bsh31Ah41Hh52H'h62_Hh71eh81mi001xp;1p;3p;2p;4g00;oj11Tg00MQj19Tg00Moj18Tg00NRj1:Tg00nnj1CTg00O4j3ATg001bj1>Tg00Ojj1=Tg00PJj2<Tg0047j1;Tg004Wj33Tg00oLj15Tg00gJR0j24Tg010Aj4BTg011;j17Tg00?fj32Tg0061R1j26Tg00^kj4@Tg00_Ej4?Tg00bcf2R2f1R3f0R4C?p=0g00Kl#1#1#1R5#1#1#1#9#8R6%95#8R7#:[g00De%C5R59A34P0%>7R7f3R8g00cXR9%=5/<4%;9R533R:702X27f4R;%54=395R<708X06,46P4f5R=?0;:f6R:P=P3P4CBf7R>?0:<%74R?=272'6X06,46P0P6f8R0?0><A27?8'6X06f9R>?00<X06,46P4f:R0?0><A27?='6P1f;%53=395700%73=27:f=R:f<R0;0<X06,46P4%58=39590:0%7;=27>P6f@f?;0<X06P=P3C@W6W5P3P4O2n2001000000120000000W1X06P3P4O2n2001000000120100000b7W4X27P3P4O2n2001000000121100000W1W3W8o"). Qed.
Lemma c8c8_of_dc : forall m A, dc_at m A 16 -> exists w1 w2 : word, rw_cells bsegs m A [C8 w1; C8 w2].
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "p'0h02bsh11Ah21Hh32H0h41mh52w1h62w2i001xp;1p;3p;2p;4g00;oj10Tg00MQj14Tg00Moj13Tg00NRj17Tg00nnj1>Tg00O4j3<Tg001bj1;Tg00Ojj1:Tg00PJj29Tg0047j18Tg004Wj32Tg00_Ej41Tg00oLj15Tg00gJR0j26Tg011kj4=Tg00Kl#0#0#0R1#0R2#0#0#4#3R3%41#3R1#7[g00Def1R4f0R5%>2R23<P0%;1R1g00bcR0f3f2g00cXR6%:2/95%86R232R7C1X01P0f5R8f4R9%54%55=262526C1X63,63X53,63P5P0P8P9P7C1f6P8P4P5C=W2X01P4P5O2n2001000000120100000W3W1W4o"). Qed.
Lemma c1_of_dc : forall m A, dc_at m A 1 -> exists b : byte, rw_cells bsegs m A [C1 b].
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "p'0h01bi001bh11Hh21Lh32H0h44__p1h54__p2h64__p3h74__x1h81xi011xh92L0h:7__arithh;4__ffh<8__varmaph=5__with>4__x2h?2bsh@1li021lhA1AhB2H1hC2_HhD3_H0hE3_H1hF2b0hG4cstrhH1mhI1yhJ2z0hK2z1p;1p;3p;2p;4p;<p;9p;6p;7p;8g00;oj1:Tg00MQj1_Tg00Moj1ZTg00NRj1dTg00nnj1}Tg00O4j3zTg001bR0j1WTg00OjR1j1mTg0047j1NTg012gj1QTg00gJR2j24Tg013\j4^Tg00ZXj1?Tg00QVR3j13Tg014Sj4@Tg015Ej1ATg00h_j1BTg016<j4MTg00PJj2JTg0171j1TTg017gj26Tg00?fj35j1RTg00`;j2STg00R6j2fTg00RYj3eTg00>`j2<Tg00S6l<PTg018Gj4OTg00S[j2bTg00acj2aTg0061R4j29Tg003>j2LTg005Wj2ITg008ij2`Tg00:Cj1|Tg00:aj1{Tg00;Lj2]Tg00Uej2\Tg00BNj4KTg00=\j1yTg00>>j2xTg00?:j2wTg00@@j3tTg00@_j4sTg004Wj32Tg00AQj4qTg018nl9pTg00^kj4oTg006LR5j1CTg003Zj2=Tg019nj1nTg006kj2HTg007Tj3VTg008=j2lTg009ej1kTg009Gj4rTg00<Tj3XTg00_Ej4jTg00`Xl<YTg00mRj6iTg00C9j7uTg00b?j7vTg00C]j7hTg00DAj8gTg00cXR6f2R7f1R8'Jf0R932p=1g00bcR:P7P8P9Cjp=0A2689p=Gg00dMR;?589p=7g00DeR<?589p=;P<P;P<P<P1f4R1P3f3R=g00dlP7P8P9M<Yp=cP8g00EjR>g00FIR?P?g00FiR@P9Eip=DP<P8g00fcP9CKp=FP8P>P?P?P@P9g00GIFup=8P7P>P?P?P@P8P9Fvp=EP7P>P?P?P@P8P9Fhp=[P=P>P?P?P@P7P8P9Ggp=>P;P;P<P<P5P3P3P=g01:SP7P8P9M<Yp=Ug00KlR5#:R>#:#:RA#:#:#:#_#Z%_A#ZRA#d[%}5RB9z89P2%WAR2%mBRC%N6R6719RD90=7X?2%Q9/G6RE901=X0A,4AP9f5RF?01DP9f6RGA1C8670FP4P:f7RHPGA1C76RIC^P:PHPG%?I#3C@f9RIf8RJ;0EX0A,4AP9P:PIPJA1C16C^P4A1CF6RK#AP:f:RLPI%BKCMP:f;PLA1CG6#?#3C@f=RKf<RM;0EX0A,4A[P9A1CH6#AP41JCJ#T%A6RJP:f>R4PKA1CI6#BCMP:f?P41JCLRL/G6#?#3C@fARIf@RN;0EX0A,4A[[P9%TLP:PIPNA1CM6#BCMP:fBRMPIA1CK6#?#3C@P0PAfDfCRI;0D16A8/7CfGRDfFRN;0EX0A,4A]2]1P4%NAR4=1C690IM16A4/7Cg00JaRI=5;Cg00H[RM1SMBRL55<ROP;P<%R;RPP3%R<RQ%38%39';17891f893eXI;X8;RRPIPM1<<MPC1SM9X8<RSPBO1RTP9X8<PSPBPB1<<BDcRSM<PP9COPO1bMBRO1aMBRU1;LB'91LBMRVA5<LM'9'IRWPLP<p-0RXg00J5RY#NRZ%WYR[1`<8%|<R\%{<R]1D]=1]<5R51\<BR^'F,8]5E]P<P^g00ECR_1\<MR`CK,8]Ra1D]1Rb5E]5[]%y?R?P]1F`5,8]P?1D]FRcC>C>1x]@R@P9P7g00LQRdg00M1Re'<1w97=5dedAt<M8CsReb;b<b=X7<X4XX5XW61;9B,9819V7'IA5<M8PF[[^7<^4X^5X^6XP9fJRdfIRf;0EX0ARg,4AA5<8MRhPUP8P7P=O6b:bJb3b9W2W1P0PAfHR0A2A79=1C670DA2A=8,6A/7CfKRi?0dEX0A,4A]2]1P9A2A84=1C690DNA2A74,6A/7CPAPgP=P:PfP0A2A=4=1C6R4%Q=/G6R0P8g01;7RfPfg00I9RfPfCq%A0e%B4,<2%?4,<;M9pCoW2W1A2A8992AF=1C690idA2A7892AG,6A/7C16A7Ri#CRd#CR6/7C%3iRF/=B/=B/;LR4P;P<PPP3PQPRP61=9BX8<R6P6PFO1RRO1P6PdPRP6PiPF1<<FCUCUPCPTPSM<PP9COP416A=R4#n%34,LMPOPWPLP<%CIRL#C,H<1H<L1H<I5V<5V<g00K@'l=2YZP[P<1`<7P8%k<CrP\P]1]<>R>/F^,8]9E]bAE]ac5[]P?P]P<P`P_P5CK,8]P?P]AX<5^=X<^/F>,8]P?1D]GC>C>C>P@Peb;b<b=X7<X><X4XX5XX6X1;8B,9719V='I1LM81=7B/=B/;=PH[[[^7<^><^4X^5X^6XP9fSfR;0EX0A,4APhPUP816AH#3P7P=P1O8b:bKbBbGb9W2W1X@2XFAP8P9O2n10110200020121100102X@2X0AP8P9O2n10110200020121100102PKP=O2WEWDXCJW2P8P9O2n2001000000121000000W3P8P9O2n2001000000121000000W3P8P9O2n2001000000121000000b3W1X?2P8P9O2n2001000000121101000W3XA<WHo"). Qed.
Lemma dc_of_cells : forall m A cs, rw_cells bsegs m A cs -> dc_at m A (Z.of_nat (cells_size cs)).
Proof.
ltac2:(KReplay.run1 (kr_t_FsKit ()) ["CANSEC1"] "h02H0h14__x1h21Ah31Hh42WFh52_Hh63_H0h77__arithh84__ffh98__varmaph:5__with;2bsh<2csh=4cstrh>1lh?1mh@1nhA1xhB1yp;1p;2p;3p;4p;6p;<p;7p;9p;Bg00;oj15Tg00MQj1DTg00Moj1ATg00NRj1ITg001bj1:Tg00ZXj11Tg00QVR0j13Tg00Ojj1=Tg00PJj26Tg0047j19Tg004Wj37Tg00h_j12Tg013\j4ETg014Sj4;Tg015Ej1<Tg016<j4CTg017gj2WTg00?fj30j1>Tg01;Sj2VTg01<Tj4BTg00AQj4UTg00>`j28Tg00Y]j3PTg00iYj2OTg000ij6?Tg00Q?j2LTg003ZR1j2@Tg00R6j2JTg00RYj3KTg00S6l<MTg019nj1NTg003>j2GTg008ij2QTg00:Cj1RTg00:aj1FTg00;Lj2STg00Uej2TTg00<Tj3dTg00BNj4cTg00C9j7bTg00>>j2aTg00?:j2`Tg00@@j3]Tg00@_j4ZTg00VHj4[Tg018nl9\Tg01=0j1YTg00^kj4XTg00_Ej4^Tg00a=lB_Tg00bcR2f2R3f1R4f0R5C^p=4g00dMR6P6P6g00DeR7P7P7g00\jP0P0P0P1g00eYf3R1P3P4g00JaR8g00H[R9P5MB_p=Hg00KlR:#5#5#5R;#5#5#5#D#A%D;#AR;#I[g00cXR<#:A4345%:;R=f4R>%13#3R?#=/65%9<R@57<741X;=%24P6%14RA%23,65=7<@94>1X@6P5A4134g0061RBP2P>P1P3CEP2P>P1P?C;f5R?%11%21'6=7<@74>P5P2f6R1P?P>CEPB%<?P2f7RBP1%2?CCP2f8R?PB%11#3C;f9R1%1B%2B'6=7<@74?[P5%<BP2f:RBP1%2?CCP2f;R?PB%11#3C;P2f<R2P?PB%1BR>%2BRC'6=7<@R@P11W;CR1=06>g01;7P6P>P1P6P1P>1VB3CBCBg00I9CU%<@eP=PC%2?90=5X>=18=C%9;9P;C1O;CE?%2@=0=Ce1L>8R8=06>%3>RC/@9R==07CP6P7%>6P0%>7%34%35507A06451J453KXB6XA6P8P=P>PC187CR=1879CHP>PCP=M<M%N>1G9Cg00J5RC#9%:C1Q74%R7%F7RCg00Ejg00FIR=P=g00FiR=P71S7:R:1T795d7g00fcP:Ccg00GIFb1aC=P5P3g00LQR=g00M1RC'81`53=0=CdA]794CZb8b9b:X171@59=075^17P5%12#3O1b7b=C[%1@=06>eM9\W6W5W4P4P5O2n2001000000121000000W0P4P5O2n2001000000121000000b0%3A#=%YAE?CXW3W<X27W?o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dc_at_any2 : forall m m' A n,
  dc_at m A n -> wmono bsegs m m' -> (0 <= A /\ A + n <= 0x10000 \/ 0x60f000 <= A) -> dc_at m' A n.
Proof.
  intros m m' A n [bs [[[WF _] [B0 [B1 BR]]] [W0 [W1 WR]]]] WM HA. cbn [cells_size csize cells_bytes cbytes app Nat.add] in *.
  rewrite app_nil_r in B1, BR. cbn in WF. rewrite Nat.add_0_r in W1, WR.
  assert (RD : forall i, 0 <= i < Z.of_nat (length bs) -> exists b, m' (wa (A + i)) = Some b).
  { intros i Hi. specialize (WR i ltac:(lia)). apply WM in WR.
    rewrite ref_wview_overlay in WR by (rewrite wa_unsigned by lia; lia).
    destruct (m' (wa (A + i))) as [b|]; [exists b; reflexivity| congruence]. }
  assert (BS : forall k, (k <= length bs)%nat -> exists bs' : list byte, length bs' = k /\
            forall i, (i < k)%nat -> m' (wa (A + Z.of_nat i)) = nth_error bs' i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi. lia.
    - destruct (IH ltac:(lia)) as (bs' & L & E). destruct (RD (Z.of_nat k) ltac:(lia)) as [b Hb].
      exists (bs' ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eq_dec i k) as [->|NE].
      + rewrite nth_error_app2 by lia. rewrite L, Nat.sub_diag. cbn. exact Hb.
      + rewrite nth_error_app1 by lia. apply E. lia. }
  destruct (BS (length bs) ltac:(lia)) as (bs' & L & E).
  exists bs'. split; [split; [cbn; destruct WF as [WF _]; split; [lia| exact I]|]|].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. split; [lia|]. split; [rewrite L; lia|].
    intros i Hi. unfold mrd. rewrite (E i ltac:(lia)).
    destruct (nth_error bs' i) eqn:N; [reflexivity|]. apply nth_error_None in N. lia.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. apply WM. apply WR. lia.
Qed.
Lemma dc_at_any : forall m m' A n,
  dc_at m A n -> wmono bsegs m m' -> 0x60f000 <= A -> dc_at m' A n.
Proof. intros m m' A n D W H. eapply dc_at_any2; [exact D | exact W | right; exact H]. Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall a : word, 0x60f000 <= bv_unsigned a -> seg_rom bsegs a = None.
Proof. intros a Ha. unfold seg_rom. rewrite ref_memory_read_none; [reflexivity| cbn; lia| lia]. Qed.
Lemma mrd_high : forall m a, 0x60f000 <= a < 2^64 -> mrd bsegs m (wa a) = m (wa a).
Proof.
  intros m a Ha. unfold mrd. destruct (m (wa a)); [reflexivity|]. apply seg_rom_high. rewrite wa_unsigned by lia. lia.
Qed.
Lemma rw_C1_high : forall m a (b : byte), rw_cells bsegs m a [C1 b] -> 0x60f000 <= a -> m (wa a) = Some b.
Proof.
  intros m a b [[WF [B0 [B1 BR]]] _] Ha. specialize (BR 0%nat ltac:(cbn; lia)). cbn in BR, B1.
  rewrite Z.add_0_r in BR. rewrite <- mrd_high by lia. exact BR.
Qed.
End CANSEC1.
