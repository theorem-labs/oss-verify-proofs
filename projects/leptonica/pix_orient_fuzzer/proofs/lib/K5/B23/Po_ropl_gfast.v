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
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Km_setelem Km_iface Km_kit Bi_ropkit LeptB_guard LeptB_guard2 LeptB_guard3 Po_ropl_iface Po_ropl_wa12k.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_ropl_gfast () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53Lib6MState2MSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7mod_addC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z8add_commC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z9land_onesK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08c69OSSVerify5KrLib2K53B23=Po_ropl_gfast=gf_land31_32qC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z7div_addC56Stdlib6ZArith6BinInt1Z7div_mulC56Stdlib6ZArith6BinInt1Z7div_modC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions8bv_swrapK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z9add_assoc".   (* [comment removed for export] *)
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Ltac2 gn_isk (r : Std.reference) (k : constant) : bool := match r with Std.ConstRef k' => Constant.equal k k' | _ => false end.
Ltac2 rec gn_lit (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Constructor _ _ => true
  | Constr.Unsafe.App h args =>
      (match Constr.Unsafe.kind h with
       | Constr.Unsafe.Constructor _ _ => Array.for_all gn_lit args
       | Constr.Unsafe.Constant k _ => if gn_isk reference:(Z_to_bv) k then Array.for_all gn_lit args else false
       | _ => false end)
  | _ => false
  end.
Ltac2 gn_ops () : Std.reference list :=
  [ reference:(Z.add); reference:(Z.sub); reference:(Z.mul); reference:(Z.opp); reference:(Z.land); reference:(Z.lor);
    reference:(Z.lxor); reference:(Z.shiftl); reference:(Z.shiftr); reference:(Z.modulo); reference:(Z.div); reference:(Z.ltb);
    reference:(Z.leb); reference:(Z.eqb); reference:(Z.b2z); reference:(negb); reference:(andb); reference:(orb); reference:(xorb);
    reference:(Z.pow); reference:(Z.lnot); reference:(Z.abs); reference:(Z.max); reference:(Z.min); reference:(Z.quot); reference:(Z.rem);
    reference:(bv_swrap); reference:(bv_wrap); reference:(bv_unsigned); reference:(bv_signed); reference:(bv_eqb); reference:(bv_ltu);
    reference:(bv_lts); reference:(bv_leu); reference:(Z.of_nat); reference:(Z.testbit); reference:(Z.ones); reference:(Z.sgn) ].
Ltac2 gn_isop (ops : Std.reference list) (h : constr) : bool :=
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant k _ => List.exist (fun r => gn_isk r k) ops
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 gn_isdiv8 (h : constr) (args : constr array) : bool :=
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant k _ => if gn_isk reference:(Z.div) k then Constr.equal (Array.get args 1) constr:(8%Z) else false
  | _ => false
  end.
Ltac2 rec gn_term (ops : Std.reference list) (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      let args' := Array.map (gn_term ops) args in
      let t' := Constr.Unsafe.make (Constr.Unsafe.App h args') in
      if gn_isop ops h then
        (if Array.for_all gn_lit args' then
         if gn_isdiv8 h args' then t' else
           (let v := Std.eval_vm None t' in if gn_lit v then v else t') else t')
      else t'
  | Constr.Unsafe.Case ci ret iv c brs =>
      Constr.Unsafe.make (Constr.Unsafe.Case ci ret iv (gn_term ops c) brs)
  | _ => t
  end.
Ltac2 gnorm_goal () : unit :=
  let g := Control.goal () in
  let g' := gn_term (gn_ops ()) g in
  if Constr.equal g g' then () else Std.change None (fun _ => g') { Std.on_hyps := Some []; Std.on_concl := Std.AllOccurrences }.
Ltac gnorm := ltac2:(Control.enter gnorm_goal).
Ltac2 gnorm_hyp (h : ident) : unit :=
  let t := Constr.type (Control.hyp h) in
  let t' := gn_term (gn_ops ()) t in
  if Constr.equal t t' then () else Std.change None (fun _ => t') { Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)]; Std.on_concl := Std.NoOccurrences }.
Ltac gnorm_in H := let f := ltac2:(h |- match Ltac1.to_constr h with
    | Some c => (match Constr.Unsafe.kind c with Constr.Unsafe.Var i => gnorm_hyp i | _ => () end)
    | None => (match Ltac1.to_ident h with Some i => gnorm_hyp i | None => () end) end) in f H.

(* [comment removed for export] *)
Lemma evt_if_t : forall segs Q R F (c : bool) (a b : word) fc rv m ro,
  c = true -> evt segs Q (MS R F a fc rv m ro) -> evt segs Q (MS R F (if c then a else b) fc rv m ro).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "p'0h01ci001ch11Fh21Qh31Rh41ah51bh62fch71mh82roh92rvh:4segsp;1p;2p;3p;7p;6g0000j1:Tg000Pj10Tg0015j18Tg001Zj11Tg0028j12Tg002[j29Tg003Gj15Tg003ij37Tg004Cj73Tg0058j34Tg005lj66Tg006J#:g007Ip-0[g008P#0R0#8#1%00#0R0#0#0R1#0#1#2R2'9R3g0095R4%11#2%52%10#2#5\2R0f6R1g009UR5574f;R6f:R7f9f8R8P1f4R9f3R:f2f1R;F334P4P5f=f<P6P7P4P2f0R7P8f7n0110000020000P1f5P9P:F334X04P7P8P;E6UUX80W7W9W6X52X42W0X13W3W2W:o"). Qed.
Lemma evt_if_f : forall segs Q R F (c : bool) (a b : word) fc rv m ro,
  c = false -> evt segs Q (MS R F b fc rv m ro) -> evt segs Q (MS R F (if c then a else b) fc rv m ro).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "p'0h01ci001ch11Fh21Qh31Rh41ah51bh62fch71mh82roh92rvh:4segsp;1p;2p;3p;7p;6g0000j1:Tg000Pj10Tg0015j18Tg001Zj11Tg0028j12Tg002[j29Tg003Gj15Tg003ij37Tg004Cj73Tg0058j34Tg005lj66Tg006J#:g007Ip-0[g008P#0R0#8#1%00#0R0#0#0R1#0#1#2R2'9R3g0095R4%11#2%52%10#2#5\2R0f6R1g00:5R5574f;R6f:R7f9f8R8f5R9f4R:f3R;f2f1R<F334P4P5f=f<P6P7P4P2f0R7P8f7n0110000020000P1P9P:P;F334X04P7P8P<E6UUX80W7W9W6X52X42W0X13W3W2W:o"). Qed.
(* [comment removed for export] *)
Ltac is_trapj segs p := first [ lazymatch p with 1287264 => idtac end
  | instr_at segs p ltac:(fun i => lazymatch i with Jal _ ?imm =>
      let t := eval vm_compute in (p + bv_signed imm) in lazymatch t with 1287264 => idtac end end) ].
Ltac xcond := first [ reflexivity | try guard_fix; first [ reflexivity | cnorm; solve_cond_rec ] ].
Ltac xbrT := apply evt_if_t; [ xcond | ].
Ltac xbrF := apply evt_if_f; [ xcond | ].
Ltac tbr := lazymatch goal with |- evt ?segs _ (MS _ _ (if ?c then Z_to_bv 64 ?T else Z_to_bv 64 ?E) _ _ _ _) =>
  first [ is_trapj segs T; xbrF | is_trapj segs E; xbrT | br | progress guard_fix; try br ] end.
Ltac is_load := next_instr ltac:(fun i => lazymatch i with Load _ _ _ _ _ => idtac end).
Ltac gwalk1_fast :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => gnorm; first [ shbr | shbr0 | shbr_inv | shbr_x3 | tbr ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => (try (is_load; gnorm)); first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
(* [comment removed for export] *)
Ltac gwalk1_tbr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | shbr_inv | shbr_x3 | tbr ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.

(* [comment removed for export] *)
Ltac wguard z := lazymatch z with context [bv_swrap _ _] => fail | context [bv_wrap _ _] => fail | context [_ mod 18446744073709551616] => fail | _ => idtac end.
Lemma gf_land31_32q : forall q c, 0 <= q -> 0 <= c -> Z.land (32 * q + c) 31 = c mod 32.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "h01zh17__arithh24__ffh38__varmaph45__with51Ch61Qh71ch81qp;2p;1p;3p;4p;6p;7g00:Uj2;Tg000Pj12Tg00;1j15Tg00;Oj27Tg00;lj24Tg0015j1LTg00<Ij2FTg00<fj20Tg003ij31Tg00=Fj29Tg00=`j1>Tg0000j1=Tg00>@j1<Tg00>^j1NTg00?<j1MTg00?gj26Tg00@Jj4:Tg00A5j6KTg00AYj2ETg00B;j2DTg00Bgj3CTg00CFj4BTg00D8j4ATg005lj63Tg00DYj2@Tg00E;j2GTg00E]j1HTg00F;j2?Tg00FYj3ITg00G<j7JTf1R0g00G`R1g00H?R2P2g00H_R3f0R4g00I?FJp=8g00I_R5g00J=R6/;0R7P5g008P#2R8#2#2#2#2#5R9f3R:'7R;f2R<'4R=%58%L8#5R8'F'010:9R>9154X05R?P514<;1049=15>X05P517:9R@14:4/09=15>X05P510<9R>P?195>14<@/09P<P:P9g00J[R@#>R>%=@R@%<5R?%N5RA%M5RBP1P2P2P3P51659g00KG1656R2C:,8BEK1EB3R3P4P<g0095R1g009URC'91D4<=11CdAC560CBR0b2b3b4A1596g00Kn[P4b1CAE3P;1@9:E3P=1G;<E3%H8,?=P>P@P?PAP5P2g00LK1658C:,8BP3P0b2b3b41;68P4b19I=8E3X57W6X75W8o"). Qed.
Lemma gf_land31_32q0 : forall q, 0 <= q -> Z.land (32 * q) 31 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h51zh61Qh71qp;2p;1p;3p;4p;8p;6p;7g00:Uj23Tg000Pj10Tg00;1j17Tg00;Oj2<Tg00;lj2NTg0015j11Tg00F;j25Tg003ij32Tg00<fj2>Tg00=Fj28Tg00=`j1;Tg0000j1:Tg00M2j29Tg00>^j1MTg00?<j1LTg00?gj2KTg00MPj2DTg00@Jj46Tg00N3j1CTg00NUj8BTg00AYj2ATg00B;j2@Tg00Bgj3?Tg00CFj4ETg00>@j1FTg00O9j4GTg005lj6HTg00P@j1=Tg00Paj6ITg00G<j7JTf1R0g00G`R1g00H?R2P2g00H_R3f0R4g00I?FJp=4g00I_R5g00J=R6/34R7P5g008PR8#0#0#0#0#0#7R9/<0R:/N6R;%18#1#1#1#7R<,54=256X55P51>69A2546X55185615;<P0P6g00J[R<#;R;%:<R<1950%M5R9%L5R=P1P2P2P3P51K56R1g00LKR>1D58C6,4=R8%C2P8GB1A=3R3P4f2R8g0095R2g009UR?'81@48=22?dA?560CER?b1b2b3X451360\7^45P4P8P0O2b0P;P<%F5P9P5P1P>P1C6,4=P3P?b1b2b31366P4b0CGEHP:%=:EIW6W7o"). Qed.
Lemma gf_div32_32q : forall q c, (32 * q + c) / 32 = q + c / 32.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "h01zh17__arithh24__ffh38__varmaph45__with54__x1h64__x2h76__sat0h81ch91qp;1p;2p;3p;4p;6p;7g000Pj13Tg00;1j1NTg00;Oj2:Tg00;lj20Tg00Q=j22Tg003ij31Tg00QZj2HTg00:Uj25Tg00=`j1@Tg0000j1?Tg00M2j2>Tg00>@j1=Tg00RKj4<Tg00>^j1MTg00?<j1LTg00MPj2;Tg00Rij39Tg00@Jj47Tg00AYj2GTg00=Fj2DTg00B;j2CTg00Bgj3BTg00CFj4ATg00?gj28Tg00A5j6ETg00SLj4FTg005lj64Tg00DYj2ITg00E;j2JTg00G<j7KTf1R0g00G`R1g00H?R2P2g00H_R3f0R4g00I?FKp=6g00I_R5P5g008PR6#3R7#3#3#3#3#NR8/:0R9,041248R:f2R;1208'0R<515X05P51:08R=1004R>/28=15<X05P510:0A154<X051H48g00J=R</5415<812;8R:,5<[[g00J[R?#@R@%??R?P51>5;P0%=5RAC<%M5RB%L5RCP51;56R61;57R7595g00KGRDA9576C7'61GC3R7P4P;g0095R6g009URE'D1C4;=16EdAB5<0CAREb2b3b4X55X651040=15>^55^65P4f3P:O2b1b7104=/28P4P0P8P@P?PAPBPCP1P2P2P3P51858PD185<C7,6CEEP7PEb2b3b4A158<g00Kn[P4b1CFE4P91I80E410941J94E4X85W9o"). Qed.
Lemma gf_div32_32q0 : forall q, (32 * q) / 32 = q.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "h01zh17__arithh24__ffh38__varmaph45__with51qp;1p;2p;3p;4p;7p;6g000Pj10Tg00;1j1ETg00;Oj23Tg00Q=j24Tg003ij31Tg00=Fj25Tg00=`j1<Tg0000j1;Tg00>@j1:Tg00>^j18Tg00?<j17Tg00?gj22Tg00@Jj49Tg00G<j7DTg00A5j6CTg00AYj2BTg00B;j2=Tg00Bgj3>Tg00CFj4?Tg00Smj3@Tg005lj66Tg00DYj2ATg00I_R0P0f0R1g008P#0#0#0#0#0#ER2'3R31412f1R4510X00P0P1A1014X0015011432g00J[R3#<%;3%:0%80%70R3g00G`R5g00H?R6P6g00H_R7P3P5P6P6P7P01202g00KGg00J=R6,20C9g00I?FDEC1B37P1f2R7g0095R3g009UR5'51=17=135dA>064C?b2b3b4A1026g00Kn[P1b19@12E613211A21E6W5o"). Qed.
(* [comment removed for export] *)
Lemma gf_sw_m64_l : forall x y, bv_swrap 32 (x mod 18446744073709551616 + y) = bv_swrap 32 (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "h07__arithh14__ffh28__varmaph35__with46__sat0h56__sat1h64__x1h74__x2h84__x3h94__x4h:1zh;2Exh<1Hh=1xh>1yp;1p;2p;3p;4p;8p;6p;7g000Pj10Tg00;1j1ATg00=`j1iTg0000j1[Tg00>@j1WTg00>^j1UTg00?<j1TTg00?gj2>Tg00AYj2hTg00=Fj2JTg00B;j2]Tg003ij3<Tg00Bgj3YTg00CFj4XTg00TNj3VTg00Q=j29Tg00;Oj24Tg00<fj21Tg00;lj22Tg00Toj2GTg00QZj2FTg00U`j1STg00V>j2RTg00V_j1QTg00W>j2DTg00Wgj3OTg00XPj3NTg00Y9j2MTg00Yej3PTg00M2j2CTg00RKj4ETg00MPj2?Tg0015j1LTg00ZEj3BTg00N3j1gTg00Zhj2fTg00NUj8eTg00[Kj1@Tg00[hj2=Tg00D8j4\Tg005lj6ZTg00Paj6^Tg001Zj1_Tg00\Ej2HTg00@Jj4`Tg00G<j7aTg00A5j6bTg00:Uj2cTg00Rij3dTf0R0#0#0p=K%00#0#0#0#0#0#0#0p=7g00I_R1f1R2g00KGP0C`p=:P2g00G`R3g00H?R4P4g00H_R5P0g00I?Fap=;P2P3P4P4P5P0Ebp=IA<120p=6g00J=R6/c0p=3Ad120p=8f2R7/22/20p=5g008PR8#0R9#0R:#0#KR;#K#7#7#7R<#0R=#7#7#7#7#AR>g00J[R?#iR@%[?RA%W1RB%U1RC%T1RD1>1>RE1>16RF':,;D'I1hD5RGP0P7g0095RHg009URI'J1]07=<HIdAY162CXRIb1b2b3A<1>6g00KnRH[P0b05V2192>,4>112>RJ'2,621G7>%37%3>RKf4RL/1>#3[[f3RM/F>%3MRNf5RO/9>RP#3\K[%S8,R1g00\lRQ#Q,D15O11D1Q5N1g00]K'M=P?@PAP1P11C1LP7PBCEP21C1MCEPCPDP3P4P4P51?18R5%L8,?1R89B1E1?1:R:'8':,;D%g41?19R9,85%A<R<,>1R5'8%A=R=,>1R4=B18,f1=B14'818:9/85':,;DGePGPIb1b2b3X61X71X81X9114>7/2M,60122714=M#@/4=75<A5L7<'6[^61^71^81^91P011O>R5PPPLPOPMO5b0b4b51272197>,4=#@/4=75<117>?52<'6P1A5M7<RO19M>,4=#@RP/4='2R9110=/=<A5LM</1=/=<R:'6X:1P111O=R81=0</6:X:11=8<,J1119=POPPP=1GM>%35\K\N1FL>%3Lf6/9>#3\K[P@PAPBPC1:4F,;D,IDPGPIb1b2b3A<1=6PH[P0b0b4b5C\EZ11M>?57<P0E^b<b;%_;R;12J0'H1220,H;'6eX>1X=1o"). Qed.
Lemma gf_sw_m64_ls : forall x y, bv_swrap 32 (x mod 18446744073709551616 - y) = bv_swrap 32 (x - y).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "h07__arithh14__ffh28__varmaph35__with46__sat0h56__sat1h64__x1h74__x2h84__x3h94__x4h:1zh;2Exh<1Hh=1xh>1yp;1p;2p;3p;4p;8p;6p;7g000Pj10Tg00;1j1@Tg00=`j1hTg0000j1[Tg00>@j1WTg00>^j1UTg00?<j1TTg00?gj2>Tg00AYj2gTg00=Fj2GTg00B;j2]Tg003ij3<Tg00Bgj3YTg00CFj4XTg00TNj3VTg00Q=j28Tg00;Oj24Tg00<fj23Tg00;lj22Tg00Toj2FTg00QZj2ETg00U`j1STg00V>j2RTg00V_j1QTg00W>j2CTg00Wgj3OTg00XPj3NTg00Y9j2MTg00Yej3PTg00M2j2BTg00RKj4DTg00MPj2=Tg0015j1LTg00ZEj3ATg00Rij3;Tg00N3j1fTg00^7j3JTg00Zhj2eTg00NUj8dTg00[hj21Tg00[Kj1?Tg00D8j4\Tg005lj6ZTg00Paj6^Tg001Zj1_Tg00\Ej2HTg00@Jj4`Tg00G<j7aTg00A5j6bTg00:Uj2cTf0R0#0#0p=K%00#0#0#0#0#0#0#0p=6g00I_R1f1R2g00KGP0C`p=9P2g00G`R3g00H?R4P4g00H_R5P0g00I?Fap=:P2P3P4P4P5P0Ebp=IA<120p=7g00J=R6/c0p=5g008PR7#0R8#0R9#0#KR:#K#6#6#6R;#0R<#6#6#6#6#@R=g00J[R>#hR?%[>R@%W1RA%U1RB%T1RC1>1=RD1>16RE'9,:C'I1gC5RFP0f2RGg0095RHg009URI'G1]0G=<HIdAY162CXRIb1b2b3A<1=6g00KnRH[P0b05V2182=,4=132=RJ'2,721FG=%5G%5=RKf4RL/3=#5[[f3RM/E=%5MRNf5RO/8=RP#5\K[%S7,R1g00\lRQ#Q,C15O11C1Q5N1g00]K'M=P>?P@P1P11B1LPGPACDP21B1MCDPBPCP3P4P4P51=17R5%L7,=1R79A1D1=19R95;1'9,:C%f41=18R89J15%@;R;,>1R55;1%@<R<,>1R4=A17,e1=A145;1AJ198=;15'9,:CGdPFPIb1b2b3X61X71X81X9114=G/2M,70112G/2;14<M#?/4<'211LG/2;'7[^61^71^81^91P013O=R5PPPLPOPMO5b0b4b511G2/2;18G=,4<#?/4<'213G=/12/2;'7P111MG/2;RO18M=,4<#?RP/4<'2R8130</1;11LM/2;/3</1;R9'7X:1P113O<R7110;/79X:1117;,G1138<POPPP<1FM=%55\K\N1EL=%5Lf6/8=#5\K[P?P@PAPB194E,:C,ICPFPIb1b2b3A<1<6PH[P0b0b4b5C\EZ13M=/1G/2;P0E^b<b;%_:R:11J0'H1120,H:'7eX>1X=1o"). Qed.
Lemma gf_sw_m64_r : forall x y, bv_swrap 32 (x + y mod 18446744073709551616) = bv_swrap 32 (x + y).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "h07__arithh14__ffh28__varmaph35__with46__sat0h56__sat1h64__x1h74__x2h84__x3h94__x4h:1zh;2Eyh<1Hh=1xh>1yp;1p;2p;3p;4p;8p;6p;7g000Pj10Tg00;1j1ATg00=`j1iTg0000j1[Tg00>@j1WTg00>^j1UTg00?<j1TTg00?gj2>Tg00AYj2hTg00=Fj2JTg00B;j2]Tg003ij3<Tg00Bgj3YTg00CFj4XTg00TNj3VTg00Q=j29Tg00;Oj24Tg00<fj21Tg00;lj22Tg00Toj2GTg00QZj2FTg00U`j1STg00V>j2RTg00V_j1QTg00W>j2DTg00Wgj3OTg00XPj3NTg00Y9j2MTg00Yej3PTg00M2j2CTg00RKj4ETg00MPj2?Tg0015j1LTg00ZEj3BTg00N3j1gTg00Zhj2fTg00NUj8eTg00[Kj1@Tg00[hj2=Tg00D8j4\Tg005lj6ZTg00Paj6^Tg001Zj1_Tg00\Ej2HTg00@Jj4`Tg00G<j7aTg00A5j6bTg00:Uj2cTg00Rij3dTf0R0#0#0p=K%00#0#0#0#0#0#0#0p=7g00I_R1f1R2g00KGP0C`p=:P2g00G`R3g00H?R4P4g00H_R5P0g00I?Fap=;P2P3P4P4P5P0Ebp=IA<120p=6g00J=R6/c0p=3Ad120p=8f2R7/22/20p=5g008PR8#0R9#0R:#0#KR;#K#7#7#7R<#0R=#7#7#7#7#AR>g00J[R?#iR@%[?RA%W1RB%U1RC%T1RD1>1>RE1>16RF':,;D'I1hD5RGP0P7g0095RHg009URI'J1]07=<HIdAY162CXRIb1b2b3A<1>6g00KnRH[P0b05V0190>,4>110>RJ'2,601G2>%32%3>RKf3RL/1>#3[[1F7>%37RMf4RN/9>RO#3\K[%S8,R1g00\lRP#Q,D15O11D1P5N1g00]K'M=P?@PAP1P11C1NP7PBCEP21C1LCEPCPDP3P4P4P51?19R9%L8,?1R59B1E1?1:R:'8':,;D%g41?18R8/89%A<R<,>1R9'8%A=R=,>1R4=B15,f1=B14'8188:/89':,;DGePGPIb1b2b3X61X71X81X9114>7/2L,62122714=L#@/4=75<A52N<'6[^61^71^81^91P011N>R9POPNf5ROPLO5b0b4b51272192>,4=#@/4=75<112>=57<'6P1A5L7<R8197>,4=#@R:/4='2R5110=/=<A5NL</1=/=<RN'6X:1P1118=RE1=0</6NX:11=E<,J1115=P8P:P=1G7>%39\K\M1FL>%3L19O>#3\K[P@PAPBPC1:4F,;D,IDPGPIb1b2b3A<1=6PH[P0b0b4b5C\EZ117>=5L<P0E^b<b;%_;R;122J'H1220,H;'6eX>1X=1o"). Qed.
Lemma gf_sw_m64_rs : forall x y, bv_swrap 32 (x - y mod 18446744073709551616) = bv_swrap 32 (x - y).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "h07__arithh14__ffh28__varmaph35__with46__sat0h56__sat1h64__x1h74__x2h84__x3h94__x4h:1zh;2Eyh<1Hh=1xh>1yp;1p;2p;3p;4p;8p;6p;7g000Pj10Tg00;1j1?Tg00=`j1fTg0000j1ZTg00>@j1VTg00>^j1TTg00?<j1STg00?gj2:Tg00AYj2eTg00=Fj2GTg00B;j2^Tg003ij3=Tg00Bgj3XTg00CFj4WTg00TNj3UTg00Q=j28Tg00;Oj24Tg00<fj23Tg00;lj22Tg00Toj2DTg00QZj2HTg00U`j1RTg00V>j2QTg00V_j1PTg00W>j2ATg00Wgj3NTg00XPj3MTg00Y9j2LTg00Yej3OTg00M2j2BTg00RKj4CTg00MPj2>Tg0015j1KTg00ZEj3@Tg00Rij3;Tg00N3j1dTg00^7j3ITg00NUj8cTg00[hj21Tg00D8j4]Tg005lj6\Tg00Paj6[Tg001Zj1YTg00\Ej2FTg00@Jj4_Tg00G<j7`Tg00A5j6aTg00:Uj2bTf0R0#0#0p=J%00#0#0#0#0#0#0#0p=7g00I_R1f1R2g00KGP0C_p=<P2g00G`R3g00H?R4P4g00H_R5P0g00I?F`p=9P2P3P4P4P5P0Eap=EA=120p=6g00J=R6/b0p=5g008PR7#0R8#0R9#0#JR:#J#7#7#7R;#0R<#7#7#7#7#?R=g00J[R>#fR?%Z>R@%V1RA%T1RB%S1RC1:1=RD1:16RE'<,9C'E1eC5RFP0f2RGg0095RHg009URI'G1^0G==HIdAX162CWRIb1b2b3A=1=6g00KnRH[P0b05U0180=,4=130=RJ'2,601D2=%52%5=RKf3RL/3=#5[[1HG=%5GRMf4RN/8=RO#5\K[%R7,Q1g00\lRP#P,A15N11A1P5M1g00]K'L=O>?P@P1P11B1NPGPACCP21B1LCCPBPCP3P4P4P51>18R8%K7,>1R59@1D1>19R95;1'<,9C%d41>17R7=I18%?;R;,:1R85;1%?<R<,:1R4=@15=@145;1AI179=;18'<,9CGcPFPIb1b2b3X61X71X81X9114=G/2L,62112G/2;14<L/4<'2112N/2;'6[^61^71^81^91P013N=R8POPNf5ROPLO5b0b4b511G2/2;182=,4</4<'2132=,1G/2;'6P111LG/2;R718G=,4<R9/4<'2R5130</1;11NL/2;/3</1;RN'6X:1P1137<RD110;/6NX:111D;,G1135<P7P9P<1DG=%58\K\M1HL=%5L18O=#5\K[P?P@PAPB1<4E,9C,ECPFPIb1b2b3A=1<6PH[P0b0b4b5C]E\13G=,1L/2;P0E[b<b;%Y:R:112J'F1120,F:'6eX>1X=1o"). Qed.
Lemma gf_b2z_lor1 : forall b, Z.lor (Z.b2z b) 1 = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "p'0h01bi001bp;1p;2p;3g00^Zj14Tg00;1j13Tg00_7j20Tg003ij31Tg00=Fj22Tg0095R0P0g00I_R0f0R1#4g008P#3R2'0;12P11202R2P2n0110000020000W0o"). Qed.
Lemma gf_b2z_lor1l : forall b, Z.lor 1 (Z.b2z b) = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "p'0h01bi001bp;1p;2p;3g00;1j14Tg00^Zj13Tg00_7j20Tg003ij31Tg00=Fj22Tg0095R0P0g00I_R0g008P#4R1f0R2#3'0;11P21201R1P1n0110000020000W0o"). Qed.
Lemma gf_land31_32q3 : forall q c d, 0 <= q -> 0 <= c + d -> Z.land (32 * q + c + d) 31 = (c + d) mod 32.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_ropl_gfast ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h61Ch71Qh81ch91dh:1qh;1zp;2p;1p;3p;4p;6p;7p;8g00;lj20Tg000Pj12Tg00;1j19Tg00;Oj2QTg0015j13Tg00F;j2FTg00<fj2ATg003ij36Tg00=`j1>Tg0000j1=Tg00M2j24Tg00>^j1;Tg00?<j1PTg00?gj2OTg00MPj2:Tg00@Jj48Tg00N3j1LTg00AYj2ETg00=Fj2BTg00B;j2@Tg00Bgj3CTg00CFj4DTg00>@j1?Tg00RKj4GTg00Rij3HTg00O9j4ITg00_Tj3JTg00Paj6KTg00:Uj2<Tg00G<j7MTg00NUj8NTg00J=R0f0R1'<p=1f1R2g00G`R3g00H?R4P4g00H_R5P1g00I?FMp=5f3R6P3P4P4P5f2R3P2P1GNp=7g00I_R7%131032#1P7g008PR8#2R9#2#2#2#2#9R:f4R;'QR<1063R='0%38#3#3#3#9,F110;6/A:567X;7P;P=g00J[R=#>R:%==R=1472%;7R>%P7R?P71O70R@g00LKRA1:78R8C8,5?RB%L4R4PBC71E?5R5P1P3g0095RBg009URC'B1@13=6BCdAC702CDR0b2b3b4X07%11%12[^07P1f5P3O2b1P:P=P71473P2%?7CGP>P?P7P@PA1:799H78C8,5?R?P4P?C7P5P0b2b3b4X07X571012#11023#1[^07^57P1P6P;P2O3b1CI10<6/03AJ<63EKW6W7X97X87W:o"). Qed.
Ltac wnorm1 := first [
    match goal with |- context [Z.land ((bv_signed (Z_to_bv 64 ?x) / 9223372036854775808) mod 18446744073709551616) (?x mod 18446744073709551616)] =>
      rewrite (clip_minneg x) by lia end
  | match goal with |- context [Z.land ((Z.shiftr (bv_signed (Z_to_bv 64 ?x)) 63) mod 18446744073709551616) (?x mod 18446744073709551616)] =>
      rewrite (clip_minneg_s x) by lia end
  | progress rewrite ?Z_to_bv_mod64l
  | progress rewrite ?gf_sw_m64_l, ?gf_sw_m64_ls, ?gf_sw_m64_r, ?gf_sw_m64_rs
  | match goal with |- context [bv_swrap 32 ?z] => wguard z; rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); lia) end
  | match goal with |- context [bv_wrap 32 ?z] => wguard z; rewrite (bv_wrap_small 32 z) by (change (bv_modulus 32) with (2^32); lia) end
  | match goal with |- context [?x mod 18446744073709551616] => wguard x; rewrite (Z.mod_small x 18446744073709551616) by lia end
  | match goal with |- context [Z.land (32 * ?q + ?c) 31] => rewrite (gf_land31_32q q c) by lia end
  | match goal with |- context [Z.land (32 * ?q) 31] => rewrite (gf_land31_32q0 q) by lia end
  | match goal with |- context [Z.land (32 * ?q + ?c + ?d) 31] => rewrite (gf_land31_32q3 q c d) by lia end
  | progress rewrite ?gf_div32_32q, ?gf_div32_32q0 ].
Ltac wnorm := repeat wnorm1.
Ltac is_store := next_instr ltac:(fun i => lazymatch i with Store _ _ _ _ => idtac end).
Ltac xcond5 := first [ reflexivity | wnorm; po_fix; gnorm; first [reflexivity | cnorm; solve_cond_rec ] | try guard_fix; first [ reflexivity | cnorm; solve_cond_rec ] ].
Ltac xbrT5 := apply evt_if_t; [ xcond5 | ].
Ltac xbrF5 := apply evt_if_f; [ xcond5 | ].
Ltac tbr5 := lazymatch goal with |- evt ?segs _ (MS _ _ (if ?c then Z_to_bv 64 ?T else Z_to_bv 64 ?E) _ _ _ _) =>
  first [ is_trapj segs T; xbrF5 | is_trapj segs E; xbrT5 | br | progress guard_fix; try br ] end.
Ltac instr_rd i k := lazymatch i with
  | Op _ ?rd _ _ => k rd | OpImm _ ?rd _ _ => k rd | ShiftImm _ ?rd _ _ => k rd | OpImm32 ?rd _ _ => k rd
  | ShiftImm32 _ ?rd _ _ => k rd | Op32 _ ?rd _ _ => k rd | Mul _ ?rd _ _ => k rd | Mul32 _ ?rd _ _ => k rd
  | Lui ?rd _ => k rd | Auipc ?rd _ => k rd | _ => idtac end.
Ltac has_wrap e := lazymatch e with context [bv_swrap _ _] => idtac | context [bv_wrap _ _] => idtac | context [_ mod 18446744073709551616] => idtac end.
Ltac wnorm_rd rd := reg_val rd ltac:(fun v => lazymatch v with Z_to_bv 64 ?e => first [ has_wrap e; wnorm | idtac ] | _ => idtac end).
Ltac gwalk1_v6 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => gnorm; first [ shbr | shbr0 | shbr_inv | shbr_x3 | tbr5 ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => (try (is_load; gnorm)); (try (is_store; wnorm));
      next_instr ltac:(fun i =>
      first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ];
      instr_rd i ltac:(fun rd => wnorm_rd rd))
  end.
(* [comment removed for export] *)
Ltac maskrow_k k base :=
  let MI := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch goal with H : mem_inv asegs mm |- _ => H end end in
  let bs := fresh "rowbs" in let L := fresh "RBL" in let ROW := fresh "ROW" in
  lazymatch base with
  | 240448 => destruct (mask_row _ 240448 k MI (or_introl eq_refl) ltac:(lia)) as (bs & L & ROW)
  | 240256 => destruct (mask_row _ 240256 k MI (or_intror eq_refl) ltac:(lia)) as (bs & L & ROW)
  end.
Ltac maskrow_sym := next_instr ltac:(fun i => lazymatch i with
  | Load SZ4 _ _ ?rs _ => reg_val rs ltac:(fun v => lazymatch v with
      | Z_to_bv 64 (?k * 4 + ?base) => maskrow_k k base
      | Z_to_bv 64 (?base + ?k * 4) => replace (Z_to_bv 64 (base + k * 4)) with (Z_to_bv 64 (k * 4 + base)) by (f_equal; lia); maskrow_k k base
      end) end).
(* [comment removed for export] *)
Ltac shfix6 := match goal with
  | |- context [Z_to_bv 64 (?c + SHB)] => lazymatch isZcst c with true => let x := eval vm_compute in (c * 8) in change (c + SHB) with (x / 8 + SHB) end
  | |- context [Z_to_bv 64 (SHB + ?c)] => lazymatch isZcst c with true => let x := eval vm_compute in (c * 8) in change (SHB + c) with (x / 8 + SHB) end
  end.
Ltac pwalk_step6 stops := first [ at_stop stops; fail 1 | gwalk1 | shfix6 | maskrow_sym ].
Ltac pw6 stops := repeat (pwalk_step6 stops).
Ltac pw6t stops := repeat (show_pc; time (pwalk_step6 stops)).
(* [comment removed for export] *)
Ltac xfork6 H := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => destruct c eqn:H end.
(* [comment removed for export] *)
Ltac cmpfix6 := repeat match goal with
  | |- context [?a <? ?b] => first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia) ]
  | |- context [?a <=? ?b] => first [ replace (a <=? b) with true by (symmetry; apply Z.leb_le; lia) | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; lia) ]
  | |- context [?a =? ?b] => first [ replace (a =? b) with true by (symmetry; apply Z.eqb_eq; lia) | replace (a =? b) with false by (symmetry; apply Z.eqb_neq; lia) ]
  end; change (Z.b2z true) with 1; change (Z.b2z false) with 0.
Ltac xcond6 := first [ reflexivity | rewrite ?Z.lor_0_r, ?Z.lor_0_l; wnorm; po_fix; cmpfix6; gnorm; first [reflexivity | cnorm; solve_cond_rec ] | try guard_fix; first [ reflexivity | cnorm; solve_cond_rec ] ].
Ltac xbrT6 := apply evt_if_t; [ xcond6 | ].
Ltac xbrF6 := apply evt_if_f; [ xcond6 | ].
Ltac tbr6 := lazymatch goal with |- evt ?segs _ (MS _ _ (if ?c then Z_to_bv 64 ?T else Z_to_bv 64 ?E) _ _ _ _) =>
  first [ is_trapj segs T; xbrF5 | is_trapj segs E; xbrT5 | xbrT6 | xbrF6 | br | progress guard_fix; br ] end.
Ltac gwalk1_v7 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => gnorm; first [ shbr | shbr0 | shbr_inv | shbr_x3 | tbr6 ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => (try (is_load; gnorm)); (try (is_store; wnorm));
      next_instr ltac:(fun i =>
      first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ];
      instr_rd i ltac:(fun rd => wnorm_rd rd))
  end.
(* [comment removed for export] *)
Ltac xcond8 := first [ reflexivity | rewrite ?Z.lor_0_r, ?Z.lor_0_l, ?gf_b2z_lor1, ?gf_b2z_lor1l; wnorm; po_fix; cmpfix6; gnorm; first [reflexivity | cnorm; solve_cond_rec ] | try guard_fix; first [ reflexivity | cnorm; solve_cond_rec ] ].
Ltac xbrT8 := apply evt_if_t; [ xcond8 | ].
Ltac xbrF8 := apply evt_if_f; [ xcond8 | ].
Ltac land3_all := repeat match goal with H : context [Z.land (32 * ?q + ?c + ?d) 31] |- _ => rewrite (gf_land31_32q3 q c d) in H by lia end.
