(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Js0PlanKit Js0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Js_e21467.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Js_e21467.ITR.
Definition IT : itab := SegItab_Js_e21467.IT.
Definition ENDS : list Z := ltac:(SegCodec.D ",2#36<9<#36<<4"%pstring).
Definition STOPS1 : list Z := [224412; 224452] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21$;+$21$23#8#1-3>#?5-41#2#1388=#3$24$16$25#3$19$1:$1;#>=#9?#?0#90"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",:'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??"%pstring).
Definition ss0 : sym_state := SS 224252 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [].
Definition F0L : list SR.region := [].
Definition BF : nat := Nat.mul 10 100.
Definition BR : list SGP.bfact := [].
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<38,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21],,1$29+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#3$1;#>=#9?#?0#90,,:'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.
Definition ex3 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#2+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#3$1;#>=#9?#?0#90,,;'&3-41],,1$29#1#1'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).
Definition ex4 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<40,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21],,1$28+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#3$1;#>=#9?#?0#90,,;'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).
Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.
Definition ex6 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#2+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#3$1;#>=#9?#?0#90,,<'&3-41],,1$28#1#1'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).
Definition ex7 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<4<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21],,1$27+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,<'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).
Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.
Definition ex9 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#2+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,='&3-41],,1$27#1#1'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).
Definition ex10 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<54,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,='&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).
Definition arms11 := Eval vm_compute in (match SGP.branch_probe IT s10 with Some e => SGP.case_arms s10 e 0 | None => None end).
Definition f11 : sym_state := match arms11 with Some (Some s, _) => s | _ => s10 end.
Definition t11 : sym_state := match arms11 with Some (_, Some s) => s | _ => s10 end.
Definition ex12 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<68,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,>'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).
Definition arms13 := Eval vm_compute in (match SGP.branch_probe IT s12 with Some e => SGP.case_arms s12 e 0 | None => None end).
Definition f13 : sym_state := match arms13 with Some (Some s, _) => s | _ => s12 end.
Definition t13 : sym_state := match arms13 with Some (_, Some s) => s | _ => s12 end.
Definition ex14 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<98,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,?'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).
Definition arms15 := Eval vm_compute in (match SGP.branch_probe IT s14 with Some e => SGP.case_arms s14 e 0 | None => None end).
Definition f15 : sym_state := match arms15 with Some (Some s, _) => s | _ => s14 end.
Definition t15 : sym_state := match arms15 with Some (_, Some s) => s | _ => s14 end.
Definition ex16 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&9],,1$27#??#90#1#1'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).
Definition ex17 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<9<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&9],,1$27#??#90##'&4&1$25#?0#1#1#1'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s17 : sym_state := snd (snd ex17).
Definition ex18 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<6<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,?'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).
Definition arms19 := Eval vm_compute in (match SGP.branch_probe IT s18 with Some e => SGP.case_arms s18 e 0 | None => None end).
Definition f19 : sym_state := match arms19 with Some (Some s, _) => s | _ => s18 end.
Definition t19 : sym_state := match arms19 with Some (_, Some s) => s | _ => s18 end.
Definition ex20 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<70,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).
Definition arms21 := Eval vm_compute in (match SGP.branch_probe IT s20 with Some e => SGP.case_arms s20 e 0 | None => None end).
Definition f21 : sym_state := match arms21 with Some (Some s, _) => s | _ => s20 end.
Definition t21 : sym_state := match arms21 with Some (_, Some s) => s | _ => s20 end.
Definition ex22 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&4#8?&9],,1$27#??#1#1'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s22 : sym_state := snd (snd ex22).
Definition ex23 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<9<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&4#8?&9],,1$27#??##'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s23 : sym_state := snd (snd ex23).
Definition ex24 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<84,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s24 : sym_state := snd (snd ex24).
Definition arms25 := Eval vm_compute in (match SGP.branch_probe IT s24 with Some e => SGP.case_arms s24 e 0 | None => None end).
Definition f25 : sym_state := match arms25 with Some (Some s, _) => s | _ => s24 end.
Definition t25 : sym_state := match arms25 with Some (_, Some s) => s | _ => s24 end.
Definition ex26 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s26 : sym_state := snd (snd ex26).
Definition ex27 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<88,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s27 : sym_state := snd (snd ex27).
Definition arms28 := Eval vm_compute in (match SGP.branch_probe IT s27 with Some e => SGP.case_arms s27 e 0 | None => None end).
Definition f28 : sym_state := match arms28 with Some (Some s, _) => s | _ => s27 end.
Definition t28 : sym_state := match arms28 with Some (_, Some s) => s | _ => s27 end.
Definition ex29 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<9<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,12'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s29 : sym_state := snd (snd ex29).
Definition ex30 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,12'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s30 : sym_state := snd (snd ex30).
Definition ex31 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<58,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,>'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s31 : sym_state := snd (snd ex31).
Definition arms32 := Eval vm_compute in (match SGP.branch_probe IT s31 with Some e => SGP.case_arms s31 e 0 | None => None end).
Definition f32 : sym_state := match arms32 with Some (Some s, _) => s | _ => s31 end.
Definition t32 : sym_state := match arms32 with Some (_, Some s) => s | _ => s31 end.
Definition ex33 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<90,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,?'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s33 : sym_state := snd (snd ex33).
Definition arms34 := Eval vm_compute in (match SGP.branch_probe IT s33 with Some e => SGP.case_arms s33 e 0 | None => None end).
Definition f34 : sym_state := match arms34 with Some (Some s, _) => s | _ => s33 end.
Definition t34 : sym_state := match arms34 with Some (_, Some s) => s | _ => s33 end.
Definition ex35 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&9],,1$27#??#:0#1#1'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s35 : sym_state := snd (snd ex35).
Definition ex36 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<9<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&9],,1$27#??#:0##'&4&1$25#>0#1#1#1'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s36 : sym_state := snd (snd ex36).
Definition ex37 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<5<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,?'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s37 : sym_state := snd (snd ex37).
Definition arms38 := Eval vm_compute in (match SGP.branch_probe IT s37 with Some e => SGP.case_arms s37 e 0 | None => None end).
Definition f38 : sym_state := match arms38 with Some (Some s, _) => s | _ => s37 end.
Definition t38 : sym_state := match arms38 with Some (_, Some s) => s | _ => s37 end.
Definition ex39 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<60,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s39 : sym_state := snd (snd ex39).
Definition arms40 := Eval vm_compute in (match SGP.branch_probe IT s39 with Some e => SGP.case_arms s39 e 0 | None => None end).
Definition f40 : sym_state := match arms40 with Some (Some s, _) => s | _ => s39 end.
Definition t40 : sym_state := match arms40 with Some (_, Some s) => s | _ => s39 end.
Definition ex41 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&4#9?&9],,1$27#??#1#1'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s41 : sym_state := snd (snd ex41).
Definition ex42 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<9<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21&9],,1$27#??+$21$23#8#1-3>#?5-41#2#1388=#3$24+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&4#9?&9],,1$27#??##'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s42 : sym_state := snd (snd ex42).
Definition ex43 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<84,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,10'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s43 : sym_state := snd (snd ex43).
Definition arms44 := Eval vm_compute in (match SGP.branch_probe IT s43 with Some e => SGP.case_arms s43 e 0 | None => None end).
Definition f44 : sym_state := match arms44 with Some (Some s, _) => s | _ => s43 end.
Definition t44 : sym_state := match arms44 with Some (_, Some s) => s | _ => s43 end.
Definition ex45 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&3&7@#100000000000000$24#38-3>#1#1'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s45 : sym_state := snd (snd ex45).
Definition ex46 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5;#36<88,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,11'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s46 : sym_state := snd (snd ex46).
Definition arms47 := Eval vm_compute in (match SGP.branch_probe IT s46 with Some e => SGP.case_arms s46 e 0 | None => None end).
Definition f47 : sym_state := match arms47 with Some (Some s, _) => s | _ => s46 end.
Definition t47 : sym_state := match arms47 with Some (_, Some s) => s | _ => s46 end.
Definition ex48 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<9<,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,12'&4$25#?5#1#1'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s48 : sym_state := snd (snd ex48).
Definition ex49 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#36<9<#36<<4#36<9<#36<<4#5=#36<<4,20#$1+$2-60$3$4#>?#>0#:0#?4#8?$21#6+$21$23#8#1-3>#?5-41#2#1388=#3&7@#100000000000000$24#38+$21#4$25#3+$21#3+$21#2$1;#>=#9?#?0#90,,12'&4$25#?5##'&3&7@#100000000000000$24#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'&3-41],,1$27##'&3-41],,1$28##'&3-41],,1$29##'$21##800000000000'$23#4#4000000'+$21$23#1#800000000000!$21#1,1$27'$27##??!$21#2,1$28'$28##??!$21#3,1$29'$29##??'$25##??,3<!"%pstring).
Definition s49 : sym_state := snd (snd ex49).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 2)) (SGA.mkplan (fst ex10) (SGP.PBranch (SGA.mkplan (fst ex12) (SGP.PBranch (SGA.mkplan (fst ex14) (SGP.PBranch (SGA.mkplan (fst ex16) (SGP.PEnd 3)) (SGA.mkplan (fst ex17) (SGP.PEnd 4)))) (SGA.mkplan (fst ex18) (SGP.PBranch (SGA.mkplan (fst ex20) (SGP.PBranch (SGA.mkplan (fst ex22) (SGP.PEnd 5)) (SGA.mkplan (fst ex23) (SGP.PEnd 6)))) (SGA.mkplan (fst ex24) (SGP.PBranch (SGA.mkplan (fst ex26) (SGP.PEnd 7)) (SGA.mkplan (fst ex27) (SGP.PBranch (SGA.mkplan (fst ex29) (SGP.PEnd 8)) (SGA.mkplan (fst ex30) (SGP.PEnd 9)))))))))) (SGA.mkplan (fst ex31) (SGP.PBranch (SGA.mkplan (fst ex33) (SGP.PBranch (SGA.mkplan (fst ex35) (SGP.PEnd 10)) (SGA.mkplan (fst ex36) (SGP.PEnd 11)))) (SGA.mkplan (fst ex37) (SGP.PBranch (SGA.mkplan (fst ex39) (SGP.PBranch (SGA.mkplan (fst ex41) (SGP.PEnd 12)) (SGA.mkplan (fst ex42) (SGP.PEnd 13)))) (SGA.mkplan (fst ex43) (SGP.PBranch (SGA.mkplan (fst ex45) (SGP.PEnd 14)) (SGA.mkplan (fst ex46) (SGP.PBranch (SGA.mkplan (fst ex48) (SGP.PEnd 15)) (SGA.mkplan (fst ex49) (SGP.PEnd 16))))))))))))))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool := SegFn.in_foot_f F0L b k w.
Definition in_kn0 (K : kentry) : bool := SegFn.in_kn_f kn0 K.
Definition SPV : nat := 2%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := SegFn.live_f SPV spoff b k.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry := SegFn.cells_of_f live in_foot in_kn0 sF spoff.
Definition spoff_of (sF : sym_state) : Z := SegFn.spoff_of_f SPV sF.
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s3).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s3).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s3 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s3 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s3).
Definition ps0 : SR.post_spec := SegFn.ps_f 224452 regs_out0 F0L cells0.
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SegFn.ps_f 224452 regs_out1 F0L cells1.
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s9).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s9).
Definition ps2 : SR.post_spec := SegFn.ps_f 224452 regs_out2 F0L cells2.
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s16).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s16).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s16 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s16 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s16).
Definition ps3 : SR.post_spec := SegFn.ps_f 224452 regs_out3 F0L cells3.
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s17).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s17).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s17 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s17 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s17).
Definition ps4 : SR.post_spec := SegFn.ps_f 224412 regs_out4 F0L cells4.
Definition regs_out5 : list expr := Eval vm_compute in (s_regs s22).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s22).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s22 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s22 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s22).
Definition ps5 : SR.post_spec := SegFn.ps_f 224452 regs_out5 F0L cells5.
Definition regs_out6 : list expr := Eval vm_compute in (s_regs s23).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s23).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s23 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s23 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s23).
Definition ps6 : SR.post_spec := SegFn.ps_f 224412 regs_out6 F0L cells6.
Definition regs_out7 : list expr := Eval vm_compute in (s_regs s26).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s26).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s26 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s26 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s26).
Definition ps7 : SR.post_spec := SegFn.ps_f 224452 regs_out7 F0L cells7.
Definition regs_out8 : list expr := Eval vm_compute in (s_regs s29).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s29).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s29 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s29 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s29).
Definition ps8 : SR.post_spec := SegFn.ps_f 224412 regs_out8 F0L cells8.
Definition regs_out9 : list expr := Eval vm_compute in (s_regs s30).
Definition exit_sp_off9 : Z := Eval vm_compute in (spoff_of s30).
Definition cells9 : list kentry := Eval vm_compute in (cells_of s30 exit_sp_off9).
Definition nfresh9 : nat := Eval vm_compute in (s_next s30 - NX0)%nat.
Definition exit_pc9 : Z := Eval vm_compute in (s_pc s30).
Definition ps9 : SR.post_spec := SegFn.ps_f 224452 regs_out9 F0L cells9.
Definition regs_out10 : list expr := Eval vm_compute in (s_regs s35).
Definition exit_sp_off10 : Z := Eval vm_compute in (spoff_of s35).
Definition cells10 : list kentry := Eval vm_compute in (cells_of s35 exit_sp_off10).
Definition nfresh10 : nat := Eval vm_compute in (s_next s35 - NX0)%nat.
Definition exit_pc10 : Z := Eval vm_compute in (s_pc s35).
Definition ps10 : SR.post_spec := SegFn.ps_f 224452 regs_out10 F0L cells10.
Definition regs_out11 : list expr := Eval vm_compute in (s_regs s36).
Definition exit_sp_off11 : Z := Eval vm_compute in (spoff_of s36).
Definition cells11 : list kentry := Eval vm_compute in (cells_of s36 exit_sp_off11).
Definition nfresh11 : nat := Eval vm_compute in (s_next s36 - NX0)%nat.
Definition exit_pc11 : Z := Eval vm_compute in (s_pc s36).
Definition ps11 : SR.post_spec := SegFn.ps_f 224412 regs_out11 F0L cells11.
Definition regs_out12 : list expr := Eval vm_compute in (s_regs s41).
Definition exit_sp_off12 : Z := Eval vm_compute in (spoff_of s41).
Definition cells12 : list kentry := Eval vm_compute in (cells_of s41 exit_sp_off12).
Definition nfresh12 : nat := Eval vm_compute in (s_next s41 - NX0)%nat.
Definition exit_pc12 : Z := Eval vm_compute in (s_pc s41).
Definition ps12 : SR.post_spec := SegFn.ps_f 224452 regs_out12 F0L cells12.
Definition regs_out13 : list expr := Eval vm_compute in (s_regs s42).
Definition exit_sp_off13 : Z := Eval vm_compute in (spoff_of s42).
Definition cells13 : list kentry := Eval vm_compute in (cells_of s42 exit_sp_off13).
Definition nfresh13 : nat := Eval vm_compute in (s_next s42 - NX0)%nat.
Definition exit_pc13 : Z := Eval vm_compute in (s_pc s42).
Definition ps13 : SR.post_spec := SegFn.ps_f 224412 regs_out13 F0L cells13.
Definition regs_out14 : list expr := Eval vm_compute in (s_regs s45).
Definition exit_sp_off14 : Z := Eval vm_compute in (spoff_of s45).
Definition cells14 : list kentry := Eval vm_compute in (cells_of s45 exit_sp_off14).
Definition nfresh14 : nat := Eval vm_compute in (s_next s45 - NX0)%nat.
Definition exit_pc14 : Z := Eval vm_compute in (s_pc s45).
Definition ps14 : SR.post_spec := SegFn.ps_f 224452 regs_out14 F0L cells14.
Definition regs_out15 : list expr := Eval vm_compute in (s_regs s48).
Definition exit_sp_off15 : Z := Eval vm_compute in (spoff_of s48).
Definition cells15 : list kentry := Eval vm_compute in (cells_of s48 exit_sp_off15).
Definition nfresh15 : nat := Eval vm_compute in (s_next s48 - NX0)%nat.
Definition exit_pc15 : Z := Eval vm_compute in (s_pc s48).
Definition ps15 : SR.post_spec := SegFn.ps_f 224412 regs_out15 F0L cells15.
Definition regs_out16 : list expr := Eval vm_compute in (s_regs s49).
Definition exit_sp_off16 : Z := Eval vm_compute in (spoff_of s49).
Definition cells16 : list kentry := Eval vm_compute in (cells_of s49 exit_sp_off16).
Definition nfresh16 : nat := Eval vm_compute in (s_next s49 - NX0)%nat.
Definition exit_pc16 : Z := Eval vm_compute in (s_pc s49).
Definition ps16 : SR.post_spec := SegFn.ps_f 224452 regs_out16 F0L cells16.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8; ps9; ps10; ps11; ps12; ps13; ps14; ps15; ps16] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Js_e21467.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 224252 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := src0_plan_sound_it SegItab_Js_e21467.IT SegItab_Js_e21467.IT_sound BF NX0 BR XSTEP F0 PSS plan 224252 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
