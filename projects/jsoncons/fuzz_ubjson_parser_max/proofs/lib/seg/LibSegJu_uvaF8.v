(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ju0PlanKit Ju0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Ju_936495.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ju_936495.ITR.
Definition IT : itab := SegItab_Ju_936495.IT.
Definition ENDS : list Z := ltac:(SegCodec.D ",2#37978#37:40"%pstring).
Definition STOPS1 : list Z := [227704; 227904] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-60$3$4#2-41#>?#?0#90$21$;+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3$17$18$19$1:$1;#>0#:0#>=#9?"%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",13'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??"%pstring).
Definition ss0 : sym_state := SS 227556 regs0 [] kn0 NX0.
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
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5;#378?4,20#$1+$2-60$3$4#2-41#>?#?0#90$21],,1$24+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3$17$18$19$1:$1;#>0#:0#>=#9?,,13'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.
Definition ex3 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5=#37978,20#$1+$2-60$3$4#2-41#>?#?0#90$21],,1$24+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3$17$18$19$1:$1;#>0#:0#>=#9?,,14'&3],,1$24##1#1'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).
Definition ex4 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5;#37904,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#1+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$25$18$19$1:$1;#>0#:0#>=#9?,,14'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s4 : sym_state := snd (snd ex4).
Definition arms5 := Eval vm_compute in (match SGP.branch_probe IT s4 with Some e => SGP.case_arms s4 e 0 | None => None end).
Definition f5 : sym_state := match arms5 with Some (Some s, _) => s | _ => s4 end.
Definition t5 : sym_state := match arms5 with Some (_, Some s) => s | _ => s4 end.
Definition ex6 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5=#37978,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#1+$21#1+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$25$18$19$1:$1;#>0#:0#>=#9?,,15'&3],,1$25##1#1'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s6 : sym_state := snd (snd ex6).
Definition ex7 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5;#37914,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#2+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$26$18$19$1:$1;#>0#:0#>=#9?,,15'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).
Definition arms8 := Eval vm_compute in (match SGP.branch_probe IT s7 with Some e => SGP.case_arms s7 e 0 | None => None end).
Definition f8 : sym_state := match arms8 with Some (Some s, _) => s | _ => s7 end.
Definition t8 : sym_state := match arms8 with Some (_, Some s) => s | _ => s7 end.
Definition ex9 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5=#37978,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#2+$21#2+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$26$18$19$1:$1;#>0#:0#>=#9?,,16'&3],,1$26##1#1'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).
Definition ex10 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5;#37924,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#3+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$27$18$19$1:$1;#>0#:0#>=#9?,,16'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s10 : sym_state := snd (snd ex10).
Definition arms11 := Eval vm_compute in (match SGP.branch_probe IT s10 with Some e => SGP.case_arms s10 e 0 | None => None end).
Definition f11 : sym_state := match arms11 with Some (Some s, _) => s | _ => s10 end.
Definition t11 : sym_state := match arms11 with Some (_, Some s) => s | _ => s10 end.
Definition ex12 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5=#37978,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#3+$21#3+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$27$18$19$1:$1;#>0#:0#>=#9?,,17'&3],,1$27##1#1'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s12 : sym_state := snd (snd ex12).
Definition ex13 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5;#37934,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#4+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$28$18$19$1:$1;#>0#:0#>=#9?,,17'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s13 : sym_state := snd (snd ex13).
Definition arms14 := Eval vm_compute in (match SGP.branch_probe IT s13 with Some e => SGP.case_arms s13 e 0 | None => None end).
Definition f14 : sym_state := match arms14 with Some (Some s, _) => s | _ => s13 end.
Definition t14 : sym_state := match arms14 with Some (_, Some s) => s | _ => s13 end.
Definition ex15 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5=#37978,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#4+$21#4+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$28$18$19$1:$1;#>0#:0#>=#9?,,18'&3],,1$28##1#1'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s15 : sym_state := snd (snd ex15).
Definition ex16 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5;#37944,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#5+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$29$18$19$1:$1;#>0#:0#>=#9?,,18'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s16 : sym_state := snd (snd ex16).
Definition arms17 := Eval vm_compute in (match SGP.branch_probe IT s16 with Some e => SGP.case_arms s16 e 0 | None => None end).
Definition f17 : sym_state := match arms17 with Some (Some s, _) => s | _ => s16 end.
Definition t17 : sym_state := match arms17 with Some (_, Some s) => s | _ => s16 end.
Definition ex18 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5=#37978,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#5+$21#5+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$29$18$19$1:$1;#>0#:0#>=#9?,,19'&3],,1$29##1#1'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).
Definition ex19 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5;#37954,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#6+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$2:$18$19$1:$1;#>0#:0#>=#9?,,19'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s19 : sym_state := snd (snd ex19).
Definition arms20 := Eval vm_compute in (match SGP.branch_probe IT s19 with Some e => SGP.case_arms s19 e 0 | None => None end).
Definition f20 : sym_state := match arms20 with Some (Some s, _) => s | _ => s19 end.
Definition t20 : sym_state := match arms20 with Some (_, Some s) => s | _ => s19 end.
Definition ex21 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5=#37978,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#6+$21#6+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$2:$18$19$1:$1;#>0#:0#>=#9?,,1:'&3],,1$2:##1#1'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).
Definition ex22 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5;#37964,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#7+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$2;$18$19$1:$1;#>0#:0#>=#9?,,1:'&3],,1$2:###'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s22 : sym_state := snd (snd ex22).
Definition arms23 := Eval vm_compute in (match SGP.branch_probe IT s22 with Some e => SGP.case_arms s22 e 0 | None => None end).
Definition f23 : sym_state := match arms23 with Some (Some s, _) => s | _ => s22 end.
Definition t23 : sym_state := match arms23 with Some (_, Some s) => s | _ => s22 end.
Definition ex24 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5=#37978,20#$1+$2-60$3$4#2-41#>?#?0#90+$21#7+$21#7+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3],,1$2;$18$19$1:$1;#>0#:0#>=#9?,,1;'&3],,1$2;##1#1'&3],,1$2:###'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s24 : sym_state := snd (snd ex24).
Definition ex25 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#37978#37:40#37978#37:40#5=#37:40,20#$1+$2-60$3$4#2-41#>?#?0#90$21+$21#7+$21$23#8-1#1-3>#?5#?4#8?#138<1^#?#??????????><73>#3+$21#8$18$19$1:$1;#>0#:0#>=#9?,,1;'&3],,1$2;###'&3],,1$2:###'&3],,1$29###'&3],,1$28###'&3],,1$27###'&3],,1$26###'&3],,1$25###'&3],,1$24###'$21#1#800000000000'$23#8#4000000'+$21$23#1#800000000000!$21#,1$24'$24##??!$21#1,1$25'$25##??!$21#2,1$26'$26##??!$21#3,1$27'$27##??!$21#4,1$28'$28##??!$21#5,1$29'$29##??!$21#6,1$2:'$2:##??!$21#7,1$2;'$2;##??,3<!"%pstring).
Definition s25 : sym_state := snd (snd ex25).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PEnd 0)) (SGA.mkplan (fst ex4) (SGP.PBranch (SGA.mkplan (fst ex6) (SGP.PEnd 1)) (SGA.mkplan (fst ex7) (SGP.PBranch (SGA.mkplan (fst ex9) (SGP.PEnd 2)) (SGA.mkplan (fst ex10) (SGP.PBranch (SGA.mkplan (fst ex12) (SGP.PEnd 3)) (SGA.mkplan (fst ex13) (SGP.PBranch (SGA.mkplan (fst ex15) (SGP.PEnd 4)) (SGA.mkplan (fst ex16) (SGP.PBranch (SGA.mkplan (fst ex18) (SGP.PEnd 5)) (SGA.mkplan (fst ex19) (SGP.PBranch (SGA.mkplan (fst ex21) (SGP.PEnd 6)) (SGA.mkplan (fst ex22) (SGP.PBranch (SGA.mkplan (fst ex24) (SGP.PEnd 7)) (SGA.mkplan (fst ex25) (SGP.PEnd 8))))))))))))))))).
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
Definition ps0 : SR.post_spec := SegFn.ps_f 227704 regs_out0 F0L cells0.
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s6).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s6).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s6 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s6 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s6).
Definition ps1 : SR.post_spec := SegFn.ps_f 227704 regs_out1 F0L cells1.
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s9).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s9).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s9 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s9 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s9).
Definition ps2 : SR.post_spec := SegFn.ps_f 227704 regs_out2 F0L cells2.
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s12).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s12).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s12 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s12 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s12).
Definition ps3 : SR.post_spec := SegFn.ps_f 227704 regs_out3 F0L cells3.
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s15).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s15).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s15 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s15 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s15).
Definition ps4 : SR.post_spec := SegFn.ps_f 227704 regs_out4 F0L cells4.
Definition regs_out5 : list expr := Eval vm_compute in (s_regs s18).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s18).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s18 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s18 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s18).
Definition ps5 : SR.post_spec := SegFn.ps_f 227704 regs_out5 F0L cells5.
Definition regs_out6 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s21).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s21).
Definition ps6 : SR.post_spec := SegFn.ps_f 227704 regs_out6 F0L cells6.
Definition regs_out7 : list expr := Eval vm_compute in (s_regs s24).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s24).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s24 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s24 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s24).
Definition ps7 : SR.post_spec := SegFn.ps_f 227704 regs_out7 F0L cells7.
Definition regs_out8 : list expr := Eval vm_compute in (s_regs s25).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s25).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s25 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s25 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s25).
Definition ps8 : SR.post_spec := SegFn.ps_f 227904 regs_out8 F0L cells8.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Ju_936495.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 227556 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := ub0_plan_sound_it SegItab_Ju_936495.IT SegItab_Ju_936495.IT_sound BF NX0 BR XSTEP F0 PSS plan 227556 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
