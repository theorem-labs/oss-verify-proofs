(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegBoil SegFn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegCodec. Import SegCodec.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Jb0PlanKit Jb0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require SegItab_Jb_ec8934.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require SegPlanFast.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Jb_ec8934.ITR.
Definition IT : itab := SegItab_Jb_ec8934.IT.
Definition ENDS : list Z := ltac:(SegCodec.D ",2#;14:8#;1574"%pstring).
Definition STOPS1 : list Z := [726184; 726388] ++ ENDS.
Definition NX0 : nat := 60.
Definition v0 (k : Z) : expr := SegFn.v0_f k.
Definition L : expr := ltac:(SegCodec.D "$4"%pstring).
Definition regs0 : list expr := ltac:(SegCodec.D ",20#$1+$2-70$3$4#?5#2-41#9?#?0$21$27$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>="%pstring).
Definition kn0 : list kentry := ltac:(SegCodec.D ",5'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000"%pstring).
Definition ss0 : sym_state := SS 726108 regs0 [] kn0 NX0.
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
Definition ex1 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;1460,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,5'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s1 : sym_state := snd (snd ex1).
Definition arms2 := Eval vm_compute in (match SGP.branch_probe IT s1 with Some e => SGP.case_arms s1 e 0 | None => None end).
Definition f2 : sym_state := match arms2 with Some (Some s, _) => s | _ => s1 end.
Definition t2 : sym_state := match arms2 with Some (_, Some s) => s | _ => s1 end.
Definition ex3 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;1474,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,6'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s3 : sym_state := snd (snd ex3).
Definition arms4 := Eval vm_compute in (match SGP.branch_probe IT s3 with Some e => SGP.case_arms s3 e 0 | None => None end).
Definition f4 : sym_state := match arms4 with Some (Some s, _) => s | _ => s3 end.
Definition t4 : sym_state := match arms4 with Some (_, Some s) => s | _ => s3 end.
Definition ex5 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;14:4,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,7'&4&1$25#?0#1#1#1'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s5 : sym_state := snd (snd ex5).
Definition arms6 := Eval vm_compute in (match SGP.branch_probe IT s5 with Some e => SGP.case_arms s5 e 0 | None => None end).
Definition f6 : sym_state := match arms6 with Some (Some s, _) => s | _ => s5 end.
Definition t6 : sym_state := match arms6 with Some (_, Some s) => s | _ => s5 end.
Definition ex7 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;1574,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,8'&4&9$27#??#90#1#1'&4&1$25#?0#1#1#1'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s7 : sym_state := snd (snd ex7).
Definition ex8 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;14:8,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,8'&4&9$27#??#90##'&4&1$25#?0#1#1#1'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s8 : sym_state := snd (snd ex8).
Definition ex9 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;1478,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,7'&4&1$25#?0#1##'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s9 : sym_state := snd (snd ex9).
Definition arms10 := Eval vm_compute in (match SGP.branch_probe IT s9 with Some e => SGP.case_arms s9 e 0 | None => None end).
Definition f10 : sym_state := match arms10 with Some (Some s, _) => s | _ => s9 end.
Definition t10 : sym_state := match arms10 with Some (_, Some s) => s | _ => s9 end.
Definition ex11 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;147<,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,8'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s11 : sym_state := snd (snd ex11).
Definition arms12 := Eval vm_compute in (match SGP.branch_probe IT s11 with Some e => SGP.case_arms s11 e 0 | None => None end).
Definition f12 : sym_state := match arms12 with Some (Some s, _) => s | _ => s11 end.
Definition t12 : sym_state := match arms12 with Some (_, Some s) => s | _ => s11 end.
Definition ex13 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;1574,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,9'&4#8?&9$27#??#1#1'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s13 : sym_state := snd (snd ex13).
Definition ex14 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;14:8,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,9'&4#8?&9$27#??##'&4&1$25#?4#1#1#1'&4&1$25#?0#1##'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s14 : sym_state := snd (snd ex14).
Definition ex15 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;1490,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,8'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s15 : sym_state := snd (snd ex15).
Definition arms16 := Eval vm_compute in (match SGP.branch_probe IT s15 with Some e => SGP.case_arms s15 e 0 | None => None end).
Definition f16 : sym_state := match arms16 with Some (Some s, _) => s | _ => s15 end.
Definition t16 : sym_state := match arms16 with Some (_, Some s) => s | _ => s15 end.
Definition ex17 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;1574,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,9'&3&7@#100000000000000$25#38-3>#1#1'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s17 : sym_state := snd (snd ex17).
Definition ex18 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;1494,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,9'&3&7@#100000000000000$25#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s18 : sym_state := snd (snd ex18).
Definition arms19 := Eval vm_compute in (match SGP.branch_probe IT s18 with Some e => SGP.case_arms s18 e 0 | None => None end).
Definition f19 : sym_state := match arms19 with Some (Some s, _) => s | _ => s18 end.
Definition t19 : sym_state := match arms19 with Some (_, Some s) => s | _ => s18 end.
Definition ex20 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;14:8,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,:'&4$25#?5#1#1'&3&7@#100000000000000$25#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s20 : sym_state := snd (snd ex20).
Definition ex21 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;1574,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,:'&4$25#?5##'&3&7@#100000000000000$25#38-3>##'&4&1$25#?4#1##'&4&1$25#?0#1##'&3#>?$25#1#1'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s21 : sym_state := snd (snd ex21).
Definition ex22 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;1464,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,6'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s22 : sym_state := snd (snd ex22).
Definition arms23 := Eval vm_compute in (match SGP.branch_probe IT s22 with Some e => SGP.case_arms s22 e 0 | None => None end).
Definition f23 : sym_state := match arms23 with Some (Some s, _) => s | _ => s22 end.
Definition t23 : sym_state := match arms23 with Some (_, Some s) => s | _ => s22 end.
Definition ex24 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;149<,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,7'&4&1$25#>0#1#1#1'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s24 : sym_state := snd (snd ex24).
Definition arms25 := Eval vm_compute in (match SGP.branch_probe IT s24 with Some e => SGP.case_arms s24 e 0 | None => None end).
Definition f25 : sym_state := match arms25 with Some (Some s, _) => s | _ => s24 end.
Definition t25 : sym_state := match arms25 with Some (_, Some s) => s | _ => s24 end.
Definition ex26 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;1574,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,8'&4&9$27#??#:0#1#1'&4&1$25#>0#1#1#1'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s26 : sym_state := snd (snd ex26).
Definition ex27 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;14:8,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,8'&4&9$27#??#:0##'&4&1$25#>0#1#1#1'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s27 : sym_state := snd (snd ex27).
Definition ex28 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;1468,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,7'&4&1$25#>0#1##'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s28 : sym_state := snd (snd ex28).
Definition arms29 := Eval vm_compute in (match SGP.branch_probe IT s28 with Some e => SGP.case_arms s28 e 0 | None => None end).
Definition f29 : sym_state := match arms29 with Some (Some s, _) => s | _ => s28 end.
Definition t29 : sym_state := match arms29 with Some (_, Some s) => s | _ => s28 end.
Definition ex30 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;146<,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,8'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s30 : sym_state := snd (snd ex30).
Definition arms31 := Eval vm_compute in (match SGP.branch_probe IT s30 with Some e => SGP.case_arms s30 e 0 | None => None end).
Definition f31 : sym_state := match arms31 with Some (Some s, _) => s | _ => s30 end.
Definition t31 : sym_state := match arms31 with Some (_, Some s) => s | _ => s30 end.
Definition ex32 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;1574,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,9'&4#9?&9$27#??#1#1'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s32 : sym_state := snd (snd ex32).
Definition ex33 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;14:8,20#$1+$2-70$3$4#?5#2-41#9?#?0$21&9$27#??$<+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,9'&4#9?&9$27#??##'&4&1$25#>=#1#1#1'&4&1$25#>0#1##'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s33 : sym_state := snd (snd ex33).
Definition ex34 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;1490,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,8'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s34 : sym_state := snd (snd ex34).
Definition arms35 := Eval vm_compute in (match SGP.branch_probe IT s34 with Some e => SGP.case_arms s34 e 0 | None => None end).
Definition f35 : sym_state := match arms35 with Some (Some s, _) => s | _ => s34 end.
Definition t35 : sym_state := match arms35 with Some (_, Some s) => s | _ => s34 end.
Definition ex36 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;1574,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,9'&3&7@#100000000000000$25#38-3>#1#1'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s36 : sym_state := snd (snd ex36).
Definition ex37 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5;#;1494,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,9'&3&7@#100000000000000$25#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s37 : sym_state := snd (snd ex37).
Definition arms38 := Eval vm_compute in (match SGP.branch_probe IT s37 with Some e => SGP.case_arms s37 e 0 | None => None end).
Definition f38 : sym_state := match arms38 with Some (Some s, _) => s | _ => s37 end.
Definition t38 : sym_state := match arms38 with Some (_, Some s) => s | _ => s37 end.
Definition ex39 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;14:8,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,:'&4$25#?5#1#1'&3&7@#100000000000000$25#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s39 : sym_state := snd (snd ex39).
Definition ex40 : list SGA.aitem * (Z * sym_state) := ltac:(SegCodec.D ",1!!,4#;14:8#;1574#;14:8#;1574#5=#;1574,20#$1+$2-70$3$4#?5#2-41#9?#?0$21#6&7@#100000000000000$25#38+$21$23#8-1#1-3>#2325=-2325>#7???8000#90#?4#8?#3$25$22$1;#>?#>0#:0#>=,,:'&4$25#?5##'&3&7@#100000000000000$25#38-3>##'&4&1$25#>=#1##'&4&1$25#>0#1##'&3#>?$25##'$21#1#800000000000'$23#1#4000000'+$21$23#1#800000000000'$25##??'$22##800000000000,3<!"%pstring).
Definition s40 : sym_state := snd (snd ex40).
Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PBranch (SGA.mkplan (fst ex3) (SGP.PBranch (SGA.mkplan (fst ex5) (SGP.PBranch (SGA.mkplan (fst ex7) (SGP.PEnd 0)) (SGA.mkplan (fst ex8) (SGP.PEnd 1)))) (SGA.mkplan (fst ex9) (SGP.PBranch (SGA.mkplan (fst ex11) (SGP.PBranch (SGA.mkplan (fst ex13) (SGP.PEnd 2)) (SGA.mkplan (fst ex14) (SGP.PEnd 3)))) (SGA.mkplan (fst ex15) (SGP.PBranch (SGA.mkplan (fst ex17) (SGP.PEnd 4)) (SGA.mkplan (fst ex18) (SGP.PBranch (SGA.mkplan (fst ex20) (SGP.PEnd 5)) (SGA.mkplan (fst ex21) (SGP.PEnd 6)))))))))) (SGA.mkplan (fst ex22) (SGP.PBranch (SGA.mkplan (fst ex24) (SGP.PBranch (SGA.mkplan (fst ex26) (SGP.PEnd 7)) (SGA.mkplan (fst ex27) (SGP.PEnd 8)))) (SGA.mkplan (fst ex28) (SGP.PBranch (SGA.mkplan (fst ex30) (SGP.PBranch (SGA.mkplan (fst ex32) (SGP.PEnd 9)) (SGA.mkplan (fst ex33) (SGP.PEnd 10)))) (SGA.mkplan (fst ex34) (SGP.PBranch (SGA.mkplan (fst ex36) (SGP.PEnd 11)) (SGA.mkplan (fst ex37) (SGP.PBranch (SGA.mkplan (fst ex39) (SGP.PEnd 12)) (SGA.mkplan (fst ex40) (SGP.PEnd 13))))))))))).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool := SegFn.in_foot_f F0L b k w.
Definition in_kn0 (K : kentry) : bool := SegFn.in_kn_f kn0 K.
Definition SPV : nat := 0%nat.
Definition live (spoff : Z) (b : expr) (k : Z) : bool := SegFn.live_f SPV spoff b k.
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry := SegFn.cells_of_f live in_foot in_kn0 sF spoff.
Definition spoff_of (sF : sym_state) : Z := SegFn.spoff_of_f SPV sF.
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s7).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s7).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s7 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s7 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s7).
Definition ps0 : SR.post_spec := SegFn.ps_f 726388 regs_out0 F0L cells0.
Definition regs_out1 : list expr := Eval vm_compute in (s_regs s8).
Definition exit_sp_off1 : Z := Eval vm_compute in (spoff_of s8).
Definition cells1 : list kentry := Eval vm_compute in (cells_of s8 exit_sp_off1).
Definition nfresh1 : nat := Eval vm_compute in (s_next s8 - NX0)%nat.
Definition exit_pc1 : Z := Eval vm_compute in (s_pc s8).
Definition ps1 : SR.post_spec := SegFn.ps_f 726184 regs_out1 F0L cells1.
Definition regs_out2 : list expr := Eval vm_compute in (s_regs s13).
Definition exit_sp_off2 : Z := Eval vm_compute in (spoff_of s13).
Definition cells2 : list kentry := Eval vm_compute in (cells_of s13 exit_sp_off2).
Definition nfresh2 : nat := Eval vm_compute in (s_next s13 - NX0)%nat.
Definition exit_pc2 : Z := Eval vm_compute in (s_pc s13).
Definition ps2 : SR.post_spec := SegFn.ps_f 726388 regs_out2 F0L cells2.
Definition regs_out3 : list expr := Eval vm_compute in (s_regs s14).
Definition exit_sp_off3 : Z := Eval vm_compute in (spoff_of s14).
Definition cells3 : list kentry := Eval vm_compute in (cells_of s14 exit_sp_off3).
Definition nfresh3 : nat := Eval vm_compute in (s_next s14 - NX0)%nat.
Definition exit_pc3 : Z := Eval vm_compute in (s_pc s14).
Definition ps3 : SR.post_spec := SegFn.ps_f 726184 regs_out3 F0L cells3.
Definition regs_out4 : list expr := Eval vm_compute in (s_regs s17).
Definition exit_sp_off4 : Z := Eval vm_compute in (spoff_of s17).
Definition cells4 : list kentry := Eval vm_compute in (cells_of s17 exit_sp_off4).
Definition nfresh4 : nat := Eval vm_compute in (s_next s17 - NX0)%nat.
Definition exit_pc4 : Z := Eval vm_compute in (s_pc s17).
Definition ps4 : SR.post_spec := SegFn.ps_f 726388 regs_out4 F0L cells4.
Definition regs_out5 : list expr := Eval vm_compute in (s_regs s20).
Definition exit_sp_off5 : Z := Eval vm_compute in (spoff_of s20).
Definition cells5 : list kentry := Eval vm_compute in (cells_of s20 exit_sp_off5).
Definition nfresh5 : nat := Eval vm_compute in (s_next s20 - NX0)%nat.
Definition exit_pc5 : Z := Eval vm_compute in (s_pc s20).
Definition ps5 : SR.post_spec := SegFn.ps_f 726184 regs_out5 F0L cells5.
Definition regs_out6 : list expr := Eval vm_compute in (s_regs s21).
Definition exit_sp_off6 : Z := Eval vm_compute in (spoff_of s21).
Definition cells6 : list kentry := Eval vm_compute in (cells_of s21 exit_sp_off6).
Definition nfresh6 : nat := Eval vm_compute in (s_next s21 - NX0)%nat.
Definition exit_pc6 : Z := Eval vm_compute in (s_pc s21).
Definition ps6 : SR.post_spec := SegFn.ps_f 726388 regs_out6 F0L cells6.
Definition regs_out7 : list expr := Eval vm_compute in (s_regs s26).
Definition exit_sp_off7 : Z := Eval vm_compute in (spoff_of s26).
Definition cells7 : list kentry := Eval vm_compute in (cells_of s26 exit_sp_off7).
Definition nfresh7 : nat := Eval vm_compute in (s_next s26 - NX0)%nat.
Definition exit_pc7 : Z := Eval vm_compute in (s_pc s26).
Definition ps7 : SR.post_spec := SegFn.ps_f 726388 regs_out7 F0L cells7.
Definition regs_out8 : list expr := Eval vm_compute in (s_regs s27).
Definition exit_sp_off8 : Z := Eval vm_compute in (spoff_of s27).
Definition cells8 : list kentry := Eval vm_compute in (cells_of s27 exit_sp_off8).
Definition nfresh8 : nat := Eval vm_compute in (s_next s27 - NX0)%nat.
Definition exit_pc8 : Z := Eval vm_compute in (s_pc s27).
Definition ps8 : SR.post_spec := SegFn.ps_f 726184 regs_out8 F0L cells8.
Definition regs_out9 : list expr := Eval vm_compute in (s_regs s32).
Definition exit_sp_off9 : Z := Eval vm_compute in (spoff_of s32).
Definition cells9 : list kentry := Eval vm_compute in (cells_of s32 exit_sp_off9).
Definition nfresh9 : nat := Eval vm_compute in (s_next s32 - NX0)%nat.
Definition exit_pc9 : Z := Eval vm_compute in (s_pc s32).
Definition ps9 : SR.post_spec := SegFn.ps_f 726388 regs_out9 F0L cells9.
Definition regs_out10 : list expr := Eval vm_compute in (s_regs s33).
Definition exit_sp_off10 : Z := Eval vm_compute in (spoff_of s33).
Definition cells10 : list kentry := Eval vm_compute in (cells_of s33 exit_sp_off10).
Definition nfresh10 : nat := Eval vm_compute in (s_next s33 - NX0)%nat.
Definition exit_pc10 : Z := Eval vm_compute in (s_pc s33).
Definition ps10 : SR.post_spec := SegFn.ps_f 726184 regs_out10 F0L cells10.
Definition regs_out11 : list expr := Eval vm_compute in (s_regs s36).
Definition exit_sp_off11 : Z := Eval vm_compute in (spoff_of s36).
Definition cells11 : list kentry := Eval vm_compute in (cells_of s36 exit_sp_off11).
Definition nfresh11 : nat := Eval vm_compute in (s_next s36 - NX0)%nat.
Definition exit_pc11 : Z := Eval vm_compute in (s_pc s36).
Definition ps11 : SR.post_spec := SegFn.ps_f 726388 regs_out11 F0L cells11.
Definition regs_out12 : list expr := Eval vm_compute in (s_regs s39).
Definition exit_sp_off12 : Z := Eval vm_compute in (spoff_of s39).
Definition cells12 : list kentry := Eval vm_compute in (cells_of s39 exit_sp_off12).
Definition nfresh12 : nat := Eval vm_compute in (s_next s39 - NX0)%nat.
Definition exit_pc12 : Z := Eval vm_compute in (s_pc s39).
Definition ps12 : SR.post_spec := SegFn.ps_f 726184 regs_out12 F0L cells12.
Definition regs_out13 : list expr := Eval vm_compute in (s_regs s40).
Definition exit_sp_off13 : Z := Eval vm_compute in (spoff_of s40).
Definition cells13 : list kentry := Eval vm_compute in (cells_of s40 exit_sp_off13).
Definition nfresh13 : nat := Eval vm_compute in (s_next s40 - NX0)%nat.
Definition exit_pc13 : Z := Eval vm_compute in (s_pc s40).
Definition ps13 : SR.post_spec := SegFn.ps_f 726388 regs_out13 F0L cells13.
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec := SegFn.mkps_f F0L cells_of spoff_of st.
Definition PSS : list SR.post_spec := [ps0; ps1; ps2; ps3; ps4; ps5; ps6; ps7; ps8; ps9; ps10; ps11; ps12; ps13] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.
Lemma cert : SGP.cert_ok RSEGS SegItab_Jb_ec8934.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 726108 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.
Definition seg_sound_ax := as0_plan_sound_it SegItab_Jb_ec8934.IT SegItab_Jb_ec8934.IT_sound BF NX0 BR XSTEP F0 PSS plan 726108 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
