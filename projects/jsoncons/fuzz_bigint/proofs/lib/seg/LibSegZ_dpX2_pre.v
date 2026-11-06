(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin As0PlanKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(246248, 36%nat) ; (308512, 371%nat) ; (310104, 26%nat) ; (397156, 5%nat) ; (397176, 319%nat) ; (418004, 6%nat) ; (513096, 12%nat) ; (581136, 4%nat) ; (607360, 12%nat) ; (774784, 50%nat) ; (774984, 1%nat) ; (775184, 1%nat) ; (775188, 1%nat) ; (775192, 19%nat) ; (775268, 29%nat) ; (798124, 100%nat) ; (799628, 105%nat) ; (801172, 12%nat) ; (834348, 62%nat) ; (835960, 162%nat) ; (836608, 29%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [798260].
Definition STOPS1 : list Z := [798260] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 773480; EVar 2; EVar 3; ELit 6360328; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KUnk (SA (EVar 2) (-320)) (ELit 320);
   KImg 65536 880640;
   KWr (SA (ELit 0) (894080)) (ELit 8);
   KWr (SA (ELit 0) (894160)) (ELit 1);
   KWr (SA (ELit 0) (898032)) (ELit 8);
   KWr (SA (ELit 0) (6491480)) (ELit 1);
   KWr (SA (ELit 0) (6491488)) (ELit 4);
   KWr (SA (ELit 0) (6491496)) (ELit 8);
   KWr (SA (ELit 0) (6492024)) (ELit 4);
   KWr (SA (ELit 0) (2147468588)) (ELit 1);
   KWr (SA (ELit 0) (2147468588)) (ELit 4);
   KWr (SA (ELit 0) (2147468589)) (ELit 1);
   KWr (SA (ELit 0) (2147468590)) (ELit 1);
   KWr (SA (ELit 0) (2147468591)) (ELit 1);
   KWr (SA (ELit 0) (2147468592)) (ELit 4);
   KWr (SA (ELit 0) (2147468596)) (ELit 1);
   KWr (SA (ELit 0) (2147468596)) (ELit 4);
   KWr (SA (ELit 0) (2147468597)) (ELit 1);
   KWr (SA (ELit 0) (2147468598)) (ELit 1);
   KWr (SA (ELit 0) (2147468599)) (ELit 1);
   KWr (SA (ELit 0) (2147468600)) (ELit 1);
   KWr (SA (ELit 0) (2147468601)) (ELit 1);
   KWr (SA (ELit 0) (2147468602)) (ELit 1);
   KWr (SA (ELit 0) (2147468603)) (ELit 1);
   KWr (SA (ELit 0) (2147468604)) (ELit 1);
   KWr (SA (ELit 0) (2147468604)) (ELit 4);
   KWr (SA (ELit 0) (2147468605)) (ELit 1);
   KWr (SA (ELit 0) (2147468606)) (ELit 1);
   KWr (SA (ELit 0) (2147468607)) (ELit 1);
   KWr (SA (ELit 0) (2147468608)) (ELit 4);
   KWr (SA (ELit 0) (2147468612)) (ELit 1);
   KWr (SA (ELit 0) (2147468612)) (ELit 4);
   KWr (SA (ELit 0) (2147468613)) (ELit 1);
   KWr (SA (ELit 0) (2147468614)) (ELit 1);
   KWr (SA (ELit 0) (2147468615)) (ELit 1);
   KWr (SA (ELit 0) (2147468620)) (ELit 1);
   KWr (SA (ELit 0) (2147468620)) (ELit 4);
   KWr (SA (ELit 0) (2147468621)) (ELit 1);
   KWr (SA (ELit 0) (2147468622)) (ELit 1);
   KWr (SA (ELit 0) (2147468623)) (ELit 1);
   KWr (SA (ELit 0) (2147468624)) (ELit 4);
   KWr (SA (ELit 0) (2147468628)) (ELit 1);
   KWr (SA (ELit 0) (2147468628)) (ELit 4);
   KWr (SA (ELit 0) (2147468629)) (ELit 1);
   KWr (SA (ELit 0) (2147468630)) (ELit 1);
   KWr (SA (ELit 0) (2147468631)) (ELit 1);
   KWr (SA (ELit 0) (2147468632)) (ELit 1);
   KWr (SA (ELit 0) (2147468632)) (ELit 4);
   KWr (SA (ELit 0) (2147468633)) (ELit 1);
   KWr (SA (ELit 0) (2147468634)) (ELit 1);
   KWr (SA (ELit 0) (2147468635)) (ELit 1);
   KWr (SA (ELit 0) (2147468636)) (ELit 4);
   KWr (SA (ELit 0) (2147468640)) (ELit 1);
   KWr (SA (ELit 0) (2147468640)) (ELit 4);
   KWr (SA (ELit 0) (2147468641)) (ELit 1);
   KWr (SA (ELit 0) (2147468642)) (ELit 1);
   KWr (SA (ELit 0) (2147468643)) (ELit 1);
   KWr (SA (ELit 0) (2147468644)) (ELit 1);
   KWr (SA (ELit 0) (2147468644)) (ELit 4);
   KWr (SA (ELit 0) (2147468645)) (ELit 1);
   KWr (SA (ELit 0) (2147468646)) (ELit 1);
   KWr (SA (ELit 0) (2147468647)) (ELit 1);
   KWr (SA (ELit 0) (2147468648)) (ELit 4);
   KWr (SA (ELit 0) (2147468652)) (ELit 1);
   KWr (SA (ELit 0) (2147468652)) (ELit 4);
   KWr (SA (ELit 0) (2147468653)) (ELit 1);
   KWr (SA (ELit 0) (2147468654)) (ELit 1);
   KWr (SA (ELit 0) (2147468655)) (ELit 1);
   KWr (SA (ELit 0) (2147468656)) (ELit 1);
   KWr (SA (ELit 0) (2147468657)) (ELit 1);
   KWr (SA (ELit 0) (2147468658)) (ELit 1);
   KWr (SA (ELit 0) (2147468659)) (ELit 1);
   KWr (SA (ELit 0) (2147562580)) (ELit 1);
   KWr (SA (ELit 0) (2147562580)) (ELit 4);
   KWr (SA (ELit 0) (2147562581)) (ELit 1);
   KWr (SA (ELit 0) (2147562582)) (ELit 1);
   KWr (SA (ELit 0) (2147562583)) (ELit 1);
   KWr (SA (ELit 0) (2147562584)) (ELit 4);
   KWr (SA (ELit 0) (2147562588)) (ELit 4);
   KWr (SA (ELit 0) (2147562592)) (ELit 4);
   KWr (SA (ELit 0) (2147562596)) (ELit 4);
   KWr (SA (ELit 0) (2147562600)) (ELit 4);
   KWr (SA (ELit 0) (2147562604)) (ELit 4);
   KWr (SA (ELit 0) (2147562608)) (ELit 4);
   KWr (SA (ELit 0) (2147562612)) (ELit 4);
   KWr (SA (ELit 0) (2147562616)) (ELit 4);
   KWr (SA (ELit 0) (2147562620)) (ELit 4);
   KWr (SA (ELit 0) (2147562624)) (ELit 4);
   KWr (SA (ELit 0) (2147562628)) (ELit 4);
   KWr (SA (ELit 0) (2147562632)) (ELit 1);
   KWr (SA (ELit 0) (2147562632)) (ELit 4);
   KWr (SA (ELit 0) (2147562633)) (ELit 1);
   KWr (SA (ELit 0) (2147562634)) (ELit 1);
   KWr (SA (ELit 0) (2147562635)) (ELit 1);
   KWord (SA (ELit 0) (6360160)) 4 (EVar 44);
   KRange (EVar 44) 1 4194303;
   KWord (SA (ELit 0) (6492024)) 4 (ELit 0);
   KWord (SA (ELit 0) (6492059)) 1 (ELit 0);
   KWord (SA (ELit 0) (6491496)) 8 (ELit 6491504);
   KWord (SA (ELit 0) (6491488)) 4 (ELit 2);
   KWord (SA (ELit 0) (6491512)) 8 (ELit 775184);
   KWord (SA (ELit 0) (6491768)) 8 (ELit 513096);
   KWord (SA (ELit 0) (6491484)) 4 (ELit 0);
   KWord (SA (ELit 0) (1505760)) 1 (ELit 0);
   KWord (SA (ELit 0) (6491504)) 8 (ELit 0);
   KWord (SA (ELit 0) (894160)) 1 (ELit 0);
   KWord (SA (ELit 0) (882312)) 8 (ELit 882312);
   KWord (SA (ELit 0) (894080)) 8 (ELit 1);
   KWord (SA (ELit 0) (897872)) 4 (ELit 1);
   KWord (SA (ELit 0) (898032)) 8 (ELit 0);
   KWord (SA (ELit 0) (911384)) 1 (ELit 1);
   KWord (SA (ELit 0) (908088)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (893600)) 8 (ELit 141664);
   KWord (SA (ELit 0) (893616)) 1 (ELit 96);
   KWord (SA (ELit 0) (906140)) 1 (ELit 1);
   KWord (SA (ELit 0) (893616)) 8 (ELit 96);
   KWord (SA (ELit 0) (1504992)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (882712)) 8 (ELit 834348);
   KWord (SA (ELit 0) (893656)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (893664)) 8 (ELit 141760);
   KWord (SA (ELit 0) (893680)) 1 (ELit 32);
   KWord (SA (ELit 0) (893680)) 8 (ELit 32);
   KWord (SA (ELit 0) (893720)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (893728)) 8 (ELit 141792);
   KWord (SA (ELit 0) (893744)) 1 (ELit 96);
   KWord (SA (ELit 0) (893744)) 8 (ELit 96);
   KWord (SA (ELit 0) (893784)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (893792)) 8 (ELit 141920);
   KWord (SA (ELit 0) (893808)) 1 (ELit 96);
   KWord (SA (ELit 0) (893808)) 8 (ELit 96);
   KWord (SA (ELit 0) (893848)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (893856)) 8 (ELit 142016);
   KWord (SA (ELit 0) (893872)) 1 (ELit 96);
   KWord (SA (ELit 0) (893872)) 8 (ELit 96);
   KWord (SA (ELit 0) (893912)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (893920)) 8 (ELit 142112);
   KWord (SA (ELit 0) (893936)) 1 (ELit 96);
   KWord (SA (ELit 0) (893936)) 8 (ELit 96);
   KWord (SA (ELit 0) (893976)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (893984)) 8 (ELit 142208);
   KWord (SA (ELit 0) (894000)) 1 (ELit 32);
   KWord (SA (ELit 0) (894000)) 8 (ELit 32);
   KWord (SA (ELit 0) (894040)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (6493184)) 8 (ELit 0);
   KWord (SA (ELit 0) (893544)) 8 (ELit 893312);
   KWord (SA (ELit 0) (893452)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (893352)) 8 (ELit 0);
   KWord (SA (ELit 0) (893368)) 8 (ELit 0);
   KWord (SA (ELit 0) (893320)) 8 (ELit 0);
   KWord (SA (ELit 0) (893328)) 8 (ELit 0);
   KWord (SA (ELit 0) (893304)) 8 (ELit 893072);
   KWord (SA (ELit 0) (893212)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (893112)) 8 (ELit 6493210);
   KWord (SA (ELit 0) (893128)) 8 (ELit 6493208);
   KWord (SA (ELit 0) (893144)) 8 (ELit 798124);
   KWord (SA (ELit 0) (6491464)) 8 (EVar 40);
   KWord (SA (ELit 0) (893192)) 4 (ELit 1);
   KWord (SA (ELit 0) (6491520)) 8 (ELit 775184);
   KWord (SA (ELit 0) (6491776)) 8 (ELit 581136);
   KWord (SA (ELit 0) (6357396)) 1 (ELit 0)].
Definition ss0 : sym_state := SS 775268 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-320), ELit 320); (ELit 0, (894080), ELit 8); (ELit 0, (894160), ELit 1); (ELit 0, (898032), ELit 8); (ELit 0, (6491480), ELit 1); (ELit 0, (6491488), ELit 4); (ELit 0, (6491496), ELit 8); (ELit 0, (6492024), ELit 4); (ELit 0, (2147468588), ELit 1); (ELit 0, (2147468588), ELit 4); (ELit 0, (2147468589), ELit 1); (ELit 0, (2147468590), ELit 1); (ELit 0, (2147468591), ELit 1); (ELit 0, (2147468592), ELit 4); (ELit 0, (2147468596), ELit 1); (ELit 0, (2147468596), ELit 4); (ELit 0, (2147468597), ELit 1); (ELit 0, (2147468598), ELit 1); (ELit 0, (2147468599), ELit 1); (ELit 0, (2147468600), ELit 1); (ELit 0, (2147468601), ELit 1); (ELit 0, (2147468602), ELit 1); (ELit 0, (2147468603), ELit 1); (ELit 0, (2147468604), ELit 1); (ELit 0, (2147468604), ELit 4); (ELit 0, (2147468605), ELit 1); (ELit 0, (2147468606), ELit 1); (ELit 0, (2147468607), ELit 1); (ELit 0, (2147468608), ELit 4); (ELit 0, (2147468612), ELit 1); (ELit 0, (2147468612), ELit 4); (ELit 0, (2147468613), ELit 1); (ELit 0, (2147468614), ELit 1); (ELit 0, (2147468615), ELit 1); (ELit 0, (2147468620), ELit 1); (ELit 0, (2147468620), ELit 4); (ELit 0, (2147468621), ELit 1); (ELit 0, (2147468622), ELit 1); (ELit 0, (2147468623), ELit 1); (ELit 0, (2147468624), ELit 4); (ELit 0, (2147468628), ELit 1); (ELit 0, (2147468628), ELit 4); (ELit 0, (2147468629), ELit 1); (ELit 0, (2147468630), ELit 1); (ELit 0, (2147468631), ELit 1); (ELit 0, (2147468632), ELit 1); (ELit 0, (2147468632), ELit 4); (ELit 0, (2147468633), ELit 1); (ELit 0, (2147468634), ELit 1); (ELit 0, (2147468635), ELit 1); (ELit 0, (2147468636), ELit 4); (ELit 0, (2147468640), ELit 1); (ELit 0, (2147468640), ELit 4); (ELit 0, (2147468641), ELit 1); (ELit 0, (2147468642), ELit 1); (ELit 0, (2147468643), ELit 1); (ELit 0, (2147468644), ELit 1); (ELit 0, (2147468644), ELit 4); (ELit 0, (2147468645), ELit 1); (ELit 0, (2147468646), ELit 1); (ELit 0, (2147468647), ELit 1); (ELit 0, (2147468648), ELit 4); (ELit 0, (2147468652), ELit 1); (ELit 0, (2147468652), ELit 4); (ELit 0, (2147468653), ELit 1); (ELit 0, (2147468654), ELit 1); (ELit 0, (2147468655), ELit 1); (ELit 0, (2147468656), ELit 1); (ELit 0, (2147468657), ELit 1); (ELit 0, (2147468658), ELit 1); (ELit 0, (2147468659), ELit 1); (ELit 0, (2147562580), ELit 1); (ELit 0, (2147562580), ELit 4); (ELit 0, (2147562581), ELit 1); (ELit 0, (2147562582), ELit 1); (ELit 0, (2147562583), ELit 1); (ELit 0, (2147562584), ELit 4); (ELit 0, (2147562588), ELit 4); (ELit 0, (2147562592), ELit 4); (ELit 0, (2147562596), ELit 4); (ELit 0, (2147562600), ELit 4); (ELit 0, (2147562604), ELit 4); (ELit 0, (2147562608), ELit 4); (ELit 0, (2147562612), ELit 4); (ELit 0, (2147562616), ELit 4); (ELit 0, (2147562620), ELit 4); (ELit 0, (2147562624), ELit 4); (ELit 0, (2147562628), ELit 4); (ELit 0, (2147562632), ELit 1); (ELit 0, (2147562632), ELit 4); (ELit 0, (2147562633), ELit 1); (ELit 0, (2147562634), ELit 1); (ELit 0, (2147562635), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-320), 320); (ELit 0, (894080), 8); (ELit 0, (894160), 1); (ELit 0, (898032), 8); (ELit 0, (6491480), 1); (ELit 0, (6491488), 4); (ELit 0, (6491496), 8); (ELit 0, (6492024), 4); (ELit 0, (2147468588), 1); (ELit 0, (2147468588), 4); (ELit 0, (2147468589), 1); (ELit 0, (2147468590), 1); (ELit 0, (2147468591), 1); (ELit 0, (2147468592), 4); (ELit 0, (2147468596), 1); (ELit 0, (2147468596), 4); (ELit 0, (2147468597), 1); (ELit 0, (2147468598), 1); (ELit 0, (2147468599), 1); (ELit 0, (2147468600), 1); (ELit 0, (2147468601), 1); (ELit 0, (2147468602), 1); (ELit 0, (2147468603), 1); (ELit 0, (2147468604), 1); (ELit 0, (2147468604), 4); (ELit 0, (2147468605), 1); (ELit 0, (2147468606), 1); (ELit 0, (2147468607), 1); (ELit 0, (2147468608), 4); (ELit 0, (2147468612), 1); (ELit 0, (2147468612), 4); (ELit 0, (2147468613), 1); (ELit 0, (2147468614), 1); (ELit 0, (2147468615), 1); (ELit 0, (2147468620), 1); (ELit 0, (2147468620), 4); (ELit 0, (2147468621), 1); (ELit 0, (2147468622), 1); (ELit 0, (2147468623), 1); (ELit 0, (2147468624), 4); (ELit 0, (2147468628), 1); (ELit 0, (2147468628), 4); (ELit 0, (2147468629), 1); (ELit 0, (2147468630), 1); (ELit 0, (2147468631), 1); (ELit 0, (2147468632), 1); (ELit 0, (2147468632), 4); (ELit 0, (2147468633), 1); (ELit 0, (2147468634), 1); (ELit 0, (2147468635), 1); (ELit 0, (2147468636), 4); (ELit 0, (2147468640), 1); (ELit 0, (2147468640), 4); (ELit 0, (2147468641), 1); (ELit 0, (2147468642), 1); (ELit 0, (2147468643), 1); (ELit 0, (2147468644), 1); (ELit 0, (2147468644), 4); (ELit 0, (2147468645), 1); (ELit 0, (2147468646), 1); (ELit 0, (2147468647), 1); (ELit 0, (2147468648), 4); (ELit 0, (2147468652), 1); (ELit 0, (2147468652), 4); (ELit 0, (2147468653), 1); (ELit 0, (2147468654), 1); (ELit 0, (2147468655), 1); (ELit 0, (2147468656), 1); (ELit 0, (2147468657), 1); (ELit 0, (2147468658), 1); (ELit 0, (2147468659), 1); (ELit 0, (2147562580), 1); (ELit 0, (2147562580), 4); (ELit 0, (2147562581), 1); (ELit 0, (2147562582), 1); (ELit 0, (2147562583), 1); (ELit 0, (2147562584), 4); (ELit 0, (2147562588), 4); (ELit 0, (2147562592), 4); (ELit 0, (2147562596), 4); (ELit 0, (2147562600), 4); (ELit 0, (2147562604), 4); (ELit 0, (2147562608), 4); (ELit 0, (2147562612), 4); (ELit 0, (2147562616), 4); (ELit 0, (2147562620), 4); (ELit 0, (2147562624), 4); (ELit 0, (2147562628), 4); (ELit 0, (2147562632), 1); (ELit 0, (2147562632), 4); (ELit 0, (2147562633), 1); (ELit 0, (2147562634), 1); (ELit 0, (2147562635), 1)].
Definition BF : nat := 200000.
(* [comment removed for export] *)
Definition BR : list SGP.bfact := [].
(* [comment removed for export] *)
Definition XSTEP := SGP.xstep_none.
Definition XSTEP2 := SGP.xstep2_none.
Definition AUTO := SGA.auto RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF STOPS1 ENDS A0 F0.
Definition LOADB := SGP.loadbyte IT BR.
Definition BLOCK := SGP.step1 RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF F0 (SR.SBlock STOPS1).
Set Printing Width 1000000. Set Printing Depth 1000000.

(* [comment removed for export] *)
Definition ex1 := Eval vm_compute in (AUTO 4000 ss0).
Definition s1 : sym_state := snd (snd ex1).

Definition plan : SGP.splan := SGA.mkplan (fst ex1) (SGP.PEnd 0).
Definition in_foot (b : expr) (k : Z) (w : Z) : bool :=
  existsb (fun r : SR.region => let '(rb, rlo, rlen) := r in (expr_eqb rb b && Z.leb rlo k && Z.leb (k + w) (rlo + rlen))%bool) F0L.
Definition in_kn0 (K : kentry) : bool := existsb (APC.kentry_eqb K) kn0.
Definition SPV : nat := 2%nat.   (* [comment removed for export] *)
Definition live (spoff : Z) (b : expr) (k : Z) : bool := (negb (expr_eqb b (EVar SPV)) || Z.leb spoff k)%bool.
(* [comment removed for export] *)
Definition cells_of (sF : sym_state) (spoff : Z) : list kentry :=
  List.filter (fun K => match K with
     | KWord (SA b k) w _ => live spoff b k && (in_foot b k (Z.of_nat w) || negb (in_kn0 K))
     | KZero (SA b k) (ELit n) | KFill (SA b k) (ELit n) _ | KBlob (SA b k) (ELit n) _ => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KZero (SA b k) _ | KFill (SA b k) _ _ | KBlob (SA b k) _ _ => live spoff b k && (in_foot b k 1 || negb (in_kn0 K))
     | KUnk (SA b k) (ELit n) => live spoff b k && (in_foot b k n || negb (in_kn0 K))
     | KRange _ _ _ | KAlign _ _ => negb (in_kn0 K)      (* [comment removed for export] *)
     | _ => false end)%bool (s_know sF).
Definition spoff_of (sF : sym_state) : Z := match nth 2 (s_regs sF) (ELit 0) with EAlu _ (EVar v) (ELit k) => if Nat.eqb v SPV then k else 0 | _ => 0 end.

(* [comment removed for export] *)
Definition regs_out0 : list expr := Eval vm_compute in (s_regs s1).
Definition exit_sp_off0 : Z := Eval vm_compute in (spoff_of s1).
Definition cells0 : list kentry := Eval vm_compute in (cells_of s1 exit_sp_off0).
Definition nfresh0 : nat := Eval vm_compute in (s_next s1 - NX0)%nat.
Definition exit_pc0 : Z := Eval vm_compute in (s_pc s1).
Definition ps0 : SR.post_spec := SR.PS 798260 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 775268 regs0 kn0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 775268 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
