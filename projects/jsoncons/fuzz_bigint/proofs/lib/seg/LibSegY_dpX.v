(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Bo0PlanKit.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(246888, 36%nat) ; (309152, 371%nat) ; (310744, 26%nat) ; (397796, 5%nat) ; (397816, 319%nat) ; (418644, 6%nat) ; (513736, 12%nat) ; (581776, 4%nat) ; (610452, 12%nat) ; (777800, 7%nat) ; (777876, 50%nat) ; (778076, 1%nat) ; (778276, 1%nat) ; (778280, 1%nat) ; (778284, 19%nat) ; (778360, 29%nat) ; (802720, 105%nat) ; (804264, 12%nat) ; (837440, 62%nat) ; (839052, 162%nat) ; (839700, 29%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition ENDS : list Z := [777808].
Definition STOPS1 : list Z := [777808] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 776572; EVar 2; EVar 3; ELit 6363400; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KUnk (SA (EVar 2) (-320)) (ELit 320);
   KImg 65536 884736;
   KWr (SA (ELit 0) (897152)) (ELit 8);
   KWr (SA (ELit 0) (897232)) (ELit 1);
   KWr (SA (ELit 0) (901104)) (ELit 8);
   KWr (SA (ELit 0) (6494552)) (ELit 1);
   KWr (SA (ELit 0) (6494560)) (ELit 4);
   KWr (SA (ELit 0) (6494568)) (ELit 8);
   KWr (SA (ELit 0) (6495096)) (ELit 4);
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
   KWr (SA (ELit 0) (2147468660)) (ELit 1);
   KWr (SA (ELit 0) (2147468660)) (ELit 4);
   KWr (SA (ELit 0) (2147468661)) (ELit 1);
   KWr (SA (ELit 0) (2147468662)) (ELit 1);
   KWr (SA (ELit 0) (2147468663)) (ELit 1);
   KWr (SA (ELit 0) (2147468664)) (ELit 4);
   KWr (SA (ELit 0) (2147468668)) (ELit 1);
   KWr (SA (ELit 0) (2147468668)) (ELit 4);
   KWr (SA (ELit 0) (2147468669)) (ELit 1);
   KWr (SA (ELit 0) (2147468670)) (ELit 1);
   KWr (SA (ELit 0) (2147468671)) (ELit 1);
   KWr (SA (ELit 0) (2147468672)) (ELit 1);
   KWr (SA (ELit 0) (2147468672)) (ELit 4);
   KWr (SA (ELit 0) (2147468673)) (ELit 1);
   KWr (SA (ELit 0) (2147468674)) (ELit 1);
   KWr (SA (ELit 0) (2147468675)) (ELit 1);
   KWr (SA (ELit 0) (2147468676)) (ELit 4);
   KWr (SA (ELit 0) (2147468680)) (ELit 1);
   KWr (SA (ELit 0) (2147468680)) (ELit 4);
   KWr (SA (ELit 0) (2147468681)) (ELit 1);
   KWr (SA (ELit 0) (2147468682)) (ELit 1);
   KWr (SA (ELit 0) (2147468683)) (ELit 1);
   KWr (SA (ELit 0) (2147468684)) (ELit 1);
   KWr (SA (ELit 0) (2147468684)) (ELit 4);
   KWr (SA (ELit 0) (2147468685)) (ELit 1);
   KWr (SA (ELit 0) (2147468686)) (ELit 1);
   KWr (SA (ELit 0) (2147468687)) (ELit 1);
   KWr (SA (ELit 0) (2147468688)) (ELit 4);
   KWr (SA (ELit 0) (2147468692)) (ELit 1);
   KWr (SA (ELit 0) (2147468692)) (ELit 4);
   KWr (SA (ELit 0) (2147468693)) (ELit 1);
   KWr (SA (ELit 0) (2147468694)) (ELit 1);
   KWr (SA (ELit 0) (2147468695)) (ELit 1);
   KWr (SA (ELit 0) (2147468696)) (ELit 1);
   KWr (SA (ELit 0) (2147468697)) (ELit 1);
   KWr (SA (ELit 0) (2147468698)) (ELit 1);
   KWr (SA (ELit 0) (2147468699)) (ELit 1);
   KWr (SA (ELit 0) (2147562966)) (ELit 1);
   KWr (SA (ELit 0) (2147562967)) (ELit 1);
   KWr (SA (ELit 0) (2147562968)) (ELit 1);
   KWr (SA (ELit 0) (2147562968)) (ELit 4);
   KWr (SA (ELit 0) (2147562969)) (ELit 1);
   KWr (SA (ELit 0) (2147562972)) (ELit 4);
   KWr (SA (ELit 0) (2147562976)) (ELit 4);
   KWr (SA (ELit 0) (2147562980)) (ELit 4);
   KWr (SA (ELit 0) (2147562984)) (ELit 4);
   KWr (SA (ELit 0) (2147562988)) (ELit 4);
   KWr (SA (ELit 0) (2147562992)) (ELit 4);
   KWr (SA (ELit 0) (2147562996)) (ELit 4);
   KWr (SA (ELit 0) (2147563000)) (ELit 4);
   KWr (SA (ELit 0) (2147563004)) (ELit 4);
   KWr (SA (ELit 0) (2147563008)) (ELit 4);
   KWr (SA (ELit 0) (2147563012)) (ELit 4);
   KWr (SA (ELit 0) (2147563016)) (ELit 4);
   KWr (SA (ELit 0) (2147563018)) (ELit 1);
   KWr (SA (ELit 0) (2147563019)) (ELit 1);
   KWr (SA (ELit 0) (2147563020)) (ELit 1);
   KWr (SA (ELit 0) (2147563021)) (ELit 1);
   KWord (SA (ELit 0) (6363232)) 4 (EVar 44);
   KRange (EVar 44) 1 4194303;
   KWord (SA (ELit 0) (6495096)) 4 (ELit 0);
   KWord (SA (ELit 0) (6495131)) 1 (ELit 0);
   KWord (SA (ELit 0) (6494568)) 8 (ELit 6494576);
   KWord (SA (ELit 0) (6494560)) 4 (ELit 2);
   KWord (SA (ELit 0) (6494584)) 8 (ELit 778276);
   KWord (SA (ELit 0) (6494840)) 8 (ELit 513736);
   KWord (SA (ELit 0) (6494556)) 4 (ELit 0);
   KWord (SA (ELit 0) (1508832)) 1 (ELit 0);
   KWord (SA (ELit 0) (6494576)) 8 (ELit 0);
   KWord (SA (ELit 0) (897232)) 1 (ELit 0);
   KWord (SA (ELit 0) (885400)) 8 (ELit 885400);
   KWord (SA (ELit 0) (897152)) 8 (ELit 1);
   KWord (SA (ELit 0) (900944)) 4 (ELit 1);
   KWord (SA (ELit 0) (901104)) 8 (ELit 0);
   KWord (SA (ELit 0) (914456)) 1 (ELit 1);
   KWord (SA (ELit 0) (911160)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (896688)) 8 (ELit 141664);
   KWord (SA (ELit 0) (896704)) 1 (ELit 96);
   KWord (SA (ELit 0) (909212)) 1 (ELit 1);
   KWord (SA (ELit 0) (896704)) 8 (ELit 96);
   KWord (SA (ELit 0) (1508064)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (885800)) 8 (ELit 837440);
   KWord (SA (ELit 0) (896744)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (896752)) 8 (ELit 141760);
   KWord (SA (ELit 0) (896768)) 1 (ELit 32);
   KWord (SA (ELit 0) (896768)) 8 (ELit 32);
   KWord (SA (ELit 0) (896808)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (896816)) 8 (ELit 142112);
   KWord (SA (ELit 0) (896832)) 1 (ELit 96);
   KWord (SA (ELit 0) (896832)) 8 (ELit 96);
   KWord (SA (ELit 0) (896872)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (896880)) 8 (ELit 142240);
   KWord (SA (ELit 0) (896896)) 1 (ELit 96);
   KWord (SA (ELit 0) (896896)) 8 (ELit 96);
   KWord (SA (ELit 0) (896936)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (896944)) 8 (ELit 142336);
   KWord (SA (ELit 0) (896960)) 1 (ELit 96);
   KWord (SA (ELit 0) (896960)) 8 (ELit 96);
   KWord (SA (ELit 0) (897000)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (897008)) 8 (ELit 142432);
   KWord (SA (ELit 0) (897024)) 1 (ELit 96);
   KWord (SA (ELit 0) (897024)) 8 (ELit 96);
   KWord (SA (ELit 0) (897064)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (897072)) 8 (ELit 142528);
   KWord (SA (ELit 0) (897088)) 1 (ELit 32);
   KWord (SA (ELit 0) (897088)) 8 (ELit 32);
   KWord (SA (ELit 0) (897128)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (6496256)) 8 (ELit 0);
   KWord (SA (ELit 0) (896632)) 8 (ELit 896400);
   KWord (SA (ELit 0) (896540)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (896440)) 8 (ELit 0);
   KWord (SA (ELit 0) (896456)) 8 (ELit 0);
   KWord (SA (ELit 0) (896408)) 8 (ELit 0);
   KWord (SA (ELit 0) (896416)) 8 (ELit 0);
   KWord (SA (ELit 0) (896392)) 8 (ELit 896160);
   KWord (SA (ELit 0) (896300)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (896200)) 8 (ELit 6496280);
   KWord (SA (ELit 0) (896216)) 8 (ELit 6496280);
   KWord (SA (ELit 0) (896168)) 8 (ELit 0);
   KWord (SA (ELit 0) (896176)) 8 (ELit 0);
   KWord (SA (ELit 0) (896152)) 8 (ELit 895920);
   KWord (SA (ELit 0) (896060)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (895960)) 8 (ELit 0);
   KWord (SA (ELit 0) (895976)) 8 (ELit 0);
   KWord (SA (ELit 0) (895928)) 8 (ELit 0);
   KWord (SA (ELit 0) (895936)) 8 (ELit 0);
   KWord (SA (ELit 0) (6494592)) 8 (ELit 778276);
   KWord (SA (ELit 0) (6494848)) 8 (ELit 581776);
   KWord (SA (ELit 0) (6360468)) 1 (ELit 0)].
Definition ss0 : sym_state := SS 778360 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-320), ELit 320); (ELit 0, (897152), ELit 8); (ELit 0, (897232), ELit 1); (ELit 0, (901104), ELit 8); (ELit 0, (6494552), ELit 1); (ELit 0, (6494560), ELit 4); (ELit 0, (6494568), ELit 8); (ELit 0, (6495096), ELit 4); (ELit 0, (2147468588), ELit 1); (ELit 0, (2147468588), ELit 4); (ELit 0, (2147468589), ELit 1); (ELit 0, (2147468590), ELit 1); (ELit 0, (2147468591), ELit 1); (ELit 0, (2147468592), ELit 4); (ELit 0, (2147468596), ELit 1); (ELit 0, (2147468596), ELit 4); (ELit 0, (2147468597), ELit 1); (ELit 0, (2147468598), ELit 1); (ELit 0, (2147468599), ELit 1); (ELit 0, (2147468600), ELit 1); (ELit 0, (2147468601), ELit 1); (ELit 0, (2147468602), ELit 1); (ELit 0, (2147468603), ELit 1); (ELit 0, (2147468644), ELit 1); (ELit 0, (2147468644), ELit 4); (ELit 0, (2147468645), ELit 1); (ELit 0, (2147468646), ELit 1); (ELit 0, (2147468647), ELit 1); (ELit 0, (2147468648), ELit 4); (ELit 0, (2147468652), ELit 1); (ELit 0, (2147468652), ELit 4); (ELit 0, (2147468653), ELit 1); (ELit 0, (2147468654), ELit 1); (ELit 0, (2147468655), ELit 1); (ELit 0, (2147468660), ELit 1); (ELit 0, (2147468660), ELit 4); (ELit 0, (2147468661), ELit 1); (ELit 0, (2147468662), ELit 1); (ELit 0, (2147468663), ELit 1); (ELit 0, (2147468664), ELit 4); (ELit 0, (2147468668), ELit 1); (ELit 0, (2147468668), ELit 4); (ELit 0, (2147468669), ELit 1); (ELit 0, (2147468670), ELit 1); (ELit 0, (2147468671), ELit 1); (ELit 0, (2147468672), ELit 1); (ELit 0, (2147468672), ELit 4); (ELit 0, (2147468673), ELit 1); (ELit 0, (2147468674), ELit 1); (ELit 0, (2147468675), ELit 1); (ELit 0, (2147468676), ELit 4); (ELit 0, (2147468680), ELit 1); (ELit 0, (2147468680), ELit 4); (ELit 0, (2147468681), ELit 1); (ELit 0, (2147468682), ELit 1); (ELit 0, (2147468683), ELit 1); (ELit 0, (2147468684), ELit 1); (ELit 0, (2147468684), ELit 4); (ELit 0, (2147468685), ELit 1); (ELit 0, (2147468686), ELit 1); (ELit 0, (2147468687), ELit 1); (ELit 0, (2147468688), ELit 4); (ELit 0, (2147468692), ELit 1); (ELit 0, (2147468692), ELit 4); (ELit 0, (2147468693), ELit 1); (ELit 0, (2147468694), ELit 1); (ELit 0, (2147468695), ELit 1); (ELit 0, (2147468696), ELit 1); (ELit 0, (2147468697), ELit 1); (ELit 0, (2147468698), ELit 1); (ELit 0, (2147468699), ELit 1); (ELit 0, (2147562966), ELit 1); (ELit 0, (2147562967), ELit 1); (ELit 0, (2147562968), ELit 1); (ELit 0, (2147562968), ELit 4); (ELit 0, (2147562969), ELit 1); (ELit 0, (2147562972), ELit 4); (ELit 0, (2147562976), ELit 4); (ELit 0, (2147562980), ELit 4); (ELit 0, (2147562984), ELit 4); (ELit 0, (2147562988), ELit 4); (ELit 0, (2147562992), ELit 4); (ELit 0, (2147562996), ELit 4); (ELit 0, (2147563000), ELit 4); (ELit 0, (2147563004), ELit 4); (ELit 0, (2147563008), ELit 4); (ELit 0, (2147563012), ELit 4); (ELit 0, (2147563016), ELit 4); (ELit 0, (2147563018), ELit 1); (ELit 0, (2147563019), ELit 1); (ELit 0, (2147563020), ELit 1); (ELit 0, (2147563021), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-320), 320); (ELit 0, (897152), 8); (ELit 0, (897232), 1); (ELit 0, (901104), 8); (ELit 0, (6494552), 1); (ELit 0, (6494560), 4); (ELit 0, (6494568), 8); (ELit 0, (6495096), 4); (ELit 0, (2147468588), 1); (ELit 0, (2147468588), 4); (ELit 0, (2147468589), 1); (ELit 0, (2147468590), 1); (ELit 0, (2147468591), 1); (ELit 0, (2147468592), 4); (ELit 0, (2147468596), 1); (ELit 0, (2147468596), 4); (ELit 0, (2147468597), 1); (ELit 0, (2147468598), 1); (ELit 0, (2147468599), 1); (ELit 0, (2147468600), 1); (ELit 0, (2147468601), 1); (ELit 0, (2147468602), 1); (ELit 0, (2147468603), 1); (ELit 0, (2147468644), 1); (ELit 0, (2147468644), 4); (ELit 0, (2147468645), 1); (ELit 0, (2147468646), 1); (ELit 0, (2147468647), 1); (ELit 0, (2147468648), 4); (ELit 0, (2147468652), 1); (ELit 0, (2147468652), 4); (ELit 0, (2147468653), 1); (ELit 0, (2147468654), 1); (ELit 0, (2147468655), 1); (ELit 0, (2147468660), 1); (ELit 0, (2147468660), 4); (ELit 0, (2147468661), 1); (ELit 0, (2147468662), 1); (ELit 0, (2147468663), 1); (ELit 0, (2147468664), 4); (ELit 0, (2147468668), 1); (ELit 0, (2147468668), 4); (ELit 0, (2147468669), 1); (ELit 0, (2147468670), 1); (ELit 0, (2147468671), 1); (ELit 0, (2147468672), 1); (ELit 0, (2147468672), 4); (ELit 0, (2147468673), 1); (ELit 0, (2147468674), 1); (ELit 0, (2147468675), 1); (ELit 0, (2147468676), 4); (ELit 0, (2147468680), 1); (ELit 0, (2147468680), 4); (ELit 0, (2147468681), 1); (ELit 0, (2147468682), 1); (ELit 0, (2147468683), 1); (ELit 0, (2147468684), 1); (ELit 0, (2147468684), 4); (ELit 0, (2147468685), 1); (ELit 0, (2147468686), 1); (ELit 0, (2147468687), 1); (ELit 0, (2147468688), 4); (ELit 0, (2147468692), 1); (ELit 0, (2147468692), 4); (ELit 0, (2147468693), 1); (ELit 0, (2147468694), 1); (ELit 0, (2147468695), 1); (ELit 0, (2147468696), 1); (ELit 0, (2147468697), 1); (ELit 0, (2147468698), 1); (ELit 0, (2147468699), 1); (ELit 0, (2147562966), 1); (ELit 0, (2147562967), 1); (ELit 0, (2147562968), 1); (ELit 0, (2147562968), 4); (ELit 0, (2147562969), 1); (ELit 0, (2147562972), 4); (ELit 0, (2147562976), 4); (ELit 0, (2147562980), 4); (ELit 0, (2147562984), 4); (ELit 0, (2147562988), 4); (ELit 0, (2147562992), 4); (ELit 0, (2147562996), 4); (ELit 0, (2147563000), 4); (ELit 0, (2147563004), 4); (ELit 0, (2147563008), 4); (ELit 0, (2147563012), 4); (ELit 0, (2147563016), 4); (ELit 0, (2147563018), 1); (ELit 0, (2147563019), 1); (ELit 0, (2147563020), 1); (ELit 0, (2147563021), 1)].
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
Eval vm_compute in (1000+1, length (fst ex1), fst (snd ex1), s_pc s1, s_next s1).

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
Definition ps0 : SR.post_spec := SR.PS 777808 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.
Eval vm_compute in (3500+0, Z.eqb (s_pc s1) 777808, s_pc s1).

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS (itab_of RSEGS ITR) X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 778360 regs0 kn0 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound ITR BF NX0 BR XSTEP F0 PSS plan 778360 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
Check seg_sound_ax.
Eval vm_compute in (3003, regs0).
Eval vm_compute in (3004, kn0).
Eval vm_compute in (3100+0, regs_out0).
Eval vm_compute in (3200+0, cells0).
Eval vm_compute in (3300+0, nfresh0, exit_sp_off0).
Eval vm_compute in (3400+0, s_know s1).
Eval vm_compute in (3600, length SXALL).
Eval vm_compute in (3601, map (fun st => (s_pc st, spoff_of st, (s_next st - NX0)%nat)) SXALL).
Eval vm_compute in (3602, map s_regs SXALL).
Eval vm_compute in (3603, map (fun st => cells_of st (spoff_of st)) SXALL).
Eval vm_compute in (3604, map s_know SXALL).
