(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin Ba0PlanKit Ba0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.seg Require SegItab_Ba_cc72f4.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_cc72f4.ITR.
Definition IT : itab := SegItab_Ba_cc72f4.IT.
Definition ENDS : list Z := [1170604].
Definition STOPS1 : list Z := [1170604] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 1137416; EVar 2; EVar 3; ELit 6756480; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KUnk (SA (EVar 2) (-320)) (ELit 320);
   KImg 65536 1269760;
   KWr (SA (ELit 0) (1286400)) (ELit 8);
   KWr (SA (ELit 0) (1286480)) (ELit 1);
   KWr (SA (ELit 0) (1290352)) (ELit 8);
   KWr (SA (ELit 0) (6887632)) (ELit 1);
   KWr (SA (ELit 0) (6887640)) (ELit 4);
   KWr (SA (ELit 0) (6887648)) (ELit 8);
   KWr (SA (ELit 0) (6888176)) (ELit 4);
   KWr (SA (ELit 0) (2147468852)) (ELit 1);
   KWr (SA (ELit 0) (2147468853)) (ELit 1);
   KWr (SA (ELit 0) (2147468854)) (ELit 1);
   KWr (SA (ELit 0) (2147468855)) (ELit 1);
   KWr (SA (ELit 0) (2147468864)) (ELit 1);
   KWr (SA (ELit 0) (2147468865)) (ELit 1);
   KWr (SA (ELit 0) (2147468866)) (ELit 1);
   KWr (SA (ELit 0) (2147468867)) (ELit 1);
   KWr (SA (ELit 0) (2147468868)) (ELit 1);
   KWr (SA (ELit 0) (2147468868)) (ELit 4);
   KWr (SA (ELit 0) (2147468869)) (ELit 1);
   KWr (SA (ELit 0) (2147468870)) (ELit 1);
   KWr (SA (ELit 0) (2147468871)) (ELit 1);
   KWr (SA (ELit 0) (2147468872)) (ELit 4);
   KWr (SA (ELit 0) (2147468876)) (ELit 1);
   KWr (SA (ELit 0) (2147468876)) (ELit 4);
   KWr (SA (ELit 0) (2147468877)) (ELit 1);
   KWr (SA (ELit 0) (2147468878)) (ELit 1);
   KWr (SA (ELit 0) (2147468879)) (ELit 1);
   KWr (SA (ELit 0) (2147468892)) (ELit 1);
   KWr (SA (ELit 0) (2147468893)) (ELit 1);
   KWr (SA (ELit 0) (2147468894)) (ELit 1);
   KWr (SA (ELit 0) (2147468895)) (ELit 1);
   KWr (SA (ELit 0) (2147468896)) (ELit 1);
   KWr (SA (ELit 0) (2147468897)) (ELit 1);
   KWr (SA (ELit 0) (2147468898)) (ELit 1);
   KWr (SA (ELit 0) (2147468899)) (ELit 1);
   KWr (SA (ELit 0) (2147468900)) (ELit 1);
   KWr (SA (ELit 0) (2147468901)) (ELit 1);
   KWr (SA (ELit 0) (2147468902)) (ELit 1);
   KWr (SA (ELit 0) (2147468903)) (ELit 1);
   KWr (SA (ELit 0) (2147468904)) (ELit 1);
   KWr (SA (ELit 0) (2147468905)) (ELit 1);
   KWr (SA (ELit 0) (2147468906)) (ELit 1);
   KWr (SA (ELit 0) (2147468907)) (ELit 1);
   KWr (SA (ELit 0) (2147468908)) (ELit 1);
   KWr (SA (ELit 0) (2147468908)) (ELit 4);
   KWr (SA (ELit 0) (2147468909)) (ELit 1);
   KWr (SA (ELit 0) (2147468910)) (ELit 1);
   KWr (SA (ELit 0) (2147468911)) (ELit 1);
   KWr (SA (ELit 0) (2147468912)) (ELit 4);
   KWr (SA (ELit 0) (2147468916)) (ELit 1);
   KWr (SA (ELit 0) (2147468916)) (ELit 4);
   KWr (SA (ELit 0) (2147468917)) (ELit 1);
   KWr (SA (ELit 0) (2147468918)) (ELit 1);
   KWr (SA (ELit 0) (2147468919)) (ELit 1);
   KWr (SA (ELit 0) (2147468920)) (ELit 1);
   KWr (SA (ELit 0) (2147468920)) (ELit 4);
   KWr (SA (ELit 0) (2147468921)) (ELit 1);
   KWr (SA (ELit 0) (2147468922)) (ELit 1);
   KWr (SA (ELit 0) (2147468923)) (ELit 1);
   KWr (SA (ELit 0) (2147468924)) (ELit 4);
   KWr (SA (ELit 0) (2147468928)) (ELit 1);
   KWr (SA (ELit 0) (2147468928)) (ELit 4);
   KWr (SA (ELit 0) (2147468929)) (ELit 1);
   KWr (SA (ELit 0) (2147468930)) (ELit 1);
   KWr (SA (ELit 0) (2147468931)) (ELit 1);
   KWr (SA (ELit 0) (2147468932)) (ELit 1);
   KWr (SA (ELit 0) (2147468932)) (ELit 4);
   KWr (SA (ELit 0) (2147468933)) (ELit 1);
   KWr (SA (ELit 0) (2147468934)) (ELit 1);
   KWr (SA (ELit 0) (2147468935)) (ELit 1);
   KWr (SA (ELit 0) (2147468936)) (ELit 4);
   KWr (SA (ELit 0) (2147468940)) (ELit 4);
   KWr (SA (ELit 0) (2147468944)) (ELit 1);
   KWr (SA (ELit 0) (2147468944)) (ELit 4);
   KWr (SA (ELit 0) (2147468945)) (ELit 1);
   KWr (SA (ELit 0) (2147468946)) (ELit 1);
   KWr (SA (ELit 0) (2147468947)) (ELit 1);
   KWr (SA (ELit 0) (2147468948)) (ELit 1);
   KWr (SA (ELit 0) (2147468948)) (ELit 4);
   KWr (SA (ELit 0) (2147468949)) (ELit 1);
   KWr (SA (ELit 0) (2147468950)) (ELit 1);
   KWr (SA (ELit 0) (2147468951)) (ELit 1);
   KWr (SA (ELit 0) (2147468952)) (ELit 4);
   KWr (SA (ELit 0) (2147468956)) (ELit 1);
   KWr (SA (ELit 0) (2147468956)) (ELit 4);
   KWr (SA (ELit 0) (2147468957)) (ELit 1);
   KWr (SA (ELit 0) (2147468958)) (ELit 1);
   KWr (SA (ELit 0) (2147468959)) (ELit 1);
   KWr (SA (ELit 0) (2147468960)) (ELit 1);
   KWr (SA (ELit 0) (2147468961)) (ELit 1);
   KWr (SA (ELit 0) (2147468962)) (ELit 1);
   KWr (SA (ELit 0) (2147468963)) (ELit 1);
   KWr (SA (ELit 0) (2147468964)) (ELit 1);
   KWr (SA (ELit 0) (2147468965)) (ELit 1);
   KWr (SA (ELit 0) (2147468966)) (ELit 1);
   KWr (SA (ELit 0) (2147468967)) (ELit 1);
   KWr (SA (ELit 0) (2147468968)) (ELit 1);
   KWr (SA (ELit 0) (2147468969)) (ELit 1);
   KWr (SA (ELit 0) (2147468970)) (ELit 1);
   KWr (SA (ELit 0) (2147468971)) (ELit 1);
   KWr (SA (ELit 0) (2147468972)) (ELit 1);
   KWr (SA (ELit 0) (2147468973)) (ELit 1);
   KWr (SA (ELit 0) (2147468974)) (ELit 1);
   KWr (SA (ELit 0) (2147468975)) (ELit 1);
   KWr (SA (ELit 0) (2147468976)) (ELit 1);
   KWr (SA (ELit 0) (2147468977)) (ELit 1);
   KWr (SA (ELit 0) (2147468978)) (ELit 1);
   KWr (SA (ELit 0) (2147468979)) (ELit 1);
   KWr (SA (ELit 0) (2147468980)) (ELit 1);
   KWr (SA (ELit 0) (2147468981)) (ELit 1);
   KWr (SA (ELit 0) (2147468982)) (ELit 1);
   KWr (SA (ELit 0) (2147468983)) (ELit 1);
   KWr (SA (ELit 0) (2147468984)) (ELit 1);
   KWr (SA (ELit 0) (2147468985)) (ELit 1);
   KWr (SA (ELit 0) (2147468986)) (ELit 1);
   KWr (SA (ELit 0) (2147468987)) (ELit 1);
   KWr (SA (ELit 0) (2147468988)) (ELit 1);
   KWr (SA (ELit 0) (2147468989)) (ELit 1);
   KWr (SA (ELit 0) (2147468990)) (ELit 1);
   KWr (SA (ELit 0) (2147468991)) (ELit 1);
   KWr (SA (ELit 0) (2147468992)) (ELit 1);
   KWr (SA (ELit 0) (2147468993)) (ELit 1);
   KWr (SA (ELit 0) (2147468994)) (ELit 1);
   KWr (SA (ELit 0) (2147468995)) (ELit 1);
   KWr (SA (ELit 0) (2147468996)) (ELit 1);
   KWr (SA (ELit 0) (2147468997)) (ELit 1);
   KWr (SA (ELit 0) (2147468998)) (ELit 1);
   KWr (SA (ELit 0) (2147468999)) (ELit 1);
   KWr (SA (ELit 0) (2147469000)) (ELit 1);
   KWr (SA (ELit 0) (2147469001)) (ELit 1);
   KWr (SA (ELit 0) (2147469002)) (ELit 1);
   KWr (SA (ELit 0) (2147469003)) (ELit 1);
   KWr (SA (ELit 0) (2147469004)) (ELit 1);
   KWr (SA (ELit 0) (2147469005)) (ELit 1);
   KWr (SA (ELit 0) (2147469006)) (ELit 1);
   KWr (SA (ELit 0) (2147469007)) (ELit 1);
   KWr (SA (ELit 0) (2147469008)) (ELit 1);
   KWr (SA (ELit 0) (2147469009)) (ELit 1);
   KWr (SA (ELit 0) (2147469010)) (ELit 1);
   KWr (SA (ELit 0) (2147469011)) (ELit 1);
   KWr (SA (ELit 0) (2147469012)) (ELit 1);
   KWr (SA (ELit 0) (2147469013)) (ELit 1);
   KWr (SA (ELit 0) (2147469014)) (ELit 1);
   KWr (SA (ELit 0) (2147469015)) (ELit 1);
   KWr (SA (ELit 0) (2147469016)) (ELit 1);
   KWr (SA (ELit 0) (2147469016)) (ELit 4);
   KWr (SA (ELit 0) (2147469017)) (ELit 1);
   KWr (SA (ELit 0) (2147469018)) (ELit 1);
   KWr (SA (ELit 0) (2147469019)) (ELit 1);
   KWr (SA (ELit 0) (2147469020)) (ELit 4);
   KWr (SA (ELit 0) (2147469024)) (ELit 1);
   KWr (SA (ELit 0) (2147469024)) (ELit 4);
   KWr (SA (ELit 0) (2147469025)) (ELit 1);
   KWr (SA (ELit 0) (2147469026)) (ELit 1);
   KWr (SA (ELit 0) (2147469027)) (ELit 1);
   KWr (SA (ELit 0) (2147469028)) (ELit 1);
   KWr (SA (ELit 0) (2147469029)) (ELit 1);
   KWr (SA (ELit 0) (2147469030)) (ELit 1);
   KWr (SA (ELit 0) (2147469031)) (ELit 1);
   KWr (SA (ELit 0) (2147469032)) (ELit 1);
   KWr (SA (ELit 0) (2147469033)) (ELit 1);
   KWr (SA (ELit 0) (2147469034)) (ELit 1);
   KWr (SA (ELit 0) (2147469035)) (ELit 1);
   KWr (SA (ELit 0) (2147469068)) (ELit 1);
   KWr (SA (ELit 0) (2147469068)) (ELit 4);
   KWr (SA (ELit 0) (2147469069)) (ELit 1);
   KWr (SA (ELit 0) (2147469070)) (ELit 1);
   KWr (SA (ELit 0) (2147469071)) (ELit 1);
   KWr (SA (ELit 0) (2147469072)) (ELit 4);
   KWr (SA (ELit 0) (2147469076)) (ELit 1);
   KWr (SA (ELit 0) (2147469076)) (ELit 4);
   KWr (SA (ELit 0) (2147469077)) (ELit 1);
   KWr (SA (ELit 0) (2147469078)) (ELit 1);
   KWr (SA (ELit 0) (2147469079)) (ELit 1);
   KWr (SA (ELit 0) (2147469080)) (ELit 1);
   KWr (SA (ELit 0) (2147469081)) (ELit 1);
   KWr (SA (ELit 0) (2147469082)) (ELit 1);
   KWr (SA (ELit 0) (2147469083)) (ELit 1);
   KWr (SA (ELit 0) (2147469084)) (ELit 1);
   KWr (SA (ELit 0) (2147469085)) (ELit 1);
   KWr (SA (ELit 0) (2147469086)) (ELit 1);
   KWr (SA (ELit 0) (2147469087)) (ELit 1);
   KWr (SA (ELit 0) (2147469088)) (ELit 1);
   KWr (SA (ELit 0) (2147469088)) (ELit 4);
   KWr (SA (ELit 0) (2147469089)) (ELit 1);
   KWr (SA (ELit 0) (2147469090)) (ELit 1);
   KWr (SA (ELit 0) (2147469091)) (ELit 1);
   KWr (SA (ELit 0) (2147469092)) (ELit 4);
   KWr (SA (ELit 0) (2147469096)) (ELit 1);
   KWr (SA (ELit 0) (2147469096)) (ELit 4);
   KWr (SA (ELit 0) (2147469097)) (ELit 1);
   KWr (SA (ELit 0) (2147469098)) (ELit 1);
   KWr (SA (ELit 0) (2147469099)) (ELit 1);
   KWr (SA (ELit 0) (2147606248)) (ELit 1);
   KWr (SA (ELit 0) (2147606248)) (ELit 4);
   KWr (SA (ELit 0) (2147606249)) (ELit 1);
   KWr (SA (ELit 0) (2147606250)) (ELit 1);
   KWr (SA (ELit 0) (2147606251)) (ELit 1);
   KWr (SA (ELit 0) (2147606252)) (ELit 4);
   KWr (SA (ELit 0) (2147606256)) (ELit 4);
   KWr (SA (ELit 0) (2147606260)) (ELit 4);
   KWr (SA (ELit 0) (2147606264)) (ELit 1);
   KWr (SA (ELit 0) (2147606264)) (ELit 4);
   KWr (SA (ELit 0) (2147606265)) (ELit 1);
   KWr (SA (ELit 0) (2147606266)) (ELit 1);
   KWr (SA (ELit 0) (2147606267)) (ELit 1);
   KWr (SA (ELit 0) (2147611484)) (ELit 1);
   KWr (SA (ELit 0) (2147611484)) (ELit 4);
   KWr (SA (ELit 0) (2147611485)) (ELit 1);
   KWr (SA (ELit 0) (2147611486)) (ELit 1);
   KWr (SA (ELit 0) (2147611487)) (ELit 1);
   KWr (SA (ELit 0) (2147611488)) (ELit 4);
   KWr (SA (ELit 0) (2147611492)) (ELit 4);
   KWr (SA (ELit 0) (2147611496)) (ELit 4);
   KWr (SA (ELit 0) (2147611500)) (ELit 4);
   KWr (SA (ELit 0) (2147611504)) (ELit 4);
   KWr (SA (ELit 0) (2147611508)) (ELit 4);
   KWr (SA (ELit 0) (2147611512)) (ELit 8);
   KWr (SA (ELit 0) (2147611520)) (ELit 8);
   KWr (SA (ELit 0) (2147611528)) (ELit 8);
   KWr (SA (ELit 0) (2147611536)) (ELit 8);
   KWr (SA (ELit 0) (2147611544)) (ELit 8);
   KWr (SA (ELit 0) (2147611552)) (ELit 8);
   KWr (SA (ELit 0) (2147611560)) (ELit 8);
   KWr (SA (ELit 0) (2147611568)) (ELit 8);
   KWr (SA (ELit 0) (2147611576)) (ELit 8);
   KWr (SA (ELit 0) (2147611584)) (ELit 8);
   KWr (SA (ELit 0) (2147611592)) (ELit 8);
   KWr (SA (ELit 0) (2147611600)) (ELit 8);
   KWr (SA (ELit 0) (2147611608)) (ELit 8);
   KWr (SA (ELit 0) (2147611616)) (ELit 8);
   KWr (SA (ELit 0) (2147611624)) (ELit 8);
   KWr (SA (ELit 0) (2147611632)) (ELit 8);
   KWr (SA (ELit 0) (2147611640)) (ELit 8);
   KWr (SA (ELit 0) (2147611648)) (ELit 4);
   KWr (SA (ELit 0) (2147611648)) (ELit 8);
   KWr (SA (ELit 0) (2147611652)) (ELit 4);
   KWr (SA (ELit 0) (2147611656)) (ELit 4);
   KWr (SA (ELit 0) (2147611656)) (ELit 8);
   KWr (SA (ELit 0) (2147611660)) (ELit 4);
   KWr (SA (ELit 0) (2147611664)) (ELit 4);
   KWr (SA (ELit 0) (2147611664)) (ELit 8);
   KWr (SA (ELit 0) (2147611668)) (ELit 4);
   KWr (SA (ELit 0) (2147611672)) (ELit 1);
   KWr (SA (ELit 0) (2147611672)) (ELit 4);
   KWr (SA (ELit 0) (2147611673)) (ELit 1);
   KWr (SA (ELit 0) (2147611674)) (ELit 1);
   KWr (SA (ELit 0) (2147611675)) (ELit 1);
   KWord (SA (ELit 0) (6756312)) 4 (EVar 44);
   KRange (EVar 44) 1 4194303;
   KWord (SA (ELit 0) (6888176)) 4 (ELit 0);
   KWord (SA (ELit 0) (6888211)) 1 (ELit 0);
   KWord (SA (ELit 0) (6887648)) 8 (ELit 6887656);
   KWord (SA (ELit 0) (6887640)) 4 (ELit 8);
   KWord (SA (ELit 0) (6887720)) 8 (ELit 448212);
   KWord (SA (ELit 0) (6887976)) 8 (ELit 0);
   KWord (SA (ELit 0) (6887636)) 4 (ELit 0);
   KWord (SA (ELit 0) (1290196)) 1 (ELit 0);
   KWord (SA (ELit 0) (6887712)) 8 (ELit 863096);
   KWord (SA (ELit 0) (6887968)) 8 (ELit 1283856);
   KWord (SA (ELit 0) (6887704)) 8 (ELit 448212);
   KWord (SA (ELit 0) (6887960)) 8 (ELit 0);
   KWord (SA (ELit 0) (6887696)) 8 (ELit 864528);
   KWord (SA (ELit 0) (6887952)) 8 (ELit 6749800);
   KWord (SA (ELit 0) (6749800)) 1 (ELit 6);
   KWord (SA (ELit 0) (6887688)) 8 (ELit 448212);
   KWord (SA (ELit 0) (6887944)) 8 (ELit 0);
   KWord (SA (ELit 0) (6887680)) 8 (ELit 864528);
   KWord (SA (ELit 0) (6887936)) 8 (ELit 6749768);
   KWord (SA (ELit 0) (6749768)) 1 (ELit 16);
   KWord (SA (ELit 0) (6887672)) 8 (ELit 1139320);
   KWord (SA (ELit 0) (6887928)) 8 (ELit 686948);
   KWord (SA (ELit 0) (6749716)) 1 (ELit 0);
   KWord (SA (ELit 0) (6887664)) 8 (ELit 1139320);
   KWord (SA (ELit 0) (6887920)) 8 (ELit 618908);
   KWord (SA (ELit 0) (1898080)) 1 (ELit 0);
   KWord (SA (ELit 0) (6887656)) 8 (ELit 0);
   KWord (SA (ELit 0) (1286480)) 1 (ELit 0);
   KWord (SA (ELit 0) (1273320)) 8 (ELit 1273320);
   KWord (SA (ELit 0) (1286400)) 8 (ELit 1);
   KWord (SA (ELit 0) (1290192)) 4 (ELit 1);
   KWord (SA (ELit 0) (1290352)) 8 (ELit 0);
   KWord (SA (ELit 0) (1303704)) 1 (ELit 1);
   KWord (SA (ELit 0) (1300408)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (1284832)) 8 (ELit 143776);
   KWord (SA (ELit 0) (1284848)) 1 (ELit 32);
   KWord (SA (ELit 0) (1298460)) 1 (ELit 1);
   KWord (SA (ELit 0) (1284848)) 8 (ELit 32);
   KWord (SA (ELit 0) (1897312)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1273832)) 8 (ELit 1210200);
   KWord (SA (ELit 0) (1284888)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1284896)) 8 (ELit 143872);
   KWord (SA (ELit 0) (1284912)) 1 (ELit 32);
   KWord (SA (ELit 0) (1284912)) 8 (ELit 32);
   KWord (SA (ELit 0) (1284952)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1284960)) 8 (ELit 143904);
   KWord (SA (ELit 0) (1284976)) 1 (ELit 96);
   KWord (SA (ELit 0) (1284976)) 8 (ELit 96);
   KWord (SA (ELit 0) (1285016)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285024)) 8 (ELit 144096);
   KWord (SA (ELit 0) (1285040)) 1 (ELit 32);
   KWord (SA (ELit 0) (1285040)) 8 (ELit 32);
   KWord (SA (ELit 0) (1285080)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285088)) 8 (ELit 144128);
   KWord (SA (ELit 0) (1285104)) 1 (ELit 64);
   KWord (SA (ELit 0) (1285104)) 8 (ELit 64);
   KWord (SA (ELit 0) (1285144)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285152)) 8 (ELit 144192);
   KWord (SA (ELit 0) (1285168)) 1 (ELit 32);
   KWord (SA (ELit 0) (1285168)) 8 (ELit 32);
   KWord (SA (ELit 0) (1285208)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285216)) 8 (ELit 144224);
   KWord (SA (ELit 0) (1285232)) 1 (ELit 96);
   KWord (SA (ELit 0) (1285232)) 8 (ELit 96);
   KWord (SA (ELit 0) (1285272)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285280)) 8 (ELit 144320);
   KWord (SA (ELit 0) (1285296)) 1 (ELit 96);
   KWord (SA (ELit 0) (1285296)) 8 (ELit 96);
   KWord (SA (ELit 0) (1285336)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285344)) 8 (ELit 144416);
   KWord (SA (ELit 0) (1285360)) 1 (ELit 128);
   KWord (SA (ELit 0) (1285360)) 8 (ELit 128);
   KWord (SA (ELit 0) (1285400)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285408)) 8 (ELit 144544);
   KWord (SA (ELit 0) (1285424)) 1 (ELit 96);
   KWord (SA (ELit 0) (1285424)) 8 (ELit 96);
   KWord (SA (ELit 0) (1285464)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285472)) 8 (ELit 144640);
   KWord (SA (ELit 0) (1285488)) 1 (ELit 64);
   KWord (SA (ELit 0) (1285488)) 8 (ELit 64);
   KWord (SA (ELit 0) (1285528)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285536)) 8 (ELit 144704);
   KWord (SA (ELit 0) (1285552)) 1 (ELit 64);
   KWord (SA (ELit 0) (1285552)) 8 (ELit 64);
   KWord (SA (ELit 0) (1285592)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285600)) 8 (ELit 144768);
   KWord (SA (ELit 0) (1285616)) 1 (ELit 64);
   KWord (SA (ELit 0) (1285616)) 8 (ELit 64);
   KWord (SA (ELit 0) (1285656)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285664)) 8 (ELit 144832);
   KWord (SA (ELit 0) (1285680)) 1 (ELit 64);
   KWord (SA (ELit 0) (1285680)) 8 (ELit 64);
   KWord (SA (ELit 0) (1285720)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285728)) 8 (ELit 144896);
   KWord (SA (ELit 0) (1285744)) 1 (ELit 64);
   KWord (SA (ELit 0) (1285744)) 8 (ELit 64);
   KWord (SA (ELit 0) (1285784)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285792)) 8 (ELit 144960);
   KWord (SA (ELit 0) (1285808)) 1 (ELit 64);
   KWord (SA (ELit 0) (1285808)) 8 (ELit 64);
   KWord (SA (ELit 0) (1285848)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285856)) 8 (ELit 145024);
   KWord (SA (ELit 0) (1285872)) 1 (ELit 64);
   KWord (SA (ELit 0) (1285872)) 8 (ELit 64);
   KWord (SA (ELit 0) (1285912)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285920)) 8 (ELit 145088);
   KWord (SA (ELit 0) (1285936)) 1 (ELit 96);
   KWord (SA (ELit 0) (1285936)) 8 (ELit 96);
   KWord (SA (ELit 0) (1285976)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1285984)) 8 (ELit 145184);
   KWord (SA (ELit 0) (1286000)) 1 (ELit 64);
   KWord (SA (ELit 0) (1286000)) 8 (ELit 64);
   KWord (SA (ELit 0) (1286040)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1286048)) 8 (ELit 145504);
   KWord (SA (ELit 0) (1286064)) 1 (ELit 96);
   KWord (SA (ELit 0) (1286064)) 8 (ELit 96);
   KWord (SA (ELit 0) (1286104)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1286112)) 8 (ELit 145600);
   KWord (SA (ELit 0) (1286128)) 1 (ELit 32);
   KWord (SA (ELit 0) (1286128)) 8 (ELit 32);
   KWord (SA (ELit 0) (1286168)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1286176)) 8 (ELit 145632);
   KWord (SA (ELit 0) (1286192)) 1 (ELit 32);
   KWord (SA (ELit 0) (1286192)) 8 (ELit 32);
   KWord (SA (ELit 0) (1286232)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1286240)) 8 (ELit 145664);
   KWord (SA (ELit 0) (1286256)) 1 (ELit 96);
   KWord (SA (ELit 0) (1286256)) 8 (ELit 96);
   KWord (SA (ELit 0) (1286296)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1286304)) 8 (ELit 1242944);
   KWord (SA (ELit 0) (1286320)) 1 (ELit 160);
   KWord (SA (ELit 0) (1286320)) 8 (ELit 160);
   KWord (SA (ELit 0) (1286360)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (6889608)) 8 (ELit 0);
   KWord (SA (ELit 0) (1284776)) 8 (ELit 1284544);
   KWord (SA (ELit 0) (1284684)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1284584)) 8 (ELit 0);
   KWord (SA (ELit 0) (1284600)) 8 (ELit 0);
   KWord (SA (ELit 0) (1284552)) 8 (ELit 0);
   KWord (SA (ELit 0) (1284560)) 8 (ELit 0);
   KWord (SA (ELit 0) (1284536)) 8 (ELit 1284304);
   KWord (SA (ELit 0) (1284444)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1284344)) 8 (ELit 6889636);
   KWord (SA (ELit 0) (1284360)) 8 (ELit 6889632);
   KWord (SA (ELit 0) (1284376)) 8 (ELit 1170468);
   KWord (SA (ELit 0) (6887616)) 8 (EVar 40);
   KWord (SA (ELit 0) (1284424)) 4 (ELit 1)].
Definition ss0 : sym_state := SS 1139404 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-320), ELit 320); (ELit 0, (1286400), ELit 8); (ELit 0, (1286480), ELit 1); (ELit 0, (1290352), ELit 8); (ELit 0, (6887632), ELit 1); (ELit 0, (6887640), ELit 4); (ELit 0, (6887648), ELit 8); (ELit 0, (6888176), ELit 4); (ELit 0, (2147468852), ELit 1); (ELit 0, (2147468853), ELit 1); (ELit 0, (2147468854), ELit 1); (ELit 0, (2147468855), ELit 1); (ELit 0, (2147468864), ELit 1); (ELit 0, (2147468865), ELit 1); (ELit 0, (2147468866), ELit 1); (ELit 0, (2147468867), ELit 1); (ELit 0, (2147468868), ELit 1); (ELit 0, (2147468868), ELit 4); (ELit 0, (2147468869), ELit 1); (ELit 0, (2147468870), ELit 1); (ELit 0, (2147468871), ELit 1); (ELit 0, (2147468872), ELit 4); (ELit 0, (2147468876), ELit 1); (ELit 0, (2147468876), ELit 4); (ELit 0, (2147468877), ELit 1); (ELit 0, (2147468878), ELit 1); (ELit 0, (2147468879), ELit 1); (ELit 0, (2147468892), ELit 1); (ELit 0, (2147468893), ELit 1); (ELit 0, (2147468894), ELit 1); (ELit 0, (2147468895), ELit 1); (ELit 0, (2147468896), ELit 1); (ELit 0, (2147468897), ELit 1); (ELit 0, (2147468898), ELit 1); (ELit 0, (2147468899), ELit 1); (ELit 0, (2147468900), ELit 1); (ELit 0, (2147468901), ELit 1); (ELit 0, (2147468902), ELit 1); (ELit 0, (2147468903), ELit 1); (ELit 0, (2147468904), ELit 1); (ELit 0, (2147468905), ELit 1); (ELit 0, (2147468906), ELit 1); (ELit 0, (2147468907), ELit 1); (ELit 0, (2147468908), ELit 1); (ELit 0, (2147468908), ELit 4); (ELit 0, (2147468909), ELit 1); (ELit 0, (2147468910), ELit 1); (ELit 0, (2147468911), ELit 1); (ELit 0, (2147468912), ELit 4); (ELit 0, (2147468916), ELit 1); (ELit 0, (2147468916), ELit 4); (ELit 0, (2147468917), ELit 1); (ELit 0, (2147468918), ELit 1); (ELit 0, (2147468919), ELit 1); (ELit 0, (2147468920), ELit 1); (ELit 0, (2147468920), ELit 4); (ELit 0, (2147468921), ELit 1); (ELit 0, (2147468922), ELit 1); (ELit 0, (2147468923), ELit 1); (ELit 0, (2147468924), ELit 4); (ELit 0, (2147468928), ELit 1); (ELit 0, (2147468928), ELit 4); (ELit 0, (2147468929), ELit 1); (ELit 0, (2147468930), ELit 1); (ELit 0, (2147468931), ELit 1); (ELit 0, (2147468932), ELit 1); (ELit 0, (2147468932), ELit 4); (ELit 0, (2147468933), ELit 1); (ELit 0, (2147468934), ELit 1); (ELit 0, (2147468935), ELit 1); (ELit 0, (2147468936), ELit 4); (ELit 0, (2147468940), ELit 4); (ELit 0, (2147468944), ELit 1); (ELit 0, (2147468944), ELit 4); (ELit 0, (2147468945), ELit 1); (ELit 0, (2147468946), ELit 1); (ELit 0, (2147468947), ELit 1); (ELit 0, (2147468948), ELit 1); (ELit 0, (2147468948), ELit 4); (ELit 0, (2147468949), ELit 1); (ELit 0, (2147468950), ELit 1); (ELit 0, (2147468951), ELit 1); (ELit 0, (2147468952), ELit 4); (ELit 0, (2147468956), ELit 1); (ELit 0, (2147468956), ELit 4); (ELit 0, (2147468957), ELit 1); (ELit 0, (2147468958), ELit 1); (ELit 0, (2147468959), ELit 1); (ELit 0, (2147468960), ELit 1); (ELit 0, (2147468961), ELit 1); (ELit 0, (2147468962), ELit 1); (ELit 0, (2147468963), ELit 1); (ELit 0, (2147468964), ELit 1); (ELit 0, (2147468965), ELit 1); (ELit 0, (2147468966), ELit 1); (ELit 0, (2147468967), ELit 1); (ELit 0, (2147468968), ELit 1); (ELit 0, (2147468969), ELit 1); (ELit 0, (2147468970), ELit 1); (ELit 0, (2147468971), ELit 1); (ELit 0, (2147468972), ELit 1); (ELit 0, (2147468973), ELit 1); (ELit 0, (2147468974), ELit 1); (ELit 0, (2147468975), ELit 1); (ELit 0, (2147468976), ELit 1); (ELit 0, (2147468977), ELit 1); (ELit 0, (2147468978), ELit 1); (ELit 0, (2147468979), ELit 1); (ELit 0, (2147468980), ELit 1); (ELit 0, (2147468981), ELit 1); (ELit 0, (2147468982), ELit 1); (ELit 0, (2147468983), ELit 1); (ELit 0, (2147468984), ELit 1); (ELit 0, (2147468985), ELit 1); (ELit 0, (2147468986), ELit 1); (ELit 0, (2147468987), ELit 1); (ELit 0, (2147468988), ELit 1); (ELit 0, (2147468989), ELit 1); (ELit 0, (2147468990), ELit 1); (ELit 0, (2147468991), ELit 1); (ELit 0, (2147468992), ELit 1); (ELit 0, (2147468993), ELit 1); (ELit 0, (2147468994), ELit 1); (ELit 0, (2147468995), ELit 1); (ELit 0, (2147468996), ELit 1); (ELit 0, (2147468997), ELit 1); (ELit 0, (2147468998), ELit 1); (ELit 0, (2147468999), ELit 1); (ELit 0, (2147469000), ELit 1); (ELit 0, (2147469001), ELit 1); (ELit 0, (2147469002), ELit 1); (ELit 0, (2147469003), ELit 1); (ELit 0, (2147469004), ELit 1); (ELit 0, (2147469005), ELit 1); (ELit 0, (2147469006), ELit 1); (ELit 0, (2147469007), ELit 1); (ELit 0, (2147469008), ELit 1); (ELit 0, (2147469009), ELit 1); (ELit 0, (2147469010), ELit 1); (ELit 0, (2147469011), ELit 1); (ELit 0, (2147469012), ELit 1); (ELit 0, (2147469013), ELit 1); (ELit 0, (2147469014), ELit 1); (ELit 0, (2147469015), ELit 1); (ELit 0, (2147469016), ELit 1); (ELit 0, (2147469016), ELit 4); (ELit 0, (2147469017), ELit 1); (ELit 0, (2147469018), ELit 1); (ELit 0, (2147469019), ELit 1); (ELit 0, (2147469020), ELit 4); (ELit 0, (2147469024), ELit 1); (ELit 0, (2147469024), ELit 4); (ELit 0, (2147469025), ELit 1); (ELit 0, (2147469026), ELit 1); (ELit 0, (2147469027), ELit 1); (ELit 0, (2147469028), ELit 1); (ELit 0, (2147469029), ELit 1); (ELit 0, (2147469030), ELit 1); (ELit 0, (2147469031), ELit 1); (ELit 0, (2147469032), ELit 1); (ELit 0, (2147469033), ELit 1); (ELit 0, (2147469034), ELit 1); (ELit 0, (2147469035), ELit 1); (ELit 0, (2147469068), ELit 1); (ELit 0, (2147469068), ELit 4); (ELit 0, (2147469069), ELit 1); (ELit 0, (2147469070), ELit 1); (ELit 0, (2147469071), ELit 1); (ELit 0, (2147469072), ELit 4); (ELit 0, (2147469076), ELit 1); (ELit 0, (2147469076), ELit 4); (ELit 0, (2147469077), ELit 1); (ELit 0, (2147469078), ELit 1); (ELit 0, (2147469079), ELit 1); (ELit 0, (2147469080), ELit 1); (ELit 0, (2147469081), ELit 1); (ELit 0, (2147469082), ELit 1); (ELit 0, (2147469083), ELit 1); (ELit 0, (2147469084), ELit 1); (ELit 0, (2147469085), ELit 1); (ELit 0, (2147469086), ELit 1); (ELit 0, (2147469087), ELit 1); (ELit 0, (2147469088), ELit 1); (ELit 0, (2147469088), ELit 4); (ELit 0, (2147469089), ELit 1); (ELit 0, (2147469090), ELit 1); (ELit 0, (2147469091), ELit 1); (ELit 0, (2147469092), ELit 4); (ELit 0, (2147469096), ELit 1); (ELit 0, (2147469096), ELit 4); (ELit 0, (2147469097), ELit 1); (ELit 0, (2147469098), ELit 1); (ELit 0, (2147469099), ELit 1); (ELit 0, (2147606248), ELit 1); (ELit 0, (2147606248), ELit 4); (ELit 0, (2147606249), ELit 1); (ELit 0, (2147606250), ELit 1); (ELit 0, (2147606251), ELit 1); (ELit 0, (2147606252), ELit 4); (ELit 0, (2147606256), ELit 4); (ELit 0, (2147606260), ELit 4); (ELit 0, (2147606264), ELit 1); (ELit 0, (2147606264), ELit 4); (ELit 0, (2147606265), ELit 1); (ELit 0, (2147606266), ELit 1); (ELit 0, (2147606267), ELit 1); (ELit 0, (2147611484), ELit 1); (ELit 0, (2147611484), ELit 4); (ELit 0, (2147611485), ELit 1); (ELit 0, (2147611486), ELit 1); (ELit 0, (2147611487), ELit 1); (ELit 0, (2147611488), ELit 4); (ELit 0, (2147611492), ELit 4); (ELit 0, (2147611496), ELit 4); (ELit 0, (2147611500), ELit 4); (ELit 0, (2147611504), ELit 4); (ELit 0, (2147611508), ELit 4); (ELit 0, (2147611512), ELit 8); (ELit 0, (2147611520), ELit 8); (ELit 0, (2147611528), ELit 8); (ELit 0, (2147611536), ELit 8); (ELit 0, (2147611544), ELit 8); (ELit 0, (2147611552), ELit 8); (ELit 0, (2147611560), ELit 8); (ELit 0, (2147611568), ELit 8); (ELit 0, (2147611576), ELit 8); (ELit 0, (2147611584), ELit 8); (ELit 0, (2147611592), ELit 8); (ELit 0, (2147611600), ELit 8); (ELit 0, (2147611608), ELit 8); (ELit 0, (2147611616), ELit 8); (ELit 0, (2147611624), ELit 8); (ELit 0, (2147611632), ELit 8); (ELit 0, (2147611640), ELit 8); (ELit 0, (2147611648), ELit 4); (ELit 0, (2147611648), ELit 8); (ELit 0, (2147611652), ELit 4); (ELit 0, (2147611656), ELit 4); (ELit 0, (2147611656), ELit 8); (ELit 0, (2147611660), ELit 4); (ELit 0, (2147611664), ELit 4); (ELit 0, (2147611664), ELit 8); (ELit 0, (2147611668), ELit 4); (ELit 0, (2147611672), ELit 1); (ELit 0, (2147611672), ELit 4); (ELit 0, (2147611673), ELit 1); (ELit 0, (2147611674), ELit 1); (ELit 0, (2147611675), ELit 1)].
Definition F0L : list SR.region := [(EVar 2, (-320), 320); (ELit 0, (1286400), 8); (ELit 0, (1286480), 1); (ELit 0, (1290352), 8); (ELit 0, (6887632), 1); (ELit 0, (6887640), 4); (ELit 0, (6887648), 8); (ELit 0, (6888176), 4); (ELit 0, (2147468852), 1); (ELit 0, (2147468853), 1); (ELit 0, (2147468854), 1); (ELit 0, (2147468855), 1); (ELit 0, (2147468864), 1); (ELit 0, (2147468865), 1); (ELit 0, (2147468866), 1); (ELit 0, (2147468867), 1); (ELit 0, (2147468868), 1); (ELit 0, (2147468868), 4); (ELit 0, (2147468869), 1); (ELit 0, (2147468870), 1); (ELit 0, (2147468871), 1); (ELit 0, (2147468872), 4); (ELit 0, (2147468876), 1); (ELit 0, (2147468876), 4); (ELit 0, (2147468877), 1); (ELit 0, (2147468878), 1); (ELit 0, (2147468879), 1); (ELit 0, (2147468892), 1); (ELit 0, (2147468893), 1); (ELit 0, (2147468894), 1); (ELit 0, (2147468895), 1); (ELit 0, (2147468896), 1); (ELit 0, (2147468897), 1); (ELit 0, (2147468898), 1); (ELit 0, (2147468899), 1); (ELit 0, (2147468900), 1); (ELit 0, (2147468901), 1); (ELit 0, (2147468902), 1); (ELit 0, (2147468903), 1); (ELit 0, (2147468904), 1); (ELit 0, (2147468905), 1); (ELit 0, (2147468906), 1); (ELit 0, (2147468907), 1); (ELit 0, (2147468908), 1); (ELit 0, (2147468908), 4); (ELit 0, (2147468909), 1); (ELit 0, (2147468910), 1); (ELit 0, (2147468911), 1); (ELit 0, (2147468912), 4); (ELit 0, (2147468916), 1); (ELit 0, (2147468916), 4); (ELit 0, (2147468917), 1); (ELit 0, (2147468918), 1); (ELit 0, (2147468919), 1); (ELit 0, (2147468920), 1); (ELit 0, (2147468920), 4); (ELit 0, (2147468921), 1); (ELit 0, (2147468922), 1); (ELit 0, (2147468923), 1); (ELit 0, (2147468924), 4); (ELit 0, (2147468928), 1); (ELit 0, (2147468928), 4); (ELit 0, (2147468929), 1); (ELit 0, (2147468930), 1); (ELit 0, (2147468931), 1); (ELit 0, (2147468932), 1); (ELit 0, (2147468932), 4); (ELit 0, (2147468933), 1); (ELit 0, (2147468934), 1); (ELit 0, (2147468935), 1); (ELit 0, (2147468936), 4); (ELit 0, (2147468940), 4); (ELit 0, (2147468944), 1); (ELit 0, (2147468944), 4); (ELit 0, (2147468945), 1); (ELit 0, (2147468946), 1); (ELit 0, (2147468947), 1); (ELit 0, (2147468948), 1); (ELit 0, (2147468948), 4); (ELit 0, (2147468949), 1); (ELit 0, (2147468950), 1); (ELit 0, (2147468951), 1); (ELit 0, (2147468952), 4); (ELit 0, (2147468956), 1); (ELit 0, (2147468956), 4); (ELit 0, (2147468957), 1); (ELit 0, (2147468958), 1); (ELit 0, (2147468959), 1); (ELit 0, (2147468960), 1); (ELit 0, (2147468961), 1); (ELit 0, (2147468962), 1); (ELit 0, (2147468963), 1); (ELit 0, (2147468964), 1); (ELit 0, (2147468965), 1); (ELit 0, (2147468966), 1); (ELit 0, (2147468967), 1); (ELit 0, (2147468968), 1); (ELit 0, (2147468969), 1); (ELit 0, (2147468970), 1); (ELit 0, (2147468971), 1); (ELit 0, (2147468972), 1); (ELit 0, (2147468973), 1); (ELit 0, (2147468974), 1); (ELit 0, (2147468975), 1); (ELit 0, (2147468976), 1); (ELit 0, (2147468977), 1); (ELit 0, (2147468978), 1); (ELit 0, (2147468979), 1); (ELit 0, (2147468980), 1); (ELit 0, (2147468981), 1); (ELit 0, (2147468982), 1); (ELit 0, (2147468983), 1); (ELit 0, (2147468984), 1); (ELit 0, (2147468985), 1); (ELit 0, (2147468986), 1); (ELit 0, (2147468987), 1); (ELit 0, (2147468988), 1); (ELit 0, (2147468989), 1); (ELit 0, (2147468990), 1); (ELit 0, (2147468991), 1); (ELit 0, (2147468992), 1); (ELit 0, (2147468993), 1); (ELit 0, (2147468994), 1); (ELit 0, (2147468995), 1); (ELit 0, (2147468996), 1); (ELit 0, (2147468997), 1); (ELit 0, (2147468998), 1); (ELit 0, (2147468999), 1); (ELit 0, (2147469000), 1); (ELit 0, (2147469001), 1); (ELit 0, (2147469002), 1); (ELit 0, (2147469003), 1); (ELit 0, (2147469004), 1); (ELit 0, (2147469005), 1); (ELit 0, (2147469006), 1); (ELit 0, (2147469007), 1); (ELit 0, (2147469008), 1); (ELit 0, (2147469009), 1); (ELit 0, (2147469010), 1); (ELit 0, (2147469011), 1); (ELit 0, (2147469012), 1); (ELit 0, (2147469013), 1); (ELit 0, (2147469014), 1); (ELit 0, (2147469015), 1); (ELit 0, (2147469016), 1); (ELit 0, (2147469016), 4); (ELit 0, (2147469017), 1); (ELit 0, (2147469018), 1); (ELit 0, (2147469019), 1); (ELit 0, (2147469020), 4); (ELit 0, (2147469024), 1); (ELit 0, (2147469024), 4); (ELit 0, (2147469025), 1); (ELit 0, (2147469026), 1); (ELit 0, (2147469027), 1); (ELit 0, (2147469028), 1); (ELit 0, (2147469029), 1); (ELit 0, (2147469030), 1); (ELit 0, (2147469031), 1); (ELit 0, (2147469032), 1); (ELit 0, (2147469033), 1); (ELit 0, (2147469034), 1); (ELit 0, (2147469035), 1); (ELit 0, (2147469068), 1); (ELit 0, (2147469068), 4); (ELit 0, (2147469069), 1); (ELit 0, (2147469070), 1); (ELit 0, (2147469071), 1); (ELit 0, (2147469072), 4); (ELit 0, (2147469076), 1); (ELit 0, (2147469076), 4); (ELit 0, (2147469077), 1); (ELit 0, (2147469078), 1); (ELit 0, (2147469079), 1); (ELit 0, (2147469080), 1); (ELit 0, (2147469081), 1); (ELit 0, (2147469082), 1); (ELit 0, (2147469083), 1); (ELit 0, (2147469084), 1); (ELit 0, (2147469085), 1); (ELit 0, (2147469086), 1); (ELit 0, (2147469087), 1); (ELit 0, (2147469088), 1); (ELit 0, (2147469088), 4); (ELit 0, (2147469089), 1); (ELit 0, (2147469090), 1); (ELit 0, (2147469091), 1); (ELit 0, (2147469092), 4); (ELit 0, (2147469096), 1); (ELit 0, (2147469096), 4); (ELit 0, (2147469097), 1); (ELit 0, (2147469098), 1); (ELit 0, (2147469099), 1); (ELit 0, (2147606248), 1); (ELit 0, (2147606248), 4); (ELit 0, (2147606249), 1); (ELit 0, (2147606250), 1); (ELit 0, (2147606251), 1); (ELit 0, (2147606252), 4); (ELit 0, (2147606256), 4); (ELit 0, (2147606260), 4); (ELit 0, (2147606264), 1); (ELit 0, (2147606264), 4); (ELit 0, (2147606265), 1); (ELit 0, (2147606266), 1); (ELit 0, (2147606267), 1); (ELit 0, (2147611484), 1); (ELit 0, (2147611484), 4); (ELit 0, (2147611485), 1); (ELit 0, (2147611486), 1); (ELit 0, (2147611487), 1); (ELit 0, (2147611488), 4); (ELit 0, (2147611492), 4); (ELit 0, (2147611496), 4); (ELit 0, (2147611500), 4); (ELit 0, (2147611504), 4); (ELit 0, (2147611508), 4); (ELit 0, (2147611512), 8); (ELit 0, (2147611520), 8); (ELit 0, (2147611528), 8); (ELit 0, (2147611536), 8); (ELit 0, (2147611544), 8); (ELit 0, (2147611552), 8); (ELit 0, (2147611560), 8); (ELit 0, (2147611568), 8); (ELit 0, (2147611576), 8); (ELit 0, (2147611584), 8); (ELit 0, (2147611592), 8); (ELit 0, (2147611600), 8); (ELit 0, (2147611608), 8); (ELit 0, (2147611616), 8); (ELit 0, (2147611624), 8); (ELit 0, (2147611632), 8); (ELit 0, (2147611640), 8); (ELit 0, (2147611648), 4); (ELit 0, (2147611648), 8); (ELit 0, (2147611652), 4); (ELit 0, (2147611656), 4); (ELit 0, (2147611656), 8); (ELit 0, (2147611660), 4); (ELit 0, (2147611664), 4); (ELit 0, (2147611664), 8); (ELit 0, (2147611668), 4); (ELit 0, (2147611672), 1); (ELit 0, (2147611672), 4); (ELit 0, (2147611673), 1); (ELit 0, (2147611674), 1); (ELit 0, (2147611675), 1)].
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
Definition ex1 : list SGA.aitem * (Z * sym_state) :=
  (([SGA.AStep (SR.SBlock [1170604; 1170604])], (93, SS 1170604 [ELit 0; ELit 1172148; EAlu Instr.ALU_ADD (EVar 2) (ELit (-144)); EVar 3; ELit 6756480; ELit 0; ELit 1152921504606846976; ELit 0; ELit 0; ELit 1284304; ELit 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-136)); ELit 2; ELit 4; ELit 17293822569102704639; ELit 1152920405095219200; ELit 18446742974197923840; ELit 66; ELit 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-136)); EVar 20; ELit 6887616; ELit 4; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; ELit 1290288; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 4); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 6889632); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 1284304); KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 1172148); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -24 |} 8 (ELit 1139512); KWord {| a_base := ELit 0; a_off := 1286400 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1290352 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611664 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611656 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611648 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611640 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611632 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611624 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611616 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611608 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611600 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611592 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611584 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611576 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611568 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611560 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611552 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611544 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611536 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611528 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611520 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611512 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611508 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611504 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611500 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611496 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611492 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611488 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611672 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147611484 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -312 |} 8 (ELit 2305843009213693952); KWord {| a_base := EVar 2; a_off := -304 |} 8 (ELit 1286368); KWord {| a_base := EVar 2; a_off := -296 |} 8 (ELit 116958); KWord {| a_base := EVar 2; a_off := -288 |} 8 (ELit 2); KWord {| a_base := EVar 2; a_off := -280 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -272 |} 8 (ELit 2305843009213693952); KWord {| a_base := EVar 2; a_off := -264 |} 8 (ELit 396528); KWord {| a_base := ELit 0; a_off := 2147606260 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147606256 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147606252 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147606264 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147606248 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469092 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469088 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469096 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469086 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469085 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469087 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469084 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469082 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469081 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469083 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469080 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469072 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469068 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469076 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469032 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469031 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469034 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469033 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469030 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469029 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469035 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469028 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469020 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469016 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469024 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469012 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469011 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469014 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469013 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469010 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469009 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469015 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469008 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469004 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469003 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469006 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469005 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469002 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469001 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469007 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469000 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468996 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468995 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468998 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468997 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468994 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468993 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468999 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468992 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468988 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468987 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468990 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468989 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468986 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468985 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468991 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468984 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468980 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468979 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468982 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468981 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468978 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468977 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468983 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468976 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468972 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468971 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468974 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468973 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468970 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468969 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468975 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468968 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468964 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468963 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468966 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468965 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468962 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468961 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468967 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468960 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468952 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468948 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468956 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468940 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468936 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468944 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468932 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468924 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468920 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468928 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468912 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468908 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468916 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468906 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468905 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468907 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468904 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468900 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468899 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468902 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468901 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468898 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468897 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468903 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468896 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468894 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468893 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468895 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468892 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468872 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468868 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468876 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468866 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468865 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468867 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468864 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468854 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468853 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468855 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468852 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -208 |} 8 (ELit 1888864); KWord {| a_base := EVar 2; a_off := -216 |} 8 (ELit 1303712); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 1303728); KWord {| a_base := EVar 2; a_off := -192 |} 8 (ELit 1303720); KWord {| a_base := EVar 2; a_off := -232 |} 8 (ELit 24); KWord {| a_base := EVar 2; a_off := -240 |} 8 (ELit 1290288); KWord {| a_base := EVar 2; a_off := -248 |} 8 (ELit 1290360); KWord {| a_base := EVar 2; a_off := -224 |} 8 (ELit 1284832); KWord {| a_base := EVar 2; a_off := -184 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 22); KWord {| a_base := ELit 0; a_off := 1286480 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6887632 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6887648 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6887640 |} 4 (ELit 32); KWord {| a_base := ELit 0; a_off := 6888176 |} 4 (EVar 44); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 1137416); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -320 |} (ELit 320); KUnk {| a_base := EVar 2; a_off := -320 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -256 |} (ELit 8); KImg 65536 1269760; KWr {| a_base := ELit 0; a_off := 1286400 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1286480 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 1290352 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 6887632 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 6887640 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 6887648 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 6888176 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468852 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468853 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468854 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468855 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468864 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468865 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468866 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468867 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468868 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468868 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468869 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468870 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468871 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468872 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468876 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468876 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468877 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468878 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468879 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468892 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468893 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468894 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468895 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468896 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468897 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468898 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468899 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468900 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468901 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468902 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468903 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468904 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468905 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468906 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468907 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468908 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468908 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468909 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468910 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468911 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468912 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468916 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468916 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468917 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468918 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468919 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468920 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468920 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468921 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468922 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468923 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468924 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468928 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468928 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468929 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468930 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468931 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468932 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468932 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468933 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468934 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468935 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468936 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468940 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468944 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468944 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468945 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468946 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468947 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468948 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468948 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468949 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468950 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468951 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468952 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468956 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468956 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468957 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468958 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468959 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468960 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468961 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468962 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468963 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468964 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468965 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468966 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468967 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468968 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468969 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468970 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468971 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468972 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468973 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468974 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468975 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468976 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468977 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468978 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468979 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468980 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468981 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468982 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468983 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468984 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468985 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468986 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468987 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468988 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468989 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468990 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468991 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468992 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468993 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468994 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468995 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468996 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468997 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468998 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468999 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469000 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469001 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469002 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469003 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469004 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469005 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469006 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469007 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469008 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469009 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469010 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469011 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469012 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469013 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469014 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469015 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469016 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469016 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469017 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469018 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469019 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469020 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469024 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469024 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469025 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469026 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469027 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469028 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469029 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469030 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469031 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469032 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469033 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469034 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469035 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469068 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469068 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469069 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469070 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469071 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469072 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469076 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469076 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469077 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469078 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469079 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469080 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469081 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469082 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469083 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469084 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469085 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469086 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469087 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469088 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469088 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469089 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469090 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469091 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469092 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469096 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469096 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469097 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469098 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469099 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147606248 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147606248 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147606249 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147606250 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147606251 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147606252 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147606256 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147606260 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147606264 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147606264 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147606265 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147606266 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147606267 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147611484 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147611484 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611485 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147611486 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147611487 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147611488 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611492 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611496 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611500 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611504 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611508 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611512 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611520 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611528 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611536 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611544 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611552 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611560 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611568 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611576 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611584 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611592 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611600 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611608 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611616 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611624 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611632 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611640 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611648 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611648 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611652 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611656 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611656 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611660 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611664 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611664 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147611668 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611672 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147611672 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147611673 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147611674 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147611675 |} (ELit 1); KWord {| a_base := ELit 0; a_off := 6756312 |} 4 (EVar 44); KRange (EVar 44) 1 4194303; KWord {| a_base := ELit 0; a_off := 6888211 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6887720 |} 8 (ELit 448212); KWord {| a_base := ELit 0; a_off := 6887976 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6887636 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 1290196 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6887712 |} 8 (ELit 863096); KWord {| a_base := ELit 0; a_off := 6887968 |} 8 (ELit 1283856); KWord {| a_base := ELit 0; a_off := 6887704 |} 8 (ELit 448212); KWord {| a_base := ELit 0; a_off := 6887960 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6887696 |} 8 (ELit 864528); KWord {| a_base := ELit 0; a_off := 6887952 |} 8 (ELit 6749800); KWord {| a_base := ELit 0; a_off := 6749800 |} 1 (ELit 6); KWord {| a_base := ELit 0; a_off := 6887688 |} 8 (ELit 448212); KWord {| a_base := ELit 0; a_off := 6887944 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6887680 |} 8 (ELit 864528); KWord {| a_base := ELit 0; a_off := 6887936 |} 8 (ELit 6749768); KWord {| a_base := ELit 0; a_off := 6749768 |} 1 (ELit 16); KWord {| a_base := ELit 0; a_off := 6887672 |} 8 (ELit 1139320); KWord {| a_base := ELit 0; a_off := 6887928 |} 8 (ELit 686948); KWord {| a_base := ELit 0; a_off := 6749716 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6887664 |} 8 (ELit 1139320); KWord {| a_base := ELit 0; a_off := 6887920 |} 8 (ELit 618908); KWord {| a_base := ELit 0; a_off := 1898080 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6887656 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1273320 |} 8 (ELit 1273320); KWord {| a_base := ELit 0; a_off := 1290192 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 1303704 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1300408 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1284832 |} 8 (ELit 143776); KWord {| a_base := ELit 0; a_off := 1284848 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1298460 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1284848 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1897312 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1273832 |} 8 (ELit 1210200); KWord {| a_base := ELit 0; a_off := 1284888 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1284896 |} 8 (ELit 143872); KWord {| a_base := ELit 0; a_off := 1284912 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1284912 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1284952 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1284960 |} 8 (ELit 143904); KWord {| a_base := ELit 0; a_off := 1284976 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1284976 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1285016 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285024 |} 8 (ELit 144096); KWord {| a_base := ELit 0; a_off := 1285040 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1285040 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1285080 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285088 |} 8 (ELit 144128); KWord {| a_base := ELit 0; a_off := 1285104 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285104 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285144 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285152 |} 8 (ELit 144192); KWord {| a_base := ELit 0; a_off := 1285168 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1285168 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1285208 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285216 |} 8 (ELit 144224); KWord {| a_base := ELit 0; a_off := 1285232 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1285232 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1285272 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285280 |} 8 (ELit 144320); KWord {| a_base := ELit 0; a_off := 1285296 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1285296 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1285336 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285344 |} 8 (ELit 144416); KWord {| a_base := ELit 0; a_off := 1285360 |} 1 (ELit 128); KWord {| a_base := ELit 0; a_off := 1285360 |} 8 (ELit 128); KWord {| a_base := ELit 0; a_off := 1285400 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285408 |} 8 (ELit 144544); KWord {| a_base := ELit 0; a_off := 1285424 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1285424 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1285464 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285472 |} 8 (ELit 144640); KWord {| a_base := ELit 0; a_off := 1285488 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285488 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285528 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285536 |} 8 (ELit 144704); KWord {| a_base := ELit 0; a_off := 1285552 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285552 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285592 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285600 |} 8 (ELit 144768); KWord {| a_base := ELit 0; a_off := 1285616 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285616 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285656 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285664 |} 8 (ELit 144832); KWord {| a_base := ELit 0; a_off := 1285680 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285680 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285720 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285728 |} 8 (ELit 144896); KWord {| a_base := ELit 0; a_off := 1285744 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285744 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285784 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285792 |} 8 (ELit 144960); KWord {| a_base := ELit 0; a_off := 1285808 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285808 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285848 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285856 |} 8 (ELit 145024); KWord {| a_base := ELit 0; a_off := 1285872 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285872 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1285912 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285920 |} 8 (ELit 145088); KWord {| a_base := ELit 0; a_off := 1285936 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1285936 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1285976 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1285984 |} 8 (ELit 145184); KWord {| a_base := ELit 0; a_off := 1286000 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1286000 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1286040 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1286048 |} 8 (ELit 145504); KWord {| a_base := ELit 0; a_off := 1286064 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1286064 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1286104 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1286112 |} 8 (ELit 145600); KWord {| a_base := ELit 0; a_off := 1286128 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1286128 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1286168 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1286176 |} 8 (ELit 145632); KWord {| a_base := ELit 0; a_off := 1286192 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1286192 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1286232 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1286240 |} 8 (ELit 145664); KWord {| a_base := ELit 0; a_off := 1286256 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1286256 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1286296 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1286304 |} 8 (ELit 1242944); KWord {| a_base := ELit 0; a_off := 1286320 |} 1 (ELit 160); KWord {| a_base := ELit 0; a_off := 1286320 |} 8 (ELit 160); KWord {| a_base := ELit 0; a_off := 1286360 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6889608 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1284776 |} 8 (ELit 1284544); KWord {| a_base := ELit 0; a_off := 1284684 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1284584 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1284600 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1284552 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1284560 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1284536 |} 8 (ELit 1284304); KWord {| a_base := ELit 0; a_off := 1284444 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1284344 |} 8 (ELit 6889636); KWord {| a_base := ELit 0; a_off := 1284360 |} 8 (ELit 6889632); KWord {| a_base := ELit 0; a_off := 1284376 |} 8 (ELit 1170468); KWord {| a_base := ELit 0; a_off := 6887616 |} 8 (EVar 40); KWord {| a_base := ELit 0; a_off := 1284424 |} 4 (ELit 1)] 56))).
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
Definition ps0 : SR.post_spec := SR.PS 1170604 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_cc72f4.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1139404 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_cc72f4.IT SegItab_Ba_cc72f4.IT_sound BF NX0 BR XSTEP F0 PSS plan 1139404 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
