(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto SegPlanJoin. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b Ba0PlanKitIt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require SegItab_Ba_cc72f4_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require SegPlanFast.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := SegItab_Ba_cc72f4_b.ITR.
Definition IT : itab := SegItab_Ba_cc72f4_b.IT.
Definition ENDS : list Z := [1180248].
Definition STOPS1 : list Z := [1180248] ++ ENDS.
Definition NX0 : nat := 56.
Definition v0 (k : Z) : expr := EAlu Instr.ALU_ADD (EVar 0) (ELit k).
Definition L : expr := EVar 4.
Definition regs0 : list expr := [ELit 0; ELit 1147060; EVar 2; EVar 3; ELit 6765824; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition kn0 : list kentry := [KRange (EVar 2) 140735332552704 140737488355328;
   KAlign (EVar 2) 16;
   KWr (SA (EVar 2) (-320)) (ELit 320);
   KUnk (SA (EVar 2) (-320)) (ELit 320);
   KImg 65536 1282048;
   KWr (SA (ELit 0) (1295744)) (ELit 8);
   KWr (SA (ELit 0) (1295824)) (ELit 1);
   KWr (SA (ELit 0) (1299696)) (ELit 8);
   KWr (SA (ELit 0) (6896976)) (ELit 1);
   KWr (SA (ELit 0) (6896984)) (ELit 4);
   KWr (SA (ELit 0) (6896992)) (ELit 8);
   KWr (SA (ELit 0) (6897520)) (ELit 4);
   KWr (SA (ELit 0) (2147468856)) (ELit 1);
   KWr (SA (ELit 0) (2147468857)) (ELit 1);
   KWr (SA (ELit 0) (2147468858)) (ELit 1);
   KWr (SA (ELit 0) (2147468859)) (ELit 1);
   KWr (SA (ELit 0) (2147468868)) (ELit 1);
   KWr (SA (ELit 0) (2147468869)) (ELit 1);
   KWr (SA (ELit 0) (2147468870)) (ELit 1);
   KWr (SA (ELit 0) (2147468871)) (ELit 1);
   KWr (SA (ELit 0) (2147468872)) (ELit 1);
   KWr (SA (ELit 0) (2147468872)) (ELit 4);
   KWr (SA (ELit 0) (2147468873)) (ELit 1);
   KWr (SA (ELit 0) (2147468874)) (ELit 1);
   KWr (SA (ELit 0) (2147468875)) (ELit 1);
   KWr (SA (ELit 0) (2147468876)) (ELit 4);
   KWr (SA (ELit 0) (2147468880)) (ELit 1);
   KWr (SA (ELit 0) (2147468880)) (ELit 4);
   KWr (SA (ELit 0) (2147468881)) (ELit 1);
   KWr (SA (ELit 0) (2147468882)) (ELit 1);
   KWr (SA (ELit 0) (2147468883)) (ELit 1);
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
   KWr (SA (ELit 0) (2147468909)) (ELit 1);
   KWr (SA (ELit 0) (2147468910)) (ELit 1);
   KWr (SA (ELit 0) (2147468911)) (ELit 1);
   KWr (SA (ELit 0) (2147468912)) (ELit 1);
   KWr (SA (ELit 0) (2147468912)) (ELit 4);
   KWr (SA (ELit 0) (2147468913)) (ELit 1);
   KWr (SA (ELit 0) (2147468914)) (ELit 1);
   KWr (SA (ELit 0) (2147468915)) (ELit 1);
   KWr (SA (ELit 0) (2147468916)) (ELit 4);
   KWr (SA (ELit 0) (2147468920)) (ELit 1);
   KWr (SA (ELit 0) (2147468920)) (ELit 4);
   KWr (SA (ELit 0) (2147468921)) (ELit 1);
   KWr (SA (ELit 0) (2147468922)) (ELit 1);
   KWr (SA (ELit 0) (2147468923)) (ELit 1);
   KWr (SA (ELit 0) (2147468924)) (ELit 1);
   KWr (SA (ELit 0) (2147468924)) (ELit 4);
   KWr (SA (ELit 0) (2147468925)) (ELit 1);
   KWr (SA (ELit 0) (2147468926)) (ELit 1);
   KWr (SA (ELit 0) (2147468927)) (ELit 1);
   KWr (SA (ELit 0) (2147468928)) (ELit 4);
   KWr (SA (ELit 0) (2147468932)) (ELit 1);
   KWr (SA (ELit 0) (2147468932)) (ELit 4);
   KWr (SA (ELit 0) (2147468933)) (ELit 1);
   KWr (SA (ELit 0) (2147468934)) (ELit 1);
   KWr (SA (ELit 0) (2147468935)) (ELit 1);
   KWr (SA (ELit 0) (2147468936)) (ELit 1);
   KWr (SA (ELit 0) (2147468936)) (ELit 4);
   KWr (SA (ELit 0) (2147468937)) (ELit 1);
   KWr (SA (ELit 0) (2147468938)) (ELit 1);
   KWr (SA (ELit 0) (2147468939)) (ELit 1);
   KWr (SA (ELit 0) (2147468940)) (ELit 4);
   KWr (SA (ELit 0) (2147468944)) (ELit 4);
   KWr (SA (ELit 0) (2147468948)) (ELit 1);
   KWr (SA (ELit 0) (2147468948)) (ELit 4);
   KWr (SA (ELit 0) (2147468949)) (ELit 1);
   KWr (SA (ELit 0) (2147468950)) (ELit 1);
   KWr (SA (ELit 0) (2147468951)) (ELit 1);
   KWr (SA (ELit 0) (2147468952)) (ELit 1);
   KWr (SA (ELit 0) (2147468952)) (ELit 4);
   KWr (SA (ELit 0) (2147468953)) (ELit 1);
   KWr (SA (ELit 0) (2147468954)) (ELit 1);
   KWr (SA (ELit 0) (2147468955)) (ELit 1);
   KWr (SA (ELit 0) (2147468956)) (ELit 4);
   KWr (SA (ELit 0) (2147468960)) (ELit 1);
   KWr (SA (ELit 0) (2147468960)) (ELit 4);
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
   KWr (SA (ELit 0) (2147469017)) (ELit 1);
   KWr (SA (ELit 0) (2147469018)) (ELit 1);
   KWr (SA (ELit 0) (2147469019)) (ELit 1);
   KWr (SA (ELit 0) (2147469020)) (ELit 1);
   KWr (SA (ELit 0) (2147469020)) (ELit 4);
   KWr (SA (ELit 0) (2147469021)) (ELit 1);
   KWr (SA (ELit 0) (2147469022)) (ELit 1);
   KWr (SA (ELit 0) (2147469023)) (ELit 1);
   KWr (SA (ELit 0) (2147469024)) (ELit 4);
   KWr (SA (ELit 0) (2147469028)) (ELit 1);
   KWr (SA (ELit 0) (2147469028)) (ELit 4);
   KWr (SA (ELit 0) (2147469029)) (ELit 1);
   KWr (SA (ELit 0) (2147469030)) (ELit 1);
   KWr (SA (ELit 0) (2147469031)) (ELit 1);
   KWr (SA (ELit 0) (2147469032)) (ELit 1);
   KWr (SA (ELit 0) (2147469033)) (ELit 1);
   KWr (SA (ELit 0) (2147469034)) (ELit 1);
   KWr (SA (ELit 0) (2147469035)) (ELit 1);
   KWr (SA (ELit 0) (2147469036)) (ELit 1);
   KWr (SA (ELit 0) (2147469037)) (ELit 1);
   KWr (SA (ELit 0) (2147469038)) (ELit 1);
   KWr (SA (ELit 0) (2147469039)) (ELit 1);
   KWr (SA (ELit 0) (2147469072)) (ELit 1);
   KWr (SA (ELit 0) (2147469072)) (ELit 4);
   KWr (SA (ELit 0) (2147469073)) (ELit 1);
   KWr (SA (ELit 0) (2147469074)) (ELit 1);
   KWr (SA (ELit 0) (2147469075)) (ELit 1);
   KWr (SA (ELit 0) (2147469076)) (ELit 4);
   KWr (SA (ELit 0) (2147469080)) (ELit 1);
   KWr (SA (ELit 0) (2147469080)) (ELit 4);
   KWr (SA (ELit 0) (2147469081)) (ELit 1);
   KWr (SA (ELit 0) (2147469082)) (ELit 1);
   KWr (SA (ELit 0) (2147469083)) (ELit 1);
   KWr (SA (ELit 0) (2147469084)) (ELit 1);
   KWr (SA (ELit 0) (2147469085)) (ELit 1);
   KWr (SA (ELit 0) (2147469086)) (ELit 1);
   KWr (SA (ELit 0) (2147469087)) (ELit 1);
   KWr (SA (ELit 0) (2147469088)) (ELit 1);
   KWr (SA (ELit 0) (2147469089)) (ELit 1);
   KWr (SA (ELit 0) (2147469090)) (ELit 1);
   KWr (SA (ELit 0) (2147469091)) (ELit 1);
   KWr (SA (ELit 0) (2147469092)) (ELit 1);
   KWr (SA (ELit 0) (2147469092)) (ELit 4);
   KWr (SA (ELit 0) (2147469093)) (ELit 1);
   KWr (SA (ELit 0) (2147469094)) (ELit 1);
   KWr (SA (ELit 0) (2147469095)) (ELit 1);
   KWr (SA (ELit 0) (2147469096)) (ELit 4);
   KWr (SA (ELit 0) (2147469100)) (ELit 1);
   KWr (SA (ELit 0) (2147469100)) (ELit 4);
   KWr (SA (ELit 0) (2147469101)) (ELit 1);
   KWr (SA (ELit 0) (2147469102)) (ELit 1);
   KWr (SA (ELit 0) (2147469103)) (ELit 1);
   KWr (SA (ELit 0) (2147612664)) (ELit 184);
   KWr (SA (ELit 0) (2147612664)) (ELit 1);
   KWr (SA (ELit 0) (2147612664)) (ELit 4);
   KWr (SA (ELit 0) (2147612665)) (ELit 1);
   KWr (SA (ELit 0) (2147612666)) (ELit 1);
   KWr (SA (ELit 0) (2147612667)) (ELit 1);
   KWr (SA (ELit 0) (2147612668)) (ELit 4);
   KWr (SA (ELit 0) (2147612672)) (ELit 4);
   KWr (SA (ELit 0) (2147612676)) (ELit 4);
   KWr (SA (ELit 0) (2147612680)) (ELit 4);
   KWr (SA (ELit 0) (2147612684)) (ELit 4);
   KWr (SA (ELit 0) (2147612688)) (ELit 4);
   KWr (SA (ELit 0) (2147612692)) (ELit 8);
   KWr (SA (ELit 0) (2147612700)) (ELit 8);
   KWr (SA (ELit 0) (2147612708)) (ELit 8);
   KWr (SA (ELit 0) (2147612716)) (ELit 8);
   KWr (SA (ELit 0) (2147612724)) (ELit 8);
   KWr (SA (ELit 0) (2147612732)) (ELit 8);
   KWr (SA (ELit 0) (2147612740)) (ELit 8);
   KWr (SA (ELit 0) (2147612748)) (ELit 8);
   KWr (SA (ELit 0) (2147612756)) (ELit 8);
   KWr (SA (ELit 0) (2147612764)) (ELit 8);
   KWr (SA (ELit 0) (2147612772)) (ELit 8);
   KWr (SA (ELit 0) (2147612780)) (ELit 8);
   KWr (SA (ELit 0) (2147612788)) (ELit 8);
   KWr (SA (ELit 0) (2147612796)) (ELit 8);
   KWr (SA (ELit 0) (2147612804)) (ELit 8);
   KWr (SA (ELit 0) (2147612812)) (ELit 8);
   KWr (SA (ELit 0) (2147612820)) (ELit 8);
   KWr (SA (ELit 0) (2147612828)) (ELit 4);
   KWr (SA (ELit 0) (2147612828)) (ELit 8);
   KWr (SA (ELit 0) (2147612832)) (ELit 4);
   KWr (SA (ELit 0) (2147612836)) (ELit 4);
   KWr (SA (ELit 0) (2147612836)) (ELit 8);
   KWr (SA (ELit 0) (2147612840)) (ELit 4);
   KWr (SA (ELit 0) (2147612844)) (ELit 4);
   KWr (SA (ELit 0) (2147612844)) (ELit 8);
   KWord (SA (ELit 0) (6765656)) 4 (EVar 44);
   KRange (EVar 44) 1 4194303;
   KWord (SA (ELit 0) (6897520)) 4 (ELit 0);
   KWord (SA (ELit 0) (6897555)) 1 (ELit 0);
   KWord (SA (ELit 0) (6896992)) 8 (ELit 6897000);
   KWord (SA (ELit 0) (6896984)) 4 (ELit 8);
   KWord (SA (ELit 0) (6897064)) 8 (ELit 449180);
   KWord (SA (ELit 0) (6897320)) 8 (ELit 0);
   KWord (SA (ELit 0) (6896980)) 4 (ELit 0);
   KWord (SA (ELit 0) (1299540)) 1 (ELit 0);
   KWord (SA (ELit 0) (6897056)) 8 (ELit 874172);
   KWord (SA (ELit 0) (6897312)) 8 (ELit 6759144);
   KWord (SA (ELit 0) (6897048)) 8 (ELit 449180);
   KWord (SA (ELit 0) (6897304)) 8 (ELit 0);
   KWord (SA (ELit 0) (6897040)) 8 (ELit 874172);
   KWord (SA (ELit 0) (6897296)) 8 (ELit 6759112);
   KWord (SA (ELit 0) (6759144)) 1 (ELit 6);
   KWord (SA (ELit 0) (6897032)) 8 (ELit 449180);
   KWord (SA (ELit 0) (6897288)) 8 (ELit 0);
   KWord (SA (ELit 0) (6897024)) 8 (ELit 872740);
   KWord (SA (ELit 0) (6897280)) 8 (ELit 1293304);
   KWord (SA (ELit 0) (6759112)) 1 (ELit 16);
   KWord (SA (ELit 0) (6897016)) 8 (ELit 1148964);
   KWord (SA (ELit 0) (6897272)) 8 (ELit 687916);
   KWord (SA (ELit 0) (6759060)) 1 (ELit 0);
   KWord (SA (ELit 0) (6897008)) 8 (ELit 1148964);
   KWord (SA (ELit 0) (6897264)) 8 (ELit 619876);
   KWord (SA (ELit 0) (1907424)) 1 (ELit 0);
   KWord (SA (ELit 0) (6897000)) 8 (ELit 0);
   KWord (SA (ELit 0) (1295824)) 1 (ELit 0);
   KWord (SA (ELit 0) (1282768)) 8 (ELit 1282768);
   KWord (SA (ELit 0) (1295744)) 8 (ELit 1);
   KWord (SA (ELit 0) (1299536)) 4 (ELit 1);
   KWord (SA (ELit 0) (1299696)) 8 (ELit 0);
   KWord (SA (ELit 0) (1313048)) 1 (ELit 1);
   KWord (SA (ELit 0) (1309752)) 8 (ELit 2147450880);
   KWord (SA (ELit 0) (1294272)) 8 (ELit 143808);
   KWord (SA (ELit 0) (1294288)) 1 (ELit 32);
   KWord (SA (ELit 0) (1307804)) 1 (ELit 1);
   KWord (SA (ELit 0) (1294288)) 8 (ELit 32);
   KWord (SA (ELit 0) (1906656)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1283280)) 8 (ELit 1219844);
   KWord (SA (ELit 0) (1294328)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294336)) 8 (ELit 143904);
   KWord (SA (ELit 0) (1294352)) 1 (ELit 32);
   KWord (SA (ELit 0) (1294352)) 8 (ELit 32);
   KWord (SA (ELit 0) (1294392)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294400)) 8 (ELit 143936);
   KWord (SA (ELit 0) (1294416)) 1 (ELit 96);
   KWord (SA (ELit 0) (1294416)) 8 (ELit 96);
   KWord (SA (ELit 0) (1294456)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294464)) 8 (ELit 144128);
   KWord (SA (ELit 0) (1294480)) 1 (ELit 32);
   KWord (SA (ELit 0) (1294480)) 8 (ELit 32);
   KWord (SA (ELit 0) (1294520)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294528)) 8 (ELit 144160);
   KWord (SA (ELit 0) (1294544)) 1 (ELit 64);
   KWord (SA (ELit 0) (1294544)) 8 (ELit 64);
   KWord (SA (ELit 0) (1294584)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294592)) 8 (ELit 144224);
   KWord (SA (ELit 0) (1294608)) 1 (ELit 32);
   KWord (SA (ELit 0) (1294608)) 8 (ELit 32);
   KWord (SA (ELit 0) (1294648)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294656)) 8 (ELit 144256);
   KWord (SA (ELit 0) (1294672)) 1 (ELit 96);
   KWord (SA (ELit 0) (1294672)) 8 (ELit 96);
   KWord (SA (ELit 0) (1294712)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294720)) 8 (ELit 144352);
   KWord (SA (ELit 0) (1294736)) 1 (ELit 96);
   KWord (SA (ELit 0) (1294736)) 8 (ELit 96);
   KWord (SA (ELit 0) (1294776)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294784)) 8 (ELit 144448);
   KWord (SA (ELit 0) (1294800)) 1 (ELit 128);
   KWord (SA (ELit 0) (1294800)) 8 (ELit 128);
   KWord (SA (ELit 0) (1294840)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294848)) 8 (ELit 144576);
   KWord (SA (ELit 0) (1294864)) 1 (ELit 96);
   KWord (SA (ELit 0) (1294864)) 8 (ELit 96);
   KWord (SA (ELit 0) (1294904)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294912)) 8 (ELit 144672);
   KWord (SA (ELit 0) (1294928)) 1 (ELit 64);
   KWord (SA (ELit 0) (1294928)) 8 (ELit 64);
   KWord (SA (ELit 0) (1294968)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1294976)) 8 (ELit 144736);
   KWord (SA (ELit 0) (1294992)) 1 (ELit 64);
   KWord (SA (ELit 0) (1294992)) 8 (ELit 64);
   KWord (SA (ELit 0) (1295032)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295040)) 8 (ELit 144800);
   KWord (SA (ELit 0) (1295056)) 1 (ELit 64);
   KWord (SA (ELit 0) (1295056)) 8 (ELit 64);
   KWord (SA (ELit 0) (1295096)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295104)) 8 (ELit 144864);
   KWord (SA (ELit 0) (1295120)) 1 (ELit 64);
   KWord (SA (ELit 0) (1295120)) 8 (ELit 64);
   KWord (SA (ELit 0) (1295160)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295168)) 8 (ELit 144928);
   KWord (SA (ELit 0) (1295184)) 1 (ELit 64);
   KWord (SA (ELit 0) (1295184)) 8 (ELit 64);
   KWord (SA (ELit 0) (1295224)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295232)) 8 (ELit 144992);
   KWord (SA (ELit 0) (1295248)) 1 (ELit 64);
   KWord (SA (ELit 0) (1295248)) 8 (ELit 64);
   KWord (SA (ELit 0) (1295288)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295296)) 8 (ELit 145056);
   KWord (SA (ELit 0) (1295312)) 1 (ELit 64);
   KWord (SA (ELit 0) (1295312)) 8 (ELit 64);
   KWord (SA (ELit 0) (1295352)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295360)) 8 (ELit 145120);
   KWord (SA (ELit 0) (1295376)) 1 (ELit 96);
   KWord (SA (ELit 0) (1295376)) 8 (ELit 96);
   KWord (SA (ELit 0) (1295416)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295424)) 8 (ELit 145216);
   KWord (SA (ELit 0) (1295440)) 1 (ELit 64);
   KWord (SA (ELit 0) (1295440)) 8 (ELit 64);
   KWord (SA (ELit 0) (1295480)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295488)) 8 (ELit 145536);
   KWord (SA (ELit 0) (1295504)) 1 (ELit 96);
   KWord (SA (ELit 0) (1295504)) 8 (ELit 96);
   KWord (SA (ELit 0) (1295544)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295552)) 8 (ELit 145632);
   KWord (SA (ELit 0) (1295568)) 1 (ELit 32);
   KWord (SA (ELit 0) (1295568)) 8 (ELit 32);
   KWord (SA (ELit 0) (1295608)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295616)) 8 (ELit 145664);
   KWord (SA (ELit 0) (1295632)) 1 (ELit 32);
   KWord (SA (ELit 0) (1295632)) 8 (ELit 32);
   KWord (SA (ELit 0) (1295672)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (1295680)) 8 (ELit 145696);
   KWord (SA (ELit 0) (1295696)) 1 (ELit 96);
   KWord (SA (ELit 0) (1295696)) 8 (ELit 96);
   KWord (SA (ELit 0) (1295736)) 8 (ELit 18446744073709551615);
   KWord (SA (ELit 0) (6898952)) 8 (ELit 0);
   KWord (SA (ELit 0) (1294224)) 8 (ELit 1293992);
   KWord (SA (ELit 0) (1294132)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1294032)) 8 (ELit 0);
   KWord (SA (ELit 0) (1294048)) 8 (ELit 0);
   KWord (SA (ELit 0) (1294000)) 8 (ELit 0);
   KWord (SA (ELit 0) (1294008)) 8 (ELit 0);
   KWord (SA (ELit 0) (1293984)) 8 (ELit 1293752);
   KWord (SA (ELit 0) (1293892)) 4 (ELit 4294967295);
   KWord (SA (ELit 0) (1293792)) 8 (ELit 6898978);
   KWord (SA (ELit 0) (1293808)) 8 (ELit 6898976);
   KWord (SA (ELit 0) (1293824)) 8 (ELit 1180112);
   KWord (SA (ELit 0) (6896960)) 8 (EVar 40);
   KWord (SA (ELit 0) (1293872)) 4 (ELit 1)].
Definition ss0 : sym_state := SS 1149048 regs0 [] kn0 NX0.
Definition F0 : list SGP.region := [(EVar 2, (-320), ELit 320); (ELit 0, (1295744), ELit 8); (ELit 0, (1295824), ELit 1); (ELit 0, (1299696), ELit 8); (ELit 0, (6896976), ELit 1); (ELit 0, (6896984), ELit 4); (ELit 0, (6896992), ELit 8); (ELit 0, (6897520), ELit 4); (ELit 0, (2147468856), ELit 1); (ELit 0, (2147468857), ELit 1); (ELit 0, (2147468858), ELit 1); (ELit 0, (2147468859), ELit 1); (ELit 0, (2147468868), ELit 1); (ELit 0, (2147468869), ELit 1); (ELit 0, (2147468870), ELit 1); (ELit 0, (2147468871), ELit 1); (ELit 0, (2147468872), ELit 1); (ELit 0, (2147468872), ELit 4); (ELit 0, (2147468873), ELit 1); (ELit 0, (2147468874), ELit 1); (ELit 0, (2147468875), ELit 1); (ELit 0, (2147468876), ELit 4); (ELit 0, (2147468880), ELit 1); (ELit 0, (2147468880), ELit 4); (ELit 0, (2147468881), ELit 1); (ELit 0, (2147468882), ELit 1); (ELit 0, (2147468883), ELit 1); (ELit 0, (2147468896), ELit 1); (ELit 0, (2147468897), ELit 1); (ELit 0, (2147468898), ELit 1); (ELit 0, (2147468899), ELit 1); (ELit 0, (2147468900), ELit 1); (ELit 0, (2147468901), ELit 1); (ELit 0, (2147468902), ELit 1); (ELit 0, (2147468903), ELit 1); (ELit 0, (2147468904), ELit 1); (ELit 0, (2147468905), ELit 1); (ELit 0, (2147468906), ELit 1); (ELit 0, (2147468907), ELit 1); (ELit 0, (2147468908), ELit 1); (ELit 0, (2147468909), ELit 1); (ELit 0, (2147468910), ELit 1); (ELit 0, (2147468911), ELit 1); (ELit 0, (2147468912), ELit 1); (ELit 0, (2147468912), ELit 4); (ELit 0, (2147468913), ELit 1); (ELit 0, (2147468914), ELit 1); (ELit 0, (2147468915), ELit 1); (ELit 0, (2147468916), ELit 4); (ELit 0, (2147468920), ELit 1); (ELit 0, (2147468920), ELit 4); (ELit 0, (2147468921), ELit 1); (ELit 0, (2147468922), ELit 1); (ELit 0, (2147468923), ELit 1); (ELit 0, (2147468924), ELit 1); (ELit 0, (2147468924), ELit 4); (ELit 0, (2147468925), ELit 1); (ELit 0, (2147468926), ELit 1); (ELit 0, (2147468927), ELit 1); (ELit 0, (2147468928), ELit 4); (ELit 0, (2147468932), ELit 1); (ELit 0, (2147468932), ELit 4); (ELit 0, (2147468933), ELit 1); (ELit 0, (2147468934), ELit 1); (ELit 0, (2147468935), ELit 1); (ELit 0, (2147468936), ELit 1); (ELit 0, (2147468936), ELit 4); (ELit 0, (2147468937), ELit 1); (ELit 0, (2147468938), ELit 1); (ELit 0, (2147468939), ELit 1); (ELit 0, (2147468940), ELit 4); (ELit 0, (2147468944), ELit 4); (ELit 0, (2147468948), ELit 1); (ELit 0, (2147468948), ELit 4); (ELit 0, (2147468949), ELit 1); (ELit 0, (2147468950), ELit 1); (ELit 0, (2147468951), ELit 1); (ELit 0, (2147468952), ELit 1); (ELit 0, (2147468952), ELit 4); (ELit 0, (2147468953), ELit 1); (ELit 0, (2147468954), ELit 1); (ELit 0, (2147468955), ELit 1); (ELit 0, (2147468956), ELit 4); (ELit 0, (2147468960), ELit 1); (ELit 0, (2147468960), ELit 4); (ELit 0, (2147468961), ELit 1); (ELit 0, (2147468962), ELit 1); (ELit 0, (2147468963), ELit 1); (ELit 0, (2147468964), ELit 1); (ELit 0, (2147468965), ELit 1); (ELit 0, (2147468966), ELit 1); (ELit 0, (2147468967), ELit 1); (ELit 0, (2147468968), ELit 1); (ELit 0, (2147468969), ELit 1); (ELit 0, (2147468970), ELit 1); (ELit 0, (2147468971), ELit 1); (ELit 0, (2147468972), ELit 1); (ELit 0, (2147468973), ELit 1); (ELit 0, (2147468974), ELit 1); (ELit 0, (2147468975), ELit 1); (ELit 0, (2147468976), ELit 1); (ELit 0, (2147468977), ELit 1); (ELit 0, (2147468978), ELit 1); (ELit 0, (2147468979), ELit 1); (ELit 0, (2147468980), ELit 1); (ELit 0, (2147468981), ELit 1); (ELit 0, (2147468982), ELit 1); (ELit 0, (2147468983), ELit 1); (ELit 0, (2147468984), ELit 1); (ELit 0, (2147468985), ELit 1); (ELit 0, (2147468986), ELit 1); (ELit 0, (2147468987), ELit 1); (ELit 0, (2147468988), ELit 1); (ELit 0, (2147468989), ELit 1); (ELit 0, (2147468990), ELit 1); (ELit 0, (2147468991), ELit 1); (ELit 0, (2147468992), ELit 1); (ELit 0, (2147468993), ELit 1); (ELit 0, (2147468994), ELit 1); (ELit 0, (2147468995), ELit 1); (ELit 0, (2147468996), ELit 1); (ELit 0, (2147468997), ELit 1); (ELit 0, (2147468998), ELit 1); (ELit 0, (2147468999), ELit 1); (ELit 0, (2147469000), ELit 1); (ELit 0, (2147469001), ELit 1); (ELit 0, (2147469002), ELit 1); (ELit 0, (2147469003), ELit 1); (ELit 0, (2147469004), ELit 1); (ELit 0, (2147469005), ELit 1); (ELit 0, (2147469006), ELit 1); (ELit 0, (2147469007), ELit 1); (ELit 0, (2147469008), ELit 1); (ELit 0, (2147469009), ELit 1); (ELit 0, (2147469010), ELit 1); (ELit 0, (2147469011), ELit 1); (ELit 0, (2147469012), ELit 1); (ELit 0, (2147469013), ELit 1); (ELit 0, (2147469014), ELit 1); (ELit 0, (2147469015), ELit 1); (ELit 0, (2147469016), ELit 1); (ELit 0, (2147469017), ELit 1); (ELit 0, (2147469018), ELit 1); (ELit 0, (2147469019), ELit 1); (ELit 0, (2147469020), ELit 1); (ELit 0, (2147469020), ELit 4); (ELit 0, (2147469021), ELit 1); (ELit 0, (2147469022), ELit 1); (ELit 0, (2147469023), ELit 1); (ELit 0, (2147469024), ELit 4); (ELit 0, (2147469028), ELit 1); (ELit 0, (2147469028), ELit 4); (ELit 0, (2147469029), ELit 1); (ELit 0, (2147469030), ELit 1); (ELit 0, (2147469031), ELit 1); (ELit 0, (2147469032), ELit 1); (ELit 0, (2147469033), ELit 1); (ELit 0, (2147469034), ELit 1); (ELit 0, (2147469035), ELit 1); (ELit 0, (2147469036), ELit 1); (ELit 0, (2147469037), ELit 1); (ELit 0, (2147469038), ELit 1); (ELit 0, (2147469039), ELit 1); (ELit 0, (2147469072), ELit 1); (ELit 0, (2147469072), ELit 4); (ELit 0, (2147469073), ELit 1); (ELit 0, (2147469074), ELit 1); (ELit 0, (2147469075), ELit 1); (ELit 0, (2147469076), ELit 4); (ELit 0, (2147469080), ELit 1); (ELit 0, (2147469080), ELit 4); (ELit 0, (2147469081), ELit 1); (ELit 0, (2147469082), ELit 1); (ELit 0, (2147469083), ELit 1); (ELit 0, (2147469084), ELit 1); (ELit 0, (2147469085), ELit 1); (ELit 0, (2147469086), ELit 1); (ELit 0, (2147469087), ELit 1); (ELit 0, (2147469088), ELit 1); (ELit 0, (2147469089), ELit 1); (ELit 0, (2147469090), ELit 1); (ELit 0, (2147469091), ELit 1); (ELit 0, (2147469092), ELit 1); (ELit 0, (2147469092), ELit 4); (ELit 0, (2147469093), ELit 1); (ELit 0, (2147469094), ELit 1); (ELit 0, (2147469095), ELit 1); (ELit 0, (2147469096), ELit 4); (ELit 0, (2147469100), ELit 1); (ELit 0, (2147469100), ELit 4); (ELit 0, (2147469101), ELit 1); (ELit 0, (2147469102), ELit 1); (ELit 0, (2147469103), ELit 1); (ELit 0, (2147612664), ELit 184); (ELit 0, (2147612664), ELit 1); (ELit 0, (2147612664), ELit 4); (ELit 0, (2147612665), ELit 1); (ELit 0, (2147612666), ELit 1); (ELit 0, (2147612667), ELit 1); (ELit 0, (2147612668), ELit 4); (ELit 0, (2147612672), ELit 4); (ELit 0, (2147612676), ELit 4); (ELit 0, (2147612680), ELit 4); (ELit 0, (2147612684), ELit 4); (ELit 0, (2147612688), ELit 4); (ELit 0, (2147612692), ELit 8); (ELit 0, (2147612700), ELit 8); (ELit 0, (2147612708), ELit 8); (ELit 0, (2147612716), ELit 8); (ELit 0, (2147612724), ELit 8); (ELit 0, (2147612732), ELit 8); (ELit 0, (2147612740), ELit 8); (ELit 0, (2147612748), ELit 8); (ELit 0, (2147612756), ELit 8); (ELit 0, (2147612764), ELit 8); (ELit 0, (2147612772), ELit 8); (ELit 0, (2147612780), ELit 8); (ELit 0, (2147612788), ELit 8); (ELit 0, (2147612796), ELit 8); (ELit 0, (2147612804), ELit 8); (ELit 0, (2147612812), ELit 8); (ELit 0, (2147612820), ELit 8); (ELit 0, (2147612828), ELit 4); (ELit 0, (2147612828), ELit 8); (ELit 0, (2147612832), ELit 4); (ELit 0, (2147612836), ELit 4); (ELit 0, (2147612836), ELit 8); (ELit 0, (2147612840), ELit 4); (ELit 0, (2147612844), ELit 4); (ELit 0, (2147612844), ELit 8)].
Definition F0L : list SR.region := [(EVar 2, (-320), 320); (ELit 0, (1295744), 8); (ELit 0, (1295824), 1); (ELit 0, (1299696), 8); (ELit 0, (6896976), 1); (ELit 0, (6896984), 4); (ELit 0, (6896992), 8); (ELit 0, (6897520), 4); (ELit 0, (2147468856), 1); (ELit 0, (2147468857), 1); (ELit 0, (2147468858), 1); (ELit 0, (2147468859), 1); (ELit 0, (2147468868), 1); (ELit 0, (2147468869), 1); (ELit 0, (2147468870), 1); (ELit 0, (2147468871), 1); (ELit 0, (2147468872), 1); (ELit 0, (2147468872), 4); (ELit 0, (2147468873), 1); (ELit 0, (2147468874), 1); (ELit 0, (2147468875), 1); (ELit 0, (2147468876), 4); (ELit 0, (2147468880), 1); (ELit 0, (2147468880), 4); (ELit 0, (2147468881), 1); (ELit 0, (2147468882), 1); (ELit 0, (2147468883), 1); (ELit 0, (2147468896), 1); (ELit 0, (2147468897), 1); (ELit 0, (2147468898), 1); (ELit 0, (2147468899), 1); (ELit 0, (2147468900), 1); (ELit 0, (2147468901), 1); (ELit 0, (2147468902), 1); (ELit 0, (2147468903), 1); (ELit 0, (2147468904), 1); (ELit 0, (2147468905), 1); (ELit 0, (2147468906), 1); (ELit 0, (2147468907), 1); (ELit 0, (2147468908), 1); (ELit 0, (2147468909), 1); (ELit 0, (2147468910), 1); (ELit 0, (2147468911), 1); (ELit 0, (2147468912), 1); (ELit 0, (2147468912), 4); (ELit 0, (2147468913), 1); (ELit 0, (2147468914), 1); (ELit 0, (2147468915), 1); (ELit 0, (2147468916), 4); (ELit 0, (2147468920), 1); (ELit 0, (2147468920), 4); (ELit 0, (2147468921), 1); (ELit 0, (2147468922), 1); (ELit 0, (2147468923), 1); (ELit 0, (2147468924), 1); (ELit 0, (2147468924), 4); (ELit 0, (2147468925), 1); (ELit 0, (2147468926), 1); (ELit 0, (2147468927), 1); (ELit 0, (2147468928), 4); (ELit 0, (2147468932), 1); (ELit 0, (2147468932), 4); (ELit 0, (2147468933), 1); (ELit 0, (2147468934), 1); (ELit 0, (2147468935), 1); (ELit 0, (2147468936), 1); (ELit 0, (2147468936), 4); (ELit 0, (2147468937), 1); (ELit 0, (2147468938), 1); (ELit 0, (2147468939), 1); (ELit 0, (2147468940), 4); (ELit 0, (2147468944), 4); (ELit 0, (2147468948), 1); (ELit 0, (2147468948), 4); (ELit 0, (2147468949), 1); (ELit 0, (2147468950), 1); (ELit 0, (2147468951), 1); (ELit 0, (2147468952), 1); (ELit 0, (2147468952), 4); (ELit 0, (2147468953), 1); (ELit 0, (2147468954), 1); (ELit 0, (2147468955), 1); (ELit 0, (2147468956), 4); (ELit 0, (2147468960), 1); (ELit 0, (2147468960), 4); (ELit 0, (2147468961), 1); (ELit 0, (2147468962), 1); (ELit 0, (2147468963), 1); (ELit 0, (2147468964), 1); (ELit 0, (2147468965), 1); (ELit 0, (2147468966), 1); (ELit 0, (2147468967), 1); (ELit 0, (2147468968), 1); (ELit 0, (2147468969), 1); (ELit 0, (2147468970), 1); (ELit 0, (2147468971), 1); (ELit 0, (2147468972), 1); (ELit 0, (2147468973), 1); (ELit 0, (2147468974), 1); (ELit 0, (2147468975), 1); (ELit 0, (2147468976), 1); (ELit 0, (2147468977), 1); (ELit 0, (2147468978), 1); (ELit 0, (2147468979), 1); (ELit 0, (2147468980), 1); (ELit 0, (2147468981), 1); (ELit 0, (2147468982), 1); (ELit 0, (2147468983), 1); (ELit 0, (2147468984), 1); (ELit 0, (2147468985), 1); (ELit 0, (2147468986), 1); (ELit 0, (2147468987), 1); (ELit 0, (2147468988), 1); (ELit 0, (2147468989), 1); (ELit 0, (2147468990), 1); (ELit 0, (2147468991), 1); (ELit 0, (2147468992), 1); (ELit 0, (2147468993), 1); (ELit 0, (2147468994), 1); (ELit 0, (2147468995), 1); (ELit 0, (2147468996), 1); (ELit 0, (2147468997), 1); (ELit 0, (2147468998), 1); (ELit 0, (2147468999), 1); (ELit 0, (2147469000), 1); (ELit 0, (2147469001), 1); (ELit 0, (2147469002), 1); (ELit 0, (2147469003), 1); (ELit 0, (2147469004), 1); (ELit 0, (2147469005), 1); (ELit 0, (2147469006), 1); (ELit 0, (2147469007), 1); (ELit 0, (2147469008), 1); (ELit 0, (2147469009), 1); (ELit 0, (2147469010), 1); (ELit 0, (2147469011), 1); (ELit 0, (2147469012), 1); (ELit 0, (2147469013), 1); (ELit 0, (2147469014), 1); (ELit 0, (2147469015), 1); (ELit 0, (2147469016), 1); (ELit 0, (2147469017), 1); (ELit 0, (2147469018), 1); (ELit 0, (2147469019), 1); (ELit 0, (2147469020), 1); (ELit 0, (2147469020), 4); (ELit 0, (2147469021), 1); (ELit 0, (2147469022), 1); (ELit 0, (2147469023), 1); (ELit 0, (2147469024), 4); (ELit 0, (2147469028), 1); (ELit 0, (2147469028), 4); (ELit 0, (2147469029), 1); (ELit 0, (2147469030), 1); (ELit 0, (2147469031), 1); (ELit 0, (2147469032), 1); (ELit 0, (2147469033), 1); (ELit 0, (2147469034), 1); (ELit 0, (2147469035), 1); (ELit 0, (2147469036), 1); (ELit 0, (2147469037), 1); (ELit 0, (2147469038), 1); (ELit 0, (2147469039), 1); (ELit 0, (2147469072), 1); (ELit 0, (2147469072), 4); (ELit 0, (2147469073), 1); (ELit 0, (2147469074), 1); (ELit 0, (2147469075), 1); (ELit 0, (2147469076), 4); (ELit 0, (2147469080), 1); (ELit 0, (2147469080), 4); (ELit 0, (2147469081), 1); (ELit 0, (2147469082), 1); (ELit 0, (2147469083), 1); (ELit 0, (2147469084), 1); (ELit 0, (2147469085), 1); (ELit 0, (2147469086), 1); (ELit 0, (2147469087), 1); (ELit 0, (2147469088), 1); (ELit 0, (2147469089), 1); (ELit 0, (2147469090), 1); (ELit 0, (2147469091), 1); (ELit 0, (2147469092), 1); (ELit 0, (2147469092), 4); (ELit 0, (2147469093), 1); (ELit 0, (2147469094), 1); (ELit 0, (2147469095), 1); (ELit 0, (2147469096), 4); (ELit 0, (2147469100), 1); (ELit 0, (2147469100), 4); (ELit 0, (2147469101), 1); (ELit 0, (2147469102), 1); (ELit 0, (2147469103), 1); (ELit 0, (2147612664), 184); (ELit 0, (2147612664), 1); (ELit 0, (2147612664), 4); (ELit 0, (2147612665), 1); (ELit 0, (2147612666), 1); (ELit 0, (2147612667), 1); (ELit 0, (2147612668), 4); (ELit 0, (2147612672), 4); (ELit 0, (2147612676), 4); (ELit 0, (2147612680), 4); (ELit 0, (2147612684), 4); (ELit 0, (2147612688), 4); (ELit 0, (2147612692), 8); (ELit 0, (2147612700), 8); (ELit 0, (2147612708), 8); (ELit 0, (2147612716), 8); (ELit 0, (2147612724), 8); (ELit 0, (2147612732), 8); (ELit 0, (2147612740), 8); (ELit 0, (2147612748), 8); (ELit 0, (2147612756), 8); (ELit 0, (2147612764), 8); (ELit 0, (2147612772), 8); (ELit 0, (2147612780), 8); (ELit 0, (2147612788), 8); (ELit 0, (2147612796), 8); (ELit 0, (2147612804), 8); (ELit 0, (2147612812), 8); (ELit 0, (2147612820), 8); (ELit 0, (2147612828), 4); (ELit 0, (2147612828), 8); (ELit 0, (2147612832), 4); (ELit 0, (2147612836), 4); (ELit 0, (2147612836), 8); (ELit 0, (2147612840), 4); (ELit 0, (2147612844), 4); (ELit 0, (2147612844), 8)].
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
  (([SGA.AStep (SR.SBlock [1180248; 1180248])], (93, SS 1180248 [ELit 0; ELit 1181792; EAlu Instr.ALU_ADD (EVar 2) (ELit (-144)); EVar 3; ELit 6765824; ELit 0; ELit 1152921504606846976; ELit 0; ELit 0; ELit 1293752; ELit 1; EAlu Instr.ALU_ADD (EVar 2) (ELit (-136)); ELit 2; ELit 2; ELit 17293822569102704639; ELit 1152920405095219200; ELit 18446742974197923840; ELit 66; ELit 2; EAlu Instr.ALU_ADD (EVar 2) (ELit (-136)); EVar 20; ELit 6896960; ELit 2; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; ELit 1299632; EVar 29; EVar 30; EVar 31] [] [KWord {| a_base := EVar 2; a_off := -112 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -120 |} 8 (ELit 0); KWord {| a_base := EVar 2; a_off := -128 |} 8 (ELit 2); KWord {| a_base := EVar 2; a_off := -136 |} 8 (ELit 6898976); KWord {| a_base := EVar 2; a_off := -104 |} 8 (EVar 40); KWord {| a_base := EVar 2; a_off := -96 |} 8 (EVar 22); KWord {| a_base := EVar 2; a_off := -88 |} 8 (EVar 21); KWord {| a_base := EVar 2; a_off := -80 |} 8 (EVar 20); KWord {| a_base := EVar 2; a_off := -72 |} 8 (EVar 19); KWord {| a_base := EVar 2; a_off := -64 |} 8 (EVar 18); KWord {| a_base := EVar 2; a_off := -56 |} 8 (EVar 9); KWord {| a_base := EVar 2; a_off := -48 |} 8 (ELit 1293752); KWord {| a_base := EVar 2; a_off := -40 |} 8 (ELit 1181792); KWord {| a_base := EVar 2; a_off := -32 |} 8 (EVar 10); KWord {| a_base := EVar 2; a_off := -24 |} 8 (ELit 1149156); KWord {| a_base := ELit 0; a_off := 1295744 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1299696 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612840 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612832 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612824 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612816 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612808 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612800 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612792 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612784 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612776 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612768 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612760 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612752 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612744 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612736 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612728 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612720 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612712 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612704 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612696 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612688 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612684 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612680 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612676 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612672 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612668 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147612664 |} 4 (ELit 0); KWord {| a_base := EVar 2; a_off := -312 |} 8 (ELit 2305843009213693952); KWord {| a_base := EVar 2; a_off := -304 |} 8 (ELit 1295744); KWord {| a_base := EVar 2; a_off := -296 |} 8 (ELit 116928); KWord {| a_base := EVar 2; a_off := -288 |} 8 (ELit 2); KWord {| a_base := EVar 2; a_off := -280 |} 8 (ELit 1); KWord {| a_base := EVar 2; a_off := -272 |} 8 (ELit 2305843009213693952); KWord {| a_base := EVar 2; a_off := -264 |} 8 (ELit 397496); KWord {| a_base := ELit 0; a_off := 2147469096 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469092 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469100 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469090 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469089 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469091 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469088 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469086 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469085 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469087 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469084 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469076 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469072 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469080 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469036 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469035 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469038 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469037 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469034 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469033 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469039 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469032 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469024 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469020 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469028 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469016 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469015 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469018 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469017 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469014 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469013 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469019 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469012 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469008 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469007 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469010 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469009 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469006 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469005 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469011 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469004 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469000 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468999 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469002 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469001 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468998 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468997 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147469003 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468996 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468992 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468991 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468994 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468993 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468990 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468989 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468995 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468988 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468984 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468983 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468986 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468985 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468982 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468981 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468987 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468980 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468976 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468975 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468978 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468977 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468974 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468973 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468979 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468972 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468968 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468967 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468970 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468969 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468966 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468965 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468971 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468964 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468956 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468952 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468960 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468944 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468940 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468948 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468936 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468928 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468924 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468932 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468916 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468912 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468920 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468910 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468909 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468911 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468908 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468904 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468903 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468906 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468905 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468902 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468901 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468907 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468900 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468898 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468897 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468899 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468896 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468876 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468872 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468880 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468870 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468869 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468871 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468868 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468858 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468857 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468859 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 2147468856 |} 1 (ELit 0); KWord {| a_base := EVar 2; a_off := -208 |} 8 (ELit 1898208); KWord {| a_base := EVar 2; a_off := -216 |} 8 (ELit 1313056); KWord {| a_base := EVar 2; a_off := -200 |} 8 (ELit 1313072); KWord {| a_base := EVar 2; a_off := -192 |} 8 (ELit 1313064); KWord {| a_base := EVar 2; a_off := -232 |} 8 (ELit 23); KWord {| a_base := EVar 2; a_off := -240 |} 8 (ELit 1299632); KWord {| a_base := EVar 2; a_off := -248 |} 8 (ELit 1299704); KWord {| a_base := EVar 2; a_off := -224 |} 8 (ELit 1294272); KWord {| a_base := EVar 2; a_off := -184 |} 8 (EVar 27); KWord {| a_base := EVar 2; a_off := -176 |} 8 (EVar 26); KWord {| a_base := EVar 2; a_off := -168 |} 8 (EVar 25); KWord {| a_base := EVar 2; a_off := -160 |} 8 (EVar 24); KWord {| a_base := EVar 2; a_off := -152 |} 8 (EVar 23); KWord {| a_base := EVar 2; a_off := -144 |} 8 (EVar 22); KWord {| a_base := ELit 0; a_off := 1295824 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6896976 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 6896992 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6896984 |} 4 (ELit 32); KWord {| a_base := ELit 0; a_off := 6897520 |} 4 (EVar 44); KWord {| a_base := EVar 2; a_off := -16 |} 8 (EVar 8); KWord {| a_base := EVar 2; a_off := -8 |} 8 (ELit 1147060); KRange (EVar 2) 140735332552704 140737488355328; KAlign (EVar 2) 16; KWr {| a_base := EVar 2; a_off := -320 |} (ELit 320); KUnk {| a_base := EVar 2; a_off := -320 |} (ELit 8); KUnk {| a_base := EVar 2; a_off := -256 |} (ELit 8); KImg 65536 1282048; KWr {| a_base := ELit 0; a_off := 1295744 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 1295824 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 1299696 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 6896976 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 6896984 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 6896992 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 6897520 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468856 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468857 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468858 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468859 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468868 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468869 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468870 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468871 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468872 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468872 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468873 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468874 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468875 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468876 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468880 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468880 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468881 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468882 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468883 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468896 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468897 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468898 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468899 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468900 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468901 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468902 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468903 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468904 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468905 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468906 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468907 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468908 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468909 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468910 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468911 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468912 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468912 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468913 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468914 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468915 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468916 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468920 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468920 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468921 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468922 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468923 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468924 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468924 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468925 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468926 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468927 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468928 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468932 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468932 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468933 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468934 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468935 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468936 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468936 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468937 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468938 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468939 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468940 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468944 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468948 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468948 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468949 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468950 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468951 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468952 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468952 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468953 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468954 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468955 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468956 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468960 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468960 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147468961 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468962 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468963 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468964 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468965 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468966 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468967 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468968 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468969 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468970 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468971 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468972 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468973 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468974 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468975 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468976 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468977 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468978 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468979 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468980 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468981 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468982 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468983 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468984 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468985 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468986 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468987 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468988 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468989 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468990 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468991 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468992 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468993 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468994 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468995 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468996 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468997 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468998 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147468999 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469000 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469001 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469002 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469003 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469004 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469005 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469006 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469007 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469008 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469009 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469010 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469011 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469012 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469013 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469014 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469015 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469016 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469017 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469018 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469019 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469020 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469020 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469021 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469022 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469023 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469024 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469028 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469028 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469029 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469030 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469031 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469032 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469033 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469034 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469035 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469036 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469037 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469038 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469039 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469072 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469072 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469073 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469074 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469075 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469076 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469080 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469080 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469081 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469082 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469083 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469084 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469085 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469086 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469087 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469088 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469089 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469090 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469091 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469092 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469092 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469093 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469094 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469095 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469096 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469100 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469100 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147469101 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469102 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147469103 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147612664 |} (ELit 184); KWr {| a_base := ELit 0; a_off := 2147612664 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147612664 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612665 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147612666 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147612667 |} (ELit 1); KWr {| a_base := ELit 0; a_off := 2147612668 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612672 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612676 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612680 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612684 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612688 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612692 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612700 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612708 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612716 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612724 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612732 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612740 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612748 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612756 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612764 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612772 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612780 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612788 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612796 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612804 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612812 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612820 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612828 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612828 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612832 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612836 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612836 |} (ELit 8); KWr {| a_base := ELit 0; a_off := 2147612840 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612844 |} (ELit 4); KWr {| a_base := ELit 0; a_off := 2147612844 |} (ELit 8); KWord {| a_base := ELit 0; a_off := 6765656 |} 4 (EVar 44); KRange (EVar 44) 1 4194303; KWord {| a_base := ELit 0; a_off := 6897555 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6897064 |} 8 (ELit 449180); KWord {| a_base := ELit 0; a_off := 6897320 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6896980 |} 4 (ELit 0); KWord {| a_base := ELit 0; a_off := 1299540 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6897056 |} 8 (ELit 874172); KWord {| a_base := ELit 0; a_off := 6897312 |} 8 (ELit 6759144); KWord {| a_base := ELit 0; a_off := 6897048 |} 8 (ELit 449180); KWord {| a_base := ELit 0; a_off := 6897304 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6897040 |} 8 (ELit 874172); KWord {| a_base := ELit 0; a_off := 6897296 |} 8 (ELit 6759112); KWord {| a_base := ELit 0; a_off := 6759144 |} 1 (ELit 6); KWord {| a_base := ELit 0; a_off := 6897032 |} 8 (ELit 449180); KWord {| a_base := ELit 0; a_off := 6897288 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 6897024 |} 8 (ELit 872740); KWord {| a_base := ELit 0; a_off := 6897280 |} 8 (ELit 1293304); KWord {| a_base := ELit 0; a_off := 6759112 |} 1 (ELit 16); KWord {| a_base := ELit 0; a_off := 6897016 |} 8 (ELit 1148964); KWord {| a_base := ELit 0; a_off := 6897272 |} 8 (ELit 687916); KWord {| a_base := ELit 0; a_off := 6759060 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6897008 |} 8 (ELit 1148964); KWord {| a_base := ELit 0; a_off := 6897264 |} 8 (ELit 619876); KWord {| a_base := ELit 0; a_off := 1907424 |} 1 (ELit 0); KWord {| a_base := ELit 0; a_off := 6897000 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1282768 |} 8 (ELit 1282768); KWord {| a_base := ELit 0; a_off := 1299536 |} 4 (ELit 1); KWord {| a_base := ELit 0; a_off := 1313048 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1309752 |} 8 (ELit 2147450880); KWord {| a_base := ELit 0; a_off := 1294272 |} 8 (ELit 143808); KWord {| a_base := ELit 0; a_off := 1294288 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1307804 |} 1 (ELit 1); KWord {| a_base := ELit 0; a_off := 1294288 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1906656 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1283280 |} 8 (ELit 1219844); KWord {| a_base := ELit 0; a_off := 1294328 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294336 |} 8 (ELit 143904); KWord {| a_base := ELit 0; a_off := 1294352 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1294352 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1294392 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294400 |} 8 (ELit 143936); KWord {| a_base := ELit 0; a_off := 1294416 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1294416 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1294456 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294464 |} 8 (ELit 144128); KWord {| a_base := ELit 0; a_off := 1294480 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1294480 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1294520 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294528 |} 8 (ELit 144160); KWord {| a_base := ELit 0; a_off := 1294544 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1294544 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1294584 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294592 |} 8 (ELit 144224); KWord {| a_base := ELit 0; a_off := 1294608 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1294608 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1294648 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294656 |} 8 (ELit 144256); KWord {| a_base := ELit 0; a_off := 1294672 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1294672 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1294712 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294720 |} 8 (ELit 144352); KWord {| a_base := ELit 0; a_off := 1294736 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1294736 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1294776 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294784 |} 8 (ELit 144448); KWord {| a_base := ELit 0; a_off := 1294800 |} 1 (ELit 128); KWord {| a_base := ELit 0; a_off := 1294800 |} 8 (ELit 128); KWord {| a_base := ELit 0; a_off := 1294840 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294848 |} 8 (ELit 144576); KWord {| a_base := ELit 0; a_off := 1294864 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1294864 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1294904 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294912 |} 8 (ELit 144672); KWord {| a_base := ELit 0; a_off := 1294928 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1294928 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1294968 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1294976 |} 8 (ELit 144736); KWord {| a_base := ELit 0; a_off := 1294992 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1294992 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295032 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295040 |} 8 (ELit 144800); KWord {| a_base := ELit 0; a_off := 1295056 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295056 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295096 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295104 |} 8 (ELit 144864); KWord {| a_base := ELit 0; a_off := 1295120 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295120 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295160 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295168 |} 8 (ELit 144928); KWord {| a_base := ELit 0; a_off := 1295184 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295184 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295224 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295232 |} 8 (ELit 144992); KWord {| a_base := ELit 0; a_off := 1295248 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295248 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295288 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295296 |} 8 (ELit 145056); KWord {| a_base := ELit 0; a_off := 1295312 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295312 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295352 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295360 |} 8 (ELit 145120); KWord {| a_base := ELit 0; a_off := 1295376 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1295376 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1295416 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295424 |} 8 (ELit 145216); KWord {| a_base := ELit 0; a_off := 1295440 |} 1 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295440 |} 8 (ELit 64); KWord {| a_base := ELit 0; a_off := 1295480 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295488 |} 8 (ELit 145536); KWord {| a_base := ELit 0; a_off := 1295504 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1295504 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1295544 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295552 |} 8 (ELit 145632); KWord {| a_base := ELit 0; a_off := 1295568 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1295568 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1295608 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295616 |} 8 (ELit 145664); KWord {| a_base := ELit 0; a_off := 1295632 |} 1 (ELit 32); KWord {| a_base := ELit 0; a_off := 1295632 |} 8 (ELit 32); KWord {| a_base := ELit 0; a_off := 1295672 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 1295680 |} 8 (ELit 145696); KWord {| a_base := ELit 0; a_off := 1295696 |} 1 (ELit 96); KWord {| a_base := ELit 0; a_off := 1295696 |} 8 (ELit 96); KWord {| a_base := ELit 0; a_off := 1295736 |} 8 (ELit 18446744073709551615); KWord {| a_base := ELit 0; a_off := 6898952 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1294224 |} 8 (ELit 1293992); KWord {| a_base := ELit 0; a_off := 1294132 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1294032 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1294048 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1294000 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1294008 |} 8 (ELit 0); KWord {| a_base := ELit 0; a_off := 1293984 |} 8 (ELit 1293752); KWord {| a_base := ELit 0; a_off := 1293892 |} 4 (ELit 4294967295); KWord {| a_base := ELit 0; a_off := 1293792 |} 8 (ELit 6898978); KWord {| a_base := ELit 0; a_off := 1293808 |} 8 (ELit 6898976); KWord {| a_base := ELit 0; a_off := 1293824 |} 8 (ELit 1180112); KWord {| a_base := ELit 0; a_off := 6896960 |} 8 (EVar 40); KWord {| a_base := ELit 0; a_off := 1293872 |} 4 (ELit 1)] 56))).
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
Definition ps0 : SR.post_spec := SR.PS 1180248 (map (fun i => (i, nth i regs_out0 (ELit 0))) (seq 1 31)) F0L cells0.

(* [comment removed for export] *)
Definition SXALL : list sym_state := [].
Definition mkps (st : sym_state) : SR.post_spec :=
  SR.PS (s_pc st) (map (fun i => (i, nth i (s_regs st) (ELit 0))) (seq 1 31)) F0L (cells_of st (spoff_of st)).
Definition PSS : list SR.post_spec := [ps0] ++ map mkps SXALL.
Definition ps := ps0. Definition regs_out := regs_out0. Definition cells := cells0. Definition nfresh := nfresh0.

Lemma cert : SGP.cert_ok RSEGS SegItab_Ba_cc72f4_b.IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NX0 BR XSTEP SGP.xstep2_none F0 PSS plan 1149048 regs0 kn0 = true.
Proof. apply SegPlanFast.SGF.cert_of_fast. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Definition seg_sound_ax := as0_plan_sound_it SegItab_Ba_cc72f4_b.IT SegItab_Ba_cc72f4_b.IT_sound BF NX0 BR XSTEP F0 PSS plan 1149048 regs0 kn0 cert (SGP.xstep_none_ok RSEGS NX0 BR F0).
