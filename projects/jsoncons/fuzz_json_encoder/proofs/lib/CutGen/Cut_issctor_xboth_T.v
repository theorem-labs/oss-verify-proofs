(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm5PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm5CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := [(727572, 168%nat); (1076900, 24%nat); (734968, 114%nat); (1057080, 78%nat); (735424, 226%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Definition BF : nat := 5000.
Definition NF : nat := 40.
Definition ENDS : list Z := [728096].
Definition HDECL : CH.hdecl := CH.HD (10752) (8224) [((EAlu Instr.ALU_SRL (EVar 10) (ELit 3)), (2147450880), ELit 34); ((EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (267)) (ELit 3)), (2147450880), ELit 1); ((EVar 11), (0), ELit 24)] [((EVar 10), (0), ELit 272)] [(1433600, 1466368)].
Definition SCELLS : list (Z * Z * Z) := [(1497016, 8, 2147450880)].
Definition GLO : Z := 1433600.
Definition GHI : Z := 1466368.
Definition CSUMS : list CA.callsum := [CAXA.xs_cs (CAXA.XSA (CAX.XSUM 527108 2560 0%nat (fun regs _ => Some (nth 10 regs (ELit 0))) (fun regs => [((nth 10 regs (ELit 0)), 0, (nth 12 regs (ELit 0)))]) (fun _ BL => BL) (fun regs _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)] ++ [KZero (SA (nth 10 regs (ELit 0)) 0) (nth 12 regs (ELit 0))], BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1227132 10240 0%nat (fun _ _ => None) (fun regs => [((nth 10 regs (ELit 0)), 0, ELit 8); ((ELit 0), 6946368, ELit 2); ((ELit 0), 6947008, ELit 2); ((ELit 0), 6947024, ELit 504); ((ELit 0), 6947704, ELit 1152); ((ELit 0), 6950696, ELit 96); ((ELit 0), 7084256, ELit 544); ((ELit 0), 7084835, ELit 1); ((ELit 0), 7085056, ELit 4)]) (fun _ BL => BL) (fun regs _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)] ++ [KWord (SA (nth 10 regs (ELit 0)) 0) 8 (ELit 6948560)], BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 528300 2560 0%nat (fun regs _ => Some (nth 10 regs (ELit 0))) (fun regs => [((nth 10 regs (ELit 0)), 0, (nth 12 regs (ELit 0)))]) (fun _ BL => BL) (fun regs _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)] ++ [KZero (SA (nth 10 regs (ELit 0)) 0) (nth 12 regs (ELit 0))], BLk)) (fun F => F)) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 1429232 4112 0%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880); KRange (EVar (g + 4)) 4096 140737479966719; KAlign (EVar (g + 4)) 16; KUnk (SA (EVar (g + 4)) 0) (nth 10 regs (ELit 0)); KWr (SA (EVar (g + 4)) 0) (nth 10 regs (ELit 0)); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 4)) 0) (nth 10 regs (ELit 0)); KDisj (SA (ELit 0) (1433600)) (ELit 36864) (SA (EVar (g + 4)) 0) (nth 10 regs (ELit 0)); KDisj (SA (ELit 0) (1497016)) (ELit 8) (SA (EVar (g + 4)) 0) (nth 10 regs (ELit 0)); KDisj (SA (EVar (g + 4)) 0) (nth 10 regs (ELit 0)) (SA (EVar 10) (0)) (ELit 272); KDisj (SA (EVar (g + 4)) 0) (nth 10 regs (ELit 0)) (SA (EVar 11) (0)) (ELit 24); KDisj (SA (EVar (g + 4)) 0) (nth 10 regs (ELit 0)) (SA (EVar 2) (-10752)) (ELit 10752)], ((EVar (g + 4)), (nth 10 regs (ELit 0))) :: BLk)) (fun F => F ++ [((APC.eadd (EVar 124) (EVar 33)), 0, ELit 1)])) (fun _ => [])); CAXA.xs_cs (CAXA.XSA (CAX.XSUM 527116 2560 0%nat (fun regs _ => Some (nth 10 regs (ELit 0))) (fun regs => [((nth 10 regs (ELit 0)), 0, (nth 12 regs (ELit 0)))]) (fun _ BL => BL) (fun regs _ _ BLk => ([KImg (1433600) (1466368); KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880)], BLk)) (fun F => F)) (fun _ => []))].
Definition XSTOPS : list Z := [].
Definition APART : list (expr * Z * expr) := CH.stack_reg HDECL :: CH.hd_crs HDECL ++ CH.hd_wrs HDECL.
(* [comment removed for export] *)
Definition t0 : CC.cutpoint := CC.CP 727572 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (ELit (8)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KZero (SA (ELit 0) 2147632185) (ELit 1);
   KZero (SA (ELit 0) 2147632186) (ELit 1);
   KZero (SA (ELit 0) 2147632188) (ELit 1);
   KUnk (SA (EVar 10) (0)) (ELit (272));
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7094272) (140737488351232);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (267)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KWord (SA (EVar 11) (8)) 8 (EVar 33);
   KWord (SA (EVar 11) (16)) 8 (EVar 34);
   KRange (EVar 11) (7094272) (140737488351232);
   KAlign (EVar 11) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-10752)) (ELit (10752));
   KWr (SA (EVar 2) (-10752)) (ELit (10752));
   KRange (EVar 2) (140735332493824) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-10752)) (ELit (10752)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-10752)) (ELit (10752)) (SA (EVar 11) (0)) (ELit (24));
   KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_ADD (EVar 10) (ELit 80)) (EVar 11)) (ELit 1)) (0) (0);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6946368)) (ELit 2);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6947008)) (ELit 2);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6947024)) (ELit 504);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6947704)) (ELit 1152);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6950696)) (ELit 96);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (7084256)) (ELit 544);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (7084835)) (ELit 1);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (7085056)) (ELit 4);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6946368)) (ELit 2);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6947008)) (ELit 2);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6947024)) (ELit 504);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6947704)) (ELit 1152);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6950696)) (ELit 96);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (7084256)) (ELit 544);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (7084835)) (ELit 1);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (7085056)) (ELit 4);
   KRange (EAlu Instr.ALU_AND (EExt false 0%nat 1%nat (EVar 32)) (ELit 1)) (0) (0)]
  40 [((EVar 2), (-10752), ELit 10752); ((EVar 10), (0), ELit 272)] [] (ELit (24)).
Definition BL0 : CA.blocks := [].
Definition hints0 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t1 : CC.cutpoint := CC.CP 727572 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (ELit (8)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KZero (SA (ELit 0) 2147632185) (ELit 1);
   KZero (SA (ELit 0) 2147632186) (ELit 1);
   KZero (SA (ELit 0) 2147632188) (ELit 1);
   KUnk (SA (EVar 10) (0)) (ELit (272));
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7094272) (140737488351232);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (267)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KWord (SA (EVar 11) (8)) 8 (EVar 33);
   KWord (SA (EVar 11) (16)) 8 (EVar 34);
   KRange (EVar 11) (7094272) (140737488351232);
   KAlign (EVar 11) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-10752)) (ELit (10752));
   KWr (SA (EVar 2) (-10752)) (ELit (10752));
   KRange (EVar 2) (140735332493824) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-10752)) (ELit (10752)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-10752)) (ELit (10752)) (SA (EVar 11) (0)) (ELit (24));
   KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_ADD (EVar 10) (ELit 80)) (EVar 11)) (ELit 1)) (0) (0);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6946368)) (ELit 2);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6947008)) (ELit 2);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6947024)) (ELit 504);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6947704)) (ELit 1152);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6950696)) (ELit 96);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (7084256)) (ELit 544);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (7084835)) (ELit 1);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (7085056)) (ELit 4);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6946368)) (ELit 2);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6947008)) (ELit 2);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6947024)) (ELit 504);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6947704)) (ELit 1152);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6950696)) (ELit 96);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (7084256)) (ELit 544);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (7084835)) (ELit 1);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (7085056)) (ELit 4);
   KRange (EAlu Instr.ALU_AND (EExt false 0%nat 1%nat (EVar 32)) (ELit 1)) (1) (1);
   KRange (EVar 34) (4096) (140737479966720);
   KAlign (EVar 34) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 34) (0)) (EVar 33);
   KDisj (SA (EVar 34) (0)) (EVar 33) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 34) (0)) (EVar 33) (SA (EVar 11) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-10752)) (ELit (10752)) (SA (EVar 34) (0)) (EVar 33);
   KRange (EVar 33) (23) (44)]
  40 [((EVar 2), (-10752), ELit 10752); ((EVar 10), (0), ELit 272)] [] (ELit (24)).
Definition BL1 : CA.blocks := [].
Definition hints1 : list (nat * CC.subst) := [].
(* [comment removed for export] *)
Definition t2 : CC.cutpoint := CC.CP 727572 [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; (ELit (8)); EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31]
  [KImg (1433600) (1466368);
   KWord (SA (ELit 0) 1497016) 8 (ELit 2147450880);
   KZero (SA (ELit 0) 2147632185) (ELit 1);
   KZero (SA (ELit 0) 2147632186) (ELit 1);
   KZero (SA (ELit 0) 2147632188) (ELit 1);
   KUnk (SA (EVar 10) (0)) (ELit (272));
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7094272) (140737488351232);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (267)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KWord (SA (EVar 11) (0)) 8 (EVar 32);
   KWord (SA (EVar 11) (8)) 8 (EVar 33);
   KWord (SA (EVar 11) (16)) 8 (EVar 34);
   KRange (EVar 11) (7094272) (140737488351232);
   KAlign (EVar 11) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (24));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (24));
   KUnk (SA (EVar 2) (-10752)) (ELit (10752));
   KWr (SA (EVar 2) (-10752)) (ELit (10752));
   KRange (EVar 2) (140735332493824) (140737488355328);
   KAlign (EVar 2) (16);
   KDisj (SA (EVar 2) (-10752)) (ELit (10752)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-10752)) (ELit (10752)) (SA (EVar 11) (0)) (ELit (24));
   KRange (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAlu Instr.ALU_ADD (EVar 10) (ELit 80)) (EVar 11)) (ELit 1)) (0) (0);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6946368)) (ELit 2);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6947008)) (ELit 2);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6947024)) (ELit 504);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6947704)) (ELit 1152);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (6950696)) (ELit 96);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (7084256)) (ELit 544);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (7084835)) (ELit 1);
   KDisj (SA (EVar 10) (0)) (ELit 272) (SA (ELit 0) (7085056)) (ELit 4);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6946368)) (ELit 2);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6947008)) (ELit 2);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6947024)) (ELit 504);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6947704)) (ELit 1152);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (6950696)) (ELit 96);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (7084256)) (ELit 544);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (7084835)) (ELit 1);
   KDisj (SA (EVar 11) (0)) (ELit 24) (SA (ELit 0) (7085056)) (ELit 4);
   KRange (EAlu Instr.ALU_AND (EExt false 0%nat 1%nat (EVar 32)) (ELit 1)) (1) (1);
   KRange (EVar 34) (4096) (140737479966720);
   KAlign (EVar 34) (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 34) (0)) (EVar 33);
   KDisj (SA (EVar 34) (0)) (EVar 33) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 34) (0)) (EVar 33) (SA (EVar 11) (0)) (ELit (24));
   KDisj (SA (EVar 2) (-10752)) (ELit (10752)) (SA (EVar 34) (0)) (EVar 33);
   KRange (EVar 33) (45) (67108864)]
  40 [((EVar 2), (-10752), ELit 10752); ((EVar 10), (0), ELit 272)] [] (ELit (24)).
Definition BL2 : CA.blocks := [].
Definition hints2 : list (nat * CC.subst) := [].
Definition TMPL : list CC.cutpoint := [t0; t1; t2].
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 2000 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := match t with CC.TGoto j _ => (1, Z.of_nat j) | CC.TOther pc => (2, pc) end.
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint :=
  CC.CP (CC.cp_pc c) (CC.cp_regs c) (CC.cp_know c) (CC.cp_nx c) (CC.cp_F c) (map fst (CA.po_leaves o)) (CC.cp_meas c).
