(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth StartupPlan2Both StartupHS2Both BothCertDefs.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanStartupCertB () := "K6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP4cres01K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission2AS>AsanNodesWJoin3XNSK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5checkC5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages5ASEGSC5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs3ITBC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP4BOTHC5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs3NXBC5ARocqVerifyHarness?AgentSubmission2AS8AsanInit5LIMITC5ARocqVerifyHarness?AgentSubmission2AS;BothStartup3XE0C5ARocqVerifyHarness?AgentSubmission2AS;BothStartup3XB0C5ARocqVerifyHarness?AgentSubmission2AS=StartupHSBoth8HS_asanBC5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs3KC0C5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs5BFUELC5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs4FUELC5ARocqVerifyHarness?AgentSubmission2AS=StartupHSBoth;HS_asanA_10C5ARocqVerifyHarness?AgentSubmission2AS?StartupPlanBothAstartup_plan_segAI6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP4cres00C5ARocqVerifyHarness?AgentSubmission2AS<BothCertDefs>startup_shapeBI6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP7loopctx00".

Lemma startup_certB :
  check ASEGS ITB BOTH NXB AsanInit.LIMIT (XNS ASEGS BOTH NXB AsanInit.LIMIT) XE0 XB0 HS_asanB KC0 BFUEL FUEL None HS_asanA_10 startup_plan_segA = COk startup_shapeB.
Proof.
KReplay.run1 (kr_t_AsanStartupCertB ()) [] "p;1p;2p;4p;3p;?g0000j16Tg000jj25Tg001Dj40Tg002>j11Tg002`j32Tg003:l?3Tg0043R0g004og005gR1g006_R2g007WR3f1g008Mg009Dg00:;g00;9g00<1g00<kf0g00=dg00>eM?3p=4g00?nR4g00@h#6R5'5P0P1P2P3C0g00Ak#1'4=245do". Time Qed.
