(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupHSAsan StartupPlan2Asan StartupHS2Asan AsanCertDefs.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanStartupCertH () := "K69OSSVerify5KrLib2AS8AsanPlan2AP4cres01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib2AS>AsanNodesWJoin3XNSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2AS8AsanPlan2AP5checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS>AsanPlanImages5ASEGSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<AsanCertDefs3IT0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP4ASANC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP3NX0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8AsanInit6LIMITHC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanStartup3XE0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS;AsanStartup3XB0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=StartupHSAsan8HS_asanAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<AsanCertDefs3KC0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<AsanCertDefs5BFUELC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<AsanCertDefs4FUELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2AS8AsanPlan2AP9asan_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS?StartupPlanAsan<startup_planC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS8AsanPlan2AP4cres00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS<AsanCertDefs=startup_shapeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2AS8AsanPlan2AP7loopctx00C1?~~~~~~~~~~~~~~~".

Lemma startup_cert_h :
  check ASEGS IT0 ASAN NX0 AsanInit.LIMITH (XNS ASEGS ASAN NX0 AsanInit.LIMITH) XE0 XB0 HS_asanA KC0 BFUEL FUEL None asan_init startup_plan = COk startup_shape.
Proof.
KReplay.run1 (kr_t_AsanStartupCertH ()) [] "p;1p;2p;4p;3p;?g0000j16Tg000jj25Tg001Dj40Tg002>j11Tg002`j32Tg003:l?3Tg0043R0g004og005gR1g006_R2g007VR3f1g008Mg009Dg00:;g00;9g00<1g00<kf0g00=dg00>aM?3p=4g00?eR4g00@_#6R5'5P0P1P2P3C0g00Aa#1'4=245do". Time Qed.
