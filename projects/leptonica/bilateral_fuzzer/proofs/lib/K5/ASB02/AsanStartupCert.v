(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import AsanTablesA AsanPlanImages.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.ASB02 Require Import AsanStartup StartupPlanAsan StartupHSAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanStartupCert () := "C79OSSVerify5KrLib2K52AS=AsanPlanSound3APSDmk_itab_ranges_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02>AsanPlanImages5ASEGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02?StartupPlanAsanCstartup_plan_rangesC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K52AS8AsanPlan2AP4cres01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C79OSSVerify5KrLib2K52AS8AsanPlan2AP5checkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanStartupCert3IT0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02;AsanTablesA6ASAN_AC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP3NX0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit5LIMITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02;AsanStartup3XN0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02;AsanStartup3XE0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02;AsanStartup3XB0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02=StartupHSAsan7HS_asanC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanStartupCert3KC0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanStartupCert5BFUELC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanStartupCert4FUELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02;AsanTablesA;asan_a_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K55ASB02?StartupPlanAsan<startup_planC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS8AsanPlan2AP4cres00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB02?AsanStartupCert=startup_shapeC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS8AsanPlan2AP7loopctx00C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof.
KReplay.run1 (kr_t_AsanStartupCert ()) [] "p;2g0000j20Tg001Ag002C'0o". Qed.

Definition startup_shape : shape := (SHole 0).

Lemma startup_cert :
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 HS_asan KC0 BFUEL FUEL None asan_a_init startup_plan = COk startup_shape.
Proof.
KReplay.run1 (kr_t_AsanStartupCert ()) [] "p;1p;2p;3p;?g003Tj15Tg004Qj24Tg004kj10Tg005Mj33Tg005gl?2Tg001Ag006cg007dg008dg009^g00:Wg00;Tg00<Qg00=Ng00>Qg00?Rg00@Uf0g00AWg00B\M?2p=1g00CfR0g00Dc#5R1'4g00En#0#1=301do". Qed.
