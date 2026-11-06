(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS23 Require Import AsanTablesA AsanPlanImages.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS23 Require Import AsanStartup StartupPlanAsan StartupHSAsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanPlanFast AsanPlanFast2.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanStartupCert () := "C79OSSVerify5KrLib2K52AS=AsanPlanSound3APSDmk_itab_ranges_soundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23>AsanPlanImages5ASEGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?StartupPlanAsanCstartup_plan_rangesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K79OSSVerify5KrLib2K52AS8AsanPlan2AP4cres01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00C79OSSVerify5KrLib2K52AS=AsanPlanFast24APF2;check_fast2C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS=AsanPlanFast24APF2Dcheck_fast2_transferC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS23?AsanStartupCert3IT0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23;AsanTablesA6ASAN_AC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2K52AS8AsanPlan2AP3NX0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanInit5LIMITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23;AsanStartup3XN0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23;AsanStartup3XE0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23;AsanStartup3XB0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23=StartupHSAsan7HS_asanC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS23?AsanStartupCert3KC0C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS23?AsanStartupCert5BFUELC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS23?AsanStartupCert4FUELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23;AsanTablesA;asan_a_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K54AS23?StartupPlanAsan<startup_planC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS8AsanPlan2AP7loopctx00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54AS23?AsanStartupCert=startup_shapeC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K52AS8AsanPlan2AP4cres00C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 12000.   (* [comment removed for export] *)
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof.
KReplay.run1 (kr_t_AsanStartupCert ()) [] "p;2g0000j20Tg001Ag002B'0o". Qed.

Definition startup_shape : shape := (SHole 0).

Lemma startup_cert :
  check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 HS_asan KC0 BFUEL FUEL None asan_a_init startup_plan = COk startup_shape.
Proof.
KReplay.run1 (kr_t_AsanStartupCert ()) [] "p;1p;2p;3p;?p;Ag003Rj17Tg0044j16Tg0051j20Tg005Kj35Tg005el?3Tg006nlA4Tg001AR0g008@R1g009@R2g00:?R3g00;9R4g00<2R5g00<nR6g00=jR7g00>fR8g00?hR9g00@hR:g00AjR;f0R<g00BkR=g00CoR>M?3p=1P0P1P2P3P4P5P6P7P8P9P:P;f2P=P>f1P<MA4p=2g00E8#7R<g00F8#6R>g00GBR=/0>%1<=5=>d32o". Qed.
