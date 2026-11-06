(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "cons"; "list"; "nil"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "EC_P"; "ok_sideK"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_builder_dispose"; "bcP"; "Posts_bd"; "Pre_bd"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose"; "NP"; "P0_bd"; "tvL"; "BDC"; "Posts_bd"; "bd_chk_stmt"; "bd_ejcert_stmt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JG_pre"; "malloc_laws"; "malloc_contracts"; "malloc_contracts_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundR SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout MallocLaws Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV BuilderDispose.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition bcP : bd_code := ltac2:(tb__ "0|0|
S16Z16834Z17330S1S0Z16890S1S0Z168e4S1S0Z16938S1S0Z1698cS1S0Z169e0S1S0Z16a34S1S0Z16a88S1S0Z16adcS1S0Z16b30S1S0Z16b84S1S0Z16bd8S1S0Z16c2cS1S0Z16c80S1S0Z16cd4S1S0Z16d28S1S0Z16d7cS1S0Z16dd0S1S0Z16e24S1S0Z16e78S1S0Z16eccS1S0Z16f20S1S0Z16f74S1S0Z16fc8S1S0Z1701cS1S0Z17070S1S0Z170c4S1S0Z17118S1S0Z1716cS1S0Z171c0S1S0Z17214S1S0Z17268S1S0Z172bcS1S0Z17310S3S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Z13858Z13864Z13878S3S11A1A7").

Lemma bd_chk_P : ltac2:(tb__ "0|0|
S18S5SaS6S7A4").
Proof. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose.bd_chk_stmt. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.fast_forallb. Qed.
Lemma bd_ejcert_P : ltac2:(tb__ "0|0|
S19S5SaS7A3").
Proof. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.BuilderDispose.bd_ejcert_stmt. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.ejcert_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Definition Pre_bd : sstate := BuilderDispose.Pre_bd bcP.
Definition Posts_bd (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) := ltac2:(tb__ "0|0|
S17S5SaS6VKc;VFB;A5").

Theorem builder_dispose_sum : ltac2:(tb__ "0|0|
S20OF_;S2SeA1SdOF_;F_;S2S4S0S0A2A1S10S1bS5S6A2S8S5R5R4A3S1cS5S6S7A3S1fS5R7SfS5S1aS5S6R6S14R5S15U0A1A6ScR4A4S12S5S13R4SbR6R5A2A4A4F_;F_;F_;Frho0;FFB;FKc;Fok;").
Proof. exact (BuilderDispose.builder_dispose_sum segs bcP C_P EC_P bd_chk_P bd_ejcert_P). Qed.

Theorem builder_dispose_sum_ex : ltac2:(tb__ "0|0|
S2SeA1SdOF_;F_;S2S4S0S0A2A1S10S1bS5S6A2S9R4A1S1dS5S6S7A3S1eS5SfS5S1aS5S6R6S14R5S15U0A1A6ScR4A4S12S5S13R4SbR6R5A2A4A3F_;F_;F_;Frho0;FFB;FKc;").
Proof. exact (BuilderDispose.builder_dispose_sum_ex segs bcP C_P EC_P bd_chk_P bd_ejcert_P). Qed.
