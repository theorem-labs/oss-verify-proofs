(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's AsanAPI_cf (YGcfNames.v, Section API) at the second allocator instance,
   image B (asan-ubsan). The image-B twin of lib/A/CfApiPreset.v: the same three sections, the same fields and the
   same definitions, by this name map and no other change:
     CfImg_A (lib/A/CfImgA.v) -> CfImg_B (lib/AU/CfImgB.v);
     tfibsegs (lib/A/AB1v.v) -> tfibsegs (lib/Reusable/YB1v.v); TfibSyms (lib/A/AF0m.v) -> TfibSyms
       (lib/Reusable/YF0m.v), as lib/AU/FCapiCfB.v imports them;
     preset_aa_stack_malloc_cf / preset_aa_set_shadow_f5_cf (lib/A/FCapiCf.v) -> preset_aa_stack_malloc_cf_B /
       preset_aa_set_shadow_f5_cf_B (lib/AU/FCapiCfB.v);
     FF_preset / snp_K_A (lib/A/CfSnprintfPreset.v) -> FF_preset_B / snp_K_B (lib/AU/CfSnprintfPresetB.v);
       snp_cr is image-free and is CfSnprintfPreset.snp_cr;
     the relro range of the whole-program listing instance PI_prog_A over A_prog_listing (lib/A/PAImg_prog.v,
       lib/A/Listing_prog.v) -> PI_prog_B over B_prog_listing (lib/B/PAImg_prog.v, lib/B/Listing_prog.v);
     every name this file defines gets the suffix _B (pa_*_cf_B, PresetAsanAPI_cf_B, preset_api_open_cf_B,
       po_*_cf_B, preset_api_cf_B).
   CfParams := CfParams_preset (lib/A/CfParamsPreset.v) is image-free and is reused; each class instance is passed
   by name (ci := CfImg_B, cp := CfParams_preset), positionally with @, or inferred (ci at :184 and :191, from the AR_laws_ok_cf argument). The RunCeil is an explicit argument (the tree has no preset RunCeil instance).
   1. The record's predicate parameters are the real definitions. A field of AsanAPI_cf quantifies over the
      FPState (forall {fx}) but its predicate parameter cannot depend on it, so every fx-dependent definition is
      passed as `forall fx, <definition at fx>`: the field then states the contract at every FPState. The realloc
      pair takes a ghost set Hp and a pc in YGcfRealloc.v; the parameter is `forall Hp` at the realloc
      interceptor's entry cf_pc_wrap_realloc (YGcfRealloc.v:70-71). arealloc_null_realizes_cf names B, which the
      record's parameter (list Segment -> Prop) does not take, so the instance's B is captured.
      The strcmp / strlen contracts are c-libc-stdio's (YGcfStr.v): their predicates are the real definitions;
      their proofs are open arguments. The snprintf contract is a Theorem Labs lane's row YGcallSnp.asnprintf_realizes_xrom
      (by path from commit 193779166e07) at ARx := ARcf segs B, the form
      YGcallSnpCk.asnprintf_cf_of_xrom instantiates, at preset's format family, window and read-only ranges at image
      B (CfSnprintfPresetB.v), CfImg_B's canary cells and image range, and as the row's [rlo, rhi) (the relro range
      of PresetRodata.arodata_okP, lib/Spec/PresetRodata.v) the image's relro range pa_relro_lo / pa_relro_hi of
      PI_prog_B (lib/B/PAImg_prog.v, generated: B_prog_relro_lo / B_prog_relro_hi, the image's PT_GNU_RELRO), as
      the walks hold arodata_okP (PRH_Base.v fpre, B/Prog/FuzzStrdupB.v RLO / RHI). Its proof is an open argument.
   2. The fields with a proof in this tree are filled: aa_laws_cf (YG0lawscf.AR_laws_ok_cf), aa_model_cf
      (YG0ucf.model_laws_cf_ok, from universe_ok (as_universe B), the instance's premise HU), aa_stack_free_cf
      (YG0tcf.astack_free_law_ok_cf), and the frame-area pair from FCapiCfB.v: aa_stack_malloc_cf
      (preset_aa_stack_malloc_cf_B; [0; 1; 3] is cf_fs_classes CfParams_preset) and aa_set_shadow_f5_cf
      (preset_aa_set_shadow_f5_cf_B; FCimgB's SET_SHADOW_F5 and CfImg_B's cf_pc_set_shadow_f5 are the same numeral,
      so the two types convert), both from AR_laws_ok_cf and the image-symbol premise HT : TfibSyms B.
   3. Every other field is a walk result not proved here: preset_api_open_cf_B collects them, with the field types
      of AsanAPI_cf at this instance, and preset_api_cf_B takes it as an argument.
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG0ncf YG0dcf YG0d2cf YG0lawscf YG0ucf YG0tcf YGcfHp YGcfRealloc YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC4aP YGcallSnp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB FCapiCfB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfSnprintfPresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfSnprintfPreset.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfNames.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The record's predicate parameters at preset's instance, image B.             *)
Definition pa_laws_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
YG0dcf.AR_laws_cf (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) segs B.

Definition pa_model_cf_B : Univ -> Prop := @YG0ucf.model_laws_cf CfParams_preset CfImg_B.

Definition pa_malloc_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
forall fx : YK11.FPState, @YG0dcf.amalloc_realizes_cf fx rc CfImg_B CfParams_preset segs B.

Definition pa_free_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
forall fx : YK11.FPState, YG0dcf.afree_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) segs B.

Definition pa_stack_malloc_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (cid : Z) : Prop :=
forall fx : YK11.FPState, YG0dcf.astack_malloc_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) segs B cid.

Definition pa_stack_free_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
YG0dcf.astack_free_law_cf (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) segs B.

Definition pa_set_shadow_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc v : Z) : Prop :=
forall fx : YK11.FPState, YG0d2cf.aset_shadow_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) segs B pc v.

Definition pa_intrin_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (op : memop) (pc : Z) : Prop :=
forall fx : YK11.FPState, YG0d2cf.aintrin_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) segs B op pc.

Definition pa_memcmp_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YG0d2cf.amemcmp_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) segs B pc.

Definition pa_bcmp_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YG0d2cf.abcmp_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) segs B pc.

(* c-libc-stdio's strcmp / strlen contracts (YGcfStr.v), at every FPState. *)
Definition pa_strcmp_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YGcfStr.astrcmp_realizes_cf (fx:=fx) (rc:=rc) (ci:=CfImg_B) (cp:=CfParams_preset) segs B pc.
Definition pa_strlen_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YGcfStr.astrlen_realizes_cf (fx:=fx) (rc:=rc) (ci:=CfImg_B) (cp:=CfParams_preset) segs B pc.

(* c-omx-alloc's snprintf row at ARcf, preset's arguments at image B and the image's relro range, at every FPState. *)
Definition pa_snprintf_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YGcallSnp.asnprintf_realizes_xrom (fx:=fx) segs B
(YG0ncf.ARcf (rc:=rc) (ci:=CfImg_B) (cp:=CfParams_preset) segs B)
(@YC4aP.pa_relro_lo rc Listing_prog.B_prog_listing PAImg_prog.PI_prog_B)
(@YC4aP.pa_relro_hi rc Listing_prog.B_prog_listing PAImg_prog.PI_prog_B)
FF_preset_B snp_K_B (@cf_got_stack_chk_guard CfImg_B) (@cf_stack_chk_guard CfImg_B) (@cf_img_lo CfImg_B)
(@cf_img_top CfImg_B) (CfSnprintfPreset.snp_cr segs) pc.

Definition pa_realloc_null_cf_B (rc : YM05.RunCeil) (B : asyms) (segs : list Segment) : Prop :=
forall (fx : YK11.FPState) (Hp : list Z),
@YGcfRealloc.arealloc_null_realizes_cf fx rc CfImg_B CfParams_preset segs B Hp (@cf_pc_wrap_realloc CfImg_B).

Definition pa_poison_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
forall fx : YK11.FPState, @YGcfHp.apoison_realizes_cf fx rc CfImg_B CfParams_preset segs B.

Definition pa_unpoison_cf_B (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
forall fx : YK11.FPState, @YGcfHp.aunpoison_realizes_cf fx rc CfImg_B CfParams_preset segs B.

(* The record at preset's instance, image B. *)
Definition PresetAsanAPI_cf_B (rc : YM05.RunCeil) (B : asyms) : Set :=
@AsanAPI_cf CfImg_B CfParams_preset
(pa_laws_cf_B rc)
pa_model_cf_B
(pa_malloc_cf_B rc)
(pa_free_cf_B rc)
(pa_stack_malloc_cf_B rc)
(pa_stack_free_cf_B rc)
(pa_set_shadow_cf_B rc)
(pa_intrin_cf_B rc)
(pa_memcmp_cf_B rc)
(pa_bcmp_cf_B rc)
(pa_strcmp_cf_B rc)
(pa_strlen_cf_B rc)
(pa_realloc_null_cf_B rc B)
(pa_poison_cf_B rc)
(pa_unpoison_cf_B rc)
(pa_snprintf_cf_B rc)
tfibsegs B.

(* ---------------------------------------------------------------------------- *)
(* 2. The fields with no proof in this tree, with AsanAPI_cf's field types.         *)
Record preset_api_open_cf_B (rc : YM05.RunCeil) (B : asyms) : Set := {
po_malloc_cf_B : pa_malloc_cf_B rc tfibsegs B;
po_free_cf_B : pa_free_cf_B rc tfibsegs B;
po_realloc_null_cf_B : pa_realloc_null_cf_B rc B tfibsegs;
po_poison_cf_B : pa_poison_cf_B rc tfibsegs B;
po_unpoison_cf_B : pa_unpoison_cf_B rc tfibsegs B;
po_asan_memcpy_cf_B : pa_intrin_cf_B rc tfibsegs B OCpy (pc_asan_memcpy (as_code B));
po_asan_memset_cf_B : pa_intrin_cf_B rc tfibsegs B OSet (pc_asan_memset (as_code B));
po_memcpy_icpt_cf_B : pa_intrin_cf_B rc tfibsegs B OCpy (pc_wrap_memcpy (as_code B));
po_memset_icpt_cf_B : pa_intrin_cf_B rc tfibsegs B OSet (pc_wrap_memset (as_code B));
po_memcmp_cf_B : pa_memcmp_cf_B rc tfibsegs B (pc_wrap_memcmp (as_code B));
po_bcmp_cf_B : pa_bcmp_cf_B rc tfibsegs B (pc_wrap_bcmp (as_code B));
po_strcmp_cf_B : pa_strcmp_cf_B rc tfibsegs B (@cf_pc_strcmp CfImg_B);
po_strlen_cf_B : pa_strlen_cf_B rc tfibsegs B (@cf_pc_strlen CfImg_B);
po_snprintf_cf_B : pa_snprintf_cf_B rc tfibsegs B (@cf_pc_snprintf CfImg_B)
}.

(* ---------------------------------------------------------------------------- *)
(* 3. The instance: the proved fields filled, the open ones taken from X.          *)
Definition preset_api_cf_B (rc : YM05.RunCeil) (B : asyms) (HU : universe_ok (as_universe B)) (HT : TfibSyms B)
(X : preset_api_open_cf_B rc B) : PresetAsanAPI_cf_B rc B :=
@Build_AsanAPI_cf CfImg_B CfParams_preset
(pa_laws_cf_B rc)
pa_model_cf_B
(pa_malloc_cf_B rc)
(pa_free_cf_B rc)
(pa_stack_malloc_cf_B rc)
(pa_stack_free_cf_B rc)
(pa_set_shadow_cf_B rc)
(pa_intrin_cf_B rc)
(pa_memcmp_cf_B rc)
(pa_bcmp_cf_B rc)
(pa_strcmp_cf_B rc)
(pa_strlen_cf_B rc)
(pa_realloc_null_cf_B rc B)
(pa_poison_cf_B rc)
(pa_unpoison_cf_B rc)
(pa_snprintf_cf_B rc)
tfibsegs B
(fun _ : YK11.FPState => AR_laws_ok_cf (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) tfibsegs B)
(@model_laws_cf_ok CfParams_preset CfImg_B (as_universe B) HU)
(fun _ : YK11.FPState => @po_malloc_cf_B rc B X)
(fun _ : YK11.FPState => @po_free_cf_B rc B X)
(fun (_ : YK11.FPState) (cid : Z) (Hc : In cid (@cf_fs_classes CfParams_preset)) (fx : YK11.FPState) =>
  preset_aa_stack_malloc_cf_B (fx:=fx) (rc:=rc) (cp:=CfParams_preset) B
    (AR_laws_ok_cf (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) tfibsegs B) HT cid Hc)
(fun _ : YK11.FPState => astack_free_law_ok_cf (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) tfibsegs B)
(fun _ : YK11.FPState => @po_realloc_null_cf_B rc B X)
(fun _ : YK11.FPState => @po_poison_cf_B rc B X)
(fun _ : YK11.FPState => @po_unpoison_cf_B rc B X)
(fun (_ : YK11.FPState) (fx : YK11.FPState) =>
  preset_aa_set_shadow_f5_cf_B (fx:=fx) (rc:=rc) (cp:=CfParams_preset) B
    (AR_laws_ok_cf (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) tfibsegs B) HT)
(fun _ : YK11.FPState => @po_asan_memcpy_cf_B rc B X)
(fun _ : YK11.FPState => @po_asan_memset_cf_B rc B X)
(fun _ : YK11.FPState => @po_memcpy_icpt_cf_B rc B X)
(fun _ : YK11.FPState => @po_memset_icpt_cf_B rc B X)
(fun _ : YK11.FPState => @po_memcmp_cf_B rc B X)
(fun _ : YK11.FPState => @po_bcmp_cf_B rc B X)
(fun _ : YK11.FPState => @po_strcmp_cf_B rc B X)
(fun _ : YK11.FPState => @po_strlen_cf_B rc B X)
(fun _ : YK11.FPState => @po_snprintf_cf_B rc B X).
