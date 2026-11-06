(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's AsanAPI_cf (YGcfNames.v, Section API) at the second allocator instance,
   image A: segs := tfibsegs (AB1v.v), CfImg := CfImg_A (CfImgA.v), CfParams := CfParams_preset (CfParamsPreset.v),
   each class instance passed by name (ci := CfImg_A, cp := CfParams_preset), positionally with @, inferred (ci at :171 and :177, from the AR_laws_ok_cf argument), or, in Section PV (:195-197), ci from the Section context and cp from the local CfParams_preset instance. The RunCeil is an explicit argument (the tree has no preset
   RunCeil instance).
   1. The record's predicate parameters are the real definitions. A field of AsanAPI_cf quantifies over the
      FPState (forall {fx}) but its predicate parameter cannot depend on it, so every fx-dependent definition is
      passed as `forall fx, <definition at fx>`: the field then states the contract at every FPState. The realloc
      pair takes a ghost set Hp and a pc in YGcfRealloc.v; the parameter is `forall Hp` at the realloc
      interceptor's entry cf_pc_wrap_realloc (YGcfRealloc.v:70-71). arealloc_null_realizes_cf names B, which the
      record's parameter (list Segment -> Prop) does not take, so the instance's B is captured.
      The strcmp / strlen contracts are c-libc-stdio's (YGcfStr.v, by path from commit
      3e37c5476fed): their predicates are the real definitions; their proofs are open arguments. The snprintf
      contract is c-omx-alloc's row YGcallSnp.asnprintf_realizes_xrom (by path from commit
      193779166e07) at ARx := ARcf segs B, the form YGcallSnpCk.asnprintf_cf_of_xrom instantiates, at preset's
      format family, window and read-only ranges (CfSnprintfPreset.v), CfImg_A's canary cells and image range, and
     as the row's [rlo, rhi) (the relro range of PresetRodata.arodata_okP, lib/Spec/PresetRodata.v) the image's
      relro range pa_relro_lo / pa_relro_hi of the whole-program listing instance PI_prog_A (lib/A/PAImg_prog.v,
      generated: A_prog_relro_lo / A_prog_relro_hi, the image's PT_GNU_RELRO), as the walks hold arodata_okP
      (PRH_Base.v fpre, Prog/FuzzStrdup.v RLO / RHI). Its proof is an open argument.
   2. The fields with a proof in this tree are filled: aa_laws_cf (YG0lawscf.AR_laws_ok_cf), aa_model_cf
      (YG0ucf.model_laws_cf_ok, from universe_ok (as_universe B), the instance's premise HU), aa_stack_free_cf
      (YG0tcf.astack_free_law_ok_cf), and the frame-area pair from h-hpreset-7's FCapiCf.v (merged at
      52a7fffa7133): aa_stack_malloc_cf (preset_aa_stack_malloc_cf; [0; 1; 3] is cf_fs_classes CfParams_preset)
      and aa_set_shadow_f5_cf (preset_aa_set_shadow_f5_cf; FCimg's SET_SHADOW_F5 and CfImg_A's
      cf_pc_set_shadow_f5 are the same numeral, so the two types convert), both from AR_laws_ok_cf and the
      image-symbol premise HT : TfibSyms B.
   3. Every other field is a walk result not proved here: preset_api_open_cf collects them, with the field types
      of AsanAPI_cf at this instance, and preset_api_cf takes it as an argument.
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YA0n YM05 YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG0ncf YG0dcf YG0d2cf YG0lawscf YG0ucf YG0tcf YGcfHp YGcfRealloc YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC4aP YGcallSnp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m CfImgA CfParamsPreset FCapiCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfSnprintfPreset.
(* stdpp, through the LPS modules, shadows several list names; In here is Stdlib's, as in YGcfNames.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The record's predicate parameters at preset's instance.                      *)
Definition pa_laws_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
YG0dcf.AR_laws_cf (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) segs B.

Definition pa_model_cf : Univ -> Prop := @YG0ucf.model_laws_cf CfParams_preset CfImg_A.

Definition pa_malloc_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
forall fx : YK11.FPState, @YG0dcf.amalloc_realizes_cf fx rc CfImg_A CfParams_preset segs B.

Definition pa_free_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
forall fx : YK11.FPState, YG0dcf.afree_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) segs B.

Definition pa_stack_malloc_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (cid : Z) : Prop :=
forall fx : YK11.FPState, YG0dcf.astack_malloc_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) segs B cid.

Definition pa_stack_free_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
YG0dcf.astack_free_law_cf (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) segs B.

Definition pa_set_shadow_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc v : Z) : Prop :=
forall fx : YK11.FPState, YG0d2cf.aset_shadow_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) segs B pc v.

Definition pa_intrin_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (op : memop) (pc : Z) : Prop :=
forall fx : YK11.FPState, YG0d2cf.aintrin_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) segs B op pc.

Definition pa_memcmp_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YG0d2cf.amemcmp_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) segs B pc.

Definition pa_bcmp_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YG0d2cf.abcmp_realizes_cf (fx := fx) (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) segs B pc.

(* c-libc-stdio's strcmp / strlen contracts (YGcfStr.v), at every FPState. *)
Definition pa_strcmp_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YGcfStr.astrcmp_realizes_cf (fx:=fx) (rc:=rc) (ci:=CfImg_A) (cp:=CfParams_preset) segs B pc.
Definition pa_strlen_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YGcfStr.astrlen_realizes_cf (fx:=fx) (rc:=rc) (ci:=CfImg_A) (cp:=CfParams_preset) segs B pc.

(* c-omx-alloc's snprintf row at ARcf, preset's arguments and the image's relro range, at every FPState. *)
Definition pa_snprintf_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) (pc : Z) : Prop :=
forall fx : YK11.FPState, YGcallSnp.asnprintf_realizes_xrom (fx:=fx) segs B
(YG0ncf.ARcf (rc:=rc) (ci:=CfImg_A) (cp:=CfParams_preset) segs B)
(@YC4aP.pa_relro_lo rc Listing_prog.A_prog_listing PAImg_prog.PI_prog_A)
(@YC4aP.pa_relro_hi rc Listing_prog.A_prog_listing PAImg_prog.PI_prog_A)
FF_preset snp_K_A (@cf_got_stack_chk_guard CfImg_A) (@cf_stack_chk_guard CfImg_A) (@cf_img_lo CfImg_A)
(@cf_img_top CfImg_A) (snp_cr segs) pc.

Definition pa_realloc_null_cf (rc : YM05.RunCeil) (B : asyms) (segs : list Segment) : Prop :=
forall (fx : YK11.FPState) (Hp : list Z),
@YGcfRealloc.arealloc_null_realizes_cf fx rc CfImg_A CfParams_preset segs B Hp (@cf_pc_wrap_realloc CfImg_A).

Definition pa_poison_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
forall fx : YK11.FPState, @YGcfHp.apoison_realizes_cf fx rc CfImg_A CfParams_preset segs B.

Definition pa_unpoison_cf (rc : YM05.RunCeil) (segs : list Segment) (B : asyms) : Prop :=
forall fx : YK11.FPState, @YGcfHp.aunpoison_realizes_cf fx rc CfImg_A CfParams_preset segs B.

(* The record at preset's instance. *)
Definition PresetAsanAPI_cf (rc : YM05.RunCeil) (B : asyms) : Set :=
@AsanAPI_cf CfImg_A CfParams_preset
(pa_laws_cf rc)
pa_model_cf
(pa_malloc_cf rc)
(pa_free_cf rc)
(pa_stack_malloc_cf rc)
(pa_stack_free_cf rc)
(pa_set_shadow_cf rc)
(pa_intrin_cf rc)
(pa_memcmp_cf rc)
(pa_bcmp_cf rc)
(pa_strcmp_cf rc)
(pa_strlen_cf rc)
(pa_realloc_null_cf rc B)
(pa_poison_cf rc)
(pa_unpoison_cf rc)
(pa_snprintf_cf rc)
tfibsegs B.

(* ---------------------------------------------------------------------------- *)
(* 2. The fields with no proof in this tree, with AsanAPI_cf's field types.         *)
Record preset_api_open_cf (rc : YM05.RunCeil) (B : asyms) : Set := {
po_malloc_cf : pa_malloc_cf rc tfibsegs B;
po_free_cf : pa_free_cf rc tfibsegs B;
po_realloc_null_cf : pa_realloc_null_cf rc B tfibsegs;
po_poison_cf : pa_poison_cf rc tfibsegs B;
po_unpoison_cf : pa_unpoison_cf rc tfibsegs B;
po_asan_memcpy_cf : pa_intrin_cf rc tfibsegs B OCpy (pc_asan_memcpy (as_code B));
po_asan_memset_cf : pa_intrin_cf rc tfibsegs B OSet (pc_asan_memset (as_code B));
po_memcpy_icpt_cf : pa_intrin_cf rc tfibsegs B OCpy (pc_wrap_memcpy (as_code B));
po_memset_icpt_cf : pa_intrin_cf rc tfibsegs B OSet (pc_wrap_memset (as_code B));
po_memcmp_cf : pa_memcmp_cf rc tfibsegs B (pc_wrap_memcmp (as_code B));
po_bcmp_cf : pa_bcmp_cf rc tfibsegs B (pc_wrap_bcmp (as_code B));
po_strcmp_cf : pa_strcmp_cf rc tfibsegs B (@cf_pc_strcmp CfImg_A);
po_strlen_cf : pa_strlen_cf rc tfibsegs B (@cf_pc_strlen CfImg_A);
po_snprintf_cf : pa_snprintf_cf rc tfibsegs B (@cf_pc_snprintf CfImg_A)
}.

(* ---------------------------------------------------------------------------- *)
(* 3. The instance: the proved fields filled, the open ones taken from X.          *)
Definition preset_api_cf (rc : YM05.RunCeil) (B : asyms) (HU : universe_ok (as_universe B)) (HT : TfibSyms B)
(X : preset_api_open_cf rc B) : PresetAsanAPI_cf rc B :=
@Build_AsanAPI_cf CfImg_A CfParams_preset
(pa_laws_cf rc)
pa_model_cf
(pa_malloc_cf rc)
(pa_free_cf rc)
(pa_stack_malloc_cf rc)
(pa_stack_free_cf rc)
(pa_set_shadow_cf rc)
(pa_intrin_cf rc)
(pa_memcmp_cf rc)
(pa_bcmp_cf rc)
(pa_strcmp_cf rc)
(pa_strlen_cf rc)
(pa_realloc_null_cf rc B)
(pa_poison_cf rc)
(pa_unpoison_cf rc)
(pa_snprintf_cf rc)
tfibsegs B
(fun _ : YK11.FPState => AR_laws_ok_cf (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) tfibsegs B)
(@model_laws_cf_ok CfParams_preset CfImg_A (as_universe B) HU)
(fun _ : YK11.FPState => @po_malloc_cf rc B X)
(fun _ : YK11.FPState => @po_free_cf rc B X)
(fun (_ : YK11.FPState) (cid : Z) (Hc : In cid (@cf_fs_classes CfParams_preset)) (fx : YK11.FPState) =>
  preset_aa_stack_malloc_cf (fx:=fx) (rc:=rc) (cp:=CfParams_preset) B (AR_laws_ok_cf (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) tfibsegs B) HT cid Hc)
(fun _ : YK11.FPState => astack_free_law_ok_cf (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) tfibsegs B)
(fun _ : YK11.FPState => @po_realloc_null_cf rc B X)
(fun _ : YK11.FPState => @po_poison_cf rc B X)
(fun _ : YK11.FPState => @po_unpoison_cf rc B X)
(fun (_ : YK11.FPState) (fx : YK11.FPState) =>
  preset_aa_set_shadow_f5_cf (fx:=fx) (rc:=rc) (cp:=CfParams_preset) B (AR_laws_ok_cf (rc := rc) (ci := CfImg_A) (cp := CfParams_preset) tfibsegs B) HT)
(fun _ : YK11.FPState => @po_asan_memcpy_cf rc B X)
(fun _ : YK11.FPState => @po_asan_memset_cf rc B X)
(fun _ : YK11.FPState => @po_memcpy_icpt_cf rc B X)
(fun _ : YK11.FPState => @po_memset_icpt_cf rc B X)
(fun _ : YK11.FPState => @po_memcmp_cf rc B X)
(fun _ : YK11.FPState => @po_bcmp_cf rc B X)
(fun _ : YK11.FPState => @po_strcmp_cf rc B X)
(fun _ : YK11.FPState => @po_strlen_cf rc B X)
(fun _ : YK11.FPState => @po_snprintf_cf rc B X).

(* ---------------------------------------------------------------------------- *)
(* 4. The shadow byte after the head of a block that is all head is visible: the  *)
(*    fact __asan_poison_memory_region / __asan_unpoison_memory_region (p, 16)     *)
(*    read, c-omx-alloc's stand-in (commit 6e9844d19ad2,                           *)
(*    lib/A/CfPoison.v:183 and lib/AU/CfPoisonB.v:189), in its text and argument   *)
(*    order. YGcfHp.poison_next_vis_cf_le16 at preset's cf_head = 16 <= 16; segs   *)
(*    and the image class are generic, so image B uses the same lemma.             *)
Section PV.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Variable segs : list Segment.
Variable B : asyms.
Lemma poison_next_vis_cf : forall ly S Hp (W : world segs) mem md p n,
  ARcf segs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> req_size n = cf_head ->
  aview segs (w_H W) mem (shadow_addr (p + cf_head)) <> None.
Proof.
intros ly S Hp W mem md p n HAR Hb Heq.
assert (A16 : cf_head = 16) by reflexivity.
exact (YGcfHp.poison_next_vis_cf_le16 segs B ly S Hp W mem md p n HAR Hb Heq ltac:(rewrite A16; lia)).
Qed.
End PV.
