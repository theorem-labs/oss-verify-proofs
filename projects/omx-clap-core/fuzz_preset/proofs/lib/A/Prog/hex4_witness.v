(* Theorem Labs, 2026-10: non-vacuity witness for the walk hypothesis `TL : PALibCore (PI := PI_prog_A) B` of
   lib/A/Prog/hex4_x.v (fuzz_preset's asan image A): it holds at TfibB, the image's asyms record (lib/A/AD2l.v), at the
   listing instance PI_prog_A (lib/A/PAImg_prog.v). *)
(* Modified by Theorem Labs, 2026-10: relocated to the #102 pin A' (asan 1be0f53d, unstripped twin bff8519bbe3e) from
   origin/cold/h-rw-pre-5-hex4m b371d41abbaa (blob dac26455166d); alreloc frozen-c4338d099cfb8025 moved 0 numerals.
   The walk's listing is now the #102 whole-program listing PI_prog_A (PAImg_prog.v 505a51ff7d08; the old per-function
   leaves listing PI_hex4 has no A' twin), and hex4_A_palib_core is the same vm_compute proof re-run at the A' tables
   (AD2l eb321db7a357, PAImg_prog 505a51ff7d08). ADDED hex4_holds_A: the bridge lib/A/Prog/S3_Hex4Bridge.v's hex4_holds
   at the A' instance (B := TfibB, ARx := h-mani-a8's ARcf at CfParams_preset), its three section hypotheses LAWS / TL
   / HW discharged by citing lib/A/PALibA.v 88c72c8175cf (palib_laws_A, palib_A, palib_head_A). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YG00 YG0f YG0d YCbq YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD2l.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* FULLY QUALIFIED image names (CrcBp's wrong-image trap, owner 19:2xZ). Locate in this file's context (pins102
   workspace of cf6f00470c9b): rsegs and Img0.rsegs resolve to lib.A.Img0.rsegs, PI_prog_A to lib.A.PAImg_prog.
   The names below are those full paths; hex4A_names_guard checks the short names against them by reflexivity. *)
#[local] Notation SEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.
#[local] Notation PI_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.PI_prog_A.
#[local] Notation TB_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AD2l.TfibB.
Lemma hex4_A_errno_img : forall a, as_errno TB_A <= a < as_errno TB_A + 4 -> in_img SEGS_A a.
Proof.
intros a Ha.
destruct (find_segment SEGS_A (as_errno TB_A) 4) as [sg|] eqn:Hf; [|vm_compute in Hf; discriminate Hf].
destruct (find_segment_hit SEGS_A (as_errno TB_A) 4 sg Hf) as (Hin & Hlo & Hhi).
exists sg. split; [exact Hin | lia].
Qed.
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem hex4_A_palib_core : PALibCore (PI := PI_A) TB_A.
Proof.
constructor.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- left. vm_compute. discriminate.
- split; [vm_compute; split; discriminate|]. split; [exact hex4_A_errno_img|].
  split; apply In_of_existsb; vm_compute; reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. split; reflexivity.
Qed.
Theorem hex4_A_palib_core_sat : exists B, PALibCore (PI := PI_A) B.
Proof. exists TB_A. exact hex4_A_palib_core. Qed.
End w.

(* the bridge at the A' instance *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI16 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnReader PALibA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S3_Hex4Bridge.
#[local] Notation PRH_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PRH_Img.prh_img_A.
Section g. Context {rc : YM05.RunCeil}.
Lemma hex4A_names_guard : rsegs = SEGS_A /\ Img0.rsegs = SEGS_A /\ @pa_segs _ _ PI_prog_A = SEGS_A /\
  @pa_segs _ _ PI_A = SEGS_A /\ prh_img_A = PRH_A /\ TfibB = TB_A.
Proof. repeat split; reflexivity. Qed.
End g.
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Theorem hex4_holds_A : forall SK : YI16.sink_head,
  thex4_specX (cp := CfParamsPreset.CfParams_preset) (PI := PRH_A) (PA := PI_A) TB_A
    (YG0ncf.ARcf (cp := CfParamsPreset.CfParams_preset) SEGS_A TB_A) SK.
Proof.
  intros SK.
  exact (hex4_holds (cp := CfParamsPreset.CfParams_preset) (HL := @cf_head CfParamsPreset.CfParams_preset)
    TB_A (YG0ncf.ARcf (cp := CfParamsPreset.CfParams_preset) SEGS_A TB_A) SK palib_laws_A palib_A palib_head_A).
Qed.
End i.
