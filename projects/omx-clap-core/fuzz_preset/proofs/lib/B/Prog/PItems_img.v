(* Theorem Labs, 2026-10: the CLOSED IMAGE FACTS parse_items' image-B segments take as named Section hypotheses, each
   proved here at the instance of record (lane PItemsB, owner; a Theorem Labs lane's audit 10:1xZ: every such hypothesis is
   either a closed image fact or a call-state premise). The segment files stay parametric in {PIi : PrhImg} and
   {cp : CfParams}; the top instantiates PIi := prh_img_B, cp := CfParams_preset and discharges:
     FRPI  (PItems_body_free.v, PItems_value.v)   by pii_frpi   (lib/B/PRH_ImgB.v:74, pi_frame F_parse_items = 144)
     FS0   (PItems_body_free.v)                   by pii_fs0    (lib/B/PRH_ImgB.v:380, pi_s0cur F_parse_items = Some 16)
     FSITE (PItems_body_free.v)                   by pii_fsite  (lib/B/PRH_ImgB.v:162, the free site 0x87f34)
     PIF_PSTRO / PIK_PSTRO / HPSTRO               by pii_pstro  (lib/B/Prog/S1ImgB.v pst_not_ro_B)
     HW : prh_head_wide                           by pii_hw     (lib/A/CfParamsPreset.v:95 preset_head_wide)
   The live class-24 count (fuzz_free's ccnt24 premise) is NOT an image fact: it is a cut premise of pi_free_pre
   (PItems_pres.v), discharged by the kit's batch (iface_room_pos + counts_of_room_pos_rl).
   Rule 24: proves no function (kind: image facts). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YM05 YI16 YP0b YC4aP YPsym YGcfNames YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB PItems_defs.
Import ListNotations.
Local Open Scope Z_scope.

Section img. Context {rc : YM05.RunCeil}.

(* parse_items' frame on image B is the listing's `addi sp, sp, -144` *)
Lemma pii_frpi : @PRH_Base.pi_frame prh_img_B F_parse_items = PI_FRAME.
Proof. reflexivity. Qed.

(* parse_items sets s0 = q + 16 (B 0x87ab8 `addi s0, s1, 16`) *)
Lemma pii_fs0 : @pi_s0cur prh_img_B F_parse_items = Some 16.
Proof. reflexivity. Qed.

(* grow sets s0 = v + 48 (B 0x870b8 `addi s0, s1, 48`; PItemsBody.Loop's PIL_S0G) *)
Lemma pii_s0g : @pi_s0cur prh_img_B F_grow = Some 48.
Proof. reflexivity. Qed.

(* parse_string's s0 is a0 + 0 (PItemsBody.Key's PIK_S0STR; PRH_ImgB.v:379) *)
Lemma pii_s0str : @pi_s0cur prh_img_B F_parse_string = Some 0.
Proof. reflexivity. Qed.

(* every frame length is a length (PItemsBody.Key's PIK_FR0; the PrhImg field pi_frame_nonneg, PRH_ImgB.v:386) *)
Lemma pii_fr0 : forall F, 0 <= @PRH_Base.pi_frame prh_img_B F.
Proof. exact (@pi_frame_nonneg prh_img_B). Qed.

(* the return site of the missing-colon `jal fuzz_free` (B 0x87f30) is parse_items' one fuzz_free site, 0x87f34 *)
Lemma pii_fsite : In (@pa_val _ B_prog_listing PI_prog_B A_TEXT + @PI_AT _ B_prog_listing PI_prog_B PI_O_FFREE + 4)
  (@pi_ret_sites prh_img_B F_parse_items RT_fuzz_free).
Proof. unfold PI_AT. vm_compute. left. reflexivity. Qed.

(* the program's statics are not read-only *)
Lemma pii_pstro : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ in_roP (@pa_segs _ B_prog_listing PI_prog_B) (@pa_relro_lo _ _ PI_prog_B) (@pa_relro_hi _ _ PI_prog_B) a.
Proof. intros a Ha. exact (pst_not_ro_B a Ha). Qed.

(* the program's statics lie in the image (PItemsBody.Loop's PIL_PSTIMG; S1ImgB.v pst_in_img_B) *)
Lemma pii_pstimg : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> in_img (@pa_segs _ B_prog_listing PI_prog_B) a.
Proof. intros a Ha. exact (pst_in_img_B a Ha). Qed.

(* the harness hides a head of at least one word *)
Lemma pii_hw : @prh_head_wide CfParams_preset.
Proof. exact preset_head_wide. Qed.

End img.
