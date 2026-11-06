(* fuzz_preset, #102 re-walk row T9 (the internal file FREE-PIECES-102.md Part 7a), file CrtImgB102: the B' IMAGE FACTS of
   check_round_trip at the CONCRETE B instance PI_prog_B (lib/B/PAImg_prog.v:402). Crt102ImgB.v Section b proves them
   over any {PA : PAImg B_prog_listing} from five hypotheses (HB_base, HB_entry, HB_segs, HB_relro, HB_hi); here each
   hypothesis is a closed lemma at PI_prog_B, and each Section-b lemma is instantiated with them, so the cut pcs, the
   two literals (MOD_AT / STAMP), the GOT pairs and the image facts hold at PI_prog_B with no premise left.

   INPUTS OF RECORD:
   - branch base: commit 5eb767764d9 (lib/A/Prog/Crt102Img.v blob c6521f7e9afa).
   - IMG_TOP_B := 0x601000, lib/Reusable/YImgTop.v:23 of RECORD, taken by path from the B' line
     commit a9548e31002 (generated from the ELF, guard img_bounds_same retired; the unit owner's 16:55Z ruling): it lets
     lib/B/PAImg_prog.v (B_prog_range) build. The earlier type-check used the non-record
     no-guard 8861a3317cf blob; the guarded 437b1552e7f blob fails at its own :32
     (img_bounds_same: "Unable to unify IMG_TOP with IMG_TOP_B").
   - pins: B' asan-ubsan d663f82d7f488d30 (unstripped twin c90d4fa54d43160b).
   - build route pins102: the internal file zfb-targets.dc6f8f60073340be.sh, FACTS 8f3e7e1a07f1, PAU
     the #102 pin set (pau-preset-102).
   - rule 24: no function proved (proof-index check_round_trip 0x82828 0x816cc, exit 4,
     the lookup record, the internal file lookup-T9.txt): only the plain (lib/Prog) and ubsan (lib/U/Prog) proofs.
     Written new.

   HOW EACH HYPOTHESIS IS DISCHARGED AT PI_prog_B:
   - HB_base_cf  : vm_compute (pa_val A_TEXT = B_prog_val A_TEXT = B_prog_base).
   - HB_entry_cf : vm_compute (pa_sigma AS_check_round_trip = 0x82828 = B_prog_base + 4 * 1111).
   - HB_segs_cf  : reflexivity (the instance's pa_segs field is rsegs of lib/B/Img0.v; no evaluation of the segments).
   - HB_relro_cf : S1ImgB.pst_not_ro_B (its pst_ro_b_B is vm_compute over prh_img_B's statics and the relro range).
   - HB_hi_cf    : pa_hi is IMG_TOP_B = 0x601000 (YImgTop.v), lia.

   crt102_cap / crt102_smx (Crt102Img.v:275 / :288) name no image: the capacity bound reads the text's frames bound
   (ck_FRAMES_CAP, FR_check_round_trip) and fs_frames 3, and the existential quantifies segs. They serve B' as stated;
   no B' copy is made. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YP0m YP02 YP0b YPsym YImgTop YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Img0 PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PIB := (B.PAImg_prog.PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PIB).
#[local] Notation VAL := (@pa_val _ B_prog_listing PIB).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PIB).
#[local] Notation BASE := (@pa_val _ B_prog_listing PIB A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PIB).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PIB).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation AT o := (BASE + (CRT_PC_B + o)).
#[local] Notation MOD_AT := (CRT_MOD_AT_B (PA := PIB)).
#[local] Notation STAMP := (CRT_STAMP_B (PA := PIB)).

(* ---- the five Section-b hypotheses, closed at PI_prog_B ---- *)
Lemma HB_base_cf : BASE = B_prog_base.
Proof. vm_compute. reflexivity. Qed.
Lemma HB_entry_cf : SIGMA AS_check_round_trip = B_prog_base + CRT_PC_B.
Proof. vm_compute. reflexivity. Qed.
Lemma HB_segs_cf : SEGS = B.Img0.rsegs.
Proof. reflexivity. Qed.
Lemma HB_relro_cf : forall a, Exists (in_zr a) PST -> ~ (RLO <= a < RHI).
Proof. intros a Ha Hr. exact (S1ImgB.pst_not_ro_B a Ha (or_intror Hr)). Qed.
Lemma HB_hi_cf : @pa_hi _ B_prog_listing PIB <= 2 ^ 31.
Proof. change (@pa_hi _ _ PIB) with IMG_TOP_B. unfold IMG_TOP_B. lia. Qed.

(* each Section-b lemma takes the hypotheses its proof uses, in declaration order; hb closes whichever is asked *)
Local Ltac hb := first [exact HB_base_cf | exact HB_entry_cf | exact HB_segs_cf | exact HB_relro_cf | exact HB_hi_cf].

(* ---- Section b's facts at PI_prog_B ---- *)
Lemma crt_pc_B_cf : BASE + CRT_PC_B = SIGMA AS_check_round_trip.
Proof. apply (crt_pc_B (PA := PIB)); hb. Qed.
Lemma crt_cut_pc_B_cf : forall off, BASE + (CRT_PC_B + off) = SIGMA AS_check_round_trip + off.
Proof. apply (crt_cut_pc_B (PA := PIB)); hb. Qed.
Lemma crt_at_B_cf : forall off, AT off = B_prog_base + (CRT_PC_B + off).
Proof. apply (crt_at_B (PA := PIB)); hb. Qed.
Lemma crt_abort_B_cf : @pi_abort prh_img_B F_check_round_trip = AT CRT_AB_OFF_B.
Proof. apply (crt_abort_B (PA := PIB)); hb. Qed.

(* the two literals: the instance's own instruction words at the five sites resolve to them ... *)
Lemma crt_str_res_B_cf :
  res_pair (segf SEGS) (AT CRT_STAMP1_HI_B) (AT CRT_STAMP1_LO_B) = Some STAMP /\
  res_pair (segf SEGS) (AT CRT_MODAT1_HI_B) (AT CRT_MODAT1_LO_B) = Some MOD_AT /\
  res_pair (segf SEGS) (AT CRT_MODAT2_HI_B) (AT CRT_MODAT2_LO_B) = Some MOD_AT /\
  res_pair (segf SEGS) (AT CRT_MODAT3_HI_B) (AT CRT_MODAT3_LO_B) = Some MOD_AT /\
  res_pair (segf SEGS) (AT CRT_STAMP2_HI_B) (AT CRT_STAMP2_LO_B) = Some STAMP.
Proof. apply (crt_str_res_B (PA := PIB)); hb. Qed.
(* ... and the bytes there *)
Lemma crt_str_rom_b_B_cf :
  str_at SEGS MOD_AT CRT_MOD_AT_S = true /\
  str_at SEGS STAMP CRT_STAMP_S = true.
Proof. apply (crt_str_rom_b_B (PA := PIB)); hb. Qed.
Lemma crt_str_rom_B_cf :
  (forall j, (j < length CRT_MOD_AT_S)%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom SEGS (Z_to_bv 64 (MOD_AT + Z.of_nat j))) =
     Some (nth j CRT_MOD_AT_S 0)) /\
  (forall j, (j < length CRT_STAMP_S)%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom SEGS (Z_to_bv 64 (STAMP + Z.of_nat j))) =
     Some (nth j CRT_STAMP_S 0)).
Proof. apply (crt_str_rom_B (PA := PIB)); hb. Qed.

(* the prologue's GOT pairs: A_OBJ 0 (the shadow base's) and A_OBJ 1 (the use-after-return flag's) *)
Lemma crt_got_B_cf :
  res_pair (segf SEGS) (AT CRT_GOT_SHB_HI_B) (AT CRT_GOT_SHB_LO_B) = Some (VAL (A_OBJ 0)) /\
  res_pair (segf SEGS) (AT CRT_GOT_UAR_HI_B) (AT CRT_GOT_UAR_LO_B) = Some (VAL (A_OBJ 1)).
Proof. apply (crt_got_B (PA := PIB)); hb. Qed.

(* the image facts a journal needs *)
Lemma crt_pst_img_B_cf : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof. apply (crt_pst_img_B (PA := PIB)); hb. Qed.
Lemma crt_pst_ro_B_cf : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. apply (crt_pst_ro_B (PA := PIB)); hb. Qed.
Lemma crt_pa_hi_B_cf : @pa_hi _ B_prog_listing PIB <= 2 ^ 31.
Proof. apply (crt_pa_hi_B (PA := PIB)); hb. Qed.
End cf.
