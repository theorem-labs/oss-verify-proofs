(* rule 24: no function proved
   rule 24: proves no function (kind: merge)
   fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b): the
   relocation checks and the INSTANCE WITNESSES of the static image premises of tx_string's B' walk
   (lib/B/Prog/BTxString.v + BTxStep.v, relocated from cold/h-rw-pre-5-b-tx 043041dbb091 by lane TxStrBp). Every lemma
   is CLOSED: a vm_compute on a closed goal at the whole-program instance PI_prog_B and the B' asyms YD2l.TfibB, or a
   citation of PALibB. This file Requires none of the walk (it builds while S10's glue has no #102 copy).
   THE IMAGE DATA (blobs on the kit's cut 7cdbb61b5fa0, the same as int102 d1659777b723): lib/B/Listing_prog.v c97cc46b3e13,
   lib/B/PAImg_prog.v 15fab93fe702, lib/B/Img0.v (rsegs), lib/B/PRH_ImgB.v 3216eca68342, lib/Reusable/YD2l.v
   95803a8b9493 (TfibB), lib/Reusable/YF0m.v f82202ebccdf, lib/Reusable/YImgTop.v d2a97d3111ce, lib/B/PALibB.v
   5baa19c890f7.
   (1) RELOCATION CHECKS: tx_string's listing slot (4221; the walk's TS_PC_B = 16884), the four tx_put return pcs the
   closed ceiling lemmas name (17160 / 17572 in BTxString.v, 17420 / 17404 in BTxStep.v), the PAddHi (A_OBJ 2) offsets
   of .str.27 / .str.28 / tx_string.hex (70432 / 70464 / 70368), the BYTES at those three addresses, and the DATA TRAP:
   the frame-description pointer's offset 0xe94f and its NEW bytes "1 32 6 7 esc:416", read from the B' segments (the
   walk neither states nor reads them).
   (2) WITNESSES of the walk's static image premises at the instance: ts_lit_img_B, ts_hex_img_B (kept_img / kept_at,
   PER-INSTANCE pa_lo / pa_hi, decff's PRH_Base), zs_aligned, pal_uar_img (IMG_LO_B / IMG_TOP_B), pal_stack_malloc0,
   pal_pst_static, PAL (PALibB.exvi_eh_palib), LAWS at ARcf (PALibB.exvi_eh_laws); and the walk's in-file image facts
   (pa_hi <= 2 ^ 31, the STK allowances, BASE + TS_PC_B = sigma tx_string).
   Numerals: DERIVED listing coordinates 16884 / 17160 / 17572 / 17420 / 17404 (4 * slot) and offsets 260 / 340 /
   344 / 672 / 192 (from tx_string's entry); the .rodata offsets 70432 / 70464 / 70368 / 0xe94f (the listing's); the
   addresses 0x21320 / 0x21340 / 0x212e0 / 0x7fffc264 / 0x7fffc268 (B' .str.27 / .str.28 / tx_string.hex and the two
   const-shadow cells, each CHECKED by vm_compute against the definitions here, so none can go stale); WORD: the
   string bytes; LENGTH: 1, 4, 16, 64, 176, 4096, 2 ^ 31. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05 YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP YF0m YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- image-free checkers and their soundness (the shape of Cno102B_Img.v's cnbx_*, written here so that no A' file
   is loaded into this B' file) ---- *)
Definition tsw_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.

Lemma tsw_allb_sound : forall f P a, tsw_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold tsw_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.

Definition tsw_in_ro_b (segs : list Segment) (rlo rhi a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    segs || ((rlo <=? a) && (a <? rhi)).

Lemma tsw_in_ro_b_sound : forall segs rlo rhi a,
  tsw_in_ro_b segs rlo rhi a = true -> PresetRodata.in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi a H. unfold tsw_in_ro_b in H. apply orb_prop in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs|]. split; [exact H0 | lia].
- right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Definition tsw_zr_b (a : Z) (r : Z * Z) : bool := (fst r <=? a) && (a <? fst r + snd r).

Lemma tsw_not_in_zrs : forall a P, existsb (tsw_zr_b a) P = false -> ~ Exists (in_zr a) P.
Proof.
intros a P H HE. apply Exists_exists in HE as (r & Hr & Ha). unfold in_zr in Ha.
assert (E : existsb (tsw_zr_b a) P = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. unfold tsw_zr_b.
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite H in E. discriminate E.
Qed.

(* image B''s listing, instance and segments, by FULLY QUALIFIED name (the closure may load other images' modules of
   the same short names; see the guard tsw_segs_B) *)
#[local] Abbreviation BLIST := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Listing_prog.B_prog_listing.
#[local] Abbreviation PIB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.PI_prog_B.
#[local] Abbreviation BSEGS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.

(* the listing's instruction at byte offset k from the listing base: a call's target / a PAddHi's object and offset *)
Definition tsw_call_at (k : Z) : option asym :=
  match plookup_list asym BLIST k with Some (PCall s _) => Some s | _ => None end.
Definition tsw_addhi_at (k : Z) : option (nat * Z) :=
  match plookup_list asym BLIST k with Some (PAddHi _ _ _ a off) => Some (a, off) | _ => None end.

(* ---- (1) RELOCATION CHECKS on the B' listing (no run ceiling needed) ---- *)
(* tx_string's slot: TS_PC_B = 4 * slot = 16884 (old pin: slot 4017, 16068) *)
Lemma tsw_slot_B : B_prog_slot AS_tx_string = 4221%nat /\ 4 * Z.of_nat (B_prog_slot AS_tx_string) = 16884.
Proof. split; vm_compute; reflexivity. Qed.

(* the four tx_put calls whose return pcs the closed ceiling lemmas name: TS_PC_B + 276 / 688 (BTxString.v
   ts_ret_ceil_C_B / _G_B) and + 536 / 520 (BTxStep.v ts_ret_ceil_F1_B / _E_B); the jal sits 4 bytes before *)
Lemma tsw_put_rets_B :
  map (fun k => tsw_call_at (k - 4)) [17160; 17572; 17420; 17404] =
  [Some AS_tx_put; Some AS_tx_put; Some AS_tx_put; Some AS_tx_put].
Proof. vm_compute. reflexivity. Qed.

(* the literal addresses' PAddHi (A_OBJ 2) offsets at tx_string + 260 (.str.27), + 340 (tx_string.hex), + 344
   (.str.28), + 672 (.str.27); and + 192, the ASan frame-description pointer (the DATA TRAP: 0xa5c0 on the old pin) *)
Lemma tsw_lit_slots_B :
  map (fun o => tsw_addhi_at (16884 + o)) [260; 340; 344; 672; 192] =
  [Some (A_OBJ 2, 70432); Some (A_OBJ 2, 70368); Some (A_OBJ 2, 70464); Some (A_OBJ 2, 70432); Some (A_OBJ 2, 0xe94f)].
Proof. vm_compute. reflexivity. Qed.

(* WRONG-IMAGE NAME GUARD (CrcBp's trap, the lead 19:3xZ): which module each short image name resolves to in this
   file's closure (printed into the build log), and a reflexivity guard that the segments every lemma below states over
   (pa_segs of PI_prog_B) are image B''s lib/B/Img0.v rsegs, named fully qualified (template: CrcBp's cr_segs_B) *)
Locate rsegs.
Locate Img0.rsegs.
Locate B_prog_listing.
Locate PI_prog_B.
Locate prh_img_B.
Locate TfibB.
Section w. Context {rc : YM05.RunCeil} {ci : CfImg}.
Lemma tsw_segs_B : @pa_segs _ BLIST PIB = BSEGS.
Proof. reflexivity. Qed.
#[local] Notation PA := (PIB).
#[local] Notation SEGS := (@pa_segs _ BLIST PA).
#[local] Notation VAL := (@pa_val _ BLIST PA).
#[local] Notation SIGMA := (@pa_sigma _ BLIST PA).
#[local] Notation BASE := (@pa_val _ BLIST PA A_TEXT).
#[local] Notation TB := YD2l.TfibB.
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

Lemma tsw_obj2_B : VAL (A_OBJ 2) = 0x10000.
Proof. vm_compute. reflexivity. Qed.

(* the walk's three literal addresses (BTxString.v TS_STR27_B / TS_STR28_B / TS_HEX_B) on B' *)
Lemma tsw_lits_B : VAL (A_OBJ 2) + 70432 = 0x21320 /\ VAL (A_OBJ 2) + 70464 = 0x21340 /\ VAL (A_OBJ 2) + 70368 = 0x212e0.
Proof. rewrite tsw_obj2_B. lia. Qed.

(* the NEW bytes at those addresses, read from B''s segments: the quote (34), the backslash (92), the 16 hex digits *)
Lemma tsw_lit_bytes_B :
  map (fun a => option_map (fun bb => bv_unsigned bb) (YK11.seg_rom SEGS (Z_to_bv 64 a)))
    [VAL (A_OBJ 2) + 70432; VAL (A_OBJ 2) + 70464] = [Some 34; Some 92] /\
  map (fun j => option_map (fun bb => bv_unsigned bb) (YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + 70368 + Z.of_nat j))))
    (seq 0 16) = map Some [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 97; 98; 99; 100; 101; 102].
Proof. split; vm_compute; reflexivity. Qed.

(* DATA TRAP: the frame-description string the prologue's pointer names is "1 32 6 7 esc:416" on B' (old pin
   "esc:382" at 0x1a5c0); the walk carries the header [F, F + 24) with no contents, so it reads none of these bytes *)
Lemma tsw_desc_bytes_B :
  map (fun j => option_map (fun bb => bv_unsigned bb) (YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + 0xe94f + Z.of_nat j))))
    (seq 0 17) = map Some [49; 32; 51; 50; 32; 54; 32; 55; 32; 101; 115; 99; 58; 52; 49; 54; 0].
Proof. vm_compute. reflexivity. Qed.

(* ---- (2) the walk's in-file image facts at B' (BTxString.v pa_hi_ok_B / HSTK_B / HSTKP_B / TS_PC_val_B) ---- *)
Lemma tsw_pa_hi_B : @pa_hi _ BLIST PA <= 2 ^ 31.
Proof. vm_compute. discriminate. Qed.

Lemma tsw_stk_B : 4096 + 176 <= @STK_tx_string prh_img_B /\
  0 <= @STK_tx_put prh_img_B /\ @STK_tx_put prh_img_B + 176 <= @STK_tx_string prh_img_B.
Proof. split; [|split]; vm_compute; discriminate. Qed.

Lemma tsw_pc_B : BASE + 16884 = SIGMA AS_tx_string.
Proof. vm_compute. reflexivity. Qed.

(* ---- (2) INSTANCE WITNESSES of the walk's static image premises (B := YD2l.TfibB) ---- *)
(* ts_lit_img_B: .str.27 (the quote, 0x21320) and .str.28 (the backslash, 0x21340), one byte each, read-only, not owned, not errno,
   their granules' const-shadow cells 0x7fffc264 / 0x7fffc268 = 2 (YF0m.Tfib_const_shadow) *)
Lemma tsw_lit_img_TfibB :
  kept_img (PA := PA) TB (VAL (A_OBJ 2) + 70432) 1 /\ kept_img (PA := PA) TB (VAL (A_OBJ 2) + 70464) 1.
Proof.
rewrite tsw_obj2_B. split; unfold kept_img;
  (split; [vm_compute; discriminate|]); (split; [vm_compute; discriminate|]); intros a Ha.
- assert (Ea : a = 0x21320) by lia. subst a.
  split; [apply tsw_in_ro_b_sound; vm_compute; reflexivity|].
  split; [apply tsw_not_in_zrs; vm_compute; reflexivity|].
  split; [cbn [as_errno YD2l.TfibB]; unfold YF0m.TFIB_ERRNO; lia|].
  right. exists 2. split; [|right; split; reflexivity].
  intros ly. cbn [as_const YD2l.TfibB]. unfold YF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right.
  replace (shadow_addr 0x21320) with 0x7fffc264 by (vm_compute; reflexivity).
  unfold YF0m.Tfib_const_shadow. repeat (first [left; reflexivity | right]).
- assert (Ea : a = 0x21340) by lia. subst a.
  split; [apply tsw_in_ro_b_sound; vm_compute; reflexivity|].
  split; [apply tsw_not_in_zrs; vm_compute; reflexivity|].
  split; [cbn [as_errno YD2l.TfibB]; unfold YF0m.TFIB_ERRNO; lia|].
  right. exists 2. split; [|right; split; reflexivity].
  intros ly. cbn [as_const YD2l.TfibB]. unfold YF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right.
  replace (shadow_addr 0x21340) with 0x7fffc268 by (vm_compute; reflexivity).
  unfold YF0m.Tfib_const_shadow. repeat (first [left; reflexivity | right]).
Qed.

(* ts_hex_img_B: tx_string.hex (0x212e0, 16 bytes) lies in one zero-shadow range of TfibB, read-only, not owned,
   not errno (kept_at's second arm; Lam = [] at the text's own premise) *)
Lemma tsw_hex_img_TfibB : kept_at (PA := PA) TB [] (VAL (A_OBJ 2) + 70368) 16.
Proof.
rewrite tsw_obj2_B. unfold kept_at. right. left.
split; [|split; [vm_compute; discriminate|split; [vm_compute; discriminate|]]].
- unfold in_zs. exists 0x212e0, (0x212f0 - 0x212e0). split; [|lia].
  cbn [as_zero_shadow YD2l.TfibB]. unfold YF0m.Tfib_zero_shadow. repeat (first [left; reflexivity | right]).
- intros a Ha.
  assert (H : zallb (fun x => tsw_in_ro_b SEGS (@pa_relro_lo _ BLIST PA) (@pa_relro_hi _ BLIST PA) x &&
                     negb (existsb (tsw_zr_b x) (as_owned_static TB))) 0x212e0 16 = true)
    by (vm_compute; reflexivity).
  pose proof (zallb_sound _ 16%nat 0x212e0 a H ltac:(change (Z.of_nat 16) with 16; lia)) as Hb. cbv beta in Hb.
  apply andb_prop in Hb as [H1 H2].
  split; [exact (tsw_in_ro_b_sound _ _ _ _ H1)|].
  split; [apply tsw_not_in_zrs; apply negb_true_iff; exact H2|].
  cbn [as_errno YD2l.TfibB]. unfold YF0m.TFIB_ERRNO. lia.
Qed.

(* zs_aligned: TfibB's zero-shadow ranges are granule-aligned *)
Lemma tsw_zs_aligned_TfibB : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TB).
Proof.
cbn [as_zero_shadow YD2l.TfibB].
assert (H : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) YF0m.Tfib_zero_shadow = true)
  by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1, H2. split; assumption.
Qed.

(* pal_uar_img: the use-after-return flag cell (B' 0xab700, 4 bytes of .bss) lies in B''s image bounds *)
Lemma tsw_pal_uar_img_TfibB : IMG_LO_B <= as_uar_cell TB /\ as_uar_cell TB + 4 <= IMG_TOP_B.
Proof. cbn [as_uar_cell YD2l.TfibB]. unfold IMG_LO_B, IMG_TOP_B. lia. Qed.

(* the walk's CfImg-bound Section facts (BTxString.v / BTxStep.v: pal_uar_img, cf_img_ok, img_cf_box, TxStr102Glue.v's
   form) at the B' CfImg instance CfImg_B (lib/AU/CfImgB.v, generated from twin c90d4fa54d43: 0x10000 / 0x601000), and
   the instance's img_box (the walk's closed img_box_B) *)
Lemma tsw_pal_uar_img_cf_TfibB : @cf_img_lo CfImgB.CfImg_B <= as_uar_cell TB /\
  as_uar_cell TB + 4 <= @cf_img_top CfImgB.CfImg_B.
Proof. cbn [as_uar_cell YD2l.TfibB]. vm_compute. split; discriminate. Qed.
Lemma tsw_cf_img_ok_B : 0 <= @cf_img_lo CfImgB.CfImg_B /\ @cf_img_top CfImgB.CfImg_B <= 2 ^ 31.
Proof. vm_compute. split; discriminate. Qed.
Lemma tsw_img_cf_box_B : @cf_img_lo CfImgB.CfImg_B <= @pa_lo _ BLIST PA /\ @pa_hi _ BLIST PA <= @cf_img_top CfImgB.CfImg_B.
Proof. vm_compute. split; discriminate. Qed.
Lemma tsw_img_box_B : 4096 <= @pa_lo _ BLIST PA /\ @pa_hi _ BLIST PA <= kLowMemEnd.
Proof. vm_compute. split; discriminate. Qed.

(* pal_stack_malloc0: the listing's __asan_stack_malloc_0 is the code record's (B' 0x3dc34) *)
Lemma tsw_pal_stack_malloc0_TfibB : SIGMA AS___asan_stack_malloc_0 = pc_stack_malloc (as_code TB) 0.
Proof. vm_compute. reflexivity. Qed.

(* pal_pst_static: alloc.c's statics (all seven prh_pst cells of PRH_ImgB) are neither runtime-owned nor errno *)
Lemma tsw_pal_pst_static_TfibB : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof.
assert (H : tsw_allb (fun a => negb (existsb (tsw_zr_b a) YF0m.Tfib_owned_static) &&
                               negb ((YF0m.TFIB_ERRNO <=? a) && (a <? YF0m.TFIB_ERRNO + 4))) PST = true)
  by (vm_compute; reflexivity).
intros a Ha. pose proof (tsw_allb_sound _ _ a H Ha) as Hb. cbv beta in Hb.
apply andb_prop in Hb as [H1 H2]. split.
- cbn [as_owned_static YD2l.TfibB]. apply tsw_not_in_zrs. apply negb_true_iff. exact H1.
- cbn [as_errno YD2l.TfibB]. intros [Hl Hh]. apply Z.leb_le in Hl. apply Z.ltb_lt in Hh. rewrite Hl, Hh in H2.
  discriminate H2.
Qed.

(* PAL and LAWS: PALibB's witnesses at the same instance, cited (PALibB.v 5baa19c890f7 :58 / :80) *)
Lemma tsw_PAL_TfibB : YC1fP.PALib (PI := PA) TB.
Proof. exact PALibB.exvi_eh_palib. Qed.

Lemma tsw_LAWS_TfibB : AR_laws_x BSEGS TB (YG0ncf.ARcf (cp := CfParamsPreset.CfParams_preset) BSEGS TB)
  (@cf_head CfParamsPreset.CfParams_preset).
Proof. exact PALibB.exvi_eh_laws. Qed.
End w.
Print Assumptions tsw_segs_B.

(* the audit: every lemma closed (the standard axioms only) *)
Print Assumptions tsw_slot_B.
Print Assumptions tsw_put_rets_B.
Print Assumptions tsw_lit_slots_B.
Print Assumptions tsw_lit_bytes_B.
Print Assumptions tsw_desc_bytes_B.
Print Assumptions tsw_stk_B.
Print Assumptions tsw_pc_B.
Print Assumptions tsw_lit_img_TfibB.
Print Assumptions tsw_hex_img_TfibB.
Print Assumptions tsw_zs_aligned_TfibB.
Print Assumptions tsw_pal_uar_img_TfibB.
Print Assumptions tsw_pal_uar_img_cf_TfibB.
Print Assumptions tsw_cf_img_ok_B.
Print Assumptions tsw_img_cf_box_B.
Print Assumptions tsw_img_box_B.
Print Assumptions tsw_pal_stack_malloc0_TfibB.
Print Assumptions tsw_pal_pst_static_TfibB.
Print Assumptions tsw_PAL_TfibB.
Print Assumptions tsw_LAWS_TfibB.
