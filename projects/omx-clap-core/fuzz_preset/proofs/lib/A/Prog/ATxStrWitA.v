(* RULE 24: proves no function (kind: merge).
   fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the relocation
   checks and the INSTANCE WITNESSES of the static image premises of tx_string's A' walk (lib/A/Prog/ATxString.v +
   ATxStep.v). Every lemma is CLOSED: a vm_compute on a closed goal at the whole-program instance PI_prog_A and the
   A' asyms AD2l.TfibB, or a citation of a closed A' lemma (PALibA, TxGlue102ImgCheck). This file Requires none of
   the walk.
   THE IMAGE DATA: lib/A/Listing_prog.v (A_prog_listing), lib/A/PAImg_prog.v (PI_prog_A), lib/A/Img0.v (rsegs),
   lib/A/PRH_Img.v (prh_img_A), lib/A/AD2l.v (TfibB, over lib/A/AF0m.v's tables), lib/A/CfImgA.v (CfImg_A),
   lib/A/PALibA.v.
   (1) RELOCATION CHECKS: tx_string's listing slot (3909; the walk's TS_PC_A = 15636), the four tx_put return pcs the
   closed ceiling lemmas name (15916 / 16308 in ATxString.v, 16164 / 16148 in ATxStep.v), the PAddHi (A_OBJ 2)
   offsets of .str.25 / .str.26 / tx_string.hex (70432 / 70464 / 70368), the BYTES at those three addresses, and the
   DATA TRAP: the frame-description pointer's offset 0xe949 and its bytes "1 32 6 7 esc:416", read from the A'
   segments (the walk neither states nor reads them).
   (2) WITNESSES of the walk's static image premises at the instance: ts_lit_img_A, ts_hex_img_A (kept_img /
   kept_at over pa_lo / pa_hi of PI_prog_A, PRH_Base), zs_aligned, pal_uar_img (IMG_LO / IMG_TOP and the CfImg_A
   form), cf_img_ok, img_cf_box, img_box, pal_stack_malloc0, pal_pst_static, PAL (PALibA.palib_A), LAWS at ARcf
   (PALibA.palib_laws_A; the instance lemma ATxString.v tx_string_A_inst takes the laws at iface_ARx, YGcallcf's
   AR_laws_x_xs); and the walk's in-file image facts (pa_hi <= 2 ^ 31, the STK allowances, BASE + TS_PC_A = sigma
   tx_string).
   Numerals: DERIVED the listing slot 3909, listing coordinates 15636 / 15916 / 16308 / 16164 / 16148 (4 * slot) and
   offsets 264 / 332 / 336 / 656 / 192 (from tx_string's entry), the object index 2 of A_OBJ 2; the .rodata offsets
   70432 / 70464 / 70368 / 0xe949 (the listing's); ADDRESS: 0x10000 (pa_val (A_OBJ 2), the base of those offsets),
   0x21320 / 0x21340 / 0x212e0 (A' .str.25 / .str.26 / tx_string.hex), 0x212f0 (the end of tx_string.hex's
   zero-shadow range in AF0m.Tfib_zero_shadow) and 0x7fffc264 / 0x7fffc268 (the two const-shadow cells), each CHECKED
   by vm_compute against the definitions here, so none can go stale; WORD: the string bytes and the const-shadow value
   2; LENGTH: 1, 4, 8 (the shadow granule), 16, 17 (the frame-description string with its NUL), 64 (the word width),
   176, 4096, 2 ^ 31. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05 YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset CfImgA AF0m AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PALibA.
(* the instance's CfImg-bound facts, already closed at A' there (pa_hi_ok_A, cf_img_ok_A, img_box_A, img_cf_box_A,
   pal_uar_img_A) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require TxGlue102ImgCheck.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- image-free checkers and their soundness (BTxStrWitB.v's, restated here so that no B' file is loaded into this
   A' file) ---- *)
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

(* image A''s listing, instance and segments, by FULLY QUALIFIED name (the closure may load other images' modules of
   the same short names; see the guard tsw_segs_A) *)
#[local] Abbreviation ALIST := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Listing_prog.A_prog_listing.
#[local] Abbreviation PIA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.PI_prog_A.
#[local] Abbreviation ASEGS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.

(* the listing's instruction at byte offset k from the listing base: a call's target / a PAddHi's object and offset *)
Definition tsw_call_at (k : Z) : option asym :=
  match plookup_list asym ALIST k with Some (PCall s _) => Some s | _ => None end.
Definition tsw_addhi_at (k : Z) : option (nat * Z) :=
  match plookup_list asym ALIST k with Some (PAddHi _ _ _ a off) => Some (a, off) | _ => None end.

(* ---- (1) RELOCATION CHECKS on the A' listing (no run ceiling needed) ---- *)
(* tx_string's slot: TS_PC_A = 4 * slot = 15636 *)
Lemma tsw_slot_A : A_prog_slot AS_tx_string = 3909%nat /\ 4 * Z.of_nat (A_prog_slot AS_tx_string) = 15636.
Proof. split; vm_compute; reflexivity. Qed.

(* the four tx_put calls whose return pcs the closed ceiling lemmas name: TS_PC_A + 280 / 672 (ATxString.v
   ts_ret_ceil_C_A / _G_A) and + 528 / 512 (ATxStep.v ts_ret_ceil_F1_A / _E_A); the jal sits 4 bytes before *)
Lemma tsw_put_rets_A :
  map (fun k => tsw_call_at (k - 4)) [15916; 16308; 16164; 16148] =
  [Some AS_tx_put; Some AS_tx_put; Some AS_tx_put; Some AS_tx_put].
Proof. vm_compute. reflexivity. Qed.

(* the literal addresses' PAddHi (A_OBJ 2) offsets at tx_string + 264 (.str.25), + 332 (tx_string.hex), + 336
   (.str.26), + 656 (.str.25); and + 192, the ASan frame-description pointer (the DATA TRAP) *)
Lemma tsw_lit_slots_A :
  map (fun o => tsw_addhi_at (15636 + o)) [264; 332; 336; 656; 192] =
  [Some (A_OBJ 2, 70432); Some (A_OBJ 2, 70368); Some (A_OBJ 2, 70464); Some (A_OBJ 2, 70432); Some (A_OBJ 2, 0xe949)].
Proof. vm_compute. reflexivity. Qed.

(* WRONG-IMAGE NAME GUARD: which module each short image name resolves to in this file's closure (printed into the
   build log), and a reflexivity guard that the segments every lemma below states over (pa_segs of PI_prog_A) are
   image A''s lib/A/Img0.v rsegs, named fully qualified *)
Locate rsegs.
Locate Img0.rsegs.
Locate A_prog_listing.
Locate PI_prog_A.
Locate prh_img_A.
Locate AD2l.TfibB.
Section w. Context {rc : YM05.RunCeil} {ci : CfImg}.
Lemma tsw_segs_A : @pa_segs _ ALIST PIA = ASEGS.
Proof. reflexivity. Qed.
#[local] Notation PA := (PIA).
#[local] Notation SEGS := (@pa_segs _ ALIST PA).
#[local] Notation VAL := (@pa_val _ ALIST PA).
#[local] Notation SIGMA := (@pa_sigma _ ALIST PA).
#[local] Notation BASE := (@pa_val _ ALIST PA A_TEXT).
#[local] Notation TA := AD2l.TfibB.
#[local] Notation PST := (prh_pst (PI := prh_img_A)).

Lemma tsw_obj2_A : VAL (A_OBJ 2) = 0x10000.
Proof. vm_compute. reflexivity. Qed.

(* the walk's three literal addresses (ATxString.v TS_STR25_A / TS_STR26_A / TS_HEX_A) on A' *)
Lemma tsw_lits_A : VAL (A_OBJ 2) + 70432 = 0x21320 /\ VAL (A_OBJ 2) + 70464 = 0x21340 /\ VAL (A_OBJ 2) + 70368 = 0x212e0.
Proof. rewrite tsw_obj2_A. lia. Qed.

(* the bytes at those addresses, read from A''s segments: the quote (34), the backslash (92), the 16 hex digits *)
Lemma tsw_lit_bytes_A :
  map (fun a => option_map (fun bb => bv_unsigned bb) (YK11.seg_rom SEGS (Z_to_bv 64 a)))
    [VAL (A_OBJ 2) + 70432; VAL (A_OBJ 2) + 70464] = [Some 34; Some 92] /\
  map (fun j => option_map (fun bb => bv_unsigned bb) (YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + 70368 + Z.of_nat j))))
    (seq 0 16) = map Some [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 97; 98; 99; 100; 101; 102].
Proof. split; vm_compute; reflexivity. Qed.

(* DATA TRAP: the frame-description string the prologue's pointer names is "1 32 6 7 esc:416" on A' (at
   0x1e949); the walk carries the header [F, F + 24) with no contents, so it reads none of these bytes *)
Lemma tsw_desc_bytes_A :
  map (fun j => option_map (fun bb => bv_unsigned bb) (YK11.seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ 2) + 0xe949 + Z.of_nat j))))
    (seq 0 17) = map Some [49; 32; 51; 50; 32; 54; 32; 55; 32; 101; 115; 99; 58; 52; 49; 54; 0].
Proof. vm_compute. reflexivity. Qed.

(* ---- (2) the walk's in-file image facts at A' (ATxString.v pa_hi_ok_A / HSTK_A / HSTKP_A / TS_PC_val_A) ---- *)
Lemma tsw_pa_hi_A : @pa_hi _ ALIST PA <= 2 ^ 31.
Proof. exact TxGlue102ImgCheck.pa_hi_ok_A. Qed.

Lemma tsw_stk_A : 4096 + 176 <= @STK_tx_string prh_img_A /\
  0 <= @STK_tx_put prh_img_A /\ @STK_tx_put prh_img_A + 176 <= @STK_tx_string prh_img_A.
Proof. split; [|split]; vm_compute; discriminate. Qed.

Lemma tsw_pc_A : BASE + 15636 = SIGMA AS_tx_string.
Proof. vm_compute. reflexivity. Qed.

(* ---- (2) INSTANCE WITNESSES of the walk's static image premises (B := AD2l.TfibB) ---- *)
(* ts_lit_img_A: .str.25 (the quote, 0x21320) and .str.26 (the backslash, 0x21340), one byte each, read-only, not
   owned, not errno, their granules' const-shadow cells 0x7fffc264 / 0x7fffc268 = 2 (AF0m.Tfib_const_shadow) *)
Lemma tsw_lit_img_TfibA :
  kept_img (PA := PA) TA (VAL (A_OBJ 2) + 70432) 1 /\ kept_img (PA := PA) TA (VAL (A_OBJ 2) + 70464) 1.
Proof.
rewrite tsw_obj2_A. split; unfold kept_img;
  (split; [vm_compute; discriminate|]); (split; [vm_compute; discriminate|]); intros a Ha.
- assert (Ea : a = 0x21320) by lia. subst a.
  split; [apply tsw_in_ro_b_sound; vm_compute; reflexivity|].
  split; [apply tsw_not_in_zrs; vm_compute; reflexivity|].
  split; [cbn [as_errno AD2l.TfibB]; unfold AF0m.TFIB_ERRNO; lia|].
  right. exists 2. split; [|right; split; reflexivity].
  intros ly. cbn [as_const AD2l.TfibB]. unfold AF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right.
  replace (shadow_addr 0x21320) with 0x7fffc264 by (vm_compute; reflexivity).
  unfold AF0m.Tfib_const_shadow. repeat (first [left; reflexivity | right]).
- assert (Ea : a = 0x21340) by lia. subst a.
  split; [apply tsw_in_ro_b_sound; vm_compute; reflexivity|].
  split; [apply tsw_not_in_zrs; vm_compute; reflexivity|].
  split; [cbn [as_errno AD2l.TfibB]; unfold AF0m.TFIB_ERRNO; lia|].
  right. exists 2. split; [|right; split; reflexivity].
  intros ly. cbn [as_const AD2l.TfibB]. unfold AF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right.
  replace (shadow_addr 0x21340) with 0x7fffc268 by (vm_compute; reflexivity).
  unfold AF0m.Tfib_const_shadow. repeat (first [left; reflexivity | right]).
Qed.

(* ts_hex_img_A: tx_string.hex (0x212e0, 16 bytes) lies in one zero-shadow range of TfibB, read-only, not owned,
   not errno (kept_at's second arm; Lam = [] at the text's own premise) *)
Lemma tsw_hex_img_TfibA : kept_at (PA := PA) TA [] (VAL (A_OBJ 2) + 70368) 16.
Proof.
rewrite tsw_obj2_A. unfold kept_at. right. left.
split; [|split; [vm_compute; discriminate|split; [vm_compute; discriminate|]]].
- unfold in_zs. exists 0x212e0, (0x212f0 - 0x212e0). split; [|lia].
  cbn [as_zero_shadow AD2l.TfibB]. unfold AF0m.Tfib_zero_shadow. repeat (first [left; reflexivity | right]).
- intros a Ha.
  assert (H : zallb (fun x => tsw_in_ro_b SEGS (@pa_relro_lo _ ALIST PA) (@pa_relro_hi _ ALIST PA) x &&
                     negb (existsb (tsw_zr_b x) (as_owned_static TA))) 0x212e0 16 = true)
    by (vm_compute; reflexivity).
  pose proof (zallb_sound _ 16%nat 0x212e0 a H ltac:(change (Z.of_nat 16) with 16; lia)) as Hb. cbv beta in Hb.
  apply andb_prop in Hb as [H1 H2].
  split; [exact (tsw_in_ro_b_sound _ _ _ _ H1)|].
  split; [apply tsw_not_in_zrs; apply negb_true_iff; exact H2|].
  cbn [as_errno AD2l.TfibB]. unfold AF0m.TFIB_ERRNO. lia.
Qed.

(* zs_aligned: TfibB's zero-shadow ranges are granule-aligned *)
Lemma tsw_zs_aligned_TfibA : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TA).
Proof.
cbn [as_zero_shadow AD2l.TfibB].
assert (H : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) AF0m.Tfib_zero_shadow = true)
  by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) H r Hr) as Hb.
apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1, H2. split; assumption.
Qed.

(* pal_uar_img: the use-after-return flag cell (A' 0xaaec0, 4 bytes of .bss) lies in A''s image bounds *)
Lemma tsw_pal_uar_img_TfibA : IMG_LO <= as_uar_cell TA /\ as_uar_cell TA + 4 <= IMG_TOP.
Proof. cbn [as_uar_cell AD2l.TfibB]. unfold IMG_LO, IMG_TOP. lia. Qed.

(* the walk's CfImg-bound Section facts (ATxString.v / ATxStep.v: pal_uar_img, cf_img_ok, img_cf_box, TxStr102Glue.v's
   form) at the A' CfImg instance CfImg_A (lib/A/CfImgA.v: 0x10000 / 0x600000), and the instance's img_box (the
   walk's closed img_box_A): TxGlue102ImgCheck.v's closed lemmas, cited *)
Lemma tsw_pal_uar_img_cf_TfibA : @cf_img_lo CfImgA.CfImg_A <= as_uar_cell TA /\
  as_uar_cell TA + 4 <= @cf_img_top CfImgA.CfImg_A.
Proof. exact TxGlue102ImgCheck.pal_uar_img_A. Qed.
Lemma tsw_cf_img_ok_A : 0 <= @cf_img_lo CfImgA.CfImg_A /\ @cf_img_top CfImgA.CfImg_A <= 2 ^ 31.
Proof. exact TxGlue102ImgCheck.cf_img_ok_A. Qed.
Lemma tsw_img_cf_box_A : @cf_img_lo CfImgA.CfImg_A <= @pa_lo _ ALIST PA /\ @pa_hi _ ALIST PA <= @cf_img_top CfImgA.CfImg_A.
Proof. exact TxGlue102ImgCheck.img_cf_box_A. Qed.
Lemma tsw_img_box_A : 4096 <= @pa_lo _ ALIST PA /\ @pa_hi _ ALIST PA <= kLowMemEnd.
Proof. exact TxGlue102ImgCheck.img_box_A. Qed.

(* pal_stack_malloc0: the listing's __asan_stack_malloc_0 is the code record's (A' 0x3db48) *)
Lemma tsw_pal_stack_malloc0_TfibA : SIGMA AS___asan_stack_malloc_0 = pc_stack_malloc (as_code TA) 0.
Proof. vm_compute. reflexivity. Qed.

(* pal_pst_static: the program's statics, the seven prh_pst cells of PRH_Img (alloc.c's six: g_live, g_peak, g_count,
   g_fail_at, g_ran_out, g_most; and fuzz_preset.c's g_own_ran_out), are neither runtime-owned nor errno *)
Lemma tsw_pal_pst_static_TfibA : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static TA) /\ ~ (as_errno TA <= a < as_errno TA + 4).
Proof.
assert (H : tsw_allb (fun a => negb (existsb (tsw_zr_b a) AF0m.Tfib_owned_static) &&
                               negb ((AF0m.TFIB_ERRNO <=? a) && (a <? AF0m.TFIB_ERRNO + 4))) PST = true)
  by (vm_compute; reflexivity).
intros a Ha. pose proof (tsw_allb_sound _ _ a H Ha) as Hb. cbv beta in Hb.
apply andb_prop in Hb as [H1 H2]. split.
- cbn [as_owned_static AD2l.TfibB]. apply tsw_not_in_zrs. apply negb_true_iff. exact H1.
- cbn [as_errno AD2l.TfibB]. intros [Hl Hh]. apply Z.leb_le in Hl. apply Z.ltb_lt in Hh. rewrite Hl, Hh in H2.
  discriminate H2.
Qed.

(* PAL and LAWS: PALibA's witnesses at the same instance, cited (LAWS at ARcf; the walk's ARx at the text's instance
   is iface_ARx, ATxString.v's instance lemma) *)
Lemma tsw_PAL_TfibA : YC1fP.PALib (PI := PA) TA.
Proof. exact PALibA.palib_A. Qed.

Lemma tsw_LAWS_TfibA : AR_laws_x ASEGS TA (YG0ncf.ARcf (cp := CfParamsPreset.CfParams_preset) ASEGS TA)
  (@cf_head CfParamsPreset.CfParams_preset).
Proof. exact PALibA.palib_laws_A. Qed.
End w.
Print Assumptions tsw_segs_A.

(* the audit: every lemma closed (the standard axioms only) *)
Print Assumptions tsw_slot_A.
Print Assumptions tsw_put_rets_A.
Print Assumptions tsw_lit_slots_A.
Print Assumptions tsw_lit_bytes_A.
Print Assumptions tsw_desc_bytes_A.
Print Assumptions tsw_pa_hi_A.
Print Assumptions tsw_stk_A.
Print Assumptions tsw_pc_A.
Print Assumptions tsw_lit_img_TfibA.
Print Assumptions tsw_hex_img_TfibA.
Print Assumptions tsw_zs_aligned_TfibA.
Print Assumptions tsw_pal_uar_img_TfibA.
Print Assumptions tsw_pal_uar_img_cf_TfibA.
Print Assumptions tsw_cf_img_ok_A.
Print Assumptions tsw_img_cf_box_A.
Print Assumptions tsw_img_box_A.
Print Assumptions tsw_pal_stack_malloc0_TfibA.
Print Assumptions tsw_pal_pst_static_TfibA.
Print Assumptions tsw_PAL_TfibA.
Print Assumptions tsw_LAWS_TfibA.
