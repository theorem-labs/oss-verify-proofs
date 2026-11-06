(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's PROLOGUE: the symbolic run from ex_value's entry (B_prog_sigma AS_ex_value, listing slot 1944) to the
   `jal frame_alloc_1` (slot 1972, `PCall AS___asan_stack_malloc_1`), in continuation form (exve_run1), for ExvEntry's
   segment lemma exvB_entry (lib/B/Prog/ExvB_Entry.v), which plugs the frame-area call rule in behind it.
   The stretch (29 slots): `addi sp, sp, -288`; `sd zero, 0(sp)`; the 13 saves of exv_saved (ExvB_Stmt.v);
   `addi s0, sp, 288`; `andi sp, sp, -32`; `mv s1, sp`; `mv s11, a1`; the two GOT loads (A_OBJ 1: the use-after-return
   flag's cell, A_OBJ 0: the shadow-base cell); `lw a2, 0(a2)` (the flag, 1 by alx_const); `ld s9, 0(a1)`
   (SHADOW_OFF by alx_const); `mv s3, a0`; `beqz a2` NOT taken (the flag's chunk is the literal 1, the run decides
   it); `li a0, 96`; `jal frame_alloc_1`. frame_alloc_1 lies below the listing, so the run stops there with ra set.
   Engine: YC1fPx's paj_run_x over YCbqG's ajournal_x at L := B_prog_listing, PL := PL_prog_B, PI := PI_prog_B
   (template: lib/A/Prog/S8aEntry.v, origin/cold/h-hpreset-7-walk-S8a, the same stretch on image A).
   No released plain or UBSan file is Required and no lemma of one is cited.
   NUMERALS:
   - LENGTH: 288 (the prologue's `addi sp, sp, -288`), 32 / -32 (the `andi sp, sp, -32` realignment), 320 (the
     stack room the statement asks below the entry sp), 184 .. 280 (exv_saved's slot offsets), 8 / 4 (word widths),
     4096 / 2 ^ 31 / 2 ^ 32 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (address-space bounds).
   - WORD: 96 (frame_alloc_1's size argument, `li a0, 96`), 1 (the use-after-return flag's value), register
     numbers 1-4, 8-11, 19, 25, 27.
   - DERIVED: 7776 (= B_prog_sigma AS_ex_value - B_prog_base, the entry's listing position), 7892 (= 7776 + 116, the
     slot after the `jal`), 116 (the return site's offset from the entry), atom numbers 2, 10, 11, 32, 33 of the
     symbolic engine.
   - ADDRESS: none is written. Every address is B_prog_sigma / pa_val of the listing instance, an asyms field, or a
     Section variable. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

(* ExvB_Open_kt.v's exv_land32, restated so this file does not depend on Open_kt (which Requires ex_ws_x) *)
Lemma exve_land32 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. change (-32) with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 5) with 32. pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.

(* the listing positions of the run (DERIVED: pc - B_prog_base) *)
Definition EXR_ENTRY : Z := B_prog_sigma AS_ex_value - B_prog_base.   (* ex_value's entry, slot 1944 *)
Definition EXR_RET1 : Z := B_prog_sigma AS_ex_value - B_prog_base + 116.    (* the slot after `jal frame_alloc_1` (slot 1972) = entry + 116 *)

(* no shadow byte is read by the stretch: the token band is empty *)
Definition EXR_Bx : sv := SLit 0.
Definition EXR_Bspan : Z * Z := (0, 0).

(* the entry state: the 288-byte save area below the entry sp (atom 2), the two GOT words, the shadow-base cell and
   the use-after-return flag's cell (atom 33) with the values alx_const gives them *)
Definition exr_regions1 : smem :=
  [ YP09.mkRegion (Some 2%nat) (-288) 0 (-288) 0 [];
    YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 12) 0))];
    YP09.mkRegion (Some (A_OBJ 12)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))] ].
Definition exr_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 4096 (2 ^ 31) 0)] [] [].
Definition ss_exr1 : sstate := mkSS EXR_ENTRY sr_atoms exr_regions1 None exr_facts1.

(* ---- journal-free helpers ---- *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma exr_entry_pc : BASE + EXR_ENTRY = B_prog_sigma AS_ex_value.
Proof. vm_compute. reflexivity. Qed.
Lemma exr_ret1_pc : BASE + EXR_RET1 = B_prog_sigma AS_ex_value + 116.
Proof. vm_compute. reflexivity. Qed.
Lemma exr_val_mem_of_rd32 : forall (W : world rsegs) mem a v,
  rd32 (aview rsegs (w_H W) mem) a v -> val_mem rsegs (mrestrict (w_H W) mem) a 4 v.
Proof.
intros W mem a v H k Hk. specialize (H k Hk). unfold aview in H.
destruct (mbyte rsegs (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in H; [|discriminate].
injection H as H. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, H.
pose proof (bv_unsigned_in_range 8 b) as Hr. rewrite H in Hr.
unfold bv_wrap. symmetry. apply Z.mod_small. exact Hr.
Qed.
Lemma exr_val_mem_of_rdword : forall (W : world rsegs) mem a v,
  rdword (aview rsegs (w_H W) mem) a = Some v -> val_mem rsegs (mrestrict (w_H W) mem) a 8 v.
Proof. intros W mem a v H. exact (val_mem_of_rdword rsegs (w_H W) mem a v H). Qed.
(* a register the run stored to a region chunk: its 8 bytes are in the memory the state describes *)
Lemma exr_saved_of : forall E ss (H : word -> bool) ms b lo hi wlo whi cs od (n : nat) (rv : word),
  st_ok rsegs E ss (restrict H ms) ->
  In (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) (ss_mem ss) ->
  bv_unsigned (ew E 2) = b ->
  In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs ->
  ew E n = rv ->
  val_mem rsegs (mrestrict H (ms_mem ms)) (b + od) 8 (bv_unsigned rv).
Proof.
intros E ss H ms b lo hi wlo whi cs od n rv HS Hin Hb Hc Hn.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs _ Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hb in Hck.
pose proof (bv_unsigned_in_range 64 rv) as Hr. unfold bv_modulus in Hr.
exact (val_of_chunk_ok rsegs E (ms_mem (restrict H ms)) b od 8 (SOff n 0) (bv_unsigned rv) Hck
  ltac:(cbn [sv_denot]; rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) Hr ltac:(cbn; lia)).
Qed.
(* a byte present before a run that only grows the memory is present after it *)
Lemma exr_apresent_grow : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh [b Hb]]. split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG. cbn in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|].
exfalso. exact (HG ltac:(discriminate) eq_refl).
Qed.
Lemma exr_ew_low : forall (regs : bvmap 5 word) extra (n : nat), (n < 32)%nat ->
  ew (Eimg (L := B_prog_listing) (PI := PA) (Ereg regs extra)) n = YK11.getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs extra n Hn. rewrite Eimg_low by (unfold A_TEXT; lia).
unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity|]. apply Nat.ltb_ge in E. lia.
Qed.
End h.

Section R1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HPAL : YC1fP.PALib (L := B_prog_listing) (PI := PI_prog_B) B.
Hypothesis HGOTU : as_got_uar B = B_prog_val (A_OBJ 1).
Hypothesis HUARC : 4096 <= as_uar_cell B /\ as_uar_cell B + 4 <= kLowMemEnd /\
  (as_uar_cell B + 4 <= B_prog_val (A_OBJ 0) \/ B_prog_val (A_OBJ 0) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= B_prog_val (A_OBJ 1) \/ B_prog_val (A_OBJ 1) + 8 <= as_uar_cell B) /\
  (as_uar_cell B + 4 <= B_prog_val (A_OBJ 12) \/ B_prog_val (A_OBJ 12) + 8 <= as_uar_cell B).
(* EXV_HYP's eh_sm1_pc (agreed with ExvEntry): the `jal` target is the class-1 frame-area entry *)
Hypothesis HSM1PC : B_prog_sigma AS___asan_stack_malloc_1 = pc_stack_malloc (as_code B) 1.
Definition exve_s1 (spe : Z) : Z := Z.land (spe - 288) (-32).

(* P is a memory invariant the run carries (YC80x.srr_inv_laws; YSRrMemnorm.v: ex_value takes P m := memnorm (e_mem E) ->
   memnorm m, the m-form keep of kit 4f18c75d4900); YC1fPx's _inv runner moves it across the run *)
Lemma exve_run1 : forall (W : world rsegs) (regs : bvmap 5 word) memc mdc
    STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k (spe q v : Z) (Q : world rsegs -> config -> Prop)
    (P : (word -> option byte) -> Prop),
  ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
  srr_inv_laws rsegs P -> P memc ->
  spZ regs = spe -> spe <= sp0 -> sp0 - STK <= spe - 320 ->
  YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
  YK11.getr regs 10 = w64 q -> YK11.getr regs 11 = w64 v ->
  (forall (regs' : bvmap 5 word) (memc' : word -> option byte) (mdc' : Model),
     ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc' mdc' k ->
     P memc' ->
     YK11.getr regs' 1 = w64 (B_prog_sigma AS_ex_value + 116) ->
     YK11.getr regs' 2 = w64 (exve_s1 spe) -> YK11.getr regs' 9 = w64 (exve_s1 spe) ->
     YK11.getr regs' 3 = YK11.getr regs 3 -> YK11.getr regs' 4 = YK11.getr regs 4 ->
     YK11.getr regs' 8 = w64 spe -> YK11.getr regs' 10 = w64 96 ->
     YK11.getr regs' 19 = w64 q -> YK11.getr regs' 25 = w64 SHADOW_OFF -> YK11.getr regs' 27 = w64 v ->
     (forall o r, In (o, r) exv_saved ->
        val_mem rsegs (mrestrict (w_H W) memc') (spe - 288 + o) 8 (bv_unsigned (YK11.getr regs (Z_to_bv 5 r)))) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spe - 288 <= a < spe) ->
        aview rsegs (w_H W) memc' a = aview rsegs (w_H W) memc a) ->
     (forall a, apresent (w_H W) memc a -> apresent (w_H W) memc' a) ->
     SRr rsegs W (cfg_at (fx := fx) rsegs (pc_stack_malloc (as_code B) 1) regs' memc' mdc') Q) ->
  SRr rsegs W (cfg_at (fx := fx) rsegs (B_prog_sigma AS_ex_value) regs memc mdc) Q.
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k spe q v Q P
  HJ PLAW HPM Hsp Hsp0 Hroom H3 H4 H10 H11 Hk.
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
pose proof Hastk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@alloc_ceiling_value rc) as [[HCm _] _].
assert (Rsp : 2 ^ 46 <= spe - 320 /\ spe <= 2 ^ 47) by lia.
(* ---- the image facts: the GOT words, the cells, their bounds ---- *)
destruct (alx_const _ _ _ LAWS lyc Sc Hpc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kgotuar).
rewrite (YC1fP.pal_cell _ HPAL) in Kcell.
rewrite (YC1fP.pal_got_shadow _ HPAL), (YC1fP.pal_cell _ HPAL) in Kgot.
rewrite HGOTU in Kgotuar. change (B_prog_val (A_OBJ 1)) with (VAL (A_OBJ 1)) in Kgotuar.
pose proof HUARC as (Hu4096 & Huhi & Hu0 & Hu1 & Hu12).
change (B_prog_val (A_OBJ 0)) with (VAL (A_OBJ 0)) in Hu0.
change (B_prog_val (A_OBJ 1)) with (VAL (A_OBJ 1)) in Hu1.
change (B_prog_val (A_OBJ 12)) with (VAL (A_OBJ 12)) in Hu12.
unfold kLowMemEnd in Huhi.
pose proof (YC1fP.pal_got_cell _ HPAL) as D012.
pose proof (YC1fP.pal_got_uar_disj _ HPAL) as (D10 & D112).
assert (Dimg : forall i, (i < 39)%nat -> 4096 <= VAL (A_OBJ i) /\ VAL (A_OBJ i) + 8 <= 2 ^ 32).
{ intros i Hi. pose proof (pa_obj_img (PAImg := PA) i Hi) as HH. change (@pa_lo _ _ PA) with IMG_LO_B in HH.
  change (@pa_hi _ _ PA) with IMG_TOP_B in HH. unfold IMG_LO_B, IMG_TOP_B in HH. lia. }
pose proof (Dimg 0%nat ltac:(lia)) as [Di0 Di0'].
pose proof (Dimg 1%nat ltac:(lia)) as [Di1 Di1'].
pose proof (Dimg 12%nat ltac:(lia)) as [Di12 Di12'].
(* ---- the environment of the entry state ---- *)
remember (Eimg (L := B_prog_listing) (PI := PA) (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (as_uar_cell B)]))
  as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = YK11.getr regs 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = YK11.getr regs 3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = YK11.getr regs 4)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spe) by (rewrite E2; exact Hsp).
(* ---- the symbolic state at the entry ---- *)
assert (HS : st_ok_pi SEGS VAL E ss_exr1
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + EXR_ENTRY)) memc (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_exr1. apply pa_entry_st_ok_full.
  - subst E; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold exr_regions1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
    + rewrite EO0, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. apply exr_val_mem_of_rdword. exact Kgot.
    + rewrite EO12, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. apply exr_val_mem_of_rdword. exact Kcell.
    + rewrite EO1, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ _ 0 8 (SOff 33 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      rewrite Z.add_0_r. apply exr_val_mem_of_rdword. exact Kgotuar.
    + rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs E _ _ 0 4 (SLit 1) 1);
      [cbn [sv_denot]; reflexivity | lia | lia |].
      rewrite Z.add_0_r. apply exr_val_mem_of_rd32. exact Kuar.
  - apply pairwise_disjoint_of_extents. unfold exr_regions1, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite EO0, EO1, EO12, E33, !unsigned_lit_small by lia. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [exr_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    try change (2 ^ 0) with 1. rewrite ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try (unfold SHADOW_OFF; lia); try lia. }
assert (SHOK : sh_ok rsegs EXR_Bx [] E (mrestrict (w_H W) memc)) by apply Forall_nil.
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS P PLAW).
unfold cfg_at. rewrite <- exr_entry_pc.
change (SRr SEGS W (mkCfg (YK11.mkst regs (Z_to_bv 64 (BASE + EXR_ENTRY)) memc (YK11.seg_rom SEGS)) mdc) Q).
(* ---- the run: slots 1944 .. 1972, to the `jal frame_alloc_1` ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM EXR_Bspan.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spe - sp0));
  [reflexivity | cbn [YP09.r_base]; rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
(* what the stores left alone: everything outside the save area [spe - 288, spe) *)
assert (KEEP : forall z, 0 <= z < 2 ^ 64 -> ~ (spe - 288 <= z < spe) ->
  aview rsegs (w_H W) (ms_mem ms) z = aview rsegs (w_H W) memc z).
{ intros z Hz Hnot. apply aview_eq_of. apply HFr.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  intros (r & Hin & Hr). unfold ss_exr1, exr_regions1 in Hin. cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia |]).
  destruct Hin. }
assert (GROW : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (exr_apresent_grow (w_H W) memc (ms_mem ms) a HG Ha)).
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (10%bv : bv 5) R10.
prreg HS (19%bv : bv 5) R19. prreg HS (25%bv : bv 5) R25. prreg HS (27%bv : bv 5) R27.
(* the realigned frame base s1 = sp = (spe - 288) & -32 *)
assert (US1 : U E (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32))) = exve_s1 spe).
{ unfold exve_s1. rewrite exve_land32.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Usp.
  rewrite (zcanon_id (spe + -288)) by (unfold M64; lia).
  change (zcanon (-32)) with (Z.land (- 2 ^ 5) (Z.ones 64)).
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite land_neg_pow2 by lia.
  change (2 ^ 5) with 32.
  replace (spe + -288) with (spe - 288) by lia.
  pose proof (Z.mod_pos_bound (spe - 288) 32 ltac:(lia)).
  unfold zcanon, M64. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
assert (US1b : U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32))) (SLit 0)) = exve_s1 spe).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, US1, (zcanon_id 0) by (unfold M64; lia).
  rewrite Z.add_0_r. apply zcanon_id. unfold M64, exve_s1. rewrite exve_land32.
  pose proof (Z.mod_pos_bound (spe - 288) 32 ltac:(lia)). lia. }
lazymatch goal with |- SRr _ _ (mkCfg (YK11.mkst ?rT ?pcT ?mT _) ?dT) _ =>
  assert (Epc : pcT = w64 (pc_stack_malloc (as_code B) 1)) by (unfold w64; rewrite <- HSM1PC; reflexivity);
  rewrite Epc; apply (Hk rT mT dT) end.
- exact HJ.
- exact HPM.
- rewrite R1. unfold w64. rewrite <- exr_ret1_pc. reflexivity.
- rewrite R2. unfold w64. rewrite <- US1. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity.
- rewrite R9. unfold w64.
  first [ rewrite <- US1b; unfold U; rewrite Z_to_bv_bv_unsigned; reflexivity
        | rewrite <- US1; unfold U; rewrite Z_to_bv_bv_unsigned; reflexivity ].
- rewrite R3, E3. reflexivity.
- rewrite R4, E4. reflexivity.
- rewrite R8, E2. unfold w64. rewrite <- Hsp. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
- rewrite R10. reflexivity.
- rewrite R19, E10. reflexivity.
- rewrite R25, E32. reflexivity.
- rewrite R27, E11. reflexivity.
- intros o r Hin. replace (spe - 288 + o) with (spe + (o - 288)) by lia.
  unfold exv_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin];
    [injection Hin as <- <-;
     eapply (exr_saved_of _ _ _ _ _ _ _ _ _ _ _ _ _ HS);
     [ cbn [ss_mem setpc]; repeat (first [left; reflexivity | right])
     | exact Usp
     | cbn [In]; repeat (first [left; reflexivity | right])
     | rewrite HE, exr_ew_low by lia; reflexivity ] |]).
  destruct Hin.
- exact KEEP.
- exact GROW.
Qed.
End R1.

Print Assumptions exve_run1.
