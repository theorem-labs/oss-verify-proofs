(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's FRAME HEADER stretch: the symbolic run from the return site of `jal frame_alloc_1` (B_prog_sigma
   AS_ex_value + 116, listing slot 1973) through the `jal ex_ws` (slot 2014, `PCall AS_ex_ws`) to ex_ws's entry
   (B_prog_sigma AS_ex_ws, slot 2794), in continuation form (exve_run2), for ExvEntry's segment lemma exvB_entry
   (lib/B/Prog/ExvB_Entry.v).
   The stretch (42 slots): `mv s8, a0`; `j`; `mv s2, s8`; `bnez s8` TAKEN (the frame atom is >= 4096, so the alloca
   probe loop of slots 1978-1984 is never run); `sd s2, 176(s1)`; the frame header words 0x41b58ab3 / an image address
   (PAddHi (A_OBJ 2)) / ex_value's entry (PAddHi A_TEXT) stored at frame + 0 / 8 / 16; s10 = (s2 >> 3) + s9 =
   shadow_addr frame; the twelve shadow bytes f1 f1 f1 f1 f8 f2 f2 f2 f8 f3 f3 f3 at s10 + 0 .. 11; `mv a0, s3`;
   `jal ex_ws`. The run stops at the call with ra = B_prog_sigma AS_ex_value + 284 (the C1 cut).
   Engine: YC1fPx's paj_run_x over YCbqG's ajournal_x at L := B_prog_listing, PL := PL_prog_B, PI := PI_prog_B
   (template: lib/A/Prog/S8aEntry.v, origin/cold/h-hpreset-7-walk-S8a, the same stretch on image A).
   Every write is awr_byte's: 176(s1) is in the caller window [sp0 - STK, sp0) (first disjunct); the header and the
   shadow bytes are the class-1 frame (1, pos) of own and its shadow (in_frames, fourth disjunct).
   No released plain or UBSan file is Required and no lemma of one is cited.
   NUMERALS:
   - LENGTH: 288 (the prologue's `addi sp, sp, -288`), 32 / -32 (the `andi sp, sp, -32` realignment), 320 / 319
     (stack room the statement gives below the entry sp; the realignment slack), 176 / 184 (the slot 176(s1) and its
     end), 24 / 12 / 16 / 128 (frame header bytes, frame shadow bytes written, the class-1 frame's shadow and frame
     bytes), 8 / 3 (word width, shadow shift), 4096 / 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (address-space bounds),
     5 (log2 of the 32-byte alignment).
   - WORD: register numbers 1-4, 8-10, 18, 19, 24-27; 63 (the shift-amount mask of `srli`).
   - DERIVED: 116 (the return site of `jal frame_alloc_1` minus the entry), 284 (the return site of `jal ex_ws` minus
     the entry, the C1 cut 0x11c), atom number 32 of the symbolic engine (shadow_addr frame).
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
Lemma exve_land32_r2 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. change (-32) with (Z.lnot (Z.ones 5)). rewrite <- Z.ldiff_land.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 5) with 32. pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.

(* the listing position the run starts at (DERIVED: pc - B_prog_base): the slot after `jal frame_alloc_1` *)
Definition EXR2_RET1 : Z := B_prog_sigma AS_ex_value - B_prog_base + 116.

(* no shadow byte is read by the stretch: the token band is empty *)
Definition EXR2_Bx : sv := SLit 0.
Definition EXR2_Bspan : Z * Z := (0, 0).

(* the state at the return site: the slot 176(s1) (atom 9 = s1), the frame header (atom 10 = a0 = the frame) and the
   frame's own shadow (atom 32 = shadow_addr frame, the first extra atom) are writable; s9 (atom 25) is the shadow
   base, and (frame >> 3) + s9 is aliased to atom 32 *)
Definition exr2_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 176 184 176 184 [];
    YP09.mkRegion (Some 10%nat) 0 24 0 24 [];
    YP09.mkRegion (Some 32%nat) 0 12 0 12 [] ].
Definition exr2_sh : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 25 0).
Definition exr2_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 (2 ^ 47) 5);
           (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0)]
          []
          [ (exr2_sh, SOff 32 0) ].
Definition ss_exr2 : sstate := mkSS EXR2_RET1 sr_atoms exr2_regions None exr2_facts.

(* the shadow address the code computes is the one atom 32 names *)
Lemma exr2_alias : forall (E : env) (f : Z), 0 <= f < 2 ^ 47 ->
  ew E 10 = w64 f -> ew E 25 = w64 SHADOW_OFF -> ew E 32 = Z_to_bv 64 (shadow_addr f) ->
  sv_denot E exr2_sh = sv_denot E (SOff 32 0).
Proof.
intros E f Hf F10 F25 F32. unfold exr2_sh.
apply U_inj. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, !U_SLit.
rewrite F10, F25, F32. unfold w64. rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
rewrite (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite !Z.add_0_r. unfold shadow_addr.
rewrite (zcanon_id f) by (unfold M64; lia).
rewrite (zcanon_id (f / 8)) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
rewrite (zcanon_id (f / 8 + SHADOW_OFF)) by (unfold M64, SHADOW_OFF; lia).
rewrite (zcanon_id (SHADOW_OFF + f / 8)) by (unfold M64, SHADOW_OFF; lia). lia.
Qed.

Section R2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable B : asyms.  Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.

(* Pm is a memory invariant the run carries (YC80x.srr_inv_laws; ex_value takes Pm m := memnorm (e_mem E) -> memnorm m,
   the m-form keep of kit 4f18c75d4900); YC1fPx's _inv runner moves it across the run *)
Lemma exve_run2 : forall (W : world rsegs) (regs : bvmap 5 word) memc mdc
    STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k (spe q v pos : Z) (Q : world rsegs -> config -> Prop)
    (Pm : (word -> option byte) -> Prop),
  let s1 := Z.land (spe - 288) (-32) in
  let f := frame_addr lyc 1 pos in
  ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
  srr_inv_laws rsegs Pm -> Pm memc ->
  In (1, pos) own ->
  spZ regs = s1 -> s1 <= spe -> spe <= sp0 -> sp0 - STK <= spe - 320 ->
  4096 <= f -> f + 128 <= alloc_ceiling -> f mod 32 = 0 ->
  (forall a, f <= a < f + 128 -> apresent (w_H W) memc a) ->
  (forall i, 0 <= i < 16 -> apresent (w_H W) memc (shadow_addr f + i)) ->
  getr regs 2 = w64 s1 -> getr regs 9 = w64 s1 -> getr regs 8 = w64 spe ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 f -> getr regs 19 = w64 q -> getr regs 25 = w64 SHADOW_OFF -> getr regs 27 = w64 v ->
  (forall (regs' : bvmap 5 word) (memc' : word -> option byte) (mdc' : Model),
     ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc' mdc' k ->
     Pm memc' ->
     getr regs' 1 = w64 (B_prog_sigma AS_ex_value + 284) ->
     getr regs' 2 = w64 s1 -> getr regs' 9 = w64 s1 -> getr regs' 8 = w64 spe ->
     getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     getr regs' 10 = w64 q -> getr regs' 18 = w64 f -> getr regs' 24 = w64 f ->
     getr regs' 19 = w64 q -> getr regs' 25 = w64 SHADOW_OFF ->
     getr regs' 26 = w64 (shadow_addr f) -> getr regs' 27 = w64 v ->
     val_mem rsegs (mrestrict (w_H W) memc') (s1 + 176) 8 f ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 176 <= a < s1 + 184) -> ~ (f <= a < f + 24) ->
        ~ (shadow_addr f <= a < shadow_addr f + 12) ->
        aview rsegs (w_H W) memc' a = aview rsegs (w_H W) memc a) ->
     (forall a, apresent (w_H W) memc a -> apresent (w_H W) memc' a) ->
     SRr rsegs W (cfg_at (fx := fx) rsegs (B_prog_sigma AS_ex_ws) regs' memc' mdc') Q) ->
  SRr rsegs W (cfg_at (fx := fx) rsegs (B_prog_sigma AS_ex_value + 116) regs memc mdc) Q.
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k spe q v pos Q Pm s1 f
  HJ PLAW HPM Hown Hsp Hs1e Hspe Hstk Hf4096 Hfceil Hf32 Hfpres Hshpres
  R2 R9 R8 R3 R4 R10 R19 R25 R27 HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _).
destruct Hastk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HinF : In (1, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (alx_frames rsegs B ARx LAWS lyc Sc Hpc W memc mdc 1 pos HAR HinF) as (_ & HFapp & _ & _).
change (frame_addr lyc 1 pos) with f in HFapp. change (fs_frame_bytes 1) with 128 in HFapp.
(* the realigned frame base *)
assert (Hs1eq : s1 = spe - 288 - (spe - 288) mod 32) by exact (exve_land32_r2 (spe - 288)).
pose proof (Z.mod_pos_bound (spe - 288) 32 ltac:(lia)) as Hm32.
assert (Hs1al : s1 mod 32 = 0) by (rewrite Hs1eq, Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity).
assert (Hs1lo : spe - 319 <= s1 <= spe - 288) by lia.
assert (Hfeq : f = frame_addr lyc 1 pos) by reflexivity.
(* ---- the symbolic state at the return site ---- *)
remember (@Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 (shadow_addr f)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EN : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat -> ew E n = getr regs r).
{ intros n r Hn Hlt. subst E. rewrite Eimg_low by exact Hlt. exact (ew_Ereg_nat regs _ n r Hn). }
assert (E2 : ew E 2 = getr regs 2) by (apply EN; [reflexivity | unfold A_TEXT; lia]).
assert (E3 : ew E 3 = getr regs 3) by (apply EN; [reflexivity | unfold A_TEXT; lia]).
assert (E4 : ew E 4 = getr regs 4) by (apply EN; [reflexivity | unfold A_TEXT; lia]).
assert (E8 : ew E 8 = getr regs 8) by (apply EN; [reflexivity | unfold A_TEXT; lia]).
assert (E9 : ew E 9 = w64 s1) by (rewrite <- R9; apply EN; [reflexivity | unfold A_TEXT; lia]).
assert (E10 : ew E 10 = w64 f) by (rewrite <- R10; apply EN; [reflexivity | unfold A_TEXT; lia]).
assert (E19 : ew E 19 = w64 q) by (rewrite <- R19; apply EN; [reflexivity | unfold A_TEXT; lia]).
assert (E25 : ew E 25 = w64 SHADOW_OFF) by (rewrite <- R25; apply EN; [reflexivity | unfold A_TEXT; lia]).
assert (E27 : ew E 27 = w64 v) by (rewrite <- R27; apply EN; [reflexivity | unfold A_TEXT; lia]).
assert (E32 : ew E 32 = Z_to_bv 64 (shadow_addr f))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Rsh : SHADOW_OFF <= shadow_addr f <= SHADOW_OFF + 2 ^ 44) by (unfold shadow_addr; lia).
assert (HS : st_ok_pi SEGS VAL E ss_exr2
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + EXR2_RET1)) memc (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_exr2. apply pa_entry_st_ok_full.
  - subst E; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold exr2_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E9. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite E10. unfold w64. rewrite unsigned_lit_small by lia. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Hfpres. lia.
    + rewrite E32. rewrite unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
      split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
      split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Hshpres. lia.
  - apply pairwise_disjoint_of_extents. unfold exr2_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E10, E32. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold shadow_addr in *.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
    destruct HFapp as (HFa0 & [HFa1 | (HFa1 & HFa2)]);
    repeat match goal with |- _ /\ _ => split end; lia.
  - split; [|split; [exact I|]].
    + cbn [exr2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E10, E25, E32. unfold w64.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF in *; lia).
      change (2 ^ 5) with 32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end;
        try exact Hs1al; try exact Hf32; try (unfold SHADOW_OFF in *; lia).
    + cbn [exr2_facts f_alias alias_ok]. split; [|exact I].
      apply (exr2_alias E f); [lia | exact E10 | exact E25 | exact E32]. }
assert (SHOK : sh_ok SEGS EXR2_Bx [] E (mrestrict (w_H W) memc)) by apply Forall_nil.
unfold cfg_at. change (w64 (B_prog_sigma AS_ex_value + 116)) with (Z_to_bv 64 (BASE + EXR2_RET1)).
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS Pm PLAW).
paj_run_tok_x_inv RUN HS HJ SHOK HPM EXR2_Bspan.
{ (* the writes: 176(s1) in the caller window; the header and the shadow bytes in the class-1 frame of own *)
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (s1 - sp0));
  [reflexivity | cbn [YP09.r_base]; rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; lia
  | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat f);
  [reflexivity | cbn [YP09.r_base]; rewrite E10; unfold w64; apply unsigned_lit_small; lia | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros z Hzr. right; right; right.
    exists 1, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd].
    rewrite <- Hfeq. change (fs_frame_bytes 1) with 128. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (shadow_addr f));
  [reflexivity | cbn [YP09.r_base]; rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros z Hzr. right; right; right.
    exists 1, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd].
    rewrite <- Hfeq. change (fs_frame_bytes 1 / 8) with 16. lia. }
  apply awr_ok_nil. }
(* ---- at the call: ex_ws's entry, ra = the C1 cut ---- *)
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
unfold cfg_at in HK.
eapply HK; clear HK.
- exact HJ.
- exact HPM.
- rewrite P1; unfold w64; f_equal; vm_compute; reflexivity.
- rewrite P2, E2; exact R2.
- rewrite P9, E9; reflexivity.
- rewrite P8, E8; exact R8.
- rewrite P3, E3; reflexivity.
- rewrite P4, E4; reflexivity.
- rewrite P10, E19; reflexivity.
- rewrite P18, E10; reflexivity.
- rewrite P24, E10; reflexivity.
- rewrite P19, E19; reflexivity.
- rewrite P25, E25; reflexivity.
- rewrite P26, E32; reflexivity.
- rewrite P27, E27; reflexivity.
- (* 176(s1) holds the frame: the chunk the store left in the first region *)
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrs & _).
  cbn [ms_mem restrict ss_mem setpc] in Hrs.
  pose proof (Forall_inv Hrs) as HR1. unfold region_ok in HR1.
  cbn [YP09.r_base YP09.r_chunks base_val] in HR1. destruct HR1 as (_ & _ & _ & Hck1).
  pose proof (Forall_inv Hck1) as Hc176.
  assert (Hb9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  pose proof (val_of_chunk_ok SEGS E _ _ 176 8 (SOff 10 0) f Hc176) as HV. rewrite Hb9 in HV. apply HV.
  + cbn [sv_denot]. rewrite E10. unfold w64. rewrite unsigned_lit_small by lia. rewrite ?Z.add_0_r. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + cbn. lia.
- (* every byte outside the three written ranges is the one before the run *)
  intros z Hzb Hn1 Hn2 Hn3. apply aview_eq_of. apply HFr.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia.
  intros (r & Hin & Hr). unfold ss_exr2, exr2_regions in Hin. cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
     rewrite ?E9, ?E10, ?E32 in Hr; unfold w64 in Hr;
     rewrite ?unsigned_lit_small in Hr by (unfold SHADOW_OFF in *; lia); lia |]).
  destruct Hin.
- (* presence only grows *)
  intros a Ha. eapply apresent_grows; [exact HG | exact Ha].
Qed.
End R2.

Check exve_run2.
Print Assumptions exve_run2.
