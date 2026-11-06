(* fuzz_preset, image B' (asan-ubsan d663f82d, the #102 pin), slice RD-GROW: the program walk of grow (B' 0x87058, 108
   instructions) against the kit's tgrow_specX (lib/A/PRH_FnReader.v) at the image-B instances (PrhImg prh_img_B, listing
   B_prog_listing with PL_prog_B / PI_prog_B); its callee fuzz_realloc is taken as the kit's text tfuzz_realloc_specX
   (lib/A/PRH_FnAlloc.v), a STATED HYPOTHESIS until S1's walk lands.
   FORM: cgif's per-function walk over a CONCRETE listing with GENERIC image facts (cgif lib/A/AC8a.v:32): the listing
   is lib/B/Listing_prog.v (B_prog_listing, the whole target range), the image is any PAImg instance of it
   (PG); the image facts the walk reads (grow's entry, the shadow-base GOT word and cell) are Section hypotheses that
   PAImg_prog.v's PI_prog_B meets. The engine is YC80x.v / YC80xf.v (SRr_run_pi_tok_AJx(f) over YCbqG's
   ajournal_x) stepped over the listing's ptree; the calls go through the engine's YCbqGcallW.v aj_call_xW.
   FILE SET: the kit's cut 7cdbb61b5fa0, as it is (its kit texts PRH_FnReader f1ae32e3b2cd,
   PRH_FnAlloc 4d8aeba047e5, PRH_Base ef7c8ca98529; its images, listing, engine and start-up files), plus this lane's
   files; PwGrowG.v / PwGrowLive.v are the shared image-free halves (one copy for A' and B'; image A's writer owns their
   changes).
   THE FREE / REALLOC MOVE: both texts are restated for it (SRr' segs RZ_cf, fpostWmR / fpostmR at wle' segs RZ_cf, the
   hull budget and use, the world-free refusal evidence, the guarded exclusion at the kids-refused arm); the runners
   are their R forms (paj_run_xfR / paj_run_xf_invR at wle'), grB_pre takes the hull budget, and grB_Q / grB_KR are
   the kit's named posts tgrP_Q / tfrP_Q.
   TEMPLATE (rule 24, not a donor): a finished grow walk over the OLD build is at
   proofs/omx-clap-core/fuzz_preset/lib/B/Prog/grow.v (blob 35bda9d02b, old entry
   0x869b8): read for its segment cuts only; never Required, cited or copied.
   The generic (image-free) half of this walk is lib/A/Prog/PwGrowG.v: this file writes image B's RUN
   lemmas, its entry state, and its two UBSan not-taken lemmas, and imports the rest.
   IMAGE B's OWN CHECKS (measured, the B' trap note :218-221): two UBSan checks trap to
   `unimp` at 0x871c0 - 0x87088 `beqz a0` (NULL: v non-null) and 0x87094 `bnez s8` after `andi s8,a0,7` (ALIGN: v
   8-aligned). Both are not taken under the kit's premises v <> 0 and v mod 8 = 0; each is its own lemma below.
   Every conclusion is srealizes through SRr (YA0n.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI00 YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK06 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC80xf YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PwGrowG PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetCfnB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* grow's entry slot in B_prog_listing: DERIVED, PAImg_prog.v B_entry_grow (slot 5731), times the slot width 4 *)
Definition GROW_OFF_B : Z := 4 * 5731.
(* LENGTH: grow's frame in image B, pi_frame F_grow at prh_img_B (its one `addi sp, sp, -96`) *)
Definition GROW_FR_B : Z := 96.
Lemma GROW_FR_B_ok : GROW_FR_B = @pi_frame prh_img_B F_grow.
Proof. vm_compute. reflexivity. Qed.
Lemma GROW_OFF_B_ok : B_prog_sigma AS_grow = B_prog_val A_TEXT + GROW_OFF_B.
Proof. vm_compute. reflexivity. Qed.

(* the symbolic entry state. Atoms: 0..31 the entry registers (sr_atoms), 32 the shadow base (the value of the
   shadow-base cell), 33..37 v's type, kids, keys, n, cap. *)
Definition growB_vA : YP09.region := YP09.mkRegion (Some 10%nat) 0 40 24 40
  [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0))].
Definition growB_vB : YP09.region := YP09.mkRegion (Some 10%nat) 40 56 48 56
  [YP09.mkChunk 40 (CVal 8 (SOff 36 0)); YP09.mkChunk 48 (CVal 8 (SOff 37 0))].
(* v's first region after the kids realloc: v + 24 holds the new kids block (atom 42, the kids call's result) *)
Definition growB_vA2 : YP09.region := YP09.mkRegion (Some 10%nat) 0 40 24 40
  [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 42 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0))].
Definition growB_regions : smem := [stack_region GROW_FR_B; growB_vA; growB_vB; got_regionP; bcell_regionP 32].
(* LENGTH / DERIVED: the stack between alloc_ceiling (asan_consts' lower bound) and 2 ^ 47 (astk_ok); v below 2 ^ 47 *)
Definition growB_facts : facts :=
  mkFacts [(2%nat, mkAF alloc_ceiling (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 56) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 3)] [] [].
Definition ss_growB0 : sstate := mkSS GROW_OFF_B sr_atoms growB_regions None growB_facts.
Definition growB_Bx : sv := SOff 32 0.
Definition growB_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition growB_SH : list shent := [mkSHE 10 0 56].
Definition growB_extra (ty kids keys n cap : Z) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 ty; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n; Z_to_bv 64 cap].

(* lia without the universally quantified hypotheses (image A's flia, lib/A/Prog/PwGrow.v: the tuned lia instantiates
   them, which explodes in a walk's large contexts); the segment files use it *)
Ltac flia := repeat match goal with
  | H : forall _ : Z, _ |- _ => clear H
  | H : forall _ : word, _ |- _ => clear H
  | H : forall _ : nat, _ |- _ => clear H
  end; lia.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {PG : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PG).
#[local] Notation VAL := (@pa_val _ B_prog_listing PG).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PG).
#[local] Notation BASE := (@pa_val _ B_prog_listing PG A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the engine's laws at the harness head length (one named hypothesis, HL = cf_head) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* image facts of the instance (PAImg_prog.v's PI_prog_B meets each by computation) *)
Hypothesis HENT : SIGMA AS_grow = BASE + GROW_OFF_B.
Hypothesis HGOT : as_got_shadow B = VAL (A_OBJ 0).
Hypothesis HCELL : as_shadow_cell B = VAL (A_OBJ 12).
Hypothesis HGC : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 0).
(* the runtime's errno cell is image bytes (YC1fP's PALib field pal_env, api_env; with HGOT / HCELL / HGC the PALib
   facts the walk reads) *)
Hypothesis HENV : api_env SEGS B.
Hypothesis HLH : @pa_lo _ B_prog_listing PG = YImgTop.IMG_LO_B /\ @pa_hi _ B_prog_listing PG = YImgTop.IMG_TOP_B.
(* the two image cells the walk reads lie in loaded segments (PI_prog_B: by computation) *)
Hypothesis HC0 : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i).
Hypothesis HC12 : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 12) + i).
(* the callee's text: the kit's tfuzz_realloc_specX at image B's instances, a STATED HYPOTHESIS until slice S1's walk *)
Hypothesis HREALLOC : @tfuzz_realloc_specX fx rc ci cp prh_img_B RL B_prog_listing PG B ARx SK.
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Existing Instance prh_img_B.
(* the alloc.c statics (the program's PST) are image bytes (prh_img_B's pi_g_* in a loaded segment: by computation) *)
Hypothesis HPST : forall a, Exists (in_zr a) PST -> in_img SEGS a.
(* ... and not read-only bytes (they are in a writable data segment, off the RELRO range: by computation at
   PI_prog_B). What carries the read-only view arodata_okP across the kids call to the keys call: the journal's image
   clause keeps an image byte only off PST (CawA102's finding, the same fact as its cwi_pst_rw) *)
Hypothesis HPSTRW : forall a, Exists (in_zr a) PST ->
  ~ in_roP SEGS (@pa_relro_lo _ B_prog_listing PG) (@pa_relro_hi _ B_prog_listing PG) a.

Definition RUNB := @paj_run_xf fx rc SK B_prog_listing PL_prog_B PG B PST ARx _ LAWS.
(* the same runner carrying a memory invariant P (walk-S6's YC80xf_inv.v): the walk's P is the m-form keep
   `memnorm mem -> memnorm m`, kept ABSTRACT inside the walk (clearbody) and instantiated once at its top *)
Definition RUNBP (P : (word -> option byte) -> Prop) (PLAW : srr_inv_laws SEGS P) :=
  @paj_run_xf_inv fx rc SK B_prog_listing PL_prog_B PG B PST ARx _ LAWS P PLAW.

(* THE ENTRY STATE of image B's grow: the kit's premises give st_ok_pi of ss_growB0 and the shadow window sh_ok. The frame
   is 96 bytes (GROW_FR_B), image A's is 80: that and the entry offset are the only image numbers here. *)
Lemma growB_entry : forall ly S Hp (W : world SEGS) regs mem md ch v ty num str kids keys n cap,
  afn_pre_x SEGS B ARx (@STK_grow prh_img_B) ly S Hp W regs mem md ch ->
  getr regs 10 = w64 v -> v mod 8 = 0 -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (v + 56 <= spZ regs - GROW_FR_B \/ spZ regs <= v) ->
  (v + 56 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= v) -> (v + 56 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= v) ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  pj_hdrR SEGS (mrestrict (w_H W) mem) v ty num str kids keys n cap ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (growB_extra ty kids keys n cap))) ss_growB0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GROW_OFF_B)) mem (seg_rom SEGS))) /\
  sh_ok SEGS growB_Bx growB_SH (Eimg (Ereg regs (growB_extra ty kids keys n cap))) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch v ty num str kids keys n cap HPRE H10 Hv8 Hv4096 Hvhi Hvstk Hd0 Hd12 Happ HH HRA.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : GROW_FR_B <= @STK_grow prh_img_B) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof HH as ((_ & HRW) & (Hty & Vty) & _ & _ & (Hkids & Vkids) & (Hkeys & Vkeys) & (Hn & Vn) & (Hcap & Vcap)).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite HGOT, HCELL in Kgot. rewrite HCELL in Kcell.
pose proof (pa_obj_img 0 ltac:(lia)) as (O0lo & O0hi). pose proof (pa_obj_img 12 ltac:(lia)) as (O12lo & O12hi).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
destruct HLH as [HLo HHi]. rewrite HLo in O0lo, O12lo. rewrite HHi in O0hi, O12hi.
unfold YImgTop.IMG_LO_B, YImgTop.IMG_TOP_B in *.
set (E := Eimg (Ereg regs (growB_extra ty kids keys n cap))).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (growB_extra ty kids keys n cap) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = w64 v).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact H10. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = v) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth growB_extra] in E32, E33, E34, E35, E36, E37.
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (UO0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite EO0; apply unsigned_lit_small; lia).
assert (UO12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite EO12; apply unsigned_lit_small; lia).
assert (DV : forall k w, ew E k = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 w).
{ intros k w Hk Hw. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hw. rewrite Z.add_0_r. reflexivity. }
rewrite restrict_mkst_fx. split.
- apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold growB_regions. repeat apply Forall_cons; try apply Forall_nil.
    * unfold stack_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
      split; [unfold GROW_FR_B; lia|]. split; [unfold GROW_FR_B; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold GROW_FR_B in *. lia.
    * unfold growB_vA, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply HRW; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ v 0 4 (SOff 33 0) ty); [apply DV; [exact E33 | lia] | exact Hty | lia |].
         rewrite Z.add_0_r. exact Vty.
      -- apply (chunk_ok_val SEGS E _ v 24 8 (SOff 34 0) kids); [apply DV; [exact E34 | lia] | exact Hkids | lia | exact Vkids].
      -- apply (chunk_ok_val SEGS E _ v 32 8 (SOff 35 0) keys); [apply DV; [exact E35 | lia] | exact Hkeys | lia | exact Vkeys].
    * unfold growB_vB, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply HRW; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ v 40 8 (SOff 36 0) n); [apply DV; [exact E36 | lia] | exact Hn | lia | exact Vn].
      -- apply (chunk_ok_val SEGS E _ v 48 8 (SOff 37 0) cap); [apply DV; [exact E37 | lia] | exact Hcap | lia | exact Vcap].
    * unfold got_regionP, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UO0.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [apply DV; [exact EO12 | lia] | change (8 * Z.of_N 8) with 64; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * unfold bcell_regionP, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UO12.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
        [apply DV; [exact E32 | unfold SHADOW_OFF; lia] | change (8 * Z.of_N 8) with 64; unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold growB_regions, stack_region, growB_vA, growB_vB, got_regionP, bcell_regionP.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold extent_of_region, zdisj.
    cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite ?U2, ?U10, ?UO0, ?UO12. unfold GROW_FR_B in *. repeat split; lia.
  + unfold facts_ok, growB_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U10, U32.
    split; [split; [|split; [|split; [| exact I]]] | split; exact I].
    * split; [unfold alloc_ceiling; lia|]. split; [change (2 ^ 4) with 16; exact Hal16 | lia].
    * split; [lia|]. split; [change (2 ^ 3) with 8; exact Hv8 | lia].
    * split; [unfold SHADOW_OFF; lia|]. split; [vm_compute; reflexivity | lia].
- unfold sh_ok, growB_SH. apply Forall_cons; [|apply Forall_nil]. split.
  + unfold growB_Bx. cbn [she_m she_lo she_hi]. rewrite !U_SOff, U32, U10, !Z.add_0_r, !zcanon_id by (unfold M64, SHADOW_OFF; lia).
    change (rd_of SEGS (mrestrict (w_H W) mem)) with (aview SEGS (w_H W) mem). exact HRA.
  + unfold app_apart, growB_Bx. cbn [she_m she_lo she_hi]. intros a Ha.
    rewrite !U_SOff, U32, U10, !Z.add_0_r, !zcanon_id in * by (unfold M64, SHADOW_OFF; lia).
    apply Happ. lia.
Qed.

(* fpre's return-address bound at grow's two fuzz_realloc calls: the return slots i = 48 (kids) and i = 68 (keys), each
   a CLOSED lemma over PRW_StepKit's pa_slot_lt_ceil_b, the one copy (the lead's engine trap, measured:
   never vm_compute the slot check inside the walk) *)
Lemma growB_ret48_ceil : bv_unsigned (Z_to_bv 64 (BASE + (GROW_OFF_B + 4 * 48))) < YM05.alloc_ceiling.
Proof.
pose proof (@pa_B_ok _ B_prog_listing PG) as (HB0 & HB40 & _).
rewrite unsigned_lit_small by (unfold GROW_OFF_B; lia).
exact (pa_slot_lt_ceil_b (L := B_prog_listing) (PL := PL_prog_B) (PI := PG) (GROW_OFF_B + 4 * 48)
  ltac:(unfold GROW_OFF_B; lia) ltac:(vm_compute; reflexivity)).
Qed.
Lemma growB_ret68_ceil : bv_unsigned (Z_to_bv 64 (BASE + (GROW_OFF_B + 4 * 68))) < YM05.alloc_ceiling.
Proof.
pose proof (@pa_B_ok _ B_prog_listing PG) as (HB0 & HB40 & _).
rewrite unsigned_lit_small by (unfold GROW_OFF_B; lia).
exact (pa_slot_lt_ceil_b (L := B_prog_listing) (PL := PL_prog_B) (PI := PG) (GROW_OFF_B + 4 * 68)
  ltac:(unfold GROW_OFF_B; lia) ltac:(vm_compute; reflexivity)).
Qed.

(* ---- THE STATEMENT LAYER (re-statements only; nothing here is a walk): one record of grow's entry data, so every
   segment lemma names the same entry state (image A's gr_in, the string walk's ps_in), the text's premises over
   it VERBATIM, and the two post bodies by the kit's NAMED posts (tgrP_Q for grow, tfrP_Q for fuzz_realloc), so neither can
   drift from its text.
   THE TEXT: tgrow_specX of lib/A/PRH_FnReader.v, restated for the free / realloc move (the conclusion at
   SRr' segs RZ_cf and fpostWmR, the hull budget premise and the hull use, the world-free refusal evidence, the guarded
   exclusion at the kids-refused arm), over the earlier cut 7cdbb61b5fa0 (no DW; the live room per event, prh_live_evs
   over prhPg_evs .. []; the two REFUSAL arms with their OUTCOME EXCLUSION and fuzz_realloc's refusal ledger,
   `mod 2 ^ 64` count); it carries the callee's refused ledgers itself.
   fuzz_realloc's text: tfuzz_realloc_specX of lib/A/PRH_FnAlloc.v, restated the same way (the realloc pair in u_fix,
   the live premise guarded by cnt <> fail, the two OUTCOME clauses). ---- *)
Record grB_in : Type := mkGrBIn {
  gb_ly : alayout; gb_S : astate; gb_Hp : list Z; gb_W : world SEGS;
  gb_regs : bvmap 5 word; gb_mem : word -> option byte; gb_md : Model; gb_ch : list (Z * Z * Z);
  gb_e : Z; gb_v : Z; gb_ty : Z; gb_num : Z; gb_str : Z; gb_kids : Z; gb_keys : Z; gb_n : Z; gb_cap : Z;
  gb_kb : list Z; gb_yb : list Z;
  gb_Lam : list (Z * Z); gb_peak : Z; gb_cnt : Z; gb_fail : Z; gb_ran : Z;
  gb_most : Z; gb_own : Z
}.
(* the kit's footprint of grow (tgrow_specX's fpostWmR argument) *)
Definition grB_FP (D : grB_in) : list (Z * Z) :=
  [(gb_v D + 24, gb_v D + 40); (gb_v D + 48, gb_v D + 56)] ++
  ablocks_fp (prhReader_ab (kids_blkR (gb_kids D) (gb_cap D) ++ keys_blkR (gb_ty D) (gb_keys D) (gb_cap D))).
(* the text's premises (the text :815-861), at one record, in the text's order *)
Definition grB_pre (CTX0 : list (list Z)) (D : grB_in) : Prop :=
  fpre B ARx STK_grow (gb_ly D) (gb_S D) (gb_Hp D) (gb_W D) (gb_regs D) (gb_mem D) (gb_md D) (gb_ch D) /\
  prh_univ_closure B CTX0 /\
  (exists ch, achain (gb_ly D) (aview SEGS (w_H (gb_W D)) (gb_mem D)) (spZ (gb_regs D) - pi_frame F_grow)
     (prh_s0 F_grow (gb_v D)) ch) /\
  room_live_cf (gb_S D) /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (gb_S D)))
    (prhPg_evs (gb_ty D =? 6) (gb_n D) (gb_cap D) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (gb_S D)))
    (prhPg_evs (gb_ty D =? 6) (gb_n D) (gb_cap D) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  PresetHullBudget.hull_budget (gb_S D) (prhPg_evs (gb_ty D =? 6) (gb_n D) (gb_cap D) []) /\
  getr (gb_regs D) 10 = w64 (gb_v D) /\ gb_v D <> 0 /\ gb_v D mod 8 = 0 /\
  pj_hdrR SEGS (mrestrict (w_H (gb_W D)) (gb_mem D)) (gb_v D) (gb_ty D) (gb_num D) (gb_str D) (gb_kids D) (gb_keys D)
    (gb_n D) (gb_cap D) /\
  pj_slots_atR (prh_lin (gb_Lam D)) (gb_ty D) (gb_kids D) (gb_keys D) (gb_n D) (gb_cap D) /\
  pj_apartR (kids_blkR (gb_kids D) (gb_cap D) ++ keys_blkR (gb_ty D) (gb_keys D) (gb_cap D)) (gb_v D) /\
  fwin (gb_ly D) (gb_W D) (gb_regs D) (gb_mem D) (gb_e D) /\
  prhReader_at B (gb_ly D) (gb_S D) (gb_Lam D) (gb_regs D) (gb_e D) (gb_v D) 56 /\
  range_addressable (aview SEGS (w_H (gb_W D)) (gb_mem D)) SHADOW_OFF (gb_v D) 56 /\
  (gb_n D = gb_cap D -> bytes_at (gb_W D) (gb_mem D) (gb_kids D) (gb_kb D) /\
     Z.of_nat (length (gb_kb D)) = 56 * gb_cap D /\
     (gb_ty D = 6 -> bytes_at (gb_W D) (gb_mem D) (gb_keys D) (gb_yb D) /\ Z.of_nat (length (gb_yb D)) = 8 * gb_cap D)) /\
  prh_ledger B (gb_ly D) (gb_S D) (gb_Hp D) (gb_W D) (gb_mem D) (gb_Lam D) (gb_peak D) (gb_cnt D) (gb_fail D) (gb_ran D)
    (gb_most D) (gb_own D) /\
  gb_cnt D + 2 < 2 ^ 64 - 1 /\
  (gb_n D = gb_cap D -> 56 * cap2R (gb_cap D) + cf_head < cf_malloc_max /\
     prh_live_evs (gb_S D) (prhPg_evs (gb_ty D =? 6) (gb_n D) (gb_cap D) [])).
(* the text's post body: the kit's NAMED post tgrP_Q (lib/A/PRH_FnReader.v, the projection layer, checked against the text
   by tgrP_Q_check), over the entry values (near-copy row PwGrowB.v:299, replaced by the alias) *)
Definition grB_Q (most own : Z)
  (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (v ty num str kids keys n cap : Z) (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran : Z)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tgrP_Q B most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran.
Definition grB_QD (D : grB_in) :=
  grB_Q (gb_most D) (gb_own D)
    (gb_ly D) (gb_S D) (gb_Hp D) (gb_W D) (gb_mem D) (gb_v D) (gb_ty D) (gb_num D) (gb_str D) (gb_kids D)
    (gb_keys D) (gb_n D) (gb_cap D) (gb_kb D) (gb_yb D) (gb_Lam D) (gb_peak D) (gb_cnt D) (gb_fail D) (gb_ran D).
(* the conclusion at one record: the m-form caller-window post at the move's world relation (fpostWmR = fpostWR over fQmn) *)
Definition grB_post (D : grB_in) : world SEGS -> config -> Prop :=
  fpostWmR B ARx SK (wle' SEGS RZ_cf) STK_grow (gb_e D) (grB_FP D) (gb_regs D) (gb_ly D) (gb_S D) (gb_Hp D) (gb_W D) (gb_mem D) (gb_md D)
    (grB_QD D).

(* fuzz_realloc's post body: the kit's NAMED post tfrP_Q (lib/A/PRH_FnAlloc.v, the projection layer, checked against
   tfuzz_realloc_specX by tfrP_Q_check), at a call from allocator state ly S Hp W with old block p (user size k, bytes
   old) and request n (near-copy row PwGrowB.v:506, replaced by the alias) *)
Definition grB_KR (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (p k n : Z) (old : list Z)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tfrP_Q B ly S Hp W p k n old Lam peak cnt fail ran most own.
(* the kids realloc (B 0x87114: a0 = kids, a1 = 56 cap') runs at the entry's allocator state (grow makes no allocator
   call before it); for cap = 0 its old block is NULL (pj_slots_atR) *)
Definition grB_KR_kids (D : grB_in) :=
  grB_KR (gb_ly D) (gb_S D) (gb_Hp D) (gb_W D) (gb_kids D) (56 * gb_cap D) (56 * cap2R (gb_cap D))
    (if gb_cap D =? 0 then [] else gb_kb D) (gb_Lam D) (gb_peak D) (gb_cnt D) (gb_fail D) (gb_ran D)
    (gb_most D) (gb_own D).

(* THE RECORD CHECK (re-statement only; image A's tgrow_specX_records): the text at image B's instance
   IS, record by record, grB_pre -> SRr' .. grB_post. So grB_pre is the text's premises verbatim and grB_Q its post
   body (the kit's tgrP_Q), machine-checked. *)
Lemma growB_tgrow_records : forall CTX0,
  @tgrow_specX fx rc ci cp prh_img_B RL B_prog_listing PG B ARx SK CTX0 <->
  (forall D : grB_in, grB_pre CTX0 D ->
     SRr' SEGS RZ_cf (gb_W D) (cfg_at SEGS (SIGMA AS_grow) (gb_regs D) (gb_mem D) (gb_md D)) (grB_post D)).
Proof.
intros CTX0. split.
- intros H D HPD. destruct D as [ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran
    most own].
  unfold grB_pre in HPD. cbn [gb_ly gb_S gb_Hp gb_W gb_regs gb_mem gb_md gb_ch gb_e gb_v gb_ty gb_num gb_str gb_kids
    gb_keys gb_n gb_cap gb_kb gb_yb gb_Lam gb_peak gb_cnt gb_fail gb_ran gb_most gb_own] in HPD.
  destruct HPD as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18
    & H19 & H20).
  exact (H most own ly S Hp W regs mem md ch e v ty num str kids keys n cap
    kb yb Lam peak cnt fail ran H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20).
- intros H. unfold tgrow_specX.
  intros most own ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb
    Lam peak cnt fail ran H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.
  exact (H (mkGrBIn ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran most own)
    (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
      (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 H20)))))))))))))))))))).
Qed.

(* THE SEGMENTS of grow's walk are separate files that Require this one: PwGrowBCap0.v (cap = 0),
   PwGrowBCapnz.v (cap <> 0, and n < cap), PwGrowBArm7.v (arm 7). *)
End c.

(* THE WRONG-IMAGE GUARD (the owner's 21:45Z hazard): in this file's context the short name
   Img0.rsegs resolves to the PLAIN image's lib/Img0.v (measured with Locate). Every statement here takes its segments
   from the Section's PG : PAImg B_prog_listing, parametrically (the segment lemmas stay parametric in PG); at the
   image-B' instance PI_prog_B those segments ARE image B's, by conversion: *)
Lemma growB_segs_B : forall (rc : YM05.RunCeil),
  @pa_segs rc B_prog_listing (@PI_prog_B rc) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
Proof. intros rc. reflexivity. Qed.

