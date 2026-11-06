(* fuzz_preset, image B' (asan-ubsan d663f82d, the #102 pin), slice RD-GROW: grow's WHOLE-FUNCTION statement.
   rule 24: proves grow (image B'); rule-24 CONFIRM for grow on both images in hand (telemetry 2026-10-30 00:40Z).
   - grow_holds_B: the kit's tgrow_specX (lib/A/PRH_FnReader.v), EXACTLY, at image B's instances over any PAImg instance PG
     of B_prog_listing, under this Section's hypotheses (PwGrowB.v's: the engine's laws, the static image facts and
     fuzz_realloc's text HREALLOC). It is the case split on cap = 0 over the two segments, PwGrowBCap0.growB_seg_cap0
     (cap = 0, hence n = cap: pj_slots_atR's n <= cap and pj_hdrR's 0 <= n) and PwGrowBCapnz.growB_seg_capnz (cap <> 0),
     read back into the text by PwGrowB.growB_tgrow_records.
   - grow_holds_B_inst: the same at the B' INSTANCE (B := YD2l.TfibB, PI := prh_img_B, L := B_prog_listing,
     PA := PI_prog_B, ci := CfImgB.CfImg_B, cp := CfParams_preset, RL := prh_room_live_a8, ARx := ARcf /\ xs_placed_cf,
     YGcallcf's ARxs), with every static image premise DISCHARGED by computation (grow's entry, the GOT word and the
     shadow cell through PALibB's record, the image bounds, the two cells in loaded segments, the alloc.c statics in
     a writable segment off the RELRO range) and the laws by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf. The one
     premise left is fuzz_realloc's text at this instance (owner: the B' allocator walk). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PwGrowG PwGrowLive PRW_StepKit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetCfnB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PwGrowB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PwGrowBArm7 PwGrowBCap0 PwGrowBCapnz.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallcf YG0lawscf YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP08 YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {PG : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PG).
#[local] Notation VAL := (@pa_val _ B_prog_listing PG).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PG).
#[local] Notation BASE := (@pa_val _ B_prog_listing PG A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HENT : SIGMA AS_grow = BASE + GROW_OFF_B.
Hypothesis HGOT : as_got_shadow B = VAL (A_OBJ 0).
Hypothesis HCELL : as_shadow_cell B = VAL (A_OBJ 12).
Hypothesis HGC : VAL (A_OBJ 0) + 8 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= VAL (A_OBJ 0).
Hypothesis HENV : api_env SEGS B.
Hypothesis HLH : @pa_lo _ B_prog_listing PG = YImgTop.IMG_LO_B /\ @pa_hi _ B_prog_listing PG = YImgTop.IMG_TOP_B.
Hypothesis HC0 : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 0) + i).
Hypothesis HC12 : forall i, 0 <= i < 8 -> in_img SEGS (VAL (A_OBJ 12) + i).
Hypothesis HREALLOC : @tfuzz_realloc_specX fx rc ci cp prh_img_B RL B_prog_listing PG B ARx SK.
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Existing Instance prh_img_B.
Hypothesis HPST : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Hypothesis HPSTRW : forall a, Exists (in_zr a) PST ->
  ~ in_roP SEGS (@pa_relro_lo _ B_prog_listing PG) (@pa_relro_hi _ B_prog_listing PG) a.

(* THE WHOLE FUNCTION: the kit's text, exactly *)
Theorem grow_holds_B : forall CTX0 : list (list Z),
  @tgrow_specX fx rc ci cp prh_img_B RL B_prog_listing PG B ARx SK CTX0.
Proof.
intros CTX0. apply (proj2 (growB_tgrow_records B ARx SK CTX0)).
intros D HPD.
destruct (Z.eq_dec (gb_cap D) 0) as [Hc0 | Hc0].
- (* cap = 0, so n = cap: pj_hdrR reads n as a u64 (0 <= n), pj_slots_atR has n <= cap *)
  assert (Hn : gb_n D = gb_cap D).
  { pose proof HPD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HH & HSLOT & _).
    pose proof HH as (_ & _ & _ & _ & _ & _ & (Hn0 & _) & _).
    pose proof HSLOT as (_ & (Hncap & _) & _ & _). lia. }
  eapply growB_seg_cap0; try eassumption.
- eapply growB_seg_capnz; try eassumption.
Qed.
End c.

(* ---- THE B' INSTANCE: the static image premises by computation ---- *)
(* image B's segments, FULLY QUALIFIED (CrcBp's trap: the closure also loads PLAIN image files) *)
#[local] Notation SEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
Definition growBi_in_img_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.
Definition growBi_in_ro_b (segs : list Segment) (rlo rhi a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    segs || ((rlo <=? a) && (a <? rhi)).
Definition growBi_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.
Lemma growBi_allb_sound : forall f P a, growBi_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold growBi_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.
Lemma growBi_in_img_b_sound : forall segs a, growBi_in_img_b segs a = true -> in_img segs a.
Proof.
intros segs a H. apply existsb_exists in H as (s & Hs & H). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs | lia].
Qed.
Lemma growBi_in_ro_b_complete : forall segs rlo rhi a, in_roP segs rlo rhi a -> growBi_in_ro_b segs rlo rhi a = true.
Proof.
intros segs rlo rhi a [(s & Hs & Hw & Hr) | Hr]; unfold growBi_in_ro_b; apply orb_true_intro; [left | right].
- apply existsb_exists. exists s. split; [exact Hs|]. rewrite Hw. cbn [negb andb].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
(* the computed checks, one closed goal each *)
Lemma growBi_pst_img : growBi_allb (growBi_in_img_b SEGS_B) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma growBi_pst_ro :
  growBi_allb (fun a => negb (growBi_in_ro_b SEGS_B B_prog_relro_lo B_prog_relro_hi a)) (@prh_pst prh_img_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma growBi_c0 : zallb (growBi_in_img_b SEGS_B) (B_prog_val (A_OBJ 0)) 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma growBi_c12 : zallb (growBi_in_img_b SEGS_B) (B_prog_val (A_OBJ 12)) 8 = true.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the guard: the segments the walk is over (pa_segs PI_prog_B) ARE image B's *)
Lemma growBi_segs_B : @pa_segs _ B_prog_listing PI_prog_B = SEGS_B.
Proof. reflexivity. Qed.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation CI := CfImgB.CfImg_B.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf (ci := CI) (cp := CP) SEGS TB ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Abbreviation RLI := (prh_room_live_a8 (cp := CP)).

Theorem grow_holds_B_inst : forall SK : YI16.sink_head,
  tfuzz_realloc_specX (ci := CI) (cp := CP) (RL := RLI) (PI := prh_img_B) (PA := PI_prog_B) TB ARcfx SK ->
  forall CTX0 : list (list Z),
  tgrow_specX (ci := CI) (cp := CP) (RL := RLI) (PI := prh_img_B) (L := B_prog_listing) (PA := PI_prog_B)
    TB ARcfx SK CTX0.
Proof.
intros SK HREALLOC CTX0.
pose proof (YGcallcf.AR_laws_x_xs (ci := CI) (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (ci := CI) (cp := CP) SEGS TB)) as LAWSx.
pose proof (YC1fP.palib_core (PI := PI_prog_B) TB PALibB.exvi_eh_palib) as PLC.
eapply (grow_holds_B (ci := CI) (cp := CP) (RL := RLI) (PG := PI_prog_B) TB ARcfx SK).
- exact LAWSx.
- exact GROW_OFF_B_ok.
- exact (palc_got_shadow _ PLC).
- exact (palc_cell _ PLC).
- exact (palc_got_cell _ PLC).
- exact (palc_env _ PLC).
- split; reflexivity.
- intros i Hi. apply growBi_in_img_b_sound.
  apply (zallb_sound _ 8 (B_prog_val (A_OBJ 0)) _ growBi_c0).
  try change (Z.of_nat 8) with 8. try change (@pa_val _ B_prog_listing PI_prog_B (A_OBJ 0)) with (B_prog_val (A_OBJ 0)).
  lia.
- intros i Hi. apply growBi_in_img_b_sound.
  apply (zallb_sound _ 8 (B_prog_val (A_OBJ 12)) _ growBi_c12).
  try change (Z.of_nat 8) with 8. try change (@pa_val _ B_prog_listing PI_prog_B (A_OBJ 12)) with (B_prog_val (A_OBJ 12)).
  lia.
- exact HREALLOC.
- intros a Ha. apply growBi_in_img_b_sound. exact (growBi_allb_sound _ _ a growBi_pst_img Ha).
- intros a Ha Hro. pose proof (growBi_allb_sound _ _ a growBi_pst_ro Ha) as H. cbv beta in H.
  pose proof (growBi_in_ro_b_complete SEGS_B B_prog_relro_lo B_prog_relro_hi a Hro) as H2.
  rewrite H2 in H. discriminate.
Qed.
End i.

(* the wrong-image check of the rebind brief (rule 7) *)
Set Printing Implicit. Unset Printing Notations.
About grow_holds_B_inst.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions grow_holds_B_inst.
