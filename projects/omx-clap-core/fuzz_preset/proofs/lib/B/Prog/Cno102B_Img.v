(* rule 24: no function proved
   rule 24: proves no function (kind: segment lemma)
   fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b): the
   INSTANCE WITNESS of check_no_overread's image record cnb_img (lib/B/Prog/Cno102B_Base.v :167-184, blob
   06098b64f859, a working branch 162ea90da065: the contract restated on the KIT CUT
   a working branch 7cdbb61b5fa0, comments only over its first cut form 20c89a1d4da2; the record's eight
   fields are unchanged from the f97c contract) at the image's own data, and the SATISFIABILITY WITNESSES, at the
   real binding, of three premises of cnb_pre: the cut's two new ones and the context premise.
   Lane CnoB102rR, sub-lane CutImg (the re-fit to the cut of sub-lane CnoBImg's file). Each field is a CLOSED lemma: a
   boolean checker evaluated by a guarded vm_compute on the concrete image, then the checker's soundness lemma; the
   assembly cnb_img_inst only unfolds the instance.
   THE IMAGE DATA OF RECORD (every path is the cut's blob, 7cdbb61b5fa0, carried unchanged into 162ea90da065):
     segments   rsegs of lib/B/Img0.v d17de1e3b380 (= images.AsanUbsan.M.loaded_segments, generated from the staged
                asan-ubsan binary; on the pins102 route that is d663f82d7f488d30, pau-preset-102).
     listing    lib/B/Listing_prog.v c97cc46b3e13 and lib/B/PAImg_prog.v 15fab93fe702 (the v3 listing, a
                pre-evaluated slot tree): PI_prog_B, B_prog_val, B_prog_sigma, B_prog_relro_lo / _hi.
     image top  lib/Reusable/YImgTop.v d2a97d3111ce (the RECORD regeneration for A' / B': IMG_TOP_B = 0x601000, B''s
                last PT_LOAD [0xa4560, 0x600010)); PAImg_prog.v B needs it (B_prog_range).
     statics    prh_img_B of lib/B/PRH_ImgB.v 3216eca68342: all SEVEN cells PRH_Base.v declares, with
                the widths: g_live 0x5ddda0:8, g_peak 0x5dddc0:8, g_count 0x5ddde0:8, g_fail_at 0xa6e00:8,
                g_ran_out 0x5dde00:1, g_most 0xa6e20:8, g_own_ran_out 0x5ddd80:1 (prh_pst); the seven addresses agree
                with the .symtab of the B' twin c90d4fa54d43160b (measured 2026-10-29).
     asyms      TfibB of lib/Reusable/YD2l.v 95803a8b9493, its as_errno = TFIB_ERRNO and as_owned_static =
                Tfib_owned_static of lib/Reusable/YF0m.v f82202ebccdf (owner: a Theorem Labs lane, the generator); YF0m
                Requires lib/Reusable/YF0l.v 4a405a3dba65 (as_code = Tfib_code), which Requires
                lib/Reusable/YImgCellsB.v f1cc7493a79d (IMG_TOP_B = 0x601000). TfibB's as_universe is
                lib/Reusable/YCej.v 71ae24321ba4's Tfib_universe, THE UNIV FORM OF RECORD (owner 02:29Z; it replaces
                8a099324acb0, the list form the f97c witness was built on): univ_of Tfib_fixed Tfib_wild.
     segments named FULLY QUALIFIED through BSEGS (the plain image's lib/Img0.v is also loaded here and answers to the
                short name `Img0.rsegs`); cnbx_segs_B checks them against PI_prog_B's pa_segs by reflexivity.
   THE FIELDS (the record's names, suffix _B): cnbi_base_B, cnbi_entry_B (B_entry_check_no_overread: sigma 0x819f0,
   slot 201 = CNB_SLOT), cnbi_own_B, cnbi_hi_B, cnbi_pst_rw_B, cnbi_pst_seg_B (a .bss byte IS a seg_rom byte: the
   generator materializes each PT_LOAD over its whole MemSiz), cnbi_pst_ok_B, cnbi_pst_errno_B.
   The image-free checkers are written here (the twins of lib/A/Prog/S1ImgA.v's pst_allb / in_img_b / in_ro_b), so
   that no A' image file is Required by name in this B' file.
   WHAT IS WITNESSED, at the real binding B := YD2l.TfibB, PI := prh_img_B, ci := lib/AU/CfImgB.v 519c583c9080
   CfImg_B, PA := PI_prog_B (every run ceiling):
     (1) THE IMAGE RECORD cnb_img, every field (cnb_img_inst): the eight image fields here; cnbi_relro_seg /
         cnbi_errno_relro / cnbi_relro_top / cnbi_ro_reads_nw by lib/AU/CfAroPresetB.v; cnbi_relro_eq by computation;
     (2) THE CLOSURE PREMISE of cnb_pre, prh_univ_closure B CTX0 (Cno102B_Base.v :235; the text PRH_FnCheck.v
         c40cf3fdcd2a :747), for the driver's context (cnb_sat_univ: the kit's lib/A/PRH_Witness.v 9479acc344ef
         prh_univ_closure_witness_B; its two image equations, as_code = YF0l.Tfib_code and as_universe =
         YCej.Tfib_universe, hold at TfibB by eq_refl);
     (3) THE ROOM PREMISE of cnb_pre, wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot S)
         (Cno102B_Base.v :249; the text :770), at the start state YG00.init_state (cnb_sat_wild: PRH_Witness.v
         prh_wild_room_witness_B, with prh_wk F_check_no_overread <= YCbqGwild.K_LLVMF by lib/A/WildBudget.v
         9134df4ca2c5 prh_wk_le_K: 6 <= 140);
     (4) THE CONTEXT PREMISE of cnb_pre, prh_ctx CTX0 F_check_no_overread x (Cno102B_Base.v :235; the text :747), at
         the context (2)'s proof uses, CTX0 = [[0x815c8]] (the driver's: RA_LLVMF 0x815c8), for x = [0x81818; 0x815c8]
         (cnb_sat_ctx). x is a context prh_reach derives: prh_reach_top [0x815c8], then prh_reach_call through THE
         CALL SITE LLVMFuzzerTestOneInput -> check_no_overread, `jal ra, check_no_overread` at B' 0x81814 with return
         site r = 0x81818 (PRH_ImgB.v pi_call_rets F_LLVMFuzzerTestOneInput F_check_no_overread = [0x81818], checked
         by the closed guarded vm_compute cnbx_cno_ret_B; the jal's target 0x81814 + 0x1dc = 0x819f0, read off the B'
         twin c90d4fa54d43160b's .text), and LLVMFuzzerTestOneInput is a frame-pointer function (pi_fp, cnbx_fp_top_B),
         so check_no_overread runs in r :: [0x815c8]; x is all of it (j = 2).
   WHAT IS NOT WITNESSED: the whole premise set cnb_pre CTX0 D at one record D. (2) has no state, (3) is at init_state,
   not at a check_no_overread entry state, and (4) is a context, not a register file and frame chain whose raZ regs ::
   spine ch is that context; no state is given at which every conjunct of cnb_pre holds at once, because fpre's ARcf
   at a grow position has no constructed witness (the internal file MIGRATION.md section 26f, owner a Theorem Labs lane).
   PRH_Witness.v is a kit file that Requires the A' records (PRH_Img, CfImgA, AF0l, ACej, WildRoomInstA) beside the B'
   ones; this file names no A' constant, and no statement here mentions PI_prog_A, A_prog_listing or prh_img_A.
   Numerals: 320 (LENGTH: the lbu offset of the hi/lo pair, the record's own), 4 (LENGTH: errno's word), 64 (WORD
   width), 2 (LENGTH: the context prefix j). ADDRESSES, in cnb_sat_ctx and its check cnbx_cno_ret_B only: 0x815c8
   (RA_LLVMF, the driver's context: the CTX0 literal of PRH_Witness.v's prh_univ_closure_witness_B) and 0x81818 (the
   return site of LLVMFuzzerTestOneInput's call to check_no_overread, checked against PRH_ImgB.v's pi_call_rets by
   the guarded vm_compute cnbx_cno_ret_B). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP08 YG0n YG0d YG0f YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YD2l YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Witness WildBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PRH_ImgB PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* THE B' SEGMENTS, FULLY QUALIFIED (lead 19:3xZ, CrcBp's wrong-image trap): this closure also loads the PLAIN image,
   whose lib/Img0.v answers to the short name `Img0.rsegs`; every lemma below names B''s segments through BSEGS, and
   cnbx_segs_B checks by reflexivity that they are the instance's pa_segs. *)
Local Notation BSEGS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs (only parsing).
Lemma cnbx_segs_B : forall rc : YM05.RunCeil, @pa_segs rc Listing_prog.B_prog_listing (@PI_prog_B rc) = BSEGS.
Proof. intros rc. reflexivity. Qed.

(* ---- image-free checkers and their soundness ---- *)
(* f holds at every byte of every range of P *)
Definition cnbx_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.

Lemma cnbx_allb_sound : forall f P a, cnbx_allb f P = true -> Exists (YG0n.in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold cnbx_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold YG0n.in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.

(* the byte a has a segment (rom) byte *)
Definition cnbx_rom_b (segs : list Segment) (a : Z) : bool :=
  match YK11.seg_rom segs (Z_to_bv 64 a) with Some _ => true | None => false end.

Lemma cnbx_rom_b_sound : forall segs a, cnbx_rom_b segs a = true -> YK11.seg_rom segs (Z_to_bv 64 a) <> None.
Proof. intros segs a H E. unfold cnbx_rom_b in H. rewrite E in H. discriminate H. Qed.

Definition cnbx_in_img_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs.

Lemma cnbx_in_img_b_sound : forall segs a, cnbx_in_img_b segs a = true -> YG0d.in_img segs a.
Proof.
intros segs a H. apply existsb_exists in H as (s & Hs & H). apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs | lia].
Qed.

Definition cnbx_in_ro_b (segs : list Segment) (rlo rhi a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs
  || ((rlo <=? a) && (a <? rhi)).

Lemma cnbx_in_ro_b_complete : forall segs rlo rhi a,
  PresetRodata.in_roP segs rlo rhi a -> cnbx_in_ro_b segs rlo rhi a = true.
Proof.
intros segs rlo rhi a [(s & Hs & Hw & Hr) | Hr]; unfold cnbx_in_ro_b; apply orb_true_intro; [left | right].
- apply existsb_exists. exists s. split; [exact Hs|]. rewrite Hw. cbn [negb andb].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
- apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* a lies in the range r *)
Definition cnbx_zr_b (a : Z) (r : Z * Z) : bool := (fst r <=? a) && (a <? fst r + snd r).

Lemma cnbx_not_in_zrs : forall a P, existsb (cnbx_zr_b a) P = false -> ~ Exists (YG0n.in_zr a) P.
Proof.
intros a P H HE. apply Exists_exists in HE as (r & Hr & Ha). unfold YG0n.in_zr in Ha.
assert (E : existsb (cnbx_zr_b a) P = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. unfold cnbx_zr_b.
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite H in E. discriminate E.
Qed.

(* ---- the closed checks at image B': each a guarded vm_compute on a closed goal ---- *)
Lemma cnbx_pst_rom : cnbx_allb (cnbx_rom_b BSEGS) (@prh_pst prh_img_B) = true.
Proof. lazymatch goal with |- cnbx_allb (cnbx_rom_b _) (@prh_pst prh_img_B) = true => vm_compute; reflexivity end. Qed.

Lemma cnbx_pst_ok :
  cnbx_allb (fun a => cnbx_in_img_b BSEGS a && negb (existsb (cnbx_zr_b a) YF0m.Tfib_owned_static))
    (@prh_pst prh_img_B) = true.
Proof.
lazymatch goal with
| |- cnbx_allb (fun a => cnbx_in_img_b _ a && negb (existsb (cnbx_zr_b a) YF0m.Tfib_owned_static))
    (@prh_pst prh_img_B) = true => vm_compute; reflexivity
end.
Qed.

Lemma cnbx_pst_ro :
  cnbx_allb (fun a => negb (cnbx_in_ro_b BSEGS B_prog_relro_lo B_prog_relro_hi a)) (@prh_pst prh_img_B) = true.
Proof.
lazymatch goal with
| |- cnbx_allb (fun a => negb (cnbx_in_ro_b _ B_prog_relro_lo B_prog_relro_hi a)) (@prh_pst prh_img_B) = true =>
  vm_compute; reflexivity
end.
Qed.

Lemma cnbx_pst_errno :
  cnbx_allb (fun a => negb ((YF0m.TFIB_ERRNO <=? a) && (a <? YF0m.TFIB_ERRNO + 4))) (@prh_pst prh_img_B) = true.
Proof.
lazymatch goal with
| |- cnbx_allb (fun a => negb ((YF0m.TFIB_ERRNO <=? a) && (a <? YF0m.TFIB_ERRNO + 4))) (@prh_pst prh_img_B) = true =>
  vm_compute; reflexivity
end.
Qed.

(* ---- THE FIELDS of cnb_img at image B' ---- *)
Lemma cnbi_base_B : B_prog_val A_TEXT = B_prog_base.
Proof. lazymatch goal with |- B_prog_val A_TEXT = B_prog_base => vm_compute; reflexivity end. Qed.

Lemma cnbi_entry_B : B_prog_sigma AS_check_no_overread = B_prog_val A_TEXT + CNB_OFF.
Proof.
lazymatch goal with |- B_prog_sigma AS_check_no_overread = B_prog_val A_TEXT + CNB_OFF => vm_compute; reflexivity end.
Qed.

Lemma cnbi_own_B : B_prog_val (A_OBJ 13) = @pi_g_own_ran_out prh_img_B.
Proof.
lazymatch goal with |- B_prog_val (A_OBJ 13) = @pi_g_own_ran_out prh_img_B => vm_compute; reflexivity end.
Qed.

Lemma cnbi_hi_B : B_prog_val (A_HI 9) + 320 = B_prog_val (A_OBJ 13).
Proof.
lazymatch goal with |- B_prog_val (A_HI 9) + 320 = B_prog_val (A_OBJ 13) => vm_compute; reflexivity end.
Qed.

Lemma cnbi_pst_rw_B : forall a, Exists (YG0n.in_zr a) (@prh_pst prh_img_B) ->
  ~ PresetRodata.in_roP BSEGS B_prog_relro_lo B_prog_relro_hi a.
Proof.
intros a Ha Hro. pose proof (cnbx_allb_sound _ _ a cnbx_pst_ro Ha) as H. cbv beta in H.
rewrite (cnbx_in_ro_b_complete _ _ _ _ Hro) in H. discriminate H.
Qed.

Lemma cnbi_pst_seg_B : forall a, Exists (YG0n.in_zr a) (@prh_pst prh_img_B) ->
  YK11.seg_rom BSEGS (Z_to_bv 64 a) <> None.
Proof. intros a Ha. apply cnbx_rom_b_sound. exact (cnbx_allb_sound _ _ a cnbx_pst_rom Ha). Qed.

Lemma cnbi_pst_ok_B : forall a, Exists (YG0n.in_zr a) (@prh_pst prh_img_B) ->
  YG0d.in_img BSEGS a /\ ~ Exists (YG0n.in_zr a) (as_owned_static YD2l.TfibB).
Proof.
intros a Ha. pose proof (cnbx_allb_sound _ _ a cnbx_pst_ok Ha) as H. cbv beta in H.
apply andb_prop in H as [H1 H2]. split; [exact (cnbx_in_img_b_sound _ _ H1)|].
apply cnbx_not_in_zrs. change (as_owned_static YD2l.TfibB) with YF0m.Tfib_owned_static.
apply negb_true_iff. exact H2.
Qed.

Lemma cnbi_pst_errno_B : forall a, Exists (YG0n.in_zr a) (@prh_pst prh_img_B) ->
  ~ (as_errno YD2l.TfibB <= a < as_errno YD2l.TfibB + 4).
Proof.
intros a Ha Hr. pose proof (cnbx_allb_sound _ _ a cnbx_pst_errno Ha) as H. cbv beta in H.
change (as_errno YD2l.TfibB) with YF0m.TFIB_ERRNO in Hr. destruct Hr as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. rewrite H1, H2 in H. discriminate H.
Qed.

(* ---- THE ASSEMBLY: the record at the instance PI_prog_B and the B' asyms TfibB, for every run ceiling ---- *)
Lemma cnb_img_inst : forall rc : YM05.RunCeil,
  cnb_img (rc := rc) (ci := CfImgB.CfImg_B) (PA := @PI_prog_B rc) YD2l.TfibB.
Proof.
intros rc. constructor.
- exact cnbi_base_B.
- exact cnbi_entry_B.
- exact cnbi_own_B.
- exact cnbi_hi_B.
- exact cnbi_pst_rw_B.
- exact cnbi_pst_seg_B.
- exact cnbi_pst_ok_B.
- exact cnbi_pst_errno_B.
- exact CfAroPresetB.relro_seg_preset_AU.
- exact (CfAroPresetB.errno_relro_preset_AU YD2l.TfibB YD2l.TfibB_syms).
- exact CfAroPresetB.relro_top_preset_AU.
- split; vm_compute; reflexivity.
- exact CfAroPresetB.ro_reads_nw_preset_AU.
Qed.

(* ---- THE SATISFIABILITY WITNESSES of three premises of cnb_pre at the real binding B := YD2l.TfibB (the header's
   (2), (3) and (4)); each premise ALONE, not the whole premise set at one state ---- *)
(* the closure premise (Cno102B_Base.v :235; the text :747) for the driver's context *)
Lemma cnb_sat_univ : exists CTX0, @prh_univ_closure prh_img_B YD2l.TfibB CfImgB.CfImg_B CTX0.
Proof. eexists. exact (PRH_Witness.prh_univ_closure_witness_B YD2l.TfibB eq_refl eq_refl). Qed.
(* the room premise (Cno102B_Base.v :249; the text :770) at the start state's depot *)
Lemma cnb_sat_wild :
  YCbqGwild.wild_room (as_universe YD2l.TfibB) [] (prh_wk F_check_no_overread) (st_depot init_state).
Proof.
exact (PRH_Witness.prh_wild_room_witness_B YD2l.TfibB F_check_no_overread eq_refl
  (WildBudget.prh_wk_le_K F_check_no_overread)).
Qed.
(* the context premise (Cno102B_Base.v :235; the text :747) at the driver's context [[0x815c8]], through the call site
   LLVMFuzzerTestOneInput -> check_no_overread (return site 0x81818): the header's (4) *)
Lemma cnbx_cno_ret_B : In 0x81818 (@pi_call_rets prh_img_B F_LLVMFuzzerTestOneInput F_check_no_overread).
Proof.
lazymatch goal with
| |- In 0x81818 (@pi_call_rets prh_img_B F_LLVMFuzzerTestOneInput F_check_no_overread) => vm_compute; left; reflexivity
end.
Qed.
Lemma cnbx_fp_top_B : @pi_fp prh_img_B F_LLVMFuzzerTestOneInput = true.
Proof. lazymatch goal with |- @pi_fp prh_img_B F_LLVMFuzzerTestOneInput = true => vm_compute; reflexivity end. Qed.
Lemma cnb_sat_ctx : exists x, @prh_ctx prh_img_B [[0x815c8]] F_check_no_overread x.
Proof.
pose proof (@prh_reach_call prh_img_B [[0x815c8]] F_LLVMFuzzerTestOneInput F_check_no_overread [0x815c8] 0x81818
  (@prh_reach_top prh_img_B [[0x815c8]] [0x815c8] (or_introl eq_refl)) cnbx_cno_ret_B) as HR.
rewrite cnbx_fp_top_B in HR. cbv iota in HR.
exists [0x81818; 0x815c8], [0x81818; 0x815c8], 2%nat. split; [exact HR | reflexivity].
Qed.

(* the audit: every lemma closed (the standard axioms only) *)
Print Assumptions cnbi_base_B.
Print Assumptions cnbi_entry_B.
Print Assumptions cnbi_own_B.
Print Assumptions cnbi_hi_B.
Print Assumptions cnbi_pst_rw_B.
Print Assumptions cnbi_pst_seg_B.
Print Assumptions cnbi_pst_ok_B.
Print Assumptions cnbi_pst_errno_B.
Print Assumptions cnb_img_inst.
Print Assumptions cnb_sat_univ.
Print Assumptions cnb_sat_wild.
Print Assumptions cnb_sat_ctx.
Check @cnb_img_inst.
Check @cnb_sat_univ.
Check @cnb_sat_wild.
Check @cnb_sat_ctx.
