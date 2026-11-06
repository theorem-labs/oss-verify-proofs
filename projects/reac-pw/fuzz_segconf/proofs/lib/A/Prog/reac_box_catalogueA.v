(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths, module names and numbers changed; 313 of its 427 lines of code are new or changed and 255 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan (image A, entry 0x8a100,
   72 bytes, 18 instructions, a 16-byte frame, no side-stack frame): reac_box_catalogue_contract of
   lib/A/Prog/reac_box_catalogue_c.v at image A's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at
   the entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}`).
   Ported from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v at origin/ossv/recipes 501c0d516c69, the
   same 18 instructions: its entry seed (cat_entry: the count cell, the frame, the shadow base's GOT word and cell as
   regions, one shadow entry for the 8-byte cell) and its one token run to the ret, restated from identity's
   caller-journal statement (its IdentCJ.v) in the afn_pre / apost_base form with the cell in the footprint; the
   object the code returns is listing object 77, fuzz_catalogue, where identity's is BOX_CATALOGUE. The c = 0 run is
   new (the logic of libreac/fuzz_ctrl's lib/A/Prog/reac_box_catalogue.v:24-37 at 09c6822d886): a0 is pinned to 0, so
   the beqz at 0x8a108 is taken and the run goes through 0x8a130 to the ret without the store.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a120, and a compare, bnez 0x8a124) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a144) is not reached; the sd at 0x8a12c writes 11 as 8 bytes. In both
   arms a0 = fuzz_catalogue (auipc/addi 0x8a130). The shadow base is the word the GOT cell as_got_shadow B (image A
   0xa2a50, listing object 0) holds: the walk takes it from PALib (pal_got_shadow, pal_cell), a listing fact, not a
   contract premise.
   Image A's numbers of the statement: the entry BASE + AF_reac_box_catalogue (the image-A owner's 16:54Z ruling), cat =
   SegInstA.catA, STK = SegInstA.STK_reac_box_catalogue (16, the frame; lib/A/Prog/SegInstA.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_box_catalogue_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* STK = SegInstA.STK_reac_box_catalogue (16: 0x8a100 addi sp,sp,-16, released at 0x8a13c; the jal at 0x8a144 is
   the dead error arm) *)
#[local] Notation STK := SegInstA.STK_reac_box_catalogue.
(* cat = SegInstA.catA (fuzz_catalogue, 0xa18e0) is listing object 77 (SegAddr.v seg_objs; the auipc/addi at 0x8a130
   is SegList.v `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0`) *)
Definition RBC_CAT_OBJ : nat := 77.

(* 11 as 8 bytes of the restricted memory, read through the ASan reader *)
Lemma rbc_sa_val11 : forall segs H mem a,
val_mem segs (mrestrict H mem) a 8 11 -> sa_val (aview segs H mem) a 8 11.
Proof.
intros segs H mem a Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map].
f_equal. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma rbc_set_fs_id : forall S, S = set_fs (st_fs S) S.
Proof. intros S. destruct S. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the shadow base: atom 32 *)
Definition RbcBx : sv := SOff 32 0.
(* c <> 0: the count cell (atom 10, 8 bytes, written), the 16-byte frame, the shadow base's GOT word and cell *)
Definition rbc_regions : smem :=
[ YP09.mkRegion (Some 10%nat) 0 8 0 8 []; stack_region 16; got_regionP; bcell_regionP 32 ].
Definition rbc_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 8) 3); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_rbc : sstate := mkSS AF_reac_box_catalogue sr_atoms rbc_regions None rbc_facts.
Definition rbc_SH : list shent := [ mkSHE 10 0 8 ].
(* c = 0: the frame only, and a0 pinned to 0 *)
Definition rbc_regions0 : smem := [ stack_region 16 ].
Definition rbc_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Definition ss_rbc0' : sstate := mkSS AF_reac_box_catalogue sr_atoms rbc_regions0 None rbc_facts0.
Definition ss_rbc0 : sstate :=
mkSS AF_reac_box_catalogue (sr_set sr_atoms (10%bv : bv 5) (SLit 0)) rbc_regions0 None rbc_facts0.
Definition rbc_extra : list word := [Z_to_bv 64 SB].
Definition EC (regs : bvmap 5 word) : env := Eimg (Ereg regs rbc_extra).
Section e.
Variable B : asyms.
(* the record hypotheses: PALib (SegPaLib.v; SegRecRest.v seg_palib gives it at PB_seg) and the listing's objects
   against the image's addresses (SegObj.v; SegRecRest.v seg_val_objs_PB) *)
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Lemma rbc_val_cat : VAL (A_OBJ RBC_CAT_OBJ) = SegInstA.catA.
Proof. rewrite (VOBJS RBC_CAT_OBJ ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* where the count cell lies, from sa_dst: off the image and the shadow band, present, and a byte the journal
   lets the call write (awr_byte: a heap block's, a caller side-stack frame's, or the caller's real stack's, in
   the footprint) *)
Lemma rbc_c_where : forall ly S W regs mem md ch c,
afn_pre SEGS B STK ly S W regs mem md ch -> sa_dst SEGS B ly S W mem regs c 8 ->
4096 <= c /\ c + 8 <= 2 ^ 47 /\ (c + 8 <= 0x10000 \/ kImgEnd <= c) /\
(c + 8 <= kLowShadowBeg \/ kHighMemBeg <= c) /\ (c + 8 <= alloc_ceiling \/ spZ regs <= c) /\
(forall a, c <= a < c + 8 -> apresent (w_H W) mem a) /\
(forall a, c <= a < c + 8 ->
 awr_byte SEGS B STK (spZ regs) [(c, c + 8)] (ablocks B ly S) (ablocks B ly S) (frames S) ly [] a).
Proof.
intros ly S W regs mem md ch c HPRE HD.
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : STK = 16) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFP : forall a, c <= a < c + 8 -> inFP [(c, c + 8)] a)
  by (intros a Ha; exists (c, c + 8); split; [left; reflexivity | cbn [fst snd]; lia]).
unfold awr_byte, awr_prog_or_caller. unfold kImgEnd.
destruct HD as [((cid & pos & Hin & Hcid & Hlo & Hhi) & _) | [((b & m & Hin & Hlo & Hhi) & _) | (Hs1 & Hs2 & Hp & _)]].
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
  pose proof (frm_off_imgP B ly S W mem md cid pos HAR Hin) as Himg.
  destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Hfp & _).
  unfold in_app in Hfa. unfold off_img in Himg.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; exact (proj1 (Hfp a ltac:(lia)))|].
  intros a Ha. right; right; right; right; right; right. split; [exact (HFP a Ha)|].
  exists cid, pos. split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hm).
  pose proof (blk_off_imgP B ly S W mem md b m HAR Hin) as Himg.
  pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
  unfold in_app in Hbapp. unfold off_img in Himg.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; exact (proj1 (Hbpres a ltac:(lia)))|].
  intros a Ha. right; left. split; [exact (HFP a Ha)|]. exists b, m. split; [exact Hin | lia].
- split; [lia|]. split; [lia|]. split; [right; lia|]. split; [right; lia|]. split; [right; lia|].
  split; [intros a Ha; replace a with (c + (a - c)) by lia; apply Hp; lia|].
  intros a Ha. right; right; right; right; right; left. split; [exact (HFP a Ha) | lia].
Qed.

(* the entry state, c <> 0 (identity's cat_entry) *)
Lemma rbc_entry : forall ly S W regs mem md ch c,
afn_pre SEGS B STK ly S W regs mem md ch ->
getr regs 10 = w64 c -> c mod 8 = 0 -> sa_addr (rdW W mem) c 8 -> sa_dst SEGS B ly S W mem regs c 8 ->
st_ok_pi SEGS VAL (EC regs) ss_rbc
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_catalogue)) mem (seg_rom SEGS)))
/\ sh_ok SEGS RbcBx rbc_SH (EC regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch c HPRE H10 Hc8 HADDR HDST.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HSTK : STK = 16) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbc_c_where ly S W regs mem md ch c HPRE HDST)
  as (Hc4096 & Hc47 & Hcimg & Hcband & Hcceil & Hcpres & _).
destruct HADDR as (_ & _ & _ & HRA & _).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold kImgEnd in *.
rewrite restrict_mkst_fx.
set (E := EC regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs rbc_extra) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E0o : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (UBx : U E RbcBx = SHADOW_OFF).
{ unfold RbcBx. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
  rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
assert (U10 : U E (SOff 10 0) = c).
{ rewrite U_SOff, E10, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
split.
- unfold ss_rbc. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rbc_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Uc. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hcpres. lia.
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * cbn [base_val]. rewrite E0o, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * cbn [base_val]. rewrite E12, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 RbcBx SB);
      [cbn [sv_denot RbcBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold rbc_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite Uc, Usp, E0o, E12, !unsigned_lit_small
      by (pose proof (pa_val_range (A_OBJ 0)); pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rbc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uc, USB.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
- unfold sh_ok, rbc_SH. constructor; [|constructor].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite UBx, U10. rewrite <- (aview_rd_of SEGS).
  split.
  + replace (8 - 0) with 8 by lia. rewrite Z.add_0_r. exact HRA.
  + intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.add_0_r in Ha.
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* the entry state, c = 0: the frame, and a0 pinned to the literal 0 *)
Lemma rbc_entry0 : forall ly S W regs mem md ch,
afn_pre SEGS B STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
st_ok_pi SEGS VAL (EC regs) ss_rbc0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_catalogue)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE H10.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HSTK : STK = 16) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := EC regs).
assert (E2 : ew E 2 = getr regs 2)
by (subst E; unfold EC; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HS0 : st_ok_pi SEGS VAL E ss_rbc0'
  (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_catalogue)) (mrestrict (w_H W) mem) (seg_rom SEGS))).
{ unfold ss_rbc0'. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rbc_regions0, stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + apply pairwise_disjoint_of_extents. cbn. tauto.
  + split; [|split; [exact I | exact I]].
    cbn [rbc_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
exact (st_ok_pi_pin_reg' E ss_rbc0' _ (10%bv : bv 5) 0 HS0 H10 eq_refl).
Qed.

(* c <> 0: one token run from the entry to the ret, through the check and the store *)
Lemma rbc_walk1 : forall ly S W (regs : bvmap 5 word) mem md ch c,
afn_pre SEGS B STK ly S W regs mem md ch ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> c <> 0 ->
c mod 8 = 0 -> sa_addr (rdW W mem) c 8 -> sa_dst SEGS B ly S W mem regs c 8 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_catalogue) regs mem md)
(apost_base SEGS B STK [(c, c + 8)] regs ly S W mem md EV_reac_box_catalogue
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 SegInstA.catA /\
 (c <> 0 -> sa_val (aview SEGS (w_H W') mem') c 8%nat 11) /\
 sa_kept SEGS W mem W' mem' regs STK (fun a => c <> 0 /\ c <= a < c + 8) /\
 sa_noalloc B ly S ly' S')).
Proof.
intros ly S W regs mem md ch c HPRE H10 Hc64 Ec Hc8 HADDR HDST.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : STK = 16) by reflexivity.
destruct (rbc_c_where ly S W regs mem md ch c HPRE HDST)
  as (Hc4096 & Hc47 & Hcimg & Hcband & Hcceil & Hcpres & Hcwr).
destruct (rbc_entry ly S W regs mem md ch c HPRE H10 Hc8 HADDR HDST) as [HS SHOK].
pose proof (ajournal_init SEGS B STK [(c, c + 8)] ly S W regs mem md ch HPRE) as HJ.
pose proof rbc_val_cat as VCAT.
remember (EC regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs rbc_extra) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (ECAT : ew E (A_OBJ RBC_CAT_OBJ) = Z_to_bv 64 SegInstA.catA)
by (rewrite <- VCAT; exact (img_env_atomP E (A_OBJ RBC_CAT_OBJ) HEI ltac:(unfold A_OBJ, RBC_CAT_OBJ, A_TEXT, A_LIM; lia))).
assert (HAE : env_agree 32 (Ereg regs rbc_extra) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_box_catalogue)) with (Z_to_bv 64 (BASE + AF_reac_box_catalogue)).
paj_run_tok RUN HS HJ SHOK Bspan;
[ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 10%nat c);
  [ reflexivity | exact Uc | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply Hcwr; lia |];
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0);
  [ reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  apply awr_ok_nil
| ].
(* the cell holds 11 *)
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
  assert (VpR : val_mem SEGS (mrestrict (w_H W) (ms_mem msc)) (c + 0) (N.to_nat 8) 11);
  [ pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msc) 0%nat _ HS eq_refl) as HR0;
    cbn [restrict ms_mem] in HR0;
    eapply (field_of_region E _ 10%nat c _ _ _ _ _ 0 8%N _ 11 HR0);
    [ exact Uc
    | cbn; first [ left; reflexivity | right; left; reflexivity ]
    | first [ reflexivity | cbn [sv_denot]; reflexivity ]
    | zside
    | zside ]
  | ]
end.
rewrite Z.add_0_r in VpR. change (N.to_nat 8) with 8%nat in VpR.
(* every byte outside the cell and the frame is kept *)
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc),
  HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc2)) |- _ =>
  assert (HKEEP : forall a, 0 <= a < 2 ^ 64 ->
    ~ (c <= a < c + 8) -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) mem a);
  [ intros a Ha HnP HnS;
    refine (kept_of_frame Ex rs (w_H W) m0 (ms_mem msc)
      (fun x => (c <= x < c + 8) \/ (spZ regs - 16 <= x < spZ regs)) HFr _ a Ha _);
    [ intros bb wlo whi x Hin Hr;
      cbn [windows map ss_mem ss_rbc rbc_regions stack_region got_regionP bcell_regionP
           YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
      destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-;
      cbn [base_val] in Hr;
      first [ rewrite Uc in Hr; left; lia
            | rewrite Usp in Hr; right; lia
            | exfalso; lia ]
    | intros [Hq | Hq]; [exact (HnP Hq) | exact (HnS Hq)] ]
  | ]
end.
(* the ret *)
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat'; unfold apost_base;
  exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs rbc_extra HS); [exact HAE | vm_compute; reflexivity]|];
  split; [cbn [ms_regs]; rewrite R10; first [exact ECAT | reflexivity]|];
  split; [intros _; apply rbc_sa_val11; exact VpR|];
  split;
  [ intros a Ha HnS HnE; apply HKEEP;
    [ exact Ha | intros Hq; apply HnE; exact (conj Ec Hq) | intros Hq; apply HnS; lia ] |];
  split; [apply Permutation_refl|]; split; [reflexivity|]; exists (st_fs S); apply rbc_set_fs_id
end.
Qed.

(* c = 0: one token run from the entry to the ret, the beqz taken *)
Lemma rbc_walk0 : forall ly S W (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B STK ly S W regs mem md ch -> getr regs 10 = w64 0 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_catalogue) regs mem md)
(apost_base SEGS B STK [] regs ly S W mem md EV_reac_box_catalogue
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 SegInstA.catA /\
 (0 <> 0 -> sa_val (aview SEGS (w_H W') mem') 0 8%nat 11) /\
 sa_kept SEGS W mem W' mem' regs STK (fun a => 0 <> 0 /\ 0 <= a < 0 + 8) /\
 sa_noalloc B ly S ly' S')).
Proof.
intros ly S W regs mem md ch HPRE H10.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HSTK : STK = 16) by reflexivity.
pose proof (rbc_entry0 ly S W regs mem md ch HPRE H10) as HS.
assert (SHOK : sh_ok SEGS RbcBx [] (EC regs) (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
pose proof (ajournal_init SEGS B STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof rbc_val_cat as VCAT.
remember (EC regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs rbc_extra) n)
by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (ECAT : ew E (A_OBJ RBC_CAT_OBJ) = Z_to_bv 64 SegInstA.catA)
by (rewrite <- VCAT; exact (img_env_atomP E (A_OBJ RBC_CAT_OBJ) HEI ltac:(unfold A_OBJ, RBC_CAT_OBJ, A_TEXT, A_LIM; lia))).
assert (HAE : env_agree 32 (Ereg regs rbc_extra) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_box_catalogue)) with (Z_to_bv 64 (BASE + AF_reac_box_catalogue)).
paj_run_tok RUN HS HJ SHOK Bspan;
[ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat 0);
  [ reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |];
  apply awr_ok_nil
| ].
(* every byte outside the frame is kept *)
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc),
  HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc2)) |- _ =>
  assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) mem a);
  [ intros a Ha HnS;
    refine (kept_of_frame Ex rs (w_H W) m0 (ms_mem msc)
      (fun x => spZ regs - 16 <= x < spZ regs) HFr _ a Ha HnS);
    intros bb wlo whi x Hin Hr;
    cbn [windows map ss_mem ss_rbc0 rbc_regions0 stack_region YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
    destruct Hin as [Hq | []]; injection Hq as <- <- <-;
    cbn [base_val] in Hr; rewrite Usp in Hr; lia
  | ]
end.
(* the ret *)
lazymatch goal with
| HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat'; unfold apost_base;
  exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1, E1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs rbc_extra HS); [exact HAE | vm_compute; reflexivity]|];
  split; [cbn [ms_regs]; rewrite R10; first [exact ECAT | reflexivity]|];
  split; [intros H00; exfalso; exact (H00 eq_refl)|];
  split; [intros a Ha HnS _; apply HKEEP; [exact Ha | intros Hq; apply HnS; lia] |];
  split; [apply Permutation_refl|]; split; [reflexivity|]; exists (st_fs S); apply rbc_set_fs_id
end.
Qed.

Theorem reac_box_catalogue_walk :
reac_box_catalogue_contract SEGS B (BASE + AF_reac_box_catalogue) SegInstA.STK_reac_box_catalogue SegInstA.catA.
Proof.
unfold reac_box_catalogue_contract.
intros ly S W regs mem md ch c HPRE H10 Hc64 HC HEV.
destruct (Z.eq_dec c 0) as [Ec | Ec].
- subst c. exact (rbc_walk0 ly S W regs mem md ch HPRE H10).
- destruct HC as [Ec0 | (Hc8 & HADDR & HDST)]; [contradiction|].
  rewrite (proj2 (Z.eqb_neq c 0) Ec).
  exact (rbc_walk1 ly S W regs mem md ch c HPRE H10 Hc64 Ec Hc8 HADDR HDST).
Qed.
(* inside the Sections: the walk's hypotheses as its assumptions *)
About reac_box_catalogue_walk.
Print Assumptions reac_box_catalogue_walk.
End e.
End f.
End d.
About reac_box_catalogue_walk.
Print Assumptions reac_box_catalogue_walk.
