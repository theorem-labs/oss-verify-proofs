(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reply_code.v, with its module paths and module names changed; 481 of its 543 lines of code are new or changed and 226 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_role_file.v; 476 of its 585 lines of code are new or changed and 434 lines of the source are left out. *)
(* The ASan walk of reac_segconf_ignore_file (reac-pw/fuzz_segconf image A, BASE + AF_reac_segconf_ignore_file =
   0x89750, 38 instructions), in the form of plugin-hostd/fuzz_command's released lib/A/Prog/check_refusal.v and
   check_refusal_s1.v (origin/ossv/recipes 501c0d516c69): one symbolic run over the listing (SegPaLib's paj_run /
   paj_branch / paj_ret_at), the call of reac_segconf_find through PaCall's cl_callS with that function's
   contract as a Section hypothesis, and after the call the record of the entry it returned, added to the
   symbolic state with st_ok_pi_add_region so the two instrumented checks pass and their error paths
   (errpath_load4 at 0x897d8, errpath_load1 at 0x897e4) are not reached.

   Proves reac_segconf_ignore_file_contract (lib/A/Prog/reac_segconf_ignore_file_c.v) at this image's numbers. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YO0b YO0c YG0q YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase SegObj SegAddr SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
reac_segconf_find_c reac_segconf_ignore_file_c reac_segconf_ignore_file_lem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the shadow base the start-up leaves in the cell the GOT word of object 0 points at *)
Definition IGF_SB : Z := 0x7fff8000.
Definition IGFx : sv := SOff 32 0.
Definition IGFspan : Z * Z := (IGF_SB, IGF_SB + 2 ^ 44 - 1).
(* the return address of the call of reac_segconf_find: 0x8976c *)
Definition IGF_RET : Z := AF_reac_segconf_ignore_file + 0x1c.
(* the value of the two fields the function loads, as functions of the model: 0 when find answers None, where
   the code never reads them *)
Definition igf_set (rcs : rconf) (nm : list Z) : Z :=
match r_find rcs nm with Some i => seg_spec.b2z (rs_ignore_set (r_seg rcs i)) | None => 0 end.
Definition igf_b0 (rcs : rconf) (nm : list Z) : Z :=
match r_find rcs nm with Some i => hd0 (rs_ignore_file (r_seg rcs i)) | None => 0 end.
(* atoms: 32 the shadow base, 33 the ignore_set word, 34 the first ignore_file byte; 44 (a register the call
   clobbers) is the entry find returns *)
Definition igf_regions : smem := [stack_region 16; got_regionP; bcell_regionP 32].
Definition igf_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF IGF_SB IGF_SB 0);
         (33%nat, mkAF 0 1 0); (34%nat, mkAF 0 255 0)] [] [].
Definition igf_ss : sstate := mkSS AF_reac_segconf_ignore_file sr_atoms igf_regions None igf_facts.
Definition igf_extra (rcs : rconf) (nm : list Z) : list word :=
map (Z_to_bv 64) [IGF_SB; igf_set rcs nm; igf_b0 rcs nm].
(* the entry find returned, with the two fields the checks guard *)
Definition igf_seg_region (fl b0 : sv) : YP09.region :=
YP09.mkRegion (Some 44%nat) 0 356 0 0 [YP09.mkChunk 28 (CVal 4 fl); YP09.mkChunk 256 (CVal 1 b0)].
Definition igf_SH : list shent := [mkSHE 44%nat 0 356].

Lemma igf_le_byte1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.

(* `seqz a1,a1; addi a1,a1,-1; and a0,a1,a0` at 0x897a4-0x897ac with a nonzero byte: the mask is all ones, so
   a0 keeps the address the addi at 0x8978c formed *)
Lemma igf_mask : forall v z, 1 <= v <= 255 -> 0 <= z < 2 ^ 64 ->
alu64 ALU_AND (alu64 ALU_ADD (alu64 ALU_SLTU (Z_to_bv 64 v) (Z_to_bv 64 1)) (Z_to_bv 64 (-1)))
      (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros v z Hv Hz.
assert (S1 : alu64 ALU_SLTU (Z_to_bv 64 v) (Z_to_bv 64 1) = Z_to_bv 64 0).
{ cbn [alu64 alu]. replace (bv_ltu (Z_to_bv 64 v) (Z_to_bv 64 1)) with false; [reflexivity|].
  symmetry. unfold bv_ltu. apply Z.ltb_ge. rewrite !unsigned_lit_small by lia. lia. }
rewrite S1, (zalu64_sound ALU_ADD 0 (-1)).
replace (zalu64 ALU_ADD 0 (-1)) with (2 ^ 64 - 1) by (vm_compute; reflexivity).
rewrite (zalu64_sound ALU_AND (2 ^ 64 - 1) z). f_equal.
unfold zalu64, zcanon, M64. cbn [zalu_raw].
try change (bv_modulus 64) with (2 ^ 64).
assert (H1 : (2 ^ 64 - 1) mod 2 ^ 64 = 2 ^ 64 - 1) by (vm_compute; reflexivity).
assert (H2 : z mod 2 ^ 64 = z) by (apply Z.mod_small; lia).
rewrite H1, H2.
assert (H3 : Z.land (2 ^ 64 - 1) z = z).
{ replace (2 ^ 64 - 1) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. }
rewrite H3. exact H2.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition igf_E (regs : bvmap 5 word) (rcs : rconf) (nm : list Z) : env :=
Eimg (Ereg regs (igf_extra rcs nm)).
Section e.
Variable B : asyms.
#[local] Notation RLO := RLO_A.
#[local] Notation RHI := RHI_A.
(* the callee's contract, at every FP state (statement pass 4); the walk proves no callee *)
Hypothesis FIND : forall fx0 : YK11.FPState,
@reac_segconf_find_contract fx0 rc SK SEGS B (BASE + AF_reac_segconf_find) STK_reac_segconf_find RLO RHI.
(* the per-binary facts: the listing's objects 0 and 12 are the record's GOT word and shadow-base cell, and the
   listing's call targets are the program's own entries *)
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* every read-only byte of this image lies below the allocator's ceiling, so the frame writes keep it *)
Lemma igf_ro_low : forall a, in_roP SEGS RLO RHI a -> 0 <= a < alloc_ceiling.
Proof.
intros a Hro. pose proof (@asan_consts rc) as (AC & _ & _ & _ & KLOW).
destruct Hro as [(s & Hs & _ & Hr) | Hr].
- assert (Himg : in_img SEGS a) by (exists s; split; [exact Hs | exact Hr]).
  pose proof (pa_segs_low a Himg). lia.
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. lia.
Qed.

Lemma igf_val_obj : forall i, (i < 13)%nat -> 0x10000 <= VAL (A_OBJ i) /\ VAL (A_OBJ i) + 8 <= kImgEnd.
Proof. intros i Hi. exact (pa_obj_img i Hi). Qed.

(* the entry state: the frame window, the GOT word of the shadow-base cell and the cell itself *)
Lemma igf_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md rcs nm,
AR SEGS B ly S W mem md ->
astk_ok STK_reac_segconf_ignore_file ly (spZ regs) ->
(forall a, spZ regs - STK_reac_segconf_ignore_file <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= igf_set rcs nm <= 1 -> 0 <= igf_b0 rcs nm <= 255 ->
st_ok_pi SEGS VAL (igf_E regs rcs nm) igf_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_ignore_file)) mem (seg_rom SEGS))).
Proof.
intros W regs mem ly S md rcs nm HAR Hstk Hpres Hset Hb0.
assert (WS : STK_reac_segconf_ignore_file = 8240) by reflexivity. rewrite WS in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (@asan_consts rc) as (AC & _).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
set (E := igf_E regs rcs nm).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold igf_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (igf_extra rcs nm)) n)
  by (intros n Hn; subst E; unfold igf_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 IGF_SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (igf_set rcs nm))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (igf_b0 rcs nm))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))).
{ pose proof (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as H.
  apply bv_eq. rewrite H. rewrite unsigned_lit_small; [reflexivity | apply pa_val_range]. }
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))).
{ pose proof (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as H.
  apply bv_eq. rewrite H. rewrite unsigned_lit_small; [reflexivity | apply pa_val_range]. }
destruct (igf_val_obj 0 ltac:(lia)) as [R0a R0b].
destruct (igf_val_obj 12 ltac:(lia)) as [R12a R12b].
pose proof (pal_got_cell B TL) as HGC.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (KIMG : kImgEnd = 0x601000) by reflexivity.
unfold igf_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold igf_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold igf_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) IGF_SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold IGF_SB; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold igf_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil Hstk0 R0a R0b R12a R12b HGC KIMG AC. clear. intros.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [igf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold IGF_SB; lia).
  unfold IGF_SB. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16.
  revert Hslo Hshi H47 Hceil Hal16 Hstk0 Hset Hb0 AC. clear. intros.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* ===================================== the walk ===================================== *)
Theorem reac_segconf_ignore_file_walk :
reac_segconf_ignore_file_contract SEGS B (BASE + AF_reac_segconf_ignore_file) STK_reac_segconf_ignore_file RLO RHI.
Proof.
unfold reac_segconf_ignore_file_contract.
intros ly S W regs mem md ch c name rcs nm HPRE HROD H10 Rc H11 Rname HQP HEV.
pose proof pa_wx as Hwx. pose proof (pa_segs_low (L := seg_listing)) as Hsegs.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_seg)) as HBLO.
pose proof (@asan_consts rc) as (AC & _ & _ & _ & KLOW).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof HQP as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
assert (WS : STK_reac_segconf_ignore_file = 8240) by reflexivity.
assert (WS1 : STK_reac_segconf_find = 8224) by reflexivity.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
(* the block that holds the reader's state *)
destruct Q4 as (blk & bn & Hblk & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS ly S W mem md blk bn HAR Hblk) as (_ & Hblk4096 & Hblkc & Hblkapp & _ & _ & Hbn).
pose proof (req_size_pos bn ltac:(lia)) as [_ Hreq].
unfold seg_spec.SEG_C_SIZE in Hb2.
(* the two field values are in range *)
assert (Hset : 0 <= igf_set rcs nm <= 1).
{ unfold igf_set. destruct (r_find rcs nm) as [i|];
  [destruct (rs_ignore_set (r_seg rcs i)); cbn [seg_spec.b2z]|]; lia. }
assert (Hb0 : 0 <= igf_b0 rcs nm <= 255).
{ unfold igf_b0. destruct (r_find rcs nm) as [i|] eqn:RF; [|lia].
  destruct (igf_find_lt (aview SEGS (w_H W) mem) c rcs nm i Q3 RF) as [Hi _].
  pose proof (igf_file0_range (aview SEGS (w_H W) mem) c rcs i Q3 Hi). lia. }
pose proof (igf_entry W regs mem ly S md rcs nm HAR Hstk Hpres Hset Hb0) as HS.
pose proof (ajournal_init SEGS B STK_reac_segconf_ignore_file ([] : list (Z * Z)) ly S W regs mem md ch HPRE) as HJ.
set (E := igf_E regs rcs nm) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, igf_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (igf_extra rcs nm)) n)
  by (intros n Hn; unfold E, igf_E; apply Eimg_low; exact Hn).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (apply EEo; reflexivity).
assert (E11 : ew E 11 = getr regs 11) by (apply EEo; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 IGF_SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (igf_set rcs nm))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (igf_b0 rcs nm))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (igf_extra rcs nm)) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
assert (SHOK0 : sh_ok SEGS IGFx ([] : list shent) E (mrestrict (w_H W) mem)) by (apply Forall_nil).
unfold cfg_at, w64.
(* 0x89750 .. 0x89768: the frame, the shadow base through the GOT word of object 0, then the call *)
paj_run_tok RUN HS HJ SHOK0 IGFspan.
{ awr_ok_tac. exact Usp. }
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
      (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq0 | Hin];
              [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]) end.
assert (KEEPL : igf_lowkept (aview SEGS (w_H W) mem) (aview SEGS (w_H W) (ms_mem ms)))
  by (intros a Ha; apply KEEP0; lia).
clear HF HFr HG. rename ms into ms1.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
prreg HS (11%bv : bv 5) P11.
assert (HspT : spZ (ms_regs ms1) = spZ regs + -16).
{ unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (P3' : getr (ms_regs ms1) 3 = Z_to_bv 64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
assert (P4' : getr (ms_regs ms1) 4 = Z_to_bv 64 (as_tp B)) by (rewrite P4, E4; exact Htp).
assert (P10' : getr (ms_regs ms1) 10 = Z_to_bv 64 c) by (rewrite P10, E10; exact H10).
assert (P11' : getr (ms_regs ms1) 11 = Z_to_bv 64 name) by (rewrite P11, E11; exact H11).
assert (P8' : getr (ms_regs ms1) 8 = Z_to_bv 64 IGF_SB) by (rewrite P8, E32; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms1) 1))
  by (rewrite P1; apply ret_ok_codeptr_v; [cbv [IGF_RET AF_reac_segconf_ignore_file]; lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms1) 1)).
{ rewrite P1, unsigned_lit_small by (cbv [IGF_RET AF_reac_segconf_ignore_file] in *; lia).
  cbv [IGF_RET AF_reac_segconf_ignore_file]. lia. }
assert (HROD1 : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) (ms_mem ms1)))
  by (exact (igf_arodata_kept SEGS B RLO RHI _ _ igf_ro_low KEEPL HROD)).
assert (HQP1 : query_pre SEGS B ly S (aview SEGS (w_H W) (ms_mem ms1)) c name rcs nm)
  by (exact (igf_query_pre_kept SEGS B ly S W mem md _ _ c name rcs nm LAWS Hsegs HAR KEEPL HQP)).
(* the call of reac_segconf_find at 0x89768 *)
rewrite (SIGP SS_reac_segconf_find
  ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_find) with AF_reac_segconf_find by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS B LAWS W (ms_regs ms1) (ms_mem ms1) _ STK_reac_segconf_ignore_file (spZ regs) [] ly S W mem md []
    ly S _ 0 STK_reac_segconf_find [] 0 (-16) (getr (ms_regs ms1) 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       getr regs2 10 = Z_to_bv 64 (seg_spec.find_ptr c rcs nm) /\
       sa_kept SEGS W (ms_mem ms1) W2 mem2 (ms_regs ms1) STK_reac_segconf_find (fun _ => False) /\
       sa_noalloc B ly S ly2 S2)
    HJ HspT);
  [reflexivity | lia | rewrite WS1; lia | rewrite WS, WS1; lia | exact P3' | exact P4' | reflexivity
   | exact HraT | exact Hra4T | | | ].
  - apply achain_low. unfold s0Z. rewrite P8', unsigned_lit_small by (unfold IGF_SB; lia).
    unfold IGF_SB. lia.
  - intros HPRE1. eapply SRr_mono.
    + exact (FIND fx ly S W (ms_regs ms1) (ms_mem ms1) _ [] c name rcs nm HPRE1 HROD1 P10' Rc P11' Rname HQP1 HEV).
    + cbv beta. unfold apost_base.
      intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
      split; [exact HP3 | exact HQ3].
  - intros a (r & Hr & _). destruct Hr. }
cbv beta.
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HQa & HKF & HNA).
change (0 + 0) with 0 in HJ3.
destruct HNA as (HPerm & Hly3 & (ffs & HS3e)).
subst ly3.
(* the frame slots the call did not touch *)
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJc3 | exact HJ3 | exact Usp | lia
    | rewrite WS; lia | lia | lia | lia |].
  intros a _ (r & Hr & _). destruct Hr. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
rewrite P1.
assert (A44 : ew (havoc E 40 (map (getr regs3) CLOB)) 44 = getr regs3 10) by reflexivity.
remember (havoc E 40 (map (getr regs3) CLOB)) as Ec eqn:HEc.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 40)%nat -> ew Ec n = ew E n)
  by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (igf_extra rcs nm)) Ec).
{ destruct HAE as [HA1 HA2]. split; [intros n Hn; rewrite OLD3 by lia; exact (HA1 n Hn) | rewrite HEc; exact HA2]. }
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK1 : sh_ok SEGS IGFx ([] : list shent) Ec (mrestrict (w_H W3) mem3)) by (apply Forall_nil).
pose proof (proj1 HJ3) as HAR3.
assert (Hin3 : In (blk, bn) (ablocks B ly S3))
  by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hblk).
(* the bytes of the block the call kept *)
assert (KB : forall x, blk <= x < blk + bn ->
  aview SEGS (w_H W3) mem3 x = aview SEGS (w_H W) mem x).
{ intros x Hx. pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KB10 & _).
  replace x with (blk + (x - blk)) by lia.
  rewrite (KB10 blk bn (x - blk) Hblk Hin3 ltac:(lia) ltac:(intros (r & Hr & _); destruct Hr)).
  apply KEEP0; lia. }
assert (Q3' : sa_rconf (aview SEGS (w_H W3) mem3) c rcs)
  by (apply (igf_rconf_kept (aview SEGS (w_H W) mem) (aview SEGS (w_H W3) mem3) c rcs blk (blk + bn)); [exact KB | lia | unfold seg_spec.SEG_C_SIZE; lia | exact Q3]).
assert (HZ0 : U Ec (SLit 0) = 0) by (vm_compute; reflexivity).
(* 0x8976c: beqz a0 *)
destruct (r_find rcs nm) as [i|] eqn:RF.
- (* find answered Some i: a0 = c + 356 i, the branch is not taken *)
  destruct (igf_find_lt (aview SEGS (w_H W) mem) c rcs nm i Q3 RF) as [Hilt Hi32].
  assert (HA0 : getr regs3 10 = Z_to_bv 64 (c + 356 * Z.of_nat i)).
  { rewrite HQa. unfold seg_spec.find_ptr. rewrite RF.
    unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE. reflexivity. }
  assert (HU44 : U Ec (SOff 44 0) = c + 356 * Z.of_nat i)
    by (apply U_atom; [rewrite A44; exact HA0 | lia]).
  assert (Hsub : blk <= c + 356 * Z.of_nat i /\ c + 356 * Z.of_nat i + 356 <= blk + bn) by lia.
  assert (HRA44 : range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF (c + 356 * Z.of_nat i) 356)
    by (apply (range_addressable_of_block SEGS B LAWS ly S3 W3 mem3 md3 blk bn);
        [exact HAR3 | exact Hin3 | lia | lia]).
  assert (HAPP : forall x, c + 356 * Z.of_nat i <= x < c + 356 * Z.of_nat i + 356 ->
           ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
  { intros x Hx. destruct Hblkapp as [H4096 [HL | [HH HC]]];
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia. }
  assert (HSH : sh_ok SEGS IGFx igf_SH Ec (mrestrict (w_H W3) mem3)).
  { unfold sh_ok, igf_SH. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W3) mem3 Ec IGFx 44%nat (c + 356 * Z.of_nat i) 356
             (c + 356 * Z.of_nat i) 0 356 HRA44).
    - unfold IGFx. apply U_atom; [rewrite OLD3 by lia; exact E32 | unfold SHADOW_OFF; lia].
    - exact HU44.
    - lia.
    - lia.
    - intros x Hx. apply HAPP. lia. }
  assert (VSET : val_mem SEGS (mrestrict (w_H W3) mem3) (c + 356 * Z.of_nat i + 28) 4
                   (seg_spec.b2z (rs_ignore_set (r_seg rcs i)))).
  { apply (igf_val_of_rd SEGS (w_H W3) mem3). intros k Hk.
    exact (igf_set_rd (aview SEGS (w_H W3) mem3) c rcs i k Q3' Hilt Hk). }
  assert (VB0 : val_mem SEGS (mrestrict (w_H W3) mem3) (c + 356 * Z.of_nat i + 256) 1
                   (hd0 (rs_ignore_file (r_seg rcs i)))).
  { apply (igf_val_of_rd SEGS (w_H W3) mem3). intros k Hk.
    destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
    rewrite igf_le_byte1 by exact (igf_file0_range (aview SEGS (w_H W3) mem3) c rcs i Q3' Hilt).
    exact (igf_file0_rd (aview SEGS (w_H W3) mem3) c rcs i Q3' Hilt). }
  pose proof (igf_file0_range (aview SEGS (w_H W3) mem3) c rcs i Q3' Hilt) as HB0R.
  assert (HBASE44 : base_val Ec (Some 44%nat) = c + 356 * Z.of_nat i).
  { cbn [base_val]. rewrite A44, HA0. apply unsigned_lit_small. lia. }
  psrr_branch_tok RUN BR HS SHOK1 IGFspan.
  + exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite HU44, HZ0 in Hc. lia.
  + clear Hc.
    (* the entry's address, as a range the token engine can compute with *)
    assert (HF44 : afact_ok Ec 44%nat (mkAF 4096 140737479966720 2)).
    { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite A44, HA0.
      rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [|lia]. change (2 ^ 2) with 4.
      apply seg_query_facts.sq_seg_mod4. exact Q2. }
    match type of HS with st_ok_pi _ _ _ ?ss ?msr =>
      pose proof (st_ok_pi_add_fact Ec ss msr 44%nat (mkAF 4096 140737479966720 2) HS HF44) as HS5 end.
    clear HS HF44. rename HS5 into HS.
    destruct (rs_ignore_set (r_seg rcs i)) eqn:HIS.
    * (* ignore_set <> 0: the lw at 0x89784 gives 1 and the branch at 0x89788 is not taken *)
      destruct (Z.eqb_spec (hd0 (rs_ignore_file (r_seg rcs i))) 0) as [HBZ|HBZ].
      -- (* ignore_file[0] = 0: the mask is 0 and a0 is 0 *)
         cbn [seg_spec.b2z] in VSET. rewrite HBZ in VB0.
         match type of HS with st_ok_pi _ _ _ ?ss _ =>
           assert (HDok : all_disjoint Ec (igf_seg_region (SLit 1) (SLit 0)) (ss_mem ss)) end.
         { cbn [all_disjoint ss_mem]. split; [|exact I].
           unfold extent_disjoint, igf_seg_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
           rewrite HBASE44. cbn [base_val]. rewrite Usp3. left. lia. }
         assert (HRok : region_ok SEGS Ec (mrestrict (w_H W3) mem3) (igf_seg_region (SLit 1) (SLit 0))).
         { unfold region_ok, igf_seg_region.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
           rewrite HBASE44. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
           constructor; [|constructor; [|constructor]].
           - apply (chunk_ok_val SEGS Ec _ (c + 356 * Z.of_nat i) 28 4 (SLit 1) 1);
             [apply bv_eq; vm_compute; reflexivity
             | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia | exact VSET].
           - apply (chunk_ok_val SEGS Ec _ (c + 356 * Z.of_nat i) 256 1 (SLit 0) 0);
             [apply bv_eq; vm_compute; reflexivity
             | change (8 * Z.of_N 1) with 8; lia | change (Z.of_N 1) with 1; lia | exact VB0]. }
         match type of HS with st_ok_pi _ _ _ ?ss ?msr =>
           pose proof (st_ok_pi_add_region Ec ss msr (igf_seg_region (SLit 1) (SLit 0)) HS
             ltac:(vm_compute; reflexivity) HRok HDok) as HS5 end.
         clear HS HRok HDok. rename HS5 into HS.
         paj_run_tok RUN HS HJ3 HSH IGFspan.
         { awr_ok_tac. exact Usp3. }
         (* the return at 0x897c4 *)
         prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
         lazymatch goal with Hfr : frame_of Ec _ (mrestrict _ _) (mrestrict _ _) |- _ =>
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wf) ?msr) =>
           assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
             aview SEGS (w_H Wf) (ms_mem msr) a = aview SEGS (w_H W3) mem3 a)
           by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
                 (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
               [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
                 repeat (destruct Hin as [Hq0 | Hin];
                         [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]);
                 destruct Hin
               | exact Ha | exact Hn ]) end end.
         eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
         intros mat'. unfold apost_base.
         lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S3, r, m, d end.
         split; [rewrite F1; rewrite OLD3 by lia; rewrite E1;
                 unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
         split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
         split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (igf_extra rcs nm) HS);
                 [exact HAE3 | vm_compute; reflexivity]|].
         split; [|split;
           [ intros a Ha Hn _;
             rewrite (KEEPF a Ha ltac:(lia));
             rewrite (HKF a Ha ltac:(lia) (fun x : False => x));
             exact (KEEP0 a Ha ltac:(lia))
           | split; [exact HPerm | split; [reflexivity | exists ffs; exact HS3e]] ]].
         assert (HIFP : seg_spec.ignore_file_ptr c rcs nm = 0).
         { unfold seg_spec.ignore_file_ptr, r_ignore_file. rewrite RF, HIS, HBZ. reflexivity. }
         rewrite HIFP. exact F10.
      -- (* ignore_file[0] <> 0: a0 is the field's address *)
         cbn [seg_spec.b2z] in VSET.
         match type of HS with st_ok_pi _ _ _ ?ss _ =>
           assert (HDok : all_disjoint Ec (igf_seg_region (SLit 1) (SOff 34 0)) (ss_mem ss)) end.
         { cbn [all_disjoint ss_mem]. split; [|exact I].
           unfold extent_disjoint, igf_seg_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
           rewrite HBASE44. cbn [base_val]. rewrite Usp3. left. lia. }
         assert (HRok : region_ok SEGS Ec (mrestrict (w_H W3) mem3) (igf_seg_region (SLit 1) (SOff 34 0))).
         { unfold region_ok, igf_seg_region.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
           rewrite HBASE44. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
           constructor; [|constructor; [|constructor]].
           - apply (chunk_ok_val SEGS Ec _ (c + 356 * Z.of_nat i) 28 4 (SLit 1) 1);
             [apply bv_eq; vm_compute; reflexivity
             | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia | exact VSET].
           - apply (chunk_ok_val SEGS Ec _ (c + 356 * Z.of_nat i) 256 1 (SOff 34 0) (hd0 (rs_ignore_file (r_seg rcs i))));
             [cbn [sv_denot]; rewrite OLD3 by lia; rewrite E34;
               rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold igf_b0; rewrite RF; reflexivity
             | change (8 * Z.of_N 1) with 8; lia | change (Z.of_N 1) with 1; lia | exact VB0]. }
         match type of HS with st_ok_pi _ _ _ ?ss ?msr =>
           pose proof (st_ok_pi_add_region Ec ss msr (igf_seg_region (SLit 1) (SOff 34 0)) HS
             ltac:(vm_compute; reflexivity) HRok HDok) as HS5 end.
         clear HS HRok HDok. rename HS5 into HS.
         paj_run_tok RUN HS HJ3 HSH IGFspan.
         { awr_ok_tac. exact Usp3. }
         (* the return at 0x897c4 *)
         prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
         lazymatch goal with Hfr : frame_of Ec _ (mrestrict _ _) (mrestrict _ _) |- _ =>
         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wf) ?msr) =>
           assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
             aview SEGS (w_H Wf) (ms_mem msr) a = aview SEGS (w_H W3) mem3 a)
           by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
                 (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
               [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
                 repeat (destruct Hin as [Hq0 | Hin];
                         [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]);
                 destruct Hin
               | exact Ha | exact Hn ]) end end.
         eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
         intros mat'. unfold apost_base.
         lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S3, r, m, d end.
         split; [rewrite F1; rewrite OLD3 by lia; rewrite E1;
                 unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
         split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
         split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (igf_extra rcs nm) HS);
                 [exact HAE3 | vm_compute; reflexivity]|].
         split; [|split;
           [ intros a Ha Hn _;
             rewrite (KEEPF a Ha ltac:(lia));
             rewrite (HKF a Ha ltac:(lia) (fun x : False => x));
             exact (KEEP0 a Ha ltac:(lia))
           | split; [exact HPerm | split; [reflexivity | exists ffs; exact HS3e]] ]].
         assert (HIFP : seg_spec.ignore_file_ptr c rcs nm = c + 356 * Z.of_nat i + 256).
         { unfold seg_spec.ignore_file_ptr, r_ignore_file, seg_spec.rseg_addr,
             seg_spec.RSEG_SIZE, seg_spec.RS_IGNORE_FILE.
           rewrite RF, HIS.
           replace (negb (hd0 (rs_ignore_file (r_seg rcs i)) =? 0)) with true
             by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact HBZ).
           cbn [andb]. reflexivity. }
         rewrite F10, HIFP. rewrite (OLD3 34%nat ltac:(lia)), E34.
         unfold igf_b0. rewrite RF. rewrite A44, HA0, unsigned_lit_small by lia.
         apply igf_mask; lia.
    * (* ignore_set = 0: the branch at 0x89788 is taken and a0 is 0 *)
      cbn [seg_spec.b2z] in VSET.
      match type of HS with st_ok_pi _ _ _ ?ss _ =>
        assert (HDok : all_disjoint Ec (igf_seg_region (SLit 0) (SOff 34 0)) (ss_mem ss)) end.
      { cbn [all_disjoint ss_mem]. split; [|exact I].
        unfold extent_disjoint, igf_seg_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
        rewrite HBASE44. cbn [base_val]. rewrite Usp3. left. lia. }
      assert (HRok : region_ok SEGS Ec (mrestrict (w_H W3) mem3) (igf_seg_region (SLit 0) (SOff 34 0))).
      { unfold region_ok, igf_seg_region.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite HBASE44. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        - apply (chunk_ok_val SEGS Ec _ (c + 356 * Z.of_nat i) 28 4 (SLit 0) 0);
          [apply bv_eq; vm_compute; reflexivity
          | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia | exact VSET].
        - apply (chunk_ok_val SEGS Ec _ (c + 356 * Z.of_nat i) 256 1 (SOff 34 0) (hd0 (rs_ignore_file (r_seg rcs i))));
          [cbn [sv_denot]; rewrite OLD3 by lia; rewrite E34;
            rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold igf_b0; rewrite RF; reflexivity
          | change (8 * Z.of_N 1) with 8; lia | change (Z.of_N 1) with 1; lia | exact VB0]. }
      match type of HS with st_ok_pi _ _ _ ?ss ?msr =>
        pose proof (st_ok_pi_add_region Ec ss msr (igf_seg_region (SLit 0) (SOff 34 0)) HS
          ltac:(vm_compute; reflexivity) HRok HDok) as HS5 end.
      clear HS HRok HDok. rename HS5 into HS.
      paj_run_tok RUN HS HJ3 HSH IGFspan.
      { awr_ok_tac. exact Usp3. }
      (* the return at 0x897c4 *)
      prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
      lazymatch goal with Hfr : frame_of Ec _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wf) ?msr) =>
        assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
          aview SEGS (w_H Wf) (ms_mem msr) a = aview SEGS (w_H W3) mem3 a)
        by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
              (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
            [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
              repeat (destruct Hin as [Hq0 | Hin];
                      [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]);
              destruct Hin
            | exact Ha | exact Hn ]) end end.
      eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros mat'. unfold apost_base.
      lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S3, r, m, d end.
      split; [rewrite F1; rewrite OLD3 by lia; rewrite E1;
              unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
      split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
      split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (igf_extra rcs nm) HS);
              [exact HAE3 | vm_compute; reflexivity]|].
      split; [|split;
        [ intros a Ha Hn _;
          rewrite (KEEPF a Ha ltac:(lia));
          rewrite (HKF a Ha ltac:(lia) (fun x : False => x));
          exact (KEEP0 a Ha ltac:(lia))
        | split; [exact HPerm | split; [reflexivity | exists ffs; exact HS3e]] ]].
      assert (HIFP : seg_spec.ignore_file_ptr c rcs nm = 0).
      { unfold seg_spec.ignore_file_ptr, r_ignore_file. rewrite RF, HIS. reflexivity. }
      rewrite HIFP. exact F10.
- (* find answered None: a0 = 0, the branch is taken, the epilogue returns 0 *)
  assert (HA0 : getr regs3 10 = Z_to_bv 64 0).
  { rewrite HQa. unfold seg_spec.find_ptr. rewrite RF. reflexivity. }
  assert (HU44 : U Ec (SOff 44 0) = 0) by (apply U_atom; [rewrite A44; exact HA0 | lia]).
  psrr_branch_tok RUN BR HS SHOK1 IGFspan.
  + clear Hc.
    paj_run_tok RUN HS HJ3 SHOK1 IGFspan.
    { awr_ok_tac. exact Usp3. }
    (* the return at 0x897c4 *)
    prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
    lazymatch goal with Hfr : frame_of Ec _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict (w_H ?Wf) ?msr) =>
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
        aview SEGS (w_H Wf) (ms_mem msr) a = aview SEGS (w_H W3) mem3 a)
      by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
            (fun a => spZ regs - 16 <= a < spZ regs) Hfr);
          [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (destruct Hin as [Hq0 | Hin];
                    [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]);
            destruct Hin
          | exact Ha | exact Hn ]) end end.
    eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S3, r, m, d end.
    split; [rewrite F1; rewrite OLD3 by lia; rewrite E1;
            unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (igf_extra rcs nm) HS);
            [exact HAE3 | vm_compute; reflexivity]|].
    split; [|split;
      [ intros a Ha Hn _;
        rewrite (KEEPF a Ha ltac:(lia));
        rewrite (HKF a Ha ltac:(lia) (fun x : False => x));
        exact (KEEP0 a Ha ltac:(lia))
      | split; [exact HPerm | split; [reflexivity | exists ffs; exact HS3e]] ]].
    assert (HIFP : seg_spec.ignore_file_ptr c rcs nm = 0).
    { unfold seg_spec.ignore_file_ptr. rewrite RF. destruct (r_ignore_file rcs nm); reflexivity. }
    rewrite HIFP, F10, A44. exact HA0.
  + exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc.
    apply Hc. rewrite HU44, HZ0. reflexivity.
Qed.
End e.
End f.
End d.
