(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 (the plumbing of
   the property loop's block lemmas: pa_chunk8, pa_keep, pa_kwr_ro, pa_run, pa_runb, pa_branch, pa_reg, pa_leaf),
   proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (kept_run) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v
   at a529a88a618 (its section g and its tactics: the (location, value) facts of a cut, the journal-and-frame step,
   the segment's write set, the first block's bounds and pod_put, the model of a shape-7 property, the start facts
   and the input at a cut) for reac-pw/fuzz_headamp's image B: rs_ / rl_ / rm_ -> hsu_ / hd_ / hm_, role's image A
   record and code -> fuzz_headamp.asan-ubsan's (lib/AU/Img0U.v rsegs, HPgImgB.headamp_himg_B: class-4 frame of
   1024 bytes, real frame of 0x220 bytes, write set [F+0x20, F+0x278) / 116 shadow bytes / [R, R+0x198)), the block
   post HPgSteps.hdu_blk_postE in place of pa_post, one table over the four pieces of image B. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropKit.v; 270 of its 325 lines of code are new or changed and 356 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): four blocks of steps of the
   piece W8 of the build (M01) of LLVMFuzzerTestOneInput 0x80c40 (J 0x82618 -> C 0x81888 / CL 0x82a18), the
   statements of lib/AU/HPgW8BKit.v: hw8_blkA (J -> pod_write_ent 0x84634), hw8_blkC0 (0x8264c -> 0x826c8 when
   first = 0), hw8_blkC2 (0x826c0 -> 0x826c8) and hw8_blkD (0x82704 -> C / CL). Proves no function (kind: segment
   lemma).

   REGISTERS AND R-CELLS this file reads: s1 = R (x9); in A s2 = pp + 0x4000 (x18), s4 (x20), s7 = pp (x23), s11 = K
   (x27), a3 (x13), t1 (x6), R+0x150 the shadow address of pp + 0x4000, pp + 0x4000 the length len; in C0 R+0x140
   (first = 0) and R+0x158 (the pod index); in C2 R+0x158; in D a1 (x11, the next pod index) and R+0x128 (cnt).
   No block writes a byte.

   HOW. Each block is one run of the token engine (lib/Reusable/YCbq.v aj_run_to_tok / aj_run_tok) over the kit's
   code table hw8_tbl from a symbolic state built from the statement's premises. A: the R-cell R+0x150 as a chunk
   holding the shadow address in the engine's own form over the atom of s7 (SOff 23 0x4000 >> 3, plus s11), s2
   pinned to SOff 23 0x4000, len as the extra atom 32 with its range [0, 5384] in a read-only region of base s7, and
   one shadow entry over pp's 19744 bytes on s7 with the shadow base s11 (its atom has the exact range [K, K]): the
   check `lbu` / `beqz` 0x8261c-0x82620 reads the literal 0 and the capacity test `bltu` 0x8263c is decided by the
   range of len. C0, C2: the R-cells as chunks (R+0x140 the literal 0, so the `beqz` 0x82654 is decided), the pod
   index as the extra atom 33. D: cnt as the extra atom 33; the run stops at `bne a1,a0` 0x82708, the branch is split
   (srr_branch_tok) and each side runs out of the table, to C or (by the `j` 0x8270c) to CL. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg HPgW8BKit HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the engine's contexts ===================================== *)
(* the band of shadow addresses the tokens may name *)
Definition hw8_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* A: the shadow base is s11 (x27); the shadow address of pp + 0x4000 as the cut keeps it in R+0x150 *)
Definition hw8_Ax : sv := SOff 27 0.
Definition hw8_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0x4000) (SLit 3)) (SOff 27 0).
(* pp on s7 (19744 bytes) *)
Definition hw8_ASH : list shent := [mkSHE 23 0 19744].
Definition HW8_PPHI : Z := 0x7fffff800000 - 19744.
(* pp in the heap, K, and len (the extra atom 32) *)
Definition hw8_Aatoms : list (nat * afact) :=
[(23%nat, mkAF 4096 HW8_PPHI 0); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 5384 0)].
(* s2 pinned to pp + 0x4000 over the atom of s7 *)
Definition hw8_Aregs : list sv := sr_set sr_atoms (18%bv : bv 5) (SOff 23 0x4000).
Definition hw8_Aslot : YP09.region :=
YP09.mkRegion (Some 9%nat) 0x150 0x158 0 0 [YP09.mkChunk 0x150 (CVal 8 hw8_shx)].
Definition hw8_Alen : YP09.region :=
YP09.mkRegion (Some 23%nat) 0x4000 0x4008 0 0 [YP09.mkChunk 0x4000 (CVal 8 (SOff 32 0))].
Definition hw8_ssA : sstate := mkSS HW8_J hw8_Aregs [hw8_Aslot; hw8_Alen] None (mkFacts hw8_Aatoms [] []).

(* C0, C2, D: env slot 32 is K (no shadow entry: these blocks read no shadow byte), slot 33 the cell's value *)
Definition hw8_Bx : sv := SOff 32 0.
Definition hw8_ext (v : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 v].
Definition hw8_facts : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition hw8_ssC0 : sstate :=
mkSS HW8_RA1 sr_atoms
[YP09.mkRegion (Some 9%nat) 0x140 0x160 0 0
  [YP09.mkChunk 0x140 (CVal 8 (SLit 0)); YP09.mkChunk 0x158 (CVal 8 (SOff 33 0))]] None hw8_facts.
Definition hw8_ssC2 : sstate :=
mkSS HW8_RA2 sr_atoms
[YP09.mkRegion (Some 9%nat) 0x158 0x160 0 0 [YP09.mkChunk 0x158 (CVal 8 (SOff 33 0))]] None hw8_facts.
Definition hw8_ssD : sstate :=
mkSS HW8_SC1 sr_atoms
[YP09.mkRegion (Some 9%nat) 0x128 0x130 0 0 [YP09.mkChunk 0x128 (CVal 8 (SOff 33 0))]] None hw8_facts.

Section k. Context {fx : YK11.FPState}.
(* an atom of the start registers, read back *)
Lemma hw8_soff0 : forall E regs extra (n : nat) (r : bv 5), env_agree 32 (Ereg regs extra) E -> (n < 32)%nat ->
Z.of_nat n = bv_unsigned r -> sv_denot E (SOff n 0) = getr regs r.
Proof.
intros E regs extra n r [HA _] Hn Hr. cbn [sv_denot]. rewrite Z.add_0_r.
assert (Ew : ew E n = ew (Ereg regs extra) n) by (first [apply HA; exact Hn | symmetry; apply HA; exact Hn]).
rewrite Ew, Z_to_bv_bv_unsigned. exact (ew_Ereg_nat regs extra n r Hr).
Qed.
Lemma hw8_ext_K : forall regs v, ew (Ereg regs (hw8_ext v)) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros. reflexivity. Qed.
Lemma hw8_ext_v : forall regs v, ew (Ereg regs (hw8_ext v)) 33 = Z_to_bv 64 v.
Proof. intros. reflexivity. Qed.
Lemma hw8_facts_ok : forall regs v, facts_ok (Ereg regs (hw8_ext v)) hw8_facts.
Proof.
intros regs v. split; [|split; exact I]. cbn [hw8_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite hw8_ext_K, unsigned_lit_small by (unfold SHADOW_OFF; lia). repeat split; try lia; apply Z.mod_1_r.
Qed.
End k.

(* ---- the walk's plumbing ---- *)
(* KE : every byte as at the block's start; a run with no write window keeps it *)
Ltac hw8_keep kwr :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
let KS := fresh "KS" in let KW := fresh "KW" in
pose proof (cb_kept_run _ _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => assert (KW : P) by kwr end;
specialize (KS KW); clear KW KE HFr; rename KS into KE
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the write windows of a state without one *)
Ltac hw8_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
(* the value of register r at the end of a run, as the symbolic state holds it *)
Ltac hw8_reg r :=
lazymatch goal with HS : st_ok ?sg ?E ?ssf (restrict ?H ?ms) |- context [getr (ms_regs ?ms) r] =>
rewrite (st_ok_restrict_reg sg H E ssf ms r HS);
let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* the leaf: hw8_post's first five clauses; the registers, the bytes and the relation are left *)
Ltac hw8_leaf0 :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
apply SRr_ret; red; split; [reflexivity|];
exists (ms_regs ms), (ms_mem ms); eexists;
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
split; [exact HJ|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|]
end.
(* ... and the registers outside clob, each still its own atom, and the bytes (KE) *)
Ltac hw8_leaf extra :=
hw8_leaf0;
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HAE : env_agree 32 (Ereg ?regs _) ?E,
  KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs extra (w_H W) _ HS HAE); vm_compute; reflexivity|];
split; [intros a Ha Hz; exact (KE a Ha Hz)|]
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* R lies in the stack: above the allocator's ceiling and below 2^47 *)
Lemma hw8_R_rng : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world rsegs) memc mdc k (R : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
sp0 - STK <= R -> R + 0x220 <= sp0 -> alloc_ceiling <= R /\ R + 0x220 <= 2 ^ 47.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k R HJ H0 H1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _). lia.
Qed.

(* ===================================== A: J 0x82618 -> pod_write_ent 0x84634 ===================================== *)
Lemma hw8_blkA : hw8_blkA_stmt B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp L HJ Hin HR0 HR1 R9 R18 R23 R27 V150 Vlen HL.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _).
destruct (hw8_R_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R HJ HR0 HR1) as (HRc & HR47).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (Erq : req_size PP_SIZE = 19744) by reflexivity.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pp PP_SIZE HAR Hin) as (_ & Hpp0 & Hppc & Happ & _).
rewrite Erq in Hppc, Happ.
remember (Ereg regs [Z_to_bv 64 L]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 L]) E) by (subst E; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; exact (ew_Ereg_nat regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 L) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E9 : ew E 9 = Z_to_bv 64 R) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E23 : ew E 23 = Z_to_bv 64 pp) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = pp) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = L) by (rewrite E32; apply unsigned_lit_small; lia).
assert (P18 : sv_denot E (SOff 23 0x4000) = getr regs 18%bv).
{ rewrite R18, denot_lit_U, (U_atom_off E 23 pp 0x4000 E23) by lia. reflexivity. }
(* the symbolic state at J *)
assert (HS : st_ok rsegs E hw8_ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 HW8_J) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. unfold hw8_ssA. apply (entry_st_ok_full rsegs).
  - unfold hw8_Aregs. apply regs_ok_rereg; [apply regs_ok_Ereg | reflexivity |].
    rewrite <- HE. symmetry. exact P18.
  - vm_compute. reflexivity.
  - rewrite <- HE. repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok, hw8_Aslot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val rsegs E _ R 0x150 8 hw8_shx (shadow_addr (pp + 0x4000) mod 2 ^ 64)); [| | cbn; lia | exact V150].
      * unfold hw8_shx. rewrite denot_lit_U. apply Z_to_bv64_eq_mod.
        rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, !U_SOff, U23, U27, !Z.add_0_r.
        change (Z.land (zcanon 3) 63) with 3. unfold zcanon, M64.
        rewrite (Z.mod_small (pp + 0x4000)) by lia. rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
        rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        assert (0 <= (pp + 0x4000) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
        rewrite (Z.mod_small ((pp + 0x4000) / 8)) by lia.
        rewrite (Z.mod_small ((pp + 0x4000) / 8 + SHADOW_OFF)) by (unfold SHADOW_OFF; lia).
        unfold shadow_addr. rewrite Z.mod_mod by lia. f_equal. lia.
      * pose proof (Z.mod_pos_bound (shadow_addr (pp + 0x4000)) (2 ^ 64) ltac:(lia)). cbn. lia.
    + unfold region_ok, hw8_Alen. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ pp 0x4000 8 (SOff 32 0) L); [| cbn; lia | cbn; lia | exact Vlen].
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
  - rewrite <- HE. apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val hw8_Aslot hw8_Alen]. rewrite U9, U23.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - rewrite <- HE. split; [|split; exact I]. cbn [f_atoms hw8_Aatoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U23, U27, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold HW8_PPHI, SHADOW_OFF. repeat split; lia. }
(* the shadow entry over pp: every byte of the block is addressable, and the block lies outside the shadow band *)
assert (SHOK : sh_ok rsegs hw8_Ax hw8_ASH E (mrestrict (w_H W) memc)).
{ unfold sh_ok, hw8_ASH. repeat apply Forall_cons; try apply Forall_nil;
  unfold shent_ok, app_apart, hw8_Ax; cbn [she_m she_lo she_hi];
  rewrite ?(U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom E 23 pp E23) by lia.
  split.
  - change (rd_of rsegs (mrestrict (w_H W) memc)) with (aview rsegs (w_H W) memc).
    apply (range_addressable_of_block rsegs B LAWS lyc Sc W memc mdc pp PP_SIZE); [exact HAR | exact Hin | lia | rewrite Erq; lia].
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg in Happ. unfold SHADOW_OFF. lia. }
clear HE.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 HW8_J) with (Z_to_bv 64 HW8_J).
aj_run_to_tok hw8_tbl_ok HS HJ SHOK hw8_span HW8_PWE; [awr_ok_tac|].
hw8_keep hw8_kwr_ro.
hw8_leaf0.
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [Z_to_bv 64 L] (w_H W) _ [((18%bv : bv 5), SOff 23 0x4000)] HS HAE);
  [intros rr ee Hq; destruct Hq as [Hq|[]]; inversion Hq; subst; exact P18 | vm_compute; reflexivity]|].
split; [intros a Ha Hz; exact (KE a Ha Hz)|].
cbv beta.
split; [hw8_reg (1%bv : bv 5); apply bv_eq; vm_compute; reflexivity|].
split; [hw8_reg (10%bv : bv 5); rewrite denot_lit_U, (U_atom E 23 pp E23) by lia; reflexivity|].
split; [hw8_reg (11%bv : bv 5); exact (hw8_soff0 E regs _ 20 20%bv HAE ltac:(lia) eq_refl)|].
split; [hw8_reg (21%bv : bv 5); exact (hw8_soff0 E regs _ 13 13%bv HAE ltac:(lia) eq_refl)|].
hw8_reg (26%bv : bv 5); exact (hw8_soff0 E regs _ 6 6%bv HAE ltac:(lia) eq_refl).
Qed.

(* ===================================== C0: 0x8264c -> 0x826c8 when first = 0 ===================================== *)
Lemma hw8_blkC0 : hw8_blkC0_stmt B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R kk HJ HR0 HR1 R9 V140 V158 Hkk.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct (hw8_R_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R HJ HR0 HR1) as (HRc & HR47).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (E9 : bv_unsigned (ew (Ereg regs (hw8_ext kk)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew (Ereg regs (hw8_ext kk)) 33 = Z_to_bv 64 kk) by apply hw8_ext_v.
assert (HS : st_ok rsegs (Ereg regs (hw8_ext kk)) hw8_ssC0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HW8_RA1) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val rsegs _ _ R 0x140 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V140].
    + apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 33 0) kk); [| cbn; lia | cbn; lia | exact V158].
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - apply hw8_facts_ok. }
remember (Ereg regs (hw8_ext kk)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hw8_ext kk)) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs hw8_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 HW8_RA1) with (Z_to_bv 64 HW8_RA1).
aj_run_to_tok hw8_tbl_ok HS HJ SHOK hw8_span HW8_SC0; [awr_ok_tac|].
hw8_keep hw8_kwr_ro.
hw8_leaf (hw8_ext kk).
cbv beta.
split; [hw8_reg (10%bv : bv 5); apply bv_eq; vm_compute; reflexivity|].
hw8_reg (11%bv : bv 5). rewrite denot_lit_U, (U_atom E 33 kk E33) by lia. reflexivity.
Qed.

(* ===================================== C2: 0x826c0 -> 0x826c8 ===================================== *)
Lemma hw8_blkC2 : hw8_blkC2_stmt B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R kk HJ HR0 HR1 R9 V158 Hkk.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct (hw8_R_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R HJ HR0 HR1) as (HRc & HR47).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (E9 : bv_unsigned (ew (Ereg regs (hw8_ext kk)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : ew (Ereg regs (hw8_ext kk)) 33 = Z_to_bv 64 kk) by apply hw8_ext_v.
assert (HS : st_ok rsegs (Ereg regs (hw8_ext kk)) hw8_ssC2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HW8_RA2) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 0x158 8 (SOff 33 0) kk); [| cbn; lia | cbn; lia | exact V158].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - apply hw8_facts_ok. }
remember (Ereg regs (hw8_ext kk)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hw8_ext kk)) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs hw8_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 HW8_RA2) with (Z_to_bv 64 HW8_RA2).
aj_run_to_tok hw8_tbl_ok HS HJ SHOK hw8_span HW8_SC0; [awr_ok_tac|].
hw8_keep hw8_kwr_ro.
hw8_leaf (hw8_ext kk).
cbv beta.
split; [hw8_reg (10%bv : bv 5); apply bv_eq; vm_compute; reflexivity|].
hw8_reg (11%bv : bv 5). rewrite denot_lit_U, (U_atom E 33 kk E33) by lia. reflexivity.
Qed.

(* ===================================== D: 0x82704 -> C 0x81888 / CL 0x82a18 ===================================== *)
Lemma hw8_blkD : hw8_blkD_stmt B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R kk1 cnt HJ HR0 HR1 R9 R11 V128 Hkk Hcnt.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct (hw8_R_rng _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R HJ HR0 HR1) as (HRc & HR47).
pose proof asan_consts as (C1 & _ & _ & _ & _).
assert (E9 : bv_unsigned (ew (Ereg regs (hw8_ext cnt)) 9) = R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E11 : ew (Ereg regs (hw8_ext cnt)) 11 = Z_to_bv 64 kk1)
  by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), R11; reflexivity).
assert (E33 : ew (Ereg regs (hw8_ext cnt)) 33 = Z_to_bv 64 cnt) by apply hw8_ext_v.
assert (HS : st_ok rsegs (Ereg regs (hw8_ext cnt)) hw8_ssD
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HW8_SC1) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 0x128 8 (SOff 33 0) cnt); [| cbn; lia | cbn; lia | exact V128].
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - apply hw8_facts_ok. }
remember (Ereg regs (hw8_ext cnt)) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (hw8_ext cnt)) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs hw8_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 HW8_SC1) with (Z_to_bv 64 HW8_SC1).
(* 0x82704: a0 := cnt; stop at the `bne a1,a0` 0x82708 *)
aj_run_tok hw8_tbl_ok HS HJ SHOK hw8_span; [awr_ok_tac|].
hw8_keep hw8_kwr_ro.
srr_branch_tok hw8_tbl_ok HS SHOK hw8_span;
rewrite branch_ne_U, (U_atom E 11 kk1 E11), (U_atom E 33 cnt E33) in Hc by lia.
- (* taken: kk1 <> cnt, to C *)
  replace (if kk1 =? cnt then HW8_CL else HW8_C) with HW8_C
    by (destruct (Z.eqb_spec kk1 cnt) as [Heq|Hne]; [cbn in Hc; discriminate | reflexivity]).
  aj_run_to_tok hw8_tbl_ok HS HJ SHOK hw8_span HW8_C; [awr_ok_tac|].
  hw8_keep hw8_kwr_ro.
  hw8_leaf (hw8_ext cnt).
  exact I.
- (* fall-through: kk1 = cnt, `j` 0x8270c to CL *)
  replace (if kk1 =? cnt then HW8_CL else HW8_C) with HW8_CL
    by (destruct (Z.eqb_spec kk1 cnt) as [Heq|Hne]; [reflexivity | cbn in Hc; discriminate]).
  aj_run_to_tok hw8_tbl_ok HS HJ SHOK hw8_span HW8_CL; [awr_ok_tac|].
  hw8_keep hw8_kwr_ro.
  hw8_leaf (hw8_ext cnt).
  exact I.
Qed.
End d.
End b.

Print Assumptions hw8_blkA.
Print Assumptions hw8_blkC0.
Print Assumptions hw8_blkC2.
Print Assumptions hw8_blkD.
