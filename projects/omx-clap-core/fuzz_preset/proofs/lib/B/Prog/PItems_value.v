(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_head.v, with its module paths and module names changed; 4555 of its 4719 lines of code are new or changed and 1142 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_body_key.v, with its module paths and module names changed; 779 of its 888 lines of code are new or changed and 4610 lines of the source are left out. *)
(* Theorem Labs, 2026-10: block VAL of parse_items' image-B walk (segment VALUE,
   file 1 of 4): B 0x87cd8 .. 0x87d94, PI_O_VAL .. PI_O_PVAL, the kid slot's checks and the checked memset. Rule 24:
   proves no function (kind: segment lemma).
   PROVED (Qed): pi_val_holds : pv_call_spec B ARx SK d CTX0 CW N -> pi_val_spec B ARx SK d CTX0 CW N, PItems_pres.v's
   pi_val_spec at image B (B_prog_listing / PL_prog_B / PI_prog_B, prh_img_B) from PItems_value_pres.v's pv_call_spec at
   the next block, the jal parse_value at PI_O_PVAL (PItems_value_call.v's). Both specs take the cursor set CW and the
   budgeted journal pi_ajR .. WS0 at the walk's relation wle' pa_segs RZ_cf with wbudget CW 0 WS0, and conclude
   pi_goalR at wle'; the three runs (PI_RUNR / PI_RUNTOR, the branches by paj_branchR), the memset
   (YGcallMxmn.aj_intrin_at_xmR, lifted by YA0nH.SRr_SRr') and the run after it take the empty-budget journal rebased at
   Sc's depot (YCbqGwild.ajournal_xw_rebaseR), and the step back before pv_call_spec is
   YCbqGwild.ajournal_xw_unbase0R (the block keeps the allocator state Sc), at the same WS0.
   THE RUN (YC1fPx paj_run_tok_x / paj_run_to_tok_x from the symbolic state ss_val, realised by pv_st_val):
     0x87cd8 .. 0x87d10: the shadow checks of [sp + 24] = shadow (v + 24) and of s8 = shadow (v + 40), n := v->n,
       kids := v->kids, slot := (n << 6) - (n << 3) + kids, the result-non-zero check; the run stops at 0x87d14;
     0x87d14 and 0x87d2c: two branches split by hand (psrr_branch_tok), the taken arm of each refuted below;
     0x87d30 .. 0x87d34: a2 := 56, jal __asan_memset (the listing names it checked_memset), through its text AMEMSET by
       YGcallMxmn.v aj_intrin_at_xm (the text with the memnorm keep): a0 = slot, a1 = 0, a2 = 56, sp at offset
       -144 - e from the window top;
     0x87d38 .. 0x87d90: after the call (jafter_call_keep_pi keeps the frame-cache region and the node region) the same
       shadow and UBSan checks again, decided by the engine from the two conditions the first copy added; a0 := s1; the
       run stops at PI_O_PVAL, where pv_call_spec is applied at the memory after the memset.
   CHECKS NOT TAKEN, each with its fact:
     0x87ce0 / 0x87d40 bnez on shadow (v + 24) and 0x87ce8 / 0x87d48 bnez on shadow (v + 40), to the errpath slow paths
       0x88030 / 0x88038 / 0x88040 / 0x88048: decided in the run by the shadow entry (v, 0, 56), from pi_cur's
       range_addressable v 56, at the entry memory and again after the memset (which keeps every shadow byte);
     0x87d10 / 0x87d70 beq (snez kids) (seqz slot), the result-non-zero check, to PI_O_TRAP: decided in the run by the
       atom facts kids >= 4096 (prh_hblock and alx_blocks) and so slot > 0;
     0x87d14 bltu slot < kids, the pointer-overflow check, to PI_O_TRAP: not taken, kids <= 2 ^ 47 and n <= 2 ^ 54
       (pi_cont) give kids + 56 n < 2 ^ 61, no wrap (pv_U_slot); its copy 0x87d74: decided in the run by the added
       condition kids + 56 n >= kids;
     0x87d2c bnez (snez (mulh n 56 xor srai (56 n) 63)), the signed-overflow check of 56 n, to PI_O_TRAP: not taken,
       56 n < 2 ^ 60 makes the high product word and the sign word 0 (pv_U_mulh); its copy 0x87d8c: decided in the run
       by the added condition.
   THE MEMSET'S PREMISES: every slot byte is an in_tmp_block byte (the kids block is a block of the current state and
     not of the entry state, rd_blocks_move); amem_range from the block's in_app; range_addressable and shadow_hull_vis
     of the slot from HSH on the kids block (its user range past cf_head covers kids .. kids + 56 cap).
   THE DATA ACROSS THE MEMSET (pv_vdata_kept, pv_frame_kept): the memset keeps every byte outside the slot and the
     ESTACK window below sp, and pv_vdata reads none of these: q's 24 bytes and the frame (above sp), the text (in a
     block of the entry state or in the image, pv_home_apart), the node v (pj_apartR), the shadow bytes (below 2 ^ 46),
     the statics (image bytes), the ledger's head words (below their own block's user range: prh_head_wide), the first
     n slots, the key slots and the blocks of Di / Dk (blocks of the current ledger other than the kids block: NoDup of
     the ledger's bases and the blocks' separation). The tree predicates move by the kit's PRH_Reader.v frame lemmas
     (pj_nodeR_frame, pj_memsR_mono, ...). pj_zeroR of the slot is the memset's effect at x = 0. pv_vdata's batch-kit tail
     crosses it too: pi_grant, the cap, the key tie and pi_fl_eqV read no memory; pi_ncaps and pi_forder move by
     PItems_value_model.pvm_ncaps_frame / pvm_forder_frame from the agreement on pi_cont's read bytes pvm_cont_ufoot
     (the header v .. v + 56, the slots i < n, the key slots i < n, the blocks of Di: all kept bytes).
   SECTION HYPOTHESES (each is discharged by its owner at the instance):
     LAWS : AR_laws_x SEGS B ARx HL (the allocator's laws at head length HL; the instance);
     HSH : pi_hshadow_law B ARx cf_head (the instance, YGcfHeadSh.v ARx_hshadow_law_cf_ok);
     AMEMSET : forall fy, YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS B ARx OSet (pa_sigma (PAImg := PA)
       AS___asan_memset) (__asan_memset's text with the memnorm keep);
     HW : prh_head_wide, 8 <= cf_head (the kit's spelling, PRH_Base.v; a Theorem Labs lane's preset_head_wide at the instance). It is
       needed: at cf_head = 0 and n = 0 the slot covers the kids block's ledger head word, which the memset zeroes, so
       no ledger holds after the memset.
   THE TRAVELLING FACTS (form (b); PItems_pres.v pi_val_pre / PItems_value_pres.v pv_call_pre): the
     overlay's normal form YAkMemnorm.memnorm crosses the three runs before the call and the run after it by
     YAkMemnorm.memnorm_sub (no run of this block writes a byte: every region has an empty window), and the memset by
     aj_intrin_at_xm's keep; pv_vdata's PItems_posb.pi_posb S Sc tr0 and pi_live over tr0 cross the block unchanged
     (pv_vdata_kept), since the block keeps the allocator state Sc and the prefix trace tr0 (the memset is a runtime
     intrinsic, the journal's state is unchanged).
   COPIED: pv_hull_sub / pv_shadow_low / pv_hull_low / pv_ro_img (FuzzStrdupB.v sd_hull_sub / sd_shadow_low /
     sd_hull_low / sd_ro_img; no .vo on this base), pv_prregx (PItems_head.v prregx; PItems_head.v is red on this
     base), pv_in_img_b / pv_pst_allb / pv_pst_allb_sound / pv_pst_in_img (lib/A/Prog/S1ImgA.v in_img_b / pst_allb /
     pst_allb_sound, lib/B/Prog/S1ImgB.v pst_in_img_B; not Required, since S1ImgA Requires lib/A/PAImg_prog.v, image
     A's PAImg instance).
   Numerals: 0x2a0 (via PI_O_VAL) and 0x2fc + 4 (via PI_O_MSET, the return offset) LENGTH, offsets inside the body;
   144, 56, 48, 40, 32, 24, 16, 8 LENGTH (the frame, the pj_value node, its fields, a slot word, alignments); 176 LENGTH
   (parse_value's frame, in pv_stk_lo); 4096 LENGTH (ESTACK, the page); 16560 DERIVED (LEAF_pv_pi, checked by
   vm_compute); 6, 5 WORD (pj_value type tags); 3, 63 WORD (shift amounts); 64 WORD (the word width); 0 WORD (the
   memset's byte); 256 DERIVED (byte modulus); 2 ^ 60 WORD (the frame word `li a0,1; slli a0,a0,0x3c`); 2 ^ 42, 2 ^ 44,
   2 ^ 46, 2 ^ 47, 2 ^ 54, 2 ^ 63, 2 ^ 64 DERIVED (address-space, shadow and capacity bounds); register, atom and region
   indices (1 .. 34, [0; 1], bvmap 5) DERIVED (the engine's numbering). No ADDRESS: every pc is PV_K_VAL, PI_AT PI_O_*
   or the engine's computed offset; the hexadecimal addresses above are comments only. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YC80xf YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW YGcallMx FCiface YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres PItems_value_pres.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PItems_value_model.
(* the walk's world relation wle' pa_segs RZ_cf (YA0nH), the bind and the branch over it (YSRrG) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

(* ---- the listing offsets of the blocks this file walks (PItems_defs.v's PI_O_*, through PI_AT) ---- *)
Definition PV_K_VAL : Z := Eval vm_compute in (B_prog_sigma AS_parse_items - B_prog_val A_TEXT + PI_O_VAL).

(* the shadow base and span of the engine (FuzzMallocB.v's form) *)
Definition PV_Bx : sv := SLit SHADOW_OFF.
Definition PV_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow address of x, in the form the engine's match_x reads *)
Definition shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) PV_Bx.

(* ---- the symbolic state at PI_O_VAL: the pinned registers of the body (PItems_defs.v pi_regs / pi_regs_body),
   the frame cache at sp (atom 2), the node's kids and n fields (atom 19 = v), extra atoms 32 = kids, 33 = n ---- *)
Definition pv_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    8%bv (SOff 9 16)) 20%bv (SOff 9 8)) 22%bv (SOff 19 40)) 24%bv (shx (SOff 19 40)))
    26%bv (SLit SHADOW_OFF)) 27%bv (shx (SOff 9 0))) 25%bv (shx (SOff 9 16))) 23%bv (shx (SOff 9 8)).
Definition pv_frame_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 144 0 0
    [YP09.mkChunk 0 (CVal 8 (SLit (2 ^ 60))); YP09.mkChunk 8 (CVal 8 (shx (SOff 19 32)));
     YP09.mkChunk 16 (CVal 8 (SOff 19 32)); YP09.mkChunk 24 (CVal 8 (shx (SOff 19 24)));
     YP09.mkChunk 32 (CVal 8 (SOff 19 24))].
Definition pv_node_region (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 56 wlo whi
    [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 40 (CVal 8 (SOff 33 0))].
Definition pv_val_regions : smem := [pv_frame_region; pv_node_region 0 0].
Definition pv_val_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
            (19%nat, mkAF 4096 (2 ^ 47 - 56) 3); (32%nat, mkAF 4096 (2 ^ 47 - 1) 4);
            (33%nat, mkAF 0 (2 ^ 54 - 1) 0) ] [] [].
Definition ss_val : sstate := mkSS PV_K_VAL pv_regs pv_val_regions None pv_val_facts.
Definition pv_val_SH : list shent := [mkSHE 19 0 56].

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Definition PV_E (regs : bvmap 5 word) (kids n : Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 kids; Z_to_bv 64 n]).

Lemma pv_denot0 : forall E k, sv_denot E (SOff k 0) = ew E k.
Proof. intros E k. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma pv_denot_shx : forall E n a c, ew E n = Z_to_bv 64 a -> 0 <= a -> a + c < 2 ^ 63 -> 0 <= c ->
  sv_denot E (shx (SOff n c)) = Z_to_bv 64 (pi_sh (a + c)).
Proof.
intros E n a c Hn Ha Hc Hc0.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (shx (SOff n c)))). f_equal.
change (U E (shx (SOff n c)) = pi_sh (a + c)). unfold shx, PV_Bx, pi_sh.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, Hn, U_lit, U_lit by (unfold SHADOW_OFF; lia).
rewrite unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (a + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (a + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id (a + c)) by (unfold M64; lia). rewrite (zcanon_id ((a + c) / 8)) by (unfold M64; lia).
unfold SHADOW_OFF. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* the symbolic state at PI_O_VAL holds of a concrete one *)
Lemma pv_st_val : forall (W : world SEGS) (regs : bvmap 5 word) mem q v kids n,
  getr regs 9 = w64 q -> getr regs 19 = w64 v -> getr regs 8 = w64 (q + 16) -> getr regs 20 = w64 (q + 8) ->
  getr regs 22 = w64 (v + 40) -> getr regs 24 = w64 (pi_sh (v + 40)) -> getr regs 26 = w64 SHADOW_OFF ->
  getr regs 27 = w64 (pi_sh q) -> getr regs 25 = w64 (pi_sh (q + 16)) -> getr regs 23 = w64 (pi_sh (q + 8)) ->
  2 ^ 46 <= spZ regs -> spZ regs + 144 <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  2 ^ 46 <= q -> q + 24 <= 2 ^ 47 -> q mod 8 = 0 ->
  4096 <= v -> v + 56 <= 2 ^ 47 -> v mod 8 = 0 -> (v + 56 <= spZ regs \/ spZ regs + 144 <= v) ->
  4096 <= kids <= 2 ^ 47 - 1 -> kids mod 16 = 0 -> 0 <= n <= 2 ^ 54 - 1 ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs) 8 (2 ^ 60) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 8) 8 (pi_sh (v + 32)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 16) 8 (v + 32) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 24) 8 (pi_sh (v + 24)) ->
  val_mem SEGS (mrestrict (w_H W) mem) (spZ regs + 32) 8 (v + 24) ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 24) 8 kids ->
  val_mem SEGS (mrestrict (w_H W) mem) (v + 40) 8 n ->
  st_ok_pi SEGS VAL (PV_E regs kids n) ss_val
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PV_K_VAL)) mem (seg_rom SEGS))).
Proof.
intros W regs mem q v kids n R9 R19 R8 R20 R22 R24 R26 R27 R25 R23 Hsp1 Hsp2 Hsp16 Hq1 Hq2 Hq8 Hv1 Hv2 Hv8 Hvs
  Hk1 Hk16 Hn M0 M8 M16 M24 M32 Mk Mn.
set (E := PV_E regs kids n).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs [Z_to_bv 64 kids; Z_to_bv 64 n]) k)
  by (intros k Hk; subst E; unfold PV_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = Z_to_bv 64 q)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 kids) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k z, ew E k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some k) = z).
{ intros k z Hk Hz. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hz. }
rewrite restrict_mkst_fx. unfold ss_val. apply pa_entry_st_ok_full.
- unfold pv_regs.
  repeat (apply regs_ok_pin; [ | intros X; discriminate X | ]); [apply regs_ok_Eimg_Ereg | ..].
  + rewrite R8. cbn [sv_denot]. rewrite E9, unsigned_lit_small by lia. reflexivity.
  + rewrite R20. cbn [sv_denot]. rewrite E9, unsigned_lit_small by lia. reflexivity.
  + rewrite R22. cbn [sv_denot]. rewrite E19, unsigned_lit_small by lia. reflexivity.
  + rewrite R24. rewrite (pv_denot_shx E 19 v 40 E19) by lia. reflexivity.
  + rewrite R26. reflexivity.
  + rewrite R27. rewrite <- (Z.add_0_r q) at 1. rewrite (pv_denot_shx E 9 q 0 E9) by lia. reflexivity.
  + rewrite R25. rewrite (pv_denot_shx E 9 q 16 E9) by lia. reflexivity.
  + rewrite R23. rewrite (pv_denot_shx E 9 q 8 E9) by lia. reflexivity.
- vm_compute. reflexivity.
- unfold pv_val_regions, pv_frame_region, pv_node_region.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (spZ regs) 0 8 (SLit (2 ^ 60)) (2 ^ 60)); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact M0.
    * apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 _ (pi_sh (v + 32)));
        [exact (pv_denot_shx E 19 v 32 E19 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold pi_sh, SHADOW_OFF; cbn;
         pose proof (Z.div_pos (v + 32) 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound (v + 32) 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia
        | cbn; lia | exact M8].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 16 8 _ (v + 32));
        [cbn [sv_denot]; rewrite E19, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact M16].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 24 8 _ (pi_sh (v + 24)));
        [exact (pv_denot_shx E 19 v 24 E19 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold pi_sh, SHADOW_OFF; cbn;
         pose proof (Z.div_pos (v + 24) 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_le_upper_bound (v + 24) 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia
        | cbn; lia | exact M24].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 32 8 _ (v + 24));
        [cbn [sv_denot]; rewrite E19, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact M32].
  + rewrite (VB 19%nat v E19) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ v 24 8 (SOff 32 0) kids); [rewrite pv_denot0, E32; reflexivity | cbn; lia | cbn; lia | exact Mk].
    * apply (chunk_ok_val SEGS E _ v 40 8 (SOff 33 0) n); [rewrite pv_denot0, E33; reflexivity | cbn; lia | cbn; lia | exact Mn].
- apply pairwise_disjoint_of_extents. unfold pv_val_regions, pv_frame_region, pv_node_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, E19, unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [pv_val_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E9, E19, E32, E33, !unsigned_lit_small by lia.
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

End e.

(* ---- address arithmetic (FuzzStrdupB.v sd_hull_sub / sd_shadow_low / sd_hull_low, copied: that file is not built
   on this base) ---- *)
Lemma pv_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma pv_shadow_low : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 46.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma pv_hull_low : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 46.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
pose proof (Z.div_pos (SHADOW_OFF + x / 8) 8 ltac:(unfold SHADOW_OFF; lia) ltac:(lia)) as P2.
assert (P3 : (x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (P4 : (SHADOW_OFF + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; unfold SHADOW_OFF; lia).
lia.
Qed.
(* the shadow byte, and the shadow hull, of any byte below 2 ^ 47 lies outside every application range *)
Section h. Context {rc : YM05.RunCeil}.
Lemma pv_shadow_app : forall p len x, in_app p len -> 0 <= x < 2 ^ 47 -> ~ (p <= shadow_of_addr SHADOW_OFF x < p + len).
Proof.
intros p len x Happ Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma pv_hull_app : forall p len x n s, in_app p len -> 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> ~ (p <= s < p + len).
Proof.
intros p len x n s Happ Hx Hn Hxn Hs. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as P1.
assert (P3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *. lia.
Qed.
End h.

(* a run whose regions have no writable window leaves the restricted memory pointwise unchanged *)
Lemma pv_frame_nowin : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' HF Hw x. apply HF. intros (r & Hin & Hr).
rewrite forallb_forall in Hw. specialize (Hw r Hin). apply Z.leb_le in Hw. lia.
Qed.

(* a register of a symbolic state read off without normalising its value (PItems_head.v prregx, both state forms) *)
Ltac pv_prregx HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.

(* the kid slot as the run leaves it in a0: kids + 56 n, no wrap (kids <= 2 ^ 47, n <= 2 ^ 54) *)
Lemma pv_U_slot : forall E kids n, ew E 32 = Z_to_bv 64 kids -> ew E 33 = Z_to_bv 64 n ->
  0 <= kids <= 2 ^ 47 -> 0 <= n <= 2 ^ 54 ->
  U E (SAlu ALU_ADD (SOff 32 0) (SMd M_MUL (SOff 33 0) (SLit 56))) = kids + 56 * n.
Proof.
intros E kids n H32 H33 Hk Hn.
rewrite U_SAlu, U_SMd, (U_atom E 32 kids H32), (U_atom E 33 n H33), U_lit by lia.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
rewrite (Z.mod_small (n * 56)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* the signed-overflow test of 56 n as the run leaves it (snez (mulh n 56 xor srai (56 n) 63)): 0, since
   0 <= 56 n < 2 ^ 63 makes both the high product word and the sign word 0 *)
Lemma pv_U_mulh : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 54 ->
  U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_XOR (SMd M_MULH (SOff 33 0) (SLit 56))
    (SAlu ALU_SRA (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 63)))) = 0.
Proof.
intros E n H33 Hn.
assert (U1 : U E (SMd M_MULH (SOff 33 0) (SLit 56)) = 0).
{ rewrite U_SMd, (U_atom E 33 n H33), U_lit by lia. cbn [zmd_raw].
  rewrite (swrap64_id n), (swrap64_id 56) by (unfold half64; lia). change (Z.of_N 64) with 64.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
assert (U2 : U E (SAlu ALU_SRA (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 63)) = 0).
{ rewrite U_SAlu, U_SMd, (U_atom E 33 n H33), !U_lit by lia. cbn [zalu_raw zmd_raw].
  rewrite (zcanon_id (n * 56)) by (unfold M64; lia). rewrite (swrap64_id (n * 56)) by (unfold half64; lia).
  change (Z.land 63 63) with 63. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
rewrite U_SAlu, U_SAlu, U1, U2, U_lit by lia. reflexivity.
Qed.

(* a run over regions without a writable window writes nothing: its write premise is vacuous *)
Ltac pv_awr :=
  lazymatch goal with |- awr_ok _ ?rs _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Section w. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Variable d : nat.

Lemma pv_v_place : forall ly S Hp W mem md Lam peak cnt fail ran most own (regs0 : bvmap 5 word) e v,
  ARx ly S Hp W mem md -> prh_ledger (L := B_prog_listing) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs0 e v 56 -> YM05.alloc_ceiling <= spZ regs0 -> spZ regs0 + e <= 2 ^ 47 ->
  4096 <= v /\ v + 56 <= 2 ^ 47 /\ (v + 56 <= YM05.alloc_ceiling \/ spZ regs0 <= v) /\
  (v + 56 <= SHADOW_OFF \/ kHighMemBeg <= v).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v HAR HLED Hat Hsp He.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
assert (HB : forall b m, In (b, m) (ablocks B ly S) -> b <= v -> v + 56 <= b + req_size m ->
  4096 <= v /\ v + 56 <= 2 ^ 47 /\ (v + 56 <= YM05.alloc_ceiling \/ spZ regs0 <= v) /\
  (v + 56 <= SHADOW_OFF \/ kHighMemBeg <= v)).
{ intros b m Hin H1 H2. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hin) as (_ & H4096 & Hc & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
destruct Hat as [(a & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- pose proof HLED as HF. apply prh_ledger_blocks in HF. pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk & Hblk & _).
  cbn [fst snd] in Hk, Hblk. apply (HB _ _ Hblk); [lia|]. unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
- apply (HB _ _ Hin); [lia|]. unfold req_size. destruct (Z.eqb_spec m 0); lia.
- destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
- unfold kHighMemBeg, SHADOW_OFF. lia.
Qed.

Hypothesis HSH : pi_hshadow_law (L := B_prog_listing) (PA := PA) B ARx cf_head.
Hypothesis AMEMSET : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS B ARx OSet (pa_sigma (PAImg := PA) AS___asan_memset).
Hypothesis HW : prh_head_wide.

Lemma pv_pc_val : pa_val (PAImg := PA) A_TEXT + PI_AT (L := B_prog_listing) (PI := PA) PI_O_VAL = BASE + PV_K_VAL.
Proof. vm_compute. reflexivity. Qed.

Lemma pv_stk_lo : 144 + ESTACK <= STK_parse_items d.
Proof.
unfold STK_parse_items. pose proof (Nat2Z.is_nonneg (PjGrammar.MAXD - d)).
assert (EL : LEAF_pv_pi = 16560) by (vm_compute; reflexivity). rewrite EL.
change (PRH_Base.pi_frame F_parse_items) with 144. change (PRH_Base.pi_frame F_parse_value) with 176.
change ESTACK with 4096. lia.
Qed.

(* the entry facts this block uses, read off pi_ent by type *)
Lemma pv_ent_facts : forall fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p kr tb v (o : bool)
  CTX0 CW,
  pi_ent (L := B_prog_listing) (PA := PA) B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d
    kr tb v o CTX0 CW ->
  (getr regs0 3 = w64 (as_gp B)) /\ (getr regs0 4 = w64 (as_tp B)) /\
  (spZ regs0 <= q) /\ (q + 24 <= spZ regs0 + e) /\
  prhReader_home (L := B_prog_listing) (PA := PA) B ly S Hp Lam text len /\
  prh_ledger (L := B_prog_listing) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own.
Proof.
intros fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p kr tb v o CTX0 CW H.
unfold pi_ent, rd_pre in H. repeat match goal with X : _ /\ _ |- _ => destruct X end.
refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); assumption.
Qed.

(* ---- the image and the statics (lib/A/Prog/S1ImgA.v's image-free checkers and lib/B/Prog/S1ImgB.v pst_in_img_B,
   copied, not Required: S1ImgB Requires S1ImgA, which Requires lib/A/PAImg_prog.v and so puts image A's PAImg
   instance into instance resolution) ---- *)
Definition pv_in_img_b (a : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS.
Definition pv_pst_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.
Lemma pv_pst_allb_sound : forall f P a, pv_pst_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold pv_pst_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.
Lemma pv_pst_in_img : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> in_img SEGS a.
Proof.
intros a Ha. assert (Hb : pv_in_img_b a = true) by (refine (pv_pst_allb_sound _ _ a _ Ha); vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hs | lia].
Qed.
(* a read-only byte is an image byte (FuzzStrdupB.v sd_ro_img, copied: that file has no .vo on this base) *)
Lemma pv_ro_img : forall a, in_roP SEGS (pa_relro_lo (PAImg := PA)) (pa_relro_hi (PAImg := PA)) a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

Lemma pv_req_ge : forall z, 0 <= z -> z <= req_size z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.

(* a byte inside a block of the entry state, or inside the image, is not a byte of a block the call allocated *)
Lemma pv_home_apart : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own lyc Sc Hpc (Wc : world SEGS)
  memc mdc D0 p0 n0 bK nK,
  ARx lyc Sc Hpc Wc memc mdc ->
  prh_ledger (L := B_prog_listing) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  Permutation (ablocks B lyc Sc) (prhReader_ab D0 ++ ablocks B ly S) ->
  In (bK, nK) (ablocks B lyc Sc) -> ~ In (bK, nK) (ablocks B ly S) ->
  prhReader_home (L := B_prog_listing) (PA := PA) B ly S Hp Lam p0 n0 ->
  forall a, p0 <= a < p0 + n0 -> ~ (bK <= a < bK + req_size nK).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own lyc Sc Hpc Wc memc mdc D0 p0 n0 bK nK HAR HLg HP HinK HnK Hh a Ha
  HaK.
pose proof (@cf_head_nonneg cp) as Hh0.
assert (Hold : forall b m, In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> False).
{ intros b m Hin Hr.
  assert (Hin' : In (b, m) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hin).
  assert (Hne : (b, m) <> (bK, nK)) by (intros Ee; rewrite Ee in Hin; exact (HnK Hin)).
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hin' HinK Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (Himg : in_img SEGS a -> False) by (intros Hi; exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ a HAR HinK HaK Hi)).
unfold prhReader_home, kept_at, kept_img in Hh.
destruct Hh as [[(b & m & Hin & H1 & H2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & H1 & H2)].
- destruct HLg as (_ & _ & HF & _). pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hab & _).
  cbn [fst snd] in Hm0, Hab.
  apply (Hold _ _ Hab).
  assert (Hmh : 0 <= m + cf_head) by lia.
  pose proof (pv_req_ge (m + cf_head) Hmh).
  lia.
- apply Himg. destruct (Hro a Ha) as (Hr & _). exact (pv_ro_img a Hr).
- apply Himg. destruct (Hro a Ha) as (Hr & _). exact (pv_ro_img a Hr).
- apply (Hold b m Hin). assert (Hm : 0 <= m \/ m < 0) by lia.
  destruct Hm as [Hm | Hm]; [pose proof (pv_req_ge m Hm); lia | lia].
Qed.

(* the ledger reads only the statics and the head words *)
Lemma pv_ledger_kept : forall ly S Hp (W : world SEGS) mem mem' Lam peak cnt fail ran most own,
  prh_ledger (L := B_prog_listing) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
     mbyte SEGS (mrestrict (w_H W) mem') a = mbyte SEGS (mrestrict (w_H W) mem) a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     mbyte SEGS (mrestrict (w_H W) mem') (a - cf_head + i) = mbyte SEGS (mrestrict (w_H W) mem) (a - cf_head + i)) ->
  prh_ledger (L := B_prog_listing) (PA := PA) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' Lam peak cnt fail ran most own (HG & HND & HB & HP) Hs Hh.
split; [|split; [exact HND|split; [|exact HP]]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & M6) & (G7 & M7) & GR).
  assert (VK : forall a n w, (forall kk, (kk < n)%nat -> Exists (in_zr (a + Z.of_nat kk)) (@prh_pst prh_img_B)) ->
    val_mem SEGS (mrestrict (w_H W) mem) a n w -> val_mem SEGS (mrestrict (w_H W) mem') a n w).
  { intros a n w Hin Hv kk Hk. rewrite (Hs _ (Hin kk Hk)). exact (Hv kk Hk). }
  refine (conj (VK _ _ _ _ G1) (conj (VK _ _ _ _ G2) (conj (VK _ _ _ _ G3) (conj (VK _ _ _ _ G4)
    (conj (VK _ _ _ _ G5) (conj (conj (VK _ _ _ _ G6) M6) (conj (conj (VK _ _ _ _ G7) M7) GR))))))).
  all: intros kk Hk; unfold prh_pst;
    repeat first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl].
- rewrite Forall_forall in HB |- *. intros [a k] Hin. destruct (HB (a, k) Hin) as (K0 & Kin & Khp & Kal & Kv).
  cbn [fst snd] in *. refine (conj K0 (conj Kin (conj Khp (conj Kal _)))).
  intros kk Hk. rewrite (Hh a k (Z.of_nat kk) Hin) by lia. exact (Kv kk Hk).
Qed.

(* stdpp's NoDup (base.v), the one prh_ledger states: a prefix of a NoDup list is NoDup *)
Lemma pv_nodup_app_l : forall {X : Type} (l1 l2 : list X), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
intros X l1 l2 H. induction l1 as [|a l1 IH]; [constructor|].
inversion H as [|a' l' Hn Hd]; subst. constructor; [|exact (IH Hd)].
intros Hi. apply Hn. apply list_elem_of_In in Hi. apply list_elem_of_In. apply in_or_app. left. exact Hi.
Qed.

(* THE DATA ACROSS THE MEMSET: pv_vdata at any memory that keeps every byte outside the kid slot and the ESTACK window
   below sp, and keeps the present bytes present. What pv_vdata reads: q's 24 bytes and the frame side (above sp), the
   text (in a block of the entry state or in the image), the node v (apart from the slot block by pj_apartR), the
   shadow of these (below 2 ^ 46), the statics (image bytes) and the head words of the ledger (each below its own
   block's user range, cf_head >= 8), the first n slots of the kids block, the key slots and every block of Di / Dk
   (blocks of the current ledger other than the kids block). *)
Lemma pv_vdata_kept : forall fx0 ly S Hp (W : world SEGS) mem ch CTX regs0 e q v (o : bool) text len tb p Lam
  peak cnt fail ran most own kr lyc Sc Hpc (Wc : world SEGS) memc memc' mdc N (f n cap : nat) acc kids keys Di nm Dk pc
  ok0 tr0 D0 Lamc peakc cntc failc ranc CTX0 CW sp,
  ARx lyc Sc Hpc Wc memc mdc ->
  pi_ent (L := B_prog_listing) (PA := PA) B fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p d
    kr tb v o CTX0 CW ->
  pv_vdata (L := B_prog_listing) (PA := PA) B regs0 e q v o text len tb p d Lam peak cnt fail ran most own S ly lyc Sc Hpc
    Wc memc N f n cap acc kids keys Di nm Dk pc ok0 tr0 D0 Lamc peakc cntc failc ranc ->
  YM05.alloc_ceiling + ESTACK <= sp -> sp <= spZ regs0 -> spZ regs0 + e <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pv_slot kids n <= a < pv_slot kids n + 56) -> ~ (sp - ESTACK <= a < sp) ->
     aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
  pv_vdata (L := B_prog_listing) (PA := PA) B regs0 e q v o text len tb p d Lam peak cnt fail ran most own S ly lyc Sc Hpc
    Wc memc' N f n cap acc kids keys Di nm Dk pc ok0 tr0 D0 Lamc peakc cntc failc ranc.
Proof.
intros fx0 ly S Hp W mem ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc memc' mdc
  N f n cap acc kids keys Di nm Dk pc ok0 tr0 D0 Lamc peakc cntc failc ranc CTX0 CW sp HAR HENT HV
  Hsp1 Hsp2 He47 HK HGR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HW as HW8. unfold prh_head_wide in HW8. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (pv_ent_facts fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p kr tb v o CTX0 CW HENT)
  as (_ & _ & Hsq & Hqs & Hhome0 & HLED0).
destruct HV as (HCUR & HNb & Hncap & HCONT & HDEP & HAPART & HKEY & HD0 & HFUEL & HEQ & HLED & HMOVE & HPOSB & HLIVE &
  HBB & HLOK & HLSUM & HROOM & HGRT & Hcapn & HNC & af & lk & HFO & HDk & HFLE).
destruct HCUR as (HIN & Hqra & Hsrc & Hhome & Hat & Hvra & HLEDc & Hcntc).
pose proof HCONT as (HHDR & Hnacc & Hncap' & Hcap54 & Hslots & Hkeys0 & HNDi & HDiap & HITEMS).
destruct Hslots as [(Hc0 & _ & _) | (Hcpos & Hkblk & Hkyblk)]; [lia|].
(* the ledger's facts by name (PRH_Base.v ledger_proj), not by position *)
pose proof HLEDc as HGc. apply prh_ledger_glob in HGc.
pose proof HLEDc as HNDL. apply prh_ledger_nodup in HNDL.
pose proof HLEDc as HFA. apply prh_ledger_blocks in HFA.
pose proof HLEDc as HPHp. apply prh_ledger_heads in HPHp.
pose proof HMOVE as (HMnew & HMperm & _ & _).
pose proof HLED as (_ & _ & _ & HPL & _).
(* every block of the current ledger: its allocator block, below the ceiling *)
assert (HBL : forall b k, In (b, k) Lamc -> 0 <= k /\ In (b - cf_head, k + cf_head) (ablocks B lyc Sc) /\
  4096 <= b - cf_head /\ b + k <= YM05.alloc_ceiling).
{ intros b k Hin. pose proof (proj1 (Forall_forall _ _) HFA (b, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4 & Hc & _).
  assert (Hkh : 0 <= k + cf_head) by lia. pose proof (pv_req_ge _ Hkh).
  split; [lia|]. split; [exact Hab|]. lia. }
destruct (HBL kids (56 * Z.of_nat cap) Hkblk) as (Hk0 & Hkab & Hk4096 & Hkceil).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hkab) as (_ & _ & _ & Hkapp & _).
assert (Hreqk : req_size (56 * Z.of_nat cap + cf_head) = 56 * Z.of_nat cap + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (56 * Z.of_nat cap + cf_head) 0); lia).
rewrite Hreqk in Hkapp.
assert (Hks : In (kids, 56 * Z.of_nat cap) (pi_sblk o kids keys cap)).
{ unfold pi_sblk. apply in_or_app. left.
  unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia. left. reflexivity. }
assert (Hkd : In (kids, 56 * Z.of_nat cap) D0)
  by (apply (Permutation_in _ (Permutation_sym HD0)); apply in_or_app; left; exact Hks).
pose proof (HMnew _ _ Hkd) as HKnew.
(* a block of the current ledger other than the kids block lies apart from it, its head word included *)
assert (G1 : forall b k a, In (b, k) Lamc -> b <> kids -> b - cf_head <= a < b + k ->
  ~ (kids - cf_head <= a < kids + 56 * Z.of_nat cap)).
{ intros b k a Hin Hne Ha Hka. destruct (HBL b k Hin) as (Hk & Hab & _ & _).
  assert (Hne' : (b - cf_head, k + cf_head) <> (kids - cf_head, 56 * Z.of_nat cap + cf_head))
    by (intros Ee; injection Ee as E1 E2; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hkab Hne') as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreqk in Hd.
  assert (Hkh : 0 <= k + cf_head) by lia. pose proof (pv_req_ge _ Hkh). lia. }
(* the parts of D0 other than the kids block are blocks of the current ledger other than the kids block *)
assert (HP0 : Permutation D0 ((kids, 56 * Z.of_nat cap) :: keys_blkR (if o then 6 else 5) keys (Z.of_nat cap) ++ Di ++ Dk)).
{ eapply perm_trans; [exact HD0|]. unfold pi_sblk, kids_blkR. rewrite (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia.
  cbn [app]. apply Permutation_refl. }
assert (HDn : forall b, In b (keys_blkR (if o then 6 else 5) keys (Z.of_nat cap) ++ Di ++ Dk) -> fst b <> kids /\ In b Lamc).
{ intros b Hb. split.
  - assert (HN : NoDup (map fst ((kids, 56 * Z.of_nat cap) :: keys_blkR (if o then 6 else 5) keys (Z.of_nat cap) ++ Di ++ Dk))).
    { assert (HN1 : NoDup (map fst (D0 ++ Lam))) by (rewrite <- (Permutation_map fst HPL); exact HNDL).
      rewrite map_app in HN1. apply pv_nodup_app_l in HN1.
      rewrite <- (Permutation_map fst HP0). exact HN1. }
    cbn [map fst] in HN. inversion HN as [|x0 l0 HN' HN'']. intros Ee. apply HN'. cbn [fst] in Ee. rewrite <- Ee.
    apply list_elem_of_In. apply in_map. exact Hb.
  - apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left.
    apply (Permutation_in _ (Permutation_sym HP0)). right. exact Hb. }
(* the bytes kept *)
set (X := fun a => 0 <= a < 2 ^ 64 /\ ~ (pv_slot kids n <= a < pv_slot kids n + 56) /\ ~ (sp - ESTACK <= a < sp)).
assert (AV : forall a, X a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a)
  by (intros a (H1 & H2 & H3); exact (HK a H1 H2 H3)).
assert (AG : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') X).
{ intros x Hx. split; [apply (mbyte_of_aview SEGS); exact (AV x Hx) | intros Hw; exact (wview_grows SEGS _ _ _ HGR Hw)]. }
assert (AGs : forall Y : Z -> Prop, (forall x, Y x -> X x) ->
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') Y)
  by (intros Y HY x Hx; exact (AG x (HY x Hx))).
assert (MB : forall a, X a -> mbyte SEGS (mrestrict (w_H Wc) memc') a = mbyte SEGS (mrestrict (w_H Wc) memc) a)
  by (intros a Ha; exact (proj1 (AG a Ha))).
assert (XL : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (pv_slot kids n <= a < pv_slot kids n + 56) -> X a)
  by (intros a Ha Hs; unfold X; lia).
assert (XK : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (kids - cf_head <= a < kids + 56 * Z.of_nat cap) -> X a)
  by (intros a Ha Hk; apply XL; [lia | unfold pv_slot; lia]).
assert (XH : forall a, sp <= a < 2 ^ 64 -> X a) by (intros a Ha; unfold X, pv_slot; lia).
assert (XN : forall a, kids <= a < kids + 56 * Z.of_nat n -> X a) by (intros a Ha; apply XL; unfold pv_slot; lia).
assert (XS : forall x, 0 <= x < 2 ^ 47 -> X (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (pv_shadow_low x Hx). pose proof (pv_shadow_app _ _ x Hkapp Hx). apply XK; lia. }
assert (XLam : forall b k a, In (b, k) Lamc -> b <> kids -> b - cf_head <= a < b + k -> X a).
{ intros b k a Hin Hne Ha. destruct (HBL b k Hin) as (_ & _ & H4 & Hc). apply XK; [lia | exact (G1 b k a Hin Hne Ha)]. }
assert (XD : forall b x, In b (keys_blkR (if o then 6 else 5) keys (Z.of_nat cap) ++ Di ++ Dk) -> pj_holdsR b x -> X x).
{ intros [b k] x Hb Hx. destruct (HDn _ Hb) as [Hne Hin]. cbn [fst] in Hne. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  apply (XLam b k x Hin Hne). lia. }
pose proof Hsrc as (Hby & Ht4096 & Htceil & Htamr & Htra & Hthull).
pose proof HIN as (Mp & Mend & Mdep & Hqrw & Hq8 & Htx0 & Htx62 & Hpcr & Hlen & Hgarr & Hqtx & Hdep).
assert (XT : forall a, text <= a < text + len -> X a).
{ intros a Ha. apply XK; [lia|].
  pose proof (pv_home_apart ly S Hp W mem Lam peak cnt fail ran most own lyc Sc Hpc Wc memc mdc D0 text len _ _ HAR HLED0
    HMperm Hkab HKnew Hhome0 a Ha) as Hx.
  rewrite Hreqk in Hx. lia. }
assert (Hacs : YM05.alloc_ceiling <= spZ regs0) by lia.
destruct (pv_v_place lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own regs0 e v HAR HLEDc Hat Hacs He47)
  as (Hv4096 & Hv47 & Hvsp & _).
assert (XV : forall a, v <= a < v + 56 -> X a).
{ intros a Ha. destruct Hvsp as [Hv1 | Hv1]; [| apply XH; lia].
  apply XL; [lia|]. intros Hs. apply (HAPART (kids, 56 * Z.of_nat cap) a Hks); [|lia].
  unfold pj_holdsR. cbn [fst snd]. unfold pv_slot in Hs. lia. }
assert (XQ : forall a, q <= a < q + 24 -> X a) by (intros a Ha; apply XH; lia).
(* THE BATCH KIT'S INVARIANTS across the memset: pi_cont's read bytes (PItems_value_model.pvm_cont_ufoot: the header v .. v + 56,
   the slots i < n, the key slots i < n, the blocks of Di) are all kept bytes, so pi_ncaps and pi_forder move by
   PItems_value_model.pvm_ncaps_frame / pvm_forder_frame (the ledger, and so lblk, is the same) *)
assert (AGu : pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc')
  (PItems_value_model.pvm_cont_ufoot o v kids keys n Di)).
{ apply AGs. intros x [Hx | [(i & Hi & Hx) | [(Ho & i & Hi & Hx) | (b & Hb & Hx)]]].
  - exact (XV x Hx).
  - apply XN. clear - Hi Hx. lia.
  - subst o.
    assert (Hkyb : In (keys, 8 * Z.of_nat cap) (keys_blkR (if true then 6 else 5) keys (Z.of_nat cap) ++ Di ++ Dk)).
    { apply in_or_app. left. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia. cbn. left. reflexivity. }
    apply (XD _ x Hkyb). unfold pj_holdsR. cbn [fst snd]. clear - Hi Hx Hncap. lia.
  - apply (XD b x); [apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hx]. }
pose proof (PItems_value_model.pvm_ncaps_frame (w_H Wc) memc _ _ o v kids keys n cap acc Di HCONT HNC AGu) as HNC'.
pose proof (PItems_value_model.pvm_forder_frame _ _ _ _ o v kids keys n Di acc af HFO (fun x k Hx => Hx) AGu) as HFO'.
refine (conj _ (conj HNb (conj Hncap (conj _ (conj HDEP (conj HAPART (conj _ (conj HD0 (conj HFUEL (conj HEQ (conj HLED
  (conj HMOVE (conj HPOSB (conj HLIVE (conj HBB (conj HLOK (conj HLSUM (conj HROOM (conj HGRT (conj Hcapn (conj HNC'
  (ex_intro _ af (ex_intro _ lk (conj HFO' (conj HDk HFLE))))))))))))))))))))))))).
- (* pi_cur *)
  refine (conj _ (conj _ (conj _ (conj Hhome (conj Hat (conj _ (conj _ Hcntc))))))).
  + refine (conj _ (conj _ (conj _ (conj _ (conj Hq8 (conj Htx0 (conj Htx62 (conj Hpcr (conj Hlen (conj _
      (conj Hqtx Hdep))))))))))).
    * apply (pj_valR_frame SEGS _ _ _ _ _ Mp). intros x Hx. apply MB. apply XQ. cbn in Hx. lia.
    * apply (pj_valR_frame SEGS _ _ _ _ _ Mend). intros x Hx. apply MB. apply XQ. cbn in Hx. lia.
    * apply (pj_valR_frame SEGS _ _ _ _ _ Mdep). intros x Hx. apply MB. apply XQ. cbn in Hx. lia.
    * intros x Hx. exact (proj2 (AG x (XQ x Hx)) (Hqrw x Hx)).
    * apply (garr8R_frame SEGS _ _ _ _ Hgarr). intros x Hx. apply MB. apply XT. lia.
  + eapply range_addressable_agree; [|exact Hqra]. intros x Hx. apply AV. apply XS. lia.
  + refine (conj _ (conj Ht4096 (conj Htceil (conj Htamr (conj _ _))))).
    * unfold bytes_at in *. apply (garr8R_frame SEGS _ _ _ _ Hby). intros x Hx. apply MB. apply XT. lia.
    * eapply range_addressable_agree; [|exact Htra]. intros x Hx. apply AV. apply XS. lia.
    * intros Hn0 s Hs. rewrite AV; [exact (Hthull Hn0 s Hs)|].
      assert (Ht0 : 0 <= text) by lia. assert (Ht47 : text + Z.of_nat (length tb) <= 2 ^ 47) by lia.
      pose proof (pv_hull_low text (Z.of_nat (length tb)) s Ht0 Hn0 Ht47 Hs).
      pose proof (pv_hull_app _ _ text (Z.of_nat (length tb)) s Hkapp Ht0 Hn0 Ht47 Hs). apply XK; lia.
  + eapply range_addressable_agree; [|exact Hvra]. intros x Hx. apply AV. apply XS. lia.
  + apply (pv_ledger_kept _ _ _ _ _ _ _ _ _ _ _ _ _ HLEDc).
    * intros a Ha. apply MB. pose proof (pv_pst_in_img a Ha) as Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hl.
      apply XK; [lia|]. intros Hka.
      assert (Hka' : kids - cf_head <= a < kids - cf_head + req_size (56 * Z.of_nat cap + cf_head)) by (rewrite Hreqk; lia).
      exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ a HAR Hkab Hka' Hi).
    * intros a k i Hin Hi. apply MB. destruct (HBL a k Hin) as (Hk & _ & H4 & Hc).
      destruct (Z.eq_dec a kids) as [-> | Hne].
      -- apply XL; [lia | unfold pv_slot; lia].
      -- apply (XLam a k _ Hin Hne). lia.
- (* pi_cont *)
  refine (conj _ (conj Hnacc (conj Hncap' (conj Hcap54 (conj (or_intror (conj Hcpos (conj Hkblk Hkyblk)))
    (conj Hkeys0 (conj HNDi (conj HDiap _)))))))).
  + apply (pj_hdrR_frame SEGS _ _ _ _ _ _ _ _ _ _ HHDR). apply AGs. intros x Hx. exact (XV x Hx).
  + destruct o.
    * apply (pj_memsR_mono SEGS _ _ _ _ _ acc kids keys Di HITEMS).
      intros i nm0 u x k D1 Hil Hxk Hinc Hx Hcs HP.
      pose proof (pj_nth_lenR acc i (nm0, u) Hil) as Hlt.
      assert (Hkyb : In (keys, 8 * Z.of_nat cap) (keys_blkR (if true then 6 else 5) keys (Z.of_nat cap) ++ Di ++ Dk)).
      { apply in_or_app. left. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia. cbn. left. reflexivity. }
      split; [|split].
      -- apply (rd_u64_frame SEGS _ _ _ _ Hx). intros y Hy. apply MB. apply (XD _ y Hkyb).
         unfold pj_holdsR. cbn [fst snd]. lia.
      -- apply (pj_cstrR_frame SEGS _ _ _ _ _ _ Hcs). intros y Hy. apply MB. apply (XD (x, k) y).
         ++ apply in_or_app. right. apply in_or_app. left. exact Hxk.
         ++ unfold pj_holdsR. cbn [fst snd]. lia.
      -- apply (pj_nodeR_frame SEGS u _ _ _ _ _ HP). apply AGs. intros y [Hy | (b & Hb & Hy)].
         ++ apply XN. lia.
         ++ apply (XD b y); [apply in_or_app; right; apply in_or_app; left; exact (Hinc b Hb) | exact Hy].
    * apply (pj_itemsR_mono _ _ (map snd acc) kids Di HITEMS).
      intros i u D1 Hil Hinc HP. pose proof (pj_nth_lenR _ i u Hil) as Hlt. rewrite length_map in Hlt.
      apply (pj_nodeR_frame SEGS u _ _ _ _ _ HP). apply AGs. intros y [Hy | (b & Hb & Hy)].
      ++ apply XN. lia.
      ++ apply (XD b y); [apply in_or_app; right; apply in_or_app; left; exact (Hinc b Hb) | exact Hy].
- (* pi_key *)
  destruct o; cbn [pi_key] in HKEY |- *; [|exact HKEY].
  destruct HKEY as (x & kx & -> & Hx & Hcs). exists x, kx. split; [reflexivity|]. split.
  + assert (Hkyb : In (keys, 8 * Z.of_nat cap) (keys_blkR (if true then 6 else 5) keys (Z.of_nat cap) ++ Di ++ [(x, kx)])).
    { apply in_or_app. left. unfold keys_blkR. rewrite (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia. cbn. left. reflexivity. }
    apply (rd_u64_frame SEGS _ _ _ _ Hx). intros y Hy. apply MB. apply (XD _ y Hkyb).
    unfold pj_holdsR. cbn [fst snd]. lia.
  + apply (pj_cstrR_frame SEGS _ _ _ _ _ _ Hcs). intros y Hy. apply MB. apply (XD (x, kx) y).
    * apply in_or_app. right. apply in_or_app. right. left. reflexivity.
    * unfold pj_holdsR. cbn [fst snd]. lia.
Qed.

(* a call that keeps every present byte present grows the restricted memory *)
Lemma pv_grows_of_present : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Ex; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)) by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Ex | exists b; exact Em]).
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

(* 56 bytes that read 0 are a zeroed node *)
Lemma pv_zero_of_aview : forall (W : world SEGS) m dd,
  (forall i, 0 <= i < 56 -> aview SEGS (w_H W) m (dd + i) = Some 0) -> pj_zeroR SEGS (mrestrict (w_H W) m) dd.
Proof.
intros W m dd H j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. split; [|lia].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
assert (Hj' : 0 <= Z.of_nat j < 56) by lia. specialize (H (Z.of_nat j) Hj'). unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) m) (dd + Z.of_nat j)) as [b|] eqn:Eb; cbn [option_map] in H; [|discriminate H].
injection H as Hb. f_equal. apply bv_eq. rewrite Hb. vm_compute. reflexivity.
Qed.

(* the frame image B's prologue built, and the frame cache, across a memory that keeps every byte above sp *)
Lemma pv_frame_kept : forall (regs0 regs regs' : bvmap 5 word) (W : world SEGS) mem (Wc : world SEGS) memc memc' e q v,
  pi_frame (L := B_prog_listing) (PA := PA) regs0 regs W mem Wc memc e q v ->
  pi_regs_body (L := B_prog_listing) (PA := PA) regs Wc memc v ->
  spZ regs' = spZ regs -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 22 = getr regs 22 -> getr regs' 24 = getr regs 24 -> spZ regs0 + e <= 2 ^ 64 ->
  (forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  pi_frame (L := B_prog_listing) (PA := PA) regs0 regs' W mem Wc memc' e q v /\
  pi_regs_body (L := B_prog_listing) (PA := PA) regs' Wc memc' v.
Proof.
intros regs0 regs regs' W mem Wc memc memc' e q v
  (Fsp & F3 & F4 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & Fw & Fra & Fe0 & Fe16)
  (B22 & B24 & M0 & M32 & M24 & M16 & M8) Hsp H3 H4 H22 H24 He HA.
unfold PI_FRAME in Fsp.
assert (VK : forall a w, spZ regs <= a -> a + 8 <= spZ regs + 144 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) a 8 w -> val_mem SEGS (mrestrict (w_H Wc) memc') a 8 w).
{ intros a w Ha1 Ha2 Hv. apply (pj_valR_frame SEGS _ _ _ _ _ Hv). intros x Hx. apply (mbyte_of_aview SEGS). apply HA.
  cbn in Hx. lia. }
unfold pi_frame, pi_regs_body. rewrite Hsp. split.
- split; [unfold PI_FRAME; lia|]. split; [rewrite H3; exact F3|]. split; [rewrite H4; exact F4|].
  split; [apply VK; [lia | lia | exact V1]|]. split; [apply VK; [lia | lia | exact V2]|].
  split; [apply VK; [lia | lia | exact V3]|]. split; [apply VK; [lia | lia | exact V4]|].
  split; [apply VK; [lia | lia | exact V5]|]. split; [apply VK; [lia | lia | exact V6]|].
  split; [apply VK; [lia | lia | exact V7]|]. split; [apply VK; [lia | lia | exact V8]|].
  split; [apply VK; [lia | lia | exact V9]|]. split; [apply VK; [lia | lia | exact V10]|].
  split; [apply VK; [lia | lia | exact V11]|]. split; [apply VK; [lia | lia | exact V12]|].
  split; [apply VK; [lia | lia | exact V13]|].
  split; [|exact (conj Fra (conj Fe0 Fe16))].
  intros a Ha Hn. rewrite HA by lia. exact (Fw a Ha Hn).
- split; [rewrite H22; exact B22|]. split; [rewrite H24; exact B24|].
  split; [apply VK; [lia | lia | exact M0]|]. split; [apply VK; [lia | lia | exact M32]|].
  split; [apply VK; [lia | lia | exact M24]|]. split; [apply VK; [lia | lia | exact M16]|].
  apply VK; [lia | lia | exact M8].
Qed.

Lemma pi_val_holds : forall CTX0 CW N,
  pv_call_spec (L := B_prog_listing) (PA := PA) (PL := PL_prog_B) B ARx SK d CTX0 CW N ->
  pi_val_spec (L := B_prog_listing) (PA := PA) (PL := PL_prog_B) B ARx SK d CTX0 CW N.
Proof.
intros CTX0 CW N HCALL. unfold pi_val_spec.
intros fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc memc
  mdc k regs WS0 HJw HWS HPRE.
destruct HPRE as (HFP & HENT & HMN & HFR & HREG & HRB & H21 & f & n & cap & acc & kids & keys & Di & nm & Dk & pc & ok0 &
  tr0 & D0 & Lamc & peakc & cntc & failc & ranc & HCUR & HNb & Hncap & HCONT & HDEP & HAPART & HKEY & HD0 & HFUEL & HEQ &
  HLED & HMOVE & HPOSB & HLIVE & HBB & HLOK & HLSUM & HROOM & HK1).
unfold pi_ajR in HJw. unfold pi_goalR. rewrite pv_pc_val.
(* THE BUDGETED JOURNAL at the walk's relation wle' pa_segs RZ_cf (PItems_pres.v pi_ajR): the runs and the memset (a
   runtime intrinsic: the allocator state stays Sc) take the empty-budget journal rebased at Sc's depot
   (YCbqGwild.ajournal_xw_rebaseR); HWD is the cover the step back before parse_value's block needs
   (YCbqGwild.ajournal_xw_unbase0R) *)
pose proof (ajxR_wild HJw) as HWD.
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJ.
clear HJw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@cf_head_nonneg cp) as Hh0.
pose proof pv_stk_lo as HSTKlo. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HREG as (R9 & R19 & R18 & R8 & R20 & R26 & R27 & R25 & R23).
pose proof HRB as (R22 & R24 & M0 & M32 & M24 & M16 & M8).
pose proof HFR as (Hsp & Hgp & Htp & V136 & V128 & V120 & V112 & V104 & V96 & V88 & V80 & V72 & V64 & V56 & V48 & V40 &
  Hwin & Hret0 & He0 & He16).
unfold PI_FRAME in Hsp.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & HstkJ & _).
pose proof HstkJ as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (pv_ent_facts fx0 ly S Hp W regs0 mem ch CTX Lam peak cnt fail ran most own e q text len p kr tb v o CTX0 CW HENT)
  as (Rgp0 & Rtp0 & Hsq & Hqs & Hhome0 & HLED0).
pose proof HCUR as (HIN & Hqra & Hsrc & Hhome & Hat & Hvra & HLEDc & Hcntc).
pose proof HIN as (Mp & Mend & Mdep & Hqrw & Hq8 & Htx0 & Htx62 & Hpcr & Hlen & Hgarr & Hqtx & Hdep).
pose proof HCONT as (HHDR & Hnacc & Hncap' & Hcap54 & Hslots & Hkeys0 & HNDi & HDiap & HITEMS).
destruct Hslots as [(Hc0 & _ & _) | (Hcpos & Hkblk & Hkyblk)]; [lia|].
pose proof HHDR as ((Hv8 & Hvrw) & Mty & Mnum & Mstr & (Rk & Mkids) & Mkeys & (Rn & Mn) & Mcap).
(* the kids block: a live harness block of the current ledger *)
pose proof HLEDc as HFA. apply prh_ledger_blocks in HFA.
pose proof (proj1 (Forall_forall _ _) HFA (kids, 56 * Z.of_nat cap) Hkblk) as (Hk0 & Hkab & Hkhp & Hk16 & _).
cbn [fst snd] in Hk0, Hkab, Hkhp, Hk16.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hkab) as (_ & Hk4096 & Hkceil & Hkapp & Hkpres & _).
assert (Hreqk : req_size (56 * Z.of_nat cap + cf_head) = 56 * Z.of_nat cap + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (56 * Z.of_nat cap + cf_head) 0); lia).
rewrite Hreqk in Hkceil, Hkapp, Hkpres.
(* the node's place *)
destruct (pv_v_place lyc Sc Hpc Wc memc mdc Lamc peakc cntc failc ranc most own regs0 e v HARc HLEDc Hat ltac:(lia)
  ltac:(lia))
  as (Hv4096 & Hv47 & Hvsp & Hvsh).
(* the symbolic state at PI_O_VAL *)
pose proof (pv_st_val (fx := fxc) Wc regs memc q v kids (Z.of_nat n) R9 R19 R8 R20 R22 R24 R26 R27 R25 R23
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(unfold in_app, kLowShadowBeg, ASAN_CEIL in *; lia) ltac:(lia) ltac:(lia) M0 M8 M16 M24 M32 Mkids Mn) as HS.
remember (PV_E regs kids (Z.of_nat n)) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs [Z_to_bv 64 kids; Z_to_bv 64 (Z.of_nat n)]) i)
  by (intros i Hi; rewrite HE; unfold PV_E; apply Eimg_low; exact Hi).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E9 : ew E 9 = Z_to_bv 64 q)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E19 : ew E 19 = Z_to_bv 64 v)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 kids) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 kids; Z_to_bv 64 (Z.of_nat n)]) E)
  by (rewrite HE; split; [intros i Hi; unfold PV_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE EL.
assert (SHOK : sh_ok SEGS PV_Bx pv_val_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, pv_val_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H Wc) memc E PV_Bx 19 v 56 v 0 56 Hvra);
  [unfold PV_Bx; rewrite U_lit by (unfold SHADOW_OFF; lia); reflexivity
  | rewrite (U_atom E 19 v E19) by lia; reflexivity | lia | lia | intros x Hx; unfold kHighMemBeg, SHADOW_OFF in *; lia]. }
pose (RUN := PI_RUNR (fx := fxc) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PA) B
  (@prh_pst prh_img_B) ARx LAWS).
pose (BR := paj_branchR (fx := fxc) (rc := rc) (L := B_prog_listing) (PI := PA) (wle' SEGS YGcfRehidePost.RZ_cf)).
unfold cfg_at. change (w64 (BASE + PV_K_VAL)) with (Z_to_bv 64 (BASE + PV_K_VAL)).
paj_run_tok_x RUN HS HJ SHOK PV_Bspan; [pv_awr|].
clear HG HEI0.
psrr_branch_tok RUN BR HS SHOK PV_Bspan.
{ (* 0x87d14 bltu (kids + 56 n) < kids, the pointer-overflow check of the slot: not taken, kids + 56 n < 2 ^ 61 *)
  rewrite branch_ltu_U, (pv_U_slot E kids (Z.of_nat n) E32 E33), (U_atom E 32 kids E32) in Hc by lia.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_tok_x RUN HS HJ SHOK PV_Bspan; [pv_awr|].
clear HG HEI0.
psrr_branch_tok RUN BR HS SHOK PV_Bspan.
{ (* 0x87d2c bnez (snez (mulh n 56 xor srai (56 n) 63)), the signed-overflow check of 56 n: not taken, 56 n < 2 ^ 63 *)
  rewrite branch_ne_U, (pv_U_mulh E (Z.of_nat n) E33), U_lit in Hc by lia. discriminate Hc. }
clear Hc.
paj_run_tok_x RUN HS HJ SHOK PV_Bspan; [pv_awr|].
clear HG HEI0.
(* ---- at the call of __asan_memset: the three runs stored nothing, a0 = slot, a1 = 0, a2 = 56 ---- *)
pose proof (pv_frame_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as K1.
pose proof (pv_frame_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity)) as K2.
pose proof (pv_frame_nowin _ _ _ _ HFr1 ltac:(vm_compute; reflexivity)) as K3.
assert (KT : forall x, mrestrict (w_H Wc) (ms_mem ms1) x = mrestrict (w_H Wc) memc x)
  by (intros x; rewrite K3, K2, K1; reflexivity).
(* the overlay stays normal across the three runs: they changed no byte (YAkMemnorm.memnorm_sub) *)
pose proof (pv_frame_nowin _ _ _ _ HF ltac:(vm_compute; reflexivity)) as U1.
pose proof (pv_frame_nowin _ _ _ _ HF0 ltac:(vm_compute; reflexivity)) as U2.
pose proof (pv_frame_nowin _ _ _ _ HF1 ltac:(vm_compute; reflexivity)) as U3.
assert (HMN1 : YAkMemnorm.memnorm SEGS (ms_mem ms1)).
{ apply (YAkMemnorm.memnorm_sub SEGS memc _ HMN). intros x b Hx. rewrite U3, U2, U1 in Hx. exact Hx. }
clear K1 K2 K3 HFr HFr0 HFr1 U1 U2 U3 HF HF0 HF1 HMN.
pmkst HS.
pv_prregx HS (10%bv : bv 5) Q10. pv_prregx HS (11%bv : bv 5) Q11. pv_prregx HS (12%bv : bv 5) Q12.
pv_prregx HS (1%bv : bv 5) Q1. pv_prregx HS (2%bv : bv 5) Q2. pv_prregx HS (3%bv : bv 5) Q3.
pv_prregx HS (4%bv : bv 5) Q4.
rewrite denot_lit_U, (pv_U_slot E kids (Z.of_nat n) E32 E33) in Q10 by lia.
rewrite denot_lit_U, (pv_U_mulh E (Z.of_nat n) E33) in Q11 by lia.
rewrite denot_lit_U, U_lit in Q12 by lia.
(* ra: the instruction after the jal, PI_O_MSET + 4 (the run's return offset, computed, not typed) *)
let k1 := eval vm_compute in (PI_AT (L := B_prog_listing) (PI := PA) (PI_O_MSET + 4)) in
assert (Q1' : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + k1))
  by (rewrite Q1; exact (codeptr_val (L := B_prog_listing) (PI := PA) E k1 HEI)).
clear Q1. rename Q1' into Q1.
rewrite pv_denot0, E2 in Q2. rewrite pv_denot0, E3, Hgp, Rgp0 in Q3. rewrite pv_denot0, E4, Htp, Rtp0 in Q4.
assert (HspT : spZ (ms_regs ms1) = spZ regs) by (unfold spZ; rewrite Q2; reflexivity).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
assert (Hks : In (kids, 56 * Z.of_nat cap) (pi_sblk o kids keys cap)).
{ unfold pi_sblk. apply in_or_app. left.
  unfold kids_blkR. rewrite (proj2 (Z.eqb_neq (Z.of_nat cap) 0)) by lia. left. reflexivity. }
assert (Hkd : In (kids, 56 * Z.of_nat cap) D0)
  by (apply (Permutation_in _ (Permutation_sym HD0)); apply in_or_app; left; exact Hks).
pose proof HMOVE as (HMnew & _ & _ & _).
pose proof (HMnew _ _ Hkd) as HKnew.
pose proof (proj1 HJ) as HAR1.
destruct (HSH lyc Sc Hpc Wc (ms_mem ms1) _ (kids - cf_head) (56 * Z.of_nat cap + cf_head) HAR1 Hkab Hkhp) as [Hbs Hhull].
rewrite Hreqk in Hbs, Hhull. replace (kids - cf_head + cf_head) with kids in Hbs, Hhull by lia.
replace (56 * Z.of_nat cap + cf_head - cf_head) with (56 * Z.of_nat cap) in Hbs, Hhull by lia.
(* the journal's model in the goal's collapsed form (YA0o.v wvb_collapse, as srr_norm_model leaves the goal) *)
repeat rewrite wvb_collapse in HJ.
(* the memset: YGcallMxmn.aj_intrin_at_xmR on the journal at wle' (it keeps the world), lifted SRr -> SRr' *)
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply SRr_SRr'.
  eapply (YGcallMxmn.aj_intrin_at_xmR (fx := fxc) (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS Hsegs
    (wle' SEGS YGcfRehidePost.RZ_cf) OSet
    (pa_sigma AS___asan_memset) (AMEMSET fxc) Wc (ms_regs ms1) (ms_mem ms1) (STK_parse_items d + e) (spZ regs0 + e)
    (rd_fp q v) ly _ Hp W mem md [] lyc Sc Hpc _ k (pv_slot kids n) 0 56 (-144 - e) _ HJ).
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - lia.
  - unfold pv_slot; lia.
  - unfold pv_slot; lia.
  - rewrite HspT; lia.
  - lia.
  - lia.
  - rewrite Hes; lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PA)); [lia | reflexivity].
  - intros a Ha. unfold pv_slot in Ha. split.
    + right; right; left. exists (kids - cf_head), (56 * Z.of_nat cap + cf_head).
      split; [exact Hkab|]. split; [exact HKnew|]. rewrite Hreqk. lia.
    + rewrite Hes. lia.
  - unfold amem_range, pv_slot, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - unfold pv_slot. apply (block_shadow_range _ _ kids (56 * Z.of_nat cap)); [exact Hbs | lia | lia].
  - intros _. unfold pv_slot. apply (pv_hull_sub _ kids (56 * Z.of_nat cap)); [apply Hhull; lia | lia | lia | lia].
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hset & Hfr2 & Hpres2 & Hmn2).
pose proof (Hmn2 HMN1) as HMN2. clear Hmn2 HMN1.
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H Wc) mem2) HP2 [0; 1]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ cbn [ms_mem restrict]. constructor; [|constructor; [|apply Forall_nil]]; split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr2; unfold pv_slot; lia.
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. exfalso. lia.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite E19, unsigned_lit_small in Ha by lia.
    apply (mbyte_of_aview SEGS). apply Hfr2; [lia | | lia].
    intros Hsl. apply (HAPART (kids, 56 * Z.of_nat cap) a Hks); [unfold pj_holdsR; cbn [fst snd]; unfold pv_slot in Hsl; lia | lia].
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. exfalso. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ev eqn:HEv in HSX.
assert (HEI2 : img_env VAL A_LIM Ev) by (rewrite HEv; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall i, (i < 34)%nat -> ew Ev i = ew E i) by (intros i Hi; rewrite HEv; apply ew_havoc_old; exact Hi).
assert (HAE2 : env_agree 32 (Ereg regs [Z_to_bv 64 kids; Z_to_bv 64 (Z.of_nat n)]) Ev)
  by (rewrite HEv; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEv.
(* the bytes the memset kept: outside the slot and the ESTACK window below sp *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (pv_slot kids n <= a < pv_slot kids n + 56) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hs Hw. rewrite Hfr2 by lia. apply (aview_eq_of SEGS). apply KT. }
assert (Hvra2 : range_addressable (aview SEGS (w_H Wc) mem2) SHADOW_OFF v 56).
{ eapply range_addressable_agree; [|exact Hvra]. intros x Hx.
  pose proof (pv_shadow_low x ltac:(lia)) as Hs0. pose proof (pv_shadow_app _ _ x Hkapp ltac:(lia)) as Hs1.
  apply KM; unfold pv_slot; lia. }
assert (Ev19 : ew Ev 19 = Z_to_bv 64 v) by (rewrite OLD2 by lia; exact E19).
assert (SHOK2 : sh_ok SEGS PV_Bx pv_val_SH Ev (mrestrict (w_H Wc) mem2)).
{ unfold sh_ok, pv_val_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H Wc) mem2 Ev PV_Bx 19 v 56 v 0 56 Hvra2);
  [unfold PV_Bx; rewrite U_lit by (unfold SHADOW_OFF; lia); reflexivity
  | rewrite (U_atom Ev 19 v Ev19) by lia; reflexivity | lia | lia
  | intros x Hx; unfold kHighMemBeg, SHADOW_OFF in *; lia]. }
clear HS HJ SHOK. rename HSX into HS. rename HJ2 into HJ. rename SHOK2 into SHOK.
pose (RUNTO := PI_RUNTOR (fx := fxc) (rc := rc) (SK := SK) (L := B_prog_listing) (PL := PL_prog_B) (PI := PA) B
  (@prh_pst prh_img_B) ARx LAWS).
paj_run_to_tok_x RUNTO HS HJ SHOK PV_Bspan (PI_AT (L := B_prog_listing) (PI := PA) PI_O_PVAL); [pv_awr|].
(* ---- AT PI_O_PVAL (`jal parse_value`): the run stored nothing; a0 = q, a1 = the slot ---- *)
clear HG HEI0.
pose proof (pv_frame_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as K4. clear HFr.
pose proof (pv_frame_nowin _ _ _ _ HF ltac:(vm_compute; reflexivity)) as U4.
assert (HMN3 : YAkMemnorm.memnorm SEGS (ms_mem ms2)).
{ apply (YAkMemnorm.memnorm_sub SEGS mem2 _ HMN2). intros x b Hx. rewrite U4 in Hx. exact Hx. }
clear U4 HF HMN2.
pmkst HS.
pv_prregx HS (2%bv : bv 5) P2. pv_prregx HS (3%bv : bv 5) P3. pv_prregx HS (4%bv : bv 5) P4.
pv_prregx HS (8%bv : bv 5) P8. pv_prregx HS (9%bv : bv 5) P9. pv_prregx HS (10%bv : bv 5) P10.
pv_prregx HS (11%bv : bv 5) P11. pv_prregx HS (18%bv : bv 5) P18. pv_prregx HS (19%bv : bv 5) P19.
pv_prregx HS (20%bv : bv 5) P20. pv_prregx HS (21%bv : bv 5) P21. pv_prregx HS (22%bv : bv 5) P22.
pv_prregx HS (23%bv : bv 5) P23. pv_prregx HS (24%bv : bv 5) P24. pv_prregx HS (25%bv : bv 5) P25.
pv_prregx HS (26%bv : bv 5) P26. pv_prregx HS (27%bv : bv 5) P27.
assert (ERv : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> (i < 32)%nat -> ew Ev i = getr regs r)
  by (intros i r Hi Hi32; rewrite (proj1 HAE2 i Hi32); exact (ew_Ereg_nat regs _ i r Hi)).
assert (Ev9 : ew Ev 9 = Z_to_bv 64 q) by (rewrite OLD2 by lia; exact E9).
assert (Ev32 : ew Ev 32 = Z_to_bv 64 kids) by (rewrite OLD2 by lia; exact E32).
assert (Ev33 : ew Ev 33 = Z_to_bv 64 (Z.of_nat n)) by (rewrite OLD2 by lia; exact E33).
assert (DS : forall i c a, ew Ev i = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> 0 <= a + c < 2 ^ 64 ->
  sv_denot Ev (SOff i c) = Z_to_bv 64 (a + c))
  by (intros i c a Hi Ha Hc; rewrite denot_lit_U, (U_atom_off Ev i a c Hi) by lia; reflexivity).
rewrite pv_denot0, (ERv 2%nat 2%bv eq_refl) in P2 by lia. rewrite pv_denot0, (ERv 3%nat 3%bv eq_refl) in P3 by lia.
rewrite pv_denot0, (ERv 4%nat 4%bv eq_refl) in P4 by lia. rewrite pv_denot0, (ERv 9%nat 9%bv eq_refl) in P9 by lia.
rewrite pv_denot0, (ERv 9%nat 9%bv eq_refl) in P10 by lia. rewrite pv_denot0, (ERv 18%nat 18%bv eq_refl) in P18 by lia.
rewrite pv_denot0, (ERv 19%nat 19%bv eq_refl) in P19 by lia. rewrite pv_denot0, (ERv 21%nat 21%bv eq_refl) in P21 by lia.
rewrite (DS 9%nat 16 q Ev9) in P8 by lia. rewrite (DS 9%nat 8 q Ev9) in P20 by lia. rewrite (DS 19%nat 40 v Ev19) in P22 by lia.
rewrite denot_lit_U, (pv_U_slot Ev kids (Z.of_nat n) Ev32 Ev33) in P11 by lia.
pose proof (pv_denot_shx Ev 9 q 0 Ev9 ltac:(lia) ltac:(lia) ltac:(lia)) as X27. rewrite Z.add_0_r in X27.
assert (HspF : spZ (ms_regs ms2) = spZ regs) by (unfold spZ; rewrite P2; reflexivity).
lazymatch goal with |- context [{| cfg_ms := mkst _ ?pcw _ _ |}] =>
  replace pcw with (w64 (pa_val (PAImg := PA) A_TEXT + PI_AT (L := B_prog_listing) (PI := PA) PI_O_PVAL))
    by (unfold w64; f_equal; vm_compute; reflexivity)
end.
repeat rewrite wvb_collapse in HJ.
lazymatch goal with |- context [{| cfg_ms := mkst ?rT _ ?mT _; cfg_model := ?dT |}] =>
  apply (HCALL fxc fx0 ly S Hp W mem md ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc Wc
    mT dT k rT WS0)
end.
(* back to the budgeted journal from S at WS0: the block kept the allocator state Sc (the runs and the memset), so
   HWD, the cover of Sc's wild part, still holds *)
{ unfold pi_ajR.
  exact (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS YGcfRehidePost.RZ_cf)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HWD). }
{ exact HWS. }
(* the memory at PI_O_PVAL keeps every byte outside the slot and the ESTACK window below sp *)
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (pv_slot kids n <= a < pv_slot kids n + 56) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
  aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hs Hw. rewrite <- (KM a Ha Hs Hw). apply (aview_eq_of SEGS). apply K4. }
assert (KG : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms2))).
{ intros x Hx. rewrite K4. assert (Hx1 : mrestrict (w_H Wc) (ms_mem ms1) x <> None) by (rewrite KT; exact Hx).
  exact (pv_grows_of_present _ _ _ Hpres2 x Hx1). }
assert (KA : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply KF; unfold pv_slot; lia. }
destruct (pv_frame_kept regs0 regs (ms_regs ms2) W mem Wc memc (ms_mem ms2) e q v HFR HRB HspF
  ltac:(rewrite P3; reflexivity) ltac:(rewrite P4; reflexivity) ltac:(rewrite P22, R22; reflexivity)
  ltac:(rewrite P24, R24; exact (pv_denot_shx Ev 19 v 40 Ev19 ltac:(lia) ltac:(lia) ltac:(lia)))
  ltac:(lia) KA) as [HFR2 HRB2].
unfold pv_call_pre.
split; [exact HFP|]. split; [exact HENT|]. split; [exact HMN3|].
(* the travelling position and live requests over tr0 are pv_vdata's own conjuncts, carried by pv_vdata_kept: the block
   keeps the allocator state Sc *)
split; [exact HFR2|].
split.
{ refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - rewrite P9. exact R9.
  - rewrite P19. exact R19.
  - rewrite P18. exact R18.
  - rewrite P8. reflexivity.
  - rewrite P20. reflexivity.
  - rewrite P26. reflexivity.
  - rewrite P27. exact X27.
  - rewrite P25. exact (pv_denot_shx Ev 9 q 16 Ev9 ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite P23. exact (pv_denot_shx Ev 9 q 8 Ev9 ltac:(lia) ltac:(lia) ltac:(lia)). }
split; [exact HRB2|]. split; [rewrite P21; exact H21|]. split; [rewrite P10; exact R9|].
exists f, n, cap, acc, kids, keys, Di, nm, Dk, pc, ok0, tr0, D0, Lamc, peakc, cntc, failc, ranc.
split; [|split; [rewrite P11; reflexivity|]].
- apply (pv_vdata_kept fx0 ly S Hp W mem ch CTX regs0 e q v o text len tb p Lam peak cnt fail ran most own kr lyc Sc Hpc
    Wc memc (ms_mem ms2) mdc N f n cap acc kids keys Di nm Dk pc ok0 tr0 D0 Lamc peakc cntc failc ranc CTX0 CW (spZ regs)
    HARc HENT).
  + exact (conj HCUR (conj HNb (conj Hncap (conj HCONT (conj HDEP (conj HAPART (conj HKEY (conj HD0 (conj HFUEL (conj HEQ
      (conj HLED (conj HMOVE (conj HPOSB (conj HLIVE (conj HBB (conj HLOK (conj HLSUM (conj HROOM HK1)))))))))))))))))).
  + lia.
  + lia.
  + lia.
  + exact KF.
  + exact KG.
- apply pv_zero_of_aview. intros i Hi. rewrite (aview_eq_of SEGS _ _ _ _ (K4 _)). rewrite Hset by lia. reflexivity.
Qed.

End w.
