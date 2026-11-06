(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 552 of its 667 lines of code are new or changed and 4938 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): SEGMENT A1 of reac_segconf_parse_file's walk (0x87a78,
   lib/A/Prog/pf_pieces.v), ENTRY 0x87a78 -> FTAKEN 0x87b24, 43 instructions. It proves `S_A1 B`:
   from H_FTAKEN at every FP state, H_ENTRY at the ambient one.

   WHAT THE 43 INSTRUCTIONS DO (dis/reac_segconf_parse_file.fuzz_segconf.asan.s):
     0x87a78 addi sp,sp,-0x140 and the probe store at 0(sp); the 13 saved registers ra, s0, s1, s2 .. s11 at
       sp0 - 8 - 8 j (0x87a80-0x87ab0); s0 = sp0 (0x87ab4); sp = s1 = (sp0 - 0x140) & -32 (0x87ab8, 0x87abc);
       the arguments into s3 = label, s9 = text, s8 = c (0x87ac0-0x87ac8);
     0x87acc-0x87ae0 the two GOT loads: the use-after-return flag through the GOT word 0xa2aa8 (listing object 1)
       and the shadow base through 0xa2a50 -> 0xabff8 (objects 0 and 12), s6 = SHADOW_OFF; s2 = 0x4000 (0x87ae4);
     0x87ae8 `beqz a1`: the flag is AR's constant 1 (uar_cell_regionP), so the real-stack fallback is not taken;
     0x87aec-0x87af0 a0 = 0x480 and the call of __asan_stack_malloc_5 (frame_alloc_5), through the kit's
       aj_stack_malloc_atS (lib/A/Prog/PaCall.v:237) with astack_malloc_realizes 5 and stack_malloc_progressP;
     0x87af4-0x87b04 s10 = 0x40e0, s7 = a0 = F, and `bnez a0` to FTAKEN: the frame's address is >= 4096, so the
       branch is taken and 0x87b08-0x87b20 (the real-stack fallback) is dead, as pf_pieces.v's head comment says.
   Model: plugin-hostd/fuzz_command's check_round_trip.v (crt_s0, the class-5 take at :786) and numberE.v (the
   entry seed), at origin/ossv/recipes 501c0d516c69; the segconf shape of both is the refuse walk's refuse_a.v /
   refuse_e.v. Segment A1's proof, 2026-10-30.

   SECTION HYPOTHESES (pf_pieces.v's list for A1, in listing terms): astack_malloc_realizes 5 at every FP state
   and stack_malloc_progressP (the frame take), the record's PALib / PALibF / model_laws, the listing's
   seg_val_relro, and SSPX (the stack-protector cells at every AR state, the image-A owner's route A: a named
   Section hypothesis until listing stage 2's SegRecCells.seg_rec_cells lands). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0d_tail YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegAddr SegPa SegPaLib
PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaCallRun SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
reac_segconf_parse_file_c SegInstA pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================ pure arithmetic (check_round_trip.v's crt_* ) ============================ *)
Lemma a1_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma a1_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite a1_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma a1_denot_and_m32_add0 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff n c) (SLit (-32))) (SLit 0)) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
unfold U. rewrite (a1_denot_and_m32 E n v c Hn H0 H1 Hv). rewrite unsigned_lit_small; [apply zcanon_id|];
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)); (split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia] | unfold M64; lia]).
Qed.
Lemma a1_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* the floor and the ceiling of an 8-byte word against an 8-aligned bound *)
Lemma a1_floor_ge : forall y M, M mod 8 = 0 -> M <= y -> M <= y / 8 * 8.
Proof.
intros y M HM H. pose proof (Z.div_mod M 8 ltac:(lia)) as DM. rewrite HM, Z.add_0_r in DM.
assert (Hd : M / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma a1_ceil_le : forall y M, M mod 8 = 0 -> y < M -> y / 8 * 8 + 8 <= M.
Proof.
intros y M HM H. pose proof (Z.div_mod M 8 ltac:(lia)) as DM. rewrite HM, Z.add_0_r in DM.
assert (Hlt : y / 8 < M / 8) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma a1_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma a1_reg_lit : forall (rr : bvmap 5 word) (k : Z) (r : bv 5) v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr k r v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the class-5 frame take (pf_pieces.v's A1 row: astack_malloc_realizes 5 at pa_sigma SS___asan_stack_malloc_5,
   stack_malloc_progressP) *)
Hypothesis ASM5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.
Hypothesis SMP : stack_malloc_progressP B.
(* the record (the walk hypotheses of fuzz_command's numberA.v) *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
(* the listing's read-only range *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (the image-A owner's route A, the shape of
   lib/A/Prog/reac_segconf_parse.v); discharged from SegRecCells.seg_rec_cells when listing stage 2 compiles *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Section x.
Context {fx : YK11.FPState}.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ================================ the entry state (numberE.v / crt_ssE) ================================ *)
(* atom 32 is the shadow base SB, atom 33 the use-after-return flag cell; the regions are the 320-byte real
   frame, the shadow GOT word 0xa2a50 (object 0) and its cell 0xabff8 (object 12), the flag's GOT word 0xa2aa8
   (object 1) and the flag cell (AR's constant 1) *)
Definition a1_ss0 : sstate := mkSS AF_reac_segconf_parse_file sr_atoms
  [stack_region 320; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33] None
  (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0)] [] []).
Definition a1_EE (regs : bvmap 5 word) : env := Eimg (Ereg regs [w64 SB; w64 (as_uar_cell B)]).
Lemma a1_EE_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (a1_EE regs) n = getr regs r.
Proof. intros regs n r Hn. unfold a1_EE. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma a1_EE_32 : forall regs, ew (a1_EE regs) 32 = Z_to_bv 64 SB.
Proof. intros regs. unfold a1_EE. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma a1_EE_33 : forall regs, ew (a1_EE regs) 33 = Z_to_bv 64 (as_uar_cell B).
Proof.
intros regs. unfold a1_EE. rewrite Eimg_low by (unfold A_TEXT; lia).
change 33%nat with (32 + 1)%nat. exact (ew_Ereg_extra regs _ 1).
Qed.
Lemma a1_seed : forall ly S (W : world SEGS) regs mem md ch,
afn_pre SEGS B STK_reac_segconf_parse_file ly S W regs mem md ch ->
st_ok_pi SEGS VAL (a1_EE regs) a1_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_parse_file)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : STK_reac_segconf_parse_file = 12800) by reflexivity.
rewrite FFS in Hslo.
assert (Usp : bv_unsigned (ew (a1_EE regs) 2) = spZ regs)
  by (rewrite (a1_EE_reg regs 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew (a1_EE regs) 32 = Z_to_bv 64 SB) by (apply a1_EE_32).
assert (E33 : ew (a1_EE regs) 33 = Z_to_bv 64 (as_uar_cell B)) by (apply a1_EE_33).
assert (E241 : ew (a1_EE regs) (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (unfold a1_EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew (a1_EE regs) (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (unfold a1_EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew (a1_EE regs) (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (unfold a1_EE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 1)) as R1.
pose proof (pa_val_range (A_OBJ 12)) as R12.
pose proof (palf_uar_img B TLF) as [HU1 HU2]. pose proof (palf_uar_al B TLF) as HU4.
unfold kImgEnd in HU2.
assert (U241 : bv_unsigned (ew (a1_EE regs) (A_OBJ 0)) = VAL (A_OBJ 0))
  by (rewrite E241; apply unsigned_lit_small; lia).
assert (U242 : bv_unsigned (ew (a1_EE regs) (A_OBJ 1)) = VAL (A_OBJ 1))
  by (rewrite E242; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew (a1_EE regs) (A_OBJ 12)) = VAL (A_OBJ 12))
  by (rewrite E253; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (a1_EE regs) 33) = as_uar_cell B)
  by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 1 ltac:(lia)) as HuarR.
unfold kImgEnd in HcellR, HgotR, HuarR.
pose proof (palf_sep B TLF) as HSEP. unfold zseps, zseps_from in HSEP. cbn [fst snd] in HSEP.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kgu).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kgu.
rewrite restrict_mkst_fx. unfold a1_ss0. apply pa_entry_st_ok_full.
- unfold a1_EE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite FFS. lia.
  + rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (a1_EE regs) _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (a1_EE regs) _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SB; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite U242. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (a1_EE regs) _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgu).
  + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS (a1_EE regs) _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS _ _ _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253, U242, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32. rewrite unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16.
  rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.
(* the 13 saved registers, from the region the prologue's stores left on atom 2 (crt_entry_frame) *)
Lemma a1_saved_of_region : forall (regs : bvmap 5 word) (H : word -> bool) (m2 : word -> option byte) cs,
region_ok SEGS (a1_EE regs) (mrestrict H m2) (YP09.mkRegion (Some 2%nat) (-320) 0 (-320) 0 cs) ->
(forall j r, nth_error PF_SAVED j = Some r ->
   In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
pf_saved (aview SEGS H m2) (spZ regs) regs.
Proof.
intros regs H m2 cs HR Hs j r Hj.
assert (Usp : bv_unsigned (ew (a1_EE regs) 2) = spZ regs)
  by (rewrite (a1_EE_reg regs 2%nat 2%bv eq_refl); reflexivity).
assert (Hin : In r PF_SAVED) by (eapply nth_error_In; exact Hj).
assert (Hrr : 0 <= r <= 27) by (unfold PF_SAVED in Hin; cbn in Hin; intuition lia).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HV.
change (bv_modulus 64) with (2 ^ 64) in HV.
apply (rdword_of_val_mem SEGS); [|exact HV].
replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region (a1_EE regs) (mrestrict H m2) 2%nat (spZ regs) cs (-320) 0 (-320) 0
  (-8 - 8 * Z.of_nat j) 8%N (SOff (Z.to_nat r) 0) _ HR Usp (Hs j r Hj)).
- cbn [sv_denot]. rewrite Z.add_0_r.
  rewrite (a1_EE_reg regs (Z.to_nat r) (Z_to_bv 5 r));
    [first [reflexivity | symmetry; apply Z_to_bv_bv_unsigned]|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HV.
- cbn. lia.
Qed.

(* ===================================== keeping the caller's objects ===================================== *)
Lemma a1_sa_addr_of_heap : forall ly S (W : world SEGS) mem md q n, AR SEGS B ly S W mem md -> sa_heap B ly S q n ->
0 <= q -> 0 < n -> sa_addr (rdW W mem) q n.
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hm) Hq Hn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4 & Hc & Happ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. pose proof asan_consts as (C1 & _).
split; [lia|]. split; [lia|].
split; [exact (amem_range_sub_app b (req_size m) q n Happ Hc ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia))|].
intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md b m q n HAR Hin ltac:(lia) ltac:(lia) Hn).
Qed.
(* the word tail of a heap object: the core's AR_block_word_vis at the new state *)
Lemma a1_tail_of_heap : forall ly S (W : world SEGS) mem md q n,
AR SEGS B ly S W mem md -> sa_heap B ly S q (n + 1) -> 0 <= n -> sa_tail (rdW W mem) (q + n).
Proof.
intros ly S W mem md q n HAR (b & m & Hin & Hb & Hm) Hn a Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
exact (AR_block_word_vis SEGS B ly S W mem md b m (q + n) a HAR Hin ltac:(lia) ltac:(lia)).
Qed.
(* a reader that keeps the shadow word range of [q, q + n) keeps sa_addr *)
Lemma a1_sa_addr_kept : forall (rd rd' : reader) q n,
(forall s, shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
0 < n -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n K Hn (H1 & H2 & H3 & H4 & H5).
assert (HB : forall x, q <= x < q + n ->
  shadow_addr q / 8 * 8 <= shadow_addr x < shadow_addr (q + n - 1) / 8 * 8 + 8).
{ intros x Hx. unfold shadow_addr.
  assert (D1 : q / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : x / 8 <= (q + n - 1) / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_mod (SHADOW_OFF + q / 8) 8 ltac:(lia)) as D3.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + q / 8) 8 ltac:(lia)) as D4.
  pose proof (Z.div_mod (SHADOW_OFF + (q + n - 1) / 8) 8 ltac:(lia)) as D5.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + n - 1) / 8) 8 ltac:(lia)) as D6.
  lia. }
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split.
- intros x Hx. destruct (H4 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  unfold shadow_of_addr. rewrite (K (SHADOW_OFF + x / 8)); [exact Hsv|]. exact (HB x Hx).
- intros _ s Hs. rewrite (K s Hs). exact (H5 Hn s Hs).
Qed.
(* a literal, the catalogue and arodata: image bytes the runtime does not own, kept byte by byte *)
Lemma a1_sa_lit_keep : forall (W : world SEGS) (mem mem' : word -> option byte) a s,
sa_lit SEGS B (rdW W mem) a s ->
(forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
   rdW W mem' x = rdW W mem x) ->
sa_lit SEGS B (rdW W mem') a s.
Proof.
intros W mem mem' a s (Ha & ((Hz & Hn0) & _) & Hp & Hr & Hi) K.
split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
split; [split; [|exact Hn0] | apply sa_tail_of_romtail; exact Hr].
intros i Hi'. pose proof Hi' as Hl. rewrite length_app in Hl. cbn [length] in Hl.
destruct (Hi (a + Z.of_nat i) ltac:(lia)) as (Hm & Ho & He).
rewrite (K _ Hm Ho He). exact (Hz i Hi').
Qed.
Lemma a1_sa_cat_keep : forall (W : world SEGS) (mem mem' : word -> option byte) cat,
sa_cat SEGS B (rdW W mem) cat ->
(forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) -> ~ (as_errno B <= x < as_errno B + 4) ->
   rdW W mem' x = rdW W mem x) ->
sa_cat SEGS B (rdW W mem') cat.
Proof.
intros W mem mem' cat (Hp & Hi & Hrows) K.
split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp.
split; [|exact (a1_sa_lit_keep W mem mem' tp _ Hl K)].
rewrite <- Htp. apply rdword_ext. intros k Hk.
assert (Hrng : cat <= pin_spec.row_addr cat i + k < cat + pin_spec.CAT_BYTES).
{ unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES in *.
  unfold pin_spec.CAT_N in Hn. lia. }
destruct (Hi _ Hrng) as (Hm & Ho & He). exact (K _ Hm Ho He).
Qed.



(* ================================= the segment ================================= *)
Lemma pf_a1_entry : HA_FTAKEN B -> H_ENTRY (fx := fx) B.
Proof.
unfold HA_FTAKEN, H_ENTRY. intros HFT v HCX HFRM.
pose proof HCX as HCX0.
destruct HCX as (HPRE & HROD & H10 & [Hc0z Hc64] & H11 & [Ht0z Ht64] & H12 & [Hlp0z Hlp64] & (fe & HPF) & HROOM & HEV).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : STK_reac_segconf_parse_file = 12800) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
rewrite FFS in Hslo.
destruct HPF as (HRP & HOSTR & HLABM).
destruct HRP as (C0 & C16 & RC & Hcheap & Ac & G1 & RF1 & O1 & T0 & ST & LS & Htheap & At & DJ & FR0 & SSP & CAT & LITS).
assert (Esp0 : pf_sp0 v = spZ (p_regs v)) by reflexivity.
assert (Es1 : pf_s1 v = 32 * ((spZ (p_regs v) - 320) / 32)).
{ unfold pf_s1, pf_sp0. pose proof (Z.div_mod (spZ (p_regs v) - 320) 32 ltac:(lia)). lia. }
destruct (a1_sp1_facts (spZ (p_regs v) - 320) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (P1 & P2 & P3).
assert (P4 : (32 * ((spZ (p_regs v) - 320) / 32) - spZ (p_regs v)) mod 16 = 0)
  by (rewrite Zminus_mod, P3, Hal16; reflexivity).
(* the seed and the journal *)
pose proof (a1_seed (p_ly v) (p_S v) (p_W v) (p_regs v) (p_mem v) (p_md v) (p_ch v) HPRE) as HS.
pose proof (ajournal_init SEGS B STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W (p_c v))
  (p_ly v) (p_S v) (p_W v) (p_regs v) (p_mem v) (p_md v) (p_ch v) HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (a1_EE (p_regs v))) by (unfold a1_EE; apply Eimg_env).
assert (Usp : bv_unsigned (ew (a1_EE (p_regs v)) 2) = spZ (p_regs v))
  by (rewrite (a1_EE_reg (p_regs v) 2%nat 2%bv eq_refl); reflexivity).
assert (E2 : ew (a1_EE (p_regs v)) 2 = Z_to_bv 64 (spZ (p_regs v)))
  by (rewrite (a1_EE_reg (p_regs v) 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E32 : ew (a1_EE (p_regs v)) 32 = Z_to_bv 64 SB) by (apply a1_EE_32).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (a1_EE (p_regs v)) (mrestrict (w_H (p_W v)) (p_mem v))) by constructor.
unfold cfg_at, PF_ENTRY.
change (w64 (BASE + AF_reac_segconf_parse_file)) with (Z_to_bv 64 (BASE + AF_reac_segconf_parse_file)).
(* R1: the prologue, the GOT loads, the flag test, up to the call of __asan_stack_malloc_5 (0x87af0) *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ unfold a1_ss0, stack_region; cbn [ss_mem].
  eapply (awr_ok_cons_stack SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat);
    [reflexivity | exact Usp | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
(* the entry run writes only [sp0 - 320, sp0) *)
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => spZ (p_regs v) - 320 <= a < spZ (p_regs v)) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
    intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia |]);
    destruct Hin)) as K0.
(* the saved registers, from the region the prologue left *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg
| st_ok _ ?Ex ?ssx ?msx =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRg
end.
cbn [ms_mem restrict] in HRg.
assert (HFR0 : pf_saved (rdW (p_W v) (ms_mem ms)) (spZ (p_regs v)) (p_regs v)).
{ apply (a1_saved_of_region (p_regs v) _ _ _ HRg).
  intros j r Hr.
  do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
  cbn in Hr. destruct j; discriminate Hr. }
clear HRg. clear HF HFr HG.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
assert (R2v : getr (ms_regs ms) 2 = w64 (32 * ((spZ (p_regs v) - 320) / 32)))
  by (rewrite R2; unfold w64; apply (a1_denot_and_m32 (a1_EE (p_regs v)) 2 (spZ (p_regs v)) (-320) E2); lia).
pmkst HS.
pose proof (palf_sm B TLF 5 ltac:(clear; cbn; tauto)) as SM5e.
change (cs_stack_malloc 5) with SS___asan_stack_malloc_5 in SM5e.
rewrite SM5e.
pose proof (count_cid_le_length 5 (frames (p_S v))) as Hcnt.
unfold sa_room_n in HROOM.
assert (Hfs5 : fs_frames 5 = 512) by (vm_compute; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
    eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 5 (ASM5 fx) ltac:(lia) (p_W v)
      (ms_regs msX) (ms_mem msX) STK_reac_segconf_parse_file (spZ (p_regs v)) (seg_spec.RC_PARSE_W (p_c v))
      (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [] (p_ly v) (p_S v) _ 0
      (32 * ((spZ (p_regs v) - 320) / 32) - spZ (p_regs v)) _ HJ)
  end.
- (unfold spZ at 1; rewrite R2v; unfold w64; rewrite unsigned_lit_small by lia; lia).
- exact P4.
- lia.
- lia.
- (rewrite R3; rewrite ?a1_den_atom0; rewrite (a1_EE_reg (p_regs v) 3%nat 3%bv eq_refl); exact Hgp).
- (rewrite R4; rewrite ?a1_den_atom0; rewrite (a1_EE_reg (p_regs v) 4%nat 4%bv eq_refl); exact Htp).
- exact R1.
- (apply ret_ok_codeptr_v; [lia | reflexivity]).
- lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz
  & Hflag & HK & HJc & (fS2 & ES2)).
replace (spZ (p_regs v) + (32 * ((spZ (p_regs v) - 320) / 32) - spZ (p_regs v)))
  with (32 * ((spZ (p_regs v) - 320) / 32)) in HK by lia.
pose proof (proj1 HJ2) as HAR2.
(* the frame of class 5 *)
assert (Hin5 : In (5, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 5 fpos HAR2 Hin5) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 5) with 2048 in HFceil, HFapp.
change (frame_addr (p_ly v) 5 fpos) with (pf_F v fpos) in Ha0, Hz, Hflag, HF4096, HFceil, HFapp.
change (flag_addr (p_ly v) 5 fpos) with (pf_FL v fpos) in Hflag.
(* the state after the call: a0 is the fresh atom 1028. The four instructions after the call read and write no
   memory, so the state keeps no region: the run's write set is empty and nothing has to be carried *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H (p_W v)) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?A -> _ => assert (HQ : A); [|specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. apply Forall_nil. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
assert (AG : forall n, (n < 1024)%nat ->
  ew (YN3v.havoc (a1_EE (p_regs v)) 1024 (map (getr regs2) CLOB)) n = ew (a1_EE (p_regs v)) n)
  by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (E1028 : ew (YN3v.havoc (a1_EE (p_regs v)) 1024 (map (getr regs2) CLOB)) 1028 = Z_to_bv 64 (pf_F v fpos)).
{ change 1028%nat with (1024 + 4)%nat.
  rewrite (ew_havoc_new (a1_EE (p_regs v)) 1024 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia).
  cbn [nth map CLOB]. exact Ha0. }
assert (HEI1 : img_env VAL A_LIM (YN3v.havoc (a1_EE (p_regs v)) 1024 (map (getr regs2) CLOB)))
  by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (U1028 : bv_unsigned (ew (YN3v.havoc (a1_EE (p_regs v)) 1024 (map (getr regs2) CLOB)) 1028) = pf_F v fpos)
  by (rewrite E1028; apply unsigned_lit_small; lia).
(* the frame's address decides `bnez a0` at 0x87b04 *)
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  pose proof (st_ok_pi_add_fact Ex _ _ 1028 (mkAF 4096 (2 ^ 47) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1028; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3
end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let w := eval vm_compute in ss3 in change ss3 with w in HS end.
(* R2: 0x87af4 .. FTAKEN 0x87b24, no write *)
paj_run_to_sh RUNTOP HS HJ2 11760.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_nil. }
(* R2 writes nothing *)
match type of HFr with frame_of ?Ex ?rsx _ _ =>
  assert (K2W : forall b wlo whi a, In (b, wlo, whi) (windows rsx) ->
    base_val Ex b + wlo <= a < base_val Ex b + whi -> (fun _ : Z => False) a)
end.
{ intros b wlo whi a Hin Hrr. cbn beta. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
  destruct Hin. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ : Z => False) HFr K2W) as K2.
assert (K2' : forall a, 0 <= a < 2 ^ 64 -> rdW (p_W v) (ms_mem ms0) a = rdW (p_W v) mem2 a)
  by (intros a Ha; apply K2; [lia | intros []]).
(* ============ the three keepers from the entry reader to the reader at FTAKEN ============ *)
destruct HK as (HKs & HKb & HKi & HKf & HKp1 & HKp2).
assert (KLOW : forall a, 0 <= a < alloc_ceiling -> rdW (p_W v) (ms_mem ms) a = rdW (p_W v) (p_mem v) a)
  by (intros a Ha; apply K0; lia).
assert (KB : forall b m i, In (b, m) (ablocks B (p_ly v) (p_S v)) -> 0 <= i < req_size m ->
  rdW (p_W v) (ms_mem ms0) (b + i) = rdW (p_W v) (p_mem v) (b + i)).
{ intros b m i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4 & Hcb & _ & _ & _ & Hm0).
  pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2].
  rewrite (K2' (b + i) ltac:(lia)).
  rewrite (HKb b m i Hin Hi ltac:(intros [])).
  apply KLOW. lia. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> rdW (p_W v) (ms_mem ms0) a = rdW (p_W v) (p_mem v) a).
{ intros a Hm Ho He. pose proof (pa_img_range a Hm) as Hrg. unfold kImgEnd in Hrg.
  rewrite (K2' a ltac:(lia)). rewrite (HKi a Hm Ho He). apply KLOW. lia. }
assert (KF : forall cid pos a, In (cid, pos) (frames (p_S v)) -> 0 <= cid ->
  (in_zr a (frame_rng (p_ly v) (cid, pos)) \/
   in_zr a (shadow_addr (frame_addr (p_ly v) cid pos), fs_frame_bytes cid / 8)) ->
  rdW (p_W v) (ms_mem ms0) a = rdW (p_W v) (p_mem v) a).
{ intros cid pos a Hin Hcid Ha.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (HG1 & HG2 & HG3).
  pose proof (fs_frame_bytes_pos cid Hcid) as HGp.
  assert (Hlow : 0 <= a < alloc_ceiling).
  { destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng, shadow_addr in Ha; cbn [fst snd] in Ha;
    unfold SHADOW_OFF in *; [lia|].
    assert (Hq0 : 0 <= frame_addr (p_ly v) cid pos / 8) by (apply Z.div_pos; lia).
    assert (Hq1 : 8 * (frame_addr (p_ly v) cid pos / 8) <= frame_addr (p_ly v) cid pos)
      by (apply Z.mul_div_le; lia).
    assert (Hq0b : 0 <= fs_frame_bytes cid / 8) by (apply Z.div_pos; lia).
    assert (Hq2 : 8 * (fs_frame_bytes cid / 8) <= fs_frame_bytes cid) by (apply Z.mul_div_le; lia).
    lia. }
  rewrite (K2' a ltac:(lia)). rewrite (HKf cid pos a Hin Ha ltac:(intros [])). apply KLOW. exact Hlow. }
(* ======================= the registers at FTAKEN ======================= *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
assert (EA2 : ew (YN3v.havoc (a1_EE (p_regs v)) 1024 (map (getr regs2) CLOB)) 2 = Z_to_bv 64 (spZ (p_regs v)))
  by (rewrite AG by lia; exact E2).
assert (EA32 : ew (YN3v.havoc (a1_EE (p_regs v)) 1024 (map (getr regs2) CLOB)) 32 = Z_to_bv 64 SB)
  by (rewrite AG by lia; exact E32).
assert (V2 : getr (ms_regs ms0) 2 = w64 (pf_s1 v)).
{ rewrite Q2, Es1. unfold w64.
  apply (a1_denot_and_m32 _ 2 (spZ (p_regs v)) (-320) EA2); lia. }
assert (V9 : getr (ms_regs ms0) 9 = w64 (pf_s1 v)).
{ rewrite Q9, Es1. unfold w64.
  first [ apply (a1_denot_and_m32 _ 2 (spZ (p_regs v)) (-320) EA2)
        | apply (a1_denot_and_m32_add0 _ 2 (spZ (p_regs v)) (-320) EA2) ]; lia. }
assert (V8 : getr (ms_regs ms0) 8 = w64 (spZ (p_regs v)))
  by (rewrite Q8; rewrite ?a1_den_atom0; rewrite ?AG by lia; rewrite E2; reflexivity).
assert (V3 : getr (ms_regs ms0) 3 = w64 (as_gp B))
  by (rewrite Q3; rewrite ?a1_den_atom0; rewrite ?AG by lia;
      rewrite (a1_EE_reg (p_regs v) 3%nat 3%bv eq_refl); exact Hgp).
assert (V4 : getr (ms_regs ms0) 4 = w64 (as_tp B))
  by (rewrite Q4; rewrite ?a1_den_atom0; rewrite ?AG by lia;
      rewrite (a1_EE_reg (p_regs v) 4%nat 4%bv eq_refl); exact Htp).
assert (V22 : getr (ms_regs ms0) 22 = w64 SHADOW_OFF)
  by (rewrite Q22; rewrite ?a1_den_atom0; rewrite ?AG by lia; rewrite E32; reflexivity).
assert (V10 : getr (ms_regs ms0) 10 = w64 (pf_F v fpos)).
{ rewrite Q10. first [ exact Ha0
                     | (rewrite ?a1_den_atom0, E1028; reflexivity)
                     | (cbn [nth map CLOB]; exact Ha0) ]. }
assert (V23 : getr (ms_regs ms0) 23 = w64 (pf_F v fpos)).
{ rewrite Q23. first [ exact Ha0
                     | (rewrite ?a1_den_atom0, E1028; reflexivity)
                     | (cbn [nth map CLOB]; exact Ha0) ]. }
assert (V24 : getr (ms_regs ms0) 24 = w64 (p_c v))
  by (rewrite Q24; rewrite ?a1_den_atom0; rewrite ?AG by lia;
      rewrite (a1_EE_reg (p_regs v) 10%nat 10%bv eq_refl); exact H10).
assert (V25 : getr (ms_regs ms0) 25 = w64 (p_t v))
  by (rewrite Q25; rewrite ?a1_den_atom0; rewrite ?AG by lia;
      rewrite (a1_EE_reg (p_regs v) 11%nat 11%bv eq_refl); exact H11).
assert (V19 : getr (ms_regs ms0) 19 = w64 (p_lp v))
  by (rewrite Q19; rewrite ?a1_den_atom0; rewrite ?AG by lia;
      rewrite (a1_EE_reg (p_regs v) 12%nat 12%bv eq_refl); exact H12).
assert (V26 : getr (ms_regs ms0) 26 = w64 16608)
  by (rewrite Q26; first [reflexivity | cbn; reflexivity | vm_compute; reflexivity]).
(* ======================= apply H_FTAKEN ======================= *)
pose proof (proj1 HJ2) as HARf.
pmkst HS.
apply (HFT fx v fpos (p_ly v) S2 (p_W v) (ms_regs ms0) (ms_mem ms0) _).
unfold INV_FTAKEN.
assert (Hc2 : sa_heap B (p_ly v) S2 (p_c v) seg_spec.SEG_C_SIZE)
  by (destruct Hcheap as (b & m & Hin & H1 & H2); exists b, m; rewrite Eab; auto).
assert (Ht2 : sa_heap B (p_ly v) S2 (p_t v) (pf_len v))
  by (destruct Htheap as (b & m & Hin & H1 & H2); exists b, m; rewrite Eab; auto).
split; [exact HCX0|].
split.
{ (* pf_fi *)
  unfold pf_fi. rewrite Esp0.
  split; [exact HJ2|].
  split; [reflexivity|].
  split; [exists fS2; exact ES2|].
  split; [rewrite Eab; apply Permutation_refl|].
  split.
  { intros j r Hj.
    assert (Hj13 : (j < 13)%nat)
      by (apply (proj1 (nth_error_Some PF_SAVED j)); rewrite Hj; discriminate).
    rewrite <- (HFR0 j r Hj). apply rdword_ext. intros k Hk.
    rewrite K2' by lia. apply HKs; lia. }
  split.
  { rewrite <- Hflag. apply rdword_ext. intros k Hk.
    apply K2'. change (fs_frame_bytes 5) with 2048. lia. }
  split; [exact HFRM|].
  unfold pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - exact (a1_reg_lit _ 2 (2%bv : bv 5) _ ltac:(vm_compute; reflexivity) V2).
  - exact (a1_reg_lit _ 3 (3%bv : bv 5) _ ltac:(vm_compute; reflexivity) V3).
  - exact (a1_reg_lit _ 4 (4%bv : bv 5) _ ltac:(vm_compute; reflexivity) V4).
  - exact (a1_reg_lit _ 8 (8%bv : bv 5) _ ltac:(vm_compute; reflexivity) V8).
  - exact (a1_reg_lit _ 9 (9%bv : bv 5) _ ltac:(vm_compute; reflexivity) V9).
  - exact (a1_reg_lit _ 22 (22%bv : bv 5) _ ltac:(vm_compute; reflexivity) V22). }
split.
{ (* pf_obj *)
  unfold pf_obj.
  split.
  { (* sa_str at t *)
    destruct ST as [[Hzs Hn0] _].
    split; [split; [|exact Hn0]|].
    - intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      destruct Htheap as (b & m & Hin & H1 & H2). unfold pf_len in H2.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm0).
      pose proof (req_size_pos m ltac:(lia)) as [_ Hq2].
      rewrite <- (Hzs i Hi).
      replace (p_t v + Z.of_nat i) with (b + (p_t v - b + Z.of_nat i)) by lia.
      apply (KB b m (p_t v - b + Z.of_nat i) Hin ltac:(lia)).
    - apply (a1_tail_of_heap (p_ly v) S2 (p_W v) (ms_mem ms0) _ (p_t v) (Z.of_nat (length (p_s v))) HARf);
        [exact Ht2 | lia]. }
  split.
  { apply (a1_sa_addr_of_heap (p_ly v) S2 (p_W v) (ms_mem ms0) _ (p_t v) (pf_len v) HARf Ht2);
      [lia | unfold pf_len; lia]. }
  split; [exact Ht2|].
  split.
  { apply (a1_sa_addr_of_heap (p_ly v) S2 (p_W v) (ms_mem ms0) _ (p_c v) seg_spec.SEG_C_SIZE HARf Hc2);
      [lia | unfold seg_spec.SEG_C_SIZE; lia]. }
  split; [exact Hc2|].
  split; [exact (a1_sa_cat_keep (p_W v) (p_mem v) (ms_mem ms0) catA CAT KI)|].
  split; [intros x Hx; exact (a1_sa_lit_keep (p_W v) (p_mem v) (ms_mem ms0) _ _ (LITS x Hx) KI)|].
  split.
  { intros a Hro Ho He. pose proof (pf_a5_k.a5_ro_img VRO a Hro) as Hia. rewrite (KI a Hia Ho He).
    exact (HROD a Hro Ho He). }
  exact (SSPX (p_ly v) S2 (p_W v) (ms_mem ms0) _ HARf). }
split.
{ (* pf_lab *)
  unfold pf_lab.
  destruct (p_lab v) as [l|] eqn:ELAB.
  - rewrite ?ELAB in HOSTR, HLABM.
    cbn [sa_ostr] in HOSTR. destruct HOSTR as (Hlp0 & [[Hlz Hln0] Hlt]).
    destruct HLABM as (HLEN & HLOC & HLADDR & HLDJ).
    assert (HBY : forall i, (i < length (l ++ [0%Z]))%nat ->
      rdW (p_W v) (ms_mem ms0) (p_lp v + Z.of_nat i) = rdW (p_W v) (p_mem v) (p_lp v + Z.of_nat i)).
    { intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
      destruct HLOC as [Hh | [Hf | (Hi1 & Hi2 & Hi3)]].
      - destruct Hh as (b & m & Hin & H1 & H2).
        destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm0).
        pose proof (req_size_pos m ltac:(lia)) as [_ Hq2].
        replace (p_lp v + Z.of_nat i) with (b + (p_lp v - b + Z.of_nat i)) by lia.
        apply (KB b m (p_lp v - b + Z.of_nat i) Hin ltac:(lia)).
      - destruct Hf as (cid & pos & Hin & Hcid & H1 & H2).
        apply (KF cid pos _ Hin Hcid). left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
      - destruct (Hi1 (p_lp v + Z.of_nat i) ltac:(lia)) as (Hm & Ho & He). exact (KI _ Hm Ho He). }
    split.
    { cbn [sa_ostr]. split; [exact Hlp0|]. split; [split|].
      - intros i Hi. rewrite (HBY i Hi). exact (Hlz i Hi).
      - exact Hln0.
      - destruct HLOC as [Hh | [Hf | (Hi1 & Hi2 & Hi3)]].
        + apply (a1_tail_of_heap (p_ly v) S2 (p_W v) (ms_mem ms0) _ (p_lp v) (Z.of_nat (length l)) HARf);
            [destruct Hh as (b & m & Hin & H1 & H2); exists b, m; rewrite Eab; auto | lia].
        + destruct Hf as (cid & pos & Hin & Hcid & H1 & H2).
          destruct (frame_al64 SEGS B (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) cid pos HAR Hin)
            as (HA1 & HA2 & HA3).
          assert (HFm8 : frame_addr (p_ly v) cid pos mod 8 = 0).
          { apply Z.mod_divide in HA1; [|lia]. destruct HA1 as [q Hq]. rewrite Hq.
            replace (q * 64) with ((q * 8) * 8) by lia. apply Z_mod_mult. }
          assert (HM8 : (frame_addr (p_ly v) cid pos + fs_frame_bytes cid) mod 8 = 0).
          { apply Z.mod_divide in HA2; [|lia]. destruct HA2 as [q2 Hq2].
            rewrite Zplus_mod, HFm8, Hq2.
            replace (q2 * 64) with ((q2 * 8) * 8) by lia. rewrite Z_mod_mult. reflexivity. }
          intros a Ha.
          rewrite (KF cid pos a Hin Hcid); [exact (Hlt a Ha)|].
          left. unfold in_zr, frame_rng. cbn [fst snd].
          pose proof (a1_floor_ge (p_lp v + Z.of_nat (length l)) (frame_addr (p_ly v) cid pos) HFm8
            ltac:(lia)) as Hfl.
          pose proof (a1_ceil_le (p_lp v + Z.of_nat (length l))
            (frame_addr (p_ly v) cid pos + fs_frame_bytes cid) HM8 ltac:(lia)) as Hcl.
          pose proof (Z.div_mod (p_lp v + Z.of_nat (length l)) 8 ltac:(lia)) as D1.
          pose proof (Z.mod_pos_bound (p_lp v + Z.of_nat (length l)) 8 ltac:(lia)) as D2.
          lia.
        + exact (Hi3 (p_ly v) S2 (p_W v) (ms_mem ms0) _ HARf). }
    split.
    { destruct HLOC as [Hh | [Hf | (Hi1 & Hi2 & Hi3)]].
      - left. destruct Hh as (b & m & Hin & H1 & H2). exists b, m. rewrite Eab. auto.
      - right. left. destruct Hf as (cid & pos & Hin & Hcid & H1 & H2). exists cid, pos.
        split; [rewrite Hfrs2; right; exact Hin|]. auto.
      - right. right. exact Hi1. }
    destruct HLOC as [Hh | [Hf | (Hi1 & Hi2 & Hi3)]].
    + apply (a1_sa_addr_of_heap (p_ly v) S2 (p_W v) (ms_mem ms0) _ (p_lp v) (Z.of_nat (length l) + 1) HARf);
        [destruct Hh as (b & m & Hin & H1 & H2); exists b, m; rewrite Eab; auto | lia | lia].
    + destruct Hf as (cid & pos & Hin & Hcid & H1 & H2).
      destruct (frame_al64 SEGS B (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) cid pos HAR Hin)
        as (HA1 & HA2 & HA3).
      apply Z.mod_divide in HA1; [|lia]. apply Z.mod_divide in HA2; [|lia].
      destruct HA1 as [q Hq]. destruct HA2 as [q2 Hq2].
      assert (Hq8 : frame_addr (p_ly v) cid pos / 8 = q * 8)
        by (rewrite Hq; replace (q * 64) with (q * 8 * 8) by lia; apply Z.div_mul; lia).
      assert (Hq28 : fs_frame_bytes cid / 8 = q2 * 8)
        by (rewrite Hq2; replace (q2 * 64) with (q2 * 8 * 8) by lia; apply Z.div_mul; lia).
      apply (a1_sa_addr_kept (rdW (p_W v) (p_mem v)) _ (p_lp v) (Z.of_nat (length l) + 1));
        [|lia|exact HLADDR].
      intros s Hs. apply (KF cid pos s Hin Hcid). right.
      unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Hq8, Hq28.
      assert (HSm8 : (SHADOW_OFF + q * 8) mod 8 = 0)
        by (unfold SHADOW_OFF; replace (2147450880 + q * 8) with ((268431360 + q) * 8) by lia; apply Z_mod_mult).
      assert (HEm8 : (SHADOW_OFF + q * 8 + q2 * 8) mod 8 = 0)
        by (unfold SHADOW_OFF; replace (2147450880 + q * 8 + q2 * 8) with ((268431360 + q + q2) * 8) by lia;
            apply Z_mod_mult).
      assert (Hlo : SHADOW_OFF + q * 8 <= SHADOW_OFF + p_lp v / 8).
      { assert (Hd : frame_addr (p_ly v) cid pos / 8 <= p_lp v / 8) by (apply Z.div_le_mono; lia).
        rewrite Hq8 in Hd. lia. }
      assert (Hhi : SHADOW_OFF + (p_lp v + (Z.of_nat (length l) + 1) - 1) / 8 < SHADOW_OFF + q * 8 + q2 * 8).
      { assert (Hd : (p_lp v + Z.of_nat (length l)) / 8 < q * 8 + q2 * 8)
          by (apply Z.div_lt_upper_bound; lia).
        replace (p_lp v + (Z.of_nat (length l) + 1) - 1) with (p_lp v + Z.of_nat (length l)) by lia. lia. }
      pose proof (a1_floor_ge (SHADOW_OFF + p_lp v / 8) (SHADOW_OFF + q * 8) HSm8 Hlo) as Hf1.
      pose proof (a1_ceil_le (SHADOW_OFF + (p_lp v + (Z.of_nat (length l) + 1) - 1) / 8)
        (SHADOW_OFF + q * 8 + q2 * 8) HEm8 Hhi) as Hf2.
      unfold shadow_addr in Hs. lia.
    + exact (Hi2 (p_ly v) S2 (p_W v) (ms_mem ms0) _ HARf).
  - rewrite ?ELAB in HOSTR. cbn [sa_ostr] in HOSTR. split; [exact HOSTR | exact I]. }
split.
{ (* sa_rconf c rcs *)
  destruct RC as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
  intros i Hi. pose proof (proj1 Henc) as HL.
  destruct Hcheap as (b & m & Hin & H1 & H2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm0).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hq2].
  unfold seg_spec.SEG_C_SIZE in H2, HL.
  rewrite <- (Hbs i Hi).
  replace (p_c v + Z.of_nat i) with (b + (p_c v - b + Z.of_nat i)) by lia.
  apply (KB b m (p_c v - b + Z.of_nat i) Hin ltac:(lia)). }
split.
{ (* zero_shadow of the frame *)
  assert (Hd : 0 <= pf_F v fpos / 8) by (apply Z.div_pos; lia).
  assert (Hd2 : pf_F v fpos / 8 <= pf_F v fpos) by (apply Z.div_le_upper_bound; lia).
  intros i Hi. change (fs_frame_bytes 5 / 8) with 256 in Hi.
  rewrite K2' by (unfold shadow_of_addr, SHADOW_OFF; lia). exact (Hz i Hi). }
(* the FTAKEN registers *)
unfold pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
- exact (a1_reg_lit _ 10 (10%bv : bv 5) _ ltac:(vm_compute; reflexivity) V10).
- exact (a1_reg_lit _ 23 (23%bv : bv 5) _ ltac:(vm_compute; reflexivity) V23).
- exact (a1_reg_lit _ 24 (24%bv : bv 5) _ ltac:(vm_compute; reflexivity) V24).
- exact (a1_reg_lit _ 25 (25%bv : bv 5) _ ltac:(vm_compute; reflexivity) V25).
- exact (a1_reg_lit _ 19 (19%bv : bv 5) _ ltac:(vm_compute; reflexivity) V19).
- exact (a1_reg_lit _ 26 (26%bv : bv 5) _ ltac:(vm_compute; reflexivity) V26).
Qed.
End x.

Theorem pf_a1_holds : S_A1 B.
Proof. unfold S_A1. intros f0 HFT. exact (pf_a1_entry (fx := f0) HFT). Qed.

End e.
End f.
End d.
