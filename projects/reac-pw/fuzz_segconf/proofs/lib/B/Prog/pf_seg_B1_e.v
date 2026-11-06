(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: chain_words' walk on the ASan build of plugin-hostd/fuzz_command, segment S1
   (chain_words_d.v cw_S1P): from the entry (0x8dfd4) through __asan_stack_malloc_3 (0x8e044) to the refusal cut KR
   (0x8e278) or the first-check cut KC (0x8e1ec). In the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v (entry,
   aj_stack_malloc_atS, re-seat) with the entry seed of lib/A/Prog/numberE.v: a run to the call, the call, a re-seat
   that keeps the three stack regions and adds the frame (the call's a0) and its shadow (the alias of
   (s8 >> 3) + s7), a plain run through the 88 shadow stores to the branch on ntok < 3, and the cut facts (cw_pc)
   read back from the symbolic state at the cut. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s1.v, with its module paths, module names and numbers changed; 57 of its 147 lines of code are new or changed and 476 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the symbolic
   entry state of reac_segconf_parse_file (0x87e38 = BASE + AF_reac_segconf_parse_file, B's SegList.v) for segment B1
   of its walk (lib/B/Prog/pf_seg_B1.v), and its seed lemma. The B1 segment lane of the image-B G3 walk owner, 2026-10-30. ADAPTED from
   the entry seed of refuse's image-B walk (the image-B refuse walk lane, lib/B/Prog/refuse_E.v: numberE.v's form, origin/ossv/recipes
   501c0d516c69 proofs/plugin-hostd/fuzz_command/lib/B/Prog/numberE.v), re-derived on parse_file's image-B prologue
   (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s, 0x87e38 .. 0x87eac):
     0x87e38 addi sp,sp,-352; 0x87e3c sd zero,0(sp)            the probe word at sp0 - 352            (b1_stk_lo)
     0x87e40 .. 0x87e70 sd ra,344(sp) .. sd s11,248(sp)       ra .. s11 at sp0 - 8 .. sp0 - 104       (b1_stk_hi)
     0x87e74 addi s0,sp,352; 0x87e78 andi sp,sp,-32; 0x87e7c mv s1,sp   s1 = sp1 = (sp0 - 352) & -32 (atom 33)
     0x87e80 mv s3,a2; 0x87e84 mv s11,a1
     0x87e88 / 0x87e94 auipc a1 / ld a1,904(a1)               GOT word 0xa3210 (listing object 0)    (got_regionP)
     0x87e8c / 0x87e90 auipc a2 / ld a2,988(a2)               GOT word 0xa3268 (listing object 1)    (uar_got_regionP)
     0x87e98 lw a2,0(a2)                                      the use-after-return flag, AR's 1       (uar_cell_regionP)
     0x87e9c ld s4,0(a1)                                      the shadow base, AR's SHADOW_OFF        (bcell_regionP)
     0x87ea0 sd a0,200(s1)                                    c to slot sp1 + 0xc8                    (b1_stk_c)
     0x87ea4 beqz a2 (not taken: a2 = 1); 0x87ea8 li a0,1152; 0x87eac jal frame_alloc_5 (__asan_stack_malloc_5)
   sp1 is sp0 - 352 or sp0 - 368 (sp0 is 16-aligned), so the three stack regions are disjoint: [sp0 - 352, sp0 - 344),
   [sp1 + 200, sp1 + 208) inside [sp0 - 168, sp0 - 144), [sp0 - 104, sp0).
   Atoms: 0-31 the registers, 32 the shadow base SB, 33 sp1, 34 the use-after-return flag cell. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation B1_SB := 32%nat (only parsing). Notation B1_SP1 := 33%nat (only parsing). Notation B1_UAR := 34%nat (only parsing).
(* the realigned locals base s1 (0x87e78 andi sp,sp,-32 after 0x87e38 addi sp,sp,-352); pf_pieces.v's pf_s1 *)
Definition b1sp1 (sp0 : Z) : Z := (sp0 - 0x160) - (sp0 - 0x160) mod 32.
(* the listing offset of frame_alloc_5's return (0x87eb0) *)
Definition B1_SM_RET : Z := AF_reac_segconf_parse_file + 0x78.
Definition b1_stk_lo : YP09.region := YP09.mkRegion (Some 2%nat) (-352) (-344) (-352) (-344) [].
Definition b1_stk_hi : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition b1_stk_c : YP09.region := YP09.mkRegion (Some B1_SP1) 200 208 200 208 [].
Definition b1_regions0 : smem :=
[ b1_stk_lo; b1_stk_hi; b1_stk_c; got_regionP; bcell_regionP B1_SB; uar_got_regionP B1_UAR; uar_cell_regionP B1_UAR ].
Definition b1_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (B1_SP1, mkAF (2^46) (2^47) 5); (B1_SB, mkAF SB SB 0); (B1_UAR, mkAF 0x10000 kImgEnd 2) ].
Definition b1_alias0 : list (sv * sv) := [ (SAlu ALU_AND (SOff 2 (-352)) (SLit (-32)), SOff B1_SP1 0) ].
Definition ss_b0 : sstate := mkSS AF_reac_segconf_parse_file sr_atoms b1_regions0 None (mkFacts b1_atoms0 [] b1_alias0).
Definition b1_extra (sp0 uar : Z) : list word := map (Z_to_bv 64) [SB; b1sp1 sp0; uar].
Lemma b1sp1_facts : forall sp0, sp0 mod 16 = 0 ->
b1sp1 sp0 mod 32 = 0 /\ (b1sp1 sp0 = sp0 - 352 \/ b1sp1 sp0 = sp0 - 368).
Proof.
intros sp0 H. unfold b1sp1. pose proof (Z.mod_pos_bound (sp0 - 0x160) 32 ltac:(lia)) as M.
assert (Hm : (sp0 - 0x160) mod 32 = 0 \/ (sp0 - 0x160) mod 32 = 16).
{ pose proof (Z.div_mod (sp0 - 0x160) 32 ltac:(lia)) as D. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
  rewrite H in D2. lia. }
split; [|lia].
replace ((sp0 - 0x160) - (sp0 - 0x160) mod 32) with (32 * ((sp0 - 0x160) / 32))
  by (pose proof (Z.div_mod (sp0 - 0x160) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma b1sp1_and : forall sp0, 0 <= sp0 - 352 < 2 ^ 64 ->
alu64 ALU_AND (Z_to_bv 64 (sp0 - 352)) (Z_to_bv 64 (-32)) = Z_to_bv 64 (b1sp1 sp0).
Proof.
intros sp0 H. rewrite and_lit_Z. f_equal. rewrite zcanon_id by (unfold M64; lia).
change (zsigned64 (-32)) with (- 2 ^ 5). rewrite land_neg_pow2 by lia. reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the seed: the symbolic entry state holds at parse_file's entry (afn_pre and the stack it asks) *)
Lemma b1_entry : forall STK W ly S regs mem md ch,
afn_pre SEGS B STK ly S W regs mem md ch -> 368 <= STK ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (b1_extra (spZ regs) (as_uar_cell B)))) ss_b0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_parse_file)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch HPRE HSTK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
set (sp0 := spZ regs) in *.
destruct (b1sp1_facts sp0 Hal16) as (Hs1al & Hs1).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (b1_extra sp0 (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (b1_extra sp0 (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth b1_extra map] in E32, E33, E34. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hkimg : kImgEnd = 0x602000) by reflexivity.
unfold ss_b0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b1_regions0, b1_stk_lo, b1_stk_hi, b1_stk_c, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB B1_SP1 (b1sp1 sp0) E33) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff B1_SB 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff B1_UAR 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB B1_UAR (as_uar_cell B) E34) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold b1_regions0, b1_stk_lo, b1_stk_hi, b1_stk_c, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB B1_SP1 (b1sp1 sp0) E33), (VB B1_UAR (as_uar_cell B) E34) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Hob0 Hob1 Hob12 Huar Hsep Hs1 Hkimg. clear. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I|]].
2: { cbn [f_alias alias_ok b1_alias0]. split; [|exact I]. cbn [sv_denot]. rewrite Usp, E33, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite <- (b1sp1_and sp0) by lia. reflexivity. }
cbn [f_atoms atoms_ok b1_atoms0]. unfold afact_ok; cbn [af_lo af_hi af_al2];
rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold SB, kImgEnd in *; lia);
change (2 ^ 5) with 32; change (2 ^ 4) with 16; change (2 ^ 2) with 4; rewrite !Z.pow_0_r, !Z.mod_1_r;
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Huar Huar4 Hs1al Hs1 Hal16 Hkimg; clear; unfold SB; intros;
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End e.
End f.
End d.
