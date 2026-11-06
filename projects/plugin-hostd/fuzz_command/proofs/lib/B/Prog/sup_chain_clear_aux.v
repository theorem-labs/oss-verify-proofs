(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the callee-free helpers of the walk of sup_chain_clear on plugin-hostd/fuzz_command's
   ASan+UBSan build (fuzz_command.asan-ubsan), for a Theorem Labs lane's lib/B/Prog/sup_chain_clear_c.v. The arithmetic of the
   realigned frame and the entry state are lib/A/Prog/answer_code.v's (a working branch 2ba4488ce71:
   land_m32, denot_and32, denot_add0, denot_off0, sp1_facts, ac_entry), moved to lib/B and to sup_chain_clear's
   B prologue; nothing here names a callee's statement. *)
(* sup_chain_clear on B (entry BASE + AF_sup_chain_clear = 0x8c570, 122 instructions, 0x8c570 .. 0x8c754 `ret`):
   `addi sp,sp,-96`, `sd zero,0(sp)`, ra and s0 .. s8 to sp + 88 .. sp + 16, `addi s0,sp,96`, `andi sp,sp,-32`
   (0x8c5a4), s1 = the realigned sp; the shadow base through the GOT word 0xa5f50 (A_OBJ 0) and the cell 0xb0c38
   (A_OBJ 12); the use-after-return flag through the GOT word 0xa5fa8 (A_OBJ 1) and the record's const cell; the
   class-0 side-stack frame from __asan_stack_malloc_0 (0x8c5d0), `sd s7,8(s1)` (0x8c604), the frame header (magic,
   descriptor 0x15923 = A_OBJ 59, pc 0x8c570 = A_OBJ 81) and its shadow f1 f1 f1 f1 f8 f8 f3 f3. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05 YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdSnText.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---------- the realigned frame: sp1 = (sp - 96) & -32 (CmdSnText.snt_land_m32 masks the low 5 bits) ---------- *)
(* the symbolic value of sp after `addi sp,sp,-96; andi sp,sp,-32` (0x8c570, 0x8c5a4) *)
Lemma scc_denot_and32 : forall E n v, ew E n = Z_to_bv 64 v -> 96 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))) = Z_to_bv 64 (32 * ((v - 96) / 32)).
Proof.
intros E n v Hn Hv.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))))). f_equal.
change (U E (SAlu ALU_AND (SOff n (-96)) (SLit (-32))) = 32 * ((v - 96) / 32)).
rewrite U_SAlu, U_SOff, U_SLit, Hn. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
unfold zcanon, M64. rewrite (Z.mod_small (v + -96)) by lia.
replace (-32 mod 2 ^ 64) with (2 ^ 64 - 32) by reflexivity.
rewrite CmdSnText.snt_land_m32 by lia. replace (v + -96) with (v - 96) by lia.
pose proof (Z.div_pos (v - 96) 32 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (v - 96) 32 ltac:(lia)).
apply Z.mod_small. lia.
Qed.

(* `mv s1, sp` (0x8c5a8) is `addi s1, sp, 0` *)
Lemma scc_denot_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD e (SLit 0)))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E e)). f_equal.
change (U E (SAlu ALU_ADD e (SLit 0)) = U E e). rewrite U_SAlu, U_SLit. cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite Z.add_0_r.
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. unfold U. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma scc_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* sp1 lies 96 or 112 bytes below the entry sp, 32-aligned *)
Lemma scc_sp1_facts : forall sp, sp mod 16 = 0 -> 2 ^ 46 <= sp ->
sp - 112 <= 32 * ((sp - 96) / 32) <= sp - 96 /\ (32 * ((sp - 96) / 32)) mod 32 = 0 /\
(32 * ((sp - 96) / 32) - sp) mod 16 = 0.
Proof.
intros sp H16 Hlo.
pose proof (Z.div_mod (sp - 96) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp - 96) 32 ltac:(lia)) as M.
assert (Hm : (sp - 96) mod 32 = 0 \/ (sp - 96) mod 32 = 16).
{ pose proof (Z.div_mod sp 16 ltac:(lia)) as D2. rewrite H16 in D2. lia. }
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
destruct Hm as [Hm|Hm].
- replace (32 * ((sp - 96) / 32) - sp) with (-96) by lia. reflexivity.
- replace (32 * ((sp - 96) / 32) - sp) with (-112) by lia. reflexivity.
Qed.

(* ---------- the symbolic state at the entry 0x8c570 ---------- *)
(* the regions the walk writes or reads before the first call: the word `sd zero,0(sp)` stores (entry sp - 96), the
   ten saved registers (entry sp - 80 .. entry sp), the word `sd s7,8(s1)` stores (sp1 + 8, atom 34 = sp1), the
   shadow base's GOT word and cell (atom 32 = SB), the use-after-return flag's GOT word and cell (atom 33 = the
   cell) *)
Definition scc_regions0 : smem := [
 YP09.mkRegion (Some 2%nat) (-96) (-88) (-96) (-88) [];
 YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 [];
 YP09.mkRegion (Some 34%nat) 8 16 8 16 [];
 got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition scc_facts0 : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (34%nat, mkAF (2^46) (2^47) 5)] [] [].
Definition ss_scc0 : sstate := mkSS AF_sup_chain_clear sr_atoms scc_regions0 None scc_facts0.

(* the class-0 side-stack frame (atom 1028 = its address F, 64 bytes; atom 1040 = its flag cell, the word at F + 56;
   atom 1041 = its shadow SB + F / 8, 8 bytes), as answer_code.v's fr_hdr / fr_flg / fr_shd for class 1: the header
   F + 0 .. F + 24 (magic, descriptor, pc) is written at 0x8c630 .. 0x8c638, the flag word read at 0x8c6f8, the
   eight shadow bytes written at 0x8c640 .. 0x8c660, 0x8c670 / 0x8c674, 0x8c69c / 0x8c6a0 and 0x8c6d8 .. 0x8c6f4 *)
Definition scc_fr_hdr : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 24 [].
Definition scc_fr_flg : YP09.region :=
YP09.mkRegion (Some 1028%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))].
Definition scc_fr_shd : YP09.region := YP09.mkRegion (Some 1041%nat) 0 8 0 8 [].
(* the shadow address of the frame as the walk computes it: (F >> 3) + SB (0x8c618, 0x8c61c) *)
Definition scc_shx_F : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0).

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
(* the walk hypotheses (cgif's names, as answer_code.v's): the shadow base's and the use-after-return flag's GOT
   words and cells *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* the extra atoms of the entry environment: 32 = SB, 33 = the use-after-return cell, 34 = sp1 *)
Definition scc_extra (sp1 : Z) : list word := map (Z_to_bv 64) [SB; as_uar_cell B; sp1].

(* the entry: any stack budget of at least the frame and its realignment (96 + 16) *)
Lemma scc_entry : forall STK W ly S regs mem md ch, 112 <= STK ->
afn_pre SEGS B STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (scc_extra (32 * ((spZ regs - 96) / 32))))) ss_scc0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_chain_clear)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch HSTK HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 1 ltac:(lia)) as HO1. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
rewrite restrict_mkst_fx.
set (sp1 := 32 * ((spZ regs - 96) / 32)).
destruct (scc_sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
(* sp1 is 96 or 112 bytes below the entry sp: the word `sd s7,8(s1)` stores lies apart from the two frame pieces *)
assert (Hsp1c : sp1 = spZ regs - 96 \/ sp1 = spZ regs - 112).
{ pose proof (Z.div_mod (sp1 - spZ regs) 16 ltac:(lia)) as D. rewrite Hsp1b in D. lia. }
set (E := Eimg (Ereg regs (scc_extra sp1))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (U34 : base_val E (Some 34%nat) = sp1) by (apply VB; [exact E34 | lia]).
assert (U0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact E241 | lia]).
assert (U1 : base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply VB; [exact E242 | lia]).
assert (U12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact E253 | lia]).
assert (U33 : base_val E (Some 33%nat) = as_uar_cell B) by (apply VB; [exact E33 | lia]).
assert (U2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
unfold ss_scc0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold scc_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U34. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[rewrite scc_denot_off0; exact E253 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
[rewrite scc_denot_off0; exact E32 | unfold SB; lia | lia |].
rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
[rewrite scc_denot_off0; exact E33 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents. unfold scc_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U34, U0, U1, U12, U33.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
destruct Hsp1c as [Hc|Hc]; repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [scc_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
rewrite Hal16, Hsp1a. unfold SB. repeat split; lia.
Qed.
End e.
End f.
End d.
Print Assumptions scc_entry.
