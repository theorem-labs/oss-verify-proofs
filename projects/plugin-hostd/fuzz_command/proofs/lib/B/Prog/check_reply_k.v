(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/check_reply_k.v (the ASan walk, a working branch 91059853ab1) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B, entry 0x86e64): the program points, g_rec and the GOT objects at B's addresses (a Theorem Labs lane's pairing, a Theorem Labs lane's reloc). *)
(* Modified by Theorem Labs, 2026-10: the walk kit of check_reply (fuzz_command.asan-ubsan, 0x86e64), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cgif_close's kit: program points, the symbolic regions, facts and
   shadow entries, the entry seed) and A/ACa2.v (a walk with a class-1 side-stack frame).

   The symbolic state at the entry (atoms 0..31 are the registers at the entry):
     32 SB (the shadow base, Bx)         33 g_rec (0x5e32c0)          34 the reply block rep
     35 g_rec.reply_size = |reply| + 1     36 rep + |reply|, the reply's NUL byte
     37 w->w (mod 2^64)                    38 w->n                      39 w->w[0] (mod 2^64)
     40 the use-after-return flag cell     41 the realigned stack pointer (sp - 128) & -32
   The prologue realigns sp with `andi sp,sp,-32` (0x86ea0); the alias of atom 41 names the result, so the store
   `sd s7,24(s1)` (0x86f7c) lands in a region of its own. The reply's last byte is read through a computed address
   rep + (size - 1) (0x86fc8); the alias of atom 36 names it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall CmdBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* program points, as listing offsets (address - 0x86530) *)
Definition CR_RET_SM : Z := 0x9a0.      (* 0x86ed0, after __asan_stack_malloc_1 *)
Definition CR_MEMCHR : Z := 0xacc.      (* 0x86ffc, the memchr call *)
Definition CR_RET_MEMCHR : Z := 0xad0.  (* 0x87000 *)
Definition CR_RET_CRA : Z := 0xadc.     (* 0x8700c, after check_reply_answer *)
Definition CR_RET_SRC : Z := 0xaec.     (* 0x8701c, after sup_reply_code *)
Definition CR_STRLEN : Z := 0xb50.      (* 0x87080, the strlen call *)
Definition CR_RET_STRLEN : Z := 0xb54.  (* 0x87084 *)
Definition CR_RET_RSO : Z := 0xb60.     (* 0x87090, after rec_shape_of *)
Definition CR_SNPRINTF : Z := 0xb80.    (* 0x870b0, the snprintf call *)
Definition CR_RET_SNP : Z := 0xb84.     (* 0x870b4 *)
Definition CR_RET_RCD : Z := 0xb8c.     (* 0x870bc, after rec_code_declared *)
Definition CR_STRCMP : Z := 0xba0.      (* 0x870d0, the strcmp call *)
Definition CR_RET_STRCMP : Z := 0xba4.  (* 0x870d4 *)
Definition CR_JOIN : Z := 0xbb4.        (* 0x870e4, the shape join *)
Definition CR_RET_SRM1 : Z := 0xbc4.    (* 0x870f4, after the first syntax_reply_matches *)
Definition CR_RET_SRM2 : Z := 0xbe0.    (* 0x87110, after the second *)
Definition CR_EPI : Z := 0xbe4.         (* 0x87114, the epilogue *)

Definition SBc : Z := 0x7fff8000.
Lemma SBc_SHADOW_OFF : SBc = SHADOW_OFF. Proof. reflexivity. Qed.
Definition crBx : sv := SOff 32 0.
Definition crSpan : Z * Z := (SBc, SBc + 2 ^ 44 - 1).

(* the realigned stack pointer *)
Definition sp1_of (sp : Z) : Z := sp - 128 - (sp - 128) mod 32.

(* the regions at the entry: the prologue's stores, the shadow-base and use-after-return GOT words and cells *)
Definition cr_stk0 : YP09.region := YP09.mkRegion (Some 2%nat) (-128) (-120) (-128) (-120) [].
Definition cr_stk1 : YP09.region := YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 [].
Definition cr_slot : YP09.region := YP09.mkRegion (Some 41%nat) 24 32 24 32 [].
Definition cr_uargot : YP09.region := YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 40 0))].
Definition cr_uarcell : YP09.region := YP09.mkRegion (Some 40%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition cr_regions0 : smem := [cr_stk0; cr_stk1; cr_slot; got_regionP; bcell_regionP 32; cr_uargot; cr_uarcell].

(* the regions the walk adds after the frame call: g_rec's GOT word and fields, the reply's NUL byte, w's fields *)
Definition cr_grecgot : YP09.region := YP09.mkRegion (Some (A_OBJ 2)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition cr_grec : YP09.region :=
YP09.mkRegion (Some 33%nat) 920 944 0 0
[YP09.mkChunk 920 (CVal 4 (SLit 1)); YP09.mkChunk 928 (CVal 8 (SOff 34 0)); YP09.mkChunk 936 (CVal 8 (SOff 35 0))].
Definition cr_nul : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition cr_words : YP09.region :=
YP09.mkRegion (Some 10%nat) 16 28 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 4 (SOff 38 0))].

Definition HPc : afact := mkAF 4096 140737479966720 4.
Definition cr_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47) 3); (32%nat, mkAF SBc SBc 0);
  (33%nat, mkAF 0x5e32c0 0x5e32c0 3); (34%nat, HPc); (35%nat, mkAF 1 8194 0);
  (36%nat, mkAF 4096 140737479966720 0); (38%nat, mkAF 0 2147483647 0); (40%nat, mkAF 65536 6316032 2);
  (41%nat, mkAF (2 ^ 46) (2 ^ 47) 5) ].
Definition cr_alias0 : list (sv * sv) :=
[ (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32)), SOff 41 0); (SAlu ALU_ADD (SOff 34 0) (SOff 35 (-1)), SOff 36 0) ].
Definition cr_facts0 : facts := mkFacts cr_atoms0 [] cr_alias0.
Definition ss_cr0 : sstate := mkSS AF_check_reply sr_atoms cr_regions0 None cr_facts0.

Definition cr_extra (rep nr ww n p0 uar sp : Z) : list word :=
map (Z_to_bv 64) [SBc; 0x5e32c0; rep; nr + 1; rep + nr; ww mod 2 ^ 64; n; p0 mod 2 ^ 64; uar; sp1_of sp].

Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x - x mod 32.
Proof.
intros x Hx.
replace (2 ^ 64 - 32) with (Z.land (Z.ones 64) (Z.lnot (Z.ones 5))) by reflexivity.
rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Definition crE (regs : bvmap 5 word) (rep nr ww n p0 uar : Z) : env :=
Eimg (Ereg regs (cr_extra rep nr ww n p0 uar (spZ regs))).
Lemma regs_ok_crE : forall regs rep nr ww n p0 uar, regs_ok (crE regs rep nr ww n p0 uar) sr_atoms regs.
Proof.
intros. unfold crE. apply (regs_ok_agree 32 (Ereg regs (cr_extra rep nr ww n p0 uar (spZ regs)))).
- split; [intros n0 Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Lemma cr_entry : forall ly S W (regs : bvmap 5 word) mem md ch STK (w rep nr ww n p0 : Z),
afn_pre SEGS B STK ly S W regs mem md ch -> 144 <= STK ->
getr regs 10 = w64 w -> w mod 8 = 0 -> spZ regs <= w -> w + 32 <= ly_stk_hi ly ->
4096 <= rep -> rep mod 16 = 0 -> 0 <= nr -> nr + 1 <= 8194 -> rep + nr + 1 <= 140737479966720 ->
0 <= n < 2 ^ 31 ->
st_ok_pi SEGS VAL (crE regs rep nr ww n p0 (as_uar_cell B)) ss_cr0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_reply)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch STK w rep nr ww n p0 HPRE HSTK H10 Hw8 Hspw Hwhi Hrep Hrep16 Hnr Hnrhi Hrephi Hn.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kgu). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite (palf_got_uar B TLF) in Kgu.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img 1 ltac:(lia)) as HguR. pose proof (palf_sep B TLF) as Hsep.
pose proof pa_B_ok as HBASE.
rewrite restrict_mkst_fx.
set (sp := spZ regs) in *.
set (E := crE regs rep nr ww n p0 (as_uar_cell B)).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (cr_extra rep nr ww n p0 (as_uar_cell B) sp)) k)
by (intros k Hk; subst E; unfold crE; apply Eimg_low; exact Hk).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (cr_extra rep nr ww n p0 (as_uar_cell B) sp) (Z_to_bv 64 0))
by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 w) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 6%nat ltac:(lia)) as E38.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
cbn [Nat.add nth cr_extra map] in E32, E33, E34, E35, E36, E38, E40, E41.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold crE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold crE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold crE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; reflexivity).
assert (Hsp1 : sp1_of sp = sp - 128 - sp mod 32 /\ (sp mod 32 = 0 \/ sp mod 32 = 16)).
{ unfold sp1_of. replace ((sp - 128) mod 32) with (sp mod 32) by (rewrite Zminus_mod; change (128 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
split; [reflexivity|]. pose proof (Z.mod_pos_bound sp 32 ltac:(lia)).
pose proof (Z.div_mod sp 32 ltac:(lia)). pose proof (Z.div_mod sp 16 ltac:(lia)). lia. }
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (Rsp1 : 2 ^ 46 <= sp1_of sp /\ sp1_of sp + 144 <= sp + 16) by (destruct Hsp1 as [Hs1 Hs2]; rewrite Hs1; lia).
assert (Hwr : forall o, sp - 144 <= o < sp -> writable_at SEGS (mrestrict (w_H W) mem) o)
by (intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia).
unfold ss_cr0, AF_check_reply. apply pa_entry_st_ok_full.
+ apply regs_ok_crE.
+ vm_compute. reflexivity.
+ unfold cr_regions0, cr_stk0, cr_stk1, cr_slot, got_regionP, bcell_regionP, cr_uargot, cr_uarcell.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply Hwr. lia.
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply Hwr. lia.
* rewrite (VB 41%nat (sp1_of sp) E41) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply Hwr. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 crBx SBc);
[cbn [sv_denot crBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBc; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 40 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgu).
* rewrite (VB 40%nat (as_uar_cell B) E40) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
+ apply pairwise_disjoint_of_extents.
unfold cr_regions0, cr_stk0, cr_stk1, cr_slot, got_regionP, bcell_regionP, cr_uargot, cr_uarcell, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 41%nat (sp1_of sp) E41) by lia. rewrite (VB 40%nat (as_uar_cell B) E40) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
cbn [zseps zseps_from fst snd] in Hsep.
destruct Hsp1 as [Hs1 Hs2]. rewrite Hs1.
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HcellR HgcD HgotR HguR Huar Hsep Hs2 HSTK. clear. unfold ASAN_CEIL. intros.
repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [cr_facts0 cr_atoms0 f_atoms atoms_ok]. unfold afact_ok, HPc. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, E38, E40, E41, !unsigned_lit_small by (unfold SBc; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
destruct Hsp1 as [Hs1 Hs2]. rewrite Hs1.
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 Hal16 Hw8 Hspw Hwhi Hrep Hrep16 Hnr Hnrhi Hrephi Hn Huar Huar4 Hs2 HSTK. clear. unfold SBc, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; try lia.
all: try (rewrite Zminus_mod, Z.mod_mod, Zminus_mod_idemp_r by lia; replace (sp - 128 - sp mod 32) with ((sp / 32 - 4) * 32) by (pose proof (Z.div_mod sp 32 ltac:(lia)); lia); apply Z_mod_mult).
all: try (replace (sp - 128 - sp mod 32) with ((sp / 32 - 4) * 32) by (pose proof (Z.div_mod sp 32 ltac:(lia)); lia); apply Z_mod_mult).
all: try reflexivity.
* cbn [cr_facts0 cr_alias0 f_alias alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_SAlu, U_SOff, U_SLit, U_SOff. cbn [zalu_raw]. rewrite Usp, E41, unsigned_lit_small by lia.
destruct Hsp1 as [Hs1 Hs2]. rewrite Hs1.
rewrite (zcanon_id (sp + -128)) by (unfold M64; lia). change (zcanon (-32)) with (2 ^ 64 - 32).
rewrite land_m32 by lia.
assert (Hm : (sp + -128) mod 32 = sp mod 32) by (replace (sp + -128) with (sp + (-4) * 32) by lia; apply Z_mod_plus_full).
rewrite Hm. rewrite !zcanon_id by (unfold M64; lia). lia.
-- apply U_inj. rewrite U_SAlu, !U_SOff. cbn [zalu_raw]. rewrite E34, E35, E36, !unsigned_lit_small by lia.
rewrite (zcanon_id (rep + 0)), (zcanon_id (nr + 1 + -1)), (zcanon_id (rep + nr + 0)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

End e.
End f.
End d.
