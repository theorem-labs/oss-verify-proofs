(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AC9z.v (the entry state of a walk): the symbolic state at number's entry (0x8e430) and its seed lemma. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberE.v, with its module paths, module names and numbers changed; 147 of its 259 lines of code are new or changed and 133 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3...): the symbolic
   entry state of refuse (0x892f8 = BASE + AF_refuse, B listing lib/B/Prog/SegList.v) and its seed lemma, in the form
   of plugin-hostd/fuzz_command lib/B/Prog/numberE.v (origin/ossv/recipes 501c0d516c69; number is the released class-0
   walk). The image-B refuse walk lane of the image-B G3 walk owner, 2026-10-30; ADAPTED from numberE.v to refuse's image-B code
   (refuse.fuzz_segconf.asan-ubsan.s).

   refuse's prologue (0x892f8-0x89374) writes: the probe `sd zero,0(sp)` at sp - 160 (r_stk_lo); the twelve saved
   registers at sp - 144 .. sp - 48 and the variadic a3 .. a7 at s0 + 8 .. s0 + 40 = sp - 40 .. sp (r_stk_hi; the
   word at sp - 48 is not written); and, after the side-stack frame take, `sd s7,8(s1)` at sp1 + 8 with sp1 = (sp -
   160) & -32 (r_stk_s1). It reads the shadow base through the GOT word 0xa3210 (listing object 0) and the
   use-after-return flag through 0xa3268 (object 1), both the kit's constant cells (got_regionP, bcell_regionP,
   uar_got_regionP, uar_cell_regionP). Of the reader's block c it reads n_refusals (c + 0x34c8) and refused
   (c + 0x34cc) as 4-byte words and stores refused + 1 (r_cnt: refused writable; n_refusals is made writable only
   on the path that stores it), and reads c->reading[0] (c + 0x4080, r_rd0).

   Atoms: 0-31 the registers, 32 the shadow base SB, 33 sp1, 34 the use-after-return flag cell, 35 n_refusals,
   36 refused, 37 reading[0]. The state is indexed by the case of n_refusals: rb_big = true for n >= 8 (atom 35 in
   [8, 23], the encoding's bound) and false for n < 8 (atom 35 in [0, 7]); with these facts the executor decides
   the `blt 7,n` exit (0x89458) and the UBSan trap branch T2 (0x89460 `bgeu n,9`) by itself. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation N_SB := 32%nat (only parsing). Notation N_SP1 := 33%nat (only parsing). Notation N_UAR := 34%nat (only parsing).
Notation N_NR := 35%nat (only parsing). Notation N_RF := 36%nat (only parsing). Notation N_RD0 := 37%nat (only parsing).
(* the listing offsets of refuse's cut points (pc - BASE; BASE = 0x84dc0 at image B) *)
Definition RB_ENTRY : Z := AF_refuse.          (* 0x892f8 *)
Definition RB_SM_RET : Z := AF_refuse + 0x88.  (* 0x89380, return of frame_alloc_0 *)
Definition RB_HEAD : Z := AF_refuse + 0x11c.   (* 0x89414, after the frame set-up and the trap branch T1 *)
Definition RB_PRE : Z := AF_refuse + 0x1b4.    (* 0x894ac, `add s6,a0,a1`: dst, where chosen *)
Definition RB_TEXT : Z := AF_refuse + 0x1ec.   (* 0x894e4, snprintf's return (both arms) *)
Definition RB_VRET : Z := AF_refuse + 0x224.   (* 0x8951c, vsnprintf's return *)
Definition RB_REL : Z := AF_refuse + 0x24c.    (* 0x89544, the frame release (all three ways in) *)
Definition rsp1 (sp0 : Z) : Z := (sp0 - 160) - (sp0 - 160) mod 32.
Definition r_stk_lo : YP09.region := YP09.mkRegion (Some 2%nat) (-160) (-152) (-160) (-152) [].
Definition r_stk_hi : YP09.region := YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0 [].
Definition r_stk_s1 : YP09.region := YP09.mkRegion (Some N_SP1) 8 16 8 16 [].
Definition r_cnt : YP09.region := YP09.mkRegion (Some 10%nat) 0x34c8 0x34d0 0x34cc 0x34d0
  [YP09.mkChunk 0x34c8 (CVal 4 (SOff N_NR 0)); YP09.mkChunk 0x34cc (CVal 4 (SOff N_RF 0))].
Definition r_rd0 : YP09.region := YP09.mkRegion (Some 10%nat) 0x4080 0x4081 0x4080 0x4080
  [YP09.mkChunk 0x4080 (CVal 1 (SOff N_RD0 0))].
Definition rb_regions0 : smem :=
[ r_stk_lo; r_stk_hi; r_stk_s1; got_regionP; bcell_regionP N_SB; uar_got_regionP N_UAR; uar_cell_regionP N_UAR;
  r_cnt; r_rd0 ].
Definition rb_nr_fact (big : bool) : afact := if big then mkAF 8 23 0 else mkAF 0 7 0.
Definition rb_atoms0 (big : bool) : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (N_SP1, mkAF (2^46) (2^47) 5); (N_SB, mkAF SB SB 0); (N_UAR, mkAF 0x10000 kImgEnd 2);
  (10%nat, mkAF 4096 (2^47 - 16616) 4); (11%nat, mkAF 0 (2^31 - 1) 0);
  (N_NR, rb_nr_fact big); (N_RF, mkAF 0 (2^32 - 2) 0); (N_RD0, mkAF 0 255 0) ].
Definition rb_alias0 : list (sv * sv) := [ (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32)), SOff N_SP1 0) ].
Definition ss_r0 (big : bool) : sstate := mkSS AF_refuse sr_atoms rb_regions0 None (mkFacts (rb_atoms0 big) [] rb_alias0).
Definition rb_extra (sp0 uar nr rf rd0 : Z) : list word := map (Z_to_bv 64) [SB; rsp1 sp0; uar; nr; rf; rd0].
(* the token run from the entry to the call of frame_alloc_0 (0x8937c), and the state after that call (pc
   0x89380; atoms 1024..1039 the clobbered registers, 1028 the frame a0); the frame added (1040 its flag cell, 1041
   its shadow SB + frame / 8; regions: the frame's words [0, 32), [32, 40) (ap), [40, 64) with the flag pointer at
   56, and the frame's 8 shadow bytes) *)
(* Every state below is computed at a CONCRETE case (F: n < 8, T: n >= 8): a vm_compute under a free case variable
   would unfold the executor's fuel when a step consults atom 35's fact. *)
Definition rb_run1 (ss : sstate) : sstate :=
sh_ss (fst (sym_runN_pi_tok seg_tpi seg_tw (run_K A_LIM (SOff 32 0) [] ss) (SOff 32 0) Bspan [] FUEL ss)).
Definition ss_r1rF : sstate := Eval vm_compute in rb_run1 (ss_r0 false).
Definition ss_r1rT : sstate := Eval vm_compute in rb_run1 (ss_r0 true).
Definition ss_r1r (big : bool) : sstate := if big then ss_r1rT else ss_r1rF.
Definition rb_after_sm (ss : sstate) : sstate := ss_after_call ss (pick (ss_mem ss) [0;1;2;3;4;5;6;7;8]%nat) 1024 RB_SM_RET.
Definition ss_r1cF : sstate := Eval vm_compute in rb_after_sm ss_r1rF.
Definition ss_r1cT : sstate := Eval vm_compute in rb_after_sm ss_r1rT.
Definition ss_r1c (big : bool) : sstate := if big then ss_r1cT else ss_r1cF.
Definition r_fr_c : YP09.region := YP09.mkRegion (Some 1028%nat) 40 64 40 56 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))].
Definition r_fr_b : YP09.region := YP09.mkRegion (Some 1028%nat) 32 40 32 40 [].
Definition r_fr_a : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 32 [].
Definition r_fsh : YP09.region := YP09.mkRegion (Some 1041%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))].
Definition rb_add_region (ss : sstate) (r : YP09.region) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition rb_add_frame (ss : sstate) : sstate :=
let s1 := add_atom (add_atom (add_atom ss 1028 (mkAF 4096 (2 ^ 47) 6)) 1040 (mkAF 4096 (2 ^ 47) 0)) 1041 (mkAF (SB + 512) (SB + 2 ^ 44) 3) in
let s2 := set_facts s1 (mkFacts (f_atoms (ss_facts s1)) (f_conds (ss_facts s1))
  ((SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0), SOff 1041 0) :: f_alias (ss_facts s1))) in
rb_add_region (rb_add_region (rb_add_region (rb_add_region s2 r_fr_c) r_fr_b) r_fr_a) r_fsh.
Definition ss_r1F : sstate := Eval vm_compute in rb_add_frame ss_r1cF.
Definition ss_r1T : sstate := Eval vm_compute in rb_add_frame ss_r1cT.
Definition ss_r1 (big : bool) : sstate := if big then ss_r1T else ss_r1F.
(* the plain run from frame_alloc_0's return to 0x89414: the frame's header words, its shadow f1 f1 f1 f1 f8 f3 f3
   f3, the slot sp1 + 8, and the trap branch T1 (0x89410, c & 7: decided by atom 10's alignment) *)
Definition ss_r2F : sstate := Eval vm_compute in fst (sym_run_toN_pi seg_tpi FUEL RB_HEAD ss_r1F).
Definition ss_r2T : sstate := Eval vm_compute in fst (sym_run_toN_pi seg_tpi FUEL RB_HEAD ss_r1T).
Definition ss_r2 (big : bool) : sstate := if big then ss_r2T else ss_r2F.
(* the token run of the head (0x89414 ..): checks 1-3 on the c block (one SH entry, the block's 16616 bytes), the
   refused++ store, the n test, the UBSan trap branches T2 (decided by atom 35's range) and T3 (0x8947c, a stuck
   branch the walk splits), the where test (0x894a0, split). A token run allows a writable window only off the
   shadow span or covered by an SH entry (YCbn.v cells_safe_b): the frame (atom 1028, any address the facts allow)
   and its shadow (1041) are read-only there; the head writes neither after 0x89414. *)
Definition rb_ro (r : YP09.region) : YP09.region := YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_lo r) (YP09.r_lo r) (YP09.r_chunks r).
Definition rb_shro (r : YP09.region) : YP09.region := match YP09.r_base r with Some 1041%nat | Some 1028%nat => rb_ro r | _ => r end.
Definition rb_shro_ss (s : sstate) : sstate := mkSS (ss_pc s) (ss_regs s) (map rb_shro (ss_mem s)) (ss_resv s) (ss_facts s).
Definition ss_r2tF : sstate := Eval vm_compute in rb_shro_ss ss_r2F.
Definition ss_r2tT : sstate := Eval vm_compute in rb_shro_ss ss_r2T.
Definition rb_SH : list shent := [mkSHE 10 0 16616].
Definition rb_K (ss : sstate) : nat := run_K A_LIM (SOff 32 0) rb_SH ss.
Definition rb_tok_to (stop : Z) (ss : sstate) : sstate :=
sh_ss (fst (sym_run_toN_pi_tok seg_tpi seg_tw (rb_K ss) (SOff 32 0) Bspan rb_SH FUEL stop ss)).
(* n >= 8: the token run reaches the release (0x89544) by the `blt 7,n` exit *)
Definition ss_r3T : sstate := Eval vm_compute in rb_tok_to RB_REL ss_r2tT.
(* n < 8: the token run stops at the trap branch T3 (0x8947c); its not-taken side, then the run to the where test *)
Definition ss_r3F : sstate := Eval vm_compute in rb_tok_to RB_PRE ss_r2tF.
Definition rb_T3_a : sv := SAlu ALU_XOR (SOff 10 11912) (SLit (-1)).
Definition rb_T3_b : sv := SMd M_MUL (SOff 35 0) (SLit 200).
Definition ss_r4F : sstate := Eval vm_compute in rb_tok_to RB_PRE (add_cond ss_r3F (mkAC BC_GEU rb_T3_a rb_T3_b)).
(* the where test (0x894a0 `bnez a2`, a2 = reading[0]): reading nonempty (where = c + 0x4080) or empty (where =
   .str.1, listing object 34); both runs stop at 0x894ac *)
Definition ss_r5F1 : sstate := Eval vm_compute in rb_tok_to RB_PRE (add_cond ss_r4F (mkAC BC_NE (SOff N_RD0 0) (SLit 0))).
Definition ss_r5F0 : sstate := Eval vm_compute in rb_tok_to RB_PRE (add_cond ss_r4F (mkAC BC_EQ (SOff N_RD0 0) (SLit 0))).
Lemma rsp1_facts : forall sp0, sp0 mod 16 = 0 ->
rsp1 sp0 mod 32 = 0 /\ (rsp1 sp0 = sp0 - 160 \/ rsp1 sp0 = sp0 - 176).
Proof.
intros sp0 H. unfold rsp1. pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as M.
assert (Hm : (sp0 - 160) mod 32 = 0 \/ (sp0 - 160) mod 32 = 16).
{ pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as D. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
rewrite H in D2. lia. }
split; [|lia].
replace ((sp0 - 160) - (sp0 - 160) mod 32) with (32 * ((sp0 - 160) / 32)) by (pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma rsp1_and : forall sp0, 0 <= sp0 - 160 < 2 ^ 64 ->
alu64 ALU_AND (Z_to_bv 64 (sp0 - 160)) (Z_to_bv 64 (-32)) = Z_to_bv 64 (rsp1 sp0).
Proof.
intros sp0 H. rewrite and_lit_Z. f_equal. rewrite zcanon_id by (unfold M64; lia).
change (zsigned64 (-32)) with (- 2 ^ 5). rewrite land_neg_pow2 by lia. reflexivity.
Qed.
Lemma rb_val1 : forall segs H mem a v, aview segs H mem a = Some v -> val_mem segs (mrestrict H mem) a 1 v.
Proof.
intros segs H mem a v Hr k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
destruct (aview_byte segs H mem a v Hr) as (b0 & _ & Hbv0 & Hrange0).
assert (Hle : le_byte v 1 0 = v).
{ unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite (Z.mod_small v (2 ^ 8)) by (change (2 ^ 8) with 256; lia). apply Z.mod_small. lia. }
assert (Hb : aview segs H mem (a + Z.of_nat 0) = Some (le_byte v 1 0)) by (rewrite Hle, Z.add_0_r; exact Hr).
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
(* an opaque wrapper for the address facts the disjointness goals use, so a tactic can find them by type *)
Definition ram (P : Prop) : Prop := P.
Ltac rnorm HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac rdj :=
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
repeat match goal with U : bv_unsigned (ew ?E ?n) = _ |- context [bv_unsigned (ew ?E ?n)] => rewrite U end;
repeat match goal with |- _ /\ _ => split end; try exact I.
Ltac rzl := lazymatch goal with AM : ram _ |- _ => revert AM end;
clear; unfold ram, off_img, zone2, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB; intros;
repeat match goal with H : _ /\ _ |- _ => destruct H end; lia.
(* add region r to the walk's state HS: r's region_ok by rok, its disjointness from the state's regions by the
   address facts AM *)
Ltac raddreg HS r rok :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ssx (restrict ?H ?msx) =>
let Rok := fresh "Rok" in let Rdj := fresh "Rdj" in let HS3 := fresh "HS3" in
assert (Rok : region_ok sg Ev (ms_mem (restrict H msx)) r);
[ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rok |];
assert (Rdj : all_disjoint Ev r (ss_mem ssx)); [ rdj; rzl |];
pose proof (st_ok_pi_add_region Ev ssx (restrict H msx) r HS eq_refl Rok Rdj) as HS3;
clear HS Rok Rdj; rename HS3 into HS; rnorm HS end.
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
(* the seed: the symbolic entry state holds at refuse's entry, given the c block's three cells *)
Lemma rb_entry : forall (big : bool) STK W ly S regs mem md ch c line nr rf rd0,
afn_pre SEGS B STK ly S W regs mem md ch -> 176 <= STK ->
getr regs 10 = w64 c -> getr regs 11 = w64 line ->
4096 <= c -> c + 16616 <= alloc_ceiling -> off_img c 16616 -> c mod 16 = 0 -> 0 <= line < 2 ^ 31 ->
(forall i, 0 <= i < 16616 -> apresent (w_H W) mem (c + i)) ->
rd32 (aview SEGS (w_H W) mem) (c + 0x34c8) nr -> rd32 (aview SEGS (w_H W) mem) (c + 0x34cc) rf ->
aview SEGS (w_H W) mem (c + 0x4080) = Some rd0 ->
(if big then 8 <= nr <= 23 else 0 <= nr <= 7) -> 0 <= rf <= 2 ^ 32 - 2 -> 0 <= rd0 <= 255 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rb_extra (spZ regs) (as_uar_cell B) nr rf rd0))) (ss_r0 big)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_refuse)) mem (seg_rom SEGS))).
Proof.
intros big STK W ly S regs mem md ch c line nr rf rd0 HPRE HSTK H10 H11 Hc0 Hc1 Hcimg Hc16 Hline Hcp Hnr Hrf Hrd0 Hbig Hrfr Hrdr.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
set (sp0 := spZ regs) in *.
destruct (rsp1_facts sp0 Hal16) as (Hs1al & Hs1).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rb_extra sp0 (as_uar_cell B) nr rf rd0))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (rb_extra sp0 (as_uar_cell B) nr rf rd0) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth rb_extra map] in E32, E33, E34, E35, E36, E37. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hkimg : kImgEnd = 0x602000) by reflexivity.
unfold ss_r0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rb_regions0, r_stk_lo, r_stk_hi, r_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, r_cnt, r_rd0.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB N_SP1 (rsp1 sp0) E33) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff N_SB 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff N_UAR 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB N_UAR (as_uar_cell B) E34) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
+ cbn [base_val]. rewrite Uc. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). replace (c + o) with (c + (o)) by lia. apply Hcp. lia. }
constructor; [|constructor; [|constructor]].
* apply (chunk_ok_val SEGS E _ c 0x34c8 4 (SOff N_NR 0) nr);
  [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | destruct big; zside | zside |].
  exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hnr).
* apply (chunk_ok_val SEGS E _ c 0x34cc 4 (SOff N_RF 0) rf);
  [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hrf).
+ cbn [base_val]. rewrite Uc. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ c 0x4080 1 (SOff N_RD0 0) rd0);
[cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (rb_val1 SEGS (w_H W) mem _ _ Hrd0).
- apply pairwise_disjoint_of_extents.
unfold rb_regions0, r_stk_lo, r_stk_hi, r_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, r_cnt, r_rd0, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB N_SP1 (rsp1 sp0) E33), (VB N_UAR (as_uar_cell B) E34) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp, Uc.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold off_img in Hcimg.
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Hob0 Hob1 Hob12 Huar Hsep Hs1 Hc0 Hc1 Hcimg Hkimg. clear. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I|]].
2: { cbn [f_alias alias_ok rb_alias0]. split; [|exact I]. cbn [sv_denot]. rewrite Usp, E33, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite <- (rsp1_and sp0) by lia. reflexivity. }
cbn [f_atoms atoms_ok rb_atoms0]. unfold afact_ok, rb_nr_fact. destruct big; cbn [af_lo af_hi af_al2];
rewrite Usp, E10, E11, E32, E33, E34, E35, E36, E37, !unsigned_lit_small by (unfold SB, kImgEnd in *; lia);
change (2 ^ 5) with 32; change (2 ^ 4) with 16; change (2 ^ 2) with 4; rewrite !Z.pow_0_r, !Z.mod_1_r;
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Huar Huar4 Hs1al Hs1 Hal16 Hc0 Hc1 Hc16 Hline Hbig Hrfr Hrdr Hkimg; clear; unfold SB; intros;
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End e.
End f.
End d.
