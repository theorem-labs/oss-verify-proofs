(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AC9z.v (the entry state of a walk): the symbolic state at number's entry (0x8e430) and its seed lemma. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/numberE.v, with its module paths, module names and numbers changed; 140 of its 263 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: refuse's walk on reac-pw/fuzz_segconf's ASan image A (fuzz_segconf.asan,
   refuse at 0x88da4), in the form of plugin-hostd/fuzz_command's lib/A/Prog/numberE.v at origin/ossv/recipes
   501c0d516c69 (number's entry state and seed): the symbolic state at refuse's entry and its seed lemma, and the
   state tactics of the walk (numberE.v's nam / nnorm / ndj / nzl / addreg / n_keep_regions / n_rewin, with an r prefix).
   The image-A refuse walk, 2026-10-30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YN2j.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG PaLibH PaSB PaDenot.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* atoms of the entry state: 0-31 the registers, 32 the shadow base SB, 33 the realigned stack pointer
   (sp - 160) & -32 of 0x88de0, 34 the use-after-return flag cell *)
Notation R_SB := 32%nat (only parsing). Notation R_SP1 := 33%nat (only parsing). Notation R_UAR := 34%nat (only parsing).
Definition rsp1 (sp0 : Z) : Z := (sp0 - 160) - (sp0 - 160) mod 32.
(* the real frame refuse stores into: the probe word at sp - 160 (0x88da8), the twelve saved registers at
   [sp - 144, sp - 48) and the variadic a3 .. a7 at [sp - 40, sp) (0x88e04-0x88e1c, s0 = sp - 48), and the slot
   sp1 + 8 that keeps the frame's address (0x88ed0); sp1 is sp - 160 or sp - 176, so the three are disjoint *)
Definition r_stk_lo : YP09.region := YP09.mkRegion (Some 2%nat) (-160) (-152) (-160) (-152) [].
Definition r_stk_hi : YP09.region := YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0 [].
Definition r_stk_s1 : YP09.region := YP09.mkRegion (Some R_SP1) 8 16 8 16 [].
Definition r_regions0 : smem :=
[ r_stk_lo; r_stk_hi; r_stk_s1; got_regionP; bcell_regionP R_SB; uar_got_regionP R_UAR; uar_cell_regionP R_UAR ].
(* a0 = c (16-aligned, a live block of 16616 bytes), a1 = line (0 .. 2^31 - 1) *)
Definition r_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (R_SP1, mkAF (2^46) (2^47) 5); (R_SB, mkAF SB SB 0); (R_UAR, mkAF 0x10000 kImgEnd 2);
  (10%nat, mkAF 4096 (2^47 - 16616) 4); (11%nat, mkAF 0 (2^31 - 1) 0) ].
Definition r_alias0 : list (sv * sv) := [ (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32)), SOff R_SP1 0) ].
Definition ss_r0 : sstate := mkSS AF_refuse sr_atoms r_regions0 None (mkFacts r_atoms0 [] r_alias0).
Definition r_extra (sp0 uar : Z) : list word := map (Z_to_bv 64) [SB; rsp1 sp0; uar].
(* the token run from the entry to the call of __asan_stack_malloc_0 (0x88e30): no inline check on the way *)
Definition ss_r1r : sstate := Eval vm_compute in
sh_ss (fst (sym_runN_pi_tok seg_tpi seg_tw (run_K A_LIM (SOff 32 0) [] ss_r0) (SOff 32 0) Bspan [] FUEL ss_r0)).
(* The canonical state at the release (0x88fc4, listing offset R_REL), which both ways into it reach (the
   n_refusals >= 8 exit 0x88efc and the end of the body 0x88fc0): gp, tp, s0 = sp - 48, s2 = s7 = the frame (atom
   1028), s8 = its shadow (atom 1041), every other register a fresh atom from 1200 (the release reloads the
   callee-saved ones from the real frame); the regions are the frame's shadow and its words [0, 32) with no chunk,
   its words [40, 64) with the flag pointer at 56, and the twelve saved registers at [sp - 144, sp - 48), all
   read-only (the release lemma opens the windows it writes). *)
Definition R_REL : Z := 0x4290.
Definition r_rel_clob : list (bv 5) :=
map (fun n => Z_to_bv 5 n) [1;2;5;6;7;9;10;11;12;13;14;15;16;17;19;20;21;22;25;26;28;29;30;31].
Definition r_rel_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-144) 0 (-144) (-144)
(map (fun p => YP09.mkChunk (fst p) (CVal 8 (SOff (snd p) 0)))
  [(-56, 1%nat); (-64, 8%nat); (-72, 9%nat); (-80, 18%nat); (-88, 19%nat); (-96, 20%nat); (-104, 21%nat);
   (-112, 22%nat); (-120, 23%nat); (-128, 24%nat); (-136, 25%nat); (-144, 26%nat)]).
Definition r_rel_mem : smem :=
[ YP09.mkRegion (Some 1041%nat) 0 8 0 0 [];
  YP09.mkRegion (Some 1028%nat) 0 32 0 0 [];
  YP09.mkRegion (Some 1028%nat) 40 64 40 40 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))];
  r_rel_stk ].
Definition r_rel_atoms : list (nat * afact) :=
[ (1041%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3); (1040%nat, mkAF 4096 (2 ^ 47) 0); (1028%nat, mkAF 4096 (2 ^ 47) 6);
  (2%nat, mkAF (2^46) (2^47) 4) ].
Definition r_rel_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0), SOff 1041 0) ].
Definition r_rel_base : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms (8%bv : bv 5) (SOff 2 (-48))) (18%bv : bv 5) (SOff 1028 0))
  (23%bv : bv 5) (SOff 1028 0)) (24%bv : bv 5) (SOff 1041 0).
Definition ss_rel : sstate := Eval vm_compute in
mkSS R_REL (sr_sets r_rel_base (junk_upd 1200 r_rel_clob)) r_rel_mem None (mkFacts r_rel_atoms [] r_rel_alias).
Lemma r_kept_refl {fx : YK11.FPState} : forall segs E (m : word -> option byte) r, region_kept segs E m m r.
Proof. intros segs E m r. split; intros; [reflexivity | assumption]. Qed.
(* the signed branch of `blt` on two small values (YI04 has only the unsigned form) *)
Lemma r_branch_lt_U : forall E a b,
bv_unsigned (sv_denot E a) < 2 ^ 63 -> bv_unsigned (sv_denot E b) < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
intros E a b Ha Hb. cbn [branch_taken]. rewrite bv_lts_signed, !signed_of_small by (unfold half64; lia).
unfold U. reflexivity.
Qed.
(* read an atom's value through the environments a run builds (numberB.v's n_evE) *)
Ltac r_evE := repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia].
(* refuse's `blt 7, n` at 0x88efc: n is the atom n, below 2 ^ 63 *)
Lemma r_branch_lt7 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SLit 7)) (sv_denot E (SOff n 0)) = (7 <? v).
Proof.
intros E n v He Hv.
assert (HU : U E (SOff n 0) = v) by (apply U_atom; [exact He | lia]).
assert (H7 : U E (SLit 7) = 7) by reflexivity.
unfold U in HU, H7.
rewrite (r_branch_lt_U E (SLit 7) (SOff n 0) ltac:(rewrite H7; lia) ltac:(rewrite HU; lia)).
unfold U. rewrite H7, HU. reflexivity.
Qed.
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
(* an opaque wrapper for the address facts the disjointness goals use, so a tactic can find them by type *)
Definition rnam (P : Prop) : Prop := P.
Ltac rnorm HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac rdj :=
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
repeat match goal with U : bv_unsigned (ew ?E ?n) = _ |- context [bv_unsigned (ew ?E ?n)] => rewrite U end;
repeat match goal with |- _ /\ _ => split end; try exact I.
Ltac rzl := lazymatch goal with AM : rnam _ |- _ => revert AM end;
clear; unfold rnam, off_img, zone2, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB, kImgEnd; intros;
repeat match goal with H : _ /\ _ |- _ => destruct H end; lia.
(* add region r to the walk's state HS: r's region_ok by rok (after the region's fields are computed), and its
   disjointness from the state's regions by the address facts AM *)
Ltac raddreg HS r rok :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ssx (restrict ?H ?msx) =>
let Rok := fresh "Rok" in let Rdj := fresh "Rdj" in let HS3 := fresh "HS3" in
assert (Rok : region_ok sg Ev (ms_mem (restrict H msx)) r);
[ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rok |];
assert (Rdj : all_disjoint Ev r (ss_mem ssx)); [ rdj; rzl |];
pose proof (st_ok_pi_add_region Ev ssx (restrict H msx) r HS eq_refl Rok Rdj) as HS3;
clear HS Rok Rdj; rename HS3 into HS; rnorm HS end.
(* keep the regions f selects *)
Ltac rkeep HS f :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
let rs' := eval vm_compute in (filter f (ss_mem ssx)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_submem Ex ssx msx rs' HS
  ltac:(lazymatch goal with |- submem ?a ?b => let b' := eval vm_compute in b in change (submem a b') end; submem_tac)
  ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; rnorm HS end.
(* the index of the region with base atom b and low offset lo *)
Fixpoint r_find (rs : smem) (b : nat) (lo : Z) (i : nat) : nat :=
match rs with
| [] => i
| r :: rs' => if (match r_base r with Some k => Nat.eqb k b | None => false end) && (r_lo r =? lo) then i else r_find rs' b lo (S i)
end.
(* give the region with base atom b and low offset lo the write window [wlo, whi) *)
Ltac rrewin HS bse lo wlo whi wtac :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
let i := eval vm_compute in (r_find (ss_mem ssx) bse lo 0) in
let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r wlo whi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; wtac))) as HS3;
clear HS; rename HS3 into HS; rnorm HS end.
Lemma r_aview_present {fx : YK11.FPState} : forall segs H mem a, apresent H mem a -> aview segs H mem a <> None.
Proof. intros segs H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
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
Lemma r_entry : forall STK W ly S regs mem md ch c line,
afn_pre SEGS B STK ly S W regs mem md ch -> 176 <= STK ->
getr regs 10 = w64 c -> getr regs 11 = w64 line ->
4096 <= c <= 2 ^ 47 - 16616 -> c mod 16 = 0 -> 0 <= line <= 2 ^ 31 - 1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (r_extra (spZ regs) (as_uar_cell B)))) ss_r0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_refuse)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch c line HPRE HSTK H10 H11 Hc Hc16 Hln.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
set (sp0 := spZ regs) in *.
destruct (rsp1_facts sp0 Hal16) as (Hs1al & Hs1).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (r_extra sp0 (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 line) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (r_extra sp0 (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth r_extra map] in E32, E33, E34. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold kImgEnd in Hob0, Hob1, Hob12, Huar.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_r0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold r_regions0, r_stk_lo, r_stk_hi, r_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB R_SP1 (rsp1 sp0) E33) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff R_SB 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff R_UAR 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB R_UAR (as_uar_cell B) E34) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold r_regions0, r_stk_lo, r_stk_hi, r_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB R_SP1 (rsp1 sp0) E33), (VB R_UAR (as_uar_cell B) E34) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Hob0 Hob1 Hob12 Huar Hsep Hs1. clear. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I|]].
2: { cbn [f_alias alias_ok r_alias0]. split; [|exact I]. cbn [sv_denot]. rewrite Usp, E33, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite <- (rsp1_and sp0) by lia. reflexivity. }
cbn [f_atoms atoms_ok r_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E32, E33, E34, !unsigned_lit_small by (unfold SB in *; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Huar Huar4 Hs1al Hs1 Hal16 Hc Hc16 Hln. clear. unfold SB, kImgEnd. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End e.
End f.
End d.
(* bring a state at the release (pc R_REL) to ss_rel: the registers of r_rel_clob become the fresh atoms 1200..1224,
   the regions of r_rel_mem are kept (each a subregion of the state's: narrowed windows, fewer chunks), the facts
   ss_rel names are kept and the branch conditions dropped *)
Ltac r_to_rel HS :=
pmkst HS;
lazymatch type of HS with st_ok_pi ?sg ?vl ?E ?ss (restrict ?H ?msx) =>
let HS2 := fresh "HS2" in
pose proof (st_ok_pi_after_stretch_hi 1200 E (abs_ss vl ss) (restrict H msx) (ms_regs msx) (mrestrict H (ms_mem msx))
  r_rel_mem R_REL r_rel_clob HS eq_refl
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) (YN2j.submemb_sound (ss_mem (abs_ss vl ss)) r_rel_mem ltac:(vm_compute; reflexivity))
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (fun _ _ => eq_refl)
  (proj2 (Forall_forall _ _) (fun r _ => r_kept_refl sg E _ r))) as HS2;
clear HS; rename HS2 into HS end;
lazymatch type of HS with st_ok_pi ?sg ?vl ?E ?ss ?msx =>
let HS2 := fresh "HS2" in
pose proof (st_ok_pi_facts_incl E ss msx r_rel_atoms r_rel_alias HS
  ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; vm_compute in Hx;
        repeat (destruct Hx as [<- | Hx]; [vm_compute; repeat (first [left; reflexivity | right]) |]); destruct Hx)
  ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; vm_compute in Hx;
        repeat (destruct Hx as [<- | Hx]; [vm_compute; repeat (first [left; reflexivity | right]) |]); destruct Hx)) as HS2;
clear HS; rename HS2 into HS end;
lazymatch type of HS with st_ok_pi ?sg ?vl ?E ?ss ?msx =>
let Heq := fresh "Heq" in
assert (Heq : ss = ss_rel) by (vm_compute; reflexivity); rewrite Heq in HS; clear Heq end;
rewrite <- restrict_mkst_fx in HS.
