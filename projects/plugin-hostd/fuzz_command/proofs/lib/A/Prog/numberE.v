(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: number's walk on the ASan build of plugin-hostd/fuzz_command, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AC9z.v (the entry state of a walk): the symbolic state at number's entry (0x8e430) and its seed lemma. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI04 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* atoms of the entry state: 0-31 the registers, 32 the shadow base SB, 33 the realigned stack pointer
   (sp - 96) & -32 of 0x8e464, 34 the use-after-return flag cell *)
Notation N_SB := 32%nat (only parsing). Notation N_SP1 := 33%nat (only parsing). Notation N_UAR := 34%nat (only parsing).
Definition nsp1 (sp0 : Z) : Z := (sp0 - 96) - (sp0 - 96) mod 32.
(* the frame number stores into: the saved registers at [sp - 80, sp) and the zero word at sp - 96, below them
   the slot sp1 + 8 that keeps the frame base (0x8e4c8); sp1 is sp - 96 or sp - 112, so the three are disjoint *)
Definition n_stk_lo : YP09.region := YP09.mkRegion (Some 2%nat) (-96) (-88) (-96) (-88) [].
Definition n_stk_hi : YP09.region := YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0 [].
Definition n_stk_s1 : YP09.region := YP09.mkRegion (Some N_SP1) 8 16 8 16 [].
Definition n_regions0 : smem :=
[ n_stk_lo; n_stk_hi; n_stk_s1; got_regionP; bcell_regionP N_SB; uar_got_regionP N_UAR; uar_cell_regionP N_UAR ].
Definition n_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (N_SP1, mkAF (2^46) (2^47) 5); (N_SB, mkAF SB SB 0); (N_UAR, mkAF 0x10000 0x606000 2);
  (10%nat, mkAF 4096 (2^47 - 1) 0); (11%nat, mkAF 4096 (2^47 - 4) 2) ].
Definition n_alias0 : list (sv * sv) := [ (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32)), SOff N_SP1 0) ].
Definition ss_n0 : sstate := mkSS AF_number sr_atoms n_regions0 None (mkFacts n_atoms0 [] n_alias0).
Definition n_extra (sp0 uar : Z) : list word := map (Z_to_bv 64) [SB; nsp1 sp0; uar].
(* the states of the walk up to the strtol call, each computed by the symbolic executor exactly as the walk
   computes it: the token run from the entry to the call of __asan_stack_malloc_0 (0x8e494), the state after that
   call (atoms 1024..1039 the clobbered registers, 1028 the frame a0), the frame added (1040 its flag cell, 1041
   its shadow SB + frame / 8; regions: the frame's words [0, 32), [32, 40) (`end`), [40, 64) with the flag pointer
   at 56, and the frame's 8 shadow bytes), and the plain run from there to the call of strtol (0x8e530) *)
Definition ss_n1r : sstate := Eval vm_compute in
sh_ss (fst (sym_runN_pi_tok cmd_tpi cmd_tw (run_K A_LIM (SOff 32 0) [] ss_n0) (SOff 32 0) Bspan [] FUEL ss_n0)).
Definition ss_n1c : sstate := Eval vm_compute in ss_after_call ss_n1r (pick (ss_mem ss_n1r) [0;1;2;3;4;5;6]%nat) 1024 32692.
Definition n_fr_c : YP09.region := YP09.mkRegion (Some 1028%nat) 40 64 40 56 [YP09.mkChunk 56 (CVal 8 (SOff 1040 0))].
Definition n_fr_b : YP09.region := YP09.mkRegion (Some 1028%nat) 32 40 32 40 [].
Definition n_fr_a : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 32 [].
Definition n_fsh : YP09.region := YP09.mkRegion (Some 1041%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))].
Definition n_add_region (ss : sstate) (r : YP09.region) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition ss_n1 : sstate := Eval vm_compute in
let s1 := add_atom (add_atom (add_atom ss_n1c 1028 (mkAF 4096 (2 ^ 47) 6)) 1040 (mkAF 4096 (2 ^ 47) 0)) 1041 (mkAF (SB + 512) (SB + 2 ^ 44) 3) in
let s2 := set_facts s1 (mkFacts (f_atoms (ss_facts s1)) (f_conds (ss_facts s1))
  ((SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0), SOff 1041 0) :: f_alias (ss_facts s1))) in
n_add_region (n_add_region (n_add_region (n_add_region s2 n_fr_c) n_fr_b) n_fr_a) n_fsh.
Definition ss_ncall : sstate := Eval vm_compute in fst (sym_runN_pi cmd_tpi FUEL ss_n1).
(* after the strtol call (0x8e534): ss_after_call keeps the frame's shadow, the frame's words [0, 32) and [40, 64)
   and the saved registers (atoms 1042..1057 the clobbered registers, 1046 strtol's result a0). The token runs to
   the release (0x8e5a0) only read memory, so every region is read-only there (a writable window in the shadow
   band is not allowed in a token run, and a read-only window keeps the result cell's bytes across a run); the
   result cell is writable for the store (0x8e598), the frame and its shadow at the release. Atom 1058 is the end
   pointer strtol wrote at frame + 32, atom 1059 the word's first byte. Regions: the result cell (atom 11, its
   shadow known: SH entry), the word's first byte (atom 10), the end pointer's word. *)
Definition n_ro (r : YP09.region) : YP09.region := YP09.mkRegion (r_base r) (r_lo r) (r_hi r) (r_lo r) (r_lo r) (r_chunks r).
Definition n_out_r : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 0 [].
Definition n_word_r : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 1059 0))].
Definition n_endw_r : YP09.region := YP09.mkRegion (Some 1028%nat) 32 40 32 32 [YP09.mkChunk 32 (CVal 8 (SOff 1058 0))].
Definition n_end_r : YP09.region := YP09.mkRegion (Some 1058%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 1070 0))].
Definition n_flag_r : YP09.region := YP09.mkRegion (Some 1040%nat) 0 1 0 1 [].
Definition ss_nB0 : sstate := Eval vm_compute in ss_after_call ss_ncall (pick (ss_mem ss_ncall) [0;1;3;5]%nat) 1042 (ss_pc ss_ncall).
Definition ss_nB : sstate := Eval vm_compute in
let s1 := add_atom (add_atom ss_nB0 1058 (mkAF 4096 (2 ^ 47 - 1) 0)) 1059 (mkAF 0 255 0) in
let s2 := mkSS (ss_pc s1) (ss_regs s1) (map n_ro (ss_mem s1)) (ss_resv s1) (ss_facts s1) in
n_add_region (n_add_region (n_add_region s2 n_endw_r) n_word_r) n_out_r.
(* the index of the region with base atom b and low offset lo *)
Fixpoint n_find (rs : smem) (b : nat) (lo : Z) (i : nat) : nat :=
match rs with
| [] => i
| r :: rs' => if (match r_base r with Some k => Nat.eqb k b | None => false end) && (r_lo r =? lo) then i else n_find rs' b lo (S i)
end.
(* the regions the release keeps: the frame's words without the end pointer's, its shadow, the saved registers *)
Definition n_keep (r : YP09.region) : bool :=
match r_base r with Some 1041%nat => true | Some 2%nat => true | Some 1028%nat => negb (r_lo r =? 32) | _ => false end.
Definition n_SH : list shent := [mkSHE 11 0 4].
(* the release (0x8e5a0..0x8e618) starts from one state on every path: the regions n_keep selects, the facts of
   ss_nB, and a0..a3 (the registers the four paths leave differently) as the fresh atoms 1100..1103 *)
Definition n_K (ss : sstate) : nat := run_K A_LIM (SOff 32 0) n_SH ss.
Definition n_set_tmps (rg : list sv) : list sv := firstn 10 rg ++ [SOff 1100 0; SOff 1101 0; SOff 1102 0; SOff 1103 0] ++ skipn 14 rg.
Definition n_canon (s : sstate) : sstate :=
mkSS (ss_pc s) (n_set_tmps (ss_regs s)) (filter n_keep (ss_mem s)) (ss_resv s) (mkFacts (f_atoms (ss_facts ss_nB)) [] (f_alias (ss_facts ss_nB))).
Definition ss_nB_r1 : sstate := Eval vm_compute in sh_ss (fst (sym_runN_pi_tok cmd_tpi cmd_tw (n_K ss_nB) (SOff 32 0) Bspan n_SH FUEL ss_nB)).
Definition ss_nB_a : sstate := Eval vm_compute in add_cond ss_nB_r1 (mkAC BC_EQ (SOff 1059 0) (SLit 0)).
Definition ss_nB_a1 : sstate := Eval vm_compute in sh_ss (fst (sym_run_toN_pi_tok cmd_tpi cmd_tw (n_K ss_nB_a) (SOff 32 0) Bspan n_SH FUEL 32956 ss_nB_a)).
Definition ss_rel0 : sstate := Eval vm_compute in n_canon ss_nB_a1.
Lemma nsp1_facts : forall sp0, sp0 mod 16 = 0 ->
nsp1 sp0 mod 32 = 0 /\ (nsp1 sp0 = sp0 - 96 \/ nsp1 sp0 = sp0 - 112).
Proof.
intros sp0 H. unfold nsp1. pose proof (Z.mod_pos_bound (sp0 - 96) 32 ltac:(lia)) as M.
assert (Hm : (sp0 - 96) mod 32 = 0 \/ (sp0 - 96) mod 32 = 16).
{ pose proof (Z.div_mod (sp0 - 96) 32 ltac:(lia)) as D. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
rewrite H in D2. lia. }
split; [|lia].
replace ((sp0 - 96) - (sp0 - 96) mod 32) with (32 * ((sp0 - 96) / 32)) by (pose proof (Z.div_mod (sp0 - 96) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma nsp1_and : forall sp0, 0 <= sp0 - 96 < 2 ^ 64 ->
alu64 ALU_AND (Z_to_bv 64 (sp0 - 96)) (Z_to_bv 64 (-32)) = Z_to_bv 64 (nsp1 sp0).
Proof.
intros sp0 H. rewrite and_lit_Z. f_equal. rewrite zcanon_id by (unfold M64; lia).
change (zsigned64 (-32)) with (- 2 ^ 5). rewrite land_neg_pow2 by lia. reflexivity.
Qed.
(* an opaque wrapper for the address facts the disjointness goals use, so a tactic can find them by type *)
Definition nam (P : Prop) : Prop := P.
Ltac nnorm HS := lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac ndj :=
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
repeat match goal with U : bv_unsigned (ew ?E ?n) = _ |- context [bv_unsigned (ew ?E ?n)] => rewrite U end;
repeat match goal with |- _ /\ _ => split end; try exact I.
Ltac nzl := lazymatch goal with AM : nam _ |- _ => revert AM end;
clear; unfold nam, off_img, zone2, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB; intros;
repeat match goal with H : _ /\ _ |- _ => destruct H end; lia.
(* add region r to the walk's state HS: r's region_ok by rok (after the region's fields are computed), and its
   disjointness from the state's regions by the address facts AM *)
Ltac addreg HS r rok :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ev ?ssx (restrict ?H ?msx) =>
let Rok := fresh "Rok" in let Rdj := fresh "Rdj" in let HS3 := fresh "HS3" in
assert (Rok : region_ok sg Ev (ms_mem (restrict H msx)) r);
[ unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
  rok |];
assert (Rdj : all_disjoint Ev r (ss_mem ssx)); [ ndj; nzl |];
pose proof (st_ok_pi_add_region Ev ssx (restrict H msx) r HS eq_refl Rok Rdj) as HS3;
clear HS Rok Rdj; rename HS3 into HS; nnorm HS end.
(* keep the regions f selects *)
Ltac n_keep_regions HS f :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
let rs' := eval vm_compute in (filter f (ss_mem ssx)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_submem Ex ssx msx rs' HS
  ltac:(lazymatch goal with |- submem ?a ?b => let b' := eval vm_compute in b in change (submem a b') end; submem_tac)
  ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; nnorm HS end.
(* give the region with base atom b and low offset lo the write window [wlo, whi) *)
Ltac n_rewin HS bse lo wlo whi wtac :=
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
let i := eval vm_compute in (n_find (ss_mem ssx) bse lo 0) in
let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r wlo whi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
  ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; wtac))) as HS3;
clear HS; rename HS3 into HS; nnorm HS end.
Lemma n_aview_present {fx : YK11.FPState} : forall segs H mem a, apresent H mem a -> aview segs H mem a <> None.
Proof. intros segs H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma n_astr_kept : forall (rd rd' : reader) p s, (forall i, 0 <= i <= Z.of_nat (length s) -> rd' (p + i) = rd (p + i)) ->
astr_atR rd p s -> astr_atR rd' p s.
Proof.
intros rd rd' p s HK [H1 H2]. split; [|exact H2]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite HK by lia. exact (H1 i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.
Lemma n_in_img_dec : forall segs a, {in_img segs a} + {~ in_img segs a}.
Proof.
intros segs a. induction segs as [|sg segs IH].
- right. intros (s & [] & _).
- destruct (Z_le_dec (Z.of_N (seg_base sg)) a) as [H1|H1];
  [destruct (Z_lt_dec a (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) as [H2|H2]|].
  + left. exists sg. split; [left; reflexivity | lia].
  + destruct IH as [IH|IH]; [left; destruct IH as (s & Hs & Hr); exists s; split; [right; exact Hs | exact Hr]|].
    right. intros (s & [<-|Hs] & Hr); [lia | apply IH; exists s; split; [exact Hs | exact Hr]].
  + destruct IH as [IH|IH]; [left; destruct IH as (s & Hs & Hr); exists s; split; [right; exact Hs | exact Hr]|].
    right. intros (s & [<-|Hs] & Hr); [lia | apply IH; exists s; split; [exact Hs | exact Hr]].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Lemma n_entry : forall STK W ly S regs mem md ch w out,
afn_pre SEGS B STK ly S W regs mem md ch -> 112 <= STK ->
getr regs 10 = w64 w -> getr regs 11 = w64 out ->
4096 <= w <= 2 ^ 47 - 1 -> 4096 <= out <= 2 ^ 47 - 4 -> out mod 4 = 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (n_extra (spZ regs) (as_uar_cell B)))) ss_n0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_number)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch w out HPRE HSTK H10 H11 Hw Hou Hou4.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
set (sp0 := spZ regs) in *.
destruct (nsp1_facts sp0 Hal16) as (Hs1al & Hs1).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (n_extra sp0 (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 out) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (n_extra sp0 (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth n_extra map] in E32, E33, E34. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_n0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold n_regions0, n_stk_lo, n_stk_hi, n_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB N_SP1 (nsp1 sp0) E33) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
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
- apply pairwise_disjoint_of_extents.
unfold n_regions0, n_stk_lo, n_stk_hi, n_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB N_SP1 (nsp1 sp0) E33), (VB N_UAR (as_uar_cell B) E34) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Hob0 Hob1 Hob12 Huar Hsep Hs1. clear. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I|]].
2: { cbn [f_alias alias_ok n_alias0]. split; [|exact I]. cbn [sv_denot]. rewrite Usp, E33, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite <- (nsp1_and sp0) by lia. reflexivity. }
cbn [f_atoms atoms_ok n_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Huar Huar4 Hs1al Hs1 Hal16 Hw Hou Hou4. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End e.
End f.
End d.
