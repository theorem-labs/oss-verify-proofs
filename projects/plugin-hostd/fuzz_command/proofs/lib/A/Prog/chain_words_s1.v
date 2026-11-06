(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: chain_words' walk on the ASan build of plugin-hostd/fuzz_command, segment S1
   (chain_words_d.v cw_S1P): from the entry (0x8dfd4) through __asan_stack_malloc_3 (0x8e044) to the refusal cut KR
   (0x8e278) or the first-check cut KC (0x8e1ec). In the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v (entry,
   aj_stack_malloc_atS, re-seat) with the entry seed of lib/A/Prog/numberE.v: a run to the call, the call, a re-seat
   that keeps the three stack regions and adds the frame (the call's a0) and its shadow (the alias of
   (s8 >> 3) + s7), a plain run through the 88 shadow stores to the branch on ntok < 3, and the cut facts (cw_pc)
   read back from the symbolic state at the cut. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI00 YI04 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibF PaLibG PaLibH PaSB PaDenot PaCall PaNoChain PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import number_c sup_chain_c sup_resp_c chain_words_c chain_words_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* atoms of the entry state: 0-31 the registers, 32 the shadow base SB, 33 the realigned stack pointer
   (sp - 128) & -32 of 0x8e014, 34 the use-after-return flag cell *)
Notation N_SB := 32%nat (only parsing). Notation N_SP1 := 33%nat (only parsing). Notation N_UAR := 34%nat (only parsing).
Definition cw_nsp1 (sp0 : Z) : Z := (sp0 - 128) - (sp0 - 128) mod 32.
(* the frame chain_words stores into: the zero word at sp - 128, the saved registers at [sp - 104, sp), and below
   the realigned slot sp1 + 8 keeping the frame base (0x8e078); sp1 is sp - 128 or sp - 144 so the three are
   pairwise disjoint (sp1 + 8 lands in the gap [sp - 120, sp - 104) or below sp - 128) *)
Definition cw_stk_lo : YP09.region := YP09.mkRegion (Some 2%nat) (-128) (-120) (-128) (-120) [].
Definition cw_stk_hi : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition cw_stk_s1 : YP09.region := YP09.mkRegion (Some N_SP1) 8 16 8 16 [].
Definition cw_regions0 : smem :=
[ cw_stk_lo; cw_stk_hi; cw_stk_s1; got_regionP; bcell_regionP N_SB; uar_got_regionP N_UAR; uar_cell_regionP N_UAR ].
Definition cw_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (N_SP1, mkAF (2^46) (2^47) 5); (N_SB, mkAF SB SB 0); (N_UAR, mkAF 0x10000 0x606000 2) ].
Definition cw_alias0 : list (sv * sv) := [ (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32)), SOff N_SP1 0) ].
Definition ss_cw0 : sstate := mkSS AF_chain_words sr_atoms cw_regions0 None (mkFacts cw_atoms0 [] cw_alias0).
Definition cw_extra (sp0 uar : Z) : list word := map (Z_to_bv 64) [SB; cw_nsp1 sp0; uar].
Lemma cw_nsp1_facts : forall sp0, sp0 mod 16 = 0 ->
cw_nsp1 sp0 mod 32 = 0 /\ (cw_nsp1 sp0 = sp0 - 128 \/ cw_nsp1 sp0 = sp0 - 144).
Proof.
intros sp0 H. unfold cw_nsp1. pose proof (Z.mod_pos_bound (sp0 - 128) 32 ltac:(lia)) as M.
assert (Hm : (sp0 - 128) mod 32 = 0 \/ (sp0 - 128) mod 32 = 16).
{ pose proof (Z.div_mod (sp0 - 128) 32 ltac:(lia)) as D. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
rewrite H in D2. lia. }
split; [|lia].
replace ((sp0 - 128) - (sp0 - 128) mod 32) with (32 * ((sp0 - 128) / 32)) by (pose proof (Z.div_mod (sp0 - 128) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma cw_nsp1_and : forall sp0, 0 <= sp0 - 128 < 2 ^ 64 ->
alu64 ALU_AND (Z_to_bv 64 (sp0 - 128)) (Z_to_bv 64 (-32)) = Z_to_bv 64 (cw_nsp1 sp0).
Proof.
intros sp0 H. rewrite and_lit_Z. f_equal. rewrite zcanon_id by (unfold M64; lia).
change (zsigned64 (-32)) with (- 2 ^ 5). rewrite land_neg_pow2 by lia. reflexivity.
Qed.
(* the shadows of two disjoint 64-aligned frames are disjoint *)
Lemma cw_shadow_disj : forall F F' n n' a, F mod 64 = 0 -> F' mod 64 = 0 -> n mod 64 = 0 -> n' mod 64 = 0 ->
(F + n <= F' \/ F' + n' <= F) -> F / 8 <= a < F / 8 + n / 8 -> F' / 8 <= a < F' / 8 + n' / 8 -> False.
Proof.
intros F F' n n' a H1 H2 H3 H4 Hd Ha Hb.
assert (G : forall X, X mod 64 = 0 -> X = 64 * (X / 64) /\ X / 8 = 8 * (X / 64)).
{ intros X HX. pose proof (Z.div_mod X 64 ltac:(lia)) as D. rewrite HX, Z.add_0_r in D. split; [exact D|].
rewrite D at 1. replace (64 * (X / 64)) with ((8 * (X / 64)) * 8) by lia. apply Z.div_mul. lia. }
destruct (G F H1) as [A1 B1]. destruct (G F' H2) as [A2 B2]. destruct (G n H3) as [A3 B3]. destruct (G n' H4) as [A4 B4].
lia.
Qed.
(* copied from lib/A/Prog/check_words_pin_set.v:113-119 (cw_lt_atom): a signed compare of a small atom with a literal *)
Lemma cw1_lt_atom : forall E n v z, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = (v <? z).
Proof.
intros E n v z Hn Hv Hz. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)). change (bv_signed (sv_denot E (SLit z))) with (Sg E (SLit z)).
rewrite S_SOff, S_SLit, Hn, Z.add_0_r, unsigned_lit_small by lia. rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* reading the symbolic state back at a cut: a register that holds an atom, an 8-byte and a 1-byte chunk of a region *)
Lemma cw_reg_atom : forall (H : word -> bool) E ss ms (r : bv 5) n,
st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros H E ss ms r n HS Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma cw_rd_chunk8 : forall E H mem base off a n v cs,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 8 (SOff n 0))) cs ->
a = base + off -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros E H mem base off a n v cs Hc Hin -> Hn Hv. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ base off 8 (SOff n 0) v Hc);
[cbn [sv_denot]; rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Hv | cbn; lia].
Qed.
Lemma cw_rd_chunk1 : forall E H mem base off a cs,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) base) cs -> In (YP09.mkChunk off (CVal 1 (SLit 0))) cs ->
a = base + off -> aview SEGS H mem a = Some 0.
Proof.
intros E H mem base off a cs Hc Hin ->. rewrite Forall_forall in Hc. specialize (Hc _ Hin).
apply aview_of_val_mem1; [|lia].
apply (val_of_chunk_ok SEGS E _ base off 1 (SLit 0) 0 Hc); [reflexivity | cbn; lia | cbn; lia].
Qed.
(* the saved registers, from the chunks the prologue's stores left in the stack region *)
Lemma cw_saved_ok : forall E H mem sp0 (regs : bvmap 5 word) cs,
Forall (YP09.chunk_ok SEGS E (mrestrict H mem) sp0) cs ->
(forall j r, nth_error cw_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
(forall r, In r cw_saved -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r)) ->
forall j r, nth_error cw_saved j = Some r ->
rdword (aview SEGS H mem) (sp0 - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros E H mem sp0 regs cs Hc Hin Hv j r Hj.
apply (cw_rd_chunk8 E H mem sp0 (-8 - 8 * Z.of_nat j) _ (Z.to_nat r) _ cs Hc (Hin j r Hj)); [lia | |].
- rewrite (Hv r (nth_error_In _ _ Hj)). symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Rg. change (bv_modulus 64) with (2 ^ 64) in Rg. exact Rg.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI : Z.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the entry seed: the symbolic state at chain_words' entry (0x8dfd4), copied from numberE.v's n_entry with
   chain_words' 128-byte prologue frame and 13 saved registers *)
Lemma cw_entry : forall STK W ly S regs mem md ch,
afn_pre SEGS B STK ly S W regs mem md ch -> 144 <= STK ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cw_extra (spZ regs) (as_uar_cell B)))) ss_cw0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_chain_words)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch HPRE HSTK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
set (sp0 := spZ regs) in *.
destruct (cw_nsp1_facts sp0 Hal16) as (Hs1al & Hs1).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cw_extra sp0 (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (cw_extra sp0 (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth cw_extra map] in E32, E33, E34. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_cw0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold cw_regions0, cw_stk_lo, cw_stk_hi, cw_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB N_SP1 (cw_nsp1 sp0) E33) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
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
unfold cw_regions0, cw_stk_lo, cw_stk_hi, cw_stk_s1, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB N_SP1 (cw_nsp1 sp0) E33), (VB N_UAR (as_uar_cell B) E34) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Hob0 Hob1 Hob12 Huar Hsep Hs1. clear. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I|]].
2: { cbn [f_alias alias_ok cw_alias0]. split; [|exact I]. cbn [sv_denot]. rewrite Usp, E33, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite <- (cw_nsp1_and sp0) by lia. reflexivity. }
cbn [f_atoms atoms_ok cw_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Huar Huar4 Hs1al Hs1 Hal16. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Hypothesis SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS.
(* awr_ok reads only the regions' bases and windows *)
Lemma cw_awr_skel : forall Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own,
skeleton rs' = skeleton rs -> awr_ok SEGS B Ex rs STK sp0 FP bl0 blc fr0 lyx own -> awr_ok SEGS B Ex rs' STK sp0 FP bl0 blc fr0 lyx own.
Proof. intros Ex rs rs' STK sp0 FP bl0 blc fr0 lyx own Hsk H a Ha. apply H. exact (in_wrange_skeleton Ex rs' rs a Hsk Ha). Qed.
Lemma cw_S1 : cw_S1P B MT RLO RHI.
Proof.
unfold cw_S1P. intros c HPRE HR HC.
assert (HSTK : 12400 <= CHAIN_WORDS_STK) by
(unfold CHAIN_WORDS_STK; pose proof (Z.le_max_l NUMBER_STK (Z.max SUP_CHAIN_STK SUP_RESP_STK)); unfold NUMBER_STK, ESTACK in *; lia).
pose proof HPRE as HPRE2.
destruct HPRE2 as [cp_afn cp_rod cp_a0 cp_tok64 cp_a1 cp_tokobj cp_toks cp_cb cp_cbO cp_ntok cp_ntokr cp_verb cp_rec cp_refuse cp_calls cp_ro cp_vobjs cp_frames cp_nev cp_live cp_meter].
set (regs := x_regs c) in *. set (ly := x_ly c) in *. set (S := x_S c) in *.
set (W := x_W c) in *. set (mem := x_mem c) in *. set (md := x_md c) in *.
pose proof cp_afn as HAFN.
destruct HAFN as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstkd & Hpres0 & Hch0 & HQT0).
destruct Hstkd as (Hal16 & Hsp00 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
destruct (cw_nsp1_facts (spZ regs) Hal16) as (Hs1al & Hs1).
pose proof (cw_entry CHAIN_WORDS_STK W ly S regs mem md (x_ch c) cp_afn ltac:(lia)) as HS.
pose proof (ajournal_init SEGS B CHAIN_WORDS_STK (cw_FP c) ly S W regs mem md (x_ch c) cp_afn) as HJ.
remember (Eimg (Ereg regs (cw_extra (spZ regs) (as_uar_cell B)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (cw_extra (spZ regs) (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as E33t. cbn [Nat.add nth cw_extra map] in E33t.
assert (E33 : ew E N_SP1 = Z_to_bv 64 (cw_nsp1 (spZ regs))) by (change N_SP1 with (32 + 1)%nat; exact E33t).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS1R : 0 <= cw_nsp1 (spZ regs) < 2 ^ 64) by (destruct Hs1 as [Hq | Hq]; rewrite Hq; lia).
assert (Usp1 : bv_unsigned (ew E N_SP1) = spZ regs + (cw_nsp1 (spZ regs) - spZ regs))
by (rewrite E33, (unsigned_lit_small _ HS1R); lia).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 2%nat ltac:(lia)) as E34. cbn [Nat.add nth cw_extra map] in E32, E34.
clear HE E33t EX.
unfold cfg_at. change (w64 (BASE + AF_chain_words)) with (Z_to_bv 64 (BASE + AF_chain_words)).
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) mem).
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
eapply awr_ok_cons_stack_off with (n := N_SP1) (d := cw_nsp1 (spZ regs) - spZ regs);
[reflexivity | exact Usp1 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
(* the call of __asan_stack_malloc_3 (0x8e044) *)
rename HF into HF1, HFr into HFr1, HG into HG1.
(* the prologue wrote only its own stack window *)
lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms1) =>
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHAIN_WORDS_STK <= a < spZ regs) -> rdW W (ms_mem ms1) a = rdW W mem a) end.
{ intros a Ha Hn. apply (kept_of_frame E _ (w_H W) mem _ (fun x => spZ regs - CHAIN_WORDS_STK <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
intros b wlo whi x Hin Hx.
lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp, ?Usp1 in Hx; cbv beta; lia |]).
destruct Hin. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md1 := mm) in *; clearbody md1 end.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
pose proof (palf_sm B TLF 3 ltac:(cbn; tauto)) as HSM3. change (cs_stack_malloc 3) with CS___asan_stack_malloc_3 in HSM3.
rewrite HSM3.
assert (HS1b : spZ regs - 144 <= cw_nsp1 (spZ regs) <= spZ regs - 128) by (destruct Hs1 as [Hq | Hq]; lia).
assert (Ho16 : (cw_nsp1 (spZ regs) - spZ regs) mod 16 = 0)
by (destruct Hs1 as [Hq | Hq]; rewrite Hq; [replace (spZ regs - 128 - spZ regs) with (-128) by lia
| replace (spZ regs - 144 - spZ regs) with (-144) by lia]; reflexivity).
pose proof (count_cid_le_length 3 (frames S)) as Hcnt.
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 3 (SM3 fx) ltac:(lia) W (ms_regs ms) (ms_mem ms)
CHAIN_WORDS_STK (spZ regs) (cw_FP c) ly S W mem md [] ly S md1 0 (cw_nsp1 (spZ regs) - spZ regs) _ HJ).
- unfold spZ at 1. rewrite R2. exact Usp1.
- exact Ho16.
- lia.
- change ESTACK with 4096. lia.
- rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp0.
- rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp0.
- exact R1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- change (fs_frames 3) with 2048. lia. }
cbv beta. clear R1 R2 R3 R4 SHOK HSM3.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJ1 & (fS2 & ES2)).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (3, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres).
destruct (al_flag _ _ LAWS _ _ _ _ _ 3 fpos HAR2 Hfin2) as (HFLp & HFLo & HFLapp & HFLce).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 fpos HAR2 Hfin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes 3) with 512 in *. change (512 / 8) with 64 in HFSpres.
set (F := frame_addr ly 3 fpos) in *. set (FL := flag_addr ly 3 fpos) in *.
assert (HFLr : 0 <= FL < 2 ^ 64) by (destruct HFLapp as [Hq _]; lia).
assert (HFrg : 0 <= F < 2 ^ 64) by lia.
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
(* re-seat after the call: the three stack regions are kept *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_stack_aj SEGS B) with (sp := spZ regs); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | lia | lia].
- eapply (region_kept_stack_aj SEGS B) with (sp := spZ regs); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | lia | lia].
- eapply (region_kept_stack_aj SEGS B) with (sp := cw_nsp1 (spZ regs));
[exact HK | exact HJ2 | rewrite E33; exact (unsigned_lit_small _ HS1R) | lia | lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
pose proof (st_ok_pi_havoc_hi 1040 _ _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc (havoc E 1024 (map (getr regs2) CLOB)) 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Ev eqn:HEv in HS.
assert (V2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite HEv, !ew_havoc_old by lia; exact Usp).
assert (V33 : bv_unsigned (ew Ev 33) = cw_nsp1 (spZ regs))
by (rewrite HEv, !ew_havoc_old by lia; rewrite E33; exact (unsigned_lit_small _ HS1R)).
assert (V32 : ew Ev 32 = Z_to_bv 64 SB) by (rewrite HEv, !ew_havoc_old by lia; exact E32).
assert (V1028 : ew Ev 1028 = Z_to_bv 64 F).
{ rewrite HEv, ew_havoc_old by lia. change 1028%nat with (1024 + 4)%nat.
rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia). exact Ha0. }
assert (V1040 : ew Ev 1040 = Z_to_bv 64 FL)
by (rewrite HEv; exact (ew_havoc_new _ 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (V1041 : ew Ev 1041 = Z_to_bv 64 (SB + F / 8))
by (rewrite HEv; exact (ew_havoc_new _ 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEIv : img_env VAL A_LIM Ev)
by (rewrite HEv; apply img_env_havoc_hi; [apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia] | unfold A_LIM; lia]).
assert (UF : bv_unsigned (ew Ev 1028) = F) by (rewrite V1028; exact (unsigned_lit_small _ HFrg)).
assert (USh : bv_unsigned (ew Ev 1041) = SB + F / 8) by (rewrite V1041; apply unsigned_lit_small; unfold SB; lia).
(* the frame's shadow address s2 = (s8 >> 3) + s7 is the atom 1041 *)
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 1028 32 1041 F SB V1028 HFrg V32 V1041)) as HS3.
clear HS. rename HS3 into HS.
(* the frame (atom 1028, its flag pointer at +504 the atom 1040) and its shadow (atom 1041) *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
assert (RFR : region_ok SEGS Ev (ms_mem msx) (fframe_region 1028 1040 3 []));
[ unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 3) with 512; rewrite UF;
split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ F (512 - 8) 8 (SOff 1040 0) FL);
[ cbn [sv_denot]; rewrite V1040, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside
| replace (F + (512 - 8)) with (F + 512 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag) ] ]
| ];
assert (DFR : all_disjoint Ev (fframe_region 1028 1040 3 []) (ss_mem ssx));
[ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
unfold fframe_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 3) with 512; rewrite UF, V2, V33; repeat split; lia
| ] end.
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 1028 1040 3 []) HS eq_refl RFR DFR) as HS3. clear HS RFR DFR. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
assert (RSH : region_ok SEGS Ev (ms_mem msx) (fshadow_region 1041 3 0 64 []));
[ unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
change (fs_frame_bytes 3 / 8) with 64; rewrite USh;
split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); pose proof (proj1 (HFSpres o ltac:(lia))) as Hq;
unfold shadow_addr, SHADOW_OFF in Hq; unfold SB; exact Hq
| apply Forall_nil ]
| ];
assert (DSH : all_disjoint Ev (fshadow_region 1041 3 0 64 []) (ss_mem ssx));
[ lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
unfold fshadow_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 3 / 8) with 64; rewrite USh, UF, V2, V33; unfold SB;
destruct HFapp as (HFa1 & [HFa2 | (HFa3 & HFa4)]); unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia
| ] end.
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 1041 3 0 64 []) HS eq_refl RSH DSH) as HS3. clear HS RSH DSH. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
(* the frame is a 32-aligned side-stack address (bnez s3 at 0x8e058 is taken) *)
pose proof (st_ok_pi_add_fact Ev _ _ 1028 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite UF; change (2 ^ 5) with 32; lia)) as HS3.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
clear HJ HJ1.
(* what the code below may write: the frame, its shadow, and the three stack regions *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
assert (AWR2 : awr_ok SEGS B Ev (ss_mem ssx) CHAIN_WORDS_STK (spZ regs) (cw_FP c) (ablocks B ly S) (ablocks B ly S2) (frames S) ly [(3, fpos)]) end.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
eapply awr_ok_cons_gen with (n := 1041%nat) (b := SB + F / 8); [reflexivity | exact USh | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 3, fpos. split; [left; reflexivity|].
right. change (frame_addr ly 3 fpos) with F. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd].
change (fs_frame_bytes 3 / 8) with 64. unfold SB in Ha. lia. }
eapply awr_ok_cons_gen with (n := 1028%nat) (b := F); [reflexivity | exact UF | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 3, fpos. split; [left; reflexivity|].
left. change (frame_addr ly 3 fpos) with F. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 3) with 512. lia. }
eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact V2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact V2 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
eapply awr_ok_cons_stack_off with (n := N_SP1) (d := cw_nsp1 (spZ regs) - spZ regs);
[reflexivity | rewrite V33; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
apply awr_ok_nil. }
(* the frame words, the 88 shadow stores of the entry poison, to the branch on ntok < 3 (0x8e1e8) *)
paj_run_sh RUNP HS HJ2.
{ exact AWR2. }
rename HF into HF2, HFr into HFr2, HG into HG2.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md3 := mm) in *; clearbody md3 end.
cbn [ms_mem mkst] in HFr2.
(* what both cuts of this segment need, read off the symbolic state at the branch (0x8e1e8) *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssB (restrict _ ?msB) =>
assert (CUT : forall ssK msK mdK, st_ok_pi SEGS VAL Ev ssK (restrict (w_H W) msK) ->
ss_regs ssK = ss_regs ssB -> ss_mem ssK = ss_mem ssB ->
ajournal SEGS B CHAIN_WORDS_STK (spZ regs) (cw_FP c) ly S W mem md [(3, fpos)] ly S2 W (ms_mem msK) mdK 0 ->
frame_of Ev (ss_mem ssB) (mrestrict (w_H W) (ms_mem msB)) (mrestrict (w_H W) (ms_mem msK)) ->
cw_pc B MT (cw_setpos c fpos) ly S2 W (ms_regs msK) (ms_mem msK) mdK /\
getr (ms_regs msK) 20 = w64 (x_ntok c) /\ getr (ms_regs msK) 21 = w64 (x_tok c) /\ getr (ms_regs msK) 23 = w64 SB) end.
{ intros ssK msK mdK HSK HrK HmK HJK HFK.
assert (EvE : forall n, (n < 1024)%nat -> ew Ev n = ew E n) by (intros n Hn; rewrite HEv, !ew_havoc_old by lia; reflexivity).
assert (RA : forall (r : bv 5) n, sr_get (ss_regs ssK) r = SOff n 0 -> getr (ms_regs msK) r = ew Ev n)
by (intros r n Hr; exact (cw_reg_atom (w_H W) Ev ssK msK r n HSK Hr)).
rewrite HrK in RA.
assert (G2 : getr (ms_regs msK) 2 = w64 (cw_nsp1 (spZ regs)))
by (rewrite (RA 2%bv 33%nat ltac:(vm_compute; reflexivity)), EvE by lia; exact E33).
assert (G9 : getr (ms_regs msK) 9 = w64 (cw_nsp1 (spZ regs)))
by (rewrite (RA 9%bv 33%nat ltac:(vm_compute; reflexivity)), EvE by lia; exact E33).
assert (G3 : getr (ms_regs msK) 3 = w64 (as_gp B))
by (rewrite (RA 3%bv 3%nat ltac:(vm_compute; reflexivity)), EvE, (EE 3%nat 3%bv eq_refl) by lia; exact Hgp0).
assert (G4 : getr (ms_regs msK) 4 = w64 (as_tp B))
by (rewrite (RA 4%bv 4%nat ltac:(vm_compute; reflexivity)), EvE, (EE 4%nat 4%bv eq_refl) by lia; exact Htp0).
assert (G8 : getr (ms_regs msK) 8 = w64 (spZ regs))
by (rewrite (RA 8%bv 2%nat ltac:(vm_compute; reflexivity)), EvE, E2 by lia; unfold w64, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (G18 : getr (ms_regs msK) 18 = w64 (SB + F / 8)) by (rewrite (RA 18%bv 1041%nat ltac:(vm_compute; reflexivity)); exact V1041).
assert (G19 : getr (ms_regs msK) 19 = w64 F) by (rewrite (RA 19%bv 1028%nat ltac:(vm_compute; reflexivity)); exact V1028).
assert (G24 : getr (ms_regs msK) 24 = w64 F) by (rewrite (RA 24%bv 1028%nat ltac:(vm_compute; reflexivity)); exact V1028).
assert (G20 : getr (ms_regs msK) 20 = w64 (x_ntok c))
by (rewrite (RA 20%bv 11%nat ltac:(vm_compute; reflexivity)), EvE, (EE 11%nat 11%bv eq_refl) by lia; exact cp_a1).
assert (G21 : getr (ms_regs msK) 21 = w64 (x_tok c))
by (rewrite (RA 21%bv 10%nat ltac:(vm_compute; reflexivity)), EvE, (EE 10%nat 10%bv eq_refl) by lia; exact cp_a0).
assert (G23 : getr (ms_regs msK) 23 = w64 SB) by (rewrite (RA 23%bv 32%nat ltac:(vm_compute; reflexivity)), EvE by lia; exact E32).
assert (RK : forall i r, nth_error (ss_mem ssK) i = Some r -> region_ok SEGS Ev (mrestrict (w_H W) (ms_mem msK)) r)
by (intros i r Hi; exact (st_ok_pi_region_nth Ev ssK (restrict (w_H W) msK) i r HSK Hi)).
rewrite HmK in RK.
lazymatch type of HrK with _ = ss_regs ?ssB =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
let r1 := eval vm_compute in (nth 1 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
let r3 := eval vm_compute in (nth 3 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (RK 0%nat r0 ltac:(vm_compute; reflexivity)) as RSH;
pose proof (RK 1%nat r1 ltac:(vm_compute; reflexivity)) as RFR;
pose proof (RK 3%nat r3 ltac:(vm_compute; reflexivity)) as RST end.
destruct RSH as (_ & _ & _ & CSH). destruct RFR as (_ & _ & _ & CFR). destruct RST as (_ & _ & _ & CST).
cbn [YP09.r_base YP09.r_chunks base_val] in CSH, CFR, CST. rewrite USh in CSH. rewrite UF in CFR. rewrite V2 in CST.
(* the bytes the code after the call did not write: outside the stack window, the frame and its shadow *)
pose proof HK as (HK1 & HK2 & HK3 & HK4 & _).
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHAIN_WORDS_STK <= a < spZ regs) -> ~ (F <= a < F + 512) ->
~ (SB + F / 8 <= a < SB + F / 8 + 64) -> rdW W (ms_mem msK) a = rdW W mem2 a).
{ intros a Ha N1 N2 N3.
assert (HWZ : forall rs, windows rs = [(Some 1041%nat, 0, 64); (Some 1028%nat, 0, 512); (Some 2%nat, -128, -120); (Some 2%nat, -104, 0); (Some 33%nat, 8, 16)] ->
forall b wlo whi x, In (b, wlo, whi) (windows rs) -> base_val Ev b + wlo <= x < base_val Ev b + whi ->
(fun y => (spZ regs - CHAIN_WORDS_STK <= y < spZ regs) \/ (F <= y < F + 512) \/ (SB + F / 8 <= y < SB + F / 8 + 64)) x).
{ intros rs Hw b wlo whi x Hin Hx. rewrite Hw in Hin. cbn [In] in Hin.
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?USh, ?UF, ?V2, ?V33 in Hx; cbv beta; lia |]).
destruct Hin. }
assert (HnZ : ~ (fun y => (spZ regs - CHAIN_WORDS_STK <= y < spZ regs) \/ (F <= y < F + 512) \/ (SB + F / 8 <= y < SB + F / 8 + 64)) a)
by (cbv beta; intros [Hq|[Hq|Hq]]; contradiction).
lazymatch type of HFr2 with frame_of _ ?rsA _ _ =>
lazymatch type of HmK with _ = ss_mem ?ssB =>
lazymatch type of HFK with frame_of _ _ (mrestrict _ (ms_mem ?msB)) _ =>
rewrite (kept_of_frame Ev (ss_mem ssB) (w_H W) (ms_mem msB) (ms_mem msK) _ HFK (HWZ (ss_mem ssB) ltac:(vm_compute; reflexivity)) a Ha HnZ);
exact (kept_of_frame Ev rsA (w_H W) mem2 (ms_mem msB) _ HFr2 (HWZ rsA ltac:(vm_compute; reflexivity)) a Ha HnZ) end end end. }
split; [split|].
- (* the frame part *)
constructor.
+ exact HJK.
+ exact G2.
+ exact G3.
+ exact G4.
+ exact G8.
+ exact G9.
+ exact G18.
+ exact G19.
+ exact G24.
+ change (forall j r, nth_error cw_saved j = Some r ->
rdword (rdW W (ms_mem msK)) (spZ regs - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 r)))).
apply (cw_saved_ok Ev (w_H W) (ms_mem msK) (spZ regs) regs _ CST).
* intros j r Hj. do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; repeat (first [left; reflexivity | right]) |]).
destruct j; cbn in Hj; discriminate.
* intros r Hr. cbn in Hr. repeat (destruct Hr as [<- | Hr]; [rewrite EvE by (cbn; lia); apply EE; reflexivity |]). destruct Hr.
+ apply (cw_rd_chunk8 Ev (w_H W) (ms_mem msK) F 504 _ 1040 _ _ CFR);
[repeat (first [left; reflexivity | right]) | reflexivity | exact V1040 | exact HFLr].
- (* nothing the caller can see has changed *)
constructor.
+ change (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W (ms_mem msK) a = rdW W mem a).
intros a Himg Hown Herr. pose proof (pa_img_range _ Himg) as HIR.
pose proof (frm_off_imgP B ly S2 W mem2 md2 3 fpos HAR2 Hfin2) as HFoi. unfold off_img in HFoi.
change (fs_frame_bytes 3) with 512 in HFoi. change (frame_addr ly 3 fpos) with F in HFoi.
rewrite (K3 a); [| lia | lia | lia | unfold SB; lia].
rewrite (HK3 a Himg Hown Herr). apply K1; lia.
+ change (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> rdW W (ms_mem msK) (p + i) = rdW W mem (p + i)).
intros p n i Hin Hi.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR0 Hin) as (Hp16 & Hp4096 & Hpce & Hpapp & _).
assert (Hin2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 p n 3 fpos HAR2 Hin2 Hfin2) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 3) with 512 in Hd. change (frame_addr ly 3 fpos) with F in Hd.
rewrite (K3 (p + i)); [| lia | lia | lia |].
2: { intros Hsh. apply (fshadow_not_app F 64 p (req_size n) (p + i) HF4096 ltac:(lia) Hpapp); [unfold SB in Hsh; lia | lia]. }
rewrite (HK2 p n i Hin Hi (fun H => H)). apply K1; lia.
+ change (forall cid pos a, In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
rdW W (ms_mem msK) a = rdW W mem a).
intros cid pos a Hin Ha. pose proof Ha as HaO.
destruct (frame_al64 SEGS B ly S W mem md cid pos HAR0 Hin) as (Hf64 & Hfs64 & Hfs).
destruct (frame_al64 SEGS B ly S2 W mem2 md2 3 fpos HAR2 Hfin2) as (HF64 & _ & _). change (frame_addr ly 3 fpos) with F in HF64.
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR0 Hin) as (_ & Hfapp & _ & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR0 Hin) as (Hf4 & Hfce & _).
destruct (in_split _ _ Hin) as (l1 & l2 & El).
pose proof (sep_frames_pos SEGS B LAWS ly S2 W mem2 md2 (3, fpos) (cid, pos) [] l1 l2 HAR2 ltac:(rewrite Hfrs2, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 3) with 512 in Hd. change (frame_addr ly 3 fpos) with F in Hd.
unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Ha. cbn [fst snd] in Ha.
set (F' := frame_addr ly cid pos) in *. set (n' := fs_frame_bytes cid) in *.
pose proof (Z.div_mod F' 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound F' 8 ltac:(lia)) as D2.
pose proof (Z.div_mod n' 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound n' 8 ltac:(lia)) as D4.
destruct Ha as [Ha | Ha].
* rewrite (K3 a); [| lia | lia | lia |].
2: { intros Hsh. apply (fshadow_not_app F 64 F' n' a HF4096 ltac:(lia) Hfapp); [unfold SB in Hsh; lia | lia]. }
rewrite (HK4 cid pos a Hin HaO (fun H => H)). apply K1; lia.
* rewrite (K3 a); [| lia | lia | |].
3: { intros Hsh. apply (cw_shadow_disj F F' 512 n' (a - SB) HF64 Hf64 eq_refl Hfs64 Hd);
[change (512 / 8) with 64; unfold SB in Hsh |- *; lia | unfold SB; lia]. }
2: { intros Hf. apply (fshadow_not_app F' (n' / 8) F 512 a Hf4 ltac:(lia) HFapp); [exact Ha | exact Hf]. }
rewrite (HK4 cid pos a Hin HaO (fun H => H)). apply K1; lia.
+ change (Permutation (ablocks B ly S2) (ablocks B ly S)). rewrite Eab. apply Permutation_refl.
+ change (st_nev S2 <= st_nev S). lia.
+ exact Hbb2.
+ change (mo_le MT S S2 0). rewrite ES2. apply (mo_le_set_fs_r MT MTFL). exact (mle_start MT S MTL).
+ change (forall i, 4 <= i < 36 -> rdW W (ms_mem msK) (SB + F / 8 + i) = Some 0).
intros i Hi. apply (cw_rd_chunk1 Ev (w_H W) (ms_mem msK) (SB + F / 8) i _ _ CSH); [| reflexivity].
assert (Hk : exists k, (k < 32)%nat /\ i = 4 + Z.of_nat k) by (exists (Z.to_nat (i - 4)); split; lia).
destruct Hk as (k & Hk & ->).
do 32 (destruct k as [|k]; [cbn; repeat (first [left; reflexivity | right]) |]). lia.
- split; [exact G20|]. split; [exact G21 | exact G23]. }
lazymatch type of RUNP with forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
let why := eval vm_compute in (sym_step_pi tpi ssx) in
lazymatch why with PStop (SR_branch ?cc ?aa ?bb) =>
apply (BR Wx Ex ssx msx _ _ cc aa bb HS); clear HS; intros Hc HS end end end.
- (* ntok < 3: the refusal cut KR (0x8e278) *)
paj_run_to_sh RUNTOP HS HJ2 (AF_chain_words + 0x2a4).
{ lazymatch type of AWR2 with awr_ok _ _ _ ?rsA _ _ _ _ _ _ _ _ =>
apply (cw_awr_skel _ rsA); [vm_compute; reflexivity | exact AWR2] end. }
rename HF into HF3, HFr into HFr3, HG into HG3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md4 := mm) in *; clearbody md4 end.
lazymatch type of HS with st_ok_pi _ _ _ ?ssK (restrict _ ?msK) =>
destruct (CUT ssK msK md4 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ2 HFr3) as (CPC & _ & _ & _);
pmkst HS;
change (SRr SEGS W (cfg_at SEGS (BASE + CW_KR) (ms_regs msK) (ms_mem msK) md4) (cw_post B MT c));
apply (HR fpos ly S2 W (ms_regs msK) (ms_mem msK) md4) end.
split; [exact CPC|].
rewrite (cw1_lt_atom Ev 11 (x_ntok c) 3) in Hc;
[| rewrite HEv, !ew_havoc_old by lia; rewrite (EE 11%nat 11%bv eq_refl); exact cp_a1 | lia | lia].
apply Z.ltb_lt in Hc.
change (VerbsRun.chain_run (x_R c) (tl (x_tks c)) = sup_resp_m (x_R c) Verbs.err_invalid_operation).
pose proof cp_ntok as Hn. revert Hn. destruct (x_tks c) as [|t0 [|t1 [|t2 rest]]]; cbn [length]; intros Hn;
[lia | reflexivity | reflexivity | lia].
- (* ntok >= 3: the cut KC (0x8e1ec) *)
paj_run_to_sh RUNTOP HS HJ2 (AF_chain_words + 0x218).
{ lazymatch type of AWR2 with awr_ok _ _ _ ?rsA _ _ _ _ _ _ _ _ =>
apply (cw_awr_skel _ rsA); [vm_compute; reflexivity | exact AWR2] end. }
rename HF into HF3, HFr into HFr3, HG into HG3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md4 := mm) in *; clearbody md4 end.
lazymatch type of HS with st_ok_pi _ _ _ ?ssK (restrict _ ?msK) =>
destruct (CUT ssK msK md4 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ2 HFr3) as (CPC & G20 & G21 & G23);
pmkst HS;
change (SRr SEGS W (cfg_at SEGS (BASE + CW_KC) (ms_regs msK) (ms_mem msK) md4) (cw_post B MT c));
apply (HC fpos ly S2 W (ms_regs msK) (ms_mem msK) md4) end.
split; [exact CPC|]. split; [exact G20|]. split; [exact G21|]. split; [exact G23|].
rewrite (cw1_lt_atom Ev 11 (x_ntok c) 3) in Hc;
[| rewrite HEv, !ew_havoc_old by lia; rewrite (EE 11%nat 11%bv eq_refl); exact cp_a1 | lia | lia].
apply Z.ltb_ge in Hc. exact Hc.
Qed.
End e.
End f.
End d.
