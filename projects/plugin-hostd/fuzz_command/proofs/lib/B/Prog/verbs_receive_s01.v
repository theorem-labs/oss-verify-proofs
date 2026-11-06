(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S01 (the prologue, 0x8ce4c .. 0x8cf98) of the walk of verbs_receive
   on the ASan+UBSan build of plugin-hostd/fuzz_command (image B, gen/dis/verbs_receive.s). vr_s01 proves vr_s01_stmt
   of lib/B/Prog/verbs_receive_iface.v: from the statement's premises (vr_ent) the function runs to 0x8cf9c with the
   state vr_b1. The structure and the tactic skeleton are the A walk's lib/A/Prog/verbs_receive_s01.v
   (a working branch); every symbolic run is redone on B's instructions.

   The walk: the symbolic executor runs the prologue (the 192-byte frame and the 13 saves, s0 = sp0, the realigned
   stack pointer s1 = (sp - 192) & -32, the use-after-return flag through the GOT word 0xa5fa8 and the shadow offset
   through 0xa5f50 into s3, both const cells of the allocator record, s8 = msg; the branch 0x8ceb0 is decided by
   the flag cell's literal 1) to the call of __asan_stack_malloc_4 at 0x8ceb8 (SM4, through vr01_stack_malloc_at);
   the state is rebuilt over the frame F (a0) and its shadow shadow_addr F; the executor runs s4 = s6 = F (the
   branch 0x8cecc is decided by F >= 4096, so the probe loop 0x8ced0-0x8cee8 is not run), the spill s1 + 72, the
   frame header at F, s9 = shadow_addr F, the shadow f1 x4 and s11 = s9 + 4, to the call of __asan_set_shadow_f8 at
   0x8cf3c (SHF8, through vr01_set_shadow_at, lib/B/Prog/verbs_receive_s01_k.v); the state is rebuilt with msg+8's
   shadow byte (0, from afobj and the journal: it lies in a caller frame's shadow, outside the footprint) and with
   the fact on atom 10 (msg in [4096, 2 ^ 47], 8-aligned, from afobj and frames_bounds), and the executor runs the
   f2/f8/f3 shadow stores, the two UBSan checks on msg and the inline check of msg+8 to 0x8cf9c. The boundary state
   is then read off the symbolic state's regions (the frame's shadow, the header, the spill slot, the saves) and
   assembled by vr01_final of lib/B/Prog/verbs_receive_s01_f.v.

   B-only code in the range, walked by the third run: 0x8cf68 `li a0,-8` (codegen: the f8 byte of save's shadow is
   loaded on its own); 0x8cf7c `beqz s8` (UBSan: msg null) and 0x8cf84 `bnez s5` after `andi s5,s8,7` (UBSan: msg
   misaligned), both to the trap 0x8d938 and both decided by the facts on atom 10 (afobj: msg lies in a live frame,
   so 4096 <= msg, and msg mod 8 = 0); 0x8cf88 `addi a0,s8,8` (a0 = msg + 8, the address the inline check reads).

   Section hypotheses (About vr_s01): SM4, SMP, SHF8 (the runtime entries of verbs_receive_c.v, SM4 and SHF8 in its
   `forall fx0` form, used at the section's fx), TL, TLF (PALib / PALibF: the GOT and shadow cells and the stack
   entries, as every side-stack walk of lib/B/Prog takes them), ML, MTL, MTFL, ROA, RRO, RPG, RECC, PROGU (the record
   facts the interface names). The walk calls no program callee, and its two runtime entries take ecall_pre
   (lib/Reusable/YG0d.v:286), which asks no frame chain, so S01 builds none. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16 YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit verbs_receive_s01_k verbs_receive_s01_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* atoms of the entry state: 0-31 the registers, 32 the shadow base SB, 33 the realigned stack pointer s1, 34 the
   use-after-return flag cell; after the first call 1024..1039 the clobbered registers (1028 the frame F), 1040 the
   frame's shadow; after the second call 1056..1071, and 1072 the shadow byte of msg+8 *)
Definition vr01_vs1 (sp0 : Z) : Z := (sp0 - 192) - (sp0 - 192) mod 32.
Definition vr01_stk_z : YP09.region := YP09.mkRegion (Some 2%nat) (-192) (-184) (-192) (-184) [].
Definition vr01_stk_hi : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition vr01_regions0 : smem :=
[ vr01_stk_z; vr01_stk_hi; got_regionP; bcell_regionP 32; uar_got_regionP 34; uar_cell_regionP 34 ].
Definition vr01_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (33%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF SB SB 0); (34%nat, mkAF 0x10000 0x606000 2) ].
Definition vr01_alias0 : list (sv * sv) := [ (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32)), SOff 33 0) ].
Definition vr01_ss0 : sstate := mkSS AF_verbs_receive sr_atoms vr01_regions0 None (mkFacts vr01_atoms0 [] vr01_alias0).
Definition vr01_extra (sp0 uar : Z) : list word := map (Z_to_bv 64) [SB; vr01_vs1 sp0; uar].
Definition vr01_spill_r : YP09.region := YP09.mkRegion (Some 33%nat) 72 80 72 80 [].
Definition vr01_hdr_r : YP09.region := YP09.mkRegion (Some 1028%nat) 0 24 0 24 [].
Definition vr01_sh_a : YP09.region := YP09.mkRegion (Some 1040%nat) 0 4 0 4 [].
Definition vr01_sh_b : YP09.region := YP09.mkRegion (Some 1040%nat) 68 80 68 80 [].
Definition vr01_msh_r : YP09.region := YP09.mkRegion (Some 1072%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].

Lemma vr01_vs1_facts : forall sp0, sp0 mod 16 = 0 ->
vr01_vs1 sp0 mod 32 = 0 /\ (vr01_vs1 sp0 = sp0 - 192 \/ vr01_vs1 sp0 = sp0 - 208).
Proof.
intros sp0 H. unfold vr01_vs1. pose proof (Z.mod_pos_bound (sp0 - 192) 32 ltac:(lia)) as M.
assert (Hm : (sp0 - 192) mod 32 = 0 \/ (sp0 - 192) mod 32 = 16).
{ pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)) as D. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
rewrite H in D2. lia. }
split; [|lia].
replace ((sp0 - 192) - (sp0 - 192) mod 32) with (32 * ((sp0 - 192) / 32)) by (pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma vr01_vs1_and : forall sp0, 0 <= sp0 - 192 < 2 ^ 64 ->
alu64 ALU_AND (Z_to_bv 64 (sp0 - 192)) (Z_to_bv 64 (-32)) = Z_to_bv 64 (vr01_vs1 sp0).
Proof.
intros sp0 H. rewrite and_lit_Z. f_equal. rewrite zcanon_id by (unfold M64; lia).
change (zsigned64 (-32)) with (- 2 ^ 5). rewrite land_neg_pow2 by lia. reflexivity.
Qed.
Lemma vr01_val_mem1_of_aview : forall segs H (m : word -> option byte) a v, aview segs H m a = Some v -> 0 <= v < 256 ->
val_mem segs (mrestrict H m) a 1 v.
Proof.
intros segs H m a v Hv Hr k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
destruct (aview_byte segs H m a v Hv) as (b & Hb & Hbv & _). rewrite Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite <- Hbv.
cbv [YO0f.le_byte YG0f.le_byte]. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small v (2 ^ 8)) by (change (2 ^ 8) with 256; lia). rewrite !(Z.mod_small v 256) by lia. reflexivity.
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
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis SM4 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 4.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis SHF8 : forall fx0 : YK11.FPState, @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f8) 0xf8.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* the symbolic state at the entry (numberE.v's n_entry) *)
Lemma vr01_entry : forall STK W ly S regs mem md ch,
afn_pre SEGS B STK ly S W regs mem md ch -> 208 <= STK ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (vr01_extra (spZ regs) (as_uar_cell B)))) vr01_ss0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_verbs_receive)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch HPRE HSTK.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
set (sp0 := spZ regs) in *.
destruct (vr01_vs1_facts sp0 Hal16) as (Hs1al & Hs1).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (vr01_extra sp0 (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (vr01_extra sp0 (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth vr01_extra map] in E32, E33, E34. clear EX.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold vr01_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold vr01_regions0, vr01_stk_z, vr01_stk_hi, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 34 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB 34%nat (as_uar_cell B) E34) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold vr01_regions0, vr01_stk_z, vr01_stk_hi, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 34%nat (as_uar_cell B) E34) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Hob0 Hob1 Hob12 Huar Hsep. clear. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption) | lia ].
- split; [|split; [exact I|]].
2: { cbn [f_alias alias_ok vr01_alias0]. split; [|exact I]. cbn [sv_denot]. rewrite Usp, E33, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite <- (vr01_vs1_and sp0) by lia. reflexivity. }
cbn [f_atoms atoms_ok vr01_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 HSTK Huar Huar4 Hs1al Hs1 Hal16. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Ltac vr01_nss HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss3 ?d => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* the region of a symbolic state at an index, as a region_ok over the restricted memory *)
Ltac vr01_reg HS i Hr :=
lazymatch type of HS with
| st_ok_pi ?sg ?vl ?Ex ?ss ?ms =>
let r := eval vm_compute in (nth_error (ss_mem ss) i) in
lazymatch r with
| Some ?rr => pose proof (st_ok_pi_region_nth Ex ss ms i rr HS ltac:(vm_compute; reflexivity)) as Hr;
cbn [ms_mem restrict] in Hr
end
end.
(* one of the prologue's saves, read off the stack region of the state after the third run *)
Ltac vr01_sv HR U AE sp od n r :=
let Hw := fresh "Hw" in
pose proof (vr01_region_word _ _ _ _ 2%nat _ _ _ _ _ sp od (SOff n 0) HR U
ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as Hw;
cbn [sv_denot] in Hw; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hw;
rewrite (AE n r ltac:(lia) eq_refl) in Hw;
match goal with |- aval_mem _ ?a _ _ => replace a with (sp + od) by (cbn; lia) end;
exact Hw.

Lemma vr_s01 : vr_s01_stmt B MT.
Proof.
intros e He.
pose proof He as HE0.
destruct e as [ly S W regs mem md ch msg fd data n q0 ev D R O rest].
unfold vr_ent in He. cbn [e_ly e_S e_W e_regs e_mem e_md e_ch e_msg e_fd e_data e_n e_q0 e_ev e_D e_R e_O e_rest] in He.
destruct He as (HPRE & HROD & H10 & HOBJ & Hfd & Hdat & Hnv & Hn & HlenD & Hindat & Hnindat & HbD & Hmsg64 & HREP & Hcalls
& Hans & Hrep & Hnrep & Hdecl & HPerm & HQ0 & HGOT & HRO & HROIN & HVO & HERR & HFLAG & HAG & HFR4 & HEV & HLIVE & MOK
& HFRM0).
cbn [e_W e_regs e_mem e_md].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HAS : ASTACK = 16384) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HSTK : 208 + ASTACK <= VERBS_RECEIVE_STK) by (unfold VERBS_RECEIVE_STK; lia).
pose proof (vr01_entry VERBS_RECEIVE_STK W ly S regs mem md ch HPRE ltac:(lia)) as HS.
pose proof (ajournal_init SEGS B VERBS_RECEIVE_STK (VERBS_RECEIVE_PG ++ ablocks_fp O) ly S W regs mem md ch HPRE) as HJ.
set (sp0 := spZ regs) in *.
destruct (vr01_vs1_facts sp0 Hal16) as (Hs1al & Hs1).
set (s1 := vr01_vs1 sp0) in *.
assert (Hsp0r : 2 ^ 46 <= sp0 <= 2 ^ 47) by lia.
remember (Eimg (Ereg regs (vr01_extra sp0 (as_uar_cell B)))) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r).
{ intros nn r Hnn. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (vr01_extra sp0 (as_uar_cell B)) (Z_to_bv 64 0))
by (intros j Hj; rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. cbn [Nat.add nth vr01_extra map] in E32, E33. clear EX.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Us1 : bv_unsigned (ew E 33) = s1) by (rewrite E33; apply unsigned_lit_small; lia).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_verbs_receive)) with (Z_to_bv 64 (BASE + AF_verbs_receive)).
(* 0x8d480 .. 0x8d4ec: the saves, s1, the use-after-return flag (1: the frame is taken), a0 = 640 *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac; exact Usp. }
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 192 <= a < sp0) -> rdW W (ms_mem ms) a = rdW W mem a).
{ apply (kept_of_frame _ _ _ _ _ _ HFr). intros b wlo whi a Hin Hr. vm_compute in Hin.
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Usp in Hr; lia|]). destruct Hin. }
clear HF HFr HG.
(* 0x8d4ec: __asan_stack_malloc_4(640) *)
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
change (pa_sigma CS___asan_stack_malloc_4) with (pa_sigma (cs_stack_malloc 4)).
rewrite (palf_sm B TLF 4 ltac:(cbn; tauto)).
pose proof (count_cid_le_length 4 (frames S)) as Hcnt.
assert (HFF : fs_frames 4 = 1024) by reflexivity.
eapply SRr_bind.
{ eapply (vr01_stack_malloc_at SEGS B LAWS pa_segs_low (pal_env B TL) ML SMP 4 (SM4 fx) ltac:(lia) W (ms_regs ms) (ms_mem ms)
VERBS_RECEIVE_STK sp0 (VERBS_RECEIVE_PG ++ ablocks_fp O) ly S W mem md [] ly S _ 0 (s1 - sp0) _ HJ).
- unfold spZ. rewrite R2, Us1. lia.
- destruct Hs1 as [Hq | Hq]; rewrite Hq; [replace (sp0 - 192 - sp0) with (-192) by lia | replace (sp0 - 208 - sp0) with (-208) by lia]; reflexivity.
- lia.
- rewrite HES. lia.
- rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite HFF. lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin2 & Hnev2 & Hbb2 & Hz
& Hflag & HK & HJi & (fS & ES2) & HKo).
rewrite HES in HK, HKo. replace (sp0 + (s1 - sp0)) with s1 in HK, HKo by lia.
(* the state after the call: the two stack regions kept *)
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1]%nat HS2.
match type of HS2 with ?P -> _ => assert (HRK : P) end.
{ cbn [ms_mem restrict]. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp2 & _).
destruct HK as (K1 & _).
constructor; [|constructor; [|constructor]];
(eapply vr01_region_kept_hi; [exact Usp | intros a Ha; apply K1; lia | intros a Ha; apply Hp2; lia]). }
specialize (HS2 HRK). clear HRK. rewrite <- restrict_mkst_fx in HS2.
clear HS R1 R2 R3 R4.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS2.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (EO1 : forall nn, (nn < 1024)%nat -> ew E1 nn = ew E nn) by (intros nn Hnn; rewrite HE1; apply ew_havoc_old; exact Hnn).
assert (A1028 : ew E1 1028 = w64 (frame_addr ly 4 pos)).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbn; lia).
unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE1.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (4, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 4 pos HAR2 Hfin2) as (HF64 & _ & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR2 Hfin2) as (_ & _ & HFpres & HFSpres).
pose proof (frm_off_imgP B _ _ _ _ _ _ _ HAR2 Hfin2) as HFoff.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite HFB in *. change (1024 / 8) with 128 in HFSpres.
set (F := frame_addr ly 4 pos) in *.
set (sF := shadow_addr F) in *.
assert (HsF : sF = SB + F / 8) by reflexivity.
assert (HF8 : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 64 ltac:(lia)); pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia).
assert (HF64q : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8q : F / 8 = 8 * (F / 64)) by (rewrite HF64q at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; rewrite Z.div_mul by lia; lia).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 2 ^ 44 - 128) by (apply Z.div_lt_upper_bound; lia).
assert (HsF8 : sF mod 8 = 0) by (rewrite HsF, HF8q; unfold SB; replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia; apply Z_mod_mult).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
(* the frame's shadow as atom 1040, F's facts, the alias of its shadow address, the regions: the frame's header, the
   shadow bytes 0..3, the spill slot s1 + 72 *)
lazymatch type of HS2 with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1040 Ev ssv msv [Z_to_bv 64 sF] HS2 ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS2.
remember (havoc E1 1040 [Z_to_bv 64 sF]) as E2 eqn:HE2 in HS3.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
assert (EO2 : forall nn, (nn < 1040)%nat -> ew E2 nn = ew E1 nn) by (intros nn Hnn; rewrite HE2; apply ew_havoc_old; exact Hnn).
assert (A1040 : ew E2 1040 = Z_to_bv 64 sF) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 sF] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HE2.
assert (EL2 : forall nn, (nn < 1024)%nat -> ew E2 nn = ew E nn) by (intros nn Hnn; rewrite EO2, EO1 by lia; reflexivity).
assert (U1028 : bv_unsigned (ew E2 1028) = F) by (rewrite EO2, A1028 by lia; apply unsigned_lit_small; lia).
assert (HsFv : sF = 2147450880 + F / 8) by reflexivity.
assert (U1040 : bv_unsigned (ew E2 1040) = sF) by (rewrite A1040; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E2 2) = sp0) by (rewrite EL2 by lia; exact Usp).
assert (U33 : bv_unsigned (ew E2 33) = s1) by (rewrite EL2 by lia; exact Us1).
assert (E2_32 : ew E2 32 = Z_to_bv 64 SB) by (rewrite EL2 by lia; exact E32).
pose proof (st_ok_pi_add_fact E2 _ _ 1028 (mkAF 4096 (2 ^ 47) 6) HS3
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1028; change (2 ^ 6) with 64; repeat split; lia)) as HS4. clear HS3.
pose proof (st_ok_pi_add_fact E2 _ _ 1040 (mkAF (SB + 512) (SB + 2 ^ 44) 3) HS4
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U1040; change (2 ^ 3) with 8; unfold SB; repeat split; lia)) as HS3. clear HS4.
assert (AL1 : sv_denot E2 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0)) = sv_denot E2 (SOff 1040 0)).
{ rewrite (denot_shx E2 1028 32 0 F SB); [| rewrite EO2, A1028 by lia; reflexivity | exact E2_32 | lia | lia | lia | unfold SB; lia].
cbn [sv_denot]. rewrite A1040, unsigned_lit_small by lia. rewrite !Z.add_0_r. rewrite HsF. reflexivity. }
pose proof (st_ok_pi_add_alias E2 _ _ _ _ HS3 AL1) as HS4. clear HS3. vr01_nss HS4.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp2 & _).
pose proof (st_ok_pi_add_region E2 _ _ vr01_sh_a HS4 eq_refl
ltac:(unfold region_ok, vr01_sh_a; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U1040; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFSpres o ltac:(lia))))
ltac:(unfold vr01_sh_a; cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U1040, U2; lia)) as HS3.
clear HS4. vr01_nss HS3.
pose proof (st_ok_pi_add_region E2 _ _ vr01_hdr_r HS3 eq_refl
ltac:(unfold region_ok, vr01_hdr_r; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U1028; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
ltac:(unfold vr01_hdr_r; cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U1028, U1040, U2; lia)) as HS4.
clear HS3. vr01_nss HS4.
pose proof (st_ok_pi_add_region E2 _ _ vr01_spill_r HS4 eq_refl
ltac:(unfold region_ok, vr01_spill_r; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U33; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply Hp2; lia)
ltac:(unfold vr01_spill_r; cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U33, U1028, U1040, U2; lia)) as HS.
clear HS4. vr01_nss HS.
(* 0x8d4f0 .. 0x8d570: s2 = s4 = F, the spill, the header, s9 = shadow(F), f1 x4, a0 = s11 = shadow(F) + 4, a1 = 64 *)
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?fr ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk sp fp b0 bc fr lyx own) end.
eapply awr_ok_cons_stack_off with (n := 33%nat) (d := s1 - sp0); [reflexivity | rewrite U33; lia | cbn; lia | cbn; lia |].
eapply awr_ok_cons_gen with (n := 1028%nat) (b := F); [reflexivity | exact U1028 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 4, pos. split; [left; reflexivity|].
left. unfold in_zr. cbn [fst snd]. rewrite HFB. fold F. lia. }
eapply awr_ok_cons_gen with (n := 1040%nat) (b := sF); [reflexivity | exact U1040 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 4, pos. split; [left; reflexivity|].
right. unfold in_zr. cbn [fst snd]. rewrite HFB. fold F sF. change (1024 / 8) with 128. lia. }
eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; lia | cbn; lia |].
eapply awr_ok_cons_stack; [reflexivity | exact U2 | cbn; lia | cbn; lia |].
apply awr_ok_nil. }
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ (ms_mem ?msx)) =>
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 208 <= a < sp0) -> ~ (F <= a < F + 24) -> ~ (sF <= a < sF + 4) ->
rdW W (ms_mem msx) a = rdW W mem2 a) end.
{ intros a Ha H1 H2 H3. apply (kept_of_frame _ _ _ _ _ (fun x => (sp0 - 208 <= x < sp0) \/ (F <= x < F + 24) \/ (sF <= x < sF + 4)) HFr);
[| exact Ha | intros [Hx | [Hx | Hx]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx)]].
intros b wlo whi x Hin Hr. vm_compute in Hin.
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U2, ?U33, ?U1028, ?U1040 in Hr; lia|]). destruct Hin. }
clear HF HFr HG.
(* 0x8d570: __asan_set_shadow_f8(shadow(F) + 4, 64) *)
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
eapply SRr_bind.
{ eapply (vr01_set_shadow_at SEGS B LAWS pa_segs_low (SIGMA CS___asan_set_shadow_f8) 0xf8 (SHF8 fx) W _ _
VERBS_RECEIVE_STK sp0 (VERBS_RECEIVE_PG ++ ablocks_fp O) ly S W mem md [(4, pos)] ly S2 _ 0 (sF + 4) 64 4 pos (s1 - sp0) _ HJ2).
- left; reflexivity.
- rewrite R10, U1040. reflexivity.
- rewrite R11. reflexivity.
- lia.
- fold F sF. lia.
- fold F sF. rewrite HFB. change (1024 / 8) with 128. lia.
- unfold spZ. rewrite R2, U33. lia.
- destruct Hs1 as [Hq | Hq]; rewrite Hq; [replace (sp0 - 192 - sp0) with (-192) by lia | replace (sp0 - 208 - sp0) with (-208) by lia]; reflexivity.
- lia.
- rewrite HES. lia.
- rewrite R3, EL2, (EE 3%nat 3%bv eq_refl) by lia. exact Hgp.
- rewrite R4, EL2, (EE 4%nat 4%bv eq_refl) by lia. exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfill & Hkeep3).
(* the state after the call: the five regions kept *)
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _ & Hp3 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR3 Hfin2) as (_ & _ & HFpres3 & HFSpres3).
rewrite HFB in HFpres3, HFSpres3. change (1024 / 8) with 128 in HFSpres3. fold F sF in HFpres3, HFSpres3.
jafter_call_keep_hi HS 1056%nat regs3 (mrestrict (w_H W) mem3) HP3 [0;1;2;3;4]%nat HS2.
match type of HS2 with ?P -> _ => assert (HRK : P) end.
{ cbn [ms_mem restrict].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- eapply vr01_region_kept_hi; [exact U33 | intros a Ha; apply Hkeep3; lia | intros a Ha; apply Hp3; lia].
- eapply vr01_region_kept_hi; [exact U1028 | intros a Ha; apply Hkeep3; lia | intros a Ha; apply (proj1 (HFpres3 a ltac:(lia)))].
- eapply vr01_region_kept_hi; [exact U1040 | intros a Ha; apply Hkeep3; lia |].
intros a Ha. replace a with (sF + (a - sF)) by lia. apply (proj1 (HFSpres3 (a - sF) ltac:(lia))).
- eapply vr01_region_kept_hi; [exact U2 | intros a Ha; apply Hkeep3; lia | intros a Ha; apply Hp3; lia].
- eapply vr01_region_kept_hi; [exact U2 | intros a Ha; apply Hkeep3; lia | intros a Ha; apply Hp3; lia]. }
specialize (HS2 HRK). clear HRK. rewrite <- restrict_mkst_fx in HS2.
clear HS R1 R2 R3 R4 R10 R11.
remember (havoc E2 1056 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS2.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
assert (EO3 : forall nn, (nn < 1056)%nat -> ew E3 nn = ew E2 nn) by (intros nn Hnn; rewrite HE3; apply ew_havoc_old; exact Hnn).
clear HE3.
(* msg: its frame, and the shadow byte of msg+8, 0 at the entry and kept by the journal (a caller frame's shadow, outside
   the footprint) *)
destruct HOBJ as ((mcid & mpos & Hmin & Hmcid & Hmal & Hmlo & Hmhi) & Hm8 & Hmra).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ mcid mpos HAR Hmin) as (Hm4096 & Hmceil & Hmapp).
destruct (frame_al64 SEGS B _ _ _ _ _ mcid mpos HAR Hmin) as (Hmfa64 & Hmb64 & Hmb64').
set (fa := frame_addr ly mcid mpos) in *. set (fb := fs_frame_bytes mcid) in *.
assert (Hmsg8 : msg = 8 * (msg / 8)) by (pose proof (Z.div_mod msg 8 ltac:(lia)); lia).
assert (Hfa8 : fa = 8 * (fa / 8)) by (pose proof (Z.div_mod fa 64 ltac:(lia)); pose proof (Z.div_mod fa 8 ltac:(lia)); pose proof (Z.mod_pos_bound fa 8 ltac:(lia)); lia).
assert (Hfb8 : fb = 8 * (fb / 8)) by (pose proof (Z.div_mod fb 64 ltac:(lia)); pose proof (Z.div_mod fb 8 ltac:(lia)); pose proof (Z.mod_pos_bound fb 8 ltac:(lia)); lia).
set (sM := SB + (msg + 8) / 8).
assert (HsMv : sM = 2147450880 + msg / 8 + 1).
{ unfold sM, SB. replace (msg + 8) with ((msg / 8 + 1) * 8) by lia. rewrite Z.div_mul by lia. lia. }
assert (NFP : forall a, 2147450880 <= a < 2147450880 + 2 ^ 44 -> ~ inFP (VERBS_RECEIVE_PG ++ ablocks_fp O) a).
{ intros a Ha (r & Hr & Hrq). apply in_app_or in Hr as [Hr | Hr].
- unfold VERBS_RECEIVE_PG in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrq;
unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in Hrq; lia.
- destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Hrq))) as (p & nn & Hpn & Hpr).
pose proof (rec_repA_in_blocks B ly S _ R O (p, nn) HREP Hpn) as Hbl.
destruct (al_blocks _ _ LAWS ly S W mem md p nn HAR Hbl) as (_ & _ & _ & Happ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
destruct (Hmra (msg + 15) ltac:(lia)) as (s0v & Hs0 & Hsok).
assert (Hm15 : (msg + 15) mod 8 = 7) by (replace (msg + 15) with (7 + (msg / 8 + 1) * 8) by lia; rewrite Z.mod_add by lia; reflexivity).
assert (Hs00 : s0v = 0) by (destruct Hsok as [Hsok | (Hsok1 & Hsok2)]; [exact Hsok | lia]).
assert (HsMe : shadow_of_addr SHADOW_OFF (msg + 15) = sM).
{ unfold shadow_of_addr, SHADOW_OFF. rewrite HsMv. replace (msg + 15) with (7 + (msg / 8 + 1) * 8) by lia.
rewrite Z.div_add by lia. change (7 / 8) with 0. lia. }
assert (VM : rdW W mem3 sM = Some 0).
{ rewrite (F4 mcid mpos sM Hmin); [rewrite <- HsMe, Hs0, Hs00; reflexivity | | apply NFP; lia].
right. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. fold fa fb. lia. }
(* the own frame and msg's frame are apart, so are their shadows *)
destruct (in_split _ _ Hmin) as (l1 & l2 & El).
pose proof (sep_frames_pos SEGS B LAWS ly S2 W mem2 md2 (4, pos) (mcid, mpos) [] l1 l2 HAR2
ltac:(rewrite Hfrs2, El; reflexivity)) as HdFM.
unfold zdisjoint, frame_rng in HdFM. cbn [fst snd] in HdFM. rewrite HFB in HdFM. fold F fa fb in HdFM.
(* atom 1072: the shadow byte of msg+8 *)
lazymatch type of HS2 with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1072 Ev ssv msv [Z_to_bv 64 sM] HS2 ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS2.
remember (havoc E3 1072 [Z_to_bv 64 sM]) as E4 eqn:HE4 in HS3.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | cbv; lia]).
assert (EO4 : forall nn, (nn < 1072)%nat -> ew E4 nn = ew E3 nn) by (intros nn Hnn; rewrite HE4; apply ew_havoc_old; exact Hnn).
assert (A1072 : ew E4 1072 = Z_to_bv 64 sM) by (rewrite HE4; exact (ew_havoc_new E3 1072 [Z_to_bv 64 sM] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HE4.
assert (EL4 : forall nn, (nn < 1056)%nat -> ew E4 nn = ew E2 nn) by (intros nn Hnn; rewrite EO4, EO3 by lia; reflexivity).
assert (U4_1028 : bv_unsigned (ew E4 1028) = F) by (rewrite EL4 by lia; exact U1028).
assert (U4_1040 : bv_unsigned (ew E4 1040) = sF) by (rewrite EL4 by lia; exact U1040).
assert (U4_2 : bv_unsigned (ew E4 2) = sp0) by (rewrite EL4 by lia; exact U2).
assert (U4_33 : bv_unsigned (ew E4 33) = s1) by (rewrite EL4 by lia; exact U33).
assert (A2x : ew E4 2 = w64 sp0) by (unfold w64; rewrite <- U4_2; symmetry; apply Z_to_bv_bv_unsigned).
assert (A33x : ew E4 33 = w64 s1) by (unfold w64; rewrite <- U4_33; symmetry; apply Z_to_bv_bv_unsigned).
assert (A1028x : ew E4 1028 = w64 F) by (unfold w64; rewrite <- U4_1028; symmetry; apply Z_to_bv_bv_unsigned).
assert (A1040x : ew E4 1040 = w64 sF) by (unfold w64; rewrite <- U4_1040; symmetry; apply Z_to_bv_bv_unsigned).
assert (U4_1072 : bv_unsigned (ew E4 1072) = sM) by (rewrite A1072; apply unsigned_lit_small; lia).
pose proof (st_ok_pi_add_fact E4 _ _ 1072 (mkAF SB (SB + 2 ^ 44) 0) HS3
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U4_1072; rewrite Z.pow_0_r, Z.mod_1_r; unfold SB; repeat split; lia)) as HS4. clear HS3.
(* atom 10 = msg: in a live frame (afobj), so 4096 <= msg <= 2 ^ 47, and 8-aligned; these facts decide B's UBSan
   branches 0x8cf7c (beqz s8) and 0x8cf84 (bnez (s8 & 7)) to the trap 0x8d938 *)
assert (U4_10 : bv_unsigned (ew E4 10) = msg).
{ rewrite EL4, EL2, (EE 10%nat 10%bv eq_refl) by lia.
transitivity (bv_unsigned (w64 msg)); [f_equal; exact H10|]. unfold w64. apply unsigned_lit_small. lia. }
pose proof (st_ok_pi_add_fact E4 _ _ 10 (mkAF 4096 (2 ^ 47) 3) HS4
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U4_10; try change (2 ^ 3) with 8; repeat split; lia)) as HS5.
clear HS4. rename HS5 into HS4.
assert (AL2 : sv_denot E4 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0)) = sv_denot E4 (SOff 1072 0)).
{ rewrite (denot_shx E4 10 32 8 msg SB); [| rewrite EL4, EL2, (EE 10%nat 10%bv eq_refl) by lia; exact H10
| rewrite EL4, EL2 by lia; exact E32 | lia | lia | lia | unfold SB; lia].
cbn [sv_denot]. rewrite A1072, unsigned_lit_small by lia. rewrite !Z.add_0_r. reflexivity. }
pose proof (st_ok_pi_add_alias E4 _ _ _ _ HS4 AL2) as HS3. clear HS4. vr01_nss HS3.
pose proof (st_ok_pi_add_region E4 _ _ vr01_msh_r HS3 eq_refl
ltac:(unfold region_ok, vr01_msh_r; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U4_1072; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS E4 _ sM 0 1 (SLit 0) 0); [reflexivity | zside | zside |];
rewrite Z.add_0_r; apply vr01_val_mem1_of_aview; [exact VM | lia])
ltac:(unfold vr01_msh_r; cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U4_1072, U4_33, U4_1028, U4_1040, U4_2; lia)) as HS4.
clear HS3. vr01_nss HS4.
pose proof (st_ok_pi_add_region E4 _ _ vr01_sh_b HS4 eq_refl
ltac:(unfold region_ok, vr01_sh_b; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U4_1040; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFSpres3 o ltac:(lia))))
ltac:(unfold vr01_sh_b; cbn [ss_mem all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U4_1072, U4_33, U4_1028, U4_1040, U4_2; lia)) as HS.
clear HS4. vr01_nss HS.
(* the walk's own bounds, without the case split that slows every later `lia` *)
assert (Hs1b : sp0 - 208 <= s1 <= sp0 - 192) by lia.
clear Hs1 HdFM.
(* 0x8cf40 .. 0x8cf98: f2 x8, f8 (B: `li a0,-8` at 0x8cf68), f3 x3, the UBSan checks on msg (0x8cf7c, 0x8cf84,
   s5 = msg & 7 = 0), a0 = msg + 8, its shadow byte 0: the bnez at 0x8cf98 falls through to 0x8cf9c *)
paj_run_to_sh RUNTOP HS HJ3 0x6a6c.
{
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?sp ?fp ?b0 ?bc ?fr ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk sp fp b0 bc fr lyx own) end.
eapply awr_ok_cons_gen with (n := 1040%nat) (b := sF); [reflexivity | exact U4_1040 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 4, pos. split; [left; reflexivity|].
right. unfold in_zr. cbn [fst snd]. rewrite HFB. fold F sF. change (1024 / 8) with 128. clear - Ha. lia. }
apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_stack_off with (n := 33%nat) (d := s1 - sp0); [reflexivity | rewrite U4_33; lia | cbn; lia | cbn; lia |].
eapply awr_ok_cons_gen with (n := 1028%nat) (b := F); [reflexivity | exact U4_1028 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 4, pos. split; [left; reflexivity|].
left. unfold in_zr. cbn [fst snd]. rewrite HFB. fold F. clear - Ha. lia. }
eapply awr_ok_cons_gen with (n := 1040%nat) (b := sF); [reflexivity | exact U4_1040 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 4, pos. split; [left; reflexivity|].
right. unfold in_zr. cbn [fst snd]. rewrite HFB. fold F sF. change (1024 / 8) with 128. clear - Ha. lia. }
eapply awr_ok_cons_stack; [reflexivity | exact U4_2 | cbn; lia | cbn; lia |].
eapply awr_ok_cons_stack; [reflexivity | exact U4_2 | cbn; lia | cbn; lia |].
apply awr_ok_nil. }
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ (ms_mem ?msx)) => rename msx into msF end.
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 208 <= a < sp0) -> ~ (F <= a < F + 24) -> ~ (sF <= a < sF + 4) ->
~ (sF + 68 <= a < sF + 80) -> rdW W (ms_mem msF) a = rdW W mem3 a).
{ intros a Ha H1 H2 H3 H5.
apply (kept_of_frame _ _ _ _ _ (fun x => (sp0 - 208 <= x < sp0) \/ (F <= x < F + 24) \/ (sF <= x < sF + 4) \/ (sF + 68 <= x < sF + 80)) HFr);
[| exact Ha | intros [Hx | [Hx | [Hx | Hx]]]; [exact (H1 Hx) | exact (H2 Hx) | exact (H3 Hx) | exact (H5 Hx)]].
intros b wlo whi x Hin Hr. vm_compute in Hin.
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U4_2, ?U4_33, ?U4_1028, ?U4_1040, ?U4_1072 in Hr; lia|]). destruct Hin. }
clear HF HFr HG.
(* ---------------------------------------------------------------------------------------------------------------
   the boundary state vr_b1 at 0x8d5c4 *)
(* the bytes the walk keeps from the entry (the program's statics and the live blocks) lie below the allocation
   ceiling, apart from the frame and from its shadow, so every run and every call kept them *)
assert (KAP : forall a, vr01_keep B ly S2 a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 1024) /\ ~ (sF <= a < sF + 128))
by (intros a Hka; exact (vr01_keep_apart B PROGU ly S2 W mem2 md2 pos a HAR2 Hfin2 Hka)).
assert (Hc208 : alloc_ceiling + 208 <= sp0) by lia.
assert (KPF : forall a, vr01_keep B ly S a -> rdW W (ms_mem msF) a = rdW W mem a).
{ intros a Hka.
assert (Hka2 : vr01_keep B ly S2 a) by (unfold vr01_keep in *; rewrite Eab; exact Hka).
destruct (KAP a Hka2) as (Hb & HnF & HnS).
rewrite (KR3 a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
rewrite (Hkeep3 a ltac:(lia) ltac:(lia)).
rewrite (KR2 a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
destruct HK as (K1 & K2 & K3 & _).
destruct Hka as [Hpg | (p & m & Hpm & Hr)].
- destruct (PROGU a Hpg) as (Hi & Ho & He). rewrite (K3 a Hi Ho He). apply KR1; lia.
- replace a with (p + (a - p)) by lia. rewrite (K2 p m (a - p) Hpm ltac:(lia) ltac:(intros [])).
apply KR1; lia. }
(* the frame's flag word, written by __asan_stack_malloc_4 and untouched since *)
assert (HFLf : rdword (rdW W (ms_mem msF)) (F + 1016) = Some (flag_addr ly 4 pos)).
{ replace (F + 1016) with (F + 1024 - 8) by lia.
rewrite (rdword_ext (rdW W mem2) (rdW W (ms_mem msF)) (F + 1024 - 8)); [exact Hflag|].
intros k Hk.
rewrite (KR3 (F + 1024 - 8 + k) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
rewrite (Hkeep3 (F + 1024 - 8 + k) ltac:(lia) ltac:(lia)).
exact (KR2 (F + 1024 - 8 + k) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
(* the 128 shadow bytes of the frame *)
vr01_reg HS 0%nat HR0. vr01_reg HS 2%nat HR2. vr01_reg HS 4%nat HR4. vr01_reg HS 6%nat HR6.
assert (SHZ : forall z, 0 <= z < 128 -> rdW W (ms_mem msF) (sF + z) = Some (vr01_shv (Z.to_nat z))).
{ intros z Hz128.
destruct (Z_lt_le_dec z 4) as [Hz4|Hz4].
- assert (Hc : z = 0 \/ z = 1 \/ z = 2 \/ z = 3) by lia.
destruct Hc as [-> | [-> | [-> | ->]]];
(eapply vr01_region_byte; [exact HR4 | exact U4_1040 | cbn [In]; repeat (first [left; reflexivity | right]) | vm_compute; reflexivity]).
- destruct (Z_lt_le_dec z 68) as [Hz68|Hz68].
+ rewrite (KR3 (sF + z) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
replace (sF + z) with (sF + 4 + (z - 4)) by lia.
rewrite (Hfill (z - 4) ltac:(lia)). f_equal. symmetry. apply vr01_shv_mid. lia.
+ destruct (Z_lt_le_dec z 80) as [Hz80|Hz80].
* assert (Hc : z = 68 \/ z = 69 \/ z = 70 \/ z = 71 \/ z = 72 \/ z = 73 \/ z = 74 \/ z = 75 \/ z = 76 \/ z = 77 \/ z = 78 \/ z = 79) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
(eapply vr01_region_byte; [exact HR0 | exact U4_1040 | cbn [In]; repeat (first [left; reflexivity | right]) | vm_compute; reflexivity]).
* rewrite (KR3 (sF + z) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
rewrite (Hkeep3 (sF + z) ltac:(lia) ltac:(lia)).
rewrite (KR2 (sF + z) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
rewrite (vr01_shv_hi (Z.to_nat z) ltac:(lia)).
unfold zero_shadow in Hz. change (shadow_of_addr SHADOW_OFF F) with sF in Hz. change (1024 / 8) with 128 in Hz.
exact (Hz z ltac:(lia)). }
assert (SHF : forall i, (i < 128)%nat -> rdW W (ms_mem msF) (sF + Z.of_nat i) = Some (vr01_shv i)).
{ intros i Hi. rewrite <- (Nat2Z.id i) at 2. apply SHZ. lia. }
(* the caller's registers the prologue saved, and the spill slot *)
assert (AEE : forall nn (r : bv 5), (nn < 32)%nat -> Z.of_nat nn = bv_unsigned r -> ew E4 nn = getr regs r)
by (intros nn r Hnn Hr; rewrite (EL4 nn ltac:(lia)), (EL2 nn ltac:(lia)); exact (EE nn r Hr)).
assert (HSAVf : forall j r, nth_error vr_saved_regs j = Some r ->
aval_mem (rdW W (ms_mem msF)) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj.
destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]; cbn in Hj;
[injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-8) 1%nat (1%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-16) 8%nat (8%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-24) 9%nat (9%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-32) 18%nat (18%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-40) 19%nat (19%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-48) 20%nat (20%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-56) 21%nat (21%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-64) 22%nat (22%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-72) 23%nat (23%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-80) 24%nat (24%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-88) 25%nat (25%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-96) 26%nat (26%bv : bv 5)
| injection Hj as <-; vr01_sv HR6 U4_2 AEE sp0 (-104) 27%nat (27%bv : bv 5)
| destruct j; cbn in Hj; discriminate Hj]. }
assert (HSPLf : Forall (fun ov => aval_mem (rdW W (ms_mem msF)) (s1 + fst ov) 8 (snd ov)) (vr_sl1 F)).
{ unfold vr_sl1. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
pose proof (vr01_region_word SEGS E4 (w_H W) (ms_mem msF) 33%nat _ _ _ _ _ s1 72 (SOff 1028 0) HR2 U4_33
ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as Hw.
cbn [sv_denot] in Hw. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U4_1028 in Hw. exact Hw. }
(* the registers at the boundary (B's vr_rl1: a0 = msg + 8, s3 = the shadow base, s4 = s6 = F, s5 = msg & 7 = 0,
   s8 = msg, s9 = shadow_addr F, s11 = shadow_addr F + 4) *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
assert (HRVf : vr_rv (ms_regs msF) [(2, s1); (3, as_gp B); (4, as_tp B); (8, sp0); (9, s1);
(10, msg + 8); (19, SHADOW_OFF); (20, F); (21, 0); (22, F); (24, msg); (25, sF); (27, sF + 4)]).
{ unfold vr_rv. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
- etransitivity; [exact Q2|]. exact A33x.
- etransitivity; [exact Q3|]. rewrite (AEE 3%nat 3%bv ltac:(lia) eq_refl). exact Hgp.
- etransitivity; [exact Q4|]. rewrite (AEE 4%nat 4%bv ltac:(lia) eq_refl). exact Htp.
- etransitivity; [exact Q8|]. exact A2x.
- etransitivity; [exact Q9|]. exact A33x.
- etransitivity; [exact Q10|]. rewrite U4_10. reflexivity.
- etransitivity; [exact Q19|]. rewrite (EL4 32%nat ltac:(lia)), (EL2 32%nat ltac:(lia)). exact E32.
- etransitivity; [exact Q20|]. exact A1028x.
- etransitivity; [exact Q21|]. reflexivity.
- etransitivity; [exact Q22|]. exact A1028x.
- etransitivity; [exact Q24|]. rewrite (AEE 10%nat 10%bv ltac:(lia) eq_refl). exact H10.
- etransitivity; [exact Q25|]. exact A1040x.
- etransitivity; [exact Q27|]. rewrite U4_1040. reflexivity. }
pmkst HS.
apply SRr_ret. do 9 eexists. split; [reflexivity|].
exact (vr01_final B MT MTL MTFL ROA RRO RPG RECC _ pos F S2 fS (ms_regs msF) (ms_mem msF) _
HE0 HJ3 ES2 eq_refl HFLf SHF HRVf HSAVf HSPLf KPF).
Qed.

End e.
End f.
End d.
