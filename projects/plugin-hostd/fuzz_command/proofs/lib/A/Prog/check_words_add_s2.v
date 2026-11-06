(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first part of sup_policy_set's ASan walk (plugin-hostd/fuzz_command, 0x8b9b0), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and AChc.v (cgif_close: the seed of a walk segment, the run, the step through a program call) and of an earlier version of lib/A/Prog/sup_reply_code.v: the entry, the inlined record() with both arms (the call of rec_calls_free on record.spill when the table holds 16 calls), the two checked stores into the slot, and the walk to the call of xstrdup on the first argument. *)
(* Modified by Theorem Labs, 2026-10: re-fitted to statement passes 4 and 5: the bundled pre
   carries the rounding-mode-0 premise where astack_pres was, the post is apost_baseF, the callees' contracts are taken
   at every FP state; the frame chains at the two calls are achain_low (s0 = the slot, below alloc_ceiling). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_policy_set_s1.v, with its module paths and module names changed; 979 of its 1060 lines of code are new or changed and 1433 lines of the source are left out. *)
(* check_words_add's walk on the ASan build of plugin-hostd/fuzz_command, part 2: the seeds, the helpers,
   the tail 0x88bd0 .. ret (cwa_tail) and the literal-placement middle 0x88b60 .. 0x88bd0 (cwa_mid_dash).

   Entry BASE + AF_check_words_add = 0x88abc, 121 instructions, 32 blocks, no loop, 7 inline checks,
   4 calls of the strcmp wrapper and 1 of the strncmp wrapper, one abort pair on the edge the premises
   exclude. The walk is cgif_file_fuzzer's: the verified symbolic executor over the position-abstract
   listing (lib/A/Prog/CmdPaLib.v paj_run / paj_run_to / psrr_branch_tok over PaShadow's sym_runN_pi_tok),
   the inline checks removed by tok_load / tok_branch (lib/Reusable/YCbn.v) from shent entries, and the
   wrapper calls going out through cgif's call rule cl_callS (lib/A/Prog/PaCall.v:380).

   The facts about the image that the statement does not give are the record CwaFacts of
   lib/A/Prog/check_words_add_s1.v; this file adds nothing about B. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require check_words_add_c.
Module PCwa := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaJournal CmdSyms CmdList CmdAddr CmdPa CmdPaLib CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaDenot PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_add_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac cwa_unf := repeat first [ progress unfold CHECK_WORDS_ADD_STK in * | progress unfold ESTACK in *
| progress unfold spZ in * | progress unfold A_G_REC in * | progress unfold OFF_CALLS in *
| progress unfold REC_SIZE in * | progress unfold CALL_SIZE in * | progress unfold SHADOW_OFF in * ].
Ltac cwa_arith := try unfold w64; rewrite ?unsigned_lit_small by (cwa_unf; lia); cwa_unf; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the shadow base, as the walk's symbolic memory names it: atom 32, the word the cell 0xb10b8 holds *)
Definition CWA_BX : sv := SOff 32 0.
Definition CWA_SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* atoms 32..37: the shadow base, the two word pointers, the two argument pointers, the recorded arity *)
Definition cwa_extra (p3 p4 q2 q3 nargs : Z) : list word :=
map (Z_to_bv 64) [SHADOW_OFF; p3; p4; q2; q3; nargs].
Definition cwa_E (regs : bvmap 5 word) (p3 p4 q2 q3 nargs : Z) : env :=
Eimg (Ereg regs (cwa_extra p3 p4 q2 q3 nargs)).

Definition cwa_regions0 : smem := [stack_region 64; got_regionP; bcell_regionP 32].
Definition cwa_facts0 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (12%nat, mkAF 0 64 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition cwa_ss0 : sstate := mkSS AF_check_words_add sr_atoms cwa_regions0 None cwa_facts0.

(* the state at 0x88bd0 (offset 0x26ec), where the five paths through the placement and client choice join:
   the frame holds the entry ra and s0..s5, s0 = cp, s1 = the placement pointer, s2 = the client pointer,
   s5 = the shadow base. Atoms: 32 the shadow base, 33 and 34 the two recorded argument pointers,
   35..41 the seven saved registers. *)
Definition cwa_frameR : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0
[YP09.mkChunk 56 (CVal 8 (SOff 35 0)); YP09.mkChunk 48 (CVal 8 (SOff 36 0));
YP09.mkChunk 40 (CVal 8 (SOff 37 0)); YP09.mkChunk 32 (CVal 8 (SOff 38 0));
YP09.mkChunk 24 (CVal 8 (SOff 39 0)); YP09.mkChunk 16 (CVal 8 (SOff 40 0));
YP09.mkChunk 8 (CVal 8 (SOff 41 0))].
Definition cwa_grecR : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 56 0 0
[YP09.mkChunk 4 (CVal 4 (SLit 4)); YP09.mkChunk 24 (CVal 8 (SOff 33 0)); YP09.mkChunk 32 (CVal 8 (SOff 34 0))].
Definition cwa_regionsT : smem := [cwa_frameR; cwa_grecR; got_regionP; bcell_regionP 21].
(* in the tail the shadow base is already in s5, so the walk's Bx is that register's atom *)
Definition CWA_BXT : sv := SOff 21 0.
Definition cwa_factsT : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46 - 64) (2 ^ 47) 4);
(8%nat, mkAF (A_G_REC + OFF_CALLS) (A_G_REC + REC_SIZE - CALL_SIZE) 0);
(21%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition cwa_SHT : list shent := [mkSHE 8 4 40].
Definition cwa_ssT : sstate := mkSS 0x26ec sr_atoms cwa_regionsT None cwa_factsT.
Definition cwa_extraT (q2 q3 : Z) (regs : bvmap 5 word) : list word :=
[Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 q2; Z_to_bv 64 q3;
getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21].
Definition cwa_ET (regsc : bvmap 5 word) (q2 q3 : Z) (regs : bvmap 5 word) : env :=
Eimg (Ereg regsc (cwa_extraT q2 q3 regs)).

(* the frame this call keeps: the seven words it saved at entry *)
Definition cwa_frame (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
val_mem SEGS m (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\
val_mem SEGS m (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem SEGS m (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\
val_mem SEGS m (sp0 - 32) 8 (bv_unsigned (getr regs 18)) /\
val_mem SEGS m (sp0 - 40) 8 (bv_unsigned (getr regs 19)) /\
val_mem SEGS m (sp0 - 48) 8 (bv_unsigned (getr regs 20)) /\
val_mem SEGS m (sp0 - 56) 8 (bv_unsigned (getr regs 21)).

(* the state at 0x88b60 (offset 0x267c) when the placement is the image literal "-" at 0x21ac0: the two
   1-byte loads of the literal, then the client choice. Atom 9 is s1 (the placement pointer), 18 is s2 (the
   word array), 19 is s3 (read), 21 is s5 (the shadow base), 33 and 34 the recorded arguments, 35..41 the
   saved registers, 43 and 44 the two word slots. *)
Definition cwa_dashR : YP09.region :=
YP09.mkRegion (Some 9%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 45)); YP09.mkChunk 1 (CVal 1 (SLit 0))].
Definition cwa_wordR (off : Z) (n : nat) : YP09.region :=
YP09.mkRegion (Some 18%nat) off (off + 8) 0 0 [YP09.mkChunk off (CVal 8 (SOff n 0))].
Definition cwa_regionsD : smem := [cwa_dashR; got_regionP; bcell_regionP 21].
Definition cwa_factsD : facts :=
mkFacts [(9%nat, mkAF 0x21ac0 0x21ac0 0);
(19%nat, mkAF 0 64 0); (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition cwa_SHD : list shent := [mkSHE 9 0 2].
Definition cwa_SHDW : list shent := [mkSHE 9 0 2; mkSHE 18 24 32].
Definition cwa_ssD : sstate := mkSS 0x267c sr_atoms cwa_regionsD None cwa_factsD.
Definition cwa_extraM (q2 q3 p3 p4 : Z) (regs : bvmap 5 word) : list word :=
[Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 q2; Z_to_bv 64 q3;
getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21;
Z_to_bv 64 0; Z_to_bv 64 p3; Z_to_bv 64 p4].
Definition cwa_EM (regsc : bvmap 5 word) (q2 q3 p3 p4 : Z) (regs : bvmap 5 word) : env :=
Eimg (Ereg regsc (cwa_extraM q2 q3 p3 p4 regs)).

(* the two readers the walk moves between *)
Lemma cwa_val_mem : forall (W : world SEGS) mem a n v,
aval_mem (rdW W mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. specialize (H k Hk). unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate].
cbn [option_map] in H. injection H as H.
assert (HB : Z_to_bv 8 (le_byte v n k) = Z_to_bv 8 (bv_unsigned b)) by (rewrite H; reflexivity).
f_equal. symmetry. etransitivity; [exact HB | apply Z_to_bv_bv_unsigned].
Qed.

Lemma cwa_aval_of_bytes : forall (rd : reader) a l i c,
abytes_atR rd a l -> nth_error l i = Some c -> aval_mem rd (a + Z.of_nat i) 1 (bv_unsigned c).
Proof.
intros rd a l i c Hb Hi k Hk. destruct k as [|k]; [|lia].
rewrite Z.add_0_r.
assert (HB : le_byte (bv_unsigned c) 1 0 = bv_unsigned c).
{ pose proof (bv_unsigned_in_range 8 c) as HR. change (bv_modulus 8) with 256 in HR.
  unfold le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity.
  replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
rewrite HB.
assert (HI : (i < length l)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
specialize (Hb i HI). rewrite Hb. f_equal. f_equal. apply (nth_error_nth l i (Z_to_bv 8 0) Hi).
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis HFACTS : CwaFacts B.

#[local] Notation LAWS := (cwa_laws B).
#[local] Notation CWA_CELL := (cf_cell B HFACTS).
#[local] Notation CWA_GOT := (cf_got B HFACTS).
#[local] Notation CWA_GREC := (cf_grec B HFACTS).

Lemma cwa_regs_ok : forall regs p3 p4 q2 q3 nargs,
regs_ok (cwa_E regs p3 p4 q2 q3 nargs) sr_atoms regs.
Proof.
intros. unfold cwa_E. apply (regs_ok_agree 32 (Ereg regs (cwa_extra p3 p4 q2 q3 nargs))).
- split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.

Lemma cwa_entry : forall ly S W (regs : bvmap 5 word) mem md (cp wp r nargs p3 p4 q2 q3 : Z),
afn_pre_na SEGS B CHECK_WORDS_ADD_STK ly S W regs mem md ->
cmd_val_objs -> getr regs 12 = w64 r -> 0 <= r <= 64 ->
st_ok_pi SEGS VAL (cwa_E regs p3 p4 q2 q3 nargs) cwa_ss0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_check_words_add)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CWA_BX [] (cwa_E regs p3 p4 q2 q3 nargs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md cp wp r nargs p3 p4 q2 q3 HPRE VOBJS H12 Hr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CHECK_WORDS_ADD_STK = 8256) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite CWA_GOT, CWA_CELL in Kgot. rewrite CWA_CELL in Kcell.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 12 ltac:(lia)) as HcellR.
assert (VO0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VO12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
pose proof pa_B_ok as HBASE.
rewrite restrict_mkst_fx.
set (E := cwa_E regs p3 p4 q2 q3 nargs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cwa_extra p3 p4 q2 q3 nargs)) n)
by (intros n Hn; subst E; unfold cwa_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E12 : ew E 12 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold cwa_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold cwa_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split; [|constructor].
unfold cwa_ss0. apply pa_entry_st_ok_full.
- apply cwa_regs_ok.
- vm_compute. reflexivity.
- unfold cwa_regions0, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CWA_BX SHADOW_OFF);
    [cbn [sv_denot CWA_BX]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold cwa_regions0, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR VO0 VO12. clear. intros. repeat split; lia.
- split; [|split; exact I].
  cbn [cwa_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E12, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Hr. clear.
  unfold SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
Qed.

Lemma cwa_regs_okT : forall regsc q2 q3 regs, regs_ok (cwa_ET regsc q2 q3 regs) sr_atoms regsc.
Proof.
intros. unfold cwa_ET. apply (regs_ok_agree 32 (Ereg regsc (cwa_extraT q2 q3 regs))).
- split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.

(* The state at the join 0x88bd0: the frame, the recorded call's three fields, the GOT word and the shadow
   cell, and the one shent the three checks of the tail need (g_rec's body is addressable). *)
Lemma cwa_tail_entry :
forall ly S W (regs : bvmap 5 word) mem md lyc Sc (Wc : world SEGS) memc mdc (regsc : bvmap 5 word) (cp q2 q3 : Z),
ajournal SEGS B CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] lyc Sc Wc memc mdc 0 ->
cmd_val_objs ->
getr regsc 2 = w64 (spZ regs - 64) -> getr regsc 8 = w64 cp -> getr regsc 21 = w64 SHADOW_OFF ->
cwa_frame (mrestrict (w_H Wc) memc) (spZ regs) regs ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
aval_mem (rdW Wc memc) (cp + CALL_OFF_NARGS) 4 4 ->
aval_mem (rdW Wc memc) (cp + CALL_OFF_ARGS + 16) 8 q2 ->
aval_mem (rdW Wc memc) (cp + CALL_OFF_ARGS + 24) 8 q3 ->
0 <= q2 < 2 ^ 64 -> 0 <= q3 < 2 ^ 64 ->
st_ok_pi SEGS VAL (cwa_ET regsc q2 q3 regs) cwa_ssT
(restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + 0x26ec)) memc (seg_rom SEGS)))
/\ sh_ok SEGS CWA_BXT cwa_SHT (cwa_ET regsc q2 q3 regs) (mrestrict (w_H Wc) memc).
Proof.
intros ly S W regs mem md lyc Sc Wc memc mdc regsc cp q2 q3 HJ VOBJS R2 R8 R21 HFR Hcp1 Hcp2 HN HQ2 HQ3 Rq2 Rq3.
unfold CALL_OFF_NARGS, CALL_OFF_ARGS in HN, HQ2, HQ3.
replace (cp + 8 + 16) with (cp + 24) in HQ2 by lia.
replace (cp + 8 + 24) with (cp + 32) in HQ3 by lia.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CHECK_WORDS_ADD_STK = 8256) by reflexivity.
assert (VO0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VO12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
destruct (al_const _ _ LAWS lyc Sc Wc memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite CWA_GOT, CWA_CELL in Kgot. rewrite CWA_CELL in Kcell.
pose proof pa_B_ok as HBASE.
destruct HFR as (F1 & F8 & F9 & F18 & F19 & F20 & F21).
rewrite restrict_mkst_fx.
set (E := cwa_ET regsc q2 q3 regs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsc (cwa_extraT q2 q3 regs)) n)
by (intros n Hn; subst E; unfold cwa_ET; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regsc 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl)).
assert (E8 : ew E 8 = getr regsc 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 8 8%bv eq_refl)).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 21 21%bv eq_refl); exact R21).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (cwa_extraT q2 q3 regs) (Z_to_bv 64 0))
by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
cbn [Nat.add nth cwa_extraT] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41.
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold cwa_ET; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold cwa_ET; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
by (rewrite E2, R2; apply unsigned_lit_small; unfold CHECK_WORDS_ADD_STK, ESTACK in *; lia).
assert (Ucp : bv_unsigned (ew E 8) = cp)
by (rewrite E8, R8; apply unsigned_lit_small; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (BS : base_val E (Some 2%nat) = spZ regs - 64) by (cbn [base_val]; exact Usp).
assert (BC : base_val E (Some 8%nat) = cp) by (cbn [base_val]; exact Ucp).
split.
- unfold cwa_ssT. apply pa_entry_st_ok_full.
  + apply cwa_regs_okT.
  + vm_compute. reflexivity.
  + unfold cwa_regionsT, cwa_frameR, cwa_grecR, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite BS. split; [unfold CHECK_WORDS_ADD_STK, ESTACK in *; lia|]. split; [lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 64) 56 8 (SOff 35 0) (bv_unsigned (getr regs 1)));
         [ cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
         | cbn; lia
         | replace (spZ regs - 64 + 56) with (spZ regs - 8) by lia; exact F1 ].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 64) 48 8 (SOff 36 0) (bv_unsigned (getr regs 8)));
         [ cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 8)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
         | cbn; lia
         | replace (spZ regs - 64 + 48) with (spZ regs - 16) by lia; exact F8 ].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 64) 40 8 (SOff 37 0) (bv_unsigned (getr regs 9)));
         [ cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 9)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
         | cbn; lia
         | replace (spZ regs - 64 + 40) with (spZ regs - 24) by lia; exact F9 ].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 64) 32 8 (SOff 38 0) (bv_unsigned (getr regs 18)));
         [ cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 18)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
         | cbn; lia
         | replace (spZ regs - 64 + 32) with (spZ regs - 32) by lia; exact F18 ].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 64) 24 8 (SOff 39 0) (bv_unsigned (getr regs 19)));
         [ cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 19)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
         | cbn; lia
         | replace (spZ regs - 64 + 24) with (spZ regs - 40) by lia; exact F19 ].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 64) 16 8 (SOff 40 0) (bv_unsigned (getr regs 20)));
         [ cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 20)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
         | cbn; lia
         | replace (spZ regs - 64 + 16) with (spZ regs - 48) by lia; exact F20 ].
      -- apply (chunk_ok_val SEGS E _ (spZ regs - 64) 8 8 (SOff 41 0) (bv_unsigned (getr regs 21)));
         [ cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (bv_unsigned_in_range 64 (getr regs 21)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
         | cbn; lia
         | replace (spZ regs - 64 + 8) with (spZ regs - 56) by lia; exact F21 ].
    * rewrite BC. split; [unfold A_G_REC, OFF_CALLS in *; lia|].
      split; [unfold A_G_REC, REC_SIZE, CALL_SIZE in *; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val SEGS E _ cp 4 4 (SLit 4) 4); [reflexivity | zside | zside |].
         exact (cwa_val_mem Wc memc (cp + 4) 4%nat 4 HN).
      -- apply (chunk_ok_val SEGS E _ cp 24 8 (SOff 33 0) q2);
         [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (cwa_val_mem Wc memc (cp + 24) 8%nat q2 HQ2).
      -- apply (chunk_ok_val SEGS E _ cp 32 8 (SOff 34 0) q3);
         [ cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (cwa_val_mem Wc memc (cp + 32) 8%nat q3 HQ3).
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CWA_BXT SHADOW_OFF);
      [cbn [sv_denot CWA_BXT]; rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold cwa_regionsT, cwa_frameR, cwa_grecR, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    rewrite BS, BC, VO0, VO12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hcp1 Hcp2. clear.
    unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, CHECK_WORDS_ADD_STK, ESTACK. intros.
    repeat split; lia.
  + split; [|split; exact I].
    cbn [cwa_factsT f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Ucp, E21, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hm : (spZ regs - 64) mod 16 = 0) by (replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia;
      rewrite Z_mod_plus_full; exact Hal16).
    revert Hslo Hshi H47 Hceil Hm C1 C3 WS Hstk0 Hcp1 Hcp2. clear.
    unfold SHADOW_OFF, A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, CHECK_WORDS_ADD_STK, ESTACK. intros.
    repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
- unfold sh_ok, cwa_SHT. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H Wc) memc E CWA_BXT 8 A_G_REC REC_SIZE cp 4 40).
  + exact (CWA_GREC lyc Sc Wc memc mdc HAR).
  + unfold U, CWA_BXT. cbn [sv_denot]. rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Ucp.
  + unfold A_G_REC, OFF_CALLS in *. lia.
  + unfold A_G_REC, REC_SIZE, CALL_SIZE in *. lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    revert Hx Hcp1 Hcp2. clear. unfold SHADOW_OFF, A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE. lia.
Qed.


(* forget every region of a walk state: the memory clause of st_ok for [] is trivially true *)
Lemma cwa_set_mem_nil : forall E ss ms,
st_ok_pi SEGS VAL E ss ms ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) [] (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms HS. unfold st_ok_pi, abs_ss in *. unfold YP0l.st_ok, YP0l.setpc in *.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_fregs] in *.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [|exact H9].
split; [reflexivity|]. split; [constructor | exact I].
Qed.

(* a signed branch between two values the facts pin below 2^63 *)
Lemma cwa_branch_lt : forall E a b (x y : Z),
sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken].
assert (HU : forall z : Z, 0 <= z < 2 ^ 63 -> bv_unsigned (Z_to_bv 64 z) = z).
{ intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. lia. }
unfold bv_lts. rewrite !bv_signed_small by (rewrite HU by lia; lia).
rewrite !HU by lia. reflexivity.
Qed.

(* a read range does not depend on which register file names the stack pointer, only on its value *)
Lemma cwa_aread_sp : forall stk (W : world SEGS) (ra rb : bvmap 5 word) mem x n,
spZ rb = spZ ra -> aread_ok SEGS stk W ra mem x n -> aread_ok SEGS stk W rb mem x n.
Proof.
intros stk W ra rb mem x n Hsp (H0 & H1 & H2 & H3 & H4 & H5 & H6).
split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
{ intros a Ha. destruct (H3 a Ha) as [Hv Hs]. split; [exact Hv|]. unfold ascratch_stk in *. rewrite Hsp. exact Hs. }
split; [exact H4|]. split; [exact H5 | exact H6].
Qed.

(* the regions of a walk state survive a runtime call when they lie outside the window it scratches *)
Lemma cwa_region_kept : forall E (W : world SEGS) memc mem2 (r : YP09.region) lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W mem2 a = rdW W memc a) ->
0 <= base_val E (YP09.r_base r) + YP09.r_lo r -> base_val E (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 ->
(base_val E (YP09.r_base r) + YP09.r_hi r <= lo \/ hi <= base_val E (YP09.r_base r) + YP09.r_lo r) ->
YP09.r_whi r <= YP09.r_wlo r ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) r.
Proof.
intros E W memc mem2 r lo hi HK H0 H1 Hap Hro. split; intros a Ha; [|lia].
apply (mbyte_of_aview SEGS). apply HK; lia.
Qed.

(* the literal "-" at 0x21ac0, in the form the wrapper contracts and the walk take it *)
Lemma cwa_dash_str : forall ly S W (regs : bvmap 5 word) mem md,
AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) -> alloc_ceiling <= spZ regs - 2 * ESTACK ->
astr_at SEGS W mem 0x21ac0 S_DASH
/\ aread_ok SEGS (2 * ESTACK) W regs mem 0x21ac0 (astr_len S_DASH + 1)
/\ atail_vis SEGS W mem (0x21ac0 + astr_len S_DASH)
/\ aval_mem (rdW W mem) 0x21ac0 1 45 /\ aval_mem (rdW W mem) 0x21ac1 1 0.
Proof.
intros ly S W regs mem md HAR HRO Hsp.
destruct HRO as [HROB HROT].
assert (HB : abytes_atR (rdW W mem) 0x21ac0 RO_lit_21ac0)
by (unfold cmd_ro_bytes in HROB; repeat (destruct HROB as [? HROB]); assumption).
assert (HL : Z.of_nat (length RO_lit_21ac0) = 2) by (vm_compute; reflexivity).
destruct (cwa_lit_facts B HFACTS ly S W regs mem md 0x21ac0 2 RO_lit_21ac0 HAR
ltac:(cbv [CWA_LITS In]; tauto) HB HL HROT ltac:(cbv [cmd_ro_ends In]; tauto) Hsp) as [HRD HTL].
assert (HS : astr_at SEGS W mem 0x21ac0 S_DASH).
{ split.
  - intros i Hi. vm_compute in Hi.
    assert (HEq : S_DASH ++ [Z_to_bv 8 0] = RO_lit_21ac0) by (vm_compute; reflexivity).
    rewrite HEq. apply HB. cbv [RO_lit_21ac0 map length]. lia.
  - cbv [S_DASH str map In]. intros [HX | []]. apply (f_equal bv_unsigned) in HX.
    rewrite !Z_to_bv_unsigned in HX. cbv in HX. discriminate HX. }
split; [exact HS|]. split; [|split].
- replace (astr_len S_DASH + 1) with 2 by (cbv [astr_len S_DASH str map length]; lia). exact HRD.
- replace (0x21ac0 + astr_len S_DASH) with (0x21ac0 + 2 - 1) by (cbv [astr_len S_DASH str map length]; lia). exact HTL.
- split.
  + replace 0x21ac0 with (0x21ac0 + Z.of_nat 0) at 2 by lia.
    exact (cwa_aval_of_bytes _ _ RO_lit_21ac0 0 (Z_to_bv 8 45) HB eq_refl).
  + replace 0x21ac1 with (0x21ac0 + Z.of_nat 1) by lia.
    exact (cwa_aval_of_bytes _ _ RO_lit_21ac0 1 (Z_to_bv 8 0) HB eq_refl).
Qed.

Let RUN := paj_run B (cwa_laws B).
Let RUNTO := paj_run_to B (cwa_laws B).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).







(* 0x88bd0 .. ret: the three checks of the recorded call, the two strcmp calls whose answers the premises
   make 0, the abort edge 0x88c5c that those answers exclude, and the epilogue. *)
Lemma cwa_tail : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md
(cp q2 q3 pp cl : Z) (x2 x3 : list byte) memc mdc (regsc : bvmap 5 word),
afn_pre_na SEGS B CHECK_WORDS_ADD_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
ajournal SEGS B CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S W memc mdc 0 ->
cmd_val_objs ->
astrcmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strcmp) ->
getr regsc 2 = w64 (spZ regs - 64) ->
getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
(forall r, 22 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr regsc 8 = w64 cp -> getr regsc 9 = w64 pp -> getr regsc 18 = w64 cl ->
getr regsc 21 = w64 SHADOW_OFF ->
cwa_frame (mrestrict (w_H W) memc) (spZ regs) regs ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
aval_mem (rdW W memc) (cp + CALL_OFF_NARGS) 4 4 ->
aval_mem (rdW W memc) (cp + CALL_OFF_ARGS + 16) 8 q2 ->
aval_mem (rdW W memc) (cp + CALL_OFF_ARGS + 24) 8 q3 ->
0 < q2 < 2 ^ 64 -> 0 < q3 < 2 ^ 64 -> 0 < pp -> 0 < cl ->
astr_at SEGS W memc q2 x2 -> aread_ok SEGS (2 * ESTACK) W regsc memc q2 (astr_len x2 + 1) ->
atail_vis SEGS W memc (q2 + astr_len x2) ->
astr_at SEGS W memc q3 x3 -> aread_ok SEGS (2 * ESTACK) W regsc memc q3 (astr_len x3 + 1) ->
atail_vis SEGS W memc (q3 + astr_len x3) ->
astr_at SEGS W memc pp x2 -> aread_ok SEGS (2 * ESTACK) W regsc memc pp (astr_len x2 + 1) ->
atail_vis SEGS W memc (pp + astr_len x2) ->
astr_at SEGS W memc cl x3 -> aread_ok SEGS (2 * ESTACK) W regsc memc cl (astr_len x3 + 1) ->
atail_vis SEGS W memc (cl + astr_len x3) ->
q3 + astr_len x3 + 1 <= alloc_ceiling -> cl + astr_len x3 + 1 <= alloc_ceiling ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 0x26ec)) memc (seg_rom SEGS)) mdc)
(apost_base SEGS B CHECK_WORDS_ADD_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ S' = S)).
Proof.
intros ly S W regs mem md cp q2 q3 pp cl x2 x3 memc mdc regsc
HPRE HRO HJ VOBJS ASTRCMP R2 R3 R4 Rhi R8 R9 R18 R21 HFR Hcp1 Hcp2 HN HQ2 HQ3
Rq2 Rq3 Hpp0 Hcl0 SQ2 RQ2 TQ2 SQ3 RQ3 TQ3 SPP RPP TPP SCL RCL TCL Bq3 Bcl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CHECK_WORDS_ADD_STK = 8256) by reflexivity.
destruct (cwa_tail_entry ly S W regs mem md ly S W memc mdc regsc cp q2 q3
HJ VOBJS R2 R8 R21 HFR Hcp1 Hcp2 HN HQ2 HQ3 ltac:(lia) ltac:(lia)) as [HS SHOK].
assert (EN : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
ew (cwa_ET regsc q2 q3 regs) n = getr regsc rr)
by (intros n rr Hn Hrr; unfold cwa_ET; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 10)%nat -> ew (cwa_ET regsc q2 q3 regs) (32 + j) = nth j (cwa_extraT q2 q3 regs) (Z_to_bv 64 0))
by (intros j Hj; unfold cwa_ET; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EN 2%nat 2%bv ltac:(lia) eq_refl) as Ea2.
pose proof (EN 9%nat 9%bv ltac:(lia) eq_refl) as Ea9.
pose proof (EN 18%nat 18%bv ltac:(lia) eq_refl) as Ea18.
pose proof (EN 21%nat 21%bv ltac:(lia) eq_refl) as Ea21.
pose proof (EX 1%nat ltac:(lia)) as Ea33. pose proof (EX 2%nat ltac:(lia)) as Ea34.
pose proof (EX 3%nat ltac:(lia)) as Ea35. pose proof (EX 4%nat ltac:(lia)) as Ea36.
pose proof (EX 5%nat ltac:(lia)) as Ea37. pose proof (EX 6%nat ltac:(lia)) as Ea38.
pose proof (EX 7%nat ltac:(lia)) as Ea39. pose proof (EX 8%nat ltac:(lia)) as Ea40.
pose proof (EX 9%nat ltac:(lia)) as Ea41.
cbn [Nat.add nth cwa_extraT] in Ea33, Ea34, Ea35, Ea36, Ea37, Ea38, Ea39, Ea40, Ea41.
pose proof (EN 8%nat 8%bv ltac:(lia) eq_refl) as Ea8.
assert (Ea241 : ew (cwa_ET regsc q2 q3 regs) 241 = Z_to_bv 64 (VAL (A_OBJ 0)))
by (unfold cwa_ET; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ea253 : ew (cwa_ET regsc q2 q3 regs) 253 = Z_to_bv 64 (VAL (A_OBJ 12)))
by (unfold cwa_ET; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
set (E := cwa_ET regsc q2 q3 regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold cwa_ET; apply Eimg_env).
paj_run_tok RUN HS HJ SHOK CWA_SPAN; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv1 := mdq) in *; clearbody mdv1 end.
assert (HmemE : ms_mem ms = memc)
by (exact (frame_of_read_only _ cwa_regionsT _ _ ltac:(vm_compute; reflexivity) HF)).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Qsp : spZ (ms_regs ms) = spZ regs + (-64)).
{ assert (HR : 0 <= spZ regs - 64 < 2 ^ 64)
  by (try unfold CHECK_WORDS_ADD_STK in *; try unfold ESTACK in *; unfold spZ in *; lia).
  unfold spZ in *. rewrite Q2, Ea2, R2. try unfold w64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B))
by (rewrite Q3, (EN 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B))
by (rewrite Q4, (EN 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
assert (Qra : YK0s.ret_ok (getr (ms_regs ms) 1))
by (rewrite Q1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]).
assert (Qa0 : getr (ms_regs ms) 10 = w64 q2) by (rewrite Q10, Ea33; reflexivity).
assert (Qa1 : getr (ms_regs ms) 11 = w64 pp) by (rewrite Q11, Ea9, R9; reflexivity).
assert (Hspc : spZ (ms_regs ms) = spZ regsc).
{ assert (HR : 0 <= spZ regs - 64 < 2 ^ 64)
  by (try unfold CHECK_WORDS_ADD_STK in *; try unfold ESTACK in *; unfold spZ in *; lia).
  rewrite Qsp. unfold spZ in *. rewrite R2. try unfold w64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
assert (HEP : ecall_pre_stk SEGS B (2 * ESTACK) ly S W (ms_regs ms) (ms_mem ms) mdv1).
{ eapply (ecall_pre_stk_at SEGS B
  (2 * ESTACK) CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) _ 0 (ms_regs ms) (-64) HJ Qsp);
  [reflexivity | lia | unfold ESTACK; lia | unfold CHECK_WORDS_ADD_STK, ESTACK; lia | exact Qra | exact Qgp | exact Qtp]. }
assert (ROMc : rt_rom_view SEGS B W (ms_mem ms))
by (eapply (cwa_rom_at B RLO RHI); [exact HRO | exact HJ]).
assert (SQ2c : astr_at SEGS W (ms_mem ms) q2 x2) by (rewrite HmemE; exact SQ2).
assert (SPPc : astr_at SEGS W (ms_mem ms) pp x2) by (rewrite HmemE; exact SPP).
assert (TQ2c : atail_vis SEGS W (ms_mem ms) (q2 + astr_len x2)) by (rewrite HmemE; exact TQ2).
assert (TPPc : atail_vis SEGS W (ms_mem ms) (pp + astr_len x2)) by (rewrite HmemE; exact TPP).
assert (RQ2c : aread_ok SEGS (2 * ESTACK) W (ms_regs ms) (ms_mem ms) q2 (astr_len x2 + 1))
by (rewrite HmemE; exact (cwa_aread_sp _ W regsc (ms_regs ms) memc _ _ Hspc RQ2)).
assert (RPPc : aread_ok SEGS (2 * ESTACK) W (ms_regs ms) (ms_mem ms) pp (astr_len x2 + 1))
by (rewrite HmemE; exact (cwa_aread_sp _ W regsc (ms_regs ms) memc _ _ Hspc RPP)).
assert (HC : SRr SEGS W (cfg_at SEGS (SIGMA CS___interceptor_trampoline_strcmp) (ms_regs ms) (ms_mem ms) mdv1)
(art_post SEGS B (2 * ESTACK) ly S W (ms_regs ms) (ms_mem ms) mdv1
(fun _ => False) (fun regs' _ => getr regs' 10 = w64 0 <-> x2 = x2)))
by (exact (ASTRCMP ly S W (ms_regs ms) (ms_mem ms) mdv1 q2 pp x2 x2
HEP Qa0 Qa1 ltac:(lia) Hpp0 SQ2c SPPc RQ2c RPPc TQ2c TPPc ROMc)).
eapply SRr_bind.
{ exact (aj_art_at SEGS B (cwa_laws B) Hsegs (cf_env B HFACTS) (2 * ESTACK) (fun _ => False)
  (SIGMA CS___interceptor_trampoline_strcmp) W (ms_regs ms) (ms_mem ms) CHECK_WORDS_ADD_STK (spZ regs) []
  ly S W mem md [] ly S mdv1 0 (-64) (getr (ms_regs ms) 1)
  (fun regs' _ => getr regs' 10 = w64 0 <-> x2 = x2)
  HJ Qsp ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(unfold CHECK_WORDS_ADD_STK, ESTACK; lia)
  eq_refl (fun a H => False_ind _ H) HC). }
cbv beta. intros W2 c2 _ (HW2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & HQr2 & HKP2). subst W2 c2.
rewrite Q1.
pose proof (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as HV0.
pose proof (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as HV12.
assert (VO0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VO12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
jafter_call_keep_pi HS 52%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. rewrite HmemE in HKP2 |- *.
  repeat apply Forall_cons; try apply Forall_nil;
  (apply (cwa_region_kept _ W memc mem2 _ (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
   [ intros a Ha Hn; exact (HKP2 a Ha Hn (fun x => x)) | .. ]);
  cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
  all: rewrite ?Ea2, ?Ea8, ?Ea241, ?Ea253, ?R2, ?R8, ?VO0, ?VO12; cwa_arith. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc; [exact HEI | cbv; lia]) end.
apply (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0) in HS;
[| cbn [ms_regs restrict mkst]; exact (proj2 HQr2 eq_refl) | reflexivity].
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?m =>
let ss' := eval vm_compute in ss in change ss with ss' in HS end.
assert (HmemE2 : forall b, 0 <= b < 2 ^ 64 -> ~ (spZ regs + -64 - 2 * ESTACK <= b < spZ regs + -64) ->
rdW W mem2 b = rdW W memc b) by (intros b Hb Hn; rewrite <- HmemE; exact (HKP2 b Hb Hn (fun x => x))).
lazymatch type of HS with st_ok_pi _ _ ?E2 _ _ =>
assert (SHOK2 : sh_ok SEGS CWA_BXT cwa_SHT E2 (mrestrict (w_H W) mem2)) end.
{ unfold sh_ok, cwa_SHT. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem2 _ CWA_BXT 8 A_G_REC REC_SIZE cp 4 40).
  + exact (CWA_GREC ly S W mem2 md2 (proj1 HJ2)).
  + unfold U, CWA_BXT. cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add].
    rewrite Ea21, R21. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. apply unsigned_lit_small. cwa_unf. lia.
  + unfold U. cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add].
    rewrite Ea8, R8. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. apply unsigned_lit_small. cwa_unf. lia.
  + cwa_unf. lia.
  + cwa_unf. lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. cwa_unf. lia. }
assert (HKO : kept_out (rdW W memc) (rdW W mem2) (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64)) by exact HmemE2.
pose proof (ASAN_CEIL_range) as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
assert (HLO : alloc_ceiling <= spZ regs + -64 - 2 * ESTACK) by (cwa_unf; lia).
assert (SQ3k : astr_at SEGS W mem2 q3 x3).
{ apply astr_atR_view. apply (astr_atR_kept _ _ _ _ q3 x3 HKO); [apply astr_atR_view; exact SQ3 | lia | unfold astr_len in Bq3; lia | cwa_unf; lia]. }
assert (SCLk : astr_at SEGS W mem2 cl x3).
{ apply astr_atR_view. apply (astr_atR_kept _ _ _ _ cl x3 HKO); [apply astr_atR_view; exact SCL | lia | unfold astr_len in Bcl; lia | cwa_unf; lia]. }
assert (L3 : 0 <= astr_len x3) by (unfold astr_len; lia).
assert (TQ3k : atail_vis SEGS W mem2 (q3 + astr_len x3)).
{ apply (atail_vis_kept SEGS W memc mem2 _ _ _ HKO TQ3).
  - clear - Rq3 L3. lia.
  - pose proof (tail_below (q3 + astr_len x3) alloc_ceiling) as TB.
    assert (TB1 : 0 <= q3 + astr_len x3 < alloc_ceiling) by (clear - Rq3 L3 Bq3; lia).
    specialize (TB TB1 CE2). clear - TB HLO. lia.
  - clear - Hshi H47. unfold spZ in *. unfold ESTACK. lia. }
assert (TCLk : atail_vis SEGS W mem2 (cl + astr_len x3)).
{ apply (atail_vis_kept SEGS W memc mem2 _ _ _ HKO TCL).
  - clear - Hcl0 L3. lia.
  - pose proof (tail_below (cl + astr_len x3) alloc_ceiling) as TB.
    assert (TB1 : 0 <= cl + astr_len x3 < alloc_ceiling) by (clear - Hcl0 L3 Bcl; lia).
    specialize (TB TB1 CE2). clear - TB HLO. lia.
  - clear - Hshi H47. unfold spZ in *. unfold ESTACK. lia. }
assert (HKH : kHighShadowEnd <= spZ regs + -64 - 2 * ESTACK) by (cwa_unf; lia).
assert (RQ3k : aread_ok SEGS (2 * ESTACK) W regsc mem2 q3 (astr_len x3 + 1)).
{ apply (aread_ok_kept SEGS (2 * ESTACK) (2 * ESTACK) W regsc regsc memc mem2 _ _ q3 _ HKO RQ3);
  [lia | exact HKH | cwa_unf; lia | unfold spZ in *; rewrite R2; try unfold w64; rewrite unsigned_lit_small by (cwa_unf; lia); cwa_unf; lia | cwa_unf; lia]. }
assert (RCLk : aread_ok SEGS (2 * ESTACK) W regsc mem2 cl (astr_len x3 + 1)).
{ apply (aread_ok_kept SEGS (2 * ESTACK) (2 * ESTACK) W regsc regsc memc mem2 _ _ cl _ HKO RCL);
  [lia | exact HKH | cwa_unf; lia | unfold spZ in *; rewrite R2; try unfold w64; rewrite unsigned_lit_small by (cwa_unf; lia); cwa_unf; lia | cwa_unf; lia]. }
clear HF HFr HG Q1 Q2 Q3 Q4 Q10 Q11 Qsp Qgp Qtp Qra Qa0 Qa1 Hspc HEP ROMc SQ2c SPPc TQ2c TPPc RQ2c RPPc HC HmemE
HV0 HV12 HP2 HQr2 HKP2 HJ SHOK.
clear ms mdv1.
paj_run_tok RUN HS HJ2 SHOK2 CWA_SPAN; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
assert (HmemF : ms_mem ms = mem2)
by (exact (frame_of_read_only _ cwa_regionsT _ _ ltac:(vm_compute; reflexivity) HF)).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Qsp : spZ (ms_regs ms) = spZ regs + (-64)).
{ assert (HR : 0 <= spZ regs - 64 < 2 ^ 64) by (cwa_unf; lia).
  unfold spZ in *. rewrite Q2, Ea2, R2. try unfold w64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
assert (Qgp : getr (ms_regs ms) 3 = w64 (as_gp B))
by (rewrite Q3, (EN 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (Qtp : getr (ms_regs ms) 4 = w64 (as_tp B))
by (rewrite Q4, (EN 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
assert (Qra : YK0s.ret_ok (getr (ms_regs ms) 1))
by (rewrite Q1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]).
assert (Qa0 : getr (ms_regs ms) 10 = w64 q3) by (rewrite Q10, Ea34; reflexivity).
assert (Qa1 : getr (ms_regs ms) 11 = w64 cl) by (rewrite Q11, Ea18, R18; reflexivity).
assert (Hspc : spZ (ms_regs ms) = spZ regsc).
{ assert (HR : 0 <= spZ regs - 64 < 2 ^ 64) by (cwa_unf; lia).
  rewrite Qsp. unfold spZ in *. rewrite R2. try unfold w64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdq) _ =>
assert (HEP : ecall_pre_stk SEGS B (2 * ESTACK) ly S W (ms_regs ms) (ms_mem ms) mdq) end.
{ eapply (ecall_pre_stk_at SEGS B
  (2 * ESTACK) CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) _ 0 (ms_regs ms) (-64) HJ2 Qsp);
  [reflexivity | lia | unfold ESTACK; lia | unfold CHECK_WORDS_ADD_STK, ESTACK; lia | exact Qra | exact Qgp | exact Qtp]. }
assert (ROMc : rt_rom_view SEGS B W (ms_mem ms))
by (eapply (cwa_rom_at B RLO RHI); [exact HRO | exact HJ2]).
assert (SQ3c : astr_at SEGS W (ms_mem ms) q3 x3) by (rewrite HmemF; exact SQ3k).
assert (SCLc : astr_at SEGS W (ms_mem ms) cl x3) by (rewrite HmemF; exact SCLk).
assert (TQ3c : atail_vis SEGS W (ms_mem ms) (q3 + astr_len x3)) by (rewrite HmemF; exact TQ3k).
assert (TCLc : atail_vis SEGS W (ms_mem ms) (cl + astr_len x3)) by (rewrite HmemF; exact TCLk).
assert (RQ3c : aread_ok SEGS (2 * ESTACK) W (ms_regs ms) (ms_mem ms) q3 (astr_len x3 + 1))
by (rewrite HmemF; exact (cwa_aread_sp _ W regsc (ms_regs ms) mem2 _ _ Hspc RQ3k)).
assert (RCLc : aread_ok SEGS (2 * ESTACK) W (ms_regs ms) (ms_mem ms) cl (astr_len x3 + 1))
by (rewrite HmemF; exact (cwa_aread_sp _ W regsc (ms_regs ms) mem2 _ _ Hspc RCLk)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdq) _ =>
assert (HC : SRr SEGS W (cfg_at SEGS (SIGMA CS___interceptor_trampoline_strcmp) (ms_regs ms) (ms_mem ms) mdq)
(art_post SEGS B (2 * ESTACK) ly S W (ms_regs ms) (ms_mem ms) mdq
(fun _ => False) (fun regs' _ => getr regs' 10 = w64 0 <-> x3 = x3)))
by (exact (ASTRCMP ly S W (ms_regs ms) (ms_mem ms) mdq q3 cl x3 x3
HEP Qa0 Qa1 ltac:(lia) Hcl0 SQ3c SCLc RQ3c RCLc TQ3c TCLc ROMc)) end.
eapply SRr_bind.
{ eapply (aj_art_at SEGS B (cwa_laws B) Hsegs (cf_env B HFACTS) (2 * ESTACK) (fun _ => False)
  (SIGMA CS___interceptor_trampoline_strcmp) W (ms_regs ms) (ms_mem ms) CHECK_WORDS_ADD_STK (spZ regs) []
  ly S W mem md [] ly S _ 0 (-64) (getr (ms_regs ms) 1)
  (fun regs' _ => getr regs' 10 = w64 0 <-> x3 = x3)
  HJ2 Qsp ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(unfold CHECK_WORDS_ADD_STK, ESTACK; lia)
  eq_refl (fun a H => False_ind _ H) HC). }
cbv beta. intros W3 c3 _ (HW3 & regs3 & mem3 & md3 & Hc3 & HJ3 & HP3 & HQr3 & HKP3). subst W3 c3.
rewrite Q1.
jafter_call_keep_pi HS 80%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. rewrite HmemF in HKP3 |- *.
  repeat apply Forall_cons; try apply Forall_nil;
  (apply (cwa_region_kept _ W mem2 mem3 _ (spZ regs + -64 - 2 * ESTACK) (spZ regs + -64));
   [ intros a Ha Hn; exact (HKP3 a Ha Hn (fun x => x)) | .. ]);
  cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
  all: cbn [ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add map CLOB].
  all: rewrite ?Ea2, ?Ea8, ?Ea241, ?Ea253, ?R2, ?R8, ?VO0, ?VO12; cwa_arith. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (HEI3 : img_env VAL A_LIM E3) by (apply img_env_havoc; [assumption | cbv; lia]) end.
apply (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0) in HS;
[| cbn [ms_regs restrict mkst]; exact (proj2 HQr3 eq_refl) | reflexivity].
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?m =>
let ss' := eval vm_compute in ss in change ss with ss' in HS end.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (SHOK3 : sh_ok SEGS CWA_BXT [] E3 (mrestrict (w_H W) mem3)) by constructor end.
clear SHOK2.
paj_run_tok RUN HS HJ3 SHOK3 CWA_SPAN; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv3 := mdq) in *; clearbody mdv3 end.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (mF := msF) in * end.
prreg HS (1%bv : bv 5) F1.
assert (FIN : forall r : Z, acallee_saved r -> getr (ms_regs mF) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  repeat (destruct Hc as [-> | Hc]); [..|subst r];
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
  first [ rewrite Ea36; reflexivity | rewrite Ea37; reflexivity | rewrite Ea38; reflexivity
        | rewrite Ea39; reflexivity | rewrite Ea40; reflexivity | rewrite Ea41; reflexivity
        | lazymatch goal with |- ew _ ?n = getr _ ?rr =>
            rewrite (EN n rr ltac:(lia) eq_refl); first [exact R3 | exact R4 | apply Rhi; lia] end
        | rewrite Ea2, R2; unfold w64; rewrite unsigned_lit_small by (cwa_unf; lia);
          replace (spZ regs - 64 + 64) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned ]. }
unfold apost_base.
exists ly, S, (ms_regs mF), (ms_mem mF), (with_vm_backing (m_vm_lazy mdv3) mat' mdv3).
split; [rewrite F1, Ea35; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B (cwa_laws B) Hsegs); exact HJ3|].
split; [intros r Hr; exact (FIN r Hr)|].
split; [apply Permutation_refl | split; reflexivity].
Qed.


(* the seed at 0x88b60 when the placement is the literal "-" *)
Lemma cwa_mid_dash_entry :
forall ly S (W : world SEGS) memc mdc (regsc : bvmap 5 word) (q2 q3 p3 p4 wp r : Z) (regs : bvmap 5 word),
AR SEGS B ly S W memc mdc -> cmd_val_objs ->
getr regsc 9 = w64 0x21ac0 -> getr regsc 18 = w64 wp -> getr regsc 19 = w64 r -> 0 <= r <= 64 ->
getr regsc 21 = w64 SHADOW_OFF ->
aval_mem (rdW W memc) 0x21ac0 1 45 -> aval_mem (rdW W memc) 0x21ac1 1 0 ->
range_addressable (rdW W memc) SHADOW_OFF 0x21ac0 2 ->
st_ok_pi SEGS VAL (cwa_EM regsc q2 q3 p3 p4 regs) cwa_ssD
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 0x267c)) memc (seg_rom SEGS)))
/\ sh_ok SEGS CWA_BXT cwa_SHD (cwa_EM regsc q2 q3 p3 p4 regs) (mrestrict (w_H W) memc).
Proof.
intros ly S W memc mdc regsc q2 q3 p3 p4 wp r regs HAR VOBJS R9 R18 R19 Hr R21 HB0 HB1 HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VO0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VO12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
destruct (al_const _ _ LAWS ly S W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite CWA_GOT, CWA_CELL in Kgot. rewrite CWA_CELL in Kcell.
pose proof pa_B_ok as HBASE.
assert (EN : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
ew (cwa_EM regsc q2 q3 p3 p4 regs) n = getr regsc rr)
by (intros n rr Hn Hrr; unfold cwa_EM; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 13)%nat -> ew (cwa_EM regsc q2 q3 p3 p4 regs) (32 + j) = nth j (cwa_extraM q2 q3 p3 p4 regs) (Z_to_bv 64 0))
by (intros j Hj; unfold cwa_EM; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EN 9%nat 9%bv ltac:(lia) eq_refl) as Ea9.
pose proof (EN 18%nat 18%bv ltac:(lia) eq_refl) as Ea18.
pose proof (EN 19%nat 19%bv ltac:(lia) eq_refl) as Ea19.
pose proof (EN 21%nat 21%bv ltac:(lia) eq_refl) as Ea21.
assert (Ea241 : ew (cwa_EM regsc q2 q3 p3 p4 regs) 241 = Z_to_bv 64 (VAL (A_OBJ 0)))
by (unfold cwa_EM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ea253 : ew (cwa_EM regsc q2 q3 p3 p4 regs) 253 = Z_to_bv 64 (VAL (A_OBJ 12)))
by (unfold cwa_EM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eb241 : ew (cwa_EM regsc q2 q3 p3 p4 regs) (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by exact Ea241.
assert (Eb253 : ew (cwa_EM regsc q2 q3 p3 p4 regs) (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by exact Ea253.
rewrite restrict_mkst_fx.
set (E := cwa_EM regsc q2 q3 p3 p4 regs) in *.
assert (Upl : bv_unsigned (ew E 9) = 0x21ac0) by (rewrite Ea9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (Ur : bv_unsigned (ew E 19) = r) by (rewrite Ea19, R19; unfold w64; apply unsigned_lit_small; lia).
assert (Usb : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite Ea21, R21; unfold w64; apply unsigned_lit_small; cwa_unf; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold cwa_ssD. apply pa_entry_st_ok_full.
  + unfold E, cwa_EM. apply (regs_ok_agree 32 (Ereg regsc (cwa_extraM q2 q3 p3 p4 regs)));
    [split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity] | vm_compute; reflexivity | apply regs_ok_Ereg].
  + vm_compute. reflexivity.
  + unfold cwa_regionsD, cwa_dashR, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Upl. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ 0x21ac0 0 1 (SLit 45) 45); [reflexivity | zside | zside |].
         exact (cwa_val_mem W memc 0x21ac0 1%nat 45 HB0).
      -- apply (chunk_ok_val SEGS E _ 0x21ac0 1 1 (SLit 0) 0); [reflexivity | zside | zside |].
         exact (cwa_val_mem W memc 0x21ac1 1%nat 0 HB1).
    * rewrite ?(VB 241%nat (VAL (A_OBJ 0)) Ea241), ?(VB (A_OBJ 0) (VAL (A_OBJ 0)) Eb241)
        by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [rewrite VO0; lia|]. split; [rewrite VO0; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite ?Ea253, ?Eb253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    * rewrite ?(VB 253%nat (VAL (A_OBJ 12)) Ea253), ?(VB (A_OBJ 12) (VAL (A_OBJ 12)) Eb253)
        by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [rewrite VO12; lia|]. split; [rewrite VO12; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CWA_BXT SHADOW_OFF);
      [cbn [sv_denot CWA_BXT]; rewrite Ea21, R21, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
  + apply pairwise_disjoint_of_extents.
    unfold cwa_regionsD, cwa_dashR, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite ?(VB 241%nat (VAL (A_OBJ 0)) Ea241), ?(VB (A_OBJ 0) (VAL (A_OBJ 0)) Eb241),
            ?(VB 253%nat (VAL (A_OBJ 12)) Ea253), ?(VB (A_OBJ 12) (VAL (A_OBJ 12)) Eb253)
      by (pose proof (pa_val_range (A_OBJ 0)); pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite ?Upl, ?VO0, ?VO12.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I].
    cbn [cwa_factsD f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Upl, Ur, Usb. rewrite !Z.pow_0_r, !Z.mod_1_r.
    cwa_unf. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
- unfold sh_ok, cwa_SHD. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) memc E CWA_BXT 9 0x21ac0 2 0x21ac0 0 2).
  + exact HRA.
  + unfold U, CWA_BXT. cbn [sv_denot]. rewrite Ea21, R21, Z.add_0_r. unfold w64.
    rewrite Z_to_bv_bv_unsigned. apply unsigned_lit_small. cwa_unf. lia.
  + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Upl.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. cwa_unf. lia.
Qed.


(* 0x88b60 .. 0x88bd0 when the placement is the literal "-": the two 1-byte checks of the literal, then the
   client is word 3 if read > 3 and the literal otherwise. *)
Lemma cwa_mid_dash : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md
(cp q2 q3 wp r p3 : Z) (x3 w3 : list byte) memc mdc (regsc : bvmap 5 word),
afn_pre_na SEGS B CHECK_WORDS_ADD_STK ly S W regs mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
ajournal SEGS B CHECK_WORDS_ADD_STK (spZ regs) [] ly S W mem md [] ly S W memc mdc 0 ->
cmd_val_objs -> astrcmp_realizes SEGS B (SIGMA CS___interceptor_trampoline_strcmp) ->
cmd_ro_ok (rdW W memc) ->
getr regsc 2 = w64 (spZ regs - 64) ->
getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
(forall rr, 22 <= rr <= 27 -> getr regsc (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)) ->
getr regsc 8 = w64 cp -> getr regsc 9 = w64 0x21ac0 -> getr regsc 18 = w64 wp ->
getr regsc 19 = w64 r -> getr regsc 21 = w64 SHADOW_OFF ->
0 <= r <= 64 ->
cwa_frame (mrestrict (w_H W) memc) (spZ regs) regs ->
A_G_REC + OFF_CALLS <= cp -> cp + CALL_SIZE <= A_G_REC + REC_SIZE ->
aval_mem (rdW W memc) (cp + CALL_OFF_NARGS) 4 4 ->
aval_mem (rdW W memc) (cp + CALL_OFF_ARGS + 16) 8 q2 ->
aval_mem (rdW W memc) (cp + CALL_OFF_ARGS + 24) 8 q3 ->
cwa_str B ly S (rdW W memc) q2 S_DASH ->
cwa_str B ly S (rdW W memc) q3 x3 ->
(3 < r -> in_blockA (ablocks B ly S) (wp + 24) 8 /\ aval_mem (rdW W memc) (wp + 24) 8 p3 /\
 cwa_str B ly S (rdW W memc) p3 w3) ->
x3 = (if 3 <? r then w3 else S_DASH) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 0x267c)) memc (seg_rom SEGS)) mdc)
(apost_base SEGS B CHECK_WORDS_ADD_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ S' = S)).
Proof.
intros ly S W regs mem md cp q2 q3 wp r p3 x3 w3 memc mdc regsc
HPRE HRO HJ VOBJS ASTRCMP HROK R2 R3 R4 Rhi R8 R9 R18 R19 R21 Hr HFR Hcp1 Hcp2 HN HQ2 HQ3
AQ2 AQ3 AW3 HX3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : CHECK_WORDS_ADD_STK = 8256) by reflexivity.
pose proof (proj1 HJ) as HARc.
assert (Hspc : alloc_ceiling <= spZ regsc - 2 * ESTACK).
{ unfold spZ in *. rewrite R2. try unfold w64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by (cwa_unf; lia). cwa_unf. lia. }
destruct (cwa_dash_str ly S W regsc memc mdc HARc HROK Hspc) as (SDA & RDA & TDA & HB0 & HB1).
pose proof (cf_lit B HFACTS ly S W memc mdc HARc) as HLIT. rewrite Forall_forall in HLIT.
destruct (HLIT (0x21ac0, 2) ltac:(cbv [CWA_LITS In]; tauto)) as [HRA _]. cbn [fst snd] in HRA.
destruct (cwa_str_facts B ly S W regsc memc mdc q2 S_DASH HARc AQ2 Hspc)
as (Hq20 & SQ2 & RQ2 & TQ2 & Bq2 & Rq2).
destruct (cwa_str_facts B ly S W regsc memc mdc q3 x3 HARc AQ3 Hspc)
as (Hq30 & SQ3 & RQ3 & TQ3 & Bq3 & Rq3).
destruct (cwa_mid_dash_entry ly S W memc mdc regsc q2 q3 p3 0 wp r regs
HARc VOBJS R9 R18 R19 Hr R21 HB0 HB1 HRA) as [HS SHOK].
assert (EN : forall (n : nat) (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
ew (cwa_EM regsc q2 q3 p3 0 regs) n = getr regsc rr)
by (intros n rr Hn Hrr; unfold cwa_EM; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hrr).
assert (EX : forall j, (j < 13)%nat ->
ew (cwa_EM regsc q2 q3 p3 0 regs) (32 + j) = nth j (cwa_extraM q2 q3 p3 0 regs) (Z_to_bv 64 0))
by (intros j Hj; unfold cwa_EM; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EN 9%nat 9%bv ltac:(lia) eq_refl) as Ea9.
pose proof (EN 18%nat 18%bv ltac:(lia) eq_refl) as Ea18.
pose proof (EN 19%nat 19%bv ltac:(lia) eq_refl) as Ea19.
pose proof (EN 21%nat 21%bv ltac:(lia) eq_refl) as Ea21.
pose proof (EX 11%nat ltac:(lia)) as Ea43. pose proof (EX 1%nat ltac:(lia)) as Ea33.
pose proof (EX 2%nat ltac:(lia)) as Ea34.
cbn [Nat.add nth cwa_extraM] in Ea33, Ea34, Ea43.
set (E := cwa_EM regsc q2 q3 p3 0 regs) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, cwa_EM; apply Eimg_env).
paj_run_to_tok RUNTO HS HJ SHOK CWA_SPAN 0x26b8; [awr_ok_tac |].
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv1 := mdq) in *; clearbody mdv1 end.
assert (HmemE : ms_mem ms = memc)
by (exact (frame_of_read_only _ cwa_regionsD _ _ ltac:(vm_compute; reflexivity) HF)).
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
assert (HR19 : sv_denot E1 (SOff 19 0) = Z_to_bv 64 r);
[ cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add];
  rewrite Z.add_0_r, Ea19, R19, Z_to_bv_bv_unsigned; reflexivity |];
assert (HR3 : sv_denot E1 (SLit 3) = Z_to_bv 64 3) by reflexivity end.
psrr_branch_tok RUN BR HS SHOK CWA_SPAN.
- rewrite (cwa_branch_lt _ _ _ 3 r HR3 HR19 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc.
  destruct (AW3 Hc) as (HBK & HVW & AP3).
  destruct (cwa_str_facts B ly S W regsc memc mdc p3 w3 HARc AP3 Hspc)
  as (Hp30 & SP3 & RP3 & TP3 & Bp3 & Rp3).
  assert (X3W : x3 = w3) by (rewrite HX3; rewrite (proj2 (Z.ltb_lt 3 r) Hc); reflexivity).
  rewrite X3W in SQ3, RQ3, TQ3, Bq3.
  destruct HBK as (qb & kb & Hinb & Hqb1 & Hqb2).
  assert (HRAW : range_addressable (rdW W memc) SHADOW_OFF qb (req_size kb))
  by (exact (range_addressable_of_block SEGS B (cwa_laws B) ly S W memc mdc qb kb qb (req_size kb) HARc Hinb
  ltac:(lia) ltac:(lia))).
  destruct (al_blocks _ _ (cwa_laws B) _ _ _ _ _ qb kb HARc Hinb) as (Hb16 & Hb4096 & Hbceil & Hbia & Hbpres & _).
  pose proof (req_size_pos kb ltac:(lia)) as [Hr1 Hr2].
  pose proof ASAN_CEIL_range as (CE1 & CE2). unfold ASAN_CEIL in CE1, CE2.
  assert (Hwp1 : 4072 <= wp) by lia.
  assert (Hwp2 : wp + 32 <= 0x7fffff800000) by lia.
  apply cwa_set_mem_nil in HS.
  apply (st_ok_pi_add_fact _ _ _ 18%nat (mkAF 4072 0x7fffff800000 0)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2];
     cbn [ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add];
     rewrite Ea18, R18; unfold w64; rewrite unsigned_lit_small by lia;
     rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia].
  apply (st_ok_pi_add_region _ _ _ (cwa_wordR 24 43)) in HS;
  [ | vm_compute; reflexivity | | ].
  + lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 _ =>
      assert (SHOKW : sh_ok SEGS CWA_BXT cwa_SHDW E1 (mrestrict (w_H W) (ms_mem ms))) end.
    { unfold sh_ok, cwa_SHDW. constructor; [|constructor; [|constructor]].
      - exact (Forall_inv SHOK).
      - apply (shent_ok_of_range SEGS (w_H W) (ms_mem ms) _ CWA_BXT 18 qb (req_size kb) wp 24 32).
        + rewrite HmemE. exact HRAW.
        + unfold U, CWA_BXT. cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add].
          rewrite Z.add_0_r, Ea21, R21. unfold w64. rewrite Z_to_bv_bv_unsigned.
          apply unsigned_lit_small. cwa_unf. lia.
        + unfold U. cbn [sv_denot ew ewset havoc Eimg extK Nat.eqb Nat.ltb Nat.leb nth Nat.sub andb length Nat.add].
          rewrite Z.add_0_r, Ea18, R18. unfold w64. rewrite Z_to_bv_bv_unsigned.
          apply unsigned_lit_small. lia.
        + lia.
        + lia.
        + intros x Hx. cbn [Z.min Z.max] in Hx.
          unfold in_app, kLowShadowBeg, kHighMemBeg in Hbia. destruct Hbia as [_ [Hap | [Hap Hap2]]];
          cwa_unf; lia. }
    clear SHOK. rename SHOKW into SHOK.
    assert (VO29 : VAL (A_OBJ 29) = 0x21ac0)
    by (rewrite (VOBJS 29%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK CWA_SPAN 0x26ec; [awr_ok_tac |].
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
      assert (HM2 : mm = memc);
      [ rewrite <- HmemE;
        lazymatch goal with HFx : frame_of _ ?rs _ mm |- _ =>
          exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HFx) end
      | ] end.
    prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
    prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
    prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21.
    assert (T2 : getr (ms_regs ms0) 2 = w64 (spZ regs - 64))
    by (rewrite P2, (EN 2%nat 2%bv ltac:(lia) eq_refl); exact R2).
    assert (T3 : getr (ms_regs ms0) 3 = getr regs 3)
    by (rewrite P3, (EN 3%nat 3%bv ltac:(lia) eq_refl); exact R3).
    assert (T4 : getr (ms_regs ms0) 4 = getr regs 4)
    by (rewrite P4, (EN 4%nat 4%bv ltac:(lia) eq_refl); exact R4).
    assert (T8 : getr (ms_regs ms0) 8 = w64 cp)
    by (rewrite P8, (EN 8%nat 8%bv ltac:(lia) eq_refl); exact R8).
    assert (T9 : getr (ms_regs ms0) 9 = w64 0x21ac0)
    by (rewrite P9, (EN 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
    assert (T18 : getr (ms_regs ms0) 18 = w64 p3) by (rewrite P18, Ea43; reflexivity).
    assert (T21 : getr (ms_regs ms0) 21 = w64 SHADOW_OFF)
    by (rewrite P21, (EN 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
    assert (Thi : forall rr, 22 <= rr <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
    { intros rr Hrr.
      assert (Hc' : rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
      repeat (destruct Hc' as [-> | Hc']); [..|subst rr];
      lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
        let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
      lazymatch goal with |- ew _ ?n = getr _ ?r2 =>
        rewrite (EN n r2 ltac:(lia) eq_refl); apply Rhi; lia end. }
    assert (Hsp0 : spZ (ms_regs ms0) = spZ regsc) by (unfold spZ; rewrite T2, R2; reflexivity).
    rewrite HM2 in HJ.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    apply (cwa_tail ly S W regs mem md cp q2 q3 0x21ac0 p3 S_DASH w3 mm mdq rg) end.
    all: rewrite ?HM2.
    all: try assumption.
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RQ2)).
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RQ3)).
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RDA)).
    all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RP3)).
    all: try (cbv [astr_len S_DASH str map length]); cwa_unf; lia.
  + unfold cwa_wordR, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst].
    assert (BW : base_val E (Some 18%nat) = wp)
    by (cbn [base_val]; rewrite Ea18, R18; unfold w64; apply unsigned_lit_small; lia).
    assert (BW' : bv_unsigned (ew E 18) = wp)
    by (rewrite Ea18, R18; unfold w64; apply unsigned_lit_small; lia).
    cbn [base_val ew ewset Nat.eqb]. rewrite HmemE, ?BW, ?BW'.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS _ _ wp 24 8 (SOff 43 0) p3);
    [ cbn [sv_denot ew ewset Nat.eqb]; rewrite Ea43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 p3)) as HR;
      change (bv_modulus 64) with (2 ^ 64) in HR; rewrite Z_to_bv_unsigned in HR; unfold bv_wrap in HR;
      change (bv_modulus 64) with (2 ^ 64) in HR; zside
    | zside |].
    exact (cwa_val_mem W memc (wp + 24) 8%nat p3 HVW).
  + cbn [ss_mem]. unfold all_disjoint. first [constructor | exact I].
- rewrite (cwa_branch_lt _ _ _ 3 r HR3 HR19 ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_ge in Hc.
  assert (VO29 : VAL (A_OBJ 29) = 0x21ac0)
  by (rewrite (VOBJS 29%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK CWA_SPAN 0x26ec; [awr_ok_tac |].
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
    assert (HM2 : mm = memc);
    [ rewrite <- HmemE;
      lazymatch goal with HFx : frame_of _ ?rs _ mm |- _ =>
        exact (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HFx) end
    | ] end.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
  prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21.
  assert (X3D : x3 = S_DASH) by (rewrite HX3; rewrite (proj2 (Z.ltb_ge 3 r) Hc); reflexivity).
  rewrite X3D in SQ3, RQ3, TQ3, Bq3.
  assert (E270 : ew (cwa_EM regsc q2 q3 p3 0 regs) 270 = Z_to_bv 64 (VAL (A_OBJ 29)))
  by (unfold cwa_EM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  fold E in E270.
  assert (T2 : getr (ms_regs ms0) 2 = w64 (spZ regs - 64))
  by (rewrite P2, (EN 2%nat 2%bv ltac:(lia) eq_refl); exact R2).
  assert (T3 : getr (ms_regs ms0) 3 = getr regs 3)
  by (rewrite P3, (EN 3%nat 3%bv ltac:(lia) eq_refl); exact R3).
  assert (T4 : getr (ms_regs ms0) 4 = getr regs 4)
  by (rewrite P4, (EN 4%nat 4%bv ltac:(lia) eq_refl); exact R4).
  assert (T8 : getr (ms_regs ms0) 8 = w64 cp)
  by (rewrite P8, (EN 8%nat 8%bv ltac:(lia) eq_refl); exact R8).
  assert (T9 : getr (ms_regs ms0) 9 = w64 0x21ac0)
  by (rewrite P9, (EN 9%nat 9%bv ltac:(lia) eq_refl); exact R9).
  assert (T18 : getr (ms_regs ms0) 18 = w64 0x21ac0)
  by (rewrite P18, E270, VO29; reflexivity).
  assert (T21 : getr (ms_regs ms0) 21 = w64 SHADOW_OFF)
  by (rewrite P21, (EN 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
  assert (Thi : forall rr, 22 <= rr <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 rr) = getr regs (Z_to_bv 5 rr)).
  { intros rr Hrr.
    assert (Hc' : rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    repeat (destruct Hc' as [-> | Hc']); [..|subst rr];
    lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
      let G := fresh "G" in prreg HS (Z_to_bv 5 k) G; rewrite G end;
    lazymatch goal with |- ew _ ?n = getr _ ?r2 =>
      rewrite (EN n r2 ltac:(lia) eq_refl); apply Rhi; lia end. }
  assert (Hsp0 : spZ (ms_regs ms0) = spZ regsc)
  by (unfold spZ; rewrite T2, R2; reflexivity).
  rewrite HM2 in HJ.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  apply (cwa_tail ly S W regs mem md cp q2 q3 0x21ac0 0x21ac0 S_DASH S_DASH mm mdq rg) end.
  all: rewrite ?HM2.
  all: try assumption.
  all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RQ2)).
  all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RQ3)).
  all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RDA)).
  all: try exact SQ3. all: try exact TQ3. all: try exact Bq3.
  all: try (exact (cwa_aread_sp _ W regsc (ms_regs ms0) memc _ _ Hsp0 RQ3)).
  all: try (cbv [astr_len S_DASH str map length]); cwa_unf; lia.
Qed.

End e.
End f.
End d.


