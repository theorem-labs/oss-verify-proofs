(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic entry states of sup_connect's ASan walk
   (plugin-hostd/fuzz_command, 0x8ad20), in the form of cgif_file_fuzzer's A/AChc.v (the seed of a walk) and
   A/AChd.v, and the per-binary facts about the program's own statics that the walk uses at every step.

   The walk is cut in two at 0x8adac, the join of record()'s two arms, because the call slot's address is
   g_rec + 16 + 56 * ncalls on one arm and record.spill on the other: before the cut the slot is only computed
   (the executor keeps it as an offset of the object atom A_OBJ 44), after the cut it is the base of a region
   and of the shadow entry that removes the nine inline checks, so it must be an atom. `scn_ss_e` is the state
   at the entry and `scn_ss_m` the state at the join.

   Atoms. At the entry: 0..31 the registers, 32 the shadow base 0x7fff8000; the regions are the 80-byte frame,
   the GOT word A_OBJ 0 = 0xa63f0 and the cell A_OBJ 12 = 0xb10b8 (read-only), and g_rec's ncalls field
   [A_OBJ 44 + 8, A_OBJ 44 + 12). At the join: 0..31 the registers there (s0 = the slot, s6 = the shadow base),
   32..40 the entry values of ra, s0..s7 that the frame holds; the regions are that frame (read-only) and the
   slot [s0, s0 + 56); the one shadow entry is [s0, s0 + 56). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_connect_s0.v; 666 of its 795 lines of code are new or changed and 293 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibF PaCall PaNoChain PaArt CmdBase CmdRep CmdObj CmdZsh CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_line_c answer_c rec_canonical_c hand_back_c sup_connect_c sup_connect_s0 sup_connect_s2.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition scn_xa (n : Z) : list word := map (Z_to_bv 64) [SCN_SB; n].
Definition scn_ncalls_ra : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) OFF_NCALLS (OFF_NCALLS + 4) OFF_NCALLS (OFF_NCALLS + 4)
[YP09.mkChunk OFF_NCALLS (CVal 4 (SOff 33 0))].
Definition scn_regs_a : smem := [stack_region 80; got_regionP; bcell_regionP 32; scn_ncalls_ra].
Definition scn_facts_a : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SCN_SB SCN_SB 0); (33%nat, mkAF 0 16 0);
(A_OBJ 44, mkAF A_G_REC A_G_REC 0)] [] [].
Definition scn_ss_a : sstate := mkSS AF_sup_connect sr_atoms scn_regs_a None scn_facts_a.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis PROG_WRITABLE : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at SEGS m a.
Hypothesis RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma scn_entry_a : forall (W : world SEGS) ly S (regs : bvmap 5 word) mem md ch n,
afn_pre SEGS B SUP_CONNECT_STK ly S W regs mem md ch ->
0 <= n <= 16 ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (scn_xa n))) scn_ss_a
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_connect)) mem (seg_rom SEGS)))
/\ sh_ok SEGS scn_Bx_e scn_SH_e (Eimg (Ereg regs (scn_xa n))) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch n HPRE Hn Hncalls.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : SUP_CONNECT_STK = 16592) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (scn_xa n))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SCN_SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 (VAL (A_OBJ 44)))
by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (scn_obj0 VOBJS) as V0. pose proof (scn_obj12 VOBJS) as V12. pose proof (scn_obj44 VOBJS) as V44.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (HW : forall o, OFF_NCALLS <= o < OFF_NCALLS + 4 ->
writable_at SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 44) + o)).
{ intros o Ho. apply (scn_pg_writable B PROG_WRITABLE ly S W mem md); [exact HAR|].
  rewrite V44. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
  cbn [fst snd]. unfold OFF_NCALLS in Ho. lia. }
assert (CK : YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (VAL (A_OBJ 44))
(YP09.mkChunk OFF_NCALLS (CVal 4 (SOff 33 0)))).
{ apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 44)) OFF_NCALLS 4 (SOff 33 0) n);
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia |].
  rewrite V44. exact (scn_val_mem_of_aval SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4 n Hncalls). }
assert (RG : forall r, In r [got_regionP; bcell_regionP 32] -> YP09.region_ok SEGS E (mrestrict (w_H W) mem) r).
{ intros r [<- | [<- | []]]; unfold region_ok, got_regionP, bcell_regionP;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  - rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (rewrite V0; lia). split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | rewrite V12; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (rewrite V12; lia). split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 scn_Bx_e SCN_SB);
    [cbn [sv_denot scn_Bx_e]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | unfold SCN_SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell). }
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H W) mem) (stack_region 80)).
{ unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
assert (RN : YP09.region_ok SEGS E (mrestrict (w_H W) mem) scn_ncalls_ra).
{ unfold region_ok, scn_ncalls_ra.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 44) (VAL (A_OBJ 44)) E285) by (rewrite V44; unfold A_G_REC; lia).
  split; [rewrite V44; unfold A_G_REC, OFF_NCALLS; lia|].
  split; [rewrite V44; unfold A_G_REC, OFF_NCALLS; lia|].
  split; [exact HW|]. constructor; [exact CK | constructor]. }
assert (HG : facts_ok E scn_facts_a).
{ split; [|split; [exact I | exact I]].
  cbn [scn_facts_a f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E285, V44, !unsigned_lit_small by (unfold SCN_SB, A_G_REC; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 FFS Hstk0 Hn. clear. unfold SCN_SB, A_G_REC. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
split.
- unfold scn_ss_a. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold scn_regs_a. constructor; [exact RS|]. constructor; [apply RG; left; reflexivity|].
    constructor; [apply RG; right; left; reflexivity|]. constructor; [exact RN | constructor].
  + apply pairwise_disjoint_of_extents.
    unfold scn_regs_a, stack_region, got_regionP, bcell_regionP, scn_ncalls_ra, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (rewrite V0; lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (rewrite V12; lia).
    rewrite (VB (A_OBJ 44) (VAL (A_OBJ 44)) E285) by (rewrite V44; unfold A_G_REC; lia).
    cbn [base_val]. rewrite Usp, V0, V12, V44.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, A_G_REC, OFF_NCALLS. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0. clear. intros.
    repeat split; lia.
  + exact HG.
- unfold sh_ok, scn_SH_e. apply Forall_nil.
Qed.


(* two readers that hold the same value at the same field agree on its bytes *)
Lemma scn_aval_same : forall (rd rd' : reader) a n v, aval_mem rd a n v -> aval_mem rd' a n v ->
forall x, a <= x < a + Z.of_nat n -> rd' x = rd x.
Proof.
intros rd rd' a n v H H' x Hx. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (H (Z.to_nat (x - a))), (H' (Z.to_nat (x - a))) by lia. reflexivity.
Qed.

(* the recorder's state over a reader that keeps g_rec, record.spill and the recorder's own blocks *)
Lemma scn_arep_keep : forall bl (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
 (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
arep_at bl rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl rd rd' R Q HR K.
pose proof HR as (S1 & S2 & S3 & HC & HA & HP & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
assert (KQ : forall pn, In pn (lay_blocks Q) ->
  In pn bl /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. destruct (scn_lay_facts _ _ _ _ _ _ pn HR Hpn) as (_ & _ & Hbl).
  split; [exact Hbl|]. intros i Hi. apply K. right; right. exists pn. split; [exact Hpn | lia]. }
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; left; exact Hx).
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + CALL_SIZE -> rd' x = rd x)
by (intros x Hx; apply K; right; left; unfold SC_SIZE, CALL_SIZE in *; lia).
assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
destruct (scn_rest_keep bl bl rd rd' A_G_REC R (l_answer Q) (l_reply Q) HA HP HX
  ltac:(intros x Hx; apply KG; unfold REC_SIZE; lia) KO) as (RA & RP & RX).
unfold arep_at.
refine (conj S1 (conj S2 (conj S3 (conj _ (conj RA (conj RP (conj RX HW))))))).
unfold ag1_calls.
refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
- apply (scn_aval_keep rd); [exact C3 | intros x Hx; apply KG; unfold OFF_NCALLS, REC_SIZE in *; lia].
- intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
  apply (scn_call_keep bl bl rd rd'); [exact Hc | |].
  + intros x Hx. apply KG. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
  + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
    exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
- apply (scn_call_keep bl bl rd rd'); [exact C5 | exact KS |].
  intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
Qed.

(* the recorder's state over a reader that keeps g_rec (except ncalls), record.spill and the blocks, with the
   ncalls value supplied (the spill arm does not write ncalls but the frame-of allows it to differ) *)
Lemma scn_arep_keep_nc : forall bl (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
aval_mem rd' (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R))) ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE /\ ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4))
 \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
 (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
arep_at bl rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl rd rd' R Q HR HNC K.
pose proof HR as (S1 & S2 & S3 & HC & HA & HP & HX & HW).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
assert (KQ : forall pn, In pn (lay_blocks Q) ->
  In pn bl /\ forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. destruct (scn_lay_facts _ _ _ _ _ _ pn HR Hpn) as (_ & _ & Hbl).
  split; [exact Hbl|]. intros i Hi. apply K. right; right. exists pn. split; [exact Hpn | lia]. }
assert (KG : forall x, A_G_REC <= x < A_G_REC + REC_SIZE ->
  ~ (A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4) -> rd' x = rd x)
by (intros x Hx Hnc; apply K; left; split; [exact Hx | exact Hnc]).
assert (KS : forall x, A_REC_SPILL <= x < A_REC_SPILL + CALL_SIZE -> rd' x = rd x)
by (intros x Hx; apply K; right; left; unfold SC_SIZE, CALL_SIZE in *; lia).
assert (KO : forall pn, In pn (oblk (l_answer Q) ++ oblk (l_reply Q)) -> In pn bl /\
  forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)).
{ intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
destruct (scn_rest_keep bl bl rd rd' A_G_REC R (l_answer Q) (l_reply Q) HA HP HX
  ltac:(intros x Hx; apply KG; unfold REC_SIZE, OFF_NCALLS in *; lia) KO) as (RA & RP & RX).
unfold arep_at.
refine (conj S1 (conj S2 (conj S3 (conj _ (conj RA (conj RP (conj RX HW))))))).
unfold ag1_calls.
refine (conj C1 (conj C2 (conj HNC (conj _ (conj _ C6))))).
- intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
  assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
  apply (scn_call_keep bl bl rd rd'); [exact Hc | |].
  + intros x Hx. apply KG; unfold OFF_CALLS, CALL_SIZE, REC_SIZE, OFF_NCALLS in *; lia.
  + intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. left. apply in_concat.
    exists P. split; [eapply nth_error_In; exact EP | exact Hpn].
- apply (scn_call_keep bl bl rd rd'); [exact C5 | exact KS |].
  intros pn Hpn. apply KQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
Qed.

(* a recorder-owned block byte is not a byte of g_rec's ncalls field (blocks are off-image, g_rec is on it) *)
Lemma scn_block_not_grec : forall ly S (W : world SEGS) mem md p k a, AR SEGS B ly S W mem md ->
In (p, k) (ablocks B ly S) -> p <= a < p + k -> ~ (A_G_REC <= a < A_G_REC + REC_SIZE).
Proof.
intros ly S W mem md p k a HAR Hin Ha Hg.
pose proof (req_size_pos k ltac:(destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & _ & _ & _ & _ & _ & H); lia)) as [_ Hreq].
destruct (al_client_img _ _ LAWS ly S W mem md a HAR
  ltac:(left; exists p, k; split; [exact Hin | lia])) as [_ Hni].
apply Hni. apply (cif_prog_img a). exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
cbn [fst snd]. unfold REC_SIZE in Hg. lia.
Qed.

(* the recorder's own blocks are live *)
Lemma scn_rep_bl : forall ly S (rd : reader) R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HR & HO) Hin. exact (scn_lay_in_bl _ _ _ _ _ _ pn HR (proj1 (HO pn) Hin)). Qed.

Lemma scn_bsum_nonneg : forall l : list (Z * Z), (forall pn, In pn l -> 0 <= snd pn) -> 0 <= bsum l.
Proof.
induction l as [|b l IH]; intros H; [cbn; lia|]. rewrite bsum_cons.
pose proof (H b (or_introl eq_refl)). pose proof (IH (fun pn Hp => H pn (or_intror Hp))). lia.
Qed.

(* every byte the recorder may name lies below the allocator's ceiling, so below the stack *)
Lemma scn_rec_low : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) a, AR SEGS B ly S W mem md ->
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
 exists pn, In pn (ablocks B ly S) /\ In pn O /\ fst pn <= a < fst pn + snd pn) ->
0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR Ha. pose proof asan_consts as (C1 & _).
destruct Ha as [Ha|[Ha|([p k] & Hin & _ & Ha)]];
[unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq]. cbn [fst snd] in Ha. lia.
Qed.

(* the bytes rec_calls_free(&record.spill, 1) may write *)
Lemma scn_rcf_fp_inv : forall P a, inFP (rcf_fp A_REC_SPILL [P]) a ->
(A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) \/
exists p k, In (p, k) P /\ p <= a < p + req_size k.
Proof.
intros P a Ha. unfold rcf_fp in Ha. cbn [length seq map concat app] in Ha. rewrite app_nil_r in Ha.
apply inFP_cons in Ha as [Ha|Ha]; [left; unfold CALL_SIZE in Ha; lia | right].
exact (inFP_ablocks_fp_inv P a Ha).
Qed.

Lemma scn_aview_mod : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte, mrestrict.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the read-only view of the entry holds at a state that differs from the entry only in [lo, hi) above the image
   (arg_line.v's al_arod_kept) *)
Lemma scn_arod_kept : forall (W : world SEGS) mem mem' lo hi,
arodata_okP SEGS RLO RHI B (rdW W mem) -> kept_out (rdW W mem) (rdW W mem') lo hi ->
(forall a, lo <= a < hi -> rdW W mem a <> None) -> kLowMemEnd <= lo -> hi <= 2 ^ 64 ->
arodata_okP SEGS RLO RHI B (rdW W mem').
Proof.
intros W mem mem' lo hi HR HK Hv Hlo Hhi a Hro Ho He.
pose proof (HR a Hro Ho He) as Ha.
set (a' := a mod 2 ^ 64). pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha'. fold a' in Ha'.
assert (Er : seg_rom SEGS (Z_to_bv 64 a) = seg_rom SEGS (Z_to_bv 64 a')).
{ f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  subst a'. rewrite Z.mod_mod by lia. reflexivity. }
rewrite scn_aview_mod in Ha |- *. fold a' in Ha |- *. rewrite Er in Ha |- *.
destruct (Z_lt_le_dec a' lo) as [Hl | Hl]; [|destruct (Z_lt_le_dec a' hi) as [Hh | Hh]].
- rewrite (HK a' Ha') by lia. exact Ha.
- exfalso. apply (Hv a' ltac:(lia)). rewrite Ha.
  rewrite (seg_rom_none SEGS a' Ha'); [reflexivity|].
  intros Hi. pose proof (pa_segs_low a' Hi). lia.
- rewrite (HK a' Ha') by lia. exact Ha.
Qed.

(* the frame the prologue wrote: the nine saved registers at their slots (cgif's cl_frame_of_region0) *)
Lemma scn_frame_of_region : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) wlo whi,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-80) 0 wlo whi
[YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
scn_frame m sp0 regs.
Proof.
intros E m sp0 regs wlo whi HR Hsp HE j r Hj.
assert (Hj9 : (j < 9)%nat) by (apply (proj1 (nth_error_Some scn_saved j)); rewrite Hj; discriminate).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia. change 8%nat with (N.to_nat 8).
do 9 (destruct j as [|j];
[ cbn in Hj; injection Hj as <-;
lazymatch goal with |- val_mem _ _ (_ + ?od) _ (bv_unsigned (getr _ (Z_to_bv 5 ?R))) =>
let od' := eval vm_compute in od in change od with od';
let n := eval vm_compute in (Z.to_nat R) in
apply (field_of_region E m 2 sp0 _ (-80) 0 wlo whi od' 8 (SOff n 0) _ HR Hsp);
[ cbn; tauto
| cbn [sv_denot]; rewrite (HE n (Z_to_bv 5 R) eq_refl), Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
| exact HRr
| cbn; lia ] end
| ]). cbn in Hj9. lia.
Qed.

(* the bytes of g_rec.ncalls are footprint bytes of the program's statics *)
Lemma scn_awr_ncalls : forall STK sp0 O bl0 blc fr0 ly own a,
A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4 ->
awr_byte SEGS B STK sp0 (scn_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Ha.
assert (HPG : inFP cmd_PG a).
{ exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS in Ha; lia]. }
do 4 right. left. split; [|split; [exact (HPROG B HB a HPG) | exact (cif_prog_img a HPG)]].
unfold scn_FP. apply inFP_cons. left. exact Ha.
Qed.

Lemma scn_sig_rcf : SIGMA CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof.
rewrite (SIGP CS_rec_calls_free); [reflexivity|].
cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]).
Qed.

(* rec_calls_free's post (rec_calls_free_c.v:98-122) at a call state, the K of cl_callS_wide *)
Definition scn_rcf_K (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
(c : Z) (ps : list (list (Z * Z))) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ concat ps) /\
 (forall i, (i < length ps)%nat -> aval_mem (rdW W' mem') (c + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 0) /\
 (forall j, 0 <= j < CALL_SIZE * Z.of_nat (length ps) -> ~ PRcf.nargs_field c (length ps) (c + j) ->
    rdW W' mem' (c + j) = rdW W mem (c + j)) /\
 (forall p n i, In (p, n) (ablocks B ly' S') -> 0 <= i < n -> rdW W' mem' (p + i) = rdW W mem (p + i)) /\
 (forall R Q, arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
    c = A_G_REC + OFF_CALLS -> ps = l_calls Q ->
    rec_repA B ly' S' (rdW W' mem') (set_calls R (rcf_cleared (r_calls R)))
      (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q))) /\
 (forall R Q, arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
    c = A_REC_SPILL -> ps = [l_spill Q] ->
    rec_repA B ly' S' (rdW W' mem') (set_spill R (fst (r_spill R), []))
      (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q))) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O ->
    iv_apart c (CALL_SIZE * Z.of_nat (length ps)) A_G_REC REC_SIZE ->
    iv_apart c (CALL_SIZE * Z.of_nat (length ps)) A_REC_SPILL SC_SIZE ->
    (forall pn, In pn (concat ps) -> ~ In pn O) ->
    rec_repA B ly' S' (rdW W' mem') R O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_REC_CALLS_FREE /\
 mo_le MT S S' (XM_REC_CALLS_FREE MT ps).

Definition scn_win (sp0 a : Z) : Prop :=
sp0 - 80 <= a < sp0 \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4.

Local Ltac scn_awr Usp U285 :=
awr_ok_tac; [exact Usp | eapply awr_ok_cons_gen; [reflexivity | exact U285 | | apply awr_ok_nil];
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply scn_awr_ncalls; unfold OFF_NCALLS; lia].
Local Ltac scn_kept HFr Zs Usp U285 :=
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zs HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a" in
        let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
        intros b wlo whi a' Hin Hr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr;
                rewrite ?Usp, ?U285 in Hr; unfold scn_win, OFF_NCALLS; lia|]); destruct Hin)).
Local Ltac scn_set_md mdv :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.

Lemma scn_nodup_pw : forall l : list (Z * Z), (forall pn, In pn l -> 1 <= req_size (snd pn)) ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hs Hp; [constructor|]. cbn [map pairwise] in Hp. destruct Hp as [Hf Hp].
constructor.
- intros Hin. rewrite Forall_forall in Hf.
  specialize (Hf (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) l x Hin)).
  pose proof (Hs x (or_introl eq_refl)). unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
- apply IH; [intros pn H; apply Hs; right; exact H | exact Hp].
Qed.

Lemma scn_nodup_app_disj : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|].
cbn [app] in H. apply List.NoDup_cons_iff in H as [Hy H]. destruct H1 as [<-|H1].
- apply Hy. apply in_or_app. right. exact H2.
- exact (IH l2 x H H1 H2).
Qed.

Lemma scn_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
assert (HS1 : forall pn, In pn (ablocks B ly S) -> 1 <= req_size (snd pn)).
{ intros [p k] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (_ & _ & _ & _ & _ & _ & Hk).
  exact (proj1 (req_size_pos k ltac:(lia))). }
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
apply pairwise_app_l in Hp as [Hp _].
exact (scn_nodup_pw _ HS1 Hp).
Qed.

Lemma scn_seg_a : SCN_B_stmt B MT ->
forall ly S W (regs : bvmap 5 word) mem md ch (pv pl pa pb : Z) verb line port_a port_b (R : rstate) (O : list (Z * Z)),
let t := snd (sup_connect_m R verb line port_a port_b) in
scn_pre B MT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_connect) regs mem md)
  (scn_post B MT ly S W regs mem md verb line port_a port_b R O t).
Proof.
intros HBS ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t HPRE.
pose proof HPRE as (HFN & HFRM & Hfr8 & HROD & HRO & H10 & Hpv & H11 & Hpl & H12 & Hpa & H13 & Hpb & HSA & HTV &
  HSL & HSPA & HSPB & HREP & HEV & HLIVE & HMOK).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (FFS : SUP_CONNECT_STK = 16592) by reflexivity.
pose proof HREP as (Q0 & HRQ & HOQ).
pose proof HRQ as (_ & _ & _ & (Hn16 & HlenQ & Hncalls & HCALLS & HSPILL & HSPLEN) & _).
assert (HSF : rec_spill_frees R =
  if Nat.ltb (length (r_calls R)) 16 then 0 else Z.of_nat (length (snd (r_spill R)))) by reflexivity.
set (n := length (r_calls R)) in *.
destruct (scn_entry_a W ly S regs mem md ch (Z.of_nat n) HFN ltac:(lia) Hncalls) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_CONNECT_STK (scn_FP O) ly S W regs mem md ch HFN) as HJ.
remember (Eimg (Ereg regs (scn_xa (Z.of_nat n)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
by (intros k r Hk; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
    rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 SCN_SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat n))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
clear HE.
assert (U285 : bv_unsigned (ew E 285%nat) = A_G_REC).
{ rewrite (HEI 285%nat ltac:(unfold A_TEXT, A_LIM; lia)). change (VAL 285%nat) with (VAL (A_OBJ 44)).
  exact (scn_obj44 VOBJS). }
assert (U292 : bv_unsigned (ew E 292%nat) = A_REC_SPILL).
{ rewrite (HEI 292%nat ltac:(unfold A_TEXT, A_LIM; lia)). change (VAL 292%nat) with (VAL (A_OBJ 51)).
  exact (scn_obj51 VOBJS). }
assert (E292 : ew E 292%nat = Z_to_bv 64 A_REC_SPILL)
by (apply bv_eq; rewrite U292, unsigned_lit_small by (unfold A_REC_SPILL; lia); reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (Hvis : forall a, spZ regs - SUP_CONNECT_STK <= a < spZ regs -> rdW W mem a <> None)
by (intros a Ha; apply (aview_some_of_apresent SEGS); apply Hpres; exact Ha).
unfold cfg_at. change (w64 (BASE + AF_sup_connect)) with (Z_to_bv 64 (BASE + AF_sup_connect)).
unfold scn_ss_a, scn_regs_a in HS.
(* 0x8ad20 .. 0x8ad74: the frame, s1/s3/s4/s5 := the arguments, a2 := g_rec.ncalls (atom 33), s6 := the shadow base *)
paj_run_tok RUN HS HJ SHOK scn_Bspan.
{ scn_awr Usp U285. }
scn_set_md mdv1.
scn_kept HFr (scn_win (spZ regs)) Usp U285. rename H into KO1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK scn_Bspan.
- (* ncalls <> 16: the table arm, 0x8ad90 .. 0x8ada8 *)
  assert (Hlt : (n < 16)%nat).
  { rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc.
    rewrite E33 in Hc. rewrite !unsigned_lit_small in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK scn_Bspan SCN_JOIN.
  { scn_awr Usp U285. }
  scn_set_md mdv2.
  scn_kept HFr (scn_win (spZ regs)) Usp U285. rename H into KO2.
  clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22.
  set (c := A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n).
  assert (HP8 : getr (ms_regs ms0) 8 = w64 c).
  { assert (Hmul : mul_div M_MUL (ew E 33) (Z_to_bv 64 56) = Z_to_bv 64 (Z.of_nat n * 56)).
    { apply bv_eq. rewrite mul_div_unsigned, E33. cbn [zmd_raw].
      rewrite (unsigned_lit_small (Z.of_nat n)) by lia.
      change (bv_unsigned (Z_to_bv 64 56)) with 56. rewrite Z_to_bv_unsigned. reflexivity. }
    assert (E285z : ew E 285%nat = Z_to_bv 64 A_G_REC)
      by (apply bv_eq; rewrite U285, unsigned_lit_small by (unfold A_G_REC; lia); reflexivity).
    rewrite P8, Hmul, E285z.
    rewrite (alu_add_small (Z.of_nat n * 56) 16 ltac:(lia) ltac:(lia) ltac:(unfold M64; lia)).
    rewrite (alu_add_small (Z.of_nat n * 56 + 16) A_G_REC ltac:(lia) ltac:(unfold A_G_REC; lia)
      ltac:(unfold A_G_REC, M64; lia)).
    unfold w64, c. f_equal. unfold A_G_REC, OFF_CALLS, CALL_SIZE. lia. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 _ HS eq_refl) as HR0;
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 _ HS eq_refl) as HR3 end.
  cbn [ms_mem restrict mkst] in HR0, HR3.

  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rJ _ ?mJ _; cfg_model := ?dJ |} _ =>
    apply (HBS ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O ly S W rJ mJ dJ 0 c O HPRE) end.
  unfold scn_mid.
  split; [exact HJ|].
  split; [rewrite HSF; destruct (Nat.ltb n 16); lia|].
  split; [left; exists (Z.of_nat n); split; [unfold REC_CALLS_MAX; lia | reflexivity]|].
  split; [left; split; [exact Hlt | reflexivity]|].
  split.
  { unfold scn_regs_join.
    split; [unfold spZ at 1; rewrite P2, Usp, unsigned_lit_small by lia; lia|].
    split; [exact HP8|].
    split; [rewrite P22, E32; reflexivity|].
    split; [rewrite P21; apply EE; reflexivity|].
    split; [rewrite P20; apply EE; reflexivity|].
    split; [rewrite P19; apply EE; reflexivity|].
    split; [rewrite P9; apply EE; reflexivity|].
    split; [rewrite P3; apply EE; reflexivity|].
    split; [rewrite P4; apply EE; reflexivity|].
    intros r Hr. assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr4 as [-> | [-> | [-> | ->]]];
    rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs restrict mkst];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
      let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity. }
  split; [exact (scn_frame_of_region E _ (spZ regs) regs _ _ HR0 Usp EE)|].
  split.
  { intros rd' Hrd Hfn Hnargs.
    assert (HNC : aval_mem (rdW W (ms_mem ms0)) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat n + 1)).
    { apply scn_aval_of_val_mem.
      exact (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) (Z.of_nat n + 1) HR3 U285
        ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity)
        ltac:(cbn; lia) ltac:(cbn; lia)). }
    apply (scn_record_lt_rep B ly S (rdW W mem) rd' R O n c REC_CONNECT HREP eq_refl Hlt
      ltac:(unfold REC_CONNECT, REC_FN_COUNT; lia) eq_refl).
    - apply (scn_aval_keep (rdW W (ms_mem ms0))); [exact HNC|]. intros x Hx. apply Hrd.
      unfold c, A_G_REC, OFF_CALLS, CALL_SIZE, OFF_NCALLS in *. lia.
    - exact Hfn.
    - exact Hnargs.
    - intros a Ha Hnc Hns. rewrite (Hrd a Hns).
      pose proof (scn_rec_low ly S W mem md O a HAR Ha) as Hlow.
      rewrite (KO2 a) by (try unfold scn_win; lia).
      apply KO1; [lia | unfold scn_win; lia]. }
  split; [intros pn Hpn; exact Hpn|].
  split; [intros pn Hpn; exact (scn_rep_bl ly S _ R O pn HREP Hpn)|].
  split; [intros pn _ Hpn; exact Hpn|].
  split; [intros pn Hpn; exact Hpn|].
  split; [intros pn Hpn _; exact Hpn|].
  split; [reflexivity|]. split; [lia|].
  replace (rec_spill_frees R * mo_free MT) with 0
    by (rewrite HSF; replace (Nat.ltb n 16) with true by (symmetry; apply Nat.ltb_lt; exact Hlt); lia).
  exact (mle_start MT S MTL).
- (* ncalls = 16: the spill arm, 0x8ad78 .. 0x8ad88 *)
  assert (H16 : n = 16%nat).
  { rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc.
    rewrite E33 in Hc. rewrite !unsigned_lit_small in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia. }
  assert (Hlen16 : length (r_calls R) = 16%nat) by (rewrite <- H16; reflexivity).
  paj_run_tok RUN HS HJ SHOK scn_Bspan.
  { scn_awr Usp U285. }
  scn_set_md mdv2.
  scn_kept HFr (scn_win (spZ regs)) Usp U285. rename H into KO2.
  clear HF HFr HG.
  assert (KOcall : forall a, 0 <= a < 2 ^ 64 -> ~ scn_win (spZ regs) a -> rdW W (ms_mem ms0) a = rdW W mem a)
    by (intros a Ha Hw; rewrite (KO2 a Ha Hw); exact (KO1 a Ha Hw)).
  (* the spill byte-ranges (g_rec body, record.spill, recorder blocks) are below alloc_ceiling, so outside the
     frame window, and outside ncalls (M2 / off-image), hence kept by KOcall *)
  assert (KOrec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
    (exists pn, In pn (ablocks B ly S) /\ In pn O /\ fst pn <= a < fst pn + snd pn) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem ms0) a = rdW W mem a).
  { intros a Ha Hnc. pose proof (scn_rec_low ly S W mem md O a HAR Ha) as Hlow.
    apply KOcall; [unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *; lia|].
    unfold scn_win. intros [Hf | Hn]; [lia | exact (Hnc Hn)]. }
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  pmkst HS.
  assert (Hsp2 : spZ (ms_regs ms0) = spZ regs + -80)
    by (unfold spZ at 1; rewrite P2; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (rewrite Usp; lia); rewrite Usp; reflexivity).
  assert (P10' : getr (ms_regs ms0) 10 = w64 A_REC_SPILL) by (rewrite P10, E292; reflexivity).
  assert (P11' : getr (ms_regs ms0) 11 = w64 1) by (exact P11).
  (* arodata holds at the call state: no read-only byte is written (frame is above the image, ncalls is not RO) *)
  assert (Hro_lo : forall a, in_roP SEGS RLO RHI a -> 0 <= a < kLowMemEnd).
  { intros a [(s & Hs & _ & Hr) | Hr].
    - apply pa_segs_low. exists s. split; [exact Hs | exact Hr].
    - unfold CMD_RLO, CMD_RHI in Hr. rewrite C5. lia. }
  assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms0))).
  { intros a Hro Ho He. pose proof (Hro_lo a Hro) as Hlo.
    rewrite (KOcall a ltac:(lia)); [exact (HROD a Hro Ho He)|].
    unfold scn_win. intros [Hf | Hn].
    - pose proof C1 as Hac. lia.
    - apply (RPG a); [exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS in Hn; lia] | exact Hro]. }
  (* the spill call record (acall_at) at the call-state reader, from HSPILL kept by KOcall *)
  assert (HSPILLc : acall_at (ablocks B ly S) (rdW W (ms_mem ms0)) A_REC_SPILL (r_spill R) (l_spill Q0)).
  { apply (scn_call_keep (ablocks B ly S) (ablocks B ly S) (rdW W mem) (rdW W (ms_mem ms0))); [exact HSPILL | |].
    - intros x Hx. apply KOrec; [right; left; unfold SC_SIZE, CALL_SIZE in *; lia|].
      unfold A_G_REC, A_REC_SPILL, OFF_NCALLS in *; lia.
    - intros [pp kk] Hpn. destruct (scn_call_pn _ _ _ _ _ _ HSPILL Hpn) as (Hpn0 & Hpn1 & Hpnbl).
      split; [exact Hpnbl|]. intros i Hi. cbn [fst snd] in *. apply KOrec.
      + right; right. exists (pp, kk). split; [exact Hpnbl|]. split; [| cbn [fst snd]; lia].
        apply (proj2 (HOQ (pp, kk))). unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn.
      + intros Hnc. apply (scn_block_not_grec ly S W mem md pp kk (pp + i) HAR Hpnbl ltac:(cbn [fst snd]; lia)).
        unfold OFF_NCALLS, REC_SIZE in *. lia. }
  pose proof HSPILLc as (Hsfn & Hsle & HsL & Hsb0 & Hsb1 & Hsnd & Hsk).
  assert (HRSF : rec_spill_frees R = Z.of_nat (length (l_spill Q0)))
    by (rewrite HSF; replace (Nat.ltb n 16) with false by (symmetry; apply Nat.ltb_ge; lia); rewrite HsL; reflexivity).
  (* ncalls value at the call state (the spill arm does not store it) *)
  assert (HNCcall : aval_mem (rdW W (ms_mem ms0)) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)))).
  { lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
      pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 _ HS eq_refl) as HR3c end.
    cbn [ms_mem restrict mkst] in HR3c.
    apply scn_aval_of_val_mem. unfold OFF_NCALLS.
    exact (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33 0) (Z.of_nat (length (r_calls R))) HR3c U285
      ltac:(cbn; tauto)
      ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (HARcall : arep_at (ablocks B ly S) (rdW W (ms_mem ms0)) A_G_REC A_REC_SPILL R Q0).
  { apply (scn_arep_keep_nc (ablocks B ly S) (rdW W mem) (rdW W (ms_mem ms0)) R Q0 HRQ HNCcall).
    intros a [[Hg Hnc] | [Hs | (pn & Hpn & Ha)]].
    - apply KOrec; [left; exact Hg | exact Hnc].
    - apply KOrec; [right; left; exact Hs | unfold A_G_REC, A_REC_SPILL, OFF_NCALLS in *; lia].
    - destruct pn as [pp kk]. cbn [fst snd] in Ha.
      pose proof (scn_lay_in_bl _ _ _ _ _ _ (pp, kk) HRQ Hpn) as Hbl.
      apply KOrec.
      + right; right. exists (pp, kk). split; [exact Hbl|]. split; [apply (proj2 (HOQ (pp, kk))); exact Hpn | cbn [fst snd]; lia].
      + intros Hnc. apply (scn_block_not_grec ly S W mem md pp kk a HAR Hbl Ha).
        unfold OFF_NCALLS, REC_SIZE in *. lia. }
  (* premises of rec_calls_free *)
  assert (Hslots : forall i P, nth_error [l_spill Q0] i = Some P ->
    (length P <= 6)%nat /\
    aval_mem (rdW W (ms_mem ms0)) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
    forall a pn, nth_error P a = Some pn ->
      aval_mem (rdW W (ms_mem ms0)) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
      In pn (ablocks B ly S)).
  { intros i P Hi. destruct i; [|destruct i; discriminate]. cbn [nth_error] in Hi. injection Hi as <-.
    split; [rewrite HsL; exact Hsle|].
    split; [replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS) by (cbn; lia);
            rewrite HsL; exact Hsb1|].
    intros a pn Hpn.
    assert (Ha' : (a < length (snd (r_spill R)))%nat) by (rewrite <- HsL; apply nth_error_Some; rewrite Hpn; discriminate).
    destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (Hsk a s pn Es Hpn) as (Hav & _ & Hin & _).
    split; [replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat a)
              with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) by (cbn; lia); exact Hav | exact Hin]. }
  assert (Hnodup : NoDup (map fst (concat [l_spill Q0]))) by (cbn [concat]; rewrite app_nil_r; exact Hsnd).
  assert (HEVB : st_nev S + EV_REC_CALLS_FREE [l_spill Q0] <= EV_MAX).
  { assert (Hd : EV_REC_CALLS_FREE [l_spill Q0] <= EV_SUP_CONNECT R).
    { unfold EV_REC_CALLS_FREE, EV_SUP_CONNECT. cbn [concat]. rewrite app_nil_r, <- HRSF.
      assert (Hc6 : 0 <= EV_XSTRDUP + EV_ARG_LINE + EV_XSTRDUP + EV_XSTRDUP + EV_ANSWER) by (vm_compute; intro; discriminate).
      lia. }
    lia. }
  assert (HMOKB : mo_ok MT S (XM_REC_CALLS_FREE MT [l_spill Q0])).
  { apply (mo_ok_le MT MTL S (XM_REC_CALLS_FREE MT [l_spill Q0]) (XM_SUP_CONNECT MT R verb line port_a port_b t) HMOK).
    unfold XM_REC_CALLS_FREE, XM_SUP_CONNECT. cbn [concat]. rewrite app_nil_r, <- HRSF.
    assert (Hx : 0 <= XM_XSTRDUP MT (sarg verb) + XM_ARG_LINE MT line + XM_XSTRDUP MT (sarg port_a) +
                 XM_XSTRDUP MT (sarg port_b) + XM_ANSWER MT t).
    { unfold XM_XSTRDUP, XM_ARG_LINE, XM_REC_CANONICAL, XM_ANSWER, XM_HAND_BACK.
      repeat apply Z.add_nonneg_nonneg;
        first [apply (mo_free_nonneg MT MTL) | apply (mo_malloc_nonneg MT MTL); lia]. }
    lia. }
  (* every byte rec_calls_free(&record.spill, 1) may write lies below alloc_ceiling, so below the stack window *)
  assert (HFP1 : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q0]) a -> a < alloc_ceiling).
  { intros a Hin. apply scn_rcf_fp_inv in Hin. destruct Hin as [Hn | (p & k & Hin & Hr)].
    - unfold CALL_OFF_NARGS, A_REC_SPILL in Hn. pose proof C1 as Hac. lia.
    - assert (HinO : In (p, k) O) by (apply (proj2 (HOQ (p, k))); unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hin).
      pose proof (scn_rep_bl ly S (rdW W mem) R O (p, k) HREP HinO) as Hinbl.
      destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hinbl) as (_ & _ & Hpc & _).
      lia. }
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W (ms_regs ms0) (ms_mem ms0) _ SUP_CONNECT_STK (spZ regs) (scn_FP O)
      ly S W mem md [] ly S mdv2 0 REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q0])
      (EV_REC_CALLS_FREE [l_spill Q0]) (-80) (Z_to_bv 64 (BASE + 18600)) []
      (scn_rcf_K ly S W (ms_mem ms0) A_REC_SPILL [l_spill Q0]) HJ Hsp2).
    - reflexivity.
    - lia.
    - unfold REC_CALLS_FREE_STK, ASTACK; lia.
    - rewrite FFS; unfold REC_CALLS_FREE_STK, ASTACK; lia.
    - rewrite P3, (EE 3%nat 3%bv eq_refl); exact Hgp.
    - rewrite P4, (EE 4%nat 4%bv eq_refl); exact Htp.
    - exact P1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - apply achain_low. unfold s0Z. rewrite P8, E292, unsigned_lit_small by (unfold A_REC_SPILL; lia).
      unfold A_REC_SPILL. lia.
    - intros HPRE2. rewrite scn_sig_rcf.
      eapply SRr_mono.
      { apply (TREC_CALLS_FREE fx ly S W (ms_regs ms0) (ms_mem ms0) mdv2 [] A_REC_SPILL [l_spill Q0] HPRE2 HROD2
          P10' P11' ltac:(cbn [length]; lia)
          ltac:(right; left; split; [unfold A_REC_SPILL; lia | cbn [length]; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE; lia])
          (eq_refl : A_REC_SPILL mod 8 = 0)
          Hslots Hnodup HEVB HMOKB). }
      cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HK3).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite P1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3 | exact HK3].
    - intros a Ha. apply scn_rcf_fp_inv in Ha. destruct Ha as [Hn | (p & k & Hin & Hr)].
      + do 4 right. left. assert (HPG : inFP cmd_PG a)
          by (exists (A_REC_SPILL, A_REC_SPILL + 56); split; [right; left; reflexivity | cbn [fst snd]; unfold CALL_OFF_NARGS in Hn; lia]).
        split; [|split; [exact (HPROG B HB a HPG) | exact (cif_prog_img a HPG)]].
        unfold scn_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. right.
        apply inFP_cons. left. unfold CALL_OFF_NARGS, SC_SIZE in *. lia.
      + assert (HinO : In (p, k) O) by (apply (proj2 (HOQ (p, k))); unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hin).
        pose proof (scn_rep_bl ly S (rdW W mem) R O (p, k) HREP HinO) as Hinbl.
        right. left. split.
        * unfold scn_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. right.
          apply inFP_cons. right. replace a with (p + (a - p)) by lia.
          apply (inFP_ablocks_fp O p k (a - p) HinO). lia.
        * exists p, k. split; [exact Hinbl | lia].
    - intros ly2 S2 W2 regs2 mem2 md2 _ a Hin Hw1 _. exfalso. pose proof (HFP1 a Hin). lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
  pose proof HK2 as (HKperm & _ & _ & _ & _ & HKsp & _ & HKbb & HKmo).
  pose proof (HKsp R Q0 HARcall eq_refl eq_refl) as HREP2.
  set (O1 := concat (l_calls Q0) ++ oblk (l_answer Q0) ++ oblk (l_reply Q0)) in HREP2.
  clear HK2 HKsp.
  (* back at 0x8ad8c: only the frame is kept (rec_calls_free's footprint is below alloc_ceiling) *)
  jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?T -> _ => assert (HRK : T); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    eapply (region_kept_stack_sub SEGS B E REC_CALLS_FREE_STK (spZ regs + -80) (rcf_fp A_REC_SPILL [l_spill Q0])
      ly S W (ms_mem ms0) mdv2 ly2 S2 W2 mem2 md2 (EV_REC_CALLS_FREE [l_spill Q0]) 2 (-80) 0 (-80) 0 _ (spZ regs)
      SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] _ HJc2 HJ2 Usp);
    [lia | rewrite FFS; lia | lia | lia | lia |].
    intros a Ha Hin. pose proof (HFP1 a Hin). lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 64 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD2 : forall n0, (n0 < 64)%nat -> ew E2 n0 = ew E n0)
    by (intros n0 Hn0; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn0).
  assert (E2_292 : ew E2 292%nat = Z_to_bv 64 A_REC_SPILL) by (rewrite HE2, ew_havoc_above; [exact E292 | cbv; lia]).
  clear HE2.
  assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
  assert (EE2 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E2 k = getr regs r).
  { intros k0 r Hk0. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
    rewrite OLD2 by lia. exact (EE k0 r Hk0). }
  assert (SHOK2 : sh_ok SEGS scn_Bx_e scn_SH_e E2 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, scn_SH_e; apply Forall_nil).
  (* 0x8ad8c: j 0x8adac, the join *)
  paj_run_to_tok RUNTO HS HJ2 SHOK2 scn_Bspan SCN_JOIN.
  { awr_ok_tac; exact Usp2. }
  scn_set_md mdv3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msJ end.
  pose proof (kept_of_frame (segs:=SEGS) E2 _ (w_H W2) mem2 (ms_mem msJ) (fun a => spZ regs - 80 <= a < spZ regs) HFr
    ltac:(intros b wlo whi a' Hin Hrr; cbv beta; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2 in Hrr; lia|]);
          destruct Hin)) as KEEPJ.
  clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    pose proof (st_ok_pi_region_nth E2 ssx (restrict _ msx) 0 _ HS eq_refl) as HR0 end.
  cbn [ms_mem restrict mkst] in HR0.
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfr2 & _).
  assert (HND2 : List.NoDup (ablocks B ly2 S2 ++ concat [l_spill Q0]))
    by (eapply Permutation_NoDup; [exact HKperm | exact (scn_ablocks_nodup ly S W mem md HAR)]).
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rJ _ ?mJ _; cfg_model := ?dJ |} _ =>
    apply (HBS ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O ly2 S2 W2 rJ mJ dJ
      (EV_REC_CALLS_FREE [l_spill Q0]) A_REC_SPILL O1 HPRE) end.
  unfold scn_mid.
  split; [exact HJ2|].
  split; [rewrite HRSF; unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; lia|].
  split; [right; reflexivity|].
  split; [right; split; [lia | reflexivity]|].
  split.
  { unfold scn_regs_join.
    split; [unfold spZ at 1; rewrite Q2, Usp2, unsigned_lit_small by lia; lia|].
    split; [rewrite Q8, E2_292; reflexivity|].
    split; [rewrite Q22, OLD2 by lia; exact E32|].
    split; [rewrite Q21; apply EE2; reflexivity|].
    split; [rewrite Q20; apply EE2; reflexivity|].
    split; [rewrite Q19; apply EE2; reflexivity|].
    split; [rewrite Q9; apply EE2; reflexivity|].
    split; [rewrite Q3; apply EE2; reflexivity|].
    split; [rewrite Q4; apply EE2; reflexivity|].
    intros r Hr. assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr4 as [-> | [-> | [-> | ->]]];
    rewrite (st_ok_pi_restrict_reg (w_H W2) E2 _ _ _ HS); cbn [ms_regs restrict mkst];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
      let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE2; reflexivity. }
  split; [exact (scn_frame_of_region E2 _ (spZ regs) regs _ _ HR0 Usp2 EE2)|].
  split.
  { intros rd' Hrd Hfn Hnargs.
    rewrite <- (scn_record_spill_eq R (fst (r_spill R), []) REC_CONNECT [] Hlen16).
    apply (scn_record_full_rep B ly2 S2 (rdW W2 mem2) rd' (set_spill R (fst (r_spill R), [])) O1 REC_CONNECT HREP2);
      [exact Hlen16 | reflexivity | unfold REC_CONNECT, REC_FN_COUNT; lia | exact Hfn | exact Hnargs |].
    intros a Ha Hns. rewrite (Hrd a Hns).
    pose proof (scn_rec_low ly2 S2 W2 (ms_mem msJ) mdv3 O1 a HAR2 Ha) as Hlow.
    apply KEEPJ; [lia | cbv beta; lia]. }
  split.
  { intros pn Hpn. apply (proj2 (HOQ pn)). unfold lay_blocks. unfold O1 in Hpn.
    apply in_app_or in Hpn as [Hp | Hp]; apply in_or_app; [left; exact Hp | right; apply in_or_app; right; exact Hp]. }
  split; [intros pn Hpn; exact (scn_rep_bl ly2 S2 _ _ O1 pn HREP2 Hpn)|].
  split.
  { intros pn Hb Ho. apply (proj1 (HOQ pn)) in Ho. unfold lay_blocks in Ho. unfold O1.
    apply in_app_or in Ho as [Hp | Hp]; [apply in_or_app; left; exact Hp|].
    apply in_app_or in Hp as [Hp | Hp]; [|apply in_or_app; right; exact Hp].
    exfalso. apply (scn_nodup_app_disj (ablocks B ly2 S2) (concat [l_spill Q0]) pn HND2 Hb).
    cbn [concat]. rewrite app_nil_r. exact Hp. }
  split; [intros pn Hpn; apply (Permutation_in pn (Permutation_sym HKperm)); apply in_or_app; left; exact Hpn|].
  split.
  { intros pn Hb Hno. apply (Permutation_in pn HKperm) in Hb. apply in_app_or in Hb as [Hb | Hb]; [exact Hb|].
    exfalso. apply Hno. apply (proj2 (HOQ pn)). unfold lay_blocks. cbn [concat] in Hb. rewrite app_nil_r in Hb.
    apply in_or_app; right; apply in_or_app; left; exact Hb. }
  split; [exact Hfr2|].
  split; [unfold LIVE_REC_CALLS_FREE in HKbb; lia|].
  rewrite HRSF. unfold XM_REC_CALLS_FREE in HKmo. cbn [concat] in HKmo. rewrite app_nil_r in HKmo. exact HKmo.
Qed.
End e.
End f.
End d.
