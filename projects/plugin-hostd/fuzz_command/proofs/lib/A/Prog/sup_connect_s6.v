(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: one part of sup_connect's ASan walk (plugin-hostd/fuzz_command),
   `sb_seg1 : SB2_stmt -> SB1_stmt`: the walk from the first meeting point 0x8ade8 to the second 0x8ae50 —
   xstrdup(verb or "(null)") at 0x8adec, the two stores c->nargs := 1 and c->args[0] := the copy,
   arg_line(c, line) at 0x8ae2c through the kit's wide call rule, and the null check of port_a, whose two
   arms meet at 0x8ae50.

   The states (sb_C1, sb_C2), the hand-over form (sb_cx, sb_env, sb_inv) and the statements SB1_stmt and
   SB2_stmt are sup_connect_s4.v's, and its helpers are used by name. The file also carries the seed of the
   second half at the join 0x8adac (`s6_seed`), which sup_connect_s7.v's `scn_seg_b` takes.

   The verb is the one argument the statement keeps in `astr_argA` form (sup_connect_c.v:96-100: it may be a
   read-only literal of the image, not only a block), so its xstrdup call does not go through s4's sb_xcall
   (whose `sb_xarg` has only the "(null)" and block arms) but through `s6_xcallA` here, which takes the
   astr_argA and the tail of the string as premises. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibF PaLibH PaCall PaNoChain PaArt CmdBase CmdRep CmdObj CmdZsh CmdAddr CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c rec_canonical_c hand_back_c xstrdup_c arg_line_c answer_c sup_connect_c sup_connect_s0 sup_connect_s2
sup_connect_s4.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the reader at the join: the memory there, read inside the slot, and the entry's reader outside it. The
   join hands the recorder over as a fact about ANY reader that differs from the memory only inside the slot
   (scn_mid, sup_connect_s0.v:434-436); this is the one the walk then carries. *)
Lemma s6_w64 : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

Definition s6_rd (rd0 rd1 : reader) (c : Z) : reader :=
fun a => if ((c <=? a) && (a <? c + CALL_SIZE))%bool then rd1 a else rd0 a.
Lemma s6_rd_in : forall rd0 rd1 c a, c <= a < c + CALL_SIZE -> s6_rd rd0 rd1 c a = rd1 a.
Proof.
intros rd0 rd1 c a Ha. unfold s6_rd.
rewrite (proj2 (Z.leb_le c a)) by lia. rewrite (proj2 (Z.ltb_lt a (c + CALL_SIZE))) by lia. reflexivity.
Qed.
Lemma s6_rd_out : forall rd0 rd1 c a, ~ (c <= a < c + CALL_SIZE) -> s6_rd rd0 rd1 c a = rd0 a.
Proof.
intros rd0 rd1 c a Ha. unfold s6_rd.
destruct ((c <=? a) && (a <? c + CALL_SIZE))%bool eqn:E; [|reflexivity].
apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement pass fixed the read-only range (CmdGlob.v) *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callees' statements, at every FP state *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary record *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* interim CmdRecFacts facts, under CmdRecFacts.v's names; each becomes a lemma of
   lib/A/Prog/CmdRecFacts.v when statement pass 3 lands *)
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis PROG_WRITABLE : forall (m : word -> option byte) a, inFP cmd_PG a -> writable_at SEGS m a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).
Hypothesis cmd_tail_vis_at : forall ly S (W : world SEGS) mem md e, AR SEGS B ly S W mem md ->
In e cmd_ro_ends -> atail_vis SEGS W mem e.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
(* the read-only objects of the image lie in the read-only range (CmdRo.v's cmd_ro_in) *)
Hypothesis cmd_ro_in_img : cmd_ro_in (in_roP SEGS RLO RHI).
Hypothesis RRO : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS RLO RHI a.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* sup_connect_s4.v's helpers with this file's record, under short names *)
Let Lxcall := sb_xcall B MT TXSTRDUP HB LAWS SIGP cmd_ro_ok_of_aro cmd_tail_vis_at cmd_heap_tail_vis cmd_ro_in_img.
Let Larod := sb_arod B RRO RPG.
Let Lshok := sb_shok B HB LAWS.
Let Lslot_kept := sb_slot_kept B HB cif_prog_img PROG_WRITABLE.
Let Lawr_slot := sb_awr_slot B HB cif_prog_img.
Let Lcall_keep := sb_call_keep B HB cif_prog_img.

Ltac s6_name_ms HS nm :=
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into nm
| st_ok _ _ _ (restrict _ ?m) => rename m into nm
end.
Ltac s6_set_md nm :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (nm := mdx) in *; clearbody nm end.
(* the region at index i of the state hypothesis, in either the `st_ok_pi` or the unfolded `st_ok` form a
   symbolic run leaves behind *)
Ltac s6_region_nth HS Ex i r H :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as H
| st_ok _ _ ?ssx ?msx =>
  pose proof (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as H
end.
(* a run that stops at a branch or at a stop offset leaves the state hypothesis in the unfolded `st_ok` form,
   whose pc is the symbolic state's; fold it back into the `st_ok_pi` form the branch rule takes *)
Ltac s6_to_pi HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ _ _ => idtac
| st_ok ?sg ?Ex (setpc ?ssx _) ?msx => change (st_ok_pi sg VAL Ex ssx msx) in HS
end.

(* ---------------------------------------------------------------------------------------------- *)
(* Transport of the caller's strings from one state of the walk to the next                          *)

(* a read-only byte of the image is the image's byte at every state the walk reaches *)
Lemma s6_ro_keep : forall (W W' : world SEGS) mem mem' a,
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem') ->
in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W' mem' a = rdW W mem a.
Proof.
intros W W' mem mem' a H H' Hro Ho He. rewrite (H' a Hro Ho He), (H a Hro Ho He). reflexivity.
Qed.

(* a block the walk's footprint does not name keeps its bytes across a journal of the walk *)
Lemma s6_blk_keep : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k q m a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (scn_FP O) ly S W mem md own ly' S' W' mem' md' k ->
In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S') -> q <= a < q + m ->
rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k q m a HAR HOin HJ Hq Hno Hq' Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hq) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
replace a with (q + (a - q)) by lia. apply (F2 q m (a - q)); [exact Hq | exact Hq' | lia |].
intros Hin. destruct (sb_fp_cases O (q + (a - q)) Hin) as [Hpg | Hb].
- pose proof (sb_pg_range _ Hpg) as Hr.
  destruct (sb_in_blk_range B LAWS ly S W mem md q m (q + (a - q)) HAR Hq ltac:(lia)) as (H1 & H2 & H3).
  unfold A_G_REC, A_G_QUITTING in Hr. lia.
- destruct (inFP_ablocks_fp_inv _ _ Hb) as (p & n & Hpn & Hr).
  destruct (sb_pdec (p, n) (q, m)) as [Heq | Ne]; [rewrite Heq in Hpn; exact (Hno Hpn)|].
  pose proof (sep_blocks SEGS B LAWS ly S W mem md p n q m HAR (HOin _ Hpn) Hq Ne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* the statement's str_arg form of an argument, at a later state of the walk: the recorder's blocks are
   dropped from the exclusion list because the callee's own contract takes [] *)
Lemma s6_argA_move : forall ly S ly' S' (W W' : world SEGS) mem mem' O p v,
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem') ->
(forall q m a, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> q <= a < q + m -> rdW W' mem' a = rdW W mem a) ->
(forall q m, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S')) ->
astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) [] p v.
Proof.
intros ly S ly' S' W W' mem mem' O p [x|] HA HROD HROD' K KB; cbn [astr_argA] in HA |- *; [|exact HA].
cbv zeta in HA |- *. destruct HA as (Hp & Hs & Hlen & [(Hbl & Hap) | (Hro & Hc1 & Hc2 & He)]).
- destruct Hbl as (q & m & Hq & Hq1 & Hq2).
  assert (Hno : ~ In (q, m) O).
  { intros Hin. pose proof (proj1 (Forall_forall _ _) Hap _ Hin) as Hd.
    unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
  split; [exact Hp|].
  split; [apply (scn_str_keep (rdW W mem)); [exact Hs | intros i Hi; apply (K q m); [exact Hq | exact Hno | lia]]|].
  split; [exact Hlen|].
  left. split; [exists q, m; split; [exact (KB q m Hq Hno) | lia] | constructor].
- split; [exact Hp|].
  split; [apply (scn_str_keep (rdW W mem)); [exact Hs|]|].
  { intros i Hi. destruct (Hro i Hi) as (Hr & Ho & Hee).
    exact (s6_ro_keep W W' mem mem' (p + i) HROD HROD' Hr Ho Hee). }
  split; [exact Hlen|].
  right. split; [exact Hro | split; [exact Hc1 | split; [exact Hc2 | exact He]]].
Qed.

(* the same for the line and the two ports, which the statement hands over in block form *)
Lemma s6_sarg_move : forall ly S ly' S' (W : world SEGS) mem md (rd' : reader) O p v,
AR SEGS B ly S W mem md -> scn_sarg B ly S (rdW W mem) O p v ->
(forall q m a, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> q <= a < q + m -> rd' a = rdW W mem a) ->
(forall q m, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S')) ->
sb_sstr (ablocks B ly' S') rd' p v.
Proof.
intros ly S ly' S' W mem md rd' O p [x|] HAR HA K KB; cbn [scn_sarg sb_sstr] in HA |- *; [|exact HA].
unfold scn_blkarg in HA. destruct HA as ((q & m & Hq & Hq1 & Hq2) & Hap & Hs & Hlen).
assert (Hno : ~ In (q, m) O).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) Hap _ Hin) as Hd.
  unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hq) as (_ & Hq4096 & _).
split; [lia|].
split; [apply (scn_str_keep (rdW W mem)); [exact Hs | intros i Hi; apply (K q m); [exact Hq | exact Hno | lia]]|].
split; [exists q, m; split; [exact (KB q m Hq Hno) | lia] | exact Hlen].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The seed of the second half at the join 0x8adac                                                   *)

Lemma s6_seed : forall ly (regs regsc : bvmap 5 word) lyc Sc (Wc : world SEGS) memc mdc c,
astk_ok SUP_CONNECT_STK ly (spZ regs) ->
AR SEGS B lyc Sc Wc memc mdc -> scn_slot c -> scn_regs_join regs regsc c ->
scn_frame (mrestrict (w_H Wc) memc) (spZ regs) regs ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (scn_extra_m regs))) scn_ss_m
  (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + SCN_JOIN)) memc (seg_rom SEGS))).
Proof.
intros ly regs regsc lyc Sc Wc memc mdc c Hstk HAR Hslot HRJ HFR.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HRJ as (Rsp & R8 & R22 & R21 & R20 & R19 & R9 & R3 & R4 & Rhi).
destruct (scn_slot_facts c Hslot) as (Hc8 & Hcr & Hcin).
assert (FFS : SUP_CONNECT_STK = 16592) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (scn_extra_m regs))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 9)%nat -> ew E (32 + j) = getr regs (Z_to_bv 5 (nth j scn_saved 0))).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  unfold scn_extra_m. do 9 (destruct j as [|j]; [reflexivity|]). lia. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
assert (U8 : bv_unsigned (ew E 8) = c)
by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small;
    unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcr; lia).
assert (E22 : ew E 22 = Z_to_bv 64 SCN_SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (U22 : bv_unsigned (ew E 22) = SCN_SB)
by (rewrite E22; apply unsigned_lit_small; unfold SCN_SB; lia).
assert (VB2 : base_val E (Some 2%nat) = spZ regs - 80) by (cbn [base_val]; exact U2).
assert (VB8 : base_val E (Some 8%nat) = c) by (cbn [base_val]; exact U8).
assert (RS : YP09.region_ok SEGS E (mrestrict (w_H Wc) memc) scn_stack_m).
{ unfold region_ok, scn_stack_m.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite VB2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj. destruct Hj as [_ Hj].
  cbn [Nat.add] in Hj.
  apply (chunk_ok_val SEGS E _ (spZ regs - 80) (72 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (getr regs (Z_to_bv 5 (nth j scn_saved 0))))).
  - cbn [sv_denot]. rewrite (EX j Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - exact (s6_w64 (getr regs (Z_to_bv 5 (nth j scn_saved 0)))).
  - lia.
  - replace (spZ regs - 80 + (72 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    change (N.to_nat 8) with 8%nat. apply (HFR j (nth j scn_saved 0)).
    do 9 (destruct j as [|j]; [reflexivity|]). lia. }
assert (RC : YP09.region_ok SEGS E (mrestrict (w_H Wc) memc) scn_slot_region).
{ unfold region_ok, scn_slot_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite VB8. unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in Hcr |- *.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (scn_pg_writable B PROG_WRITABLE lyc Sc Wc memc mdc (c + o) HAR).
  apply Hcin. unfold CALL_SIZE. lia. }
assert (Hmod16 : (spZ regs - 80) mod 2 ^ 4 = 0).
{ replace (2 ^ 4) with 16 by reflexivity. rewrite Zminus_mod, Hal16. reflexivity. }
assert (Hmod8 : c mod 2 ^ 3 = 0) by (replace (2 ^ 3) with 8 by reflexivity; exact Hc8).
assert (Hmod1 : SCN_SB mod 2 ^ 0 = 0) by (vm_compute; reflexivity).
assert (HG : facts_ok E scn_facts_m).
{ split; [|split; [exact I | exact I]].
  cbn [scn_facts_m f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U22.
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcr |- *.
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I | exact Hmod16 | exact Hmod8 | exact Hmod1 | unfold SCN_SB; lia ]. }
unfold scn_ss_m. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold scn_regs_m. constructor; [exact RS | constructor; [exact RC | constructor]].
- apply pairwise_disjoint_of_extents.
  unfold scn_regs_m, scn_stack_m, scn_slot_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB2, VB8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE in Hcr |- *.
  repeat split; lia.
- exact HG.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* xstrdup on the verb: the statement's str_arg, not sb_xarg                                         *)

(* "(null)" at 0x22480 is a read-only string of the image with a readable tail *)
Lemma s6_null_argA : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] 0x22480 (Some (sarg None)) /\
atail_vis SEGS W mem (0x22480 + Z.of_nat (length (sarg None))).
Proof.
intros ly S W mem md HAR HROD.
assert (Hro : cmd_ro_ok (rdW W mem)) by exact (cmd_ro_ok_of_aro ly S W mem md HAR HROD).
assert (HLIT : abytes_atR (rdW W mem) 0x22480 RO_lit_22480).
{ clear - Hro. destruct Hro as [Hro _]. unfold cmd_ro_bytes in Hro.
  repeat match type of Hro with
  | abytes_atR _ 0x22480 _ /\ _ => exact (proj1 Hro)
  | _ /\ _ => apply proj2 in Hro
  end. }
assert (HIN : forall i, 0 <= i < 7 -> in_roP SEGS RLO RHI (0x22480 + i)).
{ pose proof cmd_ro_in_img as HROIN. clear - HROIN. unfold cmd_ro_in in HROIN.
  repeat match type of HROIN with
  | (forall i, 0 <= i < 7 -> _ (0x22480 + i)) /\ _ => exact (proj1 HROIN)
  | _ /\ _ => apply proj2 in HROIN
  end. }
split.
- unfold astr_argA. cbv zeta. rewrite sb_null_len.
  split; [lia|]. split; [split; [rewrite sb_ro_null; exact HLIT | exact sb_null_nz]|].
  split; [unfold LMAX; lia|].
  right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity |]]].
  2: { change (0x22480 + Z.of_nat 6) with 0x22486. exact sb_end_in. }
  intros i Hi. split; [exact (HIN i Hi)|]. exact (sb_null_unowned B HB i Hi).
- rewrite sb_null_len. change (0x22480 + Z.of_nat 6) with 0x22486.
  exact (cmd_tail_vis_at ly S W mem md 0x22486 HAR sb_end_in).
Qed.

(* the string xstrdup is handed for the verb: the verb, or "(null)" when the pointer is NULL *)
Lemma s6_vargA : forall ly S (W : world SEGS) mem md pv verb,
AR SEGS B ly S W mem md -> arodata_okP SEGS RLO RHI B (rdW W mem) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] pv verb ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] (if pv =? 0 then 0x22480 else pv) (Some (sarg verb)) /\
atail_vis SEGS W mem ((if pv =? 0 then 0x22480 else pv) + Z.of_nat (length (sarg verb))).
Proof.
intros ly S W mem md pv [x|] HAR HROD HA; cbn [astr_argA] in HA.
- cbv zeta in HA. destruct HA as (Hp & Hs & Hlen & Harm).
  rewrite (proj2 (Z.eqb_neq pv 0) Hp). cbn [sarg]. split.
  + cbn [astr_argA]. cbv zeta. split; [exact Hp|]. split; [exact Hs|]. split; [exact Hlen | exact Harm].
  + destruct Harm as [(Hbl & _) | (_ & _ & _ & He)].
    * destruct Hbl as (q & m & Hq & Hq1 & Hq2).
      exact (cmd_heap_tail_vis ly S W mem md q m (pv + Z.of_nat (length x)) HAR Hq ltac:(lia)).
    * exact (cmd_tail_vis_at ly S W mem md (pv + Z.of_nat (length x)) HAR He).
- subst pv. exact (s6_null_argA ly S W mem md HAR HROD).
Qed.

(* xstrdup through the kit's call rule, with the string in the statement's str_arg form (s4's sb_xcall
   with the sb_xarg premise replaced by astr_argA and the tail) *)
Lemma s6_xcallA : forall (Q : world SEGS -> config -> Prop) sp0 FP ly S (W : world SEGS) mem md (Wq : world SEGS)
  regsq memq mdq lyq Sq kq s x,
ajournal SEGS B SUP_CONNECT_STK sp0 FP ly S W mem md [] lyq Sq Wq memq mdq kq ->
spZ regsq = sp0 + -80 ->
getr regsq 3 = w64 (as_gp B) -> getr regsq 4 = w64 (as_tp B) ->
YK0s.ret_ok (getr regsq 1) -> 4096 <= bv_unsigned (getr regsq 1) ->
s0Z regsq < alloc_ceiling ->
getr regsq 10 = w64 s ->
arodata_okP SEGS RLO RHI B (rdW Wq memq) ->
astr_argA B lyq Sq (rdW Wq memq) (in_roP SEGS RLO RHI) [] s (Some x) ->
atail_vis SEGS Wq memq (s + Z.of_nat (length x)) ->
st_nev Sq + EV_XSTRDUP <= EV_MAX -> blocks_bytes Sq + LIVE_XSTRDUP x <= LIVE_MAX ->
mo_ok MT Sq (XM_XSTRDUP MT x) ->
(forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 p,
  ajournal SEGS B SUP_CONNECT_STK sp0 FP ly S W mem md [] ly2 S2 W2 mem2 md2 (kq + EV_XSTRDUP) ->
  ajournal SEGS B XSTRDUP_STK (sp0 + -80) [] lyq Sq Wq memq mdq [] ly2 S2 W2 mem2 md2 EV_XSTRDUP ->
  aregs_preserved regsq regs2 -> getr regs2 10 = w64 p -> 4096 <= p < 2 ^ 64 ->
  Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP x) :: ablocks B lyq Sq) ->
  Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B lyq Sq) ->
  in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP x) ->
  astr_atR (rdW W2 mem2) p x ->
  blocks_bytes S2 <= blocks_bytes Sq + LIVE_XSTRDUP x ->
  mo_le MT Sq S2 (XM_XSTRDUP MT x) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (getr regsq 1) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS Wq (mkCfg (mkst regsq (Z_to_bv 64 (SIGMA CS_xstrdup)) memq (seg_rom SEGS)) mdq) Q.
Proof.
intros Q sp0 FP ly S W mem md Wq regsq memq mdq lyq Sq kq s x HJ Hsp Hgp Htp Hra Hra4 Hs0 H10 HROD HXA HTAIL
  Hev Hlive Hmok K.
rewrite (sb_sig_x SIGP).
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wq regsq memq (Z_to_bv 64 (BASE + AF_xstrdup)) SUP_CONNECT_STK sp0 FP ly S W mem md []
    lyq Sq mdq kq XSTRDUP_STK [] EV_XSTRDUP (-80) (getr regsq 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z, getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP x) :: ablocks B lyq Sq) /\
       Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B lyq Sq) /\
       in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP x) /\
       astr_atR (rdW W2 mem2) p x /\ astr_atR (rdW W2 mem2) s x /\
       blocks_bytes S2 <= blocks_bytes Sq + LIVE_XSTRDUP x /\
       mo_le MT Sq S2 (XM_XSTRDUP MT x))
    HJ Hsp eq_refl ltac:(lia) ltac:(rewrite sb_xstk; lia) ltac:(rewrite sb_xstk, sb_stk; lia) Hgp Htp eq_refl Hra Hra4
    (achain_low _ _ _ _ Hs0)).
  - intros HPREc. eapply SRr_mono.
    { exact (TXSTRDUP fx lyq Sq Wq regsq memq mdq [] s x HPREc HROD H10
        (or_introl HXA) HTAIL Hev Hlive Hmok). }
    cbv beta. unfold apost_base. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2).
    exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2 | exact HQ2].
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 &
  p & Hp10 & Hp4096 & Hperm & Hfresh & Hpblk & Hpstr & _ & Hbb & Hmle).
exact (K ly2 S2 W2 regs2 mem2 md2 p HJ2 HJ2c HP2 Hp10 Hp4096 Hperm Hfresh Hpblk Hpstr Hbb Hmle).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* 0x8ade8 -> 0x8ae50: xstrdup(verb), the two stores, arg_line(c, line), the port_a null check        *)

(* every byte of the slot lies in the walk's footprint *)
Lemma s6_slot_fp : forall O c a, scn_slot c -> c <= a < c + CALL_SIZE -> inFP (scn_FP O) a.
Proof.
intros O c a [(i & Hi & ->) | ->] Ha.
- exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8). split; [unfold scn_FP; right; left; reflexivity|].
  cbn [fst snd]. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_CALLS_MAX in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [unfold scn_FP; right; right; right; left; reflexivity|].
  cbn [fst snd]. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* arg_line's post at the call state, the K of cl_callS_wide (the m = 6 arm is impossible: c->nargs is 1) *)
Definition s6_al_K (ly4 : alayout) (S4 : astate) (c : Z) (line : list byte) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly6 S6 W6 regs6 mem6 md6 =>
  blocks_bytes S6 <= blocks_bytes S4 + LIVE_ARG_LINE line /\
  mo_le MT S4 S6 (XM_ARG_LINE MT line) /\
  exists q, 4096 <= q < 2 ^ 64 /\
    Permutation (ablocks B ly6 S6) ((q, Z.of_nat (length line) + 1) :: ablocks B ly4 S4) /\
    Forall (fun qk => iv_apart q (Z.of_nat (length line) + 1) (fst qk) (snd qk)) (ablocks B ly4 S4) /\
    aval_mem (rdW W6 mem6) (c + CALL_OFF_NARGS) 4 2 /\
    aval_mem (rdW W6 mem6) (c + CALL_OFF_ARGS + 8) 8 q /\
    astr_atR (rdW W6 mem6) q (canon line).

Lemma sb_seg1 : SB2_stmt B MT -> SB1_stmt B MT.
Proof.
intros SB2 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
  E W1 regs1 mem1 md1 ly1 S1 O1b rd1 HCX HS HENV E42 HINV HSV HSL HSA HSB.
set (t := snd (sup_connect_m R verb line port_a port_b)) in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as (HPRE & HMID).
pose proof HPRE as (HPRE0 & HFRM & Hfr8 & HROD & HRO & H10 & Hpv64 & H11 & Hpl64 & H12 & Hpa64 & H13 & Hpb64 &
  HSV0 & HSVT & HSL0 & HSA0 & HSB0 & HREP0 & Hev & Hlive & HMOK).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJc & Hk & Hslot & Hpos & HRJ & HFR & HREC & HO1O & HO1c & HOO1 & HcS & HSc & Hfrsc & Hbbc & MLEc).
pose proof HRJ as (Rsp & R8 & R22 & R21 & R20 & R19 & R9 & R3 & R4 & Rhi).
pose proof HINV as (HJ1 & Hfr1 & Hbb1 & Hlv1 & MLE1 & HREP1 & HK1 & HBK1).
pose proof HENV as (HEI & HE0).
pose proof (sb_O_facts B LAWS ly S W mem md _ R O HAR HREP0) as HOf.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn H; exact (proj1 (HOf pn H))).
assert (HOpos : Forall (fun pn => 0 < fst pn) O) by (apply Forall_forall; intros pn H; pose proof (HOf pn H); lia).
destruct (scn_slot_facts c Hslot) as (Hc8 & Hcr & Hcin).
assert (Hcr' : 0x5e3740 <= c < 0x5e3c18) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcr; lia).
pose proof sb_stk as FFS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite HE0 by lia. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
assert (E8 : ew E 8 = w64 c) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (U8 : bv_unsigned (ew E 8) = c) by (rewrite E8; apply unsigned_lit_small; lia).
assert (E22 : ew E 22 = Z_to_bv 64 SCN_SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E19 : ew E 19 = w64 pa) by (rewrite (EE 19%nat 19%bv eq_refl), R19; exact H12).
assert (E20 : ew E 20 = w64 pl) by (rewrite (EE 20%nat 20%bv eq_refl), R20; exact H11).
pose proof (Lshok ly1 S1 W1 mem1 md1 E c (proj1 HJ1) Hslot U8 E22) as SHOK.
pose proof (proj1 HJ1) as HAR1.
assert (HROD1m : arodata_okP SEGS RLO RHI B (rdW W1 mem1))
by exact (Larod SUP_CONNECT_STK (spZ regs) O ly S W mem md [] ly1 S1 W1 mem1 md1 k HAR HOin HOpos HJ1 HROD).
(* 0x8ade8 .. 0x8adec: a0 := s5, the call of xstrdup *)
paj_run_tok RUN HS HJ1 SHOK scn_Bspan.
{ awr_ok_tac. }
s6_set_md mdv1. s6_name_ms HS ms1.
pose proof (kept_of_frame (segs:=SEGS) E _ (w_H W1) mem1 (ms_mem ms1) (fun _ => False) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KEEP0.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs + -80) by (unfold spZ at 1; rewrite P2, U2; lia).
assert (Hgp1 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (Htp1 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (HnevJ : st_nev S1 + EV_XSTRDUP <= EV_MAX).
{ pose proof HJ1 as (_ & _ & _ & _ & _ & _ & Hnev & _). clear - Hnev Hev Hk.
  unfold EV_SUP_CONNECT, EV_ANSWER, EV_HAND_BACK, EV_ARG_LINE, EV_REC_CANONICAL, EV_XSTRDUP in *. lia. }
pose proof (proj1 HJ1) as HAR1n.
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW W1 (ms_mem ms1)))
by exact (Larod SUP_CONNECT_STK (spZ regs) O ly S W mem md [] ly1 S1 W1 (ms_mem ms1) mdv1 k HAR HOin HOpos HJ1 HROD).
(* the verb at this state, in the statement's str_arg form *)
assert (HSVk : astr_argA B ly1 S1 (rdW W1 (ms_mem ms1)) (in_roP SEGS RLO RHI) [] pv verb).
{ apply (s6_argA_move ly1 S1 ly1 S1 W1 W1 mem1 (ms_mem ms1) [] pv verb HSV HROD1m HROD1); [|auto].
  intros q m a Hq _ Ha. destruct (sb_in_blk_range B LAWS ly1 S1 W1 mem1 md1 q m a HAR1 Hq Ha) as (Ha1 & Ha2 & _).
  apply KEEP0; [lia | tauto]. }
destruct (s6_vargA ly1 S1 W1 (ms_mem ms1) mdv1 pv verb HAR1n HROD1 HSVk) as (HXA & HTAIL).
assert (Hlive0 : 0 <= LIVE_ANSWER t /\ 0 <= LIVE_XSTRDUP (sarg port_a) /\ 0 <= LIVE_XSTRDUP (sarg port_b) /\
  0 <= LIVE_ARG_LINE line)
by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP, LIVE_ARG_LINE, LIVE_REC_CANONICAL; lia).
assert (HLIVE : blocks_bytes S1 + LIVE_XSTRDUP (sarg verb) <= LIVE_MAX) by lia.
assert (HMOK1 : mo_ok MT S1 (XM_XSTRDUP MT (sarg verb))).
{ pose proof (mo_free_nonneg MT MTL) as M0.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg verb)) + 1) ltac:(lia)) as M1v.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg port_a)) + 1) ltac:(lia)) as M1a.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg port_b)) + 1) ltac:(lia)) as M1b.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length line) + 1) ltac:(lia)) as M1l.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)) as M1t.
  apply (mok_station MT S S1 (XM_SUP_CONNECT MT R verb line port_a port_b t) _ (XM_XSTRDUP MT (sarg verb)) MTL HMOK MLE1);
  unfold XM_SUP_CONNECT, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP, XM_ARG_LINE, XM_REC_CANONICAL in *; lia. }
eapply (s6_xcallA _ (spZ regs) (scn_FP O) ly S W mem md W1 (ms_regs ms1) (ms_mem ms1) mdv1 ly1 S1 k
  (if pv =? 0 then 0x22480 else pv) (sarg verb) HJ1 Hsp1 Hgp1 Htp1).
{ rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ rewrite P1, unsigned_lit_small by lia. lia. }
{ unfold s0Z. rewrite P8, U8. lia. }
{ rewrite P10, E42. reflexivity. }
{ exact HROD1. }
{ exact HXA. }
{ exact HTAIL. }
{ exact HnevJ. }
{ exact HLIVE. }
{ exact HMOK1. }
intros ly4 S4 W4 regs4 mem4 md4 p0 HJ4 HJ4c HP4 Hp10 [Hp4096 Hp64] Hperm Hfresh Hpblk Hpstr Hxbb Hmle.
rewrite P1.
(* back at 0x8adf0: the frame and the whole slot are kept *)
jafter_call_keep_pi HS 48%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS4.
match type of HS4 with ?T -> _ => assert (HRK : T); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
  - eapply (region_kept_stack_sub SEGS B E XSTRDUP_STK (spZ regs + -80) [] ly1 S1 W1 (ms_mem ms1) mdv1 ly4 S4 W4 mem4
      md4 EV_XSTRDUP 2 0 80 0 0 _ (spZ regs - 80) SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] _ HJ4c HJ4 U2);
    [lia | lia | lia | lia | lia | intros a _ Ha; exact (inFP_nil a Ha)].
  - apply (Lslot_kept E W1 W4 (ms_mem ms1) mem4 c 0 CALL_SIZE 0 0 _ XSTRDUP_STK (spZ regs + -80) [] ly1 S1 mdv1 ly4 S4
      md4 EV_XSTRDUP HJ4c U8 Hslot); try (unfold CALL_SIZE; lia).
    + intros b Hb. destruct (inFP_nil b Hb).
    + intros a _ Ha. exact (inFP_nil a Ha). }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E 48 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD4 : forall n, (n < 48)%nat -> ew E4 n = ew E n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
assert (E52 : ew E4 52 = getr regs4 10%bv) by (rewrite HE4; unfold havoc; cbn [ew]; reflexivity).
clear HE4.
assert (U84 : bv_unsigned (ew E4 8) = c) by (rewrite OLD4 by lia; exact U8).
assert (U24 : bv_unsigned (ew E4 2) = spZ regs - 80) by (rewrite OLD4 by lia; exact U2).
pose proof (proj1 HJ4) as HAR4.
(* the slot becomes writable on c->nargs and c->args[0] *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_region_nth E4 ssx (restrict (w_H W4) msx) 1
    (sb_ro (sb_slot 0 CALL_SIZE [YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 0 (CVal 4 (SLit 4))]))
    HS ltac:(vm_compute; reflexivity)) as HRs end.
cbn [ms_mem restrict mkst] in HRs.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (ast_ok_pi_set_region E4 ssx msx 1
    (sb_ro (sb_slot 0 CALL_SIZE [YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 0 (CVal 4 (SLit 4))]))
    (sb_slot 4 16 [YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 0 (CVal 4 (SLit 4))])
    HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)) as HS5 end.
match type of HS5 with ?P -> _ => assert (HRn : P); [|specialize (HS5 HRn); clear HRn] end.
{ cbn [ms_mem restrict mkst]. unfold sb_ro, sb_slot, region_ok in HRs |- *.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRs |- *.
  destruct HRs as (HR1 & HR2 & _ & HRch). split; [exact HR1|]. split; [exact HR2|]. split; [|exact HRch].
  rewrite U84. intros o Ho. apply (scn_pg_writable B PROG_WRITABLE ly4 S4 W4 mem4 md4 _ HAR4).
  apply Hcin. unfold CALL_SIZE. lia. }
clear HS. rename HS5 into HS.
assert (E224 : ew E4 22 = Z_to_bv 64 SCN_SB) by (rewrite OLD4 by lia; exact E22).
pose proof (Lshok ly4 S4 W4 mem4 md4 E4 c HAR4 Hslot U84 E224) as SHOK4.
(* 0x8adf0 .. 0x8ae2c: c->nargs := 1, c->args[0] := the copy, then the call of arg_line *)
paj_run_tok RUN HS HJ4 SHOK4 scn_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply Lawr_slot; [reflexivity | exact U84 | exact Hslot | cbn; lia | cbn; unfold CALL_SIZE; lia |].
  apply awr_ok_nil. }
s6_set_md mdv2. s6_name_ms HS ms5.
pose proof (kept_of_frame (segs:=SEGS) E4 _ (w_H W4) mem4 (ms_mem ms5) (fun a => c + 4 <= a < c + 16) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U84, ?U24 in Hrr; lia|]);
        destruct Hin)) as KEEP5.
clear HF HFr HG.
(* the first argument is appended to the call *)
assert (HpIn : In (p0, LIVE_XSTRDUP (sarg verb)) (ablocks B ly4 S4))
by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (Hxl : Z.of_nat (length (sarg verb)) <= LMAX).
{ destruct verb as [x|].
  - cbn [astr_argA] in HSVk. cbv zeta in HSVk. destruct HSVk as (_ & _ & Hl & _). cbn [sarg]. lia.
  - rewrite sb_null_len. unfold LMAX. lia. }
pose proof (blk_off_imgP B ly4 S4 W4 mem4 md4 _ _ HAR4 HpIn) as Hpoff. unfold off_img in Hpoff.
destruct (al_blocks _ _ LAWS ly4 S4 W4 mem4 md4 _ _ HAR4 HpIn) as (_ & _ & Hpceil & _).
pose proof (req_size_pos (LIVE_XSTRDUP (sarg verb)) ltac:(unfold LIVE_XSTRDUP; lia)) as [_ Hpreq].
unfold LIVE_XSTRDUP in Hpoff, Hpceil, Hpreq.
s6_region_nth HS E4 1%nat (sb_slot 4 16 [YP09.mkChunk 8 (CVal 8 (SOff 52 0)); YP09.mkChunk 4 (CVal 4 (SLit 1));
                                         YP09.mkChunk 0 (CVal 4 (SLit 4))]) HRa.
cbn [ms_mem restrict] in HRa.
pose proof (field_of_region E4 _ 8 c _ 0 CALL_SIZE 4 16 4 4 (SLit 1) 1 HRa U84
  ltac:(right; left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(lia)) as VN1.
pose proof (field_of_region E4 _ 8 c _ 0 CALL_SIZE 4 16 8 8 (SOff 52 0) p0 HRa U84
  ltac:(left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite E52, Hp10, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
  ltac:(cbn; lia) ltac:(lia)) as VA0.
change (N.to_nat 4) with 4%nat in VN1. change (N.to_nat 8) with 8%nat in VA0.
assert (KREC : forall a, sb_recb (ablocks B ly1 S1) O1b a ->
  ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
  ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) <= a <
     c + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8) ->
  rdW W4 (ms_mem ms5) a = rd1 a).
{ intros a Ha Hn1 Hn2. cbn [length] in Hn2. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hn1, Hn2.
  assert (Hrng : 0 <= a < 2 ^ 64 /\ ~ (c + 4 <= a < c + 16) /\ (inFP cmd_PG a \/
    exists q m, In (q, m) (ablocks B ly1 S1) /\ In (q, m) (ablocks B ly4 S4) /\ q <= a < q + m)).
  { destruct Ha as [Ha | [Ha | ([q m] & Hq & HqO & Ha)]].
    - split; [unfold A_G_REC, REC_SIZE in Ha; lia|]. split; [lia|]. left; apply sb_recb_static; left; exact Ha.
    - split; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|]. split; [lia|]. left; apply sb_recb_static; right; exact Ha.
    - cbn [fst snd] in Ha. destruct (sb_in_blk_range B LAWS ly1 S1 W1 mem1 md1 q m a HAR1 Hq Ha) as (Ha1 & Ha2 & Ha3).
      split; [lia|]. split; [lia|]. right. exists q, m. split; [exact Hq|]. split; [|exact Ha].
      eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hq]. }
  destruct Hrng as (Hrng & Hnf & Hwhere).
  rewrite (KEEP5 a Hrng Hnf).
  rewrite (Lcall_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ4c ltac:(intros b Hb; destruct (inFP_nil b Hb))
    ltac:(destruct Hwhere as [Hw | Hw]; [left; split; [exact Hw | apply inFP_nil] | right; exact Hw])).
  rewrite (KEEP0 a Hrng ltac:(tauto)). exact (HK1 a Ha). }
assert (HREP4 : rec_repA B ly4 S4 (rdW W4 (ms_mem ms5))
  (rec_record R REC_CONNECT ([] ++ [sarg verb])) ((p0, LIVE_XSTRDUP (sarg verb)) :: O1b)).
{ apply (scn_append_rep B ly1 S1 ly4 S4 rd1 (rdW W4 (ms_mem ms5)) R REC_CONNECT [] O1b c
    (sarg verb) p0 (LIVE_XSTRDUP (sarg verb)) HREP1 Hpos).
  - cbn. lia.
  - lia.
  - apply (scn_str_keep (rdW W4 mem4)); [exact Hpstr|]. intros i Hi. apply KEEP5; [lia|].
    unfold CALL_SIZE in Hcr'. lia.
  - exact Hxl.
  - unfold LIVE_XSTRDUP. lia.
  - exact Hfresh.
  - unfold iv_apart, A_G_REC, REC_SIZE, LIVE_XSTRDUP. lia.
  - unfold iv_apart, A_REC_SPILL, SC_SIZE, LIVE_XSTRDUP. lia.
  - change (Z.of_nat (length (@nil (list byte))) + 1) with 1. unfold CALL_OFF_NARGS.
    exact (scn_aval_of_val_mem SEGS _ _ _ _ _ VN1).
  - change (Z.of_nat (length (@nil (list byte)))) with 0. unfold CALL_OFF_ARGS.
    replace (c + 8 + 8 * 0) with (c + 8) by lia. exact (scn_aval_of_val_mem SEGS _ _ _ _ _ VA0).
  - exact KREC.
  - exact Hperm. }
assert (Hnew : In (p0, LIVE_XSTRDUP (sarg verb)) (ablocks B ly S) -> In (p0, LIVE_XSTRDUP (sarg verb)) O).
{ intros Hin. apply (sb_new_in_O B LAWS ly S W mem md O [] ly1 S1 W1 (ms_mem ms1) mdv1 k (spZ regs) SUP_CONNECT_STK
    p0 _ HAR HOin HJ1); [|exact Hin].
  intros Hin2. pose proof (proj1 (Forall_forall _ _) Hfresh _ Hin2) as Hap. unfold iv_apart, LIVE_XSTRDUP in Hap.
  cbn [fst snd] in Hap. lia. }
pose proof (sb_bk_step B ly S O _ _ O1b p0 _ HBK1 Hperm Hnew) as HBK4.
pose proof HJ4c as (_ & _ & _ & _ & _ & Hfr4c & _).
assert (HROD4 : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms5)))
by exact (Larod SUP_CONNECT_STK (spZ regs) O ly S W mem md [] ly4 S4 W4 (ms_mem ms5) mdv2 _ HAR HOin HOpos HJ4 HROD).
(* the line and the two ports at this state *)
assert (KBLK : forall q m a, In (q, m) (ablocks B ly1 S1) -> q <= a < q + m ->
  rdW W4 (ms_mem ms5) a = rdW W1 mem1 a).
{ intros q m a Hq Ha. destruct (sb_in_blk_range B LAWS ly1 S1 W1 mem1 md1 q m a HAR1 Hq Ha) as (Ha1 & Ha2 & Ha3).
  assert (Hr64 : 0 <= a < 2 ^ 64) by lia.
  assert (Hnf5 : ~ (c + 4 <= a < c + 16)) by lia.
  rewrite (KEEP5 a Hr64 Hnf5).
  rewrite (Lcall_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ4c ltac:(intros b Hb; destruct (inFP_nil b Hb))
    ltac:(right; exists q, m; split; [exact Hq | split;
      [eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hq] | exact Ha]])).
  apply KEEP0; [lia | tauto]. }
assert (KBL : forall pn, In pn (ablocks B ly1 S1) -> In pn (ablocks B ly4 S4))
by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hpn]).
assert (HSLk : sb_sstr (ablocks B ly4 S4) (rdW W4 (ms_mem ms5)) pl (Some line)).
{ apply (sb_sstr_keep (ablocks B ly1 S1) _ (rdW W1 mem1) _ _ _ HSL KBL).
  intros a (q & m & Hq & Ha). exact (KBLK q m a Hq Ha). }
assert (HSAk : sb_sstr (ablocks B ly4 S4) (rdW W4 (ms_mem ms5)) pa port_a).
{ apply (sb_sstr_keep (ablocks B ly1 S1) _ (rdW W1 mem1) _ _ _ HSA KBL).
  intros a (q & m & Hq & Ha). exact (KBLK q m a Hq Ha). }
assert (HSBk : sb_sstr (ablocks B ly4 S4) (rdW W4 (ms_mem ms5)) pb port_b).
{ apply (sb_sstr_keep (ablocks B ly1 S1) _ (rdW W1 mem1) _ _ _ HSB KBL).
  intros a (q & m & Hq & Ha). exact (KBLK q m a Hq Ha). }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Hsp5 : spZ (ms_regs ms5) = spZ regs + -80) by (unfold spZ at 1; rewrite Q2, U24; lia).
assert (HnevA : st_nev S4 + EV_ARG_LINE <= EV_MAX).
{ pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnev & _). clear - Hnev Hev Hk.
  unfold EV_SUP_CONNECT, EV_ANSWER, EV_HAND_BACK, EV_ARG_LINE, EV_REC_CANONICAL, EV_XSTRDUP in *. lia. }
assert (HLIVEA : blocks_bytes S4 + LIVE_ARG_LINE line <= LIVE_MAX) by lia.
assert (HMOKA : mo_ok MT S4 (XM_ARG_LINE MT line)).
{ pose proof (mo_free_nonneg MT MTL) as M0.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg verb)) + 1) ltac:(lia)) as M1v.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg port_a)) + 1) ltac:(lia)) as M1a.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg port_b)) + 1) ltac:(lia)) as M1b.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length line) + 1) ltac:(lia)) as M1l.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)) as M1t.
  apply (mok_station MT S S4 (XM_SUP_CONNECT MT R verb line port_a port_b t) _ (XM_ARG_LINE MT line) MTL HMOK
    (mle_station MT S S1 S4 _ _ MTL MLE1 Hmle));
  unfold XM_SUP_CONNECT, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP, XM_ARG_LINE, XM_REC_CANONICAL in *; lia. }
destruct HSLk as (Hpl0 & HplS & HplB & HplL).
(* 0x8ae2c: the call of arg_line, through the kit's wide call rule *)
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W4 (ms_regs ms5) (ms_mem ms5) _
    SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] ly4 S4 mdv2 (k + EV_XSTRDUP) ARG_LINE_STK
    [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 1, c + CALL_OFF_ARGS + 8 * 1 + 8)]
    EV_ARG_LINE (-80) (Z_to_bv 64 (BASE + SB_R2)) []
    (s6_al_K ly4 S4 c line) HJ4 Hsp5).
  - reflexivity.
  - lia.
  - rewrite sb_alstk; lia.
  - rewrite FFS, sb_alstk; lia.
  - rewrite Q3, OLD4 by lia. rewrite (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite Q4, OLD4 by lia. rewrite (EE 4%nat 4%bv eq_refl), R4. exact Htp.
  - exact Q1.
  - unfold SB_R2. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold SB_R2. rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite Q8, U84. lia.
  - intros HPREA. try rewrite (sb_sig_al SIGP). eapply SRr_mono.
    { apply (TARG_LINE fx ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) mdv2 [] c pl 1 line HPREA HROD4
        ltac:(rewrite Q10, OLD4 by lia; exact E8)
        ltac:(rewrite Q11, OLD4 by lia; rewrite E20; reflexivity) Hpl64 Hslot
        ltac:(unfold CALL_OFF_NARGS; exact (scn_aval_of_val_mem SEGS _ _ _ _ _ VN1))
        ltac:(unfold REC_ARGS_MAX; lia) HplB HplS HplL HnevA HLIVEA HMOKA). }
    cbv beta. unfold apost_base. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hbb6 & Hmle6 & HQ6).
    exists ly6, S6, regs6, mem6, md6. split; [rewrite Q1; reflexivity|]. split; [exact HJ6|]. split; [exact HP6|].
    split; [exact Hbb6|]. split; [exact Hmle6|].
    destruct HQ6 as [(Hm6 & _) | (_ & q & Hq4096 & Hqperm & Hqfresh & Hqn & Hqa & Hqs)];
    [unfold REC_ARGS_MAX in Hm6; lia|].
    exists q. split; [exact Hq4096|]. split; [exact Hqperm|]. split; [exact Hqfresh|].
    split; [exact Hqn|]. split; [|exact Hqs]. replace (c + CALL_OFF_ARGS + 8) with (c + CALL_OFF_ARGS + 8 * 1) by lia.
    exact Hqa.
  - intros a Ha.
    assert (Hin : c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4 \/ c + CALL_OFF_ARGS + 8 <= a < c + CALL_OFF_ARGS + 16).
    { apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [left; exact Ha|].
      apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [right; unfold CALL_OFF_ARGS in *; lia|].
      destruct (inFP_nil a Ha). }
    assert (HPG : inFP cmd_PG a) by (apply Hcin; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia).
    do 4 right. left.
    split; [exact (s6_slot_fp O c a Hslot ltac:(unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia))|].
    split; [exact (HPROG B HB a HPG) | exact (cif_prog_img a HPG)].
  - intros ly6 S6 W6 regs6 mem6 md6 HK a Hin Hw1 Hw2. exfalso.
    assert (Hr : c + CALL_OFF_NARGS <= a < c + CALL_OFF_ARGS + 16).
    { apply inFP_cons in Hin. destruct Hin as [Hin | Hin]; [unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia|].
      apply inFP_cons in Hin. destruct Hin as [Hin | Hin]; [unfold CALL_OFF_ARGS in *; lia|].
      destruct (inFP_nil a Hin). }
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hr. rewrite FFS in Hw1. lia. }
cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HJ6 & HJ6c & HP6 & Hbb6 & Hmle6 &
  q & [Hq4096 Hq64] & Hqperm & Hqfresh & Hqn & Hqa & Hqs).
unfold SB_R2.
replace (k + EV_XSTRDUP + EV_ARG_LINE) with (k + 2) in HJ6 by (unfold EV_XSTRDUP, EV_ARG_LINE, EV_REC_CANONICAL; lia).
assert (HFP1 : forall a, inFP [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4);
  (c + CALL_OFF_ARGS + 8 * 1, c + CALL_OFF_ARGS + 8 * 1 + 8)] a -> c + 4 <= a < c + 8 \/ c + 16 <= a < c + 24).
{ intros a Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS in Ha; left; lia|].
  apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS in Ha; right; lia | destruct (inFP_nil a Ha)]. }
assert (HFPG : forall b, inFP [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4);
  (c + CALL_OFF_ARGS + 8 * 1, c + CALL_OFF_ARGS + 8 * 1 + 8)] b -> inFP cmd_PG b).
{ intros b Hb. apply Hcin. pose proof (HFP1 b Hb). unfold CALL_SIZE. lia. }
(* back at 0x8ae30: the frame is kept; the slot's region is dropped (arg_line wrote two of its fields) *)
jafter_call_keep_pi HS 64%nat regs6 (mrestrict (w_H W6) mem6) HP6 [0]%nat HS6.
match type of HS6 with ?T -> _ => assert (HRK : T); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B E4 ARG_LINE_STK (spZ regs + -80) _ ly4 S4 W4 (ms_mem ms5) mdv2 ly6 S6 W6 mem6
    md6 EV_ARG_LINE 2 0 80 0 0 _ (spZ regs - 80) SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] _ HJ6c HJ6 U24);
  [lia | lia | lia | lia | lia |].
  intros a Ha Hf. pose proof (HFP1 a Hf) as Hr. rewrite FFS in *. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
remember (havoc E4 64 (map (getr regs6) CLOB)) as E6 eqn:HE6 in HS.
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc; [exact HEI4 | cbv; lia]).
assert (OLD6 : forall n, (n < 64)%nat -> ew E6 n = ew E4 n) by (intros n Hn; rewrite HE6; apply YN3v.ew_havoc_old; exact Hn).
clear HE6.
assert (U86 : bv_unsigned (ew E6 8) = c) by (rewrite OLD6 by lia; exact U84).
assert (U26 : bv_unsigned (ew E6 2) = spZ regs - 80) by (rewrite OLD6 by lia; exact U24).
assert (E226 : ew E6 22 = Z_to_bv 64 SCN_SB) by (rewrite OLD6 by lia; exact E224).
pose proof (proj1 HJ6) as HAR6.
(* c->nargs = 2 is a read-only region again *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (st_ok_pi_add_region E6 ssx msx (sb_nargs false 2) HS ltac:(vm_compute; reflexivity)) as HS7 end.
match type of HS7 with ?P1 -> ?P2 -> _ =>
  assert (HA1 : P1); [|assert (HA2 : P2); [|specialize (HS7 HA1 HA2); clear HA1 HA2]] end.
{ cbn [ms_mem restrict mkst]. unfold region_ok, sb_nargs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U86. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E6 _ c 4 4 (SLit 2) 2); [reflexivity | cbn; lia | lia |].
  unfold CALL_OFF_NARGS in Hqn. exact (scn_val_mem_of_aval SEGS _ _ _ _ _ Hqn). }
{ cbn [ss_mem list_upd all_disjoint]. unfold extent_disjoint, sb_nargs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U86, U26. repeat split; lia. }
clear HS. rename HS7 into HS.
pose proof (Lshok ly6 S6 W6 mem6 md6 E6 c HAR6 Hslot U86 E226) as SHOK6.
(* the second argument is appended to the call *)
assert (HqIn : In (q, Z.of_nat (length line) + 1) (ablocks B ly6 S6))
by (eapply Permutation_in; [apply Permutation_sym; exact Hqperm | left; reflexivity]).
pose proof (blk_off_imgP B ly6 S6 W6 mem6 md6 _ _ HAR6 HqIn) as Hqoff. unfold off_img in Hqoff.
destruct (al_blocks _ _ LAWS ly6 S6 W6 mem6 md6 _ _ HAR6 HqIn) as (_ & _ & Hqceil & _).
pose proof (req_size_pos (Z.of_nat (length line) + 1) ltac:(lia)) as [_ Hqreq].
assert (KBL6 : forall pn, In pn (ablocks B ly4 S4) -> In pn (ablocks B ly6 S6))
by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact Hqperm | right; exact Hpn]).
assert (KBLK6 : forall q0 m0 a, In (q0, m0) (ablocks B ly4 S4) -> q0 <= a < q0 + m0 ->
  rdW W6 mem6 a = rdW W4 (ms_mem ms5) a).
{ intros q0 m0 a Hq0 Ha.
  exact (Lcall_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ6c HFPG
    ltac:(right; exists q0, m0; split; [exact Hq0 | split; [exact (KBL6 _ Hq0) | exact Ha]])). }
assert (KREC2 : forall a, sb_recb (ablocks B ly4 S4) ((p0, LIVE_XSTRDUP (sarg verb)) :: O1b) a ->
  ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
  ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg verb]) <= a <
     c + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg verb]) + 8) ->
  rdW W6 mem6 a = rdW W4 (ms_mem ms5) a).
{ intros a Ha Hn1 Hn2. change (Z.of_nat (length [sarg verb])) with 1 in Hn2.
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hn1, Hn2.
  destruct Ha as [Ha | [Ha | ([q0 m0] & Hq0 & _ & Ha)]].
  - apply (Lcall_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ6c HFPG). left.
    split; [apply sb_recb_static; left; exact Ha|]. intros Hf. pose proof (HFP1 a Hf). lia.
  - apply (Lcall_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ6c HFPG). left.
    split; [apply sb_recb_static; right; exact Ha|]. intros Hf. pose proof (HFP1 a Hf). lia.
  - cbn [fst snd] in Ha. exact (KBLK6 q0 m0 a Hq0 Ha). }
assert (HREP6 : rec_repA B ly6 S6 (rdW W6 mem6)
  (rec_record R REC_CONNECT ([sarg verb] ++ [canon line]))
  ((q, Z.of_nat (length line) + 1) :: (p0, LIVE_XSTRDUP (sarg verb)) :: O1b)).
{ pose proof (scn_canon_len line) as Hcl.
  apply (scn_append_rep B ly4 S4 ly6 S6 (rdW W4 (ms_mem ms5)) (rdW W6 mem6) R REC_CONNECT [sarg verb]
    ((p0, LIVE_XSTRDUP (sarg verb)) :: O1b) c (canon line) q (Z.of_nat (length line) + 1) HREP4 Hpos).
  - cbn. lia.
  - lia.
  - exact Hqs.
  - lia.
  - lia.
  - exact Hqfresh.
  - unfold iv_apart, A_G_REC, REC_SIZE. lia.
  - unfold iv_apart, A_REC_SPILL, SC_SIZE. lia.
  - change (Z.of_nat (length [sarg verb]) + 1) with 2. exact Hqn.
  - change (Z.of_nat (length [sarg verb])) with 1. exact Hqa.
  - exact KREC2.
  - exact Hqperm. }
assert (Hnew2 : In (q, Z.of_nat (length line) + 1) (ablocks B ly S) -> In (q, Z.of_nat (length line) + 1) O).
{ intros Hin. apply (sb_new_in_O B LAWS ly S W mem md O [] ly4 S4 W4 (ms_mem ms5) mdv2 _ (spZ regs) SUP_CONNECT_STK
    q _ HAR HOin HJ4); [|exact Hin].
  intros Hin2. pose proof (proj1 (Forall_forall _ _) Hqfresh _ Hin2) as Hap. unfold iv_apart in Hap.
  cbn [fst snd] in Hap. lia. }
pose proof (sb_bk_step B ly S O _ _ ((p0, LIVE_XSTRDUP (sarg verb)) :: O1b) q _ HBK4 Hqperm Hnew2) as HBK6.
pose proof HJ6c as (_ & _ & _ & _ & _ & Hfr6c & _).
assert (Hfr6 : frames S6 = frames S) by (rewrite Hfr6c, Hfr4c; exact Hfr1).
assert (Hbb6' : blocks_bytes S6 + (LIVE_XSTRDUP (sarg port_a) + LIVE_XSTRDUP (sarg port_b) + LIVE_ANSWER t) <= LIVE_MAX)
by lia.
assert (Hlv6 : blocks_bytes S6 <= blocks_bytes S + (LIVE_XSTRDUP (sarg verb) + LIVE_ARG_LINE line)) by lia.
assert (MLE6 : mo_le MT S S6 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg verb) + XM_ARG_LINE MT line))
by exact (mle_station MT S S4 S6 _ _ MTL (mle_station MT S S1 S4 _ _ MTL MLE1 Hmle) Hmle6).
assert (HU19 : U E6 (SOff 19 0) = pa)
by (apply (U_atom E6 19 pa); [rewrite OLD6, OLD4 by lia; exact E19 | exact Hpa64]).
assert (HU0 : U E6 (SLit 0) = 0) by reflexivity.
(* 0x8ae30 .. 0x8ae44: the inline check of c->nargs, nargs > 5 (not taken), then the null check of port_a *)
paj_run_tok RUN HS HJ6 SHOK6 scn_Bspan.
{ awr_ok_tac. }
s6_set_md mdv3. s6_name_ms HS ms7.
pose proof (kept_of_frame (segs:=SEGS) E6 _ (w_H W6) mem6 (ms_mem ms7) (fun _ => False) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; lia|]); destruct Hin)) as KEEP7.
clear HF HFr HG.
s6_to_pi HS.
psrr_branch_tok RUN BR HS SHOK6 scn_Bspan.
- assert (Hpa0 : pa <> 0).
  { rewrite branch_ne_U, HU19, HU0 in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJ6 SHOK6 scn_Bspan SB_M2.
  { awr_ok_tac. }
  s6_set_md mdv4. s6_name_ms HS ms8.
  pose proof (kept_of_frame (segs:=SEGS) E6 _ (w_H W6) (ms_mem ms7) (ms_mem ms8) (fun _ => False) HFr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; lia|]); destruct Hin)) as KEEP8.
  clear HF HFr HG.
  s6_to_pi HS.
  prreg HS (19%bv : bv 5) Q19.
  assert (R19' : getr (ms_regs ms8) 19 = Z_to_bv 64 (if pa =? 0 then 0x22480 else pa)).
  { rewrite Q19, OLD6, OLD4, E19 by lia. rewrite (proj2 (Z.eqb_neq pa 0) Hpa0). reflexivity. }
  pmkst HS.
  pose proof (st_ok_pi_restrict_mkst (w_H W6) _ _ _ HS eq_refl) as Hms8. cbn [ss_pc] in Hms8.
  pose proof (sb_canon_ok W6 _ _ _ 80%nat [10; 19]%bv HS eq_refl ltac:(cbv; lia) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HC.
  rewrite Hms8 in HC.
  lazymatch type of HC with st_ok_pi _ _ _ ?ssx _ =>
    assert (HEQ : ssx = sb_C2) by (vm_compute; reflexivity); rewrite HEQ in HC; clear HEQ end.
  apply (SB2 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
    (havoc E6 80 (map (getr (ms_regs ms8)) [10; 19]%bv)) W6 (ms_regs ms8) (ms_mem ms8) mdv4 ly6 S6
    ((q, Z.of_nat (length line) + 1) :: (p0, LIVE_XSTRDUP (sarg verb)) :: O1b) (rdW W6 mem6) HCX HC).
  + split; [apply img_env_havoc; [exact HEI6 | cbv; lia]|].
    intros n Hn. rewrite YN3v.ew_havoc_old by lia. rewrite OLD6, OLD4 by lia. exact (HE0 n Hn).
  + unfold havoc. cbn [ew Nat.ltb Nat.leb Nat.sub nth map]. exact R19'.
  + split; [exact HJ6|]. split; [exact Hfr6|]. split; [exact Hbb6'|]. split; [exact Hlv6|].
    split; [exact MLE6|]. split; [exact HREP6|]. split; [|exact HBK6].
    intros a Ha. assert (Hr : 0 <= a < 2 ^ 64) by exact (sb_recb_rng B LAWS ly6 S6 W6 mem6 md6 _ a HAR6 Ha).
    rewrite (KEEP8 a Hr ltac:(tauto)). exact (KEEP7 a Hr ltac:(tauto)).
  + apply (sb_sstr_keep (ablocks B ly4 S4) _ (rdW W4 (ms_mem ms5)) _ _ _ HSAk KBL6).
    intros a (q0 & m0 & Hq0 & Ha).
    destruct (sb_in_blk_range B LAWS ly4 S4 W4 mem4 md4 q0 m0 a HAR4 Hq0 Ha) as (Ha1 & Ha2 & Ha3).
    assert (Hr : 0 <= a < 2 ^ 64) by lia.
    rewrite (KEEP8 a Hr ltac:(tauto)), (KEEP7 a Hr ltac:(tauto)). exact (KBLK6 q0 m0 a Hq0 Ha).
  + apply (sb_sstr_keep (ablocks B ly4 S4) _ (rdW W4 (ms_mem ms5)) _ _ _ HSBk KBL6).
    intros a (q0 & m0 & Hq0 & Ha).
    destruct (sb_in_blk_range B LAWS ly4 S4 W4 mem4 md4 q0 m0 a HAR4 Hq0 Ha) as (Ha1 & Ha2 & Ha3).
    assert (Hr : 0 <= a < 2 ^ 64) by lia.
    rewrite (KEEP8 a Hr ltac:(tauto)), (KEEP7 a Hr ltac:(tauto)). exact (KBLK6 q0 m0 a Hq0 Ha).
- assert (Hpa0 : pa = 0).
  { rewrite branch_ne_U, HU19, HU0 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJ6 SHOK6 scn_Bspan SB_M2.
  { awr_ok_tac. }
  s6_set_md mdv4. s6_name_ms HS ms8.
  pose proof (kept_of_frame (segs:=SEGS) E6 _ (w_H W6) (ms_mem ms7) (ms_mem ms8) (fun _ => False) HFr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; lia|]); destruct Hin)) as KEEP8.
  clear HF HFr HG.
  s6_to_pi HS.
  prreg HS (19%bv : bv 5) Q19.
  assert (R19' : getr (ms_regs ms8) 19 = Z_to_bv 64 (if pa =? 0 then 0x22480 else pa)).
  { rewrite Q19. rewrite (proj2 (Z.eqb_eq pa 0) Hpa0). apply bv_eq.
    rewrite (HEI6 293%nat ltac:(unfold A_TEXT, A_LIM; lia)).
    change (VAL 293%nat) with (VAL (A_OBJ 52)). rewrite (scn_obj52 VOBJS).
    rewrite unsigned_lit_small by lia. reflexivity. }
  pmkst HS.
  pose proof (st_ok_pi_restrict_mkst (w_H W6) _ _ _ HS eq_refl) as Hms8. cbn [ss_pc] in Hms8.
  pose proof (sb_canon_ok W6 _ _ _ 80%nat [10; 19]%bv HS eq_refl ltac:(cbv; lia) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HC.
  rewrite Hms8 in HC.
  lazymatch type of HC with st_ok_pi _ _ _ ?ssx _ =>
    assert (HEQ : ssx = sb_C2) by (vm_compute; reflexivity); rewrite HEQ in HC; clear HEQ end.
  apply (SB2 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
    (havoc E6 80 (map (getr (ms_regs ms8)) [10; 19]%bv)) W6 (ms_regs ms8) (ms_mem ms8) mdv4 ly6 S6
    ((q, Z.of_nat (length line) + 1) :: (p0, LIVE_XSTRDUP (sarg verb)) :: O1b) (rdW W6 mem6) HCX HC).
  + split; [apply img_env_havoc; [exact HEI6 | cbv; lia]|].
    intros n Hn. rewrite YN3v.ew_havoc_old by lia. rewrite OLD6, OLD4 by lia. exact (HE0 n Hn).
  + unfold havoc. cbn [ew Nat.ltb Nat.leb Nat.sub nth map]. exact R19'.
  + split; [exact HJ6|]. split; [exact Hfr6|]. split; [exact Hbb6'|]. split; [exact Hlv6|].
    split; [exact MLE6|]. split; [exact HREP6|]. split; [|exact HBK6].
    intros a Ha. assert (Hr : 0 <= a < 2 ^ 64) by exact (sb_recb_rng B LAWS ly6 S6 W6 mem6 md6 _ a HAR6 Ha).
    rewrite (KEEP8 a Hr ltac:(tauto)). exact (KEEP7 a Hr ltac:(tauto)).
  + apply (sb_sstr_keep (ablocks B ly4 S4) _ (rdW W4 (ms_mem ms5)) _ _ _ HSAk KBL6).
    intros a (q0 & m0 & Hq0 & Ha).
    destruct (sb_in_blk_range B LAWS ly4 S4 W4 mem4 md4 q0 m0 a HAR4 Hq0 Ha) as (Ha1 & Ha2 & Ha3).
    assert (Hr : 0 <= a < 2 ^ 64) by lia.
    rewrite (KEEP8 a Hr ltac:(tauto)), (KEEP7 a Hr ltac:(tauto)). exact (KBLK6 q0 m0 a Hq0 Ha).
  + apply (sb_sstr_keep (ablocks B ly4 S4) _ (rdW W4 (ms_mem ms5)) _ _ _ HSBk KBL6).
    intros a (q0 & m0 & Hq0 & Ha).
    destruct (sb_in_blk_range B LAWS ly4 S4 W4 mem4 md4 q0 m0 a HAR4 Hq0 Ha) as (Ha1 & Ha2 & Ha3).
    assert (Hr : 0 <= a < 2 ^ 64) by lia.
    rewrite (KEEP8 a Hr ltac:(tauto)), (KEEP7 a Hr ltac:(tauto)). exact (KBLK6 q0 m0 a Hq0 Ha).
Qed.

End e.
End f.
End d.
