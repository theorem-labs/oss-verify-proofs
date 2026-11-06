(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_after_reply on plugin-hostd/fuzz_command.asan (0x8c658, 100 instructions), in the shape of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (a seed state rebuilt from concrete facts at each return point) and A/ACh1.v (the segment walk of cgif_close: run, call, return); the entry seed and the slot's denotation after lib/A/Prog/sup_worker_list.v, two lemmas copied from lib/A/Prog/RecBLemmas.v; the named per-binary hypotheses take the one name and form per fact that the recorder walks share. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05 YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c xstrdup_c sup_after_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBTemplate.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas PaNoChain PaFx sup_after_reply_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
(* a register's symbolic value in a symbolic state, its denotation not normalised (the answer_code walk's preg,
   lib/A/Prog/answer_code.v) *)
Ltac sar_preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Open Scope Z_scope.

(* ---------- the layout of a resumed walk segment ---------- *)
(* the callee-saved registers the 64-byte frame holds, the j-th at sp0 - 8 - 8 * j (0x8c65c .. 0x8c674) *)
Definition sar_saved : list Z := [1; 8; 9; 18; 19; 20; 21].
(* the atoms above the 32 registers: 32 the shadow base, 33 the slot record() picked, 34 + j the entry value of
   the j-th saved register *)
Definition sar_extra (regs : bvmap 5 word) (c : Z) : list word :=
map (Z_to_bv 64) [SB; c] ++ map (fun r => getr regs (Z_to_bv 5 r)) sar_saved.
(* the frame, [sp, sp + 64) of the segment's sp = entry sp - 64, holding the saved registers (read only) *)
Definition sar_frame_r : YP09.region := YP09.mkRegion (Some 2%nat) 0 64 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 40 0)); YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0));
 YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0)); YP09.mkChunk 48 (CVal 8 (SOff 35 0));
 YP09.mkChunk 56 (CVal 8 (SOff 34 0))].
(* the slot's windows: JOIN writes fn and nargs, after arg_i the walk reads nargs = 1, after xstrdup it writes
   nargs and args[1] *)
Definition sar_slotJ : smem := [YP09.mkRegion (Some 33%nat) 0 8 0 8 []].
Definition sar_slotC : smem := [YP09.mkRegion (Some 33%nat) 4 8 4 4 [YP09.mkChunk 4 (CVal 4 (SLit 1))]].
Definition sar_slotD : smem :=
[YP09.mkRegion (Some 33%nat) 4 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit 1))]; YP09.mkRegion (Some 33%nat) 16 24 16 24 []].
Definition sar_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3)] [] [].
Definition sar_SH : list shent := [mkSHE 33 0 CALL_SIZE].
Definition sar_Bx : sv := SOff 32 0.
Definition sar_shx (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 o) (SLit 3)) (SOff 32 0).
(* the registers of a resumed segment: s1 = the slot, s4 = the shadow base; after arg_i also s2 = &c->nargs and
   s5 = its shadow byte's address *)
Definition sar_regsJ : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 9 (SOff 33 0)) 20 (SOff 32 0).
Definition sar_regsC : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 9 (SOff 33 0)) 20 (SOff 32 0)) 18 (SOff 33 4)) 21 (sar_shx 4).
(* listing offsets: the join of record()'s two arms, the returns of rec_calls_free, arg_i and xstrdup *)
Definition SAR_JOIN : Z := 0x61f0.
Definition SAR_RET_RCF : Z := 0x61d0.
Definition SAR_RET_ARGI : Z := 0x622c.
Definition SAR_RET_XS : Z := 0x6254.
(* the slot record() picks: an entry of g_rec's table, or record.spill *)
Definition sar_slot_ok (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.

Lemma sar_slot_bounds : forall c, sar_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0 /\
((A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL).
Proof.
intros c [(i & Hi & ->) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, REC_CALLS_MAX in *.
- split; [lia|]. split; [|left; lia].
  replace (6174528 + 16 + 56 * i) with ((771818 + 7 * i) * 8) by lia. apply Z_mod_mult.
- split; [lia|]. split; [reflexivity | right; reflexivity].
Qed.

Lemma sar_entry_ok : forall R, (length (r_calls R) <= 16)%nat -> sar_slot_ok (sar_entry R).
Proof.
intros R H. unfold sar_entry. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
- left. exists (Z.of_nat (length (r_calls R))). unfold REC_CALLS_MAX. split; [lia | reflexivity].
- right. reflexivity.
Qed.

Lemma sar_extra_nth : forall regs c j r, nth_error sar_saved j = Some r ->
nth (2 + j) (sar_extra regs c) (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof.
intros regs c j r Hj.
do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; reflexivity|]). destruct j; discriminate Hj.
Qed.

Lemma sar_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma sar_U_atom : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> U E (SOff m 0) = v.
Proof.
intros E m v Hm Hv. unfold U. cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned.
apply unsigned_lit_small. exact Hv.
Qed.

Lemma sar_in_of_existsb : forall (r : Z * Z) l,
existsb (fun r' => (fst r' =? fst r) && (snd r' =? snd r)) l = true -> In r l.
Proof.
intros [a b] l H. apply existsb_exists in H as ([a' b'] & Hin & E). cbn [fst snd] in E.
apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst. exact Hin.
Qed.

Lemma sar_in_of_existsbZ : forall (e : Z) l, existsb (Z.eqb e) l = true -> In e l.
Proof. intros e l H. apply existsb_exists in H as (y & Hy & E). apply Z.eqb_eq in E. subst. exact Hy. Qed.

Lemma sar_not_in_ranges : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
intros L lo hi HL a Ha HE. apply Exists_exists in HE as (r & Hr & Hin).
pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hb. cbn beta in Hb.
apply Bool.orb_true_iff in Hb. unfold in_zr in Hin.
destruct Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the saved registers in the frame below the entry sp *)
Definition sar_frame (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error sar_saved j = Some r -> aval_mem rd (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the registers of a resumed segment against the machine's *)
Ltac sar_regs_tac :=
apply regs_ok_by_cases; intros r Hr; cbv [all_regs In] in Hr;
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
    let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end
| ]); try (destruct Hr; fail).
Lemma sar_regsJ_ok : forall (regs regs1 : bvmap 5 word) c,
sar_slot_ok c -> getr regs1 9 = w64 c -> getr regs1 20 = w64 SB ->
regs_ok (Eimg (Ereg regs1 (sar_extra regs c))) sar_regsJ regs1.
Proof.
intros regs regs1 c Hc R9 R20.
set (E := Eimg (Ereg regs1 (sar_extra regs c))).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr)
  by (intros n rr Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
sar_regs_tac;
first [ rewrite sar_denot_off0; first [ symmetry; apply EE; reflexivity | rewrite E33; exact R9 | rewrite E32; exact R20 ]
      | reflexivity ].
Qed.
Lemma sar_regsC_ok : forall (regs regs1 : bvmap 5 word) c,
sar_slot_ok c -> getr regs1 9 = w64 c -> getr regs1 20 = w64 SB -> getr regs1 18 = w64 (c + 4) ->
getr regs1 21 = w64 (SB + (c + 4) / 8) ->
regs_ok (Eimg (Ereg regs1 (sar_extra regs c))) sar_regsC regs1.
Proof.
intros regs regs1 c Hc R9 R20 R18 R21.
destruct (sar_slot_bounds c Hc) as (Hcb & _). unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb.
set (E := Eimg (Ereg regs1 (sar_extra regs c))).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr)
  by (intros n rr Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (D18 : sv_denot E (SOff 33 4) = Z_to_bv 64 (c + 4)).
{ cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. reflexivity. }
assert (D21 : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 4) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + (c + 4) / 8)).
{ apply (denot_shx E 33 32 4 c SB E33 E32); unfold SB; lia. }
sar_regs_tac;
first [ rewrite sar_denot_off0; first [ symmetry; apply EE; reflexivity | rewrite E33; exact R9 | rewrite E32; exact R20 ]
      | rewrite D18; exact R18 | rewrite D21; exact R21 | reflexivity ].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_after_reply_c.v:62-65): the callees' contracts at every FP state *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
(* the per-binary facts the statement does not carry yet (lib/A/Prog/CmdRecFacts.v did not exist at an earlier
   commit), under the recorder walks' shared names and forms *)
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* the walk from arg_i's return to the end (segments C and D, the call of xstrdup): a callee that keeps the FP state
   follows arg_i, whose post is apost_baseF, so these lemmas hold at every ambient FP state (lib/A/Prog/PaFx.v's
   section (b), srr_after_callF_base) *)
Section g. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* the slot's bytes are marked usable: g_rec's table and record.spill are ranges of the record's zero shadow *)
Lemma sar_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> sar_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. destruct (sar_slot_bounds c Hc) as (_ & _ & [[Hlo Hhi] | ->]).
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) c CALL_SIZE HAR);
  [apply sar_in_of_existsb; vm_compute; reflexivity | reflexivity | reflexivity | cbn [fst snd] | cbn [fst snd]];
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia.
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) A_REC_SPILL CALL_SIZE HAR);
  [apply sar_in_of_existsb; vm_compute; reflexivity | reflexivity | reflexivity | cbn [fst snd] | cbn [fst snd]];
  unfold A_REC_SPILL, CALL_SIZE; lia.
Qed.

(* the seed of a resumed segment: the frame region and the slot's regions, from concrete facts *)
Lemma sar_seed : forall pc sregs (slot : smem) (Wc : world SEGS) (regs regs1 : bvmap 5 word) memc lyc Sc mdc c,
AR SEGS B lyc Sc Wc memc mdc ->
2 ^ 46 + 64 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
bv_unsigned (getr regs1 2) = spZ regs - 64 ->
regs_ok (Eimg (Ereg regs1 (sar_extra regs c))) sregs regs1 ->
sar_frame (rdW Wc memc) (spZ regs) regs ->
sar_slot_ok c ->
regions_wf (sar_frame_r :: slot) = true ->
Forall (region_ok SEGS (Eimg (Ereg regs1 (sar_extra regs c))) (mrestrict (w_H Wc) memc)) slot ->
pairwise_disjoint (Eimg (Ereg regs1 (sar_extra regs c))) (sar_frame_r :: slot) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (sar_extra regs c))) (mkSS pc sregs (sar_frame_r :: slot) None sar_facts)
(restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS sar_Bx sar_SH (Eimg (Ereg regs1 (sar_extra regs c))) (mrestrict (w_H Wc) memc).
Proof.
intros pc sregs slot Wc regs regs1 memc lyc Sc mdc c HAR Hsp Hsp16 Hsp1 HREG HFR Hc Hwf HSL HPD.
destruct (sar_slot_bounds c Hc) as (Hcb & Hc8 & _).
set (E := Eimg (Ereg regs1 (sar_extra regs c))) in *.
assert (ES : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (sar_extra regs c) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = getr regs1 2) by (unfold E; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (exact (ES 0%nat ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (exact (ES 1%nat ltac:(lia))).
assert (U2 : base_val E (Some 2%nat) = spZ regs - 64) by (cbn [base_val]; rewrite E2; exact Hsp1).
rewrite restrict_mkst_fx. split.
- apply pa_entry_st_ok_full.
  + exact HREG.
  + exact Hwf.
  + apply Forall_cons; [|exact HSL].
    unfold sar_frame_r, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    assert (HFJ : forall (j : nat) r, nth_error sar_saved j = Some r ->
      YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs - 64)
        (YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (34 + j) 0)))).
    { intros j r Hj.
      assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some sar_saved j)); rewrite Hj; discriminate).
      apply (chunk_ok_val SEGS E _ (spZ regs - 64) (56 - 8 * Z.of_nat j) 8 _ (bv_unsigned (getr regs (Z_to_bv 5 r)))).
      - rewrite sar_denot_off0. replace (34 + j)%nat with (32 + (2 + j))%nat by lia. rewrite (ES (2 + j)%nat ltac:(lia)).
        rewrite (sar_extra_nth regs c j r Hj). symmetry. apply Z_to_bv_bv_unsigned.
      - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR. change (bv_modulus 64) with (2 ^ 64) in HR. cbn. lia.
      - cbn. lia.
      - replace (spZ regs - 64 + (56 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
        exact (val_mem_view SEGS (w_H Wc) memc _ 8 _ (HFR j r Hj)). }
    repeat apply Forall_cons; try apply Forall_nil.
    * exact (HFJ 6%nat 21 eq_refl).
    * exact (HFJ 5%nat 20 eq_refl).
    * exact (HFJ 4%nat 19 eq_refl).
    * exact (HFJ 3%nat 18 eq_refl).
    * exact (HFJ 2%nat 9 eq_refl).
    * exact (HFJ 1%nat 8 eq_refl).
    * exact (HFJ 0%nat 1 eq_refl).
  + exact HPD.
  + split; [|split; exact I].
    cbn [sar_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    assert (Uc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit_small; unfold A_REC_SPILL, A_G_REC, OFF_CALLS in Hcb; lia).
    rewrite E2, E32, E33, Hsp1, Uc, unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia. rewrite Z_mod_plus_full.
    unfold SB, A_REC_SPILL, A_G_REC, OFF_CALLS in *.
    repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
- unfold sh_ok, sar_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H Wc) memc E sar_Bx 33 c CALL_SIZE c 0 CALL_SIZE).
  + exact (sar_slot_addressable lyc Sc Wc memc mdc c HAR Hc).
  + unfold sar_Bx. apply sar_U_atom; [exact E32 | cbv [SB SHADOW_OFF]; lia].
  + apply sar_U_atom; [exact E33 | unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE, SHADOW_OFF, A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia.
Qed.

(* every byte of g_rec / record.spill is a write the footprint names: the core's program-static disjunct of awr_byte *)
Definition sar_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
Lemma sar_in_PG : forall a, in_rec a -> Exists (in_zr a) recb_PG.
Proof.
intros a [Ha | Ha]; apply Exists_exists; unfold recb_PG.
- exists (A_G_REC, REC_SIZE). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
- exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma sar_inFP_rec : forall O a, in_rec a -> inFP (sar_FP O) a.
Proof.
intros O a [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.
Lemma sar_awr_rec : forall STK sp0 O bl0 blc fr0 lyc own a, in_rec a ->
awr_byte SEGS B STK sp0 (sar_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha. unfold awr_byte, awr_prog_or_caller.
right; right; right; right; left. split; [exact (sar_inFP_rec O a Ha)|].
split; [rewrite (recb_ts_prog_m B HB); exact (sar_in_PG a Ha) | exact (cmd_prog_img a (sar_in_PG a Ha))].
Qed.

(* the post of the statement (sup_after_reply_c.v:91-104) *)
Definition sar_post ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (id : Z)
(verb : option (list byte)) : world SEGS -> config -> Prop :=
apost_base SEGS B SUP_AFTER_REPLY_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_AFTER_REPLY R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 rec_repA B ly' S' (rdW W' mem') (sup_after_reply_m R id verb) O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_AFTER_REPLY id verb /\
 mo_le MT S S' (XM_SUP_AFTER_REPLY MT R id verb)).

(* ---------- segment D: after xstrdup (0x8c738) to the return ---------- *)
(* c->nargs := 2 and c->args[1] := the copy (the second inline arg_s), then the epilogue *)
Lemma sar_seg_D : forall ly S W regs mem md ch R O id verb lyc Sc Wc (regs2 : bvmap 5 word) mem2 md2 kc c Q2 q,
afn_pre SEGS B SUP_AFTER_REPLY_STK ly S W regs mem md ch ->
ajournal SEGS B SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) ly S W mem md [] lyc Sc Wc mem2 md2 kc ->
kc <= EV_SUP_AFTER_REPLY R ->
getr regs2 2 = w64 (spZ regs - 64) -> getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
(forall r, 22 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr regs2 9 = w64 c -> getr regs2 18 = w64 (c + 4) -> getr regs2 20 = w64 SB ->
getr regs2 21 = w64 (SB + (c + 4) / 8) -> getr regs2 10 = w64 q ->
sar_frame (rdW Wc mem2) (spZ regs) regs ->
c = sar_entry R -> (length (r_calls R) <= 16)%nat ->
aval_mem (rdW Wc mem2) (c + CALL_OFF_NARGS) 4 1 ->
arep_at (ablocks B lyc Sc) (rdW Wc mem2) A_G_REC A_REC_SPILL (rec_record R REC_AFTER_REPLY [dec id]) Q2 ->
In (q, Z.of_nat (length (sarg verb)) + 1) (ablocks B lyc Sc) -> 4096 <= q ->
astr_atR (rdW Wc mem2) q (sarg verb) -> Z.of_nat (length (sarg verb)) <= LMAX ->
~ In q (map fst (lay_blocks Q2)) ->
(forall pn, In pn (lay_blocks Q2) -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(In (q, Z.of_nat (length (sarg verb)) + 1) O \/ ~ In (q, Z.of_nat (length (sarg verb)) + 1) (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Q2) \/
   pn = (q, Z.of_nat (length (sarg verb)) + 1)) ->
mo_le MT S Sc (XM_SUP_AFTER_REPLY MT R id verb) -> blocks_bytes Sc <= blocks_bytes S + LIVE_SUP_AFTER_REPLY id verb ->
SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + SAR_RET_XS)) mem2 (seg_rom SEGS)) md2)
(sar_post ly S W regs mem md R O id verb).
Proof.
intros ly S W regs mem md ch R O id verb lyc Sc Wc regs2 mem2 md2 kc c Q2 q
HPRE HJ Hkc R2 R3 R4 Rhi R9 R18 R20 R21 R10 HFR Hc Hlen HNA HQ2 Hq Hq4 Hqs Hlx Hqf HO1 HO2 HO3 HO4 HMLE HBBD.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
assert (HcOK : sar_slot_ok c) by (rewrite Hc; apply sar_entry_ok; exact Hlen).
destruct (sar_slot_bounds c HcOK) as (Hcb & Hc8 & Hcr). unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb.
assert (HSTK : SUP_AFTER_REPLY_STK = 64 + Z.max REC_CALLS_FREE_STK (Z.max ARG_I_STK XSTRDUP_STK)) by reflexivity.
assert (HSTKv : SUP_AFTER_REPLY_STK = 16592) by (vm_compute; reflexivity).
assert (Hsp : 2 ^ 46 + 64 <= spZ regs <= 2 ^ 47) by (unfold YG0f.ASAN_CEIL in *; lia).
assert (Hsp1 : bv_unsigned (getr regs2 2) = spZ regs - 64) by (rewrite R2; apply unsigned_lit_small; lia).
set (E := Eimg (Ereg regs2 (sar_extra regs c))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (ES : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (sar_extra regs c) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros n rr Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (exact (ES 1%nat ltac:(lia))).
assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 64) by (rewrite (EEo 2%nat 2%bv eq_refl); exact Hsp1).
assert (HSL : Forall (region_ok SEGS E (mrestrict (w_H Wc) mem2)) sar_slotD).
{ unfold sar_slotD. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U33.
  - split; [lia|]. split; [lia|]. split.
    + intros o Ho. apply (cmd_prog_writable lyc Sc Wc mem2 md2 (c + o) HAR). apply sar_in_PG.
      unfold in_rec. destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia.
    + constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c 4 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia|].
      exact (val_mem_view SEGS (w_H Wc) mem2 _ 4 1 HNA).
  - split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (cmd_prog_writable lyc Sc Wc mem2 md2 (c + o) HAR). apply sar_in_PG.
    unfold in_rec. destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia. }
assert (HPD : pairwise_disjoint E (sar_frame_r :: sar_slotD)).
{ apply pairwise_disjoint_of_extents. unfold sar_frame_r, sar_slotD, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_REC_SPILL, YG0f.ASAN_CEIL in *. repeat split; lia. }
destruct (sar_seed SAR_RET_XS sar_regsC sar_slotD Wc regs regs2 mem2 lyc Sc md2 c HAR Hsp Hal16 Hsp1
  (sar_regsC_ok regs regs2 c HcOK R9 R20 R18 R21) HFR HcOK ltac:(vm_compute; reflexivity) HSL HPD) as [HS SHOK].
fold E in HS, SHOK.
assert (EX : forall j r, nth_error sar_saved j = Some r -> ew E (34 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj. assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some sar_saved j)); rewrite Hj; discriminate).
  replace (34 + j)%nat with (32 + (2 + j))%nat by lia. rewrite (ES (2 + j)%nat ltac:(lia)). exact (sar_extra_nth regs c j r Hj). }
assert (E34 : ew E 34 = getr regs 1) by exact (EX 0%nat 1 eq_refl).
assert (E35 : ew E 35 = getr regs 8) by exact (EX 1%nat 8 eq_refl).
assert (E36 : ew E 36 = getr regs 9) by exact (EX 2%nat 9 eq_refl).
assert (E37 : ew E 37 = getr regs 18) by exact (EX 3%nat 18 eq_refl).
assert (E38 : ew E 38 = getr regs 19) by exact (EX 4%nat 19 eq_refl).
assert (E39 : ew E 39 = getr regs 20) by exact (EX 5%nat 20 eq_refl).
assert (E40 : ew E 40 = getr regs 21) by exact (EX 6%nat 21 eq_refl).
clearbody E.
unfold SAR_RET_XS in HS |- *.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 33%nat); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply sar_awr_rec. unfold in_rec.
    destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr in *; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia. }
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 33%nat); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply sar_awr_rec. unfold in_rec.
    destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr in *; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia. }
  apply (awr_ok_nil SEGS B). }
(* the registers at the return *)
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2'. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
(* the slot's two written fields *)
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) sar_frame_r) in
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) sar_frame_r) in
  pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRD1;
  pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HRD2;
  cbn [ms_mem restrict mkst] in HRD1, HRD2
end.
lazymatch goal with HFx : frame_of E _ (mrestrict _ mem2) (mrestrict _ ?m3) |- _ => rename HFx into HFr3; set (mem3 := m3) in * end.
pose proof (field_of_region (segs := SEGS) E _ 33 c _ _ _ _ _ 4 4 (SLit 2) 2 HRD1 U33 ltac:(cbn; tauto) eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)) as VN.
assert (E10 : sv_denot E (SOff 10 0) = Z_to_bv 64 q) by (rewrite sar_denot_off0, (EEo 10%nat 10%bv eq_refl); exact R10).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q _ HAR Hq) as (Hq16 & Hq4096 & Hqceil & Hqapp & Hqpres & _).
pose proof (req_size_pos (Z.of_nat (length (sarg verb)) + 1) ltac:(lia)) as [Hqr0 Hqr1].
assert (Hqb : 4096 <= q < 2 ^ 47) by (unfold YG0f.ASAN_CEIL in *; lia).
pose proof (field_of_region (segs := SEGS) E _ 33 c _ _ _ _ _ 16 8 (SOff 10 0) q HRD2 U33 ltac:(cbn; tauto) E10
  ltac:(cbn; lia) ltac:(cbn; lia)) as VA.
change (N.to_nat 4) with 4%nat in VN. change (N.to_nat 8) with 8%nat in VA.
apply (aval_mem_view SEGS) in VN, VA.
(* every byte outside the two fields is kept *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 4 <= a < c + 8) -> ~ (c + 16 <= a < c + 24) ->
  rdW Wc mem3 a = rdW Wc mem2 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) mem2 mem3 (fun a => (c + 4 <= a < c + 8) \/ (c + 16 <= a < c + 24)) HFr3);
  [ | exact Ha | intros [H|H]; [exact (H1 H) | exact (H2 H)] ].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hqq | Hin]; [injection Hqq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U33 in Hrr;
    first [lia | left; lia | right; lia] |]).
  destruct Hin. }
assert (HBLK : forall p n i, In (p, n) (ablocks B lyc Sc) -> 0 <= i < n -> rdW Wc mem3 (p + i) = rdW Wc mem2 (p + i)).
{ intros p n i Hpn Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & Hp4096 & Hpceil & _).
  pose proof (blk_off_imgP B _ _ _ _ _ p n HAR Hpn) as Hoff. pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
  unfold off_img in Hoff.
  apply KEEP; destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia. }
(* the model step: the second argument *)
set (x := sarg verb) in *. set (k := Z.of_nat (length x) + 1) in *.
assert (HQin : forall pn, In pn (lay_blocks Q2) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (rec_repA_in B lyc Sc (rdW Wc mem2) (rec_record R REC_AFTER_REPLY [dec id]) (lay_blocks Q2));
  [exists Q2; split; [exact HQ2 | intros pn'; reflexivity] | exact Hpn]. }
assert (P1 : aval_mem (rdW Wc mem3) (sar_entry R + CALL_OFF_NARGS) 4 (Z.of_nat (length [dec id]) + 1)).
{ rewrite <- Hc. cbn [length]. change (Z.of_nat 1 + 1) with 2. exact VN. }
assert (P2 : aval_mem (rdW Wc mem3) (sar_entry R + CALL_OFF_ARGS + 8 * Z.of_nat (length [dec id])) 8 q).
{ rewrite <- Hc. cbn [length]. unfold CALL_OFF_ARGS. replace (c + 8 + 8 * Z.of_nat 1) with (c + 16) by lia. exact VA. }
assert (P3 : forall a, in_rec a ->
   ~ (sar_entry R + CALL_OFF_NARGS <= a < sar_entry R + CALL_OFF_NARGS + 4) ->
   ~ (sar_entry R + CALL_OFF_ARGS + 8 * Z.of_nat (length [dec id]) <= a <
      sar_entry R + CALL_OFF_ARGS + 8 * Z.of_nat (length [dec id]) + 8) ->
   rdW Wc mem3 a = rdW Wc mem2 a).
{ intros a Ha H1 H2. rewrite <- Hc in H1, H2. cbn [length] in H2. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in H1, H2.
  apply KEEP; [unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia | lia | lia]. }
assert (P4 : blocks_keptA (ablocks B lyc Sc) (rdW Wc mem2) (rdW Wc mem3) (lay_blocks Q2)).
{ intros pn Hpn. split; [exact (HQin pn Hpn)|]. intros i Hi. destruct pn as [p n]. cbn [fst snd] in *.
  exact (HBLK p n i (HQin _ Hpn) Hi). }
assert (P5 : astr_atR (rdW Wc mem3) q x).
{ apply (rastr_kept (rdW Wc mem2)); [exact Hqs|]. intros i Hi. apply (HBLK q k i Hq). unfold k; lia. }
pose proof (blk_off_imgP B _ _ _ _ _ q k HAR Hq) as Hqoff. pose proof (req_size_pos k ltac:(unfold k; lia)) as [_ Hqreq].
unfold off_img in Hqoff.
assert (P6 : iv_apart q k A_G_REC REC_SIZE) by (unfold iv_apart, A_G_REC, REC_SIZE; lia).
assert (P7 : iv_apart q k A_REC_SPILL SC_SIZE) by (unfold iv_apart, A_REC_SPILL, SC_SIZE; lia).
destruct (sar_rep_arg (ablocks B lyc Sc) (ablocks B lyc Sc) (rdW Wc mem2) (rdW Wc mem3) R REC_AFTER_REPLY [dec id] Q2 x q k
  HQ2 Hlen ltac:(cbn; lia) P1 P2 P3 P4 Hqf ltac:(lia) Hq P5 Hlx ltac:(unfold k; lia) P6 P7) as (Qf & HQf & HQfi).
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold sar_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyc, Sc, r, m, d end.
split.
{ rewrite Q1, E34. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). eapply (ajournal_mono_k SEGS B); [exact HJ | exact Hkc]. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hr' as [-> | Hr']); try (subst r).
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2', U2.
    replace (spZ regs - 64 + 64) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q3, (EEo 3%nat 3%bv eq_refl), R3. symmetry. exact Hgp.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q4, (EEo 4%nat 4%bv eq_refl), R4. symmetry. exact Htp.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8, E35. reflexivity.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q9, E36. reflexivity.
  - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q18, E37. reflexivity.
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q19, E38. reflexivity.
  - replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q20, E39. reflexivity.
  - replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q21, E40. reflexivity.
  - rewrite <- (Rhi 22 ltac:(lia)). replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q22, (EEo 22%nat 22%bv eq_refl). reflexivity.
  - rewrite <- (Rhi 23 ltac:(lia)). replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q23, (EEo 23%nat 23%bv eq_refl). reflexivity.
  - rewrite <- (Rhi 24 ltac:(lia)). replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q24, (EEo 24%nat 24%bv eq_refl). reflexivity.
  - rewrite <- (Rhi 25 ltac:(lia)). replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q25, (EEo 25%nat 25%bv eq_refl). reflexivity.
  - rewrite <- (Rhi 26 ltac:(lia)). replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q26, (EEo 26%nat 26%bv eq_refl). reflexivity.
  - rewrite <- (Rhi 27 ltac:(lia)). replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q27, (EEo 27%nat 27%bv eq_refl). reflexivity. }
exists (lay_blocks Qf). split.
{ exists Qf. split; [|intros pn; reflexivity]. unfold sup_after_reply_m. exact HQf. }
split.
{ intros pn Hpn. apply HQfi in Hpn as [Hpn | ->]; [exact (HO1 pn Hpn) | exact HO2]. }
split; [exact HO3|].
split.
{ intros pn Hpn. destruct (HO4 pn Hpn) as [H | [H | ->]]; [left; exact H | right; apply HQfi; left; exact H | right; apply HQfi; right; reflexivity]. }
split; [exact HBBD | exact HMLE].
Qed.

(* ---------- what a callee's journal keeps ---------- *)
Lemma sar_prog_unowned : forall a, in_rec a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. split; [exact (cmd_prog_img a (sar_in_PG a Ha))|].
rewrite (AF0m.ts_owned B HB), (AF0m.ts_errno B HB). unfold AF0m.TFIB_ERRNO.
destruct Ha as [Ha | Ha]; split.
- apply (sar_not_in_ranges _ A_G_REC (A_G_REC + REC_SIZE)); [vm_compute; reflexivity | exact Ha].
- unfold A_G_REC, REC_SIZE in Ha. lia.
- apply (sar_not_in_ranges _ A_REC_SPILL (A_REC_SPILL + SC_SIZE)); [vm_compute; reflexivity | exact Ha].
- unfold A_REC_SPILL, SC_SIZE in Ha. lia.
Qed.
Lemma sar_jkeep_rec : forall STK1 sp1 FP1 ly1 S1 (W1 : world SEGS) mem1 md1 own ly2 S2 W2 mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 ly1 S1 W1 mem1 md1 own ly2 S2 W2 mem2 md2 k1 ->
~ YI16.sink_open_fp FP1 -> in_rec a -> ~ inFP FP1 a -> rdW W2 mem2 a = rdW W1 mem1 a.
Proof.
intros STK1 sp1 FP1 ly1 S1 W1 mem1 md1 own ly2 S2 W2 mem2 md2 k1 a HJ Hso Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (sar_prog_unowned a Ha) as (Hi & Ho & He).
exact (F3 a Hi Ho He (fp_spares_closed FP1 a Hso Hn)).
Qed.
Lemma sar_frame_kept : forall (rd rd' : reader) sp0 regs0,
sar_frame rd sp0 regs0 -> (forall a, sp0 - 64 <= a < sp0 -> rd' a = rd a) -> sar_frame rd' sp0 regs0.
Proof.
intros rd rd' sp0 regs0 HF HK j r Hj. pose proof (HF j r Hj) as V.
assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some sar_saved j)); rewrite Hj; discriminate).
apply (aval_mem_kept rd); [exact V|]. intros k Hk. apply HK. lia.
Qed.
Lemma sar_sig : forall s, In s cmd_prog_syms -> SIG s = BASE + cmd_af s.
Proof. intros s Hs. exact (SIGP s Hs). Qed.
Lemma sar_sig_xstrdup : SIG CS_xstrdup = BASE + AF_xstrdup.
Proof. rewrite (sar_sig CS_xstrdup ltac:(vm_compute; repeat (first [left; reflexivity | right]))). reflexivity. Qed.
Lemma sar_sig_arg_i : SIG CS_arg_i = BASE + AF_arg_i.
Proof. rewrite (sar_sig CS_arg_i ltac:(vm_compute; repeat (first [left; reflexivity | right]))). reflexivity. Qed.
Lemma sar_sig_rcf : SIG CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. rewrite (sar_sig CS_rec_calls_free ltac:(vm_compute; repeat (first [left; reflexivity | right]))). reflexivity. Qed.

(* ---------- the call of xstrdup (0x8c734) and what follows ---------- *)
Lemma sar_call_XS : forall ly S W regs mem md ch R O id verb lyc Sc Wc (regsx : bvmap 5 word) memx mdx kc c Q2 p,
afn_pre SEGS B SUP_AFTER_REPLY_STK ly S W regs mem md ch ->
ajournal SEGS B SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) ly S W mem md [] lyc Sc Wc memx mdx kc ->
kc <= rec_spill_frees R + EV_ARG_I ->
st_nev S + EV_SUP_AFTER_REPLY R <= EV_MAX ->
blocks_bytes Sc + LIVE_XSTRDUP (sarg verb) <= LIVE_MAX ->
mo_ok MT S (XM_SUP_AFTER_REPLY MT R id verb) ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT + XM_ARG_I MT id) ->
blocks_bytes Sc <= blocks_bytes S + LIVE_ARG_I id ->
getr regsx 2 = w64 (spZ regs - 64) -> getr regsx 3 = w64 (as_gp B) -> getr regsx 4 = w64 (as_tp B) ->
(forall r, 22 <= r <= 27 -> getr regsx (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr regsx 9 = w64 c -> getr regsx 18 = w64 (c + 4) -> getr regsx 20 = w64 SB ->
getr regsx 21 = w64 (SB + (c + 4) / 8) -> getr regsx 10 = w64 p ->
getr regsx 1 = Z_to_bv 64 (BASE + SAR_RET_XS) ->
s0Z regsx < alloc_ceiling ->
sar_frame (rdW Wc memx) (spZ regs) regs ->
c = sar_entry R -> (length (r_calls R) <= 16)%nat ->
aval_mem (rdW Wc memx) (c + CALL_OFF_NARGS) 4 1 ->
arep_at (ablocks B lyc Sc) (rdW Wc memx) A_G_REC A_REC_SPILL (rec_record R REC_AFTER_REPLY [dec id]) Q2 ->
arodata_okP SEGS RLO RHI B (rdW Wc memx) ->
astr_argA B lyc Sc (rdW Wc memx) (in_roP SEGS RLO RHI) [] p (Some (sarg verb)) ->
atail_vis SEGS Wc memx (p + Z.of_nat (length (sarg verb))) ->
(forall pn, In pn (lay_blocks Q2) -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Q2)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B lyc Sc) -> In pn O) ->
SRr SEGS Wc (mkCfg (mkst regsx (Z_to_bv 64 (SIG CS_xstrdup)) memx (seg_rom SEGS)) mdx)
(sar_post ly S W regs mem md R O id verb).
Proof.
intros ly S W regs mem md ch R O id verb lyc Sc Wc regsx memx mdx kc c Q2 p
HPRE HJ Hkc HEV HLIVE HMOK HMLE HBBX R2 R3 R4 Rhi R9 R18 R20 R21 R10 R1 Hs0 HFR Hc Hlen HNA HQ2 HROD HSTR HTAIL HO1 HO3 HO4 HO5.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof (proj1 HJ) as HAR.
assert (HSTKv : SUP_AFTER_REPLY_STK = 16592) by (vm_compute; reflexivity).
assert (HXSv : XSTRDUP_STK = 16416) by (vm_compute; reflexivity).
assert (Hsp : 2 ^ 46 + 64 <= spZ regs <= 2 ^ 47) by (unfold YG0f.ASAN_CEIL in *; lia).
assert (Psp : spZ regsx = spZ regs + -64) by (unfold spZ at 1; rewrite R2; rewrite unsigned_lit_small by lia; lia).
assert (Hnev : st_nev Sc + EV_XSTRDUP <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). unfold EV_SUP_AFTER_REPLY, EV_ARG_I, EV_XSTRDUP in *. lia. }
assert (HMOKx : mo_ok MT Sc (XM_XSTRDUP MT (sarg verb))).
{ apply (mok_station MT S Sc (XM_SUP_AFTER_REPLY MT R id verb) (rec_spill_frees R * mo_free MT + XM_ARG_I MT id) _ MTL HMOK HMLE).
  - unfold XM_XSTRDUP. apply (mo_malloc_nonneg MT MTL). lia.
  - unfold XM_SUP_AFTER_REPLY. lia. }
assert (Hlx : Z.of_nat (length (sarg verb)) <= LMAX) by (destruct HSTR as (_ & _ & Hn & _); unfold LMAX in *; lia).
rewrite sar_sig_xstrdup.
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsx memx _ SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) ly S W mem md [] lyc Sc mdx kc
    XSTRDUP_STK [] EV_XSTRDUP (-64) (Z_to_bv 64 (BASE + SAR_RET_XS)) []
    (fun ly' S' W' regs' mem' md' => exists p' : Z,
       getr regs' 10 = w64 p' /\ 4096 <= p' < 2 ^ 64 /\
       Permutation (ablocks B ly' S') ((p', LIVE_XSTRDUP (sarg verb)) :: ablocks B lyc Sc) /\
       Forall (fun qk => iv_apart p' (LIVE_XSTRDUP (sarg verb)) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
       in_blockA (ablocks B ly' S') p' (LIVE_XSTRDUP (sarg verb)) /\
       astr_atR (rdW W' mem') p' (sarg verb) /\ astr_atR (rdW W' mem') p (sarg verb) /\
       blocks_bytes S' <= blocks_bytes Sc + LIVE_XSTRDUP (sarg verb) /\
       mo_le MT Sc S' (XM_XSTRDUP MT (sarg verb))) HJ Psp);
  [ reflexivity | lia | unfold XSTRDUP_STK, ASTACK; lia | rewrite HSTKv, HXSv; lia
  | exact R3 | exact R4 | exact R1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]
  | unfold SAR_RET_XS; rewrite unsigned_lit_small by lia; lia
  | left; split; [left; exact Hs0 | reflexivity]
  | intros HPREx; eapply SRr_mono;
    [ apply (TXSTRDUP fx lyc Sc Wc regsx memx mdx [] p (sarg verb) HPREx
        HROD R10 (or_introl HSTR) HTAIL Hnev
        ltac:(exact HLIVE) HMOKx)
    | cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
      exists ly3, S3, regs3, mem3, md3; split; [rewrite R1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
  | intros a (r & Hr & _); destruct Hr ]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJi & HP2 & HK2).
destruct HK2 as (q & Q10 & [Hq4 Hq64] & Hperm & Hapart & _ & Hqs & Hps & HBB2 & HMLE2).
pose proof HJi as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _).
assert (Hso0 : ~ YI16.sink_open_fp ([] : list (Z * Z))) by (intros (r & Hr & _); destruct Hr).
assert (HnF0 : forall a, ~ inFP ([] : list (Z * Z)) a) by (intros a (r & Hr & _); destruct Hr).
(* the registers the call keeps *)
assert (PR : forall n, acallee_saved n -> getr regs2 (Z_to_bv 5 n) = getr regsx (Z_to_bv 5 n)) by exact HP2.
assert (X2 : getr regs2 2 = w64 (spZ regs - 64)).
{ pose proof (PR 2 ltac:(unfold acallee_saved; lia)) as P. replace (Z_to_bv 5 2) with (2%bv : bv 5) in P by (apply bv_eq; reflexivity). rewrite P. exact R2. }
assert (X3 : getr regs2 3 = w64 (as_gp B)).
{ pose proof (PR 3 ltac:(unfold acallee_saved; lia)) as P. replace (Z_to_bv 5 3) with (3%bv : bv 5) in P by (apply bv_eq; reflexivity). rewrite P. exact R3. }
assert (X4 : getr regs2 4 = w64 (as_tp B)).
{ pose proof (PR 4 ltac:(unfold acallee_saved; lia)) as P. replace (Z_to_bv 5 4) with (4%bv : bv 5) in P by (apply bv_eq; reflexivity). rewrite P. exact R4. }
assert (X9 : getr regs2 9 = w64 c).
{ pose proof (PR 9 ltac:(unfold acallee_saved; lia)) as P. replace (Z_to_bv 5 9) with (9%bv : bv 5) in P by (apply bv_eq; reflexivity). rewrite P. exact R9. }
assert (X18 : getr regs2 18 = w64 (c + 4)).
{ pose proof (PR 18 ltac:(unfold acallee_saved; lia)) as P. replace (Z_to_bv 5 18) with (18%bv : bv 5) in P by (apply bv_eq; reflexivity). rewrite P. exact R18. }
assert (X20 : getr regs2 20 = w64 SB).
{ pose proof (PR 20 ltac:(unfold acallee_saved; lia)) as P. replace (Z_to_bv 5 20) with (20%bv : bv 5) in P by (apply bv_eq; reflexivity). rewrite P. exact R20. }
assert (X21 : getr regs2 21 = w64 (SB + (c + 4) / 8)).
{ pose proof (PR 21 ltac:(unfold acallee_saved; lia)) as P. replace (Z_to_bv 5 21) with (21%bv : bv 5) in P by (apply bv_eq; reflexivity). rewrite P. exact R21. }
assert (Xhi : forall r, 22 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (PR r ltac:(unfold acallee_saved; lia)). exact (Rhi r Hr). }
(* what the call keeps in memory *)
assert (KR : forall a, in_rec a -> rdW W2 mem2 a = rdW Wc memx a)
  by (intros a Ha; exact (sar_jkeep_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi Hso0 Ha (HnF0 a))).
assert (KF : forall a, spZ regs - 64 <= a < spZ regs -> rdW W2 mem2 a = rdW Wc memx a).
{ intros a Ha. apply F1; [unfold YG0f.ASAN_CEIL in *; lia | rewrite HXSv; lia | exact (HnF0 a)]. }
assert (HQin : forall pn, In pn (lay_blocks Q2) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (rec_repA_in B lyc Sc (rdW Wc memx) (rec_record R REC_AFTER_REPLY [dec id]) (lay_blocks Q2));
  [exists Q2; split; [exact HQ2 | intros pn'; reflexivity] | exact Hpn]. }
assert (Hin2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn. eapply Permutation_in; [apply Permutation_sym; exact Hperm|]. right. exact Hpn. }
assert (KB : forall p0 n0 i, In (p0, n0) (lay_blocks Q2) -> 0 <= i < n0 -> rdW W2 mem2 (p0 + i) = rdW Wc memx (p0 + i)).
{ intros p0 n0 i Hpn Hi. pose proof (HQin _ Hpn) as Hpc. pose proof (req_size_pos n0 ltac:(lia)) as [_ Hreq].
  apply (F2 p0 n0 i Hpc (Hin2 _ Hpc)); [lia | exact (HnF0 _)]. }
set (k := Z.of_nat (length (sarg verb)) + 1) in *.
assert (Hq : In (q, k) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (Hqf : ~ In q (map fst (lay_blocks Q2))).
{ intros Hin. apply in_map_iff in Hin as ([b m] & Eb & Hbm). cbn [fst] in Eb. subst b.
  pose proof (sar_lay_pos _ _ _ _ HQ2 (q, m) Hbm) as Hm. cbn [snd] in Hm.
  pose proof (proj1 (Forall_forall _ _) Hapart (q, m) (HQin _ Hbm)) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, LIVE_XSTRDUP in Hap. unfold k in *. lia. }
apply (sar_seg_D ly S W regs mem md ch R O id verb ly2 S2 W2 regs2 mem2 md2 (kc + EV_XSTRDUP) c Q2 q HPRE HJ2).
- unfold EV_SUP_AFTER_REPLY, EV_ARG_I, EV_XSTRDUP in *. lia.
- exact X2. - exact X3. - exact X4. - exact Xhi. - exact X9. - exact X18. - exact X20. - exact X21. - exact Q10.
- apply (sar_frame_kept (rdW Wc memx)); [exact HFR | exact KF].
- exact Hc. - exact Hlen.
- apply (aval_mem_kept (rdW Wc memx)); [exact HNA|]. intros kk Hkk. apply KR.
  pose proof (sar_entry_ok R Hlen) as HcOK. rewrite <- Hc in HcOK. destruct (sar_slot_bounds c HcOK) as (_ & _ & [[Hl Hh] | ->]);
  unfold in_rec, CALL_OFF_NARGS, A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia.
- apply (sar_arep_kept (ablocks B lyc Sc) _ (rdW Wc memx)); [exact HQ2 | intros pn Hpn; exact (Hin2 _ (HQin _ Hpn)) | exact KR | exact KB].
- exact Hq. - exact Hq4. - exact Hqs. - exact Hlx. - exact Hqf. - exact HO1.
- destruct (in_dec recb_pair_dec (q, k) (ablocks B ly S)) as [Hin | Hnin]; [left | right; exact Hnin].
  destruct (in_dec recb_pair_dec (q, k) (ablocks B lyc Sc)) as [Hc2 | Hnc]; [|exact (HO5 _ Hin Hnc)].
  exfalso. pose proof (proj1 (Forall_forall _ _) Hapart (q, k) Hc2) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, LIVE_XSTRDUP in Hap. unfold k in *. lia.
- intros pn Hpn Hno. exact (Hin2 _ (HO3 pn Hpn Hno)).
- intros pn Hpn. apply (Permutation_in _ Hperm) in Hpn. destruct Hpn as [<- | Hpn]; [right; right; reflexivity|].
  destruct (HO4 pn Hpn) as [H | H]; [left; exact H | right; left; exact H].
- unfold XM_SUP_AFTER_REPLY. exact (mle_station MT S Sc S2 _ _ MTL HMLE HMLE2).
- unfold LIVE_SUP_AFTER_REPLY. lia.
Qed.

(* ---------- a reader that agrees everywhere ---------- *)
Lemma sar_aro_ext : forall (rd rd' : reader), (forall a, rd' a = rd a) ->
arodata_okP SEGS RLO RHI B rd -> arodata_okP SEGS RLO RHI B rd'.
Proof. intros rd rd' Hx H a H1 H2 H3. rewrite Hx. exact (H a H1 H2 H3). Qed.
Lemma sar_frame_nowin : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' HF Hn a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a) (Hn _)). reflexivity. Qed.

(* the string the second argument names, at a state of the walk: in a live heap block (sup_after_reply_c.v:82-85) *)
Definition sar_str_ok ly1 S1 (W1 : world SEGS) mem1 (pv : Z) (verb : option (list byte)) : Prop :=
exists x, verb = Some x /\ in_blockA (ablocks B ly1 S1) pv (Z.of_nat (length x) + 1) /\
astr_atR (rdW W1 mem1) pv x /\ Z.of_nat (length x) + 1 <= LMAX + 1.
Lemma sar_str_ext : forall ly1 S1 (W1 : world SEGS) m m' pv verb, (forall a, rdW W1 m' a = rdW W1 m a) ->
sar_str_ok ly1 S1 W1 m pv verb -> sar_str_ok ly1 S1 W1 m' pv verb.
Proof.
intros ly1 S1 W1 m m' pv verb Hx (x & Hv & Hb & Hs & Hn). exists x. split; [exact Hv|]. split; [exact Hb|].
split; [|exact Hn]. apply (rastr_kept (rdW W1 m)); [exact Hs | intros i _; apply Hx].
Qed.
Lemma sar_pv_bound : forall ly1 S1 (W1 : world SEGS) mem1 md1 pv verb,
AR SEGS B ly1 S1 W1 mem1 md1 -> sar_str_ok ly1 S1 W1 mem1 pv verb -> 4096 <= pv < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 pv verb HAR (x & _ & (b & k & Hin & Hlo & Hhi) & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR Hin) as (_ & Hb4096 & Hbceil & _).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq]. lia.
Qed.
(* what xstrdup's entry asks of the string: its argument form (astr_argA, empty O) and its tail, from the block *)
Lemma sar_str_call : forall ly1 S1 (W1 : world SEGS) mem1 md1 pv x,
AR SEGS B ly1 S1 W1 mem1 md1 -> sar_str_ok ly1 S1 W1 mem1 pv (Some x) ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) [] pv (Some x) /\
atail_vis SEGS W1 mem1 (pv + Z.of_nat (length x)).
Proof.
intros ly1 S1 W1 mem1 md1 pv x HAR (x' & Hx & (b & k & Hin & Hlo & Hhi) & Hs & Hn).
injection Hx as Hx. subst x'.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR Hin) as (_ & Hb4096 & _).
split.
- unfold astr_argA. cbv zeta. split; [lia|]. split; [exact Hs|]. split; [exact Hn|].
  left. split; [exists b, k; split; [exact Hin | lia] | constructor].
- apply (cmd_heap_tail_vis ly1 S1 W1 mem1 md1 b k _ HAR Hin). lia.
Qed.

(* ---------- segment C: after arg_i (0x8c710) to the call of xstrdup ---------- *)
(* the third inline check, nargs (= 1) loaded and compared with 5, then xstrdup(verb); the "(null)" default of a
   NULL verb is not reached, the statement's verb lies in a heap block *)
Lemma sar_seg_C : forall ly S W regs mem md ch R O id pv verb lyc Sc Wc (regs2 : bvmap 5 word) mem2 md2 kc c Q2,
afn_pre SEGS B SUP_AFTER_REPLY_STK ly S W regs mem md ch ->
ajournal SEGS B SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) ly S W mem md [] lyc Sc Wc mem2 md2 kc ->
kc <= rec_spill_frees R + EV_ARG_I ->
st_nev S + EV_SUP_AFTER_REPLY R <= EV_MAX ->
blocks_bytes Sc + LIVE_XSTRDUP (sarg verb) <= LIVE_MAX ->
mo_ok MT S (XM_SUP_AFTER_REPLY MT R id verb) ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT + XM_ARG_I MT id) ->
blocks_bytes Sc <= blocks_bytes S + LIVE_ARG_I id ->
getr regs2 2 = w64 (spZ regs - 64) -> getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
(forall r, 22 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr regs2 9 = w64 c -> getr regs2 18 = w64 (c + 4) -> getr regs2 20 = w64 SB ->
getr regs2 21 = w64 (SB + (c + 4) / 8) -> getr regs2 8 = w64 pv ->
sar_frame (rdW Wc mem2) (spZ regs) regs ->
c = sar_entry R -> (length (r_calls R) <= 16)%nat ->
aval_mem (rdW Wc mem2) (c + CALL_OFF_NARGS) 4 1 ->
arep_at (ablocks B lyc Sc) (rdW Wc mem2) A_G_REC A_REC_SPILL (rec_record R REC_AFTER_REPLY [dec id]) Q2 ->
arodata_okP SEGS RLO RHI B (rdW Wc mem2) ->
sar_str_ok lyc Sc Wc mem2 pv verb ->
(forall pn, In pn (lay_blocks Q2) -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Q2)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B lyc Sc) -> In pn O) ->
SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + SAR_RET_ARGI)) mem2 (seg_rom SEGS)) md2)
(sar_post ly S W regs mem md R O id verb).
Proof.
intros ly S W regs mem md ch R O id pv verb lyc Sc Wc regs2 mem2 md2 kc c Q2
HPRE HJ Hkc HEV HLIVE HMOK HMLE HBBX R2 R3 R4 Rhi R9 R18 R20 R21 R8 HFR Hc Hlen HNA HQ2 HROD HSTR HO1 HO3 HO4 HO5.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof (proj1 HJ) as HAR.
assert (HcOK : sar_slot_ok c) by (rewrite Hc; apply sar_entry_ok; exact Hlen).
destruct (sar_slot_bounds c HcOK) as (Hcb & Hc8 & Hcr). unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb.
assert (HSTKv : SUP_AFTER_REPLY_STK = 16592) by (vm_compute; reflexivity).
assert (Hsp : 2 ^ 46 + 64 <= spZ regs <= 2 ^ 47) by (unfold YG0f.ASAN_CEIL in *; lia).
assert (Hsp1 : bv_unsigned (getr regs2 2) = spZ regs - 64) by (rewrite R2; apply unsigned_lit_small; lia).
(* where the verb lies *)
pose proof (sar_pv_bound lyc Sc Wc mem2 md2 pv verb HAR HSTR) as Hpv.
set (E := Eimg (Ereg regs2 (sar_extra regs c))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (ES : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (sar_extra regs c) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros n rr Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (exact (ES 1%nat ltac:(lia))).
assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 64) by (rewrite (EEo 2%nat 2%bv eq_refl); exact Hsp1).
assert (HSL : Forall (region_ok SEGS E (mrestrict (w_H Wc) mem2)) sar_slotC).
{ unfold sar_slotC. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U33.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ c 4 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia|].
  exact (val_mem_view SEGS (w_H Wc) mem2 _ 4 1 HNA). }
assert (HPD : pairwise_disjoint E (sar_frame_r :: sar_slotC)).
{ apply pairwise_disjoint_of_extents. unfold sar_frame_r, sar_slotC, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold YG0f.ASAN_CEIL in *. repeat split; lia. }
destruct (sar_seed SAR_RET_ARGI sar_regsC sar_slotC Wc regs regs2 mem2 lyc Sc md2 c HAR Hsp Hal16 Hsp1
  (sar_regsC_ok regs regs2 c HcOK R9 R20 R18 R21) HFR HcOK ltac:(vm_compute; reflexivity) HSL HPD) as [HS SHOK].
fold E in HS, SHOK.
assert (E8 : ew E 8 = w64 pv) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (exact (ES 0%nat ltac:(lia))).
assert (DSH : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 4) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + (c + 4) / 8)).
{ apply (denot_shx E 33 32 4 c SB E33 E32); unfold SB; lia. }
clearbody E.
rename Hc into Hce.
unfold SAR_RET_ARGI in HS |- *.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
assert (KEEP1 : forall a, rdW Wc (ms_mem ms) a = rdW Wc mem2 a).
{ lazymatch goal with HFx : frame_of E _ (mrestrict _ mem2) (mrestrict _ _) |- _ =>
  apply (sar_frame_nowin E _ (w_H Wc) mem2 _ HFx) end.
  intros a (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]). destruct Hin. }
rename ms into ms1, HJ into HJ1.
set (mdv := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdv.
(* the facts both arms hand to the call of xstrdup *)
assert (KEEPC : forall (msx : machine_state), (forall a, rdW Wc (ms_mem msx) a = rdW Wc mem2 a) ->
  sar_frame (rdW Wc (ms_mem msx)) (spZ regs) regs /\
  aval_mem (rdW Wc (ms_mem msx)) (c + CALL_OFF_NARGS) 4 1 /\
  arep_at (ablocks B lyc Sc) (rdW Wc (ms_mem msx)) A_G_REC A_REC_SPILL (rec_record R REC_AFTER_REPLY [dec id]) Q2 /\
  arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem msx))).
{ intros msx Kx. split; [apply (sar_frame_kept (rdW Wc mem2)); [exact HFR | intros a _; apply Kx]|].
  split; [apply (aval_mem_kept (rdW Wc mem2)); [exact HNA | intros kk _; apply Kx]|].
  split; [apply (sar_arep_kept (ablocks B lyc Sc) _ (rdW Wc mem2)); [exact HQ2 | intros pn Hpn; exact (lay_blocks_in _ _ _ _ _ _ HQ2 pn Hpn) | intros a _; apply Kx | intros p0 n0 i _ _; apply Kx]|].
  exact (sar_aro_ext (rdW Wc mem2) _ Kx HROD). }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the verb is not NULL: xstrdup(verb) *)
  destruct verb as [x|]; [|destruct HSTR as (x0 & Hx0 & _); discriminate Hx0].
  paj_run_tok RUN HS HJ1 SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
  assert (KEEP2 : forall a, rdW Wc (ms_mem ms) a = rdW Wc (ms_mem ms1) a).
  { lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ms1)) (mrestrict _ _) |- _ =>
    apply (sar_frame_nowin _ _ (w_H Wc) (ms_mem ms1) _ HFx) end.
    intros a (r & Hin & Hr). vm_compute in Hin.
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]). destruct Hin. }
  assert (KEEP : forall a, rdW Wc (ms_mem ms) a = rdW Wc mem2 a) by (intros a; rewrite KEEP2; apply KEEP1).
  destruct (KEEPC ms KEEP) as (KF & KN & KQ & KR).
  destruct (sar_str_call lyc Sc Wc (ms_mem ms) _ pv x (proj1 HJ1) (sar_str_ext lyc Sc Wc mem2 (ms_mem ms) pv (Some x) KEEP HSTR))
    as [HSTRx HTx].
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2'. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.
  prreg HS (20%bv : bv 5) Q20.
  sar_preg HS (21%bv : bv 5) Q21.
  sar_preg HS (Z_to_bv 5 22) Q22. sar_preg HS (Z_to_bv 5 23) Q23. sar_preg HS (Z_to_bv 5 24) Q24.
  sar_preg HS (Z_to_bv 5 25) Q25. sar_preg HS (Z_to_bv 5 26) Q26. sar_preg HS (Z_to_bv 5 27) Q27.
  apply (sar_call_XS ly S W regs mem md ch R O id (Some x) lyc Sc Wc (ms_regs ms) (ms_mem ms) _ kc c Q2 pv HPRE HJ1
    Hkc HEV HLIVE HMOK HMLE HBBX).
  + rewrite Q2', (EEo 2%nat 2%bv eq_refl). exact R2.
  + rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact R3.
  + rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact R4.
  + intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [-> | Hr']); try (subst r); rewrite <- Rhi by lia;
    first [rewrite Q22, sar_denot_off0; apply EEo; reflexivity | rewrite Q23, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q24, sar_denot_off0; apply EEo; reflexivity | rewrite Q25, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q26, sar_denot_off0; apply EEo; reflexivity | rewrite Q27, sar_denot_off0; apply EEo; reflexivity].
  + rewrite Q9, E33. reflexivity.
  + rewrite Q18, U33. reflexivity.
  + rewrite Q20, E32. reflexivity.
  + rewrite Q21. exact DSH.
  + rewrite Q10, E8. reflexivity.
  + rewrite Q1. reflexivity.
  + unfold s0Z. rewrite Q8, E8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  + exact KF.
  + exact Hce.
  + exact Hlen.
  + exact KN.
  + exact KQ.
  + exact KR.
  + cbn [sarg]. exact HSTRx.
  + cbn [sarg]. exact HTx.
  + exact HO1.
  + exact HO3.
  + exact HO4.
  + exact HO5.
- (* the verb is NULL: no caller passes one, the verb lies in a heap block *)
  exfalso. rewrite branch_ne_U in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
  rewrite (sar_U_atom E 8 pv E8 ltac:(unfold YG0f.ASAN_CEIL in *; lia)) in Hc.
  assert (HU0 : U E (SLit 0) = 0) by reflexivity. rewrite HU0 in Hc. lia.
Qed.
End g.

(* the walk from the entry to the call of arg_i, and that call: at the entry's FP state, ending in apost_baseF *)
Section h. Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* the post of the statement (sup_after_reply_c.v:91-104) *)
Definition sar_postF ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z)) (id : Z)
(verb : option (list byte)) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_AFTER_REPLY_STK
 ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O)
 regs ly S W mem md (EV_SUP_AFTER_REPLY R)
(fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
 rec_repA B ly' S' (rdW W' mem') (sup_after_reply_m R id verb) O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_AFTER_REPLY id verb /\
 mo_le MT S S' (XM_SUP_AFTER_REPLY MT R id verb)).

(* ---------- what a callee's journal keeps, part 2 ---------- *)
Lemma sar_blk_not_rec : forall ly1 S1 (W1 : world SEGS) mem1 md1 p n i,
AR SEGS B ly1 S1 W1 mem1 md1 -> In (p, n) (ablocks B ly1 S1) -> 0 <= i < req_size n -> ~ in_rec (p + i).
Proof.
intros ly1 S1 W1 mem1 md1 p n i HAR Hin Hi Hr.
pose proof (blk_off_imgP B _ _ _ _ _ p n HAR Hin) as Hoff. unfold off_img in Hoff.
unfold in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hr. lia.
Qed.
Lemma sar_jkeep_blk : forall STK1 sp1 FP1 ly1 S1 (W1 : world SEGS) mem1 md1 own ly2 S2 W2 mem2 md2 k1 p n i,
ajournal SEGS B STK1 sp1 FP1 ly1 S1 W1 mem1 md1 own ly2 S2 W2 mem2 md2 k1 ->
(forall a, inFP FP1 a -> in_rec a) ->
In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
rdW W2 mem2 (p + i) = rdW W1 mem1 (p + i).
Proof.
intros STK1 sp1 FP1 ly1 S1 W1 mem1 md1 own ly2 S2 W2 mem2 md2 k1 p n i HJ1 HF Hin1 Hin2 Hi.
pose proof HJ1 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hin1 Hin2 Hi). intros Hf. exact (sar_blk_not_rec _ _ _ _ _ p n i HAR2 Hin2 Hi (HF _ Hf)).
Qed.
(* the verb survives a call that writes only bytes of g_rec / record.spill and frees nothing *)
Lemma sar_str_kept : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 pv verb,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
(forall a, inFP FP1 a -> in_rec a) ->
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2)) ->
sar_str_ok lyc Sc Wc memc pv verb -> sar_str_ok ly2 S2 W2 mem2 pv verb.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 pv verb HJ1 HF Hbl (x & Hv & (b & k & Hbk & Hb1 & Hb2) & Hstr & Hn).
pose proof (Hbl _ Hbk) as Hbk2.
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
exists x. split; [exact Hv|]. split; [exists b, k; split; [exact Hbk2 | lia]|]. split; [|exact Hn].
apply (rastr_kept (rdW Wc memc)); [exact Hstr|].
intros i Hi. replace (pv + i) with (b + (pv + i - b)) by lia.
apply (sar_jkeep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b k (pv + i - b) HJ1 HF Hbk Hbk2). lia.
Qed.
Lemma sar_keep_reg : forall (rx r2 : bvmap 5 word) (n : Z) (rb : bv 5) (v : word),
aregs_preserved rx r2 -> acallee_saved n -> Z_to_bv 5 n = rb -> getr rx rb = v -> getr r2 rb = v.
Proof. intros rx r2 n rb v HP Hn <- Hv. rewrite (HP n Hn). exact Hv. Qed.
Ltac sar_keep HP n R := apply (sar_keep_reg _ _ n _ _ HP); [unfold acallee_saved; lia | apply bv_eq; reflexivity | exact R].

(* ---------- the call of arg_i (0x8c70c) and what follows ---------- *)
Lemma sar_call_ARGI : forall ly S W regs mem md ch R O id pv verb lyc Sc Wc (regsx : bvmap 5 word) memx mdx kc c Q1,
afn_pre SEGS B SUP_AFTER_REPLY_STK ly S W regs mem md ch ->
ajournal SEGS B SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) ly S W mem md [] lyc Sc Wc memx mdx kc ->
kc <= rec_spill_frees R ->
st_nev S + EV_SUP_AFTER_REPLY R <= EV_MAX ->
blocks_bytes Sc + LIVE_SUP_AFTER_REPLY id verb <= LIVE_MAX ->
mo_ok MT S (XM_SUP_AFTER_REPLY MT R id verb) ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
frm0 fx -> blocks_bytes Sc <= blocks_bytes S ->
Z.of_nat (length (frames Sc)) <= 8 -> -2 ^ 31 <= id < 2 ^ 31 ->
getr regsx 2 = w64 (spZ regs - 64) -> getr regsx 3 = w64 (as_gp B) -> getr regsx 4 = w64 (as_tp B) ->
(forall r, 22 <= r <= 27 -> getr regsx (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr regsx 9 = w64 c -> getr regsx 18 = w64 (c + 4) -> getr regsx 20 = w64 SB ->
getr regsx 21 = w64 (SB + (c + 4) / 8) -> getr regsx 8 = w64 pv ->
getr regsx 10 = w64 c -> getr regsx 11 = w64 id ->
getr regsx 1 = Z_to_bv 64 (BASE + SAR_RET_ARGI) ->
sar_frame (rdW Wc memx) (spZ regs) regs ->
c = sar_entry R -> (length (r_calls R) <= 16)%nat ->
aval_mem (rdW Wc memx) (c + CALL_OFF_NARGS) 4 0 ->
arep_at (ablocks B lyc Sc) (rdW Wc memx) A_G_REC A_REC_SPILL (rec_record R REC_AFTER_REPLY []) Q1 ->
arodata_okP SEGS RLO RHI B (rdW Wc memx) ->
sar_str_ok lyc Sc Wc memx pv verb ->
(forall pn, In pn (lay_blocks Q1) -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Q1)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B lyc Sc) -> In pn O) ->
SRr SEGS Wc (mkCfg (mkst regsx (Z_to_bv 64 (SIG CS_arg_i)) memx (seg_rom SEGS)) mdx)
(sar_postF ly S W regs mem md R O id verb).
Proof.
intros ly S W regs mem md ch R O id pv verb lyc Sc Wc regsx memx mdx kc c Q1
HPRE HJ Hkc HEV HLIVE HMOK HMLE HRM HBBX HFRM Hid R2 R3 R4 Rhi R9 R18 R20 R21 R8 R10 R11 R1 HFR Hc Hlen HNA HQ1 HROD HSTR
HO1 HO3 HO4 HO5.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof (proj1 HJ) as HAR.
assert (HcOK : sar_slot_ok c) by (rewrite Hc; apply sar_entry_ok; exact Hlen).
destruct (sar_slot_bounds c HcOK) as (Hcb & Hc8 & Hcr). unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb.
assert (HSTKv : SUP_AFTER_REPLY_STK = 16592) by (vm_compute; reflexivity).
assert (HAIv : ARG_I_STK = 16528) by (vm_compute; reflexivity).
assert (Hsp : 2 ^ 46 + 64 <= spZ regs <= 2 ^ 47) by (unfold YG0f.ASAN_CEIL in *; lia).
assert (Psp : spZ regsx = spZ regs + -64) by (unfold spZ at 1; rewrite R2; rewrite unsigned_lit_small by lia; lia).
pose proof (dec_length id Hid) as Hlx.
pose proof (sar_pv_bound _ _ _ _ _ pv verb HAR HSTR) as Hpv.
assert (Hs0 : s0Z regsx < alloc_ceiling).
{ unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by (unfold YG0f.ASAN_CEIL in *; lia). lia. }
assert (Hnev : st_nev Sc + EV_ARG_I <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). unfold EV_SUP_AFTER_REPLY, EV_ARG_I, EV_XSTRDUP in *. lia. }
assert (HLIVEa : blocks_bytes Sc + LIVE_ARG_I id <= LIVE_MAX).
{ unfold LIVE_SUP_AFTER_REPLY, LIVE_ARG_I, LIVE_XSTRDUP in HLIVE |- *. lia. }
assert (HXS0 : 0 <= XM_XSTRDUP MT (sarg verb)) by (unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
assert (HAI0 : 0 <= XM_ARG_I MT id) by (unfold XM_ARG_I, XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
assert (HMOKa : mo_ok MT Sc (XM_ARG_I MT id)).
{ apply (mok_station MT S Sc (XM_SUP_AFTER_REPLY MT R id verb) (rec_spill_frees R * mo_free MT) _ MTL HMOK HMLE HAI0).
  unfold XM_SUP_AFTER_REPLY. lia. }
set (FP1 := [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 0, c + CALL_OFF_ARGS + 8 * 0 + 8)]).
assert (HFP1 : forall a, inFP FP1 a -> in_rec a /\ c + 4 <= a < c + 16).
{ intros a (r & Hr & Ha). unfold FP1, CALL_OFF_NARGS, CALL_OFF_ARGS in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; (split; [|lia]);
  unfold in_rec; destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr in *;
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia. }
assert (HsoF : ~ YI16.sink_open_fp FP1).
{ intros (r & Hr & Ha). unfold FP1, CALL_OFF_NARGS, CALL_OFF_ARGS in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; lia. }
rewrite sar_sig_arg_i.
set (k := Z.of_nat (length (dec id)) + 1).
unfold sar_postF.
eapply srr_after_callF_base.
{ eapply (cl_callS_wideF B LAWS Wc regsx memx _ SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) ly S W mem md [] lyc Sc mdx kc
    ARG_I_STK FP1 EV_ARG_I (-64) (Z_to_bv 64 (BASE + SAR_RET_ARGI)) []
    (fun ly' S' W' regs' mem' md' => mo_le MT Sc S' (XM_ARG_I MT id) /\ exists p : Z,
       4096 <= p /\ Permutation (ablocks B ly' S') ((p, k) :: ablocks B lyc Sc) /\
       Forall (fun qk => iv_apart p k (fst qk) (snd qk)) (ablocks B lyc Sc) /\
       aval_mem (rdW W' mem') (c + CALL_OFF_NARGS) 4 1 /\
       aval_mem (rdW W' mem') (c + CALL_OFF_ARGS) 8 p /\
       astr_atR (rdW W' mem') p (dec id)) HJ Psp);
  [ reflexivity | lia | rewrite HAIv; lia | rewrite HSTKv, HAIv; lia
  | exact R3 | exact R4 | exact R1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]
  | unfold SAR_RET_ARGI; rewrite unsigned_lit_small by lia; lia
  | left; split; [left; exact Hs0 | reflexivity]
  | intros HPREx; eapply SRr_mono;
    [ apply (TARG_I fx lyc Sc Wc regsx memx mdx [] c id 0 HPREx HRM
        HFRM HROD (cmd_ro_ok_of_aro lyc Sc Wc memx mdx HAR HROD)
        R10 R11 Hid HcOK HNA ltac:(unfold REC_ARGS_MAX; lia)
        Hnev HLIVEa HMOKa)
    | cbv beta; unfold apost_baseF; intros W3 c3 _ (fx3 & ly3 & S3 & regs3 & mem3 & md3 & -> & Hf1 & Hf2 & HJ1 & HP & HK);
      exists fx3, ly3, S3, regs3, mem3, md3; split; [rewrite R1; reflexivity|]; split; [exact Hf1|]; split; [exact Hf2|];
      split; [exact HJ1|]; split; [exact HP|];
      destruct HK as [_ [HM [(H0 & _) | (_ & p & [Hp4 _] & Hperm & Hap & HN1 & HA0 & HS0)]]];
      [ unfold REC_ARGS_MAX in H0; lia
      | split; [exact HM|]; exists p; split; [exact Hp4|]; split; [exact Hperm|]; split; [exact Hap|];
        split; [exact HN1|]; split; [rewrite Z.mul_0_r, Z.add_0_r in HA0; exact HA0 | exact HS0] ] ]
  | intros a Ha; apply sar_awr_rec; exact (proj1 (HFP1 a Ha))
  | intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _; exfalso; destruct (HFP1 a Ha) as [_ Hb];
    unfold YG0f.ASAN_CEIL in *; lia ]. }
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 Hwle2 Hfx (HJ2 & HJi & HP2 & HK2).
destruct HK2 as (HMLE2 & p & Hp4 & Hperm & Hapart & VN & VA & Hps).
pose proof HJi as (HAR2 & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
(* the registers the call keeps *)
assert (X2 : getr regs2 2 = w64 (spZ regs - 64)) by sar_keep HP2 2 R2.
assert (X3 : getr regs2 3 = w64 (as_gp B)) by sar_keep HP2 3 R3.
assert (X4 : getr regs2 4 = w64 (as_tp B)) by sar_keep HP2 4 R4.
assert (X8 : getr regs2 8 = w64 pv) by sar_keep HP2 8 R8.
assert (X9 : getr regs2 9 = w64 c) by sar_keep HP2 9 R9.
assert (X18 : getr regs2 18 = w64 (c + 4)) by sar_keep HP2 18 R18.
assert (X20 : getr regs2 20 = w64 SB) by sar_keep HP2 20 R20.
assert (X21 : getr regs2 21 = w64 (SB + (c + 4) / 8)) by sar_keep HP2 21 R21.
assert (Xhi : forall r, 22 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)). exact (Rhi r Hr). }
(* the blocks *)
assert (HQin : forall pn, In pn (lay_blocks Q1) -> In pn (ablocks B lyc Sc)) by exact (lay_blocks_in _ _ _ _ _ _ HQ1).
assert (Hin2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn. eapply Permutation_in; [apply Permutation_sym; exact Hperm|]. right. exact Hpn. }
assert (Hpk : In (p, k) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
assert (Hpf : ~ In p (map fst (lay_blocks Q1))).
{ intros Hin. apply in_map_iff in Hin as ([b m] & Eb & Hbm). cbn [fst] in Eb. subst b.
  pose proof (sar_lay_pos _ _ _ _ HQ1 (p, m) Hbm) as Hm. cbn [snd] in Hm.
  pose proof (proj1 (Forall_forall _ _) Hapart (p, m) (HQin _ Hbm)) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, k in Hap. lia. }
pose proof (blk_off_imgP B _ _ _ _ _ p k HAR2 Hpk) as Hpoff. pose proof (req_size_pos k ltac:(unfold k; lia)) as [_ Hpreq].
unfold off_img in Hpoff.
(* the model step: the first argument *)
destruct (sar_rep_arg (ablocks B lyc Sc) (ablocks B ly2 S2) (rdW Wc memx) (rdW W2 mem2) R REC_AFTER_REPLY [] Q1 (dec id) p k
  HQ1 Hlen ltac:(cbn; lia)) as (Q2 & HQ2 & HQ2i).
{ rewrite <- Hc. exact VN. }
{ rewrite <- Hc. cbn [length Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. exact VA. }
{ intros a Ha H1 H2. rewrite <- Hc in H1, H2. cbn [length Z.of_nat] in H2. rewrite Z.mul_0_r, Z.add_0_r in H2.
  apply (sar_jkeep_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi HsoF Ha).
  intros Hf. destruct (HFP1 a Hf) as [_ Hb]. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in H1, H2. lia. }
{ intros pn Hpn. split; [exact (Hin2 _ (HQin _ Hpn))|]. intros i Hi. destruct pn as [b m]. cbn [fst snd] in *.
  pose proof (req_size_pos m ltac:(lia)) as [_ Hmr].
  apply (sar_jkeep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m i HJi (fun a Ha => proj1 (HFP1 a Ha)) (HQin _ Hpn)
    (Hin2 _ (HQin _ Hpn))). lia. }
{ exact Hpf. }
{ lia. }
{ exact Hpk. }
{ exact Hps. }
{ unfold LMAX. lia. }
{ unfold k, LMAX. lia. }
{ unfold iv_apart, A_G_REC, REC_SIZE. lia. }
{ unfold iv_apart, A_REC_SPILL, SC_SIZE. lia. }
assert (BB2 : blocks_bytes S2 = bsum (ablocks B ly2 S2)) by (apply blocks_bytes_bsum).
assert (BBc : blocks_bytes Sc = bsum (ablocks B lyc Sc)) by (apply blocks_bytes_bsum).
rewrite (bsum_perm _ _ Hperm), bsum_cons in BB2. cbn [snd] in BB2.
apply (sar_seg_C (fx := fx1) ly S W regs mem md ch R O id pv verb ly2 S2 W2 regs2 mem2 md2 (kc + EV_ARG_I) c Q2 HPRE HJ2).
- lia.
- exact HEV.
- unfold LIVE_SUP_AFTER_REPLY, LIVE_ARG_I, LIVE_XSTRDUP in HLIVE |- *. unfold k in BB2. lia.
- exact HMOK.
- exact (mle_station MT S Sc S2 _ _ MTL HMLE HMLE2).
- unfold LIVE_ARG_I, LIVE_XSTRDUP. unfold k in BB2. lia.
- exact X2. - exact X3. - exact X4. - exact Xhi. - exact X9. - exact X18. - exact X20. - exact X21. - exact X8.
- apply (sar_frame_kept (rdW Wc memx)); [exact HFR|]. intros a Ha. apply F1.
  + unfold YG0f.ASAN_CEIL in *. lia.
  + rewrite HAIv. lia.
  + intros Hf. destruct (HFP1 a Hf) as [_ Hb]. lia.
- exact Hc. - exact Hlen. - exact VN. - exact HQ2.
- eapply (@arodata_ok_journalP _ _ SEGS RLO RHI RELRO_IMG RRO B); [exact HJi | | exact HROD].
  intros a Hr Hf. destruct (cmd_ro_prog_apart a Hr) as [_ Hn]. exact (Hn (sar_in_PG a (proj1 (HFP1 a Hf)))).
- exact (sar_str_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ pv verb HJi (fun a Ha => proj1 (HFP1 a Ha)) Hin2 HSTR).
- intros pn Hpn. apply HQ2i in Hpn as [Hpn | ->]; [exact (HO1 pn Hpn)|].
  destruct (in_dec recb_pair_dec (p, k) (ablocks B ly S)) as [Hin | Hnin]; [left | right; exact Hnin].
  destruct (in_dec recb_pair_dec (p, k) (ablocks B lyc Sc)) as [Hc2 | Hnc]; [|exact (HO5 _ Hin Hnc)].
  exfalso. pose proof (proj1 (Forall_forall _ _) Hapart (p, k) Hc2) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, k in Hap. lia.
- intros pn Hpn Hno. exact (Hin2 _ (HO3 pn Hpn Hno)).
- intros pn Hpn. apply (Permutation_in _ Hperm) in Hpn. destruct Hpn as [<- | Hpn]; [right; apply HQ2i; right; reflexivity|].
  destruct (HO4 pn Hpn) as [H | H]; [left; exact H | right; apply HQ2i; left; exact H].
- intros pn Hpn Hno. apply (HO5 pn Hpn). intros Hc2. exact (Hno (Hin2 _ Hc2)).
Qed.

(* ---------- what a run keeps ---------- *)
(* the verb and the read-only bytes survive a run that writes only the stack and g_rec / record.spill *)
Lemma sar_str_run : forall lyc Sc (Wc : world SEGS) memc mdc mem3 md3 pv verb,
AR SEGS B lyc Sc Wc memc mdc -> AR SEGS B lyc Sc Wc mem3 md3 ->
(forall a, 0 <= a < alloc_ceiling -> ~ in_rec a -> rdW Wc mem3 a = rdW Wc memc a) ->
sar_str_ok lyc Sc Wc memc pv verb -> sar_str_ok lyc Sc Wc mem3 pv verb.
Proof.
intros lyc Sc Wc memc mdc mem3 md3 pv verb HAR HAR3 KEEP (x & Hv & (b & k & Hbk & Hb1 & Hb2) & Hstr & Hn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR Hbk) as (_ & Hb4096 & Hbceil & _).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
exists x. split; [exact Hv|]. split; [exists b, k; split; [exact Hbk | lia]|]. split; [|exact Hn].
apply (rastr_kept (rdW Wc memc)); [exact Hstr|].
intros i Hi. apply KEEP; [lia|]. replace (pv + i) with (b + (pv + i - b)) by lia.
apply (sar_blk_not_rec _ _ _ _ _ b k (pv + i - b) HAR Hbk). lia.
Qed.
Lemma sar_aro_run : forall (rd rd' : reader),
(forall a, 0 <= a < alloc_ceiling -> ~ in_rec a -> rd' a = rd a) ->
arodata_okP SEGS RLO RHI B rd -> arodata_okP SEGS RLO RHI B rd'.
Proof.
intros rd rd' KEEP HR a Hr Ho He. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cmd_ro_prog_apart a Hr) as [Hi Hnp]. pose proof (pa_segs_low a Hi).
rewrite KEEP; [exact (HR a Hr Ho He) | unfold YG0f.ASAN_CEIL in *; lia |].
intros Hin. exact (Hnp (sar_in_PG _ Hin)).
Qed.

(* the record() step the walk owes at the join: once fn and nargs are written, the recorder holds the new call *)
Definition sar_pending (bl : list (Z * Z)) (rd : reader) (R : rstate) (Q1 : rlay) (c : Z) : Prop :=
(forall pn, In pn (lay_blocks Q1) -> In pn bl) /\
forall rd' : reader,
  aval_mem rd' (c + CALL_OFF_FN) 4 REC_AFTER_REPLY -> aval_mem rd' (c + CALL_OFF_NARGS) 4 0 ->
  (forall a, in_rec a -> ~ (c <= a < c + 8) -> rd' a = rd a) ->
  (forall p n i, In (p, n) (lay_blocks Q1) -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
  arep_at bl rd' A_G_REC A_REC_SPILL (rec_record R REC_AFTER_REPLY []) Q1.

(* ---------- segment B: from record()'s join (0x8c6d4, or 0x8c6b4 after rec_calls_free) to the call of arg_i ---------- *)
(* the two inline checks of the slot, c->fn := 19, c->nargs := 0, then arg_i(c, id) *)
Lemma sar_seg_B : forall ly S W regs mem md ch R O id pv verb lyc Sc Wc (regs1 : bvmap 5 word) mem1 md1 kc c Q1 pc,
afn_pre SEGS B SUP_AFTER_REPLY_STK ly S W regs mem md ch ->
ajournal SEGS B SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) ly S W mem md [] lyc Sc Wc mem1 md1 kc ->
kc <= rec_spill_frees R ->
st_nev S + EV_SUP_AFTER_REPLY R <= EV_MAX ->
blocks_bytes Sc + LIVE_SUP_AFTER_REPLY id verb <= LIVE_MAX ->
mo_ok MT S (XM_SUP_AFTER_REPLY MT R id verb) ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
frm0 fx -> blocks_bytes Sc <= blocks_bytes S ->
Z.of_nat (length (frames Sc)) <= 8 -> -2 ^ 31 <= id < 2 ^ 31 ->
getr regs1 2 = w64 (spZ regs - 64) -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
(forall r, 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr regs1 9 = w64 c -> getr regs1 20 = w64 SB -> getr regs1 8 = w64 pv -> getr regs1 19 = w64 id ->
pc = SAR_JOIN \/ pc = SAR_RET_RCF ->
sar_frame (rdW Wc mem1) (spZ regs) regs ->
c = sar_entry R -> (length (r_calls R) <= 16)%nat ->
sar_pending (ablocks B lyc Sc) (rdW Wc mem1) R Q1 c ->
arodata_okP SEGS RLO RHI B (rdW Wc mem1) ->
sar_str_ok lyc Sc Wc mem1 pv verb ->
(forall pn, In pn (lay_blocks Q1) -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn (lay_blocks Q1)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B lyc Sc) -> In pn O) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)) md1)
(sar_postF ly S W regs mem md R O id verb).
Proof.
intros ly S W regs mem md ch R O id pv verb lyc Sc Wc regs1 mem1 md1 kc c Q1 pc
HPRE HJ Hkc HEV HLIVE HMOK HMLE HRM HBBX HFRM Hid R2 R3 R4 Rhi R9 R20 R8 R19 Hpc HFR Hc Hlen HPEND HROD HSTR HO1 HO3 HO4 HO5.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof (proj1 HJ) as HAR.
assert (HcOK : sar_slot_ok c) by (rewrite Hc; apply sar_entry_ok; exact Hlen).
destruct (sar_slot_bounds c HcOK) as (Hcb & Hc8 & Hcr). unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb.
assert (HSTKv : SUP_AFTER_REPLY_STK = 16592) by (vm_compute; reflexivity).
assert (Hsp : 2 ^ 46 + 64 <= spZ regs <= 2 ^ 47) by (unfold YG0f.ASAN_CEIL in *; lia).
assert (Hsp1 : bv_unsigned (getr regs1 2) = spZ regs - 64) by (rewrite R2; apply unsigned_lit_small; lia).
set (E := Eimg (Ereg regs1 (sar_extra regs c))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (ES : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (sar_extra regs c) (Z_to_bv 64 0))
  by (intros j Hj; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr)
  by (intros n rr Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (exact (ES 1%nat ltac:(lia))).
assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 64) by (rewrite (EEo 2%nat 2%bv eq_refl); exact Hsp1).
assert (HSL : Forall (region_ok SEGS E (mrestrict (w_H Wc) mem1)) sar_slotJ).
{ unfold sar_slotJ. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U33.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (cmd_prog_writable lyc Sc Wc mem1 md1 (c + o) HAR). apply sar_in_PG.
  unfold in_rec. destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr in *;
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia. }
assert (HPD : pairwise_disjoint E (sar_frame_r :: sar_slotJ)).
{ apply pairwise_disjoint_of_extents. unfold sar_frame_r, sar_slotJ, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold YG0f.ASAN_CEIL in *. repeat split; lia. }
destruct (sar_seed pc sar_regsJ sar_slotJ Wc regs regs1 mem1 lyc Sc md1 c HAR Hsp Hal16 Hsp1
  (sar_regsJ_ok regs regs1 c HcOK R9 R20) HFR HcOK ltac:(vm_compute; reflexivity) HSL HPD) as [HS SHOK].
fold E in HS, SHOK.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (exact (ES 0%nat ltac:(lia))).
assert (DSH : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 4) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + (c + 4) / 8)).
{ apply (denot_shx E 33 32 4 c SB E33 E32); unfold SB; lia. }
clearbody E.
destruct HPEND as [HPin HPEND].
(* what the run keeps: every byte outside the slot's fn and nargs words and the frame *)
assert (HSR : forall mem3 md3, AR SEGS B lyc Sc Wc mem3 md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc mem3 a = rdW Wc mem1 a) ->
  sar_str_ok lyc Sc Wc mem3 pv verb /\ arodata_okP SEGS RLO RHI B (rdW Wc mem3) /\ sar_frame (rdW Wc mem3) (spZ regs) regs).
{ intros mem3 md3 HAR3 KEEP.
  assert (K2 : forall a, 0 <= a < alloc_ceiling -> ~ in_rec a -> rdW Wc mem3 a = rdW Wc mem1 a).
  { intros a Ha Hn. apply KEEP; [unfold YG0f.ASAN_CEIL in *; lia|]. intros Hin. apply Hn. unfold in_rec.
    destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr in *; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia. }
  split; [exact (sar_str_run lyc Sc Wc mem1 md1 mem3 md3 pv verb HAR HAR3 K2 HSTR)|].
  split; [exact (sar_aro_run (rdW Wc mem1) _ K2 HROD)|].
  apply (sar_frame_kept (rdW Wc mem1)); [exact HFR|]. intros a Ha. apply KEEP; lia. }
destruct Hpc as [-> | ->].
- unfold SAR_JOIN in HS |- *.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 33%nat); [reflexivity | exact U33 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply sar_awr_rec. unfold in_rec.
      destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr in *; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia. }
    apply (awr_ok_nil SEGS B). }
  lazymatch type of HS with
  | st_ok _ _ ?ssx ?msx =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) sar_frame_r) in
    pose proof (st_ok_region_nth (segs := SEGS) E ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HRD1;
    cbn [ms_mem restrict mkst] in HRD1
  end.
  lazymatch goal with HFx : frame_of E _ (mrestrict _ mem1) (mrestrict _ ?m3) |- _ => rename HFx into HFr3; set (mem3 := m3) in * end.
  pose proof (field_of_region (segs := SEGS) E _ 33 c _ _ _ _ _ 0 4 (SLit 19) 19 HRD1 U33 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as VF.
  pose proof (field_of_region (segs := SEGS) E _ 33 c _ _ _ _ _ 4 4 (SLit 0) 0 HRD1 U33 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as VN.
  change (N.to_nat 4) with 4%nat in VF, VN.
  apply (aval_mem_view SEGS) in VF, VN.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc mem3 a = rdW Wc mem1 a).
  { intros a Ha H1.
    apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) mem1 mem3 (fun a => c <= a < c + 8) HFr3); [ | exact Ha | exact H1 ].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hqq | Hin]; [injection Hqq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U33 in Hrr; lia |]).
    destruct Hin. }
  assert (HQ1 : arep_at (ablocks B lyc Sc) (rdW Wc mem3) A_G_REC A_REC_SPILL (rec_record R REC_AFTER_REPLY []) Q1).
  { apply HPEND.
    - unfold CALL_OFF_FN. exact VF.
    - exact VN.
    - intros a Ha H1. apply KEEP; [unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia | exact H1].
    - intros p n i Hpn Hi. pose proof (HPin _ Hpn) as Hpn'.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn') as (_ & Hp4096 & Hpceil & _).
      pose proof (blk_off_imgP B _ _ _ _ _ p n HAR Hpn') as Hoff. pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
      unfold off_img in Hoff. apply KEEP; unfold YG0f.ASAN_CEIL in *; lia. }
  destruct (HSR mem3 _ (proj1 HJ) KEEP) as (HSTR3 & HROD3 & HFR3).
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1r. prreg HS (2%bv : bv 5) Q2'. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20.
  sar_preg HS (21%bv : bv 5) Q21.
  sar_preg HS (Z_to_bv 5 22) Q22. sar_preg HS (Z_to_bv 5 23) Q23. sar_preg HS (Z_to_bv 5 24) Q24.
  sar_preg HS (Z_to_bv 5 25) Q25. sar_preg HS (Z_to_bv 5 26) Q26. sar_preg HS (Z_to_bv 5 27) Q27.
  apply (sar_call_ARGI ly S W regs mem md ch R O id pv verb lyc Sc Wc (ms_regs ms) mem3 _ kc c Q1 HPRE HJ
    Hkc HEV HLIVE HMOK HMLE HRM HBBX HFRM Hid).
  + rewrite Q2', (EEo 2%nat 2%bv eq_refl). exact R2.
  + rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact R3.
  + rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact R4.
  + intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [-> | Hr']); try (subst r); rewrite <- Rhi by lia;
    first [rewrite Q22, sar_denot_off0; apply EEo; reflexivity | rewrite Q23, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q24, sar_denot_off0; apply EEo; reflexivity | rewrite Q25, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q26, sar_denot_off0; apply EEo; reflexivity | rewrite Q27, sar_denot_off0; apply EEo; reflexivity].
  + rewrite Q9, E33. reflexivity.
  + rewrite Q18, U33. reflexivity.
  + rewrite Q20, E32. reflexivity.
  + rewrite Q21. exact DSH.
  + rewrite Q8, (EEo 8%nat 8%bv eq_refl). exact R8.
  + rewrite Q10, E33. reflexivity.
  + rewrite Q11, (EEo 19%nat 19%bv eq_refl). exact R19.
  + rewrite Q1r. reflexivity.
  + exact HFR3.
  + exact Hc.
  + exact Hlen.
  + exact VN.
  + exact HQ1.
  + exact HROD3.
  + exact HSTR3.
  + exact HO1.
  + exact HO3.
  + exact HO4.
  + exact HO5.
- unfold SAR_RET_RCF in HS |- *.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 33%nat); [reflexivity | exact U33 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply sar_awr_rec. unfold in_rec.
      destruct Hcr as [Hcr | Hcr]; rewrite ?Hcr in *; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia. }
    apply (awr_ok_nil SEGS B). }
  lazymatch type of HS with
  | st_ok _ _ ?ssx ?msx =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) sar_frame_r) in
    pose proof (st_ok_region_nth (segs := SEGS) E ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HRD1;
    cbn [ms_mem restrict mkst] in HRD1
  end.
  lazymatch goal with HFx : frame_of E _ (mrestrict _ mem1) (mrestrict _ ?m3) |- _ => rename HFx into HFr3; set (mem3 := m3) in * end.
  pose proof (field_of_region (segs := SEGS) E _ 33 c _ _ _ _ _ 0 4 (SLit 19) 19 HRD1 U33 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as VF.
  pose proof (field_of_region (segs := SEGS) E _ 33 c _ _ _ _ _ 4 4 (SLit 0) 0 HRD1 U33 ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as VN.
  change (N.to_nat 4) with 4%nat in VF, VN.
  apply (aval_mem_view SEGS) in VF, VN.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc mem3 a = rdW Wc mem1 a).
  { intros a Ha H1.
    apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) mem1 mem3 (fun a => c <= a < c + 8) HFr3); [ | exact Ha | exact H1 ].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hqq | Hin]; [injection Hqq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U33 in Hrr; lia |]).
    destruct Hin. }
  assert (HQ1 : arep_at (ablocks B lyc Sc) (rdW Wc mem3) A_G_REC A_REC_SPILL (rec_record R REC_AFTER_REPLY []) Q1).
  { apply HPEND.
    - unfold CALL_OFF_FN. exact VF.
    - exact VN.
    - intros a Ha H1. apply KEEP; [unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia | exact H1].
    - intros p n i Hpn Hi. pose proof (HPin _ Hpn) as Hpn'.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn') as (_ & Hp4096 & Hpceil & _).
      pose proof (blk_off_imgP B _ _ _ _ _ p n HAR Hpn') as Hoff. pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
      unfold off_img in Hoff. apply KEEP; unfold YG0f.ASAN_CEIL in *; lia. }
  destruct (HSR mem3 _ (proj1 HJ) KEEP) as (HSTR3 & HROD3 & HFR3).
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1r. prreg HS (2%bv : bv 5) Q2'. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20.
  sar_preg HS (21%bv : bv 5) Q21.
  sar_preg HS (Z_to_bv 5 22) Q22. sar_preg HS (Z_to_bv 5 23) Q23. sar_preg HS (Z_to_bv 5 24) Q24.
  sar_preg HS (Z_to_bv 5 25) Q25. sar_preg HS (Z_to_bv 5 26) Q26. sar_preg HS (Z_to_bv 5 27) Q27.
  apply (sar_call_ARGI ly S W regs mem md ch R O id pv verb lyc Sc Wc (ms_regs ms) mem3 _ kc c Q1 HPRE HJ
    Hkc HEV HLIVE HMOK HMLE HRM HBBX HFRM Hid).
  + rewrite Q2', (EEo 2%nat 2%bv eq_refl). exact R2.
  + rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact R3.
  + rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact R4.
  + intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [-> | Hr']); try (subst r); rewrite <- Rhi by lia;
    first [rewrite Q22, sar_denot_off0; apply EEo; reflexivity | rewrite Q23, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q24, sar_denot_off0; apply EEo; reflexivity | rewrite Q25, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q26, sar_denot_off0; apply EEo; reflexivity | rewrite Q27, sar_denot_off0; apply EEo; reflexivity].
  + rewrite Q9, E33. reflexivity.
  + rewrite Q18, U33. reflexivity.
  + rewrite Q20, E32. reflexivity.
  + rewrite Q21. exact DSH.
  + rewrite Q8, (EEo 8%nat 8%bv eq_refl). exact R8.
  + rewrite Q10, E33. reflexivity.
  + rewrite Q11, (EEo 19%nat 19%bv eq_refl). exact R19.
  + rewrite Q1r. reflexivity.
  + exact HFR3.
  + exact Hc.
  + exact Hlen.
  + exact VN.
  + exact HQ1.
  + exact HROD3.
  + exact HSTR3.
  + exact HO1.
  + exact HO3.
  + exact HO4.
  + exact HO5.
Qed.

(* ---------- what rec_calls_free(&spill, 1) writes, and what it keeps ---------- *)
(* its footprint: the spill's nargs field and the bytes of the spill's argument blocks *)
Lemma sar_rcf_fp_inv : forall P a, inFP (rcf_fp A_REC_SPILL [P]) a ->
(A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) \/ exists p n, In (p, n) P /\ p <= a < p + req_size n.
Proof.
intros P a (r & Hr & Ha). unfold rcf_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- left. cbn [length seq map] in Hr. destruct Hr as [<- | []]. cbn [fst snd Z.of_nat] in Ha.
  unfold CALL_SIZE, CALL_OFF_NARGS in Ha. lia.
- right. destruct (inFP_ablocks_fp_inv (concat [P]) a (ex_intro _ r (conj Hr Ha))) as (p & n & Hin & Hpa).
  exists p, n. split; [|exact Hpa]. cbn [concat] in Hin. rewrite app_nil_r in Hin. exact Hin.
Qed.
Lemma sar_rcf_bsum_nonneg : forall l : list (Z * Z), (forall pn, In pn l -> 0 <= snd pn) -> 0 <= bsum l.
Proof.
induction l as [|x l IH]; intros H; [unfold bsum; cbn [fold_right]; lia|]. rewrite bsum_cons.
pose proof (H x (or_introl eq_refl)). pose proof (IH (fun pn Hpn => H pn (or_intror Hpn))). lia.
Qed.
(* the verb survives a call that keeps its block (when it lies in one) and writes no read-only byte *)
Lemma sar_rcf_str_kept : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 pv x,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
AR SEGS B lyc Sc Wc memc mdc ->
~ YI16.sink_open_fp FP1 -> (forall a, in_roP SEGS RLO RHI a -> ~ inFP FP1 a) ->
(forall b k, In (b, k) (ablocks B lyc Sc) -> b <= pv -> pv + (Z.of_nat (length x) + 1) <= b + k ->
   In (b, k) (ablocks B ly2 S2) /\ forall i, 0 <= i < k -> rdW W2 mem2 (b + i) = rdW Wc memc (b + i)) ->
sar_str_ok lyc Sc Wc memc pv (Some x) -> sar_str_ok ly2 S2 W2 mem2 pv (Some x).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc ly2 S2 W2 mem2 md2 k1 pv x HJ1 HAR Hso HFro HBK (x' & Hx & (b & k & Hbk & Hb1 & Hb2) & Hstr & Hn).
injection Hx as Hx. subst x'.
destruct (HBK b k Hbk Hb1 Hb2) as [Hbk2 Hkeep].
exists x. split; [reflexivity|]. split; [exists b, k; split; [exact Hbk2 | lia]|]. split; [|exact Hn].
apply (rastr_kept (rdW Wc memc)); [exact Hstr|].
intros i Hi. replace (pv + i) with (b + (pv + i - b)) by lia. apply Hkeep. lia.
Qed.

(* ---------- record()'s spill arm: the call of rec_calls_free(&spill, 1) (0x8c6b0) and what follows ---------- *)
Lemma sar_call_RCF : forall ly S W regs mem md ch R O Q id pv verb (regsx : bvmap 5 word) memx mdx,
afn_pre SEGS B SUP_AFTER_REPLY_STK ly S W regs mem md ch ->
ajournal SEGS B SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) ly S W mem md [] ly S W memx mdx 0 ->
st_nev S + EV_SUP_AFTER_REPLY R <= EV_MAX ->
blocks_bytes S + LIVE_SUP_AFTER_REPLY id verb <= LIVE_MAX ->
mo_ok MT S (XM_SUP_AFTER_REPLY MT R id verb) -> frm0 fx ->
Z.of_nat (length (frames S)) <= 8 -> -2 ^ 31 <= id < 2 ^ 31 ->
getr regsx 2 = w64 (spZ regs - 64) -> getr regsx 3 = w64 (as_gp B) -> getr regsx 4 = w64 (as_tp B) ->
(forall r, 22 <= r <= 27 -> getr regsx (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr regsx 9 = w64 A_REC_SPILL -> getr regsx 20 = w64 SB -> getr regsx 8 = w64 pv -> getr regsx 19 = w64 id ->
getr regsx 10 = w64 A_REC_SPILL -> getr regsx 11 = w64 1 ->
getr regsx 1 = Z_to_bv 64 (BASE + SAR_RET_RCF) ->
sar_frame (rdW W memx) (spZ regs) regs ->
length (r_calls R) = 16%nat ->
arep_at (ablocks B ly S) (rdW W memx) A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
arodata_okP SEGS RLO RHI B (rdW W memx) ->
(forall x, verb = Some x -> Forall (fun qk => iv_apart pv (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
sar_str_ok ly S W memx pv verb ->
SRr SEGS W (mkCfg (mkst regsx (Z_to_bv 64 (SIG CS_rec_calls_free)) memx (seg_rom SEGS)) mdx)
(sar_postF ly S W regs mem md R O id verb).
Proof.
intros ly S W regs mem md ch R O Q id pv verb regsx memx mdx
HPRE HJ HEV HLIVE HMOK HRM HFRM Hid R2 R3 R4 Rhi R9 R20 R8 R19 R10 R11 R1 HFR Hlen HQ HOQ HROD HARG HSTR.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof (proj1 HJ) as HAR.
assert (HSTKv : SUP_AFTER_REPLY_STK = 16592) by (vm_compute; reflexivity).
assert (HRCv : REC_CALLS_FREE_STK = 16496) by (vm_compute; reflexivity).
assert (Hsp : 2 ^ 46 + 64 <= spZ regs <= 2 ^ 47) by (unfold YG0f.ASAN_CEIL in *; lia).
assert (Psp : spZ regsx = spZ regs + -64) by (unfold spZ at 1; rewrite R2; rewrite unsigned_lit_small by lia; lia).
pose proof (sar_pv_bound _ _ _ _ _ pv verb HAR HSTR) as Hpv.
assert (Hs0 : s0Z regsx < alloc_ceiling).
{ unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by (unfold YG0f.ASAN_CEIL in *; lia). lia. }
(* the spill slot's call: its nargs field and its argument blocks, all of them the recorder's (in O) *)
pose proof HQ as (_ & _ & _ & (_ & _ & _ & _ & HSPc & _) & _ & _ & _ & _).
destruct HSPc as (Hfn & Hl6 & HlP & HBF & HBN & HNDs & HARGS).
assert (HSPin : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q)).
{ intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
assert (HQin : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly S)) by exact (lay_blocks_in _ _ _ _ _ _ HQ).
assert (HSPO : forall pn, In pn (l_spill Q) -> In pn O) by (intros pn Hpn; apply HOQ; exact (HSPin pn Hpn)).
assert (HSPbl : forall p n, In (p, n) (l_spill Q) -> 4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n).
{ intros p n Hpn. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (HQin _ (HSPin _ Hpn))) as (_ & H1 & H2 & _ & _ & _ & H3).
  split; [exact H1|]. split; [exact H2 | lia]. }
assert (HEVeq : EV_REC_CALLS_FREE [l_spill Q] = rec_spill_frees R).
{ unfold EV_REC_CALLS_FREE, rec_spill_frees. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H]; [lia|].
  cbn [concat]. rewrite app_nil_r, HlP. reflexivity. }
assert (HXM : XM_REC_CALLS_FREE MT [l_spill Q] = rec_spill_frees R * mo_free MT).
{ unfold XM_REC_CALLS_FREE. rewrite <- HEVeq. reflexivity. }
(* the call's footprint: below the stack, none of the read-only bytes, not the byte 0 *)
set (FP1 := rcf_fp A_REC_SPILL [l_spill Q]).
assert (HFP1 : forall a, inFP FP1 a ->
  (A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) \/ exists p n, In (p, n) (l_spill Q) /\ p <= a < p + req_size n)
  by (intros a Ha; exact (sar_rcf_fp_inv (l_spill Q) a Ha)).
assert (HFPb : forall a, inFP FP1 a -> 4096 <= a < alloc_ceiling).
{ intros a Ha. destruct (HFP1 a Ha) as [Hn | (p & n & Hpn & Hpa)].
  - unfold A_REC_SPILL in Hn. lia.
  - destruct (HSPbl p n Hpn) as (H1 & H2 & _). lia. }
assert (HsoF : ~ YI16.sink_open_fp FP1) by (intros Hf; pose proof (HFPb 0 Hf); lia).
assert (HFro : forall a, in_roP SEGS RLO RHI a -> ~ inFP FP1 a).
{ intros a Hr Hf. destruct (cmd_ro_prog_apart a Hr) as [Himg Hnp]. destruct (HFP1 a Hf) as [Hn | (p & n & Hpn & Hpa)].
  - apply Hnp. apply sar_in_PG. unfold in_rec. right. unfold A_REC_SPILL in Hn. unfold A_REC_SPILL, SC_SIZE. lia.
  - exact (recb_heap_noimg_m B ly S W memx mdx p n a HAR (HQin _ (HSPin _ Hpn)) Hpa Himg). }
assert (HAWR : forall a, inFP FP1 a -> awr_byte SEGS B SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) (ablocks B ly S)
  (ablocks B ly S) (frames S) ly [] a).
{ intros a Ha. destruct (HFP1 a Ha) as [Hn | (p & n & Hpn & Hpa)].
  - apply sar_awr_rec. unfold in_rec. right. unfold A_REC_SPILL in Hn. unfold A_REC_SPILL, SC_SIZE. lia.
  - unfold awr_byte. right. left. split.
    + assert (Hin : inFP (ablocks_fp O) (p + (a - p))) by exact (inFP_ablocks_fp O p n (a - p) (HSPO _ Hpn) ltac:(lia)).
      replace (p + (a - p)) with a in Hin by lia. destruct Hin as (r & Hr & Hrr).
      exists r. split; [right; right; exact Hr | exact Hrr].
    + exists p, n. split; [exact (HQin _ (HSPin _ Hpn)) | exact Hpa]. }
(* the premises of rec_calls_free's contract *)
assert (HLEN2 : (length [l_spill Q] <= 2)%nat) by (cbn [length]; lia).
assert (HHOME : rcf_home B ly S W memx A_REC_SPILL (CALL_SIZE * Z.of_nat (length [l_spill Q]))).
{ unfold rcf_home. right. left. unfold CALL_SIZE, SC_SIZE. cbn [length]. lia. }
assert (HENT : forall i P, nth_error [l_spill Q] i = Some P ->
  (length P <= 6)%nat /\
  aval_mem (rdW W memx) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
  forall a pn, nth_error P a = Some pn ->
    aval_mem (rdW W memx) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
    In pn (ablocks B ly S)).
{ intros i P Hi. destruct i as [|i]; [|destruct i; cbn in Hi; discriminate Hi].
  cbn [nth_error] in Hi. injection Hi as <-. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
  split; [lia|]. split; [rewrite HlP; exact HBN|].
  intros a pn Ha. destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Hs.
  - destruct (HARGS a s pn Hs Ha) as (G1 & _ & G3 & _). split; [exact G1 | exact G3].
  - exfalso. apply nth_error_None in Hs.
    pose proof (proj1 (nth_error_Some (l_spill Q) a) ltac:(rewrite Ha; discriminate)). lia. }
assert (HNEV : st_nev S + EV_REC_CALLS_FREE [l_spill Q] <= EV_MAX).
{ rewrite HEVeq. unfold EV_SUP_AFTER_REPLY, EV_ARG_I, EV_XSTRDUP in HEV. lia. }
assert (HXS0 : 0 <= XM_XSTRDUP MT (sarg verb)) by (unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
assert (HAI0 : 0 <= XM_ARG_I MT id) by (unfold XM_ARG_I, XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
assert (HMOKc : mo_ok MT S (XM_REC_CALLS_FREE MT [l_spill Q])).
{ apply (mok_station MT S S (XM_SUP_AFTER_REPLY MT R id verb) 0 _ MTL HMOK (mle_start MT S MTL)).
  - unfold XM_REC_CALLS_FREE. apply Z.mul_nonneg_nonneg; [lia | exact (mo_free_nonneg MT MTL)].
  - rewrite HXM. unfold XM_SUP_AFTER_REPLY. lia. }
lazymatch type of (TRCF fx ly S W regsx memx mdx [] A_REC_SPILL [l_spill Q]) with
| context [apost_base _ _ _ _ _ _ _ _ _ _ _ ?K0] => pose (K := K0)
end.
rewrite sar_sig_rcf.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsx memx _ SUP_AFTER_REPLY_STK (spZ regs) (sar_FP O) ly S W mem md [] ly S mdx 0
    REC_CALLS_FREE_STK FP1 (EV_REC_CALLS_FREE [l_spill Q]) (-64) (Z_to_bv 64 (BASE + SAR_RET_RCF)) [] K HJ Psp);
  [ reflexivity | lia | rewrite HRCv; lia | rewrite HSTKv, HRCv; lia
  | exact R3 | exact R4 | exact R1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]
  | unfold SAR_RET_RCF; rewrite unsigned_lit_small by lia; lia
  | left; split; [left; exact Hs0 | reflexivity]
  | intros HPREx; eapply SRr_mono;
    [ apply (TRCF fx ly S W regsx memx mdx [] A_REC_SPILL [l_spill Q] HPREx
        HROD R10 R11 HLEN2 HHOME ltac:(unfold A_REC_SPILL; reflexivity) HENT
        ltac:(cbn [concat]; rewrite app_nil_r; exact HNDs) HNEV HMOKc)
    | cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
      exists ly3, S3, regs3, mem3, md3; split; [rewrite R1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
  | exact HAWR
  | intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _; exfalso; pose proof (HFPb a Ha); lia ]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJi & HP2 & HK2).
unfold K in HK2. cbv beta in HK2.
destruct HK2 as (Hperm & _ & _ & HKB & _ & HSP & _ & _ & HMLE2).
pose proof HJi as (HAR2 & _ & _ & _ & _ & Hfr2 & _ & _ & F1 & _).
(* the registers the call keeps *)
assert (X2 : getr regs2 2 = w64 (spZ regs - 64)) by sar_keep HP2 2 R2.
assert (X3 : getr regs2 3 = w64 (as_gp B)) by sar_keep HP2 3 R3.
assert (X4 : getr regs2 4 = w64 (as_tp B)) by sar_keep HP2 4 R4.
assert (X8 : getr regs2 8 = w64 pv) by sar_keep HP2 8 R8.
assert (X9 : getr regs2 9 = w64 A_REC_SPILL) by sar_keep HP2 9 R9.
assert (X19 : getr regs2 19 = w64 id) by sar_keep HP2 19 R19.
assert (X20 : getr regs2 20 = w64 SB) by sar_keep HP2 20 R20.
assert (Xhi : forall r, 22 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)). exact (Rhi r Hr). }
(* the blocks: the spill's argument blocks freed, every other block kept *)
assert (HnoO : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn Hno. apply (Permutation_in _ Hperm) in Hpn. apply in_app_or in Hpn as [Hpn | Hpn]; [exact Hpn|].
  exfalso. apply Hno. apply HSPO. cbn [concat] in Hpn. rewrite app_nil_r in Hpn. exact Hpn. }
assert (H2in : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn. }
assert (HND : List.NoDup (ablocks B ly2 S2 ++ concat [l_spill Q])).
{ apply (Permutation_NoDup Hperm). exact (recb_ablocks_nodup_m B ly S W memx mdx HAR). }
assert (H2sp : forall pn, In pn (ablocks B ly2 S2) -> ~ In pn (l_spill Q)).
{ intros pn H1 H2. apply (list_nodup_app_disj _ _ pn HND H1). cbn [concat]. rewrite app_nil_r. exact H2. }
destruct (HSP R Q HQ eq_refl eq_refl) as (Q1 & HQ1 & HQ1e).
assert (HQ1a : forall pn, In pn (lay_blocks Q1) -> In pn O).
{ intros pn Hpn. apply HOQ. apply HQ1e in Hpn. unfold lay_blocks.
  apply in_app_or in Hpn as [H | H]; apply in_or_app; [left; exact H | right; apply in_or_app; right; exact H]. }
assert (HQ1b : forall pn, In pn O -> ~ In pn (l_spill Q) -> In pn (lay_blocks Q1)).
{ intros pn Hpn Hns. apply HQ1e. apply HOQ in Hpn. unfold lay_blocks in Hpn.
  apply in_app_or in Hpn as [H | H]; apply in_or_app; [left; exact H|]. right.
  apply in_app_or in H as [H | H]; [exfalso; exact (Hns H) | exact H]. }
assert (BB2 : blocks_bytes S2 = bsum (ablocks B ly2 S2)) by (apply blocks_bytes_bsum).
assert (BB : blocks_bytes S = bsum (ablocks B ly S)) by (apply blocks_bytes_bsum).
rewrite (bsum_perm _ _ Hperm), bsum_app in BB.
assert (BS0 : 0 <= bsum (concat [l_spill Q])).
{ cbn [concat]. rewrite app_nil_r. apply sar_rcf_bsum_nonneg. intros pn Hpn.
  pose proof (sar_lay_pos _ _ _ _ HQ pn (HSPin pn Hpn)). lia. }
apply (sar_seg_B ly S W regs mem md ch R O id pv verb ly2 S2 W2 regs2 mem2 md2 (0 + EV_REC_CALLS_FREE [l_spill Q])
  A_REC_SPILL Q1 SAR_RET_RCF HPRE HJ2).
- rewrite HEVeq. lia.
- exact HEV.
- lia.
- exact HMOK.
- rewrite <- HXM. exact HMLE2.
- exact HRM.
- lia.
- rewrite Hfr2. exact HFRM.
- exact Hid.
- exact X2. - exact X3. - exact X4. - exact Xhi. - exact X9. - exact X20. - exact X8. - exact X19.
- right. reflexivity.
- apply (sar_frame_kept (rdW W memx)); [exact HFR|]. intros a Ha. apply F1.
  + unfold YG0f.ASAN_CEIL in *. lia.
  + lia.
  + intros Hf. pose proof (HFPb a Hf). lia.
- symmetry. exact (sar_entry_full R Hlen).
- lia.
- split.
  + exact (lay_blocks_in _ _ _ _ _ _ HQ1).
  + intros rd' BF BA KG KB.
    assert (KB' : blocks_keptA (ablocks B ly2 S2) (rdW W2 mem2) rd' (lay_blocks Q1)).
    { intros [p n] Hpn. split; [exact (lay_blocks_in _ _ _ _ _ _ HQ1 _ Hpn)|]. intros i Hi. exact (KB p n i Hpn Hi). }
    pose proof (sar_rep_record_full (ablocks B ly2 S2) (ablocks B ly2 S2) (rdW W2 mem2) rd'
      (set_spill R (fst (r_spill R), [])) Q1 REC_AFTER_REPLY HQ1 Hlen eq_refl
      ltac:(unfold REC_AFTER_REPLY, REC_FN_COUNT; lia) BF BA KG KB') as HR.
    rewrite (sar_record_full_eq (set_spill R (fst (r_spill R), [])) REC_AFTER_REPLY [] Hlen) in HR.
    rewrite (sar_record_full_eq R REC_AFTER_REPLY [] Hlen). exact HR.
- eapply (@arodata_ok_journalP _ _ SEGS RLO RHI RELRO_IMG RRO B); [exact HJi | exact HFro | exact HROD].
- destruct verb as [x|]; [|destruct HSTR as (x0 & Hx0 & _); discriminate Hx0].
  apply (sar_rcf_str_kept _ _ _ ly S W memx mdx ly2 S2 W2 mem2 md2 _ pv x HJi HAR HsoF HFro); [|exact HSTR].
  intros b k Hbk Hb1 Hb2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR Hbk) as (_ & _ & _ & _ & _ & _ & Hk0).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
  assert (HbO : ~ In (b, k) O).
  { intros HbO. pose proof (proj1 (Forall_forall _ _) (HARG x eq_refl) (b, k) HbO) as Hap.
    cbn [fst snd] in Hap. unfold iv_apart in Hap. lia. }
  split; [exact (HnoO _ Hbk HbO)|]. intros i Hi. exact (HKB b k i (HnoO _ Hbk HbO) Hi).
- intros pn Hpn. left. exact (HQ1a pn Hpn).
- exact HnoO.
- intros pn Hpn. destruct (in_dec recb_pair_dec pn O) as [HO | HnO].
  + right. exact (HQ1b pn HO (H2sp pn Hpn)).
  + left. split; [exact (H2in pn Hpn) | exact HnO].
- intros pn Hpn Hno. apply (Permutation_in _ Hperm) in Hpn. apply in_app_or in Hpn as [Hpn | Hpn]; [exfalso; exact (Hno Hpn)|].
  apply HSPO. cbn [concat] in Hpn. rewrite app_nil_r in Hpn. exact Hpn.
Qed.


(* ---------- the entry: the prologue and record()'s choice of the slot ---------- *)
(* the regions of the entry segment: the 64-byte frame, the two words of the shadow base, g_rec.ncalls (its
   loaded value `nv`: the atom on the table arm, the literal 16 on the spill arm) *)
Definition sar_rs0 (nv : sv) : YP09.smem :=
[rbt_stack (-64) []; got_regionP; bcell_regionP RB_SB; rbt_ncalls nv].

Lemma sar_entry_seed : forall ly1 S1 (W1 : world SEGS) mem1 md1 (regs1 : bvmap 5 word) E sp n c nv lo hi,
AR SEGS B ly1 S1 W1 mem1 md1 ->
rbt_env_ok E sp n c -> 2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 0 <= n <= 16 -> lo <= n <= hi ->
rbt_slot_ok c ->
bv_unsigned (getr regs1 2) = sp ->
(forall a, sp - 64 <= a < sp -> apresent (w_H W1) mem1 a) ->
aval_mem (rdW W1 mem1) (A_G_REC + OFF_NCALLS) 4 n ->
sv_denot E nv = Z_to_bv 64 n ->
regs_ok E sr_atoms regs1 ->
st_ok_pi SEGS VAL E (mkSS AF_sup_after_reply sr_atoms (sar_rs0 nv) None (rbt_facts lo hi))
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + AF_sup_after_reply)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS Bxr rbt_SH E (mrestrict (w_H W1) mem1).
Proof.
intros ly1 S1 W1 mem1 md1 regs1 E sp n c nv lo hi HAR HE Hsp Hsp16 Hn Hlh Hc Hsp2 Hpres HNC HV HREG.
pose proof HE as (HEI & E2 & ESB & EN & EC).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
pose proof (pal_got_cell B TL) as Hgc.
assert (EG : ew E RB_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)),
      (rbt_grec_val VOBJS); reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (EV0 : VAL (A_OBJ 0) = 0xa63f0)
  by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (EV12 : VAL (A_OBJ 12) = 0xb10b8)
  by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split; [| exact (rbt_sh_ok B LAWS HB ly1 S1 W1 mem1 md1 E sp n c HAR HE Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- exact HREG.
- vm_compute. reflexivity.
- unfold sar_rs0, rbt_stack, got_regionP, bcell_regionP, rbt_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 2%nat sp E2) by lia. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite rbt_pow8; pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 Bxr SHADOW_OFF);
    [cbn [sv_denot Bxr]; rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite rbt_pow8; cbv [SHADOW_OFF]; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB RB_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (cmd_prog_writable ly1 S1 W1 mem1 md1); [exact HAR|].
      apply recb_grec_in. unfold OFF_NCALLS, REC_SIZE, A_G_REC in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 nv n);
    [exact HV | rewrite rbt_pow4; lia | cbn; lia |].
    exact (RecBLemmas.val_mem_view SEGS (w_H W1) mem1 (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold sar_rs0, rbt_stack, got_regionP, bcell_regionP, rbt_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB RB_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  rewrite (VB 2%nat sp E2) by lia.
  rewrite EV0, EV12.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_NCALLS in *. repeat split; lia.
- exact (rbt_facts_ok VOBJS E sp n c lo hi HE Hsp Hsp16 Hlh Hn Hc).
Qed.

Lemma sar_aval_addr : forall (rd : reader) a a' n v, aval_mem rd a n v -> a = a' -> aval_mem rd a' n v.
Proof. intros rd a a' n v H <-. exact H. Qed.
(* the saved registers, one 8-byte word each *)
Lemma sar_frame_of : forall (rd : reader) sp0 (regs0 : bvmap 5 word),
aval_mem rd (sp0 + -8) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 1))) -> aval_mem rd (sp0 + -16) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 8))) ->
aval_mem rd (sp0 + -24) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 9))) -> aval_mem rd (sp0 + -32) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 18))) ->
aval_mem rd (sp0 + -40) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 19))) -> aval_mem rd (sp0 + -48) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 20))) ->
aval_mem rd (sp0 + -56) 8 (bv_unsigned (getr regs0 (Z_to_bv 5 21))) -> sar_frame rd sp0 regs0.
Proof.
intros rd sp0 regs0 H1 H8 H9 H18 H19 H20 H21 j r Hj.
do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <-;
  first [ apply (sar_aval_addr rd _ _ _ _ H1); lia | apply (sar_aval_addr rd _ _ _ _ H8); lia
        | apply (sar_aval_addr rd _ _ _ _ H9); lia | apply (sar_aval_addr rd _ _ _ _ H18); lia
        | apply (sar_aval_addr rd _ _ _ _ H19); lia | apply (sar_aval_addr rd _ _ _ _ H20); lia
        | apply (sar_aval_addr rd _ _ _ _ H21); lia ] |]).
destruct j; discriminate Hj.
Qed.
(* a saved register's word in the frame region of a walk state *)
Lemma sar_frame_chunk : forall E (H : word -> bool) (m : word -> option byte) sp0 lo hi wlo whi cs (r : nat) (rr : bv 5) off
(regs0 : bvmap 5 word),
region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sp0 ->
In (YP09.mkChunk off (CVal 8 (SOff r 0))) cs -> ew E r = getr regs0 rr ->
aval_mem (aview SEGS H m) (sp0 + off) 8 (bv_unsigned (getr regs0 rr)).
Proof.
intros E H m sp0 lo hi wlo whi cs r rr off regs0 HR U Hin Er.
pose proof (field_of_region_any (segs := SEGS) E _ 2 sp0 cs lo hi wlo whi off 8 (SOff r 0) HR U Hin ltac:(cbn; lia)) as V.
rewrite sar_denot_off0, Er in V. change (N.to_nat 8) with 8%nat in V.
pose proof (bv_unsigned_in_range 64 (getr regs0 rr)) as HBr. change (bv_modulus 64) with (2 ^ 64) in HBr.
rewrite Z.mod_small in V by (cbn; lia).
exact (aval_mem_view SEGS H m _ 8 _ V).
Qed.

(* the lists of the recorder's blocks after record() adds an empty call *)
Lemma sar_lay_snoc : forall L s a r, lay_blocks (RLay (L ++ [[]]) s a r) = lay_blocks (RLay L s a r).
Proof. intros L s a r. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat]. rewrite app_nil_r. reflexivity. Qed.

(* the slot the inlined record() computes on the table arm: g_rec + 16 + 56 * ncalls (sup_worker_list.v's
   swl_denot_slot) *)
Lemma sar_denot_slot : forall E n c,
ew E RB_N = Z_to_bv 64 n -> 0 <= n <= 16 -> ew E RB_GREC = Z_to_bv 64 A_G_REC ->
ew E RB_C = Z_to_bv 64 c -> c = A_G_REC + OFF_CALLS + CALL_SIZE * n ->
sv_denot E (SOff RB_C 0) =
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff RB_N 0) (SLit 56)) (SLit 16)) (SOff RB_GREC 0)).
Proof.
intros E n c HN Hn HG HC ->.
apply bv_eq. cbn [sv_denot].
assert (HG64 : 0 <= A_G_REC < 2 ^ 64) by (cbv [A_G_REC]; lia).
assert (HC64 : 0 <= A_G_REC + OFF_CALLS + CALL_SIZE * n < 2 ^ 64) by (cbv [A_G_REC OFF_CALLS CALL_SIZE]; lia).
assert (HN64 : 0 <= n < 2 ^ 64) by lia.
rewrite HN, HG, HC.
rewrite (unsigned_lit_small n HN64), (unsigned_lit_small _ HG64), (unsigned_lit_small _ HC64).
rewrite !Z.add_0_r, zmd64_sound, !zalu64_sound.
cbv [zmd64 zalu64 zcanon M64 zmd_raw zalu_raw bv_swrap bv_half_modulus bv_modulus].
cbn [Z.of_N]. cbv [A_G_REC OFF_CALLS CALL_SIZE] in *.
assert (H56 : 56 mod 2 ^ 64 = 56) by reflexivity.
assert (H16 : 16 mod 2 ^ 64 = 16) by reflexivity.
assert (HGR : 6174528 mod 2 ^ 64 = 6174528) by reflexivity.
assert (Hnm : n mod 2 ^ 64 = n) by (apply Z.mod_small; lia).
rewrite H56, H16, HGR, Hnm, !Zmod_mod.
rewrite (Z.mod_small (n * 56) (2 ^ 64)) by lia.
rewrite (Z.mod_small (n * 56 + 16) (2 ^ 64)) by lia.
rewrite (Z.mod_small (n * 56 + 16 + 6174528) (2 ^ 64)) by lia.
f_equal. f_equal. lia.
Qed.

(* the statement (sup_after_reply_c.v:66-104) with its post named sar_postF *)
Lemma sar_core : forall ly S W (regs : bvmap 5 word) mem md ch (id pv : Z) (verb : option (list byte)) (R : rstate)
 (O : list (Z * Z)),
afn_pre SEGS B SUP_AFTER_REPLY_STK ly S W regs mem md ch ->
frm0 fx ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
getr regs 11 = w64 pv -> 0 <= pv < 2 ^ 64 ->
(exists x, verb = Some x /\
 in_blockA (ablocks B ly S) pv (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pv x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pv (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
rec_repA B ly S (rdW W mem) R O ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_AFTER_REPLY R <= EV_MAX -> blocks_bytes S + LIVE_SUP_AFTER_REPLY id verb <= LIVE_MAX ->
mo_ok MT S (XM_SUP_AFTER_REPLY MT R id verb) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_after_reply) regs mem md) (sar_postF ly S W regs mem md R O id verb).
Proof.
intros ly S W regs mem md ch id pv verb R O PRE HRM HROD HROOK R10 Hid R11 Hpv64 HVERB HREP HFRM HEV HLIVE HMOK.
pose proof PRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
assert (HSTKv : SUP_AFTER_REPLY_STK = 16592) by (vm_compute; reflexivity).
assert (Hsp46 : 2 ^ 46 + 64 <= spZ regs <= 2 ^ 47) by (unfold YG0f.ASAN_CEIL in *; lia).
destruct HREP as (Q & HAREP & HOQ).
pose proof HAREP as (Hgr8 & Hsc8 & Hapart & HG1 & HANS & HRPL & HSCAL & HOWN).
pose proof HG1 as (Hlen16 & HlenQ & HNC & HCALLS & HSPILL & HSPMAX).
set (n := Z.of_nat (length (r_calls R))) in *.
set (c := sar_entry R).
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
assert (HcOK : sar_slot_ok c) by (apply sar_entry_ok; exact Hlen16).
assert (Hc : rbt_slot_ok c).
{ destruct (sar_slot_bounds c HcOK) as (Hcb & Hc8 & [[H1 H2] | H3]); [left | right; exact H3].
  split; [exact H1|]. split; [exact H2 | exact Hc8]. }
destruct (sar_slot_bounds c HcOK) as (Hcb & Hc8 & Hcr). unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb.
set (E := Eimg (Ereg regs (rbt_extra regs n c))).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HENV : rbt_env_ok E (spZ regs) n c).
{ split; [exact HEI|].
  unfold E.
  rewrite (Eimg_low (Ereg regs (rbt_extra regs n c)) 2%nat ltac:(unfold A_TEXT; lia)).
  rewrite (Eimg_low (Ereg regs (rbt_extra regs n c)) RB_SB ltac:(unfold RB_SB, A_TEXT; lia)).
  rewrite (Eimg_low (Ereg regs (rbt_extra regs n c)) RB_N ltac:(unfold RB_N, A_TEXT; lia)).
  rewrite (Eimg_low (Ereg regs (rbt_extra regs n c)) RB_C ltac:(unfold RB_C, A_TEXT; lia)).
  rewrite (ew_Ereg_nat regs (rbt_extra regs n c) 2%nat 2%bv eq_refl).
  change RB_SB with (32 + 0)%nat. change RB_N with (32 + 1)%nat. change RB_C with (32 + 2)%nat.
  rewrite (ew_Ereg_extra regs (rbt_extra regs n c) 0%nat),
          (ew_Ereg_extra regs (rbt_extra regs n c) 1%nat),
          (ew_Ereg_extra regs (rbt_extra regs n c) 2%nat).
  cbn [rbt_extra nth map app].
  split; [unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [reflexivity | split; reflexivity]. }
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
  by (intros m rr Hm; unfold E; apply ew_Eimg_Ereg_nat; exact Hm).
assert (U2e : bv_unsigned (ew E 2) = spZ regs) by (rewrite (proj1 (proj2 HENV)); apply unsigned_lit_small; lia).
pose proof (ajournal_init SEGS B SUP_AFTER_REPLY_STK (sar_FP O) ly S W regs mem md ch PRE) as HJ.
(* the verb at the entry, as the segments carry it *)
assert (HSTRe : sar_str_ok ly S W mem pv verb).
{ destruct HVERB as (x & Hx & Hb & Hs & Hnx & _). exists x. split; [exact Hx|]. split; [exact Hb|]. split; [exact Hs | exact Hnx]. }
assert (HARG : forall x, verb = Some x -> Forall (fun qk => iv_apart pv (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O).
{ intros x0 Hx0. destruct HVERB as (x & Hx & _ & _ & _ & HF). rewrite Hx0 in Hx. injection Hx as Hx. subst x. exact HF. }
assert (HREG : regs_ok E sr_atoms regs) by (unfold E; apply regs_ok_Eimg_Ereg).
clearbody E.
pose proof HENV as (_ & E2e & ESB & EN & EC).
assert (EG : ew E RB_GREC = Z_to_bv 64 A_G_REC)
  by (rewrite (img_env_atomP E RB_GREC HEI ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)), (rbt_grec_val VOBJS); reflexivity).
assert (UG : bv_unsigned (ew E 285) = A_G_REC)
  by exact (eq_trans (HEI RB_GREC ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)) (rbt_grec_val VOBJS)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact ESB.
assert (E33n : ew E 33 = Z_to_bv 64 n) by exact EN.
(* the blocks the walk never writes *)
assert (Hblk : forall p0 n0 i, In (p0, n0) (ablocks B ly S) -> 0 <= i < n0 ->
  0 <= p0 + i < alloc_ceiling /\ ~ in_rec (p0 + i)).
{ intros p0 n0 i Hpn Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HAR Hpn) as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos n0 ltac:(lia)) as [_ Hreq].
  split; [lia|]. apply (sar_blk_not_rec _ _ _ _ _ p0 n0 i HAR Hpn). lia. }
destruct (Z.eq_dec n 16) as [E16 | Hne16].
- (* record()'s spill arm: the table is full (ncalls = 16) *)
  assert (Hfull : length (r_calls R) = 16%nat) by (unfold n in E16; lia).
  destruct (sar_entry_seed ly S W mem md regs E (spZ regs) n c (SLit 16) 16 16
    HAR HENV ltac:(lia) Hsp16 Hn ltac:(lia) Hc
    ltac:(reflexivity) ltac:(intros a Ha; apply Hpres; rewrite HSTKv; lia) HNC
    ltac:(rewrite E16; reflexivity)
    HREG) as [HS SHOK].
  unfold cfg_at, w64.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact U2e | cbn [YP09.r_wlo]; rewrite HSTKv; lia | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := RB_GREC);
      [reflexivity | exact (eq_trans (HEI RB_GREC ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)) (rbt_grec_val VOBJS)) | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply sar_awr_rec. unfold in_rec, A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
    apply (awr_ok_nil SEGS B). }
  lazymatch type of HS with
  | st_ok _ _ ?ssx ?msx =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) sar_frame_r) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) sar_frame_r) in
    pose proof (st_ok_region_nth (segs := SEGS) E ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRD0;
    pose proof (st_ok_region_nth (segs := SEGS) E ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HRD3;
    cbn [ms_mem restrict mkst] in HRD0, HRD3
  end.
  lazymatch goal with HFx : frame_of E _ (mrestrict _ mem) (mrestrict _ ?m3) |- _ => rename HFx into HFr; set (memX := m3) in * end.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) -> ~ (A_G_REC + 8 <= a < A_G_REC + 12) ->
    rdW W memX a = rdW W mem a).
  { intros a Ha H1 H2.
    apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem memX
      (fun a => (spZ regs - 64 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr);
    [ | exact Ha | intros [H|H]; [exact (H1 H) | exact (H2 H)] ].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hqq | Hin]; [injection Hqq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2e, ?UG in Hrr;
      first [lia | left; lia | right; lia] |]).
    destruct Hin. }
  assert (KO : forall a, 0 <= a < alloc_ceiling -> ~ in_rec a -> rdW W memX a = rdW W mem a).
  { intros a Ha Hn0. apply KEEP; [unfold YG0f.ASAN_CEIL in *; lia | rewrite HSTKv in *; unfold YG0f.ASAN_CEIL in *; lia |].
    intros Hin. apply Hn0. left. unfold A_G_REC, REC_SIZE in *. lia. }
  pose proof (field_of_region (segs := SEGS) E _ 285 A_G_REC _ _ _ _ _ 8 4 (SLit 16) 16 HRD3 UG ltac:(cbn; tauto) eq_refl
    ltac:(cbn; lia) ltac:(cbn; lia)) as VNC.
  change (N.to_nat 4) with 4%nat in VNC. apply (aval_mem_view SEGS) in VNC.
  assert (KR : forall a, in_rec a -> rdW W memX a = rdW W mem a).
  { intros a Ha. assert (Hd : (A_G_REC + 8 <= a < A_G_REC + 12) \/ ~ (A_G_REC + 8 <= a < A_G_REC + 12)) by lia.
    destruct Hd as [Hd | Hd].
    - set (k := Z.to_nat (a - (A_G_REC + 8))).
      assert (Hk : (k < 4)%nat) by (unfold k; lia).
      replace a with (A_G_REC + OFF_NCALLS + Z.of_nat k) by (unfold k, OFF_NCALLS; lia).
      rewrite (HNC k Hk). change (A_G_REC + OFF_NCALLS) with (A_G_REC + 8). rewrite (VNC k Hk). rewrite E16. reflexivity.
    - apply KEEP; [unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia
      | unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia | exact Hd]. }
  assert (HFRX : sar_frame (rdW W memX) (spZ regs) regs).
  { apply sar_frame_of.
    - exact (sar_frame_chunk E (w_H W) memX (spZ regs) _ _ _ _ _ 1 (Z_to_bv 5 1) (-8) regs HRD0 U2e ltac:(cbn; tauto) (EEo 1%nat (Z_to_bv 5 1) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memX (spZ regs) _ _ _ _ _ 8 (Z_to_bv 5 8) (-16) regs HRD0 U2e ltac:(cbn; tauto) (EEo 8%nat (Z_to_bv 5 8) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memX (spZ regs) _ _ _ _ _ 9 (Z_to_bv 5 9) (-24) regs HRD0 U2e ltac:(cbn; tauto) (EEo 9%nat (Z_to_bv 5 9) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memX (spZ regs) _ _ _ _ _ 18 (Z_to_bv 5 18) (-32) regs HRD0 U2e ltac:(cbn; tauto) (EEo 18%nat (Z_to_bv 5 18) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memX (spZ regs) _ _ _ _ _ 19 (Z_to_bv 5 19) (-40) regs HRD0 U2e ltac:(cbn; tauto) (EEo 19%nat (Z_to_bv 5 19) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memX (spZ regs) _ _ _ _ _ 20 (Z_to_bv 5 20) (-48) regs HRD0 U2e ltac:(cbn; tauto) (EEo 20%nat (Z_to_bv 5 20) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memX (spZ regs) _ _ _ _ _ 21 (Z_to_bv 5 21) (-56) regs HRD0 U2e ltac:(cbn; tauto) (EEo 21%nat (Z_to_bv 5 21) eq_refl)). }
  assert (HAREPX : arep_at (ablocks B ly S) (rdW W memX) A_G_REC A_REC_SPILL R Q).
  { apply (sar_arep_kept (ablocks B ly S) (ablocks B ly S) (rdW W mem) (rdW W memX) R Q HAREP
      (lay_blocks_in _ _ _ _ _ _ HAREP) KR).
    intros p0 n0 i Hpn Hi. destruct (Hblk p0 n0 i (lay_blocks_in _ _ _ _ _ _ HAREP _ Hpn) Hi) as [Hb1 Hb2].
    exact (KO _ Hb1 Hb2). }
  assert (ES292 : ew E 292 = Z_to_bv 64 A_REC_SPILL).
  { change 292%nat with RB_SPILL.
    rewrite (img_env_atomP E RB_SPILL HEI ltac:(unfold RB_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), (rbt_spill_val VOBJS). reflexivity. }
  pmkst HS.
  prreg HS (1%bv : bv 5) K1. prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4.
  prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
  prreg HS (10%bv : bv 5) K10. prreg HS (11%bv : bv 5) K11. prreg HS (19%bv : bv 5) K19. prreg HS (20%bv : bv 5) K20.
  sar_preg HS (Z_to_bv 5 22) Q22. sar_preg HS (Z_to_bv 5 23) Q23. sar_preg HS (Z_to_bv 5 24) Q24.
  sar_preg HS (Z_to_bv 5 25) Q25. sar_preg HS (Z_to_bv 5 26) Q26. sar_preg HS (Z_to_bv 5 27) Q27.
  apply (sar_call_RCF ly S W regs mem md ch R O Q id pv verb (ms_regs ms) memX _ PRE HJ HEV HLIVE HMOK HRM HFRM Hid).
  + rewrite K2, U2e. unfold w64. f_equal; lia.
  + rewrite K3, (EEo 3%nat 3%bv eq_refl). exact Hgp.
  + rewrite K4, (EEo 4%nat 4%bv eq_refl). exact Htp.
  + intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [-> | Hr']); try (subst r);
    first [rewrite Q22, sar_denot_off0; apply EEo; reflexivity | rewrite Q23, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q24, sar_denot_off0; apply EEo; reflexivity | rewrite Q25, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q26, sar_denot_off0; apply EEo; reflexivity | rewrite Q27, sar_denot_off0; apply EEo; reflexivity].
  + rewrite K9, ES292. reflexivity.
  + rewrite K20, E32. reflexivity.
  + rewrite K8, (EEo 11%nat 11%bv eq_refl). exact R11.
  + rewrite K19, (EEo 10%nat 10%bv eq_refl). exact R10.
  + rewrite K10, ES292. reflexivity.
  + rewrite K11. reflexivity.
  + rewrite K1. reflexivity.
  + exact HFRX.
  + exact Hfull.
  + exact HAREPX.
  + exact HOQ.
  + exact (sar_aro_run (rdW W mem) _ KO HROD).
  + exact HARG.
  + exact (sar_str_run ly S W mem md memX _ pv verb HAR (proj1 HJ) KO HSTRe).
- (* record()'s table arm: the call takes the slot g_rec.calls[ncalls] *)
  assert (Hlt : (length (r_calls R) < 16)%nat) by (unfold n in Hne16; lia).
  destruct (sar_entry_seed ly S W mem md regs E (spZ regs) n c (SOff RB_N 0) 0 15
    HAR HENV ltac:(lia) Hsp16 Hn ltac:(lia) Hc
    ltac:(reflexivity) ltac:(intros a Ha; apply Hpres; rewrite HSTKv; lia) HNC
    ltac:(cbn [sv_denot]; rewrite (proj1 (proj2 (proj2 (proj2 HENV)))), unsigned_lit_small, Z.add_0_r by lia;
          reflexivity)
    HREG) as [HS SHOK].
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan SAR_JOIN.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact U2e | cbn [YP09.r_wlo]; rewrite HSTKv; lia | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := RB_GREC);
      [reflexivity | exact (eq_trans (HEI RB_GREC ltac:(unfold RB_GREC, A_OBJ, A_TEXT, A_LIM; lia)) (rbt_grec_val VOBJS)) | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply sar_awr_rec. unfold in_rec, A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
    apply (awr_ok_nil SEGS B). }
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx ?msx =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) sar_frame_r) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) sar_frame_r) in
    pose proof (st_ok_pi_region_nth E ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRD0;
    pose proof (st_ok_pi_region_nth E ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HRD3;
    cbn [ms_mem restrict mkst] in HRD0, HRD3
  | st_ok _ _ ?ssx ?msx =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) sar_frame_r) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) sar_frame_r) in
    pose proof (st_ok_region_nth (segs := SEGS) E ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HRD0;
    pose proof (st_ok_region_nth (segs := SEGS) E ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HRD3;
    cbn [ms_mem restrict mkst] in HRD0, HRD3
  end.
  lazymatch goal with HFx : frame_of E _ (mrestrict _ mem) (mrestrict _ ?m3) |- _ => rename HFx into HFr; set (memJ := m3) in * end.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) -> ~ (A_G_REC + 8 <= a < A_G_REC + 12) ->
    rdW W memJ a = rdW W mem a).
  { intros a Ha H1 H2.
    apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem memJ
      (fun a => (spZ regs - 64 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr);
    [ | exact Ha | intros [H|H]; [exact (H1 H) | exact (H2 H)] ].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hqq | Hin]; [injection Hqq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2e, ?UG in Hrr;
      first [lia | left; lia | right; lia] |]).
    destruct Hin. }
  assert (KO : forall a, 0 <= a < alloc_ceiling -> ~ in_rec a -> rdW W memJ a = rdW W mem a).
  { intros a Ha Hn0. apply KEEP; [unfold YG0f.ASAN_CEIL in *; lia | rewrite HSTKv in *; unfold YG0f.ASAN_CEIL in *; lia |].
    intros Hin. apply Hn0. left. unfold A_G_REC, REC_SIZE in *. lia. }
  pose proof (field_of_region (segs := SEGS) E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) (n + 1) HRD3 UG ltac:(cbn; tauto)
    ltac:(cbn [sv_denot]; rewrite E33n, unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VNC.
  change (N.to_nat 4) with 4%nat in VNC. apply (aval_mem_view SEGS) in VNC.
  assert (HFRJ : sar_frame (rdW W memJ) (spZ regs) regs).
  { apply sar_frame_of.
    - exact (sar_frame_chunk E (w_H W) memJ (spZ regs) _ _ _ _ _ 1 (Z_to_bv 5 1) (-8) regs HRD0 U2e ltac:(cbn; tauto) (EEo 1%nat (Z_to_bv 5 1) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memJ (spZ regs) _ _ _ _ _ 8 (Z_to_bv 5 8) (-16) regs HRD0 U2e ltac:(cbn; tauto) (EEo 8%nat (Z_to_bv 5 8) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memJ (spZ regs) _ _ _ _ _ 9 (Z_to_bv 5 9) (-24) regs HRD0 U2e ltac:(cbn; tauto) (EEo 9%nat (Z_to_bv 5 9) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memJ (spZ regs) _ _ _ _ _ 18 (Z_to_bv 5 18) (-32) regs HRD0 U2e ltac:(cbn; tauto) (EEo 18%nat (Z_to_bv 5 18) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memJ (spZ regs) _ _ _ _ _ 19 (Z_to_bv 5 19) (-40) regs HRD0 U2e ltac:(cbn; tauto) (EEo 19%nat (Z_to_bv 5 19) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memJ (spZ regs) _ _ _ _ _ 20 (Z_to_bv 5 20) (-48) regs HRD0 U2e ltac:(cbn; tauto) (EEo 20%nat (Z_to_bv 5 20) eq_refl)).
    - exact (sar_frame_chunk E (w_H W) memJ (spZ regs) _ _ _ _ _ 21 (Z_to_bv 5 21) (-56) regs HRD0 U2e ltac:(cbn; tauto) (EEo 21%nat (Z_to_bv 5 21) eq_refl)). }
  assert (Hcv : c = A_G_REC + OFF_CALLS + CALL_SIZE * n).
  { unfold c, sar_entry. rewrite (proj2 (Nat.ltb_lt _ _) Hlt). reflexivity. }
  set (Qn := RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)).
  assert (HQn : forall pn, In pn (lay_blocks Qn) <-> In pn (lay_blocks Q)) by (intros pn; unfold Qn; rewrite sar_lay_snoc; reflexivity).
  assert (HPEND : sar_pending (ablocks B ly S) (rdW W memJ) R Qn c).
  { split.
    - intros pn Hpn. apply HQn in Hpn. exact (lay_blocks_in _ _ _ _ _ _ HAREP pn Hpn).
    - intros rd' VF VN Krec Kblk.
      apply (sar_rep_record_lt (ablocks B ly S) (ablocks B ly S) (rdW W mem) rd' R Q REC_AFTER_REPLY HAREP Hlt).
      + unfold REC_AFTER_REPLY, REC_FN_COUNT. lia.
      + apply (aval_mem_kept (rdW W memJ)); [exact VNC|]. intros k Hk.
        apply Krec; [left; unfold A_G_REC, OFF_NCALLS, REC_SIZE; lia | unfold OFF_NCALLS, A_G_REC in *; lia].
      + exact VF.
      + exact VN.
      + intros a Ha H1 H2. rewrite (Krec a Ha H2). apply KEEP;
        [unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia
        | unfold in_rec, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia | unfold OFF_NCALLS in H1; exact H1].
      + intros pn Hpn. pose proof (lay_blocks_in _ _ _ _ _ _ HAREP pn Hpn) as Hpn'. split; [exact Hpn'|].
        intros i Hi. destruct pn as [p0 n0]. cbn [fst snd] in *.
        rewrite (Kblk p0 n0 i (proj2 (HQn _) Hpn) Hi).
        destruct (Hblk p0 n0 i Hpn' Hi) as [Hb1 Hb2]. exact (KO _ Hb1 Hb2). }
  pmkst HS.
  prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4.
  prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9.
  prreg HS (19%bv : bv 5) K19. prreg HS (20%bv : bv 5) K20.
  sar_preg HS (Z_to_bv 5 22) Q22. sar_preg HS (Z_to_bv 5 23) Q23. sar_preg HS (Z_to_bv 5 24) Q24.
  sar_preg HS (Z_to_bv 5 25) Q25. sar_preg HS (Z_to_bv 5 26) Q26. sar_preg HS (Z_to_bv 5 27) Q27.
  assert (D9 : getr (ms_regs ms) 9 = w64 c).
  { rewrite K9. pose proof (sar_denot_slot E n c EN Hn EG EC Hcv) as D. cbn [sv_denot] in D.
    rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned in D.
    change RB_N with 33%nat in D. change RB_GREC with 285%nat in D. change RB_C with 34%nat in D.
    rewrite <- D. exact EC. }
  apply (sar_seg_B ly S W regs mem md ch R O id pv verb ly S W (ms_regs ms) memJ _ 0 c Qn SAR_JOIN PRE HJ).
  + unfold rec_spill_frees. destruct (Nat.ltb _ _); lia.
  + exact HEV.
  + exact HLIVE.
  + exact HMOK.
  + unfold rec_spill_frees. rewrite (proj2 (Nat.ltb_lt _ _) Hlt). rewrite Z.mul_0_l. exact (mle_start MT S MTL).
  + exact HRM.
  + lia.
  + exact HFRM.
  + exact Hid.
  + rewrite K2, U2e. unfold w64. f_equal; lia.
  + rewrite K3, (EEo 3%nat 3%bv eq_refl). exact Hgp.
  + rewrite K4, (EEo 4%nat 4%bv eq_refl). exact Htp.
  + intros r Hr. assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hr' as [-> | Hr']); try (subst r);
    first [rewrite Q22, sar_denot_off0; apply EEo; reflexivity | rewrite Q23, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q24, sar_denot_off0; apply EEo; reflexivity | rewrite Q25, sar_denot_off0; apply EEo; reflexivity
          | rewrite Q26, sar_denot_off0; apply EEo; reflexivity | rewrite Q27, sar_denot_off0; apply EEo; reflexivity].
  + exact D9.
  + rewrite K20, E32. reflexivity.
  + rewrite K8, (EEo 11%nat 11%bv eq_refl). exact R11.
  + rewrite K19, (EEo 10%nat 10%bv eq_refl). exact R10.
  + left; reflexivity.
  + exact HFRJ.
  + reflexivity.
  + exact Hlen16.
  + exact HPEND.
  + exact (sar_aro_run (rdW W mem) _ KO HROD).
  + exact (sar_str_run ly S W mem md memJ _ pv verb HAR (proj1 HJ) KO HSTRe).
  + intros pn Hpn. left. apply HOQ. apply HQn. exact Hpn.
  + intros pn Hpn _. exact Hpn.
  + intros pn Hpn. destruct (in_dec recb_pair_dec pn O) as [HO | HnO].
    * right. apply HQn. apply HOQ. exact HO.
    * left. split; [exact Hpn | exact HnO].
  + intros pn Hpn Hn0. exfalso. exact (Hn0 Hpn).
Qed.

Theorem tsup_after_reply_holds : tsup_after_reply_spec B MT.
Proof. exact sar_core. Qed.
End h.
End e.
End f.
End d.
