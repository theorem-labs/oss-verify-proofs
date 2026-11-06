(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: one part of sup_connect's walk on fuzz_command.asan-ubsan (image B): the three
   arg_s calls, `scb_seg1 : SCB_2_stmt -> SCB_1_stmt` (BASE + SCB_R1 = 0x8b490: `mv s4,a0; mv a1,s3; jal arg_s`,
   the verb), `scb_seg3 : SCB_4_stmt -> SCB_3_stmt` (BASE + SCB_R3 = 0x8b4a8: `mv a0,s4; mv a1,s1; jal arg_s`,
   port_a) and `scb_seg4 : SCB_T_stmt -> SCB_4_stmt` (BASE + SCB_R4 = 0x8b4b4: `mv a0,s4; mv a1,s0; jal arg_s`,
   port_b). The interface (scb_pre, scb_mid, the stage values, the seeds) is sup_connect_s0.v's.

   Each step re-seeds the symbolic state at the return point (scb_seed), runs the two moves to the call (the frame
   is a read-only region, so the run writes no byte), hands the state over at the call in scb_mid form
   (`scb2_mid_run`), moves the string from the entry to the call state (the verb in astr_argA form,
   `scb2_verb_move`; a port in block form, `scb2_port_move`), and then takes arg_s's contract through the shared
   call-and-rebuild lemma `scb2_call`: cl_callS_pg with arg_s's footprint (the slot's nargs and args[m] fields,
   program statics inside scb_FP), the m = 6 arm of arg_s's post excluded (length A <= 3), and the hand-over of the
   next return point rebuilt from arg_s's post (the recorder holds A ++ [y], the new block is fresh, the frame is
   kept by arg_s's journal, the callee-saved registers by aregs_preserved). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaDenot PaLibG PaCall CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_canonical_c hand_back_c record_c arg_s_c arg_line_c answer_c sup_connect_c RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCallPg CmdRecBase CmdRecRo CmdRecImg sup_connect_s0.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the machine state and the model a symbolic run leaves behind, under fixed names *)
Ltac scb2_name_ms HS nm :=
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into nm
| st_ok _ _ _ (restrict _ ?m) => rename m into nm
end.
Ltac scb2_set_md nm :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (nm := mdx) in *; clearbody nm end.
(* a register the run left untouched: the symbolic state holds atom z, which the seed's environment maps to the
   register z of the return point *)
Ltac scb2_reg_keep HS EE :=
lazymatch goal with |- getr _ (Z_to_bv 5 ?z) = _ =>
  let X := fresh "X" in prreg HS (Z_to_bv 5 z) X; rewrite X; apply EE; reflexivity
end.

Lemma scb2_pdec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Qed.

(* arg_s's footprint, at the slot of the call (rec_slot R) with A the arguments recorded so far *)
Definition scb2_FPa (R : rstate) (A : list (list byte)) : list (Z * Z) :=
if Z.of_nat (length A) <? REC_ARGS_MAX
then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
      (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A), rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length A) + 8)]
else [].

(* the slot lies in g_rec's call table or in record.spill *)
Lemma scb2_slot_rng : forall R,
(A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/ rec_slot R = A_REC_SPILL.
Proof.
intros R. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H]; [left|right; reflexivity].
unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER. lia.
Qed.

(* every byte of arg_s's footprint is a byte of the slot *)
Lemma scb2_fpa_slot : forall R A a, Z.of_nat (length A) < REC_ARGS_MAX ->
inFP (scb2_FPa R A) a -> rec_slot R <= a < rec_slot R + CALL_SIZE.
Proof.
intros R A a HA Ha. unfold scb2_FPa in Ha. rewrite (proj2 (Z.ltb_lt _ _) HA) in Ha. cbv iota in Ha.
apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE, REC_ARGS_MAX in *; lia|].
destruct (inFP_nil a Ha).
Qed.

(* a byte of the walk's footprint is a program static or a byte of one of the recorder's blocks *)
Lemma scb2_fp_cases : forall O x, inFP (scb_FP O) x ->
inFP cmd_PG x \/ exists p n, In (p, n) O /\ p <= x < p + req_size n.
Proof.
intros O x Hin. unfold scb_FP in Hin.
apply inFP_cons in Hin. destruct Hin as [H | Hin].
{ left. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity|].
  cbn [fst snd]. unfold OFF_NCALLS in H. lia. }
apply inFP_cons in Hin. destruct Hin as [H | Hin].
{ left. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity|].
  cbn [fst snd]. unfold OFF_CALLS, OFF_ANSWER in H. lia. }
apply inFP_cons in Hin. destruct Hin as [H | Hin].
{ left. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity|].
  cbn [fst snd]. unfold OFF_STATE in H. lia. }
apply inFP_cons in Hin. destruct Hin as [H | Hin].
{ left. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity|].
  cbn [fst snd]. unfold SC_SIZE in H. lia. }
right. exact (inFP_ablocks_fp_inv O x Hin).
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
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the frame region of a return-point seed is read-only: a run from there writes no byte *)
Lemma scb2_view_eq : forall E P (H : word -> bool) (m m' : word -> option byte) a,
frame_of E (ss_mem (scb_ss_m P)) (mrestrict H m) (mrestrict H m') -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E P H m m' a Hfr. unfold aview, mbyte. rewrite (Hfr (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & Ha). unfold scb_ss_m, scb_regs_m in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
unfold scb_stack_m in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia.
Qed.

(* the frame's six words are kept by any step that keeps the 48 bytes below the entry sp *)
Lemma scb2_frame_move : forall (H H' : word -> bool) (m m' : word -> option byte) sp0 regs0,
(forall a, sp0 - 48 <= a < sp0 -> aview SEGS H' m' a = aview SEGS H m a) ->
scb_frame (mrestrict H m) sp0 regs0 -> scb_frame (mrestrict H' m') sp0 regs0.
Proof.
intros H H' m m' sp0 regs0 HK HF j r Hj.
assert (Hj6 : (j < length scb_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
change (length scb_saved) with 6%nat in Hj6.
pose proof (HF j r Hj) as Hv.
apply val_mem_view. intros k Hk. rewrite HK by lia.
exact (aval_mem_view SEGS H m _ 8 _ Hv k Hk).
Qed.

(* the registers of a return point, from a state whose callee-saved registers other than s4 are that point's *)
Lemma scb2_regs_at_of : forall regs regsc regs1,
scb_regs_at regs regsc ->
(forall z, acallee_saved z -> z <> 20 -> getr regs1 (Z_to_bv 5 z) = getr regsc (Z_to_bv 5 z)) ->
scb_regs_at regs regs1.
Proof.
intros regs regsc regs1 (Rsp & R8 & R9 & R18 & R19 & R3 & R4 & Rhi) HK.
assert (X2 := HK 2 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (X3 := HK 3 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (X4 := HK 4 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (X8 := HK 8 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (X9 := HK 9 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (X18 := HK 18 ltac:(unfold acallee_saved; lia) ltac:(lia)).
assert (X19 := HK 19 ltac:(unfold acallee_saved; lia) ltac:(lia)).
replace (Z_to_bv 5 2) with (2%bv : bv 5) in X2 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 3) with (3%bv : bv 5) in X3 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 4) with (4%bv : bv 5) in X4 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 8) with (8%bv : bv 5) in X8 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 9) with (9%bv : bv 5) in X9 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 18) with (18%bv : bv 5) in X18 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 19) with (19%bv : bv 5) in X19 by (apply bv_eq; reflexivity).
split; [unfold spZ at 1; rewrite X2; exact Rsp|].
split; [rewrite X8; exact R8|]. split; [rewrite X9; exact R9|].
split; [rewrite X18; exact R18|]. split; [rewrite X19; exact R19|].
split; [rewrite X3; exact R3|]. split; [rewrite X4; exact R4|].
intros r Hr. rewrite (HK r ltac:(unfold acallee_saved; lia) ltac:(lia)). exact (Rhi r Hr).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.

(* the slot's bytes: in the walk's footprint, program statics, below alloc_ceiling *)
Lemma scb2_slot : forall O R a, rec_slot R <= a < rec_slot R + CALL_SIZE ->
inFP (scb_FP O) a /\ inFP cmd_PG a /\ Exists (in_zr a) (as_prog_static B) /\ a < alloc_ceiling.
Proof.
intros O R a Ha. pose proof asan_consts as ((C1 & _) & _).
rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
destruct (scb2_slot_rng R) as [Hc | Hc].
- split; [exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8); split;
    [unfold scb_FP; right; left; reflexivity | cbn [fst snd]; lia]|].
  split; [exists (A_G_REC, A_G_REC + 960); split; [unfold cmd_PG; left; reflexivity|];
    cbn [fst snd]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *; lia|].
  split; [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *; lia|].
  unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE in *. lia.
- rewrite Hc in Ha.
  split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split;
    [unfold scb_FP; right; right; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE, CALL_SIZE in *; lia]|].
  split; [exists (A_REC_SPILL, A_REC_SPILL + 56); split; [unfold cmd_PG; right; left; reflexivity|];
    cbn [fst snd]; unfold CALL_SIZE in *; lia|].
  split; [apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE in *; lia|].
  unfold A_REC_SPILL, CALL_SIZE in *. lia.
Qed.

(* a block the walk's footprint does not name keeps its bytes across a journal of the walk *)
Lemma scb2_blk_keep : forall O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k STK sp0 q m a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (scb_FP O) ly S W mem md own ly' S' W' mem' md' k ->
In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S') -> q <= a < q + m ->
rdW W' mem' a = rdW W mem a.
Proof.
intros O ly S W mem md own ly' S' W' mem' md' k STK sp0 q m a HAR HOin HJ Hq Hno Hq' Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hq) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
replace a with (q + (a - q)) by lia. apply (F2 q m (a - q)); [exact Hq | exact Hq' | lia |].
replace (q + (a - q)) with a by lia. intros Hin.
assert (Hblk : exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) by (exists q, m; split; [exact Hq | lia]).
assert (Hni : ~ in_img SEGS a) by exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl Hblk))).
destruct (scb2_fp_cases O a Hin) as [Hpg | (p & n & Hpn & Hpa)].
- exact (Hni (cif_prog_img _ _ IMG a Hpg)).
- assert (Ne : (q, m) <> (p, n)) by (intros Heq; rewrite Heq in Hno; exact (Hno Hpn)).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR Hq (HOin _ Hpn) Ne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* the read-only bytes are kept along a journal of the walk *)
Lemma scb2_arod : forall O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k STK sp0,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (scb_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros O ly S W mem md own ly' S' W' mem' md' k STK sp0 HAR HOin HJ HR.
apply (@arodata_ok_journalP rc SK SEGS RLO RHI (relro_img SEGS B LAWS HB IMG) (ROB SEGS B LAWS HB IMG)
  B STK sp0 (scb_FP O) ly S W mem md own ly' S' W' mem' md' k HJ); [|exact HR].
intros a Hro Hin. destruct (scb2_fp_cases O a Hin) as [Hpg | (p & n & Hpn & Hpa)].
- exact (RPG SEGS B LAWS HB IMG a Hpg Hro).
- assert (Hblk : exists p0 n0, In (p0, n0) (ablocks B ly S) /\ p0 <= a < p0 + req_size n0)
  by (exists p, n; split; [exact (HOin _ Hpn) | exact Hpa]).
  apply (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl Hblk))).
  destruct Hro as [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr]|].
  exact (relro_img SEGS B LAWS HB IMG a Hrel).
Qed.

(* the verb, in the statement's astr_argA form, at a later state of the walk (arg_s takes [] as the exclusion
   list), with the word tail arg_s's strlen reads *)
Lemma scb2_verb_move : forall ly S (W : world SEGS) mem ly' S' (W' : world SEGS) mem' md' O p v,
AR SEGS B ly' S' W' mem' md' ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p v ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem') ->
(forall q m a, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> q <= a < q + m -> rdW W' mem' a = rdW W mem a) ->
(forall q m, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S')) ->
astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) [] p v /\
(forall x, v = Some x -> atail_vis SEGS W' mem' (p + Z.of_nat (length x))).
Proof.
intros ly S W mem ly' S' W' mem' md' O p v HAR' HA HROD HROD' K KB.
assert (HA' : astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) [] p v).
{ destruct v as [x|]; cbn [astr_argA] in HA |- *; [|exact HA].
  cbv zeta in HA |- *. destruct HA as (Hp & Hs & Hlen & [(Hbl & Hap) | (Hro & Hc1 & Hc2 & He)]).
  - destruct Hbl as (q & m & Hq & Hq1 & Hq2).
    assert (Hno : ~ In (q, m) O).
    { intros Hin. pose proof (proj1 (Forall_forall _ _) Hap _ Hin) as Hd.
      unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
    split; [exact Hp|].
    split; [apply (astr_atR_kept_r (rdW W mem)); [intros a Ha; apply (K q m); [exact Hq | exact Hno | lia] | exact Hs]|].
    split; [exact Hlen|].
    left. split; [exists q, m; split; [exact (KB q m Hq Hno) | lia] | constructor].
  - split; [exact Hp|].
    split; [apply (astr_atR_kept_r (rdW W mem)); [|exact Hs]|].
    { intros a Ha. destruct (Hro (a - p) ltac:(lia)) as (Hr & Ho & Hee).
      replace a with (p + (a - p)) by lia. rewrite (HROD' _ Hr Ho Hee), (HROD _ Hr Ho Hee). reflexivity. }
    split; [exact Hlen|].
    right. split; [exact Hro | split; [exact Hc1 | split; [exact Hc2 | exact He]]]. }
split; [exact HA'|].
intros x ->. exact (cmd_str_tail SEGS B LAWS HB IMG ly' S' W' mem' md' p x HAR' HA').
Qed.

(* a port (block form) at a later state of the walk, in astr_argA form with [] and its word tail *)
Lemma scb2_port_move : forall ly S (W : world SEGS) mem ly' S' (W' : world SEGS) mem' md' O p x,
AR SEGS B ly' S' W' mem' md' ->
scb_blkarg B ly S (rdW W mem) O p x ->
(forall q m a, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> q <= a < q + m -> rdW W' mem' a = rdW W mem a) ->
(forall q m, In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S')) ->
astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) [] p (Some x) /\
(forall x', Some x = Some x' -> atail_vis SEGS W' mem' (p + Z.of_nat (length x'))).
Proof.
intros ly S W mem ly' S' W' mem' md' O p x HAR' (Hbl & Hap & Hs & Hlen) K KB.
destruct Hbl as (q & m & Hq & Hq1 & Hq2).
assert (Hno : ~ In (q, m) O).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) Hap _ Hin) as Hd.
  unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
assert (HA' : astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) [] p (Some x)).
{ apply (scb_argA_of_blkarg B LAWS ly' S' W' mem' md' (rdW W' mem') [] [] p x HAR'); [|constructor].
  split; [exists q, m; split; [exact (KB q m Hq Hno) | lia]|].
  split; [constructor|].
  split; [|exact Hlen].
  apply (astr_atR_kept_r (rdW W mem)); [intros a Ha; apply (K q m); [exact Hq | exact Hno | lia] | exact Hs]. }
split; [exact HA'|].
intros x' Hx. injection Hx as Hx. subst x'. exact (cmd_str_tail SEGS B LAWS HB IMG ly' S' W' mem' md' p x HAR' HA').
Qed.

(* the hand-over at a return point, carried to the state of the call after a run that wrote no byte *)
Lemma scb2_mid_run : forall ly S W regs mem md R O A EVd XMd LVd lyc Sc (Wc : world SEGS) regsc memc mdc kc Oc
  regs1 mem1 md1,
scb_mid B MT ly S W regs mem md R O A EVd XMd LVd lyc Sc Wc regsc memc mdc kc Oc ->
ajournal SEGS B SUP_CONNECT_STK (spZ regs) (scb_FP O) ly S W mem md [] lyc Sc Wc mem1 md1 kc ->
(forall a, aview SEGS (w_H Wc) mem1 a = aview SEGS (w_H Wc) memc a) ->
scb_regs_at regs regs1 ->
scb_mid B MT ly S W regs mem md R O A EVd XMd LVd lyc Sc Wc regs1 mem1 md1 kc Oc.
Proof.
intros ly S W regs mem md R O A EVd XMd LVd lyc Sc Wc regsc memc mdc kc Oc regs1 mem1 md1
  (HJc & Hk & HRA & HFR & HREC & HB1 & HB2 & HB3 & Hfr & Hbb & MLE) HJ1 HV HRA1.
split; [exact HJ1|]. split; [exact Hk|]. split; [exact HRA1|].
split; [apply (scb2_frame_move (w_H Wc) (w_H Wc) memc mem1 (spZ regs) regs); [intros a _; apply HV | exact HFR]|].
split.
{ apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc (rdW Wc mem1) _ Oc HREC).
  - intros pn Hpn. exact (scb_rep_live B _ _ _ _ _ pn HREC Hpn).
  - intros a _. apply HV. }
exact (conj HB1 (conj HB2 (conj HB3 (conj Hfr (conj Hbb MLE))))).
Qed.

(* the budgets' terms are nonnegative *)
Lemma scb2_nn : forall v line t,
0 <= LIVE_ARG_S v /\ 0 <= LIVE_ARG_LINE line /\ 0 <= LIVE_ANSWER t /\
0 <= XM_ARG_S MT v /\ 0 <= XM_ARG_LINE MT line /\ 0 <= XM_ANSWER MT t.
Proof.
intros v line t.
unfold LIVE_ARG_S, LIVE_ARG_LINE, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_REC_CANONICAL, LIVE_XMALLOC,
  XM_ARG_S, XM_ARG_LINE, XM_ANSWER, XM_HAND_BACK, XM_REC_CANONICAL, XM_XMALLOC.
unfold LIVE_XMALLOC.
pose proof (mo_free_nonneg MT MTL) as M0.
pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length (sarg v)) + 1) 1) ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length line) + 1) 1) ltac:(lia)) as M2.
pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)) as M3.
lia.
Qed.

(* arg_s's post at the call state, the K of cl_callS_pg *)
Definition scb2_K (lyc : alayout) (Sc : astate) (R : rstate) (A : list (list byte)) (v : option (list byte))
  (Oc : list (Z * Z)) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 blocks_bytes S' <= blocks_bytes Sc + LIVE_ARG_S v /\
 mo_le MT Sc S' (XM_ARG_S MT v) /\
 ((Z.of_nat (length A) = REC_ARGS_MAX /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\
   rec_repA B ly' S' (rdW W' mem') (rec_record R REC_CONNECT A) Oc) \/
  (Z.of_nat (length A) < REC_ARGS_MAX /\ exists p,
    let n := Z.of_nat (length (sarg v)) + 1 in
    4096 <= p < 2 ^ 64 /\
    Permutation (ablocks B ly' S') ((p, n) :: ablocks B lyc Sc) /\
    Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B lyc Sc) /\
    rec_repA B ly' S' (rdW W' mem') (rec_record R REC_CONNECT (A ++ [sarg v])) ((p, n) :: Oc))).

(* the call of arg_s(c, s) at a state handed over in scb_mid form, and the hand-over at the next return point
   BASE + Rn: the part the three steps share *)
Lemma scb2_call : forall (Rn : Z) (A : list (list byte)) (EVd XMd LVd : Z) (v : option (list byte)) (s : Z)
  ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t lyc Sc (Wc : world SEGS) regs1 mem1 md1 kc Oc
  (Q : world SEGS -> config -> Prop),
scb_pre B MT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t ->
scb_mid B MT ly S W regs mem md R O A EVd XMd LVd lyc Sc Wc regs1 mem1 md1 kc Oc ->
Z.of_nat (length A) < REC_ARGS_MAX ->
getr regs1 10 = w64 (rec_slot R) -> getr regs1 11 = w64 s -> getr regs1 20 = w64 (rec_slot R) ->
getr regs1 1 = Z_to_bv 64 (BASE + Rn) -> 0 <= Rn < 2 ^ 40 -> Rn mod 2 = 0 ->
astr_argA B lyc Sc (rdW Wc mem1) (in_roP SEGS RLO RHI) [] s v ->
(forall x, v = Some x -> atail_vis SEGS Wc mem1 (s + Z.of_nat (length x))) ->
EVd + EV_ARG_S <= EV_SUP_CONNECT R ->
LVd + LIVE_ARG_S v <= LIVE_SUP_CONNECT verb line (Some port_a) (Some port_b) t ->
XMd + XM_ARG_S MT v <= XM_SUP_CONNECT MT R verb line (Some port_a) (Some port_b) t ->
(forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k2 O2,
  scb_mid B MT ly S W regs mem md R O (A ++ [sarg v]) (EVd + EV_ARG_S) (XMd + XM_ARG_S MT v) (LVd + LIVE_ARG_S v)
    ly2 S2 W2 regs2 mem2 md2 k2 O2 ->
  getr regs2 20 = w64 (rec_slot R) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + Rn)) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_arg_s)) mem1 (seg_rom SEGS)) md1) Q.
Proof.
intros Rn A EVd XMd LVd v s ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t lyc Sc Wc regs1 mem1
  md1 kc Oc Q HPRE HMID HAl H10 H11 H20 Hra HRn HRn2 HSA HST HEVb HLVb HXMb K.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof scb_stk as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct HPRE as (HPRE0 & _ & _ & HROD & _ & _ & _ & _ & _ & _ & _ & H13 & Hpb64 & _ & _ & _ & _ & HSB & HREP &
  Hev & Hlive & HMOK).
destruct HPRE0 as (HAR & _ & _ & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HMID as (HJ1 & Hk & HRA & HFR & HREC & HB1 & HB2 & HB3 & HfrS & Hbbc & MLEc).
pose proof HRA as (Rsp & R8 & R9 & R18 & R19 & R3 & R4 & Rhi).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S))
by (intros pn Hpn; exact (scb_rep_live B ly S _ R O pn HREP Hpn)).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & Hnev1 & _).
(* s0 holds pb, a pointer into a heap block, so arg_s's frame chain is the empty one *)
assert (Hpb : pb < alloc_ceiling).
{ destruct HSB as ((q & m & Hq & Hq1 & Hq2) & _ & _ & _).
  destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hq) as (_ & _ & Hc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia. }
assert (Hs01 : s0Z regs1 < alloc_ceiling).
{ unfold s0Z. rewrite R8, H13. unfold w64. rewrite unsigned_lit_small by lia. exact Hpb. }
assert (Hsp1 : spZ regs1 = spZ regs + -48) by lia.
pose proof (scb2_arod O ly S W mem md [] lyc Sc Wc mem1 md1 kc SUP_CONNECT_STK (spZ regs) HAR HOin HJ1 HROD) as HROD1.
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc mem1 md1 HAR1 HROD1) as HRO1.
assert (HnevA : st_nev Sc + EV_ARG_S <= EV_MAX) by lia.
assert (HLIVEA : blocks_bytes Sc + LIVE_ARG_S v <= LIVE_MAX) by lia.
pose proof (scb2_nn v line t) as (_ & _ & _ & HXA0 & _ & _).
pose proof (mok_station MT S Sc _ XMd (XM_ARG_S MT v) MTL HMOK MLEc HXA0 HXMb) as HMOKA.
eapply SRr_bind.
{ eapply (cl_callS_pg B LAWS Wc regs1 mem1 (Z_to_bv 64 (BASE + AF_arg_s)) SUP_CONNECT_STK (spZ regs) (scb_FP O)
    ly S W mem md [] lyc Sc md1 kc ARG_S_STK (scb2_FPa R A) EV_ARG_S (-48) (Z_to_bv 64 (BASE + Rn)) []
    (scb2_K lyc Sc R A v Oc) HJ1 Hsp1).
  - reflexivity.
  - lia.
  - exact K6.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact Hra.
  - apply ret_ok_codeptr_v; [exact HRn | exact HRn2].
  - rewrite unsigned_lit_small by lia. lia.
  - exact (achain_low _ _ _ _ Hs01).
  - intros HPREc. eapply SRr_mono.
    { exact (TARG_S fx lyc Sc Wc regs1 mem1 md1 [] (rec_slot R) s REC_CONNECT A v R Oc HPREc HROD1 HRO1
        H10 H11 eq_refl HREC (or_introl HSA) HST HnevA HLIVEA HMOKA). }
    cbv beta. unfold apost_base. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2).
    exists ly2, S2, regs2, mem2, md2. split; [rewrite Hra; reflexivity|].
    split; [exact HJ2|]. split; [exact HP2 | exact HQ2].
  - intros a Ha. left.
    destruct (scb2_slot O R a (scb2_fpa_slot R A a HAl Ha)) as (H1 & H2 & H3 & _).
    split; [exact H1|]. right. split; [exact H3 | exact (cif_prog_img _ _ IMG a H2)]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & HK2).
unfold scb2_K in HK2.
destruct HK2 as (Hbb2 & Hmle2 & [(H6 & _) | (_ & p & Hp & Hperm & Hfresh & HREP2)]); [lia|].
apply (K ly2 S2 W2 regs2 mem2 md2 (kc + EV_ARG_S) ((p, Z.of_nat (length (sarg v)) + 1) :: Oc)).
2: { assert (X := HP2 20 ltac:(unfold acallee_saved; lia)).
     replace (Z_to_bv 5 20) with (20%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact H20. }
split; [exact HJ2|].
split; [lia|].
split; [exact (scb2_regs_at_of regs regs1 regs2 HRA (fun z Hz _ => HP2 z Hz))|].
split.
{ apply (scb2_frame_move (w_H Wc) (w_H W2) mem1 mem2 (spZ regs) regs); [|exact HFR].
  intros a Ha. pose proof HJ2c as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  apply F1; [lia | lia |].
  intros Hin. destruct (scb2_slot O R a (scb2_fpa_slot R A a HAl Hin)) as (_ & _ & _ & Hlo). lia. }
split; [exact HREP2|].
split.
{ intros pn [<- | Hpn] Hin; [|exact (HB1 pn Hpn Hin)].
  destruct (in_dec scb2_pdec (p, Z.of_nat (length (sarg v)) + 1) O) as [HO | HO]; [exact HO|exfalso].
  pose proof (proj1 (Forall_forall _ _) Hfresh _ (HB3 _ Hin HO)) as Hd.
  unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
split.
{ intros pn Hpn. apply (Permutation_in _ Hperm) in Hpn. destruct Hpn as [<- | Hpn]; [right; left; reflexivity|].
  destruct (HB2 pn Hpn) as [H | H]; [left; exact H | right; right; exact H]. }
split.
{ intros pn Hpn Hno. apply (Permutation_in _ (Permutation_sym Hperm)). right. exact (HB3 pn Hpn Hno). }
split.
{ pose proof HJ2c as (_ & _ & _ & _ & _ & Hfr2 & _). rewrite Hfr2. exact HfrS. }
split; [lia|].
exact (mle_station MT S Sc S2 XMd (XM_ARG_S MT v) MTL MLEc Hmle2).
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* The three steps                                                                                    *)

(* BASE + SCB_R1 -> BASE + SCB_R2: s4 := the slot (a0), a1 := s3 = the verb, the call arg_s(c, verb) *)
Lemma scb_seg1 : SCB_2_stmt B MT -> SCB_1_stmt B MT.
Proof.
intros K2 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc t
  HPRE HMID H10c.
pose proof HPRE as (HPRE0 & _ & _ & HROD & _ & H10 & _ & _ & _ & _ & _ & _ & _ & HSV & _ & _ & _ & _ & HREP & _).
pose proof HPRE0 as (HAR & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof HMID as (HJc & _ & HRA & HFR & _ & _ & _ & HB3 & _).
pose proof HRA as (Rsp & R8 & R9 & R18 & R19 & R3 & R4 & Rhi).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S))
by (intros pn Hpn; exact (scb_rep_live B ly S _ R O pn HREP Hpn)).
destruct (scb_seed B SCB_R1 ly regs regsc lyc Sc Wc memc mdc Hstk (proj1 HJc) Rsp HFR) as (HS & SHOK).
set (E := Eimg (Ereg regsc (scb_extra_m regs))) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clearbody E.
(* 0x8b490 .. 0x8b498: s4 := a0, a1 := s3, the call of arg_s *)
paj_run_tok RUN HS HJc SHOK scb_Bspan.
{ awr_ok_tac. }
scb2_set_md mdv. scb2_name_ms HS ms1.
pose proof (fun a => scb2_view_eq E SCB_R1 (w_H Wc) memc (ms_mem ms1) a HFr) as HV.
clear HF HFr HG.
pmkst HS. rewrite (scb_sig_arg_s SIGP).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (20%bv : bv 5) P20.
assert (HRA1 : scb_regs_at regs (ms_regs ms1)).
{ apply (scb2_regs_at_of regs regsc _ HRA). intros z Hz Hz20. unfold acallee_saved in Hz.
  assert (Hc : z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 21 \/ z = 22 \/ z = 23 \/
    z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by lia.
  repeat (destruct Hc as [-> | Hc]; [scb2_reg_keep HS EE|]). subst z. scb2_reg_keep HS EE. }
pose proof (scb2_mid_run ly S W regs mem md R O [] _ _ _ lyc Sc Wc regsc memc mdc kc Oc (ms_regs ms1) (ms_mem ms1) mdv
  HMID HJc HV HRA1) as HMID1.
pose proof (scb2_arod O ly S W mem md [] lyc Sc Wc (ms_mem ms1) mdv kc SUP_CONNECT_STK (spZ regs) HAR HOin HJc HROD)
  as HROD1.
destruct (scb2_verb_move ly S W mem lyc Sc Wc (ms_mem ms1) mdv O pv verb (proj1 HJc) HSV HROD HROD1
  (fun q m a Hq Hno Ha => scb2_blk_keep O ly S W mem md [] lyc Sc Wc (ms_mem ms1) mdv kc SUP_CONNECT_STK (spZ regs)
     q m a HAR HOin HJc Hq Hno (HB3 _ Hq Hno) Ha)
  (fun q m Hq Hno => HB3 _ Hq Hno)) as (HSA & HST).
pose proof (scb2_nn (Some port_a) line t) as (N1 & N2 & N3 & N4 & N5 & N6).
pose proof (scb2_nn (Some port_b) line t) as (N7 & _ & _ & N8 & _ & _).
apply (scb2_call SCB_R2 [] (SCB_EV1 R) (SCB_XM1 MT R) SCB_LV1 verb pv ly S W regs mem md ch pv pl pa pb verb line
  port_a port_b R O t lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv kc Oc _ HPRE HMID1).
- unfold REC_ARGS_MAX. cbn [length]. lia.
- rewrite P10, (EE 10%nat 10%bv eq_refl). exact H10c.
- rewrite P11, (EE 19%nat 19%bv eq_refl), R19. exact H10.
- rewrite P20, (EE 10%nat 10%bv eq_refl). exact H10c.
- exact P1.
- unfold SCB_R2. lia.
- reflexivity.
- exact HSA.
- exact HST.
- unfold SCB_EV1, EV_SUP_CONNECT, EV_ARG_S, EV_ARG_LINE, EV_ANSWER, EV_HAND_BACK, EV_REC_CANONICAL, EV_XMALLOC. lia.
- unfold SCB_LV1, LIVE_SUP_CONNECT. lia.
- unfold SCB_XM1, XM_SUP_CONNECT. lia.
- intros ly2 S2 W2 regs2 mem2 md2 k2 O2 HMID2 H202.
  exact (K2 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O ly2 S2 W2 regs2 mem2 md2 k2 O2
    HPRE HMID2 H202).
Qed.

(* BASE + SCB_R3 -> BASE + SCB_R4: a0 := s4 (the slot), a1 := s1 = port_a, the call arg_s(c, port_a) *)
Lemma scb_seg3 : SCB_4_stmt B MT -> SCB_3_stmt B MT.
Proof.
intros K4 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc t
  HPRE HMID H20c.
pose proof HPRE as (HPRE0 & _ & _ & HROD & _ & _ & _ & _ & _ & H12 & _ & _ & _ & _ & _ & _ & HSA0 & _ & HREP & _).
pose proof HPRE0 as (HAR & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof HMID as (HJc & _ & HRA & HFR & _ & _ & _ & HB3 & _).
pose proof HRA as (Rsp & R8 & R9 & R18 & R19 & R3 & R4 & Rhi).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S))
by (intros pn Hpn; exact (scb_rep_live B ly S _ R O pn HREP Hpn)).
destruct (scb_seed B SCB_R3 ly regs regsc lyc Sc Wc memc mdc Hstk (proj1 HJc) Rsp HFR) as (HS & SHOK).
set (E := Eimg (Ereg regsc (scb_extra_m regs))) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clearbody E.
(* 0x8b4a8 .. 0x8b4b0: a0 := s4, a1 := s1, the call of arg_s *)
paj_run_tok RUN HS HJc SHOK scb_Bspan.
{ awr_ok_tac. }
scb2_set_md mdv. scb2_name_ms HS ms1.
pose proof (fun a => scb2_view_eq E SCB_R3 (w_H Wc) memc (ms_mem ms1) a HFr) as HV.
clear HF HFr HG.
pmkst HS. rewrite (scb_sig_arg_s SIGP).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (20%bv : bv 5) P20.
assert (HRA1 : scb_regs_at regs (ms_regs ms1)).
{ apply (scb2_regs_at_of regs regsc _ HRA). intros z Hz Hz20. unfold acallee_saved in Hz.
  assert (Hc : z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 21 \/ z = 22 \/ z = 23 \/
    z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by lia.
  repeat (destruct Hc as [-> | Hc]; [scb2_reg_keep HS EE|]). subst z. scb2_reg_keep HS EE. }
pose proof (scb2_mid_run ly S W regs mem md R O _ _ _ _ lyc Sc Wc regsc memc mdc kc Oc (ms_regs ms1) (ms_mem ms1) mdv
  HMID HJc HV HRA1) as HMID1.
destruct (scb2_port_move ly S W mem lyc Sc Wc (ms_mem ms1) mdv O pa port_a (proj1 HJc) HSA0
  (fun q m a Hq Hno Ha => scb2_blk_keep O ly S W mem md [] lyc Sc Wc (ms_mem ms1) mdv kc SUP_CONNECT_STK (spZ regs)
     q m a HAR HOin HJc Hq Hno (HB3 _ Hq Hno) Ha)
  (fun q m Hq Hno => HB3 _ Hq Hno)) as (HSA & HST).
pose proof (scb2_nn (Some port_b) line t) as (N1 & N2 & N3 & N4 & N5 & N6).
apply (scb2_call SCB_R4 (scb_A3 verb line) (SCB_EV3 R) (SCB_XM3 MT R verb line) (SCB_LV3 verb line) (Some port_a) pa
  ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv kc Oc _
  HPRE HMID1).
- unfold scb_A3, REC_ARGS_MAX. cbn [length]. lia.
- rewrite P10, (EE 20%nat 20%bv eq_refl). exact H20c.
- rewrite P11, (EE 9%nat 9%bv eq_refl), R9. exact H12.
- rewrite P20, (EE 20%nat 20%bv eq_refl). exact H20c.
- exact P1.
- unfold SCB_R4. lia.
- reflexivity.
- exact HSA.
- exact HST.
- unfold SCB_EV3, SCB_EV2, SCB_EV1, EV_SUP_CONNECT, EV_ARG_S, EV_ARG_LINE, EV_ANSWER, EV_HAND_BACK,
    EV_REC_CANONICAL, EV_XMALLOC. lia.
- unfold SCB_LV3, SCB_LV2, SCB_LV1, LIVE_SUP_CONNECT. lia.
- unfold SCB_XM3, SCB_XM2, SCB_XM1, XM_SUP_CONNECT. lia.
- intros ly2 S2 W2 regs2 mem2 md2 k2 O2 HMID2 H202.
  exact (K4 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O ly2 S2 W2 regs2 mem2 md2 k2 O2
    HPRE HMID2 H202).
Qed.

(* BASE + SCB_R4 -> BASE + SCB_R5: a0 := s4 (the slot), a1 := s0 = port_b, the call arg_s(c, port_b) *)
Lemma scb_seg4 : SCB_T_stmt B MT -> SCB_4_stmt B MT.
Proof.
intros KT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc kc Oc t
  HPRE HMID H20c.
pose proof HPRE as (HPRE0 & _ & _ & HROD & _ & _ & _ & _ & _ & _ & _ & H13 & _ & _ & _ & _ & _ & HSB0 & HREP & _).
pose proof HPRE0 as (HAR & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof HMID as (HJc & _ & HRA & HFR & _ & _ & _ & HB3 & _).
pose proof HRA as (Rsp & R8 & R9 & R18 & R19 & R3 & R4 & Rhi).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S))
by (intros pn Hpn; exact (scb_rep_live B ly S _ R O pn HREP Hpn)).
destruct (scb_seed B SCB_R4 ly regs regsc lyc Sc Wc memc mdc Hstk (proj1 HJc) Rsp HFR) as (HS & SHOK).
set (E := Eimg (Ereg regsc (scb_extra_m regs))) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clearbody E.
(* 0x8b4b4 .. 0x8b4bc: a0 := s4, a1 := s0, the call of arg_s *)
paj_run_tok RUN HS HJc SHOK scb_Bspan.
{ awr_ok_tac. }
scb2_set_md mdv. scb2_name_ms HS ms1.
pose proof (fun a => scb2_view_eq E SCB_R4 (w_H Wc) memc (ms_mem ms1) a HFr) as HV.
clear HF HFr HG.
pmkst HS. rewrite (scb_sig_arg_s SIGP).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (20%bv : bv 5) P20.
assert (HRA1 : scb_regs_at regs (ms_regs ms1)).
{ apply (scb2_regs_at_of regs regsc _ HRA). intros z Hz Hz20. unfold acallee_saved in Hz.
  assert (Hc : z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 19 \/ z = 21 \/ z = 22 \/ z = 23 \/
    z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by lia.
  repeat (destruct Hc as [-> | Hc]; [scb2_reg_keep HS EE|]). subst z. scb2_reg_keep HS EE. }
pose proof (scb2_mid_run ly S W regs mem md R O _ _ _ _ lyc Sc Wc regsc memc mdc kc Oc (ms_regs ms1) (ms_mem ms1) mdv
  HMID HJc HV HRA1) as HMID1.
destruct (scb2_port_move ly S W mem lyc Sc Wc (ms_mem ms1) mdv O pb port_b (proj1 HJc) HSB0
  (fun q m a Hq Hno Ha => scb2_blk_keep O ly S W mem md [] lyc Sc Wc (ms_mem ms1) mdv kc SUP_CONNECT_STK (spZ regs)
     q m a HAR HOin HJc Hq Hno (HB3 _ Hq Hno) Ha)
  (fun q m Hq Hno => HB3 _ Hq Hno)) as (HSA & HST).
pose proof (scb2_nn (Some port_b) line t) as (N1 & N2 & N3 & N4 & N5 & N6).
apply (scb2_call SCB_R5 (scb_A4 verb line port_a) (SCB_EV4 R) (SCB_XM4 MT R verb line port_a)
  (SCB_LV4 verb line port_a) (Some port_b) pb
  ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O t lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv kc Oc _
  HPRE HMID1).
- unfold scb_A4, REC_ARGS_MAX. cbn [length]. lia.
- rewrite P10, (EE 20%nat 20%bv eq_refl). exact H20c.
- rewrite P11, (EE 8%nat 8%bv eq_refl), R8. exact H13.
- rewrite P20, (EE 20%nat 20%bv eq_refl). exact H20c.
- exact P1.
- unfold SCB_R5. lia.
- reflexivity.
- exact HSA.
- exact HST.
- unfold SCB_EV4, SCB_EV3, SCB_EV2, SCB_EV1, EV_SUP_CONNECT, EV_ARG_S, EV_ARG_LINE, EV_ANSWER, EV_HAND_BACK,
    EV_REC_CANONICAL, EV_XMALLOC. lia.
- unfold SCB_LV4, SCB_LV3, SCB_LV2, SCB_LV1, LIVE_SUP_CONNECT. lia.
- unfold SCB_XM4, SCB_XM3, SCB_XM2, SCB_XM1, XM_SUP_CONNECT. lia.
- intros ly2 S2 W2 regs2 mem2 md2 k2 O2 HMID2 H202.
  exact (KT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O ly2 S2 W2 regs2 mem2 md2 k2 O2
    HPRE HMID2 H202).
Qed.
End e.
End f.
End d.
