(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the body of sup_call's ASan walk (plugin-hostd/fuzz_command, 0x8a95c): from
   the join 0x8a9d0, where record() has picked the call slot c (sup_call_s3.v sc_mid), to answer's entry after the
   epilogue and `j answer` (0x8aa40), where the tail's SC_T_stmt gives sup_call's post.

   0x8a9d0 .. 0x8a9fc: the two inline checks of the slot (both removed by the join's shadow entry mkSHE 9 0 56)
   and the stores c->fn := REC_CALL and c->nargs := 0; 0x8aa00 .. 0x8aa08: arg_i(c, id); 0x8aa0c .. 0x8aa14:
   arg_line(c, line); 0x8aa18 .. 0x8aa3c: the shape "resp 0" (0x21ce0), changes = 1, a0 := c, the five saved
   registers reloaded and sp += 48; 0x8aa40: `j answer`.

   The two calls go through the kit's cl_callS_wide (PaNoChain.v): their footprints are the slot's nargs and
   args[m] fields, which are bytes of the program's writable statics inside sup_call's own footprint SC_FP O, so
   they pass awr_byte's program-static case; no footprint byte lies in sup_call's stack window, so the rule's
   VIS premise is vacuous. The recorder step at the end is sup_call_s2.v's sc_rep_slot (table arm) or
   sc_rep_spill (spill arm), whose premises about the bytes since the ENTRY state are the join's (sc_mid's arm
   facts) composed with what this walk keeps.

   Pass-4/5 re-fit: the callee contracts hold at every FP state (forall fx0). arg_i
   reaches the snprintf wrapper (post apost_baseF), so it goes through PaFx.v's cl_callS_wideF with the entry's
   rounding-mode-0 premise and returns at some fx1 with fxrel fx fx1; the walk goes on in place at fx1
   as follows: the symbolic state after the call is moved to fx1 by YL05.v's st_ok_xfx
   (st_ok reads the FP state only in the f registers and fcsr, which mkst fills from the FP state it is given),
   the run lemma is bound again at fx1 (paj_run (fx := fx1)), arg_line (post apost_base) is called at fx1, and
   the tail's statement is applied at fx1, its apost_baseF lifted to the entry's fx by srr_apost_baseF_lift.
   Statement pass 5 removed astack_pres: the walk no longer derives it for the two calls; their frame chains are
   the empty one (s0 holds the line, a heap pointer below alloc_ceiling: achain_low). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibH PaCall CmdBase CmdRep CmdObj CmdZsh CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
xstrdup_c rec_canonical_c hand_back_c rec_calls_free_c arg_i_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_call_s0 sup_call_s1 sup_call_s2 sup_call_s3 PaNoChain PaArt PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YL05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecCells CmdRecRo.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the stack the walk and its two callees need *)
Lemma sc_b_stk48 : 48 <= SUP_CALL_STK.
Proof. vm_compute. intros Hx. discriminate Hx. Qed.
Lemma sc_b_stk_i : 0 <= ARG_I_STK /\ ARG_I_STK + 48 <= SUP_CALL_STK.
Proof. split; vm_compute; intros Hx; discriminate Hx. Qed.
Lemma sc_b_stk_line : 0 <= ARG_LINE_STK /\ ARG_LINE_STK + 48 <= SUP_CALL_STK.
Proof. split; vm_compute; intros Hx; discriminate Hx. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* every byte of sup_call's footprint is a byte of the program's statics or of one of the recorder's blocks *)
Lemma sc_b_fp_cases : forall O a, inFP (SC_FP O) a -> inFP cmd_PG a \/ inFP (ablocks_fp O) a.
Proof.
intros O a (r & Hr & Ha). unfold SC_FP in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha;
  [left | left | left | left | right; exists r; split; [exact Hr | exact Ha]].
all: unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, SC_SIZE in *.
all: first [exists (6174528, 6174528 + 960); split; [left; reflexivity | cbn [fst snd]; lia]
           | exists (6175712, 6175712 + 56); split; [right; left; reflexivity | cbn [fst snd]; lia]].
Qed.

Lemma sc_b_pg_range : forall a, inFP cmd_PG a -> A_G_REC <= a < A_G_QUITTING + 4.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in *; lia.
Qed.

Lemma sc_b_pg_closed : forall FP1, (forall b, inFP FP1 b -> inFP cmd_PG b) -> ~ YI16.sink_open_fp FP1.
Proof.
intros FP1 HF (r & Hr & H0). pose proof (sc_b_pg_range 0 (HF 0 (ex_intro _ r (conj Hr H0)))) as H.
unfold A_G_REC in H. lia.
Qed.

Lemma sc_b_fp_closed : forall O, Forall (fun pn => 0 < fst pn) O -> ~ YI16.sink_open_fp (SC_FP O).
Proof.
intros O HO. apply sink_closed_pos. unfold SC_FP.
repeat apply Forall_cons;
  try (cbn [fst]; unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_STATE; lia).
unfold ablocks_fp. apply Forall_map. exact HO.
Qed.

(* every byte of the call slot is one of sup_call's footprint bytes *)
Lemma sc_b_slot_fp : forall O c a, sc_slot c -> c <= a < c + CALL_SIZE -> inFP (SC_FP O) a.
Proof.
intros O c a Hsl Ha. destruct Hsl as [(i & Hi & ->) | ->].
- exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8). split; [unfold SC_FP; right; left; reflexivity|].
  cbn [fst snd]. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_CALLS_MAX in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [unfold SC_FP; right; right; right; left; reflexivity|].
  cbn [fst snd]. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the footprint of arg_i / arg_line: the slot's nargs field and its args[m] slot *)
Definition sc_b_fp (c m : Z) : list (Z * Z) :=
[(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)].

Lemma sc_b_fp_slot : forall c m a, 0 <= m < REC_ARGS_MAX -> inFP (sc_b_fp c m) a -> c <= a < c + CALL_SIZE.
Proof.
intros c m a Hm (r & Hr & Ha). unfold sc_b_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE, REC_ARGS_MAX in *; lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callees' contracts, at every FP state (sup_call_c.v:65-66), and the bridge for the shape "resp 0" *)
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary record *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the image's per-binary facts: cif_prog_img _ _ IMG (CmdRecBase.v), cmd_ro_ok_of_aro,
   RRO and RPG (CmdRecRo.v) take IMG; PRW is the core's prog_rw, handed to sup_call_s1.v's sc_mid_entry *)
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis PRW : prog_rw SEGS B.
Let RUN := paj_run B LAWS.

Lemma sc_b_sig_i : SIGMA CS_arg_i = BASE + AF_arg_i.
Proof. rewrite (SIGP CS_arg_i); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma sc_b_sig_line : SIGMA CS_arg_line = BASE + AF_arg_line.
Proof. rewrite (SIGP CS_arg_line); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma sc_b_sig_ans : SIGMA CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.

(* none of the program's statics is owned by the runtime or is the errno cell *)
Lemma sc_b_pg_unowned : forall a, inFP cmd_PG a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB).
destruct Ha as (r & Hr & Hb).
assert (HOW : forallb (fun q : Z * Z => forallb (fun p : Z * Z =>
((fst q + snd q <=? fst p) || (snd p <=? fst q))%bool) cmd_PG) Tfib_owned_static = true)
by (vm_compute; reflexivity).
assert (HER : forallb (fun p : Z * Z => ((snd p <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? fst p))%bool) cmd_PG = true)
by (vm_compute; reflexivity).
split.
- intros HE. rewrite Exists_exists in HE. destruct HE as (q & Hq & Hz). unfold in_zr in Hz.
  rewrite forallb_forall in HOW. specialize (HOW q Hq). rewrite forallb_forall in HOW. specialize (HOW r Hr).
  apply Bool.orb_prop in HOW as [H1 | H1]; apply Z.leb_le in H1; lia.
- rewrite forallb_forall in HER. specialize (HER r Hr).
  apply Bool.orb_prop in HER as [H1 | H1]; apply Z.leb_le in H1; lia.
Qed.

(* a journal keeps every byte of the program's statics its footprint does not name *)
Lemma sc_b_pg_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k a,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP -> inFP cmd_PG a -> ~ inFP FP a ->
rdW W' mem' a = rdW W mem a.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k a HJ Hcl Ha Hnf.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (sc_b_pg_unowned a Ha) as [Hno He].
exact (F3 a (cif_prog_img _ _ IMG a Ha) Hno He (fp_spares_closed FP a Hcl Hnf)).
Qed.

(* the read-only bytes are kept by the walk's journal: they are image bytes outside its footprint *)
Lemma sc_b_arod : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) -> Forall (fun pn => 0 < fst pn) O ->
ajournal SEGS B STK sp0 (SC_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HAR HOin HOpos HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img SEGS a)
by (destruct Hro as [(sg & Hsg & _ & Hrng) | Hrr]; [exists sg; split; [exact Hsg | exact Hrng] | exact (RRO SEGS B LAWS HB IMG a Hrr)]).
rewrite (F3 a Himg Ho He); [exact (HR a Hro Ho He)|].
apply fp_spares_closed; [apply sc_b_fp_closed; exact HOpos|].
intros Hin. destruct (sc_b_fp_cases O a Hin) as [Hpg | Hb].
- exact (RPG SEGS B LAWS HB IMG a Hpg Hro).
- destruct (inFP_ablocks_fp_inv _ a Hb) as (p & n & Hpn & Hr).
  pose proof (blk_off_imgP B ly S W mem md p n HAR (HOin _ Hpn)) as Hoff. unfold off_img in Hoff.
  pose proof (pa_img_range a Himg) as Hrange. lia.
Qed.

(* a callee whose footprint lies in the program's statics keeps every other static byte and every byte of a
   block live before and after it *)
Lemma sc_b_call_keep : forall STK1 sp1 FP1 lyq Sq (Wq : world SEGS) memq mdq ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyq Sq Wq memq mdq [] ly2 S2 W2 mem2 md2 k1 ->
(forall b, inFP FP1 b -> inFP cmd_PG b) ->
(inFP cmd_PG a /\ ~ inFP FP1 a \/
 exists q m, In (q, m) (ablocks B lyq Sq) /\ In (q, m) (ablocks B ly2 S2) /\ q <= a < q + m) ->
rdW W2 mem2 a = rdW Wq memq a.
Proof.
intros STK1 sp1 FP1 lyq Sq Wq memq mdq ly2 S2 W2 mem2 md2 k1 a HJ HFP [(Hpg & Hna) | (q & m & Hq & Hq2 & Ha)].
- exact (sc_b_pg_kept STK1 sp1 FP1 lyq Sq Wq memq mdq [] ly2 S2 W2 mem2 md2 k1 a HJ
    (sc_b_pg_closed FP1 HFP) Hpg Hna).
- pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 q m HAR2 Hq2) as Hoff. unfold off_img in Hoff.
  pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
  replace a with (q + (a - q)) by lia. apply (F2 q m (a - q)); [exact Hq | exact Hq2 | lia |].
  intros Hin. pose proof (sc_b_pg_range _ (HFP _ Hin)) as Hr. unfold A_G_REC, A_G_QUITTING in Hr. lia.
Qed.

(* the shadow entry of the slot at any state of the allocator *)
Lemma sc_b_shok : forall ly S (W : world SEGS) mem md E c,
AR SEGS B ly S W mem md -> sc_slot c -> bv_unsigned (ew E 9) = c -> ew E 19 = Z_to_bv 64 SB ->
sh_ok SEGS sc_mid_Bx sc_mid_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR Hsl Hc Hsb.
destruct (sc_slot_facts c Hsl) as (_ & Hlo & Hhi & _). unfold A_G_REC, A_REC_SPILL in Hlo, Hhi.
unfold sh_ok, sc_mid_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E sc_mid_Bx 9%nat c 56 c 0 56).
- exact (sc_slot_addressable B HB LAWS ly S W mem md c c 56 HAR Hsl ltac:(lia) ltac:(lia)).
- unfold U, sc_mid_Bx. cbn [sv_denot]. rewrite Hsb, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hc.
- lia.
- lia.
- intros x Hx. unfold SHADOW_OFF. lia.
Qed.

(* a writable region on the slot: its window is a footprint byte of the program's statics *)
Lemma sc_b_awr_slot : forall E r rs STK sp0 O bl0 blc fr0 ly own c,
YP09.r_base r = Some 9%nat -> bv_unsigned (ew E 9) = c -> sc_slot c ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= CALL_SIZE ->
awr_ok SEGS B E rs STK sp0 (SC_FP O) bl0 blc fr0 ly own ->
awr_ok SEGS B E (r :: rs) STK sp0 (SC_FP O) bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 O bl0 blc fr0 ly own c Hb Hc Hsl Hlo Hhi H.
destruct (sc_slot_facts c Hsl) as (_ & _ & _ & Hcin).
apply (awr_ok_cons_gen B E r rs STK sp0 (SC_FP O) bl0 blc fr0 ly own 9%nat c Hb Hc); [|exact H].
intros a Ha. do 4 right. left.
split; [exact (sc_b_slot_fp O c a Hsl ltac:(unfold CALL_SIZE in *; lia))|].
split; [apply (HPROG B HB), Hcin; unfold CALL_SIZE in *; lia
       | apply (cif_prog_img _ _ IMG), Hcin; unfold CALL_SIZE in *; lia].
Qed.

(* the callees' footprint bytes: the caller may write them (awr_byte's program-static case) *)
Lemma sc_b_fp_awr : forall c m O STK sp0 bl0 blc fr0 ly own a,
sc_slot c -> 0 <= m < REC_ARGS_MAX -> inFP (sc_b_fp c m) a ->
awr_byte SEGS B STK sp0 (SC_FP O) bl0 blc fr0 ly own a.
Proof.
intros c m O STK sp0 bl0 blc fr0 ly own a Hsl Hm Ha.
pose proof (sc_b_fp_slot c m a Hm Ha) as Hin.
destruct (sc_slot_facts c Hsl) as (_ & _ & _ & Hcin).
do 4 right. left.
split; [exact (sc_b_slot_fp O c a Hsl Hin)|].
split; [exact (HPROG B HB a (Hcin a ltac:(unfold CALL_SIZE in *; lia)))
       | exact (cif_prog_img _ _ IMG a (Hcin a ltac:(unfold CALL_SIZE in *; lia)))].
Qed.

(* and they lie in the program's statics, far below any stack window *)
Lemma sc_b_fp_pg : forall c m a, sc_slot c -> 0 <= m < REC_ARGS_MAX -> inFP (sc_b_fp c m) a -> inFP cmd_PG a.
Proof.
intros c m a Hsl Hm Ha. destruct (sc_slot_facts c Hsl) as (_ & _ & _ & Hcin).
exact (Hcin a ltac:(pose proof (sc_b_fp_slot c m a Hm Ha); unfold CALL_SIZE in *; lia)).
Qed.

(* the recorder's blocks at a state are live, above the first page and of positive size *)
Lemma sc_b_O_facts : forall ly S (W : world SEGS) mem md rd R O, AR SEGS B ly S W mem md -> rec_repA B ly S rd R O ->
forall pn, In pn O -> In pn (ablocks B ly S) /\ 4096 <= fst pn /\ 1 <= snd pn.
Proof.
intros ly S W mem md rd R O HAR (Q & HQ & HOQ) [p n] Hin.
pose proof (sc_rep_blocks _ _ _ _ _ _ HQ (p, n) (proj1 (HOQ (p, n)) Hin)) as [Hbl Hpos].
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hbl) as (_ & Hp & _). cbn [fst snd] in *.
split; [exact Hbl | split; lia].
Qed.

(* a byte of a live block is no byte of the program's statics *)
Lemma sc_b_blk_not_pg : forall ly S (W : world SEGS) mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + n -> ~ inFP cmd_PG a.
Proof.
intros ly S W mem md p n a HAR Hin Ha Hpg.
pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff. unfold off_img in Hoff.
pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
pose proof (sc_b_pg_range a Hpg) as Hr. unfold A_G_REC, A_G_QUITTING in Hr. lia.
Qed.

(* a new block is apart from g_rec and from record.spill *)
Lemma sc_b_new_apart : forall ly S (W : world SEGS) mem md p n q k,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n -> (forall a, q <= a < q + k -> inFP cmd_PG a) ->
0 < k -> iv_apart p n q k.
Proof.
intros ly S W mem md p n q k HAR Hin Hn Hpg Hk.
destruct (Z.le_gt_cases (p + n) q) as [H|H]; [left; exact H|].
destruct (Z.le_gt_cases (q + k) p) as [H2|H2]; [right; exact H2|]. exfalso.
set (a := Z.max p q).
exact (sc_b_blk_not_pg ly S W mem md p n a HAR Hin ltac:(subst a; lia) (Hpg a ltac:(subst a; lia))).
Qed.

(* the range of a byte of a live block *)
Lemma sc_b_in_blk_range : forall ly S (W : world SEGS) mem md q m a,
AR SEGS B ly S W mem md -> In (q, m) (ablocks B ly S) -> q <= a < q + m ->
4096 <= a /\ a < alloc_ceiling /\ (a < 0x10000 \/ 0x606000 <= a).
Proof.
intros ly S W mem md q m a HAR Hq Ha.
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hq) as (_ & Hq4096 & Hqc & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
pose proof (blk_off_imgP B ly S W mem md q m HAR Hq) as Hoff. unfold off_img in Hoff. lia.
Qed.

(* a 64-bit word's value *)
Lemma sc_b_u64 : forall x : bv 64, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H. Qed.

Lemma sc_b_pdec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* the slot bytes a callee with footprint sc_b_fp c m writes *)
Lemma sc_b_fp_inv : forall c m a, inFP (sc_b_fp c m) a ->
c + 4 <= a < c + 8 \/ c + 8 + 8 * m <= a < c + 16 + 8 * m.
Proof.
intros c m a (r & Hr & Ha). unfold sc_b_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Ha; lia.
Qed.

Lemma sc_b_grec_pg : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof.
intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; cbn [In]; left; reflexivity|].
cbn [fst snd]. unfold REC_SIZE in Ha. lia.
Qed.

Lemma sc_b_spill_pg : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof.
intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; cbn [In]; right; left; reflexivity|].
cbn [fst snd]. unfold SC_SIZE in Ha. lia.
Qed.

(* a recorder block of the spill is one of the layout's blocks *)
Lemma sc_b_spill_lay : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof.
intros Q pn H. apply (Permutation_in _ (Permutation_sym (sc_rest_perm Q))). apply in_or_app. left. exact H.
Qed.

(* the frame region at the join: its window is the 48 bytes below the entry sp, in sup_call's stack window *)
Lemma sc_b_awr_frame : forall E rs STK sp0 FP bl0 blc fr0 ly own cs,
bv_unsigned (ew E 2) = sp0 - 48 -> 48 <= STK ->
awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 ly own ->
awr_ok SEGS B E (YP09.mkRegion (Some 2%nat) 0 48 0 48 cs :: rs) STK sp0 FP bl0 blc fr0 ly own.
Proof.
intros E rs STK sp0 FP bl0 blc fr0 ly own cs H2 HS H.
apply (awr_ok_cons_gen B E (YP09.mkRegion (Some 2%nat) 0 48 0 48 cs) rs STK sp0 FP bl0 blc fr0 ly own 2%nat (sp0 - 48)
  eq_refl H2); [|exact H].
intros a Ha. left. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia.
Qed.

(* arg_i(c, id) at 0x8aa08 through the kit's call rule for a callee whose post is apost_baseF: its footprint is the
   slot's nargs and args[0]; it returns at some FP state fx1 with fxrel fx fx1 *)
Lemma sc_b_icall : forall (Q : world SEGS -> config -> Prop) sp0 O ly S (W : world SEGS) mem md (Wq : world SEGS)
  regsq memq mdq lyq Sq kq c id,
ajournal SEGS B SUP_CALL_STK sp0 (SC_FP O) ly S W mem md [] lyq Sq Wq memq mdq kq ->
spZ regsq = sp0 + -48 ->
getr regsq 3 = w64 (as_gp B) -> getr regsq 4 = w64 (as_tp B) ->
YK0s.ret_ok (getr regsq 1) -> 4096 <= bv_unsigned (getr regsq 1) ->
s0Z regsq < alloc_ceiling ->
frm0 fx ->
Z.of_nat (length (frames Sq)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW Wq memq) ->
getr regsq 10 = w64 c -> getr regsq 11 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
sc_slot c ->
aval_mem (rdW Wq memq) (c + CALL_OFF_NARGS) 4 0 ->
st_nev Sq + EV_ARG_I <= EV_MAX -> blocks_bytes Sq + LIVE_ARG_I id <= LIVE_MAX ->
mo_ok MT Sq (XM_ARG_I MT id) ->
(forall (fx1 : YK11.FPState) ly2 S2 (W2 : world SEGS) regs2 mem2 md2 p,
  fxrel fx fx1 ->
  ajournal SEGS B SUP_CALL_STK sp0 (SC_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2 (kq + EV_ARG_I) ->
  ajournal SEGS B ARG_I_STK (sp0 + -48) (sc_b_fp c 0) lyq Sq Wq memq mdq [] ly2 S2 W2 mem2 md2 EV_ARG_I ->
  aregs_preserved regsq regs2 ->
  blocks_bytes S2 <= blocks_bytes Sq + LIVE_ARG_I id ->
  mo_le MT Sq S2 (XM_ARG_I MT id) ->
  4096 <= p < 2 ^ 64 ->
  Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length (dec id)) + 1) :: ablocks B lyq Sq) ->
  Forall (fun qk => iv_apart p (Z.of_nat (length (dec id)) + 1) (fst qk) (snd qk)) (ablocks B lyq Sq) ->
  aval_mem (rdW W2 mem2) (c + CALL_OFF_NARGS) 4 1 ->
  aval_mem (rdW W2 mem2) (c + CALL_OFF_ARGS) 8 p ->
  astr_atR (rdW W2 mem2) p (dec id) ->
  SRr SEGS W2 (mkCfg (@mkst fx1 regs2 (getr regsq 1) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS Wq (mkCfg (mkst regsq (Z_to_bv 64 (BASE + AF_arg_i)) memq (seg_rom SEGS)) mdq) Q.
Proof.
intros Q sp0 O ly S W mem md Wq regsq memq mdq lyq Sq kq c id HJ Hsp Hgp Htp Hra Hra4 Hs0 HFRM Hfr8 HROD
  H10 H11 Hid Hslot Hm0 Hev Hlive Hmok K.
pose proof (proj1 HJ) as HARq.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _ & _).
pose proof asan_consts as (C1 & _).
pose proof sc_b_stk_i as [Hi0 Hi48].
eapply SRr_bind.
{ apply (cl_callS_wideF B LAWS Wq regsq memq (Z_to_bv 64 (BASE + AF_arg_i)) SUP_CALL_STK sp0 (SC_FP O) ly S W mem md []
    lyq Sq mdq kq ARG_I_STK (sc_b_fp c 0) EV_ARG_I (-48) (getr regsq 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       blocks_bytes S2 <= blocks_bytes Sq + LIVE_ARG_I id /\ mo_le MT Sq S2 (XM_ARG_I MT id) /\
       exists p, 4096 <= p < 2 ^ 64 /\
         Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length (dec id)) + 1) :: ablocks B lyq Sq) /\
         Forall (fun qk => iv_apart p (Z.of_nat (length (dec id)) + 1) (fst qk) (snd qk)) (ablocks B lyq Sq) /\
         aval_mem (rdW W2 mem2) (c + CALL_OFF_NARGS) 4 1 /\
         aval_mem (rdW W2 mem2) (c + CALL_OFF_ARGS) 8 p /\
         astr_atR (rdW W2 mem2) p (dec id))
    HJ Hsp eq_refl ltac:(lia) Hi0 ltac:(lia) Hgp Htp eq_refl Hra Hra4 (achain_low _ _ _ _ Hs0)).
  - intros HPREc. eapply SRr_mono.
    { exact (TARG_I fx lyq Sq Wq regsq memq mdq [] c id 0 HPREc HFRM Hfr8 HROD
        (cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyq Sq Wq memq mdq HARq HROD) H10 H11 Hid Hslot Hm0 ltac:(unfold REC_ARGS_MAX; lia)
        Hev Hlive Hmok). }
    cbv beta. unfold apost_baseF.
    intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ2 & HP2 & Hbb & Hmle & HQ2).
    exists fx1, ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
    split; [exact HJ2|]. split; [exact HP2|].
    split; [exact Hbb|]. split; [exact Hmle|]. cbv zeta in HQ2.
    destruct HQ2 as [(H0 & _) | (_ & p & Hp & Hperm & Hfresh & Hna & Ha0 & Hstr)]; [unfold REC_ARGS_MAX in H0; lia|].
    rewrite Z.mul_0_r, Z.add_0_r in Ha0.
    exists p. split; [exact Hp|]. split; [exact Hperm|]. split; [exact Hfresh|]. split; [exact Hna|].
    split; [exact Ha0 | exact Hstr].
  - intros a Ha. exact (sc_b_fp_awr c 0 O SUP_CALL_STK sp0 (ablocks B ly S) (ablocks B lyq Sq) (frames S) lyq [] a
      Hslot ltac:(unfold REC_ARGS_MAX; lia) Ha).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    pose proof (sc_b_pg_range a (sc_b_fp_pg c 0 a Hslot ltac:(unfold REC_ARGS_MAX; lia) Ha)) as Hr.
    unfold A_G_REC, A_G_QUITTING in Hr. lia. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJ2c & HP2 & Hbb & Hmle &
  p & Hp & Hperm & Hfresh & Hna & Ha0 & Hstr).
exact (K fx1 ly2 S2 W2 regs2 mem2 md2 p Hfx HJ2 HJ2c HP2 Hbb Hmle Hp Hperm Hfresh Hna Ha0 Hstr).
Qed.

(* arg_line(c, line) at 0x8aa14 through the kit's call rule: its footprint is the slot's nargs and args[1]. It is
   called after arg_i, at the FP state fy that arg_i returned; its post is apost_base, so it keeps fy *)
Lemma sc_b_lcall : forall (fy : YK11.FPState) (Q : world SEGS -> config -> Prop) sp0 O ly S (W : world SEGS) mem md
  (Wq : world SEGS) regsq memq mdq lyq Sq kq c pl (line : list byte),
ajournal SEGS B SUP_CALL_STK sp0 (SC_FP O) ly S W mem md [] lyq Sq Wq memq mdq kq ->
spZ regsq = sp0 + -48 ->
getr regsq 3 = w64 (as_gp B) -> getr regsq 4 = w64 (as_tp B) ->
YK0s.ret_ok (getr regsq 1) -> 4096 <= bv_unsigned (getr regsq 1) ->
s0Z regsq < alloc_ceiling ->
arodata_okP SEGS RLO RHI B (rdW Wq memq) ->
getr regsq 10 = w64 c -> getr regsq 11 = w64 pl -> 0 <= pl < 2 ^ 64 ->
sc_slot c ->
aval_mem (rdW Wq memq) (c + CALL_OFF_NARGS) 4 1 ->
in_blockA (ablocks B lyq Sq) pl (Z.of_nat (length line) + 1) -> astr_atR (rdW Wq memq) pl line ->
Z.of_nat (length line) + 1 <= LMAX + 1 ->
st_nev Sq + EV_ARG_LINE <= EV_MAX -> blocks_bytes Sq + LIVE_ARG_LINE line <= LIVE_MAX ->
mo_ok MT Sq (XM_ARG_LINE MT line) ->
(forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 p,
  ajournal SEGS B SUP_CALL_STK sp0 (SC_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2 (kq + EV_ARG_LINE) ->
  ajournal SEGS B ARG_LINE_STK (sp0 + -48) (sc_b_fp c 1) lyq Sq Wq memq mdq [] ly2 S2 W2 mem2 md2 EV_ARG_LINE ->
  aregs_preserved regsq regs2 ->
  blocks_bytes S2 <= blocks_bytes Sq + LIVE_ARG_LINE line ->
  mo_le MT Sq S2 (XM_ARG_LINE MT line) ->
  4096 <= p < 2 ^ 64 ->
  Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length line) + 1) :: ablocks B lyq Sq) ->
  Forall (fun qk => iv_apart p (Z.of_nat (length line) + 1) (fst qk) (snd qk)) (ablocks B lyq Sq) ->
  aval_mem (rdW W2 mem2) (c + CALL_OFF_NARGS) 4 2 ->
  aval_mem (rdW W2 mem2) (c + CALL_OFF_ARGS + 8) 8 p ->
  astr_atR (rdW W2 mem2) p (canon line) ->
  SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regsq 1) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS Wq (mkCfg (@mkst fy regsq (Z_to_bv 64 (BASE + AF_arg_line)) memq (seg_rom SEGS)) mdq) Q.
Proof.
intros fy Q sp0 O ly S W mem md Wq regsq memq mdq lyq Sq kq c pl line HJ Hsp Hgp Htp Hra Hra4 Hs0 HROD
  H10 H11 Hpl Hslot Hm1 HBLK HSTR HLEN Hev Hlive Hmok K.
pose proof (proj1 HJ) as HARq.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _ & _).
pose proof asan_consts as (C1 & _).
pose proof sc_b_stk_line as [Hl0 Hl48].
eapply SRr_bind.
{ apply (cl_callS_wide (fx := fy) B LAWS Wq regsq memq (Z_to_bv 64 (BASE + AF_arg_line)) SUP_CALL_STK sp0 (SC_FP O) ly S W mem md
    [] lyq Sq mdq kq ARG_LINE_STK (sc_b_fp c 1) EV_ARG_LINE (-48) (getr regsq 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       blocks_bytes S2 <= blocks_bytes Sq + LIVE_ARG_LINE line /\ mo_le MT Sq S2 (XM_ARG_LINE MT line) /\
       exists p, 4096 <= p < 2 ^ 64 /\
         Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length line) + 1) :: ablocks B lyq Sq) /\
         Forall (fun qk => iv_apart p (Z.of_nat (length line) + 1) (fst qk) (snd qk)) (ablocks B lyq Sq) /\
         aval_mem (rdW W2 mem2) (c + CALL_OFF_NARGS) 4 2 /\
         aval_mem (rdW W2 mem2) (c + CALL_OFF_ARGS + 8) 8 p /\
         astr_atR (rdW W2 mem2) p (canon line))
    HJ Hsp eq_refl ltac:(lia) Hl0 ltac:(lia) Hgp Htp eq_refl Hra Hra4 (achain_low _ _ _ _ Hs0)).
  - intros HPREc. eapply SRr_mono.
    { exact (TARG_LINE fy lyq Sq Wq regsq memq mdq [] c pl 1 line HPREc HROD H10 H11 Hpl Hslot Hm1
        ltac:(unfold REC_ARGS_MAX; lia) HBLK HSTR HLEN Hev Hlive Hmok). }
    cbv beta. unfold apost_base. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbb & Hmle & HQ2).
    exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
    split; [exact Hbb|]. split; [exact Hmle|]. cbv zeta in HQ2.
    destruct HQ2 as [(H0 & _) | (_ & p & Hp & Hperm & Hfresh & Hna & Ha1 & Hstr)]; [unfold REC_ARGS_MAX in H0; lia|].
    exists p. split; [exact Hp|]. split; [exact Hperm|]. split; [exact Hfresh|]. split; [exact Hna|].
    split; [exact Ha1 | exact Hstr].
  - intros a Ha. exact (sc_b_fp_awr c 1 O SUP_CALL_STK sp0 (ablocks B ly S) (ablocks B lyq Sq) (frames S) lyq [] a
      Hslot ltac:(unfold REC_ARGS_MAX; lia) Ha).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    pose proof (sc_b_pg_range a (sc_b_fp_pg c 1 a Hslot ltac:(unfold REC_ARGS_MAX; lia) Ha)) as Hr.
    unfold A_G_REC, A_G_QUITTING in Hr. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & Hbb & Hmle &
  p & Hp & Hperm & Hfresh & Hna & Ha1 & Hstr).
exact (K ly2 S2 W2 regs2 mem2 md2 p HJ2 HJ2c HP2 Hbb Hmle Hp Hperm Hfresh Hna Ha1 Hstr).
Qed.

Ltac sc_b_name_ms HS nm :=
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into nm
| st_ok _ _ _ (restrict _ ?m) => rename m into nm
end.
Ltac sc_b_set_md nm :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (nm := mdx) in *; clearbody nm end.
Ltac sc_b_awr_rs :=
lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.

(* the body: from the join 0x8a9d0 to answer's entry. The tail's statement is taken at every FP state: it is applied
   at the FP state arg_i returns *)
Lemma sc_body : (forall fx0 : YK11.FPState, SC_T_stmt (fx := fx0) B MT) -> SC_B_stmt B MT.
Proof.
intros SCT ly S W regs mem md ch id pl line R O lyc Sc Wc regsc memc mdc k c t HPRE HBLK HMID.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HPRE0 & HFRM & Hfr8 & HROD & HRO & H10 & Hid & H11 & Hpl & (HINB & HAPO & HSTR & HLEN) &
  HREP0 & Hev & Hlive & HMOK).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJc & Hk & Hslot & HRJ & HFR & Hfrc & Hbbc & MLEc & HLc & HQex).
pose proof HRJ as (Rsp & R9 & R19 & R18 & R8 & R3 & R4 & Rhi).
destruct (sc_slot_facts c Hslot) as (Hc8 & Hclo & Hchi & Hcin).
unfold A_G_REC, A_REC_SPILL in Hclo, Hchi.
pose proof (proj1 HJc) as HARc.
pose proof (sc_b_O_facts ly S W mem md _ R O HAR HREP0) as HOf.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn H; exact (proj1 (HOf pn H))).
assert (HOpos : Forall (fun pn => 0 < fst pn) O) by (apply Forall_forall; intros pn H; pose proof (HOf pn H); lia).
pose proof sc_b_stk48 as WS48.
destruct HBLK as (pb & kb & Hpb & HpbO & Hpb1 & Hpb2).
destruct (sc_b_in_blk_range ly S W mem md pb kb pl HAR Hpb ltac:(lia)) as (Hpl1 & Hpl2 & _).
destruct HQex as (Q & HQ & HOQ & HARM).
(* the bytes of a block live at the entry and none of the recorder's are the join's *)
assert (JB : forall p m i, In (p, m) (ablocks B ly S) -> ~ In (p, m) O -> 0 <= i < m ->
  rdW Wc memc (p + i) = rdW W mem (p + i)).
{ intros p m i Hin HnO Hi. destruct HARM as [(_ & _ & _ & _ & _ & _ & Fb) | (_ & _ & _ & _ & Fb)].
  - exact (Fb p m i Hin Hi).
  - apply (Fb p m i Hin); [|exact Hi]. intros Hsp. apply HnO. apply HOQ. exact (sc_b_spill_lay Q _ Hsp). }
assert (Hcarm : (length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) \/
  (16 <= length (r_calls R))%nat /\ c = A_REC_SPILL).
{ destruct HARM as [(Hlt & Hceq & _) | (H16 & Hceq & _)]; [left; split; assumption | right; split; [lia | exact Hceq]]. }
(* the five saved registers in the frame at the join *)
assert (MF : forall j r, nth_error sc_saved j = Some r ->
  aval_mem (rdW Wc memc) (spZ regsc + (40 - 8 * Z.of_nat j)) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. rewrite Rsp. replace (spZ regs - 48 + (40 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
  exact (HFR j r Hj). }
pose proof (MF 0%nat 1 eq_refl) as Mra. pose proof (MF 1%nat 8 eq_refl) as M00.
pose proof (MF 2%nat 9 eq_refl) as M10. pose proof (MF 3%nat 18 eq_refl) as M20.
pose proof (MF 4%nat 19 eq_refl) as M30. clear MF.
change (40 - 8 * Z.of_nat 0) with 40 in Mra. change (40 - 8 * Z.of_nat 1) with 32 in M00.
change (40 - 8 * Z.of_nat 2) with 24 in M10. change (40 - 8 * Z.of_nat 3) with 16 in M20.
change (40 - 8 * Z.of_nat 4) with 8 in M30.
remember (bv_unsigned (getr regs (Z_to_bv 5 1))) as ra0 eqn:Era0 in Mra.
remember (bv_unsigned (getr regs (Z_to_bv 5 8))) as s00 eqn:Es00 in M00.
remember (bv_unsigned (getr regs (Z_to_bv 5 9))) as s10 eqn:Es10 in M10.
remember (bv_unsigned (getr regs (Z_to_bv 5 18))) as s20 eqn:Es20 in M20.
remember (bv_unsigned (getr regs (Z_to_bv 5 19))) as s30 eqn:Es30 in M30.
assert (Rra : 0 <= ra0 < 2 ^ 64) by (rewrite Era0; apply sc_b_u64).
assert (R00 : 0 <= s00 < 2 ^ 64) by (rewrite Es00; apply sc_b_u64).
assert (R10 : 0 <= s10 < 2 ^ 64) by (rewrite Es10; apply sc_b_u64).
assert (R20 : 0 <= s20 < 2 ^ 64) by (rewrite Es20; apply sc_b_u64).
assert (R30 : 0 <= s30 < 2 ^ 64) by (rewrite Es30; apply sc_b_u64).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
assert (Hsp16 : spZ regsc mod 16 = 0).
{ rewrite Rsp. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
destruct (sc_mid_entry B HB LAWS PRW lyc Sc Wc regsc memc mdc c ra0 s00 s10 s20 s30 HARc Hslot R9 R19
  ltac:(lia) ltac:(lia) Hsp16 ltac:(intros a Ha; apply HpresJ; lia) M30 M20 M10 M00 Mra Rra R00 R10 R20 R30)
  as [HS SHOK].
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (sc_mid_E regsc) n = getr regsc r).
{ intros n r Hn'. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold sc_mid_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn'. }
assert (HEI : img_env VAL A_LIM (sc_mid_E regsc)) by (unfold sc_mid_E; apply Eimg_env).
set (E := sc_mid_E regsc) in *. clearbody E.
assert (U2 : bv_unsigned (ew E 2) = spZ regsc) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U9 : bv_unsigned (ew E 9) = c) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
(* 0x8a9d0 .. 0x8aa08: the two checks of the slot, c->fn := REC_CALL, c->nargs := 0, a0 := c, a1 := id,
   the call of arg_i *)
paj_run_tok RUN HS HJc SHOK sc_Bspan.
{ sc_b_awr_rs.
  apply sc_b_awr_frame; [rewrite U2; lia | exact WS48 |].
  eapply sc_b_awr_slot; [reflexivity | exact U9 | exact Hslot | cbn; lia | cbn; unfold CALL_SIZE; lia |].
  apply awr_ok_nil. }
sc_b_set_md mdv1. sc_b_name_ms HS ms1.
pose proof (kept_of_frame (segs:=SEGS) E _ (w_H Wc) memc (ms_mem ms1)
  (fun a => spZ regsc <= a < spZ regsc + 48 \/ c <= a < c + 8) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U2, ?U9 in Hrr; lia|]);
        destruct Hin)) as KEEP1.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) msx) 1 _ HS eq_refl) as HRS1 end.
cbn [ms_mem restrict] in HRS1.
pose proof (field_of_region E _ 9 c _ 0 8 0 8 0 4 (SLit 1) 1 HRS1 U9
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VF1.
pose proof (field_of_region E _ 9 c _ 0 8 0 8 4 4 (SLit 0) 0 HRS1 U9
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VN1.
change (N.to_nat 4) with 4%nat in VF1, VN1.
apply sc_aval_of_val_mem in VF1. apply sc_aval_of_val_mem in VN1.
clear HRS1.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
rewrite sc_b_sig_i.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs + -48) by (unfold spZ at 1; rewrite P2, U2, Rsp; lia).
assert (Hgp1 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (Htp1 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (Hra1 : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra41 : 4096 <= bv_unsigned (getr (ms_regs ms1) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
assert (Hs01 : s0Z (ms_regs ms1) < alloc_ceiling)
  by (unfold s0Z; rewrite P8, (EE 8%nat 8%bv eq_refl), R8, H11, unsigned_lit_small by lia; lia).
assert (H101 : getr (ms_regs ms1) 10 = w64 c) by (rewrite P10, (EE 9%nat 9%bv eq_refl); exact R9).
assert (H111 : getr (ms_regs ms1) 11 = w64 id) by (rewrite P11, (EE 18%nat 18%bv eq_refl), R18; exact H10).
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms1)))
  by exact (sc_b_arod SUP_CALL_STK (spZ regs) O ly S W mem md [] lyc Sc Wc (ms_mem ms1) mdv1 k HAR HOin HOpos HJc HROD).
assert (HEV1 : st_nev Sc + EV_ARG_I <= EV_MAX).
{ pose proof HJc as (_ & _ & _ & _ & _ & _ & Hnev & _). clear - Hnev Hev Hk.
  unfold EV_SUP_CALL, EV_ARG_I, EV_ARG_LINE, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP, EV_REC_CANONICAL in *. lia. }
assert (LNN : 0 <= LIVE_ARG_I id /\ 0 <= LIVE_ARG_LINE line /\ 0 <= LIVE_ANSWER t).
{ unfold LIVE_ARG_I, LIVE_ARG_LINE, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP, LIVE_REC_CANONICAL. lia. }
unfold LIVE_SUP_CALL in Hlive.
assert (HLV1 : blocks_bytes Sc + LIVE_ARG_I id <= LIVE_MAX) by lia.
pose proof (mo_free_nonneg MT MTL) as MF0.
pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec id)) + 1) ltac:(lia)) as MFi.
pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length line) + 1) ltac:(lia)) as MFl.
pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)) as MFt.
assert (HMO1 : mo_ok MT Sc (XM_ARG_I MT id)).
{ apply (mok_station MT S Sc (XM_SUP_CALL MT R id line t) (rec_spill_frees R * mo_free MT) (XM_ARG_I MT id) MTL HMOK
    MLEc); unfold XM_SUP_CALL, XM_ANSWER, XM_HAND_BACK, XM_ARG_I, XM_ARG_LINE, XM_XSTRDUP, XM_REC_CANONICAL in *; lia. }
assert (KS1 : forall a, inFP cmd_PG a -> ~ (c <= a < c + 8) -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha Hn. pose proof (sc_b_pg_range a Ha) as Hr. unfold A_G_REC, A_G_QUITTING in Hr. apply KEEP1; lia. }
assert (KB1 : forall q m a, In (q, m) (ablocks B lyc Sc) -> q <= a < q + m -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros q m a Hq Ha. destruct (sc_b_in_blk_range lyc Sc Wc memc mdc q m a HARc Hq Ha) as (Ha1 & Ha2 & Ha3).
  apply KEEP1; lia. }
clear KEEP1.
refine (sc_b_icall _ (spZ regs) O ly S W mem md Wc (ms_regs ms1) (ms_mem ms1) mdv1 lyc Sc k c id HJc Hsp1 Hgp1 Htp1
  Hra1 Hra41 Hs01 HFRM ltac:(rewrite Hfrc; exact Hfr8) HROD1 H101 H111 Hid Hslot VN1 HEV1 HLV1 HMO1 _).
intros fx1 ly2 S2 W2 regs2 mem2 md2 p1 Hfx HJ2 HJ2c HP2 Hbb2 Hmle2 Hp1 Hperm1 Hfresh1 HN2 HA0 HSTR1.
(* arg_i returned at fx1: the rest of the walk runs at fx1 (the run lemma bound again at fx1), and the tail's
   statement is applied at fx1 with sc_pre at fx1 (rounding mode 0 at fx1: fxrel_frm0) *)
pose proof (paj_run (fx := fx1) B LAWS) as RUN1.
assert (HPRE1 : sc_pre (fx := fx1) B MT ly S W regs mem md ch id pl line R O t).
{ unfold sc_pre. split; [exact HPRE0|].
  split; [exact (fxrel_frm0 fx fx1 HFRM Hfx) | exact (proj2 (proj2 HPRE))]. }
rewrite P1.
(* back at 0x8aa0c: the frame is kept, the slot region is dropped *)
jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?T -> _ => assert (HRK : T); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B E ARG_I_STK (spZ regs + -48) (sc_b_fp c 0) lyc Sc Wc (ms_mem ms1) mdv1
    ly2 S2 W2 mem2 md2 EV_ARG_I 2 0 48 0 48 _ (spZ regs - 48) SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [] _
    HJ2c HJ2 ltac:(rewrite U2; exact Rsp)); [lia | lia | lia | lia | lia |].
  intros a Ha Hf. pose proof (sc_b_pg_range a (sc_b_fp_pg c 0 a Hslot ltac:(unfold REC_ARGS_MAX; lia) Hf)) as Hr.
  unfold A_G_REC, A_G_QUITTING in Hr. lia. }
clear HS.
(* the symbolic state after the call, stated at the entry's fx, is the same state at fx1 (YL05.v st_ok_xfx) *)
lazymatch type of HS2 with
| @st_ok_pi ?sg ?vl ?fz ?Ex ?ssx (@mkst ?fz2 ?rg ?pc ?mm ?rom) =>
    pose proof (YL05.st_ok_xfx fz fx1 sg Ex (abs_ss vl ssx) rg pc mm HS2) as HSx;
    change (@st_ok_pi sg vl fx1 Ex ssx (@mkst fx1 rg pc mm rom)) in HSx
end.
clear HS2. rewrite <- (restrict_mkst_fx (fx := fx1)) in HSx. rename HSx into HS.
remember (havoc E 64 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 64)%nat -> ew E2 n = ew E n)
  by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
clear HE2.
pose proof (proj1 HJ2c) as HAR2.
assert (Hsub12 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn H; exact (Permutation_in _ (Permutation_sym Hperm1) (or_intror H))).
assert (HP1in2 : In (p1, Z.of_nat (length (dec id)) + 1) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm1) (or_introl eq_refl)).
assert (FP0 : forall b, inFP (sc_b_fp c 0) b -> inFP cmd_PG b)
  by (intros b Hb; exact (sc_b_fp_pg c 0 b Hslot ltac:(unfold REC_ARGS_MAX; lia) Hb)).
assert (KS2 : forall a, inFP cmd_PG a -> ~ inFP (sc_b_fp c 0) a -> rdW W2 mem2 a = rdW Wc (ms_mem ms1) a)
  by (intros a Ha Hn; exact (sc_b_call_keep ARG_I_STK (spZ regs + -48) (sc_b_fp c 0) lyc Sc Wc (ms_mem ms1) mdv1
    ly2 S2 W2 mem2 md2 EV_ARG_I a HJ2c FP0 (or_introl (conj Ha Hn)))).
assert (KB2 : forall q m a, In (q, m) (ablocks B lyc Sc) -> q <= a < q + m -> rdW W2 mem2 a = rdW Wc (ms_mem ms1) a).
{ intros q m a Hq Ha. apply (sc_b_call_keep ARG_I_STK (spZ regs + -48) (sc_b_fp c 0) lyc Sc Wc (ms_mem ms1) mdv1
    ly2 S2 W2 mem2 md2 EV_ARG_I a HJ2c FP0).
  right. exists q, m. split; [exact Hq|]. split; [exact (Hsub12 _ Hq) | exact Ha]. }
(* 0x8aa0c .. 0x8aa14: a0 := c, a1 := line, the call of arg_line *)
assert (U22 : bv_unsigned (ew E2 2) = spZ regsc) by (rewrite OLD2 by lia; exact U2).
assert (U92 : bv_unsigned (ew E2 9) = c) by (rewrite OLD2 by lia; exact U9).
assert (E192 : ew E2 19 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; rewrite (EE 19%nat 19%bv eq_refl); exact R19).
pose proof (sc_b_shok ly2 S2 W2 mem2 md2 E2 c HAR2 Hslot U92 E192) as SHOK2.
paj_run_tok RUN1 HS HJ2 SHOK2 sc_Bspan.
{ sc_b_awr_rs. apply sc_b_awr_frame; [rewrite U22; lia | exact WS48 |]. apply awr_ok_nil. }
sc_b_set_md mdv2. sc_b_name_ms HS ms2.
pose proof (kept_of_frame (segs:=SEGS) E2 _ (w_H W2) mem2 (ms_mem ms2)
  (fun a => spZ regsc <= a < spZ regsc + 48) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U22 in Hrr; lia|]);
        destruct Hin)) as KEEP2.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
rewrite sc_b_sig_line.
assert (Hsp2 : spZ (ms_regs ms2) = spZ regs + -48) by (unfold spZ at 1; rewrite Q2, U22, Rsp; lia).
assert (Hgp2 : getr (ms_regs ms2) 3 = w64 (as_gp B))
  by (rewrite Q3, OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (Htp2 : getr (ms_regs ms2) 4 = w64 (as_tp B))
  by (rewrite Q4, OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (Hra2 : YK0s.ret_ok (getr (ms_regs ms2) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra42 : 4096 <= bv_unsigned (getr (ms_regs ms2) 1)) by (rewrite Q1, unsigned_lit_small by lia; lia).
assert (Hs02 : s0Z (ms_regs ms2) < alloc_ceiling)
  by (unfold s0Z; rewrite Q8, OLD2 by lia; rewrite (EE 8%nat 8%bv eq_refl), R8, H11, unsigned_lit_small by lia; lia).
assert (H102 : getr (ms_regs ms2) 10 = w64 c)
  by (rewrite Q10, OLD2 by lia; rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (H112 : getr (ms_regs ms2) 11 = w64 pl)
  by (rewrite Q11, OLD2 by lia; rewrite (EE 8%nat 8%bv eq_refl), R8; exact H11).
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms2)))
  by exact (sc_b_arod SUP_CALL_STK (spZ regs) O ly S W mem md [] ly2 S2 W2 (ms_mem ms2) mdv2 (k + EV_ARG_I)
    HAR HOin HOpos HJ2 HROD).
assert (KS3 : forall a, inFP cmd_PG a -> rdW W2 (ms_mem ms2) a = rdW W2 mem2 a).
{ intros a Ha. pose proof (sc_b_pg_range a Ha) as Hr. unfold A_G_REC, A_G_QUITTING in Hr. apply KEEP2; lia. }
assert (KB3 : forall q m a, In (q, m) (ablocks B ly2 S2) -> q <= a < q + m -> rdW W2 (ms_mem ms2) a = rdW W2 mem2 a).
{ intros q m a Hq Ha. destruct (sc_b_in_blk_range ly2 S2 W2 mem2 md2 q m a HAR2 Hq Ha) as (Ha1 & Ha2 & Ha3).
  apply KEEP2; lia. }
clear KEEP2.
assert (HN2' : aval_mem (rdW W2 (ms_mem ms2)) (c + CALL_OFF_NARGS) 4 1).
{ apply (sc_aval_frame _ _ _ _ _ HN2). intros x Hx. apply KS3. apply Hcin. unfold CALL_OFF_NARGS in Hx. lia. }
assert (Hinl : In (pb, kb) (ablocks B lyc Sc)) by exact (HLc _ Hpb HpbO).
assert (HINB2 : in_blockA (ablocks B ly2 S2) pl (Z.of_nat (length line) + 1)).
{ exists pb, kb. split; [exact (Hsub12 _ Hinl) | lia]. }
assert (HSTR2' : astr_atR (rdW W2 (ms_mem ms2)) pl line).
{ apply (sc_str_frame (rdW W mem) _ pl line HSTR). intros x Hx.
  assert (Hxb : pb <= x < pb + kb) by lia.
  rewrite (KB3 pb kb x (Hsub12 _ Hinl) Hxb), (KB2 pb kb x Hinl Hxb), (KB1 pb kb x Hinl Hxb).
  replace x with (pb + (x - pb)) by lia. exact (JB pb kb (x - pb) Hpb HpbO ltac:(lia)). }
assert (HEV2 : st_nev S2 + EV_ARG_LINE <= EV_MAX).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev & _). clear - Hnev Hev Hk.
  unfold EV_SUP_CALL, EV_ARG_I, EV_ARG_LINE, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP, EV_REC_CANONICAL in *. lia. }
assert (HLV2 : blocks_bytes S2 + LIVE_ARG_LINE line <= LIVE_MAX) by lia.
assert (HMLE2 : mo_le MT S S2 (rec_spill_frees R * mo_free MT + XM_ARG_I MT id))
  by exact (mle_station MT S Sc S2 _ _ MTL MLEc Hmle2).
assert (HMO2 : mo_ok MT S2 (XM_ARG_LINE MT line)).
{ apply (mok_station MT S S2 (XM_SUP_CALL MT R id line t) _ (XM_ARG_LINE MT line) MTL HMOK HMLE2);
  unfold XM_SUP_CALL, XM_ANSWER, XM_HAND_BACK, XM_ARG_I, XM_ARG_LINE, XM_XSTRDUP, XM_REC_CANONICAL in *; lia. }
refine (sc_b_lcall fx1 _ (spZ regs) O ly S W mem md W2 (ms_regs ms2) (ms_mem ms2) mdv2 ly2 S2 (k + EV_ARG_I) c pl line
  HJ2 Hsp2 Hgp2 Htp2 Hra2 Hra42 Hs02 HROD2 H102 H112 Hpl Hslot HN2' HINB2 HSTR2' HLEN HEV2 HLV2 HMO2 _).
intros ly3 S3 W3 regs3 mem3 md3 p2 HJ3 HJ3c HP3 Hbb3 Hmle3 Hp2 Hperm2 Hfresh2 HN3 HA1 HSTR2.
rewrite Q1.
(* back at 0x8aa18: the frame is kept *)
jafter_call_keep_pi HS 96%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?T -> _ => assert (HRK : T); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B E2 ARG_LINE_STK (spZ regs + -48) (sc_b_fp c 1) ly2 S2 W2 (ms_mem ms2) mdv2
    ly3 S3 W3 mem3 md3 EV_ARG_LINE 2 0 48 0 48 _ (spZ regs - 48) SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [] _
    HJ3c HJ3 ltac:(rewrite U22; exact Rsp)); [lia | lia | lia | lia | lia |].
  intros a Ha Hf. pose proof (sc_b_pg_range a (sc_b_fp_pg c 1 a Hslot ltac:(unfold REC_ARGS_MAX; lia) Hf)) as Hr.
  unfold A_G_REC, A_G_QUITTING in Hr. lia. }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS3. rename HS3 into HS.
remember (havoc E2 96 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 96)%nat -> ew E3 n = ew E2 n)
  by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
clear HE3.
pose proof (proj1 HJ3c) as HAR3.
assert (Hsub23 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly3 S3))
  by (intros pn H; exact (Permutation_in _ (Permutation_sym Hperm2) (or_intror H))).
assert (HP2in3 : In (p2, Z.of_nat (length line) + 1) (ablocks B ly3 S3))
  by exact (Permutation_in _ (Permutation_sym Hperm2) (or_introl eq_refl)).
assert (FP1 : forall b, inFP (sc_b_fp c 1) b -> inFP cmd_PG b)
  by (intros b Hb; exact (sc_b_fp_pg c 1 b Hslot ltac:(unfold REC_ARGS_MAX; lia) Hb)).
assert (KS4 : forall a, inFP cmd_PG a -> ~ inFP (sc_b_fp c 1) a -> rdW W3 mem3 a = rdW W2 (ms_mem ms2) a)
  by (intros a Ha Hn; exact (sc_b_call_keep ARG_LINE_STK (spZ regs + -48) (sc_b_fp c 1) ly2 S2 W2 (ms_mem ms2) mdv2
    ly3 S3 W3 mem3 md3 EV_ARG_LINE a HJ3c FP1 (or_introl (conj Ha Hn)))).
assert (KB4 : forall q m a, In (q, m) (ablocks B ly2 S2) -> q <= a < q + m -> rdW W3 mem3 a = rdW W2 (ms_mem ms2) a).
{ intros q m a Hq Ha. apply (sc_b_call_keep ARG_LINE_STK (spZ regs + -48) (sc_b_fp c 1) ly2 S2 W2 (ms_mem ms2) mdv2
    ly3 S3 W3 mem3 md3 EV_ARG_LINE a HJ3c FP1).
  right. exists q, m. split; [exact Hq|]. split; [exact (Hsub23 _ Hq) | exact Ha]. }
(* 0x8aa18 .. 0x8aa40: a1 := "resp 0", a2 := 1, a0 := c, the frame reloaded, sp += 48, `j answer` *)
assert (U23 : bv_unsigned (ew E3 2) = spZ regsc) by (rewrite OLD3 by lia; exact U22).
assert (U93 : bv_unsigned (ew E3 9) = c) by (rewrite OLD3 by lia; exact U92).
assert (E193 : ew E3 19 = Z_to_bv 64 SB) by (rewrite OLD3 by lia; exact E192).
pose proof (sc_b_shok ly3 S3 W3 mem3 md3 E3 c HAR3 Hslot U93 E193) as SHOK3.
paj_run_tok RUN1 HS HJ3 SHOK3 sc_Bspan.
{ sc_b_awr_rs. apply sc_b_awr_frame; [rewrite U23; lia | exact WS48 |]. apply awr_ok_nil. }
sc_b_set_md mdv3. sc_b_name_ms HS ms3.
pose proof (kept_of_frame (segs:=SEGS) E3 _ (w_H W3) mem3 (ms_mem ms3)
  (fun a => spZ regsc <= a < spZ regsc + 48) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U23 in Hrr; lia|]);
        destruct Hin)) as KEEP3.
clear HF HFr HG.
pmkst HS.
rewrite sc_b_sig_ans.
assert (KS5 : forall a, inFP cmd_PG a -> rdW W3 (ms_mem ms3) a = rdW W3 mem3 a).
{ intros a Ha. pose proof (sc_b_pg_range a Ha) as Hr. unfold A_G_REC, A_G_QUITTING in Hr. apply KEEP3; lia. }
assert (KB5 : forall q m a, In (q, m) (ablocks B ly3 S3) -> q <= a < q + m -> rdW W3 (ms_mem ms3) a = rdW W3 mem3 a).
{ intros q m a Hq Ha. destruct (sc_b_in_blk_range ly3 S3 W3 mem3 md3 q m a HAR3 Hq Ha) as (Ha1 & Ha2 & Ha3).
  apply KEEP3; lia. }
clear KEEP3.
(* the bytes the recorder step asks about, from the join to answer's entry *)
assert (KSall : forall a, inFP cmd_PG a -> ~ (c <= a < c + 24) -> rdW W3 (ms_mem ms3) a = rdW Wc memc a).
{ intros a Ha Hn.
  assert (N0 : ~ inFP (sc_b_fp c 0) a) by (intros Hf; destruct (sc_b_fp_inv c 0 a Hf); lia).
  assert (N1 : ~ inFP (sc_b_fp c 1) a) by (intros Hf; destruct (sc_b_fp_inv c 1 a Hf); lia).
  rewrite (KS5 a Ha), (KS4 a Ha N1), (KS3 a Ha), (KS2 a Ha N0). exact (KS1 a Ha ltac:(lia)). }
assert (KBall : forall q m a, In (q, m) (ablocks B lyc Sc) -> q <= a < q + m -> rdW W3 (ms_mem ms3) a = rdW Wc memc a).
{ intros q m a Hq Ha. pose proof (Hsub12 _ Hq) as Hq2. pose proof (Hsub23 _ Hq2) as Hq3.
  rewrite (KB5 q m a Hq3 Ha), (KB4 q m a Hq2 Ha), (KB3 q m a Hq2 Ha), (KB2 q m a Hq Ha). exact (KB1 q m a Hq Ha). }
assert (Hfn5 : aval_mem (rdW W3 (ms_mem ms3)) (c + CALL_OFF_FN) 4 REC_CALL).
{ unfold CALL_OFF_FN, REC_CALL. apply (sc_aval_frame _ _ _ _ _ VF1). intros x Hx.
  assert (Hpg : inFP cmd_PG x) by (apply Hcin; lia).
  assert (N0 : ~ inFP (sc_b_fp c 0) x) by (intros Hf; destruct (sc_b_fp_inv c 0 x Hf); lia).
  assert (N1 : ~ inFP (sc_b_fp c 1) x) by (intros Hf; destruct (sc_b_fp_inv c 1 x Hf); lia).
  rewrite (KS5 x Hpg), (KS4 x Hpg N1), (KS3 x Hpg). exact (KS2 x Hpg N0). }
assert (Hna5 : aval_mem (rdW W3 (ms_mem ms3)) (c + CALL_OFF_NARGS) 4 2).
{ apply (sc_aval_frame _ _ _ _ _ HN3). intros x Hx. unfold CALL_OFF_NARGS in Hx. apply KS5. apply Hcin. lia. }
assert (Ha05 : aval_mem (rdW W3 (ms_mem ms3)) (c + CALL_OFF_ARGS) 8 p1).
{ apply (sc_aval_frame _ _ _ _ _ HA0). intros x Hx. unfold CALL_OFF_ARGS in Hx.
  assert (Hpg : inFP cmd_PG x) by (apply Hcin; lia).
  assert (N1 : ~ inFP (sc_b_fp c 1) x) by (intros Hf; destruct (sc_b_fp_inv c 1 x Hf); lia).
  rewrite (KS5 x Hpg), (KS4 x Hpg N1). exact (KS3 x Hpg). }
assert (Ha15 : aval_mem (rdW W3 (ms_mem ms3)) (c + CALL_OFF_ARGS + 8) 8 p2).
{ apply (sc_aval_frame _ _ _ _ _ HA1). intros x Hx. unfold CALL_OFF_ARGS in Hx. apply KS5. apply Hcin. lia. }
assert (Hs15 : astr_atR (rdW W3 (ms_mem ms3)) p1 (dec id)).
{ apply (sc_str_frame (rdW W2 mem2) _ p1 (dec id) HSTR1). intros x Hx.
  assert (Hxb : p1 <= x < p1 + (Z.of_nat (length (dec id)) + 1)) by lia.
  rewrite (KB5 _ _ x (Hsub23 _ HP1in2) Hxb), (KB4 _ _ x HP1in2 Hxb). exact (KB3 _ _ x HP1in2 Hxb). }
assert (Hs25 : astr_atR (rdW W3 (ms_mem ms3)) p2 (canon line)).
{ apply (sc_str_frame (rdW W3 mem3) _ p2 (canon line) HSTR2). intros x Hx.
  pose proof (canon_length line) as CL.
  exact (KB5 _ _ x HP2in3 ltac:(lia)). }
(* the two new blocks *)
assert (Hg1 : iv_apart p1 (Z.of_nat (length (dec id)) + 1) A_G_REC REC_SIZE)
  by exact (sc_b_new_apart ly2 S2 W2 mem2 md2 _ _ A_G_REC REC_SIZE HAR2 HP1in2 ltac:(lia) sc_b_grec_pg
    ltac:(unfold REC_SIZE; lia)).
assert (Hs1 : iv_apart p1 (Z.of_nat (length (dec id)) + 1) A_REC_SPILL SC_SIZE)
  by exact (sc_b_new_apart ly2 S2 W2 mem2 md2 _ _ A_REC_SPILL SC_SIZE HAR2 HP1in2 ltac:(lia) sc_b_spill_pg
    ltac:(unfold SC_SIZE; lia)).
assert (Hg2 : iv_apart p2 (Z.of_nat (length line) + 1) A_G_REC REC_SIZE)
  by exact (sc_b_new_apart ly3 S3 W3 mem3 md3 _ _ A_G_REC REC_SIZE HAR3 HP2in3 ltac:(lia) sc_b_grec_pg
    ltac:(unfold REC_SIZE; lia)).
assert (Hs2 : iv_apart p2 (Z.of_nat (length line) + 1) A_REC_SPILL SC_SIZE)
  by exact (sc_b_new_apart ly3 S3 W3 mem3 md3 _ _ A_REC_SPILL SC_SIZE HAR3 HP2in3 ltac:(lia) sc_b_spill_pg
    ltac:(unfold SC_SIZE; lia)).
pose proof (dec_length id Hid) as DL. pose proof (canon_length line) as CL.
assert (En1 : Z.of_nat (length (dec id)) + 1 <= Z.of_nat (length (dec id)) + 1 <= LMAX + 2) by (unfold LMAX; lia).
assert (En2 : Z.of_nat (length (canon line)) + 1 <= Z.of_nat (length line) + 1 <= LMAX + 2) by (unfold LMAX in *; lia).
assert (Hl1 : Z.of_nat (length (dec id)) <= LMAX) by (unfold LMAX; lia).
assert (Hl2 : Z.of_nat (length (canon line)) <= LMAX) by (unfold LMAX in *; lia).
assert (NEW1 : In (p1, Z.of_nat (length (dec id)) + 1) O \/ ~ In (p1, Z.of_nat (length (dec id)) + 1) (ablocks B ly S)).
{ destruct (in_dec sc_b_pdec (p1, Z.of_nat (length (dec id)) + 1) O) as [H|H]; [left; exact H | right; intros Hin].
  pose proof (proj1 (Forall_forall _ _) Hfresh1 _ (HLc _ Hin H)) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap.
  lia. }
assert (NEW2 : In (p2, Z.of_nat (length line) + 1) O \/ ~ In (p2, Z.of_nat (length line) + 1) (ablocks B ly S)).
{ destruct (in_dec sc_b_pdec (p2, Z.of_nat (length line) + 1) O) as [H|H]; [left; exact H | right; intros Hin].
  pose proof (proj1 (Forall_forall _ _) Hfresh2 _ (Hsub12 _ (HLc _ Hin H))) as Hap. unfold iv_apart in Hap.
  cbn [fst snd] in Hap. lia. }
(* the registers at answer's entry *)
assert (R3' : getr regsc (Z_to_bv 5 3) = getr regs (Z_to_bv 5 3))
  by (replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact R3).
assert (R4' : getr regsc (Z_to_bv 5 4) = getr regs (Z_to_bv 5 4))
  by (replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact R4).
assert (HPT : aregs_preserved regs (ms_regs ms3)).
{ unfold aregs_preserved. intros r Hr. unfold acallee_saved in Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by lia.
  clear Hr. repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases].
  all: rewrite (st_ok_restrict_reg SEGS (w_H W3) E3 _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
      let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
  all: first
    [ rewrite U23; replace (spZ regsc + 48) with (spZ regs) by lia; unfold spZ;
      replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity); apply Z_to_bv_bv_unsigned
    | rewrite Es00; apply Z_to_bv_bv_unsigned
    | rewrite Es10; apply Z_to_bv_bv_unsigned
    | rewrite Es20; apply Z_to_bv_bv_unsigned
    | rewrite Es30; apply Z_to_bv_bv_unsigned
    | lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) =>
        rewrite (OLD3 n), (OLD2 n) by lia; rewrite (EE n (Z_to_bv 5 rr) eq_refl);
        first [ exact R3' | exact R4' | apply Rhi; lia ] end ]. }
assert (HPT1 : getr (ms_regs ms3) 1 = getr regs 1).
{ rewrite (st_ok_restrict_reg SEGS (w_H W3) E3 _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
    let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]. rewrite Era0.
  replace (1%bv : bv 5) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity). apply Z_to_bv_bv_unsigned. }
assert (Hsp3 : spZ (ms_regs ms3) = spZ regs).
{ unfold spZ. pose proof (HPT 2 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. reflexivity. }
assert (Hs03 : s0Z (ms_regs ms3) = s0Z regs).
{ unfold s0Z. pose proof (HPT 8 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 8) with (8%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. reflexivity. }
assert (Hgp3 : getr (ms_regs ms3) 3 = w64 (as_gp B)).
{ pose proof (HPT 3 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 3) with (3%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact Hgp. }
assert (Htp3 : getr (ms_regs ms3) 4 = w64 (as_tp B)).
{ pose proof (HPT 4 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 4) with (4%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. exact Htp. }
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
assert (H103 : getr (ms_regs ms3) 10 = w64 c)
  by (rewrite T10, OLD3, OLD2 by lia; rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (H113 : getr (ms_regs ms3) 11 = w64 0x21ce0).
{ rewrite T11. apply bv_eq. rewrite (HEI3 283%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  change (VAL 283%nat) with (VAL (A_OBJ 42)). rewrite (sc_obj42 VOBJS). rewrite unsigned_lit_small by lia. reflexivity. }
assert (H123 : getr (ms_regs ms3) 12 = w64 1) by (rewrite T12; reflexivity).
assert (HFPhi : forall a, alloc_ceiling <= a -> ~ inFP (SC_FP O) a).
{ intros a Ha Hin. destruct (sc_b_fp_cases O a Hin) as [Hpg | Hb].
  - pose proof (sc_b_pg_range a Hpg) as Hr. unfold A_G_REC, A_G_QUITTING in Hr. lia.
  - destruct (inFP_ablocks_fp_inv _ a Hb) as (q & m & Hqm & Hr).
    destruct (al_blocks _ _ LAWS ly S W mem md q m HAR (HOin _ Hqm)) as (_ & _ & Hqc & _). lia. }
assert (HCH3 : achain ly3 (rdW W3 (ms_mem ms3)) (spZ (ms_regs ms3)) (s0Z (ms_regs ms3)) ch).
{ rewrite Hsp3, Hs03. pose proof HJ3 as (_ & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _).
  apply (achain_ly_top ly ly3); [exact ET|].
  apply (achain_kept ly (rdW W mem) (rdW W3 (ms_mem ms3)) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. exact (aview_above_of_journal B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [] ly3 S3 W3
    (ms_mem ms3) mdv3 _ HJ3 a Ha (HFPhi a ltac:(lia))). }
assert (HFR3 : frames S3 = frames S).
{ pose proof HJ2c as (_ & _ & _ & _ & _ & Hf2 & _). pose proof HJ3c as (_ & _ & _ & _ & _ & Hf3 & _).
  rewrite Hf3, Hf2, Hfrc. reflexivity. }
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms3)))
  by exact (sc_b_arod SUP_CALL_STK (spZ regs) O ly S W mem md [] ly3 S3 W3 (ms_mem ms3) mdv3 _ HAR HOin HOpos HJ3 HROD).
(* answer's contract at its entry gives the post: the tail's statement at fx1, its apost_baseF at fx1 lifted to the
   entry's fx by fxrel fx fx1 *)
assert (TAILK : forall Ot, rec_repA B ly3 S3 (rdW W3 (ms_mem ms3)) (rec_record R REC_CALL (sc_args id line)) Ot ->
  (forall pn, In pn Ot -> In pn O \/ ~ In pn (ablocks B ly S)) ->
  (forall pn, In pn (ablocks B ly3 S3) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn Ot) ->
  SRr SEGS W3 (mkCfg (@mkst fx1 (ms_regs ms3) (Z_to_bv 64 (BASE + AF_answer)) (ms_mem ms3) (seg_rom SEGS)) mdv3)
    (sc_post (fx := fx) B MT ly S W regs mem md id line R O t)).
{ intros Ot HREP5 HOt1 HOt2.
  unfold sc_post. apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
  apply (SCT fx1 ly S W regs mem md ch id pl line R O ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) mdv3
    (k + EV_ARG_I + EV_ARG_LINE) c Ot HPRE1).
  unfold sc_tail.
  split; [exact HJ3|].
  split; [unfold EV_SC_ARGS, EV_ARG_I, EV_ARG_LINE, EV_XSTRDUP, EV_REC_CANONICAL; lia|].
  split; [exact Hsp3|]. split; [exact HPT1|]. split; [exact HPT|].
  split; [exact Hgp3|]. split; [exact Htp3|].
  split; [exact H103|]. split; [exact H113|]. split; [exact H123|].
  split; [exact HCH3|]. split; [exact Hcarm|]. split; [exact HREP5|].
  split; [exact HOt1|]. split; [exact HOt2|].
  split; [intros pn H1 H2; exact (Hsub23 _ (Hsub12 _ (HLc _ H1 H2)))|].
  split; [exact HFR3|].
  split; [lia|].
  split; [unfold XM_SC_ARGS; exact (mle_station MT S S2 S3 _ _ MTL HMLE2 Hmle3)|].
  split; [exact HROD5 | exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly3 S3 W3 (ms_mem ms3) mdv3 (proj1 HJ3) HROD5)]. }
destruct HARM as [(Hlt & Hceq & Habl & Hnc & Fg & Fs & Fb) | (H16 & Hceq & Hbliff & Fg & Fb)].
- (* the table arm: the call went into g_rec's slot n *)
  assert (Hperm : Permutation (ablocks B ly3 S3)
    ((p2, Z.of_nat (length line) + 1) :: (p1, Z.of_nat (length (dec id)) + 1) :: ablocks B ly S)).
  { rewrite Habl in Hperm1. exact (perm_trans Hperm2 (perm_skip _ Hperm1)). }
  assert (Hap1 : Forall (fun qk => iv_apart p1 (Z.of_nat (length (dec id)) + 1) (fst qk) (snd qk)) (ablocks B ly S))
    by (rewrite <- Habl; exact Hfresh1).
  assert (Hap2 : Forall (fun qk => iv_apart p2 (Z.of_nat (length line) + 1) (fst qk) (snd qk))
    ((p1, Z.of_nat (length (dec id)) + 1) :: ablocks B ly S)).
  { apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) Hfresh2).
    rewrite Habl in Hperm1. exact (Permutation_in _ (Permutation_sym Hperm1) Hx). }
  assert (Hnc5 : aval_mem (rdW W3 (ms_mem ms3)) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1)).
  { apply (sc_aval_frame _ _ _ _ _ Hnc). intros x Hx. unfold A_G_REC, OFF_NCALLS in Hx.
    apply KSall; [apply sc_b_grec_pg; unfold A_G_REC, REC_SIZE; lia | lia]. }
  assert (Fg5 : forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
      ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + CALL_SIZE) ->
      rdW W3 (ms_mem ms3) a = rdW W mem a).
  { intros a H1 H2 H3. rewrite (KSall a (sc_b_grec_pg a H1) ltac:(unfold CALL_SIZE in H3; lia)). exact (Fg a H1 H2). }
  assert (Fs5 : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rdW W3 (ms_mem ms3) a = rdW W mem a).
  { intros a H1. rewrite (KSall a (sc_b_spill_pg a H1)); [exact (Fs a H1)|].
    rewrite Hceq. unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL, SC_SIZE in *. lia. }
  assert (Fb5 : forall p m i, In (p, m) (ablocks B ly S) -> 0 <= i < m ->
      rdW W3 (ms_mem ms3) (p + i) = rdW W mem (p + i)).
  { intros p m i Hin Hi. rewrite (KBall p m (p + i) ltac:(rewrite Habl; exact Hin) ltac:(lia)). exact (Fb p m i Hin Hi). }
  subst c.
  destruct (sc_rep_slot B ly S (rdW W mem) ly3 S3 (rdW W3 (ms_mem ms3)) R Q O (dec id) (canon line) p1 p2
    (Z.of_nat (length (dec id)) + 1) (Z.of_nat (length line) + 1) HQ HOQ Hlt Hperm Hap1 Hap2 Hg1 Hs1 Hg2 Hs2
    ltac:(lia) ltac:(lia) En1 En2 Hl1 Hl2 Hnc5 Hfn5 Hna5 Ha05 Ha15 Hs15 Hs25 Fg5 Fs5 Fb5) as (O' & HREP5 & HO').
  apply (TAILK O' HREP5).
  + intros pn Hpn. apply HO' in Hpn. destruct Hpn as [H | [-> | ->]]; [left; exact H | exact NEW1 | exact NEW2].
  + intros pn Hpn. apply (Permutation_in _ Hperm) in Hpn.
    destruct Hpn as [<- | [<- | Hpn]];
      [right; apply HO'; right; right; reflexivity | right; apply HO'; right; left; reflexivity |].
    destruct (in_dec sc_b_pdec pn O) as [H|H]; [right; apply HO'; left; exact H | left; split; assumption].
- (* the spill arm: rec_calls_free emptied record.spill, which holds the call *)
  subst c.
  assert (Hbl : forall pn, In pn (ablocks B ly3 S3) <->
     ((In pn (ablocks B ly S) /\ ~ In pn (l_spill Q)) \/ pn = (p1, Z.of_nat (length (dec id)) + 1) \/
      pn = (p2, Z.of_nat (length line) + 1))).
  { intros pn. split.
    - intros Hin. apply (Permutation_in _ Hperm2) in Hin. destruct Hin as [<- | Hin]; [right; right; reflexivity|].
      apply (Permutation_in _ Hperm1) in Hin. destruct Hin as [<- | Hin]; [right; left; reflexivity|].
      left. exact (proj1 (Hbliff pn) Hin).
    - intros [Hin | [-> | ->]];
        [exact (Hsub23 _ (Hsub12 _ (proj2 (Hbliff pn) Hin))) | exact (Hsub23 _ HP1in2) | exact HP2in3]. }
  assert (Hap1 : forall qk, In qk (ablocks B ly S) -> ~ In qk (l_spill Q) ->
      iv_apart p1 (Z.of_nat (length (dec id)) + 1) (fst qk) (snd qk))
    by (intros qk H1 H2; exact (proj1 (Forall_forall _ _) Hfresh1 qk (proj2 (Hbliff qk) (conj H1 H2)))).
  assert (Hap21 : iv_apart p2 (Z.of_nat (length line) + 1) p1 (Z.of_nat (length (dec id)) + 1))
    by exact (proj1 (Forall_forall _ _) Hfresh2 _ HP1in2).
  assert (Hap2 : forall qk, In qk (ablocks B ly S) -> ~ In qk (l_spill Q) ->
      iv_apart p2 (Z.of_nat (length line) + 1) (fst qk) (snd qk))
    by (intros qk H1 H2; exact (proj1 (Forall_forall _ _) Hfresh2 qk (Hsub12 _ (proj2 (Hbliff qk) (conj H1 H2))))).
  assert (Fg5 : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rdW W3 (ms_mem ms3) a = rdW W mem a).
  { intros a H1. rewrite (KSall a (sc_b_grec_pg a H1) ltac:(unfold A_G_REC, A_REC_SPILL, REC_SIZE in *; lia)).
    exact (Fg a H1). }
  assert (Fb5 : forall p m i, In (p, m) (ablocks B ly S) -> ~ In (p, m) (l_spill Q) -> 0 <= i < m ->
      rdW W3 (ms_mem ms3) (p + i) = rdW W mem (p + i)).
  { intros p m i Hin Hns Hi. rewrite (KBall p m (p + i) (proj2 (Hbliff (p, m)) (conj Hin Hns)) ltac:(lia)).
    exact (Fb p m i Hin Hns Hi). }
  destruct (sc_rep_spill B ly S (rdW W mem) ly3 S3 (rdW W3 (ms_mem ms3)) R Q O (dec id) (canon line) p1 p2
    (Z.of_nat (length (dec id)) + 1) (Z.of_nat (length line) + 1) HQ HOQ H16 Hbl Hap1 Hap21 Hap2 Hg1 Hs1 Hg2 Hs2
    ltac:(lia) ltac:(lia) En1 En2 Hl1 Hl2 Hfn5 Hna5 Ha05 Ha15 Hs15 Hs25 Fg5 Fb5) as (O' & HREP5 & HO').
  apply (TAILK O' HREP5).
  + intros pn Hpn. apply HO' in Hpn. destruct Hpn as [(H & _) | [-> | ->]]; [left; exact H | exact NEW1 | exact NEW2].
  + intros pn Hpn. apply Hbl in Hpn. destruct Hpn as [(Hin & Hns) | [-> | ->]];
      [| right; apply HO'; right; left; reflexivity | right; apply HO'; right; right; reflexivity].
    destruct (in_dec sc_b_pdec pn O) as [H|H]; [right; apply HO'; left; split; assumption | left; split; assumption].
Qed.

End e.
End f.
End w.

About sc_body.
Print Assumptions sc_body.
