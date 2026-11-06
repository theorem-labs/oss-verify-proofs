(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second segment of sup_chain's ASan walk (plugin-hostd/fuzz_command,
   0x8c2b4): from the join of record()'s two arms (0x8c34c) to the test that skips the loop (0x8c3c4), in the
   continuation style of lib/A/Prog/sup_chain.v's sc_segA_table, after lib/A/Prog/sup_chain_clear_s2.v's scc_join
   (the join seed and the arg_i call) and lib/A/Prog/socket_send.v (the malloc wrapper's call). *)
(* Modified by Theorem Labs, 2026-10: re-fitted to statement passes 4, 4b and 5: no
   astack_pres premise, rounding mode 0 at the entry, the callee and runtime contracts taken at every FP state.
   arg_i reaches the snprintf wrapper, so both calls go through PaFx.v's cl_callS_wideF and return at some fx1, fx2
   (fxrel fx fx1, fxrel fx1 fx2); the walk after each runs at the FP state it returned, the call site's symbolic
   state taken there by PaFx.v's st_ok_restrict_xfx. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaArt
PaLibF PaLibG PaLibH PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c xstrdup_c hand_back_c rec_shape_of_c answer_c sup_chain_c RecBLemmas sup_chain_s1
sup_chain_s2
sup_chain_s3 sup_chain PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the end of the segment: `blez s1` that skips the loop (0x8c3c4, MEASURED: the disassembly of sup_chain) *)
Definition SC_LOOP : Z := AF_sup_chain + 0x110.

(* a register's symbolic value without normalising the denotation (sup_chain.v's preg, copied: a Local Ltac of
   another file's closed Section is out of reach here) *)
Ltac scb_preg HS r Hr :=
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

(* the symbolic state at the join: register atoms; s0 (atom 8) holds the slot, s6 (atom 22) the shadow base; the
   atoms 32 .. 44 hold the entry values of the 13 registers the prologue saved, in sc_saved's order, and the
   frame's chunks name them *)
Definition scb_fchunk (j : nat) : YP09.chunk := YP09.mkChunk (104 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)).
Definition scb_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0 (map scb_fchunk (seq 0 13)).
Definition scb_slot : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 0 8 [].
(* the text block's first byte, which the store list[0] := 0 writes *)
Definition scb_txt : YP09.region := YP09.mkRegion (Some 49%nat) 0 1 0 1 [].

(* the i-th region of the symbolic state, read off HS *)
Ltac scb_region HS E i W Hr :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth i (ss_mem ssx) scb_slot) in
  pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) i r HS ltac:(vm_compute; reflexivity)) as Hr;
  cbn [ms_mem restrict mkst] in Hr
| st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth i (ss_mem ssx) scb_slot) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) i r HS ltac:(vm_compute; reflexivity)) as Hr;
  cbn [ms_mem restrict mkst] in Hr
end.
Definition scb_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (22%nat, mkAF SB SB 0)] [] [].
Definition ss_scb : sstate := mkSS SC_JOIN sr_atoms [scb_frame; scb_slot] None scb_facts.
Definition scb_Bx : sv := SOff 22 0.
Definition scb_SH : list shent := [mkSHE 8 0 CALL_SIZE].
Definition scb_xs (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 r)) sc_saved.

(* the call record()'s slot takes: the table's next entry, or record.spill *)
Definition sc_k (R : rstate) : option nat :=
if Nat.ltb (length (r_calls R)) 16 then Some (length (r_calls R)) else None.
(* the recorder after record(REC_CHAIN) and the two numbers arg_i adds *)
Definition sc_R2 (R : rstate) (id n : Z) : rstate :=
sc_push_arg (sc_push_arg (rec_record R REC_CHAIN []) (sc_k R) (dec id)) (sc_k R) (dec n).

Lemma sc_target_rec0 : forall R fn c,
((length (r_calls R) < 16)%nat /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R))) \/
((length (r_calls R) = 16)%nat /\ c = A_REC_SPILL) ->
sc_target (rec_record R fn []) (sc_k R) (fn, []) c.
Proof.
intros R fn c [(Hlt & ->) | (Heq & ->)]; unfold sc_k, rec_record.
- assert (Hb : Nat.ltb (length (r_calls R)) 16 = true) by (apply Nat.ltb_lt; exact Hlt).
  rewrite Hb. cbn [sc_target]. split; [|reflexivity].
  unfold set_calls. cbn [r_calls]. apply sc_nth_last.
- rewrite Heq. cbn [Nat.ltb Nat.leb sc_target]. split; reflexivity.
Qed.

Lemma sc_target_push : forall R k e c s,
sc_target R k e c -> sc_target (sc_push_arg R k s) k (fst e, snd e ++ [s]) c.
Proof.
intros R k e c s HT. destruct k as [i|]; cbn [sc_target sc_push_arg] in *; destruct HT as [H1 H2].
- split; [|exact H2]. unfold set_calls. cbn [r_calls]. rewrite sc_upd_nth_eq, H1. reflexivity.
- split; [|exact H2]. unfold set_spill. cbn [r_spill]. rewrite H1. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition scb_E (regsc regs : bvmap 5 word) : env := Eimg (Ereg regsc (scb_xs regs)).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's own hypotheses that this segment uses *)
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary record, as cgif's walks take it *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
(* the program's writable statics (the recorder walks' shared form) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the listing's symbol for a program callee is the callee's entry (CmdObj.v's cmd_sig_prog) *)
Hypothesis SIGP : cmd_sig_prog.
(* the read-only bytes across the calls (the recorder walks' shared forms): cmd_ro_ok from arodata_okP at any
   AR state, arodata_ok_journalP's two facts, and the read-only bytes outside the program's statics *)
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.

Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

Lemma scb_sig_arg_i : SIG CS_arg_i = BASE + AF_arg_i.
Proof. rewrite SIGP by (vm_compute; tauto). reflexivity. Qed.

Lemma scb_in_PG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
Exists (in_zr a) recb_PG.
Proof. intros a [Ha | Ha]; [exact (recb_grec_in a Ha) | exact (recb_spill_in a Ha)]. Qed.

Lemma scb_slot_in : forall c a, sc_slot_ok c -> c <= a < c + CALL_SIZE ->
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
Proof.
intros c a [(i & Hi & ->) | ->] Ha; unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Lemma scb_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> sc_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR [(i & Hi & ->) | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md SC_ZSH_REC _ CALL_SIZE HAR sc_zsh_rec_in
    ltac:(reflexivity) ltac:(reflexivity)); unfold SC_ZSH_REC, A_G_REC, OFF_CALLS, CALL_SIZE; cbn [fst snd]; lia.
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md SC_ZSH_SPILL _ CALL_SIZE HAR sc_zsh_spill_in
    ltac:(reflexivity) ltac:(reflexivity)); unfold SC_ZSH_SPILL, A_REC_SPILL, CALL_SIZE; cbn [fst snd]; lia.
Qed.

(* a write of the walk to g_rec or record.spill is one the footprint names *)
Lemma scb_awr_rec : forall STK sp0 O bl0 blc fr0 lyc own a,
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp0 (sc_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha.
right; right; right; right; left.
assert (HP : Exists (in_zr a) recb_PG) by exact (scb_in_PG a Ha).
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma scb_prog_fp : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
inFP (sc_FP O) a /\ Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof.
intros O a Ha. assert (HP : Exists (in_zr a) recb_PG) by exact (scb_in_PG a Ha).
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

(* g_rec's and record.spill's bytes are none of the runtime's statics (HB's ts_owned) and not the errno cell *)
Lemma scb_rec_unowned : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB).
split.
- intros HE. apply Exists_exists in HE as ([lo m] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  assert (Hb1 : forallb (fun r => (0x5e3b00 <=? fst r) || (fst r + snd r <=? 0x5e3740)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  assert (Hb2 : forallb (fun r => (0x5e3c18 <=? fst r) || (fst r + snd r <=? 0x5e3be0)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb1 _ Hin) as Hq1. pose proof (proj1 (forallb_forall _ _) Hb2 _ Hin) as Hq2.
  cbn beta in Hq1, Hq2. cbn [fst snd] in Hq1, Hq2.
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha.
  apply Bool.orb_true_iff in Hq1 as [Hq1 | Hq1]; apply Z.leb_le in Hq1;
  apply Bool.orb_true_iff in Hq2 as [Hq2 | Hq2]; apply Z.leb_le in Hq2; lia.
- unfold TFIB_ERRNO, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
Qed.

(* a callee whose footprint misses a byte of g_rec / record.spill leaves it as it was (the journal's image clause) *)
Lemma scb_rec_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP1 ->
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
~ inFP FP1 a -> rdW W' mem' a = rdW Wc memc a.
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k a HJ Hsk Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (scb_rec_unowned a Ha) as [Ho He].
apply F3; [| exact Ho | exact He | exact (fp_spares_closed FP1 a Hsk Hn)].
apply cmd_prog_img. apply scb_in_PG. exact Ha.
Qed.

(* a live block's bytes: above the first page, below the allocator's ceiling, outside the image *)
Lemma scb_blk : forall ly S (W : world SEGS) mem md p m i, AR SEGS B ly S W mem md -> In (p, m) (ablocks B ly S) ->
0 <= i < req_size m -> 4096 <= p + i < alloc_ceiling /\ ~ in_img SEGS (p + i).
Proof.
intros ly S W mem md p m i HAR Hin Hi.
destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hin) as (_ & H4096 & Hc & _).
split; [lia|]. exact (blk_img SEGS B LAWS ly S W mem md p m (p + i) HAR Hin ltac:(lia)).
Qed.

(* a live block is apart from g_rec and record.spill *)
Lemma scb_blk_apart : forall ly S (W : world SEGS) mem md p m, AR SEGS B ly S W mem md -> In (p, m) (ablocks B ly S) ->
iv_apart p m A_G_REC REC_SIZE /\ iv_apart p m A_REC_SPILL SC_SIZE.
Proof.
intros ly S W mem md p m HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hnr).
pose proof (req_size_pos m ltac:(lia)) as [R1 R2].
assert (HI : forall a, p <= a < p + req_size m -> ~ in_img SEGS a)
  by (intros a Ha; apply (blk_img SEGS B LAWS ly S W mem md p m a HAR Hin); lia).
unfold iv_apart. split.
- destruct (Z.le_gt_cases (p + m) A_G_REC) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (A_G_REC + REC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (HI (Z.max p A_G_REC)); [lia|]. apply cmd_prog_img. apply scb_in_PG. left. unfold REC_SIZE in *. lia.
- destruct (Z.le_gt_cases (p + m) A_REC_SPILL) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (A_REC_SPILL + SC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (HI (Z.max p A_REC_SPILL)); [lia|]. apply cmd_prog_img. apply scb_in_PG. right. unfold SC_SIZE in *. lia.
Qed.

(* a block live across a callee whose footprint lies in g_rec / record.spill keeps its bytes *)
Lemma scb_blk_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k p m i,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
AR SEGS B lyc Sc Wc memc mdc ->
(forall a, inFP FP1 a -> A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
In (p, m) (ablocks B lyc Sc) -> In (p, m) (ablocks B ly' S') -> 0 <= i < m ->
rdW W' mem' (p + i) = rdW Wc memc (p + i).
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k p m i HJ HAR HFP Hin Hin' Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos m ltac:(lia)) as [R1 R2].
apply (F2 p m i); [exact Hin | exact Hin' | lia |].
intros Hf. apply HFP in Hf.
apply (blk_img SEGS B LAWS lyc Sc Wc memc mdc p m (p + i) HAR Hin); [lia|].
apply cmd_prog_img. apply scb_in_PG. exact Hf.
Qed.

(* the malloc wrapper's acall_kept keeps g_rec and record.spill, and every block that was live *)
Lemma scb_malloc_rec : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop) a,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
rdW W2 mem2 a = rdW W memc a.
Proof.
intros lyc Sc W memc W2 mem2 slo shi Er a (_ & _ & K3 & _) Ha. destruct (scb_rec_unowned a Ha) as (H2 & H3).
exact (K3 a (cmd_prog_img a (scb_in_PG a Ha)) H2 H3).
Qed.

Lemma scb_malloc_blk : forall lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi ly4 S4 mem4 md4 res m p q i,
AR SEGS B ly4 S4 W2 mem4 md4 -> ablocks B ly4 S4 = ablocks B lyc Sc ++ [(res, m)] ->
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi (fun a => res <= a < res + req_size m) ->
In (p, q) (ablocks B lyc Sc) -> 0 <= i < q -> rdW W2 mem2 (p + i) = rdW W memc (p + i).
Proof.
intros lyc Sc W memc W2 mem2 slo shi ly4 S4 mem4 md4 res m p q i HAR4 E4 (_ & K2 & _) Hin Hi.
pose proof (req_size_pos q ltac:(lia)) as [R1 R2].
apply (K2 p q i Hin ltac:(lia)).
pose proof (recb_fresh_disj_m B ly4 S4 W2 mem4 md4 (ablocks B lyc Sc) res m p q HAR4 E4 Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* no read-only byte is in the contract's footprint (arodata_ok_journalP's premise) *)
Lemma scb_ro_off : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (sc_FP O) a.
Proof.
intros ly S W mem md O HAR HOS a Hro (r & Hr & Ha).
destruct (cmd_ro_prog_apart a Hro) as [Himg Hnp].
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- apply Hnp. apply scb_in_PG. left. exact Ha.
- apply Hnp. apply scb_in_PG. right. exact Ha.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p m] & <- & Hin). cbn [fst snd] in Ha.
  exact (blk_img SEGS B LAWS ly S W mem md p m a HAR (HOS _ Hin) Ha Himg).
Qed.

(* the size the text block takes, 12n + 1, as the symbolic executor writes it *)
Lemma scb_den_size : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v <= 62 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit 12)) (SLit 1)) = Z_to_bv 64 (12 * v + 1).
Proof.
intros E m v Hm Hv.
assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x) by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
assert (Hmul : U E (SMd M_MUL (SOff m 0) (SLit 12)) = 12 * v).
{ change (SMd M_MUL (SOff m 0) (SLit 12)) with (mono m 12).
  rewrite mono_sound, Hm, unsigned_lit_small by lia. unfold M64. apply Z.mod_small. lia. }
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (U E (SAlu ALU_ADD (SMd M_MUL (SOff m 0) (SLit 12)) (SLit 1)) = 12 * v + 1).
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hmul, U_SLit, (ZC 1) by lia. apply ZC. lia.
Qed.

(* s7 := (s3 >> 3) + s6, the shadow byte of c + 4 *)
Lemma scb_den_s7 : forall E c, ew E 8 = Z_to_bv 64 c -> ew E 22 = Z_to_bv 64 SB -> 0 <= c < 2 ^ 60 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 4) (SLit 3)) (SOff 22 0)) = Z_to_bv 64 ((c + 4) / 8 + SB).
Proof.
intros E c H8 H22 Hc.
assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x) by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 4) (SLit 3)) (SOff 22 0)) = (c + 4) / 8 + SB).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, !U_SOff, H8, H22, !unsigned_lit_small by (unfold SB; lia).
rewrite (ZC 3) by lia. change (Z.land 3 63) with 3.
rewrite (ZC (c + 4)) by lia. rewrite (ZC (SB + 0)) by (unfold SB; lia).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (c + 4) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (ZC ((c + 4) / 8)) by lia. rewrite Z.add_0_r. apply ZC. unfold SB. lia.
Qed.

(* the frame the prologue wrote, read off the segment's frame region *)
Lemma scb_frame_of_region : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) cs,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) 0 112 0 0 cs) ->
bv_unsigned (ew E 2) = sp0 - 112 ->
(forall j r, nth_error sc_saved j = Some r -> ew E (32 + j) = getr regs (Z_to_bv 5 r)) ->
(forall j, (j < 13)%nat -> In (scb_fchunk j) cs) ->
sc_frame_at m sp0 regs.
Proof.
intros E m sp0 regs cs HR Hsp HE HIn j r Hj.
assert (Hj13 : (j < length sc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
change (length sc_saved) with 13%nat in Hj13.
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 - 112 + (104 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region E m 2%nat (sp0 - 112) cs 0 112 0 0 (104 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) _ HR Hsp
  (HIn j Hj13)).
- cbn [sv_denot]. rewrite (HE j r Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
  cbn. lia.
- cbn. lia.
Qed.

(* arg_i's footprint for the slot c with nargs = m (arg_i_c.v:89-91), and what the walk keeps of its post
   (arg_i_c.v:94-103, m < 6) *)
Definition scb_FPa (c m : Z) : list (Z * Z) :=
if m <? REC_ARGS_MAX
then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)]
else [].

Lemma scb_FPa_in : forall c m a, 0 <= m < REC_ARGS_MAX -> inFP (scb_FPa c m) a ->
c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4 \/ c + CALL_OFF_ARGS + 8 * m <= a < c + CALL_OFF_ARGS + 8 * m + 8.
Proof.
intros c m a Hm (r & Hr & Ha). unfold scb_FPa in Hr.
replace (m <? REC_ARGS_MAX) with true in Hr by (symmetry; apply Z.ltb_lt; lia).
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; [left | right]; exact Ha.
Qed.

Lemma scb_FPa_closed : forall c m, 0 <= c -> 0 <= m < REC_ARGS_MAX -> ~ YI16.sink_open_fp (scb_FPa c m).
Proof.
intros c m Hc Hm. apply sink_closed_pos. unfold scb_FPa.
replace (m <? REC_ARGS_MAX) with true by (symmetry; apply Z.ltb_lt; lia).
unfold CALL_OFF_NARGS, CALL_OFF_ARGS. repeat constructor; cbn [fst]; lia.
Qed.

Definition scb_Karg (lyc : alayout) (Sc : astate) (c v m : Z) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 blocks_bytes S' <= blocks_bytes Sc + LIVE_ARG_I v /\
 mo_le MT Sc S' (XM_ARG_I MT v) /\ exists p,
 4096 <= p < 2 ^ 64 /\ Permutation (ablocks B ly' S') ((p, Z.of_nat (length (dec v)) + 1) :: ablocks B lyc Sc) /\
 Forall (fun qk => iv_apart p (Z.of_nat (length (dec v)) + 1) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
 aval_mem (rdW W' mem') (c + CALL_OFF_NARGS) 4 (m + 1) /\ aval_mem (rdW W' mem') (c + CALL_OFF_ARGS + 8 * m) 8 p /\
 astr_atR (rdW W' mem') p (dec v).

(* the call arg_i(c, v) from this function's frame at the FP state fxc: arg_i's contract (at fxc) through the kit's
   cl_callS_wideF; arg_i reaches the snprintf wrapper, so it returns at some fx1 with fxrel fxc fx1 *)
Lemma scb_arg_i_call : forall (fxc : YK11.FPState) W (regsT : bvmap 5 word) memT sp0 ly S W0 mem md lyc Sc mdc kk O
c v m raw,
ajournal SEGS B SUP_CHAIN_STK sp0 (sc_FP O) ly S W0 mem md [] lyc Sc W memT mdc kk ->
AR SEGS B ly S W0 mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
frm0 fxc -> alloc_ceiling + SUP_CHAIN_STK <= sp0 ->
arodata_okP SEGS RLO RHI B (rdW W0 mem) -> Z.of_nat (length (frames S)) <= 8 ->
spZ regsT = sp0 - 112 -> 16640 <= SUP_CHAIN_STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
getr regsT 8 = w64 c -> getr regsT 10 = w64 c -> getr regsT 11 = w64 v -> -2 ^ 31 <= v < 2 ^ 31 ->
sc_slot_ok c -> aval_mem (rdW W memT) (c + CALL_OFF_NARGS) 4 m -> 0 <= m < REC_ARGS_MAX ->
st_nev Sc + EV_ARG_I <= EV_MAX -> blocks_bytes Sc + LIVE_ARG_I v <= LIVE_MAX -> mo_ok MT Sc (XM_ARG_I MT v) ->
SRr SEGS W (mkCfg (@mkst fxc regsT (Z_to_bv 64 (BASE + AF_arg_i)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fxc fx1 /\
 c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal SEGS B SUP_CHAIN_STK sp0 (sc_FP O) ly S W0 mem md [] ly2 S2 W2 mem2 md2 (kk + EV_ARG_I) /\
 ajournal SEGS B ARG_I_STK (sp0 + -112) (scb_FPa c m) lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 EV_ARG_I /\
 aregs_preserved regsT regs2 /\ scb_Karg lyc Sc c v m ly2 S2 W2 regs2 mem2 md2).
Proof.
intros fxc W regsT memT sp0 ly S W0 mem md lyc Sc mdc kk O c v m raw HJ HAR HOS HFRM HCEIL HROD HFR Hsp WS H3 H4 H1
  Hraw Hraw4 H8 H10 H11 Hv Hc Hna Hm HEV HLIVE HMOK.
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof (sc_slot_bounds c Hc) as (Hc1 & Hc2 & Hc8).
pose proof asan_consts as (C1 & _).
pose proof (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
  (scb_ro_off ly S W0 mem md O HAR HOS) HROD) as HRODc.
pose proof (cmd_ro_ok_of_aro lyc Sc W memT mdc HARc HRODc) as HROc.
assert (HFRc : Z.of_nat (length (frames Sc)) <= 8) by (rewrite Hfrs; exact HFR).
assert (HFPr : forall a, inFP (scb_FPa c m) a ->
  A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
{ intros a Ha. pose proof (scb_FPa_in c m a Hm Ha) as Hca.
  apply (scb_slot_in c); [exact Hc|]. unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE, REC_ARGS_MAX in *. lia. }
eapply (cl_callS_wideF (fx := fxc) (PI := PI) B LAWS W regsT memT _ SUP_CHAIN_STK sp0 (sc_FP O) ly S W0 mem md [] lyc Sc mdc kk
  ARG_I_STK (scb_FPa c m) EV_ARG_I (-112) raw [] (scb_Karg lyc Sc c v m) HJ).
- rewrite Hsp. lia.
- reflexivity.
- lia.
- unfold ARG_I_STK, XSTRDUP_STK, ESTACK, ASTACK. lia.
- unfold ARG_I_STK, XSTRDUP_STK, ESTACK, ASTACK. lia.
- exact H3.
- exact H4.
- exact H1.
- exact Hraw.
- exact Hraw4.
- apply achain_low. unfold s0Z. rewrite H8. unfold w64.
  rewrite unsigned_lit_small by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
  unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
- intros HPRE1. eapply SRr_mono.
  + exact (TARG_I fxc lyc Sc W regsT memT mdc [] c v m HPRE1 HFRM HFRc HRODc HROc H10 H11 Hv Hc Hna
      ltac:(unfold REC_ARGS_MAX in *; lia) HEV HLIVE HMOK).
  + cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ2 & HP2 & HBB2 & HMLE2 & HCASE).
    exists fx2, ly2, S2, regs2, mem2, md2. split; [rewrite <- H1; reflexivity|]. split; [exact Hf1|].
    split; [exact Hf2|]. split; [exact HJ2|]. split; [exact HP2|].
    unfold scb_Karg. split; [exact HBB2|]. split; [exact HMLE2|].
    destruct HCASE as [(Hm6 & _) | (_ & p & Hp & Hperm & Hfresh & Hna2 & Hap & Hstr)];
      [unfold REC_ARGS_MAX in *; lia|].
    exists p. split; [exact Hp|]. split; [exact Hperm|]. split; [exact Hfresh|].
    split; [exact Hna2|]. split; [exact Hap | exact Hstr].
- intros a Ha. apply scb_awr_rec. exact (HFPr a Ha).
- intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFPr a Ha) as Hr.
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hr. lia.
Qed.

(* the seed of the segment: the frame with the saved registers, the slot, the slot's shadow *)
Lemma scb_seed : forall ly S (W : world SEGS) mem md (regsc regs : bvmap 5 word) c sp0,
AR SEGS B ly S W mem md ->
spZ regsc = sp0 - 112 -> 2 ^ 46 + 112 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
getr regsc 8 = w64 c -> sc_slot_ok c -> getr regsc 22 = w64 SB ->
sc_frame_at (mrestrict (w_H W) mem) sp0 regs ->
st_ok_pi SEGS VAL (scb_E regsc regs) ss_scb
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + SC_JOIN)) mem (seg_rom SEGS)))
/\ sh_ok SEGS scb_Bx scb_SH (scb_E regsc regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regsc regs c sp0 HAR Hsp Hsp0 Hsp16 H8 Hc H22 HFR.
assert (Hal : (sp0 - 112) mod 16 = 0).
{ apply Z.mod_divide in Hsp16 as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 16 - 112) with ((q - 7) * 16) by lia. apply Z_mod_mult. }
pose proof (sc_slot_bounds c Hc) as (Hc1 & Hc2 & Hc8).
set (E := scb_E regsc regs).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, scb_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j r, nth_error sc_saved j = Some r -> ew E (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj.
  assert (Hj13 : (j < length sc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length sc_saved) with 13%nat in Hj13.
  unfold E, scb_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  apply nth_error_nth. unfold scb_xs. rewrite nth_error_map, Hj. reflexivity. }
assert (E2 : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hsp).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EL 22%nat 22%bv eq_refl); exact H22).
assert (Hcz : 0 <= c < 2 ^ 64) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold E, scb_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold YP09.region_ok, scb_frame.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
      destruct (nth_error sc_saved j) as [r|] eqn:Ej;
        [| apply nth_error_None in Ej; change (length sc_saved) with 13%nat in Ej; lia].
      unfold scb_fchunk.
      apply (chunk_ok_val SEGS E _ (sp0 - 112) (104 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
        (bv_unsigned (getr regs (Z_to_bv 5 r)))).
      -- cbn [sv_denot]. rewrite (EX j r Ej), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hr.
         change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- cbn. lia.
      -- replace (sp0 - 112 + (104 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
         exact (HFR j r Ej).
    * unfold YP09.region_ok, scb_slot.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 8%nat c E8 Hcz).
      split; [lia|]. split; [unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia|]. split; [|constructor].
      intros o Ho. apply (cmd_prog_writable ly S W mem md (c + o) HAR). apply scb_in_PG.
      apply (scb_slot_in c); [exact Hc | unfold CALL_SIZE; lia].
  + apply pairwise_disjoint_of_extents.
    unfold scb_frame, scb_slot, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 8%nat c E8 Hcz). cbn [base_val]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. repeat split; lia.
  + unfold scb_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I | exact I]].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E22. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold CALL_SIZE, SC_SIZE in Hc2.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold sh_ok, scb_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E scb_Bx 8%nat c CALL_SIZE c 0 CALL_SIZE).
  + exact (scb_slot_addressable ly S W mem md c HAR Hc).
  + unfold scb_Bx, U. cbn [sv_denot]. rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by (unfold SB; lia).
    reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE in Hx. unfold SHADOW_OFF.
    unfold A_G_REC, A_REC_SPILL, OFF_CALLS, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the recorder at a memory that agrees on g_rec, record.spill and the recorder's blocks (sup_chain.v
   sc_arep_kept_all, over rec_repA) *)
Lemma scb_rep_kept : forall ly S rd rd' R O, rec_repA B ly S rd R O ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall q m i, In (q, m) O -> 0 <= i < m -> rd' (q + i) = rd (q + i)) ->
rec_repA B ly S rd' R O.
Proof.
intros ly S rd rd' R O (Qr & HQ & HO) HG KB. exists Qr. split; [|exact HO].
eapply sc_arep_kept_all; [exact HQ | | |].
- intros i Hi. apply HG. left. lia.
- intros i Hi. apply HG. right. lia.
- intros [q m] Hpn i Hi. cbn [fst snd] in Hi |- *. exact (KB q m i (proj2 (HO (q, m)) Hpn) Hi).
Qed.

(* --- segment B: the join (0x8c34c) .. the loop's skip test (0x8c3c4) -----------------------------------------
   The two checked stores c->fn := REC_CHAIN and c->nargs := 0, the text block of 12n + 1 bytes from the malloc
   wrapper (its null test cannot fire), arg_i(c, id), arg_i(c, n), and the checked store list[0] := 0. *)
Lemma sc_segB : forall ly S W regs mem md ch (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z))
lyc Sc Wc (regsc : bvmap 5 word) memc mdc k c (Q : world SEGS -> config -> Prop),
(* the entry: the statement's premises this segment uses *)
afn_pre SEGS B SUP_CHAIN_STK ly S W regs mem md ch ->
frm0 fx ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
-2 ^ 31 <= id < 2 ^ 31 ->
(1 <= length ids <= 62)%nat ->
rec_repA B ly S (rdW W mem) R O ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_CHAIN R <= EV_MAX -> blocks_bytes S + LIVE_SUP_CHAIN R id ids <= LIVE_MAX ->
mo_ok MT S (XM_SUP_CHAIN MT R id ids) ->
(* the join: what sc_segA_table's continuation KJ gives *)
ajournal SEGS B SUP_CHAIN_STK (spZ regs) (sc_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
k <= rec_spill_frees R ->
spZ regsc = spZ regs - 112 ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 c -> getr regsc 22 = w64 SB ->
getr regsc 9 = w64 (Z.of_nat (length ids)) -> getr regsc 18 = w64 pids -> getr regsc 21 = w64 id ->
sc_frame_at (mrestrict (w_H Wc) memc) (spZ regs) regs ->
sc_slot_ok c ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
blocks_bytes Sc <= blocks_bytes S ->
(((length (r_calls R) < 16)%nat /\ lyc = ly /\ Sc = S /\ k = 0 /\
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat (length (r_calls R)) /\
  aval_mem (rdW Wc memc) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls R)) + 1) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
     ~ (spZ regs - SUP_CHAIN_STK <= a < spZ regs) -> rdW Wc memc a = rdW W mem a)) \/
 ((length (r_calls R) = 16)%nat /\ c = A_REC_SPILL /\
  (exists O1, rec_repA B lyc Sc (rdW Wc memc) (set_spill R (fst (r_spill R), [])) O1 /\
     (forall pn, In pn O1 -> In pn O) /\
     (forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) /\
     (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) /\
     (forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1)))) ->
(* the continuation at the loop's skip test, at the FP state fx' the second arg_i returned *)
(forall (fx' : YK11.FPState) ly' S' W' (regs' : bvmap 5 word) mem' md' (lst p1 p2 : Z) (O1 : list (Z * Z)),
 fxrel fx fx' ->
 ajournal SEGS B SUP_CHAIN_STK (spZ regs) (sc_FP O) ly S W mem md [] ly' S' W' mem' md' (k + 1 + EV_ARG_I + EV_ARG_I) ->
 spZ regs' = spZ regs - 112 ->
 getr regs' 3 = w64 (as_gp B) -> getr regs' 4 = w64 (as_tp B) ->
 getr regs' 8 = w64 c -> getr regs' 9 = w64 (Z.of_nat (length ids)) -> getr regs' 18 = w64 pids ->
 getr regs' 19 = w64 (c + 4) -> getr regs' 20 = w64 lst -> getr regs' 21 = w64 id ->
 getr regs' 22 = w64 SB -> getr regs' 23 = w64 ((c + 4) / 8 + SB) ->
 sc_frame_at (mrestrict (w_H W') mem') (spZ regs) regs ->
 (* the text block: the malloc wrapper's block of 12n + 1 bytes, its first byte 0 *)
 4096 <= lst ->
 Permutation (ablocks B ly' S')
   ((p2, Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1) :: (p1, Z.of_nat (length (dec id)) + 1) ::
    ablocks B lyc Sc ++ [(lst, 12 * Z.of_nat (length ids) + 1)]) ->
 rdW W' mem' lst = Some 0 ->
 (* the recorder: record()'s slot c holds REC_CHAIN with the two numbers; it owns the two copies arg_i made *)
 (forall pn, In pn O1 -> In pn O) ->
 (forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) ->
 (forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1) ->
 sc_target (sc_R2 R id (Z.of_nat (length ids))) (sc_k R) (REC_CHAIN, [dec id; dec (Z.of_nat (length ids))]) c ->
 rec_repA B ly' S' (rdW W' mem') (sc_R2 R id (Z.of_nat (length ids)))
   (O1 ++ [(p1, Z.of_nat (length (dec id)) + 1); (p2, Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1)]) ->
 mo_le MT S S' (rec_spill_frees R * mo_free MT + mo_malloc MT (12 * Z.of_nat (length ids) + 1) +
   XM_ARG_I MT id + XM_ARG_I MT (Z.of_nat (length ids))) ->
 SRr SEGS W' (@cfg_at fx' SEGS (BASE + SC_LOOP) regs' mem' md') Q) ->
SRr SEGS Wc (cfg_at SEGS (BASE + SC_JOIN) regsc memc mdc) Q.
Proof.
intros ly S W regs mem md ch id pids ids R O lyc Sc Wc regsc memc mdc k c Q
  HPRE HFRM HROD Hid Hlen HREP HFR HEV HLIVE HMOK HJ Hk Hspc H3 H4 H8 H22 H9 H18 H21 HFRc Hc HMLE Hbb HARM K.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (WS : 16640 <= SUP_CHAIN_STK) by (vm_compute; discriminate).
set (sp0 := spZ regs) in *.
set (n := Z.of_nat (length ids)) in *.
assert (Hn1 : 1 <= n <= 62) by (unfold n; lia).
pose proof (sc_slot_bounds c Hc) as (Hc1 & Hc2 & Hc8).
assert (Hcz : 0 <= c < 2 ^ 64) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
pose proof (proj1 HJ) as HARc.
assert (Hsp46 : 2 ^ 46 + 112 <= sp0 <= 2 ^ 47) by lia.
destruct (scb_seed lyc Sc Wc memc mdc regsc regs c sp0 HARc Hspc Hsp46 Hsp16 H8 Hc H22 HFRc) as [HS SHOK].
set (E := scb_E regsc regs) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, scb_E; apply Eimg_env).
assert (EL : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsc r).
{ intros m r Hm. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, scb_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j r, nth_error sc_saved j = Some r -> ew E (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj.
  assert (Hj13 : (j < length sc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length sc_saved) with 13%nat in Hj13.
  unfold E, scb_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  apply nth_error_nth. unfold scb_xs. rewrite nth_error_map, Hj. reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hspc).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EL 3%nat 3%bv eq_refl); exact H3).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EL 4%nat 4%bv eq_refl); exact H4).
assert (E8 : ew E 8 = w64 c) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = w64 n) by (rewrite (EL 9%nat 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = w64 pids) by (rewrite (EL 18%nat 18%bv eq_refl); exact H18).
assert (E21 : ew E 21 = w64 id) by (rewrite (EL 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = w64 SB) by (rewrite (EL 22%nat 22%bv eq_refl); exact H22).
assert (E1 : ew E 1 = getr regsc 1) by exact (EL 1%nat 1%bv eq_refl).
clearbody E.
unfold cfg_at, w64.
(* 0x8c34c .. 0x8c38c: the two checked stores to the slot, a0 := 12n + 1, the call of the malloc wrapper *)
paj_run_tok RUN HS HJ SHOK SC_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen (segs := SEGS) B) with (n := 8%nat);
    [reflexivity | rewrite E8; unfold w64; exact (unsigned_lit_small c Hcz) | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply scb_awr_rec.
  apply (scb_slot_in c); [exact Hc | unfold CALL_SIZE; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (19%bv : bv 5) P19.
scb_preg HS (10%bv : bv 5) P10. scb_preg HS (23%bv : bv 5) P23.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgA := rg) in *; set (mA := mm) in *; set (mdA := mdq) in *
end.
clearbody mdA.
assert (Uc : bv_unsigned (ew E 8) = c) by (rewrite E8; unfold w64; exact (unsigned_lit_small c Hcz)).
(* the two stores: c->fn = 17, c->nargs = 0; nothing else changed *)
lazymatch type of HS with
| st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 1 (ss_mem ssx) scb_slot) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRg;
  cbn [ms_mem restrict mkst] in HRg
end.
pose proof (field_of_region (segs := SEGS) E _ 8 c _ _ _ _ _ 0 4 (SLit 17) 17 HRg Uc ltac:(cbn; tauto)
  ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfn.
pose proof (field_of_region (segs := SEGS) E _ 8 c _ _ _ _ _ 4 4 (SLit 0) 0 HRg Uc ltac:(cbn; tauto)
  ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vna.
clear HRg. rewrite Z.add_0_r in Vfn.
change (N.to_nat 4) with 4%nat in Vfn, Vna.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ memc) (mrestrict _ mA) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc mA (fun a => c <= a < c + 8) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Uc in Hrr; lia|]);
          destruct Hin)) as UN1
end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pose proof HJ as HJ1.
(* the recorder after the two stores: record(REC_CHAIN) with no argument yet, on either arm *)
assert (HREC1 : exists O1, rec_repA B lyc Sc (rdW Wc mA) (rec_record R REC_CHAIN []) O1 /\
  (forall pn, In pn O1 -> In pn O) /\ (forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) /\
  sc_target (rec_record R REC_CHAIN []) (sc_k R) (REC_CHAIN, []) c /\
  (forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1) /\
  (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc))).
{ destruct HARM as [(Hlt & -> & -> & -> & Ec & Hnc & Hag) | (Heq & Ec & (O1 & HR1 & HO1 & HB1 & HnO1 & HOc1))].
  - exists O. split; [|split; [intros pn Hpn; exact Hpn|split; [|split; [|split]]]].
    + apply (scA_record_slot0_fr B ly S ly S (rdW W mem) (rdW Wc mA) R O c REC_CHAIN HREP Hlt Ec).
      * unfold REC_FN_COUNT, REC_CHAIN. lia.
      * intros pn Hpn. exact Hpn.
      * intros a Ha Hns Hnn.
        assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
        assert (Hns8 : ~ (c <= a < c + 8)) by (intros Hx; apply Hns; unfold CALL_SIZE; lia).
        rewrite (UN1 a Ha64 Hns8).
        apply (Hag a Ha64 Hnn). unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
      * intros p m i Hpm Hi.
        pose proof (scA_own_live B ly S _ R O HREP (p, m) Hpm) as Hin.
        destruct (scb_blk ly S W mem md p m i HAR Hin ltac:(pose proof (req_size_pos m ltac:(lia)); lia)) as (Hb & Hni).
        assert (Hpm_ : (forall x, c <= x < c + 8 \/ A_G_REC + OFF_NCALLS <= x < A_G_REC + OFF_NCALLS + 4 -> in_img SEGS x)).
        { intros x Hx. apply cmd_prog_img. apply scb_in_PG.
          destruct Hx as [Hx | Hx]; [apply (scb_slot_in c); [exact Hc | unfold CALL_SIZE; lia]|].
          left. cbv [OFF_NCALLS REC_SIZE] in Hx |- *. lia. }
        assert (Hnx1 : ~ (c <= p + i < c + 8)) by (intros Hx; exact (Hni (Hpm_ _ (or_introl Hx)))).
        assert (Hnx2 : ~ (A_G_REC + OFF_NCALLS <= p + i < A_G_REC + OFF_NCALLS + 4))
          by (intros Hx; exact (Hni (Hpm_ _ (or_intror Hx)))).
        rewrite (UN1 (p + i) ltac:(lia) Hnx1).
        apply Hag; [lia | exact Hnx2 | lia].
      * apply (sc3_aval_keep (rdW Wc memc)); [exact Hnc|].
        intros x Hx. try change (Z.of_nat 4) with 4 in Hx.
        assert (Hx64 : 0 <= x < 2 ^ 64) by (cbv [A_G_REC OFF_NCALLS] in Hx; lia).
        assert (Hxn : ~ (c <= x < c + 8)) by (rewrite Ec; cbv [A_G_REC OFF_CALLS OFF_NCALLS CALL_SIZE] in Hx |- *; lia).
        exact (UN1 x Hx64 Hxn).
      * unfold CALL_OFF_FN. rewrite Z.add_0_r. exact (aval_mem_view SEGS (w_H Wc) mA c 4 17 Vfn).
      * exact (aval_mem_view SEGS (w_H Wc) mA (c + 4) 4 0 Vna).
    + exact (scA_own_live B ly S _ R O HREP).
    + apply sc_target_rec0. left. split; [exact Hlt | exact Ec].
    + intros pn Hpn _. exact Hpn.
    + intros pn Hpn _. exact Hpn.
  - exists O1. split; [|split; [exact HO1|split; [|split; [|split]]]].
    + rewrite (rec_record_spill R REC_CHAIN [] Heq).
      apply (scA_spill_fn B lyc Sc (rdW Wc memc) (rdW Wc mA) R O1 (fst (r_spill R)) REC_CHAIN HR1).
      * unfold REC_FN_COUNT, REC_CHAIN. lia.
      * rewrite <- Ec. unfold CALL_OFF_FN. rewrite Z.add_0_r. exact (aval_mem_view SEGS (w_H Wc) mA c 4 17 Vfn).
      * rewrite <- Ec. exact (aval_mem_view SEGS (w_H Wc) mA (c + 4) 4 0 Vna).
      * intros a Ha Hnx2.
        assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
        assert (Hn8 : ~ (c <= a < c + 8)) by (rewrite Ec; cbv [CALL_OFF_FN CALL_OFF_NARGS] in Hnx2; lia).
        exact (UN1 a Ha64 Hn8).
      * intros q m i Hqm Hi.
        pose proof (scA_own_live B lyc Sc _ _ O1 HR1 (q, m) Hqm) as Hin.
        destruct (scb_blk lyc Sc Wc memc mdc q m i HARc Hin ltac:(pose proof (req_size_pos m ltac:(lia)); lia)) as (Hb & Hni).
        assert (Hn8 : ~ (c <= q + i < c + 8)).
        { intros Hx. apply Hni. apply cmd_prog_img. apply scb_in_PG.
          apply (scb_slot_in c); [exact Hc | cbv [CALL_SIZE]; lia]. }
        exact (UN1 (q + i) ltac:(lia) Hn8).
    + exact (scA_own_live B lyc Sc _ _ O1 HR1).
    + apply sc_target_rec0. right. split; [exact Heq | exact Ec].
    + exact HOc1.
    + exact HnO1. }
destruct HREC1 as (O1 & HREP1 & HO1O & HO1c & Htgt1 & HOcO1 & HnonO).
assert (HOS : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (scA_own_live B ly S _ R O HREP).
assert (HCEIL : alloc_ceiling + SUP_CHAIN_STK <= sp0) by lia.
assert (Hc60 : 0 <= c < 2 ^ 60) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
(* the meter and the bounds the three calls ask *)
assert (HX : 0 <= mo_malloc MT (12 * n + 1) /\ 0 <= XM_ARG_I MT id /\ 0 <= XM_ARG_I MT n /\
  0 <= XM_XSTRDUP MT (dec_list ids) /\ 0 <= mo_free MT /\ 0 <= XM_ANSWER MT (snd (sup_chain_m R id ids))).
{ unfold XM_ARG_I, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
  pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (12 * n + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec id)) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec n)) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec_list ids)) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1) ltac:(lia)). lia. }
assert (Hrsf : 0 <= rec_spill_frees R) by (unfold rec_spill_frees; destruct (Nat.ltb (length (r_calls R)) 16); lia).
assert (Hevc : EV_ARG_I = 1 /\ EV_XSTRDUP = 1 /\ EV_ANSWER = 3) by (repeat split; reflexivity).
assert (HEVs : st_nev S + rec_spill_frees R + 1 + EV_ARG_I + EV_ARG_I <= EV_MAX).
{ unfold EV_SUP_CHAIN in HEV. lia. }
assert (HLa : 0 <= LIVE_ARG_I id /\ 0 <= LIVE_ARG_I n) by (unfold LIVE_ARG_I, LIVE_XSTRDUP; lia).
assert (HLIVEs : blocks_bytes S + (12 * n + 1) + LIVE_ARG_I id + LIVE_ARG_I n <= LIVE_MAX).
{ assert (0 <= LIVE_XSTRDUP (dec_list ids)) by (unfold LIVE_XSTRDUP; lia).
  assert (0 <= LIVE_ANSWER (snd (sup_chain_m R id ids))) by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP; lia).
  unfold LIVE_SUP_CHAIN in HLIVE. fold n in HLIVE. lia. }
assert (HMOKs : mo_ok MT S (rec_spill_frees R * mo_free MT + mo_malloc MT (12 * n + 1) + XM_ARG_I MT id + XM_ARG_I MT n)).
{ apply (mo_ok_le MT MTL S _ (XM_SUP_CHAIN MT R id ids) HMOK). unfold XM_SUP_CHAIN. fold n. lia. }
pose proof HJ as (_ & _ & _ & _ & _ & Hfrc & Hnevc & _).
(* 0x8c38c: the malloc wrapper, size 12n + 1 *)
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT (AMALLOC4 fx) Wc rgA mA SUP_CHAIN_STK sp0 (sc_FP O) ly S W mem md []
    lyc Sc mdA k (12 * n + 1) (-112) (Z_to_bv 64 (BASE + 24236)) [] HJ).
  - rewrite P10. exact (scb_den_size E 9 n E9 ltac:(lia)).
  - unfold MALLOC_MAX. lia.
  - lia.
  - unfold spZ. rewrite P2, Usp. lia.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - rewrite P3. exact E3.
  - rewrite P4. exact E4.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia.
  - apply (achain_chain_pre lyc _ (spZ rgA) (s0Z rgA) [] rgA); [| unfold spZ; rewrite P2, Usp; lia | reflexivity |].
    + apply achain_low. unfold s0Z. rewrite P8, Uc. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
    + unfold raZ. rewrite P1, unsigned_lit_small by lia. lia.
  - apply (mok_station MT S Sc _ (rec_spill_frees R * mo_free MT) (mo_malloc MT (12 * n + 1)) MTL HMOKs HMLE); lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Ha04 & Hfr4 & Hres & Eab4 & HK4 & MLE4 & _).
pose proof (proj1 HJ4) as HAR4.
assert (Hres_in : In (res, 12 * n + 1) (ablocks B ly4 S4)) by (rewrite Eab4; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (12 * n + 1) HAR4 Hres_in) as (Hres16 & _ & Hresc & _ & Hrespres & _).
pose proof (req_size_pos (12 * n + 1) ltac:(lia)) as Hrq.
jafter_call_keep_pi HS 45%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_aj SEGS B); [exact HK4 | exact HJ4 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E 45 (map (getr regs4) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 45)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (Ea49 : ew Ea 49 = Z_to_bv 64 res) by (rewrite HEa; cbn [havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB]; exact Ha04).
clear HEa.
(* beqz a0 at 0x8c390: the block is not NULL, so the abort is not reached *)
assert (SHOKa : sh_ok SEGS scb_Bx [] Ea (mrestrict (w_H W4) mem4)) by (unfold sh_ok; apply Forall_nil).
psrr_branch_tok RUN BR HS SHOKa SC_Bspan.
{ exfalso. match goal with H : branch_taken _ _ _ = true |- _ => rename H into Hbr end.
  rewrite ?branch_eq_U, ?branch_ne_U in Hbr. rewrite (U_atom Ea 49 res Ea49 ltac:(lia)) in Hbr.
  change (U Ea (SLit 0)) with 0 in Hbr. apply Z.eqb_eq in Hbr. lia. }
(* 0x8c394 .. 0x8c3a0: s4 := the block, a0 := c, a1 := id, the call of arg_i *)
paj_run_tok RUN HS HJ4 SHOKa SC_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (20%bv : bv 5) Q20.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgB := rg) in *; set (mB := mm) in *; set (mdB := mdq) in *
end.
clearbody mdB.
lazymatch goal with Hfr : frame_of Ea _ (mrestrict _ mem4) (mrestrict _ mB) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) Ea _ (w_H W4) mem4 mB (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
          destruct Hin)) as UN2
end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pose proof (proj1 HJ4) as HAR4b.
pose proof HJ4 as (_ & _ & _ & _ & _ & Hfr4j & Hnev4 & _).
assert (Hbb4 : blocks_bytes S4 = blocks_bytes Sc + (12 * n + 1)).
{ rewrite (blocks_bytes_bsum B ly4 S4), (blocks_bytes_bsum B lyc Sc), Eab4, bsum_app.
  change (bsum [(res, 12 * n + 1)]) with (12 * n + 1 + 0). lia. }
assert (MLE_S4 : mo_le MT S S4 (rec_spill_frees R * mo_free MT + mo_malloc MT (12 * n + 1)))
  by exact (mle_station MT S Sc S4 _ _ MTL HMLE MLE4).
assert (Hna0 : aval_mem (rdW W4 mB) (c + CALL_OFF_NARGS) 4 0).
{ apply (sc3_aval_keep (rdW Wc mA)); [exact (aval_mem_view SEGS (w_H Wc) mA (c + 4) 4 0 Vna)|].
  intros x Hx. try change (Z.of_nat 4) with 4 in Hx. cbv [CALL_OFF_NARGS] in Hx.
  assert (Hxr : A_G_REC <= x < A_G_REC + REC_SIZE \/ A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE)
    by (apply (scb_slot_in c); [exact Hc | unfold CALL_SIZE; lia]).
  rewrite (UN2 x ltac:(unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hxr; lia) (fun z => z)).
  exact (scb_malloc_rec _ _ _ _ _ _ _ _ _ x HK4 Hxr). }
(* the call of arg_i(c, id), at the entry's FP state fx: it returns at some fx1 with fxrel fx fx1 *)
rewrite scb_sig_arg_i.
eapply SRr_bind.
{ apply (scb_arg_i_call fx W4 rgB mB sp0 ly S W mem md ly4 S4 mdB (k + 1) O c id 0 (getr rgB 1) HJ4 HAR HOS HFRM
    HCEIL HROD HFR).
  - unfold spZ. rewrite Q2, OLDa, Usp by lia. reflexivity.
  - exact WS.
  - rewrite Q3, OLDa by lia. exact E3.
  - rewrite Q4, OLDa by lia. exact E4.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite Q8, OLDa by lia. exact E8.
  - rewrite Q10, OLDa by lia. exact E8.
  - rewrite Q11, OLDa by lia. exact E21.
  - exact Hid.
  - exact Hc.
  - exact Hna0.
  - unfold REC_ARGS_MAX. lia.
  - lia.
  - rewrite Hbb4. lia.
  - apply (mok_station MT S S4 _ _ (XM_ARG_I MT id) MTL HMOKs MLE_S4); lia. }
cbv beta. intros W5 c5 Hwle5 (fx1 & ly5 & S5 & regs5 & mem5 & md5 & Hfx1 & -> & HJ5 & HJc5 & HP5 & HK5). rewrite Q1.
(* arg_i returned at fx1: the walk up to the second call runs at fx1 (the call site's symbolic state taken to fx1,
   the run at fx1) *)
pose proof (PaFx.st_ok_restrict_xfx fx fx1 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
pose proof (paj_run (fx := fx1) B LAWS) as RUN1.
jafter_call_keep_pi HS 61%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0]%nat HS5.
match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJc5 | exact HJ5 | rewrite OLDa by lia; exact Usp | lia | lia | lia | cbn; lia | cbn; lia |].
  intros a Ha Hf. pose proof (scb_FPa_in c 0 a ltac:(unfold REC_ARGS_MAX; lia) Hf) as Hx.
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
clear HS. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS5. rename HS5 into HS.
remember (havoc Ea 61 (map (getr regs5) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 61)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
(* the recorder after arg_i(c, id): the call holds (17, [dec id]), the recorder owns the copy of dec id *)
destruct HK5 as (HBB5 & MLE5 & p1 & Hp1 & Hperm5 & Hfresh5 & Hna5 & Hap5 & Hstr5).
set (n1 := Z.of_nat (length (dec id)) + 1) in *.
assert (Hdec1 : (1 <= length (dec id) <= 11)%nat) by exact (dec_length id Hid).
assert (Hn1b : 2 <= n1 <= 12) by (unfold n1; lia).
pose proof (proj1 HJc5) as HAR5.
assert (Hp1in : In (p1, n1) (ablocks B ly5 S5)) by (apply (Permutation_in _ (Permutation_sym Hperm5)); left; reflexivity).
assert (Hin45 : forall pn, In pn (ablocks B ly4 S4) -> In pn (ablocks B ly5 S5))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm5)); right; exact Hpn).
assert (HincC4 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly4 S4))
  by (intros pn Hpn; rewrite Eab4; apply in_or_app; left; exact Hpn).
assert (HFPa0 : forall a, inFP (scb_FPa c 0) a -> A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
{ intros a Ha. pose proof (scb_FPa_in c 0 a ltac:(unfold REC_ARGS_MAX; lia) Ha) as Hx.
  apply (scb_slot_in c); [exact Hc | unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia]. }
assert (Hp1O1 : ~ In p1 (map fst O1)).
{ intros Hq. apply in_map_iff in Hq as ([q kq] & Hqe & Hq). cbn [fst] in Hqe. subst q.
  pose proof (HincC4 _ (HO1c _ Hq)) as Hq4.
  pose proof (proj1 (Forall_forall _ _) Hfresh5 _ Hq4) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap.
  assert (Hk0 : kq <= 0) by lia.
  assert (Hne : (p1, kq) <> (p1, n1)) by (intros Hx; injection Hx as Hx; lia).
  pose proof (sep_blocks SEGS B LAWS ly5 S5 W5 mem5 md5 p1 kq p1 n1 HAR5 (Hin45 _ Hq4) Hp1in Hne) as Hd.
  destruct (al_blocks _ _ LAWS ly5 S5 W5 mem5 md5 p1 kq HAR5 (Hin45 _ Hq4)) as (_ & _ & _ & _ & _ & _ & Hkr).
  pose proof (req_size_pos kq ltac:(lia)) as [Rk _]. pose proof (req_size_pos n1 ltac:(lia)) as [Rn _].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HREP2 : rec_repA B ly5 S5 (rdW W5 mem5) (sc_push_arg (rec_record R REC_CHAIN []) (sc_k R) (dec id))
  (O1 ++ [(p1, n1)])).
{ apply (scA_push_arg B lyc Sc ly5 S5 (rdW Wc mA) (rdW W5 mem5) (rec_record R REC_CHAIN []) O1 (sc_k R)
    (REC_CHAIN, []) c (dec id) p1 HREP1 Htgt1).
  - cbn. lia.
  - intros pn Hpn. exact (Hin45 _ (HincC4 _ Hpn)).
  - intros a Ha Hm1 Hm2. cbn [snd length Z.of_nat] in Hm2.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
    rewrite (scb_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc5
      (scb_FPa_closed c 0 ltac:(lia) ltac:(unfold REC_ARGS_MAX; lia)) Ha).
    + rewrite (UN2 a Ha64 (fun z => z)). exact (scb_malloc_rec _ _ _ _ _ _ _ _ _ a HK4 Ha).
    + intros Hf. destruct (scb_FPa_in c 0 a ltac:(unfold REC_ARGS_MAX; lia) Hf) as [Hx | Hx];
        [exact (Hm1 Hx) | apply Hm2; exact Hx].
  - intros q m i Hqm Hi.
    pose proof (HincC4 _ (HO1c _ Hqm)) as Hq4.
    destruct (scb_blk ly4 S4 W4 mem4 md4 q m i HAR4 Hq4 ltac:(pose proof (req_size_pos m ltac:(lia)); lia)) as (Hb & _).
    rewrite (scb_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q m i HJc5 HAR4b HFPa0 Hq4 (Hin45 _ Hq4) Hi).
    rewrite (UN2 (q + i) ltac:(lia) (fun z => z)).
    exact (scb_malloc_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ q m i HAR4 Eab4 HK4 (HO1c _ Hqm) Hi).
  - exact Hna5.
  - exact Hap5.
  - exact Hstr5.
  - unfold LMAX. lia.
  - lia.
  - exact Hp1in.
  - exact (proj1 (scb_blk_apart ly5 S5 W5 mem5 md5 p1 n1 HAR5 Hp1in)).
  - exact (proj2 (scb_blk_apart ly5 S5 W5 mem5 md5 p1 n1 HAR5 Hp1in)).
  - exact Hp1O1. }
pose proof (sc_target_push _ _ _ _ (dec id) Htgt1) as Htgt2. cbn [fst snd app] in Htgt2.
(* 0x8c3a4 .. 0x8c3ac: a0 := c, a1 := n, the call of arg_i *)
assert (SHOKb : sh_ok SEGS scb_Bx [] Eb (mrestrict (w_H W5) mem5)) by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN1 HS HJ5 SHOKb SC_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) V1. prreg HS (2%bv : bv 5) V2. prreg HS (3%bv : bv 5) V3. prreg HS (4%bv : bv 5) V4.
prreg HS (8%bv : bv 5) V8. prreg HS (10%bv : bv 5) V10. prreg HS (11%bv : bv 5) V11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgC := rg) in *; set (mC := mm) in *; set (mdC := mdq) in *
end.
clearbody mdC.
lazymatch goal with Hfr : frame_of Eb _ (mrestrict _ mem5) (mrestrict _ mC) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) Eb _ (w_H W5) mem5 mC (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
          destruct Hin)) as UN3
end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pose proof (proj1 HJ5) as HAR5c.
pose proof HJ5 as (_ & _ & _ & _ & _ & Hfr5j & Hnev5 & _).
assert (MLE_S5 : mo_le MT S S5 (rec_spill_frees R * mo_free MT + mo_malloc MT (12 * n + 1) + XM_ARG_I MT id))
  by exact (mle_station MT S S4 S5 _ _ MTL MLE_S4 MLE5).
assert (Hna1 : aval_mem (rdW W5 mC) (c + CALL_OFF_NARGS) 4 1).
{ apply (sc3_aval_keep (rdW W5 mem5)); [exact Hna5|].
  intros x Hx. try change (Z.of_nat 4) with 4 in Hx. cbv [CALL_OFF_NARGS] in Hx.
  assert (Hxr : A_G_REC <= x < A_G_REC + REC_SIZE \/ A_REC_SPILL <= x < A_REC_SPILL + SC_SIZE)
    by (apply (scb_slot_in c); [exact Hc | unfold CALL_SIZE; lia]).
  exact (UN3 x ltac:(unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hxr; lia) (fun z => z)). }
(* the call of arg_i(c, n), at fx1 (rounding mode 0 there by fxrel): it returns at some fx2 with fxrel fx1 fx2 *)
rewrite scb_sig_arg_i.
eapply SRr_bind.
{ apply (scb_arg_i_call fx1 W5 rgC mC sp0 ly S W mem md ly5 S5 mdC (k + 1 + EV_ARG_I) O c n 1 (getr rgC 1) HJ5 HAR
    HOS (fxrel_frm0 fx fx1 HFRM Hfx1) HCEIL HROD HFR).
  - unfold spZ. rewrite V2, OLDb, OLDa, Usp by lia. reflexivity.
  - exact WS.
  - rewrite V3, OLDb, OLDa by lia. exact E3.
  - rewrite V4, OLDb, OLDa by lia. exact E4.
  - reflexivity.
  - rewrite V1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite V1, unsigned_lit_small by lia. lia.
  - rewrite V8, OLDb, OLDa by lia. exact E8.
  - rewrite V10, OLDb, OLDa by lia. exact E8.
  - rewrite V11, OLDb, OLDa by lia. exact E9.
  - lia.
  - exact Hc.
  - exact Hna1.
  - unfold REC_ARGS_MAX. lia.
  - lia.
  - lia.
  - apply (mok_station MT S S5 _ _ (XM_ARG_I MT n) MTL HMOKs MLE_S5); lia. }
cbv beta. intros W6 c6 Hwle6 (fx2 & ly6 & S6 & regs6 & mem6 & md6 & Hfx2 & -> & HJ6 & HJc6 & HP6 & HK6). rewrite V1.
(* arg_i returned at fx2: the rest of the segment runs at fx2 *)
pose proof (PaFx.st_ok_restrict_xfx fx1 fx2 _ _ _ _ _ HS eq_refl) as HSf. clear HS. rename HSf into HS.
pose proof (paj_run_to (fx := fx2) B LAWS) as RUNTO2.
jafter_call_keep_pi HS 77%nat regs6 (mrestrict (w_H W6) mem6) HP6 [0]%nat HS6.
match type of HS6 with ?t -> _ => assert (HRK : t); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJc6 | exact HJ6 | rewrite OLDb, OLDa by lia; exact Usp | lia | lia | lia
    | cbn; lia | cbn; lia |].
  intros a Ha Hf. pose proof (scb_FPa_in c 1 a ltac:(unfold REC_ARGS_MAX; lia) Hf) as Hx.
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
clear HS. rename HS6 into HS.
remember (havoc Eb 77 (map (getr regs6) CLOB)) as Ed eqn:HEd in HS.
assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEd; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDd : forall m, (m < 77)%nat -> ew Ed m = ew Eb m) by (intros m Hm; rewrite HEd; apply YN3v.ew_havoc_old; exact Hm).
clear HEd.
(* the recorder after arg_i(c, n): the call holds (17, [dec id; dec n]), the recorder owns both copies *)
destruct HK6 as (HBB6 & MLE6 & p2 & Hp2 & Hperm6 & Hfresh6 & Hna6 & Hap6 & Hstr6).
set (n2 := Z.of_nat (length (dec n)) + 1) in *.
assert (Hdec2 : (1 <= length (dec n) <= 11)%nat) by (apply dec_length; lia).
assert (Hn2b : 2 <= n2 <= 12) by (unfold n2; lia).
pose proof (proj1 HJc6) as HAR6.
assert (Hp2in : In (p2, n2) (ablocks B ly6 S6)) by (apply (Permutation_in _ (Permutation_sym Hperm6)); left; reflexivity).
assert (Hin56 : forall pn, In pn (ablocks B ly5 S5) -> In pn (ablocks B ly6 S6))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm6)); right; exact Hpn).
assert (HFPa1 : forall a, inFP (scb_FPa c 1) a -> A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
{ intros a Ha. pose proof (scb_FPa_in c 1 a ltac:(unfold REC_ARGS_MAX; lia) Ha) as Hx.
  apply (scb_slot_in c); [exact Hc | unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia]. }
assert (Hp2O : ~ In p2 (map fst (O1 ++ [(p1, n1)]))).
{ intros Hq. apply in_map_iff in Hq as ([q kq] & Hqe & Hq). cbn [fst] in Hqe. subst q.
  assert (Hq5 : In (p2, kq) (ablocks B ly5 S5)).
  { apply in_app_or in Hq as [Hq | [Hq | []]];
      [exact (Hin45 _ (HincC4 _ (HO1c _ Hq))) | injection Hq as Eq1 Eq2; rewrite <- Eq1, <- Eq2; exact Hp1in]. }
  pose proof (proj1 (Forall_forall _ _) Hfresh6 _ Hq5) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap.
  assert (Hk0 : kq <= 0) by lia.
  assert (Hne : (p2, kq) <> (p2, n2)) by (intros Hx; injection Hx as Hx; lia).
  pose proof (sep_blocks SEGS B LAWS ly6 S6 W6 mem6 md6 p2 kq p2 n2 HAR6 (Hin56 _ Hq5) Hp2in Hne) as Hd.
  destruct (al_blocks _ _ LAWS ly6 S6 W6 mem6 md6 p2 kq HAR6 (Hin56 _ Hq5)) as (_ & _ & _ & _ & _ & _ & Hkr).
  pose proof (req_size_pos kq ltac:(lia)) as [Rk _]. pose proof (req_size_pos n2 ltac:(lia)) as [Rn _].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HREP3 : rec_repA B ly6 S6 (rdW W6 mem6) (sc_R2 R id n) ((O1 ++ [(p1, n1)]) ++ [(p2, n2)])).
{ apply (scA_push_arg B ly5 S5 ly6 S6 (rdW W5 mem5) (rdW W6 mem6) _ (O1 ++ [(p1, n1)]) (sc_k R)
    (REC_CHAIN, [dec id]) c (dec n) p2 HREP2 Htgt2).
  - cbn. lia.
  - exact Hin56.
  - intros a Ha Hm1 Hm2.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
    rewrite (scb_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc6
      (scb_FPa_closed c 1 ltac:(lia) ltac:(unfold REC_ARGS_MAX; lia)) Ha).
    + exact (UN3 a Ha64 (fun z => z)).
    + intros Hf. destruct (scb_FPa_in c 1 a ltac:(unfold REC_ARGS_MAX; lia) Hf) as [Hx | Hx];
        [exact (Hm1 Hx) | apply Hm2; exact Hx].
  - intros q m i Hqm Hi.
    assert (Hq5 : In (q, m) (ablocks B ly5 S5)).
    { apply in_app_or in Hqm as [Hq | [Hq | []]];
        [exact (Hin45 _ (HincC4 _ (HO1c _ Hq))) | injection Hq as Eq1 Eq2; rewrite <- Eq1, <- Eq2; exact Hp1in]. }
    destruct (scb_blk ly5 S5 W5 mem5 md5 q m i HAR5 Hq5 ltac:(pose proof (req_size_pos m ltac:(lia)); lia)) as (Hb & _).
    rewrite (scb_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q m i HJc6 HAR5c HFPa1 Hq5 (Hin56 _ Hq5) Hi).
    exact (UN3 (q + i) ltac:(lia) (fun z => z)).
  - exact Hna6.
  - exact Hap6.
  - exact Hstr6.
  - unfold LMAX. lia.
  - lia.
  - exact Hp2in.
  - exact (proj1 (scb_blk_apart ly6 S6 W6 mem6 md6 p2 n2 HAR6 Hp2in)).
  - exact (proj2 (scb_blk_apart ly6 S6 W6 mem6 md6 p2 n2 HAR6 Hp2in)).
  - exact Hp2O. }
pose proof (sc_target_push _ _ _ _ (dec n) Htgt2) as Htgt3. cbn [fst snd app] in Htgt3.
(* the text block at this point: live, apart from the recorder's blocks and the two copies *)
assert (Hres6 : In (res, 12 * n + 1) (ablocks B ly6 S6)) by exact (Hin56 _ (Hin45 _ Hres_in)).
destruct (al_blocks _ _ LAWS ly6 S6 W6 mem6 md6 res (12 * n + 1) HAR6 Hres6) as (_ & _ & Hresc6 & Hinapp6 & Hrp6 & _).
assert (Ud49 : bv_unsigned (ew Ed 49) = res).
{ rewrite OLDd, OLDb by lia. rewrite Ea49. apply unsigned_lit_small. pose proof asan_consts as (C1' & _). lia. }
assert (Usp_d : bv_unsigned (ew Ed 2) = sp0 - 112) by (rewrite OLDd, OLDb, OLDa by lia; exact Usp).
assert (HnotRes : forall q m, In (q, m) ((O1 ++ [(p1, n1)]) ++ [(p2, n2)]) ->
  In (q, m) (ablocks B ly6 S6) /\ forall i, 0 <= i < m -> q + i <> res).
{ intros q m Hqm. apply in_app_or in Hqm as [Hqm | [Hqm | []]]; [apply in_app_or in Hqm as [Hqm | [Hqm | []]]|].
  - pose proof (HO1c _ Hqm) as HqC. split; [exact (Hin56 _ (Hin45 _ (HincC4 _ HqC)))|].
    pose proof (recb_fresh_disj_m B ly4 S4 W4 mem4 md4 (ablocks B lyc Sc) res (12 * n + 1) q m HAR4 Eab4 HqC) as Hd.
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q m HARc HqC) as (_ & _ & _ & _ & _ & _ & Hkr).
    pose proof (req_size_pos m ltac:(lia)) as [Rm1 Rm2].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. intros i Hi. lia.
  - injection Hqm as Eq1 Eq2. subst q m. split; [exact (Hin56 _ Hp1in)|].
    pose proof (proj1 (Forall_forall _ _) Hfresh5 _ Hres_in) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap.
    intros i Hi. lia.
  - injection Hqm as Eq1 Eq2. subst q m. split; [exact Hp2in|].
    pose proof (proj1 (Forall_forall _ _) Hfresh6 _ (Hin45 _ Hres_in)) as Hap. cbn [fst snd] in Hap.
    unfold iv_apart in Hap. intros i Hi. lia. }
(* the write list[0] := 0 is one the journal allows: the text block is a temporary block, or a footprint block
   of the recorder that record()'s spill arm freed and malloc handed back *)
assert (Hdz : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
assert (HAWR : awr_byte SEGS B SUP_CHAIN_STK sp0 (sc_FP O) (ablocks B ly S) (ablocks B ly6 S6) (frames S) ly6 [] res).
{ destruct (List.in_dec Hdz (res, 12 * n + 1) (ablocks B ly S)) as [HinS | HnS].
  - destruct (List.in_dec Hdz (res, 12 * n + 1) O) as [HinO | HnO].
    + right. left. split.
      * exists (res, res + req_size (12 * n + 1)). split; [|cbn [fst snd]; lia].
        right. right. unfold ablocks_fp.
        exact (in_map (fun b : Z * Z => (fst b, fst b + req_size (snd b))) O (res, 12 * n + 1) HinO).
      * exists res, (12 * n + 1). split; [exact Hres6 | lia].
    + exfalso. pose proof (HnonO _ HinS HnO) as HinC.
      pose proof (recb_fresh_disj_m B ly4 S4 W4 mem4 md4 (ablocks B lyc Sc) res (12 * n + 1) res (12 * n + 1)
        HAR4 Eab4 HinC) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - right. right. left. exists res, (12 * n + 1). split; [exact Hres6 | split; [exact HnS | lia]]. }
(* the region of the text block's first byte, and the shadow entry of its check: the symbolic state must know
   that the block's address lies in the application's range (the shadow entry's span check) *)
pose proof (st_ok_pi_add_fact Ed _ _ 49%nat (mkAF 4096 0x7fffff800000 4) HS) as HS6f.
match type of HS6f with ?t -> _ => assert (HRK : t); [|specialize (HS6f HRK); clear HRK] end.
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ud49. pose proof asan_consts as (C1' & _).
  split; [lia|]. split; [change (2 ^ 4) with 16; exact Hres16 | lia]. }
clear HS. rename HS6f into HS.
pose proof (st_ok_pi_add_region Ed _ _ scb_txt HS eq_refl) as HS7.
match type of HS7 with ?t -> _ => assert (HRK : t); [|specialize (HS7 HRK); clear HRK] end.
{ unfold region_ok, scb_txt.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
  rewrite Ud49. pose proof asan_consts as (C1' & _). split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hrp6 (res + o) ltac:(lia))). }
match type of HS7 with ?t -> _ => assert (HRK : t); [|specialize (HS7 HRK); clear HRK] end.
{ cbn [all_disjoint ss_mem]. split; [|exact I]. unfold extent_disjoint, scb_txt.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Ud49, Usp_d. left. lia. }
clear HS. rename HS7 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
rewrite <- (restrict_mkst_fx (fx := fx2)) in HS.
assert (SHOKd : sh_ok SEGS scb_Bx [mkSHE 49 0 8] Ed (mrestrict (w_H W6) mem6)).
{ unfold sh_ok. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W6) mem6 Ed scb_Bx 49%nat res 8 res 0 8).
  - exact (range_addressable_of_block SEGS B LAWS ly6 S6 W6 mem6 md6 res (12 * n + 1) res 8 HAR6 Hres6
      ltac:(lia) ltac:(lia)).
  - unfold scb_Bx. rewrite (U_atom Ed 22 SB ltac:(rewrite OLDd, OLDb, OLDa by lia; exact E22) ltac:(unfold SB; lia)).
    reflexivity.
  - apply U_atom; [rewrite OLDd, OLDb by lia; exact Ea49 | pose proof asan_consts as (C1' & _); lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. pose proof asan_consts as (_ & _ & C3' & _).
    unfold in_app in Hinapp6. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
(* 0x8c3b0 .. 0x8c3c4: the checked store list[0] := 0 *)
paj_run_to_tok RUNTO2 HS HJ6 SHOKd SC_Bspan SC_LOOP.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (awr_ok_cons_gen (segs := SEGS) B) with (n := 49%nat);
    [reflexivity | exact Ud49 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. replace a with res by lia. exact HAWR. }
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (20%bv : bv 5) F20.
prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. scb_preg HS (23%bv : bv 5) F23.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgF := rg) in *; set (mF := mm) in *; set (mdF := mdq) in *
end.
clearbody mdF.
lazymatch goal with Hfr : frame_of Ed _ (mrestrict _ mem6) (mrestrict _ mF) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) Ed _ (w_H W6) mem6 mF (fun a => res <= a < res + 1) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Ud49 in Hrr; lia|]);
          destruct Hin)) as UN4
end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* list[0] = 0, read off the text block's region *)
scb_region HS Ed 0%nat W6 HRt.
pose proof (field_of_region (segs := SEGS) Ed _ 49 res _ _ _ _ _ 0 1 (SLit 0) 0 HRt Ud49 ltac:(cbn; tauto)
  ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V0.
clear HRt. rewrite Z.add_0_r in V0. change (N.to_nat 1) with 1%nat in V0.
assert (Hlst0 : rdW W6 mF res = Some 0).
{ pose proof (aval_mem_view SEGS (w_H W6) mF res 1 0 V0 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0. }
(* the recorder across the store: the store's byte is the text block's, apart from g_rec, record.spill and the
   recorder's blocks *)
assert (HREP4 : rec_repA B ly6 S6 (rdW W6 mF) (sc_R2 R id n) (O1 ++ [(p1, n1); (p2, n2)])).
{ change (O1 ++ [(p1, n1); (p2, n2)]) with (O1 ++ [(p1, n1)] ++ [(p2, n2)]). rewrite app_assoc.
  apply (scb_rep_kept ly6 S6 (rdW W6 mem6) (rdW W6 mF) _ _ HREP3).
  - intros a Ha.
    assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
    destruct (scb_blk ly6 S6 W6 mem6 md6 res (12 * n + 1) 0 HAR6 Hres6 ltac:(lia)) as (_ & Hni).
    assert (Hna : ~ (res <= a < res + 1)).
    { intros Hx. apply Hni. replace (res + 0) with a by lia. apply cmd_prog_img. apply scb_in_PG. exact Ha. }
    exact (UN4 a Ha64 Hna).
  - intros q m i Hqm Hi. destruct (HnotRes q m Hqm) as (Hq6 & Hne).
    destruct (scb_blk ly6 S6 W6 mem6 md6 q m i HAR6 Hq6 ltac:(pose proof (req_size_pos m ltac:(lia)); lia)) as (Hb & _).
    assert (Hna : ~ (res <= q + i < res + 1)) by (pose proof (Hne i Hi); lia).
    exact (UN4 (q + i) ltac:(lia) Hna). }
(* the continuation at 0x8c3c4 *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?pc) _ _) _) _ =>
  replace pc with (BASE + SC_LOOP) by (unfold SC_LOOP, AF_sup_chain; lia) end.
eapply (K fx2 ly6 S6 W6 rgF mF mdF res p1 p2 O1).
- exact (fxrel_trans fx fx1 fx2 Hfx1 Hfx2).
- exact HJ6.
- unfold spZ. rewrite F2, OLDd, OLDb, OLDa, Usp by lia. reflexivity.
- rewrite F3, OLDd, OLDb, OLDa by lia. exact E3.
- rewrite F4, OLDd, OLDb, OLDa by lia. exact E4.
- rewrite F8, OLDd, OLDb, OLDa by lia. exact E8.
- rewrite F9, OLDd, OLDb, OLDa by lia. exact E9.
- rewrite F18, OLDd, OLDb, OLDa by lia. exact E18.
- rewrite F19, OLDd, OLDb, OLDa, E8 by lia. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- rewrite F20, OLDd, OLDb by lia. exact Ea49.
- rewrite F21, OLDd, OLDb, OLDa by lia. exact E21.
- rewrite F22, OLDd, OLDb, OLDa by lia. exact E22.
- rewrite F23. apply scb_den_s7; [rewrite OLDd, OLDb, OLDa by lia; exact E8 | rewrite OLDd, OLDb, OLDa by lia; exact E22 | lia].
- scb_region HS Ed 1%nat W6 HRf.
  apply (scb_frame_of_region Ed _ sp0 regs _ HRf Usp_d).
  + intros j r Hj.
    assert (Hj13 : (j < length sc_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    change (length sc_saved) with 13%nat in Hj13.
    rewrite OLDd, OLDb, OLDa by lia. exact (EX j r Hj).
  + intros j Hj. do 13 (destruct j as [|j]; [unfold scb_fchunk; cbn; tauto|]). lia.
- lia.
- rewrite Eab4 in Hperm5. eapply perm_trans; [exact Hperm6|]. apply perm_skip. exact Hperm5.
- exact Hlst0.
- exact HO1O.
- exact HO1c.
- exact HOcO1.
- exact Htgt3.
- exact HREP4.
- exact (mle_station MT S S5 S6 _ _ MTL MLE_S5 MLE6).
Qed.

End e.
End f.
End d.
