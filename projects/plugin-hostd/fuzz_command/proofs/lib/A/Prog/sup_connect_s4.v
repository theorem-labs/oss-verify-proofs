(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the second half of sup_connect's ASan walk (plugin-hostd/fuzz_command,
   0x8adac .. 0x8af0c), from the join of record()'s two arms to the tail jump into answer: SCN_T_stmt -> SCN_B_stmt.

   At the join the slot c (atom 8) gets c->fn := REC_CONNECT and c->nargs := 0; then each argument is copied
   into a fresh block and appended to the call (c->nargs := m + 1, c->args[m] := p): xstrdup(verb or "(null)")
   at 0x8adec, arg_line(c, line) at 0x8ae2c, xstrdup(port_a or "(null)") at 0x8ae54, xstrdup(port_b or "(null)")
   at 0x8aea0; the epilogue restores ra, s0..s7 from the frame and jumps to answer(c, "resp 0", 1). The nine
   inline checks read the shadow of the slot and are removed by the one shadow entry of scn_SH_m.

   The walk splits at the three null checks (bnez s5 / s3 / s1). Each arm runs to the `mv a0, sX` that follows
   the check, and there the two arms meet in one symbolic state: a0 and sX become fresh atoms (sb_canon_ok, the
   kit's st_ok_pi_after_stretch with nothing written) and the branch condition is dropped. The part after
   each meeting point is a lemma of its own (sb_seg1, sb_seg2, sb_seg3), and the three xstrdup calls go
   through one lemma (sb_xcall, PaCall's cl_callS with xstrdup's statement; its footprint is empty).

   The symbolic regions on the slot are kept tight: before a store run, a region is writable exactly on the two
   fields the run stores (c->nargs and c->args[m]), so the run's frame says every other byte of the recorder is
   kept, which scn_append_rep (sup_connect_s2.v) asks; before a branch every region is made read-only, so the
   arms keep the whole memory. *)
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
rec_calls_free_c rec_canonical_c hand_back_c xstrdup_c arg_line_c answer_c sup_connect_c sup_connect_s0 sup_connect_s2.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------ *)
(* The symbolic states of the walk                                                                    *)

(* the regions on the slot c (atom 8): the whole slot, c->nargs alone, and c->args[j] alone *)
Definition sb_slot (wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 CALL_SIZE wlo whi cs.
Definition sb_nargs (w : bool) (v : Z) : YP09.region :=
YP09.mkRegion (Some 8%nat) 4 8 4 (if w then 8 else 4) [YP09.mkChunk 4 (CVal 4 (SLit v))].
Definition sb_arg (j : Z) (w : bool) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 8%nat) (8 + 8 * j) (16 + 8 * j) (8 + 8 * j) (if w then 16 + 8 * j else 8 + 8 * j) cs.
(* a region made read-only *)
Definition sb_ro (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_wlo r) (YP09.r_chunks r).
(* the meeting point of the two arms of a null check: a0 and the checked register become the atoms k, k + 1,
   and the branch condition is dropped *)
Definition sb_canon (ss : sstate) (k : nat) (clob : list (bv 5)) : sstate :=
mkSS (ss_pc ss) (sr_sets (ss_regs ss) (junk_upd k clob)) (ss_mem ss) None (mkFacts (f_atoms (ss_facts ss)) [] []).
Definition sb_setmem (ss : sstate) (rs : smem) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss).

(* the executor over fuzz_command's listing, with the join's shadow entry *)
Definition sb_run (ss : sstate) :=
sym_runN_pi_tok cmd_tpi cmd_tw (run_K A_LIM scn_Bx_m scn_SH_m ss) scn_Bx_m scn_Bspan scn_SH_m FUEL ss.
Definition sb_run_to (stop : Z) (ss : sstate) :=
sym_run_toN_pi_tok cmd_tpi cmd_tw (run_K A_LIM scn_Bx_m scn_SH_m ss) scn_Bx_m scn_Bspan scn_SH_m FUEL stop ss.

(* the walk's offsets: the three meeting points (0x8ade8, 0x8ae50, 0x8ae9c) and the return points of the
   four calls (0x8adf0, 0x8ae30, 0x8ae58, 0x8aea4) *)
Definition SB_M1 : Z := 0x4904.
Definition SB_M2 : Z := 0x496c.
Definition SB_M3 : Z := 0x49b8.
Definition SB_R1 : Z := 0x490c.
Definition SB_R2 : Z := 0x494c.
Definition SB_R3 : Z := 0x4974.
Definition SB_R4 : Z := 0x49c0.

(* the state at 0x8addc (bnez s5) after the join's stores, with the slot made read-only *)
Definition sb_S1 : sstate := Eval vm_compute in
let s := sh_ss (fst (sb_run scn_ss_m)) in sb_setmem s (list_upd (ss_mem s) 1 (sb_ro (nth 1 (ss_mem s) scn_stack_m))).
(* the first meeting point, 0x8ade8: a0 and s5 are the atoms 41, 42 *)
Definition sb_C1 : sstate := Eval vm_compute in
sb_canon (sh_ss (fst (sb_run_to SB_M1 (add_cond sb_S1 (mkAC BC_NE (SOff 21 0) (SLit 0)))))) 41 [10; 21]%bv.
(* the second meeting point, 0x8ae50: after xstrdup(verb), the store run, arg_line, and the run to bnez s3;
   a0 and s3 are the atoms 80, 81 *)
Definition sb_C2 : sstate := Eval vm_compute in
let s3 := sh_ss (fst (sb_run sb_C1)) in
let p1 := ss_after_call s3 (ss_mem s3) 48 SB_R1 in
let p1' := sb_setmem p1 (list_upd (ss_mem p1) 1 (sb_slot 4 16 (YP09.r_chunks (nth 1 (ss_mem p1) scn_stack_m)))) in
let s4 := sh_ss (fst (sb_run p1')) in
let p2 := ss_after_call s4 (pick (ss_mem s4) [0%nat]) 64 SB_R2 in
let p2' := sb_setmem p2 (sb_nargs false 2 :: ss_mem p2) in
let s5 := sh_ss (fst (sb_run p2')) in
sb_canon (sh_ss (fst (sb_run_to SB_M2 (add_cond s5 (mkAC BC_NE (SOff 19 0) (SLit 0)))))) 80 [10; 19]%bv.
(* the third meeting point, 0x8ae9c: after xstrdup(port_a), the store run and the run to bnez s1, with every
   region read-only; a0 and s1 are the atoms 112, 113 *)
Definition sb_C3 : sstate := Eval vm_compute in
let s7 := sh_ss (fst (sb_run sb_C2)) in
let p3 := ss_after_call s7 (ss_mem s7) 96 SB_R3 in
let p3a := sb_setmem p3 (list_upd (ss_mem p3) 0 (sb_nargs true 2)) in
let p3b := sb_setmem p3a (sb_arg 2 true [] :: ss_mem p3a) in
let s8 := sh_ss (fst (sb_run p3b)) in
let s8r := sb_setmem s8 (map sb_ro (ss_mem s8)) in
sb_canon (sh_ss (fst (sb_run_to SB_M3 (add_cond s8r (mkAC BC_NE (SOff 9 0) (SLit 0)))))) 112 [10; 9]%bv.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma sb_stk : SUP_CONNECT_STK = 16592.
Proof. reflexivity. Qed.
Lemma sb_xstk : XSTRDUP_STK = 16416.
Proof. reflexivity. Qed.
Lemma sb_alstk : ARG_LINE_STK = 16464.
Proof. reflexivity. Qed.

(* "(null)", the literal a NULL argument becomes (A_OBJ 52 = 0x22480) *)
Lemma sb_null_eq : sarg None = map (Z_to_bv 8) [40; 110; 117; 108; 108; 41].
Proof. vm_compute. reflexivity. Qed.
Lemma sb_null_len : length (sarg None) = 6%nat.
Proof. rewrite sb_null_eq. reflexivity. Qed.
Lemma sb_ro_null : sarg None ++ [Z_to_bv 8 0] = RO_lit_22480.
Proof. rewrite sb_null_eq. vm_compute. reflexivity. Qed.
Lemma sb_null_nz : ~ In (Z_to_bv 8 0) (sarg None).
Proof.
rewrite sb_null_eq. cbn [map In]. intros H.
repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H.
Qed.
Lemma sb_end_in : In 0x22486 cmd_ro_ends.
Proof. apply In_of_existsb. vm_compute. reflexivity. Qed.

(* the statics the walk names: sup_connect's footprint lies in the program's statics and the recorder's
   blocks *)
Lemma sb_fp_cases : forall O a, inFP (scn_FP O) a -> inFP cmd_PG a \/ inFP (ablocks_fp O) a.
Proof.
intros O a (r & Hr & Ha). unfold scn_FP in Hr.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha;
[left; exists (A_G_REC, A_G_REC + 960) | left; exists (A_G_REC, A_G_REC + 960)
| left; exists (A_G_REC, A_G_REC + 960) | left; exists (A_REC_SPILL, A_REC_SPILL + 56) | right; exists r; split; assumption];
(split; [unfold cmd_PG; cbn [In]; tauto | cbn [fst snd]; unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, SC_SIZE in *; lia]).
Qed.
Lemma sb_pg_range : forall a, inFP cmd_PG a -> A_G_REC <= a < A_G_QUITTING + 4.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in *; lia.
Qed.
Lemma sb_pg_closed : forall FP1, (forall b, inFP FP1 b -> inFP cmd_PG b) -> ~ YI16.sink_open_fp FP1.
Proof.
intros FP1 HF (r & Hr & H0). pose proof (sb_pg_range 0 (HF 0 (ex_intro _ r (conj Hr H0)))) as H.
unfold A_G_REC in H. lia.
Qed.
Lemma sb_fp_closed : forall O, Forall (fun pn => 0 < fst pn) O -> ~ YI16.sink_open_fp (scn_FP O).
Proof.
intros O HO. apply sink_closed_pos. unfold scn_FP.
repeat apply Forall_cons; try (cbn [fst]; unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_STATE; lia).
unfold ablocks_fp. apply Forall_map. exact HO.
Qed.

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
(* the record's shadow checkers at any AR state (CmdChk.v's booleans; CmdRecFacts.v's names) *)
Hypothesis cmd_addressable_chk : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md ->
cmd_addr_b a n = true -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Hypothesis cmd_hull_vis_chk : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md ->
cmd_hull_b a n = true -> shadow_hull_vis (aview SEGS (w_H W) mem) a n.
(* the read-only objects of the image lie in the read-only range (CmdRo.v's cmd_ro_in) *)
Hypothesis cmd_ro_in_img : cmd_ro_in (in_roP SEGS RLO RHI).
Hypothesis RRO : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS RLO RHI a.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma sb_sig_x : SIGMA CS_xstrdup = BASE + AF_xstrdup.
Proof. rewrite (SIGP CS_xstrdup); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma sb_sig_al : SIGMA CS_arg_line = BASE + AF_arg_line.
Proof. rewrite (SIGP CS_arg_line); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.
Lemma sb_sig_ans : SIGMA CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.

Lemma sb_null_unowned : forall i, 0 <= i < 7 ->
~ Exists (in_zr (0x22480 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x22480 + i < as_errno B + 4).
Proof.
intros i Hi. rewrite (ts_owned B HB), (ts_errno B HB).
assert (HOW : forallb (fun q : Z * Z => ((0x22480 + 7 <=? fst q) || (fst q + snd q <=? 0x22480))%bool)
  Tfib_owned_static = true) by (vm_compute; reflexivity).
split.
- intros HE. rewrite Exists_exists in HE. destruct HE as (q & Hq & Hz). unfold in_zr in Hz.
  rewrite forallb_forall in HOW. specialize (HOW q Hq).
  apply Bool.orb_prop in HOW as [H1 | H1]; apply Z.leb_le in H1; lia.
- unfold TFIB_ERRNO. lia.
Qed.

(* the recorder's blocks at the entry are live, above the first page and at least one byte long *)
Lemma sb_O_facts : forall ly S (W : world SEGS) mem md rd R O, AR SEGS B ly S W mem md -> rec_repA B ly S rd R O ->
forall pn, In pn O -> In pn (ablocks B ly S) /\ 4096 <= fst pn /\ 1 <= snd pn.
Proof.
intros ly S W mem md rd R O HAR (Q & HQ & HOQ) [p n] Hin.
destruct (scn_lay_facts _ _ _ _ _ _ (p, n) HQ (proj1 (HOQ _) Hin)) as (_ & Hn & Hbl).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hbl) as (_ & Hp & _). cbn [fst snd] in *. auto.
Qed.

(* the read-only bytes are kept by the walk's journal: they are image bytes outside its footprint *)
Lemma sb_arod : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) -> Forall (fun pn => 0 < fst pn) O ->
ajournal SEGS B STK sp0 (scn_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HAR HOin HOpos HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Himg : in_img SEGS a)
by (destruct Hro as [(sg & Hsg & _ & Hrng) | Hrr]; [exists sg; split; [exact Hsg | exact Hrng] | exact (RRO a Hrr)]).
rewrite (F3 a Himg Ho He); [exact (HR a Hro Ho He)|].
apply fp_spares_closed; [apply sb_fp_closed; exact HOpos|].
intros Hin. destruct (sb_fp_cases O a Hin) as [Hpg | Hb].
- exact (RPG a Hpg Hro).
- destruct (inFP_ablocks_fp_inv _ a Hb) as (p & n & Hpn & Hr).
  pose proof (blk_off_imgP B ly S W mem md p n HAR (HOin _ Hpn)) as Hoff. unfold off_img in Hoff.
  pose proof (pa_img_range a Himg) as Hrange. lia.
Qed.

(* a callee whose footprint lies in the program's statics keeps every other static byte and every byte of
   a block live before and after it *)
Lemma sb_call_keep : forall STK1 sp1 FP1 lyq Sq (Wq : world SEGS) memq mdq ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyq Sq Wq memq mdq [] ly2 S2 W2 mem2 md2 k1 ->
(forall b, inFP FP1 b -> inFP cmd_PG b) ->
(inFP cmd_PG a /\ ~ inFP FP1 a \/
 exists q m, In (q, m) (ablocks B lyq Sq) /\ In (q, m) (ablocks B ly2 S2) /\ q <= a < q + m) ->
rdW W2 mem2 a = rdW Wq memq a.
Proof.
intros STK1 sp1 FP1 lyq Sq Wq memq mdq ly2 S2 W2 mem2 md2 k1 a HJ HFP [(Hpg & Hna) | (q & m & Hq & Hq2 & Ha)].
- exact (scn_pg_kept B HB cif_prog_img STK1 sp1 FP1 lyq Sq Wq memq mdq [] ly2 S2 W2 mem2 md2 k1 a HJ
    (sb_pg_closed FP1 HFP) Hpg Hna).
- pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 q m HAR2 Hq2) as Hoff. unfold off_img in Hoff.
  pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
  replace a with (q + (a - q)) by lia. apply (F2 q m (a - q)); [exact Hq | exact Hq2 | lia |].
  intros Hin. pose proof (sb_pg_range _ (HFP _ Hin)) as Hr. unfold A_G_REC, A_G_QUITTING in Hr. lia.
Qed.

(* a region on the slot is kept by such a callee where it misses the callee's footprint *)
Lemma sb_slot_kept : forall E (Wq W2 : world SEGS) memq mem2 c lo hi wlo whi cs STK1 sp1 FP1 lyq Sq mdq ly2 S2 md2 k1,
ajournal SEGS B STK1 sp1 FP1 lyq Sq Wq memq mdq [] ly2 S2 W2 mem2 md2 k1 ->
bv_unsigned (ew E 8) = c -> scn_slot c -> 0 <= lo -> hi <= CALL_SIZE -> 0 <= wlo -> whi <= CALL_SIZE ->
(forall b, inFP FP1 b -> inFP cmd_PG b) ->
(forall a, c + lo <= a < c + hi -> ~ inFP FP1 a) ->
region_kept SEGS E (mrestrict (w_H Wq) memq) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some 8%nat) lo hi wlo whi cs).
Proof.
intros E Wq W2 memq mem2 c lo hi wlo whi cs STK1 sp1 FP1 lyq Sq mdq ly2 S2 md2 k1 HJ Hc Hsl Hlo Hhi Hwlo Hwhi HFP HnF.
destruct (scn_slot_facts c Hsl) as (_ & _ & Hcin).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hc; intros a Ha.
- apply (mbyte_of_aview SEGS). apply (sb_call_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HFP).
  left. split; [apply Hcin; lia | apply HnF; lia].
- intros _. apply (scn_pg_writable B PROG_WRITABLE ly2 S2 W2 mem2 md2 a (proj1 HJ)). apply Hcin. lia.
Qed.

(* the shadow entry of the slot at any state of the allocator *)
Lemma sb_shok : forall ly S (W : world SEGS) mem md E c,
AR SEGS B ly S W mem md -> scn_slot c -> bv_unsigned (ew E 8) = c -> ew E 22 = Z_to_bv 64 SCN_SB ->
sh_ok SEGS scn_Bx_m scn_SH_m E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR Hsl Hc Hsb.
destruct (scn_slot_facts c Hsl) as (_ & Hcr & _). unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcr.
unfold sh_ok, scn_SH_m. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E scn_Bx_m 8 c CALL_SIZE c 0 CALL_SIZE).
- exact (scn_slot_addressable B HB LAWS ly S W mem md c c CALL_SIZE HAR Hsl ltac:(lia) ltac:(lia)).
- unfold U, scn_Bx_m. cbn [sv_denot]. rewrite Hsb, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SCN_SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hc.
- lia.
- lia.
- intros x Hx. unfold SHADOW_OFF, CALL_SIZE in *. lia.
Qed.

(* a writable region on the slot: its window is a footprint byte of the program's statics *)
Lemma sb_awr_slot : forall E r rs STK sp0 O bl0 blc fr0 ly own c,
YP09.r_base r = Some 8%nat -> bv_unsigned (ew E 8) = c -> scn_slot c -> 0 <= YP09.r_wlo r -> YP09.r_whi r <= CALL_SIZE ->
awr_ok SEGS B E rs STK sp0 (scn_FP O) bl0 blc fr0 ly own -> awr_ok SEGS B E (r :: rs) STK sp0 (scn_FP O) bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 O bl0 blc fr0 ly own c Hb Hc Hsl Hlo Hhi H.
destruct (scn_slot_facts c Hsl) as (_ & _ & Hcin).
eapply awr_ok_cons_gen; [exact Hb | exact Hc | | exact H].
intros a Ha. do 4 right. left.
split; [|split; [apply (HPROG B HB), Hcin; lia | apply cif_prog_img, Hcin; lia]].
destruct Hsl as [(i & Hi & ->) | ->].
- exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8). split; [unfold scn_FP; right; left; reflexivity|].
  cbn [fst snd]. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_CALLS_MAX in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [unfold scn_FP; right; right; right; left; reflexivity|].
  cbn [fst snd]. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the meeting point of the two arms of a null check: nothing is written, a0 and the checked register become
   fresh atoms, and the branch condition is dropped *)
Lemma sb_canon_ok : forall (W : world SEGS) E ss ms k clob,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
(k + length clob <= A_TEXT)%nat -> ss_atoms_p (pband k A_TEXT) ss = true ->
regions_wf (ss_mem ss) = true -> no_cdata (ss_mem ss) = true -> mem_atoms_p (pband k A_TEXT) (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
st_ok_pi SEGS VAL (havoc E k (map (getr (ms_regs ms)) clob)) (sb_canon ss k clob) (restrict (w_H W) ms).
Proof.
intros W E ss ms k clob HS Hrv Hk Hat Hwf Hnc Hmat Hnd Hnz.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
assert (Hat' : ss_atoms_p (pband k A_TEXT) (abs_ss VAL ss) = true) by (destruct ss; exact Hat).
assert (Hsub : submem (ss_mem ss) (ss_mem (abs_ss VAL ss))) by (destruct ss; apply submem_refl).
assert (Hrv' : ss_resv (abs_ss VAL ss) = None) by (destruct ss; exact Hrv).
pose proof (st_ok_pi_after_stretch k E (abs_ss VAL ss) (restrict (w_H W) ms) (ms_regs ms)
  (mrestrict (w_H W) (ms_mem ms)) (ss_mem ss) (ss_pc ss) clob HS Hrv' Hk Hat' Hwf Hnc Hmat Hsub Hnd Hnz
  ltac:(intros r _; reflexivity)) as H.
match type of H with ?P -> _ => assert (HK : P); [|specialize (H HK); clear HK] end.
{ apply Forall_forall. intros r _. split; [intros a _; reflexivity | intros a _ Hw; exact Hw]. }
assert (Hr : restrict (w_H W) ms =
  mkst (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)).
{ rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
rewrite Hr. unfold st_ok_pi in H |- *.
pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & HG).
destruct HG as (HA & _ & _).
pose proof (st_ok_facts SEGS _ _ _ (mkFacts (f_atoms (ss_facts ss)) [] []) H) as H2.
destruct ss. exact (H2 (conj HA (conj I I))).
Qed.

(* a caller string still to be copied: NULL or a string in a live block *)
Definition sb_sstr (bl : list (Z * Z)) (rd : reader) (p : Z) (v : option (list byte)) : Prop :=
match v with
| None => p = 0
| Some x => p <> 0 /\ astr_atR rd p x /\ in_blockA bl p (Z.of_nat (length x) + 1) /\
  Z.of_nat (length x) + 1 <= LMAX + 1
end.
(* the string xstrdup copies: "(null)" or the caller's string *)
Definition sb_xarg (bl : list (Z * Z)) (rd : reader) (s : Z) (v : option (list byte)) : Prop :=
(v = None /\ s = 0x22480) \/
(exists x, v = Some x /\ s <> 0 /\ astr_atR rd s x /\ in_blockA bl s (Z.of_nat (length x) + 1) /\
 Z.of_nat (length x) + 1 <= LMAX + 1).
Lemma sb_xarg_of : forall bl rd p v, sb_sstr bl rd p v -> sb_xarg bl rd (if p =? 0 then 0x22480 else p) v.
Proof.
intros bl rd p [x|] H; cbn [sb_sstr] in H.
- destruct H as (Hp & Hs & Hb & Hl). right. exists x. rewrite (proj2 (Z.eqb_neq p 0) Hp). auto.
- subst p. left. auto.
Qed.
Lemma sb_sstr_keep : forall bl bl' (rd rd' : reader) p v, sb_sstr bl rd p v ->
(forall pn, In pn bl -> In pn bl') ->
(forall a, (exists q m, In (q, m) bl /\ q <= a < q + m) -> rd' a = rd a) ->
sb_sstr bl' rd' p v.
Proof.
intros bl bl' rd rd' p [x|] H Hbl K; cbn [sb_sstr] in H |- *; [|exact H].
destruct H as (Hp & Hs & (q & m & Hq & H1 & H2) & Hl).
split; [exact Hp|]. split; [|split; [exists q, m; split; [apply Hbl; exact Hq | lia] | exact Hl]].
apply (scn_str_keep rd); [exact Hs|]. intros i Hi. apply K. exists q, m. split; [exact Hq|]. lia.
Qed.

(* the bytes scn_append_rep asks a step to keep *)
Definition sb_recb (bl O : list (Z * Z)) (a : Z) : Prop :=
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
exists pn, In pn bl /\ In pn O /\ fst pn <= a < fst pn + snd pn.
Lemma sb_recb_static : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
inFP cmd_PG a.
Proof.
intros a [Ha | Ha]; [exists (A_G_REC, A_G_REC + 960) | exists (A_REC_SPILL, A_REC_SPILL + 56)];
(split; [unfold cmd_PG; cbn [In]; tauto | cbn [fst snd]; unfold REC_SIZE, SC_SIZE in Ha; lia]).
Qed.

(* the block bookkeeping of scn_tail at a state of the walk *)
Definition sb_bk (ly : alayout) (S : astate) (O bl Oi : list (Z * Z)) : Prop :=
(forall pn, In pn Oi -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn bl -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn Oi) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn bl).
Definition sb_pdec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma sb_bk_step : forall ly S O bl bl' Oi p k,
sb_bk ly S O bl Oi -> Permutation bl' ((p, k) :: bl) ->
(In (p, k) (ablocks B ly S) -> In (p, k) O) ->
sb_bk ly S O bl' ((p, k) :: Oi).
Proof.
intros ly S O bl bl' Oi p k (H1 & H2 & H3) HP Hnew. split; [|split].
- intros pn [<- | Hin]; [|exact (H1 pn Hin)].
  destruct (in_dec sb_pdec (p, k) (ablocks B ly S)) as [Hi | Hi]; [left; exact (Hnew Hi) | right; exact Hi].
- intros pn Hin. apply (Permutation_in _ HP) in Hin. destruct Hin as [<- | Hin]; [right; left; reflexivity|].
  destruct (H2 pn Hin) as [Hl | Hr]; [left; exact Hl | right; right; exact Hr].
- intros pn Hin Hno. apply (Permutation_in _ (Permutation_sym HP)). right. exact (H3 pn Hin Hno).
Qed.
(* a block live at the entry and no longer live at a later state of the walk was one of the recorder's (the
   journal says its bytes lie in the footprint, so inside a recorder block, which is then the same block) *)
Lemma sb_new_in_O : forall ly S (W : world SEGS) mem md O own ly' S' (W' : world SEGS) mem' md' k sp0 STK p n,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (scn_FP O) ly S W mem md own ly' S' W' mem' md' k ->
~ In (p, n) (ablocks B ly' S') -> In (p, n) (ablocks B ly S) -> In (p, n) O.
Proof.
intros ly S W mem md O own ly' S' W' mem' md' k sp0 STK p n HAR HOin HJ Hnl Hin.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ffree & _).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2].
pose proof (Ffree p n 0 Hin Hnl ltac:(lia)) as Hf. rewrite Z.add_0_r in Hf.
pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff. unfold off_img in Hoff.
destruct (sb_fp_cases O p Hf) as [Hpg | Hb].
- pose proof (sb_pg_range p Hpg) as Hr. unfold A_G_REC, A_G_QUITTING in Hr. lia.
- destruct (inFP_ablocks_fp_inv _ p Hb) as (q & m & Hqm & Hr).
  destruct (sb_pdec (q, m) (p, n)) as [Eq | Ne]; [rewrite <- Eq; exact Hqm|].
  exfalso. pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR (HOin _ Hqm) Hin Ne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* xstrdup through the kit's call rule: its footprint is empty, so plain cl_callS composes *)
Lemma sb_xcall : forall (Q : world SEGS -> config -> Prop) sp0 FP ly S (W : world SEGS) mem md (Wq : world SEGS)
  regsq memq mdq lyq Sq kq s v,
ajournal SEGS B SUP_CONNECT_STK sp0 FP ly S W mem md [] lyq Sq Wq memq mdq kq ->
spZ regsq = sp0 + -80 ->
getr regsq 3 = w64 (as_gp B) -> getr regsq 4 = w64 (as_tp B) ->
YK0s.ret_ok (getr regsq 1) -> 4096 <= bv_unsigned (getr regsq 1) ->
s0Z regsq < alloc_ceiling ->
getr regsq 10 = w64 s ->
arodata_okP SEGS RLO RHI B (rdW Wq memq) ->
sb_xarg (ablocks B lyq Sq) (rdW Wq memq) s v ->
st_nev Sq + EV_XSTRDUP <= EV_MAX -> blocks_bytes Sq + LIVE_XSTRDUP (sarg v) <= LIVE_MAX ->
mo_ok MT Sq (XM_XSTRDUP MT (sarg v)) ->
(forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 p,
  ajournal SEGS B SUP_CONNECT_STK sp0 FP ly S W mem md [] ly2 S2 W2 mem2 md2 (kq + EV_XSTRDUP) ->
  ajournal SEGS B XSTRDUP_STK (sp0 + -80) [] lyq Sq Wq memq mdq [] ly2 S2 W2 mem2 md2 EV_XSTRDUP ->
  aregs_preserved regsq regs2 -> getr regs2 10 = w64 p -> 4096 <= p < 2 ^ 64 ->
  Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP (sarg v)) :: ablocks B lyq Sq) ->
  Forall (fun qk => iv_apart p (LIVE_XSTRDUP (sarg v)) (fst qk) (snd qk)) (ablocks B lyq Sq) ->
  in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP (sarg v)) ->
  astr_atR (rdW W2 mem2) p (sarg v) ->
  blocks_bytes S2 <= blocks_bytes Sq + LIVE_XSTRDUP (sarg v) ->
  mo_le MT Sq S2 (XM_XSTRDUP MT (sarg v)) ->
  SRr SEGS W2 (mkCfg (mkst regs2 (getr regsq 1) mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS Wq (mkCfg (mkst regsq (Z_to_bv 64 (SIGMA CS_xstrdup)) memq (seg_rom SEGS)) mdq) Q.
Proof.
intros Q sp0 FP ly S W mem md Wq regsq memq mdq lyq Sq kq s v HJ Hsp Hgp Htp Hra Hra4 Hs0 H10 HROD HARG
  Hev Hlive Hmok K.
pose proof (proj1 HJ) as HARq.
assert (HXA : astr_argA B lyq Sq (rdW Wq memq) (in_roP SEGS RLO RHI) [] s (Some (sarg v)) /\
  atail_vis SEGS Wq memq (s + Z.of_nat (length (sarg v)))).
{ destruct HARG as [(-> & ->) | (x & -> & Hs0' & Hstr & (q & m & Hqm & Hq1 & Hq2) & Hlen)].
  - assert (Hro : cmd_ro_ok (rdW Wq memq)) by exact (cmd_ro_ok_of_aro lyq Sq Wq memq mdq HARq HROD).
    assert (HLIT : abytes_atR (rdW Wq memq) 0x22480 RO_lit_22480).
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
    + unfold astr_argA. cbv zeta. rewrite sb_null_len.
      split; [lia|]. split; [split; [rewrite sb_ro_null; exact HLIT | exact sb_null_nz]|].
      split; [unfold LMAX; lia|].
      right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity |]]].
      2: { change (0x22480 + Z.of_nat 6) with 0x22486. exact sb_end_in. }
      intros i Hi. split; [exact (HIN i Hi)|]. exact (sb_null_unowned i Hi).
    + rewrite sb_null_len. change (0x22480 + Z.of_nat 6) with 0x22486.
      exact (cmd_tail_vis_at lyq Sq Wq memq mdq 0x22486 HARq sb_end_in).
  - cbn [sarg]. split.
    + unfold astr_argA. cbv zeta. split; [exact Hs0'|]. split; [exact Hstr|]. split; [exact Hlen|].
      left. split; [exists q, m; auto | constructor].
    + exact (cmd_heap_tail_vis lyq Sq Wq memq mdq q m (s + Z.of_nat (length x)) HARq Hqm ltac:(lia)). }
destruct HXA as [HXA HTAIL].
rewrite sb_sig_x.
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wq regsq memq (Z_to_bv 64 (BASE + AF_xstrdup)) SUP_CONNECT_STK sp0 FP ly S W mem md []
    lyq Sq mdq kq XSTRDUP_STK [] EV_XSTRDUP (-80) (getr regsq 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z, getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP (sarg v)) :: ablocks B lyq Sq) /\
       Forall (fun qk => iv_apart p (LIVE_XSTRDUP (sarg v)) (fst qk) (snd qk)) (ablocks B lyq Sq) /\
       in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP (sarg v)) /\
       astr_atR (rdW W2 mem2) p (sarg v) /\ astr_atR (rdW W2 mem2) s (sarg v) /\
       blocks_bytes S2 <= blocks_bytes Sq + LIVE_XSTRDUP (sarg v) /\
       mo_le MT Sq S2 (XM_XSTRDUP MT (sarg v)))
    HJ Hsp eq_refl ltac:(lia) ltac:(rewrite sb_xstk; lia) ltac:(rewrite sb_xstk, sb_stk; lia) Hgp Htp eq_refl Hra Hra4
    (achain_low _ _ _ _ Hs0)).
  - intros HPREc. eapply SRr_mono.
    { exact (TXSTRDUP fx lyq Sq Wq regsq memq mdq [] s (sarg v) HPREc HROD H10
        (or_introl HXA) HTAIL Hev Hlive Hmok). }
    cbv beta. unfold apost_base. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2).
    exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2 | exact HQ2].
  - intros a Ha. destruct (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 &
  p & Hp10 & Hp4096 & Hperm & Hfresh & Hpblk & Hpstr & _ & Hbb & Hmle).
exact (K ly2 S2 W2 regs2 mem2 md2 p HJ2 HJ2c HP2 Hp10 Hp4096 Hperm Hfresh Hpblk Hpstr Hbb Hmle).
Qed.

Lemma sb_in_blk_range : forall ly S (W : world SEGS) mem md q m a,
AR SEGS B ly S W mem md -> In (q, m) (ablocks B ly S) -> q <= a < q + m ->
4096 <= a /\ a < alloc_ceiling /\ (a < 0x10000 \/ 0x606000 <= a).
Proof.
intros ly S W mem md q m a HAR Hq Ha.
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR Hq) as (_ & Hq4096 & Hqc & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
pose proof (blk_off_imgP B ly S W mem md q m HAR Hq) as Hoff. unfold off_img in Hoff. lia.
Qed.
Lemma sb_sarg_len : forall bl rd p v, sb_sstr bl rd p v -> Z.of_nat (length (sarg v)) <= LMAX.
Proof. intros bl rd p [x|] H; cbn [sb_sstr] in H; [cbn [sarg]; lia | rewrite sb_null_len; unfold LMAX; lia]. Qed.

(* the context of the second half: the statement's premises and the join *)
Definition sb_cx ly S (W : world SEGS) regs mem md ch pv pl pa pb verb line port_a port_b R O
  lyc Sc (Wc : world SEGS) regsc memc mdc k c O1 : Prop :=
scn_pre B MT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O
  (snd (sup_connect_m R verb line port_a port_b)) /\
scn_mid B MT ly S W regs mem md R O lyc Sc Wc regsc memc mdc k c O1.
(* the environment at a meeting point: the image's atoms, and the join's atoms 0..40 *)
Definition sb_env (E : env) (regsc regs : bvmap 5 word) : Prop :=
img_env VAL A_LIM E /\ (forall n, (n < 41)%nat -> ew E n = ew (Eimg (Ereg regsc (scn_extra_m regs))) n).
(* what the walk carries from one meeting point to the next: the journal from the entry, the frames, the
   live bytes so far (`lv`) and still to come (`rem`), the meter so far, the recorder (rec_repA at a reader
   rdR the current memory agrees with on the recorder's bytes) and the block bookkeeping *)
Definition sb_inv ly S (W : world SEGS) mem md sp0 R O (Wi : world SEGS) memi mdi lyi Si ki Oi Ai (rdR : reader)
  (acc rem lv : Z) : Prop :=
ajournal SEGS B SUP_CONNECT_STK sp0 (scn_FP O) ly S W mem md [] lyi Si Wi memi mdi ki /\
frames Si = frames S /\ blocks_bytes Si + rem <= LIVE_MAX /\ blocks_bytes Si <= blocks_bytes S + lv /\
mo_le MT S Si acc /\
rec_repA B lyi Si rdR (rec_record R REC_CONNECT Ai) Oi /\
(forall a, sb_recb (ablocks B lyi Si) Oi a -> rdW Wi memi a = rdR a) /\
sb_bk ly S O (ablocks B lyi Si) Oi.

(* the walk from the third meeting point 0x8ae9c to answer *)
Definition SB3_stmt : Prop :=
forall ly S (W : world SEGS) regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc (Wc : world SEGS) regsc memc
  mdc k c O1 E (W3 : world SEGS) regs3 mem3 md3 ly3 S3 O3 (rd3 : reader),
sb_cx ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1 ->
st_ok_pi SEGS VAL E sb_C3 (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + SB_M3)) mem3 (seg_rom SEGS))) ->
sb_env E regsc regs -> ew E 113 = Z_to_bv 64 (if pb =? 0 then 0x22480 else pb) ->
sb_inv ly S W mem md (spZ regs) R O W3 mem3 md3 ly3 S3 (k + 3) O3 [sarg verb; canon line; sarg port_a] rd3
  (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg verb) + XM_ARG_LINE MT line + XM_XSTRDUP MT (sarg port_a))
  (LIVE_XSTRDUP (sarg port_b) + LIVE_ANSWER (snd (sup_connect_m R verb line port_a port_b)))
  (LIVE_XSTRDUP (sarg verb) + LIVE_ARG_LINE line + LIVE_XSTRDUP (sarg port_a)) ->
sb_sstr (ablocks B ly3 S3) (rdW W3 mem3) pb port_b ->
SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + SB_M3)) mem3 (seg_rom SEGS)) md3)
  (scn_post B MT ly S W regs mem md verb line port_a port_b R O (snd (sup_connect_m R verb line port_a port_b))).

(* the walk from the second meeting point 0x8ae50 to the third *)
Definition SB2_stmt : Prop :=
forall ly S (W : world SEGS) regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc (Wc : world SEGS) regsc memc
  mdc k c O1 E (W2 : world SEGS) regs2 mem2 md2 ly2 S2 O2 (rd2 : reader),
sb_cx ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1 ->
st_ok_pi SEGS VAL E sb_C2 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + SB_M2)) mem2 (seg_rom SEGS))) ->
sb_env E regsc regs -> ew E 81 = Z_to_bv 64 (if pa =? 0 then 0x22480 else pa) ->
sb_inv ly S W mem md (spZ regs) R O W2 mem2 md2 ly2 S2 (k + 2) O2 [sarg verb; canon line] rd2
  (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg verb) + XM_ARG_LINE MT line)
  (LIVE_XSTRDUP (sarg port_a) + LIVE_XSTRDUP (sarg port_b) +
   LIVE_ANSWER (snd (sup_connect_m R verb line port_a port_b)))
  (LIVE_XSTRDUP (sarg verb) + LIVE_ARG_LINE line) ->
sb_sstr (ablocks B ly2 S2) (rdW W2 mem2) pa port_a ->
sb_sstr (ablocks B ly2 S2) (rdW W2 mem2) pb port_b ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + SB_M2)) mem2 (seg_rom SEGS)) md2)
  (scn_post B MT ly S W regs mem md verb line port_a port_b R O (snd (sup_connect_m R verb line port_a port_b))).

(* the walk from the first meeting point 0x8ade8 to the second: xstrdup(verb), the two stores, arg_line,
   and the port_a null check *)
Definition SB1_stmt : Prop :=
forall ly S (W : world SEGS) regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc (Wc : world SEGS) regsc memc
  mdc k c O1 E (W1 : world SEGS) regs1 mem1 md1 ly1 S1 O1b (rd1 : reader),
sb_cx ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1 ->
st_ok_pi SEGS VAL E sb_C1 (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + SB_M1)) mem1 (seg_rom SEGS))) ->
sb_env E regsc regs -> ew E 42 = Z_to_bv 64 (if pv =? 0 then 0x22480 else pv) ->
sb_inv ly S W mem md (spZ regs) R O W1 mem1 md1 ly1 S1 k O1b [] rd1
  (rec_spill_frees R * mo_free MT)
  (LIVE_XSTRDUP (sarg verb) + LIVE_ARG_LINE line + LIVE_XSTRDUP (sarg port_a) + LIVE_XSTRDUP (sarg port_b) +
   LIVE_ANSWER (snd (sup_connect_m R verb line port_a port_b)))
  0 ->
(* the verb keeps the statement's str_arg form: a live block or a read-only literal of the image *)
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) [] pv verb ->
sb_sstr (ablocks B ly1 S1) (rdW W1 mem1) pl (Some line) ->
sb_sstr (ablocks B ly1 S1) (rdW W1 mem1) pa port_a ->
sb_sstr (ablocks B ly1 S1) (rdW W1 mem1) pb port_b ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SB_M1)) mem1 (seg_rom SEGS)) md1)
  (scn_post B MT ly S W regs mem md verb line port_a port_b R O (snd (sup_connect_m R verb line port_a port_b))).

Lemma sb_recb_rng : forall lyi Si (Wi : world SEGS) memi mdi Oi a, AR SEGS B lyi Si Wi memi mdi ->
sb_recb (ablocks B lyi Si) Oi a -> 0 <= a < 2 ^ 64.
Proof.
intros lyi Si Wi memi mdi Oi a HAR [Ha | [Ha | ([q m] & Hq & _ & Ha)]];
[unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
cbn [fst snd] in Ha. pose proof asan_consts as (C1 & _).
destruct (sb_in_blk_range _ _ _ _ _ q m a HAR Hq Ha) as (H1 & H2 & _). lia.
Qed.
Lemma sb_ro_sub : forall r, subregion (sb_ro r) r.
Proof.
intros r. unfold subregion, sb_ro. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia | intros c Hc; exact Hc].
Qed.
Lemma sb_ro_submem : forall rs, submem (map sb_ro rs) rs.
Proof.
induction rs as [|r rs IH]; cbn [map]; [apply submem_nil | apply submem_keep; [apply sb_ro_sub | exact IH]].
Qed.
Lemma sb_ro_wf : forall rs, regions_wf rs = true -> regions_wf (map sb_ro rs) = true.
Proof.
induction rs as [|r rs IH]; cbn [map regions_wf]; [reflexivity|]. intros H.
apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; [|exact (IH H2)].
unfold region_wf, sb_ro in H1 |- *.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in H1 |- *.
apply andb_true_iff in H1 as [H3 H4]. apply andb_true_iff in H3 as [H5 _].
apply andb_true_iff. split; [|exact H4]. apply andb_true_iff. split; [exact H5|].
apply orb_true_iff. left. apply Z.leb_refl.
Qed.
Lemma sb_ro_state : forall E ss ms, st_ok_pi SEGS VAL E ss ms ->
st_ok_pi SEGS VAL E (sb_setmem ss (map sb_ro (ss_mem ss))) ms.
Proof.
intros E ss ms HS. unfold st_ok_pi in HS |- *.
pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS) as (Hwf & _ & _).
pose proof (st_ok_submem SEGS E (abs_ss VAL ss) ms (map sb_ro (ss_mem ss)) HS
  ltac:(destruct ss; apply sb_ro_submem) ltac:(apply sb_ro_wf; destruct ss; exact Hwf)) as H.
destruct ss. exact H.
Qed.

Ltac sb_name_ms HS nm :=
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into nm
| st_ok _ _ _ (restrict _ ?m) => rename m into nm
end.
Ltac sb_set_md nm :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (nm := mdx) in *; clearbody nm end.

Lemma sb_seg3 : SCN_T_stmt B MT -> SB3_stmt.
Proof.
intros SCNT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
  E W3 regs3 mem3 md3 ly3 S3 O3 rd3 HCX HS HENV E113 HINV HSB.
set (t := snd (sup_connect_m R verb line port_a port_b)) in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HCX as (HPRE & HMID).
pose proof HPRE as (HPRE0 & HFRM & Hfr8 & HROD & HRO & H10 & Hpv64 & H11 & Hpl64 & H12 & Hpa64 & H13 & Hpb64 &
  HSV & HSVT & HSL & HSA & HSB0 & HREP0 & Hev & Hlive & HMOK).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJc & Hk & Hslot & Hpos & HRJ & HFR & HREC & HO1O & HO1c & HOO1 & HcS & HSc & Hfrsc & Hbbc & MLEc).
pose proof HRJ as (Rsp & R8 & R22 & R21 & R20 & R19 & R9 & R3 & R4 & Rhi).
pose proof HINV as (HJ3 & Hfr3 & Hbb3 & Hlv3 & MLE3 & HREP3 & HK3 & HBK3).
destruct HENV as (HEI & HE0).
pose proof (sb_O_facts ly S W mem md _ R O HAR HREP0) as HOf.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn H; exact (proj1 (HOf pn H))).
assert (HOpos : Forall (fun pn => 0 < fst pn) O) by (apply Forall_forall; intros pn H; pose proof (HOf pn H); lia).
destruct (scn_slot_facts c Hslot) as (Hc8 & Hcr & Hcin).
assert (Hcr' : 0x5e3740 <= c < 0x5e3c18) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcr; lia).
pose proof sb_stk as FFS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite HE0 by lia. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 9)%nat -> ew E (32 + j) = getr regs (Z_to_bv 5 (nth j scn_saved 0))).
{ intros j Hj. rewrite HE0 by lia. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  unfold scn_extra_m. do 9 (destruct j as [|j]; [reflexivity|]). lia. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 80) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
assert (E8 : ew E 8 = w64 c) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (U8 : bv_unsigned (ew E 8) = c) by (rewrite E8; apply unsigned_lit_small; lia).
assert (E22 : ew E 22 = Z_to_bv 64 SCN_SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
pose proof (sb_shok ly3 S3 W3 mem3 md3 E c (proj1 HJ3) Hslot U8 E22) as SHOK.
(* 0x8ae9c .. 0x8aea0: a0 := s1, the call of xstrdup *)
paj_run_tok RUN HS HJ3 SHOK scn_Bspan.
{ awr_ok_tac. }
sb_set_md mdv1. sb_name_ms HS ms1.
pose proof (kept_of_frame (segs:=SEGS) E _ (w_H W3) mem3 (ms_mem ms1) (fun _ => False) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KEEP0.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.

assert (Hsp1 : spZ (ms_regs ms1) = spZ regs + -80) by (unfold spZ at 1; rewrite P2, U2; lia).
assert (Hgp1 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (Htp1 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (HnevJ : st_nev S3 + EV_XSTRDUP <= EV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev & _). clear - Hnev Hev Hk.
  unfold EV_SUP_CONNECT, EV_ANSWER, EV_HAND_BACK, EV_ARG_LINE, EV_REC_CANONICAL, EV_XSTRDUP in *. lia. }
assert (HXA : sb_xarg (ablocks B ly3 S3) (rdW W3 (ms_mem ms1)) (if pb =? 0 then 0x22480 else pb) port_b).
{ apply sb_xarg_of. apply (sb_sstr_keep _ _ (rdW W3 mem3) _ _ _ HSB); [tauto|].
  intros a (q & m & Hq & Ha). destruct (sb_in_blk_range _ _ _ _ _ q m a (proj1 HJ3) Hq Ha) as (Ha1 & Ha2 & _).
  apply KEEP0; [lia | tauto]. }
assert (HLIVE : blocks_bytes S3 + LIVE_XSTRDUP (sarg port_b) <= LIVE_MAX).
{ assert (0 <= LIVE_ANSWER t) by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP; lia). lia. }
assert (HMOK3 : mo_ok MT S3 (XM_XSTRDUP MT (sarg port_b))).
{ pose proof (mo_free_nonneg MT MTL) as M0.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg port_b)) + 1) ltac:(lia)) as M1b.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)) as M1t.
  apply (mok_station MT S S3 (XM_SUP_CONNECT MT R verb line port_a port_b t) _ (XM_XSTRDUP MT (sarg port_b)) MTL HMOK MLE3);
  unfold XM_SUP_CONNECT, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP in *; lia. }
eapply (sb_xcall _ (spZ regs) (scn_FP O) ly S W mem md W3 (ms_regs ms1) (ms_mem ms1) mdv1 ly3 S3 (k + 3)
  (if pb =? 0 then 0x22480 else pb) port_b HJ3 Hsp1 Hgp1 Htp1).
{ rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ rewrite P1, unsigned_lit_small by lia. lia. }
{ unfold s0Z. rewrite P8, U8. lia. }
{ rewrite P10, E113. reflexivity. }
{ exact (sb_arod _ _ O ly S W mem md [] ly3 S3 W3 (ms_mem ms1) mdv1 (k + 3) HAR HOin HOpos HJ3 HROD). }
{ exact HXA. }
{ exact HnevJ. }
{ exact HLIVE. }
{ exact HMOK3. }
intros ly4 S4 W4 regs4 mem4 md4 p HJ4 HJ4c HP4 Hp10 [Hp4096 Hp64] Hperm Hfresh Hpblk Hpstr Hxbb Hmle.
rewrite P1.
(* back at 0x8aea4: c->nargs and the stack frame are kept; c->args[2]'s region is dropped *)
jafter_call_keep_pi HS 128%nat regs4 (mrestrict (w_H W4) mem4) HP4 [1; 2]%nat HS4.
match type of HS4 with ?T -> _ => assert (HRK : T); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
  - apply (sb_slot_kept E W3 W4 (ms_mem ms1) mem4 c 4 8 4 4 _ XSTRDUP_STK (spZ regs + -80) [] ly3 S3 mdv1 ly4 S4 md4
      EV_XSTRDUP HJ4c U8 Hslot); try (unfold CALL_SIZE; lia).
    + intros b Hb. destruct (inFP_nil b Hb).
    + intros a _ Ha. exact (inFP_nil a Ha).
  - eapply (region_kept_stack_sub SEGS B E XSTRDUP_STK (spZ regs + -80) [] ly3 S3 W3 (ms_mem ms1) mdv1 ly4 S4 W4 mem4
      md4 EV_XSTRDUP 2 0 80 0 0 _ (spZ regs - 80) SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] _ HJ4c HJ4 U2);
    [lia | lia | lia | lia | lia | intros a _ Ha; exact (inFP_nil a Ha)]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E 128 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD4 : forall n, (n < 128)%nat -> ew E4 n = ew E n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
assert (E132 : ew E4 132 = getr regs4 10%bv) by (rewrite HE4; unfold havoc; cbn [ew]; reflexivity).
clear HE4.
assert (U84 : bv_unsigned (ew E4 8) = c) by (rewrite OLD4 by lia; exact U8).
assert (U24 : bv_unsigned (ew E4 2) = spZ regs - 80) by (rewrite OLD4 by lia; exact U2).
pose proof (proj1 HJ4) as HAR4.
(* c->nargs becomes writable, and c->args[3] a writable region *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_region_nth E4 ssx (restrict (w_H W4) msx) 0 (sb_nargs false 3) HS ltac:(vm_compute; reflexivity))
    as HRn0 end.
cbn [ms_mem restrict mkst] in HRn0.
assert (VN : val_mem SEGS (mrestrict (w_H W4) mem4) (c + 4) 4 3).
{ exact (field_of_region E4 _ 8 c _ 4 8 4 4 4 4 (SLit 3) 3 HRn0 U84 ltac:(left; reflexivity) eq_refl
    ltac:(cbn; lia) ltac:(lia)). }
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (ast_ok_pi_set_region E4 ssx msx 0 (sb_nargs false 3) (sb_nargs true 3) HS ltac:(vm_compute; reflexivity)
    eq_refl ltac:(vm_compute; reflexivity)) as HS5 end.
match type of HS5 with ?P -> _ => assert (HRn : P); [|specialize (HS5 HRn); clear HRn] end.
{ cbn [ms_mem restrict mkst]. unfold region_ok, sb_nargs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U84. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (scn_pg_writable B PROG_WRITABLE ly4 S4 W4 mem4 md4 _ HAR4). apply Hcin. unfold CALL_SIZE. lia.
  - constructor; [|constructor]. apply (chunk_ok_val SEGS E4 _ c 4 4 (SLit 3) 3); [reflexivity | cbn; lia | lia | exact VN]. }
clear HS. rename HS5 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (st_ok_pi_add_region E4 ssx msx (sb_arg 3 true []) HS ltac:(vm_compute; reflexivity)) as HS6 end.
match type of HS6 with ?P1 -> ?P2 -> _ =>
  assert (HA1 : P1); [|assert (HA2 : P2); [|specialize (HS6 HA1 HA2); clear HA1 HA2]] end.
{ cbn [ms_mem restrict mkst]. unfold region_ok, sb_arg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U84. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (scn_pg_writable B PROG_WRITABLE ly4 S4 W4 mem4 md4 _ HAR4). apply Hcin. unfold CALL_SIZE. lia. }
{ cbn [ss_mem list_upd all_disjoint]. unfold extent_disjoint, sb_arg, sb_nargs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U84, U24. repeat split; lia. }
clear HS. rename HS6 into HS.
assert (E224 : ew E4 22 = Z_to_bv 64 SCN_SB) by (rewrite OLD4 by lia; exact E22).
pose proof (sb_shok ly4 S4 W4 mem4 md4 E4 c HAR4 Hslot U84 E224) as SHOK4.
(* 0x8aea4 .. 0x8af0c: c->nargs := 4, c->args[3] := the copy, the epilogue, the jump into answer *)
paj_run_tok RUN HS HJ4 SHOK4 scn_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply sb_awr_slot; [reflexivity | exact U84 | exact Hslot | cbn; lia | cbn; unfold CALL_SIZE; lia |].
  eapply sb_awr_slot; [reflexivity | exact U84 | exact Hslot | cbn; lia | cbn; unfold CALL_SIZE; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
sb_set_md mdv2. sb_name_ms HS ms5.
pose proof (kept_of_frame (segs:=SEGS) E4 _ (w_H W4) mem4 (ms_mem ms5) (fun a => c + 4 <= a < c + 8 \/ c + 32 <= a < c + 40) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U84, ?U24 in Hrr; lia|]);
        destruct Hin)) as KEEP5.
clear HF HFr HG.
pmkst HS.

rewrite sb_sig_ans.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
pose proof (proj1 HJ3) as HAR3.
assert (HpIn : In (p, LIVE_XSTRDUP (sarg port_b)) (ablocks B ly4 S4))
by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
pose proof (sb_sarg_len _ _ _ _ HSB) as Hxl.
pose proof (blk_off_imgP B ly4 S4 W4 mem4 md4 _ _ HAR4 HpIn) as Hpoff. unfold off_img in Hpoff.
destruct (al_blocks _ _ LAWS ly4 S4 W4 mem4 md4 _ _ HAR4 HpIn) as (_ & _ & Hpceil & _).
pose proof (req_size_pos (LIVE_XSTRDUP (sarg port_b)) ltac:(unfold LIVE_XSTRDUP; lia)) as [_ Hpreq].
unfold LIVE_XSTRDUP in Hpoff, Hpceil, Hpreq.
(* the two fields the run wrote *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_region_nth E4 ssx (restrict (w_H W4) msx) 0
    (sb_arg 3 true [YP09.mkChunk 32 (CVal 8 (SOff 132 0))]) HS ltac:(vm_compute; reflexivity)) as HRa;
  pose proof (st_ok_region_nth E4 ssx (restrict (w_H W4) msx) 1 (sb_nargs true 4) HS ltac:(vm_compute; reflexivity))
    as HRn end.
cbn [ms_mem restrict] in HRa, HRn.
pose proof (field_of_region E4 _ 8 c _ 4 8 4 8 4 4 (SLit 4) 4 HRn U84 ltac:(left; reflexivity) eq_refl
  ltac:(cbn; lia) ltac:(lia)) as VN4.
pose proof (field_of_region E4 _ 8 c _ 32 40 32 40 32 8 (SOff 132 0) p HRa U84 ltac:(left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite E132, Hp10, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
  ltac:(cbn; lia) ltac:(lia)) as VA4.
change (N.to_nat 4) with 4%nat in VN4. change (N.to_nat 8) with 8%nat in VA4.
(* the recorder's bytes outside the two fields are those of xstrdup's call site *)
assert (KREC : forall a, sb_recb (ablocks B ly3 S3) O3 a ->
  ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
  ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg verb; canon line; sarg port_a]) <= a <
     c + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg verb; canon line; sarg port_a]) + 8) ->
  rdW W4 (ms_mem ms5) a = rd3 a).
{ intros a Ha Hn1 Hn2. change (Z.of_nat (length [sarg verb; canon line; sarg port_a])) with 3 in Hn2.
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hn1, Hn2.
  assert (Hrng : 0 <= a < 2 ^ 64 /\ ~ (c + 4 <= a < c + 8 \/ c + 32 <= a < c + 40) /\ (inFP cmd_PG a \/
    exists q m, In (q, m) (ablocks B ly3 S3) /\ In (q, m) (ablocks B ly4 S4) /\ q <= a < q + m)).
  { destruct Ha as [Ha | [Ha | ([q m] & Hq & HqO & Ha)]].
    - split; [unfold A_G_REC, REC_SIZE in Ha; lia|]. split; [lia|]. left; apply sb_recb_static; left; exact Ha.
    - split; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|]. split; [lia|]. left; apply sb_recb_static; right; exact Ha.
    - cbn [fst snd] in Ha. destruct (sb_in_blk_range _ _ _ _ _ q m a HAR3 Hq Ha) as (Ha1 & Ha2 & Ha3).
      split; [lia|]. split; [lia|]. right. exists q, m. split; [exact Hq|]. split; [|exact Ha].
      eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hq]. }
  destruct Hrng as (Hrng & Hnf & Hwhere).
  rewrite (KEEP5 a Hrng Hnf).
  rewrite (sb_call_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ4c ltac:(intros b Hb; destruct (inFP_nil b Hb))
    ltac:(destruct Hwhere as [Hw | Hw]; [left; split; [exact Hw | apply inFP_nil] | right; exact Hw])).
  rewrite (KEEP0 a Hrng ltac:(tauto)). exact (HK3 a Ha). }
assert (HREP4 : rec_repA B ly4 S4 (rdW W4 (ms_mem ms5))
  (rec_record R REC_CONNECT ([sarg verb; canon line; sarg port_a] ++ [sarg port_b]))
  ((p, LIVE_XSTRDUP (sarg port_b)) :: O3)).
{ apply (scn_append_rep B ly3 S3 ly4 S4 rd3 (rdW W4 (ms_mem ms5)) R REC_CONNECT [sarg verb; canon line; sarg port_a] O3 c
    (sarg port_b) p (LIVE_XSTRDUP (sarg port_b)) HREP3 Hpos).
  - cbn. lia.
  - lia.
  - apply (scn_str_keep (rdW W4 mem4)); [exact Hpstr|]. intros i Hi. apply KEEP5; [lia|].
    unfold CALL_SIZE in Hcr'. lia.
  - exact Hxl.
  - unfold LIVE_XSTRDUP. lia.
  - exact Hfresh.
  - unfold iv_apart, A_G_REC, REC_SIZE, LIVE_XSTRDUP. lia.
  - unfold iv_apart, A_REC_SPILL, SC_SIZE, LIVE_XSTRDUP. lia.
  - change (Z.of_nat (length [sarg verb; canon line; sarg port_a]) + 1) with 4. unfold CALL_OFF_NARGS.
    exact (scn_aval_of_val_mem SEGS _ _ _ _ _ VN4).
  - change (Z.of_nat (length [sarg verb; canon line; sarg port_a])) with 3. unfold CALL_OFF_ARGS.
    replace (c + 8 + 8 * 3) with (c + 32) by lia. exact (scn_aval_of_val_mem SEGS _ _ _ _ _ VA4).
  - exact KREC.
  - exact Hperm. }
(* the block bookkeeping *)
assert (Hnew : In (p, LIVE_XSTRDUP (sarg port_b)) (ablocks B ly S) -> In (p, LIVE_XSTRDUP (sarg port_b)) O).
{ intros Hin. apply (sb_new_in_O ly S W mem md O [] ly3 S3 W3 (ms_mem ms1) mdv1 (k + 3) (spZ regs) SUP_CONNECT_STK
    p _ HAR HOin HJ3); [|exact Hin].
  intros Hin3. pose proof (proj1 (Forall_forall _ _) Hfresh _ Hin3) as Hap. unfold iv_apart, LIVE_XSTRDUP in Hap.
  cbn [fst snd] in Hap. lia. }
pose proof (sb_bk_step ly S O _ _ O3 p _ HBK3 Hperm Hnew) as (BK1 & BK2 & BK3).
(* the registers at answer's entry *)
assert (R3' : getr regsc (Z_to_bv 5 3) = getr regs (Z_to_bv 5 3))
by (replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact R3).
assert (R4' : getr regsc (Z_to_bv 5 4) = getr regs (Z_to_bv 5 4))
by (replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact R4).
assert (HPT : aregs_preserved regs (ms_regs ms5)).
{ unfold aregs_preserved. intros r Hr. unfold acallee_saved in Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by lia.
  clear Hr. repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases].
  all: rewrite (st_ok_restrict_reg SEGS (w_H W4) E4 _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
      let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
  1: { rewrite U24. replace (spZ regs - 80 + 80) with (spZ regs) by lia. unfold spZ.
    replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). apply Z_to_bv_bv_unsigned. }
  1: { rewrite OLD4 by lia. rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl). exact R3'. }
  1: { rewrite OLD4 by lia. rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl). exact R4'. }
  all: lazymatch goal with
    | |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) =>
      rewrite (OLD4 n) by lia;
      first [ let j := eval compute in (n - 32)%nat in
              pose proof (EX j ltac:(lia)) as X; cbn [Nat.add nth scn_saved] in X; exact X
            | rewrite (EE n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia ]
    end. }
assert (HPT1 : getr (ms_regs ms5) 1 = getr regs 1).
{ rewrite Q1, OLD4 by lia. pose proof (EX 0%nat ltac:(lia)) as X. cbn [Nat.add nth scn_saved] in X. rewrite X.
  replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). reflexivity. }
assert (Hsp5 : spZ (ms_regs ms5) = spZ regs).
{ unfold spZ. pose proof (HPT 2 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 2) with (2%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. reflexivity. }
assert (Hs05 : s0Z (ms_regs ms5) = s0Z regs).
{ unfold s0Z. pose proof (HPT 8 ltac:(unfold acallee_saved; lia)) as X.
  replace (Z_to_bv 5 8) with (8%bv : bv 5) in X by (apply bv_eq; reflexivity). rewrite X. reflexivity. }
assert (HFPhi : forall a, alloc_ceiling <= a -> ~ inFP (scn_FP O) a).
{ intros a Ha Hin. destruct (sb_fp_cases O a Hin) as [Hpg | Hb].
  - pose proof (sb_pg_range a Hpg) as Hr. unfold A_G_REC, A_G_QUITTING in Hr. lia.
  - destruct (inFP_ablocks_fp_inv _ a Hb) as (q & m & Hqm & Hr).
    destruct (al_blocks _ _ LAWS ly S W mem md q m HAR (HOin _ Hqm)) as (_ & _ & Hqc & _). lia. }
pose proof HJ4 as (_ & Hly4 & _). pose proof Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & ET & _).
pose proof HJ4c as (_ & _ & _ & _ & _ & Hfr4 & _).
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms5)))
by exact (sb_arod _ _ O ly S W mem md [] ly4 S4 W4 (ms_mem ms5) mdv2 _ HAR HOin HOpos HJ4 HROD).
apply (SCNT ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) mdv2
  (k + 3 + EV_XSTRDUP) c ((p, LIVE_XSTRDUP (sarg port_b)) :: O3) HPRE).
unfold scn_tail.
change (snd (sup_connect_m R verb line port_a port_b)) with t.
split; [exact HJ4|].
split; [unfold EV_SCN_ARGS, EV_ARG_LINE, EV_REC_CANONICAL, EV_XSTRDUP; lia|].
split; [exact Hsp5|].
split; [exact HPT1|].
split; [exact HPT|].
split; [rewrite Q3, OLD4, (EE 3%nat 3%bv eq_refl), R3 by lia; exact Hgp|].
split; [rewrite Q4, OLD4, (EE 4%nat 4%bv eq_refl), R4 by lia; exact Htp|].
split; [rewrite Q10, OLD4 by lia; exact E8|].
split; [rewrite Q11; apply bv_eq; rewrite (HEI4 283%nat ltac:(unfold A_TEXT, A_LIM; lia));
  change (VAL 283%nat) with (VAL (A_OBJ 42)); rewrite (scn_obj42 VOBJS); rewrite unsigned_lit_small by lia; reflexivity|].
split; [rewrite Q12; reflexivity|].
split.
{ rewrite Hsp5, Hs05. apply (achain_ly_top ly ly4); [exact ET|].
  apply (achain_kept ly (rdW W mem) (rdW W4 (ms_mem ms5)) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. exact (aview_above_of_journal B SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] ly4 S4 W4
    (ms_mem ms5) mdv2 _ HJ4 a Ha (HFPhi a ltac:(lia))). }
split; [exact Hpos|].
split; [exact HREP4|].
split; [exact BK1|]. split; [exact BK2|]. split; [exact BK3|].
split; [rewrite Hfr4; exact Hfr3|].
(* the live bytes: the three copied so far (sb_inv's lv) and port_b's copy *)
split; [unfold LIVE_SCN_ARGS; clear - Hxbb Hlv3; lia|].
split; [unfold XM_SCN_ARGS; exact (mle_station MT S S3 S4 _ _ MTL MLE3 Hmle)|].
split; [exact HROD5|].
exact (cmd_ro_ok_of_aro ly4 S4 W4 (ms_mem ms5) mdv2 (proj1 HJ4) HROD5).
Qed.

Lemma sb_seg2 : SB3_stmt -> SB2_stmt.
Proof.
intros SB3 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
  E W2 regs2 mem2 md2 ly2 S2 O2 rd2 HCX HS HENV E81 HINV HSA HSB.
set (t := snd (sup_connect_m R verb line port_a port_b)) in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCX as (HPRE & HMID).
pose proof HPRE as (HPRE0 & HFRM & Hfr8 & HROD & HRO & H10 & Hpv64 & H11 & Hpl64 & H12 & Hpa64 & H13 & Hpb64 &
  HSV & HSVT & HSL & HSA0 & HSB0 & HREP0 & Hev & Hlive & HMOK).
pose proof HPRE0 as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJc & Hk & Hslot & Hpos & HRJ & HFR & HREC & HO1O & HO1c & HOO1 & HcS & HSc & Hfrsc & Hbbc & MLEc).
pose proof HRJ as (Rsp & R8 & R22 & R21 & R20 & R19 & R9 & R3 & R4 & Rhi).
pose proof HINV as (HJ2 & Hfr2 & Hbb2 & Hlv2 & MLE2 & HREP2 & HK2 & HBK2).
pose proof HENV as (HEI & HE0).
pose proof (sb_O_facts ly S W mem md _ R O HAR HREP0) as HOf.
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
assert (E9 : ew E 9 = w64 pb) by (rewrite (EE 9%nat 9%bv eq_refl), R9; exact H13).
pose proof (sb_shok ly2 S2 W2 mem2 md2 E c (proj1 HJ2) Hslot U8 E22) as SHOK.
(* 0x8ae50 .. 0x8ae54: a0 := s3, the call of xstrdup *)
paj_run_tok RUN HS HJ2 SHOK scn_Bspan.
{ awr_ok_tac. }
sb_set_md mdv1. sb_name_ms HS ms1.
pose proof (kept_of_frame (segs:=SEGS) E _ (w_H W2) mem2 (ms_mem ms1) (fun _ => False) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KEEP0.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (Hsp1 : spZ (ms_regs ms1) = spZ regs + -80) by (unfold spZ at 1; rewrite P2, U2; lia).
assert (Hgp1 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (Htp1 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (HnevJ : st_nev S2 + EV_XSTRDUP <= EV_MAX).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev & _). clear - Hnev Hev Hk.
  unfold EV_SUP_CONNECT, EV_ANSWER, EV_HAND_BACK, EV_ARG_LINE, EV_REC_CANONICAL, EV_XSTRDUP in *. lia. }
assert (HXA : sb_xarg (ablocks B ly2 S2) (rdW W2 (ms_mem ms1)) (if pa =? 0 then 0x22480 else pa) port_a).
{ apply sb_xarg_of. apply (sb_sstr_keep _ _ (rdW W2 mem2) _ _ _ HSA); [tauto|].
  intros a (q & m & Hq & Ha). destruct (sb_in_blk_range _ _ _ _ _ q m a (proj1 HJ2) Hq Ha) as (Ha1 & Ha2 & _).
  apply KEEP0; [lia | tauto]. }
assert (HLIVE : blocks_bytes S2 + LIVE_XSTRDUP (sarg port_a) <= LIVE_MAX).
{ assert (0 <= LIVE_ANSWER t) by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP; lia).
  assert (0 <= LIVE_XSTRDUP (sarg port_b)) by (unfold LIVE_XSTRDUP; lia). lia. }
assert (HMOK2 : mo_ok MT S2 (XM_XSTRDUP MT (sarg port_a))).
{ pose proof (mo_free_nonneg MT MTL) as M0.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg port_a)) + 1) ltac:(lia)) as M1a.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg port_b)) + 1) ltac:(lia)) as M1b.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)) as M1t.
  apply (mok_station MT S S2 (XM_SUP_CONNECT MT R verb line port_a port_b t) _ (XM_XSTRDUP MT (sarg port_a)) MTL HMOK MLE2);
  unfold XM_SUP_CONNECT, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP in *; lia. }
eapply (sb_xcall _ (spZ regs) (scn_FP O) ly S W mem md W2 (ms_regs ms1) (ms_mem ms1) mdv1 ly2 S2 (k + 2)
  (if pa =? 0 then 0x22480 else pa) port_a HJ2 Hsp1 Hgp1 Htp1).
{ rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ rewrite P1, unsigned_lit_small by lia. lia. }
{ unfold s0Z. rewrite P8, U8. lia. }
{ rewrite P10, E81. reflexivity. }
{ exact (sb_arod _ _ O ly S W mem md [] ly2 S2 W2 (ms_mem ms1) mdv1 (k + 2) HAR HOin HOpos HJ2 HROD). }
{ exact HXA. }
{ exact HnevJ. }
{ exact HLIVE. }
{ exact HMOK2. }
intros ly4 S4 W4 regs4 mem4 md4 p HJ4 HJ4c HP4 Hp10 [Hp4096 Hp64] Hperm Hfresh Hpblk Hpstr Hxbb Hmle.
rewrite P1.
(* back at 0x8ae58: c->nargs and the frame are kept *)
jafter_call_keep_pi HS 96%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS4.
match type of HS4 with ?T -> _ => assert (HRK : T); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
  - apply (sb_slot_kept E W2 W4 (ms_mem ms1) mem4 c 4 8 4 4 _ XSTRDUP_STK (spZ regs + -80) [] ly2 S2 mdv1 ly4 S4 md4
      EV_XSTRDUP HJ4c U8 Hslot); try (unfold CALL_SIZE; lia).
    + intros b Hb. destruct (inFP_nil b Hb).
    + intros a _ Ha. exact (inFP_nil a Ha).
  - eapply (region_kept_stack_sub SEGS B E XSTRDUP_STK (spZ regs + -80) [] ly2 S2 W2 (ms_mem ms1) mdv1 ly4 S4 W4 mem4
      md4 EV_XSTRDUP 2 0 80 0 0 _ (spZ regs - 80) SUP_CONNECT_STK (spZ regs) (scn_FP O) ly S W mem md [] _ HJ4c HJ4 U2);
    [lia | lia | lia | lia | lia | intros a _ Ha; exact (inFP_nil a Ha)]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E 96 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD4 : forall n, (n < 96)%nat -> ew E4 n = ew E n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
assert (E100 : ew E4 100 = getr regs4 10%bv) by (rewrite HE4; unfold havoc; cbn [ew]; reflexivity).
clear HE4.
assert (U84 : bv_unsigned (ew E4 8) = c) by (rewrite OLD4 by lia; exact U8).
assert (U24 : bv_unsigned (ew E4 2) = spZ regs - 80) by (rewrite OLD4 by lia; exact U2).
pose proof (proj1 HJ4) as HAR4.
(* c->nargs becomes writable and c->args[2] a writable region *)
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_region_nth E4 ssx (restrict (w_H W4) msx) 0 (sb_nargs false 2) HS ltac:(vm_compute; reflexivity))
    as HRn0 end.
cbn [ms_mem restrict mkst] in HRn0.
assert (VN : val_mem SEGS (mrestrict (w_H W4) mem4) (c + 4) 4 2).
{ exact (field_of_region E4 _ 8 c _ 4 8 4 4 4 4 (SLit 2) 2 HRn0 U84 ltac:(left; reflexivity) eq_refl
    ltac:(cbn; lia) ltac:(lia)). }
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (ast_ok_pi_set_region E4 ssx msx 0 (sb_nargs false 2) (sb_nargs true 2) HS ltac:(vm_compute; reflexivity)
    eq_refl ltac:(vm_compute; reflexivity)) as HS5 end.
match type of HS5 with ?P -> _ => assert (HRn : P); [|specialize (HS5 HRn); clear HRn] end.
{ cbn [ms_mem restrict mkst]. unfold region_ok, sb_nargs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U84. split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (scn_pg_writable B PROG_WRITABLE ly4 S4 W4 mem4 md4 _ HAR4). apply Hcin. unfold CALL_SIZE. lia.
  - constructor; [|constructor]. apply (chunk_ok_val SEGS E4 _ c 4 4 (SLit 2) 2); [reflexivity | cbn; lia | lia | exact VN]. }
clear HS. rename HS5 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (st_ok_pi_add_region E4 ssx msx (sb_arg 2 true []) HS ltac:(vm_compute; reflexivity)) as HS6 end.
match type of HS6 with ?P1 -> ?P2 -> _ =>
  assert (HA1 : P1); [|assert (HA2 : P2); [|specialize (HS6 HA1 HA2); clear HA1 HA2]] end.
{ cbn [ms_mem restrict mkst]. unfold region_ok, sb_arg.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U84. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (scn_pg_writable B PROG_WRITABLE ly4 S4 W4 mem4 md4 _ HAR4). apply Hcin. unfold CALL_SIZE. lia. }
{ cbn [ss_mem list_upd all_disjoint]. unfold extent_disjoint, sb_arg, sb_nargs.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U84, U24. repeat split; lia. }
clear HS. rename HS6 into HS.
assert (E224 : ew E4 22 = Z_to_bv 64 SCN_SB) by (rewrite OLD4 by lia; exact E22).
pose proof (sb_shok ly4 S4 W4 mem4 md4 E4 c HAR4 Hslot U84 E224) as SHOK4.
(* 0x8ae58 .. 0x8ae90: c->nargs := 3, c->args[2] := the copy, then the null check of port_b *)
paj_run_tok RUN HS HJ4 SHOK4 scn_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply sb_awr_slot; [reflexivity | exact U84 | exact Hslot | cbn; lia | cbn; unfold CALL_SIZE; lia |].
  eapply sb_awr_slot; [reflexivity | exact U84 | exact Hslot | cbn; lia | cbn; unfold CALL_SIZE; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
sb_set_md mdv2. sb_name_ms HS ms5.
pose proof (kept_of_frame (segs:=SEGS) E4 _ (w_H W4) mem4 (ms_mem ms5) (fun a => c + 4 <= a < c + 8 \/ c + 24 <= a < c + 32) HFr
  ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U84, ?U24 in Hrr; lia|]);
        destruct Hin)) as KEEP5.
clear HF HFr HG.
(* the third argument is appended to the call *)
pose proof (proj1 HJ2) as HAR2.
assert (HpIn : In (p, LIVE_XSTRDUP (sarg port_a)) (ablocks B ly4 S4))
by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
pose proof (sb_sarg_len _ _ _ _ HSA) as Hxl.
pose proof (blk_off_imgP B ly4 S4 W4 mem4 md4 _ _ HAR4 HpIn) as Hpoff. unfold off_img in Hpoff.
destruct (al_blocks _ _ LAWS ly4 S4 W4 mem4 md4 _ _ HAR4 HpIn) as (_ & _ & Hpceil & _).
pose proof (req_size_pos (LIVE_XSTRDUP (sarg port_a)) ltac:(unfold LIVE_XSTRDUP; lia)) as [_ Hpreq].
unfold LIVE_XSTRDUP in Hpoff, Hpceil, Hpreq.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_region_nth E4 ssx (restrict (w_H W4) msx) 0
    (sb_arg 2 true [YP09.mkChunk 24 (CVal 8 (SOff 100 0))]) HS ltac:(vm_compute; reflexivity)) as HRa;
  pose proof (st_ok_pi_region_nth E4 ssx (restrict (w_H W4) msx) 1 (sb_nargs true 3) HS ltac:(vm_compute; reflexivity))
    as HRn end.
cbn [ms_mem restrict] in HRa, HRn.
pose proof (field_of_region E4 _ 8 c _ 4 8 4 8 4 4 (SLit 3) 3 HRn U84 ltac:(left; reflexivity) eq_refl
  ltac:(cbn; lia) ltac:(lia)) as VN4.
pose proof (field_of_region E4 _ 8 c _ 24 32 24 32 24 8 (SOff 100 0) p HRa U84 ltac:(left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite E100, Hp10, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
  ltac:(cbn; lia) ltac:(lia)) as VA4.
change (N.to_nat 4) with 4%nat in VN4. change (N.to_nat 8) with 8%nat in VA4.
assert (KREC : forall a, sb_recb (ablocks B ly2 S2) O2 a ->
  ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4) ->
  ~ (c + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg verb; canon line]) <= a <
     c + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg verb; canon line]) + 8) ->
  rdW W4 (ms_mem ms5) a = rd2 a).
{ intros a Ha Hn1 Hn2. change (Z.of_nat (length [sarg verb; canon line])) with 2 in Hn2.
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hn1, Hn2.
  assert (Hrng : 0 <= a < 2 ^ 64 /\ ~ (c + 4 <= a < c + 8 \/ c + 24 <= a < c + 32) /\ (inFP cmd_PG a \/
    exists q m, In (q, m) (ablocks B ly2 S2) /\ In (q, m) (ablocks B ly4 S4) /\ q <= a < q + m)).
  { destruct Ha as [Ha | [Ha | ([q m] & Hq & HqO & Ha)]].
    - split; [unfold A_G_REC, REC_SIZE in Ha; lia|]. split; [lia|]. left; apply sb_recb_static; left; exact Ha.
    - split; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|]. split; [lia|]. left; apply sb_recb_static; right; exact Ha.
    - cbn [fst snd] in Ha. destruct (sb_in_blk_range _ _ _ _ _ q m a HAR2 Hq Ha) as (Ha1 & Ha2 & Ha3).
      split; [lia|]. split; [lia|]. right. exists q, m. split; [exact Hq|]. split; [|exact Ha].
      eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hq]. }
  destruct Hrng as (Hrng & Hnf & Hwhere).
  rewrite (KEEP5 a Hrng Hnf).
  rewrite (sb_call_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ4c ltac:(intros b Hb; destruct (inFP_nil b Hb))
    ltac:(destruct Hwhere as [Hw | Hw]; [left; split; [exact Hw | apply inFP_nil] | right; exact Hw])).
  rewrite (KEEP0 a Hrng ltac:(tauto)). exact (HK2 a Ha). }
assert (HREP4 : rec_repA B ly4 S4 (rdW W4 (ms_mem ms5))
  (rec_record R REC_CONNECT ([sarg verb; canon line] ++ [sarg port_a]))
  ((p, LIVE_XSTRDUP (sarg port_a)) :: O2)).
{ apply (scn_append_rep B ly2 S2 ly4 S4 rd2 (rdW W4 (ms_mem ms5)) R REC_CONNECT [sarg verb; canon line] O2 c
    (sarg port_a) p (LIVE_XSTRDUP (sarg port_a)) HREP2 Hpos).
  - cbn. lia.
  - lia.
  - apply (scn_str_keep (rdW W4 mem4)); [exact Hpstr|]. intros i Hi. apply KEEP5; [lia|].
    unfold CALL_SIZE in Hcr'. lia.
  - exact Hxl.
  - unfold LIVE_XSTRDUP. lia.
  - exact Hfresh.
  - unfold iv_apart, A_G_REC, REC_SIZE, LIVE_XSTRDUP. lia.
  - unfold iv_apart, A_REC_SPILL, SC_SIZE, LIVE_XSTRDUP. lia.
  - change (Z.of_nat (length [sarg verb; canon line]) + 1) with 3. unfold CALL_OFF_NARGS.
    exact (scn_aval_of_val_mem SEGS _ _ _ _ _ VN4).
  - change (Z.of_nat (length [sarg verb; canon line])) with 2. unfold CALL_OFF_ARGS.
    replace (c + 8 + 8 * 2) with (c + 24) by lia. exact (scn_aval_of_val_mem SEGS _ _ _ _ _ VA4).
  - exact KREC.
  - exact Hperm. }
assert (Hnew : In (p, LIVE_XSTRDUP (sarg port_a)) (ablocks B ly S) -> In (p, LIVE_XSTRDUP (sarg port_a)) O).
{ intros Hin. apply (sb_new_in_O ly S W mem md O [] ly2 S2 W2 (ms_mem ms1) mdv1 (k + 2) (spZ regs) SUP_CONNECT_STK
    p _ HAR HOin HJ2); [|exact Hin].
  intros Hin2. pose proof (proj1 (Forall_forall _ _) Hfresh _ Hin2) as Hap. unfold iv_apart, LIVE_XSTRDUP in Hap.
  cbn [fst snd] in Hap. lia. }
pose proof (sb_bk_step ly S O _ _ O2 p _ HBK2 Hperm Hnew) as HBK4.
pose proof HJ4c as (_ & _ & _ & _ & _ & Hfr4c & _).
assert (HROD4 : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms5)))
by exact (sb_arod _ _ O ly S W mem md [] ly4 S4 W4 (ms_mem ms5) mdv2 _ HAR HOin HOpos HJ4 HROD).
assert (HSBk : sb_sstr (ablocks B ly4 S4) (rdW W4 (ms_mem ms5)) pb port_b).
{ apply (sb_sstr_keep (ablocks B ly2 S2) _ (rdW W2 mem2) _ _ _ HSB).
  - intros pn Hpn. eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hpn].
  - intros a (q & m & Hq & Ha). destruct (sb_in_blk_range _ _ _ _ _ q m a HAR2 Hq Ha) as (Ha1 & Ha2 & Ha3).
    assert (Hr64 : 0 <= a < 2 ^ 64) by lia.
    assert (Hnf5 : ~ (c + 4 <= a < c + 8 \/ c + 24 <= a < c + 32)) by lia.
    rewrite (KEEP5 a Hr64 Hnf5).
    rewrite (sb_call_keep _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ4c ltac:(intros b Hb; destruct (inFP_nil b Hb))
      ltac:(right; exists q, m; split; [exact Hq | split; [eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; exact Hq] | exact Ha]])).
    apply KEEP0; [lia | tauto]. }
assert (Hbb4 : blocks_bytes S4 + (LIVE_XSTRDUP (sarg port_b) + LIVE_ANSWER t) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly4 S4), (bsum_perm _ _ Hperm), bsum_cons, <- (blocks_bytes_bsum B ly2 S2).
  cbn [snd]. lia. }
(* the live bytes copied so far: verb, line (sb_inv's lv) and port_a's copy *)
assert (Hlv4 : blocks_bytes S4 <= blocks_bytes S + (LIVE_XSTRDUP (sarg verb) + LIVE_ARG_LINE line + LIVE_XSTRDUP (sarg port_a)))
by (clear - Hxbb Hlv2; lia).
assert (MLE4 : mo_le MT S S4
  (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT (sarg verb) + XM_ARG_LINE MT line + XM_XSTRDUP MT (sarg port_a)))
by exact (mle_station MT S S2 S4 _ _ MTL MLE2 Hmle).
pose proof HJ4 as HJ4b.
replace (k + 2 + EV_XSTRDUP) with (k + 3) in HJ4 by (unfold EV_XSTRDUP; lia).
assert (Hpbrng : 0 <= pb < 2 ^ 64) by exact Hpb64.
assert (HU9 : U E4 (SOff 9 0) = pb)
by (apply (U_atom E4 9 pb); [rewrite OLD4 by lia; exact E9 | exact Hpbrng]).
assert (HU0 : U E4 (SLit 0) = 0) by reflexivity.
(* every region read-only: the two arms of the null check write nothing *)
pose proof (sb_ro_state E4 _ _ HS) as HSr. clear HS. rename HSr into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  let v := eval vm_compute in ssx in change ssx with v in HS end.
psrr_branch_tok RUN BR HS SHOK4 scn_Bspan.
- assert (Hpb : pb <> 0).
  { rewrite branch_ne_U, HU9, HU0 in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJ4 SHOK4 scn_Bspan SB_M3.
  { awr_ok_tac. }
  sb_set_md mdv3. sb_name_ms HS ms6.
  pose proof (kept_of_frame (segs:=SEGS) E4 _ (w_H W4) (ms_mem ms5) (ms_mem ms6) (fun _ => False) HFr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KEEP6.
  clear HF HFr HG.
  prreg HS (9%bv : bv 5) Q9.
  assert (R9' : getr (ms_regs ms6) 9 = Z_to_bv 64 (if pb =? 0 then 0x22480 else pb)).
  { rewrite Q9, OLD4, E9 by lia. rewrite (proj2 (Z.eqb_neq pb 0) Hpb). reflexivity. }
  pmkst HS.
  pose proof (st_ok_pi_restrict_mkst (w_H W4) _ _ _ HS eq_refl) as Hms6. cbn [ss_pc] in Hms6.
  pose proof (sb_canon_ok W4 _ _ _ 112%nat [10; 9]%bv HS eq_refl ltac:(cbv; lia) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HC.
  rewrite Hms6 in HC.
  lazymatch type of HC with st_ok_pi _ _ _ ?ssx _ =>
    assert (HEQ : ssx = sb_C3) by (vm_compute; reflexivity); rewrite HEQ in HC; clear HEQ end.
  apply (SB3 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
    (havoc E4 112 (map (getr (ms_regs ms6)) [10; 9]%bv)) W4 (ms_regs ms6) (ms_mem ms6) mdv3 ly4 S4
    ((p, LIVE_XSTRDUP (sarg port_a)) :: O2) (rdW W4 (ms_mem ms5)) HCX HC).
  + split; [apply img_env_havoc; [exact HEI4 | cbv; lia]|].
    intros n Hn. rewrite YN3v.ew_havoc_old by lia. rewrite OLD4 by lia. exact (HE0 n Hn).
  + unfold havoc. cbn [ew Nat.ltb Nat.leb Nat.sub nth map]. exact R9'.
  + split; [exact HJ4|]. split; [rewrite Hfr4c; exact Hfr2|].
    split; [exact Hbb4|]. split; [exact Hlv4|]. split; [exact MLE4|]. split; [exact HREP4|].
    split; [|exact HBK4].
    intros a Ha. apply KEEP6; [exact (sb_recb_rng ly4 S4 W4 (ms_mem ms5) mdv2 _ a (proj1 HJ4b) Ha) | tauto].
  + apply (sb_sstr_keep (ablocks B ly4 S4) _ (rdW W4 (ms_mem ms5)) _ _ _ HSBk); [tauto|].
    intros a (q & m & Hq & Ha). destruct (sb_in_blk_range _ _ _ _ _ q m a (proj1 HJ4b) Hq Ha) as (Ha1 & Ha2 & Ha3).
    apply KEEP6; [lia | tauto].
- assert (Hpb : pb = 0).
  { rewrite branch_ne_U, HU9, HU0 in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJ4 SHOK4 scn_Bspan SB_M3.
  { awr_ok_tac. }
  sb_set_md mdv3. sb_name_ms HS ms6.
  pose proof (kept_of_frame (segs:=SEGS) E4 _ (w_H W4) (ms_mem ms5) (ms_mem ms6) (fun _ => False) HFr
    ltac:(intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KEEP6.
  clear HF HFr HG.
  prreg HS (9%bv : bv 5) Q9.
  assert (R9' : getr (ms_regs ms6) 9 = Z_to_bv 64 (if pb =? 0 then 0x22480 else pb)).
  { rewrite Q9. rewrite (proj2 (Z.eqb_eq pb 0) Hpb). apply bv_eq.
    rewrite (HEI4 293%nat ltac:(unfold A_TEXT, A_LIM; lia)).
    change (VAL 293%nat) with (VAL (A_OBJ 52)). rewrite (scn_obj52 VOBJS).
    rewrite unsigned_lit_small by lia. reflexivity. }
  pmkst HS.
  pose proof (st_ok_pi_restrict_mkst (w_H W4) _ _ _ HS eq_refl) as Hms6. cbn [ss_pc] in Hms6.
  pose proof (sb_canon_ok W4 _ _ _ 112%nat [10; 9]%bv HS eq_refl ltac:(cbv; lia) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HC.
  rewrite Hms6 in HC.
  lazymatch type of HC with st_ok_pi _ _ _ ?ssx _ =>
    assert (HEQ : ssx = sb_C3) by (vm_compute; reflexivity); rewrite HEQ in HC; clear HEQ end.
  apply (SB3 ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O lyc Sc Wc regsc memc mdc k c O1
    (havoc E4 112 (map (getr (ms_regs ms6)) [10; 9]%bv)) W4 (ms_regs ms6) (ms_mem ms6) mdv3 ly4 S4
    ((p, LIVE_XSTRDUP (sarg port_a)) :: O2) (rdW W4 (ms_mem ms5)) HCX HC).
  + split; [apply img_env_havoc; [exact HEI4 | cbv; lia]|].
    intros n Hn. rewrite YN3v.ew_havoc_old by lia. rewrite OLD4 by lia. exact (HE0 n Hn).
  + unfold havoc. cbn [ew Nat.ltb Nat.leb Nat.sub nth map]. exact R9'.
  + split; [exact HJ4|]. split; [rewrite Hfr4c; exact Hfr2|].
    split; [exact Hbb4|]. split; [exact Hlv4|]. split; [exact MLE4|]. split; [exact HREP4|].
    split; [|exact HBK4].
    intros a Ha. apply KEEP6; [exact (sb_recb_rng ly4 S4 W4 (ms_mem ms5) mdv2 _ a (proj1 HJ4b) Ha) | tauto].
  + apply (sb_sstr_keep (ablocks B ly4 S4) _ (rdW W4 (ms_mem ms5)) _ _ _ HSBk); [tauto|].
    intros a (q & m & Hq & Ha). destruct (sb_in_blk_range _ _ _ _ _ q m a (proj1 HJ4b) Hq Ha) as (Ha1 & Ha2 & Ha3).
    apply KEEP6; [lia | tauto].
Qed.

End e.
End f.
End d.
