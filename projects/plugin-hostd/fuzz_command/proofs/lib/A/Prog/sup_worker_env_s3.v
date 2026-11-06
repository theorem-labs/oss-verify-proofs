(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the segment statements of sup_worker_env's ASan walk (plugin-hostd/fuzz_command),
   in the continuation form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (CL_RC_stmtX, CL_PF_stmtX, CL_FC_stmtX: the
   state the walk holds at a point of the listing, and the post-condition the rest of the walk reaches from it). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain PaFx RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c rec_shape_of_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_worker_env_c sup_worker_env_m sup_worker_env_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the string each argument block records: the argument, or "(null)" for a NULL one (recorder.c:223-225) *)
Definition swe_sel (p : Z) : Z := if p =? 0 then 0x22480 else p.
Fixpoint swe_sum (f : list byte -> Z) (l : list (list byte)) : Z :=
match l with [] => 0 | x :: l' => f x + swe_sum f l' end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Context {B : asyms} {MT : ameter_ops}.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_worker_env_c.v), at every FP state *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the named per-binary facts of the recorder walks that the statement does not carry yet (CmdRecFacts) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_heap_tail_vis : forall ly S W mem md p n e, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= e < p + n -> atail_vis SEGS W mem e.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Section w.
(* the entry of the call: the statement's quantified variables and premises (sup_worker_env_c.v) *)
Context {ly : alayout} {S : astate} {W : world SEGS} {regs : bvmap 5 word} {mem : word -> option byte} {md : Model}
  {ch : list (Z * Z * Z)} {pf pcs pnn : Z} {format cpus nice : option (list byte)} {R : rstate} {O : list (Z * Z)}.
Hypothesis HPRE : afn_pre SEGS B SUP_WORKER_ENV_STK ly S W regs mem md ch.
Hypothesis HFRM : Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis HRO : cmd_ro_ok (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 pf.
Hypothesis HB10 : 0 <= pf < 2 ^ 64.
Hypothesis H11 : getr regs 11 = w64 pcs.
Hypothesis HB11 : 0 <= pcs < 2 ^ 64.
Hypothesis H12 : getr regs 12 = w64 pnn.
Hypothesis HB12 : 0 <= pnn < 2 ^ 64.
Hypothesis HAFx : exists x, format = Some x /\
 in_blockA (ablocks B ly S) pf (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pf x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pf (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O.
Hypothesis HACx : exists x, cpus = Some x /\
 in_blockA (ablocks B ly S) pcs (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pcs x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pcs (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O.
Hypothesis HANx : exists x, nice = Some x /\
 in_blockA (ablocks B ly S) pnn (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pnn x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pnn (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O.
Hypothesis HREP : rec_repA B ly S (rdW W mem) R O.
Hypothesis HFR8 : Z.of_nat (length (frames S)) <= 8.
Hypothesis HEV : st_nev S + EV_SUP_WORKER_ENV R <= EV_MAX.
Hypothesis HLIVE : blocks_bytes S + LIVE_SUP_WORKER_ENV R format cpus nice <= LIVE_MAX.
Hypothesis HMOK : mo_ok MT S (XM_SUP_WORKER_ENV MT R format cpus nice).

Definition swe_n : nat := length (r_calls R).
Definition swe_c : Z := swe_slot_of (Z.of_nat swe_n).
Definition swe_FP : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
Definition swe_A3 : list (list byte) := [sarg format; sarg cpus; sarg nice].
(* the post of the statement (sup_worker_env_c.v:113-132), word for word *)
Definition swe_Q : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_worker_env_m R format cpus nice = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_WORKER_ENV R format cpus nice /\
 mo_le MT S S' (XM_SUP_WORKER_ENV MT R format cpus nice).
Definition swe_POST : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_WORKER_ENV_STK swe_FP regs ly S W mem md (EV_SUP_WORKER_ENV R) swe_Q.

(* the 64-byte frame: the entry's ra, s0 .. s6 at sp0 - 8 - 8 j *)
Definition swe_frame (Wc : world SEGS) (memc : word -> option byte) : Prop :=
forall j r, nth_error swe_saved j = Some r ->
aval_mem (rdW Wc memc) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* the allocator's meter, live bytes and event count spent by the first m copies *)
Definition swe_xm (m : nat) : Z := rec_spill_frees R * mo_free MT + swe_sum (XM_XSTRDUP MT) (firstn m swe_A3).
Definition swe_live (m : nat) : Z := swe_sum LIVE_XSTRDUP (firstn m swe_A3).
(* what every segment carries after m calls of xstrdup: the journal since the entry, the frame, and the blocks:
   D the entry's blocks still live, Fr the ones record() freed (record.spill's old arguments, all the recorder's),
   NB the copies xstrdup made, O0 the recorder's own blocks that survive *)
Definition swe_core (m : nat) lyc Sc (Wc : world SEGS) memc mdc (k : Z) (O0 D Fr NB : list (Z * Z)) : Prop :=
ajournal SEGS B SUP_WORKER_ENV_STK (spZ regs) swe_FP ly S W mem md [] lyc Sc Wc memc mdc k /\
0 <= k <= rec_spill_frees R + Z.of_nat m /\
swe_frame Wc memc /\
Permutation (ablocks B ly S) (D ++ Fr) /\
Permutation (ablocks B lyc Sc) (D ++ NB) /\
(forall pn, In pn Fr -> In pn O) /\
(forall pn, In pn D -> In pn O -> In pn O0) /\
(forall pn, In pn O0 -> In pn O) /\
(forall pn, In pn NB -> ~ In pn D) /\
length NB = m /\ bsum NB = swe_live m /\
mo_le MT S Sc (swe_xm m) /\
(forall pn, In pn O0 -> In pn D).
(* the registers every segment after the join holds: the frame's sp, gp, tp, s0 = the slot, s5 = the shadow base,
   s7 .. s11 the entry's *)
Definition swe_regs_base (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (spZ regs - 64) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 swe_c /\ getr regs1 21 = w64 SB /\
(forall r, 23 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
(* after record(): s2 = &c->nargs, s6 = its shadow byte *)
Definition swe_regs_chk (regs1 : bvmap 5 word) : Prop :=
getr regs1 18 = w64 (swe_c + 4) /\ getr regs1 22 = w64 (SB + (swe_c + 4) / 8).

(* --- the statements, one per point of the listing ------------------------------------------------------------ *)
Definition swe_at (pc : Z) (Wc : world SEGS) regs1 memc mdc : Prop :=
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) swe_POST.

(* 0x8c0e4: the two arms of record() meet; storing fn and nargs completes the recorded call *)
Definition swe_J_stmt : Prop :=
forall lyc Sc Wc regs1 memc mdc k O0 D Fr,
swe_core 0 lyc Sc Wc memc mdc k O0 D Fr [] ->
swe_regs_base regs1 ->
getr regs1 20 = w64 pf -> getr regs1 19 = w64 pcs -> getr regs1 9 = w64 pnn ->
(forall rd', (forall a, in_recg a -> ~ (swe_c <= a < swe_c + 8) -> rd' a = rdW Wc memc a) ->
   (forall p k i, In (p, k) O0 -> 0 <= i < k -> rd' (p + i) = rdW Wc memc (p + i)) ->
   aval_mem rd' swe_c 4 REC_WORKER_ENV -> aval_mem rd' (swe_c + 4) 4 0 ->
   rec_repA B lyc Sc rd' (rec_record R REC_WORKER_ENV []) O0) ->
swe_at SWE_J Wc regs1 memc mdc.

(* 0x8c120 / 0x8c170 / 0x8c1bc: the m-th argument register holds swe_sel of the argument; jal xstrdup next *)
Definition swe_X_regs (m : nat) (regs1 : bvmap 5 word) : Prop :=
match m with
| 1%nat => getr regs1 20 = w64 (swe_sel pf) /\ getr regs1 19 = w64 pcs /\ getr regs1 9 = w64 pnn
| 2%nat => getr regs1 20 = w64 (swe_c + 8) /\ getr regs1 19 = w64 (swe_sel pcs) /\ getr regs1 9 = w64 pnn
| _ => getr regs1 20 = w64 (swe_c + 8) /\ getr regs1 9 = w64 (swe_sel pnn)
end.
Definition swe_X_stmt (m : nat) (pc : Z) : Prop :=
forall lyc Sc Wc regs1 memc mdc k O0 D Fr NB,
swe_core (m - 1) lyc Sc Wc memc mdc k O0 D Fr NB ->
swe_regs_base regs1 -> swe_regs_chk regs1 -> swe_X_regs m regs1 ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_WORKER_ENV (firstn (m - 1) swe_A3)) (O0 ++ NB) ->
swe_at pc Wc regs1 memc mdc.

(* 0x8c128 / 0x8c178 / 0x8c1c4: back from the m-th xstrdup, a0 = the copy p of the m-th argument string *)
Definition swe_R_regs (m : nat) (regs1 : bvmap 5 word) : Prop :=
match m with
| 1%nat => getr regs1 19 = w64 pcs /\ getr regs1 9 = w64 pnn
| 2%nat => getr regs1 20 = w64 (swe_c + 8) /\ getr regs1 9 = w64 pnn
| _ => getr regs1 20 = w64 (swe_c + 8)
end.
Definition swe_R_stmt (m : nat) (pc : Z) : Prop :=
forall lyc Sc Wc regs1 memc mdc k O0 D Fr NB p,
let x := nth (m - 1) swe_A3 [] in
swe_core m lyc Sc Wc memc mdc k O0 D Fr (NB ++ [(p, Z.of_nat (length x) + 1)]) ->
swe_regs_base regs1 -> swe_regs_chk regs1 -> swe_R_regs m regs1 -> getr regs1 10 = w64 p ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_WORKER_ENV (firstn (m - 1) swe_A3)) (O0 ++ NB) ->
4096 <= p -> astr_atR (rdW Wc memc) p x ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) (D ++ NB) ->
swe_at pc Wc regs1 memc mdc.

End w.
End e.
End f.
End d.
