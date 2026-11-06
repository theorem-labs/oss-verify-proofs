(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: send_message's walk segment s3 on plugin-hostd/fuzz_command's ASan image, from
   0x86c48 (after the copy) to rec_clear's return 0x86c70, ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v,
   AChc.v and ACke.v at c8557374ad2e (cgif_close's segment chain and its program-callee steps) with the class-1 frame
   and inline-check steps of A/ACk1.v (cgif_newgif). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/send_message_s3.v, with its module paths and module names changed; 190 of its 227 lines of code are new or changed and 517 lines of the source are left out. *)
(* sup_remove's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan,
   BASE + AF_sup_remove = 0x8b258, 119 instructions; 103 on the side-stack path walked), part 1: the shared
   definitions and the statements of the four segments.

   The walk is cut at the three returns after which a fresh symbolic state is seated:
   - G1 (sup_remove.v): entry 0x8b258 .. the call of __asan_stack_malloc_0 at 0x8b2b8 (the class-0 frame F, 64
     bytes), the frame header and its shadow f1 f1 f1 f1 f8 f8 f3 f3, record(2) at 0x8b350; ends at record's return
     0x8b354 (SR_R) with sr_g2_stmt.
   - G2 (sup_remove_g2.v): 0x8b354 .. b's shadow 00 00 (0x8b358, 0x8b35c), snprintf(b, 16, "%d", id) at 0x8b374;
     ends at the wrapper's return 0x8b378 (SR_S), at the FP state fx1 it returns, with sr_g3_stmt.
   - G3 (sup_remove_g3.v): 0x8b378 .. arg_s(c, b) at 0x8b380, b's shadow f8 f8 (0x8b384, 0x8b388), answer(c,
     "resp 0", 1) at 0x8b39c; ends at answer's return 0x8b3a0 (SR_T), at the FP state fx2 it returns, with the post
     of the statement already holding there (sup_remove_q.v composes record's, arg_s's and answer's posts) and
     sr_g4_stmt.
   - G4 (sup_remove_g4.v): 0x8b3a0 .. the frame's release (magic 0x45e0360e, shadow f5 x 8, the flag byte through
     F + 56), the epilogue and `ret` at 0x8b430: the post is kept across the release.
   The segments after an FP-changing call (the snprintf wrapper, answer) are lemmas of a closed section, applied at
   the FP state the call returned (srr_after_artF / srr_after_callF of PaFx.v).

   At every cut, sr_cut gives: the journal from the entry with the frame (0, pos) owned; the frame's flag word
   (F + 56 holds flag_addr); the registers the code reads after the cut (sp = sp1 := (sp0 - 96) & -32,
   s0 = sp0, s1 = sp1, s2 = s7 = F, s3 = id, s4 = b = F + 32, s6 = the frame's shadow SB + F / 8, s8 = -8) and the
   callee-saved ones it does not touch (gp, tp, s9 .. s11); the ten words the prologue saved at sp0 - 8 .. sp0 - 80
   (ra, s0 .. s8 of the entry). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- tactics shared by the segments (an earlier version of sup_resp's A walk) ---- *)
(* the walk makes no inline check, so its shadow entry list stays empty; restate it over the current env *)
Ltac resh HS :=
try match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end;
lazymatch type of HS with st_ok_pi ?sg _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
let SH := fresh "SHOK" in
assert (SH : sh_ok sg (SOff 32 0) [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by (unfold sh_ok; apply Forall_nil) end.
(* after each symbolic run the model is left as `with_vm_backing (m_vm_lazy md) mat md`; over a chain of runs the
   term doubles per run, so make it opaque right after each run *)
Ltac collapse_md :=
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdl) _ =>
first [ is_var mdl | let mdv := fresh "mdv" in set (mdv := mdl) in *; clearbody mdv ] end.

(* the footprint the statement names (sup_remove_c.v:119-120) *)
Definition sr_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the realigned stack pointer: `addi sp,sp,-96` then `andi sp,sp,-32` (0x8b258, 0x8b28c) *)
Definition sr_sp1 (sp0 : Z) : Z := 32 * ((sp0 - 96) / 32).
(* the three cuts, as offsets from BASE + AF_sup_remove: record's return 0x8b354, the snprintf wrapper's return
   0x8b378, answer's return 0x8b3a0 *)
Definition SR_R : Z := 0xfc.
Definition SR_S : Z := 0x120.
Definition SR_T : Z := 0x148.

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
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the post of tsup_remove_spec (sup_remove_c.v:122-140), with t := snd (sup_remove_m R id) *)
Definition sr_post (ly : alayout) (S : astate) (W : world SEGS) (R : rstate) (O : list (Z * Z)) (id : Z)
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists R' O' q,
 sup_remove_m R id = (R', snd (sup_remove_m R id)) /\
 let n := Z.of_nat (length (snd (sup_remove_m R id))) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn (ablocks B ly S) -> In pn O) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (In (q, n) (ablocks B ly S) -> In (q, n) O) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q (snd (sup_remove_m R id)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_REMOVE id (snd (sup_remove_m R id)) /\
 mo_le MT S S' (XM_SUP_REMOVE MT R id (snd (sup_remove_m R id))).

(* the statement's premises other than the rounding mode (sup_remove_c.v:97-114) *)
Definition sr_pre (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (ch : list (Z * Z * Z)) (id : Z) (R : rstate) (O : list (Z * Z)) : Prop :=
afn_pre SEGS B SUP_REMOVE_STK ly S W regs mem md ch /\
Z.of_nat (length (frames S)) <= 7 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 id /\ -2 ^ 31 <= id < 2 ^ 31 /\
rec_repA B ly S (rdW W mem) R O /\
st_nev S + EV_SUP_REMOVE R <= EV_MAX /\
blocks_bytes S + LIVE_SUP_REMOVE id (snd (sup_remove_m R id)) <= LIVE_MAX /\
mo_ok MT S (XM_SUP_REMOVE MT R id (snd (sup_remove_m R id))).

(* the ten words the prologue saves (0x8b260 .. 0x8b284): ra, s0, s1, ..., s8 of the entry, at sp0 - 8 .. sp0 - 80 *)
Definition sr_saves (rd : reader) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
rdword rd (sp0 - 8) = Some (bv_unsigned (getr regs 1)) /\
rdword rd (sp0 - 16) = Some (bv_unsigned (getr regs 8)) /\
rdword rd (sp0 - 24) = Some (bv_unsigned (getr regs 9)) /\
rdword rd (sp0 - 32) = Some (bv_unsigned (getr regs 18)) /\
rdword rd (sp0 - 40) = Some (bv_unsigned (getr regs 19)) /\
rdword rd (sp0 - 48) = Some (bv_unsigned (getr regs 20)) /\
rdword rd (sp0 - 56) = Some (bv_unsigned (getr regs 21)) /\
rdword rd (sp0 - 64) = Some (bv_unsigned (getr regs 22)) /\
rdword rd (sp0 - 72) = Some (bv_unsigned (getr regs 23)) /\
rdword rd (sp0 - 80) = Some (bv_unsigned (getr regs 24)).

(* the state at a cut: (ly, S, W, regs, mem, md) is the entry's, (lyc, Sc, Wc, regsc, memc, mdc) the cut's, (0, pos)
   the side-stack frame, k the events spent so far *)
Definition sr_cut (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (O : list (Z * Z)) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regsc : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos k : Z) : Prop :=
ajournal SEGS B SUP_REMOVE_STK (spZ regs) (sr_FP O) ly S W mem md [(0, pos)] lyc Sc Wc memc mdc k /\
rdword (rdW Wc memc) (frame_addr lyc 0 pos + 56) = Some (flag_addr lyc 0 pos) /\
spZ regsc = sr_sp1 (spZ regs) /\
getr regsc 8 = getr regs 2 /\
getr regsc 9 = w64 (sr_sp1 (spZ regs)) /\
getr regsc 18 = w64 (frame_addr lyc 0 pos) /\
getr regsc 19 = getr regs 10 /\
getr regsc 20 = w64 (frame_addr lyc 0 pos + 32) /\
getr regsc 22 = w64 (SB + frame_addr lyc 0 pos / 8) /\
getr regsc 23 = w64 (frame_addr lyc 0 pos) /\
getr regsc 24 = Z_to_bv 64 (-8) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\
getr regsc 25 = getr regs 25 /\ getr regsc 26 = getr regs 26 /\ getr regsc 27 = getr regs 27 /\
sr_saves (rdW Wc memc) (spZ regs) regs.

(* what record()'s post leaves (record_c.v:107-122), stated against the entry: the blocks Fr it freed (from the
   recorder's O; ablocks at the entry is ablocks at record's entry, the frame's take changes no block), the recorder
   at the cut, its blocks O1 = O less Fr, the live bytes and the meter *)
Definition sr_recd (ly : alayout) (S : astate) (lyc : alayout) (Sc : astate) (rdc : reader) (R : rstate)
  (O Fr O1 : list (Z * Z)) : Prop :=
Permutation (ablocks B ly S) (ablocks B lyc Sc ++ Fr) /\
Z.of_nat (length Fr) = rec_spill_frees R /\
(forall pn, In pn Fr -> In pn O) /\
rec_repA B lyc Sc rdc (rec_record R REC_REMOVE []) O1 /\
(forall pn, In pn O1 <-> In pn O /\ ~ In pn Fr) /\
blocks_bytes Sc <= blocks_bytes S /\
mo_le MT S Sc (XM_RECORD MT R).

(* ---- the segments' statements ---- *)
(* G2: from record's return (0x8b354) to the end *)
Definition sr_g2_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id : Z) (R : rstate) (O : list (Z * Z))
  lyc Sc Wc (regsc : bvmap 5 word) memc mdc (pos : Z) (Fr O1 : list (Z * Z)),
sr_pre ly S W regs mem md ch id R O -> frm0 fx ->
sr_cut ly S W regs mem md O lyc Sc Wc regsc memc mdc pos (EV_RECORD R) ->
sr_recd ly S lyc Sc (rdW Wc memc) R O Fr O1 ->
getr regsc 10 = w64 (rec_slot R) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_sup_remove + SR_R))) memc (seg_rom SEGS)) mdc)
 (apost_baseF SEGS B SUP_REMOVE_STK (sr_FP O) regs ly S W mem md (EV_SUP_REMOVE R) (sr_post ly S W R O id)).
(* G3: from the snprintf wrapper's return (0x8b378) to the end; b holds the decimal text of id, its shadow bytes
   (frame shadow 4 and 5) are 00, s5 holds record's slot *)
Definition sr_g3_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id : Z) (R : rstate) (O : list (Z * Z))
  lyc Sc Wc (regsc : bvmap 5 word) memc mdc (pos : Z) (Fr O1 : list (Z * Z)),
sr_pre ly S W regs mem md ch id R O -> frm0 fx ->
sr_cut ly S W regs mem md O lyc Sc Wc regsc memc mdc pos (EV_RECORD R) ->
sr_recd ly S lyc Sc (rdW Wc memc) R O Fr O1 ->
getr regsc 21 = w64 (rec_slot R) ->
rdW Wc memc (SB + frame_addr lyc 0 pos / 8 + 4) = Some 0 ->
rdW Wc memc (SB + frame_addr lyc 0 pos / 8 + 5) = Some 0 ->
astr_atR (rdW Wc memc) (frame_addr lyc 0 pos + 32) (dec id) ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_sup_remove + SR_S))) memc (seg_rom SEGS)) mdc)
 (apost_baseF SEGS B SUP_REMOVE_STK (sr_FP O) regs ly S W mem md (EV_SUP_REMOVE R) (sr_post ly S W R O id)).
(* G4: from answer's return (0x8b3a0) to the end, the post already holding at the cut *)
Definition sr_g4_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id : Z) (R : rstate) (O : list (Z * Z))
  lyc Sc Wc (regsc : bvmap 5 word) memc mdc (pos : Z),
sr_pre ly S W regs mem md ch id R O ->
sr_cut ly S W regs mem md O lyc Sc Wc regsc memc mdc pos (EV_SUP_REMOVE R) ->
sr_post ly S W R O id lyc Sc Wc regsc memc mdc ->
SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + (AF_sup_remove + SR_T))) memc (seg_rom SEGS)) mdc)
 (apost_baseF SEGS B SUP_REMOVE_STK (sr_FP O) regs ly S W mem md (EV_SUP_REMOVE R) (sr_post ly S W R O id)).
(* Q: the post at answer's return, from record's, arg_s's and answer's posts (no symbolic execution). (lyc, Sc, Wc,
   memc, mdc) is record's return, where sr_recd holds; arg_s is entered at (lyc, Sc) and returns at (ly3, S3) with the
   fresh block (p, ni) holding the copy of dec id; answer is entered at (ly3, S3, Wa, mema, mda), with old the
   answer g_rec held, and returns at (ly4, S4, W4, regs4, mem4, md4) with p1 (the recorder's copy) and p2 (the
   caller's) *)
Definition sr_q_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id : Z) (R : rstate) (O : list (Z * Z))
  lyc Sc (Wc : world SEGS) memc mdc (Fr O1 : list (Z * Z)) ly3 S3 (p : Z)
  (Wa : world SEGS) mema mda (old : Z) ly4 S4 (W4 : world SEGS) (regs4 : bvmap 5 word) mem4 md4 (p1 p2 : Z)
  (O' : list (Z * Z)),
let t := snd (sup_remove_m R id) in
let R1 := rec_record R REC_REMOVE [dec id] in
let n := Z.of_nat (length t) + 1 in
let ni := Z.of_nat (length (dec id)) + 1 in
sr_pre ly S W regs mem md ch id R O ->
AR SEGS B lyc Sc Wc memc mdc ->
sr_recd ly S lyc Sc (rdW Wc memc) R O Fr O1 ->
(* arg_s (arg_s_c.v:132-138, the arm with fewer than six arguments) *)
4096 <= p < 2 ^ 64 ->
Permutation (ablocks B ly3 S3) ((p, ni) :: ablocks B lyc Sc) ->
Forall (fun qk => iv_apart p ni (fst qk) (snd qk)) (ablocks B lyc Sc) ->
blocks_bytes S3 <= blocks_bytes Sc + LIVE_ARG_S (Some (dec id)) ->
mo_le MT Sc S3 (XM_ARG_S MT (Some (dec id))) ->
(* answer's entry *)
AR SEGS B ly3 S3 Wa mema mda ->
rec_repA B ly3 S3 (rdW Wa mema) R1 ((p, ni) :: O1) ->
aval_mem (rdW Wa mema) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
(* answer's post (answer_c.v:133-150) *)
AR SEGS B ly4 S4 W4 mem4 md4 ->
getr regs4 10 = w64 p2 -> 4096 <= p2 < 2 ^ 64 -> p1 <> p2 ->
(forall pn, In pn (ablocks B ly3 S3) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) ->
(forall pn, In pn (ablocks B ly4 S4) <-> (In pn (ablocks B ly3 S3) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
rec_repA B ly4 S4 (rdW W4 mem4) (fst (rec_answer R1 (REC_REMOVE, [dec id]) REC_MOD_HOST_SHAPE true)) O' ->
(forall pn, In pn O' <-> (In pn ((p, ni) :: O1) /\ fst pn <> old) \/ pn = (p1, n)) ->
astr_atR (rdW W4 mem4) p2 t ->
blocks_bytes S4 <= blocks_bytes S3 + LIVE_ANSWER t ->
mo_le MT S3 S4 (XM_ANSWER MT t) ->
sr_post ly S W R O id ly4 S4 W4 regs4 mem4 md4.

(* ---- the footprint's bytes (the A donor's sup_remove_s1.v:336-373, over B's record facts) ---- *)
Section g.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Lemma sr_inPG : forall a, (A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56) -> inFP cmd_PG a.
Proof.
intros a [Ha | Ha]; unfold cmd_PG.
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn; lia].
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn; lia].
Qed.
Lemma sr_FP_pos : forall ly S W mem md O, AR SEGS B ly S W mem md -> Forall (fun pn => In pn (ablocks B ly S)) O ->
Forall (fun r => 0 < fst r) (sr_FP O).
Proof.
intros ly S W mem md O HAR HO. unfold sr_FP.
do 4 (apply Forall_cons; [cbn [fst]; unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_STATE; lia|]).
unfold ablocks_fp. apply Forall_map. eapply Forall_impl; [|exact HO]. intros [p n] Hin. cbn [fst].
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & _). lia.
Qed.
Lemma sr_FP_cases : forall O a, inFP (sr_FP O) a -> inFP cmd_PG a \/ inFP (ablocks_fp O) a.
Proof.
intros O a (r & Hr & Ha). unfold sr_FP in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha;
[left; apply sr_inPG; unfold OFF_NCALLS, A_G_REC in *; lia | left; apply sr_inPG; unfold OFF_CALLS, OFF_ANSWER, A_G_REC in *; lia
| left; apply sr_inPG; unfold OFF_STATE, A_G_REC in *; lia | left; apply sr_inPG; unfold SC_SIZE, A_REC_SPILL in *; lia |].
right. exists r. auto.
Qed.
Lemma sr_FP_noro : forall ly S W mem md O, AR SEGS B ly S W mem md -> Forall (fun pn => In pn (ablocks B ly S)) O ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (sr_FP O) a.
Proof.
intros ly S W mem md O HAR HO a Hro Hf.
destruct (sr_FP_cases O a Hf) as [Hpg | Hb]; [exact (CmdRecRo.RPG SEGS B LAWS HB IMG a Hpg Hro)|].
destruct (inFP_ablocks_fp_inv O a Hb) as (p & n & Hin & Hr).
apply (blk_img SEGS B LAWS ly S W mem md p n a HAR); [exact (proj1 (Forall_forall _ _) HO _ Hin) | exact Hr |].
destruct Hro as [(s & Hs & _ & Hr') | Hrel]; [exists s; split; [exact Hs | exact Hr'] | exact (CmdRecRo.RRO SEGS B LAWS HB IMG a Hrel)].
Qed.
(* arodata_okP carries over a journal of the call: a read-only byte is an image byte outside the footprint *)
Lemma sr_aro_journal : forall STK sp0 O ly S W mem md own ly' S' W' mem' md' k,
AR SEGS B ly S W mem md -> Forall (fun pn => In pn (ablocks B ly S)) O ->
ajournal SEGS B STK sp0 (sr_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HAR HO HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He |].
- pose proof Hro as Hro'.
  destruct Hro' as [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (CmdRecRo.RRO SEGS B LAWS HB IMG a Hrel)].
- apply fp_spares_closed; [exact (sink_closed_pos _ (sr_FP_pos ly S W mem md O HAR HO)) | exact (sr_FP_noro ly S W mem md O HAR HO a Hro)].
Qed.
End g.
End e.
End f.
End d.
