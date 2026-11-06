(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_quarantine_clear (plugin-hostd/fuzz_command), part 3: the
   walk's statement and invariant, the facts its segments share, the walk from the call of xstrdup to the tail jump
   into answer (sqc_SX), the join segment (sqc_SJ), the entry with record()'s two arms (sqc_SA) and their
   composition (sqc_holds); in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v, AChc.v (the segment
   walk of cgif_close: a seed per segment, paj_run_tok steps, cl_callS at each program call) and of
   lib/A/Prog/sup_instance_info.v's record() spill arm (one of the recorder walks) over fuzz_command's listing. *)

(* sup_quarantine_clear (recorder.c:411-417; BASE + AF_sup_quarantine_clear = 0x8b844, 91 instructions):
   - the entry segment: the 48-byte frame, the shadow base (the word at the GOT cell 0xa63f0), g_rec.ncalls; if the
     table holds 16 calls, record.spill is the slot and rec_calls_free(spill, 1) frees its arguments (0x8b894),
     else g_rec.ncalls := n + 1 and the slot is g_rec.calls[n];
   - from the join (0x8b8b8): two inline checks (the 4-byte stores of c->fn := 11 and c->nargs := 0: a load of the
     shadow byte at (c >> 3) + 0x7fff8000 and a compare, whose error path is not reached because the slot lies in
     g_rec or record.spill, which the record marks usable), the test of the argument (its one caller passes a string
     of a heap block, so the default "(null)" is not taken), the call of xstrdup (0x8b8f8);
   - after it: two more checks (the load of c->nargs and the 8-byte store of c->args[0]), c->nargs := 1,
     c->args[0] := the copy, the call of rec_shape_of("quarantine_clear", 16) (0x8b93c);
   - after it: the frame is released and the function tail-jumps to answer(c, shape, 1) (0x8b968), which runs at
     this function's entry stack pointer and returns to its caller.

   Pass-4/5 re-fit: the callee hypotheses hold at
   every FP state (forall fx0) and are used at the entry's fx: rec_calls_free, xstrdup and rec_shape_of keep the FP
   state (apost_base, kit rules unchanged); answer is the last step (the tail jump), its post apost_baseF returns at
   some fx1 with answer's two FP clauses against the entry's fx, which are sup_quarantine_clear's apost_baseF clauses;
   answer's rounding-mode-0 premise is the entry's (HRM0). Statement pass 5 removed astack_pres: the walk no longer
   derives it for rec_calls_free, xstrdup or answer (the old sqc_astack). The frame chains the calls' afn_pre ask
   come from the walk as before: s0 = the slot (below alloc_ceiling, the empty chain) at rec_calls_free and
   xstrdup, the entry s0 (the entry's afn_pre chain, sqc_achain_kept) at answer. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c mix_call_c hand_back_c answer_c sup_quarantine_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas sup_quarantine_clear_s1 sup_quarantine_clear_s2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition SQC_STK : Z := SUP_QUARANTINE_CLEAR_STK.
Lemma SQC_STK_val : SQC_STK = 16592.
Proof. reflexivity. Qed.
(* the bytes the call may write outside its frame: g_rec, record.spill, the recorder's blocks *)
Definition sqc_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.
(* the default argument "(null)" (.str.47, 0x22480) and the verb "quarantine_clear" (.str.9, 0x21e00) *)
Definition sqc_null : list byte := bstr "(null)"%string.
Definition sqc_verb : list byte := bstr "quarantine_clear"%string.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callees (sup_quarantine_clear_c.v:70-73), at every FP state *)
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
(* the program's statics (the recorder walks' shared names, RecBTemplate.v forms) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
(* the per-binary record facts the statement does not give (the recorder walks' shared list; CmdRecFacts.v is to
   prove each): the read-only bytes the program loads are those of the image wherever arodata_okP holds,
   arodata_okP survives every journal whose footprint is off the read-only range (CmdBase.v's arodata_ok_journalP),
   the read-only range is image bytes outside the program's statics, CmdRo's objects are read-only (the premise the
   statements dropped, one name for every walk, 2026-10-29), and a live block's bytes after a string's
   terminator up to the end of its 8-byte word are readable *)
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
(* the image facts of the binary (the kit's CmdRecBase.cmd_img_facts; RecBClosed closes it by cmd_img_facts_tfib):
   the relro range lies in the image (CmdRecRo.RELRO_IMG) *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* the statement's post (sup_quarantine_clear_c.v:101-120) *)
Definition sqc_Q (ly : alayout) (S : astate) (R : rstate) (O : list (Z * Z)) (which : option (list byte))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_quarantine_clear_m R which = (R', t) /\
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
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_QUARANTINE_CLEAR R which /\
 mo_le MT S S' (XM_SUP_QUARANTINE_CLEAR MT R which).

(* the statement's premises (sup_quarantine_clear_c.v:77-96) *)
Definition sqc_pre ly S W (regs : bvmap 5 word) mem md ch (pw : Z) (which : option (list byte)) (R : rstate)
  (O : list (Z * Z)) : Prop :=
afn_pre SEGS B SQC_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pw /\ 0 <= pw < 2 ^ 64 /\
(exists x, which = Some x /\
 in_blockA (ablocks B ly S) pw (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pw x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pw (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_SUP_QUARANTINE_CLEAR R <= EV_MAX /\
blocks_bytes S + LIVE_SUP_QUARANTINE_CLEAR R which <= LIVE_MAX /\
mo_ok MT S (XM_SUP_QUARANTINE_CLEAR MT R which).

(* the walk's statement: the statement, its premises bundled *)
Definition tsqc_spec_g : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (pw : Z) (which : option (list byte)) (R : rstate) (O : list (Z * Z)),
sqc_pre ly S W regs mem md ch pw which R O ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_quarantine_clear) regs mem md)
(apost_baseF SEGS B SQC_STK (sqc_FP O) regs ly S W mem md (EV_SUP_QUARANTINE_CLEAR R) (sqc_Q ly S R O which)).


(* ---------- the walk's invariant between its segments ---------- *)

(* the journal from the entry, the frame, and the recorder's state at a base point (the entry, or after record()'s
   rec_calls_free on the spill arm), with the blocks the walk freed so far (F, the spill's arguments) *)
Definition sqc_mid ly S W (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
  lyc Sc (Wc : world SEGS) memc mdc (k : Z) lyB SBa (WB : world SEGS) memB (R0 : rstate) (O0 F : list (Z * Z)) : Prop :=
ajournal SEGS B SQC_STK (spZ regs) (sqc_FP O) ly S W mem md [] lyc Sc Wc memc mdc k /\
k = Z.of_nat (length F) /\
sqc_frame_at (mrestrict (w_H Wc) memc) (spZ regs - SQ_FRAME) regs /\
rec_repA B lyB SBa (rdW WB memB) R0 O0 /\
(length (r_calls R0) = 16%nat -> snd (r_spill R0) = []) /\
length (r_calls R0) = length (r_calls R) /\
(forall A, rec_record R0 SQ_FN A = rec_record R SQ_FN A) /\
(forall pn i, In pn O0 -> 0 <= i < snd pn -> rdW Wc memc (fst pn + i) = rdW WB memB (fst pn + i)) /\
(forall pn, In pn O0 -> In pn (ablocks B lyc Sc)) /\
Permutation (ablocks B ly S) (ablocks B lyc Sc ++ F) /\
(forall pn, In pn F -> In pn O) /\
(forall pn, In pn O0 <-> In pn O /\ ~ In pn F) /\
Z.of_nat (length F) = rec_spill_frees R /\
mo_le MT S Sc (Z.of_nat (length F) * mo_free MT).

(* g_rec and record.spill equal the base's, but for g_rec.ncalls and the first x bytes of the slot c *)
Definition sqc_recmem (rd rdB : reader) (c x : Z) : Prop :=
forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + x) -> rd a = rdB a.

Definition sqc_ncalls_ok (rd : reader) (R0 : rstate) : Prop :=
aval_mem rd (A_G_REC + OFF_NCALLS) 4 (Z.of_nat (length (r_calls (rec_record R0 SQ_FN [[]])))).

(* ---------- small facts ---------- *)

Lemma sqc_aval_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.

Lemma sqc_astr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. intros i Hi.
rewrite (Hk (Z.of_nat i)) by (rewrite length_app in Hi; cbn [length] in Hi; lia). exact (H1 i Hi).
Qed.

Lemma sqc_alu_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. rewrite alu_add. unfold v_add. apply Z_to_bv64_eq_mod.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma sqc_srl3 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 64) ltac:(lia) ltac:(lia)).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. symmetry. apply unsigned_lit_small. lia.
Qed.

(* s4 after the prologue's checks: the shadow byte's address of c->nargs *)
Definition sqc_shx4 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff SQ_C 4) (SLit 3)) (SOff SQ_SB 0).
Lemma sqc_shx4_denot : forall E c, ew E SQ_C = Z_to_bv 64 c -> ew E SQ_SB = Z_to_bv 64 SB -> 0 <= c < 2 ^ 40 ->
sv_denot E sqc_shx4 = Z_to_bv 64 (SB + (c + 4) / 8).
Proof.
intros E c Hc Hsb Hr. unfold sqc_shx4. cbn [sv_denot]. rewrite Hc, Hsb.
rewrite !unsigned_lit_small by (unfold SB; lia). rewrite Z.add_0_r.
rewrite sqc_srl3 by lia. rewrite sqc_alu_add. f_equal. lia.
Qed.

Definition sqc_regsD : list sv := Eval vm_compute in sr_set (sr_set sqc_regsC 18 (SOff SQ_C 4)) 20 sqc_shx4.

Lemma sqc_slot_ok_of : forall R0, (length (r_calls R0) <= 16)%nat -> sqc_slot_ok (sqc_slot R0).
Proof.
intros R0 H. unfold sqc_slot. destruct (Nat.ltb_spec (length (r_calls R0)) 16) as [L|L].
- left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. split; [lia|]. split; [lia|].
  rewrite Z.add_mod by lia. replace (56 * Z.of_nat (length (r_calls R0))) with (8 * (7 * Z.of_nat (length (r_calls R0)))) by lia.
  rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- right. reflexivity.
Qed.

(* ---------- the footprint, the read-only range, the program's statics ---------- *)

Lemma sqc_inFP_cases : forall O a, inFP (sqc_FP O) a ->
Exists (in_zr a) recb_PG \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold sqc_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply recb_grec_in. exact Ha.
- left. apply recb_spill_in. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  exists b, n. split; [exact Hin | exact Ha].
Qed.

(* arodata_okP along the walk's journal: the walk's footprint (g_rec, record.spill, the recorder's blocks) is off
   the read-only range *)
Lemma sqc_aro : forall ly S (W : world SEGS) mem md O lyc Sc Wc memc mdc own k sp,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B SQC_STK sp (sqc_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros ly S W mem md O lyc Sc Wc memc mdc own k sp HAR HO HJ HR.
apply (arodata_ok_journalP SEGS RLO RHI (CmdRecRo.RELRO_IMG SEGS B LAWS HB IMG) (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact HR].
intros a Hro Hfp. destruct (sqc_inFP_cases O a Hfp) as [HP | (b & n & Hin & Ha)].
- exact (proj2 (cmd_ro_prog_apart a Hro) HP).
- pose proof (HO _ Hin) as Hin'.
  apply (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ n (conj Hin' Ha)))))).
  exact (proj1 (cmd_ro_prog_apart a Hro)).
Qed.

Lemma sqc_bsum_nonneg : forall ly S (W : world SEGS) mem md L, AR SEGS B ly S W mem md ->
(forall pn, In pn L -> In pn (ablocks B ly S)) -> 0 <= bsum L.
Proof.
intros ly S W mem md L HAR HL. induction L as [|[b m] L IH]; [unfold bsum; cbn; lia|].
rewrite bsum_cons. cbn [snd].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (HL (b, m) (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hm).
assert (IH' := IH (fun pn Hpn => HL pn (or_intror Hpn))). lia.
Qed.

(* ---------- what a callee's journal keeps ---------- *)

Lemma sqc_keep_img : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; exact HF | exact Hn]].
Qed.

Lemma sqc_keep_prog : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a -> Exists (in_zr a) recb_PG ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn HP.
destruct (recb_prog_unowned_m B HB cmd_prog_img a HP) as (H1 & H2 & H3). exact (sqc_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HF Hn H1 H2 H3).
Qed.

Lemma sqc_keep_stack : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
(forall b, inFP FP1 b -> b < alloc_ceiling) -> alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Ha Hw.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply F1; [exact Ha | exact Hw | intros Hf; specialize (HF a Hf); lia].
Qed.

Lemma sqc_val_kept : forall (W W' : world SEGS) m m' a n v,
val_mem SEGS (mrestrict (w_H W) m) a n v ->
(forall k, (k < n)%nat -> rdW W' m' (a + Z.of_nat k) = rdW W m (a + Z.of_nat k)) ->
val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v Hv Hk. apply (val_mem_view SEGS). apply (sqc_aval_kept (rdW W m)); [|exact Hk].
exact (aval_mem_view SEGS (w_H W) m a n v Hv).
Qed.

(* a byte of the slot: the walk may write it (awr_byte's program-static disjunct) *)
Lemma sqc_awr_slot : forall STK sp O bl0 blc fr0 ly own c a, sqc_slot_ok c -> c <= a < c + CALL_SIZE ->
awr_byte SEGS B STK sp (sqc_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own c a Hc Ha. pose proof (sqc_in_PG_slot c a Hc Ha) as HP.
right; right; right; right; left. split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct (sqc_slot_bounds c Hc) as (Hcb & _ & [Hh | ->]).
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity|]. cbn [fst snd].
  unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, A_REC_SPILL in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity|]. cbn [fst snd].
  unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

Lemma sqc_keep_blk : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 b m i,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ inFP FP1 (b + i) ->
rdW W2 mem2 (b + i) = rdW Wc memc (b + i).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 b m i HJ H1 H2 Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). exact (F2 b m i H1 H2 Hi Hn).
Qed.

Lemma sqc_blk_noprog : forall ly S (W : world SEGS) mem md b m a, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> ~ Exists (in_zr a) recb_PG.
Proof. intros ly S W mem md b m a HAR Hin Ha HP. exact (recb_heap_noimg_m B ly S W mem md b m a HAR Hin Ha (cmd_prog_img a HP)). Qed.

Lemma sqc_blk_bounds : forall ly S (W : world SEGS) mem md b m, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m /\ m <= req_size m /\ 1 <= req_size m.
Proof.
intros ly S W mem md b m HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2]. lia.
Qed.

(* two live blocks that differ are apart *)
Lemma sqc_blk_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
b + req_size m <= p \/ p + req_size n <= b.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* the slot fact answer's pre asks (answer_c.v:103-105) *)
Lemma sqc_answer_slot : forall R0 x,
(exists k, nth_error (r_calls (rec_record R0 SQ_FN [x])) k = Some (SQ_FN, [x]) /\
   sqc_slot R0 = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(sqc_slot R0 = A_REC_SPILL /\ (SQ_FN, [x]) = r_spill (rec_record R0 SQ_FN [x])).
Proof.
intros R0 x. unfold sqc_slot, rec_record. destruct (Nat.ltb_spec (length (r_calls R0)) 16) as [L|L].
- left. exists (length (r_calls R0)). cbn [set_calls r_calls]. split; [|reflexivity].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. cbn [set_spill r_spill]. split; reflexivity.
Qed.

Lemma sqc_ncalls_len : forall R0 A A', length (r_calls (rec_record R0 SQ_FN A)) = length (r_calls (rec_record R0 SQ_FN A')).
Proof.
intros R0 A A'. unfold rec_record. destruct (Nat.ltb (length (r_calls R0)) 16); cbn [set_calls set_spill r_calls];
[rewrite !length_app; reflexivity | reflexivity].
Qed.

Definition sqc_old (Q : rlay) : Z := match l_answer Q with Some pn => fst pn | None => 0 end.

Lemma sqc_old_at : forall bl rd R Q, arep_at bl rd A_G_REC A_REC_SPILL R Q ->
aval_mem rd (A_G_REC + OFF_ANSWER) 8 (sqc_old Q) /\ (forall pn, l_answer Q = Some pn -> In pn (lay_blocks Q)).
Proof.
intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold sqc_old. split.
- unfold aanswer_at in HA. destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn|]; try contradiction;
  [exact (proj1 HA) | exact HA].
- intros pn Hpn. unfold lay_blocks. rewrite Hpn. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  left. reflexivity.
Qed.

(* the callee-saved registers, one by one *)
Lemma sqc_pres : forall (r1 r2 : bvmap 5 word),
(forall n, In n [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r2 (Z_to_bv 5 n) = getr r1 (Z_to_bv 5 n)) ->
aregs_preserved r1 r2.
Proof.
intros r1 r2 H r Hr. apply H. unfold acallee_saved in Hr. cbn [In].
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [tauto | tauto | tauto | tauto | tauto |].
assert (H0 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct H0 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; tauto.
Qed.

Lemma sqc_achain_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k v ch,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 v ch -> achain ly' (rdW W' mem') sp0 v ch.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k v ch HJ HF Hc.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hs0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top ly ly'); [exact Etop|].
apply (achain_kept ly (rdW W mem) (rdW W' mem') sp0 v ch sp0 Hc); [lia | lia |].
intros a Ha. apply F1; [lia | lia | intros Hf; specialize (HF a Hf); lia].
Qed.

Lemma sqc_heap_apart : forall ly S (W : world SEGS) mem md b m lo len,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 < len ->
(forall a, lo <= a < lo + len -> in_img SEGS a) -> iv_apart b m lo len.
Proof.
intros ly S W mem md b m lo len HAR Hin Hlen Himg. unfold iv_apart.
destruct (sqc_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & Hm & Hmr & Hr1).
destruct (Z_le_gt_dec (b + m) lo) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (lo + len) b) as [H'|H']; [right; exact H'|]. exfalso.
apply (recb_heap_noimg_m B ly S W mem md b m (Z.max b lo) HAR Hin); [lia | apply Himg; lia].
Qed.

Lemma sqc_pres' : forall (r1 r2 : bvmap 5 word),
getr r2 2%bv = getr r1 2%bv -> getr r2 3%bv = getr r1 3%bv -> getr r2 4%bv = getr r1 4%bv ->
getr r2 8%bv = getr r1 8%bv -> getr r2 9%bv = getr r1 9%bv -> getr r2 18%bv = getr r1 18%bv ->
getr r2 19%bv = getr r1 19%bv -> getr r2 20%bv = getr r1 20%bv -> getr r2 21%bv = getr r1 21%bv ->
getr r2 22%bv = getr r1 22%bv -> getr r2 23%bv = getr r1 23%bv -> getr r2 24%bv = getr r1 24%bv ->
getr r2 25%bv = getr r1 25%bv -> getr r2 26%bv = getr r1 26%bv -> getr r2 27%bv = getr r1 27%bv ->
aregs_preserved r1 r2.
Proof.
intros r1 r2 X2 X3 X4 X8 X9 X18 X19 X20 X21 X22 X23 X24 X25 X26 X27. apply sqc_pres. intros n Hn. cbn [In] in Hn.
repeat (destruct Hn as [<- | Hn]; [assumption|]). destruct Hn.
Qed.

(* answer's post (answer_c.v:114-127) at the call's values *)
Definition sqc_ansQ (lyA : alayout) (SA : astate) (R1 : rstate) (e : rcall) (shp : list byte) (O1 : list (Z * Z))
  (old : Z) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists p1 p2 O',
 let t := snd (rec_answer R1 e shp true) in
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 p2 /\ 4096 <= p2 /\ p1 <> p2 /\
 ~ In (p1, n) (ablocks B lyA SA) /\ ~ In (p2, n) (ablocks B lyA SA) /\
 (forall pn, In pn (ablocks B ly' S') <->
   (In pn (ablocks B lyA SA) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
 rec_repA B ly' S' (rdW W' mem') (fst (rec_answer R1 e shp true)) O' /\
 (forall pn, In pn O' <-> (In pn O1 /\ fst pn <> old) \/ pn = (p1, n)) /\
 astr_atR (rdW W' mem') p2 t /\
 mo_le MT SA S' (XM_ANSWER MT t).

(* after a symbolic run the model term grows (measured 2026-10-28): name it *)
Ltac sqc_md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.
Lemma rec_repA_pos : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> 0 < snd pn.
Proof. intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. exact (sqc_blocks_pos _ _ _ _ _ _ pn HA Hpn). Qed.

(* a live block is listed once *)
Lemma sqc_dup_false : forall ly S (W : world SEGS) mem md L1 L2 pn, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (L1 ++ L2) -> In pn L1 -> In pn L2 -> False.
Proof.
intros ly S W mem md L1 L2 pn HAR HP H1 H2.
pose proof H1 as H1'.
apply in_split in H1 as (a1 & b1 & ->). apply in_split in H2 as (a2 & b2 & ->).
assert (HP' : Permutation (ablocks B ly S) (pn :: pn :: (a1 ++ b1 ++ a2 ++ b2))).
{ eapply Permutation_trans; [exact HP|].
  rewrite <- app_assoc. cbn [app].
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  replace (a1 ++ b1 ++ a2 ++ pn :: b2) with ((a1 ++ b1 ++ a2) ++ pn :: b2) by (rewrite <- !app_assoc; reflexivity).
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  rewrite <- !app_assoc. reflexivity. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md pn pn _ HAR HP') as D.
assert (Hin : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact H1').
destruct pn as [b m].
destruct (sqc_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & Hr1).
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* the head of a permutation of the live blocks is apart from every other entry *)
Lemma sqc_head_apart : forall ly S (W : world SEGS) mem md x L y, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (x :: L) -> In y L ->
fst x + req_size (snd x) <= fst y \/ fst y + req_size (snd y) <= fst x.
Proof.
intros ly S W mem md x L y HAR HP Hy. apply in_split in Hy as (a & b & ->).
assert (HP' : Permutation (ablocks B ly S) (x :: y :: a ++ b)).
{ eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md x y _ HAR HP') as D. unfold zdisjoint, block_rng in D.
cbn [fst snd] in D. exact D.
Qed.

Lemma sqc_in_filter : forall (old : Z) (l : list (Z * Z)) pn,
In pn (filter (fun pn => fst pn =? old) l) -> In pn l /\ fst pn = old.
Proof.
intros old l pn. induction l as [|a l IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. revert Hd. destruct (fst a =? old) eqn:E; intros Hd; [apply Z.eqb_eq; exact E | destruct Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* the bytes answer may write: g_rec.answer, g_rec.state, and the old answer's block, which the recorder owns *)
Lemma sqc_awr_ans : forall STK sp O bl0 blc fr0 ly own (O1 : list (Z * Z)) old a,
(forall pn, In pn O1 -> fst pn = old -> In pn O /\ In pn blc) ->
inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
  ablocks_fp (filter (fun pn => fst pn =? old) O1)) a ->
awr_byte SEGS B STK sp (sqc_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own O1 old a HO (r & Hr & Hra).
assert (HG : A_G_REC <= a < A_G_REC + REC_SIZE -> awr_byte SEGS B STK sp (sqc_FP O) bl0 blc fr0 ly own a).
{ intros Ha. pose proof (recb_grec_in a Ha) as HP.
  right; right; right; right; left. split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
  exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha]. }
destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra.
- apply HG. unfold OFF_ANSWER, REC_SIZE in *. lia.
- apply HG. unfold OFF_STATE, REC_SIZE in *. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin).
  apply sqc_in_filter in Hin. destruct Hin as [Hin Hf]. cbn [fst snd] in *. destruct (HO (b, n) Hin Hf) as [HOb Hblc].
  right; left. split.
  + exists (b, b + req_size n). split; [|cbn [fst snd]; lia].
    unfold sqc_FP. right; right. unfold ablocks_fp. apply in_map_iff. exists (b, n). split; [reflexivity | exact HOb].
  + exists b, n. split; [exact Hblc | lia].
Qed.

Lemma sqc_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (sqc_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO (r & Hr & Ha). pose proof asan_consts as (C1 & _).
unfold sqc_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- unfold A_G_REC, REC_SIZE in Ha. lia.
- unfold A_REC_SPILL, SC_SIZE in Ha. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  destruct (sqc_blk_bounds ly S W mem md b n HAR (HO _ Hin)) as (_ & Hb & _). lia.
Qed.

(* the start of a block the recorder owns is the start of no other live block *)
Lemma sqc_same_start : forall ly S (W : world SEGS) mem md pn an, AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In an (ablocks B ly S) -> fst pn = fst an -> pn = an.
Proof.
intros ly S W mem md [b m] [b' m'] HAR H1 H2 Hf. cbn [fst] in Hf. subst b'.
destruct (recb_pair_dec (b, m) (b, m')) as [E | Hne]; [exact E|]. exfalso.
destruct (sqc_blk_bounds ly S W mem md b m HAR H1) as (_ & _ & _ & _ & R1).
destruct (sqc_blk_bounds ly S W mem md b m' HAR H2) as (_ & _ & _ & _ & R2).
destruct (sqc_blk_apart ly S W mem md b m b m' HAR H1 H2 Hne); lia.
Qed.

(* the bytes of a string argument decide astr_argA's reader part *)
Lemma sqc_argA_kept : forall ly S (rd rd' : reader) ro O p v, astr_argA B ly S rd ro O p (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly S rd' ro O p (Some v).
Proof.
intros ly S rd rd' ro O p v H K. cbn [astr_argA] in H |- *. destruct H as (H0 & Hs & Hl & Hr).
split; [exact H0|]. split; [exact (sqc_astr_kept rd rd' p v Hs K)|]. split; [exact Hl | exact Hr].
Qed.

Lemma sqc_argA_range : forall ly S (W : world SEGS) mem md O p v, AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some v) ->
forall i, 0 <= i < Z.of_nat (length v) + 1 -> 0 <= p + i < 2 ^ 64.
Proof.
intros ly S W mem md O p v HAR H i Hi. cbn [astr_argA] in H. destruct H as (_ & _ & _ & [(Hblk & _) | (Hro & _)]).
- destruct Hblk as (b & m & Hin & Hb1 & Hb2).
  destruct (sqc_blk_bounds ly S W mem md b m HAR Hin) as (Hb & Hc & _ & Hmr & _).
  pose proof asan_consts as (C1 & _). lia.
- destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))). lia.
Qed.

Lemma sqc_bytes_prefix : forall (rd : reader) a l l2, abytes_atR rd a (l ++ l2) -> abytes_atR rd a l.
Proof. intros rd a l l2 H i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity. Qed.

Lemma sqc_bytes_eq : forall (rd : reader) a l l', abytes_atR rd a l -> map bv_unsigned l = map bv_unsigned l' ->
abytes_atR rd a l'.
Proof.
intros rd a l l' H E i Hi.
assert (Hl : length l = length l') by (rewrite <- (length_map bv_unsigned l), E, length_map; reflexivity).
rewrite (H i) by lia. f_equal.
rewrite <- (map_nth bv_unsigned l (Z_to_bv 8 0) i), <- (map_nth bv_unsigned l' (Z_to_bv 8 0) i), E. reflexivity.
Qed.

Lemma sqc_no_zero : forall l : list byte, forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
intros l H Hin. rewrite forallb_forall in H. specialize (H _ Hin). vm_compute in H. discriminate.
Qed.

(* a byte range none of whose bytes the runtime owns and which is not the errno cell, decided on the record's lists *)
Lemma sqc_unowned_rng : forall lo n,
forallb (fun r => (fst r + snd r <=? lo) || (lo + n <=? fst r)) Tfib_owned_static = true ->
((TFIB_ERRNO + 4 <=? lo) || (lo + n <=? TFIB_ERRNO)) = true ->
forall a, lo <= a < lo + n -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros lo n Hf He a Ha. rewrite (ts_owned B HB), (ts_errno B HB). split.
- intros Hex. apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in Hf. specialize (Hf r Hr).
  unfold in_zr in Hz. apply orb_true_iff in Hf as [Hf | Hf]; apply Z.leb_le in Hf; lia.
- apply orb_true_iff in He as [He | He]; apply Z.leb_le in He; lia.
Qed.

(* one register of a seed's regs_ok: the slot, its nargs field, the shadow base, s4, or a register of its own *)
Ltac sqc_reg1 E34 E32 G8 G18 G19 G20 :=
lazymatch goal with |- getr ?rg ?r = sv_denot ?E (sr_get ?a ?r) =>
  let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v end;
first
[ let G := fresh in pose proof G20 as G; rewrite <- (sqc_shx4_denot _ _ E34 E32) in G by lia; exact G
| cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; exact G8
| cbn [sv_denot]; rewrite E34, unsigned_lit_small by lia; exact G18
| cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact G19
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  first [ symmetry; apply sqc_E_reg; reflexivity | symmetry; apply getr_zero | reflexivity ] ].
Ltac sqc_regs_ok E34 E32 G8 G18 G19 G20 :=
apply regs_ok_by_cases; let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbv [all_regs In] in Hr;
repeat (destruct Hr as [<- | Hr]; [sqc_reg1 E34 E32 G8 G18 G19 G20 | ]); try (destruct Hr; fail).
(* the writes of a segment after the prologue: the frame is read-only, the slot's first 16 bytes are g_rec's or
   record.spill's *)
Ltac sqc_awr UC Hc :=
lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end;
apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|];
eapply awr_ok_cons_gen; [reflexivity | exact UC | | apply awr_ok_nil];
cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
apply (sqc_awr_slot _ _ _ _ _ _ _ _ _ a Hc); unfold CALL_SIZE; lia.

(* ---------- after the prologue: from the call of xstrdup to the end ---------- *)
(* the walk from the call of xstrdup (0x8b8f8) on: the state there, against the entry and the base *)
Definition sqc_SX_spec : Prop := forall ly S W regs mem md ch pw which R O Q lyc Sc Wc memT mdT k lyB SBa WB memB R0 O0 F
  (regsT : bvmap 5 word) sx,
sqc_pre ly S W regs mem md ch pw which R O ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q -> (forall pn, In pn O <-> In pn (lay_blocks Q)) ->
sqc_mid ly S W regs mem md R O lyc Sc Wc memT mdT k lyB SBa WB memB R0 O0 F ->
sqc_recmem (rdW Wc memT) (rdW WB memB) (sqc_slot R0) 16 ->
sqc_ncalls_ok (rdW Wc memT) R0 ->
aval_mem (rdW Wc memT) (sqc_slot R0 + CALL_OFF_FN) 4 SQ_FN ->
aval_mem (rdW Wc memT) (sqc_slot R0 + CALL_OFF_NARGS) 4 0 ->
getr regsT 1 = w64 (BASE + SQ_RETX) -> getr regsT 2 = w64 (spZ regs - SQ_FRAME) ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 8 = w64 (sqc_slot R0) -> getr regsT 18 = w64 (sqc_slot R0 + 4) -> getr regsT 19 = w64 SB ->
getr regsT 20 = w64 (SB + (sqc_slot R0 + 4) / 8) -> getr regsT 10 = w64 sx ->
(forall r, 21 <= r <= 27 -> getr regsT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
astr_argA B lyc Sc (rdW Wc memT) (in_roP SEGS RLO RHI) [] sx (Some (sarg which)) ->
atail_vis SEGS Wc memT (sx + Z.of_nat (length (sarg which))) ->
SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS_xstrdup)) memT (seg_rom SEGS)) mdT)
(apost_baseF SEGS B SQC_STK (sqc_FP O) regs ly S W mem md (EV_SUP_QUARANTINE_CLEAR R) (sqc_Q ly S R O which)).

Lemma sqc_SX : sqc_SX_spec.
Proof.
intros ly S W regs mem md ch pw which R O Q lyc Sc Wc memT mdT k lyB SBa WB memB R0 O0 F regsT sx
  PRE HQ HOQ MID RM NC VFN VNA R1 R2 R3 R4 R8 R18 R19 R20 R10 RS7 HSTR HTAIL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & HRM0 & HROD & HRO & H10 & Hpw & HARG & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk & HFRM & HREPB & HSP0 & HLEN0 & HREC0 & HKO0 & HIO0 & HPERM & HFO & HO0 & HFN & MLE).
pose proof (proj1 HJ) as HARc.
set (sp0 := spZ regs) in *.
set (c := sqc_slot R0) in *.
set (x := sarg which) in *.
assert (HST : SQC_STK = 16592) by reflexivity.
assert (Hn16 : (length (r_calls R0) <= 16)%nat).
{ destruct HREPB as (QB & (_ & _ & _ & (G1 & _) & _) & _). exact G1. }
assert (Hc : sqc_slot_ok c) by exact (sqc_slot_ok_of R0 Hn16).
destruct (sqc_slot_bounds c Hc) as (Hcb & Hc8 & Hch').
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (lay_blocks_in _ _ _ _ _ _ HQ). apply HOQ. exact Hpn. }
(* the call of xstrdup (0x8b8f8) *)
assert (Ssp : spZ regsT = sp0 + -48) by (unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small; unfold SQ_FRAME; lia).
rewrite (SIGP CS_xstrdup ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_xstrdup) with (BASE + AF_xstrdup).
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regsT memT _ SQC_STK sp0 (sqc_FP O) ly S W mem md [] lyc Sc mdT k XSTRDUP_STK [] EV_XSTRDUP
    (-48) (w64 (BASE + SQ_RETX)) []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z,
      getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
      Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP x) :: ablocks B lyc Sc) /\
      Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
      astr_atR (rdW W2 mem2) p x /\ astr_atR (rdW W2 mem2) sx x /\
      blocks_bytes S2 <= blocks_bytes Sc + LIVE_XSTRDUP x /\
      mo_le MT Sc S2 (XM_XSTRDUP MT x)) HJ Ssp).
  - reflexivity.
  - lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - rewrite HST. unfold XSTRDUP_STK, ASTACK. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - unfold w64. apply ret_ok_codeptr_v; [unfold SQ_RETX, AF_sup_quarantine_clear; lia | reflexivity].
  - unfold w64, SQ_RETX, AF_sup_quarantine_clear. pose proof HBASE as (HB0 & HB1 & _).
    rewrite unsigned_lit_small; lia.
  - apply achain_low. unfold s0Z. rewrite R8. unfold w64.
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1. eapply SRr_mono.
    + apply (TXSTRDUP fx lyc Sc Wc regsT memT mdT [] sx x HPRE1).
      * exact (sqc_aro ly S W mem md O lyc Sc Wc memT mdT [] k sp0 HAR HOin HJ HROD).
      * exact R10.
      * left. exact HSTR.
      * exact HTAIL.
      * pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
        unfold EV_SUP_QUARANTINE_CLEAR, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia.
      * rewrite (blocks_bytes_bsum B lyc Sc). rewrite (blocks_bytes_bsum B ly S) in HLIVE.
        rewrite (bsum_perm _ _ HPERM), bsum_app in HLIVE.
        assert (HF0 : 0 <= bsum F).
        { apply (sqc_bsum_nonneg ly S W mem md F HAR). intros pn Hpn.
          apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. right. exact Hpn. }
        unfold LIVE_SUP_QUARANTINE_CLEAR, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in *. fold x in HLIVE. lia.
      * apply (mo_ok_le MT MTL Sc (XM_XSTRDUP MT x) (XM_XSTRDUP MT x + XM_ANSWER MT (snd (sup_quarantine_clear_m R which)))).
        -- apply (mo_ok_step MT MTL S Sc (Z.of_nat (length F) * mo_free MT)); [|exact MLE].
           unfold XM_SUP_QUARANTINE_CLEAR in HMOK. rewrite <- HFN in HMOK. fold x in HMOK.
           replace (Z.of_nat (length F) * mo_free MT + (XM_XSTRDUP MT x + XM_ANSWER MT (snd (sup_quarantine_clear_m R which))))
             with (Z.of_nat (length F) * mo_free MT + XM_XSTRDUP MT x + XM_ANSWER MT (snd (sup_quarantine_clear_m R which))) by lia.
           exact HMOK.
        -- unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
           pose proof (mo_free_nonneg MT MTL) as Hf.
           pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_quarantine_clear_m R which))) + 1) ltac:(lia)) as Hm.
           lia.
    + cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite R1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
      destruct HQ3 as (pq & A1 & A2 & A3 & A4 & _ & A6 & A7 & A8 & A9).
      exact (ex_intro _ pq (conj A1 (conj A2 (conj A3 (conj A4 (conj A6 (conj A7 (conj A8 A9)))))))).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (p & Hp10 & Hp4096 & Hperm2 & Hfresh2 & Hpstr & Hsstr & HBB2 & MLE2)).
pose proof (proj1 HJ2) as HAR2.
assert (Hceil0 : alloc_ceiling <= sp0 - 48) by (rewrite HST in Hslo; lia).
assert (CS2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regsT rr)
  by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (KST2 : forall a, sp0 - 48 <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW Wc memT a).
{ intros a Ha. apply (sqc_keep_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2);
  [intros b Hb; exfalso; exact (inFP_nil b Hb) | lia | lia]. }
assert (KPG2 : forall a, Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW Wc memT a).
{ intros a HP. apply (sqc_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc2); [constructor | intros Hf; exact (inFP_nil a Hf) | exact HP]. }
assert (HFRM2 : sqc_frame_at (mrestrict (w_H W2) mem2) (sp0 - SQ_FRAME) regs).
{ intros j r Hjr. apply (sqc_val_kept Wc W2 memT mem2); [exact (HFRM j r Hjr)|].
  intros kk Hkk. apply KST2. assert (Hj : (j < 6)%nat) by (change 6%nat with (length sqc_saved); apply nth_error_Some; rewrite Hjr; discriminate).
  unfold SQ_FRAME. lia. }
assert (VFN2 : aval_mem (rdW W2 mem2) (c + CALL_OFF_FN) 4 SQ_FN).
{ apply (sqc_aval_kept (rdW Wc memT)); [exact VFN|]. intros kk Hkk. apply KPG2. apply (sqc_in_PG_slot c); [exact Hc|].
  unfold CALL_OFF_FN, CALL_SIZE. lia. }
assert (VNA2 : aval_mem (rdW W2 mem2) (c + CALL_OFF_NARGS) 4 0).
{ apply (sqc_aval_kept (rdW Wc memT)); [exact VNA|]. intros kk Hkk. apply KPG2. apply (sqc_in_PG_slot c); [exact Hc|].
  unfold CALL_OFF_NARGS, CALL_SIZE. lia. }
set (nn := Z.of_nat (length (r_calls R0))).
assert (Hnn : 0 <= nn <= 16) by (subst nn; lia).
assert (Q2 : getr regs2 2 = w64 (sp0 - 48)) by (rewrite (CS2 2%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); rewrite R2; reflexivity).
assert (Q2u : bv_unsigned (getr regs2 2) = sp0 - 48) by (rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (E34 : ew (sqc_E regs2 regs nn c) 34 = Z_to_bv 64 c)
  by (rewrite (sqc_E_extra_at regs2 regs nn c 34 ltac:(lia)); reflexivity).
assert (E32 : ew (sqc_E regs2 regs nn c) 32 = Z_to_bv 64 SB)
  by (rewrite (sqc_E_extra_at regs2 regs nn c 32 ltac:(lia)); reflexivity).
assert (G8 : getr regs2 8 = Z_to_bv 64 c) by (rewrite (CS2 8%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R8).
assert (G18 : getr regs2 18 = Z_to_bv 64 (c + 4)) by (rewrite (CS2 18%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R18).
assert (G19 : getr regs2 19 = Z_to_bv 64 SB) by (rewrite (CS2 19%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R19).
assert (G20 : getr regs2 20 = Z_to_bv 64 (SB + (c + 4) / 8)) by (rewrite (CS2 20%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R20).
assert (Hcr : 0 <= c < 2 ^ 40) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb; lia).
destruct (sqc_seed B HB VOBJS cmd_prog_writable SQ_RETX sqc_regsD
  [YP09.mkChunk 4 (CVal 4 (SLit 0)); YP09.mkChunk 0 (CVal 4 (SLit 11))] W2 regs2 regs mem2 ly2 S2 md2 nn c HAR2)
  as [HS SHOK].
{ rewrite Q2u. unfold SQ_FRAME. lia. }
{ rewrite Q2u. replace (sp0 - 48) with (sp0 + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
{ exact Hnn. }
{ exact Hc. }
{ sqc_regs_ok E34 E32 G8 G18 G19 G20. }
{ rewrite Q2u. exact HFRM2. }
{ vm_compute. reflexivity. }
{ constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS _ _ c 4 4 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    apply (val_mem_view SEGS). exact VNA2.
  - apply (chunk_ok_val SEGS _ _ c 0 4 (SLit 11) 11); [reflexivity | cbn; lia | cbn; lia |].
    apply (val_mem_view SEGS). exact VFN2. }
pose proof (sqc_E_img regs2 regs nn c) as HEI.
assert (UC : bv_unsigned (ew (sqc_E regs2 regs nn c) SQ_C) = c) by (unfold SQ_C; rewrite E34; apply unsigned_lit_small; lia).
remember (sqc_E regs2 regs nn c) as E eqn:HE.
unfold w64. change (BASE + SQ_RETX) with (BASE + SQ_RETX).
(* 0x8b8fc .. 0x8b93c: the two checks after the call, c->nargs := 1, c->args[0] := the copy, the call of rec_shape_of *)
paj_run_tok RUN HS HJ2 SHOK sqc_Bspan.
{ sqc_awr UC Hc. }
pmkst HS. sqc_md.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew E kk = getr regs2 rr)
  by (intros kk rr Hkk; rewrite HE; apply sqc_E_reg; exact Hkk).
assert (V306 : ew E 306 = Z_to_bv 64 0x21e00).
{ pose proof (HEI 306%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H306.
  change (VAL 306%nat) with (VAL (A_OBJ 65)) in H306. rewrite (VOBJS 65%nat ltac:(vm_compute; lia)) in H306.
  apply bv_eq. rewrite H306. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
assert (Q1 : getr (ms_regs ms) 1 = w64 (BASE + SQ_RETS)) by (rewrite P1; reflexivity).
assert (Q2s : spZ (ms_regs ms) = sp0 + -48)
  by (unfold spZ; rewrite P2, (EE 2%nat 2%bv eq_refl), Q2; unfold w64; rewrite unsigned_lit_small; lia).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite P3, (EE 3%nat 3%bv eq_refl), (CS2 3%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite P4, (EE 4%nat 4%bv eq_refl), (CS2 4%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R4).
assert (Q10 : getr (ms_regs ms) 10 = w64 0x21e00) by (rewrite P10, V306; reflexivity).
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat (length sqc_verb))) by (rewrite P11; reflexivity).
assert (Q8 : s0Z (ms_regs ms) = c) by (unfold s0Z; rewrite P8, E34; apply unsigned_lit_small; lia).
pose proof (proj1 HJ2) as HARd.
assert (HAROd : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms)))
  by exact (sqc_aro ly S W mem md O ly2 S2 W2 (ms_mem ms) _ [] _ sp0 HAR HOin HJ2 HROD).
assert (HROd : cmd_ro_ok (rdW W2 (ms_mem ms))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARd HAROd).
(* what run D wrote: the slot's fn, nargs and args[0]; every other byte is kept *)
assert (UC34 : bv_unsigned (ew E 34) = c) by exact UC.
assert (Usp2 : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (EE 2%nat 2%bv eq_refl), Q2; unfold w64; apply unsigned_lit_small; lia).
lazymatch goal with HFx : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into HFRD end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c <= a < c + 16) HFRD
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?UC34 in Hrr; lia|]);
        destruct Hin)) as KD.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 1 (ss_mem ssx) sqc_frame) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H W2) msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRgD;
  cbn [ms_mem restrict mkst] in HRgD end.
pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 0 4%N (SLit 11) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VFND.
pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 4 4%N (SLit 1) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VNAD.
pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 8 8%N (SOff 10 0) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VA0D.
(* the call of rec_shape_of("quarantine_clear", 16) (0x8b93c) *)
rewrite (SIGP CS_rec_shape_of ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_rec_shape_of) with (BASE + AF_rec_shape_of).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W2 (ms_regs ms) (ms_mem ms) _ SQC_STK sp0 (sqc_FP O) ly S W mem md [] ly2 S2 _ _
    REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-48) (w64 (BASE + SQ_RETS))
    (fun ly3 S3 W3 regs3 mem3 md3 =>
      (exists q, getr regs3 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
       forall O1, astr_argA B ly3 S3 (rdW W3 mem3) (in_roP SEGS RLO RHI) O1 q (Some (shape_of sqc_verb))) /\
      Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\ ly3 = ly2 /\ S3 = S2) HJ2 Q2s).
  - reflexivity.
  - lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - rewrite HST. unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - unfold w64. apply ret_ok_codeptr_v; [unfold SQ_RETS, AF_sup_quarantine_clear; lia | reflexivity].
  - unfold w64, SQ_RETS, AF_sup_quarantine_clear. pose proof HBASE as (HB0 & HB1 & _).
    rewrite unsigned_lit_small; lia.
  - intros HPRE1. eapply SRr_mono.
    + apply (TREC_SHAPE_OF fx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ 0x21e00 sqc_verb HPRE1 HAROd Q10 ltac:(lia) Q11
        ltac:(vm_compute; reflexivity) HROd VOBJS).
      * intros _.
        assert (HL : abytes_atR (rdW W2 (ms_mem ms)) 0x21e00 RO_lit_21e00).
        { destruct HROd as [HRB _]. unfold cmd_ro_bytes in HRB.
          repeat match type of HRB with
          | abytes_atR _ 0x21e00 _ /\ _ => exact (proj1 HRB)
          | _ /\ _ => apply proj2 in HRB
          end. }
        assert (HVS : astr_atR (rdW W2 (ms_mem ms)) 0x21e00 sqc_verb).
        { split; [apply (sqc_bytes_eq _ _ _ _ HL); vm_compute; reflexivity|].
          apply sqc_no_zero. vm_compute. reflexivity. }
        split; [exact (sqc_bytes_prefix _ _ _ _ (proj1 HVS))|].
        right. cbn [astr_argA]. split; [lia|]. split; [exact HVS|]. split; [vm_compute; congruence|].
        right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity|]]].
        -- intros i Hi. change (Z.of_nat (length sqc_verb) + 1) with 17 in Hi. split.
           ++ assert (HRI : forall i, 0 <= i < 17 -> in_roP SEGS RLO RHI (0x21e00 + i)).
              { clear - CMD_RO_IN. pose proof CMD_RO_IN as HROIN. unfold cmd_ro_in in HROIN.
                repeat match type of HROIN with
                | (forall i, 0 <= i < 17 -> _ (0x21e00 + i)) /\ _ => exact (proj1 HROIN)
                | _ /\ _ => apply proj2 in HROIN
                end. }
              exact (HRI i Hi).
           ++ apply (sqc_unowned_rng 0x21e00 17); [vm_compute; reflexivity | vm_compute; reflexivity | lia].
        -- change (0x21e00 + Z.of_nat (length sqc_verb)) with 0x21e10. unfold cmd_ro_ends.
           repeat first [left; reflexivity | right].
      * pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
        unfold EV_REC_SHAPE_OF, EV_SUP_QUARANTINE_CLEAR, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia.
    + cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite Q1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
      exact HQ3.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 &
  ((q & Hq10 & Hq64 & HqA) & Hperm3 & Ely3 & ES3)).
pose proof (proj1 HJ3) as HAR3.
(* back at 0x8b940: the frame is kept, the rest of the state is the callee's *)
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp2; intros a Ha.
  - apply (mbyte_of_aview SEGS).
    apply (sqc_keep_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3); [intros b Hb; exfalso; exact (inFP_nil b Hb) | lia | lia].
  - lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 48 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew E3 n = ew E n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (A58 : ew E3 52 = getr regs3 10) by (rewrite HE3; reflexivity).
clear HE3.
assert (SHOK3 : sh_ok SEGS sqc_Bx [] E3 (mrestrict (w_H W3) mem3)) by (unfold sh_ok; constructor).
(* 0x8b940 .. 0x8b968: a2 := 1, a1 := the shape, a0 := c, the frame's registers back, sp += 48, j answer *)
paj_run_tok RUN HS HJ3 SHOK3 sqc_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]. apply awr_ok_nil. }
pmkst HS. sqc_md.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
(* run E kept every byte *)
lazymatch goal with HFx : frame_of E3 _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into HFRE end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFRE
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KE.
pose proof (proj1 HJ3) as HARA.
(* the registers at the jump to answer: the entry's callee-saved registers and sp, ra, a0 = c, a1 = the shape, a2 = 1 *)
assert (OE : forall n, (n < 48)%nat -> ew E3 n = ew (sqc_E regs2 regs nn c) n)
  by (intros n Hn; rewrite OLD3 by exact Hn; rewrite HE; reflexivity).
assert (CSr : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> acallee_saved (bv_unsigned rr) ->
  ew E3 n = getr regsT rr).
{ intros n rr Hn Hcs. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite OE by lia. rewrite (sqc_E_reg regs2 regs nn c n rr Hn). apply CS2. exact Hcs. }
assert (A1 : getr (ms_regs ms0) 1 = getr regs 1).
{ rewrite T1, OE by lia. rewrite (sqc_E_extra_at regs2 regs nn c 35 ltac:(lia)). reflexivity. }
assert (X2 : getr (ms_regs ms0) 2%bv = getr regs 2%bv).
{ rewrite T2, OE by lia. rewrite (sqc_E_reg regs2 regs nn c 2 2%bv eq_refl), Q2. unfold w64.
  rewrite unsigned_lit_small by lia. replace (sp0 - 48 + 48) with sp0 by lia. unfold sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (X3 : getr (ms_regs ms0) 3%bv = getr regs 3%bv).
{ rewrite T3. rewrite (CSr 3%nat 3%bv eq_refl) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia). rewrite R3, Hgp. reflexivity. }
assert (X4 : getr (ms_regs ms0) 4%bv = getr regs 4%bv).
{ rewrite T4. rewrite (CSr 4%nat 4%bv eq_refl) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia). rewrite R4, Htp. reflexivity. }
assert (X8 : getr (ms_regs ms0) 8%bv = getr regs 8%bv)
  by (rewrite T8, OE by lia; rewrite (sqc_E_extra_at regs2 regs nn c 36 ltac:(lia)); reflexivity).
assert (X9 : getr (ms_regs ms0) 9%bv = getr regs 9%bv)
  by (rewrite T9, OE by lia; rewrite (sqc_E_extra_at regs2 regs nn c 37 ltac:(lia)); reflexivity).
assert (X18 : getr (ms_regs ms0) 18%bv = getr regs 18%bv)
  by (rewrite T18, OE by lia; rewrite (sqc_E_extra_at regs2 regs nn c 38 ltac:(lia)); reflexivity).
assert (X19 : getr (ms_regs ms0) 19%bv = getr regs 19%bv)
  by (rewrite T19, OE by lia; rewrite (sqc_E_extra_at regs2 regs nn c 39 ltac:(lia)); reflexivity).
assert (X20 : getr (ms_regs ms0) 20%bv = getr regs 20%bv)
  by (rewrite T20, OE by lia; rewrite (sqc_E_extra_at regs2 regs nn c 40 ltac:(lia)); reflexivity).
assert (XH : forall (rr : bv 5) n, Z.of_nat n = bv_unsigned rr -> 21 <= bv_unsigned rr <= 27 ->
  ew E3 n = getr regs rr).
{ intros rr n Hn Hr. rewrite (CSr n rr Hn) by (unfold acallee_saved; lia).
  rewrite <- (Z_to_bv_bv_unsigned 5 rr). apply RS7. exact Hr. }
assert (X21 : getr (ms_regs ms0) 21%bv = getr regs 21%bv) by (rewrite T21; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X22 : getr (ms_regs ms0) 22%bv = getr regs 22%bv) by (rewrite T22; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X23 : getr (ms_regs ms0) 23%bv = getr regs 23%bv) by (rewrite T23; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X24 : getr (ms_regs ms0) 24%bv = getr regs 24%bv) by (rewrite T24; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X25 : getr (ms_regs ms0) 25%bv = getr regs 25%bv) by (rewrite T25; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X26 : getr (ms_regs ms0) 26%bv = getr regs 26%bv) by (rewrite T26; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (X27 : getr (ms_regs ms0) 27%bv = getr regs 27%bv) by (rewrite T27; apply XH; [reflexivity | rewrite bv_unsigned_BV; lia]).
assert (HPA : aregs_preserved regs (ms_regs ms0))
  by exact (sqc_pres' regs (ms_regs ms0) X2 X3 X4 X8 X9 X18 X19 X20 X21 X22 X23 X24 X25 X26 X27).
(* ---- the memory at the jump, against the call of xstrdup and the base ---- *)
assert (HRK3 : forall a, 0 <= a < 2 ^ 64 -> rdW W3 (ms_mem ms0) a = rdW W3 mem3 a)
  by (intros a Ha; exact (KE a Ha (fun H => H))).
assert (KAP : forall a, Exists (in_zr a) recb_PG -> ~ (c <= a < c + 16) -> rdW W3 (ms_mem ms0) a = rdW Wc memT a).
{ intros a HP Hs. pose proof (pa_img_range a (cmd_prog_img a HP)) as Hr.
  rewrite HRK3 by lia.
  rewrite (sqc_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3); [| constructor | intros Hf; exact (inFP_nil a Hf) | exact HP].
  rewrite (KD a ltac:(lia) Hs). exact (KPG2 a HP). }
assert (KAS : forall a, c <= a < c + 16 -> rdW W3 (ms_mem ms0) a = rdW W2 (ms_mem ms) a).
{ intros a Ha. pose proof (sqc_in_PG_slot c a Hc ltac:(unfold CALL_SIZE; lia)) as HP.
  pose proof (pa_img_range a (cmd_prog_img a HP)) as Hr. rewrite HRK3 by lia.
  apply (sqc_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3); [constructor | intros Hf; exact (inFP_nil a Hf) | exact HP]. }
assert (KAB2 : forall b m i, In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m ->
  rdW W3 (ms_mem ms0) (b + i) = rdW W2 mem2 (b + i)).
{ intros b m i Hin Hi. destruct (sqc_blk_bounds ly2 S2 W2 mem2 md2 b m HAR2 Hin) as (Hb0 & Hb1 & _).
  pose proof asan_consts as (CC1 & _). rewrite HRK3 by lia.
  rewrite (sqc_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m i HJc3 Hin
    ltac:(apply (Permutation_in _ (Permutation_sym Hperm3)); exact Hin) Hi ltac:(intros Hf; exact (inFP_nil _ Hf))).
  apply KD; [lia|]. intros Hs. apply (sqc_blk_noprog ly2 S2 W2 mem2 md2 b m (b + i) HAR2 Hin ltac:(lia)).
  apply (sqc_in_PG_slot c); [exact Hc | unfold CALL_SIZE; lia]. }
assert (KABT : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
  rdW W3 (ms_mem ms0) (b + i) = rdW Wc memT (b + i)).
{ intros b m i Hin Hi.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); right; exact Hin).
  rewrite (KAB2 b m i Hin2 Hi).
  exact (sqc_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m i HJc2 Hin Hin2 Hi ltac:(intros Hf; exact (inFP_nil _ Hf))). }
assert (HIN3 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly3 S3)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm3)). apply (Permutation_in _ (Permutation_sym Hperm2)).
  right. exact Hpn. }
assert (HPIN3 : In (p, LIVE_XSTRDUP x) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). apply (Permutation_in _ (Permutation_sym Hperm2)). left. reflexivity. }
assert (HPIN2 : In (p, LIVE_XSTRDUP x) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm2)); left; reflexivity).
assert (Hxlen : Z.of_nat (length x) + 1 <= LMAX + 1) by (destruct HSTR as (_ & _ & H & _); exact H).
(* the slot's fields at the jump *)
change (N.to_nat 4) with 4%nat in VFND, VNAD. change (N.to_nat 8) with 8%nat in VA0D.
replace (bv_unsigned (sv_denot E (SLit 11)) mod 2 ^ (8 * Z.of_N 4)) with 11 in VFND by (vm_compute; reflexivity).
replace (bv_unsigned (sv_denot E (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in VNAD by (vm_compute; reflexivity).
assert (Hpr : p < 2 ^ 64).
{ destruct (sqc_blk_bounds ly2 S2 W2 mem2 md2 p _ HAR2 HPIN2) as (_ & Hb1 & _ & _ & Hr1). pose proof asan_consts as (CC1 & _). lia. }
replace (bv_unsigned (sv_denot E (SOff 10 0)) mod 2 ^ (8 * Z.of_N 8)) with p in VA0D
  by (cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), Hp10, Z.add_0_r, Z_to_bv_bv_unsigned; unfold w64;
      rewrite unsigned_lit_small by lia; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); rewrite Z.mod_small by lia; reflexivity).
assert (VFNA : aval_mem (rdW W3 (ms_mem ms0)) (sqc_slot R0 + CALL_OFF_FN) 4 SQ_FN).
{ apply (sqc_aval_kept (rdW W2 (ms_mem ms))); [exact (aval_mem_view SEGS _ _ _ _ _ VFND)|].
  intros kk Hkk. apply KAS. unfold CALL_OFF_FN. lia. }
assert (VNAA : aval_mem (rdW W3 (ms_mem ms0)) (sqc_slot R0 + CALL_OFF_NARGS) 4 1).
{ apply (sqc_aval_kept (rdW W2 (ms_mem ms))); [exact (aval_mem_view SEGS _ _ _ _ _ VNAD)|].
  intros kk Hkk. apply KAS. unfold CALL_OFF_NARGS. lia. }
assert (VA0A : aval_mem (rdW W3 (ms_mem ms0)) (sqc_slot R0 + CALL_OFF_ARGS) 8 p).
{ apply (sqc_aval_kept (rdW W2 (ms_mem ms))); [exact (aval_mem_view SEGS _ _ _ _ _ VA0D)|].
  intros kk Hkk. apply KAS. unfold CALL_OFF_ARGS. lia. }
(* record(11) and arg_s, over the base *)
assert (HREP1 : rec_repA B ly3 S3 (rdW W3 (ms_mem ms0)) (rec_record R0 SQ_FN [x]) ((p, Z.of_nat (length x) + 1) :: O0)).
{ apply (sqc_rec_repA_record1 B lyB SBa (rdW WB memB) ly3 S3 (rdW W3 (ms_mem ms0)) R0 O0 SQ_FN x p HREPB HSP0).
  - unfold SQ_FN, REC_FN_COUNT. lia.
  - unfold LMAX in *. lia.
  - rewrite (sqc_ncalls_len R0 [x] [[]]). apply (sqc_aval_kept (rdW Wc memT)); [exact NC|].
    intros kk Hkk. apply KAP; [apply recb_grec_in; unfold OFF_NCALLS, REC_SIZE; lia|].
    unfold A_G_REC, OFF_NCALLS, OFF_CALLS in *. lia.
  - exact VFNA.
  - exact VNAA.
  - exact VA0A.
  - intros a Hin Hnc Hns. rewrite (KAP a); [| destruct Hin as [Hin | Hin]; [apply recb_grec_in | apply recb_spill_in]; exact Hin | exact Hns].
    apply RM; [exact Hin | exact Hnc | lia].
  - intros [b m] i Hpn Hi. cbn [fst snd] in *. pose proof (HIO0 _ Hpn) as Hin.
    destruct (sqc_blk_bounds lyc Sc Wc memT mdT b m HARc Hin) as (_ & _ & _ & Hmr & _).
    rewrite (KABT b m i Hin ltac:(lia)). exact (HKO0 (b, m) i Hpn Hi).
  - intros pn Hpn. apply HIN3. apply HIO0. exact Hpn.
  - exact HPIN3.
  - rewrite Forall_forall. intros qk Hqk. rewrite Forall_forall in Hfresh2. apply Hfresh2. apply HIO0. exact Hqk.
  - apply (sqc_heap_apart ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) A_G_REC REC_SIZE HAR2 HPIN2); [unfold REC_SIZE; lia|].
    intros a Ha. apply cmd_prog_img. apply recb_grec_in. exact Ha.
  - apply (sqc_heap_apart ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) A_REC_SPILL SC_SIZE HAR2 HPIN2); [unfold SC_SIZE; lia|].
    intros a Ha. apply cmd_prog_img. apply recb_spill_in. exact Ha.
  - lia.
  - apply (sqc_astr_kept (rdW W2 mem2)); [exact Hpstr|]. intros i Hi.
    destruct (sqc_blk_bounds ly2 S2 W2 mem2 md2 p _ HAR2 HPIN2) as (_ & _ & _ & Hmr & _). unfold LIVE_XSTRDUP in Hmr.
    exact (KAB2 p (LIVE_XSTRDUP x) i HPIN2 ltac:(unfold LIVE_XSTRDUP; lia)). }
(* the old answer: the base layout's answer block, one of O0, its address still in g_rec.answer *)
pose proof HREPB as (QB & HQB & HOQB).
destruct (sqc_old_at _ _ _ _ HQB) as [HOLDB HOLDBin].
assert (HOLD : aval_mem (rdW W3 (ms_mem ms0)) (A_G_REC + OFF_ANSWER) 8 (sqc_old QB)).
{ apply (sqc_aval_kept (rdW WB memB)); [exact HOLDB|]. intros kk Hkk.
  assert (Hcs : c + 16 <= A_G_REC + OFF_ANSWER \/ A_REC_SPILL <= c).
  { destruct Hch' as [Hh | ->]; [left | right; lia]. unfold sqc_slot in *.
    unfold c, sqc_slot in Hh |- *. destruct (Nat.ltb_spec (length (r_calls R0)) 16) as [L|L];
      unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER, REC_SIZE, A_REC_SPILL in *; lia. }
  rewrite (KAP (A_G_REC + OFF_ANSWER + Z.of_nat kk)); [| apply recb_grec_in; unfold OFF_ANSWER, REC_SIZE; lia | unfold A_G_REC, A_REC_SPILL, OFF_ANSWER in *; lia].
  apply RM; [left; unfold OFF_ANSWER, REC_SIZE; lia | unfold OFF_NCALLS, OFF_ANSWER; lia | unfold A_G_REC, A_REC_SPILL, OFF_ANSWER in *; lia]. }
assert (HOLD0 : forall pn, In pn ((p, Z.of_nat (length x) + 1) :: O0) -> fst pn = sqc_old QB -> In pn O0).
{ intros pn [<- | Hpn] Hf; [|exact Hpn]. exfalso. cbn [fst] in Hf.
  unfold sqc_old in Hf. destruct (l_answer QB) as [an|] eqn:Ean.
  - pose proof (HOLDBin an eq_refl) as Han. apply HOQB in Han. destruct an as [a1 a2]. cbn [fst] in Hf. subst a1.
    rewrite Forall_forall in Hfresh2.
    pose proof (Hfresh2 (p, a2) (HIO0 _ Han)) as Hap. cbn [fst snd] in Hap. unfold iv_apart, LIVE_XSTRDUP in Hap.
    pose proof (rec_repA_pos lyB SBa (rdW WB memB) R0 O0 HREPB (p, a2) Han) as Hpos. cbn [snd] in Hpos. lia.
  - lia. }
assert (HO1in : forall pn, In pn ((p, Z.of_nat (length x) + 1) :: O0) -> In pn (ablocks B ly3 S3)).
{ intros pn [<- | Hpn]; [exact HPIN3 | apply HIN3; apply HIO0; exact Hpn]. }
(* ---- the tail jump into answer (0x8b968): answer runs at the entry's sp and returns to the entry's ra ---- *)
pose proof (proj1 HJ3) as HARJ.
assert (HM : sup_quarantine_clear_m R which = rec_answer (rec_record R0 SQ_FN [x]) (SQ_FN, [x]) (shape_of sqc_verb) true).
{ unfold sup_quarantine_clear_m, rec_stub. rewrite HREC0. reflexivity. }
assert (SPA : spZ (ms_regs ms0) = sp0) by (unfold spZ at 1; rewrite X2; reflexivity).
assert (HAS : ANSWER_STK = 16592) by reflexivity.
assert (HFPlow : forall a, inFP (sqc_FP O) a -> a < alloc_ceiling)
  by (intros a Ha; exact (sqc_FP_low ly S W mem md O a HAR HOin Ha)).
assert (HchA : achain ly3 (rdW W3 (ms_mem ms0)) (spZ (ms_regs ms0)) (s0Z (ms_regs ms0)) ch).
{ rewrite SPA. unfold s0Z at 1. rewrite X8. exact (sqc_achain_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HFPlow Hch). }
assert (HPREA : afn_pre SEGS B ANSWER_STK ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) mdv0 ch).
{ apply (afn_pre_at SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms0) ANSWER_STK 0 ch HJ3).
  - rewrite SPA. lia.
  - reflexivity.
  - lia.
  - rewrite HAS. lia.
  - rewrite HAS, HST. lia.
  - rewrite A1. exact Hra.
  - unfold raZ. rewrite A1. exact Hra4.
  - rewrite X3. exact Hgp.
  - rewrite X4. exact Htp.
  - exact HchA. }
pose proof HJ3 as (_ & _ & _ & _ & _ & HfrJ & HnevJ & _).
assert (HRAJ : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms0)))
  by exact (sqc_aro ly S W mem md O ly3 S3 W3 (ms_mem ms0) mdv0 [] _ sp0 HAR HOin HJ3 HROD).
pose proof (proj1 HJc3) as HAR3m.
assert (Hold64 : 0 <= sqc_old QB < 2 ^ 64).
{ unfold sqc_old. destruct (l_answer QB) as [an|] eqn:Ean; [|lia].
  pose proof (HOLDBin an eq_refl) as Han. apply HOQB in Han. pose proof (HIO0 _ Han) as Hc'. destruct an as [a1 a2].
  destruct (sqc_blk_bounds lyc Sc Wc memT mdT a1 a2 HARc Hc') as (Hb0 & Hb1 & _ & _ & Hr1).
  pose proof asan_consts as (CC1 & _). cbn [fst]. lia. }
(* the meter up to the jump *)
assert (M3 : mo_le MT S2 S3 0) by (rewrite ES3; exact (mo_le_refl MT MTL S2)).
assert (MLEJ : mo_le MT S S3 (Z.of_nat (length F) * mo_free MT + XM_XSTRDUP MT x + 0))
  by exact (mle_station MT S S2 S3 _ 0 MTL (mle_station MT S Sc S2 _ _ MTL MLE MLE2) M3).
assert (HXA : 0 <= XM_ANSWER MT (snd (rec_answer (rec_record R0 SQ_FN [x]) (SQ_FN, [x]) (shape_of sqc_verb) true))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (rec_answer (rec_record R0 SQ_FN [x]) (SQ_FN, [x]) (shape_of sqc_verb) true))) + 1) ltac:(lia)).
  lia. }
rewrite (SIGP CS_answer ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_answer) with (BASE + AF_answer).
eapply SRr_mono.
{ apply (TANSWER fx ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) mdv0 ch (sqc_slot R0) q (sqc_old QB) (SQ_FN, [x])
    (shape_of sqc_verb) true (rec_record R0 SQ_FN [x]) ((p, Z.of_nat (length x) + 1) :: O0) HPREA).
  - exact HRM0.
  - rewrite HfrJ. cbn [app]. exact HFR8.
  - exact HRAJ.
  - exact (cmd_ro_ok_of_aro _ _ _ _ _ HARJ HRAJ).
  - rewrite T10, OE by lia. rewrite <- HE. exact E34.
  - clear - Hcb. unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb. lia.
  - rewrite T11, A58. exact Hq10.
  - exact Hq64.
  - rewrite T12. reflexivity.
  - exact HREP1.
  - exact HOLD.
  - exact Hold64.
  - intros _. split.
    + apply (sqc_argA_kept _ _ (rdW W3 mem3)); [exact (HqA _)|]. intros i Hi. apply HRK3.
      exact (sqc_argA_range ly3 S3 W3 mem3 md3 _ q _ HAR3m (HqA []) i Hi).
    + unfold fits. vm_compute. congruence.
  - intros _ _. exact (sqc_answer_slot R0 x).
  - unfold EV_SUP_QUARANTINE_CLEAR, EV_XSTRDUP, EV_REC_SHAPE_OF in *. lia.
  - rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ Hperm3), (bsum_perm _ _ Hperm2), bsum_cons. cbn [snd].
    rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPERM), bsum_app in HLIVE.
    unfold LIVE_SUP_QUARANTINE_CLEAR in HLIVE. rewrite HM in HLIVE. fold x in HLIVE.
    pose proof (sqc_bsum_nonneg ly S W mem md F HAR
      ltac:(intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact Hpn)).
    lia.
  - apply (mok_station MT S S3 _ _ _ MTL HMOK MLEJ HXA).
    unfold XM_SUP_QUARANTINE_CLEAR. rewrite HM. fold x. rewrite <- HFN. lia. }
(* answer returned at some fx1 with its two FP clauses against the entry's fx: sup_quarantine_clear's apost_baseF *)
cbv beta. intros W4 c4 _ (fx1 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hf1 & Hf2 & HJ4 & HP4 & HQ4).
cbv zeta in HQ4.
destruct HQ4 as (p1 & p2 & O' & Hp2 & Hp2a & Hp12 & Hfr12 & Hbl & HrepF & HO' & Hstr & HBB4 & Hmle).
set (t := snd (rec_answer (rec_record R0 SQ_FN [x]) (SQ_FN, [x]) (shape_of sqc_verb) true)) in *.
set (nT := Z.of_nat (length t) + 1) in *.
set (old := sqc_old QB) in *.
pose proof (proj1 HJ4) as HAR4.
(* the old answer's start is no other live block's *)
assert (HOLDs : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> fst pn <> old).
{ intros pn Hpn HnO Hf. unfold old, sqc_old in Hf. destruct (l_answer QB) as [an|] eqn:Ean.
  - pose proof (HOLDBin an eq_refl) as Han. apply HOQB in Han. apply HO0 in Han as [HanO _].
    apply HnO. rewrite (sqc_same_start ly S W mem md pn an HAR Hpn (HOin _ HanO) Hf). exact HanO.
  - destruct pn as [b m]. destruct (sqc_blk_bounds ly S W mem md b m HAR Hpn) as (Hb & _). cbn [fst] in Hf. lia. }
(* a block of the entry is one of the call of xstrdup's, or one rec_calls_free freed (one of O) *)
assert (HSc : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B lyc Sc) \/ In pn F).
{ intros pn Hpn. apply in_app_or. exact (Permutation_in _ HPERM Hpn). }
assert (HFnot : forall pn, In pn F -> ~ In pn (ablocks B lyc Sc)).
{ intros pn HFi HSc'. exact (sqc_dup_false ly S W mem md (ablocks B lyc Sc) F pn HAR HPERM HSc' HFi). }
(* a block live at the entry with the old answer's start is the old answer, one of O *)
assert (HOLDin' : forall pn, In pn (ablocks B ly S) -> fst pn = old -> In pn O).
{ intros pn Hpn Hf. unfold old, sqc_old in Hf. destruct (l_answer QB) as [an|] eqn:Ean.
  - pose proof (HOLDBin an eq_refl) as Han. apply HOQB in Han. apply HO0 in Han as [HanO _].
    rewrite (sqc_same_start ly S W mem md pn an HAR Hpn (HOin _ HanO) Hf). exact HanO.
  - destruct pn as [b m]. destruct (sqc_blk_bounds ly S W mem md b m HAR Hpn) as (Hb & _). cbn [fst] in Hf. lia. }
(* a block live at the entry and still at the jump that is one of answer's two copies is the old answer *)
assert (HnewS' : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly3 S3) -> (pn = (p1, nT) \/ pn = (p2, nT)) ->
  In pn O).
{ intros pn Hpn H3 Heq. destruct (Z.eq_dec (fst pn) old) as [Ho | Ho]; [exact (HOLDin' pn Hpn Ho)|].
  exfalso. destruct (Hfr12 pn H3 Ho) as [N1 N2]. destruct Heq as [Heq | Heq]; [exact (N1 Heq) | exact (N2 Heq)]. }
assert (HxF : forall n, In (p, n) (ablocks B lyc Sc) -> False).
{ intros n Hin. pose proof (sqc_head_apart ly2 S2 W2 mem2 md2 _ _ (p, n) HAR2 Hperm2 Hin) as D. cbn [fst snd] in D.
  destruct (sqc_blk_bounds lyc Sc Wc memT mdT p n HARc Hin) as (_ & _ & _ & _ & Hnr1).
  destruct (sqc_blk_bounds ly2 S2 W2 mem2 md2 p _ HAR2 HPIN2) as (_ & _ & _ & _ & HL1). lia. }
unfold apost_baseF. exists fx1, ly4, S4, regs4, mem4, md4.
split; [rewrite A1; reflexivity|].
split; [exact Hf1|]. split; [exact Hf2|].
split.
{ assert (HJF : ajournal SEGS B SQC_STK sp0 (sqc_FP O) ly S W mem md ([] ++ []) ly4 S4 W4 mem4 md4
    ((k + EV_XSTRDUP + EV_REC_SHAPE_OF) + EV_ANSWER)).
  { eapply ajournal_sub_wide.
    all: try first [exact LAWS | exact Hsegs | exact HJ3 | exact HJ4].
    all: lazymatch goal with
    | |- forall a, inFP _ a -> awr_byte _ _ _ _ _ _ _ _ _ _ a =>
        intros a Ha; eapply sqc_awr_ans; [|exact Ha];
        intros pn Hpn Hf; pose proof (HOLD0 pn Hpn Hf) as H0; split; [exact (proj1 (proj1 (HO0 pn) H0)) | exact (HO1in pn Hpn)]
    | |- forall a, inFP _ a -> _ => intros a _ Ha Hn; exfalso; apply Hn; rewrite SPA, HAS; rewrite HST in Ha; exact Ha
    | |- _ => rewrite ?SPA, ?HAS, ?HST; lia
    end. }
  cbn [app] in HJF. apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJF).
  unfold EV_SUP_QUARANTINE_CLEAR, EV_XSTRDUP, EV_REC_SHAPE_OF. rewrite Hk, HFN. lia. }
split; [exact (aregs_preserved_trans _ _ _ HPA HP4)|].
exists (fst (rec_answer (rec_record R0 SQ_FN [x]) (SQ_FN, [x]) (shape_of sqc_verb) true)), t, p2, O'.
split; [rewrite HM; apply surjective_pairing|].
split; [exact Hp2|]. split; [exact Hp2a|]. split; [exact HrepF|].
split.
{ intros pn Hpn. apply HO' in Hpn as [[Hpn1 _] | ->].
  - destruct Hpn1 as [<- | H0]; [|left; exact (proj1 (proj1 (HO0 pn) H0))].
    destruct (in_dec recb_pair_dec (p, Z.of_nat (length x) + 1) (ablocks B ly S)) as [Hin | Hnin]; [left | right; exact Hnin].
    destruct (HSc _ Hin) as [H | H]; [exfalso; exact (HxF _ H) | exact (HFO _ H)].
  - destruct (in_dec recb_pair_dec (p1, nT) (ablocks B ly S)) as [Hin | Hnin]; [left | right; exact Hnin].
    destruct (HSc _ Hin) as [H | H]; [exact (HnewS' _ Hin (HIN3 _ H) (or_introl eq_refl)) | exact (HFO _ H)]. }
split; [apply Hbl; right; right; reflexivity|].
split.
{ intros pn Hpn HnO Heq. apply HnO. destruct (HSc pn Hpn) as [H | H];
  [exact (HnewS' pn Hpn (HIN3 _ H) (or_intror Heq)) | exact (HFO _ H)]. }
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Hf & Hpn).
  pose proof HrepF as (QF & HQF & HOQF). pose proof (lay_blocks_in _ _ _ _ _ _ HQF pn (proj1 (HOQF pn) Hpn)) as Hpn4.
  pose proof (proj2 (Hbl (p2, nT)) (or_intror (or_intror eq_refl))) as Hq4.
  pose proof (sqc_same_start ly4 S4 W4 mem4 md4 pn (p2, nT) HAR4 Hpn4 Hq4 Hf) as ->.
  apply HO' in Hpn as [[Hpn1 Hfo] | Heq];
  [exact (proj2 (Hfr12 _ (HO1in _ Hpn1) Hfo) eq_refl) | injection Heq as Heq; exact (Hp12 (eq_sym Heq))]. }
split; [exact Hstr|].
split.
{ intros pn Hpn HnO.
  assert (H3 : In pn (ablocks B ly3 S3)).
  { destruct (HSc pn Hpn) as [H | H]; [exact (HIN3 _ H) | exfalso; exact (HnO (HFO _ H))]. }
  assert (H4 : In pn (ablocks B ly4 S4)) by (apply Hbl; left; split; [exact H3 | exact (HOLDs pn Hpn HnO)]).
  split; [exact H4|].
  pose proof (proj2 (Hbl (p2, nT)) (or_intror (or_intror eq_refl))) as Hq4.
  destruct pn as [b m]. cbn [fst snd].
  assert (Hne : (b, m) <> (p2, nT)) by exact (proj2 (Hfr12 (b, m) H3 (HOLDs (b, m) Hpn HnO))).
  destruct (sqc_blk_bounds ly4 S4 W4 mem4 md4 b m HAR4 H4) as (_ & _ & Hm0 & Hmr & _).
  destruct (sqc_blk_bounds ly4 S4 W4 mem4 md4 p2 nT HAR4 Hq4) as (_ & _ & Hn0 & Hnr & _).
  unfold iv_apart. destruct (sqc_blk_apart ly4 S4 W4 mem4 md4 b m p2 nT HAR4 H4 Hq4 Hne); lia. }
split.
{ intros pn Hpn. apply Hbl in Hpn as [[H3 Hf] | [-> | ->]].
  - apply (Permutation_in _ Hperm3), (Permutation_in _ Hperm2) in H3. destruct H3 as [<- | H3].
    + right; left. apply HO'. left. split; [left; unfold LIVE_XSTRDUP; reflexivity | exact Hf].
    + destruct (in_dec recb_pair_dec pn O0) as [H0 | H0n].
      * right; left. apply HO'. left. split; [right; exact H0 | exact Hf].
      * left. split.
        -- apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact H3.
        -- intros HinO. destruct (in_dec recb_pair_dec pn F) as [HFi | HFn]; [exact (HFnot _ HFi H3)|].
           apply H0n. apply HO0. split; [exact HinO | exact HFn].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ assert (BBc : blocks_bytes Sc <= blocks_bytes S).
  { rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPERM), bsum_app.
    pose proof (sqc_bsum_nonneg ly S W mem md F HAR
      ltac:(intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; right; exact Hpn)).
    lia. }
  rewrite ES3 in HBB4. unfold LIVE_SUP_QUARANTINE_CLEAR. rewrite HM. fold x. fold t. lia. }
apply (mle_weaken MT S S4 _ _ MTL (mle_station MT S S3 S4 _ _ MTL MLEJ Hmle)).
unfold XM_SUP_QUARANTINE_CLEAR. rewrite HM. fold x. rewrite <- HFN. unfold t. lia.
Qed.

(* ---------- part 4: from the entry to the call of xstrdup ---------- *)

(* a byte of a live block the recorder does not own lies outside the walk's footprint *)
Lemma sqc_blk_notFP : forall ly S (W : world SEGS) mem md O b m i, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> In (b, m) (ablocks B ly S) -> ~ In (b, m) O ->
0 <= i < req_size m -> ~ inFP (sqc_FP O) (b + i).
Proof.
intros ly S W mem md O b m i HAR HO Hin HnO Hi Hf. destruct (sqc_inFP_cases O (b + i) Hf) as [HP | (b2 & m2 & Hin2 & Ha)].
- exact (sqc_blk_noprog ly S W mem md b m (b + i) HAR Hin ltac:(lia) HP).
- assert (Hne : (b, m) <> (b2, m2)) by (intros E; apply HnO; rewrite E; exact Hin2).
  destruct (sqc_blk_apart ly S W mem md b m b2 m2 HAR Hin (HO _ Hin2) Hne); lia.
Qed.

(* the walk's invariant survives a run that writes only the slot's first 16 bytes *)
Lemma sqc_mid_kept : forall ly S W regs mem md R O lyc Sc Wc mem1 md1 mem2 md2 k lyB SBa WB memB R0 O0 F c,
sqc_mid ly S W regs mem md R O lyc Sc Wc mem1 md1 k lyB SBa WB memB R0 O0 F ->
ajournal SEGS B SQC_STK (spZ regs) (sqc_FP O) ly S W mem md [] lyc Sc Wc mem2 md2 k ->
sqc_slot_ok c ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> rdW Wc mem2 a = rdW Wc mem1 a) ->
sqc_mid ly S W regs mem md R O lyc Sc Wc mem2 md2 k lyB SBa WB memB R0 O0 F.
Proof.
intros ly S W regs mem md R O lyc Sc Wc mem1 md1 mem2 md2 k lyB SBa WB memB R0 O0 F c MID HJ2 Hc KEEP.
destruct MID as (HJ & Hk & HFRM & HREPB & HSP0 & HLEN0 & HREC0 & HKO0 & HIO0 & HPERM & HFO & HO0 & HFN & MLE).
pose proof (proj1 HJ) as HARc.
destruct (sqc_slot_bounds c Hc) as (Hcb & _ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite SQC_STK_val in Hslo. pose proof asan_consts as (C1 & _).
split; [exact HJ2|]. split; [exact Hk|]. split.
{ intros j r Hjr. apply (sqc_val_kept Wc Wc mem1 mem2); [exact (HFRM j r Hjr)|].
  intros kk Hkk. assert (Hj : (j < 6)%nat) by (change 6%nat with (length sqc_saved); apply nth_error_Some; rewrite Hjr; discriminate).
  apply KEEP; unfold SQ_FRAME, A_REC_SPILL in *; lia. }
split; [exact HREPB|]. split; [exact HSP0|]. split; [exact HLEN0|]. split; [exact HREC0|].
split.
{ intros [b m] i Hpn Hi. cbn [fst snd] in *.
  destruct (sqc_blk_bounds lyc Sc Wc mem1 md1 b m HARc (HIO0 _ Hpn)) as (Hb & Hbc & _ & Hmr & _).
  rewrite KEEP; [exact (HKO0 (b, m) i Hpn Hi) | lia |].
  intros Hs. apply (recb_heap_noimg_m B lyc Sc Wc mem1 md1 b m (b + i) HARc (HIO0 _ Hpn)); [lia|].
  apply cmd_prog_img. apply (sqc_in_PG_slot c); [exact Hc | unfold CALL_SIZE; lia]. }
exact (conj HIO0 (conj HPERM (conj HFO (conj HO0 (conj HFN MLE))))).
Qed.

(* the string argument's block is none of the recorder's, so it survives record() and stays live at the call *)
Lemma sqc_arg_at : forall ly S W regs mem md R O lyc Sc Wc mem1 md1 k lyB SBa WB memB R0 O0 F x pw,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
sqc_mid ly S W regs mem md R O lyc Sc Wc mem1 md1 k lyB SBa WB memB R0 O0 F ->
in_blockA (ablocks B ly S) pw (Z.of_nat (length x) + 1) -> astr_atR (rdW W mem) pw x ->
Z.of_nat (length x) + 1 <= LMAX + 1 ->
Forall (fun qk => iv_apart pw (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O ->
astr_argA B lyc Sc (rdW Wc mem1) (in_roP SEGS RLO RHI) [] pw (Some x) /\
atail_vis SEGS Wc mem1 (pw + Z.of_nat (length x)).
Proof.
intros ly S W regs mem md R O lyc Sc Wc mem1 md1 k lyB SBa WB memB R0 O0 F x pw HAR HOin MID Hblk Hxs Hxl Hxap.
destruct MID as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HPERM & HFO & _).
pose proof (proj1 HJ) as HARc.
destruct Hblk as (b & kb & Hin & Hb1 & Hb2).
assert (HnO : ~ In (b, kb) O).
{ intros HO. rewrite Forall_forall in Hxap. pose proof (Hxap _ HO) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart in Hap. lia. }
assert (HinSc : In (b, kb) (ablocks B lyc Sc)).
{ apply (Permutation_in _ HPERM) in Hin. apply in_app_or in Hin as [H | H]; [exact H|].
  exfalso. exact (HnO (HFO _ H)). }
destruct (sqc_blk_bounds ly S W mem md b kb HAR Hin) as (Hb & Hbc & Hk0 & Hkr & _).
split.
- cbn [astr_argA]. split; [lia|]. split.
  + apply (sqc_astr_kept (rdW W mem)); [exact Hxs|]. intros i Hi.
    replace (pw + i) with (b + (pw + i - b)) by lia.
    apply (sqc_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b kb (pw + i - b) HJ Hin HinSc); [lia|].
    apply (sqc_blk_notFP ly S W mem md O b kb (pw + i - b) HAR HOin Hin HnO). lia.
  + split; [exact Hxl|]. left. split; [exists b, kb; split; [exact HinSc | lia] | constructor].
- apply (cmd_heap_tail_vis lyc Sc Wc mem1 md1 b kb (pw + Z.of_nat (length x)) HARc HinSc). lia.
Qed.

(* from the join (0x8b8b8): the checks and stores of c->fn and c->nargs, the argument, the call of xstrdup *)
Lemma sqc_SJ : sqc_SX_spec -> forall ly S W regs mem md ch pw which R O Q lyc Sc Wc (regs1 : bvmap 5 word) mem1 md1 k
  lyB SBa WB memB R0 O0 F,
sqc_pre ly S W regs mem md ch pw which R O ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q -> (forall pn, In pn O <-> In pn (lay_blocks Q)) ->
sqc_mid ly S W regs mem md R O lyc Sc Wc mem1 md1 k lyB SBa WB memB R0 O0 F ->
sqc_recmem (rdW Wc mem1) (rdW WB memB) (sqc_slot R0) 0 ->
sqc_ncalls_ok (rdW Wc mem1) R0 ->
getr regs1 2 = w64 (spZ regs - SQ_FRAME) -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
getr regs1 8 = w64 (sqc_slot R0) -> getr regs1 9 = w64 pw -> getr regs1 19 = w64 SB ->
(forall r, 21 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SQ_JOIN)) mem1 (seg_rom SEGS)) md1)
(apost_baseF SEGS B SQC_STK (sqc_FP O) regs ly S W mem md (EV_SUP_QUARANTINE_CLEAR R) (sqc_Q ly S R O which)).
Proof.
intros HSX ly S W regs mem md ch pw which R O Q lyc Sc Wc regs1 mem1 md1 k lyB SBa WB memB R0 O0 F
  PRE HQ HOQ MID RM0 NC G2 G3 G4 G8 G9 G19 GH.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & HRM0 & HROD & HRO & H10 & Hpw & HARG & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk & HFRM & HREPB & HSP0 & HLEN0 & HREC0 & HKO0 & HIO0 & HPERM & HFO & HO0 & HFN & MLE).
pose proof (proj1 HJ) as HARc.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (lay_blocks_in _ _ _ _ _ _ HQ). apply HOQ. exact Hpn. }
pose proof HARG as (x & Hwh & Hblk & Hxs & Hxl & Hxap).
assert (Hpw0 : pw <> 0).
{ destruct Hblk as (b & kb & Hin & Hb1 & _). destruct (sqc_blk_bounds ly S W mem md b kb HAR Hin) as (Hb & _). lia. }
set (sp0 := spZ regs) in *.
set (c := sqc_slot R0) in *.
assert (HST : SQC_STK = 16592) by reflexivity.
assert (Hn16 : (length (r_calls R0) <= 16)%nat).
{ destruct HREPB as (QB & (_ & _ & _ & (Gl & _) & _) & _). exact Gl. }
assert (Hc : sqc_slot_ok c) by exact (sqc_slot_ok_of R0 Hn16).
destruct (sqc_slot_bounds c Hc) as (Hcb & Hc8 & Hch').
set (nn := Z.of_nat (length (r_calls R0))).
assert (Hnn : 0 <= nn <= 16) by (subst nn; lia).
assert (G2u : bv_unsigned (getr regs1 2) = sp0 - 48) by (rewrite G2; unfold w64; apply unsigned_lit_small; unfold SQ_FRAME; lia).
assert (E34 : ew (sqc_E regs1 regs nn c) 34 = Z_to_bv 64 c) by (rewrite (sqc_E_extra_at regs1 regs nn c 34 ltac:(lia)); reflexivity).
assert (E32 : ew (sqc_E regs1 regs nn c) 32 = Z_to_bv 64 SB) by (rewrite (sqc_E_extra_at regs1 regs nn c 32 ltac:(lia)); reflexivity).
assert (Hcr : 0 <= c < 2 ^ 40) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hcb; lia).
unfold w64 in G8, G19.
destruct (sqc_seed B HB VOBJS cmd_prog_writable SQ_JOIN sqc_regsC [] Wc regs1 regs mem1 lyc Sc md1 nn c HARc)
  as [HS SHOK].
{ rewrite G2u. unfold SQ_FRAME. lia. }
{ rewrite G2u. replace (sp0 - 48) with (sp0 + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
{ exact Hnn. }
{ exact Hc. }
{ sqc_regs_ok E34 E32 G8 G8 G19 G8. }
{ rewrite G2u. exact HFRM. }
{ vm_compute. reflexivity. }
{ constructor. }
set (E := sqc_E regs1 regs nn c) in *.
assert (HEI : img_env VAL A_LIM E) by exact (sqc_E_img regs1 regs nn c).
assert (UC : bv_unsigned (ew E SQ_C) = c) by (unfold SQ_C; rewrite E34; apply unsigned_lit_small; lia).
assert (UC34 : bv_unsigned (ew E 34) = c) by exact UC.
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew E kk = getr regs1 rr)
  by (intros kk rr Hkk; exact (sqc_E_reg regs1 regs nn c kk rr Hkk)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 48) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2u).
(* 0x8b8b8 .. 0x8b8e8: the checks of c->fn and c->nargs, the two stores, then the test of the argument *)
paj_run_tok RUN HS HJ SHOK sqc_Bspan.
{ sqc_awr UC Hc. }
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
psrr_branch_tok RUN BR HS SHOK sqc_Bspan.
all: match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hbr end.
all: assert (U9 : U E (SOff 9 0) = pw) by (apply U_atom; [rewrite (EE 9%nat 9%bv eq_refl), G9; reflexivity | lia]).
all: rewrite branch_ne_U, U9 in Hbr; change (U E (SLit 0)) with 0 in Hbr.
2: { exfalso. apply negb_false_iff, Z.eqb_eq in Hbr. exact (Hpw0 Hbr). }
(* the argument is not NULL: a0 := s1, jal xstrdup *)
paj_run_tok RUN HS HJ SHOK sqc_Bspan.
{ sqc_awr UC Hc. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20.
assert (R1 : getr (ms_regs ms) 1 = w64 (BASE + SQ_RETX)) by (rewrite P1; reflexivity).
assert (R2 : getr (ms_regs ms) 2 = w64 (spZ regs - SQ_FRAME)).
{ rewrite P2; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite (EE 2%nat 2%bv eq_refl); exact G2. }
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ rewrite P3; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite (EE 3%nat 3%bv eq_refl); exact G3. }
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ rewrite P4; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite (EE 4%nat 4%bv eq_refl); exact G4. }
assert (R8 : getr (ms_regs ms) 8 = w64 (sqc_slot R0)).
{ rewrite P8; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E34. }
assert (R18 : getr (ms_regs ms) 18 = w64 (sqc_slot R0 + 4)) by (rewrite P18, UC34; reflexivity).
assert (R19 : getr (ms_regs ms) 19 = w64 SB).
{ rewrite P19; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E32. }
assert (R20 : getr (ms_regs ms) 20 = w64 (SB + (sqc_slot R0 + 4) / 8)).
{ rewrite P20, UC34, E32. rewrite sqc_srl3 by lia. rewrite sqc_alu_add. unfold w64. f_equal. fold c. lia. }
assert (R10 : getr (ms_regs ms) 10 = w64 pw).
{ rewrite P10; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite (EE 9%nat 9%bv eq_refl); exact G9. }
assert (RS7 : forall r, 21 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (GH r Hr).
  assert (H7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct H7 as [-> | H7]); [..| subst r];
  rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
(* the slot's fn and nargs, and every other byte as at the join *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 1 (ss_mem ssx) sqc_frame) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H Wc) msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRgD;
  cbn [ms_mem restrict mkst] in HRgD end.
pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 0 4%N (SLit 11) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VFND.
pose proof (field_of_region_any E _ 34%nat c _ _ _ _ _ 4 4%N (SLit 0) HRgD UC34 ltac:(cbn; tauto) ltac:(cbn; lia)) as VNAD.
change (N.to_nat 4) with 4%nat in VFND, VNAD.
replace (bv_unsigned (sv_denot E (SLit 11)) mod 2 ^ (8 * Z.of_N 4)) with 11 in VFND by (vm_compute; reflexivity).
replace (bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 4)) with 0 in VNAD by (vm_compute; reflexivity).
assert (VFN : aval_mem (rdW Wc (ms_mem ms)) (sqc_slot R0 + CALL_OFF_FN) 4 SQ_FN)
  by exact (aval_mem_view SEGS _ _ _ _ _ VFND).
assert (VNA : aval_mem (rdW Wc (ms_mem ms)) (sqc_slot R0 + CALL_OFF_NARGS) 4 0)
  by exact (aval_mem_view SEGS _ _ _ _ _ VNAD).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 16) -> rdW Wc (ms_mem ms) a = rdW Wc mem1 a).
{ intros a Ha Hn. transitivity (rdW Wc (ms_mem ms0) a).
  - apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) (ms_mem ms0) (ms_mem ms) (fun a => c <= a < c + 16) HFr);
    [|exact Ha | exact Hn].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UC34 in Hrr; lia|]).
    destruct Hin.
  - apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) mem1 (ms_mem ms0) (fun a => c <= a < c + 16) HFr0);
    [|exact Ha | exact Hn].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UC34 in Hrr; lia|]).
    destruct Hin. }
pose proof (sqc_mid_kept ly S W regs mem md R O lyc Sc Wc mem1 md1 (ms_mem ms) _ k lyB SBa WB memB R0 O0 F c MID HJ Hc KEEP)
  as MIDc.
assert (RM16 : sqc_recmem (rdW Wc (ms_mem ms)) (rdW WB memB) (sqc_slot R0) 16).
{ intros a Ha Hnc Hns. rewrite KEEP; [apply RM0; [exact Ha | exact Hnc | lia] | | exact Hns].
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia. }
assert (NC16 : sqc_ncalls_ok (rdW Wc (ms_mem ms)) R0).
{ apply (sqc_aval_kept (rdW Wc mem1)); [exact NC|]. intros kk Hkk. apply KEEP;
  unfold A_G_REC, OFF_NCALLS, OFF_CALLS in *; lia. }
destruct (sqc_arg_at ly S W regs mem md R O lyc Sc Wc (ms_mem ms) _ k lyB SBa WB memB R0 O0 F x pw HAR HOin MIDc
  Hblk Hxs Hxl Hxap) as [HSTR HTAIL].
rewrite Hwh in PRE |- *.
exact (HSX ly S W regs mem md ch pw (Some x) R O Q lyc Sc Wc (ms_mem ms) _ k lyB SBa WB memB R0 O0 F (ms_regs ms) pw
  PRE HQ HOQ MIDc RM16 NC16 VFN VNA R1 R2 R3 R4 R8 R18 R19 R20 R10 RS7 HSTR HTAIL).
Qed.


Lemma sqc_aval_eq : forall (rd rd' : reader) a n v, aval_mem rd a n v -> aval_mem rd' a n v ->
forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k).
Proof. intros rd rd' a n v H H' k Hk. rewrite (H k Hk), (H' k Hk). reflexivity. Qed.

Lemma sqc_nodup_app_r : forall {X : Type} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros X l1. induction l1 as [|x l1 IH]; intros l2 H; [exact H|].
cbn in H. apply List.NoDup_cons_iff in H as [_ H]. exact (IH l2 H).
Qed.

Ltac sqc_fr_val3 OLD3 EE r :=
  cbn [sv_denot]; rewrite (OLD3 r) by lia; rewrite (EE r (Z_to_bv 5 (Z.of_nat r)) eq_refl), Z.add_0_r; reflexivity.

(* the slot record() picks in g_rec's table, as the listing computes it (0x8b8a4 .. 0x8b8b4) *)
Lemma sqc_slot_word : forall n, 0 <= n < 16 ->
alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 n) (Z_to_bv 64 56)) (Z_to_bv 64 16)) (Z_to_bv 64 A_G_REC) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros n Hn.
assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15) by lia.
repeat (destruct Hc as [-> | Hc]); [..| subst n]; apply bv_eq; vm_compute; reflexivity.
Qed.

(* the value a register held at the entry, as the frame stores it *)
Ltac sqc_fr_val EE r :=
  cbn [sv_denot]; rewrite (EE r (Z_to_bv 5 (Z.of_nat r)) eq_refl), Z.add_0_r; reflexivity.
Ltac sqc_fr_rng regs r :=
  let Hb := fresh "Hrng" in
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hb; change (bv_modulus 64) with (2 ^ 64) in Hb;
  cbn; lia.

(* the entry (0x8b844): the frame, the shadow base, g_rec.ncalls, the test of a full table *)
Lemma sqc_SA : sqc_SX_spec -> tsqc_spec_g.
Proof.
intros HSX ly S W regs mem md ch pw which R O PRE.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & HRM0 & HROD & HRO & H10 & Hpw & HARG & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HST : SQC_STK = 16592) by reflexivity.
set (sp0 := spZ regs) in *.
pose proof HREP as (Q & HQ & HOQ).
pose proof HQ as (_ & _ & _ & (HC1 & HC2 & HNC & HC4 & HC5 & HC6) & _).
set (nn := Z.of_nat (length (r_calls R))) in *.
assert (Hnn : 0 <= nn <= 16) by (subst nn; lia).
set (c := sqc_slot R).
assert (Hc : sqc_slot_ok c) by exact (sqc_slot_ok_of R HC1).
assert (HNCv : val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + OFF_NCALLS) 4 nn) by exact (val_mem_view SEGS _ _ _ _ _ HNC).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (fold sp0; rewrite HST in Hslo; lia).
assert (Hp48 : forall a, spZ regs - SQ_FRAME <= a < spZ regs -> apresent (w_H W) mem a)
  by (intros a Ha; apply Hpres; fold sp0 in Ha |- *; rewrite HST; unfold SQ_FRAME in Ha; lia).
pose proof (sqc_seed_entry B TL VOBJS cmd_prog_writable W regs mem ly S md nn c HAR Hsp Hal16 Hp48 Hnn Hc HNCv) as HS.
assert (SHOK : sh_ok SEGS sqc_Bx [] (sqc_E regs regs nn c) (mrestrict (w_H W) mem)) by (unfold sh_ok; constructor).
pose proof (ajournal_init SEGS B SQC_STK (sqc_FP O) ly S W regs mem md ch HPRE) as HJ.
assert (E34 : ew (sqc_E regs regs nn c) 34 = Z_to_bv 64 c) by (rewrite (sqc_E_extra_at regs regs nn c 34 ltac:(lia)); reflexivity).
assert (E33 : ew (sqc_E regs regs nn c) 33 = Z_to_bv 64 nn) by (rewrite (sqc_E_extra_at regs regs nn c 33 ltac:(lia)); reflexivity).
assert (E32 : ew (sqc_E regs regs nn c) 32 = Z_to_bv 64 SB) by (rewrite (sqc_E_extra_at regs regs nn c 32 ltac:(lia)); reflexivity).
set (E := sqc_E regs regs nn c) in *.
assert (HEI : img_env VAL A_LIM E) by exact (sqc_E_img regs regs nn c).
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew E kk = getr regs rr)
  by (intros kk rr Hkk; exact (sqc_E_reg regs regs nn c kk rr Hkk)).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U44 : bv_unsigned (ew E SQ_GREC) = A_G_REC)
  by (pose proof (sqc_E_grec VOBJS regs regs nn c) as Hg; change (ew E SQ_GREC = Z_to_bv 64 A_G_REC) in Hg;
      rewrite Hg; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (U33 : U E (SOff 33 0) = nn) by (apply U_atom; [exact E33 | lia]).
unfold cfg_at.
(* 0x8b844 .. 0x8b880: the frame, the shadow base, g_rec.ncalls, then the test of a full table *)
paj_run_tok RUN HS HJ SHOK sqc_Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite HST; lia | cbn; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := SQ_GREC); [reflexivity | exact U44 | | apply (awr_ok_nil SEGS B)].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold OFF_NCALLS in Ha.
  assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold A_G_REC, REC_SIZE in *; lia).
  right; right; right; right; left.
  split; [|split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)]].
  unfold sqc_FP. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia. }
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
psrr_branch_tok RUN BR HS SHOK sqc_Bspan.
all: match goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hbr end.
all: rewrite branch_ne_U, U33 in Hbr; change (U E (SLit 16)) with 16 in Hbr.
- (* g_rec.ncalls <> 16: the slot arm, 0x8b89c .. 0x8b8b4 *)
  apply negb_true_iff, Z.eqb_neq in Hbr.
  assert (Hn16 : (length (r_calls R) < 16)%nat) by (subst nn; lia).
  paj_run_to_tok RUNTO HS HJ SHOK sqc_Bspan SQ_JOIN.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite HST; lia | cbn; lia |].
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := SQ_GREC); [reflexivity | exact U44 | | apply (awr_ok_nil SEGS B)].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold OFF_NCALLS in Ha.
    assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold A_G_REC, REC_SIZE in *; lia).
    right; right; right; right; left.
    split; [|split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)]].
    unfold sqc_FP. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
  assert (E285 : ew E 285 = Z_to_bv 64 A_G_REC).
  { pose proof (sqc_E_grec VOBJS regs regs nn c) as Hg. exact Hg. }
  assert (U285 : bv_unsigned (ew E 285) = A_G_REC) by exact U44.
  assert (G2 : getr (ms_regs ms) 2 = w64 (spZ regs - SQ_FRAME)) by (rewrite P2, Usp; unfold w64, SQ_FRAME; f_equal; lia).
  assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Hgp).
  assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Htp).
  assert (G8 : getr (ms_regs ms) 8 = w64 (sqc_slot R)).
  { rewrite P8, E33, E285. unfold sqc_slot. rewrite (proj2 (Nat.ltb_lt _ _) Hn16). apply sqc_slot_word. subst nn; lia. }
  assert (G9 : getr (ms_regs ms) 9 = w64 pw) by (rewrite P9, (EE 10%nat 10%bv eq_refl); exact H10).
  assert (G19 : getr (ms_regs ms) 19 = w64 SB) by (rewrite P19; exact E32).
  assert (GH : forall r, 21 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr.
    assert (H7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct H7 as [-> | H7]); [..| subst r];
    rewrite (st_ok_restrict_reg SEGS (w_H W) E _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
  pose proof HS as HSt. unfold st_ok_pi, abs_ss in HSt.
  lazymatch type of HSt with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) sqc_frame) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) sqc_frame) in
    pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 0 r0 HSt ltac:(vm_compute; reflexivity)) as HR0;
    pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 3 r3 HSt ltac:(vm_compute; reflexivity)) as HR3;
    cbn [ms_mem restrict mkst] in HR0, HR3 end.
  assert (HFRm : sqc_frame_at (mrestrict (w_H W) (ms_mem ms)) (spZ regs - SQ_FRAME) regs).
  { intros j r Hjr.
    unfold sqc_saved in Hjr. destruct j as [|[|[|[|[|[|j]]]]]]; cbn in Hjr; try (destruct j; discriminate); injection Hjr as <-.
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 0) with (sp0 + -8) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-8) 8 (SOff 1 0) _ HR0 Usp ltac:(cbn; tauto));
      [sqc_fr_val EE 1%nat | sqc_fr_rng regs 1 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 1) with (sp0 + -16) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-16) 8 (SOff 8 0) _ HR0 Usp ltac:(cbn; tauto));
      [sqc_fr_val EE 8%nat | sqc_fr_rng regs 8 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 2) with (sp0 + -24) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-24) 8 (SOff 9 0) _ HR0 Usp ltac:(cbn; tauto));
      [sqc_fr_val EE 9%nat | sqc_fr_rng regs 9 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 3) with (sp0 + -32) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-32) 8 (SOff 18 0) _ HR0 Usp ltac:(cbn; tauto));
      [sqc_fr_val EE 18%nat | sqc_fr_rng regs 18 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 4) with (sp0 + -40) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-40) 8 (SOff 19 0) _ HR0 Usp ltac:(cbn; tauto));
      [sqc_fr_val EE 19%nat | sqc_fr_rng regs 19 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 5) with (sp0 + -48) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-48) 8 (SOff 20 0) _ HR0 Usp ltac:(cbn; tauto));
      [sqc_fr_val EE 20%nat | sqc_fr_rng regs 20 | cbn; lia]. }
  assert (HNC1 : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 (nn + 1)).
  { apply (aval_mem_view SEGS). unfold OFF_NCALLS.
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) (nn + 1) HR3 U285 ltac:(cbn; tauto));
    [cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia]. }
  assert (KEEPJ : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> ~ (A_G_REC + 8 <= a < A_G_REC + 12) ->
     rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1 H2. transitivity (rdW W (ms_mem ms0) a).
    - apply (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms0) (ms_mem ms)
        (fun a => (sp0 - 48 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr); [|exact Ha | tauto].
      intros b wlo whi a' Hin Hrr. vm_compute in Hin.
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]).
      destruct Hin.
    - apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms0)
        (fun a => (sp0 - 48 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr0); [|exact Ha | tauto].
      intros b wlo whi a' Hin Hrr. vm_compute in Hin.
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]).
      destruct Hin. }
  assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
  { intros pn Hpn. apply (lay_blocks_in _ _ _ _ _ _ HQ). apply HOQ. exact Hpn. }
  rewrite HST in Hslo.
  refine (sqc_SJ HSX ly S W regs mem md ch pw which R O Q ly S W (ms_regs ms) (ms_mem ms) _ 0 ly S W mem R O []
    PRE HQ HOQ _ _ _ G2 G3 G4 G8 G9 G19 GH).
  + split; [exact HJ|]. split; [reflexivity|]. split; [exact HFRm|]. split; [exact HREP|].
    split; [intros Hl; lia|]. split; [reflexivity|]. split; [intros A; reflexivity|].
    split.
    { intros [b m] i Hpn Hi. cbn [fst snd] in *.
      destruct (sqc_blk_bounds ly S W mem md b m HAR (HOin _ Hpn)) as (Hb & Hbc & _ & Hmr & _).
      apply KEEPJ; [lia | lia |].
      intros Hg. apply (sqc_blk_noprog ly S W mem md b m (b + i) HAR (HOin _ Hpn)); [lia|].
      apply recb_grec_in. unfold A_G_REC, REC_SIZE in *. lia. }
    split; [exact HOin|]. split; [rewrite app_nil_r; reflexivity|]. split; [intros pn []|].
    split; [intros pn; split; [intros H; split; [exact H | intros []] | intros [H _]; exact H]|].
    split; [unfold rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ _) Hn16); reflexivity|].
    cbn [length Z.of_nat]. rewrite Z.mul_0_l. exact (mo_le_refl MT MTL S).
  + intros a Ha Hnc _. apply KEEPJ; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia | | exact Hnc].
    unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
  + unfold sqc_ncalls_ok, rec_record. rewrite (proj2 (Nat.ltb_lt _ _) Hn16). cbn [r_calls set_calls].
    rewrite length_app. cbn [length]. replace (Z.of_nat (length (r_calls R) + 1)) with (nn + 1) by (subst nn; lia).
    exact HNC1.
- (* g_rec.ncalls = 16: the spill arm, 0x8b884 .. 0x8b894 *)
  apply negb_false_iff, Z.eqb_eq in Hbr.
  paj_run_tok RUN HS HJ SHOK sqc_Bspan.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite HST; lia | cbn; lia |].
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := SQ_GREC); [reflexivity | exact U44 | | apply (awr_ok_nil SEGS B)].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold OFF_NCALLS in Ha.
    assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold A_G_REC, REC_SIZE in *; lia).
    right; right; right; right; left.
    split; [|split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)]].
    unfold sqc_FP. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia. }
  pmkst HS.
  assert (HL : length (r_calls R) = 16%nat) by (subst nn; lia).
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  assert (U285 : bv_unsigned (ew E 285) = A_G_REC) by exact U44.
  assert (E292 : forall E', img_env VAL A_LIM E' -> ew E' 292 = Z_to_bv 64 A_REC_SPILL).
  { intros E' HE'. apply bv_eq. change 292%nat with (A_OBJ 51).
    rewrite (HE' (A_OBJ 51) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), (sqc_spill_val VOBJS : VAL (A_OBJ 51) = A_REC_SPILL).
    rewrite unsigned_lit_small; unfold A_REC_SPILL; lia. }
  assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)).
  { intros pn Hpn. apply (lay_blocks_in _ _ _ _ _ _ HQ). apply HOQ. exact Hpn. }
  (* g_rec.ncalls at the call: still 16 *)
  pose proof HS as HSt. unfold st_ok_pi, abs_ss in HSt.
  lazymatch type of HSt with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) sqc_frame) in
    pose proof (st_ok_region_nth E ssx (restrict (w_H W) msx) 3 r3 HSt ltac:(vm_compute; reflexivity)) as HR3;
    cbn [ms_mem restrict mkst] in HR3 end.
  assert (HNCc : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 nn).
  { apply (aval_mem_view SEGS). unfold OFF_NCALLS.
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 0) nn HR3 U285 ltac:(cbn; tauto));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
  (* the two runs write only the frame: g_rec.ncalls keeps its value *)
  assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1.
    destruct (Z_lt_le_dec a (A_G_REC + 8)) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec a (A_G_REC + 12)) as [Hhi|Hhi]].
    2: { replace a with (A_G_REC + OFF_NCALLS + Z.of_nat (Z.to_nat (a - (A_G_REC + 8)))) by (unfold OFF_NCALLS; lia).
         exact (sqc_aval_eq _ _ _ _ _ HNC HNCc (Z.to_nat (a - (A_G_REC + 8))) ltac:(lia)). }
    all: transitivity (rdW W (ms_mem ms0) a).
    all: try (apply (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms0) (ms_mem ms)
           (fun a => (sp0 - 48 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr); [|exact Ha | lia];
         intros b wlo whi a' Hin Hrr; vm_compute in Hin;
         repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]);
         destruct Hin).
    all: apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms0)
           (fun a => (sp0 - 48 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr0); [|exact Ha | lia];
         intros b wlo whi a' Hin Hrr; vm_compute in Hin;
         repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]);
         destruct Hin. }
  rewrite HST in Hslo.
  assert (HAc : arep_at (ablocks B ly S) (rdW W (ms_mem ms)) A_G_REC A_REC_SPILL R Q).
  { apply (sqc_arep_at_ext _ _ (rdW W mem) _ _ _ R Q HQ).
    - intros pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HQ pn Hpn).
    - intros a [Ha | [Ha | ([pb pm] & Hpn & Ha)]].
      + apply KEEPC; unfold A_G_REC, REC_SIZE in *; lia.
      + apply KEEPC; unfold A_REC_SPILL, SC_SIZE in *; lia.
      + cbn [fst snd] in Ha. pose proof (lay_blocks_in _ _ _ _ _ _ HQ (pb, pm) Hpn) as Hin.
        destruct (sqc_blk_bounds ly S W mem md pb pm HAR Hin) as (Hb & Hbc & _ & Hmr & _). apply KEEPC; lia. }
  pose proof HAc as (_ & _ & _ & (_ & _ & _ & _ & HC5c & _) & _ & _ & _ & (HNDq & _)).
  pose proof HC5c as (_ & G6 & GL & _ & GN & GNd & G7).
  (* rec_calls_free(&record.spill, 1) *)
  assert (FR : REC_CALLS_FREE_STK = 16496) by (vm_compute; reflexivity).
  assert (HspT : spZ (ms_regs ms) = sp0 + -48) by (unfold spZ at 1; rewrite P2, Usp, unsigned_lit_small by lia; lia).
  assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Hgp).
  assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Htp).
  assert (P10' : getr (ms_regs ms) 10 = w64 A_REC_SPILL) by (rewrite P10; exact (E292 E HEI)).
  assert (P11' : getr (ms_regs ms) 11 = w64 (Z.of_nat (length [l_spill Q]))) by (rewrite P11; reflexivity).
  assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
  assert (Hch1 : achain ly (rdW W (ms_mem ms)) (sp0 + -48) (s0Z (ms_regs ms)) []).
  { left. split; [|reflexivity]. left. unfold s0Z. rewrite P8, (E292 E HEI), unsigned_lit_small by (unfold A_REC_SPILL; lia).
    unfold A_REC_SPILL. lia. }
  assert (RSF : rec_spill_frees R = Z.of_nat (length (l_spill Q))).
  { unfold rec_spill_frees. rewrite HL. cbn [Nat.ltb Nat.leb]. rewrite GL. reflexivity. }
  assert (EVC : EV_REC_CALLS_FREE [l_spill Q] = Z.of_nat (length (l_spill Q)))
    by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; reflexivity).
  assert (XMC : XM_REC_CALLS_FREE MT [l_spill Q] = rec_spill_frees R * mo_free MT)
    by (unfold XM_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r, RSF; reflexivity).
  assert (XX0 : 0 <= XM_XSTRDUP MT (sarg which)) by (unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
  assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
  { intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
  assert (HEc : st_nev S + EV_REC_CALLS_FREE [l_spill Q] <= EV_MAX).
  { rewrite EVC, <- RSF. unfold EV_SUP_QUARANTINE_CLEAR, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia. }
  assert (HMOKc : mo_ok MT S (XM_REC_CALLS_FREE MT [l_spill Q])).
  { rewrite XMC. apply (mo_ok_le MT MTL S _ _ HMOK). unfold XM_SUP_QUARANTINE_CLEAR.
    pose proof (XN0 (snd (sup_quarantine_clear_m R which))). lia. }
  assert (HHOME : rcf_home B ly S W (ms_mem ms) A_REC_SPILL (CALL_SIZE * Z.of_nat (length [l_spill Q]))).
  { unfold rcf_home. right; left. cbn [length Z.of_nat]. unfold CALL_SIZE, SC_SIZE. lia. }
  assert (HENT : forall i P, nth_error [l_spill Q] i = Some P ->
     (length P <= 6)%nat /\ aval_mem (rdW W (ms_mem ms)) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
     forall a pn, nth_error P a = Some pn ->
       aval_mem (rdW W (ms_mem ms)) (A_REC_SPILL + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
       In pn (ablocks B ly S)).
  { intros i P Hi. destruct i as [|i]; [|destruct i; discriminate]. cbn in Hi. injection Hi as <-.
    cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r.
    split; [rewrite GL; exact G6|]. split; [rewrite GL; exact GN|].
    intros a pn Hpn.
    destruct (nth_error (snd (r_spill R)) a) as [s'|] eqn:Hs.
    - destruct (G7 a s' pn Hs Hpn) as (V1 & _ & V3 & _). split; [exact V1 | exact V3].
    - exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) a) ltac:(rewrite Hpn; discriminate)). lia. }
  assert (HND : NoDup (map fst (concat [l_spill Q]))) by (cbn [concat]; rewrite app_nil_r; exact GNd).
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms)))
    by exact (sqc_aro ly S W mem md O ly S W (ms_mem ms) _ [] 0 sp0 HAR HOin HJ HROD).
  assert (HspillO : forall pn, In pn (l_spill Q) -> In pn O)
    by (intros pn Hpn; apply HOQ; unfold lay_blocks; apply in_app_iff; right; apply in_app_iff; left; exact Hpn).
  assert (HFP1 : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a ->
     (A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) \/
     (exists b m, In (b, m) (l_spill Q) /\ b <= a < b + req_size m)).
  { intros a Ha. unfold rcf_fp in Ha. cbn [length seq map app] in Ha. apply inFP_cons in Ha as [Ha | Ha].
    - left. cbn [Z.of_nat] in Ha. lia.
    - right. destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba). cbn [concat] in Hbm. rewrite app_nil_r in Hbm.
      exists b, m. split; [exact Hbm | exact Hba]. }
  assert (HFP1s : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a -> a < sp0 - SQC_STK).
  { intros a Ha. rewrite HST. destruct (HFP1 a Ha) as [Ha' | (b & m & Hbm & Hba)]; [unfold A_REC_SPILL, CALL_OFF_NARGS in Ha'; lia|].
    destruct (sqc_blk_bounds ly S W mem md b m HAR (HOin _ (HspillO _ Hbm))) as (_ & Hbc & _). lia. }
  rewrite (SIGP CS_rec_calls_free ltac:(vm_compute; tauto)).
  change (pa_val A_TEXT + cmd_af CS_rec_calls_free) with (BASE + AF_rec_calls_free).
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ SQC_STK sp0 (sqc_FP O) ly S W mem md [] ly S _ 0
      REC_CALLS_FREE_STK _ (EV_REC_CALLS_FREE [l_spill Q]) (-48) (getr (ms_regs ms) 1) [] _ HJ HspT eq_refl ltac:(lia)
      ltac:(rewrite FR; lia) ltac:(rewrite FR, HST; lia) P3' P4' eq_refl HraT Hra4T Hch1).
    - intros HPRE1. exact (TRCF fx ly S W (ms_regs ms) (ms_mem ms) _ [] A_REC_SPILL [l_spill Q] HPRE1 HRODc P10' P11'
        ltac:(cbn; lia) HHOME ltac:(unfold A_REC_SPILL; reflexivity) HENT HND HEc HMOKc).
    - intros a Ha. destruct (HFP1 a Ha) as [Ha' | (b & m & Hbm & Hba)].
      + right; right; right; right; left.
        assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_spill_in; unfold A_REC_SPILL, SC_SIZE, CALL_OFF_NARGS in *; lia).
        split; [|split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)]].
        unfold sqc_FP. apply inFP_cons. right. apply inFP_cons. left. unfold A_REC_SPILL, SC_SIZE, CALL_OFF_NARGS in *. lia.
      + right; left. split.
        * unfold sqc_FP. apply inFP_cons. right. apply inFP_cons. right.
          replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b m (a - b)); [exact (HspillO _ Hbm) | lia].
        * exists b, m. split; [exact (HOin _ (HspillO _ Hbm)) | exact Hba].
    - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. pose proof (HFP1s a Ha). lia. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
  destruct HK2 as (HPermF & _ & _ & _ & _ & HRspill & _ & _ & MLEF).
  rewrite P1.
  (* back at 0x8b898 *)
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    eapply (region_kept_stack_sub SEGS B);
    [exact HJc2 | exact HJ2 | exact Usp | cbn; lia | rewrite HST; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. pose proof (HFP1s a HFa). rewrite HST in *. cbn in Ha. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HS.
  assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD3 : forall m, (m < 48)%nat -> ew E3 m = ew E m) by (intros m Hm; rewrite HE3; apply YN3v.ew_havoc_old; exact Hm).
  clear HE3.
  assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by lia; exact Usp).
  assert (SHOK3 : sh_ok SEGS sqc_Bx [] E3 (mrestrict (w_H W2) mem2)) by (unfold sh_ok; constructor).
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  (* 0x8b898: j 0x8b8b8 *)
  paj_run_to_tok RUNTO HS HJ2 SHOK3 sqc_Bspan SQ_JOIN.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp3 | cbn; rewrite HST; lia | cbn; lia |].
    apply (awr_ok_nil SEGS B). }
  pmkst HS.
  pose proof (proj1 HJ2) as HAR2.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19.
  assert (G2 : getr (ms_regs ms) 2 = w64 (spZ regs - SQ_FRAME)) by (rewrite Q2, Usp3; unfold w64, SQ_FRAME; f_equal; lia).
  assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
  { rewrite Q3. rewrite (OLD3 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp. }
  assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
  { rewrite Q4. rewrite (OLD3 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp. }
  set (R0 := set_spill R (fst (r_spill R), [])).
  assert (G8 : getr (ms_regs ms) 8 = w64 (sqc_slot R0)).
  { rewrite Q8, (E292 E3 HEI3). unfold sqc_slot, R0. cbn [set_spill r_calls]. rewrite HL. reflexivity. }
  assert (G9 : getr (ms_regs ms) 9 = w64 pw).
  { rewrite Q9. rewrite (OLD3 10%nat) by lia. rewrite (EE 10%nat 10%bv eq_refl). exact H10. }
  assert (G19 : getr (ms_regs ms) 19 = w64 SB) by (rewrite Q19; rewrite (OLD3 32%nat) by lia; exact E32).
  assert (GH : forall r, 21 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr.
    assert (H7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct H7 as [-> | H7]); [..| subst r];
    rewrite (st_ok_restrict_reg SEGS (w_H W2) E3 _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => rewrite (OLD3 m) by lia; exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
  pose proof HS as HSt2. unfold st_ok_pi, abs_ss in HSt2.
  lazymatch type of HSt2 with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) sqc_frame) in
    pose proof (st_ok_region_nth E3 ssx (restrict (w_H W2) msx) 0 r0 HSt2 ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict mkst] in HR0 end.
  assert (HFRm : sqc_frame_at (mrestrict (w_H W2) (ms_mem ms)) (spZ regs - SQ_FRAME) regs).
  { intros j r Hjr.
    unfold sqc_saved in Hjr. destruct j as [|[|[|[|[|[|j]]]]]]; cbn in Hjr; try (destruct j; discriminate); injection Hjr as <-.
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 0) with (sp0 + -8) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-8) 8 (SOff 1 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [sqc_fr_val3 OLD3 EE 1%nat | sqc_fr_rng regs 1 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 1) with (sp0 + -16) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-16) 8 (SOff 8 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [sqc_fr_val3 OLD3 EE 8%nat | sqc_fr_rng regs 8 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 2) with (sp0 + -24) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-24) 8 (SOff 9 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [sqc_fr_val3 OLD3 EE 9%nat | sqc_fr_rng regs 9 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 3) with (sp0 + -32) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-32) 8 (SOff 18 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [sqc_fr_val3 OLD3 EE 18%nat | sqc_fr_rng regs 18 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 4) with (sp0 + -40) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-40) 8 (SOff 19 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [sqc_fr_val3 OLD3 EE 19%nat | sqc_fr_rng regs 19 | cbn; lia].
    - replace (spZ regs - SQ_FRAME + 40 - 8 * Z.of_nat 5) with (sp0 + -48) by (unfold SQ_FRAME; cbn; lia).
      apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-48) 8 (SOff 20 0) _ HR0 Usp3 ltac:(cbn; tauto));
      [sqc_fr_val3 OLD3 EE 20%nat | sqc_fr_rng regs 20 | cbn; lia]. }
  (* the jump writes nothing outside the frame *)
  assert (KEEPJ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
  { intros a Ha H1.
    apply (kept_of_frame (segs := SEGS) E3 _ (w_H W2) mem2 (ms_mem ms) (fun a => sp0 - 48 <= a < sp0) HFr); [|exact Ha | exact H1].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]).
    destruct Hin. }
  set (O1 := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
  pose proof (HRspill R Q HAc eq_refl eq_refl) as HRF.
  pose proof (proj1 HJc2) as HAR2c.
  assert (HRJ : rec_repA B ly2 S2 (rdW W2 (ms_mem ms)) R0 O1).
  { apply (sqc_rec_repA_ext B ly2 S2 (rdW W2 mem2) ly2 S2 _ _ O1 HRF).
    - intros pn Hpn. destruct HRF as (QF & HQF & HOQF). exact (lay_blocks_in _ _ _ _ _ _ HQF pn (proj1 (HOQF pn) Hpn)).
    - intros a [Ha | [Ha | ([pb pm] & Hpn & Ha)]].
      + apply KEEPJ2; unfold A_G_REC, REC_SIZE in *; lia.
      + apply KEEPJ2; unfold A_REC_SPILL, SC_SIZE in *; lia.
      + cbn [fst snd] in Ha. destruct HRF as (QF & HQF & HOQF).
        pose proof (lay_blocks_in _ _ _ _ _ _ HQF (pb, pm) (proj1 (HOQF _) Hpn)) as Hin.
        destruct (sqc_blk_bounds ly2 S2 W2 mem2 md2 pb pm HAR2c Hin) as (Hb & Hbc & _ & Hmr & _). apply KEEPJ2; lia. }
  apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HNDq.
  pose proof HNDq as NDq'. unfold lay_blocks in NDq'. rewrite !map_app in NDq'.
  assert (JB2 : forall pn, In pn O1 <-> In pn O /\ ~ In pn (l_spill Q)).
  { intros pn. rewrite (HOQ pn). subst O1. unfold lay_blocks. rewrite !in_app_iff. split.
    - intros H. split; [tauto|]. intros Hs. destruct H as [Hcl | Har].
      + exact (list_nodup_app_disj _ _ (fst pn) NDq' (in_map fst _ _ Hcl) (in_or_app _ _ _ (or_introl (in_map fst _ _ Hs)))).
      + pose proof (sqc_nodup_app_r _ _ NDq') as NDr.
        apply (list_nodup_app_disj _ _ (fst pn) NDr (in_map fst _ _ Hs)).
        destruct Har as [Ha | Hr]; apply in_or_app; [left | right]; apply in_map; assumption.
    - intros [H Hs]. tauto. }
  assert (FPpos : Forall (fun r => 0 < fst r) (rcf_fp A_REC_SPILL [l_spill Q])).
  { unfold rcf_fp. apply Forall_app. split.
    - cbn. constructor; [cbn; unfold A_REC_SPILL, CALL_OFF_NARGS; lia | constructor].
    - unfold ablocks_fp. rewrite Forall_map. apply Forall_forall. intros [b m] Hbm. cbn [concat] in Hbm. rewrite app_nil_r in Hbm.
      destruct (sqc_blk_bounds ly S W mem md b m HAR (HOin _ (HspillO _ Hbm))) as (Hb & _). cbn. lia. }
  assert (NC2 : aval_mem (rdW W2 mem2) (A_G_REC + OFF_NCALLS) 4 nn).
  { apply (sqc_aval_kept (rdW W (ms_mem ms1))); [exact HNCc|]. intros kk Hkk.
    assert (HPG : Exists (in_zr (A_G_REC + OFF_NCALLS + Z.of_nat kk)) recb_PG)
      by (apply recb_grec_in; unfold A_G_REC, OFF_NCALLS, REC_SIZE; lia).
    apply (sqc_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A_G_REC + OFF_NCALLS + Z.of_nat kk) HJc2 FPpos); [|exact HPG].
    intros Hf. destruct (HFP1 _ Hf) as [Ha' | (b & m & Hbm & Hba)]; [unfold A_REC_SPILL, A_G_REC, OFF_NCALLS, CALL_OFF_NARGS in *; lia|].
    exact (sqc_blk_noprog ly S W mem md b m _ HAR (HOin _ (HspillO _ Hbm)) Hba HPG). }
  refine (sqc_SJ HSX ly S W regs mem md ch pw which R O Q ly2 S2 W2 (ms_regs ms) (ms_mem ms) _
    (0 + EV_REC_CALLS_FREE [l_spill Q]) ly2 S2 W2 (ms_mem ms) R0 O1 (l_spill Q) PRE HQ HOQ _ _ _ G2 G3 G4 G8 G9 G19 GH).
  + split; [exact HJ2|]. split; [rewrite EVC; lia|]. split; [exact HFRm|]. split; [exact HRJ|].
    split; [intros _; reflexivity|]. split; [reflexivity|].
    split; [intros A; exact (sqc_rec_record_set_spill R _ SQ_FN A HL)|].
    split; [intros; reflexivity|].
    split; [intros pn Hpn; destruct HRJ as (QJ & HQJ & HOQJ); exact (lay_blocks_in _ _ _ _ _ _ HQJ pn (proj1 (HOQJ pn) Hpn))|].
    split; [cbn [concat] in HPermF; rewrite app_nil_r in HPermF; exact HPermF|].
    split; [exact HspillO|]. split; [exact JB2|]. split; [symmetry; exact RSF|].
    rewrite <- RSF, <- XMC. exact MLEF.
  + intros a _ _ _. reflexivity.
  + unfold sqc_ncalls_ok. apply (sqc_aval_kept (rdW W2 mem2)).
    * replace (Z.of_nat (length (r_calls (rec_record R0 SQ_FN [[]])))) with nn; [exact NC2|].
      subst nn. unfold rec_record, R0. cbn [set_spill r_calls]. rewrite HL. cbn [Nat.ltb Nat.leb set_spill r_calls].
      rewrite ?HL. reflexivity.
    * intros kk Hkk. apply KEEPJ2; unfold A_G_REC, OFF_NCALLS in *; lia.
Qed.

(* the statement, from the two parts of the walk *)
Theorem sqc_holds : tsup_quarantine_clear_spec B MT.
Proof.
intros ly S W regs mem md ch pw which R O H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
exact (sqc_SA sqc_SX ly S W regs mem md ch pw which R O
  (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 H12)))))))))))).
Qed.

End e.
End f.
End d.
