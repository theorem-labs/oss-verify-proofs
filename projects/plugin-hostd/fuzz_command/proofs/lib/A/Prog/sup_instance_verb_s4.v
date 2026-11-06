(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the hypotheses, the pre- and post-condition bundles and the closing step of
   sup_instance_verb's ASan walk (plugin-hostd/fuzz_command, 0x8b3b8), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v
   (cl_cx, cl_post: the bundles a segment walk passes on) and A/ACh1.v (the step after the last call); restated over
   the statements of an earlier commit, then of passes 4, 4b, 5 (apost_baseF, fx-generic callee hypotheses). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c sup_instance_verb_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBTemplateSiv sup_instance_verb_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the footprint of the contract (sup_instance_verb_c.v:101) *)
Definition siv_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

Lemma siv_in_dec : forall (x : Z * Z) l, {In x l} + {~ In x l}.
Proof. intros x l. apply in_dec. intros a b. decide equality; apply Z.eq_dec. Qed.

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
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* every hypothesis the walk uses: the statement's (sup_instance_verb_c.v:74-81), and the walk's per-binary facts of
   the walk hypotheses (cgif's names) and the walks' shared named facts that no file of the tree states yet, each under
   its canonical name in the theorem's Section (lib/A/Prog/sup_instance_verb.v) *)
Record siv_hyps : Prop := {
sh_TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT;
sh_TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT;
sh_TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT;
sh_TRSO : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT;
sh_TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT;
sh_ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8;
sh_ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8;
sh_VOBJS : cmd_val_objs;
sh_TL : PALib B;
sh_HB : CmdBSyms B;
sh_MTL : ameter_laws MT;
sh_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a;
sh_prog_writable : forall ly S (W : world SEGS) mem md a,
  AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a;
sh_sig : cmd_sig_prog;
sh_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem);
sh_RRO : ro_below_ofl SEGS RLO RHI;
sh_RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a;
sh_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e;
sh_rec_cells : forall ly S W mem md, AR SEGS B ly S W mem md ->
  rdW W mem A_FLAG_REPLACE_STR = Some 1 /\ aguard_ok SEGS W mem 0xa7098 0x6045d8 /\
  exists ev, rd32 (rdW W mem) (as_errno B) ev;
sh_rom_view_on : forall (W : world SEGS) mem, arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem;
sh_ZSH : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> range_addressable (rdW W mem) SHADOW_OFF 0x21d60 3;
sh_HULL : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> shadow_hull_vis (rdW W mem) 0x21d60 3;
sh_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG
}.

(* the statement's premises (sup_instance_verb_c.v), in their order, but the rounding mode (frm0, carried apart: it
   is the one premise that names the FP state) *)
Definition siv_cx ly S W (regs : bvmap 5 word) mem md ch (pl ledger : Z) (line : list byte) (R : rstate)
  (O : list (Z * Z)) : Prop :=
afn_pre SEGS B SUP_INSTANCE_VERB_STK ly S W regs mem md ch /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pl /\ 0 <= pl < 2 ^ 64 /\
getr regs 11 = w64 ledger /\ -2 ^ 31 <= ledger < 2 ^ 31 /\
in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) /\ astr_atR (rdW W mem) pl line /\
Z.of_nat (length line) + 1 <= LMAX + 1 /\
Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_SUP_INSTANCE_VERB R <= EV_MAX /\ blocks_bytes S + LIVE_SUP_INSTANCE_VERB R line ledger <= LIVE_MAX /\
mo_ok MT S (XM_SUP_INSTANCE_VERB MT R line ledger).

(* the statement's post, word for word *)
Definition siv_Q (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (line : list byte) (ledger : Z) (R : rstate) (O : list (Z * Z))
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_instance_verb_m R line ledger = (R', t) /\
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
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_INSTANCE_VERB R line ledger /\
 mo_le MT S S' (XM_SUP_INSTANCE_VERB MT R line ledger).

Definition siv_post ly S W (regs : bvmap 5 word) mem md (line : list byte) (ledger : Z) (R : rstate)
  (O : list (Z * Z)) : world SEGS -> config -> Prop :=
apost_baseF SEGS B SUP_INSTANCE_VERB_STK (siv_FP O) regs ly S W mem md (EV_SUP_INSTANCE_VERB R)
  (siv_Q ly S W mem line ledger R O).

(* two live blocks with one start are one block *)
Lemma siv_block_start : forall ly S (W : world SEGS) mem md b m m',
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> In (b, m') (ablocks B ly S) -> m = m'.
Proof.
intros ly S W mem md b m m' HAR H1 H2.
destruct (Z.eq_dec m m') as [E|Hne]; [exact E|]. exfalso.
pose proof (al_blocks _ _ (AR_laws_ok SEGS B) _ _ _ _ _ b m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (al_blocks _ _ (AR_laws_ok SEGS B) _ _ _ _ _ b m' HAR H2) as (_ & _ & _ & _ & _ & _ & Hm').
pose proof (sep_blocks SEGS B (AR_laws_ok SEGS B) ly S W mem md b m b m' HAR H1 H2 ltac:(intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D.
pose proof (req_size_pos m ltac:(lia)). pose proof (req_size_pos m' ltac:(lia)). lia.
Qed.

(* two distinct live blocks lie apart *)
Lemma siv_blocks_apart : forall ly S (W : world SEGS) mem md b m p n,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
iv_apart b m p n.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (al_blocks _ _ (AR_laws_ok SEGS B) _ _ _ _ _ b m HAR H1) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (al_blocks _ _ (AR_laws_ok SEGS B) _ _ _ _ _ p n HAR H2) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (sep_blocks SEGS B (AR_laws_ok SEGS B) ly S W mem md b m p n HAR H1 H2 Hne) as D.
unfold zdisjoint in D. cbn [fst snd] in D. unfold iv_apart.
pose proof (req_size_pos m ltac:(lia)). pose proof (req_size_pos n ltac:(lia)). lia.
Qed.

(* the line's block: the live block that holds the line is none of the recorder's *)
Lemma siv_line_block : forall ly S (W : world SEGS) mem md pl n O,
AR SEGS B ly S W mem md -> in_blockA (ablocks B ly S) pl n -> 1 <= n ->
Forall (fun qk => iv_apart pl n (fst qk) (snd qk)) O ->
exists p k, In (p, k) (ablocks B ly S) /\ ~ In (p, k) O /\ p <= pl /\ pl + n <= p + k /\ 4096 <= p /\
  p + k <= alloc_ceiling.
Proof.
intros ly S W mem md pl n O HAR (p & k & Hpk & Hp1 & Hp2) Hn HAP.
destruct (al_blocks _ _ (AR_laws_ok SEGS B) _ _ _ _ _ p k HAR Hpk) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
exists p, k. split; [exact Hpk|]. split.
- intros Hin. pose proof (proj1 (Forall_forall _ _) HAP _ Hin) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap. lia.
- lia.
Qed.

(* the step after answer returns: the recorder's block facts at the tail jump (I1 .. I4), answer's post, the
   bytes spent before the tail jump, and the meter give the contract's post *)
Lemma siv_final : forall ly S (W : world SEGS) mem lyc Sc (Wc : world SEGS) memc mdc ly' S' (W' : world SEGS) mem' md'
  (regs' : bvmap 5 word) (line : list byte) (ledger : Z) (R : rstate) (O O1 O' : list (Z * Z)) (old p1 p2 : Z),
AR SEGS B lyc Sc Wc memc mdc -> AR SEGS B ly' S' W' mem' md' ->
(forall pn, In pn O1 -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O1) ->
(forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) ->
(old = 0 \/ exists m, In (old, m) O1) ->
let A := [canon line; dec ledger] in
let x := shape_of (first_word line) in
let R1 := rec_record R REC_INSTANCE_VERB A in
let t := snd (rec_answer R1 (REC_INSTANCE_VERB, A) x true) in
let n := Z.of_nat (length t) + 1 in
getr regs' 10 = w64 p2 -> 4096 <= p2 < 2 ^ 64 -> p1 <> p2 ->
(forall pn, In pn (ablocks B lyc Sc) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) ->
(forall pn, In pn (ablocks B ly' S') <-> (In pn (ablocks B lyc Sc) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
rec_repA B ly' S' (rdW W' mem') (fst (rec_answer R1 (REC_INSTANCE_VERB, A) x true)) O' ->
(forall pn, In pn O' <-> (In pn O1 /\ fst pn <> old) \/ pn = (p1, n)) ->
astr_atR (rdW W' mem') p2 t ->
blocks_bytes S' <= blocks_bytes S + LIVE_SUP_INSTANCE_VERB R line ledger ->
mo_le MT S S' (XM_SUP_INSTANCE_VERB MT R line ledger) ->
siv_Q ly S W mem line ledger R O ly' S' W' regs' mem' md'.
Proof.
intros ly S W mem lyc Sc Wc memc mdc ly' S' W' mem' md' regs' line ledger R O O1 O' old p1 p2
  HARc HAR' I1 I2 I3 I4 Hold A x R1 t n H10 Hp2 Hp12 HN HBL HREP' HO' HSTR HBB HMLE.
exists (fst (rec_answer R1 (REC_INSTANCE_VERB, A) x true)), t, p2, O'.
assert (HM : sup_instance_verb_m R line ledger = (fst (rec_answer R1 (REC_INSTANCE_VERB, A) x true), t)).
{ unfold sup_instance_verb_m, rec_stub, t, R1, A, x. destruct (rec_answer _ _ _ _). reflexivity. }
assert (HB2 : In (p2, n) (ablocks B ly' S')) by (apply HBL; right; right; reflexivity).
assert (Hold' : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> fst pn <> old).
{ intros [b m] Hin Hno Hb. cbn [fst] in Hb. subst b.
  pose proof (I2 (old, m) Hin Hno) as Hc.
  destruct Hold as [-> | (m' & Hm')].
  - pose proof (al_blocks _ _ (AR_laws_ok SEGS B) _ _ _ _ _ 0 m HARc Hc) as (_ & H4096 & _). lia.
  - pose proof (siv_block_start lyc Sc Wc memc mdc old m m' HARc Hc (I4 _ Hm')) as <-.
    destruct (I1 _ Hm') as [Ho | Hno']; [exact (Hno Ho) | exact (Hno' Hin)]. }
assert (HNe : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (p1, n) /\ pn <> (p2, n))
  by (intros pn Hin Hno; exact (HN pn (I2 pn Hin Hno) (Hold' pn Hin Hno))).
split; [exact HM|]. split; [exact H10|]. split; [exact Hp2|]. split; [exact HREP'|].
split.
{ intros pn Hpn. apply HO' in Hpn as [[Hpn _] | ->]; [exact (I1 pn Hpn)|].
  destruct (siv_in_dec (p1, n) (ablocks B ly S)) as [Hin|Hnin]; [|right; exact Hnin].
  destruct (siv_in_dec (p1, n) O) as [Ho|Hno]; [left; exact Ho|]. exfalso. exact (proj1 (HNe _ Hin Hno) eq_refl). }
split; [exact HB2|].
split; [intros pn Hin Hno; exact (proj2 (HNe pn Hin Hno))|].
split.
{ intros Hq. apply in_map_iff in Hq as ([b m] & Hb & Hbm). cbn [fst] in Hb. subst b.
  pose proof (rec_repA_in B ly' S' _ _ O' HREP' _ Hbm) as Hbm'.
  pose proof (siv_block_start ly' S' W' mem' md' p2 m n HAR' Hbm' HB2) as ->.
  apply HO' in Hbm as [[Hbm Hne] | Hbm].
  - exact (proj2 (HN _ (I4 _ Hbm) Hne) eq_refl).
  - injection Hbm as Hb. exact (Hp12 (eq_sym Hb)). }
split; [exact HSTR|].
split.
{ intros [b m] Hin Hno. pose proof (I2 _ Hin Hno) as Hc.
  assert (Hb' : In (b, m) (ablocks B ly' S')) by (apply HBL; left; split; [exact Hc | exact (Hold' _ Hin Hno)]).
  split; [exact Hb'|]. cbn [fst snd].
  exact (siv_blocks_apart ly' S' W' mem' md' b m p2 n HAR' Hb' HB2 (proj2 (HNe _ Hin Hno))). }
split.
{ intros pn Hpn. apply HBL in Hpn as [[Hc Hne] | [-> | ->]].
  - destruct (I3 pn Hc) as [Hl | Ho1]; [left; exact Hl | right; left; apply HO'; left; exact (conj Ho1 Hne)].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split; [exact HBB | exact HMLE].
Qed.

End e.
End f.
End d.
