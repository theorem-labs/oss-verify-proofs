(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sup_chain's LAST segment on plugin-hostd/fuzz_command.asan
   (BASE + AF_sup_chain + 0x184 = 0x8c438 .. the tail jump `j answer` at 0x8c4e4), in the walk style of
   lib/A/Prog/sup_chain.v's `sc_segA_table`.

   The segment is: the guarded argument block S' (the load4 check on c->nargs through s7, `li a1,5` and the
   `blt a1,a0` that skips to the free when nargs > 5 - not taken here, nargs = 2), xstrdup(list) at 0x8c450,
   the second load4 check on c->nargs, the store of nargs + 1 and the store8 check on c->args[nargs] at
   0x8c484; then wrapper_free(list) at 0x8c48c; then rec_shape_of("chain", 5) at 0x8c49c with the literal
   .str.17 at 0x21f20; then `li a2,1`, a1 := a0, a0 := s0, the epilogue that restores the 13 callee-saved
   registers and adds 112 to sp, and the tail jump `j answer`, which runs answer at this function's entry
   stack pointer.

   Statement passes 4, 4b and 5: the callee and runtime contracts are taken at every FP
   state (forall fx0) and used at the segment's fx; xstrdup, the free wrapper and rec_shape_of keep the FP state
   (old kit rules); answer reaches the snprintf wrapper, so the tail jump is PaFx.v's cl_callS_wideF with the
   segment's rounding-mode-0 premise, and apost_baseF_intro closes sup_chain's apost_baseF at the fx1 answer
   returns. astack_pres is gone from the statements: the frame chains come from the walk (s0 = the slot c at the
   two allocating calls and at rec_shape_of, achain_low; s0 = the entry s0 at the tail jump, afn_pre's chain kept). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaArt
PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c xstrdup_c rec_shape_of_c hand_back_c mix_call_c answer_c sup_chain_c RecBLemmas
PaNoChain PaFx sup_chain_s1 sup_chain_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing offset of the segment's entry: where the loop exits and where the `blez` of 0x8c3c4 skips to *)
Definition SC_TAILSEG : Z := AF_sup_chain + 0x184.

(* the walk's footprint, as sup_chain.v's sc_FP (same body, so the two are convertible) *)
Definition sc6_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* the saved registers of sup_chain's frame, in the order the prologue stored them (sup_chain.v's sc_saved) *)
Definition sc6_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* the verb the call records, "chain": the literal .str.17 at 0x21f20 without its terminator *)
Definition sc6_verb : list byte := bstr "chain"%string.

Lemma sc6_verb_ro : sc6_verb ++ [Z_to_bv 8 0] = RO_lit_21f20.
Proof. vm_compute. reflexivity. Qed.

Lemma sc6_verb_len : length sc6_verb = 5%nat.
Proof. reflexivity. Qed.

Lemma sc6_shape_eq : daemon_shape "chain"%string = shape_of sc6_verb.
Proof. reflexivity. Qed.

Lemma sc6_fits : fits (shape_of sc6_verb).
Proof. unfold fits. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma sc6_abytes_prefix : forall rd a (l1 l2 : list byte), abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 by exact Hi. reflexivity.
Qed.

(* a member of a filtered list is a member of the list (the filter answer_c.v's footprint uses) *)
Lemma sc6_filter_in : forall (old : Z) (l : list (Z * Z)) x, In x (filter (fun pn => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|a l IH]; intros H; cbn in H; [exact H|].
destruct (fst a =? old); [destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)] | right; exact (IH H)].
Qed.

(* the bytes of g_rec and record.spill *)
Definition sc6_rec (a : Z) : Prop :=
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.

Lemma sc6_slot_in : forall c a, sc_slot_ok c -> c <= a < c + CALL_SIZE -> sc6_rec a.
Proof.
intros c a Hc Ha. pose proof (sc_slot_bounds c Hc) as (H1 & H2 & _). unfold sc6_rec.
destruct Hc as [(i & Hi & ->) | ->];
  unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Lemma sc6_in_PG : forall a, sc6_rec a -> Exists (in_zr a) recb_PG.
Proof. intros a [Ha | Ha]; [exact (recb_grec_in a Ha) | exact (recb_spill_in a Ha)]. Qed.

(* the symbolic pieces of the segment's entry state *)
Definition sc6_Bx : sv := SOff 22 0.
Definition sc6_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition sc6_SH : list shent := [mkSHE 8 0 CALL_SIZE].
Definition sc6_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (22%nat, mkAF SB SB 0)] [] [].
(* s7 = ((c + 4) >> 3) + SB, as the prologue computed it at 0x8c368 / 0x8c36c *)
Definition sc6_s7 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 4) (SLit 3)) (SOff 22 0).
Definition sc6_sr : list sv := sr_sets sr_atoms [(19%bv, SOff 8 4); (23%bv, sc6_s7)].
(* the frame: 112 bytes below the entry sp, read-only for this segment (the epilogue only loads) *)
Definition sc6_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 112 0 0
[YP09.mkChunk 104 (CVal 8 (SOff 32 0)); YP09.mkChunk 96 (CVal 8 (SOff 33 0));
 YP09.mkChunk 88 (CVal 8 (SOff 34 0)); YP09.mkChunk 80 (CVal 8 (SOff 35 0));
 YP09.mkChunk 72 (CVal 8 (SOff 36 0)); YP09.mkChunk 64 (CVal 8 (SOff 37 0));
 YP09.mkChunk 56 (CVal 8 (SOff 38 0)); YP09.mkChunk 48 (CVal 8 (SOff 39 0));
 YP09.mkChunk 40 (CVal 8 (SOff 40 0)); YP09.mkChunk 32 (CVal 8 (SOff 41 0));
 YP09.mkChunk 24 (CVal 8 (SOff 42 0)); YP09.mkChunk 16 (CVal 8 (SOff 43 0));
 YP09.mkChunk 8 (CVal 8 (SOff 44 0))].
(* the slot, as two regions so that the walk's frame keeps c->args[0] and c->args[1], which lie between the two
   bytes the segment writes: c->nargs (read twice, written once) and c->args[2] (written) *)
Definition sc6_slotN : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 4 8
[YP09.mkChunk 4 (CVal 4 (SLit 2))].
Definition sc6_slotA : YP09.region := YP09.mkRegion (Some 8%nat) 8 32 24 32 [].
(* the bytes of the slot the segment may write *)
Definition sc6_wr (c a : Z) : Prop := c + 4 <= a < c + 8 \/ c + 24 <= a < c + 32.
Lemma sc6_wr_sub : forall c a, sc6_wr c a -> c + 4 <= a < c + 32.
Proof. intros c a [H | H]; lia. Qed.
Definition ss_tail : sstate := mkSS SC_TAILSEG sc6_sr [sc6_frame; sc6_slotN; sc6_slotA] None sc6_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the entry values of the 13 saved registers, as the atoms 32 .. 44 of the segment's environment *)
Definition sc6_ext (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 r)) sc6_saved.
Definition ET (regsc regs : bvmap 5 word) : env := Eimg (Ereg regsc (sc6_ext regs)).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
(* the statement's own callee contracts that this segment uses (sup_chain_c.v:82-84, :86) *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
(* cmd_ro_ok names only bytes no runtime entry owns, so arodata_okP gives it back at any AR state; arodata_okP
   travels with arodata_ok_journalP, whose two facts are RRO and RELRO_IMG, and whose footprint premise uses
   cmd_ro_prog_apart *)
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the read-only bytes of the image's literals (CmdRo.v:434): the verb "chain" at 0x21f20 that rec_shape_of reads
   through astr_argA's read-only arm *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
(* the 8-byte-rounded user bytes of a live block are visible (AR gives only [p, p + req_size n)); xstrdup's
   strlen wrapper reads the word that holds the text's terminator *)
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.

Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.

Lemma sc6_sig : SIG CS_xstrdup = BASE + AF_xstrdup /\ SIG CS_rec_shape_of = BASE + AF_rec_shape_of /\
  SIG CS_answer = BASE + AF_answer.
Proof. rewrite !SIGP by (vm_compute; tauto). vm_compute. repeat split; reflexivity. Qed.

Lemma sc6_verb_val : VAL SC_VERB = 0x21f20.
Proof. unfold SC_VERB. rewrite (VOBJS 72%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma sc6_val_of_rdword : forall (W : world SEGS) mem a v,
rdword (rdW W mem) a = Some v -> val_mem SEGS (mrestrict (w_H W) mem) a 8 v.
Proof. intros W mem a v H. exact (val_mem_of_rdword SEGS _ _ _ _ H). Qed.

(* a write of the walk to g_rec or record.spill is one the footprint names *)
Lemma sc6_awr_rec : forall STK sp0 O bl0 blc fr0 lyc own a,
sc6_rec a -> awr_byte SEGS B STK sp0 (sc6_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha.
right; right; right; right; left.
assert (HP : Exists (in_zr a) recb_PG) by exact (sc6_in_PG a Ha).
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

Lemma sc6_prog_fp : forall O a, sc6_rec a ->
inFP (sc6_FP O) a /\ Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof.
intros O a Ha. assert (HP : Exists (in_zr a) recb_PG) by exact (sc6_in_PG a Ha).
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

(* g_rec's and record.spill's bytes are none of the runtime's statics and not the errno cell *)
Lemma sc6_rec_unowned : forall a, sc6_rec a ->
~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold sc6_rec in Ha.
split.
- intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
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

(* a callee whose footprint misses a byte of g_rec / record.spill leaves it as it was *)
Lemma sc6_rec_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k a,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP1 -> sc6_rec a -> ~ inFP FP1 a -> rdW W' mem' a = rdW Wc memc a.
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k a HJ Hsk Ha Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (sc6_rec_unowned a Ha) as [Ho He].
apply F3; [| exact Ho | exact He | exact (fp_spares_closed FP1 a Hsk Hn)].
apply cmd_prog_img. apply sc6_in_PG. exact Ha.
Qed.

(* a live block is apart from g_rec and record.spill *)
Lemma sc6_blk_apart : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
iv_apart p n A_G_REC REC_SIZE /\ iv_apart p n A_REC_SPILL SC_SIZE.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hp4096 & _ & _ & _ & _ & Hnr).
assert (Hn0 : 0 <= n) by lia.
pose proof (req_size_pos n Hn0) as [R1 R2].
assert (HI : forall a, p <= a < p + req_size n -> ~ in_img SEGS a)
  by (intros a Ha; apply (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin); lia).
unfold iv_apart. split.
- destruct (Z.le_gt_cases (p + n) A_G_REC) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (A_G_REC + REC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (HI (Z.max p A_G_REC)); [lia|]. apply cmd_prog_img. apply sc6_in_PG. left. unfold REC_SIZE in *. lia.
- destruct (Z.le_gt_cases (p + n) A_REC_SPILL) as [H|H]; [left; exact H|].
  destruct (Z.le_gt_cases (A_REC_SPILL + SC_SIZE) p) as [H'|H']; [right; exact H'|]. exfalso.
  apply (HI (Z.max p A_REC_SPILL)); [lia|]. apply cmd_prog_img. apply sc6_in_PG. right. unfold SC_SIZE in *. lia.
Qed.

(* a block live across a callee whose footprint lies in g_rec / record.spill keeps its bytes *)
Lemma sc6_blk_kept : forall STK sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly' S' W' mem' md' k p n i,
ajournal SEGS B STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k ->
AR SEGS B lyc Sc Wc memc mdc ->
(forall a, inFP FP1 a -> sc6_rec a) ->
In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly' S') -> 0 <= i < n ->
rdW W' mem' (p + i) = rdW Wc memc (p + i).
Proof.
intros STK sp1 FP1 lyc Sc Wc memc mdc own ly' S' W' mem' md' k p n i HJ HAR HFP Hin Hin' Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos n ltac:(lia)) as [R1 R2].
apply (F2 p n i); [exact Hin | exact Hin' | lia |].
intros Hf. apply HFP in Hf.
apply (blk_img SEGS B LAWS lyc Sc Wc memc mdc p n (p + i) HAR Hin); [lia|].
apply cmd_prog_img. apply sc6_in_PG. exact Hf.
Qed.

(* two live blocks with the same start are the same block *)
Lemma sc6_same_start : forall ly S (W : world SEGS) mem md a b, AR SEGS B ly S W mem md ->
In a (ablocks B ly S) -> In b (ablocks B ly S) -> fst a = fst b -> a = b.
Proof.
intros ly S W mem md [pa na] [pb nb] HAR Ha Hb E. cbn [fst] in E. subst pb.
destruct (recb_pair_dec (pa, na) (pa, nb)) as [Heq | Hne]; [exact Heq|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md pa na pa nb HAR Ha Hb Hne) as Hd.
destruct (al_blocks _ _ LAWS ly S W mem md pa na HAR Ha) as (_ & _ & _ & _ & _ & _ & Hna).
destruct (al_blocks _ _ LAWS ly S W mem md pa nb HAR Hb) as (_ & _ & _ & _ & _ & _ & Hnb).
pose proof (req_size_pos na ltac:(lia)) as [Ra _]. pose proof (req_size_pos nb ltac:(lia)) as [Rb _].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the slot's 56 bytes are marked usable *)
Lemma sc6_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> sc_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. pose proof (sc_slot_bounds c Hc) as (H1 & H2 & _).
destruct Hc as [(i & Hi & ->) | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) _ CALL_SIZE HAR);
  [apply sc_in_zsh_of_existsb; vm_compute; reflexivity | reflexivity | reflexivity
  | cbn [fst]; unfold A_G_REC, OFF_CALLS, CALL_SIZE in *; lia
  | cbn [fst snd]; unfold A_G_REC, OFF_CALLS, CALL_SIZE in *; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0) A_REC_SPILL CALL_SIZE HAR);
  [apply sc_in_zsh_of_existsb; vm_compute; reflexivity | reflexivity | reflexivity
  | cbn [fst]; unfold A_REC_SPILL; lia | cbn [fst snd]; unfold A_REC_SPILL, CALL_SIZE; lia].
Qed.

(* the representation survives any change outside g_rec, record.spill and the recorder's own blocks *)
Lemma sc6_repA_keep : forall ly1 S1 rd ly2 S2 rd' R O,
rec_repA B ly1 S1 rd R O ->
(forall a, sc6_rec a -> rd' a = rd a) ->
(forall pn, In pn O -> In pn (ablocks B ly2 S2) /\
   forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
rec_repA B ly2 S2 rd' R O.
Proof.
intros ly1 S1 rd ly2 S2 rd' R O (Q & HQ & HO) KG KB.
assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly2 S2) /\
   forall i, 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
  by (intros pn Hpn; apply KB; apply HO; exact Hpn).
exists Q. split; [|exact HO].
destruct HQ as (H1 & H2 & H3 & HC & HAn & HRe & HSc & HOw).
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|split; [|split; [|split]]].
- unfold ag1_calls. split; [exact C1|]. split; [exact C2|]. split.
  + apply (sc3_aval_keep rd); [exact C3|]. intros x Hx. apply KG.
    left. unfold OFF_NCALLS, REC_SIZE in *. lia.
  + split.
    * intros i cc P Ec EP. destruct (C4 i cc P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (l_calls Q))%nat) by (apply nth_error_Some; rewrite EP; discriminate).
      assert (Hi16 : (i < 16)%nat) by lia.
      assert (HPQ : forall pn, In pn P -> In pn (lay_blocks Q)).
      { intros pn Hpn. unfold lay_blocks. apply in_or_app. left. exact (In_concat_nth _ i P pn EP Hpn). }
      apply (sc3_call_keep (ablocks B ly1 S1) _ rd rd' _ cc P Hc).
      -- intros x Hx. apply KG. left. unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      -- intros pn Hpn _. exact (proj1 (KQ pn (HPQ pn Hpn))).
      -- intros pn Hpn i' Hi'. exact (proj2 (KQ pn (HPQ pn Hpn)) i' Hi').
    * split.
      -- assert (HSQ : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q)).
         { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
         apply (sc3_call_keep (ablocks B ly1 S1) _ rd rd' _ _ _ C5).
         ++ intros x Hx. apply KG. right. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
         ++ intros pn Hpn _. exact (proj1 (KQ pn (HSQ pn Hpn))).
         ++ intros pn Hpn i' Hi'. exact (proj2 (KQ pn (HSQ pn Hpn)) i' Hi').
      -- exact C6.
- assert (HAQ : forall pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  apply (sc3_answer_keep (ablocks B ly1 S1) _ rd rd' _ _ _ HAn).
  + intros x Hx. apply KG. left. unfold OFF_ANSWER, REC_SIZE in *. lia.
  + intros pn Hpn _. exact (proj1 (KQ pn (HAQ pn Hpn))).
  + intros pn Hpn i' Hi'. exact (proj2 (KQ pn (HAQ pn Hpn)) i' Hi').
- assert (HRQ : forall pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q)).
  { intros pn Hpn. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hpn. }
  apply (sc3_reply_keep (ablocks B ly1 S1) _ rd rd' _ _ _ HRe).
  + intros x Hx. apply KG. left. unfold OFF_REPLY, OFF_REPLY_SIZE, REC_SIZE in *. lia.
  + intros pn Hpn _. exact (proj1 (KQ pn (HRQ pn Hpn))).
  + intros pn Hpn i' Hi'. exact (proj2 (KQ pn (HRQ pn Hpn)) i' Hi').
- apply (sc3_scalars_keep rd); [exact HSc|]. intros x Hx. apply KG. left.
  unfold OFF_NREPLIES, OFF_STATE, OFF_HOST, REC_SIZE in *. lia.
- exact HOw.
Qed.

(* the recorder's answer pointer, and the block it points at *)
Lemma sc6_repA_answer : forall ly S rd R O, rec_repA B ly S rd R O ->
exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists pn, In pn O /\ fst pn = old).
Proof.
intros ly S rd R O (Q & HQ & HO).
destruct HQ as (_ & _ & _ & _ & HAn & _).
unfold aanswer_at in HAn.
destruct (r_answer R) as [x|] eqn:Ea; destruct (l_answer Q) as [pn|] eqn:Eq; try contradiction.
- destruct HAn as (N1 & _). exists (fst pn). split; [exact N1|]. right. exists pn. split; [|reflexivity].
  apply HO. unfold lay_blocks. rewrite Eq. cbn [oblk].
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity.
- exists 0. split; [exact HAn | left; reflexivity].
Qed.

Lemma sc6_repA_blocks : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HQ & HO) pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HQ pn (proj1 (HO pn) Hpn)).
Qed.

(* a read-only byte is no byte of the walk's footprint: not g_rec or record.spill (program statics), not a block
   (an image byte); sup_chain.v's APART *)
Lemma sc6_ro_off : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (sc6_FP O) a.
Proof.
intros ly S W mem md O HAR HOS a Hro Hfp. destruct (cmd_ro_prog_apart a Hro) as [Himg Hpg].
unfold sc6_FP in Hfp. destruct Hfp as (r & Hr & Hra2).
destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Hra2. apply Hpg. apply recb_grec_in. exact Hra2.
- cbn [fst snd] in Hra2. apply Hpg. apply recb_spill_in. exact Hra2.
- destruct (inFP_ablocks_fp_inv O a ltac:(exists r; split; [exact Hr | exact Hra2])) as (q & nq & Hin & Hr2).
  exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
                  (or_introl (ex_intro _ q (ex_intro _ nq (conj (HOS _ Hin) Hr2))))) Himg).
Qed.

(* a string argument survives a change of memory that keeps every byte of the address space *)
Lemma sc6_argA_keep : forall ly S (W0 : world SEGS) mem0 md0 (rd rd' : reader) O p x,
AR SEGS B ly S W0 mem0 md0 ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
(forall a, 0 <= a < 2 ^ 64 -> rd' a = rd a) ->
astr_argA B ly S rd' (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros ly S W0 mem0 md0 rd rd' O p x HAR (H0 & Hs & Hl & Har) K.
pose proof asan_consts as (CA1 & _).
assert (Hb : forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= p + i < 2 ^ 64).
{ intros i Hi. destruct Har as [((q & k & Hin & Hq1 & Hq2) & _) | (Hro & _)].
  - destruct (al_blocks _ _ LAWS ly S W0 mem0 md0 q k HAR Hin) as (_ & Hq4096 & Hqc & _ & _ & _ & Hk0).
    pose proof (req_size_pos k ltac:(lia)) as [Rk1 Rk2]. lia.
  - destruct (Hro i Hi) as (Hr & _ & _). destruct (cmd_ro_prog_apart _ Hr) as [Himg _].
    pose proof (pa_img_range _ Himg). lia. }
split; [exact H0|]. split; [|split; [exact Hl | exact Har]].
apply (sc3_str_keep rd); [exact Hs|]. intros i Hi. apply K. exact (Hb i Hi).
Qed.

(* the verb "chain" (.str.17 at 0x21f20) in astr_argA's read-only arm, the form rec_shape_of's verb premise takes *)
Lemma sc6_verb_argA : forall ly S (rd : reader), abytes_atR rd 0x21f20 RO_lit_21f20 ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) [] 0x21f20 (Some sc6_verb).
Proof.
intros ly S rd HL. unfold astr_argA. rewrite sc6_verb_len.
assert (HRO6 : forall i, 0 <= i < 6 -> in_roP SEGS RLO RHI (0x21f20 + i)).
{ clear - CMD_RO_IN. unfold cmd_ro_in in CMD_RO_IN.
  repeat match type of CMD_RO_IN with
  | (forall i, 0 <= i < 6 -> _ (0x21f20 + i)) /\ _ => exact (proj1 CMD_RO_IN)
  | _ /\ _ => apply proj2 in CMD_RO_IN
  end. }
split; [lia|]. split.
{ split; [rewrite sc6_verb_ro; exact HL|].
  assert (Hnz : forallb (fun b => negb (bv_unsigned b =? 0)) sc6_verb = true) by (vm_compute; reflexivity).
  intros Hin. pose proof (proj1 (forallb_forall _ _) Hnz _ Hin) as Hb. vm_compute in Hb. discriminate Hb. }
split; [unfold LMAX; lia|]. right.
split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity|]]].
- intros i Hi. split; [apply HRO6; lia|].
  rewrite (ts_owned B HB), (ts_errno B HB). split.
  + intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
    assert (Hb1 : forallb (fun r => (0x21f26 <=? fst r) || (fst r + snd r <=? 0x21f20)) Tfib_owned_static = true)
      by (vm_compute; reflexivity).
    pose proof (proj1 (forallb_forall _ _) Hb1 _ Hin) as Hq1. cbn beta in Hq1. cbn [fst snd] in Hq1.
    apply Bool.orb_true_iff in Hq1 as [Hq1 | Hq1]; apply Z.leb_le in Hq1; lia.
  + unfold TFIB_ERRNO. lia.
- assert (HE : existsb (Z.eqb (0x21f20 + Z.of_nat 5)) cmd_ro_ends = true) by (vm_compute; reflexivity).
  apply existsb_exists in HE as (y & Hy & Ey). apply Z.eqb_eq in Ey. rewrite Ey. exact Hy.
Qed.

(* the denotation of s7 = ((c + 4) >> 3) + SB *)
Lemma sc6_s7_denot : forall E c, bv_unsigned (ew E 8) = c -> bv_unsigned (ew E 22) = SB ->
0 <= c < 2 ^ 47 -> sv_denot E sc6_s7 = Z_to_bv 64 (SB + (c + 4) / 8).
Proof.
intros E c H8 H22 Hc.
assert (ZC : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x)
  by (intros x Hx; unfold zcanon, M64; apply Z.mod_small; lia).
assert (Hd : 0 <= (c + 4) / 8 <= c + 4) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E sc6_s7)). f_equal.
change (U E sc6_s7 = SB + (c + 4) / 8). unfold sc6_s7.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, U_SLit, H8, H22, (ZC 3) by lia.
rewrite (ZC (c + 4)) by lia.
change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (ZC ((c + 4) / 8)) by lia. rewrite !Z.add_0_r.
rewrite ?(ZC SB) by (unfold SB; lia).
rewrite ZC by (unfold SB in *; lia). lia.
Qed.

Lemma sc6_soff_denot : forall E m v k, bv_unsigned (ew E m) = v -> 0 <= v + k < 2 ^ 64 ->
sv_denot E (SOff m k) = Z_to_bv 64 (v + k).
Proof.
intros E m v k Hm Hv. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SOff m k))). f_equal.
change (U E (SOff m k) = v + k). rewrite U_SOff, Hm. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* --- the entry state of the segment --------------------------------------------------------------------- *)

Lemma sc6_seed : forall ly S (W : world SEGS) mem md (regsc regs : bvmap 5 word) c sp0,
AR SEGS B ly S W mem md ->
2 ^ 46 + 112 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> spZ regsc = sp0 - 112 ->
getr regsc 8 = w64 c -> sc_slot_ok c ->
getr regsc 19 = w64 (c + 4) -> getr regsc 22 = w64 SB -> getr regsc 23 = w64 (SB + (c + 4) / 8) ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 2 ->
(forall j r, nth_error sc6_saved j = Some r ->
   val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
st_ok_pi SEGS VAL (ET regsc regs) ss_tail
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + SC_TAILSEG)) mem (seg_rom SEGS)))
/\ sh_ok SEGS sc6_Bx sc6_SH (ET regsc regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regsc regs c sp0 HAR Hsp46 Hsp16 Hspc H8 Hc H19 H22 H23 HNA HFR.
pose proof (sc_slot_bounds c Hc) as (Hc1 & Hc2 & Hc8).
assert (Hcz : 0 <= c < 2 ^ 47) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
set (E := ET regsc regs).
assert (HEI : img_env VAL A_LIM E) by (unfold E, ET; apply Eimg_env).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, ET. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (sc6_ext regs) (Z_to_bv 64 0)).
{ intros j Hj. unfold E, ET. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (X0 : ew E 32 = getr regs (Z_to_bv 5 1)) by exact (EX 0%nat ltac:(lia)).
assert (X1 : ew E 33 = getr regs (Z_to_bv 5 8)) by exact (EX 1%nat ltac:(lia)).
assert (X2 : ew E 34 = getr regs (Z_to_bv 5 9)) by exact (EX 2%nat ltac:(lia)).
assert (X3 : ew E 35 = getr regs (Z_to_bv 5 18)) by exact (EX 3%nat ltac:(lia)).
assert (X4 : ew E 36 = getr regs (Z_to_bv 5 19)) by exact (EX 4%nat ltac:(lia)).
assert (X5 : ew E 37 = getr regs (Z_to_bv 5 20)) by exact (EX 5%nat ltac:(lia)).
assert (X6 : ew E 38 = getr regs (Z_to_bv 5 21)) by exact (EX 6%nat ltac:(lia)).
assert (X7 : ew E 39 = getr regs (Z_to_bv 5 22)) by exact (EX 7%nat ltac:(lia)).
assert (X8 : ew E 40 = getr regs (Z_to_bv 5 23)) by exact (EX 8%nat ltac:(lia)).
assert (X9 : ew E 41 = getr regs (Z_to_bv 5 24)) by exact (EX 9%nat ltac:(lia)).
assert (X10 : ew E 42 = getr regs (Z_to_bv 5 25)) by exact (EX 10%nat ltac:(lia)).
assert (X11 : ew E 43 = getr regs (Z_to_bv 5 26)) by exact (EX 11%nat ltac:(lia)).
assert (X12 : ew E 44 = getr regs (Z_to_bv 5 27)) by exact (EX 12%nat ltac:(lia)).
pose proof (HFR 0%nat 1 eq_refl) as F0. pose proof (HFR 1%nat 8 eq_refl) as F1.
pose proof (HFR 2%nat 9 eq_refl) as F2. pose proof (HFR 3%nat 18 eq_refl) as F3.
pose proof (HFR 4%nat 19 eq_refl) as F4. pose proof (HFR 5%nat 20 eq_refl) as F5.
pose proof (HFR 6%nat 21 eq_refl) as F6. pose proof (HFR 7%nat 22 eq_refl) as F7.
pose proof (HFR 8%nat 23 eq_refl) as F8. pose proof (HFR 9%nat 24 eq_refl) as F9.
pose proof (HFR 10%nat 25 eq_refl) as F10. pose proof (HFR 11%nat 26 eq_refl) as F11.
pose proof (HFR 12%nat 27 eq_refl) as F12.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12.
assert (E2 : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hspc).
assert (E8 : ew E 8 = w64 c) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8).
assert (E8u : bv_unsigned (ew E 8) = c) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (E22 : ew E 22 = w64 SB) by (rewrite (EL 22%nat 22%bv eq_refl); exact H22).
assert (E22u : bv_unsigned (ew E 22) = SB) by (rewrite E22; unfold w64; apply unsigned_lit_small; unfold SB; lia).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (CHK : forall (od : Z) (m : nat) (r : Z),
  ew E m = getr regs (Z_to_bv 5 r) ->
  val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 112 + od) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (sp0 - 112) (YP09.mkChunk od (CVal 8 (SOff m 0)))).
{ intros od m r Hm Hv.
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr.
  apply (chunk_ok_val SEGS E _ (sp0 - 112) od 8 (SOff m 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  - cbn [sv_denot]. rewrite Hm, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - exact Hv. }
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold sc6_sr. apply (regs_ok_sets E sr_atoms regsc regsc).
    * unfold E, ET. apply regs_ok_Eimg_Ereg.
    * apply reg_nodup_sound. vm_compute. reflexivity.
    * intros r _. reflexivity.
    * repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      (split; [vm_compute; reflexivity|]).
      -- rewrite H19. unfold w64. rewrite (sc6_soff_denot E 8%nat c 4 E8u ltac:(lia)). reflexivity.
      -- rewrite H23, (sc6_s7_denot E c E8u E22u Hcz). reflexivity.
  + vm_compute. reflexivity.
  + unfold sc6_frame, sc6_slotN, sc6_slotA.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
    unfold YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (CHK 104 32%nat 1 X0). replace (sp0 - 112 + 104) with (sp0 - 8 - 8 * 0) by lia. exact F0.
      -- apply (CHK 96 33%nat 8 X1). replace (sp0 - 112 + 96) with (sp0 - 8 - 8 * 1) by lia. exact F1.
      -- apply (CHK 88 34%nat 9 X2). replace (sp0 - 112 + 88) with (sp0 - 8 - 8 * 2) by lia. exact F2.
      -- apply (CHK 80 35%nat 18 X3). replace (sp0 - 112 + 80) with (sp0 - 8 - 8 * 3) by lia. exact F3.
      -- apply (CHK 72 36%nat 19 X4). replace (sp0 - 112 + 72) with (sp0 - 8 - 8 * 4) by lia. exact F4.
      -- apply (CHK 64 37%nat 20 X5). replace (sp0 - 112 + 64) with (sp0 - 8 - 8 * 5) by lia. exact F5.
      -- apply (CHK 56 38%nat 21 X6). replace (sp0 - 112 + 56) with (sp0 - 8 - 8 * 6) by lia. exact F6.
      -- apply (CHK 48 39%nat 22 X7). replace (sp0 - 112 + 48) with (sp0 - 8 - 8 * 7) by lia. exact F7.
      -- apply (CHK 40 40%nat 23 X8). replace (sp0 - 112 + 40) with (sp0 - 8 - 8 * 8) by lia. exact F8.
      -- apply (CHK 32 41%nat 24 X9). replace (sp0 - 112 + 32) with (sp0 - 8 - 8 * 9) by lia. exact F9.
      -- apply (CHK 24 42%nat 25 X10). replace (sp0 - 112 + 24) with (sp0 - 8 - 8 * 10) by lia. exact F10.
      -- apply (CHK 16 43%nat 26 X11). replace (sp0 - 112 + 16) with (sp0 - 8 - 8 * 11) by lia. exact F11.
      -- apply (CHK 8 44%nat 27 X12). replace (sp0 - 112 + 8) with (sp0 - 8 - 8 * 12) by lia. exact F12.
    * rewrite (VB 8%nat c E8 ltac:(lia)).
      split; [lia|]. split; [lia|]. split.
      -- intros o Ho. apply (cmd_prog_writable ly S W mem md (c + o) HAR). apply sc6_in_PG.
         apply (sc6_slot_in c); [exact Hc | unfold CALL_SIZE; lia].
      -- apply Forall_cons; [|apply Forall_nil].
         apply (chunk_ok_val SEGS E _ c 4 4 (SLit 2) 2); [reflexivity | cbn; lia | cbn; lia |].
         change (N.to_nat 4) with 4%nat. apply val_mem_view. unfold CALL_OFF_NARGS in HNA. exact HNA.
    * rewrite (VB 8%nat c E8 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (cmd_prog_writable ly S W mem md (c + o) HAR). apply sc6_in_PG.
      apply (sc6_slot_in c); [exact Hc | unfold CALL_SIZE; lia].
  + apply pairwise_disjoint_of_extents.
    unfold sc6_frame, sc6_slotN, sc6_slotA, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 8%nat c E8 ltac:(lia)). cbn [base_val]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split | |- True => exact I end;
    first [left; unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia
          | right; unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia].
  + unfold sc6_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I | exact I]].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8u, E22u.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
    try (replace (sp0 - 112) with (sp0 + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact Hsp16);
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia.
- unfold sh_ok, sc6_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E sc6_Bx 8%nat c CALL_SIZE c 0 CALL_SIZE).
  + exact (sc6_slot_addressable ly S W mem md c HAR Hc).
  + unfold sc6_Bx, U. cbn [sv_denot]. rewrite E22. unfold w64.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E8. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by (unfold CALL_SIZE; lia).
    unfold SHADOW_OFF, A_G_REC, A_REC_SPILL, OFF_CALLS, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the slot's nargs word, read off the recorder's representation *)
Lemma sc6_target_nargs : forall ly S rd R O kk e c, rec_repA B ly S rd R O -> sc_target R kk e c ->
aval_mem rd (c + CALL_OFF_NARGS) 4 (Z.of_nat (length (snd e))) /\ (length (snd e) <= 6)%nat.
Proof.
intros ly S rd R O kk e c (Q & HQ & HO) HT.
destruct HQ as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _).
destruct kk as [i|]; destruct HT as [HT1 HT2]; subst c.
- destruct (nth_error (l_calls Q) i) as [P|] eqn:EP.
  + destruct (C4 i e P HT1 EP) as [Hc _]. destruct Hc as (_ & Hn6 & _ & _ & Hna & _).
    split; [exact Hna | exact Hn6].
  + exfalso. apply nth_error_None in EP.
    assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite HT1; discriminate). lia.
- subst e. destruct C5 as (_ & Hn6 & _ & _ & Hna & _). split; [exact Hna | exact Hn6].
Qed.

(* region_kept of the slot across a callee that keeps g_rec and record.spill *)
Lemma sc6_region_kept_slot : forall Ex (W W2 : world SEGS) memT mem2 c lo hi wlo whi cs,
bv_unsigned (ew Ex 8) = c ->
(forall a, c + lo <= a < c + hi -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memT a) ->
(forall a, c + wlo <= a < c + whi -> writable_at SEGS (mrestrict (w_H W2) mem2) a) ->
region_kept SEGS Ex (mrestrict (w_H W) memT) (mrestrict (w_H W2) mem2)
  (YP09.mkRegion (Some 8%nat) lo hi wlo whi cs).
Proof.
intros Ex W W2 memT mem2 c lo hi wlo whi cs U Hv Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U.
- intros a Ha. apply (mbyte_of_aview SEGS). exact (Hv a Ha).
- intros a Ha _. exact (Hw a Ha).
Qed.

(* the contract's post, sup_chain_c.v:120-139 exactly *)
Definition sc6_Q (ly : alayout) (S : astate) (id : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_chain_m R id ids = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CHAIN R id ids /\
 mo_le MT S S' (XM_SUP_CHAIN MT R id ids).

(* --- the walk from 0x8c438 to the tail jump `j answer` at 0x8c4e4 --------------------------------------- *)

Theorem sc_segC : forall ly S W regs mem md ch (id : Z) (ids : list Z) (R R1 : rstate)
(O O1 : list (Z * Z)) (kk : option nat) (e1 : rcall)
lyc Sc Wc regsc memc mdc (kc XMc c lst : Z),
afn_pre SEGS B SUP_CHAIN_STK ly S W regs mem md ch ->
frm0 fx ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
(1 <= length ids <= 62)%nat ->
(* the journal of the segments before this one *)
ajournal SEGS B SUP_CHAIN_STK (spZ regs) (sc6_FP O) ly S W mem md [] lyc Sc Wc memc mdc kc ->
kc + EV_XSTRDUP + 1 + EV_REC_SHAPE_OF + EV_ANSWER <= EV_SUP_CHAIN R ->
st_nev S + EV_SUP_CHAIN R <= EV_MAX ->
Z.of_nat (length (frames Sc)) <= 8 ->
blocks_bytes S + LIVE_SUP_CHAIN R id ids <= LIVE_MAX ->
blocks_bytes Sc <= blocks_bytes S + (12 * Z.of_nat (length ids) + 1) + LIVE_ARG_I id + LIVE_ARG_I (Z.of_nat (length ids)) ->
mo_ok MT S (XM_SUP_CHAIN MT R id ids) -> mo_le MT S Sc XMc ->
XMc + (XM_XSTRDUP MT (dec_list ids) + mo_free MT + XM_ANSWER MT (snd (sup_chain_m R id ids)))
  <= XM_SUP_CHAIN MT R id ids ->
(* the registers at the segment's entry *)
spZ regsc = spZ regs - 112 ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 c -> sc_slot_ok c ->
getr regsc 19 = w64 (c + 4) -> getr regsc 20 = w64 lst -> getr regsc 22 = w64 SB ->
getr regsc 23 = w64 (SB + (c + 4) / 8) ->
(* the frame the prologue wrote (sup_chain.v's sc_frame_at, unfolded) *)
(forall j r, nth_error sc6_saved j = Some r ->
   val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
(* the recorder at the segment's entry: the call e1 in slot c with its first two arguments *)
rec_repA B lyc Sc (rdW Wc memc) R1 O1 ->
sc_target R1 kk e1 c -> fst e1 = REC_CHAIN ->
snd e1 = [dec id; dec (Z.of_nat (length ids))] ->
sc_push_arg R1 kk (dec_list ids)
  = rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids] ->
(* the list text the loop built *)
In (lst, 12 * Z.of_nat (length ids) + 1) (ablocks B lyc Sc) ->
~ In (lst, 12 * Z.of_nat (length ids) + 1) O1 ->
astr_atR (rdW Wc memc) lst (dec_list ids) ->
Z.of_nat (length (dec_list ids)) <= 12 * Z.of_nat (length ids) ->
(* the blocks, against the function's entry *)
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S) \/ In pn O1 \/
   pn = (lst, 12 * Z.of_nat (length ids) + 1)) ->
(forall pn, In pn O1 -> In pn O \/ ~ In pn (ablocks B ly S)) ->
(forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1 \/ pn = (lst, 12 * Z.of_nat (length ids) + 1)) ->
(In (lst, 12 * Z.of_nat (length ids) + 1) (ablocks B ly S) ->
   In (lst, 12 * Z.of_nat (length ids) + 1) O) ->
SRr SEGS Wc (cfg_at SEGS (BASE + SC_TAILSEG) regsc memc mdc)
  (apost_baseF SEGS B SUP_CHAIN_STK (sc6_FP O) regs ly S W mem md (EV_SUP_CHAIN R)
     (sc6_Q ly S id ids R O)).
Proof.
intros ly S W regs mem md ch id ids R R1 O O1 kk e1 lyc Sc Wc regsc memc mdc kc XMc c lst
  HPRE HRM0 HROD Hids HJ Hkc HEV0 HFRc HLIVE HBBc HMOK HMLE HXM
  Hspc H3 H4 H8 Hc H19 H20 H22 H23 HFRM HREP1 HT Hfn Hsnd HR2 HLin HLnO1 HLstr HLlen
  HOS HB2 HB1 HO1 HO2 HL0.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HJ as (_ & _ & _ & _ & _ & HfrC & HnevC & _).
assert (HEVn : EV_XSTRDUP = 1 /\ EV_REC_SHAPE_OF = 0 /\ EV_ANSWER = 3) by (split; [|split]; reflexivity).
assert (HEVc : st_nev Sc + (EV_XSTRDUP + 1 + EV_REC_SHAPE_OF + EV_ANSWER) <= EV_MAX) by lia.
set (sp0 := spZ regs) in *.
assert (WS0 : 112 <= SUP_CHAIN_STK) by (vm_compute; discriminate).
assert (WS1 : XSTRDUP_STK + 112 <= SUP_CHAIN_STK) by (vm_compute; discriminate).
assert (WS2 : ASTACK + 112 <= SUP_CHAIN_STK) by (vm_compute; discriminate).
assert (WS3 : REC_SHAPE_OF_STK + 112 <= SUP_CHAIN_STK) by (vm_compute; discriminate).
assert (WS4 : ANSWER_STK <= SUP_CHAIN_STK) by (vm_compute; discriminate).
assert (WS5 : 0 <= XSTRDUP_STK /\ 0 <= REC_SHAPE_OF_STK /\ 0 <= ANSWER_STK)
  by (unfold XSTRDUP_STK, REC_SHAPE_OF_STK, ANSWER_STK, HAND_BACK_STK, MIX_CALL_STK, ASTACK, ESTACK; lia).
assert (Hsp46 : 2 ^ 46 + 112 <= sp0 <= 2 ^ 47)
  by (change (2 ^ 46) with 70368744177664; change (2 ^ 47) with 140737488355328; lia).
pose proof (sc_slot_bounds c Hc) as (Hc1 & Hc2 & Hc8).
assert (Hcz : 0 <= c /\ c + 32 < alloc_ceiling)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
assert (Hcz64 : 0 <= c < 2 ^ 47) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
assert (Hn62 : 1 <= Z.of_nat (length ids) <= 62) by lia.
pose proof (proj1 HJ) as HARc.
destruct (sc6_target_nargs lyc Sc (rdW Wc memc) R1 O1 kk e1 c HREP1 HT) as [HNA2 Hn6].
rewrite Hsnd in HNA2, Hn6. cbn [length] in HNA2, Hn6.
change (Z.of_nat 2) with 2 in HNA2.
(* the list block, and its distance from the slot *)
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc lst (12 * Z.of_nat (length ids) + 1) HARc HLin)
  as (_ & Hlst4096 & Hlstc & _ & _ & _ & Hlstn).
pose proof (req_size_pos (12 * Z.of_nat (length ids) + 1) ltac:(lia)) as [RL1 RL2].
assert (HAPL : forall i, 0 <= i < 12 * Z.of_nat (length ids) + 1 -> ~ (c + 4 <= lst + i < c + 32)).
{ destruct (sc6_blk_apart lyc Sc Wc memc mdc lst (12 * Z.of_nat (length ids) + 1) HARc HLin) as [Ap1 Ap2].
  unfold iv_apart in Ap1, Ap2. intros i Hi Hbad.
  destruct Hc as [(ii & Hii & Hce) | Hce]; rewrite Hce in *;
    unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia. }
assert (HX0 : 0 <= XM_XSTRDUP MT (dec_list ids) /\ 0 <= mo_free MT /\
              0 <= XM_ANSWER MT (snd (sup_chain_m R id ids))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
  pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec_list ids)) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1) ltac:(lia)). lia. }
(* the live bytes: the statement's budget, less the list text, the two numbers and answer's copies, covers the
   copy xstrdup makes; with the list text freed it covers answer's two copies *)
assert (HLANS : 0 <= LIVE_ANSWER (snd (sup_chain_m R id ids)))
  by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP; lia).
assert (HLIVEx : blocks_bytes Sc + LIVE_XSTRDUP (dec_list ids) <= LIVE_MAX)
  by (unfold LIVE_SUP_CHAIN in HLIVE; lia).
(* the symbolic state at the segment's entry *)
destruct (sc6_seed lyc Sc Wc memc mdc regsc regs c sp0 HARc Hsp46 Hal16 Hspc H8 Hc H19 H22 H23 HNA2 HFRM)
  as [HS SHOK].
set (E := ET regsc regs) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ET; apply Eimg_env).
assert (EL : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsc r).
{ intros m r Hm. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E, ET. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (sc6_ext regs) (Z_to_bv 64 0)).
{ intros j Hj. unfold E, ET. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (X0 : ew E 32 = getr regs (Z_to_bv 5 1)) by exact (EX 0%nat ltac:(lia)).
assert (X1 : ew E 33 = getr regs (Z_to_bv 5 8)) by exact (EX 1%nat ltac:(lia)).
assert (X2 : ew E 34 = getr regs (Z_to_bv 5 9)) by exact (EX 2%nat ltac:(lia)).
assert (X3 : ew E 35 = getr regs (Z_to_bv 5 18)) by exact (EX 3%nat ltac:(lia)).
assert (X4 : ew E 36 = getr regs (Z_to_bv 5 19)) by exact (EX 4%nat ltac:(lia)).
assert (X5 : ew E 37 = getr regs (Z_to_bv 5 20)) by exact (EX 5%nat ltac:(lia)).
assert (X6 : ew E 38 = getr regs (Z_to_bv 5 21)) by exact (EX 6%nat ltac:(lia)).
assert (X7 : ew E 39 = getr regs (Z_to_bv 5 22)) by exact (EX 7%nat ltac:(lia)).
assert (X8 : ew E 40 = getr regs (Z_to_bv 5 23)) by exact (EX 8%nat ltac:(lia)).
assert (X9 : ew E 41 = getr regs (Z_to_bv 5 24)) by exact (EX 9%nat ltac:(lia)).
assert (X10 : ew E 42 = getr regs (Z_to_bv 5 25)) by exact (EX 10%nat ltac:(lia)).
assert (X11 : ew E 43 = getr regs (Z_to_bv 5 26)) by exact (EX 11%nat ltac:(lia)).
assert (X12 : ew E 44 = getr regs (Z_to_bv 5 27)) by exact (EX 12%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hspc).
assert (E8 : ew E 8 = w64 c) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8).
assert (Uc : bv_unsigned (ew E 8) = c) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = w64 lst) by (rewrite (EL 20%nat 20%bv eq_refl); exact H20).
assert (E22 : ew E 22 = w64 SB) by (rewrite (EL 22%nat 22%bv eq_refl); exact H22).
assert (U22 : bv_unsigned (ew E 22) = SB)
  by (rewrite E22; unfold w64; apply unsigned_lit_small; unfold SB; lia).
assert (E3 : ew E 3 = getr regsc 3) by exact (EL 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regsc 4) by exact (EL 4%nat 4%bv eq_refl).
clearbody E. clear EX EL.
unfold cfg_at, w64.
(* --- 0x8c438 .. 0x8c450: the shadow check, nargs <= 5, a0 := list, the call of xstrdup --------------- *)
paj_run_tok RUN HS HJ SHOK sc6_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 8%nat) (b := c);
  [ reflexivity | exact Uc
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply sc6_awr_rec;
    apply (sc6_slot_in c); [exact Hc | unfold CALL_SIZE; lia]
  | ].
  eapply awr_ok_cons_gen with (n := 8%nat) (b := c);
  [ reflexivity | exact Uc
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply sc6_awr_rec;
    apply (sc6_slot_in c); [exact Hc | unfold CALL_SIZE; lia]
  | apply awr_ok_nil ]. }
try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
  set (mdv1 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv1 end).
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgA := rg) in *; set (mA := mm) in *; set (mdvA := mdq) in * end.
clearbody mdvA.
pose proof (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc mA (sc6_wr c) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Uc in Hrr;
       unfold sc6_wr; first [left; lia | right; lia]|]);
    destruct Hin)) as UN1.
clear HF HFr HG.
pose proof (proj1 HJ) as HARa.
pose proof (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
  (sc6_ro_off ly S W mem md O HAR HOS) HROD) as HRODa.
assert (HARGs : astr_argA B lyc Sc (rdW Wc mA) (in_roP SEGS RLO RHI) [] lst (Some (dec_list ids))).
{ unfold astr_argA. split; [lia|]. split.
  - apply (sc3_str_keep (rdW Wc memc)); [exact HLstr|].
    intros i Hi. apply UN1; [lia | intros Hw; exact (HAPL i ltac:(lia) (sc6_wr_sub c _ Hw))].
  - split; [unfold LMAX; lia|]. left. split; [|apply Forall_nil].
    exists lst, (12 * Z.of_nat (length ids) + 1). split; [exact HLin | lia]. }
assert (HTAIL : atail_vis SEGS Wc mA (lst + Z.of_nat (length (dec_list ids)))).
{ apply (cmd_heap_tail_vis lyc Sc Wc mA mdvA lst (12 * Z.of_nat (length ids) + 1));
  [exact HARa | exact HLin | lia]. }
assert (HMOKa : mo_ok MT Sc (XM_XSTRDUP MT (dec_list ids))).
{ apply (mok_station MT S Sc (XM_SUP_CHAIN MT R id ids) XMc (XM_XSTRDUP MT (dec_list ids)) MTL HMOK HMLE);
  lia. }
assert (P10' : getr rgA 10 = w64 lst) by (rewrite P10; exact E20).
rewrite (proj1 sc6_sig).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc rgA mA _ SUP_CHAIN_STK sp0 (sc6_FP O) ly S W mem md [] lyc Sc mdvA kc
    XSTRDUP_STK [] EV_XSTRDUP (-112) (getr rgA 1) [] _ HJ).
  - unfold spZ. rewrite P2, Usp. lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite P3, E3. exact H3.
  - rewrite P4, E4. exact H4.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite P8, Uc. lia.
  - intros HPRE1. eapply SRr_mono.
    + exact (TXSTRDUP fx lyc Sc Wc rgA mA mdvA [] lst (dec_list ids) HPRE1 HRODa P10'
        (or_introl HARGs) HTAIL ltac:(destruct HEVn as (EV1 & EV2 & EV3); lia) HLIVEx HMOKa).
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2).
      exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
      split; [exact HP2 | exact HK2].
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3). rewrite P1.
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc3 | exact HJ3 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia |].
    intros a Ha Hf. exact (inFP_nil a Hf).
  - apply (sc6_region_kept_slot E Wc W3 mA mem3 c _ _ _ _ _ Uc).
    + intros a Ha. apply (sc6_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3
        (sink_closed_pos [] (Forall_nil _))
        (sc6_slot_in c a Hc ltac:(unfold CALL_SIZE; lia)) (inFP_nil a)).
    + intros a Ha. apply (cmd_prog_writable ly3 S3 W3 mem3 md3 a (proj1 HJc3)). apply sc6_in_PG.
      apply (sc6_slot_in c); [exact Hc | unfold CALL_SIZE; lia].
  - apply (sc6_region_kept_slot E Wc W3 mA mem3 c _ _ _ _ _ Uc).
    + intros a Ha. apply (sc6_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3
        (sink_closed_pos [] (Forall_nil _))
        (sc6_slot_in c a Hc ltac:(unfold CALL_SIZE; lia)) (inFP_nil a)).
    + intros a Ha. apply (cmd_prog_writable ly3 S3 W3 mem3 md3 a (proj1 HJc3)). apply sc6_in_PG.
      apply (sc6_slot_in c); [exact Hc | unfold CALL_SIZE; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 48 (map (getr regs3) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 48)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (Ea48 : forall j, (j < length CLOB)%nat -> ew Ea (48 + j) = nth j (map (getr regs3) CLOB) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HEa. unfold havoc. cbn [ew].
  replace (48 + j <? 48)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (48 + j - 48)%nat with j by lia. apply nth_indep. rewrite length_map. exact Hj. }
clear HEa.
destruct HK3 as (pb & Hpb10 & [Hpb4096 Hpb64] & Hperm3 & Hfresh3 & Hpbblk & Hstrb & Hstrl & Hbb3 & HMLE3).
pose proof (proj1 HJc3) as HAR3.
assert (Hpbin : In (pb, LIVE_XSTRDUP (dec_list ids)) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm3)); left; reflexivity).
assert (HinSc3 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym Hperm3)); right; exact Hpn).
assert (HpbSc : ~ In (pb, LIVE_XSTRDUP (dec_list ids)) (ablocks B lyc Sc)).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) Hfresh3 _ Hin) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart, LIVE_XSTRDUP in Hap. lia. }
assert (Uc' : bv_unsigned (ew Ea 8) = c) by (rewrite OLDa by lia; exact Uc).
assert (U22' : bv_unsigned (ew Ea 22) = SB) by (rewrite OLDa by lia; exact U22).
assert (SHOKa : sh_ok SEGS sc6_Bx sc6_SH Ea (mrestrict (w_H W3) mem3)).
{ unfold sh_ok, sc6_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W3) mem3 Ea sc6_Bx 8%nat c CALL_SIZE c 0 CALL_SIZE).
  - exact (sc6_slot_addressable ly3 S3 W3 mem3 md3 c HAR3 Hc).
  - unfold sc6_Bx, U. cbn [sv_denot]. rewrite U22'. unfold SHADOW_OFF, SB. reflexivity.
  - unfold U. cbn [sv_denot]. rewrite Uc', Z.add_0_r. apply unsigned_lit_small. lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by (unfold CALL_SIZE; lia).
    clear - Hx Hc1 Hc2. unfold SHADOW_OFF, A_G_REC, A_REC_SPILL, OFF_CALLS, SC_SIZE, CALL_SIZE in *. lia. }
(* --- 0x8c454 .. 0x8c48c: the second check, c->nargs := 3, c->args[2] := the copy, a0 := list ---------- *)
paj_run_tok RUN HS HJ3 SHOKa sc6_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 8%nat) (b := c);
  [ reflexivity | exact Uc'
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply sc6_awr_rec;
    apply (sc6_slot_in c); [exact Hc | unfold CALL_SIZE; lia]
  | ].
  eapply awr_ok_cons_gen with (n := 8%nat) (b := c);
  [ reflexivity | exact Uc'
  | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply sc6_awr_rec;
    apply (sc6_slot_in c); [exact Hc | unfold CALL_SIZE; lia]
  | apply awr_ok_nil ]. }
try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
  set (mdv2 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv2 end).
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgB := rg) in *; set (mB := mm) in *; set (mdvB := mdq) in * end.
clearbody mdvB.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let rn := eval vm_compute in (nth 1 (ss_mem ssx) sc6_slotN) in
  let ra := eval vm_compute in (nth 2 (ss_mem ssx) sc6_slotA) in
  pose proof (st_ok_pi_region_nth Ex ssx msx 1 rn HS ltac:(vm_compute; reflexivity)) as HRgN;
  pose proof (st_ok_pi_region_nth Ex ssx msx 2 ra HS ltac:(vm_compute; reflexivity)) as HRgA
| st_ok _ ?Ex ?ssx ?msx =>
  let rn := eval vm_compute in (nth 1 (ss_mem ssx) sc6_slotN) in
  let ra := eval vm_compute in (nth 2 (ss_mem ssx) sc6_slotA) in
  pose proof (st_ok_region_nth Ex ssx msx 1 rn HS ltac:(vm_compute; reflexivity)) as HRgN;
  pose proof (st_ok_region_nth Ex ssx msx 2 ra HS ltac:(vm_compute; reflexivity)) as HRgA
end.
cbn [ms_mem restrict mkst] in HRgN, HRgA.
assert (Hpbden : sv_denot Ea (SOff 52 0) = Z_to_bv 64 pb).
{ cbn [sv_denot]. change 52%nat with (48 + 4)%nat. rewrite (Ea48 4%nat ltac:(cbv; lia)).
  cbn [CLOB map nth]. rewrite Hpb10. unfold w64.
  rewrite Z.add_0_r, unsigned_lit_small by
    (destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 pb (LIVE_XSTRDUP (dec_list ids)) HAR3 Hpbin)
       as (_ & _ & Hb & _); lia).
  reflexivity. }
pose proof (field_of_region Ea _ 8%nat c _ _ _ _ _ 4 4 (SLit 3) 3 HRgN Uc'
  ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vna.
pose proof (field_of_region Ea _ 8%nat c _ _ _ _ _ 24 8 (SOff 52 0) pb HRgA Uc'
  ltac:(cbn; tauto) Hpbden
  ltac:(destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 pb (LIVE_XSTRDUP (dec_list ids)) HAR3 Hpbin)
          as (_ & _ & Hb & _); cbn; lia) ltac:(cbn; lia)) as Vap.
clear HRgN HRgA.
pose proof (kept_of_frame (segs := SEGS) Ea _ (w_H W3) mem3 mB (sc6_wr c) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uc' in Hrr;
       try (rewrite OLDa in Hrr by lia); rewrite ?Usp in Hrr;
       unfold sc6_wr; first [left; lia | right; lia]|]);
    destruct Hin)) as UN2.
clear HF HFr HG.
pose proof (proj1 HJ3) as HAR3b.
(* the recorder after the third argument *)
assert (HREP2 : rec_repA B ly3 S3 (rdW W3 mB)
   (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids])
   (O1 ++ [(pb, LIVE_XSTRDUP (dec_list ids))])).
{ rewrite <- HR2.
  apply (scA_push_arg B lyc Sc ly3 S3 (rdW Wc memc) (rdW W3 mB) R1 O1 kk e1 c (dec_list ids) pb HREP1 HT).
  - rewrite Hsnd. cbn [length]. lia.
  - exact HinSc3.
  - intros a Ha Hn1 Hn2.
    assert (Ha64 : 0 <= a < 2 ^ 64)
      by (unfold sc6_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
    assert (Hout : ~ sc6_wr c a).
    { unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hn1, Hn2. rewrite Hsnd in Hn2. cbn [length] in Hn2.
      intros [Hbad | Hbad]; [apply Hn1 | apply Hn2]; lia. }
    rewrite (UN2 a Ha64 Hout).
    rewrite (sc6_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3
      (sink_closed_pos [] (Forall_nil _)) Ha (inFP_nil a)).
    exact (UN1 a Ha64 Hout).
  - intros q k i Hq Hi.
    assert (HqSc : In (q, k) (ablocks B lyc Sc)) by exact (sc6_repA_blocks lyc Sc _ R1 O1 HREP1 (q, k) Hq).
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q k HARc HqSc) as (_ & Hq4096 & Hqc & _ & _ & _ & Hqn).
    pose proof (req_size_pos k ltac:(lia)) as [RQ1 RQ2].
    assert (Hqi : 0 <= q + i < 2 ^ 64) by lia.
    assert (Hout : ~ sc6_wr c (q + i)).
    { destruct (sc6_blk_apart lyc Sc Wc memc mdc q k HARc HqSc) as [Aq1 Aq2].
      unfold iv_apart in Aq1, Aq2. intros Hw; apply sc6_wr_sub in Hw.
      destruct Hc as [(ii & Hii & Hce) | Hce]; rewrite Hce in *;
        unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia. }
    rewrite (UN2 _ Hqi Hout).
    rewrite (sc6_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q k i HJc3 HARa
      (fun a Ha => False_ind _ (inFP_nil a Ha)) HqSc (HinSc3 _ HqSc) ltac:(lia)).
    exact (UN1 _ Hqi Hout).
  - rewrite Hsnd. cbn [length]. apply (aval_mem_view SEGS). exact Vna.
  - rewrite Hsnd. cbn [length]. change (8 * Z.of_nat 2) with 16.
    apply (aval_mem_view SEGS). unfold CALL_OFF_ARGS. replace (c + 8 + 16) with (c + 24) by lia. exact Vap.
  - apply (sc3_str_keep (rdW W3 mem3)); [exact Hstrb|].
    intros i Hi.
    destruct (al_blocks _ _ LAWS ly3 S3 W3 mB mdvB pb (LIVE_XSTRDUP (dec_list ids)) HAR3b Hpbin)
      as (_ & Hb1 & Hb2 & _).
    pose proof (req_size_pos (LIVE_XSTRDUP (dec_list ids)) ltac:(unfold LIVE_XSTRDUP; lia)) as [RX1 RX2].
    apply UN2; [unfold LIVE_XSTRDUP in *; lia|].
    destruct (sc6_blk_apart ly3 S3 W3 mB mdvB pb (LIVE_XSTRDUP (dec_list ids)) HAR3b Hpbin) as [Ab1 Ab2].
    unfold iv_apart, LIVE_XSTRDUP in Ab1, Ab2. intros Hw; apply sc6_wr_sub in Hw.
    destruct Hc as [(ii & Hii & Hce) | Hce]; rewrite Hce in *;
      unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
  - unfold LMAX. lia.
  - lia.
  - unfold LIVE_XSTRDUP in Hpbin. exact Hpbin.
  - exact (proj1 (sc6_blk_apart ly3 S3 W3 mB mdvB pb _ HAR3b Hpbin)).
  - exact (proj2 (sc6_blk_apart ly3 S3 W3 mB mdvB pb _ HAR3b Hpbin)).
  - intros Hq. apply in_map_iff in Hq as ([q k] & Hqe & Hq). cbn [fst] in Hqe. subst q.
    assert (HqSc : In (pb, k) (ablocks B lyc Sc)) by exact (sc6_repA_blocks lyc Sc _ R1 O1 HREP1 (pb, k) Hq).
    rewrite <- (sc6_same_start ly3 S3 W3 mB mdvB (pb, LIVE_XSTRDUP (dec_list ids)) (pb, k)
      HAR3b Hpbin (HinSc3 _ HqSc) eq_refl) in HqSc.
    exact (HpbSc HqSc). }
set (R2 := rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids]) in *.
set (O2 := O1 ++ [(pb, LIVE_XSTRDUP (dec_list ids))]) in *.
set (Lb := (lst, 12 * Z.of_nat (length ids) + 1)) in *.
(* --- 0x8c48c: wrapper_free(list) ---------------------------------------------------------------------- *)
assert (Q10' : getr rgB 10 = w64 lst) by (rewrite Q10, OLDa by lia; exact E20).
assert (HLin3 : In Lb (ablocks B ly3 S3)) by exact (HinSc3 _ HLin).
pose proof HJ3 as (_ & _ & _ & _ & _ & Hfr3 & Hnev3 & _).
assert (HmS3 : mo_le MT S S3 (XMc + XM_XSTRDUP MT (dec_list ids))) by exact (mle_station MT S Sc S3 _ _ MTL HMLE HMLE3).
assert (HMOKf : mo_ok MT S3 (mo_free MT)).
{ apply (mok_station MT S S3 (XM_SUP_CHAIN MT R id ids) _ (mo_free MT) MTL HMOK HmS3); lia. }
rewrite (pal_free B TL).
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx) W3 rgB mB SUP_CHAIN_STK sp0 (sc6_FP O) ly S W mem md
    [] ly3 S3 mdvB (kc + EV_XSTRDUP) lst (12 * Z.of_nat (length ids) + 1) (-112) (getr rgB 1) [] HJ3 HLin3 Q10').
  - unfold spZ. rewrite Q2, OLDa by lia. rewrite Usp. lia.
  - reflexivity.
  - lia.
  - lia.
  - rewrite Q3, OLDa, E3 by lia. exact H3.
  - rewrite Q4, OLDa, E4 by lia. exact H4.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - destruct HEVn as (EV1 & EV2 & EV3). lia.
  - apply (achain_chain_pre ly3 (rdW W3 mB) (spZ rgB) (s0Z rgB) [] rgB).
    + apply achain_low. unfold s0Z. rewrite Q8, OLDa, Uc by lia. lia.
    + unfold spZ. rewrite Q2, OLDa by lia. rewrite Usp. lia.
    + reflexivity.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - intros HLb i Hi. destruct (inFP_ablocks_fp O lst (12 * Z.of_nat (length ids) + 1) i (HL0 HLb) Hi)
      as (r & Hr & Hb). exists r. split; [right; right; exact Hr | exact Hb].
  - exact HMOKf. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (lb1 & lb2 & Ebl1 & Ebl2) &
  Hfr4 & HK4 & HMLE4 & HJc4). rewrite Q1.
jafter_call_keep_pi HS 72%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc4 | exact HJ4 | rewrite OLDa by lia; exact Usp | lia | lia | lia | cbn; lia | cbn; lia |].
  intros a Ha Hf. destruct (inFP_ablocks_fp_inv _ a Hf) as (p' & n' & Hpn & Hr).
  destruct Hpn as [Hpn | []]. injection Hpn as <- <-. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc Ea 72 (map (getr regs4) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 72)%nat -> ew Eb m = ew Ea m)
  by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
clear HEb.
pose proof (proj1 HJc4) as HAR4.
destruct HK4 as (K41 & K42 & K43 & K44).
(* the list block is gone, and nothing the recorder owns was it *)
assert (HLn4 : ~ In Lb (ablocks B ly4 S4)).
{ rewrite Ebl2. intros Hin.
  apply in_app_or in Hin as [Hin | Hin].
  - apply in_split in Hin as (u & v & Euv). rewrite Euv in Ebl1.
    pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mB mdvB Lb Lb u v lb2 HAR3b
      ltac:(rewrite Ebl1, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng, Lb in Hd. cbn [fst snd] in Hd. lia.
  - apply in_split in Hin as (u & v & Euv). rewrite Euv in Ebl1.
    pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mB mdvB Lb Lb lb1 u v HAR3b Ebl1) as Hd.
    unfold zdisjoint, block_rng, Lb in Hd. cbn [fst snd] in Hd. lia. }
assert (HOnotL : forall pn, In pn O2 -> pn <> Lb).
{ intros pn Hpn Heq. subst pn. unfold O2 in Hpn. apply in_app_or in Hpn as [Hpn | [Hpn | []]].
  - exact (HLnO1 Hpn).
  - unfold Lb in Hpn. injection Hpn as Hpe Hne.
    pose proof (proj1 (Forall_forall _ _) Hfresh3 _ HLin) as Hap. unfold Lb in Hap. cbn [fst snd] in Hap.
    unfold iv_apart, LIVE_XSTRDUP in Hap, Hne. lia. }
assert (HblkO2 : forall pn, In pn O2 -> In pn (ablocks B ly4 S4) /\
  forall i, 0 <= i < snd pn -> rdW W4 mem4 (fst pn + i) = rdW W3 mB (fst pn + i)).
{ intros pn Hpn.
  assert (Hpn3 : In pn (ablocks B ly3 S3)) by exact (sc6_repA_blocks ly3 S3 _ _ _ HREP2 pn Hpn).
  assert (Hne : pn <> Lb) by exact (HOnotL pn Hpn).
  split.
  - rewrite Ebl2. rewrite Ebl1 in Hpn3. apply in_app_or in Hpn3 as [H | [H | H]].
    + apply in_or_app. left. exact H.
    + exfalso. exact (Hne (eq_sym H)).
    + apply in_or_app. right. exact H.
  - intros i Hi. destruct pn as [q k]. cbn [fst snd] in Hi |- *.
    destruct (al_blocks _ _ LAWS ly3 S3 W3 mB mdvB q k HAR3b Hpn3) as (_ & _ & _ & _ & _ & _ & Hk0).
    pose proof (req_size_pos k ltac:(lia)) as [Rk1 Rk2].
    apply (K42 q k i Hpn3 ltac:(lia)). intros Hbad. cbv beta in Hbad.
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 mB mdvB q k lst (12 * Z.of_nat (length ids) + 1)
      HAR3b Hpn3 HLin3 Hne) as Hd.
    pose proof (req_size_pos (12 * Z.of_nat (length ids) + 1) ltac:(lia)) as [Rl1 Rl2].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HREP3 : rec_repA B ly4 S4 (rdW W4 mem4) R2 O2).
{ apply (sc6_repA_keep ly3 S3 (rdW W3 mB) ly4 S4 (rdW W4 mem4) _ _ HREP2).
  - intros a Ha. destruct (sc6_rec_unowned a Ha) as [Ho He].
    apply K43; [apply cmd_prog_img; apply sc6_in_PG; exact Ha | exact Ho | exact He].
  - exact HblkO2. }
(* --- 0x8c490 .. 0x8c49c: a0 := "chain" (0x21f20), a1 := 5, the call of rec_shape_of ------------------- *)
assert (SHOKb : sh_ok SEGS sc6_Bx [] Eb (mrestrict (w_H W4) mem4)) by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN HS HJ4 SHOKb sc6_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
  set (mdv3 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv3 end).
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
prreg HS (11%bv : bv 5) T11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgC := rg) in *; set (mC := mm) in *; set (mdvC := mdq) in * end.
clearbody mdvC.
pose proof (kept_of_frame (segs := SEGS) Eb _ (w_H W4) mem4 mC (fun _ => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
    destruct Hin)) as UN3.
clear HF HFr HG.
pose proof (proj1 HJ4) as HAR4b.
pose proof HJ4 as (_ & _ & _ & _ & _ & Hfr4' & Hnev4 & _).
pose proof (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4
  (sc6_ro_off ly S W mem md O HAR HOS) HROD) as HROD4.
pose proof (cmd_ro_ok_of_aro ly4 S4 W4 mC mdvC HAR4b HROD4) as HRO4.
assert (HLIT : abytes_atR (rdW W4 mC) 0x21f20 RO_lit_21f20).
{ clear - HRO4. destruct HRO4 as [HRO4 _]. unfold cmd_ro_bytes in HRO4.
  repeat match type of HRO4 with
  | abytes_atR _ 0x21f20 _ /\ _ => exact (proj1 HRO4)
  | _ /\ _ => apply proj2 in HRO4
  end. }
assert (HVERB : Z.of_nat (length sc6_verb) <= 16 ->
  abytes_atR (rdW W4 mC) 0x21f20 sc6_verb /\
  (in_blockA (ablocks B ly4 S4) 0x21f20 (Z.of_nat (length sc6_verb)) \/
   astr_argA B ly4 S4 (rdW W4 mC) (in_roP SEGS RLO RHI) [] 0x21f20 (Some sc6_verb))).
{ intros _. split.
  - apply (sc6_abytes_prefix _ _ _ [Z_to_bv 8 0]). rewrite sc6_verb_ro. exact HLIT.
  - right. exact (sc6_verb_argA ly4 S4 _ HLIT). }
assert (T10' : getr rgC 10 = w64 0x21f20).
{ rewrite T10. change 313%nat with SC_VERB.
  rewrite (img_env_atomP Eb SC_VERB HEIb ltac:(unfold SC_VERB, A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite sc6_verb_val. reflexivity. }
assert (T11' : getr rgC 11 = w64 (Z.of_nat (length sc6_verb))) by (rewrite T11, sc6_verb_len; reflexivity).
rewrite (proj1 (proj2 sc6_sig)).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W4 rgC mC _ SUP_CHAIN_STK sp0 (sc6_FP O) ly S W mem md [] ly4 S4 mdvC
    (kc + EV_XSTRDUP + 1) REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-112) (getr rgC 1) [] _ HJ4).
  - unfold spZ. rewrite T2, OLDb, OLDa by lia. rewrite Usp. lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite T3, OLDb, OLDa, E3 by lia. exact H3.
  - rewrite T4, OLDb, OLDa, E4 by lia. exact H4.
  - reflexivity.
  - rewrite T1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite T1, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite T8, OLDb, OLDa, Uc by lia. lia.
  - intros HPRE2. eapply SRr_mono.
    + exact (TREC_SHAPE_OF fx ly4 S4 W4 rgC mC mdvC 0x21f20 sc6_verb (afn_pre_na_of _ _ _ _ _ _ _ _ _ _ HPRE2)
        HROD4 T10' ltac:(lia) T11' ltac:(rewrite sc6_verb_len; lia) HRO4 VOBJS HVERB
        ltac:(destruct HEVn as (EV1 & EV2 & EV3); lia)).
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2).
      exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2 | exact HK2].
  - intros a Ha. exfalso. exact (inFP_nil a Ha).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HK5). rewrite T1.
jafter_call_keep_pi HS 96%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0]%nat HS5.
match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc5 | exact HJ5 | rewrite OLDb, OLDa by lia; exact Usp | lia | lia | lia | cbn; lia | cbn; lia |].
  intros a Ha Hf. exact (inFP_nil a Hf). }
clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
remember (havoc Eb 96 (map (getr regs5) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
assert (OLDc : forall m, (m < 96)%nat -> ew Ec m = ew Eb m)
  by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
assert (Ec96 : forall j, (j < length CLOB)%nat -> ew Ec (96 + j) = nth j (map (getr regs5) CLOB) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HEc. unfold havoc. cbn [ew].
  replace (96 + j <? 96)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (96 + j - 96)%nat with j by lia. apply nth_indep. rewrite length_map. exact Hj. }
clear HEc.
assert (OLD : forall m, (m < 48)%nat -> ew Ec m = ew E m)
  by (intros m Hm; rewrite OLDc, OLDb, OLDa by lia; reflexivity).
destruct HK5 as ((q & Hq10 & Hq64 & HqA) & Hperm5 & Ely5 & ES5).
pose proof (proj1 HJc5) as HAR5.
(* --- 0x8c4a0 .. 0x8c4e4: a2 := 1, a1 := the shape, a0 := c, the frame restored, the tail jump ------------ *)
assert (SHOKc : sh_ok SEGS sc6_Bx [] Ec (mrestrict (w_H W5) mem5)) by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN HS HJ5 SHOKc sc6_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
try (lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m0) ?mat ?m1] =>
  set (mdv4 := with_vm_backing (m_vm_lazy m0) mat m1) in *; clearbody mdv4 end).
pmkst HS.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (9%bv : bv 5) U9. prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11.
prreg HS (12%bv : bv 5) U12. prreg HS (18%bv : bv 5) U18.
prreg HS (19%bv : bv 5) U19. prreg HS (20%bv : bv 5) U20. prreg HS (21%bv : bv 5) U21. prreg HS (22%bv : bv 5) U22r.
prreg HS (23%bv : bv 5) U23. prreg HS (24%bv : bv 5) U24. prreg HS (25%bv : bv 5) U25. prreg HS (26%bv : bv 5) U26.
prreg HS (27%bv : bv 5) U27.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgT := rg) in *; set (mT := mm) in *; set (mdvT := mdq) in * end.
clearbody mdvT.
pose proof (kept_of_frame (segs := SEGS) Ec _ (w_H W5) mem5 mT (fun _ => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia|]);
    destruct Hin)) as UN4.
clear HF HFr HG.
pose proof (proj1 HJ5) as HART.
pose proof HJ5 as (_ & HlyT & _ & _ & _ & HfrT & HnevT & _).
(* the registers at the tail jump: the entry's ra, sp, gp, tp and callee-saved ones, c, the shape, 1 *)
assert (Rr : forall r : bv 5, forall m (rz : Z), Z.of_nat m = 32 + Z.of_nat (length (firstn 0 sc6_saved)) ->
  True) by (intros; exact I).
clear Rr.
assert (R1' : getr rgT 1 = getr regs 1).
{ rewrite U1, OLD by lia. rewrite X0. f_equal; try (apply bv_eq; reflexivity). }
assert (Rsp : spZ rgT = sp0).
{ unfold spZ. rewrite U2, OLD by lia. rewrite Usp. rewrite unsigned_lit_small by lia. lia. }
assert (R3 : getr rgT 3 = getr regs 3) by (rewrite U3, OLD, E3, H3 by lia; exact (eq_sym Hgp)).
assert (R4 : getr rgT 4 = getr regs 4) by (rewrite U4, OLD, E4, H4 by lia; exact (eq_sym Htp)).
assert (R8 : getr rgT 8 = getr regs 8) by (rewrite U8, OLD, X1 by lia; f_equal; apply bv_eq; reflexivity).
assert (R10 : getr rgT 10 = w64 c) by (rewrite U10, OLD by lia; exact E8).
assert (R11 : getr rgT 11 = w64 q).
{ rewrite U11. change 100%nat with (96 + 4)%nat. rewrite (Ec96 4%nat ltac:(cbv; lia)). exact Hq10. }
assert (Rhi : forall r, acallee_saved r -> getr rgT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  - apply bv_eq. change (bv_unsigned (getr rgT (Z_to_bv 5 2)) = bv_unsigned (getr regs (Z_to_bv 5 2))).
    replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    fold (spZ rgT) (spZ regs). rewrite Rsp. reflexivity.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact R3.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact R4.
  - rewrite <- X1. replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U8, OLD by lia. reflexivity.
  - rewrite <- X2. replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U9, OLD by lia. reflexivity.
  - rewrite <- X3. replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U18, OLD by lia. reflexivity.
  - rewrite <- X4. replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U19, OLD by lia. reflexivity.
  - rewrite <- X5. replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U20, OLD by lia. reflexivity.
  - rewrite <- X6. replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U21, OLD by lia. reflexivity.
  - rewrite <- X7. replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U22r, OLD by lia. reflexivity.
  - rewrite <- X8. replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U23, OLD by lia. reflexivity.
  - rewrite <- X9. replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U24, OLD by lia. reflexivity.
  - rewrite <- X10. replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U25, OLD by lia. reflexivity.
  - rewrite <- X11. replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U26, OLD by lia. reflexivity.
  - rewrite <- X12. replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite U27, OLD by lia. reflexivity. }
assert (HPT : aregs_preserved regs rgT) by (intros r Hr; exact (Rhi r Hr)).
(* the recorder at answer's entry: rec_shape_of and the epilogue wrote nothing it owns *)
assert (HREP4 : rec_repA B ly5 S5 (rdW W5 mT) R2 O2).
{ apply (sc6_repA_keep ly4 S4 (rdW W4 mem4) ly5 S5 (rdW W5 mT) _ _ HREP3).
  - intros a Ha. assert (Ha64 : 0 <= a < 2 ^ 64)
      by (unfold sc6_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
    rewrite (UN4 a Ha64 (fun z => z)).
    rewrite (sc6_rec_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc5 (sink_closed_pos [] (Forall_nil _)) Ha (inFP_nil a)).
    exact (UN3 a Ha64 (fun z => z)).
  - intros pn Hpn. pose proof (sc6_repA_blocks ly4 S4 _ _ _ HREP3 pn Hpn) as Hpn4.
    assert (Hpn5 : In pn (ablocks B ly5 S5)) by exact (Permutation_in _ (Permutation_sym Hperm5) Hpn4).
    split; [exact Hpn5|]. intros i Hi. destruct pn as [q' k']. cbn [fst snd] in Hi |- *.
    destruct (al_blocks _ _ LAWS ly4 S4 W4 mC mdvC q' k' HAR4b Hpn4) as (_ & Hq4 & Hqc & _ & _ & _ & Hqk).
    pose proof (req_size_pos k' ltac:(lia)) as [Rq1 Rq2].
    assert (Hqi : 0 <= q' + i < 2 ^ 64) by lia.
    rewrite (UN4 _ Hqi (fun z => z)).
    rewrite (sc6_blk_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q' k' i HJc5 HAR4b
      (fun a Ha => False_ind _ (inFP_nil a Ha)) Hpn4 Hpn5 Hi).
    exact (UN3 _ Hqi (fun z => z)). }
destruct (sc6_repA_answer ly5 S5 _ _ _ HREP4) as (old & Hold & Holdc).
set (x := shape_of sc6_verb) in *.
set (e := (REC_CHAIN, [dec id; dec (Z.of_nat (length ids)); dec_list ids])).
assert (Hsm : sup_chain_m R id ids = rec_answer R2 e x true) by reflexivity.
assert (Ht : snd (rec_answer R2 e x true) = snd (sup_chain_m R id ids)) by (rewrite Hsm; reflexivity).
assert (HSH : r_refuse R2 = 0 -> astr_argA B ly5 S5 (rdW W5 mT) (in_roP SEGS RLO RHI) O2 q (Some x) /\ fits x).
{ intros _. split; [|exact sc6_fits].
  apply (sc6_argA_keep ly5 S5 W5 mT mdvT (rdW W5 mem5)); [exact HART | exact (HqA O2) |].
  intros a Ha. exact (UN4 a Ha (fun z => z)). }
assert (HSLOT : r_refuse R2 = 0 -> true = true ->
  (exists k, nth_error (r_calls R2) k = Some e /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (c = A_REC_SPILL /\ e = r_spill R2)).
{ intros _ _. rewrite <- HR2. destruct kk as [i|]; destruct HT as [HT1 HT2].
  - left. exists i. split; [|exact HT2]. unfold sc_push_arg, set_calls. cbn [r_calls].
    rewrite sc_upd_nth_eq, HT1. cbn [option_map]. destruct e1 as [f1 a1]. cbn [fst snd] in Hfn, Hsnd |- *.
    rewrite Hfn, Hsnd. reflexivity.
  - right. split; [exact HT2|]. unfold sc_push_arg, set_spill. cbn [r_spill]. rewrite <- HT1.
    destruct e1 as [f1 a1]. cbn [fst snd] in Hfn, Hsnd |- *. rewrite Hfn, Hsnd. reflexivity. }
assert (Hchg : true = negb (bv_unsigned (getr rgT 12) =? 0)) by (rewrite U12; reflexivity).
assert (HFRT : Z.of_nat (length (frames S5)) <= 8) by (rewrite HfrT, <- HfrC; exact HFRc).
assert (HEVT : st_nev S5 + EV_ANSWER <= EV_MAX) by (destruct HEVn as (EV1 & EV2 & EV3); lia).
assert (Hbb5 : blocks_bytes S5 + (12 * Z.of_nat (length ids) + 1) = blocks_bytes Sc + LIVE_XSTRDUP (dec_list ids)).
{ rewrite (blocks_bytes_bsum B ly5 S5), (blocks_bytes_bsum B lyc Sc).
  rewrite (bsum_perm _ _ Hperm5). rewrite Ebl2.
  assert (Hb3 : bsum (ablocks B ly3 S3) = LIVE_XSTRDUP (dec_list ids) + bsum (ablocks B lyc Sc))
    by (rewrite (bsum_perm _ _ Hperm3), bsum_cons; reflexivity).
  rewrite Ebl1, bsum_app, bsum_cons in Hb3. rewrite bsum_app. unfold Lb in Hb3. cbn [snd] in Hb3. lia. }
assert (HLIVET : blocks_bytes S5 + LIVE_ANSWER (snd (rec_answer R2 e x true)) <= LIVE_MAX)
  by (rewrite Ht; unfold LIVE_SUP_CHAIN in HLIVE; lia).
assert (Hm45 : mo_le MT S4 S5 0) by (rewrite ES5; exact (mle_start MT S4 MTL)).
pose proof (mle_station MT S S3 S4 _ _ MTL HmS3 HMLE4) as HmS4.
pose proof (mle_station MT S S4 S5 _ _ MTL HmS4 Hm45) as HmS5.
assert (HMOKT : mo_ok MT S5 (XM_ANSWER MT (snd (rec_answer R2 e x true)))).
{ rewrite Ht. apply (mok_station MT S S5 (XM_SUP_CHAIN MT R id ids) _ _ MTL HMOK HmS5); lia. }
pose proof (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5
  (sc6_ro_off ly S W mem md O HAR HOS) HROD) as HRODT.
pose proof (cmd_ro_ok_of_aro ly5 S5 W5 mT mdvT HART HRODT) as HROT.
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Holdc as [-> | ([a k] & Hpn' & Eo')]; [lia|]. cbn [fst] in Eo'. subst old.
  destruct (al_blocks _ _ LAWS ly5 S5 W5 mT mdvT a k HART (sc6_repA_blocks ly5 S5 _ _ _ HREP4 _ Hpn'))
    as (_ & Ha4096 & Hac & _ & _ & _ & Hk0).
  pose proof (req_size_pos k ltac:(lia)) as [Rk1 Rk2]. lia. }
(* the tail jump: answer runs at this function's entry sp and returns to sup_chain's caller, at some fx1 with
   fxrel fx fx1 (answer reaches the snprintf wrapper: PaFx.v's F rule) *)
rewrite (proj2 (proj2 sc6_sig)).
eapply SRr_mono.
{ eapply (cl_callS_wideF (fx := fx) B LAWS W5 rgT mT _ SUP_CHAIN_STK sp0 (sc6_FP O) ly S W mem md [] ly5 S5 mdvT
    (kc + EV_XSTRDUP + 1 + EV_REC_SHAPE_OF) ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER 0 (getr rgT 1) ch _ HJ5).
  - rewrite Rsp. lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - reflexivity.
  - rewrite R1'. exact Hra.
  - rewrite R1'. exact Hra4.
  - rewrite Z.add_0_r. unfold s0Z. rewrite R8. fold (s0Z regs).
    pose proof HlyT as (_ & _ & _ & _ & _ & _ & _ & _ & EtopT & _).
    apply (achain_ly_top ly ly5 _ _ _ _ EtopT).
    apply (achain_kept ly (rdW W mem) (rdW W5 mT) sp0 (s0Z regs) ch sp0 Hch); [lia | lia |].
    intros a Ha. pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    apply F1; [lia | lia |].
    intros (r & Hr & Hra'). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra'.
    + unfold A_G_REC, REC_SIZE in Hra'. lia.
    + unfold A_REC_SPILL, SC_SIZE in Hra'. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb' nb'] & <- & Hin). cbn [fst snd] in Hra'.
      destruct (al_blocks _ _ LAWS ly S W mem md pb' nb' HAR (HOS _ Hin)) as (_ & _ & Hbc & _). lia.
  - intros HPRE3. eapply SRr_mono.
    + exact (TANSWER fx ly5 S5 W5 rgT mT mdvT ch c q old e x true R2 O2
        HPRE3 HRM0 HFRT HRODT HROT R10 ltac:(lia) R11 Hq64 Hchg HREP4 Hold Hold64 HSH HSLOT HEVT HLIVET HMOKT).
    + cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ2 & HP2 & HK2).
      exists fx2, ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
      split; [exact HJ2|]. split; [exact HP2 | exact HK2].
  - intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + apply sc6_awr_rec. left. unfold A_G_REC, OFF_ANSWER, REC_SIZE in *. lia.
    + apply sc6_awr_rec. left. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb' nb'] & <- & Hin). cbn [fst snd] in Ha.
      apply sc6_filter_in in Hin.
      assert (HinT : In (pb', nb') (ablocks B ly5 S5)) by exact (sc6_repA_blocks ly5 S5 _ _ _ HREP4 _ Hin).
      destruct (in_dec recb_pair_dec (pb', nb') O) as [HO | HnO].
      * right; left. split.
        -- exists (pb', pb' + req_size nb'). split; [|cbn [fst snd]; exact Ha].
           right; right. apply in_map_iff. exists (pb', nb'). split; [reflexivity | exact HO].
        -- exists pb', nb'. split; [exact HinT | exact Ha].
      * right; right; left. exists pb', nb'. split; [exact HinT|]. split; [|exact Ha].
        intros H0. unfold O2 in Hin. apply in_app_or in Hin as [Hin | [Hin | []]].
        -- destruct (HO1 _ Hin) as [HO' | HnI]; [exact (HnO HO') | exact (HnI H0)].
        -- rewrite <- Hin in H0, HnO. exact (HpbSc (HB2 _ H0 HnO)).
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & Ha) Hw _. exfalso.
    destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + unfold A_G_REC, OFF_ANSWER in Ha. lia.
    + unfold A_G_REC, OFF_STATE in Ha. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb' nb'] & <- & Hin). cbn [fst snd] in Ha.
      apply sc6_filter_in in Hin.
      pose proof (sc6_repA_blocks ly5 S5 _ _ _ HREP4 _ Hin) as HinT.
      destruct (al_blocks _ _ LAWS ly5 S5 W5 mT mdvT pb' nb' HART HinT) as (_ & _ & Hbc & _). lia. }
(* --- sup_chain's post, from answer's: answer returned at fx1 with fxrel fx fx1 ------------------------- *)
cbv beta. intros W6 c6 _ (fx1 & ly6 & S6 & regs6 & mem6 & md6 & Hfx & -> & HJ6 & HJc6 & HP6 & HK6).
destruct HK6 as (p1 & p2 & O' & HK6). cbv zeta in HK6.
destruct HK6 as (Hp2r & Hp2b & H12 & HG1 & Hbl6 & HREP6 & HO'iff & Hstr6 & Hbb6 & HMLE6).
set (t := snd (rec_answer R2 e x true)) in *.
set (n := Z.of_nat (length t) + 1) in *.
pose proof (proj1 HJ6) as HAR6.
rewrite R1'.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly6 S6).
{ exact Hfx. }
{ eapply (ajournal_mono_k SEGS B); [exact HJ6|]. destruct HEVn as (EV1 & EV2 & EV3). lia. }
{ exact (aregs_preserved_trans _ _ _ HPT HP6). }
(* block bookkeeping: the entry (bl0), the segment's entry (blc), after xstrdup (bl3), after the free (bl4),
   at answer's entry (bl5) and at the end (bl6) *)
assert (Hb3 : forall pn, In pn (ablocks B ly3 S3) <-> pn = (pb, LIVE_XSTRDUP (dec_list ids)) \/ In pn (ablocks B lyc Sc)).
{ intros pn. split; intros Hpn.
  - apply (Permutation_in _ Hperm3) in Hpn. destruct Hpn as [<- | Hpn]; [left; reflexivity | right; exact Hpn].
  - apply (Permutation_in _ (Permutation_sym Hperm3)). destruct Hpn as [-> | Hpn]; [left; reflexivity | right; exact Hpn]. }
assert (Hb45 : forall pn, In pn (ablocks B ly5 S5) <-> In pn (ablocks B ly4 S4)).
{ intros pn. split; intros Hpn; [exact (Permutation_in _ Hperm5 Hpn) | exact (Permutation_in _ (Permutation_sym Hperm5) Hpn)]. }
assert (Hb4a : forall pn, In pn (ablocks B ly4 S4) -> In pn (ablocks B ly3 S3)).
{ intros pn Hpn. rewrite Ebl2 in Hpn. rewrite Ebl1. apply in_app_or in Hpn as [Hpn | Hpn];
  apply in_or_app; [left; exact Hpn | right; right; exact Hpn]. }
assert (Hb4b : forall pn, In pn (ablocks B ly3 S3) -> pn <> Lb -> In pn (ablocks B ly4 S4)).
{ intros pn Hpn Hne. rewrite Ebl1 in Hpn. rewrite Ebl2. apply in_app_or in Hpn as [Hpn | [Hpn | Hpn]].
  - apply in_or_app. left. exact Hpn.
  - exfalso. exact (Hne (eq_sym Hpn)).
  - apply in_or_app. right. exact Hpn. }
assert (HpbO2 : In (pb, LIVE_XSTRDUP (dec_list ids)) O2) by (unfold O2; apply in_or_app; right; left; reflexivity).
assert (HO1O2 : forall pn, In pn O1 -> In pn O2) by (intros pn Hpn; unfold O2; apply in_or_app; left; exact Hpn).
assert (HO2_5 : forall pn, In pn O2 -> In pn (ablocks B ly5 S5)) by exact (sc6_repA_blocks ly5 S5 _ _ _ HREP4).
assert (Hold5 : forall pn, In pn (ablocks B ly5 S5) -> fst pn = old -> In pn O2).
{ intros pn Hpn Eo. destruct Holdc as [Eold | (pn' & Hpn' & Eo')].
  - destruct pn as [a k]. destruct (al_blocks _ _ LAWS ly5 S5 W5 mT mdvT a k HART Hpn) as (_ & H4096 & _).
    cbn [fst] in Eo. lia.
  - assert (Hpn'5 : In pn' (ablocks B ly5 S5)) by exact (HO2_5 _ Hpn').
    rewrite (sc6_same_start ly5 S5 W5 mT mdvT pn pn' HART Hpn Hpn'5 ltac:(congruence)). exact Hpn'. }
(* a block of the entry that is not the recorder's is still live at answer's entry *)
assert (Hsurv : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly5 S5)).
{ intros pn H0 HnO. apply Hb45. apply Hb4b.
  - apply Hb3. right. exact (HB2 _ H0 HnO).
  - intros ->. exact (HnO (HL0 H0)). }
(* such a block does not start at the old answer: the recorder owned that one *)
assert (Hsold : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> fst pn <> old).
{ intros pn H0 HnO Eo. pose proof (Hold5 pn (Hsurv pn H0 HnO) Eo) as Hin.
  unfold O2 in Hin. apply in_app_or in Hin as [Hin | [Hin | []]].
  - destruct (HO1 _ Hin) as [HO' | HnI]; [exact (HnO HO') | exact (HnI H0)].
  - rewrite <- Hin in H0, HnO. exact (HpbSc (HB2 _ H0 HnO)). }
(* so neither of answer's two fresh blocks is one of them *)
assert (Hfresh : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (p1, n) /\ pn <> (p2, n))
  by (intros pn H0 HnO; exact (HG1 pn (Hsurv pn H0 HnO) (Hsold pn H0 HnO))).
unfold sc6_Q. exists (fst (rec_answer R2 e x true)), t, p2, O'.
split; [rewrite Hsm; exact (surjective_pairing _)|].
split; [exact Hp2r|]. split; [exact Hp2b|]. split; [exact HREP6|].
split.
{ intros pn Hpn. apply HO'iff in Hpn as [(Hin & _) | ->].
  - unfold O2 in Hin. apply in_app_or in Hin as [Hin | [Hin | []]].
    + exact (HO1 _ Hin).
    + rewrite <- Hin. destruct (in_dec recb_pair_dec (pb, LIVE_XSTRDUP (dec_list ids)) O) as [HO | HnO];
        [left; exact HO | right; intros H0; exact (HpbSc (HB2 _ H0 HnO))].
  - destruct (in_dec recb_pair_dec (p1, n) (ablocks B ly S)) as [H0 | Hn0]; [|right; exact Hn0].
    destruct (in_dec recb_pair_dec (p1, n) O) as [HO | HnO]; [left; exact HO|].
    exfalso. exact (proj1 (Hfresh _ H0 HnO) eq_refl). }
split; [apply Hbl6; right; right; reflexivity|].
split; [intros pn H0 HnO; exact (proj2 (Hfresh pn H0 HnO))|].
split.
{ intros Hq. apply in_map_iff in Hq as (pn & Ep & Hpn).
  assert (Hpn6 : In pn (ablocks B ly6 S6)) by exact (sc6_repA_blocks ly6 S6 _ _ _ HREP6 _ Hpn).
  assert (Hp26 : In (p2, n) (ablocks B ly6 S6)) by (apply Hbl6; right; right; reflexivity).
  rewrite (sc6_same_start ly6 S6 W6 mem6 md6 pn (p2, n) HAR6 Hpn6 Hp26 Ep) in Hpn.
  apply HO'iff in Hpn as [(Hin & Hno) | E12].
  - exact (proj2 (HG1 _ (HO2_5 _ Hin) Hno) eq_refl).
  - injection E12 as E12. exact (H12 (eq_sym E12)). }
split; [exact Hstr6|].
split.
{ intros pn H0 HnO. pose proof (Hsurv pn H0 HnO) as Hpn5.
  assert (Hpn6 : In pn (ablocks B ly6 S6))
    by (apply Hbl6; left; split; [exact Hpn5 | exact (Hsold pn H0 HnO)]).
  split; [exact Hpn6|].
  assert (Hne : pn <> (p2, n)) by exact (proj2 (Hfresh pn H0 HnO)).
  destruct pn as [a k].
  pose proof (sep_blocks SEGS B LAWS ly6 S6 W6 mem6 md6 a k p2 n HAR6 Hpn6
    ltac:(apply Hbl6; right; right; reflexivity) Hne) as Hd.
  destruct (al_blocks _ _ LAWS ly6 S6 W6 mem6 md6 a k HAR6 Hpn6) as (_ & _ & _ & _ & _ & _ & Hk).
  destruct (al_blocks _ _ LAWS ly6 S6 W6 mem6 md6 p2 n HAR6 ltac:(apply Hbl6; right; right; reflexivity))
    as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos k ltac:(lia)) as [_ Rk]. pose proof (req_size_pos n ltac:(lia)) as [_ Rn].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd |- *. unfold iv_apart. lia. }
split.
{ intros pn Hpn. apply Hbl6 in Hpn as [(Hpn5 & Hne) | [-> | ->]].
  - assert (Hpn4 : In pn (ablocks B ly4 S4)) by exact (proj1 (Hb45 pn) Hpn5).
    assert (HnL : pn <> Lb) by (intros ->; exact (HLn4 Hpn4)).
    apply Hb4a, Hb3 in Hpn4 as [-> | Hpnc].
    + right; left. apply HO'iff. left. split; [exact HpbO2 | exact Hne].
    + destruct (HB1 _ Hpnc) as [H0 | [HinO1 | HeqL]].
      * destruct (in_dec recb_pair_dec pn O) as [HO | HnO].
        -- right; left. apply HO'iff. left. split; [|exact Hne].
           destruct (HO2 _ HO Hpnc) as [HinO1 | HeqL];
             [exact (HO1O2 _ HinO1) | exfalso; exact (HnL HeqL)].
        -- left. split; [exact H0 | exact HnO].
      * right; left. apply HO'iff. left. split; [exact (HO1O2 _ HinO1) | exact Hne].
      * exfalso. exact (HnL HeqL).
  - right; left. apply HO'iff. right. reflexivity.
  - right; right. reflexivity. }
split.
{ try rewrite Ht in Hbb6. unfold LIVE_SUP_CHAIN. lia. }
pose proof (mle_station MT S S5 S6 _ _ MTL HmS5 HMLE6) as HmS6.
apply (mle_weaken MT S S6 _ _ MTL HmS6). rewrite Ht in *. lia.
Qed.

End e.
End f.
End d.
