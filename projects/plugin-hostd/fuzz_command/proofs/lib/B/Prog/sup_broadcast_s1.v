(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of the sup_broadcast walk on the ASan+UBSan build of plugin-hostd/fuzz_command
   (fuzz_command.asan-ubsan, 0x8b4f0, 19 instructions), made from a Theorem Labs lane's A walk (lib/A/Prog/sup_broadcast_s1.v at
   a5a5ff08765, a working branch): the return points of the two calls, the walk's footprint and
   post-condition, and two facts the A kit carried under local names: HPROG (every byte of g_rec, record.spill and
   g_quitting is one of the record's program statics, over B's ts_prog, lib/B/YF0m.v:4874, :4899) and
   sb_blocks_nodup (the live blocks start at distinct addresses, from AR's al_sep). B keeps record() as a function
   (lib/B/Prog/record_c.v), so the A kit's shadow facts for the inline store checks are record's and stay out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_line_c answer_c sup_broadcast_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* offsets in the listing (from its base, CmdList.v): the return points of the calls of record (`jal` at 0x8b508)
   and arg_line (`jal` at 0x8b514) *)
Definition SBB_RET_REC : Z := AF_sup_broadcast + 0x1c.
Definition SBB_RET_AL : Z := AF_sup_broadcast + 0x28.
(* the listing's atom of the shape "resp 0" (0x21d20, RO_lit_21d20), slot 5115 `PAddHi a1 a0 145 (A_OBJ 42) 0` *)
Definition SBB_SHAPE : nat := A_OBJ 42.
Definition SBB_SHAPE_ADDR : Z := 0x21d20.

(* blocks with pairwise disjoint byte ranges and non-negative sizes start at distinct addresses *)
Lemma sbb_pairwise_nodup : forall (l : list (Z * Z)),
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> (forall b, In b l -> 0 <= snd b) ->
List.NoDup (map fst l).
Proof.
induction l as [|[b m] t IH]; intros Hp Hpos; [constructor|].
cbn [map pairwise] in Hp. destruct Hp as [Hf Ht]. cbn [map]. constructor.
- intros Hin. apply in_map_iff in Hin as ([b' m'] & Eb & Hin'). cbn in Eb. subst b'.
  pose proof (proj1 (Forall_forall _ _) Hf (b, req_size m')
    (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) t (b, m') Hin')) as Hd.
  pose proof (req_size_pos m (Hpos (b, m) (or_introl eq_refl))) as [Hr1 _].
  pose proof (req_size_pos m' (Hpos (b, m') (or_intror Hin'))) as [Hr2 _].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- apply IH; [exact Ht | intros b0 Hb0; apply Hpos; right; exact Hb0].
Qed.

(* the footprint of the statement (sup_broadcast_c.v:106-107) *)
Definition sb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* a slot record() returns (rec_slot, record_c.v:57-60): its bytes are program statics *)
Definition sb_slot (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.
Lemma sb_slot_pg : forall c a, sb_slot c -> c <= a < c + CALL_SIZE -> inFP cmd_PG a.
Proof.
intros c a [(i & Hi & ->) | ->] Ha.
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|]. cbn [fst snd].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity|]. cbn [fst snd].
  unfold CALL_SIZE in Ha. lia.
Qed.
Lemma sb_slot_fp : forall c a O, sb_slot c -> c <= a < c + 16 -> inFP (sb_FP O) a.
Proof.
intros c a O [(i & Hi & ->) | ->] Ha; unfold sb_FP.
- apply inFP_cons; right. apply inFP_cons; left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_CALLS_MAX in *. lia.
- do 3 (apply inFP_cons; right). apply inFP_cons; left. unfold SC_SIZE. lia.
Qed.
Lemma sb_slot_range : forall c, sb_slot c -> A_G_REC + 16 <= c <= A_REC_SPILL.
Proof. intros c [(i & Hi & ->) | ->]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX, A_REC_SPILL in *; lia. Qed.
Lemma sbb_bsum_nonneg : forall l : list (Z * Z), (forall b, In b l -> 0 <= snd b) -> 0 <= bsum l.
Proof.
induction l as [|b l IH]; intros H; [cbn; lia|]. rewrite bsum_cons.
pose proof (H b (or_introl eq_refl)). pose proof (IH (fun b' Hb' => H b' (or_intror Hb'))). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.

(* every byte of g_rec, record.spill and g_quitting is one of the program's statics (RULING-STMT's HPROG, from
   CmdBSyms' ts_prog) *)
Lemma HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hin & Hr). rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* the live blocks start at distinct addresses (AR's separation, al_sep) *)
Lemma sb_blocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
List.NoDup (map fst (ablocks B ly S)).
Proof.
intros ly S W mem md HAR. destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _].
apply pairwise_app_l in Hp as [Hp _]. apply sbb_pairwise_nodup; [exact Hp|].
intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia.
Qed.

(* every byte of the statement's footprint lies below the allocator's ceiling *)
Lemma sb_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (sb_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO Ha. pose proof asan_consts as (C1 & _).
unfold sb_FP in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_NCALLS in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_CALLS, OFF_ANSWER in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_STATE in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|].
destruct (inFP_ablocks_fp_inv O a Ha) as (b & m & Hin & Hr).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR (HO _ Hin)) as (_ & _ & Hc & _). lia.
Qed.

(* the post-condition of tsup_broadcast_spec (sup_broadcast_c.v:109-128), as a function of the entry state *)
Definition sb_post (ly : alayout) (S : astate) (R : rstate) (line : list byte) (O : list (Z * Z)) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
let t := snd (sup_broadcast_m R line) in
exists R' O' q,
 sup_broadcast_m R line = (R', t) /\
 let n := Z.of_nat (length t) + 1 in
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn (ablocks B ly S) -> In pn O) /\
 (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, n)) /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly' S')) /\
 In (q, n) (ablocks B ly' S') /\ (In (q, n) (ablocks B ly S) -> In (q, n) O) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_BROADCAST line t /\
 mo_le MT S S' (XM_SUP_BROADCAST MT R line t).

End e.
End f.
End d.
