(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_worker_list on plugin-hostd/fuzz_command.asan, after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (the segment walk of cgif_close) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-10: the walk restated after an earlier version of lib/A/Prog/sup_instance_info.v
   (the ASan walk of sup_instance_info on an earlier version of the statements, after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v and A/ACke.v): the same two segments, without arg_i. *)
(* Modified by Theorem Labs, 2026-10: re-fitted to the statements of passes 4, 4b and 5 (apost_baseF, the rounding-mode
   pre, fx-generic callee contracts, no astack_pres) after lib/A/Prog/sup_remove_all_refit_s3.v (the tail call into
   answer through cl_callS_wideF, closed by apost_baseF_intro). *)

(* sup_worker_list (recorder.c:390-393, entry 0x8b4f0, 58 instructions): an inlined record(8) with no argument, then
   rec_shape_of(.str.6 "worker_list", 11) and the tail jump answer(c, shape, 0). Segment A (the entry and record()'s
   two arms) and segment B (from the join 0x8b554 on) are lib/A/Prog/sup_worker_list_s1.v's seeds; the recorder's
   steps are lib/A/Prog/sup_worker_list_s2.v. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
xstrdup_c hand_back_c rec_calls_free_c rec_shape_of_c answer_c sup_worker_list_c RecBLemmas
sup_worker_list_s1 sup_worker_list_s2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* record() of a call with no argument leaves the recorder's blocks as they were *)
Lemma swl_lay_slot0 : forall Q,
lay_blocks (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)) = lay_blocks Q.
Proof.
intros Q. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite concat_app. cbn [concat].
rewrite !app_nil_r. reflexivity.
Qed.

Lemma swl_lay_spill0 : forall Q, l_spill Q = [] ->
lay_blocks (RLay (l_calls Q) [] (l_answer Q) (l_reply Q)) = lay_blocks Q.
Proof. intros Q H0. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply]. rewrite H0. reflexivity. Qed.

(* after a symbolic run the model term grows (2026-10-28): name it *)
Ltac swl_md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.

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
(* the statement's Section hypotheses (sup_worker_list_c.v:66-69), word for word *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses (cgif's names) *)
Hypothesis TL : PALib B.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the named facts the recorder walks carry, each in its canonical form, where the statement does not give them
   (CmdRecFacts.v's lemmas once it lands) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md ->
Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
(* the premise the statement pass dropped (CmdRo.v:434): rec_shape_of's read-only arm of the verb
   literal asks in_roP of its bytes *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* the footprint of the statement *)
Definition swl_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* the statement's post (sup_worker_list_c.v:87-106), word for word *)
Definition swl_post (ly : alayout) (S : astate) (R : rstate) (O : list (Z * Z))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_worker_list_m R = (R', t) /\
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
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_WORKER_LIST R /\
 mo_le MT S S' (XM_SUP_WORKER_LIST MT R).

(* the recorder's step that the walk from SWL_JOIN completes: the slot c holds fn = 8 and no argument, everything
   else of g_rec / record.spill and of the recorder's blocks as at SWL_JOIN *)
Definition swl_jw (rdJ : reader) (R : rstate) (c : Z) (QJ : rlay) : Prop :=
forall bl2 (rd2 : reader),
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> ~ (c <= a < c + 8) -> rd2 a = rdJ a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> ~ (c <= a < c + 8) -> rd2 a = rdJ a) ->
aval_mem rd2 (c + CALL_OFF_FN) 4 REC_WORKER_LIST -> aval_mem rd2 (c + CALL_OFF_NARGS) 4 0 ->
(forall pn, In pn (lay_blocks QJ) -> In pn bl2) ->
(forall pn i, In pn (lay_blocks QJ) -> 0 <= i < snd pn -> rd2 (fst pn + i) = rdJ (fst pn + i)) ->
arep_at bl2 rd2 A_G_REC A_REC_SPILL (rec_record R REC_WORKER_LIST []) QJ.

Ltac swl_in_syms := cbn [cmd_prog_syms In]; repeat first [left; reflexivity | right].
Lemma swl_sig_rcf : SIG CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. rewrite (SIGP CS_rec_calls_free ltac:(swl_in_syms)). reflexivity. Qed.
Lemma swl_sig_shp : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite (SIGP CS_rec_shape_of ltac:(swl_in_syms)). reflexivity. Qed.
Lemma swl_sig_ans : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer ltac:(swl_in_syms)). reflexivity. Qed.

(* the read-only bytes keep the image's values along the walk: none is in the statement's footprint *)
Lemma swl_rodata_at : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k R O,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (swl_FP O) ly S W mem md own ly' S' W' mem' md' k ->
rec_repA B ly S (rdW W mem) R O ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k R O HAR HJ HREP HR.
apply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B STK sp0 (swl_FP O) ly S W mem md own ly' S' W' mem' md' k HJ); [|exact HR].
intros a Hro HF. destruct (cmd_ro_prog_apart a Hro) as [Himg Hnpg].
unfold swl_FP in HF. apply inFP_cons in HF as [Ha | HF].
{ apply Hnpg. apply Exists_exists. exists (A_G_REC, REC_SIZE). split; [left; reflexivity | unfold in_zr; cbn [fst snd]; lia]. }
apply inFP_cons in HF as [Ha | HF].
{ apply Hnpg. apply Exists_exists. exists (A_REC_SPILL, SC_SIZE). split; [right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia]. }
destruct (inFP_ablocks_fp_inv O a HF) as (p & n & Hpn & Hr).
pose proof (swl_rec_repA_in B ly S _ R O HREP (p, n) Hpn) as Hin.
destruct (al_client_img _ _ LAWS ly S W mem md a HAR) as [_ Hni].
{ left. exists p, n. split; [exact Hin | exact Hr]. }
exact (Hni Himg).
Qed.

Lemma swl_achain_ly : forall ly ly' rd sp v ch, achain ly rd sp v ch -> ly_top ly' = ly_top ly -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch H E. unfold achain in *. rewrite E. exact H. Qed.

(* two live blocks that start at the same address are the same block *)
Lemma swl_same_start : forall ly S (W : world SEGS) mem md pn pn', AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In pn' (ablocks B ly S) -> fst pn = fst pn' -> pn = pn'.
Proof.
intros ly S W mem md [p n] [p' n'] HAR H1 H2 E. cbn [fst] in E. subst p'.
destruct (recb_pair_dec (p, n) (p, n')) as [|Hne]; [assumption|]. exfalso.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p n p n' HAR H1 H2 Hne) as D.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR H1) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n' HAR H2) as (_ & _ & _ & _ & _ & _ & Hn').
pose proof (req_size_pos n ltac:(lia)). pose proof (req_size_pos n' ltac:(lia)).
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma swl_blocks_apart : forall ly S (W : world SEGS) mem md pn pn', AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In pn' (ablocks B ly S) -> pn <> pn' -> iv_apart (fst pn) (snd pn) (fst pn') (snd pn').
Proof.
intros ly S W mem md [p n] [p' n'] HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md p n p' n' HAR H1 H2 Hne) as D.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR H1) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p' n' HAR H2) as (_ & _ & _ & _ & _ & _ & Hn').
pose proof (req_size_pos n ltac:(lia)). pose proof (req_size_pos n' ltac:(lia)).
unfold zdisjoint in D. unfold iv_apart. cbn [fst snd] in *. lia.
Qed.

Lemma swl_aanswer_ptr : forall bl rd gr t q, aanswer_at bl rd gr t q -> aval_mem rd (gr + OFF_ANSWER) 8 (oaddr q).
Proof. intros bl rd gr t q H. unfold aanswer_at in H. destruct t, q; cbn [oaddr]; try contradiction; [exact (proj1 H) | exact H]. Qed.

(* answer's footprint names the recorder's blocks that start at the old answer (stdpp's filter) *)
Lemma swl_in_filter_old : forall (old : Z) (O : list (Z * Z)) x,
In x (filter (fun pn : Z * Z => fst pn =? old) O) -> In x O /\ fst x = old.
Proof.
intros old O x. induction O as [|y O IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd|Hd] in H.
- destruct H as [-> | H].
  + split; [left; reflexivity|]. revert Hd. destruct (Z.eqb_spec (fst x) old) as [Ex|Ex]; [intros _; exact Ex|].
    intros Hd; exfalso; first [discriminate Hd | exact Hd | inversion Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

(* the slot record() picks in g_rec's table, as the listing computes it (0x8b538 .. 0x8b550) *)
Lemma swl_slot_word : forall n, 0 <= n < 16 ->
alu64 ALU_ADD (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 n) (Z_to_bv 64 56)) (Z_to_bv 64 16)) (Z_to_bv 64 A_G_REC) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros n Hn.
assert (Hc : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15) by lia.
repeat (destruct Hc as [-> | Hc]); [..| subst n]; apply bv_eq; vm_compute; reflexivity.
Qed.

Lemma swl_nodup_app_r : forall {X : Type} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros X l1. induction l1 as [|x l1 IH]; intros l2 H; [exact H|].
cbn in H. apply List.NoDup_cons_iff in H as [_ H]. exact (IH l2 H).
Qed.

(* a byte of a live block: above the null page, below the allocator's ceiling (so below every stack frame), not an image byte *)
Lemma swl_blk_byte : forall ly S (W : world SEGS) mem md p n i, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> 0 <= i < n -> 4096 <= p + i /\ p + i < alloc_ceiling /\ ~ in_img SEGS (p + i).
Proof.
intros ly S W mem md p n i HAR Hin Hi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & H4 & Hc & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
split; [lia|]. split; [lia|].
destruct (al_client_img _ _ LAWS _ _ _ _ _ (p + i) HAR) as [_ Hni]; [left; exists p, n; split; [exact Hin | lia] | exact Hni].
Qed.

Lemma swl_bsum_nonneg : forall l, (forall pn, In pn l -> 0 <= snd pn) -> 0 <= bsum l.
Proof.
intros l. induction l as [|x l IH]; intros H; [cbn; lia|].
rewrite bsum_cons. pose proof (H x (or_introl eq_refl)). pose proof (IH (fun pn Hp => H pn (or_intror Hp))). lia.
Qed.

(* the statement's footprint lies below the allocator's ceiling, so below every stack byte *)
Lemma swl_FP_low : forall ly S (W : world SEGS) mem md rd R O, AR SEGS B ly S W mem md -> rec_repA B ly S rd R O ->
forall a, inFP (swl_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md rd R O HAR HREP a Ha. pose proof asan_consts as (C1 & _).
unfold swl_FP in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, REC_SIZE in Ha; lia|].
apply inFP_cons in Ha as [Ha | Ha]; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|].
destruct (inFP_ablocks_fp_inv O a Ha) as (b & m & Hbm & Hba).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (swl_rec_repA_in B ly S _ R O HREP (b, m) Hbm)) as (_ & _ & Hbc & _). lia.
Qed.

Lemma swl_not_in_zr : forall lo hi l, forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) l = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) l.
Proof.
intros lo hi l Hb a Ha Hex. apply Exists_exists in Hex as (r & Hr & Hin). rewrite forallb_forall in Hb.
pose proof (Hb r Hr) as Hr'. apply orb_true_iff in Hr' as [H | H]; apply Z.leb_le in H; unfold in_zr in Hin; lia.
Qed.

Lemma swl_in_Z : forall (x : Z) l, existsb (Z.eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & E). apply Z.eqb_eq in E. subst. exact Hy. Qed.

(* a string argument stays one when its bytes keep their values *)
Lemma swl_astr_argA_rd : forall ly S (rd rd' : reader) ro O p x, astr_argA B ly S rd ro O p (Some x) ->
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly S rd' ro O p (Some x).
Proof.
intros ly S rd rd' ro O p x H Hk. cbv beta iota zeta delta [astr_argA] in H |- *.
destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [|split; [exact H3 | exact H4]].
apply (swl_astr_kept rd); [exact H2 | exact Hk].
Qed.

(* ---------- segment B: from the join of record()'s two arms (0x8b554) to the end ---------- *)
Lemma swl_join : forall ly S W (regs : bvmap 5 word) mem md ch (R : rstate) (O : list (Z * Z))
  lyc Sc Wc (regs1 : bvmap 5 word) memc mdc (k c : Z) (F O1 : list (Z * Z)) (QJ : rlay),
afn_pre SEGS B SUP_WORKER_LIST_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
cmd_ro_ok (rdW W mem) ->
rec_repA B ly S (rdW W mem) R O ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_WORKER_LIST R <= EV_MAX -> blocks_bytes S + LIVE_SUP_WORKER_LIST R <= LIVE_MAX ->
mo_ok MT S (XM_SUP_WORKER_LIST MT R) ->
ajournal SEGS B SUP_WORKER_LIST_STK (spZ regs) (swl_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
k <= rec_spill_frees R ->
mo_le MT S Sc (rec_spill_frees R * mo_free MT) ->
blocks_bytes Sc <= blocks_bytes S ->
swl_frame SEGS (mrestrict (w_H Wc) memc) (spZ regs - SWL_FRAME) regs ->
bv_unsigned (getr regs1 2) = spZ regs - SWL_FRAME -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
getr regs1 8 = Z_to_bv 64 c -> getr regs1 9 = Z_to_bv 64 SB ->
(forall r, 18 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
swl_slot_ok c ->
(forall pn, In pn (ablocks B lyc Sc) <-> In pn (ablocks B ly S) /\ ~ In pn F) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
(forall pn, In pn F -> In pn O /\ (16 <= length (r_calls R))%nat) ->
(forall pn, In pn (lay_blocks QJ) <-> In pn O1) ->
(forall q, l_answer QJ = Some q -> In q O1) ->
swl_jw (rdW Wc memc) R c QJ ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SWL_JOIN)) memc (seg_rom SEGS)) mdc)
(apost_baseF SEGS B SUP_WORKER_LIST_STK (swl_FP O) regs ly S W mem md (EV_SUP_WORKER_LIST R) (swl_post ly S R O)).
Proof.
intros ly S W regs mem md ch R O lyc Sc Wc regs1 memc mdc k c F O1 QJ
  HPRE HFRM HROD HRO HREP Hfr8 Hev Hlive MOK HJ Hk MLE Hbb HFR Rsp Rgp Rtp R8 R9 Rhi Hc
  JB1 JB2 JB3 JO JA2 JW.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FS : SUP_WORKER_LIST_STK = 16592) by (vm_compute; reflexivity).
set (sp0 := spZ regs) in *.
pose proof (swl_FP_low ly S W mem md _ R O HAR0 HREP) as HFPlow.
pose proof (proj1 HJ) as HARc.
pose proof HFR as (F24 & F16 & F8).
destruct (swl_seedB B LAWS HB cmd_prog_writable lyc Sc Wc memc mdc regs1 (swl_frvals regs) (sp0 - SWL_FRAME) c HARc Rsp
  ltac:(unfold SWL_FRAME; lia) ltac:(unfold SWL_FRAME; rewrite Zminus_mod, Hal16; reflexivity) R8 Hc R9 eq_refl F24 F16 F8) as [HS SHOK].
set (E := swl_EB regs1 (swl_frvals regs)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold swl_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = getr regs 1) by (subst E; unfold swl_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (X33 : ew E 33 = getr regs 8) by (subst E; unfold swl_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (X34 : ew E 34 = getr regs 9) by (subst E; unfold swl_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E8 : ew E 8 = Z_to_bv 64 c) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 SB) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (Usp : bv_unsigned (ew E 2) = sp0 - SWL_FRAME) by (rewrite (EEo 2%nat 2%bv eq_refl); exact Rsp).
destruct (swl_slot_bounds c Hc) as (Hcb & Hc8 & Hcs).
assert (U8 : bv_unsigned (ew E 8) = c) by (rewrite E8; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
(* 0x8b554 .. 0x8b590: the two checked stores of the slot, the verb literal, then the call of rec_shape_of *)
paj_run_tok RUN HS HJ SHOK swl_Bspan.
{ unfold ss_swlB, swl_rsB, swl_frameB, swl_slotB. cbn [ss_mem].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 8%nat); [reflexivity | exact U8 | | apply (awr_ok_nil SEGS B)].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; right; right; left.
  split; [|split; [rewrite (recb_ts_prog_m B HB); apply (swl_in_PG c); [exact Hc | unfold CALL_SIZE; lia]
                  | apply cmd_prog_img; apply (swl_in_PG c); [exact Hc | unfold CALL_SIZE; lia]]].
  unfold swl_FP. apply inFP_cons. destruct Hcs as [Hcs | ->]; [left; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_SIZE in *; lia|].
  right. apply inFP_cons. left. unfold SC_SIZE. lia. }
pmkst HS. try swl_md.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
(* the slot after the two stores (fn = 8, nargs = 0), every other byte as at SWL_JOIN *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 1 (ss_mem ssx) swl_slotB) in
  pose proof (st_ok_region_nth (segs := SEGS) _ ssx (restrict _ msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRs;
  cbn [ms_mem restrict mkst] in HRs end.
pose proof (aval_mem_view SEGS (w_H Wc) (ms_mem ms) (c + 0) 4%nat 8
  (field_of_region E _ 8 c _ _ _ _ _ 0 4 (SLit 8) 8 HRs U8 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))) as Vfn.
pose proof (aval_mem_view SEGS (w_H Wc) (ms_mem ms) (c + 4) 4%nat 0
  (field_of_region E _ 8 c _ _ _ _ _ 4 4 (SLit 0) 0 HRs U8 ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia))) as Vna.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun a => c <= a < c + 8) HFr).
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U8 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ) as HARa.
assert (HspT : spZ (ms_regs ms) = sp0 + -32) by (unfold spZ at 1; rewrite P2, Usp; unfold SWL_FRAME; lia).
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl), Rgp; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl), Rtp; exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 0x21d80).
{ rewrite P10. apply bv_eq. change 303%nat with (A_OBJ 62).
  rewrite (HEI (A_OBJ 62) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), (swl_lit_val VOBJS). cbv [w64]. rewrite unsigned_lit_small; lia. }
assert (P11' : getr (ms_regs ms) 11 = w64 (Z.of_nat (length swl_verb))) by (rewrite P11; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
(* the budgets *)
assert (EVN : EV_ANSWER = 3) by reflexivity.
assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
assert (RSF0 : 0 <= rec_spill_frees R) by (unfold rec_spill_frees; destruct (Nat.ltb _ _); lia).
unfold EV_SUP_WORKER_LIST in Hev. unfold LIVE_SUP_WORKER_LIST in Hlive. unfold XM_SUP_WORKER_LIST in MOK.
pose proof HJ as (_ & _ & _ & _ & _ & HfrSc & HnevSc & _).
assert (HRODa : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms))) by exact (swl_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HJ HREP HROD).
assert (HROa : cmd_ro_ok (rdW Wc (ms_mem ms))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARa HRODa).
(* the verb: the literal .str.6, a read-only string the record's checks accept *)
assert (HLIT : abytes_atR (rdW Wc (ms_mem ms)) 0x21d80 RO_lit_21d80).
{ clear - HROa. destruct HROa as [HROa _]. unfold cmd_ro_bytes in HROa.
  repeat match type of HROa with
  | abytes_atR _ 0x21d80 _ /\ _ => exact (proj1 HROa)
  | _ /\ _ => apply proj2 in HROa
  end. }
assert (HROI : forall i, 0 <= i < 12 -> in_roP SEGS RLO RHI (0x21d80 + i)).
{ pose proof CMD_RO_IN as HROIN. clear - HROIN. unfold cmd_ro_in in HROIN.
  repeat match type of HROIN with
  | (forall i, 0 <= i < _ -> _ (0x21d80 + i)) /\ _ => exact (proj1 HROIN)
  | _ /\ _ => apply proj2 in HROIN
  end. }
assert (HUNOWN : forall i, 0 <= i < 12 ->
  ~ Exists (in_zr (0x21d80 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21d80 + i < as_errno B + 4)).
{ intros i Hi. rewrite (AF0m.ts_owned B HB), (AF0m.ts_errno B HB). split.
  - apply (swl_not_in_zr 0x21d80 (0x21d80 + 12)); [vm_compute; reflexivity | lia].
  - cbv [AF0m.TFIB_ERRNO]. lia. }
assert (Hno0 : ~ In (Z_to_bv 8 0) swl_verb).
{ unfold swl_verb. cbn [map]. intros Hin.
  repeat (destruct Hin as [Hin | Hin]; [apply (f_equal bv_unsigned) in Hin; vm_compute in Hin; discriminate Hin|]).
  exact Hin. }
assert (HVERB : Z.of_nat (length swl_verb) <= 16 ->
  abytes_atR (rdW Wc (ms_mem ms)) 0x21d80 swl_verb /\
  (in_blockA (ablocks B lyc Sc) 0x21d80 (Z.of_nat (length swl_verb)) \/
   astr_argA B lyc Sc (rdW Wc (ms_mem ms)) (in_roP SEGS RLO RHI) [] 0x21d80 (Some swl_verb))).
{ intros _. split.
  - apply (swl_abytes_prefix _ _ _ [Z_to_bv 8 0]). rewrite swl_verb_lit. exact HLIT.
  - right. cbv beta iota zeta delta [astr_argA]. change (Z.of_nat (length swl_verb)) with 11.
    split; [lia|]. split; [split; [rewrite swl_verb_lit; exact HLIT | exact Hno0]|]. split; [unfold LMAX; lia|].
    right. split; [intros i Hi; split; [apply HROI; lia | apply HUNOWN; lia]|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. apply swl_in_Z. vm_compute. reflexivity. }
assert (HEV3 : st_nev Sc + EV_REC_SHAPE_OF <= EV_MAX) by (unfold EV_REC_SHAPE_OF; lia).
(* 0x8b590: rec_shape_of(.str.6, 11) *)
rewrite swl_sig_shp.
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS Wc (ms_regs ms) (ms_mem ms) _ SUP_WORKER_LIST_STK sp0 (swl_FP O) ly S W mem md [] lyc Sc _
    k REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-32) (getr (ms_regs ms) 1) _ HJ HspT eq_refl ltac:(lia)
    ltac:(vm_compute; discriminate) ltac:(rewrite FS; vm_compute; discriminate) P3' P4' eq_refl HraT Hra4T).
  - intros HPRE3. exact (TREC_SHAPE_OF fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ 0x21d80 swl_verb HPRE3 HRODa P10' ltac:(lia)
      P11' ltac:(rewrite swl_verb_len; lia) HROa VOBJS HVERB HEV3).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as ((q & Hq10 & Hq0 & HqARG) & HPerm3 & Ely3 & ES3).
rewrite P1.
(* back at 0x8b594: the frame is kept, the rest of the state is the callee's *)
jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc3 | exact HJ3 | exact Usp | unfold SWL_FRAME; lia | rewrite FS; unfold SWL_FRAME; lia
  | unfold SWL_FRAME; cbn; lia | cbn; lia | cbn; lia |].
  intros a Ha HFa. exact (inFP_nil a HFa). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs3) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD4 : forall m, (m < 40)%nat -> ew E4 m = ew E m) by (intros m Hm; rewrite HE4; apply YN3v.ew_havoc_old; exact Hm).
assert (A44 : ew E4 44 = getr regs3 10) by (rewrite HE4; reflexivity).
clear HE4.
pose proof (proj1 HJ3) as HAR3.
assert (SHOK4 : sh_ok SEGS swl_BxB swl_SHB E4 (mrestrict (w_H W3) mem3)).
{ apply (swl_sh_okB B LAWS HB ly3 S3 W3 mem3 md3 E4 c HAR3 Hc).
  - rewrite OLD4 by lia. exact E9.
  - rewrite OLD4 by lia. exact E8. }
(* 0x8b594 .. 0x8b5b0: the epilogue and the tail jump to answer(c, shape, 0) *)
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
paj_run_tok RUN HS HJ3 SHOK4 swl_Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
pmkst HS. try swl_md.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12.
(* the registers at answer's entry: the entry's ra, sp, s0, s1, s2 .. s11; a0 = c, a1 = the shape, a2 = 0 *)
assert (Esp4 : bv_unsigned (ew E4 2) = sp0 - SWL_FRAME) by (rewrite OLD4 by lia; exact Usp).
assert (T1' : getr (ms_regs ms) 1 = getr regs 1) by (rewrite T1, OLD4, X32 by lia; reflexivity).
assert (T2' : getr (ms_regs ms) 2 = getr regs 2).
{ rewrite T2, Esp4. unfold SWL_FRAME. replace (sp0 - 32 + 32) with sp0 by lia. unfold sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (T3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite T3, OLD4, (EEo 3%nat 3%bv eq_refl), Rgp by lia; exact Hgp).
assert (T4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite T4, OLD4, (EEo 4%nat 4%bv eq_refl), Rtp by lia; exact Htp).
assert (T8' : getr (ms_regs ms) 8 = getr regs 8) by (rewrite T8, OLD4, X33 by lia; reflexivity).
assert (T9' : getr (ms_regs ms) 9 = getr regs 9) by (rewrite T9, OLD4, X34 by lia; reflexivity).
assert (T10' : getr (ms_regs ms) 10 = w64 c) by (rewrite T10, OLD4, E8 by lia; reflexivity).
assert (T11' : getr (ms_regs ms) 11 = w64 q) by (rewrite T11, A44; exact Hq10).
assert (Thi : forall r, 18 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hc10 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc10 as [-> | Hc10]); [..| subst r];
  rewrite (st_ok_restrict_reg SEGS (w_H W3) E4 _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite OLD4 by lia; rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end. }
assert (HPT : aregs_preserved regs (ms_regs ms)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hcs2 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ 18 <= r <= 27) by lia.
  destruct Hcs2 as [-> | [-> | [-> | [-> | [-> | Hr9]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). exact T2'.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T3', Hgp. reflexivity.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T4', Htp. reflexivity.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). exact T8'.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). exact T9'.
  - exact (Thi r Hr9). }
(* memory: the run after the call writes nothing; the callee keeps every byte outside its footprint *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E4 _ (w_H W3) mem3 (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia|]). destruct Hin. }
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK3 & HIMG3 & _).
(* a byte of g_rec / record.spill: as after the run from SWL_JOIN *)
assert (HrdM : forall a, Exists (in_zr a) recb_PG -> rdW W3 (ms_mem ms) a = rdW Wc (ms_mem ms1) a).
{ intros a HPG. destruct (recb_prog_unowned_m B HB cmd_prog_img a HPG) as (Hi & Ho & He).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (pose proof (pa_img_range a Hi); lia).
  rewrite (KEEP3 a Ha64).
  exact (HIMG3 a Hi Ho He (fp_spares_closed [] a (sink_closed_pos [] (Forall_nil _)) (inFP_nil a))). }
assert (HrdG : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) -> ~ (c <= a < c + 8) ->
  rdW W3 (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hnc.
  assert (HPG : Exists (in_zr a) recb_PG) by (destruct Ha as [Ha | Ha]; [apply recb_grec_in | apply recb_spill_in]; exact Ha).
  rewrite (HrdM a HPG). apply KEEP1; [unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia | exact Hnc]. }
(* the recorder's blocks: kept from SWL_JOIN on *)
assert (HO1bl : forall pn, In pn O1 -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply JB1. apply JB2 in Hpn as [HpO HpF]. split; [exact (swl_rec_repA_in B ly S _ R O HREP pn HpO) | exact HpF]. }
assert (Hbl3 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; apply (Permutation_in _ (Permutation_sym HPerm3)); exact Hpn).
assert (HrdB : forall pn i, In pn O1 -> 0 <= i < snd pn -> rdW W3 (ms_mem ms) (fst pn + i) = rdW Wc memc (fst pn + i)).
{ intros [b m] i Hpn Hi. cbn [fst snd] in Hi |- *.
  pose proof (HO1bl _ Hpn) as Hc0. pose proof (Hbl3 _ Hc0) as Hc3.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hc0) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
  assert (Hni : ~ in_img SEGS (b + i)).
  { destruct (al_client_img _ _ LAWS _ _ _ _ _ (b + i) HARc) as [_ Hn]; [left; exists b, m; split; [exact Hc0 | lia] | exact Hn]. }
  assert (Hnc : ~ (c <= b + i < c + 8)).
  { intros Hci. apply Hni. apply cmd_prog_img. apply (swl_in_PG c); [exact Hc | unfold CALL_SIZE; lia]. }
  assert (Ha64 : 0 <= b + i < 2 ^ 64) by lia.
  rewrite (KEEP3 _ Ha64).
  rewrite (HBLK3 b m i Hc0 Hc3 ltac:(lia) (inFP_nil _)).
  apply KEEP1; [exact Ha64 | exact Hnc]. }
assert (HFN3 : aval_mem (rdW W3 (ms_mem ms)) (c + CALL_OFF_FN) 4 REC_WORKER_LIST).
{ apply (swl_aval_kept (rdW Wc (ms_mem ms1))); [exact Vfn|]. intros j Hj. unfold CALL_OFF_FN.
  apply HrdM. apply (swl_in_PG c); [exact Hc | unfold CALL_SIZE; lia]. }
assert (HNA3 : aval_mem (rdW W3 (ms_mem ms)) (c + CALL_OFF_NARGS) 4 0).
{ apply (swl_aval_kept (rdW Wc (ms_mem ms1))); [exact Vna|]. intros j Hj. unfold CALL_OFF_NARGS.
  apply HrdM. apply (swl_in_PG c); [exact Hc | unfold CALL_SIZE; lia]. }
(* the recorder's state at answer's entry: record() done *)
pose proof (JW (ablocks B ly3 S3) (rdW W3 (ms_mem ms))
  (fun a Ha Hnc => HrdG a (or_introl Ha) Hnc) (fun a Ha Hnc => HrdG a (or_intror Ha) Hnc)
  HFN3 HNA3
  (fun pn Hpn => Hbl3 _ (HO1bl _ (proj1 (JO pn) Hpn)))
  (fun pn i Hpn Hi => HrdB pn i (proj1 (JO pn) Hpn) Hi)) as HAREP.
set (R2 := rec_record R REC_WORKER_LIST []) in *.
set (x := shape_of swl_verb) in *.
set (e := (REC_WORKER_LIST, @nil (list byte))).
set (O2 := lay_blocks QJ).
assert (HMOD : sup_worker_list_m R = rec_answer R2 e x false).
{ unfold sup_worker_list_m, rec_stub, daemon_shape. rewrite swl_verb_bstr. reflexivity. }
assert (HREP3 : rec_repA B ly3 S3 (rdW W3 (ms_mem ms)) R2 O2) by (exists QJ; split; [exact HAREP | intros pn; tauto]).
assert (HO2bl3 : forall pn, In pn O2 -> In pn (ablocks B ly3 S3)) by exact (lay_blocks_in _ _ A_G_REC A_REC_SPILL R2 QJ HAREP).
pose proof HAREP as (_ & _ & _ & _ & Hans3 & _).
pose proof (swl_aanswer_ptr _ _ _ _ _ Hans3) as HOLD3.
set (old := oaddr (l_answer QJ)) in *.
(* the shape rec_shape_of returned *)
pose proof (proj1 HJ3) as HAR3'.
destruct (HqARG [(q, 1)]) as (Hqnz & HqS & HqL & [(_ & HqF) | (HqRO & _)]).
{ exfalso. rewrite Forall_forall in HqF. pose proof (HqF (q, 1) (or_introl eq_refl)) as Hap.
  unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
assert (Hqimg : forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0x10000 <= q + i < 0x606000).
{ intros i Hi. exact (pa_img_range _ (proj1 (cmd_ro_prog_apart _ (proj1 (HqRO i Hi))))). }
pose proof (Hqimg 0 ltac:(lia)) as Hq0r. pose proof (Hqimg (Z.of_nat (length x)) ltac:(lia)) as Hqer.
assert (HqARG4 : astr_argA B ly3 S3 (rdW W3 (ms_mem ms)) (in_roP SEGS RLO RHI) O2 q (Some x)).
{ apply (swl_astr_argA_rd _ _ (rdW W3 mem3)); [exact (HqARG O2) | intros i Hi; apply KEEP3; pose proof (Hqimg i Hi); lia]. }
assert (Hfits : fits x) by (unfold fits, x; vm_compute; intro Hf; discriminate Hf).
(* the budgets at answer's entry *)
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & HfrS3 & HnevS3 & _ & HHI3 & _).
assert (MLE3' : mo_le MT Sc S3 0) by (rewrite ES3; exact (mo_le_refl MT MTL Sc)).
assert (MLEa : mo_le MT S S3 (rec_spill_frees R * mo_free MT + 0))
  by exact (mo_le_trans MT MTL _ _ _ _ _ MLE MLE3').
rewrite HMOD in MOK, Hlive.
assert (HMOK4 : mo_ok MT S3 (XM_ANSWER MT (snd (rec_answer R2 e x false)))).
{ apply (mok_station MT S S3 _ _ _ MTL MOK MLEa (XN0 _)). lia. }
assert (HEV4 : st_nev S3 + EV_ANSWER <= EV_MAX) by (unfold EV_REC_SHAPE_OF in HnevS3; lia).
assert (HLIVE4 : blocks_bytes S3 + LIVE_ANSWER (snd (rec_answer R2 e x false)) <= LIVE_MAX).
{ rewrite ES3. lia. }
assert (HROD4 : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms))) by exact (swl_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HJ3 HREP HROD).
assert (HRO4 : cmd_ro_ok (rdW W3 (ms_mem ms))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HAR3' HROD4).
assert (HspT4 : spZ (ms_regs ms) = sp0 + 0) by (unfold spZ at 1; rewrite T2'; unfold sp0, spZ; lia).
assert (HraT4 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite T1'; exact Hra).
assert (Hra4T4 : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite T1'; exact Hra4).
assert (Etop3 : ly_top ly3 = ly_top ly) by (destruct HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _); exact Etop3).
assert (HchT : achain ly3 (rdW W3 (ms_mem ms)) (sp0 + 0) (s0Z (ms_regs ms)) ch).
{ rewrite Z.add_0_r. unfold s0Z. rewrite T8'. fold (s0Z regs). apply (swl_achain_ly ly ly3); [|exact Etop3].
  apply (achain_kept ly (rdW W mem) _ sp0 _ ch sp0 Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply HHI3; [lia | lia |].
  intros HFa. unfold swl_FP in HFa. apply inFP_cons in HFa as [HFa | HFa]; [unfold A_G_REC, REC_SIZE in HFa; lia|].
  apply inFP_cons in HFa as [HFa | HFa]; [unfold A_REC_SPILL, SC_SIZE in HFa; lia|].
  destruct (inFP_ablocks_fp_inv O a HFa) as (b & m & Hbm & Hba).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 (swl_rec_repA_in B ly S _ R O HREP (b, m) Hbm)) as (_ & _ & Hbc & _). lia. }
assert (Hold_cases : old = 0 \/ (exists a0, old = fst a0 /\ In a0 O1)).
{ unfold old. destruct (l_answer QJ) as [a0|] eqn:Ea;
  [right; exists a0; split; [reflexivity | apply JA2; first [exact Ea | reflexivity]] | left; reflexivity]. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Hold_cases as [Ho | (a0 & Ho & Hin0)]; [lia|].
  destruct a0 as [b m].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR3' (HO2bl3 _ (proj2 (JO _) Hin0))) as (_ & Hb4 & Hbc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)). cbn [fst] in Ho. lia. }
(* 0x8b5b0: the tail jump to answer(c, shape, 0), at this function's entry sp *)
rewrite swl_sig_ans.
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W3 (ms_regs ms) (ms_mem ms) _ SUP_WORKER_LIST_STK sp0 (swl_FP O) ly S W mem md [] ly3 S3 _
    (k + EV_REC_SHAPE_OF) ANSWER_STK _ EV_ANSWER 0 (getr (ms_regs ms) 1) ch _ HJ3 HspT4 eq_refl ltac:(lia)
    ltac:(vm_compute; discriminate) ltac:(rewrite FS; vm_compute; discriminate) T3' T4' eq_refl HraT4 Hra4T4 HchT).
  - intros HPRE4. exact (TANSWER fx ly3 S3 W3 (ms_regs ms) (ms_mem ms) _ ch c q old e x false R2 O2 HPRE4 HFRM
      ltac:(rewrite HfrS3; exact Hfr8) HROD4 HRO4 T10' ltac:(unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hcb; lia)
      T11' Hq0 ltac:(rewrite T12; reflexivity) HREP3 HOLD3 Hold64
      (fun _ => conj HqARG4 Hfits) (fun _ Hf => ltac:(discriminate Hf)) HEV4 HLIVE4 HMOK4).
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
    { right; right; right; right; left.
      assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold OFF_ANSWER, REC_SIZE in *; lia).
      split; [|split; [rewrite (recb_ts_prog_m B HB); exact HPG | exact (cmd_prog_img a HPG)]].
      unfold swl_FP. apply inFP_cons. left. unfold OFF_ANSWER, REC_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha].
    { right; right; right; right; left.
      assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold OFF_STATE, REC_SIZE in *; lia).
      split; [|split; [rewrite (recb_ts_prog_m B HB); exact HPG | exact (cmd_prog_img a HPG)]].
      unfold swl_FP. apply inFP_cons. left. unfold OFF_STATE, REC_SIZE in *. lia. }
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba).
    apply swl_in_filter_old in Hbm as [Hbm Hbo]. cbn [fst] in Hbo.
    assert (HbO1 : In (b, m) O1) by exact (proj1 (JO _) Hbm).
    right; left. split.
    + unfold swl_FP. apply inFP_cons. right. apply inFP_cons. right.
      replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b m (a - b)); [exact (proj1 (proj1 (JB2 _) HbO1)) | lia].
    + exists b, m. split; [exact (Hbl3 _ (HO1bl _ HbO1)) | exact Hba].
  - intros ly5 S5 W5 regs5 mem5 md5 _ a Ha Hw _. exfalso. rewrite FS in Hw.
    apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_ANSWER in Ha; lia|].
    apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_STATE in Ha; lia|].
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba). apply swl_in_filter_old in Hbm as [Hbm _].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR3' (HO2bl3 _ Hbm)) as (_ & _ & Hbc & _). lia. }
cbv beta. intros W5 c5 Hwle5 (fx1 & ly5 & S5 & regs5 & mem5 & md5 & Hfx & -> & HJ5 & HJc5 & HP5 & HK5).
cbv zeta in HK5.
destruct HK5 as (p1 & p2 & O' & H10' & Hp2 & Hp12 & Hfresh & Hbl5 & HREP5 & HO' & HS5 & BB5 & MLE5).
pose proof (proj1 HJ5) as HAR5.
assert (HNEWc : forall pn, ~ In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S) -> In pn O).
{ intros pn Hn Hin. destruct (in_dec recb_pair_dec pn F) as [HF' | HF'].
  - exact (proj1 (JB3 pn HF')).
  - exfalso. apply Hn. apply JB1. split; [exact Hin | exact HF']. }
assert (HNEW : forall pn, ~ In pn (ablocks B ly3 S3) -> In pn (ablocks B ly S) -> In pn O).
{ intros pn Hn Hin. apply HNEWc; [|exact Hin]. intros Hc'. apply Hn. exact (Hbl3 _ Hc'). }
rewrite T1'.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly5 S5);
  [exact Hfx | eapply (ajournal_mono_k SEGS B); [exact HJ5 | unfold EV_SUP_WORKER_LIST, EV_REC_SHAPE_OF; lia]
  | exact (aregs_preserved_trans _ _ _ HPT HP5) |].
unfold swl_post. exists (fst (rec_answer R2 e x false)), (snd (rec_answer R2 e x false)), p2, O'.
set (nt := Z.of_nat (length (snd (rec_answer R2 e x false))) + 1) in *.
assert (Hp2in5 : In (p2, nt) (ablocks B ly5 S5)) by (apply Hbl5; right; right; reflexivity).
(* a copy answer made that was a block live at the entry: one the recorder owned (freed on the spill arm or as
   the old answer, then handed out again) *)
assert (HFO : forall X, In (X, nt) (ablocks B ly S) ->
  (forall pn, In pn (ablocks B ly3 S3) -> fst pn <> old -> pn <> (X, nt)) -> In (X, nt) O).
{ intros X Hin HX.
  destruct (in_dec recb_pair_dec (X, nt) (ablocks B ly3 S3)) as [H3 | H3]; [|exact (HNEW _ H3 Hin)].
  destruct (Z.eq_dec X old) as [Eo | Ne]; [|exfalso; exact (HX _ H3 Ne eq_refl)].
  destruct Hold_cases as [Ho | (a0 & Ho & Hin0)].
  - exfalso. destruct (al_blocks _ _ LAWS _ _ _ _ _ X nt HAR0 Hin) as (_ & Hb4 & _). lia.
  - pose proof (HO2bl3 a0 (proj2 (JO a0) Hin0)) as Ha03.
    assert (E0 : (X, nt) = a0) by exact (swl_same_start ly3 S3 W3 (ms_mem ms) _ (X, nt) a0 HAR3' H3 Ha03 ltac:(cbn [fst]; lia)).
    rewrite E0. exact (proj1 (proj1 (JB2 a0) Hin0)). }
assert (HFO1 : forall X, In (X, nt) (ablocks B ly S) -> X = p1 \/ X = p2 -> In (X, nt) O).
{ intros X Hin HX. apply (HFO X Hin). intros pn Hpn Hfo Epn. destruct (Hfresh pn Hpn Hfo) as [N1 N2].
  destruct HX as [-> | ->]; [exact (N1 Epn) | exact (N2 Epn)]. }
split; [rewrite HMOD; apply surjective_pairing|].
split; [exact H10'|]. split; [exact Hp2|]. split; [exact HREP5|].
split.
{ intros pn Hpn. apply HO' in Hpn as [(Hpn2 & Hold) | ->].
  - left. exact (proj1 (proj1 (JB2 pn) (proj1 (JO pn) Hpn2))).
  - destruct (in_dec recb_pair_dec (p1, nt) (ablocks B ly S)) as [Hin|Hnin]; [left; exact (HFO1 p1 Hin (or_introl eq_refl)) | right; exact Hnin]. }
split; [exact Hp2in5|].
split; [intros pn Hpn Hno Epn; subst pn; exact (Hno (HFO1 p2 Hpn (or_intror eq_refl)))|].
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Est & Hpn). apply HO' in Hpn as [(Hpn2 & Hold) | ->].
  - pose proof (HO2bl3 _ Hpn2) as Hpn3.
    assert (Hpn5 : In pn (ablocks B ly5 S5)) by (apply Hbl5; left; split; [exact Hpn3 | exact Hold]).
    pose proof (swl_same_start ly5 S5 W5 mem5 md5 pn (p2, nt) HAR5 Hpn5 Hp2in5 Est) as ->. exact (proj2 (Hfresh _ Hpn3 Hold) eq_refl).
  - cbn [fst] in Est. exact (Hp12 Est). }
split; [exact HS5|].
split.
{ intros pn Hpn Hno.
  assert (HnF : ~ In pn F) by (intros HF'; exact (Hno (proj1 (JB3 pn HF')))).
  assert (Hpnc : In pn (ablocks B lyc Sc)) by (apply JB1; split; [exact Hpn | exact HnF]).
  pose proof (Hbl3 _ Hpnc) as Hpn3.
  assert (Hfo : fst pn <> old).
  { destruct Hold_cases as [Ho | (a0 & Ho & Hin0)].
    - destruct pn as [b m]. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hpn) as (_ & Hb4 & _). cbn [fst]. lia.
    - intros Est. pose proof (HO2bl3 a0 (proj2 (JO a0) Hin0)) as Ha03.
      pose proof (swl_same_start ly3 S3 W3 (ms_mem ms) _ pn a0 HAR3' Hpn3 Ha03 ltac:(lia)) as ->.
      exact (Hno (proj1 (proj1 (JB2 a0) Hin0))). }
  assert (Hpn5 : In pn (ablocks B ly5 S5)) by (apply Hbl5; left; split; [exact Hpn3 | exact Hfo]).
  split; [exact Hpn5|].
  assert (Hne : pn <> (p2, nt)) by exact (proj2 (Hfresh pn Hpn3 Hfo)).
  exact (swl_blocks_apart ly5 S5 W5 mem5 md5 pn (p2, nt) HAR5 Hpn5 Hp2in5 Hne). }
split.
{ intros pn Hpn. apply Hbl5 in Hpn as [(Hpn3 & Hfo) | [-> | ->]].
  - apply (Permutation_in _ HPerm3) in Hpn3.
    apply JB1 in Hpn3 as [Hpn0 HnF]. destruct (in_dec recb_pair_dec pn O) as [HpO | HpO].
    + right; left. apply HO'. left. split; [apply JO; apply JB2; split; [exact HpO | exact HnF] | exact Hfo].
    + left. split; [exact Hpn0 | exact HpO].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ unfold LIVE_SUP_WORKER_LIST. rewrite HMOD. rewrite ES3 in BB5. lia. }
unfold XM_SUP_WORKER_LIST. rewrite HMOD.
apply (mo_le_mono MT MTL _ _ _ _ (mo_le_trans MT MTL _ _ _ _ _ MLEa MLE5)). lia.
Qed.

(* ---------- segment A: the entry and record()'s two arms (0x8b4f0 .. 0x8b554), and the statement ---------- *)
Theorem tsup_worker_list_holds : tsup_worker_list_spec B MT.
Proof.
unfold tsup_worker_list_spec.
intros ly S W regs mem md ch R O HPRE HFRM HROD HRO HREP Hfr8 Hev Hlive MOK.
change ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O) with (swl_FP O).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FS : SUP_WORKER_LIST_STK = 16592) by (vm_compute; reflexivity).
set (sp0 := spZ regs) in *.
pose proof HREP as (Q & HA & HO).
pose proof HA as (_ & _ & _ & (HC1 & HC2 & HNC & HC4 & HC5 & HC6) & _).
set (n := length (r_calls R)) in *.
destruct (swl_seedA B LAWS TL VOBJS cmd_prog_writable ly S W mem md regs (Z.of_nat n) HAR0 Hstk Hpres0 HNC ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_WORKER_LIST_STK (swl_FP O) ly S W regs mem md ch HPRE) as HJ.
set (E := swl_EA regs (Z.of_nat n)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold swl_EA. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; unfold swl_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat n)) by (subst E; unfold swl_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (U44 : bv_unsigned (ew E (A_OBJ 44)) = A_G_REC) by (rewrite (HEI (A_OBJ 44) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); exact (swl_grec_val VOBJS)).
unfold cfg_at, w64.
(* 0x8b4f0 .. 0x8b51c: the frame, the shadow base, g_rec.ncalls, then the branch on a full table *)
paj_run_tok RUN HS HJ SHOK swl_Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := A_OBJ 44); [reflexivity | exact U44 | | apply (awr_ok_nil SEGS B)].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold OFF_NCALLS in Ha.
  assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold A_G_REC, REC_SIZE in *; lia).
  right; right; right; right; left.
  split; [|split; [rewrite (recb_ts_prog_m B HB); exact HPG | exact (cmd_prog_img a HPG)]].
  unfold swl_FP. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia. }
try swl_md.
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
assert (U33 : U E (SOff 33 0) = Z.of_nat n) by (apply U_atom; [exact E33 | lia]).
psrr_branch_tok RUN BR HS SHOK swl_Bspan.
- (* g_rec.ncalls <> 16: the slot arm, 0x8b538 .. 0x8b550 *)
  rewrite branch_ne_U, U33 in Hc. cbn in Hc.
  assert (U16 : U E (SLit 16) = 16) by reflexivity. rewrite U16 in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hn16 : (n < 16)%nat) by lia.
  paj_run_to_tok RUNTO HS HJ SHOK swl_Bspan SWL_JOIN.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite FS; lia | cbn; lia |].
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := A_OBJ 44); [reflexivity | exact U44 | | apply (awr_ok_nil SEGS B)].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold OFF_NCALLS in Ha.
    assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold A_G_REC, REC_SIZE in *; lia).
    right; right; right; right; left.
    split; [|split; [rewrite (recb_ts_prog_m B HB); exact HPG | exact (cmd_prog_img a HPG)]].
    unfold swl_FP. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia. }
  pmkst HS. try swl_md.
  set (c := A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n).
  assert (Hc' : swl_slot_ok c) by (left; exists (Z.of_nat n); split; [unfold REC_CALLS_MAX; lia | reflexivity]).
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  assert (E285 : ew E 285 = Z_to_bv 64 A_G_REC).
  { apply bv_eq. change 285%nat with (A_OBJ 44). rewrite U44. rewrite unsigned_lit_small; unfold A_G_REC; lia. }
  assert (U285 : bv_unsigned (ew E 285) = A_G_REC) by exact U44.
  assert (Rsp : bv_unsigned (getr (ms_regs ms) 2) = spZ regs - SWL_FRAME)
    by (rewrite P2, Usp, unsigned_lit_small by lia; unfold SWL_FRAME, sp0; lia).
  assert (Rgp : getr (ms_regs ms) 3 = getr regs 3) by (rewrite P3; exact (EEo 3%nat 3%bv eq_refl)).
  assert (Rtp : getr (ms_regs ms) 4 = getr regs 4) by (rewrite P4; exact (EEo 4%nat 4%bv eq_refl)).
  assert (R8 : getr (ms_regs ms) 8 = Z_to_bv 64 c) by (rewrite P8, E33, E285; apply swl_slot_word; lia).
  assert (R9 : getr (ms_regs ms) 9 = Z_to_bv 64 SB) by (rewrite P9; exact E32).
  assert (Rhi : forall r, 18 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr.
    assert (Hc10 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc10 as [-> | Hc10]); [..| subst r];
    rewrite (st_ok_restrict_reg SEGS (w_H W) E _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => exact (EEo m (Z_to_bv 5 rr) eq_refl) end. }
  pose proof HS as HSt. unfold st_ok_pi, abs_ss in HSt.
  lazymatch type of HSt with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) swl_slotB) in
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) swl_slotB) in
    pose proof (st_ok_region_nth (segs := SEGS) _ ssx (restrict _ msx) 0 r0 HSt ltac:(vm_compute; reflexivity)) as HR0;
    pose proof (st_ok_region_nth (segs := SEGS) _ ssx (restrict _ msx) 3 r3 HSt ltac:(vm_compute; reflexivity)) as HR3;
    cbn [ms_mem restrict mkst] in HR0, HR3 end.
  pose proof (bv_unsigned_in_range 64 (getr regs 1)) as G1. pose proof (bv_unsigned_in_range 64 (getr regs 8)) as G8.
  pose proof (bv_unsigned_in_range 64 (getr regs 9)) as G9.
  change (bv_modulus 64) with (2 ^ 64) in G1, G8, G9.
  assert (HFRm : swl_frame SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - SWL_FRAME) regs).
  { unfold swl_frame, SWL_FRAME. fold sp0.
    replace (sp0 - 32 + 24) with (sp0 + -8) by lia. replace (sp0 - 32 + 16) with (sp0 + -16) by lia.
    replace (sp0 - 32 + 8) with (sp0 + -24) by lia.
    split; [|split].
    - apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) HR0 Usp ltac:(cbn; tauto));
      [cbn [sv_denot]; rewrite (EEo 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity | cbn; lia | cbn; lia].
    - apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-16) 8 (SOff 8 0) (bv_unsigned (getr regs 8)) HR0 Usp ltac:(cbn; tauto));
      [cbn [sv_denot]; rewrite (EEo 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity | cbn; lia | cbn; lia].
    - apply (field_of_region E _ 2 sp0 _ _ _ _ _ (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HR0 Usp ltac:(cbn; tauto));
      [cbn [sv_denot]; rewrite (EEo 9%nat 9%bv eq_refl), Z.add_0_r; reflexivity | cbn; lia | cbn; lia]. }
  assert (HNC1 : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat n + 1)).
  { apply aval_mem_view. unfold OFF_NCALLS.
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) (Z.of_nat n + 1) HR3 U285 ltac:(cbn; tauto));
    [cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia]. }
  (* the two runs write only the frame and g_rec.ncalls *)
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> ~ (A_G_REC + 8 <= a < A_G_REC + 12) ->
     rdW W (ms_mem ms0) a = rdW W mem a).
  { intros a Ha H1 H2.
    apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms0) (fun a => (sp0 - 32 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr0);
    [|exact Ha | tauto].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]).
    destruct Hin. }
  assert (KEEPJ : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> ~ (A_G_REC + 8 <= a < A_G_REC + 12) ->
     rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1 H2. rewrite <- (KEEP0 a Ha H1 H2).
    apply (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms0) (ms_mem ms) (fun a => (sp0 - 32 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr);
    [|exact Ha | tauto].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]).
    destruct Hin. }
  assert (Hcb : A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + OFF_ANSWER).
  { subst c. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE. lia. }
  assert (JW : swl_jw (rdW W (ms_mem ms)) R c (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q))).
  { intros bl2 rd2 H1 H2 HFn HNa Hbl Hb.
    rewrite swl_lay_slot0 in Hbl, Hb.
    unfold rec_record. fold n. rewrite (proj2 (Nat.ltb_lt _ _) Hn16).
    apply (swl_arep_slot0 (ablocks B ly S) (rdW W mem) bl2 rd2 R Q c REC_WORKER_LIST HA Hn16 eq_refl).
    - intros a Ha Hna Hnc. rewrite (H1 a Ha Hnc). apply KEEPJ; unfold A_G_REC, REC_SIZE, OFF_NCALLS in *; lia.
    - intros a Ha. rewrite (H2 a Ha ltac:(unfold A_G_REC, A_REC_SPILL, OFF_ANSWER, SC_SIZE, CALL_SIZE in *; lia)).
      apply KEEPJ; unfold A_G_REC, A_REC_SPILL, SC_SIZE in *; lia.
    - apply (swl_aval_kept (rdW W (ms_mem ms))); [exact HNC1|]. intros j Hj. apply H1; unfold A_G_REC, REC_SIZE, OFF_NCALLS, OFF_CALLS in *; lia.
    - exact HFn.
    - exact HNa.
    - vm_compute. split; congruence.
    - exact Hbl.
    - intros [pb pm] i Hpn Hi. cbn [fst snd] in Hi |- *.
      pose proof (Hb (pb, pm) i Hpn Hi) as Hbi. cbn [fst] in Hbi. rewrite Hbi.
      destruct (swl_blk_byte ly S W mem md pb pm i HAR0 (swl_rec_repA_in B ly S _ R O HREP (pb, pm) (proj2 (HO _) Hpn)) Hi) as (B1 & B2 & B3).
      apply KEEPJ; [lia | lia |]. intros Hg. apply B3. apply cmd_prog_img. apply recb_grec_in. unfold A_G_REC, REC_SIZE in *. lia. }
  assert (MLE0 : mo_le MT S S (rec_spill_frees R * mo_free MT)).
  { apply (mo_le_mono MT MTL _ _ 0); [apply (mo_le_refl MT MTL)|].
    assert (0 <= rec_spill_frees R) by (unfold rec_spill_frees; destruct (Nat.ltb _ _); lia).
    pose proof (mo_free_nonneg MT MTL). nia. }
  assert (RSF0 : 0 <= rec_spill_frees R) by (unfold rec_spill_frees; destruct (Nat.ltb _ _); lia).
  exact (swl_join ly S W regs mem md ch R O ly S W (ms_regs ms) (ms_mem ms) _ 0 c [] O
      (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q))
      HPRE HFRM HROD HRO HREP Hfr8 Hev Hlive MOK HJ RSF0 MLE0 ltac:(lia) HFRm Rsp Rgp Rtp R8 R9 Rhi Hc'
      (fun pn => ltac:(cbn; tauto)) (fun pn => ltac:(cbn; tauto)) (fun pn Hpn => match Hpn with end)
      (fun pn => ltac:(rewrite swl_lay_slot0, (HO pn); tauto))
      (fun q Hq => ltac:(cbn [l_answer] in Hq; apply HO; unfold lay_blocks; rewrite Hq; apply in_app_iff; right;
                          apply in_app_iff; right; apply in_app_iff; left; left; reflexivity))
      JW).
- (* g_rec.ncalls = 16: the spill arm, 0x8b520 .. 0x8b530 *)
  rewrite branch_ne_U, U33 in Hc. cbn in Hc.
  assert (U16 : U E (SLit 16) = 16) by reflexivity. rewrite U16 in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hn16 : n = 16%nat) by lia.
  assert (HL : length (r_calls R) = 16%nat) by exact Hn16.
  paj_run_tok RUN HS HJ SHOK swl_Bspan.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite FS; lia | cbn; lia |].
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
    eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := A_OBJ 44); [reflexivity | exact U44 | | apply (awr_ok_nil SEGS B)].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold OFF_NCALLS in Ha.
    assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold A_G_REC, REC_SIZE in *; lia).
    right; right; right; right; left.
    split; [|split; [rewrite (recb_ts_prog_m B HB); exact HPG | exact (cmd_prog_img a HPG)]].
    unfold swl_FP. apply inFP_cons. left. unfold A_G_REC, REC_SIZE in *. lia. }
  pmkst HS. try swl_md.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  assert (U285 : bv_unsigned (ew E 285) = A_G_REC) by exact U44.
  assert (E292 : forall E', img_env VAL A_LIM E' -> ew E' 292 = Z_to_bv 64 A_REC_SPILL).
  { intros E' HE'. apply bv_eq. change 292%nat with (A_OBJ 51).
    rewrite (HE' (A_OBJ 51) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), (swl_spill_val VOBJS).
    rewrite unsigned_lit_small; unfold A_REC_SPILL; lia. }
  (* g_rec.ncalls at the call: still 16 *)
  lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r3 := eval vm_compute in (nth 3 (ss_mem ssx) swl_slotB) in
    pose proof (st_ok_region_nth (segs := SEGS) _ ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3;
    cbn [ms_mem restrict mkst] in HR3 end.
  assert (HNCc : aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat n)).
  { apply aval_mem_view. unfold OFF_NCALLS.
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 0) (Z.of_nat n) HR3 U285 ltac:(cbn; tauto));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
  (* the two runs write only the frame: g_rec.ncalls keeps its value *)
  assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1.
    destruct (Z_lt_le_dec a (A_G_REC + 8)) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec a (A_G_REC + 12)) as [Hhi|Hhi]].
    2: { replace a with (A_G_REC + OFF_NCALLS + Z.of_nat (Z.to_nat (a - (A_G_REC + 8)))) by (unfold OFF_NCALLS; lia).
         exact (swl_aval_eq _ _ _ _ _ HNC HNCc (Z.to_nat (a - (A_G_REC + 8))) ltac:(lia)). }
    all: transitivity (rdW W (ms_mem ms0) a).
    all: try (apply (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms0) (ms_mem ms)
           (fun a => (sp0 - 32 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr); [|exact Ha | lia];
         intros b wlo whi a' Hin Hrr; vm_compute in Hin;
         repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]);
         destruct Hin).
    all: apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms0)
           (fun a => (sp0 - 32 <= a < sp0) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr0); [|exact Ha | lia];
         intros b wlo whi a' Hin Hrr; vm_compute in Hin;
         repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U285 in Hrr; lia|]);
         destruct Hin. }
  assert (Hstk_lo : alloc_ceiling + SUP_WORKER_LIST_STK <= sp0) by lia.
  assert (HAc : arep_at (ablocks B ly S) (rdW W (ms_mem ms)) A_G_REC A_REC_SPILL R Q).
  { apply (swl_arep_kept _ _ (rdW W mem) _ R Q HA).
    - intros pn Hpn. exact (swl_rec_repA_in B ly S _ R O HREP pn (proj2 (HO pn) Hpn)).
    - intros a Ha. apply KEEPC; unfold A_G_REC, REC_SIZE in *; lia.
    - intros a Ha. apply KEEPC; unfold A_REC_SPILL, SC_SIZE in *; lia.
    - intros [pb pm] i Hpn Hi. cbn [fst snd] in Hi |- *.
      destruct (swl_blk_byte ly S W mem md pb pm i HAR0 (swl_rec_repA_in B ly S _ R O HREP (pb, pm) (proj2 (HO _) Hpn)) Hi) as (B1 & B2 & B3).
      apply KEEPC; lia. }
  pose proof HAc as (_ & _ & _ & (_ & _ & _ & _ & HC5c & _) & _ & _ & _ & (HNDq & _)).
  pose proof HC5c as (_ & G6 & GL & _ & GN & GNd & G7).
  (* rec_calls_free(&record.spill, 1) *)
  assert (FR : REC_CALLS_FREE_STK = 16496) by (vm_compute; reflexivity).
  assert (HspT : spZ (ms_regs ms) = sp0 + -32) by (unfold spZ at 1; rewrite P2, Usp, unsigned_lit_small by lia; lia).
  assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Hgp).
  assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Htp).
  assert (P10' : getr (ms_regs ms) 10 = w64 A_REC_SPILL) by (rewrite P10; exact (E292 E HEI)).
  assert (P11' : getr (ms_regs ms) 11 = w64 (Z.of_nat (length [l_spill Q]))) by (rewrite P11; reflexivity).
  assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
  assert (Hch1 : achain ly (rdW W (ms_mem ms)) (sp0 + -32) (s0Z (ms_regs ms)) []).
  { left. split; [|reflexivity]. left. unfold s0Z. rewrite P8, (E292 E HEI), unsigned_lit_small by (unfold A_REC_SPILL; lia).
    unfold A_REC_SPILL. lia. }
  assert (RSF : rec_spill_frees R = Z.of_nat (length (l_spill Q))).
  { unfold rec_spill_frees. rewrite HL. cbn [Nat.ltb Nat.leb]. rewrite GL. reflexivity. }
  assert (EVC : EV_REC_CALLS_FREE [l_spill Q] = Z.of_nat (length (l_spill Q)))
    by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; reflexivity).
  assert (XMC : XM_REC_CALLS_FREE MT [l_spill Q] = rec_spill_frees R * mo_free MT)
    by (unfold XM_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r, RSF; reflexivity).
  assert (EVN : EV_ANSWER = 3) by reflexivity.
  assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
  { intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
  assert (HEc : st_nev S + EV_REC_CALLS_FREE [l_spill Q] <= EV_MAX).
  { rewrite EVC, <- RSF. unfold EV_SUP_WORKER_LIST in Hev. lia. }
  assert (HMOKc : mo_ok MT S (XM_REC_CALLS_FREE MT [l_spill Q])).
  { rewrite XMC. apply (mo_ok_le MT MTL S _ _ MOK). unfold XM_SUP_WORKER_LIST.
    pose proof (XN0 (snd (sup_worker_list_m R))). lia. }
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
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))) by exact (swl_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HJ HREP HROD).
  assert (HspillO : forall pn, In pn (l_spill Q) -> In pn O)
    by (intros pn Hpn; apply HO; unfold lay_blocks; apply in_app_iff; right; apply in_app_iff; left; exact Hpn).
  assert (HFP1 : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a ->
     (A_REC_SPILL + CALL_OFF_NARGS <= a < A_REC_SPILL + CALL_OFF_NARGS + 4) \/
     (exists b m, In (b, m) (l_spill Q) /\ b <= a < b + req_size m)).
  { intros a Ha. unfold rcf_fp in Ha. cbn [length seq map app] in Ha. apply inFP_cons in Ha as [Ha | Ha].
    - left. cbn [Z.of_nat] in Ha. lia.
    - right. destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba). cbn [concat] in Hbm. rewrite app_nil_r in Hbm.
      exists b, m. split; [exact Hbm | exact Hba]. }
  assert (HFP1s : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a -> a < sp0 - SUP_WORKER_LIST_STK).
  { intros a Ha. destruct (HFP1 a Ha) as [Ha' | (b & m & Hbm & Hba)]; [unfold A_REC_SPILL, CALL_OFF_NARGS in Ha'; lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 (swl_rec_repA_in B ly S _ R O HREP (b, m) (HspillO _ Hbm))) as (_ & _ & Hbc & _).
    lia. }
  rewrite swl_sig_rcf.
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ SUP_WORKER_LIST_STK sp0 (swl_FP O) ly S W mem md [] ly S _ 0
      REC_CALLS_FREE_STK _ (EV_REC_CALLS_FREE [l_spill Q]) (-32) (getr (ms_regs ms) 1) [] _ HJ HspT eq_refl ltac:(lia)
      ltac:(rewrite FR; lia) ltac:(rewrite FR, FS; lia) P3' P4' eq_refl HraT Hra4T Hch1).
    - intros HPRE1. exact (TRCF fx ly S W (ms_regs ms) (ms_mem ms) _ [] A_REC_SPILL [l_spill Q] HPRE1 HRODc P10' P11'
        ltac:(cbn; lia) HHOME ltac:(unfold A_REC_SPILL; reflexivity) HENT HND HEc HMOKc).
    - intros a Ha. destruct (HFP1 a Ha) as [Ha' | (b & m & Hbm & Hba)].
      + right; right; right; right; left.
        assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_spill_in; unfold A_REC_SPILL, SC_SIZE, CALL_OFF_NARGS in *; lia).
        split; [|split; [rewrite (recb_ts_prog_m B HB); exact HPG | exact (cmd_prog_img a HPG)]].
        unfold swl_FP. apply inFP_cons. right. apply inFP_cons. left. unfold A_REC_SPILL, SC_SIZE, CALL_OFF_NARGS in *. lia.
      + right; left. split.
        * unfold swl_FP. apply inFP_cons. right. apply inFP_cons. right.
          replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b m (a - b)); [exact (HspillO _ Hbm) | lia].
        * exists b, m. split; [exact (swl_rec_repA_in B ly S _ R O HREP (b, m) (HspillO _ Hbm)) | exact Hba].
    - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. rewrite FS in Hw. pose proof (HFP1s a Ha). lia. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
  destruct HK2 as (HPermF & _ & _ & _ & _ & HRspill & _ & _ & MLEF).
  rewrite P1.
  (* back at 0x8b534 *)
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    eapply (region_kept_stack_sub SEGS B);
    [exact HJc2 | exact HJ2 | exact Usp | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. pose proof (HFP1s a HFa). rewrite FS in *. cbn in Ha. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 40 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HS.
  assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD3 : forall m, (m < 40)%nat -> ew E3 m = ew E m) by (intros m Hm; rewrite HE3; apply YN3v.ew_havoc_old; exact Hm).
  clear HE3.
  assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by lia; exact Usp).
  assert (SHOK3 : sh_ok SEGS swl_BxA swl_SHA E3 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, swl_SHA; apply Forall_nil).
  rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
  (* 0x8b534: j 0x8b554 *)
  paj_run_to_tok RUNTO HS HJ2 SHOK3 swl_Bspan SWL_JOIN.
  { lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
    eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp3 | cbn; rewrite FS; lia | cbn; lia |].
    apply (awr_ok_nil SEGS B). }
  pmkst HS. try swl_md.
  pose proof (proj1 HJ2) as HAR2.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
  assert (Rsp : bv_unsigned (getr (ms_regs ms) 2) = spZ regs - SWL_FRAME)
    by (rewrite Q2, Usp3, unsigned_lit_small by lia; unfold SWL_FRAME, sp0; lia).
  assert (Rgp : getr (ms_regs ms) 3 = getr regs 3) by (rewrite Q3, OLD3 by lia; exact (EEo 3%nat 3%bv eq_refl)).
  assert (Rtp : getr (ms_regs ms) 4 = getr regs 4) by (rewrite Q4, OLD3 by lia; exact (EEo 4%nat 4%bv eq_refl)).
  assert (R8 : getr (ms_regs ms) 8 = Z_to_bv 64 A_REC_SPILL) by (rewrite Q8; exact (E292 E3 HEI3)).
  assert (R9 : getr (ms_regs ms) 9 = Z_to_bv 64 SB) by (rewrite Q9, OLD3 by lia; exact E32).
  assert (Rhi : forall r, 18 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr.
    assert (Hc10 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc10 as [-> | Hc10]); [..| subst r];
    rewrite (st_ok_restrict_reg SEGS (w_H W2) E3 _ _ _ HS); cbn [ms_regs];
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => rewrite OLD3 by lia; exact (EEo m (Z_to_bv 5 rr) eq_refl) end. }
  pose proof HS as HSt. unfold st_ok_pi, abs_ss in HSt.
  lazymatch type of HSt with st_ok _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) swl_slotB) in
    pose proof (st_ok_region_nth (segs := SEGS) _ ssx (restrict _ msx) 0 r0 HSt ltac:(vm_compute; reflexivity)) as HR0;
    cbn [ms_mem restrict mkst] in HR0 end.
  pose proof (bv_unsigned_in_range 64 (getr regs 1)) as G1. pose proof (bv_unsigned_in_range 64 (getr regs 8)) as G8.
  pose proof (bv_unsigned_in_range 64 (getr regs 9)) as G9.
  change (bv_modulus 64) with (2 ^ 64) in G1, G8, G9.
  assert (HFRm : swl_frame SEGS (mrestrict (w_H W2) (ms_mem ms)) (spZ regs - SWL_FRAME) regs).
  { unfold swl_frame, SWL_FRAME. fold sp0.
    replace (sp0 - 32 + 24) with (sp0 + -8) by lia. replace (sp0 - 32 + 16) with (sp0 + -16) by lia.
    replace (sp0 - 32 + 8) with (sp0 + -24) by lia.
    split; [|split].
    - apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) HR0 Usp3 ltac:(cbn; tauto));
      [cbn [sv_denot]; rewrite OLD3, (EEo 1%nat 1%bv eq_refl), Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
    - apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-16) 8 (SOff 8 0) (bv_unsigned (getr regs 8)) HR0 Usp3 ltac:(cbn; tauto));
      [cbn [sv_denot]; rewrite OLD3, (EEo 8%nat 8%bv eq_refl), Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
    - apply (field_of_region E3 _ 2 sp0 _ _ _ _ _ (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HR0 Usp3 ltac:(cbn; tauto));
      [cbn [sv_denot]; rewrite OLD3, (EEo 9%nat 9%bv eq_refl), Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia]. }
  (* the jump writes nothing outside the frame *)
  assert (KEEPJ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
  { intros a Ha H1.
    apply (kept_of_frame (segs := SEGS) E3 _ (w_H W2) mem2 (ms_mem ms) (fun a => sp0 - 32 <= a < sp0) HFr); [|exact Ha | exact H1].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]).
    destruct Hin. }
  set (O1 := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
  pose proof (HRspill R Q HAc eq_refl eq_refl) as HRF.
  assert (HRJ : rec_repA B ly2 S2 (rdW W2 (ms_mem ms)) (set_spill R (fst (r_spill R), [])) O1).
  { apply (swl_rec_repA_kept B ly2 S2 (rdW W2 mem2) ly2 S2 _ _ O1 HRF).
    - intros pn Hpn. exact (swl_rec_repA_in B ly2 S2 _ _ O1 HRF pn Hpn).
    - intros a Ha. apply KEEPJ2; unfold A_G_REC, REC_SIZE in *; lia.
    - intros a Ha. apply KEEPJ2; unfold A_REC_SPILL, SC_SIZE in *; lia.
    - intros pb pm i Hpn Hi.
      destruct (swl_blk_byte ly2 S2 W2 _ _ pb pm i HAR2 (swl_rec_repA_in B ly2 S2 _ _ O1 HRF (pb, pm) Hpn) Hi) as (B1 & B2 & B3).
      apply KEEPJ2; lia. }
  destruct HRJ as (Q1 & HA1 & HO1).
  assert (HQ1s : l_spill Q1 = []).
  { pose proof HA1 as (_ & _ & _ & (_ & _ & _ & _ & (_ & _ & GL1 & _) & _) & _). cbn in GL1.
    destruct (l_spill Q1); [reflexivity | discriminate]. }
  pose proof (recb_ablocks_nodup_m B ly S W mem md HAR0) as NDS.
  pose proof (Permutation_NoDup HPermF NDS) as ND2.
  apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HNDq.
  pose proof HNDq as NDq'. unfold lay_blocks in NDq'. rewrite !map_app in NDq'.
  assert (JB1 : forall pn, In pn (ablocks B ly2 S2) <-> In pn (ablocks B ly S) /\ ~ In pn (l_spill Q)).
  { intros pn. split.
    - intros H. split; [apply (Permutation_in _ (Permutation_sym HPermF)); apply in_app_iff; left; exact H|].
      intros Hs. apply (list_nodup_app_disj _ _ pn ND2 H). cbn [concat]. rewrite app_nil_r. exact Hs.
    - intros [H Hs]. apply (Permutation_in _ HPermF) in H. apply in_app_iff in H as [H|H]; [exact H|].
      exfalso. apply Hs. cbn [concat] in H. rewrite app_nil_r in H. exact H. }
  assert (JB2 : forall pn, In pn O1 <-> In pn O /\ ~ In pn (l_spill Q)).
  { intros pn. rewrite (HO pn). subst O1. unfold lay_blocks. rewrite !in_app_iff. split.
    - intros H. split; [tauto|]. intros Hs. destruct H as [Hcl | Har].
      + exact (list_nodup_app_disj _ _ (fst pn) NDq' (in_map fst _ _ Hcl) (in_or_app _ _ _ (or_introl (in_map fst _ _ Hs)))).
      + pose proof (swl_nodup_app_r _ _ NDq') as NDr.
        apply (list_nodup_app_disj _ _ (fst pn) NDr (in_map fst _ _ Hs)).
        destruct Har as [Ha | Hr]; apply in_or_app; [left | right]; apply in_map; assumption.
    - intros [H Hs]. tauto. }
  assert (MLE0 : mo_le MT S S2 (rec_spill_frees R * mo_free MT)) by (rewrite <- XMC; exact MLEF).
  assert (Hbb : blocks_bytes S2 <= blocks_bytes S).
  { rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HPermF), bsum_app.
    assert (0 <= bsum (concat [l_spill Q])); [|lia].
    apply swl_bsum_nonneg. intros [pb pm] Hpn. cbn [concat] in Hpn. rewrite app_nil_r in Hpn.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR0 (swl_rec_repA_in B ly S _ R O HREP (pb, pm) (HspillO _ Hpn))) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. lia. }
  assert (JW : swl_jw (rdW W2 (ms_mem ms)) R A_REC_SPILL (RLay (l_calls Q1) [] (l_answer Q1) (l_reply Q1))).
  { intros bl2 rd2 H1 H2 HFn HNa Hbl Hb.
    rewrite (swl_lay_spill0 Q1 HQ1s) in Hbl, Hb.
    unfold rec_record. rewrite HL. cbn [Nat.ltb Nat.leb].
    apply (swl_arep_spill0 (ablocks B ly2 S2) (rdW W2 (ms_mem ms)) bl2 rd2 _ Q1 REC_WORKER_LIST HA1 eq_refl).
    - intros a Ha. apply H1; [exact Ha | unfold A_G_REC, A_REC_SPILL, REC_SIZE in *; lia].
    - intros a Ha Hn. exact (H2 a Ha Hn).
    - exact HFn.
    - exact HNa.
    - vm_compute. split; congruence.
    - exact Hbl.
    - exact Hb. }
  assert (JB3 : forall pn, In pn (l_spill Q) -> In pn O /\ (16 <= length (r_calls R))%nat)
    by (intros pn Hs; split; [exact (HspillO pn Hs) | lia]).
  assert (Hk0 : 0 + EV_REC_CALLS_FREE [l_spill Q] <= rec_spill_frees R) by (rewrite EVC, RSF; lia).
  exact (swl_join ly S W regs mem md ch R O ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ (0 + EV_REC_CALLS_FREE [l_spill Q])
      A_REC_SPILL (l_spill Q) O1 (RLay (l_calls Q1) [] (l_answer Q1) (l_reply Q1))
      HPRE HFRM HROD HRO HREP Hfr8 Hev Hlive MOK HJ2 Hk0 MLE0 Hbb HFRm
      Rsp Rgp Rtp R8 R9 Rhi (or_intror eq_refl)
      JB1 JB2 JB3
      (fun pn => ltac:(rewrite (swl_lay_spill0 Q1 HQ1s), (HO1 pn); tauto))
      (fun q Hq => ltac:(cbn [l_answer] in Hq; apply HO1; unfold lay_blocks; rewrite Hq; apply in_app_iff; right;
                          apply in_app_iff; right; apply in_app_iff; left; left; reflexivity))
      JW).
Qed.

End e.
End f.
End d.
