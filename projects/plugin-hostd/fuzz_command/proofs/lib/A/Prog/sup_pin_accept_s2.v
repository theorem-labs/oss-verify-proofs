(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: blocks S and TA of sup_pin_accept's ASan walk (plugin-hostd/fuzz_command), after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call composed by cl_callS and the walk back from it) over fuzz_command's
   listing. *)

(* From B0 = 0x8bc40 (both arms of `bnez s1` meet; s1 holds the string to record: uri, or "(null)" when uri is NULL)
   to the tail jump into answer: the call of xstrdup, its two checks on the slot (nargs, args[0]), the store of the copy
   into the slot, the call of rec_shape_of on "pin_accept", the frame's release and `j answer` with changes = 1. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c rec_shape_of_c hand_back_c mix_call_c answer_c sup_pin_accept_c RecBLemmas sup_pin_accept_s1 sup_pin_accept_s3
sup_pin_accept_r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the verb rec_shape_of is asked for: the 10 bytes of "pin_accept" at 0x21e60 *)
Definition spa_verb : list byte := bstr "pin_accept"%string.
Lemma spa_verb_lit : spa_verb ++ [Z_to_bv 8 0] = RO_lit_21e60.
Proof. vm_compute. reflexivity. Qed.
Lemma spa_verb_shape : shape_of spa_verb = daemon_shape "pin_accept"%string.
Proof. reflexivity. Qed.
Lemma spa_null_lit : bstr "(null)"%string ++ [Z_to_bv 8 0] = RO_lit_22480.
Proof. vm_compute. reflexivity. Qed.
Lemma spa_verb_no0 : ~ In (Z_to_bv 8 0) spa_verb.
Proof.
intros Hin. apply (in_map bv_unsigned) in Hin. vm_compute in Hin.
repeat (destruct Hin as [Hin | Hin]; [discriminate Hin|]). exact Hin.
Qed.

(* the block bookkeeping of the post, over the block lists of the entry (bl0), the join (blc), answer's entry (bl3)
   and the end (bl5), from answer's post at an earlier commit (its fresh blocks are none of the entry's blocks other
   than the freed old answer's) *)
Lemma spa_post_lists2 : forall (bl0 blc bl3 bl5 O O1 O' : list (Z * Z)) pnew p1 p2 (old : Z),
(forall pn, In pn bl0 -> ~ In pn O -> In pn blc) ->
(forall pn, In pn blc -> In pn bl0) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O -> In pn blc -> In pn O1) ->
(forall pn, In pn O1 -> In pn blc) ->
~ In pnew blc ->
(forall pn, In pn bl3 <-> pn = pnew \/ In pn blc) ->
(forall pn, In pn bl3 -> fst pn <> old -> pn <> p1 /\ pn <> p2) -> p1 <> p2 ->
(forall pn, In pn bl5 <-> (In pn bl3 /\ fst pn <> old) \/ pn = p1 \/ pn = p2) ->
(forall pn, In pn O' <-> (In pn (O1 ++ [pnew]) /\ fst pn <> old) \/ pn = p1) ->
(forall pn, In pn bl3 -> fst pn = old -> In pn (O1 ++ [pnew])) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
In p2 bl5 /\
(forall pn, In pn bl0 -> ~ In pn O -> pn <> p2) /\
~ In p2 O' /\ (forall pn, In pn O' -> In pn bl5) /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl5) /\
(forall pn, In pn bl5 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = p2).
Proof.
intros bl0 blc bl3 bl5 O O1 O' pnew p1 p2 old HB2 HB1 HO1 HO2 HO1c Hnew H3 Hfold H12 H5 HO' Hold.
assert (Hdec : forall pn (l : list (Z * Z)), In pn l \/ ~ In pn l)
  by (intros pn l; destruct (in_dec (fun x y : Z * Z => decide (x = y)) pn l); tauto).
assert (K : forall pn, In pn bl0 -> ~ In pn O -> fst pn <> old).
{ intros pn H0 HnO Eo. assert (H3' : In pn bl3) by (apply H3; right; exact (HB2 _ H0 HnO)).
  pose proof (Hold _ H3' Eo) as Hin. apply in_app_or in Hin as [Hin | [E | []]].
  - exact (HnO (HO1 _ Hin)).
  - subst pn. exact (Hnew (HB2 _ H0 HnO)). }
assert (HO2in : forall pn, In pn (O1 ++ [pnew]) -> In pn bl3).
{ intros pn Hin. apply H3. apply in_app_or in Hin as [Hin | [<- | []]]; [right; exact (HO1c _ Hin) | left; reflexivity]. }
split; [|split; [|split; [|split; [|split; [|split]]]]].
- intros pn Hpn. apply HO' in Hpn as [(Hin & _) | ->].
  + apply in_app_or in Hin as [Hin | [<- | []]]; [left; exact (HO1 _ Hin)|].
    destruct (Hdec pnew bl0) as [H|H]; [|right; exact H].
    destruct (Hdec pnew O) as [HO|HO]; [left; exact HO | exfalso; exact (Hnew (HB2 _ H HO))].
  + destruct (Hdec p1 bl0) as [H|H]; [|right; exact H].
    destruct (Hdec p1 O) as [HO|HO]; [left; exact HO|]. exfalso.
    assert (H3' : In p1 bl3) by (apply H3; right; exact (HB2 _ H HO)).
    exact (proj1 (Hfold _ H3' (K _ H HO)) eq_refl).
- apply H5. right; right. reflexivity.
- intros pn H0 HnO. assert (H3' : In pn bl3) by (apply H3; right; exact (HB2 _ H0 HnO)).
  exact (proj2 (Hfold _ H3' (K _ H0 HnO))).
- intros Hin. apply HO' in Hin as [(Hin & Hne) | E]; [|exact (H12 (eq_sym E))].
  exact (proj2 (Hfold _ (HO2in _ Hin) Hne) eq_refl).
- intros pn Hpn. apply HO' in Hpn as [(Hin & Hne) | ->]; apply H5; [left; split; [exact (HO2in _ Hin) | exact Hne] | right; left; reflexivity].
- intros pn H0 HnO. apply H5. left. split; [apply H3; right; exact (HB2 _ H0 HnO) | exact (K _ H0 HnO)].
- intros pn Hpn. apply H5 in Hpn as [(Hin3 & Hne) | [-> | ->]].
  + apply H3 in Hin3 as [-> | Hc].
    * right; left. apply HO'. left. split; [apply in_or_app; right; left; reflexivity | exact Hne].
    * destruct (Hdec pn O) as [HinO | HnO].
      -- right; left. apply HO'. left. split; [apply in_or_app; left; exact (HO2 _ HinO Hc) | exact Hne].
      -- left. split; [exact (HB1 _ Hc) | exact HnO].
  + right; left. apply HO'. right. reflexivity.
  + right; right. reflexivity.
Qed.

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

(* the statement's post (sup_pin_accept_c.v:99-118), word for word *)
Definition spa_post (R : rstate) (uri : option (list byte)) (O : list (Z * Z)) ly S
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_pin_accept_m R uri = (R', t) /\
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
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_PIN_ACCEPT R uri /\
 mo_le MT S S' (XM_SUP_PIN_ACCEPT MT R uri).

(* the statement's callees *)
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names (LAWS is the core's AR_laws_ok) *)
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the per-binary facts the statements still do not give (the walks' shared names and
   forms; lib/A/Prog/CmdRecFacts.v, which is to prove them, does not exist yet) *)
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
(* the two facts arodata_ok_journalP (CmdBase.v) asks, and cmd_ro_ok from arodata_okP at any AR state *)
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
(* a heap string's tail word is visible (AR gives only [p, p + req_size n)) *)
Hypothesis cmd_heap_tail_vis : forall ly S W mem md p n e, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= e < p + n -> atail_vis SEGS W mem e.
(* the verb literal handed to rec_shape_of is read-only: the premise sup_pin_accept_c.v dropped *)
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

Lemma spa_sig : forall s, In s cmd_prog_syms -> SIG s = BASE + cmd_af s.
Proof. exact SIGP. Qed.
Lemma spa_sig_xstrdup : SIG CS_xstrdup = BASE + AF_xstrdup.
Proof. rewrite (spa_sig CS_xstrdup) by (vm_compute; repeat (first [left; reflexivity | right])). reflexivity. Qed.
Lemma spa_sig_rso : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite (spa_sig CS_rec_shape_of) by (vm_compute; repeat (first [left; reflexivity | right])). reflexivity. Qed.
Lemma spa_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (spa_sig CS_answer) by (vm_compute; repeat (first [left; reflexivity | right])). reflexivity. Qed.

(* the entry of the call record() just made *)
Lemma spa_slot_acall : forall ly S rd R c A O1,
spa_slot_of R c -> rec_repA B ly S rd (rec_record R REC_PIN_ACCEPT A) O1 ->
exists P, acall_at (ablocks B ly S) rd c (REC_PIN_ACCEPT, A) P.
Proof.
intros ly S rd R c A O1 [(Hlt & ->) | (Hge & ->)] (Q & HA & _);
destruct HA as (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & _); unfold rec_record in *.
- replace (Nat.ltb (length (r_calls R)) 16) with true in * by (symmetry; apply Nat.ltb_lt; exact Hlt).
  cbn [r_calls set_calls] in C2, C4.
  assert (Hn : nth_error (r_calls R ++ [(REC_PIN_ACCEPT, A)]) (length (r_calls R)) = Some (REC_PIN_ACCEPT, A))
    by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
  destruct (nth_error (l_calls Q) (length (r_calls R))) as [P|] eqn:HP.
  + exists P. exact (proj1 (C4 _ _ P Hn HP)).
  + exfalso. apply nth_error_None in HP. rewrite C2, length_app in HP. cbn [length] in HP. lia.
- replace (Nat.ltb (length (r_calls R)) 16) with false in * by (symmetry; apply Nat.ltb_ge; exact Hge).
  cbn [r_spill set_spill] in C5. exists (l_spill Q). exact C5.
Qed.

(* a byte of the slot is a program static the footprint names: the core's awr_byte disjunct (YCbq.v awr_prog_or_caller) *)
Lemma spa_awr_slot : forall c a STK sp0 O bl0 blc fr0 ly own, spa_slot_ok c -> c <= a < c + CALL_SIZE ->
awr_byte SEGS B STK sp0 (spa_FP O) bl0 blc fr0 ly own a.
Proof.
intros c a STK sp0 O bl0 blc fr0 ly own Hc Ha.
pose proof (spa_in_PG c a Hc Ha) as HPG.
right; right; right; right. left. split; [|split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)]].
destruct (spa_slot_bounds c Hc) as (Hcb & _ & Hce). destruct Hc as [(H1 & H2 & _) | ->].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]].
  unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]].
  unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the verb literal's 11 bytes are owned by no runtime entry and are not the errno cell (the record's lists) *)
Lemma spa_verb_unowned : forall i, 0 <= i < 11 ->
~ Exists (in_zr (0x21e60 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21e60 + i < as_errno B + 4).
Proof.
intros i Hi. rewrite (ts_owned B HB), (ts_errno B HB). split.
- intros HE. apply Exists_exists in HE as ([lo n] & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  assert (Hb : forallb (fun r => (0x21e6b <=? fst r) || (fst r + snd r <=? 0x21e60)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Hq. cbn beta in Hq. cbn [fst snd] in Hq.
  apply Bool.orb_true_iff in Hq as [Hq | Hq]; apply Z.leb_le in Hq; lia.
- unfold TFIB_ERRNO. lia.
Qed.

(* a write to g_rec or record.spill is one the footprint names (the sup_chain_clear walk's scc_awr_rec,
   lib/A/Prog/sup_chain_clear_s2.v) *)
Lemma spa_awr_rec : forall STK sp0 O bl0 blc fr0 lyc own a,
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp0 (spa_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha.
right; right; right; right; left.
assert (HP : Exists (in_zr a) recb_PG) by exact (spa_in_recPG a Ha).
split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia].
Qed.

(* From B0 to the tail jump: the concrete state where both arms of `bnez s1` meet, s1 = s the string to record. *)
Lemma spa_from_B0 : forall ly S W regs mem md ch (uri : option (list byte)) R O lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k c O1 s,
afn_pre SEGS B SUP_PIN_ACCEPT_STK ly S W regs mem md ch ->
frm0 fx ->
Z.of_nat (length (frames S)) <= 8 ->
st_nev S + EV_SUP_PIN_ACCEPT R <= EV_MAX -> blocks_bytes S + LIVE_SUP_PIN_ACCEPT R uri <= LIVE_MAX ->
mo_ok MT S (XM_SUP_PIN_ACCEPT MT R uri) ->
ajournal SEGS B SUP_PIN_ACCEPT_STK (spZ regs) (spa_FP O) ly S W mem md [] lyc Sc Wc memc mdc k ->
k <= rec_spill_frees R -> mo_le MT S Sc (rec_spill_frees R * mo_free MT) -> blocks_bytes Sc <= blocks_bytes S ->
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall pn, In pn O1 -> In pn O) ->
(forall pn, In pn O -> In pn (ablocks B lyc Sc) -> In pn O1) ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
spZ regs1 = spZ regs - SPA_FRAME -> getr regs1 8 = w64 c -> getr regs1 9 = w64 s -> getr regs1 18 = w64 (c + 4) ->
getr regs1 19 = w64 SB -> getr regs1 20 = w64 (SB + (c + 4) / 8) ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
(forall r, 21 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall j r, nth_error spa_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
spa_slot_ok c -> spa_slot_of R c ->
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_PIN_ACCEPT []) O1 ->
arodata_okP SEGS RLO RHI B (rdW Wc memc) -> cmd_ro_ok (rdW Wc memc) ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] s (Some (sarg uri)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SPA_B0)) memc (seg_rom SEGS)) mdc)
  (apost_baseF SEGS B SUP_PIN_ACCEPT_STK (spa_FP O) regs ly S W mem md (EV_SUP_PIN_ACCEPT R) (spa_post R uri O ly S)).
Proof.
intros ly S W regs mem md ch uri R O lyc Sc Wc regs1 memc mdc k c O1 s
  HPRE HFRM Hfr8 Hev Hlive HMOK HJ Hk HMLE1 Hbb1 HBK1 HBK2 HO1 HOO1 HOS Rsp R8 R9 R18 R19 R20 R3 R4 Rhi HFR Hc Hcm HREP1
  HROD1 HRO1 HSTR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (proj1 HJ) as HARc.
set (sp0 := spZ regs) in *.
assert (WS : SUP_PIN_ACCEPT_STK = 16592) by (vm_compute; reflexivity).
destruct (spa_slot_bounds c Hc) as (Hcb & Hc8 & Hce).
assert (Hcr : 0x5e3750 <= c <= 0x5e3be0 /\ c + 56 <= 0x5e3c18)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
assert (Hsp46 : 2 ^ 46 <= sp0 - SPA_FRAME) by (unfold SPA_FRAME; rewrite WS in Hslo; lia).
(* the symbolic state at B0 *)
assert (HNA : aval_mem (rdW Wc memc) (c + CALL_OFF_NARGS) 4 0).
{ destruct (spa_slot_acall lyc Sc _ R c [] O1 Hcm HREP1) as (P & (_ & _ & _ & _ & HN & _)). exact HN. }
destruct (spa_join_seed B HB cmd_prog_writable SPA_B0 lyc Sc Wc memc mdc regs regs1 c sp0 HARc Hsp46
  ltac:(lia) Hal16 Hc Rsp R8 R18 R19 R20 HFR HNA) as [HS SHOK].
set (E := Eimg (Ereg regs1 (spa_extra regs c))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 8)%nat -> ew E (32 + j) = nth j (spa_extra regs c) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (ESB : ew E 32 = Z_to_bv 64 SB) by (exact (EX 0%nat ltac:(lia))).
assert (EC : ew E 33 = Z_to_bv 64 c) by (exact (EX 1%nat ltac:(lia))).
assert (UC : bv_unsigned (ew E 33) = c) by (rewrite EC; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = sp0 - SPA_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
(* B0 .. 0x8bc44: a0 := s1, the call of xstrdup *)
paj_run_tok RUN HS HJ SHOK spa_Bspan.
{ unfold ss_at, spa_rs, spa_stack, spa_slot. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := SA_C) (b := c); [reflexivity | exact UC | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply (spa_awr_slot c a); [exact Hc | unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ memc) (mrestrict _ ?m1) |- _ =>
assert (KEEP1n : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 4 <= a < c + 16) -> rdW Wc m1 a = rdW Wc memc a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c + 4 <= a < c + 16) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UC in Hrr; cbv beta; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a Ha Hn; apply KEEP1n; [exact Ha | unfold CALL_SIZE in Hn; lia]).
(* the registers at the call *)
assert (Hsp1 : spZ (ms_regs ms) = sp0 + -48).
{ unfold spZ at 1. rewrite P2, (EE 2%nat 2%bv eq_refl). fold (spZ regs1). rewrite Rsp. unfold SPA_FRAME. lia. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), R3; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), R4; exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 s) by (rewrite P10, (EE 9%nat 9%bv eq_refl); exact R9).
assert (P8' : getr (ms_regs ms) 8 = w64 c) by (rewrite P8, EC; reflexivity).
(* the string, its tail and the read-only bytes at the call *)
destruct (spa_str_kept B lyc Sc Wc memc mdc (rdW Wc (ms_mem ms)) (in_roP SEGS RLO RHI) c s (sarg uri) HARc Hc
  cmd_ro_prog_apart HSTR KEEP1) as [HSTRX HOUTS].
set (x := sarg uri) in *.
assert (Hx0 : 0 <= s /\ s + Z.of_nat (length x) + 1 <= 2 ^ 47)
  by (pose proof (HOUTS 0 ltac:(lia)) as [_ A]; pose proof (HOUTS (Z.of_nat (length x)) ltac:(lia)) as [_ A']; lia).
assert (HRO_slot : forall a, in_roP SEGS RLO RHI a -> 0 <= a < 2 ^ 64 /\ ~ (c <= a < c + CALL_SIZE)).
{ intros a Ha. destruct (cmd_ro_prog_apart a Ha) as [Hi Hn]. pose proof (pa_img_range a Hi).
  split; [lia|]. intros Hin. apply Hn. exact (spa_in_PG c a Hc Hin). }
assert (HRODX : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms))).
{ apply (spa_aro_kept B RLO RHI (rdW Wc memc)); [exact HROD1|].
  intros a Ha. destruct (HRO_slot a Ha) as [H1 H2]. exact (KEEP1 a H1 H2). }
pose proof (proj1 HJ) as HARx.
(* the string's tail: from its block (cmd_heap_tail_vis), or from the image literal's end (cmd_ro_ok's tails) *)
assert (HTAILX : atail_vis SEGS Wc (ms_mem ms) (s + Z.of_nat (length x))).
{ destruct HSTRX as (_ & _ & _ & [((p0 & k0 & Hpk & Hp0 & Hpe) & _) | (_ & _ & _ & Hend)]).
  - apply (cmd_heap_tail_vis _ _ _ _ _ p0 k0 _ HARx Hpk). lia.
  - destruct (cmd_ro_ok_of_aro _ _ _ _ _ HARx HRODX) as [_ HTL]. exact (HTL _ Hend). }
pose proof HJ as (_ & _ & _ & _ & _ & Hfrc & Hnevc & _).
assert (EVX : EV_XSTRDUP = 1) by reflexivity. assert (EVA : EV_ANSWER = 3) by reflexivity.
assert (HXMA : 0 <= XM_ANSWER MT (snd (sup_pin_accept_m R uri))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_pin_accept_m R uri))) + 1) ltac:(lia)). lia. }
assert (HMOKc : mo_ok MT Sc (XM_XSTRDUP MT x + XM_ANSWER MT (snd (sup_pin_accept_m R uri)))).
{ apply (mo_ok_step MT MTL S Sc (rec_spill_frees R * mo_free MT)); [|exact HMLE1].
  unfold XM_SUP_PIN_ACCEPT in HMOK. rewrite Z.add_assoc. exact HMOK. }
assert (HXMX : 0 <= XM_XSTRDUP MT x) by (unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc (ms_regs ms) (ms_mem ms) _ SUP_PIN_ACCEPT_STK sp0 (spa_FP O) ly S W mem md [] lyc Sc _ k
    XSTRDUP_STK [] EV_XSTRDUP (-48) (getr (ms_regs ms) 1) [] _ HJ Hsp1).
  - reflexivity.
  - lia.
  - unfold XSTRDUP_STK, ASTACK. lia.
  - rewrite WS. unfold XSTRDUP_STK, ASTACK. lia.
  - exact P3'.
  - exact P4'.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite P8'. unfold w64. rewrite unsigned_lit_small by lia. apply achain_low. lia.
  - intros HPX. rewrite spa_sig_xstrdup.
    exact (TXSTRDUP fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ [] s x HPX HRODX P10' (or_introl HSTRX) HTAILX
      ltac:(rewrite EVX; unfold EV_SUP_PIN_ACCEPT in Hev; rewrite EVX, EVA in Hev; lia)
      ltac:(unfold LIVE_SUP_PIN_ACCEPT, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in Hlive |- *; fold x in Hlive; lia)
      ltac:(apply (mo_ok_le MT MTL Sc _ _ HMOKc); lia)).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJX & HP2 &
  (p & Hp10 & Hp4096 & HPERM & HAPART & HPINB & HSTRP & HSTRS & HBBX & HMLEX)).
pose proof HJX as (HARX & HlyX & _ & _ & _ & HfrX & HnevX & _ & XK1 & XK2 & XK3 & _).
rewrite P1.
jafter_call_keep_pi HS 41%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0;1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
    + apply (mbyte_of_aview SEGS). unfold SPA_FRAME in *. rewrite WS in Hslo.
      apply XK1; [lia | lia | intros Hf; exact (inFP_nil a Hf)].
    + lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite UC; intros a Ha.
    + apply (mbyte_of_aview SEGS).
      destruct (recb_prog_unowned_m B HB cmd_prog_img a (spa_in_PG c a Hc ltac:(unfold CALL_SIZE; lia))) as (Hi & Ho & He).
      apply XK3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; constructor | apply inFP_nil]].
    + intros _. apply (cmd_prog_writable ly2 S2 W2 mem2 md2); [exact HARX | apply (spa_in_PG c); [exact Hc | unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia]]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
remember (havoc E 41 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 41)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (E45 : ew E2 45 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (ESB2 : ew E2 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact ESB).
assert (EC2 : ew E2 33 = Z_to_bv 64 c) by (rewrite OLD2 by lia; exact EC).
assert (UC2 : bv_unsigned (ew E2 33) = c) by (rewrite EC2; apply unsigned_lit_small; lia).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - SPA_FRAME) by (rewrite OLD2 by lia; exact Usp).
pose proof (spa_shok B HB ly2 S2 W2 mem2 md2 E2 c HARX Hc ESB2 EC2) as SHOK2.
rename ms into ms1. rename HJ into HJ1.
(* 0x8bc48 .. 0x8bc88: the two checks on the slot, nargs := 1, args[0] := the copy, the call of rec_shape_of *)
paj_run_tok RUN HS HJ2 SHOK2 spa_Bspan.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := SA_C) (b := c); [reflexivity | exact UC2 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply (spa_awr_slot c a); [exact Hc | unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia]. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
lazymatch goal with Hfr : frame_of E2 _ (mrestrict _ mem2) (mrestrict _ ?m3) |- _ =>
assert (KEEP2n : forall a, 0 <= a < 2 ^ 64 -> ~ (c + 4 <= a < c + 16) -> rdW W2 m3 a = rdW W2 mem2 a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c + 4 <= a < c + 16) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?UC2 in Hrr; cbv beta; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + CALL_SIZE) -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a)
  by (intros a Ha Hn; apply KEEP2n; [exact Ha | unfold CALL_SIZE in Hn; lia]).
assert (Hsp2 : spZ (ms_regs ms) = sp0 + -48).
{ unfold spZ at 1. rewrite Q2, OLD2 by lia. rewrite (EE 2%nat 2%bv eq_refl). fold (spZ regs1). rewrite Rsp. unfold SPA_FRAME. lia. }
assert (Q3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, OLD2, (EE 3%nat 3%bv eq_refl), R3 by lia; exact Hgp).
assert (Q4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, OLD2, (EE 4%nat 4%bv eq_refl), R4 by lia; exact Htp).
assert (Q8' : getr (ms_regs ms) 8 = w64 c) by (rewrite Q8, EC2; reflexivity).
assert (Q10' : getr (ms_regs ms) 10 = w64 0x21e60).
{ rewrite Q10, (img_env_atomP E2 308 HEI2 ltac:(unfold A_TEXT, A_LIM; lia)).
  change (VAL 308%nat) with (VAL (A_OBJ 67)). rewrite (VOBJS 67%nat ltac:(vm_compute; lia)). reflexivity. }
assert (Q11' : getr (ms_regs ms) 11 = w64 (Z.of_nat (length spa_verb))) by (rewrite Q11; reflexivity).
(* the copy's block, and the slot's nargs and args[0] after the stores *)
assert (Hpin : In (p, LIVE_XSTRDUP x) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | left; reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p (LIVE_XSTRDUP x) HARX Hpin) as (Hp16 & _ & Hpceil & _).
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let r := eval vm_compute in (nth 1 (ss_mem ssx) spa_slot) in
  pose proof (st_ok_region_nth (segs:=SEGS) E2 ssx (restrict (w_H W2) msx) 1 r HS ltac:(vm_compute; reflexivity)) as HRs end.
cbn [ms_mem restrict] in HRs.
pose proof (field_of_region (segs:=SEGS) E2 _ 33 c _ _ _ _ _ 4 4%N (SLit 1) 1 HRs UC2
  ltac:(cbn; right; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as VNA.
pose proof (field_of_region (segs:=SEGS) E2 _ 33 c _ _ _ _ _ 8 8%N (SOff 45 0) p HRs UC2
  ltac:(cbn; left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E45; exact Hp10)
  ltac:(unfold LIVE_XSTRDUP in Hpceil; pose proof (req_size_pos (Z.of_nat (length x) + 1) ltac:(lia)); cbn; lia)
  ltac:(cbn; lia)) as VARG.
(* the read-only bytes, the verb "pin_accept" and the stack window at the call of rec_shape_of *)
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms))).
{ apply (spa_aro_kept B RLO RHI (rdW W2 mem2)).
  - exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX
      (fun a _ Hf => inFP_nil a Hf) HRODX).
  - intros a Ha. destruct (HRO_slot a Ha) as [H1 H2]. exact (KEEP2 a H1 H2). }
pose proof (cmd_ro_ok_of_aro ly2 S2 W2 (ms_mem ms) _ (proj1 HJ2) HROD2) as HRO2.
assert (HLIT : abytes_atR (rdW W2 (ms_mem ms)) 0x21e60 RO_lit_21e60).
{ clear - HRO2. destruct HRO2 as [HRB _]. unfold cmd_ro_bytes in HRB.
  repeat (first [exact (proj1 HRB) | apply proj2 in HRB]). }
assert (HVB : abytes_atR (rdW W2 (ms_mem ms)) 0x21e60 spa_verb).
{ intros i Hi. rewrite (HLIT i) by (rewrite <- spa_verb_lit, length_app; cbn [length]; lia).
  rewrite <- spa_verb_lit. rewrite app_nth1 by exact Hi. reflexivity. }
assert (HVRO : forall i, 0 <= i < 11 -> in_roP SEGS RLO RHI (0x21e60 + i)).
{ clear - CMD_RO_IN. unfold cmd_ro_in in CMD_RO_IN. repeat (first [exact (proj1 CMD_RO_IN) | apply proj2 in CMD_RO_IN]). }
assert (HLV : Z.of_nat (length spa_verb) = 10) by (vm_compute; reflexivity).
(* the verb literal in astr_argA's read-only arm: its bytes and terminator (cmd_ro_ok), read-only (CMD_RO_IN), owned
   by no runtime entry (the record's lists), and the record's shadow checks, decided on the concrete lists *)
assert (HVA : astr_argA B ly2 S2 (rdW W2 (ms_mem ms)) (in_roP SEGS RLO RHI) [] 0x21e60 (Some spa_verb)).
{ unfold astr_argA. cbv zeta. rewrite HLV. split; [lia|]. split.
  { split; [rewrite spa_verb_lit; exact HLIT | exact spa_verb_no0]. }
  split; [unfold LMAX; lia|]. right. split; [intros i Hi; exact (conj (HVRO i Hi) (spa_verb_unowned i Hi))|].
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  assert (Hb : existsb (Z.eqb 0x21e6a) cmd_ro_ends = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hb as (y & Hy & Hey). apply Z.eqb_eq in Hey. rewrite <- Hey in Hy. exact Hy. }
assert (HEVS : st_nev S2 + EV_REC_SHAPE_OF <= EV_MAX).
{ unfold EV_REC_SHAPE_OF. unfold EV_SUP_PIN_ACCEPT in Hev. rewrite EVX, EVA in Hev. rewrite EVX in HnevX. lia. }
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W2 (ms_regs ms) (ms_mem ms) _ SUP_PIN_ACCEPT_STK sp0 (spa_FP O) ly S W mem md [] ly2 S2 _
    (k + EV_XSTRDUP) REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-48) (getr (ms_regs ms) 1) _ HJ2 Hsp2).
  - reflexivity.
  - lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - rewrite WS. unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - exact Q3'.
  - exact Q4'.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - intros HPS. rewrite spa_sig_rso.
    exact (TREC_SHAPE_OF fx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ 0x21e60 spa_verb HPS HROD2 Q10' ltac:(lia) Q11'
      ltac:(rewrite HLV; lia) HRO2 VOBJS (fun _ => conj HVB (or_intror HVA)) HEVS).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJS & HP3 &
  ((q & Hq10 & Hq64 & HqA) & Hperm3 & Hly3 & HS3e)).
pose proof HJS as (HARS & _ & _ & _ & _ & _ & _ & _ & SK1 & SK2 & SK3 & _).
rewrite Q1.
jafter_call_keep_pi HS 60%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp2; intros a Ha.
  + apply (mbyte_of_aview SEGS). unfold SPA_FRAME in *. rewrite WS in Hslo.
    apply SK1; [lia | lia | intros Hf; exact (inFP_nil a Hf)].
  + lia. }
rewrite <- restrict_mkst_fx in HS3. clear HS. rename HS3 into HS.
remember (havoc E2 60 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 60)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (E64 : ew E3 64 = getr regs3 10) by (rewrite HE3; reflexivity).
clear HE3.
assert (OLD32 : forall n, (n < 41)%nat -> ew E3 n = ew E n) by (intros n Hn; rewrite OLD3, OLD2 by lia; reflexivity).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0 - SPA_FRAME) by (rewrite OLD32 by lia; exact Usp).
rename ms into ms2.
(* 0x8bc8c .. 0x8bcb4: a2 := 1, a1 := the shape, a0 := c, the frame restored, the tail jump into answer *)
assert (SHOK3 : sh_ok SEGS spa_Bx [] E3 (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
paj_run_tok RUN HS HJ3 SHOK3 spa_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22.
prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26.
prreg HS (27%bv : bv 5) T27.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgT := rg) in *; set (mT := mm) in *; set (mdT := mdq) in *
end.
clearbody mdT.
(* the registers at the tail jump: the entry's ra, sp, s0 .. s4 and the callee-saved ones, c, the shape, 1 *)
assert (E34 : ew E 34 = getr regs (Z_to_bv 5 1)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs (Z_to_bv 5 8)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = getr regs (Z_to_bv 5 9)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E 37 = getr regs (Z_to_bv 5 18)) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E 38 = getr regs (Z_to_bv 5 19)) by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E 39 = getr regs (Z_to_bv 5 20)) by exact (EX 7%nat ltac:(lia)).
assert (TR1 : getr rgT 1 = getr regs (Z_to_bv 5 1)) by (rewrite T1, OLD32 by lia; exact E34).
assert (TR1' : getr rgT 1 = getr regs 1)
  by (rewrite TR1; replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity); reflexivity).
assert (TRsp : spZ rgT = sp0).
{ unfold spZ. rewrite T2, OLD32 by lia. rewrite Usp. rewrite unsigned_lit_small by (unfold SPA_FRAME; lia).
  unfold SPA_FRAME. lia. }
assert (TR3 : getr rgT 3 = getr regs 3) by (rewrite T3, OLD32, (EE 3%nat 3%bv eq_refl) by lia; exact R3).
assert (TR4 : getr rgT 4 = getr regs 4) by (rewrite T4, OLD32, (EE 4%nat 4%bv eq_refl) by lia; exact R4).
assert (TR10 : getr rgT 10 = w64 c) by (rewrite T10, OLD32 by lia; exact EC).
assert (TR11 : getr rgT 11 = w64 q) by (rewrite T11, E64; exact Hq10).
assert (HPT : aregs_preserved regs rgT).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ 21 <= r <= 27) by lia.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | Hr2]]]]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    apply bv_eq. fold (spZ rgT). rewrite TRsp. reflexivity.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). exact TR3.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). exact TR4.
  - rewrite <- E35. replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T8, OLD32 by lia. reflexivity.
  - rewrite <- E36. replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T9, OLD32 by lia. reflexivity.
  - rewrite <- E37. replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T18, OLD32 by lia. reflexivity.
  - rewrite <- E38. replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T19, OLD32 by lia. reflexivity.
  - rewrite <- E39. replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T20, OLD32 by lia. reflexivity.
  - rewrite <- (Rhi r Hr2).
    assert (Hc7 : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hc7 as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
    + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T21, OLD32 by lia. exact (EE 21%nat 21%bv eq_refl).
    + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T22, OLD32 by lia. exact (EE 22%nat 22%bv eq_refl).
    + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T23, OLD32 by lia. exact (EE 23%nat 23%bv eq_refl).
    + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T24, OLD32 by lia. exact (EE 24%nat 24%bv eq_refl).
    + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T25, OLD32 by lia. exact (EE 25%nat 25%bv eq_refl).
    + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T26, OLD32 by lia. exact (EE 26%nat 26%bv eq_refl).
    + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite T27, OLD32 by lia. exact (EE 27%nat 27%bv eq_refl). }
assert (TR8 : getr rgT 8 = getr regs 8).
{ pose proof (HPT 8 ltac:(unfold acallee_saved; lia)) as H8.
  replace (Z_to_bv 5 8) with (8%bv : bv 5) in H8 by (apply bv_eq; reflexivity). exact H8. }
(* the memory the tail jump hands to answer: the epilogue wrote nothing *)
lazymatch goal with Hfr : frame_of E3 _ (mrestrict _ mem3) (mrestrict _ mT) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) E3 _ (w_H W3) mem3 mT (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia|]);
          destruct Hin)) as UN3
end.
pose proof HJ3 as (HART & HlyT & _ & _ & _ & HfrT & HnevT & _ & F1 & _).
pose proof HlyT as (_ & _ & _ & _ & _ & _ & _ & _ & EtopT & _).
pose proof (proj1 HJ2) as HAR2c.
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W3 mT)).
{ apply (spa_aro_kept B RLO RHI (rdW W3 mem3)).
  - exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := RRO) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJS
      (fun a _ Hf => inFP_nil a Hf) HROD2).
  - intros a Ha. destruct (HRO_slot a Ha) as [H1 _]. exact (UN3 a H1 (fun z => z)). }
pose proof (cmd_ro_ok_of_aro ly3 S3 W3 mT mdT HART HROD3) as HROT.
assert (HFRT : Z.of_nat (length (frames S3)) <= 8) by (rewrite HfrT; exact Hfr8).
(* the recorder after arg_s: the slot holds the copy p as its first argument *)
assert (ELX : LIVE_XSTRDUP x = Z.of_nat (length x) + 1) by reflexivity.
rewrite ELX in Hpin, HPERM, HAPART.
set (n := Z.of_nat (length x) + 1) in *.
assert (HO1c : forall pn, In pn O1 -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (proj1 (spa_rep_blocks B lyc Sc _ _ _ HREP1 pn Hpn))).
assert (Hn2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym HPERM) (or_intror Hpn))).
assert (Hn0 : 1 <= n) by (unfold n; lia).
assert (HnewSc : ~ In (p, n) (ablocks B lyc Sc)).
{ intros Hin. pose proof (proj1 (Forall_forall _ _) HAPART _ Hin) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart in Hap. lia. }
assert (HOp : forall pn, In pn O1 -> fst pn <> p).
{ intros [a k'] Hpn Ep. cbn [fst] in Ep. subst a. apply HnewSc.
  rewrite <- (spa_same_start B ly2 S2 W2 mem2 md2 (p, k') (p, n) HARX (Hn2 _ (HO1c _ Hpn)) Hpin eq_refl).
  exact (HO1c _ Hpn). }
destruct (spa_blk_apart B cmd_prog_img ly2 S2 W2 mem2 md2 p n HARX Hpin) as [Hpg1 Hpg2].
assert (Hlx : Z.of_nat (length x) <= LMAX) by (destruct HSTR as (_ & _ & HnL & _); lia).
assert (Hslot_img : forall a, c <= a < c + CALL_SIZE -> in_img SEGS a) by (intros a Ha; exact (cmd_prog_img a (spa_in_PG c a Hc Ha))).
assert (Hrd : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
   ~ (c + CALL_OFF_NARGS <= a < c + CALL_OFF_ARGS + 8) -> rdW W2 (ms_mem ms2) a = rdW Wc memc a).
{ intros a Ha Hn. assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hn.
  rewrite (KEEP2n a Ha64 ltac:(lia)).
  rewrite (spa_rec_kept B HB cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJX (sink_closed_pos [] (Forall_nil _)) Ha (inFP_nil a)).
  exact (KEEP1n a Ha64 ltac:(lia)). }
assert (Hblk : forall pn i, In pn O1 -> 0 <= i < snd pn -> rdW W2 (ms_mem ms2) (fst pn + i) = rdW Wc memc (fst pn + i)).
{ intros [a k'] i Hpn Hi. cbn [fst snd] in Hi |- *. pose proof (HO1c _ Hpn) as Hin.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc a k' HARc Hin) as (_ & Ha4 & Hac & _ & _ & _ & Hk0).
  pose proof (req_size_pos k' ltac:(lia)) as [Rk1 Rk2].
  assert (Hni : ~ in_img SEGS (a + i)) by (apply (blk_img SEGS B LAWS lyc Sc Wc memc mdc a k' (a + i) HARc Hin); lia).
  assert (Hns : ~ (c + 4 <= a + i < c + 16)) by (intros Hs; apply Hni; apply Hslot_img; unfold CALL_SIZE; lia).
  rewrite (KEEP2n (a + i) ltac:(lia) Hns).
  rewrite (spa_blk_kept B cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a k' i HJX (proj1 HJ1)
    (fun a0 Ha0 => False_ind _ (inFP_nil a0 Ha0)) Hin (Hn2 _ Hin) Hi).
  exact (KEEP1n (a + i) ltac:(lia) Hns). }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n HARX Hpin) as (_ & Hp4' & Hpc' & _ & _ & _ & _).
pose proof (req_size_pos n ltac:(lia)) as [Rn1 Rn2].
assert (Hpni : forall i, 0 <= i < n -> ~ in_img SEGS (p + i))
  by (intros i Hi; apply (blk_img SEGS B LAWS ly2 S2 W2 mem2 md2 p n (p + i) HARX Hpin); lia).
assert (HSTRP2 : astr_atR (rdW W2 (ms_mem ms2)) p x).
{ apply (spa_astr_keep (rdW W2 mem2)); [exact HSTRP|]. intros y Hy.
  apply KEEP2n; [lia|]. intros Hs. apply (Hpni (y - p) ltac:(unfold n; lia)).
  replace (p + (y - p)) with y by lia. apply Hslot_img. unfold CALL_SIZE; lia. }
destruct (spa_rep_add (ablocks B lyc Sc) (ablocks B ly2 S2) (rdW Wc memc) (rdW W2 (ms_mem ms2)) R c x p O1 Hcm HREP1
  (fun pn Hpn => Hn2 _ (HO1c _ Hpn)) HOp Hpin Hpg1 Hpg2 ltac:(lia) Hlx Hrd Hblk
  (aval_mem_view SEGS _ _ _ _ _ VNA) (aval_mem_view SEGS _ _ _ _ _ VARG) HSTRP2) as (QL2 & HA2 & HO2).
set (R2 := rec_record R REC_PIN_ACCEPT [x]) in *.
set (O2 := O1 ++ [(p, n)]) in *.
assert (HREP2 : rec_repA B ly2 S2 (rdW W2 (ms_mem ms2)) R2 O2) by (exists QL2; split; [exact HA2 | exact HO2]).
assert (HinS23 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly3 S3))
  by (intros pn Hpn; exact (Permutation_in _ (Permutation_sym Hperm3) Hpn)).
assert (HREPT : rec_repA B ly3 S3 (rdW W3 mT) R2 O2).
{ apply (spa_rep_keep B ly2 S2 (rdW W2 (ms_mem ms2)) ly3 S3 (rdW W3 mT) R2 O2 HREP2).
  - intros a Ha. assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold spa_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
    rewrite (UN3 a Ha64 (fun z => z)).
    exact (spa_rec_kept B HB cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJS (sink_closed_pos [] (Forall_nil _)) Ha (inFP_nil a)).
  - intros [a k'] Hpn. pose proof (proj1 (spa_rep_blocks B ly2 S2 _ _ _ HREP2 _ Hpn)) as Hin2.
    split; [exact (HinS23 _ Hin2)|]. intros i Hi. cbn [fst snd] in Hi |- *.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 a k' HARX Hin2) as (_ & Ha4 & Hac & _ & _ & _ & Hk0).
    pose proof (req_size_pos k' ltac:(lia)) as [Rk1 Rk2].
    rewrite (UN3 (a + i) ltac:(lia) (fun z => z)).
    exact (spa_blk_kept B cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a k' i HJS HAR2c
      (fun a0 Ha0 => False_ind _ (inFP_nil a0 Ha0)) Hin2 (HinS23 _ Hin2) Hi). }
(* answer's premises at the tail state *)
set (xs := shape_of spa_verb) in *.
set (e := (REC_PIN_ACCEPT, [x])).
set (t := snd (rec_answer R2 e xs true)).
assert (Ht : snd (sup_pin_accept_m R uri) = t) by reflexivity.
destruct (spa_rep_answer B ly3 S3 _ _ _ HREPT) as (old & Hold & Holdc).
(* the shape rec_shape_of returned, at answer's entry: rec_shape_of's post for O2, carried over the epilogue (which
   wrote nothing) *)
destruct (HqA O2) as (Hqnz & (Hqb & Hqn0) & Hqlen & Harmq).
assert (Hqimg : forall i, 0 <= i < Z.of_nat (length xs) + 1 -> 0 <= q + i < 2 ^ 64).
{ intros i Hi. destruct Harmq as [((pb & kb & Hpk & Hpb & Hpe) & _) | (Hro & _)].
  - destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 pb kb HARS Hpk) as (_ & Hp4 & Hpc & _ & _ & _ & Hk0).
    pose proof (req_size_pos kb ltac:(lia)) as [Rk1 Rk2]. lia.
  - destruct (Hro i Hi) as [Hr _]. destruct (cmd_ro_prog_apart _ Hr) as [Himg _].
    pose proof (pa_img_range _ Himg). lia. }
assert (HSH : r_refuse R2 = 0 ->
  astr_argA B ly3 S3 (rdW W3 mT) (in_roP SEGS RLO RHI) O2 q (Some xs) /\ fits xs).
{ intros _. split; [|unfold fits; vm_compute; discriminate]. unfold astr_argA.
  split; [exact Hqnz|]. split.
  { split; [|exact Hqn0]. intros i Hi.
    rewrite length_app in Hi. cbn [length] in Hi.
    rewrite (UN3 (q + Z.of_nat i) (Hqimg (Z.of_nat i) ltac:(lia)) (fun z => z)).
    exact (Hqb i ltac:(rewrite length_app; cbn [length]; lia)). }
  split; [exact Hqlen | exact Harmq]. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Holdc as [-> | ([pb kb] & Hpn & Eo)]; [lia|]. cbn [fst] in Eo. subst old.
  pose proof (proj1 (spa_rep_blocks B ly3 S3 _ _ _ HREPT _ Hpn)) as Hin.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mT mdT pb kb HART Hin) as (_ & Hp4 & Hpc & _ & _ & _ & Hk0).
  pose proof (req_size_pos kb ltac:(lia)) as [Rk1 Rk2]. lia. }
assert (HSLOT : r_refuse R2 = 0 -> true = true ->
  (exists k0, nth_error (r_calls R2) k0 = Some e /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k0) \/
  (c = A_REC_SPILL /\ e = r_spill R2)).
{ intros _ _. unfold R2, rec_record. destruct Hcm as [(Hlt & ->) | (Hge & ->)].
  - left. exists (length (r_calls R)). rewrite (proj2 (Nat.ltb_lt _ _) Hlt). cbn [r_calls set_calls].
    split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity | reflexivity].
  - right. rewrite (proj2 (Nat.ltb_ge _ _) Hge). cbn [r_spill set_spill]. split; reflexivity. }
assert (Hchg : true = negb (bv_unsigned (getr rgT 12) =? 0)) by (rewrite T12; reflexivity).
assert (HEVT : st_nev S3 + EV_ANSWER <= EV_MAX).
{ unfold EV_SUP_PIN_ACCEPT, EV_REC_SHAPE_OF, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
assert (Hbb3 : blocks_bytes S3 = n + blocks_bytes Sc).
{ rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B lyc Sc).
  rewrite (bsum_perm _ _ Hperm3), (bsum_perm _ _ HPERM), bsum_cons. reflexivity. }
assert (HLIVET : blocks_bytes S3 + LIVE_ANSWER t <= LIVE_MAX).
{ rewrite Hbb3. unfold LIVE_SUP_PIN_ACCEPT, LIVE_XSTRDUP in Hlive. fold x in Hlive. rewrite Ht in Hlive. unfold n. lia. }
assert (HXt : 0 <= XM_ANSWER MT t) by (rewrite <- Ht; exact HXMA).
assert (Hm23 : mo_le MT S2 S3 0) by (rewrite HS3e; exact (mle_start MT S2 MTL)).
pose proof (mle_station MT Sc S2 S3 _ _ MTL HMLEX Hm23) as HmSc3.
assert (HMOKT : mo_ok MT S3 (XM_ANSWER MT t)).
{ apply (mok_station MT Sc S3 (XM_XSTRDUP MT x + XM_ANSWER MT t) (XM_XSTRDUP MT x + 0) (XM_ANSWER MT t) MTL); [| exact HmSc3 | exact HXt | lia].
  rewrite <- Ht. exact HMOKc. }
(* the tail jump: answer runs at this function's entry sp and returns to its caller *)
rewrite spa_sig_answer.
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W3 rgT mT _ SUP_PIN_ACCEPT_STK sp0 (spa_FP O) ly S W mem md [] ly3 S3 mdT
    (k + EV_XSTRDUP + EV_REC_SHAPE_OF) ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) O2))
    EV_ANSWER 0 (getr rgT 1) ch _ HJ3).
  - rewrite TRsp. lia.
  - reflexivity.
  - lia.
  - unfold ANSWER_STK, HAND_BACK_STK, MIX_CALL_STK, XSTRDUP_STK, ESTACK, ASTACK. lia.
  - rewrite WS. unfold ANSWER_STK, HAND_BACK_STK, MIX_CALL_STK, XSTRDUP_STK, ESTACK, ASTACK. lia.
  - rewrite TR3. exact Hgp.
  - rewrite TR4. exact Htp.
  - reflexivity.
  - rewrite TR1'. exact Hra.
  - rewrite TR1'. exact Hra4.
  - rewrite Z.add_0_r. unfold s0Z. rewrite TR8. fold (s0Z regs).
    apply (achain_ly_top ly ly3 _ _ _ _ EtopT).
    apply (achain_kept ly (rdW W mem) (rdW W3 mT) sp0 (s0Z regs) ch sp0 Hch); [lia | lia |].
    intros a Ha. apply F1; [lia | lia |].
    intros (r & Hr & Hra'). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hra'.
    + unfold A_G_REC, REC_SIZE in Hra'. lia.
    + unfold A_REC_SPILL, SC_SIZE in Hra'. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb nb] & <- & Hin). cbn [fst snd] in Hra'.
      destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR0 (HOS _ Hin)) as (_ & _ & Hbc & _). lia.
  - intros HPRE3.
    exact (TANSWER fx ly3 S3 W3 rgT mT mdT ch c q old e xs true R2 O2
      HPRE3 HFRM HFRT HROD3 HROT TR10 ltac:(lia) TR11 Hq64 Hchg HREPT Hold Hold64 HSH HSLOT HEVT HLIVET HMOKT).
  - intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + apply spa_awr_rec. left. unfold A_G_REC, OFF_ANSWER, REC_SIZE in *. lia.
    + apply spa_awr_rec. left. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb nb] & <- & Hin). cbn [fst snd] in Ha.
      apply spa_filter_in in Hin.
      assert (HinT : In (pb, nb) (ablocks B ly3 S3)) by exact (proj1 (spa_rep_blocks B ly3 S3 _ _ _ HREPT _ Hin)).
      assert (HinFP : In (pb, nb) O -> inFP (spa_FP O) a).
      { intros HO. exists (pb, pb + req_size nb). split; [right; right; apply in_map_iff; exists (pb, nb); split; [reflexivity | exact HO]|].
        cbn [fst snd]. exact Ha. }
      destruct (in_dec (fun u v : Z * Z => decide (u = v)) (pb, nb) O) as [HO | HnO].
      * right; left. split; [exact (HinFP HO)|]. exists pb, nb. split; [exact HinT | exact Ha].
      * right; right; left. exists pb, nb. split; [exact HinT|]. split; [|exact Ha].
        intros H0. pose proof (HBK2 _ H0 HnO) as HSc.
        unfold O2 in Hin. apply in_app_or in Hin as [Hin | [E' | []]].
        -- exact (HnO (HO1 _ Hin)).
        -- rewrite <- E' in HSc. exact (HnewSc HSc).
  - intros ly6 S6 W6 regs6 mem6 md6 _ a (r & Hr & Ha) Hw _. exfalso.
    rewrite WS in Hw. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
    + unfold A_G_REC, OFF_ANSWER in Ha. lia.
    + unfold A_G_REC, OFF_STATE in Ha. lia.
    + unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([pb nb] & <- & Hin). cbn [fst snd] in Ha.
      apply spa_filter_in in Hin.
      pose proof (proj1 (spa_rep_blocks B ly3 S3 _ _ _ HREPT _ Hin)) as HinT.
      destruct (al_blocks _ _ LAWS ly3 S3 W3 mT mdT pb nb HART HinT) as (_ & _ & Hbc & _).
      rewrite WS in Hslo. lia. }
cbv beta. intros W5 c5 _ (fx1 & ly5 & S5 & regs5 & mem5 & md5 & Hfx & -> & HJ5 & HJc5 & HP5 & HK5).
destruct HK5 as (p1 & p2 & O' & HK5). cbv zeta in HK5.
change (snd (rec_answer R2 e xs true)) with t in HK5.
destruct HK5 as (Hp2r & Hp24096 & H12 & Hfold & Hbl5 & HREP5 & HO'iff & Hstr5 & HBB5 & HMLE5).
set (nt := Z.of_nat (length t) + 1) in *.
pose proof (proj1 HJ5) as HAR5.
rewrite TR1'.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly5 S5);
  [exact Hfx
  | eapply (ajournal_mono_k SEGS B); [exact HJ5|];
    unfold EV_SUP_PIN_ACCEPT, EV_REC_SHAPE_OF, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *; lia
  | exact (aregs_preserved_trans _ _ _ HPT HP5) |].
(* the block bookkeeping *)
assert (H3iff : forall pn, In pn (ablocks B ly3 S3) <-> pn = (p, n) \/ In pn (ablocks B lyc Sc)).
{ intros pn. split; intros Hpn.
  - apply (Permutation_in _ Hperm3) in Hpn. apply (Permutation_in _ HPERM) in Hpn.
    destruct Hpn as [<- | Hpn]; [left; reflexivity | right; exact Hpn].
  - apply (Permutation_in _ (Permutation_sym Hperm3)). apply (Permutation_in _ (Permutation_sym HPERM)).
    destruct Hpn as [-> | Hpn]; [left; reflexivity | right; exact Hpn]. }
assert (Hold3 : forall pn, In pn (ablocks B ly3 S3) -> fst pn = old -> In pn O2).
{ intros pn Hpn Eo. destruct Holdc as [Eold | (pn' & Hpn' & Eo')].
  - destruct pn as [a k']. destruct (al_blocks _ _ LAWS ly3 S3 W3 mT mdT a k' HART Hpn) as (_ & H4096 & _).
    cbn [fst] in Eo. lia.
  - assert (Hpn'3 : In pn' (ablocks B ly3 S3)) by exact (proj1 (spa_rep_blocks B ly3 S3 _ _ _ HREPT _ Hpn')).
    rewrite (spa_same_start B ly3 S3 W3 mT mdT pn pn' HART Hpn Hpn'3 ltac:(congruence)). exact Hpn'. }
destruct (spa_post_lists2 (ablocks B ly S) (ablocks B lyc Sc) (ablocks B ly3 S3) (ablocks B ly5 S5) O O1 O'
  (p, n) (p1, nt) (p2, nt) old HBK2 HBK1 HO1 HOO1 HO1c HnewSc H3iff Hfold
  ltac:(intros E'; injection E' as E'; exact (H12 E')) Hbl5 HO'iff Hold3) as (L1 & L2 & L3 & L4 & L4' & L5 & L6).
exists (fst (rec_answer R2 e xs true)), t, p2, O'.
split; [exact (surjective_pairing (rec_answer R2 e xs true))|].
split; [exact Hp2r|]. split; [exact Hp24096|]. split; [exact HREP5|].
split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
split.
{ intros Hq'. apply in_map_iff in Hq' as (pn & Ep & Hpn).
  apply L4. rewrite <- (spa_same_start B ly5 S5 W5 mem5 md5 pn (p2, nt) HAR5 (L4' _ Hpn) L2 Ep). exact Hpn. }
split; [exact Hstr5|].
split.
{ intros pn H0 HnO. pose proof (L5 pn H0 HnO) as H5'. split; [exact H5'|].
  pose proof (L3 pn H0 HnO) as Hne.
  destruct pn as [a k'].
  pose proof (sep_blocks SEGS B LAWS ly5 S5 W5 mem5 md5 a k' p2 nt HAR5 H5' L2 Hne) as Hd.
  destruct (al_blocks _ _ LAWS ly5 S5 W5 mem5 md5 a k' HAR5 H5') as (_ & _ & _ & _ & _ & _ & Hkk).
  destruct (al_blocks _ _ LAWS ly5 S5 W5 mem5 md5 p2 nt HAR5 L2) as (_ & _ & _ & _ & _ & _ & Hn').
  pose proof (req_size_pos k' ltac:(lia)) as [_ Rk]. pose proof (req_size_pos nt ltac:(lia)) as [_ Rn].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd |- *. unfold iv_apart. lia. }
split; [exact L6|].
split.
{ unfold LIVE_SUP_PIN_ACCEPT, LIVE_XSTRDUP. fold x. rewrite Ht. unfold n in Hbb3. lia. }
pose proof (mle_station MT S Sc S2 _ _ MTL HMLE1 HMLEX) as HmS2.
pose proof (mle_station MT S S2 S3 _ _ MTL HmS2 Hm23) as HmS3.
pose proof (mle_station MT S S3 S5 _ _ MTL HmS3 HMLE5) as HmS5.
apply (mle_weaken MT S S5 _ _ MTL HmS5). unfold XM_SUP_PIN_ACCEPT. fold x. rewrite Ht. lia.
Qed.

End e.
End f.
End d.
