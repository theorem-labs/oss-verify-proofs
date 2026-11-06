(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the tail of sup_call's ASan walk (plugin-hostd/fuzz_command, 0x8a95c): at
   answer's entry after the epilogue and `j answer` (0x8aa40), answer's contract (answer_c.v tanswer_spec) gives
   sup_call's post (sup_call_s3.v SC_T_stmt). No instruction runs here: the machine is at BASE + AF_answer.

   answer is called with c the recorded slot, the shape "resp 0" (0x21ce0, RO_lit_21ce0 of cmd_ro_ok) and
   changes = 1, on the recorder state rec_record R REC_CALL (sc_args id line) that the tail state holds; then
   sup_call_m R id line = rec_stub R REC_CALL [dec id; canon line] REC_MOD_HOST_SHAPE true
   = rec_answer (rec_record R REC_CALL (sc_args id line)) (REC_CALL, sc_args id line) REC_MOD_HOST_SHAPE true
   (RecModel.v:73-75, :115-116). answer's journal (from the tail state, STK = ANSWER_STK, at the entry sp) is
   joined to the walk's journal (from the entry state, SUP_CALL_STK) by the core's ajournal_sub_wide: g_rec's
   answer and state fields are program statics inside SC_FP, and the old answer's block is one of the recorder's
   blocks, so it is in SC_FP's ablocks_fp O or is a block the walk made.

   Pass-4/5 re-fit: answer's contract is taken at every FP state and used at the tail's
   own FP state fx (the body applies this lemma at the FP state arg_i returned); answer's rounding-mode-0 premise
   is sc_pre's. Answer returns at some fx1 with fxrel fx fx1, and PaFx.v's apost_baseF_intro gives sup_call's
   apost_baseF. Statement pass 5 removed astack_pres from both contracts, so the stack fact at answer's entry is
   gone; the frame chain answer's afn_pre asks is the tail state's (sc_tail's achain, the entry's chain). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibH PaCall CmdBase CmdRep CmdObj CmdZsh CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_call_s0 sup_call_s1 sup_call_s2 sup_call_s3 PaNoChain PaArt PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecRo.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* answer's footprint keeps the recorder's blocks that start at the old answer with stdpp's list filter *)
Lemma sc_t_filter_sub : forall (P : Z * Z -> Prop) (D : forall x, Decision (P x)) (l : list (Z * Z)) x,
  In x (filter P l) -> In x l.
Proof.
intros P D l x. induction l as [|y l IH]; intros H; [exact H|].
cbn in H.
lazymatch type of H with
| context [if ?d then _ else _] => destruct d
end.
- destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)].
- right. exact (IH H).
Qed.

(* the conjunct of a long conjunction H that closes the goal *)
Local Ltac sc_t_pick H :=
  lazymatch type of H with
  | ?A /\ ?B =>
      first [ exact (proj1 H) | let H2 := fresh "Hpk" in pose proof (proj2 H) as H2; clear H; sc_t_pick H2 ]
  | _ => exact H
  end.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
(* the statement's contract of answer, at every FP state (sup_call_c.v:67) *)
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
(* the per-binary record *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
(* the image's per-binary facts: cif_prog_img _ _ IMG (CmdRecBase.v) and cmd_ro_in_img
   (CmdRecRo.v): the image's read-only literals lie in in_roP, the fact astr_argA's read-only arm takes for the shape
   "resp 0" (check_reply_c.v:28 names it) *)
Hypothesis IMG : cmd_img_facts SEGS B.

(* two live blocks with one start are one block *)
Lemma sc_t_start_uniq : forall ly S (W : world SEGS) mem md p n m,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (p, m) (ablocks B ly S) -> n = m.
Proof.
intros ly S W mem md p n m HAR H1 H2.
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR H1) as (_ & _ & _ & _ & _ & HP & _).
assert (HN : forall q k, In (q, k) (ablocks B ly S) -> 1 <= req_size k).
{ intros q k Hq. pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hq) as (_ & _ & _ & _ & _ & _ & Hk).
  unfold req_size. destruct (Z.eqb_spec k 0); lia. }
revert HP H1 H2 HN. generalize (ablocks B ly S) as l.
induction l as [|x tl IH]; intros HP H1 H2 HN; [destruct H1|].
cbn [map] in HP. destruct HP as [HF HP].
assert (HF' : forall y, In y tl -> zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y))).
{ intros y Hy. first [rewrite Forall_forall in HF | idtac].
  apply (HF (fst y, req_size (snd y))). apply in_map_iff. exists y. split; [reflexivity | exact Hy]. }
destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
- subst x. injection E2 as E2. exact E2.
- subst x. exfalso. specialize (HF' _ H2). unfold zdisjoint in HF'. cbn [fst snd] in HF'.
  pose proof (HN p n (or_introl eq_refl)). pose proof (HN p m (or_intror H2)). lia.
- subst x. exfalso. specialize (HF' _ H1). unfold zdisjoint in HF'. cbn [fst snd] in HF'.
  pose proof (HN p m (or_introl eq_refl)). pose proof (HN p n (or_intror H1)). lia.
- apply IH; [exact HP | exact H1 | exact H2 |]. intros q k Hq. apply (HN q k). right. exact Hq.
Qed.

(* the shape's bytes are owned by no runtime entry and are not the errno cell *)
Lemma sc_t_shape_unowned : forall i, 0 <= i < 7 ->
  ~ Exists (in_zr (0x21ce0 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21ce0 + i < as_errno B + 4).
Proof.
intros i Hi. rewrite (ts_owned B HB), (ts_errno B HB).
assert (HOW : forallb (fun q : Z * Z => ((fst q + snd q <=? 0x21ce0) || (0x21ce0 + 7 <=? fst q))%bool)
  Tfib_owned_static = true) by (vm_compute; reflexivity).
assert (HER : ((0x21ce0 + 7 <=? TFIB_ERRNO) || (TFIB_ERRNO + 4 <=? 0x21ce0))%bool = true)
  by (vm_compute; reflexivity).
split.
- intros HE. rewrite Exists_exists in HE. destruct HE as (q & Hq & Hz). unfold in_zr in Hz.
  rewrite forallb_forall in HOW. specialize (HOW q Hq).
  apply Bool.orb_prop in HOW as [H1 | H1]; apply Z.leb_le in H1; lia.
- apply Bool.orb_prop in HER as [H1 | H1]; apply Z.leb_le in H1; lia.
Qed.

Lemma sc_tail_ok : SC_T_stmt B MT.
Proof.
unfold SC_T_stmt.
intros ly S W regs mem md ch id pl line R O lyt St Wt regst memt mdt kt c Ot.
cbv zeta. intros HPRE HTAIL.
set (t := snd (sup_call_m R id line)) in *.
destruct HPRE as (HPRE0 & HFRM & HFR8 & _ & _ & _ & _ & _ & _ & _ & HREP0 & HEV & HLV & HMOK).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & _ & _ & Hstk0 & _).
destruct HTAIL as (HJ & HKT & Hsp & Hra & HPR & Hgp & Htp & H10 & H11 & H12 & Hch & Hslot & HREPt & HOt & HBt &
  HSv & Hfr & Hbb & Hmle & HROD & HRO).
pose proof HJ as (HARt & _).
assert (DEC : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
(* the answer g_rec holds: 0, or the start of one of the recorder's blocks *)
pose proof HREPt as (Q & HARP & HOQ).
assert (HOLD : exists old, aval_mem (rdW Wt memt) (A_G_REC + OFF_ANSWER) 8 old /\
  (old = 0 \/ exists pa0, In pa0 Ot /\ fst pa0 = old)).
{ pose proof HARP as (_ & _ & _ & _ & HANS & _).
  revert HANS. unfold aanswer_at.
  destruct (r_answer (rec_record R REC_CALL (sc_args id line))) as [x|];
  destruct (l_answer Q) as [pa0|] eqn:EQ; intros HANS; cbv beta iota in HANS; try contradiction.
  - exists (fst pa0). split; [exact (proj1 HANS)|]. right. exists pa0. split; [|reflexivity].
    apply HOQ. unfold lay_blocks. rewrite EQ. cbn [oblk].
    apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. left; reflexivity.
  - exists 0. split; [exact HANS | left; reflexivity]. }
destruct HOLD as (old & Hold & Hold2).
(* every block of the recorder at the tail is live *)
assert (HOtB : forall pn, In pn Ot -> In pn (ablocks B lyt St)).
{ intros pn Hpn. exact (proj1 (sc_rep_blocks _ _ _ _ _ _ HARP pn (proj1 (HOQ pn) Hpn))). }
assert (HSTK : ANSWER_STK <= SUP_CALL_STK) by (unfold SUP_CALL_STK; apply Z.le_max_r).
assert (HSTK0 : 0 <= ANSWER_STK) by (apply Z.leb_le; vm_compute; reflexivity).
(* old is 0 or the start of a live block, which ends below alloc_ceiling, below the entry's stack (astk_ok) *)
assert (Hold64 : 0 <= old < 2 ^ 64).
{ pose proof Hstk0 as (_ & HS0 & Hceil & Hslo & Hshi & H47 & _).
  destruct Hold2 as [-> | ([ap ak] & Hpa0 & <-)]; [lia|]. cbn [fst].
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARt (HOtB _ Hpa0)) as (_ & H4 & Hc & _ & _ & _ & Hk).
  assert (1 <= req_size ak) by (unfold req_size; destruct (Z.eqb_spec ak 0); lia). lia. }
(* the slot answer gets: one of g_rec's call slots or record.spill *)
assert (Hc64 : 0 <= c < 2 ^ 64).
{ destruct Hslot as [(Hlt & ->) | (_ & ->)]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, A_REC_SPILL; lia. }
(* answer's premises *)
assert (HPA : afn_pre SEGS B ANSWER_STK lyt St Wt regst memt mdt ch).
{ apply (afn_pre_at SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [] lyt St Wt memt mdt kt regst
    ANSWER_STK 0 ch HJ);
  [lia | reflexivity | lia | exact HSTK0 | lia | rewrite Hra; exact Hra0 | unfold raZ in *; rewrite Hra; exact Hra40
  | exact Hgp | exact Htp | exact Hch]. }
assert (HLIT : abytes_atR (rdW Wt memt) 0x21ce0 RO_lit_21ce0).
{ destruct HRO as [HBY _]. unfold cmd_ro_bytes in HBY. cbv beta in HBY. sc_t_pick HBY. }
assert (HRIN : forall i, 0 <= i < 7 -> in_roP SEGS RLO RHI (0x21ce0 + i)).
{ pose proof (cmd_ro_in_img SEGS B LAWS HB IMG) as HROIN. unfold cmd_ro_in in HROIN. cbv beta in HROIN. sc_t_pick HROIN. }
assert (HSTR : astr_atR (rdW Wt memt) 0x21ce0 REC_MOD_HOST_SHAPE).
{ assert (EQL : REC_MOD_HOST_SHAPE ++ [Z_to_bv 8 0] = RO_lit_21ce0) by reflexivity.
  unfold astr_atR. rewrite EQL. split; [exact HLIT|].
  assert (HN : forallb (fun b : byte => negb (bv_unsigned b =? 0)) REC_MOD_HOST_SHAPE = true)
    by (vm_compute; reflexivity).
  intros Hin. rewrite forallb_forall in HN. specialize (HN _ Hin). vm_compute in HN. discriminate. }
assert (HARG : astr_argA B lyt St (rdW Wt memt) (in_roP SEGS RLO RHI) Ot 0x21ce0 (Some REC_MOD_HOST_SHAPE)).
{ assert (HL : Z.of_nat (length REC_MOD_HOST_SHAPE) + 1 = 7) by reflexivity.
  assert (HL6 : Z.of_nat (length REC_MOD_HOST_SHAPE) = 6) by reflexivity.
  unfold astr_argA. cbv beta iota zeta. rewrite HL, HL6.
  split; [lia|]. split; [exact HSTR|]. split; [unfold LMAX; lia|].
  right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity |]]].
  - intros i Hi. split; [exact (HRIN i Hi) | exact (sc_t_shape_unowned i Hi)].
  - assert (HE : existsb (Z.eqb (0x21ce0 + 6)) cmd_ro_ends = true) by (vm_compute; reflexivity).
    apply existsb_exists in HE as (y & Hy & Ey). apply Z.eqb_eq in Ey. rewrite Ey. exact Hy. }
assert (HFIT : fits REC_MOD_HOST_SHAPE) by (unfold fits; apply Z.leb_le; vm_compute; reflexivity).
assert (HSLOT : r_refuse (rec_record R REC_CALL (sc_args id line)) = 0 -> true = true ->
  (exists k, nth_error (r_calls (rec_record R REC_CALL (sc_args id line))) k =
     Some (REC_CALL, sc_args id line) /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (c = A_REC_SPILL /\
   (REC_CALL, sc_args id line) = r_spill (rec_record R REC_CALL (sc_args id line)))).
{ intros _ _. unfold rec_record. destruct Hslot as [(Hlt & Hc) | (Hge & Hc)].
  - left. exists (length (r_calls R)). rewrite (proj2 (Nat.ltb_lt _ _) Hlt). cbn [r_calls set_calls].
    split; [|exact Hc]. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
  - right. assert (E : Nat.ltb (length (r_calls R)) 16 = false) by (apply Nat.ltb_ge; lia).
    rewrite E. cbn [r_spill set_spill]. split; [exact Hc | reflexivity]. }
assert (HEVA : st_nev St + EV_ANSWER <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). unfold EV_SUP_CALL, EV_SC_ARGS in *. lia. }
assert (HLIVEA : blocks_bytes St + LIVE_ANSWER t <= LIVE_MAX) by (unfold LIVE_SUP_CALL in HLV; lia).
assert (HMOKA : mo_ok MT St (XM_ANSWER MT t)).
{ apply (mo_ok_step MT MTL S St (XM_SC_ARGS MT R id line) (XM_ANSWER MT t));
  [exact HMOK | exact Hmle]. }
(* an entry block that is not the recorder's is not the old answer's: the old answer is in Ot, and Ot's blocks that
   are live at the entry are O's *)
assert (HNOLD : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> fst pn <> old).
{ intros [pp pk] Hb Hno Hfst. pose proof (HSv _ Hb Hno) as HbT. cbn [fst] in Hfst.
  destruct Hold2 as [Eo | ([ap ak] & Hpa0 & Hpa0f)].
  - pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARt HbT) as (_ & H4 & _). lia.
  - cbn [fst] in Hpa0f. pose proof (HOtB _ Hpa0) as HaB.
    rewrite <- Hpa0f in Hfst. subst pp.
    pose proof (sc_t_start_uniq _ _ _ _ _ _ _ _ HARt HbT HaB) as Ek. subst pk.
    destruct (HOt _ Hpa0) as [HO1 | HN1]; [exact (Hno HO1) | exact (HN1 Hb)]. }
pose proof (TANSWER fx lyt St Wt regst memt mdt ch c 0x21ce0 old (REC_CALL, sc_args id line)
  REC_MOD_HOST_SHAPE true (rec_record R REC_CALL (sc_args id line)) Ot
  HPA HFRM ltac:(rewrite Hfr; exact HFR8) HROD HRO H10 Hc64 H11 ltac:(lia) ltac:(rewrite H12; reflexivity)
  HREPt Hold Hold64 (fun _ => conj HARG HFIT) HSLOT HEVA HLIVEA HMOKA) as HA.
(* answer's post, composed with the walk's journal *)
eapply SRr_mono; [exact HA|].
intros W2 c2 _ HAP. destruct HAP as (fx1 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ1 & HP1 & HK).
destruct HK as (p1 & p2 & O' & Hq10 & Hq4096 & Hp12 & Hfr2 & Hbl2 & HREP2 & HO' & Hstr2 & Hbb2 & Hmle2).
change (snd (rec_answer (rec_record R REC_CALL (sc_args id line))
  (REC_CALL, sc_args id line) REC_MOD_HOST_SHAPE true)) with t in *.
change (fst (rec_answer (rec_record R REC_CALL (sc_args id line))
  (REC_CALL, sc_args id line) REC_MOD_HOST_SHAPE true))
  with (fst (sup_call_m R id line)) in HREP2.
assert (HF : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) ::
    (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) Ot)) a ->
  awr_byte SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) (ablocks B ly S) (ablocks B lyt St) (frames S) lyt [] a).
{ intros a (r & Hr & Hb). unfold awr_byte, awr_prog_or_caller.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hb.
  - right. right. right. right. left.
    assert (HPG : inFP cmd_PG a).
    { exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_ANSWER in Hb; lia]. }
    split; [|split; [exact (HPROG B HB a HPG) | exact (cif_prog_img _ _ IMG a HPG)]].
    exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8). unfold SC_FP.
    split; [right; left; reflexivity | cbn [fst snd]; unfold OFF_CALLS, OFF_ANSWER in *; lia].
  - right. right. right. right. left.
    assert (HPG : inFP cmd_PG a).
    { exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold OFF_STATE in Hb; lia]. }
    split; [|split; [exact (HPROG B HB a HPG) | exact (cif_prog_img _ _ IMG a HPG)]].
    exists (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8). unfold SC_FP.
    split; [right; right; left; reflexivity | cbn [fst snd]; lia].
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([bp bn] & <- & Hb2). pose proof (sc_t_filter_sub _ _ _ _ Hb2) as HbOt.
    cbn [fst snd] in Hb. pose proof (HOtB _ HbOt) as HbB.
    destruct (HOt _ HbOt) as [HbO | HbN].
    + right. left. split.
      * exists (bp, bp + req_size bn). split; [|cbn [fst snd]; lia].
        unfold SC_FP. right. right. right. right. unfold ablocks_fp. apply in_map_iff.
        exists (bp, bn). split; [reflexivity | exact HbO].
      * exists bp, bn. split; [exact HbB | lia].
    + right. right. left. exists bp, bn. split; [exact HbB|]. split; [exact HbN | lia]. }
assert (VIS : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) ::
    (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: ablocks_fp (filter (fun pn => fst pn =? old) Ot)) a ->
  spZ regs - SUP_CALL_STK <= a < spZ regs -> ~ (spZ regst - ANSWER_STK <= a < spZ regst) ->
  aview SEGS (w_H W2) mem2 a <> None).
{ intros a (r & Hr & Hb) Hw _. exfalso.
  pose proof Hstk0 as (_ & _ & Hceil & Hslo & _).
  pose proof asan_consts as (C1 & _).
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hb.
  - unfold A_G_REC, OFF_ANSWER in Hb. lia.
  - unfold A_G_REC, OFF_STATE in Hb. lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([bp bn] & <- & Hb2). pose proof (sc_t_filter_sub _ _ _ _ Hb2) as HbOt.
    cbn [fst snd] in Hb. pose proof (HOtB _ HbOt) as HbB.
    pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARt HbB) as (_ & _ & Hc & _). lia. }
pose proof (ajournal_sub_wide SEGS B LAWS pa_segs_low SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md []
  lyt St Wt memt mdt kt ANSWER_STK (spZ regst) _ [] ly2 S2 W2 mem2 md2 EV_ANSWER HJ HJ1 ltac:(lia) ltac:(lia)
  HF VIS) as HJ2.
pose proof HJ1 as (HAR2 & _).
(* sup_call's post: answer returned at fx1 with fxrel fx fx1, which is sup_call's apost_baseF *)
unfold sc_post. rewrite Hra.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly2 S2);
  [exact (conj Hf1 Hf2) | | exact (aregs_preserved_trans _ _ _ HPR HP1) |].
{ apply (ajournal_mono_k SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2). unfold EV_SUP_CALL, EV_SC_ARGS in *. lia. }
cbv beta.
exists (fst (sup_call_m R id line)), O', p2.
split; [apply surjective_pairing|].
cbv zeta.
split; [exact Hq10|]. split; [exact Hq4096|]. split; [exact HREP2|].
split.
{ intros pn Hpn. apply HO' in Hpn as [[HpnOt _] | ->]; [exact (HOt pn HpnOt)|].
  destruct (in_dec DEC (p1, Z.of_nat (length t) + 1) O) as [Hin | Hnin]; [left; exact Hin|].
  right. intros Hb. exact (proj1 (Hfr2 _ (HSv _ Hb Hnin) (HNOLD _ Hb Hnin)) eq_refl). }
split.
{ intros pn Hpn. apply Hbl2 in Hpn as [[Hb Hne] | [-> | ->]].
  - destruct (HBt pn Hb) as [X | HpnOt]; [left; exact X|].
    right. left. apply HO'. left. split; [exact HpnOt | exact Hne].
  - right. left. apply HO'. right. reflexivity.
  - right. right. reflexivity. }
split.
{ intros pn Hb Hno. apply Hbl2. left. split; [exact (HSv _ Hb Hno) | exact (HNOLD _ Hb Hno)]. }
split; [apply Hbl2; right; right; reflexivity|].
split; [intros pn Hb Hno; exact (proj2 (Hfr2 _ (HSv _ Hb Hno) (HNOLD _ Hb Hno)))|].
split.
{ intros Hin. apply in_map_iff in Hin as ([pp pk] & Hf & Hpn). cbn [fst] in Hf. subst pp.
  apply HO' in Hpn as [[HpnOt Hne] | Heq].
  - pose proof (HOtB _ HpnOt) as HbT.
    assert (Hb2 : In (p2, pk) (ablocks B ly2 S2)) by (apply Hbl2; left; split; [exact HbT | exact Hne]).
    assert (Hq2 : In (p2, Z.of_nat (length t) + 1) (ablocks B ly2 S2)) by (apply Hbl2; right; right; reflexivity).
    pose proof (sc_t_start_uniq _ _ _ _ _ _ _ _ HAR2 Hb2 Hq2) as Ek. subst pk.
    exact (proj2 (Hfr2 _ HbT Hne) eq_refl).
  - injection Heq as E1 _. exact (Hp12 (eq_sym E1)). }
split; [exact Hstr2|].
split; [unfold LIVE_SUP_CALL; lia|].
exact (mo_le_trans MT MTL S St S2 _ _ Hmle Hmle2).
Qed.
End e.
End f.
End w.

About sc_tail_ok.
Print Assumptions sc_tail_ok.
