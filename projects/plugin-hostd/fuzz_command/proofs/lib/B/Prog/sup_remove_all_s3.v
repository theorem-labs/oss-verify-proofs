(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the tail of sup_connect's ASan walk (plugin-hostd/fuzz_command, 0x8ad20): at
   answer's entry after the epilogue and `j answer` (0x8af0c), answer's contract (answer_c.v tanswer_spec) gives
   sup_connect's post (sup_connect_s0.v SCN_T_stmt). No instruction runs here: the machine is at BASE + AF_answer.
   answer is printf-reaching and the last step, so its contract is taken at the entry's FP state (the rounding mode
   0 of sup_connect's pre) and its apost_baseF post, with the fx' it returns, closes sup_connect's apost_baseF by
   PaFx's apost_baseF_intro.

   answer is called with c the recorded slot, the shape "resp 0" (0x21ce0, RO_lit_21ce0 of cmd_ro_ok) and
   changes = 1, on the recorder state rec_record R REC_CONNECT (scn_args ...) that the tail state holds; then
   sup_connect_m R ... = rec_answer (rec_record R REC_CONNECT A) (REC_CONNECT, A) REC_MOD_HOST_SHAPE true
   (RecModel.v:73-75, :124-126). answer's journal (from the tail state, STK = ANSWER_STK, at the entry sp) is
   joined to the walk's journal (from the entry state, SUP_CONNECT_STK) by the core's ajournal_sub_wide: g_rec's
   answer and state fields are program statics inside scn_FP, and the old answer's block is one of the recorder's
   blocks, so it is in scn_FP's ablocks_fp O or is a block the walk made. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_connect_s5.v, with its module paths and module names changed; 204 of its 244 lines of code are new or changed and 262 lines of the source are left out. *)
(* sup_remove_all's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan), the step at
   the tail jump `j answer` (0x8b458, to answer at 0x8aa10): sra_tail proves sra_tail_stmt (sup_remove_all_s2.v).
   The walk has reached answer's entry (world Wt) with the journal J1 from sup_remove_all's entry, after record()
   (0x8b440) and the frame's release; answer's contract (tanswer_spec, answer_c.v) is applied there through PaFx.v's
   cl_callS_wideF, which composes J1 with answer's journal by the core's ajournal_sub_wide (lib/Reusable/YCbq.v), and
   answer's post-condition gives sup_remove_all's. No symbolic execution. The B twin of
   lib/A/Prog/sup_remove_all_refit_s3.v (a working branch e84227c9553, the pass-4/5 re-fit of a Theorem Labs lane's 59cc4017e62).

   The B code differs from A's here in three ways: the shape "resp 0" is at 0x21d20 (RO_lit_21d20, end 0x21d26);
   a0 is record()'s return value rec_slot R, whose slot form answer asks (the call's index in the table, or the
   spill) comes from RecBridge.v's rec_slot_entry; record()'s post-condition gives the blocks it freed and its
   meter directly.

   The facts answer's premises need beyond the walk's state: the shape is a read-only literal of the image (cmd_ro_ok's
   RO_lit_21d20, cmd_ro_in_img) whose bytes no runtime entry owns and whose shadow checks (CmdChk's cmd_addr_b /
   cmd_hull_b) and end (0x21d26 in CmdRo's cmd_ro_ends) hold by computation; the frame chain at answer's entry is the
   entry's (achain_kept; s0 is the entry s0 at the tail jump); the rounding mode is the entry's (HFRM; record keeps
   the FP state); sup_remove_all's footprint lies below alloc_ceiling and holds no read-only byte (RRO, RPG,
   blk_img). Answer's footprint bytes are bytes the outer journal may write: g_rec.answer and g_rec.state are program
   statics of the image in sup_remove_all's footprint (CmdBSyms' ts_prog, cif_prog_img), the old answer's block is
   a live block of the recorder's set. The block facts of the post-condition come from AR's separation (s1). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c answer_c sup_remove_all_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain PaFx RecBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_remove_all_s1 sup_remove_all_s2 sup_remove_all_s4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the shape's bytes are neither runtime-owned nor the errno cell (CmdBSyms' owned list and errno cell) *)
Lemma bsra_shape_unowned_tfib : forall i, 0 <= i < 7 ->
  ~ Exists (in_zr (0x21d20 + i)) Tfib_owned_static /\ ~ (TFIB_ERRNO <= 0x21d20 + i < TFIB_ERRNO + 4).
Proof.
intros i Hi. split.
- intros HE. apply Exists_exists in HE as (r & Hr & Hra).
  assert (Hd : forallb (zr_disjointb (0x21d20, 7)) Tfib_owned_static = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) Hd r Hr) as Hdr. unfold zr_disjointb in Hdr. cbn [fst snd] in Hdr.
  apply orb_prop in Hdr as [Hdr | Hdr]; apply Z.leb_le in Hdr; unfold in_zr in Hra; lia.
- unfold TFIB_ERRNO. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
(* the image facts (a Theorem Labs lane's RULING-STMT.md §1 IMG, CmdRecBase's cmd_img_facts): cif_prog_img, and CmdRecRo's RRO,
   RPG, cmd_ro_in_img and cmd_ro_ok_of_aro *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.

(* a read-only byte of the image is outside sup_remove_all's footprint *)
Lemma bsra_ro_nfp : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  forall a, in_roP SEGS RLO RHI a -> ~ inFP (sra_FP O) a.
Proof.
intros ly S W mem md O HAR HO a Hro Hf.
unfold sra_FP in Hf. rewrite !inFP_cons in Hf.
destruct Hf as [Hf | [Hf | [Hf | [Hf | Hf]]]].
1-3: refine (CmdRecRo.RPG SEGS B LAWS HB IMG a _ Hro); exists (A_G_REC, A_G_REC + 960); split; [unfold cmd_PG; apply in_eq|];
  cbn [fst snd]; unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE in Hf; lia.
- refine (CmdRecRo.RPG SEGS B LAWS HB IMG a _ Hro). exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; apply in_cons, in_eq|].
  cbn [fst snd]. unfold SC_SIZE in Hf. lia.
- destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hin & Hr).
  apply (blk_img SEGS B LAWS ly S W mem md p n a HAR (HO _ Hin) Hr).
  destruct Hro as [(s & Hs & _ & Hr') | Hr']; [exists s; split; [exact Hs | exact Hr'] | exact (CmdRecRo.RRO SEGS B LAWS HB IMG a Hr')].
Qed.

(* a byte of g_rec is a program static of the image (CmdBSyms' ts_prog, cif_prog_img) *)
Lemma bsra_grec_prog : forall a, A_G_REC <= a < A_G_REC + 960 ->
  Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof.
intros a Ha. apply (sra_prog B HB IMG). exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; apply in_eq | cbn [fst snd]; lia].
Qed.

(* the shape as answer's astr_argA takes it, at any state of the record whose read-only bytes are readable: its
   bytes are read-only and unowned, and the record's shadow checks of 0x21d20 .. 0x21d26 and its end 0x21d26 hold
   by computation *)
Lemma bsra_shape_arg : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
  cmd_ro_in (in_roP SEGS RLO RHI) ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O 0x21d20 (Some REC_MOD_HOST_SHAPE) /\ fits REC_MOD_HOST_SHAPE.
Proof.
intros ly S W mem md O HAR HROK HROIN. split; [|apply Z.leb_le; vm_compute; reflexivity].
assert (HLIT : abytes_atR (rdW W mem) 0x21d20 RO_lit_21d20).
{ destruct HROK as [HRB _]. unfold cmd_ro_bytes in HRB.
  repeat match type of HRB with
  | abytes_atR _ 0x21d20 _ /\ _ => exact (proj1 HRB)
  | _ /\ _ => apply proj2 in HRB
  end. }
assert (HRO7 : forall i, 0 <= i < 7 -> in_roP SEGS RLO RHI (0x21d20 + i)).
{ unfold cmd_ro_in in HROIN.
  repeat match type of HROIN with
  | (forall i : Z, _ -> _ (0x21d20 + i)) /\ _ => exact (proj1 HROIN)
  | _ /\ _ => apply proj2 in HROIN
  end. }
assert (HSTR : astr_atR (rdW W mem) 0x21d20 REC_MOD_HOST_SHAPE).
{ split.
  - first
    [ replace (REC_MOD_HOST_SHAPE ++ [Z_to_bv 8 0]) with RO_lit_21d20 by (vm_compute; reflexivity); exact HLIT
    | intros i Hi; change (length (REC_MOD_HOST_SHAPE ++ [Z_to_bv 8 0])) with 7%nat in Hi;
      rewrite (HLIT i ltac:(change (length RO_lit_21d20) with 7%nat; exact Hi)); f_equal;
      do 7 (destruct i as [|i]; [vm_compute; reflexivity|]); lia ].
  - intros Hin. apply (in_map (fun b : byte => bv_unsigned b)) in Hin. vm_compute in Hin.
    repeat (destruct Hin as [Hin | Hin]; [discriminate Hin|]). exact Hin. }
assert (HEND : In (0x21d20 + Z.of_nat (length REC_MOD_HOST_SHAPE)) cmd_ro_ends).
{ change (0x21d20 + Z.of_nat (length REC_MOD_HOST_SHAPE)) with 0x21d26. unfold cmd_ro_ends.
  repeat (first [left; reflexivity | right]). }
assert (HUN : forall i, 0 <= i < 7 ->
  ~ Exists (in_zr (0x21d20 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21d20 + i < as_errno B + 4)).
{ intros i Hi. rewrite (ts_owned B HB), (ts_errno B HB). exact (bsra_shape_unowned_tfib i Hi). }
unfold astr_argA. cbv beta iota zeta.
change (Z.of_nat (length REC_MOD_HOST_SHAPE) + 1) with 7.
split; [lia|]. split; [exact HSTR|]. split; [unfold LMAX; lia|]. right.
split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | exact HEND]]].
intros i Hi. split; [exact (HRO7 i Hi) | exact (HUN i Hi)].
Qed.

Theorem sra_tail : sra_tail_stmt B MT.
Proof using All.
unfold sra_tail_stmt.
intros ly S W regs mem md ch R O lyc Sc Wt memT mdT regsT freed O1.
cbv zeta.
intros HPRE HFRM HFR HROD HREP HEV HLIVE HMO HJ1 HPERM HFREED HREP1 HO1 HBBc HMLE HPR HRA H10 H11 H12.
remember (snd (sup_remove_all_m R)) as t eqn:Ht0 in *.
assert (Et : snd (rec_answer (rec_record R REC_REMOVE_ALL []) (REC_REMOVE_ALL, []) REC_MOD_HOST_SHAPE true) = t)
  by (rewrite Ht0, bsra_m_eq; reflexivity).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ1 as (HART & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres1 & Hstatic & F5 & HQT1).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (WSA : ANSWER_STK <= SUP_REMOVE_ALL_STK) by (unfold SUP_REMOVE_ALL_STK; apply Z.le_max_r).
assert (WA0 : 0 <= ANSWER_STK) by (apply Z.leb_le; vm_compute; reflexivity).
(* a0: the slot record() returned, in answer's form (RecBridge.v's rec_slot_entry) *)
set (c := rec_slot R) in *.
assert (Hcb : 0 <= c < 2 ^ 64).
{ subst c. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl | Hl];
  unfold A_G_REC, A_REC_SPILL, OFF_CALLS, CALL_SIZE; lia. }
pose proof (rec_slot_entry R REC_REMOVE_ALL []) as HSLOT. fold c in HSLOT.
(* the callee-saved registers at answer's entry are the entry's *)
assert (E2 : getr regsT 2 = getr regs 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (E3 : getr regsT 3 = getr regs 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (E4 : getr regsT 4 = getr regs 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (E8 : getr regsT 8 = getr regs 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (Esp : spZ regsT = spZ regs + 0) by (unfold spZ; rewrite E2; lia).
assert (Es0 : s0Z regsT = s0Z regs) by (unfold s0Z; rewrite E8; reflexivity).
(* the recorder's blocks are live blocks, and sup_remove_all's footprint lies below alloc_ceiling *)
assert (HOlive : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hp; exact (bsra_rep_live B _ _ _ _ _ pn HREP Hp)).
assert (HO1live : forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) by (intros pn Hp; exact (bsra_rep_live B _ _ _ _ _ pn HREP1 Hp)).
assert (HO1O : forall pn, In pn O1 -> In pn O) by (intros pn Hp; exact (proj1 (proj1 (HO1 pn) Hp))).
assert (HFPB : forall a, inFP (sra_FP O) a -> 4096 <= a < alloc_ceiling).
{ apply sra_fp_bound. intros p n Hin. destruct (bsra_blk B LAWS ly S W mem md p n HAR (HOlive _ Hin)) as (B1 & B2 & _). lia. }
(* the frame chain at answer's entry: the entry's, kept above the entry sp *)
assert (HchT : achain lyc (rdW Wt memT) (spZ regs + 0) (s0Z regsT) ch).
{ rewrite Z.add_0_r, Es0. apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_kept ly (rdW W mem) (rdW Wt memT) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | zlia |].
  intros a Ha. apply F1; [zlia | lia |]. intros Hf. pose proof (HFPB a Hf). zlia. }
(* the read-only bytes at answer's entry: J1 keeps every image byte outside its footprint *)
assert (HRODT : arodata_okP SEGS RLO RHI B (rdW Wt memT)).
{ intros a Hro Ho He. rewrite (F3 a); [exact (HROD a Hro Ho He) | | exact Ho | exact He |].
  - destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (CmdRecRo.RRO SEGS B LAWS HB IMG a Hr)].
  - apply fp_spares_closed.
    + intros H0. pose proof (HFPB 0 H0). lia.
    + exact (bsra_ro_nfp ly S W mem md O HAR HOlive a Hro). }
assert (HROKT : cmd_ro_ok (rdW Wt memT)) by exact (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wt memT mdT HART HRODT).
pose proof HREP1 as (Q1 & HQ1 & HQ1O).
destruct (bsra_answer_cell _ _ _ _ HQ1) as (old & Hold & Hold').
(* old is 0 or the start of one of the recorder's blocks *)
assert (OLD : old = 0 \/ exists pn0, In pn0 O1 /\ old = fst pn0).
{ destruct Hold' as [(_ & E0) | (pn0 & Ea & E0)]; [left; exact E0|]. right. exists pn0. split; [|exact E0].
  apply HQ1O. apply bsra_in_answer. rewrite Ea. cbn [oblk]. left. reflexivity. }
assert (Hob : 0 <= old < 2 ^ 64).
{ destruct OLD as [-> | ([p a] & Hp & ->)]; [lia|]. cbn [fst].
  destruct (bsra_blk B LAWS lyc Sc Wt memT mdT p a HART (HO1live _ Hp)) as (B1 & B2 & _ & B4). lia. }
assert (Hsh : 0 <= 0x21d20 < 2 ^ 64) by lia.
pose proof (bsra_shape_arg lyc Sc Wt memT mdT O1 HART HROKT (CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG)) as HARG.
(* the premises of answer's contract at its entry *)
assert (P1 : Z.of_nat (length (frames Sc)) <= 8) by (rewrite Hfrs; exact HFR).
assert (P7 : true = negb (bv_unsigned (getr regsT 12) =? 0)) by (rewrite H12; vm_compute; reflexivity).
assert (P10 : r_refuse (rec_record R REC_REMOVE_ALL []) = 0 ->
  astr_argA B lyc Sc (rdW Wt memT) (in_roP SEGS RLO RHI) O1 0x21d20 (Some REC_MOD_HOST_SHAPE) /\ fits REC_MOD_HOST_SHAPE)
  by (intros _; exact HARG).
assert (P11 : r_refuse (rec_record R REC_REMOVE_ALL []) = 0 -> true = true ->
  (exists k, nth_error (r_calls (rec_record R REC_REMOVE_ALL [])) k = Some (REC_REMOVE_ALL, []) /\
    c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (c = A_REC_SPILL /\ (REC_REMOVE_ALL, []) = r_spill (rec_record R REC_REMOVE_ALL []))).
{ intros _ _. exact HSLOT. }
assert (P12 : st_nev Sc + EV_ANSWER <= EV_MAX) by (unfold EV_SUP_REMOVE_ALL in HEV; lia).
assert (P13 : blocks_bytes Sc + LIVE_ANSWER t <= LIVE_MAX) by (unfold LIVE_SUP_REMOVE_ALL in HLIVE; lia).
assert (HXA : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)). lia. }
assert (P14 : mo_ok MT Sc (XM_ANSWER MT t)).
{ apply (mok_station MT S Sc (XM_SUP_REMOVE_ALL MT R t) (XM_RECORD MT R) (XM_ANSWER MT t) MTL HMO HMLE HXA).
  unfold XM_SUP_REMOVE_ALL. lia. }
(* answer's contract at its entry, with its footprint FPa and its post-condition Qa *)
pose proof (TANSWER fx lyc Sc Wt regsT memT mdT ch c 0x21d20 old (REC_REMOVE_ALL, []) REC_MOD_HOST_SHAPE true
  (rec_record R REC_REMOVE_ALL []) O1) as HANS.
cbv zeta in HANS. rewrite Et in HANS.
lazymatch type of HANS with
| context [apost_baseF _ _ _ ?F _ _ _ _ _ _ _ ?Q] =>
  remember F as FPa eqn:EFPa in HANS; remember Q as Qa eqn:EQa in HANS
end.
(* every byte of answer's footprint is a byte sup_remove_all's journal may write *)
assert (HF : forall a, inFP FPa a ->
  awr_byte SEGS B SUP_REMOVE_ALL_STK (spZ regs) (sra_FP O) (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [] a).
{ intros a Ha. rewrite EFPa in Ha. rewrite !inFP_cons in Ha.
  destruct Ha as [Ha | [Ha | Ha]].
  - right; right; right; right; left. split.
    + unfold sra_FP. rewrite !inFP_cons. right; left. unfold OFF_CALLS, OFF_ANSWER in *. lia.
    + apply bsra_grec_prog. unfold OFF_ANSWER in Ha. lia.
  - right; right; right; right; left. split.
    + unfold sra_FP. rewrite !inFP_cons. right; right; left. exact Ha.
    + apply bsra_grec_prog. unfold OFF_STATE in Ha. lia.
  - destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hin & Hr). apply bsra_filter_in in Hin.
    right; left. split.
    + unfold sra_FP. rewrite !inFP_cons. right; right; right; right.
      replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp O p n (a - p)); [exact (HO1O _ Hin) | lia].
    + exists p, n. split; [exact (HO1live _ Hin) | exact Hr]. }
(* no byte of answer's footprint lies in sup_remove_all's stack window *)
assert (VIS0 : forall a, inFP FPa a -> spZ regs - SUP_REMOVE_ALL_STK <= a < spZ regs -> False).
{ intros a Ha Hw. rewrite EFPa in Ha. rewrite !inFP_cons in Ha.
  destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, OFF_ANSWER in Ha; lia | unfold A_G_REC, OFF_STATE in Ha; lia |].
  destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hin & Hr). apply bsra_filter_in in Hin.
  destruct (bsra_blk B LAWS lyc Sc Wt memT mdT p n HART (HO1live _ Hin)) as (_ & B2 & _). lia. }
unfold cfg_at.
eapply SRr_mono.
{ refine (cl_callS_wideF B LAWS Wt regsT memT (w64 (BASE + AF_answer)) SUP_REMOVE_ALL_STK (spZ regs) (sra_FP O)
    ly S W mem md [] lyc Sc mdT (EV_RECORD R) ANSWER_STK FPa EV_ANSWER 0 (getr regsT 1) ch Qa
    HJ1 Esp ltac:(reflexivity) ltac:(lia) WA0 ltac:(lia) ltac:(rewrite E3; exact Hgp) ltac:(rewrite E4; exact Htp)
    eq_refl ltac:(rewrite HRA; exact Hra) ltac:(rewrite HRA; exact Hra4) HchT
    (fun HP => HANS HP HFRM P1 HRODT HROKT H10 Hcb H11 Hsh P7 HREP1 Hold Hob P10 P11 P12 P13 P14) HF
    (fun _ _ _ _ _ _ _ a Ha Hw _ => False_ind _ (VIS0 a Ha Hw))). }
cbv beta. intros W' c' _ (fx1 & ly' & S' & regs' & mem' & md' & Hfx & Hc' & HJo & HJ2 & HPR2 & HQ).
rewrite EQa in HQ. cbv beta in HQ.
destruct HQ as (p1 & p2 & O' & G10 & G4096 & Gne & Gfr & GBL & GREP & GO & GSTR & GBB & GMLE).
pose proof HJ2 as (HAR2 & _).
(* answer returned at fx1 with fxrel fx fx1: that is sup_remove_all's apost_baseF *)
rewrite Hc', HRA.
apply (apost_baseF_intro (fx := fx) SEGS fx1 _ _ _ _ _ _ _ _ _ _ _ _ ly' S');
  [exact Hfx | replace (EV_SUP_REMOVE_ALL R) with (EV_RECORD R + EV_ANSWER) by (unfold EV_SUP_REMOVE_ALL; lia); exact HJo
  | exact (aregs_preserved_trans _ _ _ HPR HPR2) |].
unfold sra_post. cbv beta.
exists (fst (rec_answer (rec_record R REC_REMOVE_ALL []) (REC_REMOVE_ALL, []) REC_MOD_HOST_SHAPE true)), O', p2.
split; [rewrite Ht0, bsra_m_eq; apply surjective_pairing|].
cbv zeta.
assert (ND : forall pn, In pn (ablocks B lyc Sc) -> In pn freed -> False)
  by (intros pn H1 H2; exact (bsra_nodup2 B LAWS ly S W mem md (ablocks B lyc Sc) freed pn HAR HPERM H1 H2)).
assert (H0 : forall pn, In pn (ablocks B lyc Sc) -> fst pn <> 0).
{ intros [p a] Hp. destruct (bsra_blk B LAWS lyc Sc Wt memT mdT p a HART Hp) as (B1 & _). cbn [fst]. lia. }
destruct (bsra_post_blocks (ablocks B ly S) (ablocks B lyc Sc) (ablocks B ly' S') O O1 O' freed old p1 p2 _
  HPERM HFREED HO1 HO1live ND H0 OLD
  (fun p a b => bsra_same_start B LAWS lyc Sc Wt memT mdT p a b HART)
  (fun p a b => bsra_same_start B LAWS ly' S' W' mem' md' p a b HAR2)
  Gne Gfr GBL GO) as (Q1' & Q2 & Q3 & Q4 & Q5 & Q6).
split; [exact G10|]. split; [exact G4096|]. split; [exact GREP|].
split; [exact Q1'|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
split; [exact Q6|]. split; [exact GSTR|]. split; [unfold LIVE_SUP_REMOVE_ALL; lia|].
unfold XM_SUP_REMOVE_ALL. exact (mle_station MT S Sc S' _ _ MTL HMLE GMLE).
Qed.
End e.
End f.
End d.
