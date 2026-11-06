(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of the sup_broadcast walk on fuzz_command.asan-ubsan: the run
   from arg_line's return 0x8b518 to the tail jump `j answer` (0x8b538: a1 := the shape 0x21d20 by PHi/PAddHi of
   A_OBJ 42, a2 := 1, a0 := s1, the frame restored, sp += 32) over the verified symbolic executor; the state at
   answer's entry (sbb_at_ans: answer's premises, the entry's frame chain by achain_kept, PASS4-REFIT.md section B);
   the tail call through PaFx.v's cl_callS_pgF with answer_c.v's contract at the walk's FP state; and the post of
   the statement from answer's post and the block history (sup_broadcast_s2.v sbb_post_blocks). The shape of
   a Theorem Labs lane's A walk (lib/A/Prog/sup_broadcast_s3.v at a5a5ff08765) and of the worked re-fit
   lib/A/Prog/sup_remove_all_refit_s3.v (the F tail call). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_broadcast_s6.v, with its module paths and module names changed; 127 of its 175 lines of code are new or changed and 347 lines of the source are left out. *)
(* The lemmas that the B walks' calls of record() and answer() share (fuzz_command.asan-ubsan): the recorder's
   answer cell and blocks, record()'s footprint, the program's statics, the live blocks, and answer's argument
   "resp 0" (the shape REC_MOD_HOST_SHAPE at 0x21d20). They are about no single walk, so they are here once and the
   walks import them.

   Moved here with their proofs unchanged (the copies differ only in their name prefix):
   - rca_answer_cell .. rca_rep_blocks, rca_blk, rca_same_start: the B sup_remove_all walk of another branch,
     lib/B/Prog/sup_remove_all_s1.v:33-91 and :219-237 (prefix bsra_);
     rca_shape_unowned_tfib, rca_shape_arg: sup_remove_all_s3.v:48 and :106 (prefix bsra_); rca_prog:
     sup_remove_all_s4.v:83 (sra_prog). Copied with prefix sc_t_ in an earlier version of
     lib/B/Prog/sup_call_t.v:56-124 and :375-444.
   - rca_recFP, rca_in_dec, rca_HPROG, rca_sig_record: the B sup_add walk of another branch,
     lib/B/Prog/sup_add_s1a.v:189, :164, :371, :460 (prefix s1_), copied with prefix scb_ in sup_call_b.v.
   The Section lemmas sit in a Section with the Context of their source, so after End they take the same
   arguments as the copies do. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the recorder's representation (CmdRep.v arep_at) ---- *)
(* the answer cell: 0, or the start of the answer's block *)
Lemma rca_answer_cell : forall bl rd R Q,
  arep_at bl rd A_G_REC A_REC_SPILL R Q ->
  exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\
    ((l_answer Q = None /\ old = 0) \/ (exists pn, l_answer Q = Some pn /\ old = fst pn)).
Proof.
intros bl rd R Q (_ & _ & _ & _ & HA & _). unfold aanswer_at in HA.
destruct (r_answer R) as [x|] eqn:E1; destruct (l_answer Q) as [pn|] eqn:E2; rewrite ?E1, ?E2 in HA;
  cbv beta iota in HA; try contradiction.
- exists (fst pn). split; [exact (proj1 HA)|]. right. exists pn. split; reflexivity.
- exists 0. split; [exact HA|]. left. split; reflexivity.
Qed.

Lemma rca_in_answer : forall Q pn, In pn (oblk (l_answer Q)) -> In pn (lay_blocks Q).
Proof.
intros Q pn Hp. unfold lay_blocks. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. exact Hp.
Qed.

(* membership in a filter (stdpp's filter over a boolean predicate) *)
Lemma rca_filter_in : forall (f : Z * Z -> bool) (pn : Z * Z) (l : list (Z * Z)),
  In pn (filter (fun q : Z * Z => f q) l) -> In pn l.
Proof.
intros f pn l. induction l as [|q l IH]; [intros []|].
cbn. destruct (decide (f q)) as [Hq|Hq].
- intros [Heq|Hin]; [left; exact Heq | right; exact (IH Hin)].
- intros Hin. right. exact (IH Hin).
Qed.

(* a block of an argument of a recorded call, of the answer or of the reply is a live block *)
Lemma rca_call_blocks : forall bl rd a c P pn, acall_at bl rd a c P -> In pn P -> In pn bl.
Proof.
intros bl rd a c P pn (_ & _ & HL & _ & _ & _ & H7) Hin.
destruct (In_nth_error P pn Hin) as [k Hk].
assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hk; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
exact (proj1 (proj2 (proj2 (H7 k s pn Es Hk)))).
Qed.

Lemma rca_rep_blocks : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> In pn bl.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HR & _ & _) Hin.
unfold lay_blocks in Hin. apply in_app_iff in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hp).
  destruct (In_nth_error _ _ HP) as [i Hi].
  assert (Hlt : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  exact (rca_call_blocks bl rd _ c P pn (proj1 (C4 i c P Ec Hi)) Hp).
- apply in_app_iff in Hin as [Hin | Hin]; [exact (rca_call_blocks bl rd _ _ _ pn C5 Hin)|].
  apply in_app_iff in Hin as [Hin | Hin].
  + unfold aanswer_at in HA. destruct (l_answer Q) as [pa|]; cbn [oblk In] in Hin; [|destruct Hin].
    destruct Hin as [<- | []]. destruct (r_answer R); [exact (proj1 (proj2 (proj2 HA))) | exact (False_ind _ HA)].
  + unfold areply_at in HR. destruct (l_reply Q) as [pa|]; cbn [oblk In] in Hin; [|destruct Hin].
    destruct Hin as [<- | []]. destruct (r_reply R); [exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))) | exact (False_ind _ HR)].
Qed.

(* ---- record()'s footprint (record_c.v trecord_spec) ---- *)
(* g_rec's ncalls, the slot (a call of the table or the spill), and in the spill arm the recorder's blocks *)
Definition rca_recFP (R : rstate) (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
(if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O).
(* membership in a list of blocks is decidable *)
Lemma rca_in_dec : forall (pn : Z * Z) (l : list (Z * Z)), {In pn l} + {~ In pn l}.
Proof. intros pn l. apply in_dec. decide equality; apply Z.eq_dec. Qed.

(* ---- answer's argument "resp 0" ---- *)
(* the shape's bytes are neither runtime-owned nor the errno cell (CmdBSyms' owned list and errno cell) *)
Lemma rca_shape_unowned_tfib : forall i, 0 <= i < 7 ->
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
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SIGP : cmd_sig_prog.
(* the image facts (the walk hypothesis IMG, CmdRecBase's cmd_img_facts): cif_prog_img *)
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.

(* ---- the program's statics (CmdBSyms' ts_prog) ---- *)
(* g_rec and record.spill are program statics *)
Lemma rca_HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof using HB.
intros a Ha. rewrite (ts_prog B HB).
destruct Ha as (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. unfold TFIB_PROG_STATIC.
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha;
[apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd];
unfold in_zr; cbn [fst snd]; lia.
Qed.
(* a byte of the program's statics is as_prog_static B's and an image byte (cif_prog_img) *)
Lemma rca_prog : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof.
intros a Hpg. split; [|exact (CmdRecBase.cif_prog_img _ _ IMG a Hpg)].
destruct Hpg as (r & Hr & Ha). rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. cbn [In] in Hr. apply Exists_exists.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
[exists (0x5e32c0, 960) | exists (0x5e3760, 56) | exists (0x5e37e0, 4)];
(split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]).
Qed.
(* record's call target *)
Lemma rca_sig_record : SIG CS_record = BASE + AF_record.
Proof using SIGP. rewrite (SIGP CS_record); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). Qed.

(* ---- live blocks (AR_laws) ---- *)
(* a live block: its bounds and size (al_blocks) *)
Lemma rca_blk : forall ly S (W : world SEGS) mem md p n, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n /\ 1 <= req_size n.
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
pose proof (req_size_pos n ltac:(lia)). lia.
Qed.

(* two live blocks with the same start are the same block (AR's separation) *)
Lemma rca_same_start : forall ly S (W : world SEGS) mem md p a b, AR SEGS B ly S W mem md ->
  In (p, a) (ablocks B ly S) -> In (p, b) (ablocks B ly S) -> a = b.
Proof.
intros ly S W mem md p a b HAR H1 H2. destruct (Z.eq_dec a b) as [E|Hne]; [exact E|exfalso].
assert (Hd : zdisjoint (p, req_size a) (p, req_size b)).
{ apply (sep_blocks SEGS B LAWS ly S W mem md p a p b HAR H1 H2). intros E. injection E as E. exact (Hne E). }
destruct (rca_blk ly S W mem md p a HAR H1) as (_ & _ & _ & R1).
destruct (rca_blk ly S W mem md p b HAR H2) as (_ & _ & _ & R2).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ---- answer's argument "resp 0", at a state of the record ---- *)
(* the shape as answer's astr_argA takes it, at any state of the record whose read-only bytes are readable: its
   bytes are read-only and unowned, and the record's shadow checks of 0x21d20 .. 0x21d26 and its end 0x21d26 hold
   by computation *)
Lemma rca_shape_arg : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
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
{ intros i Hi. rewrite (ts_owned B HB), (ts_errno B HB). exact (rca_shape_unowned_tfib i Hi). }
unfold astr_argA. cbv beta iota zeta.
change (Z.of_nat (length REC_MOD_HOST_SHAPE) + 1) with 7.
split; [lia|]. split; [exact HSTR|]. split; [unfold LMAX; lia|]. right.
split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | exact HEND]]].
intros i Hi. split; [exact (HRO7 i Hi) | exact (HUN i Hi)].
Qed.
End e.
End f.
End d.
