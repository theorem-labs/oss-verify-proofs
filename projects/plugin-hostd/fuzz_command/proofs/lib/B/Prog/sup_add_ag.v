(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of pins_clear (plugin-hostd/fuzz_command, entry 0x8ccb4), in
   the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACke.v (the instantiation of the cgif_close walk) over
   fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/pins_clear.v, with its module paths and module names changed; 915 of its 942 lines of code are new or changed and 55 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_add_lem.v, with its module paths and module names changed; 493 of its 582 lines of code are new or changed and 853 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command: the call of arg_s that the stages M1 -> M2,
   M3 -> M4, M4 -> M5 and M5 -> M6 share (lib/B/Prog/sup_add_s2.v, sup_add_s4.v, sup_add_s5.v, sup_add_s6.v).

   saa_call composes one call of arg_s (0x8a820, lib/B/Prog/arg_s_c.v) at a state that carries sa_core, buf's
   shadow (sa_buf0), the recorder with the arguments A recorded so far in some list Ok of blocks, the block
   accounting and the meter: PaCallPg.v's cl_callS_pg (arg_s writes the slot's nargs word and args[|A|], bytes of
   g_rec or record.spill), the frame chain of s0 = sp0 from sup_add_lem.v's sa_chain_at, arg_s at the same FP state
   (its post is apost_base). After the return it hands the continuation the same facts with A ++ [sarg v], the new
   block at the head of the recorder's list and in the accounting, the budgets moved by EV_ARG_S, LIVE_ARG_S and
   XM_ARG_S; the saved registers lie above arg_s's stack window and the flag word and buf's shadow in the side-stack
   frame, none in its footprint, so the call keeps them, and the call rule keeps the callee-saved registers.

   saa_str moves a string the entry handed over (astr_argA over the recorder's blocks O at the entry) to the state of
   a later call (astr_argA over no excluded block, arg_s's string premise), through the journal from the entry: a
   heap string's block is none of O, so it is not in sa_FP O and lies off the image (not in g_rec or record.spill),
   and it is still live (sa_acct); a read-only string is shown by arodata_okP at both states. saa_dash is the
   literal "-" (0x21d80) on astr_argA's read-only arm.

   The runs from a label to the call of arg_s share saa_seed0 / saa_seed (the registers as atoms, at most the frame's
   shadow window [lo, hi) above s9 writable), saa_regs_eq (the registers a run keeps) and saa_core_kept (sa_core
   across a run that writes at most bytes of the frame's shadow). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaDenot PaLibG PaLibF PaLibH PaCall PaCallPg PaNoChain CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts RecBLemmas.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- arithmetic ---- *)
(* the realigned base s1 = sa_s1 sp0 lies 128 or 144 bytes below sp0, 32-aligned *)
Lemma saa_s1 : forall sp0, sp0 mod 16 = 0 ->
  (sa_s1 sp0 = sp0 - 128 \/ sa_s1 sp0 = sp0 - 144) /\ sa_s1 sp0 mod 32 = 0.
Proof. intros sp0 H. unfold sa_s1. split; Z.div_mod_to_equations; lia. Qed.
(* the slot record() returned: the next table slot of g_rec or record.spill, 8-aligned *)
Lemma saa_slot : forall R, rec_slot R mod 8 = 0 /\
  ((A_G_REC + OFF_CALLS <= rec_slot R /\ rec_slot R + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/ rec_slot R = A_REC_SPILL).
Proof.
intros R. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H].
- set (k := Z.of_nat (length (r_calls R))).
  assert (Hk : 0 <= k <= 15) by (unfold k; lia).
  split.
  + replace (A_G_REC + OFF_CALLS + CALL_SIZE * k) with ((771674 + 7 * k) * 8)
      by (unfold A_G_REC, OFF_CALLS, CALL_SIZE; lia).
    apply Z.mod_mul. lia.
  + left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER. lia.
- split; [reflexivity | right; reflexivity].
Qed.
(* arg_s's footprint (arg_s_c.v:120-123, m = k < 6) lies in the slot past its fn word *)
Lemma saa_fp_in : forall c k a, 0 <= k < 6 ->
  inFP [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4);
        (c + CALL_OFF_ARGS + 8 * k, c + CALL_OFF_ARGS + 8 * k + 8)] a ->
  c + 4 <= a < c + 56.
Proof.
intros c k a Hk Ha. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Ha.
apply inFP_cons in Ha as [Ha|Ha]; [lia|].
apply inFP_cons in Ha as [Ha|Ha]; [lia | destruct (inFP_nil a Ha)].
Qed.
Lemma saa_req : forall n, 1 <= n -> req_size n = n.
Proof. intros n H. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* ---- the recorder's blocks ---- *)
Lemma saa_acall_blocks : forall bl (rd : reader) a c P, acall_at bl rd a c P ->
  forall pn, In pn P -> In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) pn Hpn.
destruct (In_nth_error P pn Hpn) as [k Ek].
assert (Hk : (k < length (snd c))%nat) by (rewrite <- H3; apply nth_error_Some; rewrite Ek; discriminate).
destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
destruct (H7 k s pn Es Ek) as (_ & _ & G3 & G4 & _). split; [exact G3|lia].
Qed.
Lemma saa_lay_in : forall bl (rd : reader) gr sc R Q, arep_at bl rd gr sc R Q ->
  forall pn, In pn (lay_blocks Q) -> In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & HAn & HRp & _ & _) pn Hpn.
destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
unfold lay_blocks in Hpn. rewrite !in_app_iff in Hpn. destruct Hpn as [Hc|[Hs|[Ha|Hr]]].
- apply in_concat in Hc as (P & HP & Hin). destruct (In_nth_error _ _ HP) as [i Ei].
  assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  exact (saa_acall_blocks _ _ _ _ _ (proj1 (C4 i c P Ec Ei)) pn Hin).
- exact (saa_acall_blocks _ _ _ _ _ C5 pn Hs).
- revert HAn. unfold aanswer_at. destruct (r_answer R) as [x|]; destruct (l_answer Q) as [q|];
  cbn [oblk In] in Ha; intros HAn; try contradiction.
  destruct Ha as [<-|[]]. destruct HAn as (_ & _ & G3 & G4 & _). split; [exact G3|lia].
- revert HRp. unfold areply_at. destruct (r_reply R) as [x|]; destruct (l_reply Q) as [q|];
  cbn [oblk In] in Hr; intros HRp; try contradiction.
  destruct Hr as [<-|[]]. destruct HRp as (_ & _ & _ & G4 & G5 & G6 & _). split; [exact G5|].
  destruct x as [|b x]; [contradiction|]. cbn [length] in G6. lia.
Qed.

(* ---- registers across a run ---- *)
(* the registers sa_core names *)
Definition saa_kz : list Z := [2; 3; 4; 8; 9; 18; 19; 23; 25; 26; 27].
(* a register a run keeps, through an equation over a list of kept registers *)
Lemma saa_reg_tr : forall (zs : list Z) (r1 r2 : bvmap 5 word) (r : bv 5) (v : word) (z : Z),
  getr r1 r = v -> (forall z', In z' zs -> getr r2 (Z_to_bv 5 z') = getr r1 (Z_to_bv 5 z')) ->
  In z zs -> Z_to_bv 5 z = r -> getr r2 r = v.
Proof. intros zs r1 r2 r v z H HK Hz Hr. subst r. rewrite (HK z Hz). exact H. Qed.
Lemma saa_in_z : forall (x : Z) l, existsb (Z.eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & E). apply Z.eqb_eq in E. subst. exact Hy. Qed.
Lemma saa_no0 : forall (l : list byte), forallb (fun b => negb (bv_unsigned b =? 0)) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
induction l as [|b l IH]; intros H Hin; [destruct Hin|].
cbn [forallb] in H. apply andb_true_iff in H as [H1 H2].
destruct Hin as [-> | Hin]; [vm_compute in H1; discriminate | exact (IH H2 Hin)].
Qed.
(* picks the conjunct of H that is the goal *)
Ltac saa_pick H :=
  match goal with |- ?G =>
    let rec go h :=
      lazymatch type of h with
      | G /\ _ => exact (proj1 h)
      | _ /\ _ => go constr:(proj2 h)
      | G => exact h
      end in
    go H
  end.
Ltac saa_kr HK H z :=
  refine (saa_reg_tr _ _ _ _ _ z H HK _ _); [apply saa_in_z; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity].
(* the kept registers of a run: the same symbolic value before and after, under the same environment *)
Lemma saa_regs_eq : forall E (sr1 sr2 : list sv) (regsA regsB : bvmap 5 word) (zs : list Z),
  (forall r, getr regsA r = sv_denot E (sr_get sr1 r)) ->
  (forall r, getr regsB r = sv_denot E (sr_get sr2 r)) ->
  forallb (fun z => sv_eqb (sr_get sr2 (Z_to_bv 5 z)) (sr_get sr1 (Z_to_bv 5 z))) zs = true ->
  forall z, In z zs -> getr regsB (Z_to_bv 5 z) = getr regsA (Z_to_bv 5 z).
Proof.
intros E sr1 sr2 regsA regsB zs HA HB' Hb z Hz. rewrite HA, HB'.
pose proof (proj1 (forallb_forall _ _) Hb z Hz) as Hz'. cbv beta in Hz'. apply sv_eqb_eq in Hz'. rewrite Hz'.
reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Section f. Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e. Variable B : asyms. Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO. #[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.

Lemma saa_rep_blocks : forall ly S rd R O, rec_repA B ly S rd R O ->
  forall pn, In pn O -> In pn (ablocks B ly S) /\ 1 <= snd pn.
Proof using Type.
intros ly S rd R O (Q & HQ & HO) pn Hpn. exact (saa_lay_in _ _ _ _ _ _ HQ pn (proj1 (HO pn) Hpn)).
Qed.

(* a byte of the slot: in sup_add's footprint, a program static of the record, an image byte, in g_rec or
   record.spill *)
Lemma saa_slot_byte : forall R (O : list (Z * Z)) a, rec_slot R <= a < rec_slot R + CALL_SIZE ->
  inFP (sa_FP O) a /\ Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a /\
  (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Proof using HB IMG.
intros R O a Ha. rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC.
destruct (saa_slot R) as [_ [[H1 H2] | Hs]].
- assert (Hg : A_G_REC + OFF_CALLS <= a < A_G_REC + OFF_ANSWER) by (unfold CALL_SIZE in *; lia).
  unfold A_G_REC, OFF_CALLS, OFF_ANSWER in Hg.
  split; [|split; [|split]].
  + unfold sa_FP. apply inFP_cons. right. apply inFP_cons. left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER. lia.
  + apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply (cif_prog_img _ _ IMG). unfold cmd_PG. apply inFP_cons. left. unfold A_G_REC. lia.
  + left. unfold A_G_REC, REC_SIZE. lia.
- rewrite Hs in Ha. unfold A_REC_SPILL, CALL_SIZE in Ha.
  split; [|split; [|split]].
  + unfold sa_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left.
    unfold A_REC_SPILL, SC_SIZE. lia.
  + apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
  + apply (cif_prog_img _ _ IMG). unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. left. unfold A_REC_SPILL. lia.
  + right. unfold A_REC_SPILL, SC_SIZE. lia.
Qed.

(* the uri at the entry (sa_uri: Some u in a live block apart from the recorder's) as astr_argA's block arm *)
Lemma saa_uri : forall ly S (W : world SEGS) mem md O pu uri, AR SEGS B ly S W mem md ->
  sa_uri B ly S (rdW W mem) O pu uri ->
  exists u, uri = Some u /\ astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pu (Some u).
Proof using LAWS.
intros ly S W mem md O pu uri HAR HU. destruct uri as [u|]; [|destruct HU].
exists u. split; [reflexivity|].
destruct HU as (Hblk & Hap & Hstr & Hn). pose proof Hblk as (b & kk & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS ly S W mem md b kk HAR Hbin) as (_ & H4 & _).
unfold astr_argA. cbv beta iota zeta.
refine (conj _ (conj Hstr (conj Hn (or_introl (conj Hblk Hap))))). lia.
Qed.

(* arodata_okP from the entry to a later state of the walk *)
Lemma saa_aro : forall STK sp0 own ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc k R O,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  rec_repA B ly S (rdW W mem) R O ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof using HB LAWS IMG.
intros STK sp0 own ly S W mem md lyc Sc Wc memc mdc k R O HAR HJ HREP HR.
apply (cmd_rodata_kept SEGS B LAWS HB IMG ly S W mem md lyc Sc Wc memc mdc STK sp0 (sa_FP O) own k HAR HJ); [|exact HR].
intros a Ha. unfold sa_FP in Ha. unfold TFIB_PROG_STATIC.
apply inFP_cons in Ha as [Ha|Ha];
  [left; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_G_REC, OFF_NCALLS in Ha; lia|].
apply inFP_cons in Ha as [Ha|Ha];
  [left; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER in Ha; lia|].
apply inFP_cons in Ha as [Ha|Ha];
  [left; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_G_REC, OFF_STATE in Ha; lia|].
apply inFP_cons in Ha as [Ha|Ha];
  [left; apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_REC_SPILL, SC_SIZE in Ha; lia|].
right. destruct Ha as (r & Hr & Hr1 & Hr2). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm).
cbn [fst snd] in Hr1, Hr2.
exists q, m. split; [apply in_or_app; left; exact (proj1 (saa_rep_blocks _ _ _ _ _ HREP (q, m) Hqm)) | lia].
Qed.

(* a string the entry handed over (astr_argA over the recorder's blocks O), at a later state of the walk, as
   arg_s's string premise asks it (no block excluded) *)
Lemma saa_str : forall STK sp0 own ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc k R O p x,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  rec_repA B ly S (rdW W mem) R O ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc) ->
  (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x) ->
  astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] p (Some x).
Proof using HB LAWS IMG.
intros STK sp0 own ly S W mem md lyc Sc Wc memc mdc k R O p x HAR HJ HREP HR0 HR1 HLIVE HS.
pose proof (saa_rep_blocks ly S (rdW W mem) R O HREP) as HOb.
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct HS as (Hp0 & Hstr & Hn & [(Hblk & Hap) | (Hro & Hca & Hch & Hend)]).
- (* in a live block apart from the recorder's *)
  destruct Hblk as (b & kk & Hbin & Hb1 & Hb2).
  assert (Hnot : ~ In (b, kk) O).
  { intros H. pose proof (proj1 (Forall_forall _ _) Hap (b, kk) H) as Hiv. cbn [fst snd] in Hiv.
    unfold iv_apart in Hiv. lia. }
  pose proof (HLIVE (b, kk) Hbin Hnot) as HL1.
  assert (Hkk : req_size kk = kk) by (apply saa_req; lia).
  assert (KP : forall y, p <= y < p + Z.of_nat (length x) + 1 -> rdW Wc memc y = rdW W mem y).
  { intros y Hy. replace y with (b + (y - b)) by lia.
    apply (F2 b kk (y - b) Hbin HL1); [rewrite Hkk; lia|].
    replace (b + (y - b)) with y by lia.
    assert (Hni : ~ in_img SEGS y).
    { intros Himg. refine (proj2 (al_client_img _ _ LAWS ly S W mem md y HAR
        (or_introl (ex_intro _ b (ex_intro _ kk (conj Hbin _))))) Himg). rewrite Hkk. lia. }
    unfold sa_FP. intros H.
    apply inFP_cons in H as [H|H];
      [apply Hni; apply (cif_prog_img _ _ IMG); unfold cmd_PG; apply inFP_cons; left;
       unfold A_G_REC, OFF_NCALLS in *; lia|].
    apply inFP_cons in H as [H|H];
      [apply Hni; apply (cif_prog_img _ _ IMG); unfold cmd_PG; apply inFP_cons; left;
       unfold A_G_REC, OFF_CALLS, OFF_ANSWER in *; lia|].
    apply inFP_cons in H as [H|H];
      [apply Hni; apply (cif_prog_img _ _ IMG); unfold cmd_PG; apply inFP_cons; left;
       unfold A_G_REC, OFF_STATE in *; lia|].
    apply inFP_cons in H as [H|H];
      [apply Hni; apply (cif_prog_img _ _ IMG); unfold cmd_PG; apply inFP_cons; right; apply inFP_cons; left;
       unfold A_REC_SPILL, SC_SIZE in *; lia|].
    destruct H as (r & Hr & Hr1 & Hr2). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm).
    cbn [fst snd] in Hr1, Hr2. destruct (HOb (q, m) Hqm) as (_ & Hm). cbn [snd] in Hm.
    rewrite (saa_req m Hm) in Hr2.
    pose proof (proj1 (Forall_forall _ _) Hap (q, m) Hqm) as Hiv. cbn [fst snd] in Hiv. unfold iv_apart in Hiv. lia. }
  unfold astr_argA. cbv beta iota zeta.
  refine (conj Hp0 (conj (astr_atR_kept_r (rdW W mem) (rdW Wc memc) p x KP Hstr)
    (conj Hn (or_introl (conj _ (Forall_nil _)))))).
  exact (ex_intro _ b (ex_intro _ kk (conj HL1 (conj Hb1 Hb2)))).
- (* read-only: the bytes are the image's at both states *)
  assert (KP : forall y, p <= y < p + Z.of_nat (length x) + 1 -> rdW Wc memc y = rdW W mem y).
  { intros y Hy. destruct (Hro (y - p) ltac:(lia)) as (H1 & H2 & H3).
    replace y with (p + (y - p)) by lia. rewrite (HR1 _ H1 H2 H3), (HR0 _ H1 H2 H3). reflexivity. }
  unfold astr_argA. cbv beta iota zeta.
  exact (conj Hp0 (conj (astr_atR_kept_r (rdW W mem) (rdW Wc memc) p x KP Hstr)
    (conj Hn (or_intror (conj Hro (conj Hca (conj Hch Hend))))))).
Qed.

(* the literal "-" (0x21d80, sup_add's default for a NULL placement or client): astr_argA's read-only arm at any
   state with cmd_ro_ok; its record checks are computed *)
Lemma saa_dash : forall ly S (W : world SEGS) mem, cmd_ro_ok (rdW W mem) ->
  astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] SA_DASH (Some (bstr "-"%string)).
Proof using HB LAWS IMG.
intros ly S W mem [Hby _].
assert (HB1 : abytes_atR (rdW W mem) 0x21d80 RO_lit_21d80) by (unfold cmd_ro_bytes in Hby; saa_pick Hby).
assert (HI1 : forall i, 0 <= i < 2 -> in_roP SEGS RLO RHI (0x21d80 + i)).
{ pose proof (cmd_ro_in_img SEGS B LAWS HB IMG) as Hin. unfold cmd_ro_in in Hin. saa_pick Hin. }
assert (HU1 : forall i, 0 <= i < 2 ->
  ~ Exists (in_zr (0x21d80 + i)) (as_owned_static B) /\ ~ (as_errno B <= 0x21d80 + i < as_errno B + 4)).
{ pose proof (cif_ro_unowned _ _ IMG) as Hun. unfold cmd_ro_in in Hun. cbv beta in Hun. saa_pick Hun. }
unfold astr_argA, SA_DASH.
refine (conj _ (conj (conj HB1 _) (conj _ (or_intror (conj _ (conj _ (conj _ _))))))).
- discriminate.
- apply saa_no0. vm_compute. reflexivity.
- vm_compute. discriminate.
- intros i Hi. exact (conj (HI1 i Hi) (HU1 i Hi)).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- apply saa_in_z. vm_compute. reflexivity.
Qed.

(* the block accounting after the block arg_s made joins the recorder's list *)
Lemma saa_acct_step : forall ly S O lyc Sc Ok live ly1 S1 p n live',
  sa_acct B ly S O lyc Sc Ok live ->
  Permutation (ablocks B ly1 S1) ((p, n) :: ablocks B lyc Sc) ->
  Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B lyc Sc) -> 1 <= n ->
  blocks_bytes S1 <= blocks_bytes Sc + live' ->
  sa_acct B ly S O ly1 S1 ((p, n) :: Ok) (live + live').
Proof using Type.
intros ly S O lyc Sc Ok live ly1 S1 p n live' (A1 & A2 & A3 & A4 & A5) HP HF Hn Hbb.
assert (Hin1 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly1 S1))
  by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact HP | right; exact Hpn]).
assert (Hnew : In (p, n) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
split; [|split; [|split; [|split]]].
- intros pn [<- | Hpn]; [|exact (A1 pn Hpn)].
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) O) as [Hi | Hi];
  [left; exact Hi | right].
  intros Hin. pose proof (A3 (p, n) Hin Hi) as Hc.
  pose proof (proj1 (Forall_forall _ _) HF (p, n) Hc) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
- intros pn Hpn. eapply Permutation_in in Hpn; [|exact HP]. destruct Hpn as [<- | Hpn].
  + right. left. reflexivity.
  + destruct (A2 pn Hpn) as [Hk | Hk]; [left; exact Hk | right; right; exact Hk].
- intros pn Hpn Hno. apply Hin1. exact (A3 pn Hpn Hno).
- intros pn [<- | Hpn]; [exact Hnew | apply Hin1; exact (A4 pn Hpn)].
- lia.
Qed.

(* the budgets the walk spends up to M2, M4, M5 and M6 are within the statement's (sup_add_c.v EV_SUP_ADD,
   LIVE_SUP_ADD, XM_SUP_ADD) *)
Lemma saa_budgets : forall R uri id placement client,
  let t := snd (sup_add_m R uri id placement client) in
  sa_ev2 R <= EV_SUP_ADD R /\ sa_ev4 R <= EV_SUP_ADD R /\ sa_ev5 R <= EV_SUP_ADD R /\ sa_ev6 R <= EV_SUP_ADD R /\
  sa_live2 uri <= LIVE_SUP_ADD uri id placement client t /\ sa_live4 uri id <= LIVE_SUP_ADD uri id placement client t /\
  sa_live5 uri id placement <= LIVE_SUP_ADD uri id placement client t /\
  sa_live6 uri id placement client <= LIVE_SUP_ADD uri id placement client t /\
  sa_acc2 MT R uri <= XM_SUP_ADD MT R uri id placement client t /\
  sa_acc4 MT R uri id <= XM_SUP_ADD MT R uri id placement client t /\
  sa_acc5 MT R uri id placement <= XM_SUP_ADD MT R uri id placement client t /\
  sa_acc6 MT R uri id placement client <= XM_SUP_ADD MT R uri id placement client t.
Proof using MTL.
intros R uri id placement client t.
assert (XA : forall x, 0 <= XM_ARG_S MT x)
  by (intros x; unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC; apply (mo_malloc_nonneg MT MTL); lia).
assert (XH : 0 <= XM_HAND_BACK MT t).
{ unfold XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)). lia. }
assert (XM : 0 <= Z.max (XM_ANSWER MT t) (XM_HAND_BACK MT t)) by lia.
assert (LM : 0 <= Z.max (LIVE_ANSWER t) (LIVE_HAND_BACK t))
  by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
assert (LA : forall x, 1 <= LIVE_ARG_S x) by (intros x; unfold LIVE_ARG_S, LIVE_XMALLOC; lia).
assert (EM : 0 <= Z.max EV_ANSWER EV_HAND_BACK) by (vm_compute; discriminate).
assert (EA : EV_ARG_S = 1) by reflexivity.
pose proof (XA (Some (dec id))) as X1. pose proof (XA (Some (darg placement (bstr "-"%string)))) as X2.
pose proof (XA (Some (darg client (bstr "-"%string)))) as X3.
pose proof (LA (Some (dec id))) as L1. pose proof (LA (Some (darg placement (bstr "-"%string)))) as L2.
pose proof (LA (Some (darg client (bstr "-"%string)))) as L3.
unfold sa_ev6, sa_ev5, sa_ev4, sa_ev2, sa_ev1, EV_SUP_ADD, sa_live6, sa_live5, sa_live4, sa_live2, LIVE_SUP_ADD,
  sa_acc6, sa_acc5, sa_acc4, sa_acc2, sa_acc1, XM_SUP_ADD.
repeat split; lia.
Qed.

(* sa_core across a run that writes at most the bytes Zs of the frame's shadow and keeps the registers sa_core names *)
Lemma saa_core_kept : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md O lyc Sc (Wc : world SEGS)
  (regsA regsB : bvmap 5 word) memA mdA memB mdB ev pos (Zs : Z -> Prop),
  sa_core B ly S W regs mem md O lyc Sc Wc regsA memA mdA ev pos ->
  ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memB mdB ev ->
  (forall a, Zs a -> shadow_addr (frame_addr lyc 1 pos) <= a < shadow_addr (frame_addr lyc 1 pos) + 16) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> rdW Wc memB a = rdW Wc memA a) ->
  (forall z, In z saa_kz -> getr regsB (Z_to_bv 5 z) = getr regsA (Z_to_bv 5 z)) ->
  sa_core B ly S W regs mem md O lyc Sc Wc regsB memB mdB ev pos.
Proof using LAWS.
intros ly S W regs mem md O lyc Sc Wc regsA regsB memA mdA memB mdB ev pos Zs HC HJB HZ KM KR.
unfold sa_core in HC |- *. cbv zeta in HC |- *.
destruct HC as (HJ & HFRAME & HFLAG & A2 & A3 & A4 & A8 & A9 & A18 & A19 & A23 & A25 & A26 & A27).
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (saa_s1 (spZ regs) Hal16) as [Hs1v _].
assert (Hin1pos : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memA mdA 1 pos HARc Hin1pos) as (HF0 & HFc & HFapp).
change (fs_frame_bytes 1) with 128 in HFc, HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (Hdm : frame_addr lyc 1 pos = 8 * (frame_addr lyc 1 pos / 8) + frame_addr lyc 1 pos mod 8)
  by (apply Z.div_mod; lia).
assert (Hmb : 0 <= frame_addr lyc 1 pos mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (HSTK : forall a, sa_s1 (spZ regs) <= a < spZ regs -> rdW Wc memB a = rdW Wc memA a).
{ intros a Ha. apply KM; [lia|]. intros HZa. pose proof (HZ a HZa) as Hr. unfold shadow_addr, SHADOW_OFF in Hr. lia. }
assert (HFR : forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 -> rdW Wc memB a = rdW Wc memA a).
{ intros a Ha. apply KM; [lia|]. intros HZa. pose proof (HZ a HZa) as Hr. unfold shadow_addr, SHADOW_OFF in Hr. lia. }
split; [exact HJB|].
split.
{ intros j r Hj.
  assert (Hjlt : (j < 13)%nat) by (apply (proj1 (nth_error_Some sa_saved j)); rewrite Hj; discriminate).
  apply (aval_mem_kept_r (rdW Wc memA)); [|exact (HFRAME j r Hj)].
  intros y Hy. apply HSTK. lia. }
split; [unfold rdword in HFLAG |- *; change (fs_frame_bytes 1) with 128 in HFLAG |- *; rewrite !HFR by lia; exact HFLAG|].
split; [saa_kr KR A2 2|]. split; [saa_kr KR A3 3|]. split; [saa_kr KR A4 4|].
split; [saa_kr KR A8 8|]. split; [saa_kr KR A9 9|]. split; [saa_kr KR A18 18|].
split; [saa_kr KR A19 19|]. split; [saa_kr KR A23 23|]. split; [saa_kr KR A25 25|].
split; [saa_kr KR A26 26|]. saa_kr KR A27 27.
Qed.
(* buf's shadow across a run that keeps its four bytes *)
Lemma saa_buf0_kept : forall (rd rd' : reader) F, sa_buf0 rd F ->
  (forall i, 0 <= i < 4 -> rd' (SHADOW_OFF + F / 8 + 8 + i) = rd (SHADOW_OFF + F / 8 + 8 + i)) -> sa_buf0 rd' F.
Proof using Type. intros rd rd' F H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

(* ---- seeds: the symbolic state at a program point of the walk, the registers as atoms ---- *)
(* the frame's shadow window [lo, hi) above s9 (atom 25), writable, no chunks *)
Definition saa_shr (lo hi : Z) : YP09.region := YP09.mkRegion (Some 25%nat) lo hi lo hi [].
Lemma saa_seed0 : forall (W : world SEGS) (regs1 : bvmap 5 word) memc pcz (G : facts),
  facts_ok (Eimg (Ereg regs1 [])) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) (mkSS pcz sr_atoms [] None G)
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pcz)) memc (seg_rom SEGS))).
Proof using Type.
intros W regs1 memc pcz G HG.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- exact HG.
Qed.
Lemma saa_seed : forall lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc pos pcz lo hi (G : facts),
  AR SEGS B lyc Sc Wc memc mdc -> In (1, pos) (frames Sc) ->
  getr regs1 25 = w64 (SHADOW_OFF + frame_addr lyc 1 pos / 8) ->
  0 <= lo -> hi <= 16 -> regions_wf [saa_shr lo hi] = true ->
  facts_ok (Eimg (Ereg regs1 [])) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) (mkSS pcz sr_atoms [saa_shr lo hi] None G)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pcz)) memc (seg_rom SEGS))).
Proof using LAWS.
intros lyc Sc Wc regs1 memc mdc pos pcz lo hi G HAR Hin R25 Hlo Hhi Hwf HG.
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 1 pos HAR Hin) as (_ & _ & _ & HFSpres).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 pos HAR Hin) as (HF0 & HFc & _).
change (fs_frame_bytes 1) with 128 in HFc. change (fs_frame_bytes 1 / 8) with 16 in HFSpres.
pose proof asan_consts as (C1 & _).
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as HF8.
assert (HF8h : frame_addr lyc 1 pos / 8 < 2 ^ 60) by (apply Z.div_lt_upper_bound; lia).
assert (U25 : bv_unsigned (ew (Eimg (Ereg regs1 [])) 25) = SHADOW_OFF + frame_addr lyc 1 pos / 8).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 [] 25 25%bv eq_refl), R25.
  apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact Hwf.
- constructor; [|constructor].
  unfold region_ok, saa_shr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U25. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|].
  split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS).
  destruct (HFSpres o ltac:(lia)) as (Hp & _). unfold shadow_addr in Hp. exact Hp.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- exact HG.
Qed.

(* ---- the call ---- *)
Local Ltac saa_cs := unfold acallee_saved;
  match goal with |- context[bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

(* one call of arg_s at a state of the walk: c = rec_slot R in a0, the string s in a1, the return address
   BASE + retk in ra; the continuation gets the state after the return *)
Lemma saa_call : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch pu id pp pc uri placement client R O
  lyc Sc (Wc : world SEGS) (regsA : bvmap 5 word) memA mdA pos (A : list (list byte)) Ok ev acc live s v retk,
  sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
  sa_core B ly S W regs mem md O lyc Sc Wc regsA memA mdA ev pos ->
  sa_buf0 (rdW Wc memA) (frame_addr lyc 1 pos) ->
  rec_repA B lyc Sc (rdW Wc memA) (rec_record R REC_ADD A) Ok ->
  (length A < 6)%nat ->
  sa_acct B ly S O lyc Sc Ok live ->
  mo_le MT S Sc acc ->
  getr regsA 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsA 10 = w64 (rec_slot R) -> getr regsA 11 = w64 s ->
  (astr_argA B lyc Sc (rdW Wc memA) (in_roP SEGS RLO RHI) [] s v \/
   (exists x, v = Some x /\ astr_atR (rdW Wc memA) s x /\ Z.of_nat (length x) + 1 <= LMAX + 1 /\
    afobj SEGS B lyc Sc Wc memA s (Z.of_nat (length x) + 1))) ->
  (forall x, v = Some x -> atail_vis SEGS Wc memA (s + Z.of_nat (length x))) ->
  ev + EV_ARG_S <= EV_SUP_ADD R ->
  live + LIVE_ARG_S v <= LIVE_SUP_ADD uri id placement client (snd (sup_add_m R uri id placement client)) ->
  acc + XM_ARG_S MT v <= XM_SUP_ADD MT R uri id placement client (snd (sup_add_m R uri id placement client)) ->
  (forall ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2 O2,
     sa_core B ly S W regs mem md O ly2 S2 W2 regs2 mem2 md2 (ev + EV_ARG_S) pos ->
     aregs_preserved regsA regs2 -> frame_addr ly2 1 pos = frame_addr lyc 1 pos ->
     sa_buf0 (rdW W2 mem2) (frame_addr ly2 1 pos) ->
     rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R REC_ADD (A ++ [sarg v])) O2 ->
     sa_acct B ly S O ly2 S2 O2 (live + LIVE_ARG_S v) ->
     mo_le MT S S2 (acc + XM_ARG_S MT v) ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2)
       (sa_final B MT ly S W regs mem md R O uri id placement client)) ->
  SRr SEGS Wc (mkCfg (mkst regsA (Z_to_bv 64 (SIG CS_arg_s)) memA (seg_rom SEGS)) mdA)
    (sa_final B MT ly S W regs mem md R O uri id placement client).
Proof using HB LAWS MTL SIGP IMG TARG_S.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regsA memA mdA pos A Ok ev acc live s v
  retk HCX HCORE HBUF HREP Hlen HACCT HMLE Hra Hrk1 Hrk2 Ha0 Ha1 HSTR HTAIL HEVb HLIVEb HACCb KONT.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & Hfr7 & HROD & HRO & H10 & Hpu & H11 & Hid & H12 & Hpp & H13 & Hpc & HU & HP & HPT &
  HC & HCT & HREP0 & Hev & Hlive & MOK).
unfold sa_core in HCORE. cbv zeta in HCORE.
destruct HCORE as (HJ & HFRAME & HFLAG & A2 & A3 & A4 & A8 & A9 & A18 & A19 & A23 & A25 & A26 & A27).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as (HB0 & HB1 & HB4).
set (sp0 := spZ regs) in *.
destruct (saa_s1 sp0 Hal16) as [Hs1v Hs1a].
assert (HSTKa : ARG_S_STK + 144 <= SUP_ADD_STK /\ 0 <= ARG_S_STK) by (vm_compute; split; discriminate).
assert (Hs1r : 0 <= sa_s1 sp0 < 2 ^ 64) by lia.
assert (Hspa : spZ regsA = sp0 + (sa_s1 sp0 - sp0))
  by (unfold spZ at 1; rewrite A2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hal : (sa_s1 sp0 - sp0) mod 16 = 0).
{ destruct Hs1v as [Hv | Hv]; rewrite Hv;
  [replace (sp0 - 128 - sp0) with (-128) by lia | replace (sp0 - 144 - sp0) with (-144) by lia]; reflexivity. }
assert (HSIG : SIG CS_arg_s = BASE + AF_arg_s).
{ rewrite (SIGP CS_arg_s); [reflexivity|]. cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right]). }
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrsc & Hnevc & _).
assert (Hin1pos : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (sa_chain_at B LAWS ly S W regs mem md ch R O lyc Sc Wc memA mdA ev pos (sa_s1 sp0) HPRE HREP0 HJ HFRAME
  ltac:(lia)) as [ch1 HCH].
assert (HCH' : achain lyc (rdW Wc memA) (sp0 + (sa_s1 sp0 - sp0)) (s0Z regsA) ch1).
{ unfold s0Z. rewrite A8. unfold w64. rewrite unsigned_lit_small by lia.
  replace (sp0 + (sa_s1 sp0 - sp0)) with (sa_s1 sp0) by lia. exact HCH. }
assert (HARO : arodata_okP SEGS RLO RHI B (rdW Wc memA))
  by exact (saa_aro SUP_ADD_STK sp0 [(1, pos)] ly S W mem md lyc Sc Wc memA mdA ev R O HAR0 HJ HREP0 HROD).
assert (HROOK : cmd_ro_ok (rdW Wc memA)) by exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc memA mdA HARc HARO).
pose proof HACCT as (_ & _ & _ & ACC4 & ACC5).
assert (HMXEV : 0 <= Z.max EV_ANSWER EV_HAND_BACK) by (vm_compute; discriminate).
assert (HEVc : st_nev Sc + EV_ARG_S <= EV_MAX) by lia.
assert (HLIVEc : blocks_bytes Sc + LIVE_ARG_S v <= LIVE_MAX) by lia.
assert (HXnn : 0 <= XM_ARG_S MT v)
  by (unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC; apply (mo_malloc_nonneg MT MTL); lia).
assert (HMOKc : mo_ok MT Sc (XM_ARG_S MT v))
  by exact (mok_station MT S Sc (XM_SUP_ADD MT R uri id placement client (snd (sup_add_m R uri id placement client)))
    acc (XM_ARG_S MT v) MTL MOK HMLE HXnn HACCb).
assert (Hret : YK0s.ret_ok (Z_to_bv 64 (BASE + retk))) by (apply ret_ok_codeptr_v; [lia | exact Hrk2]).
assert (Hret4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + retk))) by (rewrite unsigned_lit_small by lia; lia).
assert (Hlen6 : Z.of_nat (length A) < REC_ARGS_MAX) by (unfold REC_ARGS_MAX; lia).
set (k := Z.of_nat (length A)) in *.
set (FP1 := [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
             (rec_slot R + CALL_OFF_ARGS + 8 * k, rec_slot R + CALL_OFF_ARGS + 8 * k + 8)]).
assert (HFP1 : forall a, inFP FP1 a -> rec_slot R + 4 <= a < rec_slot R + 56)
  by (intros a Ha; exact (saa_fp_in (rec_slot R) k a ltac:(unfold REC_ARGS_MAX in Hlen6; lia) Ha)).
assert (HFP1b : forall a, inFP FP1 a -> a < alloc_ceiling).
{ intros a Ha. pose proof (HFP1 a Ha). destruct (saa_slot R) as [_ [[H1 H2] | Hs]];
  unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, A_REC_SPILL in *; lia. }
set (Kp := fun (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte)
    (md' : Model) =>
  blocks_bytes S' <= blocks_bytes Sc + LIVE_ARG_S v /\
  mo_le MT Sc S' (XM_ARG_S MT v) /\
  ((Z.of_nat (length A) = REC_ARGS_MAX /\ Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\
    rec_repA B ly' S' (rdW W' mem') (rec_record R REC_ADD A) Ok) \/
   (Z.of_nat (length A) < REC_ARGS_MAX /\ exists p,
     let n := Z.of_nat (length (sarg v)) + 1 in
     4096 <= p < 2 ^ 64 /\
     Permutation (ablocks B ly' S') ((p, n) :: ablocks B lyc Sc) /\
     Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B lyc Sc) /\
     rec_repA B ly' S' (rdW W' mem') (rec_record R REC_ADD (A ++ [sarg v])) ((p, n) :: Ok)))).
assert (HT : afn_pre SEGS B ARG_S_STK lyc Sc Wc regsA memA mdA ch1 ->
  SRr SEGS Wc (mkCfg (mkst regsA (Z_to_bv 64 (SIG CS_arg_s)) memA (seg_rom SEGS)) mdA)
    (apost_base SEGS B ARG_S_STK FP1 regsA lyc Sc Wc memA mdA EV_ARG_S Kp)).
{ intros HPRE1. rewrite HSIG.
  pose proof (TARG_S fx lyc Sc Wc regsA memA mdA ch1 (rec_slot R) s REC_ADD A v R Ok HPRE1 HARO HROOK Ha0 Ha1
    eq_refl HREP HSTR HTAIL HEVc HLIVEc HMOKc) as HT0.
  fold k in HT0. rewrite (proj2 (Z.ltb_lt _ _) Hlen6) in HT0. exact HT0. }
eapply SRr_bind.
{ apply (cl_callS_pg B LAWS Wc regsA memA (Z_to_bv 64 (SIG CS_arg_s)) SUP_ADD_STK sp0 (sa_FP O)
    ly S W mem md [(1, pos)] lyc Sc mdA ev ARG_S_STK FP1 EV_ARG_S (sa_s1 sp0 - sp0)
    (Z_to_bv 64 (BASE + retk)) ch1 Kp HJ Hspa Hal ltac:(lia) ltac:(lia) ltac:(lia) A3 A4 Hra Hret Hret4 HCH').
  - intros HPRE1. eapply SRr_mono; [exact (HT HPRE1)|].
    cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HK3).
    exists ly3, S3, regs3, mem3, md3. split; [rewrite Hra; reflexivity|]. split; [exact HJ3|].
    split; [exact HP3 | exact HK3].
  - intros a Ha. left. pose proof (HFP1 a Ha) as Hr.
    destruct (saa_slot_byte R O a ltac:(unfold CALL_SIZE; lia)) as (H1 & H2 & H3 & _).
    split; [exact H1 | right; exact (conj H2 H3)]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJout & HJin & HPres & HK).
unfold Kp in HK. destruct HK as (Hbb & Hmle & [(Hm6 & _) | (_ & p & HK1)]); [lia|].
cbv zeta in HK1. destruct HK1 as (Hp & HPerm & Hfresh & HREP2).
(* back at the return address *)
pose proof HJin as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & K4 & _).
assert (EF : frame_addr ly2 1 pos = frame_addr lyc 1 pos)
  by (pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _); unfold frame_addr; rewrite EF; reflexivity).
assert (EFl : flag_addr ly2 1 pos = flag_addr lyc 1 pos)
  by (pose proof Hly2 as (_ & _ & _ & _ & _ & EF' & _); unfold flag_addr; rewrite EF'; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memA mdA 1 pos HARc Hin1pos) as (HF0 & HFc & _).
assert (HFB : fs_frame_bytes 1 = 128) by reflexivity.
rewrite HFB in HFc.
assert (HF8 : 0 <= frame_addr lyc 1 pos / 8) by (apply Z.div_pos; lia).
assert (HF8h : frame_addr lyc 1 pos / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
assert (KSTK : forall a, sa_s1 sp0 <= a < sp0 -> rdW W2 mem2 a = rdW Wc memA a).
{ intros a Ha. apply K1; [lia | lia | intros HaF; pose proof (HFP1b a HaF); lia]. }
assert (KFR : forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 -> rdW W2 mem2 a = rdW Wc memA a).
{ intros a Ha. apply (K4 1 pos a Hin1pos); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFB; lia|].
  intros HaF. pose proof (HFP1b a HaF) as Hlo. pose proof (HFP1 a HaF) as Hr.
  apply (frm_img SEGS B LAWS lyc Sc Wc memA mdA 1 pos a HARc Hin1pos ltac:(rewrite HFB; lia)).
  destruct (saa_slot_byte R O a ltac:(unfold CALL_SIZE; lia)) as (_ & _ & H3 & _). exact H3. }
assert (KSH : forall a, shadow_addr (frame_addr lyc 1 pos) <= a < shadow_addr (frame_addr lyc 1 pos) + 16 ->
  rdW W2 mem2 a = rdW Wc memA a).
{ intros a Ha. apply (K4 1 pos a Hin1pos); [right; unfold in_zr; cbn [fst snd]; rewrite HFB; exact Ha|].
  intros HaF. pose proof (HFP1 a HaF) as Hr. unfold shadow_addr, SHADOW_OFF in Ha.
  destruct (saa_slot R) as [_ [[H1 H2] | Hs]];
  unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, A_REC_SPILL in *; lia. }
assert (CS2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regsA rr)
  by (intros rr Hr; pose proof (HPres (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (HCORE2 : sa_core B ly S W regs mem md O ly2 S2 W2 regs2 mem2 md2 (ev + EV_ARG_S) pos).
{ unfold sa_core. cbv zeta. fold sp0. rewrite EF, EFl.
  split; [exact HJout|].
  split.
  { intros j r Hj.
    assert (Hjlt : (j < 13)%nat) by (apply (proj1 (nth_error_Some sa_saved j)); rewrite Hj; discriminate).
    apply (aval_mem_kept_r (rdW Wc memA)); [|exact (HFRAME j r Hj)].
    intros y Hy. apply KSTK. lia. }
  split; [unfold rdword in HFLAG |- *; rewrite HFB in HFLAG |- *; rewrite !KFR by lia; exact HFLAG|].
  split; [rewrite (CS2 2%bv ltac:(saa_cs)); exact A2|].
  split; [rewrite (CS2 3%bv ltac:(saa_cs)); exact A3|].
  split; [rewrite (CS2 4%bv ltac:(saa_cs)); exact A4|].
  split; [rewrite (CS2 8%bv ltac:(saa_cs)); exact A8|].
  split; [rewrite (CS2 9%bv ltac:(saa_cs)); exact A9|].
  split; [rewrite (CS2 18%bv ltac:(saa_cs)); exact A18|].
  split; [rewrite (CS2 19%bv ltac:(saa_cs)); exact A19|].
  split; [rewrite (CS2 23%bv ltac:(saa_cs)); exact A23|].
  split; [rewrite (CS2 25%bv ltac:(saa_cs)); exact A25|].
  split; [rewrite (CS2 26%bv ltac:(saa_cs)); exact A26|].
  rewrite (CS2 27%bv ltac:(saa_cs)); exact A27. }
assert (HBUF2 : sa_buf0 (rdW W2 mem2) (frame_addr ly2 1 pos)).
{ rewrite EF. intros i Hi. rewrite KSH; [exact (HBUF i Hi)|]. unfold shadow_addr. lia. }
assert (HACC2 : sa_acct B ly S O ly2 S2 ((p, Z.of_nat (length (sarg v)) + 1) :: Ok) (live + LIVE_ARG_S v))
  by exact (saa_acct_step ly S O lyc Sc Ok live ly2 S2 p _ (LIVE_ARG_S v) HACCT HPerm Hfresh ltac:(lia) Hbb).
exact (KONT ly2 S2 W2 regs2 mem2 md2 _ HCORE2 HPres EF HBUF2 HREP2 HACC2 (mle_station MT S Sc S2 acc _ MTL HMLE Hmle)).
Qed.
End e.
End f.
End d.
