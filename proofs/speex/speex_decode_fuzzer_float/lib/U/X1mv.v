(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1hu. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1mc.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition sb_smrec1 : smrec := SMR wb_submode1 0x3bc90 0x2b3fc 0 0       0 0       0xbf800000.
Definition sb_smrec2 : smrec := SMR wb_submode2 0x3bce8 0x2b3fc 0 0x280ec 0 0x3bec8 0xbf800000.
Definition sb_smrec3 : smrec := SMR wb_submode3 0x3bd40 0x2b3fc 0 0x280ec 0 0x3bee0 0xbf800000.
Definition sb_smrec4 : smrec := SMR wb_submode4 0x3bd98 0x2b3fc 0 0x280ec 0 0x3bee0 0xbf800000.
Definition sb_smrecs : list smrec := [sb_smrec1; sb_smrec2; sb_smrec3; sb_smrec4].

Definition wb_sub_ptrs : list Z := [0; 0x3bc90; 0x3bce8; 0x3bd40; 0x3bd98; 0; 0; 0].
Definition uwb_sub_ptrs : list Z := [0; 0x3bc90; 0; 0; 0; 0; 0; 0].
Definition sb_sub_ptrs (mo : spx_mode) : list Z := match mo with ModeUWB => uwb_sub_ptrs | _ => wb_sub_ptrs end.
Definition sb_sub_ptr (mo : spx_mode) (i : Z) : Z := nth (Z.to_nat i) (sb_sub_ptrs mo) 0.
Definition sb_smrec_at (mo : spx_mode) (i : Z) : option smrec :=
match mo with
| ModeUWB => if i =? 1 then Some sb_smrec1 else None
| _ => if i =? 1 then Some sb_smrec1 else if i =? 2 then Some sb_smrec2
else if i =? 3 then Some sb_smrec3 else if i =? 4 then Some sb_smrec4 else None
end.

Definition ptr_cells (l : list Z) : list cell := map (fun z => C8 (Z_to_bv 64 z)) l.

Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).
Local Notation MODEP mo := (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo).

Definition sbmode_struct (mo : spx_mode) : Z := match mo with ModeUWB => A_sb_uwb_mode | _ => A_sb_wb_mode end.
Definition sbmode_cells (mo : spx_mode) : list cell := match mo with ModeUWB => sb_uwb_mode_cells | _ => sb_wb_mode_cells end.

Definition sb_tables (m : mem) : Prop :=
rw_cells rsegs m WB_SUBMODES_PTR (ptr_cells wb_sub_ptrs)
/\ rw_cells rsegs m UWB_SUBMODES_PTR (ptr_cells uwb_sub_ptrs)
/\ (forall r, In r sb_smrecs -> rw_cells rsegs m (smr_ptr r) (smrec_cells r))
/\ (forall r p, In r sb_smrecs -> sm_innovation_unquant (smr_sm r) = Some (InnovSplitCbShapeSignUnquant p) ->
ro_cells rsegs m (smr_innov_par r) (scb_par_cells p))
/\ rw_cells rsegs m NB_GOT_STDERR [C8 (Z_to_bv 64 NB_STDERR_VAR)]
/\ rw_cells rsegs m NB_STDERR_VAR [C8 (Z_to_bv 64 NB_RSTDERR)]
/\ lsp_cdbk_got m
/\ rw_cells rsegs m A_speex_wb_mode wb_desc_cells /\ rw_cells rsegs m A_speex_uwb_mode uwb_desc_cells
/\ rw_cells rsegs m A_sb_wb_mode sb_wb_mode_cells /\ rw_cells rsegs m A_sb_uwb_mode sb_uwb_mode_cells.

Lemma rw_ro_cells : forall m A cs, rw_cells rsegs m A cs -> ro_cells rsegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

Local Ltac pristine TP :=
apply rw_cells_of_pristine;
[ exact TP
| cbn; repeat split
| unfold RTABLES_LO, WB_SUBMODES_PTR, UWB_SUBMODES_PTR, A_sb_wb_mode, A_sb_uwb_mode, NB_GOT_STDERR, NB_STDERR_VAR, NB_GOT_LSP_HIGH, NB_GOT_LSP_NB,
A_speex_wb_mode, A_speex_uwb_mode; cbn; lia
| match goal with |- ?a + Z.of_nat ?n <= ?h => let v := eval cbv in (Z.of_nat n) in change (a + v <= h) end;
unfold RTABLES_HI, WB_SUBMODES_PTR, UWB_SUBMODES_PTR, A_sb_wb_mode, A_sb_uwb_mode, NB_GOT_STDERR, NB_STDERR_VAR, NB_GOT_LSP_HIGH, NB_GOT_LSP_NB,
A_speex_wb_mode, A_speex_uwb_mode; cbn; lia
| vm_compute; reflexivity ].

Lemma sb_tables_of_pristine : forall m, rtables_pristine m -> sb_tables m.
Proof.
intros m TP. unfold sb_tables.
split; [pristine TP|]. split; [pristine TP|].
split. { intros r Hr. unfold sb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [unfold smrec_cells; cbv zeta; pristine TP|]). destruct Hr. }
split. { intros r p Hr Hp. unfold sb_smrecs in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn in Hp; first [discriminate | injection Hp as <-; apply rw_ro_cells; unfold scb_par_cells; cbn -[rw_cells rsegs]; pristine TP] |]).
destruct Hr. }
split; [pristine TP|]. split; [pristine TP|].
split. { unfold lsp_cdbk_got. split; apply rw_ro_cells; pristine TP. }
split; [apply wb_desc_of_pristine; exact TP|]. split; [apply uwb_desc_of_pristine; exact TP|].
split; [apply sb_wb_mode_of_pristine; exact TP| apply sb_uwb_mode_of_pristine; exact TP].
Qed.

Lemma sb_tables_munch : forall W m m', sb_tables m -> rtables_pristine m -> munch W m m' ->
(forall a, RTABLES_LO <= a < RTABLES_HI -> outside W a) -> sb_tables m'.
Proof. intros W m m' _ TP MU OUT. apply sb_tables_of_pristine. eapply rtables_pristine_munch; eauto. Qed.

Lemma rtables_pristine_write : forall m a bs, rtables_pristine m -> 0 <= a ->
(a + Z.of_nat (length bs) <= RTABLES_LO \/ RTABLES_HI <= a) -> a + Z.of_nat (length bs) <= 2^64 ->
rtables_pristine (write_to_mem m (wa a) bs).
Proof.
intros m a bs TP Ha OUT Hl x Hx. rewrite write_to_mem_spec by lia.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try (apply TP; exact Hx).
exfalso. unfold RTABLES_LO, RTABLES_HI in *. lia.
Qed.

Lemma rtables_pristine_munch' : forall W m m', rtables_pristine m -> munch W m m' ->
disjoint_from W RTABLES_LO (RTABLES_HI - RTABLES_LO) -> rtables_pristine m'.
Proof.
intros W m m' TP MU DJ. eapply rtables_pristine_munch; [exact TP| exact MU|].
intros a Ha. eapply disjoint_outside; [exact DJ|]. lia.
Qed.

Lemma sb_sub_ptr_read : forall m mo i a, sb_tables m -> (mo = ModeWB \/ mo = ModeUWB) -> 0 <= i <= 7 ->
a = wa (SUBP mo + 8 * i) ->
ov_read_bytes rsegs m a 8 = Some (le8 (Z_to_bv 64 (sb_sub_ptr mo i))).
Proof.
intros m mo i a (TW & TU & _) Hmo Hi ->.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hmo as [-> | ->]; cbn [sb_submodes_ptr];
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
lazymatch goal with
| |- ov_read_bytes _ _ (wa (?B + 8 * ?k)) 8 = Some (le8 (Z_to_bv 64 ?v)) =>
let kn := eval vm_compute in (Z.to_nat (8 * k)) in
let v' := eval vm_compute in v in
change (ov_read_bytes rsegs m (wa (B + 8 * k)) 8 = Some (cbytes (C8 (Z_to_bv 64 v'))));
eapply (rw_cells_read_at rsegs m B _ kn (C8 (Z_to_bv 64 v')) 8);
[ first [exact TW | exact TU] | reflexivity | reflexivity | unfold wa; f_equal; cbn; lia ]
end.
Qed.

Lemma sb_smrecs_ptr : forall r, In r sb_smrecs -> RTABLES_LO <= smr_ptr r /\ smr_ptr r + 88 <= RTABLES_HI /\ smr_ptr r mod 8 = 0.
Proof. intros r Hr. unfold sb_smrecs in Hr. unfold RTABLES_LO, RTABLES_HI. repeat (destruct Hr as [<-|Hr]; [cbn; lia|]). destruct Hr. Qed.

Lemma sb_smrec_cases : forall mo i, (mo = ModeWB \/ mo = ModeUWB) -> 0 <= i <= 7 ->
(sb_sub_ptr mo i = 0 /\ sb_smrec_at mo i = None /\ submode_at (sbm_submodes mo) i = None)
\/ (exists r, sb_smrec_at mo i = Some r /\ In r sb_smrecs /\ sb_sub_ptr mo i = smr_ptr r /\ smr_ptr r <> 0 /\
submode_at (sbm_submodes mo) i = Some (smr_sm r) /\
(mo = ModeUWB -> sm_innovation_unquant (smr_sm r) = None)).
Proof.
intros mo i Hmo Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct Hmo as [-> | ->]; destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn;
first [ left; repeat split; reflexivity
| right; eexists; split; [reflexivity|]; split; [cbn; tauto|]; cbn; repeat split; first [reflexivity | lia | discriminate | intros; discriminate] ].
Qed.

Lemma sb_smrec_at_some : forall mo i r, sb_smrec_at mo i = Some r ->
In r sb_smrecs /\ submode_at (sbm_submodes mo) i = Some (smr_sm r) /\ 1 <= i <= 4 /\ sb_sub_ptr mo i = smr_ptr r /\
sm_lsp_unquant (smr_sm r) = LspUnquantHigh /\ (mo = ModeUWB -> sm_innovation_unquant (smr_sm r) = None).
Proof.
intros mo i r E. unfold sb_smrec_at in E.
destruct mo;
repeat match type of E with
| (if i =? ?k then _ else _) = _ => destruct (Z.eqb_spec i k) as [-> | ?]; [injection E as <-; cbn; repeat split; auto; try lia; try discriminate; intros; try discriminate; try reflexivity |]
end; try discriminate.
Qed.

Lemma sb_smrecs_facts : forall r, In r sb_smrecs ->
sm_lsp_unquant (smr_sm r) = LspUnquantHigh /\ sm_ltp_unquant (smr_sm r) = None /\
(sm_innovation_unquant (smr_sm r) = None /\ smr_innov_par r = 0
\/ exists p, sm_innovation_unquant (smr_sm r) = Some (InnovSplitCbShapeSignUnquant p) /\ scb_params_ok p /\
RTABLES_LO <= smr_innov_par r /\ smr_innov_par r + 24 <= RTABLES_HI) /\
(sm_double_codebook (smr_sm r) = 0 \/ sm_double_codebook (smr_sm r) = 1 /\ sm_innovation_unquant (smr_sm r) <> None).
Proof.
intros r Hr. unfold sb_smrecs in Hr. unfold RTABLES_LO, RTABLES_HI, scb_params_ok.
repeat (destruct Hr as [<-|Hr]; [cbn; repeat split; first [reflexivity | left; split; reflexivity | right; eexists; repeat split; try reflexivity; cbn; lia | left; reflexivity | right; split; [reflexivity| discriminate]] |]).
destruct Hr.
Qed.

Section Model.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Implicit Types (b : bits_st ptr) (s : sbd_state ptr) (d : dec_state ptr).

#[using="Type"] Lemma ctl_keeps_depth : forall d r, dec_depth (snd (speex_decoder_ctl d r)) = dec_depth d.
Proof.
induction d as [st|s low IH]; intros r.
- cbn. destruct (nb_decoder_ctl st r); reflexivity.
- destruct r; cbn [speex_decoder_ctl]; fold (@speex_decoder_ctl ptr);
repeat match goal with |- context [speex_decoder_ctl low ?q] =>
pose proof (IH q) as E; destruct (speex_decoder_ctl low q) as [v1 l1]; cbn [snd] in E end;
cbn [snd dec_depth]; rewrite ?E; reflexivity.
Qed.
#[using="Type"] Lemma ctl_mode : forall s low r, exists s' low', snd (speex_decoder_ctl (DecSB s low) r) = DecSB s' low' /\
sbd_mode s' = sbd_mode s /\ sbd_frame_size s' = sbd_frame_size s /\ sbd_encode_submode s' = sbd_encode_submode s /\
dec_depth low' = dec_depth low.
Proof.
intros s low r. pose proof (ctl_keeps_depth low) as D. destruct r; cbn [speex_decoder_ctl]; fold (@speex_decoder_ctl ptr);
repeat match goal with |- context [speex_decoder_ctl low ?q] => specialize (D q); destruct (speex_decoder_ctl low q) end;
cbn [snd] in *; sf_eexists 2%nat; (split; [reflexivity|]); destruct s; cbn; repeat split; first [reflexivity | exact D].
Qed.

#[using="Type"] Lemma ctl_keeps_mode : forall d r, dec_mode (snd (speex_decoder_ctl d r)) = dec_mode d.
Proof.
intros d r. destruct d as [st|s low]; cbn.
- destruct (nb_decoder_ctl st r); reflexivity.
- first [ pose proof (ctl_mode s low r) as sfP_; sf_destruct 5%nat sfP_ as s' low' E Em _ | sf_fb; destruct (ctl_mode s low r) as (s' & low' & E & Em & _) ]. rewrite E. cbn. exact Em.
Qed.
#[using="Type"] Lemma ctl_keeps_nested : forall d r, dec_nested d -> dec_nested (snd (speex_decoder_ctl d r)).
Proof.
induction d as [st|s low IH]; intros r ND.
- cbn. destruct (nb_decoder_ctl st r). exact I.
- destruct ND as [Em NL].
destruct r; cbn [speex_decoder_ctl]; fold (@speex_decoder_ctl ptr);
repeat match goal with |- context [speex_decoder_ctl low ?q] =>
pose proof (IH q NL) as E; pose proof (ctl_keeps_mode low q) as E2; destruct (speex_decoder_ctl low q) as [v1 l1]; cbn [snd] in E, E2 end;
cbn [snd dec_nested]; try (split; [| assumption]); destruct s; cbn in *; congruence.
Qed.

#[using="Type"] Lemma isave_ok_after_set : forall (d : dec_state bptr) mo OUT STEREO m S L,
DREP OUT STEREO m S d L -> (mo = ModeWB \/ mo = ModeUWB) -> dec_mode d = sbm_nb_mode mo ->
isave_ok (snd (speex_decoder_ctl d (CtlSetInnovationSave (sbm_frameSize mo)))).
Proof.
intros d mo OUT STEREO m S L R Hmo Em. destruct d as [st|s low]; cbn.
- destruct st; cbn. unfold HOUT_BYTES. destruct Hmo as [-> | ->]; cbn; lia.
- first [ sf_destruct 8%nat R as a j LBL _ _ _ INV _ | sf_fb; destruct R as (a & j & LBL & _ & _ & _ & INV & _) ]. destruct INV as (Hmo' & Efs & _).
cbn in Em. destruct s; cbn in *. rewrite Efs. subst sbd_mode.
destruct Hmo as [-> | ->]; cbn in Hmo' |- *; [destruct Hmo'; discriminate| reflexivity].
Qed.

Definition sbw_wb b : Z * bits_st ptr :=
if 0 <? speex_bits_remaining b then speex_bits_peek b else (0, b).
Definition sbw_id b : Z :=
let '(wideband, b1) := sbw_wb b in
if negb (wideband =? 0) then uv (ub b1 1) SB_SUBMODE_BITS else 0.
Definition sbw_bits b : bits_st ptr :=
let '(wideband, b1) := sbw_wb b in
if negb (wideband =? 0) then ub (ub b1 1) SB_SUBMODE_BITS else b1.

Definition sbsub_bits (sm : submode) b : bits_st ptr :=
match sm_innovation_unquant sm with
| None => ub b 5
| Some k => let b1 := innov_bits k (ub b 4) in
if negb (sm_double_codebook sm =? 0) then innov_bits k b1 else b1
end.
Fixpoint sbsubs_bits (n : nat) (sm : submode) b : bits_st ptr :=
match n with O => b | S n' => sbsubs_bits n' sm (sbsub_bits sm b) end.

Local Notation unpackM := (@bits_unpack_unsigned_M PState ptr).
Local Notation peekM := (@bits_peek_M PState ptr).
Local Notation remainingM := (@bits_remaining_M PState ptr).

#[using="Type"] Lemma sb_decode_subframe_run : forall sm b (st : PState),
sb_decode_subframe unpackM sm b st = Ret (Ok (sbsub_bits sm b, st)).
Proof.
intros sm b st. unfold sb_decode_subframe, sbsub_bits.
destruct (sm_innovation_unquant sm) as [k|].
- unfold mbind at 1. unfold bits_unpack_unsigned_M at 1. unfold mret at 1. rewrite unpack_eta, ebind_ret_ok. cbn [fst snd].
unfold mbind at 1. rewrite innovation_unquant_run, ebind_ret_ok.
destruct (negb (sm_double_codebook sm =? 0)); [apply innovation_unquant_run| reflexivity].
- unfold mbind, bits_unpack_unsigned_M, mret. rewrite unpack_eta, ebind_ret_ok. reflexivity.
Qed.
#[using="Type"] Lemma sb_decode_subframes_run : forall n sm b (st : PState),
sb_decode_subframes unpackM n sm b st = Ret (Ok (sbsubs_bits n sm b, st)).
Proof.
induction n as [|n IH]; intros sm b st; [reflexivity|].
cbn [sb_decode_subframes sbsubs_bits]. unfold mbind at 1. rewrite sb_decode_subframe_run, ebind_ret_ok. apply IH.
Qed.

#[using="Type"] Lemma peek_same : forall b, sb_buf_size (snd (speex_bits_peek b)) = sb_buf_size b /\
sb_owner (snd (speex_bits_peek b)) = sb_owner b /\ sb_chars (snd (speex_bits_peek b)) = sb_chars b.
Proof. intros b. unfold speex_bits_peek. destruct (_ || _); cbn; repeat split; reflexivity. Qed.
#[using="Type"] Lemma ub_same : forall b n, sb_buf_size (ub b n) = sb_buf_size b /\ sb_owner (ub b n) = sb_owner b /\ sb_chars (ub b n) = sb_chars b.
Proof. intros b n. unfold ub, speex_bits_unpack_unsigned. destruct (_ || _); cbn; repeat split; reflexivity. Qed.
#[using="Type"] Lemma sbw_wb_same : forall b, sb_buf_size (snd (sbw_wb b)) = sb_buf_size b /\
sb_owner (snd (sbw_wb b)) = sb_owner b /\ sb_chars (snd (sbw_wb b)) = sb_chars b.
Proof. intros b. unfold sbw_wb. destruct (0 <? _); [apply peek_same| cbn; repeat split; reflexivity]. Qed.
#[using="Type"] Lemma sbw_bits_same : forall b, sb_buf_size (sbw_bits b) = sb_buf_size b /\
sb_owner (sbw_bits b) = sb_owner b /\ sb_chars (sbw_bits b) = sb_chars b.
Proof.
intros b. unfold sbw_bits. pose proof (sbw_wb_same b) as W. destruct (sbw_wb b) as [wb b1]. cbn [snd] in W.
destruct (negb (wb =? 0)); [| exact W].
pose proof (ub_same b1 1) as U1. pose proof (ub_same (ub b1 1) SB_SUBMODE_BITS) as U2.
destruct W as (W1 & W2 & W3), U1 as (U11 & U12 & U13), U2 as (U21 & U22 & U23). repeat split; congruence.
Qed.
#[using="Type"] Lemma scb_bits_same : forall n hs sbits b, sb_buf_size (scb_bits n hs sbits b) = sb_buf_size b /\
sb_owner (scb_bits n hs sbits b) = sb_owner b /\ sb_chars (scb_bits n hs sbits b) = sb_chars b.
Proof.
induction n as [|n IH]; intros hs sbits b; [cbn; repeat split; reflexivity|].
cbn [scb_bits]. cbv zeta.
set (b1 := if negb (hs =? 0) then ub b 1 else b).
assert (E1 : sb_buf_size b1 = sb_buf_size b /\ sb_owner b1 = sb_owner b /\ sb_chars b1 = sb_chars b).
{ subst b1. destruct (negb (hs =? 0)); [apply ub_same| repeat split; reflexivity]. }
pose proof (ub_same b1 sbits) as E2. pose proof (IH hs sbits (ub b1 sbits)) as E3.
destruct E1 as (A1 & A2 & A3), E2 as (B1 & B2 & B3), E3 as (C1 & C2 & C3). repeat split; congruence.
Qed.
#[using="Type"] Lemma innov_bits_same : forall k b, sb_buf_size (innov_bits k b) = sb_buf_size b /\
sb_owner (innov_bits k b) = sb_owner b /\ sb_chars (innov_bits k b) = sb_chars b.
Proof. intros [|p] b; cbn [innov_bits]; [repeat split; reflexivity| apply scb_bits_same]. Qed.
#[using="Type"] Lemma sbsub_bits_same : forall sm b, sb_buf_size (sbsub_bits sm b) = sb_buf_size b /\
sb_owner (sbsub_bits sm b) = sb_owner b /\ sb_chars (sbsub_bits sm b) = sb_chars b.
Proof.
intros sm b. unfold sbsub_bits. destruct (sm_innovation_unquant sm) as [k|]; [| apply ub_same].
pose proof (ub_same b 4) as (A1 & A2 & A3). pose proof (innov_bits_same k (ub b 4)) as (B1 & B2 & B3).
destruct (negb _); [| repeat split; congruence].
pose proof (innov_bits_same k (innov_bits k (ub b 4))) as (C1 & C2 & C3). repeat split; congruence.
Qed.
#[using="Type"] Lemma sbsubs_bits_same : forall n sm b, sb_buf_size (sbsubs_bits n sm b) = sb_buf_size b /\
sb_owner (sbsubs_bits n sm b) = sb_owner b /\ sb_chars (sbsubs_bits n sm b) = sb_chars b.
Proof.
induction n as [|n IH]; intros sm b; [repeat split; reflexivity|]. cbn [sbsubs_bits].
pose proof (sbsub_bits_same sm b) as (A1 & A2 & A3). pose proof (IH sm (sbsub_bits sm b)) as (B1 & B2 & B3). repeat split; congruence.
Qed.
#[using="Type"] Lemma lsp_bits_same : forall k b, sb_buf_size (lsp_bits k b) = sb_buf_size b /\
sb_owner (lsp_bits k b) = sb_owner b /\ sb_chars (lsp_bits k b) = sb_chars b.
Proof.
assert (G : forall b1 b2 : bits_st ptr,
(sb_buf_size b2 = sb_buf_size b1 /\ sb_owner b2 = sb_owner b1 /\ sb_chars b2 = sb_chars b1) ->
forall n, sb_buf_size (ub b2 n) = sb_buf_size b1 /\ sb_owner (ub b2 n) = sb_owner b1 /\ sb_chars (ub b2 n) = sb_chars b1).
{ intros b1 b2 (E1 & E2 & E3) n. pose proof (ub_same b2 n) as (F1 & F2 & F3). repeat split; congruence. }
intros k b. destruct k; cbn [lsp_bits]; repeat apply G; repeat split; reflexivity.
Qed.

#[using="Type"] Lemma ub_ok : forall b n, bits_ok b -> 0 <= n -> bits_ok (ub b n).
Proof. intros b n OK Hn. pose proof (speex_bits_unpack_unsigned_ok b n _ _ OK Hn (unpack_eta b n)) as (OK1 & _). exact OK1. Qed.
#[using="Type"] Lemma peek_ok : forall b, bits_ok b -> bits_ok (snd (speex_bits_peek b)).
Proof. intros b OK. pose proof (speex_bits_peek_ok b _ _ OK (surjective_pairing _)) as (OK1 & _). exact OK1. Qed.
#[using="Type"] Lemma sbw_wb_ok : forall b, bits_ok b -> bits_ok (snd (sbw_wb b)).
Proof. intros b OK. unfold sbw_wb. destruct (0 <? _); [apply peek_ok; exact OK| exact OK]. Qed.
#[using="Type"] Lemma scb_bits_ok : forall n hs sbits b, bits_ok b -> 0 <= sbits -> bits_ok (scb_bits n hs sbits b).
Proof.
induction n as [|n IH]; intros hs sbits b OK Hs; [exact OK|]. cbn [scb_bits]. cbv zeta.
apply IH; [| exact Hs]. apply ub_ok; [| exact Hs]. destruct (negb _); [apply ub_ok; [exact OK| lia]| exact OK].
Qed.
#[using="Type"] Lemma innov_bits_ok : forall k b, bits_ok b -> match k with InnovSplitCbShapeSignUnquant p => scb_params_ok p | _ => True end ->
bits_ok (innov_bits k b).
Proof. intros [|p] b OK WF; cbn [innov_bits]; [exact OK|]. apply scb_bits_ok; [exact OK|]. unfold scb_params_ok in WF. lia. Qed.
End Model.

Section Unfold.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Local Notation unpackM := (@bits_unpack_unsigned_M PState ptr).
Local Notation peekM := (@bits_peek_M PState ptr).
Local Notation remainingM := (@bits_remaining_M PState ptr).
Variable notify : list Z -> M PState unit.
Implicit Types (b : bits_st ptr) (s : sbd_state ptr) (d : dec_state ptr).
Definition sbw_M s b : M PState ((sbd_state ptr * bits_st ptr) + (sbd_state ptr * bits_st ptr)) :=
rem <- remainingM b ;;
' (wideband, b) <- (if 0 <? rem then peekM b else mret (0, b)) ;;
' (st, b) <- (if negb (wideband =? 0) then
' (wideband, b) <- unpackM b 1 ;;
' (id, b) <- unpackM b SB_SUBMODE_BITS ;;
mret (set_sbd_submodeID s id, b)
else mret (set_sbd_submodeID s 0, b)) ;;
if negb (sbd_submodeID st =? 0) &&
match submode_at (sbm_submodes (sbd_mode st)) (sbd_submodeID st) with None => true | Some _ => false end
then notify MSG_INVALID_MODE ;;; mret (inr (st, b))
else mret (inl (st, b)).
#[using="Type"] Lemma sbw_M_run : forall s b (st : PState),
sbw_M s b st =
(let s1 := set_sbd_submodeID s (sbw_id b) in let b1 := sbw_bits b in
if negb (sbw_id b =? 0) &&
match submode_at (sbm_submodes (sbd_mode s)) (sbw_id b) with None => true | Some _ => false end
then (notify MSG_INVALID_MODE ;;; mret (inr (s1, b1))) st
else Ret (Ok (inl (s1, b1), st))).
Proof.
intros s b st. unfold sbw_M, sbw_id, sbw_bits, sbw_wb, bits_remaining_M, bits_peek_M, bits_unpack_unsigned_M.
unfold mbind at 1. unfold mret at 1. rewrite ebind_ret_ok.
unfold mbind at 1.
assert (E1 : (if 0 <? speex_bits_remaining b then (fun s0 : PState => Ret (Ok (speex_bits_peek b, s0))) else mret (0, b)) st
= Ret (Ok ((if 0 <? speex_bits_remaining b then speex_bits_peek b else (0, b)), st))).
{ destruct (0 <? _); reflexivity. }
rewrite E1, ebind_ret_ok. clear E1.
destruct (if 0 <? speex_bits_remaining b then speex_bits_peek b else (0, b)) as [wb b1]. cbn [fst snd].
unfold mbind at 1.
destruct (negb (wb =? 0)).
- unfold mbind at 1. unfold mret at 1 2. rewrite ebind_ret_ok. cbn [fst snd]. rewrite (unpack_eta b1 1). cbv beta iota.
unfold mbind at 1. rewrite ebind_ret_ok. cbn [fst snd]. rewrite (unpack_eta (ub b1 1) SB_SUBMODE_BITS). cbv beta iota. unfold mret at 1.
rewrite ebind_ret_ok. cbn [fst snd].
destruct s; cbn -[ub uv]. destruct (_ && _); reflexivity.
- unfold mret at 1. rewrite ebind_ret_ok. cbn [fst snd]. destruct s; cbn. reflexivity.
Qed.

#[using="Type"] Lemma sb_decode_unfold : forall s (low : dec_state ptr) LD b out,
sbd_encode_submode s = 1 ->
sb_decode notify unpackM peekM remainingM s low LD b out =
(let '(_, low1) := speex_decoder_ctl low (CtlSetInnovationSave (out + sbd_frame_size s)) in
' (ret, low2, b1) <- LD low1 b out ;;
let '(dtx, low3) := speex_decoder_ctl low2 CtlGetDtxStatus in
if negb (ret =? 0) then mret (ret, (s, low3), b1) else
sr <- sbw_M s b1 ;;
match sr with
| inr (st, b2) => mret (-2, (st, low3), b2)
| inl (st, b2) =>
match submode_at (sbm_submodes (sbd_mode st)) (sbd_submodeID st) with
| None => mret (0, (set_sbd_first st 1, low3), b2)
| Some sm =>
let '(_, low4) := speex_decoder_ctl low3 CtlGetPiGain in
let '(_, low5) := speex_decoder_ctl low4 CtlGetExc in
b3 <- lsp_unquant unpackM (sm_lsp_unquant sm) b2 ;;
b4 <- sb_decode_subframes unpackM (Z.to_nat (sbd_nbSubframes st)) sm b3 ;;
mret (0, (set_sbd_first st 0, low5), b4)
end
end).
Proof. intros s low LD b out ES. unfold sb_decode, sbw_M. rewrite ES. reflexivity. Qed.
End Unfold.
