(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S03 (TRIM, 0x8d60c-0x8d678) of the ASan walk of verbs_receive on
   plugin-hostd/fuzz_command (interface lib/A/Prog/verbs_receive_iface.v, `vr_s03_stmt`): from vr_b2 (strndup's line
   q holds l > 0 bytes, a0 = l) the six instructions 0x8d60c-0x8d620 set the loop's registers (a1 = q + l,
   a0 = q + l - 1, a2 = 32, a3 = 0x100002600), the trim loop of verbs_receive_s03_k.v runs from 0x8d624 to the exit
   0x8d67c, and the line block then holds Verbs.line D (vr_b3). The loop writes only the bytes of the line, so
   every other part of the boundary state is kept. The record facts are the named Section hypotheses
   (ROA, RRO, RECC, PROGU). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_s03_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.
Module PSF := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.StrFun.
Module PVP := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_pre.

(* ---------------------------------------------------------------------------------------------------------------
   The model's line: strndup's prefix is upto0 D, which holds no terminator; its trim is a prefix of it *)
Lemma vr3_upto_firstn : forall (D : list byte) (n : Z), n = Z.of_nat (length D) ->
firstn (Z.to_nat (PSF.strnlen_res n D)) D = PV.upto0 D /\ PSF.strnlen_res n D = Z.of_nat (length (PV.upto0 D)).
Proof. intros D n ->. exact (PVP.strnlen_upto D). Qed.

Lemma vr3_upto0_no0 : forall D : list byte, ~ In (Z_to_bv 8 0) (PV.upto0 D).
Proof.
intros D. unfold PV.upto0. induction D as [|x D IH]; cbn [PV.upto]; [intros []|].
destruct (bv_unsigned x =? 0) eqn:Ex; [intros []|].
intros [Hx | Hin]; [|exact (IH Hin)].
subst x. vm_compute in Ex. discriminate Ex.
Qed.

Lemma vr3_dropw_in : forall p (l : list byte) x, In x (PV.dropw p l) -> In x l.
Proof.
intros p l x. induction l as [|y l IH]; cbn [PV.dropw]; [tauto|].
destruct (p y); [intros H; right; exact (IH H) | tauto].
Qed.

Lemma vr3_trim_in : forall (l : list byte) x, In x (PV.trim l) -> In x l.
Proof.
intros l x H. unfold PV.trim in H. apply in_rev in H. apply vr3_dropw_in in H. apply in_rev. exact H.
Qed.

(* the bytes the loop leaves at q are the trimmed line as a C string *)
Lemma vr3_line_str : forall rd q (U : list byte), ~ In (Z_to_bv 8 0) U ->
abytes_atR rd q (PV.trim U ++ repeat (Z_to_bv 8 0) (length U - length (PV.trim U)) ++ [Z_to_bv 8 0]) ->
astr_atR rd q (PV.trim U).
Proof.
intros rd q U H0 H. split.
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  assert (Hl : (i < length (PV.trim U ++ repeat (Z_to_bv 8 0) (length U - length (PV.trim U)) ++ [Z_to_bv 8 0]))%nat)
    by (rewrite !length_app, repeat_length; cbn [length]; lia).
  rewrite (H i Hl). do 2 f_equal.
  destruct (Nat.lt_ge_cases i (length (PV.trim U))) as [Hi'|Hi'].
  + rewrite !app_nth1 by lia. reflexivity.
  + rewrite (app_nth2 (PV.trim U) (repeat (Z_to_bv 8 0) (length U - length (PV.trim U)) ++ [Z_to_bv 8 0])) by lia.
    rewrite (app_nth2 (PV.trim U) [Z_to_bv 8 0]) by lia.
    replace (i - length (PV.trim U))%nat with 0%nat by lia.
    rewrite vr3_nth_zeros. reflexivity.
- intros Hin. exact (H0 (vr3_trim_in U _ Hin)).
Qed.

Lemma vr3_l_range : forall n D, 0 <= n -> 0 <= vr_l n D <= n.
Proof.
intros n D Hn. unfold vr_l, PSF.strnlen_res. destruct (PSF.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:Fb; [|lia].
destruct (PSF.find_byte_Some _ _ _ Fb) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

(* the program statics of the record lie in cmd_PG (PROGU puts them in the image) *)
Lemma vr3_PG_rec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_REC, A_G_REC + 960). split; [unfold cmd_PG; left; reflexivity | unfold REC_SIZE in Ha; cbn; lia]. Qed.
Lemma vr3_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_REC_SPILL, A_REC_SPILL + 56). split; [unfold cmd_PG; right; left; reflexivity | unfold SC_SIZE in Ha; cbn; lia]. Qed.
Lemma vr3_PG_quit : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> inFP cmd_PG a.
Proof. intros a Ha. exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; right; right; left; reflexivity | cbn; lia]. Qed.

(* the four GOT words the recorder reads are read-only bytes of the image (CmdRo.v:426-429) *)
Lemma vr3_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb. decompose [and] Hb. clear Hb.
assert (HC : forall a (l : list byte) v, abytes_atR rd a l -> length l = 8%nat ->
  (forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) -> aval_mem rd a 8 v).
{ intros a l v Hl Hlen Hk i Hi. rewrite (Hl i ltac:(lia)). f_equal. exact (Hk i Hi). }
unfold cmd_got_ok. split; [|split; [|split]];
[ match goal with Hx : abytes_atR rd 0xa7068 _ |- _ => apply (HC _ _ _ Hx eq_refl) end
| match goal with Hx : abytes_atR rd 0xa7070 _ |- _ => apply (HC _ _ _ Hx eq_refl) end
| match goal with Hx : abytes_atR rd 0xa7078 _ |- _ => apply (HC _ _ _ Hx eq_refl) end
| match goal with Hx : abytes_atR rd 0xa7080 _ |- _ => apply (HC _ _ _ Hx eq_refl) end ];
(intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia).
Qed.

Lemma vr3_rv_get : forall (regs : bvmap 5 word) l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.

Lemma vr3_U_add : forall E c x y, ew E 10 = Z_to_bv 64 x -> ew E 21 = Z_to_bv 64 y ->
0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= x + c -> x + c + y < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff 10 c) (SOff 21 0)) = x + c + y.
Proof.
intros E c x y H10 H21 Hx Hy Hc Hs. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 10 x c H10), (U_atom E 21 y H21) by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma vr3_stk_ge : 208 + ASTACK <= VERBS_RECEIVE_STK.
Proof.
unfold VERBS_RECEIVE_STK. pose proof (Z.le_max_r VR_CALLEE_STK (Z.max ASTACK (4 * ESTACK))) as Hm1.
pose proof (Z.le_max_l ASTACK (4 * ESTACK)) as Hm2. lia.
Qed.

(* a register of the run's final symbolic state, as the term the state holds *)
Ltac vr3_reg HS r Hr :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma vr3_s1_range : forall e, vr_sp0 e - 224 <= vr_s1 e <= vr_sp0 e - 192.
Proof.
intros e. unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as Hmb.
remember ((vr_sp0 e - 192) mod 32) as r32 eqn:Hr32. clear Hr32. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the record facts (the walk hypotheses and CmdRecFacts.v's lemmas; names and types as the assembly collects them) *)
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ---------------------------------------------------------------------------------------------------------------
   vr_b3 from vr_b2's state once only the bytes of the line [q, q + l) have changed *)
Lemma vr3_b3_of : forall e pos F q lyc Sc regsc memc mdc k nm (W : world SEGS) regs' mem' md',
vr_ent B MT e ->
vr_core B MT e pos F [vr_lb e q] vr_sh2 (vr_sl1 F) ((10, vr_l (e_n e) (e_D e)) :: vr_rl2 e F q) (e_R e) (e_O e) (e_q0 e)
  k 1 nm 1 lyc Sc W regsc memc mdc ->
vr_fresh B e (vr_lb e q) -> rdword (rdW W memc) (F + 608) = Some 0 ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem' md' k ->
(forall r, In r vr3_keepz -> getr regs' (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + vr_l (e_n e) (e_D e)) -> rdW W mem' a = rdW W memc a) ->
astr_atR (rdW W mem') q (PV.line (e_D e)) ->
vr_b3 B MT e W (cfg_at SEGS (vr_pc 0x8d67c) regs' mem' md').
Proof.
intros e pos F q lyc Sc regsc memc mdc k nm W regs' mem' md' Hent Hcore Hfresh Hsave HJ' KR KM Hline.
pose proof Hcore as (HJ & Hk & Hmet & Hnm & (EF & HF2 & HF3) & Hrv & Hsv & Hsp & Henv & Hrec & Hdat & Hperm & Hq).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & Hrec0 & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
change (spZ (e_regs e)) with (vr_sp0 e) in *.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (HinF : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR HinF) as (Hf0 & Hfc & _).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
assert (HinQ : In (vr_lb e q) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
unfold vr_lb in HinQ.
pose proof (vr3_l_range (e_n e) (e_D e) ltac:(lia)) as Hlr.
set (l := vr_l (e_n e) (e_D e)) in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinQ) as (_ & Hq4 & Hqc & Hqapp & _).
assert (Hrq : req_size (l + 1) = l + 1) by (unfold req_size; destruct (Z.eqb_spec (l + 1) 0); lia).
rewrite Hrq in Hqc, Hqapp.
pose proof vr3_stk_ge as HSTKge. pose proof (vr3_s1_range e) as Hs1.
assert (HAS : ASTACK = 16384) by reflexivity.
assert (Hcei : alloc_ceiling + 16 <= vr_s1 e) by lia.
(* the bytes of the line are none of the image's, the stack's, the frame's or the shadow's *)
assert (Hout_img : forall a, in_img SEGS a -> ~ (q <= a < q + l)).
{ intros a Ha Hr. exact (blk_img SEGS B LAWS lyc Sc W memc mdc q (l + 1) a HAR HinQ ltac:(rewrite Hrq; lia) Ha). }
assert (Hout_fr : forall a, F <= a < F + 1024 -> ~ (q <= a < q + l)).
{ intros a Ha Hr. pose proof (sep_block_frame SEGS B LAWS lyc Sc W memc mdc q (l + 1) 4 pos HAR HinQ HinF) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, <- EF in Hd. change (fs_frame_bytes 4) with 1024 in Hd. lia. }
assert (Hsh : forall i, 0 <= i < 128 -> 0 <= shadow_addr F + i < 2 ^ 64 /\ ~ (q <= shadow_addr F + i < q + l)).
{ intros i Hi. unfold in_app, kLowShadowBeg in Hqapp. rewrite C3 in Hqapp. unfold shadow_addr, SHADOW_OFF.
  assert (F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). lia. }
exists pos, F, q, lyc, Sc, regs', mem', md', k, nm.
split; [reflexivity|].
split; [|split].
- split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hmet|]. split; [exact Hnm|].
  split.
  { split; [exact EF|]. split.
    - rewrite <- HF2. apply rdword_ext. intros kk Hkk. apply KM; [lia | apply Hout_fr; lia].
    - intros i Hi. destruct (Hsh (Z.of_nat i) ltac:(lia)) as [Hr1 Hr2].
      rewrite KM by assumption. exact (HF3 i Hi). }
  split.
  { unfold vr_rv. apply Forall_forall. intros [r v] Hin.
    assert (Hr : In r vr3_keepz).
    { cbn [vr_base vr_rl2 app In] in Hin. unfold vr3_keepz.
      repeat (destruct Hin as [Hx|Hin]; [injection Hx as <- _; cbn [In]; repeat first [left; reflexivity | right]|]).
      destruct Hin. }
    cbn [fst snd]. rewrite (KR r Hr). apply (vr3_rv_get regsc _ r v Hrv).
    apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; right; exact Hin]. }
  split.
  { intros j r Hj. pose proof (Hsv j r Hj) as H.
    assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length vr_saved_regs] in Hj13.
    intros kk Hkk. rewrite KM; [exact (H kk Hkk) | lia | lia]. }
  split.
  { unfold vr_spill, vr_sl1 in *. apply Forall_inv in Hsp. cbn [fst snd] in Hsp.
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    intros kk Hkk. rewrite KM; [exact (Hsp kk Hkk) | lia | lia]. }
  split.
  { destruct Henv as (HR1 & _).
    assert (HR' : arodata_okP SEGS RLO RHI B (rdW W mem')).
    { intros a Hro Ho He.
      assert (Himg : in_img SEGS a)
        by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]).
      pose proof (pa_img_range a Himg) as Hai.
      rewrite KM; [exact (HR1 a Hro Ho He) | lia | exact (Hout_img a Himg)]. }
    pose proof (proj1 HJ') as HAR'.
    pose proof (ROA lyc Sc W mem' md' HAR' HR') as HRO'.
    destruct (RECC lyc Sc W mem' md' HAR') as (Hfl & Hgd & Herr).
    split; [exact HR'|]. split; [exact (vr3_got_of_ro _ HRO')|]. split; [exact HRO'|].
    split; [exact Hgd|]. split; [exact Hfl | exact Herr]. }
  split.
  { apply (rec_repA_agree B lyc Sc lyc Sc (rdW W memc) (rdW W mem') (e_R e) (e_O e) Hrec (fun pn _ Hb => Hb)).
    - intros kk Hkk. assert (Hi : in_img SEGS (A_G_REC + kk)) by exact (proj1 (PROGU _ (vr3_PG_rec (A_G_REC + kk) ltac:(lia)))).
      pose proof (pa_img_range _ Hi). apply KM; [lia | exact (Hout_img _ Hi)].
    - intros kk Hkk. assert (Hi : in_img SEGS (A_REC_SPILL + kk)) by exact (proj1 (PROGU _ (vr3_PG_spill (A_REC_SPILL + kk) ltac:(lia)))).
      pose proof (pa_img_range _ Hi). apply KM; [lia | exact (Hout_img _ Hi)].
    - intros [p n] Hpn kk Hkk. cbn [fst snd] in *.
      assert (Hpb : In (p, n) (ablocks B lyc Sc)) by exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn).
      assert (Hne : (p, n) <> (q, l + 1)).
      { intros Eq. rewrite Eq in Hpn. apply (proj2 Hfresh). unfold vr_lb.
        exact (rec_repA_in_blocks B _ _ _ _ _ _ Hrec0 Hpn). }
      pose proof (sep_blocks SEGS B LAWS lyc Sc W memc mdc p n q (l + 1) HAR Hpb HinQ Hne) as Hd.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpb) as (_ & Hp4 & Hpc & _).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd.
      assert (Hrn : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
      apply KM; lia. }
  split; [exact Hdat|]. split; [exact Hperm|].
  intros kk Hkk. assert (Hi : in_img SEGS (A_G_QUITTING + Z.of_nat kk))
    by exact (proj1 (PROGU _ (vr3_PG_quit (A_G_QUITTING + Z.of_nat kk) ltac:(lia)))).
  pose proof (pa_img_range _ Hi). rewrite KM; [exact (Hq kk Hkk) | lia | exact (Hout_img _ Hi)].
- split; [exact Hfresh | exact Hline].
- rewrite <- Hsave. apply rdword_ext. intros kk Hkk. apply KM; [lia | apply Hout_fr; lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The segment *)
Lemma vr_s03 : vr_s03_stmt B MT.
Proof.
intros e W cf Hent Hb2.
destruct Hb2 as (pos & F & q & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hl0 & Hcore & (Hfresh & Hl) & Hsave).
pose proof Hcore as (HJ & _ & _ & _ & _ & Hrv & _ & _ & _ & _ & _ & Hperm & _).
pose proof Hent as (HPRE0 & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (vr3_upto_firstn (e_D e) (e_n e) (eq_sym HlenD)) as (HU & HlU).
set (U := PV.upto0 (e_D e)) in *.
assert (El : vr_l (e_n e) (e_D e) = Z.of_nat (length U)) by exact HlU.
unfold vr_line0 in *. unfold vr_l in Hl. rewrite HU in Hl.
(* the line block *)
assert (HIN : In (q, Z.of_nat (length U) + 1) (ablocks B lyc Sc)).
{ rewrite <- El. change (q, vr_l (e_n e) (e_D e) + 1) with (vr_lb e q).
  apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity. }
assert (HNEW : ~ In (q, Z.of_nat (length U) + 1) (ablocks B (e_ly e) (e_S e))).
{ rewrite <- El. exact (proj2 Hfresh). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ) HIN) as (_ & Hq4 & Hqc & _).
assert (Hrq : req_size (Z.of_nat (length U) + 1) = Z.of_nat (length U) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length U) + 1) 0); lia).
rewrite Hrq in Hqc.
(* the registers of vr_b2 *)
assert (R10 : getr regsc (Z_to_bv 5 10) = w64 (Z.of_nat (length U)))
  by (rewrite <- El; apply (vr3_rv_get regsc _ _ _ Hrv); apply in_or_app; right; left; reflexivity).
assert (R19 : getr regsc (Z_to_bv 5 19) = w64 SHADOW_OFF)
  by (apply (vr3_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn [vr_rl2 In]; tauto).
assert (R21 : getr regsc (Z_to_bv 5 21) = w64 q)
  by (apply (vr3_rv_get regsc _ _ _ Hrv); apply in_or_app; right; cbn [vr_rl2 In]; tauto).
(* 0x8d60c-0x8d620: a1 = q + l, a2 = 32, a3 = 0x100002600, a0 = q + l - 1 *)
remember (Eimg (Ereg regsc [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc []) E)
  by (subst E; split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew E 10 = w64 (Z.of_nat (length U)))
  by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 10 (Z_to_bv 5 10) eq_refl); exact R10).
assert (E21 : ew E 21 = w64 q)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regsc _ 21 (Z_to_bv 5 21) eq_refl); exact R21).
assert (HS : st_ok_pi SEGS VAL E (mkSS 28968 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 28968)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
    [subst E; apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
clear HE.
unfold cfg_at, w64. replace (vr_pc 0x8d60c) with (BASE + 28968) by (unfold vr_pc, AF_verbs_receive; lia).
paj_run_to_sh RUNTOP HS HJ 28992.
{ apply awr_ok_nil. }
vr3_md md1. vr3_ms HS ms1. cbn [ms_mem mkst] in HFr.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W memc a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [|exact Ha|intros []].
  intros b0 wlo whi x Hin. vm_compute in Hin. destruct Hin. }
clear HF HFr HG.
pose proof (vr3_kept_of E _ _ regsc [] vr3_keepz HS HAE ltac:(vm_compute; reflexivity)) as KR0.
cbn [ms_regs restrict] in KR0.
vr3_reg HS (Z_to_bv 5 10) P10. vr3_reg HS (Z_to_bv 5 11) P11. vr3_reg HS (Z_to_bv 5 12) P12.
vr3_reg HS (Z_to_bv 5 13) P13.
rewrite (denot_lit_U E), (vr3_U_add E (-1) (Z.of_nat (length U)) q) in P10 by first [exact E10 | exact E21 | lia].
rewrite (denot_lit_U E), (vr3_U_add E 0 (Z.of_nat (length U)) q) in P11 by first [exact E10 | exact E21 | lia].
cbn [sv_denot] in P12, P13.
assert (H19' : getr (ms_regs ms1) (Z_to_bv 5 19) = w64 SHADOW_OFF) by (rewrite (KR0 19 ltac:(cbn; tauto)); exact R19).
assert (H21' : getr (ms_regs ms1) (Z_to_bv 5 21) = w64 q) by (rewrite (KR0 21 ltac:(cbn; tauto)); exact R21).
assert (HI : vr3_inv B W VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc k q U (ms_regs ms1) (ms_mem ms1) (length U) (ms_regs ms1) (ms_mem ms1) md1).
{ split; [lia|].
  split; [rewrite P10; unfold w64; f_equal; lia|].
  split; [rewrite P11; unfold w64; f_equal; lia|].
  split; [exact P12|]. split; [exact P13|].
  split; [intros r _; reflexivity|].
  split; [exact HJ|].
  split; [intros a _ _; reflexivity|].
  split.
  - unfold vr3_bytes. rewrite firstn_all, Nat.sub_diag. cbn [repeat app].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite K0; [exact (Hl i ltac:(rewrite length_app; cbn [length]; lia)) | lia].
  - rewrite firstn_all. reflexivity. }
pmkst HS.
eapply SRr_mono.
{ exact (vr3_loop B W VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
    lyc Sc k q U (ms_regs ms1) (ms_mem ms1) HIN HNEW H19' H21' (length U) (ms_regs ms1) (ms_mem ms1) md1 HI). }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & (KR & HJ' & HF & HBy)).
replace (mkCfg (mkst regs' (Z_to_bv 64 (BASE + 29080)) mem' (seg_rom SEGS)) md')
  with (cfg_at SEGS (vr_pc 0x8d67c) regs' mem' md')
  by (unfold cfg_at, w64; replace (vr_pc 0x8d67c) with (BASE + 29080) by (unfold vr_pc, AF_verbs_receive; lia); reflexivity).
apply (vr3_b3_of e pos F q lyc Sc regsc memc mdc k nm W regs' mem' md' Hent Hcore Hfresh Hsave HJ').
- intros r Hr. rewrite (KR r Hr). exact (KR0 r Hr).
- intros a Ha Hout. rewrite El in Hout. rewrite (HF a Ha Hout). exact (K0 a Ha).
- unfold PV.line. fold U. exact (vr3_line_str (rdW W mem') q U (vr3_upto0_no0 (e_D e)) HBy).
Qed.

End e.
End f.
End d.
