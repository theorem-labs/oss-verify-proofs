(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment s4 of send_message's walk on plugin-hostd/fuzz_command's ASan image
   (0x86c70 `mv a0,s5; jal verbs_receive` up to the return 0x86c78), ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v at c8557374ad2e — the program-call step of
   cgif_close (A/ACh1.v:321-405: cl_callS over a callee's contract, the callee's premises discharged at the call
   state, the next point's statement discharged from the call's post) over fuzz_command's listing and
   send_message's segment interface (lib/A/Prog/send_message_k.v, send_message_l.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaJournal CmdPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_clear_c verbs_receive_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import send_message_k send_message_l PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------- values through a restricted memory *)
Lemma sm_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
replace (bv_modulus 8) with 256 by (vm_compute; reflexivity). apply Z.mod_small. lia.
Qed.
Lemma sm_u8_inj : forall z (b : byte), bv_unsigned b = z -> b = Z_to_bv 8 z.
Proof. intros z b <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma sm_le_byte_range : forall v n k, 0 <= le_byte v n k < 256.
Proof. intros v n k. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.
Lemma sm_option_map_Some : forall (A Bt : Type) (f : A -> Bt) (o : option A) y,
option_map f o = Some y -> exists x, o = Some x /\ f x = y.
Proof. intros A Bt f [x|] y Hq; cbn in Hq; [injection Hq as <-; exists x; split; reflexivity | discriminate Hq]. Qed.
Lemma sm_aval_of_val : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
apply sm_u8. apply sm_le_byte_range.
Qed.
Lemma sm_val_of_aval : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
apply sm_option_map_Some in Hb as (b & Eb & Hval).
rewrite Eb. f_equal. exact (sm_u8_inj _ b Hval).
Qed.

(* ---------------------------------------------------------------- arithmetic and list helpers *)
Lemma sm_mod64_8 : forall x, x mod 64 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 64 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D. replace (64 * (x / 64)) with ((8 * (x / 64)) * 8) by lia. apply Z_mod_mult.
Qed.
(* `addi sp,sp,-96; andi sp,sp,-32` moves the stack pointer down by 96 or 112 and keeps it 16-aligned *)
Lemma sm_sp1_bounds : forall sp0, sp0 mod 16 = 0 -> 0 <= sp0 ->
sp0 - 112 <= sm_sp1 sp0 <= sp0 - 96 /\ sm_sp1 sp0 mod 16 = 0.
Proof.
intros sp0 H16 Hpos. unfold sm_sp1.
pose proof (Z.div_mod (sp0 - 96) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (sp0 - 96) 32 ltac:(lia)) as M.
assert (Hm : (sp0 - 96) mod 16 = 0)
by (replace (sp0 - 96) with (sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full; exact H16).
pose proof (Z.div_mod ((sp0 - 96) mod 32) 16 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound ((sp0 - 96) mod 32) 16 ltac:(lia)) as Mq.
assert (Hq : ((sp0 - 96) mod 32) mod 16 = 0)
by (rewrite <- Znumtheory.Zmod_div_mod; [exact Hm | lia | lia | exists 2; reflexivity]).
rewrite Hq, Z.add_0_r in Dq.
split; [lia|].
replace (32 * ((sp0 - 96) / 32)) with ((2 * ((sp0 - 96) / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma sm_inFP_ablocks : forall O a, inFP (ablocks_fp O) a <-> (exists b n, In (b, n) O /\ b <= a < b + req_size n).
Proof.
intros O a. split.
- intros (r & Hin & Hr). unfold ablocks_fp in Hin. apply in_map_iff in Hin as ([b n] & <- & Hb).
  cbn [fst snd] in Hr. exists b, n. split; [exact Hb | lia].
- intros (b & n & Hb & Hr). exists (b, b + req_size n). split; [|cbn [fst snd]; lia].
  unfold ablocks_fp. exact (in_map (fun x : Z * Z => (fst x, fst x + req_size (snd x))) O (b, n) Hb).
Qed.
Lemma sm_bsum_nonneg : forall l : list (Z * Z), Forall (fun b => 0 <= snd b) l -> 0 <= bsum l.
Proof.
induction l as [|y l IH]; intros HF; [cbn [bsum fold_right]; lia|].
inversion HF as [|?? Hy Hl]; subst. rewrite bsum_cons. pose proof (IH Hl). lia.
Qed.
Lemma sm_bsum_incl : forall (l1 l2 : list (Z * Z)),
List.NoDup l1 -> incl l1 l2 -> Forall (fun b => 0 <= snd b) l2 -> bsum l1 <= bsum l2.
Proof.
induction l1 as [|x l1 IH]; intros l2 HN HI HF.
- exact (sm_bsum_nonneg l2 HF).
- inversion HN as [|?? Hnx HN1]; subst.
  assert (Hx : In x l2) by (apply HI; left; reflexivity).
  apply in_split in Hx as (p1 & p2 & ->).
  assert (HI1 : incl l1 (p1 ++ p2)).
  { intros y Hy. assert (Hy2 : In y (p1 ++ x :: p2)) by (apply HI; right; exact Hy).
    apply in_app_iff in Hy2 as [Hy2 | [Hy2 | Hy2]];
    [apply in_app_iff; left; exact Hy2 | exfalso; apply Hnx; subst; exact Hy | apply in_app_iff; right; exact Hy2]. }
  assert (HF2 : Forall (fun b : Z * Z => 0 <= snd b) (p1 ++ p2)).
  { apply Forall_forall. intros y Hy. apply (proj1 (Forall_forall _ _) HF). apply in_app_iff in Hy as [Hy|Hy];
    [apply in_app_iff; left; exact Hy | apply in_app_iff; right; right; exact Hy]. }
  pose proof (IH (p1 ++ p2) HN1 HI1 HF2) as Hle. rewrite bsum_app in Hle.
  rewrite bsum_app, !bsum_cons. lia.
Qed.
Lemma sm_strnlen_le : forall n D, 0 <= n -> 0 <= StrFun.strnlen_res n D <= n.
Proof.
intros n D Hn. unfold StrFun.strnlen_res.
destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:F; [|lia].
destruct (StrFun.find_byte_Some _ _ _ F) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

(* getr through a chain of regupd's; YK14's getr_resolve also turns getr into reg_get, which the interface's
   register facts do not speak about *)
Ltac sm_getr := repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the machine step of a PCall slot: the jal links ra and enters the callee's entry (cgif A/ACh1.v's call step,
   here without the symbolic state, because the segment runs only two instructions) *)
Lemma sm_step_pcall : forall k s (rd : Prelude.reg) regs mem rom,
plookup (@pl_tpi _ PL_cmd) k = Some (PCall s rd) -> bv_eqb rd 0 = false -> 0 <= k < 2 ^ 40 ->
RiscvSemantics.step SEGS (mkst regs (Z_to_bv 64 (BASE + k)) mem rom) =
MachineOk (mkst (regupd regs rd (Z_to_bv 64 (BASE + (k + 4)))) (Z_to_bv 64 (SIGMA s)) mem rom).
Proof.
intros k s rd regs mem rom Hpl Hrd Hk.
pose proof pa_B_ok as (HB0 & HB1 & _).
rewrite <- (pl_tpi_eq (L := cmd_listing)) in Hpl.
pose proof (cert_slot csym (clookup pa_tbl) VAL SIGMA cmd_listing pa_cert _ _ Hpl) as (Hck & Hk0 & Hk4).
unfold pi_slot_check in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hl; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrdq _].
apply reg_eqb_eq in Hrdq. subst. apply Z.eqb_eq in Ht.
pose proof (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) as Hec.
lazymatch type of Hdec with
| decode_any _ = Some (Jal ?rr ?ii, _) =>
  rewrite (step_jal_link SEGS regs (Z_to_bv 64 (BASE + k)) mem rom (Z_to_bv 32 wz) rr ii
  (pa_fetch_ok _ _ Hl) Hec Hdec)
end.
rewrite Hrd. f_equal. f_equal.
- unfold v_addi. rewrite unsigned_lit_small by lia. do 2 f_equal. lia.
- unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Ht, lit_canon.
  first [reflexivity | f_equal; lia].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the walk hypotheses of send_message_c.v this segment uses *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
(* the callee statement this segment applies *)
Hypothesis VR : forall fx0 : YK11.FPState, @tverbs_receive_spec fx0 rc SK PI B MT.
(* the read-only range facts arodata_ok_journalP asks *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Context {RO : ro_below_ofl SEGS RLO RHI}.
(* the per-binary record (the walk hypothesis HB) and the image facts (CmdRecBase.v cmd_img_facts), which the
   read-only law cmd_ro_ok_of_aro (CmdRecRo.v) takes *)
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
(* the per-binary record fact cmd_prog_unowned (CmdRecImg.v) *)
Let cmd_prog_unowned := CmdRecImg.cmd_prog_unowned SEGS B LAWS HB IMG.
(* the narrow per-binary facts this segment adds, each for exactly the addresses it names *)
Hypothesis SIGMA_verbs_receive : SIGMA CS_verbs_receive = BASE + AF_verbs_receive.
Hypothesis G_REC_PROG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) (as_prog_static B).
Hypothesis G_SPILL_PROG : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) (as_prog_static B).
Hypothesis G_QUITTING_PROG : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> Exists (in_zr a) (as_prog_static B).
Hypothesis CMD_PG_NOT_RO : forall a, inFP cmd_PG a -> ~ in_roP SEGS RLO RHI a.

(* P4 is a segment of a closed section: it holds at the FP state fx1 verbs_receive returns *)
Theorem sm_s4 : (forall fx0 : YK11.FPState, SM_P4_stmt (fx := fx0) B MT) -> SM_P3_stmt B MT.
Proof.
intros P4 ly S W regs mem md ch src n D R O rest lyc Sc Wc regs1 memc mdc k fpos res O1
CX JR Hk HRC R21 R22 HSV HFR V40 V48 Hres4096 HresO HPermc HO1O HnO1 HBY HREC HQ0 HBB MLE.
pose proof CX as (HPRE & HFRM & HFRS & HROD & HROK & HVOBJ & H10 & Hsrcr & H11 & Hn & HlenD & HBYs & Hinb
& HPerm & HRrep & HRcalls & HRref & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB4). pose proof pa_base_lo as HBLO.
pose proof JR as (HJ & Hfrs).
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & _ & Hnev & Hk0 & G1 & G2 & G3 & G4 & Ggone & Hpresc & Hstkc & G5 & HQTc).
pose proof HRC as (Rsp & Rgp & Rtp & Rs0 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R27).
assert (HSTK112 : 112 <= SEND_MESSAGE_STK) by (vm_compute; discriminate).
assert (HVRSTK : 0 <= VERBS_RECEIVE_STK) by (vm_compute; discriminate).
assert (HSTK1 : VERBS_RECEIVE_STK + 112 <= SEND_MESSAGE_STK) by (vm_compute; discriminate).
set (sp0 := spZ regs) in *.
destruct (sm_sp1_bounds sp0 Hal16 ltac:(lia)) as [Hsp1r Hsp1m].
(* this call's side-stack frame *)
assert (HFrIn : In (1, fpos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_layout _ _ LAWS ly S W mem md lyc HAR0 Hly) as (Eab & Efa & _).
assert (HFA : frame_addr lyc 1 fpos = frame_addr ly 1 fpos) by apply Efa.
destruct (frame_al64 SEGS B lyc Sc Wc memc mdc 1 fpos HARc HFrIn) as (HF64 & _ & _).
rewrite HFA in HF64.
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 fpos HARc HFrIn) as (HF4096 & HFceil & HFapp).
rewrite HFA in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
assert (HF8 : frame_addr ly 1 fpos mod 8 = 0) by (apply sm_mod64_8; exact HF64).
(* the live blocks at the call state *)
assert (HinRes : In (res, Z.max n 1) (ablocks B lyc Sc))
by (eapply Permutation_in; [apply Permutation_sym; exact HPermc|]; apply in_or_app; right; left; reflexivity).
assert (HinO1 : forall pn, In pn O1 -> In pn (ablocks B lyc Sc))
by (intros pn Hp; eapply Permutation_in; [apply Permutation_sym; exact HPermc|]; apply in_or_app; left; exact Hp).
assert (HinO : forall pn, In pn O -> In pn (ablocks B ly S))
by (intros pn Hp; eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_or_app; left; exact Hp).
(* the two footprints: the caller's (this segment's journal) and the call's *)
set (FP := ablocks_fp O ++ cmd_PG) in *.
set (FP1 := VERBS_RECEIVE_PG ++ ablocks_fp O1).
assert (HPGof : forall a, inFP VERBS_RECEIVE_PG a -> inFP cmd_PG a).
{ intros a Hf. unfold VERBS_RECEIVE_PG in Hf. unfold cmd_PG.
  apply inFP_cons in Hf as [Hf | Hf]; [apply inFP_cons; left; exact Hf|].
  apply inFP_cons in Hf as [Hf | Hf]; [apply inFP_cons; right; apply inFP_cons; left; exact Hf|].
  apply inFP_cons in Hf as [Hf | Hf];
  [apply inFP_cons; right; apply inFP_cons; right; apply inFP_cons; left; exact Hf | destruct (inFP_nil a Hf)]. }
assert (HFPceil : forall a, alloc_ceiling <= a -> ~ inFP FP a).
{ intros a Ha Hf. apply inFP_app in Hf as [Hf | Hf].
  - apply sm_inFP_ablocks in Hf as (b & m & Hb & Hr).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 (HinO _ Hb)) as (_ & _ & Hbc & _). lia.
  - destruct (cmd_prog_unowned a Hf) as (Himg & _). pose proof (pa_img_range a Himg). lia. }
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc memc)).
{ eapply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG B); [exact HJ | | exact HROD].
  intros a Hro Hf. apply inFP_app in Hf as [Hf | Hf].
  - apply sm_inFP_ablocks in Hf as (b & m & Hb & Hr).
    apply (blk_img SEGS B LAWS _ _ _ _ _ b m a HAR0 (HinO _ Hb) Hr).
    destruct Hro as [(sg & Hsg & _ & Hr2) | Hr2]; [exists sg; split; [exact Hsg | lia] | exact (RELRO_IMG a Hr2)].
  - exact (CMD_PG_NOT_RO a Hf Hro). }
assert (HROKc : cmd_ro_ok (rdW Wc memc))
by exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc memc mdc HARc HRODc).
(* ---- the two instructions: `mv a0,s5` (0x86c70) and `jal verbs_receive` (0x86c74) *)
assert (Hpl1 : plookup (@pl_tpi _ PL_cmd) SM_RET_RCL = Some (PW 0xa8513)) by (vm_compute; reflexivity).
assert (Hdec1 : decode_any (Z_to_bv 32 0xa8513) = Some (OpImm ALU_ADD 10%bv 21%bv 0%bv, 4%Z)) by vm_refl_bv.
assert (Hpl2 : plookup (@pl_tpi _ PL_cmd) (SM_RET_RCL + 4) = Some (PCall CS_verbs_receive (1%bv : Prelude.reg)))
by (vm_compute; reflexivity).
eapply (SRr_step SEGS pa_wx Wc _ _ mdc); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  exact (step_addi_at SEGS regs1 (Z_to_bv 64 (BASE + SM_RET_RCL)) (mrestrict (w_H Wc) memc) (seg_rom SEGS)
  (Z_to_bv 32 0xa8513) 10%bv 21%bv 0%bv _ (pa_fetch_pw _ _ Hpl1)
  (not_ecall_of_decode _ _ _ Hdec1 ltac:(discriminate)) Hdec1 ltac:(vm_compute; reflexivity) eq_refl). }
intros md1 Hsm1.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
assert (Epc1 : v_addi (Z_to_bv 64 (BASE + SM_RET_RCL)) 4 = Z_to_bv 64 (BASE + (SM_RET_RCL + 4))).
{ unfold v_addi. rewrite unsigned_lit_small by (unfold SM_RET_RCL, AF_send_message; lia). f_equal. lia. }
rewrite Epc1.
set (regsA := regupd regs1 10%bv (v_addi (getr regs1 21%bv) (bv_signed (0%bv : bv 12)))).
eapply (SRr_step SEGS pa_wx Wc _ _ md1); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  exact (sm_step_pcall (SM_RET_RCL + 4) CS_verbs_receive (1%bv : Prelude.reg) regsA
  (mrestrict (w_H Wc) memc) (seg_rom SEGS) Hpl2 ltac:(vm_compute; reflexivity)
  ltac:(unfold SM_RET_RCL, AF_send_message; lia)). }
intros md2 Hsm2.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict. rewrite SIGMA_verbs_receive.
set (regsc := regupd regsA 1%bv (Z_to_bv 64 (BASE + (SM_RET_RCL + 4 + 4)))).
(* neither instruction writes, so the journal carries over *)
assert (HJ2 : ajournal SEGS B SEND_MESSAGE_STK sp0 FP ly S W mem md [(1, fpos)] lyc Sc Wc memc md2 k).
{ rewrite (same_but_materialized_wvb md1 md2 Hsm2), (same_but_materialized_wvb mdc md1 Hsm1).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low).
  apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
(* the registers at the call *)
assert (Qsp : spZ regsc = sp0 + (sm_sp1 sp0 - sp0)).
{ unfold spZ, regsc, regsA. sm_getr. rewrite Rsp. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (Q10 : getr regsc 10%bv = w64 (frame_addr ly 1 fpos + 32)).
{ unfold regsc, regsA. sm_getr. change (bv_signed (0%bv : bv 12)) with 0.
  rewrite v_addi_0. exact R21. }
assert (Q3 : getr regsc 3%bv = w64 (as_gp B)) by (unfold regsc, regsA; sm_getr; rewrite Rgp; exact Hgp).
assert (Q4 : getr regsc 4%bv = w64 (as_tp B)) by (unfold regsc, regsA; sm_getr; rewrite Rtp; exact Htp).
assert (Q1 : getr regsc 1%bv = Z_to_bv 64 (BASE + SM_RET_VR))
by (unfold regsc; sm_getr; f_equal; unfold SM_RET_VR, SM_RET_RCL, AF_send_message; lia).
assert (Qs0 : s0Z regsc = sp0) by (unfold s0Z, regsc, regsA; sm_getr; rewrite Rs0; reflexivity).
assert (Hcs : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regsc rr = getr regs1 rr).
{ intros rr Hrr. unfold regsc, regsA.
  rewrite (getr_other _ 1%bv _ rr); [rewrite (getr_other _ 10%bv _ rr); [reflexivity|]|];
  intros Hq; subst rr; unfold acallee_saved in Hrr; rewrite bv_unsigned_BV in Hrr; lia. }
(* the frame chain at the realigned stack pointer *)
destruct (sm_achain B FP ly S W regs mem md ch fpos lyc Sc Wc memc mdc k HPRE JR HFPceil HSV) as [ch1 Hch1].
(* what the call cannot touch: this call's frame and its shadow, and the caller's saved words *)
assert (HSHAD : forall x, shadow_addr (frame_addr ly 1 fpos) <= x < shadow_addr (frame_addr ly 1 fpos) + 16 ->
kLowMemEnd <= x /\ x < kHighMemBeg).
{ intros x Hx.
  assert (Hd0 : 0 <= frame_addr ly 1 fpos / 8) by (apply Z.div_pos; lia).
  assert (Hdhi : frame_addr ly 1 fpos / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  unfold shadow_addr, SHADOW_OFF in Hx. unfold kLowMemEnd, kHighMemBeg. lia. }
assert (KFRAME : forall a, (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
shadow_addr (frame_addr ly 1 fpos) <= a < shadow_addr (frame_addr ly 1 fpos) + 16) -> ~ inFP FP1 a).
{ intros a Ha Hf. apply inFP_app in Hf as [Hf | Hf].
  - destruct (cmd_prog_unowned a (HPGof a Hf)) as (Himg & _). pose proof (pa_img_range a Himg) as Hr.
    destruct Ha as [Ha | Ha]; [|destruct (HSHAD a Ha); unfold kLowMemEnd in *; lia].
    exact (frm_img SEGS B LAWS lyc Sc Wc memc mdc 1 fpos a HARc HFrIn
    ltac:(rewrite HFA; change (fs_frame_bytes 1) with 128; lia) Himg).
  - apply sm_inFP_ablocks in Hf as (b & m & Hb & Hr). pose proof (HinO1 _ Hb) as Hbc.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hbc) as (_ & Hb4096 & Hbceil & Hbapp & _).
    destruct Ha as [Ha | Ha].
    + pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 1 fpos HARc Hbc HFrIn) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFA in Hd.
      change (fs_frame_bytes 1) with 128 in Hd. lia.
    + destruct (HSHAD a Ha) as [Hx1 Hx2].
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd in *. lia. }
assert (KSTACK : forall a, sp0 - 88 <= a < sp0 -> ~ inFP FP1 a).
{ intros a Ha Hf. apply inFP_app in Hf as [Hf | Hf].
  - destruct (cmd_prog_unowned a (HPGof a Hf)) as (Himg & _). pose proof (pa_img_range a Himg). lia.
  - apply sm_inFP_ablocks in Hf as (b & m & Hb & Hr).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc (HinO1 _ Hb)) as (_ & _ & Hbceil & _). lia. }
(* ---- the call: verbs_receive's post is apost_baseF, so the F rule (PaFx.v cl_callS_pgF), and the rest of the walk
   at the FP state it returns (srr_after_callF) *)
unfold sm_post.
eapply srr_after_callF;
[ eapply (cl_callS_pgF B LAWS Wc regsc memc (Z_to_bv 64 (BASE + AF_verbs_receive))
SEND_MESSAGE_STK sp0 FP ly S W mem md [(1, fpos)] lyc Sc md2 k VERBS_RECEIVE_STK FP1
(ev_vr (RecModel.rec_clear R) D) (sm_sp1 sp0 - sp0) (Z_to_bv 64 (BASE + SM_RET_VR)) ch1
(fun ly2 S2 W2 regs2 mem2 md2' =>
 let '(R', _, quit) := vr_runA (RecModel.rec_clear R) D in
 exists O' : list (Z * Z),
 rec_repA B ly2 S2 (rdW W2 mem2) R' O' /\
 aval_mem (rdW W2 mem2) A_G_QUITTING 4 (if quit then 1 else 0) /\
 Permutation (ablocks B ly2 S2) (O' ++ (res, Z.max n 1) :: rest) /\
 ~ In (res, Z.max n 1) O' /\
 aval_mem (rdW W2 mem2) (frame_addr ly 1 fpos + 32 + 8) 8 res /\
 blocks_bytes S2 <= blocks_bytes Sc + LIVE_VERBS_RECEIVE /\
 mo_le MT Sc S2 (XM_VERBS_RECEIVE MT (RecModel.rec_clear R) D)) HJ2 Qsp) | ].
- (* o mod 16 = 0 *)
  rewrite Zminus_mod, Hsp1m, Hal16. reflexivity.
- lia.
- exact HVRSTK.
- lia.
- exact Q3.
- exact Q4.
- exact Q1.
- apply ret_ok_codeptr_v; [unfold SM_RET_VR, AF_send_message; lia | reflexivity].
- rewrite unsigned_lit_small by (unfold SM_RET_VR, AF_send_message; lia).
  unfold SM_RET_VR, AF_send_message. lia.
- rewrite Qs0. replace (sp0 + (sm_sp1 sp0 - sp0)) with (sm_sp1 sp0) by lia. exact Hch1.
- (* verbs_receive's contract at the call state *)
  intros HPRE1. eapply SRr_mono;
  [ eapply (VR fx lyc Sc Wc regsc memc md2 ch1 (frame_addr ly 1 fpos + 32) 7 res n 0 D
  (RecModel.rec_clear R) O1 ((res, Z.max n 1) :: rest) HPRE1 HFRM HRODc Q10) | ].
  + (* msg is in this call's frame, below alloc_ceiling *)
    lia.
  + (* afobj: the message struct is 24 bytes of this call's class-1 frame *)
    split; [exists 1, fpos; rewrite HFA; change (fs_frame_bytes 1) with 128;
    split; [exact HFrIn | repeat split; lia]|].
    assert (H32 : (frame_addr ly 1 fpos + 32) mod 8 = 0)
    by (replace (frame_addr ly 1 fpos + 32) with (frame_addr ly 1 fpos + 4 * 8) by lia;
        rewrite Z_mod_plus_full; exact HF8).
    split; [exact H32|].
    apply zero_shadow_range; [exact H32 | reflexivity |].
    pose proof HFR as (_ & VM32 & VS4 & VS5 & VS6).
    assert (Esh : shadow_of_addr SHADOW_OFF (frame_addr ly 1 fpos + 32) = SB_F (frame_addr ly 1 fpos) + 4).
    { rewrite (shadow_of_addr_aligned_off SHADOW_OFF (frame_addr ly 1 fpos) 32 HF8).
      unfold shadow_of_addr, SB_F, SB, SHADOW_OFF. change (32 / 8) with 4. lia. }
    intros i Hi. change (24 / 8) with 3 in Hi. rewrite Esh.
    assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hi3 as [-> | [-> | ->]];
    [ replace (SB_F (frame_addr ly 1 fpos) + 4 + 0) with (SB_F (frame_addr ly 1 fpos) + 4) by lia;
      exact (aview_of_val_mem1 SEGS (w_H Wc) memc _ 0 VS4 ltac:(lia))
    | replace (SB_F (frame_addr ly 1 fpos) + 4 + 1) with (SB_F (frame_addr ly 1 fpos) + 5) by lia;
      exact (aview_of_val_mem1 SEGS (w_H Wc) memc _ 0 VS5 ltac:(lia))
    | replace (SB_F (frame_addr ly 1 fpos) + 4 + 2) with (SB_F (frame_addr ly 1 fpos) + 6) by lia;
      exact (aview_of_val_mem1 SEGS (w_H Wc) memc _ 0 VS6 ltac:(lia)) ].
  + (* msg.sender_id = 7 *)
    pose proof HFR as (_ & VM32 & _). exact (sm_aval_of_val SEGS _ _ _ _ _ VM32).
  + (* msg.data = res *)
    replace (frame_addr ly 1 fpos + 32 + 8) with (frame_addr ly 1 fpos + 40) by lia.
    exact (sm_aval_of_val SEGS _ _ _ _ _ V40).
  + (* the copy's block lies below alloc_ceiling *)
    destruct (al_blocks _ _ LAWS _ _ _ _ _ res (Z.max n 1) HARc HinRes) as (_ & _ & Hrc & _).
    pose proof (req_size_pos (Z.max n 1) ltac:(lia)). lia.
  + (* msg.data_size = n *)
    replace (frame_addr ly 1 fpos + 32 + 16) with (frame_addr ly 1 fpos + 48) by lia.
    exact (sm_aval_of_val SEGS _ _ _ _ _ V48).
  + lia.
  + exact HlenD.
  + exact HinRes.
  + exact HnO1.
  + exact HBY.
  + exact HREC.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + (* rec_clear keeps refuse and code *)
    cbn [RecModel.rec_clear r_refuse r_code]. exact HRref.
  + exact HPermc.
  + exact HQ0.
  + exact HROKc.
  + exact HVOBJ.
  + (* at most 4 live frames at verbs_receive's entry *)
    rewrite Hfrs. cbn [length]. rewrite Nat2Z.inj_succ. lia.
  + (* the events *)
    unfold EV_SEND_MESSAGE in HEV. lia.
  + (* the live bytes *)
    assert (Eb : blocks_bytes Sc = bsum (ablocks B lyc Sc)) by apply blocks_bytes_bsum.
    assert (Eb0 : blocks_bytes S = bsum (ablocks B ly S)) by apply blocks_bytes_bsum.
    rewrite (bsum_perm _ _ HPermc) in Eb. rewrite (bsum_perm _ _ HPerm) in Eb0.
    rewrite bsum_app, bsum_cons in Eb. rewrite bsum_app in Eb0. cbn [snd] in Eb.
    assert (HNDc : List.NoDup (ablocks B lyc Sc)).
    { destruct (al_sep _ _ LAWS lyc Sc Wc memc mdc HARc) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
      revert Hp. assert (Hall : forall pn, In pn (ablocks B lyc Sc) -> 0 <= snd pn).
      { intros [b m] Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hb) as (_ & _ & _ & _ & _ & _ & Hm).
        cbn [snd]. lia. }
      revert Hall. generalize (ablocks B lyc Sc) as l. intros l.
      induction l as [|[b m] l IH]; intros Hall Hp; [constructor|].
      cbn [map pairwise] in Hp. destruct Hp as [HFa Hp].
      constructor; [|apply IH; [intros pn Hpn; apply Hall; right; exact Hpn | exact Hp]].
      intros Hin. pose proof (proj1 (Forall_forall _ _) HFa (b, req_size m)
      (in_map (fun x : Z * Z => (fst x, req_size (snd x))) l (b, m) Hin)) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      pose proof (Hall (b, m) ltac:(left; reflexivity)) as Hm. cbn [snd] in Hm.
      pose proof (req_size_pos m Hm) as [Hq _]. lia. }
    assert (HNDO1 : List.NoDup O1).
    { apply (Permutation_NoDup HPermc) in HNDc. apply NoDup_remove_1 in HNDc.
      exact (NoDup_app_remove_r _ _ HNDc). }
    assert (HFO : Forall (fun b : Z * Z => 0 <= snd b) O).
    { apply Forall_forall. intros [b m] Hb.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 (HinO _ Hb)) as (_ & _ & _ & _ & _ & _ & Hm).
      cbn [snd]. lia. }
    assert (Hle : bsum O1 <= bsum O) by (apply sm_bsum_incl; [exact HNDO1 | exact HO1O | exact HFO]).
    unfold LIVE_SEND_MESSAGE in HLIVE. lia.
  + (* the meter *)
    apply (mo_ok_step MT MTL S Sc (mo_malloc MT 8192 + XM_REC_CLEAR MT R)
    (XM_VERBS_RECEIVE MT (RecModel.rec_clear R) D)); [|exact MLE].
    apply (mo_ok_le MT MTL S _ (XM_SEND_MESSAGE MT R D)); [exact HMOK|].
    unfold XM_SEND_MESSAGE. pose proof (mo_free_nonneg MT MTL). lia.
  + (* verbs_receive's post, in the shape the F rule asks *)
    cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2' & -> & Hf1 & Hf2 & HJc & HP2 & HK2).
    exists fx2, ly2, S2, regs2, mem2, md2'. split; [rewrite Q1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|].
    split; [exact HJc|]. split; [exact HP2|]. revert HK2.
    destruct (vr_runA (RecModel.rec_clear R) D) as [[R' x'] quit].
    intros (O' & HRec & HQuit & HPerm2 & HnD & HBY2 & VFfd & VFdata & VFn & HBB2 & MLE2).
    exists O'. split; [exact HRec|]. split; [exact HQuit|]. split; [exact HPerm2|].
    split; [exact HnD|]. split; [exact VFdata|]. split; [exact HBB2 | exact MLE2].
- (* the call's footprint lies inside the caller's *)
  intros a Hf. left. apply inFP_app in Hf as [Hf | Hf].
  + split; [unfold FP; apply inFP_app; right; exact (HPGof a Hf)|].
    right. split; [|exact (proj1 (cmd_prog_unowned a (HPGof a Hf)))].
    unfold VERBS_RECEIVE_PG in Hf.
    apply inFP_cons in Hf as [Hf | Hf]; [exact (G_REC_PROG a Hf)|].
    apply inFP_cons in Hf as [Hf | Hf]; [exact (G_SPILL_PROG a Hf)|].
    apply inFP_cons in Hf as [Hf | Hf]; [exact (G_QUITTING_PROG a Hf) | destruct (inFP_nil a Hf)].
  + apply sm_inFP_ablocks in Hf as (b & m & Hb & Hr). split.
    * unfold FP. apply inFP_app. left. apply sm_inFP_ablocks. exists b, m. split; [exact (HO1O _ Hb) | exact Hr].
    * left. exists b, m. split; [exact (HinO1 _ Hb) | exact Hr].
- (* ---- P4 at the return (0x86c78), at the FP state fx1 verbs_receive returned *)
  intros fx1 ly2 S2 W2 regs2 mem2 md2' _ Hfx (HJ3 & HJc & HP2 & HK2).
  (* the post back in P4's form at fx1, so that the case split on vr_runA below leaves it alone *)
  change (SRr SEGS W2 (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + SM_RET_VR)) mem2 (seg_rom SEGS)) md2')
    (sm_post (fx := fx1) B MT ly S W regs mem md R D O rest)).
  revert HK2.
  destruct (vr_runA (RecModel.rec_clear R) D) as [[R' x'] quit] eqn:EVR.
  intros (O' & HRec & HQuit & HPerm2 & HnD & VFdata & HBB2 & MLE2).
  assert (Hcs2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regs1 rr).
  { intros rr Hrr. rewrite <- (Hcs rr Hrr).
    pose proof (HP2 (bv_unsigned rr) Hrr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. }
  assert (HKEEP : forall a, (frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
  shadow_addr (frame_addr ly 1 fpos) <= a < shadow_addr (frame_addr ly 1 fpos) + 16) ->
  rdW W2 mem2 a = rdW Wc memc a).
  { intros a Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
    apply (K4 1 fpos a HFrIn); [|exact (KFRAME a Ha)].
    unfold frame_rng, in_zr. cbn [fst snd]. rewrite HFA.
    change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. exact Ha. }
  assert (HKSTK : forall a, sp0 - 88 <= a < sp0 -> rdW W2 mem2 a = rdW Wc memc a).
  { intros a Ha. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _).
    apply K1; [lia | lia | exact (KSTACK a Ha)]. }
  assert (CX1 : sm_cx (fx := fx1) B MT ly S W regs mem md ch src n D R O rest)
  by exact (conj HPRE (conj (fxrel_frm0 fx fx1 HFRM Hfx) (proj2 (proj2 CX)))).
  apply (P4 fx1 ly S W regs mem md ch src n D R O rest ly2 S2 W2 regs2 mem2 md2'
  (k + ev_vr (RecModel.rec_clear R) D) fpos res CX1).
  + (* the journal from the entry, with this call's frame on top *)
    split; [exact HJ3|].
    pose proof HJc as (_ & _ & _ & _ & _ & Hfrs2 & _). rewrite Hfrs2. exact Hfrs.
  + lia.
  + (* the callee-saved registers *)
    split; [rewrite (Hcs2 2%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Rsp|].
    split; [rewrite (Hcs2 3%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Rgp|].
    split; [rewrite (Hcs2 4%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Rtp|].
    split; [rewrite (Hcs2 8%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact Rs0|].
    split; [rewrite (Hcs2 9%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact R9|].
    split; [rewrite (Hcs2 18%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact R18|].
    split; [rewrite (Hcs2 19%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact R19|].
    split; [rewrite (Hcs2 20%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact R20|].
    split; [rewrite (Hcs2 23%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact R23|].
    split; [rewrite (Hcs2 24%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact R24|].
    split; [rewrite (Hcs2 25%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact R25|].
    split; [rewrite (Hcs2 26%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)); exact R26|].
    rewrite (Hcs2 27%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact R27.
  + rewrite (Hcs2 21%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact R21.
  + rewrite (Hcs2 22%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact R22.
  + (* the prologue's saved words are still on the caller's stack *)
    intros o r Ho.
    assert (Hor : -88 <= o <= -8)
    by (unfold sm_saved_list in Ho; cbn in Ho;
        repeat (destruct Ho as [Hq | Ho]; [injection Hq as <- <-; lia|]); destruct Ho).
    apply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2 (sp0 + o) (sp0 + o) 8);
    [intros j Hj; apply HKSTK; lia | exact (HSV o r Ho)].
  + (* the frame's bytes are kept *)
    pose proof HFR as (VFL & VM32 & VS4 & VS5 & VS6).
    assert (Esh : SB_F (frame_addr ly 1 fpos) = shadow_addr (frame_addr ly 1 fpos)) by reflexivity.
    split; [ apply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2 (frame_addr ly 1 fpos + 120) _ 8);
    [intros j Hj; apply HKEEP; left; lia | exact VFL] |].
    split; [ apply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2 (frame_addr ly 1 fpos + 32) _ 4);
    [intros j Hj; apply HKEEP; left; lia | exact VM32] |].
    split; [ apply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2 (SB_F (frame_addr ly 1 fpos) + 4) _ 1);
    [intros j Hj; apply HKEEP; right; rewrite Esh; lia | exact VS4] |].
    split; [ apply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2 (SB_F (frame_addr ly 1 fpos) + 5) _ 1);
    [intros j Hj; apply HKEEP; right; rewrite Esh; lia | exact VS5] |].
    apply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2 (SB_F (frame_addr ly 1 fpos) + 6) _ 1);
    [intros j Hj; apply HKEEP; right; rewrite Esh; lia | exact VS6].
  + (* msg.data is still res *)
    replace (frame_addr ly 1 fpos + 40) with (frame_addr ly 1 fpos + 32 + 8) by lia.
    apply sm_val_of_aval. exact VFdata.
  + exact Hres4096.
  + exact HresO.
  + (* the recorder, the quit flag and the blocks after the call *)
    rewrite EVR. exists O'. split; [exact HRec|]. split; [exact HQuit|].
    split; [exact HPerm2 | exact HnD].
  + (* the live bytes: rec_clear's bound and verbs_receive's *)
    lia.
  + (* the meter *)
    exact (mle_station MT S Sc S2 _ _ MTL MLE MLE2).
Qed.
End e.
End f.
End d.
