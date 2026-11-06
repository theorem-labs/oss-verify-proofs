(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: descriptors_panel_get's walk from the call of rec_shape_of (0x8d204) to its end (plugin-hostd/fuzz_command.asan), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a call composed with the callee's contract, then a run from a fresh seed) and lib/A/Prog/sup_reply_code.v (the frame released and a tail jump into a callee whose post gives the caller's). *)

(* 0x8d204 .. 0x8d230: rec_shape_of finds the reply shape of the verb "panel_get" (0x21f80, 9 bytes; a read-only
   string of the image); at 0x8d208 a1 := the shape, a0 := the slot c (s0), a2 := 0, the epilogue loads ra and
   s0 .. s4 from the frame and adds 48 to sp, and `j answer` runs answer at the entry's stack pointer with the
   entry's return address. The segment has no inline check. answer's post is the contract's post through s6.v's
   dpg_post_of. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
xstrdup_c hand_back_c rec_shape_of_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_panel_get_c descriptors_panel_get_s1 descriptors_panel_get_s2 descriptors_panel_get_s3
descriptors_panel_get_s4 descriptors_panel_get_s6.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the verb's bytes are RO_lit_21f80 without its terminator *)
Lemma dpg8_verb_lit : dpg_verb ++ [Z_to_bv 8 0] = RO_lit_21f80.
Proof. vm_compute. reflexivity. Qed.
Lemma dpg8_verb_len : length dpg_verb = 9%nat.
Proof. reflexivity. Qed.
Lemma dpg8_fits : fits (shape_of dpg_verb).
Proof. unfold fits. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma dpg8_abytes_prefix : forall rd a (l1 l2 : list byte), abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof.
intros rd a l1 l2 H i Hi. rewrite (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 by exact Hi. reflexivity.
Qed.
(* a register index as a 5-bit literal *)
Lemma dpg8_z5 : forall (rr : bv 5) r, bv_unsigned rr = r -> Z_to_bv 5 r = rr.
Proof. intros rr r <-. apply Z_to_bv_bv_unsigned. Qed.
(* a member of a filtered list is a member of the list (the filter of answer_c.v's footprint) *)
Lemma dpg8_filter_in : forall (old : Z) (l : list (Z * Z)) x, In x (filter (fun pn => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|a l IH]; intros H; cbn in H; [exact H|].
repeat match type of H with context [match ?d with left _ => _ | right _ => _ end] => destruct d end;
repeat match type of H with context [if ?b then _ else _] => destruct b end;
first [ destruct H as [<- | H]; [left; reflexivity | right; exact (IH H)] | right; exact (IH H) ].
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
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.

Lemma dpg8_sig_rso : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite (SIGP CS_rec_shape_of ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma dpg8_sig_ans : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (SIGP CS_answer ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.

(* what the walk keeps of rec_shape_of's post (rec_shape_of_c.v:100-105, v = "panel_get") *)
Definition dpg8_Krso (lyc : alayout) (Sc : astate) :
alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 (exists q, getr regs' 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
  forall O, astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) O q (Some (shape_of dpg_verb))) /\
 Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc.

(* the verb "panel_get" (0x21f80) as rec_shape_of's string argument: astr_argA's read-only arm, the record's
   checks decided on the concrete lists *)
Lemma dpg8_verb_argA : forall ly S rd O, abytes_atR rd 0x21f80 RO_lit_21f80 ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O 0x21f80 (Some dpg_verb).
Proof.
intros ly S rd O HL. unfold astr_argA. cbv zeta. rewrite dpg8_verb_len. change (Z.of_nat 9) with 9.
change (9 + 1) with 10.
split; [lia|]. split.
{ split; [rewrite dpg8_verb_lit; exact HL|].
  unfold dpg_verb. cbn [map In]. intros H. repeat (destruct H as [H|H]; [vm_compute in H; discriminate H|]). exact H. }
split; [unfold LMAX; lia|]. right. split; [|split; [vm_compute; reflexivity | split; [vm_compute; reflexivity|]]].
- intros i Hi. split; [|split].
  + clear - CMD_RO_IN Hi. unfold cmd_ro_in in CMD_RO_IN.
    repeat match type of CMD_RO_IN with
    | (forall i, 0 <= i < 10 -> _ (0x21f80 + i)) /\ _ => exact (proj1 CMD_RO_IN i Hi)
    | _ /\ _ => apply proj2 in CMD_RO_IN
    end.
  + rewrite (ts_owned B HB). apply (dpg_not_in_ranges _ 0x21f80 (0x21f80 + 10)); [vm_compute; reflexivity | lia].
  + rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
- assert (Hb : existsb (Z.eqb (0x21f80 + 9)) cmd_ro_ends = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hb as (e & He & Heq). apply Z.eqb_eq in Heq. rewrite Heq. exact He.
Qed.

(* astr_argA reads its reader only through the string's bytes *)
Lemma dpg8_argA_rd : forall ly S rd rd' O p x, astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (p + i)) ->
astr_argA B ly S rd' (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros ly S rd rd' O p x H Hk. unfold astr_argA in *. cbv zeta in *.
destruct H as (H0 & [Hb Hnz] & Hl & Harm). split; [exact H0|]. split; [|split; [exact Hl | exact Harm]].
split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

(* the bytes of such a string lie in a heap block or in the image *)
Lemma dpg8_argA_bound : forall ly S (W : world SEGS) mem md rd O p x, AR SEGS B ly S W mem md -> 0 <= p ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= p + i < 2 ^ 64.
Proof.
intros ly S W mem md rd O p x HAR Hp H i Hi. unfold astr_argA in H. cbv zeta in H.
pose proof asan_consts as (C1 & _).
destruct H as (_ & _ & _ & [((pb & kb & Hin & Hlo & Hhi) & _) | (Hro & _)]).
- destruct (al_blocks _ _ LAWS ly S W mem md pb kb HAR Hin) as (_ & _ & Hc & _ & _ & _ & Hk).
  pose proof (req_size_pos kb ltac:(lia)) as [_ Rk]. lia.
- destruct (Hro i Hi) as (Hr & _). destruct (cmd_ro_prog_apart _ Hr) as [Himg _].
  pose proof (pa_img_range _ Himg). lia.
Qed.

(* the walk's footprint lies below the allocator's ceiling, so below every stack byte *)
Lemma dpg8_FP_low : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> forall a, inFP (dpg_FP O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O HAR HO a Ha. pose proof asan_consts as (C1 & _).
destruct (dpg_inFP O a Ha) as [[Hg | Hg] | (pb & nb & Hpn & Hr)].
- unfold A_G_REC, REC_SIZE in Hg. lia.
- unfold A_REC_SPILL, SC_SIZE in Hg. lia.
- destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR (HO _ Hpn)) as (_ & _ & Hc & _). lia.
Qed.

Lemma dpg_R_holds : dpg_R_stmt B MT.
Proof.
intros ly S W regs mem md ch pu x R O CTX lyc Sc O1 ly2 S2 W2 regs2 mem2 md2 Q2 p
  BLK HJ2 MLE2 HBB2 HPerm2 Hap2 Hp4096 HREC2 HQ2 Hsp2 R3 R4 R1 R8 R10 R11 Rhi HFR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CTX as (HPRE & HFRM & HROD & HRO & H10 & Hpu & HBLK0 & HSTR0 & HLEN & HAPO & HREP & Hfr8 & Hev & Hlive & MOK).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof BLK as (Bsub & Bgone & BO1 & BO1g & Bperm).
pose proof HREP as (Q & HQ & HQO).
pose proof HQ as (_ & _ & _ & (HL16 & _) & _).
destruct (dpg_c_ok R HL16) as (Hc1 & Hc2 & Hc8 & Hc3).
assert (Hc64 : 0 <= dpg_c R < 2 ^ 64) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (rec_repA_in B ly S (rdW W mem) R O HREP).
pose proof (proj1 HJ2) as HAR2.
assert (HSTK1 : REC_SHAPE_OF_STK + 48 <= DPG_STK /\ ANSWER_STK <= DPG_STK)
  by (unfold DPG_STK, DESCRIPTORS_PANEL_GET_STK; lia).
assert (HSTKp : 0 <= REC_SHAPE_OF_STK /\ 0 <= ANSWER_STK) by (unfold REC_SHAPE_OF_STK, ANSWER_STK, ESTACK; lia).
(* the model's step: rec_stub of the call (24, [x]) with the shape of "panel_get" and changes = 0 *)
assert (HM : descriptors_panel_get_m R (Some x) =
  rec_answer (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (REC_DESCRIPTORS_PANEL_GET, [x]) (shape_of dpg_verb) false).
{ unfold descriptors_panel_get_m, rec_stub, daemon_shape. rewrite <- dpg_verb_bstr. reflexivity. }
(* ---------- the call of rec_shape_of("panel_get", 9) ---------- *)
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2))
  by exact (dpg_rodata_kept B cmd_ro_prog_apart _ _ ly S W mem md O [] ly2 S2 W2 mem2 md2 _ HAR0 HOin HJ2 HROD).
pose proof (cmd_ro_ok_of_aro ly2 S2 W2 mem2 md2 HAR2 HROD2) as HRO2.
assert (HLIT : abytes_atR (rdW W2 mem2) 0x21f80 RO_lit_21f80).
{ clear - HRO2. destruct HRO2 as [HRO2 _]. unfold cmd_ro_bytes in HRO2.
  repeat match type of HRO2 with
  | abytes_atR _ 0x21f80 _ /\ _ => exact (proj1 HRO2)
  | abytes_atR _ 0x21f80 _ => exact HRO2
  | _ /\ _ => apply proj2 in HRO2
  end. }
assert (HVERB : Z.of_nat (length dpg_verb) <= 16 ->
  abytes_atR (rdW W2 mem2) 0x21f80 dpg_verb /\
  (in_blockA (ablocks B ly2 S2) 0x21f80 (Z.of_nat (length dpg_verb)) \/
   astr_argA B ly2 S2 (rdW W2 mem2) (in_roP SEGS RLO RHI) [] 0x21f80 (Some dpg_verb))).
{ intros _. split.
  - apply (dpg8_abytes_prefix _ _ _ [Z_to_bv 8 0]). rewrite dpg8_verb_lit. exact HLIT.
  - right. exact (dpg8_verb_argA ly2 S2 (rdW W2 mem2) [] HLIT). }
assert (HEV2 : st_nev S2 + EV_REC_SHAPE_OF <= EV_MAX).
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
  unfold EV_DESCRIPTORS_PANEL_GET, EV_REC_SHAPE_OF, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in *. lia. }
assert (R11' : getr regs2 11 = w64 (Z.of_nat (length dpg_verb))) by (rewrite dpg8_verb_len; exact R11).
assert (HSP2 : spZ regs2 = spZ regs + -48) by (rewrite Hsp2; unfold DPG_FRAME; lia).
rewrite dpg8_sig_rso.
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W2 regs2 mem2 _ DPG_STK (spZ regs) (dpg_FP O) ly S W mem md [] ly2 S2 md2
    (rec_spill_frees R + EV_XSTRDUP) REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-48) (getr regs2 1) (dpg8_Krso ly2 S2)
    HJ2 HSP2).
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [unfold DPG_RET_R, AF_descriptors_panel_get; lia | reflexivity].
  - rewrite R1, unsigned_lit_small by (unfold DPG_RET_R, AF_descriptors_panel_get; lia).
    unfold DPG_RET_R, AF_descriptors_panel_get. lia.
  - intros HPRE1. eapply SRr_mono.
    + exact (TREC_SHAPE_OF fx ly2 S2 W2 regs2 mem2 md2 0x21f80 dpg_verb HPRE1 HROD2 R10 ltac:(lia) R11'
        ltac:(rewrite dpg8_verb_len; lia) HRO2 VOBJS HVERB HEV2).
    + cbv beta. intros Wx cx _ (lyx & Sx & regsx & memx & mdx & -> & HJx & HPx & HKx).
      exists lyx, Sx, regsx, memx, mdx. split; [reflexivity|]. split; [exact HJx|]. split; [exact HPx | exact HKx].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as ((q & Hq10 & Hq64 & HqA) & _ & Ely3 & ES3). subst ly3 S3.
rewrite R1.
(* ---------- back at 0x8d208: the registers rec_shape_of keeps, the frame ---------- *)
assert (CS3 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs3 rr = getr regs2 rr)
  by (intros rr Hr; pose proof (HP3 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (X2 : getr regs3 2 = getr regs2 2) by (apply CS3; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X3 : getr regs3 3 = getr regs2 3) by (apply CS3; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X4 : getr regs3 4 = getr regs2 4) by (apply CS3; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X8 : getr regs3 8 = getr regs2 8) by (apply CS3; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (Hsp3 : spZ regs3 = spZ regs - 48) by (unfold spZ in *; rewrite X2; unfold DPG_FRAME in Hsp2; exact Hsp2).
assert (HspR3 : 2 ^ 46 <= spZ regs3 <= 2 ^ 47 - 48) by (rewrite Hsp3; lia).
assert (Hsp16 : spZ regs3 mod 16 = 0).
{ rewrite Hsp3. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & GX1 & GX2 & GX3 & _).
assert (HFR3 : forall j r, nth_error dpg_saved j = Some r ->
  aval_mem (rdW W3 mem3) (spZ regs3 + 40 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj6 : (j < 6)%nat) by (apply (proj1 (nth_error_Some dpg_saved j)); rewrite Hj; discriminate).
  rewrite Hsp3. apply (aval_mem_kept (rdW W2 mem2)).
  - replace (spZ regs - 48 + 40 - 8 * Z.of_nat j) with (spZ regs - 8 - 8 * Z.of_nat j) by lia. exact (HFR j r Hj).
  - intros kk Hkk. apply GX1; [lia | lia | intros (r' & [] & _)]. }
destruct (dpg_tail_seed W3 mem3 regs3 regs HspR3 Hsp16 HFR3) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs3 (dpg_extra regs)))) by apply Eimg_env.
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs3 (dpg_extra regs))) n = getr regs3 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j (rr : bv 5), nth_error dpg_saved j = Some (bv_unsigned rr) ->
  ew (Eimg (Ereg regs3 (dpg_extra regs))) (32 + j) = getr regs rr).
{ intros j rr Hj. assert (Hj6 : (j < 6)%nat) by (apply (proj1 (nth_error_Some dpg_saved j)); rewrite Hj; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
  assert (Hx : nth_error (dpg_extra regs) j = Some (getr regs (Z_to_bv 5 (bv_unsigned rr))))
    by (unfold dpg_extra; rewrite nth_error_map, Hj; reflexivity).
  rewrite (nth_error_nth _ _ _ Hx), Z_to_bv_bv_unsigned. reflexivity. }
remember (Eimg (Ereg regs3 (dpg_extra regs))) as E eqn:HE.
(* 0x8d208 .. 0x8d230: a1 := the shape, a0 := c, a2 := 0, the frame restored, then `j answer` *)
paj_run_tok RUN HS HJ3 SHOK Bspan.
{ awr_ok_tac. }
rewrite ?wvb_collapse in HJ3.
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  set (rgT := rg) in *; set (mT := mm) in *; set (mdT := mdq) in *
end.
clearbody mdT.
(* the registers at the tail jump *)
assert (S1 : getr rgT 1 = getr regs 1) by (rewrite T1; exact (EX 0%nat 1%bv eq_refl)).
assert (S8 : getr rgT 8 = getr regs 8) by (rewrite T8; exact (EX 1%nat 8%bv eq_refl)).
assert (S9 : getr rgT 9 = getr regs 9) by (rewrite T9; exact (EX 2%nat 9%bv eq_refl)).
assert (S18 : getr rgT 18 = getr regs 18) by (rewrite T18; exact (EX 3%nat 18%bv eq_refl)).
assert (S19 : getr rgT 19 = getr regs 19) by (rewrite T19; exact (EX 4%nat 19%bv eq_refl)).
assert (S20 : getr rgT 20 = getr regs 20) by (rewrite T20; exact (EX 5%nat 20%bv eq_refl)).
assert (R3T : getr rgT 3 = w64 (as_gp B)) by (rewrite T3, (EE 3%nat 3%bv eq_refl), X3; exact R3).
assert (R4T : getr rgT 4 = w64 (as_tp B)) by (rewrite T4, (EE 4%nat 4%bv eq_refl), X4; exact R4).
assert (R10T : getr rgT 10 = w64 (dpg_c R)) by (rewrite T10, (EE 8%nat 8%bv eq_refl), X8; exact R8).
assert (R11T : getr rgT 11 = w64 q) by (rewrite T11, (EE 10%nat 10%bv eq_refl); exact Hq10).
assert (RspT : spZ rgT = spZ regs).
{ unfold spZ at 1. rewrite T2, (EE 2%nat 2%bv eq_refl).
  change (bv_unsigned (getr regs3 2%bv)) with (spZ regs3). rewrite Hsp3, unsigned_lit_small by lia. lia. }
assert (HI : forall r, 21 <= r <= 27 -> getr rgT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (Rhi r Hr), <- (HP3 r ltac:(unfold acallee_saved; lia)).
  assert (Hc : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
  - rewrite (dpg8_z5 21%bv 21 eq_refl), T21. exact (EE 21%nat 21%bv eq_refl).
  - rewrite (dpg8_z5 22%bv 22 eq_refl), T22. exact (EE 22%nat 22%bv eq_refl).
  - rewrite (dpg8_z5 23%bv 23 eq_refl), T23. exact (EE 23%nat 23%bv eq_refl).
  - rewrite (dpg8_z5 24%bv 24 eq_refl), T24. exact (EE 24%nat 24%bv eq_refl).
  - rewrite (dpg8_z5 25%bv 25 eq_refl), T25. exact (EE 25%nat 25%bv eq_refl).
  - rewrite (dpg8_z5 26%bv 26 eq_refl), T26. exact (EE 26%nat 26%bv eq_refl).
  - rewrite (dpg8_z5 27%bv 27 eq_refl), T27. exact (EE 27%nat 27%bv eq_refl). }
assert (HPT : aregs_preserved regs rgT).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct (Z.le_gt_cases 21 r) as [H21 | H21]; [exact (HI r ltac:(lia))|].
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
  - rewrite (dpg8_z5 2%bv 2 eq_refl). apply bv_eq. change (spZ rgT = spZ regs). exact RspT.
  - rewrite (dpg8_z5 3%bv 3 eq_refl), R3T. symmetry. exact Hgp.
  - rewrite (dpg8_z5 4%bv 4 eq_refl), R4T. symmetry. exact Htp.
  - rewrite (dpg8_z5 8%bv 8 eq_refl). exact S8.
  - rewrite (dpg8_z5 9%bv 9 eq_refl). exact S9.
  - rewrite (dpg8_z5 18%bv 18 eq_refl). exact S18.
  - rewrite (dpg8_z5 19%bv 19 eq_refl). exact S19.
  - rewrite (dpg8_z5 20%bv 20 eq_refl). exact S20. }
assert (Hchg : false = negb (bv_unsigned (getr rgT 12) =? 0)) by (rewrite T12; reflexivity).
(* the epilogue wrote nothing *)
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ mem3) (mrestrict _ mT) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ (w_H W3) mem3 mT (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq' | Hin]; [injection Hq' as <- <- <-; cbn [base_val] in Hrr; lia|]);
          destruct Hin)) as UN
end.
assert (HKT : forall a, 0 <= a < 2 ^ 64 -> rdW W3 mT a = rdW W3 mem3 a) by (intros a Ha; exact (UN a Ha (fun z => z))).
(* the state the tail jump hands to answer *)
pose proof (proj1 HJ3) as HART.
pose proof HJ3 as (_ & HlyT & _ & _ & _ & HfrT & HnevT & _ & F1T & _).
pose proof HlyT as (_ & _ & _ & _ & _ & _ & _ & _ & EtopT & _).
assert (HRODT : arodata_okP SEGS RLO RHI B (rdW W3 mT))
  by exact (dpg_rodata_kept B cmd_ro_prog_apart _ _ ly S W mem md O [] ly2 S2 W3 mT mdT _ HAR0 HOin HJ3 HROD).
pose proof (cmd_ro_ok_of_aro ly2 S2 W3 mT mdT HART HRODT) as HROT.
assert (HFRT : Z.of_nat (length (frames S2)) <= 8) by (rewrite HfrT; exact Hfr8).
assert (HCH : achain ly2 (rdW W3 mT) (spZ regs + 0) (s0Z rgT) ch).
{ rewrite Z.add_0_r.
  assert (Es0 : s0Z rgT = s0Z regs) by (unfold s0Z; rewrite S8; reflexivity).
  rewrite Es0. apply (achain_ly_top ly ly2 _ _ _ _ EtopT).
  apply (achain_kept ly (rdW W mem) (rdW W3 mT) (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
  intros a Ha. apply F1T; [lia | lia |]. intros Hfp. pose proof (dpg8_FP_low ly S W mem md O HAR0 HOin a Hfp). lia. }
(* the recorder at the tail jump: rec_shape_of and the epilogue kept g_rec, record.spill and its blocks *)
assert (HO2bl : forall pn, In pn (lay_blocks Q2) -> In pn (ablocks B ly2 S2)) by exact (lay_blocks_in _ _ _ _ _ _ HREC2).
assert (HKR : rec_rd_kept Q2 (rdW W2 mem2) (rdW W3 mT) (fun _ => False)).
{ intros a Ha _.
  destruct Ha as [Ha | [Ha | ((pb & nb) & Hpn & Hr)]].
  - rewrite HKT by (unfold A_G_REC, REC_SIZE in Ha; lia).
    destruct (dpg_unowned B HB a ltac:(left; exact Ha)) as [Hown Herr].
    apply GX3; [apply cmd_prog_img, dpg_in_PG; left; exact Ha | exact Hown | exact Herr |
      apply fp_spares_closed; [exact sink_closed_nil | intros (r' & [] & _)]].
  - rewrite HKT by (unfold A_REC_SPILL, SC_SIZE in Ha; lia).
    destruct (dpg_unowned B HB a ltac:(right; left; exact Ha)) as [Hown Herr].
    apply GX3; [apply cmd_prog_img, dpg_in_PG; right; exact Ha | exact Hown | exact Herr |
      apply fp_spares_closed; [exact sink_closed_nil | intros (r' & [] & _)]].
  - cbn [fst snd] in Hr. pose proof (HO2bl _ Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HAR2 Hin) as (_ & H4096 & Hpc & _ & _ & _ & Hk0).
    pose proof (dpg_req_ge nb (proj1 Hk0)) as [_ Hreq].
    rewrite HKT by lia.
    replace a with (pb + (a - pb)) by lia.
    apply (GX2 pb nb (a - pb)); [exact Hin | exact Hin | lia | intros (r' & [] & _)]. }
assert (HAT : arep_at (ablocks B ly2 S2) (rdW W3 mT) A_G_REC A_REC_SPILL (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) Q2)
  by exact (arep_kept _ _ _ _ _ _ HREC2 HO2bl HKR).
assert (HREPT : rec_repA B ly2 S2 (rdW W3 mT) (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (lay_blocks Q2))
  by (exists Q2; split; [exact HAT | intros pn; apply iff_refl]).
(* the answer the recorder holds: 0 or the start of one of its blocks *)
assert (HOLD : exists old, aval_mem (rdW W3 mT) (A_G_REC + OFF_ANSWER) 8 old /\ 0 <= old < 2 ^ 64 /\
  (old = 0 \/ exists m, In (old, m) (lay_blocks Q2))).
{ pose proof (arep_answer_ptr _ _ _ _ HAT) as H.
  destruct (l_answer Q2) as [[a m]|] eqn:EA.
  - exists a. split; [exact H|].
    assert (Hin : In (a, m) (lay_blocks Q2))
      by (unfold lay_blocks; rewrite EA; cbn [oblk]; rewrite !in_app_iff; right; right; left; left; reflexivity).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ a m HART (HO2bl _ Hin)) as (_ & H4096 & Hpc & _ & _ & _ & Hk).
    pose proof (dpg_req_ge m (proj1 Hk)) as [Hr1 _].
    split; [lia|]. right. exists m. exact Hin.
  - exists 0. split; [exact H|]. split; [lia | left; reflexivity]. }
destruct HOLD as (old & Hold & Hold64 & Hold').
(* answer's other premises *)
assert (HSH : r_refuse (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) = 0 ->
  astr_argA B ly2 S2 (rdW W3 mT) (in_roP SEGS RLO RHI) (lay_blocks Q2) q (Some (shape_of dpg_verb)) /\
  fits (shape_of dpg_verb)).
{ intros _. split; [|exact dpg8_fits].
  apply (dpg8_argA_rd ly2 S2 (rdW W3 mem3) (rdW W3 mT) (lay_blocks Q2) q _ (HqA (lay_blocks Q2))).
  intros i Hi. apply HKT. exact (dpg8_argA_bound ly2 S2 W3 mT mdT _ [] q _ HART (proj1 Hq64) (HqA []) i Hi). }
assert (HSLOT : r_refuse (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) = 0 -> false = true ->
  (exists k, nth_error (r_calls (rec_record R REC_DESCRIPTORS_PANEL_GET [x])) k = Some (REC_DESCRIPTORS_PANEL_GET, [x]) /\
     dpg_c R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (dpg_c R = A_REC_SPILL /\ (REC_DESCRIPTORS_PANEL_GET, [x]) = r_spill (rec_record R REC_DESCRIPTORS_PANEL_GET [x])))
  by (intros _ Hf; discriminate Hf).
assert (HEVT : st_nev S2 + EV_ANSWER <= EV_MAX)
  by (unfold EV_DESCRIPTORS_PANEL_GET, EV_REC_SHAPE_OF in *; lia).
set (t := snd (rec_answer (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (REC_DESCRIPTORS_PANEL_GET, [x])
  (shape_of dpg_verb) false)).
assert (Ht : snd (descriptors_panel_get_m R (Some x)) = t) by (rewrite HM; reflexivity).
assert (HLIVET : blocks_bytes S2 + LIVE_ANSWER t <= LIVE_MAX).
{ unfold LIVE_DESCRIPTORS_PANEL_GET in Hlive. rewrite Ht in Hlive. cbn [sarg] in Hlive. lia. }
assert (HXa : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
assert (HMOKT : mo_ok MT S2 (XM_ANSWER MT t)).
{ apply (mok_station MT S S2 (XM_DESCRIPTORS_PANEL_GET MT R (Some x))
    (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x) (XM_ANSWER MT t) MTL MOK MLE2 HXa).
  unfold XM_DESCRIPTORS_PANEL_GET. rewrite Ht. cbn [sarg]. lia. }
(* ---------- the tail jump: answer runs at the entry's sp and returns to the entry's caller ---------- *)
rewrite dpg8_sig_ans.
eapply SRr_mono.
{ eapply (cl_callS_wideF B LAWS W3 rgT mT _ DPG_STK (spZ regs) (dpg_FP O) ly S W mem md [] ly2 S2 mdT
    (rec_spill_frees R + EV_XSTRDUP + EV_REC_SHAPE_OF) ANSWER_STK
    ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
     ablocks_fp (filter (fun pn => fst pn =? old) (lay_blocks Q2)))
    EV_ANSWER 0 (getr rgT 1) ch _ HJ3).
  - rewrite RspT. lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - exact R3T.
  - exact R4T.
  - reflexivity.
  - rewrite S1. exact Hra.
  - rewrite S1. exact Hra4.
  - exact HCH.
  - intros HPRE3. eapply SRr_mono.
    + exact (TANSWER fx ly2 S2 W3 rgT mT mdT ch (dpg_c R) q old (REC_DESCRIPTORS_PANEL_GET, [x]) (shape_of dpg_verb) false
        (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (lay_blocks Q2)
        HPRE3 HFRM HFRT HRODT HROT R10T Hc64 R11T Hq64 Hchg HREPT Hold Hold64 HSH HSLOT HEVT HLIVET HMOKT).
    + cbv beta. intros Wx cx _ (fxx & lyx & Sx & regsx & memx & mdx & -> & Hf1 & Hf2 & HJx & HPx & HKx).
      exists fxx, lyx, Sx, regsx, memx, mdx. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
      split; [exact HJx|]. split; [exact HPx | exact HKx].
  - (* every byte answer writes is one this call may write *)
    intros a Hfp. apply inFP_cons in Hfp as [Ha | Hfp]; [|apply inFP_cons in Hfp as [Ha | Hfp]].
    + apply (dpg_awr_slot B HB cmd_prog_img). left. unfold A_G_REC, OFF_ANSWER, REC_SIZE in *. lia.
    + apply (dpg_awr_slot B HB cmd_prog_img). left. unfold A_G_REC, OFF_STATE, REC_SIZE in *. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (pb & nb & Hin & Hr).
      apply dpg8_filter_in in Hin.
      pose proof (HO2bl _ Hin) as HinT.
      destruct (in_dec dpg_pdec (pb, nb) O) as [HO | HnO].
      * right; left. split; [|exists pb, nb; split; [exact HinT | exact Hr]].
        replace a with (pb + (a - pb)) by lia.
        destruct (inFP_ablocks_fp O pb nb (a - pb) HO ltac:(lia)) as (r & Hr' & Ha').
        exists r. split; [right; right; exact Hr' | exact Ha'].
      * right; right; left. exists pb, nb. split; [exact HinT|]. split; [|exact Hr].
        intros H0. destruct (proj1 (HQ2 (pb, nb)) Hin) as [H1 | H1].
        -- exact (HnO (BO1 _ H1)).
        -- assert (Hnc : ~ In (pb, nb) (ablocks B lyc Sc)).
           { rewrite H1. intros Hc. rewrite Forall_forall in Hap2. specialize (Hap2 _ Hc). cbn [fst snd] in Hap2.
             unfold iv_apart, LIVE_XSTRDUP in Hap2. lia. }
           exact (HnO (proj1 (Bgone _ H0 Hnc))).
  - (* no byte of answer's footprint is in this call's stack window *)
    intros ly5 S5 W5 regs5 mem5 md5 _ a Hfp Hw _. exfalso.
    apply inFP_cons in Hfp as [Ha | Hfp]; [|apply inFP_cons in Hfp as [Ha | Hfp]].
    + unfold A_G_REC, OFF_ANSWER in Ha. lia.
    + unfold A_G_REC, OFF_STATE in Ha. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (pb & nb & Hin & Hr).
      apply dpg8_filter_in in Hin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HART (HO2bl _ Hin)) as (_ & _ & Hbc & _). lia. }
(* ---------- answer's post is the contract's post ---------- *)
cbv beta. intros W5 c5 _ (fx1 & ly5 & S5 & regs5 & mem5 & md5 & Hfx & -> & HJ5 & HJc5 & HP5 & HK5).
destruct HK5 as (p1 & p2 & O' & HK5). cbv zeta in HK5.
destruct HK5 as (Hp2r & Hp24096 & H12 & Hfr12 & Hbl5 & HREP5 & HO'iff & Hstr5 & Hbb5 & HMLE5).
pose proof (proj1 HJ5) as HAR5.
unfold dpg_post. rewrite S1.
apply (apost_baseF_intro (fx := fx) SEGS fx1 B DPG_STK (dpg_FP O) regs ly S W mem md _ _ W5 ly5 S5 regs5 mem5 md5).
{ exact Hfx. }
{ eapply (ajournal_mono_k SEGS B); [exact HJ5|]. unfold EV_DESCRIPTORS_PANEL_GET, EV_REC_SHAPE_OF. lia. }
{ exact (aregs_preserved_trans _ _ _ HPT HP5). }
apply (dpg_post_of B MT ly S R (Some x) O lyc Sc O1 ly2 S2 ly2 S2 W3 mT mdT ly5 S5 W5 regs5 mem5 md5 x p p1 p2 old
  (lay_blocks Q2) O'
  (fst (rec_answer (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) (REC_DESCRIPTORS_PANEL_GET, [x]) (shape_of dpg_verb) false))
  t BLK HPerm2 Hap2 (Permutation_refl _) HART HAR5 HQ2 HO2bl Hold' Hp24096 H12 Hfr12 Hbl5 HREP5 HO'iff Hstr5 Hp2r).
- rewrite HM. apply surjective_pairing.
- unfold t in *. unfold LIVE_DESCRIPTORS_PANEL_GET. rewrite Ht. cbn [sarg]. lia.
- unfold t in *. apply (mle_weaken MT S S5 _ _ MTL (mle_station MT S S2 S5 _ _ MTL MLE2 HMLE5)).
  unfold XM_DESCRIPTORS_PANEL_GET. rewrite Ht. cbn [sarg]. lia.
Qed.

End e.
End f.
End d.
