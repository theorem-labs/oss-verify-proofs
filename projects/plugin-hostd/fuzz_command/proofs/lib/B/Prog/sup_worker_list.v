(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_worker_list on plugin-hostd/fuzz_command.asan-ubsan (image B),
   re-walked at B's addresses after the ASan walk lib/A/Prog/sup_worker_list.v (a working branch
   80a82462f87), over a Theorem Labs lane's statements (lib/B/Prog/sup_worker_list_c.v, a Theorem Labs lane f490061c104), a Theorem Labs lane's record facts
   (lib/B/Prog/CmdRecRo.v, CmdRecRest.v) and FP-post kit (lib/B/Prog/PaFx.v). *)

(* sup_worker_list (recorder.c:390-393, B entry 0x8bb2c, 17 instructions, one segment, no branch):
   the frame (ra, s0), record(8) (a call on B; A inlined it), rec_shape_of(0x21dc0 "worker_list", 11), the epilogue
   and the tail jump answer(slot, shape, 0) at the entry's sp. No `jal __asan_report_*` and no UBSan trap site
   (capstone over fuzz_command.asan-ubsan's .symtab, a Theorem Labs lane's gen/funcs.tsv and gen/traps.B.summary), so the walk
   has no report or trap edge to refute. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c record_c rec_shape_of_c xmalloc_c hand_back_c answer_c sup_worker_list_c sup_worker_list_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecRo CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* after a symbolic run the model term grows (a Theorem Labs lane, 2026-10-28): name it *)
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
(* the statement's Section hypotheses (sup_worker_list_c.v), word for word *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs (PI := PI).
(* the walk's record facts, in a Theorem Labs lane's forms (713692f1e0c lib/B/Prog/CmdRec*.v): the allocator record and the meter's
   laws; the call targets and the image facts, each as the statement of a Theorem Labs lane's lemma of that name with this walk's
   abstract PI / segments in place of the pinned image PB_cmd / tfibsegs (CmdRecRest.v cmd_sig_prog_PB, CmdRecImg.v
   cmd_img_facts_tfib), so the file that pins the image discharges each by exact; every per-binary fact the walk uses
   is a Theorem Labs lane's lemma over them, by exact (CmdRecRo.v ROB, RELRO_IMG, CMD_RO_IN, cmd_ro_ok_of_aro; CmdRecRest.v
   cmd_ro_prog_apart, cmd_prog_img) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog (PI := PI).
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let swl_ROB : ro_below_ofl SEGS RLO RHI := CmdRecRo.ROB (SK := SK) SEGS B LAWS HB IMG.
Let swl_relro : forall a, RLO <= a < RHI -> in_img SEGS a := CmdRecRo.RELRO_IMG (SK := SK) SEGS B LAWS HB IMG.
Let swl_ro_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let swl_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let swl_ro_ok : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let swl_ro_in : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI) := CmdRecRo.CMD_RO_IN (SK := SK) SEGS B LAWS HB IMG.

(* the read-only bytes keep the image's values along the walk: none is in the statement's footprint *)
Lemma swl_rodata_at : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k R O,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (swl_FP O) ly S W mem md own ly' S' W' mem' md' k ->
rec_repA B ly S (rdW W mem) R O ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k R O HAR HJ HREP HR.
apply (arodata_ok_journalP SEGS RLO RHI swl_relro (RO := swl_ROB) B STK sp0 (swl_FP O) ly S W mem md own ly' S' W' mem' md' k HJ); [|exact HR].
intros a Hro HF. destruct (swl_ro_apart a Hro) as [Himg Hnpg].
unfold swl_FP in HF. apply inFP_cons in HF as [Ha | HF]; [exact (Hnpg (swl_grec_in a Ha))|].
apply inFP_cons in HF as [Ha | HF]; [exact (Hnpg (swl_spill_in a Ha))|].
destruct (inFP_ablocks_fp_inv O a HF) as (p & n & Hpn & Hr).
pose proof (swl_rec_repA_in B ly S _ R O HREP (p, n) Hpn) as Hin.
destruct (al_client_img _ _ LAWS ly S W mem md a HAR) as [_ Hni].
{ left. exists p, n. split; [exact Hin | exact Hr]. }
exact (Hni Himg).
Qed.

(* a byte of g_rec or record.spill is a byte the walk may write: awr_byte's program-static disjunct *)
Lemma swl_awr_pg : forall STK sp0 O bl0 blc fr0 ly own a,
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
awr_byte SEGS B STK sp0 (swl_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Ha.
assert (HPG : Exists (in_zr a) TFIB_PROG_STATIC) by (destruct Ha as [Ha | Ha]; [apply swl_grec_in | apply swl_spill_in]; exact Ha).
right; right; right; right; left.
split; [|split; [rewrite (swl_prog_static B HB); exact HPG | exact (swl_prog_img a HPG)]].
unfold swl_FP. apply inFP_cons. destruct Ha as [Ha | Ha]; [left; exact Ha|]. right. apply inFP_cons. left. exact Ha.
Qed.

(* a string argument lies below the allocator's ceiling: a heap block, or read-only image bytes *)
Lemma swl_arg_low : forall ly S (W : world SEGS) mem md (rd : reader) O p x, AR SEGS B ly S W mem md ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
forall i, 0 <= i < Z.of_nat (length x) + 1 -> p + i < alloc_ceiling.
Proof.
intros ly S W mem md rd O p x HAR H i Hi. pose proof asan_consts as (C1 & _).
cbv beta iota zeta delta [astr_argA] in H. destruct H as (_ & _ & _ & [((b & k & Hin & Hb & Hk) & _) | (HRO & _)]).
- destruct (swl_blk_byte B ly S W mem md b k (p + i - b) HAR Hin ltac:(lia)) as (_ & Hc & _).
  replace (b + (p + i - b)) with (p + i) in Hc by lia. exact Hc.
- destruct (HRO i Hi) as (Hro & _). destruct (swl_ro_apart _ Hro) as (Himg & _).
  pose proof (pa_img_range _ Himg). lia.
Qed.

(* ---------- the walk ---------- *)
Theorem tsup_worker_list_holds : tsup_worker_list_spec (PI := PI) B MT.
Proof.
unfold tsup_worker_list_spec.
intros ly S W regs mem md ch R O HPRE HFRM HROD HRO HREP Hfr8 Hev Hlive MOK.
change ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O) with (swl_FP O).
pose proof (pa_wx (PAImg := PI)) as Hwx. pose proof (pa_segs_low (PAImg := PI)) as Hsegs. pose proof (pa_B_ok (PAImg := PI)) as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
let v := eval vm_compute in SUP_WORKER_LIST_STK in assert (FS : SUP_WORKER_LIST_STK = v) by (vm_compute; reflexivity).
let v := eval vm_compute in RECORD_STK in assert (RS : RECORD_STK = v) by (vm_compute; reflexivity).
let v := eval vm_compute in REC_SHAPE_OF_STK in assert (SS : REC_SHAPE_OF_STK = v) by (vm_compute; reflexivity).
let v := eval vm_compute in ANSWER_STK in assert (AS : ANSWER_STK = v) by (vm_compute; reflexivity).
let v := eval vm_compute in EV_ANSWER in assert (EVA : EV_ANSWER = v) by (vm_compute; reflexivity).
assert (EVS : EV_REC_SHAPE_OF = 0) by reflexivity.
set (sp0 := spZ regs) in *.
pose proof HREP as (Q & HA & HO).
pose proof HA as (_ & _ & _ & (HC1 & _) & _).
set (n := length (r_calls R)) in *.
assert (Hslot : A_G_REC + OFF_CALLS <= rec_slot R <= A_REC_SPILL) by exact (swl_slot_range R HC1).
(* the budgets *)
assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (RSF0 : 0 <= rec_spill_frees R) by (unfold rec_spill_frees; destruct (Nat.ltb _ _); lia).
assert (XR0 : 0 <= XM_RECORD MT R) by (unfold XM_RECORD; pose proof (mo_free_nonneg MT MTL); nia).
unfold EV_SUP_WORKER_LIST, EV_RECORD in Hev. unfold LIVE_SUP_WORKER_LIST in Hlive. unfold XM_SUP_WORKER_LIST in MOK.
rewrite swl_model in Hlive, MOK.
set (R2 := rec_record R REC_WORKER_LIST []) in *.
set (x := shape_of swl_verb) in *.
set (e := (REC_WORKER_LIST, @nil (list byte))) in *.
set (t := snd (rec_answer R2 e x false)) in *.
(* the seed *)
destruct (swl_seed SUP_WORKER_LIST_STK ly W mem regs ltac:(rewrite FS; unfold SWL_FRAME; lia) Hstk Hpres0) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_WORKER_LIST_STK (swl_FP O) ly S W regs mem md ch HPRE) as HJ.
set (E := swl_E regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold swl_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
pose proof (swl_FP_low B ly S W mem md _ R O HAR0 HREP) as HFPlow.
unfold cfg_at, w64.
(* 0x8bb2c .. 0x8bb3c: the frame (ra at sp0 - 8, s0 at sp0 - 16), a0 = 8, then the call of record *)
paj_run_tok RUN HS HJ SHOK swl_Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
pmkst HS. try swl_md.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
(* the run writes only the frame *)
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 16 <= a < sp0) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H1.
  apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms) (fun a => sp0 - 16 <= a < sp0) HFr); [|exact Ha | exact H1].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]).
  destruct Hin. }
rename ms into ms0, mat into mat0, HF into HF0, HFr into HFr0, HG into HG0.
assert (HspT : spZ (ms_regs ms0) = sp0 + -16) by (unfold spZ at 1; rewrite P2, Usp, unsigned_lit_small by lia; lia).
assert (P3' : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (P4' : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (P10' : getr (ms_regs ms0) 10 = w64 REC_WORKER_LIST) by (rewrite P10; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms0) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms0) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
(* record's frame chain: afn_pre's chain, kept by the prologue's writes below sp0 and lowered to record's sp (s0 is
   still the caller's) *)
assert (Hch1 : achain ly (rdW W (ms_mem ms0)) (sp0 + -16) (s0Z (ms_regs ms0)) ch).
{ apply (achain_lower ly _ sp0); [|lia]. unfold s0Z. rewrite P8, (EEo 8%nat 8%bv eq_refl). fold (s0Z regs).
  apply (achain_kept ly (rdW W mem) _ sp0 _ ch sp0 Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply KEEP0; lia. }
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms0))) by exact (swl_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HJ HREP HROD).
assert (HREPc : rec_repA B ly S (rdW W (ms_mem ms0)) R O).
{ apply (swl_rec_repA_kept B ly S (rdW W mem) ly S _ R O HREP).
  - exact (swl_rec_repA_in B ly S _ R O HREP).
  - intros a Ha. apply KEEP0; unfold A_G_REC, REC_SIZE in *; lia.
  - intros a Ha. apply KEEP0; unfold A_REC_SPILL, SC_SIZE in *; lia.
  - intros p m i Hpn Hi.
    destruct (swl_blk_byte B ly S W mem md p m i HAR0 (swl_rec_repA_in B ly S _ R O HREP (p, m) Hpn) Hi) as (B1 & B2 & _).
    apply KEEP0; lia. }
assert (HEc : st_nev S + EV_RECORD R <= EV_MAX) by (unfold EV_RECORD; lia).
assert (HMOKc : mo_ok MT S (XM_RECORD MT R)).
{ apply (mo_ok_le MT MTL S _ _ MOK). pose proof (XN0 t). lia. }
(* the footprint record() writes: g_rec.ncalls, the slot's fn and nargs, and on the spill arm the spill's old
   argument blocks, all below the allocator's ceiling *)
assert (HFP1 : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
    (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a ->
    (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
    (exists b m, In (b, m) O /\ b <= a < b + req_size m)).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [left; unfold A_G_REC, OFF_NCALLS, REC_SIZE in *; lia|].
  apply inFP_cons in Ha as [Ha | Ha].
  - destruct (swl_slot_bytes R HC1 a Ha) as [H | H]; [left; exact H | right; left; exact H].
  - right; right. destruct (Nat.ltb _ _) in Ha; [exfalso; exact (inFP_nil a Ha)|].
    destruct (inFP_ablocks_fp_inv O a Ha) as (b & m & Hbm & Hba). exists b, m. split; [exact Hbm | exact Hba]. }
assert (HFP1s : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
    (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> a < alloc_ceiling).
{ intros a Ha. destruct (HFP1 a Ha) as [H | [H | (b & m & Hbm & Hba)]];
  [unfold A_G_REC, REC_SIZE in H; lia | unfold A_REC_SPILL, SC_SIZE in H; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 (swl_rec_repA_in B ly S _ R O HREP (b, m) Hbm)) as (_ & _ & Hbc & _). lia. }
(* 0x8bb3c: record(8) *)
rewrite (swl_sig_rec cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms0) (ms_mem ms0) _ SUP_WORKER_LIST_STK sp0 (swl_FP O) ly S W mem md [] ly S _ 0
    RECORD_STK _ (EV_RECORD R) (-16) (getr (ms_regs ms0) 1) ch _ HJ HspT eq_refl ltac:(lia)
    ltac:(rewrite RS; lia) ltac:(rewrite RS, FS; lia) P3' P4' eq_refl HraT Hra4T Hch1).
  - intros HPRE1. exact (TRECORD fx ly S W (ms_regs ms0) (ms_mem ms0) _ ch REC_WORKER_LIST R O HPRE1 HRODc P10'
      ltac:(unfold REC_WORKER_LIST, REC_FN_COUNT; lia) HREPc HEc HMOKc).
  - intros a Ha. destruct (HFP1 a Ha) as [H | [H | (b & m & Hbm & Hba)]].
    + exact (swl_awr_pg _ _ O _ _ _ _ _ a (or_introl H)).
    + exact (swl_awr_pg _ _ O _ _ _ _ _ a (or_intror H)).
    + right; left. split.
      * unfold swl_FP. apply inFP_cons. right. apply inFP_cons. right.
        replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b m (a - b)); [exact Hbm | lia].
      * exists b, m. split; [exact (swl_rec_repA_in B ly S _ R O HREP (b, m) Hbm) | exact Hba].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. pose proof (HFP1s a Ha). rewrite FS in Hw. lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & HK2).
destruct HK2 as (F & O1 & Ha0 & HPermF & HlenF & HFO & HREP2 & HO1 & Hbb2 & MLE2).
rewrite P1.
(* back at 0x8bb40: the frame is kept, the rest of the state is record's *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc2 | exact HJ2 | exact Usp | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a Ha HFa. pose proof (HFP1s a HFa). cbn in Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall m, (m < 40)%nat -> ew E3 m = ew E m) by (intros m Hm; rewrite HE3; apply YN3v.ew_havoc_old; exact Hm).
assert (A44 : ew E3 44 = getr regs2 10) by (rewrite HE3; reflexivity).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : sh_ok SEGS swl_Bx swl_SH E3 (mrestrict (w_H W2) mem2)) by (unfold sh_ok, swl_SH; apply Forall_nil).
(* 0x8bb40 .. 0x8bb50: s0 = the slot, a0 = 0x21dc0, a1 = 11, then the call of rec_shape_of *)
paj_run_tok RUN HS HJ2 SHOK3 swl_Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp3 | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
pmkst HS. try swl_md.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 16 <= a < sp0) -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a).
{ intros a Ha H1.
  apply (kept_of_frame (segs := SEGS) E3 _ (w_H W2) mem2 (ms_mem ms) (fun a => sp0 - 16 <= a < sp0) HFr); [|exact Ha | exact H1].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3 in Hrr; lia|]).
  destruct Hin. }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pose proof (proj1 HJ2) as HAR2.
assert (HspT2 : spZ (ms_regs ms1) = sp0 + -16) by (unfold spZ at 1; rewrite Q2, Usp3, unsigned_lit_small by lia; lia).
assert (Q3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite Q3, OLD3, (EEo 3%nat 3%bv eq_refl) by lia; exact Hgp).
assert (Q4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite Q4, OLD3, (EEo 4%nat 4%bv eq_refl) by lia; exact Htp).
assert (Q10' : getr (ms_regs ms1) 10 = w64 0x21dc0).
{ rewrite Q10. apply bv_eq. change 307%nat with (A_OBJ 66).
  rewrite (HEI3 (A_OBJ 66) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), (swl_lit_val VOBJS). cbv [w64]. reflexivity. }
assert (Q11' : getr (ms_regs ms1) 11 = w64 (Z.of_nat (length swl_verb))) by (rewrite Q11; reflexivity).
assert (HraT2 : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T2 : 4096 <= bv_unsigned (getr (ms_regs ms1) 1)) by (rewrite Q1, unsigned_lit_small by lia; lia).
assert (HROD2 : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms1))) by exact (swl_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HJ2 HREP HROD).
assert (HRO2 : cmd_ro_ok (rdW W2 (ms_mem ms1))) by exact (swl_ro_ok _ _ _ _ _ HAR2 HROD2).
assert (HVERB := swl_verb_pre B HB ly2 S2 (rdW W2 (ms_mem ms1)) HRO2 swl_ro_in).
pose proof HJ2 as (_ & _ & _ & _ & _ & HfrS2 & HnevS2 & _).
assert (HEV3 : st_nev S2 + EV_REC_SHAPE_OF <= EV_MAX) by (rewrite EVS; unfold EV_RECORD in HnevS2; lia).
(* 0x8bb50: rec_shape_of(0x21dc0, 11) *)
rewrite (swl_sig_shp cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W2 (ms_regs ms1) (ms_mem ms1) _ SUP_WORKER_LIST_STK sp0 (swl_FP O) ly S W mem md [] ly2 S2 _
    _ REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-16) (getr (ms_regs ms1) 1) _ HJ2 HspT2 eq_refl ltac:(lia)
    ltac:(rewrite SS; lia) ltac:(rewrite SS, FS; lia) Q3' Q4' eq_refl HraT2 Hra4T2).
  - intros HPRE3. exact (TREC_SHAPE_OF fx ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ 0x21dc0 swl_verb HPRE3 HROD2 Q10' ltac:(lia)
      Q11' ltac:(rewrite swl_verb_len; lia) HRO2 VOBJS HVERB HEV3).
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as ((q & Hq10 & Hq0 & HqARG) & HPerm3 & -> & ->).
rewrite Q1.
(* back at 0x8bb54: the frame is kept; the band of the new atoms starts above atom 44, the slot in s0 *)
jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B);
  [exact HJc3 | exact HJ3 | exact Usp3 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
  intros a Ha HFa. exact (inFP_nil a HFa). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E3 64 (map (getr regs3) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall m, (m < 64)%nat -> ew E4 m = ew E3 m) by (intros m Hm; rewrite HE4; apply YN3v.ew_havoc_old; exact Hm).
assert (A68 : ew E4 68 = getr regs3 10) by (rewrite HE4; reflexivity).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by lia; exact Usp3).
assert (SHOK4 : sh_ok SEGS swl_Bx swl_SH E4 (mrestrict (w_H W3) mem3)) by (unfold sh_ok, swl_SH; apply Forall_nil).
(* 0x8bb54 .. 0x8bb6c: a1 = the shape, a0 = the slot, a2 = 0, ra and s0 back from the frame, sp back, then the tail
   jump to answer *)
paj_run_tok RUN HS HJ3 SHOK4 swl_Bspan.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  eapply (awr_ok_cons_stack SEGS B) with (n := 2%nat); [reflexivity | exact Usp4 | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
pmkst HS. try swl_md.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12.
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 16 <= a < sp0) -> rdW W3 (ms_mem ms) a = rdW W3 mem3 a).
{ intros a Ha H1.
  apply (kept_of_frame (segs := SEGS) E4 _ (w_H W3) mem3 (ms_mem ms) (fun a => sp0 - 16 <= a < sp0) HFr); [|exact Ha | exact H1].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp4 in Hrr; lia|]).
  destruct Hin. }
(* the registers at answer's entry: the entry's ra, sp, gp, tp, s0, s1 .. s11; a0 = the slot, a1 = the shape, a2 = 0 *)
assert (T1' : getr (ms_regs ms) 1 = getr regs 1) by (rewrite T1, OLD4, OLD3, (EEo 1%nat 1%bv eq_refl) by lia; reflexivity).
assert (T2' : getr (ms_regs ms) 2 = getr regs 2).
{ rewrite T2, OLD4, OLD3 by lia. rewrite (EEo 2%nat 2%bv eq_refl). first [reflexivity | rewrite ?Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | rewrite Usp; unfold sp0, spZ; rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned]. }
assert (T3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite T3, OLD4, OLD3, (EEo 3%nat 3%bv eq_refl) by lia; exact Hgp).
assert (T4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite T4, OLD4, OLD3, (EEo 4%nat 4%bv eq_refl) by lia; exact Htp).
assert (T8' : getr (ms_regs ms) 8 = getr regs 8) by (rewrite T8, OLD4, OLD3, (EEo 8%nat 8%bv eq_refl) by lia; reflexivity).
assert (T9' : getr (ms_regs ms) 9 = getr regs 9) by (rewrite T9, OLD4, OLD3, (EEo 9%nat 9%bv eq_refl) by lia; reflexivity).
assert (T10' : getr (ms_regs ms) 10 = w64 (rec_slot R)) by (rewrite T10, OLD4, A44 by lia; exact Ha0).
assert (T11' : getr (ms_regs ms) 11 = w64 q) by (rewrite T11, A68; exact Hq10).
assert (Thi : forall r, 18 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hc10 : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc10 as [-> | Hc10]); [..| subst r];
  rewrite (st_ok_restrict_reg SEGS (w_H W3) E4 _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => rewrite OLD4, OLD3 by lia; exact (EEo m (Z_to_bv 5 rr) eq_refl) end. }
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
(* the recorder at answer's entry: record()'s post, kept by the run, rec_shape_of (no footprint) and the epilogue *)
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK3 & HIMG3 & _).
pose proof (proj1 HJ3) as HAR3.
assert (HrdG : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  rdW W3 (ms_mem ms) a = rdW W2 mem2 a).
{ intros a Ha.
  assert (HPG : Exists (in_zr a) TFIB_PROG_STATIC) by (destruct Ha as [Ha | Ha]; [apply swl_grec_in | apply swl_spill_in]; exact Ha).
  destruct (RecBLemmas.recb_prog_unowned_m (PI := PI) B HB swl_prog_img a HPG) as (Hi & Ho & He).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia).
  assert (Hns : ~ (sp0 - 16 <= a < sp0)) by (unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha; lia).
  rewrite (KEEP3 a Ha64 Hns).
  rewrite (HIMG3 a Hi Ho He (fp_spares_closed [] a (sink_closed_pos [] (Forall_nil _)) (inFP_nil a))).
  exact (KEEP2 a Ha64 Hns). }
assert (HO1bl : forall pn, In pn O1 -> In pn (ablocks B ly2 S2)) by exact (swl_rec_repA_in B ly2 S2 _ R2 O1 HREP2).
assert (HrdB : forall p m i, In (p, m) O1 -> 0 <= i < m -> rdW W3 (ms_mem ms) (p + i) = rdW W2 mem2 (p + i)).
{ intros p m i Hpn Hi.
  pose proof (HO1bl _ Hpn) as Hc0.
  destruct (swl_blk_byte B ly2 S2 W2 _ _ p m i HAR2 Hc0 Hi) as (B1 & B2 & _).
  pose proof (Permutation_in _ (Permutation_sym HPerm3) Hc0) as Hc3.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR2 Hc0) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
  assert (Ha64 : 0 <= p + i < 2 ^ 64) by lia.
  assert (Hns : ~ (sp0 - 16 <= p + i < sp0)) by lia.
  rewrite (KEEP3 (p + i) Ha64 Hns).
  rewrite (HBLK3 p m i Hc0 Hc3 ltac:(lia) (inFP_nil _)).
  exact (KEEP2 (p + i) Ha64 Hns). }
assert (HREP3 : rec_repA B ly2 S2 (rdW W3 (ms_mem ms)) R2 O1).
{ apply (swl_rec_repA_kept B ly2 S2 (rdW W2 mem2) ly2 S2 _ R2 O1 HREP2 HO1bl).
  - intros a Ha. exact (HrdG a (or_introl Ha)).
  - intros a Ha. exact (HrdG a (or_intror Ha)).
  - exact HrdB. }
pose proof HREP3 as (QA & HA3 & HO3).
pose proof HA3 as (_ & _ & _ & _ & Hans3 & _).
pose proof (swl_aanswer_ptr _ _ _ _ _ Hans3) as HOLD3.
set (old := swl_oaddr (l_answer QA)) in *.
assert (Hold_cases : old = 0 \/ (exists a0, old = fst a0 /\ In a0 O1)).
{ unfold old. destruct (l_answer QA) as [a0|] eqn:Ea; [right | left; reflexivity].
  exists a0. split; [reflexivity | apply HO3; exact (swl_lay_in_answer QA a0 Ea)]. }
assert (Hold64 : 0 <= old < 2 ^ 64).
{ destruct Hold_cases as [Ho | ([b m] & Ho & Hin0)]; [lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 (HO1bl _ Hin0)) as (_ & Hb4 & Hbc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)). cbn [fst] in Ho. lia. }
(* the shape rec_shape_of returned, as answer asks it *)
assert (HqARG4 : astr_argA B ly2 S2 (rdW W3 (ms_mem ms)) (in_roP SEGS RLO RHI) O1 q (Some x)).
{ apply (swl_astr_argA_rd B _ _ (rdW W3 mem3)); [exact (HqARG O1)|].
  intros i Hi. pose proof (swl_arg_low ly2 S2 W3 mem3 md3 _ O1 q x (proj1 HJc3) (HqARG O1) i Hi). apply KEEP3; lia. }
(* the budgets at answer's entry *)
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & HfrS3 & HnevS3 & _ & HHI3 & _).
assert (MLEa : mo_le MT S S2 (XM_RECORD MT R + 0)) by (rewrite Z.add_0_r; exact MLE2).
assert (HMOK4 : mo_ok MT S2 (XM_ANSWER MT t)) by (apply (mok_station MT S S2 _ _ _ MTL MOK MLEa (XN0 _)); lia).
assert (HEV4 : st_nev S2 + EV_ANSWER <= EV_MAX) by (rewrite EVS in HnevS3; unfold EV_RECORD in HnevS3; lia).
assert (HLIVE4 : blocks_bytes S2 + LIVE_ANSWER t <= LIVE_MAX) by lia.
assert (HROD4 : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem ms))) by exact (swl_rodata_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HJ3 HREP HROD).
assert (HRO4 : cmd_ro_ok (rdW W3 (ms_mem ms))) by exact (swl_ro_ok _ _ _ _ _ HAR3 HROD4).
assert (HspT4 : spZ (ms_regs ms) = sp0 + 0) by (unfold spZ at 1; rewrite T2'; unfold sp0, spZ; lia).
assert (HraT4 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite T1'; exact Hra).
assert (Hra4T4 : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite T1'; exact Hra4).
assert (Etop3 : ly_top ly2 = ly_top ly) by (destruct HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _); exact Etop3).
(* answer's frame chain: afn_pre's chain (s0 and sp are the entry's again), kept by the journal above sp0 *)
assert (HchT : achain ly2 (rdW W3 (ms_mem ms)) (sp0 + 0) (s0Z (ms_regs ms)) ch).
{ rewrite Z.add_0_r. unfold s0Z. rewrite T8'. fold (s0Z regs). apply (achain_ly_top ly ly2 _ _ _ _ Etop3).
  apply (achain_kept ly (rdW W mem) _ sp0 _ ch sp0 Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply HHI3; [lia | lia |].
  intros HFa. pose proof (HFPlow a HFa). lia. }
assert (Hc64 : 0 <= rec_slot R < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in Hslot; lia).
(* 0x8bb6c: the tail jump to answer(slot, shape, 0), at this function's entry sp *)
rewrite (swl_sig_ans cmd_sig_prog_PB).
eapply SRr_mono.
{ eapply (callS_wideF B LAWS W3 (ms_regs ms) (ms_mem ms) _ SUP_WORKER_LIST_STK sp0 (swl_FP O) ly S W mem md [] ly2 S2 _
    _ ANSWER_STK _ EV_ANSWER 0 (getr (ms_regs ms) 1) ch _ HJ3 HspT4 eq_refl ltac:(lia)
    ltac:(rewrite AS; lia) ltac:(rewrite AS, FS; lia) T3' T4' eq_refl HraT4 Hra4T4 HchT).
  - intros HPRE4. exact (TANSWER fx ly2 S2 W3 (ms_regs ms) (ms_mem ms) _ ch (rec_slot R) q old e x false R2 O1 HPRE4 HFRM
      ltac:(rewrite HfrS3; exact Hfr8) HROD4 HRO4 T10' Hc64 T11' Hq0 ltac:(rewrite T12; reflexivity) HREP3 HOLD3 Hold64
      (fun _ => conj HqARG4 swl_fits) (fun _ Hf => ltac:(discriminate Hf)) HEV4 HLIVE4 HMOK4).
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
    { apply (swl_awr_pg _ _ O _ _ _ _ _ a). left. unfold OFF_ANSWER, REC_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (swl_awr_pg _ _ O _ _ _ _ _ a). left. unfold OFF_STATE, REC_SIZE in *. lia. }
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba).
    apply swl_in_filter_old in Hbm as [Hbm Hbo]. cbn [fst] in Hbo.
    assert (HbO : In (b, m) O) by exact (proj1 (proj1 (HO1 _) Hbm)).
    right; left. split.
    + unfold swl_FP. apply inFP_cons. right. apply inFP_cons. right.
      replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b m (a - b)); [exact HbO | lia].
    + exists b, m. split; [exact (HO1bl _ Hbm) | exact Hba].
  - intros ly5 S5 W5 regs5 mem5 md5 _ a Ha Hw _. exfalso. rewrite FS in Hw.
    apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_ANSWER in Ha; lia|].
    apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, OFF_STATE in Ha; lia|].
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba). apply swl_in_filter_old in Hbm as [Hbm _].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 (HO1bl _ Hbm)) as (_ & _ & Hbc & _). lia. }
cbv beta. intros W5 c5 Hwle5 (fx5 & ly5 & S5 & regs5 & mem5 & md5 & -> & HFX5 & HCSR5 & HJ5 & HJc5 & HP5 & HK5).
cbv zeta in HK5. change (snd (rec_answer R2 e x false)) with t in HK5.
destruct HK5 as (p1 & p2 & O' & H10' & Hp2 & Hp12 & Hfresh & Hbl5 & HREP5 & HO' & HS5 & BB5 & MLE5).
pose proof (proj1 HJ5) as HAR5.
(* the blocks record() freed are F: the others stay live *)
pose proof (RecBLemmas.recb_ablocks_nodup_m (PI := PI) B ly S W mem md HAR0) as NDS.
pose proof (Permutation_NoDup HPermF NDS) as ND2.
assert (JB1 : forall pn, In pn (ablocks B ly2 S2) <-> In pn (ablocks B ly S) /\ ~ In pn F).
{ intros pn. split.
  - intros H. split; [apply (Permutation_in _ (Permutation_sym HPermF)); apply in_app_iff; left; exact H|].
    intros Hs. exact (swl_nodup_disj _ _ pn ND2 H Hs).
  - intros [H Hs]. apply (Permutation_in _ HPermF) in H. apply in_app_iff in H as [H|H]; [exact H|].
    exfalso. exact (Hs H). }
set (nt := Z.of_nat (length t) + 1) in *.
assert (Hp2in5 : In (p2, nt) (ablocks B ly5 S5)) by (apply Hbl5; right; right; reflexivity).
(* a block live at the entry that answer handed out again: one the recorder owned, freed by record()'s spill arm or
   as the old answer *)
assert (HFO1 : forall X, In (X, nt) (ablocks B ly S) -> X = p1 \/ X = p2 -> In (X, nt) O).
{ intros X Hin HX.
  destruct (in_dec swl_pair_dec (X, nt) F) as [HF' | HF']; [exact (HFO _ HF')|].
  assert (H2 : In (X, nt) (ablocks B ly2 S2)) by (apply JB1; split; [exact Hin | exact HF']).
  destruct (Z.eq_dec X old) as [Eo | Ne].
  - destruct Hold_cases as [Ho | (a0 & Ho & Hin0)].
    + exfalso. destruct (al_blocks _ _ LAWS _ _ _ _ _ X nt HAR0 Hin) as (_ & Hb4 & _). lia.
    + assert (E0 : (X, nt) = a0) by exact (swl_same_start B ly2 S2 W2 _ _ (X, nt) a0 HAR2 H2 (HO1bl _ Hin0) ltac:(cbn [fst]; lia)).
      rewrite E0. exact (proj1 (proj1 (HO1 a0) Hin0)).
  - exfalso. destruct (Hfresh (X, nt) H2 Ne) as [N1 N2]. destruct HX as [-> | ->]; [exact (N1 eq_refl) | exact (N2 eq_refl)]. }
unfold apost_baseF. exists fx5, ly5, S5, regs5, mem5, md5.
split; [rewrite T1'; reflexivity|].
split; [exact HFX5|]. split; [exact HCSR5|].
split; [eapply (ajournal_mono_k SEGS B); [exact HJ5 | rewrite EVS; unfold EV_SUP_WORKER_LIST, EV_RECORD; lia]|].
split; [exact (aregs_preserved_trans _ _ _ HPT HP5)|].
exists (fst (rec_answer R2 e x false)), t, p2, O'.
split; [rewrite swl_model; apply surjective_pairing|].
split; [exact H10'|]. split; [exact Hp2|]. split; [exact HREP5|].
(* the recorder's blocks after the call: what it owned, or blocks that were not live at the entry *)
split.
{ intros pn Hpn. destruct (in_dec swl_pair_dec pn (ablocks B ly S)) as [Hin | Hnin]; [left | right; exact Hnin].
  apply HO' in Hpn as [(Hpn1 & _) | ->].
  - exact (proj1 (proj1 (HO1 pn) Hpn1)).
  - exact (HFO1 p1 Hin (or_introl eq_refl)). }
split; [exact Hp2in5|].
(* the caller's copy is none of the blocks that were live and none of the recorder's *)
split; [intros pn Hpn Hno Epn; subst pn; exact (Hno (HFO1 p2 Hpn (or_intror eq_refl)))|].
split.
{ intros Hin. apply in_map_iff in Hin as (pn & Est & Hpn). apply HO' in Hpn as [(Hpn1 & Hold) | ->].
  - pose proof (HO1bl _ Hpn1) as Hpn2.
    assert (Hpn5 : In pn (ablocks B ly5 S5)) by (apply Hbl5; left; split; [exact Hpn2 | exact Hold]).
    pose proof (swl_same_start B ly5 S5 W5 mem5 md5 pn (p2, nt) HAR5 Hpn5 Hp2in5 Est) as ->.
    exact (proj2 (Hfresh _ Hpn2 Hold) eq_refl).
  - cbn [fst] in Est. exact (Hp12 Est). }
split; [exact HS5|].
split.
{ intros pn Hpn Hno.
  assert (HnF : ~ In pn F) by (intros HF'; exact (Hno (HFO pn HF'))).
  assert (Hpn2 : In pn (ablocks B ly2 S2)) by (apply JB1; split; [exact Hpn | exact HnF]).
  assert (Hfo : fst pn <> old).
  { destruct Hold_cases as [Ho | (a0 & Ho & Hin0)].
    - destruct pn as [b m]. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hpn) as (_ & Hb4 & _). cbn [fst]. lia.
    - intros Est. pose proof (swl_same_start B ly2 S2 W2 _ _ pn a0 HAR2 Hpn2 (HO1bl _ Hin0) ltac:(lia)) as ->.
      exact (Hno (proj1 (proj1 (HO1 a0) Hin0))). }
  assert (Hpn5 : In pn (ablocks B ly5 S5)) by (apply Hbl5; left; split; [exact Hpn2 | exact Hfo]).
  split; [exact Hpn5|].
  assert (Hne : pn <> (p2, nt)) by exact (proj2 (Hfresh pn Hpn2 Hfo)).
  exact (swl_blocks_apart B ly5 S5 W5 mem5 md5 pn (p2, nt) HAR5 Hpn5 Hp2in5 Hne). }
split.
{ intros pn Hpn. apply Hbl5 in Hpn as [(Hpn2 & Hfo) | [-> | ->]].
  - apply JB1 in Hpn2 as [Hpn0 HnF]. destruct (in_dec swl_pair_dec pn O) as [HpO | HpO].
    + right; left. apply HO'. left. split; [apply HO1; split; [exact HpO | exact HnF] | exact Hfo].
    + left. split; [exact Hpn0 | exact HpO].
  - right; left. apply HO'. right. reflexivity.
  - right; right. reflexivity. }
split.
{ unfold LIVE_SUP_WORKER_LIST. rewrite swl_model. fold R2 e x t. lia. }
unfold XM_SUP_WORKER_LIST. rewrite swl_model. fold R2 e x t.
exact (mo_le_trans MT MTL _ _ _ _ _ MLE2 MLE5).
Qed.

End e.
End f.
End d.
