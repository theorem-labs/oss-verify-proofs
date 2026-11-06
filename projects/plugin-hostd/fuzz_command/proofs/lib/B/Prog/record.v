(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of record (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan,
   entry 0x8a728, 62 instructions): trecord_spec of a Theorem Labs lane's lib/B/Prog/record_c.v (a working branch f490061c104),
   proved over its callee contract rec_calls_free_c taken at every FP state, as the statement states it; the post is
   apost_base (record reaches no printf wrapper), at the entry's FP state throughout.

   A inlines record() into every recording function, so there is no A walk of it: this walk is made from B's code
   (lib/B/Prog/record_aux.v:12-41, measured with capstone), with A's inlined record() of
   lib/A/Prog/sup_pin_accept_s4.v (a working branch 3cc8391594b: the entry segment, the two arms, the call of
   rec_calls_free on the spill arm, the meet) as the template. The segments:
     entry  0x8a728 .. 0x8a75c  the frame, the shadow base, g_rec, ncalls; record()'s `bne ncalls, 16` splits:
     table  0x8a778 .. 0x8a7a8  ncalls := ncalls + 1, s1 := g_rec + 16 + 56 ncalls, to the meet (record_s1.v);
     spill  0x8a760 .. 0x8a774  rec_calls_free(&record.spill, 1) (cl_callS_wide), `j` to the meet;
     meet   0x8a7ac .. 0x8a7f8  record_s1.v rcb_meet: the alignment trap, the two checked stores, the return.
   Each run is the token executor (paj_run_tok / paj_run_to_tok, CmdPaLib.v), which resolves the inline checks by
   the slot's shadow entry; the call's frame chain is achain_low (s0 = fn, below alloc_ceiling; PASS4-REFIT.md B).

   Report / trap edges (each refuted at its branch, never stepped over):
     0x8a77c `blt a0,a2` -> unimp 0x8a7fc (UBSan: g_rec.ncalls++ overflows): refuted by paj_run (CmdPaLib.v; its branch
       step is decide_cond2_sound under facts_ok) at record.v:309, from the fact 0 <= ncalls <= 16 (record_aux.v:113,
       seeded by rcb_seedA, record_s0.v:99) and the branch fact ncalls <> 16, from rec_repA (record_c.v:97) by
       rcb_rep_ncalls (record_aux.v:351).
     0x8a788 `bgeu a2,a3` -> unimp (UBSan: index bound of g_rec.calls[ncalls]): refuted by paj_run at record.v:309,
       from the same two facts.
     0x8a7a0 `bltu a2,a0` -> unimp (UBSan: pointer overflow of g_rec.calls + ncalls): refuted by rcb_ub_7a0 at
       record.v:100 (applied at record.v:313), from VOBJS (record_c.v:85, atom A_OBJ 44 = g_rec) and rec_repA
       (record_c.v:97, ncalls <= 16).
     0x8a7b0 `bnez a0` -> unimp (UBSan: alignment of c for c->fn): refuted by paj_run at record_s1.v:155, from the fact
       c mod 8 = 0 (record_aux.v:136, seeded by rcb_meet_seed, record_s0.v:188) that rcb_rec_slot_ok (record_aux.v:152)
       gives from rec_repA (record_c.v:97).
     0x8a7c0 `bnez a1` (guarding 0x8a804 `blt` and 0x8a80c `jal __asan_report_store4`) and 0x8a7d8 `bnez a1` (guarding
       0x8a818 `blt` and 0x8a81c `jal __asan_report_store4`): refuted by paj_run's shadow-check step at record_s1.v:155,
       from sh_ok rcb_shok (record_s0.v:80: the slot's 56 bytes have zero shadow, CmdRecCells.v cmd_cf_grec /
       CmdRecBase.v cmd_addressable_chk), from HB (CmdBSyms B) and afn_pre's AR (record_c.v:88).

   Section hypotheses beyond the statement's (TREC_CALLS_FREE, VOBJS): HB (CmdBSyms B, a Theorem Labs lane's lib/B/YF0m.v), MTL
   (ameter_laws MT), cmd_sig_prog_PB (CmdObj.v cmd_sig_prog: the call target of rec_calls_free), PRW (prog_rw SEGS B:
   the writability of g_rec and record.spill, CmdRecCells.v PROG_WRITABLE's premise) and cmd_img_facts_tfib (a Theorem Labs lane's
   CmdRecImg.v statement at this walk's abstract segments); lib/B/Prog/RecordClosed.v discharges cmd_sig_prog_PB,
   PRW, cmd_img_facts_tfib and VOBJS at the pinned image. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_aux record_s0 record_s1.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecCells CmdRecRest CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_calls_free_c record_c CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma rcb_zcanon : forall x, 0 <= x < 2 ^ 64 -> zcanon x = x.
Proof. intros x Hx. unfold zcanon, M64. apply Z.mod_small. exact Hx. Qed.

Lemma rcb_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* s1 on the table arm: g_rec + 16 + 56 * ncalls (slli / slli / sub folded to one multiplication) *)
Lemma rcb_denot_slot : forall E nn, ew E 33 = Z_to_bv 64 (Z.of_nat nn) -> ew E 285 = Z_to_bv 64 A_G_REC ->
(nn < 16)%nat ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff 285 0)) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat nn).
Proof.
intros E nn E33 E285 Hn. apply rcb_denot_U.
assert (U1 : U E (SOff 33 0) = Z.of_nat nn) by (apply (U_atom E 33 (Z.of_nat nn) E33); lia).
assert (U5 : U E (SOff 285 0) = A_G_REC) by (apply (U_atom E 285 A_G_REC E285); unfold A_G_REC; lia).
rewrite U_SAlu, U_SAlu, U_SMd, U1, U5, !U_SLit. cbn [zalu_raw zmd_raw].
rewrite (rcb_zcanon 56), (rcb_zcanon 16) by lia.
rewrite (rcb_zcanon (Z.of_nat nn * 56)) by lia.
rewrite (rcb_zcanon (Z.of_nat nn * 56 + 16)) by lia.
unfold A_G_REC, OFF_CALLS, CALL_SIZE. rewrite rcb_zcanon by lia. lia.
Qed.

(* UBSan trap site 0x8a7a0 (`bltu a2,a0` -> unimp 0x8a7fc, the pointer overflow of `g_rec.calls + ncalls`,
   recorder.c:217): a2 = ~(g_rec + 16), a0 = 56 * ncalls; with g_rec the constant A_G_REC and ncalls <= 16 the
   branch is not taken *)
Lemma rcb_ub_7a0 : forall E nn, ew E 285 = Z_to_bv 64 A_G_REC -> ew E 33 = Z_to_bv 64 nn -> 0 <= nn <= 16 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 285 16) (SLit (-1)))) (sv_denot E (SMd M_MUL (SOff 33 0) (SLit 56)))
  = false.
Proof.
intros E nn E285 E33 Hn. rewrite branch_ltu_U.
rewrite U_SAlu, U_SMd, !U_SLit.
rewrite (U_atom E 33 nn E33) by lia.
rewrite (U_atom_off E 285 A_G_REC 16 E285) by (unfold A_G_REC; lia).
cbn [zmd_raw]. rewrite (rcb_zcanon 56) by lia. rewrite (rcb_zcanon (nn * 56)) by lia.
lazymatch goal with |- (?x <? _) = false => let v := eval vm_compute in x in change x with v end.
apply Z.ltb_ge. lia.
Qed.

(* the frame's four words, read off the entry segment's stack region *)
Lemma rcb_frame_words {fx : YK11.FPState} : forall (segs : list Segment) (W : world segs) m (regs : bvmap 5 word) E0 sp0 cs,
(forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r) ->
bv_unsigned (ew E0 2) = sp0 ->
region_ok segs E0 (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 cs) ->
(forall j r, nth_error rcb_saved j = Some r ->
   In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
forall j r, nth_error rcb_saved j = Some r ->
  val_mem segs (mrestrict (w_H W) m) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros segs W m regs E0 sp0 cs HEL Hsp HR HIn j r Hj.
assert (Hr : In r rcb_saved) by (eapply nth_error_In; exact Hj).
assert (Hr32 : 0 <= r < 32) by (cbv [rcb_saved In] in Hr; lia).
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region (segs:=segs) E0 _ 2%nat sp0 cs _ _ _ _ (-8 - 8 * Z.of_nat j) 8%N
  (SOff (Z.to_nat r) 0) (bv_unsigned (getr regs (Z_to_bv 5 r))) HR Hsp (HIn j r Hj)).
- cbn [sv_denot]. rewrite (HEL (Z.to_nat r) (Z_to_bv 5 r)).
  + rewrite Z.add_0_r. reflexivity.
  + rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- cbn. lia.
Qed.

Lemma rcb_frame_in : forall j r, nth_error rcb_saved j = Some r ->
In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0)))
  [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Proof.
intros j r Hj.
do 4 (destruct j as [|j]; [cbn [nth_error rcb_saved] in Hj; injection Hj as <-; cbn; tauto|]).
destruct j; cbn in Hj; discriminate.
Qed.

(* the footprint of rec_calls_free on record.spill alone: the spill's nargs word and the blocks it frees *)
Lemma rcb_rcf_fp_inv : forall P a, inFP (rcf_fp A_REC_SPILL [P]) a ->
A_REC_SPILL + 4 <= a < A_REC_SPILL + 8 \/ exists p n, In (p, n) P /\ p <= a < p + req_size n.
Proof.
intros P a Ha. unfold rcf_fp in Ha. cbn [length seq map concat] in Ha. rewrite app_nil_r in Ha.
apply inFP_app in Ha as [Ha | Ha].
- left. apply inFP_cons in Ha as [Ha | Ha];
  [unfold CALL_SIZE, CALL_OFF_NARGS in Ha; cbn in Ha; lia | exact (False_ind _ (inFP_nil a Ha))].
- right. exact (inFP_ablocks_fp_inv P a Ha).
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
(* the statement's callee contract (taken at every FP state) and object bridge (record_c.v:84-85) *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses: the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), the meter's laws, the program
   functions' call targets (a Theorem Labs lane's CmdObj.v cmd_sig_prog, proved at the pinned image by CmdRecRest.v
   cmd_sig_prog_PB), the program statics' writability (the core's prog_rw, CmdRecCells.v's PRW), and the per-binary
   image facts (a Theorem Labs lane's CmdRecImg.v cmd_img_facts_tfib) at this walk's abstract segments *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma rcb_sig_rcf : SIG CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. rewrite cmd_sig_prog_PB by (vm_compute; repeat (first [left; reflexivity | right])). reflexivity. Qed.

(* arodata_okP reads only the read-only bytes *)
Lemma rcb_aro_kept : forall (rd rd' : reader), arodata_okP SEGS RLO RHI B rd ->
(forall a, in_roP SEGS RLO RHI a -> rd' a = rd a) -> arodata_okP SEGS RLO RHI B rd'.
Proof. intros rd rd' H HK a Hr Ho He. rewrite HK by exact Hr. exact (H a Hr Ho He). Qed.

(* the blocks rec_calls_free frees take their bytes out of the live count *)
Lemma rcb_bb_perm : forall ly S ly2 S2 P, Permutation (ablocks B ly S) (ablocks B ly2 S2 ++ P) ->
(forall pn, In pn P -> 0 <= snd pn) -> blocks_bytes S2 <= blocks_bytes S.
Proof.
intros ly S ly2 S2 P HP Hpos.
rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B ly2 S2).
rewrite (bsum_perm _ _ HP), bsum_app.
assert (HP0 : 0 <= bsum P).
{ clear - Hpos. induction P as [|pn P IH]; [cbn; lia|].
  rewrite bsum_cons. pose proof (Hpos pn (or_introl eq_refl)).
  assert (0 <= bsum P) by (apply IH; intros q Hq; apply Hpos; right; exact Hq). lia. }
lia.
Qed.

(* the awr_ok of the entry segment's regions: the frame (atom 2), the GOT word and the shadow cell (read only),
   g_rec.ncalls (the footprint's first range) *)
Local Ltac rcb_awrA Usp UG WS :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact Usp | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |];
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | (eapply awr_ok_cons_gen with (n := 285%nat);
     [reflexivity | exact UG
     | intros aa Haa; apply (rcb_awr_ncalls B HB cmd_img_facts_tfib); cbn [YP09.r_wlo YP09.r_whi] in Haa;
       unfold OFF_NCALLS in *; lia |]) ].
(* the windows of the entry segment's regions lie in the frame or g_rec.ncalls *)
Local Ltac rcb_win Usp UG :=
  intros ?b ?wlo ?whi ?a' ?Hin ?Hrr; vm_compute in Hin; cbv beta;
  repeat (destruct Hin as [?Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UG in Hrr;
    first [left; lia | right; unfold OFF_NCALLS; lia]|]); destruct Hin.
(* what the runs of the entry segment kept: every byte outside the frame and g_rec.ncalls *)
Local Ltac rcb_keep E W sp Usp UG Ha :=
  repeat (lazymatch goal with Hfr : frame_of E _ (mrestrict _ ?m) (mrestrict _ ?m') |- aview _ _ ?m' _ = _ =>
    rewrite (kept_of_frame (segs := SEGS) E _ (w_H W) m m'
      (fun a => sp - 32 <= a < sp \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) Hfr);
    [ | rcb_win Usp UG | exact Ha | tauto ] end); reflexivity.

(* the contract of lib/B/Prog/record_c.v *)
Theorem trecord_holds : trecord_spec B MT.
Proof.
unfold trecord_spec.
intros ly S W regs mem md ch fn R O HPRE HROD H10 Hfn HREP HEV HMOK.
change (SRr SEGS W (cfg_at SEGS (BASE + RCB_E) regs mem md)
  (apost_base SEGS B RECORD_STK (rca_recFP R O) regs ly S W mem md (EV_RECORD R) (rcb_post B MT R fn O ly S))).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (Hsp46 : 2 ^ 46 + 32 <= spZ regs <= 2 ^ 47)
  by (change (2 ^ 46) with 70368744177664; change (2 ^ 47) with 140737488355328; rewrite WS in Hslo; lia).
destruct (rcb_rep_ncalls B ly S (rdW W mem) R O HREP) as [Hlen HNC].
assert (HOS : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (proj1 (rcb_rep_blocks B ly S (rdW W mem) R O HREP pn Hpn))).
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
destruct (rcb_seedA B HB VOBJS PRW ly S W regs mem md n HAR Hstk Hpres Hn HNC) as [HS SHOK].
set (E := rcb_EA regs n) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rcb_EA; apply Eimg_env).
assert (EL : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs r).
{ intros kk r Hk. unfold E, rcb_EA. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (unfold E, rcb_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0%nat)).
assert (E33 : ew E 33 = Z_to_bv 64 n)
  by (unfold E, rcb_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1%nat)).
assert (EG : ew E 285 = Z_to_bv 64 A_G_REC).
{ change 285%nat with (A_OBJ 44).
  rewrite (img_env_atomP E (A_OBJ 44) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), (rcb_grec_val VOBJS). reflexivity. }
assert (ESP : ew E 294 = Z_to_bv 64 A_REC_SPILL).
{ change 294%nat with (A_OBJ 53).
  rewrite (img_env_atomP E (A_OBJ 53) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), (rcb_spill_val VOBJS). reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EL 2%nat 2%bv eq_refl); reflexivity).
assert (UG : bv_unsigned (ew E 285) = A_G_REC) by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
clearbody E.
pose proof (ajournal_init SEGS B RECORD_STK (rca_recFP R O) ly S W regs mem md ch HPRE) as HJ.
unfold cfg_at, w64.
(* the entry segment's regions: the frame, the GOT word, the shadow cell, g_rec.ncalls *)
assert (WIN : forall b wlo whi a, In (b, wlo, whi) (windows rcb_rsA) ->
  base_val E b + wlo <= a < base_val E b + whi ->
  spZ regs - 32 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4).
{ intros b wlo whi a Hin Hrr. vm_compute in Hin. cbv beta.
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?UG in Hrr;
     first [left; lia | right; unfold OFF_NCALLS; lia]|]); destruct Hin. }
(* 0x8a728 .. 0x8a75c: the frame, the shadow base, g_rec, g_rec.ncalls, record()'s branch *)
paj_run_tok RUN HS HJ SHOK rcb_Bspan.
{ rcb_awrA Usp UG WS. }
psrr_branch_tok RUN BR HS SHOK rcb_Bspan.
- (* g_rec.ncalls <> 16: the call takes the slot g_rec.calls[ncalls] *)
  assert (Hn16 : (length (r_calls R) < 16)%nat).
  { rewrite branch_ne_U, (U_atom E 33 n E33 ltac:(lia)), U_SLit in Hc.
    rewrite (rcb_zcanon 16) in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc. unfold n in Hc. lia. }
  clear Hc.
  assert (Hsf : rec_spill_frees R = 0).
  { unfold rec_spill_frees.
    replace (Nat.ltb (length (r_calls R)) 16) with true by (symmetry; apply Nat.ltb_lt; exact Hn16). reflexivity. }
  assert (Hslot : rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * n).
  { unfold rec_slot. replace (Nat.ltb (length (r_calls R)) 16) with true by (symmetry; apply Nat.ltb_lt; exact Hn16).
    reflexivity. }
  (* 0x8a778 .. 0x8a7a0: ncalls + 1 (the overflow trap 0x8a77c and the bound trap 0x8a788 are decided by the facts
     0 <= ncalls <= 16 and ncalls <> 16), g_rec.ncalls := ncalls + 1, 56 * ncalls; the run stops at 0x8a7a0 *)
  paj_run_tok RUN HS HJ SHOK rcb_Bspan.
  { rcb_awrA Usp UG WS. }
  psrr_branch_tok RUN BR HS SHOK rcb_Bspan.
  + (* 0x8a7a0 taken: the UBSan trap (pointer overflow of g_rec.calls + ncalls), refuted *)
    exfalso. rewrite (rcb_ub_7a0 E n EG E33 Hn) in Hc. discriminate.
  + (* 0x8a7a4 .. 0x8a7a8: s1 := g_rec + 16 + 56 * ncalls, to the meet *)
    paj_run_to_tok RUNTO HS HJ SHOK rcb_Bspan RCB_MEET.
    { rcb_awrA Usp UG WS. }
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (18%bv : bv 5) P18.
    pose proof (st_ok_pi_restrict_reg (w_H W) E _ _ (9%bv : bv 5) HS) as P9.
    lazymatch type of P9 with _ = sv_denot _ (sr_get ?aa ?rr) =>
      let v := eval vm_compute in (sr_get aa rr) in change (sr_get aa rr) with v in P9 end.
    cbn [ms_regs restrict mkst] in P9.
    (* the frame and the bumped call count *)
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region RCB_FRAME)) in
      pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 0 r0 HS eq_refl) as HRst;
      let r3 := eval vm_compute in (nth 3 (ss_mem ssx) rcb_ncalls) in
      pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 3 r3 HS eq_refl) as HRn end.
    cbn [ms_mem restrict mkst] in HRst, HRn.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      set (memM := ms_mem msx) in *; set (regsM := ms_regs msx) in * end.
    (* the memory the prologue and the table arm wrote: the frame and g_rec.ncalls *)
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
      ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W memM a = rdW W mem a).
    { intros a Ha H1 H2. unfold memM. rcb_keep E W (spZ regs) Usp UG Ha. }
    assert (HFRM : forall j r, nth_error rcb_saved j = Some r ->
      val_mem SEGS (mrestrict (w_H W) memM) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))))
      by exact (rcb_frame_words SEGS W memM regs E (spZ regs) _ EL Usp HRst rcb_frame_in).
    assert (HNC1 : aval_mem (rdW W memM) (A_G_REC + OFF_NCALLS) 4 (n + 1)).
    { apply aval_mem_view. change 4%nat with (N.to_nat 4).
      apply (field_of_region (segs:=SEGS) E _ 285 A_G_REC _ _ _ _ _ 8 4%N (SOff 33 1) _ HRn UG
        ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); [|cbn; lia|cbn; lia].
      apply rcb_denot_U. rewrite U_SOff, E33, unsigned_lit_small by lia. apply rcb_zcanon. lia. }
    (* the registers at the meet *)
    assert (Rsp2 : spZ regsM = spZ regs - RCB_FRAME).
    { unfold spZ at 1. rewrite P2, Usp, unsigned_lit_small by lia. unfold RCB_FRAME. lia. }
    assert (P3' : getr regsM 3 = getr regs 3) by (rewrite P3; apply EL; reflexivity).
    assert (P4' : getr regsM 4 = getr regs 4) by (rewrite P4; apply EL; reflexivity).
    assert (P8' : getr regsM 8 = w64 fn) by (rewrite P8, (EL 10%nat 10%bv eq_refl); exact H10).
    assert (P18' : getr regsM 18 = w64 SB) by (rewrite P18; exact E32).
    assert (P9' : getr regsM 9 = w64 (rec_slot R)).
    { rewrite P9, (rcb_denot_slot E (length (r_calls R)) E33 EG Hn16), Hslot. reflexivity. }
    assert (Phi : forall r, 19 <= r <= 27 -> getr regsM (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r Hr. unfold regsM.
      assert (Hr9 : r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr9 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
      (lazymatch goal with |- getr _ ?rr = _ => prreg HS rr Pr end;
       rewrite Pr; lazymatch goal with |- ew E ?nn = getr _ ?rr => exact (EL nn rr eq_refl) end). }
    (* the recorder after record()'s stores into the slot *)
    assert (HPEND : forall rd', (forall a, 0 <= a < 2 ^ 64 -> ~ (rec_slot R <= a < rec_slot R + 8) -> rd' a = rdW W memM a) ->
      aval_mem rd' (rec_slot R + CALL_OFF_FN) 4 fn -> aval_mem rd' (rec_slot R + CALL_OFF_NARGS) 4 0 ->
      rec_repA B ly S rd' (rec_record R fn []) O).
    { intros rd' Hrd' HFN HNA.
      apply (rcb_rep_record_lt B ly S (rdW W mem) ly S rd' R O fn HREP Hn16 Hfn).
      - apply (aval_mem_agree_in (rdW W memM) rd' (A_G_REC + OFF_NCALLS) 4); [exact HNC1 | | lia | cbn; lia].
        apply rd_agree_of. intros y Hy. apply Hrd'; rewrite Hslot in *; unfold A_G_REC, OFF_NCALLS, OFF_CALLS, CALL_SIZE in *; lia.
      - exact HFN.
      - exact HNA.
      - intros a Ha Hnc Hsl.
        rewrite (Hrd' a); [|unfold rcb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia | exact Hsl].
        apply KEEP; [unfold rcb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia
          | rewrite WS in Hslo; unfold rcb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia | exact Hnc].
      - intros pn Hpn. split; [exact (HOS pn Hpn)|]. destruct pn as [q k]. intros i Hi. cbn [fst snd] in Hi |- *.
        destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR (HOS _ Hpn)) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk0).
        pose proof (req_size_pos k ltac:(lia)) as [_ Hq].
        assert (Hni : ~ in_img SEGS (q + i)) by (apply (blk_img SEGS B LAWS ly S W mem md q k (q + i) HAR (HOS _ Hpn)); lia).
        rewrite (Hrd' (q + i)).
        + apply KEEP; [lia | rewrite WS in Hslo; lia |].
          intros Hnc. apply Hni. apply cmd_prog_img, rcb_grec_in. unfold OFF_NCALLS, REC_SIZE in *. lia.
        + lia.
        + intros Hin. apply Hni. apply cmd_prog_img. apply (rcb_in_PG (rec_slot R)); [exact (rcb_rec_slot_ok R Hlen)|].
          unfold CALL_SIZE. lia. }
    exact (rcb_meet B MT HB PRW cmd_img_facts_tfib ly S W regs mem md ch fn R O ly S W regsM memM _ 0 O []
      HPRE HJ ltac:(unfold EV_RECORD; rewrite Hsf; lia) ltac:(rewrite app_nil_r; apply Permutation_refl)
      ltac:(rewrite Hsf; reflexivity) (fun pn (H : In pn []) => False_ind _ H)
      (fun pn => conj (fun H => conj H (fun Hf : In pn [] => Hf)) (fun H => proj1 H)) ltac:(lia)
      ltac:(unfold XM_RECORD; rewrite Hsf, Z.mul_0_l; exact (mle_start MT S MTL)) Hlen Hfn
      Rsp2 P9' P8' P18' P3' P4' Phi HFRM HPEND).
- (* g_rec.ncalls = 16: record() frees the spill's old arguments by rec_calls_free(&record.spill, 1) *)
  assert (Hn16 : length (r_calls R) = 16%nat).
  { rewrite branch_ne_U, (U_atom E 33 n E33 ltac:(lia)), U_SLit in Hc.
    rewrite (rcb_zcanon 16) in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc. unfold n in Hc. lia. }
  assert (Hlt : Nat.ltb (length (r_calls R)) 16 = false) by (apply Nat.ltb_ge; lia).
  assert (Hslot : rec_slot R = A_REC_SPILL) by (unfold rec_slot; rewrite Hlt; reflexivity).
  pose proof HREP as (QL & HA & HO).
  pose proof HA as (_ & _ & _ & (_ & _ & _ & _ & HSP & _) & _ & _ & _ & HW).
  pose proof HSP as (_ & HSP6 & HLP & _ & HSPN & HSPND & HSPA).
  set (P := l_spill QL) in *.
  assert (Hsf : rec_spill_frees R = Z.of_nat (length P)).
  { unfold rec_spill_frees. rewrite Hlt. rewrite HLP. reflexivity. }
  assert (HEVk : EV_REC_CALLS_FREE [P] = Z.of_nat (length P))
    by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; reflexivity).
  assert (HPin : forall pn, In pn P -> In pn (ablocks B ly S)) by exact (acall_at_in _ _ _ _ _ HSP).
  assert (HPO : forall pn, In pn P -> In pn O).
  { intros pn Hpn. apply HO. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hpn. }
  (* 0x8a760 .. 0x8a770: s1 := &record.spill, a1 := 1, a0 := s1, the call rec_calls_free(&record.spill, 1) *)
  paj_run_tok RUN HS HJ SHOK rcb_Bspan.
  { rcb_awrA Usp UG WS. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (18%bv : bv 5) Q18.
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region RCB_FRAME)) in
      pose proof (st_ok_pi_region_nth E ssx msx 0 r0 HS eq_refl) as HRst;
      let r3 := eval vm_compute in (nth 3 (ss_mem ssx) rcb_ncalls) in
      pose proof (st_ok_pi_region_nth E ssx msx 3 r3 HS eq_refl) as HRn
  | st_ok _ _ ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region RCB_FRAME)) in
      pose proof (st_ok_region_nth (segs:=SEGS) E ssx msx 0 r0 HS eq_refl) as HRst;
      let r3 := eval vm_compute in (nth 3 (ss_mem ssx) rcb_ncalls) in
      pose proof (st_ok_region_nth (segs:=SEGS) E ssx msx 3 r3 HS eq_refl) as HRn
  end.
  cbn [ms_mem restrict mkst] in HRst, HRn.
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msx) => set (regsc := ms_regs msx) in *; set (memc := ms_mem msx) in *
  | st_ok _ _ _ (restrict _ ?msx) => set (regsc := ms_regs msx) in *; set (memc := ms_mem msx) in *
  end.
  (* the prologue wrote the frame only: g_rec.ncalls still holds ncalls *)
  assert (HNCc : aval_mem (rdW W memc) (A_G_REC + OFF_NCALLS) 4 n).
  { apply aval_mem_view. change 4%nat with (N.to_nat 4).
    apply (field_of_region (segs:=SEGS) E _ 285 A_G_REC _ _ _ _ _ 8 4%N (SOff 33 0) _ HRn UG
      ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); [|cbn; lia|cbn; lia].
    cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  assert (KEEPw : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W memc a = rdW W mem a).
  { intros a Ha H1 H2. unfold memc. rcb_keep E W (spZ regs) Usp UG Ha. }
  assert (KEEPc : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W memc a = rdW W mem a).
  { intros a Ha H1. destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS)) as [Hl | Hl];
    [|destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS + 4)) as [Hh | Hh]].
    - apply KEEPw; [exact Ha | exact H1 | lia].
    - replace a with ((A_G_REC + OFF_NCALLS) + Z.of_nat (Z.to_nat (a - (A_G_REC + OFF_NCALLS)))) by lia.
      rewrite (HNCc (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)),
              (HNC (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)). reflexivity.
    - apply KEEPw; [exact Ha | exact H1 | lia]. }
  assert (KEEPBc : forall q k a, In (q, k) (ablocks B ly S) -> q <= a < q + k -> rdW W memc a = rdW W mem a).
  { intros q k a Hin Ha.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR Hin) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk0).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hq].
    apply KEEPc; [lia | rewrite WS in Hslo; lia]. }
  assert (KEEPRc : forall a, in_roP SEGS RLO RHI a -> rdW W memc a = rdW W mem a).
  { intros a Hro. destruct (cmd_ro_prog_apart a Hro) as [Hi Hpg].
    pose proof (pa_img_range a Hi) as Hrg.
    apply KEEPc; [lia | rewrite WS in Hslo; lia]. }
  assert (HAc : arep_at (ablocks B ly S) (rdW W memc) A_G_REC A_REC_SPILL R QL).
  { apply (rcb_arep_keep (ablocks B ly S) (ablocks B ly S) (rdW W mem) (rdW W memc) R QL HA).
    - intros a Ha. apply KEEPc;
      [unfold rcb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia
      | rewrite WS in Hslo; unfold rcb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia].
    - intros pn Hpn. split; [exact (lay_blocks_in _ _ _ _ _ _ HA pn Hpn)|].
      apply rd_agree_of. intros x Hx. destruct pn as [q k]. cbn [fst snd] in Hx |- *.
      exact (KEEPBc q k x (lay_blocks_in _ _ _ _ _ _ HA (q, k) Hpn) Hx). }
  assert (HSPc : acall_at (ablocks B ly S) (rdW W memc) A_REC_SPILL (r_spill R) P)
    by (pose proof HAc as (_ & _ & _ & (_ & _ & _ & _ & H5 & _) & _); exact H5).
  pose proof HSPc as (_ & _ & _ & _ & HSPNc & HSPNDc & HSPAc).
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W memc))
    by (apply (rcb_aro_kept (rdW W mem)); [exact HROD | exact KEEPRc]).
  (* the registers at the call *)
  assert (HRA : getr regsc 1 = Z_to_bv 64 (BASE + RCB_RET_RCF)) by (rewrite Q1; reflexivity).
  assert (Q2' : getr regsc 2 = w64 (spZ regs - 32)).
  { rewrite Q2, Usp. reflexivity. }
  assert (Q3' : getr regsc 3 = getr regs 3) by (rewrite Q3; apply EL; reflexivity).
  assert (Q4' : getr regsc 4 = getr regs 4) by (rewrite Q4; apply EL; reflexivity).
  assert (Q8' : getr regsc 8 = w64 fn) by (rewrite Q8, (EL 10%nat 10%bv eq_refl); exact H10).
  assert (Q9' : getr regsc 9 = w64 A_REC_SPILL) by (rewrite Q9; exact ESP).
  assert (Q10' : getr regsc 10 = w64 A_REC_SPILL) by (rewrite Q10; exact ESP).
  assert (Q11' : getr regsc 11 = w64 (Z.of_nat (length [P]))) by (rewrite Q11; reflexivity).
  assert (Q18' : getr regsc 18 = w64 SB) by (rewrite Q18; exact E32).
  assert (Qhi : forall r, 19 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. unfold regsc.
    assert (Hr9 : r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr9 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    (lazymatch goal with |- getr _ ?rr = _ => prreg HS rr Pr end;
     rewrite Pr; lazymatch goal with |- ew E ?nn = getr _ ?rr => exact (EL nn rr eq_refl) end). }
  assert (HFRc : forall j r, nth_error rcb_saved j = Some r ->
    val_mem SEGS (mrestrict (w_H W) memc) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))))
    by exact (rcb_frame_words SEGS W memc regs E (spZ regs) _ EL Usp HRst rcb_frame_in).
  rewrite rcb_sig_rcf.
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W regsc memc _ RECORD_STK (spZ regs) (rca_recFP R O) ly S W mem md [] ly S _ 0
      REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [P]) (EV_REC_CALLS_FREE [P]) (-32) (getr regsc 1) [] _ HJ);
    [ unfold spZ at 1; rewrite Q2'; unfold w64; rewrite unsigned_lit_small by lia; lia
    | reflexivity | lia | vm_compute; congruence | rewrite WS; vm_compute; congruence
    | rewrite Q3'; exact Hgp | rewrite Q4'; exact Htp | reflexivity
    | rewrite HRA; apply ret_ok_codeptr_v; [unfold RCB_RET_RCF, AF_record; lia | reflexivity]
    | rewrite HRA, unsigned_lit_small by (unfold RCB_RET_RCF, AF_record; lia); unfold RCB_RET_RCF, AF_record; lia
    | apply achain_low; unfold s0Z; rewrite Q8'; unfold w64;
      rewrite unsigned_lit_small by (unfold REC_FN_COUNT in Hfn; lia); unfold REC_FN_COUNT in Hfn; lia
    | | | ].
    - intros HPRE1.
      assert (HT := TREC_CALLS_FREE fx ly S W regsc memc _ [] A_REC_SPILL [P] HPRE1 HRODc Q10' Q11'
        ltac:(cbn [length]; lia)
        ltac:(right; left; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE; cbn [length Z.of_nat]; lia)
        ltac:(unfold A_REC_SPILL; reflexivity)).
      unfold apost_base, cfg_at, w64 in HT. apply HT.
      + intros i P' Hi. destruct i as [|i]; [|destruct i; discriminate Hi].
        cbn [nth_error] in Hi. injection Hi as <-.
        split; [rewrite HLP; exact HSP6|]. split.
        * cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r, HLP. exact HSPNc.
        * intros a pn Ha. destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es.
          -- destruct (HSPAc a s pn Es Ha) as (G1 & _ & G3 & _). split; [|exact G3].
             cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. exact G1.
          -- exfalso. apply nth_error_None in Es.
             pose proof (proj1 (nth_error_Some P a) ltac:(rewrite Ha; discriminate)). unfold P in *. lia.
      + cbn [concat]. rewrite app_nil_r. exact HSPNDc.
      + rewrite HEVk, <- Hsf. unfold EV_RECORD in HEV. lia.
      + unfold XM_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r, <- Hsf. exact HMOK.
    - intros a Ha. destruct (rcb_rcf_fp_inv P a Ha) as [Hs | (p & k & Hin & Hr)].
      + apply (rcb_awr_slot B HB cmd_img_facts_tfib); [exact Hlen | rewrite Hslot; lia].
      + unfold awr_byte. right; left. split; [|exists p, k; split; [exact (HPin _ Hin) | exact Hr]].
        unfold rca_recFP. rewrite Hlt. apply inFP_cons. right. apply inFP_cons. right.
        replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp O p k (a - p)); [exact (HPO _ Hin) | lia].
    - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
      destruct (rcb_rcf_fp_inv P a Ha) as [Hs | (p & k & Hin & Hr)];
        [unfold A_REC_SPILL in Hs; rewrite WS in Hw; lia|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR (HPin _ Hin)) as (_ & _ & Hpc & _). rewrite WS in Hw. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJr & HP2 & HK2).
  destruct HK2 as (HPERM & _ & _ & _ & _ & HRSP & _ & _ & HMLE).
  pose proof (HRSP R QL HAc eq_refl eq_refl) as HREP2.
  pose proof (proj1 HJr) as HAR2.
  pose proof HJr as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
  (* 0x8a774: `j 0x8a7ac`, record()'s arms meet *)
  rewrite HRA.
  destruct (rcb_seed0 W2 regs2 mem2 RCB_RET_RCF) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 rcb_Bspan RCB_MEET.
  { apply awr_ok_nil. }
  pmkst HS2.
  lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    set (regs1 := ms_regs msx) in *; set (mem1 := ms_mem msx) in * end.
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> rdW W2 mem1 a = rdW W2 mem2 a).
  { intros a Ha. lazymatch goal with Hfr : frame_of _ _ (mrestrict _ mem2) (mrestrict _ _) |- _ =>
      apply (kept_of_frame (segs := SEGS) _ _ (w_H W2) mem2 mem1 (fun _ => False) Hfr);
      [|exact Ha | tauto]; intros b wlo whi a' Hin; destruct Hin end. }
  assert (HAE2 : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 []))).
  { split; [intros nn Hnn; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS2 HAE2 ltac:(vm_compute; reflexivity)) as HPT3.
  cbn [ms_regs restrict] in HPT3.
  pose proof (aregs_preserved_trans _ _ _ HP2 HPT3) as HPR.
  (* the recorder's blocks across the call *)
  set (O1 := concat (l_calls QL) ++ oblk (l_answer QL) ++ oblk (l_reply QL)) in *.
  assert (HO1 : forall pn, In pn O1 <-> In pn O /\ ~ In pn P).
  { intros pn. rewrite (HO pn). exact (rcb_spill_split QL pn (proj1 HW)). }
  assert (HPERM' : Permutation (ablocks B ly S) (ablocks B ly2 S2 ++ P))
    by (cbn [concat] in HPERM; rewrite app_nil_r in HPERM; exact HPERM).
  assert (HBBm : blocks_bytes S2 <= blocks_bytes S).
  { apply (rcb_bb_perm ly S ly2 S2 P HPERM'). intros pn Hpn. destruct pn as [q k]. cbn [snd].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR (HPin _ Hpn)) as (_ & _ & _ & _ & _ & _ & Hk0). lia. }
  assert (HMLE' : mo_le MT S S2 (XM_RECORD MT R)).
  { unfold XM_REC_CALLS_FREE in HMLE. cbn [concat] in HMLE. rewrite app_nil_r in HMLE.
    unfold XM_RECORD. rewrite Hsf. exact HMLE. }
  (* the frame's four words across the call: the callee's journal keeps the stack above its window *)
  assert (HFRm : forall j r, nth_error rcb_saved j = Some r ->
    val_mem SEGS (mrestrict (w_H W2) mem1) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  { intros j r Hj.
    assert (Hj4 : (j < 4)%nat) by (apply (proj1 (nth_error_Some rcb_saved j)); rewrite Hj; discriminate).
    apply val_mem_view. apply (aval_mem_agree_in (rdW W memc) _ (spZ regs - 8 - 8 * Z.of_nat j) 8);
      [apply aval_mem_view; exact (HFRc j r Hj) | | lia | cbn; lia].
    apply rd_agree_of. intros y Hy. cbn [Z.of_nat] in Hy. rewrite WS in Hslo.
    rewrite KEEP3 by lia.
    apply G1; [lia | unfold REC_CALLS_FREE_STK, ASTACK; lia |].
    intros Hf. destruct (rcb_rcf_fp_inv P y Hf) as [Hs | (p & k & Hin & Hr)];
      [unfold A_REC_SPILL in Hs; lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR (HPin _ Hin)) as (_ & _ & Hqc & _). lia. }
  (* the recorder after record()'s stores into the emptied spill *)
  assert (HPENDm : forall rd',
    (forall a, 0 <= a < 2 ^ 64 -> ~ (rec_slot R <= a < rec_slot R + 8) -> rd' a = rdW W2 mem1 a) ->
    aval_mem rd' (rec_slot R + CALL_OFF_FN) 4 fn -> aval_mem rd' (rec_slot R + CALL_OFF_NARGS) 4 0 ->
    rec_repA B ly2 S2 rd' (rec_record R fn []) O1).
  { intros rd' Hrd' HFN HNA. rewrite Hslot in Hrd', HFN, HNA.
    rewrite (rec_record_spill R fn [] Hn16).
    change (set_spill R (fn, [])) with (set_spill (set_spill R (fst (r_spill R), [])) (fn, [])).
    apply (rcb_rep_spill_fn B ly2 S2 (rdW W2 mem2) ly2 S2 rd' _ O1 fn HREP2 eq_refl Hfn HFN HNA).
    - intros a Ha Hs. rewrite (Hrd' a) by (unfold rcb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia).
      apply KEEP3. unfold rcb_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
    - intros pn Hpn.
      pose proof (proj1 (rcb_rep_blocks B ly2 S2 (rdW W2 mem2) _ O1 HREP2 pn Hpn)) as Hin2.
      split; [exact Hin2|]. apply rd_agree_of. intros x Hx. destruct pn as [q k]. cbn [fst snd] in Hx, Hin2.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ q k HAR2 Hin2) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hk0).
      pose proof (req_size_pos k ltac:(lia)) as [_ Hq].
      rewrite (Hrd' x).
      + apply KEEP3. lia.
      + lia.
      + intros Hin. apply (blk_img SEGS B LAWS ly2 S2 W2 mem2 md2 q k x HAR2 Hin2 ltac:(lia)).
        apply cmd_prog_img, rcb_spill_in. unfold A_REC_SPILL, SC_SIZE in *. lia. }
  (* the registers at the meet *)
  assert (M2a : getr regs1 2 = getr regsc 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
  assert (M8a : getr regs1 8 = getr regsc 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
  assert (M9a : getr regs1 9 = getr regsc 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
  assert (M18a : getr regs1 18 = getr regsc 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
  assert (M3a : getr regs1 3 = getr regsc 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
  assert (M4a : getr regs1 4 = getr regsc 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
  assert (Rsp2 : spZ regs1 = spZ regs - RCB_FRAME).
  { unfold spZ at 1. rewrite M2a, Q2'. unfold w64. rewrite unsigned_lit_small by (rewrite WS in Hslo; lia).
    unfold RCB_FRAME. lia. }
  assert (M9 : getr regs1 9 = w64 (rec_slot R)) by (rewrite M9a, Hslot; exact Q9').
  assert (M8 : getr regs1 8 = w64 fn) by (rewrite M8a; exact Q8').
  assert (M18 : getr regs1 18 = w64 SB) by (rewrite M18a; exact Q18').
  assert (M3 : getr regs1 3 = getr regs 3) by (rewrite M3a; exact Q3').
  assert (M4 : getr regs1 4 = getr regs 4) by (rewrite M4a; exact Q4').
  assert (Mhi : forall r, 19 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by (intros r Hr; unfold regs1; rewrite (HPR r ltac:(unfold acallee_saved; lia)); exact (Qhi r Hr)).
  exact (rcb_meet B MT HB PRW cmd_img_facts_tfib ly S W regs mem md ch fn R O ly2 S2 W2 regs1 mem1 _
    (0 + EV_REC_CALLS_FREE [P]) O1 P
    HPRE HJ2 ltac:(unfold EV_RECORD; rewrite HEVk, Hsf; lia) HPERM' (eq_sym Hsf) HPO HO1 HBBm HMLE' Hlen Hfn
    Rsp2 M9 M8 M18 M3 M4 Mhi HFRm HPENDm).
Qed.
End e.
End f.
End d.
