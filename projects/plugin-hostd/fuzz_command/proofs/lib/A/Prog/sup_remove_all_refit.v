(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the prologue of sup_call's ASan walk (plugin-hostd/fuzz_command, 0x8a95c ..
   0x8a9cc): the frame, the test of g_rec.ncalls against 16 and record()'s two arms, up to the join 0x8a9d0, where
   the body's statement (sup_call_s3.v's SC_B_stmt) takes over in the state `sc_mid`.

   Pass-4/5 re-fit: rec_calls_free's contract is taken at every FP state and used at the
   entry's fx (its post is apost_base, so the kit rule cl_callS_wide is unchanged). Statement pass 5 removed
   astack_pres, so the walk no longer derives it for rec_calls_free; the frame chain at that call is the empty one
   (s0 holds the line, a heap pointer below alloc_ceiling: achain_low). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_call_a.v, with its module paths, module names and numbers changed; 413 of its 520 lines of code are new or changed and 639 lines of the source are left out. *)
(* The ASan walk of sup_remove_all (plugin-hostd/fuzz_command, BASE + AF_sup_remove_all = 0x8ac44, 55
   instructions), in the form of cgif_file_fuzzer's cgif_close and flushFrame walks (proofs/cgif/cgif_file_fuzzer/lib/
   A/ACh2.v, A/ACjq.v): the executor over the position-abstract listing (lib/A/Prog/CmdPaLib.v), the two inline
   store4 checks removed by tok_load / tok_branch, the call of rec_calls_free through the kit's cl_callS_wide, and
   the tail jump `j answer` through sup_remove_all_refit_s3.v's sra_tail.

   0x8ac44 .. 0x8ac70 push ra, s0, s1, load the shadow base and g_rec.ncalls (n) and branch on n = 16.
   n < 16 (0x8ac8c): ncalls := n + 1, the slot is g_rec + 16 + 56 n (s0, pinned to atom 34 at 0x8aca8).
   n = 16 (0x8ac74): rec_calls_free(&record.spill, 1) frees the spill's arguments; the slot is record.spill.
   0x8aca8 .. 0x8acf8: c->fn := 3, c->nargs := 0 (each store behind a check of the slot's shadow, which the
   record keeps at 0), restore the frame and `j answer` with a0 = c, a1 = "resp 0", a2 = 1.

   Pass-4/5 re-fit (the re-fit recipe's worked example; copied from an earlier version of
   lib/A/Prog/sup_remove_all.v): the callee hypotheses hold at every FP state (forall fx0) and are used at the
   entry's fx: rec_calls_free keeps the FP state (apost_base, kit rule cl_callS_wide unchanged), answer is the last
   step (sup_remove_all_refit_s3.v's sra_tail, through cl_callS_wideF); the rounding-mode-0 premise HFRM goes to
   sra_tail for answer's own premise. Statement pass 5 removed astack_pres: the walk no longer derives it for
   rec_calls_free (the old HSTKc) or answer. The frame chains the two calls' afn_pre ask come from the walk: at
   rec_calls_free s0 = &record.spill < alloc_ceiling (achain_low, the empty chain); at answer s0 is the entry s0
   (sup_remove_all's own afn_pre chain, sup_remove_all_refit_s3.v HchT). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibF PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c answer_c sup_remove_all_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_remove_all_refit_s1 sup_remove_all_refit_s2 sup_remove_all_refit_s3 sup_remove_all_refit_s4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
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
(* the statement's own hypotheses (sup_remove_all_c.v:62-64), at every FP state *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's per-binary facts, with cgif's names and the names this port chose for the walks *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the statics are writable (the core's prog_rw, YCbq.v; the walk hypothesis PRW) and the image facts (IMG,
   CmdRecBase's cmd_img_facts: cif_prog_img, and CmdRecRo's RRO, RPG, cmd_ro_in_img, cmd_ro_ok_of_aro) *)
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
(* the step at the tail jump (sup_remove_all_s3.v) *)
Let TAILH := sra_tail B MT TANSWER VOBJS HB LAWS MTL IMG.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let AWP := awr_ok_cons_prog B HB IMG.

Ltac sra_awr WS Usp AW44 AW34 FPn FPs :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc fr ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_stack; [reflexivity | exact Usp | rewrite WS; cbn [YP09.r_wlo YP09.r_whi]; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply AWP; [reflexivity | first [exact AW44 | exact AW34] |
      cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha; first [apply FPn; lia | apply FPs; lia] |] ].
(* after a run the model is `with_vm_backing (m_vm_lazy md) mat md` in the goal and the journal: name it, so that a
   chain of runs does not double the term *)
Ltac sra_absmd :=
  repeat match goal with |- context [with_vm_backing ?l ?m ?d] =>
    let mdv := fresh "mdv" in set (mdv := with_vm_backing l m d) in *; clearbody mdv end.
(* a frame of a run keeps every byte outside the windows; each window lies in Zs *)
Ltac sra_kept Hfr Zs Usp AW44 AW34 :=
  intros ?a ?Ha ?Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ Zs Hfr); [| assumption | assumption];
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi a' Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr;
     try rewrite Usp in Hrr; try rewrite AW44 in Hrr; try rewrite AW34 in Hrr; cbv beta; lia |]);
  destruct Hin.
(* a live block lies above 4096 and below alloc_ceiling *)
Lemma sra_bl : forall ly S (W : world SEGS) mem md p k, AR SEGS B ly S W mem md -> In (p, k) (ablocks B ly S) ->
  0 <= p /\ p + k <= alloc_ceiling /\ 4096 <= p /\ p + req_size k <= alloc_ceiling.
Proof.
intros ly S W mem md p k HAR Hin. destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (Hp16 & Hp4096 & Hpceil & _ & _ & _ & Hk).
pose proof (req_size_pos k ltac:(unfold MALLOC_MAX in Hk; lia)) as [_ Hreq]. lia.
Qed.
Lemma nodup_app_disj : forall (l1 l2 : list (Z * Z)) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros l1 l2 x H H1 H2. apply list_relations.list.NoDup_app in H as (_ & H & _).
apply (H x); apply list_elem_of_In; assumption.
Qed.
(* the recorder's blocks less the spill's arguments *)
Lemma nodup_app_r : forall (l1 l2 : list (Z * Z)), NoDup (l1 ++ l2) -> NoDup l2.
Proof. intros l1 l2 H. apply list_relations.list.NoDup_app in H as (_ & _ & H). exact H. Qed.
Lemma sra_O1 : forall (A L C D O : list (Z * Z)), NoDup (A ++ L ++ C ++ D) -> (forall pn, In pn O <-> In pn (A ++ L ++ C ++ D)) ->
  forall pn, In pn (A ++ C ++ D) <-> In pn O /\ ~ In pn L.
Proof.
intros A L C D O Hnd HO pn. pose proof (nodup_app_r A _ Hnd) as Hnd2. rewrite HO. rewrite !in_app_iff. split.
- intros [H|[H|H]].
  + split; [left; exact H|]. intros HL. apply (nodup_app_disj A (L ++ C ++ D) pn Hnd H). apply in_or_app. left. exact HL.
  + split; [right; right; left; exact H|]. intros HL.
    apply (nodup_app_disj L (C ++ D) pn Hnd2 HL). apply in_or_app. left. exact H.
  + split; [right; right; right; exact H|]. intros HL.
    apply (nodup_app_disj L (C ++ D) pn Hnd2 HL). apply in_or_app. right. exact H.
- intros [[H|[H|[H|H]]] Hn]; [left; exact H | exact (False_ind _ (Hn H)) | right; left; exact H | right; right; exact H].
Qed.
Theorem tsup_remove_all_specF_holds : tsup_remove_all_specF B MT.
Proof.
unfold tsup_remove_all_specF.
intros ly S W regs mem md ch R O. cbv zeta.
intros HPRE HFRM HFR HROD HRO HREP HEV HLIVE HMO.
set (t := snd (sup_remove_all_m R)) in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : SUP_REMOVE_ALL_STK = ltac:(let v := eval vm_compute in SUP_REMOVE_ALL_STK in exact v)) by reflexivity.
assert (Hsp32 : alloc_ceiling + 16500 <= spZ regs) by (rewrite WS in Hslo; lia).
assert (Hsp47 : spZ regs <= 2 ^ 47) by lia.
(* the recorder's ncalls *)
pose proof HREP as (Q & HAQ & HOQ).
pose proof HAQ as (_ & _ & _ & (Hlen16 & _ & Hnc & _) & _).
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn : 0 <= n <= 16) by (subst n; lia).
(* the entry state *)
destruct (sra_entry B LAWS HB TL VOBJS PRW W ly S regs mem md ch n HPRE Hn Hnc) as [HS SHOK].
pose proof (ajournal_init SEGS B SUP_REMOVE_ALL_STK (sra_FP O) ly S W regs mem md ch HPRE) as HJ.
pose proof (sra_slot_range n Hn) as (Hc8 & HcPG & HcPG16 & Hc0 & Hc1 & Hcase).
assert (V42 : VAL (A_OBJ 42) = 0x21ce0) by (rewrite (VOBJS 42%nat ltac:(vm_compute; lia)); reflexivity).
assert (V44 : VAL (A_OBJ 44) = A_G_REC) by (rewrite (VOBJS 44%nat ltac:(vm_compute; lia)); reflexivity).
assert (V51 : VAL (A_OBJ 51) = A_REC_SPILL) by (rewrite (VOBJS 51%nat ltac:(vm_compute; lia)); reflexivity).
assert (EL : forall k, (k < A_TEXT)%nat -> ew (sra_E regs n) k = ew (Ereg regs (sra_extra n)) k)
  by (intros k Hk; unfold sra_E; apply Eimg_low; exact Hk).
assert (HED : ed (sra_E regs n) = ed (Ereg regs (sra_extra n))) by reflexivity.
assert (HEI : img_env VAL A_LIM (sra_E regs n)) by (unfold sra_E; apply Eimg_env).
remember (sra_E regs n) as E eqn:HE.
assert (EEo : forall k (rr : bv 5), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 sra_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (sra_slot n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EOBJ' : forall i v, (13 <= i < 100)%nat -> VAL (A_OBJ i) = v -> 0 <= v < 2 ^ 64 -> ew E (A_OBJ i) = Z_to_bv 64 v).
{ intros i v Hi Hv Hr. apply bv_eq. rewrite (HEI (A_OBJ i) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), Hv.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (E283 : ew E (A_OBJ 42) = Z_to_bv 64 0x21ce0) by (apply EOBJ'; [lia | exact V42 | lia]).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC) by (apply EOBJ'; [lia | exact V44 | unfold A_G_REC; lia]).
assert (E292 : ew E (A_OBJ 51) = Z_to_bv 64 A_REC_SPILL) by (apply EOBJ'; [lia | exact V51 | unfold A_REC_SPILL; lia]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (AW44 : bv_unsigned (ew E (A_OBJ 44)) = A_G_REC) by (rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (AW285 : bv_unsigned (ew E 285%nat) = A_G_REC) by exact AW44.
assert (AW34 : bv_unsigned (ew E 34) = sra_slot n) by (rewrite E34; apply unsigned_lit_small; lia).
assert (AW241 : bv_unsigned (ew E 241%nat) = 0xa63f0).
{ change 241%nat with (A_OBJ 0). rewrite (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (VOBJS 0%nat ltac:(vm_compute; lia)). reflexivity. }
assert (AW253 : bv_unsigned (ew E 253%nat) = 0xb10b8).
{ change 253%nat with (A_OBJ 12). rewrite (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (VOBJS 12%nat ltac:(vm_compute; lia)). reflexivity. }
assert (HAE : env_agree 32 (Ereg regs (sra_extra n)) E).
{ split; [intros k Hk; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED.
(* the footprint covers every static byte the walk writes *)
assert (FPn : forall a, A_G_REC + 8 <= a < A_G_REC + 12 -> inFP (sra_FP O) a /\ inFP cmd_PG a).
{ intros a Ha. split.
  - exists (A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4). split; [left; reflexivity | unfold OFF_NCALLS; cbn [fst snd]; lia].
  - exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC in *; lia]. }
assert (FPs : forall a, sra_slot n <= a < sra_slot n + 8 -> inFP (sra_FP O) a /\ inFP cmd_PG a).
{ intros a Ha. split; [|replace a with (sra_slot n + (a - sra_slot n)) by lia; apply HcPG16; lia].
  destruct Hcase as [(Hl & Hcv) | (Hl & Hcv)]; rewrite Hcv in Ha.
  - exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8). split; [right; left; reflexivity|].
    unfold OFF_CALLS, OFF_ANSWER, CALL_SIZE in *; cbn [fst snd]; lia.
  - exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; right; right; left; reflexivity|].
    unfold SC_SIZE; cbn [fst snd]; lia. }
unfold cfg_at, w64.
(* 0x8ac44 .. 0x8ac70: the frame, the shadow base, g_rec.ncalls, and the branch on n = 16 *)
paj_run_tok RUN HS HJ SHOK sra_Bspan.
{ sra_awr WS Usp AW44 AW34 FPn FPs. }
sra_absmd.
psrr_branch_tok RUN BR HS SHOK sra_Bspan.
- (* n <> 16: the append arm, 0x8ac8c .. 0x8aca4 store ncalls + 1 and compute the slot *)
  assert (Hnl : n < 16).
  { rewrite branch_ne_U in Hc. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc.
    rewrite (U_atom E 33 n E33) in Hc by lia. rewrite U_lit in Hc by lia. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK sra_Bspan 0x47c4.
  { sra_awr WS Usp AW44 AW34 FPn FPs. }
  sra_absmd.
  (* 0x8aca8: s0 is the slot, atom 34 *)
  assert (HP8 : sv_denot E (SOff 34 0) = sv_denot E sra_s0_append).
  { rewrite (sra_pin_append E n E33 ltac:(lia) E285). cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
    unfold sra_slot. rewrite (proj2 (Z.ltb_lt n 16) Hnl). reflexivity. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    assert (HP8' : sv_denot E (SOff 34 0) = sv_denot E (sr_get (ss_regs ss) 8%bv))
      by (replace (sr_get (ss_regs ss) 8%bv) with sra_s0_append by (vm_compute; reflexivity); exact HP8) end.
  pose proof (st_ok_pi_set_reg E _ _ 8%bv (SOff 34 0) HS HP8' eq_refl) as HS2.
  clear HS HP8 HP8'. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?m => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
  (* the slot's region: c->fn and c->nargs, written below *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    assert (HD : all_disjoint E sra_slot_region (ss_mem ss))
      by (cbn [ss_mem all_disjoint]; unfold extent_disjoint, sra_slot_region;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite ?Usp, ?AW285, ?AW34, ?AW241, ?AW253; rewrite WS in *;
          destruct Hcase as [(_ & Hcv) | (Hl & _)]; [|lia]; rewrite Hcv;
          unfold A_G_REC, OFF_CALLS, CALL_SIZE in *; repeat split; lia) end.
  pose proof (sra_add_slot B LAWS HB PRW W E _ _ ly S _ n HS (proj1 HJ) Hn E34 HD) as HS2.
  clear HS HD. rename HS2 into HS.
  pose proof (sra_shok B LAWS HB ly S W _ _ E n (proj1 HJ) Hn E32 E34) as SHOK2. clear SHOK.
  (* 0x8aca8 .. 0x8acf8: the two checked stores, the frame released, `j answer` *)
  paj_run_tok RUN HS HJ SHOK2 sra_Bspan.
  { sra_awr WS Usp AW44 AW34 FPn FPs. }
  sra_absmd.
  (* at answer's entry: the registers *)
  pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs (sra_extra n) HS HAE ltac:(vm_compute; reflexivity)) as HPT.
  cbn [ms_regs restrict] in HPT.
  prreg HS (1%bv : bv 5) T1. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  (* the bytes record() wrote: ncalls = n + 1, c->fn = 3, c->nargs = 0 *)
  assert (VN : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (A_G_REC + 8) 4 (n + 1)).
  { refine (st_chunk_val SEGS E _ (restrict (w_H W) ms1) 4%nat _ (A_OBJ 44) 8 4%N (SOff 33 1) A_G_REC (n + 1) HS eq_refl eq_refl _ AW44 _ _ _).
    - cbn. repeat (first [left; reflexivity | right]).
    - cbn [sv_denot]. rewrite E33. rewrite unsigned_lit_small by lia. reflexivity.
    - lia. - lia. }
  assert (VF : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (sra_slot n + 0) 4 3).
  { refine (st_chunk_val SEGS E _ (restrict (w_H W) ms1) 0%nat _ 34 0 4%N (SLit 3) (sra_slot n) 3 HS eq_refl eq_refl _ AW34 _ _ _).
    - cbn. repeat (first [left; reflexivity | right]).
    - reflexivity. - lia. - lia. }
  assert (VA : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (sra_slot n + 4) 4 0).
  { refine (st_chunk_val SEGS E _ (restrict (w_H W) ms1) 0%nat _ 34 4 4%N (SLit 0) (sra_slot n) 0 HS eq_refl eq_refl _ AW34 _ _ _).
    - cbn. repeat (first [left; reflexivity | right]).
    - reflexivity. - lia. - lia. }
  (* every other byte below the stack is the entry's *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12) \/ (sra_slot n <= a < sra_slot n + 8)) ->
    rdW W (ms_mem ms1) a = rdW W mem a).
  { intros a Ha Hz.
    assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
      ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12) \/ (sra_slot n <= a < sra_slot n + 8)) ->
      rdW W (ms_mem ms) a = rdW W mem a)
      by sra_kept HFr (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12) \/ (sra_slot n <= a < sra_slot n + 8)) Usp AW285 AW34.
    assert (K2 : forall a, 0 <= a < 2 ^ 64 ->
      ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12) \/ (sra_slot n <= a < sra_slot n + 8)) ->
      rdW W (ms_mem ms0) a = rdW W (ms_mem ms) a)
      by sra_kept HFr0 (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12) \/ (sra_slot n <= a < sra_slot n + 8)) Usp AW285 AW34.
    assert (K3 : forall a, 0 <= a < 2 ^ 64 ->
      ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12) \/ (sra_slot n <= a < sra_slot n + 8)) ->
      rdW W (ms_mem ms1) a = rdW W (ms_mem ms0) a)
      by sra_kept HFr1 (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12) \/ (sra_slot n <= a < sra_slot n + 8)) Usp AW285 AW34.
    rewrite (K3 a Ha Hz), (K2 a Ha Hz). exact (K1 a Ha Hz). }
  assert (KLIM : forall a, 0 <= a < alloc_ceiling -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
    ~ (A_G_REC + OFF_CALLS + CALL_SIZE * n <= a < A_G_REC + OFF_CALLS + CALL_SIZE * n + 8) ->
    rdW W (ms_mem ms1) a = rdW W mem a).
  { intros a Ha Hn1 Hn2. destruct Hcase as [(_ & Hcv) | (Hl & _)]; [|lia].
    apply KEEP; [lia|]. rewrite Hcv. unfold OFF_NCALLS, OFF_CALLS, CALL_SIZE in *. lia. }
  (* the recorder after record(): the new call in slot n *)
  assert (BL : forall p k, In (p, k) (ablocks B ly S) -> 0 <= p /\ p + k <= alloc_ceiling).
  { intros p k Hin. destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hin) as (Hp16 & Hp4096 & Hpceil & _ & _ & _ & Hk).
    pose proof (req_size_pos k ltac:(unfold MALLOC_MAX in Hk; lia)) as [_ Hreq]. lia. }
  assert (Hnl' : (length (r_calls R) < 16)%nat) by (unfold n in Hnl; lia).
  destruct Hcase as [(_ & Hcv) | (Hl & _)]; [|lia].
  rewrite Hcv in VF, VA.
  assert (HAQ' := arep_append (ablocks B ly S) alloc_ceiling BL ltac:(unfold A_REC_SPILL, SC_SIZE; lia)
    (rdW W mem) (rdW W (ms_mem ms1)) R Q HAQ Hnl' KLIM).
  cbv zeta in HAQ'. specialize (HAQ' (aval_mem_of_val_mem SEGS _ _ _ _ _ VN)).
  specialize (HAQ' (aval_mem_of_val_mem SEGS _ _ _ _ _ VF)).
  specialize (HAQ' (aval_mem_of_val_mem SEGS _ _ _ _ _ VA)).
  assert (HREPT : rec_repA B ly S (rdW W (ms_mem ms1)) (rec_record R REC_REMOVE_ALL []) O).
  { exists (RLay (l_calls Q ++ [[]]) (l_spill Q) (l_answer Q) (l_reply Q)). split; [exact HAQ'|].
    intros pn. rewrite (lay_blocks_append Q pn). exact (HOQ pn). }
  (* the tail jump: answer runs at the entry's sp *)
  pmkst HS.
  rewrite (SIGP CS_answer ltac:(unfold cmd_prog_syms; simpl; repeat (first [left; reflexivity | right]))).
  replace (cmd_af CS_answer) with AF_answer by (vm_compute; reflexivity).
  change (ew E 283%nat) with (ew E (A_OBJ 42)) in T11.
  eapply (TAILH ly S W regs mem md ch R O ly S W (ms_mem ms1) mdv1 (ms_regs ms1) 0 [] O (sra_slot n));
  [ exact HPRE | exact HFRM | exact HFR | exact HROD | exact HREP | exact HEV | exact HLIVE | exact HMO
  | exact HJ | unfold rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ 16) Hnl'); reflexivity
  | rewrite app_nil_r; apply Permutation_refl | intros pn [] | intros pn; tauto
  | rewrite Z.mul_0_l; exact (mle_start MT S MTL)
  | exact HREPT
  | left; exists (length (r_calls R)); split; [exact (proj1 (rec_record_append_nth R Hnl')) | rewrite Hcv; reflexivity]
  | rewrite Hcv; unfold A_G_REC, OFF_CALLS, CALL_SIZE in *; lia
  | exact HPT | rewrite T1, E1; reflexivity | rewrite T10, E34; reflexivity | rewrite T11, E283; reflexivity
  | rewrite T12; reflexivity ].
- (* n = 16: the spill arm, 0x8ac74 .. 0x8ac84 s0 := &record.spill and the call rec_calls_free(&record.spill, 1) *)
  assert (Hn16 : n = 16).
  { rewrite branch_ne_U in Hc. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
    rewrite (U_atom E 33 n E33) in Hc by lia. rewrite U_lit in Hc by lia. exact Hc. }
  assert (HlenR : length (r_calls R) = 16%nat) by (unfold n in Hn16; lia).
  assert (HcS : sra_slot n = A_REC_SPILL) by (unfold sra_slot; rewrite Hn16; reflexivity).
  paj_run_tok RUN HS HJ SHOK sra_Bspan.
  { sra_awr WS Usp AW44 AW34 FPn FPs. }
  sra_absmd.
  (* the state at the call *)
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  change (ew E 292%nat) with (ew E (A_OBJ 51)) in P8, P10. rewrite E292 in P8, P10.
  assert (HspC : spZ (ms_regs ms0) = spZ regs + -32).
  { unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (VNc : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (A_G_REC + 8) 4 n).
  { refine (st_chunk_val SEGS E _ (restrict (w_H W) ms0) 3%nat _ (A_OBJ 44) 8 4%N (SOff 33 0) A_G_REC n HS eq_refl eq_refl _ AW44 _ _ _).
    - cbn. repeat (first [left; reflexivity | right]).
    - cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - lia. - lia. }
  (* every byte below the stack is the entry's: the runs wrote only the frame; ncalls still holds n *)
  assert (KEEPc : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms0) a = rdW W mem a).
  { intros a Ha.
    destruct (Z_le_gt_dec (A_G_REC + 8) a) as [Hl|Hl]; [destruct (Z_lt_le_dec a (A_G_REC + 12)) as [Hh|Hh]|].
    - pose proof (aval_mem_of_val_mem SEGS _ _ _ _ _ VNc (Z.to_nat (a - (A_G_REC + 8))) ltac:(lia)) as V1.
      pose proof (Hnc (Z.to_nat (a - (A_G_REC + 8))) ltac:(lia)) as V2.
      rewrite Z2Nat.id in V1, V2 by lia. replace (A_G_REC + 8 + (a - (A_G_REC + 8))) with a in V1 by lia.
      unfold OFF_NCALLS in V2. replace (A_G_REC + 8 + (a - (A_G_REC + 8))) with a in V2 by lia.
      rewrite V1, V2. reflexivity.
    - assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) ->
        rdW W (ms_mem ms) a = rdW W mem a)
        by sra_kept HFr (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) Usp AW285 AW34.
      assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) ->
        rdW W (ms_mem ms0) a = rdW W (ms_mem ms) a)
        by sra_kept HFr0 (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) Usp AW285 AW34.
      rewrite K2 by (rewrite ?WS; lia). rewrite K1 by (rewrite ?WS; lia). reflexivity.
    - assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) ->
        rdW W (ms_mem ms) a = rdW W mem a)
        by sra_kept HFr (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) Usp AW285 AW34.
      assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) ->
        rdW W (ms_mem ms0) a = rdW W (ms_mem ms) a)
        by sra_kept HFr0 (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) Usp AW285 AW34.
      rewrite K2 by (rewrite ?WS; lia). rewrite K1 by (rewrite ?WS; lia). reflexivity. }
  assert (BL : forall p k, In (p, k) (ablocks B ly S) -> 0 <= p /\ p + k <= alloc_ceiling)
    by (intros p k Hin; pose proof (sra_bl ly S W mem md p k HAR Hin); lia).
  assert (HAQc := arep_kept (ablocks B ly S) alloc_ceiling BL ltac:(unfold A_REC_SPILL, SC_SIZE; lia)
    (rdW W mem) (rdW W (ms_mem ms0)) R Q HAQ KEEPc).
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms0))).
  { intros a Hro Ho He. assert (Himg : in_img SEGS a) by (destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (CmdRecRo.RRO SEGS B LAWS HB IMG a Hr)]).
    pose proof (Hsegs a Himg). rewrite KEEPc by lia. exact (HROD a Hro Ho He). }
  (* the spill's call before the call *)
  pose proof HAQc as (_ & _ & _ & (_ & _ & _ & _ & HSP & _) & _ & _ & _ & (HND & _)).
  set (PS := l_spill Q) in *.
  pose proof HSP as (_ & Hl6 & HlenP & _ & Hnav & HndP & Hargs).
  assert (PSbl : forall pn, In pn PS -> In pn (ablocks B ly S)).
  { intros pn Hin. destruct (In_nth_error _ _ Hin) as [k Hk].
    assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- HlenP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
    exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))). }
  assert (PSO : forall pn, In pn PS -> In pn O).
  { intros pn Hin. apply HOQ. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hin. }
  assert (Hsf : rec_spill_frees R = Z.of_nat (length PS)).
  { unfold rec_spill_frees. rewrite HlenR. cbn. rewrite HlenP. reflexivity. }
  assert (HEVA : EV_ANSWER = ltac:(let v := eval vm_compute in EV_ANSWER in exact v)) by reflexivity.
  assert (HXA : 0 <= XM_ANSWER MT t).
  { unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
    pose proof (mo_free_nonneg MT MTL). pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
  assert (FP1lo : forall a, inFP (rcf_fp A_REC_SPILL [PS]) a -> 0 <= a < alloc_ceiling /\
    ((A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) \/ exists p k, In (p, k) PS /\ p <= a < p + req_size k)).
  { intros a (r & Hr & Ha). unfold rcf_fp in Hr. apply in_app_iff in Hr as [Hr | Hr].
    - cbn in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold CALL_SIZE, CALL_OFF_NARGS in Ha.
      split; [unfold A_REC_SPILL in *; lia | left; lia].
    - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p k] & <- & Hin). cbn [concat] in Hin. rewrite app_nil_r in Hin.
      cbn [fst snd] in Ha. pose proof (sra_bl ly S W mem md p k HAR (PSbl _ Hin)) as Hb.
      split; [lia | right; exists p, k; split; [exact Hin | lia]]. }
  pmkst HS.
  rewrite (SIGP CS_rec_calls_free ltac:(unfold cmd_prog_syms; simpl; repeat (first [left; reflexivity | right]))).
  replace (cmd_af CS_rec_calls_free) with AF_rec_calls_free by (vm_compute; reflexivity).
  assert (HAS : ASTACK = 16384) by reflexivity.
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W (ms_regs ms0) (ms_mem ms0) _ SUP_REMOVE_ALL_STK (spZ regs) (sra_FP O) ly S W mem md [] ly S mdv0 0
      REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [PS]) (EV_REC_CALLS_FREE [PS]) (-32) (Z_to_bv 64 (BASE + 18340)) []).
    - exact HJ.
    - exact HspC.
    - reflexivity.
    - lia.
    - unfold REC_CALLS_FREE_STK. lia.
    - rewrite WS. unfold REC_CALLS_FREE_STK. lia.
    - rewrite P3, E3. exact Hgp.
    - rewrite P4, E4. exact Htp.
    - exact P1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - (* the frame chain at the call: s0 = &record.spill lies below alloc_ceiling, the empty chain *)
      apply achain_low. unfold s0Z. rewrite P8. rewrite unsigned_lit_small by (unfold A_REC_SPILL; lia). unfold A_REC_SPILL. lia.
    - intros Hpre'. eapply SRr_mono.
      + apply (TREC_CALLS_FREE fx ly S W (ms_regs ms0) (ms_mem ms0) mdv0 [] A_REC_SPILL [PS]).
        * exact Hpre'.
        * exact HRODc.
        * exact P10.
        * rewrite P11. reflexivity.
        * cbn. lia.
        * right. left. unfold CALL_SIZE, SC_SIZE. cbn. lia.
        * (* the table pointer is 8-aligned: record.spill at 0x5e3be0 *)
          unfold A_REC_SPILL. reflexivity.
        * intros i P' Hi. destruct i as [|i]; [|destruct i; discriminate Hi]. cbn in Hi. injection Hi as <-.
          split; [rewrite HlenP; exact Hl6|]. split.
          { replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS) by lia.
            rewrite HlenP. exact Hnav. }
          intros a pn Ha.
          assert (Ha' : (a < length (snd (r_spill R)))%nat) by (rewrite <- HlenP; apply nth_error_Some; rewrite Ha; discriminate).
          destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
          destruct (Hargs a s pn Hs Ha) as (G1 & _ & G3 & _).
          split; [|exact G3]. replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat a)
            with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat a) by lia. exact G1.
        * cbn [concat]. rewrite app_nil_r. exact HndP.
        * unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r. unfold EV_SUP_REMOVE_ALL in HEV. rewrite HEVA in HEV. lia.
        * apply (mo_ok_le MT MTL S _ (XM_SUP_REMOVE_ALL MT R t) HMO). unfold XM_REC_CALLS_FREE, XM_SUP_REMOVE_ALL.
          cbn [concat]. rewrite app_nil_r. rewrite Hsf. lia.
      + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & HQ2).
        exists ly2, S2, regs2, mem2, md2. rewrite P1 in Hc2. split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HP2|].
        exact HQ2.
    - intros a Hfp. destruct (FP1lo a Hfp) as (Ha & [Hs | (p & k & Hin & Hpk)]).
      + right; right; right; right. left. split.
        * exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; right; right; left; reflexivity | unfold SC_SIZE; cbn [fst snd]; lia].
        * assert (Hpg : inFP cmd_PG a) by (exists (A_REC_SPILL, A_REC_SPILL + 56); split; [right; left; reflexivity | cbn [fst snd]; lia]).
          split; [exact (HPROG B HB a Hpg) | exact (CmdRecBase.cif_prog_img _ _ IMG a Hpg)].
      + right. left. split.
        * exists (p, p + req_size k). split; [|cbn [fst snd]; lia]. right; right; right; right.
          unfold ablocks_fp. apply in_map_iff. exists (p, k). split; [reflexivity | exact (PSO _ Hin)].
        * exists p, k. split; [exact (PSbl _ Hin) | exact Hpk].
    - intros ly2 S2 W2 regs2 mem2 md2 _ a Hfp Hw _. destruct (FP1lo a Hfp) as (Ha & _). exfalso. rewrite WS in Hw. lia. }
  clear SHOK. cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP2 & HK2).
  (* back at 0x8ac88 *)
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
  match type of HS2 with ?T -> _ => assert (HRK : T); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _ & _ & _ & _ & Gpres & _).
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
    - apply (mbyte_of_aview SEGS). apply G1; [unfold REC_CALLS_FREE_STK; lia | unfold REC_CALLS_FREE_STK; lia |].
      intros Hfp. destruct (FP1lo a Hfp) as (Hb & _). lia.
    - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite WS. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  assert (A44 : ew (havoc E 40 (map (getr regs2) CLOB)) 44 = getr regs2 10) by reflexivity.
  remember (havoc E 40 (map (getr regs2) CLOB)) as Ec eqn:HEc.
  assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDc : forall k, (k < 40)%nat -> ew Ec k = ew E k) by (intros k Hk; rewrite HEc; apply YN3v.ew_havoc_old; exact Hk).
  assert (HAEc : env_agree 32 (Ereg regs (sra_extra n)) Ec).
  { destruct HAE as [HA1 HA2]. split; [intros k Hk; rewrite OLDc by lia; exact (HA1 k Hk) | rewrite HEc; exact HA2]. }
  assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact Usp).
  assert (Ec34 : ew Ec 34 = Z_to_bv 64 (sra_slot n)) by (rewrite OLDc by lia; exact E34).
  assert (Ec1 : ew Ec 1 = getr regs 1) by (rewrite OLDc by lia; exact E1).
  assert (Ec283 : ew Ec (A_OBJ 42) = Z_to_bv 64 0x21ce0).
  { change (A_OBJ 42) with 283%nat. rewrite HEc, ew_havoc_above by (cbv; lia). exact E283. }
  assert (AW34c : bv_unsigned (ew Ec 34) = sra_slot n) by (rewrite Ec34; apply unsigned_lit_small; lia).
  clear HEc.
  (* 0x8aca8: s0 is record.spill, atom 34 *)
  assert (HP8 : sv_denot Ec (SOff 34 0) = sv_denot Ec (SOff 292 0)).
  { cbn [sv_denot]. rewrite Ec34, !Z.add_0_r, Z_to_bv_bv_unsigned.
    change 292%nat with (A_OBJ 51). rewrite (HEIc (A_OBJ 51) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V51, HcS. reflexivity. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    assert (HP8' : sv_denot Ec (SOff 34 0) = sv_denot Ec (sr_get (ss_regs ss) 8%bv))
      by (replace (sr_get (ss_regs ss) 8%bv) with (SOff 292 0) by (vm_compute; reflexivity); exact HP8) end.
  pose proof (st_ok_pi_set_reg Ec _ _ 8%bv (SOff 34 0) HS HP8' eq_refl) as HS3.
  clear HS HP8 HP8'. rename HS3 into HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?m => let ss' := eval vm_compute in ss in change ss with ss' in HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    assert (HD : all_disjoint Ec sra_slot_region (ss_mem ss))
      by (cbn [ss_mem all_disjoint]; unfold extent_disjoint, sra_slot_region;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          rewrite ?Uspc, ?AW34c, HcS; rewrite WS in *;
          unfold A_REC_SPILL in *; repeat split; lia) end.
  pose proof (sra_add_slot B LAWS HB PRW W2 Ec _ _ ly2 S2 _ n HS (proj1 HJ1) Hn Ec34 HD) as HS3.
  clear HS HD. rename HS3 into HS.
  pose proof (sra_shok B LAWS HB ly2 S2 W2 _ _ Ec n (proj1 HJ1) Hn ltac:(rewrite OLDc by lia; exact E32) Ec34) as SHOKc.
  (* 0x8aca8 .. 0x8acf8 again *)
  paj_run_tok RUN HS HJ2 SHOKc sra_Bspan.
  { sra_awr WS Uspc AW34c AW34c FPn FPs. }
  sra_absmd.
  (* at answer's entry *)
  pose proof (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs (sra_extra n) HS HAEc ltac:(vm_compute; reflexivity)) as HPT.
  cbn [ms_regs restrict] in HPT.
  prreg HS (1%bv : bv 5) T1. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  assert (VF : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (sra_slot n + 0) 4 3).
  { refine (st_chunk_val SEGS Ec _ (restrict (w_H W2) ms1) 0%nat _ 34 0 4%N (SLit 3) (sra_slot n) 3 HS eq_refl eq_refl _ AW34c _ _ _).
    - cbn. repeat (first [left; reflexivity | right]).
    - reflexivity. - lia. - lia. }
  assert (VA : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (sra_slot n + 4) 4 0).
  { refine (st_chunk_val SEGS Ec _ (restrict (w_H W2) ms1) 0%nat _ 34 4 4%N (SLit 0) (sra_slot n) 0 HS eq_refl eq_refl _ AW34c _ _ _).
    - cbn. repeat (first [left; reflexivity | right]).
    - reflexivity. - lia. - lia. }
  assert (KEEP3 : forall a, 0 <= a < alloc_ceiling -> ~ (A_REC_SPILL <= a < A_REC_SPILL + 8) ->
    rdW W2 (ms_mem ms1) a = rdW W2 mem2 a).
  { intros a Ha Hs.
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 32 <= a < spZ regs) \/ (sra_slot n <= a < sra_slot n + 8)) ->
      rdW W2 (ms_mem ms1) a = rdW W2 mem2 a)
      by sra_kept HFr1 (fun a => (spZ regs - 32 <= a < spZ regs) \/ (sra_slot n <= a < sra_slot n + 8)) Uspc AW34c AW34c.
    apply K3; [lia | rewrite HcS; unfold A_REC_SPILL in *; lia]. }
  (* the recorder after rec_calls_free and the two stores *)
  destruct HK2 as (HPerm2 & _ & _ & _ & _ & HrepS & _ & _ & MLE1).
  specialize (HrepS R Q HAQc eq_refl eq_refl).
  pose proof (proj1 HJ1) as HAR2.
  assert (BL2 : forall p k, In (p, k) (ablocks B ly2 S2) -> 0 <= p /\ p + k <= alloc_ceiling)
    by (intros p k Hin; pose proof (sra_bl ly2 S2 W2 mem2 md2 p k HAR2 Hin); lia).
  destruct HrepS as (Q1 & HAQ1 & HOQ1).
  assert (Hsp0 : snd (r_spill (set_spill R (fst (r_spill R), []))) = []) by reflexivity.
  assert (VF2 : aval_mem (rdW W2 (ms_mem ms1)) (A_REC_SPILL + CALL_OFF_FN) 4 REC_REMOVE_ALL).
  { rewrite <- HcS. exact (aval_mem_of_val_mem SEGS _ _ _ _ _ VF). }
  assert (VA2 : aval_mem (rdW W2 (ms_mem ms1)) (A_REC_SPILL + CALL_OFF_NARGS) 4 0).
  { rewrite <- HcS. exact (aval_mem_of_val_mem SEGS _ _ _ _ _ VA). }
  assert (HAQ2 := arep_spill_set (ablocks B ly2 S2) alloc_ceiling BL2 ltac:(unfold A_REC_SPILL, SC_SIZE; lia)
    (rdW W2 mem2) (rdW W2 (ms_mem ms1)) _ Q1 HAQ1 Hsp0 KEEP3 VF2 VA2).
  rewrite <- (rec_record_full R ltac:(lia)) in HAQ2.
  (* the recorder's blocks less the spill's arguments *)
  set (O1 := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) in *.
  assert (HO1 : forall pn, In pn O1 <-> In pn O /\ ~ In pn PS).
  { intros pn. unfold O1. split.
    - intros Hin. split.
      + apply HOQ. unfold lay_blocks. apply in_app_iff in Hin as [H|H]; apply in_or_app;
        [left; exact H | right; apply in_or_app; right; exact H].
      + intros Hs. apply (RecStep.nodup_fst_mid (concat (l_calls Q)) PS (oblk (l_answer Q) ++ oblk (l_reply Q)) pn pn);
        [first [exact HND | unfold lay_blocks in HND; exact HND] | exact Hin | exact Hs | reflexivity].
    - intros [Hin Hs]. apply HOQ in Hin. unfold lay_blocks in Hin.
      apply in_app_iff in Hin as [H|H]; [apply in_or_app; left; exact H|].
      apply in_app_iff in H as [H|H]; [contradiction | apply in_or_app; right; exact H]. }
  (* the tail jump *)
  pmkst HS.
  rewrite (SIGP CS_answer ltac:(unfold cmd_prog_syms; simpl; repeat (first [left; reflexivity | right]))).
  replace (cmd_af CS_answer) with AF_answer by (vm_compute; reflexivity).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  exact (TAILH ly S W regs mem md ch R O ly2 S2 W2 mT dT rT (rec_spill_frees R) PS O1 (sra_slot n)
    HPRE HFRM HFR HROD HREP HEV HLIVE HMO
    ltac:(rewrite Hsf; unfold EV_REC_CALLS_FREE in HJ2; cbn [concat] in HJ2; rewrite app_nil_r in HJ2; exact HJ2)
    eq_refl
    ltac:(cbn [concat] in HPerm2; rewrite app_nil_r in HPerm2; exact HPerm2)
    PSO HO1
    ltac:(rewrite Hsf; unfold XM_REC_CALLS_FREE in MLE1; cbn [concat] in MLE1; rewrite app_nil_r in MLE1;
          first [exact MLE1 | rewrite Z.mul_comm; exact MLE1])
    ltac:(exists Q1; split; [exact HAQ2 | exact HOQ1])
    ltac:(right; split; [exact HcS | rewrite (rec_record_full R ltac:(lia)); reflexivity])
    ltac:(rewrite HcS; unfold A_REC_SPILL; lia)
    HPT ltac:(rewrite T1, Ec1; reflexivity) ltac:(rewrite T10, Ec34; reflexivity)
    ltac:(rewrite T11; change (ew Ec 283%nat) with (ew Ec (A_OBJ 42)); rewrite Ec283; reflexivity)
    ltac:(rewrite T12; reflexivity)) end.
Qed.
(* the statement as sup_remove_all_c.v states it: sra_FP and sra_post unfold to its footprint and post-condition *)
Theorem tsup_remove_all_spec_holds : tsup_remove_all_spec B MT.
Proof. exact tsup_remove_all_specF_holds. Qed.
End e.
End f.
End d.
Print Assumptions tsup_remove_all_specF_holds.
Print Assumptions tsup_remove_all_spec_holds.
