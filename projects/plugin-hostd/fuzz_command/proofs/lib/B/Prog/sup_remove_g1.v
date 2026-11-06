(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the entry segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0 ..
   0x8a61c), in the form of sup_resp's walk (cgif lib/A/AChf.v, flushFrame): the prologue, the realignment
   `andi sp,sp,-32`, the use-after-return flag (1: `beqz a2` falls through), the class-7 side-stack frame of
   __asan_stack_malloc_7 (not 0: `bnez s2` skips the real-stack fallback), the frame's header and shadow, the two
   shadow fills, up to the BODY cut (answer_s1.v AN_BODY_stmt). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_e.v, with its module paths, module names and numbers changed; 564 of its 744 lines of code are new or changed and 415 lines of the source are left out. *)
(* sup_remove's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan,
   BASE + AF_sup_remove = 0x8b258), segment G1: from the entry to record()'s return 0x8b354 (SR_R), where
   sr_g2_stmt (sup_remove_s1.v) takes over.

   0x8b258 .. 0x8b28c: the 96-byte frame (`sd zero,0(sp)`, the ten saves ra, s0 .. s8 at sp0 - 8 .. sp0 - 80),
     s0 := sp0, sp := (sp0 - 96) & -32 =: sp1 (sr_sp1; atom 40 here).
   0x8b290 .. 0x8b2b8: s1 := sp1, the GOT loads (the shadow base through A_OBJ 0 and the shadow cell A_OBJ 12; the
     use-after-return flag through A_OBJ 1, the record's constant cell 1, AR_const_law), s3 := id, `beqz a2` falls
     through, a0 := 64, the call of __asan_stack_malloc_0 (class 0, 64 bytes: aj_stack_malloc_atS).
   0x8b2bc .. 0x8b350: s2 = s7 := F (the frame, atom 52; not 0, so `bnez s2` skips the real-stack fallback),
     sp1 + 8 := F, s4 := F + 32, the header F + 0, + 8, + 16, s6 := SB + F / 8 (atom 64), the frame's shadow bytes
     f1 f1 f1 f1 f8 f8 f3 f3, a0 := 2 and the call of record (PaCallPg.v's cl_callS_pg, record_c.v's contract at
     the entry's FP state: record writes g_rec's ncalls and slot, so the footprint rule is the program-static one).
   At record's return the cut (sr_cut, sr_recd) is built from the journals and the symbolic state at the call, and
   the walk ends in sr_g2_stmt.

   The walk tactics and the entry state follow sup_resp's A walk (an earlier version of
   lib/A/Prog/sup_resp_s1.v and sup_resp.v:128-360); the block lemmas follow the B walk of sup_remove_all
   (lib/B/Prog/sup_remove_all_s1.v, _s4.v). Record's frame chain is achain_push on afn_pre's chain (s0 = sp0, the
   saved ra and s0 at sp0 - 8 and sp0 - 16), or the empty chain when sp0 is within 16 bytes of the stack top.

   Hypotheses the proof uses: the statement's TRECORD and ASTACK_MALLOC0 (TARG_S, TANSWER, ASNPRINTF and VOBJS are
   copied but not used here), G2 (sr_g2_stmt), and the walk hypotheses HB, LAWS, TL, TLF, ML, SMP, MTL, MTFL, IMG,
   SIGP. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRo xmalloc_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText CmdRecAns sup_remove_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the walk tactics (sup_resp's A walk, lib/A/Prog/sup_resp_s1.v:34-202, cgif's ACkc.v) ---- *)
Ltac sr_g1_rnHEI E := lazymatch goal with H : img_env _ _ E |- _ => H | _ => fail "sr_g1_rnHEI: no img_env fact for" E end.
Ltac sr_g1_hei_pose Eo kk ws :=
let Ho := sr_g1_rnHEI Eo in let H := fresh "HEIh" in
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as H | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as H ].
Ltac sr_g1_hei_havoc HS :=
lazymatch type of HS with
| st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ => first [ let H0 := sr_g1_rnHEI constr:(havoc Eo kk ws) in idtac | sr_g1_hei_pose Eo kk ws ]
| _ => idtac end.
Ltac sr_g1_nat_side := first [ apply (proj1 (PeanoNat.Nat.ltb_lt _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.eqb_neq _ _)); vm_compute; reflexivity
| apply (proj1 (PeanoNat.Nat.leb_le _ _)); vm_compute; reflexivity ].
Ltac sr_g1_evalE AG :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
repeat match goal with |- context [ew Ev ?n] => lazymatch (eval cbv in (Nat.ltb n 32)) with true => rewrite (AG n) by lia end end end;
repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
repeat match goal with H : bv_unsigned (ew ?Ex 2) = _ |- context [bv_unsigned (ew ?Ex 2)] => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia); unfold SB; first [reflexivity | lia | idtac].
Ltac sr_g1_rebaseE HS AG HEv :=
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
let HEIv := fresh "HEI" in
lazymatch type of HEv with
| _ = havoc ?Eo ?kk ?ws => lazymatch goal with Ho : img_env ?val ?lim Eo |- _ =>
first [ pose proof (img_env_havoc_hi Eo kk ws Ho ltac:(cbv; lia)) as HEIv | pose proof (img_env_havoc Eo kk ws Ho ltac:(cbv; lia)) as HEIv ];
rewrite <- HEv in HEIv end
| _ = ?En => try (lazymatch goal with Hn : img_env _ _ En |- _ => rewrite <- HEv in Hn end) end;
repeat match goal with H : img_env _ _ (ewset _ _ _) |- _ => clear H end;
assert (AG2 : forall n, (n < 32)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; apply AG; exact Hnn);
try (lazymatch goal with AD : ed ?Eo = ed E0 |- _ =>
  let AD2 := fresh "AD" in assert (AD2 : ed Ev = ed E0) by (rewrite HEv; exact AD); clear AD; rename AD2 into AD end);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 32 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by sr_g1_nat_side; rewrite ?ew_ewset_other, ?ew_havoc_old, ?ew_havoc_above by sr_g1_nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.
Ltac sr_g1_subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac sr_g1_submem_to := repeat (first [apply submem_keep; [sr_g1_subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac sr_g1_rreg_by HS r v pf H :=
lazymatch type of HS with st_ok_pi _ ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg _ Hh Ex _ ms r HS) _); change (sv_denot Ex e = v); exact pf) end.
Ltac sr_g1_norm_ssp HS := lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
Ltac sr_g1_idx_of_base rs n :=
lazymatch rs with
| YP09.mkRegion (Some n) _ _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := sr_g1_idx_of_base tl n in constr:(S i)
end.
Definition sr_g1_chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition sr_g1_trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (sr_g1_chunk_in lo hi) (YP09.r_chunks r)).
Fixpoint sr_g1_trim_stack (rs : smem) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some 2%nat => sr_g1_trim_region r lo hi :: t
| _ => r :: sr_g1_trim_stack t lo hi end end.

(* the write windows of a run, one goal per window with its range evaluated (for kept_of_frame) *)
Ltac sr_g1_win AG :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hr;
lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; revert Hr; sr_g1_evalE AG; intros Hr | ]);
try (destruct Hin).
(* an 8-byte word read through a reader that agrees on its bytes *)
Lemma sr_g1_rdword_kept : forall (rd rd' : reader) a v,
  (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk H. rewrite (rdword_ext rd rd' a Hk). exact H. Qed.

(* sup_remove's footprint lies below alloc_ceiling (the B sup_remove_all walk's sra_fp_bound, over sr_FP) *)
Lemma sr_g1_fp_bound {rc : YM05.RunCeil} : forall O, (forall p n, In (p, n) O -> 4096 <= p /\ p + req_size n <= alloc_ceiling) ->
  forall a, inFP (sr_FP O) a -> 4096 <= a < alloc_ceiling.
Proof.
intros O HO a Ha. pose proof asan_consts as (C1 & _).
unfold sr_FP in Ha. rewrite !inFP_cons in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | Ha]]]];
  [unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, SC_SIZE in Ha; lia ..|].
destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr). destruct (HO p n Hin). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- the symbolic entry state (sup_resp's sr_entry, lib/A/Prog/sup_resp_s1.v:209-307): the 96-byte frame below
   the entry sp, the shadow GOT word and cell, the use-after-return GOT word and flag ---- *)
Definition sr_g1_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition sr_g1_regions0 : smem :=
[ stack_region 96; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition sr_g1_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0x10000 0x606000 2) ].
Definition ss_sr_g1 : sstate := mkSS AF_sup_remove sr_atoms sr_g1_regions0 None (mkFacts sr_g1_atoms0 [] []).
Definition sr_g1_extra (uar : Z) : list word := map (Z_to_bv 64) [SB; uar].

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_remove_c.v:88-93) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the rest of the walk, from record's return (sup_remove_s1.v) *)
Hypothesis G2 : sr_g2_stmt B MT.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Let RUN := paj_run (fx := fx) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (fx := fx) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNP := SRr_run_pi_AJ (fx := fx) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) (PL := PL_cmd) (PI := PI) B LAWS.
Let errno_low := pal_env (PI := PI) B TL.

Lemma sr_g1_entry : forall W ly S regs mem md ch,
afn_pre SEGS B SUP_REMOVE_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (sr_g1_extra (as_uar_cell B)))) ss_sr_g1
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_remove)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : SUP_REMOVE_STK = 16704) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (sr_g1_extra (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_sr_g1. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sr_g1_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
  [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB 33%nat (as_uar_cell B) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
unfold sr_g1_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob1 Hob12 Huar Hsep. clear.
unfold ASAN_CEIL. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok sr_g1_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E33.
rewrite !unsigned_lit_small by (unfold SB in *; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
Qed.

(* the recorder's blocks are live *)
Lemma sr_g1_rep_live : forall ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HQ & HO) Hin. exact (rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HO pn) Hin)). Qed.

(* record's footprint for record(REC_REMOVE) lies in sup_remove's: g_rec.ncalls and the slot's first 8 bytes are
   program statics (g_rec's call table or record.spill), the spill arm's freed blocks are the recorder's live blocks
   (the B sup_remove_all walk's sra_rec_fp_cover) *)
Lemma sr_g1_rec_fp_cover : forall ly S rd R O, rec_repA B ly S rd R O ->
  forall a, inFP (rca_recFP R O) a -> inFP (sr_FP O) a /\
  ((exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
   (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a)).
Proof.
intros ly S rd R O HREP a Ha. unfold rca_recFP in Ha. rewrite !inFP_cons in Ha.
destruct Ha as [Ha | [Ha | Ha]].
- split.
  + unfold sr_FP. rewrite !inFP_cons. left. exact Ha.
  + right. apply (rca_prog (PI := PI) B HB IMG). exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
    unfold OFF_NCALLS in Ha. cbn [fst snd]. lia.
- unfold rec_slot in Ha. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl | Hl].
  + split.
    * unfold sr_FP. rewrite !inFP_cons. right; left. unfold OFF_CALLS, OFF_ANSWER, CALL_SIZE in *. lia.
    * right. apply (rca_prog (PI := PI) B HB IMG). exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|].
      unfold OFF_CALLS, CALL_SIZE, A_G_REC in *. cbn [fst snd]. lia.
  + split.
    * unfold sr_FP. rewrite !inFP_cons. right; right; right; left. unfold SC_SIZE. lia.
    * right. apply (rca_prog (PI := PI) B HB IMG). exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity|].
      cbn [fst snd]. lia.
- destruct (Nat.ltb (length (r_calls R)) 16); [destruct Ha as (r & [] & _)|].
  destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr). split.
  + unfold sr_FP. rewrite !inFP_cons. right; right; right; right. exact Ha.
  + left. exists p, n. split; [exact (sr_g1_rep_live ly S rd R O _ HREP Hin) | exact Hr].
Qed.

Theorem sr_g1 : tsup_remove_spec B MT.
Proof.
intros ly S W regs mem md ch id R O t HPRE HFRM HFR HROD HRO H10 Hid HREP HEV HLIVE HMO.
assert (HSRP : sr_pre B MT ly S W regs mem md ch id R O)
  by exact (conj HPRE (conj HFR (conj HROD (conj HRO (conj H10 (conj Hid (conj HREP (conj HEV (conj HLIVE HMO))))))))).
pose proof (@pa_wx _ cmd_listing PI) as Hwx. pose proof (@pa_segs_low _ cmd_listing PI) as Hsegs.
pose proof (@pa_B_ok _ cmd_listing PI) as HBASE. pose proof (pa_base_lo (PL := PL_cmd) (PI := PI)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : SUP_REMOVE_STK = 16704) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HRS : RECORD_STK = 16560) by reflexivity.
pose proof (proj1 errno_low) as [Herr0 Herr1].
assert (HOlive : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hp; exact (sr_g1_rep_live ly S _ R O pn HREP Hp)).
assert (HOF : Forall (fun pn => In pn (ablocks B ly S)) O) by (apply Forall_forall; exact HOlive).
pose proof (sr_g1_entry W ly S regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B SUP_REMOVE_STK (sr_FP O) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (sr_g1_extra (as_uar_cell B)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (apply EE; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EE; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EE; reflexivity).
assert (E8 : ew E 8 = getr regs 8) by (apply EE; reflexivity).
assert (E9 : ew E 9 = getr regs 9) by (apply EE; reflexivity).
assert (E10 : ew E 10 = getr regs 10) by (apply EE; reflexivity).
assert (E18 : ew E 18 = getr regs 18) by (apply EE; reflexivity).
assert (E19 : ew E 19 = getr regs 19) by (apply EE; reflexivity).
assert (E20 : ew E 20 = getr regs 20) by (apply EE; reflexivity).
assert (E21 : ew E 21 = getr regs 21) by (apply EE; reflexivity).
assert (E22 : ew E 22 = getr regs 22) by (apply EE; reflexivity).
assert (E23 : ew E 23 = getr regs 23) by (apply EE; reflexivity).
assert (E24 : ew E 24 = getr regs 24) by (apply EE; reflexivity).
assert (E25 : ew E 25 = getr regs 25) by (apply EE; reflexivity).
assert (E26 : ew E 26 = getr regs 26) by (apply EE; reflexivity).
assert (E27 : ew E 27 = getr regs 27) by (apply EE; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (sr_g1_extra (as_uar_cell B))) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar.
clear HE EE.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (AG : forall n, (n < 32)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (AD : ed E = ed E) by reflexivity.
unfold cfg_at. change (w64 (BASE + AF_sup_remove)) with (Z_to_bv 64 (BASE + AF_sup_remove)).
(* 0x8b258 .. 0x8b28c: the 96-byte frame, the saves, s0 := sp0, sp := (sp0 - 96) & -32 *)
paj_run_to_tok RUNTO HS HJ SHOK sr_g1_Bspan 0x4d60.
{ awr_ok_tac. exact Usp. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem) (mrestrict _ _) |- _ => rename HFx into HFr1 end.
lazymatch type of HFr1 with frame_of _ _ _ (mrestrict _ (ms_mem ?msx)) => rename msx into msA end.
repeat match goal with H : frame_of _ _ mem _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
collapse_md.
(* the run wrote the frame only: every byte below alloc_ceiling is the entry's *)
assert (KEEP1 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem msA) a = rdW W mem a).
{ intros a Ha. apply (kept_of_frame E _ (w_H W) mem (ms_mem msA) (fun x => alloc_ceiling <= x) HFr1); [| lia | cbv beta; lia].
  sr_g1_win AG. all: lia. }
clear HFr1.
(* the realigned stack pointer sp1 becomes atom 40; the frame keeps its top 80 bytes (the saves), and sp1's own
   slot sp1 + 8 (0x8b2ec `sd s7,8(s1)`) is a region of its own *)
set (sp1 := 32 * ((spZ regs + -96) / 32)).
destruct (snt_sp1_facts (spZ regs + -96) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16). fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by lia. clear Hsp1r.
assert (Esp1 : sr_sp1 (spZ regs) = sp1) by reflexivity.
sr_g1_rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1)
  (snt_denot_and_m32 E 2 (spZ regs) (-96) ltac:(rewrite E2; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) R2.
pose proof (st_ok_pi_havoc_hi 40 E _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3.
sr_g1_hei_pose E 40%nat [Z_to_bv 64 sp1].
clear HS. rename HS3 into HS. sr_g1_rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E40 : ew Ev 40 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 40 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 40 0) HS ltac:(vm_compute; reflexivity)
  ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E40, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
sr_g1_norm_ssp HS. clear R2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
pose proof (st_ok_pi_add_fact Ev ssx msx 40%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E40, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (sr_g1_trim_stack rs (-80) 0) in
pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; sr_g1_submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
sr_g1_norm_ssp HS.
assert (VO : forall Ev n, img_env VAL A_LIM Ev -> (A_TEXT <= n < A_LIM)%nat -> bv_unsigned (ew Ev n) = VAL n)
  by (intros Ev n HEv Hn; exact (HEv n Hn)).
change (A_OBJ 0) with 241%nat in Hob0. change (A_OBJ 1) with 242%nat in Hob1. change (A_OBJ 12) with 253%nat in Hob12.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HEv := sr_g1_rnHEI Ev in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 40%nat) 8 16 8 16 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    rewrite E40, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite FFS; lia)
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite ?(VO Ev 241%nat HEv), ?(VO Ev 242%nat HEv), ?(VO Ev 253%nat HEv) by (unfold A_TEXT, A_LIM; lia);
    sr_g1_evalE AG; rewrite ?E40, ?unsigned_lit_small by lia;
    repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
sr_g1_norm_ssp HS. clear HJpres.
(* 0x8b290 .. 0x8b2b8: s1 := sp1, the GOT loads (the shadow base; the use-after-return flag, 1), s3 := id, `beqz a2`
   falls through, a0 := 64, the call of __asan_stack_malloc_0 *)
resh HS.
paj_run_tok RUN HS HJ SHOK sr_g1_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E' ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb E' rs' stk sp0 fp b0 bc fr ly own) end.
  eapply awr_ok_cons_stack_off with (n := 40%nat) (d := sp1 - spZ regs);
    [reflexivity | rewrite E40, unsigned_lit_small by lia; lia | cbn [YP09.r_wlo]; rewrite FFS; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | rewrite (AG 2%nat) by lia; exact Usp | cbn [YP09.r_wlo]; rewrite FFS; lia | cbn [YP09.r_whi]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]). apply awr_ok_nil. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem msA)) (mrestrict _ _) |- _ => rename HFx into HFr2 end.
lazymatch type of HFr2 with frame_of _ _ _ (mrestrict _ (ms_mem ?msx)) => rename msx into msB end.
repeat match goal with H : frame_of _ _ (ms_mem msA) _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
assert (KEEP2 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem msB) a = rdW W (ms_mem msA) a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H W) (ms_mem msA) (ms_mem msB) (fun x => alloc_ceiling <= x) HFr2); [| lia | cbv beta; lia].
  sr_g1_win AG. all: lia. }
clear HFr2.
pmkst HS. collapse_md.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
(* the call of __asan_stack_malloc_0 (sup_resp's, A sup_resp.v:225-243) *)
pose proof (palf_sm B TLF 0 ltac:(cbn; tauto)) as HSM0. change (cs_stack_malloc 0) with CS___asan_stack_malloc_0 in HSM0.
rewrite HSM0.
pose proof (count_cid_le_length 0 (frames S)) as Hcnt.
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS (fx := fx) SEGS B LAWS Hsegs errno_low ML SMP 0 (ASTACK_MALLOC0 fx) ltac:(lia) W (ms_regs msB) (ms_mem msB)
    SUP_REMOVE_STK (spZ regs) (sr_FP O) ly S W mem md [] ly S _ 0 (sp1 - spZ regs) _ HJ).
  - unfold spZ at 1. rewrite R2, E40, unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - rewrite FFS, Hes; lia.
  - rewrite R3, (AG 3%nat), E3 by lia. exact Hgp.
  - rewrite R4, (AG 4%nat), E4 by lia. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - change (fs_frames 0) with 16384. lia. }
cbv beta. clear R1 R2 R3 R4.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hzsh & Hflag & HK & HJ1 & (fS2 & ES2)).
rewrite Hes in HK.
(* back at 0x8b2bc: the slot sp1 + 8 and the saves are kept (both above sp1) *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?T -> _ => assert (HRK : T); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  pose proof HK as (K1 & _).
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
   rewrite ?E40, ?(AG 2%nat), ?Usp, ?unsigned_lit_small by lia; intros a Ha;
   [ apply (mbyte_of_aview SEGS); apply K1; lia
   | intros _; apply (apresent_writable SEGS); apply Hpres2; rewrite FFS; lia ]). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
sr_g1_hei_havoc HS. sr_g1_rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E52 : ew Ev 52 = getr regs2 10) by (rewrite HEv; reflexivity) end.
clear HEv.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
rewrite Ha0 in E52. unfold w64 in E52.
(* the frame F (atom 52) and its shadow SB + F / 8 (atom 64): the header [F, F + 24) and the 8 shadow bytes as write
   windows with no chunks (the stores at 0x8b318 .. 0x8b348) *)
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 64 Ev ssv msv [Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3;
sr_g1_hei_pose Ev 64%nat [Z_to_bv 64 (SB + F / 8)] end.
clear HS. rename HS3 into HS. sr_g1_rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E64 : ew Ev 64 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 64 [Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 52 (HPTR 5) HS
  ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E52, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 64 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E64, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
    split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 52 32 64 F SB E52 ltac:(lia) E32 E64)) as HS3;
clear HS; rename HS3 into HS end.
sr_g1_norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 64 0 0 8 []) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    change (fs_frame_bytes 0 / 8) with 8; rewrite E64, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
      apply (proj1 (HFSpres o ltac:(change (64 / 8) with 8; lia)))
    | apply Forall_nil ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    change (fs_frame_bytes 0 / 8) with 8; rewrite E64, E40; sr_g1_evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi; unfold SB; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
sr_g1_norm_ssp HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 52%nat) 0 24 0 24 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
    rewrite E52, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite E52, E64, E40; sr_g1_evalE AG;
    clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF8lo HF8hi HF4096 HFceil HFhigh HFq HF8; unfold SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
sr_g1_norm_ssp HS.
clear SHOK.
(* 0x8b2bc .. 0x8b350: s2 = s7 := F (not 0: `bnez s2` skips the real-stack fallback), sp1 + 8 := F, s4 := F + 32,
   the header, s6 := SB + F / 8, the shadow f1 f1 f1 f1 f8 f8 f3 f3, a0 := 2, the call of record *)
paj_run_shc RUNP RUNC HS HJ2.
{ let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; sr_g1_evalE AG;
      rewrite ?E52, ?E64, ?E40, ?unsigned_lit_small by (unfold SB; lia); intros Hr;
      first [ exfalso; clear - Hr; lia
            | left; rewrite FFS; lia
            | right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
              first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; lia
                    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8;
                      fold F; unfold SB in *; lia ] ] | ]);
  destruct Hin. }
lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem2) (mrestrict _ _) |- _ => rename HFx into HFr3 end.
lazymatch type of HFr3 with frame_of _ _ _ (mrestrict _ (ms_mem ?msx)) => rename msx into msT end.
repeat match goal with H : frame_of _ _ mem2 _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS. collapse_md.
(* the run wrote the stack, the header [F, F + 24) and the frame's shadow only *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a \/ F <= a < F + 24 \/ SB + F / 8 <= a < SB + F / 8 + 8) ->
  rdW W (ms_mem msT) a = rdW W mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ (w_H W) mem2 (ms_mem msT) (fun x => alloc_ceiling <= x \/ F <= x < F + 24 \/ SB + F / 8 <= x < SB + F / 8 + 8) HFr3);
  [| exact Ha | exact Hn].
  sr_g1_win AG. all: unfold SB in *; lia. }
clear HFr3.
(* the state at record's call: the registers *)
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10.
prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26. prreg HS (27%bv : bv 5) T27.
assert (P1 : getr (ms_regs msT) 1 = Z_to_bv 64 (BASE + (AF_sup_remove + SR_R))) by (rewrite T1; reflexivity).
assert (P2 : spZ (ms_regs msT) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite T2, E40, unsigned_lit_small by lia; lia).
assert (P3 : getr (ms_regs msT) 3 = w64 (as_gp B)) by (rewrite T3, (AG 3%nat), E3 by lia; exact Hgp).
assert (P4 : getr (ms_regs msT) 4 = w64 (as_tp B)) by (rewrite T4, (AG 4%nat), E4 by lia; exact Htp).
assert (P8 : getr (ms_regs msT) 8 = getr regs 2) by (rewrite T8, (AG 2%nat), E2 by lia; reflexivity).
assert (P9 : getr (ms_regs msT) 9 = w64 sp1) by (rewrite T9, E40; reflexivity).
assert (P10 : getr (ms_regs msT) 10 = w64 REC_REMOVE) by (rewrite T10; reflexivity).
assert (P18 : getr (ms_regs msT) 18 = w64 F) by (rewrite T18, E52; reflexivity).
assert (P19 : getr (ms_regs msT) 19 = getr regs 10) by (rewrite T19, (AG 10%nat), E10 by lia; reflexivity).
assert (P20 : getr (ms_regs msT) 20 = w64 (F + 32)) by (rewrite T20, E52, unsigned_lit_small by lia; reflexivity).
assert (P22 : getr (ms_regs msT) 22 = w64 (SB + F / 8)) by (rewrite T22, E64; reflexivity).
assert (P23 : getr (ms_regs msT) 23 = w64 F) by (rewrite T23, E52; reflexivity).
assert (P24 : getr (ms_regs msT) 24 = Z_to_bv 64 (-8)) by (rewrite T24; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
assert (P25 : getr (ms_regs msT) 25 = getr regs 25) by (rewrite T25, (AG 25%nat), E25 by lia; reflexivity).
assert (P26 : getr (ms_regs msT) 26 = getr regs 26) by (rewrite T26, (AG 26%nat), E26 by lia; reflexivity).
assert (P27 : getr (ms_regs msT) 27 = getr regs 27) by (rewrite T27, (AG 27%nat), E27 by lia; reflexivity).
clear T1 T2 T3 T4 T8 T9 T10 T18 T19 T20 T22 T23 T24 T25 T26 T27.
(* the ten saves at sp0 - 8 .. sp0 - 80 (the stack region's chunks) *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rg := eval vm_compute in (nth 3 (ss_mem ssx) (stack_region 0)) in
  pose proof (st_ok_region_nth Ex ssx msx 3 rg HS ltac:(vm_compute; reflexivity)) as HRst;
  assert (UspT : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
cbn [ms_mem restrict] in HRst.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 1%nat), E1, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V1.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-16) 8 (SOff 8 0) (bv_unsigned (getr regs 8)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 8%nat), E8, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V8.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 9%nat), E9, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V9.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-32) 8 (SOff 18 0) (bv_unsigned (getr regs 18)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 18%nat), E18, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V18.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-40) 8 (SOff 19 0) (bv_unsigned (getr regs 19)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 19%nat), E19, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V19.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-48) 8 (SOff 20 0) (bv_unsigned (getr regs 20)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 20%nat), E20, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V20.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-56) 8 (SOff 21 0) (bv_unsigned (getr regs 21)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 21%nat), E21, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V21.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-64) 8 (SOff 22 0) (bv_unsigned (getr regs 22)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 22%nat), E22, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V22.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-72) 8 (SOff 23 0) (bv_unsigned (getr regs 23)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 23%nat), E23, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V23.
pose proof (field_of_region _ _ 2%nat (spZ regs) _ _ _ _ _ (-80) 8 (SOff 24 0) (bv_unsigned (getr regs 24)) HRst UspT
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite (AG 24%nat), E24, Z.add_0_r by lia; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V24.
clear HRst.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V1 (bv_unsigned_in_range _ _)) as D1.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V8 (bv_unsigned_in_range _ _)) as D8.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V9 (bv_unsigned_in_range _ _)) as D9.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V18 (bv_unsigned_in_range _ _)) as D18.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V19 (bv_unsigned_in_range _ _)) as D19.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V20 (bv_unsigned_in_range _ _)) as D20.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V21 (bv_unsigned_in_range _ _)) as D21.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V22 (bv_unsigned_in_range _ _)) as D22.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V23 (bv_unsigned_in_range _ _)) as D23.
pose proof (rdword_of_val_mem SEGS (w_H W) (ms_mem msT) _ _ V24 (bv_unsigned_in_range _ _)) as D24.
clear V1 V8 V9 V18 V19 V20 V21 V22 V23 V24.
(* the bytes at and above the entry sp are the entry's (the journal; the footprint lies below alloc_ceiling) *)
assert (HOb : forall p n, In (p, n) O -> 4096 <= p /\ p + req_size n <= alloc_ceiling).
{ intros p n Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HOlive _ Hin)) as (_ & H1 & H2 & _). lia. }
pose proof (sr_g1_fp_bound O HOb) as FPlow.
assert (KEEPhi : forall a, spZ regs <= a < 2 ^ 64 -> rdW W (ms_mem msT) a = rdW W mem a).
{ intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  apply F1; [lia | lia | intros Hf; pose proof (FPlow a Hf); lia]. }
(* record's frame chain: s0 = sp0, afn_pre's chain pushed at sp0 with the saved ra and s0 (class B), or the empty
   chain when sp0 is within 16 bytes of the stack top *)
assert (H8 : spZ regs mod 8 = 0).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as Dv. rewrite Hal16 in Dv. rewrite Dv.
  replace (16 * (spZ regs / 16) + 0) with ((2 * (spZ regs / 16)) * 8) by lia. apply Z_mod_mult. }
assert (Es0 : s0Z (ms_regs msT) = spZ regs) by (unfold s0Z; rewrite P8; reflexivity).
assert (HchT : exists ch1, achain ly (rdW W (ms_mem msT)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs msT)) ch1).
{ rewrite Es0. destruct (Z_lt_le_dec (spZ regs) (ly_top ly - 16)) as [Hlt | Hge].
  - exists ((spZ regs, raZ regs, s0Z regs) :: ch).
    apply (achain_push ly (rdW W mem) (rdW W (ms_mem msT)) (spZ regs) (s0Z regs) (raZ regs) ch (spZ regs + (sp1 - spZ regs)) Hch);
    [lia | exact KEEPhi | replace (spZ regs - 8) with (spZ regs + -8) by lia; exact D1
    | replace (spZ regs - 16) with (spZ regs + -16) by lia; exact D8 | exact Hra4 | lia | exact H8 | exact Hlt | lia].
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HchT as (ch1 & HchT).
(* record's pre: the read-only bytes (the journal), the recorder at the call (the runs and the side-stack entry
   wrote no byte of g_rec, record.spill or a live block), the events and the meter *)
pose proof (sr_aro_journal B HB LAWS IMG _ _ O ly S W mem md _ _ _ _ _ _ _ HAR HOF HJ2 HROD) as HRODT.
assert (KI : forall a, inFP cmd_PG a -> rdW W (ms_mem msT) a = rdW W mem a).
{ intros a Hpg. destruct (rca_prog (PI := PI) B HB IMG a Hpg) as [Hps Himg]. pose proof (Hsegs a Himg) as Ha.
  destruct (prog_static_sep B a (am_syms _ _ _ _ (proj1 HAR)) Hps) as (Hno & Hne & _).
  rewrite KEEP3; [| lia |].
  2: { intros [Hz | [Hz | Hz]]; [lia | | unfold SB in Hz; lia].
       exact (frm_img SEGS B LAWS ly S2 W mem2 md2 0 fpos a HAR2 Hfin2 ltac:(change (fs_frame_bytes 0) with 64; fold F; lia) Himg). }
  pose proof HK as (_ & _ & K3 & _).
  rewrite (K3 a Himg Hno Hne). rewrite KEEP2 by lia. apply KEEP1. lia. }
assert (KB : forall b n i, In (b, n) (ablocks B ly S) -> 0 <= i < req_size n -> rdW W (ms_mem msT) (b + i) = rdW W mem (b + i)).
{ intros b n i Hin Hi.
  destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hin) as (_ & Hb4 & Hbc & Hbapp & _).
  assert (Hin2 : In (b, n) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
  pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 b n 0 fpos HAR2 Hin2 Hfin2) as Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 0) with 64 in Hsep. fold F in Hsep.
  rewrite KEEP3; [| lia |].
  2: { intros [Hz | [Hz | Hz]]; [lia | lia |].
       exact (fshadow_not_app F 8 b (req_size n) (b + i) HFhi ltac:(lia) Hbapp ltac:(unfold SB in Hz; lia) ltac:(lia)). }
  pose proof HK as (_ & K2 & _).
  rewrite (K2 b n i Hin Hi (fun H => H)). rewrite KEEP2 by lia. apply KEEP1. lia. }
assert (HREPT : rec_repA B ly S2 (rdW W (ms_mem msT)) R O).
{ apply (rec_repA_kept B ly S (rdW W mem) ly S2 (rdW W (ms_mem msT)) R O HREP).
  - intros pn Hpn. rewrite Eab. exact (HOlive pn Hpn).
  - intros a [Ha | [Ha | Ha]].
    + apply KI. apply sr_inPG. left. unfold REC_SIZE in Ha. exact Ha.
    + apply KI. apply sr_inPG. right. unfold SC_SIZE in Ha. exact Ha.
    + destruct (inFP_ablocks_fp_inv O a Ha) as (p & n & Hin & Hr).
      replace a with (p + (a - p)) by lia. apply (KB p n); [exact (HOlive _ Hin) | lia]. }
assert (HEVR : st_nev S2 + EV_RECORD R <= EV_MAX).
{ rewrite Hnev2. assert (0 <= EV_ARG_S) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (0 <= EV_ANSWER) by (apply Z.leb_le; vm_compute; reflexivity). unfold EV_SUP_REMOVE in HEV. lia. }
assert (HMOR : mo_ok MT S2 (XM_RECORD MT R)).
{ rewrite ES2. apply (mo_ok_set_fs MT MTFL). apply (mo_ok_le MT MTL S _ (XM_SUP_REMOVE MT R id t) HMO).
  assert (XA : 0 <= XM_ARG_S MT (Some (dec id))).
  { unfold XM_ARG_S, xmalloc_c.XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold xmalloc_c.LIVE_XMALLOC. lia. }
  assert (XN : 0 <= XM_ANSWER MT t).
  { unfold XM_ANSWER, hand_back_c.XM_HAND_BACK, xmalloc_c.XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
    pose proof (mo_malloc_nonneg MT MTL (xmalloc_c.LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold xmalloc_c.LIVE_XMALLOC; lia)). lia. }
  unfold XM_SUP_REMOVE. lia. }
assert (Hal1 : (sp1 - spZ regs) mod 16 = 0) by (rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity).
(* 0x8b350: record(REC_REMOVE), record's contract at the entry's FP state (record keeps it, apost_base) *)
rewrite (SIGP CS_record ltac:(unfold cmd_prog_syms; simpl; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_record) with AF_record by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS_pg (fx := fx) (L := cmd_listing) (PI := PI) B LAWS W (ms_regs msT) (ms_mem msT) _ SUP_REMOVE_STK (spZ regs) (sr_FP O)
    ly S W mem md [(0, fpos)] ly S2 _ 0 RECORD_STK (rca_recFP R O) (EV_RECORD R) (sp1 - spZ regs)
    (Z_to_bv 64 (BASE + (AF_sup_remove + SR_R))) ch1).
  - exact HJ2.
  - exact P2.
  - exact Hal1.
  - lia.
  - rewrite HRS; lia.
  - rewrite HRS, FFS; lia.
  - exact P3.
  - exact P4.
  - exact P1.
  - apply ret_ok_codeptr_v; [unfold AF_sup_remove, SR_R; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold AF_sup_remove, SR_R; lia). unfold AF_sup_remove, SR_R. lia.
  - exact HchT.
  - intros Hpre'. eapply SRr_mono.
    + apply (TRECORD fx ly S2 W (ms_regs msT) (ms_mem msT) _ ch1 REC_REMOVE R O).
      * exact Hpre'.
      * exact HRODT.
      * exact P10.
      * unfold REC_REMOVE, REC_FN_COUNT. lia.
      * exact HREPT.
      * exact HEVR.
      * exact HMOR.
    + cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HJx & HPx & HQx).
      exists ly3, S3, regs3, mem3, md3. rewrite P1 in Hc3. split; [exact Hc3|]. split; [exact HJx|]. split; [exact HPx | exact HQx].
  - intros a Ha. left. exact (sr_g1_rec_fp_cover ly S2 _ R O HREPT a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJ3i & HP3 & HK3).
destruct HK3 as (Fr & O1 & G10 & GPerm & GLen & GFO & GREP & GO1 & GBB & GMLE).
(* back at 0x8b354 (SR_R): the cut *)
pose proof HJ3 as (HAR3 & Hly3 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR Hly3) as (_ & Efa3 & _).
assert (EF3 : frame_addr ly3 0 fpos = F) by exact (Efa3 0 fpos).
assert (EFL3 : flag_addr ly3 0 fpos = FL).
{ pose proof (Efa3 0 fpos) as Ee. unfold F, FL in *. unfold frame_addr, flag_addr in *. lia. }
assert (FP1c : forall a, inFP (rca_recFP R O) a -> (exists b n, In (b, n) (ablocks B ly S2) /\ b <= a < b + req_size n) \/
  (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a))
  by (intros a Ha; exact (proj2 (sr_g1_rec_fp_cover ly S2 _ R O HREPT a Ha))).
assert (FP1low : forall a, inFP (rca_recFP R O) a -> a < alloc_ceiling).
{ intros a Ha. destruct (FP1c a Ha) as [(b & n & Hb & Hr) | (_ & Himg)].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR2 Hb) as (_ & _ & Hc & _). lia.
  - pose proof (Hsegs a Himg). lia. }
assert (FP1noF : forall a, F <= a < F + 64 -> ~ inFP (rca_recFP R O) a).
{ intros a Ha Hf. destruct (FP1c a Hf) as [(b & n & Hb & Hr) | (_ & Himg)].
  - pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 b n 0 fpos HAR2 Hb Hfin2) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 0) with 64 in Hsep. fold F in Hsep. lia.
  - exact (frm_img SEGS B LAWS ly S2 W mem2 md2 0 fpos a HAR2 Hfin2 ltac:(change (fs_frame_bytes 0) with 64; fold F; lia) Himg). }
assert (KEEP4 : forall a, spZ regs + (sp1 - spZ regs) <= a < 2 ^ 64 -> rdW W3 mem3 a = rdW W (ms_mem msT) a).
{ intros a Ha. pose proof HJ3i as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
  apply F1; [lia | lia | intros Hf; pose proof (FP1low a Hf); lia]. }
assert (KEEPF : forall a, F <= a < F + 64 -> rdW W3 mem3 a = rdW W (ms_mem msT) a).
{ intros a Ha. pose proof HJ3i as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  apply (F4 0 fpos a Hfin2); [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; lia | exact (FP1noF a Ha)]. }
assert (HFLAG3 : rdword (rdW W3 mem3) (frame_addr ly3 0 fpos + 56) = Some (flag_addr ly3 0 fpos)).
{ rewrite EF3, EFL3. apply (sr_g1_rdword_kept (rdW W mem2)); [|replace (F + 56) with (F + 64 - 8) by lia; exact Hflag].
  intros k Hk. rewrite (KEEPF (F + 56 + k)) by lia. apply KEEP3; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg in HFhigh. unfold SB. lia. }
assert (SAVE : forall o v, -80 <= o <= -8 -> rdword (rdW W (ms_mem msT)) (spZ regs + o) = Some v ->
  rdword (rdW W3 mem3) (spZ regs + o) = Some v).
{ intros o v Ho H. apply (sr_g1_rdword_kept (rdW W (ms_mem msT))); [|exact H]. intros k Hk. apply KEEP4. lia. }
assert (HSAVES : sr_saves (rdW W3 mem3) (spZ regs) regs).
{ unfold sr_saves.
  split; [replace (spZ regs - 8) with (spZ regs + -8) by lia; exact (SAVE (-8) _ ltac:(lia) D1)|].
  split; [replace (spZ regs - 16) with (spZ regs + -16) by lia; exact (SAVE (-16) _ ltac:(lia) D8)|].
  split; [replace (spZ regs - 24) with (spZ regs + -24) by lia; exact (SAVE (-24) _ ltac:(lia) D9)|].
  split; [replace (spZ regs - 32) with (spZ regs + -32) by lia; exact (SAVE (-32) _ ltac:(lia) D18)|].
  split; [replace (spZ regs - 40) with (spZ regs + -40) by lia; exact (SAVE (-40) _ ltac:(lia) D19)|].
  split; [replace (spZ regs - 48) with (spZ regs + -48) by lia; exact (SAVE (-48) _ ltac:(lia) D20)|].
  split; [replace (spZ regs - 56) with (spZ regs + -56) by lia; exact (SAVE (-56) _ ltac:(lia) D21)|].
  split; [replace (spZ regs - 64) with (spZ regs + -64) by lia; exact (SAVE (-64) _ ltac:(lia) D22)|].
  split; [replace (spZ regs - 72) with (spZ regs + -72) by lia; exact (SAVE (-72) _ ltac:(lia) D23)|].
  replace (spZ regs - 80) with (spZ regs + -80) by lia; exact (SAVE (-80) _ ltac:(lia) D24). }
(* the registers at the cut: record keeps the callee-saved ones *)
assert (Q2 : getr regs3 2 = getr (ms_regs msT) 2) by exact (HP3 2 ltac:(unfold acallee_saved; lia)).
assert (Q3 : getr regs3 3 = getr (ms_regs msT) 3) by exact (HP3 3 ltac:(unfold acallee_saved; lia)).
assert (Q4 : getr regs3 4 = getr (ms_regs msT) 4) by exact (HP3 4 ltac:(unfold acallee_saved; lia)).
assert (Q8 : getr regs3 8 = getr (ms_regs msT) 8) by exact (HP3 8 ltac:(unfold acallee_saved; lia)).
assert (Q9 : getr regs3 9 = getr (ms_regs msT) 9) by exact (HP3 9 ltac:(unfold acallee_saved; lia)).
assert (Q18 : getr regs3 18 = getr (ms_regs msT) 18) by exact (HP3 18 ltac:(unfold acallee_saved; lia)).
assert (Q19 : getr regs3 19 = getr (ms_regs msT) 19) by exact (HP3 19 ltac:(unfold acallee_saved; lia)).
assert (Q20 : getr regs3 20 = getr (ms_regs msT) 20) by exact (HP3 20 ltac:(unfold acallee_saved; lia)).
assert (Q22 : getr regs3 22 = getr (ms_regs msT) 22) by exact (HP3 22 ltac:(unfold acallee_saved; lia)).
assert (Q23 : getr regs3 23 = getr (ms_regs msT) 23) by exact (HP3 23 ltac:(unfold acallee_saved; lia)).
assert (Q24 : getr regs3 24 = getr (ms_regs msT) 24) by exact (HP3 24 ltac:(unfold acallee_saved; lia)).
assert (Q25 : getr regs3 25 = getr (ms_regs msT) 25) by exact (HP3 25 ltac:(unfold acallee_saved; lia)).
assert (Q26 : getr regs3 26 = getr (ms_regs msT) 26) by exact (HP3 26 ltac:(unfold acallee_saved; lia)).
assert (Q27 : getr regs3 27 = getr (ms_regs msT) 27) by exact (HP3 27 ltac:(unfold acallee_saved; lia)).
assert (HCUT : sr_cut B ly S W regs mem md O ly3 S3 W3 regs3 mem3 md3 fpos (EV_RECORD R)).
{ split; [rewrite Z.add_0_l in HJ3; exact HJ3|].
  split; [exact HFLAG3|].
  split; [unfold spZ at 1; rewrite Q2; change (bv_unsigned (getr (ms_regs msT) 2)) with (spZ (ms_regs msT)); rewrite P2, Esp1; lia|].
  split; [rewrite Q8, P8; reflexivity|].
  split; [rewrite Q9, P9, Esp1; reflexivity|].
  split; [rewrite Q18, P18, EF3; reflexivity|].
  split; [rewrite Q19, P19; reflexivity|].
  split; [rewrite Q20, P20, EF3; reflexivity|].
  split; [rewrite Q22, P22, EF3; reflexivity|].
  split; [rewrite Q23, P23, EF3; reflexivity|].
  split; [rewrite Q24, P24; reflexivity|].
  split; [rewrite Q3, P3, Hgp; reflexivity|]. split; [rewrite Q4, P4, Htp; reflexivity|].
  split; [rewrite Q25, P25; reflexivity|]. split; [rewrite Q26, P26; reflexivity|]. split; [rewrite Q27, P27; reflexivity|].
  exact HSAVES. }
assert (HRECD : sr_recd B MT ly S ly3 S3 (rdW W3 mem3) R O Fr O1).
{ split; [rewrite <- Eab; exact GPerm|].
  split; [exact GLen|]. split; [exact GFO|]. split; [exact GREP|]. split; [exact GO1|].
  split; [rewrite <- Hbb2; exact GBB|].
  rewrite ES2 in GMLE. exact (mo_le_set_fs_l MT MTFL _ _ _ _ GMLE). }
exact (G2 ly S W regs mem md ch id R O ly3 S3 W3 regs3 mem3 md3 fpos Fr O1 HSRP HFRM HCUT HRECD G10).
Qed.
End e.
End f.
End d.
