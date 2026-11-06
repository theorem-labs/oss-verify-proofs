(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_broadcast (plugin-hostd/fuzz_command, 0x8afa0, 61
   instructions), proving tsup_broadcast_spec of sup_broadcast_c.v. Shape: cgif_file_fuzzer's cgif_close walk
   (A/ACh1.v..ACh8.v, AChc.v): the verified symbolic executor over the position-abstract listing, the two inline
   store4 checks removed by the slot's shadow entry (sup_broadcast_s5.v), the calls of rec_calls_free, arg_line and
   the tail jump to answer through the kit's cl_callS_wide, and the recorder's representation from
   sup_broadcast_s2.v. The head reads g_rec.ncalls and either records in the table's next slot (n < 16,
   sup_broadcast_s7.v) or frees the spill's arguments and records there (n = 16, sup_broadcast_s8.v); the recorder
   never holds more than 16 calls (CmdRep.v's ag1_calls).
   The per-binary facts are Section hypotheses under cgif's names (HB, LAWS, TL,
   MTL, PRW, IMG); the segment files carry the image facts they use under the names of the kit's cmd_img_facts
   fields and CmdRecFacts lemmas (cif_prog_img, cif_prog_not_ro, cif_relro_img, cmd_ro_in_img, cmd_ro_ok_of_aro),
   which this file discharges from IMG (CmdRecBase.v, CmdRecRo.v). VOBJS, SIGP and the callees' statements are the
   statement's own.
   Pass-4/5 re-fit: the callees' statements hold at every FP state (forall fx0) and are used
   at the entry's fx: rec_calls_free and arg_line keep the FP state (apost_base, kit rule cl_callS_wide), answer is
   the last step (sup_broadcast_s3.v's sb_tail, through PaFx.v's cl_callS_wideF), so the post is apost_baseF; the
   rounding-mode-0 premise HFRM goes down to sb_tail for answer's own premise. Statement pass 5 removed astack_pres:
   the walk no longer derives it for its callees. The frame chains the three calls' afn_pre ask come from the walk:
   at rec_calls_free and arg_line s0 = line (a heap pointer below alloc_ceiling, achain_low, the empty chain); at
   answer s0 is the entry s0 (sup_broadcast's own afn_pre chain, sup_broadcast_s3.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_broadcast.v, with its module paths and module names changed; 322 of its 351 lines of code are new or changed and 60 lines of the source are left out. *)
(* sup_remove's walk on the ASan build of plugin-hostd/fuzz_command, part A: the table-slot arm, from the entry to
   the join 0x8abbc (g_rec.ncalls := n + 1, c := g_rec + 16 + 56 n), then the join piece (sr_jl_stmt), the tail
   piece (sr_tail_stmt) and the post-condition's block bookkeeping (sr_post_of, sup_remove_q.v). The join piece and
   the tail piece are taken here in their stated forms (sup_remove_s1.v) and supplied in sup_remove.v.

   Statement passes 4 and 5: the arm takes the rounding-mode-0 premise HFRM
   and ends in apost_baseF; the join piece returns from arg_i at some fx1 (fxrel fx fx1), where the tail piece
   runs (rounding mode 0 by fxrel_frm0) and its apost_baseF at fx1 lifts to the arm's (srr_apost_baseF_lift).
   astack_pres is gone. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCallRun PaCall PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_remove_s1 sup_remove_r sup_remove_b sup_remove_q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the program's statics lie below 2^32 *)
Lemma srA_PG_low : forall a, inFP cmd_PG a -> 0 <= a < 2 ^ 32.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in *. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
(* a run's frame window: the stack window [sp - 32, sp) and g_rec.ncalls; the GOT word and the shadow cell are read
   only (empty windows) *)
Ltac srA_win Usp AW :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a' Hin Hrr; cbv beta; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin];
  [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?AW in Hrr; unfold OFF_NCALLS; lia|]);
destruct Hin.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma srA_aval_of_val_mem : forall (H : word -> bool) mem a (n : nat) v,
val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis JL : sr_jl_stmt B MT.
(* the tail piece at every FP state: the arm applies it at the fx1 that arg_i returned (inside the join piece) *)
Hypothesis TAIL : forall fx0 : YK11.FPState, @sr_tail_stmt fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a byte of a live block is no byte of the program's statics *)
Lemma srA_blk_PG : forall ly S (W : world SEGS) mem md p k a, AR SEGS B ly S W mem md -> In (p, k) (ablocks B ly S) ->
p <= a < p + req_size k -> ~ inFP cmd_PG a.
Proof. intros ly S W mem md p k a HAR Hin Ha Hpg. exact (blk_img SEGS B LAWS ly S W mem md p k a HAR Hin Ha (cif_prog_img a Hpg)). Qed.
(* a live block lies apart from a range of the program's statics *)
Lemma srA_apart_PG : forall ly S (W : world SEGS) mem md p k lo len, AR SEGS B ly S W mem md -> In (p, k) (ablocks B ly S) ->
1 <= k -> 0 < len -> (forall a, lo <= a < lo + len -> inFP cmd_PG a) -> iv_apart p k lo len.
Proof.
intros ly S W mem md p k lo len HAR Hin Hk Hl Hpg. unfold iv_apart.
destruct (Z_le_gt_dec (p + k) lo) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (lo + len) p) as [H'|H']; [right; exact H'|]. exfalso.
pose proof (req_size_pos k ltac:(lia)) as [_ Hr].
apply (srA_blk_PG ly S W mem md p k (Z.max p lo) HAR Hin); [lia | apply Hpg; lia].
Qed.

(* the initial regions' writes: the frame and g_rec.ncalls *)
Ltac sr_awr0 Usp E285 :=
change (ss_mem ss_sr0) with [stack_region 32; got_regionP; bcell_regionP 32; sr_nc_region];
apply (awr_ok_cons_stack SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat); [reflexivity | exact Usp | cbn; vm_compute; discriminate | cbn; lia |];
apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
apply (awr_ok_cons_prog B HB cif_prog_img _ _ _ _ _ _ _ _ _ _ _ (A_OBJ 44) A_G_REC);
[ reflexivity | rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi sr_nc_region] in Ha; split;
  [ exists (A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4); split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS; lia]
  | apply sr_inPG; unfold A_G_REC in *; lia ]
| apply awr_ok_nil ].


Lemma sr_arm_slot : forall ly S W (regs : bvmap 5 word) mem md ch (id : Z) (R : rstate) (O : list (Z * Z)),
let t := snd (sup_remove_m R id) in
afn_pre SEGS B SUP_REMOVE_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
cmd_ro_ok (rdW W mem) ->
getr regs 10 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_REMOVE R <= EV_MAX -> blocks_bytes S + LIVE_SUP_REMOVE id t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_REMOVE MT R id t) ->
(length (r_calls R) < 16)%nat ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_remove) regs mem md)
(apost_baseF SEGS B SUP_REMOVE_STK (sr_FP O) regs ly S W mem md (EV_SUP_REMOVE R) (sr_post B MT ly S O R id)).
Proof.
intros ly S W regs mem md ch id R O t HPRE HFRM Hfr8 HROD HRO H10 Hid HREP Hev Hlive MOK Hlt.
(* the table arm: record() frees nothing *)
assert (Hsf0 : rec_spill_frees R = 0) by (unfold rec_spill_frees; rewrite (proj2 (Nat.ltb_lt _ 16) Hlt); reflexivity).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_REMOVE_STK = 16592) by (vm_compute; reflexivity).
destruct HREP as (Q & HQ & HOQ).
destruct (sr_lay_live _ _ _ _ _ _ HQ) as [HND HLIVE].
assert (HOB : Forall (fun pn => In pn (ablocks B ly S)) O).
{ apply Forall_forall. intros pn Hpn. apply HLIVE. apply HOQ. exact Hpn. }
destruct (sr_ncalls _ _ _ _ _ _ HQ) as [Hnc Hn16].
set (n := length (r_calls R)) in *.
pose proof (sr_entry B HB LAWS TL VOBJS PRW W ly S regs mem md ch (Z.of_nat n) HPRE Hnc ltac:(lia)) as HS.
pose proof (ajournal_init SEGS B SUP_REMOVE_STK (sr_FP O) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (sr_extra (Z.of_nat n)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 id) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E sr_kN = Z_to_bv 64 (Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold sr_kN, A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC).
{ subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). reflexivity. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E8 : ew E 8 = getr regs 8) by (apply EEo; reflexivity).
assert (E9 : ew E 9 = getr regs 9) by (apply EEo; reflexivity).
assert (E18 : ew E 18 = getr regs 18) by (apply EEo; reflexivity).
assert (E33' : ew E 33%nat = Z_to_bv 64 (Z.of_nat n)) by exact E33.
assert (AW285 : bv_unsigned (ew E 285%nat) = A_G_REC).
{ assert (E285' : ew E 285%nat = Z_to_bv 64 A_G_REC) by exact E285.
  rewrite E285'. apply unsigned_lit_small. unfold A_G_REC. lia. }
assert (HAE : env_agree 32 (Ereg regs (sr_extra (Z.of_nat n))) E).
{ subst E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
clear HE EEo.
assert (SHOK : sh_ok SEGS sr_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK sr_Bspan.
{ sr_awr0 Usp E285. }
sr_fold_md.
psrr_branch_tok RUN BR HS SHOK sr_Bspan.
2: { exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 33 (Z.of_nat n) E33) in Hc by lia.
     rewrite U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
paj_run_to_tok RUNTO HS HJ SHOK sr_Bspan (AF_sup_remove + SR_J).
{ sr_awr0 Usp E285. }
sr_fold_md.
(* the state at the join: registers, the frame, ncalls = n + 1, and what the two runs kept *)
pmkst HS.
set (c := A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat n).
assert (Hcv : c = A_G_REC + 16 + 56 * Z.of_nat n) by reflexivity.
assert (Hsl : sr_slot c) by (left; exists (Z.of_nat n); split; [unfold REC_CALLS_MAX; lia | reflexivity]).
(* the registers: sp - 32, s0 = id, s1 = c, s2 = the shadow base, gp, tp and s3 .. s11 kept. The kept list is given
   explicitly: left as an evar, `vm_compute; reflexivity` on `forallb _ ?l = true` did not end in 1800 s. *)
pose proof (regs_kept_of_st_ok_pi E _ (restrict (w_H W) ms0) regs (sr_extra (Z.of_nat n))
  (map (Z_to_bv 5) [19; 20; 21; 22; 23; 24; 25; 26; 27]) HS HAE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (18%bv : bv 5) P18.
pose proof (st_ok_pi_restrict_reg (w_H W) E _ ms0 9%bv HS) as P9.
lazymatch type of P9 with _ = sv_denot E (sr_get (ss_regs ?ss) _) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) 9%bv) in change (sr_get (ss_regs ss) 9%bv) with e in P9 end.
rewrite denot_lit_U, U_SAlu, U_SAlu, U_SMd in P9.
rewrite (U_atom E 33 (Z.of_nat n) E33) in P9 by lia.
rewrite U_lit, U_lit in P9 by lia.
rewrite (U_atom E 285 A_G_REC E285) in P9 by (unfold A_G_REC; lia).
assert (P9' : getr (ms_regs ms0) 9 = w64 c).
{ rewrite P9. unfold w64. f_equal. cbn [zalu_raw zmd_raw].
  rewrite (zcanon_id (Z.of_nat n * 56)) by (unfold M64; lia).
  rewrite (zcanon_id (Z.of_nat n * 56 + 16)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64, A_G_REC; lia).
  rewrite Hcv. lia. }
clear P9.
assert (Hspj : spZ (ms_regs ms0) = spZ regs - 32).
{ unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by (rewrite WS in *; lia). lia. }
assert (H8j : getr (ms_regs ms0) 8 = getr regs 10) by (rewrite P8, E10; symmetry; exact H10).
assert (H18j : getr (ms_regs ms0) 18 = w64 SB) by (rewrite P18; exact E32).
assert (H3j : getr (ms_regs ms0) 3 = getr regs 3) by (rewrite P3; exact E3).
assert (H4j : getr (ms_regs ms0) 4 = getr regs 4) by (rewrite P4; exact E4).
assert (Hsj : forall r, 19 <= r <= 27 -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. apply KR. apply in_map. cbn [In]. lia. }
clear KR P2 P3 P4 P8 P18.
(* the frame (the entry ra, s0, s1, s2) and ncalls = n + 1 *)
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
  let rg0 := eval vm_compute in (nth 0 (ss_mem ss) sr_jslot) in
  let rg3 := eval vm_compute in (nth 3 (ss_mem ss) sr_jslot) in
  pose proof (st_ok_region_nth E _ (restrict (w_H W) ms0) 0 rg0 HS ltac:(vm_compute; reflexivity)) as HR0;
  pose proof (st_ok_region_nth E _ (restrict (w_H W) ms0) 3 rg3 HS ltac:(vm_compute; reflexivity)) as HR3 end.
cbn [ms_mem restrict] in HR0, HR3.
pose proof (field_of_region E _ 2%nat (spZ regs) _ _ _ _ _ (-32) 8 (SOff 18 0) (bv_unsigned (getr regs 18)) HR0 Usp
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite E18, Z.add_0_r; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V18.
pose proof (field_of_region E _ 2%nat (spZ regs) _ _ _ _ _ (-24) 8 (SOff 9 0) (bv_unsigned (getr regs 9)) HR0 Usp
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite E9, Z.add_0_r; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V9.
pose proof (field_of_region E _ 2%nat (spZ regs) _ _ _ _ _ (-16) 8 (SOff 8 0) (bv_unsigned (getr regs 8)) HR0 Usp
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite E8, Z.add_0_r; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V8.
pose proof (field_of_region E _ 2%nat (spZ regs) _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) HR0 Usp
  ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
  ltac:(cbn [sv_denot]; rewrite E1, Z.add_0_r; reflexivity) ltac:(apply bv_unsigned_in_range) ltac:(cbn; lia)) as V1.
pose proof (field_of_region E _ 285%nat A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) (Z.of_nat n + 1) HR3 AW285
  ltac:(cbn [In]; left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite E33', unsigned_lit_small by lia; reflexivity)
  ltac:(change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia) ltac:(cbn; lia)) as VNC.
change (N.to_nat 8) with 8%nat in V18, V9, V8, V1. change (N.to_nat 4) with 4%nat in VNC.
replace (spZ regs + -32) with (spZ regs - 32) in V18 by lia.
replace (spZ regs + -24) with (spZ regs - 24) in V9 by lia.
replace (spZ regs + -16) with (spZ regs - 16) in V8 by lia.
replace (spZ regs + -8) with (spZ regs - 8) in V1 by lia.
pose proof (srA_aval_of_val_mem _ _ _ _ _ VNC) as VNCa. clear HR0 HR3 VNC.
(* the two runs wrote the frame and ncalls only *)
assert (KEEPJ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem ms0) a = rdW W mem a).
{ intros a Ha H1 H2.
  assert (HZ : ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)))
    by (intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)]).
  rewrite (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms) (ms_mem ms0)
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) HFr0
    ltac:(srA_win Usp AW285) a Ha HZ).
  exact (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms)
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) HFr
    ltac:(srA_win Usp AW285) a Ha HZ). }
clear HF HFr HG HF0 HFr0 HG0.
(* the events, live bytes and meter arg_i may spend *)
assert (EVI0 : 0 <= EV_ARG_I) by (vm_compute; discriminate).
assert (EVA0 : 0 <= EV_ANSWER) by (vm_compute; discriminate).
assert (LA0 : 0 <= LIVE_ANSWER t) by (unfold LIVE_ANSWER, hand_back_c.LIVE_HAND_BACK, xstrdup_c.LIVE_XSTRDUP; lia).
assert (HXA0 : 0 <= XM_ARG_I MT id).
{ unfold XM_ARG_I, xstrdup_c.XM_XSTRDUP. apply (mo_malloc_nonneg MT MTL). lia. }
assert (HXM0 : 0 <= XM_ANSWER MT t).
{ unfold XM_ANSWER, hand_back_c.XM_HAND_BACK, xstrdup_c.XM_XSTRDUP.
  pose proof (mo_free_nonneg MT MTL) as F0.
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)) as M0. lia. }
assert (HevA : st_nev S + EV_ARG_I <= EV_MAX).
{ pose proof Hev as Hx. unfold EV_SUP_REMOVE in Hx. rewrite Hsf0 in Hx. lia. }
assert (HliveA : blocks_bytes S + LIVE_ARG_I id <= LIVE_MAX).
{ pose proof Hlive as Hx. unfold LIVE_SUP_REMOVE in Hx. lia. }
assert (HmokA : mo_ok MT S (XM_ARG_I MT id)).
{ refine (mok_station MT S S _ 0 _ MTL MOK (mle_start MT S MTL) HXA0 _).
  unfold XM_SUP_REMOVE. rewrite Hsf0. lia. }
(* the join piece; its continuation is the state at the tail jump *)
change (BASE + 18136) with (BASE + (AF_sup_remove + SR_J)).
refine (JL ly S W regs mem md ch id O 0 ly S W (ms_regs ms0) (ms_mem ms0) mdv0 c (EV_SUP_REMOVE R)
  (sr_post B MT ly S O R id) HPRE HFRM Hfr8 H10 Hid HROD HOB HJ Hsl Hspj H8j P9' H18j H3j H4j Hsj V18 V9 V8 V1
  HevA HliveA HmokA _).
intros fx1 Hfx lyt St Wt regst memt mdt p HJt Hspt Hra1 HPT H10t H11t H12t VFN VNA VARG HSTR Hp4096 HPERM HAPART
  KEEPPG KEEPBL HBB HMLE.
pose proof (proj1 HJt) as HARt.
pose proof (dec_length id Hid) as Hdl.
assert (Hpin : In (p, Z.of_nat (length (dec id)) + 1) (ablocks B lyt St))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | left; reflexivity]).
assert (HinS : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B lyt St))
  by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact HPERM | right; exact Hpn]).
assert (Hpk : ~ In (p, Z.of_nat (length (dec id)) + 1) (ablocks B ly S)).
{ pose proof (Permutation_NoDup HPERM (sr_nodup_blocks B LAWS lyt St Wt memt mdt HARt)) as Hnd.
  apply List.NoDup_cons_iff in Hnd. exact (proj1 Hnd). }
(* the bytes of the tail state: the statics outside ncalls and the slot's 16 bytes, and the live blocks at the entry *)
assert (KPG : forall a, inFP cmd_PG a -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + 16) ->
  rdW Wt memt a = rdW W mem a).
{ intros a Hpg H1 H2. rewrite (KEEPPG a Hpg H2). pose proof (srA_PG_low a Hpg).
  apply KEEPJ; [lia | rewrite WS in *; lia | exact H1]. }
assert (KBL : forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < req_size m -> rdW Wt memt (b + i) = rdW W mem (b + i)).
{ intros b m i Hin Hi. rewrite (KEEPBL b m i Hin Hi).
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4096 & Hbc & _).
  apply KEEPJ; [lia | rewrite WS in *; lia |].
  intros Hn. apply (srA_blk_PG ly S W mem md b m (b + i) HAR Hin ltac:(lia)).
  apply sr_inPG. unfold OFF_NCALLS, A_G_REC in *. lia. }
(* the recorder at the tail state: the new call in slot n *)
assert (VNCt : aval_mem (rdW Wt memt) (A_G_REC + OFF_NCALLS) 4 (Z.of_nat n + 1)).
{ apply (srr_aval_keep_in _ _ _ _ _ (A_G_REC + 8) (A_G_REC + 12) VNCa); [lia | cbn; lia|].
  intros x Hx. apply KEEPPG; [apply sr_inPG; unfold A_G_REC in *; lia | rewrite Hcv; unfold A_G_REC in *; lia]. }
assert (AP1 : iv_apart p (Z.of_nat (length (dec id)) + 1) A_G_REC REC_SIZE).
{ apply (srA_apart_PG lyt St Wt memt mdt p _ A_G_REC REC_SIZE HARt Hpin); [lia | unfold REC_SIZE; lia |].
  intros a Ha. apply sr_inPG. left. unfold REC_SIZE in Ha. exact Ha. }
assert (AP2 : iv_apart p (Z.of_nat (length (dec id)) + 1) A_REC_SPILL SC_SIZE).
{ apply (srA_apart_PG lyt St Wt memt mdt p _ A_REC_SPILL SC_SIZE HARt Hpin); [lia | unfold SC_SIZE; lia |].
  intros a Ha. apply sr_inPG. right. unfold SC_SIZE in Ha. exact Ha. }
assert (HLQ : forall pn, In pn (lay_blocks Q) ->
  In pn (ablocks B lyt St) /\ iv_apart p (Z.of_nat (length (dec id)) + 1) (fst pn) (snd pn)).
{ intros pn Hpn. pose proof (proj1 (HLIVE pn Hpn)) as Hb.
  split; [exact (HinS pn Hb) | exact (proj1 (Forall_forall _ _) HAPART pn Hb)]. }
assert (KREC : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> ~ (c <= a < c + 16) -> rdW Wt memt a = rdW W mem a).
{ intros a Ha H1 H2. apply KPG; [apply sr_inPG; unfold REC_SIZE, SC_SIZE in Ha; exact Ha | exact H1 | exact H2]. }
assert (KBLK : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rdW Wt memt (fst pn + i) = rdW W mem (fst pn + i)).
{ intros [b m] i Hpn Hi. cbn [fst snd] in Hi |- *. pose proof (HLIVE _ Hpn) as (Hb & Hm & _). cbn [snd] in Hm.
  pose proof (req_size_pos m ltac:(lia)) as [_ Hrq]. exact (KBL b m i Hb ltac:(lia)). }
pose proof (sr_rep_slot (ablocks B ly S) (ablocks B lyt St) (rdW W mem) (rdW Wt memt) R Q REC_REMOVE p (dec id)
  HQ Hlt ltac:(unfold REC_REMOVE, REC_FN_COUNT; lia) VNCt VFN VNA VARG HSTR ltac:(unfold LMAX; lia)
  ltac:(lia) Hpin AP1 AP2 HLQ KREC KBLK) as HR'.
assert (HREP1 : rec_repA B lyt St (rdW Wt memt) (rec_record R REC_REMOVE [dec id])
  ((p, Z.of_nat (length (dec id)) + 1) :: O)).
{ exists (RLay (l_calls Q ++ [[(p, Z.of_nat (length (dec id)) + 1)]]) (l_spill Q) (l_answer Q) (l_reply Q)).
  split; [exact HR'|]. intros pn. rewrite srr_lay_slot. cbn [In]. rewrite HOQ. unfold lay_blocks.
  rewrite !in_app_iff. cbn [In]. rewrite !in_app_iff. tauto. }
(* g_rec.answer, the old answer: one of the recorder's blocks, or 0 *)
destruct (sr_old _ _ _ _ _ _ HR') as [HOLDAV _]. cbn [l_answer] in HOLDAV.
destruct (sr_old _ _ _ _ _ _ HQ) as [_ HOLDQ].
assert (Hold64 : 0 <= match l_answer Q with Some pa => fst pa | None => 0 end < 2 ^ 64).
{ destruct (l_answer Q) as [[b m]|] eqn:Ela; [|lia].
  destruct (HOLDQ (b, m) eq_refl) as (_ & Hb & _).
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb) as (_ & H4 & Hc4 & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [Hr1 _]. cbn [fst]. lia. }
assert (HOLDC : forall pn, In pn (ablocks B lyt St) -> fst pn = match l_answer Q with Some pa => fst pa | None => 0 end ->
  In pn O /\ In pn (ablocks B ly S)).
{ intros pn Hpn Hf. destruct (l_answer Q) as [pa|] eqn:Ela.
  - destruct (HOLDQ pa eq_refl) as (Hpa1 & Hpa2 & _).
    pose proof (sr_fst_inj B LAWS lyt St Wt memt mdt pn pa HARt Hpn (HinS pa Hpa2) Hf) as Ep. subst pn.
    split; [apply HOQ; exact Hpa1 | exact Hpa2].
  - destruct pn as [b m]. cbn [fst] in Hf. subst b.
    destruct (al_blocks _ _ LAWS lyt St Wt memt mdt 0 m HARt Hpn) as (_ & H4 & _). lia. }
assert (HOLDO : forall pn, In pn ((p, Z.of_nat (length (dec id)) + 1) :: O) ->
  fst pn = match l_answer Q with Some pa => fst pa | None => 0 end -> In pn O).
{ intros pn [<- | Hpn] Hf; [|exact Hpn]. exfalso. destruct (HOLDC _ Hpin Hf) as [_ Hb]. exact (Hpk Hb). }
(* the call record() made: slot n of the table *)
assert (HSLOT : (exists k0, nth_error (r_calls (rec_record R REC_REMOVE [dec id])) k0 = Some (REC_REMOVE, [dec id]) /\
    c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k0) \/
  (c = A_REC_SPILL /\ (REC_REMOVE, [dec id]) = r_spill (rec_record R REC_REMOVE [dec id]))).
{ left. exists (length (r_calls R)). split; [|reflexivity].
  rewrite (srr_rec_record_lt R REC_REMOVE [dec id] Hlt). cbn [r_calls set_calls].
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
assert (Hkt : 0 + EV_ARG_I + EV_ANSWER <= EV_SUP_REMOVE R) by (unfold EV_SUP_REMOVE; rewrite Hsf0; lia).
assert (HliveT : blocks_bytes St + LIVE_ANSWER t <= LIVE_MAX) by (unfold LIVE_SUP_REMOVE in Hlive; lia).
assert (Hacc : XM_ARG_I MT id + XM_ANSWER MT t <= XM_SUP_REMOVE MT R id t) by (unfold XM_SUP_REMOVE; rewrite Hsf0; lia).
(* the tail piece at fx1 (answer's rounding mode 0 from the entry's through fxrel), and the post-condition from its
   post; its apost_baseF at fx1 is the arm's at fx (PaFx.v's srr_apost_baseF_lift) *)
pose proof (TAIL fx1 ly S W regs mem md ch id R O lyt St Wt regst memt mdt (0 + EV_ARG_I)
  ((p, Z.of_nat (length (dec id)) + 1) :: O) c (match l_answer Q with Some pa => fst pa | None => 0 end) (XM_ARG_I MT id)
  HPRE (fxrel_frm0 fx fx1 HFRM Hfx) Hfr8 HROD HOB HJt Hspt Hra1 HPT H10t H11t H12t HREP1 HOLDAV Hold64 HOLDO HSLOT
  ltac:(lia) Hkt Hev HliveT MOK HMLE Hacc) as TL1.
assert (HP0 : Permutation (ablocks B ly S) (ablocks B ly S ++ [])) by (rewrite app_nil_r; apply Permutation_refl).
assert (HF0 : forall pn, In pn [] -> In pn O) by (intros pn []).
assert (HO10 : forall pn, In pn O <-> In pn O /\ ~ In pn []).
{ intros pn. split; [intros H; split; [exact H | intros []] | intros [H _]; exact H]. }
assert (HO2 : forall pn, In pn ((p, Z.of_nat (length (dec id)) + 1) :: O) <->
  In pn O \/ pn = (p, Z.of_nat (length (dec id)) + 1)).
{ intros pn. cbn [In]. split; intros [H|H]; [right; symmetry; exact H | left; exact H | right; exact H | left; symmetry; exact H]. }
assert (HOB2 : forall pn, In pn ((p, Z.of_nat (length (dec id)) + 1) :: O) -> In pn (ablocks B lyt St)).
{ intros pn [<- | H]; [exact Hpin | apply HinS; exact (proj1 (Forall_forall _ _) HOB pn H)]. }
assert (Hold : forall pn, In pn (ablocks B lyt St) -> fst pn = match l_answer Q with Some pa => fst pa | None => 0 end ->
  In pn O) by (intros pn Hpn Hf; exact (proj1 (HOLDC pn Hpn Hf))).
apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
eapply SRr_mono; [exact TL1|].
unfold apost_baseF. cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ2 & HP2 & HK2).
exists fx2, ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
split; [exact HJ2|]. split; [exact HP2|].
exact (sr_post_of B MT LAWS ly S W mem md O R id lyt St ((p, Z.of_nat (length (dec id)) + 1) :: O) O [] (ablocks B ly S)
  p (Z.of_nat (length (dec id)) + 1) (match l_answer Q with Some pa => fst pa | None => 0 end) ly2 S2 W2 regs2 mem2 md2
  HAR HP0 HF0 HO10 HPERM Hpk HO2 HOB2 Hold HBB (proj1 HJ2) HK2).
Qed.
End c.
End b.
End a.
