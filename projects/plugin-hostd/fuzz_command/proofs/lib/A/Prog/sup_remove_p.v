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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_broadcast.v, with its module paths and module names changed; 431 of its 462 lines of code are new or changed and 58 lines of the source are left out. *)
(* sup_remove's walk on the ASan build of plugin-hostd/fuzz_command, part P: the spill arm (g_rec.ncalls = 16), from
   the entry through `bne a2,a3` not taken (0x8ab84), s1 := record.spill, rec_calls_free(&record.spill, 1) (0x8ab98,
   through cl_callS_wide with rec_calls_free's statement), `j 0x8abbc` to the join, then the join piece (sr_jl_stmt),
   the tail piece (sr_tail_stmt) and the post-condition's block bookkeeping (sr_post_of, sup_remove_q.v). The join
   piece and the tail piece are taken here in their stated forms (sup_remove_s1.v) and supplied in sup_remove.v.

   Statement passes 4 and 5: the arm takes the rounding-mode-0 premise HFRM
   and ends in apost_baseF. rec_calls_free keeps the FP state (its post is apost_base): its statement is used at
   the entry's fx through the unchanged kit rule cl_callS_wide, and its frame chain is achain's empty case (s0 = id,
   at that call). The join piece returns from arg_i at some fx1 (fxrel fx fx1), where the tail piece runs
   (rounding mode 0 by fxrel_frm0); its apost_baseF at fx1 lifts to the arm's (srr_apost_baseF_lift). astack_pres
   is gone. *)
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
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
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
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a.
Hypothesis RRO : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a.
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis JL : sr_jl_stmt B MT.
Hypothesis TAIL : forall fx0 : YK11.FPState, @sr_tail_stmt fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

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

Lemma srp_u64 : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). reflexivity. Qed.
Lemma srp_aval_of_val_mem : forall (H : word -> bool) mem a (n : nat) v,
val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma srp_aval_keep : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.
(* the call target of rec_calls_free *)
Lemma srp_sig_rcf : SIGMA CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. rewrite (SIGP CS_rec_calls_free); [reflexivity | cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right])]. Qed.
(* a spill call without arguments has no argument blocks *)
Lemma srp_lspill_nil : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q -> snd (r_spill R) = [] -> l_spill Q = [].
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & _) Hsp. destruct HC as (_ & _ & _ & _ & C5 & _).
destruct C5 as (_ & _ & E & _). rewrite Hsp in E. destruct (l_spill Q); [reflexivity | discriminate].
Qed.
(* the recorder's block set with one spill argument x in place of none *)
Lemma srp_lay_spill_in : forall C A Y (x pn : Z * Z),
In pn (lay_blocks (RLay C [x] A Y)) <-> In pn (lay_blocks (RLay C [] A Y)) \/ pn = x.
Proof.
intros C A Y x pn. unfold lay_blocks. cbn [l_calls l_spill l_answer l_reply app].
generalize (oblk A ++ oblk Y). intros L. rewrite !in_app_iff. cbn [In].
split.
- intros [H | [H | H]]; [left; left; exact H | right; symmetry; exact H | left; right; exact H].
- intros [[H | H] | H]; [left; exact H | right; right; exact H | right; left; symmetry; exact H].
Qed.
(* the full table: record() writes the spill *)
Lemma srp_rec_record_full : forall R fn A, length (r_calls R) = 16%nat -> rec_record R fn A = set_spill R (fn, A).
Proof. intros R fn A H. unfold rec_record. rewrite H. reflexivity. Qed.
(* a chunk of a region of the symbolic state holds its value *)
Lemma srp_chunk : forall E ss ms i n lo hi wlo whi cs od (w : N) e b v,
st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> val_mem SEGS (ms_mem ms) (b + od) (N.to_nat w) v.
Proof.
intros E ss ms i n lo hi wlo whi cs od w e b v HS Hi Hb Hc He Hv Hw.
exact (field_of_region E (ms_mem ms) n b cs lo hi wlo whi od w e v (st_ok_region_nth E ss ms i _ HS Hi) Hb Hc He Hv Hw).
Qed.
(* a live block lies apart from a range of the program's statics *)
Lemma srp_blk_apart : forall ly S (W : world SEGS) mem md p k g n, AR SEGS B ly S W mem md -> In (p, k) (ablocks B ly S) ->
1 <= k -> 1 <= n -> (forall a, g <= a < g + n -> inFP cmd_PG a) -> iv_apart p k g n.
Proof.
intros ly S W mem md p k g n HAR Hin Hk Hn Hpg. unfold iv_apart.
destruct (Z_le_gt_dec (p + k) g) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (g + n) p) as [H2|H2]; [right; exact H2|]. exfalso.
pose proof (req_size_pos k ltac:(lia)) as [_ Hrq].
apply (blk_img SEGS B LAWS ly S W mem md p k (Z.max p g) HAR Hin ltac:(lia)).
apply cif_prog_img, Hpg. lia.
Qed.
(* the recorder's blocks after the spill call: the cleared spill's set and the new argument *)
Lemma srp_Ot : forall (Q1 : rlay) (O1 : list (Z * Z)) (x : Z * Z), l_spill Q1 = [] ->
(forall pn, In pn O1 <-> In pn (lay_blocks Q1)) ->
forall pn, In pn (lay_blocks (RLay (l_calls Q1) [x] (l_answer Q1) (l_reply Q1))) <-> In pn O1 \/ pn = x.
Proof.
intros [C S0 A Y] O1 x Hs HO pn. cbn [l_spill l_calls l_answer l_reply] in *. subst S0.
rewrite srp_lay_spill_in, HO. tauto.
Qed.

Lemma sr_arm_spill : forall ly S W (regs : bvmap 5 word) mem md ch (id : Z) (R : rstate) (O : list (Z * Z)),
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
length (r_calls R) = 16%nat ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_remove) regs mem md)
(apost_baseF SEGS B SUP_REMOVE_STK (sr_FP O) regs ly S W mem md (EV_SUP_REMOVE R) (sr_post B MT ly S O R id)).
Proof.
intros ly S W regs mem md ch id R O t HPRE HFRM Hfr8 HROD HRO H10 Hid HREP Hev Hlive MOK Hn16.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_REMOVE_STK = 16592) by (vm_compute; reflexivity).
pose proof HREP as (Q & HQ & HOQ).
destruct (sr_lay_live _ _ _ _ _ _ HQ) as [HND HLIVE].
assert (HOB : Forall (fun pn => In pn (ablocks B ly S)) O).
{ apply Forall_forall. intros pn Hpn. apply HLIVE. apply HOQ. exact Hpn. }
destruct (sr_ncalls _ _ _ _ _ _ HQ) as [Hnc _].
rewrite Hn16 in Hnc. change (Z.of_nat 16) with 16 in Hnc.
pose proof (sr_entry B HB LAWS TL VOBJS PRW W ly S regs mem md ch 16 HPRE Hnc ltac:(lia)) as HS.
pose proof (ajournal_init SEGS B SUP_REMOVE_STK (sr_FP O) ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (sr_extra 16))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E8 : ew E 8 = getr regs 8) by (apply EEo; reflexivity).
assert (E9 : ew E 9 = getr regs 9) by (apply EEo; reflexivity).
assert (E18 : ew E 18 = getr regs 18) by (apply EEo; reflexivity).
assert (E10' : ew E 10 = getr regs 10) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 id) by (rewrite E10'; exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E sr_kN = Z_to_bv 64 16) by (subst E; rewrite Eimg_low by (unfold sr_kN, A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E33' : ew E 33 = Z_to_bv 64 16) by exact E33.
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC).
{ subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). reflexivity. }
assert (E292 : ew E (A_OBJ 51) = Z_to_bv 64 A_REC_SPILL).
{ subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite (VOBJS 51%nat ltac:(vm_compute; lia)). reflexivity. }
assert (AW285 : bv_unsigned (ew E 285%nat) = A_G_REC) by (change 285%nat with (A_OBJ 44); rewrite E285; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (sr_extra 16)) E).
{ subst E. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
clear HE EEo.
assert (SHOK : sh_ok SEGS sr_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
unfold cfg_at, w64.
(* 0x8ab50 .. 0x8ab84: the frame, the shadow base, g_rec.ncalls = 16, and the branch *)
paj_run_tok RUN HS HJ SHOK sr_Bspan.
{ sr_awr0 Usp E285. }
sr_fold_md.
psrr_branch_tok RUN BR HS SHOK sr_Bspan.
{ exfalso. rewrite branch_ne_U in Hc. rewrite (U_atom E 33 16 E33) in Hc by lia.
  rewrite U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. lia. }
(* 0x8ab88 .. 0x8ab98: s1 := &record.spill, a1 := 1, a0 := s1, and the call of rec_calls_free *)
paj_run_tok RUN HS HJ SHOK sr_Bspan.
{ sr_awr0 Usp E285. }
sr_fold_md.
(* the state at the call *)
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
change (ew E 292%nat) with (ew E (A_OBJ 51)) in P10. rewrite E292 in P10.
assert (HspC : spZ (ms_regs ms0) = spZ regs + -32).
{ unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (WR : REC_CALLS_FREE_STK = 16496) by (vm_compute; reflexivity).
(* the runs wrote only the frame: every byte below alloc_ceiling is the entry's (g_rec.ncalls still holds 16) *)
assert (KF1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms)
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr).
  intros b wlo whi a' Hin Hrr. cbv beta. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?AW285 in Hrr; lia|]).
  destruct Hin. }
assert (KF0 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) ->
  rdW W (ms_mem ms0) a = rdW W (ms_mem ms) a).
{ apply (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms) (ms_mem ms0)
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12)) HFr0).
  intros b wlo whi a' Hin Hrr. cbv beta. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?AW285 in Hrr; lia|]).
  destruct Hin. }
assert (VNc : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (A_G_REC + 8) 4 16).
{ refine (srp_chunk E _ (restrict (w_H W) ms0) 3%nat 285%nat _ _ _ _ _ 8 4%N (SOff 33 0) A_G_REC 16 HS eq_refl AW285 _ _ _ _).
  - cbn. repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite E33', Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn. lia.
  - cbn. lia. }
assert (KEEPc : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms0) a = rdW W mem a).
{ intros a Ha.
  destruct (Z_le_gt_dec (A_G_REC + 8) a) as [Hl|Hl]; [destruct (Z_lt_le_dec a (A_G_REC + 12)) as [Hh|Hh]|].
  - pose proof (srp_aval_of_val_mem _ _ _ _ _ VNc (Z.to_nat (a - (A_G_REC + 8))) ltac:(lia)) as V1.
    pose proof (Hnc (Z.to_nat (a - (A_G_REC + 8))) ltac:(lia)) as V2.
    rewrite Z2Nat.id in V1, V2 by lia. unfold OFF_NCALLS in V2.
    replace (A_G_REC + 8 + (a - (A_G_REC + 8))) with a in V1, V2 by lia. rewrite V1, V2. reflexivity.
  - rewrite KF0 by lia. apply KF1; lia.
  - rewrite KF0 by lia. apply KF1; lia. }
clear KF0 KF1 VNc.
assert (HQc : arep_at (ablocks B ly S) (rdW W (ms_mem ms0)) A_G_REC A_REC_SPILL R Q).
{ apply (sr_arep_keep (ablocks B ly S) (ablocks B ly S) (rdW W mem) (rdW W (ms_mem ms0)) A_G_REC A_REC_SPILL R Q HQ).
  - intros pn Hpn. exact (proj1 (HLIVE pn Hpn)).
  - intros a Ha. apply KEEPc. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha. lia.
  - intros [p n] i Hin Hi. cbn [fst snd] in *. destruct (HLIVE _ Hin) as (Hb & Hn1 & _).
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hb) as (_ & H4096 & Hpc & _).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. apply KEEPc. lia. }
destruct (sr_rcf_pre (ablocks B ly S) (rdW W (ms_mem ms0)) R Q HQc) as (HPS & HNDPS & HLPS & HPSQ).
assert (Hsf : rec_spill_frees R = Z.of_nat (length (concat [l_spill Q]))).
{ unfold rec_spill_frees. rewrite Hn16, HLPS. reflexivity. }
assert (PSO : forall pn, In pn (l_spill Q) -> In pn O) by (intros pn Hpn; apply HOQ, HPSQ, Hpn).
assert (PSbl : forall pn, In pn (l_spill Q) -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (proj1 (HLIVE pn (HPSQ pn Hpn)))).
assert (HEVc : 0 <= EV_ARG_I /\ 0 <= EV_ANSWER) by (split; vm_compute; discriminate).
assert (HXA : 0 <= XM_ANSWER MT t /\ 0 <= XM_ARG_I MT id).
{ unfold XM_ANSWER, XM_ARG_I, hand_back_c.XM_HAND_BACK, xstrdup_c.XM_XSTRDUP.
  pose proof (mo_free_nonneg MT MTL). pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length t) + 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (dec id)) + 1) ltac:(lia)). lia. }
assert (HLA : 0 <= LIVE_ANSWER t) by (unfold LIVE_ANSWER, hand_back_c.LIVE_HAND_BACK, xstrdup_c.LIVE_XSTRDUP; lia).
(* rec_calls_free's footprint: record.spill's nargs field and the spill's argument blocks *)
assert (FP1lo : forall a, inFP (rcf_fp A_REC_SPILL [l_spill Q]) a -> 0 <= a < alloc_ceiling /\
  ((A_REC_SPILL + 4 <= a < A_REC_SPILL + 8) \/ exists p k, In (p, k) (l_spill Q) /\ p <= a < p + req_size k)).
{ intros a (r & Hr & Ha). unfold rcf_fp in Hr. apply in_app_iff in Hr as [Hr | Hr].
  - cbn in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha. unfold CALL_SIZE, CALL_OFF_NARGS in Ha.
    split; [unfold A_REC_SPILL in *; lia | left; lia].
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p k] & <- & Hin). cbn [concat] in Hin. rewrite app_nil_r in Hin.
    cbn [fst snd] in Ha. destruct (al_blocks _ _ LAWS ly S W mem md p k HAR (PSbl _ Hin)) as (_ & H4096 & Hpc & _).
    split; [lia | right; exists p, k; split; [exact Hin | lia]]. }
pose proof (sr_aro_journal B LAWS RPG RRO SUP_REMOVE_STK (spZ regs) O ly S W mem md [] ly S W (ms_mem ms0) mdv0 0 HAR HOB HJ HROD)
  as HRODc.
(* the frame chain at the call: s0 = id is no frame pointer *)
assert (HCH : achain ly (rdW W (ms_mem ms0)) (spZ regs + -32) (s0Z (ms_regs ms0)) []).
{ assert (Hs0 : s0Z (ms_regs ms0) = id mod 2 ^ 64) by (unfold s0Z; rewrite P8, E10; apply srp_u64).
  rewrite Hs0. left. split; [|reflexivity].
  destruct (Z_lt_le_dec id 0) as [Hn | Hn].
  - right. left. assert (Hm : id mod 2 ^ 64 = id + 2 ^ 64)
      by (rewrite <- (Z.mod_add id 1 (2 ^ 64)) by lia; apply Z.mod_small; lia).
    rewrite Hm. lia.
  - left. rewrite Z.mod_small by lia. lia. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms0) (ms_mem ms0) (Z_to_bv 64 (SIGMA CS_rec_calls_free)) SUP_REMOVE_STK (spZ regs)
    (sr_FP O) ly S W mem md [] ly S mdv0 0 REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q]) (EV_REC_CALLS_FREE [l_spill Q])
    (-32) (Z_to_bv 64 (BASE + 18104)) [] _ HJ HspC).
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite P3, E3. exact Hgp.
  - rewrite P4, E4. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - exact HCH.
  - (* rec_calls_free's statement, c = &record.spill, ps = [the spill's arguments] *)
    intros HPREc. rewrite srp_sig_rcf. eapply SRr_mono.
    { refine (TREC_CALLS_FREE fx ly S W (ms_regs ms0) (ms_mem ms0) mdv0 [] A_REC_SPILL [l_spill Q] HPREc HRODc P10
        ltac:(rewrite P11; reflexivity) ltac:(cbn; lia) _ ltac:(reflexivity) HPS HNDPS _ _).
      - right. left. unfold CALL_SIZE, SC_SIZE. cbn. lia.
      - unfold EV_SUP_REMOVE in Hev. rewrite Hsf in Hev. unfold EV_REC_CALLS_FREE. lia.
      - apply (mo_ok_le MT MTL S _ (XM_SUP_REMOVE MT R id t) MOK). unfold XM_REC_CALLS_FREE, XM_SUP_REMOVE.
        rewrite Hsf. lia. }
    unfold apost_base. cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HP2 & HQ2).
    exists ly2, S2, regs2, mem2, md2. rewrite P1 in Hc2. split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HP2 | exact HQ2].
  - (* rec_calls_free's footprint lies in sup_remove's: record.spill (a static) and the recorder's blocks *)
    intros a Hfp. destruct (FP1lo a Hfp) as (Ha & [Hs | (p & k & Hin & Hpk)]).
    + right; right; right; right. left.
      assert (Hpg : inFP cmd_PG a) by (apply sr_inPG; right; unfold A_REC_SPILL in *; lia).
      split; [|split; [exact (HPROG B HB a Hpg) | exact (cif_prog_img a Hpg)]].
      unfold sr_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left.
      unfold SC_SIZE, A_REC_SPILL in *. lia.
    + right. left. split.
      * unfold sr_FP. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. right.
        exists (p, p + req_size k). split; [|cbn [fst snd]; lia].
        unfold ablocks_fp. apply in_map_iff. exists (p, k). split; [reflexivity | exact (PSO _ Hin)].
      * exists p, k. split; [exact (PSbl _ Hin) | exact Hpk].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Hfp Hw _. destruct (FP1lo a Hfp) as (Ha & _). exfalso. lia. }
clear SHOK. cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP2 & HQ2).
destruct HQ2 as (HPerm2 & _ & _ & _ & _ & HrepS & _ & HBB1 & MLE1).
specialize (HrepS R Q HQc eq_refl eq_refl).
(* back at 0x8ab9c: the frame region is kept by the call *)
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & HNEV2 & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?T -> _ => assert (HRK : T); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply F1c; [lia | lia | intros Hf; destruct (FP1lo a Hf); lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ec eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM Ec) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (sr_extra 16)) Ec) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (E292c : ew Ec (A_OBJ 51) = Z_to_bv 64 A_REC_SPILL) by (rewrite HE2, ew_havoc_above by (cbv; lia); exact E292).
clear HE2.
assert (Usp2 : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (SHOK2 : sh_ok SEGS sr_Bx [] Ec (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
(* 0x8ab9c: `j 0x8abbc`, the join *)
paj_run_to_tok RUNTO HS HJ2 SHOK2 sr_Bspan (AF_sup_remove + SR_J).
{ lazymatch goal with |- awr_ok ?sg ?bb ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E rs' stk sp0 fp b0 bc fr ly own) end.
  apply (awr_ok_cons_stack SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat);
    [reflexivity | exact Usp2 | cbn; vm_compute; discriminate | cbn; lia | apply awr_ok_nil]. }
sr_fold_md.
(* the run kept every byte outside the frame *)
assert (KEEPj : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W2 (ms_mem ms1) a = rdW W2 mem2 a).
{ apply (kept_of_frame (segs := SEGS) Ec _ (w_H W2) mem2 (ms_mem ms1) (fun a => spZ regs - 32 <= a < spZ regs) HFr1).
  intros b wlo whi a' Hin Hrr. cbv beta. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2 in Hrr; lia|]).
  destruct Hin. }
(* the state at the join: s0 = id, s1 = &record.spill, s2 = the shadow base, the frame words *)
pmkst HS.
prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
prreg HS (9%bv : bv 5) T9. prreg HS (18%bv : bv 5) T18.
pose proof (regs_kept_of_st_ok_pi Ec _ _ regs (sr_extra 16) (map (Z_to_bv 5) [19; 20; 21; 22; 23; 24; 25; 26; 27])
  HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
assert (J2 : spZ (ms_regs ms1) = spZ regs - 32) by (unfold spZ at 1; rewrite T2, Usp2; rewrite unsigned_lit_small by lia; lia).
assert (J8 : getr (ms_regs ms1) 8 = getr regs 10) by (rewrite T8, OLD2 by lia; exact E10').
assert (J9 : getr (ms_regs ms1) 9 = w64 A_REC_SPILL) by (rewrite T9; exact E292c).
assert (J18 : getr (ms_regs ms1) 18 = w64 SB) by (rewrite T18, OLD2 by lia; exact E32).
assert (J3 : getr (ms_regs ms1) 3 = getr regs 3) by (rewrite T3, OLD2 by lia; exact E3).
assert (J4 : getr (ms_regs ms1) 4 = getr regs 4) by (rewrite T4, OLD2 by lia; exact E4).
assert (JS : forall r, 19 <= r <= 27 -> getr (ms_regs ms1) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. apply KR. apply in_map. cbn [In]. lia. }
assert (V18 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (spZ regs - 32) 8 (bv_unsigned (getr regs 18))).
{ replace (spZ regs - 32) with (spZ regs + -32) by lia.
  refine (srp_chunk Ec _ (restrict (w_H W2) ms1) 0%nat 2%nat _ _ _ _ _ (-32) 8%N (SOff 18 0) (spZ regs) _ HS eq_refl Usp2 _ _ _ _).
  - cbn. repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite OLD2 by lia. rewrite E18, Z.add_0_r. reflexivity.
  - apply bv_unsigned_in_range.
  - cbn. lia. }
assert (V9 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (spZ regs - 24) 8 (bv_unsigned (getr regs 9))).
{ replace (spZ regs - 24) with (spZ regs + -24) by lia.
  refine (srp_chunk Ec _ (restrict (w_H W2) ms1) 0%nat 2%nat _ _ _ _ _ (-24) 8%N (SOff 9 0) (spZ regs) _ HS eq_refl Usp2 _ _ _ _).
  - cbn. repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite OLD2 by lia. rewrite E9, Z.add_0_r. reflexivity.
  - apply bv_unsigned_in_range.
  - cbn. lia. }
assert (V8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (spZ regs - 16) 8 (bv_unsigned (getr regs 8))).
{ replace (spZ regs - 16) with (spZ regs + -16) by lia.
  refine (srp_chunk Ec _ (restrict (w_H W2) ms1) 0%nat 2%nat _ _ _ _ _ (-16) 8%N (SOff 8 0) (spZ regs) _ HS eq_refl Usp2 _ _ _ _).
  - cbn. repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite OLD2 by lia. rewrite E8, Z.add_0_r. reflexivity.
  - apply bv_unsigned_in_range.
  - cbn. lia. }
assert (V1 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms1)) (spZ regs - 8) 8 (bv_unsigned (getr regs 1))).
{ replace (spZ regs - 8) with (spZ regs + -8) by lia.
  refine (srp_chunk Ec _ (restrict (w_H W2) ms1) 0%nat 2%nat _ _ _ _ _ (-8) 8%N (SOff 1 0) (spZ regs) _ HS eq_refl Usp2 _ _ _ _).
  - cbn. repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite OLD2 by lia. rewrite E1, Z.add_0_r. reflexivity.
  - apply bv_unsigned_in_range.
  - cbn. lia. }
assert (HEVj : st_nev S2 + EV_ARG_I <= EV_MAX).
{ unfold EV_SUP_REMOVE in Hev. rewrite Hsf in Hev. unfold EV_REC_CALLS_FREE in HNEV2. lia. }
assert (HLVj : blocks_bytes S2 + LIVE_ARG_I id <= LIVE_MAX).
{ unfold LIVE_SUP_REMOVE in Hlive. unfold LIVE_REC_CALLS_FREE in HBB1. lia. }
assert (HMOj : mo_ok MT S2 (XM_ARG_I MT id)).
{ apply (mok_station MT S S2 (XM_SUP_REMOVE MT R id t) (XM_REC_CALLS_FREE MT [l_spill Q]) (XM_ARG_I MT id) MTL MOK MLE1 (proj2 HXA)).
  unfold XM_SUP_REMOVE, XM_REC_CALLS_FREE. rewrite Hsf. lia. }
(* the join piece, c = &record.spill *)
refine (JL ly S W regs mem md ch id O (0 + EV_REC_CALLS_FREE [l_spill Q]) ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) mdv1 A_REC_SPILL
  (EV_SUP_REMOVE R) (sr_post B MT ly S O R id) HPRE HFRM Hfr8 H10 Hid HROD HOB HJ2 (or_intror eq_refl) J2 J8 J9 J18 J3 J4 JS
  V18 V9 V8 V1 HEVj HLVj HMOj _).
intros fx1 Hfx lyt St Wt regst memt mdt p HJt Hspt H1t HPt H10t H11t H12t HFN HNA HARG HSTR Hp4096 HPERM HAPART KPG KBL
  HBBt HMLEt.
pose proof HJt as (HARt & _).
(* the recorder after rec_calls_free: the spill's arguments freed *)
destruct HrepS as (Q1 & HQ1 & HOQ1).
set (O1 := concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) in *.
assert (HO1 : forall pn, In pn O1 <-> In pn O /\ ~ In pn (l_spill Q)).
{ intros pn. unfold O1. rewrite (sr_drop_spill Q HND pn), HOQ. tauto. }
destruct (sr_lay_live _ _ _ _ _ _ HQ1) as [_ LV1].
(* the bytes the arm kept from the call's return to answer's entry *)
assert (KG' : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_REC_SPILL <= a < A_REC_SPILL + 16) -> rdW Wt memt a = rdW W2 mem2 a).
{ intros a Ha Hn. rewrite KPG; [| apply sr_inPG; unfold REC_SIZE, SC_SIZE in Ha; exact Ha | exact Hn].
  apply KEEPj; unfold A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in Ha |- *; lia. }
assert (KQ' : forall pn i, In pn (lay_blocks Q1) -> 0 <= i < snd pn -> rdW Wt memt (fst pn + i) = rdW W2 mem2 (fst pn + i)).
{ intros [b m] i Hin Hi. cbn [fst snd] in *. destruct (LV1 _ Hin) as (Hb & Hm & _).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hb) as (_ & H4096 & Hpc & _).
  rewrite (KBL b m i Hb ltac:(lia)). apply KEEPj; lia. }
(* the new call in record.spill *)
pose proof (dec_length id Hid) as Hdl.
set (k := Z.of_nat (length (dec id)) + 1) in *.
assert (Hpin : In (p, k) (ablocks B lyt St)) by (eapply Permutation_in; [apply Permutation_sym; exact HPERM | left; reflexivity]).
assert (APG : iv_apart p k A_G_REC REC_SIZE).
{ apply (srp_blk_apart lyt St Wt memt mdt p k A_G_REC REC_SIZE HARt Hpin); [lia | unfold REC_SIZE; lia |].
  intros a Ha. apply sr_inPG. left. unfold REC_SIZE in Ha. exact Ha. }
assert (APS : iv_apart p k A_REC_SPILL SC_SIZE).
{ apply (srp_blk_apart lyt St Wt memt mdt p k A_REC_SPILL SC_SIZE HARt Hpin); [lia | unfold SC_SIZE; lia |].
  intros a Ha. apply sr_inPG. right. unfold SC_SIZE in Ha. exact Ha. }
assert (AQ : forall pn, In pn (lay_blocks Q1) -> In pn (ablocks B lyt St) /\ iv_apart p k (fst pn) (snd pn)).
{ intros pn Hpn. pose proof (proj1 (LV1 pn Hpn)) as Hb. split.
  - eapply Permutation_in; [apply Permutation_sym; exact HPERM | right; exact Hb].
  - exact (proj1 (Forall_forall _ _) HAPART pn Hb). }
pose proof (sr_rep_spill (ablocks B ly2 S2) (ablocks B lyt St) (rdW W2 mem2) (rdW Wt memt)
  (set_spill R (fst (r_spill R), [])) Q1 REC_REMOVE p (dec id) HQ1 eq_refl
  ltac:(split; vm_compute; first [discriminate | reflexivity]) HFN HNA HARG HSTR ltac:(unfold LMAX; lia) ltac:(lia)
  Hpin APG APS AQ KG' KQ') as HQ2.
rewrite sr_set_spill2, <- (srp_rec_record_full R REC_REMOVE [dec id] Hn16) in HQ2.
fold k in HQ2.
set (Q2 := RLay (l_calls Q1) [(p, k)] (l_answer Q1) (l_reply Q1)) in HQ2.
assert (HOt : forall pn, In pn (lay_blocks Q2) <-> In pn O1 \/ pn = (p, k))
  by exact (srp_Ot Q1 O1 (p, k) (srp_lspill_nil _ _ _ _ _ _ HQ1 eq_refl) HOQ1).
destruct (sr_lay_live _ _ _ _ _ _ HQ2) as [_ LV2].
(* the old answer *)
destruct (sr_old _ _ _ _ _ _ HQ2) as [Hold Hold2]. cbn [Q2 l_answer] in Hold, Hold2.
set (old := match l_answer Q1 with Some pn => fst pn | None => 0 end) in Hold, Hold2.
assert (Holdr : 0 <= old < 2 ^ 64 /\ forall pn, In pn (ablocks B lyt St) -> fst pn = old -> In pn O).
{ unfold old. destruct (l_answer Q1) as [[pa1 pa2]|] eqn:EA.
  - assert (Hpq : In (pa1, pa2) (lay_blocks Q1)).
    { unfold lay_blocks. rewrite EA. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity. }
    destruct (Hold2 (pa1, pa2) eq_refl) as (_ & Hpa & _).
    destruct (al_blocks _ _ LAWS lyt St Wt memt mdt _ _ HARt Hpa) as (_ & H4096 & Hpc & _).
    destruct (LV1 _ Hpq) as (_ & Hm & _). cbn [snd] in Hm.
    pose proof (req_size_pos pa2 ltac:(lia)) as [_ Hrq].
    split; [cbn [fst]; lia|].
    intros pn Hpn Ef. rewrite (sr_fst_inj B LAWS lyt St Wt memt mdt pn (pa1, pa2) HARt Hpn Hpa Ef).
    apply (proj1 (HO1 (pa1, pa2))). apply HOQ1. exact Hpq.
  - split; [lia|]. intros [b m] Hpn Ef. cbn [fst] in Ef. subst b.
    destruct (al_blocks _ _ LAWS lyt St Wt memt mdt _ _ HARt Hpn) as (_ & H4096 & _). lia. }
destruct Holdr as [Holdr Holdb].
(* answer's tail call, composed into sup_remove's journal *)
assert (Hkt0 : 0 <= 0 + EV_REC_CALLS_FREE [l_spill Q] + EV_ARG_I) by (unfold EV_REC_CALLS_FREE; lia).
assert (Hkt : 0 + EV_REC_CALLS_FREE [l_spill Q] + EV_ARG_I + EV_ANSWER <= EV_SUP_REMOVE R)
  by (unfold EV_SUP_REMOVE, EV_REC_CALLS_FREE; rewrite Hsf; lia).
assert (HlvS : blocks_bytes St + LIVE_ANSWER t <= LIVE_MAX)
  by (unfold LIVE_SUP_REMOVE in Hlive; unfold LIVE_REC_CALLS_FREE in HBB1; lia).
assert (Hacc : XM_REC_CALLS_FREE MT [l_spill Q] + XM_ARG_I MT id + XM_ANSWER MT t <= XM_SUP_REMOVE MT R id t)
  by (unfold XM_SUP_REMOVE, XM_REC_CALLS_FREE; rewrite Hsf; lia).
(* the tail piece at fx1 (rounding mode 0 through fxrel); its apost_baseF at fx1 is the arm's at fx *)
assert (HTAIL := TAIL fx1 ly S W regs mem md ch id R O lyt St Wt regst memt mdt (0 + EV_REC_CALLS_FREE [l_spill Q] + EV_ARG_I)
  (lay_blocks Q2) A_REC_SPILL old (XM_REC_CALLS_FREE MT [l_spill Q] + XM_ARG_I MT id) HPRE (fxrel_frm0 fx fx1 HFRM Hfx)
  Hfr8 HROD HOB HJt Hspt H1t HPt H10t H11t H12t (ex_intro _ Q2 (conj HQ2 (fun pn => iff_refl _))) Hold Holdr
  (fun pn Hpn Ef => Holdb pn (proj1 (LV2 pn Hpn)) Ef)
  (or_intror (conj eq_refl (eq_sym (f_equal r_spill (srp_rec_record_full R REC_REMOVE [dec id] Hn16)))))
  Hkt0 Hkt Hev HlvS MOK (mle_station MT S S2 St _ _ MTL MLE1 HMLEt) Hacc).
apply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hfx|].
eapply SRr_mono; [exact HTAIL|].
unfold apost_baseF. cbv beta. intros W' c' _ (fx2 & ly' & S' & regs' & mem' & md' & Hc' & Hf1 & Hf2 & HJ' & HP' & HQ').
exists fx2, ly', S', regs', mem', md'. split; [exact Hc'|]. split; [exact Hf1|]. split; [exact Hf2|].
split; [exact HJ'|]. split; [exact HP'|].
pose proof HJ' as (HAR' & _).
cbn [concat] in HPerm2. rewrite app_nil_r in HPerm2.
refine (sr_post_of B MT LAWS ly S W mem md O R id lyt St (lay_blocks Q2) O1 (l_spill Q) (ablocks B ly2 S2) p k old
  ly' S' W' regs' mem' md' HAR HPerm2 PSO HO1 HPERM _ HOt (fun pn Hpn => proj1 (LV2 pn Hpn)) Holdb _ HAR' HQ').
- intros Hin. pose proof (proj1 (Forall_forall _ _) HAPART _ Hin) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
- unfold LIVE_REC_CALLS_FREE in HBB1. lia.
Qed.
End c.
End b.
End a.
