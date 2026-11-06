(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first segment of sup_pool_config's ASan walk (plugin-hostd/fuzz_command): from
   the entry (0x8bcfc) to the point where record()'s two arms meet (0x8bd78): the prologue, then g_rec.ncalls := n + 1
   on the table arm, or rec_calls_free(&record.spill, 1) on the spill arm, in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v .. ACh8.v (a seed, the symbolic run to a call, the callee's contract
   through cl_callS, the state after the call). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YC5d YG0q YI67.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c rec_shape_of_c answer_c hand_back_c mix_call_c sup_pool_config_c PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
RecBLemmas sup_pool_config_s1 sup_pool_config_s2 sup_pool_config_s3 sup_pool_config_s4 sup_pool_config_s5
sup_pool_config_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a register of the symbolic state, its symbolic value evaluated (sup_policy_set_s1.v's sps_reg) *)
Ltac spc_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* the region i of the symbolic state, evaluated *)
Ltac spc_region HS i HR :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ssx (restrict ?H ?msx) =>
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth E ssx (restrict H msx) i r HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict mkst] in HR
| st_ok _ ?E ?ssx (restrict ?H ?msx) =>
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth E ssx (restrict H msx) i r HS ltac:(vm_compute; reflexivity)) as HR;
  cbn [ms_mem restrict mkst] in HR
end.

(* the writable windows of the entry segment's regions: the frame and g_rec.ncalls *)
Ltac spc_winA Usp EGu' :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin; cbv beta;
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?EGu' in Hrr;
    first [left; lia | right; unfold OFF_NCALLS; lia]|]); destruct Hin.

(* the machine state and the restricted frame fact the last symbolic run introduced, under fixed names *)
Ltac spc_name_run HS m HFR :=
  lazymatch type of HS with context [restrict _ ?x] => rename x into m end;
  lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem m)) |- _ => rename H into HFR end.

(* the slot of the entry segment is never written there: the walk drops it from the seed *)
Definition spc_rsE : smem := [spc_frame0; got_regionP; bcell_regionP 32; spc_ncalls].
(* the frame the prologue stores (ra, s0 .. s5 below the entry sp, atom 2), as the walk's stack region holds it *)
Definition spc_fchunks : list YP09.chunk :=
[YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

Lemma spc_soff0 : forall E k, sv_denot E (SOff k 0) = ew E k.
Proof. intros E k. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Lemma spc_bsum_nonneg : forall l, (forall pn, In pn l -> 0 <= snd pn) -> 0 <= bsum l.
Proof.
intros l. induction l as [|x l IH]; intros H; [cbn; lia|]. rewrite bsum_cons.
pose proof (H x (or_introl eq_refl)). pose proof (IH (fun pn Hp => H pn (or_intror Hp))). lia.
Qed.

(* the footprint of rec_calls_free on record.spill alone: the spill's nargs word and the blocks it frees *)
Lemma spc_rcf_fp_inv : forall P a, inFP (rcf_fp A_REC_SPILL [P]) a ->
A_REC_SPILL + 4 <= a < A_REC_SPILL + 8 \/ exists p n, In (p, n) P /\ p <= a < p + req_size n.
Proof.
intros P a Ha. unfold rcf_fp in Ha. cbn [length seq map concat] in Ha. rewrite app_nil_r in Ha.
apply inFP_app in Ha as [Ha | Ha].
- left. apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_SIZE, CALL_OFF_NARGS in Ha; cbn in Ha; lia | exact (False_ind _ (inFP_nil a Ha))].
- right. exact (inFP_ablocks_fp_inv P a Ha).
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
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HY : spc_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a write of the walk to g_rec is a footprint write to a program static *)
Lemma spc_awr_grec : forall STK sp0 O bl0 blc fr0 lyc own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp0 (spc_FP O) bl0 blc fr0 lyc own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyc own a Ha. spc_unpack HY.
right; right; right; right. unfold awr_prog_or_caller. left.
split; [exact (spc_inFP_grec O a Ha)|].
pose proof (recb_grec_in a Ha) as HPG.
split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)].
Qed.

Lemma spc_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS SPC_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc. split; [|apply Forall_nil].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I |].
split; [exact I | split; exact I].
Qed.

(* the frame the prologue stored, read off the walk's stack region *)
Lemma spc_frame_of_region : forall E (W : world SEGS) m sp0 (regs : bvmap 5 word),
region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 spc_fchunks) ->
bv_unsigned (ew E 2) = sp0 ->
(forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r) ->
spc_frame_at (mrestrict (w_H W) m) sp0 regs.
Proof.
intros E W m sp0 regs HR Hsp Hew j r Hj.
assert (Hj7 : (j < 7)%nat) by (apply (proj1 (nth_error_Some spc_saved j)); rewrite Hj; discriminate).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
assert (ONE : forall off rn, In (YP09.mkChunk off (CVal 8 (SOff rn 0))) spc_fchunks -> Z.of_nat rn = r -> (rn < 32)%nat ->
  val_mem SEGS (mrestrict (w_H W) m) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros off rn Hin Hrn Hrn32. change 8%nat with (N.to_nat 8).
  apply (field_of_region E _ 2 sp0 spc_fchunks (-64) 0 (-64) 0 off 8 (SOff rn 0) _ HR Hsp Hin); [| exact HRr | cbn; lia].
  rewrite spc_soff0. rewrite (Hew rn (Z_to_bv 5 r)); [symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hrn. }
do 7 (destruct j as [|j]; [cbn [nth_error spc_saved] in Hj; injection Hj as <-;
  match goal with |- val_mem _ _ (sp0 - 8 - 8 * Z.of_nat ?jj) _ _ =>
    let off := eval cbv in (-8 - 8 * Z.of_nat jj) in
    replace (sp0 - 8 - 8 * Z.of_nat jj) with (sp0 + off) by (cbn; lia) end;
  (eapply ONE; [cbn [spc_fchunks In]; tauto | reflexivity | lia]) |]).
lia.
Qed.
(* a symbolic run with no writable window keeps every byte *)
Lemma spc_frame_nowin : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) ->
forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' HF Hn a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a) (Hn _)). reflexivity. Qed.

Lemma spc_denot_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* s1 on the table arm: g_rec + 16 + 56 * ncalls (atom 285 = g_rec, atom 33 = ncalls) *)
Lemma spc_denot_slot : forall E n, ew E 33 = Z_to_bv 64 n -> ew E 285 = Z_to_bv 64 A_G_REC -> 0 <= n < 16 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff 285 0)) =
Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E n E33 E285 Hn. apply spc_denot_U.
assert (U1 : U E (SOff 33 0) = n) by (apply (U_atom E 33 n E33); lia).
assert (U5 : U E (SOff 285 0) = A_G_REC) by (apply (U_atom E 285 A_G_REC E285); unfold A_G_REC; lia).
rewrite U_SAlu, U_SAlu, U_SMd, U1, U5, !U_SLit. cbn [zalu_raw zmd_raw].
rewrite (YP0m.zcanon_small 56), (YP0m.zcanon_small 16) by lia.
rewrite (YP0m.zcanon_small (n * 56)) by lia.
rewrite (YP0m.zcanon_small (n * 56 + 16)) by lia.
unfold A_G_REC, OFF_CALLS, CALL_SIZE. rewrite YP0m.zcanon_small by lia. lia.
Qed.

(* the string argument (a heap string, none of the recorder's blocks) and its tail at a later state of the walk, in
   the form spc_midJ asks (s4's spc_arg_kept) *)
Lemma spc_argK : forall STK sp0 O ly S W mem md own ly' S' W' mem' md' k pn x,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (spc_FP O) ly S W mem md own ly' S' W' mem' md' k ->
(forall pk, In pk O -> In pk (ablocks B ly S)) ->
(forall pk, In pk (ablocks B ly S) -> ~ In pk O -> In pk (ablocks B ly' S')) ->
in_blockA (ablocks B ly S) pn (Z.of_nat (length x) + 1) -> astr_atR (rdW W mem) pn x ->
Z.of_nat (length x) + 1 <= LMAX + 1 ->
Forall (fun qk => iv_apart pn (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O ->
astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) [] pn (Some x) /\
(forall y, Some x = Some y -> atail_vis SEGS W' mem' (pn + Z.of_nat (length y))).
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k pn x HAR HJ HO HSURV HIB HAT Hlx HAP. spc_unpack HY.
assert (K : astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) [] pn (Some x) /\
  atail_vis SEGS W' mem' (pn + Z.of_nat (length x))) by (eapply spc_arg_kept; eassumption).
destruct K as [H1 H2]. split; [exact H1 | intros y Hy; injection Hy as <-; exact H2].
Qed.

Lemma spc_seg_entry : forall ly S W regs mem md ch pn max name R O,
spc_pre B MT ly S W regs mem md ch pn max name R O ->
spc_cont_J B MT ly S W regs mem md R O pn name max ->
SRr SEGS W (cfg_at SEGS (BASE + AF_sup_pool_config) regs mem md) (spc_goal B MT ly S W regs mem md R O name max).
Proof.
intros ly S W regs mem md ch pn max name R O HPRE HCONT. unfold spc_cont_J in HCONT.
spc_unpack HY.
pose proof HPRE as (HFN & HFR0 & HROD & HRO & H10 & Hpn & H11 & Hmax & HSTR & HREP & HFR8 & HEV & HLIVE & HMOK).
destruct HSTR as (x & -> & HIB & HAT & Hlx & HAP).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKv : SUP_POOL_CONFIG_STK = 16592) by (vm_compute; reflexivity).
assert (WR : REC_CALLS_FREE_STK = 16496) by (vm_compute; reflexivity).
rewrite HSTKv in Hpres, Hslo, Hbot.
assert (Hsp : 2 ^ 46 + 64 <= spZ regs <= 2 ^ 47) by lia.
destruct (spc_rep_ncalls B ly S _ R O HREP) as [HNC Hlen16].
pose proof (spc_slot_okR R Hlen16) as HcOK.
set (n := Z.of_nat (length (r_calls R))) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
destruct (spc_entry_seed B LAWS TL HB VOBJS ly S W mem md regs n (spc_slot R) HAR ltac:(lia) ltac:(lia) Hsp16
  ltac:(intros a Ha; apply Hpres; lia) Hn HcOK HNC
  ltac:(intros a Ha; apply (cmd_prog_writable ly S W mem md a HAR); apply recb_grec_in;
        unfold A_G_REC, REC_SIZE, OFF_NCALLS in *; lia)
  ltac:(intros a Ha; apply (cmd_prog_writable ly S W mem md a HAR); exact (spc_slot_PG _ a HcOK Ha))) as [HS0 SHOK].
set (E := Eimg (Ereg regs (spc_extra regs n (spc_slot R)))) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
destruct (spc_E_lit regs regs n (spc_slot R)) as (E32 & E33 & E34). fold E in E32, E33, E34.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by exact (spc_E_reg regs regs n (spc_slot R)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (EG : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC).
{ unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite (spc_grec_val VOBJS). reflexivity. }
assert (EGu : bv_unsigned (ew E (A_OBJ 44)) = A_G_REC) by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (EGu' : bv_unsigned (ew E 285) = A_G_REC) by exact EGu.
assert (ES : ew E (A_OBJ 51) = Z_to_bv 64 A_REC_SPILL).
{ unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite (spc_spill_val VOBJS). reflexivity. }
(* the meter's terms after record() are not negative *)
assert (HMN : 0 <= mo_free MT /\ (forall k, 0 <= k -> 0 <= mo_malloc MT k))
  by (split; [exact (mo_free_nonneg MT MTL) | exact (mo_malloc_nonneg MT MTL)]).
assert (XMX : 0 <= XM_XSTRDUP MT (sarg (Some x))) by (unfold XM_XSTRDUP; apply (proj2 HMN); lia).
assert (XMI : 0 <= XM_ARG_I MT max) by (unfold XM_ARG_I, XM_XSTRDUP; apply (proj2 HMN); lia).
assert (XMA : 0 <= XM_ANSWER MT (snd (sup_pool_config_m R (Some x) max))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP.
  pose proof (proj2 HMN (Z.of_nat (length (snd (sup_pool_config_m R (Some x) max))) + 1) ltac:(lia)). lia. }
(* the entry segment never touches the slot: drop its region, so that every byte of record.spill is kept *)
pose proof (st_ok_pi_submem E ss_spc0 _ spc_rsE HS0
  ltac:(change (ss_mem ss_spc0) with spc_rs0; unfold spc_rsE, spc_rs0; submem_tac) ltac:(vm_compute; reflexivity)) as HS.
clear HS0.
pose proof (ajournal_init SEGS B SUP_POOL_CONFIG_STK (spc_FP O) ly S W regs mem md ch HFN) as HJ.
unfold cfg_at, w64.
(* 0x8bcfc .. 0x8bd40: the prologue, g_rec.ncalls loaded, up to `bne a2,a3` *)
paj_run_tok RUN HS HJ SHOK SPC_SPAN.
{ awr_ok_tac; [exact Usp|].
  eapply awr_ok_cons_gen; [reflexivity | exact EGu | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
    apply spc_awr_grec; unfold OFF_NCALLS, REC_SIZE in *; lia |].
  apply awr_ok_nil. }
spc_md.
spc_name_run HS ms1 HFr1.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha H1 H2. apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms1)
    (fun a => spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFr1);
  [spc_winA Usp EGu' | exact Ha | tauto]. }
psrr_branch_tok RUN BR HS SHOK SPC_SPAN.
- (* g_rec.ncalls <> 16: record() takes g_rec.calls[ncalls] and sets ncalls := ncalls + 1 *)
  assert (Hn16 : (length (r_calls R) < 16)%nat).
  { rewrite branch_ne_U, (U_atom E 33 n E33) in Hc by lia. rewrite U_SLit in Hc.
    rewrite (YP0m.zcanon_small 16) in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc. unfold n in Hc. lia. }
  assert (Hlt : Nat.ltb (length (r_calls R)) 16 = true) by (apply Nat.ltb_lt; exact Hn16).
  assert (Hcv : spc_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * n) by (unfold spc_slot; rewrite Hlt; reflexivity).
  assert (Hsf : rec_spill_frees R = 0) by (unfold rec_spill_frees; rewrite Hlt; reflexivity).
  assert (HRB : spc_RB R = R) by (unfold spc_RB; rewrite Hlt; reflexivity).
  (* 0x8bd40 .. 0x8bd78: ncalls := n + 1, s1 := g_rec + 16 + 56 n *)
  paj_run_to_tok RUNTO HS HJ SHOK SPC_SPAN SPC_JOIN.
  { awr_ok_tac; [exact Usp|].
    eapply awr_ok_cons_gen; [reflexivity | exact EGu | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
      apply spc_awr_grec; unfold OFF_NCALLS, REC_SIZE in *; lia |].
    apply awr_ok_nil. }
  pmkst HS. spc_md.
  spc_name_run HS msJ HFrJ.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem msJ) a = rdW W mem a).
  { intros a Ha H1 H2. rewrite <- (KEEP1 a Ha H1 H2).
    apply (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms1) (ms_mem msJ)
      (fun a => spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFrJ);
    [spc_winA Usp EGu' | exact Ha | tauto]. }
  spc_region HS 0%nat HRs. spc_region HS 3%nat HRn.
  assert (HFRM : spc_frame_at (mrestrict (w_H W) (ms_mem msJ)) (spZ regs) regs)
    by exact (spc_frame_of_region E W (ms_mem msJ) (spZ regs) regs HRs Usp EE).
  assert (HNC1 : aval_mem (rdW W (ms_mem msJ)) (A_G_REC + OFF_NCALLS) 4 (n + 1)).
  { apply (aval_mem_view SEGS (w_H W) (ms_mem msJ)). change 4%nat with (N.to_nat 4).
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 1) _ HRn EGu' ltac:(cbn; tauto)); [| cbn; lia | cbn; lia].
    apply spc_denot_U. rewrite U_SOff, E33, unsigned_lit_small by lia. apply YP0m.zcanon_small. lia. }
  spc_reg HS (2%bv : bv 5) Q2. spc_reg HS (8%bv : bv 5) Q8. spc_reg HS (9%bv : bv 5) Q9.
  spc_reg HS (18%bv : bv 5) Q18. spc_reg HS (20%bv : bv 5) Q20.
  destruct (spc_argK _ _ O ly S W mem md _ ly S W (ms_mem msJ) _ _ pn x HAR HJ (spc_rep_in B ly S _ R O HREP)
    (fun pk Hpk _ => Hpk) HIB HAT Hlx HAP) as [HA1 HA2].
  apply (HCONT ly S (rdW W mem) ly S W (ms_mem msJ) _ (ms_regs msJ) O []).
  unfold spc_midJ. cbv zeta.
  split; [rewrite Hsf; exact HJ|].
  split; [intros pk; split; [intros H; split; [exact H | intros []] | intros [H _]; exact H]|].
  split; [intros pk []|].
  split; [intros pk; split; [intros H; split; [exact H | intros []] | intros [H _]; exact H]|].
  split; [intros Hf; exfalso; apply Hf; reflexivity|].
  split; [lia|].
  split; [rewrite Hsf, Z.mul_0_l; exact (mle_start MT S MTL)|].
  split; [exact HFRM|].
  split; [rewrite HRB; exact HREP|].
  split.
  { intros a Ha Hnc _. apply KEEP; [unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia
      | unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia | exact (Hnc Hn16)]. }
  split.
  { intros [p k] i Hpk Hi. cbn [fst snd] in *.
    destruct (spc_rep_own B ly S _ R O HREP (p, k) Hpk) as (Hk0 & Hap1 & _). cbn [fst snd] in Hap1.
    pose proof (spc_rep_in B ly S _ R O HREP (p, k) Hpk) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hin) as (_ & H4096 & Hpc & _).
    pose proof (req_size_pos k ltac:(lia)) as [_ Hrq].
    apply KEEP; [lia | lia | unfold iv_apart, A_G_REC, REC_SIZE, OFF_NCALLS in *; lia]. }
  split; [intros _; exact HNC1|].
  split; [exact HA1|]. split; [exact HA2|].
  split; [rewrite Q2; apply spc_denot_U; rewrite U_SOff, Usp; apply YP0m.zcanon_small; lia|].
  split; [rewrite Q8, spc_soff0, (EE 11%nat 11%bv eq_refl); exact H11|].
  split; [rewrite Q9, Hcv; exact (spc_denot_slot E n E33 EG ltac:(unfold n in *; lia))|].
  split; [rewrite Q18, spc_soff0, (EE 10%nat 10%bv eq_refl); exact H10|].
  split; [rewrite Q20, spc_soff0, E32; reflexivity|].
  intros r Hr. cbv [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [match goal with |- getr _ ?rr = _ => spc_reg HS rr Qr end; rewrite Qr, spc_soff0; apply EE; reflexivity|]).
  destruct Hr.
- (* g_rec.ncalls = 16: record() frees the spill's arguments by rec_calls_free(&record.spill, 1) *)
  assert (Hn16 : length (r_calls R) = 16%nat).
  { rewrite branch_ne_U, (U_atom E 33 n E33) in Hc by lia. rewrite U_SLit in Hc.
    rewrite (YP0m.zcanon_small 16) in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc. unfold n in Hc. lia. }
  assert (Hge : Nat.ltb (length (r_calls R)) 16 = false) by (rewrite Hn16; reflexivity).
  assert (Hcv : spc_slot R = A_REC_SPILL) by (unfold spc_slot; rewrite Hge; reflexivity).
  assert (HRB : spc_RB R = set_spill R (fst (r_spill R), [])) by (unfold spc_RB; rewrite Hge; reflexivity).
  (* 0x8bd40 .. 0x8bd54: s1 := &record.spill, the call of rec_calls_free(s1, 1) *)
  paj_run_tok RUN HS HJ SHOK SPC_SPAN.
  { awr_ok_tac; [exact Usp|].
    eapply awr_ok_cons_gen; [reflexivity | exact EGu | intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
      apply spc_awr_grec; unfold OFF_NCALLS, REC_SIZE in *; lia |].
    apply awr_ok_nil. }
  pmkst HS. spc_md.
  spc_name_run HS msC HFrC.
  assert (KEEPw : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) -> rdW W (ms_mem msC) a = rdW W mem a).
  { intros a Ha H1 H2. rewrite <- (KEEP1 a Ha H1 H2).
    apply (kept_of_frame (segs := SEGS) E _ (w_H W) (ms_mem ms1) (ms_mem msC)
      (fun a => spZ regs - 64 <= a < spZ regs \/ A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) HFrC);
    [spc_winA Usp EGu' | exact Ha | tauto]. }
  spc_region HS 0%nat HRs. spc_region HS 3%nat HRn.
  assert (HNCc : aval_mem (rdW W (ms_mem msC)) (A_G_REC + OFF_NCALLS) 4 n).
  { apply (aval_mem_view SEGS (w_H W) (ms_mem msC)). change 4%nat with (N.to_nat 4).
    apply (field_of_region E _ 285 A_G_REC _ _ _ _ _ 8 4 (SOff 33 0) _ HRn EGu' ltac:(cbn; tauto)); [| cbn; lia | cbn; lia].
    rewrite spc_soff0. exact E33. }
  (* g_rec.ncalls holds n before and after: every byte outside the frame is kept *)
  assert (KEEPc : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) -> rdW W (ms_mem msC) a = rdW W mem a).
  { intros a Ha H1. destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS)) as [Hl | Hl];
    [|destruct (Z_lt_le_dec a (A_G_REC + OFF_NCALLS + 4)) as [Hh | Hh]].
    - apply KEEPw; [exact Ha | exact H1 | lia].
    - replace a with ((A_G_REC + OFF_NCALLS) + Z.of_nat (Z.to_nat (a - (A_G_REC + OFF_NCALLS)))) by lia.
      rewrite (HNCc (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)), (HNC (Z.to_nat (a - (A_G_REC + OFF_NCALLS))) ltac:(lia)).
      reflexivity.
    - apply KEEPw; [exact Ha | exact H1 | lia]. }
  assert (HFRc : spc_frame_at (mrestrict (w_H W) (ms_mem msC)) (spZ regs) regs)
    by exact (spc_frame_of_region E W (ms_mem msC) (spZ regs) regs HRs Usp EE).
  (* the recorder at the call: g_rec, record.spill and the recorder's blocks are untouched by the prologue *)
  assert (HREPc : rec_repA B ly S (rdW W (ms_mem msC)) R O).
  { apply (spc_rep_keep B ly S ly S (rdW W mem) (rdW W (ms_mem msC)) R O HREP (spc_rep_in B ly S _ R O HREP)).
    - intros a Ha. apply KEEPc; unfold A_G_REC, REC_SIZE in *; lia.
    - intros a Ha. apply KEEPc; unfold A_REC_SPILL, SC_SIZE in *; lia.
    - intros [p k] i Hpk Hi. cbn [fst snd] in *.
      destruct (spc_rep_own B ly S _ R O HREP (p, k) Hpk) as (Hk0 & _).
      pose proof (spc_rep_in B ly S _ R O HREP (p, k) Hpk) as Hin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hin) as (_ & H4096 & Hpc & _).
      pose proof (req_size_pos k ltac:(lia)) as [_ Hrq].
      apply KEEPc; lia. }
  destruct HREPc as (QL & HAc & HOc).
  destruct (spc_spill_rcf_pre (ablocks B ly S) (rdW W (ms_mem msC)) R QL HAc) as (HLP6 & HLP & HSPN & HSPA & HSPND).
  destruct (spc_spill_split (ablocks B ly S) (rdW W (ms_mem msC)) R QL O HAc HOc) as [HPO HO0].
  assert (HPin : forall pk, In pk (l_spill QL) -> In pk (ablocks B ly S))
    by (intros pk Hpk; exact (spc_rep_in B ly S _ R O HREP pk (HPO pk Hpk))).
  assert (Hsf : rec_spill_frees R = Z.of_nat (length (l_spill QL))) by (unfold rec_spill_frees; rewrite Hge, HLP; reflexivity).
  assert (HEVk : EV_REC_CALLS_FREE [l_spill QL] = Z.of_nat (length (l_spill QL)))
    by (unfold EV_REC_CALLS_FREE; cbn [concat]; rewrite app_nil_r; reflexivity).
  assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W (ms_mem msC)))
    by exact (spc_aro B MT HY _ _ O ly S W mem md _ _ _ _ _ _ _ HAR (spc_rep_in B ly S _ R O HREP) HJ HROD).
  (* the registers at the call *)
  spc_reg HS (1%bv : bv 5) Q1. spc_reg HS (2%bv : bv 5) Q2. spc_reg HS (3%bv : bv 5) Q3. spc_reg HS (4%bv : bv 5) Q4.
  spc_reg HS (8%bv : bv 5) Q8. spc_reg HS (9%bv : bv 5) Q9. spc_reg HS (10%bv : bv 5) Q10. spc_reg HS (11%bv : bv 5) Q11.
  spc_reg HS (18%bv : bv 5) Q18. spc_reg HS (20%bv : bv 5) Q20.
  assert (HRA : getr (ms_regs msC) 1 = Z_to_bv 64 (BASE + SPC_RCF)) by (rewrite Q1; apply codeptr_val; exact HEI).
  assert (Q2' : getr (ms_regs msC) 2 = w64 (spZ regs - 64))
    by (rewrite Q2; apply spc_denot_U; rewrite U_SOff, Usp; apply YP0m.zcanon_small; lia).
  assert (Q3' : getr (ms_regs msC) 3 = getr regs 3) by (rewrite Q3, spc_soff0; apply EE; reflexivity).
  assert (Q4' : getr (ms_regs msC) 4 = getr regs 4) by (rewrite Q4, spc_soff0; apply EE; reflexivity).
  assert (Q8' : getr (ms_regs msC) 8 = w64 max) by (rewrite Q8, spc_soff0, (EE 11%nat 11%bv eq_refl); exact H11).
  assert (Q9' : getr (ms_regs msC) 9 = w64 A_REC_SPILL) by (rewrite Q9, spc_soff0; exact ES).
  assert (Q10' : getr (ms_regs msC) 10 = w64 A_REC_SPILL) by (rewrite Q10, spc_soff0; exact ES).
  assert (Q11' : getr (ms_regs msC) 11 = w64 (Z.of_nat (length [l_spill QL]))) by (rewrite Q11; reflexivity).
  assert (Q18' : getr (ms_regs msC) 18 = w64 pn) by (rewrite Q18, spc_soff0, (EE 10%nat 10%bv eq_refl); exact H10).
  assert (Q20' : getr (ms_regs msC) 20 = w64 SB) by (rewrite Q20, spc_soff0, E32; reflexivity).
  assert (Qhi : forall r, In r [3; 4; 22; 23; 24; 25; 26; 27] ->
    getr (ms_regs msC) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. cbv [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [match goal with |- getr _ ?rr = _ => spc_reg HS rr Qr end; rewrite Qr, spc_soff0; apply EE; reflexivity|]).
    destruct Hr. }
  assert (SIGr : SIG CS_rec_calls_free = BASE + AF_rec_calls_free).
  { rewrite (SIGP CS_rec_calls_free ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))). f_equal. }
  rewrite SIGr.
  eapply SRr_bind.
  { eapply (cl_callS_wide B LAWS W (ms_regs msC) (ms_mem msC) _ SUP_POOL_CONFIG_STK (spZ regs) (spc_FP O) ly S W mem md []
      ly S _ 0 REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill QL]) (EV_REC_CALLS_FREE [l_spill QL]) (-64)
      (getr (ms_regs msC) 1) [] _ HJ).
    - unfold spZ at 1. rewrite Q2'. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - reflexivity.
    - lia.
    - rewrite WR. lia.
    - rewrite WR, HSTKv. lia.
    - rewrite Q3'. exact Hgp.
    - rewrite Q4'. exact Htp.
    - reflexivity.
    - rewrite HRA. apply ret_ok_codeptr_v; [unfold SPC_RCF, AF_sup_pool_config; lia | reflexivity].
    - rewrite HRA, unsigned_lit_small by (unfold SPC_RCF, AF_sup_pool_config; lia). unfold SPC_RCF, AF_sup_pool_config. lia.
    - unfold s0Z. rewrite Q8'. apply spc_achain_max; [exact Hmax | lia].
    - intros HPRE1.
      assert (HT := TRCF fx ly S W (ms_regs msC) (ms_mem msC) _ [] A_REC_SPILL [l_spill QL] HPRE1 HRODc Q10' Q11'
        ltac:(cbn [length]; lia)
        ltac:(right; left; unfold A_REC_SPILL, SC_SIZE, CALL_SIZE; cbn [length Z.of_nat]; lia)).
      unfold apost_base, cfg_at, w64 in HT. apply HT.
      + unfold A_REC_SPILL. reflexivity.
      + intros i P Hi. destruct i as [|i]; [|destruct i; discriminate Hi]. cbn [nth_error] in Hi. injection Hi as <-.
        split; [exact HLP6|]. split.
        * cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. exact HSPN.
        * intros a pk Ha. destruct (HSPA a pk Ha) as [G1 G3]. split; [|exact G3].
          cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. exact G1.
      + cbn [concat]. rewrite app_nil_r. exact HSPND.
      + rewrite HEVk, <- Hsf. unfold EV_SUP_POOL_CONFIG, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia.
      + apply (mo_ok_le MT MTL S _ (XM_SUP_POOL_CONFIG MT R (Some x) max) HMOK).
        unfold XM_REC_CALLS_FREE, XM_SUP_POOL_CONFIG. cbn [concat]. rewrite app_nil_r, <- Hsf. lia.
    - intros a Ha. destruct (spc_rcf_fp_inv (l_spill QL) a Ha) as [Hs | (p & k & Hin & Hr)].
      + apply (spc_awr_slot B HB cmd_prog_img _ _ _ _ _ _ _ _ A_REC_SPILL a (or_intror eq_refl)).
        unfold CALL_SIZE in *. lia.
      + right; left. split.
        * replace a with (p + (a - p)) by lia. apply (spc_inFP_blk O p k (a - p)); [exact (HPO _ Hin) | lia].
        * exists p, k. split; [exact (HPin _ Hin) | exact Hr].
    - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. rewrite HSTKv in Hw.
      destruct (spc_rcf_fp_inv (l_spill QL) a Ha) as [Hs | (p & k & Hin & Hr)]; [unfold A_REC_SPILL in Hs; lia|].
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR (HPin _ Hin)) as (_ & _ & Hpc & _). lia. }
  (* back at 0x8bd58 *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJr & HP2 & HK2).
  destruct HK2 as (HPERM & _ & _ & _ & _ & HRSP & _ & _ & HMLE).
  pose proof (HRSP R QL HAc eq_refl eq_refl) as HREP2.
  cbn [concat] in HPERM. rewrite app_nil_r in HPERM.
  rewrite HRA.
  (* 0x8bd58: `j 0x8bd78`, record()'s arms meet *)
  destruct (spc_seed0 W2 regs2 mem2 SPC_RCF) as [HS2 SHOK2].
  assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 SPC_SPAN SPC_JOIN.
  { apply awr_ok_nil. }
  pmkst HS2. spc_md.
  spc_name_run HS2 msJ HFrJ.
  assert (KEEP3 : forall a, rdW W2 (ms_mem msJ) a = rdW W2 mem2 a).
  { apply (spc_frame_nowin _ _ _ _ _ HFrJ). intros a (r & Hr & _). vm_compute in Hr. destruct Hr. }
  assert (HAE2 : env_agree 32 (Ereg regs2 []) (Eimg (Ereg regs2 []))).
  { split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS2 HAE2 ltac:(vm_compute; reflexivity)) as HPT3.
  cbn [ms_regs restrict] in HPT3.
  pose proof (aregs_preserved_trans _ _ _ HP2 HPT3) as HPP.
  assert (HSURV : forall pk, In pk (ablocks B ly S) -> ~ In pk O -> In pk (ablocks B ly2 S2)).
  { intros pk Hpk HnO. apply (Permutation_in _ HPERM) in Hpk. apply in_app_or in Hpk as [H|H]; [exact H|].
    exfalso. exact (HnO (HPO pk H)). }
  destruct (spc_argK _ _ O ly S W mem md _ ly2 S2 W2 (ms_mem msJ) _ _ pn x HAR HJ2 (spc_rep_in B ly S _ R O HREP)
    HSURV HIB HAT Hlx HAP) as [HA1 HA2].
  pose proof HJr as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
  apply (HCONT ly2 S2 (rdW W2 mem2) ly2 S2 W2 (ms_mem msJ) _ (ms_regs msJ)
    (concat (l_calls QL) ++ oblk (l_answer QL) ++ oblk (l_reply QL)) (l_spill QL)).
  unfold spc_midJ. cbv zeta.
  split; [replace (rec_spill_frees R) with (0 + EV_REC_CALLS_FREE [l_spill QL]) by (rewrite HEVk, Hsf; lia); exact HJ2|].
  split.
  { intros pk. pose proof (Stdlib.Sorting.Permutation.Permutation_NoDup HPERM (recb_ablocks_nodup_m B ly S W mem md HAR)) as HND2.
    split.
    - intros H2. split; [apply (Permutation_in _ (Permutation_sym HPERM)); apply in_or_app; left; exact H2|].
      intros HP. exact (list_nodup_app_disj _ _ pk HND2 H2 HP).
    - intros [H1 HnP]. apply (Permutation_in _ HPERM) in H1. apply in_app_or in H1 as [H1|H1]; [exact H1 | contradiction]. }
  split; [exact HPO|].
  split; [exact HO0|].
  split; [intros _; lia|].
  split.
  { rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPERM), bsum_app.
    assert (0 <= bsum (l_spill QL)).
    { apply spc_bsum_nonneg. intros pk Hpk. pose proof (spc_rep_own B ly S _ R O HREP pk (HPO pk Hpk)) as (H0 & _). lia. }
    lia. }
  split; [rewrite Hsf; unfold XM_REC_CALLS_FREE in HMLE; cbn [concat] in HMLE; rewrite app_nil_r in HMLE; exact HMLE|].
  split.
  { apply (spc_frame_kept (w_H W) (w_H W2) (ms_mem msC) (ms_mem msJ) (spZ regs) regs HFRc).
    intros a Ha. rewrite KEEP3. apply G1; [lia | rewrite WR; lia |].
    intros Hf. destruct (spc_rcf_fp_inv (l_spill QL) a Hf) as [Hs | (p & k & Hin & Hr)]; [unfold A_REC_SPILL in Hs; lia|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR (HPin _ Hin)) as (_ & _ & Hpc & _). lia. }
  split; [rewrite HRB; exact HREP2|].
  split; [intros a _ _ _; apply KEEP3|].
  split; [intros pk i _ _; apply KEEP3|].
  split; [intros Hlt; lia|].
  split; [exact HA1|]. split; [exact HA2|].
  split; [etransitivity; [exact (HPP 2 ltac:(unfold acallee_saved; lia)) | exact Q2']|].
  split; [etransitivity; [exact (HPP 8 ltac:(unfold acallee_saved; lia)) | exact Q8']|].
  split; [etransitivity; [exact (HPP 9 ltac:(unfold acallee_saved; lia)) | rewrite Hcv; exact Q9']|].
  split; [etransitivity; [exact (HPP 18 ltac:(unfold acallee_saved; lia)) | exact Q18']|].
  split; [etransitivity; [exact (HPP 20 ltac:(unfold acallee_saved; lia)) | exact Q20']|].
  intros r Hr. assert (Hcs : acallee_saved r) by (cbv [In] in Hr; unfold acallee_saved; lia).
  rewrite (HPP r Hcs). exact (Qhi r Hr).
Qed.

End e.
End f.
End d.
