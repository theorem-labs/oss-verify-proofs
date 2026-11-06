(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: record()'s spill arm of descriptors_add's ASan walk (plugin-hostd/fuzz_command):
   from the entry to the join of record()'s two arms through the call of rec_calls_free, after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment through a program call and back). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c mix_call_c descriptors_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas descriptors_add_s1 descriptors_add_m descriptors_add_s2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
#[local] Notation LAWS := (AR_laws_ok SEGS B).
(* descriptors_add_s2.v's section hypotheses, in its order (so its lemmas apply with them) *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis RRO : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
(* this arm's own: the statement's rec_calls_free contract *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
#[local] Set Default Proof Using "All".
(* descriptors_add_s2.v's section hypotheses as one prefix *)
#[local] Notation S2 f := (f B MT TL HB VOBJS cmd_prog_img cmd_prog_writable SIGP TXSTRDUP TMIX_CALL MTL
  cmd_ro_ok_of_aro RRO RELRO_IMG cmd_ro_prog_apart cmd_heap_tail_vis).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the entry of rec_calls_free, as the listing's symbol table names it *)
Lemma da_sig_rec_calls_free : SIG CS_rec_calls_free = BASE + AF_rec_calls_free.
Proof. rewrite (SIGP CS_rec_calls_free ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.

(* the footprint rec_calls_free names for the spill slot: the slot's nargs field and the blocks it frees
   (lib/A/Prog/rec_calls_free_c.v:39-41); after lv2_refusals_forget.v's lrf_inFP_inv *)
Lemma da_rcf_fp_in : forall (P : list (Z * Z)) a, inFP (rcf_fp A_REC_SPILL [P]) a ->
(A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/ (exists pn, In pn P /\ fst pn <= a < fst pn + req_size (snd pn)).
Proof.
intros P a (r & Hr & Ha). unfold rcf_fp in Hr. rewrite in_app_iff in Hr. destruct Hr as [Hr | Hr].
- left. cbn [length seq map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd Z.of_nat] in Ha.
  unfold CALL_OFF_NARGS, SC_SIZE, CALL_SIZE in *. lia.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hin). cbn [fst snd] in Ha.
  cbn [concat] in Hin. rewrite app_nil_r in Hin. exists (q, m). split; [exact Hin | cbn [fst snd]; exact Ha].
Qed.
(* the entry segment's own runs write only the frame below the caller's sp and g_rec.ncalls
   (descriptors_add_s2.v's da_keep_win, with this segment's windows) *)
Lemma da_keep_fr : forall E rs (H : word -> bool) (m m' : word -> option byte) (sp0 : Z),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall a, in_wrange E rs a -> (sp0 - 64 <= a < sp0) \/ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' sp0 Hfr Hw a Ha N1 N2. apply (aview_eq_of SEGS). apply Hfr.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros Hin. destruct (Hw a Hin) as [H1 | H1]; [exact (N1 H1) | exact (N2 H1)].
Qed.
(* one recorded call follows a reader that keeps the slot's 56 bytes and the live blocks *)
Lemma da_call_kept_rd : forall bl (rd rd' : reader) c0 P a, acall_at bl rd a c0 P ->
(forall j, 0 <= j < CALL_SIZE -> rd' (a + j) = rd (a + j)) ->
(forall q m i, In (q, m) bl -> 0 <= i < m -> rd' (q + i) = rd (q + i)) ->
acall_at bl rd' a c0 P.
Proof.
intros bl rd rd' c0 P a (H1 & H2 & H3 & Vfn & Vna & Hnd & Hargs) K KB.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split.
{ apply (aval_mem_kept rd); [exact Vfn|]. intros k Hk. rewrite <- !Z.add_assoc. apply K. cbv [CALL_OFF_FN CALL_SIZE]. lia. }
split.
{ apply (aval_mem_kept rd); [exact Vna|]. intros k Hk. rewrite <- !Z.add_assoc. apply K. cbv [CALL_OFF_NARGS CALL_SIZE]. lia. }
split; [exact Hnd|].
intros k s pn Hs Hpn. destruct (Hargs k s pn Hs Hpn) as (Vp & Hp0 & Hin & Hlen & Hstr).
assert (Hk6 : (k < length (snd c0))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
split.
{ apply (aval_mem_kept rd); [exact Vp|]. intros j Hj. rewrite <- !Z.add_assoc. apply K. cbv [CALL_OFF_ARGS CALL_SIZE]. lia. }
split; [exact Hp0|]. split; [exact Hin|]. split; [exact Hlen|].
apply (rastr_kept rd); [exact Hstr|]. intros i Hi. destruct pn as [p n]. cbn [fst snd] in *.
apply (KB p n i Hin). lia.
Qed.
(* the recorder's representation follows a reader that keeps g_rec, record.spill and the live blocks
   (descriptors_add_m.v's aval_mem_kept / rastr_kept / rabytes_kept, one conjunct at a time) *)
Lemma da_arep_kept : forall bl (rd rd' : reader) R0 Q0,
arep_at bl rd A_G_REC A_REC_SPILL R0 Q0 ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall q m i, In (q, m) bl -> 0 <= i < m -> rd' (q + i) = rd (q + i)) ->
arep_at bl rd' A_G_REC A_REC_SPILL R0 Q0.
Proof.
intros bl rd rd' R0 Q0 (Hg8 & Hs8 & Hap & HC & HA & HR & HSC & HOWN) KG KS KB.
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
pose proof HC as (Hl16 & HlQ & Vnc & HCA & HSP & HSPL).
split.
{ split; [exact Hl16|]. split; [exact HlQ|]. split.
  { apply (aval_mem_kept rd); [exact Vnc|]. intros k Hk. apply KG. cbv [OFF_NCALLS REC_SIZE]. lia. }
  split.
  { intros i c0 P Hi HiQ. destruct (HCA i c0 P Hi HiQ) as [Hc Hf]. split; [|exact Hf].
    assert (Hi16 : (i < length (r_calls R0))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    apply (da_call_kept_rd bl rd); [exact Hc | | exact KB].
    intros j Hj. apply KG. cbv [OFF_CALLS CALL_SIZE REC_SIZE] in *. lia. }
  split; [|exact HSPL].
  apply (da_call_kept_rd bl rd); [exact HSP | | exact KB].
  intros j Hj. apply KS. cbv [SC_SIZE CALL_SIZE] in *. lia. }
split.
{ destruct (r_answer R0) as [x|]; destruct (l_answer Q0) as [[p n]|]; try exact HA.
  - destruct HA as (Vp & Hp0 & Hin & Hlen & Hstr & Hx). cbn [fst snd] in *.
    split; [apply (aval_mem_kept rd); [exact Vp|]; intros k Hk; apply KG; cbv [OFF_ANSWER REC_SIZE]; lia|].
    split; [exact Hp0|]. split; [exact Hin|]. split; [exact Hlen|]. split; [|exact Hx].
    apply (rastr_kept rd); [exact Hstr|]. intros i Hi. apply (KB p n i Hin). lia.
  - apply (aval_mem_kept rd); [exact HA|]. intros k Hk. apply KG. cbv [OFF_ANSWER REC_SIZE]. lia. }
split.
{ destruct (r_reply R0) as [x|]; destruct (l_reply Q0) as [[p n]|]; try exact HR.
  - destruct HR as (Vp & Vsz & Hp0 & Hne & Hin & Hlen & Hby & Hx). cbn [fst snd] in *.
    split; [apply (aval_mem_kept rd); [exact Vp|]; intros k Hk; apply KG; cbv [OFF_REPLY REC_SIZE]; lia|].
    split; [apply (aval_mem_kept rd); [exact Vsz|]; intros k Hk; apply KG; cbv [OFF_REPLY_SIZE REC_SIZE]; lia|].
    split; [exact Hp0|]. split; [exact Hne|]. split; [exact Hin|]. split; [exact Hlen|]. split; [|exact Hx].
    apply (rabytes_kept rd); [exact Hby|]. intros i Hi. apply (KB p n i Hin). lia.
  - destruct HR as [V1 V2]. split.
    + apply (aval_mem_kept rd); [exact V1|]. intros k Hk. apply KG. cbv [OFF_REPLY REC_SIZE]. lia.
    + apply (aval_mem_kept rd); [exact V2|]. intros k Hk. apply KG. cbv [OFF_REPLY_SIZE REC_SIZE]. lia. }
split; [|exact HOWN].
pose proof HSC as (V1 & V2 & V3 & V4 & V5 & B1 & B2 & B3 & B4 & B5).
split; [apply (aval_mem_kept rd); [exact V1|]; intros k Hk; apply KG; cbv [OFF_REFUSE REC_SIZE]; lia|].
split; [apply (aval_mem_kept rd); [exact V2|]; intros k Hk; apply KG; cbv [OFF_CODE REC_SIZE]; lia|].
split; [apply (aval_mem_kept rd); [exact V3|]; intros k Hk; apply KG; cbv [OFF_NREPLIES REC_SIZE]; lia|].
split; [apply (aval_mem_kept rd); [exact V4|]; intros k Hk; apply KG; cbv [OFF_STATE REC_SIZE]; lia|].
split; [apply (aval_mem_kept rd); [exact V5|]; intros k Hk; apply KG; cbv [OFF_HOST REC_SIZE]; lia|].
repeat (split; [assumption|]). exact B5.
Qed.
(* the caller's saved registers stay in the frame when the frame's bytes are kept, across a change of world *)
Lemma da_frame_kept2 : forall (W W' : world SEGS) m m' sp0 regs,
(forall a, sp0 - 64 <= a < sp0 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
da_frame_at (mrestrict (w_H W) m) sp0 regs -> da_frame_at (mrestrict (w_H W') m') sp0 regs.
Proof.
intros W W' m m' sp0 regs HK Hfr j r Hj.
assert (Hj7 : (j < length da_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
cbn [length da_saved] in Hj7.
apply (val_mem_view SEGS (w_H W') m'). intros kk Hkk.
rewrite HK by lia.
exact (aval_mem_view SEGS (w_H W) m _ 8%nat _ (Hfr j r Hj) kk Hkk).
Qed.
(* the write ranges of the entry segment's region list: the frame (atom 2) and g_rec.ncalls (atom DA_GREC) *)
Ltac da_win0 U2 UG :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros a (r & Hin & Ha);
lazymatch type of Hin with In r ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
[ left; rewrite U2 in Ha; lia | lia | lia | right; rewrite UG in Ha; unfold OFF_NCALLS in *; lia ].

(* record()'s spill arm (ncalls = 16): 0x8ce34 .. 0x8ce88 the prologue, the load of g_rec.ncalls and the call
   rec_calls_free(&record.spill, 1); back at 0x8ce8c, `j` to the join (0x8ceac), where the join continuation K takes
   over *)
Lemma da_spill : forall ly S W (regs : bvmap 5 word) mem md ch (pu : Z) (uri : option (list byte)) (R : rstate)
  (O : list (Z * Z)),
afn_pre SEGS B DESCRIPTORS_ADD_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
getr regs 10 = w64 pu -> 0 <= pu < 2 ^ 64 ->
(exists x, uri = Some x /\
 in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pu x /\
 Z.of_nat (length x) + 1 <= LMAX + 1 /\
 Forall (fun qk => iv_apart pu (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O) ->
rec_repA B ly S (rdW W mem) R O ->
(16 <= length (r_calls R))%nat ->
st_nev S + EV_DESCRIPTORS_ADD R <= EV_MAX ->
mo_ok MT S (XM_DESCRIPTORS_ADD MT R uri) ->
da_join_K B MT ly S W regs mem md R uri O pu ->
SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_add) regs mem md)
 (apost_base SEGS B DESCRIPTORS_ADD_STK (da_FP O) regs ly S W mem md (EV_DESCRIPTORS_ADD R) (da_Q B MT ly S R uri O)).
Proof.
intros ly S W regs mem md ch pu uri R O HPRE HROD H10 Hpu HSTR HREP Hlen16 HEV HMOK HK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : DESCRIPTORS_ADD_STK = 16560) by reflexivity.
destruct HREP as (Q & HQ & HOQ).
pose proof HQ as (Hg8 & Hs8 & Hap & HCALLS & HANS & HREPL & HSCAL & HOWN).
pose proof HCALLS as (Hle16 & HlenQ & Vnc & HCA & HSPL & HSPLL).
assert (Hn16 : length (r_calls R) = 16%nat) by lia.
assert (Vnc16 : aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 16) by (rewrite Hn16 in Vnc; exact Vnc).
destruct (da_entry B TL HB VOBJS cmd_prog_img cmd_prog_writable ly S W mem md regs 16 16 16
  HAR Hstk Hpres Vnc16 ltac:(lia) ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B DESCRIPTORS_ADD_STK (da_FP O) ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (da_E0 regs 16)) by (unfold da_E0; apply Eimg_env).
assert (Usp : bv_unsigned (ew (da_E0 regs 16) 2) = spZ regs).
{ unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (UG : bv_unsigned (ew (da_E0 regs 16) DA_GREC) = A_G_REC).
{ rewrite (img_env_atomP (da_E0 regs 16) DA_GREC HEI ltac:(unfold DA_GREC, A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (da_grec_val B TL HB VOBJS cmd_prog_img cmd_prog_writable). apply unsigned_lit_small. unfold A_G_REC; lia. }
assert (UG285 : bv_unsigned (ew (da_E0 regs 16) 285) = A_G_REC) by (change 285%nat with DA_GREC; exact UG).
assert (E33 : ew (da_E0 regs 16) 33 = Z_to_bv 64 16).
{ unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (E34 : ew (da_E0 regs 16) 34 = Z_to_bv 64 A_REC_SPILL).
{ unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
unfold cfg_at.
paj_run_tok RUN HS HJ SHOK da_Bspan.
{ unfold ss_da0, da_rs0, stack_region, got_regionP, bcell_regionP, da_ncalls. cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact Usp | cbn [YP09.r_wlo]; rewrite HTS; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := DA_GREC); [reflexivity | exact UG | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  apply (da_awr_grec B TL HB VOBJS cmd_prog_img cmd_prog_writable). unfold OFF_NCALLS, REC_SIZE in *. lia. }
da_fold_md. rename HFr into HFr1. rename HG into HG1. clear HF.
(* 0x8ce74: `bne ncalls,16` - the table arm asks ncalls <> 16, which the seed's atom refutes *)
psrr_branch_tok RUN BR HS SHOK da_Bspan.
{ cbn [sv_denot] in Hc. rewrite E33 in Hc. vm_compute in Hc. discriminate Hc. }
(* 0x8ce78 .. 0x8ce88: s0 := &record.spill, a0 := s0, a1 := 1, and the call of rec_calls_free *)
paj_run_tok RUN HS HJ SHOK da_Bspan.
{ unfold da_rs0, stack_region, got_regionP, bcell_regionP, da_ncalls. cbn [ss_mem add_cond].
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact Usp | cbn [YP09.r_wlo]; rewrite HTS; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := DA_GREC); [reflexivity | exact UG | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  apply (da_awr_grec B TL HB VOBJS cmd_prog_img cmd_prog_writable). unfold OFF_NCALLS, REC_SIZE in *. lia. }
da_fold_md.
(* what the two runs kept: every byte off the frame and off g_rec.ncalls *)
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
  ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha N1 N2.
  rewrite (da_keep_fr _ _ _ _ _ (spZ regs) HFr ltac:(da_win0 Usp UG285) a Ha N1 N2).
  exact (da_keep_fr _ _ _ _ _ (spZ regs) HFr1 ltac:(da_win0 Usp UG285) a Ha N1 N2). }
assert (HPGr : forall a, Exists (in_zr a) recb_PG -> 0x10000 <= a < 0x606000)
  by (intros a HP; exact (pa_img_range a (cmd_prog_img a HP))).
assert (KPG : forall a, Exists (in_zr a) recb_PG -> ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) ->
  aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a HP N2. pose proof (HPGr a HP) as Hr. apply KP; [lia | rewrite HTS in Hslo; lia | exact N2]. }
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (proj1 (arep_lay_in _ _ _ _ R Q pn HQ (proj1 (HOQ pn) Hpn)))).
assert (HSPinQ : forall pn, In pn (l_spill Q) -> In pn (lay_blocks Q)).
{ intros pn Hpn. unfold lay_blocks. rewrite in_app_iff. right. rewrite in_app_iff. left. exact Hpn. }
assert (HSPin : forall pn, In pn (l_spill Q) -> In pn (ablocks B ly S))
  by (intros pn Hpn; exact (HO pn (proj2 (HOQ pn) (HSPinQ pn Hpn)))).
assert (HROFP : forall a, in_roP SEGS RLO RHI a -> ~ inFP (da_FP O) a).
{ intros a Hro (r & Hr & Ha). destruct (cmd_ro_prog_apart a Hro) as [Himg Hnp].
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
  - exact (Hnp (recb_grec_in a Ha)).
  - exact (Hnp (recb_spill_in a Ha)).
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q kk] & <- & Hin). cbn [fst snd] in Ha.
    apply (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
      (or_introl (ex_intro _ q (ex_intro _ kk (conj (HO _ Hin) Ha)))))). exact Himg. }
assert (KPB : forall q m i, In (q, m) (ablocks B ly S) -> 0 <= i < req_size m ->
  aview SEGS (w_H W) (ms_mem ms0) (q + i) = aview SEGS (w_H W) mem (q + i)).
{ intros q m i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR Hin) as (_ & H4096 & Hcl & _).
  assert (Hrg : q <= q + i < q + req_size m) by lia.
  assert (Hn : ~ Exists (in_zr (q + i)) recb_PG).
  { intros HP. apply (proj2 (al_client_img _ _ LAWS ly S W mem md (q + i) HAR
      (or_introl (ex_intro _ q (ex_intro _ m (conj Hin Hrg)))))). exact (cmd_prog_img _ HP). }
  apply KP; [lia | rewrite HTS in Hslo; lia |].
  intros Hnc. apply Hn. apply recb_grec_in. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
(* the spill slot's call record, at the memory the runs left *)
assert (Hspl_len : Z.of_nat (length (l_spill Q)) = rec_spill_frees R).
{ unfold rec_spill_frees. rewrite Hn16. cbn [Nat.ltb Nat.leb].
  pose proof HSPL as (_ & _ & HlenP & _). rewrite HlenP. reflexivity. }
assert (HEVps : EV_REC_CALLS_FREE [l_spill Q] = rec_spill_frees R).
{ unfold EV_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r. exact Hspl_len. }
assert (HXMps : XM_REC_CALLS_FREE MT [l_spill Q] = rec_spill_frees R * mo_free MT).
{ unfold XM_REC_CALLS_FREE. cbn [concat]. rewrite app_nil_r. rewrite Hspl_len. reflexivity. }
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (da_E0 regs 16) n = getr regs r).
{ intros n r Hn. unfold da_E0. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (U292 : ew (da_E0 regs 16) 292 = Z_to_bv 64 A_REC_SPILL).
{ change 292%nat with DA_SPILL.
  rewrite (img_env_atomP (da_E0 regs 16) DA_SPILL HEI ltac:(unfold DA_SPILL, A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (da_spill_val B TL HB VOBJS cmd_prog_img cmd_prog_writable). reflexivity. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
(* the frame (region 0) and g_rec.ncalls (region 3) of the symbolic state at the call *)
lazymatch type of HS with ?P ?E ?ssx ?msx => lazymatch ssx with ?sp ?ss0 ?pcx =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ss0) da_frameM) in
  assert (HRf : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms0)) r0)
    by exact (st_ok_region_nth E ssx msx 0 r0 HS ltac:(change (ss_mem ssx) with (ss_mem ss0); vm_compute; reflexivity));
  let r3 := eval vm_compute in (nth 3 (ss_mem ss0) da_frameM) in
  assert (HRn : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms0)) r3)
    by exact (st_ok_region_nth E ssx msx 3 r3 HS ltac:(change (ss_mem ssx) with (ss_mem ss0); vm_compute; reflexivity))
end end.
(* g_rec.ncalls still holds 16 at the call: the arm wrote no other value there *)
assert (HNCm : aval_mem (rdW W (ms_mem ms0)) (A_G_REC + OFF_NCALLS) 4 16).
{ apply (aval_mem_view SEGS).
  eapply (S2 da_field (da_E0 regs 16) _ DA_GREC A_G_REC _ 8 12 8 12 8 4 (SOff 33 0) 16);
  [ exact HRn | exact UG | repeat (first [left; reflexivity | right])
  | cbn [sv_denot]; rewrite E33, unsigned_lit_small by lia; reflexivity
  | change (8 * Z.of_N 4) with 32; lia | change (Z.of_N 4) with 4; lia
  | unfold OFF_NCALLS; lia | reflexivity ]. }
(* the caller's saved registers in the frame at the call *)
assert (HfrC : da_frame_at (mrestrict (w_H W) (ms_mem ms0)) (spZ regs) regs).
{ intros j r Hj.
  assert (Hj7 : (j < length da_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length da_saved] in Hj7.
  assert (Hj6 : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6)%nat) by lia.
  repeat (destruct Hj6 as [-> | Hj6]); [| | | | | | subst j];
  cbn [nth_error da_saved] in Hj; injection Hj as <-;
  lazymatch goal with |- val_mem _ _ (spZ regs - 8 - 8 * Z.of_nat ?jj) _ (bv_unsigned (getr regs (Z_to_bv 5 ?rz))) =>
    eapply (S2 da_field (da_E0 regs 16) _ 2%nat (spZ regs) _ (-64) 0 (-64) 0 (-8 - 8 * Z.of_nat jj) 8 _
      (bv_unsigned (getr regs (Z_to_bv 5 rz))));
    [ exact HRf | exact Usp | repeat (first [left; reflexivity | right])
    | cbn [sv_denot];
      lazymatch goal with |- context [ew _ ?n] => rewrite (EL n (Z_to_bv 5 rz) eq_refl) end;
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 rz))) as Hrr;
      change (bv_modulus 64) with (2 ^ 64) in Hrr; change (8 * Z.of_N 8) with 64; lia
    | change (Z.of_N 8) with 8; lia | lia | reflexivity ]
  end. }
(* the recorder's representation at the call: g_rec off ncalls, record.spill and the live blocks are kept, and
   ncalls holds the same 16 *)
assert (HQm : arep_at (ablocks B ly S) (rdW W (ms_mem ms0)) A_G_REC A_REC_SPILL R Q).
{ apply (da_arep_kept _ (rdW W mem)); [exact HQ | | |].
  - intros a Ha.
    assert (Hd : (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4) \/
                 ~ (A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4)) by lia.
    destruct Hd as [Hn | Hn]; [|exact (KPG a (recb_grec_in a Ha) Hn)].
    assert (Hk : (Z.to_nat (a - (A_G_REC + OFF_NCALLS)) < 4)%nat) by lia.
    replace a with (A_G_REC + OFF_NCALLS + Z.of_nat (Z.to_nat (a - (A_G_REC + OFF_NCALLS)))) by lia.
    rewrite (HNCm _ Hk), (Vnc16 _ Hk). reflexivity.
  - intros a Ha. apply KPG; [exact (recb_spill_in a Ha) |].
    clear - Ha. unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, SC_SIZE in *. lia.
  - intros q m i Hin Hi. pose proof (req_size_pos m ltac:(lia)) as [_ Hrq]. exact (KPB q m i Hin ltac:(lia)). }
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
assert (Psp : spZ rg = spZ regs + -64)
  by (unfold spZ at 1; rewrite P2, Usp, unsigned_lit_small by lia; lia);
assert (P3' : getr rg 3 = w64 (as_gp B)) by (rewrite P3, (EL 3%nat 3%bv eq_refl); exact Hgp);
assert (P4' : getr rg 4 = w64 (as_tp B)) by (rewrite P4, (EL 4%nat 4%bv eq_refl); exact Htp);
assert (P10' : getr rg 10 = w64 A_REC_SPILL) by (rewrite P10, U292; reflexivity);
assert (P11' : getr rg 11 = w64 (Z.of_nat (length [l_spill Q]))) by (cbn [length]; exact P11);
assert (Ps0 : achain ly (aview SEGS (w_H W) mm) (spZ regs + -64) (s0Z rg) [])
  by (apply achain_low; unfold s0Z; rewrite P8, U292, unsigned_lit_small by (unfold A_REC_SPILL; lia);
      unfold A_REC_SPILL in *; lia);
eapply SRr_bind;
[ eapply (cl_callS_wide B LAWS W rg mm _ DESCRIPTORS_ADD_STK (spZ regs) (da_FP O) ly S W mem md [] ly S mdq 0
    REC_CALLS_FREE_STK (rcf_fp A_REC_SPILL [l_spill Q]) (EV_REC_CALLS_FREE [l_spill Q]) (-64) (getr rg 1) []
    (fun ly' S' W' regs' mem' md' =>
       Permutation (ablocks B ly S) (ablocks B ly' S' ++ l_spill Q) /\
       rec_repA B ly' S' (rdW W' mem') (set_spill R (fst (r_spill R), []))
         (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)) /\
       (forall p n i, In (p, n) (ablocks B ly' S') -> 0 <= i < n ->
          rdW W' mem' (p + i) = aview SEGS (w_H W) mm (p + i)) /\
       blocks_bytes S' <= blocks_bytes S + LIVE_REC_CALLS_FREE /\
       mo_le MT S S' (XM_REC_CALLS_FREE MT [l_spill Q])) HJ Psp);
  [ reflexivity | lia | unfold REC_CALLS_FREE_STK, ASTACK; lia
  | rewrite HTS; unfold REC_CALLS_FREE_STK, ASTACK; lia
  | exact P3' | exact P4' | reflexivity
  | rewrite P1; apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity]
  | rewrite P1, unsigned_lit_small by lia; lia
  | exact Ps0
  | intros HPRE1; rewrite da_sig_rec_calls_free; eapply SRr_mono;
    [ eapply (TRCF fx ly S W rg mm mdq [] A_REC_SPILL [l_spill Q] HPRE1);
      [ eapply (arodata_ok_journalP (RO := RRO) SEGS RLO RHI RELRO_IMG B); [exact HJ | exact HROFP | exact HROD]
      | exact P10' | exact P11' | cbn [length]; lia
      | right; left; cbn [length]; unfold CALL_SIZE, SC_SIZE, A_REC_SPILL in *; lia
      | unfold A_REC_SPILL; reflexivity
      | intros i P Hi;
        destruct i as [|i]; [|cbn [nth_error] in Hi; destruct i; discriminate Hi];
        cbn [nth_error] in Hi; injection Hi as <-;
        pose proof HSPL as (Hfn & Hna6 & HlenP & Vfn & Vna & Hnd & Hargs);
        split; [rewrite HlenP; exact Hna6 | split];
        [ replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_NARGS) with (A_REC_SPILL + CALL_OFF_NARGS)
            by (cbn [Z.of_nat]; lia);
          rewrite HlenP; apply (aval_mem_kept (rdW W mem)); [exact Vna|];
          intros k Hk; apply KPG;
          [ apply recb_spill_in; cbv [A_REC_SPILL CALL_OFF_NARGS SC_SIZE]; lia
          | cbv [A_G_REC A_REC_SPILL OFF_NCALLS CALL_OFF_NARGS]; lia ]
        | intros k pn Hpn;
          assert (Hk : (k < length (snd (r_spill R)))%nat)
            by (rewrite <- HlenP; apply nth_error_Some; rewrite Hpn; discriminate);
          destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia];
          destruct (Hargs k s pn Hs Hpn) as (Vp & Hp0 & Hinb & Hlen' & Hstr');
          split;
          [ replace (A_REC_SPILL + CALL_SIZE * Z.of_nat 0 + CALL_OFF_ARGS + 8 * Z.of_nat k)
              with (A_REC_SPILL + CALL_OFF_ARGS + 8 * Z.of_nat k) by (cbn [Z.of_nat]; lia);
            apply (aval_mem_kept (rdW W mem)); [exact Vp|];
            intros j Hj; apply KPG;
            [ apply recb_spill_in; cbv [A_REC_SPILL CALL_OFF_ARGS SC_SIZE]; lia
            | cbv [A_G_REC A_REC_SPILL OFF_NCALLS CALL_OFF_ARGS]; lia ]
          | exact Hinb ] ]
      | cbn [concat]; rewrite app_nil_r; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HSPL))))))
      | rewrite HEVps; unfold EV_DESCRIPTORS_ADD, EV_XSTRDUP in *; lia
      | rewrite HXMps; apply (mo_ok_le MT MTL S _ (XM_DESCRIPTORS_ADD MT R uri) HMOK);
        unfold XM_DESCRIPTORS_ADD, XM_XSTRDUP;
        pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (sarg uri)) + 1) ltac:(lia)); lia ]
    | cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK3);
      exists ly3, S3, regs3, mem3, md3; split; [reflexivity | split; [exact HJ1 | split; [exact HP |]]];
      destruct HK3 as (HPerm & _ & _ & HKeep & _ & HRepS & _ & HBB & HML);
      cbn [concat] in HPerm; rewrite app_nil_r in HPerm;
      split; [exact HPerm | split; [exact (HRepS R Q HQm eq_refl eq_refl) | split; [exact HKeep | split; [exact HBB | exact HML]]]] ]
  | intros a Ha; destruct (da_rcf_fp_in (l_spill Q) a Ha) as [Hsp | ([q m] & Hin & Hq)];
    [ apply (da_awr_slot B TL HB VOBJS cmd_prog_img cmd_prog_writable _ _ _ _ _ _ _ _ A_REC_SPILL);
      [right; reflexivity | unfold CALL_SIZE, SC_SIZE in *; lia]
    | right; left; split;
      [ exists (q, q + req_size m); split;
        [right; right; apply in_map_iff; exists (q, m); split; [reflexivity | apply HOQ; apply HSPinQ; exact Hin]
        | cbn [fst snd] in *; lia]
      | exists q, m; split; [exact (HSPin (q, m) Hin) | cbn [fst snd] in *; lia] ] ]
  | intros lyv Sv Wv regsv memv mdv' _ a Ha Hw _; exfalso;
    destruct (da_rcf_fp_in (l_spill Q) a Ha) as [Hsp | ([q m] & Hin & Hq)];
    [ unfold A_REC_SPILL, SC_SIZE in *; rewrite HTS in Hslo; lia
    | destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR (HSPin (q, m) Hin)) as (_ & _ & Hcl & _);
      cbn [fst snd] in Hq; rewrite HTS in Hslo; lia ] ]
| ] end.
cbv beta. intros WR cR HwleR (lyR & SR & regsR & memR & mdR & -> & HJ2 & HJc2 & HP2 & HPerm2 & HRep2 & HKeep2 & HBB2 & MLE2).
pose proof (proj1 HJ2) as HAR2.
destruct HRep2 as (Q' & HQ' & HOQ').
(* what rec_calls_free kept: the frame above its window (its footprint is the spill's nargs field and the blocks
   it frees) *)
assert (KC : forall a, spZ regs - 64 <= a < spZ regs -> rdW WR memR a = rdW W (ms_mem ms0) a).
{ intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _).
  apply K1; [lia | lia |].
  intros Hf. destruct (da_rcf_fp_in (l_spill Q) a Hf) as [Hsp | ([q m] & Hin & Hq)];
  [ unfold A_REC_SPILL, SC_SIZE in *; lia
  | destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR (HSPin (q, m) Hin)) as (_ & _ & Hcl & _);
    cbn [fst snd] in Hq; lia ]. }
(* back at 0x8ce8c: the symbolic state after the call keeps no region (the join's segment needs none) *)
jafter_call_keep_pi HS 35%nat regsR (mrestrict (w_H WR) memR) HP2 (@nil nat) HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rewrite P1.
remember (havoc (da_E0 regs 16) 35 (map (getr regsR) CLOB)) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 35)%nat -> ew E2 n = ew (da_E0 regs 16) n)
  by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (SHOK2 : sh_ok SEGS da_Bx0 da_SH0 E2 (mrestrict (w_H WR) memR)).
{ apply (da_slot_sh_ok B TL HB VOBJS cmd_prog_img cmd_prog_writable lyR SR WR memR mdR E2 34 32 A_REC_SPILL HAR2
    (or_intror eq_refl)).
  - rewrite OLD2 by lia. exact E34.
  - rewrite OLD2 by lia. unfold da_E0. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
(* 0x8ce8c: `j` to the join (the second run's frame facts are spent: KP holds them) *)
clear HF HG HFr.
paj_run_to_tok RUNTO HS HJ2 SHOK2 da_Bspan DA_JOIN.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_nil. }
da_fold_md. rename HFr into HFrJ. clear HF.
pmkst HS.
prreg HS (2%bv : bv 5) J2. prreg HS (3%bv : bv 5) J3. prreg HS (4%bv : bv 5) J4. prreg HS (8%bv : bv 5) J8.
prreg HS (9%bv : bv 5) J9. prreg HS (19%bv : bv 5) J19. prreg HS (20%bv : bv 5) J20.
prreg HS (22%bv : bv 5) J22. prreg HS (23%bv : bv 5) J23. prreg HS (24%bv : bv 5) J24.
prreg HS (25%bv : bv 5) J25. prreg HS (26%bv : bv 5) J26. prreg HS (27%bv : bv 5) J27.
assert (Hdec : forall a b : Z * Z, {a = b} + {a <> b}) by (decide equality; apply Z.eq_dec).
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rg _ ?mm _; cfg_model := ?mdq |} _ =>
(* the `j` run kept every byte *)
assert (KJ : forall a, 0 <= a < 2 ^ 64 -> rdW WR mm a = rdW WR memR a)
  by (intros a Ha; apply (aview_eq_of SEGS); apply HFrJ; rewrite Z_to_bv_unsigned; unfold bv_wrap;
      change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small by lia;
      intros (r & Hin & _);
      lazymatch type of Hin with In r ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
      destruct Hin);
apply (HK lyR SR WR rg mm mdq (0 + EV_REC_CALLS_FREE [l_spill Q]) (ablocks B lyR SR) (rdW WR memR)
  (set_spill R (fst (r_spill R), [])) Q' A_REC_SPILL HJ2)
end.
- rewrite HEVps. lia.
- (* the registers at the join *)
  unfold da_regsJ.
  split; [rewrite J2, OLD2, Usp by lia; f_equal; lia|].
  split; [rewrite J3, OLD2 by lia; exact (EL 3%nat 3%bv eq_refl)|].
  split; [rewrite J4, OLD2 by lia; exact (EL 4%nat 4%bv eq_refl)|].
  split; [rewrite J8; change 292%nat with DA_SPILL;
          rewrite (img_env_atomP E2 DA_SPILL HEI2 ltac:(unfold DA_SPILL, A_OBJ, A_TEXT, A_LIM; lia));
          rewrite (da_spill_val B TL HB VOBJS cmd_prog_img cmd_prog_writable); reflexivity|].
  split; [rewrite J9, OLD2 by lia; rewrite (EL 10%nat 10%bv eq_refl); exact H10|].
  split; [rewrite J19; change 285%nat with DA_GREC;
          rewrite (img_env_atomP E2 DA_GREC HEI2 ltac:(unfold DA_GREC, A_OBJ, A_TEXT, A_LIM; lia));
          rewrite (da_grec_val B TL HB VOBJS cmd_prog_img cmd_prog_writable); reflexivity|].
  split; [rewrite J20, OLD2 by lia; unfold da_E0; rewrite Eimg_low by (unfold A_TEXT; lia);
          exact (ew_Ereg_extra regs _ 0)|].
  intros r Hr.
  assert (Hr' : r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hr' as [-> | Hr']); [| | | | | subst r];
  [ replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity); rewrite J22, OLD2 by lia;
    exact (EL 22%nat 22%bv eq_refl)
  | replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity); rewrite J23, OLD2 by lia;
    exact (EL 23%nat 23%bv eq_refl)
  | replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity); rewrite J24, OLD2 by lia;
    exact (EL 24%nat 24%bv eq_refl)
  | replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity); rewrite J25, OLD2 by lia;
    exact (EL 25%nat 25%bv eq_refl)
  | replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity); rewrite J26, OLD2 by lia;
    exact (EL 26%nat 26%bv eq_refl)
  | replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity); rewrite J27, OLD2 by lia;
    exact (EL 27%nat 27%bv eq_refl) ].
- (* the frame at the join: kept by rec_calls_free (above its window) and by the `j` run *)
  apply (da_frame_kept2 W WR (ms_mem ms0) _ (spZ regs) regs); [|exact HfrC].
  intros a Ha. rewrite (KJ a ltac:(lia)). exact (KC a Ha).
- exact HQ'.
- reflexivity.
- cbn [set_spill r_calls]. rewrite Hn16. reflexivity.
- intros Hlt. cbn [set_spill r_calls] in Hlt. lia.
- intros _. reflexivity.
- intros a Ha _. apply KJ. unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in *. lia.
- intros q kk i Hin Hi. pose proof (req_size_pos kk ltac:(lia)) as [_ Hrq].
  destruct (S2 da_blk_not_PG lyR SR WR memR mdR q kk (q + i) HAR2 Hin ltac:(lia)) as [_ Hr].
  exact (KJ _ Hr).
- unfold descriptors_add_m, rec_stub_mix, rec_record. cbn [set_spill r_calls]. rewrite Hn16. reflexivity.
- intros pn Hpn. apply (proj2 (HOQ' pn)) in Hpn. apply HOQ. revert Hpn. unfold lay_blocks.
  rewrite !in_app_iff. tauto.
- intros pn HinS HnO. apply (Permutation_in _ HPerm2) in HinS. apply in_app_iff in HinS as [H | H]; [exact H|].
  exfalso. apply HnO. apply HOQ. exact (HSPinQ pn H).
- intros pn Hin.
  assert (HinS : In pn (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HPerm2)); apply in_app_iff; left; exact Hin).
  destruct (List.in_dec Hdec pn O) as [HoO | HnO]; [right | left; split; [exact HinS | exact HnO]].
  apply (proj1 (HOQ pn)) in HoO. apply (proj1 (HOQ' pn)).
  revert HoO. unfold lay_blocks. rewrite !in_app_iff. intros [H | [H | H]]; [left; exact H | exfalso | right; exact H].
  exact (list_nodup_app_disj _ _ pn (Permutation_NoDup HPerm2 (recb_ablocks_nodup_m B _ _ _ _ _ HAR)) Hin H).
- rewrite <- HXMps. exact MLE2.
- unfold LIVE_REC_CALLS_FREE in HBB2. lia.
- (* the string at the join: its block is none of record.spill's (they are apart from it), so it stays live, and
     rec_calls_free and the `j` run keep its bytes *)
  destruct HSTR as (x & Hx & Hblk & Hstr & Hxl & HapO).
  exists x. split; [exact Hx|].
  destruct Hblk as (q0 & k0 & Hin0 & Hq1 & Hq2).
  assert (HinR : In (q0, k0) (ablocks B lyR SR)).
  { pose proof (Permutation_in _ HPerm2 Hin0) as H. apply in_app_iff in H as [H | H]; [exact H|].
    exfalso. pose proof (proj1 (Forall_forall _ _) HapO (q0, k0) (proj2 (HOQ _) (HSPinQ _ H))) as Ha.
    cbn [fst snd] in Ha. unfold iv_apart in Ha. lia. }
  split; [exists q0, k0; split; [exact HinR | lia]|].
  split; [|exact Hxl].
  apply (rastr_kept (rdW W mem)); [exact Hstr|].
  intros i Hi. pose proof (req_size_pos k0 ltac:(lia)) as [_ Hrq].
  replace (pu + i) with (q0 + (pu - q0 + i)) by lia.
  destruct (S2 da_blk_not_PG lyR SR WR memR mdR q0 k0 (q0 + (pu - q0 + i)) HAR2 HinR ltac:(lia)) as [_ Hr].
  rewrite (KJ _ Hr), (HKeep2 q0 k0 (pu - q0 + i) HinR ltac:(lia)).
  exact (KPB q0 k0 (pu - q0 + i) Hin0 ltac:(lia)).
Qed.

End e.
End f.
End d.
