(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: descriptors_panel_get's walk from the call of xstrdup to the call of rec_shape_of (plugin-hostd/fuzz_command.asan), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a call through cl_callS and the callee's contract, then a run from a fresh seed to the next segment's statement). *)

(* 0x8d1c0 .. 0x8d204: xstrdup copies the argument; the inlined arg_s checks the shadow byte at
   ((c + 4) >> 3) + 0x7fff8000 of c->nargs and the one of c->args[0] (both in the slot, whose shadow is 0, so the
   error paths are not reached) and stores nargs := 1, args[0] := the copy; then a0 := "panel_get" (0x21f80),
   a1 := 9 and the call of rec_shape_of, where `dpg_R_stmt` (descriptors_panel_get_s3.v) takes over. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c rec_shape_of_c hand_back_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_panel_get_c descriptors_panel_get_s1 descriptors_panel_get_s2 descriptors_panel_get_s3 descriptors_panel_get_s4
descriptors_panel_get_s6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the verb "panel_get" (0x21f80) is the listing's object 77 (CmdAddr.v's cmd_objs) *)
Lemma dpg_verb_atom : A_OBJ 77 = 318%nat.
Proof. vm_compute. reflexivity. Qed.

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
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Hypothesis cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
In (p, n) (ablocks B ly S) -> p <= e < p + n -> atail_vis SEGS W mem e.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.

Lemma dpg_verb_val : VAL (A_OBJ 77) = 0x21f80.
Proof. rewrite (VOBJS 77%nat) by (vm_compute; lia). vm_compute. reflexivity. Qed.

(* the live blocks' sizes are not negative *)
Lemma dpg_bsum_nonneg : forall ly S (W : world SEGS) mem md l, AR SEGS B ly S W mem md ->
(forall pn, In pn l -> In pn (ablocks B ly S)) -> 0 <= bsum l.
Proof.
intros ly S W mem md l HAR. induction l as [|[p n] l IH]; intros Hl; cbn [bsum fold_right]; [lia|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (Hl _ (or_introl eq_refl))) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. assert (0 <= fold_right (fun b acc => snd b + acc) 0 l) by (apply IH; intros pn Hpn; apply Hl; right; exact Hpn).
lia.
Qed.

Lemma dpg_X_of_R : dpg_R_stmt B MT -> dpg_X_stmt B MT.
Proof.
intros HR ly S W regs mem md ch pu x R O CTX lyc Sc Wc regs1 memc mdc Q1 O1 s MID BLK HREC HO1 R1 R10 R18 R20 HBLKS HSTRS.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CTX as (HPRE & HFRM & HROD & HRO & H10 & Hpu & HBLK0 & HSTR0 & HLEN & HAPO & HREP & Hfr8 & Hev & Hlive & MOK).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & MLE & Hsp1 & R3 & R4 & R8 & R19 & Rhi & HFR).
pose proof (proj1 HJ) as HAR.
pose proof BLK as (Bsub & Bgone & BO1 & BO1g & Bperm).
pose proof HREP as (Q & HQ & HQO).
pose proof HQ as (_ & _ & _ & (HL16 & _) & _).
destruct (dpg_c_ok R HL16) as (Hc1 & Hc2 & Hc8 & Hc3).
assert (Hc3' : (dpg_c R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ dpg_c R = A_REC_SPILL)
  by (destruct Hc3 as [[H _] | H]; [left | right]; exact H).
assert (Hcr : 4096 <= dpg_c R /\ dpg_c R + 16 <= 0x606000)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (rec_repA_in B ly S (rdW W mem) R O HREP).
assert (HSTK1 : XSTRDUP_STK + 48 <= DPG_STK) by (unfold DPG_STK, DESCRIPTORS_PANEL_GET_STK; lia).
assert (HSTKp : 0 <= XSTRDUP_STK) by (unfold XSTRDUP_STK, ASTACK; lia).
(* the meter, the event and live budgets xstrdup asks *)
assert (HXMa : 0 <= XM_ANSWER MT (snd (descriptors_panel_get_m R (Some x)))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (descriptors_panel_get_m R (Some x)))) + 1) ltac:(lia)). lia. }
assert (HXMx : 0 <= XM_XSTRDUP MT x) by (unfold XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
assert (HLIVEa : 0 <= LIVE_ANSWER (snd (descriptors_panel_get_m R (Some x))))
  by (unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP; lia).
assert (HEVv : 0 <= EV_ANSWER /\ EV_XSTRDUP = 1) by (vm_compute; repeat split; discriminate).
assert (Hbb : blocks_bytes Sc <= blocks_bytes S).
{ destruct Bperm as (fr & Hfr). rewrite (blocks_bytes_bsum B lyc Sc), (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hfr), bsum_app.
  assert (0 <= bsum fr); [|lia].
  apply (dpg_bsum_nonneg ly S W mem md fr HAR0). intros pn Hpn. apply (Permutation_in pn (Permutation_sym Hfr)).
  apply in_or_app. right. exact Hpn. }
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs1 & Hnev1 & _).
assert (HEVx : st_nev Sc + EV_XSTRDUP <= EV_MAX) by (unfold EV_DESCRIPTORS_PANEL_GET in Hev; lia).
assert (HLVx : blocks_bytes Sc + LIVE_XSTRDUP x <= LIVE_MAX)
  by (unfold LIVE_DESCRIPTORS_PANEL_GET in Hlive; cbn [sarg] in Hlive; lia).
assert (HMOKx : mo_ok MT Sc (XM_XSTRDUP MT x)).
{ apply (mok_station MT S Sc (XM_DESCRIPTORS_PANEL_GET MT R (Some x)) (rec_spill_frees R * mo_free MT) (XM_XSTRDUP MT x)
    MTL MOK MLE HXMx).
  unfold XM_DESCRIPTORS_PANEL_GET. cbn [sarg]. lia. }
(* xstrdup's premises: the return address, the read-only bytes, the stack words above its sp, the string *)
assert (SIGX : SIG CS_xstrdup = BASE + AF_xstrdup).
{ rewrite (SIGP CS_xstrdup) by (cbv [cmd_prog_syms]; repeat (first [left; reflexivity | right])).
  reflexivity. }
assert (Hraw1 : YK0s.ret_ok (getr regs1 1))
  by (rewrite R1; apply ret_ok_codeptr_v; [unfold DPG_RET_X, AF_descriptors_panel_get; lia | reflexivity]).
assert (Hraw4 : 4096 <= bv_unsigned (getr regs1 1))
  by (rewrite R1, unsigned_lit_small by (unfold DPG_RET_X, AF_descriptors_panel_get; lia);
      unfold DPG_RET_X, AF_descriptors_panel_get; lia).
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW Wc memc))
  by exact (dpg_rodata_kept B cmd_ro_prog_apart _ _ ly S W mem md O [] lyc Sc Wc memc mdc _ HAR0 HOin HJ HROD).
pose proof HBLKS as (qb & kb & Hqb & Hqb1 & Hqb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ qb kb HAR Hqb) as (_ & Hqb4096 & _).
assert (HARG : astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] s (Some x)).
{ unfold astr_argA. split; [lia|]. split; [exact HSTRS|]. split; [exact HLEN|].
  left. split; [exact HBLKS | constructor]. }
assert (HTAIL : atail_vis SEGS Wc memc (s + Z.of_nat (length x)))
  by exact (cmd_heap_tail_vis lyc Sc Wc memc mdc qb kb (s + Z.of_nat (length x)) HAR Hqb ltac:(lia)).
(* the call of xstrdup *)
eapply SRr_bind.
{ eapply (cl_callS B LAWS Wc regs1 memc (Z_to_bv 64 (SIG CS_xstrdup)) DPG_STK (spZ regs) (dpg_FP O) ly S W mem md [] lyc Sc mdc
    (rec_spill_frees R) XSTRDUP_STK [] EV_XSTRDUP (-48) (getr regs1 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 => exists p : Z,
        getr regs2 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
        Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP x) :: ablocks B lyc Sc) /\
        Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B lyc Sc) /\
        in_blockA (ablocks B ly2 S2) p (LIVE_XSTRDUP x) /\
        astr_atR (rdW W2 mem2) p x /\ astr_atR (rdW W2 mem2) s x /\
        blocks_bytes S2 <= blocks_bytes Sc + LIVE_XSTRDUP x /\ mo_le MT Sc S2 (XM_XSTRDUP MT x)) HJ).
  - unfold DPG_FRAME in Hsp1. lia.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - reflexivity.
  - exact Hraw1.
  - exact Hraw4.
  - apply achain_low. unfold s0Z. rewrite R8, unsigned_lit_small by lia. lia.
  - intros HPRE1. rewrite SIGX. eapply SRr_mono.
    + exact (TXSTRDUP fx lyc Sc Wc regs1 memc mdc [] s x HPRE1 HROD1 R10 (or_introl HARG) HTAIL HEVx HLVx HMOKx).
    + cbv beta. unfold apost_base. intros Wx cx _ (lyx & Sx & regsx & memx & mdx & -> & HJ1 & HP & HK3).
      exists lyx, Sx, regsx, memx, mdx. split; [reflexivity | split; [exact HJ1 | split; [exact HP | exact HK3]]].
  - intros a (r & [] & _). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJx & HP2 &
  (p & Hp10 & Hp4096 & HPerm2 & Hap2 & Hpblk & Hcp & Hsrc & HBBx & MLEx)).
(* back at 0x8d1c4: the registers xstrdup keeps, the frame, the slot's nargs word *)
pose proof (proj1 HJ2) as HAR2.
assert (Hpin : In (p, LIVE_XSTRDUP x) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym HPerm2)); left; reflexivity).
assert (Hphi : p + Z.of_nat (length x) + 1 <= 2 ^ 63).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ p (LIVE_XSTRDUP x) HAR2 Hpin) as (_ & _ & Hpc & _).
  pose proof (dpg_req_ge (Z.of_nat (length x) + 1) ltac:(lia)).
  unfold LIVE_XSTRDUP in Hpc. lia. }
assert (CS2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr regs1 rr)
  by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (X2 : getr regs2 2 = getr regs1 2) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X3 : getr regs2 3 = getr regs1 3) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X4 : getr regs2 4 = getr regs1 4) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X8 : getr regs2 8 = getr regs1 8) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X18 : getr regs2 18 = getr regs1 18) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X19 : getr regs2 19 = getr regs1 19) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X20 : getr regs2 20 = getr regs1 20) by (apply CS2; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (Hsp2 : spZ regs2 = spZ regs - 48)
  by (unfold spZ at 1; rewrite X2; unfold DPG_FRAME in Hsp1; exact Hsp1).
pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & GX1 & GX2 & GX3 & _).
assert (HFR2 : forall j r, nth_error dpg_saved j = Some r ->
  aval_mem (rdW W2 mem2) (spZ regs2 + 40 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj6 : (j < 6)%nat) by (apply (proj1 (nth_error_Some dpg_saved j)); rewrite Hj; discriminate).
  rewrite Hsp2. apply (aval_mem_kept (rdW Wc memc)).
  - replace (spZ regs - 48 + 40 - 8 * Z.of_nat j) with (spZ regs - 8 - 8 * Z.of_nat j) by lia. exact (HFR j r Hj).
  - intros kk Hkk. apply GX1; [lia | lia | intros (r' & [] & _)]. }
assert (HNA2 : aval_mem (rdW W2 mem2) (dpg_c R + 4) 4 0).
{ apply (aval_mem_kept (rdW Wc memc)); [exact (dpg_nargs0 _ _ _ _ _ HREC HL16)|].
  intros kk Hkk.
  assert (Hin : A_G_REC <= dpg_c R + 4 + Z.of_nat kk < A_G_REC + REC_SIZE \/
                A_REC_SPILL <= dpg_c R + 4 + Z.of_nat kk < A_REC_SPILL + SC_SIZE)
    by (apply (dpg_slot_PG (dpg_c R)); [exact Hc1 | exact Hc2 | exact Hc3' | lia]).
  destruct (dpg_unowned B HB (dpg_c R + 4 + Z.of_nat kk)
    ltac:(destruct Hin as [Hin | Hin]; [left | right; left]; exact Hin)) as [Hown Herr].
  apply GX3; [apply cmd_prog_img, dpg_in_PG; exact Hin | exact Hown | exact Herr |
    apply fp_spares_closed; [exact sink_closed_nil | intros (r' & [] & _)]]. }
assert (HspR2 : 2 ^ 46 <= spZ regs2 <= 2 ^ 47 - 48) by (rewrite Hsp2; lia).
assert (Hsp16x : spZ regs2 mod 16 = 0).
{ rewrite Hsp2. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
destruct (dpg_retx_seed B HB cmd_prog_writable ly2 S2 W2 mem2 md2 regs2 regs (dpg_c R) HAR2 HspR2 Hsp16x
  ltac:(rewrite X8; exact R8) Hc1 Hc2 Hc8 Hc3' ltac:(rewrite X19; exact R19)
  ltac:(rewrite X18; exact R18) ltac:(rewrite X20; exact R20) HFR2 HNA2) as [HS SHOK].
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg regs2 (dpg_extra regs)))) by apply Eimg_env.
assert (EE2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs2 (dpg_extra regs))) n = getr regs2 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
remember (Eimg (Ereg regs2 (dpg_extra regs))) as E2 eqn:HE2.
assert (E8u2 : bv_unsigned (ew E2 8) = dpg_c R)
  by (rewrite (EE2 8%nat 8%bv eq_refl), X8, R8; apply unsigned_lit_small; lia).
(* 0x8d1c4 .. 0x8d204: the checks on c->nargs and c->args[0], nargs := 1, args[0] := the copy, then rec_shape_of *)
rewrite R1.
paj_run_tok RUN HS HJ2 SHOK Bspan.
{ awr_ok_tac; eapply awr_ok_cons_gen; [reflexivity | exact E8u2 | | apply awr_ok_nil];
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (dpg_awr_slot B HB cmd_prog_img);
  apply (dpg_slot_PG (dpg_c R)); [exact Hc1 | exact Hc2 | exact Hc3' | lia]. }
rewrite ?wvb_collapse in HJ2.
match goal with |- context [with_vm_backing ?a ?b ?c] => set (mdX := with_vm_backing a b c) in *; clearbody mdX end.
(* the run kept every byte outside the slot's nargs and args[0] *)
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ mem2) (mrestrict _ ?m1) |- _ =>
assert (KEEPX : forall a, 0 <= a < 2 ^ 64 -> ~ (dpg_c R + 4 <= a < dpg_c R + 16) ->
  aview SEGS (w_H W2) m1 a = aview SEGS (w_H W2) mem2 a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => dpg_c R + 4 <= a < dpg_c R + 16) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E8u2 in Hrr; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
pmkst HS.
assert (E10 : ew E2 10 = Z_to_bv 64 p) by (rewrite (EE2 10%nat 10%bv eq_refl); exact Hp10).
lazymatch goal with HS : st_ok _ ?Ex2 ?SSX (restrict _ ?ms2) |- _ =>
  assert (EXL2 : forall n, (n < 32)%nat -> ew Ex2 n = ew E2 n)
    by (intros n Hn; repeat (rewrite ew_ewset_other by lia); reflexivity);
  assert (KR : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs ms2) r = getr regs2 r)
    by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ _ r HS), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite ?(EXL2 (Z.to_nat (bv_unsigned r)) ltac:(lia)); apply EE2; lia);
  let r1 := eval vm_compute in (nth 1 (ss_mem SSX) dpg_slot_r) in
  pose proof (st_ok_region_nth (segs:=SEGS) Ex2 SSX (restrict (w_H W2) ms2) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRs;
  cbn [ms_mem restrict] in HRs;
  assert (E8x : bv_unsigned (ew Ex2 8) = dpg_c R) by (first [exact E8u2 | rewrite (EXL2 8%nat ltac:(lia)); exact E8u2]);
  pose proof (field_of_region (segs:=SEGS) Ex2 _ 8 (dpg_c R) _ _ _ _ _ 4 4 (SLit 1) 1 HRs E8x
    ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V4;
  pose proof (field_of_region (segs:=SEGS) Ex2 _ 8 (dpg_c R) _ _ _ _ _ 8 8 (SOff 10 0) p HRs E8x
    ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite ?(EXL2 10%nat ltac:(lia)), E10, Z.add_0_r, unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as V8;
  change (N.to_nat 4) with 4%nat in V4; change (N.to_nat 8) with 8%nat in V8
end.
prreg HS (1%bv : bv 5) T1. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  set (regsX := rg) in *; set (memX := mm) in * end.
(* the copy: a fresh heap block, apart from the image and from every block the recorder holds *)
assert (Hplo : forall i, 0 <= i < Z.of_nat (length x) + 1 -> p + i < 0x10000 \/ 0x606000 <= p + i).
{ intros i Hi. pose proof (blk_off_imgP B ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) (proj1 HJx) Hpin) as Ho.
  unfold off_img, LIVE_XSTRDUP in Ho. pose proof (dpg_req_ge (Z.of_nat (length x) + 1) ltac:(lia)). lia. }
assert (HcpX : astr_atR (rdW W2 memX) p x).
{ destruct Hcp as [Hab Hnz]. split; [|exact Hnz]. intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (KEEPX (p + Z.of_nat i)); [exact (Hab i ltac:(rewrite length_app; cbn [length]; lia)) | lia |].
  pose proof (Hplo (Z.of_nat i) ltac:(lia)). unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *. lia. }
assert (HpQ : ~ In p (map fst (lay_blocks Q1))).
{ intros Hin. apply in_map_iff in Hin as ((p' & m) & Hp' & Hpm). cbn [fst] in Hp'. subst p'.
  assert (Hc' : In (p, m) (ablocks B lyc Sc))
    by exact (rec_repA_in B lyc Sc (rdW Wc memc) _ O1 (ex_intro _ Q1 (conj HREC HO1)) _ (proj2 (HO1 _) Hpm)).
  assert (Hm : m = LIVE_XSTRDUP x).
  { apply (dpg_same_start B ly2 S2 W2 mem2 md2 p m _ (proj1 HJx)); [|exact Hpin].
    apply (Permutation_in _ (Permutation_sym HPerm2)). right. exact Hc'. }
  subst m. rewrite Forall_forall in Hap2. specialize (Hap2 _ Hc'). unfold iv_apart, LIVE_XSTRDUP in Hap2.
  cbn [fst snd] in Hap2. lia. }
(* the recorder after arg_s: the call (24, [x]) with the copy *)
assert (HKQ : rec_rd_kept Q1 (rdW Wc memc) (rdW W2 memX) (fun a => dpg_c R + CALL_OFF_NARGS <= a < dpg_c R + CALL_OFF_ARGS + 8)).
{ intros a Ha Hn. unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hn.
  destruct Ha as [Ha | [Ha | ((pb & pk) & Hpn & Hr)]].
  - rewrite (KEEPX a); [|unfold A_G_REC, REC_SIZE in Ha; lia | lia].
    destruct (dpg_unowned B HB a ltac:(left; exact Ha)) as [Hown Herr].
    apply GX3; [apply cmd_prog_img, dpg_in_PG; left; exact Ha | exact Hown | exact Herr |
      apply fp_spares_closed; [exact sink_closed_nil | intros (r' & [] & _)]].
  - rewrite (KEEPX a); [|unfold A_REC_SPILL, SC_SIZE in Ha; lia | lia].
    destruct (dpg_unowned B HB a ltac:(right; left; exact Ha)) as [Hown Herr].
    apply GX3; [apply cmd_prog_img, dpg_in_PG; right; exact Ha | exact Hown | exact Herr |
      apply fp_spares_closed; [exact sink_closed_nil | intros (r' & [] & _)]].
  - cbn [fst snd] in Hr.
    assert (Hc' : In (pb, pk) (ablocks B lyc Sc))
      by exact (rec_repA_in B lyc Sc (rdW Wc memc) _ O1 (ex_intro _ Q1 (conj HREC HO1)) _ (proj2 (HO1 _) Hpn)).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pk HAR Hc') as (_ & H4096 & Hpc & _ & _ & _ & Hk0).
    pose proof (blk_off_imgP B lyc Sc Wc memc mdc pb pk HAR Hc') as Ho. unfold off_img in Ho.
    pose proof (dpg_req_ge pk (proj1 Hk0)) as [_ Hreq].
    rewrite (KEEPX a); [| lia | unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia].
    replace a with (pb + (a - pb)) by lia.
    apply (GX2 pb pk (a - pb)); [exact Hc' | apply (Permutation_in _ (Permutation_sym HPerm2)); right; exact Hc' | lia | intros (r' & [] & _)]. }
assert (HapG : iv_apart p (Z.of_nat (length x) + 1) A_G_REC REC_SIZE).
{ destruct (blk_off_imgP B ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) (proj1 HJx) Hpin) as [Ho | Ho];
  unfold LIVE_XSTRDUP in *; pose proof (dpg_req_ge (Z.of_nat (length x) + 1) ltac:(lia));
  unfold iv_apart, A_G_REC, REC_SIZE; lia. }
assert (HapS : iv_apart p (Z.of_nat (length x) + 1) A_REC_SPILL SC_SIZE).
{ destruct (blk_off_imgP B ly2 S2 W2 mem2 md2 p (LIVE_XSTRDUP x) (proj1 HJx) Hpin) as [Ho | Ho];
  unfold LIVE_XSTRDUP in *; pose proof (dpg_req_ge (Z.of_nat (length x) + 1) ltac:(lia));
  unfold iv_apart, A_REC_SPILL, SC_SIZE; lia. }
assert (V4' : aval_mem (rdW W2 memX) (dpg_c R + CALL_OFF_NARGS) 4 1)
  by (unfold CALL_OFF_NARGS; exact (aval_mem_view SEGS (w_H W2) _ _ _ _ V4)).
assert (V8' : aval_mem (rdW W2 memX) (dpg_c R + CALL_OFF_ARGS) 8 p)
  by (unfold CALL_OFF_ARGS; exact (aval_mem_view SEGS (w_H W2) _ _ _ _ V8)).
destruct (dpg_arg_step (ablocks B lyc Sc) (ablocks B ly2 S2) (rdW Wc memc) (rdW W2 memX) R Q1 REC_DESCRIPTORS_PANEL_GET p x
  HREC HL16 (fun pn H => Permutation_in _ (Permutation_sym HPerm2) (or_intror H)) Hpin ltac:(lia) HpQ HapG HapS
  ltac:(lia) HcpX V4' V8' HKQ) as (Q2 & HREC2 & HQ2).
(* the state at the call of rec_shape_of, as dpg_R_stmt takes it *)
assert (HQ2' : forall pn, In pn (lay_blocks Q2) <-> In pn O1 \/ pn = (p, Z.of_nat (length x) + 1)).
{ intros pn. pose proof (HQ2 pn). pose proof (HO1 pn). tauto. }
assert (MLE2 : mo_le MT S S2 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x))
  by exact (mo_le_trans MT MTL _ _ _ _ _ MLE MLEx).
assert (HBB2 : blocks_bytes S2 <= blocks_bytes S + LIVE_XSTRDUP x) by lia.
assert (KX2 : getr regsX 2 = getr regs2 2) by (apply KR; vm_compute; reflexivity).
assert (KX3 : getr regsX 3 = getr regs2 3) by (apply KR; vm_compute; reflexivity).
assert (KX4 : getr regsX 4 = getr regs2 4) by (apply KR; vm_compute; reflexivity).
assert (KX8 : getr regsX 8 = getr regs2 8) by (apply KR; vm_compute; reflexivity).
assert (HspX : spZ regsX = spZ regs - DPG_FRAME) by (unfold spZ at 1; rewrite KX2, X2; exact Hsp1).
assert (R3X : getr regsX 3 = w64 (as_gp B)) by (rewrite KX3, X3; exact R3).
assert (R4X : getr regsX 4 = w64 (as_tp B)) by (rewrite KX4, X4; exact R4).
assert (R8X : getr regsX 8 = w64 (dpg_c R)) by (rewrite KX8, X8; exact R8).
assert (R1X : getr regsX 1 = Z_to_bv 64 (BASE + DPG_RET_R))
  by (rewrite T1; unfold DPG_RET_R, AF_descriptors_panel_get; reflexivity).
assert (T10' : getr regsX 10 = w64 0x21f80)
  by (rewrite T10, <- (Z_to_bv_bv_unsigned 64 (ew E2 318)), (HEI2 318%nat ltac:(cbv; lia)), <- dpg_verb_atom, dpg_verb_val;
      reflexivity).
assert (T11' : getr regsX 11 = w64 9) by (rewrite T11; reflexivity).
assert (RhiX : forall r, 21 <= r <= 27 -> getr regsX (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (Rhi r Hr), <- (HP2 r ltac:(unfold acallee_saved; lia)).
  assert (Hrr : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hrr as [-> | Hrr]; [apply KR; vm_compute; reflexivity|]).
  subst r. apply KR. vm_compute. reflexivity. }
assert (HFRX : forall j r, nth_error dpg_saved j = Some r ->
  aval_mem (rdW W2 memX) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj6 : (j < 6)%nat) by (apply (proj1 (nth_error_Some dpg_saved j)); rewrite Hj; discriminate).
  apply (aval_mem_kept (rdW W2 mem2)).
  - replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs2 + 40 - 8 * Z.of_nat j) by lia. exact (HFR2 j r Hj).
  - intros kk Hkk. apply KEEPX; [lia | unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia]. }
exact (HR ly S W regs mem md ch pu x R O CTX lyc Sc O1 ly2 S2 W2 regsX memX mdX Q2 p BLK HJ2 MLE2 HBB2 HPerm2 Hap2
  Hp4096 HREC2 HQ2' HspX R3X R4X R1X R8X T10' T11' RhiX HFRX).
Qed.

End e.
End f.
End d.
