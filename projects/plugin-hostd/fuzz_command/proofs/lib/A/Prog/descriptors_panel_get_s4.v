(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: descriptors_panel_get's walk from the join of record()'s arms (0x8d180) to the call of xstrdup (plugin-hostd/fuzz_command.asan), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment proved from the next one's statement: seed, run, branch, call) and lib/A/Prog/sup_reply_code.v. *)

(* 0x8d180 .. 0x8d1c0: the two inline checks on the slot (the shadow byte at (c >> 3) + 0x7fff8000 and at
   ((c + 4) >> 3) + 0x7fff8000; the slot lies in g_rec or record.spill, whose shadow is 0, so the error path is not
   reached), the stores c->fn := 24 and c->nargs := 0, the test of uri (never NULL: a string in a heap block), and
   the call of xstrdup. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
descriptors_panel_get_c descriptors_panel_get_s1 descriptors_panel_get_s2 descriptors_panel_get_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a range's shadow facts read only shadow bytes, at or above SHADOW_OFF *)
Lemma dpg_ra_kept : forall (rd rd' : reader) a n,
(forall s, SHADOW_OFF <= s < 2 ^ 64 -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 63 ->
range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Han H x Hx. destruct (H x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite HK; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 60) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma dpg_hull_kept : forall (rd rd' : reader) a n,
(forall s, SHADOW_OFF <= s < 2 ^ 64 -> rd' s = rd s) -> 0 <= a -> 0 < n -> a + n <= 2 ^ 63 ->
shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n HK Ha Hn Han H s Hs. rewrite HK; [exact (H s Hs)|]. unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (a + n - 1) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
pose proof (Z.div_pos (a + n - 1) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
assert (Hd : (2147450880 + a / 8) / 8 * 8 >= 2147450880).
{ replace (2147450880 + a / 8) with (a / 8 + 268431360 * 8) by lia. rewrite Z.div_add by lia.
  pose proof (Z.div_pos (a / 8) 8 ltac:(lia) ltac:(lia)). lia. }
unfold SHADOW_OFF. lia.
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
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* the walk's footprint holds no sink token: its ranges start at g_rec, record.spill and the recorder's blocks *)
Lemma dpg_FP_closed : forall ly S O, (forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall (W : world SEGS) mem md, AR SEGS B ly S W mem md -> ~ YI16.sink_open_fp (dpg_FP O).
Proof.
intros ly S O HO W mem md HAR. unfold dpg_FP. apply sink_closed_cons; [cbn; unfold A_G_REC; lia|].
apply sink_closed_cons; [cbn; unfold A_REC_SPILL; lia|]. apply sink_closed_ablocks_fp.
apply Forall_forall. intros [p n] Hpn. cbn [fst].
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hpn)) as (_ & H4096 & _). lia.
Qed.

(* a byte of the walk's footprint is a byte of g_rec, of record.spill or of one of the recorder's blocks *)
Lemma dpg_inFP : forall O a, inFP (dpg_FP O) a ->
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
exists p n, In (p, n) O /\ p <= a < p + req_size n.
Proof.
intros O a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. left. exact Ha.
- left. right. exact Ha.
- right. apply (inFP_ablocks_fp_inv O a). exists r. split; [exact Hr | exact Ha].
Qed.

(* the read-only bytes keep the image's bytes along the walk: no footprint byte is read only *)
Lemma dpg_rodata_kept : forall STK sp0 ly S W mem md O own lyc Sc Wc memc mdc k,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp0 (dpg_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros STK sp0 ly S W mem md O own lyc Sc Wc memc mdc k HAR0 HO HJ HR a Hro Hown Herr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (cmd_ro_prog_apart a Hro) as [Himg Hpg].
rewrite (F3 a Himg Hown Herr); [exact (HR a Hro Hown Herr)|].
apply fp_spares_closed; [exact (dpg_FP_closed ly S O HO W mem md HAR0)|].
intros HF. destruct (dpg_inFP O a HF) as [Hg | (p & n & Hpn & Hr)].
- exact (Hpg (dpg_in_PG a Hg)).
- exact (blk_img SEGS B LAWS ly S W mem md p n a HAR0 (HO _ Hpn) Hr Himg).
Qed.

(* a store to g_rec or record.spill is one the journal admits: the bytes are the call's footprint and the
   program's statics (CmdBSyms' ts_prog) *)
Lemma dpg_awr_slot : forall STK sp0 O bl0 blc fr0 ly own a,
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
awr_byte SEGS B STK sp0 (dpg_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Ha. right; right; right; right. left.
split; [|split].
- destruct Ha as [Ha | Ha];
  [ exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]
  | exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; lia] ].
- rewrite (ts_prog B HB), <- dpg_PG_tfib. exact (dpg_in_PG a Ha).
- apply cmd_prog_img. exact (dpg_in_PG a Ha).
Qed.

(* a heap string and its word tail lie outside the slot's words: a heap block is off the image, and the slot's
   words are words of g_rec / record.spill *)
Lemma dpg_arg_out : forall ly S (W : world SEGS) mem md p (x : list byte) c,
AR SEGS B ly S W mem md -> A_G_REC + OFF_CALLS <= c -> c + 16 <= A_REC_SPILL + SC_SIZE -> c mod 8 = 0 ->
((c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL) ->
in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) ->
4096 <= p /\
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= p + i /\ p + i + 8 <= 2 ^ 63 /\ ~ (c <= p + i < c + 16)) /\
(forall a, p + Z.of_nat (length x) < a < p + Z.of_nat (length x) - (p + Z.of_nat (length x)) mod 8 + 8 ->
  0 <= a < 2 ^ 63 /\ ~ (c <= a < c + 16)).
Proof.
intros ly S W mem md p x c HAR Hc1 Hc2 Hc8 Hc3 (pb & pk & Hin & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (e := p + Z.of_nat (length x)).
pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as He8.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pk HAR Hin) as (Hb16 & H4096 & Hpc & _ & _ & _ & Hkr).
pose proof (req_size_pos pk ltac:(lia)) as [_ Hreq].
pose proof (blk_off_imgP B ly S W mem md pb pk HAR Hin) as Hoff. unfold off_img in Hoff.
pose proof alloc_ceiling_value as Hac.
unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in Hc1, Hc2.
split; [lia|]. split.
- intros i Hi. lia.
- intros a Ha. subst e. destruct Hoff as [Hoff | Hoff].
  + assert (Hw : p + Z.of_nat (length x) - (p + Z.of_nat (length x)) mod 8 + 8 <= 0x10000).
    { pose proof (Z.div_mod (p + Z.of_nat (length x)) 8 ltac:(lia)) as Hd.
      assert ((p + Z.of_nat (length x)) / 8 < 0x2000) by (apply Z.div_lt_upper_bound; lia). lia. }
    lia.
  + lia.
Qed.

Lemma dpg_J_of_X : dpg_X_stmt B MT -> dpg_J_stmt B MT.
Proof.
intros HX ly S W regs mem md ch pu x R O CTX lyc Sc Wc regs1 memc mdc Q1 O1 MID BLK HREC HO1 R9 HBLK HSTR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CTX as (HPRE & HAP & HROD & HRO & H10 & Hpu & HBLK0 & HSTR0 & HLEN & HAPO & HREP & Hfr8 & Hev & Hlive & MOK).
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
assert (HspR : 2 ^ 46 <= spZ regs1 <= 2 ^ 47 - 48) by (rewrite Hsp1; unfold DPG_FRAME; lia).
assert (Hsp16 : spZ regs1 mod 16 = 0).
{ rewrite Hsp1. unfold DPG_FRAME. replace (spZ regs - 48) with (spZ regs + (-3) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hal16. }
assert (HFR1 : forall j r, nth_error dpg_saved j = Some r ->
  aval_mem (rdW Wc memc) (spZ regs1 + 40 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. rewrite Hsp1. unfold DPG_FRAME.
  replace (spZ regs - 48 + 40 - 8 * Z.of_nat j) with (spZ regs - 8 - 8 * Z.of_nat j) by lia. exact (HFR j r Hj). }
(destruct (dpg_join_seed B HB cmd_prog_writable lyc Sc Wc memc mdc regs1 regs (dpg_c R) HAR HspR Hsp16 R8
  Hc1 Hc2 Hc8 Hc3' R19 HFR1) as [HS SHOK]).
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (dpg_extra regs)))) by apply Eimg_env.
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs1 (dpg_extra regs))) n = getr regs1 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
remember (Eimg (Ereg regs1 (dpg_extra regs))) as E eqn:HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 48) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp1).
assert (Hcr : 0 <= dpg_c R < 2 ^ 64) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia).
assert (E8u : bv_unsigned (ew E 8) = dpg_c R)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; exact Hcr).
(* 0x8d180 .. 0x8d1b0: the two checks on the slot, c->fn := 24, c->nargs := 0; then bnez s1 *)
(paj_run_tok RUN HS HJ SHOK Bspan).
{ (awr_ok_tac; eapply awr_ok_cons_gen; [reflexivity | exact E8u | | apply awr_ok_nil];
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply dpg_awr_slot;
  apply (dpg_slot_PG (dpg_c R)); [exact Hc1 | exact Hc2 | exact Hc3' | lia]). }
lazymatch goal with Hfr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?m1) |- _ =>
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (dpg_c R <= a < dpg_c R + 8) ->
  aview SEGS (w_H Wc) m1 a = aview SEGS (w_H Wc) memc a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => dpg_c R <= a < dpg_c R + 8) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E8u in Hrr; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
(* the call of xstrdup from any state that keeps the join's memory outside the slot's first word and holds the
   two stores: the next segment's statement *)
assert (HXcall : forall (regsx : bvmap 5 word) memx mdx (sx : Z),
  ajournal SEGS B DPG_STK (spZ regs) (dpg_FP O) ly S W mem md [] lyc Sc Wc memx mdx (rec_spill_frees R) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dpg_c R <= a < dpg_c R + 8) ->
     aview SEGS (w_H Wc) memx a = aview SEGS (w_H Wc) memc a) ->
  aval_mem (rdW Wc memx) (dpg_c R + CALL_OFF_FN) 4 REC_DESCRIPTORS_PANEL_GET ->
  aval_mem (rdW Wc memx) (dpg_c R + CALL_OFF_NARGS) 4 0 ->
  getr regsx 2 = getr regs1 2 -> getr regsx 3 = getr regs1 3 -> getr regsx 4 = getr regs1 4 ->
  getr regsx 8 = getr regs1 8 -> getr regsx 19 = getr regs1 19 ->
  (forall r, 21 <= r <= 27 -> getr regsx (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  getr regsx 1 = Z_to_bv 64 (BASE + DPG_RET_X) -> getr regsx 10 = w64 sx ->
  getr regsx 18 = w64 (dpg_c R + 4) -> getr regsx 20 = w64 (SB + (dpg_c R + 4) / 8) ->
  in_blockA (ablocks B lyc Sc) sx (Z.of_nat (length x) + 1) -> astr_atR (rdW Wc memx) sx x ->
  SRr SEGS Wc (mkCfg (mkst regsx (Z_to_bv 64 (SIG CS_xstrdup)) memx (seg_rom SEGS)) mdx)
    (dpg_post B MT ly S W regs mem md R (Some x) O)).
{ intros regsx memx mdx sx HJx KEEP Vfn Vna X2 X3 X4 X8 X19 Xhi X1 X10 X18 X20 HBx HSx.
  apply (HX ly S W regs mem md ch pu x R O CTX lyc Sc Wc regsx memx mdx Q1 O1 sx); try assumption.
  - split; [exact HJx|]. split; [exact MLE|].
    split; [unfold spZ; rewrite X2; exact Hsp1|]. split; [rewrite X3; exact R3|]. split; [rewrite X4; exact R4|].
    split; [rewrite X8; exact R8|]. split; [rewrite X19; exact R19|].
    split; [intros r Hr; rewrite (Xhi r Hr); exact (Rhi r Hr)|].
    intros j r Hj. apply (aval_mem_kept (rdW Wc memc)); [exact (HFR j r Hj)|].
    intros kk Hkk.
    assert (Hj6 : (j < 6)%nat) by (apply (proj1 (nth_error_Some dpg_saved j)); rewrite Hj; discriminate).
    apply KEEP; [lia|]. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *. lia.
  - apply HREC; [exact Vfn | exact Vna|].
    intros a Ha Hna. apply KEEP; [|exact Hna].
    destruct Ha as [Ha | [Ha | (pn & Hpn & Hr)]]; [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia|].
    assert (Hpn' : In pn (ablocks B ly S))
      by (apply (rec_repA_in B ly S (rdW W mem) R O HREP); apply BO1; apply HO1; exact Hpn).
    destruct pn as [pb pk]. destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pk HAR0 Hpn') as (_ & H4096 & Hpc & _ & _ & _ & Hkr).
    cbn [fst snd] in Hr. pose proof (req_size_pos pk ltac:(lia)) as [_ Hreq]. lia. }
destruct (dpg_arg_out lyc Sc Wc memc mdc pu x (dpg_c R) HAR Hc1 Hc2 Hc8 Hc3' HBLK) as (Hpu4 & AO1 & AO2).
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
  assert (EXL1 : forall n, (n < 32)%nat -> ew Ex n = ew E n)
  by (intros n Hn; repeat (rewrite ew_ewset_other by lia); reflexivity) end.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s1 <> 0: the string uri is handed over *)
  (paj_run_tok RUN HS HJ SHOK Bspan).
  { awr_ok_tac; eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_nil];
    [first [exact E8u | rewrite (EXL1 8%nat ltac:(lia)); exact E8u]|].
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply dpg_awr_slot;
    apply (dpg_slot_PG (dpg_c R)); [exact Hc1 | exact Hc2 | exact Hc3' | lia]. }
  (* at the call: the registers, the memory kept and the slot's two words *)
  pmkst HS.
  lazymatch goal with HS : st_ok _ ?Ex2 ?SSX (restrict _ ?ms2) |- _ =>
  assert (EXL2 : forall n, (n < 32)%nat -> ew Ex2 n = ew E n)
    by (intros n Hn; repeat (rewrite ew_ewset_other by lia); apply EXL1; exact Hn);
  assert (KR : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs ms2) r = getr regs1 r)
    by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H Wc) _ _ _ r HS), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite ?(EXL2 (Z.to_nat (bv_unsigned r)) ltac:(lia)); apply EE; lia);
  match goal with Hfr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ (ms_mem ms2)) |- _ =>
    lazymatch m1 with memc => fail | _ =>
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (dpg_c R <= a < dpg_c R + 8) ->
      aview SEGS (w_H Wc) (ms_mem ms2) a = aview SEGS (w_H Wc) memc a)
    by (intros a Ha Hn; rewrite <- (KEEP1 a Ha Hn);
        apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => dpg_c R <= a < dpg_c R + 8) Hfr);
        [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
            rewrite ?(EXL1 8%nat ltac:(lia)), ?E8u in Hrr; lia|]);
          destruct Hin
        | exact Ha | exact Hn ]) end end;
  let r1 := eval vm_compute in (nth 1 (ss_mem SSX) dpg_slot_r) in
  pose proof (st_ok_region_nth (segs:=SEGS) Ex2 SSX (restrict (w_H Wc) ms2) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRs;
  cbn [ms_mem restrict] in HRs;
  assert (E8x : bv_unsigned (ew Ex2 8) = dpg_c R) by (first [exact E8u | rewrite (EXL2 8%nat ltac:(lia)); exact E8u]);
  pose proof (field_of_region (segs:=SEGS) Ex2 _ 8 (dpg_c R) _ _ _ _ _ 0 4 (SLit 24) 24 HRs E8x
    ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V0;
  pose proof (field_of_region (segs:=SEGS) Ex2 _ 8 (dpg_c R) _ _ _ _ _ 4 4 (SLit 0) 0 HRs E8x
    ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V4;
  change (N.to_nat 4) with 4%nat in V0, V4; rewrite Z.add_0_r in V0;
  pose proof (st_ok_restrict_reg SEGS (w_H Wc) _ _ _ (20%bv : bv 5) HS) as P20;
  let v20 := eval vm_compute in (sr_get (ss_regs SSX) (20%bv : bv 5)) in change (sr_get (ss_regs SSX) (20%bv : bv 5)) with v20 in P20;
  pose proof (st_ok_restrict_reg SEGS (w_H Wc) _ _ _ (18%bv : bv 5) HS) as P18;
  let v18 := eval vm_compute in (sr_get (ss_regs SSX) (18%bv : bv 5)) in change (sr_get (ss_regs SSX) (18%bv : bv 5)) with v18 in P18;
  pose proof (st_ok_restrict_reg SEGS (w_H Wc) _ _ _ (1%bv : bv 5) HS) as P1;
  let v1 := eval vm_compute in (sr_get (ss_regs SSX) (1%bv : bv 5)) in change (sr_get (ss_regs SSX) (1%bv : bv 5)) with v1 in P1;
  pose proof (st_ok_restrict_reg SEGS (w_H Wc) _ _ _ (10%bv : bv 5) HS) as P10;
  let v10 := eval vm_compute in (sr_get (ss_regs SSX) (10%bv : bv 5)) in change (sr_get (ss_regs SSX) (10%bv : bv 5)) with v10 in P10
  end.
  rewrite ?wvb_collapse in HJ.
  assert (E8 : ew E 8 = Z_to_bv 64 (dpg_c R)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
  assert (E19 : ew E 19 = Z_to_bv 64 SB) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ => apply (HXcall rg mm _ pu HJ KEEP2) end.
  + unfold CALL_OFF_FN. rewrite Z.add_0_r. exact (aval_mem_view SEGS (w_H Wc) _ _ _ _ V0).
  + unfold CALL_OFF_NARGS. exact (aval_mem_view SEGS (w_H Wc) _ _ _ _ V4).
  + apply KR. vm_compute. reflexivity.
  + apply KR. vm_compute. reflexivity.
  + apply KR. vm_compute. reflexivity.
  + apply KR. vm_compute. reflexivity.
  + apply KR. vm_compute. reflexivity.
  + intros r Hr. apply KR.
    assert (Hrr : r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hrr as [-> | Hrr]; [vm_compute; reflexivity|]). subst r. vm_compute. reflexivity.
  + rewrite P1. lazymatch goal with H : img_env _ _ E |- _ => exact (codeptr_val E 27872 H) end.
  + rewrite P10. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 9%nat 9%bv eq_refl). exact R9.
  + rewrite P18. cbn [sv_denot]. rewrite E8u. reflexivity.
  + rewrite P20. rewrite (denot_shx E 8 19 4 (dpg_c R) SB E8 E19) by (unfold SB, A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE in *; lia).
    reflexivity.
  + exact HBLK.
  + destruct HSTR as [Hab Hnz]. split; [|exact Hnz]. intros i Hi.
    pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
    destruct (AO1 (Z.of_nat i) ltac:(lia)) as (A1 & A2 & A3).
    rewrite (KEEP2 (pu + Z.of_nat i)) by lia. exact (Hab i Hi).
- (* s1 = 0: not reached, uri is a heap string *)
  exfalso.
  rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  rewrite ?U_SOff in Hc. rewrite ?(EXL1 9%nat ltac:(lia)) in Hc. rewrite (EE 9%nat 9%bv eq_refl), R9 in Hc.
  rewrite unsigned_lit_small in Hc by lia.
  assert (Hp0 : pu = 0).
  { rewrite Z.add_0_r in Hc. unfold U in Hc. cbn [sv_denot] in Hc. rewrite zcanon_small in Hc by lia. exact Hc. }
  lia.
Qed.

End e.
End f.
End d.
