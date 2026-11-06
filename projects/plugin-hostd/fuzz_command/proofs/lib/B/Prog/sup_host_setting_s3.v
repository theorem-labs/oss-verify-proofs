(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of descriptors_get (plugin-hostd/fuzz_command.asan) from the join of
   record()'s arms to the tail jump into answer, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and ACh2.v (a walk
   segment: run, call out by cl_callS, resume) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_get_s3.v, with its module paths and module names changed; 445 of its 524 lines of code are new or changed and 934 lines of the source are left out. *)
(* A segment lemma of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan), on the
   points and statements of sup_host_setting_s0.v:
   - hs_seg_rec: from REC (0x8b64c, back from record(6), a0 = c) `mv s11,a0; mv a1,s6`, the call of arg_line
     (0x8b128, at 0x8b654) through cl_callS_wide (arg_line writes c->nargs and c->args[0], program statics in the
     whole call's footprint), back at AL (0x8b658).
   The B twin of the ASan walk's hs_seg_al (lib/A/Prog/sup_host_setting_s4.v on e323bbe76d2, a call of arg_i there),
   with B's frame: every call is made at the realigned sp1 = hs_sp1 sp0, with s0 = sp0, so the callee's frame chain
   is the entry's with the prologue's frame record pushed on it (hs3_achain, achain_push). Shared helpers of the walk (the whole call's footprint, the line
   and the tokens at a later state, the frame kept by a callee) are here as hs3_*. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c rec_canonical_c record_c arg_line_c arg_s_c xmalloc_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_host_setting_aux sup_host_setting_s1 sup_host_setting_s0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas RecBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the shadow base atom (s10) and its span, the token executor's Bx / Bspan *)
Definition hs3_Bx : sv := SOff 26 0.
Definition hs3_Bspan : Z * Z := (HS_SB, HS_SB + 2 ^ 44 - 1).

Lemma hs3_stk : SUP_HOST_SETTING_STK = 16736.
Proof. vm_compute. reflexivity. Qed.

Lemma hs3_wl_nonneg : forall l, 0 <= hs_words_len l.
Proof. intros l. unfold hs_words_len. induction l as [|w l IH]; cbn [fold_right]; lia. Qed.

(* the realigned stack pointer: 16-aligned, 160 or 176 below the entry sp *)
Lemma hs3_sp1 : forall sp0, sp0 mod 16 = 0 -> 0 <= sp0 ->
  sp0 - 176 <= hs_sp1 sp0 <= sp0 - 160 /\ (hs_sp1 sp0 - sp0) mod 16 = 0 /\ hs_sp1 sp0 mod 32 = 0.
Proof.
intros sp0 H16 H0. unfold hs_sp1.
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as M.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16.
assert (Hm : (sp0 - 160) mod 32 = 0 \/ (sp0 - 160) mod 32 = 16).
{ assert (E : (sp0 - 160) mod 16 = 0) by (rewrite Zminus_mod, H16; reflexivity).
  pose proof (Z.div_mod (sp0 - 160) 16 ltac:(lia)) as D2. rewrite E in D2. lia. }
split; [lia|]. split.
- destruct Hm as [Hm|Hm].
  + replace (32 * ((sp0 - 160) / 32) - sp0) with (-160) by lia. reflexivity.
  + replace (32 * ((sp0 - 160) / 32) - sp0) with (-176) by lia. reflexivity.
- rewrite Z.mul_comm. apply Z.mod_mul. lia.
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
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

Definition hs3_pair_dec (a b : Z * Z) : {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma hs3_grec_in : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) recb_PG.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.
Lemma hs3_spill_in : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) recb_PG.
Proof. intros a Ha. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. Qed.

(* the slot's bytes are bytes of the recorder's two statics, both in the whole call's footprint *)
Lemma hs3_slot_rec : forall R a, rec_slot R <= a < rec_slot R + CALL_SIZE -> hs_in_rec a.
Proof.
intros R a Ha. destruct (hs_slot_bounds R) as (B1 & B2 & _ & [B4 | B4]); unfold hs_in_rec; [left | right];
  unfold A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE, OFF_ANSWER, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Lemma hs3_rec_fp : forall O a, hs_in_rec a -> inFP (hs_FP O) a /\ Exists (in_zr a) recb_PG.
Proof.
intros O a [Ha | Ha]; split.
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [apply in_eq | cbn [fst snd]; lia].
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [apply in_cons, in_eq | cbn [fst snd]; lia].
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma hs3_slot_cases : forall R,
  (exists i, 0 <= i < REC_CALLS_MAX /\ rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ rec_slot R = A_REC_SPILL.
Proof.
intros R. unfold rec_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H].
- left. exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity].
- right. reflexivity.
Qed.

(* a byte of a live block that is none of the recorder's is outside the footprint *)
Lemma hs3_blk_outFP : forall ly S (W : world SEGS) mem md O p n a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (p, n) (ablocks B ly S) -> ~ In (p, n) O -> p <= a < p + req_size n -> ~ inFP (hs_FP O) a.
Proof.
intros ly S W mem md O p n a HAR HO Hin Hno Ha Hfp.
unfold hs_FP in Hfp. apply inFP_cons in Hfp as [Hg | Hfp].
{ exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin Ha (hh_prog_img B MT HH a (hs3_grec_in a Hg))). }
apply inFP_cons in Hfp as [Hs | Hfp].
{ exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin Ha (hh_prog_img B MT HH a (hs3_spill_in a Hs))). }
destruct (inFP_ablocks_fp_inv O a Hfp) as (q & m & Hqm & Hr).
assert (Hne : (q, m) <> (p, n)) by (intros E; rewrite E in Hqm; exact (Hno Hqm)).
pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR (HO (q, m) Hqm) Hin Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* an image byte that is none of the program's statics is outside the footprint *)
Lemma hs3_img_outFP : forall ly S (W : world SEGS) mem md O a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
in_img SEGS a -> ~ Exists (in_zr a) recb_PG -> ~ inFP (hs_FP O) a.
Proof.
intros ly S W mem md O a HAR HO Himg Hpg Hfp.
unfold hs_FP in Hfp. apply inFP_cons in Hfp as [Hg | Hfp].
{ exact (Hpg (hs3_grec_in a Hg)). }
apply inFP_cons in Hfp as [Hs | Hfp].
{ exact (Hpg (hs3_spill_in a Hs)). }
destruct (inFP_ablocks_fp_inv O a Hfp) as (q & m & Hqm & Hr).
exact (blk_img SEGS B LAWS ly S W mem md q m a HAR (HO (q, m) Hqm) Hr Himg).
Qed.

(* the read-only bytes lie outside the whole call's footprint (arodata_ok_journalP's premise) *)
Lemma hs3_ro_off_fp : forall x, hs_cx B MT x -> forall a, in_roP SEGS RLO RHI a -> ~ inFP (hs_FP (i_O x)) a.
Proof.
intros x CX a Hro.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
pose proof HPRE as (HAR0 & _).
destruct (hh_ro_prog_apart B MT HH a Hro) as [Himg Hnpg].
exact (hs3_img_outFP _ _ _ _ _ (i_O x) a HAR0 (fun pn H => proj1 (hs_rec_own B _ _ _ _ _ HREP0 pn H)) Himg Hnpg).
Qed.

(* the read-only view at a state of the call *)
Lemma hs3_rod_now : forall x fpos lyc Sc Wc memc mdc k, hs_cx B MT x ->
  ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
    [(0, fpos)] lyc Sc Wc memc mdc k ->
  arodata_okP SEGS RLO RHI B (rdW Wc memc) /\ cmd_ro_ok (rdW Wc memc).
Proof.
intros x fpos lyc Sc Wc memc mdc k CX HJ.
pose proof CX as (_ & HROD & _).
assert (H : arodata_okP SEGS RLO RHI B (rdW Wc memc)).
{ assert (RELRO : forall a, RLO <= a < RHI -> in_img SEGS a)
    by (intros a Ha; exact (proj1 (hh_ro_prog_apart B MT HH a (or_intror Ha)))).
  exact (arodata_ok_journalP SEGS RLO RHI RELRO (RO := hh_RRO B MT HH) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
    (hs3_ro_off_fp x CX) HROD). }
split; [exact H|]. exact (hh_ro_ok_of_aro B MT HH _ _ _ _ _ (proj1 HJ) H).
Qed.

(* a byte of the whole call's footprint lies below the allocator's ceiling: the recorder's statics are image bytes,
   its blocks are heap blocks *)
Lemma hs3_FP_low : forall x a, hs_cx B MT x -> inFP (hs_FP (i_O x)) a -> a < alloc_ceiling.
Proof.
intros x a CX (r & Hr & Hra).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
pose proof HPRE as (HAR0 & _).
pose proof (@ASAN_CEIL_range rc) as [C1 _]. unfold ASAN_CEIL in C1.
unfold hs_FP in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Hra. unfold A_G_REC, REC_SIZE in Hra. lia.
- cbn [fst snd] in Hra. unfold A_REC_SPILL, SC_SIZE in Hra. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p q] & <- & Hpq). cbn [fst snd] in Hra.
  destruct (hs_rec_own B _ _ _ _ _ HREP0 (p, q) Hpq) as [Hin _].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p q HAR0 Hin) as (_ & _ & Hpc & _ & _ & _ & Hq).
  pose proof (req_size_pos q ltac:(lia)) as [_ Hrq]. lia.
Qed.

(* an 8-byte field read as a word *)
Lemma hs3_rdword_aval : forall (rd : reader) a v, aval_mem rd a 8 v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v Hc Hv. unfold rdword.
pose proof (Hc 0%nat ltac:(lia)) as H0. pose proof (Hc 1%nat ltac:(lia)) as H1. pose proof (Hc 2%nat ltac:(lia)) as H2.
pose proof (Hc 3%nat ltac:(lia)) as H3. pose proof (Hc 4%nat ltac:(lia)) as H4. pose proof (Hc 5%nat ltac:(lia)) as H5.
pose proof (Hc 6%nat ltac:(lia)) as H6. pose proof (Hc 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7. rewrite Z.add_0_r in H0.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. f_equal. apply le_bytes8. exact Hv.
Qed.

(* the frame chain a callee's afn_pre asks for, at a call from sp1 with s0 = sp0 (a class-B site, a Theorem Labs lane's
   PASS4-REFIT.md section B): the entry's chain (afn_pre's), kept above sp0 by the journal, with the frame record
   (sp0, ra, s0) the prologue stored at sp0 - 8 and sp0 - 16 pushed on it (achain_push, lib/Reusable/YCbq.v:413);
   at ly_top - 16 <= sp0 the chain is empty *)
Lemma hs3_achain : forall x fpos lyc Sc Wc memc mdc k (regsc : bvmap 5 word), hs_cx B MT x ->
  ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
    [(0, fpos)] lyc Sc Wc memc mdc k ->
  hs_frame (rdW Wc memc) (spZ (i_regs x)) (i_regs x) ->
  spZ regsc = hs_sp1 (spZ (i_regs x)) -> getr regsc 8 = w64 (spZ (i_regs x)) ->
  exists ch, achain lyc (rdW Wc memc) (spZ regsc) (s0Z regsc) ch.
Proof.
intros x fpos lyc Sc Wc memc mdc k regsc CX HJ HFR Hsp H8.
pose proof CX as (HPRE & _). pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof hs3_stk as FS.
pose proof (@ASAN_CEIL_range rc) as [C1 _]. unfold ASAN_CEIL in C1.
set (sp0 := spZ (i_regs x)) in *.
destruct (hs3_sp1 sp0 Hal16 ltac:(lia)) as (S1a & S1b & _).
assert (Hs0 : s0Z regsc = sp0) by (unfold s0Z; rewrite H8; unfold w64; apply unsigned_lit_small; lia).
rewrite Hs0, Hsp.
destruct (Z_lt_le_dec sp0 (ly_top lyc - 16)) as [Hlt | Hge].
2:{ exists []. left. split; [right; left; exact Hge | reflexivity]. }
assert (H8m : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. exists (2 * q). lia. }
pose proof (HFR 0%nat 1 eq_refl) as R0. pose proof (HFR 1%nat 8 eq_refl) as R1. cbn [Z.of_nat] in R0, R1.
eexists.
apply (achain_push lyc (rdW (i_W x) (i_mem x)) (rdW Wc memc) sp0 (s0Z (i_regs x)) (raZ (i_regs x)) (i_ch x)
  (hs_sp1 sp0)).
- apply (achain_ly_top (i_ly x)); [exact Etop | exact Hch].
- rewrite Etop. lia.
- intros a Ha. apply F1; [lia | lia |]. intros Hfp. pose proof (hs3_FP_low x a CX Hfp). lia.
- apply hs3_rdword_aval; [|apply bv_unsigned_in_range].
  replace (sp0 - 8) with (sp0 - 8 - 8 * 0) by lia. exact R0.
- apply hs3_rdword_aval; [|apply bv_unsigned_in_range].
  replace (sp0 - 16) with (sp0 - 8 - 8 * 1) by lia. exact R1.
- exact Hra4.
- lia.
- exact H8m.
- exact Hlt.
- lia.
Qed.

(* a string argument of the entry (inside a live block that is none of the recorder's) at a state of the call *)
Lemma hs3_str_now : forall x fpos lyc Sc Wc memc mdc k O1 Nw Rest p s, hs_cx B MT x ->
  ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
    [(0, fpos)] lyc Sc Wc memc mdc k ->
  hs_ba B x lyc Sc O1 Nw Rest ->
  hs_str B (i_ly x) (i_S x) (rdW (i_W x) (i_mem x)) (i_O x) p s ->
  in_blockA (ablocks B lyc Sc) p (Z.of_nat (length s) + 1) /\ astr_atR (rdW Wc memc) p s /\
  Z.of_nat (length s) + 1 <= LMAX + 1 /\ p <> 0 /\
  exists q m, In (q, m) (ablocks B lyc Sc) /\ q <= p /\ p + Z.of_nat (length s) + 1 <= q + m /\ ~ In (q, m) (i_O x).
Proof.
intros x fpos lyc Sc Wc memc mdc k O1 Nw Rest p s CX HJ HBA HARG.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
pose proof HPRE as (HARe & _).
pose proof HBA as (BA1 & BA2 & BA3 & _).
assert (HO : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x)))
  by (intros pn Hpn; exact (proj1 (hs_rec_own B _ _ _ _ _ HREP0 pn Hpn))).
unfold hs_str in HARG. destruct HARG as (Hp0 & HSTR & Hnle & HBLK & HAP).
destruct HBLK as (q & m & Hqm & Hq1 & Hq2).
assert (Hno : ~ In (q, m) (i_O x)).
{ intros Hin. rewrite Forall_forall in HAP. pose proof (HAP (q, m) Hin) as Hap.
  unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
assert (Hqc : In (q, m) (ablocks B lyc Sc))
  by exact (Permutation_in _ (Permutation_sym BA1) (in_or_app _ _ _ (or_intror (BA3 _ Hqm Hno)))).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARe Hqm) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hmr).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
assert (Hkept : forall a, q <= a < q + req_size m -> rdW Wc memc a = rdW (i_W x) (i_mem x) a).
{ intros a Ha. replace a with (q + (a - q)) by lia.
  pose proof HJ as (_&_&_&_&_&_&_&_&_& F2 &_).
  apply (F2 q m (a - q) Hqm Hqc ltac:(lia)).
  exact (hs3_blk_outFP _ _ _ _ _ (i_O x) q m (q + (a - q)) HARe HO Hqm Hno ltac:(lia)). }
split; [exists q, m; split; [exact Hqc | lia]|].
split.
{ destruct HSTR as [HB Hnz]. split; [|exact Hnz]. intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (Hkept (p + Z.of_nat i)) by lia. exact (HB i ltac:(rewrite length_app; cbn [length]; lia)). }
split; [exact Hnle|]. split; [exact Hp0|].
exists q, m. split; [exact Hqc|]. split; [lia|]. split; [lia | exact Hno].
Qed.

(* a callee's journal keeps the saved registers, the frame's flag pointer, and everything outside its window and
   footprint above alloc_ceiling *)
Lemma hs3_frame_kept_on : forall (rd rd' : reader) sp0 regs,
  (forall b, sp0 - 104 <= b < sp0 -> rd' b = rd b) -> hs_frame rd sp0 regs -> hs_frame rd' sp0 regs.
Proof.
intros rd rd' sp0 regs Heq H j r Hj k Hk.
assert (Hj13 : (j < length HS_SAVED)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
change (length HS_SAVED) with 13%nat in Hj13.
rewrite Heq by lia. exact (H j r Hj k Hk).
Qed.

Lemma hs3_aval_on : forall (rd rd' : reader) a n v,
  (forall b, a <= b < a + Z.of_nat n -> rd' b = rd b) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Heq H k Hk. rewrite Heq by lia. exact (H k Hk). Qed.

(* the frame's bytes are outside the whole call's footprint and above 4096 *)
Lemma hs3_frame_facts : forall x fpos lyc Sc Wc memc mdc k, hs_cx B MT x ->
  ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
    [(0, fpos)] lyc Sc Wc memc mdc k ->
  In (0, fpos) (frames Sc) /\ frame_addr lyc 0 fpos = hs_F x fpos /\ flag_addr lyc 0 fpos = hs_FL x fpos /\
  4096 <= hs_F x fpos /\ hs_F x fpos + 64 <= alloc_ceiling /\ hs_F x fpos mod 64 = 0.
Proof.
intros x fpos lyc Sc Wc memc mdc k CX HJ.
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (0, fpos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr lyc 0 fpos = hs_F x fpos).
{ unfold hs_F, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (EL : flag_addr lyc 0 fpos = hs_FL x fpos).
{ unfold hs_FL, flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF2 & _). rewrite EF2. reflexivity. }
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HARc Hin) as (F1 & F2 & _).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HARc Hin) as (F3 & _).
rewrite EF in F1, F2, F3. change (fs_frame_bytes 0) with 64 in F2.
split; [exact Hin|]. split; [exact EF|]. split; [exact EL|]. split; [lia|]. split; [lia|].
exact F3.
Qed.

(* the recorder's blocks are at least one byte long *)
Lemma hs3_own_pos : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> 1 <= snd pn.
Proof. intros ly S rd R O (Q & HA & HQ) pn Hpn. exact (proj2 (hs_lay_info _ _ _ _ _ _ HA pn (proj1 (HQ pn) Hpn))). Qed.

(* a heap byte is no read-only image byte (strcat's written range, RtString.v astrcat_realizes) *)
Lemma hs3_heap_norom : forall ly S (W : world SEGS) mem md p n a, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n -> ~ in_rom SEGS a.
Proof.
intros ly S W mem md p n a HAR Hin Ha (sg & Hsg & _ & Hr).
apply (recb_heap_noimg_m B ly S W mem md p n a HAR Hin Ha). exists sg. split; [exact Hsg | exact Hr].
Qed.

(* strcat's word separation (RtString.v aword_end): the source x .. x + len + 1 in one live block, the destination
   tail dt .. dt + len + 1 in another; blocks start 16-aligned and are disjoint, so a source block before the
   destination's ends, rounded up to 8, at or before the destination block's start *)
Lemma hs3_word_sep : forall ly S (W : world SEGS) mem md q m p n x len dt,
  AR SEGS B ly S W mem md -> In (q, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (q, m) <> (p, n) ->
  q <= x -> x + len + 1 <= q + req_size m -> p <= dt -> dt + len + 1 <= p + req_size n ->
  dt + len + 1 <= x \/ aword_end x (len + 1) <= dt.
Proof.
intros ly S W mem md q m p n x len dt HAR Hq Hp Hne H1 H2 H3 H4.
pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR Hq Hp Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hp) as (Hp16 & _).
destruct Hd as [Hd | Hd]; [right | left; lia].
unfold aword_end.
pose proof (Z.div_mod (- (x + (len + 1))) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (- (x + (len + 1))) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod p 16 ltac:(lia)) as D3. rewrite Hp16 in D3.
clear - H2 H3 Hd D1 D2 D3. lia.
Qed.

(* a token of the entry lies, at a state of the call, in a live block that is none of the blocks this call made *)
Lemma hs3_tok_blk : forall x fpos lyc Sc Wc memc mdc k O1 Nw Rest p s, hs_cx B MT x ->
  ajournal SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
    [(0, fpos)] lyc Sc Wc memc mdc k ->
  hs_ba B x lyc Sc O1 Nw Rest ->
  hs_str B (i_ly x) (i_S x) (rdW (i_W x) (i_mem x)) (i_O x) p s ->
  exists q m, In (q, m) (ablocks B lyc Sc) /\ q <= p /\ p + Z.of_nat (length s) + 1 <= q + m /\ ~ In (q, m) Nw.
Proof.
intros x fpos lyc Sc Wc memc mdc k O1 Nw Rest p s CX HJ HBA HARG.
pose proof HBA as (BA1 & _ & BA3 & _ & _ & BA6 & _).
destruct HARG as (_ & _ & _ & (q & m & Hqm & Hq1 & Hq2) & HAP).
assert (Hno : ~ In (q, m) (i_O x)).
{ intros Hin. rewrite Forall_forall in HAP. pose proof (HAP (q, m) Hin) as Hap.
  unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
exists q, m. split; [|split; [lia|split; [lia|]]].
- exact (Permutation_in _ (Permutation_sym BA1) (in_or_app _ _ _ (or_intror (BA3 _ Hqm Hno)))).
- intros HNw. exact (Hno (BA6 _ HNw Hqm)).
Qed.

(* the meter's parts are not negative *)
Lemma hs3_xx_nonneg : forall n, 0 <= XM_XMALLOC MT n.
Proof. intros n. unfold XM_XMALLOC, LIVE_XMALLOC. apply (mo_malloc_nonneg MT (hh_MTL B MT HH)). lia. Qed.
Lemma hs3_xs_nonneg : forall v, 0 <= XM_ARG_S MT v.
Proof. intros v. unfold XM_ARG_S. apply hs3_xx_nonneg. Qed.
Lemma hs3_xl_nonneg : forall T, 0 <= XM_ARG_LINE MT T.
Proof. intros T. unfold XM_ARG_LINE, XM_REC_CANONICAL. apply hs3_xx_nonneg. Qed.

(* ---- REC 0x8b64c: s11 := c, a1 := line, the call of arg_line ---- *)
Lemma hs_seg_rec : forall x, ST_AL B MT x -> ST_REC B MT x.
Proof.
intros x AL. unfold ST_REC.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest CX FXR MID REP RG R10.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) & R18 & R19 & R20 & R21 & R22 & R23).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (hs_slot_bounds (i_R x)) as (SL1 & SL2 & _ & _).
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
pose proof hs3_stk as FS.
assert (HALS2 : ARG_LINE_STK = 16480) by (vm_compute; reflexivity).
assert (HALS : 0 <= ARG_LINE_STK) by (rewrite HALS2; lia).
assert (HPSB : as_prog_static B = recb_PG) by (rewrite (ts_prog B (hh_HB B MT HH)); reflexivity).
pose (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HS : st_ok_pi SEGS VAL E (mkSS HS_REC sr_atoms [] None (mkFacts [(26%nat, mkAF HS_SB HS_SB 0)] [] []))
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_REC)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact (regs_ok_Eimg_Ereg regs1 []).
  - reflexivity.
  - constructor.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 26%nat 26%bv eq_refl), K26. unfold w64.
    rewrite !unsigned_lit_small by (unfold HS_SB; lia). rewrite Z.pow_0_r, !Z.mod_1_r. unfold HS_SB. lia. }
assert (SHOK : sh_ok SEGS hs3_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
clearbody E.
(* 0x8b64c .. 0x8b654: s11 := c, a1 := line, the call of arg_line *)
paj_run_tok RUN HS HJ SHOK hs3_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
assert (KEQ : forall a, aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hr & _). destruct Hr. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite (EE 2%nat 2%bv eq_refl), K2 in P2. rewrite (EE 3%nat 3%bv eq_refl), K3 in P3. rewrite (EE 4%nat 4%bv eq_refl), K4 in P4.
rewrite (EE 8%nat 8%bv eq_refl), K8 in P8. rewrite (EE 9%nat 9%bv eq_refl), K9 in P9.
rewrite (EE 10%nat 10%bv eq_refl), R10 in P10. rewrite (EE 22%nat 22%bv eq_refl), R22 in P11.
rewrite (EE 18%nat 18%bv eq_refl), R18 in P18. rewrite (EE 19%nat 19%bv eq_refl), R19 in P19.
rewrite (EE 20%nat 20%bv eq_refl), R20 in P20. rewrite (EE 21%nat 21%bv eq_refl), R21 in P21.
rewrite (EE 22%nat 22%bv eq_refl), R22 in P22. rewrite (EE 23%nat 23%bv eq_refl), R23 in P23.
rewrite (EE 24%nat 24%bv eq_refl), K24 in P24. rewrite (EE 25%nat 25%bv eq_refl), K25 in P25.
rewrite (EE 26%nat 26%bv eq_refl), K26 in P26. rewrite (EE 10%nat 10%bv eq_refl), R10 in P27.
assert (Qsp : spZ (ms_regs ms) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))).
{ unfold spZ at 1. rewrite P2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (SIGAL : SIG CS_arg_line = BASE + AF_arg_line).
{ rewrite (hh_sigp B MT HH CS_arg_line ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
rewrite SIGAL.
(* arg_line's premises at the call *)
pose proof HJ as (HARc & _ & _ & _ & _ & HFRSc & HNEVc & _).
destruct (hs3_rod_now x fpos lyc Sc Wc (ms_mem ms) mdv k CX HJ) as [HRODc HROc].
destruct (hs3_achain x fpos lyc Sc Wc (ms_mem ms) mdv k (ms_regs ms) CX HJ
  (hs3_frame_kept_on (rdW Wc memc) _ _ _ (fun b _ => KEQ b) HFR) ltac:(rewrite Qsp; lia) P8) as (ch1 & HCH).
destruct (hs3_str_now x fpos lyc Sc Wc (ms_mem ms) mdv k O1 [] Rest (i_pl x) (i_line x) CX HJ HBA HLINE)
  as (LB & LSTR & LLEN & _ & q0 & m0 & Hq0 & _ & _ & Hq0O).
assert (REPc : rec_repA B lyc Sc (rdW Wc (ms_mem ms)) (rec_record (i_R x) REC_HOST_SETTING []) O1)
  by exact (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms)) _ _ REP (fun a _ => KEQ a)
    (fun pn H => proj1 (hs_rec_own B _ _ _ _ _ REP pn H))).
assert (HEVc : st_nev Sc + EV_ARG_LINE <= EV_MAX).
{ unfold EV_SUP_HOST_SETTING, hs_k0 in *. unfold EV_ARG_LINE, EV_REC_CANONICAL, EV_ARG_S, EV_XMALLOC in *. lia. }
assert (HLIVEc : blocks_bytes Sc + LIVE_ARG_LINE (i_line x) <= LIVE_MAX).
{ unfold LIVE_SUP_HOST_SETTING in HLIVE. unfold LIVE_ARG_S, LIVE_XMALLOC in HLIVE.
  pose proof (Z.le_max_l (hs_words_len (i_toks x) + 1) 1).
  pose proof (Z.le_max_l (Z.of_nat (length (sarg (Some (dec (Z.of_nat (length (i_toks x))))))) + 1) 1).
  pose proof (Z.le_max_l (Z.of_nat (length (sarg (Some (join_sp (i_toks x))))) + 1) 1).
  pose proof (hs3_wl_nonneg (i_toks x)). lia. }
assert (HMOc : mo_ok MT Sc (XM_ARG_LINE MT (i_line x))).
{ pose proof (hh_MTL B MT HH) as ML.
  apply (mok_station MT (i_S x) Sc (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x)) (hs_m0 MT x) _ ML HMO HMLE).
  - exact (hs3_xl_nonneg (i_line x)).
  - unfold XM_SUP_HOST_SETTING, hs_m0.
    pose proof (hs3_xs_nonneg (Some (dec (Z.of_nat (length (i_toks x)))))).
    pose proof (hs3_xs_nonneg (Some (join_sp (i_toks x)))).
    pose proof (hs3_xx_nonneg (hs_words_len (i_toks x) + 1)).
    pose proof (mo_free_nonneg MT ML). lia. }
(* the raw form arg_line asks (RecBridge.v rec_bridge_slot): the slot, nargs = 0 *)
destruct (rec_bridge_slot B lyc Sc (rdW Wc (ms_mem ms)) (i_R x) REC_HOST_SETTING [] O1 REPc) as (HSL & HNA & _ & _).
(* arg_line writes c->nargs and c->args[0] *)
pose (FP1 := if 0 <? REC_ARGS_MAX
  then [(rec_slot (i_R x) + CALL_OFF_NARGS, rec_slot (i_R x) + CALL_OFF_NARGS + 4);
        (rec_slot (i_R x) + CALL_OFF_ARGS + 8 * 0, rec_slot (i_R x) + CALL_OFF_ARGS + 8 * 0 + 8)]
  else []).
assert (HFP1 : forall a, inFP FP1 a -> rec_slot (i_R x) <= a < rec_slot (i_R x) + CALL_SIZE).
{ intros a (r & Hr & Ha). unfold FP1 in Hr. cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_arg_line)) SUP_HOST_SETTING_STK
    (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc _ k
    ARG_LINE_STK FP1 EV_ARG_LINE (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) (getr (ms_regs ms) 1) ch1 _
    HJ Qsp S1b ltac:(lia) HALS ltac:(lia)).
  - rewrite P3. exact Hgp.
  - rewrite P4. exact Htp.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - replace (spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))) with (spZ (ms_regs ms)) by lia. exact HCH.
  - intros HPRE1.
    exact (hh_arg_line B MT HH fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ ch1 (rec_slot (i_R x)) (i_pl x) 0
      (i_line x) HPRE1 HRODc P10 P11 Hpl HSL HNA ltac:(unfold REC_ARGS_MAX; lia) LB LSTR LLEN HEVc HLIVEc HMOc).
  - intros a Ha. right; right; right; right; left.
    destruct (hs3_rec_fp (i_O x) a (hs3_slot_rec (i_R x) a (HFP1 a Ha))) as [Hfp Hpg].
    split; [exact Hfp|]. split; [rewrite HPSB; exact Hpg | exact (hh_prog_img B MT HH a Hpg)].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFP1 a Ha).
    rewrite FS in Hw. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
(* back at 0x8b658 *)
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & HK2).
cbv zeta in HK2.
destruct HK2 as (HBB2 & HMLE2 & [(Hm6 & _) | (_ & p & Hp4096 & HPERM2 & HAPART & HNA2 & HARG2 & HSTR2)]);
  [unfold REC_ARGS_MAX in Hm6; lia|].
pose proof HJ2c as (HAR2 & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
destruct (hs3_frame_facts x fpos lyc Sc Wc (ms_mem ms) mdv k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
rewrite P1.
refine (AL fpos ly2 S2 W2 mem2 md2 regs2 (k + EV_ARG_LINE) O1 Rest p CX FXR _ _ _ _).
- refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  + unfold hs_k1, hs_k0 in *. unfold EV_ARG_LINE, EV_REC_CANONICAL, EV_XMALLOC. lia.
  + exact (mle_station MT _ _ _ _ _ (hh_MTL B MT HH) HMLE HMLE2).
  + unfold hs_l1. lia.
  + apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFR].
    intros b Hb. rewrite <- (KEQ b). apply J1; [lia | rewrite HALS2; lia |].
    intros Hin. apply HFP1 in Hin. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
  + apply (hs3_aval_on (rdW Wc memc)); [|exact HFL].
    intros b Hb. rewrite <- (KEQ b). apply (J4 0 fpos b HFin).
    * left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 0) with 64. cbn in Hb. lia.
    * intros Hin. apply HFP1 in Hin. cbn in Hb.
      apply (frm_img SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv 0 fpos b HARc HFin);
        [rewrite EFA; change (fs_frame_bytes 0) with 64; lia|].
      destruct (hs3_rec_fp (i_O x) b (hs3_slot_rec (i_R x) b Hin)) as [_ Hpg]. exact (hh_prog_img B MT HH b Hpg).
  + pose proof HBA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
    assert (EB0 : Z.of_nat (length (i_line x)) + 1 = hs_b0 x) by reflexivity.
    rewrite <- EB0.
    split; [|split; [exact BA2|split; [exact BA3|split; [exact BA4|split; [exact BA5|split; [|exact BA7]]]]]].
    * eapply Permutation_trans; [exact HPERM2|]. cbn [app]. apply perm_skip. exact BA1.
    * intros pn [<- | []] Hin.
      destruct (in_dec hs3_pair_dec (p, Z.of_nat (length (i_line x)) + 1) (i_O x)) as [Ho | Hno]; [exact Ho|]. exfalso.
      pose proof (Permutation_in _ (Permutation_sym BA1) (BA3 _ Hin Hno)) as Hc.
      pose proof (proj1 (Forall_forall _ _) HAPART _ Hc) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
- (* the recorder after the append (RecBridge.v rec_bridge_add) *)
  pose proof (canon_length (i_line x)) as HCL.
  assert (HIN2 : In (p, Z.of_nat (length (i_line x)) + 1) (ablocks B ly2 S2))
    by exact (Permutation_in _ (Permutation_sym HPERM2) (in_eq _ _)).
  assert (HnF : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
    ~ (rec_slot (i_R x) + CALL_OFF_NARGS <= a < rec_slot (i_R x) + CALL_OFF_NARGS + 4) ->
    ~ (rec_slot (i_R x) + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) <= a <
       rec_slot (i_R x) + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8) -> ~ inFP FP1 a).
  { intros a _ Hn1 Hn2 (r & Hr & Hrq). unfold FP1 in Hr. cbn in Hr, Hn2.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq; [apply Hn1 | apply Hn2]; lia. }
  refine (rec_bridge_add B lyc Sc ly2 S2 (rdW Wc (ms_mem ms)) (rdW W2 mem2) (i_R x) REC_HOST_SETTING [] O1
    (canon (i_line x)) p (Z.of_nat (length (i_line x)) + 1) REPc ltac:(cbn; lia) _ _ HIN2 _ _ _ ltac:(lia)
    ltac:(lia) ltac:(unfold LMAX in *; lia) HNA2 HARG2 HSTR2).
  + intros a Ha Hn1 Hn2.
    assert (Hpg : Exists (in_zr a) recb_PG) by (destruct Ha as [Ha | Ha]; [exact (hs3_grec_in a Ha) | exact (hs3_spill_in a Ha)]).
    assert (Hpg' : Exists (in_zr a) (as_prog_static B)) by (rewrite HPSB; exact Hpg).
    destruct (prog_static_sep B a (ts_ok B (hh_HB B MT HH)) Hpg') as (Hno & Hne & _).
    apply J3; [exact (hh_prog_img B MT HH a Hpg) | exact Hno | exact Hne |].
    apply fp_spares_closed; [| exact (HnF a Ha Hn1 Hn2)]. apply sink_closed_pos. unfold FP1.
    pose proof (hs_slot_bounds (i_R x)) as (SB1 & _).
    apply Forall_cons; [cbn [fst]; unfold A_G_REC, OFF_CALLS, CALL_OFF_NARGS in *; lia|].
    apply Forall_cons; [cbn [fst]; unfold A_G_REC, OFF_CALLS, CALL_OFF_ARGS in *; lia|].
    apply Forall_nil.
  + intros [q m] Hpn. cbn [fst snd].
    destruct (hs_rec_own B _ _ _ _ _ REPc (q, m) Hpn) as (Hinc & Ha1 & Ha2).
    assert (Hin2 : In (q, m) (ablocks B ly2 S2))
      by exact (Permutation_in _ (Permutation_sym HPERM2) (in_cons _ _ _ Hinc)).
    split; [exact Hin2|].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hinc) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
    intros i Hi. apply (J2 q m i Hinc Hin2 ltac:(lia)).
    intros (r & Hr & Hrq2). unfold FP1 in Hr. cbn in Hr.
    pose proof (hs_slot_bounds (i_R x)) as (SB1 & SB2 & _ & SB4).
    unfold iv_apart in Ha1, Ha2. cbn [fst snd] in Ha1, Ha2.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq2;
      unfold A_G_REC, REC_SIZE, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE, CALL_OFF_NARGS, CALL_OFF_ARGS, OFF_ANSWER in *; lia.
  + intros Hin. apply in_map_iff in Hin as ([q m] & Hq & Hpn). cbn [fst] in Hq. subst q.
    destruct (hs_rec_own B _ _ _ _ _ REPc (p, m) Hpn) as (Hinc & _).
    pose proof (hs3_own_pos _ _ _ _ _ REPc (p, m) Hpn) as Hm1. cbn [snd] in Hm1.
    pose proof (proj1 (Forall_forall _ _) HAPART _ Hinc) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
  + apply (recb_heap_apart_m B ly2 S2 W2 mem2 md2 p _ A_G_REC REC_SIZE HAR2 HIN2); [lia | unfold REC_SIZE; lia|].
    intros a Ha. apply (hh_prog_img B MT HH). exact (hs3_grec_in a Ha).
  + apply (recb_heap_apart_m B ly2 S2 W2 mem2 md2 p _ A_REC_SPILL SC_SIZE HAR2 HIN2); [lia | unfold SC_SIZE; lia|].
    intros a Ha. apply (hh_prog_img B MT HH). exact (hs3_spill_in a Ha).
- split.
  + split; [transitivity (getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact P2]|].
    split; [transitivity (getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact P9]|].
    split; [transitivity (getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact P8]|].
    split; [transitivity (getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact P3]|].
    split; [transitivity (getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact P4]|].
    split; [transitivity (getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact P24]|].
    split; [transitivity (getr (ms_regs ms) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact P25]|].
    transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact P26].
  + split; [transitivity (getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact P18]|].
    split; [transitivity (getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact P19]|].
    split; [transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact P20]|].
    split; [transitivity (getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact P21]|].
    split; [transitivity (getr (ms_regs ms) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact P22]|].
    transitivity (getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact P23].
- transitivity (getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact P27].
Qed.

End e.
End f.
End d.
