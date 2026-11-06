(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:251-253 [Apache-2.0]. The [Apache-2.0 OR MIT] text is used under
   Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_fits.v, with its addresses changed; 260 of its 348 lines of code are new or changed and 709 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), the piece +0x1388 .. +0x13ec
   (0x81afc .. 0x81b60): j_wdec_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v, from inv_I_end to the cut
   jc0. The width decision reads mf+176 = t_in and mf+160 = t_out (0x81b08, 0x81b0c) and writes nothing; a0 ends
   holding SlotModel.n_wok as 1 or 0.

   The run:
     0x81afc .. 0x81b04  a0 := n_r + 1; the abort 0x82614 when 1 <u a0 (n_r is 0 or -1: refuted);
     0x81b08, 0x81b0c    a3 := t_in, a4 := t_out;
     0x81b10 .. 0x81b2c  t_in = 0 goes to the t_out tests; t_in = 1, t_in > 40 and an odd t_in leave a0 = 0;
     0x81b30 .. 0x81b54  the same tests of t_out (t_out = 0 goes to 0x81b58);
     0x81b58, 0x81b5c    a0 := (t_in | t_out) <> 0.
   The proof runs to 0x81b10 once, then splits the model first: t_in (and, where the program tests it, t_out)
   in five classes (0; 1; above 40; odd in 2..40; even in 2..40). In each class the symbolic state gets what
   decides the tests: the register pinned to the literal (0 or 1), or the atom's range (with its low bit for the
   even class), so each class is one straight run to 0x81b60; the odd classes decide their one parity test by
   hand (jb_and1). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the prefix turns it back on, and so does this file. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- facts of the model and of the words, independent of the program ----------------------------------- *)
(* The five classes of a channel width as the program tests it. *)
Lemma jw_cls : forall v, 0 <= v ->
v = 0 \/ v = 1 \/ 40 < v \/ (2 <= v <= 40 /\ Z.even v = false) \/ (2 <= v <= 40 /\ Z.even v = true).
Proof.
intros v Hv.
destruct (Z.eq_dec v 0) as [H0 | H0]; [left; exact H0 | right].
destruct (Z.eq_dec v 1) as [H1 | H1]; [left; exact H1 | right].
destruct (Z_lt_le_dec 40 v) as [H2 | H2]; [left; exact H2 | right].
destruct (Z.even v) eqn:He; [right | left]; (split; [clear - Hv H0 H1 H2; lia | reflexivity]).
Qed.

(* 0x81b58, 0x81b5c: `or a0,a3,a4; snez a0,a0` is 1 when one of the two is not 0. *)
Lemma jw_snez : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> (x <> 0 \/ y <> 0) ->
zalu64 ALU_SLTU 0 (zalu64 ALU_OR x y) = 1.
Proof.
intros x y Hx Hy Hn.
assert (Lx : Z.log2 x < 64).
{ destruct (Z.eq_dec x 0) as [Hx0 | Hx0]; [rewrite Z.log2_nonpos by lia; lia|].
  apply Z.log2_lt_pow2; lia. }
assert (Ly : Z.log2 y < 64).
{ destruct (Z.eq_dec y 0) as [Hy0 | Hy0]; [rewrite Z.log2_nonpos by lia; lia|].
  apply Z.log2_lt_pow2; lia. }
assert (H0 : 0 <= Z.lor x y) by (apply Z.lor_nonneg; lia).
assert (H1 : Z.lor x y <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia).
assert (H2 : Z.lor x y < 2 ^ 64).
{ apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia. apply Z.max_lub_lt; assumption. }
unfold zalu64. cbn [zalu_raw].
rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia).
rewrite !(zcanon_id (Z.lor x y)) by (unfold M64; lia).
change (zcanon 0) with 0.
replace (0 <? Z.lor x y) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.

Lemma jw_snez_bv : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> (x <> 0 \/ y <> 0) ->
alu64 ALU_SLTU (Z_to_bv 64 0) (alu64 ALU_OR (Z_to_bv 64 x) (Z_to_bv 64 y)) = Z_to_bv 64 1.
Proof.
intros x y Hx Hy Hn. rewrite (zalu64_sound ALU_OR x y), (zalu64_sound ALU_SLTU 0).
rewrite (jw_snez x y Hx Hy Hn). reflexivity.
Qed.

(* The atom facts the classes give the engine: a range, and for the even class the low bit 0. *)
Lemma jw_af0 : forall E (n : nat) v lo hi, bv_unsigned (ew E n) = v -> lo <= v <= hi ->
afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi Hn Hv. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hn, Z.pow_0_r, Z.mod_1_r.
split; [exact Hv | split; [reflexivity | clear; lia]].
Qed.

Lemma jw_af1 : forall E (n : nat) v lo hi, bv_unsigned (ew E n) = v -> lo <= v <= hi -> Z.even v = true ->
afact_ok E n (mkAF lo hi 1).
Proof.
intros E n v lo hi Hn Hv He. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hn.
apply Z.even_spec in He. destruct He as [k Hk].
assert (Hm : v mod 2 ^ 1 = 0) by (rewrite Hk; change (2 ^ 1) with 2; rewrite Z.mul_comm; apply Z_mod_mult).
split; [exact Hv | split; [exact Hm | clear; lia]].
Qed.

(* A state whose regions are all read-only has no write window: the run keeps every byte, and its write
   obligation is empty. *)
Lemma jw_nwr : forall E (rs : smem) a, forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
~ in_wrange E rs a.
Proof.
intros E rs a Hb (r & Hin & Hr). rewrite forallb_forall in Hb. specialize (Hb r Hin).
apply Z.leb_le in Hb. lia.
Qed.

Lemma jw_feq : forall (H : word -> bool) E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') ->
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
mrestrict H m' = mrestrict H m.
Proof.
intros H E rs m m' HF Hb. apply functional_extensionality. intros x. apply HF. apply (jw_nwr E rs _ Hb).
Qed.

Lemma jw_awr : forall E rs STK sp0 FP bl0 blc ly own,
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof. intros E rs STK sp0 FP bl0 blc ly own Hb a Ha. exfalso. exact (jw_nwr E rs a Hb Ha). Qed.

(* After a run: the memory equals the memory the piece started with (EQ), carried run to run. *)
Ltac jw_mem0 EQ :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (jw_feq _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as EQ; cbn [ms_mem mkst] in EQ end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac jw_mem EQ :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let EQ2 := fresh "EQ" in
    pose proof (jw_feq _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as EQ2; cbn [ms_mem mkst] in EQ2;
    rewrite EQ in EQ2; clear EQ; rename EQ2 into EQ end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac jw_run RUNTOP HS HJ EQ stop :=
  paj_run_to_sh RUNTOP HS HJ stop; [apply jw_awr; vm_compute; reflexivity | jw_mem EQ].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation JKEEP := (jkeep B).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC0 := (jc0 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

(* Pinning a register to the literal it holds. *)
Lemma jw_pin : forall (W : world SEGS) E ss ms (r : bv 5) z,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> getr (ms_regs ms) r = Z_to_bv 64 z -> bv_eqb r 0 = false ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss))
(restrict (w_H W) ms).
Proof. intros W E ss ms r z HS Hr H0. exact (st_ok_pi_pin_reg' E ss _ r z HS Hr H0). Qed.

(* The cut at +0x13ec from a state the engine reached there: every register j_mk_jc0 keeps is still its own
   atom, and the memory is the one the piece started with. *)
Lemma jw_leaf : forall (g : ectx) pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 E extra,
frames S2 = [(4, pos)] ->
0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * MEV MT) ->
mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * MEV MT) ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
mf_id3 g pos mf W2 mem2 ->
getr regs2 12 = w64 SHADOW_OFF ->
getr regs2 18 = w64 (SlotModel.n_fam (e_pl g)) ->
getr regs2 27 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) ->
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) ->
env_agree 32 (Ereg regs2 extra) E ->
forall ss ms md3,
st_ok_pi SEGS VAL E ss (restrict (w_H W2) ms) ->
ss_resv ss = None -> ss_pc ss = 0x13ec ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
[2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 22%bv; 23%bv; 24%bv; 27%bv] = true ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 (ms_mem ms) md3 (4 * Z.of_nat (m_nrec g) + 7) ->
mrestrict (w_H W2) (ms_mem ms) = mrestrict (w_H W2) mem2 ->
getr (ms_regs ms) 10 = w64 (if SlotModel.n_wok (e_pl g) then 1 else 0) ->
m_fds md3 = m_fds md2 -> m_fs md3 = m_fs md2 ->
JC0 g pos mf nm tk dp W2 (mkCfg ms md3).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E extra Hfrs Hk MLE MOK HC HK Hmf3 R12 R18 R27 R22 HAE
ss ms md3 HS Hrv Hpc Hkeep HJ EQ R10 Efds Efs.
rewrite (st_ok_pi_restrict_mkst (w_H W2) E ss ms HS Hrv), Hpc.
exact (j_mk_jc0 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
ameta_inv arodata_okS g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) md3
Hfrs Hk MLE MOK HC HK Hmf3 R12 R18 R27 R22 HJ EQ
(regs_kept_of_st_ok_pi E ss (restrict (w_H W2) ms) regs2 extra _ HS HAE Hkeep) R10 Efds Efs).
Qed.

Local Ltac jw_end LEAF HS HJ EQ :=
  apply SRr_ret; apply (LEAF _ _ _ HS);
  [ reflexivity | reflexivity | vm_compute; reflexivity | exact HJ | exact EQ | idtac
  | rewrite ?j_wvb_fds; reflexivity | rewrite ?j_wvb_fs; reflexivity ].
(* a0 = 0 at the leaf. *)
Local Ltac jw_x10_0 HS L :=
  rewrite L; let Q := fresh "Q" in prreg HS (10%bv : bv 5) Q; rewrite Q; reflexivity.
(* a0 = (t_in | t_out) <> 0 at the leaf, with one of the two not 0. *)
Local Ltac jw_x10_1 HS L E38 E39 Hti64 Hto64 Ti To :=
  rewrite L; let Q := fresh "Q" in prreg HS (10%bv : bv 5) Q; rewrite Q; rewrite ?E38, ?E39;
  first [ reflexivity
        | apply jw_snez_bv; [clear - Hti64 Hto64; lia | clear - Hti64 Hto64; lia | clear - Ti To; lia] ].

Lemma j_wdec : j_wdec_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS.
Proof.
unfold j_wdec_stmt. intros LAWS HSTK g pos mf nm tk dp W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (Hid & Rs7 & Hmf3 & Hbl & R24 & R21 & R10 & R12 & R18 & R27 & R22 &
V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hbufs).
assert (HK : JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2)
by (unfold jkeep; exact (conj Hbl (conj Rs7 (conj R24 (conj R21 (conj V152 (conj V184 (conj V144 (conj V128
(conj V120 (conj V176 (conj V160 (conj V112 (conj Hid Hbufs)))))))))))))).
destruct (j1_entry B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
ameta_inv arodata_okS HSTK LAWS g pos mf nm tk dp 0x1388 ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC HK Hmf3)
as (_ & HS & _).
clear V152 V184 V144 V128 V120 V176 V160 V112 Hbufs Hid Rs7 Hbl R21.
set (E := j1_E regs2 (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_cap_tok (e_pl g))
(SlotModel.t_cap_disp (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold j1_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs2 (j1_extra (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g))
(SlotModel.t_cap_tok (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
(SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)))) E)
by (subst E; split; [intros n Hn; unfold j1_E; apply Eimg_low; clear - Hn; unfold A_TEXT; lia | reflexivity]).
destruct (j1_ew regs2 (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_cap_tok (e_pl g))
(SlotModel.t_cap_disp (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)))
as (Ew10 & _ & E38 & E39).
fold E in Ew10, E38, E39.
clearbody E.
assert (E10 : ew E 10 = w64 (SlotModel.n_r (e_pl g))) by (rewrite Ew10; exact R10).
clear Ew10.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_okw_bounds (e_pl g)) as (Hti & Hto).
assert (Hti64 : 0 <= SlotModel.t_in (e_pl g) < 2 ^ 64) by (clear - Hti; lia).
assert (Hto64 : 0 <= SlotModel.t_out (e_pl g) < 2 ^ 64) by (clear - Hto; lia).
assert (U38 : bv_unsigned (ew E 38) = SlotModel.t_in (e_pl g))
by (rewrite E38; apply unsigned_lit_small; exact Hti64).
assert (U39 : bv_unsigned (ew E 39) = SlotModel.t_out (e_pl g))
by (rewrite E39; apply unsigned_lit_small; exact Hto64).
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_r_cases (e_pl g)) as HNR.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (paj_branch (PI := PI)) as BR.
pose proof (jw_leaf g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E _ Hfrs Hk MLE MOK HC HK Hmf3 R12 R18 R27 R22 HAE)
as LEAF.
unfold cfg_at. change (w64 (BASE + 0x1388)) with (Z_to_bv 64 (BASE + 0x1388)).
(* ---- 0x81afc .. 0x81b04: a0 := n_r + 1, the abort when 1 <u a0 ---- *)
paj_run_to_sh RUNTOP HS HJ 0x13ec; [apply jw_awr; vm_compute; reflexivity | jw_mem0 EQ].
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite (jb_ltu_off E 10 1 1) in Hc by (clear; lia). rewrite E10 in Hc.
  destruct HNR as [Hr | Hr]; rewrite Hr in Hc; vm_compute in Hc; discriminate Hc. }
clear Hc.
(* ---- 0x81b08, 0x81b0c: a3 := t_in, a4 := t_out; stop at the first test 0x81b10 ---- *)
jw_run RUNTOP HS HJ EQ 5020.
destruct (jw_cls (SlotModel.t_in (e_pl g)) (proj1 Hti)) as [Ti | [Ti | [Ti | [[Ti Tpo] | [Ti Tpe]]]]].
- (* t_in = 0: a3 is the literal 0; the t_out tests decide *)
  prreg HS (13%bv : bv 5) Q13. rewrite E38, Ti in Q13.
  pose proof (jw_pin W2 E _ _ 13%bv 0 HS Q13 eq_refl) as HS2. clear HS Q13. rename HS2 into HS.
  destruct (jw_cls (SlotModel.t_out (e_pl g)) (proj1 Hto)) as [To | [To | [To | [[To Tqo] | [To Tqe]]]]].
  + (* t_out = 0: a0 := (0 | 0) <> 0 = 0 *)
    prreg HS (14%bv : bv 5) Q14. rewrite E39, To in Q14.
    pose proof (jw_pin W2 E _ _ 14%bv 0 HS Q14 eq_refl) as HS2. clear HS Q14. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
    jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_both0 (e_pl g) Ti To).
  + (* t_out = 1: 0x81b3c, a0 := 0 *)
    prreg HS (14%bv : bv 5) Q14. rewrite E39, To in Q14.
    pose proof (jw_pin W2 E _ _ 14%bv 1 HS Q14 eq_refl) as HS2. clear HS Q14. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
    jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_false_out (e_pl g) (or_introl To)).
  + (* t_out > 40: 0x81b4c, a0 = 0 *)
    assert (AF : afact_ok E 39%nat (mkAF 41 255 0))
    by (apply (jw_af0 E 39%nat (SlotModel.t_out (e_pl g))); [exact U39 | clear - To Hto; lia]).
    pose proof (st_ok_pi_add_fact E _ _ 39%nat _ HS AF) as HS2. clear HS AF. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
    jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_false_out (e_pl g) (or_intror (or_introl To))).
  + (* t_out odd in 2..40: 0x81b54 taken by hand, a0 = 0 *)
    assert (AF : afact_ok E 39%nat (mkAF 2 40 0))
    by (apply (jw_af0 E 39%nat (SlotModel.t_out (e_pl g))); [exact U39 | exact To]).
    pose proof (st_ok_pi_add_fact E _ _ 39%nat _ HS AF) as HS2. clear HS AF. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec.
    psrr_branch_pi RUNP BR HS.
    * clear Hc. jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
      jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_false_out (e_pl g)
        (or_intror (or_intror (conj To Tqo)))).
    * exfalso. rewrite (jb_and1 E 39%nat (SlotModel.t_out (e_pl g)) E39 Hto64), Tqo in Hc.
      cbn in Hc. discriminate Hc.
  + (* t_out even in 2..40: 0x81b58, a0 := (0 | t_out) <> 0 = 1 *)
    assert (AF : afact_ok E 39%nat (mkAF 2 40 1))
    by (apply (jw_af1 E 39%nat (SlotModel.t_out (e_pl g))); [exact U39 | exact To | exact Tqe]).
    pose proof (st_ok_pi_add_fact E _ _ 39%nat _ HS AF) as HS2. clear HS AF. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
    assert (NZ : SlotModel.t_in (e_pl g) <> 0 \/ SlotModel.t_out (e_pl g) <> 0) by (clear - To; lia).
    jw_x10_1 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_true (e_pl g) (or_introl Ti)
      (or_intror (conj To Tqe)) NZ) E38 E39 Hti64 Hto64 Ti To.
- (* t_in = 1: 0x81b18 taken, 0x81b3c, a0 := 0 *)
  prreg HS (13%bv : bv 5) Q13. rewrite E38, Ti in Q13.
  pose proof (jw_pin W2 E _ _ 13%bv 1 HS Q13 eq_refl) as HS2. clear HS Q13. rename HS2 into HS.
  jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
  jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_false_in (e_pl g) (or_introl Ti)).
- (* t_in > 40: 0x81b24 taken, a0 = 0 *)
  assert (AF : afact_ok E 38%nat (mkAF 41 255 0))
  by (apply (jw_af0 E 38%nat (SlotModel.t_in (e_pl g))); [exact U38 | clear - Ti Hti; lia]).
  pose proof (st_ok_pi_add_fact E _ _ 38%nat _ HS AF) as HS2. clear HS AF. rename HS2 into HS.
  jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
  jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_false_in (e_pl g) (or_intror (or_introl Ti))).
- (* t_in odd in 2..40: 0x81b2c taken by hand, a0 = 0 *)
  assert (AF : afact_ok E 38%nat (mkAF 2 40 0))
  by (apply (jw_af0 E 38%nat (SlotModel.t_in (e_pl g))); [exact U38 | exact Ti]).
  pose proof (st_ok_pi_add_fact E _ _ 38%nat _ HS AF) as HS2. clear HS AF. rename HS2 into HS.
  jw_run RUNTOP HS HJ EQ 0x13ec.
  psrr_branch_pi RUNP BR HS.
  + clear Hc. jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
    jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_false_in (e_pl g)
      (or_intror (or_intror (conj Ti Tpo)))).
  + exfalso. rewrite (jb_and1 E 38%nat (SlotModel.t_in (e_pl g)) E38 Hti64), Tpo in Hc.
    cbn in Hc. discriminate Hc.
- (* t_in even in 2..40: 0x81b2c falls through to the t_out tests *)
  assert (AF : afact_ok E 38%nat (mkAF 2 40 1))
  by (apply (jw_af1 E 38%nat (SlotModel.t_in (e_pl g))); [exact U38 | exact Ti | exact Tpe]).
  pose proof (st_ok_pi_add_fact E _ _ 38%nat _ HS AF) as HS2. clear HS AF. rename HS2 into HS.
  destruct (jw_cls (SlotModel.t_out (e_pl g)) (proj1 Hto)) as [To | [To | [To | [[To Tqo] | [To Tqe]]]]].
  + (* t_out = 0: 0x81b58, a0 := (t_in | 0) <> 0 = 1 *)
    prreg HS (14%bv : bv 5) Q14. rewrite E39, To in Q14.
    pose proof (jw_pin W2 E _ _ 14%bv 0 HS Q14 eq_refl) as HS2. clear HS Q14. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
    assert (NZ : SlotModel.t_in (e_pl g) <> 0 \/ SlotModel.t_out (e_pl g) <> 0) by (clear - Ti; lia).
    jw_x10_1 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_true (e_pl g) (or_intror (conj Ti Tpe))
      (or_introl To) NZ) E38 E39 Hti64 Hto64 Ti To.
  + (* t_out = 1: 0x81b3c, a0 := 0 *)
    prreg HS (14%bv : bv 5) Q14. rewrite E39, To in Q14.
    pose proof (jw_pin W2 E _ _ 14%bv 1 HS Q14 eq_refl) as HS2. clear HS Q14. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
    jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_false_out (e_pl g) (or_introl To)).
  + (* t_out > 40: 0x81b4c taken, a0 = 0 *)
    assert (AF : afact_ok E 39%nat (mkAF 41 255 0))
    by (apply (jw_af0 E 39%nat (SlotModel.t_out (e_pl g))); [exact U39 | clear - To Hto; lia]).
    pose proof (st_ok_pi_add_fact E _ _ 39%nat _ HS AF) as HS2. clear HS AF. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
    jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_false_out (e_pl g) (or_intror (or_introl To))).
  + (* t_out odd in 2..40: 0x81b54 taken by hand, a0 = 0 *)
    assert (AF : afact_ok E 39%nat (mkAF 2 40 0))
    by (apply (jw_af0 E 39%nat (SlotModel.t_out (e_pl g))); [exact U39 | exact To]).
    pose proof (st_ok_pi_add_fact E _ _ 39%nat _ HS AF) as HS2. clear HS AF. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec.
    psrr_branch_pi RUNP BR HS.
    * clear Hc. jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
      jw_x10_0 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_false_out (e_pl g)
        (or_intror (or_intror (conj To Tqo)))).
    * exfalso. rewrite (jb_and1 E 39%nat (SlotModel.t_out (e_pl g)) E39 Hto64), Tqo in Hc.
      cbn in Hc. discriminate Hc.
  + (* t_out even in 2..40: 0x81b58, a0 := (t_in | t_out) <> 0 = 1 *)
    assert (AF : afact_ok E 39%nat (mkAF 2 40 1))
    by (apply (jw_af1 E 39%nat (SlotModel.t_out (e_pl g))); [exact U39 | exact To | exact Tqe]).
    pose proof (st_ok_pi_add_fact E _ _ 39%nat _ HS AF) as HS2. clear HS AF. rename HS2 into HS.
    jw_run RUNTOP HS HJ EQ 0x13ec. jw_end LEAF HS HJ EQ.
    assert (NZ : SlotModel.t_in (e_pl g) <> 0 \/ SlotModel.t_out (e_pl g) <> 0) by (clear - Ti; lia).
    jw_x10_1 HS (LLVMFuzzerTestOneInput_seg_J_model.m2_wok_true (e_pl g) (or_intror (conj Ti Tpe))
      (or_intror (conj To Tqe)) NZ) E38 E39 Hti64 Hto64 Ti To.
Qed.

Check (j_wdec : j_wdec_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
asink_none ameta_inv arodata_okS).

End c.
End b.
End a.

About j_wdec.
Print Assumptions j_wdec.
