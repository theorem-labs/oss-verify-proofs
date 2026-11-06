(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACik.v:90-93, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* The shared part of segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), +0x1388 .. +0x1988
   (0x81afc .. 0x820fc, 384 slots): the width decision, the expected name and display, and the fits check.
   seg_J of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v: the symbolic start state of every one of its runs, the
   geometry of the entry's class-4 frame, the branch forms of its tests, the lemmas that move a memory fact to
   a later memory, the cuts the segment is split at, and one `Prop` per piece. Each piece is proved in its own
   file `LLVMFuzzerTestOneInput_seg_J_<part>.v`; `LLVMFuzzerTestOneInput_seg_J.v` chains them into seg_J.
   The copy loops are stated apart, in lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_loops_stmt.v. *)
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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this segment's address arithmetic (shadow_addr, the
   frame's 64-byte alignment) needs it, so this file turns it back on, as lib/A/Prog/LLVMFuzzerTestOneInput_D6.v
   does. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic state at 0x81afc (+0x1388). Region 0: the ten machine-frame words the first run reads, base
   s1 (atom 9), read-only. Region 1: the two frame variables the run zeroes the first byte of, base the frame
   address (atom 32), writable over [exp_nm, exp_dp + 1). Region 2: the frame's shadow, base s7 (atom 23),
   writable over the twelve cells of exp_nm and exp_dp (66..69 and 74..81). *)
Definition j1_mf : YP09.region := YP09.mkRegion (Some 9%nat) 64 192 64 64
[YP09.mkChunk 64 (CVal 8 (SOff 32 0));
YP09.mkChunk 120 (CVal 8 (SOff 37 0));
YP09.mkChunk 128 (CVal 8 (SOff 36 0));
YP09.mkChunk 136 (CVal 8 (SOff 32 355));
YP09.mkChunk 144 (CVal 8 (SOff 35 0));
YP09.mkChunk 152 (CVal 8 (SOff 33 0));
YP09.mkChunk 160 (CVal 8 (SOff 39 0));
YP09.mkChunk 168 (CVal 8 (SOff 40 0));
YP09.mkChunk 176 (CVal 8 (SOff 38 0));
YP09.mkChunk 184 (CVal 8 (SOff 34 0))].
Definition j1_sf : YP09.region := YP09.mkRegion (Some 32%nat) 528 593 528 593 [].
Definition j1_sh : YP09.region := YP09.mkRegion (Some 23%nat) 66 82 66 82 [].
Definition ss_j1 (pc : Z) : sstate := mkSS pc sr_atoms [j1_mf; j1_sf; j1_sh] None (mkFacts [] [] []).
(* The width decision writes nothing, so its state has the machine-frame words alone, read-only. *)
Definition ss_j0 (pc : Z) : sstate := mkSS pc sr_atoms [j1_mf] None (mkFacts [] [] []).

(* The branch forms of the width decision (0x81b04 .. 0x81b68): a register against a literal, and the
   parity test `andi r,1`. *)
Lemma jb_eq_lit : forall E (n : nat) v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit k)) = (v =? k).
Proof.
intros E n v k H Hv Hk. rewrite YI04.branch_eq_U, (U_atom E n v H Hv), U_SLit.
rewrite (zcanon_id k) by (unfold M64; lia). reflexivity.
Qed.
Lemma jb_ne_lit : forall E (n : nat) v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit k)) = negb (v =? k).
Proof.
intros E n v k H Hv Hk. rewrite YI04.branch_ne_U, (U_atom E n v H Hv), U_SLit.
rewrite (zcanon_id k) by (unfold M64; lia). reflexivity.
Qed.
Lemma jb_ltu_lit : forall E (n : nat) v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SLit k)) (sv_denot E (SOff n 0)) = (k <? v).
Proof.
intros E n v k H Hv Hk. rewrite YI04.branch_ltu_U, (U_atom E n v H Hv), U_SLit.
rewrite (zcanon_id k) by (unfold M64; lia). reflexivity.
Qed.
Lemma jland_mod : forall v, 0 <= v -> Z.land v 1 = v mod 2.
Proof.
intros v Hv. replace 1 with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia.
change (2 ^ 1) with 2. reflexivity.
Qed.
Lemma jb_ltu_off : forall E (n : nat) c k, 0 <= k < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SLit k)) (sv_denot E (SOff n c)) = (k <? zcanon (bv_unsigned (ew E n) + c)).
Proof.
intros E n c k Hk. rewrite YI04.branch_ltu_U, U_SOff, U_SLit.
rewrite (zcanon_id k) by (unfold M64; lia). reflexivity.
Qed.
Lemma jland1v : forall v, 0 <= v -> (v mod 2 =? 0) = Z.even v.
Proof.
intros v Hv. destruct (Z.even v) eqn:Ev.
- apply Z.even_spec in Ev as [q ->]. rewrite Z.mul_comm, Z_mod_mult. reflexivity.
- assert (Hodd : Z.odd v = true) by (rewrite <- Z.negb_even, Ev; reflexivity).
  apply Z.odd_spec in Hodd as [q ->]. rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full.
  reflexivity.
Qed.
Lemma jb_and1 : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1))) (sv_denot E (SLit 0)) = negb (Z.even v).
Proof.
intros E n v H Hv. rewrite YI04.branch_ne_U, U_SAlu, (U_atom E n v H Hv), ?U_SLit.
rewrite ?(zcanon_id 0) by (unfold M64; lia). rewrite ?(zcanon_id 1) by (unfold M64; lia).
cbn [zalu_raw]. rewrite (jland_mod v ltac:(lia)).
rewrite (zcanon_id (v mod 2)) by (pose proof (Z.mod_pos_bound v 2 ltac:(lia)); unfold M64; lia).
f_equal. apply jland1v. lia.
Qed.

Lemma j_wvb_fds : forall (md : Model) mat, m_fds (with_vm_backing (m_vm_lazy md) mat md) = m_fds md.
Proof. intros md mat. destruct md as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity. Qed.
Lemma j_wvb_fs : forall (md : Model) mat, m_fs (with_vm_backing (m_vm_lazy md) mat md) = m_fs md.
Proof. intros md mat. destruct md as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity. Qed.

(* Moving a fact of one memory to another that agrees with it on the bytes the fact speaks of. *)
Section mv.
Variable segs : list Segment.
Lemma j_garr8_moved : forall H H' (m m' : word -> option byte) a l,
(forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma j_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
(forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma j_block_shadow_moved : forall (rd rd' : reader) Bs a n,
(forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof.
intros rd rd' Bs a n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi).
Qed.
End mv.

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
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JKEEP := (jkeep B).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

(* The environment of the first run: the registers, then the ten values the machine-frame words hold. *)
Definition j1_extra (SF nm dp cn ct cd ti to : Z) : list word :=
map (Z_to_bv 64) [SF; nm; dp; cn; ct; cd; ti; to; SHADOW_OFF].
Definition j1_E (regs : bvmap 5 word) (SF nm dp cn ct cd ti to : Z) : env :=
Eimg (Ereg regs (j1_extra SF nm dp cn ct cd ti to)).
Lemma j1_ew : forall regs SF nm dp cn ct cd ti to,
ew (j1_E regs SF nm dp cn ct cd ti to) 10 = getr regs 10 /\
ew (j1_E regs SF nm dp cn ct cd ti to) 24 = getr regs 24 /\
ew (j1_E regs SF nm dp cn ct cd ti to) 38 = Z_to_bv 64 ti /\
ew (j1_E regs SF nm dp cn ct cd ti to) 39 = Z_to_bv 64 to.
Proof.
intros. unfold j1_E.
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 24 24%bv eq_refl)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)|].
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 7).
Qed.

(* The geometry of the entry's own class-4 frame, from the journal: where it is, that it is 64-aligned,
   and that it does not meet its own shadow cells (the frame is app memory, the shadow is the band). *)
Lemma j_geo : forall (g : ectx) pos k ly2 S2 (W2 : world SEGS) mem2 md2,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 k ->
frames S2 = [(4, pos)] ->
frame_addr ly2 4 pos = SFa g pos /\
4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ SFa g pos mod 64 = 0 /\
0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling /\
(SFa g pos + 1024 <= shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= SFa g pos).
Proof.
intros g pos k ly2 S2 W2 mem2 md2 HJ Hfrs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
split; [exact EFa|]. split; [exact HSF0|]. split; [exact HSF1|]. split; [exact HSF64|].
split; [clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia|].
split; [clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia|].
clear - Esh HSF0 HSF1 HSFapp C1.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
destruct HSFapp as (_ & [Hlo | [Hhi1 Hhi2]]); [left | right]; lia.
Qed.

(* What the first run needs of the state at 0x81afc, as a predicate of the raw pieces: inv_I_end's own
   content, read off the acut. It also gives the three atom values the later runs need. *)
Lemma j1_entry : forall (g : ectx) pos mf nm tk dp pc ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
frames S2 = [(4, pos)] ->
ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
arodata_okS g pos mf ly2 S2 W2 regs2 mem2 md2 ->
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SFa g pos + V_id + 3) ->
st_ok_pi SEGS VAL (j1_E regs2 (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g))
(SlotModel.t_cap_tok (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
(SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g))) (ss_j1 pc)
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + pc)) mem2 (seg_rom SEGS))) /\
st_ok_pi SEGS VAL (j1_E regs2 (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g))
(SlotModel.t_cap_tok (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
(SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g))) (ss_j0 pc)
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + pc)) mem2 (seg_rom SEGS))) /\
bv_unsigned (ew (j1_E regs2 (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g))
(SlotModel.t_cap_tok (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
(SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g))) 9) = mf /\
bv_unsigned (ew (j1_E regs2 (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g))
(SlotModel.t_cap_tok (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
(SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g))) 23) = shadow_addr (SFa g pos) /\
bv_unsigned (ew (j1_E regs2 (SFa g pos) nm dp (SlotModel.t_cap_name (e_pl g))
(SlotModel.t_cap_tok (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
(SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g))) 32) = SFa g pos.
Proof.
intros g pos mf nm tk dp pc ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC HK V136.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & Hly2 & Hsecs & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
set (sp0 := e_sp0 g) in *.
destruct (j_geo g pos _ ly2 S2 W2 mem2 md2 HJ Hfrs) as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1u & Hsfsh).
set (SF := SFa g pos) in *.
set (sh := shadow_addr SF) in *.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling) by (split; [exact Hsh0 | exact Hsh1u]).
assert (Hti : 0 <= SlotModel.t_in (e_pl g) < 256) by exact (SlotModel.inb_range _ _).
assert (Hto : 0 <= SlotModel.t_out (e_pl g) < 256) by exact (SlotModel.inb_range _ _).
assert (Hcn : 0 <= SlotModel.t_cap_name (e_pl g) < 40)
by (unfold SlotModel.t_cap_name; apply Z.mod_pos_bound; lia).
assert (Hct : 0 <= SlotModel.t_cap_tok (e_pl g) < 40)
by (unfold SlotModel.t_cap_tok; apply Z.mod_pos_bound; lia).
assert (Hcd : 0 <= SlotModel.t_cap_disp (e_pl g) < 64)
by (unfold SlotModel.t_cap_disp; apply Z.mod_pos_bound; lia).
destruct Hbl as [Hperm Hhs].
assert (Hnm : 4096 <= nm /\ 0 <= Z.max (SlotModel.t_cap_name (e_pl g)) 1).
{ inversion Hhs as [|h0 hs0 Hh0 Hrest]; subst. cbn [fst snd] in Hh0. exact Hh0. }
assert (Hdp : 4096 <= dp).
{ inversion Hhs as [|h0 hs0 Hh0 Hrest]; subst.
  inversion Hrest as [|h1 hs1 Hh1 Hrest2]; subst.
  inversion Hrest2 as [|h2 hs2 Hh2 Hrest3]; subst. cbn [fst snd] in Hh2. exact (proj1 Hh2). }
assert (Hnmb : nm < 2 ^ 64 /\ dp < 2 ^ 64).
{ pose proof (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1) HAR2
    ltac:(apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity)) as (_ & Hn1 & Hn2 & _).
  pose proof (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) HAR2
    ltac:(apply (Permutation_in _ (Permutation_sym Hperm)); right; right; left; reflexivity)) as (_ & Hd1 & Hd2 & _).
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(lia)) as [Hr1 _].
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(lia)) as [Hr2 _].
  clear - Hn1 Hn2 Hd1 Hd2 Hr1 Hr2 C1. lia. }
rewrite restrict_mkst_fx.
set (E := j1_E regs2 SF nm dp (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_cap_tok (e_pl g))
(SlotModel.t_cap_disp (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (j1_extra SF nm dp
(SlotModel.t_cap_name (e_pl g)) (SlotModel.t_cap_tok (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
(SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)))) n)
by (intros n Hn; subst E; unfold j1_E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = getr regs2 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 9 9%bv eq_refl)).
assert (E23 : ew E 23 = getr regs2 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ 23 23%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nm) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 dp) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (SlotModel.t_cap_name (e_pl g))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (SlotModel.t_cap_tok (e_pl g))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (SlotModel.t_cap_disp (e_pl g))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (SlotModel.t_in (e_pl g))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (SlotModel.t_out (e_pl g))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 8)).
assert (U9 : bv_unsigned (ew E 9) = mf)
by (rewrite E9, Rs1; apply unsigned_lit_small; clear - Hmf0 H47 Hmfb Hshi C1; lia).
assert (U23 : bv_unsigned (ew E 23) = sh)
by (rewrite E23, Rs7; apply unsigned_lit_small; clear - Hsh1 C1; lia).
assert (U32 : bv_unsigned (ew E 32) = SF) by (rewrite E32; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (HMF : YP09.region_ok SEGS E (mrestrict (w_H W2) mem2) j1_mf).
{ unfold j1_mf, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val SEGS E _ mf 64 8 (SOff 32 0) SF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - HSF0 HSF1 C1; lia | lia | exact V64].
* apply (chunk_ok_val SEGS E _ mf 120 8 (SOff 37 0) (SlotModel.t_cap_disp (e_pl g)));
[cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hcd; lia | lia | exact V120].
* apply (chunk_ok_val SEGS E _ mf 128 8 (SOff 36 0) (SlotModel.t_cap_tok (e_pl g)));
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hct; lia | lia | exact V128].
* apply (chunk_ok_val SEGS E _ mf 136 8 (SOff 32 355) (SF + V_id + 3));
[cbn [sv_denot]; rewrite U32; unfold V_id; f_equal; clear; lia
| clear - HSF0 HSF1 C1; unfold V_id; lia | lia | exact V136].
* apply (chunk_ok_val SEGS E _ mf 144 8 (SOff 35 0) (SlotModel.t_cap_name (e_pl g)));
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hcn; lia | lia | exact V144].
* apply (chunk_ok_val SEGS E _ mf 152 8 (SOff 33 0) nm);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hnm Hnmb; lia | lia | exact V152].
* apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 39 0) (SlotModel.t_out (e_pl g)));
[cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hto; lia | lia | exact V160].
* apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 40 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| unfold SHADOW_OFF; lia | lia | exact V168].
* apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 38 0) (SlotModel.t_in (e_pl g)));
[cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hti; lia | lia | exact V176].
* apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 34 0) dp);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hdp Hnmb; lia | lia | exact V184].
}
assert (HSF : YP09.region_ok SEGS E (mrestrict (w_H W2) mem2) j1_sf).
{ unfold j1_sf, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 32%nat SF E32 ltac:(clear - HSF0 HSF1 C1; lia)).
split; [clear - HSF0; lia|]. split; [clear - HSF0 HSF1 C1; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS).
apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
[(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) (SF + o) HJ ltac:(
right; right; right; exists 4, pos; split; [left; reflexivity|]; left;
unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; clear - Ho; lia))). }
assert (HSH : YP09.region_ok SEGS E (mrestrict (w_H W2) mem2) j1_sh).
{ unfold j1_sh, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 23%nat sh ltac:(rewrite E23, Rs7; reflexivity) ltac:(clear - Hsh1 C1; lia)).
split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS).
apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
[(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) (sh + o) HJ ltac:(
right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; fold sh; clear - Ho; lia))). }
assert (HRG : regs_ok E sr_atoms regs2) by (subst E; unfold j1_E; apply regs_ok_Eimg_Ereg).
assert (HFA : facts_ok E (mkFacts [] [] [])).
{ unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [exact I | split; exact I]. }
split; [|split; [|split; [exact U9 | split; [exact U23 | exact U32]]]].
- unfold ss_j1. apply pa_entry_st_ok_full.
+ exact HRG.
+ vm_compute. reflexivity.
+ repeat apply Forall_cons; try apply Forall_nil; assumption.
+ apply pairwise_disjoint_of_extents. unfold j1_mf, j1_sf, j1_sh, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 32%nat SF E32 ltac:(clear - HSF0 HSF1 C1; lia)),
(VB 23%nat sh ltac:(rewrite E23, Rs7; reflexivity) ltac:(clear - Hsh1 C1; lia)).
cbn [base_val]. rewrite U9.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hmf0 Hsh1 Hsfsh HSF0 HSF1 C1 HSF64. clear. intros. repeat split; lia.
+ exact HFA.
- unfold ss_j0. apply pa_entry_st_ok_full.
+ exact HRG.
+ vm_compute. reflexivity.
+ repeat apply Forall_cons; try apply Forall_nil; assumption.
+ apply pairwise_disjoint_of_extents. unfold j1_mf, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
+ exact HFA.
Qed.

#[local] Notation INVI := (inv_I_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation INVJ := (inv_J_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

(* +0x13ec (0x81b60): the width case is decided and its answer is in a0; nothing has been written yet. *)
Definition jc0 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x13ec)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
mf_id3 g pos mf W2 mem2 /\
getr regs2 10 = w64 (if SlotModel.n_wok (e_pl g) then 1 else 0) /\
getr regs2 12 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SlotModel.n_fam (e_pl g)) /\
getr regs2 27 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g))).

(* The run keeps every byte: the read-only state ss_j0 has no write window. *)
Lemma j_keep_all : forall (W : world SEGS) E rs m m',
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
(forall a, ~ in_wrange E rs a) ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W E rs m m' HF Hn a Ha. apply aview_eq_of. apply HF. apply Hn.
Qed.

(* The cut at +0x13ec, from the state the segment started in: the width tests write nothing, so the memory
   is the one the cut came in with (EQR) and every register but a0 is kept. *)
Lemma j_mk_jc0 : forall (g : ectx) pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs3 mem3 md3,
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
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) ->
mrestrict (w_H W2) mem3 = mrestrict (w_H W2) mem2 ->
(forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 21%bv; 22%bv; 23%bv; 24%bv; 27%bv] ->
getr regs3 r = getr regs2 r) ->
getr regs3 10 = w64 (if SlotModel.n_wok (e_pl g) then 1 else 0) ->
m_fds md3 = m_fds md2 -> m_fs md3 = m_fs md2 ->
jc0 g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x13ec) regs3 mem3 md3).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
Hfrs Hk MLE MOK HC HK Hmf3 R12 R18 R27 R22 HJ3 EQR RK R10 Efds Efs.
assert (EQV : aview SEGS (w_H W2) mem3 = aview SEGS (w_H W2) mem2)
by (unfold aview; rewrite EQR; reflexivity).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
unfold mf_id3 in Hmf3. unfold id_at, sh_zero, sh_blk, bytes_at8 in Hid.
unfold bytes_at8 in Hinb, Hbufs.
rewrite <- EQR in V16, V64, V192, V168, Vra, Vs0, V24, V32, V40, V48, V56, V64b, V72, V80, V88, V96,
V104, Vflag, Hinb, V152, V184, V144, V128, V120, V176, V160, V112, Hmf3, Hid, Hbufs.
rewrite <- EQV in Hid.
unfold jc0, acut.
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon.
  split; [rewrite (RK 2%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rsp|].
  split; [rewrite (RK 9%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rs1|].
  split; [rewrite (RK 8%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (RK 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rgp|].
  split; [rewrite (RK 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rtp|].
  split; [exact V16|]. split; [exact V64|]. split; [exact V192|]. split; [exact V168|].
  split; [exact Vra|]. split; [exact Vs0|]. split; [exact V24|]. split; [exact V32|].
  split; [exact V40|]. split; [exact V48|]. split; [exact V56|]. split; [exact V64b|].
  split; [exact V72|]. split; [exact V80|]. split; [exact V88|]. split; [exact V96|].
  split; [exact V104|]. split; [exact Vflag|]. split; [exact HPRE|].
  split; [rewrite Efds; exact Hfds|]. split; [rewrite Efs; exact Hfs|]. exact Hinb. }
split.
{ unfold jkeep.
  split; [exact Hbl|].
  split; [unfold sh_reg; rewrite (RK 23%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact Rs7|].
  split; [rewrite (RK 24%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R24|].
  split; [rewrite (RK 21%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R21|].
  split; [exact V152|]. split; [exact V184|]. split; [exact V144|]. split; [exact V128|].
  split; [exact V120|]. split; [exact V176|]. split; [exact V160|]. split; [exact V112|].
  split; [exact Hid|]. exact Hbufs. }
split; [exact Hmf3|].
split; [exact R10|].
split; [rewrite (RK 12%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R12|].
split; [rewrite (RK 18%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R18|].
split; [rewrite (RK 27%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R27|].
rewrite (RK 22%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R22.
Qed.



(* ---- the image facts the segment reads, at any state of its journal ------------------------------------- *)
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Lemma j_img : forall (g : ectx) pos k ly2 S2 (W2 : world SEGS) mem2 md2,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 k -> EPRE g -> llvmf_img B G W2 mem2.
Proof.
intros g pos k ly2 S2 W2 mem2 md2 HJ HPRE.
apply HIMG. apply (IdentBase.arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
(e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2 k HJ).
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROD & _). apply HRO. exact HROD.
Qed.

(* ---- the cuts inside segment J --------------------------------------------------------------------------- *)
(* The stem the expected name starts from: `id.model_name` when the record named one, else the family's string
   in the image. The cut carries its bytes and its shadow, so the copy loop needs no image hypothesis. *)
(* Where the stem is, in a form that crosses a call. The frame case needs nothing (the call keeps the
   entry's own frame and its shadow); the image case is stated for every state of this walk's journal, since
   the low shadow band is kept by no clause of tcj_kept and must be re-derived from the registered globals. *)
Definition jstem_any (g : ectx) (pos st : Z) : Prop :=
st = SFa g pos + V_id + 3 \/
(forall ly S (W : world SEGS) mem md k,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly S W mem md k ->
bytes_at8 W mem st (SlotModel.n_stem (e_pl g) ++ [RcIdentModel.zb 0]) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF st
(Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1)).
Definition jstem (g : ectx) (pos : Z) (W2 : world SEGS) (mem2 : word -> option byte) (st : Z) : Prop :=
jstem_any g pos st /\
bytes_at8 W2 mem2 st (SlotModel.n_stem (e_pl g) ++ [RcIdentModel.zb 0]) /\
(st + Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1 <= SFa g pos + V_nm \/
SFa g pos + V_nm + N_nm <= st) /\
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF st
(Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1) /\
amem_range st (Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1) /\ 0 < st.

(* +0x1440 (0x81bb4): the widths are good; the shadow of exp_nm and exp_dp is cleared (0x81b78..0x81ba4) and
   both hold the empty string (0x81ba8, 0x81bac). x25 = &exp_nm, x26 = &exp_dp (0x81b70, 0x81b74). *)
Definition jc1 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1440)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\ mf_id3 g pos mf W2 mem2 /\
getr regs2 12 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SlotModel.n_fam (e_pl g)) /\
getr regs2 27 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
val_mem SEGS (rd W2 mem2) (SFa g pos + V_nm) 1 0 /\
val_mem SEGS (rd W2 mem2) (SFa g pos + V_dp) 1 0).

(* +0x14c8 (0x81c3c): the stem is chosen and its address is in mf+136 (0x81c38, or kept from 0x80af8 when the
   record named a model). *)
Definition jc2 (g : ectx) (pos mf nm tk dp st : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x14c8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 12 = w64 SHADOW_OFF /\
getr regs2 22 = w64 (SlotModel.t_cap_disp (e_pl g)) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
val_mem SEGS (rd W2 mem2) (SFa g pos + V_nm) 1 0 /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 st /\ jstem g pos W2 mem2 st).

(* +0x1524 (0x81c98): `w4` (SF+688) holds the four width digits and their NUL, its shadow is cleared
   (0x81c44) and both put_dec counters are zero (0x81c48, 0x81c4c; put_dec left mf+208 = 4, then the NUL
   store at 0x81c94 used it). x6 = the shadow base (0x81c78), x18 = &w4 (0x81c40). *)
Definition jc3 (g : ectx) (pos mf nm tk dp st : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1524)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\ getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
sh_zero W2 mem2 (SFa g pos + V_w4) N_w4 /\
bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
val_mem SEGS (rd W2 mem2) (SFa g pos + V_nm) 1 0 /\
val_mem SEGS (rd W2 mem2) (mf + 136) 8 st /\ jstem g pos W2 mem2 st).

(* +0x15c4 (0x81d38): the stem is copied into exp_nm and x27 holds its length (0x81d2c, 0x81d34). *)
Definition jc4 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x15c4)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\ getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
getr regs2 27 = w64 (Z.of_nat (length (SlotModel.n_stem (e_pl g)))) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
sh_zero W2 mem2 (SFa g pos + V_w4) N_w4 /\
bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_stem (e_pl g))).

(* +0x16b8 (0x81e2c): exp_nm holds the whole expected name and x27 its length; x22 = the complement of
   &exp_nm (0x81d38). *)
Definition jc5 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x16b8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\ getr regs2 22 = w64 (Z.lnot (SFa g pos + V_nm)) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\ getr regs2 26 = w64 (SFa g pos + V_dp) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g))).

(* +0x1748 (0x81ebc): exp_nm has its NUL (0x81e3c) and exp_dp holds a copy of it; x12 = its length. *)
Definition jc6 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1748)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (j_dp1 (e_pl g)) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
getr regs2 12 = w64 (j_L1 (e_pl g)) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0])).

(* +0x17e8 (0x81f5c): the literal " (" and the first channel width are in exp_dp, mf+200 holds its length and
   x6 is the shadow base again (0x81f58). *)
Definition jc7 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x17e8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (j_dp2 (e_pl g)) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 (j_L2 (e_pl g)) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0])).

(* +0x188c (0x82000): the literal " in / " and the second width are in exp_dp (0x81ffc reloaded x6). *)
Definition jc8 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x188c)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (j_dp3 (e_pl g)) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 (j_L3 (e_pl g)) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0])).

(* +0x1910 (0x82084): the whole display is in exp_dp but its NUL; x13 = its length, x12 = its last address,
   x11 = 5 (the literal just copied). *)
Definition jc9 (g : ectx) (pos mf nm tk dp : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1910)
(fun ly2 S2 W2 regs2 mem2 md2 =>
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (SlotModel.n_EXP_DP (e_pl g)) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
getr regs2 11 = w64 5 /\
getr regs2 12 = w64 (SFa g pos + V_dp + j_L3 (e_pl g)) /\
getr regs2 13 = w64 (j_L3 (e_pl g)) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0])).

(* ---- one Prop per piece ----------------------------------------------------------------------------------
   Each piece is `<the hypotheses it uses> -> forall g pos mf nm tk dp ..., <its start cut> -> SRr ... <its end>`.
   A lane proves `Lemma j_<part> : j_<part>_stmt.` in its own file and this file does not move. *)

(* +0x1388 .. +0x13ec (0x81afc .. 0x81b60): the eight tests of the two channel widths (0x81b04 .. 0x81b54).
   Nothing is written; a0 ends holding SlotModel.n_wok as 1 or 0. *)
Definition j_wdec_stmt : Prop :=
AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
forall (g : ectx) pos mf nm tk dp W2 c2, INVI g pos mf nm tk dp W2 c2 ->
SRr SEGS W2 c2 (jc0 g pos mf nm tk dp).

(* +0x13ec .. +0x1440: the two frame variables are unpoisoned (twelve shadow stores) and emptied; with bad
   widths the branch at 0x81bb0 goes straight to +0x1988, which is inv_J_end's own slot. *)
Definition j_width_stmt : Prop :=
AR_laws SEGS B ->
forall (g : ectx) pos mf nm tk dp W2 c2, jc0 g pos mf nm tk dp W2 c2 ->
SRr SEGS W2 c2 (fun W3 c3 =>
(SlotModel.n_wok (e_pl g) = true /\ jc1 g pos mf nm tk dp W3 c3) \/
(SlotModel.n_wok (e_pl g) = false /\ INVJ g pos mf nm tk dp W3 c3)).

(* +0x1440 .. +0x14c8: the stem. With a model name whose first byte is not NUL the code keeps `id.model_name`
   (mf+136 from 0x80af8); otherwise it reads switch.table.LLVMFuzzerTestOneInput (object 7) at the family, or
   "REAC" (object 8) for a family outside 1..3, after the shadow test of the table entry at 0x81be8. *)
Definition j_stem_stmt : Prop :=
AR_laws SEGS B -> PALib B -> globs_marked SEGS B G -> img_shadow_vis SEGS B ->
In (VAL (A_OBJ 7), 24) G -> In (VAL (A_OBJ 8), 5) G ->
forall (g : ectx) pos mf nm tk dp W2 c2, jc1 g pos mf nm tk dp W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (fun W3 c3 => exists st, jc2 g pos mf nm tk dp st W3 c3).

(* +0x14c8 .. +0x1524: `w4` is unpoisoned, both counters cleared, and put_dec writes the two widths into it
   (0x81c60, 0x81c74) with its NUL at 0x81c94. UBSan traps refuted: 0x81c84, 0x81c8c. *)
Definition j_w4_stmt : Prop :=
AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK -> EV_LLVMF <= EV_LIB -> put_dec.tput_dec_spec B -> identb_prog_sig_ok (PI := PI) -> ameter_laws MT ->
(forall s s' : astate, mo_le MT s s' 0) ->
forall (g : ectx) pos mf nm tk dp st W2 c2, jc2 g pos mf nm tk dp st W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (jc3 g pos mf nm tk dp st).

(* +0x1524 .. +0x15c4: the stem copy. The loop itself is j_stemcpy_stmt; this piece is its entry (the shadow
   test of the stem's first byte at 0x81ca4 and the empty-stem path 0x81d34) and its exit. *)
Definition j_stemcpy_glue_stmt : Prop :=
AR_laws SEGS B -> j_stemcpy_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS ->
forall (g : ectx) pos mf nm tk dp st W2 c2, jc3 g pos mf nm tk dp st W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (jc4 g pos mf nm tk dp).

(* +0x15c4 .. +0x16b8: the tail test. When the stem already ends in the four digits (bcmp at 0x81d68) the name
   is the stem; otherwise a dash is appended (0x81d94) and the digits copied (j_w4cpy_stmt). UBSan traps
   refuted: 0x81d4c, 0x81d50, 0x81d58, 0x81d78, 0x81d7c, 0x81dbc, 0x81dc4, 0x81e30, 0x81e34. *)
Definition j_w4tail_stmt : Prop :=
AR_laws SEGS B -> abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp) ->
STK_LLVMF <= LLVMF_STK ->
j_w4cpy_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS ->
forall (g : ectx) pos mf nm tk dp W2 c2, jc4 g pos mf nm tk dp W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (jc5 g pos mf nm tk dp).

(* +0x16b8 .. +0x1748: the NUL of exp_nm (0x81e3c) and the copy of exp_nm into exp_dp (j_dpcpy_stmt). *)
Definition j_dpcpy_glue_stmt : Prop :=
AR_laws SEGS B -> j_dpcpy_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS ->
forall (g : ectx) pos mf nm tk dp W2 c2, jc5 g pos mf nm tk dp W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (jc6 g pos mf nm tk dp).

(* +0x1748 .. +0x17e8: the literal " (" (j_lit1_stmt) and put_dec of the first width (0x81f54). *)
Definition j_lit1_glue_stmt : Prop :=
AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK -> EV_LLVMF <= EV_LIB -> put_dec.tput_dec_spec B -> identb_prog_sig_ok (PI := PI) -> ameter_laws MT ->
(forall s s' : astate, mo_le MT s s' 0) ->
globs_marked SEGS B G -> In (VAL (A_OBJ 9), 3) G ->
j_lit1_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS ->
forall (g : ectx) pos mf nm tk dp W2 c2, jc6 g pos mf nm tk dp W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (jc7 g pos mf nm tk dp).

(* +0x17e8 .. +0x188c: the literal " in / " (j_lit2_stmt) and put_dec of the second width (0x81ff8). *)
Definition j_lit2_glue_stmt : Prop :=
AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK -> EV_LLVMF <= EV_LIB -> put_dec.tput_dec_spec B -> identb_prog_sig_ok (PI := PI) -> ameter_laws MT ->
(forall s s' : astate, mo_le MT s s' 0) ->
globs_marked SEGS B G -> In (VAL (A_OBJ 10), 7) G ->
j_lit2_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS ->
forall (g : ectx) pos mf nm tk dp W2 c2, jc7 g pos mf nm tk dp W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (jc8 g pos mf nm tk dp).

(* +0x188c .. +0x1910: the literal " out)" (j_lit3_stmt). *)
Definition j_lit3_glue_stmt : Prop :=
AR_laws SEGS B -> globs_marked SEGS B G -> In (VAL (A_OBJ 11), 6) G ->
j_lit3_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS ->
forall (g : ectx) pos mf nm tk dp W2 c2, jc8 g pos mf nm tk dp W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (jc9 g pos mf nm tk dp).

(* +0x1910 .. +0x1988: the NUL of exp_dp (0x82098), the three capacity tests with the memchr of the first dash
   (0x820b0), and the re-poisoning of `w4` (0x820f8). The aborts at 0x820d4 and 0x820f0 are refuted by
   SlotModel.n_fits and reac_box_name's result. UBSan traps refuted: 0x8208c, 0x82090. *)
Definition j_fits_stmt : Prop :=
AR_laws SEGS B -> amemchr_realizes SEGS B (SIGMA IB___interceptor_trampoline_memchr) ->
STK_LLVMF <= LLVMF_STK ->
forall (g : ectx) pos mf nm tk dp W2 c2, jc9 g pos mf nm tk dp W2 c2 ->
SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (INVJ g pos mf nm tk dp).

End c.
End b.
End a.
