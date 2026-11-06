(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its module names and numbers changed; 479 of its 554 lines of code are new or changed and 1068 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x81974 .. 0x81e60): the expected name and
   display of the harness (fuzz_identity.c:429-478).
     0x81974..0x81980  r := reac_box_name's result; r + 1 <u 2 (r is 0 or -1)
     0x81984..0x819dc  wok := width_ok(in) && width_ok(out) && !(in == 0 && out == 0)
     0x819e0..0x819e8  !wok && r != -1 aborts
     0x819ec..0x81a28  exp_nm, exp_dp: their shadow is made usable, exp_nm[0] = exp_dp[0] = 0
     0x81a2c           !wok: to 0x81e68, then 0x81e68 bnez s11 to 0x82090 (K's end; r = -1)
     0x81a30..0x81a74  the stem: id.model_name when has_model_name and its first byte is not 0, else stem_of(fam)
     0x81a78..0x81ab0  w4 := DEC(in,2) DEC(out,2) by two put_dec calls
     0x81ab4..0x81b5c  w4[4] = 0; the stem copy loop into exp_nm
     0x81b60..0x81c18  unless exp_nm ends in w4 (bcmp at 0x81b70): '-' and w4 are appended
     0x81c1c..0x81ca0  exp_nm[ln] = 0; the copy loop of exp_nm into exp_dp
     0x81ca4..0x81e14  " (", put_dec(in,1), " in / ", put_dec(out,1), " out)", exp_dp[ld] = 0
     0x81e18..0x81e5c  fits := ln < cap_name && lt < cap_tok && ld < cap_disp (memchr of '-' at 0x81e2c);
                       fits && r != 0 aborts, !fits && r != -1 aborts
  Every abort branch is decided by the plain model (SlotModel.n_r: r = 0 exactly when wok and fits), every
  shadow test by the shadow the segment itself writes, id's shadow, or the registered globals' shadow.
  This file proves jL0 (0x81974..0x819e0), jB (0x819e0..0x81a30, and the bad-width exit at 0x82090) and seg_J_holds;
  pieces C, D, E, F and the two copy loops are in their own files over the shared cut _Jcut.v (its header lists
  them), and seg_J_of_pieces composes them. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_Jcut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_JC LLVMFuzzerTestOneInput_JD LLVMFuzzerTestOneInput_JEall LLVMFuzzerTestOneInput_JF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the address arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic state at 0x81974: the machine frame's three words the tree reads (mf+80 = SF, mf+128 = SF+355,
   mf+176 = the shadow base), read-only; atoms 32 = SF, 33 = SHADOW_OFF, 24 = in, 26 = out. *)
Definition j0_mf : YP09.region := YP09.mkRegion (Some 9%nat) 80 184 184 184
  [YP09.mkChunk 80 (CVal 8 (SOff 32 0)); YP09.mkChunk 128 (CVal 8 (SOff 32 355));
   YP09.mkChunk 176 (CVal 8 (SOff 33 0))].
Definition j0_facts : facts := mkFacts [(24%nat, mkAF 0 255 0); (26%nat, mkAF 0 255 0)] [] [].
Definition ss_j0 : sstate := mkSS 0x1268 sr_atoms [j0_mf] None j0_facts.
(* Piece B writes exp_nm[0] and exp_dp[0] (base x12 = SF) and the shadow cells 66 .. 81 of the frame (base
   x19 = shadow_addr SF); a0 (wok) and s11 (r) are pinned to their values. *)
Definition jB_sh : YP09.region := YP09.mkRegion (Some 19%nat) 66 82 66 82 [].
Definition jB_fr : YP09.region := YP09.mkRegion (Some 12%nat) 528 593 528 593 [].
Definition ss_jB0 : sstate := mkSS 0x12d4 sr_atoms [jB_sh; jB_fr] None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
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
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation HBLOCKS := (hblocks B).

(* ---- what the segment takes, each as the contract's Section states it (LLVMFuzzerTestOneInput.v) ----------- *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis G_SW : In (VAL (A_OBJ 7), 24) G.
Hypothesis G_IN : In (VAL (A_OBJ 9), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 10), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IS___interceptor_trampoline_memchr).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.

(* ---- the shared layer of segment J (LLVMFuzzerTestOneInput_Jcut.v), at this Section's variables ------------ *)
#[local] Notation jcut := (LLVMFuzzerTestOneInput_Jcut.jcut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
  LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation jc := (LLVMFuzzerTestOneInput_Jcut.jc B).
#[local] Notation jcut_mk := (LLVMFuzzerTestOneInput_Jcut.jcut_mk B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0).
#[local] Notation jlay_of := (LLVMFuzzerTestOneInput_Jcut.jlay_of B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK
  EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).
#[local] Notation jacut_mono := (LLVMFuzzerTestOneInput_Jcut.jacut_mono B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY
  LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation jcut_close := (LLVMFuzzerTestOneInput_Jcut.jcut_close B MT XM_LIB XN_LIB RLO RHI RA_LLVMF
  A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS MTL HMT0 AJ_NIL_IO).

(* ---- 0x81974 .. 0x819e0: r, and the widths ---------------------------------------------------------------- *)
Definition Pe0 (g : ectx) (pos : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model) : Prop :=
  getr regs2 10 = w64 (if SlotModel.n_wok (e_pl g) then 1 else 0) /\
  getr regs2 27 = w64 (SlotModel.n_r (e_pl g)) /\
  getr regs2 12 = w64 (SFa g pos) /\ getr regs2 13 = w64 SHADOW_OFF /\ getr regs2 14 = w64 (SFa g pos + 355) /\
  getr regs2 23 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
  getr regs2 25 = w64 (SlotModel.n_fam (e_pl g)).

(* What every state of the segment at a boundary carries about the state the segment started from. *)
Definition jstart (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) /\
  frames S2 = [(4, pos)] /\ 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF /\
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) /\
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) /\
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 /\ jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
  getr regs2 10 = w64 (SlotModel.n_r (e_pl g)) /\
  getr regs2 23 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
  getr regs2 25 = w64 (SlotModel.n_fam (e_pl g)).

(* The end of the widths' decision tree: every leaf is at 0x819e0 with its own a0, the memory as it was. *)
Lemma jL0_close : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E ss ms md extra,
  jstart g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W2) ms) -> ss_pc ss = 0x12d4 -> ss_resv ss = None ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 (ms_mem ms) md (4 * Z.of_nat (m_nrec g) + 7) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a) ->
  env_agree 32 (Ereg regs2 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 8; 9; 3; 4; 19; 20; 21; 22; 23; 25]%bv = true ->
  sr_get (ss_regs ss) 27 = SOff 10 0 -> sr_get (ss_regs ss) 12 = SOff 32 0 ->
  sr_get (ss_regs ss) 13 = SOff 33 0 -> sr_get (ss_regs ss) 14 = SOff 32 355 ->
  ew E 32 = w64 (SFa g pos) -> ew E 33 = w64 SHADOW_OFF ->
  sv_denot E (sr_get (ss_regs ss) 10) = w64 (if SlotModel.n_wok (e_pl g) then 1 else 0) ->
  SRr SEGS W2 (mkCfg ms md) (jcut g pos mf nm tk dp (BASE + 0x12d4) (Pe0 g pos)).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E ss ms md extra HST
  HS Hpc Hrv HJ3 KEEP HAE Hkept Q27 Q12 Q13 Q14 E32 E33 Q10.
destruct HST as (HJ2 & Hfr2 & HK & MLE & MOK & HC & HJC & R10 & R23 & R25).
pose proof (st_ok_pi_restrict_mkst (w_H W2) E ss ms HS Hrv) as Hms. rewrite Hpc in Hms.
pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W2) ms) regs2 extra _ HS HAE Hkept) as RK.
cbn [ms_regs restrict] in RK.
assert (RG : forall r : bv 5, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r))
  by (intros r; exact (st_ok_pi_restrict_reg (w_H W2) E ss ms r HS)).
destruct HJC as (Hlay & HJCr). pose proof Hlay as (_ & _ & _ & HSF0 & HSF1 & _).
pose proof asan_consts as (C1 & _).
assert (EA : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs2 extra) n) by (intros n Hn; exact (proj1 HAE n Hn)).
apply SRr_ret. rewrite Hms.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as [D1 D2].
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [D3 D4].
apply (jcut_mk g pos mf nm tk dp (BASE + 0x12d4) (Pe0 g pos) ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md
  HJ2 Hfr2 HK MLE MOK HC (conj Hlay HJCr) HJ3 Hfr2 (Permutation_refl _)).
- intros a Ha _. exact (KEEP a Ha).
- intros r Hr. apply RK. cbn in Hr |- *. tauto.
- intros fd. rewrite D3, D1. reflexivity.
- rewrite D4, D2. reflexivity.
- unfold Pe0.
  assert (A10 : ew E 10 = getr regs2 10) by (rewrite EA by lia; exact (ew_Ereg_nat regs2 _ 10 10%bv eq_refl)).
  assert (P10 : getr (ms_regs ms) 10 = w64 (if SlotModel.n_wok (e_pl g) then 1 else 0)) by (rewrite RG; exact Q10).
  assert (P27 : getr (ms_regs ms) 27 = w64 (SlotModel.n_r (e_pl g))).
  { rewrite RG, Q27. cbn [sv_denot]. rewrite A10, R10, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (P12 : getr (ms_regs ms) 12 = w64 (SFa g pos)).
  { rewrite RG, Q12. cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (P13 : getr (ms_regs ms) 13 = w64 SHADOW_OFF).
  { rewrite RG, Q13. cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (P14 : getr (ms_regs ms) 14 = w64 (SFa g pos + 355)).
  { rewrite RG, Q14. cbn [sv_denot]. rewrite E32. unfold w64.
    rewrite unsigned_lit_small by (clear - HSF0 HSF1 C1; lia). reflexivity. }
  assert (P23 : getr (ms_regs ms) 23 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))))
    by (rewrite RK by (cbn; tauto); exact R23).
  assert (P25 : getr (ms_regs ms) 25 = w64 (SlotModel.n_fam (e_pl g)))
    by (rewrite RK by (cbn; tauto); exact R25).
  exact (conj P10 (conj P27 (conj P12 (conj P13 (conj P14 (conj P23 P25)))))).
Qed.
(* A leaf of the tree: the state at 0x819e0 is a jcut, with a0 still to be computed. *)
Ltac jclose0 HST HSx HJx HAEx E32x E33x :=
  eapply (jL0_close _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HST HSx eq_refl eq_refl HJx);
  [ intros aK HaK; jkeepgoal
  | exact HAEx
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | vm_compute; reflexivity | vm_compute; reflexivity
  | exact E32x | exact E33x
  | lazymatch goal with |- sv_denot ?Ex ?e = ?rhs =>
      let e' := eval vm_compute in e in change (sv_denot Ex e' = rhs) end ].

#[local] Notation INV_I := (inv_I_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
(* The writable windows of a run whose regions are all read-only: none. *)
Ltac jawr_ro :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]); apply awr_ok_nil.
(* One step of the width tree: run to the next branch of the segment and split there. *)
Ltac jstep1 HSx HJx :=
  paj_run_to_sh RUNTOP HSx HJx 0x12d4; [ jawr_ro | psrr_branch_pi RUNP BR HSx ].

(* 0x81974 .. 0x819e0: r is 0 or -1, and a0 is 1 exactly when the two widths are good. The tree has twelve
   leaves at 0x819e0 and one abort (0x81980, r + 1 >=u 2), which the model refutes. *)
Lemma jL0 : forall g pos mf nm tk dp W2 c2,
  INV_I g pos mf nm tk dp W2 c2 ->
  SRr SEGS W2 c2 (jcut g pos mf nm tk dp (BASE + 0x12d4) (Pe0 g pos)).
Proof.
intros g pos mf nm tk dp W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & HK & MLE & MOK & HC & HP).
destruct HP as (Hid & Hid3 & Hhb & R10 & R25 & R23 & R24 & R26 & R20 & R21 & R22 &
  V184 & V152 & V144 & V160 & V168 & V136 & Hjb).
assert (HJC : jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2).
{ refine (conj (jlay_of g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC Hhb) _).
  exact (conj Hid (conj Hid3 (conj Hhb (conj R20 (conj R21 (conj R22 (conj V184 (conj V152
    (conj V144 (conj V160 (conj V168 (conj V136 Hjb)))))))))))). }
assert (HST : jstart g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2) by
  (exact (conj HJ (conj Hfrs (conj HK (conj MLE (conj MOK (conj HC (conj HJC (conj R10 (conj R23 R25)))))))))).
pose proof HC as HC0.
destruct HC0 as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfss & Hinb).
pose proof (proj1 HJC) as Hlay.
destruct Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof asan_consts as (C1 & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (JModel.tin_range (e_pl g)) as Rin. pose proof (JModel.tout_range (e_pl g)) as Rout.
pose proof (JModel.n_r_cases (e_pl g)) as Hrc.
pose proof (JModel.n_r_zero (e_pl g)) as Hr0w.
set (SF := SFa g pos) in *.
(* the environment: atom 32 = the side frame, atom 33 = the shadow base *)
remember (Eimg (Ereg regs2 [w64 SF; w64 SHADOW_OFF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 SF)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = w64 SHADOW_OFF)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HAE : env_agree 32 (Ereg regs2 [w64 SF; w64 SHADOW_OFF]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (E24 : ew E 24 = w64 (SlotModel.t_in (e_pl g))) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (Hid3' : val_mem SEGS (rd W2 mem2) (mf + 128) 8 (SFa g pos + 355)).
{ unfold mf_id3, V_id in Hid3. replace (SFa g pos + 352 + 3) with (SFa g pos + 355) in Hid3 by lia.
  exact Hid3. }
assert (E26 : ew E 26 = w64 (SlotModel.t_out (e_pl g))) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E10 : ew E 10 = w64 (SlotModel.n_r (e_pl g))) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. unfold ASTACK in *. lia. }
(* the U-value of every operand the tree branches on *)
assert (UIN : U E (SOff 24 0) = SlotModel.t_in (e_pl g))
  by (rewrite (jU_off E 24 _ 0 E24), Z.add_0_r; apply Z.mod_small; unfold M64; lia).
assert (UOUT : U E (SOff 26 0) = SlotModel.t_out (e_pl g))
  by (rewrite (jU_off E 26 _ 0 E26), Z.add_0_r; apply Z.mod_small; unfold M64; lia).
assert (UR1 : U E (SOff 10 1) = (SlotModel.n_r (e_pl g) + 1) mod M64) by (apply (jU_off E 10 _ 1 E10)).
assert (UAI : U E (SAlu ALU_AND (SOff 24 0) (SLit 1)) = (if Z.odd (SlotModel.t_in (e_pl g)) then 1 else 0))
  by (apply (jU_and1 E 24 _ E24); unfold M64; lia).
assert (UAO : U E (SAlu ALU_AND (SOff 26 0) (SLit 1)) = (if Z.odd (SlotModel.t_out (e_pl g)) then 1 else 0))
  by (apply (jU_and1 E 26 _ E26); unfold M64; lia).
assert (USL : U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SOff 24 0) (SOff 26 0)))
    = (if Z.eqb (SlotModel.t_in (e_pl g)) 0 && Z.eqb (SlotModel.t_out (e_pl g)) 0 then 0 else 1))
  by (exact (jU_sltu_or E 24 26 _ _ E24 E26 Rin Rout)).
(* the symbolic state at 0x81974 *)
assert (HS : st_ok_pi SEGS VAL E ss_j0
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1268)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_j0. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold j0_mf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [unfold ASTACK in *; lia|]. split; [unfold ASTACK in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    + apply (chunk_ok_val SEGS E _ mf 80 8 (SOff 32 0) SF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | lia | lia | exact V80].
    + apply (chunk_ok_val SEGS E _ mf 128 8 (SOff 32 355) (SFa g pos + 355));
      [cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
      | lia | lia | exact Hid3'].
    + apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 33 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; lia | lia | exact V176].
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok, j0_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E24. unfold w64.
      rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E26. unfold w64.
      rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia]. }
unfold cfg_at. change (w64 (BASE + 0x1268)) with (Z_to_bv 64 (BASE + 0x1268)).
(* the tree: run to the next branch and split, until every leaf is at 0x819e0 (nine deep at most) *)
all: try jstep1 HS HJ. all: try jstep1 HS HJ. all: try jstep1 HS HJ. all: try jstep1 HS HJ.
all: try jstep1 HS HJ. all: try jstep1 HS HJ. all: try jstep1 HS HJ. all: try jstep1 HS HJ.
all: try jstep1 HS HJ. all: try jstep1 HS HJ.
(* each leaf is at its last branch with the branch's condition; one more run reaches 0x819e0 *)
all: try (paj_run_to_sh RUNTOP HS HJ 0x12d4; [ jawr_ro | ]).
all: jbr1 UIN UOUT UAI UAO USL UR1.
(* every leaf: the widths decide n_wok, and a0 is 1 exactly then *)
- (* 0x81980: r + 1 >=u 2 is the abort path; r is 0 or -1 *)
  exfalso.
  match goal with H : context[(SlotModel.n_r (e_pl g) + 1) mod _] |- _ =>
    destruct Hrc as [Hr|Hr]; rewrite Hr in H; clear - H; lia end.
- (* in = 0, out = 0 *)
  assert (Hw : SlotModel.n_wok (e_pl g) = false) by (apply JModel.wok_false_00; jlia).
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, USL, Hw.
  replace (SlotModel.t_in (e_pl g) =? 0) with true by (symmetry; apply Z.eqb_eq; jlia).
  replace (SlotModel.t_out (e_pl g) =? 0) with true by (symmetry; apply Z.eqb_eq; jlia).
  reflexivity.
- (* in = 0, out > 40 *)
  assert (Hw : SlotModel.n_wok (e_pl g) = false) by (apply JModel.wok_false_out, JModel.okw_big; jlia).
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, jU_lit, Hw. reflexivity.
- (* in = 0, out odd *)
  jodd_t (SlotModel.t_out (e_pl g)) Ho.
  assert (Hw : SlotModel.n_wok (e_pl g) = false) by (apply JModel.wok_false_out, JModel.okw_odd; exact Ho).
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, jU_lit, Hw. reflexivity.
- (* in = 0, out even in [2, 40] *)
  jeven_t (SlotModel.t_out (e_pl g)) Ho.
  assert (Hw : SlotModel.n_wok (e_pl g) = true).
  { apply JModel.wok_true; [replace (SlotModel.t_in (e_pl g)) with 0 by jlia; exact JModel.okw_zero
    | apply JModel.okw_even_ok; [jlia | exact Ho] | right; jlia]. }
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, USL, Hw.
  replace (SlotModel.t_out (e_pl g) =? 0) with false by (symmetry; apply Z.eqb_neq; jlia).
  rewrite andb_false_r. reflexivity.
- (* in = 0, out = 1 *)
  assert (Hw : SlotModel.n_wok (e_pl g) = false).
  { apply JModel.wok_false_out. replace (SlotModel.t_out (e_pl g)) with 1 by jlia. exact JModel.okw_one. }
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, jU_lit, Hw. reflexivity.
- (* in = 1 *)
  assert (Hw : SlotModel.n_wok (e_pl g) = false).
  { apply JModel.wok_false_in. replace (SlotModel.t_in (e_pl g)) with 1 by jlia. exact JModel.okw_one. }
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, jU_lit, Hw. reflexivity.
- (* in > 40 *)
  assert (Hw : SlotModel.n_wok (e_pl g) = false) by (apply JModel.wok_false_in, JModel.okw_big; jlia).
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, jU_lit, Hw. reflexivity.
- (* in odd *)
  jodd_t (SlotModel.t_in (e_pl g)) Ho.
  assert (Hw : SlotModel.n_wok (e_pl g) = false) by (apply JModel.wok_false_in, JModel.okw_odd; exact Ho).
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, jU_lit, Hw. reflexivity.
- (* in even in [2, 40], out = 0 *)
  jeven_t (SlotModel.t_in (e_pl g)) Ho.
  assert (Hw : SlotModel.n_wok (e_pl g) = true).
  { apply JModel.wok_true; [apply JModel.okw_even_ok; [jlia | exact Ho]
    | replace (SlotModel.t_out (e_pl g)) with 0 by jlia; exact JModel.okw_zero | left; jlia]. }
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, USL, Hw.
  replace (SlotModel.t_in (e_pl g) =? 0) with false by (symmetry; apply Z.eqb_neq; jlia).
  reflexivity.
- (* in even in [2, 40], out > 40 *)
  assert (Hw : SlotModel.n_wok (e_pl g) = false) by (apply JModel.wok_false_out, JModel.okw_big; jlia).
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, jU_lit, Hw. reflexivity.
- (* in even in [2, 40], out odd *)
  jodd_t (SlotModel.t_out (e_pl g)) Ho.
  assert (Hw : SlotModel.n_wok (e_pl g) = false) by (apply JModel.wok_false_out, JModel.okw_odd; exact Ho).
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, jU_lit, Hw. reflexivity.
- (* in even in [2, 40], out even in [2, 40] *)
  jeven_t (SlotModel.t_in (e_pl g)) Hoi. jeven_t (SlotModel.t_out (e_pl g)) Hoo.
  assert (Hw : SlotModel.n_wok (e_pl g) = true).
  { apply JModel.wok_true; [apply JModel.okw_even_ok; [jlia | exact Hoi]
    | apply JModel.okw_even_ok; [jlia | exact Hoo] | left; jlia]. }
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, USL, Hw.
  replace (SlotModel.t_in (e_pl g) =? 0) with false by (symmetry; apply Z.eqb_neq; jlia).
  reflexivity.
- (* in even in [2, 40], out = 1 *)
  assert (Hw : SlotModel.n_wok (e_pl g) = false).
  { apply JModel.wok_false_out. replace (SlotModel.t_out (e_pl g)) with 1 by jlia. exact JModel.okw_one. }
  jclose0 HST HS HJ HAE E32 E33. rewrite jsv_U, jU_lit, Hw. reflexivity.
Qed.
(* ---- 0x819e0 .. 0x81a30 / 0x82090 (piece B): exp_nm, exp_dp, their shadow, and the wok test ---------------- *)
#[local] Notation INV_K := (inv_K_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
(* A shadow cell a run wrote 0 to. *)
Lemma jsh0 : forall E (m : word -> option byte) H n b cs lo hi wlo whi od,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 (SLit 0))) cs -> aview SEGS H m (b + od) = Some 0.
Proof.
intros E m H n b cs lo hi wlo whi od HR Hb Hin. apply aview_of_val_mem1; [|lia].
exact (field_of_region E (mrestrict H m) n b cs lo hi wlo whi od 1%N (SLit 0) 0 HR Hb Hin eq_refl
  ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Ltac jin := cbn [In]; repeat (first [left; reflexivity | right]).
(* The i-th region of a symbolic state, as region_ok of the memory (seg_A's get_region). *)
Ltac jget_region HS i HR :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?ms =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with Some ?rg =>
      pose proof (st_ok_region_nth E (abs_ss val ss) ms i rg HS ltac:(vm_compute; reflexivity)) as HR end end.
(* The two windows of B are the frame's own bytes and shadow cells. *)
Ltac jawr_B U19 U12 EFa posv :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_gen;
    [ reflexivity | first [exact U19 | exact U12]
    | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 4, posv;
      split; [left; reflexivity | unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 4) with 1024;
              change (1024 / 8) with 128; first [left; clear - Ha; lia | right; clear - Ha; lia]]
    | ] ].
Ltac jwin_B U19 U12 SF :=
  let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb wl wh aa Hin Hr;
  lazymatch type of Hin with In _ (windows ?rs) =>
    let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin end;
  repeat (destruct Hin as [Hin | Hin];
          [ injection Hin as <- <- <-; cbn [base_val] in Hr; rewrite ?U19, ?U12 in Hr; unfold WJ; fold SF;
            right; right; first [left; clear - Hr; lia | right; clear - Hr; lia] | ]);
  destruct Hin.

Lemma jB : forall g pos mf nm tk dp W2 c2,
  jcut g pos mf nm tk dp (BASE + 0x12d4) (Pe0 g pos) W2 c2 ->
  SRr SEGS W2 c2 (fun W3 c3 => jcut g pos mf nm tk dp (BASE + 0x1324) (Pj1 g pos) W3 c3 \/
    (SlotModel.n_wok (e_pl g) = false /\ INV_K g pos mf nm tk dp W3 c3)).
Proof.
intros g pos mf nm tk dp W2 c2 Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & HK & MLE & MOK & HC & HJC & HP).
destruct HP as (R10 & R27 & R12 & R13 & R14 & R23 & R25).
pose proof HC as HC0.
destruct HC0 as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & _).
pose proof (proj1 HJC) as Hlay.
destruct Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR2 & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR2 Hin4) as (HFal & _ & HFpres & HFSpres).
change (fs_frame_bytes 4) with 1024 in *. rewrite EFa in HFpres, HFSpres.
set (SF := SFa g pos) in *.
assert (HSHr : SHADOW_OFF + 4096 / 8 <= shadow_addr SF /\ shadow_addr SF + 128 <= 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF in *. clear - HSF0 HSF1 C1. split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia | ].
  assert (SF / 8 <= 2 ^ 60) by (apply Z.div_le_upper_bound; lia). lia. }
(* the environment: the registers' own atoms *)
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (HAE : env_agree 32 (Ereg regs2 []) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U12 : bv_unsigned (ew E 12) = SF)
  by (rewrite (EE 12%nat 12%bv eq_refl), R12; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
assert (U19 : bv_unsigned (ew E 19) = shadow_addr SF)
  by (rewrite (EE 19%nat 19%bv eq_refl), Rs3; apply unsigned_lit_small; clear - HSHr; unfold SHADOW_OFF in *; lia).
assert (HS0 : st_ok_pi SEGS VAL E ss_jB0
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x12d4)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_jB0. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold jB_sh, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U19.
      split; [clear - HSHr; unfold SHADOW_OFF in *; lia|]. split; [clear - HSHr; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (HFSpres o ltac:(change (1024 / 8) with 128; clear - Ho; lia))).
    + unfold jB_fr, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U12.
      split; [clear - HSF0; lia|]. split; [clear - HSF1 C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (SF + o) ltac:(clear - Ho; lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, extent_of_region, jB_sh, jB_fr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi fst snd base_val]. rewrite U19, U12.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HSFapp.
    unfold shadow_addr, SHADOW_OFF in *.
    clear - HSFapp HSF0 HSF1 C1. repeat split; try exact I.
    destruct HSFapp as [_ [HL | [HH1 HH2]]].
    + right. assert (SF / 8 <= 268431360) by (apply Z.div_le_upper_bound; lia). lia.
    + left. assert (2 ^ 41 <= SF / 8) by (apply Z.div_le_lower_bound; lia). lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
pose proof (JModel.n_r_cases (e_pl g)) as Hrc.
pose proof (JModel.n_r_zero (e_pl g)) as Hr0w.
assert (HSF528 : forall i, shadow_of_addr SHADOW_OFF (SF + 528) + i = shadow_addr SF + (66 + i)).
{ intros i. unfold shadow_of_addr, shadow_addr. replace (SF + 528) with (SF + 66 * 8) by lia.
  rewrite Z.div_add by lia. lia. }
assert (HSF592 : forall i, shadow_of_addr SHADOW_OFF (SF + 592) + i = shadow_addr SF + (74 + i)).
{ intros i. unfold shadow_of_addr, shadow_addr. replace (SF + 592) with (SF + 74 * 8) by lia.
  rewrite Z.div_add by lia. lia. }
unfold cfg_at. change (w64 (BASE + 0x12d4)) with (Z_to_bv 64 (BASE + 0x12d4)).
pose proof HJ as HJ0.
destruct (SlotModel.n_wok (e_pl g)) eqn:Hw; cbn [negb] in R10.
- (* good widths: a0 = 1; r is 0 or -1, B runs to 0x81a30 the same way *)
  assert (Hr27 : exists rv, getr regs2 27 = Z_to_bv 64 rv /\ SlotModel.n_r (e_pl g) = rv /\ (rv = 0 \/ rv = -1))
    by (destruct Hrc as [Hr|Hr]; [exists 0 | exists (-1)]; rewrite Hr in R27; refine (conj R27 (conj Hr _)); auto).
  destruct Hr27 as (rv & Q27 & Hrv & Hrv01).
  pose proof (st_ok_pi_pin_reg' E _ _ 10%bv 1 HS0 R10 eq_refl) as HS1.
  pose proof (st_ok_pi_pin_reg' E _ _ 27%bv rv HS1 Q27 eq_refl) as HS. clear HS0 HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_jB0] in HS.
  destruct Hrv01 as [-> | ->].
  all: paj_run_to_sh RUNTOP HS HJ 0x1324; [ jawr_B U19 U12 EFa pos | ].
  all: apply SRr_mono with (Q := jcut g pos mf nm tk dp (BASE + 0x1324) (Pj1 g pos)); [| intros W3 c3 _ H3; left; exact H3].
  all: jget_region HS 0%nat RSH; cbn [ms_mem restrict] in RSH.
  all: lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
         pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (WJ g pos mf) HFr ltac:(jwin_B U19 U12 SF)) as KEEP end.
  all: eapply (jcut_close g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E _ _ _ [] 0x1324 (Pj1 g pos)
         HJ0 Hfrs HK MLE MOK HC HJC HS eq_refl eq_refl); [exact HJ | exact KEEP | exact HAE | vm_compute; reflexivity |].
  all: pose proof (regs_kept_of_st_ok_pi E _ _ regs2 [] [12; 13; 14; 23; 25]%bv HS HAE ltac:(vm_compute; reflexivity)) as RK.
  all: cbn [ms_regs restrict] in RK.
  all: prreg HS (27%bv : bv 5) Q27'; prreg HS (26%bv : bv 5) Q26; prreg HS (24%bv : bv 5) Q24.
  all: lazymatch type of RSH with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
         assert (SH : forall od, In (YP09.mkChunk od (CVal 1 (SLit 0))) cs ->
                   aview SEGS (w_H W2) (ms_mem ms) (shadow_addr SF + od) = Some 0)
           by (intros od Hin; exact (jsh0 E (ms_mem ms) (w_H W2) 19 _ _ _ _ _ _ od RSH U19 Hin)) end.
  all: unfold Pj1; refine (conj Hw _).
  all: split; [rewrite Hrv; exact Q27'|].
  all: split; [rewrite Q26; cbn [sv_denot]; rewrite U12; reflexivity|].
  all: split; [rewrite Q24; cbn [sv_denot]; rewrite U12; reflexivity|].
  all: split; [rewrite RK by (cbn; tauto); exact R12|].
  all: split; [rewrite RK by (cbn; tauto); exact R13|].
  all: split; [rewrite RK by (cbn; tauto); rewrite R14; unfold V_id; f_equal; lia|].
  all: split; [rewrite RK by (cbn; tauto); exact R23|].
  all: split; [rewrite RK by (cbn; tauto); exact R25|].
  all: unfold sh_zero, zero_shadow, V_nm, N_nm, V_dp, N_dp.
  all: split; intros i Hi; [change (32 / 8) with 4 in Hi; rewrite HSF528 | change (64 / 8) with 8 in Hi; rewrite HSF592].
  all: assert (Hi8 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ (4 <= i < 8)) by lia.
  all: destruct Hi8 as [-> | [-> | [-> | [-> | Hi8]]]]; [apply SH; jin .. |].
  all: assert (Hi4 : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  all: destruct Hi4 as [-> | [-> | [-> | ->]]]; (first [exfalso; clear - Hi; lia | apply SH; jin]).
- (* bad widths: a0 = 0 and r = -1 (r = 0 needs good widths); the run goes 0x81a2c -> 0x81e68 -> 0x82090 *)
  destruct Hrc as [Hr | Hr]; [exfalso; destruct (Hr0w Hr) as [Hc _]; discriminate Hc|].
  rewrite Hr in R27.
  pose proof (st_ok_pi_pin_reg' E _ _ 10%bv 0 HS0 R10 eq_refl) as HS1.
  pose proof (st_ok_pi_pin_reg' E _ _ 27%bv (-1) HS1 R27 eq_refl) as HS. clear HS0 HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_jB0] in HS.
  paj_run_to_sh RUNTOP HS HJ 0x1984; [ jawr_B U19 U12 EFa pos | ].
  apply SRr_mono with (Q := jcut g pos mf nm tk dp (BASE + 0x1984) (fun _ _ _ _ _ _ => True)).
  2: { intros W3 c3 _ H3. right. split; [first [reflexivity | exact Hw]|].
       revert H3. unfold LLVMFuzzerTestOneInput_Jcut.jcut, inv_K_end. apply jacut_mono.
       intros ly3 S3 W4 regs3 mem3 md3 _ (HJC3 & _).
       destruct HJC3 as (_ & _ & _ & Hhb3 & _ & R21' & R22' & V184' & _).
       exact (conj Hhb3 (conj R22' (conj R21' V184'))). }
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (WJ g pos mf) HFr ltac:(jwin_B U19 U12 SF)) as KEEP end.
  eapply (jcut_close g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E _ _ _ [] 0x1984 (fun _ _ _ _ _ _ => True)
    HJ0 Hfrs HK MLE MOK HC HJC HS eq_refl eq_refl); [exact HJ | exact KEEP | exact HAE | vm_compute; reflexivity | exact I].
Qed.

(* ---- seg_J from its pieces ------------------------------------------------------------------------------------ *)
(* jL0 and jB here; C, D, E, F by their own lanes (_JC.v .. _JF.v). With bad widths the run leaves B at 0x82090
   (inv_K_end); with good widths it goes through C, D, E and F to 0x81e60 (inv_J_end). *)
Lemma seg_J_of_pieces :
  j_C_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS ->
  j_D_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS ->
  j_E_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS ->
  j_F_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS ->
  seg_J B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros JC JD JE JF g pos mf nm tk dp W2 c2 HI.
apply (SRr_bind SEGS W2 c2 _ _ (jL0 g pos mf nm tk dp W2 c2 HI)). intros W3 c3 _ H3.
apply (SRr_bind SEGS W3 c3 _ _ (jB g pos mf nm tk dp W3 c3 H3)). intros W4 c4 _ [H4 | H4].
- apply (SRr_bind SEGS W4 c4 _ _ (JC g pos mf nm tk dp W4 c4 H4)). intros W5 c5 _ H5.
  apply (SRr_bind SEGS W5 c5 _ _ (JD g pos mf nm tk dp W5 c5 H5)). intros W6 c6 _ H6.
  apply (SRr_bind SEGS W6 c6 _ _ (JE g pos mf nm tk dp W6 c6 H6)). intros W7 c7 _ H7.
  apply (SRr_mono SEGS W7 c7 _ _ (JF g pos mf nm tk dp W7 c7 H7)). intros W8 c8 _ H8. left. exact H8.
- apply SRr_ret. right. exact H4.
Qed.

(* C (_JC.v), D (_JD.v) and F (_JF.v) put in: only E is left. *)
Lemma seg_J_of_E :
  j_E_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS ->
  seg_J B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros JE. apply seg_J_of_pieces.
- exact (j_C B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
    ameta_inv arodata_okS HSTK HEV LAWS MTL HMT0 HRO G GM G_SW HIMG PSIG HPD AJ_NIL_IO).
- exact (j_D B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
    ameta_inv arodata_okS HSTK LAWS MTL HMT0 ABCMP AJ_NIL_IO).
- exact JE.
- exact (j_F B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
    ameta_inv arodata_okS HSTK LAWS MTL HMT0 HRO AMEMCHR AJ_NIL_IO).
Qed.

(* ---- segment J ----------------------------------------------------------------------------------------------- *)
Theorem seg_J_holds :
  seg_J B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
exact (seg_J_of_E (j_E B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS HSTK HEV LAWS MTL HMT0 HRO G GM G_IN G_OUT HIMG PSIG HPD AJ_NIL_IO)).
Qed.

End c.
End b.
End a.
