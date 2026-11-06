(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-278
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1570-1572, 1593-1598, 1605-1613 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The
   same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:106-109. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_base.v; 301 of its 390 lines of code are new or changed and 554 lines of the source are left out. *)
(* The token piece of seg_K of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B): k_tok_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_stmt.v, +0x19a8 .. +0x19c0 (fuzz_identity.asan-ubsan 0x8211c ..
   0x82134). The stretch is `mv a0,s5`, the strlen wrapper call (0x82120), `sext.w a0,a0`, `mv a1,s5`,
   `ld a2,128(s1)` and the check_str call (0x82130). s5 = tk is a live heap block of KH (hblocks) holding
   n_TK ++ [0] (KH's n_r = 0 conjunct), so the wrapper returns n_lt (KModel.tk_len), and check_str gets
   (n_lt, tk, cap_tok) with n_lt < cap_tok (SlotModel.n_fits). The stretch has no ASan check of its own (the
   only load is the machine-frame slot mf+128) and no __asan_report call. Two symbolic runs (engine of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_L.v), the wrapper and check_str in the journal form of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_base.v (k_strlen_at, k_check_str_at), the string facts of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_str.v (ks_str). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81 IdentBlkTail.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
check_str reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the frame-offset arithmetic below needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_K_hand_stmt LLVMFuzzerTestOneInput_seg_K_base LLVMFuzzerTestOneInput_seg_K_hand_str.

(* ---- the symbolic states ---------------------------------------------------------------------- *)
(* +0x19a8: `mv a0,s5` and the strlen wrapper call; no memory. *)
Definition kt_ss1 : sstate := mkSS 0x19a8 sr_atoms [] None (mkFacts [] [] []).
(* +0x19b0: `sext.w a0,a0`, `mv a1,s5`, the load of cap_tok from the machine frame's slot mf+128
   (read-only; atom 32 is cap_tok) and the check_str call. *)
Definition kt_r2mf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 128 136 128 128 [YP09.mkChunk 128 (CVal 8 (SOff 32 0))].
Definition kt_ss2 : sstate := mkSS 0x19b0 sr_atoms [kt_r2mf] None (mkFacts [] [] []).

(* A register of a symbolic state after a run, with the symbolic value computed and not normalised. *)
Ltac kt_reg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
(* The callee-saved side condition of aregs_preserved, with the register literal computed. *)
Ltac kt_cs :=
unfold acallee_saved;
match goal with
| |- context [bv_unsigned ?x] =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v
end; lia.

Lemma kt_pres : forall (r : bv 5) (regs regs' : bvmap 5 word),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
intros r regs regs' H Hr. specialize (H (bv_unsigned r) Hr). rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* `sext.w` (addiw 0) of a non-negative 32-bit value. *)
Lemma kt_aluw0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 0)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv.
rewrite denot_lit_U. f_equal.
rewrite U_of_S, S_SAluw, (U_atom E n v Hn ltac:(lia)), U_SLit. cbn [zalu_raw].
unfold zcanon, M64, bv_swrap, bv_half_modulus, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
change (2 ^ 32 / 2) with (2 ^ 31).
rewrite (Z.mod_small v (2 ^ 32)) by lia. repeat (rewrite Z.mod_0_l by lia). rewrite Z.add_0_r.
rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.

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
Variable G : list (Z * Z).
#[local] Notation KPREn := (KPRE B RLO RHI LLVMF_STK arodata_okS G).
#[local] Notation KHn := (KH B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation KCn := (KC B LLVMF_STK).
Section h.
Hypothesis HPRE : KPREn.
Lemma kt_laws : AR_laws SEGS B. Proof. eapply k_laws. exact HPRE. Qed.
Let RUNP := SRr_run_pi_AJ B kt_laws.
Let RUNC := SRr_run_pi_AJ_call B kt_laws.
Lemma kt_sig_cs : SIGMA IB_check_str = BASE + AF_check_str.
Proof. pose proof (k_psig B RLO RHI LLVMF_STK arodata_okS G HPRE) as PS. exact (PS IB_check_str AF_check_str eq_refl). Qed.

Section run.
Variables (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model).
Hypothesis HKH : KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2.

Lemma kt_geom :
  alloc_ceiling + 8192 <= mf - 8208 /\ mf + 320 <= e_sp0 g /\ e_sp0 g <= 2 ^ 47 /\
  e_sp0 g mod 16 = 0 /\ e_sp0 g - 336 <= mf /\ mf mod 32 = 0 /\ e_sp0 g - LLVMF_STK <= mf - 8208 /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  frame_addr ly2 4 pos = SFa g pos /\
  shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8 /\ 0 <= shadow_addr (SFa g pos) /\
  shadow_addr (SFa g pos) + 128 <= alloc_ceiling /\ In (4, pos) (frames S2).
Proof. eapply k_geom; [exact HPRE | exact HKH]. Qed.

(* The token's length and capacity on the n_r = 0 path (SlotModel.n_fits). *)
Lemma kt_nlt : 0 <= SlotModel.n_lt (e_pl g) < SlotModel.t_cap_tok (e_pl g) /\ SlotModel.t_cap_tok (e_pl g) < 40.
Proof.
pose proof HKH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnr0).
destruct (KModel.n_r0 _ Hnr0) as [_ Hfits].
destruct (KModel.fits_unfold _ Hfits) as (_ & Hlt & _).
pose proof (KModel.tk_len (e_pl g)) as Etk.
assert (Hc : 0 <= SlotModel.t_cap_tok (e_pl g) < 40) by (unfold SlotModel.t_cap_tok; apply Z.mod_pos_bound; lia).
clear - Hlt Etk Hc. lia.
Qed.

(* The token string tk (s5): the facts the strlen wrapper and check_str ask of it at a KC state. *)
Lemma kt_str : forall mem md,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem md (4 * Z.of_nat (m_nrec g) + 7) ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  let r := SlotModel.n_lt (e_pl g) in
  0 < tk /\ tk + r + 1 <= alloc_ceiling /\
  first_byte SEGS W2 mem tk (r + 1) 0 r /\
  (forall a, tk <= a < tk + (r + 1) -> aview SEGS (w_H W2) mem a <> None) /\
  amem_range tk (r + 1) /\
  range_addressable (aview SEGS (w_H W2) mem) SHADOW_OFF tk (r + 1) /\
  shadow_hull_vis (aview SEGS (w_H W2) mem) tk (r + 1) /\
  (forall a, tk + r < a < tk + r - (tk + r) mod 8 + 8 -> aview SEGS (w_H W2) mem a <> None) /\
  (tk + r + 1 <= IMG_LO \/ IMG_TOP <= tk).
Proof.
intros mem md HJ HKP.
pose proof HKH as (_ & _ & _ & _ & _ & _ & HHB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HR0 & Hnr0).
destruct (HR0 Hnr0) as (_ & Hbt & _).
destruct (KModel.n_r0 _ Hnr0) as [Hwok Hfits].
destruct (KModel.fits_unfold _ Hfits) as (_ & Hlt & _).
pose proof (KModel.tk_len (e_pl g)) as Etk.
assert (Hin : In (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1) (ablocks B ly2 S2)).
{ destruct HHB as [Hperm _]. eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
  right; left; reflexivity. }
assert (Hnz : KModel.nzb (SlotModel.n_TK (e_pl g)) = true).
{ unfold SlotModel.n_TK, SlotModel.TOK. apply KModel.nzb_tok, KModel.nzb_EXP_NM, Hwok. }
assert (Hlen : Z.of_nat (length (SlotModel.n_TK (e_pl g))) + 1 <= req_size (Z.max (SlotModel.t_cap_tok (e_pl g)) 1)).
{ rewrite Etk. pose proof (Z.le_max_l (SlotModel.t_cap_tok (e_pl g)) 1) as Hm1.
  pose proof (Z.le_max_r (SlotModel.t_cap_tok (e_pl g)) 1) as Hm2.
  assert (Hreq : req_size (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) = Z.max (SlotModel.t_cap_tok (e_pl g)) 1).
  { unfold req_size. destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) 0) as [E|E];
      [exfalso; clear - E Hm2; lia | reflexivity]. }
  rewrite Hreq. clear - Hlt Hm1; lia. }
pose proof (ks_str B RLO RHI LLVMF_STK arodata_okS G HPRE g pos mf ly2 S2 W2 mem2 mem md tk
  (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) (SlotModel.n_TK (e_pl g)) (proj1 HJ) HKP Hin Hbt Hnz Hlen) as H.
cbv zeta in H. rewrite Etk in H. cbv zeta. exact H.
Qed.

(* A step that changes memory only inside the callees' window below sp = mf keeps kkeep. *)
Lemma kt_kkeep_out : forall mem mem', kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - (16 + 2 * ESTACK) <= a < mf) ->
     aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) mem a) ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem'.
Proof.
intros mem mem' (K1 & K2 & K3) HO.
pose proof kt_geom as (G1 & _ & _ & _ & _ & _ & _ & G8 & G9 & _ & _ & G12 & _ & G14 & G15 & _).
pose proof asan_consts as (C1 & _).
pose proof HKH as (HJ2 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
split; [|split].
- intros a Ha Hw. rewrite (HO a ltac:(clear - Ha C1; lia) Hw). exact (K1 a Ha Hw).
- intros b n i Hb Hi.
  destruct (al_blocks SEGS B kt_laws ly2 S2 W2 mem2 md2 b n (proj1 HJ2) Hb) as (_ & Hb4 & Hbc & _).
  rewrite (HO (b + i) ltac:(clear - Hb4 Hbc Hi C1; lia) ltac:(rewrite Hes; clear - Hb4 Hbc Hi G1; lia)).
  exact (K2 b n i Hb Hi).
- intros a Ha Hc Hs.
  assert (Hlo : 0 <= a < alloc_ceiling).
  { unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. rewrite G12 in Ha.
    change (fs_frame_bytes 4) with 1024 in Ha. change (1024 / 8) with 128 in Ha.
    clear - Ha G8 G9 G14 G15. lia. }
  rewrite (HO a ltac:(clear - Hlo C1; lia) ltac:(rewrite Hes; clear - Hlo G1; lia)).
  exact (K3 a Ha Hc Hs).
Qed.

(* check_str's own journal (window [mf - CHECK_STR_STK, mf), no frames of its own) keeps kkeep. *)
Lemma kt_kkeep_cj : forall mem mem' md md' sp, sp = mf -> kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  ajournal SEGS B check_str.CHECK_STR_STK sp [] ly2 S2 W2 mem md [] ly2 S2 W2 mem' md' 0 ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem'.
Proof.
intros mem mem' md md' sp -> (K1 & K2 & K3) HJc.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & _ & J3 & _).
pose proof kt_geom as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G16).
split; [|split].
- intros a Ha Hw. rewrite (J1 a Ha ltac:(unfold check_str.CHECK_STR_STK; exact Hw)). exact (K1 a Ha Hw).
- intros b n i Hb Hi. rewrite (J2 b n i Hb Hb Hi (inFP_nil _)). exact (K2 b n i Hb Hi).
- intros a Ha Hc Hs. rewrite (J3 4 pos a G16 Ha (inFP_nil _)). exact (K3 a Ha Hc Hs).
Qed.

Lemma kt_main : forall regs mem md (Q : world SEGS -> config -> Prop),
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md -> KR g pos regs -> getr regs 18 = w64 nm ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> KR g pos regs' ->
    getr regs' 18 = w64 nm -> SRr SEGS W2 (cfg_at SEGS (BASE + 0x19c0) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19a8) regs mem md) Q.
Proof.
intros regs mem md Q HKC HKR R18 HK.
destruct HKC as (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh).
pose proof kt_geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof kt_nlt as ((Hr0 & Hrc) & Hc40).
pose proof HKH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V128 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : check_str.CHECK_STR_STK = 8208) by reflexivity.
set (r := SlotModel.n_lt (e_pl g)) in *.
set (c := SlotModel.t_cap_tok (e_pl g)) in *.
assert (Hmf : 0 <= mf < 2 ^ 64) by (clear - G1 G2 G3 C1; lia).
assert (Hsp0 : 0 <= e_sp0 g < 2 ^ 64) by (clear - G1 G2 G3 C1; lia).
assert (Ho16 : (mf - e_sp0 g) mod 16 = 0) by (clear - G4 G6; lia).
unfold cfg_at. change (w64 (BASE + 0x19a8)) with (Z_to_bv 64 (BASE + 0x19a8)).
(* ================ run 1: +0x19a8, `mv a0,s5`, the strlen wrapper call ================ *)
remember (Eimg (Ereg regs [])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs r)
  by (intros n r' Hn; rewrite HE1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE1 : env_agree 32 (Ereg regs []) E1)
  by (split; [intros n Hn; rewrite HE1, Eimg_low by (unfold A_TEXT; lia); reflexivity | rewrite HE1; reflexivity]).
assert (HS1 : st_ok_pi SEGS VAL E1 kt_ss1
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x19a8)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kt_ss1. apply pa_entry_st_ok_full.
  - rewrite HE1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS1 HJ.
{ apply awr_ok_nil. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem a).
{ intros a Ha. apply (kept_of_frame E1 _ (w_H W2) mem (ms_mem ms) (fun _ => False) HFr); [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold kt_ss1, windows in Hin. cbn in Hin. destruct Hin. }
clear HF HFr HG.
assert (P1 : aregs_preserved regs (ms_regs ms)).
{ eapply aregs_preserved_of_st_ok; [exact HS1 | exact HAE1 | vm_compute; reflexivity]. }
prreg HS1 (10%bv : bv 5) R1_10. prreg HS1 (1%bv : bv 5) R1_1.
rewrite (EE1 21%nat 21%bv eq_refl), Rtk in R1_10.
assert (HKP1 : kkeep B g pos mf ly2 S2 W2 mem2 (ms_mem ms))
  by (apply (kt_kkeep_out mem); [exact HKP | intros a Ha _; exact (KEEP1 a Ha)]).
pose proof (kt_str (ms_mem ms) _ HJ HKP1) as H1str. cbv zeta in H1str. fold r in H1str.
destruct H1str as (Hx0 & Hxc & Hfb1 & Hpr1 & Hmr1 & Hra1 & Hhv1 & Htl1 & Himg1).
assert (Usp1 : spZ (ms_regs ms) = e_sp0 g + (mf - e_sp0 g)).
{ unfold spZ. rewrite (kt_pres 2%bv _ _ P1 ltac:(kt_cs)), Rsp. unfold w64. rewrite unsigned_lit_small by exact Hmf.
  clear; lia. }
pmkst HS1.
eapply SRr_bind.
{ apply (k_strlen_at B RLO RHI LLVMF_STK arodata_okS G HPRE W2 (ms_regs ms) (ms_mem ms) LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 7) tk r
    (mf - e_sp0 g) (Z_to_bv 64 (BASE + 6576)) HJ R1_10 Hx0 Hr0).
  - clear - Hrc Hc40; lia.
  - clear - Hxc C1; lia.
  - exact Usp1.
  - exact Ho16.
  - clear - G2; lia.
  - rewrite Hes. clear - G7; lia.
  - rewrite (kt_pres 3%bv _ _ P1 ltac:(kt_cs)). exact Rgp.
  - rewrite (kt_pres 4%bv _ _ P1 ltac:(kt_cs)). exact Rtp.
  - exact R1_1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - exact Hfb1.
  - intros a Ha. split; [exact (Hpr1 a Ha)|]. rewrite Usp1, Hes. clear - Ha Hxc G1 C1; lia.
  - intros a Ha. rewrite Hes. clear - Ha Hxc G1; lia.
  - exact Hmr1.
  - exact Hra1.
  - exact Hhv1.
  - exact Htl1.
  - exact (proj2 (k_aro B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
      ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH _ _ HJ)). }
cbv beta. intros W' c' _ (-> & regs3 & mem3 & md3 & -> & HJ3 & P2 & R3_10 & Hfr3 & _).
clear HS1 KEEP1 Hfb1 Hpr1 Hmr1 Hra1 Hhv1 Htl1.
assert (HKP3 : kkeep B g pos mf ly2 S2 W2 mem2 mem3).
{ apply (kt_kkeep_out (ms_mem ms)); [exact HKP1|]. intros a Ha Hw. apply Hfr3; [exact Ha|].
  rewrite Hes in Hw |- *. clear - Hw; lia. }
clear Hfr3.
(* ================ run 2: +0x19b0, `sext.w a0,a0`, `mv a1,s5`, the load of cap_tok, check_str ================ *)
remember (Eimg (Ereg regs3 [Z_to_bv 64 c])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs3 r)
  by (intros n r' Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs3 [Z_to_bv 64 c]) E2)
  by (split; [intros n Hn; rewrite HE2, Eimg_low by (unfold A_TEXT; lia); reflexivity | rewrite HE2; reflexivity]).
assert (E2_32 : ew E2 32 = Z_to_bv 64 c)
  by (rewrite HE2, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (U2_9 : bv_unsigned (ew E2 9) = mf).
{ rewrite (EE2 9%nat 9%bv eq_refl), (kt_pres 9%bv _ _ P2 ltac:(kt_cs)), (kt_pres 9%bv _ _ P1 ltac:(kt_cs)), Rs1.
  unfold w64. apply unsigned_lit_small. exact Hmf. }
assert (V128' : val_mem SEGS (rd W2 mem3) (mf + 128) 8 c).
{ apply (k_vm_hi B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
    ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH mem3 (mf + 128) 8 c HKP3);
  [clear; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - Hmf G1 G2 G3; lia | exact V128]. }
assert (HS2 : st_ok_pi SEGS VAL E2 kt_ss2
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + 0x19b0)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kt_ss2. apply pa_entry_st_ok_full.
  - rewrite HE2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold kt_r2mf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2_9. split; [clear - G1 C1; lia|]. split; [clear - G1 G2 G3 C1; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E2 _ mf 128 8 (SOff 32 0) c);
    [ cbn [sv_denot]; rewrite E2_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | cbn; clear - Hrc Hr0 Hc40; lia | cbn; lia | exact V128' ].
  - cbn [pairwise_disjoint all_disjoint].
    repeat match goal with |- _ /\ _ => split end; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS2 HJ3.
{ intros a (r' & Hr' & Ha). unfold kt_ss2 in Hr'. cbn [ss_mem In] in Hr'.
  destruct Hr' as [<- | []]. unfold kt_r2mf in Ha.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. clear - Ha; lia. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha. apply (kept_of_frame E2 _ (w_H W2) mem3 (ms_mem ms0) (fun _ => False) HFr); [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr'. unfold kt_ss2, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr'. clear - Hr'; lia. }
clear HF HFr HG.
assert (P3 : aregs_preserved regs3 (ms_regs ms0)).
{ eapply aregs_preserved_of_st_ok; [exact HS2 | exact HAE2 | vm_compute; reflexivity]. }
kt_reg HS2 (10%bv : bv 5) R4_10.
prreg HS2 (11%bv : bv 5) R4_11. prreg HS2 (12%bv : bv 5) R4_12. prreg HS2 (1%bv : bv 5) R4_1.
rewrite (kt_aluw0 E2 10%nat r) in R4_10
  by (first [rewrite (EE2 10%nat 10%bv eq_refl); exact R3_10 | clear - Hr0 Hrc Hc40; lia]).
rewrite (EE2 21%nat 21%bv eq_refl), (kt_pres 21%bv _ _ P2 ltac:(kt_cs)), (kt_pres 21%bv _ _ P1 ltac:(kt_cs)), Rtk
  in R4_11.
rewrite E2_32 in R4_12.
assert (HKP4 : kkeep B g pos mf ly2 S2 W2 mem2 (ms_mem ms0))
  by (apply (kt_kkeep_out mem3); [exact HKP3 | intros a Ha _; exact (KEEP2 a Ha)]).
clear KEEP2.
pose proof (kt_str (ms_mem ms0) _ HJ3 HKP4) as H2str. cbv zeta in H2str. fold r in H2str.
destruct H2str as (_ & _ & Hfb2 & _ & Hmr2 & Hra2 & Hhv2 & Htl2 & _).
assert (P13 : aregs_preserved regs (ms_regs ms0))
  by (eapply aregs_preserved_trans; [eapply aregs_preserved_trans; [exact P1 | exact P2] | exact P3]).
assert (Usp2 : spZ (ms_regs ms0) = e_sp0 g + (mf - e_sp0 g)).
{ unfold spZ. rewrite (kt_pres 2%bv _ _ P13 ltac:(kt_cs)), Rsp. unfold w64. rewrite unsigned_lit_small by exact Hmf.
  clear; lia. }
destruct (k_achain B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms0) HKP4) as (ch & Hch).
pmkst HS2. rewrite kt_sig_cs.
eapply SRr_bind.
{ apply (k_check_str_at B RLO RHI LLVMF_STK arodata_okS G HPRE W2 (ms_regs ms0) (ms_mem ms0) LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 7)
    (mf - e_sp0 g) (Z_to_bv 64 (BASE + 6592)) ch r tk c HJ3 Usp2 Ho16).
  - clear - G2; lia.
  - rewrite WS. clear - G7; lia.
  - rewrite (kt_pres 3%bv _ _ P13 ltac:(kt_cs)). exact Rgp.
  - rewrite (kt_pres 4%bv _ _ P13 ltac:(kt_cs)). exact Rtp.
  - exact R4_1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO; lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by (clear; lia).
    replace (s0Z (ms_regs ms0)) with (e_sp0 g); [exact Hch|].
    unfold s0Z. rewrite (kt_pres 8%bv _ _ P13 ltac:(kt_cs)), Rs0. unfold w64.
    rewrite unsigned_lit_small by exact Hsp0. reflexivity.
  - exact (proj2 (k_aro B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
      ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH _ _ HJ3)).
  - exact R4_10.
  - exact R4_11.
  - exact R4_12.
  - clear - Hr0 Hrc Hc40; lia.
  - clear - Hr0 Hrc Hc40; lia.
  - intros _. unfold check_str.tcheck_str_ok.
    split; [exact Hrc|]. split; [exact Hx0|]. split; [exact Himg1|]. split; [exact Hfb2|].
    split; [intros a Ha; rewrite Usp2, WS; clear - Ha Hxc G1; lia|].
    split; [exact Hmr2|]. split; [exact Hra2|]. split; [exact Hhv2 | exact Htl2]. }
cbv beta. intros W' c' _ (ly' & S' & regs4 & mem4 & md4 & -> & HJ4 & HJc & P4 & (-> & -> & ->)).
assert (PP : aregs_preserved regs regs4) by (eapply aregs_preserved_trans; [exact P13 | exact P4]).
destruct HKR as (R22 & R25 & R26).
refine (HK regs4 mem4 md4 _ _ _).
- split; [rewrite Z.add_0_r in HJ4; exact HJ4|].
  split; [exact (kt_kkeep_cj (ms_mem ms0) mem4 _ md4 (e_sp0 g + (mf - e_sp0 g)) ltac:(clear; lia) HKP4 HJc)|].
  rewrite !(kt_pres _ _ _ PP) by kt_cs.
  repeat split; assumption.
- unfold KR. rewrite !(kt_pres _ _ _ PP) by kt_cs. repeat split; assumption.
- rewrite (kt_pres _ _ _ PP) by kt_cs. exact R18.
Qed.

End run.
End h.

Lemma k_tok : k_tok_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS G.
Proof.
intros HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH.
exact (kt_main HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH).
Qed.

Check (k_tok : k_tok_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS G).

End c.
End b.
End a.
