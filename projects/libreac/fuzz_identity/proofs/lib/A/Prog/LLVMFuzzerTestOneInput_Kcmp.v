(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its module names and addresses changed; 502 of its 569 lines of code are new or changed and 1076 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig IdentBlkTail YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_Kcut LLVMFuzzerTestOneInput_Klib.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require reac_box_catalogue_defect check_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Import RcIdentModel.

Lemma kc_pres_get : forall (regs regs' : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E. Qed.

Ltac kc_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] =>
    let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.

Ltac kc_awr := first
  [ cbn [ss_mem k_ssm add_cond]; apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo k_mfr]; lia | apply awr_ok_nil]
  | let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
    intros a (r & Hr & Ha); try unfold k_ssm in Hr; cbn [ss_mem add_cond In] in Hr;
    repeat (let Eq := fresh "Eq" in destruct Hr as [Eq | Hr];
      [subst r; try unfold k_mfr in Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|]);
    destruct Hr ].

Ltac kc_win := let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb wlo whi aa Hin Hr; cbv beta; unfold windows in Hin; try unfold k_ssm in Hin; try unfold k_mfr in Hin;
  cbn in Hin;
  repeat (let Eq := fresh "Eq" in destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; lia|]);
  destruct Hin.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma kc_shadow_off : forall F o, F mod 64 = 0 -> o mod 8 = 0 -> 0 <= F -> 0 <= o ->
  shadow_of_addr SHADOW_OFF (F + o) = shadow_addr F + o / 8.
Proof. intros F o HF Ho H0 H1. unfold shadow_of_addr, shadow_addr. lia. Qed.

Lemma kc_meet : forall (W : world SEGS) mem x y (s : list byte),
  bytes_at8 W mem x (s ++ [zb 0]) -> bytes_at8 W mem y (s ++ [zb 0]) -> nzl s ->
  (forall i, 0 <= i < Z.of_nat (length s) -> exists c, aview SEGS (w_H W) mem (x + i) = Some c /\
     aview SEGS (w_H W) mem (y + i) = Some c /\ c <> 0) /\
  aview SEGS (w_H W) mem (x + Z.of_nat (length s)) = Some 0 /\
  aview SEGS (w_H W) mem (y + Z.of_nat (length s)) = Some 0.
Proof.
intros W mem x y s Hx Hy Hnz.
assert (Hlen : length (s ++ [zb 0]) = S (length s)) by (rewrite length_app; cbn [length]; lia).
split.
- intros i Hi. exists (bz (nthb (s ++ [zb 0]) (Z.to_nat i))).
  split; [replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia; apply k_bytes_aview; [exact Hx | rewrite Hlen; lia]|].
  split; [replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia; apply k_bytes_aview; [exact Hy | rewrite Hlen; lia]|].
  unfold nthb. rewrite app_nth1 by lia.
  apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- assert (H0 : bz (nthb (s ++ [zb 0]) (length s)) = 0) by (unfold nthb; rewrite nth_middle; reflexivity).
  pose proof (k_bytes_aview W mem x (s ++ [zb 0]) (length s) Hx ltac:(rewrite Hlen; lia)) as Ax.
  pose proof (k_bytes_aview W mem y (s ++ [zb 0]) (length s) Hy ltac:(rewrite Hlen; lia)) as Ay.
  rewrite H0 in Ax, Ay. split; [exact Ax | exact Ay].
Qed.

Definition kc_env (g : ectx) (pos nm : Z) (regs : bvmap 5 word) : env :=
  Eimg (Ereg regs (k_extra (SlotModel.t_row (e_pl g)) (SlotModel.t_cap_disp (e_pl g))
    (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g)) (SlotModel.t_out (e_pl g)) nm (SFa g pos))).

Lemma kc_env_reg : forall g pos nm regs n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (kc_env g pos nm regs) n = getr regs r.
Proof. intros g pos nm regs n r Hn. unfold kc_env. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma kc_env_img : forall g pos nm regs, img_env VAL A_LIM (kc_env g pos nm regs).
Proof. intros. unfold kc_env. apply Eimg_env. Qed.

Lemma kc_env_agree : forall g pos nm regs, env_agree 32 (Ereg regs (k_extra (SlotModel.t_row (e_pl g))
  (SlotModel.t_cap_disp (e_pl g)) (SlotModel.t_cap_name (e_pl g)) (SlotModel.t_in (e_pl g))
  (SlotModel.t_out (e_pl g)) nm (SFa g pos))) (kc_env g pos nm regs).
Proof. intros. unfold kc_env. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma kc_env_ex : forall g pos nm regs,
  ew (kc_env g pos nm regs) 35 = Z_to_bv 64 (SlotModel.t_in (e_pl g)) /\
  ew (kc_env g pos nm regs) 36 = Z_to_bv 64 (SlotModel.t_out (e_pl g)) /\
  ew (kc_env g pos nm regs) 37 = Z_to_bv 64 SHADOW_OFF /\
  ew (kc_env g pos nm regs) 38 = Z_to_bv 64 nm /\
  ew (kc_env g pos nm regs) 39 = Z_to_bv 64 (SFa g pos).
Proof.
intros. unfold kc_env.
rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra regs _ 3)|]. split; [exact (ew_Ereg_extra regs _ 4)|].
split; [exact (ew_Ereg_extra regs _ 5)|]. split; [exact (ew_Ereg_extra regs _ 6) | exact (ew_Ereg_extra regs _ 7)].
Qed.

Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis ASTRCMP : StrcmpDef.astrcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_strcmp).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).

Theorem k_cmp : @k_cmp_stmt fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf nm tk dp W2 regs2' mem2' md2' W c HJend Hr HK.
destruct HJend as (ly2 & S2 & regs2 & mem2 & md2 & Ecfg & HJ0 & Hfrs0 & Hk & MLE0 & MOK0 & HC & HP).
unfold cfg_at in Ecfg. injection Ecfg as -> -> ->.
destruct HP as (HBL0 & Hwok & R27 & R26 & R24 & R20 & R21 & R22 & Vnm & Vcn & Vcd & Vin & Vout & Vrow &
  Bxn & Bxd & Znm & Zdp & Hr0).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HK as (-> & lyk & Sk & regs & mem & md & -> & HJ & Hfrs & MLE & MOK & HBL & KC & KB & KF &
  Q2 & Q9 & Q8 & Q3 & Q4 & Q19 & Q18 & _ & Q21 & Q22 & Q24 & Q26 & _).
destruct (Hr0 Hr) as (Bnm & Btk & Bdp). clear Hr0.
clear HJ0 Hfrs0 MLE0 MOK0 HBL0 R27 R26 R24 R20 R21 R22 Rsp Rs1 Rs0 Rgp Rtp Rs3 Hfds Hfs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'. assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr lyk 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames Sk)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyk Sk W2 mem md 4 pos HAR Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B lyk Sk W2 mem md 4 pos HAR Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsp47 : e_sp0 g <= 2 ^ 47) by (clear - Hshi H47; lia).
assert (Hsh1 : 0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling).
{ rewrite Esh. clear - HSF0 HSF1 C1. unfold SHADOW_OFF. lia. }
assert (VH : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem) a n v).
{ intros a n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk.
  apply KC; [clear - Hkk H0 H1 Hmf0; lia | clear - Hkk H0; lia]. }
apply VH in V80; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in Vrow; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in Vcn; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in Vcd; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in Vin; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in Vout; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in V176; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in Vnm; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in V192; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in Vmf24; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in Vra; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in Vs0; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in W9; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in W18; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in W19; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in W20; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in W21; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in W22; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in W23; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in W24; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in W25; [|lia|change (Z.of_nat 8) with 8; lia]. apply VH in W26; [|lia|change (Z.of_nat 8) with 8; lia].
apply VH in W27; [|lia|change (Z.of_nat 8) with 8; lia].
assert (Hblk : forall x, In x (k_blocks g nm tk dp) -> In x (ablocks B lyk Sk)).
{ intros x Hx. destruct HBL as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  apply in_or_app. left. exact Hx. }
assert (Inm : In (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) (ablocks B lyk Sk))
  by (apply Hblk; unfold k_blocks; left; reflexivity).
assert (Itk : In (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1) (ablocks B lyk Sk))
  by (apply Hblk; unfold k_blocks; right; left; reflexivity).
assert (Idp : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B lyk Sk))
  by (apply Hblk; unfold k_blocks; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Inm) as (_ & N4096 & Nceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Itk) as (_ & T4096 & Tceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Idp) as (_ & D4096 & Dceil & _).
destruct (k_r0 (e_pl g) Hr) as [_ Hfits].
destruct (k_fits (e_pl g) Hfits) as (Fnm & Ftk & Fdp).
pose proof (SlotModel.n_ln_le (e_pl g) Hwok) as HL21.
pose proof (SlotModel.n_ld_le (e_pl g) Hwok) as HL38.
unfold SlotModel.n_ln, SlotModel.n_ld in HL21, HL38, Fnm, Fdp.
pose proof (k_n_tk_len (e_pl g)) as HLT.
assert (Hcn : Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 1 <= req_size (Z.max (SlotModel.t_cap_name (e_pl g)) 1))
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_name (e_pl g)) 1) 0); lia).
assert (Hct : Z.of_nat (length (SlotModel.n_TK (e_pl g))) + 1 <= req_size (Z.max (SlotModel.t_cap_tok (e_pl g)) 1))
  by (rewrite HLT; unfold req_size; destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) 0); lia).
assert (Hcd : Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1 <= req_size (Z.max (SlotModel.t_cap_disp (e_pl g)) 1))
  by (unfold req_size; destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) 0); lia).
assert (BH : forall p cap (s : list byte), In (p, cap) (ablocks B lyk Sk) -> Z.of_nat (length s) + 1 <= req_size cap ->
  bytes_at8 W2 mem2 p (s ++ [zb 0]) -> bytes_at8 W2 mem p (s ++ [zb 0])).
{ intros p cap s Hin Hc Hb. unfold bytes_at8 in *. apply (k_garr8_moved W2 mem2 mem _ _); [|exact Hb].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk.
  apply (KB p cap kk Hin). clear - Hkk Hc; lia. }
assert (BF : forall o (s : list byte), 0 <= o -> o + Z.of_nat (length s) + 1 <= 1024 ->
  bytes_at8 W2 mem2 (SFa g pos + o) (s ++ [zb 0]) -> bytes_at8 W2 mem (SFa g pos + o) (s ++ [zb 0])).
{ intros o s H0 H1 Hb. unfold bytes_at8 in *. apply (k_garr8_moved W2 mem2 mem _ _); [|exact Hb].
  intros kk Hkk. rewrite length_map, length_app in Hkk. cbn [length] in Hkk.
  apply KF.
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, HFB. clear - Hkk H0 H1; lia.
  - intros [X Y]. apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 (SFa g pos + o + kk));
    [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp
    | rewrite Esh in X, Y; unfold SHADOW_OFF in X, Y; clear - X Y; lia | clear - Hkk H0 H1; lia]. }
assert (ZF : forall o n, 0 <= o -> o mod 8 = 0 -> 0 <= n -> o + n <= 688 ->
  sh_zero W2 mem2 (SFa g pos + o) n -> sh_zero W2 mem (SFa g pos + o) n).
{ intros o n H0 H8 Hn H1 Hz i Hi. specialize (Hz i Hi).
  rewrite (kc_shadow_off (SFa g pos) o HSF64 H8 ltac:(clear - HSF0; lia) H0) in Hz |- *.
  rewrite KF; [exact Hz | |].
  - right. unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. clear - Hi H0 H8 Hn H1; lia.
  - clear - Hi H0 H8 Hn H1; lia. }
assert (VFL : val_mem SEGS (rd W2 mem) (SFa g pos + 1016) 8 (flag_addr (e_ly g) 4 pos)).
{ eapply (val_mem_kept SEGS); [|exact Vflag]. intros kk Hkk. cbn in Hkk.
  apply KF.
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, HFB. clear - Hkk; lia.
  - intros [X Y]. apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 (SFa g pos + 1016 + kk));
    [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp
    | rewrite Esh in X, Y; unfold SHADOW_OFF in X, Y; clear - X Y; lia | clear - Hkk; lia]. }
assert (HINB : forall kk, 0 <= kk < Z.of_nat (length (e_pl g)) ->
  aview SEGS (w_H W2) mem (e_p g + kk) = aview SEGS (w_H W2) mem2 (e_p g + kk) /\
  0 <= e_p g + kk /\ e_p g + kk < alloc_ceiling).
{ intros kk Hkk. pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
  destruct HPRE' as ((HAR0 & _) & _ & _ & _ & Hinp & Hlen & _).
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [rewrite <- Hlen in Hkk; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hine) as (_ & Q4096 & Qceil & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  assert (Hin' : In (e_p g, e_n g) (ablocks B lyk Sk)).
  { destruct HBL as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
  split; [apply (KB (e_p g) (e_n g) kk Hin'); clear - Hkk Hlen Hrq; lia|].
  clear - Hkk Hlen Hrq Q4096 Qceil; lia. }
assert (HBn : bytes_at8 W2 mem nm (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0])) by exact (BH _ _ _ Inm Hcn Bnm).
assert (HBt : bytes_at8 W2 mem tk (SlotModel.n_TK (e_pl g) ++ [zb 0])) by exact (BH _ _ _ Itk Hct Btk).
assert (HBd : bytes_at8 W2 mem dp (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0])) by exact (BH _ _ _ Idp Hcd Bdp).
assert (HXn : bytes_at8 W2 mem (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0]))
  by (apply BF; [unfold V_nm; lia | unfold V_nm; lia | exact Bxn]).
assert (HXd : bytes_at8 W2 mem (SFa g pos + V_dp) (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0]))
  by (apply BF; [unfold V_dp; lia | unfold V_dp; lia | exact Bxd]).
assert (HZn : sh_zero W2 mem (SFa g pos + V_nm) N_nm)
  by (apply ZF; [unfold V_nm; lia | reflexivity | unfold N_nm; lia | unfold V_nm, N_nm; lia | exact Znm]).
assert (HZd : sh_zero W2 mem (SFa g pos + V_dp) N_dp)
  by (apply ZF; [unfold V_dp; lia | reflexivity | unfold N_dp; lia | unfold V_dp, N_dp; lia | exact Zdp]).
clear BH BF ZF KC KB KF Bnm Btk Bdp Bxn Bxd Znm Zdp Vflag VH.
assert (MB : forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
    aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) mem a) ->
  forall a (l : list byte), 0 <= a -> a + Z.of_nat (length l) <= alloc_ceiling ->
  bytes_at8 W2 mem a l -> bytes_at8 W2 m' a l).
{ intros m' HM a l H0 H1 Hb. unfold bytes_at8 in *. apply (k_garr8_moved W2 mem m' _ _); [|exact Hb].
  intros kk Hkk. rewrite length_map in Hkk.
  apply HM; [clear - Hkk H0 H1 C1; lia | clear - Hkk H1 Hmf0; unfold ESTACK; lia]. }
assert (MV : forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
    aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) mem a) ->
  forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rd W2 mem) a n v -> val_mem SEGS (rd W2 m') a n v).
{ intros m' HM a n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk.
  apply HM; [clear - Hkk H0 H1 Hmf0 C1; lia | clear - Hkk H0; lia]. }
assert (MVL : forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
    aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) mem a) ->
  forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem SEGS (rd W2 mem) a n v -> val_mem SEGS (rd W2 m') a n v).
{ intros m' HM a n v H0 H1 Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hkk.
  apply HM; [clear - Hkk H0 H1 C1; lia | clear - Hkk H1 Hmf0; unfold ESTACK; lia]. }
assert (MZ : forall m', (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
    aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) mem a) ->
  forall o n, 0 <= o -> o mod 8 = 0 -> 0 <= n -> o + n <= 1024 ->
  sh_zero W2 mem (SFa g pos + o) n -> sh_zero W2 m' (SFa g pos + o) n).
{ intros m' HM o n H0 H8 Hn H1 Hz i Hi. specialize (Hz i Hi).
  rewrite (kc_shadow_off (SFa g pos) o HSF64 H8 ltac:(clear - HSF0; lia) H0) in Hz |- *.
  rewrite HM; [exact Hz | clear - Hi H0 H8 Hn H1 Hsh1 C1; lia | clear - Hi H0 H8 Hn H1 Hsh1 Hmf0; unfold ESTACK; lia]. }
assert (HSM : forall regsX memX off, getr regsX 9 = w64 mf ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) -> aview SEGS (w_H W2) memX a = aview SEGS (w_H W2) mem a) ->
  st_ok_pi SEGS VAL (kc_env g pos nm regsX) (k_ssm off)
    (restrict (w_H W2) (mkst regsX (Z_to_bv 64 (BASE + off)) memX (seg_rom SEGS)))).
{ intros regsX memX off H9 HM.
  assert (VM : forall o v, 80 <= o -> o + 8 <= 192 -> val_mem SEGS (rd W2 mem) (mf + o) 8 v ->
    val_mem SEGS (rd W2 memX) (mf + o) 8 v).
  { intros o v H0 H1 Hv. apply (MV _ HM); [lia | clear - H1 Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact Hv]. }
  unfold kc_env. apply (k_ok_mf W2 regsX memX off mf); [exact H9 | lia | clear - Hmfb Hsp47; lia
  | apply VM; [lia | lia | exact V80] | apply VM; [lia | lia | exact Vrow] | apply VM; [lia | lia | exact Vcd]
  | apply VM; [lia | lia | exact Vcn] | apply VM; [lia | lia | exact Vin] | apply VM; [lia | lia | exact Vout]
  | apply VM; [lia | lia | exact V176] | apply VM; [lia | lia | exact Vnm]]. }
remember (kc_env g pos nm regs) as E eqn:HE.
pose proof (HSM regs mem 0x17ac Q9 ltac:(intros a _ _; reflexivity)) as HS. rewrite <- HE in HS.
pose proof (kc_env_img g pos nm regs) as HEI. rewrite <- HE in HEI.
pose proof (kc_env_agree g pos nm regs) as HAE. rewrite <- HE in HAE.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply kc_env_reg; exact Hn).
clear HE.
unfold cfg_at. change (w64 (BASE + 0x17ac)) with (Z_to_bv 64 (BASE + 0x17ac)).
paj_run_shc RUNP RUNC HS HJ.
{ kc_awr. }
rename ms into msA.
assert (KPA : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem msA) a = aview SEGS (w_H W2) mem a).
{ intros a Ha _. apply (kept_of_frame E _ (w_H W2) mem (ms_mem msA) (fun _ => False) HFr); [kc_win | exact Ha | intros []]. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (1%bv : bv 5) R1.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (EE 18%nat 18%bv eq_refl), Q18 in R10. rewrite (EE 26%nat 26%bv eq_refl), Q26 in R11.
rewrite (EE 2%nat 2%bv eq_refl), Q2 in R2. rewrite (EE 3%nat 3%bv eq_refl), Q3 in R3.
rewrite (EE 4%nat 4%bv eq_refl), Q4 in R4.
pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as APA.
pmkst HS.
pose proof HJ as (HART & _).
assert (HBnA : bytes_at8 W2 (ms_mem msA) nm (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0])).
{ apply (MB _ KPA); [clear - N4096; lia | rewrite length_app; cbn [length]; clear - Nceil Hcn; lia | exact HBn]. }
assert (HXnA : bytes_at8 W2 (ms_mem msA) (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0])).
{ apply (MB _ KPA); [clear - HSF0; unfold V_nm; lia
  | rewrite length_app; cbn [length]; clear - HSF1 HL21; unfold V_nm; lia | exact HXn]. }
assert (HZnA : sh_zero W2 (ms_mem msA) (SFa g pos + V_nm) N_nm).
{ apply (MZ _ KPA); [unfold V_nm; lia | reflexivity | unfold N_nm; lia | unfold V_nm, N_nm; lia | exact HZn]. }
destruct (kc_meet W2 (ms_mem msA) nm (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g)) HBnA HXnA
  (k_exp_nm_nz (e_pl g) Hwok)) as (KPR1 & AX1 & AY1).
destruct (k_heap_str B LAWS lyk Sk W2 (ms_mem msA) _ nm _ (SlotModel.n_EXP_NM (e_pl g)) HART Inm HBnA
  (k_exp_nm_nz (e_pl g) Hwok) Hcn) as (_ & AMX1 & RAX1 & HUX1 & _).
assert (Usp : spZ (ms_regs msA) = e_sp0 g + (mf - e_sp0 g)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small; [lia | clear - Hmf0 Hmfb Hsp47 C1; lia]. }
assert (SRX1 : src_ok SEGS W2 (ms_regs msA) (ms_mem msA) nm (Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 1)).
{ intros a Ha. rewrite Usp. split; [|clear - Ha N4096 Nceil Hcn Hmf0; unfold ESTACK; lia].
  destruct (Z.lt_ge_cases a (nm + Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))))) as [Hl | Hg].
  - destruct (KPR1 (a - nm) ltac:(lia)) as (cc & Hc1 & _ & _). replace a with (nm + (a - nm)) by lia.
    rewrite Hc1. discriminate.
  - replace a with (nm + Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g)))) by lia. rewrite AX1. discriminate. }
assert (SRY1 : src_ok SEGS W2 (ms_regs msA) (ms_mem msA) (SFa g pos + V_nm)
  (Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 1)).
{ intros a Ha. rewrite Usp. split; [|clear - Ha HSF0 HSF1 HL21 Hmf0; unfold ESTACK, V_nm in *; lia].
  destruct (Z.lt_ge_cases a (SFa g pos + V_nm + Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))))) as [Hl | Hg].
  - destruct (KPR1 (a - (SFa g pos + V_nm)) ltac:(lia)) as (cc & _ & Hc1 & _).
    replace a with (SFa g pos + V_nm + (a - (SFa g pos + V_nm))) by lia. rewrite Hc1. discriminate.
  - replace a with (SFa g pos + V_nm + Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g)))) by lia.
    rewrite AY1. discriminate. }
assert (WX1 : forall a, nm <= a <= nm + Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) ->
  ~ (e_sp0 g + (mf - e_sp0 g) - 2 * ESTACK <= a < e_sp0 g + (mf - e_sp0 g)))
  by (intros a Ha; clear - Ha N4096 Nceil Hcn Hmf0; unfold ESTACK; lia).
assert (WY1 : forall a, SFa g pos + V_nm <= a <= SFa g pos + V_nm + Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) ->
  ~ (e_sp0 g + (mf - e_sp0 g) - 2 * ESTACK <= a < e_sp0 g + (mf - e_sp0 g)))
  by (intros a Ha; clear - Ha HSF1 HL21 Hmf0; unfold ESTACK, V_nm in *; lia).
assert (AMY1 : amem_range (SFa g pos + V_nm) (Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 1))
  by (apply (amem_range_sub_app (SFa g pos) 1024); [exact HSFapp | exact HSF1 | unfold V_nm; lia
      | clear - HL21; unfold V_nm; lia | lia]).
assert (RAY1 : range_addressable (aview SEGS (w_H W2) (ms_mem msA)) SHADOW_OFF (SFa g pos + V_nm)
  (Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 1)).
{ apply (range_addressable_sub _ _ (SFa g pos + V_nm) N_nm); [| lia | clear - HL21; unfold N_nm; lia].
  apply zero_shadow_range; [clear - HSF64; unfold V_nm; lia | reflexivity | exact HZnA]. }
assert (HUY1 : shadow_hull_vis (aview SEGS (w_H W2) (ms_mem msA)) (SFa g pos + V_nm)
  (Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 1)).
{ eapply (shadow_hull_vis_of_frame SEGS B LAWS lyk Sk W2 (ms_mem msA) _ 4 pos); [exact HART | exact Hin4
  | rewrite EFa; unfold V_nm; lia | rewrite EFa, HFB; clear - HL21; unfold V_nm; lia | lia]. }
assert (P5 : nm + Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 1 <= 2 ^ 63) by (clear - N4096 Nceil Hcn C1; lia).
assert (P6 : SFa g pos + V_nm + Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 1 <= 2 ^ 63)
  by (clear - HSF1 HL21 C1; unfold V_nm; lia).
assert (P7 : (mf - e_sp0 g) mod 16 = 0) by (clear - Hmf32 Hsp0al; lia).
assert (P9 : 2 * ESTACK - (mf - e_sp0 g) <= LLVMF_STK) by (clear - Hmfb HSTK' Has; unfold ESTACK; lia).
assert (RET1 : YK0s.ret_ok (Z_to_bv 64 (BASE + 6072))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
eapply SRr_bind.
{ exact (@reac_box_catalogue_defect.aj_strcmp_at fx rc SK PI B LAWS _ ASTRCMP W2 (ms_regs msA) (ms_mem msA)
    _ _ _ _ _ _ _ _ _ _ _ _ _ nm (SFa g pos + V_nm) (Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))))
    (mf - e_sp0 g) _ HJ R10 R11 ltac:(clear - N4096; lia) ltac:(clear - HSF0; unfold V_nm; lia) ltac:(lia)
    ltac:(clear - HL21; lia) P5 P6 Usp P7 ltac:(clear - Hmfb; lia) P9 R3 R4 R1 RET1
    KPR1 (ex_intro _ 0 (ex_intro _ 0 (conj AX1 (conj AY1 (or_intror eq_refl)))))
    SRX1 SRY1 WX1 WY1 AMX1 AMY1 RAX1 HUX1 RAY1 HUY1). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v1 & -> & HJ3 & HP3 & Hv1 & Hcmp1 & Hfr1 & _).
assert (V1 : v1 = w64 0) by (apply Hcmp1; rewrite AX1, AY1; reflexivity).
assert (KP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem a).
{ intros a Ha Hn. rewrite (Hfr1 a Ha) by (clear - Hn; lia). exact (KPA a Ha Hn). }
assert (AP3 : aregs_preserved regs regs3) by exact (aregs_preserved_trans _ _ _ APA HP3).
assert (G9 : getr regs3 9 = w64 mf) by (rewrite (kc_pres_get _ _ 9%bv AP3) by kc_cs; exact Q9).
clear HS HJ HEI HAE EE KPA APA HBnA HXnA HZnA KPR1 AX1 AY1 AMX1 RAX1 HUX1 SRX1 SRY1 WX1 WY1 AMY1 RAY1 HUY1
  R10 R11 R1 R2 R3 R4 Usp HART Hcmp1 Hfr1 HP3 P5 P6 RET1.
remember (kc_env g pos nm regs3) as E1 eqn:HE1.
pose proof (HSM regs3 mem3 0x17b8 G9 KP3) as HS1. rewrite <- HE1 in HS1.
pose proof (kc_env_img g pos nm regs3) as HEI1. rewrite <- HE1 in HEI1.
pose proof (kc_env_agree g pos nm regs3) as HAE1. rewrite <- HE1 in HAE1.
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs3 r)
  by (intros n r Hn; rewrite HE1; apply kc_env_reg; exact Hn).
clear HE1.
psrr_branch_pi RUNP BR HS1.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  rewrite ?U_SLit, ?U_SOff, (EE1 10%nat 10%bv eq_refl), Hv1, V1. reflexivity. }
paj_run_shc RUNP RUNC HS1 HJ3.
{ kc_awr. }
rename ms into msB.
assert (KPB : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem msB) a = aview SEGS (w_H W2) mem a).
{ intros a Ha Hn. rewrite <- (KP3 a Ha Hn).
  apply (kept_of_frame E1 _ (w_H W2) mem3 (ms_mem msB) (fun _ => False) HFr); [kc_win | exact Ha | intros []]. }
clear HF HFr HG.
prreg HS1 (10%bv : bv 5) R10. prreg HS1 (11%bv : bv 5) R11. prreg HS1 (1%bv : bv 5) R1.
prreg HS1 (2%bv : bv 5) R2. prreg HS1 (3%bv : bv 5) R3. prreg HS1 (4%bv : bv 5) R4.
rewrite (EE1 22%nat 22%bv eq_refl), (kc_pres_get _ _ 22%bv AP3), Q22 in R10 by kc_cs.
rewrite (EE1 24%nat 24%bv eq_refl), (kc_pres_get _ _ 24%bv AP3), Q24 in R11 by kc_cs.
rewrite (EE1 2%nat 2%bv eq_refl), (kc_pres_get _ _ 2%bv AP3), Q2 in R2 by kc_cs.
rewrite (EE1 3%nat 3%bv eq_refl), (kc_pres_get _ _ 3%bv AP3), Q3 in R3 by kc_cs.
rewrite (EE1 4%nat 4%bv eq_refl), (kc_pres_get _ _ 4%bv AP3), Q4 in R4 by kc_cs.
pose proof (aregs_preserved_of_st_ok SEGS _ E1 _ _ regs3 _ HS1 HAE1 ltac:(vm_compute; reflexivity)) as APB.
pmkst HS1.
pose proof HJ3 as (HART & _).
assert (HBdB : bytes_at8 W2 (ms_mem msB) dp (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0])).
{ apply (MB _ KPB); [clear - D4096; lia | rewrite length_app; cbn [length]; clear - Dceil Hcd; lia | exact HBd]. }
assert (HXdB : bytes_at8 W2 (ms_mem msB) (SFa g pos + V_dp) (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0])).
{ apply (MB _ KPB); [clear - HSF0; unfold V_dp; lia
  | rewrite length_app; cbn [length]; clear - HSF1 HL38; unfold V_dp; lia | exact HXd]. }
assert (HZdB : sh_zero W2 (ms_mem msB) (SFa g pos + V_dp) N_dp).
{ apply (MZ _ KPB); [unfold V_dp; lia | reflexivity | unfold N_dp; lia | unfold V_dp, N_dp; lia | exact HZd]. }
destruct (kc_meet W2 (ms_mem msB) dp (SFa g pos + V_dp) (SlotModel.n_EXP_DP (e_pl g)) HBdB HXdB
  (k_exp_dp_nz (e_pl g) Hwok)) as (KPR2 & AX2 & AY2).
destruct (k_heap_str B LAWS lyk Sk W2 (ms_mem msB) _ dp _ (SlotModel.n_EXP_DP (e_pl g)) HART Idp HBdB
  (k_exp_dp_nz (e_pl g) Hwok) Hcd) as (_ & AMX2 & RAX2 & HUX2 & _).
assert (Usp : spZ (ms_regs msB) = e_sp0 g + (mf - e_sp0 g)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small; [lia | clear - Hmf0 Hmfb Hsp47 C1; lia]. }
assert (SRX2 : src_ok SEGS W2 (ms_regs msB) (ms_mem msB) dp (Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1)).
{ intros a Ha. rewrite Usp. split; [|clear - Ha D4096 Dceil Hcd Hmf0; unfold ESTACK; lia].
  destruct (Z.lt_ge_cases a (dp + Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))))) as [Hl | Hg].
  - destruct (KPR2 (a - dp) ltac:(lia)) as (cc & Hc1 & _ & _). replace a with (dp + (a - dp)) by lia.
    rewrite Hc1. discriminate.
  - replace a with (dp + Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g)))) by lia. rewrite AX2. discriminate. }
assert (SRY2 : src_ok SEGS W2 (ms_regs msB) (ms_mem msB) (SFa g pos + V_dp)
  (Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1)).
{ intros a Ha. rewrite Usp. split; [|clear - Ha HSF0 HSF1 HL38 Hmf0; unfold ESTACK, V_dp in *; lia].
  destruct (Z.lt_ge_cases a (SFa g pos + V_dp + Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))))) as [Hl | Hg].
  - destruct (KPR2 (a - (SFa g pos + V_dp)) ltac:(lia)) as (cc & _ & Hc1 & _).
    replace a with (SFa g pos + V_dp + (a - (SFa g pos + V_dp))) by lia. rewrite Hc1. discriminate.
  - replace a with (SFa g pos + V_dp + Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g)))) by lia.
    rewrite AY2. discriminate. }
assert (WX2 : forall a, dp <= a <= dp + Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) ->
  ~ (e_sp0 g + (mf - e_sp0 g) - 2 * ESTACK <= a < e_sp0 g + (mf - e_sp0 g)))
  by (intros a Ha; clear - Ha D4096 Dceil Hcd Hmf0; unfold ESTACK; lia).
assert (WY2 : forall a, SFa g pos + V_dp <= a <= SFa g pos + V_dp + Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) ->
  ~ (e_sp0 g + (mf - e_sp0 g) - 2 * ESTACK <= a < e_sp0 g + (mf - e_sp0 g)))
  by (intros a Ha; clear - Ha HSF1 HL38 Hmf0; unfold ESTACK, V_dp in *; lia).
assert (AMY2 : amem_range (SFa g pos + V_dp) (Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1))
  by (apply (amem_range_sub_app (SFa g pos) 1024); [exact HSFapp | exact HSF1 | unfold V_dp; lia
      | clear - HL38; unfold V_dp; lia | lia]).
assert (RAY2 : range_addressable (aview SEGS (w_H W2) (ms_mem msB)) SHADOW_OFF (SFa g pos + V_dp)
  (Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1)).
{ apply (range_addressable_sub _ _ (SFa g pos + V_dp) N_dp); [| lia | clear - HL38; unfold N_dp; lia].
  apply zero_shadow_range; [clear - HSF64; unfold V_dp; lia | reflexivity | exact HZdB]. }
assert (HUY2 : shadow_hull_vis (aview SEGS (w_H W2) (ms_mem msB)) (SFa g pos + V_dp)
  (Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1)).
{ eapply (shadow_hull_vis_of_frame SEGS B LAWS lyk Sk W2 (ms_mem msB) _ 4 pos); [exact HART | exact Hin4
  | rewrite EFa; unfold V_dp; lia | rewrite EFa, HFB; clear - HL38; unfold V_dp; lia | lia]. }
assert (P5 : dp + Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1 <= 2 ^ 63) by (clear - D4096 Dceil Hcd C1; lia).
assert (P6 : SFa g pos + V_dp + Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1 <= 2 ^ 63)
  by (clear - HSF1 HL38 C1; unfold V_dp; lia).
assert (RET2 : YK0s.ret_ok (Z_to_bv 64 (BASE + 6088))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
eapply SRr_bind.
{ exact (@reac_box_catalogue_defect.aj_strcmp_at fx rc SK PI B LAWS _ ASTRCMP W2 (ms_regs msB) (ms_mem msB)
    _ _ _ _ _ _ _ _ _ _ _ _ _ dp (SFa g pos + V_dp) (Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))))
    (mf - e_sp0 g) _ HJ3 R10 R11 ltac:(clear - D4096; lia) ltac:(clear - HSF0; unfold V_dp; lia) ltac:(lia)
    ltac:(clear - HL38; lia) P5 P6 Usp P7 ltac:(clear - Hmfb; lia) P9 R3 R4 R1 RET2
    KPR2 (ex_intro _ 0 (ex_intro _ 0 (conj AX2 (conj AY2 (or_intror eq_refl)))))
    SRX2 SRY2 WX2 WY2 AMX2 AMY2 RAX2 HUX2 RAY2 HUY2). }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & v2 & -> & HJ4 & HP4 & Hv2 & Hcmp2 & Hfr2 & _).
assert (V2 : v2 = w64 0) by (apply Hcmp2; rewrite AX2, AY2; reflexivity).
assert (KP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) mem4 a = aview SEGS (w_H W2) mem a).
{ intros a Ha Hn. rewrite (Hfr2 a Ha) by (clear - Hn; lia). exact (KPB a Ha Hn). }
assert (AP4 : aregs_preserved regs regs4)
  by exact (aregs_preserved_trans _ _ _ (aregs_preserved_trans _ _ _ AP3 APB) HP4).
assert (G9b : getr regs4 9 = w64 mf) by (rewrite (kc_pres_get _ _ 9%bv AP4) by kc_cs; exact Q9).
clear HS1 HJ3 HEI1 HAE1 EE1 KP3 KPB APB HBdB HXdB HZdB KPR2 AX2 AY2 AMX2 RAX2 HUX2 SRX2 SRY2 WX2 WY2 AMY2 RAY2 HUY2
  R10 R11 R1 R2 R3 R4 Usp HART Hcmp2 Hfr2 HP4 P5 P6 RET2 Hv1 V1 G9 Hc.
remember (kc_env g pos nm regs4) as E2 eqn:HE2.
pose proof (HSM regs4 mem4 0x17c8 G9b KP4) as HS2. rewrite <- HE2 in HS2.
pose proof (kc_env_img g pos nm regs4) as HEI2. rewrite <- HE2 in HEI2.
pose proof (kc_env_ex g pos nm regs4) as (X35 & X36 & X37 & X38 & X39).
rewrite <- HE2 in X35, X36, X37, X38, X39.
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs4 r)
  by (intros n r Hn; rewrite HE2; apply kc_env_reg; exact Hn).
clear HE2.
paj_run_sh RUNP HS2 HJ4.
{ kc_awr. }
rename ms into msC.
assert (KPC : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem msC) a = aview SEGS (w_H W2) mem a).
{ intros a Ha Hn. rewrite <- (KP4 a Ha Hn).
  apply (kept_of_frame E2 _ (w_H W2) mem4 (ms_mem msC) (fun _ => False) HFr); [kc_win | exact Ha | intros []]. }
clear HF HFr HG.
psrr_branch_pi RUNP BR HS2.
{ exfalso. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
  rewrite ?U_SLit, ?U_SOff, (EE2 10%nat 10%bv eq_refl), Hv2, V2. reflexivity. }
paj_run_to_sh RUNTOP HS2 HJ4 0x17f4.
{ kc_awr. }
rename ms into msD.
assert (KPD : forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
  aview SEGS (w_H W2) (ms_mem msD) a = aview SEGS (w_H W2) mem a).
{ intros a Ha Hn. rewrite <- (KPC a Ha Hn).
  apply (kept_of_frame E2 _ (w_H W2) (ms_mem msC) (ms_mem msD) (fun _ => False) HFr); [kc_win | exact Ha | intros []]. }
clear HF HFr HG.
apply SRr_ret. unfold k_loop_at, acut. pmkst HS2.
prreg HS2 (10%bv : bv 5) F10. prreg HS2 (15%bv : bv 5) F15. prreg HS2 (12%bv : bv 5) F12.
prreg HS2 (13%bv : bv 5) F13. prreg HS2 (14%bv : bv 5) F14. prreg HS2 (6%bv : bv 5) F6.
prreg HS2 (18%bv : bv 5) F18. prreg HS2 (21%bv : bv 5) F21. prreg HS2 (22%bv : bv 5) F22.
prreg HS2 (24%bv : bv 5) F24. prreg HS2 (25%bv : bv 5) F25. prreg HS2 (2%bv : bv 5) F2.
prreg HS2 (9%bv : bv 5) F9. prreg HS2 (8%bv : bv 5) F8. prreg HS2 (3%bv : bv 5) F3.
prreg HS2 (4%bv : bv 5) F4. prreg HS2 (19%bv : bv 5) F19.
assert (GP : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> acallee_saved (bv_unsigned r) ->
  getr (ms_regs msD) r = ew E2 n -> getr (ms_regs msD) r = getr regs r).
{ intros r n Hn Hcs Hr'. rewrite Hr', (EE2 n r Hn). exact (kc_pres_get _ _ r AP4 Hcs). }
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as [Efd Efs].
exists lyk, Sk, (ms_regs msD), (ms_mem msD). eexists.
split; [reflexivity|].
split; [exact HJ4|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon.
  split; [rewrite (GP 2%bv 2%nat eq_refl ltac:(kc_cs) F2); exact Q2|].
  split; [rewrite (GP 9%bv 9%nat eq_refl ltac:(kc_cs) F9); exact Q9|].
  split; [rewrite (GP 8%bv 8%nat eq_refl ltac:(kc_cs) F8); exact Q8|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (GP 3%bv 3%nat eq_refl ltac:(kc_cs) F3); exact Q3|].
  split; [rewrite (GP 4%bv 4%nat eq_refl ltac:(kc_cs) F4); exact Q4|].
  split; [rewrite (GP 19%bv 19%nat eq_refl ltac:(kc_cs) F19); exact Q19|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact V80]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact V192]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact V176]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact Vra]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact Vs0]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W9]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W18]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W19]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W20]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W21]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W22]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W23]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W24]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W25]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W26]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact W27]|].
  split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact Vmf24]|].
  split; [apply (MVL _ KPD); [clear - HSF0; lia | clear - HSF1; change (Z.of_nat 8) with 8; lia | exact VFL]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  unfold bytes_at8. unfold bytes_at8 in Hinb. apply (k_garr8_moved W2 mem2 (ms_mem msD) _ _); [|exact Hinb].
  intros kk Hkk. rewrite length_map in Hkk. destruct (HINB kk Hkk) as (Em & Hb0 & Hb1).
  rewrite <- Em. apply KPD; [clear - Hb0 Hb1 C1; lia | clear - Hb1 Hmf0; unfold ESTACK; lia]. }
split; [exact HBL|]. split; [exact Hr|].
split; [apply Nat.le_0_l|].
split; [reflexivity|]. split; [reflexivity|].
split; [rewrite F10, X38; unfold w64; f_equal; lia|].
split; [rewrite F15, X38; unfold w64; f_equal; lia|].
split; [rewrite F12; reflexivity|].
split; [rewrite F13; reflexivity|].
split; [rewrite F14; reflexivity|].
split; [rewrite F6, X37; reflexivity|].
split; [rewrite F18, X39, unsigned_lit_small; [reflexivity | clear - HSF0 HSF1 C1; lia]|].
split; [rewrite (GP 21%bv 21%nat eq_refl ltac:(kc_cs) F21); exact Q21|].
split; [rewrite (GP 22%bv 22%nat eq_refl ltac:(kc_cs) F22); exact Q22|].
split; [rewrite F24, X35; reflexivity|].
split; [rewrite F25, X36; reflexivity|].
split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact Vrow]|].
split; [apply (MV _ KPD); [clear - Hmfb; lia | clear - Hmfb Hsp47; change (Z.of_nat 8) with 8; lia | exact Vnm]|].
split; [apply (MB _ KPD); [clear - N4096; lia | rewrite length_app; cbn [length]; clear - Nceil Hcn; lia | exact HBn]|].
split; [apply (MB _ KPD); [clear - T4096; lia | rewrite length_app; cbn [length]; clear - Tceil Hct; lia | exact HBt]|].
apply (MB _ KPD); [clear - D4096; lia | rewrite length_app; cbn [length]; clear - Dceil Hcd; lia | exact HBd].
Qed.
End c.
End b.
End a.
