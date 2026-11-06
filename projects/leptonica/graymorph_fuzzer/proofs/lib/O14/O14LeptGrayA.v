(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptStderr O14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL7a.
Import O14CL7a.O14LeptErr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptPixHdr O14LeptPixCreate O14LeptPixDestroy O14LeptCmapValid O14LeptCmap2 O14LeptPixCopyA O14LeptPixCopy O14LeptPixSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14Kit.
Import O14Kit.O14MemcpyBase. Import O14Kit.O14Memcpy. Import O14Kit.O14Memset.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptGrayD_iface O14_code_gmACE.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition PC_pixAddBorderGeneral : Z := 0x178a4.
Definition PC_pixRemoveBorderGeneral : Z := 0x17b60.
Definition PC_pixDestroy : Z := 0x15b78.
Definition ABG_STACK : Z := 128 + 112 + LSF.      (* [comment removed for export] *)
Definition RBG_STACK : Z := 96 + 112 + LSF.       (* [comment removed for export] *)

Section GrayA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pixCopyResolution_run : forall regs m (pixd pixs : Z) (vs vd : pixv) (ret : word),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> pixs <> pixd -> PIXat m pixs vs -> PIXat m pixd vd -> p_xres vs = 0%Z -> p_yres vs = 0%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x15f84 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixd pixs vs vd ret Hps Hpd NE PXs PXd Hx Hy SOKd Hret H1 H10 H11.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (PIX_rd_res0 SEGS m pixs vs PXs Hx Hy) as Cres.
    eexists. split.
    - stepb_ft F_15e88 D_15e88 ltac:(condZ).
      stepb_ft F_15e8c D_15e8c ltac:(condZ).
      stepb_ft F_15e90 D_15e90 ltac:(condZ).
      sn F_15e94 D_15e94. sn F_15e98 D_15e98.
      stepLD F_15e9c D_15e9c (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Cres) ltac:(apply lez8; lia).
      stepST F_15ea0 D_15ea0 (Z_to_bv 64 (pixd + 24)) (Z_to_bv 64 0) ltac:(sok_in SOKd).
      stepret F_15ea4 D_15ea4 ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pixCopySpp_run : forall regs m (pixd pixs : Z) (vs vd : pixv) (ret : word),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> pixs <> pixd -> PIXat m pixs vs -> PIXat m pixd vd -> (1 <= p_spp vs)%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x15eb4 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (p_spp vs)))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixd pixs vs vd ret Hps Hpd NE PXs PXd Hspp SOKd Hret H1 H10 H11.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof (wf_spp _ WFs) as Rspp.
    pose proof (PIX_rd_spp SEGS _ _ _ PXs) as Cspp.
    eexists. split.
    - stepb_ft F_15db8 D_15db8 ltac:(condZ).
      stepb_ft F_15dbc D_15dbc ltac:(condZ).
      stepb_ft F_15dc0 D_15dc0 ltac:(condZ).
      stepLD F_15dc4 D_15dc4 (Z_to_le_bytes 4 (p_spp vs)) (Z_to_bv 64 (p_spp vs)) ltac:(addr_norm; exact Cspp) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_spp vs)) by lia.
      stepb_ft F_15dc8 D_15dc8 ltac:(condZ).
      sn F_15dcc D_15dcc. sn F_15dd0 D_15dd0.
      stepST F_15dd4 D_15dd4 (Z_to_bv 64 (pixd + 12)) (Z_to_bv 64 (p_spp vs)) ltac:(sok_in SOKd).
      stepret F_15dd8 D_15dd8 ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition FR2 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)).

  (* [comment removed for export] *)
  Lemma pct_A : forall regs m (s pixs : Z) (ret : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x15c44 : word) m rom) (mkst regs' (0x15cfc : word) (FR2 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x15c58 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2]%list) regs regs'.
  Proof.
    intros regs m s pixs ret Hs Hs64 Hp SOK H2 H1 H10. unfold FR2. eexists. split.
    - zv F_15b48 D_15b48 (Z_to_bv 64 (s - 16)).
      stepST F_15b4c D_15b4c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15b50 D_15b50 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepb_ft F_15b54 D_15b54 ltac:(condZ).
      sn F_15b58 D_15b58.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pct_B : forall regs m (s pixd : Z) (vd : pixv),
    (1 <= pixd)%Z -> PIXat m pixd vd -> (0 <= p_wpl vd * p_h vd)%Z -> (4 * (p_wpl vd * p_h vd) < 2 ^ 31)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x15c58 : word) m rom) (mkst regs' (0x2942c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x15c80
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl vd * p_h vd))
      /\ getr regs' 8 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pixd vd Hp PX Hwh Hsz H2 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (wf_h _ WF) as Rh. pose proof (wf_wpl _ WF) as Rwpl. pose proof (wf_data _ WF) as Rdata.
    pose proof (PIX_rd_h SEGS _ _ _ PX) as Ch. pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    eexists. split.
    - stepb_ft F_15b5c D_15b5c ltac:(condZ).
      stepLD F_15b60 D_15b60 (Z_to_le_bytes 4 (p_h vd)) (Z_to_bv 64 (p_h vd)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      stepLD F_15b64 D_15b64 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; exact Cwpl) ltac:(apply lez4; lia).
      stepLD F_15b68 D_15b68 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdata) ltac:(apply lez8; lia).
      zv F_15b6c D_15b6c (Z_to_bv 64 (p_wpl vd * p_h vd)).
      stepiv F_15b70 D_15b70 (Z_to_bv 64 (4 * (p_wpl vd * p_h vd))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_15b74 D_15b74. sn F_15b78 D_15b78. sn F_15b7c D_15b7c. sn F_15b80 D_15b80.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pct_C : forall regs m (s pixd : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 8 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x15c80 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s pixd ret s0v Hs Hs64 Hret R8 R16 H2 H8. eexists. split.
    - sn F_15b84 D_15b84. sn F_15b88 D_15b88.
      stepLD8 F_15bf0 D_15bf0 ret. stepLD8 F_15bf4 D_15bf4 s0v.
      zv F_15bf8 D_15bf8 (Z_to_bv 64 s). stepret F_15bfc D_15bfc ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pct_F : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x2aa40) 8 = Some (Z_to_le_bytes 8 0x2bab0) -> rdn SEGS m (Z_to_bv 64 0x2bab0) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x15c58 : word) m rom) (mkst regs' (0x1543c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x104bd /\ getr regs' 11 = Z_to_bv 64 0x10da4
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Rg Rs R8 R16 H2 H10. eexists. split.
    - stepb_tk F_15b5c D_15b5c ltac:(condZ).
      sn F_15bb4 D_15bb4.
      stepLD F_15bb8 D_15bb8 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_15bbc D_15bbc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_15bc0 D_15bc0. stepb_ft F_15bc4 D_15bc4 ltac:(condZ).
      sn F_15bc8 D_15bc8. sn F_15bcc D_15bcc. sn F_15bd0 D_15bd0. sn F_15bd4 D_15bd4.
      sn F_15bd8 D_15bd8.
      stepLD8 F_15bdc D_15bdc ret. stepLD8 F_15be0 D_15be0 s0v.
      zv F_15be4 D_15be4 (Z_to_bv 64 s). sn F_15be8 D_15be8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cells2 (m : word -> option byte) (s : Z) (ret s0v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v).
Lemma cells2_FR2 : forall m s ret regs, (16 <= s)%Z -> (s < 2 ^ 64)%Z -> cells2 (FR2 m s ret regs) s ret (getr regs 8).
Proof. intros m s ret regs Hs Hs64. unfold cells2, FR2. repeat split; rdn_solve. Qed.
Lemma cells2_frm : forall C s' m m' s ret s0v, Cok C -> FRM C s' m m' ->
  (s' <= s - 16)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z -> cells2 m s ret s0v -> cells2 m' s ret s0v.
Proof.
  intros C s' m m' s ret s0v CK F Hs' Hlo Hs64 (R1 & R2). unfold cells2.
  rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
Qed.
Lemma cells2_out : forall m m' (lo hi s : Z) ret s0v,
  (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 16 \/ s <= lo)%Z -> (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells2 m s ret s0v -> cells2 m' s ret s0v.
Proof.
  intros m m' lo hi s ret s0v OUT Hhi Hs Hs64 (R1 & R2). unfold cells2.
  repeat split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption]).
Qed.

#[local] Definition ct_rest : list (bv 5) := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma pct_tail_W : forall C A A1 m md m2 vm1 regs r2 (s pixd w h d cd data : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> TKs C A m md regs s w h d cv ret S kR bR ->
  aroom A1 vm1 (kR - RK_pixcopy) (bR - RB_pixcopy14) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 16 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A1 m2 (with_vmmaps vm1 md) -> POSTM C A s m m2 ->
  cells2 m2 s ret (getr regs 8) ->
  getr r2 2 = Z_to_bv 64 (s - 16) -> getr r2 10 = Z_to_bv 64 pixd ->
  (forall x, In x ct_rest -> getr r2 x = getr regs x) -> getr regs 2 = Z_to_bv 64 s ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  pixt_new C A A1 m2 pixd w h d cd data cv ->
  realizes SEGS (mkCfg (mkst r2 (0x15c58 : word) m2 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C A A1 m md m2 vm1 regs r2 s pixd w h d cd data cv ret S kR bR CK HK Hrm1 Hs16 Hlo Hhi Hret HWa PMa' CE2 E2 Hres RR H2 HOK Hw Hh PT.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  set (n := (4 * (wpl_of w d * h))%Z) in *. assert (En : n = (4 * (wpl_of w d * h))%Z) by reflexivity.
  assert (Hn1 : (1 <= n)%Z) by (rewrite En; nia).
  pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). rewrite <- En in TOPd, L1d.
  assert (SUBa : sub_live A A1).
  { intros q k Lq. destruct CMR as [[_ LEQ] | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LAcd & LAad & _ & _ & _ & _ & _ & LEQ)].
    - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence].
    - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence | intros ->; congruence | intros ->; congruence]. }
  destruct (pct_B al_rom r2 m2 s pixd (hdv w h d cd data) ltac:(lia) PXd ltac:(cbn; lia) ltac:(cbn; lia) E2 Hres)
    as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & AG3). cbn [p_data p_wpl p_h hdv] in V10, V12. rewrite <- En in V12.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  (* [comment removed for export] *)
  pose proof (blk_sok C A1 m2 _ data n CK HWa L1d ltac:(lia) ltac:(lia) ltac:(lia)) as SOKd.
  destruct (memset_spec r3 m2 al_rom data n (Z_to_bv 64 0x15c80) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12)
    as (r4 & RUN4 & W10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |].
  replace (Z_to_bv 64 0x15c80) with (0x15c80 : word) by (apply bv_eq; reflexivity).
  set (M5 := zf m2 data [(0, n)]%Z).
  assert (OUT5 : forall x : word, (u x < data \/ data + n <= u x)%Z -> M5 x = m2 x).
  { intros x Hx. subst M5. apply zf_outside. apply inzr_falseP. cbn [inzrP]. lia. }
  assert (CH : forall a, M5 a <> m2 a -> scratch C s a \/ (exists p k, live A1 p = Some k /\ live A p = None /\ (u p <= u a < u p + k)%Z)).
  { intros a NE. right. exists (Z_to_bv 64 data), n. rewrite u_Z2bv by lia. split; [exact L1d | split; [exact L0d|]].
    destruct (Z_lt_ge_dec (u a) data); [exfalso; apply NE; apply OUT5; lia|].
    destruct (Z_lt_ge_dec (u a) (data + n)); [lia | exfalso; apply NE; apply OUT5; lia]. }
  assert (HW5 : W C A1 M5 (with_vmmaps vm1 md)).
  { apply (W_local C A1 m2 _ M5 s CK HWa Hhi); [| subst M5; apply zf_grows].
    intros a NE. destruct (CH a NE) as [X|(p & k & L & _ & R)]; [left; exact X | right; exists p, k]. split; [exact L | split; [| exact R]].
    destruct (bv_eq_dec _ p (Z_to_bv 64 data)) as [->|NE']; [exact L00d|].
    exfalso. apply NE. apply OUT5.
    pose proof (ai_live_disjoint A1 m2 _ _ _ _ _ (w_inv _ _ _ _ HWa) L L1d NE') as D. rewrite u_Z2bv in D by lia.
    pose proof (ai_live_hull A1 m2 _ _ _ (w_inv _ _ _ _ HWa) L) as (Hn0 & _). pose proof (round16_ge k Hn0).
    pose proof (round16_ge n ltac:(lia)). lia. }
  assert (PM5 : POSTM C A s m M5) by (eapply POSTM_trans; [exact PMa' | exact (POSTM_local C A A1 m2 _ M5 s CK HWa SUBa CH)]).
  assert (EQ5 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 data -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z -> (p <= u x < p + k)%Z -> M5 x = m2 x).
  { intros p k x L NE' G0 K0 Hx. apply OUT5.
    pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa L L1d NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. lia. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  assert (PXd5 : PIXat M5 pixd (hdv w h d cd data)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; exact (EQ5 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) Hx)]).
  assert (CE5 : cells2 M5 s ret (getr regs 8)).
  { destruct CE2 as (C1 & C2). unfold cells2.
    repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT5; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]). }
  destruct CE5 as (C1 & C2).
  destruct (pct_C al_rom r4 M5 s pixd ret _ ltac:(lia) ltac:(lia) Hret C1 C2 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r5 & RUN5 & Z2 & Z1 & Z10 & Z8 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN5 |].
  apply (HK A1 M5 vm1 r5 HW5).
  - apply cs_kept_intro; csr; try reflexivity. all: unfold ct_rest in RR; csr; reflexivity.
  - exact PM5.
  - exists pixd, cd, data. split; [exact Z10|].
    unfold pixt_new. rewrite <- En. do 13 (split; [assumption|]). split; [exact PXd5|].
    destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)]; [left; split; [exact CD0 | exact LEQ] | right].
    exists ad. do 16 (split; [assumption|]). split; [| exact LEQ].
    assert (NEw1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    apply (CMAPat_frame m2); [exact CM4|]. intros x Hx. exact (EQ5 cd 24%Z x L2cd NEw1 ltac:(lia) ltac:(lia) Hx).
  - exact Hrm1.
Qed.

(* [comment removed for export] *)
Theorem pixCreateTemplate_gsure_W : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PCT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB_pixcopy14 <= bR)%Z ->
  TKs C A m md regs s w h d cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x15c44 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold PCT_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (pct_A al_rom regs m s pixs ret ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR2 m s ret regs) md /\ POSTM C A s m (FR2 m s ret regs)) by (unfold FR2; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR2 m s ret regs) in *.
  pose proof (cells2_FR2 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 16 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (hdv w h d cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  apply (pixCreateTemplateNoInit_sure_W C A M1 md r1 (s - 16) pixs w h d cm datas cv (Z_to_bv 64 0x15c58) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw Hh Lps HCM1 kR bR Hrm Hrk Hrb).
  unfold TKs. intros A1 m2 vm1 r2 HWa CSa PMa (pixd & cd & data & Hres & PT) Hrm1.
  replace (Z_to_bv 64 0x15c58) with (0x15c58 : word) by (apply bv_eq; reflexivity).
  pose proof (cells2_frm C (s - 16) M1 m2 s _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  apply (pct_tail_W C A A1 m md m2 vm1 regs r2 s pixd w h d cd data cv ret S kR bR CK HK Hrm1 Hs16 ltac:(lia) Hhi Hret HWa PMa' CE2
           ltac:(csr; reflexivity) Hres ltac:(unfold ct_rest; rest_solve) H2 HOK Hw Hh PT).
Qed.

(* [comment removed for export] *)
Theorem pixCreateTemplate_sure_W : pixCreateTemplate_sure_contract RK_pixcopy RB_pixcopy14.
Proof.
  unfold pixCreateTemplate_sure_contract, PC_pixCreateTemplate, TP14.
  intros C A m md regs s pixs w h d datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps kR bR Hrm Hrk Hrb HK.
  replace (Z_to_bv 64 0x15c44) with (0x15c44 : word) by (apply bv_eq; reflexivity).
  apply (pixCreateTemplate_gsure_W C A m md regs s pixs w h d 0 datas (CMAPV 0 0 0 0 0) ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps
           (or_introl eq_refl) kR bR Hrm Hrk Hrb).
  unfold TKs. intros A' m' vm' regs' HW' CS' PM' (pixd & cd & data & Hres & PT) Hrm'.
  apply (HK A' m' vm' regs' pixd data HW' CS' PM' Hres); [| exact Hrm'].
  destruct PT as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & PXd & CMR).
  destruct CMR as [[CD0 LEQ] | (ad & CMOKc & _)].
  - subst cd. unfold pixt_new. do 13 (split; [assumption|]). split; [exact PXd|]. left. split; [reflexivity | exact LEQ].
  - exfalso. destruct CMOKc as (Hd & _). cbn in Hd. lia.
Qed.

(* [comment removed for export] *)
Theorem pixCreateTemplate_W : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PCT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB_pixcopy14 <= bR)%Z ->
  TK C A m md regs s w h d cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x15c44 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold PCT_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (pct_A al_rom regs m s pixs ret ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR2 m s ret regs) md /\ POSTM C A s m (FR2 m s ret regs)) by (unfold FR2; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR2 m s ret regs) in *.
  pose proof (cells2_FR2 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 16 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (hdv w h d cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  apply (pixCreateTemplateNoInit_W C A M1 md r1 (s - 16) pixs w h d cm datas cv (Z_to_bv 64 0x15c58) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw Hh Lps HCM1 kR bR Hrm Hrk Hrb).
  unfold TK. intros A1 m2 vm1 r2 HWa CSa PMa OUTa Hrm1.
  replace (Z_to_bv 64 0x15c58) with (0x15c58 : word) by (apply bv_eq; reflexivity).
  pose proof (cells2_frm C (s - 16) M1 m2 s _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & cd & data & Hres & PT)].
  - (* [comment removed for export] *)
    destruct CE2 as (C1 & C2).
    destruct (pct_F al_rom r2 m2 s ret _ ltac:(lia) ltac:(lia) (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) C1 C2 ltac:(csr; reflexivity) Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m2 _ r3 s 0x104bd 0x10da4 13 17 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd str_pixCreateTemplate).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m2 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + exact Hrm1.
  - apply (pct_tail_W C A A1 m md m2 vm1 regs r2 s pixd w h d cd data cv ret S kR bR CK
             (fun A' m' vm' regs' X1 X2 X3 X4 X5 => HK A' m' vm' regs' X1 X2 X3 (or_intror X4) X5)
             Hrm1 Hs16 ltac:(lia) Hhi Hret HWa PMa' CE2 ltac:(csr; reflexivity) Hres ltac:(unfold ct_rest; rest_solve) H2 HOK Hw Hh PT).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem pixDestroy_keep_W : forall C A m md regs (s pp pix R : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = 0%Z ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  live A (Z_to_bv 64 (p_data v)) = Some R -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None -> (0 < R)%Z -> p_data v <> pix ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 pix) = None -> live A' (Z_to_bv 64 (p_data v)) = None ->
     (forall q, q <> Z_to_bv 64 pix -> q <> Z_to_bv 64 (p_data v) -> live A' q = live A q) ->
     POSTM C A' (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15b78 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix R v ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 H10 Rpp PX Hrc Ht Hc Lp L0p LR LR0 HR NEdp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold ALLOC_STACK in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) R CK HW LR HR) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (SOKp : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix v x PX ltac:(lia) E). }
  destruct (pxd_A al_rom regs m s pp pix v ret ltac:(lia) Hpp ltac:(lia) ALp (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia))
              SOKp Rpp PX Hrc ltac:(lia) Gp H2 H1 H10) as (r1 & RUN1 & Q2 & Q8 & Q9 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C A s m M0) by (subst M0; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (HW1 : W C A M1 md).
  { subst M1. apply (W_store_blk C A M0 md (Z_to_bv 64 pix) _ 64 _ CK HW0 Lp L0p); [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  assert (F1 : FRM C s m M1).
  { eapply FRM_trans; [exact (proj1 PM0)|]. subst M1.
    refine (proj1 (POSTM_blk C (c_A0 C) A M0 md (Z_to_bv 64 pix) _ 64 _ s CK HW0 Lp L0p (W_sub0 _ _ _ _ HW0) _ _));
      [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  assert (K1 : forall q k i, live A q = Some k -> q <> Z_to_bv 64 pix -> (0 <= i < k)%Z -> M1 (at_ q i) = m (at_ q i)).
  { intros q k i Lq NEq Hi. rewrite <- (proj2 PM0 q k i Lq Hi). subst M1.
    pose proof (blk_apart C A m md _ _ _ _ CK HW Lq Lp NEq ltac:(lia) ltac:(lia)) as D. rewrite u_Z2bv in D by lia.
    destruct (blk_range C A m md q k CK HW Lq ltac:(lia)) as [Gq TOPq].
    apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; [cbn; lia|]. unfold at_. pose proof (u64_range q). rewrite u_Z2bv by lia. cbn. lia. }
  assert (PX1 : PIXat M1 pix (set_rc v 0)).
  { subst M1. apply PIX_wr_rc; [|lia]. subst M0.
    repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (R8 : rdn SEGS M1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (subst M1 M0; rdn_solve).
  assert (R16 : rdn SEGS M1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (subst M1 M0; rdn_solve).
  assert (R24 : rdn SEGS M1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (subst M1 M0; rdn_solve).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
  assert (ER1 : forall r, In r cs_rest -> getr r1 r = getr regs r).
  { intros r Hr. apply AG1. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr. }
  (* [comment removed for export] *)
  destruct (pxd_B1 al_rom r1 M1 (p_data v) ltac:(lia) ltac:(lia) (W_pmm_free C A M1 md HW1) Q10) as (r2 & RUN2 & P10 & P1 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  assert (P4 : getr r2 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
  assert (P2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x21ef4 : word) with (Z_to_bv 64 0x21ef4) by (apply bv_eq; reflexivity).
  apply (W_free16 C A M1 md r2 (Z_to_bv 64 (p_data v)) (Z_to_bv 64 0x15bc0) R (s - 32) S CK HW1 P10 LR LR0 P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r3 HWa CSa La LEQa PMa HRTa.
  replace (Z_to_bv 64 0x15bc0) with (0x15bc0 : word) by (apply bv_eq; reflexivity).
  assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
  assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (LEQa _ NEpd); exact Lp).
  assert (PXa : PIXat m1 pix (set_rc v 0)).
  { apply (PIXat_frame M1); [exact PX1|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 pix) 64%Z (u x - pix)%Z Lp1 ltac:(lia)) as E.
    unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
  assert (E2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8 : getr r3 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  assert (E9 : getr r3 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (E4 : getr r3 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
  (* [comment removed for export] *)
  destruct (pxd_C0 al_rom r3 m1 s pix (set_rc v 0) ltac:(lia) ltac:(lia) PXa ltac:(cbn; exact Ht) ltac:(cbn; exact Hc)
              (W_sok_win C A1 m1 _ (s - 32) 32 CK HWa ltac:(lia) ltac:(cbn; lia)) ltac:(lia) E2 E8) as (r4 & RUN4 & X2 & X8 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |].
  set (M2 := wbytes m1 _ _).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  assert (X9 : getr r4 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (X4 : getr r4 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
  (* [comment removed for export] *)
  destruct (pxd_D al_rom r4 M2 pix X8) as (r5 & RUN5 & Y10 & Y1 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  assert (Y4 : getr r5 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
  assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x21ef4 : word) with (Z_to_bv 64 0x21ef4) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 M2 _ r5 (Z_to_bv 64 pix) (Z_to_bv 64 0x15bec) 64 (s - 32) S CK HW2 Y10 Lp1 L0p Y1
           ltac:(red; apply bv_eq; reflexivity) Y4 Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r6 HWb CSb Lb LEQb PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
  replace (Z_to_bv 64 0x15bec) with (0x15bec : word) by (apply bv_eq; reflexivity).
  assert (Z2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (Z9 : getr r6 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (FR12 : FRM C s m m2).
  { eapply FRM_trans; [exact F1|]. eapply FRM_trans; [eapply FRM_mono; [exact (proj1 PMa) | lia]|].
    eapply FRM_trans; [exact (proj1 PM2) | eapply FRM_mono; [exact (proj1 PMb) | lia]]. }
  destruct (pxd_E al_rom r6 m2 s pp ret (getr regs 8) (getr regs 9) ltac:(lia) Hpp ltac:(lia) Hret) as (r7 & RUN7 & V2 & V1 & V8 & V9 & AG7).
  { apply (W_sok_win C A2 m2 _ pp 8 CK HWb); [lia | cbn; lia]. }
  { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 8) 8 CK (proj1 PMb)) by (cbn; lia). subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). exact R8. }
  { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 16) 8 CK (proj1 PMb)) by (cbn; lia). subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact R16. }
  { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 24) 8 CK (proj1 PMb)) by (cbn; lia). subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact R24. }
  { exact Z2. } { exact Z9. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN7 |].
  set (M3 := wbytes m2 _ _).
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A2 (pp + 8) m2 M3) by (subst M3; wp_win CK).
  destruct WP3 as [HW3 PM3].
  assert (NEdp' : Z_to_bv 64 (p_data v) <> Z_to_bv 64 pix) by (intros E; apply NEpd; rewrite E; reflexivity).
  assert (Ld2 : live A2 (Z_to_bv 64 (p_data v)) = None) by (rewrite (LEQb _ NEdp'); exact La).
  apply (HK A2 M3 vm2 r7 HW3).
  - apply cs_kept_of_rest; [rewrite V2, H2; reflexivity | exact V8 | exact V9 |].
    intros r Hr. rewrite (AG7 r) by (cbn [In cs_rest] in Hr; repeat (destruct Hr as [<-|Hr]; [notin_lit|]); destruct Hr).
    rewrite (cs_rest_of_kept _ _ CSb r Hr). rewrite (AG5 r) by (cbn [In cs_rest] in Hr; repeat (destruct Hr as [<-|Hr]; [notin_lit|]); destruct Hr).
    rewrite (AG4 r) by (cbn [In cs_rest] in Hr; repeat (destruct Hr as [<-|Hr]; [notin_lit|]); destruct Hr).
    rewrite (cs_rest_of_kept _ _ CSa r Hr). rewrite (AG2 r) by (cbn [In cs_rest] in Hr; repeat (destruct Hr as [<-|Hr]; [notin_lit|]); destruct Hr).
    exact (ER1 r Hr).
  - exact Lb.
  - exact Ld2.
  - intros q N1 N2. rewrite (LEQb q N1). exact (LEQa q N2).
  - split; [eapply FRM_trans; [eapply FRM_mono; [exact FR12 | lia] | exact (proj1 PM3)]|].
    intros q k i Lq Hi.
    assert (N1 : q <> Z_to_bv 64 pix) by (intros ->; congruence).
    assert (N2 : q <> Z_to_bv 64 (p_data v)) by (intros ->; congruence).
    assert (Lq1 : live A1 q = Some k) by (rewrite <- (LEQb q N1); exact Lq).
    assert (Lq0 : live A q = Some k) by (rewrite <- (LEQa q N2); exact Lq1).
    rewrite (proj2 PM3 q k i Lq Hi). rewrite (proj2 PMb q k i Lq Hi). rewrite (proj2 PM2 q k i Lq1 Hi). rewrite (proj2 PMa q k i Lq1 Hi).
    exact (K1 q k i Lq0 N1 Hi).
  - subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - intros a Ha. subst M3. rewrite (wbytes_out_Z _ _ 8); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia].
    destruct (win_facts C a CK ltac:(unfold win; lia)) as (_ & Ga & N2 & N3 & N4 & _).
    apply FR12; try assumption; [intros [_ X]; lia | unfold scratch; lia].
  - room_tac.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pix_fresh (C : lctx) (A A' : AS) (m' : word -> option byte) (pixd w h d data : Z) : Prop :=
  (4096 <= pixd)%Z /\ (pixd + 64 <= alloc_top (c_vm C))%Z /\ (pixd mod 16 = 0)%Z /\
  (4096 <= data)%Z /\ (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z /\ (data mod 16 = 0)%Z /\ pixd <> data /\
  live A (Z_to_bv 64 pixd) = None /\ live A (Z_to_bv 64 data) = None /\
  live (c_A0 C) (Z_to_bv 64 pixd) = None /\ live (c_A0 C) (Z_to_bv 64 data) = None /\
  live A' (Z_to_bv 64 pixd) = Some 64%Z /\ live A' (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z /\
  (forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> live A' q = live A q) /\
  PIXat m' pixd (hdv w h d 0 data).

Lemma pixt_new_fresh : forall C A A' m' pixd w h d data cv, pixt_new C A A' m' pixd w h d 0 data cv -> pix_fresh C A A' m' pixd w h d data.
Proof.
  intros C A A' m' pixd w h d data cv (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & PXd & CMR).
  unfold pix_fresh. repeat (split; [assumption|]). split; [| exact PXd].
  destruct CMR as [[_ LEQ] | (ad & _ & G & _)]; [exact LEQ | exfalso; lia].
Qed.

Lemma pix_fresh_sub : forall C A A' m' pixd w h d data, pix_fresh C A A' m' pixd w h d data -> sub_live A A'.
Proof.
  intros C A A' m' pixd w h d data (_ & _ & _ & _ & _ & _ & _ & L0p & L0d & _ & _ & L1p & L1d & LEQ & _).
  exact (sub_live_new2 A A' _ _ _ _ L0p L0d L1p L1d LEQ).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pixAddBorderGeneral_contract : Prop :=
  forall C A m md regs (s pixs w h d datas left right top bot val : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
  getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 val ->
  PIXat m pixs (hdv w h d 0 datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 8)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z -> ((left * d) mod 32 = 0)%Z ->
  (val = 0 \/ val = 2 ^ d - 1)%Z -> ((w + left + right) * (h + top + bot) <= 400000000)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB_pixcopy14 <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (w + left + right) (h + top + bot) d /\
                             pix_fresh C A A' m' pixd (w + left + right) (h + top + bot) d data) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB_pixcopy14) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixAddBorderGeneral) m al_rom) md) S.

Definition pixRemoveBorderGeneral_contract : Prop :=
  forall C A m md regs (s pixs w h d datas left right top bot : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RBG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
  getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
  PIXat m pixs (hdv w h d 0 datas) -> hdr_ok w h d -> (d = 1 \/ d = 8)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z -> ((left * d) mod 32 = 0)%Z ->
  (1 <= w - left - right)%Z -> (1 <= h - top - bot)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB_pixcopy14 <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (w - left - right) (h - top - bot) d /\
                             pix_fresh C A A' m' pixd (w - left - right) (h - top - bot) d data) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB_pixcopy14) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRemoveBorderGeneral) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixRemoveBorderGeneral_null_contract : Prop :=
  forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RBG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRemoveBorderGeneral) m al_rom) md) S.

End GrayA.
