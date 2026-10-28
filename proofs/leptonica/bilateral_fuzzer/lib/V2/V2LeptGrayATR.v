(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptUb V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptPixDestroy V2LeptCmapValid V2LeptCmap2 V2LeptPixCreateT2 V2LeptPixCopyA V2LeptPixCopyAT V2LeptPixCopyTR V2MemcpyBase V2Memcpy V2Memset V2_code_pixCreateTemplate V2_code_pixCopyResolution.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition PC_pixAddBorderGeneral : Z := 0x1c144.
Definition PCT_STACK : Z := 16 + 128 + 16 + LSF.     (* [comment removed for export] *)
Definition PC_pixDestroy : Z := 0x1982c.
Definition ABG_STACK : Z := 128 + 112 + LSF.      (* [comment removed for export] *)
Definition RBG_STACK : Z := 96 + 112 + LSF.       (* [comment removed for export] *)

Section GrayA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pixCopyResolution_run : forall regs m (pixd pixs : Z) (vs vd : pixv) (ret : word),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> pixs <> pixd -> (pixs mod 8 = 0)%Z -> (pixd mod 8 = 0)%Z ->
    PIXat m pixs vs -> PIXat m pixd vd -> p_xres vs = 0%Z -> p_yres vs = 0%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x19bf4 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixd pixs vs vd ret Hps Hpd NE ALs ALd PXs PXd Hx Hy SOK Hret H1 H10 H11.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (PIX_rd_res0 SEGS m pixs vs PXs Hx Hy) as Cres.
    eexists. split.
    - stepb_ft F_19bf4 D_19bf4 ltac:(condZ).
      stepb_ft F_19bf8 D_19bf8 ltac:(condZ).
      stepb_ft F_19bfc D_19bfc ltac:(condZ).
      guard8 F_19c00 D_19c00 ALs. stepb_ft F_19c04 D_19c04 ltac:(condZ).
      guard8 F_19c08 D_19c08 ALd. stepb_ft F_19c0c D_19c0c ltac:(condZ).
      stepLD F_19c10 D_19c10 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Cres) ltac:(apply lez8; lia).
      stepST F_19c14 D_19c14 (Z_to_bv 64 (pixd + 24)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zv F_19c18 D_19c18 (Z_to_bv 64 0).
      stepret F_19c1c D_19c1c ret ltac:(pin; reflexivity).
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
      msteps SEGS (mkst regs (0x1990c : word) m rom) (mkst regs' (0x199dc : word) (FR2 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x19920 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2]%list) regs regs'.
  Proof.
    intros regs m s pixs ret Hs Hs64 Hp SOK H2 H1 H10. unfold FR2. eexists. split.
    - zv F_1990c D_1990c (Z_to_bv 64 (s - 16)).
      stepST F_19910 D_19910 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_19914 D_19914 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepb_ft F_19918 D_19918 ltac:(condZ).
      sn F_1991c D_1991c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pct_B : forall regs m (s pixd : Z) (vd : pixv),
    (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (0 <= p_wpl vd * p_h vd)%Z -> (4 * (p_wpl vd * p_h vd) < 2 ^ 31)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x19920 : word) m rom) (mkst regs' (0x43880 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x1995c
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl vd * p_h vd))
      /\ getr regs' 8 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pixd vd Hp ALd PX Hwh Hsz H2 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (wf_h _ WF) as Rh. pose proof (wf_wpl _ WF) as Rwpl. pose proof (wf_data _ WF) as Rdata.
    assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd).
    assert (Hm4 : (0 <= 4 * p_wpl vd * p_h vd < 2 ^ 31)%Z) by nia.
    pose proof (PIX_rd_h SEGS _ _ _ PX) as Ch. pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    eexists. split.
    - stepb_ft F_19920 D_19920 ltac:(condZ).
      guard8 F_19924 D_19924 ALd8. stepb_ft F_19928 D_19928 ltac:(condZ).
      stepLD F_1992c D_1992c (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; exact Cwpl) ltac:(apply lez4; lia).
      stepLD F_19930 D_19930 (Z_to_le_bytes 4 (p_h vd)) (Z_to_bv 64 (p_h vd)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      stepiv F_19934 D_19934 (Z_to_bv 64 (4 * p_wpl vd)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_19938 D_19938. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_1993c D_1993c (Z_to_bv 64 (4 * (p_wpl vd * p_h vd))).
      sn F_19940 D_19940. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_19944 D_19944 ltac:(condZ).
      stepLD F_19948 D_19948 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdata) ltac:(apply lez8; lia).
      sn F_1994c D_1994c. sn F_19950 D_19950. zv F_19954 D_19954 (Z_to_bv 64 0). sn F_19958 D_19958.
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
      msteps SEGS (mkst regs (0x1995c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s pixd ret s0v Hs Hs64 Hret R8 R16 H2 H8. eexists. split.
    - sn F_1995c D_1995c. sn F_19960 D_19960.
      stepLD8 F_199c8 D_199c8 ret. stepLD8 F_199cc D_199cc s0v.
      zv F_199d0 D_199d0 (Z_to_bv 64 s). stepret F_199d4 D_199d4 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pct_F : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x19920 : word) m rom) (mkst regs' (0x17ec4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10765 /\ getr regs' 11 = Z_to_bv 64 0x117e8
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s ret s0v Hs Hs64 Rg Rs R8 R16 H2 H10. eexists. split.
    - stepb_tk F_19920 D_19920 ltac:(condZ).
      sn F_1998c D_1998c.
      stepLD F_19990 D_19990 (Z_to_le_bytes 8 0x45f08) (Z_to_bv 64 0x45f08) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_19994 D_19994 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_19998 D_19998. stepb_ft F_1999c D_1999c ltac:(condZ).
      sn F_199a0 D_199a0. sn F_199a4 D_199a4. sn F_199a8 D_199a8. sn F_199ac D_199ac.
      sn F_199b0 D_199b0.
      stepLD8 F_199b4 D_199b4 ret. stepLD8 F_199b8 D_199b8 s0v.
      zv F_199bc D_199bc (Z_to_bv 64 s). sn F_199c0 D_199c0.
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
  rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). split; assumption.
Qed.
Lemma cells2_out : forall m m' (lo hi s : Z) ret s0v,
  (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 16 \/ s <= lo)%Z -> (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells2 m s ret s0v -> cells2 m' s ret s0v.
Proof.
  intros m m' lo hi s ret s0v OUT Hhi Hs Hs64 (R1 & R2). unfold cells2.
  split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption]).
Qed.

#[local] Definition ct_rest : list (bv 5) := [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition TKs (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h d cm : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h d cd data cv) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w d * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

(* [comment removed for export] *)
Lemma pct_tail_W : forall C A A1 m md m2 vm1 regs r2 (s pixd w h d cm cd data : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> TKs C A m md regs s w h d cm cv ret S kR bR ->
  aroom A1 vm1 (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w d * h)) + RB_cmapT cm)) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 16 <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A1 m2 (with_vmmaps vm1 md) -> POSTM C A s m m2 ->
  cells2 m2 s ret (getr regs 8) ->
  getr r2 2 = Z_to_bv 64 (s - 16) -> getr r2 10 = Z_to_bv 64 pixd ->
  (forall x, In x ct_rest -> getr r2 x = getr regs x) -> getr regs 2 = Z_to_bv 64 s ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  pixt_new C A A1 m2 pixd w h d cd data cv ->
  realizes SEGS (mkCfg (mkst r2 (0x19920 : word) m2 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C A A1 m md m2 vm1 regs r2 s pixd w h d cm cd data cv ret S kR bR CK HK Hrm1 Hs16 Hlo Hhi Hret HW2 PM2 CE2 R2 R10 RR H2 HOK Hw Hh PT.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  set (n := (4 * (wpl_of w d * h))%Z) in *. assert (En : n = (4 * (wpl_of w d * h))%Z) by reflexivity. clearbody n.
  pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). rewrite <- En in TOPd, L1d.
  assert (SUBa : sub_live A A1).
  { intros q k Lq. destruct CMR as [[_ LEQ] | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LAcd & LAad & _ & _ & _ & _ & _ & LEQ)].
    - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence].
    - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence | intros ->; congruence | intros ->; congruence]. }
  assert (Hn1 : (4 <= n)%Z) by (rewrite En; nia).
  destruct (pct_B al_rom r2 m2 s pixd (hdv w h d cd data) ltac:(lia) ALp PXd ltac:(cbn; nia) ltac:(cbn; lia) R2 R10)
    as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & AG3). cbn [p_data p_wpl p_h hdv] in V10, V12. rewrite <- En in V12.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  pose proof (blk_sok C A1 m2 _ data n CK HW2 L1d ltac:(lia) ltac:(lia) ltac:(lia)) as SOKd.
  destruct (memset_spec r3 m2 al_rom data n (Z_to_bv 64 0x1995c) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12)
    as (r4 & RUN4 & W10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
  replace (Z_to_bv 64 0x1995c) with (0x1995c : word) by (apply bv_eq; reflexivity).
  set (M5 := zf m2 data [(0, n)]%Z).
  assert (OUT5 : forall x : word, (u x < data \/ data + n <= u x)%Z -> M5 x = m2 x).
  { intros x Hx. subst M5. apply zf_outside. apply inzr_falseP. cbn [inzrP]. lia. }
  assert (CH : forall a, M5 a <> m2 a -> scratch C s a \/ (exists p k, live A1 p = Some k /\ live A p = None /\ (u p <= u a < u p + k)%Z)).
  { intros a NE. right. exists (Z_to_bv 64 data), n. rewrite u_Z2bv by lia. split; [exact L1d | split; [exact L0d|]].
    destruct (Z_lt_ge_dec (u a) data); [exfalso; apply NE; apply OUT5; lia|].
    destruct (Z_lt_ge_dec (u a) (data + n)); [lia | exfalso; apply NE; apply OUT5; lia]. }
  assert (HW5 : W C A1 M5 (with_vmmaps vm1 md)).
  { apply (W_local C A1 m2 _ M5 s CK HW2 Hhi); [| subst M5; apply zf_grows].
    intros a NE. destruct (CH a NE) as [X|(p & k & L & _ & R)]; [left; exact X | right; exists p, k]. split; [exact L | split; [| exact R]].
    destruct (bv_eq_dec _ p (Z_to_bv 64 data)) as [->|NE']; [exact L00d|].
    exfalso. apply NE. apply OUT5.
    pose proof (ai_live_disjoint A1 m2 _ _ _ _ _ (w_inv _ _ _ _ HW2) L L1d NE') as D. rewrite u_Z2bv in D by lia.
    pose proof (ai_live_hull A1 m2 _ _ _ (w_inv _ _ _ _ HW2) L) as (Hn0 & _). pose proof (round16_ge k Hn0).
    pose proof (round16_ge n ltac:(lia)). lia. }
  assert (PM5 : POSTM C A s m M5) by (eapply POSTM_trans; [exact PM2 | exact (POSTM_local C A A1 m2 _ M5 s CK HW2 SUBa CH)]).
  assert (EQ5 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 data -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z -> (p <= u x < p + k)%Z -> M5 x = m2 x).
  { intros p k x L NE' G0 K0 Hx. apply OUT5.
    pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HW2 L L1d NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. lia. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  assert (PXd5 : PIXat M5 pixd (hdv w h d cd data)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; exact (EQ5 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) Hx)]).
  assert (CE5 : cells2 M5 s ret (getr regs 8)).
  { destruct CE2 as (C1 & C2). unfold cells2.
    repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT5; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]). }
  assert (X2 : getr r4 2 = Z_to_bv 64 (s - 16)) by (rewrite (AG4 2) by (cbv; intuition discriminate); exact V2).
  assert (X8 : getr r4 8 = Z_to_bv 64 pixd) by (rewrite (AG4 8) by (cbv; intuition discriminate); exact V8).
  destruct CE5 as (C1 & C2).
  destruct (pct_C al_rom r4 M5 s pixd ret (getr regs 8) ltac:(lia) ltac:(lia) Hret C1 C2 X2 X8) as (r5 & RUN5 & Z2 & Z1 & Z10 & Z8 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN5 |].
  apply (HK A1 M5 vm1 r5 HW5).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8; try reflexivity. all: unfold ct_rest in RR; csr; reflexivity.
  - exact PM5.
  - exists pixd, cd, data. split; [exact Z10|].
    unfold pixt_new. rewrite <- En. do 13 (split; [assumption|]). split; [exact PXd5|].
    destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)]; [left; split; [exact CD0 | exact LEQ] | right].
    exists ad. do 16 (split; [assumption|]). split; [| exact LEQ].
    assert (NEw1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    apply (CMAPat_frame m2); [exact CM4|]. intros x Hx. exact (EQ5 cd 24%Z x L2cd NEw1 ltac:(lia) ltac:(lia) Hx).
  - rewrite <- En. exact Hrm1.
Qed.

(* [comment removed for export] *)
Theorem pixCreateTemplate_szTR_W : forall C A m md regs (s pixs rc w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PCT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdvr rc w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w d * h)) + RB_cmapT cm) <= bR)%Z ->
  TK C A m md regs s w h d cm cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x1990c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs rc w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold PCT_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (pct_A al_rom regs m s pixs ret ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR2 m s ret regs) md /\ POSTM C A s m (FR2 m s ret regs)) by (unfold FR2; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR2 m s ret regs) in *.
  pose proof (cells2_FR2 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 16 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (hdvr rc w h d cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
    pose proof CM as (Hc0 & Hc64 & _).
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  apply (pixCreateTemplateNoInit_szTR_W C A M1 md r1 (s - 16) pixs rc w h d cm datas cv (Z_to_bv 64 0x19920) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10
           PXs1 HOK Hw Hh Lps HCM1 kR bR Hrm Hrk Hrb).
  intros A1 m2 vm1 r2 HWa CSa PMa OUTa Hrm1.
  replace (Z_to_bv 64 0x19920) with (0x19920 : word) by (apply bv_eq; reflexivity).
  pose proof (cells2_frm C (s - 16) M1 m2 s _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & cd & data & Hres & PT)].
  - destruct CE2 as (C1 & C2).
    destruct (pct_F al_rom r2 m2 s ret _ ltac:(lia) ltac:(lia) (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) C1 C2 E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m2 _ r3 s 0x10765 0x117e8 13 17 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd str_pixCreateTemplate).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8; reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m2 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + exact Hrm1.
  - assert (RR : forall x, In x ct_rest -> getr r2 x = getr regs x) by (unfold ct_rest; rest_solve).
    assert (HKs : TKs C A m md regs s w h d cm cv ret S kR bR).
    { intros A' m' vm' regs' HW' CS' PM' (pixd' & cd' & data' & R' & PN') Hr'.
      apply (HK A' m' vm' regs' HW' CS' PM'); [right; exists pixd', cd', data'; split; assumption | exact Hr']. }
    exact (pct_tail_W C A A1 m md m2 vm1 regs r2 s pixd w h d cm cd data cv ret S kR bR CK HKs Hrm1 Hs16 ltac:(lia) Hhi Hret HWa PMa' CE2 E2 Hres RR H2 HOK Hw Hh PT).
Qed.

(* [comment removed for export] *)

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
  intros C A A' m' pixd w h d data cv (Gp & TOPp & ALp & Gd & TOPd & ALd & NE & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR).
  unfold pix_fresh. do 13 (split; [assumption|]). split; [| exact PXd].
  destruct CMR as [[_ LEQ] | (ad & _ & Gcd & _)]; [exact LEQ | lia].
Qed.

Lemma pix_fresh_sub : forall C A A' m' pixd w h d data, pix_fresh C A A' m' pixd w h d data -> sub_live A A'.
Proof.
  intros C A A' m' pixd w h d data (_ & _ & _ & _ & _ & _ & _ & L0p & L0d & _ & _ & L1p & L1d & LEQ & _).
  eapply sub_live_new2; [exact L0p | exact L0d | exact L1p | exact L1d | exact LEQ].
Qed.

(* [comment removed for export] *)
End GrayA.
