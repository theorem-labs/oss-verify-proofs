(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptUb.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptErr.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptPixCreate V2LeptPadBitsW V2LeptCmapValid V2LeptCmap2 V2LeptPixCopyA.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MemcpyBase V2Memcpy V2Memset.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_stringReplace V2_code_pixCreateTemplateNoInit V2_code_pixCopy_1a314.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom14.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition hdv (w h d cm data : Z) : pixv := PIXV w h d (spp_of d) (wpl_of w d) 1%Z 0%Z 0%Z 0%Z 0%Z 0%Z cm data.

Section PixRes.
Variable segs : list Segment.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
Lemma PIX_rd_res0 : forall m p v, PIXat m p v -> p_xres v = 0%Z -> p_yres v = 0%Z ->
  rdn segs m (Z_to_bv 64 (p + 24)) 8 = Some (Z_to_le_bytes 8 0).
Proof.
  intros m p v (Hp & Hn & WF & HB) Hx Hy.
  pose proof (bytes_at_field segs m p (pix_bytes v) 24 8 ltac:(lia) ltac:(rewrite pix_bytes_len; lia) ltac:(rewrite pix_bytes_len; cbn; lia) HB) as R.
  destruct v; cbn in Hx, Hy; subst. exact R.
Qed.
Lemma PIX_wr_res0 : forall m p v, PIXat m p v -> p_xres v = 0%Z -> p_yres v = 0%Z ->
  PIXat (wbytes m (Z_to_bv 64 (p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) p v.
Proof.
  intros m p v (Hp & Hn & WF & HB) Hx Hy. split; [lia|]. split; [lia|]. split; [exact WF|].
  pose proof (bytes_at_wbytes_in m p (pix_bytes v) 24 (Z_to_le_bytes 8 0) HB ltac:(lia) ltac:(rewrite pix_bytes_len; cbn; lia)
                ltac:(rewrite pix_bytes_len, length_Z_to_le_bytes; cbn; lia)) as H.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H. rewrite w2b_Z by lia.
  destruct v; cbn in Hx, Hy; subst. exact H.
Qed.
(* [comment removed for export] *)
Lemma PIX_wr_text0 : forall m p v, PIXat m p v -> p_text v = 0%Z ->
  PIXat (wbytes m (Z_to_bv 64 (p + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) p v.
Proof.
  intros m p v PX Ht. pose proof (PIX_wr_text m p v 0 PX ltac:(lia)) as X. destruct v; cbn in Ht; subst. exact X.
Qed.
Lemma PIX_wr_fmt0 : forall m p v, PIXat m p v -> p_fmt v = 0%Z ->
  PIXat (wbytes m (Z_to_bv 64 (p + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))) p v.
Proof.
  intros m p v PX Ht. pose proof (PIX_wr_fmt m p v 0 PX ltac:(lia)) as X. destruct v; cbn in Ht; subst. exact X.
Qed.
Lemma PIX_wr_spp_same : forall m p v, PIXat m p v ->
  PIXat (wbytes m (Z_to_bv 64 (p + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (p_spp v)))) p v.
Proof.
  intros m p v PX. pose proof PX as (_ & _ & WF & _). pose proof (PIX_wr_spp m p v (p_spp v) PX (wf_spp _ WF)) as X. destruct v. exact X.
Qed.
End PixRes.

Lemma zbv_ne2 : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b Ha Hb NE E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. Qed.

Section PixCopy.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  (* [comment removed for export] *)
  Definition FR4 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)).

  Definition cells4 (m : word -> option byte) (s : Z) (ret s0v s1v s2v : word) : Prop :=
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v).

  Lemma cells4_FR4 : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z -> cells4 (FR4 m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18).
  Proof. intros m s ret regs Hs Hs64. unfold cells4, FR4. repeat split; rdn_solve. Qed.

  Lemma cells4_frm : forall C s' m m' s ret s0v s1v s2v, Cok C -> FRM C s' m m' ->
    (s' <= s - 32)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z ->
    cells4 m s ret s0v s1v s2v -> cells4 m' s ret s0v s1v s2v.
  Proof.
    intros C s' m m' s ret s0v s1v s2v CK F Hs' Hlo Hs64 (R1 & R2 & R3 & R4). unfold cells4.
    rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
  Qed.

  Lemma cells4_out : forall m m' (lo hi s : Z) ret s0v s1v s2v,
    (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 32 \/ s <= lo)%Z -> (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    cells4 m s ret s0v s1v s2v -> cells4 m' s ret s0v s1v s2v.
  Proof.
    intros m m' lo hi s ret s0v s1v s2v OUT Hhi Hs Hs64 (R1 & R2 & R3 & R4). unfold cells4.
    repeat split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption]).
  Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma ptn_A : forall regs m (s pixs : Z) (vs : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 16 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 32 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x199dc : word) m rom) (mkst regs' (0x19374 : word) (FR4 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x19a10
      /\ getr regs' 10 = Z_to_bv 64 (p_w vs) /\ getr regs' 11 = Z_to_bv 64 (p_h vs) /\ getr regs' 12 = Z_to_bv 64 (p_d vs)
      /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 8 = getr regs 8
      /\ regs_agree (fun r => In r [1; 2; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixs vs ret Hs Hs64 Hp ALp PX DJ SOK H2 H1 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh. pose proof (wf_d _ WF) as Rd.
    assert (ALp8 : (pixs mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
    assert (PX1 : PIXat (FR4 m s ret regs) pixs vs).
    { unfold FR4. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_w SEGS _ _ _ PX1) as Cw. pose proof (PIX_rd_h SEGS _ _ _ PX1) as Ch. pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
    unfold FR4 in *. eexists. split.
    - zv F_199dc D_199dc (Z_to_bv 64 (s - 32)).
      stepST F_199e0 D_199e0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_199e4 D_199e4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_199e8 D_199e8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_199ec D_199ec (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepb_ft F_199f0 D_199f0 ltac:(condZ).
      sn F_199f4 D_199f4.
      guard8 F_199f8 D_199f8 ALp8. stepb_ft F_199fc D_199fc ltac:(condZ).
      stepLD F_19a00 D_19a00 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Cw) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepLD F_19a04 D_19a04 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepLD F_19a08 D_19a08 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      sn F_19a0c D_19a0c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ptn_F : forall regs m (s : Z) (ret s0v s1v s2v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x19a10 : word) m rom) (mkst regs' (0x17ec4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10765 /\ getr regs' 11 = Z_to_bv 64 0x11d5d
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v Hs Hs64 Rg Rs R8 R16 R24 R32 H2 H10. eexists. split.
    - stepb_tk F_19a10 D_19a10 ltac:(condZ).
      sn F_19a5c D_19a5c.
      stepLD F_19a60 D_19a60 (Z_to_le_bytes 8 0x45f08) (Z_to_bv 64 0x45f08) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_19a64 D_19a64 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_19a68 D_19a68. stepb_ft F_19a6c D_19a6c ltac:(condZ).
      sn F_19a70 D_19a70. sn F_19a74 D_19a74. sn F_19a78 D_19a78. sn F_19a7c D_19a7c.
      sn F_19a80 D_19a80.
      stepLD8 F_19a84 D_19a84 ret. stepLD8 F_19a88 D_19a88 s0v. stepLD8 F_19a8c D_19a8c s1v. stepLD8 F_19a90 D_19a90 s2v.
      zv F_19a94 D_19a94 (Z_to_bv 64 s). sn F_19a98 D_19a98.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ptn_B : forall regs m (s pixs pixd : Z) (vs vd : pixv),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> pixs <> pixd -> (pixd mod 16 = 0)%Z -> PIXat m pixs vs -> PIXat m pixd vd ->
    (1 <= p_spp vs)%Z -> p_spp vd = p_spp vs -> p_xres vs = 0%Z -> p_yres vs = 0%Z ->
    (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z -> store_ok SEGS m (Z_to_bv 64 pixd) 64 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x19a10 : word) m rom)
                  (mkst regs' (0x19c84 : word)
                     (wbytes (wbytes m (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (p_spp vs))))
                             (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x19af8
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs
      /\ getr regs' 18 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixs pixd vs vd Hps Hpd NE ALd PXs PXd Hspp Espp Hx Hy DJ SOKd H2 H10 H9.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof (wf_spp _ WFs) as Rspp.
    assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd).
    pose proof (PIX_rd_spp SEGS _ _ _ PXs) as Cspp.
    assert (Cres : rdn SEGS (wbytes m (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (p_spp vs)))) (Z_to_bv 64 (pixs + 24)) 8 = Some (Z_to_le_bytes 8 0)).
    { rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact (PIX_rd_res0 SEGS m pixs vs PXs Hx Hy). }
    eexists. split.
    - stepb_ft F_19a10 D_19a10 ltac:(condZ).
      sn F_19a14 D_19a14.
      stepb_ft F_19a18 D_19a18 ltac:(condZ).
      stepLD F_19a1c D_19a1c (Z_to_le_bytes 4 (p_spp vs)) (Z_to_bv 64 (p_spp vs)) ltac:(addr_norm; exact Cspp) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_spp vs)) by lia.
      guard8 F_19a20 D_19a20 ALd8.
      stepb_ft F_19a24 D_19a24 ltac:(condZ).
      stepb_ft F_19a28 D_19a28 ltac:(condZ).
      stepST F_19a2c D_19a2c (Z_to_bv 64 (pixd + 12)) (Z_to_bv 64 (p_spp vs)) ltac:(sok_in SOKd).
      sn F_19a30 D_19a30.
      stepb_ft F_19ae0 D_19ae0 ltac:(condZ).
      stepLD F_19ae4 D_19ae4 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Cres) ltac:(apply lez8; lia).
      stepST F_19ae8 D_19ae8 (Z_to_bv 64 (pixd + 24)) (Z_to_bv 64 0) ltac:(sok_in SOKd).
      sn F_19aec D_19aec. sn F_19af0 D_19af0. sn F_19af4 D_19af4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ptn_C : forall regs m (s pixs pixd : Z) (vs vd : pixv),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixs vs -> PIXat m pixd vd ->
    p_text vs = 0%Z -> p_text vd = 0%Z -> p_fmt vs = 0%Z ->
    (pixs + 64 <= pixd \/ pixd + 64 <= pixs)%Z -> (pixd + 64 <= s - 64 \/ s <= pixd)%Z -> (pixs + 64 <= s - 64 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 32 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x19af8 : word) m rom)
                  (mkst regs' (0x1bd14 : word)
                     (wbytes (wbytes (wbytes (wbytes (wbytes m
                        (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x19b04)))
                        (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
                        (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixs)))
                        (Z_to_bv 64 (pixd + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                        (Z_to_bv 64 (pixd + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x19b18
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pixs pixd vs vd Hs Hs64 Hps Hpd ALd PXs PXd Hts Htd Hfs DJ DJd DJs SOKd SOK H2 H8 H9.
    pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    assert (ALt : ((pixd + 40) mod 8 = 0)%Z) by (apply al16_plus_mod8; [exact ALd | reflexivity]).
    pose proof (PIX_rd_text SEGS _ _ _ PXs) as Cts. rewrite Hts in Cts. pose proof (PIX_rd_text SEGS _ _ _ PXd) as Ctd. rewrite Htd in Ctd.
    pose proof (PIX_rd_fmt SEGS _ _ _ PXs) as Cfs. rewrite Hfs in Cfs.
    eexists. split.
    - stepLD F_19af8 D_19af8 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Cts) ltac:(apply lez8; lia).
      zv F_19afc D_19afc (Z_to_bv 64 (pixd + 40)).
      sn F_19b00 D_19b00.
      zv F_18064 D_18064 (Z_to_bv 64 (s - 64)).
      stepST F_18068 D_18068 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 0x19b04) ltac:(sok_in SOK).
      stepST F_1806c D_1806c (Z_to_bv 64 (s - 48)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepST F_18070 D_18070 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 pixs) ltac:(sok_in SOK).
      stepb_ft F_18074 D_18074 ltac:(condZ).
      sn F_18078 D_18078.
      guard8 F_1807c D_1807c ALt. stepb_ft F_18080 D_18080 ltac:(condZ).
      sn F_18084 D_18084.
      stepLD F_18088 D_18088 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact Ctd) ltac:(apply lez8; lia).
      stepb_tk F_1808c D_1808c ltac:(condZ).
      stepb_tk F_18094 D_18094 ltac:(condZ).
      sn F_180e4 D_180e4. sn F_180e8 D_180e8.
      stepST F_180ec D_180ec (Z_to_bv 64 (pixd + 40)) (Z_to_bv 64 0) ltac:(sok_in SOKd).
      sn F_180f0 D_180f0.
      stepLD8 F_180f8 D_180f8 (Z_to_bv 64 0x19b04). stepLD8 F_180fc D_180fc (Z_to_bv 64 pixd). stepLD8 F_18100 D_18100 (Z_to_bv 64 pixs).
      zv F_18104 D_18104 (Z_to_bv 64 (s - 32)).
      stepret F_18108 D_18108 (0x19b04 : word) ltac:(bveq).
      stepLD F_19b04 D_19b04 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; repeat rdn_peel1; exact Cfs) ltac:(apply lez4; lia).
      stepST F_19b08 D_19b08 (Z_to_bv 64 (pixd + 32)) (Z_to_bv 64 0) ltac:(sok_in SOKd).
      sn F_19b0c D_19b0c. sn F_19b10 D_19b10. sn F_19b14 D_19b14.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ptn_D : forall regs m (s pixd : Z) (ret s0v s1v s2v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x19b18 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18]%list) regs regs'.
  Proof.
    intros regs m s pixd ret s0v s1v s2v Hs Hs64 Hret R8 R16 R24 R32 H2 H8. eexists. split.
    - sn F_19b18 D_19b18.
      stepLD8 F_19b1c D_19b1c ret. stepLD8 F_19b20 D_19b20 s0v. stepLD8 F_19b24 D_19b24 s1v. stepLD8 F_19b28 D_19b28 s2v.
      zv F_19b2c D_19b2c (Z_to_bv 64 s). stepret F_19b30 D_19b30 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_A : forall regs m (s pixs : Z) (vs : pixv) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 16 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 48 \/ s <= pixs)%Z ->
    (0 < 4 * (p_wpl vs * p_h vs) < 2 ^ 31)%Z -> (0 <= p_wpl vs * p_h vs)%Z -> (p_wpl vs < 2 ^ 24)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x1a314 : word) m rom) (mkst regs' (0x199dc : word) (FR5 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x1a3fc /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 (4 * (p_wpl vs * p_h vs)) /\ getr regs' 8 = Z_to_bv 64 0 /\ getr regs' 19 = getr regs 19
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixs vs ret Hs Hs64 Hp ALp PX DJ Hsz Hwh Hwpl SOK H2 H1 H10 H11. pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (wf_h _ WF) as Rh. pose proof (wf_wpl _ WF) as Rwpl.
    assert (ALp8 : (pixs mod 8 = 0)%Z) by (apply al16_mod8; exact ALp).
    assert (PX1 : PIXat (FR5 m s ret regs) pixs vs).
    { unfold FR5. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_h SEGS _ _ _ PX1) as Ch. pose proof (PIX_rd_wpl SEGS _ _ _ PX1) as Cwpl.
    assert (Hm4 : (0 <= 4 * p_wpl vs * p_h vs < 2 ^ 31)%Z) by nia.
    unfold FR5 in *. eexists. split.
    - zv F_1a314 D_1a314 (Z_to_bv 64 (s - 48)).
      stepST F_1a318 D_1a318 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_1a31c D_1a31c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1a320 D_1a320 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_1a324 D_1a324 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_1a328 D_1a328 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      sn F_1a32c D_1a32c.
      stepb_ft F_1a330 D_1a330 ltac:(condZ).
      sn F_1a334 D_1a334.
      stepb_ft F_1a338 D_1a338 ltac:(condZ).
      guard8 F_1a33c D_1a33c ALp8. stepb_ft F_1a340 D_1a340 ltac:(condZ).
      stepLD F_1a344 D_1a344 (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; exact Cwpl) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vs)) by lia.
      sn F_1a348 D_1a348.
      zv F_1a34c D_1a34c (Z_to_bv 64 (p_wpl vs + 536870912)).
      sn F_1a350 D_1a350. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srliw_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_1a354 D_1a354 ltac:(condZ).
      stepLD F_1a358 D_1a358 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      sn F_1a35c D_1a35c. fixv (Z_to_bv 64 (4 * p_wpl vs)) ltac:(rewrite v_slliw_2, sw32_small by lia; f_equal; lia).
      zv F_1a360 D_1a360 (Z_to_bv 64 (4 * (p_wpl vs * p_h vs))).
      sn F_1a364 D_1a364. fixv (Z_to_bv 64 (4 * (p_wpl vs * p_h vs))) ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
      stepb_ft F_1a368 D_1a368 ltac:(condZ).
      stepb_tk F_1a36c D_1a36c ltac:(condZ).
      sn F_1a3f4 D_1a3f4. sn F_1a3f8 D_1a3f8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_F1 : forall regs m (s : Z),
    rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x1a3fc : word) m rom) (mkst regs' (0x17ec4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x1a490
      /\ getr regs' 10 = Z_to_bv 64 0x10765 /\ getr regs' 11 = Z_to_bv 64 0x117e8 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 0x45f08
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 19]%list) regs regs'.
  Proof.
    intros regs m s Rg Rs H2 H10. eexists. split.
    - stepb_tk F_1a3fc D_1a3fc ltac:(condZ).
      sn F_1a464 D_1a464.
      stepLD F_1a468 D_1a468 (Z_to_le_bytes 8 0x45f08) (Z_to_bv 64 0x45f08) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_1a46c D_1a46c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rs) ltac:(apply lez4; lia).
      sn F_1a470 D_1a470. stepb_ft F_1a474 D_1a474 ltac:(condZ).
      sn F_1a478 D_1a478. sn F_1a47c D_1a47c. sn F_1a480 D_1a480. sn F_1a484 D_1a484. sn F_1a488 D_1a488. sn F_1a48c D_1a48c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_F2 : forall regs m (s : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) -> cells5 m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 -> getr regs 19 = Z_to_bv 64 0x45f08 ->
    exists regs',
      msteps SEGS (mkst regs (0x1a490 : word) m rom) (mkst regs' (0x17ec4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x10765 /\ getr regs' 11 = Z_to_bv 64 0x1173b /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v Hs Hs64 Rs (R8 & R16 & R24 & R32 & R40) H2 H10 H19. eexists. split.
    - stepb_tk F_1a490 D_1a490 ltac:(condZ).
      stepLD F_1a510 D_1a510 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rs) ltac:(apply lez4; lia).
      sn F_1a514 D_1a514. stepb_ft F_1a518 D_1a518 ltac:(condZ).
      sn F_1a51c D_1a51c. sn F_1a520 D_1a520. sn F_1a524 D_1a524. sn F_1a528 D_1a528. sn F_1a52c D_1a52c.
      sn F_1a3a8 D_1a3a8. sn F_1a3ac D_1a3ac.
      stepLD8 F_1a3d8 D_1a3d8 ret. stepLD8 F_1a3dc D_1a3dc s0v. stepLD8 F_1a3e0 D_1a3e0 s1v.
      stepLD8 F_1a3e4 D_1a3e4 s2v. stepLD8 F_1a3e8 D_1a3e8 s3v.
      zv F_1a3ec D_1a3ec (Z_to_bv 64 s). sn F_1a3f0 D_1a3f0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_B : forall regs m (s pixd : Z) (vd : pixv),
    (1 <= pixd)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> (0 <= p_wpl vd * p_h vd)%Z -> (4 * (p_wpl vd * p_h vd) < 2 ^ 31)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x1a3fc : word) m rom) (mkst regs' (0x43880 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x1a434
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl vd * p_h vd))
      /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pixd vd Hp ALd PX Hwh Hsz H2 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    pose proof (wf_h _ WF) as Rh. pose proof (wf_wpl _ WF) as Rwpl. pose proof (wf_data _ WF) as Rdata.
    assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd).
    assert (Hm4 : (0 <= 4 * p_wpl vd * p_h vd < 2 ^ 31)%Z) by nia.
    pose proof (PIX_rd_h SEGS _ _ _ PX) as Ch. pose proof (PIX_rd_wpl SEGS _ _ _ PX) as Cwpl. pose proof (PIX_rd_data SEGS _ _ _ PX) as Cdata.
    eexists. split.
    - stepb_ft F_1a3fc D_1a3fc ltac:(condZ).
      sn F_1a400 D_1a400.
      guard8 F_1a404 D_1a404 ALd8. stepb_ft F_1a408 D_1a408 ltac:(condZ).
      stepLD F_1a40c D_1a40c (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; exact Cwpl) ltac:(apply lez4; lia).
      stepLD F_1a410 D_1a410 (Z_to_le_bytes 4 (p_h vd)) (Z_to_bv 64 (p_h vd)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      stepiv F_1a414 D_1a414 (Z_to_bv 64 (4 * p_wpl vd)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_1a418 D_1a418. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_1a41c D_1a41c (Z_to_bv 64 (4 * (p_wpl vd * p_h vd))).
      sn F_1a420 D_1a420. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_1a424 D_1a424 ltac:(condZ).
      stepLD F_1a428 D_1a428 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdata) ltac:(apply lez8; lia).
      sn F_1a42c D_1a42c. sn F_1a430 D_1a430.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_C : forall regs m (s pixd pixs : Z) (vd vs : pixv) (nb : Z),
    (1 <= pixd)%Z -> (1 <= pixs)%Z -> (pixd mod 16 = 0)%Z -> PIXat m pixd vd -> PIXat m pixs vs ->
    (p_data vd mod 16 = 0)%Z -> (p_data vs mod 16 = 0)%Z -> (0 <= nb < 2 ^ 31)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 nb ->
    exists regs',
      msteps SEGS (mkst regs (0x1a434 : word) m rom) (mkst regs' (0x4347c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x1a50c
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd) /\ getr regs' 11 = Z_to_bv 64 (p_data vs) /\ getr regs' 12 = Z_to_bv 64 nb
      /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 nb
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs vd vs nb Hpd Hps ALd PXd PXs ALdd ALds Hnb H2 H8 H9 H18.
    pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof (wf_data _ WFd) as Rdd. pose proof (wf_data _ WFs) as Rds.
    assert (ALd8 : (pixd mod 8 = 0)%Z) by (apply al16_mod8; exact ALd).
    pose proof (Z_lor_range64 (p_data vd) (p_data vs) ltac:(lia) ltac:(lia)) as ORr.
    pose proof (lor_mod4_0 (p_data vd) (p_data vs) ltac:(lia) ltac:(lia) ltac:(apply al16_mod4; exact ALdd) ltac:(apply al16_mod4; exact ALds)) as OR4.
    pose proof (PIX_rd_data SEGS _ _ _ PXd) as Cdd. pose proof (PIX_rd_data SEGS _ _ _ PXs) as Cds.
    eexists. split.
    - guard8 F_1a434 D_1a434 ALd8. stepb_tk F_1a438 D_1a438 ltac:(condZ).
      stepLD F_1a4f0 D_1a4f0 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdd) ltac:(apply lez8; lia).
      stepLD F_1a4f4 D_1a4f4 (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; exact Cds) ltac:(apply lez8; lia).
      orv F_1a4f8 D_1a4f8 (p_data vd) (p_data vs). guard4 F_1a4fc D_1a4fc OR4. stepb_ft F_1a500 D_1a500 ltac:(condZ).
      sn F_1a504 D_1a504. fixv (Z_to_bv 64 nb) ltac:(rewrite v_addiw_Z; f_equal; rewrite sw32_small by lia; lia).
      sn F_1a508 D_1a508.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcp_D : forall regs m (s pixd : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells5 m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x1a50c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pixd ret s0v s1v s2v s3v Hs Hs64 Hret (R8 & R16 & R24 & R32 & R40) H2 H8. eexists. split.
    - sn F_1a50c D_1a50c. sn F_1a534 D_1a534.
      stepLD8 F_1a538 D_1a538 ret. stepLD8 F_1a53c D_1a53c s0v. stepLD8 F_1a540 D_1a540 s1v.
      stepLD8 F_1a544 D_1a544 s2v. stepLD8 F_1a548 D_1a548 s3v.
      zv F_1a54c D_1a54c (Z_to_bv 64 s). stepret F_1a550 D_1a550 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.


Lemma str_pixCreateTemplateNoInit : str16 0x11d5d 23. Proof. str16_tac. Qed.

#[local] Definition tn_rest : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition cmres (C : lctx) (A A' : AS) (m' : word -> option byte) (pixd data cd : Z) (cv : cmapv) : Prop :=
  (cd = 0%Z /\ forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> live A' q = live A q)
  \/ (exists ad, cmap_ok cv /\ (4096 <= cd)%Z /\ (cd + 32 <= alloc_top (c_vm C))%Z /\ (4096 <= ad)%Z /\ (ad + 4 * c_nalloc cv <= alloc_top (c_vm C))%Z /\
       cd <> ad /\ cd <> pixd /\ cd <> data /\ ad <> pixd /\ ad <> data /\
       live A (Z_to_bv 64 cd) = None /\ live A (Z_to_bv 64 ad) = None /\ live (c_A0 C) (Z_to_bv 64 cd) = None /\ live (c_A0 C) (Z_to_bv 64 ad) = None /\
       live A' (Z_to_bv 64 cd) = Some 24%Z /\ live A' (Z_to_bv 64 ad) = Some (4 * c_nalloc cv)%Z /\
       CMAPat m' cd (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) /\
       (forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> q <> Z_to_bv 64 cd -> q <> Z_to_bv 64 ad -> live A' q = live A q)).

(* [comment removed for export] *)
Definition pixt_new (C : lctx) (A A' : AS) (m' : word -> option byte) (pixd w h d cd data : Z) (cv : cmapv) : Prop :=
  (4096 <= pixd)%Z /\ (pixd + 64 <= alloc_top (c_vm C))%Z /\ (pixd mod 16 = 0)%Z /\
  (4096 <= data)%Z /\ (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z /\ (data mod 16 = 0)%Z /\ pixd <> data /\
  live A (Z_to_bv 64 pixd) = None /\ live A (Z_to_bv 64 data) = None /\
  live (c_A0 C) (Z_to_bv 64 pixd) = None /\ live (c_A0 C) (Z_to_bv 64 data) = None /\
  live A' (Z_to_bv 64 pixd) = Some 64%Z /\ live A' (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z /\
  PIXat m' pixd (hdv w h d cd data) /\ cmres C A A' m' pixd data cd cv.

(* [comment removed for export] *)
Definition TK (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h d : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h d cd data cv) ) ->
     aroom A' vm' (kR - RK_pixcopy) (bR - RB_pixcopy14) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

(* [comment removed for export] *)
Lemma ptn_tail_W : forall C A A2 m md m4 vm2 regs r4 (s pixs pixd w h d cm datas cd data : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> TK C A m md regs s w h d cv ret S kR bR ->
  aroom A2 vm2 (kR - RK_pixcopy) (bR - RB_pixcopy14) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 128 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  W C A2 m4 (with_vmmaps vm2 md) -> POSTM C A s m m4 -> sub_live A A2 ->
  cells4 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) ->
  getr r4 2 = Z_to_bv 64 (s - 32) -> getr r4 8 = Z_to_bv 64 pixd -> getr r4 9 = Z_to_bv 64 pixs ->
  (forall x, In x tn_rest -> getr r4 x = getr regs x) -> getr regs 2 = Z_to_bv 64 s ->
  PIXat m4 pixs (hdv w h d cm datas) -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  (4096 <= pixd)%Z -> (pixd + 64 <= alloc_top (c_vm C))%Z -> (pixd mod 16 = 0)%Z ->
  (4096 <= data)%Z -> (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z -> (data mod 16 = 0)%Z -> pixd <> data ->
  live A (Z_to_bv 64 pixd) = None -> live A (Z_to_bv 64 data) = None ->
  live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A2 (Z_to_bv 64 pixd) = Some 64%Z -> live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z ->
  PIXat m4 pixd (hdv w h d cd data) -> cmres C A A2 m4 pixd data cd cv ->
  realizes SEGS (mkCfg (mkst r4 (0x19af8 : word) m4 al_rom) (with_vmmaps vm2 md)) S.
Proof.
  intros C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas cd data cv ret S kR bR CK HK Hrm2 Hs16 Hlo Hhi Hret HW4 PM4 SUB CE4 R2 R8 R9 RR H2 PXs Lps HOK Hw Hh
         Gp TOPp ALp Gd TOPd ALd NEpd LAp LAd L00p L00d L2p L2d PXd CMR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  pose proof (SUB _ _ Lps) as Lps2.
  destruct (blk_range C A2 m4 _ (Z_to_bv 64 pixs) 64 CK HW4 Lps2 ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in LAp; discriminate).
  pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 Lps2 L2p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
  destruct (ptn_C al_rom r4 m4 s pixs pixd (hdv w h d cm datas) (hdv w h d cd data) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALp PXs PXd
              eq_refl eq_refl eq_refl APsp ltac:(lia) ltac:(lia) (blk_sok C A2 m4 _ pixd 64 CK HW4 L2p ltac:(lia) ltac:(lia) ltac:(lia))
              (W_sok_win C A2 m4 _ (s - 64) 32 CK HW4 ltac:(lia) ltac:(cbn; lia)) R2 R8 R9)
    as (r5 & RUN5 & Y2 & Y1 & Y10 & Y11 & Y8 & Y9 & AG5).
  apply box_i in APsp.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
  set (Mw := wbytes (wbytes (wbytes m4 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x19b04)))
                            (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)))
                            (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixs))).
  set (M5 := wbytes (wbytes Mw (Z_to_bv 64 (pixd + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (pixd + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
  assert (WPw : W C A2 Mw (with_vmmaps vm2 md) /\ POSTM C A s m Mw) by (subst Mw; wp_win CK).
  assert (WP5 : W C A2 M5 (with_vmmaps vm2 md) /\ POSTM C A s m M5).
  { subst M5. do 2 (apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L2p | exact LAp | exact L00p | exact SUB | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    exact WPw. }
  destruct WP5 as [HW5 PM5].
  assert (OUTw : forall x : word, ~ (s - 56 <= u x < s - 32)%Z -> Mw x = m4 x).
  { intros x Hx. subst Mw. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (OUT5 : forall x : word, ~ (pixd + 32 <= u x < pixd + 48)%Z -> M5 x = Mw x).
  { intros x Hx. subst M5. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXd5 : PIXat M5 pixd (hdv w h d cd data)).
  { subst M5. apply PIX_wr_fmt0; [|reflexivity]. apply PIX_wr_text0; [|reflexivity]. apply (PIXat_frame m4); [exact PXd|]. intros x Hx. apply OUTw. lia. }
  assert (CE5 : cells4 M5 s ret (getr regs 8) (getr regs 9) (getr regs 18)).
  { eapply (cells4_out Mw _ (pixd + 32) (pixd + 48)); [exact OUT5 | lia | lia | lia |].
    eapply (cells4_out m4 _ (s - 56) (s - 32)); [exact OUTw | lia | lia | lia | exact CE4]. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  apply (padbits_W C A A2 M5 _ r5 (s - 32) pixd (hdv w h d cd data) (Z_to_bv 64 0x19b18) S CK HW5 SUB Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11 PXd5 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl L2p).
  { cbn. exact L2d. } { cbn. exact LAd. } { cbn. exact L00d. } { cbn. exact NEpdw. }
  intros m6 r6 HW6 CS6 PM6 PX6 OUT6 A10. cbn [p_data p_wpl p_h hdv] in OUT6. unfold LSF in OUT6.
  replace (Z_to_bv 64 0x19b18) with (0x19b18 : word) by (apply bv_eq; reflexivity).
  pose proof (cells4_frm C (s - 32) M5 m6 s _ _ _ _ CK (proj1 PM6) ltac:(lia) ltac:(lia) ltac:(lia) CE5) as (C1 & C2 & C3 & C4).
  destruct (ptn_D al_rom r6 m6 s pixd ret _ _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 C4 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r7 & RUN7 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
  apply (HK A2 m6 vm2 r7 HW6).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Z18; try reflexivity. all: unfold tn_rest in RR; csr; reflexivity.
  - eapply POSTM_trans; [exact PM5 | eapply POSTM_mono; [|exact PM6]; lia].
  - right. exists pixd, cd, data. split; [exact Z10|].
    unfold pixt_new. do 13 (split; [assumption|]). split; [exact PX6|].
    destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)]; [left; split; [exact CD0 | exact LEQ] | right].
    exists ad. do 16 (split; [assumption|]). split; [| exact LEQ].
    assert (NEw1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
    pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 L2cd L2d NEw1 ltac:(lia) ltac:(lia)) as APcdd. rewrite !u_Z2bv in APcdd by lia.
    assert (NEw2 : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (apply zbv_ne2; lia).
    pose proof (blk_apart C A2 m4 _ _ _ _ _ CK HW4 L2cd L2p NEw2 ltac:(lia) ltac:(lia)) as APcdp. rewrite !u_Z2bv in APcdp by lia.
    apply (CMAPat_frame m4); [exact CM4|]. intros x Hx. rewrite OUT6 by lia. rewrite OUT5 by lia. apply OUTw. lia.
  - exact Hrm2.
Qed.

Theorem pixCreateTemplateNoInit_W : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 128 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB_pixcopy14 <= bR)%Z ->
  TK C A m md regs s w h d cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x199dc : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PXs HOK Hw Hh Lps HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  destruct (ptn_A al_rom regs m s pixs (hdv w h d cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) ALps PXs ltac:(lia)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & Q8 & AG1). cbn [p_w p_h p_d hdv] in Q10, Q11, Q12.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR4 m s ret regs) md /\ POSTM C A s m (FR4 m s ret regs)) by (unfold FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR4 m s ret regs) in *.
  pose proof (cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 32 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR4. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  assert (Hwh : (w * h <= 400000000)%Z) by (clear - Hw Hh Hw2 Hh2; nia).
  apply (pixCreateNoInit_W C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x19a10) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 ltac:(lia) ltac:(lia) Hwh ltac:(lia)).
  intros A1 m2 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x19a10) with (0x19a10 : word) by (apply bv_eq; reflexivity).
  pose proof (cells4_frm C (s - 32) M1 m2 s _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (hdv w h d cm datas)).
  { apply (PIXat_frame m); [exact PXs|]. intros x Hx. rewrite (LIVK_byte C A M1 m2 md pixs 64 x CK HW1 (proj2 PMa) Lps ltac:(lia) TOPps Hx). apply OUT1. lia. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & data & Hres & _ & PN)].
  - (* [comment removed for export] *)
    destruct CE2 as (C1 & C2 & C3 & C4).
    destruct (ptn_F al_rom r2 m2 s ret _ _ _ ltac:(lia) ltac:(lia) (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) C1 C2 C3 C4 E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m2 _ r3 s 0x10765 0x11d5d 13 23 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd str_pixCreateTemplateNoInit).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9, ?V18, ?Q8; reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m2 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + room_tac.
  - (* [comment removed for export] *)
    destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & _).
    cbn [p_wpl p_h set_data pix_hdr] in TOPd, L1d.
    change (PIXat m2 pixd (hdv w h d 0 data)) in PXd.
    assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0p | exact L0d | exact L1p | exact L1d | exact LEQ]).
    pose proof (SUBa _ _ Lps) as Lps1.
    pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa Lps1 L1p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
    destruct (ptn_B al_rom r2 m2 s pixs pixd (hdv w h d cm datas) (hdv w h d 0 data) ltac:(lia) ltac:(lia) ltac:(lia) ALp PXs2 PXd
                (proj1 (spp_of_range d)) eq_refl eq_refl eq_refl APsp (blk_sok C A1 m2 _ pixd 64 CK HWa L1p ltac:(lia) ltac:(lia) ltac:(lia)) E2 Hres E9)
      as (r3 & RUN3 & X2 & X1 & X10 & X11 & X8 & X9 & X18 & AG3).
    apply box_i in APsp.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    cbn [p_spp hdv] in *.
    set (M3 := wbytes (wbytes m2 (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (spp_of d)))) (Z_to_bv 64 (pixd + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3).
    { subst M3. do 2 (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L1p | exact L0p | exact L00p | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
      split; [exact HWa | exact PMa']. }
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (pixd + 12 <= u x < pixd + 32)%Z -> M3 x = m2 x).
    { intros x Hx. subst M3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PXd3 : PIXat M3 pixd (hdv w h d 0 data)).
    { subst M3. apply (PIX_wr_res0 _ pixd (hdv w h d 0 data)); [| reflexivity | reflexivity].
      exact (PIX_wr_spp_same m2 pixd (hdv w h d 0 data) PXd). }
    assert (PXs3 : PIXat M3 pixs (hdv w h d cm datas)).
    { pose proof (box_e _ APsp) as U. apply (PIXat_frame m2); [exact PXs2|]. intros x Hx. apply OUT3. lia. }
    assert (CE3 : cells4 M3 s ret (getr regs 8) (getr regs 9) (getr regs 18)) by (eapply (cells4_out m2 _ (pixd + 12) (pixd + 32)); [exact OUT3 | lia | lia | lia | exact CE2]).
    assert (X4 : getr r3 4 = Z_to_bv 64 0x56270) by (rewrite (AG3 4) by (cbv; intuition discriminate); exact E4).
    assert (HCM3 : cm = 0%Z \/ (CMAPat M3 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
    { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
      pose proof (SUBa _ _ Lcm) as Lcm1.
      assert (NEcp : Z_to_bv 64 cm <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lcm; rewrite Lcm in L0p; discriminate).
      pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa Lcm1 L1p NEcp ltac:(lia) ltac:(lia)) as APcp. rewrite !u_Z2bv in APcp by lia.
      split; [| split; [exact CMOK | split; [exact Lcm1 | exact (SUBa _ _ Larr)]]].
      apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite OUT3 by lia.
      rewrite (LIVK_byte C A M1 m2 md cm 24 x CK HW1 (proj2 PMa) Lcm ltac:(lia) TOPcm Hx). apply OUT1. lia. }
    apply (pixCopyColormap_W C A A1 M3 _ r3 (s - 32) pixd pixs (hdv w h d 0 data) (hdv w h d cm datas) cv (Z_to_bv 64 0x19af8) S CK HW3 SUBa X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 X11
             PXd3 PXs3 eq_refl eq_refl ltac:(pose proof (box_e _ APsp); lia) L1p L0p L00p Lps1 HCM3
             (kR - RK_pix) (bR - RB_pix14) ltac:(room_tac) ltac:(room_consts; lia) ltac:(room_consts; lia)).
    intros A2 m4 vm2 r4 HWb CSb PMb OUTb Hrm2. rewrite with_vmmaps_twice in HWb |- *.
    replace (Z_to_bv 64 0x19af8) with (0x19af8 : word) by (apply bv_eq; reflexivity).
    pose proof (cells4_frm C (s - 32) M3 m4 s _ _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE3) as CE4.
    assert (PMb' : POSTM C A s m m4) by (eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PMb]; lia]).
    assert (PXs4 : PIXat m4 pixs (hdv w h d cm datas)).
    { apply (PIXat_frame M3); [exact PXs3|]. intros x Hx. exact (LIVK_at A M3 m4 pixs 64 x (proj2 PMb) Lps ltac:(lia) ltac:(lia) Hx). }
    assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (Y8 : getr r4 8 = Z_to_bv 64 pixd) by (csr; reflexivity).
    assert (Y9 : getr r4 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
    assert (RR : forall x, In x tn_rest -> getr r4 x = getr regs x) by (unfold tn_rest; rest_solve).
    destruct OUTb as [[LIVEQ PXd4] | (cd & ad & CC & PXd4)].
    + apply (ptn_tail_W C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas 0 data cv ret S kR bR CK HK ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret HWb PMb'
               (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LIVEQ)) CE4 Y2 Y8 Y9 RR H2 PXs4 Lps HOK Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               ltac:(rewrite LIVEQ; exact L1p) ltac:(rewrite LIVEQ; exact L1d) PXd4).
      left. split; [reflexivity|]. intros q N1 N2. rewrite LIVEQ. apply LEQ; assumption.
    + pose proof CC as (CMOKc & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & LA1cd & LA1ad & L00cd & L00ad & L2cd & L2ad & LEQ2 & CM4).
      assert (NEcdp : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1cd; rewrite L1p in LA1cd; discriminate).
      assert (NEadp : Z_to_bv 64 ad <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1ad; rewrite L1p in LA1ad; discriminate).
      assert (NEcdd : Z_to_bv 64 cd <> Z_to_bv 64 data) by (intros E; rewrite E in LA1cd; rewrite L1d in LA1cd; discriminate).
      assert (NEadd : Z_to_bv 64 ad <> Z_to_bv 64 data) by (intros E; rewrite E in LA1ad; rewrite L1d in LA1ad; discriminate).
      assert (SUBb : sub_live A1 A2) by (eapply sub_live_new2; [exact LA1cd | exact LA1ad | exact L2cd | exact L2ad | exact LEQ2]).
      apply (ptn_tail_W C A A2 m md m4 vm2 regs r4 s pixs pixd w h d cm datas cd data cv ret S kR bR CK HK ltac:(room_tac) Hs16 ltac:(unfold LSF; lia) Hhi Hret HWb PMb'
               (sub_live_trans _ _ _ SUBa SUBb) CE4 Y2 Y8 Y9 RR H2 PXs4 Lps HOK Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               (SUBb _ _ L1p) (SUBb _ _ L1d) PXd4).
      right. exists ad.
      split; [exact CMOKc|]. split; [exact Gcd|]. split; [exact TOPcd|]. split; [exact Gad|]. split; [exact TOPad|]. split; [exact NEcdad|].
      split; [intros E; apply NEcdp; rewrite E; reflexivity|]. split; [intros E; apply NEcdd; rewrite E; reflexivity|].
      split; [intros E; apply NEadp; rewrite E; reflexivity|]. split; [intros E; apply NEadd; rewrite E; reflexivity|].
      split; [rewrite <- (LEQ _ NEcdp NEcdd); exact LA1cd|]. split; [rewrite <- (LEQ _ NEadp NEadd); exact LA1ad|].
      split; [exact L00cd|]. split; [exact L00ad|]. split; [exact L2cd|]. split; [exact L2ad|]. split; [exact CM4|].
      intros q N1 N2 N3 N4. rewrite (LEQ2 q N3 N4). apply LEQ; assumption.
Qed.


Lemma str_pixCreateTemplate : str16 0x117e8 17. Proof. str16_tac. Qed.
Lemma str_pixCopy : str16 0x1173b 7. Proof. str16_tac. Qed.

Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Theorem pixCopy_W : forall C A m md regs (s pixs w h d cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 176 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> (RB_pixcopy14 <= bR)%Z ->
  TK C A m md regs s w h d cv ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x1a314 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs w h d cm datas cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof (wf_data _ WFs) as Rds. cbn [p_data hdv] in Rds.
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datas) _ CK HW Lds ltac:(lia)) as [Gds TOPds]. rewrite u_Z2bv in Gds, TOPds by lia.
  set (n := (4 * (wpl_of w d * h))%Z) in *. assert (En : n = (4 * (wpl_of w d * h))%Z) by reflexivity.
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lds) as (_ & ALds & _). rewrite u_Z2bv in ALds by lia.
  destruct (pcp_A al_rom regs m s pixs (hdv w h d cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) ALps PXs ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q9 & Q18 & Q8 & Q19 & AG1). cbn [p_wpl p_h hdv] in Q18. rewrite <- En in Q18.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR5 m s ret regs) md /\ POSTM C A s m (FR5 m s ret regs)) by (unfold FR5; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR5 m s ret regs) in *.
  pose proof (cells5_FR5 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 48 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR5. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (hdv w h d cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right]. split; [| split; [exact CMOK | split; [exact Lcm | exact Larr]]].
    pose proof CM as (Hc0 & Hc64 & _). destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
    apply (CMAPat_frame m); [exact CM|]. intros x Hx. apply OUT1. lia. }
  apply (pixCreateTemplateNoInit_W C A M1 md r1 (s - 48) pixs w h d cm datas cv (Z_to_bv 64 0x1a3fc) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw Hh Lps HCM1 kR bR Hrm Hrk Hrb).
  unfold TK. intros A1 m2 vm1 r2 HWa CSa PMa OUTa Hrm1.
  replace (Z_to_bv 64 0x1a3fc) with (0x1a3fc : word) by (apply bv_eq; reflexivity).
  pose proof (cells5_frm C (s - 48) M1 m2 s _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (hdv w h d cm datas)).
  { apply (PIXat_frame M1); [exact PXs1|]. intros x Hx. exact (LIVK_at A M1 m2 pixs 64 x (proj2 PMa) Lps ltac:(lia) ltac:(lia) Hx). }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
  assert (E18 : getr r2 18 = Z_to_bv 64 n) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & cd & data & Hres & PT)].
  - (* [comment removed for export] *)
    destruct (pcp_F1 al_rom r2 m2 s (W_sev_got C A1 m2 _ HWa) (W_sev C A1 m2 _ HWa) E2 Hres0) as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V19 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m2 _ r3 (s - 48) 0x10765 0x117e8 13 17 (Z_to_bv 64 0x1a490) (Z_to_bv 64 0) S CK HWa V2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
             V10 V11 V12 str_msg_pixd str_pixCreateTemplate).
    intros m3 r4 HW3 OUT3 GR3 CS3 B10. unfold LSF in OUT3.
    replace (Z_to_bv 64 0x1a490) with (0x1a490 : word) by (apply bv_eq; reflexivity).
    pose proof (cells5_out m2 m3 _ _ s _ _ _ _ _ OUT3 ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (Y19 : getr r4 19 = Z_to_bv 64 0x45f08) by (csr; reflexivity).
    destruct (pcp_F2 al_rom r4 m3 s ret _ _ _ _ ltac:(lia) ltac:(lia) (W_sev C A1 m3 _ HW3) CE3 ltac:(csr; reflexivity) B10 Y19)
      as (r5 & RUN5 & X2 & X1 & X10 & X11 & X12 & X8 & X9 & X18 & X19 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
    apply (returnErrorPtr_W C A1 m3 _ r5 s 0x10765 0x1173b 13 7 ret (Z_to_bv 64 0) S CK HW3 X2 Hs16 ltac:(unfold LSF; lia) Hhi X1 Hret
             X10 X11 X12 str_msg_pixd str_pixCopy).
    intros m4 r6 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r6).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?X8, ?X9, ?X18, ?X19, ?Q19; reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply POSTM_trans; [eapply (POSTM_range C A1 m2 _ m3); [exact CK | exact HWa | exact OUT3 | lia | lia | lia] |].
      eapply (POSTM_range C A1 m3 _ m4); [exact CK | exact HW3 | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + exact Hrm1.
  - (* [comment removed for export] *)
    pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). rewrite <- En in TOPd, L1d.
    assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
    assert (NEsd : Z_to_bv 64 datas <> Z_to_bv 64 data) by (intros E; rewrite E in Lds; rewrite Lds in L0d; discriminate).
    assert (SUBa : sub_live A A1).
    { intros q k Lq. destruct CMR as [[_ LEQ] | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LAcd & LAad & _ & _ & _ & _ & _ & LEQ)].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence | intros ->; congruence | intros ->; congruence]. }
    pose proof (SUBa _ _ Lps) as Lps1. pose proof (SUBa _ _ Lds) as Lds1.
    destruct (pcp_B al_rom r2 m2 s pixd (hdv w h d cd data) ltac:(lia) ALp PXd ltac:(cbn; lia) ltac:(cbn; lia) E2 Hres)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & AG3). cbn [p_data p_wpl p_h hdv] in V10, V12. rewrite <- En in V12.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    (* [comment removed for export] *)
    pose proof (blk_sok C A1 m2 _ data n CK HWa L1d ltac:(lia) ltac:(lia) ltac:(lia)) as SOKd.
    destruct (memset_spec r3 m2 al_rom data n (Z_to_bv 64 0x1a434) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12)
      as (r4 & RUN4 & W10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |].
    replace (Z_to_bv 64 0x1a434) with (0x1a434 : word) by (apply bv_eq; reflexivity).
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
    assert (NEspd : Z_to_bv 64 pixs <> Z_to_bv 64 data) by (intros E; rewrite E in Lps; rewrite Lps in L0d; discriminate).
    assert (PXd5 : PIXat M5 pixd (hdv w h d cd data)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; exact (EQ5 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) Hx)]).
    assert (PXs5 : PIXat M5 pixs (hdv w h d cm datas)) by (apply (PIXat_frame m2); [exact PXs2 | intros x Hx; exact (EQ5 pixs 64%Z x Lps1 NEspd ltac:(lia) ltac:(lia) Hx)]).
    assert (CE5 : cells5 M5 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
    { destruct CE2 as (C1 & C2 & C3 & C4 & C5). unfold cells5.
      repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT5; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]). }
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (rewrite (AG4 2) by (cbv; intuition discriminate); exact V2).
    assert (X8 : getr r4 8 = Z_to_bv 64 pixd) by (rewrite (AG4 8) by (cbv; intuition discriminate); exact V8).
    assert (X9 : getr r4 9 = Z_to_bv 64 pixs) by (rewrite (AG4 9) by (cbv; intuition discriminate); rewrite V9; exact E9).
    assert (X18 : getr r4 18 = Z_to_bv 64 n) by (rewrite (AG4 18) by (cbv; intuition discriminate); rewrite V18; exact E18).
    destruct (pcp_C al_rom r4 M5 s pixd pixs (hdv w h d cd data) (hdv w h d cm datas) n ltac:(lia) ltac:(lia) ALp PXd5 PXs5
                ltac:(cbn; exact ALd) ltac:(cbn; exact ALds) ltac:(lia) X2 X8 X9 X18)
      as (r5 & RUN5 & Y2 & Y1 & Y10 & Y11 & Y12 & Y8 & Y9 & Y18 & AG5). cbn [p_data hdv] in Y10, Y11.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN5 |].
    (* [comment removed for export] *)
    destruct (blk_rdn C A1 M5 _ datas n (Z.to_nat n) CK HW5 Lds1 ltac:(lia) ltac:(lia) ltac:(lia)) as (bs & Hsrc & Hlen).
    pose proof (blk_apart C A1 M5 _ _ _ _ _ CK HW5 Lds1 L1d NEsd ltac:(lia) ltac:(lia)) as APsd. rewrite !u_Z2bv in APsd by lia.
    assert (HOKm : mcH M5 (Z_to_bv 64 data) (Z_to_bv 64 datas) n bs).
    { constructor; rewrite ?u_Z2bv by lia; [lia | exact Hlen | rewrite Hlen; exact Hsrc | rewrite Hlen; exact (blk_sok C A1 M5 _ data n CK HW5 L1d ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | lia]. }
    apply box_i in APsd.
    destruct (ref_memcpy M5 _ _ n bs al_rom HOKm r5 (Z_to_bv 64 0x1a50c) ltac:(red; apply bv_eq; reflexivity) Y1 Y10 Y11 Y12) as (r6 & RUN6 & KP6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN6 |].
    replace (Z_to_bv 64 0x1a50c) with (0x1a50c : word) by (apply bv_eq; reflexivity).
    set (M6 := wbytes M5 (Z_to_bv 64 data) bs) in *.
    assert (HW6 : W C A1 M6 (with_vmmaps vm1 md)).
    { subst M6. apply (W_store_blk C A1 M5 _ (Z_to_bv 64 data) (Z_to_bv 64 data) n bs CK HW5 L1d L00d); rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
    assert (PM6 : POSTM C A s m M6).
    { eapply POSTM_trans; [exact PM5|]. subst M6. apply (POSTM_blk C A A1 M5 _ (Z_to_bv 64 data) (Z_to_bv 64 data) n bs s CK HW5 L1d L0d SUBa); rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
    assert (OUT6 : forall x : word, ~ (data <= u x < data + n)%Z -> M6 x = M5 x).
    { intros x Hx. subst M6. apply wbytes_outside; rewrite Hlen, u_Z2bv by lia; lia. }
    assert (EQ6 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 data -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z -> (p <= u x < p + k)%Z -> M6 x = M5 x).
    { intros p k x L NE' G0 K0 Hx. apply OUT6.
      pose proof (blk_apart C A1 m2 _ _ _ _ _ CK HWa L L1d NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. lia. }
    assert (PXd6 : PIXat M6 pixd (hdv w h d cd data)) by (apply (PIXat_frame M5); [exact PXd5 | intros x Hx; exact (EQ6 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) Hx)]).
    assert (CE6 : cells5 M6 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
    { eapply (cells5_out M5 _ data (data + n)); [exact OUT6 | lia | lia | lia | exact CE5]. }
    assert (K2 : getr r6 2 = getr r5 2) by (apply KP6; in_kept). assert (K8 : getr r6 8 = getr r5 8) by (apply KP6; in_kept).
    assert (K3 : getr r6 3 = getr r5 3) by (apply KP6; in_kept). assert (K4 : getr r6 4 = getr r5 4) by (apply KP6; in_kept).
    assert (K20 : getr r6 20 = getr r5 20) by (apply KP6; in_kept). assert (K21 : getr r6 21 = getr r5 21) by (apply KP6; in_kept).
    assert (K22 : getr r6 22 = getr r5 22) by (apply KP6; in_kept). assert (K23 : getr r6 23 = getr r5 23) by (apply KP6; in_kept).
    assert (K24 : getr r6 24 = getr r5 24) by (apply KP6; in_kept). assert (K25 : getr r6 25 = getr r5 25) by (apply KP6; in_kept).
    assert (K26 : getr r6 26 = getr r5 26) by (apply KP6; in_kept). assert (K27 : getr r6 27 = getr r5 27) by (apply KP6; in_kept).
    destruct (pcp_D al_rom r6 M6 s pixd ret _ _ _ _ ltac:(lia) ltac:(lia) Hret CE6 ltac:(rewrite K2; exact Y2) ltac:(rewrite K8; exact Y8))
      as (r7 & RUN7 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & Z19 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
    apply (HK A1 M6 vm1 r7 HW6).
    + apply cs_kept_intro; csr; try reflexivity. all: rewrite ?Z8, ?Z9, ?Z18, ?Z19; try reflexivity.
      all: rewrite ?K3, ?K4, ?K20, ?K21, ?K22, ?K23, ?K24, ?K25, ?K26, ?K27; csr; reflexivity.
    + exact PM6.
    + right. exists pixd, cd, data. split; [exact Z10|].
      unfold pixt_new. rewrite <- En. do 13 (split; [assumption|]). split; [exact PXd6|].
      destruct CMR as [[CD0 LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & LAcd & LAad & L00cd & L00ad & L2cd & L2ad & CM4 & LEQ)]; [left; split; [exact CD0 | exact LEQ] | right].
      exists ad. do 16 (split; [assumption|]). split; [| exact LEQ].
      assert (NEw1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
      apply (CMAPat_frame m2); [exact CM4|]. intros x Hx. rewrite (EQ6 cd 24%Z x L2cd NEw1 ltac:(lia) ltac:(lia) Hx). exact (EQ5 cd 24%Z x L2cd NEw1 ltac:(lia) ltac:(lia) Hx).
    + exact Hrm1.
Qed.

End PixCopy.
