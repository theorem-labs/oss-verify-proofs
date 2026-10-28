(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23Memset V23_code_morphA_clear.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptClearAll.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Definition PC_pixClearAll : Z := 0x6ff30.
Definition CLR_STACK : Z := 16 + LSF.     (* [comment removed for export] *)

Section ClearAll.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pca_A : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix mod 8 = 0)%Z -> PIXat m pix v -> PIXat (O23LeptClearAll.FR1 m s ret) pix v ->
    (0 <= p_wpl v * p_h v)%Z -> (4 * (p_wpl v * p_h v) < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6ff30 : word) m rom) (mkst regs' (0x11e6d4 : word) (O23LeptClearAll.FR1 m s ret) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x6ff6c
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl v * p_h v))
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 Hpix AL8 PX PX1 Hn Hn31 SOK H2 H1 H10.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF). pose proof (wf_h _ WF). pose proof (wf_data _ WF).
    unfold O23LeptClearAll.FR1 in *. eexists. split.
    - stepb_ft F_6ff30 D_6ff30 ltac:(condZ).
      guard8 F_6ff34 D_6ff34 AL8.
      stepb_ft F_6ff38 D_6ff38 ltac:(condZ).
      stepLD F_6ff3c D_6ff3c (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepLD F_6ff40 D_6ff40 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepiv F_6ff44 D_6ff44 (Z_to_bv 64 (4 * p_wpl v)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_6ff48 D_6ff48. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_6ff4c D_6ff4c (Z_to_bv 64 (4 * (p_wpl v * p_h v))).
      sn F_6ff50 D_6ff50. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_6ff54 D_6ff54 ltac:(condZ).
      zv F_6ff58 D_6ff58 (Z_to_bv 64 (s - 16)).
      stepST F_6ff5c D_6ff5c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepLD F_6ff60 D_6ff60 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX1)) ltac:(apply lez8; lia).
      sn F_6ff64 D_6ff64. sn F_6ff68 D_6ff68.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pca_B : forall regs m (s : Z) (ret : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    getr regs 2 = Z_to_bv 64 (s - 16) ->
    exists regs',
      msteps SEGS (mkst regs (0x6ff6c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 10]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 Hret R8 H2. eexists. split.
    - sn F_6ff6c D_6ff6c.
      stepLD8 F_6ff70 D_6ff70 ret.
      zv F_6ff74 D_6ff74 (Z_to_bv 64 s).
      stepret F_6ff78 D_6ff78 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
Theorem pixClearAll_W : forall C Ar A m md regs (s pix k : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CLR_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pix ->
  PIXat m pix v -> live A (Z_to_bv 64 pix) = Some 64%Z -> Z_to_bv 64 pix <> Z_to_bv 64 (p_data v) ->
  (1 <= p_wpl v * p_h v)%Z -> (4 * (p_wpl v * p_h v) < 2 ^ 31)%Z ->
  live A (Z_to_bv 64 (p_data v)) = Some k -> (4 * (p_wpl v * p_h v) <= k)%Z ->
  live Ar (Z_to_bv 64 (p_data v)) = None -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pix v ->
     (forall i, (0 <= i < 4 * (p_wpl v * p_h v))%Z -> m' (Z_to_bv 64 (p_data v + i)) = Some (Z_to_bv 8 0)) ->
     (forall x : word, ~ (p_data v <= u x < p_data v + 4 * (p_wpl v * p_h v))%Z -> ~ scratch C s x -> m' x = m x) ->
     getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6ff30 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix k v ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 PX Lp NEpd Hn Hn31 Ld Hk Ld0 Ld00 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold CLR_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF). pose proof (wf_h _ WF). pose proof (wf_data _ WF).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) k CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Ld NEpd) as DJ. rewrite !u_Z2bv in DJ by lia.
  unfold round16 in DJ at 1. change ((64 + 15) / 16)%Z with 4%Z in DJ. pose proof (round16_ge k ltac:(lia)).
  pose proof (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (PX1 : PIXat (O23LeptClearAll.FR1 m s ret) pix v).
  { apply (PIXat_frame m); [exact PX|]. intros x Hx. unfold O23LeptClearAll.FR1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  destruct (pca_A al_rom regs m s pix v ret ltac:(lia) ltac:(lia) ltac:(lia) AL8 PX PX1 ltac:(lia) Hn31 SOK H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (O23LeptClearAll.FR1 m s ret) md /\ POSTM C Ar s m (O23LeptClearAll.FR1 m s ret)) by (unfold O23LeptClearAll.FR1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (R8 : rdn SEGS (O23LeptClearAll.FR1 m s ret) (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (unfold O23LeptClearAll.FR1; rdn_solve).
  assert (OUT1 : forall x : word, ~ (s - 8 <= u x < s)%Z -> O23LeptClearAll.FR1 m s ret x = m x).
  { intros x Hx. unfold O23LeptClearAll.FR1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  set (M1 := O23LeptClearAll.FR1 m s ret) in *.
  assert (SOKd : store_ok SEGS M1 (Z_to_bv 64 (p_data v)) (Z.to_nat (4 * (p_wpl v * p_h v))) = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (M1 x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A M1 _ (Z_to_bv 64 (p_data v)) _ x CK HW1 Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  apply (memset_at md r1 M1 al_rom (p_data v) (4 * (p_wpl v * p_h v)) (Z_to_bv 64 0x6ff6c) S
           (w_pure _ _ _ _ HW) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) Q1 Q10 Q11 Q12).
  intros r2 A10 AG2.
  pose proof (memset_post_mem M1 (p_data v) (4 * (p_wpl v * p_h v)) ltac:(lia) ltac:(lia)) as (Z0 & ZO & ZG).
  set (M2 := zf M1 (p_data v) [(0, 4 * (p_wpl v * p_h v))]%Z) in *.
  assert (CH : forall a, M2 a <> M1 a -> (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) (p_data v)) as [Hl|Hl]; [exfalso; apply NE; apply ZO; lia|].
    destruct (Z_lt_ge_dec (u a) (p_data v + 4 * (p_wpl v * p_h v))) as [Hh|Hh]; [lia | exfalso; apply NE; apply ZO; lia]. }
  replace (Z_to_bv 64 0x6ff6c) with (0x6ff6c : word) by (apply bv_eq; reflexivity).
  assert (R8' : rdn SEGS M2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite <- R8. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply ZO. lia. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (pca_B al_rom r2 M2 s ret ltac:(lia) ltac:(lia) Hret R8' E2) as (r3 & RUN3 & U2 & U1 & U10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN3 |].
  apply (HK M2 r3).
  - apply (W_local C A M1 md M2 s CK HW1 Hhi); [| exact ZG].
    intros a NE. right. exists (Z_to_bv 64 (p_data v)), k. rewrite u_Z2bv by lia.
    split; [exact Ld|]. split; [exact Ld00|]. pose proof (CH a NE). lia.
  - apply cs_kept_intro; csr; try reflexivity.
  - eapply POSTM_trans; [exact PM1|]. apply (POSTM_local C Ar A M1 md M2 s CK HW1 SUB).
    intros a NE. right. exists (Z_to_bv 64 (p_data v)), k. rewrite u_Z2bv by lia.
    split; [exact Ld|]. split; [exact Ld0|]. pose proof (CH a NE). lia.
  - apply (PIXat_frame M1); [exact PX1|]. intros x Hx. apply ZO. lia.
  - intros i Hi. exact (Z0 i Hi).
  - intros x Hx Hsc. rewrite ZO by lia. apply OUT1. intros Hx'. apply Hsc. unfold scratch. lia.
  - exact U10.
Qed.

End ClearAll.
