(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptStderr O17LeptBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17CL7a.
Import O17CL7a.O17LeptErr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17_code_132e8_14000 O17_code_14000_15000 O17_code_16000_17000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].


Lemma sllw_1 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z -> v_sllw (Z_to_bv 64 1) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ d).
Proof. intros d [->|[->|[->| ->]]]; apply bv_eq; vm_compute; reflexivity. Qed.

Section Cmap.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).


(* [comment removed for export] *)
Definition cmap_new (C : lctx) (A A' : AS) (m' : word -> option byte) (cm arr d : Z) : Prop :=
  (1 <= cm)%Z /\ (cm + 24 <= alloc_top (c_vm C))%Z /\ (cm mod 16 = 0)%Z /\
  (1 <= arr)%Z /\ (arr + 4 * 2 ^ d <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\ cm <> arr /\
  live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 arr) = None /\
  live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  live A' (Z_to_bv 64 cm) = Some 24%Z /\ live A' (Z_to_bv 64 arr) = Some (4 * 2 ^ d)%Z /\
  (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 arr -> live A' q = live A q) /\
  CMAPat m' cm (CMAPV arr d (2 ^ d) 0 0).





Section SegsD.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pd_A : forall regs m (s pp cm arr : Z) (ret : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (1 <= cm)%Z -> (cm + 24 < 2 ^ 64)%Z -> (0 <= arr < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 cm) ->
    rdn SEGS m (Z_to_bv 64 cm) 8 = Some (Z_to_le_bytes 8 arr) ->
    (cm + 24 <= s - 32 \/ s <= cm)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x149c8 : word) m rom)
                  (mkst regs' (0x16604 : word)
                        (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x149f0
      /\ getr regs' 10 = Z_to_bv 64 arr /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 cm
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pp cm arr ret Hs Hpp Hpp64 Hcm Hcm64 Harr SOK Rpp Rarr DJ H2 H1 H10.
    eexists. split.
    - zv F_148cc D_148cc (Z_to_bv 64 (s - 32)).
      stepST F_148d0 D_148d0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_148d4 D_148d4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_148d8 D_148d8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_148dc D_148dc ltac:(condZ).
      sn F_148e0 D_148e0.
      stepLD F_148e4 D_148e4 (Z_to_le_bytes 8 cm) (Z_to_bv 64 cm) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_ft F_148e8 D_148e8 ltac:(condZ).
      stepLD F_148ec D_148ec (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      sn F_148f0 D_148f0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_B : forall regs m (cm : Z),
    getr regs 9 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (0x149f0 : word) m rom) (mkst regs' (0x16604 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 1 = Z_to_bv 64 0x149f8
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cm H9.
    eexists. split.
    - sn F_148f4 D_148f4.
      sn F_148f8 D_148f8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_C : forall regs m (s pp : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x149f8 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v Hs Hpp Hpp64 Hret SOK R8 R16 R24 H2 H8.
    eexists. split.
    - stepST F_148fc D_148fc (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_14900 D_14900.
      stepLD8 F_1493c D_1493c ret.
      stepLD8 F_14940 D_14940 s0v.
      stepLD8 F_14944 D_14944 s1v.
      zv F_14948 D_14948 (Z_to_bv 64 s).
      stepret F_1494c D_1494c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsD.

(* [comment removed for export] *)
Theorem pixcmapDestroy_W : forall C A m md regs (s pp cm : Z) (cv : cmapv) (k : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x30520 ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 cm) ->
  CMAPat m cm cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> live A (Z_to_bv 64 (c_arr cv)) = Some k ->
  live (c_A0 C) (Z_to_bv 64 cm) = None -> live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None -> cm <> c_arr cv ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 cm) = None -> live A' (Z_to_bv 64 (c_arr cv)) = None ->
     (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 (c_arr cv) -> live A' q = live A q) ->
     POSTM C A' (pp + 8) m m' ->
     rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x149c8 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp cm cv k ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 H10 Rpp CM Lcm Larr L0cm L0arr NE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold ALLOC_STACK in Hlo.
  pose proof CM as (Ccm0 & Ccm64 & CWF & _). pose proof (cf_arr _ CWF) as Rarr.
  set (arr := c_arr cv) in *.
  pose proof (alloc_top_lt (m_vmmaps md)) as ATL. unfold two_pow_64 in ATL. destruct (w_vm _ _ _ _ HW) as (_ & VT & _).
  (* [comment removed for export] *)
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
  assert (NEw : Z_to_bv 64 cm <> Z_to_bv 64 arr).
  { intros E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. }
  destruct (pd_A al_rom regs m s pp cm arr ret ltac:(lia) Hpp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp (CMAP_rd_arr SEGS m cm cv CM) ltac:(lia) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A (pp + 8) m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x30520) by (rewrite (AG1 4) by notin_lit; exact H4).
  replace (0x16604 : word) with (Z_to_bv 64 0x16604) by (apply bv_eq; reflexivity).
  apply (W_free16 C A M1 md r1 (Z_to_bv 64 arr) (Z_to_bv 64 0x149f0) k (s - 32) S CK HW1 Q10 Larr L0arr Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 HWa CSa La LEQa PMa HRTa.
  replace (Z_to_bv 64 0x149f0) with (0x149f0 : word) by (apply bv_eq; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 cm) by (csr; reflexivity).
  destruct (pd_B al_rom r2 m1 cm E9) as (r3 & RUN3 & P10 & P1 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (P4 : getr r3 4 = Z_to_bv 64 0x30520) by (csr; reflexivity).
  assert (P2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (Lcm1 : live A1 (Z_to_bv 64 cm) = Some 24%Z) by (rewrite (LEQa _ NEw); exact Lcm).
  replace (0x16604 : word) with (Z_to_bv 64 0x16604) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 m1 _ r3 (Z_to_bv 64 cm) (Z_to_bv 64 0x149f8) 24 (s - 32) S CK HWa P10 Lcm1 L0cm P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 HWb CSb Lb LEQb PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
  replace (Z_to_bv 64 0x149f8) with (0x149f8 : word) by (apply bv_eq; reflexivity).
  assert (V2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (V8 : getr r4 8 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (FR2 : FRM C (s - 32) M1 m2) by (eapply FRM_trans; [exact (proj1 PMa) | exact (proj1 PMb)]).
  destruct (pd_C al_rom r4 m2 s pp ret (getr regs 8) (getr regs 9) ltac:(lia) Hpp ltac:(lia) Hret) as (r5 & RUN5 & X2 & X1 & X8 & X9 & AG5).
  { apply (W_sok_win C A2 m2 _ pp 8 CK HWb); [lia | cbn; lia]. }
  { rewrite (FRM_rdn16 C (s - 32) M1 m2 (s - 8) 8 CK FR2) by (cbn; lia). subst M1. rdn_solve. }
  { rewrite (FRM_rdn16 C (s - 32) M1 m2 (s - 16) 8 CK FR2) by (cbn; lia). subst M1. rdn_solve. }
  { rewrite (FRM_rdn16 C (s - 32) M1 m2 (s - 24) 8 CK FR2) by (cbn; lia). subst M1. rdn_solve. }
  { exact V2. } { exact V8. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
  assert (WP3 : W C A2 (wbytes m2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm2 md) /\
                POSTM C A2 (pp + 8) m2 (wbytes m2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0)))).
  { apply (WP_win C A2 A2 m2 m2 _ _ _ (pp + 8) CK); [split; [exact HWb | apply POSTM_refl] | apply sub_live_refl | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]. }
  destruct WP3 as [HW3 PM3].
  apply (HK A2 _ vm2 r5).
  - exact HW3.
  - apply cs_kept_intro; csr; try reflexivity.
  - exact Lb.
  - rewrite (LEQb _ (not_eq_sym NEw)). exact La.
  - intros q N1 N2. rewrite (LEQb q N1). apply LEQa. exact N2.
  - (* [comment removed for export] *)
    eapply POSTM_trans; [|exact PM3].
    eapply POSTM_trans; [apply (POSTM_sub C A2 A); [|exact PM1]|].
    { intros q kq Lq. destruct (bv_eq_dec _ q (Z_to_bv 64 cm)) as [->|N1]; [congruence|].
      rewrite (LEQb q N1) in Lq. destruct (bv_eq_dec _ q (Z_to_bv 64 arr)) as [->|N2]; [congruence|].
      rewrite (LEQa q N2) in Lq. exact Lq. }
    eapply POSTM_trans; [apply (POSTM_sub C A2 A1); [| eapply POSTM_mono; [|exact PMa]; lia]|].
    { intros q kq Lq. destruct (bv_eq_dec _ q (Z_to_bv 64 cm)) as [->|N1]; [congruence|]. rewrite (LEQb q N1) in Lq. exact Lq. }
    eapply POSTM_mono; [|exact PMb]. lia.
  - rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - room_tac.
Qed.

End Cmap.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
