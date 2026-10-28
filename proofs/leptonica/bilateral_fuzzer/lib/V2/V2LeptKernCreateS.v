(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptBaseK V2LeptErr V2KernUb V2LeptKernSegs2 V2LeptKernC2dS V2_code_kern.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit LeptRoomK LeptRoomBL.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KernCreate.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma live_apart : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Hn Hk.
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X];
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.

Lemma zbv_ne : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b Ha Hb NE E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. Qed.

(* [comment removed for export] *)
Definition kern (C : lctx) (A A' : AS) (m' : word -> option byte) (kel arr h w : Z) (rows : Z -> Z) : Prop :=
  (1 <= kel)%Z /\ (kel + 24 <= alloc_top (c_vm C))%Z /\ (kel mod 16 = 0)%Z /\
  live A' (Z_to_bv 64 kel) = Some 24%Z /\ live A (Z_to_bv 64 kel) = None /\ live (c_A0 C) (Z_to_bv 64 kel) = None /\
  rdn SEGS m' (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) /\
  rdn SEGS m' (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS m' (Z_to_bv 64 (kel + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 arr)) /\
  (1 <= arr)%Z /\ (arr + 8 * h <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\ kel <> arr /\
  live A' (Z_to_bv 64 arr) = Some (8 * h)%Z /\ live A (Z_to_bv 64 arr) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  (forall i, (0 <= i < h)%Z ->
      (1 <= rows i)%Z /\ (rows i + 4 * w <= alloc_top (c_vm C))%Z /\ (rows i mod 16 = 0)%Z /\ rows i <> arr /\ rows i <> kel /\
      live A' (Z_to_bv 64 (rows i)) = Some (4 * w)%Z /\ live A (Z_to_bv 64 (rows i)) = None /\ live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\
      rdn SEGS m' (Z_to_bv 64 (arr + 8 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (rows i)))) /\
  (forall i j, (0 <= i < h)%Z -> (0 <= j < h)%Z -> i <> j -> rows i <> rows j) /\
  (forall q, q <> Z_to_bv 64 kel -> q <> Z_to_bv 64 arr -> (forall i, (0 <= i < h)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q).

Lemma kernelCreate_core : forall C A m md regs (s w h : Z) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 h -> getr regs 11 = Z_to_bv 64 w -> (1 <= w <= 100000)%Z -> (1 <= h <= 100000)%Z -> (w * h < 2 ^ 29)%Z ->
  aroom A (m_vmmaps md) kR bR -> (RK_kern h <= kR)%Z -> (RB_kernS h w <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists kel arr rows, getr regs' 10 = Z_to_bv 64 kel /\ kern C A A' m' kel arr h w rows) ->
     aroom A' vm' (kR - RK_kern h) (bR - RB_kernS h w) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x382d0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h ret S kR bR CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hw Hh Hwh HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  rewrite RK_kern_c2d in HRK. rewrite RB_kernS_c2dS in HRB.
  pose proof (alloc_margin_ge 24 ltac:(lia)) as G24. pose proof (RB_c2dS_nonneg h w ltac:(lia) ltac:(lia)) as GC2.
  assert (GK2 : (0 <= RK_c2d h)%Z) by (unfold RK_c2d; lia).
  destruct (kc_A al_rom regs m s w h ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hwh (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := KCF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold KCF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (CE1 : rdn SEGS M1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
                rdn SEGS M1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
                rdn SEGS M1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { subst M1. unfold KCF. repeat split; rdn_chain. }
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  replace (0x3c0f8 : word) with (Z_to_bv 64 0x3c0f8) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 _ r1 1 24 kR bR (Z_to_bv 64 0x38398) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           HRM ltac:(lia) ltac:(change (1 * 24)%Z with 24%Z; lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa HRMa. rewrite ?with_vmmaps_twice in HWa |- *.
  change (1 * 24)%Z with 24%Z in *.
  replace (Z_to_bv 64 0x38398) with (0x38398 : word) by (apply bv_eq; reflexivity).
  destruct CE1 as (C1 & C2 & C3).
  assert (D1 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia); exact C1).
  assert (D2 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia); exact C2).
  assert (D3 : rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia); exact C3).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  assert (E8 : getr r2 8 = Z_to_bv 64 w) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 h) by (csr; reflexivity).
  pose proof (u64_range res) as Hru.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (kel := u res) in *. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
  assert (Hkel : (1 <= kel)%Z /\ (kel + 24 <= alloc_top (c_vm C))%Z) by (unfold round16 in TOP; change ((24 + 15) / 16)%Z with 2%Z in TOP; lia).
  clearbody kel.
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  destruct (kc_B1 al_rom r2 m1 (s - 32) w h kel ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite <- (Z.add_0_r kel); apply mod16_plus_mod8; [exact AL16 | reflexivity])
              (W_sok_blk C A1 m1 _ _ _ kel 8 CK HWa L1 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              E2 Hres E8 E9) as (r3 & RUN3 & P2 & P1 & P10 & P11 & P8 & P9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  set (M2 := wbytes (wbytes m1 _ _) _ _).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
  { subst M2.
    apply (WP_blk C A A1 m _ _ (Z_to_bv 64 kel) _ 24); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    apply (WP_blk C A A1 m _ _ (Z_to_bv 64 kel) _ 24); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HWa | exact PMa']. }
  destruct WP2 as [HW2 PM2].
  assert (OUT2 : forall x : word, ~ (kel <= u x < kel + 8)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Ksy : rdn SEGS M2 (Z_to_bv 64 kel) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))) by (subst M2; rdn_chain).
  assert (Ksx : rdn SEGS M2 (Z_to_bv 64 (kel + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))) by (subst M2; rdn_chain).
  assert (P4 : getr r3 4 = Z_to_bv 64 0x56270) by (rewrite (AG3 4) by (cbv; intuition discriminate); exact E4).
  apply (create2dFloatArray_W C A1 M2 _ r3 (s - 32) w h (Z_to_bv 64 0x383bc) S (kR - 1) (bR - alloc_margin 24) CK HW2 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) P1 ltac:(red; apply bv_eq; reflexivity) P4 P10 P11 Hw Hh HRMa ltac:(lia) ltac:(lia)).
  intros A3 m3 vm3 r4 arr rows HW3 CS3 PM3 A4a KR HRM3. rewrite ?with_vmmaps_twice in HW3 |- *.
  replace (Z_to_bv 64 0x383bc) with (0x383bc : word) by (apply bv_eq; reflexivity).
  pose proof PM3 as [F3 LK3].
  assert (D1' : rdn SEGS m3 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 32) M2 m3 (s - 8) 8 CK F3) by (cbn; lia). rewrite <- D1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply OUT2. cbn in Hx. lia. }
  assert (D2' : rdn SEGS m3 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 32) M2 m3 (s - 16) 8 CK F3) by (cbn; lia). rewrite <- D2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply OUT2. cbn in Hx. lia. }
  assert (D3' : rdn SEGS m3 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 32) M2 m3 (s - 24) 8 CK F3) by (cbn; lia). rewrite <- D3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply OUT2. cbn in Hx. lia. }
  assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (Y8 : getr r4 8 = Z_to_bv 64 kel) by (csr; reflexivity).
  assert (Y4 : getr r4 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  pose proof KR as (Ga & TOPa & ALa & La & LaA1 & La0 & ROWS & DIST & RQ).
  assert (Lk3 : live A3 (Z_to_bv 64 kel) = Some 24%Z).
  { rewrite (RQ (Z_to_bv 64 kel)); [exact L1 | intros E; rewrite E, LaA1 in L1; discriminate |].
    intros i Hi E. destruct (ROWS i Hi) as (_ & _ & _ & _ & _ & LiA1 & _). rewrite E, LiA1 in L1. discriminate. }
  assert (NEka : kel <> arr) by (intros E; rewrite E, LaA1 in L1; discriminate).
  destruct (kc_C1 al_rom r4 m3 s kel arr ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret
              (W_sok_blk C A3 m3 _ _ _ (kel + 16) 8 CK HW3 Lk3 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              ltac:(lia) D1' D2' D3' Y2 A4a Y8) as (r5 & RUN5 & V2 & V1 & V10 & V8 & V9 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
  set (M4 := wbytes m3 _ _).
  assert (SUB3 : sub_live A A3).
  { intros q k Lq. pose proof (SUBa q k Lq) as Lq1. rewrite (RQ q); [exact Lq1 | intros ->; rewrite Lq1 in LaA1; discriminate |].
    intros i Hi ->. destruct (ROWS i Hi) as (_ & _ & _ & _ & _ & LiA1 & _). rewrite Lq1 in LiA1. discriminate. }
  assert (PM3' : POSTM C A s m m3) by (eapply POSTM_trans; [exact PM2 | apply (POSTM_sub C A A1 _ _ _ SUBa); eapply POSTM_mono; [|exact PM3]; lia]).
  assert (WP4 : W C A3 M4 (with_vmmaps vm3 md) /\ POSTM C A s m M4).
  { subst M4. apply (WP_blk C A A3 m m3 _ (Z_to_bv 64 kel) _ 24 _ s CK (conj HW3 PM3') Lk3 L0 L00 SUB3); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
  destruct WP4 as [HW4 PM4].
  assert (OUT4 : forall x : word, ~ (kel + 16 <= u x < kel + 24)%Z -> M4 x = m3 x).
  { intros x Hx. subst M4. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  apply (HK A3 M4 vm3 r5 HW4).
  - apply cs_kept_intro; csr; reflexivity.
  - exact PM4.
  - exists kel, arr, rows. split; [exact V10|].
    pose proof (live_apart C A3 m3 _ _ _ _ _ CK HW3 Lk3 La ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as APka. rewrite !u_Z2bv in APka by lia.
    split; [lia|]. split; [lia|]. split; [exact AL16|]. split; [exact Lk3|]. split; [exact L0|]. split; [exact L00|].
    split. { subst M4. rewrite rdn_wbytes_out_Z; [| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia].
             rewrite <- Ksy. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
             exact (LIVK_at A1 M2 m3 kel 24 x LK3 L1 ltac:(lia) ltac:(lia) ltac:(lia)). }
    split. { subst M4. rewrite rdn_wbytes_out_Z; [| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia].
             rewrite <- Ksx. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
             exact (LIVK_at A1 M2 m3 kel 24 x LK3 L1 ltac:(lia) ltac:(lia) ltac:(lia)). }
    split; [subst M4; apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia|].
    split; [exact Ga|]. split; [exact TOPa|]. split; [exact ALa|]. split; [exact NEka|]. split; [exact La|]. split; [exact (eq_trans (eq_sym (LEQ (Z_to_bv 64 arr) ltac:(apply not_eq_sym; apply zbv_ne; lia))) LaA1) |].
    split; [exact La0|]. split; [|split; [exact DIST|]].
    + intros i Hi. destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
      assert (NEik : rows i <> kel) by (intros E; rewrite <- E, G6 in L1; discriminate).
      pose proof (live_apart C A3 m3 _ _ _ _ _ CK HW3 Lk3 G5 ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as APki. rewrite !u_Z2bv in APki by lia.
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact NEik|]. split; [exact G5|].
      split; [rewrite <- (LEQ (Z_to_bv 64 (rows i)) ltac:(apply zbv_ne; lia)); exact G6|]. split; [exact G7|].
      subst M4. rewrite rdn_wbytes_out_Z; [exact G8|]. rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
      pose proof (live_apart C A3 m3 _ _ _ _ _ CK HW3 Lk3 La ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as AP2. rewrite !u_Z2bv in AP2 by lia. lia.
    + intros q NQk NQa NQr. rewrite (RQ q NQa NQr). exact (LEQ q NQk).
  - replace (kR - RK_kern h)%Z with (kR - 1 - RK_c2d h)%Z by (rewrite RK_kern_c2d; lia).
    replace (bR - RB_kernS h w)%Z with (bR - alloc_margin 24 - RB_c2dS h w)%Z by (rewrite RB_kernS_c2dS; lia).
    exact HRM3.
Qed.

Theorem kernelCreate_S_W : forall C A m md regs (s w h : Z) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 h -> getr regs 11 = Z_to_bv 64 w -> (1 <= w <= 100000)%Z -> (1 <= h <= 100000)%Z -> (w * h < 2 ^ 29)%Z ->
  aroom A (m_vmmaps md) kR bR -> (RK_kern h <= kR)%Z -> (RB_kernS h w <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists kel arr rows, getr regs' 10 = Z_to_bv 64 kel /\ kern C A A' m' kel arr h w rows) ) ->
     aroom A' vm' (kR - RK_kern h) (bR - RB_kernS h w) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x382d0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h ret S kR bR CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hw Hh Hwh HRM HRK HRB HK.
  apply (kernelCreate_core C A m md regs s w h ret S kR bR CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hw Hh Hwh HRM HRK HRB).
  intros A' m' vm' regs' HW' CS PM EX HR. exact (HK A' m' vm' regs' HW' CS PM (or_intror EX) HR).
Qed.

End KernCreate.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
