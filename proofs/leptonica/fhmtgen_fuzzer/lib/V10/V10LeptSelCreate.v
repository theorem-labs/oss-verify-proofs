(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSlots LeptSel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptSel_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10_code_fhFG.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptSelSegs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoom10.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section SelCreate.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsA.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma sca_A : forall regs m (s : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x26e30 : word) m rom)
                  (mkst regs' (0x2b0d0 : word)
                     (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                             (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                             (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x26e50
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 16 /\ getr regs' 8 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10.
    eexists. split.
    - zv F_26d34 D_26d34 (Z_to_bv 64 (s - 32)).
      stepST F_26d38 D_26d38 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_26d3c D_26d3c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_26d40 D_26d40 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_26d44 D_26d44. sn F_26d48 D_26d48. sn F_26d4c D_26d4c. sn F_26d50 D_26d50.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma sca_B : forall regs m (pa : Z),
    (1 <= pa)%Z -> (pa + 16 < 2 ^ 64)%Z -> (pa mod 8 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 pa) 16 = true ->
    getr regs 10 = Z_to_bv 64 pa -> getr regs 8 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x26e50 : word) m rom)
                  (mkst regs' (0x2b0d0 : word) (wbytes (wbytes m (Z_to_bv 64 pa) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                                                      (Z_to_bv 64 (pa + 4)) (word_to_le_bytes 4 (Z_to_bv 64 50))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x26e8c
      /\ getr regs' 10 = Z_to_bv 64 50 /\ getr regs' 11 = Z_to_bv 64 8 /\ getr regs' 9 = Z_to_bv 64 pa
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pa Hpa Hpa64 ALpa SOK H10 H8.
    eexists. split.
    - stepb_ft F_26d54 D_26d54 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_26d58 D_26d58 andi_7 ALpa. stepb_ft F_26d5c D_26d5c ltac:(condZ).        (* [comment removed for export] *)
      sn F_26d60 D_26d60. sn F_26d64 D_26d64. sn F_26d68 D_26d68. sn F_26d6c D_26d6c.
      stepb_ft F_26d70 D_26d70 ltac:(pin; vm_compute; reflexivity).                   (* [comment removed for export] *)
      sn F_26d74 D_26d74.
      stepST F_26d78 D_26d78 (Z_to_bv 64 pa) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepST F_26d7c D_26d7c (Z_to_bv 64 (pa + 4)) (Z_to_bv 64 50) ltac:(sok_in SOK).
      sn F_26d80 D_26d80. sn F_26d84 D_26d84. sn F_26d88 D_26d88. sn F_26d8c D_26d8c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.


  (* [comment removed for export] *)
  Lemma sca_C : forall regs m (s pa arr : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr < 2 ^ 64)%Z -> (1 <= pa)%Z -> (pa + 16 < 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pa) 16 = true -> (pa + 16 <= s - 32 \/ s <= pa)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 arr -> getr regs 9 = Z_to_bv 64 pa ->
    exists regs',
      msteps SEGS (mkst regs (0x26e8c : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (pa + 8)) (word_to_le_bytes 8 (Z_to_bv 64 arr))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pa /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pa arr ret s0v s1v Hs Hs64 Harr Hpa Hpa64 Hret SOKp DJ R8 R16 R24 H2 H10 H9.
    eexists. split.
    - stepST F_26d90 D_26d90 (Z_to_bv 64 (pa + 8)) (Z_to_bv 64 arr) ltac:(sok_in SOKp).
      sn F_26d94 D_26d94.
      stepLD8 F_26d98 D_26d98 ret.
      stepLD8 F_26d9c D_26d9c s0v.
      stepLD8 F_26da0 D_26da0 s1v.
      zv F_26da4 D_26da4 (Z_to_bv 64 s).
      stepret F_26da8 D_26da8 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsA.

(* [comment removed for export] *)
Lemma bok_of_calloc : forall C (res : word) (n : Z), (0 <= n)%Z -> u res <> 0%Z -> (u res mod 16 = 0)%Z ->
  (u res + round16 n <= alloc_top (c_vm C))%Z -> bok (alloc_top (c_vm C)) (u res) n.
Proof. intros C res n Hn Hnz Hal TOP. pose proof (u64_range res). pose proof (round16_ge n Hn). repeat split; [lia | lia | exact Hal]. Qed.

Theorem selaCreate_W : forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 0 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (2 <= kR)%Z -> (2 * RB10_small <= bR)%Z ->
  (forall A' m' vm' regs' (sela arr : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 sela ->
     (forall sels vs nms, sela_at (alloc_top (c_vm C)) A' m' sela arr 0 sels vs nms) ->
     live A (Z_to_bv 64 sela) = None -> live A (Z_to_bv 64 arr) = None ->
     live (c_A0 C) (Z_to_bv 64 sela) = None -> live (c_A0 C) (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 sela -> q <> Z_to_bv 64 arr -> live A' q = live A q) ->
     aroom A' vm' (kR - 2) (bR - 2 * RB10_small) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x26e30 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 kR bR Hrm Hrk Hrb HK.
  pose proof (alloc_margin_small_le (1 * 16) ltac:(lia)) as MG1. pose proof (alloc_margin_small_le (50 * 8) ltac:(lia)) as MG2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold CALLOC_STACK, ALLOC_STACK in Hlo. unfold RB10_small in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (sca_A al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  replace (0x2b0d0 : word) with (Z_to_bv 64 0x2b0d0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 md r1 1 16 kR bR (Z_to_bv 64 0x26e50) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hroom1.
  replace (Z_to_bv 64 0x26e50) with (0x26e50 : word) by (apply bv_eq; reflexivity).
  assert (E2a : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8a : getr r2 8 = Z_to_bv 64 0) by (csr; reflexivity).
  assert (E4a : getr r2 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (bok_of_calloc C res (1 * 16) ltac:(lia) Hnz AL16 TOP) as Bpa.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (pa := u res) in *. clearbody pa. destruct Bpa as (Gpa & TOPpa & ALpa).
  rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
  assert (REC0 : RECat m1 pa (zflds [4; 4; 8]%nat)).
  { apply RECat_zero; [lia | cbn; lia | repeat constructor |]. cbn [flds_len zflds Nat.add]. intros i Hi.
    unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
  assert (SOKp1 : store_ok SEGS m1 (Z_to_bv 64 pa) 16 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m1 pa _ x REC0 ltac:(cbn; lia) E). }
  destruct (sca_B al_rom r2 m1 pa ltac:(lia) ltac:(lia) (bok_mod8 _ _ _ (conj Gpa (conj TOPpa ALpa))) SOKp1 Hres E8a) as (r3 & RUN3 & P2 & P1 & P10 & P11 & P9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  set (M2 := wbytes (wbytes m1 _ _) _ _).
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
  { subst M2.
    do 2 (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pa) _ 16); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    split; [exact HWa | exact PMa']. }
  destruct WP2 as [HW2 PM2].
  assert (REC2 : RECat M2 pa (sela_flds 0 50 0)).
  { subst M2. unfold sela_flds.
    eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 1 4);
      [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
    eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z)] _ 0 4);
      [ exact REC0 | cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity ]. }
  assert (P4 : getr r3 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  assert (P2' : getr r3 2 = Z_to_bv 64 (s - 32)) by (rewrite P2; exact E2a).
  replace (0x2b0d0 : word) with (Z_to_bv 64 0x2b0d0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A1 M2 _ r3 50 8 (kR - 1) (bR - alloc_margin (1 * 16)) (Z_to_bv 64 0x26e8c) (s - 32) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hroom1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 res2 HWb Hres2 CSb Hnz2 K0 K1 K00 KEQ ZERO2 AL16b TOPb PMb Hroom2. rewrite with_vmmaps_twice in HWb. rewrite with_vmmaps_twice.
  replace (Z_to_bv 64 0x26e8c) with (0x26e8c : word) by (apply bv_eq; reflexivity).
  assert (F2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (F9 : getr r4 9 = Z_to_bv 64 pa) by (csr; reflexivity).
  pose proof (bok_of_calloc C res2 (50 * 8) ltac:(lia) Hnz2 AL16b TOPb) as Barr.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  set (arr := u res2) in *. clearbody arr. destruct Barr as (Garr & TOParr & ALarr).
  rewrite Eres2 in Hres2, K0, K1, K00, KEQ.
  assert (NE : arr <> pa) by (intros E; rewrite E in K0; rewrite K0 in L1; discriminate L1).
  assert (REC4 : RECat m2 pa (sela_flds 0 50 0)).
  { apply (RECat_POSTM C A1 (s - 32) M2 m2 (Z_to_bv 64 pa) 16 _ _ REC2 PMb L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
  assert (SOKp2 : store_ok SEGS m2 (Z_to_bv 64 pa) 16 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (RECat_defined m2 pa _ x REC4 ltac:(cbn; lia) E). }
  assert (S8 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 8) 8 CK (proj1 PMb)) by (cbn; lia). subst M2.
    rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia).
    rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (S16 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 16) 8 CK (proj1 PMb)) by (cbn; lia). subst M2.
    rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia).
    rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (S24 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 32) M2 m2 (s - 24) 8 CK (proj1 PMb)) by (cbn; lia). subst M2.
    rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia).
    rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (PMb' : POSTM C A s m m2).
  { eapply POSTM_trans; [exact PM2|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
  destruct (sca_C al_rom r4 m2 s pa arr ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret SOKp2 ltac:(lia)
              S8 S16 S24 F2 Hres2 F9) as (r5 & RUN5 & V2 & V1 & V10 & V8 & V9 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
  set (M4 := wbytes m2 _ _).
  assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
  assert (Lpa2 : live A2 (Z_to_bv 64 pa) = Some 16%Z) by (rewrite (KEQ _ (zneq_w pa arr ltac:(lia) ltac:(lia) (not_eq_sym NE))); exact L1).
  assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C A s m M4).
  { subst M4.
    apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pa) _ 16); [exact CK | | exact Lpa2 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HWb | exact PMb']. }
  destruct WP4 as [HW4 PM4].
  apply (HK A2 M4 vm2 r5 pa arr HW4).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9; reflexivity.
  - exact PM4.
  - exact V10.
  - intros sels vs nms. split; [lia|]. split; [repeat split; lia|]. split; [exact Lpa2|].
    split.
    { subst M4. unfold sela_flds.
      eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 50%Z); (8%nat, 0%Z)] _ 2 8);
        [ exact REC4 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ]. }
    split; [repeat split; lia|]. split; [replace 400%Z with (50 * 8)%Z by lia; exact K1|]. split; [exact NE|].
    split; [intros i Hi; lia | intros i j p q Hi; lia].
  - exact L0.
  - rewrite <- (LEQ _ (zneq_w arr pa ltac:(lia) ltac:(lia) NE)). exact K0.
  - exact L00.
  - exact K00.
  - intros q N1 N2. rewrite (KEQ q N2). exact (LEQ q N1).
  - apply (aroom_mono A2 vm2 _ _ _ _ Hroom2); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lui_m10001 : v_addiw (Z_to_bv 64 18446744073709543424) (-1809) = Z_to_bv 64 (2 ^ 64 - 10001).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma addw_m10001 : forall n, (1 <= n <= 10000)%Z ->
  v_addw (Z_to_bv 64 n) (Z_to_bv 64 (2 ^ 64 - 10001)) = Z_to_bv 64 (2 ^ 64 + (n - 10001)).
Proof.
  intros n Hn. rewrite v_addw_Z. apply bv_eq. rewrite !u_Z2bv_mod. unfold sw32.
  replace ((n + (2 ^ 64 - 10001) + 2 ^ 31) mod 2 ^ 32)%Z with (n - 10001 + 2 ^ 31)%Z.
  2:{ replace (n + (2 ^ 64 - 10001) + 2 ^ 31)%Z with ((n - 10001 + 2 ^ 31) + 2 ^ 32 * 2 ^ 32)%Z by lia.
      rewrite Z_mod_plus_full. rewrite Z.mod_small; lia. }
  replace (n - 10001 + 2 ^ 31 - 2 ^ 31)%Z with ((2 ^ 64 + (n - 10001)) + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Section SegsC.
Variable rom : word -> option byte.

  Definition SCF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)).

  Definition sccells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
    rdn SEGS M (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v).

  Lemma sccells_SCF : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    sccells (SCF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20).
  Proof. intros m s ret regs Hs Hs64. unfold sccells, SCF. repeat split; rdn_chain. Qed.

  Lemma sccells_frame : forall M M' s ret s0v s1v s2v s3v s4v, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    sccells M s ret s0v s1v s2v s3v s4v -> (forall x : word, (s - 48 <= u x < s)%Z -> M' x = M x) -> sccells M' s ret s0v s1v s2v s3v s4v.
  Proof.
    intros M M' s ret s0v s1v s2v s3v s4v Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6) E.
    unfold sccells. repeat split;
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5 | rewrite <- C6];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition SC5F (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)).

  Definition sc5cells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v).

  Lemma sc5cells_SC5F : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    sc5cells (SC5F m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19).
  Proof. intros m s ret regs Hs Hs64. unfold sc5cells, SC5F. repeat split; rdn_chain. Qed.

  Lemma sc5cells_frame : forall M M' s ret s0v s1v s2v s3v, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    sc5cells M s ret s0v s1v s2v s3v -> (forall x : word, (s - 48 <= u x < s)%Z -> M' x = M x) -> sc5cells M' s ret s0v s1v s2v s3v.
  Proof.
    intros M M' s ret s0v s1v s2v s3v Hs Hs64 (C1 & C2 & C3 & C4 & C5) E.
    unfold sc5cells. repeat split;
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma scr_A : forall regs m (s sy sx : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 sy -> getr regs 11 = Z_to_bv 64 sx -> getr regs 12 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x27068 : word) m rom) (mkst regs' (0x2b0d0 : word) (SC5F m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x27098 /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 32
      /\ getr regs' 9 = Z_to_bv 64 sx /\ getr regs' 18 = Z_to_bv 64 sy /\ getr regs' 19 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 2; 9; 10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s sy sx ret Hs Hs64 SOK H2 H1 H10 H11 H12.
    eexists. split.
    - zv F_26f6c D_26f6c (Z_to_bv 64 (s - 48)).
      stepST F_26f70 D_26f70 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_26f74 D_26f74 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_26f78 D_26f78 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_26f7c D_26f7c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_26f80 D_26f80 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      sn F_26f84 D_26f84. sn F_26f88 D_26f88. sn F_26f8c D_26f8c. sn F_26f90 D_26f90. sn F_26f94 D_26f94. sn F_26f98 D_26f98.
      unfold SC5F. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma scr_B : forall regs m (sy sx sel : Z),
    (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (sel mod 8 = 0)%Z -> (0 <= sx < 2 ^ 31)%Z -> (0 <= sy < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 sel) 8 = true ->
    getr regs 10 = Z_to_bv 64 sel -> getr regs 9 = Z_to_bv 64 sx -> getr regs 18 = Z_to_bv 64 sy -> getr regs 19 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x27098 : word) m rom)
                  (mkst regs' (0x2716c : word) (wbytes (wbytes m (Z_to_bv 64 sel) (word_to_le_bytes 4 (Z_to_bv 64 sy)))
                                                      (Z_to_bv 64 (sel + 4)) (word_to_le_bytes 4 (Z_to_bv 64 sx))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x270e8 /\ getr regs' 10 = Z_to_bv 64 sy /\ getr regs' 11 = Z_to_bv 64 sx
      /\ getr regs' 8 = Z_to_bv 64 sel /\ getr regs' 9 = Z_to_bv 64 sx /\ getr regs' 18 = Z_to_bv 64 sy
      /\ regs_agree (fun r => In r [1; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs m sy sx sel Hk Hk64 ALk Hw Hh SOK H10 H9 H18 H19. eexists. split.
    - sn F_26f9c D_26f9c.
      stepb_tk F_26fa0 D_26fa0 ltac:(condZ).                                          (* [comment removed for export] *)
      zand F_26fc8 D_26fc8 andi_7 ALk.                                                (* [comment removed for export] *)
      stepiv F_26fcc D_26fcc (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite zbv_seqz by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_26fd0 D_26fd0 ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_26fd4 D_26fd4 ltac:(condZ).                                          (* [comment removed for export] *)
      stepST F_26fd8 D_26fd8 (Z_to_bv 64 sel) (Z_to_bv 64 sy) ltac:(sok_in SOK).
      stepST F_26fdc D_26fdc (Z_to_bv 64 (sel + 4)) (Z_to_bv 64 sx) ltac:(sok_in SOK).
      sn F_26fe0 D_26fe0. sn F_26fe4 D_26fe4. sn F_26fe8 D_26fe8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma scr_C : forall regs m (s sel arr : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sel)%Z -> (sel + 32 < 2 ^ 64)%Z -> (1 <= arr < 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 (sel + 16)) 8 = true -> (sel + 32 <= s - 48 \/ s <= sel)%Z ->
    sc5cells m s ret s0v s1v s2v s3v ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 arr -> getr regs 8 = Z_to_bv 64 sel ->
    exists regs',
      msteps SEGS (mkst regs (0x270e8 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (sel + 16)) (word_to_le_bytes 8 (Z_to_bv 64 arr))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 sel
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s sel arr ret s0v s1v s2v s3v Hs Hs64 Hk Hk64 Ha Hret SOK DJ CE H2 H10 H8.
    destruct CE as (C1 & C2 & C3 & C4 & C5).
    eexists. split.
    - stepST F_26fec D_26fec (Z_to_bv 64 (sel + 16)) (Z_to_bv 64 arr) ltac:(sok_in SOK).
      stepb_tk F_26ff0 D_26ff0 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_2704c D_2704c.
      stepLD8 F_27050 D_27050 ret. stepLD8 F_27054 D_27054 s0v. stepLD8 F_27058 D_27058 s1v.
      stepLD8 F_2705c D_2705c s2v. stepLD8 F_27060 D_27060 s3v.
      zv F_27064 D_27064 (Z_to_bv 64 s).
      stepret F_27068 D_27068 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition C2F (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)).

  Definition c2cells (M : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v s5v s6v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
    rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
    rdn SEGS M (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) /\
    rdn SEGS M (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 s5v) /\
    rdn SEGS M (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 s6v).

  Lemma c2cells_C2F : forall m s ret regs, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    c2cells (C2F m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22).
  Proof. intros m s ret regs Hs Hs64. unfold c2cells, C2F. repeat split; rdn_chain. Qed.

  Lemma c2cells_frame : forall M M' s ret s0v s1v s2v s3v s4v s5v s6v, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    c2cells M s ret s0v s1v s2v s3v s4v s5v s6v -> (forall x : word, (s - 64 <= u x < s)%Z -> M' x = M x) -> c2cells M' s ret s0v s1v s2v s3v s4v s5v s6v.
  Proof.
    intros M M' s ret s0v s1v s2v s3v s4v s5v s6v Hs Hs64 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) E.
    unfold c2cells. repeat split;
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4 | rewrite <- C5 | rewrite <- C6 | rewrite <- C7 | rewrite <- C8];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  Local Ltac c2_epi CE :=
    let C1 := fresh in let C2 := fresh in let C3 := fresh in let C4 := fresh in let C5 := fresh in let C6 := fresh in let C7 := fresh in let C8 := fresh in
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).

  (* [comment removed for export] *)
  Lemma c2d_A : forall regs m (s sx sy : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sx <= 10000)%Z -> (1 <= sy <= 10000)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 sy -> getr regs 11 = Z_to_bv 64 sx ->
    exists regs',
      msteps SEGS (mkst regs (0x2716c : word) m rom) (mkst regs' (0x2b0d0 : word) (C2F m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x27234 /\ getr regs' 10 = Z_to_bv 64 sy /\ getr regs' 11 = Z_to_bv 64 8
      /\ getr regs' 8 = Z_to_bv 64 sx /\ getr regs' 9 = Z_to_bv 64 sy
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s sx sy ret Hs Hs64 Hsx Hsy SOK H2 H1 H10 H11. eexists. split.
    - zv F_27070 D_27070 (Z_to_bv 64 (s - 64)).
      stepST F_27074 D_27074 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_27078 D_27078 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_2707c D_2707c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_27080 D_27080 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_27084 D_27084 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_27088 D_27088 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_2708c D_2708c (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_27090 D_27090 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      sn F_27094 D_27094.
      sn F_27098 D_27098.
      stepiv F_2709c D_2709c (Z_to_bv 64 (2 ^ 64 - 10001)) ltac:(gres; pin; imm_norm; exact lui_m10001).
      sn F_270a0 D_270a0. fixv (Z_to_bv 64 (2 ^ 64 + (sx - 10001))) ltac:(rewrite addw_m10001 by lia; reflexivity).
      stepb_tk F_270a4 D_270a4 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_270c8 D_270c8.
      sn F_270cc D_270cc. fixv (Z_to_bv 64 (2 ^ 64 + (sy - 10001))) ltac:(rewrite addw_m10001 by lia; reflexivity).
      stepb_tk F_270d0 D_270d0 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_2712c D_2712c. sn F_27130 D_27130. sn F_27134 D_27134.
      unfold C2F. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_B : forall regs m (arr : Z),
    (1 <= arr < 2 ^ 64)%Z -> (arr mod 8 = 0)%Z -> getr regs 10 = Z_to_bv 64 arr ->
    exists regs',
      msteps SEGS (mkst regs (0x27234 : word) m rom) (mkst regs' (0x27250 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 18 = Z_to_bv 64 arr /\ getr regs' 19 = Z_to_bv 64 1 /\ getr regs' 20 = Z_to_bv 64 1
      /\ getr regs' 21 = Z_to_bv 64 arr /\ getr regs' 22 = Z_to_bv 64 arr
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [10; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m arr Ha ALa H10. eexists. split.
    - sn F_27138 D_27138.
      sn F_2713c D_2713c. fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).             (* [comment removed for export] *)
      zand F_27140 D_27140 andi_7 ALa.                                                (* [comment removed for export] *)
      stepiv F_27144 D_27144 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite zbv_seqz by lia; reflexivity).   (* [comment removed for export] *)
      zlit F_27148 D_27148 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      sn F_2714c D_2714c. sn F_27150 D_27150.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_H : forall regs m (sx : Z),
    getr regs 8 = Z_to_bv 64 sx ->
    exists regs',
      msteps SEGS (mkst regs (0x27250 : word) m rom) (mkst regs' (0x2b0d0 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x2725c /\ getr regs' 10 = Z_to_bv 64 sx /\ getr regs' 11 = Z_to_bv 64 4
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m sx H8. eexists. split.
    - sn F_27154 D_27154. sn F_27158 D_27158. sn F_2715c D_2715c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_I1 : forall regs m (arr sy i row : Z),
    (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < sy)%Z -> (sy < 2 ^ 31)%Z -> (1 <= row < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = true ->
    getr regs 10 = Z_to_bv 64 row -> getr regs 9 = Z_to_bv 64 (sy - i) -> getr regs 18 = Z_to_bv 64 arr -> getr regs 19 = Z_to_bv 64 1 ->
    getr regs 20 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 (arr + 8 * i) -> getr regs 22 = Z_to_bv 64 (arr + 8 * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x2725c : word) m rom)
                  (mkst regs' (0x27250 : word) (wbytes m (Z_to_bv 64 (arr + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 row))) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 9 = Z_to_bv 64 (sy - (i + 1)) /\ getr regs' 21 = Z_to_bv 64 (arr + 8 * (i + 1))
      /\ getr regs' 22 = Z_to_bv 64 (arr + 8 * (i + 1))
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ regs_agree (fun r => In r [9; 11; 21; 22]%list) regs regs'.
  Proof.
    intros regs m arr sy i row Ha Ha64 Hi Hi1 Hsy Hrow SOK H10 H9 H18 H19 H20 H21 H22. eexists. split.
    - stepb_ft F_27160 D_27160 ltac:(condZ).                                          (* [comment removed for export] *)
      stepiv F_27164 D_27164 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
      zlit F_27168 D_27168 (Z_to_bv 64 1).                                            (* [comment removed for export] *)
      stepb_ft F_2716c D_2716c ltac:(condZ).                                          (* [comment removed for export] *)
      stepb_ft F_27170 D_27170 ltac:(condZ).                                          (* [comment removed for export] *)
      stepST F_27174 D_27174 (Z_to_bv 64 (arr + 8 * i)) (Z_to_bv 64 row) ltac:(store_ok_peel; exact SOK).
      zv F_27178 D_27178 (Z_to_bv 64 (arr + 8 * (i + 1))).
      zv F_2717c D_2717c (Z_to_bv 64 (sy - (i + 1))).
      zv F_27180 D_27180 (Z_to_bv 64 (arr + 8 * (i + 1))).
      stepb_tk F_27184 D_27184 ltac:(condZ).                                          (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma c2d_I2 : forall regs m (s arr sy i row : Z) (ret s0v s1v s2v s3v s4v s5v s6v : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr + 8 * sy < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = sy)%Z -> (sy < 2 ^ 31)%Z -> (1 <= row < 2 ^ 64)%Z ->
    ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (arr + 8 * i)) 8 = true -> (arr + 8 * sy <= s - 64 \/ s <= arr)%Z ->
    c2cells m s ret s0v s1v s2v s3v s4v s5v s6v ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 row -> getr regs 9 = Z_to_bv 64 (sy - i) -> getr regs 18 = Z_to_bv 64 arr ->
    getr regs 19 = Z_to_bv 64 1 -> getr regs 20 = Z_to_bv 64 1 -> getr regs 21 = Z_to_bv 64 (arr + 8 * i) -> getr regs 22 = Z_to_bv 64 (arr + 8 * i) ->
    exists regs',
      msteps SEGS (mkst regs (0x2725c : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (arr + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 row))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 arr
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m s arr sy i row ret s0v s1v s2v s3v s4v s5v s6v Hs Hs64 Ha Ha64 Hi Hi1 Hsy Hrow Hret SOK DJ CE H2 H10 H9 H18 H19 H20 H21 H22. c2_epi CE.
    eexists. split.
    - stepb_ft F_27160 D_27160 ltac:(condZ).
      stepiv F_27164 D_27164 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
      zlit F_27168 D_27168 (Z_to_bv 64 1).
      stepb_ft F_2716c D_2716c ltac:(condZ).
      stepb_ft F_27170 D_27170 ltac:(condZ).
      stepST F_27174 D_27174 (Z_to_bv 64 (arr + 8 * i)) (Z_to_bv 64 row) ltac:(store_ok_peel; exact SOK).
      zv F_27178 D_27178 (Z_to_bv 64 (arr + 8 * (i + 1))).
      zv F_2717c D_2717c (Z_to_bv 64 0).
      zv F_27180 D_27180 (Z_to_bv 64 (arr + 8 * (i + 1))).
      stepb_ft F_27184 D_27184 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_27188 D_27188.
      stepLD8 F_2718c D_2718c ret. stepLD8 F_27190 D_27190 s0v. stepLD8 F_27194 D_27194 s1v.
      stepLD8 F_27198 D_27198 s2v. stepLD8 F_2719c D_2719c s3v. stepLD8 F_271a0 D_271a0 s4v. stepLD8 F_271a4 D_271a4 s5v. stepLD8 F_271a8 D_271a8 s6v.
      zv F_271ac D_271ac (Z_to_bv 64 s).
      stepret F_271b0 D_271b0 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End SegsC.

(* [comment removed for export] *)
Definition spart (C : lctx) (A A' : AS) (m' : word -> option byte) (sel arr dv sy sx n : Z) (rows : Z -> Z) : Prop :=
  let T := alloc_top (c_vm C) in
  bok T sel 32 /\ live A' (Z_to_bv 64 sel) = Some 32%Z /\ live A (Z_to_bv 64 sel) = None /\ live (c_A0 C) (Z_to_bv 64 sel) = None /\
  RECat m' sel (sel_flds sy sx 0 0 dv 0) /\
  bok T arr (8 * sy) /\ live A' (Z_to_bv 64 arr) = Some (8 * sy)%Z /\ live A (Z_to_bv 64 arr) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\ arr <> sel /\
  (forall i, (0 <= i < n)%Z ->
      bok T (rows i) (4 * sx) /\ live A' (Z_to_bv 64 (rows i)) = Some (4 * sx)%Z /\ live A (Z_to_bv 64 (rows i)) = None /\
      live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\ rows i <> arr /\ rows i <> sel /\
      bytes_at m' (arr + 8 * i) (Z_to_le_bytes 8 (rows i))) /\
  (forall i j, (0 <= i < n)%Z -> (0 <= j < n)%Z -> i <> j -> rows i <> rows j) /\
  (forall q, q <> Z_to_bv 64 sel -> q <> Z_to_bv 64 arr -> (forall i, (0 <= i < n)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q).

#[local] Definition sc_rest : list (bv 5) := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma W_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

Lemma sccells_FRM : forall C M M' s ret s0v s1v s2v s3v s4v, Cok C -> FRM C (s - 48) M M' ->
  (c_top C - LSTK <= s - 48)%Z -> (s <= c_top C)%Z ->
  sccells M s ret s0v s1v s2v s3v s4v -> sccells M' s ret s0v s1v s2v s3v s4v.
Proof.
  intros C M M' s ret s0v s1v s2v s3v s4v CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold sccells.
  rewrite !(FRM_rdn16 C (s - 48) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition c2rows (C : lctx) (A A' : AS) (m' : word -> option byte) (arr sy sx n : Z) (rows : Z -> Z) : Prop :=
  let T := alloc_top (c_vm C) in
  bok T arr (8 * sy) /\ live A' (Z_to_bv 64 arr) = Some (8 * sy)%Z /\ live A (Z_to_bv 64 arr) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  (forall i, (0 <= i < n)%Z ->
      bok T (rows i) (4 * sx) /\ live A' (Z_to_bv 64 (rows i)) = Some (4 * sx)%Z /\ live A (Z_to_bv 64 (rows i)) = None /\
      live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\ rows i <> arr /\
      bytes_at m' (arr + 8 * i) (Z_to_le_bytes 8 (rows i))) /\
  (forall i j, (0 <= i < n)%Z -> (0 <= j < n)%Z -> i <> j -> rows i <> rows j) /\
  (forall q, q <> Z_to_bv 64 arr -> (forall i, (0 <= i < n)%Z -> q <> Z_to_bv 64 (rows i)) -> live A' q = live A q).

(* [comment removed for export] *)
#[local] Definition c2_rest : list (bv 5) := [3; 4; 23; 24; 25; 26; 27]%bv.

Lemma c2cells_FRM : forall C M M' s ret s0v s1v s2v s3v s4v s5v s6v, Cok C -> FRM C (s - 64) M M' ->
  (c_top C - LSTK <= s - 64)%Z -> (s <= c_top C)%Z ->
  c2cells M s ret s0v s1v s2v s3v s4v s5v s6v -> c2cells M' s ret s0v s1v s2v s3v s4v s5v s6v.
Proof.
  intros C M M' s ret s0v s1v s2v s3v s4v s5v s6v CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold c2cells.
  rewrite !(FRM_rdn16 C (s - 64) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition KR (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s sx sy kP pP : Z) (S : TSet) : Prop :=
  forall A' m' vm' r arr rows, W C A' m' (with_vmmaps vm' md) -> cs_kept regs r -> POSTM C A s m m' ->
    getr r 10 = Z_to_bv 64 arr -> c2rows C A A' m' arr sy sx sy rows ->
    aroom A' vm' (kP - sy) (pP - sy * RB10_small) ->
    realizes SEGS (mkCfg (mkst r (getr regs 1) m' al_rom) (with_vmmaps vm' md)) S.

(* [comment removed for export] *)
Lemma c2d_loop : forall (k : nat) C A m md regs (s sx sy kP pP : Z) (S : TSet) A1 M1 vm1 r (n arr : Z) (rows : Z -> Z),
  Cok C -> KR C A m md regs s sx sy kP pP S ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x45480 -> ret_ok (getr regs 1) ->
  (1 <= sx <= 500)%Z -> (1 <= sy <= 250)%Z -> (Z.of_nat k = sy - 1 - n)%Z -> (0 <= n < sy)%Z -> getr regs 2 = Z_to_bv 64 s ->
  (sy <= kP)%Z -> (sy * RB10_small <= pP)%Z ->
  W C A1 M1 (with_vmmaps vm1 md) -> POSTM C A s m M1 ->
  c2cells M1 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) ->
  c2rows C A A1 M1 arr sy sx n rows ->
  aroom A1 vm1 (kP - n) (pP - n * RB10_small) ->
  getr r 2 = Z_to_bv 64 (s - 64) -> getr r 8 = Z_to_bv 64 sx -> getr r 9 = Z_to_bv 64 (sy - n) -> getr r 18 = Z_to_bv 64 arr ->
  getr r 19 = Z_to_bv 64 1 -> getr r 20 = Z_to_bv 64 1 -> getr r 21 = Z_to_bv 64 (arr + 8 * n) -> getr r 22 = Z_to_bv 64 (arr + 8 * n) ->
  getr r 4 = Z_to_bv 64 0x45480 ->
  (forall x, In x c2_rest -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x27250 : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [|k IH]; intros C A m md regs s sx sy kP pP S A1 M1 vm1 r n arr rows CK HKR Hs16 Hlo Hhi H4 Hret Hw Hh Hk Hn H2 HkP HpP HW PM CE
    KP HRM R2 R8 R9 R18 R19 R20 R21 R22 R4 RR;
    pose proof KP as (Ba & La & LaA & La0 & ROWS & DIST & RQ);
    pose proof Ba as (Ga & TOPa & ALa);
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LLU16] in *; unfold c2_rest in RR; unfold CALLOC_STACK, ALLOC_STACK in Hlo;
    pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    pose proof (alloc_margin_small_le (sx * 4) ltac:(lia)) as MG; unfold RB10_small in *;
    (* [comment removed for export] *)
    destruct (c2d_H al_rom r M1 sx R8) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & AG1);
    (eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]);
    replace (0x2b0d0 : word) with (Z_to_bv 64 0x2b0d0) by (apply bv_eq; reflexivity);
    (apply (W_calloc16_sure C A1 M1 _ r1 sx 4 (kP - n) (pP - n * 2 ^ 17) (Z_to_bv 64 0x2725c) (s - 64) S CK HW Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
             HRM ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
             ltac:(red; apply bv_eq; reflexivity) ltac:(rewrite (AG1 4) by notin_lit; exact R4)
             ltac:(rewrite Q2; exact R2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)));
    intros A2 m2 vm2 r2 res HW2 Hres CS2 Hnz L1 L2 L00 LEQ ZERO AL16 TOP PM2 HRM2; rewrite with_vmmaps_twice in HW2 |- *;
    replace (Z_to_bv 64 0x2725c) with (0x2725c : word) by (apply bv_eq; reflexivity);
    pose proof (c2cells_FRM C M1 m2 s _ _ _ _ _ _ _ _ CK (proj1 PM2) ltac:(lia) ltac:(lia) CE) as CE2;
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity);
    assert (E8 : getr r2 8 = Z_to_bv 64 sx) by (csr; reflexivity);
    assert (E9 : getr r2 9 = Z_to_bv 64 (sy - n)) by (csr; reflexivity);
    assert (E18 : getr r2 18 = Z_to_bv 64 arr) by (csr; reflexivity);
    assert (E19 : getr r2 19 = Z_to_bv 64 1) by (csr; reflexivity);
    assert (E20 : getr r2 20 = Z_to_bv 64 1) by (csr; reflexivity);
    assert (E21 : getr r2 21 = Z_to_bv 64 (arr + 8 * n)) by (csr; reflexivity);
    assert (E22 : getr r2 22 = Z_to_bv 64 (arr + 8 * n)) by (csr; reflexivity);
    assert (E4 : getr r2 4 = Z_to_bv 64 0x45480) by (csr; reflexivity);
    assert (RR2 : forall x, In x c2_rest -> getr r2 x = getr regs x) by (unfold c2_rest; rest_solve);
    (* [comment removed for export] *)
    assert (ROWS2 : forall i, (0 <= i < n)%Z ->
              bok (alloc_top (c_vm C)) (rows i) (4 * sx) /\ live A1 (Z_to_bv 64 (rows i)) = Some (4 * sx)%Z /\ live A (Z_to_bv 64 (rows i)) = None /\
              live (c_A0 C) (Z_to_bv 64 (rows i)) = None /\ rows i <> arr /\
              bytes_at m2 (arr + 8 * i) (Z_to_le_bytes 8 (rows i)))
      by (intros i Hi; destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G5 & G7);
          do 5 (split; [assumption|]);
          apply (bytes_at_frame M1); [exact G7 | | lia | rewrite length_Z_to_le_bytes; lia];
          rewrite length_Z_to_le_bytes; intros x Hx;
          exact (LIVK_in A1 M1 m2 arr (8 * sy) x (proj2 PM2) La ltac:(lia) ltac:(lia) ltac:(lia)));
    assert (SUB1 : sub_live A A1)
      by (intros q kq Lq; rewrite (RQ q); [exact Lq | intros ->; rewrite Lq in LaA; discriminate |];
          intros i Hi ->; destruct (ROWS i Hi) as (_ & _ & LA & _); rewrite Lq in LA; discriminate);
    assert (PM2' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM|]; apply (POSTM_sub C A A1 _ _ _ SUB1); eapply POSTM_mono; [|exact PM2]; lia);
    (* [comment removed for export] *)
    pose proof (bok_of_calloc C res (sx * 4) ltac:(lia) Hnz AL16 TOP) as Brw;
    assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self);
    set (rw := u res) in *;
    rewrite Eres in Hres, L1, L2, L00, LEQ;
    clearbody rw; pose proof Brw as (Grw & TOPrw & ALrw);
    assert (NEra : Z_to_bv 64 rw <> Z_to_bv 64 arr) by (intros E; rewrite E in L1; rewrite L1 in La; discriminate);
    assert (La2 : live A2 (Z_to_bv 64 arr) = Some (8 * sy)%Z) by (rewrite (LEQ _ (not_eq_sym NEra)); exact La);
    assert (NErr : forall i, (0 <= i < n)%Z -> Z_to_bv 64 (rows i) <> Z_to_bv 64 rw)
      by (intros i Hi E; destruct (ROWS i Hi) as (_ & G5 & _); rewrite E, L1 in G5; discriminate);
    assert (SOKn : store_ok SEGS m2 (Z_to_bv 64 (arr + 8 * n)) 8 = true)
      by (apply (W_sok_blk C A2 m2 _ _ _ (arr + 8 * n) 8 CK HW2 La2); rewrite u_Z2bv by lia; cbn; lia);
    assert (SUB2 : sub_live A A2)
      by (intros q kq Lq; rewrite (LEQ q); [exact (SUB1 q kq Lq)|]; intros ->; rewrite (SUB1 _ _ Lq) in L1; discriminate);
    set (rows' := fun i : Z => if (i =? n)%Z then rw else rows i);
    set (m3 := wbytes m2 (Z_to_bv 64 (arr + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 rw)));
    assert (WP3 : W C A2 m3 (with_vmmaps vm2 md) /\ POSTM C A s m m3)
      by (subst m3; apply (WP_blk C A A2 m m2 _ (Z_to_bv 64 arr) _ (8 * sy) _ s CK (conj HW2 PM2') La2 LaA La0 SUB2); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia);
    assert (CE3 : c2cells m3 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22))
      by (apply (c2cells_frame m2 m3 s); [lia | lia | exact CE2 |]; intros x Hx; subst m3; apply wbytes_outside; rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn;
          pose proof (blk_range C A2 m2 _ (Z_to_bv 64 arr) _ CK HW2 La2 ltac:(lia)) as [_ X]; rewrite u_Z2bv in X by lia; lia);
    assert (KP3 : c2rows C A A2 m3 arr sy sx (n + 1) rows').
  1,3: split; [exact Ba|]; split; [exact La2|]; split; [exact LaA|]; split; [exact La0|]; split; [|split].
  1,4: intros i Hi; unfold rows'; destruct (Z.eqb_spec i n) as [->|NEi];
       [ split; [replace (4 * sx)%Z with (sx * 4)%Z by lia; exact Brw|];
         split; [rewrite L2; f_equal; lia|];
         split; [rewrite <- (RQ _ NEra (fun i' Hi' => not_eq_sym (NErr i' Hi'))); exact L1|];
         split; [exact L00|];
         split; [intros E; apply NEra; rewrite E; reflexivity|];
         subst m3; rewrite (w2b_Z 8 rw) by lia; apply bytes_at_wbytes_same; [lia | rewrite length_Z_to_le_bytes; lia]
       | destruct (ROWS2 i ltac:(lia)) as (G1 & G2 & G3 & G4 & G5 & G7);
         split; [exact G1|]; split; [rewrite (LEQ _ (NErr i ltac:(lia))); exact G2|]; do 3 (split; [assumption|]);
         subst m3; apply bytes_at_wbytes_out; [exact G7 | lia | rewrite length_Z_to_le_bytes; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
                                              | rewrite length_Z_to_le_bytes, length_N_to_le_bytes, u_Z2bv by lia; cbn; lia] ].
  1,3: intros i i' Hi Hi' NE; unfold rows'; destruct (Z.eqb_spec i n) as [->|N1], (Z.eqb_spec i' n) as [->|N2];
       [ lia
       | intros E; apply (NErr i' ltac:(lia)); rewrite E; reflexivity
       | intros E; apply (NErr i ltac:(lia)); rewrite E; reflexivity
       | apply DIST; lia ].
  1,2: intros q NQa NQr; pose proof (NQr n ltac:(lia)) as X; unfold rows' in X; rewrite Z.eqb_refl in X;
       rewrite (LEQ q X); apply RQ; [exact NQa|]; intros i Hi; pose proof (NQr i ltac:(lia)) as Y; unfold rows' in Y;
       destruct (Z.eqb_spec i n); [lia | exact Y].
  - (* [comment removed for export] *)
    pose proof (blk_range C A2 m2 _ (Z_to_bv 64 arr) _ CK HW2 La2 ltac:(lia)) as [_ Xa]. rewrite u_Z2bv in Xa by lia.
    destruct (c2d_I2 al_rom r2 m2 s arr sy n rw (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret SOKn ltac:(lia) CE2 E2 Hres E9 E18 E19 E20 E21 E22)
      as (r3 & RUN3 & P2 & P1 & P10 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. fold m3.
    assert (En : (n + 1)%Z = sy) by lia.
    apply (HKR A2 m3 vm2 r3 arr rows' (proj1 WP3)).
    + apply cs_kept_intro; csr; reflexivity.
    + exact (proj2 WP3).
    + exact P10.
    + rewrite En in KP3. exact KP3.
    + replace (kP - sy)%Z with (kP - n - 1)%Z by lia. unfold RB10_small. replace (pP - sy * 2 ^ 17)%Z with (pP - n * 2 ^ 17 - 2 ^ 17)%Z by lia.
      rewrite MG in HRM2. exact HRM2.
  - (* [comment removed for export] *)
    destruct (c2d_I1 al_rom r2 m2 arr sy n rw ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOKn Hres E9 E18 E19 E20 E21 E22)
      as (r3 & RUN3 & P2 & P9 & P21 & P22 & P8 & P18 & P19 & P20 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. fold m3.
    apply (IH C A m md regs s sx sy kP pP S A2 m3 vm2 r3 (n + 1)%Z arr rows' CK HKR Hs16 ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) Hhi H4 Hret Hw Hh ltac:(lia) ltac:(lia) H2 HkP HpP
             (proj1 WP3) (proj2 WP3) CE3 KP3); try (csr; reflexivity).
    + replace (kP - (n + 1))%Z with (kP - n - 1)%Z by lia. replace (pP - (n + 1) * 2 ^ 17)%Z with (pP - n * 2 ^ 17 - 2 ^ 17)%Z by lia.
      rewrite MG in HRM2. exact HRM2.
    + unfold c2_rest; rest_solve.
Qed.

(* [comment removed for export] *)
Theorem create2dIntArray_W : forall C A m md regs (s sx sy : Z) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 sy -> getr regs 11 = Z_to_bv 64 sx -> (1 <= sx <= 500)%Z -> (1 <= sy <= 250)%Z ->
  aroom A (m_vmmaps md) kR bR -> (1 + sy <= kR)%Z -> ((1 + sy) * RB10_small <= bR)%Z ->
  (forall A' m' vm' regs' arr rows, W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 arr -> c2rows C A A' m' arr sy sx sy rows ->
     aroom A' vm' (kR - (1 + sy)) (bR - (1 + sy) * RB10_small) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x2716c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s sx sy ret S kR bR CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hsx Hsy HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof (alloc_margin_small_le (sy * 8) ltac:(lia)) as MG2.
  assert (HRB' : ((1 + sy) * 2 ^ 17 <= bR)%Z) by (unfold RB10_small in HRB; exact HRB). unfold RB10_small in MG2.
  assert (HsS : (c_top C - LSTK + 64 <= s)%Z) by (unfold CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  destruct (c2d_A al_rom regs m s sx sy ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := C2F m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold C2F; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (c2cells_C2F m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  (* [comment removed for export] *)
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (rewrite (AG1 4) by notin_lit; exact H4).
  replace (0x2b0d0 : word) with (Z_to_bv 64 0x2b0d0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 _ r1 sy 8 kR bR (Z_to_bv 64 0x27234) (s - 64) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           HRM ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK in *; lia) ltac:(lia)).
  intros A2 m2 vm2 r2 res HW2 Hres CS2 Hnz L1 L2 L00 LEQ ZERO AL16 TOP PM2 HRM2. rewrite ?with_vmmaps_twice in HW2 |- *.
  replace (Z_to_bv 64 0x27234) with (0x27234 : word) by (apply bv_eq; reflexivity).
  pose proof (c2cells_FRM C M1 m2 s _ _ _ _ _ _ _ _ CK (proj1 PM2) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (PM2' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  assert (E8 : getr r2 8 = Z_to_bv 64 sx) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 sy) by (csr; reflexivity).
  assert (RR2 : forall x, In x c2_rest -> getr r2 x = getr regs x) by (unfold c2_rest; rest_solve).
  pose proof (bok_of_calloc C res (sy * 8) ltac:(lia) Hnz AL16 TOP) as Barr.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (arr := u res) in *. rewrite Eres in Hres, L1, L2, L00, LEQ. clearbody arr.
  pose proof Barr as (Garr & TOParr & ALarr).
  destruct (c2d_B al_rom r2 m2 arr ltac:(lia) ltac:(rewrite <- (Z.add_0_r arr); apply mod16_plus_mod8; [exact ALarr | reflexivity]) Hres)
    as (r3 & RUN3 & P2 & P18 & P19 & P20 & P21 & P22 & P8 & P9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  set (kP := (kR - 1)%Z) in *. set (pP := (bR - alloc_margin (sy * 8))%Z) in *.
  assert (HKR : KR C A m md regs s sx sy kP pP S).
  { intros A' m' vm' r arr' rows' HW' CS PM' R10' KRW' HR'. rewrite H1.
    apply (HK A' m' vm' r arr' rows' HW' CS PM' R10' KRW').
    apply (aroom_mono _ _ _ _ _ _ HR'); subst kP pP; rewrite ?MG2; unfold RB10_small; lia. }
  apply (c2d_loop (Z.to_nat (sy - 1)) C A m md regs s sx sy kP pP S A2 m2 vm2 r3 0 arr (fun _ => 0%Z) CK HKR Hs16 Hlo Hhi H4
           ltac:(rewrite H1; exact Hret) Hsx Hsy ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) H2 ltac:(subst kP; lia)
           ltac:(subst pP; rewrite MG2; unfold RB10_small; lia) HW2 PM2' CE2); try (csr; reflexivity).
  - split; [replace (8 * sy)%Z with (sy * 8)%Z by lia; exact Barr|]. split; [rewrite L2; f_equal; lia|]. split; [exact L1|]. split; [exact L00|].
    split; [intros i Hi; lia|]. split; [intros i j Hi; lia|].
    intros q NQa _. exact (LEQ q NQa).
  - replace (kP - 0)%Z with kP by lia. replace (pP - 0 * RB10_small)%Z with pP by lia. subst kP pP. exact HRM2.
  - rewrite P9, Z.sub_0_r. exact E9.
  - rewrite P21. f_equal. lia.
  - rewrite P22. f_equal. lia.
  - unfold c2_rest; rest_solve.
Qed.

(* [comment removed for export] *)
Lemma spart_full : forall C A A' m' sel arr sy sx rows, (1 <= sy <= 10000)%Z -> (1 <= sx <= 10000)%Z ->
  spart C A A' m' sel arr arr sy sx sy rows ->
  let v := SELV sy sx 0 0 arr 0 rows in
  sel_at (alloc_top (c_vm C)) A' m' sel v /\ sel_off A sel v /\ sel_off (c_A0 C) sel v /\ sel_only A A' sel v.
Proof.
  intros C A A' m' sel arr sy sx rows Hsy Hsx (Bk & Lk & LkA & Lk0 & Rk & Ba & La & LaA & La0 & NEak & ROWS & DIST & RQ) v.
  split; [|split; [|split]].
  - unfold sel_at. cbn [v_sy v_sx v_cy v_cx v_data v_name v_rows v].
    split; [exact Hsy|]. split; [exact Hsx|]. split; [exact Bk|]. split; [exact Lk|]. split; [exact Rk|].
    split; [exact Ba|]. split; [exact La|]. split; [exact NEak|]. split; [|exact DIST].
    intros i Hi. destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    split; [exact G1|]. split; [exact G2|]. split; [exact G5|]. split; [exact G6 | exact G7].
  - intros p [->|[->|(i & Hi & ->)]]; [exact LkA | exact LaA |]. cbn [v_sy v_rows v] in *. destruct (ROWS i Hi) as (_ & _ & G3 & _). exact G3.
  - intros p [->|[->|(i & Hi & ->)]]; [exact Lk0 | exact La0 |]. cbn [v_sy v_rows v] in *. destruct (ROWS i Hi) as (_ & _ & _ & G4 & _). exact G4.
  - intros q NQ. apply RQ.
    + apply NQ. left. reflexivity.
    + apply NQ. right. left. reflexivity.
    + intros i Hi. apply NQ. right. right. exists i. split; [exact Hi | reflexivity].
Qed.

Lemma sc5cells_FRM : forall C M M' s ret s0v s1v s2v s3v, Cok C -> FRM C (s - 48) M M' ->
  (c_top C - LSTK <= s - 48)%Z -> (s <= c_top C)%Z ->
  sc5cells M s ret s0v s1v s2v s3v -> sc5cells M' s ret s0v s1v s2v s3v.
Proof.
  intros C M M' s ret s0v s1v s2v s3v CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold sc5cells.
  rewrite !(FRM_rdn16 C (s - 48) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Theorem selCreate_W : forall C A m md regs (s sy sx : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + 64 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 sy -> getr regs 11 = Z_to_bv 64 sx -> getr regs 12 = Z_to_bv 64 0 -> (1 <= sx <= 500)%Z -> (1 <= sy <= 250)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (2 + sy <= kR)%Z -> ((2 + sy) * RB10_small <= bR)%Z ->
  (forall A' m' vm' regs' (sel arr : Z) (rows : Z -> Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 sel ->
     sel_at (alloc_top (c_vm C)) A' m' sel (SELV sy sx 0 0 arr 0 rows) ->
     sel_off A sel (SELV sy sx 0 0 arr 0 rows) -> sel_off (c_A0 C) sel (SELV sy sx 0 0 arr 0 rows) -> sel_only A A' sel (SELV sy sx 0 0 arr 0 rows) ->
     aroom A' vm' (kR - (2 + sy)) (bR - (2 + sy) * RB10_small) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x27068 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s sy sx ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh kR bR HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof (alloc_margin_small_le (1 * 32) ltac:(lia)) as MG1.
  assert (HRB' : ((2 + sy) * 2 ^ 17 <= bR)%Z) by (unfold RB10_small in HRB; exact HRB). unfold RB10_small in MG1.
  assert (HsS : (c_top C - LSTK + 112 <= s)%Z) by (unfold CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  (* [comment removed for export] *)
  destruct (scr_A al_rom regs m s sy sx ret ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q9 & Q18 & Q19 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := SC5F m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold SC5F; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (sc5cells_SC5F m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x45480) by (rewrite (AG1 4) by notin_lit; exact H4).
  replace (0x2b0d0 : word) with (Z_to_bv 64 0x2b0d0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 _ r1 1 32 kR bR (Z_to_bv 64 0x27098) (s - 48) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           HRM ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK in *; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa HRMa. rewrite ?with_vmmaps_twice in HWa |- *.
  replace (Z_to_bv 64 0x27098) with (0x27098 : word) by (apply bv_eq; reflexivity).
  pose proof (sc5cells_FRM C M1 m1 s _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) CE1) as CEa.
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x45480) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 sx) by (csr; reflexivity).
  assert (E18 : getr r2 18 = Z_to_bv 64 sy) by (csr; reflexivity).
  assert (E19 : getr r2 19 = Z_to_bv 64 0) by (csr; reflexivity).
  (* [comment removed for export] *)
  pose proof (bok_of_calloc C res (1 * 32) ltac:(lia) Hnz AL16 TOP) as Bsel.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (sel := u res) in *. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO. clearbody sel. change (1 * 32)%Z with 32%Z in *.
  pose proof Bsel as (Gsel & TOPsel & ALsel).
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  assert (REC0 : RECat m1 sel (zflds [4; 4; 4; 4; 8; 8]%nat)).
  { apply RECat_zero; [lia | cbn; lia | repeat constructor |]. cbn [flds_len zflds Nat.add]. intros i Hi.
    unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
  destruct (scr_B al_rom r2 m1 sy sx sel ltac:(lia) ltac:(lia) (bok_mod8 _ _ _ Bsel) ltac:(lia) ltac:(lia)
              (W_sok_blk C A1 m1 _ _ _ sel 8 CK HWa L1 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              Hres E9 E18 E19) as (r3 & RUN3 & P2 & P1 & P10 & P11 & P8 & P9 & P18 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  set (M2 := wbytes (wbytes m1 _ _) _ _).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A s m M2).
  { subst M2.
    do 2 (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 sel) _ 32); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    split; [exact HWa | exact PMa']. }
  destruct WP2 as [HW2 PM2].
  pose proof (blk_range C A1 m1 _ (Z_to_bv 64 sel) _ CK HWa L1 ltac:(lia)) as [_ Xk]. rewrite u_Z2bv in Xk by lia.
  assert (OUT2 : forall x : word, ~ (sel <= u x < sel + 8)%Z -> M2 x = m1 x).
  { intros x Hx. subst M2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (CE2 : sc5cells M2 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { apply (sc5cells_frame m1 M2 s); [lia | lia | exact CEa |]. intros x Hx. apply OUT2. lia. }
  assert (REC2 : RECat M2 sel (sel_flds sy sx 0 0 0 0)).
  { subst M2. unfold sel_flds.
    eapply (REC_wr' _ _ [(4%nat, sy); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] _ 1 4);
      [ | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ].
    eapply (REC_wr' _ _ [(4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] _ 0 4);
      [ exact REC0 | cbn; lia | cbn; lia | reflexivity | cbn [fld_off Z.of_nat]; f_equal; lia | reflexivity ]. }
  assert (P4 : getr r3 4 = Z_to_bv 64 0x45480) by (rewrite (AG3 4) by notin_lit; exact E4).
  assert (P2' : getr r3 2 = Z_to_bv 64 (s - 48)) by (rewrite P2; exact E2).
  apply (create2dIntArray_W C A1 M2 _ r3 (s - 48) sx sy (Z_to_bv 64 0x270e8) S (kR - 1) (bR - alloc_margin 32) CK HW2 P2'
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK in *; lia) ltac:(lia) P1
           ltac:(red; apply bv_eq; reflexivity) P4 P10 P11 Hw Hh HRMa ltac:(lia) ltac:(rewrite MG1; unfold RB10_small; lia)).
  intros A3 m3 vm3 r4 arr rows HW3 CS3 PM3 R10a KRW HRM3. rewrite ?with_vmmaps_twice in HW3 |- *.
  replace (Z_to_bv 64 0x270e8) with (0x270e8 : word) by (apply bv_eq; reflexivity).
  pose proof KRW as (Ba & La & LaA1 & La0 & ROWS & DIST & RQ). pose proof Ba as (Ga & TOPa & ALa).
  assert (Lk3 : live A3 (Z_to_bv 64 sel) = Some 32%Z).
  { rewrite (RQ (Z_to_bv 64 sel)); [exact L1 | intros E; rewrite E, LaA1 in L1; discriminate |].
    intros i Hi E. destruct (ROWS i Hi) as (_ & _ & LiA1 & _). rewrite E, LiA1 in L1. discriminate. }
  assert (NEka : arr <> sel) by (intros E; rewrite E, L1 in LaA1; discriminate).
  assert (LaA : live A (Z_to_bv 64 arr) = None) by (rewrite <- (LEQ _ (zbv_ne arr sel ltac:(lia) ltac:(lia) NEka)); exact LaA1).
  assert (SUB3 : sub_live A A3).
  { intros q kq Lq. pose proof (SUBa q kq Lq) as Lq1. rewrite (RQ q); [exact Lq1 | intros ->; rewrite Lq1 in LaA1; discriminate |].
    intros i Hi ->. destruct (ROWS i Hi) as (_ & _ & LiA1 & _). rewrite Lq1 in LiA1. discriminate. }
  assert (PM3' : POSTM C A s m m3) by (eapply POSTM_trans; [exact PM2 | apply (POSTM_sub C A A1 _ _ _ SUBa); eapply POSTM_mono; [|exact PM3]; lia]).
  pose proof (sc5cells_FRM C M2 m3 s _ _ _ _ _ CK (proj1 PM3) ltac:(lia) ltac:(lia) CE2) as CE3.
  assert (REC3 : RECat m3 sel (sel_flds sy sx 0 0 0 0)).
  { apply (RECat_POSTM C A1 (s - 48) M2 m3 (Z_to_bv 64 sel) 32 _ _ REC2 PM3 L1); rewrite u_Z2bv by lia; [lia | cbn; lia]. }
  (* [comment removed for export] *)
  assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  assert (Y8 : getr r4 8 = Z_to_bv 64 sel) by (csr; reflexivity).
  destruct (scr_C al_rom r4 m3 s sel arr (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite H1; exact Hret)
              (W_sok_blk C A3 m3 _ _ _ (sel + 16) 8 CK HW3 Lk3 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              ltac:(lia) CE3 Y2 R10a Y8) as (r5 & RUN5 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
  set (m4 := wbytes m3 (Z_to_bv 64 (sel + 16)) (word_to_le_bytes 8 (Z_to_bv 64 arr))).
  assert (WP4 : W C A3 m4 (with_vmmaps vm3 md) /\ POSTM C A s m m4)
    by (subst m4; apply (WP_blk C A A3 m m3 _ (Z_to_bv 64 sel) _ 32 _ s CK (conj HW3 PM3') Lk3 L0 L00 SUB3); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia).
  assert (Rk4 : RECat m4 sel (sel_flds sy sx 0 0 arr 0)).
  { subst m4. unfold sel_flds.
    eapply (REC_wr' _ _ [(4%nat, sy); (4%nat, sx); (4%nat, 0%Z); (4%nat, 0%Z); (8%nat, 0%Z); (8%nat, 0%Z)] _ 4 8);
      [ exact REC3 | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity ]. }
  pose proof (live_apart C A3 m3 _ _ _ _ _ CK HW3 Lk3 La ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as APka. rewrite !u_Z2bv in APka by lia.
  (* [comment removed for export] *)
  assert (KP4 : spart C A A3 m4 sel arr arr sy sx sy rows).
  { split; [exact Bsel|]. split; [exact Lk3|]. split; [exact L0|]. split; [exact L00|]. split; [exact Rk4|].
    split; [exact Ba|]. split; [exact La|]. split; [exact LaA|]. split; [exact La0|]. split; [exact NEka|]. split; [|split; [exact DIST|]].
    - intros i Hi. destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G5 & G7). pose proof G1 as (Gr & TOPr & _).
      assert (NEik : rows i <> sel) by (intros E; rewrite E, L1 in G3; discriminate).
      split; [exact G1|]. split; [exact G2|].
      split; [rewrite <- (LEQ _ (zbv_ne (rows i) sel ltac:(lia) ltac:(lia) NEik)); exact G3|].
      split; [exact G4|]. split; [exact G5|]. split; [exact NEik|].
      subst m4. apply bytes_at_wbytes_out; [exact G7 | lia | rewrite length_Z_to_le_bytes; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
                                           | rewrite length_Z_to_le_bytes, length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    - intros q NQk NQa NQr. rewrite (RQ q NQa NQr). exact (LEQ q NQk). }
  destruct (spart_full C A A3 m4 sel arr sy sx rows ltac:(lia) ltac:(lia) KP4) as (SA & SO & SO0 & SN).
  rewrite H1. apply (HK A3 m4 vm3 r5 sel arr rows (proj1 WP4)).
  - apply cs_kept_intro; csr; reflexivity.
  - exact (proj2 WP4).
  - exact V10.
  - exact SA.
  - exact SO.
  - exact SO0.
  - exact SN.
  - apply (aroom_mono _ _ _ _ _ _ HRM3); rewrite ?MG1; unfold RB10_small; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma snew_len1 : forall len, (0 <= len < 2 ^ 31 - 1)%Z ->
  v_srai (v_addi (v_or (v_slli (Z_to_bv 64 len) 32) (Z_to_bv 64 4294967295)) 1) 32 = Z_to_bv 64 (len + 1).
Proof.
  intros len Hl. rewrite zbv_slli by lia. unfold v_or. rewrite !u_Z2bv by lia.
  assert (EL : Z.lor (len * 2 ^ 32) 4294967295 = (len * 2 ^ 32 + 4294967295)%Z).
  { assert (LA : Z.land (len * 2 ^ 32) 4294967295 = 0%Z).
    { change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones by lia. apply Z_mod_mult. }
    rewrite <- (Z.lxor_lor _ _ LA). symmetry. apply Z.add_nocarry_lxor. exact LA. }
  rewrite EL. rewrite zbv_addi. rewrite zbv_srai_small by lia. f_equal.
  replace (len * 2 ^ 32 + 4294967295 + 1)%Z with ((len + 1) * 2 ^ 32)%Z by lia. apply Z_div_mult. lia.
Qed.

Lemma snew_len2 : forall len, (0 <= len < 2 ^ 31)%Z -> v_srli (v_slli (Z_to_bv 64 len) 33) 33 = Z_to_bv 64 len.
Proof. intros len Hl. rewrite zbv_slli by lia. rewrite zbv_srli by lia. f_equal. apply Z_div_mult. lia. Qed.

Lemma b8_norm : forall b : byte, Z_to_bv 8 (u (Z_to_bv 64 (u b))) = b.
Proof. intros b. pose proof (u8_range b). rewrite u_Z2bv by lia. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia. Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall p, (0 <= p < 2 ^ 64)%Z -> Z.lxor p (2 ^ 64 - 1) = (2 ^ 64 - 1 - p)%Z.
Proof.
  intros p Hp. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec.
  replace (2 ^ 64 - 1 - p)%Z with ((Z.lnot p) mod 2 ^ 64)%Z.
  2:{ unfold Z.lnot. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
  destruct (Z_lt_ge_dec n 64).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
    replace (2 ^ 64 - 1)%Z with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia.
    apply Bool.xorb_true_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    replace (2 ^ 64 - 1)%Z with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_high by lia.
    rewrite Bool.xorb_false_r.
    destruct (Z.eq_dec p 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma zbv_not : forall p, (0 <= p < 2 ^ 64)%Z -> v_xori (Z_to_bv 64 p) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - p).
Proof.
  intros p Hp. unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 (-1)) with (2 ^ 64 - 1)%Z.
  f_equal. apply lxor_ones64. lia.
Qed.

Section SegsN.
Variable rom : word -> option byte.

  Definition SNF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)).

  Definition sncells (M : word -> option byte) (s : Z) (ret s0v s1v s2v : word) : Prop :=
    rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
    rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
    rdn SEGS M (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v).

  Lemma sncells_SNF : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    sncells (SNF m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18).
  Proof. intros m s ret regs Hs Hs64. unfold sncells, SNF. repeat split; rdn_chain. Qed.

  Lemma sncells_frame : forall M M' s ret s0v s1v s2v, (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    sncells M s ret s0v s1v s2v -> (forall x : word, (s - 32 <= u x < s)%Z -> M' x = M x) -> sncells M' s ret s0v s1v s2v.
  Proof.
    intros M M' s ret s0v s1v s2v Hs Hs64 (C1 & C2 & C3 & C4) E.
    unfold sncells. repeat split; [rewrite <- C1 | rewrite <- C2 | rewrite <- C3 | rewrite <- C4];
      (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]; intros x Hx; cbn in Hx; apply E; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma snw_A : forall regs m (s src : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= src < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 src ->
    exists regs',
      msteps SEGS (mkst regs (0x158d0 : word) m rom) (mkst regs' (0x32870 : word) (SNF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x158f0 /\ getr regs' 10 = Z_to_bv 64 src
      /\ getr regs' 8 = Z_to_bv 64 src
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof.
    intros regs m s src ret Hs Hs64 Hsrc SOK H2 H1 H10.
    eexists. split.
    - zv F_157d4 D_157d4 (Z_to_bv 64 (s - 32)).
      stepST F_157d8 D_157d8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_157dc D_157dc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_157e0 D_157e0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_157e4 D_157e4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepb_ft F_157e8 D_157e8 ltac:(condZ).
      sn F_157ec D_157ec. sn F_157f0 D_157f0.
      unfold SNF. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma snw_B : forall regs m (len : Z),
    (0 <= len < 2 ^ 31 - 1)%Z -> getr regs 10 = Z_to_bv 64 len ->
    exists regs',
      msteps SEGS (mkst regs (0x158f0 : word) m rom) (mkst regs' (0x2b0d0 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 1 = Z_to_bv 64 0x15908 /\ getr regs' 10 = Z_to_bv 64 (len + 1) /\ getr regs' 11 = Z_to_bv 64 1
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = Z_to_bv 64 len /\ getr regs' 18 = Z_to_bv 64 len
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m len Hl H10. eexists. split.
    - sn F_157f4 D_157f4.                                                             (* [comment removed for export] *)
      sn F_157f8 D_157f8. fixv (Z_to_bv 64 len) ltac:(pin; rewrite zbv_addiw_small by lia; f_equal; lia).         (* [comment removed for export] *)
      sn F_157fc D_157fc. fixv (Z_to_bv 64 (len + 1)) ltac:(pin; rewrite zbv_addiw_small by lia; reflexivity).   (* [comment removed for export] *)
      stepb_ft F_15800 D_15800 ltac:(condZ).                                          (* [comment removed for export] *)
      sn F_15804 D_15804. sn F_15808 D_15808.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma snw_C : forall regs m (src len dst : Z),
    (1 <= len < 2 ^ 31)%Z -> (1 <= dst < 2 ^ 64)%Z -> (1 <= src < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 dst -> getr regs 9 = Z_to_bv 64 len -> getr regs 18 = Z_to_bv 64 len -> getr regs 8 = Z_to_bv 64 src ->
    exists regs',
      msteps SEGS (mkst regs (0x15908 : word) m rom) (mkst regs' (0x15928 : word) m rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 10 = Z_to_bv 64 dst /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 len
      /\ getr regs' 11 = Z_to_bv 64 (2 ^ 64 - 1 - dst) /\ getr regs' 15 = Z_to_bv 64 (2 ^ 64 - 1 - src)
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [11; 12; 13; 14; 15]%list) regs regs'.
  Proof.
    intros regs m src len dst Hl Hd Hsrc H10 H9 H18 H8. eexists. split.
    - stepb_ft F_1580c D_1580c ltac:(condZ).
      stepb_ft F_15810 D_15810 ltac:(condZ).
      sn F_15814 D_15814. sn F_15818 D_15818.
      sn F_1581c D_1581c. fixv (Z_to_bv 64 (2 ^ 64 - 1 - dst)) ltac:(pin; apply zbv_not; lia).   (* [comment removed for export] *)
      sn F_15820 D_15820.
      sn F_15824 D_15824. fixv (Z_to_bv 64 len) ltac:(pin; apply snew_len2; lia).
      sn F_15828 D_15828. fixv (Z_to_bv 64 (2 ^ 64 - 1 - src)) ltac:(pin; apply zbv_not; lia).   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma snw_L_cont : forall regs m (src dst len i : Z) (b : byte),
    (1 <= src)%Z -> (src + len < 2 ^ 64)%Z -> (1 <= dst)%Z -> (dst + len < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 < len)%Z -> (len < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (src + i)) 1 = Some [b] -> (u b <> 0)%Z -> store_ok SEGS m (Z_to_bv 64 (dst + i)) 1 = true ->
    getr regs 8 = Z_to_bv 64 src -> getr regs 10 = Z_to_bv 64 dst -> getr regs 13 = Z_to_bv 64 i -> getr regs 14 = Z_to_bv 64 len ->
    getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - dst) -> getr regs 15 = Z_to_bv 64 (2 ^ 64 - 1 - src) ->
    exists regs',
      msteps SEGS (mkst regs (0x15928 : word) m rom) (mkst regs' (0x15928 : word) (wbytes m (Z_to_bv 64 (dst + i)) [b]) rom)
      /\ getr regs' 2 = getr regs 2 /\ getr regs' 10 = Z_to_bv 64 dst /\ getr regs' 13 = Z_to_bv 64 (i + 1) /\ getr regs' 14 = Z_to_bv 64 len
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [12; 13; 16; 17]%list) regs regs'.
  Proof.
    intros regs m src dst len i b Hs Hs64 Hd Hd64 Hi Hi1 Hl Rb Nb SOK H8 H10 H13 H14 H11 H15. pose proof (u8_range b) as Ub.
    eexists. split.
    - stepb_ft F_1582c D_1582c ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_15830 D_15830 (Z_to_bv 64 (src + i)).
      stepLBU F_15834 D_15834 b ltac:(addr_norm; exact Rb).
      stepb_ft F_15838 D_15838 ltac:(condZ).
      stepb_ft F_1583c D_1583c ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_15840 D_15840 (Z_to_bv 64 (dst + i)).
      zv F_15844 D_15844 (Z_to_bv 64 (i + 1)).
      stepST F_15848 D_15848 (Z_to_bv 64 (dst + i)) (Z_to_bv 64 (u b)) ltac:(store_ok_peel; exact SOK).
      rewrite b8_norm.
      sn F_1584c D_1584c.
      stepb_tk F_15850 D_15850 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma snw_L_last : forall regs m (s src dst len i : Z) (b : byte) (ret s0v s1v s2v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    (1 <= src)%Z -> (src + len < 2 ^ 64)%Z -> (1 <= dst)%Z -> (dst + len < 2 ^ 64)%Z -> (0 <= i)%Z -> (i + 1 = len)%Z -> (len < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (src + i)) 1 = Some [b] -> (u b <> 0)%Z -> store_ok SEGS m (Z_to_bv 64 (dst + i)) 1 = true ->
    (dst + len <= s - 32 \/ s <= dst)%Z -> ret_ok ret -> sncells m s ret s0v s1v s2v ->
    getr regs 2 = Z_to_bv 64 (s - 32) ->
    getr regs 8 = Z_to_bv 64 src -> getr regs 10 = Z_to_bv 64 dst -> getr regs 13 = Z_to_bv 64 i -> getr regs 14 = Z_to_bv 64 len ->
    getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - dst) -> getr regs 15 = Z_to_bv 64 (2 ^ 64 - 1 - src) ->
    exists regs',
      msteps SEGS (mkst regs (0x15928 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 (dst + i)) [b]) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 dst
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 13; 16; 17; 18]%list) regs regs'.
  Proof.
    intros regs m s src dst len i b ret s0v s1v s2v Hs0 Hs064 Hs Hs64 Hd Hd64 Hi Hi1 Hl Rb Nb SOK DJ Hret CE H2 H8 H10 H13 H14 H11 H15.
    pose proof (u8_range b) as Ub. destruct CE as (C1 & C2 & C3 & C4).
    eexists. split.
    - stepb_ft F_1582c D_1582c ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_15830 D_15830 (Z_to_bv 64 (src + i)).
      stepLBU F_15834 D_15834 b ltac:(addr_norm; exact Rb).
      stepb_ft F_15838 D_15838 ltac:(condZ).
      stepb_ft F_1583c D_1583c ltac:(condZ).                                          (* [comment removed for export] *)
      zv F_15840 D_15840 (Z_to_bv 64 (dst + i)).
      zv F_15844 D_15844 (Z_to_bv 64 (i + 1)).
      stepST F_15848 D_15848 (Z_to_bv 64 (dst + i)) (Z_to_bv 64 (u b)) ltac:(store_ok_peel; exact SOK).
      rewrite b8_norm.
      sn F_1584c D_1584c.
      stepb_ft F_15850 D_15850 ltac:(condZ).
      sn F_15854 D_15854.
      stepLD8 F_158c8 D_158c8 ret. stepLD8 F_158cc D_158cc s0v. stepLD8 F_158d0 D_158d0 s1v. stepLD8 F_158d4 D_158d4 s2v.
      zv F_158d8 D_158d8 (Z_to_bv 64 s).
      stepret F_158dc D_158dc ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsN.

(* [comment removed for export] *)
Lemma lit_rdn : forall C A m md (a : Z) (n : nat) l, W C A m md -> (0x10000 <= a)%Z -> (a + Z.of_nat n <= 0x2b000)%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 a) n = Some l -> rdn SEGS m (Z_to_bv 64 a) n = Some l.
Proof.
  intros C A m md a n l HW Ha Hn R. rewrite <- R. rewrite <- p16_segs. apply (W_rdn_ro C A m md a n HW); cbn [fst snd ll_ro LLU16]; lia.
Qed.

Lemma sl_c1_img : rdn SEGS (fun _ => None) (Z_to_bv 64 0x11768) 8 = Some (Z_to_le_bytes 8 SL_C1).
Proof. vm_refl_bv. Qed.
Lemma sl_c2_img : rdn SEGS (fun _ => None) (Z_to_bv 64 0x11758) 8 = Some (Z_to_le_bytes 8 SL_C2).
Proof. vm_refl_bv. Qed.

#[local] Definition sn_rest : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma snw_loop : forall (k : nat) C A A2 m md vm2 regs (s src dst len : Z) (bs : list byte) (S : TSet) Mi r (i : Z),
  Cok C ->
  (forall m' r', W C A2 m' (with_vmmaps vm2 md) -> POSTM C A s m m' -> cs_kept regs r' -> getr r' 10 = Z_to_bv 64 dst ->
     bytes_at m' dst (bs ++ [Z_to_bv 8 0]) ->
     realizes SEGS (mkCfg (mkst r' (getr regs 1) m' al_rom) (with_vmmaps vm2 md)) S) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok (getr regs 1) ->
  getr regs 2 = Z_to_bv 64 s ->
  (0x10000 <= src)%Z -> (src + len + 1 <= 0x2b000)%Z -> Z.of_nat (length bs) = len -> (1 <= len <= 2027)%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 src) (Datatypes.S (length bs)) = Some (bs ++ [Z_to_bv 8 0]) -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
  (Z.of_nat k = len - 1 - i)%Z -> (0 <= i < len)%Z ->
  bok (alloc_top (c_vm C)) dst (len + 1) -> live A2 (Z_to_bv 64 dst) = Some (len + 1)%Z -> live A (Z_to_bv 64 dst) = None ->
  live (c_A0 C) (Z_to_bv 64 dst) = None -> sub_live A A2 ->
  W C A2 Mi (with_vmmaps vm2 md) -> POSTM C A s m Mi ->
  sncells Mi s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) ->
  (forall j, (0 <= j < i)%Z -> Mi (Z_to_bv 64 (dst + j)) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0))) ->
  (forall j, (i <= j < len + 1)%Z -> Mi (Z_to_bv 64 (dst + j)) = Some (Z_to_bv 8 0)) ->
  getr r 2 = Z_to_bv 64 (s - 32) -> getr r 8 = Z_to_bv 64 src -> getr r 10 = Z_to_bv 64 dst -> getr r 13 = Z_to_bv 64 i -> getr r 14 = Z_to_bv 64 len ->
  getr r 11 = Z_to_bv 64 (2 ^ 64 - 1 - dst) -> getr r 15 = Z_to_bv 64 (2 ^ 64 - 1 - src) ->
  (forall x, In x sn_rest -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x15928 : word) Mi al_rom) (with_vmmaps vm2 md)) S.
Proof.
  induction k as [|k IH]; intros C A A2 m md vm2 regs s src dst len bs S Mi r i CK HK Hs16 Hlo Hhi Hret H2 Hsrc0 Hsrc1 Hlen Hl Rlit NZ Hk Hi
    Bd Ld LdA Ld0 SUB HW PM CE DONE ZERO R2 R8 R10 R12 R14 R11 R15 RR;
    pose proof Bd as (Gd & TOPd & ALd);
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LLU16] in *; unfold sn_rest in RR; unfold CALLOC_STACK, ALLOC_STACK in Hlo;
    pose proof (alloc_top_lt (c_vm C)) as AT; unfold two_pow_64 in AT;
    assert (LA : Z.of_nat (length (bs ++ [Z_to_bv 8 0])) = (len + 1)%Z) by (rewrite length_app; cbn [length]; lia);
    assert (RS : rd_str SEGS Mi src (bs ++ [Z_to_bv 8 0]))
      by (apply rd_str_rdn; replace (length (bs ++ [Z_to_bv 8 0])) with (Datatypes.S (length bs)) by (rewrite length_app; cbn [length]; lia);
          apply (lit_rdn C A2 Mi _ src _ _ HW); [lia | lia | exact Rlit]);
    pose proof (RS i ltac:(lia)) as Rb; rewrite app_nth1 in Rb by lia;
    assert (Nb : (u (nth (Z.to_nat i) bs (Z_to_bv 8 0)) <> 0)%Z)
      by (apply byte_nz_u; rewrite Forall_forall in NZ; apply NZ; apply nth_In; lia);
    set (b := nth (Z.to_nat i) bs (Z_to_bv 8 0)) in *;
    assert (SOK : store_ok SEGS Mi (Z_to_bv 64 (dst + i)) 1 = true)
      by (apply (W_sok_blk C A2 Mi _ _ _ (dst + i) 1 CK HW Ld); rewrite u_Z2bv by lia; cbn; lia);
    set (M' := wbytes Mi (Z_to_bv 64 (dst + i)) [b]);
    assert (WP' : W C A2 M' (with_vmmaps vm2 md) /\ POSTM C A s m M')
      by (subst M'; apply (WP_blk C A A2 m Mi _ (Z_to_bv 64 dst) _ (len + 1) _ s CK (conj HW PM) Ld LdA Ld0 SUB); rewrite !u_Z2bv by lia; cbn; lia);
    assert (DONE' : forall j, (0 <= j < i + 1)%Z -> M' (Z_to_bv 64 (dst + j)) = Some (nth (Z.to_nat j) bs (Z_to_bv 8 0)))
      by (intros j Hj; subst M'; destruct (Z.eq_dec j i) as [->|NE];
          [ rewrite wbytes_inside; rewrite ?u_Z2bv by lia; cbn [length]; [| lia | lia]; replace (dst + i - (dst + i))%Z with 0%Z by lia; reflexivity
          | rewrite wbytes_outside by (rewrite !u_Z2bv by lia; cbn [length]; lia); apply DONE; lia ]);
    assert (ZERO' : forall j, (i + 1 <= j < len + 1)%Z -> M' (Z_to_bv 64 (dst + j)) = Some (Z_to_bv 8 0))
      by (intros j Hj; subst M'; rewrite wbytes_outside by (rewrite !u_Z2bv by lia; cbn [length]; lia); apply ZERO; lia).
  - (* [comment removed for export] *)
    pose proof (blk_range C A2 Mi _ (Z_to_bv 64 dst) _ CK HW Ld ltac:(lia)) as [_ Xd]. rewrite u_Z2bv in Xd by lia.
    destruct (snw_L_last al_rom r Mi s src dst len i b (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rb Nb SOK ltac:(lia) Hret CE R2 R8 R10 R12 R14 R11 R15)
      as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & Q18 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. fold M'.
    apply (HK M' r1 (proj1 WP') (proj2 WP')).
    + apply cs_kept_intro; csr; reflexivity.
    + exact Q10.
    + intros j Hj. rewrite LA in Hj. destruct (Z_lt_ge_dec j len) as [Hlt|Hge].
      * rewrite app_nth1 by lia. apply DONE'. lia.
      * assert (j = len) by lia. subst j. rewrite app_nth2 by lia. replace (Z.to_nat len - length bs)%nat with 0%nat by lia.
        cbn [nth]. apply ZERO'. lia.
  - (* [comment removed for export] *)
    destruct (snw_L_cont al_rom r Mi src dst len i b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rb Nb SOK R8 R10 R12 R14 R11 R15)
      as (r1 & RUN1 & Q2 & Q10 & Q12 & Q14 & Q8 & Q9 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. fold M'.
    assert (CE' : sncells M' s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)).
    { apply (sncells_frame Mi M' s); [lia | lia | exact CE |]. intros x Hx. subst M'.
      pose proof (blk_range C A2 Mi _ (Z_to_bv 64 dst) _ CK HW Ld ltac:(lia)) as [_ X]. rewrite u_Z2bv in X by lia.
      apply wbytes_outside; rewrite u_Z2bv by lia; cbn [length]; lia. }
    apply (IH C A A2 m md vm2 regs s src dst len bs S M' r1 (i + 1)%Z CK HK Hs16 ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) Hhi Hret H2 Hsrc0 Hsrc1 Hlen Hl Rlit NZ ltac:(lia) ltac:(lia)
             Bd Ld LdA Ld0 SUB (proj1 WP') (proj2 WP') CE' DONE' ZERO'); try (csr; reflexivity).
    unfold sn_rest. rest_solve.
Qed.

(* [comment removed for export] *)
Theorem stringNew_W : forall C A m md regs (s src p : Z) (bs wd : list byte) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x45480 ->
  getr regs 10 = Z_to_bv 64 src ->
  (0x10000 <= src)%Z -> (src + Z.of_nat (length bs) + 16 <= 0x2b000)%Z -> (1 <= Z.of_nat (length bs) <= 2027)%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 src) (Datatypes.S (length bs)) = Some (bs ++ [Z_to_bv 8 0]) -> Forall (fun b => b <> Z_to_bv 8 0) bs ->
  (1 <= p <= 7)%Z -> ((src + p) mod 8 = 0)%Z -> (p <= Z.of_nat (length bs))%Z ->
  rdn SEGS (fun _ => None) (Z_to_bv 64 (src + p)) 8 = Some wd -> strlen_stop (Z_to_bv 64 (bytes_le_to_Z wd)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (1 <= kR)%Z -> (RB10_small <= bR)%Z ->
  (forall A' m' vm' regs' (dst : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 dst ->
     selname_at (alloc_top (c_vm C)) A' m' dst bs ->
     live A (Z_to_bv 64 dst) = None -> live (c_A0 C) (Z_to_bv 64 dst) = None ->
     (forall q, q <> Z_to_bv 64 dst -> live A' q = live A q) ->
     aroom A' vm' (kR - 1) (bR - RB10_small) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x158d0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s src p bs wd ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 Hsrc0 Hsrc1 Hlen Rlit NZ Hp Hal Hpl Rwd STOP kR bR HRM HRK HRB HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  set (len := Z.of_nat (length bs)) in *.
  pose proof (alloc_margin_small_le ((len + 1) * 1) ltac:(lia)) as MG. unfold RB10_small in *.
  assert (HsS : (32 <= s)%Z /\ (s < 2 ^ 64)%Z) by (unfold CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  destruct (snw_A al_rom regs m s src ret ltac:(lia) ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(unfold CALLOC_STACK, ALLOC_STACK in Hlo; lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := SNF m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold SNF; unfold CALLOC_STACK, ALLOC_STACK in Hlo; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (sncells_SNF m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  (* [comment removed for export] *)
  assert (RS1 : rd_str SEGS M1 src (bs ++ [Z_to_bv 8 0])).
  { apply rd_str_rdn. replace (length (bs ++ [Z_to_bv 8 0])) with (Datatypes.S (length bs)) by (rewrite length_app; cbn [length]; lia).
    apply (lit_rdn C A M1 md src _ _ HW1); [lia | lia | exact Rlit]. }
  destruct (strlen_run_W al_rom r1 M1 src p bs wd (Z_to_bv 64 0x158f0) RS1 NZ ltac:(lia) ltac:(fold len; lia) Hp Hal Hpl
              (lit_rdn C A M1 md (src + p) 8 wd HW1 ltac:(lia) ltac:(lia) Rwd) STOP
              (lit_rdn C A M1 md 0x11768 8 _ HW1 ltac:(lia) ltac:(lia) sl_c1_img) (lit_rdn C A M1 md 0x11758 8 _ HW1 ltac:(lia) ltac:(lia) sl_c2_img)
              Q1 ltac:(red; apply bv_eq; reflexivity) Q10) as (r2 & RUN2 & P10 & AG2). fold len in P10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  replace (Z_to_bv 64 0x158f0) with (0x158f0 : word) by (apply bv_eq; reflexivity).
  destruct (snw_B al_rom r2 M1 len ltac:(lia) P10) as (r3 & RUN3 & V2 & V1 & V10 & V11 & V8 & V9 & V18 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
  assert (V4 : getr r3 4 = Z_to_bv 64 0x45480)
    by (rewrite (AG3 4) by notin_lit; rewrite (AG2 4) by notin_lit; rewrite (AG1 4) by notin_lit; exact H4).
  assert (V2' : getr r3 2 = Z_to_bv 64 (s - 32)) by (rewrite V2; rewrite (AG2 2) by notin_lit; exact Q2).
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  replace (0x2b0d0 : word) with (Z_to_bv 64 0x2b0d0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure C A M1 _ r3 (len + 1) 1 kR bR (Z_to_bv 64 0x15908) (s - 32) S CK HW1 V10 V11 ltac:(lia) ltac:(lia) ltac:(lia)
           HRM ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; lia) V1
           ltac:(red; apply bv_eq; reflexivity) V4 V2' ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK in *; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 res HW2 Hres CS2 Hnz L0 L1 L00 LEQ ZERO AL16 TOP PM2 HRM2. rewrite ?with_vmmaps_twice in HW2 |- *.
  replace (Z_to_bv 64 0x15908) with (0x15908 : word) by (apply bv_eq; reflexivity).
  pose proof (bok_of_calloc C res ((len + 1) * 1) ltac:(lia) Hnz AL16 TOP) as Bd. replace ((len + 1) * 1)%Z with (len + 1)%Z in * by lia.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (dst := u res) in *. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO. clearbody dst. pose proof Bd as (Gd & TOPd & ALd).
  assert (SUB : sub_live A A2) by (eapply sub_live_new; eassumption).
  assert (PM2' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]).
  assert (CE2 : sncells m2 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18)).
  { destruct CE1 as (C1 & C2 & C3 & C4). unfold sncells.
    rewrite !(FRM_rdn16 C (s - 32) M1 m2 _ _ CK (proj1 PM2)) by (unfold CALLOC_STACK, ALLOC_STACK in Hlo; lia). repeat split; assumption. }
  assert (E9 : getr r4 9 = Z_to_bv 64 len) by (csr; reflexivity).
  assert (E18 : getr r4 18 = Z_to_bv 64 len) by (csr; reflexivity).
  assert (E8 : getr r4 8 = Z_to_bv 64 src) by (csr; reflexivity).
  destruct (snw_C al_rom r4 m2 src len dst ltac:(lia) ltac:(lia) ltac:(lia) Hres E9 E18 E8) as (r5 & RUN5 & Y2 & Y10 & Y12 & Y14 & Y11 & Y15 & Y8 & Y9 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  apply (snw_loop (Z.to_nat (len - 1)) C A A2 m md vm2 regs s src dst len bs S m2 r5 0 CK); try assumption; try lia.
  - (* [comment removed for export] *)
    intros m' r' W' PM' CS' R10' BA'. rewrite H1.
    apply (HK A2 m' vm2 r' dst W' CS' PM' R10').
    + split; [exact Bd|]. split; [exact L1|]. split; [exact NZ | exact BA'].
    + exact L0.
    + exact L00.
    + exact LEQ.
    + rewrite MG in HRM2. exact HRM2.
  - rewrite H1. exact Hret.
  - intros j Hj. unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia.
  - rewrite Y2. csr. reflexivity.
  - rewrite Y8. csr. reflexivity.
  - unfold sn_rest. rest_solve.
Qed.

End SelCreate.
