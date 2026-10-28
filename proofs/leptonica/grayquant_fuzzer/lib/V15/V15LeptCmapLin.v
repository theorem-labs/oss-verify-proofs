(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoom14 DitherLib DitherLoop DitherTab KernelW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptPixCopy V15_code_gqD V15CmapLin.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL14a.
Import V15CL14a.V15LeptDither_iface.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac cs_side := unfold callee_saved; repeat (first [ (left; reflexivity) | right ]); first [ reflexivity | (cbn; lia) | (vm_compute; split; discriminate) ].

Section CmapLinW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma cml_ret : forall {fx : FPState} regs m (ret : word), ret_ok ret -> getr regs 1 = ret ->
  msteps SEGS (mkst regs (Z_to_bv 64 0x18720) m al_rom) (mkst regs ret m al_rom).
Proof.
  intros fx regs m ret Hret H1. replace (Z_to_bv 64 0x18720) with (0x18720 : word) by (apply bv_eq; reflexivity).
  stepret F_1861c D_1861c ret ltac:(exact H1). apply mst_refl.
Qed.

(* [comment removed for export] *)
Lemma CMAPat_fields : forall {fx : FPState} (m : word -> option byte) (c arr d na n : Z), (0 <= c)%Z -> (c + 24 < 2 ^ 64)%Z ->
  cmap_wf (CMAPV arr d na n 0) -> (forall x : word, (c <= u x < c + 24)%Z -> m x <> None) ->
  rdn SEGS m (Z_to_bv 64 c) 8 = Some (Z_to_le_bytes 8 arr) -> rdn SEGS m (Z_to_bv 64 (c + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  rdn SEGS m (Z_to_bv 64 (c + 12)) 4 = Some (Z_to_le_bytes 4 na) -> rdn SEGS m (Z_to_bv 64 (c + 16)) 4 = Some (Z_to_le_bytes 4 n) ->
  (forall i, (20 <= i < 24)%Z -> m (Z_to_bv 64 (c + i)) = Some (Z_to_bv 8 0)) ->
  CMAPat m c (CMAPV arr d na n 0).
Proof.
  intros fx m c arr d na n Hc Hn WF DEF R0 R8 R12 R16 Z20. split; [lia|]. split; [lia|]. split; [exact WF|].
  unfold cmap_bytes. cbn [c_arr c_d c_nalloc c_n c_pad].
  apply bytes_at_app; split; [|apply bytes_at_app; split; [|apply bytes_at_app; split; [|apply bytes_at_app; split]]].
  - apply (rdn_bytes_at SEGS m c (Z_to_le_bytes 8 arr)); rewrite ?length_Z_to_le_bytes; [lia | cbn; lia | | exact R0].
    cbn. intros i Hi. apply DEF. rewrite u_Z2bv by lia. lia.
  - rewrite length_Z_to_le_bytes. apply (rdn_bytes_at SEGS m (c + Z.of_nat 8) (Z_to_le_bytes 4 d)); rewrite ?length_Z_to_le_bytes; [lia | cbn; lia | | exact R8].
    cbn. intros i Hi. apply DEF. rewrite u_Z2bv by lia. lia.
  - rewrite !length_Z_to_le_bytes. replace (c + Z.of_nat 8 + Z.of_nat 4)%Z with (c + 12)%Z by (cbn; lia).
    apply (rdn_bytes_at SEGS m (c + 12) (Z_to_le_bytes 4 na)); rewrite ?length_Z_to_le_bytes; [lia | cbn; lia | | exact R12].
    cbn. intros i Hi. apply DEF. rewrite u_Z2bv by lia. lia.
  - rewrite !length_Z_to_le_bytes. replace (c + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4)%Z with (c + 16)%Z by (cbn; lia).
    apply (rdn_bytes_at SEGS m (c + 16) (Z_to_le_bytes 4 n)); rewrite ?length_Z_to_le_bytes; [lia | cbn; lia | | exact R16].
    cbn. intros i Hi. apply DEF. rewrite u_Z2bv by lia. lia.
  - rewrite !length_Z_to_le_bytes. replace (c + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4)%Z with (c + 20)%Z by (cbn; lia).
    change (Z_to_le_bytes 4 0) with (repeat (Z_to_bv 8 0) 4). apply bytes_at_zeros. intros i Hi. cbn in Hi.
    replace (c + 20 + i)%Z with (c + (20 + i))%Z by lia. apply Z20. lia.
Qed.

Theorem pixcmapCreateLinear24_W : pixcmapCreateLinear24_contract.
Proof.
  unfold pixcmapCreateLinear24_contract, PC_pixcmapCreateLinear, CML_STACK, TP15, RK_cml, RB_cml.
  intros fx C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL. unfold CALLOC_STACK, ALLOC_STACK in *.
  (* [comment removed for export] *)
  assert (sokF : forall k, (8 <= k <= 48)%Z -> store_ok SEGS m (Z_to_bv 64 (s - k)) 8 = true).
  { intros k Hk. apply (W_sok_win C A m md (s - k) 8 CK HW); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (HYPa : ca_hyps s) by (unfold ca_hyps; repeat split; first [assumption | lia]).
  destruct (ca_1849c al_rom s HYPa fx regs m (sokF 8%Z ltac:(lia)) (sokF 16%Z ltac:(lia)) (sokF 24%Z ltac:(lia)) (sokF 32%Z ltac:(lia)) (sokF 40%Z ltac:(lia))
              (sokF 48%Z ltac:(lia)) H2 H10 H11)
    as (r1 & m1 & RUN1 & FR1 & Q1 & Q2 & Q9 & Q10 & Q11 & Q12 & Q18 & Q19 & SVra & SV8 & SV9 & SV18 & SV19 & SV20 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct (rinv_WP C A A m md m1 s _ CK HW (sub_live_refl A) Hhi FR1) as [HW1 PM1].
  { intros r Hr. left. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbn [fst snd]; lia |]). destruct Hr. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x455c0) by (rewrite (AG1 4%bv) by notin_list; exact H4).
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x2891c) with (Z_to_bv 64 166172) by reflexivity.
  apply (W_calloc16_sure C A m1 md r1 1 24 kR bR (Z_to_bv 64 99860) (s - 48) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia) Hrm ltac:(lia)
           ltac:(rewrite alloc_margin_small by lia; lia) ltac:(unfold ROOM_NMAX; lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r2 res HW2 E10 CS2 NZ2 L0c L1c L00c LEQ2 Z2 AL2 TOP2 PM2 Hrm2.
  set (cm := u res) in *. assert (Ecm : res = Z_to_bv 64 cm) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite Ecm in *.
  assert (Gcm : (4096 <= cm)%Z /\ (cm + 24 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A2 m2 _ (Z_to_bv 64 cm) 24 CK HW2 L1c ltac:(lia)) as [X Y]. rewrite u_Z2bv in X, Y by (pose proof (u64_range res); unfold cm; lia). lia. }
  assert (Rcm : (0 <= cm < 2 ^ 64)%Z) by (pose proof (u64_range res); unfold cm in *; lia).
  rewrite ?u_Z2bv in AL2, TOP2, NZ2 by lia. change (1 * 24)%Z with 24%Z in *.
  (* [comment removed for export] *)
  pose proof (blk_sok C A2 m2 _ cm 24 CK HW2 L1c ltac:(lia) ltac:(lia) ltac:(lia)) as SOKc.
  assert (HYPb : cb_hyps (s - 48) cm).
  { unfold cb_hyps. repeat split; first [lia | exact AL2 | (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)]. }
  destruct (cb_18510 al_rom (s - 48) cm HYPb fx r2 m2
              ltac:(apply (reg_sok SEGS m2 m2 cm _ (cm + 8) 4 (mem_grows_refl _) SOKc); cbn; lia)
              ltac:(apply (reg_sok SEGS m2 m2 cm _ (cm + 12) 4 (mem_grows_refl _) SOKc); cbn; lia)
              ltac:(rewrite (CS2 2%bv) by cs_side; exact Q2) ltac:(rewrite (CS2 9%bv) by cs_side; exact Q9) E10
              ltac:(rewrite (CS2 18%bv) by cs_side; exact Q18) ltac:(rewrite (CS2 19%bv) by cs_side; exact Q19))
    as (r3 & m3 & RUN3 & FR3 & P1 & P8 & P10 & P11 & SVd & SVn & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  assert (SUB2 : sub_live A A2) by (apply (sub_live_new A A2 (Z_to_bv 64 cm) 24 L0c L1c LEQ2)).
  destruct (rinv_WP C A2 A m2 (with_vmmaps vm2 md) m3 (s - 48) _ CK HW2 SUB2 ltac:(lia) FR3) as [HW3 PM3].
  { intros r Hr. right. exists (Z_to_bv 64 cm), 24%Z. rewrite u_Z2bv by lia. cbn [In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd]; (split; [exact L1c|]; split; [exact L0c|]; split; [exact L00c|]; lia). }
  (* [comment removed for export] *)
  assert (P4 : getr r3 4 = Z_to_bv 64 0x455c0) by (rewrite (AG3 4%bv) by notin_list; rewrite (CS2 4%bv) by cs_side; exact Q4).
  assert (P2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (rewrite (AG3 2%bv) by notin_list; rewrite (CS2 2%bv) by cs_side; exact Q2).
  replace (Z_to_bv 64 0x2891c) with (Z_to_bv 64 166172) by reflexivity.
  apply (W_calloc16_sure C A2 m3 (with_vmmaps vm2 md) r3 4 4 (kR - 1) (bR - alloc_margin 24) (Z_to_bv 64 99896) (s - 48) S CK HW3 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hrm2) ltac:(lia)
           ltac:(rewrite !alloc_margin_small by lia; lia) ltac:(unfold ROOM_NMAX; lia) P1 ltac:(red; apply bv_eq; reflexivity) P4 P2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A4 m4 vm4 r4 res4 HW4 F10 CS4 NZ4 L0a L1a L00a LEQ4 Z4 AL4 TOP4 PM4 Hrm4. rewrite with_vmmaps_twice in HW4 |- *.
  set (arr := u res4) in *. assert (Earr : res4 = Z_to_bv 64 arr) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite Earr in *.
  assert (Rarr : (0 <= arr < 2 ^ 64)%Z) by (pose proof (u64_range res4); unfold arr in *; lia).
  change (4 * 4)%Z with 16%Z in *.
  assert (Garr : (4096 <= arr)%Z /\ (arr + 16 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A4 m4 _ (Z_to_bv 64 arr) 16 CK HW4 L1a ltac:(lia)) as [X Y]. rewrite u_Z2bv in X, Y by lia. lia. }
  assert (L1c4 : live A4 (Z_to_bv 64 cm) = Some 24%Z).
  { rewrite LEQ4; [exact L1c|]. intros E. rewrite E in L1c. rewrite L1c in L0a. discriminate. }
  assert (NEca : Z_to_bv 64 cm <> Z_to_bv 64 arr) by (intros E; rewrite E in L1c; rewrite L1c in L0a; discriminate).
  pose proof (blk_apart C A4 m4 _ _ _ 24 16 CK HW4 L1c4 L1a NEca ltac:(lia) ltac:(lia)) as APca. rewrite !u_Z2bv in APca by lia.
  (* [comment removed for export] *)
  assert (KEEP : forall k v, (8 <= k <= 48)%Z -> rdn SEGS m1 (Z_to_bv 64 (s - k)) 8 = Some v -> rdn SEGS m4 (Z_to_bv 64 (s - 48 + (48 - k))) 8 = Some v).
  { intros k v Hk R. replace (s - 48 + (48 - k))%Z with (s - k)%Z by lia. rewrite <- R.
    rewrite (FRM_rdn16 C (s - 48) m3 m4 (s - k) 8 CK (proj1 PM4)) by (cbn; lia).
    rewrite (mframe_rdn SEGS _ m2 m3 (s - k) 8 FR3) by (try lia; try (cbn; lia); intros c [<- | [<- | []]]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    apply (FRM_rdn16 C (s - 48) m1 m2 (s - k) 8 CK (proj1 PM2)); cbn; lia. }
  pose proof (blk_sok C A4 m4 _ cm 24 CK HW4 L1c4 ltac:(lia) ltac:(lia) ltac:(lia)) as SOKc4.
  pose proof (blk_sok C A4 m4 _ arr 16 CK HW4 L1a ltac:(lia) ltac:(lia) ltac:(lia)) as SOKa4.
  assert (sokA : forall k, (0 <= k <= 15)%Z -> store_ok SEGS m4 (Z_to_bv 64 (arr + k)) 1 = true).
  { intros k Hk. apply (reg_sok SEGS m4 m4 arr _ (arr + k) 1 (mem_grows_refl _) SOKa4); cbn; lia. }
  assert (KN4 : rdn SEGS m4 (Z_to_bv 64 (cm + 12)) 4 = Some (Z_to_le_bytes 4 4)).
  { rewrite <- w2b_Z by lia. rewrite <- SVn. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    exact (LIVK_at A2 m3 m4 cm 24 x (proj2 PM4) L1c ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (HYPc : cc_hyps (s - 48) cm arr).
  { unfold cc_hyps, dapart.
    repeat split; first [lia | exact AL2 | exact AL4 | (rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)]. }
  destruct (cc_18534 al_rom (s - 48) cm arr HYPc fx r4 m4 _ _ _ _ _ _
              (KEEP 8%Z _ ltac:(lia) SVra) (KEEP 16%Z _ ltac:(lia) SV8) (KEEP 24%Z _ ltac:(lia) SV9) (KEEP 32%Z _ ltac:(lia) SV18) (KEEP 40%Z _ ltac:(lia) SV19)
              ltac:(replace (s - 48)%Z with (s - 48 + (48 - 48))%Z by lia; exact (KEEP 48%Z _ ltac:(lia) SV20))
              ltac:(apply (reg_sok SEGS m4 m4 cm _ cm 8 (mem_grows_refl _) SOKc4); cbn; lia)
              ltac:(apply (reg_sok SEGS m4 m4 cm _ (cm + 16) 4 (mem_grows_refl _) SOKc4); cbn; lia)
              (sokA 2%Z ltac:(lia)) ltac:(replace arr with (arr + 0)%Z by lia; apply sokA; lia) (sokA 1%Z ltac:(lia)) (sokA 3%Z ltac:(lia)) (sokA 6%Z ltac:(lia)) (sokA 4%Z ltac:(lia))
              (sokA 5%Z ltac:(lia)) (sokA 7%Z ltac:(lia)) (sokA 10%Z ltac:(lia)) (sokA 8%Z ltac:(lia)) (sokA 9%Z ltac:(lia)) (sokA 11%Z ltac:(lia)) (sokA 14%Z ltac:(lia))
              (sokA 12%Z ltac:(lia)) (sokA 13%Z ltac:(lia)) (sokA 15%Z ltac:(lia)) KN4
              ltac:(rewrite (CS4 2%bv) by cs_side; exact P2) ltac:(rewrite (CS4 8%bv) by cs_side; exact P8) F10
              ltac:(rewrite (CS4 18%bv) by cs_side; rewrite (AG3 18%bv) by notin_list; rewrite (CS2 18%bv) by cs_side; exact Q18))
    as (r5 & m5 & RUN5 & FR5 & X1 & X2 & X5 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X18 & X19 & X20 & SVarr
        & SA0 & SA1 & SA2 & SA3 & SA4 & SA5 & SA6 & SA7 & SA8 & SA9 & SA10 & SA11 & SA12 & SA13 & SA14 & SA15 & SVnn & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
  rewrite rdv_word8 in X1, X8, X9, X18, X19, X20.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact (cml_ret r5 m5 ret Hret ltac:(rewrite X1; exact H1)) |].
  (* [comment removed for export] *)
  assert (L0a' : live A (Z_to_bv 64 arr) = None) by (rewrite <- (LEQ2 (Z_to_bv 64 arr)); [exact L0a | intros E; apply NEca; symmetry; exact E]).
  assert (LEQ : forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 arr -> live A4 q = live A q) by (intros q N1 N2; rewrite (LEQ4 q N2); exact (LEQ2 q N1)).
  assert (SUB4 : sub_live A A4) by exact (sub_live_new2 A A4 _ _ 24 16 L0c L0a' L1c4 L1a LEQ).
  destruct (rinv_WP C A4 A m4 (with_vmmaps vm4 md) m5 (s - 48) _ CK HW4 SUB4 ltac:(lia) FR5) as [HW5 PM5].
  { intros r Hr. right. cbn [In] in Hr.
    destruct Hr as [<- | [<- | Hr]]; [exists (Z_to_bv 64 cm), 24%Z | exists (Z_to_bv 64 cm), 24%Z | exists (Z_to_bv 64 arr), 16%Z]; rewrite u_Z2bv by lia;
      [ cbn [fst snd]; (split; [exact L1c4|]; split; [exact L0c|]; split; [exact L00c|]; lia) ..
      | split; [exact L1a|]; split; [exact L0a'|]; split; [exact L00a|];
        repeat (destruct Hr as [<- | Hr]; [cbn [fst snd]; lia |]); destruct Hr ]. }
  assert (PMall : POSTM C A s m m5).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_mono; [|eapply POSTM_trans; [exact PM2|]; eapply POSTM_trans; [exact PM3|]; eapply POSTM_trans; [exact (POSTM_sub C A A2 _ m3 m4 SUB2 PM4) | exact PM5]]. lia. }
  apply (HK A4 m5 vm4 r5 cm arr HW5).
  - apply cs_kept_intro; first [ assumption | (rewrite X2, H2; f_equal; lia)
      | (rewrite (AG5 _) by notin_list; rewrite (CS4 _) by cs_side; rewrite (AG3 _) by notin_list; rewrite (CS2 _) by cs_side; apply AG1; notin_list) ].
  - exact PMall.
  - exact X10.
  - unfold cmap_new. cbn [c_arr c_nalloc]. change (4 * 4)%Z with 16%Z.
    assert (T32 : (cm + 32 <= alloc_top (c_vm C))%Z) by (replace 32%Z with (round16 24) by reflexivity; exact TOP2).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj L0c (conj L0a' (conj L00c (conj L00a (conj L1c4 (conj L1a (conj _ (conj _ LEQ))))))))))))); try lia.
    + apply CMAPat_fields; try lia.
      * constructor; cbn; lia.
      * intros x Hx. destruct (blk_byte C A4 m5 _ (Z_to_bv 64 cm) 24 x CK HW5 L1c4 ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact D.
      * rewrite <- w2b_Z by lia. exact SVarr.
      * rewrite <- w2b_Z by lia. rewrite <- SVd.
        rewrite (mframe_rdn SEGS _ m4 m5 (cm + 8) 4 FR5) by (try lia; try (cbn; lia); intros c0 Hc0; cbn [In] in Hc0;
          repeat (destruct Hc0 as [<- | Hc0]; [cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia |]); destruct Hc0).
        apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
        exact (LIVK_at A2 m3 m4 cm 24 x (proj2 PM4) L1c ltac:(lia) ltac:(lia) ltac:(lia)).
      * rewrite <- KN4.
        apply (mframe_rdn SEGS _ m4 m5 (cm + 12) 4 FR5); [lia | cbn; lia |]. intros c0 Hc0; cbn [In] in Hc0.
        repeat (destruct Hc0 as [<- | Hc0]; [cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia |]); destruct Hc0.
      * rewrite <- w2b_Z by lia. exact SVnn.
      * intros i Hi. destruct FR5 as [_ EQ5]. rewrite EQ5.
        -- rewrite (LIVK_at A2 m3 m4 cm 24 (Z_to_bv 64 (cm + i)) (proj2 PM4) L1c ltac:(lia) ltac:(lia) ltac:(rewrite u_Z2bv by lia; lia)).
           destruct FR3 as [_ EQ3]. rewrite EQ3.
           ++ pose proof (Z2 i ltac:(lia)) as ZZ. unfold at_ in ZZ. rewrite u_Z2bv in ZZ by lia. exact ZZ.
           ++ intros c0 [<- | [<- | []]]; unfold incell; cbn [fst snd]; rewrite u_Z2bv by lia; lia.
        -- intros c0 Hc0. cbn [In] in Hc0. unfold incell. rewrite u_Z2bv by lia.
           repeat (destruct Hc0 as [<- | Hc0]; [cbn [fst snd]; lia |]). destruct Hc0.
    + unfold cmap_ok. cbn [c_d c_nalloc c_n c_arr]. split; [right; left; reflexivity|]. repeat split; lia.
  - rewrite !alloc_margin_small in Hrm4 by lia. replace (kR - 1 - 1)%Z with (kR - 2)%Z in Hrm4 by lia.
    replace (bR - 2 ^ 17 - 2 ^ 17)%Z with (bR - 2 * 2 ^ 17)%Z in Hrm4 by lia. exact Hrm4.
Qed.
End CmapLinW.
