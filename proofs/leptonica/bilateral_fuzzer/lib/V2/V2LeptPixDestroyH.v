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
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptCmap V2LeptPixDestroy V2LeptPixDestroyK.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require LiaFast.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require V2LeptPixDestroySlot.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocVL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2RelocMusl V2LeptEnv V2LeptG.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptSlots.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Module PxdSegsH.
Section PxdS.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pxdh_A : forall regs m (s pp pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (pp + 8 <= s - 32 \/ s <= pp)%Z -> (4096 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pix mod 16 = 0)%Z -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
    PIXat m pix v -> p_rc v = 1%Z -> (pix + 64 <= s - 32 \/ s <= pix)%Z -> (4096 <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x1982c : word) m rom)
                  (mkst regs' (0x19874 : word)
                        (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
                                (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 8 = Z_to_bv 64 pix /\ getr regs' 9 = Z_to_bv 64 pp
      /\ getr regs' 10 = Z_to_bv 64 (p_data v)
      /\ regs_agree (fun r => In r [2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof. rl_tail (@V2LeptPixDestroySlot.pxdh_A fx v2_reloc v2_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pxdh_E : forall regs m (s pp : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (pp + 8 <= s - 32 \/ s <= pp)%Z -> (4096 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 9 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x198b0 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof. rl_tail (@V2LeptPixDestroySlot.pxdh_E fx v2_reloc v2_code_vl rom). Qed.

End Segs.
End PxdS.
End PxdSegsH.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section DestroyH.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem pixDestroy_free_W : forall C A m md regs (s pp pix R : Z) (v : pixv) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = 0%Z ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  live A (Z_to_bv 64 (p_data v)) = Some R -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None -> (0 < R)%Z -> p_data v <> pix ->
  (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pix /\ p <> Z_to_bv 64 (p_data v)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 pix) = None -> live A' (Z_to_bv 64 (p_data v)) = None ->
     (forall q, q <> Z_to_bv 64 pix -> q <> Z_to_bv 64 (p_data v) -> live A' q = live A q) -> sub_live A' A ->
     POSTD C A' s pp m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1982c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix R v sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 ALpp H10 SL Rpp PX Hrc Ht Hc Lp L0p LD LD0 HR NEdp SBn HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ALLOC_STACK in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) R CK HW LD HR) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Hpp4k Hpptop].
  assert (DJ : (pp + 8 <= s - 32 \/ s <= pp)%Z).
  { destruct (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as [[X _] | (_ & X & Y)]; lia. }
  assert (SOKp : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix v x PX ltac:(lia) E). }
  destruct (PxdSegsH.pxdh_A al_rom regs m s pp pix v ret ltac:(lia) ltac:(lia) DJ Hpp4k ltac:(lia) ALp ALpp
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) SOKp Rpp PX Hrc ltac:(lia) Gp H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q8 & Q9 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C (c_A0 C) s m M0) by (subst M0; wp_win CK).
  assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) s m M1).
  { subst M1. apply (WP_blk C (c_A0 C) A m M0 md (Z_to_bv 64 pix) _ 64); [exact CK | exact WP0 | exact Lp | exact L0p | exact L0p | exact (w_keep _ _ _ _ HW) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  destruct WP1 as [HW1 _].
  assert (PX1 : PIXat M1 pix (set_rc v 0)).
  { subst M1. apply PIX_wr_rc; [|lia]. subst M0.
    repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (R8 : rdn SEGS M1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (subst M1 M0; rdn_solve).
  assert (R16 : rdn SEGS M1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (subst M1 M0; rdn_solve).
  assert (R24 : rdn SEGS M1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (subst M1 M0; rdn_solve).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  destruct (PxdSegs.pxd_B1 al_rom r1 M1 (p_data v) ltac:(lia) ltac:(lia) (W_pmm_free C A M1 md HW1) Q10) as (r2 & RUN2 & P10 & P1 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  assert (P4 : getr r2 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  assert (P2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x3c230 : word) with (Z_to_bv 64 0x3c230) by (apply bv_eq; reflexivity).
  apply (W_free16 C A M1 md r2 (Z_to_bv 64 (p_data v)) (Z_to_bv 64 0x19884) R (s - 32) S CK HW1 P10 LD LD0 P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r3 HWa CSa La LEQa PMa HRTa.
  replace (Z_to_bv 64 0x19884) with (0x19884 : word) by (apply bv_eq; reflexivity).
  assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
  assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (LEQa _ NEpd); exact Lp).
  assert (PXa : PIXat m1 pix (set_rc v 0)).
  { apply (PIXat_frame M1); [exact PX1|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 pix) 64%Z (u x - pix)%Z Lp1 ltac:(lia)) as E.
    unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
  assert (E2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8 : getr r3 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  assert (E9 : getr r3 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  destruct (PxdSegs.pxd_C0 al_rom r3 m1 s pix (set_rc v 0) ltac:(lia) ltac:(lia) PXa ltac:(cbn; exact Ht) ltac:(cbn; exact Hc)
              (W_sok_win C A1 m1 _ (s - 32) 32 CK HWa ltac:(lia) ltac:(cbn; lia)) ltac:(lia) E2 E8) as (r4 & RUN4 & X2 & X8 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN4 |].
  set (M2 := wbytes m1 _ _).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A1 s m1 M2) by (subst M2; wp_win CK).
  destruct WP2 as [HW2 PM2].
  destruct (PxdSegs.pxd_D al_rom r4 M2 pix X8) as (r5 & RUN5 & Z10 & Z1 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  assert (Z4 : getr r5 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
  assert (Z2 : getr r5 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x3c230 : word) with (Z_to_bv 64 0x3c230) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 M2 (with_vmmaps vm1 md) r5 (Z_to_bv 64 pix) (Z_to_bv 64 0x198b0) 64 (s - 32) S CK HW2 Z10 Lp1 L0p Z1
           ltac:(red; apply bv_eq; reflexivity) Z4 Z2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r6 HWb CSb Lb LEQb PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
  replace (Z_to_bv 64 0x198b0) with (0x198b0 : word) by (apply bv_eq; reflexivity).
  assert (NEdp' : Z_to_bv 64 (p_data v) <> Z_to_bv 64 pix) by (apply zneq_w; lia).
  assert (Ld2 : live A2 (Z_to_bv 64 (p_data v)) = None) by (rewrite (LEQb _ NEdp'); exact La).
  assert (EQ2 : forall q, q <> Z_to_bv 64 pix -> q <> Z_to_bv 64 (p_data v) -> live A2 q = live A q).
  { intros q N1 N2. rewrite (LEQb q N1). exact (LEQa q N2). }
  assert (SUB2 : sub_live A2 A).
  { intros q k Lq. assert (N1 : q <> Z_to_bv 64 pix) by (intros ->; rewrite Lq in Lb; discriminate).
    assert (N2 : q <> Z_to_bv 64 (p_data v)) by (intros ->; rewrite Lq in Ld2; discriminate).
    rewrite <- (EQ2 q N1 N2). exact Lq. }
  assert (SUB21 : sub_live A2 A1).
  { intros q k Lq. assert (N1 : q <> Z_to_bv 64 pix) by (intros ->; rewrite Lq in Lb; discriminate).
    rewrite <- (LEQb q N1). exact Lq. }
  assert (SL2 : slotok C A2 s pp sb).
  { apply (slot_keep C A A2 s pp sb SL). intros p n E. destruct (SBn p n E) as [N1 N2]. exact (EQ2 p N1 N2). }
  assert (F2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (F9 : getr r6 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (RR : forall a : Z, (s - 24 <= a)%Z -> (a + 8 <= s)%Z -> rdn SEGS m2 (Z_to_bv 64 a) 8 = rdn SEGS M1 (Z_to_bv 64 a) 8).
  { intros a Ha1 Ha2.
    rewrite (FRM_rdn16 C (s - 32) M2 m2 a 8 CK (proj1 PMb)) by (cbn; lia).
    subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
    rewrite (FRM_rdn16 C (s - 32) M1 m1 a 8 CK (proj1 PMa)) by (cbn; lia). reflexivity. }
  destruct (PxdSegsH.pxdh_E al_rom r6 m2 s pp ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) DJ Hpp4k ltac:(lia) Hret)
    as (r7 & RUN7 & V2 & V1 & V8 & V9 & AG7).
  { rewrite <- p16_segs. exact (slot_sok C A2 m2 _ s pp sb CK HWb SL2 ltac:(lia)). }
  { rewrite (RR (s - 8)%Z) by lia. exact R8. }
  { rewrite (RR (s - 16)%Z) by lia. exact R16. }
  { rewrite (RR (s - 24)%Z) by lia. exact R24. }
  { exact F2. } { exact F9. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN7 |].
  assert (ER1 : forall r, In r cs_rest -> getr r1 r = getr regs r).
  { intros r Hr. apply AG1. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr. }
  assert (REST : forall r, In r cs_rest -> getr r7 r = getr regs r).
  { intros r Hr. pose proof Hr as Hr0. rewrite <- (ER1 r Hr0). cbn [In cs_rest] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ rewrite AG7, (cs_rest_of_kept _ _ CSb _ Hr0), AG5, AG4, (cs_rest_of_kept _ _ CSa _ Hr0), AG2;
        first [reflexivity | notin_lit] |]).
    destruct Hr. }
  apply (HK A2 _ vm2 r7).
  - exact (slot_W C A2 m2 _ s pp sb _ CK HWb SL2 ltac:(lia) ltac:(rewrite length_N_to_le_bytes; reflexivity)).
  - apply cs_kept_of_rest; [rewrite V2, H2; reflexivity | exact V8 | exact V9 | exact REST].
  - exact Lb.
  - exact Ld2.
  - exact EQ2.
  - exact SUB2.
  - assert (PD0 : POSTD C A2 s pp m M0).
    { apply (POSTD_of_POSTM C A A2 s pp m M0); [| exact SUB2].
      apply (POSTM_range C A m md M0 (s - 32) s s CK HW); [| lia | lia | lia].
      intros a Ha. subst M0. rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
    assert (PD1 : POSTD C A2 s pp M0 M1).
    { subst M1. apply (POSTD_deadw C A A2 M0 md (Z_to_bv 64 pix) _ 64 _ s pp CK (proj1 WP0) Lp Lb SUB2); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
    assert (PD2 : POSTD C A2 s pp M1 m1).
    { apply (POSTD_of_POSTM C A1 A2 s pp M1 m1); [| exact SUB21]. eapply POSTM_mono; [|exact PMa]. lia. }
    assert (PD3 : POSTD C A2 s pp m1 M2) by (apply (POSTD_of_POSTM C A1 A2 s pp m1 M2 PM2 SUB21)).
    assert (PD4 : POSTD C A2 s pp M2 m2).
    { apply (POSTD_of_POSTM C A2 A2 s pp M2 m2); [| intros q k Lq; exact Lq]. eapply POSTM_mono; [|exact PMb]. lia. }
    assert (PD5 : POSTD C A2 s pp m2 (wbytes m2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0)))).
    { apply POSTD_slotw; [rewrite length_N_to_le_bytes; reflexivity | lia | lia]. }
    eapply POSTD_trans; [exact PD0|]. eapply POSTD_trans; [exact PD1|]. eapply POSTD_trans; [exact PD2|].
    eapply POSTD_trans; [exact PD3|]. eapply POSTD_trans; [exact PD4|]. exact PD5.
  - rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - room_tac.
Qed.

End DestroyH.
