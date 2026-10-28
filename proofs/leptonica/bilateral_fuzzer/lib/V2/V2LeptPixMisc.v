(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith LibAtomic LeptRecs LeptSlots.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require LiaFast.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require RelocKitVL RelocTacVL CanonImgVL RCodeVL_237d4_24000.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require MuslTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocVL.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Module PxmVL.
Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_237d4_24000 MuslTac.
#[local] Ltac zval ::= rl_zval.
#[local] Ltac condZ ::= rl_condZ.
Section PxmS.
Context {fx : FPState} {RLOC : Reloc} {RCODEF : RelocCodeVL RLOC}.
Variable rom : word -> option byte.

  Lemma pxm_null : forall regs m (s pp : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret ->
    store_ok rl_segs m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn rl_segs m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) -> (pp + 8 <= s - 32 \/ s <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps rl_segs (mkst regs (rl dVL_23d30 0x23d30) m rom)
                     (mkst regs' ret (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                     (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                     (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hs64 Hpp Hpp64 ALpp Hret SOK Rpp DJ H2 H1 H10.
    eexists. split.
    - zv F_23d30 D_23d30 (Z_to_bv 64 (s - 32)).
      stepST F_23d34 D_23d34 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_23d38 D_23d38 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_23d3c D_23d3c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_23d40 D_23d40 ltac:(condZ).
      stepiv F_23d44 D_23d44 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite ALpp; reflexivity).
      stepb_ft F_23d48 D_23d48 ltac:(condZ).
      stepLD F_23d4c D_23d4c (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_tk F_23d50 D_23d50 ltac:(condZ).
      stepLD8 F_23df8 D_23df8 ret.
      stepLD8 F_23dfc D_23dfc (getr regs 8).
      stepLD8 F_23e00 D_23e00 (getr regs 9).
      zv F_23e04 D_23e04 (Z_to_bv 64 s).
      stepret F_23e08 D_23e08 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma pxm_dec : forall regs m (s pp pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret -> (pix mod 16 = 0)%Z -> (1 <= pix)%Z ->
    store_ok rl_segs m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok rl_segs m (Z_to_bv 64 pix) 64 = true -> store_ok rl_segs m (Z_to_bv 64 pp) 8 = true ->
    rdn rl_segs m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) -> (pp + 8 <= s - 32 \/ s <= pp)%Z ->
    PIXat m pix v -> p_rc v = 2%Z -> (pix + 64 <= s - 32)%Z -> (pp + 8 <= pix \/ pix + 64 <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps rl_segs (mkst regs (rl dVL_23d30 0x23d30) m rom)
                     (mkst regs' ret (wbytes (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                     (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                     (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
                                     (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
                                     (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pp pix v ret Hs Hs64 Hpp Hpp64 ALpp Hret Hal Hpix SOK SOKp SOKpp Rpp DJ PX RC Hps DJp H2 H1 H10.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact Hal | reflexivity]).
    eexists. split.
    - zv F_23d30 D_23d30 (Z_to_bv 64 (s - 32)).
      stepST F_23d34 D_23d34 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_23d38 D_23d38 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_23d3c D_23d3c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_23d40 D_23d40 ltac:(condZ).
      stepiv F_23d44 D_23d44 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite ALpp; reflexivity).
      stepb_ft F_23d48 D_23d48 ltac:(condZ).
      stepLD F_23d4c D_23d4c (Z_to_le_bytes 8 pix) (Z_to_bv 64 pix) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_ft F_23d50 D_23d50 ltac:(condZ).
      stepiv F_23d54 D_23d54 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite AL8; reflexivity).
      stepb_ft F_23d58 D_23d58 ltac:(condZ).
      zv F_23d5c D_23d5c (Z_to_bv 64 (pix + 20)).
      sn F_23d60 D_23d60.
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w rl_segs _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 2) (Z_to_bv 64 2) F_23d64 eq_refl D_23d64);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; repeat rdn_peel1; pose proof (PIX_rd_rc rl_segs _ _ _ PX) as RR; rewrite RC in RR; exact RR
          | apply lez4; lia
          | gres; sok_in SOKp ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (2 + 18446744073709551615)%Z) with (Z_to_bv 64 1) by (apply bv_eq; rl_vmc_VL).
      rewrite (v_lw_small 2) by lia.
      sn F_23d68 D_23d68.
      stepb_tk F_23d6c D_23d6c ltac:(condZ).
      stepST F_23db8 D_23db8 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOKpp).
      sn F_23dbc D_23dbc.
      stepLD8 F_23df8 D_23df8 ret.
      stepLD8 F_23dfc D_23dfc (getr regs 8).
      stepLD8 F_23e00 D_23e00 (getr regs 9).
      zv F_23e04 D_23e04 (Z_to_bv 64 s).
      stepret F_23e08 D_23e08 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End PxmS.
End PxmVL.

Section PixMisc.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {PN8 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
Variable rom : word -> option byte.

  Definition pxF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma px_null : forall regs m (s pp : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) -> (pp + 8 <= s - 32 \/ s <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x1982c : word) m rom) (mkst regs' ret (pxF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11]%list) regs regs'.
  Proof. rl_tail (@PxmVL.pxm_null fx v2_reloc v2_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma px_dec : forall regs m (s pp pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret -> (pix mod 16 = 0)%Z -> (1 <= pix)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) -> (pp + 8 <= s - 32 \/ s <= pp)%Z ->
    PIXat m pix v -> p_rc v = 2%Z -> (pix + 64 <= s - 32)%Z -> (pp + 8 <= pix \/ pix + 64 <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x1982c : word) m rom)
                  (mkst regs' ret (wbytes (wbytes (pxF m s ret regs) (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
                                          (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11; 12]%list) regs regs'.
  Proof. rl_tail (@PxmVL.pxm_dec fx v2_reloc v2_code_vl rom). Qed.
End Segs.

Lemma pxF_out : forall m s ret regs (x : word), (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 32 \/ s <= u x)%Z -> pxF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold pxF.
  rewrite !wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
Qed.

Theorem pixDestroy_null_W : forall C A m md regs (s pp : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     (forall x : word, (u x < s - 32 \/ s <= u x)%Z -> m' x = m x) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1982c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret ALpp H10 SL Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  destruct (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Hpp4k Hpptop].
  assert (DJ : (pp + 8 <= s - 32 \/ s <= pp)%Z).
  { destruct (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as [[X _] | (_ & X & Y)]; lia. }
  destruct (px_null al_rom regs m s pp ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp Hret
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := pxF m s ret regs).
  assert (WP0 : W C A M0 md /\ POSTM C (c_A0 C) s m M0) by (subst M0; unfold pxF; wp_win CK).
  apply (HK M0 r1 (proj1 WP0)).
  - apply cs_kept_of_rest; [rewrite Q2, H2; reflexivity | exact Q8 | exact Q9 |].
    intros r Hr. apply AG1. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
  - apply (POSTM_range C A m md M0 (s - 32) s s CK HW); [| lia | lia | lia].
    intros a Ha. subst M0. apply pxF_out; lia.
  - intros x Hx. subst M0. apply pxF_out; lia.
Qed.

Lemma set_rc_rc : forall v z z', set_rc (set_rc v z) z' = set_rc v z'.
Proof. intros v z z'. reflexivity. Qed.
Lemma set_rc_id : forall v, set_rc v (p_rc v) = v.
Proof. intros []. reflexivity. Qed.

(* [comment removed for export] *)
Theorem pixDestroy_dec_W : forall C A m md regs (s pp pix : Z) (v : pixv) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 2%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pix) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     PIXat m' pix (set_rc v 1) -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall x : word, (u x < s - 32 \/ s <= u x)%Z -> ~ (pix + 20 <= u x < pix + 24)%Z -> ~ inslot pp x -> m' x = m x) ->
     mem_grows m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1982c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix v sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret ALpp H10 SL Rpp PX Hrc Lp L0p SBn HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Hpp4k Hpptop].
  assert (DJ : (pp + 8 <= s - 32 \/ s <= pp)%Z).
  { destruct (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as [[X _] | (_ & X & Y)]; lia. }
  assert (Hps : (pix + 64 <= s - 32)%Z) by lia.
  assert (DJp : (pp + 8 <= pix \/ pix + 64 <= pp)%Z).
  { destruct sb as [[p n]|]; cbn in SL.
    - destruct SL as (Lq & _ & Q1 & Q2).
      pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lq) as (Hn0 & _).
      pose proof (round16_ge n Hn0) as Rn. pose proof (round16_ge 64 ltac:(lia)) as R64.
      destruct (ai_live_disjoint A m (m_vmmaps md) p n (Z_to_bv 64 pix) 64 (w_inv _ _ _ _ HW) Lq Lp (SBn p n eq_refl)) as [D|D];
        rewrite u_Z2bv in D by lia; lia.
    - destruct SL as [Q1 Q2]. lia. }
  assert (SOKp : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix v x PX ltac:(lia) E). }
  assert (SOKpp : store_ok SEGS m (Z_to_bv 64 pp) 8 = true).
  { rewrite <- p16_segs. exact (slot_sok C A m md s pp sb CK HW SL ltac:(lia)). }
  destruct (px_dec al_rom regs m s pp pix v ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp Hret ALp ltac:(lia)
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) SOKp SOKpp Rpp DJ PX Hrc Hps DJp H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := pxF m s ret regs).
  assert (WP0 : W C A M0 md /\ POSTM C (c_A0 C) s m M0) by (subst M0; unfold pxF; wp_win CK).
  set (M1 := wbytes M0 (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1))).
  assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) s m M1).
  { subst M1. apply (WP_blk C (c_A0 C) A m M0 md (Z_to_bv 64 pix) _ 64);
      [exact CK | exact WP0 | exact Lp | exact L0p | exact L0p | exact (w_keep _ _ _ _ HW)
      | rewrite !u_Z2bv by lia; lia
      | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  destruct WP1 as [HW1 _].
  assert (PX1 : PIXat M1 pix (set_rc v 1)).
  { subst M1. apply PIX_wr_rc; [|lia]. subst M0. unfold pxF.
    repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  set (M2 := wbytes M1 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  apply (HK M2 r1).
  - exact (slot_W C A M1 md s pp sb _ CK HW1 SL ltac:(lia) ltac:(rewrite length_N_to_le_bytes; reflexivity)).
  - apply cs_kept_of_rest; [rewrite Q2, H2; reflexivity | exact Q8 | exact Q9 |].
    intros r Hr. apply AG1. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
  - subst M2. apply PIXat_out; [exact PX1 | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
  - subst M2. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - intros x Hx1 Hx2 Hx3. unfold inslot in Hx3. subst M2 M1.
    rewrite !wbytes_outside; [subst M0; apply pxF_out; lia | ..]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
  - subst M2 M1 M0. unfold pxF.
    eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply wbytes_grows].
    eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply wbytes_grows]. apply wbytes_grows.
Qed.
End PixMisc.
