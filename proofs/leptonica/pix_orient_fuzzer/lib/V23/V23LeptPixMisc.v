(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LeptDefs LeptStructs LeptArith LibAtomic LeptRecs LeptSlots.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23_code_6d000_6e000 V23_code_6e000_6f000.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixMisc.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {PN8 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).

  Definition pxF (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma px_null : forall regs m (s pp : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) -> (pp + 8 <= s - 32 \/ s <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x6df98 : word) m rom) (mkst regs' ret (pxF m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hs64 Hpp Hpp64 Hret ALpp SOK Rpp DJ H2 H1 H10.
    eexists. split.
    - zv F_6df98 D_6df98 (Z_to_bv 64 (s - 32)).
      stepST F_6df9c D_6df9c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6dfa0 D_6dfa0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_6dfa4 D_6dfa4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_6dfa8 D_6dfa8 ltac:(condZ).
      zand F_6dfac D_6dfac andi_7 ALpp. stepb_ft F_6dfb0 D_6dfb0 ltac:(condZ).
      stepLD F_6dfb4 D_6dfb4 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_tk F_6dfb8 D_6dfb8 ltac:(condZ).
      unfold pxF.
      stepLD8 F_6e060 D_6e060 ret. stepLD8 F_6e064 D_6e064 (getr regs 8). stepLD8 F_6e068 D_6e068 (getr regs 9).
      zv F_6e06c D_6e06c (Z_to_bv 64 s).
      stepret F_6e070 D_6e070 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma px_dec : forall regs m (s pp pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret -> (pix mod 16 = 0)%Z -> (1 <= pix)%Z -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) -> (pp + 8 <= s - 32 \/ s <= pp)%Z ->
    PIXat m pix v -> p_rc v = 2%Z -> (pix + 64 <= s - 32)%Z -> (pp + 8 <= pix \/ pix + 64 <= pp)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x6df98 : word) m rom)
                  (mkst regs' ret (wbytes (wbytes (pxF m s ret regs) (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
                                          (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pp pix v ret Hs Hs64 Hpp Hpp64 Hret Hal Hpix1 ALpp SOK SOKx SOKp Rpp DJ PX RC Hpix DJ2 H2 H1 H10.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact Hal | reflexivity]).
    assert (PX' : PIXat (pxF m s ret regs) pix v).
    { unfold pxF. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    eexists. split.
    - zv F_6df98 D_6df98 (Z_to_bv 64 (s - 32)).
      stepST F_6df9c D_6df9c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6dfa0 D_6dfa0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_6dfa4 D_6dfa4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_6dfa8 D_6dfa8 ltac:(condZ).
      zand F_6dfac D_6dfac andi_7 ALpp. stepb_ft F_6dfb0 D_6dfb0 ltac:(condZ).
      stepLD F_6dfb4 D_6dfb4 (Z_to_le_bytes 8 pix) (Z_to_bv 64 pix) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_ft F_6dfb8 D_6dfb8 ltac:(condZ).
      zand F_6dfbc D_6dfbc andi_7 AL8. stepb_ft F_6dfc0 D_6dfc0 ltac:(condZ).
      zv F_6dfc4 D_6dfc4 (Z_to_bv 64 (pix + 20)).
      sn F_6dfc8 D_6dfc8.
      change (wbytes (wbytes (wbytes m _ _) _ _) _ _) with (pxF m s ret regs).
      chain_step;
        [ reflexivity
        | eapply (step_amoadd_w SEGS _ _ _ rom _ _ _ _ _ _ (Z_to_le_bytes 4 2) (Z_to_bv 64 2) F_6dfcc eq_refl D_6dfcc);
          [ gres; rewrite u_Z2bv by lia; apply mod16_plus_mod4; [exact Hal | reflexivity]
          | gres; rewrite <- RC; exact (PIX_rd_rc SEGS _ _ _ PX')
          | apply lez4; lia
          | gres; unfold pxF; sok_in SOKx ]
        | step_simpl ].
      gres. rewrite zbv_add. replace (Z_to_bv 64 (2 + 18446744073709551615)%Z) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
      rewrite (v_lw_small 2) by lia.
      sn F_6dfd0 D_6dfd0.
      stepb_tk F_6dfd4 D_6dfd4 ltac:(condZ).
      stepST F_6e020 D_6e020 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(unfold pxF; sok_in SOKp).
      sn F_6e024 D_6e024.
      unfold pxF.
      stepLD8 F_6e060 D_6e060 ret. stepLD8 F_6e064 D_6e064 (getr regs 8). stepLD8 F_6e068 D_6e068 (getr regs 9).
      zv F_6e06c D_6e06c (Z_to_bv 64 s).
      stepret F_6e070 D_6e070 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma pxF_out : forall m s ret regs (x : word), (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  (u x < s - 32 \/ s <= u x)%Z -> pxF m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold pxF.
  repeat (rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
  reflexivity.
Qed.

Theorem pixDestroy_null_W : forall C A m md regs (s pp : Z) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     (forall x : word, (u x < s - 32 \/ s <= u x)%Z -> m' x = m x) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6df98 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 SL ALpp Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (DJ : (pp + 8 <= s - 32 \/ s <= pp)%Z) by lia.
  destruct (px_null al_rom regs m s pp ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret ALpp
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp DJ H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (pxF m s ret regs) md /\ POSTM C A s m (pxF m s ret regs)) by (unfold pxF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  apply (HK _ r1 HW1); [| exact PM1 | intros x Hx; apply pxF_out; lia].
  apply cs_kept_intro; rewrite ?Q2, ?Q8, ?Q9, ?H2; try reflexivity.
  all: rewrite (AG1 _) by notin_lit; reflexivity.
Qed.

Lemma set_rc_rc : forall v z z', set_rc (set_rc v z) z' = set_rc v z'.
Proof. intros v z z'. destruct v; reflexivity. Qed.
Lemma set_rc_id : forall v, set_rc v (p_rc v) = v.
Proof. intros v. destruct v; reflexivity. Qed.

(* [comment removed for export] *)
Theorem pixDestroy_dec_W : forall C A m md regs (s pp pix : Z) (v : pixv) (sb : option (word * Z)) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> slotok C A s pp sb -> (pp mod 8 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 2%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall p k, sb = Some (p, k) -> p <> Z_to_bv 64 pix) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     PIXat m' pix (set_rc v 1) -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall x : word, (u x < s - 32 \/ s <= u x)%Z -> ~ (pix + 20 <= u x < pix + 24)%Z -> ~ inslot pp x -> m' x = m x) ->
     mem_grows m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6df98 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix v sb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 SL ALpp Rpp PX RC Lpix L0pix DISJ HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lpix ltac:(lia)) as [Gpix TOPpix]. rewrite u_Z2bv in Gpix, TOPpix by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpix) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  pose proof (slot_range C A m md s pp sb CK HW SL ltac:(lia)) as [Ppp Ppp2].
  pose proof (slot_where C A m md s pp sb CK HW SL ltac:(lia)) as SW.
  assert (DJ : (pp + 8 <= s - 32 \/ s <= pp)%Z) by lia.
  (* [comment removed for export] *)
  assert (DJ2 : (pp + 8 <= pix \/ pix + 64 <= pp)%Z).
  { destruct sb as [[p n]|]; cbn in SL; [| lia].
    destruct SL as (Lp & _ & R1 & R2).
    pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Lpix (DISJ p n eq_refl)) as D.
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (Hn0 & _). pose proof (round16_ge n Hn0).
    rewrite u_Z2bv in D by lia. change (round16 64) with 64%Z in D. lia. }
  assert (SOKx : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix v x PX ltac:(lia) E). }
  pose proof (slot_sok C A m md s pp sb CK HW SL ltac:(lia)) as SOKp. rewrite p16_segs in SOKp.
  destruct (px_dec al_rom regs m s pp pix v ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret ALp ltac:(lia) ALpp
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) SOKx SOKp Rpp DJ PX RC ltac:(lia) DJ2 H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (HW1 : W C A (pxF m s ret regs) md) by (unfold pxF; pose proof (POSTM_refl C A s m) as PM0; assert (WP : W C A (pxF m s ret regs) md /\ POSTM C A s m (pxF m s ret regs)) by (unfold pxF; wp_win CK); exact (proj1 WP)).
  set (M2 := wbytes (pxF m s ret regs) (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1))).
  assert (HW2 : W C A M2 md).
  { subst M2. apply (W_store_blk C A _ md (Z_to_bv 64 pix) _ 64 _ CK HW1 Lpix L0pix); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; [lia | cbn; lia]. }
  set (M3 := wbytes M2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))).
  assert (HW3 : W C A M3 md).
  { subst M3. apply (slot_W C A M2 md s pp sb _ CK HW2 SL ltac:(lia)). rewrite length_N_to_le_bytes. reflexivity. }
  apply (HK M3 r1 HW3).
  - apply cs_kept_intro; rewrite ?Q2, ?Q8, ?Q9, ?H2; try reflexivity. all: rewrite (AG1 _) by notin_lit; reflexivity.
  - subst M3 M2. apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    rewrite <- (set_rc_rc v 2 1). apply PIX_wr_rc; [|lia].
    rewrite <- RC, set_rc_id. unfold pxF. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX.
  - subst M3. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - intros x Hx N1 N2. unfold inslot in N2. subst M3 M2.
    rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
    rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
    apply pxF_out; lia.
  - subst M3 M2. unfold pxF. intros x Hx. repeat apply wbytes_grows. exact Hx.
Qed.
End PixMisc.
