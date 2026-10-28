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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import MemsetFillLib MemsetFill_iface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23MemsetFill V23_code_morphA_setall.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSetAll.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Definition SETALL_STACK : Z := 32 + LSF.     (* [comment removed for export] *)

Section SetAll.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma psa_A : forall regs m (s pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix mod 8 = 0)%Z ->
    PIXat (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) pix v -> p_cmap v = 0%Z ->
    (0 <= p_wpl v * p_h v)%Z -> (4 * (p_wpl v * p_h v) < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6ffb4 : word) m rom) (mkst regs' (0x11e6d4 : word) (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x70044
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 255 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl v * p_h v))
      /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pix v ret Hs Hs64 Hpix AL8 PX Hcm Hn Hn31 SOK H2 H1 H10.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF). pose proof (wf_h _ WF). pose proof (wf_data _ WF).
    unfold O23LeptSetAll.FR3 in *. eexists. split.
    - zv F_6ffb4 D_6ffb4 (Z_to_bv 64 (s - 32)).
      stepST F_6ffb8 D_6ffb8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_6ffbc D_6ffbc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_6ffc0 D_6ffc0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_6ffc4 D_6ffc4 ltac:(condZ).
      sn F_6ffc8 D_6ffc8. sn F_6ffcc D_6ffcc.
      stepb_ft F_6f238 D_6f238 ltac:(condZ).
      guard8 F_6f23c D_6f23c AL8.
      stepb_ft F_6f240 D_6f240 ltac:(condZ).
      stepLD F_6f244 D_6f244 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rewrite <- Hcm; exact (PIX_rd_cmap SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepret F_6f248 D_6f248 (0x6ffd0 : word) ltac:(bveq).
      stepb_tk F_6ffd0 D_6ffd0 ltac:(condZ).
      guard8 F_70014 D_70014 AL8.
      stepb_ft F_70018 D_70018 ltac:(condZ).
      stepLD F_7001c D_7001c (Z_to_le_bytes 4 (p_wpl v)) (Z_to_bv 64 (p_wpl v)) ltac:(addr_norm; exact (PIX_rd_wpl SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepLD F_70020 D_70020 (Z_to_le_bytes 4 (p_h v)) (Z_to_bv 64 (p_h v)) ltac:(addr_norm; exact (PIX_rd_h SEGS _ _ _ PX)) ltac:(apply lez4; lia).
      stepiv F_70024 D_70024 (Z_to_bv 64 (4 * p_wpl v)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_70028 D_70028. fixv (Z_to_bv 64 0) ltac:(apply v_mulh_small; lia).
      zv F_7002c D_7002c (Z_to_bv 64 (4 * (p_wpl v * p_h v))).
      sn F_70030 D_70030. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srai_small by lia; f_equal; apply Z.div_small; lia).
      stepb_ft F_70034 D_70034 ltac:(condZ).
      stepLD F_70038 D_70038 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      sn F_7003c D_7003c. sn F_70040 D_70040.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma psa_B : forall regs m (s : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) ->
    exists regs',
      msteps SEGS (mkst regs (0x70044 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret R8 R16 R24 H2. eexists. split.
    - sn F_70044 D_70044. sn F_70048 D_70048.
      stepLD8 F_7008c D_7008c ret. stepLD8 F_70090 D_70090 s0v. stepLD8 F_70094 D_70094 s1v.
      zv F_70098 D_70098 (Z_to_bv 64 s).
      stepret F_7009c D_7009c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma cells3_FR3 : forall m s ret a b, (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS (O23LeptSetAll.FR3 m s ret a b) (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS (O23LeptSetAll.FR3 m s ret a b) (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 a) /\
  rdn SEGS (O23LeptSetAll.FR3 m s ret a b) (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 b).
Proof.
  intros m s ret a b Hs Hs64. unfold O23LeptSetAll.FR3. repeat split; repeat rdn_peel1; rdn_solve.
Qed.

(* [comment removed for export] *)
Theorem pixSetAll_nocmap_W : forall C Ar A m md regs (s pix k : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SETALL_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pix ->
  PIXat m pix v -> live A (Z_to_bv 64 pix) = Some 64%Z -> Z_to_bv 64 pix <> Z_to_bv 64 (p_data v) -> p_cmap v = 0%Z ->
  (1 <= p_wpl v * p_h v)%Z -> (4 * (p_wpl v * p_h v) < 2 ^ 31)%Z ->
  live A (Z_to_bv 64 (p_data v)) = Some k -> (4 * (p_wpl v * p_h v) <= k)%Z ->
  live Ar (Z_to_bv 64 (p_data v)) = None -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pix v ->
     (forall x : word, ~ (p_data v <= u x < p_data v + 4 * (p_wpl v * p_h v))%Z -> ~ scratch C s x -> m' x = m x) ->
     getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6ffb4 : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pix k v ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 PX Lp NEpd Hcm Hn Hn31 Ld Hk Ld0 Ld00 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. unfold SETALL_STACK, LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF). pose proof (wf_h _ WF). pose proof (wf_data _ WF).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) k CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Ld NEpd) as DJ. rewrite !u_Z2bv in DJ by lia.
  unfold round16 in DJ at 1. change ((64 + 15) / 16)%Z with 4%Z in DJ. pose proof (round16_ge k ltac:(lia)).
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (OUT1 : forall x : word, ~ (s - 24 <= u x < s)%Z -> O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9) x = m x).
  { intros x Hx. unfold O23LeptSetAll.FR3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PX1 : PIXat (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) pix v).
  { apply (PIXat_frame m); [exact PX|]. intros x Hx. apply OUT1. lia. }
  destruct (psa_A al_rom regs m s pix v ret ltac:(lia) ltac:(lia) ltac:(lia) AL8 PX1 Hcm ltac:(lia) Hn31 SOK H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) md /\ POSTM C Ar s m (O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)))
    by (unfold O23LeptSetAll.FR3; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (cells3_FR3 m s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
  set (M1 := O23LeptSetAll.FR3 m s ret (getr regs 8) (getr regs 9)) in *.
  assert (SOKd : store_ok SEGS M1 (Z_to_bv 64 (p_data v)) (Z.to_nat (4 * (p_wpl v * p_h v))) = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (M1 x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A M1 _ (Z_to_bv 64 (p_data v)) _ x CK HW1 Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  destruct (memset_fill_o14 r1 M1 al_rom (p_data v) (4 * (p_wpl v * p_h v))%Z 255%Z (Z_to_bv 64 0x70044)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) Q1 Q10 Q11 Q12)
    as (r2 & M2 & RUN2 & A10 & AG2 & ZO & ZG & ZN).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
  replace (Z_to_bv 64 0x70044) with (0x70044 : word) by (apply bv_eq; reflexivity).
  assert (CH : forall a, M2 a <> M1 a -> (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) (p_data v)) as [Hl|Hl]; [exfalso; apply NE; apply ZO; lia|].
    destruct (Z_lt_ge_dec (u a) (p_data v + 4 * (p_wpl v * p_h v))) as [Hh|Hh]; [lia | exfalso; apply NE; apply ZO; lia]. }
  assert (R8 : rdn SEGS M2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite <- C1. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply ZO. lia. }
  assert (R16 : rdn SEGS M2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite <- C2. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply ZO. lia. }
  assert (R24 : rdn SEGS M2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite <- C3. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply ZO. lia. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  destruct (psa_B al_rom r2 M2 s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret R8 R16 R24 E2)
    as (r3 & RUN3 & U2 & U1 & U10 & U8 & U9 & AG3).
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
  - intros x Hx Hsc. rewrite ZO by lia. apply OUT1. intros Hx'. apply Hsc. unfold scratch. lia.
  - exact U10.
Qed.

End SetAll.
