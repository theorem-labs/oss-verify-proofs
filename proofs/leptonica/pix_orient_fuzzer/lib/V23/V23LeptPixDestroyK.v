(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptCmap V23LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.VL Require LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocCode V23RelocSites V23RelocImg V23RelocVL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23RelocMusl V23LeptEnv V23LeptG.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixDestroy.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Module PxdSegs.
Section PxdS.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pxd_A : forall regs m (s pp pix : Z) (v : pixv) (ret : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pix mod 16 = 0)%Z -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
    PIXat m pix v -> p_rc v = 1%Z -> (pix + 64 <= s - 32 \/ s <= pix)%Z -> (4096 <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x6df98 : word) m rom)
                  (mkst regs' (0x6dfe0 : word)
                        (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
                                (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 8 = Z_to_bv 64 pix /\ getr regs' 9 = Z_to_bv 64 pp
      /\ getr regs' 10 = Z_to_bv 64 (p_data v)
      /\ regs_agree (fun r => In r [2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixDestroy.pxd_A fx v23_reloc v23_code_vl rom). Qed.
  (* [comment removed for export] *)
  Lemma pxd_B1 : forall regs m (data : Z),
    (1 <= data)%Z -> (data < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x127c80) 8 = Some (Z_to_le_bytes 8 0x10e818) ->
    getr regs 10 = Z_to_bv 64 data ->
    exists regs',
      msteps SEGS (mkst regs (0x6dfe0 : word) m rom) (mkst regs' (0x10e818 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 data /\ getr regs' 1 = Z_to_bv 64 0x6dff0
      /\ regs_agree (fun r => In r [1; 11]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixDestroy.pxd_B1 fx v23_reloc v23_sites v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pxd_B0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (0x6dfe0 : word) m rom) (mkst regs (0x6dff0 : word) m rom).
  Proof. rl_tail (@VL.LeptPixDestroy.pxd_B0 fx v23_reloc v23_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pxd_C1 : forall regs m (s pix cm : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_text v = 0%Z -> p_cmap v = cm -> (1 <= cm)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6dff0 : word) m rom)
                  (mkst regs' (0x7350c : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 cm))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x6e010
      /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixDestroy.pxd_C1 fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pxd_C2 : forall regs m (pix : Z),
    (0 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 8 = Z_to_bv 64 pix ->
    msteps SEGS (mkst regs (0x6e010 : word) m rom)
                (mkst regs (0x6e014 : word) (wbytes m (Z_to_bv 64 (pix + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom).
  Proof. rl_tail (@VL.LeptPixDestroy.pxd_C2 fx v23_reloc v23_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pxd_C0 : forall regs m (s pix : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_text v = 0%Z -> p_cmap v = 0%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6dff0 : word) m rom)
                  (mkst regs' (0x6e014 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixDestroy.pxd_C0 fx v23_reloc v23_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pxd_D : forall regs m (pix : Z),
    getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6e014 : word) m rom) (mkst regs' (0x10e818 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 1 = Z_to_bv 64 0x6e01c
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixDestroy.pxd_D fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pxd_E : forall regs m (s pp : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 9 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x6e01c : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixDestroy.pxd_E fx v23_reloc v23_code_vl rom). Qed.

End Segs.
End PxdS.
End PxdSegs.

Section DestroyK.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WKEEP (C : lctx) (s pp : Z) (m m' : word -> option byte) : Prop :=
  forall a : word, (s <= u a < c_top C)%Z -> ~ (pp <= u a < pp + 8)%Z -> m' a = m a.

Lemma WKEEP_trans : forall C s pp m1 m2 m3, WKEEP C s pp m1 m2 -> WKEEP C s pp m2 m3 -> WKEEP C s pp m1 m3.
Proof. intros C s pp m1 m2 m3 A B a H1 H2. rewrite (B a H1 H2). exact (A a H1 H2). Qed.

Lemma WKEEP_FRM : forall C s s' pp m m', Cok C -> FRM C s' m m' -> (s' <= s)%Z -> (c_top C - LSTK <= s')%Z -> WKEEP C s pp m m'.
Proof.
  intros C s s' pp m m' CK F Hs Hlo a Ha _. pose proof (win_facts C a CK ltac:(unfold win; lia)) as (_ & AT & NG & NE & NH & _).
  apply F; [apply above_not_gap; lia | exact NG | exact NE | exact NH | unfold scratch; lia].
Qed.

Lemma WKEEP_below : forall C s pp m (a0 : word) bs, (u a0 + Z.of_nat (length bs) <= s)%Z -> (s <= c_top C)%Z -> (c_top C <= 2 ^ 64)%Z ->
  WKEEP C s pp m (wbytes m a0 bs).
Proof. intros C s pp m a0 bs H Hs Ht a Ha _. apply wbytes_outside; lia. Qed.

Lemma WKEEP_slot : forall C s pp m bs, length bs = 8%nat -> (0 <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> WKEEP C s pp m (wbytes m (Z_to_bv 64 pp) bs).
Proof. intros C s pp m bs L Hp Hp8 a Ha Hn. apply wbytes_outside; rewrite L, u_Z2bv by lia; cbn; lia. Qed.

Lemma POSTM_stack_any : forall C A' m' md' m (a : word) bs (s : Z), Cok C -> W C A' m' md' ->
  (c_top C - LSTK <= u a)%Z -> (u a + Z.of_nat (length bs) <= s)%Z -> (s <= c_top C)%Z -> POSTM C A' s m (wbytes m a bs).
Proof.
  intros C A' m' md' m a bs s CK HW' Hlo Hhi Hs. pose proof CK as [T1 T2 T3 T4 T5]. split.
  - intros x _ _ _ _ H5. unfold scratch in H5. apply wbytes_outside; lia.
  - intros q k i Lq Hi. destruct (blk_byte C A' m' md' q k (at_ q i) CK HW' Lq) as (_ & _ & _ & NW & _).
    + unfold at_. pose proof (ai_live_hull A' m' (m_vmmaps md') q k (w_inv _ _ _ _ HW') Lq) as (Hk0 & _ & TOP & _). pose proof (u64_range q).
      pose proof (round16_ge k Hk0). pose proof (alloc_top_lt (m_vmmaps md')) as AT. unfold two_pow_64 in AT. rewrite u_Z2bv; lia.
    + unfold win in NW. apply wbytes_outside; lia.
Qed.

Lemma LIVK_freed_blk : forall C A m md A' (p a : word) (n : Z) bs, Cok C -> W C A m md -> live A p = Some n ->
  (forall q k, live A' q = Some k -> live A q = Some k) -> live A' p = None ->
  (u p <= u a)%Z -> (u a + Z.of_nat (length bs) <= u p + n)%Z -> LIVK A' m (wbytes m a bs).
Proof.
  intros C A m md A' p a n bs CK HW Lp SUB Lp' Hlo Hhi q k i Lq Hi.
  pose proof (SUB q k Lq) as LqA. assert (NE : p <> q) by (intros ->; rewrite Lq in Lp'; discriminate).
  pose proof (ai_live_hull A m (m_vmmaps md) q k (w_inv _ _ _ _ HW) LqA) as (Hk0 & _ & TOPq & _). pose proof (round16_ge k Hk0).
  pose proof (ai_live_hull A m (m_vmmaps md) p n (w_inv _ _ _ _ HW) Lp) as (Hn0 & _ & TOPp & _). pose proof (round16_ge n Hn0).
  pose proof (alloc_top_lt (m_vmmaps md)) as AT. unfold two_pow_64 in AT. pose proof (u64_range q). pose proof (u64_range p). pose proof (u64_range a).
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp LqA NE) as [D|D];
    unfold at_; apply wbytes_outside; rewrite ?u_Z2bv by lia; lia.
Qed.

Lemma pixDestroy_wkeep_fin : forall C A m md regs (s pp pix : Z) (ret s0v s1v : word) (S : TSet),
  Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix -> getr regs 9 = Z_to_bv 64 pp -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) ->
     getr regs' 2 = Z_to_bv 64 s -> getr regs' 8 = s0v -> getr regs' 9 = s1v ->
     (forall r, In r cs_rest -> getr regs' r = getr regs r) ->
     live A' (Z_to_bv 64 pix) = None -> (forall q, q <> Z_to_bv 64 pix -> live A' q = live A q) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> WKEEP C s pp m m' -> POSTM C A' (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6e014 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix ret s0v s1v S CK HW Hs16 Hlo Hpp Hpphi Hret H2 H8 H9 H4 R8 R16 R24 Lp L0p HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ALLOC_STACK in Hlo.
  destruct (PxdSegs.pxd_D al_rom regs m pix H8) as (r1 & RUN1 & Q10 & Q1 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  assert (Q2 : getr r1 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x10e818 : word) with (Z_to_bv 64 0x10e818) by (apply bv_eq; reflexivity).
  apply (W_free16 C A m md r1 (Z_to_bv 64 pix) (Z_to_bv 64 0x6e01c) 64 (s - 32) S CK HW Q10 Lp L0p Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 HWa CSa La LEQa PMa HRTa.
  replace (Z_to_bv 64 0x6e01c) with (0x6e01c : word) by (apply bv_eq; reflexivity).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  destruct (PxdSegs.pxd_E al_rom r2 m1 s pp ret s0v s1v ltac:(lia) Hpp ltac:(lia) Hret) as (r3 & RUN3 & V2 & V1 & V8 & V9 & AG3).
  { apply (W_sok_win C A1 m1 _ pp 8 CK HWa); [lia | cbn; lia]. }
  { rewrite (FRM_rdn16 C (s - 32) m m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). exact R8. }
  { rewrite (FRM_rdn16 C (s - 32) m m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact R16. }
  { rewrite (FRM_rdn16 C (s - 32) m m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact R24. }
  { exact E2. } { exact E9. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (WP : W C A1 (wbytes m1 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm1 md) /\
               POSTM C (c_A0 C) (pp + 8) m (wbytes m1 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0)))).
  { apply (WP_win C A1 (c_A0 C) m m1 _ _ _ (pp + 8) CK); [| exact (w_keep _ _ _ _ HWa) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
    split; [exact HWa|]. apply (POSTM_sub C (c_A0 C) A1); [exact (w_keep _ _ _ _ HWa)|]. eapply POSTM_mono; [|exact PMa]. lia. }
  destruct WP as [HW3 PM3].
  apply (HK A1 _ vm1 r3); try assumption; try (solve [room_tac]).
  - intros r Hr. cbn [In cs_rest] in Hr.
    repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]). destruct Hr.
  - eapply WKEEP_trans; [apply (WKEEP_FRM C s (s - 32) pp m m1 CK (proj1 PMa)); lia | apply WKEEP_slot; [rewrite length_N_to_le_bytes; reflexivity | lia | lia]].
  - eapply POSTM_trans; [eapply POSTM_mono; [|exact PMa]; lia|]. eapply (POSTM_wbytes_win C A1 m1 _ _ _ (pp + 8) CK HWa); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
  - rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
Qed.

Lemma pixDestroy_wkeep_tail : forall C A m md regs (s pp pix cm karr : Z) (v : pixv) (cv : cmapv) (ret s0v s1v : word) (S : TSet),
  Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix -> getr regs 9 = Z_to_bv 64 pp -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
  PIXat m pix v -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) ->
     getr regs' 2 = Z_to_bv 64 s -> getr regs' 8 = s0v -> getr regs' 9 = s1v ->
     (forall r, In r cs_rest -> getr regs' r = getr regs r) ->
     live A' (Z_to_bv 64 pix) = None ->
     (cm <> 0%Z -> live A' (Z_to_bv 64 cm) = None /\ live A' (Z_to_bv 64 (c_arr cv)) = None) ->
     (forall q, q <> Z_to_bv 64 pix -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 (c_arr cv)) -> live A' q = live A q) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> WKEEP C s pp m m' -> POSTM C A' (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6dff0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix cm karr v cv ret s0v s1v S CK HW Hs16 Hlo Hpp Hpphi Hret H2 H8 H9 H4 R8 R16 R24 PX Ht Hc Lp L0p HCM HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ALLOC_STACK in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct HCM as [Hcm0 | (CM & Lcm & Larr & L0cm & L0arr & NE1 & NE2 & NE3 & Hk)].
  - 
    rewrite Hcm0 in Hc.
    destruct (PxdSegs.pxd_C0 al_rom regs m s pix v ltac:(lia) ltac:(lia) PX Ht Hc SOK ltac:(lia) H2 H8) as (r1 & RUN1 & Q2 & Q8 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    set (M1 := wbytes m _ _).
    assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1) by (subst M1; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (Q9 : getr r1 9 = Z_to_bv 64 pp) by (csr; reflexivity).
    assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    apply (pixDestroy_wkeep_fin C A M1 md r1 s pp pix ret s0v s1v S CK HW1 Hs16 ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi Hret Q2 Q8 Q9 Q4);
      [subst M1; rdn_solve | subst M1; rdn_solve | subst M1; rdn_solve | exact Lp | exact L0p |].
    intros A' m' vm' regs' HW' X2 X8 X9 XR L' LEQ' PM' WK' PMA' Rpp' RT'.
    apply (HK A' m' vm' regs' HW' X2 X8 X9); try assumption; try (solve [room_tac]).
    + intros r Hr. rewrite (XR r Hr). apply AG1. cbn [In cs_rest] in Hr.
      repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
    + intros X. exfalso. apply X. exact Hcm0.
    + intros q N1 _. apply LEQ'. exact N1.
    + eapply POSTM_trans; [exact PM1 | exact PM'].
    + eapply WKEEP_trans; [| exact WK']. subst M1. apply WKEEP_below; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia].
    + eapply POSTM_trans; [| exact PMA']. subst M1. apply (POSTM_stack_any C A' m' _ m _ _ (pp + 8) CK HW'); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
  - 
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF) as Rarr.
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
    destruct (PxdSegs.pxd_C1 al_rom regs m s pix cm v ltac:(lia) ltac:(lia) PX Ht Hc ltac:(lia) SOK ltac:(lia) H2 H8) as (r1 & RUN1 & Q2 & Q10 & Q1 & Q8 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    set (M1 := wbytes m _ _).
    assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1) by (subst M1; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    assert (CM1 : CMAPat M1 cm cv).
    { subst M1. apply (CMAPat_out m cm cv); [exact CM | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    apply (pixcmapDestroy_W C A M1 md r1 (s - 32) (s - 32) cm cv karr (Z_to_bv 64 0x6e010) S CK HW1 Q2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) Q1
             ltac:(red; apply bv_eq; reflexivity) Q4 ltac:(replace (s - 32)%Z with (s + (-32))%Z by lia; apply mod16_plus_mod8; [exact Hs16 | reflexivity]) Q10).
    { subst M1. rewrite <- (w2b_Z 8 cm) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
    { exact CM1. } { exact Lcm. } { exact Larr. } { exact L0cm. } { exact L0arr. } { exact NE1. }
    intros A1 m1 vm1 r2 HWa CSa La1 La2 LEQa PMa _ HRTa.
    replace (Z_to_bv 64 0x6e010) with (0x6e010 : word) by (apply bv_eq; reflexivity).
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (E8 : getr r2 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    assert (E9 : getr r2 9 = Z_to_bv 64 pp) by (csr; reflexivity).
    assert (E4 : getr r2 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z).
    { rewrite (LEQa _ (zneq_w pix cm ltac:(lia) ltac:(lia) (not_eq_sym NE2)) (zneq_w pix (c_arr cv) ltac:(lia) ltac:(lia) (not_eq_sym NE3))). exact Lp. }
    
    assert (SOKp1 : store_ok SEGS m1 (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso.
      exact (proj1 (proj2 (blk_byte C A1 m1 _ (Z_to_bv 64 pix) 64 x CK HWa Lp1 ltac:(rewrite u_Z2bv by lia; lia))) E). }
    pose proof (PxdSegs.pxd_C2 al_rom r2 m1 pix ltac:(lia) ltac:(lia) SOKp1 E8) as RUN2.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN2 |].
    set (M2 := wbytes m1 _ _).
    assert (PMm1 : POSTM C (c_A0 C) (pp + 8) m m1).
    { eapply POSTM_trans; [exact PM1|]. apply (POSTM_sub C (c_A0 C) A1); [exact (w_keep _ _ _ _ HWa) | eapply POSTM_mono; [|exact PMa]; lia]. }
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C (c_A0 C) (pp + 8) m M2).
    { subst M2. apply (WP_blk C (c_A0 C) A1 m m1 _ (Z_to_bv 64 pix) _ 64); [exact CK | split; [exact HWa | exact PMm1] | exact Lp1 | exact L0p | exact L0p | exact (w_keep _ _ _ _ HWa) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
    destruct WP2 as [HW2 PM2].
    apply (pixDestroy_wkeep_fin C A1 M2 _ r2 s pp pix ret s0v s1v S CK HW2 Hs16 ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi Hret E2 E8 E9 E4).
    { subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
    { subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
    { subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
    { exact Lp1. }
    { exact L0p. }
    intros A' m' vm' regs' HW' X2 X8 X9 XR L' LEQ' PM' WK' PMA' Rpp' RT'. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW'.
    apply (HK A' m' vm' regs' HW' X2 X8 X9); try assumption; try (solve [room_tac]).
    + intros r Hr. rewrite (XR r Hr). rewrite (cs_rest_of_kept _ _ CSa r Hr). apply AG1. cbn [In cs_rest] in Hr.
      repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
    + intros _. split; [| ]. 
      * rewrite (LEQ' _ (zneq_w cm pix ltac:(lia) ltac:(lia) NE2)). exact La1.
      * rewrite (LEQ' _ (zneq_w (c_arr cv) pix ltac:(lia) ltac:(lia) NE3)). exact La2.
    + intros q N1 N23. destruct (N23 ltac:(lia)) as [N2 N3]. rewrite (LEQ' q N1). apply LEQa; assumption.
    + eapply POSTM_trans; [exact PM2 | exact PM'].
    + eapply WKEEP_trans; [| exact WK']. eapply WKEEP_trans; [| subst M2; apply WKEEP_below; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia]].
      eapply WKEEP_trans; [| apply (WKEEP_FRM C s (s - 32 + 8) pp M1 m1 CK (proj1 PMa)); lia].
      subst M1. apply WKEEP_below; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia].
    + eapply POSTM_trans; [| exact PMA'].
      assert (SUBf : sub_live A' A1) by (intros q k Lq; rewrite <- (LEQ' q); [exact Lq|]; intros ->; rewrite Lq in L'; discriminate).
      eapply POSTM_trans; [| subst M2; apply (POSTM_blk C A' A1 m1 _ (Z_to_bv 64 pix) _ 64 _ (pp + 8) CK HWa Lp1 L' SUBf); [rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]].
      apply (POSTM_trans C A' (pp + 8) m M1 m1).
      * subst M1. apply (POSTM_stack_any C A' m' _ m _ _ (pp + 8) CK HW'); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
      * apply (POSTM_sub C A' A1); [| eapply POSTM_mono; [|exact PMa]; lia].
        intros q k Lq. rewrite <- (LEQ' q); [exact Lq|]. intros ->. rewrite Lq in L'. discriminate.
Qed.

Theorem pixDestroy_wkeep_W : forall C A m md regs (s pp pix cm karr R : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (p_data v = 0%Z \/ (live A (Z_to_bv 64 (p_data v)) = Some R /\ live (c_A0 C) (Z_to_bv 64 (p_data v)) = None /\ (0 < R)%Z /\
                      p_data v <> pix /\ (cm <> 0%Z -> p_data v <> cm /\ p_data v <> c_arr cv))) ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     O23LeptPixDestroy.pixd_post A A' pix (p_data v) cm (c_arr cv) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> WKEEP C s pp m m' -> POSTM C A' (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6df98 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix cm karr R v cv ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 ALpp H10 Rpp PX Hrc Ht Hc Lp L0p HD HCM HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ALLOC_STACK in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (SOKp : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix v x PX ltac:(lia) E). }
  destruct (PxdSegs.pxd_A al_rom regs m s pp pix v ret ltac:(lia) Hpp ltac:(lia) ALp ALpp (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia))
              SOKp Rpp PX Hrc ltac:(lia) Gp H2 H1 H10) as (r1 & RUN1 & Q2 & Q8 & Q9 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C (c_A0 C) (pp + 8) m M0) by (subst M0; wp_win CK).
  assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1).
  { subst M1. apply (WP_blk C (c_A0 C) A m M0 md (Z_to_bv 64 pix) _ 64); [exact CK | exact WP0 | exact Lp | exact L0p | exact L0p | exact (w_keep _ _ _ _ HW) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  destruct WP1 as [HW1 PM1].
  assert (PX1 : PIXat M1 pix (set_rc v 0)).
  { subst M1. apply PIX_wr_rc; [|lia]. subst M0.
    repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (R8 : rdn SEGS M1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (subst M1 M0; rdn_solve).
  assert (R16 : rdn SEGS M1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (subst M1 M0; rdn_solve).
  assert (R24 : rdn SEGS M1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (subst M1 M0; rdn_solve).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)).
  { destruct HCM as [X|(CM & X)]; [left; exact X | right; split; [|exact X]].
    pose proof CM as (Hc0 & Hc64 & _). destruct X as (Lcm & _ & _ & _ & _ & NE2 & _).
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
    pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lcm Lp (zneq_w cm pix ltac:(lia) ltac:(lia) NE2)) as D.
    rewrite !u_Z2bv in D by lia. unfold round16 in D. change ((24 + 15) / 16)%Z with 2%Z in D. change ((64 + 15) / 16)%Z with 4%Z in D.
    subst M1 M0. repeat (apply CMAPat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact CM. }
  
  assert (TAIL : forall A1 m1 vm1 r2, W C A1 m1 (with_vmmaps vm1 md) ->
            getr r2 2 = Z_to_bv 64 (s - 32) -> getr r2 8 = Z_to_bv 64 pix -> getr r2 9 = Z_to_bv 64 pp -> getr r2 4 = Z_to_bv 64 0x1381d0 ->
            (forall r, In r cs_rest -> getr r2 r = getr regs r) ->
            POSTM C A1 (s - 32) M1 m1 -> PIXat m1 pix (set_rc v 0) ->
            live A1 (Z_to_bv 64 pix) = Some 64%Z ->
            (cm <> 0%Z -> live A1 (Z_to_bv 64 cm) = live A (Z_to_bv 64 cm) /\ live A1 (Z_to_bv 64 (c_arr cv)) = live A (Z_to_bv 64 (c_arr cv))) ->
            (p_data v <> 0%Z -> live A1 (Z_to_bv 64 (p_data v)) = None) ->
            (forall q, (p_data v <> 0%Z -> q <> Z_to_bv 64 (p_data v)) -> live A1 q = live A q) ->
            (cm <> 0%Z -> CMAPat m1 cm cv) ->
            roomtr A (m_vmmaps md) A1 vm1 0 0 ->
            realizes SEGS (mkCfg (mkst r2 (0x6dff0 : word) m1 al_rom) (with_vmmaps vm1 md)) S).
  { intros A1 m1 vm1 r2 HWa E2 E8 E9 E4 ER PMa PXa Lp1 Lcm1 LD1 LEQa CMa RTa.
    apply (pixDestroy_wkeep_tail C A1 m1 _ r2 s pp pix cm karr (set_rc v 0) cv ret (getr regs 8) (getr regs 9) S CK HWa Hs16
             ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi Hret E2 E8 E9 E4).
    - rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). exact R8.
    - rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact R16.
    - rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact R24.
    - exact PXa.
    - cbn. exact Ht.
    - cbn. exact Hc.
    - exact Lp1.
    - exact L0p.
    - destruct HCM1 as [X|(CM & Lcm & Larr & X)]; [left; exact X | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A M1 md _ _ CK HW1 Lcm ltac:(lia)) as [G _]. rewrite u_Z2bv in G by lia.
      assert (NC : cm <> 0%Z) by lia.
      destruct (Lcm1 NC) as [E1 E2']. rewrite E1, E2'.
      split; [exact (CMa NC) | split; [exact Lcm | split; [exact Larr | exact X]]].
    - intros A' m' vm' regs' HW' X2 X8 X9 XR L' Lcm' LEQ' PM' WK' PMA' Rpp' RT'. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW'.
      assert (SUB1' : forall q k, live A' q = Some k -> live A1 q = Some k).
      { intros q k Lq. assert (Nq : q <> Z_to_bv 64 pix) by (intros ->; rewrite Lq in L'; discriminate).
        rewrite <- (LEQ' q Nq); [exact Lq|]. intros NC. destruct (Lcm' NC) as [N2 N3]. split; intros ->; [rewrite Lq in N2 | rewrite Lq in N3]; discriminate. }
      assert (SUB' : forall q k, live A' q = Some k -> live A q = Some k).
      { intros q k Lq. pose proof (SUB1' q k Lq) as Lq1. rewrite <- (LEQa q); [exact Lq1|]. intros ND ->. rewrite (LD1 ND) in Lq1. discriminate. }
      apply (HK A' m' vm' regs' HW').
      + apply cs_kept_of_rest; [rewrite X2, H2; reflexivity | exact X8 | exact X9 |].
        intros r Hr. rewrite (XR r Hr). exact (ER r Hr).
      + split; [exact L'|]. split; [|split].
        * intros ND. destruct HD as [X|(LR & LR0 & HR & NEdp & NEdc)]; [exfalso; exact (ND X)|].
          rewrite (LEQ' (Z_to_bv 64 (p_data v))); [exact (LD1 ND) | apply zneq_w; lia |].
          intros NC. destruct (NEdc NC) as [N2 N3].
          destruct HCM as [X|(CM & _ & _ & _ & _ & _)]; [exfalso; exact (NC X)|]. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF).
          split; apply zneq_w; lia.
        * intros NC. exact (Lcm' NC).
        * intros q N1 N2 N3. rewrite (LEQ' q N1 N3). apply LEQa. exact N2.
      + eapply POSTM_trans; [eapply POSTM_mono; [|exact PM1]; lia|].
        eapply POSTM_trans; [apply (POSTM_sub C (c_A0 C) A1); [exact (w_keep _ _ _ _ HWa) | eapply POSTM_mono; [|exact PMa]; lia] | exact PM'].
      + eapply WKEEP_trans; [| exact WK']. eapply WKEEP_trans; [| apply (WKEEP_FRM C s (s - 32) pp M1 m1 CK (proj1 PMa)); lia].
        subst M1 M0. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
        repeat (eapply WKEEP_trans; [| apply WKEEP_below; [rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia]]).
        intros a _ _; reflexivity.
      + eapply POSTM_trans; [| exact PMA']. eapply POSTM_trans; [| apply (POSTM_sub C A' A1 _ _ _ SUB1'); eapply POSTM_mono; [|exact PMa]; lia].
        apply (POSTM_trans C A' (pp + 8) m M0 M1).
        * subst M0. repeat (eapply POSTM_trans; [| apply (POSTM_stack_any C A' m' _ _ _ _ (pp + 8) CK HW'); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia]).
          apply POSTM_refl.
        * subst M1. split.
          -- intros x Hg1 _ _ _ _. apply wbytes_outside; [rewrite length_N_to_le_bytes, u_Z2bv by lia; lia|]. rewrite length_N_to_le_bytes, u_Z2bv by lia.
             destruct (Z_lt_ge_dec (u x) (pix + 20)); [left; lia|]. destruct (Z_lt_ge_dec (u x) (pix + 24)); [| right; cbn; lia].
             exfalso. apply Hg1. destruct (blk_byte C A M0 md (Z_to_bv 64 pix) 64 x CK (proj1 WP0) Lp ltac:(rewrite u_Z2bv by lia; lia)) as (G & _). exact G.
          -- apply (LIVK_freed_blk C A M0 md A' (Z_to_bv 64 pix) _ 64 _ CK (proj1 WP0) Lp SUB' L'); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia.
      + exact Rpp'.
      + room_tac. }
  assert (ER1 : forall r, In r cs_rest -> getr r1 r = getr regs r).
  { intros r Hr. apply AG1. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr. }
  destruct HD as [D0 | (LR & LR0 & HR & NEdp & NEdc)].
  - 
    rewrite D0 in Q10.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (PxdSegs.pxd_B0 al_rom r1 M1 Q10) |].
    rewrite <- (with_vmmaps_same md). rewrite <- (with_vmmaps_same md) in HW1.
    apply (TAIL A M1 (m_vmmaps md) r1 HW1 Q2 Q8 Q9 Q4 ER1).
    + apply POSTM_refl.
    + exact PX1.
    + exact Lp.
    + intros _. split; reflexivity.
    + intros ND. exfalso. exact (ND D0).
    + intros q _. reflexivity.
    + intros NC. destruct HCM1 as [X|(CM & _)]; [exfalso; exact (NC X) | exact CM].
    + room_tac.
  - 
    rename R into Rn.
    destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) Rn CK HW LR HR) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    destruct (PxdSegs.pxd_B1 al_rom r1 M1 (p_data v) ltac:(lia) ltac:(lia) (W_pmm_free C A M1 md HW1) Q10) as (r2 & RUN2 & P10 & P1 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    assert (P4 : getr r2 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    assert (P2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    replace (0x10e818 : word) with (Z_to_bv 64 0x10e818) by (apply bv_eq; reflexivity).
    apply (W_free16 C A M1 md r2 (Z_to_bv 64 (p_data v)) (Z_to_bv 64 0x6dff0) Rn (s - 32) S CK HW1 P10 LR LR0 P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r3 HWa CSa La LEQa PMa HRTa.
    replace (Z_to_bv 64 0x6dff0) with (0x6dff0 : word) by (apply bv_eq; reflexivity).
    assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
    assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (LEQa _ NEpd); exact Lp).
    apply (TAIL A1 m1 vm1 r3 HWa).
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + intros r Hr. rewrite (cs_rest_of_kept _ _ CSa r Hr). rewrite (AG2 r). exact (ER1 r Hr).
      cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
    + exact PMa.
    + apply (PIXat_frame M1); [exact PX1|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 pix) 64%Z (u x - pix)%Z Lp1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E.
    + exact Lp1.
    + intros NC. destruct (NEdc NC) as [N2 N3].
      destruct HCM as [X|(CM & _)]; [exfalso; exact (NC X)|]. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF).
      split; apply LEQa; apply zneq_w; lia.
    + intros _. exact La.
    + intros q Hq. apply LEQa. apply Hq. lia.
    + intros NC. destruct HCM1 as [X|(CM & Lcm & X)]; [exfalso; exact (NC X)|]. pose proof CM as (Hc0 & Hc64 & CWF & _).
      destruct (NEdc NC) as [N2 N3].
      assert (Lcm1 : live A1 (Z_to_bv 64 cm) = Some 24%Z) by (rewrite (LEQa _ (zneq_w cm (p_data v) ltac:(lia) ltac:(lia) (not_eq_sym N2))); exact Lcm).
      apply (CMAPat_frame M1); [exact CM|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 cm) 24%Z (u x - cm)%Z Lcm1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (cm + (u x - cm))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E.
    + room_tac.
Qed.

Theorem pixDestroy_keep_W : forall C A m md regs (s pp pix cm karr R : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  live A (Z_to_bv 64 (p_data v)) = Some R -> live (c_A0 C) (Z_to_bv 64 (p_data v)) = None -> (0 < R)%Z -> p_data v <> pix ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ p_data v <> cm /\ p_data v <> c_arr cv /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     O23LeptPixDestroy.pixd_post A A' pix (p_data v) cm (c_arr cv) ->
     POSTM C A' (pp + 8) m m' ->
     rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6df98 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix cm karr R v cv ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 ALp H10 Rpp PX Hrc Htx Hcm L0 L00 LD LD0 HR NEpd CMs HK.
  apply (pixDestroy_wkeep_W C A m md regs s pp pix cm karr R v cv ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 ALp H10 Rpp PX Hrc Htx Hcm L0 L00).
  - right. split; [exact LD|]. split; [exact LD0|]. split; [exact HR|]. split; [exact NEpd|].
    intros NZ. destruct CMs as [E|(_ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & _)]; [contradiction|]. split; assumption.
  - destruct CMs as [E|(X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _ & _ & X9)]; [left; exact E|].
    right. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj X8 X9)))))))).
  - intros A' m' vm' regs' HW' CS' PP' _ WK PM' R0 RT.
    apply (HK A' m' vm' regs' HW' CS' PP' PM' R0); [|exact RT].
    intros a Ha. apply WK; lia.
Qed.

End DestroyK.
