(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import LeptDefs.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Room.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure} {LL : LeptLayout}.
Context {PINS : LeptPins}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition roomtr (A : AS) (vm : VmMaps) (A' : AS) (vm' : VmMaps) (K B : Z) : Prop :=
  forall k b, aroom A vm k b -> K <= k -> B <= b -> aroom A' vm' (k - K) (b - B).

Lemma roomtr_refl : forall A vm K B, 0 <= K -> 0 <= B -> roomtr A vm A vm K B.
Proof.
  intros A vm K B HK HB k b Hr Hk Hb. apply (aroom_mono A vm k b); [exact Hr | lia | lia].
Qed.

Lemma roomtr_weaken : forall A vm A' vm' K B K' B',
  roomtr A vm A' vm' K B -> K <= K' -> B <= B' -> roomtr A vm A' vm' K' B'.
Proof.
  intros A vm A' vm' K B K' B' T HK HB k b Hr Hk Hb.
  apply (aroom_mono A' vm' (k - K) (b - B)); [apply T; [exact Hr | lia | lia] | lia | lia].
Qed.

Lemma roomtr_trans : forall A vm A1 vm1 A2 vm2 K1 B1 K2 B2,
  roomtr A vm A1 vm1 K1 B1 -> roomtr A1 vm1 A2 vm2 K2 B2 -> 0 <= K2 -> 0 <= B2 ->
  roomtr A vm A2 vm2 (K1 + K2) (B1 + B2).
Proof.
  intros A vm A1 vm1 A2 vm2 K1 B1 K2 B2 T1 T2 HK2 HB2 k b Hr Hk Hb.
  replace (k - (K1 + K2)) with (k - K1 - K2) by lia. replace (b - (B1 + B2)) with (b - B1 - B2) by lia.
  apply T2; [apply T1; [exact Hr | lia | lia] | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma roomtr_wv : forall A vm md A' vm' K B,
  roomtr A (m_vmmaps (with_vmmaps vm md)) A' vm' K B -> roomtr A vm A' vm' K B.
Proof. intros A vm md A' vm' K B T. rewrite with_vmmaps_vmmaps in T. exact T. Qed.

(* [comment removed for export] *)
Lemma roomtr_alloc : forall A vm A' vm' n B,
  roomtr A vm A' vm' 1 (alloc_margin n) -> n + 2 ^ 22 <= B -> roomtr A vm A' vm' 1 B.
Proof.
  intros A vm A' vm' n B T HB. apply (roomtr_weaken A vm A' vm' 1 (alloc_margin n)); [exact T | lia |].
  pose proof (alloc_margin_le n). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma W_calloc_l : forall C A m md regs (cnt sz : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
  0 <= cnt < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= cnt * sz < 2 ^ 61 ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + CALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
        \/ (u res <> 0 /\ live A res = None /\ live A' res = Some (cnt * sz) /\ live (c_A0 C) res = None /\
            (forall q, q <> res -> live A' q = live A q) /\
            (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) /\
            u res mod 16 = 0 /\ u res + round16 (cnt * sz) <= alloc_top (c_vm C)) ) ->
      POSTM C A s m m' ->
      roomtr A (m_vmmaps md) A' vm' 1 (alloc_margin (cnt * sz)) ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S.
Proof.
  intros C A m md regs cnt sz ret s S CK HW H10 H11 Hcnt Hsz Hprod H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_calloc_l fx A m md regs cnt sz ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 H11 Hcnt Hsz Hprod H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s (1024 + 32) CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' res Hinv' Hres Hcs Hout Hfr Hlive Hdef E1 E2 E3 E4 HRT.
    rewrite H2, u_Z2bv in Hfr by lia.
    assert (Hkeep' : (forall q k, live (c_A0 C) q = Some k -> live A' q = Some k) /\
                     (u res <> 0 -> live (c_A0 C) res = None)).
    { destruct Hout as [[-> EQ]|(R1 & R2 & R3 & R4 & R5 & R6)].
      - split; [exact (keep_same C A A' (w_keep _ _ _ _ HW) EQ) | intros X; exfalso; apply X; reflexivity].
      - destruct (keep_new C A A' res _ (w_keep _ _ _ _ HW) R2 R3 R4) as [X Y]. split; [exact X | intros _; exact Y]. }
    destruct Hkeep' as [Hkeep' Hres0].
    destruct (W_after_call C A m md A' m' vm' s (1024 + 32) CK HW ltac:(lia) ltac:(lia) Hhi
                Hinv' Hkeep' Hfr (fun q k i L Hi => Hlive q k i (w_keep _ _ _ _ HW q k L) Hi) Hdef E1 E2 E3 E4) as [HW' F].
    apply (HK A' m' vm' regs' res HW' Hres Hcs); [|split; [exact F|exact Hlive] | exact HRT].
    destruct Hout as [L|(R1 & R2 & R3 & R4 & R5 & R6)]; [left; exact L|right].
    destruct (ai_live_hull A' m' vm' res (cnt * sz) Hinv' R3) as (_ & AL16 & TOP & _).
    rewrite E2, V2 in TOP.
    repeat split; try assumption. exact (Hres0 R1).
Qed.

Lemma W_malloc_l : forall C A m md regs (n : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 61 ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
        \/ (u res <> 0 /\ live A res = None /\ live A' res = Some n /\ live (c_A0 C) res = None /\
            (forall q, q <> res -> live A' q = live A q) /\
            u res mod 16 = 0 /\ u res + round16 n <= alloc_top (c_vm C)) ) ->
      POSTM C A s m m' ->
      roomtr A (m_vmmaps md) A' vm' 1 (alloc_margin n) ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S.
Proof.
  intros C A m md regs n ret s S CK HW H10 Hn H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_malloc_l fx A m md regs n ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 Hn H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s 1024 CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' res Hinv' Hres Hcs Hout Hfr Hlive Hdef E1 E2 E3 E4 HRT.
    rewrite H2, u_Z2bv in Hfr by lia.
    assert (Hkeep' : (forall q k, live (c_A0 C) q = Some k -> live A' q = Some k) /\
                     (u res <> 0 -> live (c_A0 C) res = None)).
    { destruct Hout as [[-> EQ]|(R1 & R2 & R3 & R4 & R5)].
      - split; [exact (keep_same C A A' (w_keep _ _ _ _ HW) EQ) | intros X; exfalso; apply X; reflexivity].
      - destruct (keep_new C A A' res _ (w_keep _ _ _ _ HW) R2 R3 R4) as [X Y]. split; [exact X | intros _; exact Y]. }
    destruct Hkeep' as [Hkeep' Hres0].
    destruct (W_after_call C A m md A' m' vm' s 1024 CK HW ltac:(lia) ltac:(lia) Hhi
                Hinv' Hkeep' Hfr (fun q k i L Hi => Hlive q k i (w_keep _ _ _ _ HW q k L) Hi) Hdef E1 E2 E3 E4) as [HW' F].
    apply (HK A' m' vm' regs' res HW' Hres Hcs); [|split; [exact F|exact Hlive] | exact HRT].
    destruct Hout as [L|(R1 & R2 & R3 & R4 & R5)]; [left; exact L|right].
    destruct (ai_live_hull A' m' vm' res n Hinv' R3) as (_ & AL16 & TOP & _).
    rewrite E2, V2 in TOP.
    repeat split; try assumption. exact (Hres0 R1).
Qed.

Lemma W_free_l : forall C A m md regs (p ret : word) (n s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = p -> live A p = Some n -> live (c_A0 C) p = None ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs',
      W C A' m' (with_vmmaps vm' md) ->
      (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      live A' p = None -> (forall q, q <> p -> live A' q = live A q) ->
      POSTM C A' s m m' ->
      roomtr A (m_vmmaps md) A' vm' 0 0 ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_free_pc m al_rom) md) S.
Proof.
  intros C A m md regs p ret n s S CK HW H10 Lp Lp0 H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_free_l fx A m md regs p ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 (or_intror (ex_intro _ n Lp)) H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s 1024 CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' Hinv' Hcs Lp' EQ Hfr Hlive Hdef E1 E2 E3 E4 _ HRT.
    rewrite H2, u_Z2bv in Hfr by lia.
    pose proof (keep_free C A A' p n (w_keep _ _ _ _ HW) Lp Lp0 Lp' EQ) as Hkeep'.
    assert (Hdef' : forall a, m a <> None -> u a < al_image_hi \/ owned A a \/ m' a <> None).
    { intros a Ha. destruct (Hdef a Ha) as [X|X]; [right; left; exact X | right; right; exact X]. }
    destruct (W_after_call C A m md A' m' vm' s 1024 CK HW ltac:(lia) ltac:(lia) Hhi Hinv' Hkeep' Hfr
                (fun q k i L Hi => Hlive q k i (Hkeep' q k L) Hi) Hdef' E1 E2 E3 E4) as [HW' F].
    apply (HK A' m' vm' regs' HW' Hcs Lp' EQ (conj F Hlive)).
    intros k b Hr _ _. rewrite !Z.sub_0_r. exact (HRT k b Hr).
Qed.

(* [comment removed for export] *)
Lemma W_free0_l : forall C A m md regs (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md -> live (c_A0 C) (Z_to_bv 64 0) = None ->
  getr regs 10 = Z_to_bv 64 0 ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs',
      W C A' m' (with_vmmaps vm' md) ->
      (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      live A' (Z_to_bv 64 0) = None -> (forall q, q <> Z_to_bv 64 0 -> live A' q = live A q) ->
      POSTM C A s m m' ->
      roomtr A (m_vmmaps md) A' vm' 0 0 ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_free_pc m al_rom) md) S.
Proof.
  intros C A m md regs ret s S CK HW Z0 H10 H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_free_l fx A m md regs (Z_to_bv 64 0) ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 (or_introl eq_refl) H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s 1024 CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' Hinv' Hcs Lp' EQ Hfr Hlive Hdef E1 E2 E3 E4 _ HRT.
    rewrite H2, u_Z2bv in Hfr by lia.
    assert (Hkeep' : forall q k, live (c_A0 C) q = Some k -> live A' q = Some k).
    { intros q k L. destruct (bv_eq_dec _ q (Z_to_bv 64 0)) as [->|NE]; [congruence|].
      rewrite (EQ q NE). exact (w_keep _ _ _ _ HW q k L). }
    assert (Hdef' : forall a, m a <> None -> u a < al_image_hi \/ owned A a \/ m' a <> None).
    { intros a Ha. destruct (Hdef a Ha) as [X|X]; [right; left; exact X | right; right; exact X]. }
    assert (Hlive2 : forall q k i, live (c_A0 C) q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)).
    { intros q k i L Hi. exact (Hlive q k i (Hkeep' q k L) Hi). }
    destruct (W_after_call C A m md A' m' vm' s 1024 CK HW ltac:(lia) ltac:(lia) Hhi Hinv' Hkeep' Hfr Hlive2 Hdef' E1 E2 E3 E4) as [HW' F].
    apply (HK A' m' vm' regs' HW' Hcs Lp' EQ).
    + split; [exact F|].
      intros q k i L Hi. destruct (bv_eq_dec _ q (Z_to_bv 64 0)) as [->|NE].
      * (* [comment removed for export] *)
        exfalso. destruct (Z_lt_ge_dec 0 k) as [Hk|Hk]; [| lia].
        pose proof (blk_range C A m md (Z_to_bv 64 0) k CK HW L Hk) as [B _]. rewrite u_Z2bv in B by lia. lia.
      * exact (Hlive q k i ltac:(rewrite (EQ q NE); exact L) Hi).
    + intros k b Hr _ _. rewrite !Z.sub_0_r. exact (HRT k b Hr).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma W_calloc_sure : forall C A m md regs (cnt sz k b : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
  0 <= cnt < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= cnt * sz < 2 ^ 61 ->
  aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin (cnt * sz) <= b -> cnt * sz <= ROOM_NMAX ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + CALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      u res <> 0 -> live A res = None -> live A' res = Some (cnt * sz) -> live (c_A0 C) res = None ->
      (forall q, q <> res -> live A' q = live A q) ->
      (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) ->
      u res mod 16 = 0 -> u res + round16 (cnt * sz) <= alloc_top (c_vm C) ->
      POSTM C A s m m' ->
      aroom A' vm' (k - 1) (b - alloc_margin (cnt * sz)) ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S.
Proof.
  intros C A m md regs cnt sz k b ret s S CK HW H10 H11 Hcnt Hsz Hprod Hroom Hk Hb Hmax H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_calloc_sure fx A m md regs cnt sz k b ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 H11 Hcnt Hsz Hprod Hroom Hk Hb Hmax H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s (1024 + 32) CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' res Hinv' Hres Hcs R1 R2 R3 R4 Rnew R6 Hfr Hlive Hdef E1 E2 E3 E4 Hroom'.
    rewrite H2, u_Z2bv in Hfr by lia.
    destruct (keep_new C A A' res _ (w_keep _ _ _ _ HW) R2 R3 R4) as [Hkeep' Hres0].
    destruct (W_after_call C A m md A' m' vm' s (1024 + 32) CK HW ltac:(lia) ltac:(lia) Hhi
                Hinv' Hkeep' Hfr (fun q k0 i L Hi => Hlive q k0 i (w_keep _ _ _ _ HW q k0 L) Hi) Hdef E1 E2 E3 E4) as [HW' F].
    destruct (ai_live_hull A' m' vm' res (cnt * sz) Hinv' R3) as (_ & AL16 & TOP & _).
    rewrite E2, V2 in TOP.
    exact (HK A' m' vm' regs' res HW' Hres Hcs R1 R2 R3 Hres0 R4 R6 AL16 TOP (conj F Hlive) Hroom').
Qed.

Lemma W_malloc_sure : forall C A m md regs (n k b : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 61 ->
  aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin n <= b -> n <= ROOM_NMAX ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = al_gp ->
  getr regs 2 = Z_to_bv 64 s -> s mod 16 = 0 -> c_top C - LSTK + ALLOC_STACK <= s -> s <= c_top C ->
  (forall A' m' vm' regs' (res : word),
      W C A' m' (with_vmmaps vm' md) ->
      getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
      u res <> 0 -> live A res = None -> live A' res = Some n -> live (c_A0 C) res = None ->
      (forall q, q <> res -> live A' q = live A q) ->
      u res mod 16 = 0 -> u res + round16 n <= alloc_top (c_vm C) ->
      POSTM C A s m m' ->
      aroom A' vm' (k - 1) (b - alloc_margin n) ->
      realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S.
Proof.
  intros C A m md regs n k b ret s S CK HW H10 Hn Hroom Hk Hb Hmax H1 Hret H4 H2 Hs16 Hlo Hhi HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. destruct (w_vm _ _ _ _ HW) as (V1 & V2 & V3 & V4).
  unfold CALLOC_STACK, ALLOC_STACK in *.
  assert (Hs : 0 <= s < 2 ^ 64) by lia.
  eapply (ai_malloc_sure fx A m md regs n k b ret (c_sp0 C) (c_argv C) (c_envp C) S
            (w_inv _ _ _ _ HW) (w_pure _ _ _ _ HW) (w_env _ _ _ _ HW) H10 Hn Hroom Hk Hb Hmax H1 (pin_ret _ Hret) H4).
  - rewrite H2, u_Z2bv by lia. exact Hs16.
  - rewrite H2, u_Z2bv by lia. rewrite V2. lia.
  - rewrite H2, u_Z2bv by lia. lia.
  - rewrite H2. intros a Ha. rewrite u_Z2bv in Ha by lia. exact (W_call_win C A m md s 1024 CK HW ltac:(lia) Hhi a Ha).
  - intros A' m' vm' regs' res Hinv' Hres Hcs R1 R2 R3 R4 Rnew Hfr Hlive Hdef E1 E2 E3 E4 Hroom'.
    rewrite H2, u_Z2bv in Hfr by lia.
    destruct (keep_new C A A' res _ (w_keep _ _ _ _ HW) R2 R3 R4) as [Hkeep' Hres0].
    destruct (W_after_call C A m md A' m' vm' s 1024 CK HW ltac:(lia) ltac:(lia) Hhi
                Hinv' Hkeep' Hfr (fun q k0 i L Hi => Hlive q k0 i (w_keep _ _ _ _ HW q k0 L) Hi) Hdef E1 E2 E3 E4) as [HW' F].
    destruct (ai_live_hull A' m' vm' res n Hinv' R3) as (_ & AL16 & TOP & _).
    rewrite E2, V2 in TOP.
    exact (HK A' m' vm' regs' res HW' Hres Hcs R1 R2 R3 Hres0 R4 AL16 TOP (conj F Hlive) Hroom').
Qed.

End Room.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RK_hdr : Z := 1.      Definition RB_hdr : Z := 2 ^ 23.      (* [comment removed for export] *)
Definition RK_cmap : Z := 2.     Definition RB_cmap : Z := 2 ^ 24.     (* [comment removed for export] *)
Definition RK_pix : Z := 2.      Definition RB_pix : Z := 2 ^ 27.      (* [comment removed for export] *)
Definition RK_deser : Z := 5.    Definition RB_deser : Z := 2 ^ 28.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac room_norm :=
  repeat match goal with
         | H : context [m_vmmaps (with_vmmaps _ _)] |- _ =>
             lazymatch type of H with roomtr _ _ _ _ _ _ => rewrite !with_vmmaps_vmmaps in H | aroom _ _ _ _ => rewrite !with_vmmaps_vmmaps in H end
         end;
  rewrite ?with_vmmaps_vmmaps.
Ltac room_margins :=
  repeat match goal with
         | H : roomtr _ _ _ _ _ (alloc_margin ?n) |- _ =>
             lazymatch goal with
             | _ : alloc_margin n <= n + 2 ^ 22 |- _ => fail
             | _ => pose proof (alloc_margin_le n)
             end
         end.
Ltac room_consts := unfold RK_hdr, RB_hdr, RK_cmap, RB_cmap, RK_pix, RB_pix, RK_deser, RB_deser in *.
Ltac room_fwd :=
  repeat match goal with
         | H : roomtr ?X ?vx ?Y ?vy ?K1 ?B1, Hr : aroom ?X ?vx ?k ?b |- _ =>
             (* [comment removed for export] *)
             tryif (constr_eq X Y; constr_eq vx vy) then fail else
             (let Hn := fresh "Hroom" in
              assert (Hn : aroom Y vy (k - K1) (b - B1)) by (apply H; [exact Hr | lia | lia]);
              clear Hr H)
         end.
Ltac room_end :=
  lazymatch goal with
  | |- aroom ?Y ?vy ?k' ?b' =>
      match goal with
      | Hr : aroom Y vy ?k ?b |- _ => apply (aroom_mono Y vy k b k' b' Hr); lia
      end
  end.
(* [comment removed for export] *)
Ltac room_clear :=
  repeat match goal with
         | H : ?T |- _ =>
             lazymatch T with
             | roomtr _ _ _ _ _ _ => fail
             | aroom _ _ _ _ => fail
             | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail
             | @eq Z _ _ => fail
             | _ /\ _ => fail | _ \/ _ => fail
             | _ => clear H
             end
         end.
Ltac room_tac :=
  room_clear; room_norm; room_margins; room_consts;
  lazymatch goal with
  | |- roomtr _ _ _ _ _ _ => let k := fresh "k" in let b := fresh "b" in let Hr := fresh "Hroom" in
                             let Hk := fresh "Hk" in let Hb := fresh "Hb" in intros k b Hr Hk Hb
  | |- aroom _ _ _ _ => idtac
  end;
  room_fwd; room_end.
