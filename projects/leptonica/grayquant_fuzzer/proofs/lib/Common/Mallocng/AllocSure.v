(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg AllocIface PureModel AsanCeil VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_margin (n : Z) : Z :=
  if n <=? 2028 then Z.min (2^17) (n + 2^22) else Z.min (n + 2^20 + 2^16) (52 * n + 2^16 + 2^12).

Lemma alloc_margin_le : forall n, alloc_margin n <= n + 2^22.
Proof. intros n. unfold alloc_margin. destruct (n <=? 2028); lia. Qed.
Lemma alloc_margin_ge : forall n, 0 <= n -> n <= alloc_margin n.
Proof. intros n Hn. unfold alloc_margin. destruct (Z.leb_spec n 2028); lia. Qed.
Lemma alloc_margin_mono : forall n n', n <= n' -> alloc_margin n <= alloc_margin n'.
Proof. intros n n' H. unfold alloc_margin. destruct (Z.leb_spec n 2028); destruct (Z.leb_spec n' 2028); lia. Qed.
(* [comment removed for export] *)
Lemma alloc_margin_small : forall n, 0 <= n <= 2028 -> alloc_margin n = 2^17.
Proof. intros n Hn. unfold alloc_margin. destruct (Z.leb_spec n 2028); lia. Qed.
Lemma alloc_margin_mid : forall n, 0 <= n -> alloc_margin n <= 52 * n + 2^17.
Proof. intros n Hn. unfold alloc_margin. destruct (Z.leb_spec n 2028); lia. Qed.
Lemma alloc_margin_big : forall n, 0 <= n -> alloc_margin n <= n + 2^20 + 2^16.
Proof. intros n Hn. unfold alloc_margin. destruct (Z.leb_spec n 2028); lia. Qed.

(* [comment removed for export] *)
Definition ROOM_BCAP : Z := 2^33.
Definition ROOM_KMAX : Z := 420000.
Definition ROOM_NMAX : Z := 2^28.

(* [comment removed for export] *)
#[export] Existing Instance aic_base.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLayout.
Context {AL : AllocLayout} {CL : CallocLayout}.

Class AllocSure := {
  asr_calloc :: AllocCalloc;

  (* [comment removed for export] *)
  aroom : AS -> VmMaps -> Z -> Z -> Prop;
  aroom_mono : forall A h k b k' b',
      aroom A h k b -> 0 <= k' <= k -> 0 <= b' <= b -> aroom A h k' b';
  aroom_nonneg : forall A h k b, aroom A h k b -> 0 <= k /\ 0 <= b;
  aroom_init : forall h0 k b,
      init_ledger h0 -> ROOM_BCAP <= vm_limit h0 ->
      0 <= k <= ROOM_KMAX -> 0 <= b <= ROOM_BCAP ->
      aroom A0 h0 k b;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ai_malloc_l : forall (fx : FPState) A m md regs (n : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2^61 ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
            \/ (bv_unsigned res <> 0 /\ live A res = None /\ live A' res = Some n /\
                (forall q, q <> res -> live A' q = live A q) /\
                (forall i, 0 <= i < round16 n -> owned A (at_ res i) \/ m (at_ res i) = None)) ) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          (* [comment removed for export] *)
          (forall k b, aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin n <= b ->
                       aroom A' vm' (k - 1) (b - alloc_margin n)) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S;

  ai_free_l : forall (fx : FPState) A m md regs (p ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = p -> (p = Z_to_bv 64 0 \/ exists n, live A p = Some n) ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs',
          ainv A' m' vm' ->
          (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          live A' p = None -> (forall q, q <> p -> live A' q = live A q) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A' q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          vm_live_bytes vm' <= vm_live_bytes (m_vmmaps md) ->
          (* [comment removed for export] *)
          (forall k b, aroom A (m_vmmaps md) k b -> aroom A' vm' k b) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_free_pc m al_rom) md) S;

  ai_calloc_l : forall (fx : FPState) A m md regs (cnt sz : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
      0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q))
            \/ (bv_unsigned res <> 0 /\ live A res = None /\ live A' res = Some (cnt * sz) /\
                (forall q, q <> res -> live A' q = live A q) /\
                (forall i, 0 <= i < round16 (cnt * sz) -> owned A (at_ res i) \/ m (at_ res i) = None) /\
                (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0))) ) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          (* [comment removed for export] *)
          (forall k b, aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin (cnt * sz) <= b ->
                       aroom A' vm' (k - 1) (b - alloc_margin (cnt * sz))) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ai_malloc_sure : forall (fx : FPState) A m md regs (n k b : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2^61 ->
      (* [comment removed for export] *)
      aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin n <= b -> n <= ROOM_NMAX ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          bv_unsigned res <> 0 -> live A res = None -> live A' res = Some n ->
          (forall q, q <> res -> live A' q = live A q) ->
          (forall i, 0 <= i < round16 n -> owned A (at_ res i) \/ m (at_ res i) = None) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k' i, live A q = Some k' -> 0 <= i < k' -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          aroom A' vm' (k - 1) (b - alloc_margin n) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S;

  ai_calloc_sure : forall (fx : FPState) A m md regs (cnt sz k b : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> md_pure md ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
      0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 ->
      (* [comment removed for export] *)
      aroom A (m_vmmaps md) k b -> 1 <= k -> alloc_margin (cnt * sz) <= b -> cnt * sz <= ROOM_NMAX ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      alloc_top (m_vmmaps md) + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          bv_unsigned res <> 0 -> live A res = None -> live A' res = Some (cnt * sz) ->
          (forall q, q <> res -> live A' q = live A q) ->
          (forall i, 0 <= i < round16 (cnt * sz) -> owned A (at_ res i) \/ m (at_ res i) = None) ->
          (forall i, 0 <= i < cnt * sz -> m' (at_ res i) = Some (Z_to_bv 8 0)) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - CALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k' i, live A q = Some k' -> 0 <= i < k' -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) -> alloc_top vm' = alloc_top (m_vmmaps md) ->
          vm_init_sp vm' = vm_init_sp (m_vmmaps md) -> vm_reserved vm' = vm_reserved (m_vmmaps md) ->
          aroom A' vm' (k - 1) (b - alloc_margin (cnt * sz)) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_calloc_pc m al_rom) md) S
}.

End WithLayout.
