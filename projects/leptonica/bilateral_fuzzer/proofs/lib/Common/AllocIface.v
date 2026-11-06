(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition round16 (n : Z) : Z := 16 * ((n + 15) / 16).

(* [comment removed for export] *)
Definition callee_saved (r : reg) : Prop :=
  r = 2%bv \/ r = 3%bv \/ r = 4%bv \/ r = 8%bv \/ r = 9%bv \/
  (18 <= bv_unsigned r <= 27).

(* [comment removed for export] *)
Definition ALLOC_STACK : Z := 1024.

(* [comment removed for export] *)
Class AllocLayout := {
  al_segs : list Segment;                 (* [comment removed for export] *)
  al_rom : word -> option byte;           (* [comment removed for export] *)
  al_malloc_pc : word;                    (* [comment removed for export] *)
  al_free_pc : word;                      (* [comment removed for export] *)
  al_gp : word;                           (* [comment removed for export] *)
  al_globals : word -> Prop;              (* [comment removed for export] *)
  al_errno_slot : word -> Prop;           (* [comment removed for export] *)
  al_grantable : word -> Prop;            (* [comment removed for export] *)
  al_ceiling : Z;                         (* [comment removed for export] *)
  al_image_hi : Z;                        (* [comment removed for export] *)
  al_in_ro : word -> Prop;                (* [comment removed for export] *)
  al_in_rw : word -> Prop;                (* [comment removed for export] *)
  al_ret_ok : word -> Prop;               (* [comment removed for export] *)
  (* [comment removed for export] *)
  al_env : word -> list (list byte) -> list (list byte) ->
           (word -> option byte) -> Prop;
  (* [comment removed for export] *)
  al_init_vm : word -> VmMaps;
  (* [comment removed for export] *)
  al_mmap_threshold : Z
}.

Section WithLayout.
Context {AL : AllocLayout}.

Class AllocIface := {
  AS : Type;
  ainv  : AS -> (word -> option byte) -> VmMaps -> Prop;
  live  : AS -> word -> option Z;
  owned : AS -> word -> Prop;

  ai_globals_owned : forall A a, al_globals a -> owned A a;
  ai_live_hull : forall A m vm p n, ainv A m vm -> live A p = Some n ->
      0 <= n /\ bv_unsigned p mod 16 = 0 /\
      bv_unsigned p + round16 n <= al_ceiling /\
      forall i, 0 <= i < round16 n ->
        owned A (at_ p i) /\ m (at_ p i) <> None /\
        ~ al_in_ro (at_ p i) /\ ~ al_in_rw (at_ p i);
  ai_live_disjoint : forall A m vm p n q k, ainv A m vm ->
      live A p = Some n -> live A q = Some k -> p <> q ->
      bv_unsigned p + round16 n <= bv_unsigned q \/
      bv_unsigned q + round16 k <= bv_unsigned p;
  ai_live_not_globals : forall A m vm p n i, ainv A m vm -> live A p = Some n ->
      0 <= i < round16 n -> ~ al_globals (at_ p i);
  ai_owned_where : forall A m vm a, ainv A m vm -> owned A a ->
      al_globals a \/ (al_grantable a /\ m a <> None);
  ai_frame : forall A m m' vm, ainv A m vm ->
      (forall a, owned A a ->
                 (forall p n, live A p = Some n ->
                              ~ (bv_unsigned p <= bv_unsigned a < bv_unsigned p + n)) ->
                 m' a = m a) ->
      (forall a, owned A a -> m a <> None -> m' a <> None) ->
      (forall a, al_grantable a -> m' a <> None -> m a <> None) ->
      ainv A m' vm;

  A0 : AS;
  ai_init_live  : forall p, live A0 p = None;
  ai_init_owned : forall a, owned A0 a <-> al_globals a;
  ai_init : forall m brk,
      (forall a, al_globals a -> m a = None) ->
      (forall a, al_grantable a -> m a = None) ->
      valid_brk al_segs brk ->
      ainv A0 m (al_init_vm brk);

  (* [comment removed for export] *)
  fresh_small : AS -> Z -> Prop;
  ai_init_fresh : fresh_small A0 0;
  ai_fresh_mono : forall A k k', fresh_small A k -> k <= k' -> fresh_small A k';

  ai_malloc : forall (fx : FPState) A m md regs (n : Z) (ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> m_halted md = None ->
      al_env sp0 argv envp m ->
      getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2^63 ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      al_ceiling + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          ( (res = Z_to_bv 64 0 /\ (forall q, live A' q = live A q) /\
             (forall k, fresh_small A k -> k <= 80 -> fresh_small A' k))
            \/ (bv_unsigned res <> 0 /\ live A res = None /\ live A' res = Some n /\
                (forall q, q <> res -> live A' q = live A q) /\
                (forall i, 0 <= i < round16 n -> owned A (at_ res i) \/ m (at_ res i) = None)) ) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S;

  ai_malloc_strong : forall (fx : FPState) A m md regs (n k : Z) (ret sp0 : word) argv envp (Snull Sok : TSet),
      ainv A m (m_vmmaps md) -> m_halted md = None ->
      al_env sp0 argv envp m ->
      fresh_small A k -> k <= 80 ->
      getr regs 10 = Z_to_bv 64 n -> 0 < n < 2^40 ->
      vm_live_bytes (m_vmmaps md) + n + 2^24 <= vm_limit (m_vmmaps md) ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      al_ceiling + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs',
          ainv A' m' vm' ->
          getr regs' 10 = Z_to_bv 64 0 -> (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          (forall q, live A' q = live A q) -> fresh_small A' k ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k' i, live A q = Some k' -> 0 <= i < k' -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) ->
          vm_live_bytes vm' <= vm_live_bytes (m_vmmaps md) + n + 2^23 ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) Snull) ->
      (forall A' m' vm' regs' (res : word),
          ainv A' m' vm' ->
          getr regs' 10 = res -> bv_unsigned res <> 0 ->
          (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          live A res = None -> live A' res = Some n ->
          (forall q, q <> res -> live A' q = live A q) ->
          ((al_mmap_threshold <= n \/ (n = 65536 /\ forall q, live A q = None)) ->
             fresh_small A' (k + 1)) ->
          (forall i, 0 <= i < round16 n -> owned A (at_ res i) \/ m (at_ res i) = None) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k' i, live A q = Some k' -> 0 <= i < k' -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> bv_unsigned a < al_image_hi \/ owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) ->
          vm_live_bytes vm' <= vm_live_bytes (m_vmmaps md) + n + 2^23 ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) Sok) ->
      realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) (t_alt2 Snull Sok);

  ai_free : forall (fx : FPState) A m md regs (p ret sp0 : word) argv envp (S : TSet),
      ainv A m (m_vmmaps md) -> m_halted md = None ->
      al_env sp0 argv envp m ->
      getr regs 10 = p -> (p = Z_to_bv 64 0 \/ exists n, live A p = Some n) ->
      getr regs 1 = ret -> al_ret_ok ret -> getr regs 4 = al_gp ->
      bv_unsigned (getr regs 2) mod 16 = 0 ->
      al_ceiling + 8192 <= bv_unsigned (getr regs 2) ->
      bv_unsigned (getr regs 2) <= bv_unsigned sp0 ->
      (forall a : word, bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2) ->
                        m a <> None /\ ~ owned A a /\ ~ al_in_ro a /\ ~ al_in_rw a) ->
      (forall A' m' vm' regs',
          ainv A' m' vm' ->
          (forall r, callee_saved r -> getr regs' r = getr regs r) ->
          live A' p = None -> (forall q, q <> p -> live A' q = live A q) ->
          ((forall n, live A p = Some n -> al_mmap_threshold <= n \/ n = 65536) ->
             forall k, fresh_small A k -> fresh_small A' k) ->
          (forall a, ~ owned A a -> ~ owned A' a -> ~ al_errno_slot a ->
                     ~ (bv_unsigned (getr regs 2) - ALLOC_STACK <= bv_unsigned a < bv_unsigned (getr regs 2)) ->
                     m' a = m a) ->
          (forall q k i, live A' q = Some k -> 0 <= i < k -> m' (at_ q i) = m (at_ q i)) ->
          (forall a, m a <> None -> owned A a \/ m' a <> None) ->
          vm_limit vm' = vm_limit (m_vmmaps md) ->
          vm_live_bytes vm' <= vm_live_bytes (m_vmmaps md) ->
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_free_pc m al_rom) md) S
}.

End WithLayout.
