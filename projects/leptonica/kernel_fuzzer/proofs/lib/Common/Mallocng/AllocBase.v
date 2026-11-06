(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg AllocIface PureModel.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section WithLayout.
Context {AL : AllocLayout}.

(* [comment removed for export] *)
Definition grantable (vm : VmMaps) (a : word) : Prop :=
  al_grantable a /\ bv_unsigned a < alloc_top vm.

(* [comment removed for export] *)
Record init_ledger (h : VmMaps) : Prop := {
  il_maps : vm_maps h = [];
  il_noaccess : vm_noaccess h = [];
  il_reserved : vm_reserved h = segments_reserved al_segs;
  il_start_brk : vm_start_brk h = vm_brk h;
  il_brk : valid_brk al_segs (vm_brk h);
  il_sp : valid_sp (vm_init_sp h)
}.

Class AllocBase := {
  AS : Type;
  ainv  : AS -> (word -> option byte) -> VmMaps -> Prop;
  live  : AS -> word -> option Z;
  owned : AS -> word -> Prop;

  ai_globals_owned : forall A a, al_globals a -> owned A a;
  ai_live_hull : forall A m vm p n, ainv A m vm -> live A p = Some n ->
      0 <= n /\ bv_unsigned p mod 16 = 0 /\
      bv_unsigned p + round16 n <= alloc_top vm /\
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
      al_globals a \/ (grantable vm a /\ m a <> None);
  ai_frame : forall A m m' vm, ainv A m vm ->
      (forall a, owned A a ->
                 (forall p n, live A p = Some n ->
                              ~ (bv_unsigned p <= bv_unsigned a < bv_unsigned p + n)) ->
                 m' a = m a) ->
      (forall a, owned A a -> m a <> None -> m' a <> None) ->
      (forall a, grantable vm a -> m' a <> None -> m a <> None) ->
      ainv A m' vm;

  A0 : AS;
  ai_init_live  : forall p, live A0 p = None;
  ai_init_owned : forall a, owned A0 a <-> al_globals a;
  ai_init : forall m h0,
      init_ledger h0 ->
      (forall a, al_globals a -> m a = None) ->
      (forall a, grantable h0 a -> m a = None) ->
      ainv A0 m h0;


  ai_malloc : forall (fx : FPState) A m md regs (n : Z) (ret sp0 : word) argv envp (S : TSet),
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
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_malloc_pc m al_rom) md) S;

  ai_free : forall (fx : FPState) A m md regs (p ret sp0 : word) argv envp (S : TSet),
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
          realizes al_segs (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
      realizes al_segs (mkCfg (mkst regs al_free_pc m al_rom) md) S
}.


End WithLayout.
