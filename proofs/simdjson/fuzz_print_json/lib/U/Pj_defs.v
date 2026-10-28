(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition PJ_APPEND_ELEM : Z := 0x3db5c.
Definition PJ_APPEND_ARR : Z := 0x3eef4.
Definition PJ_APPEND_OBJ : Z := 0x3f1e4.
Definition PJ_GROW : Z := 0x40014.
Definition PJ_OSPUT : Z := 0x4009c.
Definition PJ_PADOUT : Z := 0x402b0.
Definition PJ_TOCHARS : Z := 0x4056c.
Definition PJ_SF : Z := 0x5b228.
Definition PJ_XSPUTN : Z := 0x825f8.
Definition PJ_OVERFLOW : Z := 0x3d9b0.
Definition PJ_OPNEW : Z := 0xd4db0.
Definition PJ_OPNEW_ARR : Z := 0xd4e20.

Definition PJ_GROW_STACK : Z := 48 + 16 + RMALLOC_STACK.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Record sbst : Type := mkSb { sb_buf : Z; sb_size : Z; sb_cap : Z; sb_blk : option bptr; sb_fuel : nat }.

Definition sb_k (st : sbst) : Z := Z.of_nat PJ_FUEL - Z.of_nat (sb_fuel st).

Definition sb_ch (st : sbst) : @chst bptr := (sb_fuel st, sb_cap st, sb_blk st).

Definition sbblocks (st : sbst) : list block :=
  match sb_blk st with Some b => [(b, sb_buf st, sb_cap st)] | None => [] end.

Definition SBINV (m : mem) (SB len : Z) (st : sbst) : Prop :=
  rw_cells usegs m (SB + 64) [C8 (Z_to_bv 64 (sb_buf st)); C8 (Z_to_bv 64 (sb_size st)); C8 (Z_to_bv 64 (sb_cap st))]
  /\ 0 <= sb_size st <= sb_cap st
  /\ (exists bs, rw_cells usegs m (sb_buf st) [CB (Z.to_nat (sb_cap st)) bs])
  /\ (exists ji, rw_cells usegs m SB [CB 64 ji])
  /\ (sb_fuel st <= PJ_FUEL)%nat
  /\ 64 * 2 ^ (sb_k st) <= sb_cap st <= PJ_CAPMAX len
  /\ match sb_blk st with
     | None => sb_buf st = SB /\ sb_cap st = 64 /\ sb_fuel st = PJ_FUEL
     | Some _ => rblock_range (sb_buf st) (sb_cap st)
     end.

Definition sb0 (SB : Z) : sbst := mkSb SB 0 64 None PJ_FUEL.

Lemma sb_k_range : forall st, (sb_fuel st <= PJ_FUEL)%nat -> 0 <= sb_k st <= 24.
Proof. intros st H. unfold sb_k, PJ_FUEL in *. lia. Qed.

Lemma SBINV_fuel : forall m SB len st, 0 <= len <= SJ_PADMAX -> SBINV m SB len st -> exists f, sb_fuel st = S f.
Proof.
  intros m SB len st HL (_ & _ & _ & _ & HF & HC & _).
  pose proof (sb_k_range st HF) as K.
  assert (K22 : sb_k st < 22) by (eapply (chain_fuel len (sb_cap st)); [exact HL| lia| apply HC| apply HC]).
  unfold sb_k, PJ_FUEL in *. destruct (sb_fuel st) as [|f]; [cbn in K22; lia| exists f; reflexivity].
Qed.

Lemma SBINV_cap_pos : forall m SB len st, SBINV m SB len st -> 64 <= sb_cap st.
Proof.
  intros m SB len st (_ & _ & _ & _ & HF & HC & _). pose proof (sb_k_range st HF) as K.
  assert (0 < 2 ^ sb_k st) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma grow_request_ok : forall m SB len st need, 0 <= len -> SBINV m SB len st ->
  sb_cap st < need -> need <= PJ_OUTMAX len -> chain_ok len (sb_cap st) (Z.max (2 * sb_cap st) need) = true.
Proof.
  intros m SB len st need HL I HN HB. apply chain_ok_machine; try assumption.
  pose proof (SBINV_cap_pos _ _ _ _ I). lia.
Qed.
Lemma grow_request_ok2 : forall m SB len st, 0 <= len -> SBINV m SB len st ->
  sb_cap st < PJ_OUTMAX len -> chain_ok len (sb_cap st) (2 * sb_cap st) = true.
Proof.
  intros m SB len st HL I HB. apply chain_ok_spec. unfold PJ_CAPMAX. pose proof (SBINV_cap_pos _ _ _ _ I). lia.
Qed.

Definition sb_grown (st : sbst) (b : bptr) (NEW z : Z) : sbst := mkSb NEW (sb_size st) z (Some b) (Nat.pred (sb_fuel st)).

Definition grow_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB0 : list block) (lo B : Z) (SB len : Z) (st : sbst) (z : Z) (m : mem)
    (b : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (NEW : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo q /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (sbblocks (sb_grown st b NEW z) ++ LB0) m'
    /\ SBINV m' SB len (sb_grown st b NEW z)
    /\ lx_pres LB0 q [(SB + 64, SB + 88)] m m'.

Definition grow_stmt : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB0 : list block) (q lo B : Z) (errv : word)
         (SB len : Z) (st : sbst) (z : Z),
  RHEAP s (sbblocks st ++ LB0) m -> rauxv_ok m B -> q <= B -> B < 2^63 ->
  stk usegs m lo q -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= q - PJ_GROW_STACK ->
  rw_cells usegs m LX_ERRNO [C4 errv] -> mem_inv usegs m ->
  q <= SB -> SB + 88 <= B ->
  0 <= len <= SJ_PADMAX -> SBINV m SB len st -> chain_ok len (sb_cap st) z = true ->
  implM usegs (pj_grow1 raw_malloc raw_free ps_so set_so_ps z (sb_blk st)) s
        (grow_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 lo B SB len st z m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SB) (Z_to_bv 64 z) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PJ_GROW) fc None m (seg_rom usegs)).

End WithCeiling0.
