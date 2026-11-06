(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AF_fakestack_rep A_slack5 A_bundle A_init5 A_balloc5 A_rtok5 AF_alloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_DEPOT_PUT : Z := 0x73f64.
Definition dTD : Z := 0x18fa58.      (* [comment removed for export] *)
Definition dSS : Z := 0x17fa48.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition DSLACK : Z := 2^29.
Lemma DSLACK_covers : 2 * NMAXA + 2^20 + 2^23 + 2 * 4095 <= DSLACK.
Proof. unfold DSLACK, NMAXA. cbn. lia. Qed.
(* [comment removed for export] *)
Definition K_DEPOT : Z := 640.

Section DputIface.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).

(* [comment removed for export] *)
Definition dput_statics (m : mem) : Prop :=
  statics m /\ rw_cells asegs m (V_CFLAGS + 240) [C4 (wz 0)].

(* [comment removed for export] *)
Definition dput_mutexes (m : mem) : Prop :=
  rw_cells asegs m (dTD + 0x400008) [C4 (wz 0)]
  /\ (forall k, 0 <= k < kStoreBlockCount -> rw_cells asegs m (dSS + 28 + 16 * k) [C4 (wz 0)]).

(* [comment removed for export] *)
Definition dput_scur (a : astate) : Prop := as_frames a <= kStoreBlockFrames * (zlen (as_store_blocks a) + 1).
Lemma DepotR_scur : forall a m, DepotR asegs E0 a m -> dput_scur a.
Proof. intros a m [(_ & _ & _ & _ & _ & _ & SC) _]. exact SC. Qed.

(* [comment removed for export] *)
Definition dput_w_ok (a' : astate) (lo usp : Z) (iv : Z * Z) : Prop :=
  let x := fst iv in let y := snd iv in
     (lo <= x /\ y <= usp)
  \/ (exists r, In r (depot_static E0) /\ fst r <= x /\ y <= fst r + snd r)
  \/ (exists b, In b (ae_depot_nodes E0 :: as_node_blocks a') /\ b <= x /\ y <= b + kDepotNodeBlockBytes)
  \/ (exists b, In b (ae_store_blk E0 :: as_store_blocks a') /\ b <= x /\ y <= b + kStoreBlockBytes).

Lemma dput_w_ok_pt : forall a' lo usp iv, dput_w_ok a' lo usp iv ->
  (lo <= fst iv /\ snd iv <= usp) \/ (forall z, fst iv <= z < snd iv -> DepotFPd E0 a' z).
Proof.
  intros a' lo usp [x y] H. unfold dput_w_ok in H. cbn [fst snd] in *.
  destruct H as [H|[(r & Hr & H1 & H2)|[(b & Hb & H1 & H2)|(b & Hb & H1 & H2)]]]; [left; exact H| right| right| right]; intros z Hz.
  - left. exists r. split; [| clear -H1 H2 Hz; lia].
    unfold depot_static in Hr. destruct Hr as [<-|[<-|[]]]; [left| right; left]; reflexivity.
  - right; left. exists b. split; [exact Hb| clear -H1 H2 Hz; lia].
  - right; right. exists b. split; [exact Hb| clear -H1 H2 Hz; lia].
Qed.

(* [comment removed for export] *)
Definition dput_post_state (a a' : astate) (m m' : mem) (mo mo' : Model) (s : aps) (C C' lo usp : Z) (key : list Z) (id : Z) : Prop :=
     stk asegs m' lo usp /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ (exists W, munch W m m' /\ Forall (dput_w_ok a' lo usp) W)
  /\ (exists fuel orc evs orc', arun fuel (depot_put E0 key a) orc = Some (a', ONorm id, evs, orc'))
  /\ 1 <= id < 2^31
  /\ DepotR asegs E0 a' m' /\ dput_mutexes m' /\ dput_statics m'
  /\ AKern E0 a' mo'
  /\ RTOKc (C - 1) (C' - DSLACK) (sA a' s) mo'
  /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo.

(* [comment removed for export] *)
Definition depot_put_srz_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (Pq : list Z) (Dq : list batch)
         (lo A len C C' : Z) (ws : list word) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> 1 <= C -> DSLACK <= C' -> AKern E0 a mo -> AWf E0 Pq Dq a ->
  zlen (as_node_blocks a) <= 1832 -> zlen (as_store_blocks a) <= 7400 -> AsanState.sec_bytes a <= 2^39 ->
  as_ndepot_ins a + 1 <= kInitialCredit ->
  (* [comment removed for export] *)
  DepotR asegs E0 a m -> dput_mutexes m -> dput_statics m -> mem_inv asegs m ->
  (* [comment removed for export] *)
  stk asegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_DEPOT -> usp mod 16 = 0 ->
  (* [comment removed for export] *)
  usp <= A -> A + 8 * zlen ws < 2^47 -> u64arr asegs m A ws -> 1 <= len <= zlen ws -> zlen ws <= 30 ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate) (id : Z),
     dput_post_state a a' m m' mo mo' s C C' lo usp (bst_key len ws) id ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz id) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) (wz len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_DEPOT_PUT) fc None m (seg_rom asegs)) mo) K.

End DputIface.
End RC__1.
