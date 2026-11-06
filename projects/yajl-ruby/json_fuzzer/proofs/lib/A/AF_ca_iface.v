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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot
  AsanWf1 AsanWf3 AsanWf5 AsanRepX.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AF_fakestack_rep A_slack5 A_bundle A_init5 A_balloc5 A_rtok5 A_bevents5 AF_alloc_iface.
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
Definition A_CA : Z := 0x372a0.
Definition K_CA : Z := 3968.

(* [comment removed for export] *)
Definition ca_span (n : Z) : Z := if from_primary n then class_size (malloc_class n) else round_up (needed n) kPageSize.

(* [comment removed for export] *)
Definition ca_cost (n : Z) : Z := if from_primary n then 160 else cost2 (map_size n).
(* [comment removed for export] *)
Definition ca_gcost (n : Z) : Z := if from_primary n then 0 else map_size n + NMAXA + 4095.

Section CaIface.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).

(* [comment removed for export] *)
Definition ca_op (n : Z) : AM (option Z) :=
  aupd (upd_nprimc (from_primary n) (malloc_class n)) ;;;
  (if from_primary n then cache_pop E0 (malloc_class n) else sec_alloc E0 (needed n)).

(* [comment removed for export] *)
Definition CAINV (a1 : astate) (m : mem) (mo : Model) : Prop :=
  AWf E0 [] [] a1 /\ AKern E0 a1 mo /\ res_ok a1 /\ AQbound a1 /\ depot_inv E0 a1 /\ mem_inv asegs m /\ rt_misc5 FSB0 PL0 E0 m
  /\ sstats_ok a1                                  (* [comment removed for export] *)
  /\ csmall a1.                                    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ca_post (a a1 : astate) (m m' : mem) (mo mo' : Model) (s : aps) (C C' n lo usp : Z) (ab : Z) (a0' : word) : Prop :=
     stk asegs m' lo usp /\ wmono asegs m m'
  /\ (exists W, munch W m m' /\ Forall (aw_ok E0 a a1 lo usp) W
               /\ Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks a) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W)
  /\ (exists fuel orc evs orc', arun fuel (ca_op n a) orc = Some (a1, ONorm (Some ab), evs, orc'))
  /\ CAINV a1 m' mo'
  /\ RTOKc (C - ca_cost n) (C' - ca_gcost n) (sA a1 s) mo'
  /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo
  /\ a0' = wz ab
  /\ ARepX asegs E0 (DepotR asegs E0) a1 m' ab (ab + ca_span n)
  /\ (exists shj, rw_cells asegs m' (kShadowBase + ab / 8) [CB (Z.to_nat (ca_span n / 8)) shj]
                  /\ (from_primary n = true -> shj = repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (ca_span n / 8))))
  /\ (if from_primary n
      then as_cache_inited a1 = true /\ avail E0 [] a1 (malloc_class n) ab
           /\ exists x, ab = chunk_of_compact SB (malloc_class n) x /\ (16 * x) mod class_size (malloc_class n) = 0
      else exists r0, ab = r0 + kPageSize /\ as_sec a1 = as_sec a ++ [mkSec r0 (map_size n) (needed n)] /\ sec_fresh E0 a r0 (map_size n)).

(* [comment removed for export] *)
Definition ca_srz_case (SIDE : aps -> Z -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (n lo C C' : Z) (K : TSet),
  let a := aps_alloc s in let usp := bv_unsigned sp in
  SIDE s n ->
  K [] ->
  (* [comment removed for export] *)
  RTOKc C C' s mo -> acharge n <= C -> ca_gcost n <= C' -> AINV E0 FSB0 PL0 a m mo -> abudget_pre a n ->
  0 < n <= 2^27 -> nbig_live a <= 8000 ->
  (* [comment removed for export] *)
  stk asegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_CA -> usp mod 16 = 0 -> usp < 2^47 ->
  tp = wz 0x5e0b10 ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a1 : astate) (ab : Z),
     ca_post a a1 m m' mo mo' s C C' n lo usp ab a0' ->
     realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom asegs)) mo') K) ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INST) (wz (T + kThrCache)) (wz (needed n)) (wz 8) a4 a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_CA) fc None m (seg_rom asegs)) mo) K.

Definition ca_srz_stmt : Prop := ca_srz_case (fun _ _ => True).

Lemma ca_srz_case_join : forall (S1 S2 S : aps -> Z -> Prop),
  (forall s n, S s n -> S1 s n \/ S2 s n) -> ca_srz_case S1 -> ca_srz_case S2 -> ca_srz_case S.
Proof. intros S1 S2 S HS H1 H2. intro. intros. destruct (HS _ _ H) as [X|X]; [eapply H1| eapply H2]; eauto. Qed.
End CaIface.
End RC__1.
