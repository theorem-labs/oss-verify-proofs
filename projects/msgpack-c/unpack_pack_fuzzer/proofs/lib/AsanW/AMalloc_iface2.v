(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Export ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AEmbRep AEmbFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Definition twins_pres (LB : list ablock) (m m' : amem) : Prop :=
  forall p A n, In (HB p A n) LB -> is_primary n = true ->
    forall i, 0 <= i < shlen (n + 7) -> m' (wa (shad A + i)) = m (wa (shad A + i)).

Lemma twins_pres_refl : forall LB m, twins_pres LB m m.
Proof. intros LB m p A n _ _ i _. reflexivity. Qed.
Lemma twins_pres_sub : forall LB LB' m m', twins_pres LB m m' -> (forall p A n, In (HB p A n) LB' -> In (HB p A n) LB) -> twins_pres LB' m m'.
Proof. intros LB LB' m m' T SUB p A n Hin PR i Hi. exact (T p A n (SUB p A n Hin) PR i Hi). Qed.
Lemma twins_pres_trans : forall LB m1 m2 m3, twins_pres LB m1 m2 -> twins_pres LB m2 m3 -> twins_pres LB m1 m3.
Proof. intros LB m1 m2 m3 T1 T2 p A n Hin PR i Hi. rewrite (T2 p A n Hin PR i Hi). exact (T1 p A n Hin PR i Hi). Qed.

Definition aheap_pres_e (CI : list (Z * Z)) (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
  forall a, 0 <= a < 2^64 -> aclient_addr CI LB SP a -> ~ (AERRNO <= a < AERRNO + 4) ->
    m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Lemma aheap_pres_e_of : forall CI LB SP m m', aheap_pres CI LB SP m m' -> aheap_pres_e CI LB SP m m'.
Proof. intros CI LB SP m m' H a Ha Hc _. exact (H a Ha Hc). Qed.

Definition c6m (RESV : list (Z * Z)) (RNG : footprint) (st : astate) : Prop := emb_rng st RNG /\ emb_clr RESV st.

Section Stmts.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition amalloc_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ match snd r with
       | None => False
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ ablock_range A n
           /\ AHEAP L RNG' (fst r) (HB p A n :: LB) m'
           /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
           /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
           /\ (is_primary n = false -> A = aptr_addr (fst r) p)
           /\ ablock_shadow m' A n
       end.

Definition amalloc_stmt2 : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).

Definition amalloc_null_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list ablock) (lo : Z) (m : amem) (st' : astate) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres_e CI LB (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ AHEAP L RNG' st' LB m'
    /\ rw_cells asegs m' AERRNO [C4 (Z_to_bv 64 12)].
Definition amalloc_post2x (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => amalloc_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => amalloc_null_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB lo m (fst r) RNG' ms'
    end.
Definition amalloc_stmt2x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells asegs m AERRNO [C4 e0]) ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post2x L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).

Definition afree_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (lo : Z) (m : amem)
    (r : astate) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ twins_pres (lb_remove p LB) m m'
    /\ AHEAP L RNG' r (lb_remove p LB) m'.

Definition afree_stmt2 : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z),
  AHEAP L RNG st LB m -> In (HB p A n) LB ->
  ablock_shadow m A n ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).

Definition afree_null_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ AHEAP L RNG st LB m'.

Definition afree_null_stmt2 : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (lo : Z) (tr : list Z),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (afree_null_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
End Stmts.

Record AMallocIface2 := mkAMallocIface2 {
  aci : list (Z * Z);
  AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop;

  AI_aci_img : forall iv, In iv aci -> snd iv <= AIMG_HI;
  AI_aci_lo : forall iv, In iv aci -> 0 <= fst iv;
  AI_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP L RNG st LB m -> AHEAP L RNG' st LB m;
  AI_perm : forall L RNG st LB LB' m, Permutation.Permutation LB LB' -> AHEAP L RNG st LB m -> AHEAP L RNG st LB' m;
  AI_frame : forall L RNG st LB m m' (W : list ivl),
      AHEAP L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
      Forall (fun iv => aclient_range aci LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W ->
      AHEAP L RNG st LB m';
  AI_frame_twin : forall L RNG st LB m m' p A n,
      AHEAP L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
      munch [(shad A, shad A + shlen (n + 7))] m m' -> wmono asegs m m' ->
      (forall i, 0 <= i < shlen (n + 7) -> m' (wa (shad A + i)) <> None) ->
      AHEAP L RNG st LB m';
  AI_block : forall L RNG st LB m p A n,
      AHEAP L RNG st LB m -> In (HB p A n) LB ->
      1 <= n <= AREQMAX /\
      ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7))
      /\ (exists bs, rw_cells asegs m (shad A) [CB (Z.to_nat (shlen (n + 7))) bs] /\ (is_primary n = false -> ablock_shadow m A n))
      /\ wr_at asegs m A n
      /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
      /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
           /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO));
  AI_block_bounds : forall L RNG st LB m b,
      AHEAP L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP;
  AI_blocks_disjoint : forall L RNG st LB m b1 b2,
      AHEAP L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
      ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1;
  AI_blocks_nodup : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup LB;
  AI_hb_ids : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup (hb_ids LB);
  AI_layout : forall L RNG st LB m, AHEAP L RNG st LB m ->
      al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936)
      /\ a_space_beg st = al_space_beg L /\ (length (al_U L) <= Z.to_nat AUMAX)%nat
      /\ AIMG_HI <= al_fake L /\ al_fake L + 0xb09000 <= ATOP;
  AI_relro : forall L RNG st LB m, AHEAP L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None;
  AI_rtcells : forall L RNG st LB m, AHEAP L RNG st LB m -> artcells m;

  AI_malloc : amalloc_stmt2x aci AHEAP;
  AI_free : afree_stmt2 aci AHEAP;
  AI_free_null : afree_null_stmt2 aci AHEAP
}.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import AProto.TwinB.
Export ABase.TwinB.
Import AMalloc_iface.TwinB.
Import AEmbRep.TwinB AEmbFrame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Definition twins_pres (LB : list ablock) (m m' : amem) : Prop :=
  forall p A n, In (HB p A n) LB -> is_primary n = true ->
    forall i, 0 <= i < shlen (n + 7) -> m' (wa (shad A + i)) = m (wa (shad A + i)).

Lemma twins_pres_refl : forall LB m, twins_pres LB m m.
Proof. intros LB m p A n _ _ i _. reflexivity. Qed.
Lemma twins_pres_sub : forall LB LB' m m', twins_pres LB m m' -> (forall p A n, In (HB p A n) LB' -> In (HB p A n) LB) -> twins_pres LB' m m'.
Proof. intros LB LB' m m' T SUB p A n Hin PR i Hi. exact (T p A n (SUB p A n Hin) PR i Hi). Qed.
Lemma twins_pres_trans : forall LB m1 m2 m3, twins_pres LB m1 m2 -> twins_pres LB m2 m3 -> twins_pres LB m1 m3.
Proof. intros LB m1 m2 m3 T1 T2 p A n Hin PR i Hi. rewrite (T2 p A n Hin PR i Hi). exact (T1 p A n Hin PR i Hi). Qed.

Definition aheap_pres_e (CI : list (Z * Z)) (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
  forall a, 0 <= a < 2^64 -> aclient_addr CI LB SP a -> ~ (AERRNO <= a < AERRNO + 4) ->
    m' (wa a) = m (wa a) /\ (wview bsegs m (wa a) <> None -> wview bsegs m' (wa a) <> None).
Lemma aheap_pres_e_of : forall CI LB SP m m', aheap_pres CI LB SP m m' -> aheap_pres_e CI LB SP m m'.
Proof. intros CI LB SP m m' H a Ha Hc _. exact (H a Ha Hc). Qed.

Definition c6m (RESV : list (Z * Z)) (RNG : footprint) (st : astate) : Prop := emb_rng st RNG /\ emb_clr RESV st.

Section Stmts.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition amalloc_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ match snd r with
       | None => False
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ ablock_range A n
           /\ AHEAP L RNG' (fst r) (HB p A n :: LB) m'
           /\ rw_cells bsegs m' A [CB (Z.to_nat n) junk]
           /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
           /\ (is_primary n = false -> A = aptr_addr (fst r) p)
           /\ ablock_shadow m' A n
       end.

Definition amalloc_stmt2 : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).

Definition amalloc_null_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list ablock) (lo : Z) (m : amem) (st' : astate) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres_e CI LB (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ AHEAP L RNG' st' LB m'
    /\ rw_cells bsegs m' AERRNO [C4 (Z_to_bv 64 12)].
Definition amalloc_post2x (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => amalloc_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => amalloc_null_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB lo m (fst r) RNG' ms'
    end.
Definition amalloc_stmt2x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells bsegs m AERRNO [C4 e0]) ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post2x L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).

Definition afree_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (lo : Z) (m : amem)
    (r : astate) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ twins_pres (lb_remove p LB) m m'
    /\ AHEAP L RNG' r (lb_remove p LB) m'.

Definition afree_stmt2 : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z),
  AHEAP L RNG st LB m -> In (HB p A n) LB ->
  ablock_shadow m A n ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).

Definition afree_null_post2 (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ twins_pres LB m m'
    /\ AHEAP L RNG st LB m'.

Definition afree_null_stmt2 : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (lo : Z) (tr : list Z),
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (afree_null_post2 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
End Stmts.

Record AMallocIface2 := mkAMallocIface2 {
  aci : list (Z * Z);
  AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop;

  AI_aci_img : forall iv, In iv aci -> snd iv <= AIMG_HI;
  AI_aci_lo : forall iv, In iv aci -> 0 <= fst iv;
  AI_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP L RNG st LB m -> AHEAP L RNG' st LB m;
  AI_perm : forall L RNG st LB LB' m, Permutation.Permutation LB LB' -> AHEAP L RNG st LB m -> AHEAP L RNG st LB' m;
  AI_frame : forall L RNG st LB m m' (W : list ivl),
      AHEAP L RNG st LB m -> munch W m m' -> wmono bsegs m m' ->
      Forall (fun iv => aclient_range aci LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W ->
      AHEAP L RNG st LB m';
  AI_frame_twin : forall L RNG st LB m m' p A n,
      AHEAP L RNG st LB m -> In (HB p A n) LB -> is_primary n = true ->
      munch [(shad A, shad A + shlen (n + 7))] m m' -> wmono bsegs m m' ->
      (forall i, 0 <= i < shlen (n + 7) -> m' (wa (shad A + i)) <> None) ->
      AHEAP L RNG st LB m';
  AI_block : forall L RNG st LB m p A n,
      AHEAP L RNG st LB m -> In (HB p A n) LB ->
      1 <= n <= AREQMAX /\
      ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7))
      /\ (exists bs, rw_cells bsegs m (shad A) [CB (Z.to_nat (shlen (n + 7))) bs] /\ (is_primary n = false -> ablock_shadow m A n))
      /\ wr_at bsegs m A n
      /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
      /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
           /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at bsegs m (shad RLO) (shlen (RHI - RLO));
  AI_block_bounds : forall L RNG st LB m b,
      AHEAP L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP;
  AI_blocks_disjoint : forall L RNG st LB m b1 b2,
      AHEAP L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
      ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1;
  AI_blocks_nodup : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup LB;
  AI_hb_ids : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup (hb_ids LB);
  AI_layout : forall L RNG st LB m, AHEAP L RNG st LB m ->
      al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936)
      /\ a_space_beg st = al_space_beg L /\ (length (al_U L) <= Z.to_nat AUMAX)%nat
      /\ AIMG_HI <= al_fake L /\ al_fake L + 0xb09000 <= ATOP;
  AI_relro : forall L RNG st LB m, AHEAP L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None;
  AI_rtcells : forall L RNG st LB m, AHEAP L RNG st LB m -> artcells m;

  AI_malloc : amalloc_stmt2x aci AHEAP;
  AI_free : afree_stmt2 aci AHEAP;
  AI_free_null : afree_null_stmt2 aci AHEAP
}.
End CANSEC1.
End TwinB.
