(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ARep AMalloc_iface APoisonR_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AU_kit AU_iface AHarnessU_iface AU_parts_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section OpDel.
  Variable CI : list (Z * Z).
  Variable P : alayout -> footprint -> astate -> list ablock -> amem -> Prop.
  Definition opdelete_stmtP (entry : Z) : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A n lo : Z) (tr : list Z),
    P L RNG (aps_m s) LB m -> In (HB p A n) LB ->
    mem_inv asegs m ->
    stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
    bv_unsigned sp + 16 < al_top L ->
    tp = Z_to_bv 64 ATP ->
    a0 = Z_to_bv 64 A ->
    uchain m (al_top L) AFREE_PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr ->
    In (AFREE_PC :: bv_unsigned ra :: tr) (al_U L) ->
    bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC -> (length tr <= 28)%nat ->
    bv_unsigned sp mod 16 = 0 ->
    rng RNG lo (al_top L - lo) ->
    aps_ok L s ->
    implMA RNG (HarnessM.opdelete afree_M p) s
      (fun _ s' RNG' ms' => aps_rest s' = aps_rest s
         /\ afree_post CI P L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s) LB p lo m (aps_m s') RNG' ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End OpDel.

(* [comment removed for export] *)
Lemma opdelete_stmtP_A : forall AI entry, opdelete_stmtA_at AI entry <-> opdelete_stmtP (aci AI) (AHEAP AI) entry.
Proof. intros AI entry. unfold opdelete_stmtA_at, opdelete_stmtP. split; intros H; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kit.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  (* [comment removed for export] *)
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.

  (* [comment removed for export] *)
  Definition lblock_facts (RNG : footprint) (st : astate) (m : amem) (p : AsanCtrl.aptr) (A n : Z) : Prop :=
    1 <= n <= AREQMAX
    /\ ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7))
    /\ wr_at asegs m A n
    /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n)
    /\ (exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
           /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO))).

  Record ALooseKit := mkALooseKit {
    (* [comment removed for export] *)
    AHL : alayout -> footprint -> astate -> list ablock -> amem -> Prop;
    lk_setb : alayout -> AsanCtrl.aptr -> Z -> Z -> option (list byte) -> alayout;
    lk_tight : alayout -> Prop;
    (* [comment removed for export] *)
    lk_of_AI : forall L RNG st LB m, AHEAP AI L RNG st LB m -> AHL L RNG st LB m /\ lk_tight L;
    lk_to_AI : forall L RNG st LB m, AHL L RNG st LB m -> lk_tight L -> AHEAP AI L RNG st LB m;
    (* [comment removed for export] *)
    lk_set_some : forall L RNG st LB m m' p A n (bs : list byte) slo shi glo ghi,
        AHL L RNG st LB m -> In (HB p A n) LB ->
        munch [(slo, shi); (glo, ghi)] m m' -> wmono asegs m m' ->
        ATOP + 4096 <= slo -> shi <= 2^47 -> shad A <= glo -> ghi <= shad A + granules n ->
        rw_cells asegs m' (shad A) [CB (Z.to_nat (granules n)) bs] ->
        AHL (lk_setb L p A n (Some bs)) RNG st LB m';
    lk_set_none : forall L RNG st LB m m' p A n slo shi glo ghi,
        AHL L RNG st LB m -> In (HB p A n) LB ->
        munch [(slo, shi); (glo, ghi)] m m' -> wmono asegs m m' ->
        ATOP + 4096 <= slo -> shi <= 2^47 -> shad A <= glo -> ghi <= shad A + granules n ->
        rw_cells asegs m' (shad A) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
        AHL (lk_setb L p A n None) RNG st LB m';
    (* [comment removed for export] *)
    lk_cell_some : forall L RNG st LB m p A n (bs : list byte),
        AHL (lk_setb L p A n (Some bs)) RNG st LB m -> In (HB p A n) LB -> length bs = Z.to_nat (granules n) ->
        rw_cells asegs m (shad A) [CB (Z.to_nat (granules n)) bs];
    lk_collapse : forall L p A n e e', lk_setb (lk_setb L p A n e) p A n e' = lk_setb L p A n e';
    lk_restore : forall L p A n, lk_tight L -> lk_setb L p A n None = L;
    (* [comment removed for export] *)
    lk_top : forall L p A n e, al_top (lk_setb L p A n e) = al_top L;
    lk_bot : forall L p A n e, al_bot (lk_setb L p A n e) = al_bot L;
    lk_U : forall L p A n e, al_U (lk_setb L p A n e) = al_U L;
    lk_sp0 : forall L p A n e, al_sp0 (lk_setb L p A n e) = al_sp0 L;
    lk_V : forall L p A n e i, al_V (lk_setb L p A n e) i = al_V L i;
    lk_fflag : forall L p A n e c F, fflag (lk_setb L p A n e) c F = fflag L c F;
    lk_rngfs : forall L p A n e RNG, rng_fs (lk_setb L p A n e) RNG <-> rng_fs L RNG;
    lk_aps_ok : forall L p A n e s, aps_ok (lk_setb L p A n e) s <-> aps_ok L s;
    (* [comment removed for export] *)
    lk_frame : forall L RNG st LB m m' (W : list ivl),
        AHL L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
        Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W ->
        AHL L RNG st LB m';
    lk_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHL L RNG st LB m -> AHL L RNG' st LB m;
    lk_perm : forall L RNG st LB LB' m, Permutation.Permutation LB LB' -> AHL L RNG st LB m -> AHL L RNG st LB' m;
    (* [comment removed for export] *)
    lk_fake_flag : forall L RNG st LB m cls F N,
        AHL L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
        rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
        /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
        /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
        /\ ~ in_ranges CI (fflag L cls F);
    lk_fake_release : forall L RNG st LB m cls F N,
        AHL L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
        AHL L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]);
    (* [comment removed for export] *)
    lk_block : forall L RNG st LB m p A n, AHL L RNG st LB m -> In (HB p A n) LB -> lblock_facts RNG st m p A n;
    lk_block_bounds : forall L RNG st LB m b,
        AHL L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP;
    lk_blocks_disjoint : forall L RNG st LB m b1 b2,
        AHL L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
        ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1;
    lk_hb_ids : forall L RNG st LB m, AHL L RNG st LB m -> List.NoDup (hb_ids LB);
    lk_layout : forall L RNG st LB m, AHL L RNG st LB m ->
        al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936)
        /\ a_space_beg st = al_space_beg L /\ (length (al_U L) <= Z.to_nat AUMAX)%nat
        /\ AIMG_HI <= al_fake L /\ al_fake L + 0xb09000 <= ATOP;
    lk_rtcells : forall L RNG st LB m, AHL L RNG st LB m -> artcells m;
    lk_relro : forall L RNG st LB m, AHL L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None;
    lk_premap : forall L RNG st LB m, AHL L RNG st LB m -> premap_cells m;
    (* [comment removed for export] *)
    lk_opdel_sz : opdelete_stmtP CI AHL AOPDEL_SZ
  }.
End Kit.
End CANSEC1.
