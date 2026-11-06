(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface ADepot_iface APoisonR_iface ARep AHeapP ASec F_amalloc_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AEmbRep AEmbFrame ARefill_iface_x ARefillP_x AC6Frame. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMallocPG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.AMallocPG_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMallocPG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.AAllocatePG_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMallocS_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocS_x.AMallocS_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMallocS_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocS_x.AAllocateS_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Notation AMALLOC_STACK_X := 4608 (only parsing).
Section Stmt.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition amalloc_stmt_x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK_X ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells asegs m AERRNO [C4 e0]) ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post_x CI AHEAP L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).

Definition aallocate_stmt_x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo S pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->

  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> bv_unsigned sp + 2144 < 2^47 -> rng RNG S 2056 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (aallocate_post_x CI AHEAP L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).

Definition amalloc_post_h (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
        /\ aheap_pres_e CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
        /\ rw_cells asegs m' AERRNO [C4 (Z_to_bv 64 12)]
    end.
Definition amalloc_stmt_h : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK_X ->
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
        (epostF (amalloc_post_h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).

Definition aallocate_post_h (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
        /\ aheap_pres CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
    end.
Definition aallocate_stmt_h : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo S pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> bv_unsigned sp + 2144 < 2^47 -> rng RNG S 2056 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (aallocate_post_h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
End Stmt.

Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis HLD : ahole_lawsD (AH DI AQ ASEC_of AFK).
Hypothesis EXHW : exh_first_stmt.
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15bd20 \/ 0x15bd21 <= fst iv)) CI.

Theorem amalloc_all_x : amalloc_stmt_x CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold amalloc_stmt_x. intros.
  destruct (is_primary n) eqn:P.
  - eapply (amalloc_prim_x DI AQ ASEC_of AFK HL HLD EXHW CI CI_OK CI_OK2 CI_OK3); eassumption.
  - eapply (amalloc_sec_x DI AQ AFK HL PR CI CI_OK CI_OK2 CI_OK3); try eassumption. unfold AMALLOC_STACK. lia.
Qed.

Theorem aallocate_all_x : aallocate_stmt_x CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold aallocate_stmt_x. intros.
  destruct (is_primary n) eqn:P.
  - eapply (aallocate_prim_x DI AQ ASEC_of AFK HL HLD EXHW CI CI_OK CI_OK2 CI_OK3); eassumption.
  - eapply (aallocate_sec_x DI AQ AFK HL PR CI CI_OK CI_OK2 CI_OK3); eassumption.
Qed.

Lemma aheap_c6 : forall L RNG st LB m, AHEAP_P (AH DI AQ ASEC_of AFK) L RNG st LB m -> AEXH L st m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _). destruct AR as (_ & _ & _ & _ & _ & _ & HS & _).
  exact (hx_get _ HLD L st X m HS).
Qed.
Theorem amalloc_all_h : amalloc_stmt_h CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold amalloc_stmt_h. intros until RESV. intros OVF AHP MI ST BOT LO TP A0 NR AUNW S0NE RA4 RANE SP16 RSTK ARV FCB [ER ECL] CAPB ERRC.
  destruct (aheap_c6 _ _ _ _ _ AHP) as (XC & EC & AXF & _ & _).
  eapply implF_epost_mono.
  { eapply (amalloc_all_x L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo tr RESV); try eassumption.
    split; [exact XC|]. split; [exact EC|]. split; [exact ER| exact ECL]. }
  intros r RNG' ms' [_ M]. exact M.
Qed.
Theorem aallocate_all_h : aallocate_stmt_h CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold aallocate_stmt_h. intros until RESV.
  intros OVF AHP MI ST BOT LO TP A0 A1 A2 A3 A4 A5 NR SSA TB LTB TRF TRU LTRC SPS S47 SP47 RS RSTK ARV FCB [ER ECL] CAPB.
  destruct (aheap_c6 _ _ _ _ _ AHP) as (XC & EC & AXF & _ & _).
  eapply implF_epost_mono.
  { eapply (aallocate_all_x L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo S pc trc tb RESV); try eassumption.
    split; [exact XC|]. split; [exact EC|]. split; [exact ER| exact ECL]. }
  intros r RNG' ms' [_ M]. exact M.
Qed.
End S.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB ADepot_iface.TwinB APoisonR_iface.TwinB ARep.TwinB AHeapP.TwinB ASec.TwinB F_amalloc_arep.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import AEmbRep.TwinB AEmbFrame.TwinB ARefill_iface_x.TwinB ARefillP_x.TwinB AC6Frame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.TwinB.AMallocPG_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.TwinB.AAllocatePG_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocS_x.TwinB.AMallocS_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocS_x.TwinB.AAllocateS_x.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Notation AMALLOC_STACK_X := 4608 (only parsing).
Section Stmt.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition amalloc_stmt_x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK_X ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells bsegs m AERRNO [C4 e0]) ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post_x CI AHEAP L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).

Definition aallocate_stmt_x : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo S pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->

  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr bsegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> bv_unsigned sp + 2144 < 2^47 -> rng RNG S 2056 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (aallocate_post_x CI AHEAP L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).

Definition amalloc_post_h (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ aheap_pres_e CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
        /\ rw_cells bsegs m' AERRNO [C4 (Z_to_bv 64 12)]
    end.
Definition amalloc_stmt_h : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK_X ->
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
        (epostF (amalloc_post_h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).

Definition aallocate_post_h (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ aheap_pres CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
    end.
Definition aallocate_stmt_h : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo S pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->
  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr bsegs m (S + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 -> bv_unsigned sp + 2144 < 2^47 -> rng RNG S 2056 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (aallocate_post_h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
End Stmt.

Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis HLD : ahole_lawsD (AH DI AQ ASEC_of AFK).
Hypothesis EXHW : exh_first_stmt.
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15dee0 \/ 0x15dee1 <= fst iv)) CI.

Theorem amalloc_all_x : amalloc_stmt_x CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold amalloc_stmt_x. intros.
  destruct (is_primary n) eqn:P.
  - eapply (amalloc_prim_x DI AQ ASEC_of AFK HL HLD EXHW CI CI_OK CI_OK2 CI_OK3); eassumption.
  - eapply (amalloc_sec_x DI AQ AFK HL PR CI CI_OK CI_OK2 CI_OK3); try eassumption. unfold AMALLOC_STACK. lia.
Qed.

Theorem aallocate_all_x : aallocate_stmt_x CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold aallocate_stmt_x. intros.
  destruct (is_primary n) eqn:P.
  - eapply (aallocate_prim_x DI AQ ASEC_of AFK HL HLD EXHW CI CI_OK CI_OK2 CI_OK3); eassumption.
  - eapply (aallocate_sec_x DI AQ AFK HL PR CI CI_OK CI_OK2 CI_OK3); eassumption.
Qed.

Lemma aheap_c6 : forall L RNG st LB m, AHEAP_P (AH DI AQ ASEC_of AFK) L RNG st LB m -> AEXH L st m.
Proof.
  intros L RNG st LB m (_ & _ & [X [AR _]] & _). destruct AR as (_ & _ & _ & _ & _ & _ & HS & _).
  exact (hx_get _ HLD L st X m HS).
Qed.
Theorem amalloc_all_h : amalloc_stmt_h CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold amalloc_stmt_h. intros until RESV. intros OVF AHP MI ST BOT LO TP A0 NR AUNW S0NE RA4 RANE SP16 RSTK ARV FCB [ER ECL] CAPB ERRC.
  destruct (aheap_c6 _ _ _ _ _ AHP) as (XC & EC & AXF & _ & _).
  eapply implF_epost_mono.
  { eapply (amalloc_all_x L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo tr RESV); try eassumption.
    split; [exact XC|]. split; [exact EC|]. split; [exact ER| exact ECL]. }
  intros r RNG' ms' [_ M]. exact M.
Qed.
Theorem aallocate_all_h : aallocate_stmt_h CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold aallocate_stmt_h. intros until RESV.
  intros OVF AHP MI ST BOT LO TP A0 A1 A2 A3 A4 A5 NR SSA TB LTB TRF TRU LTRC SPS S47 SP47 RS RSTK ARV FCB [ER ECL] CAPB.
  destruct (aheap_c6 _ _ _ _ _ AHP) as (XC & EC & AXF & _ & _).
  eapply implF_epost_mono.
  { eapply (aallocate_all_x L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo S pc trc tb RESV); try eassumption.
    split; [exact XC|]. split; [exact EC|]. split; [exact ER| exact ECL]. }
  intros r RNG' ms' [_ M]. exact M.
Qed.
End S.
End CANSEC1.
End TwinB.
