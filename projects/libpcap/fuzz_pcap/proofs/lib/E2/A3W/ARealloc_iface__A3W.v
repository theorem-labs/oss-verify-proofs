(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ARealloc_iface.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition AREALLOC_SYM : Z := 0x56180.   (* [comment removed for export] *)
Definition AREALLOC_PC : Z := 0x568f0.    (* [comment removed for export] *)
Definition AREALLOC_STACK : Z := 8192.   (* [comment removed for export] *)

Section Stmts.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition arealloc_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (nold : Z) (bs : list byte) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ match snd r with
       | None => False      (* [comment removed for export] *)
       | Some q => exists A' junk,
           a0 = Z_to_bv 64 A' /\ ablock_range A' n
           /\ AHEAP L RNG' (fst r) (HB q A' n :: lb_remove p LB) m'
           /\ length junk = Z.to_nat (n - Z.min nold n)
           /\ rw_cells asegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min nold n)) bs ++ junk)]
           /\ rng RNG' A' n /\ rng RNG' (shad A') (shlen (n + 7))
       end.

Definition arealloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (bs : list byte) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m -> In (HB p A nold) LB ->
  rw_cells asegs m A [CB (Z.to_nat nold) bs] ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AREALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AREALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (arealloc ATOP RESV st p n))
        (epostF (arealloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p nold bs n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom asegs)).
End Stmts.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition AREALLOC_SYM : Z := 0x561e8.   (* [comment removed for export] *)
Definition AREALLOC_PC : Z := 0x56958.    (* [comment removed for export] *)
Definition AREALLOC_STACK : Z := 8192.   (* [comment removed for export] *)

Section Stmts.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition arealloc_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (nold : Z) (bs : list byte) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ match snd r with
       | None => False      (* [comment removed for export] *)
       | Some q => exists A' junk,
           a0 = Z_to_bv 64 A' /\ ablock_range A' n
           /\ AHEAP L RNG' (fst r) (HB q A' n :: lb_remove p LB) m'
           /\ length junk = Z.to_nat (n - Z.min nold n)
           /\ rw_cells asegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min nold n)) bs ++ junk)]
           /\ rng RNG' A' n /\ rng RNG' (shad A') (shlen (n + 7))
       end.

Definition arealloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (bs : list byte) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m -> In (HB p A nold) LB ->
  rw_cells asegs m A [CB (Z.to_nat nold) bs] ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AREALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AREALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (arealloc ATOP RESV st p n))
        (epostF (arealloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p nold bs n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom asegs)).
End Stmts.
End CANSEC1.
End TwB.
End ARealloc_iface.

(* [comment removed for export] *)
Module ARefill_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition cache_refill_tree {R} (st : astate) (c : Z) (k : astate -> bool -> AM R) : AM R :=
  let st1 := init_cache st in
  let n := max_count st1 c / 2 in
  let r1 := get_cls st1 c in
  let take (st2 : astate) : AM R :=
    let r2 := get_cls st2 c in
    if c_num_freed r2 <? n then aundef_ (UCheck 229) (k st2 false)
    else k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed r2 - n) r2)) st2) true in
  if n <=? c_num_freed r1 then take st1
  else populate_free_array st1 c (n - c_num_freed r1) (fun st2 ok => if ok then take st2 else k st2 false).

#[using="Type"] Lemma cache_alloc_unfold : forall {R} st c (k : astate -> bool -> AM R),
  cache_alloc st c k =
    (if 0 <? c_count (get_cls st c) then k (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) true
     else cache_refill_tree st c k).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition apop (c : Z) (st : astate) : astate :=
  put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st.

#[using="Type"] Lemma put_cls_put_cls : forall c r1 r2 st, put_cls c r2 (put_cls c r1 st) = put_cls c r2 st.
Proof. intros. unfold put_cls, set_cls. cbn. f_equal. apply insert_insert_eq. Qed.
#[using="Type"] Lemma get_cls_put_cls : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma take_is_apop : forall c n st2,
  put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
  = apop c (put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2).
Proof. intros. unfold apop. rewrite get_cls_put_cls, put_cls_put_cls. reflexivity. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation AREFILL_STACK := 1536 (only parsing).
Notation arefill_W L st c sp :=
  ([(sp - AREFILL_STACK, sp);
    (al_t L + 208, al_t L + 3168);   (* [comment removed for export] *)
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition refill_ret (H : aholes) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_r : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    (* [comment removed for export] *)
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c').

Definition refill_stmt (H : aholes) : Prop :=
  forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall st_r X' RNG' ms', refill_ret H L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k (apop c st_r) true)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x38ad8) fc None m (seg_rom asegs)).
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition cache_refill_tree {R} (st : astate) (c : Z) (k : astate -> bool -> AM R) : AM R :=
  let st1 := init_cache st in
  let n := max_count st1 c / 2 in
  let r1 := get_cls st1 c in
  let take (st2 : astate) : AM R :=
    let r2 := get_cls st2 c in
    if c_num_freed r2 <? n then aundef_ (UCheck 229) (k st2 false)
    else k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed r2 - n) r2)) st2) true in
  if n <=? c_num_freed r1 then take st1
  else populate_free_array st1 c (n - c_num_freed r1) (fun st2 ok => if ok then take st2 else k st2 false).

#[using="Type"] Lemma cache_alloc_unfold : forall {R} st c (k : astate -> bool -> AM R),
  cache_alloc st c k =
    (if 0 <? c_count (get_cls st c) then k (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) true
     else cache_refill_tree st c k).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition apop (c : Z) (st : astate) : astate :=
  put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st.

#[using="Type"] Lemma put_cls_put_cls : forall c r1 r2 st, put_cls c r2 (put_cls c r1 st) = put_cls c r2 st.
Proof. intros. unfold put_cls, set_cls. cbn. f_equal. apply insert_insert_eq. Qed.
#[using="Type"] Lemma get_cls_put_cls : forall c r st, get_cls (put_cls c r st) c = r.
Proof. intros. unfold get_cls, put_cls, set_cls. cbn. rewrite lookup_insert_eq. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma take_is_apop : forall c n st2,
  put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
  = apop c (put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2).
Proof. intros. unfold apop. rewrite get_cls_put_cls, put_cls_put_cls. reflexivity. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation AREFILL_STACK := 1536 (only parsing).
Notation arefill_W L st c sp :=
  ([(sp - AREFILL_STACK, sp);
    (al_t L + 208, al_t L + 3168);   (* [comment removed for export] *)
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition refill_ret (H : aholes) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_r : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    (* [comment removed for export] *)
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c').

Definition refill_stmt (H : aholes) : Prop :=
  forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall st_r X' RNG' ms', refill_ret H L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k (apop c st_r) true)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x38b40) fc None m (seg_rom asegs)).
End CANSEC2.
End TwB.
End ARefill_iface.

(* [comment removed for export] *)
Module ASecRecycle_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation SREC_STACK := 1024 (only parsing).

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Iface.
(* [comment removed for export] *)
Variable ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop.
(* [comment removed for export] *)
Variable RSEC : list achunk -> footprint -> Prop.

(* [comment removed for export] *)
Definition AHS (AQ : alayout -> astate -> aconc -> amem -> Prop) (cs : list achunk)
    (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop) : aholes :=
  mkAHoles AQ (ASECc cs) AD AF.

(* [comment removed for export] *)

(* [comment removed for export] *)
Record srec_holes_ok (AQ : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) : Prop := mkSHO {
  sho_quar : forall L st st' X X' m m' W,
      AQ L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' -> AQ L st' X' m';
  sho_depot : forall L m m' W,
      AD L m -> munch W m m' ->
      Forall (fun iv => forall a, fst iv <= a < snd iv ->
                           ~ (0x1804c8 <= a < 0x5d0510) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                           /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
      AD L m'
}.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition srec_W (L : alayout) (sp : Z) (mb ms : Z) (nres : Z) : list (Z * Z) :=
  [(sp - SREC_STACK, sp); (al_t L + 2800, al_t L + 3168); (AINSTANCE + 64, AINSTANCE + 728);
   (al_ptr_array L, al_ptr_array L + 8 * nres); (mb, mb + ms); (shad mb, shad mb + shlen ms)].
(* [comment removed for export] *)
Definition srec_hl_ok (L : alayout) (hl : Z) : Prop :=
  ablk hl (hl + 8) /\ hl + 8 <= ATOP /\ sec_clear L hl 8.

(* [comment removed for export] *)
Definition srec_ret (AQ : alayout -> astate -> aconc -> amem -> Prop) (cs1 cs2 : list achunk)
    (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (mb ms : Z) (lo : Z) (m : amem)
    (st' : astate) (RNG' : footprint) (ms' : machine_state) : Prop :=
  exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' hl,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ st' = set_nsec (a_nsec st - 1) st
    /\ srec_hl_ok L hl
    (* [comment removed for export] *)
    /\ ((mb <= hl /\ hl + 8 <= mb + ms) \/ (exists lms ln, In (CSec (hl - 24) lms ln) (cs1 ++ cs2) /\ sec_wf1 L (CSec (hl - 24) lms ln)))
    /\ munch (srec_W L (bv_unsigned sp) mb ms (a_nres st) ++ [(hl, hl + 8)]) m m' /\ mem_inv asegs m'   (* [comment removed for export] *)
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AREP (AHS AQ (cs1 ++ cs2) AD AF) L st' X m'
    (* [comment removed for export] *)
    /\ fstepS (NMunmap mb ms) (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 mb, Z_to_bv 64 ms)] [] []) RNG RNG'
    /\ arng L RNG' st' /\ RSEC (cs1 ++ cs2) RNG'.

(* [comment removed for export] *)
Definition srec_stmt : Prop :=
  forall (AQ : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
         (cs1 cs2 : list achunk) {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (mb ms n CBA lo : Z),
  srec_holes_ok AQ AD ->
  alayout_ok L -> arng L RNG st -> RSEC (cs1 ++ CSec mb ms n :: cs2) RNG ->
  AREP (AHS AQ (cs1 ++ CSec mb ms n :: cs2) AD AF) L st X m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SREC_STACK -> bv_unsigned sp <= 2^47 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (mb + PG + rz_size n - 16) ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall st' RNG' ms', srec_ret AQ cs1 cs2 AD AF L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X mb ms lo m st' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k st')) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x35f40) fc None m (seg_rom asegs)).
End Iface.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation SREC_STACK := 1024 (only parsing).

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Iface.
(* [comment removed for export] *)
Variable ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop.
(* [comment removed for export] *)
Variable RSEC : list achunk -> footprint -> Prop.

(* [comment removed for export] *)
Definition AHS (AQ : alayout -> astate -> aconc -> amem -> Prop) (cs : list achunk)
    (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop) : aholes :=
  mkAHoles AQ (ASECc cs) AD AF.

(* [comment removed for export] *)

(* [comment removed for export] *)
Record srec_holes_ok (AQ : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) : Prop := mkSHO {
  sho_quar : forall L st st' X X' m m' W,
      AQ L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' -> AQ L st' X' m';
  sho_depot : forall L m m' W,
      AD L m -> munch W m m' ->
      Forall (fun iv => forall a, fst iv <= a < snd iv ->
                           ~ (0x1808c8 <= a < 0x5d0910) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                           /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
      AD L m'
}.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition srec_W (L : alayout) (sp : Z) (mb ms : Z) (nres : Z) : list (Z * Z) :=
  [(sp - SREC_STACK, sp); (al_t L + 2800, al_t L + 3168); (AINSTANCE + 64, AINSTANCE + 728);
   (al_ptr_array L, al_ptr_array L + 8 * nres); (mb, mb + ms); (shad mb, shad mb + shlen ms)].
(* [comment removed for export] *)
Definition srec_hl_ok (L : alayout) (hl : Z) : Prop :=
  ablk hl (hl + 8) /\ hl + 8 <= ATOP /\ sec_clear L hl 8.

(* [comment removed for export] *)
Definition srec_ret (AQ : alayout -> astate -> aconc -> amem -> Prop) (cs1 cs2 : list achunk)
    (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (mb ms : Z) (lo : Z) (m : amem)
    (st' : astate) (RNG' : footprint) (ms' : machine_state) : Prop :=
  exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' hl,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ st' = set_nsec (a_nsec st - 1) st
    /\ srec_hl_ok L hl
    (* [comment removed for export] *)
    /\ ((mb <= hl /\ hl + 8 <= mb + ms) \/ (exists lms ln, In (CSec (hl - 24) lms ln) (cs1 ++ cs2) /\ sec_wf1 L (CSec (hl - 24) lms ln)))
    /\ munch (srec_W L (bv_unsigned sp) mb ms (a_nres st) ++ [(hl, hl + 8)]) m m' /\ mem_inv asegs m'   (* [comment removed for export] *)
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ AREP (AHS AQ (cs1 ++ cs2) AD AF) L st' X m'
    (* [comment removed for export] *)
    /\ fstepS (NMunmap mb ms) (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 mb, Z_to_bv 64 ms)] [] []) RNG RNG'
    /\ arng L RNG' st' /\ RSEC (cs1 ++ cs2) RNG'.

(* [comment removed for export] *)
Definition srec_stmt : Prop :=
  forall (AQ : alayout -> astate -> aconc -> amem -> Prop) (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop)
         (cs1 cs2 : list achunk) {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (mb ms n CBA lo : Z),
  srec_holes_ok AQ AD ->
  alayout_ok L -> arng L RNG st -> RSEC (cs1 ++ CSec mb ms n :: cs2) RNG ->
  AREP (AHS AQ (cs1 ++ CSec mb ms n :: cs2) AD AF) L st X m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SREC_STACK -> bv_unsigned sp <= 2^47 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (mb + PG + rz_size n - 16) ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  (forall st' RNG' ms', srec_ret AQ cs1 cs2 AD AF L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X mb ms lo m st' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k st')) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x35fa8) fc None m (seg_rom asegs)).
End Iface.
End CANSEC1.
End TwB.
End ASecRecycle_iface.

(* [comment removed for export] *)
Module F_aalloc_s.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition rz2log_post (res : Z) (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

#[using="Type"] Lemma rz2log16_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 16 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (rz2log_post 0 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x39250) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RTLS RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 16%nat ST.
  do 2 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                 (* [comment removed for export] *)
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lstep. zstep. step. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  do 4 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

#[using="Type"] Lemma rz2log2048_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 2048 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (rz2log_post 7 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x39250) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RTLS RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 16%nat ST.
  do 2 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                 (* [comment removed for export] *)
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lstep. zstep. step. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  do 4 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARSSLIM : Z := 0x130862.
#[using="Type"] Lemma rss_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m ARSSLIM [C1 (Z_to_bv 8 0)] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x624d4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros C RIMG RTLS. unfold ARSSLIM in *.
  step. lstep. zstep. step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma can_poison_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m ACANPOISON [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57588) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros C RIMG RTLS. unfold ACANPOISON in *.
  step. lstep. step. zstep. step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALSAN_TLSOFF : Z := 0xa6108.   (* [comment removed for export] *)
Definition ALSAN_CNT : Z := (ATPv + 16).       (* [comment removed for export] *)
#[using="Type"] Lemma lsan_disabled_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m ALSAN_TLSOFF [C8 (Z_to_bv 64 0x10)] ->                       (* [comment removed for export] *)
  rw_cells asegs m ALSAN_CNT [C4 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x83ae0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros -> C1 C2 RIMG RTLS. unfold ALSAN_TLSOFF, ALSAN_CNT, ATP in *.
  step. step. zstep. rewrite (Z.add_comm 16 ATPv).     (* [comment removed for export] *)
  lstep. zstep. step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMHOOKS : Z := 0x1400c0.
#[using="Type"] Lemma run_malloc_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv asegs m ->
  rw_cells asegs m AMHOOKS [C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists a0' a2' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x646f0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI HK RIMG RTLS RSTK. unfold AMHOOKS in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 32%nat ST.
  do 5 step.                                   (* [comment removed for export] *)
  do 2 step.                                   (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  step. zstep. step. step. if_lit.            (* [comment removed for export] *)
  do 6 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.
End CANSEC1.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition rz2log_post (res : Z) (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

#[using="Type"] Lemma rz2log16_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 16 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (rz2log_post 0 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x392b8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RTLS RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 16%nat ST.
  do 2 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                 (* [comment removed for export] *)
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lstep. zstep. step. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  do 4 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

#[using="Type"] Lemma rz2log2048_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 2048 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (rz2log_post 7 ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x392b8) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RTLS RSTK. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 16%nat ST.
  do 2 step.                                   (* [comment removed for export] *)
  zstep. step. zstep. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                 (* [comment removed for export] *)
  zstep. step. step. step. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lstep. zstep. step. step. if_lit.           (* [comment removed for export] *)
  step. zstep. step. if_lit.                  (* [comment removed for export] *)
  do 4 step.                                  (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARSSLIM : Z := 0x130c62.
#[using="Type"] Lemma rss_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m ARSSLIM [C1 (Z_to_bv 8 0)] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6253c) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros C RIMG RTLS. unfold ARSSLIM in *.
  step. lstep. zstep. step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma can_poison_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  rw_cells asegs m ACANPOISON [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x575f0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros C RIMG RTLS. unfold ACANPOISON in *.
  step. lstep. step. zstep. step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ALSAN_TLSOFF : Z := 0xa64e8.   (* [comment removed for export] *)
Definition ALSAN_CNT : Z := (ATPv + 16).       (* [comment removed for export] *)
#[using="Type"] Lemma lsan_disabled_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m ALSAN_TLSOFF [C8 (Z_to_bv 64 0x10)] ->                       (* [comment removed for export] *)
  rw_cells asegs m ALSAN_CNT [C4 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng_atls RNG ->
  evtF asegs RNG (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                      F (ret_pc ra) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x83b48) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros -> C1 C2 RIMG RTLS. unfold ALSAN_TLSOFF, ALSAN_CNT, ATP in *.
  step. step. zstep. rewrite (Z.add_comm 16 ATPv).     (* [comment removed for export] *)
  lstep. zstep. step. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMHOOKS : Z := 0x1404c0.
#[using="Type"] Lemma run_malloc_hooks_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv asegs m ->
  rw_cells asegs m AMHOOKS [C8 (Z_to_bv 64 0)] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists a0' a2' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x64758) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI HK RIMG RTLS RSTK. unfold AMHOOKS in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 32%nat ST.
  do 5 step.                                   (* [comment removed for export] *)
  do 2 step.                                   (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  step. zstep. step. step. if_lit.            (* [comment removed for export] *)
  do 6 step.                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End F_aalloc_s.

(* [comment removed for export] *)
Module F_acache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition combined_alloc_entry := 0x38388%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).     (* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition cache_hit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t c cnt idx spacebeg lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * idx)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj']).

#[using="Type"] Lemma combined_alloc_hit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38388) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. lia. }   (* [comment removed for export] *)
  do 2 zstep. rewrite HC.                           (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K4; zify_cond K4. { exfalso. lia. }   (* [comment removed for export] *)
  step. zstep. zstep.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  lstep.                                            (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. lia. }   (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  zstep. step. zstep. zstep.                        (* [comment removed for export] *)
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. clear RD. rewrite (zx32_small idxw) by lia.  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO.                                   (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 4 zstep.                                       (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  do 8 step.                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst R.
  setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  finish. eexists. exact STS.
Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition combined_alloc_entry := 0x383f0%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).     (* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition cache_hit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t c cnt idx spacebeg lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * idx)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj']).

#[using="Type"] Lemma combined_alloc_hit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x383f0) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. lia. }   (* [comment removed for export] *)
  do 2 zstep. rewrite HC.                           (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K4; zify_cond K4. { exfalso. lia. }   (* [comment removed for export] *)
  step. zstep. zstep.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  lstep.                                            (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. lia. }   (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  zstep. step. zstep. zstep.                        (* [comment removed for export] *)
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. clear RD. rewrite (zx32_small idxw) by lia.  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO.                                   (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 4 zstep.                                       (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  do 8 step.                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst R.
  setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  finish. eexists. exact STS.
Qed.
End CANSEC2.
End TwB.
End F_acache.

(* [comment removed for export] *)
Module F_acache2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition calloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t c lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x38638) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                  (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache_rec t c)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x38ad8) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma calloc_pre_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c lo : Z) (maxc csz : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38388) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> SZ HC CR T0 T1 RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. lia. }   (* [comment removed for export] *)
  do 2 zstep. rewrite HC.                           (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K4; zify_cond K4. { exfalso. lia. }   (* [comment removed for export] *)
  step. zstep. zstep.                               (* [comment removed for export] *)
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  lstep.                                            (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. 2: { exfalso. apply K5. reflexivity. }   (* [comment removed for export] *)
  do 7 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  subst R. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma calloc_popj_spec : forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v rv : word)
    (F : bvmap 5 word) fc (m : amem) (t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  bv_unsigned rv <> 0 ->
  1 <= c <= 16 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x38638) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38638) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  word_range sp SPR. word_range idxw IXR. word_range rv RVR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  step. if_cases K0; zify_cond K0. { exfalso. apply RV. exact K0. }   (* [comment removed for export] *)
  lstep.                                            (* [comment removed for export] *)
  do 3 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  zstep. step. zstep. zstep.                        (* [comment removed for export] *)
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. clear RD. rewrite (zx32_small idxw) by lia.  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO.                                   (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 4 zstep.                                       (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  do 8 step.                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst R.
  setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  finish. eexists. exact STS.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition calloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t c lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x386a0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                  (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache_rec t c)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x38b40) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma calloc_pre_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c lo : Z) (maxc csz : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x383f0) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> SZ HC CR T0 T1 RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. lia. }   (* [comment removed for export] *)
  do 2 zstep. rewrite HC.                           (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K4; zify_cond K4. { exfalso. lia. }   (* [comment removed for export] *)
  step. zstep. zstep.                               (* [comment removed for export] *)
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  lstep.                                            (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. 2: { exfalso. apply K5. reflexivity. }   (* [comment removed for export] *)
  do 7 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  subst R. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma calloc_popj_spec : forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v rv : word)
    (F : bvmap 5 word) fc (m : amem) (t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  bv_unsigned rv <> 0 ->
  1 <= c <= 16 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x386a0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x386a0) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RTLS RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  word_range sp SPR. word_range idxw IXR. word_range rv RVR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  step. if_cases K0; zify_cond K0. { exfalso. apply RV. exact K0. }   (* [comment removed for export] *)
  lstep.                                            (* [comment removed for export] *)
  do 3 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  zstep. step. zstep. zstep.                        (* [comment removed for export] *)
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. clear RD. rewrite (zx32_small idxw) by lia.  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO.                                   (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 4 zstep.                                       (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  do 8 step.                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst R.
  setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  finish. eexists. exact STS.
Qed.
End CANSEC1.
End TwB.
End F_acache2.
