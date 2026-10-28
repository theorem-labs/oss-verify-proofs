(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG CtSizes CtWire CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs W_bio_push W_bio_write W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition GENTIME_ADJ : Z := 0x12d468.
Definition GENTIME_SET_STRING : Z := 0x12d3d4.
Definition GENTIME_PRINT : Z := 0x12d4f8.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition gentime_leaf_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (r : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gentime_adj_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (canary : word)
    (s : PState) (L : list block) (lo B : Z) (m : mem) (G : Z) (t : tm6)
    (p : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem) (D : Z) (errv' : word) (junk : list (bv 8)),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)      (* [comment removed for export] *)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_but L (bv_unsigned sp) (G, G + 24) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rblock_range D 20 /\ RHEAP s' ((p, D, 20) :: L) m'
    /\ rw_cells ctusegs m' G (asn1_string_cells 15 V_ASN1_GENERALIZEDTIME D 0)
    /\ rw_cells ctusegs m' D [CB 20%nat (zb (gen15 t) ++ Z_to_bv 8 0 :: junk)] /\ length junk = 4%nat.

Definition gentime_adj_ok_stmt (STACK : Z) : Prop :=
  forall (X : Type) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv canary : word)
         (G : Z) (gb : bptr) (ts : Z) (t : tm6)
         (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp < 2^63 ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - STACK -> bv_unsigned sp mod 16 = 0 ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP -> crypto_statics m -> realloc_statics m ->
    ssp_cells m canary -> frm0 fc ->
    In (gb, G, 24) L -> rw_cells ctusegs m G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) ->
    0 <= ts < 2^64 -> gentime_adj ts = Some t ->
    a0 = wz G -> a1 = wz 0 -> a2 = wz (ts_day ts) -> a3 = wz (ts_sec ts) ->
    k None = LUnr ->
    (forall p s' ms', gentime_adj_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F canary s L lo B m G t p s' ms' ->
                     implM ctusegs (interp (k (Some p))) s' Q ms') ->
    implM ctusegs (interp (LMalloc 20 k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz GENTIME_ADJ) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition gentime_adj_fail_stmt (STACK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (G : Z) (ts : Z) (canary : word),
    stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - STACK -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^63 ->
    ssp_cells m canary -> tp = wz RATP -> frm0 fc ->
    rw_cells ctusegs m G (asn1_string_cells 0 V_ASN1_GENERALIZEDTIME 0 0) -> (G + 24 <= lo \/ bv_unsigned sp <= G) ->
    0 <= ts < 2^64 -> gentime_adj ts = None ->
    a0 = wz G -> a1 = wz 0 -> a2 = wz (ts_day ts) -> a3 = wz (ts_sec ts) ->
    evt ctusegs (gentime_leaf_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz GENTIME_ADJ) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gentime_setstr_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (L : list block) (lo B : Z) (m : mem) (G D : Z) (dp : bptr) (ts : Z)
    (p' : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (errv' : word),
    ms' = MS (mkR ra sp gp (wz RATP) t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_but (lb_remove dp L) (bv_unsigned sp) (G, G + 24) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((p', D, 19) :: lb_remove dp L) m'
    /\ rw_cells ctusegs m' G (asn1_string_cells 19 V_ASN1_GENERALIZEDTIME D 0)
    /\ rw_cells ctusegs m' D [CB 19%nat (zb (genstr ts))].

Definition gentime_setstr_ok_stmt (STACK : Z) : Prop :=
  forall (X : Type) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (L : list block) (lo B : Z) (errv : word)
         (G D GS : Z) (gb dp : bptr) (ts : Z) (djunk : list (bv 8)) (gtail : list (bv 8))
         (k : option bptr -> lprog X) (Q : X -> PState -> machine_state -> Prop),
    RHEAP s L m -> rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
    stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - STACK -> bv_unsigned sp mod 16 = 0 ->
    rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RATP -> crypto_statics m -> realloc_statics m -> frm0 fc ->
    In (gb, G, 24) L -> In (dp, D, 20) L -> gb <> dp ->
    rw_cells ctusegs m G (asn1_string_cells 15 V_ASN1_GENERALIZEDTIME D 0) -> rw_cells ctusegs m D [CB 20%nat djunk] ->
    printable ts = true -> 0 <= ts < 2^64 ->
    rw_cells ctusegs m GS [CB 20%nat (zb (genstr ts) ++ Z_to_bv 8 0 :: gtail)] -> bv_unsigned sp <= GS -> GS + 20 <= B -> (GS + 20) mod 8 = 0 ->
    a0 = wz G -> a1 = wz GS ->
    k None = LUnr ->
    (forall p' s' ms', gentime_setstr_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s L lo B m G D dp ts p' s' ms' ->
                      implM ctusegs (interp (k (Some p'))) s' Q ms') ->
    implM ctusegs (interp (LReallocI dp 19 k)) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz GENTIME_SET_STRING) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition gentime_setstr_fail_stmt (STACK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (G GS ts : Z) (gtail : list (bv 8)) (canary : word),
    stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - STACK -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^63 ->
    ssp_cells m canary -> tp = wz RATP -> frm0 fc ->
    printable ts = false -> 0 <= ts < 2^64 ->
    rw_cells ctusegs m GS [CB 20%nat (zb (genstr ts) ++ Z_to_bv 8 0 :: gtail)] -> bv_unsigned sp <= GS -> GS + 20 <= 2^63 ->
    a0 = wz G -> a1 = wz GS ->
    evt ctusegs (gentime_leaf_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz GENTIME_SET_STRING) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition gentime_print_stmt (STACK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (G D out pv nw ts : Z) (canary : word),
    stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - STACK -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^63 ->
    ssp_cells m canary -> tp = wz RATP -> frm0 fc ->
    rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw) -> obj_range out BIO_SIZE lo -> 0 <= nw < 2^64 -> null_meth_cells m ->
    rw_cells ctusegs m G (asn1_string_cells 19 V_ASN1_GENERALIZEDTIME D 0) -> (G + 24 <= lo \/ bv_unsigned sp <= G) -> (G + 24 <= out \/ out + 128 <= G) ->
    rw_cells ctusegs m D [CB 19%nat (zb (genstr ts))] -> printable ts = true -> 0 <= ts < 2^64 ->
    4096 <= D -> D + 19 <= lo -> (D + 19 <= out \/ out + 128 <= D) ->
    0 < G -> G mod 8 = 0 -> out mod 8 = 0 ->
    a0 = wz out -> a1 = wz G ->
    evt ctusegs (fun ms' => exists r, 0 <= r <= 28 /\
                   bio_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo [(out, out + 128)] canary 1
                     (fun m' => rw_cells ctusegs m' out (bio_null_cells NULL_METHOD pv (nw + r))) m ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz GENTIME_PRINT) fc None m (seg_rom ctusegs)).

End WithCeiling0.
