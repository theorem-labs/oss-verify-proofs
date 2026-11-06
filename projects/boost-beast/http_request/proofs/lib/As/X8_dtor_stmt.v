(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2
     AXRep_fields AXRep_mbuf X8Kit X8SRKit X8_F_insert4 X8_rsfree X8_state2_stmt X8_pst.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ADL_LOOP : Z := 0xb833c.          (* [comment removed for export] *)
Definition ADL_RA   : Z := 0xb8390.          (* [comment removed for export] *)
Definition ADL_EXIT : Z := 0xb83c0.          (* [comment removed for export] *)
Definition ADELETE_LIST_STACK : Z := 32 + AFREE_STACK.

Definition ABF_RA1 : Z := 0xb8210.  Definition ABF_RA2 : Z := 0xb8224.  Definition ABF_RA3 : Z := 0xb8238.
Definition ABFIELDS_DTOR_STACK : Z := 16 + RSFREE_STACK.      (* [comment removed for export] *)

Definition AMB_LOOP : Z := 0xb8294.          (* [comment removed for export] *)
Definition AMB_RA   : Z := 0xb82cc.          (* [comment removed for export] *)
Definition AMB_EXIT : Z := 0xb82d4.
Definition AMBUF_DTOR_STACK : Z := 32 + AFREE_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition afowned (em : gmap Z elt) (b : block) : Prop :=
  exists d, em !! (blk_addr b) = Some d /\ blk_size b = esize d.

(* [comment removed for export] *)
Definition abfowned (em : gmap Z elt) (h : hdrv) (b : block) : Prop :=
  afowned em b \/ svowned (hv_mp h) (hv_ml h) b \/ svowned (hv_tp h) (hv_tl h) b.

(* [comment removed for export] *)
Definition hdr_cleared (h : hdrv) : hdrv := mkHV 0 0 0 0 (hv_ver h) (hv_vb h).

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
Fixpoint dl_cost (L : list Z) (em : gmap Z elt) : Z :=
  match L with
  | [] => 0
  | e :: L' => match em !! e with Some d => as_Cf H (esize d) | None => 0 end + dl_cost L' em
  end.
Fixpoint mb_cost (es : list mbe) : Z :=
  match es with [] => 0 | (x, s) :: es' => as_Cf H (mb_block_size s) + mb_cost es' end.
Definition bf_cost (L : list Z) (em : gmap Z elt) (h : hdrv) : Z := dl_cost L em + as_Cf H (hv_ml h) + as_Cf H (hv_tl h).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition adelete_list_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (lo B shi : Z) (L : list Z) (em : gmap Z elt) (errv : word)
    (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' LB' m'
    /\ (forall b, In b LB' <-> (In b LB /\ ~ afowned em b))
    /\ lb_bytes LB' <= lb_bytes LB /\ (length LB' <= length LB)%nat
    /\ xpres H LB' (bv_unsigned sp) [] m m'
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - dl_cost L em.

Definition adelete_list_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (Fa lo B shi : Z) (S L : list Z) (ns : NS) (ls : LS) (em : gmap Z elt)
         (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_FIELDS_DELETE_LIST) fc None m (seg_rom asegs) ->
    a0 = wz Fa ->
    AFieldsC m Fa S L ns ls em -> AFieldsOwn LB em ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ADELETE_LIST_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
    bv_unsigned sp mod 16 = 0 ->
    (* [comment removed for export] *)
    aobj LB LF Fa 48 -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    dl_cost L em <= as_AL H s ->
    as_SR H (adelete_list_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF lo B shi L em errv m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition abfields_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (Fa lo B shi : Z) (L : list Z) (em : gmap Z elt) (h : hdrv) (errv : word)
    (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' LB' m'
    /\ (forall b, In b LB' <-> (In b LB /\ ~ abfowned em h b))
    /\ lb_bytes LB' <= lb_bytes LB /\ (length LB' <= length LB)%nat
    /\ rw_cells asegs m' (Fa + 48) (HdrCells (hdr_cleared h))
    /\ xpres H LB' (bv_unsigned sp) [(Fa + 48, Fa + 80)]%Z m m'
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ accessible m' (Fa + 48) 32
    /\ as_AL H s' >= as_AL H s - bf_cost L em h.

Definition abfields_dtor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (Fa lo B shi : Z) (S L : list Z) (ns : NS) (ls : LS) (em : gmap Z elt)
         (h : hdrv) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_FIELDS_DTOR) fc None m (seg_rom asegs) ->
    a0 = wz Fa ->
    AFieldsC m Fa S L ns ls em -> AFieldsOwn LB em ->
    rw_cells asegs m (Fa + 48) (HdrCells h) -> HdrOwnA LB m h -> HdrDisjP em h ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ABFIELDS_DTOR_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
    bv_unsigned sp mod 16 = 0 ->
    (* [comment removed for export] *)
    aobj LB LF Fa 88 -> accessible m (Fa + 48) 32 ->
    (1 <= hv_ml h -> Fa + 80 <= hv_mp h \/ hv_mp h + hv_ml h <= Fa + 48) ->
    (1 <= hv_tl h -> Fa + 80 <= hv_tp h \/ hv_tp h + hv_tl h <= Fa + 48) ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    bf_cost L em h <= as_AL H s ->
    as_SR H (abfields_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF Fa lo B shi L em h errv m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ambuf_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (lo B shi : Z) (es : list mbe) (errv : word)
    (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' LB' m'
    /\ (forall b, In b LB' <-> (In b LB /\ ~ mbownedP es b))
    /\ lb_bytes LB' <= lb_bytes LB /\ (length LB' <= length LB)%nat
    /\ xpres H LB' (bv_unsigned sp) [] m m'
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - mb_cost es.

Definition ambuf_dtor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (b lo B shi : Z) (es : list mbe) (out insz outpos outend : Z)
         (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_MB_DTOR) fc None m (seg_rom asegs) ->
    a0 = wz b ->
    AMBraw m b es out insz outpos outend -> AMBufOwn LB es ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AMBUF_DTOR_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
    bv_unsigned sp mod 16 = 0 ->
    (* [comment removed for export] *)
    aobj LB LF b 64 -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    mb_cost es <= as_AL H s ->
    as_SR H (ambuf_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF lo B shi es errv m mo)
      (mkCfg msF mo).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AVP_BASIC_PARSER : Z := 0x116548.     (* [comment removed for export] *)
Definition APD_RA1 : Z := 0xa4c1c.   (* [comment removed for export] *)
Definition APD_RA2 : Z := 0xa4c24.   (* [comment removed for export] *)
Definition APARSER_DTOR_STACK : Z := 48 + ABFIELDS_DTOR_STACK.
Definition PARSER_SIZE_D : Z := 344.

(* [comment removed for export] *)
Definition apowned (em : gmap Z elt) (h : hdrv) (es : list mbe) (b : block) : Prop := abfowned em h b \/ mbownedP es b.

(* [comment removed for export] *)
Definition ParserCoreCellsD (c : pcore) (pad7 pad2 : list byte) : list cell :=
  C8 (wz AVP_BASIC_PARSER) :: tl (ParserCoreCells c pad7 pad2).

(* [comment removed for export] *)
Definition parser_dtor_X (P : Z) : list (Z * Z) := [(P, P + 8); (P + 40, P + 48); (P + 128, P + 160)]%Z.

Definition aparser_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (P lo B shi : Z) (c : pcore) (pad7 pad2 : list byte) (L : list Z) (em : gmap Z elt)
    (h : hdrv) (es : list mbe) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
  fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
    as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' LB' m'
    /\ (forall b, In b LB' <-> (In b LB /\ ~ apowned em h es b))
    /\ lb_bytes LB' <= lb_bytes LB /\ (length LB' <= length LB)%nat
    /\ rw_cells asegs m' P (ParserCoreCellsD c pad7 pad2)
    /\ rw_cells asegs m' (P + 128) (HdrCells (hdr_cleared h))
    /\ rw_cells asegs m' (P + 288) [C8 (wz 0)] /\ rw_cells asegs m' (P + 336) [C8 (wz 0)]
    /\ xpres H LB' (bv_unsigned sp) (parser_dtor_X P) m m'
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ accessible m' P PARSER_SIZE_D
    /\ as_AL H s' >= as_AL H s - (mb_cost es + bf_cost L em h).

Definition aparser_dtor_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (P lo B shi : Z) (c : pcore) (pad7 pad2 : list byte)
         (S L : list Z) (ns : NS) (ls : LS) (em : gmap Z elt) (h : hdrv)
         (es : list mbe) (out insz outpos outend : Z) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_PARSER_DTOR) fc None m (seg_rom asegs) ->
    a0 = wz P ->
    rw_cells asegs m P (ParserCoreCells c pad7 pad2) ->
    rw_cells asegs m (P + 288) [C8 (wz 0)] -> rw_cells asegs m (P + 336) [C8 (wz 0)] ->
    AFieldsC m (P + 80) S L ns ls em -> AFieldsOwn LB em ->
    rw_cells asegs m (P + 128) (HdrCells h) -> HdrOwnA LB m h -> HdrDisjP em h ->
    AMBraw m (P + 168) es out insz outpos outend -> AMBufOwn LB es -> BodyDisjP em h es ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - APARSER_DTOR_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = wz ATP ->
    bv_unsigned sp mod 16 = 0 ->
    (* [comment removed for export] *)
    aobj LB LF P PARSER_SIZE_D -> P mod 8 = 0 -> accessible m P PARSER_SIZE_D ->
    (1 <= hv_ml h -> P + PARSER_SIZE_D <= hv_mp h \/ hv_mp h + hv_ml h <= P) ->
    (1 <= hv_tl h -> P + PARSER_SIZE_D <= hv_tp h \/ hv_tp h + hv_tl h <= P) ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    mb_cost es + bf_cost L em h <= as_AL H s ->
    as_SR H (aparser_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF P lo B shi c pad7 pad2 L em h es errv m mo)
      (mkCfg msF mo).

End HCW.
