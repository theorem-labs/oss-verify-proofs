(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXRep AXRep2 AXPRep AXPRep2.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8Kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import X8SRKit.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ECCLEAR_STACK : Z := 16 + AINTRIN_STACK.

Definition ecclear_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (E, E + 24)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' E (ErrCodeCells EC_clear)
    /\ ACONST m'.

Definition ecclear_stmt (pc_entry : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (E lo : Z) (ej : list byte),
  rw_cells bsegs m E [CB 24 ej] ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ECCLEAR_STACK <= bv_unsigned sp -> aceil <= lo ->
  aapp E 24 ->
  mem_inv bsegs m ->
  ACONST m -> accessible m E 24 -> shvis m E (E + 24) ->
  evt bsegs (ecclear_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc E lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz E) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc_entry) fc None m (seg_rom bsegs)).

Definition on_header_impl_stmt : Prop := ecclear_stmt P_A_ON_HEADER_IMPL.
Definition on_finish_impl_stmt : Prop := ecclear_stmt P_A_ON_FINISH_IMPL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cl_cells (c : pcore) (rj : list byte) : list cell :=
  if Z.testbit (pc_f c) 10
  then [C1 (b8 1); CB 7 (skipn 1 (firstn 8 rj)); C8 (wz (pc_len0 c))]
  else [C1 (b8 0); CB 7 (skipn 1 (firstn 8 rj)); C1 (b8 0); CB 7 (skipn 9 rj)].

Definition ACL_STACK : Z := 16.

Definition cl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P R lo : Z) (c : pcore) (pad7 pad2 rj : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (R, R + 16)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' P (ParserCoreCells c pad7 pad2)
    /\ rw_cells bsegs m' R (cl_cells c rj)
    /\ ACONST m'.

Definition cl_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P R lo : Z) (c : pcore) (pad7 pad2 rj : list byte),
  rw_cells bsegs m P (ParserCoreCells c pad7 pad2) -> pcore_ok c -> 3 <= pc_state c ->
  rw_cells bsegs m R [CB 16 rj] -> (P + 80 <= R \/ R + 16 <= P) ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ACL_STACK <= bv_unsigned sp -> aceil <= lo ->
  (P + 80 <= lo \/ bv_unsigned sp <= P) -> (R + 16 <= lo \/ bv_unsigned sp <= R) ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> accessible m P 80 -> P mod 8 = 0 -> accessible m R 16 -> R mod 8 = 0 -> awin (R, R + 16) ->
  0 < R ->                                      (* [comment removed for export] *)
  evt bsegs (cl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P R lo c pad7 pad2 rj m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz R) (wz P) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_BP_CONTENT_LENGTH) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_pure (B : Z) (sp : word) (P E lo shi : Z) : Prop :=
  lo + B <= bv_unsigned sp /\ aceil <= lo
  /\ aapp P 80 /\ P mod 8 = 0 /\ aapp E 24 /\ E mod 8 = 0
  /\ (P + 80 <= E \/ E + 24 <= P)
  /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp + 64 <= shi.

(* [comment removed for export] *)
Definition stin_pure (B : Z) (sp : word) (P IN E lo shi : Z) : Prop :=
  st_pure B sp P E lo shi
  /\ bv_unsigned sp <= IN /\ IN + 8 <= shi /\ IN mod 8 = 0.

(* [comment removed for export] *)
Definition body_W (lo : Z) (sp : word) (P E : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (P, P + 80); (E, E + 24); (AG_HTTP_CAT, AG_HTTP_CAT + 64)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition peof_body_flags (c : pcore) : bool := Z.testbit (pc_f c) 10 || Z.testbit (pc_f c) 11.

(* [comment removed for export] *)
Definition peof_assigns (c : pcore) : bool :=
  (pc_state c <=? 2) || (peof_body_flags c && negb (pc_state c =? 11)).

Definition peof_res (c : pcore) : ecv * pcore :=
  if pc_state c <=? 2 then (EC_http_loc HE_PARTIAL_MESSAGE ALOC_PEOF_1, c)
  else if peof_body_flags c then
         (if pc_state c =? 11 then (EC_clear, c) else (EC_http_loc HE_PARTIAL_MESSAGE ALOC_PEOF_2, c))
  else (EC_clear, pc_set_state c 11).

Definition PEOF_STACK : Z := 64 + AASSIGN_STACK.

Definition peof_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P E lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (g : bool) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (body_W lo sp P E) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' P (ParserCoreCells (snd (peof_res c)) pad7 pad2)
    /\ rw_cells bsegs m' E (ErrCodeCells (fst (peof_res c)))
    /\ AHttpCat m' (peof_assigns c || g) /\ AXStatics2 m'
    /\ ACONST m' /\ stack0 m' lo shi.

Definition peof_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P E lo shi : Z) (c : pcore) (pad7 pad2 ej : list byte) (g : bool),
  rw_cells bsegs m P (ParserCoreCells c pad7 pad2) -> pcore_ok c -> pc_state c <> 0 ->
  rw_cells bsegs m E [CB 24 ej] ->
  AHttpCat m g -> AXStatics2 m ->
  stk bsegs m lo (bv_unsigned sp) ->
  st_pure PEOF_STACK sp P E lo shi ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi -> accessible m P 80 -> accessible m E 24 -> shvis m E (E + 24) ->
  evt bsegs (peof_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P E lo shi c pad7 pad2 g m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz E) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_BP_PUT_EOF) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition APB_RET : Z := 0xd23f0.
Definition PB_STACK : Z := 80 + AINTRIN_STACK.

(* [comment removed for export] *)
Definition shw (a : Z) : word := Z_to_bv 64 (Z.shiftr a 3 + 2147450880).

Definition pb_frame (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition pb_seg1_post (sp : word) (gp tp s8 s9 s10 s11 : word) (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (P IN E n p0 lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 j8 m',
    ms' = MS (mkR (wz APB_RET) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (wz E) (wz P)
                  (wz P) (wz p0) (wz (Z.min (pc_len c) n)) (wz E) (wz P_A_ON_BODY_IMPL) a5 a6 a7
                  (wz IN) (wz (P + 24)) (shw P) (wz 2147450880) (shw IN) (shw (P + 24)) s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz P_A_ON_BODY_IMPL) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (E, E + 24)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells bsegs m' (bv_unsigned sp + -80) (CB 8 j8 :: pb_frame s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ rw_cells bsegs m' P (ParserCoreCells c pad7 pad2)
    /\ rw_cells bsegs m' IN [C8 (wz p0)]
    /\ rw_cells bsegs m' E (ErrCodeCells EC_clear)
    /\ AXStatics2 m'
    /\ ACONST m' /\ stack0 m' lo shi.

Definition pb_seg1_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P IN E n p0 lo shi : Z) (c : pcore) (pad7 pad2 ej : list byte),
  rw_cells bsegs m P (ParserCoreCells c pad7 pad2) -> pcore_ok c ->
  rw_cells bsegs m IN [C8 (wz p0)] ->
  rw_cells bsegs m E [CB 24 ej] ->
  AXStatics2 m ->
  stk bsegs m lo (bv_unsigned sp) ->
  stin_pure PB_STACK sp P IN E lo shi ->
  0 <= n < 2^64 -> 0 <= p0 < 2^64 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi -> accessible m P 80 -> accessible m E 24 -> shvis m E (E + 24) ->
  evt bsegs (pb_seg1_post sp gp tp s8 s9 s10 s11 s7 s6 s5 s4 s3 s2 s1 s0 ra F fc P IN E n p0 lo shi c pad7 pad2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz IN) (wz n) (wz E) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_BP_PARSE_BODY) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pb_done (E1 : ecv) (c : pcore) (r : Z) : bool := negb (ec_failed E1) && (pc_len c =? r).

Definition pb_core (E1 : ecv) (c : pcore) (r : Z) : pcore :=
  mkPC (pc_blim_has c) (pc_blim c) (pc_len c - r) (pc_len0 c) (pc_skip c) (pc_hlim c)
       (if pb_done E1 c r then 11 else pc_state c) (pc_f c).

Definition pb_ec (E1 : ecv) (c : pcore) (r : Z) : ecv := if pb_done E1 c r then EC_clear else E1.

Definition pb_seg2_post (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P IN E lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (p0 r : Z) (E1 : ecv) (g : bool) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (P, P + 80); (IN, IN + 8); (E, E + 24)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' P (ParserCoreCells (pb_core E1 c r) pad7 pad2)
    /\ rw_cells bsegs m' IN [C8 (wz (p0 + r))]
    /\ rw_cells bsegs m' E (ErrCodeCells (pb_ec E1 c r))
    /\ AHttpCat m' g /\ AXStatics2 m'
    /\ ACONST m' /\ stack0 m' lo shi.

Definition pb_seg2_stmt : Prop :=
  forall rax rav sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s0v s1v s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P IN E lo shi : Z) (c : pcore) (pad7 pad2 j8 : list byte) (p0 r : Z) (E1 : ecv) (g : bool),
  rw_cells bsegs m (bv_unsigned sp + -80) (CB 8 j8 :: pb_frame s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  rw_cells bsegs m P (ParserCoreCells c pad7 pad2) -> pcore_ok c ->
  rw_cells bsegs m IN [C8 (wz p0)] ->
  rw_cells bsegs m E (ErrCodeCells E1) -> ec_ok E1 ->
  AHttpCat m g -> AXStatics2 m ->
  stk bsegs m lo (bv_unsigned sp + -80) ->
  stin_pure PB_STACK sp P IN E lo shi ->
  0 <= r <= pc_len c -> 0 <= p0 -> p0 + r < 2^64 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi -> accessible m P 80 -> accessible m E 24 -> shvis m E (E + 24) ->
  0 < p0 ->                                     (* [comment removed for export] *)
  evt bsegs (pb_seg2_post rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8 s9 s10 s11 F fc P IN E lo shi c pad7 pad2 p0 r E1 g m)
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (wz E) (wz P) (wz r) a1 a2 a3 a4 a5 a6 a7
              (wz IN) (wz (P + 24)) (shw P) (wz 2147450880) (shw IN) (shw (P + 24)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APB_RET) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fh_res (c : pcore) : ecv * pcore :=
  let f := pc_f c in
  if Z.testbit f 11 && negb (Z.testbit f 4) then (EC_http_loc HE_BAD_TRANSFER_ENCODING ALOC_FH_TE1, c)
  else if Z.testbit f 13 && negb (Z.testbit f 11) then (EC_http_loc HE_BAD_TRANSFER_ENCODING ALOC_FH_TE2, c)
  else if Z.testbit f 0 then (EC_clear, pc_set_state c 11)
  else if Z.testbit f 10 then
    (if negb (pc_blim_has c =? 0) && (pc_blim c <? pc_len c) then (EC_http_loc HE_BODY_LIMIT ALOC_FH_BODYLIM, c)
     else if pc_len c =? 0 then (EC_clear, pc_set_state c 11)
     else (EC_clear, pc_set_state_f c 3 (Z.lor f 8)))
  else if Z.testbit f 11 then (EC_clear, pc_set_state_f c 7 (Z.lor f 8))
  else (EC_clear, mkPC (pc_blim_has c) (pc_blim c) 0 0 (pc_skip c) (pc_hlim c) 11 f).

(* [comment removed for export] *)
Definition fh_assigns (c : pcore) : bool := negb (ec_cat (fst (fh_res c)) =? 0).
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.
Scheme kc__2 := Elimination for Corelib.Init.Datatypes.bool Sort Prop.

Lemma fh_res_ok : forall c, pcore_ok c -> pcore_ok (snd (fh_res c)).
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pcore); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pcore_ok); constr:(@kc__1); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_blim_has); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_blim); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_len); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_len0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_skip); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_hlim); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_state); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_f); constr:(@Corelib.Init.Datatypes.snd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.ecv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_state1_stmt.HCW.fh_res); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep2.lor8_f14); constr:(@Stdlib.ZArith.BinInt.Z.lor); constr:(@Corelib.Init.Datatypes.andb); constr:(@Stdlib.ZArith.BinInt.Z.testbit); constr:(@Corelib.Init.Datatypes.negb); constr:(@Corelib.Init.Datatypes.bool); constr:(@kc__2); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Init.Datatypes.pair); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.EC_http_loc); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.HE_BAD_TRANSFER_ENCODING); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.ALOC_FH_TE1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.ALOC_FH_TE2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.EC_clear); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep2.pc_set_state); constr:(@Stdlib.ZArith.BinInt.Z.eqb); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.HE_BODY_LIMIT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.ALOC_FH_BODYLIM); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep2.pc_set_state_f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.mkPC); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.Tauto.X); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.RingMicromega.OpEq)|] [|@b; @Ha; @__ff; @__varmap; @__wit; @__x1; @__p1; @__arith; @__sat14; @__sat12; @__sat10; @__sat9; @__sat11; @__sat13; @F8; @Ff; @Stt; @H0; @Hl; @Sk; @Ln0; @Ln; @Bl; @Bh; @c|] "#7:#R$J#\#Z$:$;$9#U#p#w##$B$O#$$##C#B#F#D#%#3#G#/#R#E#'#0#(#)#+#,#1#2#4$,#-#7$.#.#;#>#^#*#5#6#8#:#?#&#9#<#H#m#=#@#A#|$0$3$@$C$<$7$G$L$K$J#r#y#}#~$'$($2$1$4$5$6$8$A$D$E$H$I$F#L#M$M#N#P#Q#_#`#f#X#Y$+#n$>$=#V#z$N#i#k#j#h#o#g#e#a#c#]#u#[$)#l$?#s$%#q#d#v#t#x#W$$$*$&#b#{$-$/N#|%#}%#~%$#%$$&$%'$&$$''$(*$)$$*'$+*$,$$-$$.&$/$$0&$1$$2$$3$$4$$5$$6%#+&$7$$8&$9&$:%$;%$<%$=$$>$$?$$@%$A'$B($C%$D+$E%$F%$G%$H%$I&,K;N'D#C8S:'D%#&%#6N$C#7S:8#B$7#7#8#J'#$+##+#5N$C#7-7#7#7#7#8#J2#%+##+#4N$C#%$'#$#2N$C#%$+#$#/N$C#717#7#7#7#B#7#8#$,##,#0NBS:8#8BB%8#8s#$Bs#&8#8s#0Bs#28#USED=D$#=D'#=D)#=D,#=D.#=D1#=D3#=Ds#=#=Ds#D#=DC#1D9#)N$C#788#Js#E#%'##'##*##s####s#0##s#5##s#:##s#F##s#R#AS$3IH#,#j##&#6S$$C#$$s#P#$#5S$$C#%$s#I#$#4S$$C#%$s#M#$#2S$$C#%$s#Q#$#/S$$C#$$s#A#$#0S$1D#s#+)S$$C#%$s#(#$##'##*##/##4##9##>#;SA'D#C'D$s#{&$#6S*$C#$$s#t#$#5S*$C#%$s#m#$#4S*$C#%$s#q#$#2S*$C#%$s#u#$#/S*$C#$$s#e#$#0S*1D#s#O)S*$C#%$s#L#$##'##*##/##4##9##>#6S,$C#$$s$8#$#5S,$C#%$s$1#$#4S,$C#%$s$5#$#2S,$C#%$s$9#$#/S,$C#$$s$)#$#0S,1D#s#o)S,$C#%$s#l#$##'##*##/##4##9##>#AS-3IH#,#j##&#5S-$C#%$s$Q#$#4S-$C#%$s$U#$#2S-$C#%$s$Y#$#/S-$C#$$s$I#$#0S-1D#s$3)S-$C#%$s$0#$##'##*##/##4##9#6S;$C#$$s$w#$#5S.$C#%$s$p#$#4S.$C#%$s$t#$#2S.$C#%$s$x#$#/S.$C#$$s$h#$#0S.1D#s$R)S.$C#%$s$O#$##'##*##/##4##9#5S/$C#%$s%/#$#4S/$C#%$s%3#$#2S/$C#%$s%7#$#/S/$C#$$s%'#$#0S/1D#s$m)S/$C#%$s$j#$##'##*##/##4##9#AS43IH#,#j##&#4S4$C#%$s%N#$#2S4$C#%$s%R#$#/S4$C#$$s%B#$#0S41D#s%,)S4$C#%$s%)#$##'##*##/##4#5S7$C#%$s%d#$#4S'$C#%$s%h#$#2S'$C#%$s%l#$#/S'$C#$$s%\#$#0S'1D#s%F)S'$C#%$s%C#$##'##*##/##4#4S+$C#%$s%~#$#2S+$C#%$s&&#$#/S+$C#$$s%r#$#0S+1D#s%\)S+$C#%$s%Y#$##'##*##/##4#AS03IH#,#j##&#2S0$C#%$s&<#$#/S0$C#$$s&,#$#0S01D#s%r)S0$C#%$s%o#$##'##*##/#4S1$C#%$s&M#$#2S%$C#%$s&Q#$#/S%$C#$$s&A#$#0S%1D#s&+)S%$C#%$s&(#$##'##*##/#2S2$C#%$s&b#$#/S2$C#$$s&R#$#0S21D#s&<)S2$C#%$s&9#$##'##*##/#AS<3IH#,#j##&#/S<$C#$$s&c#$#0S<1D#s&M)S<$C#%$s&J#$##'##*#2S=$C#%$s''#$#/S5$C#$$s&s#$#0S51D#s&])S5$C#%$s&Z#$##'##*#/S>$C#$$s'##$#0S>1D#s&i)S>$C#%$s&f#$##'##*#ASB3IH#,#j##&#0SB1D#s&u)SB$C#%$s&r#$##'#/S?$C#$$s':#$#0S81D#s'$)S8$C#%$s&}#$##'#0SC1D#s'+)SC$C#%$s'(#$##'#ASF3IH#,#j##&#)SF$C#%$s'1#$#0S91D#s':)S@$C#%$s'7#$#)SGVST#K?$s'Q$C#%$s'=#$#)SH9#s'Q9$s'ZC#D%#VSUIHKSISV-IH#P)P7s'cB#8#9&#9's']C#D%#KSISW-IH#P9,CGPs'c-IHO#9/s'g;P@#CC#6P5PI$#D&#KSXSY-IH#P@'C?:s'u<Ps'z#-IHO#nJ#$##@&#%#1##nJ#$##A*#%#(##<Ps'{'-IHO#2P/PH52CC$#s'ys##-IHO#nJ#$##s#(@#%#'##nJ#$##s#)9#%#*##nJ#$##s#*=#%#;##nJ#$##s#+A#%#?##nJ#$##s#,K#%#s#*##3IH#,#j#$J#;Q'D#C'D$s(a&$#6Q$C#$$s(Z#$#5Q$C#%$s(S#$#4Q$C#%$s(W#$#2Q$C#%$s([#$#/Q$C#$$s(K#$#0Q'DC#'Ds(y$'Ds(t%'Ds(L&'Ds(L''Ds(K('Ds(K)'Ds(J*'Ds(J+'Ds(I,&#S3&%#&'#&)#&+#&-#&/#&1#&3#&5#)Q$C#%$s(E#$##'##=##B##s#'##s#,##s#1#Ls)4s(N%Cs)5$Cs(P%Cs(Pk##$#k##&#$Cs):Ms);s(UNj##S6#j#%%#$Cs(Wk##S6#k#%(#Ls)As)=$Cs)>%Cs)>k##$#k##2#Ms)Fs)BNj##S6#j#%0#$Cs)Dk##S6#k#%3#Ls)Ls)=$Cs)>%Cs)>k##$#k##=#Ms)Qs)BNj##S6#j#%;#$Cs)Dk##S6#k#%>#VSZCs)WVSJS[#m##s#&UN#US*$US;%USESKUS\SKVS]DNUS^DUS_D>DCVS`DS:*D$SL#+&GEEF#LZSM'GEEFSA[SN(GEEF$#USaE\SO*GEEF$#&VSb+FVSJJSPVScKS$'J#SPm$%#WSdDCNXSeKS$$#l#&*)#l#'54#l#(87#j#)D#j#*S(#$CK##N$CNk##$#k#)D#k#*S(#)Sf%#s)::#$S'l#+,&#l#,s#&s#J#l#-s#(s#?#l#.s#*s#5#l#/s#2s#/#l#.s#:s#6#l#0s#?s#<#l#-s#Gs#C#l#1s#Ls#I#l#,s#Vs#Q#m##s#`>Ds*.USQs)JWSRD$#*Ds#,SS#+s#/GEEF#L[SNs#0GEEFs#+#\SOs#1GEEF#s#*$l#&#s#)s##l#'s#5s#4#l#(s#8s#7#j#)D#j#*S(#%Ks)S#N#%Ns)Uk##$#k#)D#k#*S(#$CB:#s##S'l#++%#l#,s#Es#i#l#-s#Gs#^#l#.s#Is#T#l#/s#Qs#N#l#.s#Ys#U#l#0s#^s#[#l#-s#fs#b#l#1s#ks#h#l#,s#us#p#m##s#~(s$$s$#B#(s$'s$#SA#(s$=s$#S;#(s$Bs$#S7#(s$Gs$#S1#(s$Ls$#S=#(s$Qs$#S?#(s$Vs$#S9#1Ds$Bs)t##s$+#s$E##s$J##s$O##s$T##s$Y##s$^#m#+#,Qm#$#-IHs%6Q3IH#,#m#&#9s$<s%59s$=s*3C#D%#-IHs%4S#)S#9#CGS#s*9-IHO#9&s*=;S#@#CC#6S#5S#I$#D&#-IHs%4S#@&C?0s*J<S#s*O#-IHO#nJ#$##s%Q&#%#0##nJ#$##s%R)#%#(##95s*J<S#s*Q(-IHO#2S#/S#H52CC$#s*O:-IHO#nJ#$##s%Z)#%#'##nJ#$##s%[9#%#+##nJ#$##s%\=#%#;##nJ#$##s%]K#%#@##3IH#,#j#$J#'Ds%PC'Ds%Qs+5&$#$Cs%P$s%Qs+-#$#$Cs%R%s%Ss+%#$#4P$C#%$s+)#$#$Cs%L%s%Ms+,#$#$Cs%N$s%Os*w#$#0P'DC#'Ds+I$'Ds+D%'Ds*x&'Ds*x''Ds*w('Ds*w)'Ds*v*'Ds*v+'Ds*u,&#S3&%#&'#&)#&+#&-#&/#&1#&3#&5#$Cs&*%s&+s*p#$##&##<##@##s#$##s#)##s#-#)Sg%#s*y:#$S+l#+s$Ks$E#l#,s$es%-#l#-s$gs$~#l#.s$is$t#l#/s$qs$n#l#.s$ys$u#l#0s$~s${#l#-s%*s%&#l#1s%/s%,#l#,s%9s%4#m##8$C0:#1S+l#+s$8s$2#l#,s$rs%:#l#-s$ts%/#l#.s$vs%%#l#/s$~s${#l#.s%*s%&#l#0s%/s%,#l#-s%7s%3#l#1s%<s%9#l#,s%Fs%A#m##s#$(s#&s#%0#(s#(s#%S*#(s#>s#%S.#(s#Bs#%S'#(s#Fs#%S%#(s#Ks#%S5#(s#Os#%S8#(s#Ss#%S@#1Ds#Cs+E##s#-#s#F##s#J##s#N##s#S##s#W##s#[#m#+#,Pm#$#3IHs&X,#m#%#GS)s+^-IHO#)S)9#s+c;S)@#CC#6S)5S)I$#D&#-IHs&ZS)@&C?-s+p<S)s+u#-IHO#nJ#$##s&w&#%#1##nJ#$##s&x)#%#(##92s+p<S)s+w(-IHO#2S)/S)H52CC$#s+u7-IHO#nJ#$##s'$)#%#'##nJ#$##s'%9#%#+##nJ#$##s'&K#%#<##3IH#,#j#$J#'Ds$CC'Ds$Ds,Z&$#$Cs$C$s$Ds,R#$#$Cs$E%s$Fs,J#$#4S#$C#%$s,N#$#$Cs$?%s$@s,Q#$#$Cs$A$s$Bs,@#$#'DCs,4'Ds,ms,5'Ds,hs,6'Ds,@s,7'Ds,@s,8'Ds,?s,9'Ds,?s,:'Ds,>s,;'Ds,>s,<'Ds,=s,=&#S3&%#&'#&)#&+#&-#&/#&1#&3#&5#$Cs$o%s$ps,8#$##&##;##?##s####s#(##s#,#UShD>Ds,R*Ds&%M#+s&'GEEF#L>Ds-1*D#M&+s&*GEEF#L*Ds%^M(+s&,GEEF#L>Ds,c*D#M++s&/GEEF#L>Ds,e*D#M.+s&2GEEF#L>Ds,f*D#M1+s&5GEEF#L>Ds,h*D#M4+s&8GEEF#L>Ds,i*D#M7+s&;GEEF#L>Ds,k*D#M:+s&>GEEF#L*D<M<+s&@GEEF#LZSMs&AGEEFS$.s&BGEEF$#.s&CGEEF'#.s&DGEEF+#.s&EGEEF/#.s&FGEEF3#.s&GGEEF7#.s&HGEEF;#.s&IGEEF?#.s&JGEEFB#.s&KGEEFs#&#l#&#s&Cs&=l#'s#+s&N#l#(s&Rs&Q#j#*S(#&s#BK&s#D#&s#F#&s#H#&s#J#&s#L#&s#N#&s#P#&s#R#&s#T#k#*S(#UKS3l#+/$#l#,s&bs'*#l#-s&ds&{#l#.s&fs&q#l#/s&ns&k#l#.s&vs&r#l#0s&{s&x#l#-s''s'##l#1s',s')#l#,s'6s'1#m##s#N)Si%#s-(:#$S0l#+s&Vs&P#l#,s&ps'8#l#-s&rs'-#l#.s&ts'##l#/s&|s&y#l#.s'(s'$#l#0s'-s'*#l#-s'5s'1#l#1s':s'7#l#,s'Ds'?#m##s#[$C0:#1S0l#+s&Cs&=#l#,s&}s'E#l#-s'#s':#l#.s'%s'0#l#/s'-s'*#l#.s'5s'1#l#0s':s'7#l#-s'Bs'>#l#1s'Gs'D#l#,s'Qs'L#m##s#g(s#is#h0#(s#ks#h?#(s$$s#hS/#(s$(s#hS+#(s$,s#hS2#(s$1s#hS>#(s$5s#hSC#(s$9s#hSG#;s&$'D#C'D$s.9&$#6s&($C#$$s.2#$#5s&,$C#%$s.+#$#4s&0$C#%$s./#$#2s&4$C#%$s.3#$#/s&8$C#$$s.##$#0s&<1D#s-i)s&>$C#%$s-f#$##'##*##/##4##9##>##s###m#s#(#,s&Jm#$#3IHs&K,#m#%#;R@#CC#6R5RI$#D&#-IHs(~R@&CGRs.3-IHO#)R?#s.;<Rs.@#-IHO#nJ#$##s)B)#%#'##nJ#$##s)C,#%#+##9(s.;<Rs.B(-IHO#2R/RH85CC$#s.@--IHO#nJ#$##s)K)#%#'##nJ#$##s)LK#%#+##3IH#,#j#$J#-IHs)8S&5S&@#CGS&s.J-IHO#)S&?#s.R<S&s.W#-IHO#nJ#$##s)Y)#%#'##nJ#$##s)ZK#%#,##3IH#,#j#$J#'Ds#-C'Ds#.s/2&$#$Cs#-$s#.s/*#$#$Cs#/%s#0s.~#$#4R$C#%$s/&#$#$Cs#&%s#'s/)#$#$Cs#($s#)s.t#$#0R'DC#'Ds/F$'Ds/A%'Ds.u&'Ds.u''Ds.t('Ds.t)'Ds.s*'Ds.s+'Ds.r,&#S3&%#&'#&)#&+#&-#&/#&1#&3#&5#$Cs#J%s#Ks.m#$##&##<##@##s#$##s#)##s#-#)Sj%#s.v:#$S%l#+s(Hs(B#l#,s(bs)*#l#-s(ds({#l#.s(fs(q#l#/s(ns(k#l#.s(vs(r#l#0s({s(x#l#-s)'s)##l#1s),s))#l#,s)6s)1#m##8$C0:#1S%l#+s(5s(/#l#,s(os)7#l#-s(qs),#l#.s(ss(~#l#/s({s(x#l#.s)'s)##l#0s),s))#l#-s)4s)0#l#1s)9s)6#l#,s)Cs)>#m##s#$(s#&s#%0#(s#(s#%S;#(s#>s#%S7#(s#Bs#%S1#(s#Fs#%S=#(s#Ks#%S?#(s#Os#%S9#(s#Ss#%Q#1Ds#Cs/B##s#-#s#F##s#J##s#N##s#S##s#W##s#[#m#+#,Rm#$#3IHs$),#m#%#GSDs/[-IHO#)SD?#s/c<SDs/h#-IHO#nJ#$##s*jK#%#'##3IH#,#j#$J#;S&'D#C'D$s0C&$#6S&$C#$$s0<#$#$Cs$'%s$(s04#$#4S&$C#%$s08#$#2S&$C#%$s0<#$#/S&$C#$$s0,#$#$Cs$2%s$3s/l#$##s&:##'##,##1##6##:#)Sk%#s/u:#$S2l#+s)Gs)A#l#,s)as*)#l#-s)cs)z#l#.s)es)p#l#/s)ms)j#l#.s)us)q#l#0s)zs)w#l#-s*&s)~#l#1s*+s*(#l#,s*5s*0#m##8$C0:#1S2l#+s)4s).#l#,s)ns*6#l#-s)ps*+#l#.s)rs)}#l#/s)zs)w#l#.s*&s)~#l#0s*+s*(#l#-s*3s*/#l#1s*8s*5#l#,s*Bs*=#m##s#$(s#&s#%0#(s&\s#%s%l#(s#)s#%S'#(s#.s#%S%#(s#3s#%S5#(s#8s#%S8#(s#<s#%S@#(s#As#%P#;s$`'D#C'D$s1*&$#6s$d$C#$$s1##$#5s$h$C#%$s0x#$#4s$l$C#%$s0|#$#2s$p$C#%$s1$#$#/s$t$C#$$s0p#$#0s$x1D#s0Z)s$z$C#%$s0W#$##'##*##/##4##9##>##s###m#s#(#,s%*m#$#3IHs%+,#m#%#'DCs1$'Ds1Ts1%'Ds1Os1&'Ds1's1''Ds1's1('Ds1&s1)'Ds1&s1*'Ds1%s1+'Ds1%s1,'Ds1$s1-&#S3&%#&'#&)#&+#&-#&/#&1#&3#&5#$Cs%@%s%As0{#$##&##s#r##s#w##s#|##s$%##s$)#*Ds*fMs'<+s*hGEEF#L*Ds'CMs'>+s*jGEEF#L*Ds*BMs'@+s*lGEEF#L*Ds'BMs'B+s*nGEEF#L*Ds'AMs'D+s*pGEEF#L*Ds'@Ms'F+s*rGEEF#L*Ds'?Ms'H+s*tGEEF#L*Ds'>Ms'J+s*vGEEF#L*Ds'=Ms'L+s*xGEEF#L*Ds'VMs'N+s*zGEEF#L.s*{GEEF#s'<.s*|GEEF&#.s*}GEEF)#.s*~GEEF,#.s+#GEEF/#.s+$GEEF2#.s+%GEEF5#.s+&GEEF8#.s+'GEEF;#.s+(GEEF>#l#&#s*|s*vl#'s'ds++#l#(s+/s+.#j#*S(#&s#8K&s#:#&s#<#&s#>#&s#@#&s#B#&s#D#&s#F#&s#H#&s#J#k#*S(#l#+.#s';l#,s+>s+b#l#-s+@s+W#l#.s+Bs+M#l#/s+Js+G#l#.s+Rs+N#l#0s+Ws+T#l#-s+_s+[#l#1s+ds+a#l#,s+ns+i#m##s#C?s$Is1u%#s1`:#$S%l#+s+2s+,#l#,s+Ls+p#l#-s+Ns+e#l#.s+Ps+[#l#/s+Xs+U#l#.s+`s+\#l#0s+es+b#l#-s+ms+i#l#1s+rs+o#l#,s+|s+w#m##s#P$C0:#1S%l#+s*{s*u#l#,s+Ys+}#l#-s+[s+r#l#.s+]s+h#l#/s+es+b#l#.s+ms+i#l#0s+rs+o#l#-s+zs+v#l#1s,#s+|#l#,s,-s,(#m##s#\(s#^s#]0#(s#`s#]?#(s$ps#]S'#(s$us#]S%#(s$zs#]S5#(s%#s#]S8#(s%'s#]S@#(s%,s#]P#;s&G'D#C'D$s2q&$#6s&K$C#$$s2j#$#5s&O$C#%$s2c#$#4s&S$C#%$s2g#$#2s&W$C#%$s2k#$#/s&[$C#$$s2[#$#0s&_1D#s2E)s&a$C#%$s2B#$##'##*##/##4##9##>##s###m#s#(#,s&mm#$#3IHs&n,#m#%#Es%\s$J#Kl#$s'3J#Es&ns%h#Kl#$s)[J#<S&s2ls&w-IHO#Hs%as%]CCs%Rs%Ns2hs&z-IHO#nJ#$##s-sK#%#%##3IH#,#j#$J#'DCs2t'Ds3Ks2u'Ds3Fs2v'Ds2zs2w'Ds2zs2x'Ds2ys2y'Ds2ys2z'Ds2xs2{'Ds2xs2|'Ds2ws2}&#S3&%#&'#&)#&+#&-#&/#&1#&3#&5#$Cs'N%s'Os2r#$##&##s&}##s'%##s')##s'.##s'2#*Ds,]Ms)-+s,_GEEF#L*Ds):Ms)/+s,aGEEF#L*Ds,9Ms)1+s,cGEEF#L*Ds)9Ms)3+s,eGEEF#L*Ds)8Ms)5+s,gGEEF#L*Ds)7Ms)7+s,iGEEF#L*Ds)6Ms)9+s,kGEEF#L*Ds)5Ms);+s,mGEEF#L*Ds)4Ms)=+s,oGEEF#L*Ds)MMs)?+s,qGEEF#L.s,rGEEF#s)3.s,sGEEF&#.s,tGEEF)#.s,uGEEF,#.s,vGEEF/#.s,wGEEF2#.s,xGEEF5#.s,yGEEF8#.s,zGEEF;#.s,{GEEF>#l#&#s,ss,ml#'s)[s,~#l#(s-&s-%#j#*S(#&s#8K&s#:#&s#<#&s#>#&s#@#&s#B#&s#D#&s#F#&s#H#&s#J#k#*S(#l#+.#s)2l#,s-5s-Y#l#-s-7s-N#l#.s-9s-D#l#/s-As->#l#.s-Is-E#l#0s-Ns-K#l#-s-Vs-R#l#1s-[s-X#l#,s-es-`#m##s#C?s'?s3l%#s3W:#$S1l#+s-)s-##l#,s-Cs-g#l#-s-Es-\#l#.s-Gs-R#l#/s-Os-L#l#.s-Ws-S#l#0s-\s-Y#l#-s-ds-`#l#1s-is-f#l#,s-ss-n#m##s#P$C0:#1S1l#+s,rs,l#l#,s-Ps-t#l#-s-Rs-i#l#.s-Ts-_#l#/s-\s-Y#l#.s-ds-`#l#0s-is-f#l#-s-qs-m#l#1s-vs-s#l#,s.$s-{#m##s#\(s#^s#]0#(s#`s#]?#(s'{s#]S7#(s(#s#]S1#(s('s#]S=#(s(,s#]S?#(s(0s#]S9#(s(4s#]Q#;s(P'D#C'D$s4h&$#6s(T$C#$$s4a#$#5s(X$C#%$s4Z#$#4s(\$C#%$s4^#$#2s(`$C#%$s4b#$#/s(d$C#$$s4R#$#0s(h1D#s4<)s(j$C#%$s49#$##'##*##/##4##9##>##s###m#s#(#,s(vm#$#3IHs(w,#m#%#$CC##s.@#s*rs(:#s(S##s(W##&##'##s(d#*Ds.3SLs.3+s.5GEEF#Ll#&#s.-s.'l#'s*qs.8#l#(s.<s.;#l#+#/Kl#,s.?s.c#l#-s.As.X#l#.s.Cs.N#l#/s.Ks.H#l#.s.Ss.O#l#0s.Xs.U#l#-s.`s.\#l#1s.es.b#l#,s.os.j#m##9USQs59WSRDs-x#*Ds.ESS#+s.GGEEF#Ll#&#s.?s.9l#'s+'s.J#l#(s.Ns.M#l#+#s.^Kl#,s.Qs.u#l#-s.Ss.j#l#.s.Us.`#l#/s.]s.Z#l#.s.es.a#l#0s.js.g#l#-s.rs.n#l#1s.ws.t#l#,s/%s.|#m##s.h(s#,s.i5#m##s#,(s+@s(ds*Ps(B(s(}s#-S7#(s)%s#-S1#(s#0s#-&#(s#1s#-'#(s)2s#-S9#(s)6s#-Q#;s)N'D#C'D$s5j&$#6s)R$C#$$s5c#$#5s)V$C#%$s5\#$#4s)Z$C#%$s5`#$#2s)^$C#%$s5d#$#/s)b$C#$$s5T#$#0s)f1D#s5>)s)h$C#%$s5;#$##'##*##/##4##9##>##s###m#s#(#,s)tm#$#3IHs)u,#m#%#Es%Ls#a#Kl#$s,JJ#Es)us%V#Kl#$s.%J#Es,As*8#Kl#$s0\J#Es-hs,b#Kl#$s./J#Es0?s.4#Kl#$s0nJ#ASH3IH#,#m#&#l#2s0|s0x#j#3s1##j#4s1(#V#NKj##s1,#j##s1:#Fs1;s17s12#Kj#5s1>#j#6s1F#V#NKj##s1L#j##s1`#Fs1as1Zs1U#Kj#5s1f#j#7s1s#V#NKj##s1y#j##s2;#Fs2<s20s2+#Kj#5s2A#j#8s2S#V#NKj##s2Y#j##s3%#Fs3&s2qs2l#Kj#5s3+#j#9s3B#V#NKj##s3H#j##s3z#Fs3{s3es3`#Kj#5s4$#j#:s4@#V#NKj##s4F#j##s5&#Fs5's4hs4c#Kj#5s5,#j#;s5M#V#NKj##s5S#j##s6l#Fs6ms5zs5u#Kj#5s6s#j#<H##"). Qed.

Definition FH_STACK : Z := 96 + AASSIGN_STACK.     (* [comment removed for export] *)

Definition fh_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P E lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (g : bool) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (body_W lo sp P E) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' P (ParserCoreCells (snd (fh_res c)) pad7 pad2)
    /\ rw_cells bsegs m' E (ErrCodeCells (fst (fh_res c)))
    /\ AHttpCat m' (fh_assigns c || g) /\ AXStatics2 m'
    /\ ACONST m' /\ stack0 m' lo shi.

Definition fh_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P E lo shi : Z) (c : pcore) (pad7 pad2 ej : list byte) (g : bool),
  rw_cells bsegs m P (ParserCoreCells c pad7 pad2) -> pcore_ok c ->
  rw_cells bsegs m E [CB 24 ej] ->
  AHttpCat m g -> AXStatics2 m ->
  stk bsegs m lo (bv_unsigned sp) ->
  st_pure FH_STACK sp P E lo shi ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi -> accessible m P 80 -> accessible m E 24 -> shvis m P (P + 80) -> shvis m E (E + 24) ->
  evt bsegs (fh_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P E lo shi c pad7 pad2 g m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz E) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_BP_FINISH_HEADER) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ec_hc (E : ecv) : Prop :=
  E = EC_clear \/ (ec_cat E = AG_HTTP_CAT /\ 2 <= ec_flags E /\ 0 <= ec_val E < 2^31).

(* [comment removed for export] *)
Definition is_needmore (E : ecv) : bool :=
  (ec_cat E =? AG_HTTP_CAT) && (2 <=? ec_flags E) && (ec_val E =? HE_NEED_MORE).

(* [comment removed for export] *)
Definition psl_ec (E : ecv) (n hl loc : Z) : ecv :=
  if is_needmore E && (hl <=? n) then EC_http_loc HE_HEADER_LIMIT loc else E.

Definition APSL_RET : Z := 0xd1a84.   Definition APF_RET : Z := 0xd1c48.    (* [comment removed for export] *)
Definition WRAP_STACK : Z := 96 + AASSIGN_STACK.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition wrap_saved (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition seg1_post (pc_inner pc_ret : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P IN E n p0 hl lo shi : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR (wz pc_ret) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (wz (P + 64)) (wz IN)
                  (wz P) (wz IN) (wz (p0 + Z.min n hl)) (wz E) a4 a5 a6 a7
                  (wz E) (wz n) (wz p0) (shw IN) (shw (P + 64)) (wz 2147450880) s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz pc_inner) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells bsegs m' (bv_unsigned sp + -96) [CB 24 junk]
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) (wrap_saved s7 s6 s5 s4 s3 s2 s1 s0 ra)
    /\ (pc_inner = P_A_BP_INNER_PARSE_START_LINE -> a4 = wz 0)
    /\ ACONST m' /\ stack0 m' lo shi.

Definition seg1_stmt (pc_entry pc_inner pc_ret : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P IN E n p0 lo shi : Z) (c : pcore) (pad7 pad2 : list byte),
  rw_cells bsegs m P (ParserCoreCells c pad7 pad2) -> pcore_ok c ->
  rw_cells bsegs m IN [C8 (wz p0)] ->
  stk bsegs m lo (bv_unsigned sp) ->
  stin_pure WRAP_STACK sp P IN E lo shi ->
  0 <= n < 2^64 -> 0 <= p0 -> p0 + n < 2^64 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi -> accessible m P 80 ->
  0 < p0 ->                                     (* [comment removed for export] *)
  evt bsegs (seg1_post pc_inner pc_ret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P IN E n p0 (pc_hlim c) lo shi m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz IN) (wz n) (wz E) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc_entry) fc None m (seg_rom bsegs)).

Definition psl_seg1_stmt : Prop := seg1_stmt P_A_BP_PARSE_START_LINE P_A_BP_INNER_PARSE_START_LINE APSL_RET.
Definition pf_seg1_stmt : Prop := seg1_stmt P_A_BP_PARSE_FIELDS P_A_BP_INNER_PARSE_FIELDS APF_RET.

Definition seg2_W (lo : Z) (sp : word) (P E : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (P + 64, P + 68); (E, E + 24); (AG_HTTP_CAT, AG_HTTP_CAT + 64)]%Z.

Definition seg2_post_e (Ef : ecv) (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P IN E lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (p0 in1 : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom bsegs)
    /\ munch (seg2_W lo sp P E) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' P (ParserCoreCells (mkPC (pc_blim_has c) (pc_blim c) (pc_len c) (pc_len0 c) (pc_skip c)
                                              (pc_hlim c - (in1 - p0)) (pc_state c) (pc_f c)) pad7 pad2)
    /\ rw_cells bsegs m' IN [C8 (wz in1)]
    /\ rw_cells bsegs m' E (ErrCodeCells Ef)
    /\ AHttpCat m' true /\ AXStatics2 m'
    /\ ACONST m' /\ stack0 m' lo shi.

Definition seg2_post (rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P IN E lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (p0 in1 n loc : Z) (E1 : ecv) (m : mem) : machine_state -> Prop :=
  seg2_post_e (psl_ec E1 n (pc_hlim c) loc) rav sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 F fc P IN E lo shi c pad7 pad2 p0 in1 m.

(* [comment removed for export] *)
Definition seg2_stmt (pc_ret loc : Z) : Prop :=
  forall rv rax sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P IN E lo shi : Z) (c : pcore) (pad7 pad2 junk : list byte)
    (p0 in1 n : Z) (E1 : ecv) (g : bool),
  rw_cells bsegs m (bv_unsigned sp + -96) [CB 24 junk] ->
  rw_cells bsegs m (bv_unsigned sp + -72) (wrap_saved s7v s6v s5v s4v s3v s2v s1v s0v rax) ->
  rw_cells bsegs m P (ParserCoreCells c pad7 pad2) -> pcore_ok c ->
  rw_cells bsegs m IN [C8 (wz in1)] ->
  rw_cells bsegs m E (ErrCodeCells E1) -> ec_ok E1 -> ec_hc E1 ->
  AHttpCat m g -> AXStatics2 m ->
  stk bsegs m lo (bv_unsigned sp + -96) ->
  stin_pure WRAP_STACK sp P IN E lo shi ->
  p0 <= in1 <= p0 + pc_hlim c -> 0 <= p0 -> in1 < 2^64 -> 0 <= n < 2^64 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi -> accessible m P 80 -> accessible m E 24 -> shvis m E (E + 24) ->
  evt bsegs (seg2_post rax sp gp tp s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 F fc P IN E lo shi c pad7 pad2 p0 in1 n loc E1 m)
    (MS (mkR rv (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (wz (P + 64)) (wz IN) a0 a1 a2 a3 a4 a5 a6 a7
              (wz E) (wz n) (wz p0) (shw IN) (shw (P + 64)) (wz 2147450880) s8v s9v s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc_ret) fc None m (seg_rom bsegs)).

Definition psl_seg2_stmt : Prop := seg2_stmt APSL_RET ALOC_PSL_HL.
Definition pf_seg2_stmt : Prop := seg2_stmt APF_RET ALOC_PF_HL.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pch_fail (c c' : pcore) (n : Z) (E' : ecv) : Prop :=
  ec_cat E' = AG_HTTP_CAT /\ ec_failed E' = true /\ ec_ok E' /\ 2 <= ec_flags E'
  /\ In (ec_val E') [HE_NEED_MORE; HE_BAD_CHUNK; HE_BAD_LINE_ENDING; HE_BAD_CHUNK_EXTENSION; HE_BODY_LIMIT]
  /\ pc_state c' = pc_state c /\ pc_f c' = pc_f c /\ pc_hlim c' = pc_hlim c /\ pc_len c' = pc_len c
  /\ pc_len0 c' = pc_len0 c /\ pc_blim_has c' = pc_blim_has c /\ 0 <= pc_blim c' <= pc_blim c
  /\ 0 <= pc_skip c' /\ (pc_skip c' <= pc_skip c \/ pc_skip c' < n).

(* [comment removed for export] *)
Definition pch_succ (c c' : pcore) (p0 n p' : Z) : Prop :=
  p0 + 2 <= p' <= p0 + n /\ pc_skip c' = 0 /\ pc_f c' = Z.lor (pc_f c) 64 /\ 0 <= pc_len c' < 2^64
  /\ pc_len0 c' = pc_len0 c /\ pc_blim_has c' = pc_blim_has c /\ 0 <= pc_blim c' <= pc_blim c
  /\ ((pc_state c' = 9 /\ 0 < pc_len c' /\ pc_hlim c' = pc_hlim c)
      \/ (pc_state c' = 10 /\ pc_len c' = 0 /\ pc_hlim c' = pc_hlim c + 2)).

Definition pch_out (c c' : pcore) (p0 n p' : Z) (E' : ecv) : Prop :=
  (E' = EC_clear /\ pch_succ c c' p0 n p') \/ (p' = p0 /\ pch_fail c c' n E').

Lemma lor64_f14 : forall f, 0 <= f < 2^14 -> 0 <= Z.lor f 64 < 2^14.
Proof. intros f Hf. apply lor_bound; lia. Qed.
Scheme kc__3 := Elimination for Corelib.Init.Logic.or Sort Prop.

Lemma pch_out_ok : forall c c' p0 n p' E',
  pcore_ok c -> pc_hlim c <= 8192 -> pc_skip c < 2^62 -> 0 <= n < 2^62 -> pch_out c c' p0 n p' E' ->
  pcore_ok c' /\ pc_skip c' < 2^62.
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pcore); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.ecv); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pcore_ok); constr:(@kc__1); constr:(@Corelib.Init.Logic.or); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_blim_has); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_blim); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_len); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_len0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_skip); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_hlim); constr:(@Stdlib.Lists.List.In); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_state); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.pc_f); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_state1_stmt.HCW.pch_out); constr:(@kc__3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.EC_clear); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_state1_stmt.HCW.pch_succ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_state1_stmt.HCW.pch_fail); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.lor); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.X8_state1_stmt.HCW.lor64_f14); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.False); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.OR); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Init.Datatypes.tt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.Lt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.ec_cat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.AG_HTTP_CAT); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.ec_failed); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.ec_ok); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.ec_flags); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.ec_val); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.HE_NEED_MORE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.HE_BAD_CHUNK); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXRep.HE_BAD_LINE_ENDING); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.HE_BAD_CHUNK_EXTENSION); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AXPRep.HE_BODY_LIMIT); constr:(@Corelib.Init.Logic.and_ind); constr:(@Corelib.Init.Logic.or_ind)|] [|@z; @Ha; @__ff; @__varmap; @__wit; @__x1; @__arith; @__sat70; @__sat68; @__sat66; @__sat64; @__sat63; @__sat65; @__sat67; @__sat69; @__p1; @__x2; @__p2; @H1; @L1; @H0; @ST; @BL; @BH; @LN0; @LN; @FF; @SK; @P1; @S; @_H; @__x3; @H17; @H16; @H15; @H14; @H13; @H12; @H11; @H10; @H9; @H8; @H7; @H6; @H5; @H4; @H3; @H2; @SK0; @_H3; @_H2; @_H1; @_H0; @Fl; @OUT; @N62; @SK62; @HL; @Ff; @Stt; @Hl; @Sk; @Ln0; @Ln; @Bl; @Bh; @E'; @p'; @n; @p0; @c'; @c|] "#Qi$9%A$=$D$x##$y$w#$%$$~$9#K#I#N#O#-#H#n#1#5#Q#t#)#J#M#R#S#U#k#P#T#V#W#X#Y#\#`#f#l#p%-#*#,#0#9#=#E#Z#[#]#_#a#c#d#e#g#h#i#s#v#x#|#4#A#F#G#^#b#j#m#o#r#u$c$'#.#<#D#q#w$h%(%)#%#&$$$4#2#6#8#:#C#L%3$F#3#7#?$>#{$#$1#>#@$Y#'$q#z%1#y#(#+#/#B$a$e$o$s$&#}$+$3$0$5$7$U#;$f$p$X%6%7$)$-$.$/$8%B$<$^$g$m$l$k$r$t$v%%%&%*%+%'%0%4%5%@%?%>%=%<#~$%$($*$,$2$6$G$H$B$N$A$P$Q$S$V$R$I$O$M$C$|${$`$\$@$z$T$K$_$u$E%;$]%#%:$?$L$W%9%A%,$j$Z$[%/%8$J$b$d$n$i$}%.%2U$m%$n%$o&$p%$q%$r$$s$$t$$u$$v&$w$$x$$y$$z$${'$|*$}'$~%%#(%$*%%&%&$#&&%')%(+%)$%*$%+%%,%%-$%.$%/$%0)%1$%2(%3*%4&%5(%6'%7'%8$%9%%:%%;&%<%%=%%>%#&%%?)%@$AT$0S(%C#D<Sp%C%#'%#-S($D#8Sp<#B$8#8#<#L'#$+##+#/S($D#8-8#8#8#8#<#L2#&+##+#.S($D#&$'#$#(S($D#&$+#$#)S($D#818#8#8#8#B#8#<#$,##,#*S(BSp<#<BB%<#<s#$Bs#&<#<s#0Bs#2<#UT3C7C$#7C'#7C)#7C,#7C.#7C1#7C3#7Cs#=#7Cs#D#7CD#,C9#+S($D#88<#Ls#E#&'##'##*##s####s#0##s#5##s#:##s#F##s#R#)S;8s#/8#<#$&#(T%Bs#*B#8#<#Ls#Y#&(#$DS(&S(%#$#CQS<T%S;S(T$AQ(Q&#*#%#k##'#k##)#k##-#k##5#j##;#-S;$D#$$s#e#$#/S;$D#&$s#^#$#.S;$D#&$s#b#$#(S;$D#&$s#f#$#$Ds#+$s#,s#U#$#*S;,C#s#?+S;$D#&$s#<#$##'##*##.##3##8##=#0T%%C#D%C$s$3'$#-S<$D#$$s$,#$#/S<$D#&$s$%#$#.S<$D#&$s$)#$#(S<$D#&$s$-#$#)S<$D#$$s#y#$#*S<,C#s#c+S<$D#&$s#`#$##'##*##/##4##9##>#-Q$D#$$s$L#$#/Q$D#&$s$E#$#.Q$D#&$s$I#$#$Ds#Y&s#Zs$L#$#)Q$D#$$s$<#$#*Q,C#s$&+Q$D#&$s$##$##'##*##/##3##8##=#)S]$#s#{(T&&#s#v$DQ&Qs#x#$#CS$S=T&S]QS<AS$(S$&#s#}#%#k##'#k##)#k##-#k##0#j##3#/S]$D#&$s$q#$#.S]$D#&$s$u#$#(S]$D#&$s$y#$#$D?$@s$h#$#*S],C#s$R+S]$D#&$s$O#$##'##*##.##3##8#-T&$D#$$s%:#$#/S=$D#&$s%3#$#.S=$D#&$s%7#$#(S=$D#&$s%;#$#)S=$D#$$s%+#$#*S=,C#s$q+S=$D#&$s$n#$##'##*##/##4##9#/S$$D#&$s%N#$#.S$$D#&$s%R#$#$Ds#K&s#Ls%U#$#)S$$D#$$s%E#$#*S$,C#s%/+S$$D#&$s%,#$##'##*##/##3##8#)Si$#s%'(Sq&#s$~$DS$&S$s%$#$#CS%SPSqSiS$S=AS%(S%&#s%)#%#k##'#k##)#k##-#k##0#j##3#.Si$D#&$s%y#$#(Si$D#&$s%}#$#$D;$<s%l#$#*Si,C#s%V+Si$D#&$s%S#$##'##*##.##3#/Sq$D#&$s&2#$#.SP$D#&$s&6#$#(SP$D#&$s&:#$#)SP$D#$$s&*#$#*SP,C#s%p+SP$D#&$s%m#$##'##*##/##4#.S%$D#&$s&L#$#$Ds#=&s#>s&O#$#)S%$D#$$s&?#$#*S%,C#s&)+S%$D#&$s&&#$##'##*##/##3#)Sj$#s%|(Sr&#s%w$DS%&S%s%y#$#CS>SkSrSjS%SPAS>(S>&#s%~#%#k##'#k##)#k##-#k##0#j##3#(Sj$D#&$s&r#$#$D7$8s&a#$#*Sj,C#s&K+Sj$D#&$s&H#$##'##*##.#.Sr$D#&$s'&#$#(Sk$D#&$s'*#$#)Sk$D#$$s&v#$#*Sk,C#s&`+Sk$D#&$s&]#$##'##*##/#$Ds#/&s#0s':#$#)S>$D#$$s'*#$#*S>,C#s&p+S>$D#&$s&m#$##'##*##/#)Sl$#s&f(T4&#s&a$DS>&S>s&c#$#CS?S^T4SlS>SkAS?(S?&#s&h#%#k##'#k##)#k##-#k##0#j##3#$D3$4s'G#$#*Sl,C#s'1+Sl$D#&$s'.#$##'##*#$D<&=s'f#$#)S^$D#$$s'V#$#*S^,C#s'@+S^$D#&$s'=#$##'##*#)S?$D#$$s'b#$#*S?,C#s'L+S?$D#&$s'I#$##'##*#)Sx$#s'A(Ss&#s'<$DS?&S?s'>#$#CSQSySsSxS?S^ASQ(SQ&#s'C#%#k##'#k##)#k##-#k##0#j##3#*Sx,C#s'e+Sx$D#&$s'b#$##'#)Ss$D#$$s(*#$#*Sy,C#s'p+Sy$D#&$s'm#$##'#*SQ,C#s'w+SQ$D#&$s't#$##'#)T'$#s'k(Sm&#s'f$DSQ&SQs'h#$#CS@S_SmT'SQSyAS@(S@&#s'm#%#k##'#k##)#k##-#k##0#j##3#+T'$D#&$s(.#$#*Sm,C#s(7+S_$D#&$s(4#$#)S@$#s(*(SR&#s(%$DS_&S_s('#$#CRSSSRS@S_Sm%StS_SzHNRSSSRS@#$#%CS@SSINRSRS_#$#'&#0N%C#D%C$s)4'$#-N$D#$$s)-#$#/N$D#&$s)&#$#.N$D#&$s)*#$#(N$D#&$s).#$#)N$D#$$s(z#$#*N,C#s(d+N$D#&$s(a#$##'##*##/##4##9##>##s###&7s(V#$#j##s#*#%StS@SzHS)NRSSSR#$#%StSRSzHMS)NRSS#$#0M%C#D%C$s)b'$#-M$D#$$s)[#$#/M$D#&$s)T#$#.M$D#&$s)X#$#(M$D#&$s)\#$#)M$D#$$s)L#$#*M,C#s)6+M$D#&$s)3#$##'##*##/##4##9##>##s###&7s)(#$#j##s#*#HSnMS)NR%StRSzHOS*SnMS)4S*s*)$#M4S*Sn$M##%#(O%C#D+O+P>#s*#%C%#/O$D#&$s*&#$#.O.P%C$#0O0P%C$#-O$D#-P$%##%#*O%C#s)q&D3)O)P%C$##&##(#%C*s)w%C:D4(s*M%C*##%##'#')##2##8##<##@##s#%##s#*##s#-#%C?D%C@s*`'$#$D>$?s*X#$#/P$D#&$s*Q#$#$Ds#,&s#-s*T#$#(P$D#&$s*X#$#$Ds#%$s#&s*G#$#*P,C#s*1$Ds#@&s#As*-#$##&##)##-##2##6##;##?#&5s)~#$#j##s#%#%C8D+S/>#s*o%Cs#P#.S/%Cs#J#0S/%Cs#I#-S/$s#G##s#,#%C<s*X&Ds#+)S/%Cs#E##%##'#%CBs*]%Cs#1D4(s+3%Cs#K##%##'#')##0##4##7##s#7##;##?#4Ps+>$#S*4PO$S*##%#(S&%C#D+S&+S+>#s+8%C%#/S&$D#&$s+;#$#.S&.S+%C$#0S&0S+%C$#-S&$D#-S+$%##%#*S&%C#s+*&D3)S&)S+%C$##&##(#%C*s+0%C:D4(s+b%C*##%##'#')##2##8##<##@##s#%##s#*#(S+%C#D+S,>#s+a%Cs#-#/S+$D#&$s+d#$#.S,%Cs#+#0S,%Cs#*#$Ds#'-S,$s#)##%#*S+%C#s+P&D0)S,%Cs#(##%##'#%C)s+U%C6D4(s,+%Cs#.##%##'#')##1##6##9##<##A##s#%#%C<D%C=s,='$#$D<$=s,5#$#/S,$D#&$s,.#$#$Ds#(&s#)s,1#$#(S,$D#&$s,5#$#$Ds#$$s#%s,$#$#*S,,C#s+j$Ds#;&s#<s+f#$##&##)##-##2##6##;##?#&5s+[#$#j##s#%#+S0>#s,K%Cs#J#.S0%Cs#E#0S0%Cs#E#-S0$s#D##s#+#%C;s,4&Ds#*)S0%Cs#C##%##'#%CAs,9%Cs#0D4(s,k%Cs#I##%##'#')##0##4##7##s#6##;#(S0%C#D+S-+S1>#s,j%C%#/S-$D#&$s,m#$#.S-.S1%C$#0S-0S1%C$#-S-$D#-S1$%##%#*S-%C#s,\&D3)S-)S1%C$##&##(#%C*s,b%C:D4(s-8%C*##%##'#')##2##8##<##@##s#%#+S2>#s-4%Cs#*#/S1$D#&$s-7#$#.S2%Cs#(#0S2%Cs#'#$Ds#$-S2$s#&##%#*S1%C#s-#&D0)S2%Cs#%##%##'#%C)s-(%C6D4(s-Z%Cs#+##%##'#')##1##6##9##<##A#%C;D%C<s-k'$#$D;$<s-c#$#/S2$D#&$s-\#$#$Ds#'&s#(s-_#$#(S2$D#&$s-c#$#$Ds##$s#$s-R#$#*S2,C#s-<$Ds#:&s#;s-8#$##&##)##-##2##6##;##?#&5s--#$#j##s#%#.S3%Cs#A#0S3%Cs#A#-S3$s#@##s#(#%C8s-_&Ds#')S3%Cs#?##%##'#%C>s-d%Cs#-D4(s.:%Cs#E##%##'#')##0##4##7##s#3#+S3+S4>#s.6%C%#/S4$D#&$s.9#$#.S4.SA%C$#0S40SA%C$#-S4$D#-SA$%##%#*S4%C#s.(&D3)S4)SA%C$##&##(#%C*s..%C:D4(s.`%C*##%##'#')##2##8##<##@#/SA$D#&$s.[#$#.SB%Cs#$#0SB%Cs###$D@-SB$B##%#*SA%C#s.G&D0)SB%CA##%##'#%C)s.L%C6D4(s.~%Cs#'##%##'#')##1##6##9##<#%C:D%C;s/2'$#$D:$;s/*#$#/SB$D#&$s/##$#$Ds#&&s#'s/&#$#(SB$D#&$s/*#$#$DB$s##s.u#$#*SB,C#s._+SB$D#&$s.\#$##'##*##.##3##7##<##@#&6s.Q#$#j##s#&#.S5%Cs#A#0S5%Cs#A#-S5$s#@##s#)#%C9s/'&Ds#()S5%Cs#?##%##'#%C?s/,%Cs#.D4(s/^%Cs#E##%##'#')##0##4##7#/S5$D#&$s/X#$#.SC.ST%C$#0SC0ST%C$#-SC$D#-ST$%##%#*SC%C#s/G/SC&D#)SC)ST%C$##&##)#%C+s/N%C*D4(s0$%C*##%##'#')##3##9##=#.SD%C@#0SD%C?#$D<-SD$>##%#*ST%C#s/b/ST&D#)SD%C=##%##(#%C*s/h%C)D4(s0>%Cs####%##'#')##2##7##:#%C:D%C;s0M'$#$D:$;s0E#$#/SD$D#&$s0>#$#$Ds#&&s#'s0A#$#(SD$D#&$s0E#$#$DA$Bs04#$#*SD,C#s/z+SD$D#&$s/w#$##'##*##.##3##7##<##@#&6s/l#$#j##s#&#0S6%Cs#?#-S6$s#>##s#'#%C7s0@&Ds#&)S6%Cs#<##%##'#%C=s0E%Cs#,D4(s0w%Cs#B##%##'#')##0##4#.S6.SE%C$#0SE0SU%C$#-SE$D#-SU$%##%#*SE%C#s0[/SE&D#)SE)SU%C$##&##)#%C+s0b%C*D4(s18%C*##%##'#')##3##9#0SF%C<#$D9-SF$;##%#*SU%C#s0s/SU&D#)SF%C:##%##(#%C*s0y%C)D4(s1O%C@##%##'#')##2##7#%C9D%C:s1]'$#$D9$:s1U#$#/SF$D#&$s1N#$#.SF$D#&$s1R#$#(SF$D#&$s1V#$#$DA$Bs1E#$#*SF,C#s1/+SF$D#&$s1,#$##'##*##.##3##8##=##A#&6s0}#$#j##s#'#-SG$s#<##s#&#%C5s1O&Ds#%)SG%Cs#:##%##'#%C;s1T%Cs#+D4(s2*%Cs#@##%##'#')##0#0SG0SH%C$#-SH$D#-S7$%##%#*SH%C#s1f/SH&D#)SH)S7%C$##&##)#%C+s1m%C*D4(s2C%C*##%##'#')##3#$D6-SI$8##%#*S7%C#s1{/S7&D#)SI%C7##%##(#%C*s2%%C)D4(s2W%C=##%##'#')##2#0SI%C#D%C$s2e'$#$D9$:s2]#$#/SI$D#&$s2V#$#.SI$D#&$s2Z#$#(SI$D#&$s2^#$#$DA$Bs2M#$#*SI,C#s27+SI$D#&$s24#$##'##*##.##3##8##=##A#&6s2)#$#j##s#(#%C2s2T&DB)SJ%Cs#7##%##'#%C8s2Y%Cs#(D4(s3/%Cs#=##%##'#')#-SJ$D#-SK$%##%#*SK%C#s2g/SK&D#)SK)SV%C$##&##)#%C+s2n%C*D4(s3D%C*##%##'#')#+S.VTA#N>$s3<$D#&$s2f#$#*S.%C#s2}/S.&D#)S.)S8%C$##&##)#%C+s3(%C*D4(s3Z%C*##%##'#')#0S8%C#D%C$s3g'$#-S8$D#$$s3`#$#/S8$D#&$s3Y#$#.S8$D#&$s3]#$#(S8$D#&$s3a#$#$DA$Bs3P#$#*S8,C#s3:+S8$D#&$s37#$##'##*##.##3##8##=##B#&6s3,#$#j##s#)#%C2s3W&DB)SW%Cs#7##%##'#*SW%C#s3^/SW&D#)S#%C+##%##(#0S#%C#D%C$s4@'$#-S#$D#$$s49#$#/S#$D#&$s42#$#.S#$D#&$s46#$#(S#$D#&$s4:#$#$D:$;s4)#$#*S#,C#s3o+S#$D#&$s3l#$##'##*##.##3##8##=##B#&6s3a#$#j##s#)#&DA)SX%Cs#/##%#*SX%C#s45/S`&D#)S`)SY%C$##&#0SY%C#D%C$s4s'$#-SY$D#$$s4l#$#/SY$D#&$s4e#$#.SY$D#&$s4i#$#(SY$D#&$s4m#$#$D9$:s4\#$#,CIs4E+SY$D#&$s4B#$##'##)##-##2##7##<##A#&5s47#$#k##s#(#j#$C#/S9&D#)S9%C#s#0#%#,Cs4hs4Z##4#:##>##s####s#(##s#-##s#2###3j##s#8#)SL%Cs#<#/SL&D#)S')SZ%C$#)SM0SM%C#D%C$s5U'$#-SM$D#$$s5N#$#/SM$D#&$s5G#$#.SM$D#&$s5K#$#(SM$D#&$s5O#$#$DF$Fs5>#$#+SM$D#&$s5##$##s#/##(##,##1##6##;##@#&4s4t#$#j#$C#&Fs5b#4#)Sa$D#$$s5R#$###2#(##@##s#%##s#*##s#/#&Fs5'#$#j#$C#>?s5r$DD&Ds5s#$#&Fs5B#s#'##s#N##3##'##s#0##s#5##s#:##s#?#&Ds57#$#j#$C#+Sa>#s6'$D#&$s5Q#$##s#]##B##6##s#(##s#D##s#I##s#N###1j#$C#%CFD%CFs6J'$#.Sa$D#&$s68#$###0#s#Q##s#V##*###>j#$C#-SZ$D#$$s6M#$#/SZ$D#&$s6F#$#$Ds#j$s#ks65#$#%CDs6,%Cs6bs6-%Cs6]s6.%Cs65s6/%Cs65s60%Cs64s61%Cs64s62%Cs63s63%Cs63s64%Cs62s65'#T('%#''#')#'+#'-#'/#'1#'3#'5#$Ds#L&s#Ms6-#$##&##;##s#N##s#w##A##s#&##s$*#Ms6ys67&Ds6z$Ds69&Ds69k##$#k##&#$Ds7#Ns7$s6>Ij##S[#j#%%#$Ds6@k##S[#k#%(#Ms7*s60$Ds61k###s#Xk##1#Ns7.s64Ij##S[#j#%/#$Ds66k##S[#k#%2#Ms74s70$Ds71&Ds71k##$#k##<#Ns79s75Ij##S[#j#%:#$Ds77k##S[#k#%=#Ms7?s70$Ds71k###s#xk##s#&#Ns7Cs74Ij##S[#j#%s#$#$Ds76k##S[#k#%s#'#VTBDs7IVT)T5#m##s#/UI#US{$US;%UQ&UTCSpVTDC#UT*T6UT*#OC#WTEC&#OC&GC$#P#S|UT3Sb7Sb$#7Sb%#UTFSbVT+CIUTGCUTHCQCSp?CD1C$K#2&HEEG#J?Cs7j1C'K#2)HEEG#J6*HEEG&#UTIE;,HEEG$#$VTJ-GVT)ScSdVTKFSe%Sc#Sdm$%#WTLCDIXTMFSe$#l#&*)#l#'76#l#(:9#j#)C#%CID%CIs7|'$#k##s$5#k#)C#0S\R#S}l#**%#l#+s#0s#^#l#,s#2s#T#l#-s#4s#J#l#.s#6s#A#l#/s#>s#;#l#.s#Es#B#l#0s#Js#G#l#-s#Rs#N#l#1s#Ws#T#l#,s#^s#[#l#2s#cs#`#l#+s#ms#h#m##s%;1Cs#+S:s#,2s#.HEEG#JSs#/HEEGSfFs#0HEEG$#;s#1HEEG#s#(%l#&#s#'Al#'s#5s#4#l#(s#:s#7#j#)C#j#3L##s%5I$DIk##$#k#)C#k#3L#-T,-S\$$#9#%S^l#*,'#l#+s#Qs$##l#,s#Ss#u#l#-s#Us#k#l#.s#Ws#b#l#/s#_s#\#l#.s#fs#c#l#0s#ks#h#l#-s#ss#o#l#1s#xs#u#l#,s$#s#|#l#2s$(s$%#l#+s$2s$-#m##s$[OCT6GCs#X#GCs#[#P#S|7Sb#s#XVT+CSeUTNCJC$I#Ss#VHEEGS{QCs8Y1Cs#WS:#2s#YHEEG#JFs#ZHEEG&#Ss#[HEEGT$?Cs8]Ts8[WS~C$#1C*S:#2s#`HEEG#JFs#aHEEG(#1Cs#aS:&2s#cHEEG#J;s#dHEEG%s#[#;s#eHEEG-s#\#l#&#s#[s#Ul#'4s#h#l#(8s#k#j#)C#j#4C#j#3L#j#5L#$FI#Se#$Ses8k#S{#k###$k##&#k#)C#k#4C#k#3L#k#5L#$Ds#<$Ds#>ZF$#s#>s#?S^SMl#*0&#l#+s$/s$]#l#,s$1s$S#l#-s$3s$I#l#.s$5s$@#l#/s$=s$:#l#.s$Ds$A#l#0s$Is$F#l#-s$Qs$M#l#1s$Vs$S#l#,s$]s$Z#l#2s$bs$_#l#+s$ls$g#m##s%83s%:s%9s#=#/T,&#s8{9#$Rl#*s#Xs#S#l#+s$As$o#l#,s$Cs$e#l#-s$Es$[#l#.s$Gs$R#l#/s$Os$L#l#.s$Vs$S#l#0s$[s$X#l#-s$cs$_#l#1s$hs$e#l#,s$os$l#l#2s$ts$q#l#+s$~s$y#m##s%GTs91WS~Cs#A#1Cs$?So#2s$AHEEG#JFs$BHEEGs#q#;s$CHEEG#s$:$l#&#s$9s$3l#'s$Gs$F#l#(s$Ls$I#j#)C#j#3L##Is&6&Is9;k##$#k#)C#k#3L#$Ds##9#s#$Rl#**%#l#+s$as%3#l#,s$cs%)#l#-s$es${#l#.s$gs$r#l#/s$os$l#l#.s$vs$s#l#0s${s$x#l#-s%'s%##l#1s%,s%)#l#,s%3s%0#l#2s%8s%5#l#+s%Bs%=#m##s%f3s%hs%gs###.S\&#s9Q9#$S#l#*s$.s$)#l#+s$ss%E#l#,s$us%;#l#-s$ws%1#l#.s$ys%(#l#/s%%s$~#l#.s%,s%)#l#0s%1s%.#l#-s%9s%5#l#1s%>s%;#l#,s%Es%B#l#2s%Js%G#l#+s%Ts%O#m##s&t$D39#4S#l#*s#,s#'#l#+s%'s%U#l#,s%)s%K#l#-s%+s%A#l#.s%-s%8#l#/s%5s%2#l#.s%<s%9#l#0s%As%>#l#-s%Is%E#l#1s%Ns%K#l#,s%Us%R#l#2s%Zs%W#l#+s%ds%_#m##s''3s')s'(3#1Cs%#S:s%#2s%&HEEG#Jl#&#s$xs$rl#'s$2s%)#l#(s%/s%,#l#*#s&cFl#+s%;s%i#l#,s%=s%_#l#-s%?s%U#l#.s%As%L#l#/s%Is%F#l#.s%Ps%M#l#0s%Us%R#l#-s%]s%Y#l#1s%bs%_#l#,s%is%f#l#2s%ns%k#l#+s%xs%s#m##s&pVT)T5TO3s&rs&q$#)S\$#s9t9#$S7l#*s$es$`#l#+s%Ns%|#l#,s%Ps%r#l#-s%Rs%h#l#.s%Ts%_#l#/s%\s%Y#l#.s%cs%`#l#0s%hs%e#l#-s%ps%l#l#1s%us%r#l#,s%|s%y#l#2s&%s%~#l#+s&/s&*#m##s&Q?Cs:(1Cs%KS:#2s%MHEEG#JFs%NHEEGs$}#;s%OHEEG#s%F$l#&#s%Es%?l#'s%Ss%R#l#(s%Xs%U#j#)C#j#3L##Is'R$Is:3k##$#k#)C#k#3L#$DB9#s##S7l#**%#l#+s%ms&?#l#,s%os&5#l#-s%qs&+#l#.s%ss%~#l#/s%{s%x#l#.s&&s&##l#0s&+s&(#l#-s&3s&/#l#1s&8s&5#l#,s&?s&<#l#2s&Ds&A#l#+s&Ns&I#m##s&o3s&qs&pB#?Cs:=1Cs%jK#2s%mHEEG#J1Cs%iK%2s%oHEEG#J1Cs$rK'2s%qHEEG#J?Cs:J1C#K*2s%tHEEG#J?Cs:L1C#K-2s%wHEEG#J?Cs:M1C#K02s%zHEEG#J?Cs:O1C#K32s%}HEEG#J1C5K52s&#HEEG#J?Cs:Q1C#K82s&&HEEG#J?Cs:R1C#K;2s&)HEEG#JSs&*HEEGSe6s&+HEEG$#6s&,HEEG(#6s&-HEEG,#6s&.HEEG/#6s&/HEEG3#6s&0HEEG7#6s&1HEEG;#6s&2HEEG?#6s&3HEEGB#6s&4HEEGs#%#l#&#s&*s&$l#'s%@s&7#l#(s&=s&:#j#3L#'s'4F's'6#'s'8#'s':#'s'<#'s'>#'s'@#'s'B#'s'D#'s'F#k#3L#UFT(l#*/$#l#+s&Vs'(#l#,s&Xs&z#l#-s&Zs&p#l#.s&\s&g#l#/s&ds&a#l#.s&ks&h#l#0s&ps&m#l#-s&xs&t#l#1s&}s&z#l#,s'(s'%#l#2s'-s'*#l#+s'7s'2#m##s'C+S\>#s;F&#s:o9#$Sll#*s&#s%z#l#+s&hs':#l#,s&js'0#l#-s&ls'&#l#.s&ns&y#l#/s&vs&s#l#.s&}s&z#l#0s'&s'##l#-s'.s'*#l#1s'3s'0#l#,s':s'7#l#2s'?s'<#l#+s'Is'D#m##s'TTs;%WS~Cs%h#1Cs&fSo#2s&hHEEG#JFs&iHEEGs&<#;s&jHEEG#s&a$l#&#s&`s&Zl#'s&ns&m#l#(s&ss&p#j#)C#j#3L##Is(J&Is;/k##$#k#)C#k#3L#$Ds##9#s#$Sll#**%#l#+s',s'Z#l#,s'.s'P#l#-s'0s'F#l#.s'2s'=#l#/s':s'7#l#.s'As'>#l#0s'Fs'C#l#-s'Ns'J#l#1s'Ss'P#l#,s'Zs'W#l#2s'_s'\#l#+s'is'd#m##s's3s'us'ts###3s'ws'ts#6#3s(0s'ts#{#3s(cs'ts$Q#3s)0s'ts$g#3s(6s'ts%.#3s(;s'ts%a#3s)?s'ts&b#3s'ts(^#s$W#s)Vs'|#s(8##s(k##s)8##s(>##s(C##s)G###s(fm#+#0SZ:Cs)Ns(L$#Sq.SZ:Cs)Ds([$#Sr+SZ:Cs(zs(k$#Ss(SZ:CDs(}$#Sm:Cs)Vs)1#s)XFj#6s)X#j#7s)\#V#IFj##s)`#j##s*A#5s*Bs*?s)d#Fj#6s)o#*S9:Cs;zs)v$#Fj#6s*H#V#IFj##s*L#j##s*~#5s+#s*zs*R#Fj#6s+&#U#Fj##s+\#%Cs+>s<&%Cs+ND4s+.s<X%Cs+c##%##'#%Cs+.s<,%Cs+-D4s+,s<^%Cs+5##%##'#j###s*c%Cs+%D4s*bs<d%Cs+3##%#%Cs*bs<7%Cs*aD4s*_s<i%Cs*a##%#k###s*;j#$C#%Cs*:D4s*fs<o%Cs*:##%#,Cs<Bs<5##s*K#s*Q##s*U##s*Z##s*_##s*d##s*i###s*Jj##2#4s*9s<|%Cs*s#%Cs*9D4s*7s=#%Cs*9#4s*7s=%#2s)y#s)~##s*&##s*+##s*0##s*5##s*:###s)xj#$C#4s)us=/$D#$$s<i#$###/#s){##s*7##s*<##s*A##s*F###s)uj#$C##s#'s)o#,##s)s##s*@##s*E##s*J##s*O###s)nj#$C##s#0s)i#5##s)|##s*2##s*N##s*S##s*X###s)wj#$C##s)b)#s*T##s*Y##s)i###s)}j#$C#$Ds#0$s#1s=0#$#%CDs=&%Cs=]s='%Cs=Xs=(%Cs=0s=)%Cs=0s=*%Cs=/s=+%Cs=/s=,%Cs=.s=-%Cs=.s=.%Cs=-s=/'#T('%#''#')#'+#'-#'/#'1#'3#'5###s)W#8##s*F##s*o##s)u##s)z##s*~#WTPCs(os'r1Cs(oS:#2s(rHEEG#J;s(sHEEGs(Es(j#l#&#s(is(cl#'s(ws(v#l#(s(|s(y#j#)C#j#3L#4Is=z$D#k##s(F#k#)C#k#3L#l#*(#s&Dl#+s)3s)a#l#,s)5s)W#l#-s)7s)M#l#.s)9s)D#l#/s)As)>#l#.s)Hs)E#l#0s)Ms)J#l#-s)Us)Q#l#1s)Zs)W#l#,s)as)^#l#2s)fs)c#l#+s)ps)k#m##s#;?Cs==1Cs)0S:#2s)2HEEG#J1CAS:s&F2s)4HEEG#J;s)5HEEG%s),#l#&#s)+s)%l#'s)9s)8#l#(s)>s);#j#)C#$Fs=G$@s=tk##$#k#)C#Rs&bS6l#*($#l#+s)Ps)~#l#,s)Rs)t#l#-s)Ts)j#l#.s)Vs)a#l#/s)^s)[#l#.s)es)b#l#0s)js)g#l#-s)rs)n#l#1s)ws)t#l#,s)~s){#l#2s*'s*$#l#+s*1s*,#m##s#W3s#Ys#X@#1Cs)LKs&,2s)OHEEG#J1Cs)KKs&.2s)QHEEG#J1Cs(TKs&02s)SHEEG#J1Cs&@Ks&22s)UHEEG#J1Cs&?Ks&42s)WHEEG#J1Cs&>Ks&62s)YHEEG#J1Cs&=Ks&82s)[HEEG#J1Cs&OKs&:2s)]HEEG#J1Cs&<Ks&<2s)_HEEG#J1Cs&;Ks&>2s)aHEEG#J6s)bHEEG#s&:6s)cHEEG&#6s)dHEEG)#6s)eHEEG,#6s)fHEEG/#6s)gHEEG2#6s)hHEEG5#6s)iHEEG8#6s)jHEEG;#6s)kHEEG>#l#&#s)as)[l#'s(ws)n#l#(s)ts)q#j#3L#'s#pF's#r#'s#t#'s#v#'s#x#'s#z#'s#|#'s#~#'s$$#'s$&#k#3L#l#*.#s&9l#+s*0s*^#l#,s*2s*T#l#-s*4s*J#l#.s*6s*A#l#/s*>s*;#l#.s*Es*B#l#0s*Js*G#l#-s*Rs*N#l#1s*Ws*T#l#,s*^s*[#l#2s*cs*`#l#+s*ms*h#m##s#~3s$#s*w#s%b3s$8s$#s#?#3s+fs$#s'T#3s,3s$#s'j#3s+9s$#s(1#3s+>s$#s(d#3s,Bs$#s)e#3s$#s+a#s'Z#s$~s+##s$@##s+n##s,;##s+A##s+F##s,J###s+im#+#:Cs,Ps$K#s%aSq:Cs,Es$R#s%`Sr:Cs+zs$\#s%_Ss:CDs$f#s%^Sm:Cs$|s$s#s,WFj#6s$~#j#7s%%#V#IFj##s%(#j##s%>#5s%?s%=s%,#Fj#6s%7#:Cs>ws%<#s%]Fj#6s%C#V#IFj##s%F#j##s%Q#5s%Rs%Ns%L#Fj#6s%T#U#Fj##s.T#ZT7s.[s.Us.-s%]#Il#8s.is.e#j#9s.l#j#:s.}#V#IFj##s/(#j##s/l#5s/ms/^s/7#Fj#8s/r#j#;s0-#V#IFj##s02#j##s0~#5s1#s0ks0E#Fj#8s1&#j#<s1A#V#IFj##s1F#j##s2;#5s2<s2%s1\#Fj#8s2?#j#=s2^#V#IFj##s2d#j##s3^#5s3_s3Fs2}#Fj#8s3d#j#>s4+#V#IFj##s41#j##s50#5s51s4os4K#Fj#8s55#j#?s5]#V#IFj##s5a#j##s6h#5s6is6Gs6##Fj#8s6l#j#@s7;#V#IFj##s7B#j##s8S#5s8Ts8*s7b#Fj#As8Z#j#Bs8\#V#IFj##s8_#j##s9/#5s90s9/s8b#Fj#8s92#U#Fj##s9c#%CSRRIS)NSSS@#$#%CSSNIMS)RSR#$#j###s8mISnMNSS%CNMIOS*MNUT8S)%C#T9KS)%Sc#SdDS)@S)$s@=#=S)7CTQs?h7CTR#7CTS#7CTT#7CTU#,C(#%Cs8`s86%Cs8ts8s%Cs8qs8F$Ds8x$s8ys8A&s8zSn'$##&##s8i##s8o##s8s##+##s8g##.##0##2##:##=##?##B#j###s8=KM%Sc#SdDM@M$s@^#=M,C#?*S/%Cs8S#%Cs94s8D/S/%Cs8d#(S/$s8_#&s8`S*'$##s8a##s8C##s8G##s8J##+##s8C##/##1##4##7##:##<#UT8Sn%C#T9KS*%Sc#SdDS*@S*$s@|#=S*,C#s#=%Cs8)s7_%Cs8=s8<%Cs8:s7m$Ds8A$s8Bs7t&s8CP'$##&##s82##s88##s8<##+##s80##.##0##2##5##8##:#KO%Sc#SdDO@O$sA:#=O,C#s#W%Cs7ys7Q%Cs8Vs8-%Cs8+s7a$Ds81$s82s7\&s83S/'$##&##s8&##s8+##s8.##+##s8%##.##0##2##5##8##:#j###s7WDP@P$sAS#=P,C#s#p*S0%Cs7k#%Cs8Gs7]/S0%Cs7|#$s7vs7D&s7wS&'$##s7x##s7[##s7_##s7b##*##s7[##.##0##3##6##9#KS/%Sc#SdDS&@S&$sAm#=S&,C#s$.%Cs7Ds6}%Cs7Xs7W%Cs7Us7/(S-$D#(S1$%#&&S,'$##'##s7O##s7U##s7Y##-##s7M##0##2##4##7##:#DS+@S+$sB*#=S+,C#s$G%Cs7:s6o%Cs7ps7J%Cs7Hs7#$D9$:s6z&;S0'$##&##s7C##s7H##s7K##+##s7B##.##0##2##5##8#j###s6t@S,$sBA#=S,,C#s$^*S3%Cs7+#%Cs7bs6a/S3%Cs7<#(S3$s77#&s78S-'$##s79##s6{##s7###s7&##+##s6{##/##1##4##7#DS0@S-$sBY#=S-,C#s$v%Cs6ds6E+SA%Cs6x#%Cs6vs6T(S4$D#(SA$%#&&S2'$##'##s6p##s6v##s6z##-##s6n##0##3##5##8#@S1$sBq#=S1,C#s%2%Cs6]s67%C:s66%Cs6ks6G$D7$8s6B&9S3'$##&##s6f##s6k##s6n##+##s6e##.##0##2##5#j###s6:=S2,C#s%F*S5%Cs6L#+S5%Cs6L#%Cs6]s6((S5$s6X#&s6YS4'$##s6Z##s6?##s6C##s6F##+##s6?##.##1##4#@S3$sC?#=S4,C#s%\%Cs6+s5l+SC+ST%C$#%Cs6-s5n(SC$D#(ST$%#&&SB'$##'##s68##s6>##s6B##-##s65##0##4##6#=SA,C#s%r%Cs6&s5\%C7s5[%Cs6&s5l$D4$5s5g&6S5'$##&##s6/##s64##s67##+##s6-##.##0##2#j###s5^*S6%Cs5n#+S6%Cs5n#/S6%Cs6$#%Cs6Es5O(S6$s5|#&s5}SC'$##s5~##s5e##s5i##*##,##s5e##0##3#=S5,C#s&<%Cs5Ss5;+SE+SU%C$#%Cs5Us5=.SU%Cs5c#(SE$D#(SU$%#&&SD'$##'##s5b##s5h##,##/##s5_##2##6#%Cs5Ps5*%C6s5)%Cs5Ps5;%C5s58$D2$3s56&4S6'$##&##s5Z##s5_##*##,##s5X##/##1#j###s5,+SG%Cs5:#/SG%Cs5M#.SG%Cs5K#%Cs5ms4|(SG$s5J#&s5KSE'$##s5L##s55##)##+##.##s55##2#*SG%C#s5%+S7%C#s4F%Cs4ms4X.S7%C#s4V0S7%C#s4c(S7$D#$$s4W&%SG'$##&##s4{##*##-##0##s4y##3##s2Ks4U#s4\##s4`##s4e##s4j##s4o##s4s###s4Tk##+#j#$C#+SH%C#@%Cs5Cs5..SH%C#@%Cs5O?(SH$D#$$@&%SF'$##&##s5P##*##,##/##s5M##2#*SJ,C#sDO##s4s#s4z##s4~##s5'##s5,##s51##s55###s4rj##s#)#/SJ%Cs55#.SJ%Cs53#0SJ%Cs5@#$s5Ts4j#s5>#(SJ$s55#&s56SH'$##s57##(##+##.##1##s5##+SJ+SK%C$#+SV%Cs4ps4[/SV%C#s4_.SV.S.%C$#0SV0S.%C$#-SV$D#-S.$%##%#(SV$D#(S.$%#&&SJ'$##'##*##0##4##8##;#%C5D%C6sEq'$#$D4$5sEi#$#$Ds4}&s4~sEa#$#$DA&BsEd#$#$D8&9sEg#$#$Ds5($s5)sEV#$##s0Es,h#s4d##%##)##-##1##5##9#&s#&sE-#$#k##?#j#$C#%Cs5Os#9.SK%C#s#90SK%C#s#8$Ds5Y$s5Zs#7#$#(SK$D#$$s#6&%SI'$##&##)##-##0##3##s5]##Bs4}#s#&##s#*##s#.##s#2##s#6###?j##s#;#%Cs5Ts5>%Cs#Rs5;%Cs#Ps5H$s#Ms5E#s#<#$s#Js5;&s#KSK'$##s#7##'##*##,##.#/SX%Cs4s#.SX%Cs4q#0SX%Cs5##-SX$s4}##s4}#(SX$s4t#&s4uS8'$##s4v##(##,##/##2#%C0D%C1sFm'$#$D1$2sFe#$#$D:&;sF]#$#$D;&<sF`#$#$D7&8sFc#$##s1>s.|,Cs-,sF9+S9$D#&$sF6#$##'##)##+##/##3##7##;#&s#'sF+#$#k##A#j#$C#%Cs5Vs5H.SW%C#s5F0SW%C#s5T-SW$D#$$s5S#$#(SW$D#$$s5K&%S.'$##&##)##.##1##4#$Ds4c$s4dsFv#$###s###s#+##s#/##s#3##s#7##s#;###Bj##s#@#.S9%Cs#Q#0S9%Cs#Q#-S9$s#Q##s#C#(S9$s#Q#&s#RSW'$##s#?##(##,##/#%Cs5#s5P.SL%Cs5@#0SL%Cs5N#-SL$s5L##s5L#(SL$s5C#&s5DS9'$##s5E##(##,##/#%C/D%C0sGn'$#$D0$1sGf#$##s26s1$$D8&9sG_#$#$D4&5sGb#$#$Ds5-$s5.sGQ#$#*S',C#sG;+S'$D#&$sG8#$##'##*##.##2##6##8##<#&s#'sG-#$#k##B#j#$C#.S`%C#s5p0S`%C#s5~-S`$D#$$s5}#$#(S`$D#$$s5u&%SX'$##&##)##.##1#/S'$D#&$sH/#$###?#s#4##s#8###>j##s#=#0S'%Cs#K#-S'$s#K##s#>#(S'$s#K#&s#LS`'$##s#<##(##,#.S'%C#s.s0Sa%Cs5f#-Sa$s5d##s5d#(Sa$s5[#&s5\S''$##s5]##(##,#%C.D%C/sHg'$#$D/$0sH_#$#/SN$D#&$sHX#$#$D3&4sH[#$#)SN$D#$$sHK#$#*SN,C#sH5+SN$D#&$sH2#$##'##*##/##s#k##4##9##=#&s#'sH'#$#k##s###j#$C#%Cs/Hs67$s55s64#s55#$Ds/E$s/Fs6+&s/GSL'$##&##(##+#.SN$D#&$sH~#$###9#s#*##s#/##s#3###8j##s#8#-SN$s#C##s#7#(SN$s#C#&s#DSZ'$##s#5##(#0SN0T#%C$#0S}-S}$D#-Su$%##%#(S}$D#(Su$%#&&SN'$##'##*#$D-$.sIP#$#/SO$D#&$sII#$#.SO$D#&$sIM#$#$D3&4sIP#$#)SO$D#$$sI@#$#*SO,C#sI*+SO$D#&$sI'#$##'##*##/##3##8##=##s4Y#&s#'sHx#$#k##s#$#j#$C#-T#$D#$$s#4#$#(T#$D#$$s#3&%Sa'$##&##)#0SO%C#D%C$sJ.'$###7##6j##s#7#(SO$s#>#&s#?T#'$##s#0#-SO$D#-T-$%##%#(T-$D#(TV$%#&&Su'$##'#$D'(Sv$)#&*SO'$##'#0Sg%C#D%C$sJL'$#-Sv$D#$$sJE#$#/Sg$D#&$sJ>#$#.Sg$D#&$sJB#$#$D7&8sJE#$#)Sg$D#$$sJ5#$#*Sg,C#sI{+Sg$D#&$sIx#$##'##*##/##3##8##=##B#&s#+sIm#$#j##s#)#(Sg$s#/#&s#0T-'$#$D&(TW(T,$$#&%Sv'$#%Cs5YD%Cs5ZsJ|'$#$s5=sJs#s4^#/S\$D#&$sJl#$##s3ks3{$D0&1sJp#$##s3)s3H*S\,C#sJG$Ds23&s24sJC#$##&##)##+##/##1##6##9#&@sJ80ShR#T.l#*s5|s5w#l#+s6Fs6i#l#,s6Hs6u#l#-s6Js6`#l#.s6Ls6W#l#/s6Ts6Q#l#.s6[s6X#l#0s6`s6]#l#-s6hs6d#l#1s6ws6t#l#,s7%s6|#l#2s6os6l#l#+s6vs6s#m##s#*-T/-Sh$$#9#%S%l#*s5os5j#l#+s6Xs6{#l#,s6Zs7+#l#-s6\s6r#l#.s6^s6i#l#/s6fs6c#l#.s6ms6j#l#0s6rs6o#l#-s6zs6v#l#1s7-s7*#l#,s77s72#l#2s7%s6~#l#+s7,s7)#m##s5:$D3$D5ZF$#56S%S\l#*s5Js5@#l#+s6is70#l#,s6ks7<#l#-s6ms7'#l#.s6os6z#l#/s6ws6t#l#.s6~s6{#l#0s7's7$#l#-s7/s7+#l#1s7>s7;#l#,s7Hs7C#l#2s76s73#l#+s7=s7:#m##s#L3s5Ls#M4#/Sh&#sKY9#$Svl#*s66s61#l#+s6{s7B#l#,s6}s7N#l#-s7#s79#l#.s7%s70#l#/s7-s7*#l#.s74s71#l#0s79s76#l#-s7As7=#l#1s7Ps7M#l#,s7Zs7U#l#2s7Hs7E#l#+s7Os7L#m##s#[$D39#4Svl#*s54s5/#l#+s7/s7R#l#,s71s7^#l#-s73s7I#l#.s75s7@#l#/s7=s7:#l#.s7Ds7A#l#0s7Is7F#l#-s7Qs7M#l#1s7`s7]#l#,s7js7e#l#2s7Xs7U#l#+s7_s7\#m##s#j3s#ls#k3#.Sh&#sK{9#$Sul#*s6Xs6S#l#+s7As7d#l#,s7Cs7p#l#-s7Es7[#l#.s7Gs7R#l#/s7Os7L#l#.s7Vs7S#l#0s7[s7X#l#-s7cs7_#l#1s7rs7o#l#,s7|s7w#l#2s7js7g#l#+s7qs7n#m##s5+$D39#4Sul#*s5Vs5Q#l#+s7Qs7t#l#,s7Ss8$#l#-s7Us7k#l#.s7Ws7b#l#/s7_s7\#l#.s7fs7c#l#0s7ks7h#l#-s7ss7o#l#1s8&s8##l#,s80s8+#l#2s7zs7w#l#+s8%s7~#m##s5K3s5<s5L3#;s7OHEEGs7#s7Fs7#l#&#s7Es7?l#'s7Ss7R#l#(s7Xs7U#j#)C#k##s9Rs6zk#)C#(T/R#S$l#*'%#l#+s7is80#l#,s7ks8<#l#-s7ms8'#l#.s7os7z#l#/s7ws7t#l#.s7~s7{#l#0s8's8$#l#-s8/s8+#l#1s8>s8;#l#,s8Hs8C#l#2s86s83#l#+s8=s8:#m##s$EUT*s7rOC#GCs7ss6xGC$#P#S|GC&s6zP#S|7Sb#s7s7Sb&#JCs6ySfs6zVT+CSfJC#Sfs6{JC#Sfs6|JC&I#8sLMQC#1Cs7uS:#2s7wHEEG#JQCsLK1Cs7xSo#2s7zHEEG#J6s7{HEEG&#TsL(WS~Cs7##1C(So#2s8#HEEG#JFs8$HEEGs7'#1C.So&2s8&HEEG#J;s8'HEEG#s7zs6D;s8(HEEG&s7{#;s8)HEEG,s7|#l#&#s7{s7ul#'6s8,#l#(<s8/#j#)C#j#4C#j#CC#j#3L#&FSe's7##&SfsL9#S{#&SfsM&k##%#k##%#k##(#k#)C#k#4C#k#CC#k#3L#$DSw(Sh[F$Sw#s#GS=S.S8l#*2&#l#+s8Qs8t#l#,s8Ss9$#l#-s8Us8k#l#.s8Ws8b#l#/s8_s8\#l#.s8fs8c#l#0s8ks8h#l#-s8ss8o#l#1s9&s9##l#,s90s9+#l#2s8zs8w#l#+s9%s8~#m##s%,3s%.s%-s#G#)Sh$#sM-9#$SLl#*s7zs7u#l#+s8cs9*#l#,s8es96#l#-s8gs8}#l#.s8is8t#l#/s8qs8n#l#.s8xs8u#l#0s8}s8z#l#-s9)s9%#l#1s98s95#l#,s9Bs9=#l#2s90s9-#l#+s97s94#m##s5c$D39#4SLl#*s5ls5g#l#+s8ss9:#l#,s8us9F#l#-s8ws91#l#.s8ys9(#l#/s9%s8~#l#.s9,s9)#l#0s91s9.#l#-s99s95#l#1s9Hs9E#l#,s9Rs9M#l#2s9@s9=#l#+s9Gs9D#m##s663s5ts673#$s86sMm-TX$#sMo/T:$D#&$sMg*T:,C#sM</TY&#sMk.T.$D#&$sMn*T.,C#sMC.TZ&#sMr(T;$D#&$sMu*T;,C#sMJ(T<&#sMy)T=$D#$$sMh*T=,C#sMQ)T0$#sMl+Sw$D#&$sMP*Sw,C#sMX+T[&#sMT$DT0&T0sMB*T/,C#sM^&SwsME-T1$s%[#*T1,C#sMc-T\$'#0T2%C#D%C$sNO*T2,C#sMj(T2(T>$$#&%T1*T>,C#sMpj#D&S'j#D&S'ZT?('%$#SPj#E/#j#E/$ZT?10.$#T<j#F4#j#Gs%a#Es%b:8#Sjj#H=#j#IB#Es##B@#SVj#Js#%#j#Ks#+#Es#,s#+s#)#S.j#Ls#/#j#Ms#5#Es#6s#5s#3#S#j#Ns#9#j#Os#?#Es#@s#?s#=#S9j#Ps#C#j#Qs#I#Es#Js#Is#G#SYj#Rs#M#j#Ss#S#Es#Ts#Ss#Q#S'j#6s#W#j#8s8T#Es8Us#[s&I#SM+Sh&#sN.9#$S#l#*s9>s99#l#+s:'s:J#l#,s:)s:V#l#-s:+s:A#l#.s:-s:8#l#/s:5s:2#l#.s:<s:9#l#0s:As:>#l#-s:Is:E#l#1s:Xs:U#l#,s:bs:]#l#2s:Ps:M#l#+s:Ws:T#m##s&Y$D39#4S#l#*s5qs5l#l#+s:7s:e#l#,s:9s:[#l#-s:;s:Q#l#.s:=s:H#l#/s:Es:B#l#.s:Ls:I#l#0s:Qs:N#l#-s:Ys:U#l#1s:^s:[#l#,s:es:b#l#2s:js:g#l#+s:ts:o#m##s&h3s&js&i3#3s&ls&is#%#3s&os&is$$#3s&qs&is$G#3s&us&is%H#3s&ws&is%k#3s&|s&is&2#3s'#s&is&W#1Cs:;Sos$y2s:=HEEG#J;s:>HEEGs$vs:5#;s:?HEEGs$ys:6#;s:@HEEGs%#s:7#l#&#s:6s:0l#'s%-s:C#l#(s%3s:F#j#)C#j#4C#j#CC#j#3L#k##s$ss$sk##s$s#k##s$v#k#)C#k#4C#k#CC#k#3L#l#**#s$nl#+s:`s;'#l#,s:bs;3#l#-s:ds:z#l#.s:fs:q#l#/s:ns:k#l#.s:us:r#l#0s:zs:w#l#-s;&s:~#l#1s;5s;2#l#,s;?s;:#l#2s;-s;*#l#+s;4s;1#m##s',3s'.s'-s#$#j#?s'I#j#Ts'O#V#IFj##s'R#j##s('#5s((s($s'X#Fj#8s(*#j#:s(2#V#IFj##s(9#j##s(|#5s(}s(vs(@#Fj#8s(H#:Cs)(s(T#s)*Fj#8s)*#V#IFj##s)/#j##s)y#5s)zs)qs):#Fj#8s)E#:Cs<xs)P#s67Fj#8s*##V#IFj##s*'#j##s*|#5s*}s*qs*5#Fj#8s*?#:Cs=es*Q#s=sFj#8s+&#V#IFj##s+)#j##s,+#5s,,s+ys+:#Fj#8s+F#:Cs>Os+Z#s>WFj#8s>W#V#IFj##s,3#j##s-7#5s-8s,|s,B#Fj#8s,K#:Cs-;s,_#s-=Fj#8s-=#V#IFj##s-B#j##s.1#5s.2s-~s-V#Fj#8s-b#:Cs@Ds-u#s@YFj#8s.7#V#IFj##s.;#j##s.^#5s._s.Qs.O#Fj#8s.a#j#Us.w#V#IFj##s.{#j##s/D#5s/Es/6s/4#Fj#8s/H#j#Vs/_#V#IFj##s/c#j##s00#5s01s/{s/y#Fj#8s04#j#Ws0M#V#IFj##s0P#j##s1##5s1$s0ks0i#Fj#8s1&#j#Xs1@#V#IFj##s1D#j##s1v#5s1ws1`s1^#Fj#8s1z#j#Bs29#V#IFj##s2=#j##s2{#5s2|s2]s2[#Fj#Ys3##j#Bs3%#V#IFj##s3(#j##s3-#5s3.s3-s3+#Fj#8s30#U#Fj##sJ7#ZT7sJ;sJ8sIks36#FAR(R&#sOh#%#m#'#j#ZsJD#j#[sJF#j#\sJJ#j#]sJM#j#^sJP#j#_sJU#V#IFj##sJY#j##sJt#5sJusJqsJ_#Fj#8sJx#j#`sK$#V#IFj##sK*#j##sKK#5sKLsKEsK3#Fj#8sKQ#j#asK^#V#IFj##sKc#j##sL1#5sL2sL&sKp#Fj#8sL6#j#bsLH#V#IFj##sLN#j##sM%#5sM&sLrsL`#Fj#8sM+#j#csMB#V#IFj##sMH#j##sN)#5sN*sMqsM_#Fj#8sN/#j#dsNK#V#IFj##sNQ#j##sO<#5sO=sO#sNm#Fj#8sOB#j#esOc#V#IFj##sOi#j##sQ:#5sQ;sPHsP.#Fj#8sQA#j#fSt#j#gC#j#hC#j#iC#j#jT@#j#kT@##"). Qed.

(* [comment removed for export] *)
Definition PCH_STACK : Z := 160 + (112 + AASSIGN_STACK).

Definition pch_W (lo : Z) (sp : word) (P IN E : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (P, P + 80); (IN, IN + 8); (E, E + 24); (AG_HTTP_CAT, AG_HTTP_CAT + 64)]%Z.

(* [comment removed for export] *)
Definition pch_post0 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P IN E lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (p0 : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' p' E' c' g',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (pch_W lo sp P IN E) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' P (ParserCoreCells c' pad7 pad2)
    /\ rw_cells bsegs m' IN [C8 (wz p')]
    /\ rw_cells bsegs m' E (ErrCodeCells E')
    /\ rw_cells bsegs m' (P + 288) [C8 (wz 0)]
    /\ bytes_at bsegs m' p0 bs
    /\ pch_out c c' p0 (Z.of_nat (length bs)) p' E'
    /\ AHttpCat m' g' /\ AXStatics2 m'
    /\ ACONST m' /\ stack0 m' lo shi.


(* [comment removed for export] *)
Definition pch_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P IN E lo shi : Z) (LF : list fframe) (c : pcore) (pad7 pad2 : list byte) (p0 : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' p' E' c' g' (XS : list (Z * Z)),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (pch_W lo sp P IN E ++ XS) m m' /\ Forall (fs_scratch H LF) XS          (* [comment removed for export] *)
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' P (ParserCoreCells c' pad7 pad2)
    /\ rw_cells bsegs m' IN [C8 (wz p')]
    /\ rw_cells bsegs m' E (ErrCodeCells E')
    /\ rw_cells bsegs m' (P + 288) [C8 (wz 0)]
    /\ bytes_at bsegs m' p0 bs
    /\ pch_out c c' p0 (Z.of_nat (length bs)) p' E'
    /\ AHttpCat m' g' /\ AXStatics2 m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi.

(* [comment removed for export] *)
Definition pch_pure (sp : word) (P IN E lo shi : Z) (c : pcore) (p0 : Z) (bs : list byte) : Prop :=
  pcore_ok c /\ pc_skip c < 2^62 /\ Z.of_nat (length bs) < 2^62
  /\ stin_pure PCH_STACK sp P IN E lo shi
  /\ aapp P 296 /\ (P + 296 <= E \/ E + 24 <= P)
  /\ aapp p0 (Z.of_nat (length bs))
  /\ (p0 + Z.of_nat (length bs) <= P \/ P + 296 <= p0)
  /\ (p0 + Z.of_nat (length bs) <= E \/ E + 24 <= p0).

Definition pch_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (P IN E lo shi : Z) (c : pcore) (pad7 pad2 : list byte) (p0 : Z) (bs : list byte)
    (E0 : ecv) (g : bool) (s : as_St H) (LB : list block) (LF : list fframe),
  rw_cells bsegs m P (ParserCoreCells c pad7 pad2) ->
  rw_cells bsegs m IN [C8 (wz p0)] ->
  rw_cells bsegs m E (ErrCodeCells E0) ->
  rw_cells bsegs m (P + 288) [C8 (wz 0)] ->
  bytes_at bsegs m p0 bs ->
  AHttpCat m g -> AXStatics2 m ->
  stk bsegs m lo (bv_unsigned sp) ->
  pch_pure sp P IN E lo shi c p0 bs ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi ->
  accessible m P 296 -> accessible m E 24 -> shvis m E (E + 24) -> accessible m p0 (Z.of_nat (length bs)) ->
  (* [comment removed for export] *)
  tp = Z_to_bv 64 ATP -> as_RHEAP H s LB m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat ->
  aobj LB LF P 296 -> aobj LB LF E 24 -> aobj LB LF p0 (Z.of_nat (length bs)) ->
  evt bsegs (pch_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P IN E lo shi LF c pad7 pad2 p0 bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz IN) (wz (Z.of_nat (length bs))) (wz E) a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_BP_PARSE_CHUNK_HEADER) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition APF_TABPTR : Z := 0x123e80.
Definition aoPP (sp : word) : Z := bv_unsigned sp + 144.   (* [comment removed for export] *)
Definition aoVL (sp : word) : Z := bv_unsigned sp + 152.   (* [comment removed for export] *)
Definition aoNM (sp : word) : Z := bv_unsigned sp + 168.   (* [comment removed for export] *)

Definition pf_fail (E' : ecv) : Prop :=
  ec_cat E' = AG_HTTP_CAT /\ ec_failed E' = true /\ ec_ok E' /\ 2 <= ec_flags E'
  /\ In (ec_val E') [HE_NEED_MORE; HE_HEADER_LIMIT; HE_BAD_LINE_ENDING; HE_BAD_FIELD; HE_BAD_VALUE].

(* [comment removed for export] *)
Definition pf_succ (p0 L vb p' nlen vptr vlen bsz : Z) : Prop :=
  p0 + 2 <= p' /\ p' + 1 <= L /\ 1 <= nlen /\ p0 + nlen < p'
  /\ p0 + nlen + 3 <= p' /\ 0 <= vlen /\ nlen + vlen + 3 <= p' - p0
  /\ ((p0 <= vptr /\ 0 <= vlen /\ vptr + vlen <= p') \/ (vptr = vb /\ vlen = bsz)).

Definition pf_out (E0 E' : ecv) (p0 L vb p' : Z) (n1 n2 v1 v2 : word) (bsz : Z) : Prop :=
  (E' = E0 /\ exists nlen vptr vlen, n1 = wz p0 /\ n2 = wz nlen /\ v1 = wz vptr /\ v2 = wz vlen
                /\ pf_succ p0 L vb p' nlen vptr vlen bsz)
  \/ pf_fail E'.

Definition APfTab (m : mem) : Prop := rw_cells bsegs m APF_TABPTR [C8 (wz AL_TAB_IS_TOKEN_LIT)].

(* [comment removed for export] *)
Definition PF_STACK : Z := 192 + (64 + AASSIGN_STACK).

Definition pf_W (lo : Z) (sp : word) (B E : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (bv_unsigned sp + 144, bv_unsigned sp + 184); (B, B + 4104); (E, E + 24);   (* [comment removed for export] *)
   (AG_HTTP_CAT, AG_HTTP_CAT + 64)]%Z.

Definition pf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B E lo shi : Z) (p0 : Z) (bs : list byte) (E0 : ecv) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' p' E' g' (n1 n2 v1 v2 : word) bsz bb,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (pf_W lo sp B E) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (aoPP sp) [C8 (wz p')]
    /\ rw_cells bsegs m' (aoNM sp) [C8 n1; C8 n2]
    /\ rw_cells bsegs m' (aoVL sp) [C8 v1; C8 v2]
    /\ rw_cells bsegs m' B [C8 (wz bsz); CB 4096 bb] /\ 0 <= bsz <= 4096
    /\ rw_cells bsegs m' E (ErrCodeCells E')
    /\ bytes_at bsegs m' p0 bs /\ APfTab m'
    /\ pf_out E0 E' p0 (p0 + Z.of_nat (length bs)) (B + 8) p' n1 n2 v1 v2 bsz
    /\ AHttpCat m' g' /\ AXStatics2 m'
    /\ ACONST m' /\ stack0 m' lo shi.

Definition pf_pure (sp : word) (B E lo shi : Z) (p0 : Z) (bs : list byte) (E0 : ecv) : Prop :=
  ec_ok E0 /\ ec_failed E0 = false
  /\ lo + PF_STACK <= bv_unsigned sp /\ aceil <= lo
  /\ aapp p0 (Z.of_nat (length bs))
  /\ aapp E 24 /\ E mod 8 = 0
  /\ aapp B 4104 /\ B mod 8 = 0
  /\ (p0 + Z.of_nat (length bs) <= E \/ E + 24 <= p0)
  /\ (p0 + Z.of_nat (length bs) <= B \/ B + 4104 <= p0)
  /\ (B + 4104 <= E \/ E + 24 <= B)
  /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp + 184 <= shi.   (* [comment removed for export] *)

Definition pf_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B E lo shi : Z) (p0 : Z) (bs : list byte) (E0 : ecv) (g : bool)
    (nm0 vl0 : list byte) (bsz0 : Z) (bb0 : list byte),
  rw_cells bsegs m (aoPP sp) [C8 (wz p0)] ->
  rw_cells bsegs m (aoNM sp) [CB 16 nm0] ->
  rw_cells bsegs m (aoVL sp) [CB 16 vl0] ->
  rw_cells bsegs m B [C8 (wz bsz0); CB 4096 bb0] -> 0 <= bsz0 <= 4096 ->
  rw_cells bsegs m E (ErrCodeCells E0) ->
  bytes_at bsegs m p0 bs -> APfTab m ->
  AHttpCat m g -> AXStatics2 m ->
  stk bsegs m lo (bv_unsigned sp) ->
  pf_pure sp B E lo shi p0 bs E0 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi ->
  accessible m p0 (Z.of_nat (length bs)) -> shvis m p0 (p0 + Z.of_nat (length bs)) ->
  accessible m E 24 -> shvis m E (E + 24) ->
  accessible m B 4104 -> shvis m B (B + 4104) ->
  evt bsegs (pf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B E lo shi p0 bs E0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (aoPP sp)) (wz (p0 + Z.of_nat (length bs))) (wz (aoNM sp)) (wz (aoVL sp))
              (wz B) (wz E) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_BP_PARSE_FIELD) fc None m (seg_rom bsegs)).

End HCW.
