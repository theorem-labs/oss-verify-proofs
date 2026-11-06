(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXRep_fields AXRep_mbuf.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape RBTac RBSafe DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition MB_DEREF_STACK : Z := 16.                        (* [comment removed for export] *)
Definition MB_SR_STACK : Z := 64 + AINTRIN_STACK.           (* [comment removed for export] *)
Definition MB_COMMIT_STACK : Z := 64 + AINTRIN_STACK.       (* [comment removed for export] *)
Definition MB_BCOPY_STACK : Z := 112 + AINTRIN_STACK.       (* [comment removed for export] *)
Definition MB_ALLOC_STACK : Z := 112 + AOPNEW_STACK.        (* [comment removed for export] *)
Definition MB_PREP_STACK : Z := 304 + MB_ALLOC_STACK.       (* [comment removed for export] *)
Definition MB_DBP_STACK : Z := 208 + MB_PREP_STACK.         (* [comment removed for export] *)
Definition PUT_STACK : Z := 176 + MB_DBP_STACK.             (* [comment removed for export] *)
Definition OBI_STACK : Z := 32 + PUT_STACK.                 (* [comment removed for export] *)
Definition OCB_STACK : Z := 144 + PUT_STACK.                (* [comment removed for export] *)

Lemma PUT_STACK_val : PUT_STACK = 9008. Proof. reflexivity. Qed.
Lemma OBI_STACK_val : OBI_STACK = 9040. Proof. reflexivity. Qed.
Lemma OCB_STACK_val : OCB_STACK = 9152. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mb_new_blocks (es : list mbe) (insz n : Z) (p : bptr) (x : Z) : list block :=
  if mb_need es insz n then [(p, x, mb_block_size (mb_grow es insz n))] else [].

(* [comment removed for export] *)
Definition mb_off (b : Z) (es : list mbe) (A n : Z) : Prop :=
  (A + n <= b \/ b + 64 <= A) /\ forall x s, In (x, s) es -> A + n <= x \/ x + mb_block_size s <= A.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

(* [comment removed for export] *)
Definition put_cost (es : list mbe) (insz n : Z) : Z :=
  if mb_need es insz n then as_Cm H (mb_block_size (mb_grow es insz n)) else 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition put_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (b : Z) (es : list mbe) (insz n src E lo B shi : Z) (bs : list byte)
    (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p : bptr) (x : Z) (XS : list (Z * Z)),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ as_RHEAP H s' (mb_new_blocks es insz n p x ++ LB) m'
    /\ (mb_need es insz n = true -> rblock_range x (mb_block_size (mb_grow es insz n)))
    /\ AMBuf m' b (mb_put_es es insz n x) (insz + n)
    /\ AMBufOwn (mb_new_blocks es insz n p x ++ LB) (mb_put_es es insz n x)
    /\ rw_cells bsegs m' E (ErrCodeCells EC_clear)
    /\ bytes_at bsegs m' src bs
    /\ Forall (fs_scratch H LF) XS
    /\ xpres H LB (bv_unsigned sp) (((E, E + 24) :: (b, b + 64) :: mb_elemsW es) ++ XS) m m'
    (* [comment removed for export] *)
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ accessible m' E 24 /\ accessible m' src n
    /\ as_AL H s' >= as_AL H s - put_cost es insz n.

(* [comment removed for export] *)
Definition put_pre (K : Prop) (sp ra tp : word) (msF : machine_state) (m : mem) (mo : Model)
    (s : as_St H) (LB : list block) (LF : list fframe) (rd b : Z) (es : list mbe) (insz n src E lo B shi : Z)
    (bs ej : list byte) (errv : word) : Prop :=
  AMBuf m b es insz -> AMBufOwn LB es -> 1 <= n -> insz + n <= 2^26 ->     (* [comment removed for export] *)
  rw_cells bsegs m rd [C8 (wz b)] ->
  rw_cells bsegs m E [CB 24 ej] ->
  (rd + 8 <= E \/ E + 24 <= rd) ->
  bytes_at bsegs m src bs -> zlength bs = n ->
  (src + n <= E \/ E + 24 <= src) ->
  as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
  (mb_need es insz n = true -> lb_bytes LB + mb_block_size (mb_grow es insz n) <= as_LIVE_MAX H) ->
  (mb_need es insz n = true -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H) ->
  as_rauxv_ok H m B -> bv_unsigned sp <= B ->
  stk bsegs m lo (bv_unsigned sp) -> aceil <= lo ->
  bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
  rw_cells bsegs m (errno_addr tp) [C4 errv] -> mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  aobj LB LF b 64 ->
  aobj LB LF rd 8 -> rd mod 8 = 0 -> accessible m rd 8 -> mb_off b es rd 8 ->
  aobj LB LF E 24 -> E mod 8 = 0 -> accessible m E 24 -> mb_off b es E 24 ->
  aobj LB LF src n -> accessible m src n -> mb_off b es src n ->
  as_RFS H LF m -> (length LF + 3 < AFS_MAXLIVE)%nat -> ACONST m ->
  stack0 m lo shi -> bv_unsigned sp <= shi ->
  (mb_need es insz n = true -> as_Cm H (mb_block_size (mb_grow es insz n)) <= as_AL H s) ->
  K.

(* [comment removed for export] *)
Definition put_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (rd cbp b : Z) (es : list mbe) (insz n src E lo B shi : Z)
         (bs ej : list byte) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_READER_PUT) fc None m (seg_rom bsegs) ->
    a0 = wz rd -> a1 = wz cbp -> a2 = wz E ->
    rw_cells bsegs m cbp [C8 (wz src); C8 (wz n)] -> bv_unsigned sp <= cbp -> cbp + 16 <= shi -> cbp mod 8 = 0 ->
    lo <= bv_unsigned sp - PUT_STACK ->
    put_pre
      (as_SR H (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF b es insz n src E lo B shi bs m mo)
         (mkCfg msF mo))
      sp ra tp msF m mo s LB LF rd b es insz n src E lo B shi bs ej errv.

(* [comment removed for export] *)
Definition obi_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (P b : Z) (es : list mbe) (insz n src E lo B shi : Z)
         (bs ej : list byte) (errv : word),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_ON_BODY_IMPL) fc None m (seg_rom bsegs) ->
    a0 = wz P -> a1 = wz src -> a2 = wz n -> a3 = wz E ->
    0 <= P ->
    lo <= bv_unsigned sp - OBI_STACK ->
    put_pre
      (as_SR H (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF b es insz n src E lo B shi bs m mo)
         (mkCfg msF mo))
      sp ra tp msF m mo s LB LF (P + 232) b es insz n src E lo B shi bs ej errv.

(* [comment removed for export] *)
Definition ocb_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (P rem b : Z) (es : list mbe) (insz n src E lo B shi : Z)
         (bs ej : list byte) (errv : word) (r344 : list cell),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_ON_CHUNK_BODY_IMPL) fc None m (seg_rom bsegs) ->
    a0 = wz P -> a1 = wz rem -> a2 = wz src -> a3 = wz n -> a4 = wz E -> 0 <= rem < 2^64 ->
    0 <= P ->
    rw_cells bsegs m (P + 336) (C8 (wz 0) :: r344) -> (P + 336) mod 8 = 0 -> accessible m (P + 336) 8 ->
    (P + 336 + Z.of_nat (cells_size (C8 (wz 0) :: r344)) <= lo \/ bv_unsigned sp <= P + 336) ->
    lo <= bv_unsigned sp - OCB_STACK ->                  (* [comment removed for export] *)
    (length LF + 4 < AFS_MAXLIVE)%nat ->                 (* [comment removed for export] *)
    put_pre
      (as_SR H (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF b es insz n src E lo B shi bs m mo)
         (mkCfg msF mo))
      sp ra tp msF m mo s LB LF (P + 232) b es insz n src E lo B shi bs ej errv.

End HCW.
