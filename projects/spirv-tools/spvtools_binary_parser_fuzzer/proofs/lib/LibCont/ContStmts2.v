(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff
  SumMemcpyBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Export ContStmts ContStmts3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Stmts2.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

#[local] Notation cfg fx R pc M model :=
  (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
#[local] Abbreviation vec32 := (CRep.vec32 MI).
#[local] Abbreviation vec_opnd := (CRep.vec_opnd MI).
#[local] Abbreviation NEW_STACK := (ContStmts.NEW_STACK SEGS L MI).
#[local] Abbreviation callB := (LibEff.callB MI ST).
#[local] Abbreviation retB := (LibEff.retB MI ST).
#[local] Abbreviation roomL := (LibEff.roomL MI).

Definition vec32_push_backU_stmt (xb : Z) (c : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret v b cap src x : Z) (xs : list Z) (K : TSet),
    let STK := vc_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 src ->
    vec32 A M v b xs cap -> obj_ok MI A sp STK v 24 -> v mod 8 = 0 ->
    fld SEGS M src 4 x -> 0 <= x < xb -> obj_ok MI A sp STK src 4 -> 0 <= src -> src + 4 <= 2 ^ 63 -> src mod 4 = 0 ->
    (forall a, zwin src (src + 4) a -> ~ zwin v (v + 24) a) ->
    4 * vgrow cap <= NMAX MI ->
    (Zlen xs = cap -> roomL A (live MI A) (4 * vgrow cap)) ->
    (forall A' R' M' model' (b' cap' : Z),
        retB A' s R R' M' model model' ->
        vec32 A' M' v b' (xs ++ [x]) cap' ->
        (Zlen xs < cap /\ b' = b /\ cap' = cap /\ live MI A' = live MI A
         \/ Zlen xs = cap /\ cap' = vgrow cap /\ lapply (live MI A) (LAdd b' (4 * cap') :: del_if b) (live MI A')) ->
        eff MI A A' M M' (sp - STK, sp)
            (fun a => zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + 4 * cap) a) \/ zwin b' (b' + 4 * cap') a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry c) M model) K.

Definition vec_opnd_pbslow_stmt (c : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret v b cap src : Z) (K : TSet),
    let STK := vc_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 src ->
    vec_opnd A M v b cap cap -> obj_ok MI A sp STK v 24 -> v mod 8 = 0 -> ro_clear L M ->
    mdef M src 20 -> obj_ok MI A sp STK src 20 -> 0 <= src -> src + 20 <= 2 ^ 63 -> src mod 4 = 0 ->
    (forall a, zwin src (src + 20) a -> ~ zwin v (v + 24) a) ->
    OPND_SZ * vgrow cap <= NMAX MI ->
    roomL A (live MI A) (OPND_SZ * vgrow cap) ->
    (forall A' R' M' model' (b' : Z),
        retB A' s R R' M' model model' ->
        vec_opnd A' M' v b' (cap + 1) (vgrow cap) ->
        getr R' 10%bv = Z_to_bv 64 (b' + OPND_SZ * (cap + 1)) ->
        lapply (live MI A) (LAdd b' (OPND_SZ * vgrow cap) :: del_if b) (live MI A') ->
        eff MI A A' M M' (sp - STK, sp)
            (fun a => zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + OPND_SZ * cap) a) \/ zwin b' (b' + OPND_SZ * vgrow cap) a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry c) M model) K.
#[local] Abbreviation str_rep := (CRep.str_rep MI).

Definition makestringU_stmt (c : str_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret p w nw : Z) (ws : list Z) (K : TSet),
    let STK := sc_ms_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 w -> getr R 12%bv = Z_to_bv 64 nw ->
    0 <= p -> p + 24 <= 2 ^ 63 -> mdef M p 24 -> obj_ok MI A sp STK p 24 ->
    0 <= nw -> Zlen ws = nw -> 0 <= w -> w + 4 * nw <= 2 ^ 63 -> w mod 4 = 0 ->
    (forall i, 0 <= i < nw -> 0 <= Znth i ws < 2 ^ 32 /\ fld SEGS M (w + 4 * i) 4 (Znth i ws)) ->
    obj_ok MI A sp STK w (4 * nw) ->
    (forall a, zwin w (w + 4 * nw) a -> ~ zwin p (p + 24) a) ->
    8 * nw + 48 <= NMAX MI ->
    (forall n, str_gsize n -> n <= 8 * nw + 2 ->
       (n < BIG MI -> LibIface.count_class SEGS L MI A (size_class MI n) + 2 <= caps MI A (size_class MI n)
                      /\ LibIface.count_class SEGS L MI A (size_class MI n + 1) + 2 <= caps MI A (size_class MI n + 1))
       /\ (BIG MI <= n -> LibIface.big_bytes SEGS L MI A + 2 * round_big MI n <= bigcap MI A)) ->
    (forall A' R' M' model' (m' : sbuf) (J : Z -> Prop),
        retB A' s R R' M' model model' ->
        str_rep A' M' p m' (ms_chars ws) ->
        (forall q k, In (q, k) (live MI A') <-> In (q, k) (live MI A) \/ In (q, k) (str_blocks m')) ->
        (forall q k, In (q, k) (str_blocks m') -> ~ In q (map fst (live MI A))) ->
        junk_ok MI A J ->
        sbuf_asz_le m' (8 * nw + 2) ->
        eff MI A A' M M' (sp - STK, sp) (fun a => zwin p (p + 24) a \/ sbuf_fp m' a \/ J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (sc_makestring c) M model) K.
End Stmts2.
