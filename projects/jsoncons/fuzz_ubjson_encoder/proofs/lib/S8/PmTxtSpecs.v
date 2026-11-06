(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmStatics PmSpecs PmParSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMTXS.
Import PMSP.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation parser_at := (PM.parser_at segs A PMSP.T3 PMSP.T4).
Abbreviation iss_at := (PM.iss_at segs A PMSP.T3).
Abbreviation entry := (PMSP.entry A L).
Abbreviation frame_ok := (PMSP.frame_ok A L).
Abbreviation o_p := (PMSP.o_p A).
Abbreviation o_is := (PMSP.o_is A).
Abbreviation o_src := (PMSP.o_src A).
Abbreviation o_tb := (PMSP.o_tb A).

Definition tbfill_args (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  exists p, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 PM.CHUNK /\
    exists c n q, PM.p_tb s = PM.VLong c n q /\ q <= p /\ p + PM.CHUNK <= q + c.
Definition tbfill_W (R : bvmap 5 word) (W : list L5.range) : Prop :=
  exists p, getr R 11%bv = Z_to_bv 64 p /\ 0 <= p < 2 ^ 64 /\ W = [(p, PM.CHUNK)].
Definition tbfill_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  PMPS.fill_res R R' M' src src' sm sm' /\ exists p c, getr R 11%bv = Z_to_bv 64 p /\ getr R' 10%bv = Z_to_bv 64 c /\ L5.defined M' p c.
Definition fill_buffer_tb_spec : Prop := PMPS.src_spec segs A L HI (pa_fill_buffer A) 3 tbfill_args tbfill_W tbfill_res.

Definition srd_read_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb len : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) -> model_ok model -> K [] -> entry R M sp r 5 -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_src fb) -> getr R 11%bv = Z_to_bv 64 (o_tb fb) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    parser_at M (o_p fb) (o_is fb) s -> iss_at M (o_is fb) str sm -> PMST.base_ok segs A M -> PM.tb_ok (PM.p_tb s) (PM.p_tg s) ->
    incl (PM.vs_own str) LBX -> PM.unread (PM.p_src s) sm < 2 ^ 26 -> PM.vs_size (PM.p_tb s) + PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    credit_le (PM.pot_text L (PM.p_tb s) (PM.p_tg s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        PMSP.consumed (PM.p_src s) (PM.p_src s') sm sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s) + d ->
        parser_at M' (o_p fb) (o_is fb) s' -> iss_at M' (o_is fb) str sm' -> PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
        PM.p_more s' = PM.p_more s -> PM.p_done s' = PM.p_done s -> PM.p_depth s' = PM.p_depth s ->
        PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s -> PM.p_stk s' = PM.p_stk s ->
        PMSP.src_step (PM.p_src s) (PM.p_src s') sm sm' ->
        L5C.hpres L LBX sp (pm_scr 5) (W_srcf A fb ++ [(o_tb fb, 24)]) M M' ->
        credit_keep cr cr' (PM.pot_text L (PM.p_tb s) (PM.p_tg s)) (PM.pot_text L (PM.p_tb s') (PM.p_tg s')) ->
        model_but_vm model model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R (pa_srd_read A) M model) K.

End Specs.
End PMTXS.
