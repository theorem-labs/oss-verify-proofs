(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
PmLayout PmModel PmStatics PmSpecs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMSX.
Import PMSP.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Definition reader_read_spec : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
(LBX : list (Z * Z)) (cr : credit) (sp r fb cat : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (e : bool),
hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) -> model_ok model -> K [] -> entry A L R M sp r 11 -> frame_ok A L sp fb ->
getr R 10%bv = Z_to_bv 64 (o_p A fb) -> getr R 11%bv = Z_to_bv 64 (o_ec A fb) ->
run_pre segs A M fb s str sm e -> incl (PM.vs_own str) LBX -> (1 <= length (PM.p_stk s))%nat -> ec_at segs M (o_ec A fb) 0 cat ->
PM.unread (PM.p_src s) sm < 2 ^ 26 ->
credit_le (PM.pot_parser L (pst_reset s)) cr ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
regs_preserved R R' ->
parse_post segs A M' fb (pst_reset s) s' str sm sm' e e' ->
L5C.hpres L LBX sp (pm_scr 11) (W_run A fb) M M' ->
credit_keep cr cr' (PM.pot_parser L (pst_reset s)) cr0 ->
model_but_vm model model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
srealizes segs SCFG (cfg segs R' r M' model') K) ->
srealizes segs SCFG (cfg segs R (pa_reader_read A) M model) K.
Definition vec_dtor_spec : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
(LB : list (Z * Z)) (cr : credit) (t v b k sp r : Z) (stk : list PM.pstate),
hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] -> entry A L R M sp r 0 ->
getr R 10%bv = Z_to_bv 64 t -> sp <= t -> t + 8 <= hl_sptop L -> L5.u64_at segs M t v ->
sp <= v -> v + 24 <= hl_sptop L -> v mod 8 = 0 -> L5.defined M v 24 ->
PM.vec_at segs T3 T4 M v b k stk -> In (b, 32 * 2 ^ k) LB ->
(forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
regs_preserved R R' ->
L5C.hpres L (lb_remove b LB) sp (pm_scr 0) [(v, 24)] M M' ->
model_but_vm model model' -> hi_heap HI (lb_remove b LB) cr M' (m_vmmaps model') ->
srealizes segs SCFG (cfg segs R' r M' model') K) ->
srealizes segs SCFG (cfg segs R (pa_vec_dtor A) M model) K.
End Specs.
End PMSX.
