(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PeCLayout PeCSink PeCModel PeCSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECTXS.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

(* [comment removed for export] *)
Definition cstr_resize_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o n sp r tg : Z) (s : PM.vstr),
    hi_heap HI (PM.vs_own s ++ LB) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> PMSP.entry A L R M sp r 1 ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> sp <= o -> o + 24 <= hl_sptop L -> o mod 8 = 0 ->
    PM.vstr_at segs PMSP.T3 M o s -> PM.tb_ok s tg -> 0 <= n <= PM.vs_size s + PM.CHUNK -> n < 2 ^ 26 + PM.CHUNK ->
    PMSP.credit_le (PM.pot_text L s tg) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.vstr) (tg' : Z) (cr' : credit),
        regs_preserved R R' -> PM.vstr_at segs PMSP.T3 M' o s' -> PM.vs_size s' = n -> PM.tb_ok s' tg' ->
        (forall l, Z.of_nat (length l) <= Z.min n (PM.vs_size s) -> L5.bytes_at segs M (PM.vs_data o s) l -> L5.bytes_at segs M' (PM.vs_data o s') l) ->
        (n <= PM.vs_cap s -> PM.vs_own s' = PM.vs_own s /\ tg' = tg) ->
        L5C.hpres L LB sp (PMSP.pm_scr 1) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PM.pot_text L s tg) (PM.pot_text L s' tg') ->
        model_but_vm model model' -> hi_heap HI (PM.vs_own s' ++ LB) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R (pa_str_resize A) M model) K.

(* [comment removed for export] *)
Definition csrd_read_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb len : Z) (pl tl : list Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> PMSP.entry A L R M sp r 5 -> PMSP.frame_ok A L sp fb ->
    getr R 10%bv = Z_to_bv 64 (PMSP.o_src A fb) -> getr R 11%bv = Z_to_bv 64 (PMSP.o_tb A fb) -> getr R 12%bv = Z_to_bv 64 len -> 0 <= len < 2 ^ 64 ->
    PM.parser_at segs A PMSP.T3 PMSP.T4 M (PMSP.o_p A fb) (PMSP.o_is A fb) s -> PM.iss_at segs A PMSP.T3 M (PMSP.o_is A fb) str sm ->
    PMST.base_ok segs A M -> PM.tb_ok (PM.p_tb s) (PM.p_tg s) ->
    incl (PM.vs_own str) LBX -> PM.unread (PM.p_src s) sm < 2 ^ 26 -> PM.vs_size (PM.p_tb s) + PM.unread (PM.p_src s) sm < 2 ^ 26 ->
    PECS.payload_ok pl -> PEC.content_ok segs A M fb pl (PM.p_src s) str sm ->
    Z.of_nat (length tl) = PM.vs_size (PM.p_tb s) -> L5.bytes_at segs M (PM.vs_data (PMSP.o_tb A fb) (PM.p_tb s)) tl ->
    PMSP.credit_le (PM.pot_text L (PM.p_tb s) (PM.p_tg s)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
        PMSP.consumed (PM.p_src s) (PM.p_src s') sm sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s) + d ->
        d = Z.min len (PM.unread (PM.p_src s) sm) ->
        L5.bytes_at segs M' (PM.vs_data (PMSP.o_tb A fb) (PM.p_tb s')) (tl ++ UbjRef.slice pl (PEC.pos_of pl (PM.p_src s) sm) d) ->
        PM.parser_at segs A PMSP.T3 PMSP.T4 M' (PMSP.o_p A fb) (PMSP.o_is A fb) s' -> PM.iss_at segs A PMSP.T3 M' (PMSP.o_is A fb) str sm' ->
        PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
        PM.p_more s' = PM.p_more s -> PM.p_done s' = PM.p_done s -> PM.p_depth s' = PM.p_depth s ->
        PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s -> PM.p_stk s' = PM.p_stk s ->
        PMSP.src_step (PM.p_src s) (PM.p_src s') sm sm' ->
        PEC.content_ok segs A M' fb pl (PM.p_src s') str sm' ->
        L5C.hpres L LBX sp (PMSP.pm_scr 5) (PMSP.W_srcf A fb ++ [(PMSP.o_tb A fb, 24)]) M M' ->
        PMSP.credit_keep cr cr' (PM.pot_text L (PM.p_tb s) (PM.p_tg s)) (PM.pot_text L (PM.p_tb s') (PM.p_tg s')) ->
        model_but_vm model model' -> hi_heap HI (PM.parser_own s' ++ LBX) cr' M' (m_vmmaps model') ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R (pa_srd_read A) M model) K.

End Specs.
End PECTXS.
