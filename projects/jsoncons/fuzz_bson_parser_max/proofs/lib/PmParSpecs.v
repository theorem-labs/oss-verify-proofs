(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMPS.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

Abbreviation vstr_at := (PM.vstr_at segs PMSP.T3).
Abbreviation iss_at := (PM.iss_at segs A PMSP.T3).
Abbreviation parser_at := (PM.parser_at segs A PMSP.T3 PMSP.T4).
Abbreviation entry := (PMSP.entry A L).
Abbreviation frame_ok := (PMSP.frame_ok A L).
Abbreviation o_p := (PMSP.o_p A).
Abbreviation o_is := (PMSP.o_is A).
Abbreviation o_src := (PMSP.o_src A).
Abbreviation o_tb := (PMSP.o_tb A).
Abbreviation pm_scr := PMSP.pm_scr.

(* [comment removed for export] *)
Definition with_src (s : PM.pst) (src' : PM.srcst) : PM.pst :=
  PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) src' (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xsgetn_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (sp r ois dst : Z) (str : PM.vstr) (sm : PM.strm),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r 2 ->
    getr R 10%bv = Z_to_bv 64 (ois + 16) -> getr R 11%bv = Z_to_bv 64 dst -> getr R 12%bv = Z_to_bv 64 PM.CHUNK ->
    sp <= ois -> ois + 272 <= hl_sptop L -> ois mod 8 = 0 ->
    iss_at M ois str sm -> PMST.base_ok segs A M -> incl (PM.vs_own str) LB ->
    (exists B m, In (B, m) LB /\ B <= dst /\ dst + PM.CHUNK <= B + m) ->
    (dst + PM.CHUNK <= PM.sm_g sm \/ PM.sm_eg sm <= dst) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (c : Z),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 c -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) ->
        iss_at M' ois str (PM.STRM (PM.sm_g sm + c) (PM.sm_eg sm) (PM.sm_st sm)) ->
        L5.defined M' dst c ->
        L5C.hpres L LB sp (pm_scr 2) [(ois + 40, 8); (dst, PM.CHUNK)] M M' ->
        hi_heap HI LB cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model) K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R (pa_xsgetn A) M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition src_spec (pc h : Z) (args : bvmap 5 word -> (word -> option byte) -> Z -> Z -> PM.pst -> Prop)
           (Wx : bvmap 5 word -> list L5.range -> Prop)
           (res : bvmap 5 word -> bvmap 5 word -> (word -> option byte) -> PM.srcst -> PM.srcst -> PM.strm -> PM.strm -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (cr : credit) (sp r fb : Z) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (Wextra : list L5.range),
    hi_heap HI (PM.parser_own s ++ LBX) cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] -> entry R M sp r h -> frame_ok sp fb ->
    getr R 10%bv = Z_to_bv 64 (o_src fb) -> args R M sp fb s -> Wx R Wextra ->
    parser_at M (o_p fb) (o_is fb) s -> iss_at M (o_is fb) str sm -> PMST.base_ok segs A M ->
    incl (PM.vs_own str) LBX ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (src' : PM.srcst) (sm' : PM.strm),
        regs_preserved R R' ->
        parser_at M' (o_p fb) (o_is fb) (with_src s src') ->
        iss_at M' (o_is fb) str sm' -> PMSP.src_step (PM.p_src s) src' sm sm' ->
        res R R' M' (PM.p_src s) src' sm sm' ->
        L5C.hpres L (PM.parser_own s ++ LBX) sp (pm_scr h) (PMSP.W_src A fb (PM.p_src s) ++ Wextra) M M' ->
        hi_heap HI (PM.parser_own s ++ LBX) cr M' (m_vmmaps model) ->
        srealizes segs SCFG (@PMSP.cfg segs fx' R' r M' model) K) ->
    srealizes segs SCFG (@PMSP.cfg segs fx R pc M model) K.

Definition no_args (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop := True.

(* [comment removed for export] *)
Definition fill_args (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  getr R 11%bv = Z_to_bv 64 (PM.sr_qc (PM.p_src s)) /\ getr R 12%bv = Z_to_bv 64 PM.CHUNK.
Definition fill_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  src' = src /\ exists c, getr R' 10%bv = Z_to_bv 64 c /\ 0 <= c <= PM.CHUNK /\ PM.sm_g sm' = PM.sm_g sm + c
    /\ (PM.sm_st sm = 0 -> c = Z.min PM.CHUNK (PM.sm_eg sm - PM.sm_g sm) /\ PM.sm_st sm' = (if Z.ltb c PM.CHUNK then 2 else 0))
    /\ (PM.sm_st sm = 2 -> c = 0 /\ PM.sm_st sm' = 2).
Definition fill_buffer_spec : Prop := src_spec (pa_fill_buffer A) 3 fill_args PMSP.no_W fill_res.

(* [comment removed for export] *)
Definition peek_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  PMSP.consumed src src' sm sm' = 0 /\
  (getr R' 10%bv = Z_to_bv 64 256 \/ (exists c, 0 <= c < 256 /\ getr R' 10%bv = Z_to_bv 64 c /\ 1 <= PM.sr_rem src')).
Definition peek_spec : Prop := src_spec (pa_peek A) 4 no_args PMSP.no_W peek_res.

(* [comment removed for export] *)
Definition ignore_args (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop := getr R 11%bv = Z_to_bv 64 1.
Definition ignore_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  (PMSP.consumed src src' sm sm' = 1 \/ PMSP.consumed src src' sm sm' = 0) /\ (1 <= PM.sr_rem src -> PMSP.consumed src src' sm sm' = 1).
Definition ignore_spec : Prop := src_spec (pa_ignore A) 4 ignore_args PMSP.no_W ignore_res.

(* [comment removed for export] *)
Definition read_dst (M : word -> option byte) (sp fb : Z) (s : PM.pst) (p k : Z) : Prop :=
  (sp <= p /\ p + k <= fb /\ k <= 8 /\ L5.defined M p k)
  \/ ((exists n, PM.p_tb s = PM.VShort n) /\ o_tb fb + 1 <= p /\ p + k <= o_tb fb + 24)
  \/ (exists c n q, PM.p_tb s = PM.VLong c n q /\ q <= p /\ p + k <= q + c).
Definition read_args (R : bvmap 5 word) (M : word -> option byte) (sp fb : Z) (s : PM.pst) : Prop :=
  exists p k, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 k /\ 1 <= k <= PM.CHUNK /\ read_dst M sp fb s p k.
Definition read_W (R : bvmap 5 word) (W : list L5.range) : Prop :=
  exists p k, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 k /\ 0 <= p < 2 ^ 64 /\ 0 <= k < 2 ^ 64 /\ W = [(p, k)].
Definition read_res (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  exists p k d, getr R 11%bv = Z_to_bv 64 p /\ getr R 12%bv = Z_to_bv 64 k /\ 0 <= p < 2 ^ 64 /\ 1 <= k <= PM.CHUNK
    /\ getr R' 10%bv = Z_to_bv 64 d /\ 0 <= d <= k
    /\ PMSP.consumed src src' sm sm' = d /\ L5.defined M' p d
    /\ (1 <= PM.sr_rem src -> 1 <= d) /\ (d = 0 -> PM.sr_rem src' = 0 /\ PM.sm_st sm' = 2).
Definition src_read_spec : Prop := src_spec (pa_src_read A) 4 read_args read_W read_res.

End Specs.
End PMPS.
