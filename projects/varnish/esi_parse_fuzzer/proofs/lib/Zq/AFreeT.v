(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv ARtStmts ARtSscs AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH0.

Module AFreeD.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 AMTac ARt2_lib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt2gfb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw ARt20wx ARtSoqz ARtSnjd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt22wr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt4chi AIcpnnp AFreeH AFreeH0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx.ARt27j4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2gfb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22wr.ARt2mo1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt4chi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
Definition free_dtail_W (sp : word) (thr : Z) : list (Z * Z) :=
  [(bv_unsigned sp + -2128 + -80 - 48, bv_unsigned sp + -2128 + -80); (QINST + 152, QINST + 156); (QINST + 160, QINST + 192); (thr + 80, thr + 112)].
Definition free_dtail_WA (sp : word) (thr gl : Z) : list (Z * Z) :=
  [(bv_unsigned sp + -2128 + -80 - 48, bv_unsigned sp + -2128 + -80); (QINST + 152, QINST + 156); (QINST + 160, QINST + 192); (thr + 80, thr + 112); (gl, gl + 8)].
Definition free_dtailR_W := free_dtail_W.
Definition free_dtailR_WA := free_dtail_WA.

(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TfIncl.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_with_region B S a n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TfIncl.tf_with_region_fast B S a n.
(* [comment removed for export] *)

Section FreeTail.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p n b1 tsd ctx thr top bot r8 n0 f0 fr fd : Z) (D : list (list Z)) (old : word) (oldsh : list byte).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 2688.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RANE : bv_unsigned ra <> 0x58994.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis VLE : bv_unsigned s0 <= bv_unsigned sp.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
  Hypothesis TPE : tp = Z_to_bv 64 TP.
  (* [comment removed for export] *)
  Hypothesis PAL : p mod 16 = 0.
  Hypothesis PLO : aobj (p + -16) (16 + 8 * r8).   (* [comment removed for export] *)
  Hypothesis PNB : 0x60a000 <= p + -16.             (* [comment removed for export] *)
  Hypothesis PHI : p + 8 * r8 <= alloc_ceiling.
  Hypothesis NR : 1 <= n < 2^32.
  Hypothesis NQ : n <= 2^28.
  Hypothesis R8 : 8 * r8 - 8 < n <= 8 * r8.
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 3 = 1.
  Hypothesis HDR : rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)].
  Hypothesis CTX0 : rw_cells rsegs m p [C8 old].
  Hypothesis SHC : rw_cells rsegs m (sh p) [CB (Z.to_nat r8) oldsh].
  (* [comment removed for export] *)
  Hypothesis FCo : free_consts m.
  Hypothesis PCo : poison_consts m.
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (wz ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (wz kMainTid)].
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)].
  Hypothesis TDT : ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis TST : rw_cells rsegs m (thr + 2824) [C8 (wz fr); C8 (wz fd)].
  Hypothesis FRR : 0 <= fr < 2^64.
  Hypothesis FDR : 0 <= fd < 2^64.
  (* [comment removed for export] *)
  Hypothesis DR : depot_repL AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 3 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SEP_pc : apart (p + -16) (8 * r8 + 16) ctx 0x10000.
  Hypothesis SEP_pt : apart (p + -16) (8 * r8 + 16) thr 4096.
  Hypothesis SEP_pn : apart (p + -16) (8 * r8 + 16) n0 kDepotNodesBlock.
  Hypothesis SEP_pf : apart (p + -16) (8 * r8 + 16) f0 kStackStoreBlockBytes.
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).
  Let KEY : list Z := free_key top bot fp ra.
  Let D' : list (list Z) := fst (depot_putC D KEY).
  Let fid : Z := snd (depot_putC D KEY).


  Definition free_dtail0_post (W0 : list (Z * Z)) (m0 m7 : word -> option byte) (nb fb lb qb rl hi gf gl gqb : Z) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (W0 ++ free_dtail_W sp thr) m0 m' /\ wmono rsegs m0 m'
    /\ munch (free_dtail_W sp thr) m7 m' /\ wmono rsegs m7 m'
    /\ mem_inv rsegs m' /\ stk rsegs m' lo fp
    /\ rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (thr + 8) [C8 (wz top); C8 (wz bot)]
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' (thr + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
    /\ rw_cells rsegs m' (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)]
    /\ rw_cells rsegs m' (QINST + 160) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz (gqb + qb))].

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition free_dtailA_post (W0 : list (Z * Z)) (m0 m7 : word -> option byte) (nb fb lb qb rl hi gn gf gl gqb : Z) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (W0 ++ free_dtail_WA sp thr gl) m0 m' /\ wmono rsegs m0 m'
    /\ munch (free_dtail_WA sp thr gl) m7 m' /\ wmono rsegs m7 m'
    /\ mem_inv rsegs m' /\ stk rsegs m' lo fp
    /\ rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (thr + 8) [C8 (wz top); C8 (wz bot)]
    /\ rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))]
    /\ rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)]
    /\ rw_cells rsegs m' p [C8 (wz fid)]
    /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
    /\ depot_repL AL_pboth rsegs D' n0 f0 m'
    /\ rw_cells rsegs m' (thr + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
    /\ rw_cells rsegs m' (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 rl); C2 (wz hi)]
    /\ rw_cells rsegs m' (QINST + 160) [C8 (wz (gn + nb)); C8 (wz gf); C8 (wz lb); C8 (wz (gqb + qb))]
    /\ rw_cells rsegs m' gl [C8 (wz fb)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End FreeTail.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
End AFreeD.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT.AFreeD.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module AFreeN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 AMTac ARt2_lib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt2gfb ARt22fz AIcpnnp AFreeH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt2gfb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx.ARt27j4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2gfb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22fz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2gfb.AFreeM0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition dealloc_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists m',
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz dealloc_entry) fc None m (seg_rom rsegs)).

Theorem dealloc_null_ok : dealloc_null_stmt.
Proof.
  unfold dealloc_null_stmt. intros until lo. intros MI ST LOLE CEIL RA.
  pose proof alloc_ceiling_val as CV. unfold dealloc_entry in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 64%nat ST.
  do 10 amz. if_true. (* [comment removed for export] *)
  do 10 amz.          (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
Qed.

End CEIL.

(* [comment removed for export] *)
Definition free_null_W (sp : word) (lo thr : Z) : list (Z * Z) := [(lo, bv_unsigned sp); (thr + 3168, thr + 3168 + 1)].
Definition free_null0_W (sp : word) (lo thr : Z) : list (Z * Z) :=
  free_null_W sp lo thr ++
  [(0x144648, 0x14464c); (IAB, IAB + 1); (IAB + 8, IAB + 8 + 262144); (IAB + 0x40040, IAB + 0x40040 + 3456);
   (IAB + 0x40dc0, IAB + 0x40dc0 + 262728); (IAB + 0x81008, IAB + 0x81008 + 40)].

Section FreeNull.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo tsd ctx thr top bot : Z).

  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 2688.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis RA0 : 4096 <= bv_unsigned ra.
  Hypothesis RANE : bv_unsigned ra <> 0x58994.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis VLE : bv_unsigned s0 <= bv_unsigned sp.
  Hypothesis TOPR : 0 <= top < 2^64.
  Hypothesis BOTR : 0 <= bot < 2^64.
  Hypothesis TPE : tp = Z_to_bv 64 TP.
  (* [comment removed for export] *)
  Hypothesis FCo : free_consts m.
  Hypothesis PCo : poison_consts m.
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TTB : rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)].
  Hypothesis TDT : ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)].
  Hypothesis TUNW : rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).

  Definition free_null_post : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (free_null_W sp lo thr) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo fp
    /\ rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (thr + 8) [C8 (wz top); C8 (wz bot)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition free_null0_post (hi : Z) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (free_null0_W sp lo thr) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo fp
    /\ rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (thr + 8) [C8 (wz top); C8 (wz bot)]
    (* [comment removed for export] *)
    /\ rw_cells rsegs m' 0x144648 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (wz hi)]
    /\ rw_cells rsegs m' IAB [C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' (IAB + 8) [CB (Z.to_nat 262144) (repeat (Z_to_bv 8 0) (Z.to_nat 262144))]
    /\ u64arr rsegs m' (IAB + 0x40040) (repeat (wz 0) 432)
    /\ rw_cells rsegs m' (IAB + 0x40dc0) [C8 (wz 4096); C8 (wz (IAB + 0x40dd0)); CB (Z.to_nat 262712) (repeat (Z_to_bv 8 0) (Z.to_nat 262712))]
    /\ rw_cells rsegs m' (IAB + 0x81008) [CB 40 (repeat (Z_to_bv 8 0) 40)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End FreeNull.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
End AFreeN.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ia_pre0 (m : mem) : Prop :=
     rw_cells rsegs m 0x144648 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]
  /\ rw_cells rsegs m IAB [C1 (Z_to_bv 8 0)]
  /\ rw_cells rsegs m (IAB + 8) [CB (Z.to_nat 262144) (repeat (Z_to_bv 8 0) (Z.to_nat 262144))]
  /\ u64arr rsegs m (IAB + 0x40040) (repeat (wz 0) 432)
  /\ rw_cells rsegs m (IAB + 0x40dc0) [CB (Z.to_nat 262728) (repeat (Z_to_bv 8 0) (Z.to_nat 262728))]
  /\ rw_cells rsegs m (IAB + 0x81008) [CB 40 (repeat (Z_to_bv 8 0) 40)].
(* [comment removed for export] *)
Definition ia_post0 (m : mem) : Prop :=
     rw_cells rsegs m 0x144648 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (wz 0)]
  /\ rw_cells rsegs m IAB [C1 (Z_to_bv 8 0)]
  /\ rw_cells rsegs m (IAB + 8) [CB (Z.to_nat 262144) (repeat (Z_to_bv 8 0) (Z.to_nat 262144))]
  /\ u64arr rsegs m (IAB + 0x40040) (repeat (wz 0) 432)
  /\ rw_cells rsegs m (IAB + 0x40dc0) [C8 (wz 4096); C8 (wz (IAB + 0x40dd0)); CB (Z.to_nat 262712) (repeat (Z_to_bv 8 0) (Z.to_nat 262712))]
  /\ rw_cells rsegs m (IAB + 0x81008) [CB 40 (repeat (Z_to_bv 8 0) 40)].
(* [comment removed for export] *)
Definition ia_pre (ia0 : bool) (m : mem) : Prop := if ia0 then ro_cells rsegs m 0x144648 [C1 (Z_to_bv 8 1)] else ia_pre0 m.
Definition ia_post (ia0 : bool) (m : mem) : Prop := if ia0 then True else ia_post0 m.
(* [comment removed for export] *)
Definition ia_W : list (Z * Z) :=
  [(0x144648, 0x14464c); (IAB, IAB + 1); (IAB + 8, IAB + 8 + 262144); (IAB + 0x40040, IAB + 0x40040 + 3456);
   (IAB + 0x40dc0, IAB + 0x40dc0 + 262728); (IAB + 0x81008, IAB + 0x81008 + 40)].
Definition ia_Wk (ia0 : bool) : list (Z * Z) := if ia0 then [] else ia_W.

(* [comment removed for export] *)

Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[u w] W IH]; intros a n a' n' D H1 H2; cbn [disjoint_from] in *; [exact I|].
  destruct D as [D1 D2]. split; [lia| exact (IH _ _ _ _ D2 H1 H2)].
Qed.

(* [comment removed for export] *)
Lemma ia_post_xfer : forall ia0 W (m m' : mem),
  ia_post ia0 m -> munch W m m' -> wmono rsegs m m' -> disjoint_from W 0x144648 4 -> disjoint_from W IAB 0x81030 ->
  ia_post ia0 m'.
Proof.
  intros ia0 W m m' P MU WM D1 D2. destruct ia0; [exact I|]. cbn [ia_post] in P |- *. unfold ia_post0, IAB in *.
  (first [ dand6 P as P1 P2 P3 P4 P5 P6 | destruct P as (P1 & P2 & P3 & P4 & P5 & P6) ]).
  split; [eapply rw_cells_transport; [exact P1| exact MU| exact WM| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; exact D1]|].
  split; [eapply rw_cells_transport; [exact P2| exact MU| exact WM| apply (disjoint_from_sub _ _ _ _ _ D2); cbn; lia]|].
  split; [eapply rw_cells_transport; [exact P3| exact MU| exact WM| apply (disjoint_from_sub _ _ _ _ _ D2); cbn [cells_size csize Nat.add]; lia]|].
  split; [eapply u64arr_transport; [exact P4| exact MU| exact WM| apply (disjoint_from_sub _ _ _ _ _ D2); rewrite ?repeat_length; lia]|].
  split; [eapply rw_cells_transport; [exact P5| exact MU| exact WM| apply (disjoint_from_sub _ _ _ _ _ D2); cbn [cells_size csize Nat.add]; lia]|].
  eapply rw_cells_transport; [exact P6| exact MU| exact WM| apply (disjoint_from_sub _ _ _ _ _ D2); cbn [cells_size csize Nat.add]; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive ftail : Set := TN | T0 | TA.

(* [comment removed for export] *)
Definition tail_W (tk : ftail) (sp : word) (thr gl : Z) : list (Z * Z) :=
  match tk with TN => [] | T0 => free_dtail_W sp thr | TA => free_dtail_WA sp thr gl end.

(* [comment removed for export] *)
Definition tail_pre (tk : ftail) (gn gf gl gqb : Z) (glnx : word) (m : mem) : Prop :=
  match tk with
  | TN => True
  | T0 => rw_cells rsegs m (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]
          /\ rw_cells rsegs m (QINST + 160) [C8 (wz 0); C8 (wz gf); C8 (wz gl); C8 (wz gqb)]
  | TA => rw_cells rsegs m (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]
          /\ rw_cells rsegs m (QINST + 160) [C8 (wz gn); C8 (wz gf); C8 (wz gl); C8 (wz gqb)]
          /\ rw_cells rsegs m gl [C8 glnx]
  end.
(* [comment removed for export] *)
Definition tail_ok (tk : ftail) (gn gqb qb' : Z) : Prop :=
  match tk with
  | TN => qb' <= 2^20
  | T0 => 2^20 < qb' /\ 0 <= gqb /\ gqb + qb' <= 2^28
  | TA => 2^20 < qb' /\ 0 <= gqb /\ gqb + qb' <= 2^28 /\ gn <> 0 /\ 0 <= gn < 2^64
  end.

Section CEIL.
Context {Clg : Ceiling}.
(* [comment removed for export] *)
Definition tail_apart (tk : ftail) (gl thr p r8 n0 f0 : Z) (objs : list Z) : Prop :=
  match tk with
  | TA => kHighMemBeg <= gl /\ gl + 24 <= alloc_ceiling /\ (thr + 112 <= gl \/ gl + 8 <= thr + 80)
          /\ apart gl 24 (p + -16) (8 * r8 + 16) /\ apart gl 24 thr 4096 /\ apart gl 24 n0 kDepotNodesBlock /\ apart gl 24 f0 kStackStoreBlockBytes
          /\ Forall (fun x => apart gl 24 x 8192) objs
  | _ => True
  end.
End CEIL.

(* [comment removed for export] *)
Definition tail_post (tk : ftail) (gn gf gl gqb : Z) (nb fb lb qb : Z) (thr : Z) (m : mem) : Prop :=
  match tk with
  | TN => rw_cells rsegs m (thr + 80) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)]
  | T0 => rw_cells rsegs m (thr + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
          /\ rw_cells rsegs m (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]
          /\ rw_cells rsegs m (QINST + 160) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz (gqb + qb))]
  | TA => rw_cells rsegs m (thr + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
          /\ rw_cells rsegs m (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]
          /\ rw_cells rsegs m (QINST + 160) [C8 (wz (gn + nb)); C8 (wz gf); C8 (wz lb); C8 (wz (gqb + qb))]
          /\ rw_cells rsegs m gl [C8 (wz fb)]
  end.
