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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASechs3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASechs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietcz7.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_cfree_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietcz7.dl_tf_cfree_lia.
(* [comment removed for export] *)
Ltac aobjL H := let A := fresh "A" H in pose proof (proj1 H) as A; aobj_lin1 A.
Ltac aobj_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => exact (proj1 H) end
  | match goal with K : aobjK _ _ |- _ => exact (aobjK_e _ _ K) end
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_sub _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | apply aobj_hi; kun; lia ].
Ltac pz_side := first
  [ assumption
  | match goal with H : aobj _ _ /\ _ |- _ => apply (aobj_pz_in _ _ _ _ (proj1 H)); kun; lia end
  | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); kun; lia end
  | unfold pz_in, kLowShadowMapBeg, kHighMemBeg; kun; lia ].

Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- _ /\ _ => split; sides
  | |- _ => sides1 end.

Definition keep (P : Prop) : Prop := P.


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
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.

Section T3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr sb AB q d e dc ru n0 f0 : Z) (b0w : byte) (b1v : Z) (d8 : word)
            (D : list (list Z)) (k : list Z) (olds oll olt : list byte) (Q : machine_state -> Prop).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis DC : dc = d + (if e =? 0 then 0 else 1).
  Hypothesis SOA : bv_unsigned sp <= stkobj /\ stkobj + 2064 <= 2^47.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_sb : AB + 8 * ru <= sb \/ sb + 2^37 <= AB.
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis PCo : poison_consts m.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  Hypothesis DR : dr AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0 : n0 + kDepotNodesBlock <= AB - 4096 \/ AB + 8 * ru <= n0.
  Hypothesis SEP_f0 : f0 + kStackStoreBlockBytes <= AB - 4096 \/ AB + 8 * ru <= f0.
  Hypothesis KL : (1 <= length k <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) k.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 (Z_to_bv 64 (stkobj + 16)); C8 (Z_to_bv 64 (Z.of_nat (length k)))].
  Hypothesis TRB : bytes_at rsegs m (stkobj + 16) (u64s (map (Z_to_bv 64) k)).
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 d8].
  Hypothesis SBc : ro_cells rsegs m 0xb1578 [C8 (Z_to_bv 64 sb)].
  Hypothesis PGS : ro_cells rsegs m 0xb1598 [C8 (Z_to_bv 64 4096)].
  Hypothesis HSZ : ro_cells rsegs m (AB - 4096 + 16) [C8 (Z_to_bv 64 (needed_size2 n))].
  Hypothesis SHL : rw_cells rsegs m (q + kShadowOffset) [CB 256 oll].
  Hypothesis SHU : u8arr rsegs m (q + 256 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHT : rw_cells rsegs m (q + 256 + dc + kShadowOffset) [CB (Z.to_nat (ru - 256 - dc)) olt].
  Hypothesis K : forall (m1 md : word -> option byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      let id := snd (depot_putC D k) in
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000);
             (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
             (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc));
             (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)] m m1 ->
      wmono rsegs m m1 ->
      dr AL_pboth rsegs (fst (depot_putC D k)) n0 f0 md ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
             (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc));
             (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)] md m1 -> wmono rsegs md m1 ->
      rw_cells rsegs m1 (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
      bytes_at rsegs m1 (q + kShadowOffset) (repeat (Z_to_bv 8 250) 256) ->
      bytes_at rsegs m1 (q + 256 + dc + kShadowOffset) (repeat (Z_to_bv 8 250) (Z.to_nat (ru - 256 - dc))) ->
      bytes_at rsegs m1 (q + 256 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d)) ->
      wr_at rsegs m1 (q + 256 + kShadowOffset) d ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37534) fc None m1 (seg_rom rsegs)).

  (* [comment removed for export] *)
End T3.

(* [comment removed for export] *)
Section T4.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr AB q d e ru : Z) (oldp : byte) (Q : machine_state -> Prop).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 < e < 8.
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb240d [C1 (Z_to_bv 8 1)].  (* [comment removed for export] *)
  Hypothesis SHP : rw_cells rsegs m (q + 256 + d + kShadowOffset) [C1 oldp].
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + 256 + d + kShadowOffset, q + 256 + d + kShadowOffset + 1)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 (q + 256 + d + kShadowOffset) [C1 (Z_to_bv 8 e)] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (AB + 2048 + 8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x375c8) fc None m1 (seg_rom rsegs)).

  (* [comment removed for export] *)
End T4.

Section T4z.
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s2 s3 s4 s5 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (n d : Z) (Q : machine_state -> Prop).
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis NDE : n = 8 * d + 0.
  Hypothesis K : evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 (8 * d)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x375c8) fc None m (seg_rom rsegs)).
  (* [comment removed for export] *)
End T4z.

(* [comment removed for export] *)
Section T5.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr AB ru : Z) (v0 v1 v2 vl : word) (uj : list byte) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis SEP_thr : thr + 4096 <= AB \/ AB + 8 * ru <= thr.
  Hypothesis SEP_ctx : ctx + 0x10000 <= AB \/ AB + 8 * ru <= ctx.
  Hypothesis SEP_tc : ctx + 0x10000 <= thr \/ thr + 4096 <= ctx.
  Hypothesis TSDL : 0x10000 <= tsd /\ tsd + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 8 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF44 : ro_cells rsegs m 0xb23e4 [C4 (Z_to_bv 64 4096)].   (* [comment removed for export] *)
  Hypothesis AF52 : ro_cells rsegs m 0xb23ec [C4 (Z_to_bv 64 kMallocFillByte)].  (* [comment removed for export] *)
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STL : rw_cells rsegs m (thr + 2904) [C8 vl].
  Hypothesis USR : rw_cells rsegs m (AB + 2048) [CB 4096%nat uj].
  Hypothesis K : forall (m1 : word -> option byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' v0' v1' v2' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2904, thr + 2912);
             (AB + 2048, AB + 2048 + 4096)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 (thr + 2800) [C8 v0'; C8 v1'; C8 v2'] ->
      rw_cells rsegs m1 (thr + 2904) [C8 (Z_to_bv 64 (bv_unsigned vl + 1))] ->
      rw_cells rsegs m1 (AB + 2048) [CB 4096%nat (fill_result canfill uj 4096%nat)] ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 s6 (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x3775c) fc None m1 (seg_rom rsegs)).

  (* [comment removed for export] *)
End T5.

(* [comment removed for export] *)
Section T6.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill thr AB ru b1v id : Z) (b0w : byte) (j0 j1 : word) (Q : machine_state -> Prop).
  Variables (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 524288.
  Hypothesis RAA : bv_unsigned cra mod 2 = 0.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis TPL : 0x10000 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 64 <= 0x60a000.   (* [comment removed for export] *)
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis ABA : AB mod 4096 = 0.
  Hypothesis ABR : aobj (AB - 4096) (4096 + 8 * ru) /\ AB + 8 * ru <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis RU8 : round_up (needed_size2 n) 4096 = 8 * ru.
  Hypothesis LS1 : ro_cells rsegs m 0xa97d0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146680 [C8 (Z_to_bv 64 0)].
  Hypothesis HDR : rw_cells rsegs m (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
  Hypothesis B1R : 0 <= b1v < 256.
  Hypothesis ABH : rw_cells rsegs m AB [C8 j0; C8 j1].
  Hypothesis K : forall (m1 : word -> option byte)
                        (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2032, AB + 2034); (AB, AB + 16)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 (AB + 2032) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.lor (Z.land b1v 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
      rw_cells rsegs m1 AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + 2032))] ->
      evt rsegs Q
        (MS (mkR cra sp gp tp t0' t1' t2' cs0 cs1
                 (Z_to_bv 64 (AB + 2048)) a1' a2' a3' a4' a5' a6' a7'
                 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3' t4' t5' t6')
            F (ret_pc cra) fc None m1 (seg_rom rsegs)).

  (* [comment removed for export] *)
End T6.

(* [comment removed for export] *)
Section Tnull.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s1 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo canfill : Z) (oomb : byte) (Q : machine_state -> Prop).
  Variables (sp : word) (cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra : word) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis RAA : bv_unsigned cra mod 2 = 0.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill cs11 cs10 cs9 cs8 cs7 cs6 cs5 cs4 cs3 cs2 cs1 cs0 cra junk0).
  Hypothesis OOM : rw_cells rsegs m 0x136e20 [C1 oomb].
  Hypothesis MRN : ro_cells rsegs m 0x136e21 [C1 (Z_to_bv 8 1)].
  Hypothesis K : forall (m1 : word -> option byte)
                        (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x136e20, 0x136e21)] m m1 ->
      wmono rsegs m m1 ->
      rw_cells rsegs m1 0x136e20 [C1 (Z_to_bv 8 1)] ->
      evt rsegs Q
        (MS (mkR cra sp gp tp t0' t1' t2' cs0 cs1
                 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3' t4' t5' t6')
            F (ret_pc cra) fc None m1 (seg_rom rsegs)).

  (* [comment removed for export] *)
End Tnull.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
