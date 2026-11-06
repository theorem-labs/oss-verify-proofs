(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AIcpm9j ARtStmts AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ASechs3 ASech8k.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASechs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASech8k.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
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
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @SBR; @AABR; @NR; @NDE; @ER; @SOA; @ABQ; @SPR; @RGE; @NS2; @DCR; @RU1; @OL; @IDR; @K0; @ABR; @DN0; @DF0; @ADN0; @ADF0; @CE0; @KL; @DLEN; @HIGH; @RLT; @LOW; @ABA])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietcz7.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_cfree_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietcz7.dl_tf_cfree_lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
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

(* [comment removed for export] *)


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

(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@AABR; @ABQ; @ABR; @ADF0; @ADN0; @DCR; @DF0; @DN0; @ER; @LO; @NDE; @NR; @NS2; @RGE; @RU1; @SBR; @SEP_f0; @SEP_n0; @SOA])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= hot_tf_cut; hot_tf_lia0.
(* [comment removed for export] *)
Section T3A8.
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
  Hypothesis NR : 64513 <= n < 2^31.
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
  Hypothesis DR : dr AL_pasan rsegs D n0 f0 m.
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
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis PGS : ro_cells rsegs m 0xb1d98 [C8 (Z_to_bv 64 4096)].
  Hypothesis HSZ : ro_cells rsegs m (AB - 4096 + 16) [C8 (Z_to_bv 64 (needed_size2 n))].
  Hypothesis SHL : rw_cells rsegs m (q + kShadowOffset) [CB 256 oll].
  Hypothesis SHU : u8arr rsegs m (q + 256 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHT : rw_cells rsegs m (q + 256 + dc + kShadowOffset) [CB (Z.to_nat (ru - 256 - dc)) olt].
  Hypothesis K : forall (m1 md : word -> option byte)
                        (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      let id := snd (depot_putC D k) in
      mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -128) ->
      munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000);
             (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
             (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc));
             (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)] m m1 ->
      wmono rsegs m m1 ->
      dr AL_pasan rsegs (fst (depot_putC D k)) n0 f0 md ->
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
            F (Z_to_bv 64 0x37654) fc None m1 (seg_rom rsegs)).

  #[using="K SHT OL SHU SHL HSZ PGS SBc HDR TRB TRC KR KL SEP_f0 SEP_n0 DF0 DN0 DTOT DLEN DND DR DPS PS PCo RU8 SEP_sb ABR ABA ABQ SBR THR SOA DC ER NDE NR SPR LO ST MI dr olt oll olds D d8 b1v b0w f0 n0 ru dc e d q sb lo Clg"] Lemma sec_seg3_a8 : evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 (stkobj + 16)) (Z_to_bv 64 (Z.of_nat (length k))) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37544) fc None m (seg_rom rsegs)).
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. try aobjL ABR. try aobjL MBR. try aobjL PAR. pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000);
             (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
             (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc));
             (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (rz_size_large n ltac:(lia)) as RSL. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    pose proof (needed_size2_secondary n ltac:(unfold kMaxPrimaryUser; lia)) as NS2.
    pose proof (round_up_4096_facts (needed_size2 n) ltac:(lia)) as [RU1 RU2]. rewrite RU8 in RU1, RU2.
    assert (DCR : d <= dc <= d + 1) by (rewrite DC; destruct (e =? 0); lia).
    pose proof PCo as PC'. destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps).
    clear PCo. kun.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof alloc_ceiling_val as CV.
    pose proof (depot_putC_id_range D k) as IDR.
    pose proof (u8arr_bound rsegs m _ _ SHU) as SHB. rewrite OL, Z2Nat.id in SHB by lia.
    amz. callz (depot_call dr DPS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D k (stkobj + 16) n0 f0 lo). all: sides. (* [comment removed for export] *) lazymatch type of KL with ?T => change T with (id T) in KL end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?md _) =>
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2040, AB + 2048); (q + 2147450880, q + 2147450880 + 256);
             (q + 256 + dc + 2147450880, q + 256 + dc + 2147450880 + (ru - 256 - dc));
             (q + 256 + 2147450880, q + 256 + 2147450880 + d)] md) as MU2;
      pose proof (wmono_refl rsegs md) as WM2 end.
    amz. amz. rewrite (Z.mod_small (snd (depot_putC D k)) 4294967296) by lia. amz. rewrite Z.lor_0_l. amz.
    amz. if_true. (* [comment removed for export] *)
    (* [comment removed for export] *)
    amz. (* [comment removed for export] *)
    assert (JOIN : forall x0 x1 x2 mx x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : word,
      evt rsegs Q (MS (mkR (Z_to_bv 64 226632) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x0 x1 x2 (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 sb) mx x4 x5 x6 x7 x8 x9
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 x10 x11 x12 x13)
            F (Z_to_bv 64 0x375b4) fc None m0 (seg_rom rsegs))).
    2:{ destruct SEP_sb as [LOW|HIGH].
        - amz. br_taken. apply JOIN.
        - amz. br_not_taken. amz. amz. amz. amz. br_taken. apply JOIN. }
    intros y0 y1 y2 mx y4 y5 y6 y7 y8 y9 y10 y11 y12 y13.
    (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    replace (Z.land 4095 AB) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2^12) with 4096; lia).
    amz. if_false. amz. amz. if_false. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    rewrite (roundup_page_land (needed_size2 n)) by lia. rewrite RU8.
    amz. (* [comment removed for export] *)
    amz. amz. (* [comment removed for export] *)
    replace (Z.land (AB + 2048 + n + 7) 18446744073709551608) with (AB + 2048 + 8 * dc).
    2:{ rewrite NDE. replace (AB + 2048 + (8 * d + e) + 7) with ((AB + 2048) + 8 * d + e + 7) by lia.
        rewrite (roundup8_land (AB + 2048) d e); [rewrite DC; reflexivity | lia | | lia | lia | lia].
        apply mod_add_lit; [lia| | reflexivity]. apply (mod0_down AB 4096 8); [exists 512; reflexivity| exact ABA]. }
    amz. amz. amz. amz. (* [comment removed for export] *)
    replace (AB + 2048 - AB) with 2048 by lia.
    callz (poison_call PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q 256 AB 2048 250 lo oll). all: try sides.
    lazymatch goal with H : bytes_at rsegs ?mm (q + 2147450880) _ |- _ =>
      rename H into SHLP; change (keep ltac:(lazymatch type of SHLP with ?t => exact t end)) in SHLP;
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128);
             (q + 256 + dc + 2147450880, q + 256 + dc + 2147450880 + (ru - 256 - dc));
             (q + 256 + 2147450880, q + 256 + 2147450880 + d)] mm) as MU3;
      pose proof (wmono_refl rsegs mm) as WM3 end.
    amz. amz. (* [comment removed for export] *)
    replace (AB - (AB + 2048 + 8 * dc) + 8 * ru) with (8 * (ru - 256 - dc)) by lia.
    amz. amz. amz. (* [comment removed for export] *)
    callz (poison_call PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q + 256 + dc) (ru - 256 - dc) (AB + 2048 + 8 * dc) (8 * (ru - 256 - dc)) 250 lo olt).
    all: try sides.
    lazymatch goal with H : bytes_at rsegs ?mm (q + 256 + dc + 2147450880) _ |- _ =>
      rename H into SHTP; change (keep ltac:(lazymatch type of SHTP with ?t => exact t end)) in SHTP;
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + 256 + 2147450880, q + 256 + 2147450880 + d)] mm) as MU4;
      pose proof (wmono_refl rsegs mm) as WM4 end.
    (* [comment removed for export] *)
    amz. amz. amz. (* [comment removed for export] *)
    replace (Z.land n 281474976710648) with (8 * d) by (symmetry; rewrite NDE; apply land_mask48_m8; lia).
    amz. br_not_taken. (* [comment removed for export] *)
    amz. amz. amz. amz. (* [comment removed for export] *)
    pose proof (proj2 SHU) as WRS. rewrite OL, Z2Nat.id in WRS by lia.
    callz (poison_call PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q + 256) d (AB + 2048) (8 * d) 0 lo olds). all: try sides.
    1:{ rewrite <- OL. apply rw_cells_of_u8arr. exact SHU. }
    eapply K; try eassumption.
    - unfold keep in SHLP. eapply bytes_at_transport; [exact SHLP | exact MU3 | cbn [disjoint_from]; rewrite repeat_length; lia].
    - unfold keep in SHTP. eapply bytes_at_transport; [exact SHTP | exact MU4 | cbn [disjoint_from]; rewrite repeat_length; lia].
  Qed.
End T3A8.

Section PT3A8.

Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj thr sb AB q d e dc ru n0 f0 : Z) (b0w : byte) (b1v : Z) (d8 : word)
            (D : list (list Z)) (k : list Z) (olds oll olt : list byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp + -128).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis NR : 64513 <= n < 2^31.
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
  Hypothesis DR : dr AL_pasan rsegs D n0 f0 m.
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
  Hypothesis SBc : ro_cells rsegs m 0xb1d78 [C8 (Z_to_bv 64 sb)].
  Hypothesis PGS : ro_cells rsegs m 0xb1d98 [C8 (Z_to_bv 64 4096)].
  Hypothesis HSZ : ro_cells rsegs m (AB - 4096 + 16) [C8 (Z_to_bv 64 (needed_size2 n))].
  Hypothesis SHL : rw_cells rsegs m (q + kShadowOffset) [CB 256 oll].
  Hypothesis SHU : u8arr rsegs m (q + 256 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHT : rw_cells rsegs m (q + 256 + dc + kShadowOffset) [CB (Z.to_nat (ru - 256 - dc)) olt].
    Definition sec_seg3_a8_post : machine_state -> Prop := fun ms' =>
    exists (m1 md : word -> option byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    let id := snd (depot_putC D k) in
    ms' = (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (8 * ru)) (Z_to_bv 64 n)
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 (8 * d)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n + 7)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3' t4' t5' t6')
            F (Z_to_bv 64 0x37654) fc None m1 (seg_rom rsegs)) /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (0x187288, 0x5d72a8); (n0, n0 + 0x100000); (f0, f0 + 0x800000);
             (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
             (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc));
             (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)] m m1 /\
    wmono rsegs m m1 /\
    mem_inv rsegs m1 /\
    stk rsegs m1 lo (bv_unsigned sp + -128) /\
    dr AL_pasan rsegs (fst (depot_putC D k)) n0 f0 md /\
    munch [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (AB + 2040, AB + 2048); (q + kShadowOffset, q + kShadowOffset + 256);
             (q + 256 + dc + kShadowOffset, q + 256 + dc + kShadowOffset + (ru - 256 - dc));
             (q + 256 + kShadowOffset, q + 256 + kShadowOffset + d)] md m1 /\
    wmono rsegs md m1 /\
    rw_cells rsegs m1 (AB + 2032) [C1 b0w; C1 (Z_to_bv 8 b1v); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] /\
    bytes_at rsegs m1 (q + kShadowOffset) (repeat (Z_to_bv 8 250) 256) /\
    bytes_at rsegs m1 (q + 256 + dc + kShadowOffset) (repeat (Z_to_bv 8 250) (Z.to_nat (ru - 256 - dc))) /\
    bytes_at rsegs m1 (q + 256 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d)) /\
    wr_at rsegs m1 (q + 256 + kShadowOffset) d.

  #[using="SHT OL SHU SHL HSZ PGS SBc HDR TRB TRC KR KL SEP_f0 SEP_n0 DF0 DN0 DTOT DLEN DND DR DPS PS PCo RU8 SEP_sb ABR ABA ABQ SBR THR SOA DC ER NDE NR SPR LO ST MI olt oll olds d8 e sb Clg"] Lemma sec_seg3_a8_spec : evt rsegs sec_seg3_a8_post
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 n)
                 (Z_to_bv 64 (stkobj + 16)) (Z_to_bv 64 (Z.of_nat (length k))) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size2 n)) (Z_to_bv 64 (AB + 2048)) (Z_to_bv 64 (AB + 2032))
                 (Z_to_bv 64 0xb1d58) (Z_to_bv 64 stkobj) (Z_to_bv 64 0) (Z_to_bv 64 (AB + 2048 + n)) (Z_to_bv 64 thr) (Z_to_bv 64 1)
                 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37544) fc None m (seg_rom rsegs)).
  Proof.
    eapply sec_seg3_a8; try eassumption. intros. subst. apply evt_done. unfold sec_seg3_a8_post.
    hot_eexists_all. cbv zeta.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits. all: first [reflexivity | eassumption].
  Qed.
End PT3A8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
