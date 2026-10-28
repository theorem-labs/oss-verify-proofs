(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BllocRepFacts BllocRepFacts2 BllocRepX BsDepotInv BsDepotHash BsUnwind BidBits BW_AllocBase BW_MallocBase BW_IAInit BW_Put1 BW_Enqueue1 BW_Enqueue2 BW_Put2 BS_Free1 BS_Free2 BllocWalkKit BG_MallocModel BG_WFHit BG_Malloc BG_Malloc2 BG_FreeModel BG_WFFree BG_Free1 BG_FreeFacts BG_Free2 BG_Free3 BG_Free4 BG_RepQ.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac lia ::=
  first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma need_new_true_full : forall t, need_new t = true -> qc_list t <> [] -> kBatchCount <= qb_count (last (qc_list t) (mkQB 0 0 0 [])).
Proof. intros t. unfold need_new. destruct (qc_list t) as [|b r]; intros NN NE; [exfalso; exact (NE eq_refl)| apply Z.leb_le; exact NN]. Qed.

Section FreeNewHit.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s : ast) (LB : list (Z * Z)) (d : depot) (lo : Z) (CH : list (Z * Z)) (ch : chunk) (bs sbs : list byte).

  Let st := a_st s.
  Let TH := a_thr s.
  Let CTX := a_ctx s.
  Let sb := a_sb s.
  Let U := ch_user_beg ch.
  Let size := ch_used ch.
  Let tq := as_tq st.
  Let l := qc_list tq.
  Let k := zlen l.
  Let lb := last l (mkQB 0 0 0 []).
  Let LA := qb_addr lb.
  Let pc := get_pc st kBatchClass.
  Let cnt := pc_count pc.
  Let chunks := pc_chunks pc.
  Let cp := hd 0 chunks.
  Let B := compact_to_addr st kBatchClass cp.
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CH.
  Let T := utrace 0xba24c (bv_unsigned sp) (a_top s) (a_bot s) 30 CHI.
  Let nT := Z.of_nat (length T).
  Let d' := d_put d (depot_hash T) nT.

  Let tq' := tq_new tq B (ch_chunk_beg ch) size.
  Let cache' := upd_nth (as_cache st) (zidx kBatchClass) (mkPC (cnt - 1) (tl chunks)).
  Let s' := free_s' s ch tq' cache' (a_L s) (a_S s) (a_AL s).

  Let Wh : list ivl := free_head_W lo (bv_unsigned sp) TH U size d.
  Let Wn : list ivl := enq_new_W lo (bv_unsigned sp) TH B LA.
  Let W : list ivl := Wh ++ Wn.

  Hypothesis HR : ARHEAP s LB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis ALLOC : ch_state ch = CAllocated.
  Hypothesis UHI : aapp (ch_user_beg ch - 16) (16 + round_up (ch_used ch) 8).
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 2912 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis TP : tp = wz ATP.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 32768.
  Hypothesis FCH : goodframe (a_bot s) (bv_unsigned sp) (a_top s) = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) (a_top s) = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m (a_top s) (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz U.
  Hypothesis BLK : rw_cells asegs m U [CB (Z.to_nat size) bs].
  Hypothesis SHB : SHAD m U sbs /\ Z.of_nat (length sbs) = nsh size.

  Hypothesis QSZ : size <= kQuarantineMaxSize /\ size < 2^32.
  Hypothesis NN : need_new tq = true.
  Hypothesis HIT : cnt <> 0.
  Hypothesis NOD : qc_bytes tq + size + kBatchSize <= kMaxCacheSize.

  Let R : AREP s m. Proof. exact (proj1 HR). Qed.
  Let OK : ast_ok s. Proof. exact (proj1 R). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.

  Let FLG4 : rw_cells asegs m AIAINIT [C1 (b8 (if as_internal_init st then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Proof.
    pose proof R as RR. destruct RR as (_ & _ & FL & _).
    destruct FL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F16 & _). exact F16.
  Qed.
  Let IAX : if as_internal_init st then ia_after m else ia_pristine m.
  Proof. pose proof R as RR. destruct RR as (_ & _ & _ & _ & _ & IA & _). unfold ia_rep in IA. unfold ia_after, ia_pristine. exact IA. Qed.
  Let PURE := free_pure s m ch R CHIN UHI.
  Let HC24 : 0 <= kBatchClass < kNumClasses. Proof. unfold kBatchClass, kNumClasses. lia. Qed.
  Let PCS : pc_chunks (get_pc st kBatchClass) = cp :: tl chunks.
  Proof.
    pose proof (co_count _ _ (WF_cache st kBatchClass WFs HC24)) as C1. fold pc cnt chunks in C1.
    unfold cp. fold pc. fold chunks. destruct chunks as [|x r] eqn:E; [| reflexivity]. exfalso. apply HIT. rewrite C1. reflexivity.
  Qed.
  Ltac zlets := repeat match goal with H := _ |- _ => subst H end.

  Definition free_newhit_gpost : machine_state -> Prop := fun ms' =>
    exists m', free_ret_post sp ra s0 s1 s2 s3 s4 s5 gp tp s6 s7 s8 s9 s10 s11 F fc lo m' ms'
      /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ ARHEAP s' (lb_remove U LB) m' /\ DEPOT asegs d' m'.

End FreeNewHit.
End HCW.
