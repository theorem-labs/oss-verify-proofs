(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AMalq4j AMalrrv.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AInv ARtStmts ARtS4t2 AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalz1i AMalw7s.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalc5w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA.AMalrao OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i.AMallocR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalz1i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalw7s.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LWS; @LVS; @OL; @LKS; @KRf; @ARF; @SBR; @RIR; @ATHR; @CGE; @Ha; @HB'; @HA'; @ABR; @RZ32'; @KL; @TPL; @RSR; @Bthr; @ADN0; @ADF0; @SOA; @TSDL; @LO; @SPR; @NSB; @CE0; @MXR; @Bthr1; @ACTR; @DN0; @DF0; @KSO; @RGE; @NS; @NR; @Bctx1; @Bctx; @SEP_tr; @SEP_thr; @CSR; @X; @H; @KLz; @KLz__])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation apart := AMallocA.apart.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Module HotBulk. Import Ltac2.
Ltac2 clear_boxed () :=
  let ids := List.map_filter (fun h => let (id, _, ty) := h in
               lazy_match! ty with boxed _ => Some id | _ => None end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac2 clear_negs () :=
  let ids := List.map_filter (fun h => let (id, _, ty) := h in
               lazy_match! ty with not _ => Some id | _ => None end) (Control.hyps ()) in
  match ids with [] => () | _ :: _ => Std.clear ids end.
End HotBulk.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac slia ::= first [ exact I | lazymatch goal with |- _ /\ _ => split; slia | |- _ => lia end ].
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



Ltac box_places := repeat match goal with H : 0 <= _ <= 1 /\ 0 <= _ <= 1 /\ _ |- _ => box H end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unbox_places := repeat match goal with H : boxed (0 <= _ <= 1 /\ 0 <= _ <= 1 /\ _) |- _ => unfold boxed in H end.
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I | lia
        | multimatch goal with H : apart _ _ _ _ |- _ =>
            (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia
        | unbox_places; first [ lia
            | multimatch goal with H : apart _ _ _ _ |- _ =>
                (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ] ].
(* [comment removed for export] *)

Ltac kung := cbv delta [kHighMemBeg kDepotNodesBlock kStackStoreBlockBytes kShadowOffset kStackStoreBlockFrames kMaxSize
                        kAsanHeapLeftRedzoneMagic kMaxPrimaryUser kMallocFillByte kAllocBegMagic CHUNK_ALLOCATED].
Ltac eqrefl := lazymatch goal with |- _ = _ => reflexivity end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sides1c := first [ eassumption | eqrefl | lia | modtac ].
Ltac sidesc := lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sidesc
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sidesc
  | |- _ /\ _ => first [eassumption | split; sidesc]
  | |- _ => sides1c end.
Ltac sides1 ::= first [ eassumption | eqrefl | lia | kung; lia | modtac
                      | rewrite ?unsigned_lit by lia; first [eassumption | eqrefl | lia | modtac]
                      | unbox_places; kung; lia ].
Ltac sides ::= lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- aobj _ _ => aobj_side
  | |- aobjK _ _ => apply aobjK_i; aobj_side
  | |- pz_in _ _ => pz_side
  | |- forall _, _ -> evt _ _ _ => idtac
  | |- poison_consts _ => unfold poison_consts; sides
  | |- thread_cells _ _ _ _ _ => unfold thread_cells; sides
  | |- _ /\ _ => first [eassumption | split; sides]
  | |- _ => sides1 end.

(* [comment removed for export] *)
Tactic Notation "callx" uconstr(SPEC) "cleaning" tactic(CLEAN) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | CLEAN; post_call_z segs m ]
  end.
Tactic Notation "callx" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [eapply SPEC | ]; [> try sidesc .. | idtac]; [> try sides .. | post_call_z segs m ]
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac xfer1 H M WMH :=
  lazymatch type of M with munch ?W ?mi ?mc =>
  lazymatch type of H with
  | ro_cells _ _ ?A ?cs => apply (ro_cells_transport rsegs W mi mc A cs) in H; [| exact M| cbn [disjoint_from]; simpl_sizes; slia]
  | rw_cells _ _ ?A ?cs => apply (rw_cells_transport rsegs W mi mc A cs) in H; [| exact M| exact WMH| cbn [disjoint_from]; simpl_sizes; slia]
  | u32arr _ _ ?A ?ws => apply (u32arr_transport rsegs W mi mc A ws) in H; [| exact M| exact WMH| cbn [disjoint_from]; simpl_sizes; rewrite ?u32s_length; slia]
  end end.

Section AllocTail.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo n stkobj canfill tsd ctx thr c maxc sb AB q r8 d e n0 f0 ri nf : Z).
  Variables (ks ws : list word) (b0w b1w : byte) (kw statv na h2 w4 d8 j0 j1 v0 v1 v2 : word) (vs : list word)
            (D : list (list Z)) (k : list Z) (olds uj : list byte) (oldp : byte) (nf0 : Z) (pad junk0 : list byte).
  Variable dr : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop.

  (* [comment removed for export] *)
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 1024.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPR : bv_unsigned sp + 65536 < 2^64.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis NR : 1 <= n <= 64512.
  Hypothesis NDE : n = 8 * d + e.
  Hypothesis ER : 0 <= e < 8.
  Hypothesis CF : 0 <= canfill <= 1.
  Hypothesis SOA : bv_unsigned sp <= stkobj /\ stkobj + 2064 <= 2^47.
  (* [comment removed for export] *)
  Hypothesis GT : get_thread_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt dr.
  Hypothesis BLK2 : classid_blk2_stmt.
  (* [comment removed for export] *)
  Hypothesis PCo : poison_consts m.
  Hypothesis AF1 : ro_cells rsegs m 0xa8b68 [C8 (Z_to_bv 64 0xb23b8)].
  Hypothesis AF2 : ro_cells rsegs m 0xb240d [C1 (Z_to_bv 8 1)].
  Hypothesis AF44 : ro_cells rsegs m 0xb23e4 [C4 (Z_to_bv 64 4096)].
  Hypothesis AF52 : ro_cells rsegs m 0xb23ec [C4 (Z_to_bv 64 kMallocFillByte)].
  Hypothesis LS1 : ro_cells rsegs m 0xa97d0 [C8 (Z_to_bv 64 0x10)].
  Hypothesis LS2 : ro_cells rsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)].
  Hypothesis HK : ro_cells rsegs m 0x146680 [C8 (Z_to_bv 64 0)].
  Hypothesis SBc : ro_cells rsegs m 0xb1578 [C8 (Z_to_bv 64 sb)].
  (* [comment removed for export] *)
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TH0 : ro_cells rsegs m thr [C8 (Z_to_bv 64 ctx)].
  Hypothesis CT8 : ro_cells rsegs m (ctx + 8) [C4 (Z_to_bv 64 0)].
  Hypothesis THR : aobj thr 4096 /\ thr + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis THRA : thr mod 16 = 0.
  Hypothesis CTR : aobj ctx 0x10000 /\ ctx + 0x10000 <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis TSDL : 0x5e7b28 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis TPL : bv_unsigned tp = 0x5e7bd8.
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis SEP_thr : apart thr 4096 sb (2^37).
  Hypothesis SEP_ctx : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  (* [comment removed for export] *)
  Hypothesis HC : c = size_class (needed_size n).
  (* [comment removed for export] *)
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis MXR : 2 <= maxc <= 16.
  Hypothesis RIR : kHighMemBeg <= ri /\ ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_cri : apart ctx 0x10000 ri 4096.
  Hypothesis SEP_n0r : apart n0 kDepotNodesBlock ri 4096.
  Hypothesis SEP_f0r : apart f0 kStackStoreBlockBytes ri 4096.
  Hypothesis LWS : length ws = Z.to_nat (Z.shiftr maxc 1).
  Hypothesis KW : nth_error ws (Z.to_nat (Z.shiftr maxc 1 - 1)) = Some kw.
  Hypothesis KWR : bv_unsigned kw < 2^32.
  Hypothesis ABU : AB + class_size c <= sb + c * 2^32 + 3758096384.
  Hypothesis STA : rw_cells rsegs m (thr + 208 + 2576) [C8 statv].
  Hypothesis STS : rw_cells rsegs m (thr + 2800) [C8 v0; C8 v1; C8 v2].
  Hypothesis STA2 : u64arr rsegs m (thr + 2912) vs.
  Hypothesis LVS : length vs = 32%nat.
  (* [comment removed for export] *)
  Hypothesis ABE : AB = sb + c * 2^32 + 16 * bv_unsigned kw.
  Hypothesis ABA : AB mod 32 = 0.
  Hypothesis ABQ : AB = 8 * q.
  Hypothesis ABR : sb <= AB /\ AB + class_size c <= sb + 2^37.
  Hypothesis RZ8 : rz_size n = 8 * r8.
  Hypothesis HDR : rw_cells rsegs m (AB + rz_size n + -16) [C1 b0w; C1 b1w; C2 h2; C4 w4; C8 d8].
  Hypothesis ABH : rz_size n <> 16 -> rw_cells rsegs m AB [C8 j0; C8 j1].
  Hypothesis SHA : ro_cells rsegs m (q + kShadowOffset) [C1 (Z_to_bv 8 kAsanHeapLeftRedzoneMagic)].
  Hypothesis SHU : u8arr rsegs m (q + r8 + kShadowOffset) olds.
  Hypothesis OL : length olds = Z.to_nat d.
  Hypothesis SHP : e <> 0 -> rw_cells rsegs m (q + r8 + d + kShadowOffset) [C1 oldp].
  Hypothesis USR : rw_cells rsegs m (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj].
  (* [comment removed for export] *)
  Hypothesis DR : dr AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Hypothesis SEP_n0 : apart n0 kDepotNodesBlock sb (2^37).
  Hypothesis SEP_f0 : apart f0 kStackStoreBlockBytes sb (2^37).
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  (* [comment removed for export] *)
  Hypothesis DRF : forall D' (m1 m2 : word -> option byte), dr AL_pboth rsegs D' n0 f0 m1 ->
      (forall a, depot_foot AL_pboth n0 f0 a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> dr AL_pboth rsegs D' n0 f0 m2.
  Hypothesis KL : (1 <= length k <= 255)%nat.
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) k.
  Hypothesis TRC : ro_cells rsegs m stkobj [C8 (Z_to_bv 64 (stkobj + 16)); C8 (Z_to_bv 64 (Z.of_nat (length k)))].
  Hypothesis TRB : bytes_at rsegs m (stkobj + 16) (u64s (map (Z_to_bv 64) k)).

  (* [comment removed for export] *)
  Hypothesis NF0 : 0 <= nf0 /\ nf0 + Z.shiftr maxc 1 < 2^27.
  Hypothesis FRA : rw_cells rsegs m (bv_unsigned sp + -128) (alloc_s1a_frame sp canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra junk0).
  Hypothesis FRC : rw_cells rsegs m (bv_unsigned sp + -128 + -48) (comb_frameR n).
  Hypothesis FRR : rw_cells rsegs m (bv_unsigned sp + -128 + -48 + -32) (refill_frame pad (Z_to_bv 64 (thr + 208 + 80 * c)) (Z_to_bv 64 c) (Z_to_bv 64 comb_refill_ret)).

  #[using="FRR FRC FRA NF0 TRB TRC KR KL DRF SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_f0 SEP_n0 DF0 DN0 DTOT DLEN DND DR USR SHP OL SHU SHA ABH HDR RZ8 ABR ABQ ABA ABE LVS STA2 STS STA ABU KWR KW LWS SEP_f0r SEP_n0r SEP_cri SEP_rs SEP_tr SBAL RIAL RIR MXR LKS HC SEP_tc SEP_ctx SEP_thr SBR TPL TSDL CTR THRA THR CT8 TH0 TC SBc HK LS2 LS1 AF52 AF44 AF2 AF1 PCo BLK2 DPS PS TSS SOA CF ER NDE NR SPR SPA LO junk0 pad oldp olds v2 v1 v0 j1 j0 d8 w4 h2 statv kw b0w ctx tsd Clg"] Lemma alloc_tail : forall ms',
    gfa_post gp tp F fc (bv_unsigned sp + -128 + -48 + -32) lo (ri + 128 * c) (free_array_of sb c) nf0 (Z.shiftr maxc 1)
             (thr + 208 + 80 * c) 0 maxc (class_size c) na ws ks
             (Z_to_bv 64 1) (Z_to_bv 64 thr) (Z_to_bv 64 7) (Z_to_bv 64 (-8)) (Z_to_bv 64 stkobj) (Z_to_bv 64 0xb1558) (Z_to_bv 64 n)
             (Z_to_bv 64 0xb1558) (Z_to_bv 64 (thr + 208)) (Z_to_bv 64 8) (Z_to_bv 64 (Z.shiftr maxc 1)) (Z_to_bv 64 (thr + 208 + 80 * c)) (Z_to_bv 64 refill_ret) m ms' ->
    evt rsegs (alloc_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo n canfill thr c maxc sb AB q r8 d e n0 f0 ri nf0
                 ks ws b1w na vs D k uj dr) ms'.
  Proof.
    pose proof alloc_ceiling_val as CE0. try aobjL THR. try aobjL CTR. try aobjL DN0. try aobjL DF0. (* [comment removed for export] *)
    pose proof (rz_size_range n) as RSR. pose proof (rounded_size_ge n) as RGE. pose proof (rounded_size_lt n) as RLT.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (NSB : 1 <= needed_size n <= 65536).
    { split; [clear - NR RSR RGE NS; lia|]. apply needed_size_primary_le; apply (proj2 (from_primary_iff n)); unfold kMaxPrimaryUser; lia. }
    pose proof (size_class_range (needed_size n) ltac:(unfold kMaxSize; lia)) as CR1. rewrite <- HC in CR1.
    pose proof (size_class_ge (needed_size n) ltac:(unfold kMaxSize; lia)) as CGE. rewrite <- HC in CGE.
    pose proof (class_size_range c CR1) as CSR.
    pose proof PCo as PC'. destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps).
    pose proof TC as TC'. destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds). pose proof Bnds as Bnds_; destruct Bnds_ as (Btsd0 & Btsd1 & Bctx0 & Bctx1 & Bthr & Bthr1 & Btp & Bctx). aobj_lin1 Bthr. aobj_lin1 Bctx. kun.
    unfold kMallocFillByte, kAsanHeapLeftRedzoneMagic, kAllocBegMagic, CHUNK_ALLOCATED in *.
    assert (LO0 : 0 <= lo) by (clear - LO CE0; lia).
    assert (KSO : kShadowOffset = 2147450880) by reflexivity.
    assert (KRf : 1 <= Z.shiftr maxc 1 <= 8) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
    pose proof (conj CR1 (conj CSR (conj RSR (conj RGE (conj NS (conj NSB (conj NR (conj NDE (conj ER (conj KSO (conj KRf (conj CE0 (conj LO (conj SPR (conj SBR (conj ABR (conj ABU (conj RIR (conj MXR (conj NF0 (conj ABQ RZ8))))))))))))))))))))) as ARF.
    pose proof alloc_ceiling_val as CV.
    clear PCo TC.
    (* [comment removed for export] *)
    box_places. box SPA. box THRA. box ABA. box KWR. box ABE. box DLEN. box DTOT. box RA. box CF. box NSB. box RLT. box HC. box LKS. box RIAL. box SBAL.
    box Bnds. box CV. box LO0. box KL. box KR. box DND.
    (* [comment removed for export] *)
    box Ccan. box Cgotcf. box Cthr. box Cgotsh. box Cshoff. box Cgotmid. box Cgotmide. box Cgothi. box Chivars.
    box Cgotms. box Creal. box Cgotps. box Cps. box AF1. box AF2. box AF44. box AF52. box LS1. box LS2. box HK. box SBc.
    box Cini. box Ckey. box Ctsd. box Cctx. box Cthr2. box TH0. box CT8. box TRC. box TRB. box SHA.
    box STA. box STS. box STA2. box HDR. box SHU. box USR.
    (* [comment removed for export] *)
    Ltac small_ctx := first [ ltac2:(Ltac2.Control.enter HotBulk.clear_boxed) | repeat match goal with H : boxed _ |- _ => clear H end ].   (* [comment removed for export] *)   (* [comment removed for export] *)
    Ltac lia_small := first [ match goal with F : 1 <= c <= 30 /\ _ |- _ => clear - F; lia end | repeat match goal with H' : ~ _ |- _ => clear H' end; small_ctx; lia ].
    (* [comment removed for export] *)
    Ltac cls X := lazymatch X with
      | context [stkobj] => constr:(1%nat) | context [bv_unsigned sp] => constr:(1%nat)
      | context [thr] => constr:(2%nat) | context [ctx] => constr:(3%nat) | context [AB] => constr:(4%nat)
      | context [q] => constr:(5%nat) | context [n0] => constr:(6%nat) | context [f0] => constr:(7%nat) | context [ri] => constr:(8%nat) | context [sb] => constr:(9%nat)
      | _ => match goal with
             | Hr : ?alo <= X < _ |- _ => cls alo
             | Hr : ?alo <= X <= _ |- _ => cls alo
             | Hr : ?alo <= X |- _ => lazymatch alo with context [bv_unsigned sp] => constr:(1%nat) | context [thr] => constr:(2%nat) | context [ctx] => constr:(3%nat) | context [q] => constr:(5%nat) | context [AB] => constr:(4%nat) | context [ri] => constr:(8%nat) | _ => fail end
             | _ => constr:(0%nat) end
      end.
    Ltac negs_clear := first [ ltac2:(Ltac2.Control.enter HotBulk.clear_negs) | repeat match goal with X' : ~ _ |- _ => clear X' end ].   (* [comment removed for export] *)
    Ltac agl H := eapply (apart_gl _ _ _ _ H); negs_clear; small_ctx; lia.
    Ltac agr H := eapply (apart_gr _ _ _ _ H); negs_clear; small_ctx; lia.
    Ltac ubl := unbox_places; negs_clear; small_ctx; lia.
    Ltac sbl := negs_clear; small_ctx; lia.
    Ltac ivl := lazymatch goal with |- ?A + _ <= ?lo \/ _ <= _ =>
      let a := cls A in let l := cls lo in
      lazymatch a with
      | 1%nat => sbl
      | 2%nat => lazymatch l with 3%nat => agr SEP_tc | 4%nat => agl SEP_thr | 5%nat => ubl | 6%nat => agr SEP_n0t | 7%nat => agr SEP_f0t | 8%nat => agl SEP_tr | 9%nat => agl SEP_thr | 0%nat => ubl | _ => sbl end
      | 3%nat => lazymatch l with 2%nat => agl SEP_tc | 4%nat => agl SEP_ctx | 5%nat => ubl | 6%nat => agr SEP_n0c | 7%nat => agr SEP_f0c | 8%nat => agl SEP_cri | 9%nat => agl SEP_ctx | 0%nat => ubl | _ => sbl end
      | 4%nat => lazymatch l with 2%nat => agr SEP_thr | 3%nat => agr SEP_ctx | 6%nat => agr SEP_n0 | 7%nat => agr SEP_f0 | 8%nat => agr SEP_rs | _ => sbl end
      | 5%nat => lazymatch l with 2%nat => ubl | 3%nat => ubl | 6%nat => ubl | 7%nat => ubl | _ => sbl end
      | 6%nat => lazymatch l with 2%nat => agl SEP_n0t | 3%nat => agl SEP_n0c | 4%nat => agl SEP_n0 | 5%nat => ubl | 8%nat => agl SEP_n0r | 9%nat => agl SEP_n0 | 0%nat => ubl | _ => sbl end
      | 7%nat => lazymatch l with 2%nat => agl SEP_f0t | 3%nat => agl SEP_f0c | 4%nat => agl SEP_f0 | 5%nat => ubl | 8%nat => agl SEP_f0r | 9%nat => agl SEP_f0 | 0%nat => ubl | _ => sbl end
      | 8%nat => lazymatch l with 2%nat => agr SEP_tr | 3%nat => agr SEP_cri | 4%nat => agl SEP_rs | 6%nat => agr SEP_n0r | 7%nat => agr SEP_f0r | 9%nat => agl SEP_rs | _ => sbl end
      | 9%nat => lazymatch l with 2%nat => agr SEP_thr | 3%nat => agr SEP_ctx | 6%nat => agr SEP_n0 | 7%nat => agr SEP_f0 | 8%nat => agr SEP_rs | _ => sbl end
      | _ => lazymatch l with 2%nat => ubl | 3%nat => ubl | 6%nat => ubl | 7%nat => ubl | _ => sbl end
      end end.
    Ltac slia ::=
      (* [comment removed for export] *)
      lazymatch goal with
      | |- ~ (_ <= ?a < _) /\ _ => repeat match goal with H : ?A /\ _ |- _ => lazymatch A with ~ (_ <= a < _) => destruct H as [? H] end end
      | |- _ => idtac
      end;
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
      lazymatch goal with
      | |- True => exact I
      | |- ~ (?lo <= ?a < ?hi) =>
          (* [comment removed for export] *)
          repeat match goal with H : ?A /\ _ |- _ => lazymatch A with ~ (_ <= a < _) => destruct H as [? H] end end;
          first [ assumption
                | let cl := cls lo in
                  multimatch goal with H : ~ (?lo' <= a < ?hi') |- _ =>
                    let cl' := cls lo' in constr_eq cl cl';
                    apply (notin_mono a lo hi lo' hi' H); negs_clear; small_ctx; lia end
                | apply outside_of_disj; ivl
                | multimatch goal with H : ~ (?lo' <= a < ?hi') |- _ =>
                    apply (notin_mono a lo hi lo' hi' H); repeat match goal with H' : ~ _ |- _ => clear H' end; lia end
                | repeat match goal with H' : ~ _ |- _ => clear H' end; lia
                | unbox_places; repeat match goal with H' : ~ _ |- _ => clear H' end; lia ]
      | |- _ => first [ ivl
                      | small_ctx; lia
                      | multimatch goal with H : apart _ _ _ _ |- _ =>
                          (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; small_ctx; lia
                      | unbox_places; small_ctx; first [ lia
                          | multimatch goal with H : apart _ _ _ _ |- _ =>
                              (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ] ]
      end.
    (* [comment removed for export] *)
    Ltac sarr := rewrite ?u32s_length, ?u64s_length, ?upd_length.
    Ltac disj := cbn [disjoint_from]; simpl_sizes; sarr; slia.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Ltac useD lo := match goal with D : forall A k, 0 <= k -> lo <= A -> _ |- _ => apply D end; simpl_sizes; sarr; lia.
    Ltac disjA A := lazymatch A with
      | context [stkobj] => useD (bv_unsigned sp)
      | context [thr] => first [ useD thr | useD (thr + 2800) ]   (* [comment removed for export] *)
      | context [ctx] => useD ctx
      | context [q] => useD (q + 2147450880)
      | context [AB] => useD (AB + rz_size n)
      | context [ri] => useD ri
      | _ => useD 0x10000
      end.
    (* [comment removed for export] *)
    Ltac slia_big := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
      first [ exact I | ivl | lia
            | multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia
            | unbox_places; first [ lia
                | multimatch goal with H : apart _ _ _ _ |- _ => (eapply (apart_gl _ _ _ _ H) + eapply (apart_gr _ _ _ _ H)) end; lia ] ].
    Ltac refresh H M WMH H' :=
      lazymatch type of M with munch ?W ?mi ?mc =>
      lazymatch type of H with
      | boxed (ro_cells _ _ ?A ?cs) => assert (H' : ro_cells rsegs mc A cs); [apply (ro_cells_transport rsegs W mi mc A cs H M); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      | boxed (bytes_at _ _ ?A ?bs) => assert (H' : bytes_at rsegs mc A bs); [apply (bytes_at_transport rsegs W mi mc A bs H M); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      | boxed (rw_cells _ _ ?A ?cs) => assert (H' : rw_cells rsegs mc A cs); [apply (rw_cells_transport rsegs W mi mc A cs H M WMH); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      | boxed (u8arr _ _ ?A ?bs) => assert (H' : u8arr rsegs mc A bs); [apply (u8arr_transport rsegs W mi mc A bs H M WMH); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      | boxed (u64arr _ _ ?A ?ws) => assert (H' : u64arr rsegs mc A ws); [apply (u64arr_transport rsegs W mi mc A ws H M WMH); first [disjA A | (unbox_places; small_ctx; disj)] | ]
      end end.
    (* [comment removed for export] *)
    pose proof (munch_refl (alloc_refill_W sp thr c AB n q r8 d e n0 f0 ri) m) as MU. unfold alloc_refill_W in MU.
    pose proof (munch_refl (alloc_refill_Wc sp thr AB n q r8 d n0 f0 ri c) m) as MUc. unfold alloc_refill_Wc in MUc.
    (* [comment removed for export] *)
    lazymatch type of MUc with munch ?Wc m m =>
      assert (Dsh : forall A k, 0 <= k -> q + 2147450880 <= A -> A + k <= q + r8 + 2147450880 -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; unbox_places; small_ctx; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia);
      assert (Dstk : forall A k, 0 <= k -> bv_unsigned sp <= A -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA'; cbn [disjoint_from]; unbox_places; small_ctx; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia);
      assert (Dthr : forall A k, 0 <= k -> thr <= A -> A + k <= thr + 208 -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl);
      assert (Dctx : forall A k, 0 <= k -> ctx <= A -> A + k <= ctx + 0x10000 -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl);
      assert (Dimg : forall A k, 0 <= k -> 0x10000 <= A -> (A + k <= 0x186a88 \/ (0x5d6aa8 <= A /\ A + k <= 0x60a000)) -> disjoint_from Wc A k)
        by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; unbox_places; small_ctx; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia)
    end.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp - 1024, bv_unsigned sp + -128);
                            (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584); (ri + 128 * c, ri + 128 * c + 8); (ri + 128 * c + 16, ri + 128 * c + 24); (ri + 128 * c + 72, ri + 128 * c + 80); (AB + rz_size n + -16, AB + rz_size n)] m) as M0_2.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp - 1024, bv_unsigned sp + -128);
                            (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584); (ri + 128 * c, ri + 128 * c + 8); (ri + 128 * c + 16, ri + 128 * c + 24); (ri + 128 * c + 72, ri + 128 * c + 80); (AB + rz_size n + -16, AB + rz_size n);
                            (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + rz_size n + -8, AB + rz_size n);
                            (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d)] m) as M0_3.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp - 1024, bv_unsigned sp + -128);
                            (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584); (ri + 128 * c, ri + 128 * c + 8); (ri + 128 * c + 16, ri + 128 * c + 24); (ri + 128 * c + 72, ri + 128 * c + 80); (AB + rz_size n + -16, AB + rz_size n);
                            (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + rz_size n + -8, AB + rz_size n);
                            (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d);
                            (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1)] m) as M0_4.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (bv_unsigned sp - 1024, bv_unsigned sp + -128);
                            (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584); (ri + 128 * c, ri + 128 * c + 8); (ri + 128 * c + 16, ri + 128 * c + 24); (ri + 128 * c + 72, ri + 128 * c + 80); (AB + rz_size n + -16, AB + rz_size n);
                            (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + rz_size n + -8, AB + rz_size n);
                            (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d);
                            (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
                            (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096)] m) as M0_5.

    (* [comment removed for export] *)
    intros ms' GP.
    assert (CAL : (thr + 208) mod 16 = 0) by (unbox_places; unfold boxed in THRA; rewrite Z.add_mod, THRA by lia; reflexivity).
    assert (SEP_cr : apart (thr + 208) 3888 ri 4096) by (generalize SEP_tr; unfold apart; clear; intros; lia).
    assert (SEP_cs : apart (thr + 208) 3888 sb (2^37)) by (generalize SEP_thr; unfold apart; clear; intros; lia).
    (* [comment removed for export] *)
    assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; clear - LO CE0 SPR; lia).
    assert (LOc : alloc_ceiling <= lo /\ lo <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) - 208) by (rewrite USP; clear - LO; lia).
    assert (SPAc : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) mod 16 = 0) by (rewrite USP; unfold boxed in SPA; rewrite Z.add_mod, SPA by lia; reflexivity).
    assert (SPHc : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) <= 2^47) by (rewrite USP; clear - SOA; lia).
    assert (CLOc : aobj (thr + 208) 3888) by (unbox_places; apply (aobj_sub _ _ _ _ (proj1 THR)); clear; lia).
    assert (CSZc : 0 <= class_size c < 2^64) by (clear - CSR; lia).
    assert (FRCc : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) + -48)
                     [C8 (Z_to_bv 64 (rz_size n)); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x3731c)])
      by (rewrite USP; exact FRC).
    assert (FRRc : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) + -48 + -32)
                     (refill_frame pad (Z_to_bv 64 (thr + 208 + 80 * c)) (Z_to_bv 64 c) (Z_to_bv 64 244396))) by (rewrite USP; exact FRR).
    unfold boxed in HC, LKS, RIAL, SBAL, KWR.
    simple refine (comb_gfa_tail (Z_to_bv 64 0x3731c) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 n)
              (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 0xb1558) (Z_to_bv 64 stkobj)
              (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 thr) (Z_to_bv 64 1) F fc lo (thr + 208) c maxc (class_size c) sb ri (needed_size n) ks ws kw na
              LOc SPAc SPHc NSB HC CLOc CAL (proj1 SBR) (proj2 SBR) SBAL (proj1 RIR) (proj2 RIR) RIAL SEP_cr SEP_cs SEP_rs MXR CSZc LKS LWS KW KWR
              _ nf0 pad statv m FRCc FRRc SBc STA (proj1 NF0) (proj2 NF0) _ ms' _);
      [ | rewrite USP; exact GP].
    clear LOc SPAc SPHc CLOc CSZc FRCc FRRc.
    intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c statv' m1 LN1 STA1 MX1 NFC1 NAL1 FARR1 MU1 WM1 MI1 ST1.
    clear FRC FRR GP.
    unfold comb_refill_W, free_array_of in MU1. cbv zeta in MU1. rewrite ?unsigned_lit in MU1, ST1 by lia.
    unfold boxed in HDR.   (* [comment removed for export] *)
    kpost MU1 WM1.
    replace (ret_pc (Z_to_bv 64 0x3731c)) with (Z_to_bv 64 0x3731c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite <- ABE.
    (* [comment removed for export] *)
    refresh TH0 MUc WM TH01. refresh CT8 MUc WM CT81. refresh TRC MUc WM TRC1.
    box LN1. box STA1. box MX1. box NFC1. box NAL1. box FARR1.
    eapply evt_cut; [eapply (alloc_seg2T_spec _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo n stkobj canfill ctx thr c sb AB) | ];
      [> try sidesc .. | idtac]; [> try sides .. | idtac].
    clear TH01 CT81 TRC1.
    intros ms2 PO2. destruct_exs PO2. unfold alloc_seg2T_post in PO2.
    destruct PO2 as (E2 & MU2 & WM2 & MI2 & ST2 & HDR2). subst ms2.
    (* [comment removed for export] *)
    unfold boxed in LN1, STA1, MX1, NFC1, NAL1, FARR1.
    xfer1 LN1 MU2 WM2. xfer1 STA1 MU2 WM2. xfer1 MX1 MU2 WM2. xfer1 NFC1 MU2 WM2. xfer1 NAL1 MU2 WM2.
    lazymatch type of MU2 with munch ?W2 ?ma ?mb =>
      assert (FARR1' : u32arr rsegs mb (free_array_of sb c + 4 * nf0) ws) by
        (apply (u32arr_transport rsegs W2 ma mb _ _ FARR1 MU2 WM2); cbn [disjoint_from]; rewrite LWS; unfold free_array_of; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl) end.
    clear FARR1. rename FARR1' into FARR1.
    kpost MU2 WM2.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128);
                              (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000); (AB + rz_size n + -8, AB + rz_size n);
                              (q + r8 + kShadowOffset, q + r8 + kShadowOffset + d);
                              (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
                              (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096);
                              (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] mc) as M2_6;
      pose proof (wmono_refl rsegs mc) as WM2;
      lazymatch goal with H : rw_cells rsegs mc (thr + 208 + 80 * c) _ |- _ => rename H into LN2; box LN2 end;
      lazymatch goal with H : rw_cells rsegs mc (thr + 208 + 2576) _ |- _ => rename H into STA2'; box STA2' end;
      lazymatch goal with H : rw_cells rsegs mc (ri + 128 * c) _ |- _ => rename H into MX2; box MX2 end;
      lazymatch goal with H : rw_cells rsegs mc (ri + 128 * c + 16) _ |- _ => rename H into NFC2; box NFC2 end;
      lazymatch goal with H : rw_cells rsegs mc (ri + 128 * c + 72) _ |- _ => rename H into NAL2; box NAL2 end;
      lazymatch goal with H : u32arr rsegs mc _ ws |- _ => rename H into FARR2; box FARR2 end end.
    (* [comment removed for export] *)
    refresh TRC MUc WM TRC1. refresh TRB MUc WM TRB1. refresh SHA MUc WM SHA1.
    refresh Ccan MUc WM Ccan1. refresh Cgotcf MUc WM Cgotcf1. refresh Cthr MUc WM Cthr1. refresh Cgotsh MUc WM Cgotsh1. refresh Cshoff MUc WM Cshoff1.
    refresh Cgotmid MUc WM Cgotmid1. refresh Cgotmide MUc WM Cgotmide1. refresh Cgothi MUc WM Cgothi1. refresh Chivars MUc WM Chivars1.
    refresh Cgotms MUc WM Cgotms1. refresh Creal MUc WM Creal1. refresh Cgotps MUc WM Cgotps1. refresh Cps MUc WM Cps1.
    refresh SHU M0_2 WM SHU0. clear SHU.
    (* [comment removed for export] *)
    lazymatch type of M0_2 with munch ?W2 m ?mc =>
      assert (DR1 : dr AL_pboth rsegs D n0 f0 mc) by
        (eapply (DRF D m mc DR); intros a Ha; apply (M0_2 (Z_to_bv 64 a)); rewrite unsigned_lit;
         [| unfold depot_foot in Ha; cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha; unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha; unbox_places; lia];
         unfold depot_foot in Ha; cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha; unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha;
         cbn [outside]; destruct Ha as [Ha|[Ha|Ha]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply outside_of_disj; slia_big) end.
    clear M0_2.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with H : rw_cells rsegs mc (AB + rz_size n + -16) _ |- _ => rename H into HDR2 end end.
    callx (alloc_seg3_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n stkobj thr c sb AB q r8 d e n0 f0 _ _ _ D k olds dr)
      cleaning (clear TRC1 TRB1 SHA1 Ccan1 Cgotcf1 Cthr1 Cgotsh1 Cshoff1 Cgotmid1 Cgotmide1 Cgothi1 Chivars1 Cgotms1 Creal1 Cgotps1 Cps1 DR1 HDR2 SHU0).
    (* [comment removed for export] *)
    lazymatch goal with H : dr _ _ _ n0 f0 ?mdx |- _ => rename H into DRd;
      lazymatch goal with H2 : munch ?Wd mdx ?mc |- _ =>
        apply (munch_weaken Wd (alloc_hit_W2 sp thr c AB n q r8 d e)) in H2;
        [ rename H2 into MUd; unfold alloc_hit_W2 in MUd
        | unfold sub_fp, alloc_hit_W2; cbn [outside]; intros a Ho; slia ] end end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
                              (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096)] mc) as M3_5;
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (q + r8 + d + kShadowOffset, q + r8 + d + kShadowOffset + Z.min e 1);
                              (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8); (AB + rz_size n, AB + rz_size n + Z.min n 4096);
                              (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] mc) as M3_6;
      pose proof (wmono_refl rsegs mc) as WM3;
      lazymatch goal with H : rw_cells rsegs mc (AB + rz_size n + -16) _ |- _ => rename H into HDR3; cbv zeta in HDR3; box HDR3 end;
      lazymatch goal with H : bytes_at rsegs mc (q + r8 + kShadowOffset) _ |- _ => rename H into SHZ3; box SHZ3 end;
      lazymatch goal with H : wr_at rsegs mc (q + r8 + kShadowOffset) _ |- _ => rename H into SHW3; box SHW3 end end.
    (* [comment removed for export] *)
    refresh AF1 MUc WM AF1x. refresh AF2 MUc WM AF2x.
    refresh Ccan MUc WM Ccan1. refresh Cgotcf MUc WM Cgotcf1. refresh Cthr MUc WM Cthr1. refresh Cgotsh MUc WM Cgotsh1. refresh Cshoff MUc WM Cshoff1.
    refresh Cgotmid MUc WM Cgotmid1. refresh Cgotmide MUc WM Cgotmide1. refresh Cgothi MUc WM Cgothi1. refresh Chivars MUc WM Chivars1.
    refresh Cgotms MUc WM Cgotms1. refresh Creal MUc WM Creal1. refresh Cgotps MUc WM Cgotps1. refresh Cps MUc WM Cps1.
    lazymatch type of M0_3 with munch ?W3 m ?mc =>
      assert (SHP3 : e <> 0 -> rw_cells rsegs mc (q + r8 + d + kShadowOffset) [C1 oldp]) by
        (intros NE; apply (rw_cells_transport rsegs W3 m mc _ _ (SHP NE) M0_3 WM); disj) end.
    clear M0_3.
    callx (alloc_seg4_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n stkobj thr c sb AB q r8 d e oldp)
      cleaning (clear AF1x AF2x Ccan1 Cgotcf1 Cthr1 Cgotsh1 Cshoff1 Cgotmid1 Cgotmide1 Cgothi1 Chivars1 Cgotms1 Creal1 Cgotps1 Cps1 SHP3).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (munch_refl [(bv_unsigned sp - 1024, bv_unsigned sp + -128); (thr + 2800, thr + 2824); (thr + 2912 + 8 * c, thr + 2912 + 8 * c + 8);
                              (AB + rz_size n, AB + rz_size n + Z.min n 4096); (AB + rz_size n + -16, AB + rz_size n + -14); (AB, AB + 16)] mc) as M4_6;
      pose proof (wmono_refl rsegs mc) as WM4;
      lazymatch goal with H : e <> 0 -> rw_cells rsegs mc _ _ |- _ => rename H into SHE4 end end.
    (* [comment removed for export] *)
    refresh AF1 MUc WM AF1y. refresh AF44 MUc WM AF44y. refresh AF52 MUc WM AF52y.
    refresh Cini MUc WM Cini1. refresh Ckey MUc WM Ckey1. refresh Ctsd MUc WM Ctsd1. refresh Cctx MUc WM Cctx1. refresh Cthr2 MUc WM Cthr1x.
    refresh Ccan MUc WM Ccan1. refresh Cgotcf MUc WM Cgotcf1. refresh Cthr MUc WM Cthr1. refresh Cgotsh MUc WM Cgotsh1. refresh Cshoff MUc WM Cshoff1.
    refresh Cgotmid MUc WM Cgotmid1. refresh Cgotmide MUc WM Cgotmide1. refresh Cgothi MUc WM Cgothi1. refresh Chivars MUc WM Chivars1.
    refresh Cgotms MUc WM Cgotms1. refresh Creal MUc WM Creal1. refresh Cgotps MUc WM Cgotps1. refresh Cps MUc WM Cps1.
    (* [comment removed for export] *)
    lazymatch type of M0_4 with munch ?W04 _ _ =>
      first [ assert (D4thr : forall A k, 0 <= k -> thr + 2800 <= A -> A + k <= thr + 4096 -> disjoint_from W04 A k)
                by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl) | idtac "ATREF: D4thr not proved" ];
      first [ assert (D4ab : forall A k, 0 <= k -> AB + rz_size n <= A -> A + k <= sb + 2^37 -> disjoint_from W04 A k)
                by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl) | idtac "ATREF: D4ab not proved" ] end.
    refresh STS M0_4 WM STS0. refresh STA2 M0_4 WM STA20. refresh USR M0_4 WM USR0. clear STS STA2 USR M0_4. try clear D4thr. try clear D4ab.
    callx (alloc_seg5_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n stkobj canfill tsd ctx thr c sb AB)
      cleaning (clear AF1y AF44y AF52y Cini1 Ckey1 Ctsd1 Cctx1 Cthr1x Ccan1 Cgotcf1 Cthr1 Cgotsh1 Cshoff1 Cgotmid1 Cgotmide1 Cgothi1 Chivars1 Cgotms1 Creal1 Cgotps1 Cps1 STS0 STA20 USR0).
    (* [comment removed for export] *)
    refresh LS1 MUc WM LS1x. refresh LS2 MUc WM LS2x. refresh HK MUc WM HKx.
    assert (RZ32 : rz_size n <> 16 -> 32 <= rz_size n) by (pose proof (rz_size_cases n) as X; clear - X RSR; lia).
    lazymatch type of M0_5 with munch ?W5 m ?mc =>
      assert (ABH5 : rz_size n <> 16 -> rw_cells rsegs mc AB [C8 j0; C8 j1]) by
        (intros NE; pose proof (RZ32 NE) as RZ32'; apply (rw_cells_transport rsegs W5 m mc _ _ (ABH NE) M0_5 WM); disj) end.
    clear M0_5.
    refresh HDR3 M3_5 WM3 HDR5. clear HDR3 M3_5.
    pose proof (b1_mid_range (bv_unsigned b1w) ltac:(pose proof (bv_unsigned_in_range _ b1w); lia)) as B1MR.
    callx (alloc_seg6_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo n stkobj canfill thr c sb AB (b1_mid (bv_unsigned b1w)) (snd (depot_putC D k)))
      cleaning (clear LS1x LS2x HKx ABH5 HDR5).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of M2_6 with munch ?W26 _ _ =>
      first [ assert (D26thr : forall A k, 0 <= k -> thr <= A -> A + k <= thr + 2800 -> disjoint_from W26 A k)
                by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl) | idtac "ATREF: D26thr not proved" ];
      first [ assert (D26ri : forall A k, 0 <= k -> ri <= A -> A + k <= ri + 4096 -> disjoint_from W26 A k)
                by (intros A' k' Hk' HA' HB'; cbn [disjoint_from]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl) | idtac "ATREF: D26ri not proved" ] end.
    refresh LN2 M2_6 WM2 PCf. refresh STA2' M2_6 WM2 STAf. refresh MX2 M2_6 WM2 MXf. refresh NFC2 M2_6 WM2 NFCf. refresh NAL2 M2_6 WM2 NALf.
    lazymatch type of M2_6 with munch ?W26 ?m2 ?mc =>
      assert (FARRf : u32arr rsegs mc (free_array_of sb c + 4 * nf0) ws) by
        (unfold boxed in FARR2; apply (u32arr_transport rsegs W26 m2 mc _ _ FARR2 M2_6 WM2); cbn [disjoint_from]; rewrite LWS; unfold free_array_of; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; ivl) end.
    lazymatch type of M3_6 with munch ?W36 ?m3 ?mc =>
      assert (SHZf : bytes_at rsegs mc (q + r8 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat d))) by
        (unfold boxed in SHZ3; apply (bytes_at_transport rsegs W36 m3 mc _ _ SHZ3 M3_6); cbn [disjoint_from]; rewrite repeat_length, Z2Nat.id by lia; slia) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (SHWf : wr_at rsegs mc (q + r8 + kShadowOffset) d) by (unfold boxed in SHW3; exact (wr_at_transport rsegs _ mc _ _ SHW3 WM3));
      assert (SHEf : e <> 0 -> rw_cells rsegs mc (q + r8 + d + kShadowOffset) [C1 (Z_to_bv 8 e)]) by
        (intros NE; lazymatch type of M4_6 with munch ?W46 ?m4 mc =>
           apply (rw_cells_transport rsegs W46 m4 mc _ _ (SHE4 NE) M4_6 WM4); disj end) end.
    apply evt_done. unfold alloc_tail_post.
    hot_eexists_all.
    split; [reflexivity|].
    split; [exact MU|].
    split; [exact WM|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    all: first [eassumption | rewrite <- ?KSO; eassumption].
  Qed.
End AllocTail.

(* [comment removed for export] *)
Section Closed.
Context {Clg : Ceiling}.
  Theorem alloc_tail_ok : alloc_tail_stmt.
  Proof.
    unfold alloc_tail_stmt. intros until dr. cbv zeta. intros. eapply alloc_tail; eassumption.
  Qed.
End Closed.
