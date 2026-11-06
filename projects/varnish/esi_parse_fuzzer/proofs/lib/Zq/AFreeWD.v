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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtSeg3 ARtSf1m ARtSnjd ARtSrgm AMTac ARt2_lib ARt_u2d AMallocI.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeH AFreeH0 ANodijx ANod9v0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt4chi.

Module AFreeP.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt22wr ARt22fz AIcpnnp ARtSnjd AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt4chi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx.ARt27j4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2gfb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt23oh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2hw4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22wr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22fz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt4chi.AFreePB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @SBR; @Ha; @SPH; @NR; @IAMR; @R8; @PNB; @DN0; @DF0; @LPLO; @Bthr'; @ADN0; @ADF0; @LBthr; @H30; @SEP_pn; @SEP_pf; @TSDL; @Bctx'; @H15; @SEP_n0t; @SEP_f0t; @SEP_pc; @SEP_pt; @Hx; @H26; @KL; @DTOT; @KL2; @NQB; @POUT; @KLz; @KLz__])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietcz7.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_cfree_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietcz7.dl_tf_cfree_lia.
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
Definition free_prefixB_W (sp : word) (lo thr p n0 f0 : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (thr + 3168, thr + 3168 + 1); (p + -16, p + -12); (p, p + 8);
   (thr + 2824, thr + 2840); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000)].
Definition free_prefixB0_W (sp : word) (lo thr p n0 f0 : Z) : list (Z * Z) :=
  free_prefixB_W sp lo thr p n0 f0 ++
  [(0x144648, 0x14464c); (IAB, IAB + 1); (IAB + 8, IAB + 8 + 262144); (IAB + 0x40040, IAB + 0x40040 + 3456);
   (IAB + 0x40dc0, IAB + 0x40dc0 + 262728); (IAB + 0x81008, IAB + 0x81008 + 40)].

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
Local Ltac fside_asm := first
  [ lazymatch goal with
    | |- rw_cells ?s ?m ?a _ => match goal with H : rw_cells s m a _ |- _ => exact H end
    | |- ro_cells ?s ?m ?a _ => match goal with H : ro_cells s m a _ |- _ => exact H end
    end
  | eassumption ].
Local Ltac fside_tail E := lazymatch goal with |- ?g => tryif has_evar g then first [ fside_asm | eqrefl ]
             else first [ fside_asm | eqrefl | lia | unfold QINST, AINST; kung; lia | rewrite <- E; fside_asm
                        | match goal with S : sh _ = _ |- _ => rewrite S; fside_asm end | left; kung; lia
                        | rewrite ?unsigned_lit by lia; first [fside_asm | lia | kung; lia]
                        | kung; slia
                        | apply mod_add_lit; [lia | assumption | reflexivity]
                        | lazymatch goal with |- _ \/ _ => unfold boxed in *; kung; lia end ]
 end.
Local Ltac fside E ::=
  lazymatch goal with
  | |- apart _ _ _ _ => fail
  | |- forall _ : word, _ => fail
  | |- forall _ : machine_state, _ => fail
  | |- poison_consts _ => unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; fside_asm
  | |- aobj _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else faobj end
  | |- aobjK _ _ => apply aobjK_i; faobj
  | |- pz_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else fpz end
  | |- pz0_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- fl_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- m2s_in _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- _ \/ _ => first [ solve [kung; slia] | fside_tail E ]
  | |- _ => fside_tail E
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@LO; @Bthr'; @SBR; @LPLO; @Bctx'; @LBthr; @PNB; @NR; @R8; @LBctx2; @ADN0; @DN0; @ADF0; @DF0])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= hot_tf_cut; hot_tf_lia0.
(* [comment removed for export] *)
Section FreeBig.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p n b1 tsd ctx thr top bot r8 n0 f0 fr fd : Z) (D : list (list Z)) (old : word) (sb : Z).

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
  Hypothesis NQB : 2^28 < n.
  Hypothesis R8 : 8 * r8 - 8 < n <= 8 * r8.
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 3 = 1.
  Hypothesis HDR : rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)].
  Hypothesis CTX0 : rw_cells rsegs m p [C8 old].
  (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis POUT : p + -16 < sb \/ sb + 2^37 <= p + -16.
  Hypothesis CSB : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
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

  #[using="SEP_tc SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_pf SEP_pn SEP_pt SEP_pc DF0 DN0 DTOT DLEN DND DR FDR FRR TST TUNW TDT TTB TSDL CT8 TH0 TC PCo FCo CSB POUT SBR CTX0 HDR B1M B1R R8 NQB NR PNB PLO PAL TPE BOTR TOPR VLE RANE RA0 SPH SPA LO ST MI sb old r8 ctx tsd Clg"] Lemma free_prefixB : ro_cells rsegs m (0xb5dc8 + 8 * Z.shiftr p 32) [C8 (wz 0)] ->   (* [comment removed for export] *)
    ro_cells rsegs m 0x144648 [C1 (Z_to_bv 8 1)] -> forall (Q : machine_state -> Prop),
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (jrest pad jb1 : list byte) (m' : word -> option byte),
        (* [comment removed for export] *)
        rw_cells rsegs m' (fp + -2128) [C8 (wz (fp + -2128 + 16))] ->
        rw_cells rsegs m' (fp + -2128 + 32) [CB 2024 jrest] ->
        rw_cells rsegs m' (fp + -2128 + 2056) [C8 (wz fp)] ->
        rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz (dep_w8 top bot fp))] ->
        rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58994); CB 8 (dep_b16 top bot fp ra jb1)] ->
        rw_cells rsegs m' (fp + -2128 + 12) [C4 (wz 0)] ->
        rw_cells rsegs m' (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m' (fp + -2128 + -80) [C8 (wz (thr + 208)); C8 (wz (fp + -2128)); C8 s6; C8 (wz (fp + -81)); C8 (wz (fp + -2128));
                                            C8 (wz 1); C8 (wz 0x58994); C8 (wz p); C8 (wz fp); C8 (wz 0x58a04)] ->
        (* [comment removed for export] *)
        rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (thr + 8) [C8 (wz top); C8 (wz bot)] ->
        rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
        rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        rw_cells rsegs m' p [C8 (wz fid)] ->
        depot_repL AL_pboth rsegs D' n0 f0 m' ->
        munch (free_prefixB_W sp lo thr p n0 f0) m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (fp + -2128 - 80) ->
        evt rsegs Q (MS (mkR (wz qput_recret) (wz (fp + -2128 + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                            (wz (fp + -2128 + -80)) (wz (p + -16)) (wz (thr + 208)) (wz (fp + -2128)) (wz (p + -16)) (wz n) a6' a7'
                            (wz 0x58994) (wz 1) (wz (fp + -2128)) (wz (fp + -81)) (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz cbrec_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x5884c) fc None m (seg_rom rsegs)).
  Proof. try clear RA2. try clear PHI.   (* [comment removed for export] *)
    intros IAM Fiai Q K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof FCo as FC'. (first [ dand9 FC' as Fini Fmcs Fgotcf Ffu Fhook Fgotfl Fffs Fqmax Fcmax | destruct FC' as (Fini & Fmcs & Fgotcf & Ffu & Fhook & Fgotfl & Fffs & Fqmax & Fcmax) ]).
    unfold free_prefixB_W, qput_recret, cbrec_entry, QINST, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kStackStoreBlockFrames, off_th_unwinding in *.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    rewrite TPL in *. change (6192088 - 88) with 6192000 in Ctsd.
    (* [comment removed for export] *)
    assert (IAMR : 0 <= Z.shiftr p 32 < 2^15).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^15) with (2^47). lia. }
    set (p32 := Z.shiftr p 32) in *. assert (P32E : p32 = Z.shiftr p 32) by reflexivity. clearbody p32.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    rewrite ?SHF in *.
    (* [comment removed for export] *)
    amz.
    (* [comment removed for export] *)
    eapply free_pro_ok; [exact MI| exact ST| lia|].
    intros junk pad m1 FRO SAV MU1 WM1 MI1 ST1.
    rewrite ?unsigned_lit in FRO, SAV, MU1, ST1 by lia.
    xfer Cini MU1 WM1. xfer Ckey MU1 WM1. xfer Ctsd MU1 WM1. xfer Cctx MU1 WM1. xfer Cthr2 MU1 WM1.
    xfer Ccan MU1 WM1. xfer Cgotcf MU1 WM1. xfer Cthr MU1 WM1. xfer Cgotsh MU1 WM1. xfer Cshoff MU1 WM1. xfer Cgotmid MU1 WM1.
    xfer Cgotmide MU1 WM1. xfer Cgothi MU1 WM1. xfer Chivars MU1 WM1. xfer Cgotms MU1 WM1. xfer Creal MU1 WM1. xfer Cgotps MU1 WM1. xfer Cps MU1 WM1.
    xfer Fini MU1 WM1. xfer Fiai MU1 WM1. xfer Fmcs MU1 WM1. xfer Fgotcf MU1 WM1. xfer Ffu MU1 WM1. xfer Fhook MU1 WM1. xfer Fgotfl MU1 WM1.
    xfer Fffs MU1 WM1. xfer Fqmax MU1 WM1. xfer Fcmax MU1 WM1.
    xfer IAM MU1 WM1. xfer TH0 MU1 WM1. xfer CT8 MU1 WM1. xfer TTB MU1 WM1. xfer TDT MU1 WM1. xfer TUNW MU1 WM1. xfer TST MU1 WM1.
    xfer HDR MU1 WM1. xfer CTX0 MU1 WM1. xfer CSB MU1 WM1.
    assert (DR1 : depot_repL AL_pboth rsegs D n0 f0 m1).
    { eapply (depot_repL_agree _ _ D n0 f0 m m1 DR). intros a Ha. apply (MU1 (Z_to_bv 64 a)).
      unfold depot_foot in Ha; cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha; unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha.
      destruct Ha as [Ha|[Ha|Ha]]; rewrite unsigned_lit by lia; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply outside_of_disj; slia. }
    clear DR MI ST.
    (* [comment removed for export] *)
    assert (MU : munch (free_prefixB_W sp lo thr p n0 f0) m m1).
    { unfold free_prefixB_W. eapply munch_weaken; [| exact MU1]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    unfold free_prefixB_W in MU. pose proof WM1 as WM. clear MU1 WM1.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (ia_fast_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo)|];
      [exact MI1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; lia| lia| exact Fiai| reflexivity|].
    intros ms' PO. destruct_exs PO. (first [ dand5 PO as E MUc WMc MI2 ST2 | destruct PO as (E & MUc & WMc & MI2 & ST2) ]). subst ms'. rewrite ?unsigned_lit in MUc, ST2 by lia.
    xdepot DR1 MUc. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 362640)) with (Z_to_bv 64 362640) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    (* [comment removed for export] *)
    (first [ pose proof ((obj_reshape m2 _ _ FRO)) as dR_6; dex4 dR_6 as j0 j3 j12 jb; rename dR_6 into OBJ | pose proof ((obj_reshape m2 _ _ FRO)) as dR_6; dand5 dR_6 as j0 j3 j12 jb OBJ | destruct (obj_reshape m2 _ _ FRO) as (j0 & j3 & j12 & jb & OBJ) ]). clear FRO.
    assert (TC2 : thread_cells m2 tp tsd ctx thr) by tcells TPL.
    rewrite <- (Z_to_bv_bv_unsigned sp). rewrite !(unsigned_lit fp) by lia.
    eapply (free_mid_ok _ gp tp _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 fp p tsd ctx thr top bot lo ra s0 s5 s4 s3 s2 s1 j0 j3 pad j12 jb);
      [> try (fside P32E) .. | idtac].
    intros t0b t1b t2b a6b a7b t3b t4b t5b t6b jb1 jrest m3 O0 O32 PFP DEP O12 TUNW3 SAV3 MU3 WM3 MI3 ST3. unfa.
    apply fdep_cells in DEP. destruct DEP as [D8 D16].
    clear TUNW. xdepot DR1 MU3. kpost MU3 WM3.
    assert (TC3 : thread_cells m3 tp tsd ctx thr) by tcells TPL. clear TC2.
    (* [comment removed for export] *)
    eapply (dealloc_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 AINST p n b1 (fp + -2128) tsd ctx thr fr fd lo old);
      [> try (fside P32E) .. | idtac].
    intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 HDR4 CTX4 TST4 MU4 WM4 MI4 ST4. unfa.
    rewrite ?unsigned_lit in MU4, ST4 by lia.
    clear HDR CTX0 TST. xdepot DR1 MU4. kpost MU4 WM4.
    assert (TC4 : thread_cells m4 tp tsd ctx thr) by tcells TPL. clear TC3.
    (* [comment removed for export] *)
    destruct (ftrc_cells m4 top bot fp ra jb1 (fp + -2128) O0 D8 O12 D16) as [TRC TRB].
    pose proof (free_key_len top bot fp ra) as KL. pose proof (free_key_range top bot fp ra) as KR. pose proof (free_key_len2 top bot fp ra) as KL2.
    fold KEY in TRC, TRB, KL, KR, KL2.
    eapply (qchunk_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 AINST p n b1 (fp + -2128) tsd ctx thr lo D KEY (fp + -2128 + 16) n0 f0);
      [> try (fside P32E) .. | idtac].
    intros t0d t1d t2d a6d a7d t3d t4d t5d t6d m5 HDR5 CTX5 DR5 MU5 WM5 MI5 ST5. unfa.
    rewrite ?unsigned_lit in MU5, ST5 by lia. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in MU5.
    unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in MU5. change (5860008 + 8 * 2 ^ 15) with 6122152 in MU5.
    clear HDR4 CTX4 DR1 TRC TRB. kpost MU5 WM5.
    assert (TC5 : thread_cells m5 tp tsd ctx thr) by tcells TPL. clear TC4.
    (* [comment removed for export] *)
    change (AINST + 728) with QINST.
    eapply (qput_pre_big_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 QINST (thr + 80) (thr + 208) (fp + -2128) p n (2^28) (2^20) sb lo);
      [> try (fside P32E) .. | idtac].
    intros m6 PFR MU6 WM6 MI6 ST6. unfa.
    rewrite ?unsigned_lit in PFR, MU6, ST6 by lia.
    xdepot DR5 MU6. kpost MU6 WM6.
    rewrite unsigned_lit by lia.
    eapply K; unfa; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

End FreeBig.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
End AFreeP.


Module AFreeP0.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw ARt20wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt23nw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt22wr ARt22fz AIcpnnp ARtSnjd AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt4chi.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx.ARt27j4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2gfb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2e3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt20wx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt23oh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt23nw.ARt2hw4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22wr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt22fz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt4chi.AFreePB.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @SPR; @LWS; @CV; @PNB; @Ha; @ADN0; @ADF0; @NQB; @R8; @LO0; @KL; @KL2; @SBR; @LBthr; @LPLO; @IAMR; @Bthr'; @H30; @H31; @H33; @NR; @SEP_pn; @SEP_pf; @Bctx'; @HyS; @SEP_n0t; @SEP_f0t; @SEP_pc; @SEP_pt; @SPH; @PQ; @Btsd'; @TSDL; @H26; @H27; @H29; @DTOT; @POUT; @H15; @H16; @H18; @KLz; @KLz__])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietcz7.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_cfree_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietcz7.dl_tf_cfree_lia.
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
Definition free_prefixB_W (sp : word) (lo thr p n0 f0 : Z) : list (Z * Z) :=
  [(lo, bv_unsigned sp); (thr + 3168, thr + 3168 + 1); (p + -16, p + -12); (p, p + 8);
   (thr + 2824, thr + 2840); (0x186a88, 0x5d6aa8); (n0, n0 + 0x100000); (f0, f0 + 0x800000)].
Definition free_prefixB0_W (sp : word) (lo thr p n0 f0 : Z) : list (Z * Z) :=
  free_prefixB_W sp lo thr p n0 f0 ++
  [(0x144648, 0x14464c); (IAB, IAB + 1); (IAB + 8, IAB + 8 + 262144); (IAB + 0x40040, IAB + 0x40040 + 3456);
   (IAB + 0x40dc0, IAB + 0x40dc0 + 262728); (IAB + 0x81008, IAB + 0x81008 + 40)].

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
Local Ltac fside_asm := first
  [ lazymatch goal with
    | |- rw_cells ?s ?m ?a _ => match goal with H : rw_cells s m a _ |- _ => exact H end
    | |- ro_cells ?s ?m ?a _ => match goal with H : ro_cells s m a _ |- _ => exact H end
    end
  | eassumption ].
Local Ltac fside_tail E := lazymatch goal with |- ?g => tryif has_evar g then first [ fside_asm | eqrefl ]
             else first [ fside_asm | eqrefl | lia | unfold QINST, AINST; kung; lia | rewrite <- E; fside_asm
                        | match goal with S : sh _ = _ |- _ => rewrite S; fside_asm end | left; kung; lia
                        | rewrite ?unsigned_lit by lia; first [fside_asm | lia | kung; lia]
                        | kung; slia
                        | apply mod_add_lit; [lia | assumption | reflexivity]
                        | lazymatch goal with |- _ \/ _ => unfold boxed in *; kung; lia end ]
 end.
Local Ltac fside E ::=
  lazymatch goal with
  | |- apart _ _ _ _ => fail
  | |- forall _ : word, _ => fail
  | |- forall _ : machine_state, _ => fail
  | |- poison_consts _ => unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; fside_asm
  | |- aobj _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else faobj end
  | |- aobjK _ _ => apply aobjK_i; faobj
  | |- pz_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else fpz end
  | |- pz0_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- fl_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- m2s_in _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- _ \/ _ => first [ solve [kung; slia] | fside_tail E ]
  | |- _ => fside_tail E
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@LO; @SBR; @PNB; @LBthr; @Bthr'; @LPLO; @LBctx2; @Bctx'; @R8; @NR; @DN0; @DF0; @ADN0; @ADF0])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= first [ solve [ hot_tf_cut; hot_tf_lia0 ] | hot_tf_lia0 ].
(* [comment removed for export] *)
Section FreeBig.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo p n b1 tsd ctx thr top bot r8 n0 f0 fr fd : Z) (D : list (list Z)) (old : word) (sb : Z).

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
  Hypothesis NQB : 2^28 < n.
  Hypothesis R8 : 8 * r8 - 8 < n <= 8 * r8.
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 3 = 1.
  Hypothesis HDR : rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)].
  Hypothesis CTX0 : rw_cells rsegs m p [C8 old].
  (* [comment removed for export] *)
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis POUT : p + -16 < sb \/ sb + 2^37 <= p + -16.
  Hypothesis CSB : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
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

  #[using="SEP_tc SEP_f0c SEP_n0c SEP_f0t SEP_n0t SEP_pf SEP_pn SEP_pt SEP_pc DF0 DN0 DTOT DLEN DND DR FDR FRR TST TUNW TDT TTB TSDL CT8 TH0 TC PCo FCo CSB POUT SBR CTX0 HDR B1M B1R R8 NQB NR PNB PLO PAL TPE BOTR TOPR VLE RANE RA0 SPH SPA LO ST MI sb old r8 ctx tsd Clg"] Lemma free_prefixB0 : forall (hi : Z) (ij0 : byte) (ij1 ij3 ij4 : list byte) (ws : list word),
    0 <= hi < 2^15 ->
    rw_cells rsegs m 0x144648 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz hi)] ->
    rw_cells rsegs m IAB [C1 ij0] ->
    rw_cells rsegs m (IAB + 8) [CB (Z.to_nat 262144) ij1] ->
    u64arr rsegs m (IAB + 0x40040) ws -> length ws = 432%nat ->
    rw_cells rsegs m (IAB + 0x40dc0) [CB (Z.to_nat 262728) ij3] ->
    rw_cells rsegs m (IAB + 0x81008) [CB 40 ij4] ->
    forall (Q : machine_state -> Prop),
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (jrest pad jb1 : list byte) (m' : word -> option byte),
        (* [comment removed for export] *)
        rw_cells rsegs m' (fp + -2128) [C8 (wz (fp + -2128 + 16))] ->
        rw_cells rsegs m' (fp + -2128 + 32) [CB 2024 jrest] ->
        rw_cells rsegs m' (fp + -2128 + 2056) [C8 (wz fp)] ->
        rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz (dep_w8 top bot fp))] ->
        rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58994); CB 8 (dep_b16 top bot fp ra jb1)] ->
        rw_cells rsegs m' (fp + -2128 + 12) [C4 (wz 0)] ->
        rw_cells rsegs m' (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m' (fp + -2128 + -80) [C8 (wz (thr + 208)); C8 (wz (fp + -2128)); C8 s6; C8 (wz (fp + -81)); C8 (wz (fp + -2128));
                                            C8 (wz 1); C8 (wz 0x58994); C8 (wz p); C8 (wz fp); C8 (wz 0x58a04)] ->
        (* [comment removed for export] *)
        rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (thr + 8) [C8 (wz top); C8 (wz bot)] ->
        rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->
        rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        rw_cells rsegs m' p [C8 (wz fid)] ->
        depot_repL AL_pboth rsegs D' n0 f0 m' ->
        (* [comment removed for export] *)
        rw_cells rsegs m' 0x144648 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (wz hi)] ->
        rw_cells rsegs m' IAB [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (IAB + 8) [CB (Z.to_nat 262144) (repeat (Z_to_bv 8 0) (Z.to_nat 262144))] ->
        u64arr rsegs m' (IAB + 0x40040) (repeat (wz 0) 432) ->
        rw_cells rsegs m' (IAB + 0x40dc0) [C8 (wz 4096); C8 (wz (IAB + 0x40dd0)); CB (Z.to_nat 262712) (repeat (Z_to_bv 8 0) (Z.to_nat 262712))] ->
        rw_cells rsegs m' (IAB + 0x81008) [CB 40 (repeat (Z_to_bv 8 0) 40)] ->
        munch (free_prefixB0_W sp lo thr p n0 f0) m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (fp + -2128 - 80) ->
        evt rsegs Q (MS (mkR (wz qput_recret) (wz (fp + -2128 + -80)) gp tp t0' t1' t2' (wz QINST) (wz (thr + 80))
                            (wz (fp + -2128 + -80)) (wz (p + -16)) (wz (thr + 208)) (wz (fp + -2128)) (wz (p + -16)) (wz n) a6' a7'
                            (wz 0x58994) (wz 1) (wz (fp + -2128)) (wz (fp + -81)) (wz (2^20)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz cbrec_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x5884c) fc None m (seg_rom rsegs)).
  Proof. try clear RA2. try clear PHI.   (* [comment removed for export] *)
    intros hi ij0 ij1 ij3 ij4 ws HIR IA0 RIAB RMAP RST LWS RSEC RPAD Q K.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof FCo as FC'. (first [ dand9 FC' as Fini Fmcs Fgotcf Ffu Fhook Fgotfl Fffs Fqmax Fcmax | destruct FC' as (Fini & Fmcs & Fgotcf & Ffu & Fhook & Fgotfl & Fffs & Fqmax & Fcmax) ]).
    unfold free_prefixB0_W, free_prefixB_W, qput_recret, cbrec_entry, IAB, QINST, kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kStackStoreBlockFrames, off_th_unwinding in *.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    rewrite TPL in *. change (6192088 - 88) with 6192000 in Ctsd.
    (* [comment removed for export] *)
    assert (IAMR : 0 <= Z.shiftr p 32 < 2^15).
    { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^15) with (2^47). lia. }
    set (p32 := Z.shiftr p 32) in *. assert (P32E : p32 = Z.shiftr p 32) by reflexivity. clearbody p32.
    set (pq := p / 16) in *. assert (PQ : p = 16 * pq) by (subst pq; rewrite (Z_div_mod_eq_full p 16) at 1; rewrite PAL; lia).
    clearbody pq.
    assert (SHF : sh p = 2 * pq + 2147450880) by (unfold sh, kShadowOffset; rewrite PQ; replace (16 * pq) with ((2 * pq) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    rewrite ?SHF in *.
    (* [comment removed for export] *)
    amz.
    (* [comment removed for export] *)
    eapply free_pro_ok; [exact MI| exact ST| lia|].
    intros junk pad m1 FRO SAV MU1 WM1 MI1 ST1.
    rewrite ?unsigned_lit in FRO, SAV, MU1, ST1 by lia.
    xfer Cini MU1 WM1. xfer Ckey MU1 WM1. xfer Ctsd MU1 WM1. xfer Cctx MU1 WM1. xfer Cthr2 MU1 WM1.
    xfer Ccan MU1 WM1. xfer Cgotcf MU1 WM1. xfer Cthr MU1 WM1. xfer Cgotsh MU1 WM1. xfer Cshoff MU1 WM1. xfer Cgotmid MU1 WM1.
    xfer Cgotmide MU1 WM1. xfer Cgothi MU1 WM1. xfer Chivars MU1 WM1. xfer Cgotms MU1 WM1. xfer Creal MU1 WM1. xfer Cgotps MU1 WM1. xfer Cps MU1 WM1.
    xfer Fini MU1 WM1. xfer Fmcs MU1 WM1. xfer Fgotcf MU1 WM1. xfer Ffu MU1 WM1. xfer Fhook MU1 WM1. xfer Fgotfl MU1 WM1.
    xfer Fffs MU1 WM1. xfer Fqmax MU1 WM1. xfer Fcmax MU1 WM1.
    xfer TH0 MU1 WM1. xfer CT8 MU1 WM1. xfer TTB MU1 WM1. xfer TDT MU1 WM1. xfer TUNW MU1 WM1. xfer TST MU1 WM1.
    xfer HDR MU1 WM1. xfer CTX0 MU1 WM1. xfer CSB MU1 WM1.
    xfer IA0 MU1 WM1. xfer RIAB MU1 WM1. xferbig RMAP MU1 WM1. xferbig RST MU1 WM1. xferbig RSEC MU1 WM1. xfer RPAD MU1 WM1.
    assert (DR1 : depot_repL AL_pboth rsegs D n0 f0 m1).
    { eapply (depot_repL_agree _ _ D n0 f0 m m1 DR). intros a Ha. apply (MU1 (Z_to_bv 64 a)).
      unfold depot_foot in Ha; cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha; unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in Ha.
      destruct Ha as [Ha|[Ha|Ha]]; rewrite unsigned_lit by lia; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply outside_of_disj; slia. }
    clear DR MI ST.
    (* [comment removed for export] *)
    pose proof WM1 as WM. clear WM1.
    (* [comment removed for export] *)
    eapply evt_cut; [eapply (ia_init_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 hi lo ij0 ij1 ij3 ij4 ws)|];
      [ exact MI1| rewrite unsigned_lit by lia; exact ST1| rewrite unsigned_lit by lia; lia| lia| exact HIR| exact IA0| exact Cgotps| exact Cps
      | exact RIAB| exact RMAP| exact RST| exact LWS| exact RSEC| exact RPAD| reflexivity|].
    clear IA0 RIAB RMAP RST RSEC RPAD.
    intros ms' PO. destruct_exs PO. (first [ dand11 PO as E MUc WMc MI2 ST2 IA1 RIAB RMAP RST RSEC RPAD | destruct PO as (E & MUc & WMc & MI2 & ST2 & IA1 & RIAB & RMAP & RST & RSEC & RPAD) ]). subst ms'.
    unfold IAB in MUc, RIAB, RMAP, RST, RSEC, RPAD. rewrite ?unsigned_lit in MUc, ST2 by lia.
    lazymatch type of MUc with munch _ _ ?mc => rename mc into m2 end.
    (* [comment removed for export] *)
    assert (MU2 : munch (free_prefixB0_W sp lo thr p n0 f0) m m2).
    { intros y Hy. apply outside_app in Hy. destruct Hy as [HyA HyB].
      unfold free_prefixB_W in HyA. unfold IAB in HyB. cbn [outside] in HyA, HyB. destruct HyA as [HyS _].
      rewrite (MUc y); [apply (MU1 y); cbn [outside]; try (generalize alloc_ceiling_val); clear -HyS LO SPR; try pose proof alloc_ceiling_val; lia|]. cbn [outside]. split; [try (generalize alloc_ceiling_val); clear -HyS LO SPR; try pose proof alloc_ceiling_val; lia| exact HyB]. }
    kp MU2. clear MU1.
    (* [comment removed for export] *)
    assert (IAM2 : ro_cells rsegs m2 (744904 + 8 * p32) [C8 (wz 0)]) by (apply (zeros_word_at m2 744904 262144 (8 * p32) RMAP); lia).
    (* [comment removed for export] *)
    kp IA1. kp RIAB. kp RMAP. kp RST. kp RSEC. kp RPAD.
    xdepot DR1 MUc. kpost MUc WMc.
    pose proof (munch_refl (free_prefixB_W sp lo thr p n0 f0) m2) as MUB. unfold free_prefixB_W in MUB.
    pose proof (wmono_refl rsegs m2) as WMB.
    replace (ret_pc (Z_to_bv 64 362640)) with (Z_to_bv 64 362640) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    (* [comment removed for export] *)
    (first [ pose proof ((obj_reshape m2 _ _ FRO)) as dR_6; dex4 dR_6 as j0 j3 j12 jb; rename dR_6 into OBJ | pose proof ((obj_reshape m2 _ _ FRO)) as dR_6; dand5 dR_6 as j0 j3 j12 jb OBJ | destruct (obj_reshape m2 _ _ FRO) as (j0 & j3 & j12 & jb & OBJ) ]). clear FRO.
    assert (TC2 : thread_cells m2 tp tsd ctx thr) by tcells TPL.
    rewrite <- (Z_to_bv_bv_unsigned sp). rewrite !(unsigned_lit fp) by lia.
    eapply (free_mid_ok _ gp tp _ _ _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 fp p tsd ctx thr top bot lo ra s0 s5 s4 s3 s2 s1 j0 j3 pad j12 jb);
      [> try (fside P32E) .. | idtac].
    intros t0b t1b t2b a6b a7b t3b t4b t5b t6b jb1 jrest m3 O0 O32 PFP DEP O12 TUNW3 SAV3 MU3 WM3 MI3 ST3. unfa.
    apply fdep_cells in DEP. destruct DEP as [D8 D16].
    clear TUNW. xdepot DR1 MU3. kpost MU3 WM3.
    assert (TC3 : thread_cells m3 tp tsd ctx thr) by tcells TPL. clear TC2.
    (* [comment removed for export] *)
    eapply (dealloc_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 AINST p n b1 (fp + -2128) tsd ctx thr fr fd lo old);
      [> try (fside P32E) .. | idtac].
    intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 HDR4 CTX4 TST4 MU4 WM4 MI4 ST4. unfa.
    rewrite ?unsigned_lit in MU4, ST4 by lia.
    clear HDR CTX0 TST. xdepot DR1 MU4. kpost MU4 WM4.
    assert (TC4 : thread_cells m4 tp tsd ctx thr) by tcells TPL. clear TC3.
    (* [comment removed for export] *)
    destruct (ftrc_cells m4 top bot fp ra jb1 (fp + -2128) O0 D8 O12 D16) as [TRC TRB].
    pose proof (free_key_len top bot fp ra) as KL. pose proof (free_key_range top bot fp ra) as KR. pose proof (free_key_len2 top bot fp ra) as KL2.
    fold KEY in TRC, TRB, KL, KR, KL2.
    eapply (qchunk_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 AINST p n b1 (fp + -2128) tsd ctx thr lo D KEY (fp + -2128 + 16) n0 f0);
      [> try (fside P32E) .. | idtac].
    intros t0d t1d t2d a6d a7d t3d t4d t5d t6d m5 HDR5 CTX5 DR5 MU5 WM5 MI5 ST5. unfa.
    rewrite ?unsigned_lit in MU5, ST5 by lia. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in MU5.
    unfold kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in MU5. change (5860008 + 8 * 2 ^ 15) with 6122152 in MU5.
    clear HDR4 CTX4 DR1 TRC TRB. kpost MU5 WM5.
    assert (TC5 : thread_cells m5 tp tsd ctx thr) by tcells TPL. clear TC4.
    (* [comment removed for export] *)
    change (AINST + 728) with QINST.
    eapply (qput_pre_big_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 QINST (thr + 80) (thr + 208) (fp + -2128) p n (2^28) (2^20) sb lo);
      [> try (fside P32E) .. | idtac].
    intros m6 PFR MU6 WM6 MI6 ST6. unfa.
    rewrite ?unsigned_lit in PFR, MU6, ST6 by lia.
    xdepot DR5 MU6. kpost MU6 WM6.
    rewrite unsigned_lit by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m6 end.
    unfa. unfold IAB.
    (* [comment removed for export] *)
    unfold keep in IA1, RIAB, RMAP, RST, RSEC, RPAD.
    xferb IA1 MUB WMB. xferb RIAB MUB WMB. xferb RMAP MUB WMB. xferb RST MUB WMB. xferb RSEC MUB WMB. xferb RPAD MUB WMB.
    unfold keep in MU2.
    assert (MUF : munch (free_prefixB0_W sp lo thr p n0 f0) m m6).
    { intros y Hy. rewrite <- (MU2 y Hy). apply MUB. apply outside_app in Hy. destruct Hy as [HyA _].
      unfold free_prefixB_W in HyA. exact HyA. }
    clear MU2 MUB. unfold free_prefixB0_W, free_prefixB_W, IAB in MUF. cbn [app] in MUF |- .
    eapply K.
    all: kcell.
  Qed.


End FreeBig.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
End AFreeP0.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeS AFreeT.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSeg3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSf1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANod9v0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt4chi.AFreePB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeWD.AFreeP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeWD.AFreeP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
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
Definition free_directS0_W (ia0 : bool) (sp : word) (lo thr p n0 f0 pa idx hla h msz : Z) : list (Z * Z) :=
  free_prefixB_W sp lo thr p n0 f0
  ++ [(0xb1800, 0xb1804); (thr + 2840, thr + 2856); (0xb15d0, 0xb15d9); (0xb15e8, 0xb15f8); (0xb1818, 0xb1828);
      (pa + 8 * idx, pa + 8 * idx + 8); (hla + 24, hla + 32); (sh h, sh h + msz / 8); (thr + 2888, thr + 2904)]
  ++ ia_Wk ia0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ro_cells_ag : forall (m m' : mem) A cs,
  ro_cells rsegs m A cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wz (A + i)) = m (wz (A + i))) -> ro_cells rsegs m' A cs.
Proof.
  intros m m' A cs [WF B] AG. split; [exact WF|]. eapply bytes_at_agree_gen; [exact B|]. rewrite cells_bytes_length by exact WF. exact AG.
Qed.
Lemma rw_cells_ag : forall (m m' : mem) A cs,
  rw_cells rsegs m A cs -> wmono rsegs m m' -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wz (A + i)) = m (wz (A + i))) -> rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[WF B] WR] WM AG. split; [split; [exact WF|]|].
  - eapply bytes_at_agree_gen; [exact B|]. rewrite cells_bytes_length by exact WF. exact AG.
  - eapply wr_at_transport; [exact WR| exact WM].
Qed.
(* [comment removed for export] *)
Definition img_quiet (x : Z) : Prop :=
  (0x10000 <= x < 0xb15d0) \/ (0xb1828 <= x < 0xb5dc0) \/ (0x136df0 <= x < 0x144648) \/ (0x14464c <= x < 0x186a88) \/ (0x5d6aa8 <= x < 0x60a000).
(* [comment removed for export] *)
Definition img_quiet1 (x : Z) : Prop := img_quiet x \/ (0xb15d0 <= x < 0xb1828).
(* [comment removed for export] *)
Ltac img_xfer H m2 AG WM :=
  lazymatch type of H with
  | ro_cells _ ?mm ?A ?cs => apply (ro_cells_ag mm m2 A cs) in H; [| intros i Hi; apply AG; clear -Hi; unfold img_quiet1, img_quiet; cbn [cells_size csize Nat.add] in Hi; lia]
  | rw_cells _ ?mm ?A ?cs => apply (rw_cells_ag mm m2 A cs) in H; [| exact WM | intros i Hi; apply AG; clear -Hi; unfold img_quiet1, img_quiet; cbn [cells_size csize Nat.add] in Hi; lia]
  end.

Section FreeDirect.
  Context {Clg : Ceiling}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  (* [comment removed for export] *)
  Variables (lo p n b1 tsd ctx thr top bot r8 n0 f0 fr fd : Z) (D : list (list Z)) (old : word) (sb : Z).
  (* [comment removed for export] *)
  Variables (pa u1 u2 srt h msz csz idx nf ca gA gM rf rfd mu md sealed : Z) (hs : list word) (hl hlb hlm hls canary : word) (oldsh : list byte).

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation nch := (Z.of_nat (length hs)).
  #[warnings="-notation-for-abbreviation"] Local Notation hla := (bv_unsigned hl).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 2688.
  Hypothesis LOD : lo <= bv_unsigned sp - 2832.   (* [comment removed for export] *)
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
  Hypothesis PLO : aobj (p + -16) (16 + 8 * r8).
  Hypothesis PNB : 0x60a000 <= p + -16.
  Hypothesis PHI : p + 8 * r8 <= alloc_ceiling.
  Hypothesis NR : 1 <= n < 2^32.
  Hypothesis NQB : 2^28 < n.
  Hypothesis R8 : 8 * r8 - 8 < n <= 8 * r8.
  Hypothesis B1R : 0 <= b1 < 256.
  Hypothesis B1M : Z.land b1 3 = 1.
  Hypothesis HDR : rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)].
  Hypothesis CTX0 : rw_cells rsegs m p [C8 old].
  Hypothesis SBR : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling.
  Hypothesis POUT : p + -16 < sb \/ sb + 2^37 <= p + -16.
  Hypothesis CSB : ro_cells rsegs m 0xb1578 [C8 (wz sb)].
  (* [comment removed for export] *)
  Hypothesis FCo : free_consts m.
  Hypothesis PCo : poison_consts m.
  Hypothesis IAM : ro_cells rsegs m (0xb5dc8 + 8 * Z.shiftr p 32) [C8 (wz 0)].   (* [comment removed for export] *)
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
  Hypothesis TRF : rw_cells rsegs m (thr + 2840) [C8 (wz rf); C8 (wz rfd)].
  Hypothesis TMU : rw_cells rsegs m (thr + 2888) [C8 (wz mu); C8 (wz md)].
  Hypothesis RFR : 0 <= rf < 2^64.
  Hypothesis RFDR : 0 <= rfd < 2^64.
  Hypothesis MUR : 0 <= mu < 2^64.
  Hypothesis MDR : 0 <= md < 2^64.
  (* [comment removed for export] *)
  Hypothesis DR : depot_repL AL_pboth rsegs D n0 f0 m.
  Hypothesis DND : NoDup (map depot_hashC D).
  Hypothesis DLEN : Z.of_nat (length D) + 1 < 65535.
  Hypothesis DTOT : depot_total D + 3 < kStackStoreBlockFrames.
  Hypothesis DN0 : aobj n0 kDepotNodesBlock /\ n0 + kDepotNodesBlock <= alloc_ceiling.
  Hypothesis DF0 : aobj f0 kStackStoreBlockBytes /\ f0 + kStackStoreBlockBytes <= alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis PALO : aobj pa (8 * nch).
  Hypothesis PAHI : pa + 8 * nch <= alloc_ceiling.
  Hypothesis PAAL : pa mod 8 = 0.
  Hypothesis NRC : 1 <= nch < 2^20.
  Hypothesis U1R : 0 <= u1 < 256.
  Hypothesis U2R : 0 <= u2 < 2^15.
  Hypothesis SRTR : 0 <= srt < 256.
  Hypothesis IDX : 0 <= idx < nch.
  Hypothesis NTH : nth_error hs (Z.to_nat idx) = Some (wz h).
  Hypothesis NTL : nth_error hs (Z.to_nat (nch - 1)) = Some hl.
  Hypothesis HLLO : aobj hla 32.
  Hypothesis HLHI : hla + 32 <= alloc_ceiling.
  Hypothesis HLAL : hla mod 8 = 0.
  Hypothesis NFR : 0 <= nf < 2^64.
  Hypothesis CAR : 0 <= ca < 2^64.
  Hypothesis GAR : 0 <= gA < 2^64.
  Hypothesis GMR : 0 <= gM < 2^64.
  Hypothesis CSR : 0 <= csz < 2^64.
  Hypothesis HLO : aobj h msz.
  Hypothesis HAL : h mod 4096 = 0.
  Hypothesis MSZ : 4096 + 32 <= msz.
  Hypothesis MSZAL : msz mod 4096 = 0.
  Hypothesis HHI : h + msz <= alloc_ceiling.
  Hypothesis HSB : apart h msz sb (2^37).
  Hypothesis PH : p = h + 6144.                 (* [comment removed for export] *)
  Hypothesis PIN : p + 8 * r8 <= h + msz.
  Hypothesis BIG : 0x10000 <= msz / 8.          (* [comment removed for export] *)
  Hypothesis SHR : 0x7fff8200 <= sh h /\ sh h + msz / 8 <= kHighMemBeg.   (* [comment removed for export] *)
  Hypothesis NRST : nearest hs (p + -16) = h.
  Hypothesis SEALR : sealed <> 0 /\ 0 <= sealed < 2^64.
  Hypothesis SEP_hp : apart h msz pa (8 * nch).
  Hypothesis SEP_lp : apart hla 32 pa (8 * nch).
  Hypothesis SEP_ht : apart h msz thr 4096.
  Hypothesis SEP_hc : apart h msz ctx 0x10000.
  Hypothesis SEP_hn : apart h msz n0 kDepotNodesBlock.
  Hypothesis SEP_hf : apart h msz f0 kStackStoreBlockBytes.
  Hypothesis SEP_at : apart pa (8 * nch) thr 4096.
  Hypothesis SEP_ac : apart pa (8 * nch) ctx 0x10000.
  Hypothesis SEP_an : apart pa (8 * nch) n0 kDepotNodesBlock.
  Hypothesis SEP_af : apart pa (8 * nch) f0 kStackStoreBlockBytes.
  Hypothesis SEP_lt : apart hla 32 thr 4096.
  Hypothesis SEP_lc : apart hla 32 ctx 0x10000.
  Hypothesis SEP_ln : apart hla 32 n0 kDepotNodesBlock.
  Hypothesis SEP_lf : apart hla 32 f0 kStackStoreBlockBytes.
  Hypothesis HLA : hla = h \/ apart hla 32 h msz.
  Hypothesis SEP_pc : apart (p + -16) (8 * r8 + 16) ctx 0x10000.
  Hypothesis SEP_pt : apart (p + -16) (8 * r8 + 16) thr 4096.
  Hypothesis SEP_pn : apart (p + -16) (8 * r8 + 16) n0 kDepotNodesBlock.
  Hypothesis SEP_pf : apart (p + -16) (8 * r8 + 16) f0 kStackStoreBlockBytes.
  Hypothesis SEP_n0t : apart n0 kDepotNodesBlock thr 4096.
  Hypothesis SEP_f0t : apart f0 kStackStoreBlockBytes thr 4096.
  Hypothesis SEP_n0c : apart n0 kDepotNodesBlock ctx 0x10000.
  Hypothesis SEP_f0c : apart f0 kStackStoreBlockBytes ctx 0x10000.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  (* [comment removed for export] *)
  Hypothesis CLMA : ro_cells rsegs m LMA_L [C8 (wz 4096); C8 (wz pa)].
  Hypothesis CSEAL : ro_cells rsegs m 0xa8bb0 [C8 (wz sealed)].
  Hypothesis NSRT : rw_cells rsegs m 0xb15d0 [C8 (wz nch); C1 (Z_to_bv 8 srt)].
  Hypothesis NFCA : rw_cells rsegs m 0xb15e8 [C8 (wz nf); C8 (wz ca)].
  Hypothesis LCK : rw_cells rsegs m 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 u1); C2 (wz u2)].
  Hypothesis GAM : rw_cells rsegs m 0xb1818 [C8 (wz gA); C8 (wz gM)].
  Hypothesis ARR : u64arr rsegs m pa hs.
  Hypothesis HDRL : rw_cells rsegs m h [C8 (wz h); C8 (wz msz); C8 (wz csz); C8 (wz idx)].
  Hypothesis HLC : hla = h \/ rw_cells rsegs m hla [C8 hlb; C8 hlm; C8 hls; C8 (wz (nch - 1))].
  Hypothesis A8C : a8_consts m canary.
  Hypothesis SHC : rw_cells rsegs m (sh h) [CB (Z.to_nat (msz / 8)) oldsh].

  Let KEY : list Z := free_key top bot fp ra.
  Let D' : list (list Z) := fst (depot_putC D KEY).
  Let fid : Z := snd (depot_putC D KEY).

  Let PRE := free_prefixB ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo p n b1 tsd ctx thr top bot r8 n0 f0 fr fd D old sb MI ST LO SPA SPH RA0 RANE VLE TOPR BOTR TPE PAL PLO PNB NR NQB R8 B1R B1M
    HDR CTX0 SBR POUT CSB FCo PCo TC TH0 CT8 TSDL TTB TDT TUNW TST FRR FDR DR DND DLEN DTOT DN0 DF0 SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc.
  Let PRE0 := free_prefixB0 ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo p n b1 tsd ctx thr top bot r8 n0 f0 fr fd D old sb MI ST LO SPA SPH RA0 RANE VLE TOPR BOTR TPE PAL PLO PNB NR NQB R8 B1R B1M
    HDR CTX0 SBR POUT CSB FCo PCo TC TH0 CT8 TSDL TTB TDT TUNW TST FRR FDR DR DND DLEN DTOT DN0 DF0 SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition free_directS2_post (m9 : mem) (qb : Z) : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz qb) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(fp + -2128 + -80 - 48, fp + -2128 + -80)] m9 m' /\ wmono rsegs m9 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo fp.

  (* [comment removed for export] *)
End FreeDirect.
