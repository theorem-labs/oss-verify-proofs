(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA W_cryptoA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA W_check_tlenA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColP Require W_check_tlen_gen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Notation tlen_tree := CtColP.W_check_tlen_gen.tlen_tree.
Notation tlen_plen := CtColP.W_check_tlen_gen.tlen_plen.
Notation tlc_in := CtRepP.W_check_tlen.tlc_in.

(* [comment removed for export] *)
Definition CHECK_TLEN_GEN_COST_A : Z := 1 + 2 * GETOBJ_ERR_COST_A.
Definition ctl_costA (g : go_res) (ot : option Z) : Z :=
  1 + match go_err g with
      | Some _ => go_costA g + GETOBJ_ERR_COST_A
      | None => match ot with
                | Some t => if negb (go_tag g =? t) || negb (go_cls g =? 0) then GETOBJ_ERR_COST_A else 0
                | None => 0
                end
      end.

(* [comment removed for export] *)
Lemma col_consts : CHECK_TLEN_STACK_A = 66352 /\ COLLECT_STACK_A = 66528 /\ GETOBJ_ERR_COST_A = 13 /\ CHECK_TLEN_FRAMES_A = 6
                   /\ GROW_STACK_A = 65744 /\ CHECK_TLEN_GEN_COST_A = 27 /\ COLLECT_FRAME_A = 176.
Proof. repeat split; vm_compute; reflexivity. Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).

Section Act.
  Variables (sp : word) (m : mem) (Σ : rts RT) (LB : list block) (E : ap_env) (lo : Z) (K : list block).
  Variables (c : list Z) (D : Z) (XP : list (Z * Z)) (OFS STK CST FRM : Z).
  Local Notation oinvK := (oinv sp m Σ LB E lo K c D XP OFS STK CST FRM).

  (* [comment removed for export] *)
  Definition tlen_postA (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mX : mem) (NEW : list block)
      (PIC PPC : Z) (TLCo : option Z) (rv : Z) (cells_pic : list cell) (pp : Z) (CX' : Z)
      (st' : ap_st bptr) (ΣY : rts RT) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY boY,
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz TP_A) t0 t1 t2 s0 s1 (wz rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None mY (seg_rom ctasegs)
      /\ oinvK ΣY st' mY OWY boY NEW CX'
      /\ ax_pres (NEW ++ LB) (bv_unsigned sp + OFS)
                 ([(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)] ++ LIBW_A) mX mY
      /\ rw_cells ctasegs mY PIC cells_pic /\ rw_cells ctasegs mY PPC [C8 (wz pp)]
      /\ match TLCo with Some a => exists vb j, rw_cells ctasegs mY a [C1 vb; CB 31 j] | None => True end.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition check_tlen_gen_actA : Prop :=
    forall (X : Type) (ot : option Z) (KE KW KS : @AM bptr X) (Q : X * ap_st bptr -> rts RT -> machine_state -> Prop)
      (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      ΣX stX mX OWX boX NEW (CX : Z) (ras : list Z) (op len PIC PPC : Z) (TLCo : option Z) (bi bc : bv 8) (jl j31 : list (bv 8)),
    let g := get_object c op len in
    CHECK_TLEN_STACK_A <= STK -> CHECK_TLEN_FRAMES_A <= FRM ->
    oinvK ΣX stX mX OWX boX NEW CX -> CHECK_TLEN_GEN_COST_A <= CX ->
    uw_chain USTACK_TOP mX (bv_unsigned sp + OFS) (bv_unsigned s0) ras -> uk_ctx CHECK_TLEN_A (bv_unsigned ra :: ras) -> ras <> nil ->
    0 <= op -> 0 < len -> op + len <= zlength c ->
    match ot with Some t => 0 <= t < 2 ^ 31 | None => True end ->
    (* [comment removed for export] *)
    bv_unsigned sp + OFS <= PIC -> PIC + 10 <= bv_unsigned sp -> bv_unsigned sp + OFS <= PPC -> PPC + 8 <= bv_unsigned sp ->
    (PPC + 8 <= PIC \/ PIC + 10 <= PPC) -> (PIC + 2) mod 8 = 0 -> PPC mod 8 = 0 ->
    match TLCo with Some a => In (a, a + 32) XP /\ a mod 8 = 0 /\ rw_cells ctasegs mX a (tlc_in j31) | None => True end ->
    rw_cells ctasegs mX PIC [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctasegs mX PPC [C8 (wz (D + op))] ->
    (* [comment removed for export] *)
    (forall e st' Σ' ms' bi' bc' jl' CX',
       go_err g = Some e -> CX - ctl_costA g ot <= CX' ->
       tlen_postA ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW PIC PPC TLCo 0 [C1 bi'; C1 bc'; CB 8 jl'] (D + op) CX' st' Σ' ms' ->
       implAp (KE st') Σ' Q ms') ->
    (* [comment removed for export] *)
    (forall t st' Σ' ms' bi' bc' jl' CX',
       ot = Some t -> go_err g = None -> (go_tag g <> t \/ go_cls g <> 0) -> CX - ctl_costA g ot <= CX' ->
       tlen_postA ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW PIC PPC TLCo 0 [C1 bi'; C1 bc'; CB 8 jl'] (D + op) CX' st' Σ' ms' ->
       implAp (KW st') Σ' Q ms') ->
    (* [comment removed for export] *)
    (forall st' Σ' ms' CX',
       go_err g = None -> match ot with Some t => go_tag g = t /\ go_cls g = 0 | None => True end -> CX - ctl_costA g ot <= CX' ->
       tlen_postA ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW PIC PPC TLCo 1
                  [C1 (Z_to_bv 8 (Z.land (go_ret g) 1)); C1 (Z_to_bv 8 (Z.land (go_ret g) 32)); C8 (wz (tlen_plen g op len))] (D + go_p g) CX' st' Σ' ms' ->
       implAp (KS st') Σ' Q ms') ->
    implAp (tlen_tree g ot KE KW KS stX) ΣX Q
           (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz TP_A) t0 t1 t2 s0 s1
                    (wz (PIC + 2)) (wz 0) (wz 0) (wz PIC) (wz (PIC + 1)) (wz PPC) (wz len) (wz match ot with Some t => t | None => -1 end)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 0) (wz 0) (wz match TLCo with Some a => a | None => 0 end) t6)
               FX (wz CHECK_TLEN_A) fcX None mX (seg_rom ctasegs)).
End Act.

(* [comment removed for export] *)
Definition check_tlen_gen_specA : Prop :=
  forall (sp : word) (m : mem) (Σ : rts RT) (LB : list block) (E : ap_env) (lo : Z) (K : list block)
         (c : list Z) (D : Z) (XP : list (Z * Z)) (OFS STK CST FRM : Z),
    kit_hyps sp LB lo c D XP OFS STK -> 0 < D -> D + zlength c < 2 ^ 63 -> zlength c < 2 ^ 26 ->
    check_tlen_gen_actA sp m Σ LB E lo K c D XP OFS STK CST FRM.

End WithRT.
