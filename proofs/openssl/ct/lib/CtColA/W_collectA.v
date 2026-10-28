(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX UnwindRecA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit ApErrKitA2 W_get_objectA W_check_tlenA W_err_newA W_err_set_debugA W_err_vsetA I_strcpyA Fr_asn1_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColP Require ColDefs W_check_tlen_gen W_collect.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtP Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA CtlStmtA W_bufmemA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.
Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac unhide H := unfold hidden in H.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Local Ltac thaw H := unfold frozen in H.
Local Ltac xportby H MU WM tac :=
  eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [cells_size csize Nat.add disjoint_from fst snd]; tac].

(* [comment removed for export] *)
Notation collect_S := CtColP.W_collect.collect_S.
Notation collect_O := CtColP.W_collect.collect_O.

(* [comment removed for export] *)
Local Notation E_co_grow := (E_asn1_collect_246410 : uk_call 0x243768 0x2438d8 0x24b32c).      (* [comment removed for export] *)
Local Notation E_co_new1133 := (E_asn1_collect_2464a8 : uk_call 0x243768 0x243964 0x1fd52c).   (* [comment removed for export] *)
Local Notation E_co_dbg1133 := (E_asn1_collect_2464c0 : uk_call 0x243768 0x24397c 0x1fd844).
Local Notation E_co_new1116 := (E_asn1_collect_246518 : uk_call 0x243768 0x24398c 0x1fd52c).   (* [comment removed for export] *)
Local Notation E_co_dbg1116 := (E_asn1_collect_246530 : uk_call 0x243768 0x2439a4 0x1fd844).
Local Notation E_co_new1123 := (E_asn1_collect_246544 : uk_call 0x243768 0x2439b8 0x1fd52c).   (* [comment removed for export] *)
Local Notation E_co_dbg1123 := (E_asn1_collect_24655c : uk_call 0x243768 0x2439d0 0x1fd844).
Local Notation E_co_new1107 := (E_asn1_collect_2464d8 : uk_call 0x243768 0x243a40 0x1fd52c).   (* [comment removed for export] *)
Local Notation E_co_dbg1107 := (E_asn1_collect_2464f0 : uk_call 0x243768 0x243a58 0x1fd844).
Local Notation E_co_err := (E_asn1_collect_246594 : uk_call 0x243768 0x243a68 0x1fdab8).       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CO_RESERVE : Z := CHECK_TLEN_GEN_COST_A + GETOBJ_ERR_COST_A.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges} {UR : UnwindRec ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Proofs.
  Hypothesis STRCPY : strcpy_icontract RT.
  Hypothesis HCTL : forall AR' : ARun, strcpy_icontract (@ar_RT AR') -> @check_tlen_gen_specA AR' UK.
  Local Notation ECT := (E_asn1_collect_2463a4 : uk_call 0x243768 0x243880 0x2426a8).           (* [comment removed for export] *)

  Section Act.
  (* [comment removed for export] *)
  Variables (sp : word) (m : mem) (Σ : rts RT) (LB : list block) (E : ap_env) (lo : Z) (K : list block).
  Variables (c : list Z) (D : Z) (XP : list (Z * Z)) (CST FRM : Z).
  Variables (BUF : Z).
  Hypothesis KH0 : kit_hyps sp LB lo c D XP 0 0.
  Hypothesis D1 : 0 < D.
  Hypothesis D63 : D + zlength c < 2 ^ 63.
  Hypothesis D26 : zlength c < 2 ^ 26.
  Hypothesis XBUF : In (BUF, BUF + 32) XP.
  Hypothesis ALB : BUF mod 8 = 0.
  Hypothesis FRMG : CHECK_TLEN_FRAMES_A <= FRM.

  Local Notation oinvK OFS STK := (oinv sp m Σ LB E lo K c D XP OFS STK CST FRM).
  (* [comment removed for export] *)
  Local Ltac kit L KHx := lazymatch type of KHx with kit_hyps _ _ _ _ _ _ ?OFSx ?STKx => eapply (L AR sp m Σ LB E lo K c D XP OFSx STKx CST FRM KHx) end.
  Local Ltac kitp L KHx H := lazymatch type of KHx with kit_hyps _ _ _ _ _ _ ?OFSx ?STKx => pose proof (L AR sp m Σ LB E lo K c D XP OFSx STKx CST FRM KHx) as H end.
  (* [comment removed for export] *)
  Local Ltac kitc KHx := lazymatch type of KHx with kit_hyps _ _ _ _ _ _ ?OFSx ?STKx => eapply (@oinv_ap_callA AR UK sp m Σ LB E lo K c D XP OFSx STKx CST FRM KHx) end.

  (* [comment removed for export] *)
  Lemma KHof : forall OFS STK, lo <= bv_unsigned sp + OFS - STK -> 0 <= STK -> OFS <= 0 -> OFS mod 16 = 0 -> kit_hyps sp LB lo c D XP OFS STK.
  Proof.
    intros OFS STK LO STK0 OFS0 OFS16. destruct KH0 as (DF & CEIL & LO0 & _ & _ & _ & TOP & SP16 & _ & XPok & XPD & PBX & D0).
    unfold kit_hyps. repeat (split; [assumption|]). exact D0.
  Qed.

  (* [comment removed for export] *)
  Definition MB : Z := (zlength c + 4) / 3 * 4.
  (* [comment removed for export] *)
  Definition co_credit (len cap : Z) : Z := len + 10 * (MB - cap) + CO_RESERVE.

  (* [comment removed for export] *)
  Definition buf_invA (mX : mem) (b : bufm bptr) (A : Z) : Prop :=
    0 <= bm_len b /\ bm_len b = zlength (bm_bytes b) /\ Forall (fun x => 0 <= x < 256) (bm_bytes b) /\ bm_max b <= MB /\
    match bm_data b with
    | None => A = 0 /\ bm_len b = 0
    | Some (q, n) => bm_len b <= n /\ 4 <= n < 2 ^ 31 /\
                     exists rest, rw_cells ctasegs mX A [CB (Z.to_nat (bm_len b)) (to_bytes (bm_bytes b)); CB (Z.to_nat (n - bm_len b)) rest]
    end.

  (* [comment removed for export] *)
  Definition coll_postA (OFS STK : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mX : mem) (NEW1 : list block)
      (PP p len cap CX : Z) (r : (bufm bptr * option Z) * ap_st bptr) (ΣY : rts RT) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY boY (A' CX' : Z),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz TP_A) t0 t1 t2 s0 s1 (wz match snd (fst r) with Some _ => 1 | None => 0 end) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None mY (seg_rom ctasegs)
      /\ oinvK OFS STK ΣY (snd r) mY OWY boY (buf_blk (fst (fst r)) A' ++ NEW1) CX'
      /\ rw_cells ctasegs mY BUF (buf_cells (fst (fst r)) A') /\ buf_invA mY (fst (fst r)) A'
      /\ rw_cells ctasegs mY PP [C8 (wz (D + match snd (fst r) with Some p' => p' | None => p end))]
      /\ ax_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_A) mX mY
      /\ cap <= bm_max (fst (fst r))
      /\ match snd (fst r) with
         | Some p' => p <= p' <= p + len /\ bm_len (fst (fst r)) <= p' /\ CX - ((p' - p) + 10 * (bm_max (fst (fst r)) - cap)) <= CX'
         | None => True
         end.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition entry_okA (fuel : nat) : Prop := forall (j : nat) (X0 : list Z) (OFS STK : Z)
      (ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      ΣX stX mX OWX boX NEW1 (b : bufm bptr) (A0 : Z) (p len : Z) (inf : bool) (iv PP CX : Z) (ras : list Z),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK_A + COLLECT_FRAME_A * (5 - Z.of_nat j) <= STK ->
    oinvK OFS STK ΣX stX mX OWX boX (buf_blk b A0 ++ NEW1) CX -> co_credit len (bm_max b) <= CX ->
    bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp -> PP mod 8 = 0 ->
    rw_cells ctasegs mX BUF (buf_cells b A0) -> buf_invA mX b A0 -> rw_cells ctasegs mX PP [C8 (wz (D + p))] ->
    0 <= p -> 0 <= len -> p + len <= zlength c -> (j <= 5)%nat -> 0 <= iv < 2 ^ 64 -> Z.land iv 1 = (if inf then 1 else 0) -> bm_len b <= p ->
    uw_chain USTACK_TOP mX (bv_unsigned sp + OFS) (bv_unsigned s0) ras -> bv_unsigned ra :: ras = repeat ASN1_COLLECT_REC_RA j ++ X0 -> uk_ctxJ j X0 ->
    implAp (collect fuel c b p len inf (Z.of_nat j) stX) ΣX
           (coll_postA OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW1 PP p len (bm_max b) CX)
           (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz TP_A) t0 t1 t2 s0 s1 (wz BUF) (wz PP) (wz len) (wz iv) (wz (Z.of_nat j)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FX (wz ASN1_COLLECT_A) fcX None mX (seg_rom ctasegs)).

  (* [comment removed for export] *)
  Definition co_savedA (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Local Ltac act_facts OFS STK LO OFS0 OFS16 STKP KH :=
    pose proof (KHof OFS STK LO ltac:(clear - STKP; lia) OFS0 OFS16) as KH;
    let DF := fresh "DF" in let CEIL := fresh "CEIL" in let LO0 := fresh "LO0" in let STK0 := fresh "STK0" in let TOP := fresh "TOP" in
    let SP16 := fresh "SP16" in let XPok := fresh "XPok" in let XPD := fresh "XPD" in let PBX := fresh "PBX" in let D0 := fresh "D0" in
    pose proof KH as (DF & CEIL & LO0 & _ & STK0 & _ & TOP & SP16 & _ & XPok & XPD & PBX & D0);
    pose proof (SPR sp LB lo c D XP OFS STK KH) as SPR; pose proof (ESP sp LB lo c D XP OFS STK KH) as ESP;
    pose proof TOP as TOPN; unfold USTACK_TOP in TOPN.

  (* [comment removed for export] *)
  Local Ltac chain_goal E0 OFS := rewrite ?E0; replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia).

  (* [comment removed for export] *)
  Local Notation ctxJ_call := (@uk_ctxJ_call UK ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6 UR).
  Local Notation ctxJ_rec := (@uk_ctxJ_rec UK ASN1_COLLECT_A ASN1_COLLECT_REC_RA 6 UR).

  (* [comment removed for export] *)
  Local Ltac uw_from FR UW AXA :=
    lazymatch type of FR with
    | rw_cells _ ?mA ?a ?cs =>
        let pre := eval cbn [List.removelast app co_savedA] in (List.removelast (List.removelast cs)) in
        lazymatch goal with
        | |- uw_chain _ _ ?f1 ?fp1 _ =>
            eapply (uw_call _ mA f1 fp1 176 pre _ _ _ UW AXA);
              [reflexivity| clear; lia| uchk_open; Z.div_mod_to_equations; lia| unfold USTACK_TOP in *; lia| apply bv_unsigned_in_range
              | rewrite !Z_to_bv_bv_unsigned; replace (fp1 + - (176)) with a by (clear; lia); exact FR]
        end
    end.

  (* [comment removed for export] *)
  Local Ltac heap_facts HEAPX :=
    let Ca := fresh "CEa" in let Cb := fresh "CEb" in let Cc := fresh "CEc" in
    pose proof (AH_ceil _ _ _ _ HEAPX) as (Ca & Cb & Cc);
    pose proof Ca as CN1; pose proof Cb as CN2; pose proof Cc as CN3; unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CN1, CN2, CN3.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition co_siteA (base rad : Z) (nmid : nat) (rs : rsite) (rsn : Z) : Prop :=
    (base = 0x243960 /\ rad = 0x24397c /\ nmid = 3%nat /\ rs = RS_coll_miss_eoc /\ rsn = 137)
    \/ (base = 0x243988 /\ rad = 0x2439a4 /\ nmid = 4%nat /\ rs = RS_coll_nested /\ rsn = ERR_R_NESTED_ASN1_ERROR)
    \/ (base = 0x2439b4 /\ rad = 0x2439d0 /\ nmid = 3%nat /\ rs = RS_coll_nest_str /\ rsn = 197)
    \/ (base = 0x243a3c /\ rad = 0x243a58 /\ nmid = 3%nat /\ rs = RS_coll_unexp_eoc /\ rsn = 159).

  (* [comment removed for export] *)
  Lemma co_site_edges : forall base rad nmid rs rsn, co_siteA base rad nmid rs rsn ->
    uk_call ASN1_COLLECT_A (base + 4) ERR_NEW /\ uk_call ASN1_COLLECT_A rad ERR_SET_DEBUG.
  Proof.
    intros base rad nmid rs rsn [(-> & -> & _)|[(-> & -> & _)|[(-> & -> & _)|(-> & -> & _)]]]; unfold ASN1_COLLECT_A, ERR_NEW, ERR_SET_DEBUG; split.
    - exact E_co_new1133. - exact E_co_dbg1133. - exact E_co_new1116. - exact E_co_dbg1116.
    - exact E_co_new1123. - exact E_co_dbg1123. - exact E_co_new1107. - exact E_co_dbg1107.
  Qed.

  Definition co_raise_postA (OFS STK : Z) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp : word) (mX : mem) (NEW : list block) (CX : Z)
      (r : unit * ap_st bptr) (ΣY : rts RT) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY boY,
      ms' = MS (mkR (Z_to_bv 64 0x243a68) (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F' (Z_to_bv 64 0x243a68) fc' None mY (seg_rom ctasegs)
      /\ oinv sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM ΣY (snd r) mY OWY boY NEW (CX - GETOBJ_ERR_COST_A)
      /\ ax_pres (NEW ++ LB) (bv_unsigned sp + (OFS + -176)) LIBW_A mX mY.

  Lemma co_raiseA : forall base rad nmid rs rsn (j : nat) (X0 : list Z) (OFS STK : Z)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp : word)
      (FX : bvmap 5 word) (fcX : bv 32) ΣX stX mX OWX boX NEW CX (raA : Z) (ras : list Z),
    co_siteA base rad nmid rs rsn ->
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK_A <= STK ->
    oinv sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM ΣX stX mX OWX boX NEW CX -> GETOBJ_ERR_COST_A <= CX ->
    uw_chain USTACK_TOP mX (bv_unsigned sp + OFS + -176) (bv_unsigned sp + OFS) (raA :: ras) ->
    raA :: ras = repeat ASN1_COLLECT_REC_RA j ++ X0 -> uk_ctxJ j X0 ->
    implAp (err_raise rs stX) ΣX (co_raise_postA OFS STK (Z_to_bv 64 (bv_unsigned sp + OFS)) x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp mX NEW CX)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (wz TP_A) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FX (Z_to_bv 64 base) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until ras. intros SITE LO OFS0 OFS16 STKG OI CXle UWc EQR CTXJ.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7). rewrite KC2 in STKG. pose proof FRMG as FRMG6. rewrite KC4 in FRMG6.
    assert (LO' : lo <= bv_unsigned sp + (OFS + -176) - (STK - 176)) by (clear - LO; lia).
    assert (OFS16' : (OFS + -176) mod 16 = 0) by (clear - OFS16; rewrite Z.add_mod, OFS16 by lia; reflexivity).
    assert (OFS0' : OFS + -176 <= 0) by (clear - OFS0; lia). assert (STKP : 66528 - 176 <= STK - 176) by (clear - STKG; lia).
    act_facts (OFS + -176) (STK - 176) LO' OFS0' OFS16' STKP KH.
    assert (E0 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS)) = bv_unsigned sp + OFS) by (apply unsigned_lit; clear - SPR LO LO0 STKP OFS0; lia).
    kitp @oinv_facts KH OFc. pose proof (OFc _ _ _ _ _ _ _ OI) as (HEAPX & _). clear OFc. heap_facts HEAPX.
    destruct (co_site_edges _ _ _ _ _ SITE) as [Enew Edbg].
    destruct (lit_okA_auto A_TASN_DEC_C_A 23 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_okA_auto A_ASN1_COLLECT_A 13 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    assert (RSF : rs_flen rs = 23) by (destruct SITE as [(_ & _ & _ & -> & _)|[(_ & _ & _ & -> & _)|[(_ & _ & _ & -> & _)|(_ & _ & _ & -> & _)]]]; reflexivity).
    assert (RSN : rs_fnlen rs = 13) by (destruct SITE as [(_ & _ & _ & -> & _)|[(_ & _ & _ & -> & _)|[(_ & _ & _ & -> & _)|(_ & _ & _ & -> & _)]]]; reflexivity).
    assert (RC : rs_code rs = ERR_PACK 13 rsn /\ 0 <= rsn < 8388608)
      by (destruct SITE as [(_ & _ & _ & -> & ->)|[(_ & _ & _ & -> & ->)|[(_ & _ & _ & -> & ->)|(_ & _ & _ & -> & ->)]]]; (split; [reflexivity| unfold ERR_R_NESTED_ASN1_ERROR; clear; lia])).
    destruct RC as [RC RB]. rewrite <- RSF in LF. rewrite <- RSN in LN.
    assert (RADR : 0 <= rad < 2 ^ 64 /\ 0 <= base + 4 < 2 ^ 64 /\ rad <> ASN1_COLLECT_REC_RA /\ base + 4 <> ASN1_COLLECT_REC_RA)
      by (unfold ASN1_COLLECT_REC_RA; destruct SITE as [(-> & -> & _)|[(-> & -> & _)|[(-> & -> & _)|(-> & -> & _)]]]; clear; lia).
    destruct RADR as (RADR & BASR & RADN & BASN).
    unfold err_raise. unfold MallocRep.wz in *.
    (* [comment removed for export] *)
    assert (UWK : forall mA mB (NEWx : list block), ax_pres (NEWx ++ LB) (bv_unsigned sp + (OFS + -176)) LIBW_A mA mB ->
                  uw_chain USTACK_TOP mA (bv_unsigned sp + OFS + -176) (bv_unsigned sp + OFS) (raA :: ras) ->
                  uw_chain USTACK_TOP mB (bv_unsigned sp + OFS + -176) (bv_unsigned sp + OFS) (raA :: ras)).
    { intros mA mB NEWx AX UWx. apply (uw_chain_axpres _ _ _ _ _ _ _ AX) in UWx; [exact UWx| clear; lia| clear - CN1 CEIL LO STK0; alia]. }
    Local Ltac ecu := pose proof col_consts as (_ & _ & KC3' & _); unfold ERR_SET_ERROR_COST, ERR_SET_ERROR_FRAMES, ERR_SET_ERROR_STACK,
                           ERR_VSET_ERROR_COST, ERR_VSET_ERROR_FRAMES, ERR_VSET_ERROR_STACK, ERR_NEW_COST, ERR_NEW_FRAMES, ERR_NEW_STACK,
                           ERR_SET_DEBUG_COST, ERR_SET_DEBUG_FRAMES, ERR_SET_DEBUG_STACK, RT_STACK, CHECK_TLEN_FRAMES_A, GETOBJ_FRAMES_A in *.
    (* [comment removed for export] *)
    assert (TAIL : forall (r1 : unit * ap_st bptr) (ΣA : rts RT) (q5 q6 q7 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (F1 : bvmap 5 word) (fc1 : bv 32) mA OW1 bo1,
      oinv sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM ΣA (snd r1) mA OW1 bo1 NEW (CX - ERR_NEW_COST) ->
      ax_pres (NEW ++ LB) (bv_unsigned sp + (OFS + -176)) LIBW_A mX mA ->
      implAp (abind (err_set_debug rs) (fun _ => err_set_error rs) (snd r1)) ΣA (co_raise_postA OFS STK (Z_to_bv 64 (bv_unsigned sp + OFS)) x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp mX NEW CX)
        (MS (mkR (Z_to_bv 64 rad) (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (Z_to_bv 64 TP_A) q5 q6 q7 (Z_to_bv 64 (bv_unsigned sp + OFS)) x9
                  (Z_to_bv 64 A_TASN_DEC_C_A) (Z_to_bv 64 (rs_line rs)) (Z_to_bv 64 A_ASN1_COLLECT_A) q13 q14 q15 q16 q17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 q28 q29 q30 q31)
            F1 (Z_to_bv 64 ERR_SET_DEBUG) fc1 None mA (seg_rom ctasegs))).
    { intros until bo1. intros OIa AXa.
      eapply implAp_abind.
      { kitc KH;
          [exact (ERR_set_debug_walkA STRCPY rs A_TASN_DEC_C_A A_ASN1_COLLECT_A bo1 _ _ _ _ LF LN)| exact OIa| ecu; clear - STKG; lia| | ecu; clear - FRMG6; lia
          | chain_goal E0 OFS; exact (UWK _ _ _ AXa UWc)| rewrite unsigned_lit by exact RADR; rewrite EQR; exact (ctxJ_call j X0 _ _ Edbg RADN CTXJ)
          | clear; intros HX; discriminate HX| cbv beta; unfold MallocRep.wz; repeat split; reflexivity].
        ecu. clear - CXle KC3'. lia. }
      intros r2 ΣB ms2 PO2. unfold ap_call_postA in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & bo2 & -> & OIb & AXb & EBO2). cbv beta in EBO2. subst bo2.
      assert (SE : forall (q5' q6' q7' q13' q14' q15' q16' q17' q28' q29' q30' q31' : word),
        implAp (err_set_error rs (snd r2)) ΣB (co_raise_postA OFS STK (Z_to_bv 64 (bv_unsigned sp + OFS)) x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp mX NEW CX)
          (MS (mkR (Z_to_bv 64 0x243a68) (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (Z_to_bv 64 TP_A) q5' q6' q7' (Z_to_bv 64 (bv_unsigned sp + OFS)) x9
                    (Z_to_bv 64 13) (Z_to_bv 64 rsn) (Z_to_bv 64 0) q13' q14' q15' q16' q17' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 q28' q29' q30' q31')
              F2 (Z_to_bv 64 ERR_SET_ERROR) fc2 None mB (seg_rom ctasegs))).
      { intros.
        eapply implAp_mono.
        { kitc KH;
            [exact (@ERR_set_error_closedA AR UK BE rs 13 rsn bo1)| exact OIb| ecu; clear - STKG; lia| | ecu; clear - FRMG6; lia
            | chain_goal E0 OFS; exact (UWK _ _ _ (ax_pres_trans _ _ _ _ _ _ AXa AXb) UWc)| rewrite unsigned_lit by (clear; lia); rewrite EQR; exact (ctxJ_call j X0 _ _ E_co_err ltac:(unfold ASN1_COLLECT_REC_RA; clear; lia) CTXJ)
            | clear; intros HX; discriminate HX| cbv beta; unfold ERR_LIB_SYS, MallocRep.wz; repeat split; first [reflexivity| exact RC| (clear - RB; lia)| (clear; lia)]].
          pose proof OIb as (PREb & _). pose proof PREb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRb & _). ecu. clear - CXle CRb KC3'. cbn [ar_RT] in *. lia. }
        intros r3 ΣC ms3 PO3. unfold ap_call_postA in PO3.
        destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & bo3 & -> & OIc & AXc & EBO3). cbv beta in EBO3. subst bo3.
        rewrite (ret_pc_even 0x243a68) by (clear; lia).
        unfold co_raise_postA. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, bo1.
        split; [reflexivity|]. split; [| exact (ax_pres_trans _ _ _ _ _ _ AXa (ax_pres_trans _ _ _ _ _ _ AXb AXc))].
        kit @oinv_credit KH; [exact OIc| ecu; pose proof OIc as (PREc & _); pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRc & _); clear - CXle CRc KC3'; cbn [ar_RT] in *; lia]. }
      kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OIb) as (HEAPb & STb & _ & _ & _ & _ & MIb & _). clear OC.
      pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctasegs mB) as WM.
      apply implAp_from_evt.
      destruct SITE as [(-> & -> & -> & RS & ->)|[(-> & -> & -> & RS & ->)|[(-> & -> & -> & RS & ->)|(-> & -> & -> & RS & ->)]]];
        rewrite ?ret_pc_even by (clear; lia).
      - do 5 step. apply evt_done. apply SE.
      - do 6 step. apply evt_done. apply SE.
      - do 5 step. apply evt_done. apply SE.
      - do 4 step. apply evt_done. apply SE. }
    (* [comment removed for export] *)
    kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STX & _ & _ & _ & _ & MIX & _). clear OC.
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
    assert (HEAD : forall b0, base = b0 ->
      implAp (abind err_new (fun _ : unit => abind (err_set_debug rs) (fun _ : unit => err_set_error rs)) stX) ΣX
        (co_raise_postA OFS STK (Z_to_bv 64 (bv_unsigned sp + OFS)) x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp mX NEW CX)
        (MS (mkR (Z_to_bv 64 (base + 4)) (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (Z_to_bv 64 TP_A) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) x9 x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) FX (Z_to_bv 64 ERR_NEW) fcX None mX (seg_rom ctasegs))).
    { intros b0 Eb.
      eapply implAp_abind.
      { kitc KH;
          [exact (ERR_new_walkA boX)| exact OI| ecu; clear - STKG; lia| | ecu; clear - FRMG6; lia
          | chain_goal E0 OFS; exact UWc| rewrite unsigned_lit by exact BASR; rewrite EQR; exact (ctxJ_call j X0 _ _ Enew BASN CTXJ)
          | clear; intros HX; discriminate HX| reflexivity].
        ecu. clear - CXle KC3'. lia. }
      intros r1 ΣA ms1 PO1. unfold ap_call_postA in PO1.
      destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & bo1 & -> & OIa & AXa & EBO1). cbv beta in EBO1. subst bo1.
      kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OIa) as (HEAPa & STa & _ & _ & _ & _ & MIa & _). clear OC.
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
      apply implAp_from_evt. subst base.
      destruct SITE as [(-> & -> & -> & -> & ->)|[(-> & -> & -> & -> & ->)|[(-> & -> & -> & -> & ->)|(-> & -> & -> & -> & ->)]]];
        rewrite ?ret_pc_even by (clear; lia); do 5 step; step; apply evt_done; (eapply TAIL; [exact OIa| exact AXa]). }
    (* [comment removed for export] *)
    apply implAp_from_evt.
    destruct SITE as [(-> & -> & -> & -> & ->)|[(-> & -> & -> & -> & ->)|[(-> & -> & -> & -> & ->)|(-> & -> & -> & -> & ->)]]];
      step; apply evt_done; (eapply HEAD; reflexivity).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition shw (a : Z) : word := Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 a)) 3 + SHB).
  (* [comment removed for export] *)
  Definition co_headA (wpp w1 w2 w3 : word) (ivm : Z) (j0 j1 : list (bv 8)) (bi bc : bv 8) (jl : list (bv 8)) (pv : Z) : list cell :=
    [CB 8 j0; C8 wpp; C8 (Z_to_bv 64 ivm); C8 w1; C8 w3; C8 w2; CB 6 j1; C1 bi; C1 bc; CB 8 jl; C8 (Z_to_bv 64 pv)].
  (* [comment removed for export] *)
  Definition co_frameA (PP ivm : Z) (j0 j1 : list (bv 8)) (bi bc : bv 8) (jl : list (bv 8)) (pv : Z) : list cell :=
    co_headA (shw PP) (shw (BUF + 8)) (shw BUF) (Z_to_bv 64 (BUF + 8)) ivm j0 j1 bi bc jl pv.

  Lemma co_head_blobA : forall mA F wpp w1 w2 w3 ivm j0 j1 bi bc jl pv tl,
    rw_cells ctasegs mA F (co_headA wpp w1 w2 w3 ivm j0 j1 bi bc jl pv ++ tl) -> exists jhd, rw_cells ctasegs mA F (CB 72 jhd :: tl).
  Proof.
    intros until tl. intros H. apply rw_cells_app in H. destruct H as [H1 H2].
    apply rw_cells_CB_ofA in H1. cbn [cells_size csize Nat.add plus] in H1 |- *. exists (cells_bytes (co_headA wpp w1 w2 w3 ivm j0 j1 bi bc jl pv)).
    change (CB 72 (cells_bytes (co_headA wpp w1 w2 w3 ivm j0 j1 bi bc jl pv)) :: tl) with ([CB 72 (cells_bytes (co_headA wpp w1 w2 w3 ivm j0 j1 bi bc jl pv))] ++ tl).
    apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact H1| exact H2].
  Qed.
  (* [comment removed for export] *)
  Lemma junk24_words : forall mA F (j : list (bv 8)) tl,
    rw_cells ctasegs mA F (CB 24 j :: tl) ->
    rw_cells ctasegs mA F (C8 (le_bytes_to_word (firstn 8 j)) :: C8 (le_bytes_to_word (firstn 8 (skipn 8 j))) :: C8 (le_bytes_to_word (skipn 16 j)) :: tl).
  Proof.
    intros mA F j tl H. pose proof H as [[W _] _]. cbn in W. destruct W as [L Wt].
    eapply rw_cells_recast; [exact H| cbn; repeat split; exact Wt| | reflexivity].
    cbn [cells_bytes cbytes app]. unfold le8, word_to_le_bytes, le_bytes_to_word.
    assert (E8 : forall bs : list (bv 8), length bs = 8%nat -> Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs))) = bs).
    { intros bs HL. pose proof (CtP.Printf_lib.bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in HR.
      rewrite unsigned_lit by lia. rewrite <- HL. apply CtP.Printf_lib.Z_to_le_bytes_to_Z. }
    rewrite !E8 by (rewrite ?length_firstn, ?length_skipn; lia).
    replace (skipn 16 j) with (skipn 8 (skipn 8 j)) by (rewrite skipn_skipn; reflexivity).
    rewrite (app_assoc (firstn 8 (skipn 8 j))), (firstn_skipn 8 (skipn 8 j)). rewrite (app_assoc (firstn 8 j)), (firstn_skipn 8 j). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma co_ret0A : forall (OFS STK : Z) (pc0 : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      ΣA stA mX mA OWA boA NEW1 (b : bufm bptr) (A PP p len cap CX0 CXA : Z) (jhd : list (bv 8)),
    (pc0 = 0x243a68 \/ (pc0 = 0x243a6c /\ x10 = wz 0)) ->
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK_A <= STK ->
    oinv sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM ΣA stA mA OWA boA (buf_blk b A ++ NEW1) CXA ->
    bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp ->
    rw_cells ctasegs mA BUF (buf_cells b A) -> buf_invA mA b A -> rw_cells ctasegs mA PP [C8 (wz (D + p))] ->
    agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mA ->
    rw_cells ctasegs mA (bv_unsigned sp + OFS + -176) (CB 72 jhd :: co_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    cap <= bm_max b ->
    evt ctasegs (coll_postA OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW1 PP p len cap CX0 (b, None, stA) ΣA)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (wz TP_A) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FA (Z_to_bv 64 pc0) fcA None mA (seg_rom ctasegs)).
  Proof.
    intros until jhd. intros PC LO OFS0 OFS16 STKG OI PPlo PPhi HBUF BI HPP AXG FR CAP.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7). rewrite KC2 in STKG.
    assert (LO' : lo <= bv_unsigned sp + (OFS + -176) - (STK - 176)) by (clear - LO; lia).
    assert (OFS16' : (OFS + -176) mod 16 = 0) by (clear - OFS16; rewrite Z.add_mod, OFS16 by lia; reflexivity).
    assert (OFS0' : OFS + -176 <= 0) by (clear - OFS0; lia). assert (STKP : 66528 - 176 <= STK - 176) by (clear - STKG; lia).
    act_facts (OFS + -176) (STK - 176) LO' OFS0' OFS16' STKP KH.
    kitp @oinv_facts KH OFc. pose proof (OFc _ _ _ _ _ _ _ OI) as (HEAPA & _ & BND & _). clear OFc. heap_facts HEAPA.
    kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STA & _ & _ & _ & _ & MIA & _). clear OC.
    replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in STA by (clear; lia).
    unfold co_savedA in FR. unfold MallocRep.wz in *.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
    assert (FIN : forall mA', mA' = mA ->
      evt ctasegs (coll_postA OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW1 PP p len cap CX0 (b, None, stA) ΣA)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (Z_to_bv 64 TP_A) x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            FA (Z_to_bv 64 0x243a6c) fcA None mA' (seg_rom ctasegs))).
    { intros mA' ->.
      replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) by (clear; lia).
      do 13 step. release_frame FR STA (bv_unsigned sp + OFS). step. step.
      match goal with H : stk ctasegs mA lo (bv_unsigned sp + OFS) |- _ => rename H into ST3 end.
      apply evt_done. unfold coll_postA. cbn [fst snd].
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FA, fcA, mA, OWA, boA, A, CXA.
      split; [reflexivity|].
      split. { eapply (oinv_reframe sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM OFS STK); [exact OI| exact TOP| exact SP16| exact ST3| clear - LO; lia| exact OFS0| clear - STKP; lia| exact OFS16]. }
      split; [exact HBUF|]. split; [exact BI|]. split; [exact HPP|]. split; [| split; [exact CAP| exact I]].
      intros a Ha Hc. apply (AXG a Ha).
      destruct Hc as [HX Hc]. split; [| exact Hc]. intros Hr. apply HX. cbn [rin_ivs fst snd app] in Hr |- *. clear - Hr. tauto. }
    destruct PC as [-> | [-> ->]].
    - step. apply FIN. reflexivity.
    - apply FIN. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma co_ret1A : forall (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      ΣA stA mX mA OWA boA NEW1 (b : bufm bptr) (A PP p0 len0 p' cap CX0 CXA ivm : Z) (w1 w2 w3 : word) (j0 j1 jl : list (bv 8)) (bi bc : bv 8),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK_A <= STK ->
    oinv sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM ΣA stA mA OWA boA (buf_blk b A ++ NEW1) CXA ->
    bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp -> PP mod 8 = 0 ->
    rw_cells ctasegs mA BUF (buf_cells b A) -> buf_invA mA b A -> rw_cells ctasegs mA PP [C8 (wz (D + p0))] ->
    agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mA ->
    rw_cells ctasegs mA (bv_unsigned sp + OFS + -176) (co_headA (shw PP) w1 w2 w3 ivm j0 j1 bi bc jl (D + p') ++ co_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    p0 <= p' <= p0 + len0 -> p0 + len0 <= zlength c -> bm_len b <= p' -> cap <= bm_max b -> CX0 - ((p' - p0) + 10 * (bm_max b - cap)) <= CXA ->
    evt ctasegs (coll_postA OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW1 PP p0 len0 cap CX0 (b, Some p', stA) ΣA)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (wz TP_A) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz PP) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FA (Z_to_bv 64 0x243944) fcA None mA (seg_rom ctasegs)).
  Proof.
    intros until bc. intros LO OFS0 OFS16 STKG OI PPlo PPhi ALP HBUF BI HPP AXG FR PB PL BLP CAP CRP.
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7). rewrite KC2 in STKG.
    assert (LO' : lo <= bv_unsigned sp + (OFS + -176) - (STK - 176)) by (clear - LO; lia).
    assert (OFS16' : (OFS + -176) mod 16 = 0) by (clear - OFS16; rewrite Z.add_mod, OFS16 by lia; reflexivity).
    assert (OFS0' : OFS + -176 <= 0) by (clear - OFS0; lia). assert (STKP : 66528 - 176 <= STK - 176) by (clear - STKG; lia).
    act_facts (OFS + -176) (STK - 176) LO' OFS0' OFS16' STKP KH.
    kitp @oinv_facts KH OFc. pose proof (OFc _ _ _ _ _ _ _ OI) as (HEAPA & _ & BND & _). clear OFc. heap_facts HEAPA.
    kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STA & _ & _ & _ & _ & MIA & _). clear OC.
    replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in STA |- * by (clear; lia).
    assert (EPP : bv_unsigned (Z_to_bv 64 PP) = PP) by (apply unsigned_lit; clear - PPlo PPhi LO LO0 STKP SPR OFS0; lia).
    (* [comment removed for export] *)
    assert (ACCS : acc ctasegs mA (bv_unsigned sp + OFS - 176) (176 + - OFS)).
    { destruct HEAPA as (HA & HS & _). apply (af_acc_stack RT AF ΣA mA _ _ HA); [| clear - TOP; unfold USTACK_TOP in *; lia].
      rewrite HS. clear - CEIL LO STKP. unfold BnHeapA.ACEIL, STACK_WIN in *. lia. }
    destruct (AH_shb _ _ _ _ HEAPA) as [SHB1 SHB2].
    unfold co_headA, co_savedA, shw in FR |- *. cbn [app] in FR. unfold MallocRep.wz in *. rewrite ?EPP in FR |- *.
    pose proof (proj1 (Forall_forall _ _) XPok _ XBUF) as (bB & HbB & BB1 & BB2). cbn [fst snd] in BB1, BB2.
    pose proof (BND bB ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbB)) as (BB3 & BB4 & BB5 & BB6).
    pose proof (munch_refl [(PP, PP + 8)]%Z mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
    assert (OFFW : offshW [(PP, PP + 8)]%Z) by (cbn [offshW]; clear - CEIL LO STKP CN2 PPlo OFS0; alia).
    freeze HBUF.
    (* [comment removed for export] *)
    step. step. step. step. step.
    do 13 step. release_frame FR STA (bv_unsigned sp + OFS). step. step.
    name_mem m3.
    match goal with H : stk ctasegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctasegs m3 |- _ => rename H into MI3 end.
    match goal with H : munch _ mA m3 |- _ => rename H into MU3 end. match goal with H : wmono ctasegs mA m3 |- _ => rename H into WM3 end.
    thaw HBUF. xportby HBUF MU3 WM3 ltac:(unfold CtColP.ColDefs.buf_cells; cbn; clear - BB1 BB2 BB5 CEIL LO STKP PPlo OFS0; unfold BnHeapA.ACEIL in *; lia).
    apply evt_done. unfold coll_postA. cbn [fst snd].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FA, fcA, m3, OWA, boA, A, CXA.
    split; [reflexivity|].
    split. { eapply (oinv_reframe sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM OFS STK); [| exact TOP| exact SP16| exact ST3| clear - LO; lia| exact OFS0| clear - STKP; lia| exact OFS16].
             kit @oinv_munch KH; [exact OI| exact MU3| exact WM3| exact MI3| | constructor; [left; cbn [fst snd]; clear - PPlo PPhi OFS0 LO STKP; lia| constructor]].
             destruct (stk_carve ctasegs m3 lo (bv_unsigned sp + OFS) 176 ST3 ltac:(clear - LO STKP; lia)) as [ST4 _].
             replace (bv_unsigned sp + OFS - Z.of_nat 176) with (bv_unsigned sp + (OFS + -176)) in ST4 by (clear; lia). exact ST4. }
    split; [assumption|].
    split. { destruct BI as (BI1 & BI2 & BI3 & BIM & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|]. split; [exact BIM|].
             destruct (bm_data b) as [[q n]|] eqn:EBD; [| exact BI4]. destruct BI4 as (C1' & C2' & rest & HC). split; [exact C1'|]. split; [exact C2'|]. exists rest.
             pose proof (BND (q, A, n) ltac:(apply in_app_iff; right; apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity)) as (_ & _ & BA & _). cbn [blk_addr blk_size fst snd] in BA.
             xportby HC MU3 WM3 ltac:(clear - BA CEIL LO STKP PPlo OFS0 C1' BI1; alia). exact HC. }
    split; [assumption|].
    split. { intros a Ha Hc. destruct Hc as [HX Hc].
             rewrite (agree_on_of_munch_nw _ _ _ MU3 a Ha ltac:(cbn [outside fst snd]; split; [| exact I]; clear - HX; cbn [rin_ivs fst snd app] in HX; lia)).
             apply (AXG a Ha). split; [| exact Hc]. intros Hr. apply HX. cbn [rin_ivs fst snd app] in Hr |- *. clear - Hr. tauto. }
    split; [exact CAP|]. split; [exact PB|]. split; [exact BLP| exact CRP].
  Qed.

  (* [comment removed for export] *)
  Lemma co_exitA : forall (fuel : nat) (j : nat) (X0 : list Z) (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      ΣA stA mX mA OWA boA NEW1 (b : bufm bptr) (A PP p0 len0 p cap CX0 CXA iv : Z) (inf : bool) (w1 w2 w3 : word) (j0 j1 jl : list (bv 8)) (bi bc : bv 8) (ras : list Z),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK_A <= STK ->
    oinv sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM ΣA stA mA OWA boA (buf_blk b A ++ NEW1) CXA -> GETOBJ_ERR_COST_A <= CXA ->
    bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp -> PP mod 8 = 0 ->
    rw_cells ctasegs mA BUF (buf_cells b A) -> buf_invA mA b A -> rw_cells ctasegs mA PP [C8 (wz (D + p0))] ->
    agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mA ->
    rw_cells ctasegs mA (bv_unsigned sp + OFS + -176) (co_headA (shw PP) w1 w2 w3 (Z.land iv 1) j0 j1 bi bc jl (D + p) ++ co_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    0 <= iv < 2 ^ 64 -> Z.land iv 1 = (if inf then 1 else 0) ->
    p0 <= p <= p0 + len0 -> p0 + len0 <= zlength c -> bm_len b <= p -> cap <= bm_max b -> CX0 - ((p - p0) + 10 * (bm_max b - cap)) <= CXA ->
    uw_chain USTACK_TOP mX (bv_unsigned sp + OFS) (bv_unsigned s0) ras -> bv_unsigned ra :: ras = repeat ASN1_COLLECT_REC_RA j ++ X0 -> uk_ctxJ j X0 ->
    agree_on (fun a => bv_unsigned sp + OFS <= a < USTACK_TOP) mX mA ->
    implAp (collect fuel c b p 0 inf (Z.of_nat j) stA) ΣA
           (coll_postA OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW1 PP p0 len0 cap CX0)
           (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (wz TP_A) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz PP) x10 x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               FA (Z_to_bv 64 0x24393c) fcA None mA (seg_rom ctasegs)).
  Proof.
    intros until ras. intros LO OFS0 OFS16 STKG OI CXG PPlo PPhi ALP HBUF BI HPP AXG FR IV IV1 PB PL BLP CAP CRP UW EQR CTXJ AXA.
    destruct fuel as [|f]; [rewrite collect_O; apply implAp_unr|].
    rewrite collect_S. cbn [Z.leb].
    pose proof col_consts as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6 & KC7). pose proof STKG as STKG0. rewrite KC2 in STKG.
    assert (LO' : lo <= bv_unsigned sp + (OFS + -176) - (STK - 176)) by (clear - LO; lia).
    assert (OFS16' : (OFS + -176) mod 16 = 0) by (clear - OFS16; rewrite Z.add_mod, OFS16 by lia; reflexivity).
    assert (OFS0' : OFS + -176 <= 0) by (clear - OFS0; lia). assert (STKP : 66528 - 176 <= STK - 176) by (clear - STKG; lia).
    act_facts (OFS + -176) (STK - 176) LO' OFS0' OFS16' STKP KH.
    kitp @oinv_facts KH OFc. pose proof (OFc _ _ _ _ _ _ _ OI) as (HEAPA & _ & BND & _). clear OFc. heap_facts HEAPA.
    kitp @oinv_call KH OC. pose proof (OC _ _ _ _ _ _ _ OI) as (_ & STA & _ & _ & _ & _ & MIA & _). clear OC.
    replace (bv_unsigned sp + (OFS + -176)) with (bv_unsigned sp + OFS + -176) in STA by (clear; lia).
    pose proof FR as FR0. unfold co_headA, co_savedA, shw in FR. cbn [app] in FR. unfold MallocRep.wz in *.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
    apply implAp_from_evt.
    step. step. if_cases KI; zc KI.
    - (* [comment removed for export] *)
      destruct inf; [| exfalso; apply KI; rewrite IV1; reflexivity].
      apply evt_done.
      eapply implAp_abind.
      { replace (Z_to_bv 64 (bv_unsigned sp + OFS + -176)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) by (f_equal; clear; lia).
        eapply (co_raiseA 0x243960 0x24397c 3%nat RS_coll_miss_eoc 137 j X0 OFS STK); [left; repeat split; reflexivity| exact LO| exact OFS0| exact OFS16| exact STKG0| exact OI| exact CXG| | exact EQR| exact CTXJ].
        uw_from FR UW AXA. }
      intros r1 Σ1 ms1 PO1. unfold co_raise_postA in PO1.
      destruct PO1 as (q0 & q1 & q2 & p0' & p1' & p2' & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mR & OWR & boR & -> & OIR & AXR).
      cbn [fst snd] in OIR.
      (* [comment removed for export] *)
      assert (CL : forall a, (bv_unsigned sp + OFS - 176 <= a < bv_unsigned sp + OFS \/ BUF <= a < BUF + 32 \/ PP <= a < PP + 8) ->
                    ax_client ((buf_blk b A ++ NEW1) ++ LB) (bv_unsigned sp + (OFS + -176)) LIBW_A a).
      { intros a Ha. split; [intros Hr; pose proof (libw_rangeA a Hr) as Hb|].
        - pose proof (proj1 (Forall_forall _ _) XPok _ XBUF) as (bB & HbB & BB1 & BB2). cbn [fst snd] in BB1, BB2.
          pose proof (BND bB ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbB)) as (BB3 & _ & BB5 & BB6). clear - Ha Hb BB1 BB2 BB3 BB5 BB6 CEIL LO STKP PPlo OFS0 CN1. lia.
        - destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha TOP OFS0; unfold USTACK_TOP in *; lia| | left; clear - Ha PPlo PPhi TOP OFS0; unfold USTACK_TOP in *; lia].
          pose proof (proj1 (Forall_forall _ _) XPok _ XBUF) as (bB & HbB & BB1 & BB2). cbn [fst snd] in BB1, BB2.
          right; right. exists bB. split; [apply in_app_iff; right; exact HbB| clear - Ha BB1 BB2; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AXR) in FR0; [| intros a Ha; apply CL; unfold co_headA, co_savedA in Ha; cbn in Ha; clear - Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AXR) in HBUF; [| intros a Ha; apply CL; unfold CtColP.ColDefs.buf_cells in Ha; cbn in Ha; clear - Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AXR) in HPP; [| intros a Ha; apply CL; cbn in Ha; clear - Ha; lia].
      assert (BIR : buf_invA mR b A).
      { destruct BI as (BI1 & BI2 & BI3 & BIM & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|]. split; [exact BIM|].
        destruct (bm_data b) as [[q n]|] eqn:EBD; [| exact BI4]. destruct BI4 as (C1' & C2' & rest & HC). split; [exact C1'|]. split; [exact C2'|]. exists rest.
        apply (rw_cells_agree _ _ _ _ _ AXR) in HC; [exact HC|]. intros a Ha. cbn in Ha. split; [intros Hr; pose proof (libw_rangeA a Hr) as Hb|].
        - pose proof (BND (q, A, n) ltac:(apply in_app_iff; right; apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity)) as (_ & _ & _ & BA6). cbn [blk_addr blk_size fst snd] in BA6.
          clear - Ha Hb BA6 C1' BI1. lia.
        - right; right. exists (q, A, n). split; [apply in_app_iff; left; unfold CtColP.ColDefs.buf_blk; rewrite EBD; left; reflexivity| cbn; clear - Ha C1' BI1; lia]. }
      destruct (co_head_blobA mR _ _ _ _ _ _ _ _ _ _ _ _ _ FR0) as [jhd FRh].
      apply implAp_from_evt. cbn [fst snd].
      eapply evt_mono; [eapply (co_ret0A OFS STK 0x243a68); [left; reflexivity| exact LO| exact OFS0| exact OFS16| exact STKG0| exact OIR| exact PPlo| exact PPhi| exact HBUF| exact BIR| exact HPP| | exact FRh| exact CAP]
                       | intros ms Hms; apply implAp_aret; exact Hms].
      eapply agree_on_trans; [exact AXG|]. eapply agree_on_mono; [exact AXR|]. intros a [HX Ha]. split; [intros Hr; apply HX; cbn [rin_ivs fst snd app] in Hr |- *; clear - Hr; tauto|].
      destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha OFS0; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
      apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; apply in_app_iff; right; exact Hb'| right; exact Hb'].
    - (* [comment removed for export] *)
      destruct inf; [exfalso; revert KI; rewrite IV1; rewrite ?unsigned_lit by (clear; lia); clear; lia|].
      eapply evt_mono; [eapply (co_ret1A OFS STK) with (p0 := p0) (len0 := len0) (cap := cap) (CX0 := CX0);
        [exact LO| exact OFS0| exact OFS16| exact STKG0| exact OI| exact PPlo| exact PPhi| exact ALP| exact HBUF| exact BI| exact HPP| exact AXG| exact FR0
        | exact PB| exact PL| exact BLP| exact CAP| clear - CRP; lia] |].
      intros ms Hms. apply implAp_aret. exact Hms.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition loop_okA (fuel : nat) : Prop := forall (j : nat) (X0 : list Z) (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word)
      ΣA stA mX mA OWA boA NEW1 (b : bufm bptr) (A PP p0 len0 p len cap CX0 CXA iv : Z) (inf : bool) (j0 j1 jl : list (bv 8)) (bi bc : bv 8) (ras : list Z),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK_A + COLLECT_FRAME_A * (5 - Z.of_nat j) <= STK ->
    oinv sp m Σ LB E lo K c D XP (OFS + -176) (STK - 176) CST FRM ΣA stA mA OWA boA (buf_blk b A ++ NEW1) CXA ->
    bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp -> PP mod 8 = 0 ->
    rw_cells ctasegs mA BUF (buf_cells b A) -> buf_invA mA b A -> rw_cells ctasegs mA PP [C8 (wz (D + p0))] ->
    agree_on (ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A)) mX mA ->
    rw_cells ctasegs mA (bv_unsigned sp + OFS + -176) (co_frameA PP (Z.land iv 1) j0 j1 bi bc jl (D + p) ++ co_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    0 <= iv < 2 ^ 64 -> Z.land iv 1 = (if inf then 1 else 0) ->
    0 <= p0 -> p0 <= p -> 0 < len -> p + len = p0 + len0 -> p0 + len0 <= zlength c -> (j <= 5)%nat -> bm_len b <= p ->
    cap <= bm_max b -> CX0 - ((p - p0) + 10 * (bm_max b - cap)) <= CXA -> co_credit len0 cap <= CX0 ->
    uw_chain USTACK_TOP mX (bv_unsigned sp + OFS) (bv_unsigned s0) ras -> bv_unsigned ra :: ras = repeat ASN1_COLLECT_REC_RA j ++ X0 -> uk_ctxJ j X0 ->
    x22 = Z_to_bv 64 (Z.of_nat j + 1) ->
    implAp (collect fuel c b p len inf (Z.of_nat j) stA) ΣA
           (coll_postA OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mX NEW1 PP p0 len0 cap CX0)
           (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + (OFS + -176))) gp (wz TP_A) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz PP) x10 x11 x12 x13 x14 x15 x16 x17
                    (wz (Z.of_nat j)) (wz len) (wz BUF) (wz 5) x22 x23 x24 x25 (wz 1) (wz SHB) x28 x29 x30 x31)
               FA (Z_to_bv 64 0x243814) fcA None mA (seg_rom ctasegs)).

  Lemma loop_okA_O : loop_okA O.
  Proof. unfold loop_okA. intros. rewrite collect_O. apply implAp_unr. Qed.

  End Act.
End Proofs.
End WithRT.
