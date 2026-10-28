(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Startup_B.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_c2i_int W_get_object W_get_object_walk W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColU Require Import ColKit ColDefs W_bufmem W_check_tlen_gen W_check_eoc.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac ubchk_strong := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep;
  let C := fresh "Cs" in if_cases C;
  [ exfalso; zify_cond C;
    repeat (first [ rewrite ub_land64_small in C by lia | rewrite ub_lxor_sign63 in C by lia | rewrite unsigned_lit in C by lia ]);
    ub_ltb_cases C
  | clear C ].
Local Ltac ub1c :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (ub_kind pc) in
      lazymatch k with
      | 1%Z => zstep
      | 2%Z => first [ (zstep; udecide) | ubchk_strong | uchk ]
      end
  end.
Local Ltac step := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
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


(* [comment removed for export] *)
Lemma collect_S : forall {ptr} f d (b : bufm ptr) p len inf depth,
  collect (S f) d b p len inf depth =
    (if len <=? 0 then
      (if inf then err_raise RS_coll_miss_eoc ;;; aret (b, None) else aret (b, Some p))
    else if (2 <=? len) && (znth d p =? 0) && (znth d (p + 1) =? 0) then
      (if inf then aret (b, Some (p + 2)) else err_raise RS_coll_unexp_eoc ;;; aret (b, None))
    else
      let g := get_object d p len in
      match go_err g with
      | Some e => tlen_fail e ;;; err_raise RS_coll_nested ;;; aret (b, None)
      | None =>
          let p1 := go_p g in
          let ininf := Z.testbit (go_ret g) 0 in
          let cst := negb (Z.land (go_ret g) 32 =? 0) in
          let plen := if ininf then len - (p1 - p) else go_len g in
          if cst then
            if 5 <=? depth then err_raise RS_coll_nest_str ;;; aret (b, None)
            else
              ' (b1, r) <- collect f d b p1 plen ininf (depth + 1) ;;
              match r with
              | None => aret (b1, None)
              | Some p2 => collect f d b1 p2 (len - (p2 - p)) inf depth
              end
          else
            ' (b1, p2) <- (if plen =? 0 then aret (b, p1) else collect_data d b p1 plen) ;;
            collect f d b1 p2 (len - (p2 - p)) inf depth
      end).
Proof. intros. reflexivity. Qed.
Lemma collect_O : forall {ptr} d (b : bufm ptr) p len inf depth, collect O d b p len inf depth = aunr.
Proof. intros. reflexivity. Qed.
Global Opaque collect.

(* [comment removed for export] *)
Definition A_ASN1_COLLECT_S : Z := 0x3147d.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HGO : ASN1_get_object_spec.

  Section Act.
  (* [comment removed for export] *)
  Variables (sp : word) (m : mem) (s : PState) (LB : list block) (E : ap_env) (lo B : Z) (canary : word) (K : list block).
  Variables (d : list Z) (D : Z) (XP : list (Z * Z)).
  Hypothesis DF : Forall (fun b => 0 <= b < 256) d.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis XPok : Forall (fun iv : Z * Z => bv_unsigned sp <= fst iv /\ snd iv <= B) XP.
  Hypothesis PBX : d = [] \/ exists pb PA psz, In (pb, PA, psz) LB /\ PA <= D /\ D + zlength d <= PA + psz.
  Hypothesis D1 : 0 < D.
  Hypothesis D63 : D + zlength d < 2 ^ 63.
  Hypothesis D30 : zlength d < 2 ^ 30.

  Local Notation oinvK OFS STK := (oinv sp m s LB E lo B canary K d D XP OFS STK).

  (* [comment removed for export] *)
  Definition buf_inv (mX : mem) (b : bufm bptr) (A : Z) : Prop :=
    0 <= bm_len b /\ bm_len b = zlength (bm_bytes b) /\ Forall (fun x => 0 <= x < 256) (bm_bytes b) /\
    match bm_data b with
    | None => A = 0 /\ bm_len b = 0
    | Some (q, n) => bm_len b <= n /\ 4 <= n < 2 ^ 31 /\ 0 < A /\ A + n <= alloc_ceiling /\ (A + n <= 65536 \/ 3493888 <= A) /\
                     exists rest, rw_cells ctusegs mX A [CB (Z.to_nat (bm_len b)) (to_bytes (bm_bytes b)); CB (Z.to_nat (n - bm_len b)) rest]
    end.

  (* [comment removed for export] *)
  Definition coll_post (OFS STK : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX : bvmap 5 word) (mX : mem) (NEW1 : list block)
      (BUF PP p len : Z) (r : (bufm bptr * option Z) * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY (errvY : word) boY (A' : Z),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz RATP) t0 t1 t2 s0 s1 (wz match snd (fst r) with Some _ => 1 | None => 0 end) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None mY (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get FX k)
      /\ oinvK OFS STK s' (snd r) mY OWY errvY boY (buf_blk (fst (fst r)) A' ++ NEW1)
      /\ rw_cells ctusegs mY BUF (buf_cells (fst (fst r)) A') /\ buf_inv mY (fst (fst r)) A'
      /\ rw_cells ctusegs mY PP [C8 (wz (D + match snd (fst r) with Some p' => p' | None => p end))]
      /\ lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mY
      /\ match snd (fst r) with Some p' => p <= p' <= p + len /\ bm_len (fst (fst r)) <= p' | None => True end.

  (* [comment removed for export] *)
  Definition entry_ok (fuel : nat) : Prop := forall (OFS STK : Z)
      (ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX NEW1 (b : bufm bptr) (A0 : Z) (p len : Z) (inf : bool) (iv depth BUF PP : Z),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK + 144 * (5 - depth) <= STK ->
    oinvK OFS STK sX stX mX OWX errvX boX (buf_blk b A0 ++ NEW1) -> frm0 fcX ->
    bv_unsigned sp + OFS <= BUF -> BUF + 32 <= bv_unsigned sp -> BUF mod 8 = 0 -> bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp -> PP mod 8 = 0 -> (BUF + 32 <= PP \/ PP + 8 <= BUF) ->
    rw_cells ctusegs mX BUF (buf_cells b A0) -> buf_inv mX b A0 -> rw_cells ctusegs mX PP [C8 (wz (D + p))] ->
    0 <= p -> 0 <= len -> p + len <= zlength d -> 0 <= depth <= 5 -> 0 <= iv < 2 ^ 64 -> Z.land iv 1 = (if inf then 1 else 0) -> bm_len b <= p ->
    implM ctusegs (interp (ap_embed (collect fuel d b p len inf depth stX))) sX
          (coll_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW1 BUF PP p len)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz RATP) t0 t1 t2 s0 s1 (wz BUF) (wz PP) (wz len) (wz iv) (wz depth) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              FX (wz ASN1_COLLECT) fcX None mX (seg_rom ctusegs)).

  (* [comment removed for export] *)
  Definition co_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition co_site (base rad : Z) (nmid : nat) (rs : rsite) (rsn : Z) : Prop :=
    (base = 0x1131b0 /\ rad = 0x1131cc /\ nmid = 3%nat /\ rs = RS_coll_miss_eoc /\ rsn = 137)
    \/ (base = 0x113208 /\ rad = 0x113224 /\ nmid = 4%nat /\ rs = RS_coll_nested /\ rsn = ERR_R_NESTED_ASN1_ERROR)
    \/ (base = 0x113234 /\ rad = 0x113250 /\ nmid = 3%nat /\ rs = RS_coll_nest_str /\ rsn = 197)
    \/ (base = 0x1131e0 /\ rad = 0x1131fc /\ nmid = 3%nat /\ rs = RS_coll_unexp_eoc /\ rsn = 159).

  Definition co_raise_post (OFS' STK' : Z) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp : word) (FX : bvmap 5 word) (mX : mem) (NEW : list block)
      (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY (errvY : word) boY,
      ms' = MS (mkR (Z_to_bv 64 0x113298) (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F' (Z_to_bv 64 0x113298) fc' None mY (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get FX k)
      /\ oinvK OFS' STK' s' (snd r) mY OWY errvY boY NEW
      /\ lx_pres (NEW ++ LB) (bv_unsigned sp + OFS') LIBW_AP mX mY.

  Lemma co_raise : forall base rad nmid rs rsn (OFS' STK' : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp : word)
      (FX : bvmap 5 word) (fcX : bv 32) sX stX mX OWX errvX boX NEW,
    co_site base rad nmid rs rsn ->
    lo <= bv_unsigned sp + OFS' - STK' -> OFS' <= 0 -> OFS' mod 16 = 0 -> ERR_SET_ERROR_STACK <= STK' ->
    oinvK OFS' STK' sX stX mX OWX errvX boX NEW -> frm0 fcX ->
    implM ctusegs (interp (ap_embed (err_raise rs stX))) sX (co_raise_post OFS' STK' x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp FX mX NEW)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FX (Z_to_bv 64 base) fcX None mX (seg_rom ctusegs)).
  Proof using B63 CEIL GLO HF HM PBX SPB XPok.
    intros until NEW. intros SITE LO OFS0 OFS16 STKG OI FRMX.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (STK0 : 0 <= STK') by (unfold ERR_SET_ERROR_STACK in STKG; lia).
    pose proof (ESP sp lo B OFS' STK' GLO LO STK0 OFS0 SPB B63) as ESP.
    destruct (lit_ok_auto A_TASN_DEC_C 23 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_ok_auto A_ASN1_COLLECT_S 13 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    assert (RSF : rs_flen rs = 23) by (destruct SITE as [(_ & _ & _ & -> & _)|[(_ & _ & _ & -> & _)|[(_ & _ & _ & -> & _)|(_ & _ & _ & -> & _)]]]; reflexivity).
    assert (RSN : rs_fnlen rs = 13) by (destruct SITE as [(_ & _ & _ & -> & _)|[(_ & _ & _ & -> & _)|[(_ & _ & _ & -> & _)|(_ & _ & _ & -> & _)]]]; reflexivity).
    assert (RC : rs_code rs = ERR_PACK 13 rsn /\ 0 <= rsn < 8388608)
      by (destruct SITE as [(_ & _ & _ & -> & ->)|[(_ & _ & _ & -> & ->)|[(_ & _ & _ & -> & ->)|(_ & _ & _ & -> & ->)]]]; (split; [reflexivity| unfold ERR_R_NESTED_ASN1_ERROR; lia])).
    destruct RC as [RC RB].
    rewrite <- RSF in LF. rewrite <- RSN in LN.
    unfold err_raise. pose proof OI as (PREX & LXX & KO & KI & KP & SO & FA & HB).
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    (* [comment removed for export] *)
    assert (TAIL : forall (r1 : unit * ap_st bptr) (sA : PState) (q5 q6 q7 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (F1 : bvmap 5 word) (fc1 : bv 32) mA OW1 (errv1 : word) bo1,
      frm0 fc1 -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get FX k) ->
      oinvK OFS' STK' sA (snd r1) mA OW1 errv1 bo1 NEW -> lx_pres (NEW ++ LB) (bv_unsigned sp + OFS') LIBW_AP mX mA ->
      implM ctusegs (interp (ap_embed (abind (err_set_debug rs) (fun _ => err_set_error rs) (snd r1)))) sA (co_raise_post OFS' STK' x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp FX mX NEW)
        (MS (mkR (Z_to_bv 64 rad) (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (wz RATP) q5 q6 q7 x8 x9 (wz A_TASN_DEC_C) (wz (rs_line rs)) (wz A_ASN1_COLLECT_S) q13 q14 q15 q16 q17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 q28 q29 q30 q31)
            F1 (wz ERR_SET_DEBUG) fc1 None mA (seg_rom ctusegs))).
    { intros until bo1. intros FRM1 FE1 OIa LXa.
      eapply implM_abind.
      { eapply (oinv_ap_call sp m s LB E lo B canary K d D XP OFS' STK' CEIL GLO LO STK0 OFS0 SPB B63 OFS16 XPok PBX);
          [exact (ERR_set_debug_walk HM HF rs A_TASN_DEC_C A_ASN1_COLLECT_S bo1 _ _ _ _ LF LN)| exact OIa| unfold ERR_SET_DEBUG_STACK, ERR_SET_ERROR_STACK in *; lia| exact FRM1| cbv beta; repeat split; reflexivity]. }
      intros r2 sB ms2 PO2. unfold ap_call_post in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                       & -> & FRM2 & FE2 & OIb & LXb & EBO2). cbv beta in EBO2. subst bo2.
      unfold MallocRep.wz.
      assert (SE : forall (q5' q6' q7' q13' q14' q15' q16' q17' q28' q29' q30' q31' : word) mB',
        mB' = mB ->
        implM ctusegs (interp (ap_embed (err_set_error rs (snd r2)))) sB (co_raise_post OFS' STK' x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp FX mX NEW)
          (MS (mkR (Z_to_bv 64 0x113298) (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (Z_to_bv 64 RATP) q5' q6' q7' x8 x9 (Z_to_bv 64 13) (Z_to_bv 64 rsn) (Z_to_bv 64 0) q13' q14' q15' q16' q17'
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 q28' q29' q30' q31')
              F2 (Z_to_bv 64 ERR_SET_ERROR) fc2 None mB' (seg_rom ctusegs))).
      { intros until mB'. intros ->.
        eapply implM_mono.
        { eapply (oinv_ap_call sp m s LB E lo B canary K d D XP OFS' STK' CEIL GLO LO STK0 OFS0 SPB B63 OFS16 XPok PBX);
            [exact (ERR_set_error_walk rs 13 rsn bo1)| exact OIb| lia| exact FRM2|].
          cbv beta. unfold ERR_LIB_SYS, MallocRep.wz. repeat split; first [reflexivity| lia| exact RC]. }
        intros r3 sC ms3 PO3. unfold ap_call_post in PO3.
        destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & errv3 & bo3
                         & -> & FRM3 & FE3 & OIc & LXc & EBO3). cbv beta in EBO3. subst bo3.
        replace (ret_pc (Z_to_bv 64 0x113298)) with (Z_to_bv 64 0x113298) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold co_raise_post. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3, bo1.
        split; [reflexivity|]. split; [exact FRM3|]. split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk); apply (FE1 k Hk)|].
        split; [exact OIc|]. eapply lx_pres_trans; [exact LXa|]. eapply lx_pres_trans; [exact LXb| exact LXc]. }
      pose proof (oinv_call sp m s LB E lo B canary K d D XP OFS' STK' GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIb) as (_ & _ & _ & STb & _ & _ & ERRb & MIb & _).
      unfold LX_ERRNO, RATP in ERRb. change (3355176 - 164) with 3355012 in ERRb.
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctusegs mB) as WM.
      unfold implM. iprefix.
      destruct SITE as [(-> & -> & -> & RS & ->)|[(-> & -> & -> & RS & ->)|[(-> & -> & -> & RS & ->)|(-> & -> & -> & RS & ->)]]];
        (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).
      - do 5 step. ihere. to_implM. apply SE. reflexivity.
      - do 6 step. ihere. to_implM. apply SE. reflexivity.
      - do 5 step. ihere. to_implM. apply SE. reflexivity.
      - do 5 step. ihere. to_implM. apply SE. reflexivity. }
    (* [comment removed for export] *)
    destruct SITE as [(-> & -> & -> & -> & ->)|[(-> & -> & -> & -> & ->)|[(-> & -> & -> & -> & ->)|(-> & -> & -> & -> & ->)]]];
      (unfold implM; iprefix; step; ihere; to_implM;
       eapply implM_abind;
       [ eapply (oinv_ap_call sp m s LB E lo B canary K d D XP OFS' STK' CEIL GLO LO STK0 OFS0 SPB B63 OFS16 XPok PBX);
         [exact (ERR_new_walk HF boX)| exact OI| unfold ERR_NEW_STACK, ERR_SET_ERROR_STACK in *; lia| exact FRMX| reflexivity]
       | intros r1 sA ms1 PO1; unfold ap_call_post in PO1;
         destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1 & bo1
                          & -> & FRM1 & FE1 & OIa & LXa & EBO1); cbv beta in EBO1; subst bo1;
         lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end;
         pose proof (oinv_call sp m s LB E lo B canary K d D XP OFS' STK' GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIa) as (_ & _ & _ & STa & _ & _ & ERRa & MIa & _);
         unfold LX_ERRNO, RATP in ERRa; change (3355176 - 164) with 3355012 in ERRa;
         clear MU WM; pose proof (munch_refl (@nil (Z * Z)) mA) as MU; pose proof (wmono_refl ctusegs mA) as WM;
         unfold implM; iprefix; do 5 step; step; ihere; to_implM;
         eapply (TAIL r1 sA); [exact FRM1| exact FE1| exact OIa| exact LXa] ]).
  Qed.

  (* [comment removed for export] *)
  Lemma co_ret0 : forall (OFS STK : Z) (pc0 : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      sA stA mX mA OWA errvA boA NEW1 (b : bufm bptr) (A BUF PP p len : Z) (jhd : list byte),
    (pc0 = 0x113298 \/ (pc0 = 0x11329c /\ x10 = wz 0)) ->
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK <= STK ->
    oinvK (OFS + -144) (STK - 144) sA stA mA OWA errvA boA (buf_blk b A ++ NEW1) -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get FX k) ->
    bv_unsigned sp + OFS <= BUF -> BUF + 32 <= bv_unsigned sp -> bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp ->
    rw_cells ctusegs mA BUF (buf_cells b A) -> buf_inv mA b A -> rw_cells ctusegs mA PP [C8 (wz (D + p))] ->
    lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mA ->
    rw_cells ctusegs mA (bv_unsigned sp + OFS + -144) (CB 40 jhd :: co_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    evt ctusegs (coll_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW1 BUF PP p len (b, None, stA) sA)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FA (Z_to_bv 64 pc0) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL GLO PBX SP16 SPB XPok.
    intros until jhd. intros PC LO OFS0 OFS16 STKG OI FRMA FEA BUFlo BUFhi PPlo PPhi HBUF BI HPP LXA FR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK - 144) by lia. assert (LO' : lo <= bv_unsigned sp + (OFS + -144) - (STK - 144)) by lia.
    assert (OFS0' : OFS + -144 <= 0) by lia. assert (OFS16' : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STA by lia.
    unfold co_saved in FR. unfold MallocRep.wz in *.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    assert (FIN : forall mA', mA' = mA ->
      evt ctusegs (coll_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW1 BUF PP p len (b, None, stA) sA)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            FA (Z_to_bv 64 0x11329c) fcA None mA' (seg_rom ctusegs))).
    { intros mA' ->.
      do 14 step. release_frame FR STA (bv_unsigned sp + OFS). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
      apply evt_done. unfold coll_post. cbn [fst snd].
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FA, fcA, m3, OWA, errvA, boA, A.
      split; [reflexivity|]. split; [exact FRMA|]. split; [exact FEA|].
      split. { eapply (oinv_reframe sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) OFS STK); [| exact SPB| exact SP16| exact ST3| lia| lia| lia| exact OFS16].
               eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO' STK0 OFS0' SPB B63 SP16 OFS16' XPok PBX); [exact OI| exact MU| exact WM| exact MI3| | exact ERRA| constructor].
               replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia.
               destruct (stk_carve ctusegs m3 lo (bv_unsigned sp + OFS) 144 ST3 ltac:(lia)) as [ST4 _]. replace (bv_unsigned sp + OFS - Z.of_nat 144) with (bv_unsigned sp + OFS + -144) in ST4 by lia. exact ST4. }
      split; [exact HBUF|]. split; [exact BI|]. split; [exact HPP|]. split; [| exact I].
      eapply lx_pres_trans; [exact LXA|]. eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc. exact I. }
    destruct PC as [-> | [-> ->]].
    - step. apply FIN. reflexivity.
    - apply FIN. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma co_ret1 : forall (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      sA stA mX mA OWA errvA boA NEW1 (b : bufm bptr) (A BUF PP p len p' : Z) (jhd : list byte),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK <= STK ->
    oinvK (OFS + -144) (STK - 144) sA stA mA OWA errvA boA (buf_blk b A ++ NEW1) -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get FX k) ->
    bv_unsigned sp + OFS <= BUF -> BUF + 32 <= bv_unsigned sp -> bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp -> (BUF + 32 <= PP \/ PP + 8 <= BUF) ->
    rw_cells ctusegs mA BUF (buf_cells b A) -> buf_inv mA b A -> rw_cells ctusegs mA PP [C8 (wz (D + p))] ->
    lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mA ->
    rw_cells ctusegs mA (bv_unsigned sp + OFS + -144) (CB 40 jhd :: co_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    p <= p' <= p + len -> p + len <= zlength d -> bm_len b <= p' ->
    evt ctusegs (coll_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW1 BUF PP p len (b, Some p', stA) sA)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (wz RATP) x5 x6 x7 x8 (wz PP) (wz (D + p')) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FA (Z_to_bv 64 0x113260) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL GLO PBX SP16 SPB XPok.
    intros until jhd. intros LO OFS0 OFS16 STKG OI FRMA FEA BUFlo BUFhi PPlo PPhi DJ HBUF BI HPP LXA FR PB PL BLP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK - 144) by lia. assert (LO' : lo <= bv_unsigned sp + (OFS + -144) - (STK - 144)) by lia.
    assert (OFS0' : OFS + -144 <= 0) by lia. assert (OFS16' : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OI) as (HEAPA & _ & BND & _).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STA by lia.
    unfold co_saved in FR. unfold MallocRep.wz in *. unfold buf_cells in HBUF.
    assert (BIR : match bm_data b with Some (q, n) => 0 < A /\ A + n <= alloc_ceiling | None => True end).
    { destruct BI as (_ & _ & _ & BI4). destruct (bm_data b) as [[q n]|]; [| exact I]. destruct BI4 as (_ & _ & B1 & B2 & _). split; assumption. }
    pose proof (munch_refl [(PP, PP + 8)]%Z mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    step. step. step.
    do 14 step. release_frame FR STA (bv_unsigned sp + OFS). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
    apply evt_done. unfold coll_post. cbn [fst snd].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FA, fcA, m3, OWA, errvA, boA, A.
    split; [reflexivity|]. split; [exact FRMA|]. split; [exact FEA|].
    split. { eapply (oinv_reframe sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) OFS STK); [| exact SPB| exact SP16| exact ST3| lia| lia| lia| exact OFS16].
             eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO' STK0 OFS0' SPB B63 SP16 OFS16' XPok PBX); [exact OI| exact MU| exact WM| exact MI3| | exact ERRA|].
             - replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia.
               destruct (stk_carve ctusegs m3 lo (bv_unsigned sp + OFS) 144 ST3 ltac:(lia)) as [ST4 _]. replace (bv_unsigned sp + OFS - Z.of_nat 144) with (bv_unsigned sp + OFS + -144) in ST4 by lia. exact ST4.
             - constructor; [left; cbn; lia| constructor]. }
    split; [exact HBUF|].
    split. { destruct BI as (BI1 & BI2 & BI3 & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|].
             destruct (bm_data b) as [[q n]|]; [| exact BI4]. destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
             eapply rw_cells_transport; [exact HC| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. cbn. lia. }
    split; [assumption|]. split; [| split; [exact PB| exact BLP]].
    eapply lx_pres_trans; [exact LXA|].
    eapply (lx_pres_munch_gen sA (OWA ++ buf_blk b A) (NEW1 ++ LB)); [rewrite <- app_assoc; rewrite (app_assoc (buf_blk b A)); exact HEAPA| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
    constructor; [| constructor]. right. left. split; [cbn; lia|]. intros a Ha. cbn in Ha. cbn. right. left. lia.
  Qed.

  (* [comment removed for export] *)
  Definition co_head (j0 : list byte) (ivm : Z) (j1 : list byte) (bi bc : byte) (jl : list byte) (pv : Z) : list cell :=
    [CB 8 j0; C8 (wz ivm); CB 6 j1; C1 bi; C1 bc; CB 8 jl; C8 (wz pv)].

  Lemma co_head_blob : forall mA F j0 ivm j1 bi bc jl pv tl,
    rw_cells ctusegs mA F (CB 8 j0 :: C8 (Z_to_bv 64 ivm) :: CB 6 j1 :: C1 bi :: C1 bc :: CB 8 jl :: C8 (Z_to_bv 64 pv) :: tl) -> exists jhd, rw_cells ctusegs mA F (CB 40 jhd :: tl).
  Proof.
    intros until tl. intros H. change (rw_cells ctusegs mA F (co_head j0 ivm j1 bi bc jl pv ++ tl)) in H. apply rw_cells_app in H. destruct H as [H1 H2].
    apply rw_cells_CB_of in H1. cbn [cells_size csize Nat.add plus] in H1 |- *. exists (cells_bytes (co_head j0 ivm j1 bi bc jl pv)).
    change (CB 40 (cells_bytes (co_head j0 ivm j1 bi bc jl pv)) :: tl) with ([CB 40 (cells_bytes (co_head j0 ivm j1 bi bc jl pv))] ++ tl).
    apply (proj2 (rw_cells_app _ _ _ _)). split; [exact H1| exact H2].
  Qed.

  (* [comment removed for export] *)
  Lemma co_exit : forall (fuel : nat) (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      sA stA mX mA OWA errvA boA NEW1 (b : bufm bptr) (A BUF PP p0 len0 p : Z) (inf : bool) (depth : Z) j0 j1 bi bc jl,
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK <= STK ->
    oinvK (OFS + -144) (STK - 144) sA stA mA OWA errvA boA (buf_blk b A ++ NEW1) -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get FX k) ->
    bv_unsigned sp + OFS <= BUF -> BUF + 32 <= bv_unsigned sp -> bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp -> (BUF + 32 <= PP \/ PP + 8 <= BUF) ->
    rw_cells ctusegs mA BUF (buf_cells b A) -> buf_inv mA b A -> rw_cells ctusegs mA PP [C8 (wz (D + p0))] ->
    lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mA ->
    rw_cells ctusegs mA (bv_unsigned sp + OFS + -144) (co_head j0 (if inf then 1 else 0) j1 bi bc jl (D + p) ++ co_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    0 <= p0 -> p0 <= p <= p0 + len0 -> p0 + len0 <= zlength d -> bm_len b <= p ->
    implM ctusegs (interp (ap_embed (collect fuel d b p 0 inf depth stA))) sA
          (coll_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW1 BUF PP p0 len0)
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz PP) (wz (D + p)) x11 x12 x13 x14 x15 x16 x17
                   x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
              FA (Z_to_bv 64 0x1131a8) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL GLO HF HM PBX SP16 SPB XPok.
    intros until jl. intros LO OFS0 OFS16 STKG OI FRMA FEA BUFlo BUFhi PPlo PPhi DJ HBUF BI HPP LXA FR P0 PB PL BLP.
    destruct fuel as [|f]; [rewrite collect_O; apply implM_aunr|].
    rewrite collect_S. cbn [Z.leb].
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof STKG as STKG0. unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK - 144) by lia. assert (LO' : lo <= bv_unsigned sp + (OFS + -144) - (STK - 144)) by lia.
    assert (OFS0' : OFS + -144 <= 0) by lia. assert (OFS16' : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STA by lia.
    unfold co_head, co_saved in FR. cbn [app] in FR. unfold MallocRep.wz in *.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    unfold implM. iprefix.
    step. destruct inf.
    - (* [comment removed for export] *)
      step. if_cases KI; zc KI; [exfalso; revert KI; rewrite ?unsigned_lit by lia; lia|]. clear KI.
      ihere. to_implM. eapply implM_abind.
      { replace (bv_unsigned sp + OFS + -144) with (bv_unsigned sp + (OFS + -144)) by lia.
        eapply (co_raise 0x1131b0 0x1131cc 3%nat RS_coll_miss_eoc 137 (OFS + -144) (STK - 144)); [left; repeat split; reflexivity| exact LO'| exact OFS0'| exact OFS16'| unfold ERR_SET_ERROR_STACK; lia| exact OI| exact FRMA]. }
      intros r sB msB POB. unfold co_raise_post in POB.
      destruct POB as (q0 & q1 & q2 & p0' & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F2 & fc2 & mB & OW2 & errv2 & bo2 & -> & FRM2 & FE2 & OIb & LXb).
      replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LXb |- * by lia.
      pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OI) as (_ & _ & BND & _).
      pose proof (agree_of_lx_pres _ _ _ _ _ LXb) as AGb.
      assert (CL : forall a, bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp -> lx_client (buf_blk b A ++ NEW1 ++ LB) (bv_unsigned sp + OFS + -144) LIBW_AP a).
      { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
      rewrite <- app_assoc in AGb.
      destruct (co_head_blob _ _ _ _ _ _ _ _ _ _ FR) as [jhd FRB]. clear FR.
      apply (rw_cells_agree _ _ _ _ _ AGb) in FRB; [| intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in HBUF; [| intros a Ha; apply CL; unfold buf_cells in Ha; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in HPP; [| intros a Ha; apply CL; cbn in Ha; lia].
      destruct r as [u stB]. cbn [fst snd] in *. apply implM_aret.
      eapply (co_ret0 OFS STK 0x113298 ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F2 fc2);
        [left; reflexivity| exact LO| exact OFS0| exact OFS16| exact STKG0| exact OIb| exact FRM2| intros k Hk; rewrite (FE2 k Hk); apply (FEA k Hk)
        | exact BUFlo| exact BUFhi| exact PPlo| exact PPhi| exact HBUF| | exact HPP| | exact FRB].
      + destruct BI as (BI1 & BI2 & BI3 & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|].
        destruct (bm_data b) as [[q n]|] eqn:EBD; [| exact BI4]. destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
        apply (rw_cells_agree _ _ _ _ _ AGb) in HC; [exact HC|]. intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; cbn in Ha; lia|].
        right. left. exists (q, A, n). split; [apply in_app_iff; left; unfold buf_blk; rewrite EBD; left; reflexivity| cbn; cbn in Ha; lia].
      + eapply lx_pres_trans; [exact LXA|]. eapply lx_pres_weaken; [exact LXb| lia| intros b0 Hb0; rewrite <- app_assoc; apply in_app_iff; right; exact Hb0| intros a Ha; apply rin_ivs_app; right; exact Ha].
    - (* [comment removed for export] *)
      step. if_cases KI; zc KI; [| exfalso; revert KI; rewrite ?unsigned_lit by lia; lia]. clear KI.
      ihere. to_implM. apply implM_aret.
      destruct (co_head_blob _ _ _ _ _ _ _ _ _ _ FR) as [jhd FRB]. clear FR.
      eapply (co_ret1 OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX FA fcA);
        [exact LO| exact OFS0| exact OFS16| exact STKG0| exact OI| exact FRMA| exact FEA| exact BUFlo| exact BUFhi| exact PPlo| exact PPhi| exact DJ| exact HBUF| exact BI| exact HPP| exact LXA| exact FRB| lia| lia| exact BLP].
  Qed.

  (* [comment removed for export] *)
  Definition loop_ok (fuel : nat) : Prop := forall (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x27 x28 x29 x30 x31 : word)
      sA stA mX mA OWA errvA boA NEW1 (b : bufm bptr) (A BUF PP p0 len0 p len : Z) (inf : bool) (depth : Z) j0 j1 bi bc jl,
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> COLLECT_STACK + 144 * (5 - depth) <= STK ->
    oinvK (OFS + -144) (STK - 144) sA stA mA OWA errvA boA (buf_blk b A ++ NEW1) -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get FX k) ->
    bv_unsigned sp + OFS <= BUF -> BUF + 32 <= bv_unsigned sp -> BUF mod 8 = 0 -> bv_unsigned sp + OFS <= PP -> PP + 8 <= bv_unsigned sp -> PP mod 8 = 0 -> (BUF + 32 <= PP \/ PP + 8 <= BUF) ->
    rw_cells ctusegs mA BUF (buf_cells b A) -> buf_inv mA b A -> rw_cells ctusegs mA PP [C8 (wz (D + p0))] ->
    lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mA ->
    rw_cells ctusegs mA (bv_unsigned sp + OFS + -144) (co_head j0 (if inf then 1 else 0) j1 bi bc jl (D + p) ++ co_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    0 <= p0 -> p0 <= p -> 0 < len -> p + len = p0 + len0 -> p0 + len0 <= zlength d -> 0 <= depth <= 5 -> bm_len b <= p ->
    implM ctusegs (interp (ap_embed (collect fuel d b p len inf depth stA))) sA
          (coll_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW1 BUF PP p0 len0)
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz PP) x10 x11 x12 x13 x14 x15 x16 x17
                   (wz depth) (wz BUF) (wz len) (wz (depth + 1)) x22 x23 (wz 0) (wz (D + p)) (wz 5) x27 x28 x29 x30 x31)
              FA (Z_to_bv 64 0x113080) fcA None mA (seg_rom ctusegs)).

  Lemma loop_ok_O : loop_ok O.
  Proof. unfold loop_ok. intros. rewrite collect_O. apply implM_aunr. Qed.

  Lemma loop_step : forall f, loop_ok f -> entry_ok f -> loop_ok (S f).
  Proof using B63 CEIL D1 D30 D63 DF GLO HF HGO HM PBX SP16 SPB XPok.
    intros f IHL IHE. unfold loop_ok.
    intros until jl. intros LO OFS0 OFS16 STKG OI FRMA FEA BUFlo BUFhi BUFal PPlo PPhi PPal DJ HBUF BI HPP LXA FR P0 PP0 LEN0 PL PLD DEP BLP.
    rewrite collect_S. replace (len <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof STKG as STKG0. unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK - 144) by lia. assert (LO' : lo <= bv_unsigned sp + (OFS + -144) - (STK - 144)) by lia.
    assert (OFS0' : OFS + -144 <= 0) by lia. assert (OFS16' : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    assert (E144 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) = bv_unsigned sp + OFS + -144) by (apply unsigned_lit; lia).
    pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OI) as (HEAPA & NDA & BND & _).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _).
    pose proof OI as (_ & _ & _ & _ & _ & _ & _ & HB).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STA by lia.
    unfold co_head, co_saved in FR. cbn [app] in FR. unfold MallocRep.wz in *.
    assert (BY : forall i, 0 <= i < zlength d -> 0 <= znth d i < 256) by (intros i Hi; apply znth_range; exact DF).
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    (* [comment removed for export] *)
    assert (CONT : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y27 y28 y29 y30 y31 : word) (FB : bvmap 5 word) (fcB : bv 32)
                          sB stB mB OWB errvB boB (b1 : bufm bptr) (A1 p2 : Z) j0' j1' bi' bc' jl',
      oinvK (OFS + -144) (STK - 144) sB stB mB OWB errvB boB (buf_blk b1 A1 ++ NEW1) -> frm0 fcB -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FB k = reg_get FX k) ->
      rw_cells ctusegs mB BUF (buf_cells b1 A1) -> buf_inv mB b1 A1 -> rw_cells ctusegs mB PP [C8 (Z_to_bv 64 (D + p0))] ->
      lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mB ->
      rw_cells ctusegs mB (bv_unsigned sp + OFS + -144)
        [CB 8 j0'; C8 (Z_to_bv 64 (if inf then 1 else 0)); CB 6 j1'; C1 bi'; C1 bc'; CB 8 jl'; C8 (Z_to_bv 64 (D + p2));
         C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      p <= p2 <= p + len -> bm_len b1 <= p2 ->
      implM ctusegs (interp (ap_embed (collect f d b1 p2 (len - (p2 - p)) inf depth stB))) sB
            (coll_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW1 BUF PP p0 len0)
            (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 PP) y10 y11 y12 y13 y14 y15 y16 y17
                     (Z_to_bv 64 depth) (Z_to_bv 64 BUF) (Z_to_bv 64 len) (Z_to_bv 64 (depth + 1)) y22 y23 (Z_to_bv 64 0) (Z_to_bv 64 (D + p)) (Z_to_bv 64 5) y27 y28 y29 y30 y31)
                FB (Z_to_bv 64 0x11317c) fcB None mB (seg_rom ctusegs))).
    { intros until jl'. intros OIB FRMB FEB HBUFB BIB HPPB LXB FRB P2 BLP2.
      pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OIB) as (_ & _ & _ & STB & _ & _ & ERRB & MIB & _).
      unfold LX_ERRNO, RATP in ERRB. change (3355176 - 164) with 3355012 in ERRB.
      replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STB by lia.
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctusegs mB) as WM.
      unfold implM. iprefix.
      step. step. step.
      step. setreg 20%Z (Z_to_bv 64 (len - (p2 - p))) ltac:(rewrite ?unsigned_lit by lia; f_equal; lia).
      step. if_cases KL; zc KL.
      - (* [comment removed for export] *)
        ihere. to_implM.
        eapply (IHL OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX FB fcB) with (p0 := p0) (len0 := len0);
          [exact LO| exact OFS0| exact OFS16| exact STKG0| exact OIB| exact FRMB| exact FEB| exact BUFlo| exact BUFhi| exact BUFal| exact PPlo| exact PPhi| exact PPal| exact DJ
          | exact HBUFB| exact BIB| exact HPPB| exact LXB| exact FRB| lia| lia| exact KL0| lia| lia| lia| exact BLP2].
      - (* [comment removed for export] *)
        step. ihere. to_implM.
        assert (EL : len - (p2 - p) = 0) by (apply andb_false_iff in KL; destruct KL as [KL|KL]; apply Z.ltb_ge in KL; lia). rewrite EL.
        eapply (co_exit f OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX FB fcB) with (p0 := p0) (len0 := len0);
          [exact LO| exact OFS0| exact OFS16| unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIB| exact FRMB| exact FEB| exact BUFlo| exact BUFhi| exact PPlo| exact PPhi| exact DJ
          | exact HBUFB| exact BIB| exact HPPB| exact LXB| exact FRB| lia| lia| lia| exact BLP2]. }
    Local Ltac noop := idtac.
    (* [comment removed for export] *)
    lazymatch goal with |- implM _ (interp (ap_embed ((if _ then _ else ?T) stA))) _ _ _ => set (TL := T) end.
    assert (TLEN : forall (y1 y10 y11 y12 : word) (mq : mem),
      munch [(bv_unsigned sp + OFS + -144 - 16, bv_unsigned sp + OFS + -144); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8)]%Z mA mq ->
      wmono ctusegs mA mq -> mem_inv ctusegs mq -> stk ctusegs mq lo (bv_unsigned sp + OFS + -144) ->
      rw_cells ctusegs mq (bv_unsigned sp + OFS + -112) [C8 (Z_to_bv 64 (D + p))] ->
      evt ctusegs (fun ms' => impl ctusegs (at_node ctusegs) (interp (ap_embed (TL stA)) sA)
                    (epost (fun pq : (bufm bptr * option Z) * ap_st bptr * PState => coll_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW1 BUF PP p0 len0 pq.1 pq.2)) ms')
        (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 PP) y10 y11 y12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 depth) (Z_to_bv 64 BUF) (Z_to_bv 64 len) (Z_to_bv 64 (depth + 1)) x22 x23 (Z_to_bv 64 0) (Z_to_bv 64 (D + p)) (Z_to_bv 64 5) x27 x28 x29 x30 x31)
            FA (Z_to_bv 64 0x113090) fcA None mq (seg_rom ctusegs))).
    { intros y1 y10 y11 y12 mq MUq WMq MIq STq HPq.
      (* [comment removed for export] *)
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
        change (rw_cells ctusegs mA (bv_unsigned sp + OFS + -144) ([c0; c1; c2] ++ [c3; c4; c5] ++ [c6] ++ rest)) in FR end.
      apply rw_cells_app in FR. destruct FR as [FRH FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_app in FR. destruct FR as [FPIC FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_app in FR. destruct FR as [FPPC FRS]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRS.
      replace (bv_unsigned sp + OFS + -144 + 22) with (bv_unsigned sp + OFS + -122) in FPIC by lia.
      replace (bv_unsigned sp + OFS + -144 + 22 + 10) with (bv_unsigned sp + OFS + -112) in FPPC by lia.
      replace (bv_unsigned sp + OFS + -144 + 22 + 10 + 8) with (bv_unsigned sp + OFS + -104) in FRS by lia.
      xport FRH MUq WMq. xport FPIC MUq WMq. xport FRS MUq WMq. clear FPPC. rename HPq into FPPC.
      xport ERRA MUq WMq. xport HBUF MUq WMq. xport HPP MUq WMq.
      assert (BIq : buf_inv mq b A).
      { destruct BI as (BI1 & BI2 & BI3 & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|].
        destruct (bm_data b) as [[q n]|]; [| exact BI4]. destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
        eapply rw_cells_transport; [exact HC| exact MUq| exact WMq|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. cbn. lia. }
      assert (LXq : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mq).
      { eapply lx_pres_trans; [exact LXA|].
        eapply (lx_pres_munch_gen sA (OWA ++ buf_blk b A) (NEW1 ++ LB)); [rewrite <- app_assoc; rewrite (app_assoc (buf_blk b A)); exact HEAPA| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MUq| exact WMq|].
        constructor; [left; cbn; lia| constructor; [left; cbn; lia| constructor]]. }
      assert (OIq : oinvK (OFS + -144) (STK - 144) sA stA mq OWA errvA boA (buf_blk b A ++ NEW1)).
      { eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO' STK0 OFS0' SPB B63 SP16 OFS16' XPok PBX);
          [exact OI| exact MUq| exact WMq| exact MIq| replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia; exact STq| exact ERRA|].
        constructor; [left; cbn; lia| constructor; [left; cbn; lia| constructor]]. }
      clear OI BI LXA STA MIA MU WM HB HEAPA NDA BND MUq WMq.
      pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OIq) as (HEAPA & NDA & BND & _).
      pose proof OIq as (_ & _ & _ & _ & _ & _ & _ & HB).
      rename OIq into OI, BIq into BI, LXq into LXA, STq into STA, MIq into MIA.
      clear mA. rename mq into mA.
      pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
      do 11 step. step.
      setreg 10%Z (Z_to_bv 64 (bv_unsigned sp + OFS + -122 + 2)) ltac:(f_equal; lia). setreg 14%Z (Z_to_bv 64 (bv_unsigned sp + OFS + -122 + 1)) ltac:(f_equal; lia).
      ihere. subst TL. cbv zeta. to_implM.
      replace (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -144))) by (f_equal; lia).
      pose proof (check_tlen_gen HM HF HGO sp m s LB E lo B canary K d D XP DF CEIL GLO SPB B63 SP16 XPok PBX D1 D63 D30 (bufm bptr * option Z)%type None) as W.
      cbv beta iota delta [tlen_tree] in W.
      eapply W with (KW := aunr) (TLCo := None) (PIC := bv_unsigned sp + OFS + -122) (PPC := bv_unsigned sp + OFS + -112) (j31 := []);
        [exact LO'| exact OFS0'| exact OFS16'| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI| exact FRMA| lia| lia| lia| exact I
        | lia| lia| lia| lia| lia| replace (bv_unsigned sp + OFS + -122 + 2) with (bv_unsigned sp + OFS + -120) by lia; apply mod8_frame; [exact SP16| exact OFS16| reflexivity]
        | apply mod8_frame; [exact SP16| exact OFS16| reflexivity]
        | exact I| exact FPIC| exact FPPC| | | ].
      - (* [comment removed for export] *)
        intros e st' s' ms' bi' bc' jl' EG POT. unfold tlen_post in POT.
        destruct POT as (q0 & q1 & q2 & p1' & p2' & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mT & OWT & errvT & boT
                         & -> & FRM1 & FE1 & OIT & LXT & HPICT & HPPCT & _).
        replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LXT |- * by lia.
        replace (ret_pc (Z_to_bv 64 0x1130c0)) with (Z_to_bv 64 0x1130c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_lx_pres _ _ _ _ _ LXT) as AGT.
        assert (CLT : forall a, (bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp + OFS + -122 \/ bv_unsigned sp + OFS + -104 <= a < bv_unsigned sp) ->
                      lx_client (buf_blk b A ++ NEW1 ++ LB) (bv_unsigned sp + OFS + -144)
                        ([(bv_unsigned sp + OFS + -122, bv_unsigned sp + OFS + -122 + 10); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8);
                          (bv_unsigned sp + OFS + -122, bv_unsigned sp + OFS + -122)] ++ LIBW_AP) a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
        rewrite <- app_assoc in AGT.
        apply (rw_cells_agree _ _ _ _ _ AGT) in FRH; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FRS; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HBUF; [| intros a Ha; apply CLT; unfold buf_cells in Ha; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HPP; [| intros a Ha; apply CLT; cbn in Ha; lia].
        assert (BIT : buf_inv mT b A).
        { destruct BI as (BI1 & BI2 & BI3 & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|].
          destruct (bm_data b) as [[q n]|] eqn:EBD; [| exact BI4]. destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
          apply (rw_cells_agree _ _ _ _ _ AGT) in HC; [exact HC|]. intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; cbn in Ha; lia|].
          right. left. exists (q, A, n). split; [apply in_app_iff; left; unfold buf_blk; rewrite EBD; left; reflexivity| cbn; cbn in Ha; lia]. }
        assert (LXAT : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mT).
        { eapply lx_pres_trans; [exact LXA|].
          lazymatch type of LXT with lx_pres ?L0 ?SP0 ?X0 mA mT =>
            assert (LXT' : lx_pres (NEW1 ++ LB) SP0 X0 mA mT) by (eapply lx_pres_weaken; [exact LXT| lia| intros b0 Hb0; rewrite <- app_assoc; apply in_app_iff; right; exact Hb0| intros a Ha; exact Ha]) end.
          eapply (lx_pres_up _ _ _ _ _ _ _ lo); [exact LXT'| lia| | lia|].
          - intros q A' n Hq. pose proof (BND q A' n ltac:(apply in_app_iff; right; rewrite <- app_assoc; apply in_app_iff; right; exact Hq)). lia.
          - intros a Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [right; cbn in Ha; lia| left; apply rin_ivs_app; right; exact Ha]. }
        pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OIT) as (_ & _ & _ & STT & _ & _ & ERRT & MIT & _).
        unfold LX_ERRNO, RATP in ERRT. change (3355176 - 164) with 3355012 in ERRT.
        replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STT by lia.
        clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mT) as MU. pose proof (wmono_refl ctusegs mT) as WM.
        unfold MallocRep.wz. unfold implM. iprefix. step. if_true.
        ihere. to_implM. eapply implM_abind.
        { replace (bv_unsigned sp + OFS + -144) with (bv_unsigned sp + (OFS + -144)) by lia.
          eapply (co_raise 0x113208 0x113224 4%nat RS_coll_nested ERR_R_NESTED_ASN1_ERROR (OFS + -144) (STK - 144));
            [right; left; repeat split; reflexivity| exact LO'| exact OFS0'| exact OFS16'| unfold ERR_SET_ERROR_STACK; lia| exact OIT| exact FRM1]. }
        intros r sB msB POB. unfold co_raise_post in POB.
        destruct POB as (o0 & o1 & o2 & n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & o3 & o4 & o5 & o6 & F2 & fc2 & mB & OW2 & errv2 & bo2 & -> & FRM2 & FE2 & OIb & LXb).
        replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LXb |- * by lia.
        pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OIT) as (_ & _ & BNDT & _).
        pose proof (agree_of_lx_pres _ _ _ _ _ LXb) as AGb.
        assert (CL : forall a, bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp -> lx_client (buf_blk b A ++ NEW1 ++ LB) (bv_unsigned sp + OFS + -144) LIBW_AP a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
        rewrite <- app_assoc in AGb.
        join2 FRH HPICT. join2 FRH HPPCT. join2 FRH FRS.
        destruct (co_head_blob _ _ _ _ _ _ _ _ _ _ FRH) as [jhd FRB]. clear FRH.
        apply (rw_cells_agree _ _ _ _ _ AGb) in FRB; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGb) in HBUF; [| intros a Ha; apply CL; unfold buf_cells in Ha; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGb) in HPP; [| intros a Ha; apply CL; cbn in Ha; lia].
        destruct r as [u stB]. cbn [fst snd] in *. apply implM_aret.
        eapply (co_ret0 OFS STK 0x113298 ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F2 fc2);
          [left; reflexivity| exact LO| exact OFS0| exact OFS16| unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIb| exact FRM2
          | intros k Hk; rewrite (FE2 k Hk), (FE1 k Hk); apply (FEA k Hk)
          | exact BUFlo| exact BUFhi| exact PPlo| exact PPhi| exact HBUF| | exact HPP| | exact FRB].
        + destruct BIT as (BI1 & BI2 & BI3 & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|].
          destruct (bm_data b) as [[q n]|] eqn:EBD; [| exact BI4]. destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
          apply (rw_cells_agree _ _ _ _ _ AGb) in HC; [exact HC|]. intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; cbn in Ha; lia|].
          right. left. exists (q, A, n). split; [apply in_app_iff; left; unfold buf_blk; rewrite EBD; left; reflexivity| cbn; cbn in Ha; lia].
        + eapply lx_pres_trans; [exact LXAT|]. eapply lx_pres_weaken; [exact LXb| lia| intros b0 Hb0; rewrite <- app_assoc; apply in_app_iff; right; exact Hb0| intros a Ha; apply rin_ivs_app; right; exact Ha].
      - (* [comment removed for export] *) intros t st' s' ms' bi' bc' jl' ET. discriminate ET.
      - (* [comment removed for export] *)
        intros st' s' ms' EG _ POT. unfold tlen_post in POT.
        destruct POT as (q0 & q1 & q2 & p1' & p2' & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mT & OWT & errvT & boT
                         & -> & FRM1 & FE1 & OIT & LXT & HPICT & HPPCT & _).
        replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LXT |- * by lia.
        replace (ret_pc (Z_to_bv 64 0x1130c0)) with (Z_to_bv 64 0x1130c0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        set (g := get_object d p len) in *.
        pose proof (get_object_bounds d p len ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros; lia) LEN0) as GB. cbv zeta in GB. fold g in GB. rewrite EG in GB.
        destruct GB as (GB1 & GB2 & GB3).
        pose proof (go_ret_cases d p len) as RC. cbv zeta in RC. fold g in RC.
        assert (RB : 0 <= go_ret g < 64) by (destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER; lia).
        pose proof (ret_bits (go_ret g) RC) as (R1 & R32 & R129 & R128 & R11 & RTB).
        assert (PLB : 0 <= tlen_plen g p len /\ go_p g + tlen_plen g p len <= p + len).
        { unfold tlen_plen. destruct (Z.testbit (go_ret g) 0); lia. }
        pose proof (agree_of_lx_pres _ _ _ _ _ LXT) as AGT.
        assert (CLT : forall a, (bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp + OFS + -122 \/ bv_unsigned sp + OFS + -104 <= a < bv_unsigned sp) ->
                      lx_client (buf_blk b A ++ NEW1 ++ LB) (bv_unsigned sp + OFS + -144)
                        ([(bv_unsigned sp + OFS + -122, bv_unsigned sp + OFS + -122 + 10); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8);
                          (bv_unsigned sp + OFS + -122, bv_unsigned sp + OFS + -122)] ++ LIBW_AP) a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
        rewrite <- app_assoc in AGT.
        apply (rw_cells_agree _ _ _ _ _ AGT) in FRH; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in FRS; [| intros a Ha; apply CLT; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HBUF; [| intros a Ha; apply CLT; unfold buf_cells in Ha; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGT) in HPP; [| intros a Ha; apply CLT; cbn in Ha; lia].
        assert (BIT : buf_inv mT b A).
        { destruct BI as (BI1 & BI2 & BI3 & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|].
          destruct (bm_data b) as [[q n]|] eqn:EBD; [| exact BI4]. destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
          apply (rw_cells_agree _ _ _ _ _ AGT) in HC; [exact HC|]. intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; cbn in Ha; lia|].
          right. left. exists (q, A, n). split; [apply in_app_iff; left; unfold buf_blk; rewrite EBD; left; reflexivity| cbn; cbn in Ha; lia]. }
        clear BI.
        assert (LXAT : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mT).
        { eapply lx_pres_trans; [exact LXA|].
          lazymatch type of LXT with lx_pres ?L0 ?SP0 ?X0 mA mT =>
            assert (LXT' : lx_pres (NEW1 ++ LB) SP0 X0 mA mT) by (eapply lx_pres_weaken; [exact LXT| lia| intros b0 Hb0; rewrite <- app_assoc; apply in_app_iff; right; exact Hb0| intros a Ha; exact Ha]) end.
          eapply (lx_pres_up _ _ _ _ _ _ _ lo); [exact LXT'| lia| | lia|].
          - intros q A' n Hq. pose proof (BND q A' n ltac:(apply in_app_iff; right; rewrite <- app_assoc; apply in_app_iff; right; exact Hq)). lia.
          - intros a Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [right; cbn in Ha; lia| left; apply rin_ivs_app; right; exact Ha]. }
        clear LXT AGT CLT.
        pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OIT) as (_ & _ & _ & STT & _ & _ & ERRT & MIT & _).
        pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OIT) as (HEAPT & NDT & BNDT & FRESHT & DJLT & DJOT).
        pose proof OIT as (_ & _ & _ & _ & _ & _ & _ & HBT).
        unfold LX_ERRNO, RATP in ERRT. change (3355176 - 164) with 3355012 in ERRT.
        replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STT by lia.
        cut_hd HPICT HINF (bv_unsigned sp + OFS + -121). cut_hd HPICT HCST (bv_unsigned sp + OFS + -120). rename HPICT into HPLEN.
        clear MU WM. pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z mT) as MU. pose proof (wmono_refl ctusegs mT) as WM.
        unfold MallocRep.wz. unfold implM. iprefix.
        step. if_cases KA; zc KA; [exfalso; revert KA; rewrite ?unsigned_lit by lia; lia|]. clear KA.
        step. step. destruct (Z.land (go_ret g) 32 =? 0) eqn:EC.
        + (* [comment removed for export] *)
          apply Z.eqb_eq in EC. if_cases KC; zc KC; [| exfalso; apply KC; rewrite EC; reflexivity]. clear KC.
          cbv beta iota delta [negb]. fold (tlen_plen g p len). set (plen := tlen_plen g p len) in *.
          step. destruct (plen =? 0) eqn:EZ.
          * (* [comment removed for export] *)
            apply Z.eqb_eq in EZ. step. if_cases KZ; zc KZ; [| exfalso; apply KZ; rewrite EZ; reflexivity]. clear KZ.
            cbn [abind apbind aret fst snd].
            ihere. to_implM.
            apply rw_cells_CB_of in HPLEN. cbn [cells_size csize Nat.add plus] in HPLEN.
            join2 FRH HINF. join2 FRH HCST. join2 FRH HPLEN. join2 FRH HPPCT. join2 FRH FRS.
            eapply CONT; [exact OIT| exact FRM1| intros k Hk; rewrite (FE1 k Hk); apply (FEA k Hk)| exact HBUF| exact BIT| exact HPP| exact LXAT| exact FRH| lia| lia].
          * (* [comment removed for export] *)
            apply Z.eqb_neq in EZ. step. if_cases KZ; zc KZ; [exfalso; revert KZ; unfold MallocRep.wz; rewrite ?unsigned_lit by lia; lia|]. clear KZ.
            unfold collect_data.
            pose proof BIT as (BL0 & BLEN & BBY & BI4).
            assert (BMX : bm_len b <= bm_max b /\ bm_max b < 2 ^ 31).
            { unfold bm_max. destruct (bm_data b) as [[q n]|]; [destruct BI4 as (C1' & C2 & _); lia| destruct BI4 as [_ ->]; lia]. }
            unfold buf_cells in HBUF.
            step. step. setreg 11%Z (Z_to_bv 64 (bm_len b + plen)) ltac:(unfold MallocRep.wz; rewrite ?unsigned_lit by lia; reflexivity).
            step. if_cases KN; zc KN; [exfalso; revert KN; rewrite ?signed_small, ?unsigned_lit by lia; lia|]. clear KN.
            step. step.
            assert (LX63 : forall x, 0 <= x < 2 ^ 63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808).
            { intros x Hx. change 9223372036854775808 with (2 ^ 63). symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj_0. intros n.
              rewrite Z.land_spec, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 63 n) as [<-|]; [| apply andb_false_r]. rewrite andb_true_r.
              destruct (Z.eq_dec x 0) as [->|NZ]; [reflexivity|]. apply Z.bits_above_log2; [lia|]. apply (Z.log2_lt_pow2 x 63); lia. }
            setreg 27%Z (Z_to_bv 64 0) ltac:(unfold MallocRep.wz; rewrite ?unsigned_lit by lia; rewrite LX63 by lia;
              f_equal; destruct (Z.ltb_spec (plen + 9223372036854775808) 9223372036854775808); [lia| reflexivity]).
            ihere. to_implM.
            set (Q1 := fun (r : (bufm bptr * Z) * ap_st bptr) (sB : PState) (msB : machine_state) =>
              exists (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y27 y28 y29 y30 y31 : word) (FB : bvmap 5 word) (fcB : bv 32) mB OWB (errvB : word) boB (b1 : bufm bptr) (A1 : Z) jl1,
                msB = MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 PP) y10 y11 y12 y13 y14 y15 y16 y17
                               (Z_to_bv 64 depth) (Z_to_bv 64 BUF) (Z_to_bv 64 len) (Z_to_bv 64 (depth + 1)) y22 y23 (Z_to_bv 64 0) (Z_to_bv 64 (D + p)) (Z_to_bv 64 5) y27 y28 y29 y30 y31)
                          FB (Z_to_bv 64 0x11317c) fcB None mB (seg_rom ctusegs)
                /\ r = ((b1, go_p g + plen), st')
                /\ oinvK (OFS + -144) (STK - 144) sB st' mB OWB errvB boB (buf_blk b1 A1 ++ NEW1) /\ frm0 fcB /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get FB k = reg_get FX k)
                /\ rw_cells ctusegs mB BUF (buf_cells b1 A1) /\ buf_inv mB b1 A1 /\ rw_cells ctusegs mB PP [C8 (Z_to_bv 64 (D + p0))]
                /\ lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mB
                /\ rw_cells ctusegs mB (bv_unsigned sp + OFS + -144)
                     [CB 8 j0; C8 (Z_to_bv 64 (if inf then 1 else 0)); CB 6 j1; C1 (Z_to_bv 8 (Z.land (go_ret g) 1)); C1 (Z_to_bv 8 (Z.land (go_ret g) 32)); CB 8 jl1; C8 (Z_to_bv 64 (D + (go_p g + plen)));
                      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                /\ bm_len b1 <= go_p g + plen).
            assert (AFTER : forall (bytes0 : list byte) (r1 : bufm bptr * ap_st bptr) (s1' : PState) (ms1 : machine_state),
              firstn (Z.to_nat (bm_len b)) bytes0 = to_bytes (bm_bytes b) ->
              grow_post sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) (Z_to_bv 64 0x11311c) gp (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 PP)
                        (Z_to_bv 64 depth) (Z_to_bv 64 BUF) (Z_to_bv 64 len) (Z_to_bv 64 (depth + 1)) (Z_to_bv 64 plen) (Z_to_bv 64 (bm_len b)) (Z_to_bv 64 0) (Z_to_bv 64 (D + p)) (Z_to_bv 64 5) (Z_to_bv 64 0)
                        F1 fc1 st' OWT boT mT NEW1 b (bm_len b + plen) BUF bytes0 r1 s1' ms1 ->
              implM ctusegs (interp (ap_embed ((fun b' : bufm bptr => aret ({| bm_len := bm_len b'; bm_data := bm_data b'; bm_bytes := bm_bytes b ++ slice d (go_p g) plen |}, go_p g + plen)) (fst r1) (snd r1)))) s1' Q1 ms1).
            { intros bytes0 r1 s1' ms1 FB0 PO1. unfold grow_post in PO1.
              destruct PO1 as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & mY & errvY & q & A' & n' & rest' & -> & ER1 & EB1 & OI1 & HBUF1 & HBLK1 & LEN1 & N1 & A1p & A1c & LX1).
              rewrite FB0 in HBLK1. destruct r1 as [b' st1]. cbn [fst snd] in ER1, EB1 |- *. subst st1 b'. cbn [bm_len bm_data bm_bytes].
              replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LX1 |- * by lia.
              replace (ret_pc (Z_to_bv 64 0x11311c)) with (Z_to_bv 64 0x11311c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
              pose proof (agree_of_lx_pres _ _ _ _ _ LX1) as AG1.
              assert (CL1 : forall a, (bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp /\ (a < BUF \/ BUF + 32 <= a)) -> lx_client (NEW1 ++ LB) (bv_unsigned sp + OFS + -144) ([(BUF, BUF + 32)] ++ LIBW_AP) a).
              { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
              apply (rw_cells_agree _ _ _ _ _ AG1) in FRH; [| intros a Ha; apply CL1; cbn in Ha; lia].
              apply (rw_cells_agree _ _ _ _ _ AG1) in HINF; [| intros a Ha; apply CL1; cbn in Ha; lia].
              apply (rw_cells_agree _ _ _ _ _ AG1) in HCST; [| intros a Ha; apply CL1; cbn in Ha; lia].
              apply (rw_cells_agree _ _ _ _ _ AG1) in HPLEN; [| intros a Ha; apply CL1; cbn in Ha; lia].
              apply (rw_cells_agree _ _ _ _ _ AG1) in HPPCT; [| intros a Ha; apply CL1; cbn in Ha; lia].
              apply (rw_cells_agree _ _ _ _ _ AG1) in FRS; [| intros a Ha; apply CL1; cbn in Ha; lia].
              apply (rw_cells_agree _ _ _ _ _ AG1) in HPP; [| intros a Ha; apply CL1; cbn in Ha; lia].
              pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI1) as (_ & _ & _ & STY & _ & _ & ERRY & MIY & _).
              pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OI1) as (HEAPY & NDY & BNDY & FRESHY & DJLY & DJOY).
              pose proof OI1 as (_ & _ & _ & _ & _ & _ & _ & HBY).
              unfold LX_ERRNO, RATP in ERRY. change (3355176 - 164) with 3355012 in ERRY.
              replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STY by lia.
              pose proof (BNDY q A' n' ltac:(apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & BAI' & _).
              (* [comment removed for export] *)
              destruct (slice_bytes mY D d (go_p g) plen HBY DF ltac:(lia) ltac:(lia) ltac:(lia)) as [SRC SLEN].
              assert (SEP : D + go_p g + plen <= A' + bm_len b \/ A' + bm_len b + plen <= D + go_p g).
              { destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)]; [exfalso; rewrite E0 in PLD; unfold zlength in PLD; cbn in PLD; lia|].
                pose proof (DJLY q A' n' pb PA psz ltac:(left; reflexivity) HPB). lia. }
              cut_hd HBLK1 HB1 (A' + bm_len b). pose proof (cb_len _ _ _ _ HBLK1) as RL.
              replace (Z.to_nat (n' - bm_len b)) with (Z.to_nat plen + Z.to_nat (n' - bm_len b - plen))%nat in HBLK1 by lia.
              apply cb_split in HBLK1. cut_hd HBLK1 HB2 (A' + bm_len b + plen). rename HBLK1 into HB3.
              unfold MallocRep.wz in *. cut_hd HBUF1 HLEN1 (BUF + 8). cut_hd HBUF1 HDAT1 (BUF + 16).
              clear MU WM. pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (A' + bm_len b, A' + bm_len b + plen)]%Z mY) as MU. pose proof (wmono_refl ctusegs mY) as WM.
              unfold implM. iprefix.
              step. if_cases KR; zc KR; [exfalso; revert KR; rewrite ?unsigned_lit by lia; lia|]. clear KR.
              step. step. step. step.
              step. step. setreg 10%Z (Z_to_bv 64 (A' + bm_len b)) ltac:(rewrite ?unsigned_lit by lia; f_equal; lia).
              eapply evt_cut.
              { eapply memcpy_callZ with (Dst := A' + bm_len b) (Src := D + go_p g) (N := plen) (src := to_bytes (slice d (go_p g) plen));
                  [exact SRC| rewrite <- (Nat2Z.id (length _)), SLEN; reflexivity| exact HB2| lia| lia| lia| lia| assumption]. }
              intros ms' PO. unfold memcpy_postZ in PO.
              destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & mZ & -> & MU2 & WM2 & MI2 & HCP & _).
              xport FRH MU2 WM2. xport HINF MU2 WM2. xport HCST MU2 WM2. xport HPLEN MU2 WM2. xport HPPCT MU2 WM2. xport FRS MU2 WM2. xport HPP MU2 WM2.
              xport HLEN1 MU2 WM2. xport HDAT1 MU2 WM2. xport HBUF1 MU2 WM2. xport HB1 MU2 WM2. xport HB3 MU2 WM2. xport ERRY MU2 WM2.
              match goal with H : stk ctusegs mY lo _ |- _ => rename H into ST1 end.
              assert (ST2 : stk ctusegs mZ lo (bv_unsigned sp + OFS + -144)).
              { eapply stk_transport; [exact ST1| exact MU2| exact WM2|]. intros x Hx. left. cbn. lia. }
              assert (MU' : munch [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (A' + bm_len b, A' + bm_len b + plen)]%Z mY mZ).
              { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x; cbn; lia. }
              pose proof (wmono_trans _ _ _ _ WM WM2) as WM'. clear MU WM MU2 WM2 ST1. rename MU' into MU. rename WM' into WM. clear MIY. rename MI2 into MI.
              replace (ret_pc (Z_to_bv 64 0x113158)) with (Z_to_bv 64 0x113158) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
              step. step.
              lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
              match goal with H : stk ctusegs mB lo _ |- _ => rename H into STB end.
              ihere. to_implM. apply implM_aret. apply evt_done. subst Q1. cbv beta.
              apply rw_cells_CB_of in HPLEN. cbn [cells_size csize Nat.add plus] in HPLEN.
              lazymatch type of HPPCT with rw_cells _ _ _ [C8 (Z_to_bv 64 ?v)] => replace v with (D + (go_p g + plen)) in HPPCT by (rewrite ?unsigned_lit by lia; lia) end.
              join2 FRH HINF. join2 FRH HCST. join2 FRH HPLEN. join2 FRH HPPCT. join2 FRH FRS.
              join2 HLEN1 HDAT1. join2 HLEN1 HBUF1.
              join2 HB1 HCP. apply cb_join in HB1. rewrite <- to_bytes_app in HB1.
              replace (Z.to_nat (bm_len b) + Z.to_nat plen)%nat with (Z.to_nat (bm_len b + plen)) in HB1 by lia. join2 HB1 HB3.
              eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, F1, fc1, mB, OWT, errvY, boT,
                      {| bm_len := bm_len b + plen; bm_data := Some (q, n'); bm_bytes := bm_bytes b ++ slice d (go_p g) plen |}, A', _.
              split; [reflexivity|]. split; [reflexivity|].
              split. { eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO' STK0 OFS0' SPB B63 SP16 OFS16' XPok PBX); [exact OI1| exact MU| exact WM| exact MI| replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia; exact STB| exact ERRY|].
                       constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists q, A', n'. split; [left; reflexivity| cbn; lia]. }
              split; [exact FRM1|]. split; [intros k Hk; rewrite (FE1 k Hk); apply (FEA k Hk)|].
              split; [unfold buf_cells, bm_max; cbn [bm_len bm_data]; exact HLEN1|].
              split. { unfold buf_inv. cbn [bm_len bm_data bm_bytes].
                       split; [lia|]. split; [rewrite zlength_app_c, zlength_slice by lia; lia|]. split; [apply Forall_app; split; [exact BBY| apply slice_range; exact DF]|].
                       split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BAI'|].
                       eexists. replace (n' - bm_len b - plen) with (n' - (bm_len b + plen)) in HB1 by lia. exact HB1. }
              split; [exact HPP|].
              split. { eapply lx_pres_trans; [exact LXAT|]. eapply lx_pres_trans.
                       - eapply lx_pres_weaken; [exact LX1| lia| intros b0 Hb0; exact Hb0| intros a Ha; apply rin_ivs_app in Ha; apply rin_ivs_app; destruct Ha as [Ha|Ha]; [left; cbn in Ha |- *; lia| right; exact Ha]].
                       - eapply (lx_pres_munch_gen s1' (OWT ++ [(q, A', n')]) (NEW1 ++ LB)); [rewrite <- app_assoc; exact HEAPY| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
                         constructor; [left; cbn; lia|]. constructor; [| constructor]. right. right. exists q, A', n'. split; [apply in_app_iff; right; left; reflexivity| cbn; lia]. }
              split; [exact FRH|]. cbn [bm_len]. lia. }
            destruct (bm_data b) as [[q n]|] eqn:EBD.
            -- destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). apply cb_join in HC.
               replace (Z.to_nat (bm_len b) + Z.to_nat (n - bm_len b))%nat with (Z.to_nat n) in HC by lia.
               eapply (implM_abind _ _ _ _ Q1).
               { eapply implM_abind.
                 { replace (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -144))) by (f_equal; lia).
                   eapply (BUF_MEM_grow_clean_walk HM HF sp m s LB E lo B canary K d D XP CEIL GLO SPB B63 SP16 XPok PBX (OFS + -144) (STK - 144)) with (b := b) (A0 := A)
                     (bytes := to_bytes (bm_bytes b) ++ rest);
                     [exact LO'| exact OFS0'| exact OFS16'| pose proof grow_le_tlen; unfold COLLECT_STACK, COLLECT_FRAME in STKG0; lia| exact OIT| exact FRM1
                     | lia| lia| exact BUFal| exact HBUF| unfold bm_max; rewrite EBD; lia| lia| lia| rewrite EBD; split; [lia| exact HC]]. }
                 intros r1 s1' ms1 PO1. try unfold MallocRep.wz in PO1. eapply AFTER; [| exact PO1].
                 rewrite firstn_app. pose proof (cb_len _ _ _ _ HC) as LL. rewrite length_app in LL.
                 replace (Z.to_nat (bm_len b) - length (to_bytes (bm_bytes b)))%nat with 0%nat by (pose proof (zlength_to_bytes (bm_bytes b)); unfold zlength in *; lia).
                 cbn [firstn]. rewrite app_nil_r. apply firstn_all2. pose proof (zlength_to_bytes (bm_bytes b)). unfold zlength in *. lia. }
               intros r sB msB POQ. subst Q1. cbv beta in POQ.
               destruct POQ as (z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z22 & z23 & z24 & z28 & z29 & z30 & z31 & FB & fcB & mB & OWB & errvB & boB & b1 & A1 & jl1
                                & -> & ER & OIB & FRMB & FEB & HBUFB & BIB & HPPB & LXB & FRB & BLPB).
               rewrite ER. cbn beta iota.
               eapply CONT; [exact OIB| exact FRMB| exact FEB| exact HBUFB| exact BIB| exact HPPB| exact LXB| exact FRB| lia| exact BLPB].
            -- destruct BI4 as [EA0 EL0].
               eapply (implM_abind _ _ _ _ Q1).
               { eapply implM_abind.
                 { replace (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -144))) by (f_equal; lia).
                   eapply (BUF_MEM_grow_clean_walk HM HF sp m s LB E lo B canary K d D XP CEIL GLO SPB B63 SP16 XPok PBX (OFS + -144) (STK - 144)) with (b := b) (A0 := A)
                     (bytes := []);
                     [exact LO'| exact OFS0'| exact OFS16'| pose proof grow_le_tlen; unfold COLLECT_STACK, COLLECT_FRAME in STKG0; lia| exact OIT| exact FRM1
                     | lia| lia| exact BUFal| exact HBUF| unfold bm_max; rewrite EBD; lia| lia| lia| rewrite EBD; exact EA0]. }
                 intros r1 s1' ms1 PO1. try unfold MallocRep.wz in PO1. eapply AFTER; [| exact PO1].
                 rewrite EL0. cbn [Z.to_nat firstn]. symmetry. rewrite BLEN in EL0. destruct (bm_bytes b); [reflexivity| unfold zlength in EL0; cbn in EL0; lia]. }
               intros r sB msB POQ. subst Q1. cbv beta in POQ.
               destruct POQ as (z1 & z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z22 & z23 & z24 & z28 & z29 & z30 & z31 & FB & fcB & mB & OWB & errvB & boB & b1 & A1 & jl1
                                & -> & ER & OIB & FRMB & FEB & HBUFB & BIB & HPPB & LXB & FRB & BLPB).
               rewrite ER. cbn beta iota.
               eapply CONT; [exact OIB| exact FRMB| exact FEB| exact HBUFB| exact BIB| exact HPPB| exact LXB| exact FRB| lia| exact BLPB].
        + (* [comment removed for export] *)
          apply Z.eqb_neq in EC. if_cases KC; zc KC; [exfalso|].
          { pose proof (land_32_cases (go_ret g)) as [L0|L32]; [exact (EC L0)|]. revert KC. rewrite L32. rewrite (byte_lit 32), (unsigned_lit 32) by lia. lia. }
          clear KC. cbv beta iota delta [negb]. fold (tlen_plen g p len). set (plen := tlen_plen g p len) in *.
          step. destruct (5 <=? depth) eqn:ED.
          * (* [comment removed for export] *)
            apply Z.leb_le in ED. if_cases KD; zc KD; [| exfalso; revert KD; rewrite ?unsigned_lit by lia; lia]. clear KD.
            ihere. to_implM. eapply implM_abind.
            { replace (bv_unsigned sp + OFS + -144) with (bv_unsigned sp + (OFS + -144)) by lia.
              eapply (co_raise 0x113234 0x113250 3%nat RS_coll_nest_str 197 (OFS + -144) (STK - 144));
                [right; right; left; repeat split; reflexivity| exact LO'| exact OFS0'| exact OFS16'| unfold ERR_SET_ERROR_STACK; lia| exact OIT| exact FRM1]. }
            intros r sB msB POB. unfold co_raise_post in POB.
            destruct POB as (o0 & o1 & o2 & n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & o3 & o4 & o5 & o6 & F2 & fc2 & mB & OW2 & errv2 & bo2 & -> & FRM2 & FE2 & OIb & LXb).
            replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LXb |- * by lia.
            pose proof (agree_of_lx_pres _ _ _ _ _ LXb) as AGb.
            assert (CL : forall a, bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp -> lx_client (buf_blk b A ++ NEW1 ++ LB) (bv_unsigned sp + OFS + -144) LIBW_AP a).
            { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
            rewrite <- app_assoc in AGb.
            apply rw_cells_CB_of in HPLEN. cbn [cells_size csize Nat.add plus] in HPLEN.
            join2 FRH HINF. join2 FRH HCST. join2 FRH HPLEN. join2 FRH HPPCT. join2 FRH FRS.
            destruct (co_head_blob _ _ _ _ _ _ _ _ _ _ FRH) as [jhd FRB]. clear FRH.
            apply (rw_cells_agree _ _ _ _ _ AGb) in FRB; [| intros a Ha; apply CL; cbn in Ha; lia].
            apply (rw_cells_agree _ _ _ _ _ AGb) in HBUF; [| intros a Ha; apply CL; unfold buf_cells in Ha; cbn in Ha; lia].
            apply (rw_cells_agree _ _ _ _ _ AGb) in HPP; [| intros a Ha; apply CL; cbn in Ha; lia].
            destruct r as [u stB]. cbn [fst snd] in *. apply implM_aret.
            eapply (co_ret0 OFS STK 0x113298 ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F2 fc2);
              [left; reflexivity| exact LO| exact OFS0| exact OFS16| unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIb| exact FRM2
              | intros k Hk; rewrite (FE2 k Hk), (FE1 k Hk); apply (FEA k Hk)
              | exact BUFlo| exact BUFhi| exact PPlo| exact PPhi| exact HBUF| | exact HPP| | exact FRB].
            -- destruct BIT as (BI1 & BI2 & BI3 & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|].
               destruct (bm_data b) as [[q n]|] eqn:EBD; [| exact BI4]. destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
               apply (rw_cells_agree _ _ _ _ _ AGb) in HC; [exact HC|]. intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; cbn in Ha; lia|].
               right. left. exists (q, A, n). split; [apply in_app_iff; left; unfold buf_blk; rewrite EBD; left; reflexivity| cbn; cbn in Ha; lia].
            -- eapply lx_pres_trans; [exact LXAT|]. eapply lx_pres_weaken; [exact LXb| lia| intros b0 Hb0; rewrite <- app_assoc; apply in_app_iff; right; exact Hb0| intros a Ha; apply rin_ivs_app; right; exact Ha].
          * (* [comment removed for export] *)
            apply Z.leb_gt in ED. if_cases KD; zc KD; [exfalso; revert KD; rewrite ?unsigned_lit by lia; lia|]. clear KD.
            step. step. setreg 13%Z (Z_to_bv 64 (Z.land (go_ret g) 1)) ltac:(rewrite zxb_lit by lia; reflexivity).
            step. step. step. step.
            assert (IV1 : Z.land (Z.land (go_ret g) 1) 1 = (if Z.testbit (go_ret g) 0 then 1 else 0)).
            { rewrite R11. destruct (Z.testbit (go_ret g) 0) eqn:TB.
              - apply (proj1 RTB). first [exact TB| reflexivity].
              - destruct R1 as [E1|E1]; [exact E1|]. exfalso. pose proof (proj2 RTB E1) as X. first [discriminate X| rewrite X in TB; discriminate TB]. }
            assert (IVR : 0 <= Z.land (go_ret g) 1 < 2 ^ 64) by lia.
            ihere. to_implM. eapply implM_abind.
            { replace (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -144))) by (f_equal; lia).
              eapply (IHE (OFS + -144) (STK - 144)) with (b := b) (A0 := A) (p := go_p g) (BUF := BUF) (PP := bv_unsigned sp + OFS + -112);
                [exact LO'| exact OFS0'| exact OFS16'| unfold COLLECT_STACK, COLLECT_FRAME in STKG0 |- *; lia| exact OIT| exact FRM1
                | lia| lia| exact BUFal| lia| lia| clear - SP16 OFS16; Z.div_mod_to_equations; lia| lia| exact HBUF| exact BIT| exact HPPCT| lia| lia| lia| lia| exact IVR| exact IV1| lia]. }
            intros r1 s1' ms1 PO1. unfold coll_post in PO1.
            destruct PO1 as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & F2 & fc2 & m2 & OW2 & errv2 & bo2 & A2
                             & -> & FRM2 & FE2 & OI2 & HBUF2 & BI2 & HPP2 & LX2 & BND2).
            replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LX2 |- * by lia.
            replace (ret_pc (Z_to_bv 64 0x1130e8)) with (Z_to_bv 64 0x1130e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
            destruct r1 as [[b1 ro] st1]. cbn [fst snd] in *.
            pose proof (agree_of_lx_pres _ _ _ _ _ LX2) as AG2.
            assert (CL2 : forall a, (bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp /\ (a < BUF \/ BUF + 32 <= a) /\ (a < bv_unsigned sp + OFS + -112 \/ bv_unsigned sp + OFS + -104 <= a)) ->
                      lx_client (NEW1 ++ LB) (bv_unsigned sp + OFS + -144) ([(BUF, BUF + 32); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 8)] ++ LIBW_AP) a).
            { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
            apply (rw_cells_agree _ _ _ _ _ AG2) in FRH; [| intros a Ha; apply CL2; cbn in Ha; lia].
            apply (rw_cells_agree _ _ _ _ _ AG2) in HINF; [| intros a Ha; apply CL2; cbn in Ha; lia].
            apply (rw_cells_agree _ _ _ _ _ AG2) in HCST; [| intros a Ha; apply CL2; cbn in Ha; lia].
            apply (rw_cells_agree _ _ _ _ _ AG2) in HPLEN; [| intros a Ha; apply CL2; cbn in Ha; lia].
            apply (rw_cells_agree _ _ _ _ _ AG2) in FRS; [| intros a Ha; apply CL2; cbn in Ha; lia].
            apply (rw_cells_agree _ _ _ _ _ AG2) in HPP; [| intros a Ha; apply CL2; cbn in Ha; lia].
            assert (LXA2 : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX m2).
            { eapply lx_pres_trans; [exact LXAT|].
              eapply (lx_pres_up _ _ _ _ _ _ _ lo); [exact LX2| lia| | lia|].
              - intros q A' n Hq. pose proof (BNDT q A' n ltac:(apply in_app_iff; right; rewrite <- app_assoc; apply in_app_iff; right; exact Hq)). lia.
              - intros a Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [| left; apply rin_ivs_app; right; exact Ha].
                cbn in Ha. destruct Ha as [Ha|[Ha|[]]]; [left; cbn; lia| right; lia]. }
            pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI2) as (_ & _ & _ & ST2 & _ & _ & ERR2 & MI2 & _).
            unfold LX_ERRNO, RATP in ERR2. change (3355176 - 164) with 3355012 in ERR2.
            replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in ST2 by lia.
            clear MU WM. pose proof (munch_refl (@nil (Z * Z)) m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
            apply rw_cells_CB_of in HPLEN. cbn [cells_size csize Nat.add plus] in HPLEN.
            unfold MallocRep.wz in *. unfold implM. iprefix.
            destruct ro as [p2|].
            -- (* [comment removed for export] *)
               step. if_cases KR; zc KR; [exfalso; revert KR; rewrite ?unsigned_lit by lia; lia|]. clear KR.
               step. ihere. to_implM. cbn beta iota.
               join2 FRH HINF. join2 FRH HCST. join2 FRH HPLEN. join2 FRH HPP2. join2 FRH FRS.
               eapply CONT; [exact OI2| exact FRM2| intros k Hk; rewrite (FE2 k Hk), (FE1 k Hk); apply (FEA k Hk)| exact HBUF2| exact BI2| exact HPP| exact LXA2| exact FRH| lia| lia].
            -- (* [comment removed for export] *)
               step. if_cases KR; zc KR; [| exfalso; apply KR; reflexivity]. clear KR.
               ihere. to_implM. cbn beta iota. apply implM_aret.
               join2 FRH HINF. join2 FRH HCST. join2 FRH HPLEN. join2 FRH HPP2. join2 FRH FRS.
               destruct (co_head_blob _ _ _ _ _ _ _ _ _ _ FRH) as [jhd FRB]. clear FRH.
               eapply (co_ret0 OFS STK 0x11329c ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F2 fc2);
                 [right; split; reflexivity| exact LO| exact OFS0| exact OFS16| unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI2| exact FRM2
                 | intros k Hk; rewrite (FE2 k Hk), (FE1 k Hk); apply (FEA k Hk)
                 | exact BUFlo| exact BUFhi| exact PPlo| exact PPhi| exact HBUF2| exact BI2| exact HPP| exact LXA2| exact FRB]. }
    (* [comment removed for export] *)
    assert (LO0 : 0 <= lo) by (destruct STA as [H _]; exact H).
    assert (DLO : D + zlength d <= lo).
    { destruct PBX as [E0|(pb & PA & psz & HPB & PB1 & PB2)]; [rewrite E0 in PLD; unfold zlength in PLD; cbn in PLD; lia|].
      pose proof (BND pb PA psz ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HPB)) as (_ & _ & BC & _). lia. }
    unfold implM. iprefix.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
      change (rw_cells ctusegs mA (bv_unsigned sp + OFS + -144) ([c0; c1; c2; c3; c4; c5] ++ [c6] ++ rest)) in FR end.
    apply rw_cells_app in FR. destruct FR as [FRH FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FPC FRS]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRS.
    replace (bv_unsigned sp + OFS + -144 + 32) with (bv_unsigned sp + OFS + -112) in FPC by lia.
    step. step. step.
    eapply evt_cut.
    { eapply (check_eoc_walk (bv_unsigned sp + OFS + -144) (bv_unsigned sp + OFS + -112)) with (lo := lo) (D := D) (p := p) (len := len) (d := d);
        [exact STA| exact MIA| lia| lia| clear - SP16 OFS16; Z.div_mod_to_equations; lia| exact FPC| clear - SP16 OFS16; Z.div_mod_to_equations; lia
        | lia| lia| right; lia| left; lia| exact HB| exact DF| exact D1| exact DLO| exact D63| lia| lia| lia]. }
    intros ms' (y11 & y12 & mq & -> & MUq & WMq & MIq & STq & HPq). cbv beta.
    replace (ret_pc (Z_to_bv 64 1126540)) with (Z_to_bv 64 1126540) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct (eoc_test d p len) eqn:EOC.
    - replace (Z_to_bv 64 (if true then 1 else 0)) with (Z_to_bv 64 1) by reflexivity.
      replace (if true then p + 2 else p) with (p + 2) in HPq by reflexivity.
      assert (L2 : 2 <= len) by (unfold eoc_test in EOC; apply andb_true_iff in EOC as [EOC _]; apply andb_true_iff in EOC as [EOC _]; apply Z.leb_le in EOC; exact EOC).
      unfold eoc_test in EOC. rewrite EOC.
      pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
      xport FRH MUq WMq. xport FRS MUq WMq. xport HPP MUq WMq. xport ERRA MUq WMq.
      eapply rw_cells_transport in HBUF; [| exact MUq| exact WMq| unfold buf_cells; cbn [cells_size csize Nat.add disjoint_from fst snd]; cbn; lia].
      assert (OIq : oinvK (OFS + -144) (STK - 144) sA stA mq OWA errvA boA (buf_blk b A ++ NEW1)).
      { eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO' STK0 OFS0' SPB B63 SP16 OFS16' XPok PBX);
          [exact OI| exact MUq| exact WMq| exact MIq| replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia; exact STq| exact ERRA|].
        constructor; [left; cbn; lia| constructor; [left; cbn; lia| constructor]]. }
      assert (BIq : buf_inv mq b A).
      { destruct BI as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
        destruct (bm_data b) as [[q n]|]; [| exact B4]. destruct B4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
        eapply rw_cells_transport; [exact HC| exact MUq| exact WMq|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. cbn. lia. }
      assert (LXq : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX mq).
      { eapply lx_pres_trans; [exact LXA|].
        eapply (lx_pres_munch_gen sA (OWA ++ buf_blk b A) (NEW1 ++ LB)); [rewrite <- app_assoc; rewrite (app_assoc (buf_blk b A)); exact HEAPA| exact CEIL| exact GLO| lia| exact MUq| exact WMq|].
        constructor; [left; cbn; lia| constructor; [left; cbn; lia| constructor]]. }
      join2 FRH HPq. join2 FRH FRS. rename FRH into FRq.
      clear OI BI LXA MUq WMq.
      step. step. destruct inf.
      + step. if_cases KI; zc KI; try (exfalso; first [apply KI; reflexivity| revert KI; rewrite ?unsigned_lit by lia; lia]).
        step.
        ihere. to_implM. apply implM_aret.
        destruct (co_head_blob _ _ _ _ _ _ _ _ _ _ FRq) as [jhd FRB]. clear FRq.
        eapply (co_ret1 OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX FA fcA);
          [exact LO| exact OFS0| exact OFS16| unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIq| exact FRMA| exact FEA
          | exact BUFlo| exact BUFhi| exact PPlo| exact PPhi| exact DJ| exact HBUF| exact BIq| exact HPP| exact LXq| exact FRB| lia| lia| lia].
      + step. if_cases KI; zc KI; try (exfalso; first [apply KI; reflexivity| revert KI; rewrite ?unsigned_lit by lia; lia]).
        ihere. to_implM. eapply implM_abind.
        { replace (bv_unsigned sp + OFS + -144) with (bv_unsigned sp + (OFS + -144)) by lia.
          eapply (co_raise 1126880 1126908 3%nat RS_coll_unexp_eoc 159 (OFS + -144) (STK - 144));
            [right; right; right; repeat split; reflexivity| exact LO'| exact OFS0'| exact OFS16'| unfold ERR_SET_ERROR_STACK; lia| exact OIq| exact FRMA]. }
        intros r sB msB POB. unfold co_raise_post in POB.
        destruct POB as (o0 & o1 & o2 & n0 & n1 & n2 & n3 & n4 & n5 & n6 & n7 & o3 & o4 & o5 & o6 & F2 & fc2 & mB & OW2 & errv2 & bo2 & -> & FRM2 & FE2 & OIb & LXb).
        replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LXb |- * by lia.
        pose proof (agree_of_lx_pres _ _ _ _ _ LXb) as AGb.
        assert (CL : forall a, bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp -> lx_client (buf_blk b A ++ NEW1 ++ LB) (bv_unsigned sp + OFS + -144) LIBW_AP a).
        { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
        rewrite <- app_assoc in AGb.
        destruct (co_head_blob _ _ _ _ _ _ _ _ _ _ FRq) as [jhd FRB]. clear FRq.
        apply (rw_cells_agree _ _ _ _ _ AGb) in FRB; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGb) in HBUF; [| intros a Ha; apply CL; unfold buf_cells in Ha; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AGb) in HPP; [| intros a Ha; apply CL; cbn in Ha; lia].
        destruct r as [u stB]. cbn [fst snd] in *. apply implM_aret.
        eapply (co_ret0 OFS STK 1127064 ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F2 fc2);
          [left; reflexivity| exact LO| exact OFS0| exact OFS16| unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIb| exact FRM2
          | intros k Hk; rewrite (FE2 k Hk); apply (FEA k Hk)
          | exact BUFlo| exact BUFhi| exact PPlo| exact PPhi| exact HBUF| | exact HPP| | exact FRB].
        * destruct BIq as (BI1 & BI2 & BI3 & BI4). split; [exact BI1|]. split; [exact BI2|]. split; [exact BI3|].
          destruct (bm_data b) as [[q n]|] eqn:EBD; [| exact BI4]. destruct BI4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
          apply (rw_cells_agree _ _ _ _ _ AGb) in HC; [exact HC|]. intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; cbn in Ha; lia|].
          right. left. exists (q, A, n). split; [apply in_app_iff; left; unfold buf_blk; rewrite EBD; left; reflexivity| cbn; cbn in Ha; lia].
        * eapply lx_pres_trans; [exact LXq|]. eapply lx_pres_weaken; [exact LXb| lia| intros b0 Hb0; rewrite <- app_assoc; apply in_app_iff; right; exact Hb0| intros a Ha; apply rin_ivs_app; right; exact Ha].
    - replace (Z_to_bv 64 (if false then 1 else 0)) with (Z_to_bv 64 0) by reflexivity.
      replace (if false then p + 2 else p) with p in HPq by reflexivity.
      step. try (if_cases KE; zc KE; try (exfalso; revert KE; rewrite ?unsigned_lit by lia; lia)).
      unfold eoc_test in EOC. rewrite EOC.
      eapply TLEN; [exact MUq| exact WMq| exact MIq| exact STq| exact HPq].
  Qed.

  (* [comment removed for export] *)
  Lemma entry_of_loop : forall f, loop_ok f -> entry_ok f.
  Proof using B63 CEIL D30 GLO HF HM PBX SP16 SPB XPok.
    intros f IHL. unfold entry_ok.
    intros until PP. intros LO OFS0 OFS16 STKG OI FRMX BUFlo BUFhi BUFal PPlo PPhi PPal DJ HBUF BI HPP P0 LEN0 PL DEP IVR IV1 BLP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof STKG as STKG0. unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK) by lia.
    pose proof (ESP sp lo B OFS STK GLO LO STK0 OFS0 SPB B63) as ESP.
    pose proof (oinv_facts sp m s LB E lo B canary K d D XP OFS STK _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & _).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP OFS STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STX & _ & _ & ERRX & MIX & _).
    unfold LX_ERRNO, RATP in ERRX. change (3355176 - 164) with 3355012 in ERRX.
    unfold ASN1_COLLECT, MallocRep.wz in *. unfold buf_cells in HBUF.
    pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    unfold implM. iprefix.
    carve_frame 144%nat STX. do 15 step.
    step. step. step. step. step. step. setreg 13%Z (Z_to_bv 64 (if inf then 1 else 0)) ltac:(rewrite <- IV1, (unsigned_lit iv) by lia; reflexivity).
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ ?mm _ (?c0 :: ?c1 :: CB 16 ?j :: ?rest) =>
      change (rw_cells ctusegs mm (bv_unsigned sp + OFS + -144) ([c0; c1] ++ [CB 16 j] ++ rest)) in FR; set (j16 := j) in FR; clearbody j16 end.
    apply rw_cells_app in FR. destruct FR as [FRA FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FRJ FRB]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    replace (bv_unsigned sp + OFS + -144 + 16) with (bv_unsigned sp + OFS + -128) in FRJ by lia.
    replace (bv_unsigned sp + OFS + -144 + 16 + 16) with (bv_unsigned sp + OFS + -112) in FRB by lia.
    apply (cb_split _ _ 6 10) in FRJ. cut_hd FRJ FJ6 (bv_unsigned sp + OFS + -122).
    apply (cb_split _ _ 1 9) in FRJ. cut_hd FRJ FJI (bv_unsigned sp + OFS + -121).
    apply (cb_split _ _ 1 8) in FRJ. cut_hd FRJ FJC (bv_unsigned sp + OFS + -120).
    destruct (cb_byte _ _ _ FJI) as [bi FJI']. clear FJI. destruct (cb_byte _ _ _ FJC) as [bc FJC']. clear FJC.
    join2 FRA FJ6. join2 FRA FJI'. join2 FRA FJC'. join2 FRA FRJ. join2 FRA FRB. rename FRA into FR. rewrite (unsigned_lit iv), IV1 in FR by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with H : stk ctusegs m1 lo _ |- _ => rename H into ST1 end. match goal with H : mem_inv ctusegs m1 |- _ => rename H into MI1 end.
    (* [comment removed for export] *)
    stk_join ST1 FR STF (bv_unsigned sp + OFS).
    assert (OI0 : oinvK OFS STK sX stX m1 OWX errvX boX (buf_blk b A0 ++ NEW1)).
    { eapply (oinv_munch sp m s LB E lo B canary K d D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OI| exact MU| exact WM| exact MI1| exact STF| exact ERRX|].
      constructor; [left; cbn; lia| constructor]. }
    assert (OFS16' : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    assert (OI1 : oinvK (OFS + -144) (STK - 144) sX stX m1 OWX errvX boX (buf_blk b A0 ++ NEW1)).
    { eapply (oinv_reframe sp m s LB E lo B canary K d D XP OFS STK); [exact OI0| exact SPB| exact SP16| replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia; exact ST1| lia| lia| lia| exact OFS16']. }
    assert (LX1 : lx_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32); (PP, PP + 8)] ++ LIBW_AP) mX m1).
    { eapply (lx_pres_munch_gen sX (OWX ++ buf_blk b A0) (NEW1 ++ LB)); [rewrite <- app_assoc; rewrite (app_assoc (buf_blk b A0)); exact HEAPX| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
      constructor; [left; cbn; lia| constructor]. }
    assert (BI1 : buf_inv m1 b A0).
    { destruct BI as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
      destruct (bm_data b) as [[q n]|]; [| exact B4]. destruct B4 as (C1' & C2 & C3 & C4' & C5 & rest & HC). repeat (split; [assumption|]). exists rest.
      eapply rw_cells_transport; [exact HC| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. cbn. lia. }
    step. if_cases KL; zc KL.
    - (* [comment removed for export] *)
      assert (EL : len = 0) by (apply andb_false_iff in KL; destruct KL as [KL|KL]; apply Z.ltb_ge in KL; lia). subst len.
      step. ihere. to_implM.
      eapply (co_exit f OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX FX fcX) with (p0 := p) (len0 := 0);
        [exact LO| exact OFS0| exact OFS16| unfold COLLECT_STACK, COLLECT_FRAME, CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI1| exact FRMX| intros k Hk; reflexivity
        | exact BUFlo| exact BUFhi| exact PPlo| exact PPhi| exact DJ| exact HBUF| exact BI1| exact HPP| exact LX1| exact FR| lia| lia| lia| exact BLP].
    - (* [comment removed for export] *)
      do 5 step.
      setreg 21%Z (Z_to_bv 64 (depth + 1)) ltac:(rewrite ?unsigned_lit by lia; rewrite ?swrap32_small by lia; reflexivity).
      setreg 24%Z (Z_to_bv 64 0) ltac:(rewrite (unsigned_lit BUF) by lia; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; rewrite BUFal; reflexivity).
      ihere. to_implM.
      eapply (IHL OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX FX fcX) with (p0 := p) (len0 := len);
        [exact LO| exact OFS0| exact OFS16| exact STKG0| exact OI1| exact FRMX| intros k Hk; reflexivity
        | exact BUFlo| exact BUFhi| exact BUFal| exact PPlo| exact PPhi| exact PPal| exact DJ| exact HBUF| exact BI1| exact HPP| exact LX1| exact FR| lia| lia| exact KL0| lia| lia| lia| exact BLP].
  Qed.

  Theorem collect_ok : forall fuel, loop_ok fuel /\ entry_ok fuel.
  Proof using B63 CEIL D1 D30 D63 DF GLO HF HGO HM PBX SP16 SPB XPok.
    induction fuel as [|f [IHL IHE]].
    - split; [apply loop_ok_O|]. unfold entry_ok. intros. rewrite collect_O. apply implM_aunr.
    - pose proof (loop_step f IHL IHE) as L1. split; [exact L1| apply entry_of_loop; exact L1].
  Qed.

  (* [comment removed for export] *)
  Theorem asn1_collect_walk : forall fuel, entry_ok fuel.
  Proof using B63 CEIL D1 D30 D63 DF GLO HF HGO HM PBX SP16 SPB XPok. intros fuel. exact (proj2 (collect_ok fuel)). Qed.

  End Act.
End Proofs.
End WithCeiling0.
