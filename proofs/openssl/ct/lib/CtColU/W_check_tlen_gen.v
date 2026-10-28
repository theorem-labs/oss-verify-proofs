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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApErrKit2 ApErrKit3 ApIface W_err_new W_err_set_debug W_err_set_error W_c2i_int W_get_object W_check_tlen.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnBoth Require Import UbKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColU Require Import ColKit ColDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac ubchk_strong := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep;
  let C := fresh "Cs" in if_cases C;
  [ exfalso; zify_cond C;
    try unfold MallocRep.wz in C;
    repeat (first [ rewrite unsigned_lit in C by lia | rewrite swrap32_small in C by lia | rewrite ub_land64_small in C by lia | rewrite ub_lxor_sign63 in C by lia ]);
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
Local Ltac zstep := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
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
Definition A_ASN1_CHECK_TLEN : Z := 0x23ff3.

(* [comment removed for export] *)
Definition tlen_tree {X} (g : go_res) (ot : option Z) (KE KW KS : @AM bptr X) : @AM bptr X :=
  match go_err g with
  | Some e => abind (tlen_fail e) (fun _ => KE)
  | None =>
      match ot with
      | None => KS
      | Some t => if negb (go_tag g =? t) || negb (go_cls g =? 0) then abind (err_raise RS_tlen_wrong_tag) (fun _ => KW) else KS
      end
  end.

(* [comment removed for export] *)
Definition tlen_plen (g : go_res) (op len : Z) : Z :=
  if Z.testbit (go_ret g) 0 then len - (go_p g - op) else go_len g.

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
  Lemma D0 : 0 <= D. Proof using D1 sp. lia. Qed.

  Local Notation oinvK OFS STK := (oinv sp m s LB E lo B canary K d D XP OFS STK).

  (* [comment removed for export] *)
  Definition go_post (OFS' STK' : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX : bvmap 5 word) (mX : mem) (NEW : list block)
      (g : go_res) (PP PL PT PC : Z) (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY (errvY : word) boY (jl j2 j3 : list byte),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (wz RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None mY (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get FX k)
      /\ oinvK OFS' STK' s' (snd r) mY OWY errvY boY NEW
      /\ lx_pres (NEW ++ LB) (bv_unsigned sp + OFS') ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_AP) mX mY
      /\ rw_cells ctusegs mY PP [C8 (wz (D + go_p g))]
      /\ match go_err g with
         | None => a0 = wz (go_ret g)
                   /\ rw_cells ctusegs mY PL [C8 (wz (go_len g))] /\ rw_cells ctusegs mY PT [C4 (wz (go_tag g))] /\ rw_cells ctusegs mY PC [C4 (wz (go_cls g))]
         | Some GeTooLong => a0 = wz (Z.lor (go_ret g) 128)
                   /\ rw_cells ctusegs mY PL [C8 (wz (go_len g))] /\ rw_cells ctusegs mY PT [C4 (wz (go_tag g))] /\ rw_cells ctusegs mY PC [C4 (wz (go_cls g))]
         | Some _ => a0 = wz 128
                   /\ rw_cells ctusegs mY PL [CB 8 jl] /\ rw_cells ctusegs mY PT [CB 4 j2] /\ rw_cells ctusegs mY PC [CB 4 j3]
         end.

  Lemma go_call : forall (OFS' STK' : Z)
      (ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX NEW (op len PP PL PT PC : Z) (jl j2 j3 : list byte),
    lo <= bv_unsigned sp + OFS' - STK' -> OFS' <= 0 -> OFS' mod 16 = 0 -> GETOBJ_STACK <= STK' ->
    oinvK OFS' STK' sX stX mX OWX errvX boX NEW -> frm0 fcX ->
    0 <= op -> 0 < len -> op + len <= zlength d ->
    go_cells_ok (bv_unsigned sp + OFS') PP PL PT PC -> PP + 8 <= bv_unsigned sp -> PL + 8 <= bv_unsigned sp -> PT + 4 <= bv_unsigned sp -> PC + 4 <= bv_unsigned sp ->
    rw_cells ctusegs mX PP [C8 (wz (D + op))] -> rw_cells ctusegs mX PL [CB 8 jl] -> rw_cells ctusegs mX PT [CB 4 j2] -> rw_cells ctusegs mX PC [CB 4 j3] ->
    implM ctusegs (interp (ap_embed (go_eff (get_object d op len) stX))) sX
          (go_post OFS' STK' ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW (get_object d op len) PP PL PT PC)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (wz RATP) t0 t1 t2 s0 s1 (wz PP) (wz PL) (wz PT) (wz PC) (wz len) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              FX (wz ASN1_GET_OBJECT) fcX None mX (seg_rom ctusegs)).
  Proof using B63 CEIL D1 D30 D63 DF GLO HGO PBX SPB XPok.
    intros until j3. intros LO OFS0 OFS16 STKG OI FRMX OP0 LEN0 OPL GC B1 B2 B3 B4 HPP HPL HPT HPC.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (STK0 : 0 <= STK') by (unfold GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG; lia).
    pose proof (ESP sp lo B OFS' STK' GLO LO STK0 OFS0 SPB B63) as ESP.
    pose proof OI as (PREX & LXX & KO & KI & KP & SO & FA & HB).
    pose proof HGO as W. unfold ASN1_get_object_spec in W.
    eapply implM_mono.
    { eapply W with (K := K) (d := d) (op := op) (omax := len) (PP := PP) (PL := PL) (PT := PT) (PC := PC);
        [ eapply ap_pre_stack_le; [exact PREX| exact STKG] | reflexivity | exact FRMX | exact KO | exact KI
        | exact (oinv_payload sp m s LB E lo B canary K d D XP OFS' STK' DF PBX _ _ _ _ _ _ _ OI D1 D63 D30) | exact OP0 | exact LEN0 | exact OPL
        | rewrite ESP; exact GC | lia | lia | lia | lia
        | exact HPP | exact HPL | exact HPT | exact HPC
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]. }
    intros r s' ms' PO. cbv beta in PO. unfold getobj_post in PO. rewrite ?ESP in PO.
    destruct PO as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F' & fc' & mY & OWY & errvY & jl' & j2' & j3'
                     & -> & FRM' & FE' & PREY & LXY & SOY & FAY & BKY & HPPY & RES).
    unfold go_post. exists q0, q1, q2, p0, p1, p2, p3, p4, p5, p6, p7, q3, q4, q5, q6, F', fc', mY, OWY, errvY, boX, jl', j2', j3'.
    split; [reflexivity|]. split; [exact FRM'|]. split; [exact FE'|].
    split.
    { eapply (oinv_after sp m s LB E lo B canary K d D XP OFS' STK' CEIL GLO LO STK0 OFS0 SPB B63 OFS16 XPok PBX _ _ _ _ _ _ NEW s' (snd r) mY OWY errvY boX _ []);
        [exact OI| exact PREY| exact LXY| | exact SOY| exact FAY| exact BKY].
      intros a Ha. left. unfold go_cells_ok in GC. cbn [rin_ivs fst snd app] in Ha. lia. }
    split; [exact LXY|]. split; [exact HPPY| exact RES].
  Qed.

  (* [comment removed for export] *)
  Definition tlen_post (OFS STK : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX : bvmap 5 word) (mX : mem) (NEW : list block)
      (PIC PPC : Z) (TLCo : option Z) (rv : Z) (cells_pic : list cell) (pp : Z)
      (st' : ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY (errvY : word) boY,
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz RATP) t0 t1 t2 s0 s1 (wz rv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None mY (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get FX k)
      /\ oinvK OFS STK s' st' mY OWY errvY boY NEW
      /\ lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) ([(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)] ++ LIBW_AP) mX mY
      /\ rw_cells ctusegs mY PIC cells_pic /\ rw_cells ctusegs mY PPC [C8 (wz pp)]
      /\ match TLCo with Some a => exists vb j, rw_cells ctusegs mY a [C1 vb; CB 31 j] | None => True end.

  (* [comment removed for export] *)
  Definition tl_site (base : Z) (rs : rsite) : Prop :=
    (base = 0x1129fc /\ rs = RS_tlen_bad_hdr) \/ (base = 0x112a90 /\ rs = RS_tlen_wrong_tag).

  Definition tl_raise_post (OFS' STK' : Z) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp : word) (FX : bvmap 5 word) (mX : mem) (NEW : list block)
      (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) mY OWY (errvY : word) boY,
      ms' = MS (mkR (Z_to_bv 64 0x112a28) (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F' (Z_to_bv 64 0x112a28) fc' None mY (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get FX k)
      /\ oinvK OFS' STK' s' (snd r) mY OWY errvY boY NEW
      /\ lx_pres (NEW ++ LB) (bv_unsigned sp + OFS') LIBW_AP mX mY.

  Lemma tl_raise : forall base rs (OFS' STK' : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp : word)
      (FX : bvmap 5 word) (fcX : bv 32) sX stX mX OWX errvX boX NEW,
    tl_site base rs ->
    lo <= bv_unsigned sp + OFS' - STK' -> OFS' <= 0 -> OFS' mod 16 = 0 -> ERR_SET_ERROR_STACK <= STK' ->
    oinvK OFS' STK' sX stX mX OWX errvX boX NEW -> frm0 fcX ->
    implM ctusegs (interp (ap_embed (err_raise rs stX))) sX (tl_raise_post OFS' STK' x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp FX mX NEW)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FX (Z_to_bv 64 base) fcX None mX (seg_rom ctusegs)).
  Proof using B63 CEIL GLO HF HM PBX SPB XPok.
    intros until NEW. intros SITE LO OFS0 OFS16 STKG OI FRMX.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (STK0 : 0 <= STK') by (unfold ERR_SET_ERROR_STACK in STKG; lia).
    pose proof (ESP sp lo B OFS' STK' GLO LO STK0 OFS0 SPB B63) as ESP.
    destruct (lit_ok_auto A_TASN_DEC_C 23 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_ok_auto A_ASN1_CHECK_TLEN 16 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    assert (RSF : rs_flen rs = 23) by (destruct SITE as [(_ & ->)|(_ & ->)]; reflexivity).
    assert (RSN : rs_fnlen rs = 16) by (destruct SITE as [(_ & ->)|(_ & ->)]; reflexivity).
    rewrite <- RSF in LF. rewrite <- RSN in LN.
    unfold err_raise. pose proof OI as (PREX & LXX & KO & KI & KP & SO & FA & HB).
    pose proof (munch_refl (@nil (Z * Z)) mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    (* [comment removed for export] *)
    assert (TAIL : forall (r1 : unit * ap_st bptr) (sA : PState) (raD rsn : Z) (nmid : nat) (q5 q6 q7 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (F1 : bvmap 5 word) (fc1 : bv 32) mA OW1 (errv1 : word) bo1,
      ((raD = 0x112a18 /\ nmid = 2%nat /\ rs = RS_tlen_bad_hdr /\ rsn = 102) \/ (raD = 0x112aac /\ nmid = 3%nat /\ rs = RS_tlen_wrong_tag /\ rsn = 168)) ->
      frm0 fc1 -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F1 k = reg_get FX k) ->
      oinvK OFS' STK' sA (snd r1) mA OW1 errv1 bo1 NEW -> lx_pres (NEW ++ LB) (bv_unsigned sp + OFS') LIBW_AP mX mA ->
      implM ctusegs (interp (ap_embed (abind (err_set_debug rs) (fun _ => err_set_error rs) (snd r1)))) sA (tl_raise_post OFS' STK' x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp FX mX NEW)
        (MS (mkR (Z_to_bv 64 raD) (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (wz RATP) q5 q6 q7 x8 x9 (wz A_TASN_DEC_C) (wz (rs_line rs)) (wz A_ASN1_CHECK_TLEN) q13 q14 q15 q16 q17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 q28 q29 q30 q31)
            F1 (wz ERR_SET_DEBUG) fc1 None mA (seg_rom ctusegs))).
    { intros until bo1. intros HS FRM1 FE1 OIa LXa.
      assert (RC : rs_code rs = ERR_PACK 13 rsn /\ 0 <= rsn < 8388608) by (destruct HS as [(_ & _ & -> & ->)|(_ & _ & -> & ->)]; (split; [reflexivity| lia])).
      destruct RC as [RC RB].
      eapply implM_abind.
      { eapply (oinv_ap_call sp m s LB E lo B canary K d D XP OFS' STK' CEIL GLO LO STK0 OFS0 SPB B63 OFS16 XPok PBX);
          [exact (ERR_set_debug_walk HM HF rs A_TASN_DEC_C A_ASN1_CHECK_TLEN bo1 _ _ _ _ LF LN)| exact OIa| unfold ERR_SET_DEBUG_STACK, ERR_SET_ERROR_STACK in *; lia| exact FRM1| cbv beta; repeat split; reflexivity]. }
      intros r2 sB ms2 PO2. unfold ap_call_post in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                       & -> & FRM2 & FE2 & OIb & LXb & EBO2). cbv beta in EBO2. subst bo2.
      unfold MallocRep.wz.
      assert (SE : forall (q5' q6' q7' q13' q14' q15' q16' q17' q28' q29' q30' q31' : word) mB',
        mB' = mB ->
        implM ctusegs (interp (ap_embed (err_set_error rs (snd r2)))) sB (tl_raise_post OFS' STK' x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 gp FX mX NEW)
          (MS (mkR (Z_to_bv 64 0x112a28) (Z_to_bv 64 (bv_unsigned sp + OFS')) gp (Z_to_bv 64 RATP) q5' q6' q7' x8 x9 (Z_to_bv 64 13) (Z_to_bv 64 rsn) (Z_to_bv 64 0) q13' q14' q15' q16' q17'
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
        replace (ret_pc (Z_to_bv 64 0x112a28)) with (Z_to_bv 64 0x112a28) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        unfold tl_raise_post. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3, bo1.
        split; [reflexivity|]. split; [exact FRM3|]. split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk); apply (FE1 k Hk)|].
        split; [exact OIc|]. eapply lx_pres_trans; [exact LXa|]. eapply lx_pres_trans; [exact LXb| exact LXc]. }
      pose proof (oinv_call sp m s LB E lo B canary K d D XP OFS' STK' GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OIb) as (_ & _ & _ & STb & _ & _ & ERRb & MIb & _).
      unfold LX_ERRNO, RATP in ERRb. change (3355176 - 164) with 3355012 in ERRb.
      clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mB) as MU. pose proof (wmono_refl ctusegs mB) as WM.
      unfold implM. iprefix.
      destruct HS as [(-> & -> & RS & ->)|(-> & -> & RS & ->)];
        (lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end).
      - step. step. step. step. ihere. to_implM. apply SE. reflexivity.
      - step. step. step. step. step. ihere. to_implM. apply SE. reflexivity. }
    (* [comment removed for export] *)
    destruct SITE as [(-> & ->)|(-> & ->)];
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
         unfold implM; iprefix; do 5 step; step; ihere; to_implM ]).
    - eapply (TAIL r1 sA 0x112a18 102 2%nat); [left; repeat split; reflexivity| exact FRM1| exact FE1| exact OIa| exact LXa].
    - eapply (TAIL r1 sA 0x112aac 168 3%nat); [right; repeat split; reflexivity| exact FRM1| exact FE1| exact OIa| exact LXa].
  Qed.

  Definition tlen_postR (OFS STK : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX : bvmap 5 word) (mX : mem) (NEW : list block)
      (PIC PPC : Z) (TLCo : option Z) (rv : Z) (cells_pic : list cell) (pp : Z) (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    tlen_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW PIC PPC TLCo rv cells_pic pp (snd r) s'.

  (* [comment removed for export] *)
  Definition tl_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma tlen_ret0 : forall (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      sA stA mX mA OWA errvA boA NEW (PIC PPC : Z) (TLCo : option Z) (cpic : list cell) (pp : Z) (jhd : list byte) (vb : byte) (jt : list byte),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> CHECK_TLEN_STACK <= STK ->
    oinvK (OFS + -144) (STK - 144) sA stA mA OWA errvA boA NEW -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get FX k) ->
    bv_unsigned sp + OFS <= PIC -> PIC + 10 <= bv_unsigned sp -> bv_unsigned sp + OFS <= PPC -> PPC + 8 <= bv_unsigned sp ->
    match TLCo with Some a => PIC + 10 <= a /\ PPC + 8 <= a /\ a + 32 <= bv_unsigned sp /\ a mod 8 = 0 /\ rw_cells ctusegs mA a [C1 vb; CB 31 jt] | None => True end ->
    lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) ([(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)] ++ LIBW_AP) mX mA ->
    rw_cells ctusegs mA PIC cpic -> cells_size cpic = 10%nat -> rw_cells ctusegs mA PPC [C8 (wz pp)] ->
    rw_cells ctusegs mA (bv_unsigned sp + OFS + -144) (CB 40 jhd :: tl_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    evt ctusegs (tlen_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW PIC PPC TLCo 0 cpic pp stA sA)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (wz RATP) x5 x6 x7 x8 (wz match TLCo with Some a => a | None => 0 end) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FA (Z_to_bv 64 0x112a28) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL GLO PBX SP16 SPB XPok.
    intros until jt. intros LO OFS0 OFS16 STKG OI FRMA FEA PIClo PIChi PPClo PPChi HTLC LXA HPIC SZP HPPC FR.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK - 144) by lia. assert (LO' : lo <= bv_unsigned sp + (OFS + -144) - (STK - 144)) by lia.
    assert (OFS0' : OFS + -144 <= 0) by lia. assert (OFS16' : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OI) as (HEAPA & NDA & BND & _).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STA by lia.
    unfold tl_saved in FR. unfold MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)]%Z mA) as MU.
    pose proof (wmono_refl ctusegs mA) as WM.
    destruct TLCo as [TLC|].
    - destruct HTLC as (T1 & T2 & T3 & T8 & HT). cut_hd HT HTV (TLC + 1).
      step. if_cases KC; zc KC; [exfalso; revert KC; rewrite ?unsigned_lit by lia; lia|]. clear KC.
      step. step. step.
      do 14 step. release_frame FR STA (bv_unsigned sp + OFS). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
      join2 HTV HT.
      apply evt_done. unfold tlen_post.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FA, fcA, m3, OWA, errvA, boA.
      split; [reflexivity|]. split; [exact FRMA|]. split; [exact FEA|].
      split. { eapply (oinv_reframe sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) OFS STK); [| exact SPB| exact SP16| exact ST3| lia| lia| lia| exact OFS16].
               eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO' STK0 OFS0' SPB B63 SP16 OFS16' XPok PBX); [exact OI| exact MU| exact WM| exact MI3| | exact ERRA|].
               - replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia.
                 destruct (stk_carve ctusegs m3 lo (bv_unsigned sp + OFS) 144 ST3 ltac:(lia)) as [ST4 _]. replace (bv_unsigned sp + OFS - Z.of_nat 144) with (bv_unsigned sp + OFS + -144) in ST4 by lia. exact ST4.
               - constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
      split. { eapply lx_pres_trans; [exact LXA|].
               eapply (lx_pres_munch_gen sA OWA (NEW ++ LB)); [exact HEAPA| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
               constructor; [left; cbn; lia|]. constructor; [| constructor]. right. left. split; [cbn; lia|]. intros a Ha. cbn in Ha. cbn. right. right. left. lia. }
      split; [exact HPIC|]. split; [exact HPPC|]. exists (Z_to_bv 8 0), jt. exact HTV.
    - step. if_true. step.
      do 14 step. release_frame FR STA (bv_unsigned sp + OFS). step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
      apply evt_done. unfold tlen_post.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FA, fcA, m3, OWA, errvA, boA.
      split; [reflexivity|]. split; [exact FRMA|]. split; [exact FEA|].
      split. { eapply (oinv_reframe sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) OFS STK); [| exact SPB| exact SP16| exact ST3| lia| lia| lia| exact OFS16].
               eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO' STK0 OFS0' SPB B63 SP16 OFS16' XPok PBX); [exact OI| exact MU| exact WM| exact MI3| | exact ERRA|].
               - replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia.
                 destruct (stk_carve ctusegs m3 lo (bv_unsigned sp + OFS) 144 ST3 ltac:(lia)) as [ST4 _]. replace (bv_unsigned sp + OFS - Z.of_nat 144) with (bv_unsigned sp + OFS + -144) in ST4 by lia. exact ST4.
               - constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
      split. { eapply lx_pres_trans; [exact LXA|].
               eapply (lx_pres_munch_gen sA OWA (NEW ++ LB)); [exact HEAPA| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
               constructor; [left; cbn; lia|]. constructor; [| constructor]. right. left. split; [cbn; lia| intros a Ha; cbn in Ha; lia]. }
      split; [exact HPIC|]. split; [exact HPPC|]. exact I.
  Qed.

  (* [comment removed for export] *)
  Lemma tlen_after_err : forall (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      sA stA mX mA OWA errvA boA NEW (PIC PPC : Z) (TLCo : option Z) (cpic : list cell) (pp : Z) (jhd : list byte) (vb : byte) (jt : list byte),
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> CHECK_TLEN_STACK <= STK ->
    oinvK (OFS + -144) (STK - 144) sA stA mA OWA errvA boA NEW -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get FX k) ->
    bv_unsigned sp + OFS <= PIC -> PIC + 10 <= bv_unsigned sp -> bv_unsigned sp + OFS <= PPC -> PPC + 8 <= bv_unsigned sp ->
    match TLCo with Some a => PIC + 10 <= a /\ PPC + 8 <= a /\ a + 32 <= bv_unsigned sp /\ a mod 8 = 0 /\ rw_cells ctusegs mA a [C1 vb; CB 31 jt] | None => True end ->
    lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) ([(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)] ++ LIBW_AP) mX mA ->
    rw_cells ctusegs mA PIC cpic -> cells_size cpic = 10%nat -> rw_cells ctusegs mA PPC [C8 (wz pp)] ->
    rw_cells ctusegs mA (bv_unsigned sp + OFS + -144) (CB 40 jhd :: tl_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    Z.land (bv_unsigned x10) 128 <> 0 ->
    implM ctusegs (interp (ap_embed (err_raise RS_tlen_bad_hdr stA))) sA
      (tlen_postR OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW PIC PPC TLCo 0 cpic pp)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz match TLCo with Some a => a | None => 0 end) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FA (Z_to_bv 64 0x112954) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL GLO HF HM PBX SP16 SPB XPok.
    intros until jt. intros LO OFS0 OFS16 STKG OI FRMA FEA PIClo PIChi PPClo PPChi HTLC LXA HPIC SZP HPPC FR B7.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK - 144) by lia. assert (LO' : lo <= bv_unsigned sp + (OFS + -144) - (STK - 144)) by lia.
    assert (OFS0' : OFS + -144 <= 0) by lia. assert (OFS16' : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STA by lia.
    unfold MallocRep.wz in *.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    unfold implM. iprefix.
    step. step. if_cases KB; zc KB; [| exfalso; apply B7; revert KB; rewrite ?unsigned_lit by lia; cbn; lia]. clear KB.
    ihere. to_implM.
    eapply implM_post_evt.
    { replace (bv_unsigned sp + OFS + -144) with (bv_unsigned sp + (OFS + -144)) by lia.
      eapply (tl_raise 0x1129fc RS_tlen_bad_hdr (OFS + -144) (STK - 144)); [left; split; reflexivity| exact LO'| exact OFS0'| exact OFS16'| unfold ERR_SET_ERROR_STACK; lia| exact OI| exact FRMA]. }
    intros r sB msB POB. unfold tl_raise_post in POB.
    destruct POB as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F2 & fc2 & mB & OW2 & errv2 & bo2 & -> & FRM2 & FE2 & OIb & LXb).
    cbv beta. replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LXb |- * by lia.
    pose proof (agree_of_lx_pres _ _ _ _ _ LXb) as AGb.
    assert (CL : forall a, bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp -> lx_client (NEW ++ LB) (bv_unsigned sp + OFS + -144) LIBW_AP a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AGb) in FR; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in HPIC; [| intros a Ha; apply CL; rewrite SZP in Ha; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGb) in HPPC; [| intros a Ha; apply CL; cbn in Ha; lia].
    destruct r as [u stB]. cbn [fst snd] in *. unfold tlen_postR. cbn [fst snd].
    eapply (tlen_ret0 OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F2 fc2) with (vb := vb) (jt := jt);
      [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIb| exact FRM2| intros k Hk; rewrite (FE2 k Hk); apply (FEA k Hk)
      | exact PIClo| exact PIChi| exact PPClo| exact PPChi| | | exact HPIC| exact SZP| exact HPPC| exact FR].
    - destruct TLCo as [TLC|]; [| exact I]. destruct HTLC as (T1 & T2 & T3 & T8 & HT). split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T8|].
      apply (rw_cells_agree _ _ _ _ _ AGb) in HT; [exact HT| intros a Ha; apply CL; cbn in Ha; lia].
    - eapply lx_pres_trans; [exact LXA|]. eapply lx_pres_weaken; [exact LXb| lia| intros b Hb; exact Hb| intros a Ha; apply rin_ivs_app; right; exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma tlen_after_wrong : forall (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 : word)
      sA stA mX mA OWA errvA boA NEW (op len t PIC PPC : Z) (TLCo : option Z) (cpic : list cell) (j0 : list byte) (vb : byte) (jt : list byte),
    let g := get_object d op len in
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> CHECK_TLEN_STACK <= STK ->
    oinvK (OFS + -144) (STK - 144) sA stA mA OWA errvA boA NEW -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get FX k) ->
    bv_unsigned sp + OFS <= PIC -> PIC + 10 <= bv_unsigned sp -> bv_unsigned sp + OFS <= PPC -> PPC + 8 <= bv_unsigned sp ->
    match TLCo with Some a => PIC + 10 <= a /\ PPC + 8 <= a /\ a + 32 <= bv_unsigned sp /\ a mod 8 = 0 /\ rw_cells ctusegs mA a [C1 vb; CB 31 jt] | None => True end ->
    lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) ([(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)] ++ LIBW_AP) mX mA ->
    rw_cells ctusegs mA PIC cpic -> cells_size cpic = 10%nat -> rw_cells ctusegs mA PPC [C8 (wz (D + op))] ->
    rw_cells ctusegs mA (bv_unsigned sp + OFS + -144)
      ([CB 8 j0; C8 (wz 0); C8 (wz (D + go_p g)); C8 (wz (go_len g)); C4 (wz (go_cls g)); C4 (wz (go_tag g))] ++ tl_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    0 < len -> go_err g = None -> 0 <= t < 2 ^ 31 -> (go_tag g <> t \/ go_cls g <> 0) ->
    implM ctusegs (interp (ap_embed (err_raise RS_tlen_wrong_tag stA))) sA
      (tlen_postR OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW PIC PPC TLCo 0 cpic (D + op))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz match TLCo with Some a => a | None => 0 end)
               (wz (go_ret g)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (wz 0) (wz t) x28 x29 x30 x31)
          FA (Z_to_bv 64 0x112954) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL DF GLO HF HM PBX SP16 SPB XPok.
    intros until jt. cbv zeta. intros LO OFS0 OFS16 STKG OI FRMA FEA PIClo PIChi PPClo PPChi HTLC LXA HPIC SZP HPPC FR LEN0 EG TR MIS.
    set (g := get_object d op len) in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK - 144) by lia. assert (LO' : lo <= bv_unsigned sp + (OFS + -144) - (STK - 144)) by lia.
    assert (OFS0' : OFS + -144 <= 0) by lia. assert (OFS16' : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STA by lia.
    pose proof (get_object_bounds d op len ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros; lia) LEN0) as GB. cbv zeta in GB. fold g in GB. rewrite EG in GB.
    destruct GB as (GB1 & GB2 & GB3).
    pose proof (go_ret_cases d op len) as RC. cbv zeta in RC. fold g in RC.
    pose proof (go_cls_cases d op len) as CC. cbv zeta in CC. fold g in CC.
    pose proof (go_tag_range d op len) as TG. cbv zeta in TG. fold g in TG. unfold INT_MAX in TG.
    unfold tl_saved in FR. unfold MallocRep.wz in *.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctusegs mA) as WM.
    (* [comment removed for export] *)
    assert (EXIT : forall (y11 : word) mA', mA' = mA ->
      evt ctusegs (fun ms' => impl ctusegs (at_node ctusegs) (interp (ap_embed (err_raise RS_tlen_wrong_tag stA)) sA)
                    (epost (fun p : () * ap_st bptr * PState => tlen_postR OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW PIC PPC TLCo 0 cpic (D + op) p.1 p.2)) ms')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 match TLCo with Some a => a | None => 0 end)
                 (Z_to_bv 64 (go_ret g)) y11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 0) (Z_to_bv 64 t) x28 x29 x30 x31)
            FA (Z_to_bv 64 0x112a80) fcA None mA' (seg_rom ctusegs))).
    { intros y11 mA' ->.
      step. step. if_true.
      ihere. to_implM.
      eapply implM_post_evt.
      { replace (bv_unsigned sp + OFS + -144) with (bv_unsigned sp + (OFS + -144)) by lia.
        eapply (tl_raise 0x112a90 RS_tlen_wrong_tag (OFS + -144) (STK - 144)); [right; split; reflexivity| exact LO'| exact OFS0'| exact OFS16'| unfold ERR_SET_ERROR_STACK; lia| exact OI| exact FRMA]. }
      intros r sB msB POB. unfold tl_raise_post in POB.
      destruct POB as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F2 & fc2 & mB & OW2 & errv2 & bo2 & -> & FRM2 & FE2 & OIb & LXb).
      cbv beta. replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LXb |- * by lia.
      pose proof (agree_of_lx_pres _ _ _ _ _ LXb) as AGb.
      assert (CL : forall a, bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp -> lx_client (NEW ++ LB) (bv_unsigned sp + OFS + -144) LIBW_AP a).
      { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AGb) in FR; [| intros a Ha; apply CL; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in HPIC; [| intros a Ha; apply CL; rewrite SZP in Ha; cbn in Ha; lia].
      apply (rw_cells_agree _ _ _ _ _ AGb) in HPPC; [| intros a Ha; apply CL; cbn in Ha; lia].
      apply rw_cells_app in FR. destruct FR as [FRH FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
      apply rw_cells_CB_of in FRH. cbn [cells_size csize Nat.add plus] in FRH. join2 FRH FR.
      destruct r as [u stB]. cbn [fst snd] in *. unfold tlen_postR. cbn [fst snd].
      eapply (tlen_ret0 OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F2 fc2) with (vb := vb) (jt := jt);
        [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIb| exact FRM2| intros k Hk; rewrite (FE2 k Hk); apply (FEA k Hk)
        | exact PIClo| exact PIChi| exact PPClo| exact PPChi| | | exact HPIC| exact SZP| exact HPPC| exact FRH].
      - destruct TLCo as [TLC|]; [| exact I]. destruct HTLC as (T1 & T2 & T3 & T8 & HT). split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T8|].
        apply (rw_cells_agree _ _ _ _ _ AGb) in HT; [exact HT| intros a Ha; apply CL; cbn in Ha; lia].
      - eapply lx_pres_trans; [exact LXA|]. eapply lx_pres_weaken; [exact LXb| lia| intros b Hb; exact Hb| intros a Ha; apply rin_ivs_app; right; exact Ha]. }
    cbn [app] in FR. unfold implM. iprefix.
    step. step. if_cases KB; zc KB; [exfalso; apply KB; destruct RC as [->|[->|[->| ->]]]; reflexivity|]. clear KB.
    step. if_cases KX; zc KX; [exfalso; revert KX; rewrite ?signed_small by lia; lia|]. clear KX.
    step. rewrite (sx32_small (go_tag g)) by lia.
    step. if_cases KT; zc KT.
    { (* [comment removed for export] *) apply EXIT. reflexivity. }
    step. rewrite (sx32_small (go_cls g)) by lia.
    step. if_cases KC; zc KC.
    { apply EXIT. reflexivity. }
    exfalso. revert KT KC. rewrite ?unsigned_lit by lia. intros KT KC. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tlen_after_ok : forall (X : Type) (ot : option Z) (KS : @AM bptr X) (Q : X * ap_st bptr -> PState -> machine_state -> Prop) (OFS STK : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FX FA : bvmap 5 word) (fcA : bv 32)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
      sA stA mX mA OWA errvA boA NEW (op len PIC PPC : Z) (TLCo : option Z) (bi bc : byte) (jl j0 : list byte) (vb : byte) (jt : list byte),
    let g := get_object d op len in
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> CHECK_TLEN_STACK <= STK ->
    oinvK (OFS + -144) (STK - 144) sA stA mA OWA errvA boA NEW -> frm0 fcA -> (forall k : reg, bv_unsigned k <> 10 -> reg_get FA k = reg_get FX k) ->
    bv_unsigned sp + OFS <= PIC -> PIC + 10 <= bv_unsigned sp -> bv_unsigned sp + OFS <= PPC -> PPC + 8 <= bv_unsigned sp ->
    (PPC + 8 <= PIC \/ PIC + 10 <= PPC) -> (PIC + 2) mod 8 = 0 -> PPC mod 8 = 0 ->
    match TLCo with Some a => PIC + 10 <= a /\ PPC + 8 <= a /\ a + 32 <= bv_unsigned sp /\ a mod 8 = 0 /\ rw_cells ctusegs mA a [C1 vb; CB 31 jt] | None => True end ->
    lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) ([(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)] ++ LIBW_AP) mX mA ->
    rw_cells ctusegs mA PIC [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctusegs mA PPC [C8 (wz (D + op))] ->
    rw_cells ctusegs mA (bv_unsigned sp + OFS + -144)
      ([CB 8 j0; C8 (wz 0); C8 (wz (D + go_p g)); C8 (wz (go_len g)); C4 (wz (go_cls g)); C4 (wz (go_tag g))] ++ tl_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    0 <= op -> 0 < len -> op + len <= zlength d -> go_err g = None ->
    match ot with Some t => 0 <= t < 2 ^ 31 /\ go_tag g = t /\ go_cls g = 0 | None => True end ->
    (forall st' s' ms',
       tlen_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW PIC PPC TLCo 1
                 [C1 (Z_to_bv 8 (Z.land (go_ret g) 1)); C1 (Z_to_bv 8 (Z.land (go_ret g) 32)); C8 (wz (tlen_plen g op len))] (D + go_p g) st' s' ms' ->
       implM ctusegs (interp (ap_embed (KS st'))) s' Q ms') ->
    implM ctusegs (interp (ap_embed (KS stA))) sA Q
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (wz match TLCo with Some a => a | None => 0 end)
               (wz (go_ret g)) x11 x12 x13 x14 x15 x16 x17 (wz PPC) (wz 0) (wz (D + op)) (wz (PIC + 2)) (wz (PIC + 1)) (wz PIC) (wz len) (wz 0) (wz 0)
               (wz match ot with Some t => t | None => -1 end) x28 x29 x30 x31)
          FA (Z_to_bv 64 0x112954) fcA None mA (seg_rom ctusegs)).
  Proof using B63 CEIL D1 D30 D63 DF GLO PBX SP16 SPB XPok.
    intros until jt. cbv zeta. intros LO OFS0 OFS16 STKG OI FRMA FEA PIClo PIChi PPClo PPChi DJ AL8 AL8P HTLC LXA HPIC HPPC FR OP0 LEN0 OPL EG OT HK.
    set (g := get_object d op len) in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    assert (STK0 : 0 <= STK - 144) by lia. assert (LO' : lo <= bv_unsigned sp + (OFS + -144) - (STK - 144)) by lia.
    assert (OFS0' : OFS + -144 <= 0) by lia. assert (OFS16' : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OI) as (HEAPA & NDA & BND & _).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO' STK0 OFS0' SPB B63 _ _ _ _ _ _ _ OI) as (_ & _ & _ & STA & _ & _ & ERRA & MIA & _).
    unfold LX_ERRNO, RATP in ERRA. change (3355176 - 164) with 3355012 in ERRA.
    replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STA by lia.
    pose proof (get_object_bounds d op len ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros; lia) LEN0) as GB. cbv zeta in GB. fold g in GB. rewrite EG in GB.
    destruct GB as (GB1 & GB2 & GB3).
    pose proof (go_ret_cases d op len) as RC. cbv zeta in RC. fold g in RC.
    pose proof (go_cls_cases d op len) as CC. cbv zeta in CC. fold g in CC.
    pose proof (go_tag_range d op len) as TG. cbv zeta in TG. fold g in TG. unfold INT_MAX in TG.
    unfold tl_saved in FR. cbn [app] in FR. unfold MallocRep.wz in *.
    cut_hd HPIC HINF (PIC + 1). cut_hd HPIC HCST (PIC + 2). rename HPIC into HOLEN.
    pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (PIC, PIC + 10); (PPC, PPC + 8);
                            (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)]%Z mA) as MU.
    pose proof (wmono_refl ctusegs mA) as WM.
    (* [comment removed for export] *)
    assert (FIN : forall (y11 : word) mB (vb' : byte),
      munch [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (PIC, PIC + 10); (PPC, PPC + 8);
             (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)]%Z mA mB -> wmono ctusegs mA mB -> mem_inv ctusegs mB ->
      stk ctusegs mB lo (bv_unsigned sp + OFS + -144) -> rw_cells ctusegs mB 3355012 [C4 errvA] ->
      rw_cells ctusegs mB PIC [C1 bi] -> rw_cells ctusegs mB (PIC + 1) [C1 bc] -> rw_cells ctusegs mB (PIC + 2) [CB 8 jl] -> rw_cells ctusegs mB PPC [C8 (Z_to_bv 64 (D + op))] ->
      match TLCo with Some a => rw_cells ctusegs mB a [C1 vb'; CB 31 jt] | None => True end ->
      rw_cells ctusegs mB (bv_unsigned sp + OFS + -144)
        [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + go_p g)); C8 (Z_to_bv 64 (go_len g)); C4 (Z_to_bv 64 (go_cls g)); C4 (Z_to_bv 64 (go_tag g));
         C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt ctusegs (fun ms' => impl ctusegs (at_node ctusegs) (interp (ap_embed (KS stA)) sA) (epost (fun p : X * ap_st bptr * PState => Q p.1 p.2)) ms')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 match TLCo with Some a => a | None => 0 end)
                 (Z_to_bv 64 (go_ret g)) y11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 PPC) (Z_to_bv 64 0) (Z_to_bv 64 (D + op)) (Z_to_bv 64 (PIC + 2)) (Z_to_bv 64 (PIC + 1)) (Z_to_bv 64 PIC) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 match ot with Some t => t | None => -1 end) x28 x29 x30 x31)
            FA (Z_to_bv 64 0x112980) fcA None mB (seg_rom ctusegs))).
    { intros y11 mB vb' MU' WM' MIB STB ERRB HINF' HCST' HOLEN' HPPC' HTLC' FR'.
      clear MU WM HINF HCST HOLEN HPPC FR. rename MU' into MU. rename WM' into WM.
      (* [comment removed for export] *)
      assert (FIN2 : forall (y12 y13 y14 : word) mC,
        munch [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (PIC, PIC + 10); (PPC, PPC + 8);
               (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)]%Z mA mC -> wmono ctusegs mA mC -> mem_inv ctusegs mC ->
        stk ctusegs mC lo (bv_unsigned sp + OFS + -144) -> rw_cells ctusegs mC 3355012 [C4 errvA] ->
        rw_cells ctusegs mC PIC [C1 bi] -> rw_cells ctusegs mC (PIC + 1) [C1 bc] -> rw_cells ctusegs mC (PIC + 2) [CB 8 jl] -> rw_cells ctusegs mC PPC [C8 (Z_to_bv 64 (D + op))] ->
        match TLCo with Some a => rw_cells ctusegs mC a [C1 vb'; CB 31 jt] | None => True end ->
        rw_cells ctusegs mC (bv_unsigned sp + OFS + -144)
          [CB 8 j0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (D + go_p g)); C8 (Z_to_bv 64 (tlen_plen g op len)); C4 (Z_to_bv 64 (go_cls g)); C4 (Z_to_bv 64 (go_tag g));
           C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        evt ctusegs (fun ms' => impl ctusegs (at_node ctusegs) (interp (ap_embed (KS stA)) sA) (epost (fun p : X * ap_st bptr * PState => Q p.1 p.2)) ms')
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 match TLCo with Some a => a | None => 0 end)
                   (Z_to_bv 64 (go_ret g)) (Z_to_bv 64 (Z.land (go_ret g) 1)) y12 y13 y14 x15 x16 x17 (Z_to_bv 64 PPC) (Z_to_bv 64 0) (Z_to_bv 64 (D + op)) (Z_to_bv 64 (PIC + 2)) (Z_to_bv 64 (PIC + 1)) (Z_to_bv 64 PIC) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0)
                   (Z_to_bv 64 match ot with Some t => t | None => -1 end) x28 x29 x30 x31)
              FA (Z_to_bv 64 0x1129a4) fcA None mC (seg_rom ctusegs))).
      { intros y12 y13 y14 mC MU2 WM2 MIC STC ERRC HINF2 HCST2 HOLEN2 HPPC2 HTLC2 FR2. move MU after MU2. move WM after WM2. clear MU WM MIB STB ERRB HINF' HCST' HOLEN' HPPC' HTLC' FR'.
        rename MU2 into MU. rename WM2 into WM.
        destruct TLCo as [TLC|].
        - destruct HTLC as (T1 & T2 & T3 & _). rename HTLC2 into HT2.
        step. if_cases KP; zc KP; [exfalso; revert KP; rewrite ?unsigned_lit by lia; lia|]. clear KP.
        step. rewrite le1_lit. mem_after_store.
        step. if_cases KP; zc KP; [exfalso; revert KP; rewrite ?unsigned_lit by lia; lia|]. clear KP.
        step. step. rewrite le1_lit. mem_after_store.
        step. if_cases KP; zc KP; [exfalso; revert KP; rewrite ?unsigned_lit by lia; lia|]. clear KP.
        step. step.
        step. if_true. step. if_true.
        step. step. step. step.
        do 14 step.
        match goal with H : stk ctusegs _ lo (bv_unsigned sp + OFS + -144) |- _ => release_frame FR2 H (bv_unsigned sp + OFS) end. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
        ihere. apply HK. unfold tlen_post.
        join2 HINF2 HCST2. join2 HINF2 HOLEN2.
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FA, fcA, m3, OWA, errvA, boA.
        split; [reflexivity|]. split; [exact FRMA|]. split; [exact FEA|].
        split. { eapply (oinv_reframe sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) OFS STK); [| exact SPB| exact SP16| exact ST3| lia| lia| lia| exact OFS16].
                 eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO' STK0 OFS0' SPB B63 SP16 OFS16' XPok PBX); [exact OI| exact MU| exact WM| exact MI3| | exact ERRC|].
                 - replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia.
                   destruct (stk_carve ctusegs m3 lo (bv_unsigned sp + OFS) 144 ST3 ltac:(lia)) as [ST4 _]. replace (bv_unsigned sp + OFS - Z.of_nat 144) with (bv_unsigned sp + OFS + -144) in ST4 by lia. exact ST4.
                 - constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
        split. { eapply lx_pres_trans; [exact LXA|].
                 eapply (lx_pres_munch_gen sA OWA (NEW ++ LB)); [exact HEAPA| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
                 constructor; [left; cbn; lia|].
                 constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; left; lia]|].
                 constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; right; left; lia]|].
                 constructor; [| constructor].
                 right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; first [lia | right; right; left; lia]]. }
        rewrite (unsigned_lit (go_ret g)) in HINF2 by (destruct RC as [->|[->|[->| ->]]]; lia).
        split; [exact HINF2|]. split; [exact HPPC2|].
        exists vb', jt. exact HT2.
        - clear HTLC2.
        step. if_cases KP; zc KP; [exfalso; revert KP; rewrite ?unsigned_lit by lia; lia|]. clear KP.
        step. rewrite le1_lit. mem_after_store.
        step. if_cases KP; zc KP; [exfalso; revert KP; rewrite ?unsigned_lit by lia; lia|]. clear KP.
        step. step. rewrite le1_lit. mem_after_store.
        step. if_cases KP; zc KP; [exfalso; revert KP; rewrite ?unsigned_lit by lia; lia|]. clear KP.
        step. step.
        step. if_true. step. if_true.
        step. step. step. step.
        do 14 step.
        match goal with H : stk ctusegs _ lo (bv_unsigned sp + OFS + -144) |- _ => release_frame FR2 H (bv_unsigned sp + OFS) end. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
        match goal with H : stk ctusegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
        ihere. apply HK. unfold tlen_post.
        join2 HINF2 HCST2. join2 HINF2 HOLEN2.
        eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, FA, fcA, m3, OWA, errvA, boA.
        split; [reflexivity|]. split; [exact FRMA|]. split; [exact FEA|].
        split. { eapply (oinv_reframe sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) OFS STK); [| exact SPB| exact SP16| exact ST3| lia| lia| lia| exact OFS16].
                 eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO' STK0 OFS0' SPB B63 SP16 OFS16' XPok PBX); [exact OI| exact MU| exact WM| exact MI3| | exact ERRC|].
                 - replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia.
                   destruct (stk_carve ctusegs m3 lo (bv_unsigned sp + OFS) 144 ST3 ltac:(lia)) as [ST4 _]. replace (bv_unsigned sp + OFS - Z.of_nat 144) with (bv_unsigned sp + OFS + -144) in ST4 by lia. exact ST4.
                 - constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
        split. { eapply lx_pres_trans; [exact LXA|].
                 eapply (lx_pres_munch_gen sA OWA (NEW ++ LB)); [exact HEAPA| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU| exact WM|].
                 constructor; [left; cbn; lia|].
                 constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; left; lia]|].
                 constructor; [right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; right; left; lia]|].
                 constructor; [| constructor].
                 right; left; split; [cbn; lia| intros a Ha; cbn in Ha; cbn; first [lia | right; right; left; lia]]. }
        rewrite (unsigned_lit (go_ret g)) in HINF2 by (destruct RC as [->|[->|[->| ->]]]; lia).
        split; [exact HINF2|]. split; [exact HPPC2|].
        exact I. }
      assert (RB : 0 <= go_ret g < 64) by (destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER; lia).
      destruct TLCo as [TLC|].
      + destruct HTLC as (T1 & T2 & T3 & _). rename HTLC' into HT1.
        step. setreg 11%Z (Z_to_bv 64 (Z.land (go_ret g) 1)) ltac:(rewrite (unsigned_lit (go_ret g)) by lia; reflexivity).
        step. if_cases KI; zc KI.
        * (* [comment removed for export] *)
          assert (EPL : tlen_plen g op len = go_len g).
          { unfold tlen_plen. destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER in KI |- *; first [reflexivity| discriminate KI]. }
          rewrite <- EPL in FR'.
          eapply FIN2; [exact MU| exact WM| assumption| assumption| exact ERRB| exact HINF'| exact HCST'| exact HOLEN'| exact HPPC'| exact HT1| exact FR'].
        * (* [comment removed for export] *)
          step. step. step.
          assert (EPL : tlen_plen g op len = len - (go_p g - op)).
          { unfold tlen_plen. destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER in KI |- *; first [reflexivity| exfalso; apply KI; reflexivity]. }
          replace (Z_to_bv 64 (len + - (D + go_p g + - (D + op)))) with (Z_to_bv 64 (tlen_plen g op len)) in FR'
            by (rewrite EPL; f_equal; lia).
          eapply FIN2; [exact MU| exact WM| assumption| assumption| exact ERRB| exact HINF'| exact HCST'| exact HOLEN'| exact HPPC'| exact HT1| exact FR'].
      + clear HTLC'.
        step. setreg 11%Z (Z_to_bv 64 (Z.land (go_ret g) 1)) ltac:(rewrite (unsigned_lit (go_ret g)) by lia; reflexivity).
        step. if_cases KI; zc KI.
        * (* [comment removed for export] *)
          assert (EPL : tlen_plen g op len = go_len g).
          { unfold tlen_plen. destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER in KI |- *; first [reflexivity| discriminate KI]. }
          rewrite <- EPL in FR'.
          eapply FIN2; [exact MU| exact WM| assumption| assumption| exact ERRB| exact HINF'| exact HCST'| exact HOLEN'| exact HPPC'| exact I| exact FR'].
        * (* [comment removed for export] *)
          step. step. step.
          assert (EPL : tlen_plen g op len = len - (go_p g - op)).
          { unfold tlen_plen. destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER in KI |- *; first [reflexivity| exfalso; apply KI; reflexivity]. }
          replace (Z_to_bv 64 (len + - (D + go_p g + - (D + op)))) with (Z_to_bv 64 (tlen_plen g op len)) in FR'
            by (rewrite EPL; f_equal; lia).
          eapply FIN2; [exact MU| exact WM| assumption| assumption| exact ERRB| exact HINF'| exact HCST'| exact HOLEN'| exact HPPC'| exact I| exact FR'].
      }
    unfold implM. iprefix.
    step. step. if_cases KB; zc KB; [exfalso; apply KB; destruct RC as [->|[->|[->| ->]]]; reflexivity|]. clear KB.
    step. if_cases KX; zc KX.
    - (* [comment removed for export] *)
      destruct ot as [t|]; [exfalso; destruct OT as (TR & _); revert KX; rewrite land_ones64_small by lia; lia|].
      destruct TLCo as [TLC|]; [destruct HTLC as (T1 & T2 & T3 & T8 & HT)|].
      + eapply (FIN _ _ vb); [exact MU| exact WM| assumption| assumption| exact ERRA| exact HINF| exact HCST| exact HOLEN| exact HPPC| exact HT| exact FR].
      + eapply (FIN _ _ vb); [exact MU| exact WM| assumption| assumption| exact ERRA| exact HINF| exact HCST| exact HOLEN| exact HPPC| exact I| exact FR].
    - destruct ot as [t|].
      2: { exfalso. revert KX. rewrite Z.land_m1_l. lia. }
      destruct OT as (TR & ETG & ECL).
      step. rewrite (sx32_small (go_tag g)) by lia.
      step. if_cases KT; zc KT; [exfalso; revert KT; rewrite ?unsigned_lit by lia; lia|]. clear KT.
      step. rewrite (sx32_small (go_cls g)) by lia.
      step. if_cases KC; zc KC; [exfalso; revert KC; rewrite ?unsigned_lit by lia; lia|]. clear KC.
      destruct TLCo as [TLC|].
      + destruct HTLC as (T1 & T2 & T3 & T8 & HT). cut_hd HT HTV (TLC + 1).
        step. if_cases K9; zc K9; [exfalso; revert K9; rewrite ?unsigned_lit by lia; lia|]. clear K9.
        step. join2 HTV HT.
        eapply (FIN _ _ (Z_to_bv 8 0)); [exact MU| exact WM| assumption| assumption| exact ERRA| exact HINF| exact HCST| exact HOLEN| exact HPPC| exact HTV| exact FR].
      + step. if_true.
        eapply (FIN _ _ vb); [exact MU| exact WM| assumption| assumption| exact ERRA| exact HINF| exact HCST| exact HOLEN| exact HPPC| exact I| exact FR].
  Qed.

  Lemma check_tlen_gen : forall (X : Type) (ot : option Z) (KE KW KS : @AM bptr X) (Q : X * ap_st bptr -> PState -> machine_state -> Prop)
      (OFS STK : Z)
      (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      sX stX mX OWX errvX boX NEW (op len PIC PPC : Z) (TLCo : option Z) (bi bc : byte) (jl j31 : list byte),
    let g := get_object d op len in
    lo <= bv_unsigned sp + OFS - STK -> OFS <= 0 -> OFS mod 16 = 0 -> CHECK_TLEN_STACK <= STK ->
    oinvK OFS STK sX stX mX OWX errvX boX NEW -> frm0 fcX ->
    0 <= op -> 0 < len -> op + len <= zlength d ->
    match ot with Some t => 0 <= t < 2 ^ 31 | None => True end ->
    (* [comment removed for export] *)
    bv_unsigned sp + OFS <= PIC -> PIC + 10 <= bv_unsigned sp -> bv_unsigned sp + OFS <= PPC -> PPC + 8 <= bv_unsigned sp ->
    (PPC + 8 <= PIC \/ PIC + 10 <= PPC) -> (PIC + 2) mod 8 = 0 -> PPC mod 8 = 0 ->
    match TLCo with Some a => PIC + 10 <= a /\ PPC + 8 <= a /\ a + 32 <= bv_unsigned sp /\ a mod 8 = 0 /\ rw_cells ctusegs mX a (tlc_in j31) | None => True end ->
    rw_cells ctusegs mX PIC [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctusegs mX PPC [C8 (wz (D + op))] ->
    (* [comment removed for export] *)
    (forall e st' s' ms' bi' bc' jl',
       go_err g = Some e ->
       tlen_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW PIC PPC TLCo 0 [C1 bi'; C1 bc'; CB 8 jl'] (D + op) st' s' ms' ->
       implM ctusegs (interp (ap_embed (KE st'))) s' Q ms') ->
    (* [comment removed for export] *)
    (forall t st' s' ms' bi' bc' jl',
       ot = Some t -> go_err g = None -> (go_tag g <> t \/ go_cls g <> 0) ->
       tlen_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW PIC PPC TLCo 0 [C1 bi'; C1 bc'; CB 8 jl'] (D + op) st' s' ms' ->
       implM ctusegs (interp (ap_embed (KW st'))) s' Q ms') ->
    (* [comment removed for export] *)
    (forall st' s' ms',
       go_err g = None -> match ot with Some t => go_tag g = t /\ go_cls g = 0 | None => True end ->
       tlen_post OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX mX NEW PIC PPC TLCo 1
                 [C1 (Z_to_bv 8 (Z.land (go_ret g) 1)); C1 (Z_to_bv 8 (Z.land (go_ret g) 32)); C8 (wz (tlen_plen g op len))] (D + go_p g) st' s' ms' ->
       implM ctusegs (interp (ap_embed (KS st'))) s' Q ms') ->
    implM ctusegs (interp (ap_embed (tlen_tree g ot KE KW KS stX))) sX Q
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz RATP) t0 t1 t2 s0 s1
                   (wz (PIC + 2)) (wz 0) (wz 0) (wz PIC) (wz (PIC + 1)) (wz PPC) (wz len) (wz match ot with Some t => t | None => -1 end)
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 0) (wz 0) (wz match TLCo with Some a => a | None => 0 end) t6)
              FX (wz CHECK_TLEN) fcX None mX (seg_rom ctusegs)).
  Proof using B63 CEIL D1 D30 D63 DF GLO HF HGO HM PBX SP16 SPB XPok.
    intros until j31. cbv zeta. intros LO OFS0 OFS16 STKG OI FRMX OP0 LEN0 OPL OT PIClo PIChi PPClo PPChi DJ AL8 AL8P HTLC HPIC HPPC KE_ KW_ KS_.
    set (g := get_object d op len) in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (STK0 : 0 <= STK) by (unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG; lia).
    pose proof (ESP sp lo B OFS STK GLO LO STK0 OFS0 SPB B63) as ESP.
    pose proof (oinv_facts sp m s LB E lo B canary K d D XP OFS STK _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & DJL & DJO).
    pose proof (oinv_call sp m s LB E lo B canary K d D XP OFS STK GLO LO STK0 OFS0 SPB B63 _ _ _ _ _ _ _ OI) as (_ & AUXX & SPBX & STX & _ & _ & ERRX & MIX & CSX & ASX).
    pose proof OI as (PREX & LXX & KO & KI & KP & SO & FA & HB).
    unfold LX_ERRNO, RATP in ERRX. change (3355176 - 164) with 3355012 in ERRX. clear HB.
    unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK in STKG.
    unfold CHECK_TLEN, MallocRep.wz in *.
    pose proof (get_object_bounds d op len ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros; lia) LEN0) as GB. cbv zeta in GB. fold g in GB.
    assert (E144 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) = bv_unsigned sp + OFS + -144) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z mX) as MU. pose proof (wmono_refl ctusegs mX) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 144%nat STX. do 15 step.
    step. step. step.
    step. step. step. step. if_cases KL; zc KL; [exfalso; apply andb_false_iff in KL; destruct KL as [KL|KL]; apply Z.ltb_ge in KL; lia|]. clear KL0 KL1.
    do 5 step. step.
    name_mem m1.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: CB 16 ?j :: ?rest) =>
      change (rw_cells ctusegs m1 (bv_unsigned sp + OFS + -144) ([c0] ++ [c1; c2] ++ [CB 16 j] ++ rest)) in FR end.
    apply rw_cells_app in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FRA FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FRX FRS]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRS.
    replace (bv_unsigned sp + OFS + -144 + 8) with (bv_unsigned sp + OFS + -136) in FRA by lia.
    replace (bv_unsigned sp + OFS + -144 + 8 + 16) with (bv_unsigned sp + OFS + -120) in FRX by lia.
    replace (bv_unsigned sp + OFS + -144 + 8 + 16 + 16) with (bv_unsigned sp + OFS + -104) in FRS by lia.
    cut_hd FRA FRO (bv_unsigned sp + OFS + -128). rename FRA into FRP.
    lazymatch type of FRX with rw_cells _ _ _ [CB 16 ?jj] => set (jx := jj) in FRX; clearbody jx end.
    assert (FRX' : rw_cells ctusegs m1 (bv_unsigned sp + OFS + -120) [CB 8 (firstn 8 jx); CB 4 (firstn 4 (skipn 8 jx)); CB 4 (skipn 12 jx)]).
    { pose proof FRX as [[Wf _] _]. cbn in Wf. destruct Wf as [L16 _].
      eapply rw_cells_recast; [exact FRX| cbn; rewrite !length_firstn, !length_skipn; repeat split; first [lia | exact I]| | cbn; lia].
      cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      transitivity (firstn 8 jx ++ skipn 8 jx); [| apply firstn_skipn]. f_equal.
      transitivity (firstn 4 (skipn 8 jx) ++ skipn 4 (skipn 8 jx)); [| apply firstn_skipn]. f_equal. rewrite skipn_skipn. reflexivity. }
    clear FRX. cut_hd FRX' FRL (bv_unsigned sp + OFS + -112). cut_hd FRX' FRC (bv_unsigned sp + OFS + -108). rename FRX' into FRT.
    assert (STK1 : 0 <= STK - 144) by lia. assert (LO1 : lo <= bv_unsigned sp + (OFS + -144) - (STK - 144)) by lia.
    assert (OFS1 : OFS + -144 <= 0) by lia. assert (OFS161 : (OFS + -144) mod 16 = 0) by (rewrite <- Zplus_mod_idemp_l, OFS16; reflexivity).
    assert (GC : go_cells_ok (bv_unsigned sp + (OFS + -144)) (bv_unsigned sp + OFS + -128) (bv_unsigned sp + OFS + -120) (bv_unsigned sp + OFS + -108) (bv_unsigned sp + OFS + -112)) by (unfold go_cells_ok; lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (CALL : forall mc (j0 : list cell),
      munch [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z mX mc -> wmono ctusegs mX mc -> mem_inv ctusegs mc -> stk ctusegs mc lo (bv_unsigned sp + OFS + -144) ->
      rw_cells ctusegs mc 3355012 [C4 errvX] ->
      rw_cells ctusegs mc (bv_unsigned sp + OFS + -144) j0 -> cells_size j0 = 8%nat ->
      rw_cells ctusegs mc (bv_unsigned sp + OFS + -136) [C8 (Z_to_bv 64 0)] -> rw_cells ctusegs mc (bv_unsigned sp + OFS + -128) [C8 (Z_to_bv 64 (D + op))] ->
      rw_cells ctusegs mc (bv_unsigned sp + OFS + -120) [CB 8 (firstn 8 jx)] -> rw_cells ctusegs mc (bv_unsigned sp + OFS + -112) [CB 4 (firstn 4 (skipn 8 jx))] ->
      rw_cells ctusegs mc (bv_unsigned sp + OFS + -108) [CB 4 (skipn 12 jx)] ->
      rw_cells ctusegs mc (bv_unsigned sp + OFS + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ctusegs mc PIC [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctusegs mc PPC [C8 (Z_to_bv 64 (D + op))] ->
      match TLCo with Some a => rw_cells ctusegs mc a (tlc_in j31) | None => True end ->
      oinvK (OFS + -144) (STK - 144) sX stX mc OWX errvX boX NEW /\ lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) ([(PIC, PIC + 10); (PPC, PPC + 8); (match TLCo with Some a => a | None => PIC end, match TLCo with Some a => a + 32 | None => PIC end)] ++ LIBW_AP) mX mc).
    { intros mc j0 MU1 WM1 MI1 ST1 ERR1 G0 SZ0 G1 G2 G3 G4 G5 G6 GPIC GPPC GTLC.
      assert (STF : stk ctusegs mc lo (bv_unsigned sp + OFS)).
      { stk_join ST1 G0 STa (bv_unsigned sp + OFS + -136). stk_join STa G1 STb (bv_unsigned sp + OFS + -128). stk_join STb G2 STc (bv_unsigned sp + OFS + -120).
        stk_join STc G3 STd (bv_unsigned sp + OFS + -112). stk_join STd G4 STe (bv_unsigned sp + OFS + -108). stk_join STe G5 STf (bv_unsigned sp + OFS + -104).
        stk_join STf G6 STg (bv_unsigned sp + OFS). exact STg. }
      assert (OI1 : oinvK OFS STK sX stX mc OWX errvX boX NEW).
      { eapply (oinv_munch sp m s LB E lo B canary K d D XP OFS STK CEIL GLO LO STK0 OFS0 SPB B63 SP16 OFS16 XPok PBX); [exact OI| exact MU1| exact WM1| exact MI1| exact STF| exact ERR1|].
        constructor; [left; cbn; lia| constructor]. }
      split.
      - eapply (oinv_reframe sp m s LB E lo B canary K d D XP OFS STK); [exact OI1| exact SPB| exact SP16| replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia; exact ST1| lia| lia| lia| exact OFS161].
      - eapply (lx_pres_munch_gen sX OWX (NEW ++ LB)); [exact HEAPX| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU1| exact WM1|].
        constructor; [left; cbn; lia| constructor]. }
    (* [comment removed for export] *)
    assert (CL : forall a, (bv_unsigned sp + OFS + -104 <= a < bv_unsigned sp \/ bv_unsigned sp + OFS + -144 <= a < bv_unsigned sp + OFS + -128) ->
                 lx_client (NEW ++ LB) (bv_unsigned sp + OFS + -144)
                   ([(bv_unsigned sp + OFS + -128, bv_unsigned sp + OFS + -128 + 8); (bv_unsigned sp + OFS + -120, bv_unsigned sp + OFS + -120 + 8);
                     (bv_unsigned sp + OFS + -108, bv_unsigned sp + OFS + -108 + 4); (bv_unsigned sp + OFS + -112, bv_unsigned sp + OFS + -112 + 4)] ++ LIBW_AP) a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
    destruct TLCo as [TLC|].
    - (* [comment removed for export] *)
      destruct HTLC as (T1 & T2 & T3 & T8 & HT). unfold tlc_in in HT. xport HT MU WM. cut_hd HT HTV (TLC + 1). setreg 9%Z (Z_to_bv 64 TLC) ltac:(reflexivity).
      step. if_cases K9; zc K9; [exfalso; revert K9; rewrite ?unsigned_lit by lia; lia|]. clear K9.
      step. step. step. if_cases KV; zc KV; [| exfalso; apply KV; reflexivity]. clear KV.
      step. step. step. step. step. step.
      name_mem mc.
      match goal with H : stk ctusegs mc lo _ |- _ => rename H into STc end. match goal with H : mem_inv ctusegs mc |- _ => rename H into MIc end.
      join2 HTV HT.
      destruct (CALL mc _ MU WM MIc STc ERRX FR0 eq_refl FRO FRP FRL FRC FRT FRS HPIC HPPC HTV) as [OIc LXc].
      ihere. unfold tlen_tree. destruct (go_err g) as [e|] eqn:EG.
      + (* [comment removed for export] *)
        unfold tlen_fail. to_implM.
        eapply implM_abind.
        { eapply implM_abind.
          { replace (match e with GeHdr => err_raise RS_hdr_too_long | GeTooLong => err_raise RS_too_long | GeTooSmall => aunr end) with (go_eff g) by (unfold go_eff; rewrite EG; reflexivity).
            replace (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -144))) by (f_equal; lia).
            eapply (go_call (OFS + -144) (STK - 144)); [exact LO1| exact OFS1| exact OFS161| unfold GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIc| exact FRMX| exact OP0| exact LEN0| exact OPL| exact GC| lia| lia| lia| lia
              | exact FRP| exact FRL| exact FRT| exact FRC]. }
          intros r1 sr ms1 PO1. unfold go_post in PO1. fold g in PO1. rewrite EG in PO1.
          destruct PO1 as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mr & OW1 & errv1 & bo1 & jl' & j2' & j3'
                           & -> & FRM1 & FE1 & OI1 & LX1 & HPP1 & RES1).
          replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LX1 |- * by lia.
          replace (ret_pc (Z_to_bv 64 0x1128d8)) with (Z_to_bv 64 0x1128d8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          pose proof (agree_of_lx_pres _ _ _ _ _ LX1) as AG1.
          apply (rw_cells_agree _ _ _ _ _ AG1) in FR0; [| intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG1) in FRO; [| intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG1) in FRS; [| intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG1) in HPIC; [| intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG1) in HPPC; [| intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG1) in HTV; [| intros a Ha; apply CL; cbn in Ha; lia].
          pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO1 STK1 OFS1 SPB B63 _ _ _ _ _ _ _ OI1) as (_ & _ & _ & STr & _ & _ & ERRr & MIr & _).
          unfold LX_ERRNO, RATP in ERRr. change (3355176 - 164) with 3355012 in ERRr. replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STr by lia.
          clear MU WM. pose proof (munch_refl [(TLC, TLC + 32)] mr) as MU. pose proof (wmono_refl ctusegs mr) as WM.
          cut_hd HTV HTV0 (TLC + 1). rename HTV into HT. rename HTV0 into HTV.
          pose proof (go_ret_cases d op len) as RC. cbv zeta in RC. fold g in RC.
          assert (LXr : forall m2, munch [(TLC, TLC + 32)]%Z mr m2 -> wmono ctusegs mr m2 ->
                    lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) ([(PIC, PIC + 10); (PPC, PPC + 8); (TLC, TLC + 32)] ++ LIBW_AP) mX m2).
          { intros m2 MU2 WM2. eapply lx_pres_trans; [exact LXc|]. eapply lx_pres_trans.
            - eapply (lx_pres_up _ _ _ _ _ _ _ lo); [exact LX1| lia| intros q A n Hq; pose proof (BND q A n ltac:(apply in_app_iff; right; exact Hq)); lia| lia|].
              intros a Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [right; cbn in Ha; lia| left; apply rin_ivs_app; right; exact Ha].
            - pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OI1) as (HEAP1 & _).
              eapply (lx_pres_munch_gen sr OW1 (NEW ++ LB)); [exact HEAP1| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU2| exact WM2|].
              constructor; [| constructor]. right. left. split; [cbn; lia|]. intros a Ha. cbn in Ha. cbn. right. right. left. lia. }
          (* [comment removed for export] *)
          assert (B7 : Z.land (bv_unsigned p0) 128 <> 0 /\ Z.land (bv_unsigned p0) 129 <> 0).
          { destruct e; destruct RES1 as (-> & _); unfold MallocRep.wz.
            - rewrite unsigned_lit by lia. split; cbv; discriminate.
            - destruct RC as [E0|[E0|[E0|E0]]]; rewrite E0; split; cbv; discriminate.
            - rewrite unsigned_lit by lia. split; cbv; discriminate. }
          destruct B7 as [B7 B81].
          assert (CELLS : exists cl ct cc, rw_cells ctusegs mr (bv_unsigned sp + OFS + -120) [cl] /\ csize cl = 8%nat
                           /\ rw_cells ctusegs mr (bv_unsigned sp + OFS + -108) [ct] /\ csize ct = 4%nat /\ rw_cells ctusegs mr (bv_unsigned sp + OFS + -112) [cc] /\ csize cc = 4%nat
                           /\ match cl with CB _ _ | C8 _ => True | _ => False end /\ match ct with CB _ _ | C4 _ => True | _ => False end /\ match cc with CB _ _ | C4 _ => True | _ => False end).
          { destruct e; destruct RES1 as (_ & H1 & H2 & H3); eexists _, _, _;
              (split; [exact H1|]; split; [reflexivity|]; split; [exact H2|]; split; [reflexivity|]; split; [exact H3|]; split; [reflexivity|]; repeat split; exact I). }
          clear RES1. destruct CELLS as (cl & ct & cc & HPL1 & SZL & HPT1 & SZT & HPC1 & SZC & SH1 & SH2 & SH3).
          destruct cl; try contradiction; destruct ct; try contradiction; destruct cc; try contradiction; cbn in SZL, SZT, SZC; subst;
            (unfold implM; iprefix;
             step; step; step; step; step; step; step; step; step; zstep; zstep; step; step;
             step; if_cases K15; zc K15; [clear K15| exfalso; apply B81; revert K15; rewrite ?unsigned_lit by lia; intros K15; exact K15];
             ihere; to_implM;
             join2 FR0 FRO; join2 FR0 HPP1; join2 FR0 HPL1; join2 FR0 HPC1; join2 FR0 HPT1;
             apply rw_cells_CB_of in FR0; cbn [cells_size csize Nat.add plus] in FR0; join2 FR0 FRS;
             apply rw_cells_CB_of in HT; cbn [cells_size csize Nat.add plus] in HT; join2 HTV HT;
             lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end;
             eapply (tlen_after_err OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F1 fc1) with (TLCo := Some TLC);
               [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| | exact FRM1| exact FE1
               | exact PIClo| exact PIChi| exact PPClo| exact PPChi| split; [exact T1| split; [exact T2| split; [exact T3| split; [exact T8| exact HTV]]]]| apply LXr; [exact MU| exact WM]
               | exact HPIC| reflexivity| exact HPPC| exact FR0| exact B7];
             eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO1 STK1 OFS1 SPB B63 SP16 OFS161 XPok PBX); [exact OI1| exact MU| exact WM| assumption| | exact ERRr|];
             [replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia; assumption
             | constructor; [left; cbn; lia| constructor]]). }
        intros r2 sr2 ms2 PO2. unfold tlen_postR in PO2. cbn [fst snd] in PO2. eapply (KE_ e); [reflexivity| exact PO2].
      + (* [comment removed for export] *)
        lazymatch goal with |- impl _ _ (interp (ap_embed (?R stX)) _) _ _ => set (REST := R) end.
        replace (REST stX) with (abind (go_eff g) (fun _ : unit => REST) stX) by (unfold go_eff; rewrite EG; reflexivity).
        to_implM. eapply implM_abind.
        { replace (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -144))) by (f_equal; lia).
          eapply (go_call (OFS + -144) (STK - 144)); [exact LO1| exact OFS1| exact OFS161| unfold GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIc| exact FRMX| exact OP0| exact LEN0| exact OPL| exact GC| lia| lia| lia| lia
            | exact FRP| exact FRL| exact FRT| exact FRC]. }
        intros r1 sr ms1 PO1. unfold go_post in PO1. fold g in PO1. rewrite EG in PO1.
        destruct PO1 as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mr & OW1 & errv1 & bo1 & jl' & j2' & j3'
                         & -> & FRM1 & FE1 & OI1 & LX1 & HPP1 & -> & HPL1 & HPT1 & HPC1).
        replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LX1 |- * by lia.
        replace (ret_pc (Z_to_bv 64 0x1128d8)) with (Z_to_bv 64 0x1128d8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_lx_pres _ _ _ _ _ LX1) as AG1.
        apply (rw_cells_agree _ _ _ _ _ AG1) in FR0; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG1) in FRO; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG1) in FRS; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG1) in HPIC; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG1) in HPPC; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG1) in HTV; [| intros a Ha; apply CL; cbn in Ha; lia].
        pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO1 STK1 OFS1 SPB B63 _ _ _ _ _ _ _ OI1) as (_ & _ & _ & STr & _ & _ & ERRr & MIr & _).
        unfold LX_ERRNO, RATP in ERRr. change (3355176 - 164) with 3355012 in ERRr. replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STr by lia.
        clear MU WM. pose proof (munch_refl [(TLC, TLC + 32)] mr) as MU. pose proof (wmono_refl ctusegs mr) as WM.
        cut_hd HTV HTV0 (TLC + 1). rename HTV into HT. rename HTV0 into HTV.
        pose proof (go_ret_cases d op len) as RC. cbv zeta in RC. fold g in RC.
        pose proof (go_cls_cases d op len) as CC. cbv zeta in CC. fold g in CC.
        pose proof (go_tag_range d op len) as TG. cbv zeta in TG. fold g in TG. unfold INT_MAX in TG.
        pose proof (get_object_bounds d op len ltac:(eapply Forall_impl; [| exact DF]; cbv beta; intros; lia) LEN0) as GB1. cbv zeta in GB1. fold g in GB1. rewrite EG in GB1.
        destruct GB1 as (GB1 & GB2 & GB3).
        assert (RB : 0 <= go_ret g < 64) by (destruct RC as [ER|[ER|[ER|ER]]]; rewrite ER; lia).
        assert (LXr : forall m2, munch [(TLC, TLC + 32)]%Z mr m2 -> wmono ctusegs mr m2 ->
                  lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) ([(PIC, PIC + 10); (PPC, PPC + 8); (TLC, TLC + 32)] ++ LIBW_AP) mX m2).
        { intros m2 MU2 WM2. eapply lx_pres_trans; [exact LXc|]. eapply lx_pres_trans.
          - eapply (lx_pres_up _ _ _ _ _ _ _ lo); [exact LX1| lia| intros q A n Hq; pose proof (BND q A n ltac:(apply in_app_iff; right; exact Hq)); lia| lia|].
            intros a Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [right; cbn in Ha; lia| left; apply rin_ivs_app; right; exact Ha].
          - pose proof (oinv_facts sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) _ _ _ _ _ _ _ OI1) as (HEAP1 & _).
            eapply (lx_pres_munch_gen sr OW1 (NEW ++ LB)); [exact HEAP1| exact CEIL| unfold GLOBALS_TOP; lia| lia| exact MU2| exact WM2|].
            constructor; [| constructor]. right. left. split; [cbn; lia|]. intros a Ha. cbn in Ha. cbn. right. right. left. lia. }
        (* [comment removed for export] *)
        assert (JOIN : forall (y11 y12 y13 y14 y15 : word) m2 (tl : list cell) (jz : list byte),
          munch [(TLC, TLC + 32)]%Z mr m2 -> wmono ctusegs mr m2 -> mem_inv ctusegs m2 -> stk ctusegs m2 lo (bv_unsigned sp + OFS + -144) -> rw_cells ctusegs m2 3355012 [C4 errv1] ->
          rw_cells ctusegs m2 TLC [C1 (Z_to_bv 8 1)] -> rw_cells ctusegs m2 (TLC + 1) tl -> cells_size tl = 31%nat ->
          rw_cells ctusegs m2 PIC [C1 bi; C1 bc; CB 8 jl] -> rw_cells ctusegs m2 PPC [C8 (Z_to_bv 64 (D + op))] ->
          rw_cells ctusegs m2 (bv_unsigned sp + OFS + -144) [CB 8 jz] -> rw_cells ctusegs m2 (bv_unsigned sp + OFS + -136) [C8 (Z_to_bv 64 0)] ->
          rw_cells ctusegs m2 (bv_unsigned sp + OFS + -128) [C8 (Z_to_bv 64 (D + go_p g))] -> rw_cells ctusegs m2 (bv_unsigned sp + OFS + -120) [C8 (Z_to_bv 64 (go_len g))] ->
          rw_cells ctusegs m2 (bv_unsigned sp + OFS + -112) [C4 (Z_to_bv 64 (go_cls g))] -> rw_cells ctusegs m2 (bv_unsigned sp + OFS + -108) [C4 (Z_to_bv 64 (go_tag g))] ->
          rw_cells ctusegs m2 (bv_unsigned sp + OFS + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
          implM ctusegs (interp (ap_embed (REST (snd r1)))) sr Q
            (MS (mkR (Z_to_bv 64 0x1128d8) (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) gp (Z_to_bv 64 RATP) q0 q1 q2 (Z_to_bv 64 (bv_unsigned sp + OFS)) (Z_to_bv 64 TLC)
                     (Z_to_bv 64 (go_ret g)) y11 y12 y13 y14 y15 p6 p7
                     (Z_to_bv 64 PPC) (Z_to_bv 64 0) (Z_to_bv 64 (D + op)) (Z_to_bv 64 (PIC + 2)) (Z_to_bv 64 (PIC + 1)) (Z_to_bv 64 PIC) (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0)
                     (Z_to_bv 64 match ot with Some t => t | None => -1 end) q3 q4 q5 q6)
                F1 (Z_to_bv 64 0x112954) fc1 None m2 (seg_rom ctusegs))).
        { intros y11 y12 y13 y14 y15 m2 tl jz MU2 WM2 MI2 ST2 ERR2 GTV GT SZTL GPIC GPPC G0 G1 G2 G3 G4 G5 G6.
          apply rw_cells_CB_of in GT. rewrite SZTL in GT. join2 GTV GT.
          apply rw_cells_CB_of in G0. cbn [cells_size csize Nat.add plus] in G0.
          join2 G0 G1. join2 G0 G2. join2 G0 G3. join2 G0 G4. join2 G0 G5. join2 G0 G6.
          assert (OI2 : oinvK (OFS + -144) (STK - 144) sr (snd r1) m2 OW1 errv1 bo1 NEW).
          { eapply (oinv_munch sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) CEIL GLO LO1 STK1 OFS1 SPB B63 SP16 OFS161 XPok PBX); [exact OI1| exact MU2| exact WM2| exact MI2| | exact ERR2|].
            - replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) by lia. exact ST2.
            - constructor; [left; cbn; lia| constructor]. }
          subst REST. cbv beta. unfold MallocRep.wz.
          destruct ot as [t|].
          * destruct (negb (go_tag g =? t) || negb (go_cls g =? 0)) eqn:EB.
            -- (* [comment removed for export] *)
               eapply implM_abind.
               { eapply (tlen_after_wrong OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F1 fc1) with (TLCo := Some TLC);
                   [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI2| exact FRM1| exact FE1
                   | exact PIClo| exact PIChi| exact PPClo| exact PPChi| split; [exact T1| split; [exact T2| split; [exact T3| split; [exact T8| exact GTV]]]]| apply LXr; [exact MU2| exact WM2]
                   | exact GPIC| reflexivity| exact GPPC| exact G0| exact LEN0| exact EG| exact OT|].
                 apply orb_true_iff in EB. destruct EB as [EB|EB]; apply negb_true_iff in EB; apply Z.eqb_neq in EB; [left| right]; exact EB. }
               intros r2 sr2 ms2 PO2. unfold tlen_postR in PO2. cbn [fst snd] in PO2.
               eapply (KW_ t); [reflexivity| reflexivity| | exact PO2].
               apply orb_true_iff in EB. destruct EB as [EB|EB]; apply negb_true_iff in EB; apply Z.eqb_neq in EB; [left| right]; exact EB.
            -- (* [comment removed for export] *)
               apply orb_false_iff in EB. destruct EB as [EB1 EB2]. apply negb_false_iff in EB1. apply negb_false_iff in EB2. apply Z.eqb_eq in EB1. apply Z.eqb_eq in EB2.
               eapply (tlen_after_ok X (Some t) KS Q OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F1 fc1) with (TLCo := Some TLC);
                 [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI2| exact FRM1| exact FE1
                 | exact PIClo| exact PIChi| exact PPClo| exact PPChi| exact DJ| exact AL8| exact AL8P| split; [exact T1| split; [exact T2| split; [exact T3| split; [exact T8| exact GTV]]]]| apply LXr; [exact MU2| exact WM2]
                 | exact GPIC| exact GPPC| exact G0| exact OP0| exact LEN0| exact OPL| exact EG
                 | split; [exact OT| split; [exact EB1| exact EB2]]|].
               intros st' s' ms' PO2. eapply KS_; [reflexivity| split; [exact EB1| exact EB2]| exact PO2].
          * eapply (tlen_after_ok X None KS Q OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F1 fc1) with (TLCo := Some TLC);
              [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI2| exact FRM1| exact FE1
              | exact PIClo| exact PIChi| exact PPClo| exact PPChi| exact DJ| exact AL8| exact AL8P| split; [exact T1| split; [exact T2| split; [exact T3| split; [exact T8| exact GTV]]]]| apply LXr; [exact MU2| exact WM2]
              | exact GPIC| exact GPPC| exact G0| exact OP0| exact LEN0| exact OPL| exact EG| exact I|].
            intros st' s' ms' PO2. eapply KS_; [reflexivity| exact I| exact PO2]. }
        (* [comment removed for export] *)
        unfold implM. iprefix.
        step. step. step. step. step. step. step. step. step. zstep. zstep. step. step.
        step. if_cases K15; zc K15.
        * ihere. to_implM. eapply JOIN; [exact MU| exact WM| assumption| assumption| exact ERRr| exact HTV| exact HT| reflexivity| exact HPIC| exact HPPC| exact FR0| exact FRO| exact HPP1| exact HPL1| exact HPC1| exact HPT1| exact FRS].
        * step. step. if_cases K24; zc K24; [| exfalso; revert K24; rewrite ?unsigned_lit, ?swrap32_small, ?signed_small by lia; lia]. clear K24.
          ihere. to_implM. eapply JOIN; [exact MU| exact WM| assumption| assumption| exact ERRr| exact HTV| exact HT| reflexivity| exact HPIC| exact HPPC| exact FR0| exact FRO| exact HPP1| exact HPL1| exact HPC1| exact HPT1| exact FRS].
    - (* [comment removed for export] *)
      setreg 9%Z (Z_to_bv 64 0) ltac:(reflexivity).
      step. if_true. step. step. step. step. step. step. step.
      name_mem mc.
      match goal with H : stk ctusegs mc lo _ |- _ => rename H into STc end. match goal with H : mem_inv ctusegs mc |- _ => rename H into MIc end.
      lazymatch type of FR0 with rw_cells _ _ _ [CB 8 ?j] => set (j0 := j) in FR0; clearbody j0 end.
      destruct (CALL mc [CB 8 j0] MU WM MIc STc ERRX FR0 eq_refl FRO FRP FRL FRC FRT FRS HPIC HPPC I) as [OIc LXc].
      ihere. unfold tlen_tree. destruct (go_err g) as [e|] eqn:EG.
      + (* [comment removed for export] *)
        unfold tlen_fail. to_implM.
        eapply implM_abind.
        { eapply implM_abind.
          { replace (match e with GeHdr => err_raise RS_hdr_too_long | GeTooLong => err_raise RS_too_long | GeTooSmall => aunr end) with (go_eff g) by (unfold go_eff; rewrite EG; reflexivity).
            replace (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -144))) by (f_equal; lia).
            eapply (go_call (OFS + -144) (STK - 144)); [exact LO1| exact OFS1| exact OFS161| unfold GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIc| exact FRMX| exact OP0| exact LEN0| exact OPL| exact GC| lia| lia| lia| lia
              | exact FRP| exact FRL| exact FRT| exact FRC]. }
          intros r1 sr ms1 PO1. unfold go_post in PO1. fold g in PO1. rewrite EG in PO1.
          destruct PO1 as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mr & OW1 & errv1 & bo1 & jl' & j2' & j3'
                           & -> & FRM1 & FE1 & OI1 & LX1 & HPP1 & RES1).
          replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LX1 |- * by lia.
          assert (RES1' : Z.land (bv_unsigned p0) 128 <> 0 /\ exists cl ct cc, rw_cells ctusegs mr (bv_unsigned sp + OFS + -120) [cl] /\ csize cl = 8%nat
                           /\ rw_cells ctusegs mr (bv_unsigned sp + OFS + -108) [ct] /\ csize ct = 4%nat /\ rw_cells ctusegs mr (bv_unsigned sp + OFS + -112) [cc] /\ csize cc = 4%nat).
          { pose proof (go_ret_cases d op len) as RC. cbv zeta in RC. fold g in RC.
            destruct e; destruct RES1 as (-> & H1 & H2 & H3);
              (split; [| eexists _, _, _; split; [exact H1|]; split; [reflexivity|]; split; [exact H2|]; split; [reflexivity|]; split; [exact H3| reflexivity]]).
            - unfold MallocRep.wz. rewrite unsigned_lit by lia. cbv. discriminate.
            - unfold MallocRep.wz. destruct RC as [E0|[E0|[E0|E0]]]; rewrite E0; cbv; discriminate.
            - unfold MallocRep.wz. rewrite unsigned_lit by lia. cbv. discriminate. }
          clear RES1. destruct RES1' as (B7 & cl & ct & cc & HPL1 & SZL & HPT1 & SZT & HPC1 & SZC).
          replace (ret_pc (Z_to_bv 64 0x1128bc)) with (Z_to_bv 64 0x1128bc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          pose proof (agree_of_lx_pres _ _ _ _ _ LX1) as AG1.
          apply (rw_cells_agree _ _ _ _ _ AG1) in FR0; [| intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG1) in FRO; [| intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG1) in FRS; [| intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG1) in HPIC; [| intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AG1) in HPPC; [| intros a Ha; apply CL; cbn in Ha; lia].
          pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO1 STK1 OFS1 SPB B63 _ _ _ _ _ _ _ OI1) as (_ & _ & _ & STr & _ & _ & ERRr & MIr & _).
          unfold LX_ERRNO, RATP in ERRr. change (3355176 - 164) with 3355012 in ERRr. replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STr by lia.
          clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mr) as MU. pose proof (wmono_refl ctusegs mr) as WM.
          unfold implM. iprefix. step. ihere. to_implM.
          (* [comment removed for export] *)
          join2 FR0 FRO. join2 FR0 HPP1. join2 FR0 HPL1. join2 FR0 HPC1. join2 FR0 HPT1.
          apply rw_cells_CB_of in FR0. cbn [cells_size csize Nat.add plus] in FR0. rewrite SZL, SZC, SZT in FR0. cbn [Nat.add plus] in FR0. join2 FR0 FRS.
          eapply (tlen_after_err OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F1 fc1) with (TLCo := None) (vb := Z_to_bv 8 0) (jt := []);
            [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI1| exact FRM1| exact FE1
            | exact PIClo| exact PIChi| exact PPClo| exact PPChi| exact I| | exact HPIC| reflexivity| exact HPPC| exact FR0| exact B7].
          eapply lx_pres_trans; [exact LXc|].
          eapply (lx_pres_up _ _ _ _ _ _ _ lo); [exact LX1| lia| intros q A n Hq; pose proof (BND q A n ltac:(apply in_app_iff; right; exact Hq)); lia| lia|].
          intros a Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [right; cbn in Ha; lia| left; apply rin_ivs_app; right; exact Ha]. }
        intros r2 sr2 ms2 PO2. unfold tlen_postR in PO2. cbn [fst snd] in PO2. eapply (KE_ e); [reflexivity| exact PO2].
      + (* [comment removed for export] *)
        lazymatch goal with |- impl _ _ (interp (ap_embed (?R stX)) _) _ _ => set (REST := R) end.
        replace (REST stX) with (abind (go_eff g) (fun _ : unit => REST) stX) by (unfold go_eff; rewrite EG; reflexivity).
        to_implM. eapply implM_abind.
        { replace (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) with (Z_to_bv 64 (bv_unsigned sp + (OFS + -144))) by (f_equal; lia).
          eapply (go_call (OFS + -144) (STK - 144)); [exact LO1| exact OFS1| exact OFS161| unfold GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OIc| exact FRMX| exact OP0| exact LEN0| exact OPL| exact GC| lia| lia| lia| lia
            | exact FRP| exact FRL| exact FRT| exact FRC]. }
        intros r1 sr ms1 PO1. unfold go_post in PO1. fold g in PO1. rewrite EG in PO1.
        destruct PO1 as (q0 & q1 & q2 & p0 & p1 & p2 & p3 & p4 & p5 & p6 & p7 & q3 & q4 & q5 & q6 & F1 & fc1 & mr & OW1 & errv1 & bo1 & jl' & j2' & j3'
                         & -> & FRM1 & FE1 & OI1 & LX1 & HPP1 & -> & HPL1 & HPT1 & HPC1).
        replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in LX1 |- * by lia.
        replace (ret_pc (Z_to_bv 64 0x1128bc)) with (Z_to_bv 64 0x1128bc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof (agree_of_lx_pres _ _ _ _ _ LX1) as AG1.
        apply (rw_cells_agree _ _ _ _ _ AG1) in FR0; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG1) in FRO; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG1) in FRS; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG1) in HPIC; [| intros a Ha; apply CL; cbn in Ha; lia].
        apply (rw_cells_agree _ _ _ _ _ AG1) in HPPC; [| intros a Ha; apply CL; cbn in Ha; lia].
        pose proof (oinv_call sp m s LB E lo B canary K d D XP (OFS + -144) (STK - 144) GLO LO1 STK1 OFS1 SPB B63 _ _ _ _ _ _ _ OI1) as (_ & _ & _ & STr & _ & _ & ERRr & MIr & _).
        unfold LX_ERRNO, RATP in ERRr. change (3355176 - 164) with 3355012 in ERRr. replace (bv_unsigned sp + (OFS + -144)) with (bv_unsigned sp + OFS + -144) in STr by lia.
        clear MU WM. pose proof (munch_refl (@nil (Z * Z)) mr) as MU. pose proof (wmono_refl ctusegs mr) as WM.
        unfold implM. iprefix. step. ihere. to_implM.
        join2 FR0 FRO. join2 FR0 HPP1. join2 FR0 HPL1. join2 FR0 HPC1. join2 FR0 HPT1. join2 FR0 FRS.
        assert (LXr : lx_pres (NEW ++ LB) (bv_unsigned sp + OFS) ([(PIC, PIC + 10); (PPC, PPC + 8); (PIC, PIC)] ++ LIBW_AP) mX mr).
        { eapply lx_pres_trans; [exact LXc|].
          eapply (lx_pres_up _ _ _ _ _ _ _ lo); [exact LX1| lia| intros q A n Hq; pose proof (BND q A n ltac:(apply in_app_iff; right; exact Hq)); lia| lia|].
          intros a Ha. apply rin_ivs_app in Ha. destruct Ha as [Ha|Ha]; [right; cbn in Ha; lia| left; apply rin_ivs_app; right; exact Ha]. }
        subst REST. cbv beta. unfold MallocRep.wz.
        destruct ot as [t|].
        * destruct (negb (go_tag g =? t) || negb (go_cls g =? 0)) eqn:EB.
          -- (* [comment removed for export] *)
             eapply implM_abind.
             { eapply (tlen_after_wrong OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F1 fc1) with (TLCo := None) (vb := Z_to_bv 8 0) (jt := []);
                 [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI1| exact FRM1| exact FE1
                 | exact PIClo| exact PIChi| exact PPClo| exact PPChi| exact I| exact LXr| exact HPIC| reflexivity| exact HPPC| exact FR0| exact LEN0| exact EG| exact OT|].
               apply orb_true_iff in EB. destruct EB as [EB|EB]; apply negb_true_iff in EB; apply Z.eqb_neq in EB; [left| right]; exact EB. }
             intros r2 sr2 ms2 PO2. unfold tlen_postR in PO2. cbn [fst snd] in PO2.
             eapply (KW_ t); [reflexivity| reflexivity| | exact PO2].
             apply orb_true_iff in EB. destruct EB as [EB|EB]; apply negb_true_iff in EB; apply Z.eqb_neq in EB; [left| right]; exact EB.
          -- (* [comment removed for export] *)
             apply orb_false_iff in EB. destruct EB as [EB1 EB2]. apply negb_false_iff in EB1. apply negb_false_iff in EB2. apply Z.eqb_eq in EB1. apply Z.eqb_eq in EB2.
             eapply (tlen_after_ok X (Some t) KS Q OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F1 fc1) with (TLCo := None) (vb := Z_to_bv 8 0) (jt := []);
               [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI1| exact FRM1| exact FE1
               | exact PIClo| exact PIChi| exact PPClo| exact PPChi| exact DJ| exact AL8| exact AL8P| exact I| exact LXr| exact HPIC| exact HPPC| exact FR0| exact OP0| exact LEN0| exact OPL| exact EG
               | split; [exact OT| split; [exact EB1| exact EB2]]|].
             intros st' s' ms' PO2. eapply KS_; [reflexivity| split; [exact EB1| exact EB2]| exact PO2].
        * eapply (tlen_after_ok X None KS Q OFS STK ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FX F1 fc1) with (TLCo := None) (vb := Z_to_bv 8 0) (jt := []);
            [exact LO| exact OFS0| exact OFS16| unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| exact OI1| exact FRM1| exact FE1
            | exact PIClo| exact PIChi| exact PPClo| exact PPChi| exact DJ| exact AL8| exact AL8P| exact I| exact LXr| exact HPIC| exact HPPC| exact FR0| exact OP0| exact LEN0| exact OPL| exact EG| exact I|].
          intros st' s' ms' PO2. eapply KS_; [reflexivity| exact I| exact PO2].
  Qed.
  End Act.
End Proofs.
End WithCeiling0.
