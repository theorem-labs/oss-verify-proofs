(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnDivWords BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib BgWords BgArith BgMont BgExp.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Cells Step Arr Bytes Frame.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr ShiftPure.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnP Require Import BnLeaves.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA W_cryptoA W_smallA AsStruct2.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import W_ctxA W_ctx_getA W_ctx_endA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnAKitAF BnCallAF W_expandAF W_callsAF W_ctxAF W_ctx_getAF W_ctx_endAF W_lshiftAF W_div_tailAF W_divAF W_bndivAF W_uaddAF W_addAF W_subAF W_set_wordAF W_cmpAF AFrameComp ExpKitAF W_small3A W_calls3AF W_nnmodAF ExpStmtF ExpBodyKitF PlaceMont PlaceKitA W_mont_ctxAF W_mont_freeAF MontKitAF Fr_exp_mont.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).

Definition mont_out (rr rq : bnref) (pm : bptr) : BM (M:=btree bptr) (ptr:=bptr) unit :=
  bbind ops (BN_from_montgomery ops rr rq) (fun _ => bbind ops (BN_MONT_CTX_free ops pm) (fun _ => BN_CTX_end ops)).
Definition mont_gueron (bits window : Z) (rr rp rm rq : bnref) (vals : list bnref) (pm : bptr) : BM (M:=btree bptr) (ptr:=bptr) unit :=
  bbind ops (bget ops rm) (fun m =>
  let j := bn_top m in
  if (j =? 0)%nat then bunr ops else
  bbind ops
    (if Z.testbit (nth (j - 1) (bn_buf m) 0) 63 then
       if (rq =? rm)%nat then bunr ops else
       bbind ops (bn_wexpand ops rq j) (fun _ =>
       bbind ops (bget ops rq) (fun rb =>
       bbind ops (bget ops rm) (fun m =>
       bset ops rq (mkBN (bn_d rb) (splice (bn_buf rb) 0 (neg_limbs (firstn j (bn_buf m)))) j (bn_neg rb) (bn_flags rb)))))
     else bn_to_mont_fixed_top ops rq ROne) (fun _ =>
  bbind ops (exp_window_loop ops (bn_mul_mont_fixed_top ops) (Z.to_nat bits) rp rq vals window (bits - 1) true) (fun _ =>
  mont_out rr rq pm))).
Definition mont_tail (bits : Z) (rr ra_ rp rm d rq v0 : bnref) (pm : bptr) : BM (M:=btree bptr) (ptr:=bptr) unit :=
  bbind ops (bget ops ra_) (fun a =>
  bbind ops (BN_ucmp ops ra_ rm) (fun c =>
  bbind ops (if bn_neg a || (0 <=? c) then bbind ops (BN_nnmod ops v0 ra_ rm) (fun _ => bret ops v0) else bret ops ra_) (fun aa =>
  bbind ops (bn_to_mont_fixed_top ops v0 aa) (fun _ =>
  bbind ops (exp_table ops (bn_mul_mont_fixed_top ops) (window_bits bits) v0 d) (fun vals =>
  mont_gueron bits (window_bits bits) rr rp rm rq vals pm))))).
Definition mont_rest (bits : Z) (rr ra_ rp rm : bnref) : BM (M:=btree bptr) (ptr:=bptr) unit :=
  bbind ops (BN_CTX_start ops) (fun _ =>
  bbind ops (BN_CTX_get ops) (fun d =>
  bbind ops (BN_CTX_get ops) (fun rq =>
  bbind ops (BN_CTX_get ops) (fun v0 =>
  bbind ops (BN_MONT_CTX_new ops) (fun pm =>
  bbind ops (BN_MONT_CTX_set ops rm) (fun _ =>
  mont_tail bits rr ra_ rp rm d rq v0 pm)))))).
Lemma BN_mod_exp_mont_eq : forall rr ra_ rp rm,
  BN_mod_exp_mont ops rr ra_ rp rm =
  bbind ops (bget ops rm) (fun m =>
    if negb (is_odd_pure m) then bunr ops
    else bbind ops (any_consttime ops [rp; ra_; rm]) (fun ct =>
         if ct then bunr ops
         else bbind ops (BN_num_bits ops rp) (fun bits =>
              if bits =? 0 then exp_bits0 ops rr rm else mont_rest bits rr ra_ rp rm))).
Proof. reflexivity. Qed.

Lemma testbit_63 : forall v, 0 <= v < 2 ^ 64 -> Z.testbit v 63 = (2 ^ 63 <=? v).
Proof.
  intros v Hv. destruct (Z.leb_spec (2 ^ 63) v) as [H|H].
  - apply Z.testbit_true; [lia|]. replace (v / 2 ^ 63) with 1 by (apply Z.div_unique with (r := v - 2 ^ 63); lia). reflexivity.
  - apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma nth_error_wlimbs : forall (l : list Z) i, (i < length l)%nat -> nth_error (wlimbs l) i = Some (Z_to_bv 64 (nth i l 0)).
Proof. intros l i H. unfold wlimbs. rewrite nth_error_map. rewrite (nth_error_nth' l 0 H). reflexivity. Qed.
Lemma hpl_pl_mont : forall PL x r, hpl PL r -> hpl (pl_set_mont PL x) r.
Proof.
  intros PL x r [N H]. split; [exact N|]. intros p E.
  destruct (mont_ref r) eqn:MR.
  - destruct x as [[a q]|]; [|rewrite (pl_of_mont_none (pl_set_mont PL None) r eq_refl MR) in E; discriminate E].
    destruct (mont_ref_cases r MR) as [-> | [-> | -> ]]; cbn in E; injection E as <-; eauto.
  - rewrite pl_of_set_mont_other in E by exact MR. exact (H p E).
Qed.
Lemma nbuf_pl_mont : forall PL x r, nbuf PL r -> nbuf (pl_set_mont PL x) r.
Proof.
  intros PL x r H a d E.
  destruct (mont_ref r) eqn:MR.
  - destruct x as [[a0 q]|]; [|rewrite (pl_of_mont_none (pl_set_mont PL None) r eq_refl MR) in E; discriminate E].
    destruct (mont_ref_cases r MR) as [-> | [-> | -> ]]; cbn in E; discriminate E.
  - rewrite pl_of_set_mont_other in E by exact MR. exact (H a d E).
Qed.

Lemma ref_at_mont_fresh : forall (st : bstate bptr) OW PL x r a, pl_mont PL = None -> ref_at st OW PL r a -> ref_at st OW (pl_set_mont PL x) r a.
Proof.
  intros st OW PL x r a E H. destruct (mont_ref r) eqn:MR.
  - exfalso. pose proof (pl_of_mont_none PL r E MR) as N.
    assert (RF : (r < NFIX)%nat) by (destruct (mont_ref_cases r MR) as [-> | [-> | -> ]]; unfold RMontRR, RMontN, RMontNi, NFIX; lia).
    apply (proj1 (ref_at_fixed st OW PL r a RF)) in H. destruct H as (p & Ep & _). rewrite N in Ep. discriminate Ep.
  - apply ref_at_pl_mont_other; [exact MR| exact H].
Qed.

Lemma ref_at_mont_enter : forall (st : bstate bptr) OW PL r a (b : block) x, pl_mont PL = None -> ref_at st OW PL r a ->
  ref_at (st_mont_init st) (b :: OW) (pl_set_mont PL x) r a.
Proof.
  intros st OW PL r a b x E H. unfold st_mont_init. apply ref_at_setbn, ref_at_setbn, ref_at_setbn, ref_at_set_mont.
  apply ref_at_mont_fresh; [exact E|]. eapply ref_at_ow_mono; [| exact H]. intros y Hy. right. exact Hy.
Qed.

Section Body.
Context {AR1 : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR1).
Local Notation AF := (@ar_AF AR1).
Local Notation PMc := (@ar_PMc AR1).
Local Notation ACEIL := (@BnHeapA.ACEIL AR1).
Local Notation AHEAP := (@BnHeapA.AHEAP AR1).

Section Proofs.

  Variables (CS CMM CFM CMS : Z).
  Hypothesis CSstart : BN_CTX_START_STACK <= CS.
  Hypothesis CSget : BN_CTX_GET_STACK <= CS.
  Hypothesis CSend : BN_CTX_END_STACK <= CS.
  Hypothesis CSnnmod : BN_NNMOD_STACK <= CS.
  Hypothesis CSsetw : BN_SET_WORD_STACK <= CS.
  Hypothesis CSnb : BN_NUM_BITS_STACK <= CS.
  Hypothesis CSucmp : BN_UCMP_STACK <= CS.
  Hypothesis CSwexp : BN_WEXPAND_STACK <= CS.
  Hypothesis CSnew : BN_MONT_CTX_NEW_STACK <= CS.
  Hypothesis CSfree : BN_MONT_CTX_FREE_STACK <= CS.
  Hypothesis CMM0 : 0 <= CMM.
  Hypothesis CFM0 : 0 <= CFM.
  Hypothesis CMS0 : 0 <= CMS.

  Hypothesis bn_mul_mont_fixed_top_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ rb : bnref) (ar aa ab am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x227550 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> ref_at ls OW PL rb ab -> wref PL rr -> rb <> ROne -> nbuf PL ra_ -> nbuf PL rb ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz ab -> a3 = wz am -> a4 = wz ac ->
    implA (bn_mul_mont_fixed_top (tree_ops bptr) rr ra_ rb ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x227550) fc None m (seg_rom bgasegs)).
  Hypothesis bn_to_mont_fixed_top_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMM ->
    fr_room 1 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x227c1c (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> nbuf PL ra_ ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (bn_to_mont_fixed_top (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x227c1c) fc None m (seg_rom bgasegs)).
  Hypothesis BN_from_montgomery_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rr ra_ : bnref) (ar aa am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CFM ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x227b30 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rr ar -> ref_at ls OW PL ra_ aa -> wref PL rr -> ra_ <> ROne ->
    pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz aa -> a2 = wz am -> a3 = wz ac ->
    implA (BN_from_montgomery (tree_ops bptr) rr ra_ ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CFM (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x227b30) fc None m (seg_rom bgasegs)).
  Hypothesis BN_MONT_CTX_set_walkA : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs)
      (lo : Z) (ras : list Z) (rd : bnref) (ad am ac : Z) (qm qc : bptr),
    bn_preA Σ ls m OW LB PL EA sp lo CS CMS ->
    fr_room 3 ls OW LB ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx 0x227e44 (bv_unsigned ra :: ras) ->
    tp = wz TP_A -> ref_at ls OW PL rd ad -> rd <> ROne -> pl_mont PL = Some (am, qm) -> pl_ctx PL = Some (ac, qc) -> pl_bn PL RTmod = None ->
    a0 = wz am -> a1 = wz ad -> a2 = wz ac ->
    implA (BN_MONT_CTX_set (tree_ops bptr) rd ls) Σ
      (bn_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m PL EA CMS (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x227e44) fc None m (seg_rom bgasegs)).

  Definition EXP_MONT_TOTAL : Z := 40 * MC + CMS + BN_NNMOD_COST + CFM + 65600 * CMM.

  Section Fixed.

    Variable Q : unit * bstate bptr -> rts RT -> machine_state -> Prop.
    Variables (sp gp s0 ra : word) (Σ1 : rts RT) (ls : bstate bptr) (m1 : mem) (OW LB : list block) (PL0 : placement) (EA : BnRepDefs.err_addrs).
    Variables (lo spa f TOTAL : Z) (q : bptr) (ras : list Z) (g : nat) (junk : list byte).
    Variables (rr ra_ rp rm : bnref) (arr ara arp arm ac : Z) (qc : bptr).
    Local Notation LBX := ((q, f + 32, 256) :: LB).
    Hypothesis TOTAL_OK : EXP_MONT_TOTAL <= TOTAL.
    Hypothesis LOK : lo <= spa - CS.
    Hypothesis ROOM : fr_room 3 ls OW LBX.
    Hypothesis TIGHT : cnt_bal ls OW + Z.of_nat (length LBX) + 72 <= LIVE_MAX.
    Hypothesis INF : In (f, 3%nat) (@ar_FR AR1).
    Hypothesis NFV : forall x, f + 32 <= x < f + 288 -> ~ rin_ivs (pl_frames PL0) x.
    Hypothesis CTX : uk_ctx BN_MOD_EXP_MONT (bv_unsigned ra :: ras).
    Hypothesis HPC : pl_ctx PL0 = Some (ac, qc).
    Hypothesis HFM : pl_mont PL0 = None.
    Hypothesis HFT : pl_bn PL0 RTmod = None.
    Hypothesis HAr : ref_at ls OW PL0 rr arr.
    Hypothesis HAa : ref_at ls OW PL0 ra_ ara.
    Hypothesis HAp : ref_at ls OW PL0 rp arp.
    Hypothesis HAm : ref_at ls OW PL0 rm arm.
    Hypothesis WRr : hpl PL0 rr.
    Hypothesis NROa : ra_ <> ROne.
    Hypothesis NROp : rp <> ROne.
    Hypothesis NROm : rm <> ROne.
    Hypothesis NBa : nbuf PL0 ra_.

    Definition locs (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : word) : list cell :=
      [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14; C8 w15; C8 w16; C8 w17; C8 (Z_to_bv 64 f)].

    Hypothesis CONT : forall (Σk : rts RT) (lsk : bstate bptr) (mk : mem) (OWk : list block) (loc : list cell) (used : Z) (mb : mem)
          (x1 x5 x6 x7 x9 y10 y11 y12 y13 y14 y15 y16 y17 x20 x21 rv x24 x25 x26 x27 x28 x29 x30 x31 : word) (Fk : bvmap 5 word) (fck : bv 32),
        cenvA LBX PL0 lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb (loc ++ [CB g junk]) used Σk lsk mk OWk ->
        lib_state lsk mk OWk PL0 EA -> used <= TOTAL -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb -> rv = wz 1 ->
        implA (TRet (tt, lsk)) Σk Q
          (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) x5 x6 x7 sp x9 y10 y11 y12 y13 y14 y15 y16 y17
                   (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x20 x21 (Z_to_bv 64 f) rv x24 x25 x26 x27 x28 x29 x30 x31)
              Fk (wz EXP_MONT_EXIT) fck None mk (seg_rom bgasegs)).

    Lemma MC0 : 0 <= MC. Proof. unfold MC. lia. Qed.
    Lemma NROr : rr <> ROne. Proof. exact (proj1 (hpl_wref _ _ WRr)). Qed.

    Ltac lstep v := step;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
      | |- _ => idtac
      end.

    Ltac fgeo HEAP :=
      destruct (AH_fr_geo _ _ _ _ f 3%nat HEAP INF) as (G1 & G2 & G3 & G4 & G5); unfold fs_size in G3, G5;
      change (Z.shiftl 64 (Z.of_nat 3)) with 512 in G3, G5; unfold SEGTOP_A, STACK_WIN, BnHeapA.ACEIL in *.

    Ltac solve_loc := lazymatch goal with |- exists loc, ?l = loc ++ _ => exists (removelast l); reflexivity end.

    Ltac strip2 l := lazymatch l with
      | cons _ (cons _ nil) => constr:(@nil cell)
      | cons ?x ?t => let r := strip2 t in constr:(cons x r)
      end.

    Ltac relocal EV LS MU WM ST MI FR FSZ EV' LS' :=
      unfold locs in FSZ; cbn [app cells_size csize Nat.add] in FSZ;
      lazymatch type of FR with rw_cells _ _ _ ?fr => let p := strip2 fr in
        destruct (cenv_localA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ EV LS MU WM ltac:(clear; lia) ltac:(clear - FSZ; lia) ST MI FR
                    ltac:(cbn [cells_size csize Nat.add app]; clear - FSZ; lia)) as (EV' & LS') end.

    Local Ltac kit EV :=
      pose proof EV as (OK & _);
      pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & _ & FROKK & _ & _);
      pose proof (ESPvA _ _ _ _ _ _ _ _ _ _ _ _ OK (proj1 (proj2 EV))) as ESP;
      pose proof (AH_ceil _ _ _ _ (proj1 (proj2 EV))) as (CE1 & CE2 & CE3); unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CE1, CE2, CE3;
      assert (CS16 : 16 <= CS) by (pose proof CSend as H; unfold BN_CTX_END_STACK in H; clear - H; lia);
      assert (LOFB16 : lo <= spa - 16) by (clear - LOK CS16; lia);
      pose proof MC0 as MCP.

    Section Scope.
      Variables (am : Z) (qm : bptr).
      Hypothesis AMR : 0 < am < 2 ^ 63.
      Local Notation PL := (pl_set_mont PL0 (Some (am, qm))).
      Local Notation CENV := (cenvA LBX PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW)).
      Lemma HPM : pl_mont PL = Some (am, qm). Proof. reflexivity. Qed.
      Lemma HPCS : pl_ctx PL = Some (ac, qc). Proof. exact HPC. Qed.
      Lemma ROOMS : fr_room 3 ls ((qm, am, 96) :: OW) LBX.
      Proof. apply fr_room_mont; [exact ROOM | clear - TIGHT; unfold block in *; lia]. Qed.
      Lemma WRrS : wref PL rr. Proof. apply hpl_wref. apply hpl_pl_mont. exact WRr. Qed.

      Lemma HArS : ref_at ls ((qm, am, 96) :: OW) PL rr arr.
      Proof. apply ref_at_mont_fresh; [exact HFM|]. eapply ref_at_ow_mono; [| exact HAr]. intros b Hb. right. exact Hb. Qed.
      Lemma HAaS : ref_at ls ((qm, am, 96) :: OW) PL ra_ ara.
      Proof. apply ref_at_mont_fresh; [exact HFM|]. eapply ref_at_ow_mono; [| exact HAa]. intros b Hb. right. exact Hb. Qed.
      Lemma HApS : ref_at ls ((qm, am, 96) :: OW) PL rp arp.
      Proof. apply ref_at_mont_fresh; [exact HFM|]. eapply ref_at_ow_mono; [| exact HAp]. intros b Hb. right. exact Hb. Qed.
      Lemma HAmS : ref_at ls ((qm, am, 96) :: OW) PL rm arm.
      Proof. apply ref_at_mont_fresh; [exact HFM|]. eapply ref_at_ow_mono; [| exact HAm]. intros b Hb. right. exact Hb. Qed.

      Lemma mont_exit : forall mb used ΣK lsK mK OWK (rq : bnref) (ar : Z) (ri : nat) (w0 w1 w2 w3 w5 w6 w7 w8 w9 w10 w12 w14 w15 w16 w17 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x23 x24 x25 x26 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 w2 w3 (Z_to_bv 64 arr) w5 w6 w7 w8 w9 w10 (Z_to_bv 64 0) w12 (Z_to_bv 64 am) w14 w15 w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> used + CFM <= TOTAL -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        ref_at lsK OWK PL rq ar -> rq = RPool ri ->
        implA (mont_out rr rq qm lsK) ΣK Q
          (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) x21 (Z_to_bv 64 f) x23 x24 x25 x26 (Z_to_bv 64 ar) t3 t4 t5 t6)
              F (Z_to_bv 64 2815980) fc None mK (seg_rom bgasegs)).
      Proof.
        intros until fc. intros EVK LSK KCOST AXB HArK Er. kit EVK. unfold MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). cbn [app locs] in FRK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HArS) as HArrK.
        unfold mont_out. unfold bbind at 1. cbn [bind tree_ops].
        apply implA_from_evt. do 6 step.

    apply evt_done.
    eapply implA_bind.
    { eapply (BN_from_montgomery_walkA) with (lo := lo) (OW := OWK) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HArrK | exact HArK | exact WRrS | rewrite Er; unfold RPool, ROne, NFIX; clear; lia | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EVK | exact LSK | exact LOK | clear - KCOST CFM0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af61c CTX).
    }
    cbv beta. intros [ueA lseA] ΣeA mseA PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FeA & fceA & meA & OWeA & PLeA & -> & CPeA & (EPLeA & ->)).
    subst PLeA. specialize (CPeA eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVK CPeA) as (EVeA & LSeA).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPeA) as RSeA. clear CPeA.
    rewrite (ret_pc_even 2816004) by (clear; lia).
        cbv beta. cbn [fst snd].
        pose proof EVeA as (_ & _ & STeA & MIeA & _ & _ & _ & _ & FReA & FSZeA & _). cbn [app locs] in FReA.
        unfold MallocRep.wz. apply implA_from_evt. do 3 step.
        step. if_false.
        do 2 step.

        apply evt_done.
        eapply (mont_free_callA (fun _ => BN_CTX_end ops) Q LBX PL0 EA lo (bv_unsigned sp) spa s0 ra ras TOTAL Σ1 ls OW mb _ _ ΣeA lseA meA OWeA am qm);
          [ exact EVeA | exact LSeA | exact HFM | reflexivity | clear - LOK CSfree; lia | clear - KCOST; lia | reflexivity
          | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af648 CTX) |].
        intros ΣF lsF mF OWF z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 FF fcF EVF LSF.
        rewrite (ret_pc_even 2816048) by (clear; lia).
        pose proof EVF as (OKF & _).
        unfold MallocRep.wz. apply implA_from_evt. do 2 step.

        apply evt_done.
        eapply implA_post.
        { eapply (BN_CTX_end_walkA) with (lo := lo) (OW := OWF) (LB := LBX) (PL := PL0) (EA := EA);
            [| reflexivity | exact HPC | reflexivity].
          eapply cenv_preA; [exact EVF | exact LSF | clear - LOK CSend; lia | clear - KCOST CFM0; lia]. }
        cbv beta. intros [uE lsE] ΣE msE PO.
        apply (bn_postA_cpost LBX PL0 EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OKF | exact (proj1 (proj2 EVF))].
        cbn [fst snd] in *.
        destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FE & fcE & mE & OWE & PLE & -> & CPE & (EPLE & EOWE)).
        subst PLE. specialize (CPE eq_refl).
        destruct (cenv_postA LBX PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVF CPE) as (EVE & LSE).
        rewrite (ret_pc_even 2816056) by (clear; lia).
        destruct uE. eapply CONT; [exact EVE | exact LSE | clear - KCOST CFM0; lia | exact AXB | reflexivity].
      Qed.

      Definition bst (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (pc : Z) (fc : bv 32) (m : mem) : machine_state :=
        MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x20 x21 (Z_to_bv 64 f) x23 x24 x25 x26 x27 t3 t4 t5 t6)
           F (Z_to_bv 64 pc) fc None m (seg_rom bgasegs).

      Local Notation MUL := (bn_mul_mont_fixed_top ops).

      Definition SQRQ (mb : mem) (pre : list cell) (used0 : Z) (lsK : bstate bptr) (OWK : list block) (x23 x20 x24 x25 x26 : word) (ar : Z)
          (r : unit * bstate bptr) (Σ' : rts RT) (ms' : machine_state) : Prop :=
        exists mK' OWK' used' (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc,
          ms' = bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 (Z_to_bv 64 0) x23 x24 x25 x26 (Z_to_bv 64 ar) t3 t4 t5 t6 F 2815892 fc mK'
          /\ CENV mb pre used' Σ' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable lsK OWK (snd r) OWK' /\ used' <= used0.

      Lemma sqr_loopA : forall c mb used ΣK lsK mK OWK (rq : bnref) (ar : Z) (ri : nat) (x20 x24 x25 x26 : word) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w14 w15 w16 w17 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (x23 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 ac) (Z_to_bv 64 am) w14 w15 w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA ->
        ref_at lsK OWK PL rq ar -> rq = RPool ri -> Z.of_nat (S c) < 2 ^ 31 ->
        used + Z.of_nat (S c) * CMM <= TOTAL ->
        implA (exp_sqr_loop ops MUL (S c) rq lsK) ΣK (SQRQ mb (locs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 (Z_to_bv 64 ac) (Z_to_bv 64 am) w14 w15 w16 w17 ++ [CB g junk]) (used + Z.of_nat (S c) * CMM) lsK OWK x23 x20 x24 x25 x26 ar)
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 (Z_to_bv 64 (Z.of_nat (S c))) x23 x24 x25 x26 (Z_to_bv 64 ar) t3 t4 t5 t6 F 2815856 fc mK).
      Proof.
        induction c as [|c IH]; intros until fc; intros EVK LSK HArK Er CBN KCOST; kit EVK; unfold bst, MallocRep.wz in *;
          pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _); cbn [app locs] in FRK;
          rewrite exp_sqr_loop_S; apply implA_from_evt; do 5 step; step.
        -
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_mul_mont_fixed_top_walkA) with (lo := lo) (OW := OWK) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HArK | exact HArK | exact HArK | rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri)) | rewrite Er; unfold RPool, ROne, NFIX; clear; lia | rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri)) | rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri)) | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EVK | exact LSK | exact LOK | clear - KCOST CMM0; lia].
      - eapply cenv_roomA; [exact EVK | exact ROOMS | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af5a0 CTX).
    }
    cbv beta. intros [us lss] Σs mss PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fs & fcs & ms & OWs & PLs & -> & CPs & (EPLs & ->)).
    subst PLs. specialize (CPs eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVK CPs) as (EVs & LSs).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPs) as RSs. clear CPs.
    rewrite (ret_pc_even 2815880) by (clear; lia).
          unfold MallocRep.wz. apply implA_from_evt. step. if_false.
          step. rewrite unsigned_lit by (clear - CBN; lia). rewrite (bn_swrap32_small _) by (clear - CBN; lia).
          rewrite exp_sqr_loop_O. change (Z.of_nat 1 + -1) with 0.
          step. if_false.
          apply evt_done. apply implA_ret.
          unfold SQRQ, bst. exists ms, OWs, (used + CMM). do 18 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact EVs|]. split; [exact LSs|]. split; [exact RSs|]. clear - CMM0. lia.
        -
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_mul_mont_fixed_top_walkA) with (lo := lo) (OW := OWK) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HArK | exact HArK | exact HArK | rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri)) | rewrite Er; unfold RPool, ROne, NFIX; clear; lia | rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri)) | rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri)) | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EVK | exact LSK | exact LOK | clear - KCOST CMM0; lia].
      - eapply cenv_roomA; [exact EVK | exact ROOMS | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af5a0 CTX).
    }
    cbv beta. intros [us lss] Σs mss PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fs & fcs & ms & OWs & PLs & -> & CPs & (EPLs & ->)).
    subst PLs. specialize (CPs eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVK CPs) as (EVs & LSs).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPs) as RSs. clear CPs.
    rewrite (ret_pc_even 2815880) by (clear; lia).
          unfold MallocRep.wz. apply implA_from_evt. step. if_false.
          step. rewrite unsigned_lit by (clear - CBN; lia). rewrite (bn_swrap32_small _) by (clear - CBN; lia).
          replace (Z.of_nat (S (S c)) + -1) with (Z.of_nat (S c)) by (clear; lia).
          step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - CBN; lia); zify_cond KZ; try (exfalso; clear - KZ; lia).
          apply evt_done.
          eapply implA_mono; [eapply (IH mb (used + CMM) Σs lss ms OWs rq ar ri x20 x24 x25 x26); [exact EVs| exact LSs| exact (ref_at_stable _ _ _ _ PL _ _ RSs HArK)| exact Er| clear - CBN; lia| clear - KCOST; lia]|].
          cbv beta. intros r Σ' ms' (mK' & OWK' & used' & R); unfold SQRQ. exists mK', OWK', used'.
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3 & K4).
          do 18 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|]. split; [eapply refs_stable_trans; [exact RSs| exact K3]|]. clear - K4. lia.
      Qed.

      Lemma scan_loopA : forall c (i wvalue wend : Z) mb used ΣK lsK mK OWK (wstart window : Z) (POST : machine_state -> Prop) (x26 : word) (w0 w1 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w16 w17 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (x23 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ref_at lsK OWK PL rp arp ->
        1 <= i -> i + Z.of_nat c = window -> (0 < c)%nat -> window <= 6 -> 0 <= wstart < 2 ^ 31 -> 0 <= wend < i -> wend <= wstart -> 1 <= wvalue < 2 ^ (wend + 1) ->
        (forall mK' (wv' we' : Z) (x1' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x27 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
            CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK' OWK ->
            lib_state lsK mK' OWK PL EA ->
            window_scan (is_bit_set_pure (getbn rp lsK)) wstart c i wvalue wend = (wv', we') ->
            evt bgasegs POST (bst x1' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 wv') x21 x23 (Z_to_bv 64 wstart) (Z_to_bv 64 we') x26 x27 t3 t4 t5 t6 F' 2815816 fc' mK')) ->
        evt bgasegs POST (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 wvalue) (Z_to_bv 64 (wstart - i)) x23 (Z_to_bv 64 wstart) (Z_to_bv 64 wend) x26 (Z_to_bv 64 i) t3 t4 t5 t6 F 2815764 fc mK).
      Proof.
        induction c as [|c IH]; intros until fc; intros EVK LSK HApK I1 IC C0 W6 WS WE WES WV K; [lia|]. kit EVK. unfold bst, MallocRep.wz in *.
        assert (P2 : 2 ^ (wend + 1) <= 2 ^ i) by (apply Z.pow_le_mono_r; lia).
        assert (P6 : 2 ^ i <= 2 ^ 6) by (apply Z.pow_le_mono_r; lia).
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        step. rewrite lts_signed by (clear - WS I1 IC W6; lia).
        destruct (Z.ltb_spec (wstart - i) 0) as [LT|GE].
        -
          cbn [negb]. eapply (K mK wvalue wend); [exact EVK| exact LSK|]. cbn [window_scan]. replace (wstart - i <? 0) with true by (symmetry; apply Z.ltb_lt; exact LT). reflexivity.
        - cbn [negb].

          step. step. step.
    eapply (is_bit_set_callA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb LOFB16); [exact EVK | exact LSK | exact HApK | exact NROp | clear - GE WS I1; lia |].
    intros mT y0T y1T y2T y4T y5T y6T y7T y8T y9T y10T y11T y12T y13T y14T EVT LST.
          rewrite (ret_pc_even 2815780) by (clear; lia).
          pose proof EVT as (_ & _ & STT & MIT & _ & _ & _ & _ & FRT & FSZT & _). cbn [app locs] in FRT.
          destruct (is_bit_set_pure (getbn rp lsK) (wstart - i)) eqn:EB; cbn [Z.b2z].
          +
            step. if_false.
            step. rewrite (unsigned_lit i), (unsigned_lit wend) by (clear - I1 WE IC W6; lia). rewrite (bn_swrap32_small (i - wend)) by (clear - I1 WE IC W6; lia).
            pose proof (lor_shiftl_1 wvalue (i - wend) ltac:(clear - WV P2; lia) ltac:(clear - WE; lia)) as LOR.
            assert (WB2 : 1 <= Z.lor (Z.shiftl wvalue (i - wend)) 1 < 2 ^ (i + 1)).
            { rewrite LOR.
              assert (2 <= 2 ^ (i - wend)) by (replace (2 ^ (i - wend)) with (2 * 2 ^ (i - wend - 1)) by (rewrite <- Z.pow_succ_r by (clear - WE; lia); f_equal; clear - WE; lia);
                                             assert (0 < 2 ^ (i - wend - 1)) by (apply Z.pow_pos_nonneg; clear - WE; lia); lia).
              assert (wvalue * 2 ^ (i - wend) <= (2 ^ (wend + 1) - 1) * 2 ^ (i - wend)) by (apply Z.mul_le_mono_nonneg_r; clear - WV WE H; lia).
              assert (2 ^ (wend + 1) * 2 ^ (i - wend) = 2 ^ (i + 1)) by (rewrite <- Z.pow_add_r by (clear - WE; lia); f_equal; clear - WE; lia).
              assert (0 <= wvalue * 2 ^ (i - wend)) by (apply Z.mul_nonneg_nonneg; clear - WV H; lia).
              assert ((2 ^ (wend + 1) - 1) * 2 ^ (i - wend) = 2 ^ (wend + 1) * 2 ^ (i - wend) - 2 ^ (i - wend)) by (clear; lia).
              clear - H H0 H1 H2 H3 WV. lia. }
            assert (P7 : 2 ^ (i + 1) <= 2 ^ 7) by (apply Z.pow_le_mono_r; clear - IC C0 W6; lia).
            assert (SH : 0 <= Z.shiftl wvalue (i - wend) < 2 ^ 7) by (rewrite LOR in WB2; rewrite Z.shiftl_mul_pow2 by (clear - WE; lia); clear - WB2 P7; lia).
            step. rewrite (unsigned_lit (i - wend)) by (clear - I1 WE IC W6; lia). rewrite (Z.mod_small (i - wend) 32) by (clear - I1 WE IC W6; lia).
            rewrite (unsigned_lit wvalue) by (clear - WV P2 P6; lia). rewrite (bn_swrap32_small (Z.shiftl wvalue (i - wend))) by (clear - SH; lia).
            step. rewrite (unsigned_lit (Z.shiftl wvalue (i - wend))) by (clear - SH; lia).
            step.
            step. rewrite (swrap32_wrap64 i 1) by (clear - I1 IC W6; lia).
            step. rewrite (swrap32_wrap64 (wstart - i) (-1)) by (clear - GE WS I1 IC W6; lia). replace (wstart - i + -1) with (wstart - (i + 1)) by (clear; lia).
            step.
            step. if_cases KW; rewrite ?unsigned_lit in KW by (clear - I1 IC W6; lia); zify_cond KW.
            *
              eapply (IH (i + 1) (Z.lor (Z.shiftl wvalue (i - wend)) 1) i mb used ΣK lsK mT OWK wstart window POST x26 w0 w1 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w16 w17);
                [exact EVT| exact LST| exact HApK| clear - I1; lia| clear - IC; lia| clear - IC KW; lia| exact W6| exact WS| clear - I1; lia| clear - GE; lia
                | exact WB2 |].
              intros mK' wv' we' x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x21' x27' t3' t4' t5' t6' F'' fc'' EV' LS' SC.
              eapply K; [exact EV'| exact LS'|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB. exact SC.
            *
              eapply (K mT); [exact EVT| exact LST|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB.
              replace c with 0%nat by (clear - IC KW; lia). reflexivity.
          +
            step. if_true.
            step. rewrite (swrap32_wrap64 i 1) by (clear - I1 IC W6; lia).
            step. rewrite (swrap32_wrap64 (wstart - i) (-1)) by (clear - GE WS I1 IC W6; lia). replace (wstart - i + -1) with (wstart - (i + 1)) by (clear; lia).
            step.
            step. if_cases KW; rewrite ?unsigned_lit in KW by (clear - I1 IC W6; lia); zify_cond KW.
            * eapply (IH (i + 1) wvalue wend mb used ΣK lsK mT OWK wstart window POST x26 w0 w1 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w16 w17);
                [exact EVT| exact LST| exact HApK| clear - I1; lia| clear - IC; lia| clear - IC KW; lia| exact W6| exact WS| clear - WE; lia| exact WES| exact WV|].
              intros mK' wv' we' x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x21' x27' t3' t4' t5' t6' F'' fc'' EV' LS' SC.
              eapply K; [exact EV'| exact LS'|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB. exact SC.
            * eapply (K mT); [exact EVT| exact LST|]. cbn [window_scan]. replace (wstart - i <? 0) with false by (symmetry; apply Z.ltb_ge; exact GE). rewrite EB.
              replace c with 0%nat by (clear - IC KW; lia). reflexivity.
      Qed.

      Definition vtab (lsK : bstate bptr) (OWK : list block) (ws : list word) (vals : list bnref) (addrs : list Z) : Prop :=
        length addrs = length vals /\
        forall i, (i < length vals)%nat ->
          nth_error ws i = Some (Z_to_bv 64 (nth i addrs 0)) /\ ref_at lsK OWK PL (nth i vals 0%nat) (nth i addrs 0)
          /\ (exists j, nth i vals 0%nat = RPool j) /\ 0 < nth i addrs 0 < 2^64.
      Lemma vtab_stable : forall lsK OWK ls' OW' ws vals addrs, vtab lsK OWK ws vals addrs -> refs_stable lsK OWK ls' OW' -> vtab ls' OW' ws vals addrs.
      Proof.
        intros lsK OWK ls' OW' ws vals addrs [L H] RS. split; [exact L|]. intros i Hi. destruct (H i Hi) as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS H2)|]. split; [exact H3| exact H4].
      Qed.
      Lemma vtab_snoc : forall lsK OWK ws vals addrs v a j, vtab lsK OWK ws vals addrs -> (length vals < length ws)%nat ->
        ref_at lsK OWK PL v a -> v = RPool j -> 0 < a < 2^64 ->
        vtab lsK OWK (Arr.upd ws (length vals) (Z_to_bv 64 a)) (vals ++ [v]) (addrs ++ [a]).
      Proof.
        intros lsK OWK ws vals addrs v a j [L H] Hl HA Ev Ha. split; [rewrite !length_app; cbn; lia|].
        intros i Hi. rewrite length_app in Hi. cbn in Hi.
        destruct (Nat.lt_ge_cases i (length vals)) as [Hlt|Hge].
        - destruct (H i Hlt) as (H1 & H2 & H3 & H4). rewrite !app_nth1 by lia.
          split; [rewrite nth_error_upd_other by lia; exact H1|]. split; [exact H2|]. split; [exact H3| exact H4].
        - assert (Ei : i = length vals) by lia. subst i.
          rewrite app_nth2 by lia. rewrite (app_nth2 vals [v] 0%nat) by lia. rewrite L, Nat.sub_diag. cbn [nth].
          split; [apply nth_error_upd_same; exact Hl|]. split; [exact HA|]. split; [exists j; exact Ev| exact Ha].
      Qed.

      Definition outk (rq : bnref) : unit * bstate bptr -> btree bptr (unit * bstate bptr) := fun p => mont_out rr rq qm (snd p).

      Definition WLOOP (fuel : nat) : Prop := forall (wstart : Z) (start : bool) mb used ΣK lsK mK OWK ws vals addrs (window : Z) (rq : bnref) (ar : Z) (ri : nat)
          (w0 w1 w3 w6 w8 w9 w10 w12 w16 w17 : word) (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x24 t3 t4 t5 t6 : word) (x23 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) w8 w9 w10 (Z_to_bv 64 0) w12 (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgasegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
        0 <= wstart < Z.of_nat fuel -> wstart < 2 ^ 24 ->
        ref_at lsK OWK PL rq ar -> rq = RPool ri -> ref_at lsK OWK PL rp arp ->
        used + 2 * (wstart + 1) * CMM + CFM <= TOTAL ->
        implA (tbind (exp_window_loop ops MUL fuel rp rq vals window wstart start lsK) (outk rq)) ΣK Q
          (bst x1 t0 t1 t2 (Z_to_bv 64 wstart) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ac) (Z_to_bv 64 (wstart - 1)) x23 x24 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 ar) t3 t4 t5 t6 F 2815668 fc mK).

      Lemma after_scanA : forall fuel, WLOOP fuel -> forall (wstart wv we : Z) (start : bool) mb used ΣK lsK mK OWK ws vals addrs (window : Z) (rq : bnref) (ar : Z) (ri : nat)
          (w0 w1 w3 w6 w8 w9 w16 w17 : word) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (x23 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) w8 w9 (Z_to_bv 64 we) (Z_to_bv 64 0) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgasegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
        0 <= wstart < 2 ^ 24 -> 0 <= we < window -> we <= wstart -> 1 <= wv < 2 ^ (we + 1) -> wstart - (we + 1) < Z.of_nat fuel ->
        ref_at lsK OWK PL rq ar -> rq = RPool ri -> ref_at lsK OWK PL rp arp ->
        used + 2 * (wstart + 1) * CMM + CFM <= TOTAL ->
        implA (tbind (tbind ((if start then bret ops tt else exp_sqr_loop ops MUL (Z.to_nat (we + 1)) rq) lsK)
                            (fun p2 => tbind (MUL rq rq (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) (snd p2))
                               (fun p => (if wstart - (we + 1) <? 0 then bret ops tt
                                          else exp_window_loop ops MUL fuel rp rq vals window (wstart - (we + 1)) false) (snd p)))) (outk rq)) ΣK Q
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.shiftr wv 1)) x21 x23 (Z_to_bv 64 wstart) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 ar) t3 t4 t5 t6 F 2815844 fc mK).
      Proof.
        intros fuel REC. intros until fc; intros EVK LSK AXB VB LEN VT VL WB WS WE WES WV WF HArK Er HApK KCOST. kit EVK. unfold bst, MallocRep.wz in *.
        fgeo (proj1 (proj2 EVK)).
        assert (ALV : (f + 32) mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
        assert (L32 : Z.of_nat (length vals) <= 32).
        { rewrite VL. destruct (1 <? window); [|lia]. change 32 with (2 ^ 5). apply Z.pow_le_mono_r; lia. }
        assert (WV2 : 0 <= Z.shiftr wv 1 < Z.of_nat (length vals)).
        { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. rewrite VL.
          assert (2 ^ (we + 1) <= 2 ^ window) by (apply Z.pow_le_mono_r; lia).
          destruct (Z.ltb_spec 1 window) as [Hw|Hw].
          - assert (2 ^ window = 2 * 2 ^ (window - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
          - assert (we = 0) by lia. subst we. change (2 ^ (0 + 1)) with 2 in WV. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        assert (WEC : 0 <= we * CMM) by (apply Z.mul_nonneg_nonneg; [clear - WE; lia | exact CMM0]).
        assert (WSC : 0 <= (wstart - we) * CMM) by (apply Z.mul_nonneg_nonneg; [clear - WES; lia | exact CMM0]).

        assert (TAIL : forall used1 Σt ls1 mt OW1 (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x21' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
              CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) w8 w9 (Z_to_bv 64 we) (Z_to_bv 64 0) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used1 Σt ls1 mt OW1 ->
              lib_state ls1 mt OW1 PL EA -> refs_stable lsK OWK ls1 OW1 ->
              used1 + CMM + 2 * (wstart - we) * CMM + CFM <= TOTAL ->
              implA (tbind (MUL rq rq (nth (Z.to_nat (Z.shiftr wv 1)) vals 0%nat) ls1)
                       (fun p => tbind ((if wstart - (we + 1) <? 0 then bret ops tt
                                         else exp_window_loop ops MUL fuel rp rq vals window (wstart - (we + 1)) false) (snd p)) (outk rq))) Σt Q
                (MS (mkR x1' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 (Z.shiftr wv 1)) x21' (Z_to_bv 64 f) x23 (Z_to_bv 64 wstart) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 ar) t3' t4' t5' t6')
                    F' (Z_to_bv 64 2815892) fc' None mt (seg_rom bgasegs))).
        { intros until fc'. intros EV1 LS1 RS1 KCOST1.
          pose proof VT as [VTL VT']. destruct (VT' (Z.to_nat (Z.shiftr wv 1)) ltac:(clear - WV2; lia)) as (Wi & HAi & (ji & Ei) & AiR). clear VT'.
          pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HArK) as HAr1.
          pose proof EV1 as (_ & _ & ST1 & MI1 & _ & _ & _ & _ & FR1 & FSZ1 & _). cbn [app locs] in FR1.
          pose proof (obj_arrA (q, f + 32, 256) LB PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ ws EV1 VB
                        ltac:(cbn [blk_size snd]; rewrite LEN; reflexivity) ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFV; clear - Hxq; lia)) as VA.
          cbn [blk_addr fst snd] in VA.
          pose proof (obj_acc _ _ _ _ (q, f + 32, 256) (proj1 (proj2 EV1)) ltac:(left; reflexivity)) as ACCV. cbn [blk_addr blk_size fst snd] in ACCV.
          pose proof (munch_refl [] mt) as MU0.
          apply implA_from_evt.
          step. rewrite (unsigned_lit (Z.shiftr wv 1)) by (clear - WV2 L32; lia). rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 3) with 8.
          step. step.
          assert (XR : 0 <= f + 32 + Z.shiftr wv 1 * 8 < 2 ^ 64 /\ f + 32 <= f + 32 + Z.shiftr wv 1 * 8 /\ f + 32 + Z.shiftr wv 1 * 8 + 8 <= f + 32 + 256) by (clear - WV2 L32 G1 G3 CE1 CE2 CE3; lia).
          step. rewrite (unsigned_lit (f + 32 + Z.shiftr wv 1 * 8)) by (clear - XR; lia).
          step. shl_with ACCV ALV. chk0.
          assert (Wi' : nth_error ws (Z.to_nat (Z.shiftr wv 1)) = Some (Z_to_bv 64 (nth (Z.to_nat (Z.shiftr wv 1)) addrs 0))) by exact Wi.
          let a := cur_mem_addr in pose proof (u64arr_read bgasegs mt (f + 32) _ (Z.shiftr wv 1) _ a VA Wi' ltac:(clear - WV2; lia) ltac:(addr_tac)) as RD.
          step. clear RD VA Wi' ACCV MU0.

          do 7 step.

    apply evt_done.
    eapply implA_bind.
    { eapply (bn_mul_mont_fixed_top_walkA) with (lo := lo) (OW := OW1) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HAr1 | exact HAr1 | exact (ref_at_stable _ _ _ _ PL _ _ RS1 HAi) | rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri)) | rewrite Ei; unfold RPool, ROne, NFIX; clear; lia | rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri)) | rewrite Ei; apply nbuf_pool | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV1 | exact LS1 | exact LOK | clear - KCOST1 CMM0 CFM0 WSC; lia].
      - eapply cenv_roomA; [exact EV1 | exact ROOMS | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV1).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af5e8 CTX).
    }
    cbv beta. intros [uv lsv] Σv msv PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV1))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fv & fcv & mv & OWv & PLv & -> & CPv & (EPLv & ->)).
    subst PLv. specialize (CPv eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EV1 CPv) as (EVv & LSv).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPv) as RSv. clear CPv.
    rewrite (ret_pc_even 2815952) by (clear; lia).
          pose proof (refs_stable_trans _ _ _ _ _ _ RS1 RSv) as RS0v.
          unfold MallocRep.wz. apply implA_from_evt. step. if_false.
          pose proof EVv as (_ & _ & STv & MIv & _ & _ & _ & _ & FRv & FSZv & _). cbn [app locs] in FRv.
          step.
          step. rewrite (unsigned_lit we) by (clear - WE WB; lia). rewrite zb_lxor_ones by (clear - WE WB; lia).
          step. rewrite (unsigned_lit wstart) by (clear - WS; lia). rewrite (unsigned_lit (18446744073709551615 - we)) by (clear - WE WB; lia).
          replace (wstart + (18446744073709551615 - we)) with ((wstart - (we + 1)) + 18446744073709551616) by (clear; lia).
          rewrite swrap32_plus_2_64, (bn_swrap32_small (wstart - (we + 1))) by (clear - WS WE WB; lia).
          step.
          step.
          step. rewrite lts_signed by (clear - WS WE WB; lia).
          destruct (Z.ltb_spec (wstart - (we + 1)) 0) as [WLT|WGE]; cbn [negb].
          -
            apply evt_done. unfold bret. cbn [ret tree_ops tbind fst snd]. unfold outk. cbn [snd].
            eapply mont_exit; [exact EVv | exact LSv | clear - KCOST1 CMM0 WSC; lia | exact AXB | exact (ref_at_stable _ _ _ _ PL _ _ RS0v HArK) | exact Er].
          -
            step. rewrite (swrap32_wrap64 (wstart - (we + 1)) (-1)) by (clear - WS WE WB WGE; lia). replace (wstart - (we + 1) + -1) with (wstart - (we + 1) - 1) by (clear; lia).
            step.

            apply evt_done.
            eapply (REC (wstart - (we + 1)) false mb _ _ _ mv _ ws vals addrs window rq ar ri);
              [exact EVv| exact LSv| exact AXB| exact VB| exact LEN| eapply vtab_stable; [exact VT| exact RS0v]| exact VL| exact WB| clear - WGE WF; lia| clear - WS WE; lia
              | exact (ref_at_stable _ _ _ _ PL _ _ RS0v HArK)| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS0v HApK)
              | clear - KCOST1; lia]. }
        apply implA_tbind_assoc.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        destruct start; cbn [negb Z.b2z] in *.
        -
          rewrite tbind_bret. cbv beta. cbn [fst snd].
          apply implA_from_evt. step. if_true.
          apply evt_done. apply implA_tbind_assoc. eapply TAIL; [exact EVK| exact LSK| apply refs_stable_refl| clear - KCOST CMM0 WEC; lia].
        -
          apply implA_from_evt. step. if_false. step. step.
          rewrite ?(unsigned_lit we) by (clear - WE WB; lia).
          replace (Z.to_nat (we + 1)) with (S (Z.to_nat we)) by (clear - WE; lia).
          replace (Z_to_bv 64 (we + 1)) with (Z_to_bv 64 (Z.of_nat (S (Z.to_nat we)))) by (f_equal; clear - WE; lia).
          apply evt_done. eapply implA_bind.
          { eapply (sqr_loopA (Z.to_nat we) mb used _ _ _ _ rq ar ri); [exact EVK| exact LSK| exact HArK| exact Er| clear - WE WB; lia
              | replace (Z.of_nat (S (Z.to_nat we))) with (we + 1) by (clear - WE; lia); clear - KCOST CMM0 CFM0 WEC WSC; lia]. }
          cbv beta. intros [uq lsq] Σq msq (mq & OWq & usedq & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & EVq & LSq & RSq & UQ). cbn [fst snd] in *.
          replace (Z.of_nat (S (Z.to_nat we))) with (we + 1) in UQ by (clear - WE; lia).
          unfold bst. apply implA_tbind_assoc. eapply TAIL; [exact EVq| exact LSq| exact RSq| clear - KCOST UQ CMM0 WEC; lia].
      Qed.

      Lemma window_loopA : forall fuel, WLOOP fuel.
      Proof.
        induction fuel as [|fuel IH]; unfold WLOOP; intros until fc; intros EVK LSK AXB VB LEN VT VL WB WS WS24 HArK Er HApK KCOST; [exfalso; clear - WS; lia|].
        kit EVK. unfold bst, MallocRep.wz in *.
        assert (WSC : 0 <= wstart * CMM) by (apply Z.mul_nonneg_nonneg; [clear - WS; lia | exact CMM0]).
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        apply implA_from_evt.

        step. step. step. step.
    eapply (is_bit_set_callA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb LOFB16); [exact EVK | exact LSK | exact HApK | exact NROp | clear - WS WS24; lia |].
    intros mi y0i y1i y2i y4i y5i y6i y7i y8i y9i y10i y11i y12i y13i y14i EVi LSi.
        rewrite (ret_pc_even 2815684) by (clear; lia).
        pose proof EVi as (_ & _ & STi & MIi & _ & _ & _ & _ & FRi & FSZi & _). cbn [app locs] in FRi.
        pose proof (munch_refl [(spa, spa + 152)]%Z mi) as MU. pose proof (wmono_refl bgasegs mi) as WM.
        destruct (is_bit_set_pure (getbn rp lsK) wstart) eqn:EB; cbn [Z.b2z].
        -
          destruct (window_scan (is_bit_set_pure (getbn rp lsK)) wstart (Z.to_nat (window - 1)) 1 1 0) as [wv we] eqn:SC.
          rewrite (ewl_set MUL fuel rp rq vals window wstart start lsK wv we EB SC). cbv beta.
          pose proof (window_scan_bnd (is_bit_set_pure (getbn rp lsK)) wstart (Z.to_nat (window - 1)) 1 1 0
                        ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - WS; lia) ltac:(clear; cbn; lia)) as BND.
          rewrite SC in BND. destruct BND as (WE & WES & WV).
          replace (1 + Z.of_nat (Z.to_nat (window - 1))) with window in WE by (clear - WB; lia).
          step. if_true. step. step. step.
          step. if_cases KW; rewrite ?unsigned_lit in KW by (clear - WB; lia); zify_cond KW.
          +
            assert (W1 : window = 1) by (clear - KW WB; lia). subst window.
            change (Z.to_nat (1 - 1)) with 0%nat in SC. cbn [window_scan] in SC. injection SC as <- <-.
            lstep 0. step.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
            relocal EVi LSi MU WM STi MIi FRi FSZi EVa LSa. clear MU WM STi MIi FRi FSZi.
            apply evt_done.
            eapply (after_scanA fuel IH wstart 1 0 start mb used _ lsK mA OWK ws vals addrs 1 rq ar ri);
              [exact EVa| exact LSa| exact AXB| exact VB| exact LEN| exact VT| exact VL| exact WB| clear - WS WS24; lia| clear; lia| clear - WS; lia| clear; cbn; lia| clear - WS; lia
              | exact HArK| exact Er| exact HApK| exact KCOST].
          +
            step. step. step.
            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
            relocal EVi LSi MU WM STi MIi FRi FSZi EVa LSa. clear MU WM STi MIi FRi FSZi.
            eapply (scan_loopA (Z.to_nat (window - 1)) 1 1 0 mb used _ lsK mA OWK wstart window);
              [exact EVa| exact LSa| exact HApK| clear; lia| clear - WB; lia| clear - KW WB; lia| clear - WB; lia| clear - WS WS24; lia| clear; lia| clear - WS; lia
              | clear; cbn; lia|].
            intros mK' wv' we' x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x21' x27' t3' t4' t5' t6' F' fc' EV' LS' SC'.
            rewrite SC in SC'. injection SC' as <- <-.
            assert (P7 : 2 ^ (we + 1) <= 2 ^ 7) by (apply Z.pow_le_mono_r; clear - WE WB; lia).
            assert (SHR : 0 <= Z.shiftr wv 1 < 2 ^ 7) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 1) with 2; clear - WV P7; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
            unfold bst.
            pose proof EV' as (_ & _ & STx & MIx & _ & _ & _ & _ & FRx & FSZx & _). cbn [app locs] in FRx.
            pose proof (munch_refl [(spa, spa + 152)]%Z mK') as MU. pose proof (wmono_refl bgasegs mK') as WM.
            step.
            step. rewrite (unsigned_lit wv) by (clear - WV P7; lia). rewrite ?(bn_swrap32_small wv) by (clear - WV P7; lia).
            rewrite ?(bn_swrap32_small (Z.shiftr wv 1)) by (clear - SHR; lia).
            step. step. step.

            lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
            relocal EV' LS' MU WM STx MIx FRx FSZx EVb LSb. clear MU WM STx MIx FRx FSZx.
            apply evt_done.
            eapply (after_scanA fuel IH wstart wv we start mb used _ lsK mB OWK ws vals addrs window rq ar ri);
              [exact EVb| exact LSb| exact AXB| exact VB| exact LEN| exact VT| exact VL| exact WB| clear - WS WS24; lia| exact WE| exact WES| exact WV| clear - WS WE; lia
              | exact HArK| exact Er| exact HApK| exact KCOST].
        -
          rewrite (ewl_clear MUL fuel rp rq vals window wstart start lsK EB). cbv beta.
          step. if_false.
          assert (NEXT : forall used1 Σn ls1 mn OW1 (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
                CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) w8 w9 w10 (Z_to_bv 64 0) w12 (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used1 Σn ls1 mn OW1 ->
                lib_state ls1 mn OW1 PL EA -> refs_stable lsK OWK ls1 OW1 -> used1 + 2 * wstart * CMM + CFM <= TOTAL ->
                implA (tbind ((if wstart =? 0 then bret ops tt
                               else exp_window_loop ops MUL fuel rp rq vals window (wstart - 1) start) ls1) (outk rq)) Σn Q
                  (MS (mkR x1' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                           (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 (wstart - 1)) (Z_to_bv 64 f) x23 (Z_to_bv 64 wstart) (Z_to_bv 64 SHB)
                           (Z_to_bv 64 (Z.b2z (negb start))) (Z_to_bv 64 ar) t3' t4' t5' t6')
                      F' (Z_to_bv 64 2815720) fc' None mn (seg_rom bgasegs))).
          { intros until fc'. intros EV1 LS1 RS1 KCOST1.
            apply implA_from_evt.
            destruct (Z.eqb_spec wstart 0) as [W0|WN0].
            -
              subst wstart.
              step. step. step. if_false. step.
              apply evt_done. unfold bret. cbn [ret tree_ops tbind fst snd]. unfold outk. cbn [snd].
              eapply mont_exit; [exact EV1 | exact LS1 | clear - KCOST1; lia | exact AXB | exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK) | exact Er].
            - step. rewrite (swrap32_wrap64 wstart (-1)) by (clear - WS WS24; lia). replace (wstart + -1) with (wstart - 1) by (clear; lia).
              step. rewrite (swrap32_wrap64 (wstart - 1) (-1)) by (clear - WS WS24; lia). replace (wstart - 1 + -1) with (wstart - 1 - 1) by (clear; lia).
              step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - WS WS24; lia); zify_cond KZ; [|exfalso; clear - KZ WN0; lia].
              apply evt_done.
              eapply (IH (wstart - 1) start mb _ _ _ mn _ ws vals addrs window rq ar ri);
                [exact EV1| exact LS1| exact AXB| exact VB| exact LEN| eapply vtab_stable; [exact VT| exact RS1]| exact VL| exact WB| clear - WS WN0; lia| clear - WS24; lia
                | exact (ref_at_stable _ _ _ _ PL _ _ RS1 HArK)| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RS1 HApK)
                | clear - KCOST1; lia]. }
          apply evt_done. apply implA_tbind_assoc.
          destruct start; cbn [negb Z.b2z] in *.
          +
            rewrite tbind_bret. cbv beta. cbn [fst snd].
            apply implA_from_evt. step. if_true.
            apply evt_done. eapply NEXT; [exact EVi| exact LSi| apply refs_stable_refl| clear - KCOST CMM0 WSC; lia].
          +
            apply implA_from_evt. step. if_false.
            do 5 step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_mul_mont_fixed_top_walkA) with (lo := lo) (OW := OWK) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HArK | exact HArK | exact HArK | rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri)) | rewrite Er; unfold RPool, ROne, NFIX; clear; lia | rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri)) | rewrite Er; exact (hpl_nbuf _ _ (hpl_pool PL ri)) | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EVi | exact LSi | exact LOK | clear - KCOST CMM0 CFM0 WSC; lia].
      - eapply cenv_roomA; [exact EVi | exact ROOMS | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVi).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af4fc CTX).
    }
    cbv beta. intros [ur lsr] Σr msr PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVi))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fr & fcr & mr & OWr & PLr & -> & CPr & (EPLr & ->)).
    subst PLr. specialize (CPr eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVi CPr) as (EVr & LSr).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPr) as RSr. clear CPr.
    rewrite (ret_pc_even 2815716) by (clear; lia).
            unfold MallocRep.wz. apply implA_from_evt. step. if_false.
            apply evt_done. eapply NEXT; [exact EVr| exact LSr| exact RSr| clear - KCOST CMM0; lia].
      Qed.

      Lemma win_entryA : forall fuel (wstart : Z) (start : bool) mb used ΣK lsK mK OWK ws vals addrs (window : Z) (rq : bnref) (ar : Z) (ri : nat)
          (w0 w1 w3 w6 w8 w9 w10 w12 w16 w17 : word) (x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 x21 x24 x26 x27 t3 t4 t5 t6 : word) (x23 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) w8 w9 w10 (Z_to_bv 64 0) w12 (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK ->
        lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgasegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
        0 <= wstart < Z.of_nat fuel -> wstart < 2 ^ 24 ->
        ref_at lsK OWK PL rq ar -> rq = RPool ri -> ref_at lsK OWK PL rp arp ->
        used + 2 * (wstart + 1) * CMM + CFM <= TOTAL ->
        implA (tbind (exp_window_loop ops MUL fuel rp rq vals window wstart start lsK) (outk rq)) ΣK Q
          (bst x1 t0 t1 t2 (Z_to_bv 64 wstart) (Z_to_bv 64 (Z.b2z (negb start))) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ac) x21 x23 x24 (Z_to_bv 64 SHB) x26 x27 t3 t4 t5 t6 F 2815656 fc mK).
      Proof.
        intros until fc; intros EVK LSK AXB VB LEN VT VL WB WS WS24 HArK Er HApK KCOST. kit EVK. unfold bst, MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        apply implA_from_evt.
        step.
        step. rewrite (swrap32_wrap64 wstart (-1)) by (clear - WS WS24; lia). replace (wstart + -1) with (wstart - 1) by (clear; lia).
        step. rewrite (unsigned_lit (Z.b2z (negb start))) by (clear; destruct start; cbn; lia).
        replace (Z.land (Z.b2z (negb start)) 1) with (Z.b2z (negb start)) by (clear; destruct start; reflexivity).
        apply evt_done.
        eapply (window_loopA fuel wstart start mb used _ lsK mK OWK ws vals addrs window rq ar ri);
          [exact EVK| exact LSK| exact AXB| exact VB| exact LEN| exact VT| exact VL| exact WB| exact WS| exact WS24| exact HArK| exact Er| exact HApK| exact KCOST].
      Qed.

      Definition GFQ (x23 : word) (mb : mem) (pre : list cell) (used0 : Z) (lsT : bstate bptr) (OWT : list block)
          (rv : unit * bstate bptr) (Σ' : rts RT) (ms' : machine_state) : Prop :=
        exists mK' OWK' used' (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x24 x26 x27 t3 t4 t5 t6 : word) F fc,
          ms' = bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ac) x21 x23 x24 (Z_to_bv 64 SHB) x26 x27 t3 t4 t5 t6 F 2815644 fc mK'
          /\ CENV mb pre used' Σ' (snd rv) mK' OWK' /\ lib_state (snd rv) mK' OWK' PL EA /\ refs_stable lsT OWT (snd rv) OWK' /\ used' <= used0.

      Definition GFILL_stmt : Prop := forall mb used ΣT lsT mT OWT (rq : bnref) (ar : Z) (ri : nat) (bits window : Z) (w0 w1 w3 w6 w9 w10 w16 w17 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (x23 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) w9 w10 (Z_to_bv 64 0) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣT lsT mT OWT -> lib_state lsT mT OWT PL EA ->
        ref_at lsT OWT PL rq ar -> rq = RPool ri -> ref_at lsT OWT PL rm arm -> rq <> rm ->
        (1 <= bn_top (getbn rm lsT))%nat -> used + MC <= TOTAL ->
        implA (tbind (bn_wexpand ops rq (bn_top (getbn rm lsT)) lsT)
                 (fun p => bset ops rq
                             (mkBN (bn_d (getbn rq (snd p)))
                                   (splice (bn_buf (getbn rq (snd p))) 0 (neg_limbs (firstn (bn_top (getbn rm lsT)) (bn_buf (getbn rm (snd p))))))
                                   (bn_top (getbn rm lsT)) (bn_neg (getbn rq (snd p))) (bn_flags (getbn rq (snd p)))) (snd p))) ΣT
          (GFQ x23 mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) w9 w10 (Z_to_bv 64 0) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) (used + MC) lsT OWT)
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (shad arm)) x21 x23 (Z_to_bv 64 (Z.of_nat (bn_top (getbn rm lsT)))) (Z_to_bv 64 SHB) (Z_to_bv 64 arm) (Z_to_bv 64 am) t3 t4 t5 t6 F 2815420 fc mT).
      Hypothesis GFILL : GFILL_stmt.

      Lemma L_gueron : forall mb used ΣK lsK mK OWK ws vals addrs (bits window : Z) (rq : bnref) (ar : Z) (ri : nat) (w0 w1 w3 w6 w9 w10 w16 w17 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x25 x27 t3 t4 t5 t6 : word) (x23 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) w9 w10 (Z_to_bv 64 0) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgasegs mb (f + 32) ws -> length ws = 32%nat ->
        vtab lsK OWK ws vals addrs -> Z.of_nat (length vals) = (if 1 <? window then 2 ^ (window - 1) else 1) -> 1 <= window <= 6 ->
        0 < bits <= 32768 -> ref_at lsK OWK PL rq ar -> rq = RPool ri ->
        used + MC + CMM + 2 * bits * CMM + CFM <= TOTAL ->
        implA (mont_gueron bits window rr rp rm rq vals qm lsK) ΣK Q
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x23 (Z_to_bv 64 (shad (arm + 8))) x25 (Z_to_bv 64 arm) x27 t3 t4 t5 t6 F 2815304 fc mK).
      Proof.
        intros until fc; intros EVK LSK AXB VB LEN VT VL WB BITS HAqK Er KCOST. kit EVK. unfold bst, MallocRep.wz in *.
        pose proof EVK as (_ & HEAPK & _ & _ & _ & _ & _ & RSK & _).
        pose proof (AH_nodup_l _ _ _ _ HEAPK) as NDK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAmS) as HAmK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HApS) as HApK.
        destruct (open_for_read LBX PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ 16 EVK LSK HAmK NROm ltac:(clear; lia) LOFB16)
          as (Dm & BNm & (OKm1 & OKm2 & OKm3 & OKm4) & Um & _ & _ & _ & SEPm & SEPDm & _ & ACCm & ALm & ACCDm & ALDm & BDm & _ & Am0).
        unfold USTACK_TOP in SPT.
        assert (BC : 0 <= bits * CMM) by (apply Z.mul_nonneg_nonneg; [clear - BITS; lia | exact CMM0]).
        unfold mont_gueron, bbind, bget, bunr. cbn [bind ret unreachable tree_ops tbind fst snd]. cbv beta zeta.
        set (bm := getbn rm lsK) in *.
        destruct (Nat.eqb_spec (bn_top bm) 0) as [T0|TN0]; [apply implA_unr|].
        eapply implA_bind with (Q1 := GFQ x23 mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) w9 w10 (Z_to_bv 64 0) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) (used + MC + CMM) lsK OWK).
        2: { cbv beta. intros [uL lsL] ΣL msL (mL & OWL & usedL & R).
             destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & EVL & LSL & RSL & UL). cbn [fst snd] in *.
             unfold bst. pose proof EVL as (_ & _ & STL & MIL & _ & _ & _ & _ & FRL & FSZL & _). cbn [app locs] in FRL.
             apply implA_from_evt. step. step.
             step. rewrite (swrap32_wrap64 bits (-1)) by (clear - BITS; lia). replace (bits + -1) with (bits - 1) by (clear; lia).
             apply evt_done.
             eapply (win_entryA (Z.to_nat bits) (bits - 1) true mb _ _ _ mL _ ws vals addrs window rq ar ri);
               [exact EVL| exact LSL| exact AXB| exact VB| exact LEN| eapply vtab_stable; [exact VT| exact RSL]| exact VL| exact WB| clear - BITS; lia| clear - BITS; lia
               | exact (ref_at_stable _ _ _ _ PL _ _ RSL HAqK)| exact Er| exact (ref_at_stable _ _ _ _ PL _ _ RSL HApK)
               | replace (bits - 1 + 1) with bits by (clear; lia); clear - KCOST UL; lia]. }
        assert (NROq : rq <> ROne) by (rewrite Er; unfold RPool, ROne, NFIX; clear; lia).
        assert (TOP : 1 <= Z.of_nat (bn_top bm) <= 512) by (unfold BG_DMAX in OKm3; clear - TN0 OKm2 OKm3; lia).
        assert (NTH : nth_error (wlimbs (bn_buf bm)) (Z.to_nat (Z.of_nat (bn_top bm) - 1)) = Some (Z_to_bv 64 (nth (bn_top bm - 1) (bn_buf bm) 0))).
        { replace (Z.to_nat (Z.of_nat (bn_top bm) - 1)) with (bn_top bm - 1)%nat by (clear - TOP; lia). apply nth_error_wlimbs. unfold bn_dmax in OKm2. clear - TN0 OKm2. lia. }
        assert (LIMB : 0 <= nth (bn_top bm - 1) (bn_buf bm) 0 < 2 ^ 64).
        { assert (Hl : limb (nth (bn_top bm - 1) (bn_buf bm) 0)) by (apply (proj1 (List.Forall_nth limb (bn_buf bm)) OKm1); unfold bn_dmax in OKm2; clear - TN0 OKm2; lia).
          unfold limb, BW in Hl. exact Hl. }
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        unfold BnRepDefs.bn_cells in BNm. fold bm in BNm, Um, ACCDm, BDm.
        pose proof (munch_refl (@nil (Z * Z)) mK) as MU0.
        apply implA_from_evt.
        shl_with ACCm ALm. chk0.
        do 3 step. replace (Z.shiftr (bv_unsigned (Z_to_bv 64 arm)) 3 + SHB) with (shad arm) by (rewrite (unsigned_lit arm) by (clear - Am0 SEPm SPT FBSP; lia); unfold shad; rewrite ?Z.shiftr_div_pow2 by (clear; lia); reflexivity).
        shl_with ACCm ALm. step. chk0.
        step. unfold MallocRep.wz. rewrite (sx32_small (Z.of_nat (bn_top bm))) by (clear - TOP; lia).
        do 4 step. rewrite (unsigned_lit (Z.of_nat (bn_top bm))) by (clear - TOP; lia). rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 3) with 8.
        assert (DR : 0 <= Dm + Z.of_nat (bn_top bm) * 8 + -8 < 2 ^ 64) by (clear - BDm TOP; lia).
        step. rewrite (unsigned_lit (Dm + Z.of_nat (bn_top bm) * 8 + -8)) by exact DR.
        step. shl_limb ACCDm ALDm BDm (Z.of_nat (bn_top bm) - 1). chk0.
        let a := cur_mem_addr in pose proof (u64arr_read bgasegs mK Dm _ (Z.of_nat (bn_top bm) - 1) _ a Um NTH ltac:(clear - TOP; lia) ltac:(addr_tac)) as RD.
        step. clear RD.
        step. rewrite bv_lts_zero_r. rewrite (unsigned_lit (nth (bn_top bm - 1) (bn_buf bm) 0)) by exact LIMB. rewrite <- (testbit_63 _ LIMB).
        destruct (Z.testbit (nth (bn_top bm - 1) (bn_buf bm) 0) 63) eqn:TB.
        -
          destruct (Nat.eqb_spec rq rm) as [EQ|NEQ]; [apply evt_done; apply implA_unr|].
          apply evt_done.
          eapply implA_mono; [eapply (GFILL mb used ΣK lsK mK OWK rq ar ri bits window); [exact EVK | exact LSK | exact HAqK | exact Er | exact HAmK | exact NEQ | fold bm; clear - TN0; lia | clear - KCOST CMM0 BC CFM0; lia]|].
          cbv beta. intros rv Σ' ms' (mK' & OWK' & used' & R). unfold GFQ. exists mK', OWK', used'.
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3 & K4).
          do 22 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. clear - K4 CMM0. lia.
        -
          step.
          eapply (value_one_callA LBX PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb LOFB16); [exact EVK | exact LSK |].
          intros mV y0V y1V y2V y4V y5V y6V y7V y8V y9V y10V y11V y12V y13V y14V EVV LSV.
          rewrite (ret_pc_even 2815384) by (clear; lia).
          pose proof EVV as (_ & _ & STV & MIV & _ & _ & _ & _ & FRV & FSZV & _). cbn [app locs] in FRV.
          do 5 step. step.

    apply evt_done.
    eapply implA_post.
    { eapply (bn_to_mont_fixed_top_walkA) with (lo := lo) (OW := OWK) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HAqK | exact (ref_at_one lsK OWK PL) | rewrite Er; exact (hpl_wref _ _ (hpl_pool PL ri)) | apply nbuf_one | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EVV | exact LSV | exact LOK | clear - KCOST CMM0 BC CFM0 MCP; lia].
      - eapply cenv_roomA; [exact EVV | exact ROOMS | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVV).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af3c8 CTX).
    }
    cbv beta. intros [uo lso] Σo mso PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVV))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fo & fco & mo & OWo & PLo & -> & CPo & (EPLo & ->)).
    subst PLo. specialize (CPo eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVV CPo) as (EVo & LSo).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPo) as RSo. clear CPo.
    rewrite (ret_pc_even 2815408) by (clear; lia).
          unfold MallocRep.wz. apply implA_from_evt. step. if_true.
          apply evt_done. apply implA_ret.
          unfold GFQ, bst. exists mo, OWo, (used + CMM). do 22 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact EVo|]. split; [exact LSo|]. split; [exact RSo|]. clear - MCP. lia.
      Qed.

      Lemma table_loopA : forall c vals addrs mb used ΣK lsK mK OWK ws (bits window : Z) (d rq : bnref) (ad ar : Z) (di ri : nat) (w0 w1 w3 w6 w16 w17 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 (Z_to_bv 64 window) w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) w6 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) (Z_to_bv 64 ad) (Z_to_bv 64 (window - 1)) (Z_to_bv 64 0) (Z_to_bv 64 ac) (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgasegs mb (f + 32) ws -> length ws = 32%nat -> vtab lsK OWK ws vals addrs -> (1 <= length vals)%nat ->
        Z.of_nat (length vals) + Z.of_nat (S c) = 2 ^ (window - 1) -> 1 < window <= 6 -> 0 < bits <= 32768 ->
        ref_at lsK OWK PL d ad -> d = RPool di -> ref_at lsK OWK PL rq ar -> rq = RPool ri ->
        used + Z.of_nat (S c) * (MC + CMM) + MC + CMM + 2 * bits * CMM + CFM <= TOTAL ->
        implA (tbind (exp_table_loop ops MUL (S c) vals d lsK) (fun p => mont_gueron bits window rr rp rm rq (fst p) qm (snd p))) ΣK Q
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length vals) + 1)) x21 (Z_to_bv 64 (f + 32 + 8 * (Z.of_nat (length vals) - 1)))
               (Z_to_bv 64 (shad (arm + 8))) (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length vals))) (Z_to_bv 64 arm) (Z_to_bv 64 ad) t3 t4 t5 t6 F 2815176 fc mK).
      Proof.
        induction c as [|c IH]; intros until fc; intros EVK LSK AXB VB LEN VT K1 KC WB BITS HAd Ed HAqK Er KCOST; kit EVK; unfold bst, MallocRep.wz in *;
          fgeo (proj1 (proj2 EVK));
          assert (ALV : (f + 32) mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia);
          assert (NROd : d <> ROne) by (rewrite Ed; unfold RPool, ROne, NFIX; clear; lia);
          assert (P5 : 2 ^ (window - 1) <= 2 ^ 5) by (apply Z.pow_le_mono_r; clear - WB; lia);
          assert (K32 : (length vals < 32)%nat) by (clear - KC P5; lia);
          assert (BC : 0 <= bits * CMM) by (apply Z.mul_nonneg_nonneg; [clear - BITS; lia | exact CMM0]);
          pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _); cbn [app locs] in FRK;
          rewrite exp_table_loop_S; rewrite last_nth;
          apply implA_from_evt; step; step.
        -
          replace (Z.of_nat 1 * (MC + CMM)) with (MC + CMM) in KCOST by (clear; lia).
          assert (CC : 0 <= 0) by (clear; lia).
    apply evt_done.
    apply implA_tbind_assoc. eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OWK) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPCS | reflexivity].
      - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSget; lia | clear - KCOST CMM0 MCP BC CFM0 CC; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af2e8 CTX).
    }
    cbv beta. intros [ug lsg] Σg msg PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fg & fcg & mg & OWg & PLg & -> & CPg & (EPLg & (vi & Ev) & (av & HAv & ->) & INCLg)).
    subst PLg. specialize (CPg eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVK CPg) as (EVg & LSg).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPg) as RSg. clear CPg.
    rewrite (ret_pc_even 2815184) by (clear; lia).
        pose proof (proj1 (proj2 EVg)) as HEAPg. pose proof (lib_state_h_parts _ _ _ _ _ _ LSg) as PARTSg.
        assert (NROv : ug <> ROne) by (rewrite Ev; unfold RPool, ROne, NFIX; clear; lia).
        pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPg PARTSg FROKK HAv NROv) as (Av0 & AvC & _).
        assert (AvR : 0 < av < 2^64) by (unfold BnHeapA.ACEIL, STACK_WIN in *; clear - Av0 AvC CE1 CE2 CE3; lia). clear AvC.
        unfold MallocRep.wz.

        pose proof EVg as (_ & _ & STg & MIg & _ & _ & _ & _ & FRg & FSZg & _). cbn [app locs] in FRg.
        pose proof (obj_arrA (q, f + 32, 256) LB PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ ws EVg VB
                      ltac:(cbn [blk_size snd]; rewrite LEN; reflexivity) ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFV; clear - Hxq; lia)) as VA.
        cbn [blk_addr fst snd] in VA.
        pose proof (obj_acc _ _ _ _ (q, f + 32, 256) HEAPg ltac:(left; reflexivity)) as ACCV. cbn [blk_addr blk_size fst snd] in ACCV.
        assert (IDX : 0 <= Z.of_nat (length vals) < Z.of_nat (length ws)) by (rewrite LEN; clear - K32; lia).
        assert (XR : 0 <= f + 32 + 8 * (Z.of_nat (length vals) - 1) /\ f + 32 + 8 * Z.of_nat (length vals) + 8 <= f + 32 + 256 /\ f + 288 < 2 ^ 64) by (clear - K1 K32 G1 G3 CE1 CE2 CE3; lia).
        pose proof (munch_refl [(f + 32, f + 288)]%Z mg) as MU. pose proof (wmono_refl bgasegs mg) as WM.
        apply implA_from_evt.
        step. rewrite ?(unsigned_lit (f + 32 + 8 * (Z.of_nat (length vals) - 1))) by (clear - XR; lia).
        replace (f + 32 + 8 * (Z.of_nat (length vals) - 1) + 8) with (f + 32 + 8 * Z.of_nat (length vals)) by (clear; lia).
        step. rewrite ?(unsigned_lit (f + 32 + 8 * Z.of_nat (length vals))) by (clear - XR; lia).
        step. step. shl_with ACCV ALV. chk0.
        pose proof (u64arr_store_ok bgasegs mg (f + 32) ws (Z.of_nat (length vals)) (wa (f + 32 + 8 * Z.of_nat (length vals))) VA IDX eq_refl) as SOKW.
        pose proof (u64arr_write bgasegs mg (f + 32) ws (Z.of_nat (length vals)) (Z_to_bv 64 av) VA IDX) as U2.
        clear ACCV.
        step. store_done.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mV end.
        rewrite Nat2Z.id in U2.
        destruct (cenv_objA (q, f + 32, 256) LB PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ EVg LSg MU WM
                    ltac:(constructor; [cbn [blk_addr blk_size fst snd]; clear; lia | constructor])
                    ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFV; clear - Hxq; lia) STg MIg) as (EVV & LSV & AXO).
        pose proof (ax_pres_trans _ _ _ _ _ _ AXB AXO) as AXB2.
        pose proof U2 as VB2. apply hide_intro in VB2.
        clear MU WM STg MIg FRg FSZg EVg LSg HEAPg PARTSg.
        step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AvR; lia); zify_cond KZ; [exfalso; clear - KZ AvR; lia| clear KZ].
        pose proof EVV as (_ & _ & STV & MIV & _ & _ & _ & _ & FRV & FSZV & _). cbn [app locs] in FRV.

        pose proof U2 as VAL.
        pose proof (obj_acc _ _ _ _ (q, f + 32, 256) (proj1 (proj2 EVV)) ltac:(left; reflexivity)) as ACCL. cbn [blk_addr blk_size fst snd] in ACCL.
        pose proof (munch_refl [] mV) as MU0.
        step. rewrite ?(unsigned_lit (f + 32 + 8 * (Z.of_nat (length vals) - 1))) by (clear - XR; lia).
        step. step. shl_with ACCL ALV. chk0.
        pose proof VT as [VL VT']. pose proof (VT' (length vals - 1)%nat ltac:(clear - K1; lia)) as (Wp & HAprev & (jp & Eprev) & AprevR). clear VT'.
        assert (Wp' : nth_error (Arr.upd ws (length vals) (Z_to_bv 64 av)) (Z.to_nat (Z.of_nat (length vals) - 1)) = Some (Z_to_bv 64 (nth (length vals - 1) addrs 0))).
        { rewrite nth_error_upd_other by (clear - K1; lia). replace (Z.to_nat (Z.of_nat (length vals) - 1)) with (length vals - 1)%nat by (clear; lia). exact Wp. }
        let a := cur_mem_addr in pose proof (u64arr_read bgasegs mV (f + 32) _ (Z.of_nat (length vals) - 1) _ a VAL Wp' ltac:(clear - K1; lia) ltac:(addr_tac)) as RD.
        step. clear RD VAL ACCL MU0.
        do 4 step.
    apply evt_done.
    apply implA_tbind_assoc. eapply implA_bind.
    { eapply (bn_mul_mont_fixed_top_walkA) with (lo := lo) (OW := OWg) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HAv | exact (ref_at_stable _ _ _ _ PL _ _ RSg HAprev) | exact (ref_at_stable _ _ _ _ PL _ _ RSg HAd) | rewrite Ev; exact (hpl_wref _ _ (hpl_pool PL vi)) | exact NROd | rewrite Eprev; apply nbuf_pool | rewrite Ed; apply nbuf_pool | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EVV | exact LSV | exact LOK | clear - KCOST CMM0 MCP BC CFM0 CC; lia].
      - eapply cenv_roomA; [exact EVV | exact ROOMS | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVV).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af330 CTX).
    }
    cbv beta. intros [um lsm] Σm msm PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVV))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fm & fcm & mm & OWm & PLm & -> & CPm & (EPLm & ->)).
    subst PLm. specialize (CPm eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mV _ _ _ _ _ _ _ _ _ _ _ EVV CPm) as (EVm & LSm).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPm) as RSm. clear CPm.
    rewrite (ret_pc_even 2815256) by (clear; lia).
        pose proof (refs_stable_trans _ _ _ _ _ _ RSg RSm) as RSgm.
        assert (VT2 : vtab lsm OWm (Arr.upd ws (length vals) (Z_to_bv 64 av)) (vals ++ [ug]) (addrs ++ [av])).
        { apply (vtab_stable lsg OWg); [|exact RSm]. eapply vtab_snoc; [eapply vtab_stable; [exact VT| exact RSg]| rewrite LEN; exact K32| exact HAv| exact Ev| exact AvR]. }
        apply hide_elim in VB2.
        unfold MallocRep.wz. apply implA_from_evt. step. if_false.
        pose proof EVm as (_ & _ & STm & MIm & _ & _ & _ & _ & FRm & FSZm & _). cbn [app locs] in FRm.
        step. step.

          rewrite (unsigned_lit (Z.of_nat (length vals) + 1)) by (clear - K32; lia). rewrite (unsigned_lit (window - 1)) by (clear - WB; lia).
          rewrite (Z.mod_small (window - 1) 32) by (clear - WB; lia).
          unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small (Z.of_nat (length vals) + 1)) by (clear - K32; lia).
          rewrite Z.shiftr_div_pow2 by (clear - WB; lia).
          assert (PP : 0 < 2 ^ (window - 1)) by (apply Z.pow_pos_nonneg; clear - WB; lia).
          replace ((Z.of_nat (length vals) + 1) / 2 ^ (window - 1)) with 1 by (replace (Z.of_nat (length vals) + 1) with (2 ^ (window - 1)) by (clear - KC; lia); symmetry; apply Z.div_same; clear - PP; lia).
          rewrite (bn_swrap32_small 1) by (clear; lia).
          step. step. step. step. if_true.
          rewrite exp_table_loop_O. cbn [tbind fst snd].
          apply evt_done.
          eapply (L_gueron mV (used + MC + CMM) Σm lsm mm OWm (Arr.upd ws (length vals) (Z_to_bv 64 av)) (vals ++ [ug]) (addrs ++ [av]) bits window rq ar ri);
            [ exact EVm | exact LSm | exact AXB2 | exact VB2 | etransitivity; [apply Arr.upd_length| exact LEN] | exact VT2
            | rewrite length_app; cbn [length]; replace (1 <? window) with true by (symmetry; apply Z.ltb_lt; clear - WB; lia); clear - KC; lia
            | clear - WB; lia | exact BITS | exact (ref_at_stable _ _ _ _ PL _ _ RSgm HAqK) | exact Er | clear - KCOST; lia ].
        -
          replace (Z.of_nat (S (S c)) * (MC + CMM)) with ((MC + CMM) + Z.of_nat (S c) * (MC + CMM)) in KCOST by (clear; lia).
          assert (CC : 0 <= Z.of_nat (S c) * (MC + CMM)) by (apply Z.mul_nonneg_nonneg; [clear; lia | clear - MCP CMM0; lia]).
    apply evt_done.
    apply implA_tbind_assoc. eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OWK) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HPCS | reflexivity].
      - eapply cenv_preA; [exact EVK | exact LSK | clear - LOK CSget; lia | clear - KCOST CMM0 MCP BC CFM0 CC; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVK).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af2e8 CTX).
    }
    cbv beta. intros [ug lsg] Σg msg PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVK))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fg & fcg & mg & OWg & PLg & -> & CPg & (EPLg & (vi & Ev) & (av & HAv & ->) & INCLg)).
    subst PLg. specialize (CPg eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVK CPg) as (EVg & LSg).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPg) as RSg. clear CPg.
    rewrite (ret_pc_even 2815184) by (clear; lia).
        pose proof (proj1 (proj2 EVg)) as HEAPg. pose proof (lib_state_h_parts _ _ _ _ _ _ LSg) as PARTSg.
        assert (NROv : ug <> ROne) by (rewrite Ev; unfold RPool, ROne, NFIX; clear; lia).
        pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPg PARTSg FROKK HAv NROv) as (Av0 & AvC & _).
        assert (AvR : 0 < av < 2^64) by (unfold BnHeapA.ACEIL, STACK_WIN in *; clear - Av0 AvC CE1 CE2 CE3; lia). clear AvC.
        unfold MallocRep.wz.

        pose proof EVg as (_ & _ & STg & MIg & _ & _ & _ & _ & FRg & FSZg & _). cbn [app locs] in FRg.
        pose proof (obj_arrA (q, f + 32, 256) LB PL lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ ws EVg VB
                      ltac:(cbn [blk_size snd]; rewrite LEN; reflexivity) ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFV; clear - Hxq; lia)) as VA.
        cbn [blk_addr fst snd] in VA.
        pose proof (obj_acc _ _ _ _ (q, f + 32, 256) HEAPg ltac:(left; reflexivity)) as ACCV. cbn [blk_addr blk_size fst snd] in ACCV.
        assert (IDX : 0 <= Z.of_nat (length vals) < Z.of_nat (length ws)) by (rewrite LEN; clear - K32; lia).
        assert (XR : 0 <= f + 32 + 8 * (Z.of_nat (length vals) - 1) /\ f + 32 + 8 * Z.of_nat (length vals) + 8 <= f + 32 + 256 /\ f + 288 < 2 ^ 64) by (clear - K1 K32 G1 G3 CE1 CE2 CE3; lia).
        pose proof (munch_refl [(f + 32, f + 288)]%Z mg) as MU. pose proof (wmono_refl bgasegs mg) as WM.
        apply implA_from_evt.
        step. rewrite ?(unsigned_lit (f + 32 + 8 * (Z.of_nat (length vals) - 1))) by (clear - XR; lia).
        replace (f + 32 + 8 * (Z.of_nat (length vals) - 1) + 8) with (f + 32 + 8 * Z.of_nat (length vals)) by (clear; lia).
        step. rewrite ?(unsigned_lit (f + 32 + 8 * Z.of_nat (length vals))) by (clear - XR; lia).
        step. step. shl_with ACCV ALV. chk0.
        pose proof (u64arr_store_ok bgasegs mg (f + 32) ws (Z.of_nat (length vals)) (wa (f + 32 + 8 * Z.of_nat (length vals))) VA IDX eq_refl) as SOKW.
        pose proof (u64arr_write bgasegs mg (f + 32) ws (Z.of_nat (length vals)) (Z_to_bv 64 av) VA IDX) as U2.
        clear ACCV.
        step. store_done.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mV end.
        rewrite Nat2Z.id in U2.
        destruct (cenv_objA (q, f + 32, 256) LB PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ EVg LSg MU WM
                    ltac:(constructor; [cbn [blk_addr blk_size fst snd]; clear; lia | constructor])
                    ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFV; clear - Hxq; lia) STg MIg) as (EVV & LSV & AXO).
        pose proof (ax_pres_trans _ _ _ _ _ _ AXB AXO) as AXB2.
        pose proof U2 as VB2. apply hide_intro in VB2.
        clear MU WM STg MIg FRg FSZg EVg LSg HEAPg PARTSg.
        step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AvR; lia); zify_cond KZ; [exfalso; clear - KZ AvR; lia| clear KZ].
        pose proof EVV as (_ & _ & STV & MIV & _ & _ & _ & _ & FRV & FSZV & _). cbn [app locs] in FRV.

        pose proof U2 as VAL.
        pose proof (obj_acc _ _ _ _ (q, f + 32, 256) (proj1 (proj2 EVV)) ltac:(left; reflexivity)) as ACCL. cbn [blk_addr blk_size fst snd] in ACCL.
        pose proof (munch_refl [] mV) as MU0.
        step. rewrite ?(unsigned_lit (f + 32 + 8 * (Z.of_nat (length vals) - 1))) by (clear - XR; lia).
        step. step. shl_with ACCL ALV. chk0.
        pose proof VT as [VL VT']. pose proof (VT' (length vals - 1)%nat ltac:(clear - K1; lia)) as (Wp & HAprev & (jp & Eprev) & AprevR). clear VT'.
        assert (Wp' : nth_error (Arr.upd ws (length vals) (Z_to_bv 64 av)) (Z.to_nat (Z.of_nat (length vals) - 1)) = Some (Z_to_bv 64 (nth (length vals - 1) addrs 0))).
        { rewrite nth_error_upd_other by (clear - K1; lia). replace (Z.to_nat (Z.of_nat (length vals) - 1)) with (length vals - 1)%nat by (clear; lia). exact Wp. }
        let a := cur_mem_addr in pose proof (u64arr_read bgasegs mV (f + 32) _ (Z.of_nat (length vals) - 1) _ a VAL Wp' ltac:(clear - K1; lia) ltac:(addr_tac)) as RD.
        step. clear RD VAL ACCL MU0.
        do 4 step.
    apply evt_done.
    apply implA_tbind_assoc. eapply implA_bind.
    { eapply (bn_mul_mont_fixed_top_walkA) with (lo := lo) (OW := OWg) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HAv | exact (ref_at_stable _ _ _ _ PL _ _ RSg HAprev) | exact (ref_at_stable _ _ _ _ PL _ _ RSg HAd) | rewrite Ev; exact (hpl_wref _ _ (hpl_pool PL vi)) | exact NROd | rewrite Eprev; apply nbuf_pool | rewrite Ed; apply nbuf_pool | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EVV | exact LSV | exact LOK | clear - KCOST CMM0 MCP BC CFM0 CC; lia].
      - eapply cenv_roomA; [exact EVV | exact ROOMS | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVV).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af330 CTX).
    }
    cbv beta. intros [um lsm] Σm msm PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVV))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fm & fcm & mm & OWm & PLm & -> & CPm & (EPLm & ->)).
    subst PLm. specialize (CPm eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mV _ _ _ _ _ _ _ _ _ _ _ EVV CPm) as (EVm & LSm).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPm) as RSm. clear CPm.
    rewrite (ret_pc_even 2815256) by (clear; lia).
        pose proof (refs_stable_trans _ _ _ _ _ _ RSg RSm) as RSgm.
        assert (VT2 : vtab lsm OWm (Arr.upd ws (length vals) (Z_to_bv 64 av)) (vals ++ [ug]) (addrs ++ [av])).
        { apply (vtab_stable lsg OWg); [|exact RSm]. eapply vtab_snoc; [eapply vtab_stable; [exact VT| exact RSg]| rewrite LEN; exact K32| exact HAv| exact Ev| exact AvR]. }
        apply hide_elim in VB2.
        unfold MallocRep.wz. apply implA_from_evt. step. if_false.
        pose proof EVm as (_ & _ & STm & MIm & _ & _ & _ & _ & FRm & FSZm & _). cbn [app locs] in FRm.
        step. step.

          rewrite (unsigned_lit (Z.of_nat (length vals) + 1)) by (clear - K32; lia). rewrite (unsigned_lit (window - 1)) by (clear - WB; lia).
          rewrite (Z.mod_small (window - 1) 32) by (clear - WB; lia).
          unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small (Z.of_nat (length vals) + 1)) by (clear - K32; lia).
          rewrite Z.shiftr_div_pow2 by (clear - WB; lia).
          assert (PP : 0 < 2 ^ (window - 1)) by (apply Z.pow_pos_nonneg; clear - WB; lia).
          replace ((Z.of_nat (length vals) + 1) / 2 ^ (window - 1)) with 0 by (symmetry; apply Z.div_small; clear - KC PP; lia).
          rewrite (bn_swrap32_small 0) by (clear; lia).
          step. step. step. step. if_false. step.
          rewrite ?(unsigned_lit (f + 32 + 8 * Z.of_nat (length vals))) by (clear - XR; lia).
          rewrite ?(unsigned_lit (Z.of_nat (length vals) + 1)) by (clear - K32; lia).

          replace (Z_to_bv 64 (Z.of_nat (length vals) + 2)) with (Z_to_bv 64 (Z.of_nat (length (vals ++ [ug])) + 1)) by (rewrite length_app; cbn [length]; f_equal; clear; lia).
          replace (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length vals) + 8)) with (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length (vals ++ [ug])))) by (rewrite length_app; cbn [length]; f_equal; clear; lia).
          replace (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length vals))) with (Z_to_bv 64 (f + 32 + 8 * (Z.of_nat (length (vals ++ [ug])) - 1))) by (rewrite length_app; cbn [length]; f_equal; clear; lia).
          apply evt_done.
          eapply (IH (vals ++ [ug]) (addrs ++ [av]) mV (used + MC + CMM) Σm lsm mm OWm (Arr.upd ws (length vals) (Z_to_bv 64 av)) bits window d rq ad ar di ri);
            [ exact EVm | exact LSm | exact AXB2 | exact VB2 | etransitivity; [apply Arr.upd_length| exact LEN] | exact VT2
            | rewrite length_app; cbn [length]; clear; lia | rewrite length_app; cbn [length]; clear - KC; lia | exact WB | exact BITS
            | exact (ref_at_stable _ _ _ _ PL _ _ RSgm HAd) | exact Ed | exact (ref_at_stable _ _ _ _ PL _ _ RSgm HAqK) | exact Er | clear - KCOST; lia ].
      Qed.

      Lemma vtab_one : forall lsK OWK ws v0 av0 vi, nth_error ws 0 = Some (Z_to_bv 64 av0) -> ref_at lsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 ->
        vtab lsK OWK ws [v0] [av0].
      Proof.
        intros lsK OWK ws v0 av0 vi W0 HAv Ev AvR. split; [reflexivity|]. intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by (clear - Hi; lia). subst i. cbn [nth].
        split; [exact W0|]. split; [exact HAv|]. split; [exists vi; exact Ev| exact AvR].
      Qed.

      Lemma L_tableW : forall mb used ΣK lsK mK OWK ws (bits window : Z) (d v0 rq : bnref) (ad av0 ar : Z) (di vi ri : nat) (w0 w1 w2 w3 w10 w12 w16 w17 : word)
          (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x21 x24 t3 t4 t5 t6 : word) (x23 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 w2 w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 (shad (arm + 8))) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) (Z_to_bv 64 ad) w10 (Z_to_bv 64 0) w12 (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgasegs mb (f + 32) ws -> length ws = 32%nat -> nth_error ws 0 = Some (Z_to_bv 64 av0) ->
        ref_at lsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 ->
        ref_at lsK OWK PL d ad -> d = RPool di -> ref_at lsK OWK PL rq ar -> rq = RPool ri ->
        3 <= window <= 6 -> 0 < bits <= 32768 ->
        used + 33 * (MC + CMM) + MC + CMM + 2 * bits * CMM + CFM <= TOTAL ->
        implA (tbind (exp_table ops MUL window v0 d lsK) (fun p => mont_gueron bits window rr rp rm rq (fst p) qm (snd p))) ΣK Q
          (bst x1 t0 t1 t2 (Z_to_bv 64 window) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ac) x21 x23 x24 (Z_to_bv 64 av0) (Z_to_bv 64 arm) (Z_to_bv 64 am) t3 t4 t5 t6 F 2815108 fc mK).
      Proof.
        intros until fc; intros EVK LSK AXB VB LEN W0 HAv0 Ev AvR HAd Ed HAqK Er WB BITS KCOST. kit EVK. unfold bst, MallocRep.wz in *.
        assert (BC : 0 <= bits * CMM) by (apply Z.mul_nonneg_nonneg; [clear - BITS; lia | exact CMM0]).
        assert (P5 : 4 <= 2 ^ (window - 1) <= 32).
        { split; [change 4 with (2 ^ 2) | change 32 with (2 ^ 5)]; apply Z.pow_le_mono_r; clear - WB; lia. }
        unfold exp_table. replace (1 <? window) with true by (symmetry; apply Z.ltb_lt; clear - WB; lia).
        unfold bbind at 1. cbn [bind tree_ops].
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        pose proof (munch_refl [(spa, spa + 152)]%Z mK) as MU. pose proof (wmono_refl bgasegs mK) as WM.
        apply implA_from_evt. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
        relocal EVK LSK MU WM STK MIK FRK FSZK EVS LSS. clear MU WM STK MIK FSZK.
        do 5 step. step.
    apply evt_done.
    apply implA_tbind_assoc. eapply implA_bind.
    { eapply (bn_mul_mont_fixed_top_walkA) with (lo := lo) (OW := OWK) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HAd | exact HAv0 | exact HAv0 | rewrite Ed; exact (hpl_wref _ _ (hpl_pool PL di)) | rewrite Ev; unfold RPool, ROne, NFIX; clear; lia | rewrite Ev; apply nbuf_pool | rewrite Ev; apply nbuf_pool | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EVS | exact LSS | exact LOK | clear - KCOST CMM0 MCP BC CFM0; lia].
      - eapply cenv_roomA; [exact EVS | exact ROOMS | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVS).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af2b8 CTX).
    }
    cbv beta. intros [ud lsd] Σd msd PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVS))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fd & fcd & md & OWd & PLd & -> & CPd & (EPLd & ->)).
    subst PLd. specialize (CPd eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVS CPd) as (EVd & LSd).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPd) as RSd. clear CPd.
    rewrite (ret_pc_even 2815136) by (clear; lia).
        unfold MallocRep.wz. apply implA_from_evt. step. if_false.
        pose proof EVd as (_ & _ & STd & MId & _ & _ & _ & _ & FRd & FSZd & _). cbn [app locs] in FRd.
        pose proof (munch_refl [(spa, spa + 152)]%Z md) as MU. pose proof (wmono_refl bgasegs md) as WM.
        step. step.
        step.   rewrite ?(unsigned_lit window) by (clear - WB; lia). replace (window + -1) with (window - 1) by (clear; lia).
        step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT end.
        relocal EVd LSd MU WM STd MId FRd FSZd EVT LST. clear MU WM STd MId FSZd.
        do 5 step.

        replace (Z_to_bv 64 (f + 40)) with (Z_to_bv 64 (f + 32 + 8 * Z.of_nat (length [v0]))) by (cbn [length]; f_equal; clear; lia).
        replace (Z_to_bv 64 (f + 32)) with (Z_to_bv 64 (f + 32 + 8 * (Z.of_nat (length [v0]) - 1))) by (cbn [length]; f_equal; clear; lia).
        change (Z_to_bv 64 2) with (Z_to_bv 64 (Z.of_nat (length [v0]) + 1)).
        cbv beta. cbn [fst snd].
        replace (Z.to_nat (2 ^ (window - 1)) - 1)%nat with (S (Z.to_nat (2 ^ (window - 1)) - 2)) by (clear - P5; lia).
        apply evt_done.
        eapply (table_loopA (Z.to_nat (2 ^ (window - 1)) - 2) [v0] [av0] mb (used + CMM) Σd lsd mT OWd ws bits window d rq ad ar di ri);
          [ exact EVT | exact LST | exact AXB | exact VB | exact LEN | eapply vtab_one; [exact W0 | exact (ref_at_stable _ _ _ _ PL _ _ RSd HAv0) | exact Ev | exact AvR]
          | cbn [length]; clear; lia | cbn [length]; clear - P5; lia | clear - WB; lia | exact BITS
          | exact (ref_at_stable _ _ _ _ PL _ _ RSd HAd) | exact Ed | exact (ref_at_stable _ _ _ _ PL _ _ RSd HAqK) | exact Er | ].
        assert (CN : Z.of_nat (S (Z.to_nat (2 ^ (window - 1)) - 2)) <= 32) by (clear - P5; lia).
        assert (CP : Z.of_nat (S (Z.to_nat (2 ^ (window - 1)) - 2)) * (MC + CMM) <= 32 * (MC + CMM)) by (apply Z.mul_le_mono_nonneg_r; [clear - MCP CMM0; lia | exact CN]).
        clear - KCOST CP MCP CMM0. lia.
      Qed.

      Lemma L_cascade : forall mb used ΣK lsK mK OWK ws (bits : Z) (d v0 rq : bnref) (ad av0 ar : Z) (di vi ri : nat) (w0 w1 w2 w3 w10 w12 w16 w17 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x24 t3 t4 t5 t6 : word) (x23 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 w2 w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 (shad (arm + 8))) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) (Z_to_bv 64 ad) w10 (Z_to_bv 64 0) w12 (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgasegs mb (f + 32) ws -> length ws = 32%nat -> nth_error ws 0 = Some (Z_to_bv 64 av0) ->
        ref_at lsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 ->
        ref_at lsK OWK PL d ad -> d = RPool di -> ref_at lsK OWK PL rq ar -> rq = RPool ri ->
        0 < bits <= 32768 ->
        used + 33 * (MC + CMM) + MC + CMM + 2 * bits * CMM + CFM <= TOTAL ->
        implA (tbind (exp_table ops MUL (window_bits bits) v0 d lsK) (fun p => mont_gueron bits (window_bits bits) rr rp rm rq (fst p) qm (snd p))) ΣK Q
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ac) x21 x23 x24 (Z_to_bv 64 av0) (Z_to_bv 64 arm) (Z_to_bv 64 am) t3 t4 t5 t6 F 2814916 fc mK).
      Proof.
        intros until fc; intros EVK LSK AXB VB LEN W0 HAv0 Ev AvR HAd Ed HAqK Er BITS KCOST. kit EVK. unfold bst, MallocRep.wz in *.
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        unfold window_bits.
        apply implA_from_evt.
        step. step.
        step. rewrite lts_signed by (clear - BITS; lia).
        destruct (Z.ltb_spec 671 bits) as [B1|B1]; cbn [negb].
        {
          do 2 step. apply evt_done.
          eapply (L_tableW mb used ΣK lsK mK OWK ws bits 6 d v0 rq ad av0 ar di vi ri);
            [exact EVK | exact LSK | exact AXB | exact VB | exact LEN | exact W0 | exact HAv0 | exact Ev | exact AvR | exact HAd | exact Ed | exact HAqK | exact Er | clear; lia | exact BITS | exact KCOST].
        }
        step.
        step. rewrite lts_signed by (clear - BITS; lia).
        destruct (Z.ltb_spec 239 bits) as [B2|B2]; cbn [negb].
        {
          do 2 step. apply evt_done.
          eapply (L_tableW mb used ΣK lsK mK OWK ws bits 5 d v0 rq ad av0 ar di vi ri);
            [exact EVK | exact LSK | exact AXB | exact VB | exact LEN | exact W0 | exact HAv0 | exact Ev | exact AvR | exact HAd | exact Ed | exact HAqK | exact Er | clear; lia | exact BITS | exact KCOST].
        }
        step.
        step. rewrite lts_signed by (clear - BITS; lia).
        destruct (Z.ltb_spec 79 bits) as [B3|B3]; cbn [negb].
        {
          do 2 step. apply evt_done.
          eapply (L_tableW mb used ΣK lsK mK OWK ws bits 4 d v0 rq ad av0 ar di vi ri);
            [exact EVK | exact LSK | exact AXB | exact VB | exact LEN | exact W0 | exact HAv0 | exact Ev | exact AvR | exact HAd | exact Ed | exact HAqK | exact Er | clear; lia | exact BITS | exact KCOST].
        }
        step.
        step. rewrite lts_signed by (clear - BITS; lia).

        destruct (Z.ltb_spec bits 24) as [B4|B4]; cbn [negb].
        2: { replace (23 <? bits) with true by (symmetry; apply Z.ltb_lt; clear - B4; lia).
             step. apply evt_done.
             eapply (L_tableW mb used ΣK lsK mK OWK ws bits 3 d v0 rq ad av0 ar di vi ri);
               [exact EVK | exact LSK | exact AXB | exact VB | exact LEN | exact W0 | exact HAv0 | exact Ev | exact AvR | exact HAd | exact Ed | exact HAqK | exact Er | clear; lia | exact BITS | exact KCOST]. }

        replace (23 <? bits) with false by (symmetry; apply Z.ltb_ge; clear - B4; lia).
        unfold exp_table. change (1 <? 1) with false. cbv iota. unfold bret. cbn [ret tree_ops tbind fst snd].
        pose proof (munch_refl [(spa, spa + 152)]%Z mK) as MU. pose proof (wmono_refl bgasegs mK) as WM.
        step. step. lstep 1. step.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mW end.
        relocal EVK LSK MU WM STK MIK FRK FSZK EVW LSW. clear MU WM STK MIK FSZK.
        apply evt_done.
        eapply (L_gueron mb used ΣK lsK mW OWK ws [v0] [av0] bits 1 rq ar ri);
          [ exact EVW | exact LSW | exact AXB | exact VB | exact LEN | eapply vtab_one; [exact W0 | exact HAv0 | exact Ev | exact AvR]
          | reflexivity | clear; lia | exact BITS | exact HAqK | exact Er | clear - KCOST MCP CMM0; lia ].
      Qed.

      Lemma BN_ucmp_eq : forall (s : bstate bptr) r1 r2, Z.land (bn_flags (getbn r1 s)) 4 = 0 -> Z.land (bn_flags (getbn r2 s)) 4 = 0 ->
        BN_ucmp ops r1 r2 s = TRet (ucmp_pure (getbn r1 s) (getbn r2 s), s).
      Proof. intros s r1 r2 H1 H2. unfold BN_ucmp, bbind, bget, bret, bunr, has_flag, BN_FLG_CONSTTIME. cbn [bind ret unreachable tree_ops tbind fst snd]. rewrite H1, H2. reflexivity. Qed.

      Lemma L_tail : forall mb used ΣK lsK mK OWK ws (bits : Z) (d v0 rq : bnref) (ad av0 ar : Z) (di vi ri : nat) (w11 w0 w1 w2 w3 w10 w12 w16 w17 : word)
          (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
        CENV mb (locs w0 w1 w2 w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 (shad (arm + 8))) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) (Z_to_bv 64 ad) w10 w11 w12 (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK -> lib_state lsK mK OWK PL EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
        u64arr bgasegs mb (f + 32) ws -> length ws = 32%nat -> nth_error ws 0 = Some (Z_to_bv 64 av0) ->
        ref_at lsK OWK PL v0 av0 -> v0 = RPool vi -> 0 < av0 < 2 ^ 64 ->
        ref_at lsK OWK PL d ad -> d = RPool di -> ref_at lsK OWK PL rq ar -> rq = RPool ri ->
        0 < bits <= 32768 ->
        used + BN_NNMOD_COST + CMM + 33 * (MC + CMM) + MC + CMM + 2 * bits * CMM + CFM <= TOTAL ->
        implA (mont_tail bits rr ra_ rp rm d rq v0 qm lsK) ΣK Q
          (bst x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 ac) x21 (Z_to_bv 64 0) (Z_to_bv 64 ara) (Z_to_bv 64 av0) (Z_to_bv 64 arm) x27 t3 t4 t5 t6 F 2814808 fc mK).
      Proof.
        intros until fc; intros EVK LSK AXB VB LEN W0 HAv0 Ev AvR HAd Ed HAqK Er BITS KCOST. kit EVK. unfold bst, MallocRep.wz in *.
        pose proof EVK as (_ & HEAPK & _ & _ & _ & _ & _ & RSK & _).
        pose proof (lib_state_h_parts _ _ _ _ _ _ LSK) as PARTSK.
        pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAaS) as HAaK. pose proof (ref_at_stable _ _ _ _ PL _ _ RSK HAmS) as HAmK.
        assert (HVa : vref ra_ lsK) by (eapply ref_at_valid; [exact LSK | exact HAaK]).
        assert (HVm : vref rm lsK) by (eapply ref_at_valid; [exact LSK | exact HAmK]).
        pose proof (st_wf_ok _ _ (proj1 PARTSK) HVa NROa) as (_ & _ & _ & OKa4).
        pose proof (st_wf_ok _ _ (proj1 PARTSK) HVm NROm) as (_ & _ & _ & OKm4).
        assert (CTa : Z.land (bn_flags (getbn ra_ lsK)) 4 = 0) by (destruct OKa4 as [E|E]; rewrite E; reflexivity).
        assert (CTm : Z.land (bn_flags (getbn rm lsK)) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
        assert (NNC : 0 <= BN_NNMOD_COST) by (unfold BN_NNMOD_COST, BN_DIV_FT_COST; clear - MCP; unfold MC in *; lia).
        assert (BC : 0 <= bits * CMM) by (apply Z.mul_nonneg_nonneg; [clear - BITS; lia | exact CMM0]).
        destruct (open_for_read LBX PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ 16 EVK LSK HAaK NROa ltac:(clear; lia) LOFB16)
          as (Da & BNa & _ & _ & _ & _ & _ & SEPa & _ & _ & ACCa & ALa & _ & _ & _ & _ & Aa0).
        unfold USTACK_TOP in SPT. unfold BnRepDefs.bn_cells in BNa.
        set (ba := getbn ra_ lsK) in *.

        assert (TOM : forall (aa : bnref) (aaddr : Z) used1 Σa ls1 ma OW1 (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x21' x27' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
              CENV mb (locs w0 w1 w2 w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 (shad (arm + 8))) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) (Z_to_bv 64 ad) w10 (Z_to_bv 64 0) w12 (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used1 Σa ls1 ma OW1 -> lib_state ls1 ma OW1 PL EA -> refs_stable lsK OWK ls1 OW1 ->
              ref_at ls1 OW1 PL aa aaddr -> nbuf PL aa ->
              used1 + CMM + 33 * (MC + CMM) + MC + CMM + 2 * bits * CMM + CFM <= TOTAL ->
              implA (tbind (bn_to_mont_fixed_top ops v0 aa ls1)
                       (fun p => tbind (exp_table ops MUL (window_bits bits) v0 d (snd p)) (fun p0 => mont_gueron bits (window_bits bits) rr rp rm rq (fst p0) qm (snd p0)))) Σa Q
                (MS (mkR x1' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) x21' (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 aaddr) (Z_to_bv 64 av0) (Z_to_bv 64 arm) x27' t3' t4' t5' t6')
                    F' (Z_to_bv 64 2814888) fc' None ma (seg_rom bgasegs))).
        { intros until fc'. intros EV1 LS1 RS1 HAaa NBaa KCOST1.
          pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HAv0) as HAv1.
          pose proof EV1 as (_ & _ & ST1 & MI1 & _ & _ & _ & _ & FR1 & FSZ1 & _). cbn [app locs] in FR1.
          apply implA_from_evt. do 5 step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (bn_to_mont_fixed_top_walkA) with (lo := lo) (OW := OW1) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | | reflexivity | exact HAv1 | exact HAaa | rewrite Ev; exact (hpl_wref _ _ (hpl_pool PL vi)) | exact NBaa | exact HPM | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV1 | exact LS1 | exact LOK | clear - KCOST1 CMM0 MCP BC CFM0; lia].
      - eapply cenv_roomA; [exact EV1 | exact ROOMS | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV1).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af1d8 CTX).
    }
    cbv beta. intros [ut lst] Σt mst PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV1))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Ft & fct & mt & OWt & PLt & -> & CPt & (EPLt & ->)).
    subst PLt. specialize (CPt eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EV1 CPt) as (EVt & LSt).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPt) as RSt. clear CPt.
    rewrite (ret_pc_even 2814912) by (clear; lia).
          cbv beta. cbn [fst snd].
          unfold MallocRep.wz. apply implA_from_evt. step. if_false.
          apply evt_done.
          eapply (L_cascade mb (used1 + CMM) Σt lst mt OWt ws bits d v0 rq ad av0 ar di vi ri);
            [ exact EVt | exact LSt | exact AXB | exact VB | exact LEN | exact W0 | exact (ref_at_stable _ _ _ _ PL _ _ RSt HAv1) | exact Ev | exact AvR
            | exact (ref_at_stable _ _ _ _ PL _ _ (refs_stable_trans _ _ _ _ _ _ RS1 RSt) HAd) | exact Ed
            | exact (ref_at_stable _ _ _ _ PL _ _ (refs_stable_trans _ _ _ _ _ _ RS1 RSt) HAqK) | exact Er | exact BITS | clear - KCOST1; lia ]. }

        assert (NNM : forall used1 Σb ls1 mc OW1 (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x21' x27' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
              CENV mb (locs w0 w1 w2 w3 (Z_to_bv 64 arr) (Z_to_bv 64 ar) (Z_to_bv 64 (shad (arm + 8))) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 bits) (Z_to_bv 64 ad) w10 (Z_to_bv 64 0) w12 (Z_to_bv 64 am) (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used1 Σb ls1 mc OW1 -> lib_state ls1 mc OW1 PL EA -> refs_stable lsK OWK ls1 OW1 ->
              used1 + BN_NNMOD_COST + CMM + 33 * (MC + CMM) + MC + CMM + 2 * bits * CMM + CFM <= TOTAL ->
              implA (tbind (tbind (BN_nnmod ops v0 ra_ rm ls1) (fun p => TRet (v0, snd p)))
                       (fun pa => tbind (bn_to_mont_fixed_top ops v0 (fst pa) (snd pa))
                          (fun p => tbind (exp_table ops MUL (window_bits bits) v0 d (snd p)) (fun p0 => mont_gueron bits (window_bits bits) rr rp rm rq (fst p0) qm (snd p0))))) Σb Q
                (MS (mkR x1' (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                         (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) x21' (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 ara) (Z_to_bv 64 av0) (Z_to_bv 64 arm) x27' t3' t4' t5' t6')
                    F' (Z_to_bv 64 2814860) fc' None mc (seg_rom bgasegs))).
        { intros until fc'. intros EV1 LS1 RS1 KCOST1.
          pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HAv0) as HAv2. pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HAaK) as HAa2.
          pose proof (ref_at_stable _ _ _ _ PL _ _ RS1 HAmK) as HAm2.
          apply implA_from_evt. do 4 step. step.
          apply evt_done. apply implA_tbind_assoc.
    eapply implA_bind.
    { eapply (BN_nnmod_walkA) with (lo := lo) (OW := OW1) (LB := ((q, f + 32, 256) :: LB)) (PL := PL) (EA := EA);
        [| | | reflexivity | exact HAv2 | exact HAa2 | exact HAm2 | rewrite Ev; apply hpl_pool | exact NROa | exact NROm | exact (nbuf_pl_mont _ _ _ NBa) | exact HPCS | reflexivity | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EV1 | exact LS1 | clear - LOK CSnnmod; lia | clear - KCOST1 CMM0 MCP BC CFM0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EV1).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af1b8 CTX).
    }
    cbv beta. intros [un lsn] Σn msn PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EV1))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fn & fcn & mn & OWn & PLn & -> & CPn & (EPLn & ->)).
    subst PLn. specialize (CPn eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EV1 CPn) as (EVn & LSn).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPn) as RSn. clear CPn.
    rewrite (ret_pc_even 2814880) by (clear; lia).
          cbv beta. cbn [fst snd tbind].
          unfold MallocRep.wz. apply implA_from_evt. step. step. if_false.
          apply evt_done.
          eapply (TOM v0 av0 (used1 + BN_NNMOD_COST) Σn lsn mn OWn);
            [ exact EVn | exact LSn | exact (refs_stable_trans _ _ _ _ _ _ RS1 RSn) | exact (ref_at_stable _ _ _ _ PL _ _ RSn HAv2) | rewrite Ev; apply nbuf_pool | clear - KCOST1; lia ]. }
        unfold mont_tail, bbind, bget. cbn [bind ret tree_ops tbind fst snd]. cbv beta. fold ba.
        rewrite (BN_ucmp_eq lsK ra_ rm CTa CTm). cbn [tbind fst snd].
        pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & _ & FRK & FSZK & _). cbn [app locs] in FRK.
        pose proof (munch_refl [(spa, spa + 152)]%Z mK) as MU. pose proof (wmono_refl bgasegs mK) as WM.
        pose proof (munch_refl (@nil (Z * Z)) mK) as MU0.
        apply implA_from_evt.
        do 4 step. shl_with ACCa ALa. chk0.
        step. unfold MallocRep.wz. rewrite (sx32_small (Z.b2z (bn_neg ba))) by (clear; destruct (bn_neg ba); cbn; lia).
        clear MU0. lstep 0.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
        relocal EVK LSK MU WM STK MIK FRK FSZK EVS LSS. clear MU WM STK MIK FSZK FRK.
        destruct (bn_neg ba) eqn:NEG; cbn [Z.b2z orb].
        -
          step. if_true.
          apply evt_done. eapply NNM; [exact EVS | exact LSS | apply refs_stable_refl | clear - KCOST; lia].
        -
          step. if_false.
          do 2 step. step.
          eapply evt_cut.
          { eapply (BN_ucmp_evtA) with (lo := lo) (OW := OWK) (LB := LBX) (PL := PL) (EA := EA) (r1 := ra_) (r2 := rm) (a := ara) (b := arm);
              [ eapply cenv_preA; [exact EVS | exact LSS | clear - LOK CSucmp; lia | clear - KCOST NNC CMM0 MCP BC CFM0; lia]
              | reflexivity | exact HAaK | exact HAmK | exact NROa | exact NROm | reflexivity | reflexivity ]. }
          intros msc PO.
          apply (bn_postA_cpost LBX PL EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK | exact (proj1 (proj2 EVS))].
          cbn [fst snd] in PO.
          destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fc & fcc & mc & OWc & PLc & -> & CPc & (EPLc & -> & CRc & _ & EOWc)).
          subst PLc. specialize (CPc eq_refl).
          destruct (cenv_postA LBX PL EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mb _ _ _ _ _ _ _ _ _ _ _ EVS CPc) as (EVc & LSc).
          pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPc) as RSc. clear CPc.
          rewrite (ret_pc_even 2814856) by (clear; lia).
          replace (used + 0) with used in EVc by (clear; lia).
          unfold ba in *. set (c := ucmp_pure (getbn ra_ lsK) (getbn rm lsK)) in *.
          step. rewrite lts_signed by (clear - CRc; lia).
          destruct (Z.ltb_spec c 0) as [CL|CG]; cbn [negb].
          +
            replace (0 <=? c) with false by (symmetry; apply Z.leb_gt; exact CL). cbv iota. rewrite tbind_bret. cbv beta. cbn [fst snd].
            apply evt_done.
            eapply (TOM ra_ ara used); [exact EVc | exact LSc | exact RSc | exact (ref_at_stable _ _ _ _ PL _ _ RSc HAaK) | exact (nbuf_pl_mont _ _ _ NBa) | clear - KCOST NNC; lia].
          + replace (0 <=? c) with true by (symmetry; apply Z.leb_le; exact CG). cbv iota.
            apply evt_done. eapply NNM; [exact EVc | exact LSc | exact RSc | clear - KCOST; lia].
      Qed.

    End Scope.

    Hypothesis GFILLF : forall am qm, GFILL_stmt am qm.

    Lemma L_rest : forall mb used ΣK lsK mK OWK (bits : Z) (jv : list byte) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w16 w17 : word)
        (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
      cenvA LBX PL0 lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb (locs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) used ΣK lsK mK OWK ->
      lib_state lsK mK OWK PL0 EA -> ax_pres LB (bv_unsigned sp) (XW PL0) m1 mb ->
      rw_cells bgasegs mb (f + 32) [CB 256 jv] ->
      0 < bits <= 32768 ->
      used + 4 * MC + MC + CMS + BN_NNMOD_COST + CMM + 33 * (MC + CMM) + MC + CMM + 2 * bits * CMM + CFM <= TOTAL ->
      implA (mont_rest bits rr ra_ rp rm lsK) ΣK Q
        (MS (mkR x1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 bits) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 ac) (Z_to_bv 64 ara) (Z_to_bv 64 f) (Z_to_bv 64 0) (Z_to_bv 64 (arm + 8)) (Z_to_bv 64 arr) (Z_to_bv 64 arm)
                 (Z_to_bv 64 (shad (arm + 8))) t3 t4 t5 t6)
            F (Z_to_bv 64 2814696) fc None mK (seg_rom bgasegs)).
    Proof.
      intros until fc; intros EVK LSK AXB FRV BITS KCOST. kit EVK. unfold MallocRep.wz in *.
      assert (NNC : 0 <= BN_NNMOD_COST) by (unfold BN_NNMOD_COST, BN_DIV_FT_COST; clear - MCP; unfold MC in *; lia).
      assert (BC : 0 <= bits * CMM) by (apply Z.mul_nonneg_nonneg; [clear - BITS; lia | exact CMM0]).
      fgeo (proj1 (proj2 EVK)).
      pose proof EVK as (_ & _ & STK & MIK & _ & _ & _ & RSK & FRK & FSZK & _). cbn [app locs] in FRK.
      pose proof (munch_refl [(spa, spa + 152)]%Z mK) as MU. pose proof (wmono_refl bgasegs mK) as WM.
      unfold mont_rest. unfold bbind at 1. cbn [bind tree_ops].
      apply implA_from_evt. do 7 step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
      relocal EVK LSK MU WM STK MIK FRK FSZK EVS LSS. clear MU WM STK MIK FSZK FRK.
      do 2 step. step.

    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_start_walkA) with (lo := lo) (OW := OWK) (LB := ((q, f + 32, 256) :: LB)) (PL := PL0) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EVS | exact LSS | clear - LOK CSstart; lia | clear - KCOST CMM0 MCP BC CFM0 NNC CMS0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVS).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af128 CTX).
    }
    cbv beta. intros [ucs lscs] Σcs mscs PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVS))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fcs & fccs & mcs & OWcs & PLcs & -> & CPcs & (EPLcs & INCLcs)).
    subst PLcs. specialize (CPcs eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVS CPcs) as (EVcs & LScs).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPcs) as RScs. clear CPcs.
    rewrite (ret_pc_even 2814736) by (clear; lia).
      cbv beta. cbn [fst snd]. unfold bbind at 1. cbn [bind tree_ops].
      unfold MallocRep.wz. apply implA_from_evt. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OWcs) (LB := ((q, f + 32, 256) :: LB)) (PL := PL0) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EVcs | exact LScs | clear - LOK CSget; lia | clear - KCOST CMM0 MCP BC CFM0 NNC CMS0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVcs).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af130 CTX).
    }
    cbv beta. intros [ug1 lsg1] Σg1 msg1 PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVcs))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fg1 & fcg1 & mg1 & OWg1 & PLg1 & -> & CPg1 & (EPLg1 & (di & Ed) & (ad & HAd & ->) & INCLg1)).
    subst PLg1. specialize (CPg1 eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVcs CPg1) as (EVg1 & LSg1).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPg1) as RSg1. clear CPg1.
    rewrite (ret_pc_even 2814744) by (clear; lia).
      cbv beta. cbn [fst snd]. unfold bbind at 1. cbn [bind tree_ops].
      pose proof EVg1 as (_ & _ & STg1 & MIg1 & _ & _ & _ & _ & FRg1 & FSZg1 & _). cbn [app locs] in FRg1.
      pose proof (munch_refl [(spa, spa + 152)]%Z mg1) as MU. pose proof (wmono_refl bgasegs mg1) as WM.
      unfold MallocRep.wz. apply implA_from_evt. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT1 end.
      relocal EVg1 LSg1 MU WM STg1 MIg1 FRg1 FSZg1 EVT1 LST1. clear MU WM STg1 MIg1 FSZg1 FRg1.
      step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OWg1) (LB := ((q, f + 32, 256) :: LB)) (PL := PL0) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EVT1 | exact LST1 | clear - LOK CSget; lia | clear - KCOST CMM0 MCP BC CFM0 NNC CMS0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVT1).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af13c CTX).
    }
    cbv beta. intros [ug2 lsg2] Σg2 msg2 PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVT1))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fg2 & fcg2 & mg2 & OWg2 & PLg2 & -> & CPg2 & (EPLg2 & (ri & Er) & (ar & HAq & ->) & INCLg2)).
    subst PLg2. specialize (CPg2 eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVT1 CPg2) as (EVg2 & LSg2).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPg2) as RSg2. clear CPg2.
    rewrite (ret_pc_even 2814756) by (clear; lia).
      cbv beta. cbn [fst snd]. unfold bbind at 1. cbn [bind tree_ops].
      pose proof EVg2 as (_ & _ & STg2 & MIg2 & _ & _ & _ & _ & FRg2 & FSZg2 & _). cbn [app locs] in FRg2.
      pose proof (munch_refl [(spa, spa + 152)]%Z mg2) as MU. pose proof (wmono_refl bgasegs mg2) as WM.
      unfold MallocRep.wz. apply implA_from_evt. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT2 end.
      relocal EVg2 LSg2 MU WM STg2 MIg2 FRg2 FSZg2 EVT2 LST2. clear MU WM STg2 MIg2 FSZg2 FRg2.
      step. step. step.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_CTX_get_walkA) with (lo := lo) (OW := OWg2) (LB := ((q, f + 32, 256) :: LB)) (PL := PL0) (EA := EA);
        [| | | reflexivity | exact HPC | reflexivity].
      - eapply cenv_preA; [exact EVT2 | exact LST2 | clear - LOK CSget; lia | clear - KCOST CMM0 MCP BC CFM0 NNC CMS0; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVT2).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af14c CTX).
    }
    cbv beta. intros [ug3 lsg3] Σg3 msg3 PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVT2))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fg3 & fcg3 & mg3 & OWg3 & PLg3 & -> & CPg3 & (EPLg3 & (vi & Ev) & (av0 & HAv0 & ->) & INCLg3)).
    subst PLg3. specialize (CPg3 eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ _ _ _ EVT2 CPg3) as (EVg3 & LSg3).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPg3) as RSg3. clear CPg3.
    rewrite (ret_pc_even 2814772) by (clear; lia).
      cbv beta. cbn [fst snd].
      pose proof (proj1 (proj2 EVg3)) as HEAPg3. pose proof (lib_state_h_parts _ _ _ _ _ _ LSg3) as PARTSg3.
      assert (NROv : ug3 <> ROne) by (rewrite Ev; unfold RPool, ROne, NFIX; clear; lia).
      pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPg3 PARTSg3 FROKK HAv0 NROv) as (Av0 & AvC & _).
      assert (AvR : 0 < av0 < 2^64) by (unfold BnHeapA.ACEIL, STACK_WIN in *; clear - Av0 AvC CE1 CE2 CE3; lia). clear AvC.
      pose proof EVg3 as (_ & _ & STg3 & MIg3 & _ & _ & _ & _ & FRg3 & FSZg3 & _). cbn [app locs] in FRg3.
      pose proof (munch_refl [(spa, spa + 152)]%Z mg3) as MU. pose proof (wmono_refl bgasegs mg3) as WM.
      unfold MallocRep.wz. apply implA_from_evt. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT3 end.
      relocal EVg3 LSg3 MU WM STg3 MIg3 FRg3 FSZg3 EVT3 LST3. clear MU WM STg3 MIg3 FSZg3 FRg3 HEAPg3 PARTSg3.

      pose proof (obj_keepA (q, f + 32, 256) LB PL0 lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ (f + 32) _ EVT3 FRV
                    ltac:(cbn [blk_addr fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; clear; lia)
                    ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFV; clear - Hxq; lia)) as FRVc.
      pose proof EVT3 as (_ & _ & STc & MIc & _).
      pose proof (munch_refl [(f + 32, f + 288)]%Z mT3) as MU. pose proof (wmono_refl bgasegs mT3) as WM.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mV end.
      destruct (val_obj_init _ _ _ _ FRVc) as (ws0 & LEN0 & WS0 & VB). clear FRVc.
      destruct (cenv_objA (q, f + 32, 256) LB PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW mb _ _ _ _ _ _ _ _ EVT3 LST3 MU WM
                  ltac:(constructor; [cbn [blk_addr blk_size fst snd]; clear; lia | constructor])
                  ltac:(cbn [blk_addr blk_size fst snd]; intros xq Hxq; apply NFV; clear - Hxq; lia) STc MIc) as (EVV & LSV & AXO).
      pose proof (ax_pres_trans _ _ _ _ _ _ AXB AXO) as AXB2.
      apply hide_intro in VB.
      clear MU WM STc MIc EVT3 LST3.
      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AvR; lia); zify_cond KZ; [exfalso; clear - KZ AvR; lia| clear KZ].
      pose proof EVV as (_ & _ & STV & MIV & _ & _ & _ & _ & FRVv & FSZV & _). cbn [app locs] in FRVv.
      pose proof (munch_refl [(spa, spa + 152)]%Z mV) as MU. pose proof (wmono_refl bgasegs mV) as WM.
      step. step. lstep 0.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT4 end.
      relocal EVV LSV MU WM STV MIV FRVv FSZV EVT4 LST4. clear MU WM STV MIV FSZV FRVv.
      step. step.
      step. if_true.
      step.

      apply evt_done.
      eapply (mont_new_callA _ Q LBX PL0 EA lo (bv_unsigned sp) spa s0 ra ras TOTAL Σ1 ls OW mV _ _ (used + 4 * MC + MC));
        [ exact EVT4 | exact LST4 | exact HFM | reflexivity | clear - LOK CSnew; lia | clear; lia | clear - KCOST CMM0 MCP BC CFM0 NNC CMS0; lia | reflexivity
        | clear - TIGHT; unfold block in *; lia
        | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af22c CTX) |].
      intros qm am Σn mn n0 n1 n2 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 Fn fcn AMR EVn LSn.
      rewrite (ret_pc_even 2814996) by (clear; lia). unfold MallocRep.wz.
      pose proof EVn as (OKn & _ & STn & MIn & _ & _ & _ & RSn & FRn & FSZn & _). cbn [app locs] in FRn.
      pose proof (munch_refl [(spa, spa + 152)]%Z mn) as MU. pose proof (wmono_refl bgasegs mn) as WM.
      apply implA_from_evt.
      step. if_cases KZ; rewrite ?unsigned_lit in KZ by (clear - AMR; lia); zify_cond KZ; [exfalso; clear - KZ AMR; lia| clear KZ].
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mT5 end.
      relocal EVn LSn MU WM STn MIn FRn FSZn EVT5 LST5. clear MU WM STn MIn FSZn FRn.
      pose proof (ref_at_stable _ _ _ _ (pl_set_mont PL0 (Some (am, qm))) _ _ RSn (HAmS am qm)) as HAmN.
      do 2 step. step.
      unfold bbind at 1. cbn [bind tree_ops].
      pose proof OKn as OK'.
    apply evt_done.
    eapply implA_bind.
    { eapply (BN_MONT_CTX_set_walkA) with (lo := lo) (OW := ((qm, am, 96) :: OWg3)) (LB := ((q, f + 32, 256) :: LB)) (PL := (pl_set_mont PL0 (Some (am, qm)))) (EA := EA);
        [| | | | reflexivity | exact HAmN | exact NROm | exact (HPM am qm) | exact (HPCS am qm) | exact HFT | reflexivity | reflexivity | reflexivity].
      - eapply cenv_preA; [exact EVT5 | exact LST5 | exact LOK | clear - KCOST CMM0 MCP BC CFM0 NNC CMS0; lia].
      - eapply cenv_roomA; [exact EVT5 | exact (ROOMS am qm) | clear; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVT5).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af240 CTX).
    }
    cbv beta. intros [ums lsms] Σms msms PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) (pl_set_mont PL0 (Some (am, qm))) EA lo (bv_unsigned sp) spa TOTAL Σ1 ls ((qm, am, 96) :: OW)) in PO; [| exact OK' | exact (proj1 (proj2 EVT5))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Fms & fcms & mms & OWms & PLms & -> & CPms & (EPLms & ->)).
    subst PLms. specialize (CPms eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) (pl_set_mont PL0 (Some (am, qm))) EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls ((qm, am, 96) :: OW) mV _ _ _ _ _ _ _ _ _ _ _ EVT5 CPms) as (EVms & LSms).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPms) as RSms. clear CPms.
    rewrite (ret_pc_even 2815016) by (clear; lia).
      cbv beta. cbn [fst snd].
      unfold MallocRep.wz. apply implA_from_evt. step. if_true.
      apply evt_done.
      eapply (L_tail am qm (GFILLF am qm) mV (used + 4 * MC + MC + CMS) Σms lsms mms OWms ws0 bits ug1 ug3 ug2 ad av0 ar di vi ri);
        [ exact EVms | exact LSms | exact AXB2 | apply hide_elim in VB; exact VB | exact LEN0 | exact WS0
        | exact (ref_at_stable _ _ _ _ _ _ _ RSms (ref_at_mont_enter _ _ _ _ _ (qm, am, 96) (Some (am, qm)) HFM HAv0)) | exact Ev | exact AvR
        | exact (ref_at_stable _ _ _ _ _ _ _ RSms (ref_at_mont_enter _ _ _ _ _ (qm, am, 96) (Some (am, qm)) HFM (ref_at_stable _ _ _ _ _ _ _ RSg3 (ref_at_stable _ _ _ _ _ _ _ RSg2 HAd)))) | exact Ed
        | exact (ref_at_stable _ _ _ _ _ _ _ RSms (ref_at_mont_enter _ _ _ _ _ (qm, am, 96) (Some (am, qm)) HFM (ref_at_stable _ _ _ _ _ _ _ RSg3 HAq))) | exact Er | exact BITS | clear - KCOST; lia ].
    Qed.

    Lemma body_main : forall (ra' u0 u1 u2 x10 x11 x12 x13 b4 b5 b6 b7 u3 u4 u5 u6 s8 : word) (F' : bvmap 5 word) (fc' : bv 32) (j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j16 j17 jv : list byte),
      cenvA LBX PL0 lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 ([CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10; CB 8 j11; CB 8 j12; CB 8 j13; CB 8 j14; C8 (Z_to_bv 64 arp); CB 8 j16; CB 8 j17; C8 (Z_to_bv 64 f)] ++ [CB g junk]) 0 Σ1 ls m1 OW ->
      lib_state ls m1 OW PL0 EA ->
      rw_cells bgasegs m1 (f + 32) [CB 256 jv] ->
      implA (BN_mod_exp_mont ops rr ra_ rp rm ls) Σ1 Q
        (MS (mkR ra' (Z_to_bv 64 spa) gp (wz TP_A) u0 u1 u2 sp (Z_to_bv 64 spa) x10 x11 x12 x13 b4 b5 b6 b7
                 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (wz ac) (wz ara) (Z_to_bv 64 f) (wz 0) s8 (wz arr) (wz arm) (Z_to_bv 64 SHB) u3 u4 u5 u6)
            F' (wz EXP_MONT_BODY) fc' None m1 (seg_rom bgasegs)).
    Proof.
      intros until jv. intros EV0 LS0 FRV. kit EV0. unfold MallocRep.wz, EXP_MONT_BODY in *.
      pose proof (proj1 (proj2 EV0)) as HEAP0.
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS0) as PARTS.
      assert (T0 : 0 <= TOTAL) by (pose proof TOTAL_OK as H; unfold EXP_MONT_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H; clear - H MCP CMM0 CFM0 CMS0; unfold MC in *; lia).
      set (ba := getbn ra_ ls). set (bp := getbn rp ls). set (bm := getbn rm ls).
      assert (HVa : vref ra_ ls) by (eapply ref_at_valid; [exact LS0 | exact HAa]).
      assert (HVp : vref rp ls) by (eapply ref_at_valid; [exact LS0 | exact HAp]).
      assert (HVm : vref rm ls) by (eapply ref_at_valid; [exact LS0 | exact HAm]).
      pose proof (st_wf_ok _ _ (proj1 PARTS) HVa NROa) as (_ & _ & _ & OKa4). fold ba in OKa4.
      pose proof (st_wf_ok _ _ (proj1 PARTS) HVp NROp) as (OKp1 & OKp2 & OKp3 & OKp4). fold bp in OKp1, OKp2, OKp3, OKp4.
      pose proof (st_wf_ok _ _ (proj1 PARTS) HVm NROm) as (_ & OKm2 & OKm3 & OKm4). fold bm in OKm2, OKm3, OKm4.
      unfold BG_DMAX in OKp3, OKm3.
      assert (CTa : Z.land (bn_flags ba) 4 = 0) by (destruct OKa4 as [E|E]; rewrite E; reflexivity).
      assert (CTp : Z.land (bn_flags bp) 4 = 0) by (destruct OKp4 as [E|E]; rewrite E; reflexivity).
      assert (CTm : Z.land (bn_flags bm) 4 = 0) by (destruct OKm4 as [E|E]; rewrite E; reflexivity).
      clear OKa4 OKp4 OKm4.
      rewrite BN_mod_exp_mont_eq.
      unfold any_consttime, BN_num_bits, bbind, bget, bret, bunr. cbn [bind ret unreachable tree_ops tbind fst snd fold_right]. cbv beta.
      fold bm.
      apply implA_from_evt.

      step. step.
    eapply (is_odd_callA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EV0 | exact LS0 | exact HAm | exact NROm |].
    intros mA y0A y1A y2A y4A y5A y6A y7A y8A y9A y10A y11A y12A y13A y14A EVA LSA.
      rewrite (ret_pc_even 2814488) by (clear; lia). fold bm.
      destruct (is_odd_pure bm) eqn:ODD; cbn [Z.b2z negb]; [| apply evt_done; apply implA_unr].
      cbv beta. fold ba bp bm. unfold has_flag, BN_FLG_CONSTTIME. rewrite CTa, CTp, CTm. cbn [Z.eqb negb orb andb]. cbv beta.
      step. if_false.

      destruct (open_for_read LBX PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 _ _ _ _ _ _ _ _ 16 EVA LSA HAm NROm ltac:(clear; lia) LOFB16)
        as (Dm & BNm & _ & _ & _ & _ & _ & SEPm & _ & _ & ACCm & ALm & _ & _ & _ & _ & Am0).
      unfold USTACK_TOP in SPT. unfold BnRepDefs.bn_cells in BNm. fold bm in BNm.
      pose proof EVA as (_ & _ & STA & MIA & _ & _ & _ & _ & FRA & FSZA & _). cbn [app] in FRA.
      pose proof (munch_refl [(spa, spa + 152)]%Z mA) as MU. pose proof (wmono_refl bgasegs mA) as WM.
      assert (OFF : offshW [(spa, spa + 152)]) by (cbn [offshW]; unfold SHLO, SHHI, BnHeapA.ACEIL in *; clear - CEIL LOFB FBSP SPT CE1 CE2 CE3; lia).
      do 3 step.
      replace (Z.shiftr (bv_unsigned (Z_to_bv 64 (arm + 8))) 3) with (Z.shiftr (arm + 8) 3) by (rewrite (unsigned_lit (arm + 8)) by (clear - Am0 SEPm SPT FBSP; lia); reflexivity).
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS end.
      relocal EVA LSA MU WM STA MIA FRA FSZA EVS LSS.
      step. replace (Z.shiftr (arm + 8) 3 + SHB) with (shad (arm + 8)) by (unfold shad; rewrite ?Z.shiftr_div_pow2 by (clear; lia); reflexivity).
      shl_with ACCm ALm. chk0.
      step. unfold MallocRep.wz. rewrite (sx32_small (Z.of_nat (bn_top bm))) by (clear - OKm2 OKm3; lia).
      step. step.
      step. rewrite lts_signed by (clear - OKm2 OKm3; lia).
      replace (1048575 <? Z.of_nat (bn_top bm)) with false by (symmetry; apply Z.ltb_ge; clear - OKm2 OKm3; lia). cbn [negb].
      clear MU WM STA MIA FRA FSZA OFF ACCm BNm.

      pose proof EVS as (_ & _ & _ & _ & _ & _ & _ & _ & FRS & _). cbn [app] in FRS.
      step. step. step.
    eapply (get_flags_callA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EVS | exact LSS | exact HAp | exact NROp |].
    intros mB y0B y1B y2B y4B y5B y6B y7B y8B y9B y10B y11B y12B y13B y14B EVB LSB.
      rewrite (ret_pc_even 2814548) by (clear; lia).
      fold bp. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTp.
      step. change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
      step. step. step.
    eapply (get_flags_callA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EVB | exact LSB | exact HAa | exact NROa |].
    intros mC y0C y1C y2C y4C y5C y6C y7C y8C y9C y10C y11C y12C y13C y14C EVC LSC.
      rewrite (ret_pc_even 2814564) by (clear; lia).
      fold ba. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTa.
      step. change (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false. cbv iota.
      step. step. step.
    eapply (get_flags_callA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EVC | exact LSC | exact HAm | exact NROm |].
    intros mD y0D y1D y2D y4D y5D y6D y7D y8D y9D y10D y11D y12D y13D y14D EVD LSD.
      rewrite (ret_pc_even 2814580) by (clear; lia).
      fold bm. rewrite (unsigned_lit 4) by (clear; lia). rewrite CTm.
      step. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.

      pose proof EVD as (_ & _ & _ & _ & _ & _ & _ & _ & FRD & _). cbn [app] in FRD.
      step. step.
    eapply (num_bits_callA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 ); [exact EVD | exact LSD | exact HAp | exact NROp | unfold BN_NUM_BITS_STACK in *; clear - LOK CSnb; lia |].
    intros mE y0E y1E y2E y4E y5E y6E y7E y8E y9E y10E y11E y12E y13E y14E EVE LSE.
      rewrite (ret_pc_even 2814692) by (clear; lia).
      pose proof (num_bits_pure_range bp OKp1) as BITS.
      fold bp. cbn [Z.eqb negb]. cbv beta. cbn [tbind fst snd]. cbv beta. set (bits := num_bits_pure bp) in *.
      assert (BITSR : bits <= 32768) by (clear - BITS OKp2 OKp3; lia).
      step. if_cases KB; rewrite ?unsigned_lit in KB by (clear - BITS BITSR; lia); zify_cond KB.
      2: {
           replace (bits =? 0) with false by (symmetry; apply Z.eqb_neq; exact KB).
           pose proof (cenv_pre_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EVE) as WFE. cbn [cells_wf cell_wf app] in WFE.
           destruct WFE as (L0 & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & _ & _ & L16 & L17 & _ & LJ & _).
           destruct (cb8_word j0 L0) as (w0 & E0). destruct (cb8_word j1 L1) as (w1 & E1). destruct (cb8_word j2 L2) as (w2 & E2). destruct (cb8_word j3 L3) as (w3 & E3).
           destruct (cb8_word j4 L4) as (w4 & E4). destruct (cb8_word j5 L5) as (w5 & E5). destruct (cb8_word j6 L6) as (w6 & E6). destruct (cb8_word j7 L7) as (w7 & E7).
           destruct (cb8_word j8 L8) as (w8 & E8). destruct (cb8_word j9 L9) as (w9 & E9). destruct (cb8_word j10 L10) as (w10 & E10). destruct (cb8_word j11 L11) as (w11 & E11).
           destruct (cb8_word j12 L12) as (w12 & E12). destruct (cb8_word j13 L13) as (w13 & E13). destruct (cb8_word j16 L16) as (w16 & E16). destruct (cb8_word j17 L17) as (w17 & E17).
           assert (EVR : cenvA LBX PL0 lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1
                           (locs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 (Z_to_bv 64 SHB) (Z_to_bv 64 arp) w16 w17 ++ [CB g junk]) 0 Σ1 ls mE OW).
           { eapply cenv_recastA; [exact EVE | | |].
             - unfold locs. cbn [cells_wf cell_wf app]. repeat split; exact LJ.
             - unfold locs. cbn [cells_bytes cbytes app]. rewrite E0, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E16, E17. reflexivity.
             - reflexivity. }
           assert (BC : bits * CMM <= 32768 * CMM) by (apply Z.mul_le_mono_nonneg_r; [exact CMM0 | exact BITSR]).
           apply evt_done.
           eapply (L_rest m1 0 Σ1 ls mE OW bits jv);
             [ exact EVR | exact LSE | apply ax_pres_refl | exact FRV | clear - BITS KB BITSR; lia
             | pose proof TOTAL_OK as H; unfold EXP_MONT_TOTAL in H; clear - H MCP CMM0 BC; lia ]. }

      replace (bits =? 0) with true by (symmetry; apply Z.eqb_eq; exact KB).
      unfold exp_bits0, bbind, bget. cbn [bind ret tree_ops tbind fst snd]. fold bm.
      step. step. step. step.
    eapply (abs_is_word_callA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EVE | exact LSE | exact HAm | exact NROm |].
    intros mF y0F y1F y2F y4F y5F y6F y7F y8F y9F y10F y11F y12F y13F y14F EVF LSF.
      rewrite (ret_pc_even 2814952) by (clear; lia).
      fold bm. rewrite (unsigned_lit 1) by (clear; lia).
      destruct (abs_is_word_pure bm 1); cbn [Z.b2z].
      -
        step. change (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false. cbv iota. step. step.
        eapply (zero_callA LBX PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 LOFB16); [exact EVF | exact LSF | exact HAr | exact (hpl_wref _ _ WRr) |].
        intros mG z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 lsG EVG LSG.
        rewrite (ret_pc_even 2814964) by (clear; lia).
        unfold BN_zero, bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
        step.
        apply evt_done. eapply (CONT _ _ _ _ [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10; CB 8 j11; CB 8 j12; CB 8 j13; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 arp); CB 8 j16; CB 8 j17; C8 (Z_to_bv 64 f)]); [exact EVG | exact LSG | exact T0 | apply ax_pres_refl | reflexivity].
      -
        step. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota. step. step. step.
        unfold BN_one.
    apply evt_done.
    eapply implA_post.
    { eapply (BN_set_word_walkA) with (lo := lo) (OW := OW) (LB := ((q, f + 32, 256) :: LB)) (PL := PL0) (EA := EA) (w := 1);
        [| | | reflexivity | exact HAr | exact (hpl_wref _ _ WRr) | reflexivity | reflexivity | clear; lia].
      - eapply cenv_preA; [exact EVF | exact LSF | clear - LOK CSsetw; lia | pose proof TOTAL_OK as H; unfold EXP_MONT_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H; clear - H MCP CMM0 CFM0 CMS0; unfold MC in *; lia].
      - rewrite ESP. exact (cenv_uwA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl EVF).
      - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_BN_mod_exp_mont_2af25c CTX).
    }
    cbv beta. intros [uH lsH] ΣH msH PO.
    apply (bn_postA_cpost ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa TOTAL Σ1 ls OW) in PO; [| exact OK | exact (proj1 (proj2 EVF))].
    cbn [fst snd] in *.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FH & fcH & mH & OWH & PLH & -> & CPH & (EPLH & -> & INCLH)).
    subst PLH. specialize (CPH eq_refl).
    destruct (cenv_postA ((q, f + 32, 256) :: LB) PL0 EA lo (bv_unsigned sp) spa s0 ra (Some ras) TOTAL Σ1 ls OW m1 _ _ _ _ _ _ _ _ _ _ _ EVF CPH) as (EVH & LSH).
    pose proof (cpost_refsA _ _ _ _ _ _ _ _ _ _ _ _ _ _ CPH) as RSH. clear CPH.
    rewrite (ret_pc_even 2815044) by (clear; lia).
        apply implA_from_evt. step. step.
        apply evt_done. destruct uH. eapply (CONT _ _ _ _ [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3; CB 8 j4; CB 8 j5; CB 8 j6; CB 8 j7; CB 8 j8; CB 8 j9; CB 8 j10; CB 8 j11; CB 8 j12; CB 8 j13; C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 arp); CB 8 j16; CB 8 j17; C8 (Z_to_bv 64 f)]); [exact EVH | exact LSH | pose proof TOTAL_OK as H; unfold EXP_MONT_TOTAL, BN_NNMOD_COST, BN_DIV_FT_COST in H; clear - H MCP CMM0 CFM0 CMS0; unfold MC in *; lia | apply ax_pres_refl | reflexivity].
    Qed.

  End Fixed.
End Proofs.
End Body.
