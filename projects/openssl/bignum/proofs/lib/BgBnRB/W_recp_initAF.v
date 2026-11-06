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
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA ImplAX UnwindA EdgesA AsStruct RtCallA AsStruct2 W_ctx_getA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnCallAF AFrameComp PlaceRecpA RecpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BN_RECP_CTX_INIT : Z := 0x2bc2b4.
Definition RECP_INIT_STACK : Z := 32 + 16 + RT_STACK.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma zero_cells : forall (m : mem) d n, bytes_at bgbsegs m d (repeat (Z_to_bv 8 0) n) -> wr_at bgbsegs m d (Z.of_nat n) -> rw_cells bgbsegs m d [CB n (repeat (Z_to_bv 8 0) n)].
Proof.
  intros m d n BZ WRZ. split; [split; [cbn [cells_wf cell_wf]; rewrite repeat_length; tauto | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BZ]|].
  cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact WRZ.
Qed.

Lemma recp_init_callA : forall {X : Type} (t : btree bptr X) (Q : X -> rts RT -> machine_state -> Prop)
    (objs LBo : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv FB : Z) (s0w raw : word) (rasO : option (list Z)) (TOTAL : Z)
    (Σ0 : rts RT) (ls0 : bstate bptr) (OW0 : list block) (m0 : mem) (pre : list cell) (used : Z) (Σ : rts RT) (ls : bstate bptr) (m : mem) (OW : list block)
    (q : bptr) (an : Z)
    (ra gp tp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  cenvA (objs ++ LBo) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> lib_state ls m OW PL EA ->
  In (q, an, 64) objs -> an mod 8 = 0 -> (forall x, an <= x < an + 64 -> ~ rin_ivs (pl_frames PL) x) ->
  pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None -> pl_recp PL = None ->
  lo <= FB - RECP_INIT_STACK -> tp = wz TP_A ->
  (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 F' fc',
      cenvA (objs ++ LBo) (pl_place_recp PL an) lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m' pre used Σ (st_recp_init ls) m' OW ->
      lib_state (st_recp_init ls) m' OW (pl_place_recp PL an) EA ->
      ax_pres LBo SPv (XW PL) m0 m' ->
      implA t Σ Q (MS (mkR ra (Z_to_bv 64 FB) gp (wz TP_A) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                      F' (ret_pc ra) fc' None m' (seg_rom bgbsegs))) ->
  implA t Σ Q (MS (mkR ra (Z_to_bv 64 FB) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 an) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                  F (wz BN_RECP_CTX_INIT) fc None m (seg_rom bgbsegs)).
Proof.
  intros until fc. intros EV LS Hb A8 NF E1 E2 E3 LO -> K.
  pose proof EV as (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRC & FSZ & UW).
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  unfold RECP_INIT_STACK, BN_RECP_CTX_INIT, RT_STACK, MallocRep.wz in *.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  assert (HbL : In (q, an, 64) (objs ++ LBo)) by (apply in_or_app; left; exact Hb).
  assert (HbA : In (q, an, 64) (OW ++ objs ++ LBo)) by (apply in_or_app; right; exact HbL).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HbA) as (B0 & _ & _ & BC & BI). cbn [blk_addr blk_size fst snd] in B0, BC, BI.
  assert (ESP : bv_unsigned (Z_to_bv 64 FB) = FB) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - C1 CEIL LOFB FBSP SPT; lia).
  assert (Ean : bv_unsigned (Z_to_bv 64 an) = an) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - B0 BC C3; lia).
  pose proof (munch_refl [(FB - 32, FB)]%Z m) as MU. pose proof (wmono_refl bgbsegs m) as WM.
  apply implA_from_evt. rewrite ?ESP.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB bgbsegs _ _ [] 32 _ [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 4 step. do 2 step. do 2 step. step.

  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP1 : bv_unsigned (Z_to_bv 64 (FB + -32)) = FB + -32) by (apply unsigned_lit; unfold BnHeapA.ACEIL in *; clear - C1 CEIL LO LOFB FBSP SPT; lia).
  assert (HEAP1 : AHEAP Σ OW (objs ++ LBo) m1).
  { eapply (AH_frame Σ OW (objs ++ LBo) m m1 _ HEAP MU WM). constructor; [left; cbn [fst snd]; unfold BnHeapA.ACEIL, USTACK_TOP in *; clear - CEIL LO FBSP SPT; lia | constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ objs ++ LBo) FB) m m1).
  { eapply (stack_munch_agree Σ OW (objs ++ LBo) m m1 _ FB HEAP MU). constructor; [cbn [fst snd]; unfold BnHeapA.ACEIL in *; clear - CEIL LO; lia | constructor]. }
  assert (STKC : forall x, FB + -32 <= x < FB -> aclient_addr (OW ++ objs ++ LBo) (FB + -32) x /\ ~ (an <= x < an + 64)).
  { intros xq Hx. split; [left; unfold USTACK_TOP; clear - Hx FBSP SPT; lia | unfold BnHeapA.ACEIL in *; clear - Hx BC CEIL LO; lia]. }
  assert (INB : forall x d n, an <= d -> d + n <= an + 64 -> d <= x < d + n -> aclient_addr (OW ++ objs ++ LBo) (FB + -32) x).
  { intros xq d1 n1 H1 H2 Hx. right; right. exists (q, an, 64). split; [exact HbA | cbn [blk_addr blk_size fst snd]; lia]. }

  apply evt_done.
  eapply implA_step_same.
  { eapply (asan_memset_cpsA) with (d := an) (n := 64) (c := Z_to_bv 8 0) (bd := (q, an, 64)) (lo := lo) (OW := OW) (LB := objs ++ LBo); try reflexivity;
      [exact HEAP1 | rewrite ESP1; exact ST | exact CEIL | rewrite ESP1; unfold RT_STACK; clear - LO; lia
      | rewrite ESP1; unfold USTACK_TOP; clear - SPT FBSP; lia | rewrite ESP1; clear - FB16; Z.div_mod_to_equations; lia | assumption | exact HbA
      | cbn [blk_addr blk_size fst snd]; clear; lia ..]. }
  intros msK PO. unfold icall_post in PO. rewrite ?ESP1 in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MI2 & ST2 & HEAP2 & WM2 & AG2 & BZ & WRZ).
  rewrite (ret_pc_even 2867928) by (clear; lia). unfold MallocRep.wz.
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros xq Hx; cbn [cells_size csize Nat.add] in Hx; apply STKC; clear - Hx; lia].
  change (Z.to_nat 64) with 64%nat in BZ.
  pose proof (zero_cells m2 an 64 BZ WRZ) as BALL.
  apply (rw_cells_split_CB bgbsegs _ _ [] 64 _ [] [24; 24; 12; 4]%nat) in BALL; [| reflexivity]. cbn [mk_CB_cells app firstn skipn repeat] in BALL.
  pose proof (rw_cells_app_r m2 an [CB 24 (repeat (Z_to_bv 8 0) 24)] _ BALL) as BHI. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BHI.
  clear BALL BZ WRZ.

  apply implA_from_evt.
  step. if_cases KZ; zify_cond KZ; [exfalso; rewrite ?Ean in KZ; clear - KZ B0; lia|]. clear KZ.
  step.
  step. if_cases KA; zify_cond KA; [exfalso; apply KA; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear; lia); change (2 ^ 3) with 8; exact A8|]. clear KA.
  do 2 step.
  apply evt_done.
  eapply implA_step_same.
  { eapply (bn_init_cpsA) with (A := an) (bd := (q, an, 64)) (lo := lo) (OW := OW) (LB := objs ++ LBo); try reflexivity;
      [exact HEAP2 | rewrite ESP1; exact ST2 | exact CEIL | rewrite ESP1; unfold BN_INIT_STACK, RT_STACK; clear - LO; lia
      | rewrite ESP1; unfold USTACK_TOP; clear - SPT FBSP; lia | rewrite ESP1; clear - FB16; Z.div_mod_to_equations; lia | exact MI2 | exact HbA
      | cbn [blk_addr blk_size fst snd]; clear; lia ..]. }
  intros msK PO. unfold icall_post in PO. rewrite ?ESP1 in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MI3 & ST3 & HEAP3 & WM3 & AG3 & BN0).
  rewrite (ret_pc_even 2867948) by (clear; lia). unfold MallocRep.wz.
  apply (rw_cells_agree _ _ _ _ _ AG3) in FR; [| intros xq Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply STKC; clear - Hx; lia | unfold BnHeapA.ACEIL in *; clear - Hx BC CEIL LO; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG3) in BHI; [| intros xq Hx; cbn [cells_size csize Nat.add] in Hx; split; [apply (INB xq (an + 24) 40); clear - Hx; lia | clear - Hx; lia]].

  apply implA_from_evt.
  step. do 3 step.
  release_frame FR ST3 FB.
  do 2 step.

  apply evt_done.
  eapply implA_step_same.
  { eapply (bn_init_cpsA) with (A := an + 24) (bd := (q, an, 64)) (lo := lo) (OW := OW) (LB := objs ++ LBo); try reflexivity;
      [exact HEAP3 | rewrite ESP; exact ST3 | exact CEIL | rewrite ESP; unfold BN_INIT_STACK, RT_STACK; clear - LO; lia
      | rewrite ESP; unfold USTACK_TOP; clear - SPT FBSP; lia | rewrite ESP; exact FB16 | exact MI3 | exact HbA
      | cbn [blk_addr blk_size fst snd]; clear; lia ..]. }
  intros msK PO. unfold icall_post in PO. rewrite ?ESP in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & BN1).
  unfold MallocRep.wz.
  apply (rw_cells_agree _ _ _ _ _ AG4) in BN0; [| intros xq Hx; lazymatch type of Hx with context [Z.of_nat (cells_size ?c)] => change (Z.of_nat (cells_size c)) with 24 in Hx end; split; [right; right; exists (q, an, 64); split; [exact HbA | cbn [blk_addr blk_size fst snd]; clear - Hx; lia] | clear - Hx; lia]].
  pose proof (rw_cells_app_r m3 (an + 24) [CB 24 (repeat (Z_to_bv 8 0) 24)] _ BHI) as BSC. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in BSC.
  replace (an + 24 + 24) with (an + 48) in BSC by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AG4) in BSC; [| intros xq Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; right; exists (q, an, 64); split; [exact HbA | cbn [blk_addr blk_size fst snd]; clear - Hx; lia] | clear - Hx; lia]].
  pose proof (rw_cells_app_l m4 (an + 48) [CB 12 (repeat (Z_to_bv 8 0) 12)] _ BSC) as BS3.
  assert (C3c : rw_cells bgbsegs m4 (an + 48) [C4 (wz 0); C4 (wz 0); C4 (wz 0)]).
  { apply (rw_cells_recast m4 (an + 48) _ _ BS3); [cbn; tauto | vm_compute; reflexivity | reflexivity]. }

  assert (AGT : agree_on (fun a => aclient_addr (OW ++ objs ++ LBo) FB a /\ ~ (an <= a < an + 64)) m m4).
  { assert (UP : forall a, aclient_addr (OW ++ objs ++ LBo) FB a -> aclient_addr (OW ++ objs ++ LBo) (FB + -32) a).
    { intros a [Ha|[Ha|Ha]]; [left; clear - Ha; lia | right; left; exact Ha | right; right; exact Ha]. }
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG1|]; intros a [Ha _]; exact Ha|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG2|]; intros a [Ha Hn]; split; [exact (UP a Ha) | exact Hn]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG3|]; intros a [Ha Hn]; split; [exact (UP a Ha) | clear - Hn; lia]|].
    eapply agree_on_mono; [exact AG4|]. intros a [Ha Hn]. split; [exact Ha | clear - Hn; lia]. }
  destruct (cenv_obj_agreeA objs LBo PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m m4 OW FB (q, an, 64) an 64 EV LS Hb
              ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) NF ltac:(clear; lia) AGT HEAP4 ST4 MI4) as (EV4 & LS4 & AXO4).
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as (_ & PWF & _).
  assert (PWF' : pl_wf (pl_place_recp PL an)).
  { apply (pl_wf_place_recp_nf PL an PWF B0). intros xq Hx. apply NF. clear - Hx. lia. }
  assert (LSP : lib_state (st_recp_init ls) m4 OW (pl_place_recp PL an) EA).
  { unfold lib_state in *. apply (lib_state_place_recp false [] ls m4 OW PL EA an LS4 PWF' E1 E2 E3); [exact BN0 | exact BN1 | exact C3c]. }
  pose proof (cenv_place_recpA (objs ++ LBo) PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m4 pre used Σ ls m4 OW an (q, an, 64) EV4 LS4 E1 E2 HbL
                ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) ltac:(cbn [blk_addr blk_size fst snd]; clear; lia) A8) as EVP.
  eapply K; [exact EVP | exact LSP | exact AXO4].
Qed.

End WithRT.
