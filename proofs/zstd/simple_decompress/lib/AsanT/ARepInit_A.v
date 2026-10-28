(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ALayout ARep AHeapP AQConst ARepQ ARepInit_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition X0 : aconc := mkAConc (fun _ => mkXClass [] []) [].
(* [comment removed for export] *)
Definition ST0 (V : nat -> Z) : astate := ainit (a_space_beg0 V) (a_ptr_array0 V).

Lemma get_cls_ST0 : forall V c, get_cls (ST0 V) c = aclass0.
Proof. intros. apply get_cls_ainit. Qed.
Lemma max_count_ST0 : forall V c, max_count (ST0 V) c = 0.
Proof. intros. reflexivity. Qed.
Lemma ndist_ST0 : forall V c, ndist (ST0 V) c = 0.
Proof. intros. unfold ndist. rewrite get_cls_ST0. cbn. apply Zdiv_0_l. Qed.
Lemma busy_of_X0 : forall c k, busy_of X0 c k = None.
Proof. intros. reflexivity. Qed.
Lemma busy_slots_X0 : forall c, busy_slots X0 c = [].
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_round_up_Z_bounds : forall x, x <= page_round_up_Z x < x + 4096 /\ page_round_up_Z x mod 4096 = 0.
Proof.
  intros x. unfold page_round_up_Z, page_size. split; [| apply Z_mod_mult]. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Local Ltac aobj_close :=
  unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI;
  split; [rewrite Z.mul_comm; apply Z_mod_mult|]; split; [lia|]; split; [lia|]; split; lia.

Theorem alayout_stack_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) both_pure_facts -> 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
  al_bot (mkALayout (LV V) w U) + 0x800000 = al_top (mkALayout (LV V) w U) /\ al_top (mkALayout (LV V) w U) mod 4096 = 0
  /\ ATOP + 0x800000 - 160 <= al_top (mkALayout (LV V) w U) <= ATOP + 0x800000 + 3936 /\ al_top (mkALayout (LV V) w U) <= 2^47.
Proof.
  intros V w U HP HAT. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  unfold al_bot, al_top. rewrite LV_sp0.
  pose proof (page_round_up_Z_bounds (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 0xa0)) as [T1 T2].
  set (T := page_round_up_Z _) in *. clearbody T.
  apply Z.mod_divide in T2 as [q ->]; [| lia]. change (2^47) with (34359738368 * 4096).
  split; [lia|]. split; [apply Z_mod_mult|]. split; lia.
Qed.

Theorem alayout_ok_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) both_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
  32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
  alayout_ok (mkALayout (LV V) w U).
Proof.
  intros V w U HP HU HAT.
  pf V HP (PVar 0 4294901760 4294967295) Q0. pf V HP (PVar 6 0 255) Q6. pf V HP (PVar 10 0 7) Q10.
  constructor; rewrite ?LV_t, ?LV_ctx, ?LV_nodes, ?LV_store, ?LV_fake, ?LV_ptr_array, ?LV_space_beg; unfold al_res, al_dtls; cbn [al_V LV Nat.eqb].
  - (* [comment removed for export] *)
    pf V HP (PVar 227 1 34359736319) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512) DB.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6377472) DI.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 228 1573 34359736304) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 453 1573 34359736064) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 454 1573 34359734272) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 377 1573 34359733495) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 208 4295491576 34326181871) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 226 1573 34359734272) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 2147446784) 17592186048512) DB.
    aobj_close.
  - (* [comment removed for export] *)
    pf V HP (PVar 310 1 34359736319) P.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512) DB.
    pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6377472) DI.
    aobj_close.
  - (* [comment removed for export] *) pf V HP (PVar 208 4295491576 34326181871) P. lia.
  - (* [comment removed for export] *) pf V HP (PVar 209 0 15) P. lia.
  - (* [comment removed for export] *)
    pf V HP (PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0) H4.
    pf V HP (PVar 209 0 15) P.
    change 65535 with (Z.ones 16) in H4. rewrite Z.land_ones in H4 by lia. change (2^16) with 65536 in H4.
    pose proof (Z.mod_pos_bound (4096 * V 208%nat) 65536 ltac:(lia)) as B.
    set (u := (4096 * V 208%nat) mod 65536) in *.
    assert (Hv : (-4096 * V 209%nat + u) mod MainExport.two64 = 0) by lia.
    apply Z.mod_divide in Hv; [| unfold MainExport.two64; lia]. destruct Hv as [q Hq]. unfold MainExport.two64 in Hq.
    replace (4096 * (V 208%nat - V 209%nat) + 65536) with ((4096 * V 208%nat / 65536 + 1) * 65536); [apply Z_mod_mult|].
    pose proof (Z.div_mod (4096 * V 208%nat) 65536 ltac:(lia)). lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 226)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 227)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 228)) 65536) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200) D. unfold adisj. lia.
  - (* [comment removed for export] *) pf V HP (PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 310)) 4096) D. unfold adisj. lia.
  - (* [comment removed for export] *)
    clear Q0 Q6 Q10. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
    unfold al_bot, al_top. rewrite LV_sp0.
    pose proof (page_round_up_Z_bounds (32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 0xa0)) as [T1 T2].
    set (T := page_round_up_Z _) in *. clearbody T.
    apply Z.mod_divide in T2 as [q ->]; [| lia]. change (2^47) with (34359738368 * 4096).
    split; [lia|]. split; [apply Z_mod_mult|]. split; lia.   (* [comment removed for export] *)
  - (* [comment removed for export] *) exact HU.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem awf_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)),
  Forall (pfact_ok V) both_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
  32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->
  awf (mkALayout (LV V) w U) (ST0 V) X0.
Proof.
  intros V w U HP HU HAT. pose proof (alayout_space _ (alayout_ok_init V w U HP HU HAT)) as (S1 & S2 & S3 & S4).
  unfold awf. repeat match goal with |- _ /\ _ => split end.
  - unfold ST0, ainit, a_space_beg0, al_space_beg. cbn [a_space_beg al_V LV Nat.eqb]. lia.
  - reflexivity.
  - exact S3. - exact S1. - exact S2.
  - intros c Hc. rewrite get_cls_ST0, max_count_ST0, busy_slots_X0, ndist_ST0. cbn.
    unfold K_FREEARR_OFF, K_FREEARR_MAX, K_USER_MAP, K_FREEARR_MAP.
    repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity;
      first [ apply Zmod_0_l | constructor | intros k [] ].
  - intros c _. apply get_cls_ST0.
  - intros b [].
  - intros p c n H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros p ch H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b1 b2 [].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem ablocks_init : forall L st, ablocks L st X0 [].      (* [comment removed for export] *)
Proof.
  intros L st. split; [intros p A n []|]. split; [intros cls A n []|]. split; constructor.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem qcoupled_init : forall L V, qcoupled L (ST0 V) X0 qconc0.
Proof.
  intros L V. unfold qcoupled. cbn.
  split; [reflexivity|]. split; [reflexivity|]. split; [constructor|]. split; [constructor|]. split; [constructor|].
  split; [intros k; split; [intros []| intros (b & [] & _)]|].
  split; [intros c k; split; [intros []| intros (b & [] & _)]|]. constructor.
Qed.

Theorem qnum_init : forall V, qnum (ST0 V).
Proof.
  intros V. unfold qnum. cbn. unfold Q_CACHE, Q_MAX. repeat split; try lia. constructor.
Qed.
End CANSEC1.
