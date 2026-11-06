(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5Core L5CoreSpecs L5CoreKitS L5Words L5Hp L5Reduce L5ReduceG L5DivSpecs L5DivXP L5DivEarly.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5DIVO1H.
Import L5CS. Import L5DS. Import L5DIVXP.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition HALF : Z := 0x21f9c.
Definition DT2 : Z := 0x222d0.

(* [comment removed for export] *)
Local Notation preserved_sregs := L5DIVEARLY.preserved_sregs.
Local Notation u64_at_agree1 := L5DIVEARLY.u64_at_agree1.
Local Notation u8_at_agree1 := L5DIVEARLY.u8_at_agree1.
Local Notation big_at_agree1 := L5DIVEARLY.big_at_agree1.
Local Notation defined_agree1 := L5DIVEARLY.defined_agree1.
Local Notation model_ok_but_vm := L5DIVEARLY.model_ok_but_vm.
Local Notation mem_eq := L5DIVEARLY.mem_eq.
Local Notation mod16_mod8 := L5DIVEARLY.mod16_mod8.
Local Notation div_saves_kept := L5DIVEARLY.div_saves_kept.
Local Notation outside1 := L5DIVEARLY.outside1.
Local Notation outside2 := L5DIVEARLY.outside2.

Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
(* [comment removed for export] *)
Local Ltac kreg K i H := etransitivity; [exact (K i ltac:(inl)) | exact H].
Local Ltac uSCR := unfold DIV_SCR, ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac prune_mod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; prune_mod; lia.
Local Ltac fsclia := prune_impl; prune_disj; prune_mod; uSCR; lia.
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].


Lemma DIV_SCR_val : DIV_SCR = 8848. Proof. reflexivity. Qed.
Lemma ASSIGN_SCR_val : ASSIGN_SCR = 8480. Proof. reflexivity. Qed.
Lemma RESIZE_SCR_val : RESIZE_SCR = 8432. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition VdH (sp X Q f38 qneg sgn d f69 x0 x1 rm : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp | 33%nat => X | 35%nat => Q | 38%nat => f38 | 61%nat => qneg | 62%nat => sgn | 63%nat => d | 69%nat => f69
  | 70%nat => x0 | 71%nat => x1 | 72%nat => rm
  | _ => 0
  end.

(* [comment removed for export] *)
Definition half_fb (fbx : Z) (nr : nat) (sgn : Z) : Z := Z.lor (Z.land (assign_fb fbx 0 nr false) 253) sgn.

(* [comment removed for export] *)
Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis RESIZE : resize_spec L HI.
Hypothesis ASSIGN : assign_spec L HI.

Let IMG := L5DIVEARLY.IMG L LY.
Let IMGLO := L5DIVEARLY.IMGLO L LY.
Let ERRNOV := L5DIVEARLY.ERRNOV L LY.
Let LBdef := @L5DIVEARLY.LBdef _ L HI HIok.
Let kept_above := L5DIVEARLY.kept_above L LY.
Let kept_inblock := @L5DIVEARLY.kept_inblock _ L HI LY HIok.
Let cdef_above := L5DIVEARLY.cdef_above L LY.
Let cdef_below := L5DIVEARLY.cdef_below L LY.
Let hi_heap_stackwrite := @L5DIVEARLY.hi_heap_stackwrite _ L HI LY HIok.

(* [comment removed for export] *)
Lemma half_path (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LBc : list (Z * Z)) (crc : credit)
      (sp X Q qneg sgn d fbx x0 x1 : Z) (Rs : bvmap 5 word) :
  (* [comment removed for export] *)
  getr R (reg 2) = Z_to_bv 64 (sp - 304) -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 qneg -> 0 <= qneg <= 1 -> getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 X ->
  getr R (reg 19) = Z_to_bv 64 d -> 1 <= d < 2 ^ 32 -> getr R (reg 23) = Z_to_bv 64 (X + 16) -> getr R (reg 24) = Z_to_bv 64 (Q + 16) ->
  getr R (reg 26) = Z_to_bv 64 sgn -> (sgn = 0 \/ sgn = 2) -> getr R (reg 27) = Z_to_bv 64 X ->
  (* [comment removed for export] *)
  hi_heap HI LBc crc M (m_vmmaps model) -> model_ok model -> K [] -> L5C.stk (hl_sptop L) M sp DIV_SCR ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M X (L5.BO fbx 2 (L5.BInl x0 x1)) -> X mod 8 = 0 -> sp <= X -> X + 32 <= hl_sptop L -> L5.defined M X 32 ->
  (* [comment removed for export] *)
  zero_obj M Q -> Q mod 8 = 0 -> sp <= Q -> Q + 32 <= hl_sptop L -> L5.defined M Q 32 -> (X + 32 <= Q \/ Q + 32 <= X) ->
  div_saves M sp Rs ->
  (* [comment removed for export] *)
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (nq : nat) (q0 q1 : Z) (nr : nat) (r0 r1 : Z),
      getr R' (reg 2) = Z_to_bv 64 (sp - 304) -> getr R' (reg 3) = Z_to_bv 64 GP -> getr R' (reg 4) = Z_to_bv 64 TP ->
      (forall i, In i [9; 19; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg i) = getr R (reg i)) ->
      L5.big_at RSEGS M' Q (L5.BO (2 * qneg) nq (L5.BInl q0 q1)) ->
      L5.big_at RSEGS M' X (L5.BO (half_fb fbx nr sgn) nr (L5.BInl r0 r1)) -> (nr <= 1)%nat ->
      L5.defined M' X 32 -> L5.defined M' Q 32 ->
      div_saves M' sp Rs -> (forall a, sp - 168 <= a < sp -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      L5C.hpres L LBc sp DIV_SCR [(X, 32); (Q, 32)] M M' ->
      model_but_vm model model' -> hi_heap HI LBc crc M' (m_vmmaps model') ->
      srealizes RSEGS SCFG (cfg R' DT2 M' model') K) ->
  srealizes RSEGS SCFG (cfg R HALF M model) K.
Proof.
  intros H2 H3 H4 H8 Hq H9 H18 H19 Hd H23 H24 H26 Hsg H27 HH MOK HK STK OBX AX8 SX HX DX ZQ AQ8 SQ HQ DQ APQ DS KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & SCR0). rewrite DIV_SCR_val in SLO, SCR0.
  pose proof (proj1 MOK) as Mh. pose proof (proj1 (proj2 MOK)) as Ml.
  pose proof ERRNOV as EV. pose proof IMG as IMG'.
  pose proof OBX as OB. unfold L5.big_at in OB. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OB. destruct OB as (Xf & Xfr & Xl & Xb0 & X16 & X24 & _ & Rx0 & Rx1).
  pose proof ZQ as OQ. unfold zero_obj, L5.big_at in OQ. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OQ. destruct OQ as (Qf & _ & Ql & _ & Q16 & Q24 & _).
  (* [comment removed for export] *)
  assert (Wsp: 0 <= sp < 2 ^ 64) by flia. assert (WX: 0 <= X < 2 ^ 64) by flia. assert (WQ: 0 <= Q < 2 ^ 64) by flia.
  assert (Wq: 0 <= qneg < 2 ^ 64) by flia. assert (Wsg: 0 <= sgn < 2 ^ 64) by (clear - Hsg; lia). assert (Wd: 0 <= d < 2 ^ 64) by flia.
  assert (W0: 0 <= 0 < 2 ^ 64) by (clear; lia). assert (Wx0: 0 <= x0 < 2 ^ 64) by (clear - Rx0; lia). assert (Wx1: 0 <= x1 < 2 ^ 64) by (clear - Rx1; lia).
  assert (SPR: 1048880 <= sp <= 140737488355328) by flia. assert (XR: 1048576 <= X <= 140737488355296) by flia. assert (QR: 1048576 <= Q <= 140737488355296) by flia.
  assert (APX: sp - 304 + 304 <= X \/ X + 32 <= sp - 304) by (left; flia). assert (APQ2: sp - 304 + 304 <= Q \/ Q + 32 <= sp - 304) by (left; flia).
  assert (Hq': 0 <= qneg <= 1) by flia. assert (Hsg': 0 <= sgn <= 2) by (clear - Hsg; lia). assert (Hd': 1 <= d <= 4294967295) by (clear - Hd; lia).
  assert (B255: 0 <= 0 <= 255) by (clear; lia). assert (Rx0': 0 <= x0 <= 18446744073709551615) by (clear - Rx0; lia). assert (Rx1': 0 <= x1 <= 18446744073709551615) by (clear - Rx1; lia).
  (* [comment removed for export] *)
  pose proof (dxh1_conc fx R M (VdH sp X Q 0 qneg sgn d 0 x0 x1 0)) as P1. cbn [VdH] in P1.
  destruct (P1 Wsp WX WQ Wq H2 H8 H9 H18 SPR A16 XR AX8 APX Xl Hq')
    as (fx1 & R1 & M1 & _ & FR1 & _ & (MS1 & K1 & A1 & A10 & A11 & A18 & A20)). clear P1.
  pose proof (mem_eq M M1 FR1) as EM1. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  eapply (RESIZE fx1 R1 M model K LBc crc Q (sp - 304) 0x21fb0 2%nat (L5.BO 0 0 (L5.BInl 0 0)) [] HH MOK HK A10 A11).
  - clear; cbn; lia.
  - cbn. intros F; discriminate F.
  - intros F. exfalso. clear - F. lia.
  - exact A1.
  - split. clear; lia. reflexivity.
  - kreg K1 2%nat H2.
  - kreg K1 4%nat H4.
  - split. { replace (sp - 304) with (sp + (-19) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. exact SPT. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact ZQ.
  - split. reflexivity. split. constructor. reflexivity.
  - exact AQ8. - flia. - exact HQ.
  - apply (L5C.writable_of_defined RSEGS). exact DQ. flia. flia.
  - cbn. intros cap q E. discriminate E.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 g LB2 cr2 POST MBV2 HH2.
    destruct POST as (RP2 & GPOST). destruct g as [|A cap].
    2:{ exfalso. destruct GPOST as (_ & F & _). clear - F. lia. }
    destruct GPOST as (_ & -> & -> & (st1 & OQ2 & OLq & SAME1) & HP2). cbn [L5.bo_fb L5.bo_st L5.bo_len L5.bo_data] in OQ2, OLq, SAME1, HP2.
    destruct st1 as [u0 u1|cq qq]. 2:{ contradiction. } clear SAME1.
    assert (U00: u0 = 0 /\ u1 = 0). { destruct OLq as (_ & _ & E). cbn in E. injection E. intros -> ->. split; reflexivity. }
    destruct U00 as [-> ->].
    replace (Q + 16 + 8 * Z.of_nat 0) with (Q + 16) in HP2 by (clear; lia).
    replace (8 * Z.max 0 (Z.of_nat 2 - Z.of_nat 0)) with 16 in HP2 by (clear; lia).
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2. pose proof MOK2 as (Mh2 & Ml2 & _).
    (* [comment removed for export] *)
    assert (KA2: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (Q <= a < Q + 32) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha NQ. apply (kept_above M M2 LBc (sp - 304) RESIZE_SCR _ a HP2). fsclia. uSCR; clear; lia. flia. exact Ha.
      apply outside2. exact NQ. clear - NQ; lia. }
    assert (SCR2: L5.defined M2 (sp - 8848) 8848).
    { replace 8848 with (112 + (8432 + 304)) at 2 by (clear; lia). apply L5C.defined_app. 3: clear; lia.
      { eapply (cdef_below M M2 LBc (sp - 304) RESIZE_SCR _ (sp - 8848) 112 HP2). flia. fsclia. uSCR; clear; lia. flia. flia.
        eapply L5.defined_sub. exact SCR0. flia. flia. }
      apply L5C.defined_app. 3: clear; lia.
      { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP2) as D. rewrite RESIZE_SCR_val in D. exactA D. }
      eapply (cdef_above M M2 LBc (sp - 304) RESIZE_SCR _ _ 304 HP2). fsclia. uSCR; clear; lia. flia. flia. flia.
      eapply L5.defined_sub. exact SCR0. flia. flia. }
    assert (DX2: L5.defined M2 X 32).
    { eapply (cdef_above M M2 LBc (sp - 304) RESIZE_SCR _ X 32 HP2). fsclia. uSCR; clear; lia. flia. flia. flia. exact DX. }
    assert (DQ2: L5.defined M2 Q 32).
    { eapply (cdef_above M M2 LBc (sp - 304) RESIZE_SCR _ Q 32 HP2). fsclia. uSCR; clear; lia. flia. flia. flia. exact DQ. }
    assert (E2: getr R2 (reg 2) = Z_to_bv 64 (sp - 304)). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by inl. exact H2. }
    assert (E4: getr R2 (reg 4) = Z_to_bv 64 TP). { rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4. }
    assert (E9: getr R2 (reg 9) = Z_to_bv 64 Q). { rewrite (preserved_sregs R1 R2 9 RP2) by inl. rewrite (K1 9%nat) by inl. exact H9. }
    assert (E18: getr R2 (reg 18) = Z_to_bv 64 2). { rewrite (preserved_sregs R1 R2 18 RP2) by inl. exact A18. }
    assert (E19: getr R2 (reg 19) = Z_to_bv 64 d). { rewrite (preserved_sregs R1 R2 19 RP2) by inl. rewrite (K1 19%nat) by inl. exact H19. }
    assert (E20: getr R2 (reg 20) = Z_to_bv 64 qneg). { rewrite (preserved_sregs R1 R2 20 RP2) by inl. exact A20. }
    assert (E23: getr R2 (reg 23) = Z_to_bv 64 (X + 16)). { rewrite (preserved_sregs R1 R2 23 RP2) by inl. rewrite (K1 23%nat) by inl. exact H23. }
    assert (E24: getr R2 (reg 24) = Z_to_bv 64 (Q + 16)). { rewrite (preserved_sregs R1 R2 24 RP2) by inl. rewrite (K1 24%nat) by inl. exact H24. }
    assert (E26: getr R2 (reg 26) = Z_to_bv 64 sgn). { rewrite (preserved_sregs R1 R2 26 RP2) by inl. rewrite (K1 26%nat) by inl. exact H26. }
    assert (E27: getr R2 (reg 27) = Z_to_bv 64 X). { rewrite (preserved_sregs R1 R2 27 RP2) by inl. rewrite (K1 27%nat) by inl. exact H27. }
    pose proof OQ2 as OQ2'. unfold L5.big_at in OQ2'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OQ2'. destruct OQ2' as (Qf2 & _ & Ql2 & _).
    (* [comment removed for export] *)
    pose proof (dxh2_conc fx2 R2 M2 (VdH sp X Q 0 qneg sgn d 0 x0 x1 0)) as P2. cbn [VdH] in P2.
    assert (WQ16: L5.writable RSEGS M2 (Q + 16) 16).
    { apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact DQ2|clear; lia|clear; lia] | flia | flia]. }
    assert (X16_2: L5.u64_at RSEGS M2 (X + 16) x0). { eapply u64_at_agree1; [intros i Hi; apply KA2; [flia | generalize APQ Hi; clear; lia] | flia | flia | exact X16]. }
    assert (X24_2: L5.u64_at RSEGS M2 (X + 24) x1). { eapply u64_at_agree1; [intros i Hi; apply KA2; [flia | generalize APQ Hi; clear; lia] | flia | flia | exact X24]. }
    destruct (P2 Wsp WX WQ Wd W0 Wx0 Wx1 E2 E9 E18 E19 E23 E24 SPR A16 QR AQ8 APQ2 Qf2 B255 eq_refl WQ16 XR AX8 APX APQ X16_2 X24_2 Rx0' Rx1' Hd')
      as (fx3 & R3 & M3 & MG3 & _ & FR3 & (MS3 & K3 & B1 & B10 & _ & _)). clear P2.
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS3.
    assert (HH3: hi_heap HI LBc crc M3 (m_vmmaps model2)).
    { eapply (hi_heap_stackwrite LBc crc M2 M3 _ (Q + 16) (Q + 16 + 16)). exact HH2. exact FR3. flia. flia. flia. exact MG3. }
    (* [comment removed for export] *)
    assert (DQ3: L5.defined M3 Q 32). { eapply L5.defined_grows. exact MG3. exact DQ2. }
    destruct (L5KS.limbs_of_defined M3 (Q + 16) 2 ltac:(eapply L5.defined_sub; [exact DQ3 | clear; lia | clear; cbn; lia]) ltac:(flia) ltac:(flia))
      as (wq & WQL & WQR & WQA).
    destruct wq as [|qw0 [|qw1 [|? ?]]]; try discriminate WQL.
    pose proof (Forall_inv WQR) as Rq0. pose proof (Forall_inv (Forall_inv_tail WQR)) as Rq1. cbn beta in Rq0, Rq1.
    assert (OQ3: L5.big_at RSEGS M3 Q (L5.BO 0 2 (L5.BInl qw0 qw1))).
    { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. { eapply u8_at_agree1. 4: exact Qf2. intros i Hi; apply FR3; flia. flia. flia. }
      split. clear; lia. split. { eapply u64_at_agree1. 4: exact Ql2. intros i Hi; apply FR3; flia. flia. flia. }
      split. reflexivity. split. { pose proof (WQA 0%nat ltac:(cbn; lia)) as V0. cbn [nth] in V0. exactA V0. }
      split. { pose proof (WQA 1%nat ltac:(cbn; lia)) as V1. cbn [nth] in V1. exactA V1. }
      split. clear; lia. split. exact Rq0. exact Rq1. }
    (* [comment removed for export] *)
    destruct (L5REDG.reduce_run fx3 R3 M3 Q 0x22034 (L5.BO 0 2 (L5.BInl qw0 qw1)) [qw0; qw1] B10 B1 ltac:(split; [clear; lia | reflexivity]) OQ3 AQ8 ltac:(flia) ltac:(flia)
                ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact DQ3 | clear; lia | clear; lia] | flia | flia])
                ltac:(cbn [L5.bo_data L5.bo_cap L5.bo_st]; eapply L5.defined_sub; [exact DQ3 | clear; lia | clear; lia])
                ltac:(cbn [L5.bo_data L5.bo_st]; exact WQA) WQL WQR
                ltac:(cbn [L5.bo_st]; intros cap q E; discriminate E))
      as (fx4 & R4 & M4 & MS4 & OQ4 & RP4 & C10 & FR4 & MG4).
    cbn [L5.bo_fb L5.bo_st] in OQ4.
    replace (if (L5W.rlen [qw0; qw1] =? 0)%nat then Z.land 0 253 else 0) with 0 in OQ4 by (destruct (L5W.rlen [qw0; qw1] =? 0)%nat; reflexivity).
    set (nq := L5W.rlen [qw0; qw1]) in OQ4.
    assert (FR4Z: forall i, 0 <= i < 2 ^ 64 -> ~ (Q <= i < Q + 16) -> M4 (Z_to_bv 64 i) = M3 (Z_to_bv 64 i)).
    { intros i Hi Hn. apply FR4. apply outside1. rewrite BG.unsigned_lit by exact Hi. exact Hn. }
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS4.
    assert (HH4: hi_heap HI LBc crc M4 (m_vmmaps model2)).
    { eapply (hi_heap_stackwrite LBc crc M3 M4 _ Q (Q + 16)). exact HH3. exact FR4Z. flia. flia. flia. exact MG4. }
    pose proof (mem_grows_trans _ _ _ MG3 MG4) as MG34.
    assert (KQ4: forall i, sp - 304 <= i < 2 ^ 64 -> ~ (Q <= i < Q + 32) -> M4 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi Hn. rewrite FR4Z. rewrite FR3. apply KA2. exact Hi. exact Hn. flia. clear - Hn; lia. flia. clear - Hn; lia. }
    (* [comment removed for export] *)
    set (rm := bv_unsigned (getr R3 (reg 8))).
    assert (Rrm: 0 <= rm < 2 ^ 64). { subst rm. apply BL.bvu_range. }
    assert (F2: getr R4 (reg 2) = Z_to_bv 64 (sp - 304)). { rewrite (preserved_sregs R3 R4 2 RP4) by inl. rewrite (K3 2%nat) by inl. exact E2. }
    assert (F8: getr R4 (reg 8) = Z_to_bv 64 rm). { rewrite (preserved_sregs R3 R4 8 RP4) by inl. subst rm. symmetry. apply Z_to_bv_bv_unsigned. }
    assert (F27: getr R4 (reg 27) = Z_to_bv 64 X). { rewrite (preserved_sregs R3 R4 27 RP4) by inl. rewrite (K3 27%nat) by inl. exact E27. }
    (* [comment removed for export] *)
    pose proof (dxh3_conc fx4 R4 M4 (VdH sp X Q 0 qneg sgn d 0 x0 x1 rm)) as P3. cbn [VdH] in P3.
    assert (WF4: L5.writable RSEGS M4 (sp - 304) 304).
    { apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_grows; [exact MG34|]; eapply L5.defined_sub; [exact SCR2|clear; lia|clear; lia] | flia | flia]. }
    destruct (P3 Wsp WX Rrm F2 F8 F27 SPR A16 WF4 ltac:(clear - Rrm; lia))
      as (fx5 & R5 & M5 & MG5 & _ & FR5 & (MS5 & K5 & C1 & C10' & C11 & T176 & T184 & T192 & T200)). clear P3.
    pose proof (model_ok_but_vm _ _ MOK MBV2) as MOK2'. 
    eapply (L5.cps_of_msteps RSEGS). exact Mh2. exact Ml2. exact MS5.
    assert (HH5: hi_heap HI LBc crc M5 (m_vmmaps model2)).
    { eapply (hi_heap_stackwrite LBc crc M4 M5 _ (sp - 200) (sp - 200 + 32)). exact HH4. exact FR5. flia. flia. flia. exact MG5. }
    pose proof (mem_grows_trans _ _ _ MG34 MG5) as MG35.
    (* [comment removed for export] *)
    set (nr := if 0 <? rm then 1%nat else 0%nat).
    assert (NR1: (nr <= 1)%nat). { subst nr. destruct (0 <? rm); clear; lia. }
    assert (T192': L5.u64_at RSEGS M5 (sp - 192) (Z.of_nat nr)). { subst nr. destruct (0 <? rm); exact T192. }
    assert (OT5: L5.big_at RSEGS M5 (sp - 200) (L5.BO 0 nr (L5.BInl rm 0))).
    { unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact T200. split. clear; lia. split. exactA T192'.
      split. reflexivity. split. exactA T184. split. exactA T176. split. clear - NR1; lia. split. exact Rrm. clear; lia. }
    assert (OLT5: L5C.obj_limbs RSEGS M5 (L5.BO 0 nr (L5.BInl rm 0)) (firstn nr [rm; 0])).
    { split. { cbn [L5.bo_len]. rewrite length_firstn. cbn [length]. clear - NR1; lia. }
      split. { subst nr. destruct (0 <? rm); cbn; repeat constructor; clear - Rrm; lia. } reflexivity. }
    (* [comment removed for export] *)
    eapply (ASSIGN fx5 R5 M5 model2 K LBc crc X (sp - 200) (sp - 304) 0x22054 (L5.BO fbx 2 (L5.BInl x0 x1)) (L5.BO 0 nr (L5.BInl rm 0)) (firstn nr [rm; 0])
              HH5 MOK2 HK C10' C11).
    + cbn [L5.bo_len]. clear - NR1; lia.
    + unfold L5.bo_dyn. cbn [L5.bo_fb]. rewrite Xb0. intros F; discriminate F.
    + cbn [L5.bo_len]. intros F. exfalso. clear - F NR1. lia.
    + exact C1.
    + split. clear; lia. reflexivity.
    + kreg K5 2%nat F2.
    + etransitivity. exact (K5 4%nat ltac:(inl)). rewrite (preserved_sregs R3 R4 4 RP4) by inl. rewrite (K3 4%nat) by inl. exact E4.
    + split. { replace (sp - 304) with (sp + (-19) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
      split. fsclia. split. flia. split. exact SPT. uSCR. eapply L5.defined_grows. exact MG35. eapply L5.defined_sub. exact SCR2. flia. flia.
    + eapply big_at_agree1. 4: exact OBX. 2: flia. 2: flia. intros i Hi. rewrite FR5. apply KQ4. flia. generalize APQ Hi; clear; lia. flia. flia.
    + exact AX8. + flia. + exact HX.
    + apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG35. exact DX2. flia. flia.
    + cbn. intros cap q E. discriminate E.
    + exact OT5.
    + exact OLT5.
    + rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity.
    + flia. + flia.
    + cbn. intros cap q E. discriminate E.
    + right. flia.
    + cbn. intros c q c' q' E. discriminate E.
    + (* [comment removed for export] *)
      intros fx6 R6 M6 model6 g2 LB6 cr6 POST2 MBV6 HH6.
      destruct POST2 as (RP6 & _ & GP2). destruct g2 as [|A cap].
      2:{ exfalso. destruct GP2 as (_ & F3 & _). cbn [L5.bo_len] in F3. clear - F3 NR1. lia. }
      destruct GP2 as (_ & -> & -> & (st2 & OX6 & OL6 & SAME2) & HP6). cbn [L5.bo_fb L5.bo_st L5.bo_len L5.bo_data] in OX6, OL6, SAME2, HP6.
      destruct st2 as [r0 r1|c' q']. 2:{ contradiction. } clear SAME2.
      replace (8 * Z.max (Z.of_nat nr) (Z.of_nat 2)) with 16 in HP6 by (clear - NR1; lia).
      set (f38 := assign_fb fbx 0 nr false) in *.
      pose proof (model_ok_but_vm _ _ MOK2 MBV6) as MOK6. pose proof MOK6 as (Mh6 & Ml6 & _).
      pose proof OX6 as OX6'. unfold L5.big_at in OX6'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OX6'. destruct OX6' as (Xf6 & F38 & Xl6 & Xb6 & X16' & X24' & _ & Rr0 & Rr1).
      (* [comment removed for export] *)
      assert (KA6: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
      { intros a Ha NX. apply (kept_above M5 M6 LBc (sp - 304) ASSIGN_SCR _ a HP6). fsclia. uSCR; clear; lia. flia. exact Ha.
        apply outside2. exact NX. clear - NX; lia. }
      assert (DX6: L5.defined M6 X 32).
      { eapply (cdef_above M5 M6 LBc (sp - 304) ASSIGN_SCR _ X 32 HP6). fsclia. uSCR; clear; lia. flia. flia. flia. eapply L5.defined_grows. exact MG35. exact DX2. }
      assert (DQ6: L5.defined M6 Q 32).
      { eapply (cdef_above M5 M6 LBc (sp - 304) ASSIGN_SCR _ Q 32 HP6). fsclia. uSCR; clear; lia. flia. flia. flia. eapply L5.defined_grows. exact MG35. exact DQ2. }
      assert (SCR6: L5.defined M6 (sp - 304) 304).
      { eapply (cdef_above M5 M6 LBc (sp - 304) ASSIGN_SCR _ (sp - 304) 304 HP6). fsclia. uSCR; clear; lia. flia. flia. flia.
        eapply L5.defined_grows. exact MG35. eapply L5.defined_sub. exact SCR2. flia. flia. }
      assert (G2': getr R6 (reg 2) = Z_to_bv 64 (sp - 304)). { rewrite (preserved_sregs R5 R6 2 RP6) by inl. rewrite (K5 2%nat) by inl. exact F2. }
      assert (G9': getr R6 (reg 9) = Z_to_bv 64 Q).
      { rewrite (preserved_sregs R5 R6 9 RP6) by inl. rewrite (K5 9%nat) by inl. rewrite (preserved_sregs R3 R4 9 RP4) by inl. rewrite (K3 9%nat) by inl. exact E9. }
      assert (G20': getr R6 (reg 20) = Z_to_bv 64 qneg).
      { rewrite (preserved_sregs R5 R6 20 RP6) by inl. rewrite (K5 20%nat) by inl. rewrite (preserved_sregs R3 R4 20 RP4) by inl. rewrite (K3 20%nat) by inl. exact E20. }
      assert (G26': getr R6 (reg 26) = Z_to_bv 64 sgn).
      { rewrite (preserved_sregs R5 R6 26 RP6) by inl. rewrite (K5 26%nat) by inl. rewrite (preserved_sregs R3 R4 26 RP4) by inl. rewrite (K3 26%nat) by inl. exact E26. }
      assert (G27': getr R6 (reg 27) = Z_to_bv 64 X). { rewrite (preserved_sregs R5 R6 27 RP6) by inl. rewrite (K5 27%nat) by inl. exact F27. }
      pose proof OQ4 as OQ4'. unfold L5.big_at in OQ4'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OQ4'. destruct OQ4' as (Qf4 & _ & Ql4 & _ & Q16'' & Q24'' & NQ2 & _).
      assert (KQ6: forall i, Q <= i < Q + 32 -> M6 (Z_to_bv 64 i) = M4 (Z_to_bv 64 i)).
      { intros i Hi. rewrite KA6. apply FR5. flia. flia. flia. generalize APQ Hi; clear; lia. }
      (* [comment removed for export] *)
      pose proof (dxh4_conc fx6 R6 M6 (VdH sp X Q f38 qneg sgn d 0 x0 x1 rm)) as P4. cbn [VdH] in P4.
      assert (W38: 0 <= f38 < 2 ^ 64) by (clear - F38; lia). assert (F38': 0 <= f38 <= 255) by (clear - F38; lia).
      assert (WF6: L5.writable RSEGS M6 (sp - 304) 304). { apply (L5C.writable_of_defined RSEGS); [exact SCR6 | flia | flia]. }
      assert (T200_6: L5.u8_at RSEGS M6 (sp - 200) 0). { eapply u8_at_agree1; [intros i Hi; apply KA6; flia | flia | flia | exact T200]. }
      assert (Qf6: L5.u8_at RSEGS M6 Q 0). { eapply u8_at_agree1; [intros i Hi; apply KQ6; flia | flia | flia | exact Qf4]. }
      assert (WQ6: L5.writable RSEGS M6 Q 32). { apply (L5C.writable_of_defined RSEGS); [exact DQ6 | flia | flia]. }
      assert (WX6: L5.writable RSEGS M6 X 32). { apply (L5C.writable_of_defined RSEGS); [exact DX6 | flia | flia]. }
      destruct (P4 Wsp WX WQ W38 Wq Wsg W0 G2' G9' G20' G26' G27' SPR A16 WF6 T200_6 QR AQ8 APQ2 Qf6 B255 WQ6 XR AX8 APX Xf6 F38' WX6 APQ Hq' Hsg')
        as (fx7 & R7 & M7 & MG7 & _ & FR7 & (MS7 & K7 & _ & _ & CX7 & CQ7)). clear P4.
      rewrite Z.land_0_l, Z.lor_0_l, Z.mod_small in CQ7 by (clear - Hq; lia).
      eapply (L5.cps_of_msteps RSEGS). exact Mh6. exact Ml6. exact MS7.
      (* [comment removed for export] *)
      assert (KEEP: forall a, sp - 168 <= a < sp -> M7 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha. rewrite FR7. rewrite KA6. rewrite FR5. apply KQ4. flia. flia. flia. flia. flia. flia. flia. flia. flia. }
      (* [comment removed for export] *)
      assert (CEIL: hl_ceil L <= sp - DIV_SCR). { unfold hl_ceil. rewrite DIV_SCR_val. clear - SLO. lia. }
      assert (LBceil: forall b, In b LBc -> fst b + snd b <= hl_ceil L).
      { intros [A n] Hb. pose proof (LBdef _ _ _ _ HH A n Hb) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
      assert (NSCR: forall W a, L5C.kept L LBc sp DIV_SCR W a -> ~ (sp - DIV_SCR <= a < sp)).
      { intros W a KA. eapply L5HP.kept_not_in_scratch. exact KA. exact LBceil. exact CEIL. unfold hl_ceil. rewrite IMG'. clear - SPT; lia. }
      set (W := [(X, 32); (Q, 32)]).
      assert (HP0: L5C.hpres L LBc sp DIV_SCR W M M).
      { apply L5C.hpres_intro. intros a _; reflexivity. rewrite DIV_SCR_val. exact SCR0. intros a _ _ _ D; exact D. }
      assert (HPB: L5C.hpres L LBc sp DIV_SCR W M M2).
      { eapply (L5HP.hpres_trans L LBc LBc sp DIV_SCR W M M M2 (sp - 304) RESIZE_SCR). exact HP0. exact HP2.
        - intros a KA. eapply L5HP.kept_mono. exact KA. intros b Hb; exact Hb. fsclia. flia.
          intros OW. pose proof (L5HP.outside_in _ _ Q 32 OW ltac:(subst W; cbn; right; left; reflexivity)) as NQ. apply outside2. exact NQ. clear - NQ; lia.
        - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite DIV_SCR_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      assert (HPC: L5C.hpres L LBc sp DIV_SCR W M M4).
      { eapply (L5HP.hpres_trans L LBc LBc sp DIV_SCR W M M2 M4 sp DIV_SCR W). exact HPB.
        - eapply (L5HP.hpres_piece L LBc sp DIV_SCR W M2 M4 (fun a => Q <= a < Q + 32)).
          { intros a Ha Hn. rewrite FR4Z. apply FR3. exact Ha. clear - Hn; lia. exact Ha. clear - Hn; lia. }
          intros a KA C. apply (L5HP.outside_in _ _ Q 32 (L5HP.kept_outside_W _ _ _ _ _ _ KA)). subst W; cbn. right; left; reflexivity. exact C.
          rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG34. exact SCR2. exact MG34.
        - intros a KA; exact KA. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite DIV_SCR_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      assert (HPD: L5C.hpres L LBc sp DIV_SCR W M M5).
      { eapply (L5HP.hpres_trans L LBc LBc sp DIV_SCR W M M4 M5 sp DIV_SCR W). exact HPC.
        - eapply (L5HP.hpres_piece L LBc sp DIV_SCR W M4 M5 (fun a => sp - 200 <= a < sp - 200 + 32)). exact FR5.
          intros a KA C. apply (NSCR W a KA). rewrite DIV_SCR_val. clear - C; lia.
          rewrite DIV_SCR_val. eapply L5.defined_grows. exact MG35. exact SCR2. exact MG5.
        - intros a KA; exact KA. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite DIV_SCR_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      assert (HPE: L5C.hpres L LBc sp DIV_SCR W M M6).
      { eapply (L5HP.hpres_trans L LBc LBc sp DIV_SCR W M M5 M6 (sp - 304) ASSIGN_SCR). exact HPD. exact HP6.
        - intros a KA. eapply L5HP.kept_mono. exact KA. intros b Hb; exact Hb. fsclia. flia.
          intros OW. pose proof (L5HP.outside_in _ _ X 32 OW ltac:(subst W; cbn; left; reflexivity)) as NX. apply outside2. exact NX. clear - NX; lia.
        - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite DIV_SCR_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HPE) as SCRE.
      assert (HPF: L5C.hpres L LBc sp DIV_SCR W M M7).
      { eapply (L5HP.hpres_trans L LBc LBc sp DIV_SCR W M M6 M7 sp DIV_SCR W). exact HPE.
        - eapply (L5HP.hpres_piece L LBc sp DIV_SCR W M6 M7 (fun a => (Q <= a < Q + 1) \/ (X <= a < X + 1))).
          { intros a Ha Hn. apply FR7. exact Ha. clear - Hn; lia. clear - Hn; lia. }
          intros a KA [C|C]. apply (L5HP.outside_in _ _ Q 32 (L5HP.kept_outside_W _ _ _ _ _ _ KA)). subst W; cbn. right; left; reflexivity. clear - C; lia.
          apply (L5HP.outside_in _ _ X 32 (L5HP.kept_outside_W _ _ _ _ _ _ KA)). subst W; cbn. left; reflexivity. clear - C; lia.
          eapply L5.defined_grows. exact MG7. exact SCRE. exact MG7.
        - intros a KA; exact KA. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite DIV_SCR_val; clear; lia. - rewrite EV; clear; lia. - flia. }
      (* [comment removed for export] *)
      apply (KONT fx7 R7 M7 model6 nq qw0 qw1 nr r0 r1).
      * rewrite (K7 2%nat) by inl. exact G2'.
      * rewrite (K7 3%nat) by inl. rewrite (preserved_sregs R5 R6 3 RP6) by inl. rewrite (K5 3%nat) by inl. rewrite (preserved_sregs R3 R4 3 RP4) by inl.
        rewrite (K3 3%nat) by inl. rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. exact H3.
      * rewrite (K7 4%nat) by inl. rewrite (preserved_sregs R5 R6 4 RP6) by inl. rewrite (K5 4%nat) by inl. rewrite (preserved_sregs R3 R4 4 RP4) by inl.
        rewrite (K3 4%nat) by inl. exact E4.
      * intros i Hi. cbn in Hi.
        repeat (destruct Hi as [<-|Hi];
          [ rewrite K7 by inl; rewrite (preserved_sregs R5 R6 _ RP6) by inl; rewrite K5 by inl; rewrite (preserved_sregs R3 R4 _ RP4) by inl;
            rewrite K3 by inl; rewrite (preserved_sregs R1 R2 _ RP2) by inl; rewrite K1 by inl; reflexivity |]). destruct Hi.
      * (* [comment removed for export] *)
        assert (KQ7: forall a, Q + 1 <= a < Q + 32 -> M7 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
        { intros a Ha. rewrite FR7. apply KQ6. flia. flia. clear - Ha; lia. generalize APQ Ha; clear; lia. }
        unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact CQ7. split. clear - Hq; lia.
        split. { eapply u64_at_agree1. 4: exact Ql4. intros i Hi; apply KQ7; flia. flia. flia. }
        split. apply Z.testbit_even_0.
        split. { eapply u64_at_agree1. 4: exact Q16''. intros i Hi; apply KQ7; flia. flia. flia. }
        split. { eapply u64_at_agree1. 4: exact Q24''. intros i Hi; apply KQ7; flia. flia. flia. }
        split. exact NQ2. split. exact Rq0. exact Rq1.
      * (* [comment removed for export] *)
        assert (SB0: Z.testbit sgn 0 = false). { destruct Hsg as [-> | ->]; reflexivity. }
        assert (EFB: Z.lor (Z.land f38 253) sgn = half_fb fbx nr sgn) by reflexivity. rewrite EFB in CX7.
        assert (KX: forall a, X + 1 <= a < X + 32 -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)). { intros a Ha. apply FR7. flia. generalize APQ Ha; clear; lia. clear - Ha; lia. }
        unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact CX7.
        split. { rewrite <- EFB. apply lor_byte. apply land_byte. clear - F38; lia. clear; lia. clear - Hsg; lia. }
        split. { eapply u64_at_agree1. 4: exact Xl6. intros i Hi; apply KX; flia. flia. flia. }
        split. { rewrite <- EFB, Z.lor_spec, Z.land_spec, Xb6, SB0. reflexivity. }
        split. { eapply u64_at_agree1. 4: exact X16'. intros i Hi; apply KX; flia. flia. flia. }
        split. { eapply u64_at_agree1. 4: exact X24'. intros i Hi; apply KX; flia. flia. flia. }
        split. clear - NR1; lia. split. exact Rr0. exact Rr1.
      * exact NR1.
      * eapply L5.defined_grows. exact MG7. exact DX6.
      * eapply L5.defined_grows. exact MG7. exact DQ6.
      * eapply div_saves_kept. 4: exact DS. intros i Hi. apply KEEP. flia. flia. flia.
      * exact KEEP.
      * exact HPF.
      * exact (L5C.model_but_vm_trans _ _ _ MBV2 MBV6).
      * eapply (hi_heap_stackwrite LBc crc M6 M7 _ sp (hl_sptop L)). exact HH6.
        { intros i Hi Hn. apply FR7. exact Hi. clear - Hn SQ HQ; lia. clear - Hn SX HX; lia. } flia. flia. flia. exact MG7.
Qed.


End WithHeap.
End SCFG_1.
End L5DIVO1H.
