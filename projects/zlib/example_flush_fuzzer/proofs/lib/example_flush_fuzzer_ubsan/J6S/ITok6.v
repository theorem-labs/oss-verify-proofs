(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Frame Hoare StepTac ZlibStmtBase ExSmallIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvApi InflateInvLoop InflateInvCall InflateRc InflateCall HarnessKit HarnessFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.FMQ6 Require Import CallocLib6 CallocTail6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 Callee6 CalleeKits6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 UpdWin6 Callee6i Infl6 Infl6B Infl6C IInit6.
Import InflLv Infl6A.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition LMEMC (v : icv) (w : iw) (M : word -> option byte) : Prop :=
  is6_scalars M (cv_S v) (ISP (cv_ZP v) (cv_WB v)) (w_s w)
  /\ cells s6_segs M (cv_S v + 168) 2 2 320 (arr_get (is_lens (w_s w)))
  /\ cells s6_segs M (cv_S v + 808) 2 2 288 (arr_get (is_work (w_s w)))
  /\ cells s6_segs M (cv_S v + 1384) 4 4 1444 (arr_get (is_codes (w_s w)))
  /\ (cv_WN v <> 0 -> cells s6_segs M (cv_WB v) 1 1 (cv_WN v) (arr_get (is_window (w_s w))))
  /\ cells s6_segs M (cv_I0 v) 1 1 (cv_NI v) (arr_get (ic_input (w_c w)))
  /\ cells s6_segs M (cv_P0 v) 1 1 (ir_put (w_r w)) (arr_get (ic_outbuf (w_c w)))
  /\ izs6 v M (w_c w)
  /\ iframe6 v M
  /\ cell s6_segs M (cv_sp v - INF_FRAME + 80) 8 (ir_out (w_r w)).

Lemma LMEMC_of : forall v w M, LMEM v w M -> LMEMC v w M.
Proof.
  intros v w M HM. destruct HM. unfold LMEMC. repeat (split; [assumption|]). assumption.
Qed.
Lemma LMEM_ofC : forall v w M, LMEMC v w M -> rod6_clear M ->
  mapped M (cv_sp v - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH) -> mapped M (cv_ZP v) 112 -> mapped M (cv_S v) 7176 ->
  mapped M (cv_P0 v) (cv_NO v) -> (cv_WN v <> 0 -> mapped M (cv_WB v) (cv_WN v)) -> LMEM v w M.
Proof.
  intros v w M (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) Hrod M1 M2 M3 M4 M5. constructor; assumption.
Qed.

Lemma cell_local : forall (M M' : word -> option byte) a (w : nat) v,
  cell s6_segs M a w v -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  (forall z, a <= z < a + Z.of_nat w -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)) -> cell s6_segs M' a w v.
Proof. intros. eapply cell_ext; eassumption. Qed.
Lemma cells_local : forall (M M' : word -> option byte) P st (w : nat) n f,
  cells s6_segs M P st w n f -> Z.of_nat w <= st -> 0 <= P -> P + st * n <= 2 ^ 64 ->
  (forall z, P <= z < P + st * n -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)) -> cells s6_segs M' P st w n f.
Proof.
  intros M M' P st w n f Hc Hw HP HPn HE i Hi.
  assert (st * i + st <= st * n) by nia. assert (0 <= st * i) by nia.
  apply (cell_local M M' _ w _ (Hc i Hi)); [nia | nia |]. intros z Hz. apply HE. nia.
Qed.

Lemma fields_local : forall (M M' : word -> option byte) Sb L vs size,
  fields s6_segs M Sb L vs -> layout_within L size = true -> 0 <= Sb -> Sb + size <= 2 ^ 64 ->
  (forall z, Sb <= z < Sb + size -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)) -> fields s6_segs M' Sb L vs.
Proof.
  intros M M' Sb L. induction L as [|[o w] L IH]; intros vs size Hf HW HS0 HS1 HE; destruct vs as [|v vs]; cbn in Hf |- *; try exact Hf.
  cbn [layout_within] in HW. apply andb_prop in HW as [HW HW']. apply andb_prop in HW as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  destruct Hf as [Hc Hf]. split; [| exact (IH vs size Hf HW' HS0 HS1 HE)].
  apply (cell_local M M' _ w _ Hc); [lia | lia |]. intros z Hz. apply HE. lia.
Qed.
Lemma is6_scalars_local : forall (M M' : word -> option byte) Sb q s,
  is6_scalars M Sb q s -> 0 <= Sb -> Sb + 7176 <= 2 ^ 64 ->
  (forall z, Sb <= z < Sb + 7176 -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)) -> is6_scalars M' Sb q s.
Proof. intros M M' Sb q s H HS0 HS1 HE. unfold is6_scalars in *. exact (fields_local M M' Sb _ _ 7176 H is6_layout_within HS0 HS1 HE). Qed.

Lemma izs6_local : forall v c (M M' : word -> option byte),
  izs6 v M c -> 0 <= cv_ZP v -> cv_ZP v + 112 <= 2 ^ 64 ->
  (forall z, cv_ZP v <= z < cv_ZP v + 112 -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)) -> izs6 v M' c.
Proof.
  intros v c M M' H HZ0 HZ1 HE. unfold izs6 in *.
  repeat match goal with |- _ /\ _ => split end;
  repeat match type of H with _ /\ _ => let X := fresh "C" in destruct H as [X H] end;
  lazymatch goal with |- cell _ _ ?a ?w _ =>
    match goal with C : cell _ M a w _ |- _ => apply (cell_local M M' _ _ _ C); [lia | cbn; lia | intros z Hz; apply HE; cbn in Hz; lia] end
  end.
Qed.

Lemma iframe6_local : forall v (M M' : word -> option byte),
  iframe6 v M -> 224 <= cv_sp v -> cv_sp v <= 2 ^ 64 ->
  (forall z, cv_sp v - 224 <= z < cv_sp v -> M' (Z_to_bv 64 z) = M (Z_to_bv 64 z)) -> iframe6 v M'.
Proof.
  intros v M M' H Hs0 Hs1 HE. unfold iframe6, INF_FRAME in *. destruct H as [Hsv H].
  split.
  { intros r o Hin. pose proof (Hsv r o Hin) as C.
    assert (Ho : 0 <= o /\ o + 8 <= 224).
    { unfold saved_slots in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; cbn; lia|]). destruct Hin. }
    apply (cell_local M M' _ _ _ C); [lia | cbn; lia | intros z Hz; apply HE; cbn in Hz; lia]. }
  repeat match goal with |- _ /\ _ => split end;
  repeat match type of H with _ /\ _ => let X := fresh "C" in destruct H as [X H] end;
  lazymatch goal with |- cell _ _ ?a ?w _ =>
    first [ match goal with C : cell _ M a w _ |- _ => apply (cell_local M M' _ _ _ C); [lia | cbn; lia | intros z Hz; apply HE; cbn in Hz; lia] end
          | apply (cell_local M M' _ _ _ H); [lia | cbn; lia | intros z Hz; apply HE; cbn in Hz; lia] ]
  end.
Qed.


(* 1.4: updatewindow's own registers (s0 = end, s1 = copy, s2 = 1, s3 = state) are unchanged; inflate's
   registers it has not touched move with inflate's 1.4 permutation: out - left in x20, NI in x21, out in x25. Its
   save slots hold inflate's s0..s4 by position: x8 S, x9 ret, x18 have, x19 left, x20 out - left. *)
Definition WSTR (v : icv) (rx : iregs) (RW : bvmap 5 word) : Prop :=
  getr RW 13 = zw (cv_fa v) /\ getr RW 10 = zw (cv_opq v) /\ getr RW 11 = zw 32768 /\ getr RW 12 = zw 1
  /\ getr RW 2 = zw (cv_sp v - INF_FRAME - 48) /\ getr RW 8 = zw (cv_P0 v + ir_put rx) /\ getr RW 9 = zw (ir_out rx - ir_left rx)
  /\ getr RW 18 = zw 1 /\ getr RW 19 = zw (cv_S v) /\ getr RW 21 = zw (cv_NI v) /\ getr RW 25 = zw (ir_out rx)
  /\ getr RW 20 = zw (ir_out rx - ir_left rx).

Definition UWC (h : Z) (rx : iregs) (S : Z) (M : word -> option byte) : Prop :=
  cell s6_segs M (h - INF_FRAME - 8) 8 pc6_uw_ret /\ cell s6_segs M (h - INF_FRAME - 16) 8 S
  /\ cell s6_segs M (h - INF_FRAME - 24) 8 (ir_ret rx mod 2 ^ 64) /\ cell s6_segs M (h - INF_FRAME - 32) 8 (ir_have rx)
  /\ cell s6_segs M (h - INF_FRAME - 40) 8 (ir_left rx) /\ cell s6_segs M (h - INF_FRAME - 48) 8 (ir_out rx - ir_left rx).


Lemma rod6_store : forall M a bs, rod6_clear M -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (a + Z.of_nat (length bs) <= ROD6_LO \/ ROD6_HI <= a) -> rod6_clear (wbytes M (zw a) bs).
Proof.
  intros M a bs H Ha Hab Hout x Hx. rewrite wbytes_inside; [exact (H x Hx) | exact Ha | exact Hab | lia].
Qed.
Lemma ROM6_of_rod6 : forall M, rod6_clear M -> ROM6 M.
Proof.
  intros M H i Hi. unfold S6AdlerBase.RO_LO, S6AdlerBase.RO_HI in Hi.
  rewrite <- (u_zw_small i) by lia. change (Z_to_bv 64 (bv_unsigned (zw i))) with (Z_to_bv 64 (bv_unsigned (zw i : word))).
  rewrite Z_to_bv_bv_unsigned. apply H. rewrite u_zw_small by lia. unfold ROD6_LO, ROD6_HI. lia.
Qed.

Lemma zblock_of_zeros_at : forall m a k, 0 <= a -> 0 <= k -> a + k < 2 ^ 64 ->
  (forall x : word, a <= bv_unsigned x < a + k -> m x <> None) -> zeros_at s6_segs m a k -> zblock m a k.
Proof.
  intros m a k Ha Hk Hak Hmp Hz x Hx. exact (pointwise_of_zeros_at m a k Ha Hk ltac:(lia) Hmp Hz x Hx).
Qed.

Lemma uw_fresh_fields : forall s b g,
  let s' := uw_fresh s b g in
  is_mode s' = is_mode s /\ is_last s' = is_last s /\ is_wrap s' = is_wrap s /\ is_havedict s' = is_havedict s /\ is_flags s' = is_flags s
  /\ is_total s' = is_total s /\ is_check s' = is_check s /\ is_wbits s' = is_wbits s /\ is_wsize s' = is_wsize s /\ is_whave s' = is_whave s
  /\ is_wnext s' = is_wnext s /\ is_bits s' = is_bits s /\ is_hold s' = is_hold s
  /\ is_lens s' = is_lens s /\ is_work s' = is_work s /\ is_codes s' = is_codes s
  /\ is_window s' = iarr_u8_of g 0 (shl32 1 (is_wbits s)) /\ is_window_blk s' = Some b
  /\ is_dmax s' = is_dmax s /\ is_head s' = is_head s.
Proof. intros s b g. unfold uw_fresh. destruct s; repeat split; reflexivity. Qed.
Lemma is6_vals_uw_fresh : forall s b g q S, is6_vals (uw_fresh s b g) q S = is6_vals s q S.
Proof. intros s b g q S. unfold is6_vals, isl_vals, uw_fresh. destruct s; reflexivity. Qed.
Lemma sL_uw_fresh : forall s c r b g, sL (uw_fresh s b g) c r = uw_fresh (sL s c r) b g.
Proof.
  intros s c r b g. unfold sL, sT, ckA, uw_fresh, noupd. destruct (_ =? 0); [| destruct (_ =? 1)]; destruct s; reflexivity.
Qed.
Lemma cL_uw_fresh : forall v s c r b g, cL v (uw_fresh s b g) c r = cL v s c r.
Proof.
  intros v s c r b g. unfold cL, dtv. rewrite sL_uw_fresh.
  pose proof (uw_fresh_fields (sL s c r) b g) as F. cbv zeta in F. destruct F as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & F12 & _).
  rewrite F1, F2, F12. unfold ckA. replace (is_check (uw_fresh s b g)) with (is_check s) by (destruct s; reflexivity). reflexivity.
Qed.
Lemma arr_get_fresh0 : forall n i, arr_get (iarr_u8_of (fun _ : Z => 0) 0 n) i = 0.
Proof. intros n i. unfold iarr_u8_of. rewrite arr_get_init. reflexivity. Qed.
Lemma arr_len_fresh : forall g n, arr_len (iarr_u8_of g 0 n) = n.
Proof. intros g n. unfold iarr_u8_of. apply arr_len_init. Qed.

Lemma inflate_p_granted : forall v s zc sx cx rx b g,
  inflateStateCheck s = false ->
  inf_loop ivar_ref (cv_flush v) (W1M s (icall_of_zcall zc)) = (SLeave, mkW sx cx rx) ->
  leave_need (cv_flush v) (sR sx rx) (cR cx rx) rx = true -> is_window_blk sx = None ->
  (is_wrap sx = 5 \/ is_wrap sx = 1) -> is_wbits sx = 15 -> is_wsize sx = 0 -> 0 <= is_wnext sx -> 0 <= is_whave sx ->
  (is_flags sx = 0 \/ ir_out rx = ir_left rx) -> ir_in rx = cv_NI v ->
  0 <= cv_NI v - ir_have rx < 2 ^ 32 -> 0 <= ir_out rx - ir_left rx < 2 ^ 32 ->
  fst (inflate_p ivar_ref (Some (b, g)) s zc (cv_flush v))
  = (uwc (uw_fresh (sL (sR sx rx) (cR cx rx) rx) b g) (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx),
     zret_of_icall (cL v (sR sx rx) (cR cx rx) rx) (retv v (cv_flush v) rx))
  /\ snd (inflate_p ivar_ref (Some (b, g)) s zc (cv_flush v)) <> None.
Proof.
  intros v s zc sx cx rx b g Hchk EQL LN EWB Hwrap Hwbits Hws Hwn Hwh Hfl Hin Bin Bout.
  rewrite (inflate_p_W1M ivar_ref (Some (b, g)) s zc (cv_flush v) Hchk). rewrite EQL.
  unfold inf_leave_p. rewrite RESTORE_eq. cbn [w_s w_c w_r]. rewrite LN.
  pose proof (sR_fields sx rx) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
  pose proof (cR_fields cx rx) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  rewrite Y15, EWB. cbn [fst snd]. split; [| discriminate].
  rewrite Q6, Q3, Q4. rewrite (wrap32_id (ir_out rx - ir_left rx)) by lia.
  pose proof (uw_fresh_fields (sR sx rx) b g) as F. cbv zeta in F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20).
  rewrite (uw_core_eq (uw_fresh (sR sx rx) b g) (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx)
             ltac:(rewrite F8, Y6; exact Hwbits) ltac:(rewrite F9, Y11; left; exact Hws)
             ltac:(rewrite F11, F9, Y13, Y11; split; [exact Hwn | intros E; exfalso; exact (E Hws)])
             ltac:(rewrite F10, F9, Y12, Y11; split; [exact Hwh | intros E; exfalso; exact (E Hws)]) ltac:(lia)).
  pose proof (uwc_fields (uw_fresh (sR sx rx) b g) (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx)) as U. cbv zeta in U.
  destruct U as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11).
  rewrite (leave_tail_eq v (cv_flush v) (uwc (uw_fresh (sR sx rx) b g) (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx)) (cR cx rx) rx
             Q1 Q4 Q3 Hin ltac:(rewrite U5, F3, Y5; exact Hwrap) ltac:(rewrite U7, F5, Y7; exact Hfl) Bin Bout).
  pose proof (sL_uwc v (uw_fresh (sR sx rx) b g) (cR cx rx) rx (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx)) as [E1 E2].
  rewrite E1, E2, sL_uw_fresh, cL_uw_fresh. reflexivity.
Qed.
End FXG.
