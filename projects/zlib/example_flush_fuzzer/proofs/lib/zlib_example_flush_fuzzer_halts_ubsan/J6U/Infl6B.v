(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvLoop.
From Stdlib Require Import NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.Riscv Require Import Decode.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvApi.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateInvCall.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import HarnessKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import HarnessFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6c.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflArmLib6d.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import UpdWin6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateRc.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateCall.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import InflLoop6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import Infl6.
Import InflLv Infl6A.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition ilL : cfg := ilSx [0x215ac; 0x21684] [].

Definition lv_pins : list (Z * expr) :=
  [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (18, EVar 34%nat); (11, EVar 35%nat);
   (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat);
   (26, EAdd (EVar 43%nat) (EVar 44%nat)); (27, EVar 45%nat)].

Lemma pins_of_leave : forall v s c r R,
  LREG_leave v (mkW s c r) R ->
  getr R 2 = zw (cv_sp v - 256) /\ getr R 8 = zw (cv_S v) /\ getr R 13 = zw (cv_ZP v) /\ getr R 18 = zw (cv_ZP v) /\ getr R 11 = zw (cv_flush v)
  /\ getr R 23 = zw (ir_have r) /\ getr R 9 = zw (cv_P0 v + ir_put r)
  /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r) /\ getr R 26 = zw (cv_I0 v + ir_next r)
  /\ getr R 27 = zw (ir_ret r) /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.
Proof.
  intros v s c r R H. unfold LREG_leave, LVARS, INF_FRAME in H. cbn [w_r] in H.
  destruct H as (G2 & G27 & G13 & G8 & G11 & G3 & G4 & (G24 & G9 & G22 & G18 & G25) & G26).
  repeat split; assumption.
Qed.

Lemma cell_lo1 : forall mem a v, cell s6u_segs mem a 4 v -> cell s6u_segs mem a 1 v.
Proof.
  intros mem a v H. unfold cell in *.
  rewrite (rdn_firstn s6u_segs mem 4 (zw a) _ 1 H) by lia. rewrite firstn_Z_to_le_bytes by lia. reflexivity.
Qed.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Lemma sel_flush4 : forall f, 0 <= f <= 4 -> ((f + -4) mod 2 ^ 64 <? 1) = (f =? 4).
Proof.
  intros f Hf. change (2 ^ 64) with 18446744073709551616.
  destruct (Z.eqb_spec f 4) as [->|NE]; [reflexivity|].
  apply Z.ltb_ge. lia.
Qed.
Lemma sel_ret0 : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> (x mod 2 ^ 64 <? 1) = (x =? 0).
Proof.
  intros x Hx. change (2 ^ 64) with 18446744073709551616. change (2 ^ 31) with 2147483648 in Hx.
  destruct (Z.eqb_spec x 0) as [->|NE]; [reflexivity|]. apply Z.ltb_ge. lia.
Qed.
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Lemma sel_inout : forall a b c d, 0 <= a -> 0 <= b -> 0 <= c -> 0 <= d ->
  (Z.lor (Z.lxor a b) (Z.lxor c d) <? 1) = ((a - b =? 0) && (c - d =? 0)).
Proof.
  intros a b c d Ha Hb Hc Hd.
  assert (X1 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  assert (X2 : 0 <= Z.lxor c d) by (apply Z.lxor_nonneg; lia).
  assert (X3 : 0 <= Z.lor (Z.lxor a b) (Z.lxor c d)) by (apply Z.lor_nonneg; lia).
  destruct (Z.eqb_spec (a - b) 0) as [E1|E1]; destruct (Z.eqb_spec (c - d) 0) as [E2|E2]; cbn [andb].
  - replace b with a by lia. replace d with c by lia. rewrite !Z.lxor_nilpotent. cbn. reflexivity.
  - apply Z.ltb_ge. assert (Z.lxor c d <> 0) by (intros E; apply Z.lxor_eq in E; lia).
    assert (Z.lor (Z.lxor a b) (Z.lxor c d) <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia). lia.
  - apply Z.ltb_ge. assert (Z.lxor a b <> 0) by (intros E; apply Z.lxor_eq in E; lia).
    assert (Z.lor (Z.lxor a b) (Z.lxor c d) <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia). lia.
  - apply Z.ltb_ge. assert (Z.lxor a b <> 0) by (intros E; apply Z.lxor_eq in E; lia).
    assert (Z.lor (Z.lxor a b) (Z.lxor c d) <> 0) by (intros E; apply Z.lor_eq_0_iff in E; lia). lia.
Qed.
Lemma sel01 : forall a b c : bool,
  (Z.land (Z.lor (if a then 1 else 0) (if b then 1 else 0)) (if c then 1 else 0) <> 0) <-> ((b || a) && c = true).
Proof. intros [|] [|] [|]; cbv; split; intros H; try reflexivity; try discriminate; exfalso; apply H; reflexivity. Qed.
Lemma sel01f : forall a b c : bool,
  ((b || a) && c = false) -> Z.land (Z.lor (if a then 1 else 0) (if b then 1 else 0)) (if c then 1 else 0) = 0.
Proof. intros [|] [|] [|]; cbv; intros H; try reflexivity; discriminate. Qed.

Lemma lxor_eqb : forall a k, 0 <= a -> 0 <= k -> (Z.lxor a k <? 1) = (a =? k).
Proof.
  intros a k Ha Hk. assert (X : 0 <= Z.lxor a k) by (apply Z.lxor_nonneg; lia).
  destruct (Z.eqb_spec a k) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.ltb_ge. assert (Z.lxor a k <> 0) by (intros E; apply Z.lxor_eq in E; lia). lia.
Qed.
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Lemma last_nz : forall la, - 2 ^ 31 <= la < 2 ^ 31 -> (0 <? szwrap 32 (la mod 2 ^ 32) mod 2 ^ 64) = negb (la =? 0).
Proof.
  intros la H. rewrite szwrap_mod by lia. rewrite szwrap_small by (cbn; lia).
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 31) with 2147483648 in H.
  destruct (Z.eqb_spec la 0) as [->|NE]; cbn [negb]; [reflexivity|]. apply Z.ltb_lt. lia.
Qed.
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Lemma lor01 : forall b3 b4 : bool, Z.lor (if b3 then 1 else 0) (if b4 then 1 else 0) = (if b3 || b4 then 1 else 0).
Proof. intros [|] [|]; reflexivity. Qed.
Lemma dtv_exec : forall bi la mo, - 2 ^ 31 <= la < 2 ^ 31 -> 0 <= mo ->
  (if 0 <? szwrap 32 (la mod 2 ^ 32) mod 2 ^ 64 then 1 else 0) * 2 ^ 6 + bi + (if Z.lxor mo 16191 <? 1 then 1 else 0) * 2 ^ 7
  + Z.lor (if Z.lxor mo 16199 <? 1 then 1 else 0) (if Z.lxor mo 16194 <? 1 then 1 else 0) * 2 ^ 8
  = bi + (if negb (la =? 0) then 64 else 0) + (if mo =? TYPE then 128 else 0) + (if (mo =? LEN_) || (mo =? COPY_) then 256 else 0).
Proof.
  intros bi la mo Hla Hmo. rewrite last_nz by exact Hla. rewrite !lxor_eqb by lia. unfold TYPE, LEN_, COPY_.
  rewrite lor01. destruct (negb (la =? 0)); destruct (mo =? 16191); destruct ((mo =? 16199) || (mo =? 16194)); lia.
Qed.


Definition cR (c : icall) (r : iregs) : icall :=
  icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r).
Definition sR (s : inflate_state) (r : iregs) : inflate_state := iset_bits (iset_hold s (ir_hold r)) (ir_bits r).
Lemma RESTORE_eq : forall s c r, RESTORE (mkW s c r) = mkW (sR s r) (cR c r) r.
Proof. intros. reflexivity. Qed.
Lemma cR_fields : forall c r,
  ic_avail_in (cR c r) = ir_have r /\ ic_next_in (cR c r) = ir_next r /\ ic_next_out (cR c r) = ir_put r /\ ic_avail_out (cR c r) = ir_left r
  /\ ic_input (cR c r) = ic_input c /\ ic_outbuf (cR c r) = ic_outbuf c /\ ic_total_in (cR c r) = ic_total_in c
  /\ ic_total_out (cR c r) = ic_total_out c /\ ic_adler (cR c r) = ic_adler c /\ ic_msg (cR c r) = ic_msg c /\ ic_data_type (cR c r) = ic_data_type c.
Proof. intros c r. destruct c; repeat split; reflexivity. Qed.
Lemma sR_fields : forall s r,
  is_bits (sR s r) = ir_bits r /\ is_hold (sR s r) = ir_hold r /\ is_mode (sR s r) = is_mode s /\ is_last (sR s r) = is_last s
  /\ is_wrap (sR s r) = is_wrap s /\ is_wbits (sR s r) = is_wbits s /\ is_flags (sR s r) = is_flags s /\ is_havedict (sR s r) = is_havedict s
  /\ is_total (sR s r) = is_total s /\ is_check (sR s r) = is_check s /\ is_wsize (sR s r) = is_wsize s /\ is_whave (sR s r) = is_whave s
  /\ is_wnext (sR s r) = is_wnext s /\ is_window (sR s r) = is_window s /\ is_window_blk (sR s r) = is_window_blk s.
Proof. intros s r. destruct s; repeat split; reflexivity. Qed.

Section Leave.
  Variable v : icv.
  Hypothesis C : ictx v.

  Local Abbreviation NI := (cv_NI v). Local Abbreviation NO := (cv_NO v).

  Definition sT (s : inflate_state) (r : iregs) : inflate_state := iset_total s (wrap64 (is_total s + (ir_out r - ir_left r))).
  Definition cT (c : icall) (r : iregs) : icall :=
    icset_total_out (icset_total_in c (wrap64 (ic_total_in c + (NI - ir_have r)))) (wrap64 (ic_total_out c + (ir_out r - ir_left r))).
  Definition noupd (s : inflate_state) (r : iregs) : bool := (ir_out r - ir_left r =? 0) || (is_wrap s =? 1).
  Definition dtv (s : inflate_state) : Z :=
    is_bits s + (if negb (is_last s =? 0) then 64 else 0) + (if is_mode s =? TYPE then 128 else 0)
    + (if (is_mode s =? LEN_) || (is_mode s =? COPY_) then 256 else 0).
  Definition retv (flush : Z) (r : iregs) : Z :=
    if (((NI - ir_have r =? 0) && (ir_out r - ir_left r =? 0)) || (flush =? Z_FINISH)) && (ir_ret r =? Z_OK) then Z_BUF_ERROR else ir_ret r.

  Definition MT1 (s : inflate_state) (c : icall) (r : iregs) (M : word -> option byte) : word -> option byte :=
    let in_ := NI - ir_have r in let out := ir_out r - ir_left r in
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (zw (cv_ZP v)) (Z_to_le_bytes 8 (cv_I0 v + ir_next r)))
      (zw (cv_ZP v + 8)) (Z_to_le_bytes 4 (ir_have r)))
      (zw (cv_ZP v + 16)) (Z_to_le_bytes 8 (wrap64 (ic_total_in c + in_))))
      (zw (cv_ZP v + 24)) (Z_to_le_bytes 8 (cv_P0 v + ir_put r)))
      (zw (cv_ZP v + 32)) (Z_to_le_bytes 4 (ir_left r)))
      (zw (cv_ZP v + 40)) (Z_to_le_bytes 8 (wrap64 (ic_total_out c + out))))
      (zw (cv_S v + 48)) (Z_to_le_bytes 8 (wrap64 (is_total s + out))))
      (zw (cv_S v + 96)) (Z_to_le_bytes 8 (ir_hold r)))
      (zw (cv_S v + 104)) (Z_to_le_bytes 4 (ir_bits r)).

  Lemma MT1_other : forall s c r M (x : word),
    ~ (cv_S v <= bv_unsigned x < cv_S v + 7176) -> ~ (cv_ZP v <= bv_unsigned x < cv_ZP v + 112) ->
    MT1 s c r M x = M x.
  Proof.
    intros s c r M x N2 N3. pose proof (ic_S _ C) as CS. pose proof (ic_ZP _ C) as CZP. pose proof (u64_range x).
    unfold MT1. rewrite !wbytes_inside; [reflexivity | lia | cbn; lia | cbn; lia | lia | cbn; lia | cbn; lia | lia | cbn; lia | cbn; lia
                                     | lia | cbn; lia | cbn; lia | lia | cbn; lia | cbn; lia | lia | cbn; lia | cbn; lia
                                     | lia | cbn; lia | cbn; lia | lia | cbn; lia | cbn; lia | lia | cbn; lia | cbn; lia].
  Qed.
  Lemma MT1_grows : forall s c r M (x : word), M x <> None -> MT1 s c r M x <> None.
  Proof. intros s c r M x Hx. unfold MT1. repeat apply wbytes_grows. exact Hx. Qed.

  Lemma icset_total_in_facts : forall c m,
    ic_next_in (icset_total_in c m) = ic_next_in c /\ ic_avail_in (icset_total_in c m) = ic_avail_in c
    /\ ic_next_out (icset_total_in c m) = ic_next_out c /\ ic_avail_out (icset_total_in c m) = ic_avail_out c
    /\ ic_input (icset_total_in c m) = ic_input c /\ ic_outbuf (icset_total_in c m) = ic_outbuf c
    /\ ic_total_out (icset_total_in c m) = ic_total_out c /\ ic_adler (icset_total_in c m) = ic_adler c
    /\ ic_msg (icset_total_in c m) = ic_msg c /\ ic_data_type (icset_total_in c m) = ic_data_type c
    /\ ic_total_in (icset_total_in c m) = m.
  Proof. intros c m. destruct c. repeat split; reflexivity. Qed.
  Lemma icset_data_type_facts : forall c m,
    ic_next_in (icset_data_type c m) = ic_next_in c /\ ic_avail_in (icset_data_type c m) = ic_avail_in c
    /\ ic_next_out (icset_data_type c m) = ic_next_out c /\ ic_avail_out (icset_data_type c m) = ic_avail_out c
    /\ ic_input (icset_data_type c m) = ic_input c /\ ic_outbuf (icset_data_type c m) = ic_outbuf c
    /\ ic_total_out (icset_data_type c m) = ic_total_out c /\ ic_adler (icset_data_type c m) = ic_adler c
    /\ ic_msg (icset_data_type c m) = ic_msg c /\ ic_total_in (icset_data_type c m) = ic_total_in c
    /\ ic_data_type (icset_data_type c m) = m.
  Proof. intros c m. destruct c. repeat split; reflexivity. Qed.

  Lemma LMEM_store_total_in : forall s c r M m,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW s (icset_total_in c m) r) (wbytes M (zw (cv_ZP v + 16)) (Z_to_le_bytes 8 m)).
  Proof.
    intros s c r M m HM Hput.
    open_ictx C. open_lmem HM.
    pose proof (icset_total_in_facts c m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | cbn; lia |]. unfold offimg, IMG6_TOP in CoZ. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoZ CZP. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6u_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | cbn; lia |].
      unfold sep in CZS. unfold is6_SIZE. clear - CZS CZP CS. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | cbn; lia | unfold sep in CZS; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZW. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZI. cbn. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | cbn; lia |]. unfold sep in CZO. cbn. lia.
    - unfold izs6 in *. rewrite F7, F8, F9, ?F10, F11.
      destruct Mzs as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      repeat match goal with |- _ /\ _ => split end;
        try (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | cbn; lia]).
      apply cell_write_same; [lia | cbn; lia].
    - apply (iframe6_other v C); [exact Mfr | lia | cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Mleftc |- *; apply (cell_write_other _ _ _ _ _ _ _ Mleftc); [lia | cbn; lia | lia | cbn; lia | unfold sep in CfZ; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

  Lemma LMEM_store_dt : forall s c r M m bs,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v -> length bs = 4%nat ->
    LMEM v (mkW s (icset_data_type c m) r) (wbytes M (zw (cv_ZP v + 88)) bs).
  Proof.
    intros s c r M m bs HM Hput Hl.
    open_ictx C. open_lmem HM.
    pose proof (icset_data_type_facts c m) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    constructor; cbn [w_s w_c w_r]; rewrite ?F1, ?F2, ?F3, ?F4, ?F5, ?F6.
    - intros x Hx. rewrite wbytes_inside; [exact (Mrod x Hx) | lia | rewrite Hl; cbn; lia |]. unfold offimg, IMG6_TOP in CoZ. unfold ROD6_LO, ROD6_HI in Hx. clear - Hx CoZ CZP Hl. rewrite Hl. cbn. lia.
    - unfold is6_scalars in *. apply (fields_write_other s6u_segs _ _ is6_layout _ is6_SIZE _ _ Msc is6_layout_within); [lia | unfold is6_SIZE; lia | lia | rewrite Hl; cbn; lia |].
      unfold sep in CZS. unfold is6_SIZE. clear - CZS CZP CS Hl. rewrite Hl. cbn. lia.
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mlens); [cbn; lia | lia | lia | lia | rewrite Hl; cbn; lia | unfold sep in CZS; rewrite Hl; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mwork); [cbn; lia | lia | lia | lia | rewrite Hl; cbn; lia | unfold sep in CZS; rewrite Hl; cbn; lia].
    - apply (cells_write_other _ _ _ _ _ _ _ _ _ Mcodes); [cbn; lia | lia | lia | lia | rewrite Hl; cbn; lia | unfold sep in CZS; rewrite Hl; cbn; lia].
    - intros Hwn. apply (cells_write_other _ _ _ _ _ _ _ _ _ (Mwin Hwn)); [cbn; lia | lia | lia | lia | rewrite Hl; cbn; lia |]. unfold sep in CZW. rewrite Hl. cbn. lia.
    - destruct (Z.eq_dec (cv_NI v) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Minp); [cbn; lia | lia | lia | lia | rewrite Hl; cbn; lia |]. unfold sep in CZI. rewrite Hl. cbn. lia.
    - destruct (Z.eq_dec (ir_put r) 0) as [E0|E0]; [rewrite E0; apply cells_nil|].
      apply (cells_write_other _ _ _ _ _ _ _ _ _ Mout); [cbn; lia | lia | lia | lia | rewrite Hl; cbn; lia |]. unfold sep in CZO. rewrite Hl. cbn. lia.
    - unfold izs6 in *. rewrite F7, F8, F9, F10.
      destruct Mzs as (Z0 & Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z96).
      repeat match goal with |- _ /\ _ => split end;
        (eapply cell_write_other; [eassumption | lia | cbn; lia | lia | rewrite Hl; cbn; lia | rewrite Hl; cbn; lia]).
    - apply (iframe6_other v C); [exact Mfr | lia | rewrite Hl; cbn; lia | unfold iframe6_ok, INF_FRAME; unfold sep in CfZ; rewrite Hl; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Moutc |- *; apply (cell_write_other _ _ _ _ _ _ _ Moutc); [lia | rewrite ?Hl; cbn; lia | lia | rewrite ?Hl; cbn; lia | unfold sep in CfZ; rewrite ?Hl; cbn; lia].
    - pose proof (ic_sp _ C) as Csp_o; unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp_o, Mleftc |- *; apply (cell_write_other _ _ _ _ _ _ _ Mleftc); [lia | rewrite ?Hl; cbn; lia | lia | rewrite ?Hl; cbn; lia | unfold sep in CfZ; rewrite ?Hl; cbn; lia].
    - apply mapped_wbytes. exact Mmap_f.
    - apply mapped_wbytes. exact Mmap_Z.
    - apply mapped_wbytes. exact Mmap_S.
    - apply mapped_wbytes. exact Mmap_P.
    - intros Hwn. apply mapped_wbytes. exact (Mmap_W Hwn).
  Qed.

  Lemma LMEM_MT1 : forall s c r M,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v ->
    LMEM v (mkW (sT (sR s r) r) (cT (cR c r) r) r) (MT1 s c r M).
  Proof.
    intros s c r M HM Hput. pose proof (ic_S _ C) as CS.
    pose proof (LMEM_store_next_in v C s c r M (ir_next r) HM Hput) as H1. rewrite (Z.add_0_r (cv_ZP v)) in H1.
    pose proof (LMEM_store_avail_in v C s _ r _ (ir_have r) H1 Hput) as H2.
    pose proof (LMEM_store_total_in s _ r _ (wrap64 (ic_total_in c + (NI - ir_have r))) H2 Hput) as H3.
    pose proof (LMEM_store_next_out v C s _ r _ (ir_put r) H3 Hput) as H4.
    pose proof (LMEM_store_avail_out v C s _ r _ (ir_left r) H4 Hput) as H5.
    pose proof (LMEM_store_total_out v C s _ r _ (wrap64 (ic_total_out c + (ir_out r - ir_left r))) H5 Hput) as H6.
    match type of H6 with LMEM _ (mkW _ ?c6 _) ?M6 =>
      replace (cT (cR c r) r) with c6 by (destruct c; reflexivity);
      assert (H7 : LMEM v (mkW (iset_total s (wrap64 (is_total s + (ir_out r - ir_left r)))) c6 r) (wbytes M6 (zw (cv_S v + 48)) (Z_to_le_bytes 8 (wrap64 (is_total s + (ir_out r - ir_left r))))))
    end.
    { eapply (LMEM_store_scalar v C s _ r _ _ 48 _ H6); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_total _ (cv_S v) _ s _ (lm_sc _ _ _ H6)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    match type of H7 with LMEM _ (mkW ?s7 ?c7 _) ?M7 =>
      assert (H8 : LMEM v (mkW (iset_hold s7 (ir_hold r)) c7 r) (wbytes M7 (zw (cv_S v + 96)) (Z_to_le_bytes 8 (ir_hold r))))
    end.
    { eapply (LMEM_store_scalar v C _ _ r _ _ 96 _ H7); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_hold _ (cv_S v) _ _ (ir_hold r) (lm_sc _ _ _ H7)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    replace (sT (sR s r) r) with (iset_bits (iset_hold (iset_total s (wrap64 (is_total s + (ir_out r - ir_left r)))) (ir_hold r)) (ir_bits r)) by (destruct s; reflexivity).
    unfold MT1.
    eapply (LMEM_store_scalar v C _ _ r _ _ 104 _ H8); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
    apply (is6_upd_bits _ (cv_S v) _ _ (ir_bits r) (lm_sc _ _ _ H8)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia].
  Qed.

  Lemma sT_fields : forall s r,
    is_bits (sT s r) = is_bits s /\ is_hold (sT s r) = is_hold s /\ is_mode (sT s r) = is_mode s /\ is_last (sT s r) = is_last s
    /\ is_wrap (sT s r) = is_wrap s /\ is_wbits (sT s r) = is_wbits s /\ is_flags (sT s r) = is_flags s /\ is_check (sT s r) = is_check s
    /\ is_wsize (sT s r) = is_wsize s /\ is_window (sT s r) = is_window s /\ is_window_blk (sT s r) = is_window_blk s.
  Proof. intros s r. destruct s; repeat split; reflexivity. Qed.
  Lemma cT_fields : forall c r,
    ic_next_out (cT c r) = ic_next_out c /\ ic_input (cT c r) = ic_input c /\ ic_msg (cT c r) = ic_msg c
    /\ ic_next_in (cT c r) = ic_next_in c /\ ic_avail_in (cT c r) = ic_avail_in c /\ ic_avail_out (cT c r) = ic_avail_out c
    /\ ic_outbuf (cT c r) = ic_outbuf c.
  Proof. intros c r. destruct c; repeat split; reflexivity. Qed.

  Lemma lv_T1 : forall s c r R M,
    LMEM v (mkW s c r) M -> LREG_leave v (mkW s c r) R -> RINV NI NO r -> CINV NI NO c ->
    ir_in r = NI -> (is_wrap s = 5 \/ is_wrap s = 1) -> (is_flags s = 0 \/ ir_out r = ir_left r) ->
    0 <= is_total s < 2 ^ 64 -> 0 <= is_check s < 2 ^ 64 -> - 2 ^ 31 <= ir_ret r < 2 ^ 31 ->
    let out := ir_out r - ir_left r in
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_leave) M s6u_rom)
                      (mkst R1 (Z_to_bv 64 (if noupd s r then 0x215ac else A6U_ADLER32)) (MT1 s c r M) s6u_rom)
      /\ LMEM v (mkW (sT (sR s r) r) (cT (cR c r) r) r) (MT1 s c r M)
      /\ (forall rg : reg, reg_in rg [1; 10; 11; 12; 13; 14; 15; 16; 20]%bv = false -> getr R1 rg = getr R rg)
      /\ getr R1 20 = zw out /\ getr R1 2 = zw (cv_sp v - 256)
      /\ getr R1 27 = zw (ir_ret r) /\ getr R1 23 = zw (ir_have r) /\ getr R1 9 = zw (cv_P0 v + ir_put r) /\ getr R1 8 = zw (cv_S v)
      /\ getr R1 18 = zw (cv_ZP v) /\ getr R1 19 = zw (ir_bits r) /\ getr R1 3 = getr (cv_R0 v) 3 /\ getr R1 4 = getr (cv_R0 v) 4
      /\ (noupd s r = true -> getr R1 13 = zw (cv_ZP v) /\ getr R1 11 = zw (cv_flush v))
      /\ (noupd s r = false -> getr R1 10 = zw (is_check s) /\ getr R1 11 = zw (cv_P0 v + (ir_put r - out)) /\ getr R1 12 = zw out
                     /\ getr R1 1 = zw 0x2159c).
  Proof.
    intros s c r R M HM HR RI CI Hin Hw Hf Htot Hck Hret. cbv zeta.
    pose proof (pins_of_leave _ _ _ _ _ HR) as (P2 & P27 & P13 & P8 & P11 & P24 & P9 & P22 & P18 & P25 & P26 & P3 & P4).
    open_ictx C. pose proof HM as HM0. open_lmem HM. open_frame Mfr. open_zs Mzs. open_rinv RI. open_cinv CI. unfold mapped in *.
    pose proof (is6_total _ _ _ _ Msc) as C40. pose proof (is6_wrap _ _ _ _ Msc) as C16.
    pose proof (is6_flags _ _ _ _ Msc) as C24. pose proof (is6_check _ _ _ _ Msc) as C32.
    assert (Hput : 0 <= ir_put r <= NO) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hout : 0 <= ir_out r - ir_left r <= ir_put r /\ ir_out r - ir_left r < 2 ^ 31) by (clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia).
    assert (HinB : 0 <= NI - ir_have r < 2 ^ 31) by (clear - Rnx0 Rhv0 Rnh CI0; lia).
    assert (P26' : getr R 27 = zw (ir_ret r mod 2 ^ 64)) by (rewrite zw_mod; exact P26).
    assert (Hrm : 0 <= ir_ret r mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    pose proof (LMEM_MT1 s c r M HM0 Hput) as HM9.
    Local Ltac t1_regs HR1 Hfr1 P26 P24 P9 P27 P8 P18 P3 P4 :=
      let Q19 := fresh "Q19" in
      split; [fr_weak Hfr1|];
      split; [symex_reg HR1 (20%bv : reg) as Q19; rewrite Q19; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; first [reflexivity | f_equal; lia]|];
      split; [rewrite (Hfr1 (2%bv : reg) eq_refl); assumption|];
      split; [rewrite (Hfr1 (27%bv : reg) eq_refl); exact P26|];
      split; [rewrite (Hfr1 (23%bv : reg) eq_refl); exact P24|];
      split; [rewrite (Hfr1 (9%bv : reg) eq_refl); exact P9|];
      split; [rewrite (Hfr1 (8%bv : reg) eq_refl); exact P27|];
      split; [rewrite (Hfr1 (18%bv : reg) eq_refl); exact P8|];
      split; [rewrite (Hfr1 (19%bv : reg) eq_refl); exact P18|];
      split; [rewrite (Hfr1 (3%bv : reg) eq_refl); exact P3|];
      split; [rewrite (Hfr1 (4%bv : reg) eq_refl); exact P4|].
    destruct Hw as [Hw|Hw]; rewrite Hw in C16; pose proof (cell_lo1 _ _ _ C16) as C16b.
    2:{
      replace (noupd s r) with true by (unfold noupd; rewrite Hw, orb_true_r; reflexivity).
      arm_symexP lv_pins ilL 40%nat [true]
        [RVal (EVar 39%nat); RVal (EVar 42%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat); RVal (EVar 49%nat); RVal (ELit 1)]
        (@nil (Z * expr)) [(45%nat, 2 ^ 64); (46%nat, 2 ^ 31); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64); (49%nat, 2 ^ 64)] v r
        [ir_ret r mod 2 ^ 64; NI; ic_total_in c; ic_total_out c; is_total s] NoVals F0
        (mkst R (Z_to_bv 64 pc6_leave) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTT1w" G end.
      rewrite ?(Z.mod_small (NI - ir_have r) (2 ^ 32)) in Hms1 by (clear - HinB; lia).
      rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) in Hms1 by (clear - Hout; lia).
      rewrite ?szwrap32_small in Hms1 by (clear - HinB Hout; lia).
      rewrite ?(Z.mod_small (NI - ir_have r) (2 ^ 32)) in Hms1 by (clear - HinB; lia).
      rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) in Hms1 by (clear - Hout; lia).
      rewrite <- ?(le8_wrap64 (ic_total_in c + _)), <- ?(le8_wrap64 (ic_total_out c + _)), <- ?(le8_wrap64 (is_total s + _)) in Hms1.
      exists R1. split; [unfold MT1; by_run Hms1|]. split; [exact HM9|].
      t1_regs HR1 Hfr1 P26 P24 P9 P27 P8 P18 P3 P4.
      split; [intros _; split; [rewrite (Hfr1 (13%bv : reg) eq_refl); exact P13 | rewrite (Hfr1 (11%bv : reg) eq_refl); exact P11]|].
      intros X; discriminate X. }
    replace (noupd s r) with (ir_out r - ir_left r =? 0) by (unfold noupd; rewrite Hw; cbn [Z.eqb Pos.eqb]; rewrite orb_false_r; reflexivity).
    destruct (Z.eqb_spec (ir_out r - ir_left r) 0) as [E0|E0].
    -
      assert (Eol : ir_out r = ir_left r) by (clear - E0; lia).
      arm_symexP lv_pins ilL 40%nat [false; true]
        [RVal (EVar 39%nat); RVal (EVar 42%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat); RVal (EVar 49%nat); RVal (ELit 5)]
        (@nil (Z * expr)) [(45%nat, 2 ^ 64); (46%nat, 2 ^ 31); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64); (49%nat, 2 ^ 64)] v r
        [ir_ret r mod 2 ^ 64; NI; ic_total_in c; ic_total_out c; is_total s] NoVals F0
        (mkst R (Z_to_bv 64 pc6_leave) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTT1a" G end.
      rewrite ?(Z.mod_small (NI - ir_have r) (2 ^ 32)) in Hms1 by (clear - HinB; lia).
      rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) in Hms1 by (clear - Hout; lia).
      rewrite ?szwrap32_small in Hms1 by (clear - HinB Hout; lia).
      rewrite ?(Z.mod_small (NI - ir_have r) (2 ^ 32)) in Hms1 by (clear - HinB; lia).
      rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) in Hms1 by (clear - Hout; lia).
      rewrite <- ?(le8_wrap64 (ic_total_in c + _)), <- ?(le8_wrap64 (ic_total_out c + _)), <- ?(le8_wrap64 (is_total s + _)) in Hms1.
      exists R1. split; [unfold MT1; by_run Hms1|]. split; [exact HM9|].
      t1_regs HR1 Hfr1 P26 P24 P9 P27 P8 P18 P3 P4.
      split; [intros _; split; [rewrite (Hfr1 (13%bv : reg) eq_refl); exact P13 | rewrite (Hfr1 (11%bv : reg) eq_refl); exact P11]|].
      intros X; discriminate X.
    -
      destruct Hf as [Hf|Hf]; [| exfalso; clear - E0 Hf; lia].
      rewrite Hf in C24.
      arm_symexP lv_pins ilL 50%nat [false; false; true; false]
        [RVal (EVar 39%nat); RVal (EVar 42%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat); RVal (EVar 49%nat); RVal (ELit 5);
         RVal (ELit 0); RVal (EVar 50%nat)]
        (@nil (Z * expr)) [(45%nat, 2 ^ 64); (46%nat, 2 ^ 31); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64); (49%nat, 2 ^ 64); (50%nat, 2 ^ 64)] v r
        [ir_ret r mod 2 ^ 64; NI; ic_total_in c; ic_total_out c; is_total s; is_check s] NoVals F0
        (mkst R (Z_to_bv 64 pc6_leave) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: try (rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) by (clear - Hout; lia); rewrite ?szwrap32_small by (clear - Hout; lia);
                rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) by (clear - Hout; lia); clear - Hout Hput CP0; ub_ptr_side).
      all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTT1b" G end.
      rewrite ?(Z.mod_small (NI - ir_have r) (2 ^ 32)) in Hms1 by (clear - HinB; lia).
      rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) in Hms1 by (clear - Hout; lia).
      rewrite ?szwrap32_small in Hms1 by (clear - HinB Hout; lia).
      rewrite ?(Z.mod_small (NI - ir_have r) (2 ^ 32)) in Hms1 by (clear - HinB; lia).
      rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) in Hms1 by (clear - Hout; lia).
      rewrite <- ?(le8_wrap64 (ic_total_in c + _)), <- ?(le8_wrap64 (ic_total_out c + _)), <- ?(le8_wrap64 (is_total s + _)) in Hms1.
      exists R1. split; [unfold MT1; by_run Hms1|]. split; [exact HM9|].
      t1_regs HR1 Hfr1 P26 P24 P9 P27 P8 P18 P3 P4.
      split; [intros X; discriminate X|].
      intros _. split; [symex_reg HR1 (10%bv : reg) as Q; exact Q|].
      split; [symex_reg HR1 (11%bv : reg) as Q; rewrite Q; rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) by (clear - Hout; lia); rewrite ?szwrap32_small by (clear - Hout; lia); rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) by (clear - Hout; lia); f_equal; lia|].
      split; [symex_reg HR1 (12%bv : reg) as Q; rewrite Q; rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) by (clear - Hout; lia); rewrite ?szwrap32_small by (clear - Hout; lia); rewrite ?(Z.mod_small (ir_out r - ir_left r) (2 ^ 32)) by (clear - Hout; lia); first [reflexivity | f_equal; lia]|].
      symex_reg HR1 (1%bv : reg) as Q; exact Q.
  Qed.

  Lemma lv_T2 : forall s c r R M A,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v -> 0 <= A < 2 ^ 64 ->
    getr R 2 = zw (cv_sp v - 256) -> getr R 8 = zw (cv_S v) -> getr R 18 = zw (cv_ZP v) -> getr R 10 = zw A ->
    let M' := wbytes (wbytes M (zw (cv_S v + 40)) (Z_to_le_bytes 8 A)) (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 A) in
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x2159c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x215ac) M' s6u_rom)
      /\ LMEM v (mkW (iset_check s A) (icset_adler c A) r) M'
      /\ getr R1 13 = zw (cv_ZP v) /\ getr R1 11 = zw (cv_flush v)
      /\ (forall rg : reg, reg_in rg [11; 13]%bv = false -> getr R1 rg = getr R rg).
  Proof.
    intros s c r R M A HM Hput HA G2 G27 G8 G10. cbv zeta.
    open_ictx C. pose proof HM as HM0. open_lmem HM. open_frame Mfr. unfold mapped in *.
    symex s6u_segs ilL 12%nat (@nil bool) [RVal (EVar 35%nat)]
      [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (10, EVar 36%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 5); (36%nat, 2 ^ 64)] NoRegions
      [cv_sp v - 256; cv_S v; cv_ZP v; cv_flush v; A] NoVals F0 F0'
      (mkst R (Z_to_bv 64 0x2159c) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTT2" G end.
    exists R1. split; [by_run Hms1|].
    split.
    { apply (LMEM_store_adler v C (iset_check s A) c r _ A); [| exact Hput].
      apply (LMEM_store_scalar v C s c r _ M 40 _ HM0); [lia | cbn; lia | exact Hput | | destruct s; reflexivity | destruct s; reflexivity | destruct s; reflexivity | destruct s; reflexivity].
      apply (is6_upd_check M (cv_S v) _ s A Msc); [clear - CS; lia | unfold is6_SIZE; clear - CS; lia]. }
    split; [symex_reg HR1 (13%bv : reg) as Q13; exact Q13|]. split; [symex_reg HR1 (11%bv : reg) as Q11; exact Q11|].
    fr_weak Hfr1.
  Qed.

  Definition needv (s : inflate_state) (r : iregs) : bool :=
    negb (is_wsize s =? 0) || (negb (ir_out r - ir_left r =? 0) && (is_mode s <? BAD) && ((is_mode s <? CHECK) || negb (cv_flush v =? Z_FINISH))).

  Lemma needv_leave_need : forall s c r,
    ic_avail_out c = ir_left r -> leave_need (cv_flush v) s c r = needv s r.
  Proof.
    intros s c r Hao. unfold leave_need, needv. rewrite Hao.
    replace (ir_out r =? ir_left r) with (ir_out r - ir_left r =? 0); [reflexivity|].
    destruct (Z.eqb_spec (ir_out r) (ir_left r)); destruct (Z.eqb_spec (ir_out r - ir_left r) 0); try reflexivity; lia.
  Qed.

  Definition t3_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (18, EVar 34%nat); (11, EVar 35%nat);
     (20, ESub (EVar 42%nat) (EVar 39%nat))].
  Definition t3_vb : list (nat * Z) := [(45%nat, 64); (46%nat, 16211); (47%nat, 2 ^ 32); (48%nat, 32769)].

  Lemma dtv_execU : forall bi la mo, - 2 ^ 31 <= la < 2 ^ 31 -> 0 <= mo ->
    bi + (if 0 <? szwrap 32 (la mod 2 ^ 32) mod 2 ^ 64 then 1 else 0) * 2 ^ 6 + (if Z.lxor mo 16191 <? 1 then 1 else 0) * 2 ^ 7
    + Z.lor (if Z.lxor mo 16199 <? 1 then 1 else 0) (if Z.lxor mo 16194 <? 1 then 1 else 0) * 2 ^ 8
    = bi + (if negb (la =? 0) then 64 else 0) + (if mo =? TYPE then 128 else 0) + (if (mo =? LEN_) || (mo =? COPY_) then 256 else 0).
  Proof.
    intros bi la mo Hla Hmo. rewrite <- (dtv_exec bi la mo Hla Hmo). lia.
  Qed.

  Lemma lv_T3 : forall s c r R M,
    LMEM v (mkW s c r) M -> RINV NI NO r -> ic_next_out c = ir_put r ->
    0 <= is_bits s < 64 -> - 2 ^ 31 <= is_last s < 2 ^ 31 -> HEAD <= is_mode s <= MEM -> (is_wsize s = 0 \/ is_wsize s = 32768) ->
    getr R 2 = zw (cv_sp v - 256) -> getr R 8 = zw (cv_S v) -> getr R 13 = zw (cv_ZP v) -> getr R 18 = zw (cv_ZP v) -> getr R 11 = zw (cv_flush v) ->
    getr R 20 = zw (ir_out r - ir_left r) ->
    exists R1 bs,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x215ac) M s6u_rom)
                     (mkst R1 (Z_to_bv 64 (if needv s r then pc6_uw else 0x21684)) (wbytes M (zw (cv_ZP v + 88)) bs) s6u_rom)
      /\ length bs = 4%nat /\ bs = Z_to_le_bytes 4 (dtv s)
      /\ getr R1 2 = zw (cv_sp v - 256)
      /\ (forall rg : reg, reg_in rg [1; 10; 11; 12; 14; 15; 16]%bv = false -> getr R1 rg = getr R rg)
      /\ (needv s r = true -> getr R1 10 = zw (cv_ZP v) /\ getr R1 11 = zw (cv_P0 v + ir_put r) /\ getr R1 12 = zw (ir_out r - ir_left r)
                           /\ getr R1 1 = zw pc6_uw_ret)
      /\ (needv s r = false -> getr R1 11 = zw (cv_flush v)).
  Proof.
    intros s c r R M HM RI Hno Hbits Hlast Hmode Hws G2 G27 G13 G8 G11 G19.
    open_ictx C. open_lmem HM. open_zs Mzs. open_rinv RI. unfold mapped in *. unfold HEAD, MEM in Hmode.
    pose proof (is6_mode _ _ _ _ Msc) as C8. pose proof (is6_last _ _ _ _ Msc) as C12. pose proof (is6_wsize _ _ _ _ Msc) as C60.
    pose proof (is6_bits _ _ _ _ Msc) as C88.
    rewrite Hno in Z24.
    assert (Hla : - 2 ^ 31 <= is_last s < 2 ^ 31) by exact Hlast.
    assert (Hmo : 0 <= is_mode s) by (clear - Hmode; lia).
    assert (Blast : 0 <= is_last s mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
    assert (Hws' : 0 <= is_wsize s < 32769) by (clear - Hws; lia).
    assert (Hout : 0 <= ir_out r - ir_left r <= ir_put r /\ ir_out r - ir_left r < 2 ^ 31) by (clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia).
    assert (G19' : getr R 20 = zw (ir_out r - ir_left r)) by exact G19.
    unfold needv, BAD, CHECK, Z_FINISH.
    Local Ltac t3_post R1 HR1 Hfr1 Hms1 s Hla Hmo G2 :=
      rewrite (dtv_execU (is_bits s) (is_last s) (is_mode s) Hla Hmo) in Hms1;
      eexists R1, _; split; [by_run Hms1|]; split; [reflexivity|]; split; [reflexivity|];
      split; [rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2|];
      split; [fr_weak Hfr1|];
      split;
      [ let Hnd := fresh "Hnd" in intros Hnd;
        first [ discriminate Hnd
              | let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in let Q12 := fresh "Q12" in let Q1 := fresh "Q1" in
                split; [symex_reg HR1 (10%bv : reg) as Q10; exact Q10|];
                split; [symex_reg HR1 (11%bv : reg) as Q11; exact Q11|];
                split; [symex_reg HR1 (12%bv : reg) as Q12; rewrite Q12; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; first [reflexivity | f_equal; lia]
                       | symex_reg HR1 (1%bv : reg) as Q1; exact Q1]
              | match goal with |- ?G => idtac "T3POSTT LEFT" G end ]
      | let Hnd := fresh "Hnd" in intros Hnd;
        first [ discriminate Hnd
              | rewrite (Hfr1 (11%bv : reg) eq_refl); assumption
              | match goal with |- ?G => idtac "T3POSTF LEFT" G end ] ].
    destruct (Z.eqb_spec (is_wsize s) 0) as [W0|W1]; cbn [negb orb].
    - destruct (Z.eqb_spec (ir_out r - ir_left r) 0) as [O0|O1]; cbn [negb andb].
      + arm_symexP t3_pins ilL 50%nat [false; false; false; true; true]
          [RVal (EVar 47%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 48%nat); RVal (EVar 39%nat); RVal (EVar 42%nat)]
          (@nil (Z * expr)) t3_vb v r [is_bits s; is_mode s; is_last s mod 2 ^ 32; is_wsize s] NoVals F0
          (mkst R (Z_to_bv 64 0x215ac) M s6u_rom) R1 HR1 Hfr1 Hms1.
        all: try arm_side.
        all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT3B" G end.
        t3_post R1 HR1 Hfr1 Hms1 s Hla Hmo G2.
      + destruct (Z.ltb_spec (is_mode s) 16209) as [B0|B1]; cbn [andb].
        * destruct (Z.eqb_spec (cv_flush v) 4) as [F4|F4]; cbn [negb orb].
          -- destruct (Z.ltb_spec (is_mode s) 16206) as [K0|K1].
             ++ arm_symexP t3_pins ilL 50%nat [false; false; false; true; false; false; false; true]
                  [RVal (EVar 47%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 48%nat); RVal (EVar 39%nat); RVal (EVar 42%nat); RVal (EAdd (EVar 37%nat) (EVar 38%nat))]
                  (@nil (Z * expr)) t3_vb v r [is_bits s; is_mode s; is_last s mod 2 ^ 32; is_wsize s] NoVals F0
                  (mkst R (Z_to_bv 64 0x215ac) M s6u_rom) R1 HR1 Hfr1 Hms1.
                all: try arm_side.
                all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT3E" G end.
                t3_post R1 HR1 Hfr1 Hms1 s Hla Hmo G2.
             ++ arm_symexP t3_pins ilL 50%nat [false; false; false; true; false; false; false; false]
                  [RVal (EVar 47%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 48%nat); RVal (EVar 39%nat); RVal (EVar 42%nat)]
                  (@nil (Z * expr)) t3_vb v r [is_bits s; is_mode s; is_last s mod 2 ^ 32; is_wsize s] NoVals F0
                  (mkst R (Z_to_bv 64 0x215ac) M s6u_rom) R1 HR1 Hfr1 Hms1.
                all: try arm_side.
                all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT3F" G end.
                t3_post R1 HR1 Hfr1 Hms1 s Hla Hmo G2.
          -- arm_symexP t3_pins ilL 50%nat [false; false; false; true; false; false; true]
               [RVal (EVar 47%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 48%nat); RVal (EVar 39%nat); RVal (EVar 42%nat); RVal (EAdd (EVar 37%nat) (EVar 38%nat))]
               (@nil (Z * expr)) t3_vb v r [is_bits s; is_mode s; is_last s mod 2 ^ 32; is_wsize s] NoVals F0
               (mkst R (Z_to_bv 64 0x215ac) M s6u_rom) R1 HR1 Hfr1 Hms1.
             all: try arm_side.
             all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT3D" G end.
             replace ((is_mode s <? 16206) || true) with true by (destruct (is_mode s <? 16206); reflexivity).
             t3_post R1 HR1 Hfr1 Hms1 s Hla Hmo G2.
        * arm_symexP t3_pins ilL 50%nat [false; false; false; true; false; true]
            [RVal (EVar 47%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 48%nat); RVal (EVar 39%nat); RVal (EVar 42%nat)]
            (@nil (Z * expr)) t3_vb v r [is_bits s; is_mode s; is_last s mod 2 ^ 32; is_wsize s] NoVals F0
            (mkst R (Z_to_bv 64 0x215ac) M s6u_rom) R1 HR1 Hfr1 Hms1.
          all: try arm_side.
          all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT3C" G end.
          t3_post R1 HR1 Hfr1 Hms1 s Hla Hmo G2.
    - arm_symexP t3_pins ilL 50%nat [false; false; false; false]
        [RVal (EVar 47%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 48%nat); RVal (EAdd (EVar 37%nat) (EVar 38%nat))]
        (@nil (Z * expr)) t3_vb v r [is_bits s; is_mode s; is_last s mod 2 ^ 32; is_wsize s] NoVals F0
        (mkst R (Z_to_bv 64 0x215ac) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT3A" G end.
      t3_post R1 HR1 Hfr1 Hms1 s Hla Hmo G2.
  Qed.

  Lemma lv_ret : forall s c r R M,
    LMEM v (mkW s c r) M -> RINV NI NO r -> - 2 ^ 31 <= ir_ret r < 2 ^ 31 ->
    getr R 2 = zw (cv_sp v - 256) -> getr R 11 = zw (cv_flush v) ->
    getr R 23 = zw (ir_have r) -> getr R 27 = zw (ir_ret r) ->
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x21684) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_ret) M s6u_rom)
      /\ getr R1 10 = zw (retv (cv_flush v) r) /\ getr R1 2 = zw (cv_sp v - 256)
      /\ (forall rg : reg, reg_in rg [10; 11; 12; 13; 27]%bv = false -> getr R1 rg = getr R rg).
  Proof.
    intros s c r R M HM RI Hret G2 G11 G24 G26.
    open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. unfold mapped in *.
    assert (G26' : getr R 27 = zw (ir_ret r mod 2 ^ 64)) by (rewrite zw_mod; exact G26).
    assert (Hrm : 0 <= ir_ret r mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct ((((NI - ir_have r =? 0) && (ir_out r - ir_left r =? 0)) || (cv_flush v =? Z_FINISH)) && (ir_ret r =? Z_OK)) eqn:ER;
      unfold Z_FINISH, Z_OK in ER;
      [ pose proof (proj2 (sel01 ((cv_flush v + -4) mod 2 ^ 64 <? 1) (Z.lor (Z.lxor NI (ir_have r)) (Z.lxor (ir_out r) (ir_left r)) <? 1) (ir_ret r mod 2 ^ 64 <? 1))
                      ltac:(rewrite sel_flush4, sel_ret0, sel_inout by (clear - Cflush Hret Rhv0 Rnh Rnx0 Rlf0 Rout CI0; lia); exact ER)) as BR
      | pose proof (sel01f ((cv_flush v + -4) mod 2 ^ 64 <? 1) (Z.lor (Z.lxor NI (ir_have r)) (Z.lxor (ir_out r) (ir_left r)) <? 1) (ir_ret r mod 2 ^ 64 <? 1)
                      ltac:(rewrite sel_flush4, sel_ret0, sel_inout by (clear - Cflush Hret Rhv0 Rnh Rnx0 Rlf0 Rout CI0; lia); exact ER)) as BR ].
    - symex s6u_segs ilL 30%nat [false] [RVal (EVar 45%nat); RVal (EVar 39%nat); RVal (EVar 42%nat)]
        [(2, EVar 32%nat); (11, EVar 35%nat); (23, EVar 36%nat); (27, EVar 46%nat)]
        [(32%nat, 2 ^ 63); (35%nat, 5); (36%nat, 2 ^ 31); (39%nat, 2 ^ 31); (42%nat, 2 ^ 31); (45%nat, 2 ^ 31); (46%nat, 2 ^ 64)] NoRegions
        [cv_sp v - 256; 0; 0; cv_flush v; ir_have r; 0; 0; ir_left r; 0; 0; ir_out r; 0; 0; NI; ir_ret r mod 2 ^ 64] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x21684) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTRETa" G end.
      exists R1. split; [by_run Hms1|].
      split; [symex_reg HR1 (10%bv : reg) as Q; rewrite Q; unfold retv, Z_FINISH, Z_OK, Z_BUF_ERROR; rewrite ER; first [reflexivity | apply zw_mod]|].
      split; [rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2 | fr_weak Hfr1].
    - symex s6u_segs ilL 30%nat [true] [RVal (EVar 45%nat); RVal (EVar 39%nat); RVal (EVar 42%nat)]
        [(2, EVar 32%nat); (11, EVar 35%nat); (23, EVar 36%nat); (27, EVar 46%nat)]
        [(32%nat, 2 ^ 63); (35%nat, 5); (36%nat, 2 ^ 31); (39%nat, 2 ^ 31); (42%nat, 2 ^ 31); (45%nat, 2 ^ 31); (46%nat, 2 ^ 64)] NoRegions
        [cv_sp v - 256; 0; 0; cv_flush v; ir_have r; 0; 0; ir_left r; 0; 0; ir_out r; 0; 0; NI; ir_ret r mod 2 ^ 64] NoVals F0 F0'
        (mkst R (Z_to_bv 64 0x21684) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTRETb" G end.
      exists R1. split; [by_run Hms1|].
      split; [symex_reg HR1 (10%bv : reg) as Q; rewrite Q; unfold retv, Z_FINISH, Z_OK, Z_BUF_ERROR; rewrite ER; first [reflexivity | apply zw_mod]|].
      split; [rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2 | fr_weak Hfr1].
  Qed.

  Lemma lv_R0 : forall R M,
    iframe6 v M ->
    getr R 2 = zw (cv_sp v - 256) -> getr R 10 = zw 0 ->
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_uw_ret) M s6u_rom) (mkst R1 (Z_to_bv 64 0x21684) M s6u_rom)
      /\ getr R1 11 = zw (cv_flush v) /\ getr R1 12 = zw 16209
      /\ (forall rg : reg, reg_in rg [11; 12]%bv = false -> getr R1 rg = getr R rg).
  Proof.
    intros R M HF G2 G10.
    open_ictx C. pose proof HF as Mfr. open_frame Mfr.
    symex s6u_segs ilL 8%nat [true] [RVal (ELit 16209); RVal (EVar 35%nat)]
      [(2, EVar 32%nat); (10, ELit 0)]
      [(32%nat, 2 ^ 63); (35%nat, 5)] NoRegions
      [cv_sp v - 256; 0; 0; cv_flush v] NoVals F0 F0'
      (mkst R (Z_to_bv 64 pc6_uw_ret) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- exists _, _ => idtac | |- ?G => idtac "LEFTR0" G end.
    exists R1. split; [by_run Hms1|].
    split; [symex_reg HR1 (11%bv : reg) as Q11; exact Q11|]. split; [symex_reg HR1 (12%bv : reg) as Q12; exact Q12|].
    fr_weak Hfr1.
  Qed.

End Leave.
End FXG.
