(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_c_pure Z_infl_c_tab Zg_infl_iface Zg_inffast_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition PC_FF_W3L : Z := 0x22cd4.   (* [comment removed for export] *)
Definition PC_FF_LPC : Z := 0x22c14.   (* [comment removed for export] *)
Definition PC_FF_LPD : Z := 0x22c80.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ffrom (X : ictx) (fr : fromptr) : Z := faddr (il_Aw (ix_L X)) (il_NO (ix_L X)) fr.
(* [comment removed for export] *)
Definition srcn (s : inflate_state) (out : Z) (fr : fromptr) (n : Z) : Prop :=
  match fr with FWin i => is_window_blk s <> None /\ 0 <= i /\ i + n <= 32768 | FOut j => 0 <= j /\ j < out end.

Lemma srcn_succ : forall s out fr n, srcn s out fr n -> 1 <= n -> srcn s (out + 1) (from_succ fr) (n - 1).
Proof. intros s out [i|j] n H Hn; cbn in *; [destruct H as (A & B & C); split; [exact A| lia] | lia]. Qed.

Lemma ffrom_succ : forall X fr, ffrom X (from_succ fr) = ffrom X fr + 1.
Proof. intros X [i|j]; cbn; unfold ffrom; cbn; lia. Qed.
Lemma ffrom_add : forall X fr k, ffrom X (fr_add fr k) = ffrom X fr + Z.of_nat k.
Proof. intros X fr k. unfold ffrom. apply faddr_add. Qed.

Lemma icset_outbuf_twice : forall c a b, icset_outbuf (icset_outbuf c a) b = icset_outbuf c b.
Proof. intros. reflexivity. Qed.
Lemma ic_outbuf_set : forall c a, ic_outbuf (icset_outbuf c a) = a.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CP.
Variables (X : ictx) (s : inflate_state) (c : icall).
Local Notation L := (ix_L X).

Definition CPM (ob : arr) (out : Z) (m : mem) : Prop :=
  u8arr usegs m (il_NO L) (iout_bytes (ix_rest0 X) (icset_outbuf c ob) out) /\ mem_inv usegs m.

(* [comment removed for export] *)
Definition CPS : Prop :=
  ix_ok X /\ (is_window_blk s <> None -> ix_hasw X = true) /\ (is_window_blk s <> None -> arr_len (is_window s) = 32768)
  /\ (forall i, 0 <= i < arr_len (is_window s) -> 0 <= arr_get (is_window s) i < 256)
  /\ Z.of_nat (length (ix_rest0 X)) < 2^31.

(* [comment removed for export] *)
Lemma ff_src_read : forall ob out fr n me m a,
  CPS -> u8arr usegs m (il_NO L) (iout_bytes (ix_rest0 X) (icset_outbuf c ob) out) -> iwin me L s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out <= Z.of_nat (length (ix_rest0 X)) ->
  (forall i, 0 <= i < out -> 0 <= arr_get ob i < 256) ->
  srcn s out fr n -> 1 <= n -> a = wa (ffrom X fr) ->
  ov_read_bytes usegs m a 1 = Some [Z_to_bv 8 (fval (is_window s) ob fr)] /\ 0 <= fval (is_window s) ob fr < 256.
Proof.
  intros ob out fr n me m a (XO & Whas & Wlen & Bwin & R31) OUT Gwin MUf WMf Hout OBT SR Hn ->.
  destruct fr as [i|j]; cbn [fval]; cbn in SR.
  - destruct SR as (NWB & Hi & Hin). pose proof (Whas NWB) as HASW. ix_open XO. pose proof (xo_win _ XO HASW) as XW.
    apply (iwin_munch me m L s (ffW X)) in Gwin; [| exact MUf | exact WMf | intros _; unfold ffW; cbn [disjoint_from]; isep ].
    unfold iwin in Gwin. destruct (is_window_blk s) eqn:EWB; [|exfalso; apply NWB; reflexivity].
    pose proof (Wlen NWB) as WL.
    assert (RB : 0 <= arr_get (is_window s) i < 256) by (apply Bwin; lia). split; [|exact RB].
    apply (u8arr_read usegs m (il_Aw L) (av8 (is_window s) 32768) i); [exact Gwin| apply av8_nth; lia| lia| unfold ffrom; cbn; reflexivity].
  - assert (RB : 0 <= arr_get ob j < 256) by (apply OBT; lia). split; [|exact RB].
    apply (u8arr_read usegs m (il_NO L) (iout_bytes (ix_rest0 X) (icset_outbuf c ob) out) j); [exact OUT| | lia| unfold ffrom; cbn; reflexivity].
    rewrite (iout_bytes_nth (ix_rest0 X) (icset_outbuf c ob) out j) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ff_out_store_ok : forall ob out m a,
  u8arr usegs m (il_NO L) (iout_bytes (ix_rest0 X) (icset_outbuf c ob) out) -> 0 <= out < Z.of_nat (length (ix_rest0 X)) ->
  a = wa (il_NO L + out) -> store_ok usegs m a 1 = true.
Proof.
  intros ob out m a OUT Hout ->.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) out ltac:(lia)) as LOB.
  apply (u8arr_store_ok usegs m (il_NO L) (iout_bytes (ix_rest0 X) (icset_outbuf c ob) out) out); [exact OUT| rewrite LOB; lia| reflexivity].
Qed.
(* [comment removed for export] *)
Definition OBT (ob : arr) (out : Z) : Prop := forall i, 0 <= i < out -> 0 <= arr_get ob i < 256.
Lemma obt_step : forall ob out v, OBT ob out -> 0 <= out < arr_len ob -> 0 <= v < 256 -> OBT (arr_set ob out v) (out + 1).
Proof.
  intros ob out v H Ho Hv i Hi. destruct (Z.eq_dec i out) as [->|NE].
  - rewrite arr_get_set_same by lia. exact Hv.
  - rewrite arr_get_set_other by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma ffrom_range : forall out fr n, CPS -> srcn s out fr n -> 0 <= n -> out + n <= Z.of_nat (length (ix_rest0 X)) ->
  0 < ffrom X fr /\ ffrom X fr + n <= ix_lo X.
Proof.
  intros out fr n (XO & Whas & Wlen & Bwin & R31) SR Hn Hon. ix_open XO. destruct fr as [i|j]; cbn in SR; unfold ffrom; cbn [faddr].
  - destruct SR as (NWB & Hi & Hin). pose proof (xo_win _ XO (Whas NWB)). lia.
  - lia.
Qed.
End CP.

(* [comment removed for export] *)
Ltac out_write OUT LOB ob out v :=
  let OUT2 := fresh "OUT" in
  lazymatch type of OUT with
  | u8arr _ ?m (il_NO (ix_L ?X)) (iout_bytes _ (icset_outbuf ?c _) _) =>
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a ?bs) _) =>
        replace (write_to_mem m a bs) with (write_to_mem m (wa (il_NO (ix_L X) + out)) bs) by (f_equal; unfold wa; word_eq_tac) end;
      pose proof (u8arr_write usegs m (il_NO (ix_L X)) _ out (Z_to_bv 8 v) OUT ltac:(rewrite LOB; lia)) as OUT2; clear OUT;
      store_done;
      rewrite iout_bytes_store in OUT2 by (rewrite ?ic_outbuf_set, ?arr_len_set; lia);
      rewrite icset_outbuf_twice, ic_outbuf_set in OUT2;
      clear LOB;
      pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (arr_set ob out v)) (out + 1) ltac:(lia)) as LOB;
      apply (f_equal Z.of_nat) in LOB;
      rename OUT2 into OUT
  end.

(* [comment removed for export] *)
Ltac cp_load HS OUT Gwin MUf WMf OBT SR fr ob out n ae RV :=
  let RD := fresh "RD" in
  lazymatch goal with X : ictx, s : inflate_state, c : icall |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    destruct (ff_src_read X s c ob out fr n _ m (wa ae) HS OUT Gwin MUf WMf ltac:(lia) OBT SR ltac:(lia)
                ltac:(unfold wa; first [ f_equal; lia | f_equal; rewrite ?ffrom_succ, ?ffrom_add; cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add]; lia
                                        | unfold ffrom; cbn [faddr from_succ]; word_eq_tac ])) as [RD RV];
    zs; cbv beta; rewrite (bv8_small _ RV); clear RD
  end.
(* [comment removed for export] *)
Ltac cp_store OUT LOB ob out v RV :=
  let SOK := fresh "SOK" in
  lazymatch goal with X : ictx, c : icall |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    pose proof (ff_out_store_ok X c ob out m (wa (il_NO (ix_L X) + out)) OUT ltac:(lia) eq_refl) as SOK;
    zs; rewrite le1_wz_byte by exact RV;
    out_write OUT LOB ob out v; try clear SOK
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W3.
Variables (X : ictx) (s : inflate_state) (c : icall) (r : iregs).

Definition w3_post (hold bits fin : Z) (obF : arr) (outF : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 x5 x6 x7 x9 x13 x23 x27 x29 m',
    ms' = FFL X s c r (mkF fin outF hold bits 0 0 0 (FOut 0) obF) PC_FF_COND x1 x5 x6 x7 x9 x13 x23 x27 x29 m'
    /\ munch (ffW X) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ CPM X c obF outF m' /\ OBT obF outF.

Local Ltac w3_fin OUT OBT MUf WMf :=
  apply evt_done; unfold w3_post; do 10 eexists;
  split; [eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg|];
  split; [exact MUf|]; split; [exact WMf|]; split; [assumption|]; split; [split; [exact OUT| assumption]| exact OBT].

(* [comment removed for export] *)
Lemma ff_w3t : forall fr ob out0 out len hold bits fin obF outF (x5 x6 x7 x9 x13 x23 : word) me m,
  CPS X s -> CPM X c ob out m -> iwin me (ix_L X) s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out0 <= out -> out + len <= Z.of_nat (length (ix_rest0 X)) -> (len = 0 \/ len = 1 \/ len = 2) -> arr_len ob = Z.of_nat (length (ix_rest0 X)) ->
  OBT ob out -> (1 <= len -> srcn s out fr len) ->
  0 <= hold < 2^64 -> 0 <= bits < 2^32 -> 0 <= fin <= arr_len (ix_input X) ->
  obF = cblit (is_window s) fr ob out (Z.to_nat len) -> outF = out + len ->
  evt usegs (w3_post hold bits fin obF outF me)
    (FFL X s c r (mkF fin out0 hold bits 0 0 0 (FOut 0) ob) PC_FF_TAIL (wz (il_NO (ix_L X) + out)) x5 x6 x7 x9 x13 x23 (wz len) (wz (ffrom X fr)) m).
Proof.
  intros fr ob out0 out len hold bits fin obF outF x5 x6 x7 x9 x13 x23 me m HS [OUT MI] Gwin MUf WMf Ho Hol Hlen Lob OBT SRn Rh Rb Rfin EobF EoutF.
  pose proof HS as (XO & Whas & Wlen & Bwin & R31). ix_open XO. unfold FFL, ff_sp, PC_FF_TAIL. cbn [f_hold f_in f_out f_bits].
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) out ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold ffW in MUf. subst obF outF.
  zstep. br_cases K0.
  { (* [comment removed for export] *)
    assert (E0 : len = 0) by lia. subst len. do 2 zs.
    cbn [Z.to_nat cblit]. replace (out + 0) with out by lia. w3_fin OUT OBT MUf WMf. }
  pose proof (SRn ltac:(lia)) as SR.
  pose proof (ffrom_range X s out fr len HS SR ltac:(lia) ltac:(lia)) as RFR.
  (* [comment removed for export] *)
  zstep. gF. zstep. gF.
  cp_load HS OUT Gwin MUf WMf OBT SR fr ob out len (ffrom X fr) RV.
  set (v0 := fval (is_window s) ob fr) in *.
  cp_store OUT LOB ob out v0 RV.
  pose proof (obt_step ob out v0 OBT ltac:(lia) RV) as OBT1.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    assert (E1 : len = 1) by lia. subst len. subst v0.
    cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add cblit]. w3_fin OUT OBT1 MUf WMf.
  - assert (E2 : len = 2) by lia. subst len.
    pose proof (srcn_succ s out fr 2 SR ltac:(lia)) as SR1.
    (* [comment removed for export] *)
    zstep. br_false. zstep. br_false.
    cp_load HS OUT Gwin MUf WMf OBT1 SR1 (from_succ fr) (arr_set ob out v0) (out + 1) 1 (ffrom X fr + 1) RV0.
    set (v1 := fval (is_window s) (arr_set ob out v0) (from_succ fr)) in *.
    zs.
    cp_store OUT LOB (arr_set ob out v0) (out + 1) v1 RV0.
    pose proof (obt_step _ _ v1 OBT1 ltac:(rewrite arr_len_set; lia) RV0) as OBT2.
    replace (out + 1 + 1) with (out + 2) in OUT, OBT2 by lia. subst v1 v0.
    zs. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add cblit]. w3_fin OUT OBT2 MUf WMf.
Qed.

Local Ltac ffreg2 :=
  first [ ffreg
        | f_equal; rewrite ?ffrom_add, ?ffrom_succ; unfold ffrom; cbn [faddr Z.of_nat Pos.to_nat Pos.iter_op Nat.add]; lia
        | try match goal with H : win_addr _ _ = il_Aw _ |- _ => rewrite H end; unfold ffrom; cbn [faddr]; ffreg ].

(* [comment removed for export] *)
Lemma ff_w3l : forall k fr ob out0 out len hold bits fin obF outF (x6 x7 x9 x23 : word) me m,
  CPS X s -> CPM X c ob out m -> iwin me (ix_L X) s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out0 <= out -> out + len <= Z.of_nat (length (ix_rest0 X)) -> 3 <= len -> len <= 3 * Z.of_nat k -> arr_len ob = Z.of_nat (length (ix_rest0 X)) ->
  OBT ob out -> srcn s out fr len ->
  0 <= hold < 2^64 -> 0 <= bits < 2^32 -> 0 <= fin <= arr_len (ix_input X) ->
  obF = cblit (is_window s) fr ob out (Z.to_nat len) -> outF = out + len ->
  evt usegs (w3_post hold bits fin obF outF me)
    (FFL X s c r (mkF fin out0 hold bits 0 0 0 (FOut 0) ob) PC_FF_W3L (wz (il_NO (ix_L X) + out)) (wz (ffrom X fr)) x6 x7 x9 (wz (il_NO (ix_L X) + out)) x23 (wz len) (wz (ffrom X fr)) m).
Proof.
  intros k. induction k as [|k IH]; intros fr ob out0 out len hold bits fin obF outF x6 x7 x9 x23 me m HS [OUT MI] Gwin MUf WMf Ho Hol H3 Hk Lob OBT SR Rh Rb Rfin EobF EoutF; [lia|].
  pose proof HS as (XO & Whas & Wlen & Bwin & R31). ix_open XO. unfold FFL, ff_sp, PC_FF_W3L. cbn [f_hold f_in f_out f_bits].
  pose proof (ffrom_range X s out fr len HS SR ltac:(lia) ltac:(lia)) as RFR.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) out ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold ffW in MUf.
  (* [comment removed for export] *)
  zstep. gF. zstep. gF. zstep. zstep.
  (* [comment removed for export] *)
  cp_load HS OUT Gwin MUf WMf OBT SR fr ob out len (ffrom X fr) RV.
  set (v0 := fval (is_window s) ob fr) in *.
  zstep.
  cp_store OUT LOB ob out v0 RV.
  pose proof (obt_step ob out v0 OBT ltac:(lia) RV) as OBT1.
  pose proof (srcn_succ s out fr len SR ltac:(lia)) as SR1.
  zstep. br_false. zstep. zstep. br_false.
  (* [comment removed for export] *)
  cp_load HS OUT Gwin MUf WMf OBT1 SR1 (from_succ fr) (arr_set ob out v0) (out + 1) (len - 1) (ffrom X fr + 1) RV0.
  set (v1 := fval (is_window s) (arr_set ob out v0) (from_succ fr)) in *.
  zstep.
  cp_store OUT LOB (arr_set ob out v0) (out + 1) v1 RV0.
  pose proof (obt_step _ _ v1 OBT1 ltac:(rewrite arr_len_set; lia) RV0) as OBT2.
  pose proof (srcn_succ s (out + 1) (from_succ fr) (len - 1) SR1 ltac:(lia)) as SR2.
  zstep. br_false. zstep. zstep. br_false.
  (* [comment removed for export] *)
  cp_load HS OUT Gwin MUf WMf OBT2 SR2 (from_succ (from_succ fr)) (arr_set (arr_set ob out v0) (out + 1) v1) (out + 1 + 1) (len - 1 - 1) (ffrom X fr + 2) RV1.
  set (v2 := fval (is_window s) (arr_set (arr_set ob out v0) (out + 1) v1) (from_succ (from_succ fr))) in *.
  zs. zstep. zstep. zstep.
  cp_store OUT LOB (arr_set (arr_set ob out v0) (out + 1) v1) (out + 1 + 1) v2 RV1.
  pose proof (obt_step _ _ v2 OBT2 ltac:(rewrite !arr_len_set; lia) RV1) as OBT3.
  pose proof (srcn_succ s (out + 1 + 1) (from_succ (from_succ fr)) (len - 1 - 1) SR2 ltac:(lia)) as SR3.
  replace (len - 1 - 1 - 1) with (len - 3) in SR3 by lia.
  set (ob3 := arr_set (arr_set (arr_set ob out v0) (out + 1) v1) (out + 1 + 1) v2) in *.
  assert (EobF3 : obF = cblit (is_window s) (from_succ (from_succ (from_succ fr))) ob3 (out + 1 + 1 + 1) (Z.to_nat (len - 3))).
  { subst obF ob3 v0 v1 v2. replace (Z.to_nat len) with (S (S (S (Z.to_nat (len - 3))))) by lia. reflexivity. }
  assert (Lob3 : arr_len ob3 = Z.of_nat (length (ix_rest0 X))) by (subst ob3; rewrite !arr_len_set; exact Lob).
  clearbody ob3. clear OBT OBT1 OBT2 SR SR1 SR2 EobF RV RV0.
  zstep. zstep. br_cases K.
  - (* [comment removed for export] *)
    eapply evt_eq; [| eapply (IH (from_succ (from_succ (from_succ fr))) ob3 out0 (out + 1 + 1 + 1) (len - 3));
      first [exact HS | split; [exact OUT| assumption] | exact Gwin | exact MUf | exact WMf | exact EobF3 | exact OBT3 | exact SR3 | lia] ].
    eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
  - (* [comment removed for export] *)
    zstep. zstep.
    eapply evt_eq; [| eapply (ff_w3t (from_succ (from_succ (from_succ fr))) ob3 out0 (out + 1 + 1 + 1) (len - 3));
      first [exact HS | split; [exact OUT| assumption] | exact Gwin | exact MUf | exact WMf | exact EobF3 | exact OBT3 | intros _; exact SR3 | lia] ].
    unfold PC_FF_TAIL. eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
Qed.

(* [comment removed for export] *)
Lemma ff_w3 : forall fr ob out len hold bits fin obF outF (x1 x5 x6 x7 x9 x13 x23 : word) me m,
  CPS X s -> CPM X c ob out m -> iwin me (ix_L X) s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out -> out + len <= Z.of_nat (length (ix_rest0 X)) -> 0 <= len -> arr_len ob = Z.of_nat (length (ix_rest0 X)) ->
  OBT ob out -> (1 <= len -> srcn s out fr len) ->
  0 <= hold < 2^64 -> 0 <= bits < 2^32 -> 0 <= fin <= arr_len (ix_input X) ->
  obF = cblit (is_window s) fr ob out (Z.to_nat len) -> outF = out + len ->
  evt usegs (w3_post hold bits fin obF outF me)
    (FFL X s c r (mkF fin out hold bits 0 0 0 (FOut 0) ob) PC_FF_W3E x1 x5 x6 x7 x9 x13 x23 (wz len) (wz (ffrom X fr)) m).
Proof.
  intros fr ob out len hold bits fin obF outF x1 x5 x6 x7 x9 x13 x23 me m HS HM Gwin MUf WMf Ho Hol Hlen Lob OBT SRn Rh Rb Rfin EobF EoutF.
  pose proof HS as (XO & Whas & Wlen & Bwin & R31). pose proof HM as [OUT MI]. ix_open XO. unfold FFL, ff_sp, PC_FF_W3E. cbn [f_hold f_in f_out f_bits].
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) out ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  zstep. zstep. zstep. br_cases K.
  - (* [comment removed for export] *)
    eapply evt_eq; [| eapply (ff_w3t fr ob out out len); first [exact HS | exact HM | exact Gwin | exact MUf | exact WMf | exact EobF | exact OBT | exact SRn | lia] ].
    unfold PC_FF_TAIL. eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
  - zstep. zstep.
    eapply evt_eq; [| eapply (ff_w3l (Z.to_nat len) fr ob out out len); first [exact HS | exact HM | exact Gwin | exact MUf | exact WMf | exact EobF | exact OBT | exact (SRn ltac:(lia)) | lia] ].
    unfold PC_FF_W3L. eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition opc_post (pc' : Z) (hold bits fin : Z) (frF : fromptr) (obF : arr) (outF : Z) (x9 x23 x27 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x7 m',
    ms' = FFL X s c r (mkF fin outF hold bits 0 0 0 (FOut 0) obF) pc' (wz (il_NO (ix_L X) + outF)) (wz 0) (wz (ffrom X frF)) x7 x9 (wz (il_NO (ix_L X) + outF)) x23 x27 (wz (ffrom X frF)) m'
    /\ munch (ffW X) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ CPM X c obF outF m' /\ OBT obF outF.

Lemma ff_opcd : forall pce pcx k fr ob out cnt hold bits fin frF obF outF (x1 x7 x9 x23 x27 : word) me m,
  (pce = PC_FF_LPC /\ pcx = 0x22c40 \/ pce = PC_FF_LPD /\ pcx = 0x22cac) ->
  CPS X s -> CPM X c ob out m -> iwin me (ix_L X) s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out -> out + cnt <= Z.of_nat (length (ix_rest0 X)) -> 1 <= cnt -> cnt <= Z.of_nat k -> arr_len ob = Z.of_nat (length (ix_rest0 X)) ->
  OBT ob out -> srcn s out fr cnt ->
  0 <= hold < 2^64 -> 0 <= bits < 2^32 -> 0 <= fin <= arr_len (ix_input X) ->
  frF = fr_add fr (Z.to_nat cnt) -> obF = cblit (is_window s) fr ob out (Z.to_nat cnt) -> outF = out + cnt ->
  evt usegs (opc_post pcx hold bits fin frF obF outF x9 x23 x27 me)
    (FFL X s c r (mkF fin out hold bits 0 0 0 (FOut 0) ob) pce x1 (wz cnt) (wz (ffrom X fr)) x7 x9 (wz (il_NO (ix_L X) + out)) x23 x27 (wz (ffrom X fr)) m).
Proof.
  intros pce pcx k. induction k as [|k IH]; intros fr ob out cnt hold bits fin frF obF outF x1 x7 x9 x23 x27 me m HPC HS [OUT MI] Gwin MUf WMf Ho Hol Hc Hk Lob OBT SR Rh Rb Rfin EfrF EobF EoutF; [lia|].
  pose proof HS as (XO & Whas & Wlen & Bwin & R31). ix_open XO. unfold FFL, ff_sp. cbn [f_hold f_in f_out f_bits].
  pose proof (ffrom_range X s out fr cnt HS SR ltac:(lia) ltac:(lia)) as RFR.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) out ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold ffW in MUf.
  assert (Lob1 : arr_len (arr_set ob out (fval (is_window s) ob fr)) = Z.of_nat (length (ix_rest0 X))) by (rewrite arr_len_set; exact Lob).
  assert (EobF1 : obF = cblit (is_window s) (from_succ fr) (arr_set ob out (fval (is_window s) ob fr)) (out + 1) (Z.to_nat (cnt - 1)))
    by (subst obF; replace (Z.to_nat cnt) with (S (Z.to_nat (cnt - 1))) by lia; reflexivity).
  assert (EfrF1 : frF = fr_add (from_succ fr) (Z.to_nat (cnt - 1)))
    by (subst frF; replace (Z.to_nat cnt) with (S (Z.to_nat (cnt - 1))) by lia; reflexivity).
  destruct HPC as [[-> ->]|[-> ->]]; unfold PC_FF_LPC, PC_FF_LPD.
  all: zstep; gF; zstep; gF.
  all: cp_load HS OUT Gwin MUf WMf OBT SR fr ob out cnt (ffrom X fr) RV.
  all: set (v0 := fval (is_window s) ob fr) in *.
  all: zstep; zstep; zs.
  all: cp_store OUT LOB ob out v0 RV.
  all: pose proof (obt_step ob out v0 OBT ltac:(lia) RV) as OBT1.
  all: pose proof (srcn_succ s out fr cnt SR ltac:(lia)) as SR1.
  all: zstep; zstep; br_cases K.
  1,3: eapply evt_eq; [| eapply (IH (from_succ fr) (arr_set ob out v0) (out + 1) (cnt - 1));
         first [exact HS | split; [exact OUT| assumption] | exact Gwin | exact MUf | exact WMf | exact EfrF1 | exact EobF1 | exact OBT1 | exact SR1 | exact Lob1 | tauto | lia] ];
       eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
  all: assert (E1 : cnt = 1) by lia.
  all: apply evt_done; unfold opc_post; do 2 eexists;
       split; [eapply FFL_intro2; cbn [f_hold f_in f_out f_bits];
               first [ffreg2 | rewrite EfrF1, E1; change (Z.to_nat (1 - 1)) with 0%nat; cbn [fr_add]; ffreg2 ] |];
       split; [exact MUf|]; split; [exact WMf|]; split; [assumption|];
       rewrite EobF1, EoutF, E1; change (Z.to_nat (1 - 1)) with 0%nat; cbn [cblit];
       split; [split; [exact OUT| assumption]| exact OBT1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition opa_post (hold bits fin : Z) (frF : fromptr) (obF : arr) (outF : Z) (x23 x27 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = FFL X s c r (mkF fin outF hold bits 0 0 0 (FOut 0) obF) 0x22ad4 (wz 0) (wz (il_NO (ix_L X) + outF + 1)) (wz (ffrom X frF)) (wz (il_NO (ix_L X) + outF))
            (wz (il_NO (ix_L X) + outF)) (wz (il_NO (ix_L X) + outF)) x23 x27 (wz (ffrom X frF)) m'
    /\ munch (ffW X) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ CPM X c obF outF m' /\ OBT obF outF.

Lemma ff_opa : forall k fr ob out cnt hold bits fin frF obF outF (x9 x13 x23 x27 : word) me m,
  CPS X s -> CPM X c ob out m -> iwin me (ix_L X) s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out -> out + cnt <= Z.of_nat (length (ix_rest0 X)) -> 1 <= cnt -> cnt <= Z.of_nat k -> arr_len ob = Z.of_nat (length (ix_rest0 X)) ->
  OBT ob out -> srcn s out fr cnt ->
  0 <= hold < 2^64 -> 0 <= bits < 2^32 -> 0 <= fin <= arr_len (ix_input X) ->
  frF = fr_add fr (Z.to_nat cnt) -> obF = cblit (is_window s) fr ob out (Z.to_nat cnt) -> outF = out + cnt ->
  evt usegs (opa_post hold bits fin frF obF outF x23 x27 me)
    (FFL X s c r (mkF fin out hold bits 0 0 0 (FOut 0) ob) 0x22aa0 (wz cnt) (wz (il_NO (ix_L X) + out + 1)) (wz (ffrom X fr)) (wz (il_NO (ix_L X) + out))
         x9 x13 x23 x27 (wz (ffrom X fr)) m).
Proof.
  intros k. induction k as [|k IH]; intros fr ob out cnt hold bits fin frF obF outF x9 x13 x23 x27 me m HS [OUT MI] Gwin MUf WMf Ho Hol Hc Hk Lob OBT SR Rh Rb Rfin EfrF EobF EoutF; [lia|].
  pose proof HS as (XO & Whas & Wlen & Bwin & R31). ix_open XO. unfold FFL, ff_sp. cbn [f_hold f_in f_out f_bits].
  pose proof (ffrom_range X s out fr cnt HS SR ltac:(lia) ltac:(lia)) as RFR.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) out ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold ffW in MUf.
  assert (Lob1 : arr_len (arr_set ob out (fval (is_window s) ob fr)) = Z.of_nat (length (ix_rest0 X))) by (rewrite arr_len_set; exact Lob).
  assert (EobF1 : obF = cblit (is_window s) (from_succ fr) (arr_set ob out (fval (is_window s) ob fr)) (out + 1) (Z.to_nat (cnt - 1)))
    by (subst obF; replace (Z.to_nat cnt) with (S (Z.to_nat (cnt - 1))) by lia; reflexivity).
  assert (EfrF1 : frF = fr_add (from_succ fr) (Z.to_nat (cnt - 1)))
    by (subst frF; replace (Z.to_nat cnt) with (S (Z.to_nat (cnt - 1))) by lia; reflexivity).
  zstep. gF. zstep. gF. zstep.
  cp_load HS OUT Gwin MUf WMf OBT SR fr ob out cnt (ffrom X fr) RV.
  set (v0 := fval (is_window s) ob fr) in *.
  zstep. zstep. zs.
  cp_store OUT LOB ob out v0 RV.
  pose proof (obt_step ob out v0 OBT ltac:(lia) RV) as OBT1.
  pose proof (srcn_succ s out fr cnt SR ltac:(lia)) as SR1.
  zstep. zstep. zstep. br_cases K.
  - eapply evt_eq; [| eapply (IH (from_succ fr) (arr_set ob out v0) (out + 1) (cnt - 1));
      first [exact HS | split; [exact OUT| assumption] | exact Gwin | exact MUf | exact WMf | exact EfrF1 | exact EobF1 | exact OBT1 | exact SR1 | exact Lob1 | lia] ].
    eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
  - assert (E1 : cnt = 1) by lia.
    apply evt_done; unfold opa_post; eexists;
    split; [eapply FFL_intro2; cbn [f_hold f_in f_out f_bits];
            first [ffreg2 | rewrite EfrF1, E1; change (Z.to_nat (1 - 1)) with 0%nat; cbn [fr_add]; ffreg2 ] |].
    split; [exact MUf|]. split; [exact WMf|]. split; [assumption|].
    rewrite EobF1, EoutF, E1; change (Z.to_nat (1 - 1)) with 0%nat; cbn [cblit].
    split; [split; [exact OUT| assumption]| exact OBT1].
Qed.

(* [comment removed for export] *)
Definition opb_post (out0 hold bits fin : Z) (frF : fromptr) (obF : arr) (outF : Z) (x23 x27 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x6 m',
    ms' = FFL X s c r (mkF fin out0 hold bits 0 0 0 (FOut 0) obF) 0x22b14 (wz (il_NO (ix_L X) + outF)) (wz (ffrom X frF)) x6 (wz (ffrom X frF)) (wz (il_NO (ix_L X) + outF))
            (wz (il_NO (ix_L X) + outF)) x23 x27 (wz 0) m'
    /\ munch (ffW X) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ CPM X c obF outF m' /\ OBT obF outF.

Lemma ff_opb : forall k fr ob out0 out cnt hold bits fin frF obF outF (x1 x6 x23 x27 : word) me m,
  CPS X s -> CPM X c ob out m -> iwin me (ix_L X) s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out0 <= out -> out + cnt <= Z.of_nat (length (ix_rest0 X)) -> 1 <= cnt -> cnt <= Z.of_nat k -> arr_len ob = Z.of_nat (length (ix_rest0 X)) ->
  OBT ob out -> srcn s out fr cnt ->
  0 <= hold < 2^64 -> 0 <= bits < 2^32 -> 0 <= fin <= arr_len (ix_input X) ->
  frF = fr_add fr (Z.to_nat cnt) -> obF = cblit (is_window s) fr ob out (Z.to_nat cnt) -> outF = out + cnt ->
  evt usegs (opb_post out0 hold bits fin frF obF outF x23 x27 me)
    (FFL X s c r (mkF fin out0 hold bits 0 0 0 (FOut 0) ob) 0x22ae8 x1 (wz (ffrom X fr)) x6 (wz (ffrom X fr)) (wz (il_NO (ix_L X) + out))
         (wz (il_NO (ix_L X) + out)) x23 x27 (wz cnt) m).
Proof.
  intros k. induction k as [|k IH]; intros fr ob out0 out cnt hold bits fin frF obF outF x1 x6 x23 x27 me m HS [OUT MI] Gwin MUf WMf Ho Hol Hc Hk Lob OBT SR Rh Rb Rfin EfrF EobF EoutF; [lia|].
  pose proof HS as (XO & Whas & Wlen & Bwin & R31). ix_open XO. unfold FFL, ff_sp. cbn [f_hold f_in f_out f_bits].
  pose proof (ffrom_range X s out fr cnt HS SR ltac:(lia) ltac:(lia)) as RFR.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) out ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold ffW in MUf.
  assert (Lob1 : arr_len (arr_set ob out (fval (is_window s) ob fr)) = Z.of_nat (length (ix_rest0 X))) by (rewrite arr_len_set; exact Lob).
  assert (EobF1 : obF = cblit (is_window s) (from_succ fr) (arr_set ob out (fval (is_window s) ob fr)) (out + 1) (Z.to_nat (cnt - 1)))
    by (subst obF; replace (Z.to_nat cnt) with (S (Z.to_nat (cnt - 1))) by lia; reflexivity).
  assert (EfrF1 : frF = fr_add (from_succ fr) (Z.to_nat (cnt - 1)))
    by (subst frF; replace (Z.to_nat cnt) with (S (Z.to_nat (cnt - 1))) by lia; reflexivity).
  zstep. gF. zstep. br_false.
  cp_load HS OUT Gwin MUf WMf OBT SR fr ob out cnt (ffrom X fr) RV.
  set (v0 := fval (is_window s) ob fr) in *.
  zstep. zstep. zs.
  cp_store OUT LOB ob out v0 RV.
  pose proof (obt_step ob out v0 OBT ltac:(lia) RV) as OBT1.
  pose proof (srcn_succ s out fr cnt SR ltac:(lia)) as SR1.
  zstep. zstep. zstep. br_cases K.
  - eapply evt_eq; [| eapply (IH (from_succ fr) (arr_set ob out v0) out0 (out + 1) (cnt - 1));
      first [exact HS | split; [exact OUT| assumption] | exact Gwin | exact MUf | exact WMf | exact EfrF1 | exact EobF1 | exact OBT1 | exact SR1 | exact Lob1 | lia] ].
    eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
  - assert (E1 : cnt = 1) by lia.
    apply evt_done; unfold opb_post; do 2 eexists;
    split; [eapply FFL_intro2; cbn [f_hold f_in f_out f_bits];
            first [ffreg2 | rewrite EfrF1, E1; change (Z.to_nat (1 - 1)) with 0%nat; cbn [fr_add]; ffreg2 ] |].
    split; [exact MUf|]. split; [exact WMf|]. split; [assumption|].
    rewrite EobF1, EoutF, E1; change (Z.to_nat (1 - 1)) with 0%nat; cbn [cblit].
    split; [split; [exact OUT| assumption]| exact OBT1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ff_do3t : forall ob out0 j len dist hold bits fin obF outF (x1 x6 x7 x9 x13 x23 : word) me m,
  CPS X s -> CPM X c ob (out0 + j) m -> iwin me (ix_L X) s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out0 -> 0 <= j -> out0 + j + len <= Z.of_nat (length (ix_rest0 X)) -> 0 <= len <= 2 -> arr_len ob = Z.of_nat (length (ix_rest0 X)) ->
  OBT ob (out0 + j) -> 1 <= dist <= out0 -> dist < 2^32 ->
  0 <= hold < 2^64 -> 0 <= bits < 2^32 -> 0 <= fin <= arr_len (ix_input X) ->
  obF = cblit (is_window s) (FOut (out0 + j - dist)) ob (out0 + j) (Z.to_nat len) -> outF = out0 + j + len ->
  evt usegs (w3_post hold bits fin obF outF me)
    (FFL X s c r (mkF fin out0 hold bits 0 0 0 (FOut 0) ob) 0x22b90 x1 (wz j) x6 x7 x9 x13 x23 (wz len) (wz (il_NO (ix_L X) + out0 - dist)) m).
Proof.
  intros ob out0 j len dist hold bits fin obF outF x1 x6 x7 x9 x13 x23 me m HS [OUT MI] Gwin MUf WMf Ho Hj Hol Hlen Lob OBT Hd Hd32 Rh Rb Rfin EobF EoutF.
  pose proof HS as (XO & Whas & Wlen & Bwin & R31). ix_open XO. unfold FFL, ff_sp. cbn [f_hold f_in f_out f_bits].
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) (out0 + j) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold ffW in MUf.
  assert (SR : srcn s (out0 + j) (FOut (out0 + j - dist)) len) by (cbn; lia).
  zstep. zstep. br_cases K0.
  - (* [comment removed for export] *)
    assert (E0 : len = 0) by lia.
    apply evt_done; unfold w3_post; do 10 eexists.
    split; [eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2|].
    split; [exact MUf|]. split; [exact WMf|]. split; [assumption|].
    rewrite EobF, EoutF, E0. change (Z.to_nat 0) with 0%nat. cbn [cblit]. rewrite Z.add_0_r.
    split; [split; [exact OUT| assumption]| exact OBT].
  - zstep. zstep. br_false. zstep. br_false.
    cp_load HS OUT Gwin MUf WMf OBT SR (FOut (out0 + j - dist)) ob (out0 + j) len (il_NO (ix_L X) + out0 - dist + j) RV.
    set (v0 := fval (is_window s) ob (FOut (out0 + j - dist))) in *.
    zstep.
    cp_store OUT LOB ob (out0 + j) v0 RV.
    pose proof (obt_step ob (out0 + j) v0 OBT ltac:(lia) RV) as OBT1.
    zstep. br_cases K1.
    + (* [comment removed for export] *)
      assert (E1 : len = 1) by lia.
      zstep. apply evt_done; unfold w3_post; do 10 eexists.
      split; [eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2|].
      split; [exact MUf|]. split; [exact WMf|]. split; [assumption|].
      rewrite EobF, EoutF, E1. change (Z.to_nat 1) with 1%nat. cbn [cblit]. subst v0.
      split; [split; [exact OUT| assumption]| exact OBT1].
    + assert (E2 : len = 2) by lia.
      pose proof (srcn_succ s (out0 + j) (FOut (out0 + j - dist)) len SR ltac:(lia)) as SR1. cbn [from_succ] in SR1.
      zstep. zstep. br_false. zstep. br_false.
      cp_load HS OUT Gwin MUf WMf OBT1 SR1 (FOut (out0 + j - dist + 1)) (arr_set ob (out0 + j) v0) (out0 + j + 1) 1
              (il_NO (ix_L X) + out0 - dist + j + 1) RV0.
      set (v1 := fval (is_window s) (arr_set ob (out0 + j) v0) (FOut (out0 + j - dist + 1))) in *.
      zstep.
      cp_store OUT LOB (arr_set ob (out0 + j) v0) (out0 + j + 1) v1 RV0.
      pose proof (obt_step _ _ v1 OBT1 ltac:(rewrite arr_len_set; lia) RV0) as OBT2.
      zstep. zstep. apply evt_done; unfold w3_post; do 10 eexists.
      split; [eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2|].
      split; [exact MUf|]. split; [exact WMf|]. split; [assumption|].
      rewrite EobF, EoutF, E2. change (Z.to_nat 2) with 2%nat. cbn [cblit from_succ]. subst v0 v1.
      replace (out0 + j + 2) with (out0 + j + 1 + 1) by lia.
      split; [split; [exact OUT| assumption]| exact OBT2].
Qed.

(* [comment removed for export] *)
Lemma ff_do3l : forall k ob out0 j len dist hold bits fin obF outF (x1 x6 x7 x9 x13 x23 : word) me m,
  CPS X s -> CPM X c ob (out0 + j) m -> iwin me (ix_L X) s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out0 -> 0 <= j -> out0 + j + len <= Z.of_nat (length (ix_rest0 X)) -> 3 <= len -> len <= 3 * Z.of_nat k -> arr_len ob = Z.of_nat (length (ix_rest0 X)) ->
  OBT ob (out0 + j) -> 1 <= dist <= out0 -> dist < 2^32 ->
  0 <= hold < 2^64 -> 0 <= bits < 2^32 -> 0 <= fin <= arr_len (ix_input X) ->
  obF = cblit (is_window s) (FOut (out0 + j - dist)) ob (out0 + j) (Z.to_nat len) -> outF = out0 + j + len ->
  evt usegs (w3_post hold bits fin obF outF me)
    (FFL X s c r (mkF fin out0 hold bits 0 0 0 (FOut 0) ob) 0x22b3c x1 (wz j) x6 x7 x9 x13 x23 (wz len) (wz (il_NO (ix_L X) + out0 - dist)) m).
Proof.
  intros k; induction k as [|k IH]; [intros; lia|].
  intros ob out0 j len dist hold bits fin obF outF x1 x6 x7 x9 x13 x23 me m HS [OUT MI] Gwin MUf WMf Ho Hj Hol H3 Hk Lob OBT Hd Hd32 Rh Rb Rfin EobF EoutF.
  pose proof HS as (XO & Whas & Wlen & Bwin & R31). ix_open XO. unfold FFL, ff_sp. cbn [f_hold f_in f_out f_bits].
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) (out0 + j) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  unfold ffW in MUf.
  assert (SR : srcn s (out0 + j) (FOut (out0 + j - dist)) len) by (cbn; lia).
  (* [comment removed for export] *)
  zstep. zstep. gF. zstep. zstep. gF.
  (* [comment removed for export] *)
  cp_load HS OUT Gwin MUf WMf OBT SR (FOut (out0 + j - dist)) ob (out0 + j) len (il_NO (ix_L X) + out0 - dist + j) RV.
  set (v0 := fval (is_window s) ob (FOut (out0 + j - dist))) in *.
  cp_store OUT LOB ob (out0 + j) v0 RV.
  pose proof (obt_step ob (out0 + j) v0 OBT ltac:(lia) RV) as OBT1.
  pose proof (srcn_succ s (out0 + j) (FOut (out0 + j - dist)) len SR ltac:(lia)) as SR1. cbn [from_succ] in SR1.
  zstep. br_false. zstep. br_false.
  (* [comment removed for export] *)
  cp_load HS OUT Gwin MUf WMf OBT1 SR1 (FOut (out0 + j - dist + 1)) (arr_set ob (out0 + j) v0) (out0 + j + 1) (len - 1) (il_NO (ix_L X) + out0 - dist + j + 1) RV0.
  set (v1 := fval (is_window s) (arr_set ob (out0 + j) v0) (FOut (out0 + j - dist + 1))) in *.
  zstep.
  cp_store OUT LOB (arr_set ob (out0 + j) v0) (out0 + j + 1) v1 RV0.
  pose proof (obt_step _ _ v1 OBT1 ltac:(rewrite arr_len_set; lia) RV0) as OBT2.
  pose proof (srcn_succ s (out0 + j + 1) (FOut (out0 + j - dist + 1)) (len - 1) SR1 ltac:(lia)) as SR2. cbn [from_succ] in SR2.
  replace (out0 + j - dist + 1 + 1) with (out0 + j - dist + 2) in SR2 by lia.
  zstep. br_false. zstep. zstep. br_false.
  (* [comment removed for export] *)
  cp_load HS OUT Gwin MUf WMf OBT2 SR2 (FOut (out0 + j - dist + 2)) (arr_set (arr_set ob (out0 + j) v0) (out0 + j + 1) v1) (out0 + j + 1 + 1) (len - 1 - 1)
          (il_NO (ix_L X) + out0 - dist + j + 2) RV1.
  set (v2 := fval (is_window s) (arr_set (arr_set ob (out0 + j) v0) (out0 + j + 1) v1) (FOut (out0 + j - dist + 2))) in *.
  zs.
  cp_store OUT LOB (arr_set (arr_set ob (out0 + j) v0) (out0 + j + 1) v1) (out0 + j + 1 + 1) v2 RV1.
  pose proof (obt_step _ _ v2 OBT2 ltac:(rewrite !arr_len_set; lia) RV1) as OBT3.
  set (ob3 := arr_set (arr_set (arr_set ob (out0 + j) v0) (out0 + j + 1) v1) (out0 + j + 1 + 1) v2) in *.
  assert (EobF3 : obF = cblit (is_window s) (FOut (out0 + (j + 3) - dist)) ob3 (out0 + (j + 3)) (Z.to_nat (len - 3))).
  { subst obF ob3 v0 v1 v2. replace (Z.to_nat len) with (S (S (S (Z.to_nat (len - 3))))) by lia. cbn [cblit from_succ].
    replace (out0 + j - dist + 1 + 1 + 1) with (out0 + (j + 3) - dist) by lia. replace (out0 + j - dist + 1 + 1) with (out0 + j - dist + 2) by lia.
    replace (out0 + j + 1 + 1 + 1) with (out0 + (j + 3)) by lia. reflexivity. }
  assert (Lob3 : arr_len ob3 = Z.of_nat (length (ix_rest0 X))) by (subst ob3; rewrite !arr_len_set; exact Lob).
  replace (out0 + j + 1 + 1) with (out0 + (j + 3) - 1) in OUT by lia.
  assert (OUT3 : u8arr usegs _ (il_NO (ix_L X)) (iout_bytes (ix_rest0 X) (icset_outbuf c ob3) (out0 + (j + 3))))
    by (replace (out0 + (j + 3)) with (out0 + (j + 3) - 1 + 1) by lia; exact OUT).
  replace (out0 + j + 1 + 1 + 1) with (out0 + (j + 3)) in OBT3 by lia.
  clearbody ob3. clear OBT OBT1 OBT2 SR SR1 SR2 EobF RV RV0.
  zstep. zstep. br_cases K.
  - eapply evt_eq; [| eapply (IH ob3 out0 (j + 3) (len - 3) dist);
      first [exact HS | split; [exact OUT3| assumption] | exact Gwin | exact MUf | exact WMf | exact EobF3 | exact OBT3 | exact Lob3 | lia] ].
    eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
  - eapply evt_eq; [| eapply (ff_do3t ob3 out0 (j + 3) (len - 3) dist);
      first [exact HS | split; [exact OUT3| assumption] | exact Gwin | exact MUf | exact WMf | exact EobF3 | exact OBT3 | exact Lob3 | lia] ].
    eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
Qed.

(* [comment removed for export] *)
Lemma ff_do3 : forall ob out len dist hold bits fin obF outF (x1 x5 x6 x7 x9 x13 x29 : word) me m,
  CPS X s -> CPM X c ob out m -> iwin me (ix_L X) s -> munch (ffW X) me m -> wmono usegs me m ->
  0 <= out -> out + len <= Z.of_nat (length (ix_rest0 X)) -> 3 <= len -> arr_len ob = Z.of_nat (length (ix_rest0 X)) ->
  OBT ob out -> 1 <= dist <= out -> dist < 2^32 ->
  0 <= hold < 2^64 -> 0 <= bits < 2^32 -> 0 <= fin <= arr_len (ix_input X) ->
  obF = cblit (is_window s) (FOut (out - dist)) ob out (Z.to_nat len) -> outF = out + len ->
  evt usegs (w3_post hold bits fin obF outF me)
    (FFL X s c r (mkF fin out hold bits 0 0 0 (FOut 0) ob) PC_FF_OUT x1 x5 x6 x7 x9 x13 (wz dist) (wz len) x29 m).
Proof.
  intros ob out len dist hold bits fin obF outF x1 x5 x6 x7 x9 x13 x29 me m HS HM Gwin MUf WMf Ho Hol H3 Lob OBT Hd Hd32 Rh Rb Rfin EobF EoutF.
  pose proof HS as (XO & Whas & Wlen & Bwin & R31). pose proof HM as [OUT MI]. ix_open XO. unfold FFL, ff_sp, PC_FF_OUT. cbn [f_hold f_in f_out f_bits].
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c ob) out ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  gF. do 4 zs. gXsub. zstep. zstep.
  eapply evt_eq; [| eapply (ff_do3l (Z.to_nat len) ob out 0 len dist);
      first [exact HS | rewrite Z.add_0_r; exact HM | exact Gwin | exact MUf | exact WMf | rewrite Z.add_0_r; exact EobF | rewrite Z.add_0_r; exact OBT | exact Lob | lia] ].
  eapply FFL_intro2; cbn [f_hold f_in f_out f_bits]; ffreg2.
Qed.
End W3.
