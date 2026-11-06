(* Walk of reac-repacer's rp_lock_lookup in fuzz_lock.ubsan: the tests of one line, 0x13408-0x13440
   (repace_conf.c:131-136). Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Spec Require Import StrFun LockSpec.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import DigitsMach field_c digits_c
  strlen_c memchr_c bcmp_c rp_lock_lookup_c RpLib.
Import ListNotations.
Open Scope Z_scope.

Ltac uns := rewrite ?unsigned_lit by lia.
Ltac br v := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; unfold_cond; fold_lit_ux; uns; solve_cond_rec]
  end.

Section R.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (tx pa rate lo b std : Z) (T P SL : list byte).
Hypothesis Htx : 0 < tx.
Hypothesis HtxE : tx + Z.of_nat (length T) < 2^64.
Hypothesis Hpa : 0 < pa.
Hypothesis HPb : pa + Z.of_nat (length P + 1 + length SL) <= 2^64.
Hypothesis Hrate : rate = 44100 \/ rate = 48000 \/ rate = 96000.
Hypothesis HSTD : std_period rate = std.
Hypothesis Hstd : std = 272109 \/ std = 250000 \/ std = 125000.
Hypothesis Hb : b + 160 = bv_unsigned sp.
Hypothesis Hb8 : b mod 8 = 0.
Hypothesis Hlo : 0 <= lo <= b.
Hypothesis DT : tx + Z.of_nat (length T) <= b \/ b + 160 <= tx.
Hypothesis DP : pa + Z.of_nat (length P + 1 + length SL) <= b \/ b + 160 <= pa.

Local Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Local Notation Q := (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lock_lookup T P rate)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_FRAME, bv_unsigned sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp)).

(* the registers in the loop: s0 rate, s1 -1, s2 the line, s3 strlen(port), s4 found, s10 stop, s11 '#' *)
Local Notation LS pc mm xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 vs2 vs4 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 :=
  (MS (mkR xra (Z_to_bv 64 b) gp tp xt0 xt1 xt2 (Z_to_bv 64 rate) (Z_to_bv 64 (-1)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           vs2 (Z_to_bv 64 (Z.of_nat (length P))) vs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (tx + Z.of_nat (length T)))
           (Z_to_bv 64 35) xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Local Notation INV0 m := (RpLib.INV0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 tx pa lo b std T P SL m).
Local Notation INV m := (RpLib.INV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 tx pa lo b std T P SL m).

Ltac slot := first [ eapply c8_cb; eassumption | eapply cb_ex; eassumption ].
Ltac mk_inv0 := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); assumption.
Ltac mk_inv := refine (conj _ (conj _ (conj _ (conj _ _)))); [mk_inv0 | slot | slot | slot | slot].
Hypothesis BC : bcmp_contract.

Ltac dec2 := eapply (rp_dec2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 tx pa rate lo b std T P SL
                       Htx Hpa HPb Hrate HSTD Hstd Hlo DT DP).

(* 0x13408: has_nul, the name tests and memcmp of repace_conf.c:131-136 *)
Lemma rp_dec1 : forall (l : list byte) (o o1 n1 o2 n2 o3 n3 : nat) (fnd h v1 v2 v3 w1 w2 w3 : Z) (m : word -> option byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs7 xt3 xt4 xt5 xt6 c48 : word),
  fld l 0 = (o1, n1) -> fld l (o1 + n1) = (o2, n2) -> fld l (o2 + n2) = (o3, n3) ->
  (o1 + n1 <= length l)%nat -> (o2 + n2 <= length l)%nat -> (o3 + n3 <= length l)%nat ->
  0 <= h < 2^64 -> (h = 0 <-> is_some (find_byte 0 l) = false) ->
  v1 = tx + Z.of_nat o + Z.of_nat o1 -> v2 = tx + Z.of_nat o + Z.of_nat o2 -> v3 = tx + Z.of_nat o + Z.of_nat o3 ->
  w1 = Z.of_nat n1 -> w2 = Z.of_nat n2 -> w3 = Z.of_nat n3 ->
  bytes_at rsegs m (tx + Z.of_nat o) l -> INV0 m ->
  rw_cells rsegs m (b + 24) [C8 (Z_to_bv 64 v3)] -> rw_cells rsegs m (b + 32) [C8 (Z_to_bv 64 v2)] ->
  rw_cells rsegs m (b + 40) [C8 (Z_to_bv 64 v1)] -> rw_cells rsegs m (b + 48) [C8 c48] ->
  (forall (m' : word -> option byte) (v4 : Z)
          (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6 : word),
     v4 = upd P rate l fnd -> INV m' ->
     evt rsegs Q (LS 0x1343c m' yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 (Z_to_bv 64 v4)
                     ys5 ys6 ys7 ys8 ys9 yt3 yt4 yt5 yt6)) ->
  evt rsegs Q (LS 0x13408 m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 fnd)
                  (Z_to_bv 64 w2) (Z_to_bv 64 w3) xs7 (Z_to_bv 64 w1) (Z_to_bv 64 h) xt3 xt4 xt5 xt6).
Proof.
  intros l o o1 n1 o2 n2 o3 n3 fnd h v1 v2 v3 w1 w2 w3 m xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs7
    xt3 xt4 xt5 xt6 c48 FL1 FL2 FL3 B1 B2 B3 HH HHN -> -> -> -> -> -> BL I0 C18 C20 C28 C30 K.
  pose proof BC as BCu. unfold bcmp_contract in BCu.
  pose proof (line_val_eq P rate l o1 n1 o2 n2 o3 n3 FL1 FL2 FL3) as LVE. rewrite HSTD in LVE.
  destruct I0 as (BT & BP & FHL & FS & ST & MU & WM & MI).
  pose proof (bytes_at_bound _ _ _ _ BL) as BLb.
  pose proof (bytes_at_bound _ _ _ _ BP) as BPb. rewrite length_app in BPb; cbn [length] in BPb.
  pose proof (bnd_sp sp) as Rsp.
  (* 0x13408 bnez s9: has_nul *)
  step.
  destruct (is_some (find_byte 0 l)) eqn:NUL.
  { assert (h <> 0) by (intros E; apply HHN in E; congruence). br true.
    eapply K; [unfold upd; rewrite LVE; try rewrite NUL; reflexivity | mk_inv]. }
  assert (h = 0) by (apply HHN; reflexivity). subst h. br false.
  (* 0x1340c beqz s8: name_len = 0 *)
  step. destruct (Nat.eqb_spec n1 0) as [N1|N1].
  { br true. eapply K; [unfold upd; rewrite LVE; try rewrite NUL; subst n1; reflexivity | mk_inv]. }
  br false.
  (* 0x13410 ld a0,0x28(sp); 0x13414 beqz a0 (UBSan null check, trap at 0x1348c): name = s + o1 > 0 *)
  step. step. br false.
  destruct (DigitsMach.byte_at l o1 ltac:(lia)) as [c Nc].
  pose proof (DigitsMach.rdb m (tx + Z.of_nat o) l o1 c BL Nc) as RC.
  pose proof (byte_range c) as Rc.
  (* 0x13418 lbu a1,0(a0); 0x1341c beq a1,s11: name[0] = '#' *)
  step. unfold zxb. step.
  destruct (Z.eqb_spec (bv_unsigned c) 35) as [H35|H35].
  { br true. eapply K; [unfold upd; rewrite LVE; try rewrite NUL; try rewrite (proj2 (Nat.eqb_neq n1 0) N1);
                        rewrite (nth_of_error l o1 c _ Nc); unfold bz; rewrite H35; reflexivity | mk_inv]. }
  br false.
  (* 0x13420 li a1,15; 0x13424 bltu a1,s8: name_len > 15 *)
  step. step. destruct (Nat.ltb_spec 15 n1) as [G|G].
  { br true. eapply K; [unfold upd; rewrite LVE; try rewrite NUL; try rewrite (proj2 (Nat.eqb_neq n1 0) N1);
                        rewrite (nth_of_error l o1 c _ Nc); unfold bz; rewrite (proj2 (Z.eqb_neq _ _) H35);
                        try rewrite (proj2 (Nat.ltb_lt _ _) G); reflexivity | mk_inv]. }
  br false.
  (* 0x13428 bne s8,s3: name_len <> plen *)
  step. destruct (Nat.eqb_spec n1 (length P)) as [EP|EP].
  2: { br true. eapply K; [unfold upd; rewrite LVE; try rewrite NUL; try rewrite (proj2 (Nat.eqb_neq n1 0) N1);
                           rewrite (nth_of_error l o1 c _ Nc); unfold bz; rewrite (proj2 (Z.eqb_neq _ _) H35);
                           try rewrite (proj2 (Nat.ltb_ge _ _) G); try rewrite (proj2 (Nat.eqb_neq _ _) EP);
                           reflexivity | mk_inv]. }
  br false.
  (* 0x1342c ld a1,0x10(sp); mv a2,s3; jal bcmp *)
  step. step. step.
  destruct (memcmp_model_total (slice l o1 n1) P (length P)) as [v Hv]; [rewrite slice_len; lia | lia |].
  pose proof (memcmp_range _ _ _ _ Hv) as Rv.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply BCu with (ls := slice l o1 n1) (rs := P ++ Z_to_bv 8 0 :: SL) (v := v);
      [ rewrite unsigned_lit by lia; eapply (bytes_sub' _ _ _ o1 n1); [exact BL | lia | lia | reflexivity]
      | rewrite unsigned_lit by lia; exact BP
      | rewrite unsigned_lit by lia; rewrite ?Z.add_0_r, Nat2Z.id; rewrite memcmp_app by lia; exact Hv
      | exact MI ]
    | post_call segs mm ] end.
  repeat match goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  rewrite <- EP in Hv.
  (* 0x13438 beqz a0: memcmp(name, port, plen) = 0 *)
  step.
  destruct (Z.eqb_spec v 0) as [V0|V0].
  2: { if_false_by (w_neq0 v ltac:(lia) V0).
       eapply K; [unfold upd; rewrite LVE; try rewrite NUL; try rewrite (proj2 (Nat.eqb_neq n1 0) N1);
                  rewrite (nth_of_error l o1 c _ Nc); unfold bz; rewrite (proj2 (Z.eqb_neq _ _) H35);
                  try rewrite (proj2 (Nat.ltb_ge _ _) G); try rewrite (proj2 (Nat.eqb_eq _ _) EP); rewrite Hv;
                  destruct v; [congruence | reflexivity | reflexivity] | mk_inv]. }
  subst v. br true.
  dec2; [exact B2 | exact B3 | | reflexivity | reflexivity | reflexivity | reflexivity | exact BL | mk_inv0
        | eassumption | eassumption | eassumption | eassumption | exact K].
  rewrite LVE; try rewrite NUL; try rewrite (proj2 (Nat.eqb_neq n1 0) N1);
  rewrite (nth_of_error l o1 c _ Nc); unfold bz; rewrite (proj2 (Z.eqb_neq _ _) H35);
  try rewrite (proj2 (Nat.ltb_ge _ _) G); try rewrite (proj2 (Nat.eqb_eq _ _) EP); rewrite Hv. reflexivity.
Qed.

End R.
