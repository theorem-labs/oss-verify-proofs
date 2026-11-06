From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_exit slot_step memcpy_c.
Import ListNotations.
Open Scope Z_scope.

Definition R17 : Z := 0x134e4.
Definition MALLOC_PC : Z := 0x17330.
Definition R17_RET : Z := 0x136fc.

Definition rec_take (n : Z) : Z := Z.min n 2.
Definition rec_want (R : list byte) : Z := rdb R 0 + 256 * rdb R 1.
Definition rec_rem (n : Z) : Z := n - rec_take n.
Lemma zxb_unsigned : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. pose proof (byte_range b). apply unsigned_lit. lia. Qed.

Definition rec_len (R : list byte) (n : Z) : Z := Z.min (rec_want R) (rec_rem n).
Ltac zltb_false := match goal with |- context [?x <? ?y] => replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) end; cbv iota.
Ltac zltb_true := match goal with |- context [?x <? ?y] => replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) end; cbv iota.


Lemma slot_R17_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n p : Z) (R : list byte) (jop : word),
  sp = Z_to_bv 64 X -> s3 = Z_to_bv 64 n -> s6 = Z_to_bv 64 p ->
  0 <= X -> X + 2592 <= 2 ^ 64 -> 0 <= n -> Z.of_nat (length R) = n -> p + n < 2 ^ 64 ->
  bytes_at rsegs m p R ->
  rw_cells rsegs m (X + 216) [C8 jop] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (a1' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 R17_RET) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rec_len R n)) a1' a2 a3 a4 a5 a6 a7
                     s2 (Z_to_bv 64 (rec_len R n)) s4 s5 (Z_to_bv 64 (p + rec_take n)) (Z_to_bv 64 (rec_rem n))
                     s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 MALLOC_PC) fc None m' (seg_rom rsegs) /\
       munch [(X + 216, X + 224)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 216) [C8 s10])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R17) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X n p R jop Esp Es3 Es6 HX0 HX1 Hn HL Hpn HB C216 MI.
  subst sp s3 s6. unfold R17, R17_RET, MALLOC_PC.
  pose proof (munch_refl [(X + 216, X + 224)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound rsegs m p R HB) as HBp.
  pose proof (byte_range (nth 0 R (Z_to_bv 8 0))) as Hr0.
  pose proof (byte_range (nth 1 R (Z_to_bv 8 0))) as Hr1.
  destruct (Z.eq_dec n 0) as [E0|N0]; [|destruct (Z.eq_dec n 1) as [E1|N1]].
  - rewrite E0 in *. destruct R as [|b R]; [|cbn in HL; lia].
    step. rewrite eqb_lit by lia. cbn [Z.eqb negb].
    step. step. step. step.
    step.
    step. step. rewrite ltu_lit by lia. cbn [Z.ltb Z.compare].
    step. step. step.
    apply evt_done. eexists (Z_to_bv 64 0), _. split.
    + replace (rec_len [] 0) with 0 by reflexivity. replace (rec_take 0) with 0 by reflexivity.
      replace (rec_rem 0) with 0 by reflexivity. rewrite Z.add_0_r. reflexivity.
    + split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - rewrite E1 in *.
    assert (R0 : ov_read_bytes rsegs m (wa p) 1 = Some [nth 0 R (Z_to_bv 8 0)]).
    { replace (wa p) with (wa (p + Z.of_nat 0)) by (f_equal; lia). apply read1; [exact HB | lia]. }
    step. rewrite eqb_lit by lia. cbn [Z.eqb Pos.eqb negb].
    step. step. step. rewrite eqb_lit by lia. cbn [Z.eqb Pos.eqb negb].
    step. step. step. step.
    step. step.
    rewrite Z.lor_0_l, zxb_unsigned.
    step. rewrite ltu_lit by lia. zltb_false.
    step. step. step.
    assert (EL : rec_len R 1 = 0) by (unfold rec_len, rec_rem, rec_take, rec_want, rdb; lia).
    assert (ET : rec_take 1 = 1) by reflexivity. assert (ER : rec_rem 1 = 0) by reflexivity.
    rewrite EL, ET, ER.
    apply evt_done. eexists (Z_to_bv 64 0), _. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; eassumption.
  - assert (R0 : ov_read_bytes rsegs m (wa p) 1 = Some [nth 0 R (Z_to_bv 8 0)]).
    { replace (wa p) with (wa (p + Z.of_nat 0)) by (f_equal; lia). apply read1; [exact HB | lia]. }
    assert (R1 : ov_read_bytes rsegs m (wa (p + 1)) 1 = Some [nth 1 R (Z_to_bv 8 0)]).
    { apply (read1 m p R 1 HB). lia. }
    step. rewrite eqb_lit by lia. replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    step. step. step. rewrite eqb_lit by lia. replace (n =? 1) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    step. step. step. step.
    step. step.
    assert (W : Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (nth 1 R (Z_to_bv 8 0)))) 8)))
                  (bv_unsigned (zxb (nth 0 R (Z_to_bv 8 0)))) = rec_want R).
    { rewrite !zxb_unsigned. rewrite (unsigned_lit (Z.shiftl _ 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      unfold rec_want, rdb. apply lor_byte_shift; lia. }
    rewrite W.
    assert (HW : 0 <= rec_want R < 65536) by (unfold rec_want, rdb; lia).
    assert (ET : rec_take n = 2) by (unfold rec_take; lia).
    assert (ER : rec_rem n = n + -2) by (unfold rec_rem; lia).
    rewrite ET, ER.
    step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (rec_want R) (n + -2)) as [Hlt|Hge].
    + cbv iota. step. step.
      assert (EL : rec_len R n = rec_want R) by (unfold rec_len; rewrite ER; lia). rewrite EL.
      apply evt_done. eexists _, _. split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; eassumption.
    + cbv iota. step. step. step.
      assert (EL : rec_len R n = n + -2) by (unfold rec_len; rewrite ER; lia). rewrite EL.
      apply evt_done. eexists _, _. split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Ltac r17_fin := apply evt_done; do 17 eexists; split; [reflexivity|];
  repeat (split; [eassumption|]); eassumption.

Ltac r17_tail k Hk :=
  step; step;
  step; rewrite eqb_lit by lia;
  destruct (Z.eqb_spec k 0) as [K0|K0]; cbn [negb];
  [ subst k; r17_fin
  | step; step; rewrite eqb_lit by lia;
    destruct (Z.eqb_spec k 2) as [K2|K2]; cbn [negb];
    [ subst k; r17_fin
    | assert (K1 : k = 1) by lia; subst k; r17_fin ] ].

Definition r17_exit (k : Z) : Z := if k =? 0 then 0x13740 else if k =? 1 then 0x13758 else 0x13730.

Lemma slot_R17_copy : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X f len body k : Z) (Rb junk : list byte) (jb jf : word),
  memcpy_contract ->
  sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 f -> s3 = Z_to_bv 64 len -> s6 = Z_to_bv 64 body -> s5 = Z_to_bv 64 k ->
  0 <= X -> X + 2592 <= 2 ^ 64 -> 0 < f -> f + len <= X -> 0 <= len < 2 ^ 16 -> 0 <= k <= 2 ->
  0 <= body -> body + len <= f \/ f + len <= body -> body + len < 2 ^ 64 ->
  bytes_at rsegs m body Rb -> Z.of_nat (length Rb) = len ->
  rw_cells rsegs m f [CB (Z.to_nat len) junk] ->
  rw_cells rsegs m (X + 184) [C8 jb] -> rw_cells rsegs m (X + 224) [C8 jf] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 f) s11 t3' t4' t5' t6')
                F (Z_to_bv 64 (r17_exit k)) fc None m' (seg_rom rsegs) /\
       munch [(f, f + len); (X + 184, X + 192); (X + 224, X + 232)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' f [CB (Z.to_nat len) Rb] /\
       rw_cells rsegs m' (X + 184) [C8 (Z_to_bv 64 body)] /\ rw_cells rsegs m' (X + 224) [C8 (Z_to_bv 64 f)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R17_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X f len body k Rb junk jb jf MCC Esp Ea0 Es3 Es6 Es5 HX0 HX1 Hf0 Hf1 Hlen Hk Hb0 Hdj Hb1 HB HL RF C184 C224 MI.
  subst sp a0 s3 s6 s5. unfold R17_RET, r17_exit.
  pose proof (munch_refl [(f, f + len); (X + 184, X + 192); (X + 224, X + 232)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. rewrite eqb_lit by lia. replace (f =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec len 0) as [L0|L0].
  - destruct RF as [[Hwf ?] ?]. cbn in Hwf. destruct junk as [|? ?]; [|cbn in Hwf; lia].
    rewrite L0 in *. destruct Rb as [|? ?]; [|cbn in HL; lia].
    assert (RF : rw_cells rsegs m f [CB (Z.to_nat 0) []]) by (split; [split|]; assumption).
    r17_tail k Hk.
  - cbn [negb]. step. step. step. step.
    eapply evt_cut.
    { eapply (MCC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m Rb junk).
      - rewrite (unsigned_lit body) by lia. exact HB.
      - rewrite (unsigned_lit len) by lia. lia.
      - rewrite (unsigned_lit f), (unsigned_lit len) by lia. exact RF.
      - rewrite (unsigned_lit f), (unsigned_lit len), (unsigned_lit body) by lia. lia.
      - exact MI. }
    intros ms' PO. unfold memcpy_post in PO.
    destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & Eq & MUc & WMc & MI2 & RVm & OBm).
    subst ms'.
    rewrite (unsigned_lit f), (unsigned_lit len) in MUc, RVm by lia. rewrite (unsigned_lit body) in OBm by lia.
    transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI.
    rewrite (ret_pc_even 79644) by (first [lia | reflexivity]).
    r17_tail k Hk.
Qed.

Definition R27 : Z := 0x1409c.
Definition R27_RET : Z := 0x140b0.

Lemma slot_R27_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X f len rem body : Z),
  sp = Z_to_bv 64 X -> s3 = Z_to_bv 64 len -> s7 = Z_to_bv 64 rem ->
  0 <= X -> X + 2592 <= 2 ^ 64 -> 0 <= len <= rem -> rem < 2 ^ 64 -> 0 <= body -> body + len < 2 ^ 64 ->
  rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 body)] -> rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 f)] ->
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 R27_RET) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
                              s2 (Z_to_bv 64 (rem - len)) s4 (Z_to_bv 64 (body + len)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 FREE_PC) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R27) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X f len rem body Esp Es3 Es7 HX0 HX1 Hl Hr Hb0 Hb1 C184 C224.
  subst sp s3 s7. unfold R27, R27_RET, FREE_PC.
  step. step. step. step. step.
  rewrite (unsigned_lit rem), (unsigned_lit len) by lia.
  apply evt_done. reflexivity.
Qed.

Lemma slot_R27_ret : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 LATCH) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 R27_RET) fc None m (seg_rom rsegs)).
Proof.
  intros R F fc m. unfold R27_RET, LATCH.
  step. apply evt_done. reflexivity.
Qed.
