From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib slot_ser_defs slot_ser_pure.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c snprintf_c reac_box_name_c strlen_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_json_text reac_disco_table_json_c tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import json_scalar_c.
Import ListNotations.
Open Scope Z_scope.

Definition SER_R9 : Z := 0x1361c.
Definition SER_R14 : Z := 0x1431c.

Lemma ser_cb_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma ser_eqb_refl : forall w : word, bv_eqb w w = true.
Proof. intros w. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma ser_eqb_m1 : forall x, 0 <= x < 2 ^ 64 - 1 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false.
Proof.
  intros x Hx. unfold bv_eqb. rewrite unsigned_lit by lia. rewrite unsigned_lit_wrap.
  apply Z.eqb_neq. change (-1 mod 2 ^ 64) with (2 ^ 64 - 1). lia.
Qed.

Lemma ser_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia). reflexivity.
Qed.

Lemma ser_u8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma ser_nth_pf : forall B k, (k < length B)%nat -> nth k (pf_bytes (B ++ [0])) (Z_to_bv 8 0) = Z_to_bv 8 (nth k B 0).
Proof.
  intros B k Hk. unfold pf_bytes. rewrite map_app. rewrite app_nth1 by (rewrite length_map; lia).
  apply (map_nth (Z_to_bv 8) B 0 k).
Qed.

Lemma ser_nth_pf_end : forall B, nth (length B) (pf_bytes (B ++ [0])) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  intros B. unfold pf_bytes. rewrite map_app. rewrite app_nth2 by (rewrite length_map; lia).
  rewrite length_map, Nat.sub_diag. reflexivity.
Qed.


Lemma ser_nth_pfs : forall B k rest, (k < length B)%nat ->
  nth k (pf_bytes B ++ rest) (Z_to_bv 8 0) = Z_to_bv 8 (nth k B 0).
Proof.
  intros B k rest Hk. unfold pf_bytes. rewrite app_nth1 by (rewrite length_map; lia).
  apply (map_nth (Z_to_bv 8) B 0 k).
Qed.
Lemma ser_noz : forall B, Forall (fun c => 33 <= c <= 255) B -> ~ In (Z_to_bv 8 0) (pf_bytes B).
Proof.
  intros B F H. unfold pf_bytes in H. apply in_map_iff in H as (c & E & Hc).
  rewrite Forall_forall in F. specialize (F c Hc). apply (f_equal bv_unsigned) in E.
  rewrite ser_u8 in E by lia. change (bv_unsigned (Z_to_bv 8 0)) with 0 in E. lia.
Qed.

Lemma ser_cb : forall m a n bs, rw_cells rsegs m a [CB n bs] <->
  length bs = n /\ bytes_at rsegs m a bs /\ wr_at rsegs m a (Z.of_nat n).
Proof.
  intros. unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma ser_c8 : forall m a w, rw_cells rsegs m a [C8 w] -> rw_cells rsegs m a [CB 8 (le8 w)].
Proof.
  intros m a w [[_ B] W]. apply ser_cb. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W.
  rewrite app_nil_r in B. split; [apply length_le8|]. split; [exact B|exact W].
Qed.

Lemma ser_join : forall m A A2 n1 n2 n b1 b2, A2 = A + Z.of_nat n1 -> n = (n1 + n2)%nat ->
  rw_cells rsegs m A [CB n1 b1] -> rw_cells rsegs m A2 [CB n2 b2] -> rw_cells rsegs m A [CB n (b1 ++ b2)].
Proof.
  intros m A A2 n1 n2 n b1 b2 EA En H1 H2. subst A2 n.
  apply ser_cb in H1 as (L1 & B1 & W1). apply ser_cb in H2 as (L2 & B2 & W2).
  apply ser_cb. split; [rewrite length_app; lia|]. split.
  - apply bytes_at_app. split; [exact B1|]. rewrite L1. exact B2.
  - destruct W1 as (Ha & Hn & H). destruct W2 as (Ha2 & Hn2 & H'). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.ltb_spec i (Z.of_nat n1)).
    + apply H. lia.
    + replace (A + i) with (A + Z.of_nat n1 + (i - Z.of_nat n1)) by lia. apply H'. lia.
Qed.

Lemma ser_split : forall m A A2 n1 n2 n bs, A2 = A + Z.of_nat n1 -> n = (n1 + n2)%nat ->
  rw_cells rsegs m A [CB n bs] ->
  rw_cells rsegs m A [CB n1 (firstn n1 bs)] /\ rw_cells rsegs m A2 [CB n2 (skipn n1 bs)].
Proof.
  intros m A A2 n1 n2 n bs EA En H. subst A2 n. apply ser_cb in H as (L & B & W).
  rewrite <- (firstn_skipn n1 bs) in B. apply bytes_at_app in B as [B1 B2].
  rewrite length_firstn in B2. replace (Nat.min n1 (length bs)) with n1 in B2 by lia.
  destruct W as (Ha & Hn & H). split; apply ser_cb.
  - split; [rewrite length_firstn; lia|]. split; [exact B1|]. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [rewrite length_skipn; lia|]. split; [exact B2|]. split; [lia|]. split; [lia|].
    intros i Hi. replace (A + Z.of_nat n1 + i) with (A + (Z.of_nat n1 + i)) by lia. apply H. lia.
Qed.

Lemma slot_R8_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (op : Z),
  s10 = Z_to_bv 64 op -> 0 <= op < 256 ->
  evt rsegs
    (fun ms' => exists a1' : word,
       ms' = MS (mkR (Z_to_bv 64 SER_RET) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ser_capz op)) a1' a2 a3 a4 a5 a6 a7
                     s2 s3 s4 (Z_to_bv 64 (ser_cap op)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 SER_MALLOC) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SER_IN) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m op Es10 Hop.
  subst s10. unfold SER_IN, SER_RET, SER_MALLOC.
  pose proof (ser_k_range op Hop) as Hk. pose proof (ser_cap_range op Hop) as [Hc Hcz].
  rewrite Hcz.
  step. step. rewrite (unsigned_lit op) by lia. rewrite ser_k_bits by exact Hop.
  step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (ser_k op) 0) as [K0|K0]; cbn [negb].
  - assert (EC : ser_cap op = 1280) by (unfold ser_cap; rewrite K0; reflexivity). rewrite EC.
    step. step. step. step. step.
    replace (Z_to_bv 64 (1280 + bv_unsigned (v_sltiu (Z_to_bv 64 1280) 1))) with (Z_to_bv 64 1280)
      by (vm_compute; reflexivity).
    apply evt_done. eexists. reflexivity.
  - assert (EC : ser_cap op = 41 * ser_k op - 39)
      by (unfold ser_cap; rewrite (proj2 (Z.eqb_neq _ _) K0); reflexivity).
    rewrite EC. rewrite EC in Hc.
    step. step. step. step. step. step.
    rewrite (unsigned_lit (ser_k op)) by lia.
    replace (ser_k op * 41 + -39) with (41 * ser_k op - 39) by lia.
    unfold v_sltiu. rewrite (unsigned_lit (41 * ser_k op - 39)) by lia.
    replace (bv_wrap 64 1) with 1 by reflexivity.
    replace (41 * ser_k op - 39 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity. rewrite Z.add_0_r.
    apply evt_done. eexists. reflexivity.
Qed.

Lemma slot_R14 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 SER_FREE_RET) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 SER_FREE) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SER_R14) fc None m (seg_rom rsegs)).
Proof.
  intros. unfold SER_R14, SER_FREE_RET, SER_FREE.
  step. step. apply evt_done. reflexivity.
Qed.

Lemma slot_R8_ret : reac_disco_table_json_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (canary : word)
    (X lo buf cap now : Z) (T junk : list byte),
  sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 buf -> s5 = Z_to_bv 64 cap -> s11 = Z_to_bv 64 now ->
  0 < X -> X mod 16 = 0 -> X + 2592 < 2 ^ 63 -> 0 <= now < 2 ^ 64 ->
  2 <= cap <= 1280 -> 0 < buf -> buf + cap <= lo -> pf_img_free buf cap ->
  rw_cells rsegs m buf [CB (Z.to_nat cap) junk] ->
  length T = 400%nat -> disco_table_c.table_ok T -> rw_cells rsegs m (X + 512) [CB 400 T] ->
  bytes_at rsegs m BN_TS bn_table ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo X -> lo + TJ_K <= X -> IMG_END <= lo ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
       frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo X /\
       ((ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 buf) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F' (Z_to_bv 64 SER_R14) fc' None m' (seg_rom rsegs) /\
         munch [(lo, X); (buf, buf + cap)] m m')
        \/ (ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length (tj_text T now)))) s5 s6 s7 s8 s9 s10 s11
                          t3' t4' t5' t6')
                    F' (Z_to_bv 64 SER_R9) fc' None m' (seg_rom rsegs) /\
            Z.of_nat (length (tj_text T now)) < cap /\
            munch [(lo, X); (buf, buf + Z.of_nat (length (tj_text T now)) + 1)] m m' /\
            bytes_at rsegs m' buf (pf_bytes (tj_text T now ++ [0])))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SER_RET) fc None m (seg_rom rsegs)).
Proof.
  intros TJC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m canary X lo buf cap now T junk Esp Ea0 Es5 Es11 HX0 HX16 HX1 Hnow Hcap Hb0 Hblo HIF RB LT TOK RT
    BN GG GW FRM MI TM ST HLO HIMG.
  subst sp a0 s5 s11. unfold SER_RET, SER_R9, SER_R14.
  assert (HBB : buf + cap <= 2 ^ 64)
    by (pose proof (rw_cells_bound rsegs m buf _ RB) as H; cbn [cells_size csize] in H; lia).
  pose proof (ser_tj_ok T LT TOK) as [TOK' WF].
  pose proof (C7_text_bound box_tok (tj_entries T) now ser_tok_ok TOK' WF Hnow) as HLB.
  change (table_json_text box_tok (tj_entries T) now) with (tj_text T now) in HLB.
  pose proof (ser_cb_bytes m (X + 512) 400 T RT) as RTB.
  assert (HLO' : lo + 6224 <= X) by (change TJ_K with 6224 in HLO; lia).
  step. rewrite eqb_lit by lia. replace (buf =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply TJC with (lo := lo) (canary := canary) (T := T) (junk := junk);
      rewrite ?unsigned_lit by lia;
      first [ assumption | lia
            | (intros _; split; [lia|]; split; [exact RB|]; split; [lia|]; split; [lia|exact HIF]) ]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m2 &
              Eq & FRM2 & FK & WM2 & MI2 & TM2 & ST2 & A1 & A2 & A3).
  subst ms'. rewrite (ret_pc_even 79360) by (first [lia | reflexivity]).
  rewrite !(unsigned_lit cap), !(unsigned_lit buf), !(unsigned_lit X), !(unsigned_lit now) in * by lia.
  set (len := Z.of_nat (length (tj_text T now))) in *.
  assert (HL9 : len <= 969) by (unfold len; lia).
  step. step. step. rewrite ltu_lit by lia.
  destruct (Z.ltb_spec cap 3) as [C3|C3]; [|destruct (Z.ltb_spec len cap) as [CL|CL]].
  - destruct (A1 C3) as [E MU]. subst a0'.
    replace (cap <? 1280) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
    step. step. rewrite ser_eqb_refl. cbv iota.
    apply evt_done. do 19 eexists.
    split; [exact FRM2|]. split; [exact FK|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|].
    left. split; [reflexivity|]. eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; intuition lia.
  - destruct (A2 C3 CL) as (E & MU & BT). subst a0'.
    destruct (Z.ltb_spec cap 1280) as [C12|C12]; cbv iota.
    + step. step. rewrite ser_eqb_m1 by lia. cbv iota.
      apply evt_done. do 19 eexists.
      split; [exact FRM2|]. split; [exact FK|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|].
      right. split; [reflexivity|]. split; [exact CL|]. split; [exact MU|exact BT].
    + step. step. rewrite ser_eqb_m1 by lia. cbv iota.
      step. step. rewrite ser_eqb_m1 by lia. cbv iota.
      apply evt_done. do 19 eexists.
      split; [exact FRM2|]. split; [exact FK|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|].
      right. split; [reflexivity|]. split; [exact CL|]. split; [exact MU|exact BT].
  - destruct (A3 C3 CL) as [E MU]. subst a0'.
    replace (cap <? 1280) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
    step. step. rewrite ser_eqb_refl. cbv iota.
    apply evt_done. do 19 eexists.
    split; [exact FRM2|]. split; [exact FK|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|].
    left. split; [reflexivity|exact MU].
Qed.

Lemma slot_R9 : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X buf cap i p : Z) (B : list Z)
    (slack j160 j184 : list byte),
  sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 i -> s3 = Z_to_bv 64 buf -> s4 = Z_to_bv 64 (Z.of_nat (length B)) ->
  s5 = Z_to_bv 64 cap -> s7 = Z_to_bv 64 p ->
  0 <= X -> X + 2592 <= 2 ^ 64 -> 0 < buf -> Z.of_nat (length B) < cap < 2 ^ 63 ->
  Forall (fun c => 33 <= c <= 255) B -> (2 <= length B)%nat ->
  nth 0 B 0 = 91 -> nth (length B - 1) B 0 = 93 ->
  bytes_at rsegs m buf (pf_bytes (B ++ [0])) -> bytes_at rsegs m (buf + Z.of_nat (length B) + 1) slack ->
  (- (buf + Z.of_nat (length B) + 1)) mod 8 <= Z.of_nat (length slack) ->
  buf + Z.of_nat (length B) + 1 + Z.of_nat (length slack) <= X ->
  rw_cells rsegs m (X + 160) [CB 8 j160] -> rw_cells rsegs m (X + 184) [CB 8 j184] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (buf + Z.of_nat (length B))) a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 SER_JSON) fc None m' (seg_rom rsegs) /\
       munch [(X + 160, X + 168); (X + 184, X + 192)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 i)] /\ rw_cells rsegs m' (X + 184) [C8 (Z_to_bv 64 p)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SER_R9) fc None m (seg_rom rsegs)).
Proof.
  intros SLC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X buf cap i p B slack j160 j184 Esp Es1 Es3 Es4 Es5 Es7 HX0 HX1 Hb0 Hcap HB33 HB2 HB0 HBn BB BS HSL HSX
    C160 C184 MI.
  subst sp s1 s3 s4 s5 s7. unfold SER_R9, SER_JSON.
  assert (LB2 : Z.of_nat (length (pf_bytes (B ++ [0]))) = Z.of_nat (length B) + 1)
    by (unfold pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
  set (len := Z.of_nat (length B)) in *.
  pose proof (munch_refl [(X + 160, X + 168); (X + 184, X + 192)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  step. step. rewrite ser_lts by lia. replace (len <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. rewrite ltu_lit by lia. replace (len <? cap) with true by (symmetry; apply Z.ltb_lt; lia). cbv [negb]; cbv iota.
  pose proof (read1 m1 buf (pf_bytes (B ++ [0])) (length B) BB ltac:(lia)) as RD0.
  rewrite ser_nth_pf_end in RD0. unfold wa in RD0. fold len in RD0.
  step. step. step.
  change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). rewrite ser_eqb_refl. cbn [negb]. cbv iota.
  step. step.
  assert (BSL : bytes_at rsegs m1 buf (pf_bytes B ++ Z_to_bv 8 0 :: slack)).
  { replace (pf_bytes B ++ Z_to_bv 8 0 :: slack) with (pf_bytes (B ++ [0]) ++ slack)
      by (unfold pf_bytes; rewrite map_app, <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BB|]. rewrite LB2, Z.add_assoc. exact BS. }
  assert (LPB : length (pf_bytes B) = length B) by (unfold pf_bytes; apply length_map).
  eapply evt_cut.
  { eapply SLC with (str := pf_bytes B) (slack := slack);
      rewrite ?(unsigned_lit buf) by lia;
      [exact BSL | exact (ser_noz B HB33) | rewrite LPB; fold len; lia | exact MI]. }
  intros ms' PO. unfold strlen_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  Eq & MU2 & WM2 & MI2 & BS2).
  subst ms'. rewrite (ret_pc_even 79428) by (first [lia | reflexivity]).
  rewrite (unsigned_lit buf) in BS2 by lia.
  transport_after_call rsegs m1 m2 MU2 WM2. clear MU2 WM2 MI.
  rewrite LPB. fold len.
  step. rewrite ser_eqb_refl. cbn [negb]. cbv iota.
  pose proof (read1 m2 buf _ 0 BS2 ltac:(rewrite length_app, LPB; lia)) as RD1.
  rewrite ser_nth_pfs, HB0 in RD1 by lia. replace (wa (buf + Z.of_nat 0)) with (Z_to_bv 64 buf) in RD1
    by (unfold wa; f_equal; lia).
  step. step. step. change (zxb (Z_to_bv 8 91)) with (Z_to_bv 64 91). rewrite ser_eqb_refl. cbn [negb]. cbv iota.
  pose proof (read1 m2 buf _ (length B - 1) BS2 ltac:(rewrite length_app, LPB; cbn [length]; lia)) as RD2.
  rewrite ser_nth_pfs, HBn in RD2 by lia. replace (wa (buf + Z.of_nat (length B - 1))) with (Z_to_bv 64 (buf + len + -1)) in RD2
    by (unfold wa, len; f_equal; lia).
  step. step. step. change (zxb (Z_to_bv 8 93)) with (Z_to_bv 64 93). rewrite ser_eqb_refl. cbn [negb]. cbv iota.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact C160|exact C184].
Qed.
