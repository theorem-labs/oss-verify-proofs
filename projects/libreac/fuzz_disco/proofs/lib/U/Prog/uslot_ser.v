From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text disco_json_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_json_c slot_ser_defs slot_ser_pure slot_ser.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv slot_lib printf_facts_c snprintf_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c strlen_c disco_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_defs uslot_ser_pure uslot_ser_tokb.
Import ListNotations.
Open Scope Z_scope.

Definition uSER_R9 : Z := 0x13758.
Definition uSER_R14 : Z := 0x14174.

Lemma user_cb_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

Lemma user_nth_pf : forall B k, (k < length B)%nat -> nth k (pf_bytes (B ++ [0])) (Z_to_bv 8 0) = Z_to_bv 8 (nth k B 0).
Proof. exact ser_nth_pf. Qed.

Lemma user_nth_pf_end : forall B, nth (length B) (pf_bytes (B ++ [0])) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. exact ser_nth_pf_end. Qed.

Lemma user_nth_pfs : forall B k rest, (k < length B)%nat ->
  nth k (pf_bytes B ++ rest) (Z_to_bv 8 0) = Z_to_bv 8 (nth k B 0).
Proof. exact ser_nth_pfs. Qed.

Lemma user_noz : forall B, Forall (fun c => 33 <= c <= 255) B -> ~ In (Z_to_bv 8 0) (pf_bytes B).
Proof. exact ser_noz. Qed.

Lemma user_cb : forall m a n bs, rw_cells rsegs m a [CB n bs] <->
  length bs = n /\ bytes_at rsegs m a bs /\ wr_at rsegs m a (Z.of_nat n).
Proof.
  intros. unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, Nat.add_0_r. tauto.
Qed.

Lemma user_c8 : forall m a w, rw_cells rsegs m a [C8 w] -> rw_cells rsegs m a [CB 8 (le8 w)].
Proof.
  intros m a w [[_ B] W]. apply user_cb. cbn [cells_bytes cbytes cells_size csize Nat.add] in B, W.
  rewrite app_nil_r in B. split; [apply length_le8|]. split; [exact B|exact W].
Qed.

Lemma user_join : forall m A A2 n1 n2 n b1 b2, A2 = A + Z.of_nat n1 -> n = (n1 + n2)%nat ->
  rw_cells rsegs m A [CB n1 b1] -> rw_cells rsegs m A2 [CB n2 b2] -> rw_cells rsegs m A [CB n (b1 ++ b2)].
Proof.
  intros m A A2 n1 n2 n b1 b2 EA En H1 H2. subst A2 n.
  apply user_cb in H1 as (L1 & B1 & W1). apply user_cb in H2 as (L2 & B2 & W2).
  apply user_cb. split; [rewrite length_app; lia|]. split.
  - apply bytes_at_app. split; [exact B1|]. rewrite L1. exact B2.
  - destruct W1 as (Ha & Hn & H). destruct W2 as (Ha2 & Hn2 & H'). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.ltb_spec i (Z.of_nat n1)).
    + apply H. lia.
    + replace (A + i) with (A + Z.of_nat n1 + (i - Z.of_nat n1)) by lia. apply H'. lia.
Qed.

Lemma user_split : forall m A A2 n1 n2 n bs, A2 = A + Z.of_nat n1 -> n = (n1 + n2)%nat ->
  rw_cells rsegs m A [CB n bs] ->
  rw_cells rsegs m A [CB n1 (firstn n1 bs)] /\ rw_cells rsegs m A2 [CB n2 (skipn n1 bs)].
Proof.
  intros m A A2 n1 n2 n bs EA En H. subst A2 n. apply user_cb in H as (L & B & W).
  rewrite <- (firstn_skipn n1 bs) in B. apply bytes_at_app in B as [B1 B2].
  rewrite length_firstn in B2. replace (Nat.min n1 (length bs)) with n1 in B2 by lia.
  destruct W as (Ha & Hn & H). split; apply user_cb.
  - split; [rewrite length_firstn; lia|]. split; [exact B1|]. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
  - split; [rewrite length_skipn; lia|]. split; [exact B2|]. split; [lia|]. split; [lia|].
    intros i Hi. replace (A + Z.of_nat n1 + i) with (A + (Z.of_nat n1 + i)) by lia. apply H. lia.
Qed.

Lemma user_not_lit : forall t, 0 <= t < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 t)) 18446744073709551615) = Z_to_bv 64 (nt t).
Proof. intros t Ht. unfold nt. rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. reflexivity. Qed.

Lemma uslot_R8_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X op : Z) (j136 j152 : list byte),
  sp = Z_to_bv 64 X -> s9 = Z_to_bv 64 op -> 0 <= op < 256 -> 0 <= X -> X + 2624 <= 2 ^ 64 ->
  rw_cells rsegs m (X + 136) [CB 8 j136] -> rw_cells rsegs m (X + 152) [CB 8 j152] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (a1' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 uSER_RET) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ser_capz op)) a1' a2 a3 a4 a5 a6 a7
                     s2 s3 s4 (Z_to_bv 64 (ser_cap op)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 uSER_MALLOC) fc None m' (seg_rom rsegs) /\
       munch [(X + 136, X + 144); (X + 152, X + 160)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 136) [C8 s7] /\ rw_cells rsegs m' (X + 152) [C8 s6])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 uSER_IN) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X op
    j136 j152 Esp Es9 Hop HX0 HX1 C136 C152 MI.
  subst sp s9. unfold uSER_IN, uSER_RET, uSER_MALLOC.
  pose proof (ser_k_range op Hop) as Hk. pose proof (ser_cap_range op Hop) as [Hc Hcz].
  rewrite Hcz.
  pose proof (munch_refl [(X + 136, X + 144); (X + 152, X + 160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. rewrite (unsigned_lit op) by lia. rewrite ser_k_bits by exact Hop.
  step. step.
  step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec (ser_k op) 0) as [K0|K0]; cbn [negb].
  - assert (EC : ser_cap op = 1280) by (unfold ser_cap; rewrite K0; reflexivity). rewrite EC.
    step. step. step. step. step.
    replace (Z_to_bv 64 (1280 + bv_unsigned (v_sltiu (Z_to_bv 64 1280) 1))) with (Z_to_bv 64 1280)
      by (vm_compute; reflexivity).
    apply evt_done. eexists. eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
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
    apply evt_done. eexists. eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma uslot_R14 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs
    (fun ms' => ms' = MS (mkR (Z_to_bv 64 uSER_FREE_RET) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 uSER_FREE) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 uSER_R14) fc None m (seg_rom rsegs)).
Proof.
  intros. unfold uSER_R14, uSER_FREE_RET, uSER_FREE.
  step. step. apply evt_done. reflexivity.
Qed.

Lemma uslot_R8_ret : U.Prog.reac_disco_table_json_c.reac_disco_table_json_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (canary : word)
    (X lo buf cap now : Z) (T junk : list byte),
  sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 buf -> s5 = Z_to_bv 64 cap ->
  0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 <= now < 2 ^ 64 ->
  2 <= cap <= 1280 -> 0 < buf -> buf + cap <= lo -> pf_img_free buf cap ->
  rw_cells rsegs m buf [CB (Z.to_nat cap) junk] ->
  length T = 400%nat -> U.Prog.disco_table_c.table_ok T -> rw_cells rsegs m (X + 544) [CB 400 T] ->
  rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
  bytes_at rsegs m BN_TS bn_table ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  frm0 fc -> mem_inv rsegs m -> U.MemNorm.task_mem rsegs m -> stk rsegs m lo X ->
  lo + U.Prog.reac_disco_table_json_c.TJ_K <= X -> IMG_END <= lo ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
       frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ U.MemNorm.task_mem rsegs m' /\ stk rsegs m' lo X /\
       ((ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 buf) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F' (Z_to_bv 64 uSER_R14) fc' None m' (seg_rom rsegs) /\
         munch [(lo, X); (buf, buf + cap)] m m')
        \/ (ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length (tj_text T now)))) s5 s6 s7 s8 s9 s10 s11
                          t3' t4' t5' t6')
                    F' (Z_to_bv 64 uSER_R9) fc' None m' (seg_rom rsegs) /\
            Z.of_nat (length (tj_text T now)) < cap /\
            munch [(lo, X); (buf, buf + Z.of_nat (length (tj_text T now)) + 1)] m m' /\
            bytes_at rsegs m' buf (pf_bytes (tj_text T now ++ [0])))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 uSER_RET) fc None m (seg_rom rsegs)).
Proof.
  intros TJC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m canary X lo buf cap now T junk Esp Ea0 Es5 HX0 HX16 HX1 Hnow Hcap Hb0 Hblo HIF RB LT TOK RT RN
    BN GG GW FRM MI TM ST HLO HIMG.
  subst sp a0 s5. unfold uSER_RET, uSER_R9, uSER_R14.
  assert (HBB : buf + cap <= 2 ^ 64)
    by (pose proof (rw_cells_bound rsegs m buf _ RB) as H; cbn [cells_size csize] in H; lia).
  pose proof (user_tj_ok T LT TOK) as [TOK' WF].
  pose proof (C7_text_bound box_tok (tj_entries T) now ser_tok_ok TOK' WF Hnow) as HLB.
  change (table_json_text box_tok (tj_entries T) now) with (tj_text T now) in HLB.
  pose proof (user_cb_bytes m (X + 544) 400 T RT) as RTB.
  assert (HLO' : lo + 6240 <= X) by (change U.Prog.reac_disco_table_json_c.TJ_K with 6240 in HLO; lia).
  step. rewrite eqb_lit by lia. replace (buf =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  step. step. step. step. step. step.
  eapply evt_cut.
  { eapply TJC with (lo := lo) (canary := canary) (T := T) (junk := junk);
      rewrite ?unsigned_lit by lia;
      first [ assumption | lia
            | (intros _; split; [lia|]; split; [exact RB|]; split; [lia|]; split; [lia|exact HIF]) ]. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & m2 &
              Eq & FRM2 & FK & WM2 & MI2 & TM2 & ST2 & A1 & A2 & A3).
  subst ms'. rewrite (ret_pc_even 79676) by (first [lia | reflexivity]).
  rewrite !(unsigned_lit cap), !(unsigned_lit buf), !(unsigned_lit X), !(unsigned_lit now) in * by lia.
  change (U.Prog.reac_disco_table_json_c.tj_text T now) with (tj_text T now) in A2, A3.
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

Lemma uslot_R9 : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (buf cap : Z) (B : list Z) (slack : list byte),
  s3 = Z_to_bv 64 buf -> s4 = Z_to_bv 64 (Z.of_nat (length B)) -> s5 = Z_to_bv 64 cap ->
  0 < buf -> Z.of_nat (length B) < cap < 2 ^ 31 ->
  Forall (fun c => 33 <= c <= 255) B -> (2 <= length B)%nat ->
  nth 0 B 0 = 91 -> nth (length B - 1) B 0 = 93 ->
  bytes_at rsegs m buf (pf_bytes (B ++ [0])) -> bytes_at rsegs m (buf + Z.of_nat (length B) + 1) slack ->
  (- (buf + Z.of_nat (length B) + 1)) mod 8 <= Z.of_nat (length slack) ->
  mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                       (m' : word -> option byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (nt buf)) a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 uSER_JSON) fc None m' (seg_rom rsegs) /\
       munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 uSER_R9) fc None m (seg_rom rsegs)).
Proof.
  intros SLC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m buf cap B slack Es3 Es4 Es5 Hb0 Hcap HB33 HB2 HB0 HBn BB BS HSL MI.
  subst s3 s4 s5. unfold uSER_R9, uSER_JSON.
  assert (LB2 : Z.of_nat (length (pf_bytes (B ++ [0]))) = Z.of_nat (length B) + 1)
    by (unfold pf_bytes; rewrite length_map, length_app; cbn [length]; lia).
  pose proof (bytes_at_bound rsegs m buf _ BB) as HBB. rewrite LB2 in HBB.
  set (len := Z.of_nat (length B)) in *.
  step. step. rewrite ser_lts by lia. replace (len <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. rewrite ltu_lit by lia. replace (len <? cap) with true by (symmetry; apply Z.ltb_lt; lia). cbv [negb]; cbv iota.
  step. rewrite user_not_lit by lia.
  step. rewrite utok_nt_ltu by lia. cbv iota.
  pose proof (read1 m buf (pf_bytes (B ++ [0])) (length B) BB ltac:(lia)) as RD0.
  rewrite user_nth_pf_end in RD0. unfold wa in RD0. fold len in RD0.
  step. step. step.
  change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). rewrite ser_eqb_refl. cbn [negb]. cbv iota.
  step. step.
  assert (BSL : bytes_at rsegs m buf (pf_bytes B ++ Z_to_bv 8 0 :: slack)).
  { replace (pf_bytes B ++ Z_to_bv 8 0 :: slack) with (pf_bytes (B ++ [0]) ++ slack)
      by (unfold pf_bytes; rewrite map_app, <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BB|]. rewrite LB2, Z.add_assoc. exact BS. }
  assert (LPB : length (pf_bytes B) = length B) by (unfold pf_bytes; apply length_map).
  eapply evt_cut.
  { eapply SLC with (str := pf_bytes B) (slack := slack);
      rewrite ?(unsigned_lit buf) by lia;
      [exact BSL | exact (user_noz B HB33) | rewrite LPB; fold len; lia | exact MI]. }
  intros ms' PO. unfold strlen_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  Eq & MU2 & WM2 & MI2 & BS2).
  subst ms'. rewrite (ret_pc_even 79744) by (first [lia | reflexivity]).
  rewrite (unsigned_lit buf) in BS2 by lia.
  clear RD0 BSL BB BS MI.
  rewrite LPB. fold len.
  step. rewrite ser_eqb_refl. cbn [negb]. cbv iota.
  pose proof (read1 m2 buf _ 0 BS2 ltac:(rewrite length_app, LPB; lia)) as RD1.
  rewrite user_nth_pfs, HB0 in RD1 by lia. replace (wa (buf + Z.of_nat 0)) with (Z_to_bv 64 buf) in RD1
    by (unfold wa; f_equal; lia).
  step. step. step. change (zxb (Z_to_bv 8 91)) with (Z_to_bv 64 91). rewrite ser_eqb_refl. cbn [negb]. cbv iota.
  step. rewrite ?(unsigned_lit len) by lia. rewrite swrap32_id by lia.
  step. rewrite utok_nt_ltu by lia. cbv iota.
  pose proof (read1 m2 buf _ (length B - 1) BS2 ltac:(rewrite length_app, LPB; cbn [length]; lia)) as RD2.
  rewrite user_nth_pfs, HBn in RD2 by lia. replace (wa (buf + Z.of_nat (length B - 1))) with (Z_to_bv 64 (buf + (len + -1))) in RD2
    by (unfold wa, len; f_equal; lia).
  step. step. step. step. change (zxb (Z_to_bv 8 93)) with (Z_to_bv 64 93). rewrite ser_eqb_refl. cbn [negb]. cbv iota.
  apply evt_done. do 17 eexists. split; [reflexivity|].
  split; [exact MU2|]. split; [exact WM2|exact MI2].
Qed.
