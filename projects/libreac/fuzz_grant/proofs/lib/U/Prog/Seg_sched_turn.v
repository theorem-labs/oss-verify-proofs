From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Arr
  Tac Bytes ZBridge Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel SlotNeeds_c GrantSlotPlan SlotBridge
  LLVMFuzzerTestOneInput_c Seg_sched_lib reac_headamp_tx_next_c reac_headamp_tx_effective_c reac_headamp_default_c
  NextModel NextLemmas GrantModel HeadampSched SegSetModel HeadampI1.
Import ListNotations.
Open Scope Z_scope.

Lemma le1_one : forall w, le1 w = [Z_to_bv 8 (bv_unsigned w)].
Proof. reflexivity. Qed.

Lemma wr_sub : forall m A n B j, wr_at rsegs m A n -> A <= B -> 0 <= j -> B + j <= A + n -> wr_at rsegs m B j.
Proof.
  intros m A n B j (HA & Hn & H) HB Hj HBj. split; [lia|]. split; [lia|].
  intros i Hi. replace (B + i) with (A + (B - A + i)) by lia. apply H. lia.
Qed.

Lemma u8_wr : forall m A bs, u8arr rsegs m A bs -> wr_at rsegs m A (Z.of_nat (length bs)).
Proof. intros m A bs [_ H]. exact H. Qed.

Lemma next_blk : reac_headamp_tx_next_contract -> forall (S t lo : Z) (T T' : list byte) (r c p v : Z) (bs : list byte)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  sp = Z_to_bv 64 S -> s0 = Z_to_bv 64 t -> s7 = Z_to_bv 64 (-1) ->
  next_model T t = (r, (c, p, v), T') ->
  0 <= lo -> lo + 48 <= S -> S + 66 < 2 ^ 63 -> 0 < t -> t mod 4 = 0 -> t + 460 < 2 ^ 63 ->
  (t + 460 <= lo \/ S + 66 <= t) ->
  length T = 460%nat -> length T' = 460%nat -> 0 <= s32 T 440 ->
  (r = 1 -> 0 <= c < 256 /\ 0 <= p < 256 /\ 0 <= v < 256) ->
  rw_cells rsegs m t [CB 460 T] -> rw_cells rsegs m (S + 63) [CB 3 bs] -> stk rsegs m lo S -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte) (bs' : list byte),
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13bb4) fc None m' (seg_rom rsegs) /\
      munch [(lo, S); (t, t + 460); (S + 63, S + 66)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo S /\
      rw_cells rsegs m' t [CB 460 T'] /\ rw_cells rsegs m' (S + 63) [CB 3 bs'] /\
      (r = 1 -> bs' = [Z_to_bv 8 v; Z_to_bv 8 p; Z_to_bv 8 c]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b94) fc None m (seg_rom rsegs)).
Proof.
  intros NXT S t lo T T' r c p v bs ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m -> -> -> EN Hlo HloS HS1 Ht0 Ht4 Ht1 Hdis HTl HTl' H440 Hrng HT HB HSK HMI.
  destruct (CB_bytes _ _ _ _ HT) as (HTB & HTW & _). clear HT.
  destruct (cb_u8 _ _ _ _ HB) as [U HBl]. clear HB.
  assert (MU : munch [(lo, S); (t, t + 460); (S + 63, S + 66)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  set (bf := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-1)))).
  assert (HS : store_ok rsegs m (wa (S + 63 + 2)) 1 = true)
    by (apply (u8arr_store_ok _ _ _ _ 2 _ U); [rewrite HBl; lia | reflexivity]).
  zstep.
  replace (wa (S + 65)) with (wa (S + 63 + 2)) by (f_equal; lia).
  rewrite le1_one. fold bf.
  pose proof (u8arr_write _ _ _ _ 2 bf U ltac:(rewrite HBl; lia)) as U1. clear U.
  transport_chunks rsegs m (S + 63 + 2) [bf].
  footprint_after_store rsegs m (S + 63 + 2) [bf].
  apply (mem_inv_store rsegs m (wa (S + 63 + 2)) [bf]) in HMI; [|exact HS]. clear HS.
  set (m1 := write_to_mem m (wa (S + 63 + 2)) [bf]) in *.
  assert (HS : store_ok rsegs m1 (wa (S + 63 + 1)) 1 = true)
    by (apply (u8arr_store_ok _ _ _ _ 1 _ U1); [rewrite upd_length, HBl; lia | reflexivity]).
  zstep.
  replace (wa (S + 64)) with (wa (S + 63 + 1)) by (f_equal; lia).
  rewrite le1_one. fold bf.
  pose proof (u8arr_write _ _ _ _ 1 bf U1 ltac:(rewrite upd_length, HBl; lia)) as U2. clear U1.
  transport_chunks rsegs m1 (S + 63 + 1) [bf].
  footprint_after_store rsegs m1 (S + 63 + 1) [bf].
  apply (mem_inv_store rsegs m1 (wa (S + 63 + 1)) [bf]) in HMI; [|exact HS]. clear HS.
  set (m2 := write_to_mem m1 (wa (S + 63 + 1)) [bf]) in *.
  assert (HS : store_ok rsegs m2 (wa (S + 63 + 0)) 1 = true)
    by (apply (u8arr_store_ok _ _ _ _ 0 _ U2); [rewrite !upd_length, HBl; lia | reflexivity]).
  zstep.
  replace (wa (S + 63)) with (wa (S + 63 + 0)) by (f_equal; lia).
  rewrite le1_one. fold bf.
  pose proof (u8arr_write _ _ _ _ 0 bf U2 ltac:(rewrite !upd_length, HBl; lia)) as U3. clear U2.
  transport_chunks rsegs m2 (S + 63 + 0) [bf].
  footprint_after_store rsegs m2 (S + 63 + 0) [bf].
  apply (mem_inv_store rsegs m2 (wa (S + 63 + 0)) [bf]) in HMI; [|exact HS]. clear HS.
  set (m3 := write_to_mem m2 (wa (S + 63 + 0)) [bf]) in *.
  set (bs3 := upd (upd (upd bs (Z.to_nat 2) bf) (Z.to_nat 1) bf) (Z.to_nat 0) bf) in *.
  assert (Hl3 : length bs3 = 3%nat) by (unfold bs3; rewrite !upd_length; exact HBl).
  pose proof (u8_wr _ _ _ U3) as W3. rewrite Hl3 in W3.
  zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply NXT with (lo := lo) (t := t) (chp := S + 65) (parp := S + 64) (valp := S + 63) (T := T);
      first [ reflexivity | exact Ht4 | exact HTl | exact HTB | exact HTW | exact HMI
            | (apply (wr_sub _ _ _ _ _ W3); lia)
            | (intros _; exact H440)
            | (rewrite ?unsigned_lit by lia; unfold REAC_HEADAMP_TX_NEXT_FRAME; first [exact HSK | lia]) ]. }
  intros ms' Hpost. rewrite EN in Hpost. cbv beta iota delta [next_post] in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                     HTB' & WM' & HSK' & HMI' & Hm).
  rewrite (unsigned_lit S) in HSK', Hm by lia.
  unfold REAC_HEADAMP_TX_NEXT_FRAME in Hm.
  rewrite (ret_pc_even 80820) by (first [lia | reflexivity]).
  apply evt_done.
  assert (HT' : rw_cells rsegs m' t [CB 460 T'])
    by (apply rw_cells_CB; [exact HTl' | exact HTB' | exact (wr_at_transport _ _ _ _ _ HTW WM')]).
  pose proof (wr_at_transport _ _ _ _ _ W3 WM') as W3'.
  revert Hm. destruct (Z.eqb_spec r 1) as [E1 | E1]; intros Hm.
  - destruct Hm as (MU' & Bc & Bp & Bv).
    destruct (Hrng E1) as (Rc & Rp & Rv).
    rewrite (le1_small c Rc) in Bc. rewrite (le1_small p Rp) in Bp. rewrite (le1_small v Rv) in Bv.
    assert (MU2 : munch [(lo, S); (t, t + 460); (S + 63, S + 66)] m3 m').
    { eapply munch_weaken; [|exact MU']. unfold sub_fp. cbn [outside]. intros y Hy. lia. }
    assert (HB3 : bytes_at rsegs m' (S + 63) [Z_to_bv 8 v; Z_to_bv 8 p; Z_to_bv 8 c]).
    { apply (proj2 (bytes_at_app rsegs m' (S + 63) [Z_to_bv 8 v] [Z_to_bv 8 p; Z_to_bv 8 c])).
      split; [exact Bv|]. cbn [length].
      apply (proj2 (bytes_at_app rsegs m' (S + 63 + Z.of_nat 1) [Z_to_bv 8 p] [Z_to_bv 8 c])).
      cbn [length]. replace (S + 63 + Z.of_nat 1) with (S + 64) by lia.
      replace (S + 64 + Z.of_nat 1) with (S + 65) by lia. split; assumption. }
    exists (Z_to_bv 64 80820), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m',
      [Z_to_bv 8 v; Z_to_bv 8 p; Z_to_bv 8 c].
    split; [subst r; reflexivity|].
    split; [exact (munch_trans _ _ _ _ MU MU2)|].
    split; [exact (wmono_trans _ _ _ _ WM WM')|].
    split; [exact HMI'|].
    split; [exact HSK'|].
    split; [exact HT'|].
    split; [apply rw_cells_CB; [reflexivity | exact HB3 | exact W3'] | intros _; reflexivity].
  - assert (MU2 : munch [(lo, S); (t, t + 460); (S + 63, S + 66)] m3 m').
    { eapply munch_weaken; [|exact Hm]. unfold sub_fp. cbn [outside]. intros y Hy. lia. }
    assert (U' : u8arr rsegs m' (S + 63) bs3).
    { apply (u8arr_transport rsegs [(S - 48, S); (t, t + 460)] m3 m' _ _ U3 Hm WM'). cbn [disjoint_from]. rewrite Hl3. lia. }
    exists (Z_to_bv 64 80820), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', bs3.
    split; [reflexivity|].
    split; [exact (munch_trans _ _ _ _ MU MU2)|].
    split; [exact (wmono_trans _ _ _ _ WM WM')|].
    split; [exact HMI'|].
    split; [exact HSK'|].
    split; [exact HT'|].
    split; [exact (u8_cb _ _ _ _ U' Hl3) | intros E; contradiction].
Qed.

Lemma frames_range : forall pl, 0 <= frames pl < 4097.
Proof.
  intros pl. unfold frames, sched_rd.
  destruct (rd8 pl (pos_raw pl)) as [sb p1]. cbv beta iota zeta.
  destruct (rd8 pl p1) as [sw p2]. cbv beta iota zeta.
  destruct (rd32 pl p2) as [per p3]. cbv beta iota zeta.
  destruct (rd16 pl p3) as [f p4]. cbv beta iota zeta.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma sched_flag_spec : forall pl sb sw per fr p4, sched_rd pl = (sb, sw, per, fr, p4) ->
  (sw <> 0 -> sb < 48 -> sched_flag pl = 1) /\ 0 <= sched_flag pl <= 1.
Proof.
  intros pl sb sw per fr p4 E. unfold sched_flag. rewrite E. cbv beta iota zeta.
  destruct (Z.eqb_spec sw 0); destruct (Z.ltb_spec sb 48); cbn [negb andb]; lia.
Qed.

Lemma tailT : forall x t i ms0 sb sw per fr p4 T' us'
  (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word) m,
  sched_rd (x_pl x) = (sb, sw, per, fr, p4) -> sched_at (x_pl x) t (S i) = (T', us') ->
  x_n x < 2 ^ 26 -> Z.of_nat i < frames (x_pl x) ->
  rw_cells rsegs m (x_p x) [CB (length (x_pl x)) (x_pl x)] ->
  stk rsegs m (x_S x - LLVM_STACK) (x_S x) -> mem_inv rsegs m ->
  bytes_at rsegs m CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES -> CTRL_HEADAMP_ROW + 24 <= x_S x - LLVM_STACK ->
  (x_p x + x_n x <= CTRL_HEADAMP_ROW \/ CTRL_HEADAMP_ROW + 24 <= x_p x) ->
  rw_cells rsegs m (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x])) ->
  rw_cells rsegs m t [CB 460 T'] -> I1 T' -> length T' = 460%nat ->
  length us' = 144%nat -> rw_cells rsegs m (SPL x + 66) [CB 144 us'] ->
  rw_cells rsegs m (SPL x + 48) [C8 (Z_to_bv 64 (wnot (SPL x + 66)))] ->
  rw_cells rsegs m (SPL x + 360) [CB 144 (ws_end (x_pl x))] ->
  rw_cells rsegs m (SPL x + 216) [CB 144 (st_end (x_pl x))] ->
  length (ws_end (x_pl x)) = 144%nat -> length (st_end (x_pl x)) = 144%nat ->
  Hrel (T_end (x_pl x)) (ws_end (x_pl x)) (st_end (x_pl x)) ->
  x_S x mod 16 = 0 -> length (x_sv x) = 12%nat -> x_S x < 2 ^ 63 ->
  0 < x_p x -> x_p x + x_n x < 2 ^ 63 -> (x_p x + x_n x <= x_S x - LLVM_STACK \/ x_S x <= x_p x) ->
  blk x t 460 -> t mod 16 = 0 ->
  munch ((x_S x - LLVM_STACK, x_S x) :: [(t, t + 460)]) (ms_mem ms0) m -> wmono rsegs (ms_mem ms0) m ->
  evt rsegs (fun ms' => kept x [(t, t + 460)] ms0 ms' /\
    ((Z.of_nat (S i) < frames (x_pl x) /\ At_sched x t (S i) ms') \/
     (Z.of_nat (S i) = frames (x_pl x) /\ At_freeT x t ms')))
    (MS (mkR ra (Z_to_bv 64 (SPL x)) (x_gp x) (x_tp x) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 sb) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (sb + sw)) (Z_to_bv 64 (wnot (SPL x + 360))) s4 (Z_to_bv 64 (sched_flag (x_pl x)))
             (Z_to_bv 64 (Z.of_nat i - frames (x_pl x))) (Z_to_bv 64 (-1))
             (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 47) (Z_to_bv 64 3) t3 t4 t5 t6)
        (x_F x) (Z_to_bv 64 0x13cc0) (x_fc x) None m (seg_rom rsegs)).
Proof.
  intros x t i ms0 sb sw per fr p4 T' us' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 m
    ESR ESA Hn Hi HP HS HMI Hrow Hrs Hrp HSV HT HI1 HTl Hul HUS HC48 HWS HST Hwl Hstl HH HS16 Hsv12 HS63 Hp0 Hpn Hpd
    HBLK Ht16 MU WM.
  pose proof (frames_range (x_pl x)) as HFR.
  zstep.
  rewrite swrap32_mod64, (swrap32_id (Z.of_nat i - frames (x_pl x) + 1)) by lia.
  replace (Z.of_nat i - frames (x_pl x) + 1) with (Z.of_nat (S i) - frames (x_pl x)) by lia.
  zstep. if_cases HC; zify_cond HC.
  - apply evt_done. split; [split; cbn [ms_mem MS]; assumption|].
    left. split; [lia|].
    unfold At_sched, body, common, table, arrays. rewrite ESR, ESA. cbv beta iota.
    cbn [ms_mem ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom MS].
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try assumption; try lia.
  - apply evt_done. split; [split; cbn [ms_mem MS]; assumption|].
    right. split; [lia|].
    unfold At_freeT, body, common.
    cbn [ms_mem ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom MS].
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try assumption; try lia.
Qed.

Lemma shl1 : forall c, Z.shiftl c 1 = 2 * c.
Proof. intros c. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Ltac fix_ret :=
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] => rewrite (ret_pc_even n) by (first [lia | reflexivity]) end.

Ltac tbr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?C then _ else _) _ _ _ _) =>
      first [ if_true | if_false
            | (let HC := fresh "HC" in destruct C eqn:HC; zify_cond HC; try (exfalso; lia)) ]
  end.

Ltac callE EFF HTl HTB HT4 :=
  eapply evt_cut;
  [ eapply EFF; [reflexivity | reflexivity | reflexivity | lia | lia | right; split; [exact HTl | split; [exact HTB | exact HT4]]]
  | let ms' := fresh "ms" in
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->); fix_ret ].

Ltac callD DFL :=
  eapply evt_cut;
  [ eapply DFL; [reflexivity | lia]
  | let ms' := fresh "ms" in
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->); fix_ret ].

Ltac tdrv EFF DFL HTl HTB HT4 rw :=
  repeat (rw;
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 81088) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 81108) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 81184) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 81548) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 87448) _ _ _ _) => callE EFF HTl HTB HT4
    | |- evt _ _ (MS _ _ (Z_to_bv 64 87432) _ _ _ _) => callD DFL
    | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 _)) _ _ _ _) => fix_ret
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => tbr
    | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep
    end).

Lemma mid1 : reac_headamp_tx_effective_contract -> reac_headamp_default_contract ->
  forall (S t c p v sb sw fl : Z) (T : list byte) (bw bst bu : byte)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  sp = Z_to_bv 64 S -> s0 = Z_to_bv 64 t -> a0 = Z_to_bv 64 1 ->
  s1 = Z_to_bv 64 sb -> s2 = Z_to_bv 64 (sb + sw) -> s3 = Z_to_bv 64 (wnot (S + 360)) -> s5 = Z_to_bv 64 fl ->
  s8 = Z_to_bv 64 2 -> s9 = Z_to_bv 64 1 -> s10 = Z_to_bv 64 47 -> s11 = Z_to_bv 64 3 ->
  0 <= S -> S + 600 < 2 ^ 63 -> 0 < t -> t mod 4 = 0 -> 0 <= sb < 256 -> 0 <= sw < 256 ->
  0 <= c < 48 -> 0 <= p < 3 -> legal p v -> v = eff T t c p -> length T = 460%nat -> bytes_at rsegs m t T ->
  rw_cells rsegs m (S + 48) [C8 (Z_to_bv 64 (wnot (S + 66)))] ->
  ov_read_bytes rsegs m (wa (S + 63)) 1 = Some [Z_to_bv 8 v] ->
  ov_read_bytes rsegs m (wa (S + 64)) 1 = Some [Z_to_bv 8 p] ->
  ov_read_bytes rsegs m (wa (S + 65)) 1 = Some [Z_to_bv 8 c] ->
  ov_read_bytes rsegs m (wa (S + 360 + (3 * c + p))) 1 = Some [bw] ->
  ov_read_bytes rsegs m (wa (S + 216 + (3 * c + p))) 1 = Some [bst] ->
  ov_read_bytes rsegs m (wa (S + 66 + (3 * c + p))) 1 = Some [bu] ->
  store_ok rsegs m (wa (S + 66 + (3 * c + p))) 1 = true ->
  (bv_unsigned bw <> 0 -> v = bv_unsigned bst) ->
  (bv_unsigned bw = 0 -> v = dflt p /\ fl = 1 /\ sb <= c < sb + sw /\ bv_unsigned bu = 0) ->
  evt rsegs (fun ms' => exists (ra' t0' t1' t2' s4' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13cc0) fc None
               (if bv_unsigned bw =? 0 then write_to_mem m (wa (S + 66 + (3 * c + p))) [Z_to_bv 8 1] else m)
               (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13bb4) fc None m (seg_rom rsegs)).
Proof.
  intros EFF DFL S t c p v sb sw fl T bw bst bu ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
    s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m -> -> -> -> -> -> -> -> -> -> -> HS0 HS1 Ht0 HT4 Hsb Hsw Hc Hp Hlg Hv HTl HTB
    HC48 RDv RDp RDc RDw RDs RDu HSU Hwnz Hwz.
  unfold legal in Hlg. unfold wnot in *.
  pose proof (byte_range bw) as Rw. pose proof (byte_range bst) as Rs. pose proof (byte_range bu) as Ru.
  assert (Ec : bv_unsigned (Z_to_bv 8 c) = c) by (apply byte_small; lia).
  assert (Ep : bv_unsigned (Z_to_bv 8 p) = p) by (apply byte_small; lia).
  assert (Ev : bv_unsigned (Z_to_bv 8 v) = v) by (apply byte_small; lia).
  destruct (Z.eq_dec (bv_unsigned bw) 0) as [W0 | W1].
  - destruct (Hwz W0) as (Hdv & -> & Hcr & Hu0). clear Hwz Hwnz.
    rewrite W0. cbn [Z.eqb].
    tdrv EFF DFL HTl HTB HT4 ltac:(rewrite ?Ec, ?Ep, ?Ev, ?Hu0, ?shl1; rewrite ?zb_lxor_ones by lia).
    all: rewrite (le1_small 1) by lia; apply evt_done; do 17 eexists; reflexivity.
  - pose proof (Hwnz W1) as Hsv. clear Hwz Hwnz.
    rewrite (proj2 (Z.eqb_neq _ 0) W1).
    tdrv EFF DFL HTl HTB HT4 ltac:(rewrite ?Ec, ?Ep, ?Ev, ?shl1; rewrite ?zb_lxor_ones by lia).
    all: apply evt_done; do 17 eexists; reflexivity.
Qed.

Lemma rd3 : forall m A b0 b1 b2, rw_cells rsegs m A [CB 3 [b0; b1; b2]] ->
  ov_read_bytes rsegs m (wa (A + 0)) 1 = Some [b0] /\ ov_read_bytes rsegs m (wa (A + 1)) 1 = Some [b1] /\
  ov_read_bytes rsegs m (wa (A + 2)) 1 = Some [b2].
Proof.
  intros m A b0 b1 b2 H. destruct (CB_bytes _ _ _ _ H) as (HB & _ & _).
  split; [|split]; rewrite (bytes_at_read rsegs m A _ _ 1 HB) by (cbn; lia); reflexivity.
Qed.

Lemma arr_rd : forall m A n bs k, rw_cells rsegs m A [CB n bs] -> 0 <= k < Z.of_nat n ->
  ov_read_bytes rsegs m (wa (A + k)) 1 = Some [nth (Z.to_nat k) bs (Z_to_bv 8 0)].
Proof.
  intros m A n bs k H Hk. destruct (CB_bytes _ _ _ _ H) as (HB & _ & HL).
  rewrite (bytes_at_read rsegs m A bs k 1 HB) by lia.
  rewrite (firstn1_skipn_nth bs _ (Z_to_bv 8 0)) by lia. reflexivity.
Qed.

Lemma us_step_ws : forall ws us c p v, tb ws (3 * c + p) <> 0 -> us_step ws us 1 (c, p, v) = us.
Proof. intros ws us c p v H. unfold us_step. rewrite (proj2 (Z.eqb_neq _ 0) H), !andb_false_r. reflexivity. Qed.

Lemma us_step_put : forall ws us c p v, 0 <= c < 48 -> 0 <= p < 3 -> tb ws (3 * c + p) = 0 ->
  tb us (3 * c + p) = 0 -> us_step ws us 1 (c, p, v) = ws_put us c p 1.
Proof.
  intros ws us c p v Hc Hp Hw Hu. unfold us_step. rewrite Hw, Hu.
  rewrite (proj2 (Z.ltb_lt c 48)), (proj2 (Z.ltb_lt p 3)) by lia. reflexivity.
Qed.

Lemma upd_upd_bytes : forall (l : list byte) i b, (i < length l)%nat -> upd l i b = upd_bytes l i [b].
Proof.
  intros l i b H. rewrite upd_firstn_skipn by exact H. unfold upd_bytes. cbn [length app].
  replace (i + 1)%nat with (S i) by lia. reflexivity.
Qed.

Theorem seg_sched_turn_holds : reac_headamp_tx_next_contract -> reac_headamp_tx_effective_contract ->
  reac_headamp_default_contract -> seg_sched_turn.
Proof.
  intros NXT EFF DFL. unfold seg_sched_turn. intros x t i ms H.
  apply evt_canon; [eqv_inv_tac|].
  destruct H as (((Hpc & HF & Hfc & Hrv & Hsvc & Hro & Hgp & Htp & HPL & HST & HMI & Hp0 & Hpn & Hpd & Hrow & Hrs & Hrp) &
                  Hsp & HSV & HS16 & Hsv12 & HS63) &
                 Hn & Hi & Hs0 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10 & Hs11 & Hs3 & Hs5 & HC48 & HSB & HTU &
                 (Hwl & Hstl & HWS & HSTA) & HHr).
  revert HSB HTU.
  destruct (sched_rd (x_pl x)) as [[[[sb sw] per] fr] p4] eqn:ESR.
  destruct (sched_at (x_pl x) t i) as [T us] eqn:ESA.
  intros (Hs1 & Hs2) ((HTb & HT16 & HTl & HT) & HI1 & Hul & HUS).
  pose proof HTb as HTb'. unfold blk in HTb'.
  pose proof (frame_ok (x_pl x) t i ltac:(lia)) as FO. rewrite ESR, ESA in FO. cbv beta iota in FO.
  destruct (next_model T t) as [[r [[c p] v]] T'] eqn:EN.
  destruct FO as (_ & _ & H440 & HTl' & HI1' & ES & Hr & Hr1).
  destruct (sched_flag_spec _ _ _ _ _ _ ESR) as (HFL1 & HFL0).
  pose proof (frames_range (x_pl x)) as HFR.
  assert (HRNG : r = 1 -> 0 <= c < 256 /\ 0 <= p < 256 /\ 0 <= v < 256)
    by (intros E1; destruct (Hr1 E1) as (Hc & Hp & Hlg & _); unfold legal in Hlg; lia).
  rewrite canon_rg by exact Hsvc.
  rewrite Hpc, HF, Hfc, Hrv, Hro, Hs0, Hs1, Hs2, Hs3, Hs5, Hs6, Hs7, Hs8, Hs9, Hs10, Hs11, Hsp, Hgp, Htp.
  unfold w64, PC_SCHED.
  unfold w64 in HC48.
  set (m00 := ms_mem ms) in *.
  assert (ELS : LLVM_STACK = 8800) by reflexivity.
  assert (ELR : length CTRL_HEADAMP_BYTES = 24%nat) by reflexivity.
  assert (ESPL : SPL x = x_S x - 608) by reflexivity.
  assert (Exn : x_n x = Z.of_nat (length (x_pl x))) by reflexivity.
  assert (Ht4 : t mod 4 = 0) by (Z.div_mod_to_equations; lia).
  remember (map C8 (rev (x_sv x) ++ [x_ra x])) as SVC eqn:ESVC.
  assert (HSVC : cells_size SVC = 104%nat)
    by (subst SVC; rewrite cells_size_C8, length_app, length_rev, Hsv12; reflexivity).
  pose proof HST as (HS0 & HS0' & _).
  assert (MU : munch [(x_S x - LLVM_STACK, x_S x); (t, t + 460)] m00 m00) by apply munch_refl.
  assert (WM : wmono rsegs m00 m00) by apply wmono_refl.
  destruct (stk_split rsegs m00 (x_S x - LLVM_STACK) (SPL x) (x_S x) HST ltac:(lia)) as [HSlo HShi]. clear HST.
  destruct (stk_split3 m00 _ _ (SPL x + 63) 3 HShi ltac:(lia) ltac:(lia)) as (HS1 & (junk & HJ) & HS2). clear HShi.
  call (next_blk NXT (SPL x) t (x_S x - LLVM_STACK) T T' r c p v junk).
  1-3: reflexivity. exact EN. 1-4: lia. exact Ht4. 1-2: lia. exact HTl. exact HTl'. exact H440. exact HRNG.
  exact HT. exact HJ. exact HSlo. exact HMI.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end.
  match goal with H : stk rsegs m1 (x_S x - LLVM_STACK) (SPL x) |- _ => rename H into HSlo' end.
  match goal with H : rw_cells rsegs m1 (SPL x + 63) [CB 3 ?b] |- _ => rename H into HB3 end.
  match goal with H : rw_cells rsegs m1 t [CB 460 T'] |- _ => rename H into HT' end.
  pose proof (stk_merge3 _ _ _ _ _ _ _ HS1 HB3 HS2 ltac:(lia) ltac:(lia) ltac:(lia)) as HShi.
  pose proof (stk_merge rsegs _ _ _ _ HSlo' HShi ltac:(lia)) as HST.
  clear HS1 HS2 HSlo' HShi.
  destruct Hr as [-> | ->].
  - clear HB3 POST.
    tdrv EFF DFL HTl' HTl' Ht4 idtac.
    rewrite us_step_0 in ES. subst SVC.
    eapply (tailT x t i ms sb sw per fr p4 T' us); eassumption.
  - specialize (POST eq_refl). match type of POST with ?b = _ => subst b end.
    destruct (Hr1 eq_refl) as (Hc & Hp & Hlg & Hv & Hwnz & Hwz). clear Hr1 HRNG.
    pose proof (sched_rd_range (x_pl x)) as SRR. rewrite ESR in SRR.
    destruct (rd3 _ _ _ _ _ HB3) as (RDv & RDp & RDc).
    replace (SPL x + 63 + 0) with (SPL x + 63) in RDv by lia.
    replace (SPL x + 63 + 1) with (SPL x + 64) in RDp by lia.
    replace (SPL x + 63 + 2) with (SPL x + 65) in RDc by lia.
    destruct (CB_bytes _ _ _ _ HT') as (HTB' & _ & _).
    pose proof (arr_rd m1 (SPL x + 360) 144 (ws_end (x_pl x)) (3 * c + p) HWS ltac:(lia)) as RDw.
    pose proof (arr_rd m1 (SPL x + 216) 144 (st_end (x_pl x)) (3 * c + p) HSTA ltac:(lia)) as RDs.
    pose proof (arr_rd m1 (SPL x + 66) 144 us (3 * c + p) HUS ltac:(lia)) as RDu.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ HUS) as UU.
    assert (HSU : store_ok rsegs m1 (wa (SPL x + 66 + (3 * c + p))) 1 = true)
      by (apply (u8arr_store_ok _ _ _ _ (3 * c + p) _ UU); [rewrite Hul; lia | reflexivity]).
    set (bw := nth (Z.to_nat (3 * c + p)) (ws_end (x_pl x)) (Z_to_bv 8 0)) in *.
    set (bst := nth (Z.to_nat (3 * c + p)) (st_end (x_pl x)) (Z_to_bv 8 0)) in *.
    set (bu := nth (Z.to_nat (3 * c + p)) us (Z_to_bv 8 0)) in *.
    change (tb (ws_end (x_pl x)) (3 * c + p)) with (bv_unsigned bw) in *.
    change (tb (st_end (x_pl x)) (3 * c + p)) with (bv_unsigned bst) in *.
    change (tb us (3 * c + p)) with (bv_unsigned bu) in *.
    assert (Hwz' : bv_unsigned bw = 0 -> v = dflt p /\ sched_flag (x_pl x) = 1 /\ sb <= c < sb + sw /\
                   bv_unsigned bu = 0)
      by (intros W; destruct (Hwz W) as (A1 & A2 & A3 & A4 & A5); split; [exact A1|];
          split; [exact (HFL1 A2 A3)|]; split; [exact A4 | exact A5]).
    eapply evt_cut.
    { eapply (mid1 EFF DFL (SPL x) t c p v sb sw (sched_flag (x_pl x)) T' bw bst bu).
      1-11: reflexivity. 1-3: lia. exact Ht4. 1-4: lia. exact Hlg. exact Hv. exact HTl'. exact HTB'. exact HC48.
      exact RDv. exact RDp. exact RDc. exact RDw. exact RDs. exact RDu. exact HSU. exact Hwnz. exact Hwz'. }
    intros ms1 (ra1 & t01 & t11 & t21 & s41 & a01 & a11 & a21 & a31 & a41 & a51 & a61 & a71 & t31 & t41 & t51 &
                t61 & ->).
    clear RDv RDp RDc RDw RDs RDu HTB'.
    destruct (Z.eq_dec (bv_unsigned bw) 0) as [W0 | W1].
    + rewrite W0. cbn [Z.eqb].
      destruct (Hwz W0) as (_ & _ & _ & _ & Hu0).
      pose proof (u8arr_write _ _ _ _ (3 * c + p) (Z_to_bv 8 1) UU ltac:(rewrite Hul; lia)) as UU'.
      clear HUS UU.
      transport_chunks rsegs m1 (SPL x + 66 + (3 * c + p)) [Z_to_bv 8 1].
      footprint_after_store rsegs m1 (SPL x + 66 + (3 * c + p)) [Z_to_bv 8 1].
      apply (mem_inv_store rsegs m1 (wa (SPL x + 66 + (3 * c + p))) [Z_to_bv 8 1]) in MI; [|exact HSU].
      set (m2 := write_to_mem m1 (wa (SPL x + 66 + (3 * c + p))) [Z_to_bv 8 1]) in *.
      apply rw_cells_of_u8arr in UU'. rewrite upd_length, Hul, upd_upd_bytes in UU' by lia.
      change (upd_bytes us (Z.to_nat (3 * c + p)) [Z_to_bv 8 1]) with (ws_put us c p 1) in UU'.
      rewrite (us_step_put _ _ _ _ _ Hc Hp W0 Hu0) in ES. subst SVC.
      eapply (tailT x t i ms sb sw per fr p4 T' (ws_put us c p 1)); try eassumption.
      apply len_ws_put; [exact Hul | lia | lia].
    + rewrite (proj2 (Z.eqb_neq _ 0) W1).
      rewrite (us_step_ws _ _ _ _ _ W1) in ES. subst SVC.
      eapply (tailT x t i ms sb sw per fr p4 T' us); eassumption.
Qed.
