From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel RgLemmas
  memcpy_c memset_c reac_ctrl_stamp_headamp_c.
Import ListNotations.
Open Scope Z_scope.

Lemma legal_legalb : forall p v, legal p v -> legalb p v = true.
Proof.
  intros p v H. unfold legal in H. unfold legalb.
  destruct H as [[Hp Hv] | [Hp Hv]].
  - rewrite (proj2 (Z.ltb_lt p 2)), (proj2 (Z.leb_le v 1)) by lia. reflexivity.
  - subst p. rewrite (proj2 (Z.leb_le v 55)) by lia. rewrite orb_true_r. reflexivity.
Qed.

Lemma nth_read1 : forall m A (bs : list byte) j,
  bytes_at rsegs m A bs -> (j < length bs)%nat ->
  ov_read_bytes rsegs m (wa (A + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros m A bs j H Hj.
  rewrite (bytes_at_read rsegs m A bs (Z.of_nat j) 1 H) by lia.
  rewrite Nat2Z.id. f_equal.
  clear H. revert j Hj. induction bs as [|b bs IH]; intros j Hj; cbn in Hj; [lia|].
  destruct j as [|j]; cbn; [reflexivity|]. apply IH. lia.
Qed.

Lemma turnA : memcpy_contract -> memset_contract -> reac_ctrl_stamp_headamp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (spo vv : word)
         (base p lo k r n : Z) (vl x1 dn rs : list byte) (cs0 csS : list cell),
    sp = Z_to_bv 64 (bv_unsigned spo + -1616) ->
    s1 = Z_to_bv 64 base -> s4 = Z_to_bv 64 p ->
    s5 = Z_to_bv 64 (bv_unsigned spo + -1580) ->
    0 <= base < 256 -> 0 <= p < 3 -> 0 <= k -> 1 <= r -> k + r = n ->
    bv_unsigned s6 = bv_unsigned s2 + 34 * k ->
    bv_unsigned s9 = bv_unsigned vv + p ->
    (Z.to_nat p < length vl)%nat ->
    legal p (vz vl (Z.to_nat p)) ->
    lo + 1888 <= bv_unsigned spo -> 0 <= lo -> bv_unsigned spo mod 16 = 0 ->
    bytes_at rsegs m (bv_unsigned vv) vl ->
    rw_cells rsegs m (bv_unsigned spo + -1616) cs0 -> cells_size cs0 = 20%nat ->
    rw_cells rsegs m (bv_unsigned spo + -1596) [CB 1492 x1] ->
    rw_cells rsegs m (bv_unsigned spo + -104) csS -> cells_size csS = 104%nat ->
    rw_cells rsegs m (bv_unsigned s2) [CB (Z.to_nat (34 * k)) dn] ->
    rw_cells rsegs m (bv_unsigned s2 + 34 * k) [CB (Z.to_nat (34 * r)) rs] ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned spo + -1616) ->
    (bv_unsigned s2 + 34 * n <= lo \/ bv_unsigned spo <= bv_unsigned s2) ->
    (bv_unsigned vv + Z.of_nat (length vl) <= lo \/ bv_unsigned spo <= bv_unsigned vv) ->
    (bv_unsigned vv + Z.of_nat (length vl) <= bv_unsigned s2 \/ bv_unsigned s2 + 34 * n <= bv_unsigned vv) ->
    munch [(bv_unsigned spo - 1888, bv_unsigned spo); (bv_unsigned s2, bv_unsigned s2 + 34 * n)] m0 m ->
    wmono rsegs m0 m ->
    bytes_at rsegs m0 CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned spo - 1888 \/ bv_unsigned spo <= CTRL_ROW) ->
    (bv_unsigned s2 + 34 * n <= CTRL_ROW \/ CTRL_ROW + 24 <= bv_unsigned s2) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (x1' : list byte),
         ms' = MS (mkR (Z_to_bv 64 0x1403c) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7' s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x1403c) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' (bv_unsigned vv) vl /\
         rw_cells rsegs m' (bv_unsigned spo + -1616) cs0 /\
         rw_cells rsegs m' (bv_unsigned spo + -1596) [CB 1492 x1'] /\
         rw_cells rsegs m' (bv_unsigned spo + -104) csS /\
         rw_cells rsegs m' (bv_unsigned s2) [CB (Z.to_nat (34 * (k + 1))) (dn ++ GA base p (vz vl (Z.to_nat p)))] /\
         rw_cells rsegs m' (bv_unsigned s2 + 34 * (k + 1)) [CB (Z.to_nat (34 * (r - 1))) (skipn 34 rs)] /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned spo + -1616) /\
         munch [(bv_unsigned spo - 1888, bv_unsigned spo); (bv_unsigned s2, bv_unsigned s2 + 34 * n)] m0 m' /\
         wmono rsegs m0 m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14000) fc None m (seg_rom rsegs)).
Proof.
  intros MEMC MEMS STAMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m0 spo vv base p lo k r n vl x1 dn rs cs0 csS
    -> -> -> -> HB HP Hk Hr Hn H6 H9 Hj HLEG LO Hlo HM16 HV FR0 Hcs0 SCR FRS HcsS DONE REST HMI ST D1 D2 D3 MU WM
    HROW HROWD HROWR.
  pose proof (bv_unsigned_in_range 64 spo) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 s2) as Rs2. unfold bv_modulus in Rs2.
  pose proof (bv_unsigned_in_range 64 vv) as Rvv. unfold bv_modulus in Rvv.
  pose proof (rw_cells_bound rsegs m _ _ REST) as BR. cbn [cells_size csize] in BR.
  rewrite Nat.add_0_r, Z2Nat.id in BR by lia.
  replace (34 * r) with (34 + 34 * (r - 1)) in REST by lia.
  apply rw_cells_cb_split in REST; [|lia|lia]. destruct REST as [R1 R2].
  assert (RD : ov_read_bytes rsegs m s9 1 = Some [nth (Z.to_nat p) vl (Z_to_bv 8 0)]).
  { rewrite <- (Z_to_bv_bv_unsigned s9). rewrite H9.
    replace (bv_unsigned vv + p) with (bv_unsigned vv + Z.of_nat (Z.to_nat p)) by lia.
    apply nth_read1; assumption. }
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat p) vl (Z_to_bv 8 0))) as Rv. unfold bv_modulus in Rv.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1616)) = bv_unsigned spo + -1616)
    by (rewrite unsigned_lit by lia; lia).
  assert (USCR : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1596)) = bv_unsigned spo + -1596)
    by (rewrite unsigned_lit by lia; lia).
  assert (US5 : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1580)) = bv_unsigned spo + -1580)
    by (rewrite unsigned_lit by lia; lia).
  assert (U1492 : bv_unsigned (Z_to_bv 64 1492) = 1492) by reflexivity.
  assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
  assert (USTK : REAC_CTRL_STAMP_HEADAMP_STACK = 272) by reflexivity.
  zstep.
  zstep. zstep. zstep. zstep.
  call MEMS.
  { rewrite USCR. exact SCR. }
  { exact HMI. }
  match goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1596))) _ |- _ =>
    rewrite USCR in H; rename H into SZ end.
  match type of SZ with rw_cells ?s ?mm ?A [CB _ ?bs] =>
    change (rw_cells s mm A [CB (Z.to_nat (16 + 1476)) bs]) in SZ end.
  apply rw_cells_cb_split in SZ; [|lia|lia]. destruct SZ as [S1 SZ].
  match type of SZ with rw_cells ?s ?mm ?A [CB _ ?bs] =>
    change (rw_cells s mm A [CB (Z.to_nat (34 + 1442)) bs]) in SZ end.
  apply rw_cells_cb_split in SZ; [|lia|lia]. destruct SZ as [S2 S3].
  zstep. zstep. zstep. zstep. zstep.
  call (STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (bv_unsigned spo + -1596) base p (vz vl (Z.to_nat p)) lo _).
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  { lia. }
  { lia. }
  { unfold vz. lia. }
  { assumption. }
  { rewrite USP. exact ST. }
  { unfold REAC_CTRL_STAMP_HEADAMP_STACK. rewrite USP. lia. }
  { rewrite USP. replace (bv_unsigned spo + -1616) with (bv_unsigned spo + (-101) * 16) by lia.
    rewrite Z_mod_plus_full. exact HM16. }
  { eapply row_keep; [exact HROW | eassumption | cbn [disjoint_from]; repeat split; lia]. }
  { unfold REAC_CTRL_STAMP_HEADAMP_STACK. rewrite USP. lia. }
  { intros _. split; [exact S2 | split; [lia | split; [right; rewrite USP; lia | lia]]]. }
  rewrite (legal_legalb _ _ HLEG) in POST. destruct POST as [Hst0 S2'].
  subst.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1616))) |- _ =>
    rewrite USP in H end.
  zstep. first [ if_false | idtac ].
  zstep. zstep. zstep. zstep.
  call MEMC.
  { rewrite US5. replace (bv_unsigned spo + -1580) with (bv_unsigned spo + -1596 + 16) by lia.
    apply rw_cells_bytes. exact S2'. }
  { reflexivity. }
  { rewrite H6. exact R1. }
  { rewrite US5, H6, U34. lia. }
  { assumption. }
  match goal with H : rw_cells _ _ (bv_unsigned s6) _ |- _ => rewrite H6 in H; rename H into NR end.
  pose proof (rw_cells_cb_join _ _ 16 34 _ _ ltac:(lia) ltac:(lia) S1 S2') as J1.
  replace (bv_unsigned spo + -1596 + 16 + 34) with (bv_unsigned spo + -1596 + (16 + 34)) in S3 by lia.
  pose proof (rw_cells_cb_join _ _ (16 + 34) 1442 _ _ ltac:(lia) ltac:(lia) J1 S3) as J2.
  pose proof (rw_cells_cb_join _ _ (34 * k) 34 _ _ ltac:(lia) ltac:(lia) DONE NR) as J3.
  apply evt_done. do 16 eexists. eexists. eexists. split; [reflexivity|].
  split; [assumption|].
  split; [exact FR0|].
  split; [exact J2|].
  split; [exact FRS|].
  split; [replace (34 * (k + 1)) with (34 * k + 34) by lia; exact J3|].
  split; [replace (bv_unsigned s2 + 34 * (k + 1)) with (bv_unsigned s2 + 34 * k + 34) by lia;
          replace (34 * (r - 1)) with (34 * (r - 1)) by lia; exact R2|].
  split; [assumption|].
  split; [assumption|].
  split; [exact MU|exact WM].
Qed.

Lemma turnB : memcpy_contract -> memset_contract -> reac_ctrl_stamp_headamp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (spo vv : word)
         (ch p j0 lo k r n : Z) (vl x1 dn rs : list byte) (cs0 csS : list cell),
    sp = Z_to_bv 64 (bv_unsigned spo + -1616) ->
    s6 = Z_to_bv 64 ch -> s11 = Z_to_bv 64 p ->
    s5 = Z_to_bv 64 (bv_unsigned spo + -1580) ->
    0 <= ch < 256 -> 0 <= p < 3 -> 0 <= j0 -> 0 <= k -> 1 <= r -> k + r = n ->
    bv_unsigned s3 = bv_unsigned s2 + 34 * k ->
    bv_unsigned s9 = bv_unsigned vv + j0 ->
    (Z.to_nat (j0 + p) < length vl)%nat ->
    legal p (vz vl (Z.to_nat (j0 + p))) ->
    lo + 1888 <= bv_unsigned spo -> 0 <= lo -> bv_unsigned spo mod 16 = 0 ->
    bytes_at rsegs m (bv_unsigned vv) vl ->
    rw_cells rsegs m (bv_unsigned spo + -1616) cs0 -> cells_size cs0 = 20%nat ->
    rw_cells rsegs m (bv_unsigned spo + -1596) [CB 1492 x1] ->
    rw_cells rsegs m (bv_unsigned spo + -104) csS -> cells_size csS = 104%nat ->
    rw_cells rsegs m (bv_unsigned s2) [CB (Z.to_nat (34 * k)) dn] ->
    rw_cells rsegs m (bv_unsigned s2 + 34 * k) [CB (Z.to_nat (34 * r)) rs] ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned spo + -1616) ->
    (bv_unsigned s2 + 34 * n <= lo \/ bv_unsigned spo <= bv_unsigned s2) ->
    (bv_unsigned vv + Z.of_nat (length vl) <= lo \/ bv_unsigned spo <= bv_unsigned vv) ->
    (bv_unsigned vv + Z.of_nat (length vl) <= bv_unsigned s2 \/ bv_unsigned s2 + 34 * n <= bv_unsigned vv) ->
    munch [(bv_unsigned spo - 1888, bv_unsigned spo); (bv_unsigned s2, bv_unsigned s2 + 34 * n)] m0 m ->
    wmono rsegs m0 m ->
    bytes_at rsegs m0 CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned spo - 1888 \/ bv_unsigned spo <= CTRL_ROW) ->
    (bv_unsigned s2 + 34 * n <= CTRL_ROW \/ CTRL_ROW + 24 <= bv_unsigned s2) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (x1' : list byte),
         ms' = MS (mkR (Z_to_bv 64 0x140f0) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7' s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x140f0) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' (bv_unsigned vv) vl /\
         rw_cells rsegs m' (bv_unsigned spo + -1616) cs0 /\
         rw_cells rsegs m' (bv_unsigned spo + -1596) [CB 1492 x1'] /\
         rw_cells rsegs m' (bv_unsigned spo + -104) csS /\
         rw_cells rsegs m' (bv_unsigned s2)
           [CB (Z.to_nat (34 * (k + 1))) (dn ++ GA ch p (vz vl (Z.to_nat (j0 + p))))] /\
         rw_cells rsegs m' (bv_unsigned s2 + 34 * (k + 1)) [CB (Z.to_nat (34 * (r - 1))) (skipn 34 rs)] /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned spo + -1616) /\
         munch [(bv_unsigned spo - 1888, bv_unsigned spo); (bv_unsigned s2, bv_unsigned s2 + 34 * n)] m0 m' /\
         wmono rsegs m0 m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140b0) fc None m (seg_rom rsegs)).
Proof.
  intros MEMC MEMS STAMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m0 spo vv ch p j0 lo k r n vl x1 dn rs cs0 csS
    -> -> -> -> HC HP Hj0 Hk Hr Hn H3 H9 Hj HLEG LO Hlo HM16 HV FR0 Hcs0 SCR FRS HcsS DONE REST HMI ST D1 D2 D3 MU WM
    HROW HROWD HROWR.
  pose proof (bv_unsigned_in_range 64 spo) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 s2) as Rs2. unfold bv_modulus in Rs2.
  pose proof (bv_unsigned_in_range 64 vv) as Rvv. unfold bv_modulus in Rvv.
  pose proof (bv_unsigned_in_range 64 s9) as Rs9. unfold bv_modulus in Rs9.
  pose proof (rw_cells_bound rsegs m _ _ REST) as BR. cbn [cells_size csize] in BR.
  rewrite Nat.add_0_r, Z2Nat.id in BR by lia.
  replace (34 * r) with (34 + 34 * (r - 1)) in REST by lia.
  apply rw_cells_cb_split in REST; [|lia|lia]. destruct REST as [R1 R2].
  assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s9 + p)) 1
               = Some [nth (Z.to_nat (j0 + p)) vl (Z_to_bv 8 0)]).
  { change (Z_to_bv 64 (bv_unsigned s9 + p)) with (wa (bv_unsigned s9 + p)). rewrite H9.
    replace (bv_unsigned vv + j0 + p) with (bv_unsigned vv + Z.of_nat (Z.to_nat (j0 + p))) by lia.
    apply nth_read1; assumption. }
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (j0 + p)) vl (Z_to_bv 8 0))) as Rv. unfold bv_modulus in Rv.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1616)) = bv_unsigned spo + -1616)
    by (rewrite unsigned_lit by lia; lia).
  assert (USCR : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1596)) = bv_unsigned spo + -1596)
    by (rewrite unsigned_lit by lia; lia).
  assert (US5 : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1580)) = bv_unsigned spo + -1580)
    by (rewrite unsigned_lit by lia; lia).
  assert (U1492 : bv_unsigned (Z_to_bv 64 1492) = 1492) by reflexivity.
  assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
  assert (USTK : REAC_CTRL_STAMP_HEADAMP_STACK = 272) by reflexivity.
  zstep.
  zstep. zstep. zstep. zstep. zstep.
  call MEMS.
  { rewrite USCR. exact SCR. }
  { exact HMI. }
  match goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1596))) _ |- _ =>
    rewrite USCR in H; rename H into SZ end.
  match type of SZ with rw_cells ?s ?mm ?A [CB _ ?bs] =>
    change (rw_cells s mm A [CB (Z.to_nat (16 + 1476)) bs]) in SZ end.
  apply rw_cells_cb_split in SZ; [|lia|lia]. destruct SZ as [S1 SZ].
  match type of SZ with rw_cells ?s ?mm ?A [CB _ ?bs] =>
    change (rw_cells s mm A [CB (Z.to_nat (34 + 1442)) bs]) in SZ end.
  apply rw_cells_cb_split in SZ; [|lia|lia]. destruct SZ as [S2 S3].
  zstep. zstep. zstep. zstep. zstep.
  call (STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (bv_unsigned spo + -1596) ch p (vz vl (Z.to_nat (j0 + p))) lo _).
  { reflexivity. }
  { reflexivity. }
  { f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  { reflexivity. }
  { lia. }
  { lia. }
  { unfold vz. lia. }
  { assumption. }
  { rewrite USP. exact ST. }
  { unfold REAC_CTRL_STAMP_HEADAMP_STACK. rewrite USP. lia. }
  { rewrite USP. replace (bv_unsigned spo + -1616) with (bv_unsigned spo + (-101) * 16) by lia.
    rewrite Z_mod_plus_full. exact HM16. }
  { eapply row_keep; [exact HROW | eassumption | cbn [disjoint_from]; repeat split; lia]. }
  { unfold REAC_CTRL_STAMP_HEADAMP_STACK. rewrite USP. lia. }
  { intros _. split; [exact S2 | split; [lia | split; [right; rewrite USP; lia | lia]]]. }
  rewrite (legal_legalb _ _ HLEG) in POST. destruct POST as [Hst0 S2'].
  subst.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1616))) |- _ =>
    rewrite USP in H end.
  zstep. first [ if_false | idtac ].
  zstep. zstep. zstep. zstep.
  call MEMC.
  { rewrite US5. replace (bv_unsigned spo + -1580) with (bv_unsigned spo + -1596 + 16) by lia.
    apply rw_cells_bytes. exact S2'. }
  { reflexivity. }
  { rewrite H3. exact R1. }
  { rewrite US5, H3, U34. lia. }
  { assumption. }
  match goal with H : rw_cells _ _ (bv_unsigned s3) _ |- _ => rewrite H3 in H; rename H into NR end.
  pose proof (rw_cells_cb_join _ _ 16 34 _ _ ltac:(lia) ltac:(lia) S1 S2') as J1.
  replace (bv_unsigned spo + -1596 + 16 + 34) with (bv_unsigned spo + -1596 + (16 + 34)) in S3 by lia.
  pose proof (rw_cells_cb_join _ _ (16 + 34) 1442 _ _ ltac:(lia) ltac:(lia) J1 S3) as J2.
  pose proof (rw_cells_cb_join _ _ (34 * k) 34 _ _ ltac:(lia) ltac:(lia) DONE NR) as J3.
  apply evt_done. do 16 eexists. eexists. eexists. split; [reflexivity|].
  split; [assumption|].
  split; [exact FR0|].
  split; [exact J2|].
  split; [exact FRS|].
  split; [replace (34 * (k + 1)) with (34 * k + 34) by lia; exact J3|].
  split; [replace (bv_unsigned s2 + 34 * (k + 1)) with (bv_unsigned s2 + 34 * k + 34) by lia; exact R2|].
  split; [assumption|].
  split; [assumption|].
  split; [exact MU|exact WM].
Qed.
