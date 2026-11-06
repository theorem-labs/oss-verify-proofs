From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel RgLemmas
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

Lemma not_val : forall x : word,
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned x) 18446744073709551615)) = 18446744073709551615 - bv_unsigned x.
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  rewrite zb_lxor_ones by lia. apply unsigned_lit. lia.
Qed.

Lemma ovf_chk_ok : forall a b k, b <= a -> 0 <= k < 9223372036854775808 ->
  Z.lxor (Z.lxor (Z.b2z (a <? b)) (Z.b2z (Z.lxor k 9223372036854775808 <? 9223372036854775808))) 1 <> 0.
Proof.
  intros a b k Hab Hk.
  rewrite (proj2 (Z.ltb_ge a b)) by lia.
  replace (Z.lxor k 9223372036854775808) with (k + 9223372036854775808).
  2:{ pose proof (zb_lxor_sign k ltac:(lia)) as E. change (2 ^ 63) with 9223372036854775808 in E.
      rewrite E. rewrite Z.mod_small by lia. reflexivity. }
  rewrite (proj2 (Z.ltb_ge (k + 9223372036854775808) 9223372036854775808)) by lia.
  cbn. discriminate.
Qed.

Ltac zsimpl_hyp H :=
  repeat first
    [ match type of H with context [Z.shiftl ?a 1] =>
        rewrite (Z.shiftl_mul_pow2 a 1) in H by lia; change (2 ^ 1) with 2 in H end
    | match type of H with context [?a mod 18446744073709551616] =>
        rewrite (Z.mod_small a 18446744073709551616) in H by lia end
    | match type of H with context [bv_swrap 32 ?a] => rewrite (swrap32_id a) in H by lia end
    | match type of H with context [bv_signed (Z_to_bv 64 ?a)] => rewrite (signed64_small a) in H by lia end ].

Ltac zsimpl_goal :=
  repeat first
    [ match goal with |- context [Z.shiftl ?a 1] =>
        rewrite (Z.shiftl_mul_pow2 a 1) by lia; change (2 ^ 1) with 2 end
    | match goal with |- context [?a mod 18446744073709551616] =>
        rewrite (Z.mod_small a 18446744073709551616) by lia end
    | match goal with |- context [bv_swrap 32 ?a] => rewrite (swrap32_id a) by lia end
    | match goal with |- context [bv_signed (Z_to_bv 64 ?a)] => rewrite (signed64_small a) by lia end ].

Ltac trap_off :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let HT := fresh "HT" in
      if_cases HT; zify_cond HT;
      [ exfalso; zsimpl_hyp HT;
        first [ lia
              | match type of HT with
                | Z.lxor (Z.lxor (Z.b2z (?a <? ?b)) (Z.b2z (Z.lxor ?k _ <? _))) 1 = 0 =>
                    exact (ovf_chk_ok a b k ltac:(lia) ltac:(lia) HT)
                end ]
      | clear HT ]
  | _ => idtac
  end.

Ltac unlits :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.

Lemma turnA : memcpy_contract -> memset_contract -> reac_ctrl_stamp_headamp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (spo : word)
         (base p lo k r n : Z) (vl x1 dn rs : list byte) (cs0 csS : list cell),
    sp = Z_to_bv 64 (bv_unsigned spo + -1632) ->
    s2 = Z_to_bv 64 base -> s4 = Z_to_bv 64 p ->
    s5 = Z_to_bv 64 (bv_unsigned spo + -1580) ->
    0 <= base < 256 -> 0 <= p < 3 -> 0 <= k -> 1 <= r -> k + r = n ->
    bv_unsigned s8 = 34 * k ->
    bv_unsigned s7 = 18446744073709551615 - bv_unsigned s3 ->
    bv_unsigned s9 = 18446744073709551615 - bv_unsigned s0 ->
    (Z.to_nat p < length vl)%nat ->
    legal p (vz vl (Z.to_nat p)) ->
    lo + 1856 <= bv_unsigned spo -> 0 <= lo -> bv_unsigned spo mod 16 = 0 ->
    bytes_at rsegs m (bv_unsigned s0) vl ->
    rw_cells rsegs m (bv_unsigned spo + -1632) cs0 -> cells_size cs0 = 36%nat ->
    rw_cells rsegs m (bv_unsigned spo + -1596) [CB 1492 x1] ->
    rw_cells rsegs m (bv_unsigned spo + -104) csS -> cells_size csS = 104%nat ->
    rw_cells rsegs m (bv_unsigned s3) [CB (Z.to_nat (34 * k)) dn] ->
    rw_cells rsegs m (bv_unsigned s3 + 34 * k) [CB (Z.to_nat (34 * r)) rs] ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned spo + -1632) ->
    (bv_unsigned s3 + 34 * n <= lo \/ bv_unsigned spo <= bv_unsigned s3) ->
    (bv_unsigned s0 + Z.of_nat (length vl) <= lo \/ bv_unsigned spo <= bv_unsigned s0) ->
    (bv_unsigned s0 + Z.of_nat (length vl) <= bv_unsigned s3 \/ bv_unsigned s3 + 34 * n <= bv_unsigned s0) ->
    munch [(bv_unsigned spo - 1856, bv_unsigned spo); (bv_unsigned s3, bv_unsigned s3 + 34 * n)] m0 m ->
    wmono rsegs m0 m ->
    bytes_at rsegs m0 CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned spo - 1856 \/ bv_unsigned spo <= CTRL_ROW) ->
    (bv_unsigned s3 + 34 * n <= CTRL_ROW \/ CTRL_ROW + 24 <= bv_unsigned s3) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (x1' : list byte),
         ms' = MS (mkR (Z_to_bv 64 0x145f0) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x145f0) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' (bv_unsigned s0) vl /\
         rw_cells rsegs m' (bv_unsigned spo + -1632) cs0 /\
         rw_cells rsegs m' (bv_unsigned spo + -1596) [CB 1492 x1'] /\
         rw_cells rsegs m' (bv_unsigned spo + -104) csS /\
         rw_cells rsegs m' (bv_unsigned s3) [CB (Z.to_nat (34 * (k + 1))) (dn ++ GA base p (vz vl (Z.to_nat p)))] /\
         rw_cells rsegs m' (bv_unsigned s3 + 34 * (k + 1)) [CB (Z.to_nat (34 * (r - 1))) (skipn 34 rs)] /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned spo + -1632) /\
         munch [(bv_unsigned spo - 1856, bv_unsigned spo); (bv_unsigned s3, bv_unsigned s3 + 34 * n)] m0 m' /\
         wmono rsegs m0 m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x145a8) fc None m (seg_rom rsegs)).
Proof.
  intros MEMC MEMS STAMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m0 spo base p lo k r n vl x1 dn rs cs0 csS
    -> -> -> -> HB HP Hk Hr Hn H8 H7 H9 Hj HLEG LO Hlo HM16 HV FR0 Hcs0 SCR FRS HcsS DONE REST HMI ST D1 D2 D3 MU WM
    HROW HROWD HROWR.
  pose proof (bv_unsigned_in_range 64 spo) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 s3) as Rs3. unfold bv_modulus in Rs3.
  pose proof (bv_unsigned_in_range 64 s0) as Rs0. unfold bv_modulus in Rs0.
  pose proof (rw_cells_bound rsegs m _ _ REST) as BR. cbn [cells_size csize] in BR.
  rewrite Nat.add_0_r, Z2Nat.id in BR by lia.
  pose proof (bytes_at_bound rsegs _ _ _ HV) as BV.
  assert (Hj' : p < Z.of_nat (length vl)) by lia.
  replace (34 * r) with (34 + 34 * (r - 1)) in REST by lia.
  apply rw_cells_cb_split in REST; [|lia|lia]. destruct REST as [R1 R2].
  assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s0 + p)) 1 = Some [nth (Z.to_nat p) vl (Z_to_bv 8 0)]).
  { change (Z_to_bv 64 (bv_unsigned s0 + p)) with (wa (bv_unsigned s0 + p)).
    replace (bv_unsigned s0 + p) with (bv_unsigned s0 + Z.of_nat (Z.to_nat p)) by lia.
    apply nth_read1; assumption. }
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat p) vl (Z_to_bv 8 0))) as Rv. unfold bv_modulus in Rv.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1632)) = bv_unsigned spo + -1632)
    by (rewrite unsigned_lit by lia; lia).
  assert (USCR : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1596)) = bv_unsigned spo + -1596)
    by (rewrite unsigned_lit by lia; lia).
  assert (US5 : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1580)) = bv_unsigned spo + -1580)
    by (rewrite unsigned_lit by lia; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 (bv_unsigned s3 + bv_unsigned s8)) = bv_unsigned s3 + 34 * k)
    by (rewrite unsigned_lit by lia; lia).
  assert (U1492 : bv_unsigned (Z_to_bv 64 1492) = 1492) by reflexivity.
  assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
  assert (USTK : REAC_CTRL_STAMP_HEADAMP_STACK = 224) by reflexivity.
  zstep. trap_off.
  zstep. trap_off.
  zstep. zstep.
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
  { rewrite USP. replace (bv_unsigned spo + -1632) with (bv_unsigned spo + (-102) * 16) by lia.
    rewrite Z_mod_plus_full. exact HM16. }
  { eapply row_keep; [exact HROW | eassumption | cbn [disjoint_from]; repeat split; lia]. }
  { unfold REAC_CTRL_STAMP_HEADAMP_STACK. rewrite USP. lia. }
  { intros _. split; [exact S2 | split; [lia | split; [right; rewrite USP; lia | lia]]]. }
  rewrite (legal_legalb _ _ HLEG) in POST. destruct POST as [Hst0 S2'].
  subst.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1632))) |- _ =>
    rewrite USP in H end.
  zstep. first [ if_false | idtac ].
  zstep. zstep. zstep. zstep.
  call MEMC.
  { rewrite US5. replace (bv_unsigned spo + -1580) with (bv_unsigned spo + -1596 + 16) by lia.
    apply rw_cells_bytes. exact S2'. }
  { reflexivity. }
  { rewrite UD. exact R1. }
  { rewrite US5, UD, U34. lia. }
  { assumption. }
  match goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 (bv_unsigned s3 + bv_unsigned s8))) _ |- _ =>
    rewrite UD in H; rename H into NR end.
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
  split; [replace (bv_unsigned s3 + 34 * (k + 1)) with (bv_unsigned s3 + 34 * k + 34) by lia; exact R2|].
  split; [assumption|].
  split; [assumption|].
  split; [exact MU|exact WM].
Qed.

Lemma turnB : memcpy_contract -> memset_contract -> reac_ctrl_stamp_headamp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m m0 : word -> option byte) (spo cw fl cnt : word)
         (ch p j0 lo k r n : Z) (vl x1 dn rs xa xb : list byte) (csS : list cell),
    sp = Z_to_bv 64 (bv_unsigned spo + -1632) ->
    s4 = Z_to_bv 64 k -> s6 = Z_to_bv 64 ch -> s9 = Z_to_bv 64 p -> s11 = Z_to_bv 64 j0 ->
    0 <= ch < 256 -> 0 <= p < 3 -> 0 <= j0 -> j0 + p < 2147483647 -> 0 <= k -> 1 <= r -> k + r = n ->
    bv_unsigned s7 = bv_unsigned s3 + 34 * k ->
    bv_unsigned s10 = bv_unsigned s3 + 34 * k ->
    0 < bv_unsigned s3 -> 0 < bv_unsigned s0 ->
    bv_unsigned fl = 0 -> bv_unsigned cnt <> p ->
    (Z.to_nat (j0 + p) < length vl)%nat ->
    legal p (vz vl (Z.to_nat (j0 + p))) ->
    lo + 1856 <= bv_unsigned spo -> 0 <= lo -> bv_unsigned spo mod 16 = 0 ->
    bytes_at rsegs m (bv_unsigned s0) vl ->
    rw_cells rsegs m (bv_unsigned spo + -1632) [CB 8 xa; C8 cw; C8 fl; C8 cnt; CB 4 xb] ->
    rw_cells rsegs m (bv_unsigned spo + -1596) [CB 1492 x1] ->
    rw_cells rsegs m (bv_unsigned spo + -104) csS -> cells_size csS = 104%nat ->
    rw_cells rsegs m (bv_unsigned s3) [CB (Z.to_nat (34 * k)) dn] ->
    rw_cells rsegs m (bv_unsigned s3 + 34 * k) [CB (Z.to_nat (34 * r)) rs] ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned spo + -1632) ->
    (bv_unsigned s3 + 34 * n <= lo \/ bv_unsigned spo <= bv_unsigned s3) ->
    (bv_unsigned s0 + Z.of_nat (length vl) <= lo \/ bv_unsigned spo <= bv_unsigned s0) ->
    (bv_unsigned s0 + Z.of_nat (length vl) <= bv_unsigned s3 \/ bv_unsigned s3 + 34 * n <= bv_unsigned s0) ->
    munch [(bv_unsigned spo - 1856, bv_unsigned spo); (bv_unsigned s3, bv_unsigned s3 + 34 * n)] m0 m ->
    wmono rsegs m0 m ->
    bytes_at rsegs m0 CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned spo - 1856 \/ bv_unsigned spo <= CTRL_ROW) ->
    (bv_unsigned s3 + 34 * n <= CTRL_ROW \/ CTRL_ROW + 24 <= bv_unsigned s3) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s8' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (x1' : list byte),
         ms' = MS (mkR (Z_to_bv 64 0x14738) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8' s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x14738) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' (bv_unsigned s0) vl /\
         rw_cells rsegs m' (bv_unsigned spo + -1632) [CB 8 xa; C8 cw; C8 fl; C8 cnt; CB 4 xb] /\
         rw_cells rsegs m' (bv_unsigned spo + -1596) [CB 1492 x1'] /\
         rw_cells rsegs m' (bv_unsigned spo + -104) csS /\
         rw_cells rsegs m' (bv_unsigned s3)
           [CB (Z.to_nat (34 * (k + 1))) (dn ++ GA ch p (vz vl (Z.to_nat (j0 + p))))] /\
         rw_cells rsegs m' (bv_unsigned s3 + 34 * (k + 1)) [CB (Z.to_nat (34 * (r - 1))) (skipn 34 rs)] /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned spo + -1632) /\
         munch [(bv_unsigned spo - 1856, bv_unsigned spo); (bv_unsigned s3, bv_unsigned s3 + 34 * n)] m0 m' /\
         wmono rsegs m0 m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x146a8) fc None m (seg_rom rsegs)).
Proof.
  intros MEMC MEMS STAMP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m m0 spo cw fl cnt ch p j0 lo k r n vl x1 dn rs xa xb csS
    -> -> -> -> -> HC HP Hj0 Hj2 Hk Hr Hn H7 H10 Hs3 Hs0 Hfl Hcnt Hj HLEG LO Hlo HM16 HV FR0 SCR FRS HcsS DONE REST HMI ST
    D1 D2 D3 MU WM HROW HROWD HROWR.
  pose proof (bv_unsigned_in_range 64 spo) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 s3) as Rs3. unfold bv_modulus in Rs3.
  pose proof (bv_unsigned_in_range 64 s0) as Rs0. unfold bv_modulus in Rs0.
  pose proof (rw_cells_bound rsegs m _ _ REST) as BR. cbn [cells_size csize] in BR.
  rewrite Nat.add_0_r, Z2Nat.id in BR by lia.
  pose proof (bytes_at_bound rsegs _ _ _ HV) as BV.
  assert (Hj' : j0 + p < Z.of_nat (length vl)) by lia.
  replace (34 * r) with (34 + 34 * (r - 1)) in REST by lia.
  apply rw_cells_cb_split in REST; [|lia|lia]. destruct REST as [R1 R2].
  assert (RD : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s0 + (j0 + p))) 1
               = Some [nth (Z.to_nat (j0 + p)) vl (Z_to_bv 8 0)]).
  { change (Z_to_bv 64 (bv_unsigned s0 + (j0 + p))) with (wa (bv_unsigned s0 + (j0 + p))).
    replace (bv_unsigned s0 + (j0 + p)) with (bv_unsigned s0 + Z.of_nat (Z.to_nat (j0 + p))) by lia.
    apply nth_read1; assumption. }
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (j0 + p)) vl (Z_to_bv 8 0))) as Rv. unfold bv_modulus in Rv.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1632)) = bv_unsigned spo + -1632)
    by (rewrite unsigned_lit by lia; lia).
  assert (USCR : bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1596)) = bv_unsigned spo + -1596)
    by (rewrite unsigned_lit by lia; lia).
  assert (U1492 : bv_unsigned (Z_to_bv 64 1492) = 1492) by reflexivity.
  assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
  assert (USTK : REAC_CTRL_STAMP_HEADAMP_STACK = 224) by reflexivity.
  zstep; zstep; trap_off.
  zstep; trap_off.
  zstep; zstep; zstep; zstep; zstep; trap_off.
  zstep; zstep; trap_off.
  zstep; zstep; zstep; trap_off.
  zstep; zstep; zstep; trap_off.
  zstep; zstep; zstep; zstep; zstep; trap_off.
  rewrite (swrap32_id (j0 + p + 0)) by lia.
  zstep.
  zstep; zstep; zstep; zstep.
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
  zstep; zstep; zstep; zstep; zstep.
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
  { rewrite USP. replace (bv_unsigned spo + -1632) with (bv_unsigned spo + (-102) * 16) by lia.
    rewrite Z_mod_plus_full. exact HM16. }
  { eapply row_keep; [exact HROW | eassumption | cbn [disjoint_from]; repeat split; lia]. }
  { unfold REAC_CTRL_STAMP_HEADAMP_STACK. rewrite USP. lia. }
  { intros _; split; [exact S2 | split; [lia | split; [right; rewrite USP; lia | lia]]]. }
  rewrite (legal_legalb _ _ HLEG) in POST. destruct POST as [Hst0 S2'].
  subst.
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 (bv_unsigned spo + -1632))) |- _ =>
    rewrite USP in H end.
  zstep; first [ if_false | idtac ].
  zstep; zstep; zstep; zstep.
  call MEMC.
  { unlits. match goal with |- bytes_at _ _ ?e _ => replace e with (bv_unsigned spo + -1596 + 16) by lia end.
    apply rw_cells_bytes. exact S2'. }
  { reflexivity. }
  { rewrite H10. exact R1. }
  { unlits. rewrite H10. lia. }
  { assumption. }
  match goal with H : rw_cells _ _ (bv_unsigned s10) _ |- _ => rewrite H10 in H; rename H into NR end.
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
  split; [replace (bv_unsigned s3 + 34 * (k + 1)) with (bv_unsigned s3 + 34 * k + 34) by lia; exact R2|].
  split; [assumption|].
  split; [assumption|].
  split; [exact MU|exact WM].
Qed.
