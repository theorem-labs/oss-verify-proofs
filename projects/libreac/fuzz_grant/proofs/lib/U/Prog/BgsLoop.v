From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel RgLemmas
  memcpy_c memset_c reac_ctrl_stamp_headamp_c reac_ctrl_build_grant_sweep_c BgsTurn.
Import ListNotations.
Open Scope Z_scope.
Definition saved_cells (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma bgs_exit : forall (ra0 sp0 gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word)
    (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 r s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (cs : list cell),
  1632 <= bv_unsigned sp0 ->
  rw_cells rsegs m (bv_unsigned sp0 + -1632) cs -> cells_size cs = 1528%nat ->
  rw_cells rsegs m (bv_unsigned sp0 + -104) (saved_cells ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o) ->
  stk rsegs m lo (bv_unsigned sp0 + -1632) -> lo <= bv_unsigned sp0 + -1632 ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s0o s1o r a1' a2' a3' a4' a5' a6' a7'
                     s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o t3' t4' t5' t6')
                F (ret_pc ra0) fc None m (seg_rom rsegs) /\
       stk rsegs m lo (bv_unsigned sp0))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -1632)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 r s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14774) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o
    ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 r s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo cs HSP HCS Hcs HFRS ST HLO.
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. unfold bv_modulus in Rsp.
  unfold saved_cells in HFRS.
  assert (J : rw_cells rsegs m (bv_unsigned sp0 + -1632)
                (cs ++ [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0])).
  { apply rw_cells_app. split; [exact HCS|]. rewrite Hcs.
    replace (bv_unsigned sp0 + -1632 + Z.of_nat 1528) with (bv_unsigned sp0 + -104) by lia. exact HFRS. }
  pose proof (stk_release rsegs m lo (bv_unsigned sp0 + -1632) _ ST J HLO) as ST2.
  rewrite cells_size_app, Hcs in ST2. cbn [cells_size csize Nat.add] in ST2.
  replace (bv_unsigned sp0 + -1632 + Z.of_nat 1632) with (bv_unsigned sp0) in ST2 by lia.
  clear J.
  zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep.
  apply evt_done. do 14 eexists. split; [reflexivity | exact ST2].
Qed.

Lemma sweep_ok_spec : forall sw vals M base w, sweep_ok sw vals M base w = true <->
  bv_unsigned sw <> 0 /\ bv_unsigned vals <> 0 /\ 1 <= w /\ base + w <= 48 /\ 8 + 3 * w <= M.
Proof.
  intros. unfold sweep_ok. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq, !Z.leb_le. tauto.
Qed.

Definition prefixB (base : Z) (vl : list byte) (c : nat) : list byte :=
  HEAD_ACK34 ++ ga_chan base vl 0 ++ HEAD_MARK34 ++ GBall ++ concat (map (ga_chan base vl) (seq 1 (c - 1))).

Lemma prefixB_SWEEP : forall base vl w, prefixB base vl w = SWEEP base w vl.
Proof. reflexivity. Qed.

Lemma prefixB_step : forall base vl c, (1 <= c)%nat ->
  ((prefixB base vl c ++ ga_row base vl c 0) ++ ga_row base vl c 1) ++ ga_row base vl c 2 = prefixB base vl (S c).
Proof.
  intros base vl c Hc. unfold prefixB, ga_chan.
  replace (S c - 1)%nat with (S (c - 1)) by lia. rewrite seq_S.
  replace (1 + (c - 1))%nat with c by lia. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r.
  rewrite !app_assoc. reflexivity.
Qed.

Lemma ga_row_eq : forall base vl c p, 0 <= c -> 0 <= p < 3 -> base + c < 256 -> 0 <= base ->
  GA (base + c) p (vz vl (Z.to_nat (3 * c + p))) = ga_row base vl (Z.to_nat c) (Z.to_nat p).
Proof.
  intros base vl c p Hc Hp Hb Hb0. unfold ga_row.
  rewrite Z2Nat.id by lia. rewrite (Z.mod_small (base + c)) by lia. rewrite Z2Nat.id by lia.
  f_equal. f_equal. lia.
Qed.

Lemma legal_at : forall w vl c p, vals_legal (Z.to_nat w) vl -> 0 <= c -> c < w -> 0 <= p < 3 ->
  legal p (vz vl (Z.to_nat (3 * c + p))).
Proof.
  intros w vl c p H Hc Hcw Hp.
  pose proof (H (Z.to_nat (3 * c + p)) ltac:(lia)) as L.
  replace (Z.of_nat (Z.to_nat (3 * c + p) mod 3)) with p in L; [exact L|].
  rewrite Nat2Z.inj_mod, Z2Nat.id by lia. change (Z.of_nat 3) with 3.
  rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma rw_ro_disj : forall m d (n : Z) bs s jk,
  mem_inv rsegs m -> rw_cells rsegs m d [CB (Z.to_nat n) jk] -> ro_bytes rsegs s bs -> 0 < n -> 0 <= s ->
  Z.of_nat (length bs) = n -> d + n <= s \/ s + n <= d.
Proof.
  intros m d n bs s jk HI [_ W] HR Hn Hs HL. cbn [cells_size csize] in W.
  rewrite Nat.add_0_r, Z2Nat.id in W by lia.
  pose proof (wr_ro_disj m d n s bs HI W HR Hn Hs ltac:(lia)). lia.
Qed.

Lemma img_ack : ro_bytes rsegs 0x105b4 HEAD_ACK34.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma img_mark : ro_bytes rsegs 0x105d6 HEAD_MARK34.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma img_gbi : forall i, 0 <= i <= 5 -> ro_bytes rsegs (0x104a8 + 34 * i) (GB i).
Proof.
  intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as H by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    apply ro_bytes_b_sound; vm_compute; reflexivity.
Qed.

Definition gbp (i : nat) : list byte := concat (map (fun j => GB (Z.of_nat j)) (seq 0 i)).

Lemma gbp_S : forall i, gbp (S i) = gbp i ++ GB (Z.of_nat i).
Proof.
  intros i. unfold gbp. rewrite seq_S, map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity.
Qed.

Lemma gbp_6 : gbp 5 ++ GB 5 = GBall.
Proof. vm_compute. reflexivity. Qed.

Lemma prefixB1 : forall base vl, 0 <= base < 256 ->
  prefixB base vl 1 =
  ((((HEAD_ACK34 ++ GA base 0 (vz vl 0)) ++ GA base 1 (vz vl 1)) ++ GA base 2 (vz vl 2)) ++ HEAD_MARK34) ++ GBall.
Proof.
  intros base vl Hb. unfold prefixB, ga_chan, ga_row. cbn [seq map concat Nat.sub]. rewrite app_nil_r.
  change (Z.of_nat 0) with 0. change (Z.of_nat 1) with 1. change (Z.of_nat 2) with 2.
  change (3 * 0 + 0)%nat with 0%nat. change (3 * 0 + 1)%nat with 1%nat. change (3 * 0 + 2)%nat with 2%nat.
  rewrite Z.add_0_r, Z.mod_small by lia. rewrite !app_assoc. reflexivity.
Qed.

Lemma grp_loop : memcpy_contract ->
  forall (d : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i : Z) (rs : list byte),
    Z.of_nat d = 6 - i -> 0 <= i <= 5 ->
    s4 = Z_to_bv 64 (66728 + 34 * i) -> s5 = Z_to_bv 64 (170 + 34 * i) -> s6 = Z_to_bv 64 374 ->
    bv_unsigned s7 = 18446744073709551615 - bv_unsigned s3 ->
    mem_inv rsegs m ->
    rw_cells rsegs m (bv_unsigned s3 + 170) [CB (Z.to_nat (34 * i)) (gbp (Z.to_nat i))] ->
    rw_cells rsegs m (bv_unsigned s3 + 170 + 34 * i) [CB (Z.to_nat (34 * (6 - i))) rs] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s5' t3' t4' t5' t6' ra' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4' s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x14648) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned s3 + 170 + 34 * i, bv_unsigned s3 + 374)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         rw_cells rsegs m' (bv_unsigned s3 + 170) [CB 204 GBall])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14628) fc None m (seg_rom rsegs)).
Proof.
  intros MEMC d. induction d as [|d IH];
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m i rs Hd Hi -> -> -> H7 HMI DONE REST.
  { lia. }
  pose proof (bv_unsigned_in_range 64 s3) as Rs3. unfold bv_modulus in Rs3.
  pose proof (rw_cells_bound rsegs m _ _ REST) as BR. cbn [cells_size csize] in BR.
  rewrite Nat.add_0_r, Z2Nat.id in BR by lia.
  replace (34 * (6 - i)) with (34 + 34 * (5 - i)) in REST by lia.
  apply rw_cells_cb_split in REST; [|lia|lia]. destruct REST as [R1 R2].
  pose proof (img_gbi i Hi) as HGB.
  pose proof (munch_refl [(bv_unsigned s3 + 170 + 34 * i, bv_unsigned s3 + 374)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UD : bv_unsigned (Z_to_bv 64 (bv_unsigned s3 + (170 + 34 * i))) = bv_unsigned s3 + 170 + 34 * i)
    by (rewrite unsigned_lit by lia; lia).
  assert (UG : bv_unsigned (Z_to_bv 64 (66728 + 34 * i)) = 0x104a8 + 34 * i) by (rewrite unsigned_lit by lia; lia).
  assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
  pose proof (wr_ro_disj _ _ _ _ _ HMI (proj2 R1) HGB ltac:(cbn; lia) ltac:(lia) ltac:(rewrite length_GB; lia)) as HDJ.
  rewrite length_GB in HDJ. cbn [cells_size csize] in HDJ.
  zstep. trap_off.
  zstep. zstep. zstep. zstep.
  call MEMC.
  { rewrite UG. apply (ro_bytes_at rsegs _ (0x104a8 + 34 * i) (GB i)); [assumption | lia | rewrite length_GB; lia | exact HGB]. }
  { rewrite length_GB. reflexivity. }
  { rewrite UD. exact R1. }
  { rewrite UG, U34, UD. lia. }
  { assumption. }
  match goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 (bv_unsigned s3 + (170 + 34 * i)))) _ |- _ =>
    rewrite UD in H; rename H into NR end.
  pose proof (rw_cells_cb_join _ _ (34 * i) 34 _ _ ltac:(lia) ltac:(lia) DONE NR) as J.
  zstep. zstep. zstep.
  if_cases E; zify_cond E.
  - assert (Hi5 : i < 5) by lia. clear E.
    match type of J with rw_cells _ ?mm _ _ =>
      assert (J' : rw_cells rsegs mm (bv_unsigned s3 + 170) [CB (Z.to_nat (34 * (i + 1))) (gbp (Z.to_nat (i + 1)))])
    end.
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite gbp_S, Z2Nat.id by lia.
      replace (34 * (i + 1)) with (34 * i + 34) by lia. exact J. }
    eapply evt_mono.
    { eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i + 1) _).
      - lia.
      - lia.
      - f_equal. lia.
      - f_equal. lia.
      - reflexivity.
      - exact H7.
      - assumption.
      - exact J'.
      - replace (bv_unsigned s3 + 170 + 34 * (i + 1)) with (bv_unsigned s3 + 170 + 34 * i + 34) by lia.
        replace (34 * (6 - (i + 1))) with (34 * (5 - i)) by lia. exact R2. }
    intros ms' (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & b14 & b15 & b16 & b17
                & m' & -> & MU' & WM' & MI' & ROWS').
    do 18 eexists. eexists. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn [outside]; intros; slia]|].
    split; [eapply wmono_trans; eassumption|].
    split; [exact MI'|exact ROWS'].
  - assert (Hi5 : i = 5) by lia. clear E. subst i.
    apply evt_done. do 18 eexists. eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|].
    change (Z.to_nat 5) with 5%nat in J. rewrite gbp_6 in J. exact J.
Qed.

Ltac turnB_side w vl c P HLEG HLEN UC :=
  first [ solve [apply (legal_at w vl c P HLEG); lia]
        | solve [zsimpl_goal; rewrite Z.lxor_nilpotent; reflexivity]
        | solve [rewrite UC; lia]
        | solve [rewrite HLEN; lia]
        | solve [f_equal; zsimpl_goal; lia]
        | solve [f_equal; unlits; zsimpl_goal; lia]
        | solve [f_equal; unlits; zsimpl_goal; change 255 with (Z.ones 8); rewrite Z.land_ones by lia;
                 apply Z.mod_small; lia]
        | solve [unlits; lia]
        | solve [lia] ].

Lemma bgs_loopB : memcpy_contract -> memset_contract -> reac_ctrl_stamp_headamp_contract ->
  forall (ra0 sp0 gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (sw vals : word) (M base w lo : Z) (vl : list byte),
    sweep_ok sw vals M base w = true ->
    0 <= base < 256 -> int32 w ->
    lo + 1856 <= bv_unsigned sp0 -> 0 <= lo -> bv_unsigned sp0 mod 16 = 0 ->
    length vl = Z.to_nat (3 * w) -> vals_legal (Z.to_nat w) vl ->
    (bv_unsigned sw + 34 * (8 + 3 * w) <= lo \/ bv_unsigned sp0 <= bv_unsigned sw) ->
    (bv_unsigned vals + 3 * w <= lo \/ bv_unsigned sp0 <= bv_unsigned vals) ->
    (bv_unsigned vals + 3 * w <= bv_unsigned sw \/ bv_unsigned sw + 34 * (8 + 3 * w) <= bv_unsigned vals) ->
    bytes_at rsegs m0 CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned sp0 - 1856 \/ bv_unsigned sp0 <= CTRL_ROW) ->
    (bv_unsigned sw + 34 * (8 + 3 * w) <= CTRL_ROW \/ CTRL_ROW + 24 <= bv_unsigned sw) ->
    forall (d : nat) (c : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : word -> option byte) (x0 x4 x1 rs : list byte),
      Z.of_nat d = w - c -> 1 <= c -> c < w ->
      a1 = Z_to_bv 64 34 -> a2 = Z_to_bv 64 c -> s5 = Z_to_bv 64 (8 + 3 * c) ->
      bytes_at rsegs m (bv_unsigned vals) vl ->
      rw_cells rsegs m (bv_unsigned sp0 + -1632) [CB 24 x0; C8 (Z_to_bv 64 (2147483639 - 3 * c)); CB 4 x4] ->
      rw_cells rsegs m (bv_unsigned sp0 + -1596) [CB 1492 x1] ->
      rw_cells rsegs m (bv_unsigned sp0 + -104) (saved_cells ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o) ->
      rw_cells rsegs m (bv_unsigned sw) [CB (Z.to_nat (34 * (8 + 3 * c))) (prefixB base vl (Z.to_nat c))] ->
      rw_cells rsegs m (bv_unsigned sw + 34 * (8 + 3 * c)) [CB (Z.to_nat (34 * (3 * w - 3 * c))) rs] ->
      mem_inv rsegs m ->
      stk rsegs m lo (bv_unsigned sp0 + -1632) ->
      munch [(bv_unsigned sp0 - 1856, bv_unsigned sp0); (bv_unsigned sw, bv_unsigned sw + 34 * (8 + 3 * w))] m0 m ->
      wmono rsegs m0 m ->
      evt rsegs (bgs_post ra0 sp0 gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F fc m0 sw vals M base w lo vl)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -1632)) gp tp t0 t1 t2 vals (Z_to_bv 64 w) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 base) sw s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14668) fc None m (seg_rom rsegs)).
Proof.
  intros MEMC MEMS STAMP ra0 sp0 gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F fc m0 sw vals M base w lo vl
    HOK HB HW LO Hlo HM16 HLEN HLEG D1 D2 D3 HROW HROWD HROWR d.
  pose proof HOK as HOK'. apply sweep_ok_spec in HOK' as (Hsw & Hvals & Hw1 & Hbw & HMw).
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 sw) as Rsw. unfold bv_modulus in Rsw.
  pose proof (bv_unsigned_in_range 64 vals) as Rvals. unfold bv_modulus in Rvals.
  assert (D2' : bv_unsigned vals + Z.of_nat (length vl) <= lo \/ bv_unsigned sp0 <= bv_unsigned vals)
    by (rewrite HLEN, Z2Nat.id by lia; exact D2).
  assert (D3' : bv_unsigned vals + Z.of_nat (length vl) <= bv_unsigned sw \/
                bv_unsigned sw + 34 * (8 + 3 * w) <= bv_unsigned vals)
    by (rewrite HLEN, Z2Nat.id by lia; exact D3).
  induction d as [|d IH];
    intros c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m x0 x4 x1 rs
      Hd Hc Hcw -> -> -> HV FR0 SCR FRS DONE REST HMI ST MU WM.
  { lia. }
  pose proof (rw_cells_bound rsegs m _ _ REST) as BR. cbn [cells_size csize] in BR.
  rewrite Nat.add_0_r, Z2Nat.id in BR by lia.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  assert (Hch : Z_to_bv 64 (Z.land (base + c) 255) = Z_to_bv 64 (base + c)).
  { f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  assert (U7 : bv_unsigned (Z_to_bv 64 (bv_unsigned sw + (8 + 3 * c) * 34)) = bv_unsigned sw + 34 * (8 + 3 * c))
    by (rewrite unsigned_lit by lia; lia).
  assert (UC : bv_unsigned (Z_to_bv 64 (2147483639 - 3 * c)) = 2147483639 - 3 * c)
    by (rewrite unsigned_lit by lia; lia).
  eapply evt_cut.
  { eapply (turnB MEMC MEMS STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 sp0
              (Z_to_bv 64 c) _ (Z_to_bv 64 (2147483639 - 3 * c))
              (base + c) 0 (3 * c) lo (8 + 3 * c) (3 * w - 3 * c) (8 + 3 * w) vl _ (prefixB base vl (Z.to_nat c)) rs
              _ _ _);
      first [ reflexivity | exact Hch | eassumption | idtac ].
    all: turnB_side w vl c 0 HLEG HLEN UC. }
  intros ms' Hp.
  destruct Hp as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s8' & t3' & t4' & t5' & t6'
                  & m2 & x1' & -> & HV2 & FR02 & SCR2 & FRS2 & DONE2 & REST2 & HMI2 & ST2 & MU2 & WM2).
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases E1; zify_cond E1; [ clear E1 | exfalso; zsimpl_hyp E1; lia ].
  zsimpl_goal.
  eapply evt_cut.
  { eapply (turnB MEMC MEMS STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 sp0
              (Z_to_bv 64 c) _ (Z_to_bv 64 (2147483639 - 3 * c))
              (base + c) 1 (3 * c) lo (8 + 3 * c + 1) (3 * w - 3 * c - 1) (8 + 3 * w) vl _ _ (skipn 34 rs)
              _ _ _);
      first [ reflexivity | exact Hch | eassumption | idtac ].
    all: turnB_side w vl c 1 HLEG HLEN UC. }
  intros ms' Hp.
  destruct Hp as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & s8'' & t3'' & t4''
                  & t5'' & t6'' & m3 & x1'' & -> & HV3 & FR03 & SCR3 & FRS3 & DONE3 & REST3 & HMI3 & ST3 & MU3 & WM3).
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases E2; zify_cond E2; [ clear E2 | exfalso; zsimpl_hyp E2; lia ].
  zsimpl_goal.
  eapply evt_cut.
  { eapply (turnB MEMC MEMS STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 sp0
              (Z_to_bv 64 c) _ (Z_to_bv 64 (2147483639 - 3 * c))
              (base + c) 2 (3 * c) lo (8 + 3 * c + 1 + 1) (3 * w - 3 * c - 1 - 1) (8 + 3 * w) vl _ _
              (skipn 34 (skipn 34 rs)) _ _ _);
      first [ reflexivity | exact Hch | eassumption | idtac ].
    all: turnB_side w vl c 2 HLEG HLEN UC. }
  intros ms' Hp.
  destruct Hp as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13
                  & u14 & u15 & m4 & x14 & -> & HV4 & FR04 & SCR4 & FRS4 & DONE4 & REST4 & HMI4 & ST4 & MU4 & WM4).
  zstep. zstep. zstep. zstep. zstep. zstep.
  if_cases E3; zify_cond E3; [ exfalso; zsimpl_hyp E3; lia | clear E3 ].
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  pose proof (bytes_at_bound rsegs _ _ _ HV4) as BV. rewrite HLEN, Z2Nat.id in BV by lia.
  rewrite (ga_row_eq base vl c 0), (ga_row_eq base vl c 1), (ga_row_eq base vl c 2) in DONE4 by lia.
  change (Z.to_nat 0) with 0%nat in DONE4. change (Z.to_nat 1) with 1%nat in DONE4.
  change (Z.to_nat 2) with 2%nat in DONE4.
  rewrite (prefixB_step base vl (Z.to_nat c)) in DONE4 by lia.
  replace (S (Z.to_nat c)) with (Z.to_nat (c + 1)) in DONE4 by lia.
  replace (34 * (8 + 3 * c + 1 + 1 + 1)) with (34 * (8 + 3 * (c + 1))) in DONE4 by lia.
  replace (bv_unsigned sw + 34 * (8 + 3 * c + 1 + 1 + 1)) with (bv_unsigned sw + 34 * (8 + 3 * (c + 1))) in REST4
    by lia.
  replace (34 * (3 * w - 3 * c - 1 - 1 - 1)) with (34 * (3 * w - 3 * (c + 1))) in REST4 by lia.
  if_cases E; zify_cond E; zsimpl_hyp E.
  - assert (Hne : c + 1 < w) by lia. clear E.
    zsimpl_goal.
    match type of FR04 with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5] =>
      apply (rw_cells_merge rsegs _ _ [] [c1; c2; c3] [c4; c5]) in FR04 end.
    cbn [cells_size csize Nat.add app] in FR04.
    zsimpl_hyp FR04.
    replace (2147483639 - 3 * c + -3) with (2147483639 - 3 * (c + 1)) in FR04 by lia.
    eapply (IH (c + 1)).
    { lia. }
    { lia. }
    { lia. }
    { reflexivity. }
    { first [ reflexivity | f_equal; lia ]. }
    { f_equal. lia. }
    { exact HV4. }
    { exact FR04. }
    { exact SCR4. }
    { exact FRS4. }
    { exact DONE4. }
    { exact REST4. }
    { exact HMI4. }
    { exact ST4. }
    { exact MU4. }
    { exact WM4. }
  - assert (Heq : c + 1 = w) by lia. clear E.
    zstep.
    zsimpl_goal.
    eapply evt_mono.
    { eapply bgs_exit.
      { lia. }
      { eapply (proj2 (rw_cells_app _ _ _ _)). split; [exact FR04|].
        cbn [cells_size csize Nat.add].
        replace (bv_unsigned sp0 + -1632 + Z.of_nat 36) with (bv_unsigned sp0 + -1596) by lia. exact SCR4. }
      { reflexivity. }
      { exact FRS4. }
      { exact ST4. }
      { lia. } }
    intros ms' Hx.
    destruct Hx as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & -> & STF).
    unfold bgs_post. rewrite HOK.
    do 15 eexists. eexists. split; [reflexivity|].
    split; [exact WM4|]. split; [exact HMI4|]. split; [exact STF|].
    split; [eapply row_keep; [exact HROW | exact MU4 | cbn [disjoint_from]; repeat split; lia]|].
    split.
    { f_equal. lia. }
    split.
    { unfold REAC_CTRL_BUILD_GRANT_SWEEP_STACK. exact MU4. }
    rewrite <- prefixB_SWEEP. rewrite <- Heq. exact DONE4.
Qed.
