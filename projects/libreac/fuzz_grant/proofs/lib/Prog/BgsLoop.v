From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel RgLemmas
  memcpy_c memset_c reac_ctrl_stamp_headamp_c reac_ctrl_build_grant_sweep_c BgsTurn.
Import ListNotations.
Open Scope Z_scope.
Definition saved_cells (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma bgs_exit : forall (ra0 sp0 gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word)
    (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (cs : list cell),
  1616 <= bv_unsigned sp0 ->
  rw_cells rsegs m (bv_unsigned sp0 + -1616) cs -> cells_size cs = 1512%nat ->
  rw_cells rsegs m (bv_unsigned sp0 + -104) (saved_cells ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o) ->
  stk rsegs m lo (bv_unsigned sp0 + -1616) -> lo <= bv_unsigned sp0 + -1616 ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s0o s1o r a1' a2' a3' a4' a5' a6' a7'
                     s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o t3' t4' t5' t6')
                F (ret_pc ra0) fc None m (seg_rom rsegs) /\
       stk rsegs m lo (bv_unsigned sp0))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -1616)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14128) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp0 gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o
    ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo cs HSP HCS Hcs HFRS ST HLO.
  pose proof (bv_unsigned_in_range 64 sp0) as Rsp. unfold bv_modulus in Rsp.
  unfold saved_cells in HFRS.
  assert (J : rw_cells rsegs m (bv_unsigned sp0 + -1616)
                (cs ++ [C8 s11o; C8 s10o; C8 s9o; C8 s8o; C8 s7o; C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra0])).
  { apply rw_cells_app. split; [exact HCS|]. rewrite Hcs.
    replace (bv_unsigned sp0 + -1616 + Z.of_nat 1512) with (bv_unsigned sp0 + -104) by lia. exact HFRS. }
  pose proof (stk_release rsegs m lo (bv_unsigned sp0 + -1616) _ ST J HLO) as ST2.
  rewrite cells_size_app, Hcs in ST2. cbn [cells_size csize Nat.add] in ST2.
  replace (bv_unsigned sp0 + -1616 + Z.of_nat 1616) with (bv_unsigned sp0) in ST2 by lia.
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

Lemma img_ack : ro_bytes rsegs 0x1057c HEAD_ACK34.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma img_mark : ro_bytes rsegs 0x1059e HEAD_MARK34.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma img_gb : ro_bytes rsegs 0x10470 GBall.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma prefixB1 : forall base vl, 0 <= base < 256 ->
  prefixB base vl 1 =
  ((((HEAD_ACK34 ++ GA base 0 (vz vl 0)) ++ GA base 1 (vz vl 1)) ++ GA base 2 (vz vl 2)) ++ HEAD_MARK34) ++ GBall.
Proof.
  intros base vl Hb. unfold prefixB, ga_chan, ga_row. cbn [seq map concat Nat.sub]. rewrite app_nil_r.
  change (Z.of_nat 0) with 0. change (Z.of_nat 1) with 1. change (Z.of_nat 2) with 2.
  change (3 * 0 + 0)%nat with 0%nat. change (3 * 0 + 1)%nat with 1%nat. change (3 * 0 + 2)%nat with 2%nat.
  rewrite Z.add_0_r, Z.mod_small by lia. rewrite !app_assoc. reflexivity.
Qed.

Lemma bgs_loopB : memcpy_contract -> memset_contract -> reac_ctrl_stamp_headamp_contract ->
  forall (ra0 sp0 gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (sw vals : word) (M base w lo : Z) (vl : list byte),
    sweep_ok sw vals M base w = true ->
    0 <= base < 256 -> int32 w ->
    lo + 1888 <= bv_unsigned sp0 -> 0 <= lo -> bv_unsigned sp0 mod 16 = 0 ->
    length vl = Z.to_nat (3 * w) -> vals_legal (Z.to_nat w) vl ->
    (bv_unsigned sw + 34 * (8 + 3 * w) <= lo \/ bv_unsigned sp0 <= bv_unsigned sw) ->
    (bv_unsigned vals + 3 * w <= lo \/ bv_unsigned sp0 <= bv_unsigned vals) ->
    (bv_unsigned vals + 3 * w <= bv_unsigned sw \/ bv_unsigned sw + 34 * (8 + 3 * w) <= bv_unsigned vals) ->
    bytes_at rsegs m0 CTRL_ROW CTRL_ROW_BYTES ->
    (CTRL_ROW + 24 <= bv_unsigned sp0 - 1888 \/ bv_unsigned sp0 <= CTRL_ROW) ->
    (bv_unsigned sw + 34 * (8 + 3 * w) <= CTRL_ROW \/ CTRL_ROW + 24 <= bv_unsigned sw) ->
    forall (d : nat) (c : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (m : word -> option byte) (x0 x1 rs : list byte),
      Z.of_nat d = w - c -> 1 <= c -> c < w ->
      s0 = Z_to_bv 64 w -> s1 = Z_to_bv 64 base -> a0 = Z_to_bv 64 c ->
      s5 = Z_to_bv 64 (bv_unsigned sp0 + -1580) -> s6 = Z_to_bv 64 34 -> s8 = Z_to_bv 64 3 ->
      bv_unsigned s9 = bv_unsigned vals + 3 * c -> s10 = Z_to_bv 64 (8 + 3 * c) ->
      bytes_at rsegs m (bv_unsigned vals) vl ->
      rw_cells rsegs m (bv_unsigned sp0 + -1616) [CB 20 x0] ->
      rw_cells rsegs m (bv_unsigned sp0 + -1596) [CB 1492 x1] ->
      rw_cells rsegs m (bv_unsigned sp0 + -104) (saved_cells ra0 s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o) ->
      rw_cells rsegs m (bv_unsigned sw) [CB (Z.to_nat (34 * (8 + 3 * c))) (prefixB base vl (Z.to_nat c))] ->
      rw_cells rsegs m (bv_unsigned sw + 34 * (8 + 3 * c)) [CB (Z.to_nat (34 * (3 * w - 3 * c))) rs] ->
      mem_inv rsegs m ->
      stk rsegs m lo (bv_unsigned sp0 + -1616) ->
      munch [(bv_unsigned sp0 - 1888, bv_unsigned sp0); (bv_unsigned sw, bv_unsigned sw + 34 * (8 + 3 * w))] m0 m ->
      wmono rsegs m0 m ->
      evt rsegs (bgs_post ra0 sp0 gp tp s0o s1o s2o s3o s4o s5o s6o s7o s8o s9o s10o s11o F fc m0 sw vals M base w lo vl)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -1616)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 sw s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x14094) fc None m (seg_rom rsegs)).
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
    intros c ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m x0 x1 rs
      Hd Hc Hcw -> -> -> -> -> -> H9 -> HV FR0 SCR FRS DONE REST HMI ST MU WM.
  { lia. }
  pose proof (rw_cells_bound rsegs m _ _ REST) as BR. cbn [cells_size csize] in BR.
  rewrite Nat.add_0_r, Z2Nat.id in BR by lia.
  zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.
  assert (Hch : Z_to_bv 64 (Z.land (base + c) 255) = Z_to_bv 64 (base + c)).
  { f_equal. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  eapply evt_cut.
  { eapply (turnB MEMC MEMS STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 sp0 vals
              (base + c) 0 (3 * c) lo (8 + 3 * c) (3 * w - 3 * c) (8 + 3 * w) vl _ (prefixB base vl (Z.to_nat c)) rs
              _ _).
    { reflexivity. }
    { exact Hch. }
    { reflexivity. }
    { reflexivity. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { rewrite unsigned_lit by lia. lia. }
    { exact H9. }
    { rewrite HLEN. lia. }
    { apply (legal_at w vl c 0 HLEG); lia. }
    { exact LO. }
    { exact Hlo. }
    { exact HM16. }
    { assumption. }
    { eassumption. }
    { reflexivity. }
    { eassumption. }
    { eassumption. }
    { reflexivity. }
    { eassumption. }
    { eassumption. }
    { assumption. }
    { assumption. }
    { exact D1. }
    { exact D2'. }
    { exact D3'. }
    { assumption. }
    { assumption. }
    { exact HROW. }
    { exact HROWD. }
    { exact HROWR. } }
  intros ms' Hp.
  destruct Hp as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s7' & t3' & t4' & t5' & t6'
                  & m2 & x1' & -> & HV2 & FR02 & SCR2 & FRS2 & DONE2 & REST2 & HMI2 & ST2 & MU2 & WM2).
  zstep. zstep. zstep. zstep.
  if_true.
  eapply evt_cut.
  { eapply (turnB MEMC MEMS STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 sp0 vals
              (base + c) 1 (3 * c) lo (8 + 3 * c + 1) (3 * w - 3 * c - 1) (8 + 3 * w) vl _ _ (skipn 34 rs) _ _).
    { reflexivity. }
    { exact Hch. }
    { reflexivity. }
    { reflexivity. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { rewrite unsigned_lit by lia. lia. }
    { exact H9. }
    { rewrite HLEN. lia. }
    { apply (legal_at w vl c 1 HLEG); lia. }
    { exact LO. }
    { exact Hlo. }
    { exact HM16. }
    { exact HV2. }
    { exact FR02. }
    { reflexivity. }
    { exact SCR2. }
    { exact FRS2. }
    { reflexivity. }
    { exact DONE2. }
    { replace (3 * w - 3 * c - 1) with (3 * w - 3 * c - 1) by lia.
      replace (34 * (3 * w - 3 * c - 1)) with (34 * (3 * w - 3 * c - 1)) by lia. exact REST2. }
    { exact HMI2. }
    { exact ST2. }
    { exact D1. }
    { exact D2'. }
    { exact D3'. }
    { exact MU2. }
    { exact WM2. }
    { exact HROW. }
    { exact HROWD. }
    { exact HROWR. } }
  intros ms' Hp.
  destruct Hp as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & s7'' & t3'' & t4''
                  & t5'' & t6'' & m3 & x1'' & -> & HV3 & FR03 & SCR3 & FRS3 & DONE3 & REST3 & HMI3 & ST3 & MU3 & WM3).
  zstep. zstep. zstep. zstep.
  if_true.
  eapply evt_cut.
  { eapply (turnB MEMC MEMS STAMP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 sp0 vals
              (base + c) 2 (3 * c) lo (8 + 3 * c + 1 + 1) (3 * w - 3 * c - 1 - 1) (8 + 3 * w) vl _ _
              (skipn 34 (skipn 34 rs)) _ _).
    { reflexivity. }
    { exact Hch. }
    { reflexivity. }
    { reflexivity. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { lia. }
    { rewrite unsigned_lit by lia. lia. }
    { exact H9. }
    { rewrite HLEN. lia. }
    { apply (legal_at w vl c 2 HLEG); lia. }
    { exact LO. }
    { exact Hlo. }
    { exact HM16. }
    { exact HV3. }
    { exact FR03. }
    { reflexivity. }
    { exact SCR3. }
    { exact FRS3. }
    { reflexivity. }
    { exact DONE3. }
    { exact REST3. }
    { exact HMI3. }
    { exact ST3. }
    { exact D1. }
    { exact D2'. }
    { exact D3'. }
    { exact MU3. }
    { exact WM3. }
    { exact HROW. }
    { exact HROWD. }
    { exact HROWR. } }
  intros ms' Hp.
  destruct Hp as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13
                  & u14 & u15 & m4 & x14 & -> & HV4 & FR04 & SCR4 & FRS4 & DONE4 & REST4 & HMI4 & ST4 & MU4 & WM4).
  zstep. zstep. zstep. zstep.
  if_false.
  zstep. zstep. zstep. zstep. zstep. zstep.
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
  if_cases E.
  - assert (Hne : c + 1 <> w).
    { intro Heq. subst w. unfold bv_eqb in E. rewrite Z.eqb_refl in E. discriminate. }
    destruct (rw_cells_forget _ _ _ _ FR04) as (x0' & FR05). cbn [cells_size csize Nat.add] in FR05.
    eapply (IH (c + 1)).
    { lia. }
    { lia. }
    { lia. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { rewrite unsigned_lit by lia. lia. }
    { rewrite swrap32_id by lia. f_equal. lia. }
    { exact HV4. }
    { exact FR05. }
    { exact SCR4. }
    { exact FRS4. }
    { exact DONE4. }
    { exact REST4. }
    { exact HMI4. }
    { exact ST4. }
    { exact MU4. }
    { exact WM4. }
  - assert (Heq : c + 1 = w).
    { unfold bv_eqb in E. apply negb_false_iff in E. apply Z.eqb_eq in E.
      rewrite !unsigned_lit in E by lia. exact E. }
    zstep.
    eapply evt_mono.
    { eapply bgs_exit.
      { lia. }
      { eapply (proj2 (rw_cells_app _ _ _ _)). split; [exact FR04|].
        cbn [cells_size csize Nat.add].
        replace (bv_unsigned sp0 + -1616 + Z.of_nat 20) with (bv_unsigned sp0 + -1596) by lia. exact SCR4. }
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
    { rewrite (swrap32_id (8 + 3 * c + 1)) by lia. rewrite (Z.mod_small (8 + 3 * c + 1)) by lia.
      rewrite (swrap32_id (8 + 3 * c + 1 + 1)) by lia. rewrite (Z.mod_small (8 + 3 * c + 1 + 1)) by lia.
      rewrite (swrap32_id (8 + 3 * c + 1 + 1 + 1)) by lia. f_equal. lia. }
    split.
    { unfold REAC_CTRL_BUILD_GRANT_SWEEP_STACK. exact MU4. }
    rewrite <- prefixB_SWEEP. rewrite <- Heq. exact DONE4.
Qed.
