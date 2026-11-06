From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c disco_table bcmp_c reac_disco_table_observe_c slot_inv slot_lib uslot_frame uslot_observe.
Import ListNotations.
Open Scope Z_scope.

Ltac nt :=
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
    lazymatch pc with context [bv_eqb ?a ?b] =>
      replace (bv_eqb a b) with true
        by (symmetry; first [ apply so_eqb_refl | (rewrite eqb_lit by lia; apply Z.eqb_eq; lia) ]);
      cbn [negb]
    end
  end.

Lemma eqb_s32 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eqb_spec v 0) as [->|N]; [reflexivity|].
  apply Z.eqb_neq. intros E. apply Z.mod_divide in E; [|lia]. destruct E as [c Ec]. nia.
Qed.

Ltac tk :=
  lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
    lazymatch pc with context [bv_eqb ?a ?b] =>
      replace (bv_eqb a b) with false
        by (symmetry; first [ (rewrite eqb_s32 by lia; apply Z.eqb_neq; lia)
                            | (rewrite eqb_lit by lia; apply Z.eqb_neq; lia) | (vm_compute; reflexivity) ]);
      cbn [negb]
    end
  end.

Lemma le4_s32 : forall z, 0 <= z < 2 ^ 31 -> Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z (Z_to_le_bytes 4 z))) = Z_to_bv 64 z.
Proof.
  intros z Hz. rewrite bytes_le_to_Z_to_le_bytes by lia. change (8 * Z.of_nat 4) with 32.
  rewrite Z.mod_small by lia. rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma own_le : forall ow, 0 <= ow <= 1 ->
  Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z (Z_to_le_bytes 4 (if ow =? 0 then 0 else 1)))) = Z_to_bv 64 ow.
Proof. intros ow H. assert (E : ow = 0 \/ ow = 1) by lia. destruct E as [->| ->]; vm_compute; reflexivity. Qed.

Lemma memcmp_same : forall l, length l = 6%nat -> memcmp_model l l 6 = Some 0.
Proof.
  intros l L. destruct (memcmp6 l l L L) as (v & Hv & Hv0 & _).
  assert (E : v = 0) by (apply Hv0; reflexivity). subst v. exact Hv.
Qed.

Definition r25_post (sp gp tp s0 s1 s2 s3 s4 s6 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X : Z) (T' G : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5' s6 s7' s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 R27) fc None m' (seg_rom rsegs) /\
    munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    rw_cells rsegs m' (X + 544) [CB 400 T'] /\ rw_cells rsegs m' (X + 1056) [CB 24 G].

Lemma uslot_R26 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X ret : Z) (T G T' : list byte),
  sp = Z_to_bv 64 X -> s5 = Z_to_bv 64 ret -> s7 = Z_to_bv 64 (n_of T) ->
  0 < X -> X + 2624 < 2 ^ 63 ->
  length T = 400%nat -> tbl_T1 T -> 8 <= n_of T -> (T', ret) = observe_full T ->
  rw_cells rsegs m (X + 544) [CB 400 T'] -> rw_cells rsegs m (X + 1056) [CB 24 G] ->
  mem_inv rsegs m ->
  evt rsegs (r25_post sp gp tp s0 s1 s2 s3 s4 s6 s8 s9 s10 s11 F fc X T' G m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R25) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X ret T G T' Esp Es5 Es7 HX0 HX1 LT T1 HN E RT RG MI.
  subst sp s5 s7. unfold R25, R27, r25_post in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof T1 as T1'. unfold tbl_T1 in T1'.
  apply rwc_split in RT. destruct RT as (LT2 & HT & WT).
  destruct (full_facts T T' ret LT E) as (_ & Er & E384 & E388 & _ & _). subst ret.
  step. step. rewrite lts_lit by lia. replace (7 <? n_of T) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
  step. nt.
  rdx (X + 544) T' 384 4%nat RN. rewrite E384 in RN.
  step. rewrite lw_val by (apply length_sub; lia).
  change (bv_swrap 32 (bytes_le_to_Z (sub T 384 4))) with (n_of T).
  step. nt. clear RN.
  rdx (X + 544) T' 388 4%nat RV. rewrite E388 in RV.
  revert RV. destruct (Z.eqb_spec (ov_of T) 0) as [Hov|Hov]; intros RV.
  - step. rewrite lw_val by (rewrite length_Z_to_le_bytes; reflexivity).
    step. tk.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [apply rwc_mk; assumption|]. exact RG.
  - step. rewrite lw_val by (apply length_sub; lia).
    change (bv_swrap 32 (bytes_le_to_Z (sub T 388 4))) with (ov_of T).
    pose proof (s32_range T 388) as HOV. change (s32_at T 388) with (ov_of T) in HOV.
    step. tk.
    apply evt_done. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [apply rwc_mk; assumption|]. exact RG.
Qed.

Definition R25_BCMP : Z := 0x144d0.

Lemma uslot_R25_pre :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X n : Z) (T' : list byte),
  sp = Z_to_bv 64 X -> s5 = Z_to_bv 64 1 -> s7 = Z_to_bv 64 n ->
  0 < X -> X + 2624 < 2 ^ 63 -> 0 <= n < 8 ->
  sub T' 384 4 = Z_to_le_bytes 4 (n + 1) ->
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 (nt (X + 544)))] ->
  rw_cells rsegs m (X + 544) [CB 400 T'] ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (X + 544 + 48 * n)) (Z_to_bv 64 (X + 1056)) (Z_to_bv 64 6)
                    a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (X + 544 + 48 * n)) s6 (Z_to_bv 64 (n + 1)) s8 s9 s10 s11
                    t3 t4 t5 t6)
               F (Z_to_bv 64 R25_BCMP) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R25) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X n T' Esp Es5 Es7 HX0 HX1 Hn E384 R200 RT.
  subst sp s5 s7. unfold R25, R25_BCMP in *.
  apply rwc_split in RT. destruct RT as (LT2 & HT & WT).
  step. step. rewrite lts_lit by lia. replace (7 <? n) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. step. rewrite ltu_lit by lia. replace (8 <? n) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step. step. rewrite !shl_w by lia. change (2 ^ 4) with 16. change (2 ^ 6) with 64.
  step. rewrite sub_ww.
  step. step. rewrite ltu_lit by (unfold nt; lia).
  replace (nt (X + 544) <? n * 64 - n * 16) with false by (symmetry; apply Z.ltb_ge; unfold nt; lia). cbv iota.
  step. step. nt.
  rdx (X + 544) T' 384 4%nat RN. rewrite E384 in RN.
  step. rewrite lw_val by (rewrite length_Z_to_le_bytes; reflexivity). rewrite le4_s32 by lia.
  step. rewrite addiw_small by lia.
  step. nt. clear RN.
  replace (n * 64 - n * 16) with (48 * n) by lia.
  step. step. step. step. step.
  apply evt_done. reflexivity.
Qed.

Lemma uslot_R25_cmp : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X now ow n : Z) (T' G : list byte),
  sp = Z_to_bv 64 X -> s9 = Z_to_bv 64 ow ->
  a0 = Z_to_bv 64 (X + 544 + 48 * n) -> a1 = Z_to_bv 64 (X + 1056) -> a2 = Z_to_bv 64 6 ->
  s5 = Z_to_bv 64 (X + 544 + 48 * n) ->
  0 < X -> X + 2624 < 2 ^ 63 -> 0 <= now < 2 ^ 64 -> 0 <= ow <= 1 -> 0 <= n < 8 ->
  length G = 24%nat ->
  (forall d w, 0 <= d -> d + Z.of_nat w <= 48 -> sub T' (48 * n + d) w = sub (new_entry G ow now) d w) ->
  rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
  rw_cells rsegs m (X + 544) [CB 400 T'] -> rw_cells rsegs m (X + 1056) [CB 24 G] ->
  mem_inv rsegs m ->
  evt rsegs (r25_post sp gp tp s0 s1 s2 s3 s4 s6 s8 s9 s10 s11 F fc X T' G m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R25_BCMP) fc None m (seg_rom rsegs)).
Proof.
  intros BCC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X now ow n T' G Esp Es9 Ea0 Ea1 Ea2 Es5 HX0 HX1 Hnow How Hn LG NF RN RT RG MI.
  subst sp s9 a0 a1 a2 s5. unfold R25_BCMP, r25_post in *.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  apply rwc_split in RT. destruct RT as (LT2 & HT & WT).
  apply rwc_split in RG. destruct RG as (_ & HG & WG).
  destruct (new_fields G ow now LG) as (F0 & F8 & F12 & F13 & F14 & F15 & F16 & F20 & F24 & F32 & F40).
  assert (EM0 : sub T' (48 * n) 6 = s_mac G).
  { replace (48 * n) with (48 * n + 0) by lia. rewrite NF by lia. exact F0. }
  step.
  eapply evt_cut.
  { eapply (BCC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (s_mac G) (s_mac G) 0).
    - rewrite unsigned_lit by lia. rewrite <- EM0. apply bytes_at_sub; [exact HT | lia | lia].
    - rewrite unsigned_lit by lia. rewrite <- (Z.add_0_r (X + 1056)). unfold s_mac.
      apply bytes_at_sub; [exact HG | lia | lia].
    - rewrite (unsigned_lit 6) by lia. apply memcmp_same. apply len_mac. exact LG.
    - exact MI. }
  intros ms' PO. unfold memcmp_post in PO.
  destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 &
                  Eq & MUc & WMc & MI2 & B1 & B2).
  subst ms'. clear B1 B2.
  transport_after_call rsegs m m2 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 83156) by (first [lia | reflexivity]).
  step. nt.
  rdx (X + 544) T' (48 * n + 8) 4%nat RA. rewrite NF in RA by lia. rewrite F8 in RA.
  rdx (X + 1056) G 8 4%nat RB.
  step. step. step. nt. clear RA RB.
  rdx (X + 544) T' (48 * n + 12) 1%nat RA. rewrite NF in RA by lia. rewrite F12 in RA.
  rdx (X + 1056) G 12 1%nat RB.
  step. step. step. nt. clear RA RB.
  rdx (X + 544) T' (48 * n + 13) 1%nat RA. rewrite NF in RA by lia. rewrite F13 in RA.
  rdx (X + 1056) G 13 1%nat RB.
  step. step. step. nt. clear RA RB.
  rdx (X + 544) T' (48 * n + 14) 1%nat RA. rewrite NF in RA by lia. rewrite F14 in RA.
  rdx (X + 1056) G 14 1%nat RB.
  step. step. step. nt. clear RA RB.
  rdx (X + 544) T' (48 * n + 15) 1%nat RA. rewrite NF in RA by lia. rewrite F15 in RA.
  rdx (X + 1056) G 15 1%nat RB.
  step. step. step. nt. clear RA RB.
  rdx (X + 544) T' (48 * n + 16) 1%nat RA. rewrite NF in RA by lia. rewrite F16 in RA.
  rdx (X + 1056) G 16 1%nat RB.
  step. step. step. nt. clear RA RB.
  rdx (X + 544) T' (48 * n + 20) 4%nat RA. rewrite NF in RA by lia. rewrite F20 in RA.
  rdx (X + 1056) G 20 4%nat RB.
  step. step. step. nt. clear RA RB.
  rdx (X + 544) T' (48 * n + 24) 4%nat RA. rewrite NF in RA by lia. rewrite F24 in RA.
  step. rewrite !lw_val by first [ (rewrite length_Z_to_le_bytes; reflexivity) | (apply length_sub; lia) ].
  rewrite own_le by lia.
  step. nt. clear RA.
  rdx (X + 544) T' (48 * n + 32) 8%nat RA. rewrite NF in RA by lia. rewrite F32 in RA.
  rewrite le8_lit in RA by lia.
  step. step. step. nt. clear RA.
  rdx (X + 544) T' (48 * n + 40) 8%nat RA. rewrite NF in RA by lia. rewrite F40 in RA.
  rewrite le8_lit in RA by lia.
  step. step. step. nt. clear RA.
  step.
  apply evt_done. do 19 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI2|].
  split; apply rwc_mk; assumption.
Qed.

Lemma uslot_R25_R26 : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X now ow ret : Z) (T G T' : list byte),
  sp = Z_to_bv 64 X -> s5 = Z_to_bv 64 ret -> s9 = Z_to_bv 64 ow -> s7 = Z_to_bv 64 (n_of T) ->
  0 < X -> X + 2624 < 2 ^ 63 -> 0 <= now < 2 ^ 64 -> 0 <= ow <= 1 ->
  length T = 400%nat -> length G = 24%nat -> tbl_T1 T ->
  (8 <= n_of T /\ (T', ret) = observe_full T) \/ (n_of T < 8 /\ (T', ret) = observe_new T G ow now) ->
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 (nt (X + 544)))] ->
  rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
  rw_cells rsegs m (X + 544) [CB 400 T'] -> rw_cells rsegs m (X + 1056) [CB 24 G] ->
  mem_inv rsegs m ->
  evt rsegs (r25_post sp gp tp s0 s1 s2 s3 s4 s6 s8 s9 s10 s11 F fc X T' G m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R25) fc None m (seg_rom rsegs)).
Proof.
  intros BCC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X now ow ret T G T' Esp Es5 Es9 Es7 HX0 HX1 Hnow How LT LG T1 ARM R200 RN RT RG MI.
  pose proof T1 as T1'. unfold tbl_T1 in T1'.
  destruct ARM as [(HN & E) | (HN & E)].
  - exact (uslot_R26 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m X ret T G T' Esp Es5 Es7 HX0 HX1 LT T1 HN E RT RG MI).
  - destruct (new_facts T G ow now T' ret LT LG ltac:(lia) E) as (_ & Er & E384 & _ & NF). subst ret.
    eapply evt_cut.
    { exact (uslot_R25_pre ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m X (n_of T) T' Esp Es5 Es7 HX0 HX1 ltac:(lia) E384 R200 RT). }
    intros ms' ->.
    eapply (uslot_R25_cmp BCC) with (n := n_of T); try eassumption; try reflexivity; lia.
Qed.
