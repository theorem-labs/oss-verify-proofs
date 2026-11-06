From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import memcpy_c read_mac_c.
Import ListNotations.
Open Scope Z_scope.

Lemma base_ro : ro_bytes rsegs 0x10398 mac_base.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma land7 : forall c, 0 <= c -> c mod 8 = 0 -> Z.land c 7 = 0.
Proof. intros c Hc H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma notmac_ltu : forall (x : word) mac i, bv_unsigned x = 2^64 - 1 - mac -> 0 <= i <= 5 -> mac + 6 <= 2^64 ->
  bv_ltu x (Z_to_bv 64 i) = false.
Proof.
  intros x mac i Hx Hi Hm. unfold bv_ltu. rewrite Hx, unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.

Lemma notmac_val : forall mac, 0 <= mac < 2^64 ->
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 mac)) 18446744073709551615)) = 2^64 - 1 - mac.
Proof.
  intros mac Hm. rewrite (unsigned_lit mac) by lia. rewrite zb_lxor_ones by lia. rewrite unsigned_lit by lia. lia.
Qed.

Lemma u8arr_split : forall m A bs k, (k <= length bs)%nat -> u8arr rsegs m A bs ->
  u8arr rsegs m A (firstn k bs) /\ u8arr rsegs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k Hk [Hb Hw]. rewrite <- (firstn_skipn k bs) in Hb. apply bytes_at_app in Hb. destruct Hb as [H1 H2].
  rewrite length_firstn in H2. replace (Nat.min k (length bs)) with k in H2 by lia.
  destruct Hw as (Wa & Wn & W).
  split; split; try assumption.
  - split; [lia|]. split; [rewrite length_firstn; lia|]. intros i Hi. apply W. rewrite length_firstn in Hi. lia.
  - split; [lia|]. split; [rewrite length_skipn; lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply W. rewrite length_skipn in Hi. lia.
Qed.

Lemma u8arr_merge : forall m A bs1 bs2, u8arr rsegs m A bs1 -> u8arr rsegs m (A + Z.of_nat (length bs1)) bs2 ->
  u8arr rsegs m A (bs1 ++ bs2).
Proof.
  intros m A bs1 bs2 [B1 (W1a & W1n & W1)] [B2 (W2a & W2n & W2)]. split.
  - apply bytes_at_app. split; assumption.
  - rewrite length_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (length bs1))) as [L|G].
    + apply W1. lia.
    + replace (A + i) with (A + Z.of_nat (length bs1) + (i - Z.of_nat (length bs1))) by lia. apply W2. lia.
Qed.

Lemma stk_fill : forall m m' lo hi a bs, stk rsegs m lo hi -> munch [(a, a + Z.of_nat (length bs))] m m' ->
  wmono rsegs m m' -> bytes_at rsegs m' a bs -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi a bs (H1 & H2 & H) MU WM HB. pose proof HB as (Ba & Bl & BB). split; [lia|]. split; [lia|].
  intros x Hx. destruct (H x Hx) as [Hw [b Hb]]. split; [apply WM; exact Hw|].
  destruct (Z.leb_spec a x); destruct (Z.ltb_spec x (a + Z.of_nat (length bs))).
  - replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia. rewrite BB by lia.
    destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|]. apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
  - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
Qed.

Lemma upd_prefix : forall (out junk : list byte) i b, (i < length out)%nat -> length out = length junk ->
  nth_error out i = Some b ->
  upd (firstn i out ++ skipn i junk) i b = firstn (S i) out ++ skipn (S i) junk.
Proof.
  intros out junk i b Hi Hl Hn.
  destruct (nth_error_split out i b Hn) as (pre & post & -> & Hpre). subst i.
  rewrite length_app in Hl. cbn [length] in Hl.
  rewrite firstn_app_exact.
  rewrite upd_firstn_skipn by (rewrite length_app, length_skipn; lia).
  rewrite firstn_app_exact.
  rewrite skipn_app, skipn_all2 by lia. rewrite skipn_skipn. cbn [app].
  rewrite firstn_app, firstn_all2 by lia. replace (S (length pre) - length pre)%nat with 1%nat by lia. cbn [firstn].
  rewrite <- app_assoc. cbn [app]. repeat f_equal. all: lia.
Qed.

Definition out6 (pl : list byte) : list byte := firstn 6 (pl ++ repeat (Z_to_bv 8 0) 6).

Lemma out6_length : forall pl, length (out6 pl) = 6%nat.
Proof. intros pl. unfold out6. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma out6_pl : forall pl i b, (i < 6)%nat -> nth_error pl i = Some b -> nth_error (out6 pl) i = Some b.
Proof.
  intros pl i b Hi H. unfold out6. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i 6); [|lia].
  rewrite nth_error_app1; [exact H|]. apply nth_error_Some. rewrite H. discriminate.
Qed.

Lemma out6_zero : forall pl i, (i < 6)%nat -> (length pl <= i)%nat -> nth_error (out6 pl) i = Some (Z_to_bv 8 0).
Proof.
  intros pl i Hi H. unfold out6. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i 6); [|lia].
  rewrite nth_error_app2 by lia. apply nth_error_repeat. lia.
Qed.

Lemma zxb0 : Z_to_bv 64 0 = zxb (Z_to_bv 8 0).
Proof. apply bv_eq. reflexivity. Qed.

Lemma wr1 : forall W m0 m a b lo hi,
  munch W m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> stk rsegs m lo hi ->
  store_ok rsegs m (wa a) 1 = true -> 0 <= a -> a + 1 <= 2^64 -> inside W a 1 ->
  munch W m0 (write_to_mem m (wa a) [b]) /\ wmono rsegs m0 (write_to_mem m (wa a) [b]) /\
  mem_inv rsegs (write_to_mem m (wa a) [b]) /\ stk rsegs (write_to_mem m (wa a) [b]) lo hi.
Proof.
  intros W m0 m a b lo hi MU WM HI ST HS Ha Hb Hin. split; [|split; [|split]].
  - apply munch_write; [exact MU | exact Ha | cbn; lia | exact Hin].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact HI | exact HS].
  - apply stk_write; [exact ST | exact Ha | cbn; lia].
Qed.

Lemma first1 : forall (pl : list byte) b z, nth_error pl 0 = Some b -> firstn 1 (pl ++ [z]) = [b].
Proof. intros pl b z H. destruct pl as [|x r]; [discriminate|]. cbn [nth_error] in H. injection H as <-. reflexivity. Qed.

Lemma first0 : forall (pl : list byte) z, length pl = 0%nat -> firstn 1 (pl ++ [z]) = [z].
Proof. intros pl z H. destruct pl as [|x r]; cbn in H |- *; [reflexivity | discriminate]. Qed.

Lemma len_mix : forall (out junk : list byte) k, length out = 6%nat -> length junk = 6%nat -> (k <= 6)%nat ->
  length (firstn k out ++ skipn k junk) = 6%nat.
Proof. intros out junk k H1 H2 Hk. rewrite length_app, length_firstn, length_skipn. lia. Qed.

Ltac curmem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => mm end.

Ltac dj := simpl_sizes; cbn [disjoint_from]; repeat split; lia.

Theorem read_mac_holds : memcpy_contract -> read_mac_contract.
Proof.
  intros MEMCPY. unfold read_mac_contract, READ_MAC, READ_MAC_FRAME, MAC_BASE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo c p n mac pl junk -> -> CA CUR MACc HB HL HP HI ST LO D1 D2 D3 D4 D5 D6 D7.
  unfold apart in D1, D2, D3, D4, D5, D6, D7.
  pose proof (rw_cells_bound rsegs m c _ CUR) as BC. cbn [cells_size csize Nat.add] in BC.
  change (Z.of_nat 16) with 16 in BC.
  pose proof (rw_cells_bound rsegs m mac _ MACc) as BM. cbn [cells_size csize Nat.add] in BM.
  change (Z.of_nat 6) with 6 in BM.
  pose proof MACc as [[[LJ _] _] _]. cbn [cell_wf] in LJ.
  pose proof (bytes_at_bound rsegs m p pl HB) as BP. rewrite HL in BP.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  assert (Hn : 0 <= n < 2^64) by (destruct (Z.leb_spec 1 n); [specialize (HP ltac:(lia)); lia | lia]).
  assert (HBp : 1 <= n -> bytes_at rsegs m p pl) by (intros; exact HB). clear HB.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (c, c + 16); (mac, mac + 6)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 6 step.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => remember j as fj eqn:Efj; clear Efj end.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  assert (EPI : forall m' (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells rsegs m' (bv_unsigned sp + -32) [CB 8 fj; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m' lo (bv_unsigned sp + -32) ->
    munch [(bv_unsigned sp + -32, bv_unsigned sp); (c, c + 16); (mac, mac + 6)] m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' ->
    rw_cells rsegs m' c [C8 (Z_to_bv 64 (p + read_mac_used a1 n)); C8 (Z_to_bv 64 (n - read_mac_used a1 n))] ->
    rw_cells rsegs m' mac [CB 6 (read_mac_out a1 pl)] ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x139c0) fc None m' (seg_rom rsegs))).
  { intros m' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 FR1 ST1 MU1 WM1 HI1 CUR1 MAC1.
    clear FR ST CUR MACc HI MU WM.
    do 4 step.
    release_frame FR1 ST1 (bv_unsigned sp).
    step.
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact ST1|]. split; [exact HI1|]. split; [exact CUR1|exact MAC1]. }
  step.
  unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.eqb_spec (bv_unsigned a1) 0) as [A0|A0]; cbn [negb].
  - assert (RU : read_mac_used a1 n = Z.min 1 n) by (unfold read_mac_used; rewrite A0; reflexivity).
    assert (RO : read_mac_out a1 pl = mac_base ++ firstn 1 (pl ++ [Z_to_bv 8 0]))
      by (unfold read_mac_out; rewrite A0; reflexivity).
    do 5 step.
    let mm := curmem in rename mm into M.
    pose proof (u8arr_of_rw_cells rsegs M mac 6 junk MACc) as MA.
    destruct (u8arr_split M mac junk 5 ltac:(lia) MA) as [MA5 MA1]. clear MA MACc.
    pose proof (rw_cells_of_u8arr rsegs M mac _ MA5) as R5. rewrite length_firstn in R5.
    replace (Nat.min 5 (length junk)) with 5%nat in R5 by lia.
    pose proof (rw_cells_of_u8arr rsegs M _ _ MA1) as R1. rewrite length_skipn in R1.
    replace (length junk - 5)%nat with 1%nat in R1 by lia. replace (mac + Z.of_nat 5) with (mac + 5) in R1 by lia.
    clear MA5 MA1.
    pose proof (ro_bytes_at rsegs M 0x10398 mac_base HI ltac:(lia) ltac:(cbn; lia) base_ro) as HBASE.
    eapply evt_cut.
    { eapply MEMCPY.
      - rewrite unsigned_lit by lia. exact HBASE.
      - reflexivity.
      - rewrite (unsigned_lit mac) by lia. exact R5.
      - rewrite !unsigned_lit by lia. lia.
      - exact HI. }
    intros ms' Hp. unfold memcpy_post in Hp.
    destruct Hp as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & M2 & -> & MU2 & WM2
                    & HI2 & MB2 & _).
    replace (ret_pc (Z_to_bv 64 0x1397c)) with (Z_to_bv 64 0x1397c) by (apply bv_eq; vm_compute; reflexivity).
    rewrite (unsigned_lit mac) in MU2, MB2 by lia.
    change (bv_unsigned (Z_to_bv 64 5)) with 5 in MU2. change (Z.to_nat (bv_unsigned (Z_to_bv 64 5))) with 5%nat in MB2.
    pose proof (rw_cells_transport rsegs _ M M2 _ _ FR MU2 WM2 ltac:(dj)) as FR2.
    pose proof (rw_cells_transport rsegs _ M M2 _ _ CUR MU2 WM2 ltac:(dj)) as CUR2.
    pose proof (rw_cells_transport rsegs _ M M2 _ _ R1 MU2 WM2 ltac:(dj)) as R12.
    pose proof (stk_fill M M2 lo (bv_unsigned sp + -32) mac mac_base ST MU2 WM2
                  (proj1 (u8arr_of_rw_cells rsegs M2 mac _ _ MB2))) as ST2.
    assert (MU3 : munch [(bv_unsigned sp + -32, bv_unsigned sp); (c, c + 16); (mac, mac + 6)] m M2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
      unfold sub_fp. intros x Hx. cbn [outside] in Hx |- *. split; [lia | exact I]. }
    pose proof (wmono_trans rsegs m M M2 WM WM2) as WM3.
    clear FR CUR R1 ST MU2 WM2 MU WM HI HBASE R5.
    rename FR2 into FR, CUR2 into CUR, R12 into R1, ST2 into ST, MU3 into MU, WM3 into WM, HI2 into HI, MB2 into MB.
    step.
    rewrite (unsigned_lit c) by lia. rewrite land7 by lia.
    step. if_false.
    step. step.
    rewrite eqb_lit by lia.
    assert (TAIL2 : forall M3 b (x10 x11 x12 x13 : word),
      x10 = zxb b -> firstn 1 (pl ++ [Z_to_bv 8 0]) = [b] ->
      rw_cells rsegs M3 (bv_unsigned sp + -32) [CB 8 fj; C8 s1; C8 s0; C8 ra] ->
      stk rsegs M3 lo (bv_unsigned sp + -32) ->
      munch [(bv_unsigned sp + -32, bv_unsigned sp); (c, c + 16); (mac, mac + 6)] m M3 ->
      wmono rsegs m M3 -> mem_inv rsegs M3 ->
      rw_cells rsegs M3 c [C8 (Z_to_bv 64 (p + Z.min 1 n)); C8 (Z_to_bv 64 (n - Z.min 1 n))] ->
      rw_cells rsegs M3 mac [CB 5 mac_base] -> rw_cells rsegs M3 (mac + 5) [CB 1 (skipn 5 junk)] ->
      evt rsegs QQ (MS (mkR (Z_to_bv 64 0x1397c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp y5 y6 y7
                            (Z_to_bv 64 mac) (Z_to_bv 64 c) x10 x11 x12 x13 y14 y15 y16 y17
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x139b4) fc None M3 (seg_rom rsegs))).
    { intros M3 b x10 x11 x12 x13 -> Hb FR3 ST3 MU4 WM4 HI3 CUR3 MB3 R13.
      clear FR ST MU WM HI CUR MB R1.
      pose proof (u8arr_of_rw_cells rsegs M3 _ _ _ R13) as MA3. clear R13.
      pose proof (u8arr_store_ok rsegs M3 (mac + 5) _ 0 (wa (mac + 5)) MA3 ltac:(rewrite length_skipn; lia)
                    ltac:(f_equal; lia)) as HS.
      step. step.
      unfold bv_ltu. rewrite (unsigned_lit mac) by lia. if_false.
      step.
      rewrite le1_zxb.
      pose proof (u8arr_write rsegs M3 (mac + 5) _ 0 b MA3 ltac:(rewrite length_skipn; lia)) as MA4.
      rewrite Z.add_0_r in MA4.
      assert (U1 : upd (skipn 5 junk) (Z.to_nat 0) b = [b]).
      { pose proof (length_skipn 5 junk) as L5. rewrite LJ in L5.
        destruct (skipn 5 junk) as [|j5 [|]]; cbn in L5 |- *; [lia | reflexivity | lia]. }
      rewrite U1 in MA4.
      destruct (wr1 _ m M3 (mac + 5) b lo (bv_unsigned sp + -32) MU4 WM4 HI3 ST3 HS ltac:(lia) ltac:(lia)
                  ltac:(cbn [inside]; lia)) as (MU5 & WM5 & HI5 & ST5).
      pose proof (rw_cells_frame rsegs M3 c _ (mac + 5) [b] CUR3 ltac:(lia) ltac:(cbn; lia) ltac:(simpl_sizes; lia))
        as CUR5.
      pose proof (rw_cells_frame rsegs M3 _ _ (mac + 5) [b] FR3 ltac:(lia) ltac:(cbn; lia) ltac:(simpl_sizes; lia))
        as FR5.
      pose proof (rw_cells_frame rsegs M3 mac _ (mac + 5) [b] MB3 ltac:(lia) ltac:(cbn; lia) ltac:(simpl_sizes; lia))
        as MB5.
      change (write_to_mem M3 (Z_to_bv 64 (mac + 5)) [b]) with (write_to_mem M3 (wa (mac + 5)) [b]).
      remember (write_to_mem M3 (wa (mac + 5)) [b]) as M5 eqn:EM5. clear EM5.
      apply EPI; [exact FR5 | exact ST5 | exact MU5 | exact WM5 | exact HI5 | rewrite RU; exact CUR5 |].
      rewrite RO, Hb. apply (rw_cells_of_u8arr rsegs M5 mac (mac_base ++ [b])).
      apply u8arr_merge; [exact (u8arr_of_rw_cells rsegs M5 mac _ _ MB5) | exact MA4]. }
    destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
    + step.
      apply (TAIL2 _ (Z_to_bv 8 0)); [exact zxb0 | apply first0; lia | exact FR | exact ST | exact MU | exact WM | exact HI
                                      | | exact MB | exact R1].
      replace (Z_to_bv 64 (p + Z.min 1 n)) with (Z_to_bv 64 p) by (f_equal; lia).
      replace (Z_to_bv 64 (n - Z.min 1 n)) with (Z_to_bv 64 n) by (f_equal; lia). exact CUR.
    + destruct (HP ltac:(lia)) as [HP1 HP2].
      do 6 step.
      rewrite ltu_lit by lia. if_false.
      step.
      destruct (nth_error pl 0) as [b0|] eqn:E0; [|apply nth_error_None in E0; lia].
      let mm := curmem in
      pose proof (bytes_at_transport rsegs _ m mm p pl (HBp ltac:(lia)) MU ltac:(dj)) as HBc;
      pose proof (u8ro_read rsegs mm p pl 0 b0 (wa p) HBc E0 ltac:(lia) ltac:(f_equal; lia)) as RD.
      step. step.
      apply (TAIL2 _ b0); [reflexivity | apply first1; exact E0 | exact FR | exact ST | exact MU | exact WM | exact HI
                           | | exact MB | exact R1].
      replace (p + Z.min 1 n) with (p + 1) by lia. replace (n - Z.min 1 n) with (n + -1) by lia. exact CUR.
  - assert (RU : read_mac_used a1 n = Z.min 6 n)
      by (unfold read_mac_used; destruct (Z.eqb_spec (bv_unsigned a1) 0); [lia | reflexivity]).
    assert (RO : read_mac_out a1 pl = out6 pl)
      by (unfold read_mac_out, out6; destruct (Z.eqb_spec (bv_unsigned a1) 0); [lia | reflexivity]).
    step.
    rewrite (unsigned_lit c) by lia. rewrite land7 by lia.
    step. if_false.
    do 3 step.
    let mm := curmem in rename mm into M.
    assert (LOOP : forall (j : nat) i M1 (x11 x14 x15 x16 : word),
      Z.of_nat j = 6 - i -> 0 <= i < 6 -> bv_unsigned x11 = 2^64 - 1 - mac ->
      rw_cells rsegs M1 (bv_unsigned sp + -32) [CB 8 fj; C8 s1; C8 s0; C8 ra] ->
      stk rsegs M1 lo (bv_unsigned sp + -32) ->
      munch [(bv_unsigned sp + -32, bv_unsigned sp); (c, c + 16); (mac, mac + 6)] m M1 ->
      wmono rsegs m M1 -> mem_inv rsegs M1 ->
      rw_cells rsegs M1 c [C8 (Z_to_bv 64 (p + Z.min i n)); C8 (Z_to_bv 64 (n - Z.min i n))] ->
      rw_cells rsegs M1 mac [CB 6 (firstn (Z.to_nat i) (out6 pl) ++ skipn (Z.to_nat i) junk)] ->
      evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (mac + i))
                            (Z_to_bv 64 c) (Z_to_bv 64 i) x11 (Z_to_bv 64 6) (Z_to_bv 64 1) x14 x15 x16 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x13920) fc None M1 (seg_rom rsegs))).
    { clear FR ST MU WM HI CUR MACc.
      induction j as [|j IH]; intros i M1 x11 x14 x15 x16 Hj Hi Hx FR1 ST1 MU1 WM1 HI1 CUR1 MAC1; [lia|].
      assert (TAIL : forall M2 b (x15' x16' : word),
        nth_error (out6 pl) (Z.to_nat i) = Some b ->
        rw_cells rsegs M2 (bv_unsigned sp + -32) [CB 8 fj; C8 s1; C8 s0; C8 ra] ->
        stk rsegs M2 lo (bv_unsigned sp + -32) ->
        munch [(bv_unsigned sp + -32, bv_unsigned sp); (c, c + 16); (mac, mac + 6)] m M2 ->
        wmono rsegs m M2 -> mem_inv rsegs M2 ->
        rw_cells rsegs M2 c [C8 (Z_to_bv 64 (p + Z.min (i + 1) n)); C8 (Z_to_bv 64 (n - Z.min (i + 1) n))] ->
        rw_cells rsegs M2 mac [CB 6 (firstn (Z.to_nat i) (out6 pl) ++ skipn (Z.to_nat i) junk)] ->
        evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (mac + i))
                              (Z_to_bv 64 c) (Z_to_bv 64 i) x11 (Z_to_bv 64 6) (Z_to_bv 64 1) (zxb b) x15' x16' a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x13954) fc None M2 (seg_rom rsegs))).
      { intros M2 b x15' x16' Hb FR2 ST2 MU2 WM2 HI2 CUR2 MAC2.
        clear FR1 ST1 MU1 WM1 HI1 CUR1 MAC1.
        pose proof (u8arr_of_rw_cells rsegs M2 _ _ _ MAC2) as MA2. clear MAC2.
        pose proof (len_mix (out6 pl) junk (Z.to_nat i) (out6_length pl) LJ ltac:(lia)) as LM.
        pose proof (u8arr_store_ok rsegs M2 mac _ i (wa (mac + i)) MA2 ltac:(rewrite LM; lia) eq_refl) as HS.
        step.
        rewrite le1_zxb.
        pose proof (u8arr_write rsegs M2 mac _ i b MA2 ltac:(rewrite LM; lia)) as MA3.
        rewrite upd_prefix in MA3 by (rewrite ?out6_length, ?LJ; first [lia | exact Hb]).
        destruct (wr1 _ m M2 (mac + i) b lo (bv_unsigned sp + -32) MU2 WM2 HI2 ST2 HS ltac:(lia) ltac:(lia)
                    ltac:(cbn [inside]; lia)) as (MU3 & WM3 & HI3 & ST3).
        pose proof (rw_cells_frame rsegs M2 c _ (mac + i) [b] CUR2 ltac:(lia) ltac:(cbn; lia) ltac:(simpl_sizes; lia))
          as CUR3.
        pose proof (rw_cells_frame rsegs M2 _ _ (mac + i) [b] FR2 ltac:(lia) ltac:(cbn; lia) ltac:(simpl_sizes; lia))
          as FR3.
        pose proof (rw_cells_of_u8arr rsegs _ mac _ MA3) as MAC3.
        rewrite (len_mix (out6 pl) junk (S (Z.to_nat i)) (out6_length pl) LJ ltac:(lia)) in MAC3.
        change (write_to_mem M2 (Z_to_bv 64 (mac + i)) [b]) with (write_to_mem M2 (wa (mac + i)) [b]).
        remember (write_to_mem M2 (wa (mac + i)) [b]) as M3 eqn:EM3. clear EM3.
        clear HS MA2 MA3 CUR2 FR2 MU2 WM2 HI2 ST2.
        step. step. step.
        rewrite eqb_lit by lia.
        destruct (Z.eqb_spec (i + 1) 6) as [I6|I6]; cbn [negb].
        - step.
          apply EPI; [exact FR3 | exact ST3 | exact MU3 | exact WM3 | exact HI3 | |].
          + rewrite RU. replace 6 with (i + 1) by lia. exact CUR3.
          + rewrite RO. replace (S (Z.to_nat i)) with 6%nat in MAC3 by lia.
            rewrite firstn_all2 in MAC3 by (rewrite out6_length; lia).
            rewrite skipn_all2 in MAC3 by lia. rewrite app_nil_r in MAC3. exact MAC3.
        - replace (mac + i + 1) with (mac + (i + 1)) by lia.
          apply (IH (i + 1) M3); [lia | lia | exact Hx | exact FR3 | exact ST3 | exact MU3 | exact WM3 | exact HI3
                                 | exact CUR3 |].
          replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact MAC3. }
      step. step.
      rewrite eqb_lit by lia.
      destruct (Z.eqb_spec (n - Z.min i n) 0) as [Z0|Z0]; cbn [negb].
      - step. step.
        rewrite (notmac_ltu x11 mac i Hx ltac:(lia) ltac:(lia)). cbn [negb].
        rewrite zxb0.
        apply (TAIL _ (Z_to_bv 8 0)); [apply out6_zero; lia | exact FR1 | exact ST1 | exact MU1 | exact WM1 | exact HI1
                                      | | exact MAC1].
        replace (Z.min (i + 1) n) with (Z.min i n) by lia. exact CUR1.
      - assert (Iin : i < n) by lia. destruct (HP ltac:(lia)) as [HP1 HP2].
        replace (Z.min i n) with i in * by lia.
        do 5 step.
        rewrite ltu_lit by lia. if_false.
        step.
        destruct (nth_error pl (Z.to_nat i)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
        let mm := curmem in
        pose proof (bytes_at_transport rsegs _ m mm p pl (HBp ltac:(lia)) MU1 ltac:(dj)) as HBc;
        pose proof (u8ro_read rsegs mm p pl i b (wa (p + i)) HBc Eb ltac:(lia) eq_refl) as RD.
        step. step.
        rewrite (notmac_ltu x11 mac i Hx ltac:(lia) ltac:(lia)). cbn [negb].
        step.
        apply (TAIL _ b); [apply out6_pl; [lia | exact Eb] | exact FR1 | exact ST1 | exact MU1 | exact WM1 | exact HI1
                          | | exact MAC1].
        replace (p + Z.min (i + 1) n) with (p + i + 1) by lia.
        replace (n - Z.min (i + 1) n) with (n - i + -1) by lia. exact CUR1. }
    replace (Z_to_bv 64 mac) with (Z_to_bv 64 (mac + 0)) by (f_equal; lia).
    apply (LOOP 6%nat 0 M); [lia | lia | rewrite Z.add_0_r; apply notmac_val; lia | exact FR | exact ST | exact MU
                            | exact WM | exact HI | | exact MACc].
    replace (Z_to_bv 64 (p + Z.min 0 n)) with (Z_to_bv 64 p) by (f_equal; lia).
    replace (Z_to_bv 64 (n - Z.min 0 n)) with (Z_to_bv 64 n) by (f_equal; lia). exact CUR.
Qed.
