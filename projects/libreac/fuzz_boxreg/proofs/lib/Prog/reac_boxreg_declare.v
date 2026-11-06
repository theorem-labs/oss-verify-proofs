From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg BoxregRd BoxregUpd BoxregStep lowest_free_base_c
  memset_c printf_facts_c snprintf_c reac_boxreg_set_name_c reac_boxreg_declare_c reac_boxreg_declare_inv.
Import ListNotations.
Open Scope Z_scope.

Ltac bx_cond :=
  try (match goal with |- context [MS _ _ (if ?c then _ else _) _ _ _ _] =>
    let c' := eval vm_compute in c in change c with c' end; cbv beta iota).


Lemma decl_pin_loop : forall (d : nat) (i : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (r n k b0 : Z)
    (bs : list byte),
  d = Z.to_nat (n - i) -> 0 <= i < n -> n = bx_n bs -> n <= 5 -> bytes_at rsegs m r bs -> length bs = 288%nat ->
  boxreg_B2 bs -> boxreg_B3 bs -> 0 <= b0 -> 0 <= k <= 40 -> b0 + k <= 40 ->
  a1 = Z_to_bv 64 (r + 12 + 56 * i) -> a2 = Z_to_bv 64 (n - i) -> a0 = Z_to_bv 64 (b0 + k) -> s4 = Z_to_bv 64 b0 ->
  (forall j, 0 <= j < i -> ~ meets b0 k (bx_base bs j) (bx_nch bs j)) ->
  (slice_meets bs b0 k -> forall (x11 x12 x13 x14 : word),
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b0 + k)) x11 x12 x13 x14 a5 a6 a7
                          s2 s3 (Z_to_bv 64 b0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13978) fc None m (seg_rom rsegs))) ->
  (~ slice_meets bs b0 k -> forall (x11 x12 x13 x14 : word),
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b0 + k)) x11 x12 x13 x14 a5 a6 a7
                          s2 s3 (Z_to_bv 64 b0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13900) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x138e0) fc None m (seg_rom rsegs)).
Proof.
  induction d as [|d IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Q
      r n k b0 bs Hd Hi Hn Hn5 HB HL H2 H3 Hb0 Hk Hbk E11 E12 E10 E20 HP KM KF; [lia|].
  subst a1 a2 a0 s4.
  pose proof (bytes_at_bound rsegs m r bs HB) as RB. rewrite HL in RB.
  unfold boxreg_B2 in H2.
  destruct (H3 i ltac:(lia)) as (_ & Nk & _ & Nb & Ne).
  pose proof (rd4_bytes_at m r bs (56 * i + 8) HB ltac:(lia) ltac:(rewrite HL; lia)) as BB.
  replace (r + (56 * i + 8)) with (r + 56 * i + 8) in BB by lia.
  change (rd4 bs (56 * i + 8)) with (bx_base bs i) in BB.
  pose proof (rd4_bytes_at m r bs (56 * i + 12) HB ltac:(lia) ltac:(rewrite HL; lia)) as BC.
  replace (r + (56 * i + 12)) with (r + 56 * i + 12) in BC by lia.
  change (rd4 bs (56 * i + 12)) with (bx_nch bs i) in BC.
  pose proof (bx_ov4 _ _ _ BB) as RB1. pose proof (bx_ov4 _ _ _ BC) as RC1.
  assert (NEXT : ~ meets b0 k (bx_base bs i) (bx_nch bs i) -> forall x13 x14 : word,
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (b0 + k)) (Z_to_bv 64 (r + 12 + 56 * i))
                          (Z_to_bv 64 (n - i)) x13 x14 a5 a6 a7 s2 s3 (Z_to_bv 64 b0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x138f4) fc None m (seg_rom rsegs))).
  { intros NM x13 x14. step. step. step.
    rewrite bx_eqb by lia. destruct (Z.eqb_spec (n - i + -1) 0) as [En|En]; bx_cond.
    - apply KF. intros (j & Hj & Hm). destruct (Z.eq_dec j i) as [->|Nj]; [exact (NM Hm)|]. apply (HP j); [lia|exact Hm].
    - eapply (IH (i + 1)) with (r := r) (n := n) (k := k) (b0 := b0) (bs := bs);
        [lia | lia | exact Hn | exact Hn5 | exact HB | exact HL | exact H2 | exact H3 | exact Hb0 | exact Hk | exact Hbk
        | f_equal; lia | f_equal; lia | reflexivity | reflexivity | | exact KM | exact KF].
      intros j Hj. destruct (Z.eq_dec j i) as [->|Nj]; [exact NM|]. apply HP. lia. }
  step. rewrite bx_sx32 by (unfold bx_base; apply rd4_range).
  step. rewrite bx_sx32 by (unfold bx_nch; apply rd4_range).
  step. rewrite swrap_add by lia.
  step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec b0 (bx_nch bs i + bx_base bs i)) as [L1|L1]; bx_cond.
  - step. rewrite bx_lts by lia.
    destruct (Z.ltb_spec (bx_base bs i) (b0 + k)) as [L2|L2]; bx_cond.
    + apply KM. exists i. split; [lia|]. unfold meets. lia.
    + apply NEXT. unfold meets. lia.
  - apply NEXT. unfold meets. lia.
Qed.



Lemma bx_img_shift : forall D n D' n', pf_img_free D n -> D <= D' -> D' + n' <= D + n -> pf_img_free D' n'.
Proof.
  intros D n D' n' H H1 H2. unfold pf_img_free in *. intros i Hi sg Hs C.
  apply (H (D' - D + i) ltac:(lia) sg Hs). replace (D + (D' - D + i)) with (D' + i) by lia. exact C.
Qed.


Lemma bx_img_disj : forall D n a k, pf_img_free D n -> 0 < n -> 0 < k ->
  existsb (fun s : word * word => (bv_unsigned (fst s) <=? a) && (a + k <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs) = true ->
  a + k <= D \/ D + n <= a.
Proof.
  intros D n a k H Hn Hk E. apply existsb_exists in E. destruct E as (sg & Hs & Hb).
  apply andb_true_iff in Hb. destruct Hb as [B1 B2]. apply Z.leb_le in B1, B2. unfold pf_img_free in H.
  destruct (Z_le_gt_dec (a + k) D) as [L1 | L1]; [left; exact L1|].
  destruct (Z_le_gt_dec (D + n) a) as [L2 | L2]; [right; exact L2|].
  exfalso. destruct (Z_le_gt_dec D a) as [L3 | L3].
  - apply (H (a - D) ltac:(lia) sg Hs). lia.
  - apply (H 0 ltac:(lia) sg Hs). lia.
Qed.

Lemma decl_name_eq : forall s,
  upd_bytes (repeat (Z_to_bv 8 0) 32) 0 (pf_bytes (firstn 31 s ++ [0])) = name_field s.
Proof.
  intros s. unfold upd_bytes, name_field, pf_bytes.
  assert (L : length (map (Z_to_bv 8) (firstn 31 s ++ [0])) = S (Nat.min (length s) 31)).
  { rewrite length_map, length_app, length_firstn. cbn [length]. lia. }
  rewrite L. change (firstn 0 (repeat (Z_to_bv 8 0) 32)) with (@nil byte). rewrite app_nil_l.
  change (0 + S (Nat.min (length s) 31))%nat with (S (Nat.min (length s) 31)).
  rewrite map_app, <- app_assoc. f_equal.
  rewrite bx_skipn_repeat_gen. cbn [map app].
  replace (32 - Nat.min (length s) 31)%nat with (S (32 - S (Nat.min (length s) 31)))%nat by lia.
  reflexivity.
Qed.

Lemma decl_row_split : forall b k p s,
  decl_row b k p s = (repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0)
                      ++ le4 (Z_to_bv 64 p)) ++ name_field s.
Proof. intros. unfold decl_row. rewrite <- !app_assoc. reflexivity. Qed.

Theorem reac_boxreg_declare_holds :
  lowest_free_base_contract -> memset_contract -> snprintf_contract -> reac_boxreg_declare_contract.
Proof.
  intros LFB MEMS SNP. unfold reac_boxreg_declare_contract, REAC_BOXREG_DECLARE, DECLARE_K.
  unfold lowest_free_base_contract, LOWEST_FREE_BASE in LFB. unfold memset_contract, MEMSET in MEMS.
  unfold snprintf_contract, SNPRINTF in SNP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r k nm b0 lo bs canary s -> -> -> -> Hk Hb0 Hnm Hr8 HRI HB HW HI HN ST LO LOI SPB DJ2 FR0 MI TM GG GD.
  assert (KST : bx_keep (stk rsegs m lo (bv_unsigned sp))) by exact ST.
  assert (KHW : bx_keep (wr_at rsegs m r 288)) by exact HW.
  pose proof (bx_img_disj r 288 GOT_GUARD 8 HRI ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as IG1.
  pose proof (bx_img_disj r 288 GUARD 8 HRI ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)) as IG2.
  unfold IMG_END in LOI. unfold GOT_GUARD, GUARD in GG, GD, IG1, IG2.
  pose proof (bytes_at_bound rsegs m r bs HB) as RB.
  destruct HI as [[HL [H1 [H2 [H3 [H4 [H5 H6]]]]]] H7].
  rewrite HL in RB.
  assert (Hn : 0 <= bx_n bs <= 5) by exact H1.
  assert (Hf40 : 1 <= bx_fabric bs <= 40) by exact H2.
  pose proof (rd4_bytes_at m r bs 284 HB ltac:(lia) ltac:(rewrite HL; lia)) as BF.
  pose proof (rd4_bytes_at m r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as BN.
  change (rd4 bs 284) with (bx_fabric bs) in BF. change (rd4 bs 280) with (bx_n bs) in BN.
  pose proof (rd4_range bs 284) as RFb. change (rd4 bs 284) with (bx_fabric bs) in RFb.
  pose proof (munch_refl [(lo, bv_unsigned sp); (r, r + 288)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  assert (EPI : forall (m' : word -> option byte) (z : Z) (F' : bvmap 5 word) (fc' : bv 32)
     (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
     ((declare_refused bs k b0 /\ z = -1 /\ bytes_at rsegs m' r bs) \/
      (exists b p, declare_placed bs k b0 b p /\ z = bx_n bs /\ bytes_at rsegs m' r (decl_bytes bs b k p s))) ->
     fkeep F F' -> frm0 fc' ->
     rw_cells rsegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     stk rsegs m' lo (bv_unsigned sp + -64) ->
     munch [(lo, bv_unsigned sp); (r, r + 288)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                           x18 (Z_to_bv 64 z) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                      F' (Z_to_bv 64 0x13978) fc' None m' (seg_rom rsegs))).
  { intros m' z F' fc' x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31
      RES FK FM FR' ST' MU' WM' MI'.
    do 9 step. release_frame FR' ST' (bv_unsigned sp). step. step.
    apply evt_done. unfold QQ. do 15 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact FK|]. split; [exact FM|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
    split; [exact (bx_task_munch2 m m' lo (bv_unsigned sp) r TM MU' KST KHW)|].
    split; [exact ST'|].
    destruct RES as [(HR & -> & HB') | (b & p & HP & -> & HB')];
      [left; split; [exact HR|]; split; [reflexivity|exact HB']
      | right; exists b, p; split; [exact HP|]; split; [reflexivity|exact HB']]. }
  carve_frame 64%nat ST.
  do 15 step.
  rewrite bx_wtest by lia.
  destruct (Z.leb_spec 2 k) as [Hk2|Hk2]; [destruct (Z.leb_spec k 40) as [Hk40|Hk40]|]; cbn [andb negb].
  2,3: (eapply EPI; [left; split; [unfold declare_refused; left; intros (_ & Hw & _); lia | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]).
  do 2 step.
  rewrite bx_land1 by lia. rewrite bx_eqb by (pose proof (Z.mod_pos_bound k 2); lia).
  destruct (Z.eqb_spec (k mod 2) 0) as [Hev|Hod]; cbn [negb].
  2: (eapply EPI; [left; split; [unfold declare_refused; left; intros (He & _); apply Hod, bx_even, He | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]).
  pose proof (bx_ov4 _ _ _ BF) as RF.
  step. rewrite bx_sx32 by lia.
  step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec (bx_fabric bs) k) as [Hfk|Hfk]; bx_cond.
  { eapply EPI; [left; split; [unfold declare_refused; left; intros (_ & _ & Hw); lia | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]. }
  assert (WOK : box_width_ok k (bx_fabric bs)) by (split; [apply bx_even; exact Hev | lia]).
  pose proof (bx_ov4 _ _ _ BN) as RN.
  step. rewrite bx_sx32 by lia.
  step. step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec 4 (bx_n bs)) as [Hn5|Hn5]; bx_cond.
  { eapply EPI; [left; split; [unfold declare_refused; right; left; lia | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]. }
  assert (TAIL : forall (b p : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    declare_placed bs k b0 b p ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 r) (Z_to_bv 64 nm)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 k) (Z_to_bv 64 (-1)) (Z_to_bv 64 b0)
                          (Z_to_bv 64 b) (Z_to_bv 64 (bx_n bs)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x1391c) fc None m1 (seg_rom rsegs))).
  { intros b p x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HP.
    pose proof HP as (_ & Hn5' & HC).
    assert (Hp : (p = 1 /\ 0 <= b0) \/ (p = 0 /\ b0 < 0)) by (destruct HC as [(? & _ & ? & _) | (? & ? & _)]; tauto).
    assert (Hbr : 0 <= b /\ b + k <= bx_fabric bs).
    { destruct HC as [(B0 & -> & _ & (R0 & R1 & _)) | (B0 & _ & Bb & Hlf)]; [lia|].
      destruct Hlf as [(E & _) | (_ & L2 & _)]; lia. }
    step. do 5 step. rewrite bx_off56 by lia.
    assert (EP : Z_to_bv 64 (Z.lxor (bv_unsigned (v_slti (Z_to_bv 64 b0) 0)) 1) = Z_to_bv 64 p).
    { unfold v_slti, zsig. rewrite bx_signed by lia.
      destruct Hp as [(-> & B) | (-> & B)]; destruct (Z.ltb_spec b0 0); try lia; reflexivity. }
    rewrite EP.
    assert (KB1 : bx_keep (bytes_at rsegs m1 r bs)) by exact HB.
    pose proof (bx_rw_sub m1 r bs (56 * bx_n bs) 56 HB ltac:(rewrite HL; exact HW) ltac:(lia) ltac:(lia)
                  ltac:(rewrite HL; lia)) as ROW.
    pose proof (bx_rw_sub m1 r bs 280 4 HB ltac:(rewrite HL; exact HW) ltac:(lia) ltac:(lia)
                  ltac:(rewrite HL; lia)) as NF.
    rewrite <- le4_rd4 in NF by (apply bsub_length; rewrite ?HL; lia).
    change (rd4 bs 280) with (bx_n bs) in NF. change (Z.to_nat 56) with 56%nat in ROW.
    change (Z.to_nat 4) with 4%nat in NF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (r + 56 * bx_n bs, r + 56 * bx_n bs + 56); (r + 280, r + 284)] m1)
      as MU1.
    do 4 step.
    eapply evt_cut.
    { eapply MEMS; [ | exact MI ].
      rewrite (unsigned_lit (r + 56 * bx_n bs)) by lia. rewrite (unsigned_lit 56) by lia. exact ROW. }
    intros ms' PO. unfold memset_post in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m2 & E & MUc & WMc
                    & MI2 & RZ).
    subst ms'.
    rewrite (unsigned_lit (r + 56 * bx_n bs)) in MUc, RZ by lia. rewrite (unsigned_lit 56) in MUc, RZ by lia.
    try rewrite (unsigned_lit 0) in RZ by lia. change (Z.to_nat 56) with 56%nat in RZ.
    try change (0 mod 256) with 0 in RZ.
    replace (ret_pc (Z_to_bv 64 80196)) with (Z_to_bv 64 80196) by (apply bv_eq; vm_compute; reflexivity).
    transport_after_call rsegs m1 m2 MUc WMc. clear MUc WMc MI.
    change 56%nat with (24 + 32)%nat in RZ. apply bx_rw_split in RZ. destruct RZ as [R24 R32].
    rewrite bx_firstn_repeat in R24. rewrite bx_skipn_repeat in R32.
    replace (r + 56 * bx_n bs + Z.of_nat 24) with (r + 56 * bx_n bs + 24) in R32 by lia.
    step. step. step. step. rewrite eqb_lit by lia.
    destruct (Z.eqb_spec nm 0) as [N0|N0]; bx_cond.
    - assert (Es : s = []) by (destruct HN as [(_ & ->) | (Hq & _)]; [reflexivity | lia]). subst s.
      step. rewrite bx_sx32 by lia. step. step.
      pose proof (bx_rw_bytes _ _ _ R24) as RB24. cbn [cells_bytes cbytes] in RB24.
      pose proof (bx_rw_bytes _ _ _ R32) as RB32. cbn [cells_bytes cbytes] in RB32. rewrite app_nil_r in RB32.
      pose proof (bx_rw_bytes _ _ _ NF) as NFB. cbn [cells_bytes cbytes] in NFB. rewrite app_nil_r in NFB.
      eapply EPI; [ | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI2].
      right. exists b, p. split; [exact HP|]. split; [reflexivity|].
      unfold decl_bytes. eapply bx_patch2; [exact KB1 | exact MU1 | | | | | ].
      + replace (r + Z.of_nat (Z.to_nat (56 * bx_n bs))) with (r + 56 * bx_n bs) by lia.
        rewrite decl_row_split. apply bytes_at_app. split.
        * eapply bytes_at_ext; [exact RB24|]. rewrite app_nil_r.
          replace (firstn 4 (skipn 4 (skipn 12 (repeat (Z_to_bv 8 0) 24)))) with (le4 (Z_to_bv 64 0))
            by (vm_compute; reflexivity).
          reflexivity.
        * cbn [length]. rewrite !length_app, !length_le4, repeat_length.
          match goal with |- bytes_at _ _ ?a _ => replace a with (r + 56 * bx_n bs + 24) by lia end.
          eapply bytes_at_ext; [exact RB32|]. reflexivity.
      + replace (r + Z.of_nat 280) with (r + 280) by lia. exact NFB.
      + unfold decl_row, name_field. rewrite !length_app, !length_le4, !repeat_length. cbn. lia.
      + rewrite length_le4, HL. lia.
      + intros i Hi Ha Hb. unfold decl_row, name_field in Ha. rewrite !length_app, !length_le4, !repeat_length in Ha.
        cbn in Ha. rewrite length_le4 in Hb. rewrite HL in Hi.
        cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - destruct HN as [(Hq & _) | (_ & SF & SL & slack & SB & SM & SD1 & SD2)]; [lia|].
      pose proof (bytes_at_bound rsegs m nm _ SB) as NB.
      unfold pf_bytes in NB. rewrite !length_app, length_map, length_app in NB. cbn [length] in NB.
      assert (SB0 : bytes_at rsegs m0 nm (pf_bytes (s ++ [0]) ++ slack)).
      { eapply bytes_at_transport; [exact SB | exact MU | ]. cbn [disjoint_from].
        unfold pf_bytes. rewrite !length_app, length_map, length_app. cbn [length].
        split; [lia | split; [lia | exact I]]. }
      pose proof (bx_rw_bytes _ _ _ R32) as RB32. cbn [cells_bytes cbytes] in RB32. rewrite app_nil_r in RB32.
      assert (KD : bx_keep (bytes_at rsegs m0 (r + 56 * bx_n bs + 24) (repeat (Z_to_bv 8 0) 32))) by exact RB32.
      clear RB32.
      assert (SPL : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
      step. step. step. step. step. step.
      assert (U1 : bv_unsigned (Z_to_bv 64 (r + 56 * bx_n bs + 24)) = r + 56 * bx_n bs + 24)
        by (apply unsigned_lit; lia).
      assert (U2 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
      assert (U3 : bv_unsigned (Z_to_bv 64 66309) = 66309) by reflexivity.
      assert (Lw : (length (firstn 31 s) <= 31)%nat) by (rewrite length_firstn; lia).
      eapply evt_cut.
      { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 lo canary [37; 115] [Ps] [APtr s] s
                    (repeat (Z_to_bv 8 0) 32));
        [ rewrite U3; apply ro_bytes_at; [eassumption | lia | cbn; lia | apply ro_bytes_b_sound; vm_compute; reflexivity]
        | unfold RO_LO; rewrite U3; lia
        | unfold RO_END; rewrite U3; cbn [length]; lia
        | reflexivity
        | cbn [pf_args_ok pf_arg_ok]; rewrite (unsigned_lit nm) by lia; rewrite SPL, U1, U2; split; [|exact I];
          split; [exact SF|]; exists slack; split; [exact SB0|]; split; [exact SM|]; split; [lia|]; split; lia
        | cbn; rewrite app_nil_r; reflexivity
        | rewrite U1, U2; change (Z.to_nat 32) with 32%nat; exact R32
        | rewrite U2; lia
        | exact SL
        | rewrite U1; lia
        | rewrite U1, U2, SPL; lia
        | rewrite U1, U2; apply (bx_img_shift r 288); [exact HRI | lia | lia]
        | rewrite SPL; exact ST
        | unfold SNPRINTF_K; rewrite SPL; lia
        | unfold IMG_END; lia
        | rewrite SPL; lia
        | exact FR0
        | eassumption
        | exact (bx_task_munch2 _ _ _ _ _ TM MU KST KHW)
        | eassumption
        | eassumption ]. }
      intros ms' PO. unfold printf_post in PO.
      destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & Ft & fc2 & m3
                      & E & MUc & WMc & MI3 & TM3 & FM3 & FK3 & ST3 & BY3).
      subst ms'. rewrite U1, U2 in MUc, BY3. rewrite SPL in MUc, ST3.
      change (Z.to_nat (32 - 1)) with 31%nat in MUc, BY3.
      replace (ret_pc (Z_to_bv 64 80236)) with (Z_to_bv 64 80236) by (apply bv_eq; vm_compute; reflexivity).
      assert (NM3 : bytes_at rsegs m3 (r + 56 * bx_n bs + 24) (name_field s)).
      { rewrite <- decl_name_eq. eapply bx_patch1; [exact KD | exact MUc | | | ].
        - change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact BY3.
        - rewrite repeat_length. unfold pf_bytes. rewrite length_map, length_app, length_firstn. cbn [length]. lia.
        - intros i Hi Hni. rewrite repeat_length in Hi. unfold pf_bytes in Hni.
          rewrite length_map, length_app, length_firstn in Hni. cbn [length] in Hni.
          cbn [outside]. rewrite length_firstn. split; [lia|]. split; [lia | exact I]. }
      transport_after_call rsegs m0 m3 MUc WMc. clear MUc WMc.
      pose proof (name_field_length s) as LN.
      step. rewrite bx_sx32 by lia. step. step.
      pose proof (bx_rw_bytes _ _ _ R24) as RB24. cbn [cells_bytes cbytes] in RB24.
      pose proof (bx_rw_bytes _ _ _ NF) as NFB. cbn [cells_bytes cbytes] in NFB. rewrite app_nil_r in NFB.
      eapply EPI; [ | exact FK3 | exact FM3 | exact FR | exact ST3 | exact MU | exact WM | eassumption].
      right. exists b, p. split; [exact HP|]. split; [reflexivity|].
      unfold decl_bytes. eapply bx_patch2; [exact KB1 | exact MU1 | | | | | ].
      + replace (r + Z.of_nat (Z.to_nat (56 * bx_n bs))) with (r + 56 * bx_n bs) by lia.
        rewrite decl_row_split. apply bytes_at_app. split.
        * eapply bytes_at_ext; [exact RB24|]. rewrite app_nil_r.
          replace (firstn 4 (skipn 4 (skipn 12 (repeat (Z_to_bv 8 0) 24)))) with (le4 (Z_to_bv 64 0))
            by (vm_compute; reflexivity).
          reflexivity.
        * cbn [length]. rewrite !length_app, !length_le4, repeat_length.
          match goal with |- bytes_at _ _ ?a _ => replace a with (r + 56 * bx_n bs + 24) by lia end.
          exact NM3.
      + replace (r + Z.of_nat 280) with (r + 280) by lia. exact NFB.
      + rewrite decl_row_length. lia.
      + rewrite length_le4, HL. lia.
      + intros i Hi Ha Hb. rewrite decl_row_length in Ha. rewrite length_le4 in Hb. rewrite HL in Hi.
        cbn [outside]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  do 3 step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec b0 0) as [Bn|Bp]; bx_cond.
  - step. step. step.
    eapply evt_cut.
    { eapply LFB; [reflexivity | reflexivity | lia | exact HB | exact HL | exact H1 | exact H2 | exact H3]. }
    intros ms' PO.
    destruct PO as (u5 & u6 & u7 & res & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & E
                    & lf & Elf & Hlf).
    subst ms' res.
    replace (ret_pc (Z_to_bv 64 80148)) with (Z_to_bv 64 80148) by (apply bv_eq; vm_compute; reflexivity).
    assert (Hlfr : -1 <= lf <= 40) by (destruct Hlf as [(-> & _) | (HA & HB' & _)]; unfold boxreg_B2 in H2; lia).
    step. step. rewrite bx_lts by lia.
    destruct (Z.ltb_spec lf 0) as [Ln|Ln]; bx_cond.
    + eapply EPI; [left; split; [unfold declare_refused; right; right; right; split;
                                 [lia | replace (-1) with lf by lia; exact Hlf]
                              | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI].
    + eapply TAIL. split; [exact WOK|]. split; [lia|]. right. split; [lia|]. split; [reflexivity|].
      split; [lia | exact Hlf].
  - step. rewrite swrap_sub by lia.
    step. rewrite bx_lts by lia.
    destruct (Z.ltb_spec (bx_fabric bs - k) b0) as [Fb|Fb]; bx_cond.
    { eapply EPI; [left; split; [unfold declare_refused; right; right; left; split; [lia | intros (_ & Hr & _); lia]
                              | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]. }
    step. rewrite bx_lts by lia.
    destruct (Z.ltb_spec 0 (bx_n bs)) as [Np|Np]; bx_cond.
    + step. rewrite swrap_add by lia. step. step.
      eapply (decl_pin_loop (Z.to_nat (bx_n bs)) 0) with (r := r) (n := bx_n bs) (k := k) (b0 := b0) (bs := bs);
        [lia | lia | reflexivity | lia | exact HB | exact HL | exact H2 | exact H3 | lia | lia | lia
        | f_equal; lia | f_equal; lia | reflexivity | reflexivity | intros; lia | | ].
      * intros SM x11 x12 x13 x14.
        eapply EPI; [left; split; [unfold declare_refused; right; right; left; split; [lia | intros (_ & _ & Hr); exact (Hr SM)]
                                  | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI].
      * intros NSM x11 x12 x13 x14. step. step. eapply TAIL.
        split; [exact WOK|]. split; [lia|]. left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
        split; [lia|]. split; [lia | exact NSM].
    + step. step. eapply TAIL.
      split; [exact WOK|]. split; [lia|]. left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [lia|]. split; [lia|]. intros (j & Hj & _). lia.
Qed.
