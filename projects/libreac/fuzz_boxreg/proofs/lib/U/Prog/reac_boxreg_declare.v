From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd BoxregUpd BoxregStep lowest_free_base_c
  memset_c printf_facts_c snprintf_c reac_boxreg_set_name_c range_taken_c reac_boxreg_declare_c
  reac_boxreg_declare_inv.
Import ListNotations.
Open Scope Z_scope.

Ltac bx_cond :=
  try (match goal with |- context [MS _ _ (if ?c then _ else _) _ _ _ _] =>
    let c' := eval vm_compute in c in change c with c' end; cbv beta iota).



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



Ltac bx_tac MUc WMc := lazymatch type of MUc with munch _ ?ma ?mb => transport_after_call rsegs ma mb MUc WMc end.

Theorem reac_boxreg_declare_holds :
  range_taken_contract -> lowest_free_base_contract -> memset_contract -> snprintf_contract ->
  reac_boxreg_declare_contract.
Proof.
  intros RT LFB MEMS SNP. unfold reac_boxreg_declare_contract, REAC_BOXREG_DECLARE, DECLARE_K.
  unfold range_taken_contract, RANGE_TAKEN in RT.
  unfold lowest_free_base_contract, LOWEST_FREE_BASE, LOWEST_FREE_BASE_FRAME in LFB.
  unfold memset_contract, MEMSET in MEMS. unfold snprintf_contract, SNPRINTF in SNP.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r k nm b0 lo bs canary s -> -> -> -> Hk Hb0 Hnm Hr8 Hr0 HRI HB HW HI HN ST LO LOI SPB DJ2 FR0 MI TM GG GD.
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
  assert (R4 : r mod 4 = 0) by (Z.div_mod_to_equations; lia).
  pose proof (rd4_bytes_at m r bs 284 HB ltac:(lia) ltac:(rewrite HL; lia)) as BF.
  pose proof (rd4_bytes_at m r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as BN.
  change (rd4 bs 284) with (bx_fabric bs) in BF. change (rd4 bs 280) with (bx_n bs) in BN.
  pose proof (rd4_range bs 284) as RFb. change (rd4 bs 284) with (bx_fabric bs) in RFb.
  pose proof (munch_refl [(lo, bv_unsigned sp); (r, r + 288)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (Hlo & _ & _).
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  assert (EPI : forall (m' : word -> option byte) (z : Z) (F' : bvmap 5 word) (fc' : bv 32) (j0 : list byte)
     (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31 : word),
     ((declare_refused bs k b0 /\ z = -1 /\ bytes_at rsegs m' r bs) \/
      (exists b p, declare_placed bs k b0 b p /\ z = bx_n bs /\ bytes_at rsegs m' r (decl_bytes bs b k p s))) ->
     fkeep F F' -> frm0 fc' ->
     rw_cells rsegs m' (bv_unsigned sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     stk rsegs m' lo (bv_unsigned sp + -64) ->
     munch [(lo, bv_unsigned sp); (r, r + 288)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
                           x18 (Z_to_bv 64 z) x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                      F' (Z_to_bv 64 0x13c84) fc' None m' (seg_rom rsegs))).
  { intros m' z F' fc' j0 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31
      RES FK FM FR' ST' MU' WM' MI'.
    do 8 step. release_frame FR' ST' (bv_unsigned sp). step. step.
    apply evt_done. unfold QQ. do 15 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact FK|]. split; [exact FM|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
    split; [exact (bx_task_munch2 m m' lo (bv_unsigned sp) r TM MU' KST KHW)|].
    split; [exact ST'|].
    destruct RES as [(HR & -> & HB') | (b & p & HP & -> & HB')];
      [left; split; [exact HR|]; split; [reflexivity|exact HB']
      | right; exists b, p; split; [exact HP|]; split; [reflexivity|exact HB']]. }
  carve_frame 64%nat ST.
  do 14 step.
  rewrite bx_wtest by lia.
  destruct (Z.leb_spec 2 k) as [Hk2|Hk2]; [destruct (Z.leb_spec k 40) as [Hk40|Hk40]|]; cbn [andb negb].
  2,3: (eapply EPI; [left; split; [unfold declare_refused; left; intros (_ & Hw & _); lia | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]).
  do 2 step.
  rewrite bx_land1 by lia. rewrite bx_eqb by (pose proof (Z.mod_pos_bound k 2); lia).
  destruct (Z.eqb_spec (k mod 2) 0) as [Hev|Hod]; cbn [negb].
  2: (eapply EPI; [left; split; [unfold declare_refused; left; intros (He & _); apply Hod, bx_even, He | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]).
  step. rewrite eqb_lit by lia. destruct (Z.eqb_spec r 0) as [Rz|Rz]; [lia|]. bx_cond.
  step. rewrite bx_land3 by lia. rewrite R4. step. bx_cond.
  pose proof (bx_ov4 _ _ _ BF) as RF.
  step. rewrite bx_sx32 by lia.
  step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec (bx_fabric bs) k) as [Hfk|Hfk]; bx_cond.
  { eapply EPI; [left; split; [unfold declare_refused; left; intros (_ & _ & Hw); lia | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]. }
  assert (WOK : box_width_ok k (bx_fabric bs)) by (split; [apply bx_even; exact Hev | lia]).
  pose proof (bx_ov4 _ _ _ BN) as RN.
  step. step. rewrite bx_sx32 by lia.
  step. step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec 4 (bx_n bs)) as [Hn5|Hn5]; bx_cond.
  { eapply EPI; [left; split; [unfold declare_refused; right; left; lia | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]. }
  assert (TAIL : forall (mt : word -> option byte) (b p : Z) (j0 : list byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    declare_placed bs k b0 b p -> bytes_at rsegs mt r bs -> wr_at rsegs mt r 288 ->
    rw_cells rsegs mt (bv_unsigned sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs mt lo (bv_unsigned sp + -64) ->
    munch [(lo, bv_unsigned sp); (r, r + 288)] m mt -> wmono rsegs m mt -> mem_inv rsegs mt ->
    bytes_at rsegs mt 120544 (le8 (Z_to_bv 64 322768)) -> bytes_at rsegs mt 322768 (le8 canary) ->
    evt rsegs QQ (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x5 x6 x7 (Z_to_bv 64 r) (Z_to_bv 64 nm)
                          x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 k) (Z_to_bv 64 (-1)) (Z_to_bv 64 b0)
                          (Z_to_bv 64 b) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x13c10) fc None mt (seg_rom rsegs))).
  { clear HB HW FR ST MU WM MI GG GD BN RN BF RF.
    intros mt b p j0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HP HB HW FR ST MU WM MI GG GD.
    pose proof (rd4_bytes_at mt r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as BN.
    change (rd4 bs 280) with (bx_n bs) in BN.
    pose proof HP as (_ & Hn5' & HC).
    assert (Hp : (p = 1 /\ 0 <= b0) \/ (p = 0 /\ b0 < 0)) by (destruct HC as [(? & _ & ? & _) | (? & ? & _)]; tauto).
    assert (Hbr : 0 <= b /\ b + k <= bx_fabric bs).
    { destruct HC as [(B0 & -> & _ & (R0 & R1 & _)) | (B0 & _ & Bb & Hlf)]; [lia|].
      destruct Hlf as [(E & _) | (_ & L2 & _)]; lia. }
    pose proof (bx_ov4 _ _ _ BN) as RN.
    step. rewrite bx_sx32 by lia. step. step.
    rewrite bx_ltu by lia. replace (bx_n bs <? 6) with true by (symmetry; apply Z.ltb_lt; lia). bx_cond.
    step. step. step. rewrite bx_off56 by lia.
    step. step. rewrite bx_lxor_ltu by lia. bx_cond.
    step. step. step.
    assert (EP : Z_to_bv 64 (Z.lxor (bv_unsigned (v_slti (Z_to_bv 64 b0) 0)) 1) = Z_to_bv 64 p).
    { unfold v_slti, zsig. rewrite bx_signed by lia.
      destruct Hp as [(-> & B) | (-> & B)]; destruct (Z.ltb_spec b0 0); try lia; reflexivity. }
    rewrite EP.
    assert (KB1 : bx_keep (bytes_at rsegs mt r bs)) by exact HB.
    pose proof (bx_rw_sub mt r bs (56 * bx_n bs) 56 HB ltac:(rewrite HL; exact HW) ltac:(lia) ltac:(lia)
                  ltac:(rewrite HL; lia)) as ROW.
    pose proof (bx_rw_sub mt r bs 280 4 HB ltac:(rewrite HL; exact HW) ltac:(lia) ltac:(lia)
                  ltac:(rewrite HL; lia)) as NF.
    rewrite <- le4_rd4 in NF by (apply bsub_length; rewrite ?HL; lia).
    change (rd4 bs 280) with (bx_n bs) in NF. change (Z.to_nat 56) with 56%nat in ROW.
    change (Z.to_nat 4) with 4%nat in NF.
    pose proof (munch_refl [(lo, bv_unsigned sp); (r + 56 * bx_n bs, r + 56 * bx_n bs + 56); (r + 280, r + 284)] mt)
      as MU1.
    do 4 step.
    eapply evt_cut.
    { eapply MEMS; [ | eassumption ].
      rewrite (unsigned_lit (r + 56 * bx_n bs)) by lia. rewrite (unsigned_lit 56) by lia. exact ROW. }
    intros ms' PO. unfold memset_post in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m2 & E & MUc & WMc
                    & MI2 & RZ).
    subst ms'.
    rewrite (unsigned_lit (r + 56 * bx_n bs)) in MUc, RZ by lia. rewrite (unsigned_lit 56) in MUc, RZ by lia.
    try rewrite (unsigned_lit 0) in RZ by lia. change (Z.to_nat 56) with 56%nat in RZ.
    try change (0 mod 256) with 0 in RZ.
    replace (ret_pc (Z_to_bv 64 80972)) with (Z_to_bv 64 80972) by (apply bv_eq; vm_compute; reflexivity).
    bx_tac MUc WMc. clear MUc WMc.
    change 56%nat with (24 + 32)%nat in RZ. apply bx_rw_split in RZ. destruct RZ as [R24 R32].
    rewrite bx_firstn_repeat in R24. rewrite bx_skipn_repeat in R32.
    replace (r + 56 * bx_n bs + Z.of_nat 24) with (r + 56 * bx_n bs + 24) in R32 by lia.
    step. step. step. step. rewrite eqb_lit by lia.
    destruct (Z.eqb_spec nm 0) as [N0|N0]; bx_cond.
    - assert (Es : s = []) by (destruct HN as [(_ & ->) | (Hq & _)]; [reflexivity | lia]). subst s.
      step. rewrite bx_sx32 by lia. step. rewrite swrap_addi by lia. step. rewrite bx_lts by lia.
      replace (bx_n bs + 1 <? bx_n bs) with false by (symmetry; apply Z.ltb_ge; lia). bx_cond. step.
      pose proof (bx_rw_bytes _ _ _ R24) as RB24. cbn [cells_bytes cbytes] in RB24.
      pose proof (bx_rw_bytes _ _ _ R32) as RB32. cbn [cells_bytes cbytes] in RB32. rewrite app_nil_r in RB32.
      pose proof (bx_rw_bytes _ _ _ NF) as NFB. cbn [cells_bytes cbytes] in NFB. rewrite app_nil_r in NFB.
      eapply EPI; [ | intros i _; reflexivity | exact FR0 | eassumption | eassumption | eassumption | eassumption | eassumption].
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
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SB0 : bytes_at rsegs mm nm (pf_bytes (s ++ [0]) ++ slack))
          by (eapply bytes_at_transport; [exact SB | exact MU | ]; cbn [disjoint_from];
              unfold pf_bytes; rewrite !length_app, length_map, length_app; cbn [length];
              split; [lia | split; [lia | exact I]]);
        pose proof (bx_rw_bytes _ _ _ R32) as RB32; cbn [cells_bytes cbytes] in RB32; rewrite app_nil_r in RB32;
        assert (KD : bx_keep (bytes_at rsegs mm (r + 56 * bx_n bs + 24) (repeat (Z_to_bv 8 0) 32))) by exact RB32
      end.
      clear RB32.
      assert (SPL : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
      step. step. step. step. step. step.
      assert (U1 : bv_unsigned (Z_to_bv 64 (r + 56 * bx_n bs + 24)) = r + 56 * bx_n bs + 24)
        by (apply unsigned_lit; lia).
      assert (U2 : bv_unsigned (Z_to_bv 64 32) = 32) by reflexivity.
      assert (U3 : bv_unsigned (Z_to_bv 64 66309) = 66309) by reflexivity.
      assert (Lw : (length (firstn 31 s) <= 31)%nat) by (rewrite length_firstn; lia).
      eapply evt_cut.
      { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo canary [37; 115] [Ps] [APtr s] s
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
      replace (ret_pc (Z_to_bv 64 81012)) with (Z_to_bv 64 81012) by (apply bv_eq; vm_compute; reflexivity).
      assert (NM3 : bytes_at rsegs m3 (r + 56 * bx_n bs + 24) (name_field s)).
      { rewrite <- decl_name_eq. eapply bx_patch1; [exact KD | exact MUc | | | ].
        - change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact BY3.
        - rewrite repeat_length. unfold pf_bytes. rewrite length_map, length_app, length_firstn. cbn [length]. lia.
        - intros i Hi Hni. rewrite repeat_length in Hi. unfold pf_bytes in Hni.
          rewrite length_map, length_app, length_firstn in Hni. cbn [length] in Hni.
          cbn [outside]. rewrite length_firstn. split; [lia|]. split; [lia | exact I]. }
      bx_tac MUc WMc. clear MUc WMc.
      pose proof (name_field_length s) as LN.
      step. rewrite bx_sx32 by lia. step. rewrite swrap_addi by lia. step. rewrite bx_lts by lia.
      replace (bx_n bs + 1 <? bx_n bs) with false by (symmetry; apply Z.ltb_ge; lia). bx_cond. step.
      pose proof (bx_rw_bytes _ _ _ R24) as RB24. cbn [cells_bytes cbytes] in RB24.
      pose proof (bx_rw_bytes _ _ _ NF) as NFB. cbn [cells_bytes cbytes] in NFB. rewrite app_nil_r in NFB.
      eapply EPI; [ | exact FK3 | exact FM3 | eassumption | eassumption | eassumption | eassumption | eassumption].
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
  step. step. rewrite bx_lts by lia.
  destruct (Z.ltb_spec b0 0) as [Bn|Bp]; bx_cond.
  - step. step. step.
    assert (SPL : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    eapply evt_cut.
    { eapply LFB; [reflexivity | reflexivity | lia | exact HB | exact HL | exact H1 | exact H2 | exact H3 | exact R4
                  | rewrite SPL; exact ST | rewrite SPL; lia | rewrite SPL; lia | exact MI]. }
    intros ms' PO.
    destruct PO as (u5 & u6 & u7 & res & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & E
                    & MUc & WMc & MI1 & ST1 & lf & Elf & Hlf).
    subst ms' res. rewrite SPL in MUc, ST1.
    replace (ret_pc (Z_to_bv 64 80904)) with (Z_to_bv 64 80904) by (apply bv_eq; vm_compute; reflexivity).
    bx_tac MUc WMc. clear MUc WMc MI.
    assert (Hlfr : -1 <= lf <= 40) by (destruct Hlf as [(-> & _) | (HA & HB' & _)]; unfold boxreg_B2 in H2; lia).
    step. step. rewrite bx_lts by lia.
    destruct (Z.ltb_spec lf 0) as [Ln|Ln]; bx_cond.
    + eapply EPI; [left; split; [unfold declare_refused; right; right; right; split;
                                 [lia | replace (-1) with lf by lia; exact Hlf]
                              | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST1 | exact MU | exact WM | exact MI1].
    + eapply TAIL; [ | exact HB | exact HW | exact FR | exact ST1 | exact MU | exact WM | exact MI1 | exact GG | exact GD].
      split; [exact WOK|]. split; [lia|]. right. split; [lia|]. split; [reflexivity|].
      split; [lia | exact Hlf].
  - step. rewrite swrap_sub by lia. step. rewrite bx_lts by lia.
    destruct (Z.ltb_spec (bx_fabric bs - k) b0) as [Fb|Fb]; bx_cond.
    { eapply EPI; [left; split; [unfold declare_refused; right; right; left; split; [lia | intros (_ & Hr & _); lia]
                              | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI]. }
    step. step. step. step.
    eapply evt_cut.
    { eapply RT; [reflexivity | reflexivity | reflexivity | exact HB | exact HL | exact R4 | exact H1 | lia
                 | | lia | lia | lia].
      intros i Hi. destruct (H3 i Hi) as (A1 & A2 & A3 & A4 & A5). repeat split; lia. }
    intros ms' PO.
    destruct PO as (u5 & u6 & u7 & res & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & E & RR).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 80880)) with (Z_to_bv 64 80880) by (apply bv_eq; vm_compute; reflexivity).
    destruct RR as [(SM & ->) | (NSM & ->)].
    + step. step. bx_cond. step.
      eapply EPI; [left; split; [unfold declare_refused; right; right; left; split; [lia | intros (_ & _ & Hr); exact (Hr SM)]
                              | split; [reflexivity | exact HB]]
         | intros i _; reflexivity | exact FR0 | exact FR | exact ST | exact MU | exact WM | exact MI].
    + step. step. bx_cond.
      eapply TAIL; [ | exact HB | exact HW | exact FR | exact ST | exact MU | exact WM | exact MI | exact GG | exact GD].
      split; [exact WOK|]. split; [lia|]. left. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      split; [lia|]. split; [lia | exact NSM].
Qed.
