From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import reac_scene_struct SceneTac SceneD SceneTM.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import memcpy_c bcmp_c reac_ctrl_build_scene_step_c check_step_c.
Import ListNotations.
Open Scope Z_scope.

Definition TPre (sp again body : word) (lo S : Z) (b sv mb : list byte) : Prop :=
  bv_unsigned sp = S - 9072 /\ S mod 16 = 0 /\ 0x51000 <= lo /\ lo + 9296 <= S /\
  bv_unsigned body <> 0 /\ length b = 8904%nat /\ length sv = 104%nat /\ length mb = 6%nat /\
  (bv_unsigned again + 8904 <= lo \/ S <= bv_unsigned again) /\
  (bv_unsigned body + 8904 <= lo \/ S <= bv_unsigned body) /\
  (bv_unsigned again + 8904 <= bv_unsigned body \/ bv_unsigned body + 8904 <= bv_unsigned again).

Definition TMem (sp again body : word) (m0 m : word -> option byte) (lo S : Z) (b sv mb : list byte) (k : Z) : Prop :=
  exists ja bj : list byte,
    mem_inv rsegs m /\ munch [(S - 9296, S); (bv_unsigned again, bv_unsigned again + 8904)] m0 m /\
    wmono rsegs m0 m /\
    stk rsegs m lo (bv_unsigned sp) /\ stk rsegs m (bv_unsigned sp) (bv_unsigned sp + 24) /\
    rw_cells rsegs m (bv_unsigned sp + 24) [CB 34 bj] /\ stk rsegs m (bv_unsigned sp + 58) S /\
    bytes_at rsegs m (bv_unsigned sp + 8) (le8 (Z_to_bv 64 8904)) /\
    bytes_at rsegs m (bv_unsigned sp + 16) (le8 (Z_to_bv 64 8904)) /\
    bytes_at rsegs m (S - 104) sv /\ bytes_at rsegs m (S - 110) mb /\ bytes_at rsegs m (bv_unsigned body) b /\
    rw_cells rsegs m (bv_unsigned again) [CB (Z.to_nat (scT_off k)) (firstn (Z.to_nat (scT_off k)) b)] /\
    rw_cells rsegs m (bv_unsigned again + scT_off k) [CB (Z.to_nat (8904 - scT_off k)) ja].

Definition TMid (sp gp tp again body : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
    (lo S : Z) (b sv mb : list byte) (k : Z) (ms' : machine_state) : Prop :=
  exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                  x27 x28 x29 x30 x31) F (Z_to_bv 64 0x151a0) fc None m' (seg_rom rsegs) /\
    x2 = sp /\ x3 = gp /\ x4 = tp /\ x9 = body /\ x19 = again /\
    bv_unsigned x18 = (if k =? 0 then 0 else 8904) /\ bv_unsigned x20 = k + 1 /\ bv_unsigned x21 = 8904 /\
    bv_unsigned x23 = scT_off (k + 1) /\ bv_unsigned x24 = 8904 /\ bv_unsigned x25 = scT_off (k + 1) /\
    bv_unsigned x26 = 8905 /\ bv_unsigned x27 = 343 /\
    TMem sp again body m0 m' lo S b sv mb (k + 1).

Definition QT (sp gp tp again body : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (lo S : Z) (b sv mb : list byte) (ms' : machine_state) : Prop :=
  exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 : word) (m' : word -> option byte),
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                  x27 x28 x29 x30 x31) F (Z_to_bv 64 0x16558) fc None m' (seg_rom rsegs) /\
    x1 = Z_to_bv 64 0x151d4 /\ x2 = sp /\ x3 = gp /\ x4 = tp /\ x9 = body /\ x10 = again /\
    munch [(S - 9296, S); (bv_unsigned again, bv_unsigned again + 8904)] m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo S /\ bytes_at rsegs m' (bv_unsigned body) b /\
    bytes_at rsegs m' (S - 104) sv /\ bytes_at rsegs m' (S - 110) mb /\
    bytes_at rsegs m' (bv_unsigned sp + 8) (le8 (Z_to_bv 64 8904)) /\
    bytes_at rsegs m' (bv_unsigned sp + 16) (le8 (Z_to_bv 64 8904)).

Lemma scT_bytes_addr : forall m A A' l, bytes_at rsegs m A l -> A = A' -> bytes_at rsegs m A' l.
Proof. intros; subst; assumption. Qed.

Lemma scT_rw_resize : forall m A A' n n' l, rw_cells rsegs m A [CB n l] -> A = A' -> n = n' ->
  rw_cells rsegs m A' [CB n' l].
Proof. intros; subst; assumption. Qed.

Lemma scT_rw_of : forall m A l n, bytes_at rsegs m A l -> length l = n ->
  wr_at rsegs m A (Z.of_nat (cells_size [CB n l])) -> rw_cells rsegs m A [CB n l].
Proof.
  intros m A l n Hb Hl Hw. split; [split; [cbn [cells_wf cell_wf]; split; [exact Hl | exact I] | ] | exact Hw].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
Qed.

Lemma scT_u8_len : forall k, bv_unsigned (Z_to_bv 8 (scene_len k)) = scene_len k.
Proof. intros k. unfold scene_len. destruct (k =? 0); [reflexivity|]. destruct (k =? 342); reflexivity. Qed.

Lemma scT_swrap : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma scene_T_turn : forall (k : Z) (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s9 t3 t4 t5 t6 : word)
    (sp gp tp again body s4 s5 s7 s8 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo S : Z) (b sv mb : list byte),
  reac_ctrl_build_scene_step_contract -> check_step_contract -> memcpy_contract ->
  0 <= k <= 342 -> bv_unsigned s4 = k -> bv_unsigned s5 = 8904 -> bv_unsigned s7 = scT_off k ->
  bv_unsigned s8 = (if k =? 0 then 0 else 8904) -> bv_unsigned s10 = 8905 -> bv_unsigned s11 = 343 ->
  TPre sp again body lo S b sv mb -> TMem sp again body m0 m lo S b sv mb k ->
  evt rsegs (TMid sp gp tp again body F fc m0 lo S b sv mb k)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 body a0 a1 a2 a3 a4 a5 a6 a7 s2 again s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15124) fc None m (seg_rom rsegs)).
Proof.
  intros k ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s9 t3 t4 t5 t6 sp gp tp again body s4 s5 s7 s8 s10 s11
         F fc m0 m lo S b sv mb BUILD CHK MEMC Hk H4 H5 H7 H8 H10 H11 PRE MEM.
  unfold reac_ctrl_build_scene_step_contract, REAC_CTRL_BUILD_SCENE_STEP, REAC_CTRL_BUILD_SCENE_STEP_FRAME,
    TAIL_TRAILER_AT in BUILD.
  unfold check_step_contract, CHECK_STEP, CHECK_STEP_K in CHK.
  destruct PRE as (HSP & S16 & LO1 & LO2 & HBD & LB & LSV & LMB & DA & DB & DAB).
  destruct MEM as (ja & bj & HMI & MU & WM & STa & STb & BLK & STc & Q8 & Q16 & HSV & HMB & HB & AG1 & AG2).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 again) as Rag.
  pose proof (bv_unsigned_in_range 64 body) as Rbo. unfold bv_modulus in Rsp, Rag, Rbo.
  pose proof (scT_bnd k Hk) as BND.
  pose proof (scT_off_step k Hk) as OST.
  pose proof LB as LBz. change 8904%nat with (Z.to_nat 8904) in LBz.
  pose proof (rw_cells_bound _ _ _ _ AG2) as BAG. cbn [cells_size csize] in BAG.
  assert (R8 : 0 <= (if k =? 0 then 0 else 8904) < 2^64) by (destruct (k =? 0); lia).
  assert (E4 : s4 = Z_to_bv 64 k) by (apply bv_eq; rewrite H4, unsigned_lit by lia; reflexivity).
  assert (E5 : s5 = Z_to_bv 64 8904) by (apply bv_eq; rewrite H5; reflexivity).
  assert (E7 : s7 = Z_to_bv 64 (scT_off k)) by (apply bv_eq; rewrite H7, unsigned_lit by lia; reflexivity).
  assert (E8 : s8 = Z_to_bv 64 (if k =? 0 then 0 else 8904))
    by (apply bv_eq; rewrite H8, unsigned_lit by exact R8; reflexivity).
  assert (E10 : s10 = Z_to_bv 64 8905) by (apply bv_eq; rewrite H10; reflexivity).
  assert (E11 : s11 = Z_to_bv 64 343) by (apply bv_eq; rewrite H11; reflexivity).
  subst s4 s5 s7 s8 s10 s11. clear H4 H5 H7 H8 H10 H11.
  pose proof STc as (_ & HS64 & _).
  assert (U24 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 24)) = bv_unsigned sp + 24) by (apply unsigned_lit; lia).
  assert (Uk : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  assert (U8904 : bv_unsigned (Z_to_bv 64 8904) = 8904) by reflexivity.
  assert (OK : scene_step_ok (Z_to_bv 64 (bv_unsigned sp + 24)) body (Z_to_bv 64 8904) (Z_to_bv 64 k) = true).
  { unfold scene_step_ok. rewrite U24, Uk, U8904.
    replace (bv_unsigned sp + 24 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (bv_unsigned body =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (k <=? 342) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  zr_until 0x155e8.
  eapply evt_cut; [eapply BUILD | ].
  { exact HMI. }
  { exact STa. }
  { lia. }
  { intros _. rewrite U24. split; [exact BLK|]. split; [exact HB|]. split; [exact LB|].
    split; [lia|]. split; [lia|]. split; lia. }
  sd_postc.
  rename PC into STa1.
  rewrite OK in POST. cbv iota in POST. destruct POST as [A0 BLK1].
  match type of A0 with ?a = _ => subst a end.
  rewrite U24, Uk in BLK1.
  zstep. sres_if.
  pose proof (sd_cb_bytes _ _ _ _ BLK1) as BB.
  pose proof (proj2 BLK1) as BW. clear BLK1.
  pose proof (scT_block_len b k LB Hk) as LBK.
  pose proof (bytes_at_byte1 _ _ _ 4 BB ltac:(rewrite LBK; lia)) as R4.
  pose proof (bytes_at_byte1 _ _ _ 5 BB ltac:(rewrite LBK; lia)) as R5.
  pose proof (bytes_at_byte1 _ _ _ 7 BB ltac:(rewrite LBK; lia)) as R7.
  pose proof (bytes_at_byte1 _ _ _ 8 BB ltac:(rewrite LBK; lia)) as R8b.
  change (Z.to_nat 4) with 4%nat in R4. change (Z.to_nat 5) with 5%nat in R5.
  change (Z.to_nat 7) with 7%nat in R7. change (Z.to_nat 8) with 8%nat in R8b.
  rewrite scT_nth4 in R4. rewrite scT_nth5 in R5.
  zstep. zstep. zstep. zstep.
  rewrite scT_u8_len, Z.lor_0_l.
  zr_until 0x153ec.
  clear R4 R5 R7 R8b.
  assert (S16' : bv_unsigned sp mod 16 = 0) by (rewrite HSP; Z.div_mod_to_equations; lia).
  eapply evt_cut; [eapply CHK | ].
  { assumption. }
  { exact STa1. }
  { lia. }
  { exact S16'. }
  { rewrite Uk. lia. }
  { rewrite U24, Uk. exact BB. }
  { exact HB. }
  { exact LB. }
  { rewrite U24. lia. }
  { lia. }
  sd_postc.
  rename POST into STa2.
  zstep.
  let K := fresh "K" in if_cases K; zify_cond K.
  1: assert (K0 : k = 0) by (rewrite ?Uk in K; lia);
     assert (SRC : scT_src k = 9) by (rewrite K0; reflexivity);
     assert (LEN0 : scene_len k = 24) by (rewrite K0; reflexivity);
     zr_until 0x1d508;
     replace (bv_unsigned sp + 33) with (bv_unsigned sp + 24 + scT_src k) by lia.
  2: assert (K0 : k <> 0) by (rewrite ?Uk in K; lia);
     assert (SRC : scT_src k = 7) by (unfold scT_src; rewrite (proj2 (Z.eqb_neq _ _) K0); reflexivity);
     zr_until 0x1d508;
     replace (bv_unsigned sp + 31) with (bv_unsigned sp + 24 + scT_src k) by lia.
  all: assert (Ua0 : bv_unsigned (Z_to_bv 64 (bv_unsigned again + scT_off k)) = bv_unsigned again + scT_off k)
         by (apply unsigned_lit; lia).
  all: assert (Ulen : bv_unsigned (Z_to_bv 64 (scene_len k)) = scene_len k) by (apply unsigned_lit; lia).
  all: assert (Ua1 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 24 + scT_src k)) = bv_unsigned sp + 24 + scT_src k)
         by (apply unsigned_lit; lia).
  all: destruct (sd_cb_cut _ _ _ _ (Z.to_nat (scene_len k)) AG2 ltac:(lia)) as [AG2a AG2b]; clear AG2.
  all: pose proof (bytes_at_slice _ _ _ (Z.to_nat (scT_src k)) (Z.to_nat (scene_len k)) BB ltac:(rewrite LBK; lia))
         as BSRC.
  all: eapply evt_cut; [eapply MEMC | ];
         [ rewrite Ua1; eapply scT_bytes_addr; [exact BSRC | lia]
         | rewrite Ulen, length_firstn, length_skipn, LBK; lia
         | rewrite Ua0, Ulen; exact AG2a
         | rewrite Ua1, Ua0, Ulen; lia
         | assumption
         | ].
  all: sd_postc.
  all: rename PC into AGn; clear POST; rewrite Ua0, Ulen in AGn.
  all: pose proof (rw_cells_join2 _ (bv_unsigned again) (bv_unsigned again + scT_off k) _ _ AG1
                     ltac:(cbn [cells_size csize]; lia) AGn) as AGj; clear AG1 AGn.
  all: lazymatch goal with AGj : rw_cells _ ?mm _ _ |- _ =>
         assert (AG1n : rw_cells rsegs mm (bv_unsigned again)
                          [CB (Z.to_nat (scT_off (k + 1))) (firstn (Z.to_nat (scT_off (k + 1))) b)])
           by (eapply rw_cells_rebytes;
               [ exact AGj
               | cbn [cells_wf cell_wf]; rewrite length_firstn; split; [lia | exact I]
               | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; symmetry; apply scT_again_step; [exact LB | lia] ])
       end; clear AGj.
  all: apply (scT_rw_resize _ _ (bv_unsigned again + scT_off (k + 1)) _ (Z.to_nat (8904 - scT_off (k + 1)))) in AG2b;
         [ | lia | lia ].
  all: pose proof (scT_rw_of _ _ _ 34 BB LBK BW) as BLKn; clear BB BW.
  all: zr_until 0x151a0.
  all: unfold TMid, TMem; finish.
  all: try reflexivity.
  all: try (rewrite unsigned_lit by exact R8; reflexivity).
  all: try (rewrite scT_swrap by lia; apply unsigned_lit; lia).
  all: try (rewrite unsigned_lit by lia; lia).
  all: try (rewrite K0, scT_nth7_0, scT_nth8_0; sd_closed_vm).
  all: try (rewrite unsigned_lit by exact R8; rewrite (proj2 (Z.eqb_neq _ _) K0); reflexivity).
  all: do 2 eexists; OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib.AndN.and_splits; eassumption.
Qed.

Lemma scene_T_tail : forall (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s9 t3 t4 t5 t6 : word)
    (sp gp tp again body s4 s5 s7 s8 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo S : Z) (b sv mb : list byte),
  bcmp_contract ->
  bv_unsigned s2 = 8904 -> bv_unsigned s4 = 343 -> bv_unsigned s9 = 8904 -> bv_unsigned s11 = 343 ->
  TPre sp again body lo S b sv mb -> TMem sp again body m0 m lo S b sv mb 343 ->
  evt rsegs (QT sp gp tp again body F fc m0 lo S b sv mb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 body a0 a1 a2 a3 a4 a5 a6 a7 s2 again s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x151a0) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s9 t3 t4 t5 t6 sp gp tp again body s4 s5 s7 s8 s10 s11 F fc m0 m lo S b sv mb BCMPc H2 H4 H9 H11 PRE MEM.
  destruct PRE as (HSP & S16 & LO1 & LO2 & HBD & LB & LSV & LMB & DA & DB & DAB).
  destruct MEM as (ja & bj & HMI & MU & WM & STa & STb & BLK & STc & Q8 & Q16 & HSV & HMB & HB & AG1 & AG2).
  clear AG2.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof LB as LBz. change 8904%nat with (Z.to_nat 8904) in LBz.
  pose proof STc as (_ & HS64 & _).
  rewrite (scT_again_all b LB) in AG1.
  pose proof (sd_cb_bytes _ _ _ _ AG1) as AGB. clear AG1.
  zr_until 0x1d4d4.
  eapply evt_cut; [eapply BCMPc | ].
  { exact AGB. }
  { exact HB. }
  { apply sd_mcm_refl. change (bv_unsigned (Z_to_bv 64 8904)) with 8904. lia. }
  { assumption. }
  sd_postc. clear PC POST.
  zr_until 0x16558.
  sd_rel BLK STb (bv_unsigned sp + 58).
  pose proof (stk_merge rsegs _ _ _ _ STb STc ltac:(lia)) as STbc.
  pose proof (stk_merge rsegs _ lo (bv_unsigned sp) _ STa STbc ltac:(lia)) as STF.
  unfold QT. finish.
  all: reflexivity.
Qed.

Lemma scene_T_loop : forall (n : nat) (k : Z) (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s9 t3 t4 t5 t6 : word)
    (sp gp tp again body s4 s5 s7 s8 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo S : Z) (b sv mb : list byte),
  reac_ctrl_build_scene_step_contract -> check_step_contract -> memcpy_contract -> bcmp_contract ->
  k = 342 - Z.of_nat n -> 0 <= k ->
  bv_unsigned s4 = k -> bv_unsigned s5 = 8904 -> bv_unsigned s7 = scT_off k ->
  bv_unsigned s8 = (if k =? 0 then 0 else 8904) -> bv_unsigned s10 = 8905 -> bv_unsigned s11 = 343 ->
  TPre sp again body lo S b sv mb -> TMem sp again body m0 m lo S b sv mb k ->
  evt rsegs (QT sp gp tp again body F fc m0 lo S b sv mb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 body a0 a1 a2 a3 a4 a5 a6 a7 s2 again s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15124) fc None m (seg_rom rsegs)).
Proof.
  intros n. induction n as [|n IH];
    intros k ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s6 s9 t3 t4 t5 t6 sp gp tp again body s4 s5 s7 s8 s10 s11 F fc m0 m lo S b sv mb BUILD CHK MEMC BCMPc Hn Hk H4 H5 H7 H8 H10 H11 PRE MEM;
    (eapply evt_cut; [eapply scene_T_turn; try eassumption; lia | ]);
    intros ms' MID;
    destruct MID as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m' & E & E2 & E3 & E4 & E9 & E19 &
                     H18' & H20' & H21' & H23' & H24' & H25' & H26' & H27' & MEM');
    subst ms' x2 x3 x4 x9 x19.
  - assert (K : k = 342) by lia. subst k.
    change (if 342 =? 0 then 0 else 8904) with 8904 in H18'.
    change (scT_off (342 + 1)) with 8904 in H25'.
    eapply scene_T_tail; try eassumption; lia.
  - zstep. sres_if.
    eapply (IH (k + 1)); try eassumption; try lia.
    rewrite (proj2 (Z.eqb_neq (k + 1) 0) ltac:(lia)). exact H24'.
Qed.

Lemma scene_T_x : forall (ra t0 t1 t2 s0 again a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6 : word) (sp gp tp body : word) (F : bvmap 5 word) (fc : bv 32)
                          (m : word -> option byte) (lo S : Z) (b sv mb ja : list byte),
  reac_ctrl_build_scene_step_contract -> check_step_contract -> memcpy_contract -> bcmp_contract ->
  bv_unsigned sp = S - 9072 -> S mod 16 = 0 -> stk rsegs m lo S -> 0x51000 <= lo -> lo + 9296 <= S ->
  bv_unsigned again <> 0 -> bv_unsigned body <> 0 -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned again) [CB 8904 ja] ->
  bytes_at rsegs m (bv_unsigned body) b -> length b = 8904%nat ->
  bytes_at rsegs m (S - 104) sv -> length sv = 104%nat ->
  bytes_at rsegs m (S - 110) mb -> length mb = 6%nat ->
  bytes_at rsegs m (bv_unsigned sp + 8) (le8 (Z_to_bv 64 8904)) ->
  bytes_at rsegs m (bv_unsigned sp + 16) (le8 (Z_to_bv 64 8904)) ->
  (bv_unsigned again + 8904 <= lo \/ S <= bv_unsigned again) ->
  (bv_unsigned body + 8904 <= lo \/ S <= bv_unsigned body) ->
  (bv_unsigned again + 8904 <= bv_unsigned body \/ bv_unsigned body + 8904 <= bv_unsigned again) ->
  evt rsegs (QT sp gp tp again body F fc m lo S b sv mb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 body again a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15100) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 s0 again a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 sp gp tp body F fc
         m lo S b sv mb ja BUILD CHK MEMC BCMPc HSP S16 ST LO1 LO2 HAG HBD HMI HJA HB LB HSV LSV HMB LMB Q8 Q16
         DA DB DAB.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof ST as (_ & HS64 & _).
  pose proof (munch_refl [(S - 9296, S); (bv_unsigned again, bv_unsigned again + 8904)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  destruct (stk_split rsegs m lo (bv_unsigned sp + 58) S ST ltac:(lia)) as [STl STc]. clear ST.
  destruct (sd_carve_at m lo (bv_unsigned sp + 24) (bv_unsigned sp + 58) 34 STl ltac:(lia) ltac:(lia) ltac:(lia))
    as [STl2 [bj BLK]].
  clear STl. change (Z.to_nat 34) with 34%nat in BLK.
  destruct (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + 24) STl2 ltac:(lia)) as [STa STb]. clear STl2.
  destruct (sd_cb_cut _ _ _ _ 0 HJA ltac:(lia)) as [AG1 AG2]. clear HJA.
  zr_until 0x15124.
  eapply (scene_T_loop 342%nat 0); try eassumption; try reflexivity; try lia.
  - unfold TPre. repeat split; assumption.
  - unfold TMem. exists (skipn 0 ja), bj.
    OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib.AndN.and_splits; first [exact AG1 | exact AG2 | assumption].
Qed.
