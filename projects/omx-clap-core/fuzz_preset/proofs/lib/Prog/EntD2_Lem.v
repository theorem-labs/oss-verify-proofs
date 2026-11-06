From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame pj_get_c pj_get_str_c EntD_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require StrFun.
Import ListNotations.
Open Scope Z_scope.

Definition KSYM : list Z := [115; 121; 109; 98; 111; 108].
Definition KVAL : list Z := [118; 97; 108; 117; 101].
Definition KENC : list Z := [101; 110; 99; 111; 100; 105; 110; 103].
Definition KBYT : list Z := [98; 121; 116; 101; 115].

Lemma d2_ro_out : forall m lo S x b, mem_inv rsegs m -> stk rsegs m lo S -> ro_byte rsegs x b -> ~ (lo <= x < S).
Proof.
  intros m lo S x b MI (H0 & H1 & H) (_ & RO) Hx.
  destruct (H x Hx) as (W & _).
  destruct (m (wa x)) as [b'|] eqn:E.
  - rewrite (MI (wa x) b' E) in RO. discriminate.
  - rewrite (wview_not_ro rsegs m (wa x) W E) in RO. discriminate.
Qed.

Lemma d2_key : forall m lo S k s, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - 64 -> 0 <= k ->
  k + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
  forallb (fun c => (0 <? c) && (c <? 256)) s = true ->
  ro_bytes_b rsegs k (map (Z_to_bv 8) (s ++ [0])) = true ->
  pj_cbytes rsegs m k s /\ (k + Z.of_nat (length s) + 1 <= S - 64 \/ S <= k).
Proof.
  intros m lo S k s MI ST LO H0 H1 HF HB. split; [exact (entd_cb m k s MI H0 H1 HF HB)|].
  pose proof (ro_bytes_b_sound rsegs _ _ HB) as RB.
  assert (Hn : forall x, k <= x < k + (Z.of_nat (length s) + 1) -> ~ (S - 64 <= x < S)).
  { intros x Hx Hw.
    assert (Li : (Z.to_nat (x - k) < length (map (Z_to_bv 8) (s ++ [0%Z])))%nat)
      by (rewrite length_map, length_app; cbn [length]; lia).
    destruct (nth_error (map (Z_to_bv 8) (s ++ [0])) (Z.to_nat (x - k))) as [b|] eqn:E;
      [| apply nth_error_None in E; lia].
    pose proof (ro_bytes_nth rsegs _ k (Z.to_nat (x - k)) b RB E) as RBx.
    rewrite Z2Nat.id in RBx by lia. replace (k + (x - k)) with x in RBx by lia.
    exact (d2_ro_out m lo S x b MI ST RBx ltac:(lia)). }
  pose proof (entd_apart k (Z.of_nat (length s) + 1) (S - 64) S ltac:(lia) ltac:(lia) Hn). lia.
Qed.

Lemma d2_ksym : forall m lo S, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - 64 ->
  pj_cbytes rsegs m 0x10383 KSYM /\ (0x10383 + Z.of_nat (length KSYM) + 1 <= S - 64 \/ S <= 0x10383).
Proof.
  intros m lo S MI ST LO.
  apply (d2_key m lo S); [exact MI | exact ST | exact LO | lia | cbn; lia | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma d2_kval : forall m lo S, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - 64 ->
  pj_cbytes rsegs m 0x1038a KVAL /\ (0x1038a + Z.of_nat (length KVAL) + 1 <= S - 64 \/ S <= 0x1038a).
Proof.
  intros m lo S MI ST LO.
  apply (d2_key m lo S); [exact MI | exact ST | exact LO | lia | cbn; lia | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma d2_kenc : forall m lo S, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - 64 ->
  pj_cbytes rsegs m 0x102ac KENC /\ (0x102ac + Z.of_nat (length KENC) + 1 <= S - 64 \/ S <= 0x102ac).
Proof.
  intros m lo S MI ST LO.
  apply (d2_key m lo S); [exact MI | exact ST | exact LO | lia | cbn; lia | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma d2_kbyt : forall m lo S, mem_inv rsegs m -> stk rsegs m lo S -> lo <= S - 64 ->
  pj_cbytes rsegs m 0x10431 KBYT /\ (0x10431 + Z.of_nat (length KBYT) + 1 <= S - 64 \/ S <= 0x10431).
Proof.
  intros m lo S MI ST LO.
  apply (d2_key m lo S); [exact MI | exact ST | exact LO | lia | cbn; lia | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

Lemma d2_root_out : forall m L S t D, pj_node rsegs m L (S + 8) t D ->
  (forall a n, L a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\ disjoint_from [(a, a + n)] (S - 64) 136) ->
  forall x, pj_foot (S + 8) D x -> outside [(S - 64, S); (S + 64, S + 72)] x.
Proof.
  intros m L S t D HN HL x [Hx|((a & n) & Hb & Hx)]; cbn [outside].
  - split; [lia|]. split; [lia|exact I].
  - pose proof (pj_node_blocks rsegs t m L (S + 8) D HN a n Hb) as Lb.
    destruct (HL a n Lb) as (_ & _ & _ & Hd). cbn [disjoint_from] in Hd.
    unfold pj_holds in Hx; cbn [fst snd] in Hx.
    split; [lia|]. split; [lia|exact I].
Qed.

Lemma d2_sub : forall m L S t D kname z, pj_node rsegs m L (S + 8) t D -> pj_get_res m L (S + 8) t D kname z ->
  (forall a n, L a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\ disjoint_from [(a, a + n)] (S - 64) 136) ->
  z = 0 \/ exists v Dz, pj_node rsegs m L z v Dz /\
    (forall x, pj_foot z Dz x -> outside [(S - 64, S); (S + 64, S + 72)] x).
Proof.
  intros m L S t D kname z HN HR HL.
  destruct (entd_get_sub m L (S + 8) t D kname z HN HR) as [E|(v & Dz & Hv & Hf)]; [left; exact E|right].
  exists v, Dz. split; [exact Hv|]. intros x Hx. exact (d2_root_out m L S t D HN HL x (Hf x Hx)).
Qed.

Lemma d2_kid : forall m L z4 items D4 kids i u,
  pj_node rsegs m L z4 (JArr items) D4 -> pj_u64 rsegs m (z4 + 24) kids -> nth_error items i = Some u ->
  forall W, (forall x, pj_foot z4 D4 x -> outside W x) ->
  exists D1, pj_node rsegs m L (kids + 56 * Z.of_nat i) u D1 /\
    (forall x, pj_foot (kids + 56 * Z.of_nat i) D1 x -> outside W x).
Proof.
  intros m L z4 items D4 kids i u HN HK Ei W HO.
  destruct (entd_arr m L z4 items D4 i u HN Ei) as (kids' & cap & D1 & HK' & _ & _ & HP & HF).
  rewrite (pj_u64_uniq rsegs m (z4 + 24) kids' kids HK' HK) in HP, HF.
  exists D1. split; [exact HP|]. intros x Hx. exact (HO x (HF x Hx)).
Qed.

Lemma d2_hdr : forall W m0 m L z4 items D4 kids,
  pj_node rsegs m0 L z4 (JArr items) D4 -> (forall x, pj_foot z4 D4 x -> outside W x) -> munch W m0 m ->
  pj_u64 rsegs m0 (z4 + 24) kids ->
  ov_read_bytes rsegs m (wa z4) 4 = Some (le4 (Z_to_bv 64 5)) /\
  ov_read_bytes rsegs m (wa (z4 + 40)) 8 = Some (le8 (Z_to_bv 64 (Z.of_nat (length items)))) /\
  ov_read_bytes rsegs m (wa (z4 + 24)) 8 = Some (le8 (Z_to_bv 64 kids)).
Proof.
  intros W m0 m L z4 items D4 kids HN HO MU HK.
  pose proof (entd_node_tr W m0 m L z4 (JArr items) D4 HN MU HO) as HN'.
  destruct (entd_arr_hdr m L z4 items D4 HN') as (H5 & H40 & _).
  assert (HK' : pj_u64 rsegs m (z4 + 24) kids).
  { apply (pj_u64_eq rsegs m0 m); [exact HK|]. intros x Hx. apply MU. apply HO. left. lia. }
  split; [exact (rd4 rsegs m z4 5 H5)|]. split; [exact (rd8 rsegs m (z4 + 40) _ H40)|].
  exact (rd8 rsegs m (z4 + 24) kids HK').
Qed.

Lemma d2_gs : pj_get_str_contract ->
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (S lo o k : Z)
    (kname : list Z) (u : jv) (Du : list (Z * Z)) (c : word),
  a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 k -> 120 <= S -> S mod 16 = 0 ->
  (forall a n, L a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\ disjoint_from [(a, a + n)] (S - 64) 136) ->
  (o = 0 \/ pj_node rsegs m0 L o u Du /\ (forall x, pj_foot o Du x -> outside [(S - 64, S); (S + 64, S + 72)] x)) ->
  pj_cbytes rsegs m k kname -> k + Z.of_nat (length kname) + 1 <= S - 64 \/ S <= k ->
  munch [(S - 64, S); (S + 64, S + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo S -> lo <= S - 64 -> rw_cells rsegs m (S + 64) [C8 c] ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(S - 64, S); (S + 64, S + 72)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo S /\ rw_cells rsegs m' (S + 64) [C8 c])
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_GET_STR) fc None m (seg_rom rsegs)).
Proof.
  intros HG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m L
    S lo o k kname u Du c E0 E1 HS HA HL HO HK HKd MU WM MI ST LO SL.
  pose proof ST as (ST0 & ST1 & _).
  pose proof (rw_cells_bound rsegs m (S + 64) [C8 c] SL) as SB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SB.
  assert (SU : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (HN : o = 0 \/ pj_node rsegs m L o u Du).
  { destruct HO as [HO|(HN & HF)]; [left; exact HO | right].
    exact (entd_node_tr _ m0 m L o u Du HN MU HF). }
  assert (Hod : o + 56 <= S - 64 \/ S <= o).
  { destruct HO as [->|(HN0 & HF)]; [lia|].
    pose proof (entd_rng m0 L o u Du HN0) as Ro.
    apply (entd_apart o 56 (S - 64) S); [lia | lia |].
    intros x Hx Hw. destruct (HF x (or_introl Hx)) as (Hx1 & _). exact (Hx1 Hw). }
  eapply evt_cut.
  { eapply (HG ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m L o k kname u Du lo E0 E1 HN HK); rewrite ?SU.
    - intros a n Hl. destruct (HL a n Hl) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - exact HA.
    - exact ST.
    - lia.
    - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - exact MI. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
              MU' & WM' & MI' & ST' & _ & _).
  rewrite SU in MU', ST'.
  apply evt_done. exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|].
  split; [apply (munch_trans _ _ _ _ MU); refine (munch_weaken _ _ _ _ _ MU');
          intros x Hx; cbn [outside] in Hx |- *; tauto|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact MI'|]. split; [exact ST'|].
  eapply rw_cells_transport; [exact SL | exact MU' | exact WM' | cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia].
Qed.

Lemma d2_pg : pj_get_contract ->
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (L : Z -> Z -> Prop) (S lo o k : Z)
    (kname : list Z) (u : jv) (Du : list (Z * Z)) (c : word),
  a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 k -> 120 <= S -> S mod 16 = 0 ->
  (forall a n, L a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\ disjoint_from [(a, a + n)] (S - 64) 136) ->
  (o = 0 \/ pj_node rsegs m0 L o u Du /\ (forall x, pj_foot o Du x -> outside [(S - 64, S); (S + 64, S + 72)] x)) ->
  pj_cbytes rsegs m k kname -> k + Z.of_nat (length kname) + 1 <= S - 64 \/ S <= k ->
  munch [(S - 64, S); (S + 64, S + 72)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  stk rsegs m lo S -> lo <= S - 64 -> rw_cells rsegs m (S + 64) [C8 c] ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(S - 64, S); (S + 64, S + 72)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\
      stk rsegs m' lo S /\ rw_cells rsegs m' (S + 64) [C8 c])
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_GET) fc None m (seg_rom rsegs)).
Proof.
  intros HG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m L
    S lo o k kname u Du c E0 E1 HS HA HL HO HK HKd MU WM MI ST LO SL.
  pose proof ST as (ST0 & ST1 & _).
  pose proof (rw_cells_bound rsegs m (S + 64) [C8 c] SL) as SB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SB.
  assert (SU : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (HN : o = 0 \/ pj_node rsegs m L o u Du).
  { destruct HO as [HO|(HN & HF)]; [left; exact HO | right].
    exact (entd_node_tr _ m0 m L o u Du HN MU HF). }
  assert (Hod : o + 56 <= S - 64 \/ S <= o).
  { destruct HO as [->|(HN0 & HF)]; [lia|].
    pose proof (entd_rng m0 L o u Du HN0) as Ro.
    apply (entd_apart o 56 (S - 64) S); [lia | lia |].
    intros x Hx Hw. destruct (HF x (or_introl Hx)) as (Hx1 & _). exact (Hx1 Hw). }
  eapply evt_cut.
  { eapply (HG ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m L o k kname u Du lo E0 E1 HN HK); rewrite ?SU.
    - intros a n Hl. destruct (HL a n Hl) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I].
    - exact HA.
    - exact ST.
    - lia.
    - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - exact MI. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E &
              MU' & WM' & MI' & ST' & _ & _).
  rewrite SU in MU', ST'.
  apply evt_done. exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|].
  split; [apply (munch_trans _ _ _ _ MU); refine (munch_weaken _ _ _ _ _ MU');
          intros x Hx; cbn [outside] in Hx |- *; destruct Hx as (Hx & _); split; [lia | exact I]|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM')|].
  split; [exact MI'|]. split; [exact ST'|].
  eapply rw_cells_transport; [exact SL | exact MU' | exact WM' | cbn [disjoint_from cells_size csize Nat.add Z.of_nat]; lia].
Qed.

Lemma d2_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma d2_le8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_nonneg bs) as HR0. pose proof (bytes_le_to_Z_bound bs) as HR.
  rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply StrFun.Z_to_le_bytes_to_Z.
Qed.

Lemma d2_slot : forall m A, stk rsegs m A (A + 8) -> exists c, rw_cells rsegs m A [C8 c].
Proof.
  intros m A H.
  destruct (stk_carve rsegs m A (A + 8) 8 H ltac:(change (Z.of_nat 8) with 8; lia)) as (_ & junk & HJ).
  change (Z.of_nat 8) with 8 in HJ. replace (A + 8 - 8) with A in HJ by lia.
  destruct HJ as ((Hwf & HB) & HW). cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (Hl & _).
  exists (le_bytes_to_word junk). split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes] in HB |- *. rewrite app_nil_r in HB |- *. rewrite d2_le8 by exact Hl. exact HB.
  - exact HW.
Qed.

Lemma d2_unslot : forall m A c, rw_cells rsegs m A [C8 c] -> stk rsegs m A (A + 8).
Proof. intros m A c H. exact (stk_of_rw_cells rsegs m A [C8 c] H). Qed.
