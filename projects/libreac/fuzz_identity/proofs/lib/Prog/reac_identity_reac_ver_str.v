From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import write_uint_c reac_identity_reac_ver_str_c.
Import ListNotations.
Open Scope Z_scope.

Lemma vs_eqb : forall X Y, 0 <= X < 2 ^ 64 -> 0 <= Y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 X) (Z_to_bv 64 Y) = (X =? Y).
Proof. intros X Y HX HY. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma vs_ltu : forall X Y, 0 <= X < 2 ^ 64 -> 0 <= Y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 X) (Z_to_bv 64 Y) = (X <? Y).
Proof. intros X Y HX HY. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma vs_w1 : forall z, 0 <= z < 2 ^ 31 - 1 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 1)) = Z_to_bv 64 (z + 1).
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with 2147483648. lia.
Qed.

Lemma vs_addw : forall x y, 0 <= x -> 0 <= y -> x + y < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 x) + bv_unsigned (Z_to_bv 64 y))) = Z_to_bv 64 (x + y).
Proof.
  intros x y Hx Hy Hxy. rewrite (unsigned_lit x), (unsigned_lit y) by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with 2147483648. lia.
Qed.

Lemma vs_le1 : forall z, 0 <= z < 256 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite (unsigned_lit z) by lia. reflexivity. Qed.

Lemma vs_lsd_lt10 : forall k x, x < 10 -> write_uint_lsd (S k) x = [write_uint_dg (x mod 10)].
Proof. intros k x Hx. cbn [write_uint_lsd]. rewrite (proj2 (Z.ltb_lt x 10) Hx). reflexivity. Qed.

Lemma vs_lsd_ge10 : forall k x, 10 <= x ->
  write_uint_lsd (S k) x = write_uint_dg (x mod 10) :: write_uint_lsd k (x / 10).
Proof. intros k x Hx. cbn [write_uint_lsd]. rewrite (proj2 (Z.ltb_ge x 10) Hx). reflexivity. Qed.

Lemma vs_lsd_pos : forall k x, (1 <= length (write_uint_lsd (S k) x))%nat.
Proof. intros k x. cbn [write_uint_lsd length]. lia. Qed.

Lemma vs_lsd_len : forall k x, (length (write_uint_lsd k x) <= k)%nat.
Proof.
  induction k as [|k IH]; intros x; cbn [write_uint_lsd length]; [lia|].
  destruct (x <? 10); cbn [length]; [lia|]. specialize (IH (x / 10)). lia.
Qed.

Lemma vs_n_range : forall v, 1 <= write_uint_n v <= 5.
Proof.
  intros v. unfold write_uint_n, write_uint_D. rewrite length_rev.
  pose proof (vs_lsd_len 5 v). pose proof (vs_lsd_pos 4 v). lia.
Qed.

Lemma vs_n_ge10 : forall v, 10 <= v -> 2 <= write_uint_n v.
Proof.
  intros v Hv. unfold write_uint_n, write_uint_D. rewrite length_rev.
  rewrite (vs_lsd_ge10 4 v) by lia. cbn [length]. pose proof (vs_lsd_pos 3 (v / 10)). lia.
Qed.

Lemma vs_D_lt10 : forall v, 0 <= v < 10 -> write_uint_D v = [write_uint_dg v].
Proof.
  intros v Hv. unfold write_uint_D. rewrite (vs_lsd_lt10 4 v) by lia. cbn [rev app].
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma vs_n_lt10 : forall v, 0 <= v < 10 -> write_uint_n v = 1.
Proof. intros v Hv. unfold write_uint_n. rewrite vs_D_lt10 by lia. reflexivity. Qed.

Lemma vs_LV : forall ma mi pa, reac_ver_str_LV ma mi pa =
  write_uint_n ma + 1 + write_uint_n mi + (if pa <? 10 then 2 else write_uint_n pa).
Proof.
  intros ma mi pa. unfold reac_ver_str_LV, reac_ver_str_VER, reac_ver_str_DEC2, write_uint_n.
  rewrite !length_app. cbn [length]. destruct (pa <? 10); cbn [length]; lia.
Qed.

Lemma vs_wr_sub : forall m a n a' n', wr_at rsegs m a n -> a <= a' -> a' + n' <= a + n -> wr_at rsegs m a' n'.
Proof.
  intros m a n a' n' (H1 & H2 & H) Ha Hn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Definition vs_inv (m0 m : word -> option byte) (lo S o LV : Z) (cs : list cell) (PRE : list byte) : Prop :=
  rw_cells rsegs m (S + -48) cs /\ stk rsegs m lo (S + -48) /\
  munch [(S - 64, S); (o, o + LV + 1)] m0 m /\ wmono rsegs m0 m /\
  wr_at rsegs m o 20 /\ bytes_at rsegs m o PRE.

Lemma vs_inv_store_ok : forall m0 m lo S o LV cs PRE k,
  vs_inv m0 m lo S o LV cs PRE -> 0 <= k -> k + 1 <= 20 -> store_ok rsegs m (wa (o + k)) 1 = true.
Proof.
  intros m0 m lo S o LV cs PRE k (_ & _ & _ & _ & HW & _) Hk Hk2.
  apply (wr_at_store_ok rsegs m o 20 k 1 HW); lia.
Qed.

Lemma vs_inv_store : forall m0 m lo S o LV k cs PRE b,
  0 <= lo -> lo + 64 <= S -> S <= 2 ^ 64 -> 0 <= o -> o + 20 <= 2 ^ 64 -> (o + 20 <= S - 64 \/ S <= o) ->
  cells_size cs = 48%nat -> k = Z.of_nat (length PRE) -> k + 1 <= 20 -> k + 1 <= LV + 1 ->
  vs_inv m0 m lo S o LV cs PRE ->
  vs_inv m0 (write_to_mem m (wa (o + k)) [b]) lo S o LV cs (PRE ++ [b]).
Proof.
  intros m0 m lo S o LV k cs PRE b Hlo HLO HS Ho HoN HD Hcs Hk Hk1 HkL (FR & ST & MU & WM & HW & BP).
  pose proof (bytes_at_bound rsegs m o PRE BP) as HB.
  split; [|split; [|split; [|split; [|split]]]].
  - apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | rewrite Hcs; cbn [length]; lia].
  - apply stk_write; [exact ST | lia | cbn [length]; lia].
  - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside length]; lia].
  - apply wmono_write. exact WM.
  - apply wr_at_write. exact HW.
  - apply bytes_at_app. split.
    + apply bytes_at_write_other; [exact BP | lia | cbn [length]; lia | cbn [length]; lia].
    + rewrite <- Hk. apply bytes_at_write_same; cbn [length]; lia.
Qed.

Lemma vs_call : write_uint_contract ->
  forall (S lo o LV k v RA : Z) (cs : list cell) (PRE : list byte)
    (gp tp t0 t1 t2 s0 s1 w0 w1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (Q : machine_state -> Prop),
  0 <= lo -> lo + 64 <= S -> S <= 2 ^ 64 -> 0 <= o -> o + 20 <= 2 ^ 64 -> (o + 20 <= S - 64 \/ S <= o) ->
  cells_size cs = 48%nat -> 0 <= v < 65536 -> k = Z.of_nat (length PRE) -> k + 5 <= 20 ->
  k + write_uint_n v <= LV + 1 -> 0 <= RA < 2 ^ 64 -> RA mod 2 = 0 ->
  w0 = Z_to_bv 64 (o + k) -> w1 = Z_to_bv 64 v ->
  vs_inv m0 m lo S o LV cs PRE ->
  (forall (m' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 : word),
     vs_inv m0 m' lo S o LV cs (PRE ++ write_uint_D v) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (S + -48)) gp tp y5 y6 y7 s0 s1 (Z_to_bv 64 (write_uint_n v))
                         y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
                  F (Z_to_bv 64 RA) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (S + -48)) gp tp t0 t1 t2 s0 s1 w0 w1 a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14944) fc None m (seg_rom rsegs)).
Proof.
  intros WU S lo o LV k v RA cs PRE gp tp t0 t1 t2 s0 s1 w0 w1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m0 m Q Hlo HLO HS Ho HoN HD Hcs Hv Hk Hk5 HkL HRA HRA2 E0 E1 INV K.
  subst w0 w1.
  destruct INV as (FR & ST & MU & WM & HW & BP).
  pose proof (bytes_at_bound rsegs m o PRE BP) as HB.
  assert (Esp : bv_unsigned (Z_to_bv 64 (S + -48)) = S + -48) by (apply unsigned_lit; lia).
  pose proof (vs_n_range v) as Hn.
  unfold write_uint_contract in WU.
  eapply evt_cut.
  { eapply (WU (Z_to_bv 64 RA) (Z_to_bv 64 (S + -48)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (o + k)) (Z_to_bv 64 v)
              a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (o + k) v lo).
    - reflexivity.
    - reflexivity.
    - exact Hv.
    - eapply vs_wr_sub; [exact HW | lia | lia].
    - rewrite Esp. exact ST.
    - rewrite Esp. lia.
    - rewrite Esp. lia. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m' & E & MU' & WM' & ST' & BT').
  subst ms'. rewrite Esp in MU', ST'.
  rewrite (ret_pc_even RA) by lia.
  apply K.
  split; [|split; [|split; [|split; [|split]]]].
  - eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | rewrite Hcs; cbn [disjoint_from]; lia].
  - exact ST'.
  - eapply munch_trans; [exact MU |]. eapply munch_weaken; [|exact MU'].
    unfold sub_fp. cbn [outside]. intros x [H1 [H2 _]]. repeat split; lia.
  - eapply wmono_trans; [exact WM | exact WM'].
  - eapply wr_at_transport; [exact HW | exact WM'].
  - apply bytes_at_app. split.
    + eapply bytes_at_transport; [exact BP | exact MU' | cbn [disjoint_from]; lia].
    + replace (o + Z.of_nat (length PRE)) with (o + k) by lia. exact BT'.
Qed.

Definition vs_ret (W : list ivl) (r : word) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m0 : word -> option byte) (R : (word -> option byte) -> Prop)
  : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch W m0 m' /\ wmono rsegs m0 m' /\ stk rsegs m' lo (bv_unsigned sp) /\ R m'.

Lemma vs_epilogue : forall (W : list ivl) (R : (word -> option byte) -> Prop)
  (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 g1 g8 g9 g18 g19 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (lo : Z) (junk : list byte) (m0 m : word -> option byte),
  rw_cells rsegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -48) -> lo + 48 <= bv_unsigned sp ->
  munch W m0 m -> wmono rsegs m0 m -> R m ->
  evt rsegs (vs_ret W a0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc lo m0 R)
    (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7
           g18 g19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14928) fc None m (seg_rom rsegs)).
Proof.
  intros W R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 g1 g8 g9 g18 g19 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    t3 t4 t5 t6 F fc lo junk m0 m FR ST LO MU WM HR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Hlo & _ & _).
  step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  step.
  apply evt_done. unfold vs_ret. do 12 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|exact HR].
Qed.

Lemma vs_tail : write_uint_contract ->
  forall (lo o LV w pa : Z) (cs : list cell) (PRE junk : list byte)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 g1 g19 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte),
  cs = [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  0 <= lo -> lo + 64 <= bv_unsigned sp -> 0 <= o -> o + 20 <= 2 ^ 64 ->
  (o + 20 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= o) ->
  0 <= pa < 65536 -> w = Z.of_nat (length PRE) -> w + 6 <= 20 -> w + write_uint_n pa <= LV ->
  vs_inv m0 m lo (bv_unsigned sp) o LV cs PRE ->
  evt rsegs (vs_ret [(bv_unsigned sp - 64, bv_unsigned sp); (o, o + LV + 1)] (Z_to_bv 64 (write_uint_n pa + w))
               ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc lo m0
               (fun m' => bytes_at rsegs m' o (PRE ++ write_uint_D pa ++ [Z_to_bv 8 0])))
    (MS (mkR g1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 pa) a0 a1 a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 w) g19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14910) fc None m (seg_rom rsegs)).
Proof.
  intros WU lo o LV w pa cs PRE junk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 g1 g19 t0 t1 t2
    a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m0 m Ecs Hlo HLO Ho HoN HD Hpa Hw Hw6 HwL INV.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (vs_n_range pa) as Hn3.
  assert (Hcs : cells_size cs = 48%nat) by (subst cs; reflexivity).
  step. step. step.
  eapply (vs_call WU (bv_unsigned sp) lo o LV w pa 0x1491c cs PRE);
    [lia | lia | lia | lia | lia | lia | exact Hcs | lia | exact Hw | lia | lia | lia | reflexivity
    | f_equal; lia | reflexivity | exact INV | ].
  intros m1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 INV1.
  step.
  rewrite (vs_addw (write_uint_n pa) w) by lia.
  step.
  assert (HS : store_ok rsegs m1 (wa (o + (write_uint_n pa + w))) 1 = true)
    by (eapply vs_inv_store_ok; [exact INV1 | lia | lia]).
  step.
  rewrite ?vs_le1 by lia.
  pose proof (vs_inv_store m0 m1 lo (bv_unsigned sp) o LV (write_uint_n pa + w) cs (PRE ++ write_uint_D pa)
                (Z_to_bv 8 0)) as INV2.
  specialize (INV2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hcs
                ltac:(rewrite length_app; unfold write_uint_n in *; lia) ltac:(lia) ltac:(lia) INV1).
  destruct INV2 as (FR & ST & MU & WM & _ & BP).
  subst cs.
  rewrite <- app_assoc in BP.
  eapply vs_epilogue; [exact FR | exact ST | lia | exact MU | exact WM | exact BP].
Qed.

Theorem reac_identity_reac_ver_str_holds : write_uint_contract -> reac_identity_reac_ver_str_contract.
Proof.
  intros WU. unfold reac_identity_reac_ver_str_contract, REAC_IDENTITY_REAC_VER_STR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ma mi pa o c lo E0 E1 E2 E3 E4 Hma Hmi Hpa Ho Hc ST HLO HACC.
  subst a0 a1 a2 a3 a4.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof ST as (Hlo & Hhi & _).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  step. step. step. step. step. step. step. step. step. step.
  rewrite (vs_eqb o 0) by lia.
  destruct (Z.eqb_spec o 0) as [Ho0 | Ho0]; cbv iota.
  - eapply evt_mono.
    + eapply vs_epilogue with (R := fun _ => True); [eassumption | eassumption | lia | exact MU | exact WM | exact I].
    + intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m' & E & MU' & WM' & ST' & _).
      exists y5, y6, y7. eexists. exists y11, y12, y13, y14, y15, y16, y17, y28, m'.
      split; [exact E|]. split; [exact WM'|]. split; [exact ST'|].
      cbn [orb].
      split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity] | exact MU'].
  - step. step. step.
    rewrite (vs_ltu c 20) by lia.
    destruct (Z.ltb_spec c 20) as [Hc20 | Hc20]; cbv iota.
    + eapply evt_mono.
      * eapply vs_epilogue with (R := fun _ => True); [eassumption | eassumption | lia | exact MU | exact WM | exact I].
      * intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m' & E & MU' & WM' & ST' & _).
        exists y5, y6, y7. eexists. exists y11, y12, y13, y14, y15, y16, y17, y28, m'.
        split; [exact E|]. split; [exact WM'|]. split; [exact ST'|].
        cbn [orb].
        split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity] | exact MU'].
    + destruct (HACC Ho0 Hc20) as [HW HD].
      pose proof (vs_LV ma mi pa) as HLV.
      pose proof (vs_n_range ma) as Hn1. pose proof (vs_n_range mi) as Hn2. pose proof (vs_n_range pa) as Hn3.
      pose proof HW as (_ & HoN & _).
      lazymatch goal with FR : rw_cells rsegs ?mc (bv_unsigned sp + -48) ?cs, STc : stk rsegs ?mc lo _ |- _ =>
        assert (INV0 : vs_inv m mc lo (bv_unsigned sp) o (reac_ver_str_LV ma mi pa) cs []);
        [ split; [exact FR | split; [exact STc | split;
            [ eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros x [H1 _]; repeat split; lia
            | split; [exact WM | split; [eapply wr_at_transport; [exact HW | exact WM] | apply bytes_at_nil; lia]]]]]
        | ];
        assert (Hcs : cells_size cs = 48%nat) by reflexivity;
        clear FR STc MU
      end.
      step. step. step.
      eapply (vs_call WU (bv_unsigned sp) lo o (reac_ver_str_LV ma mi pa) 0 ma 0x148d8 _ []);
        [lia | lia | lia | lia | lia | lia | exact Hcs | lia | reflexivity | lia | destruct (pa <? 10); lia
        | lia | reflexivity | f_equal; lia | reflexivity | exact INV0 | ].
      intros m1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 INV1.
      step.
      rewrite (vs_w1 (write_uint_n ma)) by lia.
      step. step.
      assert (HS1 : store_ok rsegs m1 (wa (o + write_uint_n ma)) 1 = true)
        by (eapply vs_inv_store_ok; [exact INV1 | lia | lia]).
      step.
      rewrite ?vs_le1 by lia.
      epose proof (vs_inv_store m m1 lo (bv_unsigned sp) o (reac_ver_str_LV ma mi pa) (write_uint_n ma) _
                    ([] ++ write_uint_D ma) (Z_to_bv 8 46)) as INV2.
      specialize (INV2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hcs
                    ltac:(reflexivity) ltac:(lia) ltac:(destruct (pa <? 10); lia) INV1).
      step. step. step.
      eapply (vs_call WU (bv_unsigned sp) lo o (reac_ver_str_LV ma mi pa) (write_uint_n ma + 1) mi 0x148f4 _
                (([] ++ write_uint_D ma) ++ [Z_to_bv 8 46]));
        [lia | lia | lia | lia | lia | lia | exact Hcs | lia
        | rewrite !length_app; cbn [length]; unfold write_uint_n; lia | lia | destruct (pa <? 10); lia
        | lia | reflexivity | f_equal; lia | reflexivity | exact INV2 | ].
      intros m2 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 INV3.
      step. step.
      rewrite (vs_addw (write_uint_n mi) (write_uint_n ma + 1)) by lia.
      step.
      rewrite (vs_ltu 9 pa) by lia.
      destruct (Z.ltb_spec 9 pa) as [Hpa9 | Hpa9]; cbv iota.
      * pose proof (vs_n_ge10 pa ltac:(lia)) as Hn3'.
        rewrite (proj2 (Z.ltb_ge pa 10)) in HLV by lia.
        eapply evt_mono.
        { eapply (vs_tail WU lo o (reac_ver_str_LV ma mi pa) (write_uint_n mi + (write_uint_n ma + 1)) pa _
                    ((([] ++ write_uint_D ma) ++ [Z_to_bv 8 46]) ++ write_uint_D mi));
            [reflexivity | lia | lia | lia | lia | lia | lia
            | rewrite !length_app; cbn [length]; unfold write_uint_n; lia | lia | lia | exact INV3]. }
        intros ms' (y5' & y6' & y7' & y11' & y12' & y13' & y14' & y15' & y16' & y17' & y28' & m' & E & MU' & WM' & ST' & BP').
        exists y5', y6', y7'. eexists. exists y11', y12', y13', y14', y15', y16', y17', y28', m'.
        split; [exact E|]. split; [exact WM'|]. split; [exact ST'|].
        cbn [orb].
        split; [f_equal; lia|]. split; [exact MU'|].
        eapply bytes_at_ext; [exact BP'|].
        unfold reac_ver_str_VER, reac_ver_str_DEC2. rewrite (proj2 (Z.ltb_ge pa 10)) by lia.
        rewrite <- !app_assoc. reflexivity.
      * rewrite (proj2 (Z.ltb_lt pa 10)) in HLV by lia.
        pose proof (vs_n_lt10 pa ltac:(lia)) as Hn3'.
        step. step.
        rewrite (vs_w1 (write_uint_n mi + (write_uint_n ma + 1))) by lia.
        step.
        assert (HS2 : store_ok rsegs m2 (wa (o + (write_uint_n mi + (write_uint_n ma + 1)))) 1 = true)
          by (eapply vs_inv_store_ok; [exact INV3 | lia | lia]).
        step.
        rewrite ?vs_le1 by lia.
        epose proof (vs_inv_store m m2 lo (bv_unsigned sp) o (reac_ver_str_LV ma mi pa)
                      (write_uint_n mi + (write_uint_n ma + 1)) _
                      ((([] ++ write_uint_D ma) ++ [Z_to_bv 8 46]) ++ write_uint_D mi) (Z_to_bv 8 48)) as INV4.
        specialize (INV4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hcs
                      ltac:(rewrite !length_app; cbn [length]; unfold write_uint_n; lia) ltac:(lia) ltac:(lia) INV3).
        eapply evt_mono.
        { eapply (vs_tail WU lo o (reac_ver_str_LV ma mi pa) (write_uint_n mi + (write_uint_n ma + 1) + 1) pa _
                    (((([] ++ write_uint_D ma) ++ [Z_to_bv 8 46]) ++ write_uint_D mi) ++ [Z_to_bv 8 48]));
            [reflexivity | lia | lia | lia | lia | lia | lia
            | rewrite !length_app; cbn [length]; unfold write_uint_n; lia | lia | lia | exact INV4]. }
        intros ms' (y5' & y6' & y7' & y11' & y12' & y13' & y14' & y15' & y16' & y17' & y28' & m' & E & MU' & WM' & ST' & BP').
        exists y5', y6', y7'. eexists. exists y11', y12', y13', y14', y15', y16', y17', y28', m'.
        split; [exact E|]. split; [exact WM'|]. split; [exact ST'|].
        cbn [orb].
        split; [f_equal; lia|]. split; [exact MU'|].
        eapply bytes_at_ext; [exact BP'|].
        unfold reac_ver_str_VER, reac_ver_str_DEC2. rewrite (proj2 (Z.ltb_lt pa 10)) by lia.
        rewrite (vs_D_lt10 pa) by lia.
        rewrite <- !app_assoc. reflexivity.
Qed.
