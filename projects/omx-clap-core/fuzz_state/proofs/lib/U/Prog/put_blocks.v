From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memcpy_c.
Import ListNotations.
Open Scope Z_scope.

Definition PUT : Z := 0x150bc.
Definition PUT_FRAME : Z := 48.

Definition pj_rec (m : word -> option byte) (o b l c f : Z) (pad : list byte) : Prop :=
  rw_cells rsegs m o [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 l); C8 (Z_to_bv 64 c); C4 (Z_to_bv 64 f); CB 4 pad].

Definition put_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (lo : Z) (W : list ivl) (m : word -> option byte) (P : (word -> option byte) -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch W m m' /\ wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\ P m'.

Lemma sx32_nz : forall f, 0 < f < 2^32 -> negb (bv_eqb (sx32 (Z_to_bv 64 f)) (Z_to_bv 64 0)) = true.
Proof.
  intros f Hf. unfold bv_eqb, sx32. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2^64). change (bv_half_modulus 32) with (2^31).
  change (bv_modulus 32) with (2^32). apply negb_true_iff, Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma land7 : forall o, o mod 8 = 0 -> Z.land o 7 = 0.
Proof. intros o H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Section PutEpilogue.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list ivl) (m m1 : word -> option byte) (P : (word -> option byte) -> Prop) (junk : list byte).
  Hypothesis MU : munch W m m1.
  Hypothesis WM : wmono rsegs m m1.
  Hypothesis LO : lo + PUT_FRAME <= bv_unsigned sp.
  Hypothesis ST : stk rsegs m1 lo (bv_unsigned sp - 48).
  Hypothesis FR : rw_cells rsegs m1 (bv_unsigned sp - 48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis PM : P m1.
  Lemma put_epilogue : forall ra1 t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 t3 t4 t5 t6,
    evt rsegs (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m P)
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x15194) fc None m1 (seg_rom rsegs)).
  Proof using MU WM LO ST FR PM.
    intros. unfold PUT_FRAME in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp.
    do 6 zstep.
    replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by lia.
    rewrite Z_to_bv_bv_unsigned.
    release_frame FR ST (bv_unsigned sp). zstep. finish.
  Qed.
End PutEpilogue.

Theorem put_failed :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o b l c f : Z) (pad : list byte),
    pj_rec m o b l c f pad -> o mod 8 = 0 -> 0 < f < 2^32 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PUT_FRAME <= bv_unsigned sp ->
    (o + 32 <= bv_unsigned sp - PUT_FRAME \/ bv_unsigned sp <= o) ->
    evt rsegs (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo
                 [(bv_unsigned sp - PUT_FRAME, bv_unsigned sp)] m (fun m' => pj_rec m' o b l c f pad))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PUT) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo o b l c f pad
    REC AL HF ST LO DO.
  unfold pj_rec, PUT, PUT_FRAME in *.
  pose proof (rw_cells_bound _ _ _ _ REC) as RO. change (0 <= o /\ o + 32 <= 2^64) in RO.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  carve_frame 48%nat ST.
  do 9 zstep.
  rewrite (land7 o AL). if_false.
  do 2 zstep.
  if_true_by (sx32_nz f HF).
  eapply put_epilogue; [exact MU | exact WM | unfold PUT_FRAME; lia | exact ST | exact FR | exact REC].
Qed.

Lemma wr_at_sub : forall m a n k n', wr_at rsegs m a n -> 0 <= k -> 0 <= n' -> k + n' <= n -> wr_at rsegs m (a + k) n'.
Proof.
  intros m a n k n' (Ha & Hn & H) Hk Hn' Hkn. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply H. lia.
Qed.

Lemma wr_at_shrink : forall m a n n', wr_at rsegs m a n -> 0 <= n' <= n -> wr_at rsegs m a n'.
Proof. intros m a n n' (Ha & Hn & H) Hn'. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed.

Definition put_text (m : word -> option byte) (o b l c : Z) (pad : list byte) (pre bs : list Z) : Prop :=
  pj_rec m o b (l + Z.of_nat (length bs)) c 0 pad /\ bytes_at rsegs m b (map (Z_to_bv 8) (pre ++ bs ++ [0])).

Lemma bv_ltu_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma bv_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Section PutCopy.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list ivl) (m m1 : word -> option byte) (junk junkb : list byte)
    (o b l c s : Z) (pad : list byte) (pre bs : list Z).
  Hypothesis MC : memcpy_contract.
  Hypothesis MU : munch W m m1.
  Hypothesis WM : wmono rsegs m m1.
  Hypothesis SW : sub_fp [(o + 8, o + 16); (b + l, b + l + Z.of_nat (length bs) + 1)] W.
  Hypothesis LO : lo + 48 <= bv_unsigned sp.
  Hypothesis ST : stk rsegs m1 lo (bv_unsigned sp - 48).
  Hypothesis FR : rw_cells rsegs m1 (bv_unsigned sp - 48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis REC : pj_rec m1 o b l c 0 pad.
  Hypothesis RB : 0 < b < 2^64.
  Hypothesis RC : 0 <= c < 2^64.
  Hypothesis RL : Z.of_nat (length pre) = l.
  Hypothesis MI : mem_inv rsegs m1.
  Hypothesis BUF : wr_at rsegs m1 (b + l) (Z.of_nat (length bs) + 1).
  Hypothesis JB : bytes_at rsegs m1 (b + l) junkb.
  Hypothesis LJ : length junkb = length bs.
  Hypothesis PRE : bytes_at rsegs m1 b (map (Z_to_bv 8) pre).
  Hypothesis SRC : bytes_at rsegs m1 s (map (Z_to_bv 8) bs).
  Hypothesis RS : s < 2^64.
  Hypothesis DOF : o + 32 <= lo \/ bv_unsigned sp <= o.
  Hypothesis DBF : b + l + Z.of_nat (length bs) + 1 <= lo \/ bv_unsigned sp <= b.
  Hypothesis DBO : b + l + Z.of_nat (length bs) + 1 <= o \/ o + 32 <= b.
  Hypothesis DSB : s + Z.of_nat (length bs) <= b + l \/ b + l + Z.of_nat (length bs) <= s.
  Lemma put_copy : forall ra1 t0 t1 t2 a2 a3 a4 a5 a6 a7 g19 t3 t4 t5 t6,
    evt rsegs (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m
                 (fun m' => put_text m' o b l c pad pre bs))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 (Z.of_nat (length bs)))
             (Z_to_bv 64 b) (Z_to_bv 64 l) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 s) g19
             s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1513c) fc None m1 (seg_rom rsegs)).
  Proof using MC MU WM SW LO ST FR REC RB RC RL MI BUF JB LJ PRE SRC RS DOF DBF DBO DSB.
    intros. unfold pj_rec in *.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
    pose proof ST as (SB1 & SB2 & _).
    pose proof (bytes_at_bound _ _ _ _ PRE) as PB. rewrite length_map in PB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SRB. rewrite length_map in SRB.
    pose proof (Nat2Z.is_nonneg (length bs)) as NN.
    set (N := Z.of_nat (length bs)) in *.
    assert (LM : Z.of_nat (length (map (Z_to_bv 8) bs)) = N) by (rewrite length_map; reflexivity).
    assert (LP : Z.of_nat (length (map (Z_to_bv 8) pre)) = l) by (rewrite length_map; exact RL).
    assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 48)) = bv_unsigned sp - 48) by (apply unsigned_lit; lia).
    pose proof BUF as (BB1 & BB2 & _).
    assert (UBL : bv_unsigned (Z_to_bv 64 (b + l)) = b + l) by (apply unsigned_lit; lia).
    assert (US : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
    assert (UN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
    assert (NN' : Z.to_nat N = length bs) by (unfold N; lia).
    pose proof (munch_refl [(o + 8, o + 16); (b + l, b + l + N + 1)] m1) as MUc.
    pose proof (wmono_refl rsegs m1) as WMc.
    do 2 zstep.
    rewrite bv_ltu_lit by lia. if_false.
    do 4 zstep.
    decide_tests. cbn [Z.b2z]. zb_fold_lits. if_false.
    replace (l + b) with (b + l) by ring.
    do 4 zstep.
    eapply evt_cut.
    { apply (MC (Z_to_bv 64 86372) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 N)
               (Z_to_bv 64 (b + l)) (Z_to_bv 64 s) (Z_to_bv 64 N)
               a3 a4 a5 a6 a7 (Z_to_bv 64 s) g19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
               (map (Z_to_bv 8) bs) junkb); rewrite ?UBL, ?US, ?UN.
      - exact SRC.
      - rewrite length_map, NN'. reflexivity.
      - split; [split|].
        + cbn [cells_wf cell_wf]. split; [lia | exact I].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact JB.
        + apply (wr_at_shrink _ _ _ _ BUF). cbn [cells_size csize]. lia.
      - exact DSB.
      - exact MI. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E & MU2 & WM2 & MI2 & DCL & SRC2).
    subst ms'. rewrite UBL, UN in MU2. rewrite UBL, UN in DCL.
    assert (DST : bytes_at rsegs m2 (b + l) (map (Z_to_bv 8) bs)).
    { destruct DCL as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r in DB. exact DB. }
    clear DCL SRC2 MI2.
    assert (ST2 := stk_transport_disjoint _ _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)).
    replace (ret_pc (Z_to_bv 64 86372)) with (Z_to_bv 64 86372) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    assert (FR2 := rw_cells_transport _ _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)).
    assert (REC2 := rw_cells_transport _ _ _ _ _ _ REC MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)).
    assert (PRE2 := bytes_at_transport _ _ _ _ _ _ PRE MU2 ltac:(rewrite length_map; cbn [disjoint_from]; lia)).
    assert (BUF2 := wr_at_transport _ _ _ _ _ BUF WM2).
    assert (MUc2 : munch [(o + 8, o + 16); (b + l, b + l + N + 1)] m1 m2)
      by (eapply munch_weaken; [|exact MU2]; unfold sub_fp; cbn [outside]; intros; lia).
    clear MUc FR REC PRE BUF MU2 ST JB SRC.
    rename WM2 into WMc2.
    do 6 zstep.
    rewrite bv_ltu_lit by lia. if_false.
    do 4 zstep.
    decide_tests. cbn [Z.b2z]. zb_fold_lits. if_false.
    zstep.
    rewrite bv_eqb_lit by lia. if_false.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HS : store_ok rsegs mm (wa (b + l + N)) 1 = true)
        by (apply (wr_at_store_ok rsegs mm (b + l) (N + 1) N 1%nat); [assumption | lia | lia]) end.
    zstep.
    replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by reflexivity.
    pose proof BUF2 as (WB1 & WB2 & _).
    eapply (put_epilogue ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m _
              (fun m' => put_text m' o b l c pad pre bs) junk).
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [exact SW|].
      apply munch_write; [exact MUc2 | lia | cbn [length]; lia | cbn [inside length]; lia].
    - eapply wmono_trans; [exact WM|]. apply wmono_write. exact WMc2.
    - unfold PUT_FRAME; lia.
    - apply stk_write; [exact ST2 | lia | cbn [length]; lia].
    - apply rw_cells_frame; [exact FR2 | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
    - unfold put_text, pj_rec. split.
      + apply rw_cells_frame; [exact REC2 | lia | cbn [length]; lia | cbn [cells_size csize length]; lia].
      + rewrite !map_app. apply bytes_at_app. split.
        * apply bytes_at_write_other; [exact PRE2 | lia | cbn [length]; lia | lia].
        * rewrite LP. apply bytes_at_app. split.
          -- apply bytes_at_write_other; [exact DST | lia | cbn [length]; lia | lia].
          -- rewrite LM. cbn [map]. apply bytes_at_write_same; [lia | cbn [length]; lia].
  Qed.
End PutCopy.

Theorem put_fast : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o b l c s : Z) (pad junkb : list byte)
         (pre bs : list Z),
    pj_rec m o b l c 0 pad -> o mod 8 = 0 -> 0 < b -> 0 <= c < 2^64 ->
    Z.of_nat (length pre) = l -> l + Z.of_nat (length bs) + 1 <= c ->
    wr_at rsegs m b c -> bytes_at rsegs m b (map (Z_to_bv 8) pre) -> bytes_at rsegs m s (map (Z_to_bv 8) bs) -> s < 2^64 ->
    bytes_at rsegs m (b + l) junkb -> length junkb = length bs -> mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PUT_FRAME <= bv_unsigned sp ->
    (o + 32 <= lo \/ bv_unsigned sp <= o) ->
    (b + c <= lo \/ bv_unsigned sp <= b) ->
    (b + c <= o \/ o + 32 <= b) ->
    (s + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= s) ->
    (s + Z.of_nat (length bs) <= b + l \/ b + l + Z.of_nat (length bs) <= s) ->
    evt rsegs (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo
                 [(bv_unsigned sp - PUT_FRAME, bv_unsigned sp); (o + 8, o + 16);
                  (b + l, b + l + Z.of_nat (length bs) + 1)] m
                 (fun m' => put_text m' o b l c pad pre bs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 s) (Z_to_bv 64 (Z.of_nat (length bs))) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PUT) fc None m (seg_rom rsegs)).
Proof.
  intros MC ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o b l c s pad junkb pre bs REC AL BP RC RL NEED BUF PRE SRC RS JB LJ MI ST LO DOF DBF DBO DSF DSB.
  unfold PUT, PUT_FRAME in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof BUF as (BB1 & BB2 & _).
  pose proof (bytes_at_bound _ _ _ _ SRC) as SRB. rewrite length_map in SRB.
  pose proof (Nat2Z.is_nonneg (length bs)) as NN.
  assert (LM : Z.of_nat (length (map (Z_to_bv 8) bs)) = Z.of_nat (length bs)) by (rewrite length_map; reflexivity).
  assert (LP : Z.of_nat (length (map (Z_to_bv 8) pre)) = l) by (rewrite length_map; exact RL).
  assert (LJZ : Z.of_nat (length junkb) = Z.of_nat (length bs)) by (rewrite LJ; reflexivity).
  assert (BUF1 : wr_at rsegs m (b + l) (Z.of_nat (length bs) + 1)) by (apply (wr_at_sub _ _ _ _ _ BUF); lia).
  clear BUF.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (o + 8, o + 16);
                          (b + l, b + l + Z.of_nat (length bs) + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold pj_rec in REC.
  pose proof (rw_cells_bound _ _ _ _ REC) as RO. change (0 <= o /\ o + 32 <= 2^64) in RO.
  carve_frame 48%nat ST.
  do 9 zstep.
  rewrite (land7 o AL). if_false.
  do 2 zstep.
  if_false.
  do 7 zstep.
  rewrite (bv_ltu_lit c (Z.of_nat (length bs) + l + 1)) by lia.
  if_true.
  zstep.
  eapply (put_copy ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo _ m _ _ junkb o b l c s pad pre bs);
    try eassumption.
  all: first [ unfold sub_fp; cbn [outside]; intros; lia | lia ].
Qed.

Definition PUT_REALLOC_RET : Z := 0x15124.
Definition FUZZ_REALLOC : Z := 0x1413c.

Lemma dbl_pow : forall f j need, 0 <= j <= 51 -> need <= 2^63 -> 51 <= j + Z.of_nat f ->
  exists j', j <= j' <= 51 /\ dbl f (4096 * 2^j) need = 4096 * 2^j' /\ need <= 4096 * 2^j'.
Proof.
  induction f as [|f IH]; intros j need Hj Hn Hf.
  - cbn [Z.of_nat] in Hf. assert (j = 51) by lia. subst j. exists 51. cbn [dbl].
    change (4096 * 2^51) with (2^63). split; [lia|]. split; [reflexivity|lia].
  - cbn [dbl]. destruct (Z.leb_spec need (4096 * 2^j)) as [H|H].
    + exists j. split; [lia|]. split; [reflexivity|exact H].
    + assert (J : j <> 51) by (intro E; subst j; change (4096 * 2^51) with (2^63) in H; lia).
      assert (E2 : 2 * (4096 * 2^j) = 4096 * 2^(j + 1)) by (rewrite Z.pow_add_r by lia; ring).
      rewrite E2.
      destruct (IH (j + 1) need ltac:(lia) Hn ltac:(rewrite Nat2Z.inj_succ in Hf; lia)) as (j' & Hj' & E & Hle).
      exists j'. split; [lia|]. split; [exact E|exact Hle].
Qed.

Lemma newcap_pow : forall c need, (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2^j) -> need <= 2^63 ->
  exists j, 0 <= j <= 51 /\ newcap c need = 4096 * 2^j /\ need <= newcap c need.
Proof.
  intros c need Hc Hn. unfold newcap.
  destruct Hc as [-> | (j & Hj & ->)].
  - change (if 0 =? 0 then 4096 else 0) with (4096 * 2^0).
    destruct (dbl_pow 64 0 need ltac:(lia) Hn ltac:(cbn; lia)) as (j' & Hj' & E & Hle).
    exists j'. rewrite E. split; [lia|]. split; [reflexivity|exact Hle].
  - assert (P : 0 < 2^j) by (apply Z.pow_pos_nonneg; lia).
    replace (4096 * 2^j =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (dbl_pow 64 j need Hj Hn ltac:(cbn; lia)) as (j' & Hj' & E & Hle).
    exists j'. rewrite E. split; [lia|]. split; [reflexivity|exact Hle].
Qed.

Section PutLoop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (need : Z).
  Hypothesis HN : 0 <= need <= 2^63.
  Lemma put_loop : forall f c s3, 0 < c < 2^64 -> need <= c * 2^(Z.of_nat f) ->
    (forall a2, evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 need) a1 a2 a3 a4 a5 a6 a7 s2
                                   (Z_to_bv 64 (dbl f c need)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x15118) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 need) a1 (Z_to_bv 64 c) a3 a4 a5 a6 a7 s2
                       s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1510c) fc None m (seg_rom rsegs)).
  Proof using HN.
    induction f as [|f IH]; intros c s3 Hc Hn K.
    - change (Z.of_nat 0) with 0 in Hn. rewrite Z.pow_0_r, Z.mul_1_r in Hn.
      do 3 zstep. rewrite (bv_ltu_lit c need) by lia. if_false. apply K.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia.
      do 3 zstep. rewrite (bv_ltu_lit c need) by lia.
      destruct (c <? need) eqn:H; cbv iota.
      + apply Z.ltb_lt in H.
        replace (Z.shiftl c 1) with (2 * c) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
        apply (IH (2 * c)); [lia | replace (2 * c * 2 ^ Z.of_nat f) with (c * (2 * 2 ^ Z.of_nat f)) by ring; exact Hn |].
        intros a2. specialize (K a2). cbn [dbl] in K. rewrite (proj2 (Z.leb_gt need c) H) in K. exact K.
      + apply Z.ltb_ge in H. specialize (K (Z_to_bv 64 (Z.shiftl c 1))). cbn [dbl] in K.
        rewrite (proj2 (Z.leb_le need c) H) in K. exact K.
  Qed.
End PutLoop.

Theorem put_grow_to_call :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o b l c n s : Z) (pad : list byte),
    pj_rec m o b l c 0 pad -> o mod 8 = 0 -> 0 <= l -> 0 <= n -> l + n + 1 <= 2^63 -> c < l + n + 1 ->
    (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2^j) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + PUT_FRAME <= bv_unsigned sp ->
    (o + 32 <= bv_unsigned sp - PUT_FRAME \/ bv_unsigned sp <= o) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
                         (junk : list byte),
         ms' = MS (mkR (Z_to_bv 64 PUT_REALLOC_RET) (Z_to_bv 64 (bv_unsigned sp - PUT_FRAME)) gp tp t0' t1' t2'
                       (Z_to_bv 64 o) (Z_to_bv 64 n) (Z_to_bv 64 b) (Z_to_bv 64 (newcap c (l + n + 1)))
                       a2' a3' a4' a5' a6' a7' (Z_to_bv 64 s) (Z_to_bv 64 (newcap c (l + n + 1)))
                       s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 FUZZ_REALLOC) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - PUT_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp - PUT_FRAME) /\
         rw_cells rsegs m' (bv_unsigned sp - PUT_FRAME) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
         pj_rec m' o b l c 0 pad)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 s) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 PUT) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o b l c n s pad REC AL HL HNN NEED GROW HC ST LO DO.
  unfold PUT, PUT_FRAME, PUT_REALLOC_RET, FUZZ_REALLOC in *. unfold pj_rec in REC.
  pose proof (rw_cells_bound _ _ _ _ REC) as RO. change (0 <= o /\ o + 32 <= 2^64) in RO.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  destruct (newcap_pow c (l + n + 1) HC NEED) as (jn & Hjn & NCE & NCL).
  assert (CR : c = 0 \/ 0 < c <= 2^63).
  { destruct HC as [-> | (j & Hj & ->)]; [left; reflexivity | right].
    assert (0 < 2^j) by (apply Z.pow_pos_nonneg; lia).
    assert (2^j <= 2^51) by (apply Z.pow_le_mono_r; lia). lia. }
  replace (l + n + 1) with (n + l + 1) in * by ring.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 9 zstep.
  rewrite (land7 o AL). if_false.
  do 2 zstep.
  if_false.
  do 7 zstep.
  rewrite (bv_ltu_lit c (n + l + 1)) by lia.
  if_false.
  zstep.
  destruct CR as [C0 | CP].
  - subst c. if_false. zstep.
    eapply put_loop with (f := 64%nat); [lia | lia | change (Z.of_nat 64) with 64; lia |].
    intros a2'. do 3 zstep.
    replace (dbl 64 4096 (n + l + 1)) with (newcap 0 (n + l + 1)) by reflexivity.
    finish.
    all: try eassumption.
  - rewrite (bv_eqb_lit c 0) by lia. if_true.
    eapply put_loop with (f := 64%nat); [lia | lia | change (Z.of_nat 64) with 64; lia |].
    intros a2'. do 3 zstep.
    replace (dbl 64 c (n + l + 1)) with (newcap c (n + l + 1))
      by (unfold newcap; replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    finish.
    all: try eassumption.
Qed.

Theorem put_after_realloc_null :
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lo o b l c f : Z) (pad junk : list byte)
         (ra1 t0 t1 t2 g9 a1 a2 a3 a4 a5 a6 a7 g18 g19 t3 t4 t5 t6 : word),
    pj_rec m o b l c f pad ->
    stk rsegs m lo (bv_unsigned sp - PUT_FRAME) -> lo + PUT_FRAME <= bv_unsigned sp ->
    rw_cells rsegs m (bv_unsigned sp - PUT_FRAME) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (o + 32 <= bv_unsigned sp - PUT_FRAME \/ bv_unsigned sp <= o) ->
    evt rsegs (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(o + 24, o + 28)] m
                 (fun m' => pj_rec m' o b l c 1 pad))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - PUT_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 o) g9 (Z_to_bv 64 0)
               a1 a2 a3 a4 a5 a6 a7 g18 g19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PUT_REALLOC_RET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo o b l c f pad junk
    ra1 t0 t1 t2 g9 a1 a2 a3 a4 a5 a6 a7 g18 g19 t3 t4 t5 t6 REC ST LO FR DO.
  unfold PUT_FRAME, PUT_REALLOC_RET in *. unfold pj_rec in REC.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (munch_refl [(o + 24, o + 28)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. if_true. do 3 zstep.
  eapply put_epilogue; [exact MU | exact WM | unfold PUT_FRAME; lia | exact ST | exact FR | exact REC].
Qed.

Theorem put_after_realloc : memcpy_contract ->
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lo o b l c q c' s : Z) (pad junk junkb : list byte) (pre bs : list Z)
         (ra1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    pj_rec m o b l c 0 pad -> 0 < q < 2^64 -> 0 <= c' < 2^64 ->
    Z.of_nat (length pre) = l -> l + Z.of_nat (length bs) + 1 <= c' ->
    wr_at rsegs m q c' -> bytes_at rsegs m q (map (Z_to_bv 8) pre) -> bytes_at rsegs m s (map (Z_to_bv 8) bs) -> s < 2^64 ->
    bytes_at rsegs m (q + l) junkb -> length junkb = length bs -> mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp - PUT_FRAME) -> lo + PUT_FRAME <= bv_unsigned sp ->
    rw_cells rsegs m (bv_unsigned sp - PUT_FRAME) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    (o + 32 <= lo \/ bv_unsigned sp <= o) ->
    (q + c' <= lo \/ bv_unsigned sp <= q) ->
    (q + c' <= o \/ o + 32 <= q) ->
    (s + Z.of_nat (length bs) <= q + l \/ q + l + Z.of_nat (length bs) <= s) ->
    (s + Z.of_nat (length bs) <= o \/ o + 32 <= s) ->
    evt rsegs (put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo
                 [(o, o + 24); (q + l, q + l + Z.of_nat (length bs) + 1)] m
                 (fun m' => put_text m' o q l c' pad pre bs))
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - PUT_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 o)
               (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 s) (Z_to_bv 64 c')
               s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PUT_REALLOC_RET) fc None m (seg_rom rsegs)).
Proof.
  intros MC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo o b l c q c' s pad junk junkb pre bs
    ra1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 REC HQ HC RL NEED BUF PRE SRC RS JB LJ MI ST LO FR DOF DBF DBO DSB DSO.
  unfold PUT_FRAME, PUT_REALLOC_RET in *. unfold pj_rec in REC.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof BUF as (BB1 & BB2 & _).
  pose proof (bytes_at_bound _ _ _ _ SRC) as SRB. rewrite length_map in SRB.
  pose proof (Nat2Z.is_nonneg (length bs)) as NN.
  assert (LM : Z.of_nat (length (map (Z_to_bv 8) bs)) = Z.of_nat (length bs)) by (rewrite length_map; reflexivity).
  assert (LP : Z.of_nat (length (map (Z_to_bv 8) pre)) = l) by (rewrite length_map; exact RL).
  assert (LJZ : Z.of_nat (length junkb) = Z.of_nat (length bs)) by (rewrite LJ; reflexivity).
  assert (BUF1 : wr_at rsegs m (q + l) (Z.of_nat (length bs) + 1)) by (apply (wr_at_sub _ _ _ _ _ BUF); lia).
  clear BUF.
  pose proof (munch_refl [(o, o + 24); (q + l, q + l + Z.of_nat (length bs) + 1)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. rewrite (bv_eqb_lit q 0) by lia. if_false.
  do 4 zstep.
  eapply (put_copy ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo _ m _ _ junkb o q l c' s pad pre bs);
    try eassumption.
  all: first [ unfold sub_fp; cbn [outside]; intros; lia | lia ].
Qed.
