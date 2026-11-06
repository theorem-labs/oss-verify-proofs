From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import HeadampModel GrantModel GrantSweepModel GroupaModel
  BuildSweepModel reac_headamp_tx_effective_c GroupaNeeds_c reac_grant_build_sweep_c.
Import ListNotations.
Open Scope Z_scope.

Ltac u8s := cbv beta; repeat match goal with |- context [bv_unsigned (Z_to_bv 8 ?x)] => rewrite (u8_lit x) by lia end.
Ltac br_not := let HC := fresh "HC" in if_cases HC; zify_cond HC; [exfalso; lia | ].
Ltac br_taken := let HC := fresh "HC" in if_cases HC; zify_cond HC; [ | exfalso; lia ].

Ltac exit_tail HOK spv :=
  do 15 zstep;
  lazymatch goal with
  | R0 : rw_cells _ _ (bv_unsigned spv + -240) _, RM : rw_cells _ _ (bv_unsigned spv + -232) _,
    RV : rw_cells _ _ (bv_unsigned spv + -224) _, RS : rw_cells _ _ (bv_unsigned spv + -104) _,
    ST : stk _ _ _ (bv_unsigned spv + -240) |- _ =>
      release_frame R0 ST (bv_unsigned spv + -232); release_frame RM ST (bv_unsigned spv + -224);
      release_frame RV ST (bv_unsigned spv + -104); release_frame RS ST (bv_unsigned spv)
  end;
  rewrite HOK; cbv iota;
  finish; try reflexivity.

Section Loop.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (s mx al t base w lo : Z) (T junk J J0 : list byte).
Hypothesis EFF : reac_headamp_tx_effective_contract.
Hypothesis BGS : reac_ctrl_build_grant_sweep_need.
Hypothesis Rsp : 0 <= bv_unsigned sp < 18446744073709551616.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis Hlo0 : 0 <= lo.
Hypothesis LO : lo + 2128 <= bv_unsigned sp.
Hypothesis Hs : 0 < s < 18446744073709551616.
Hypothesis Hmx : -2^31 <= mx < 2^31.
Hypothesis Hal : 0 < al < 18446744073709551616.
Hypothesis DAL : al + 2 <= bv_unsigned sp - 2128 \/ bv_unsigned sp <= al.
Hypothesis Hb : 0 <= base < 256.
Hypothesis HW : 1 <= w <= 40.
Hypothesis HBW : base + w <= 48.
Hypothesis HLT : length T = 460%nat.
Hypothesis HT4 : t mod 4 = 0.
Hypothesis DT : t + 460 <= bv_unsigned sp - 2128 \/ bv_unsigned sp <= t.
Hypothesis H01 : tx_set01 T.
Hypothesis HLEG : tx_legal T.
Hypothesis HLJ : length J = 120%nat.
Hypothesis DROWS : (8 + 3 * w <=? mx) = true ->
  s + 34 * (8 + 3 * w) <= bv_unsigned sp - 2128 \/ bv_unsigned sp <= s.
Hypothesis DROWR : (8 + 3 * w <=? mx) = true ->
  s + 34 * (8 + 3 * w) <= IM4_ROW \/ IM4_ROW + 24 <= s.
Hypothesis DROW : IM4_ROW + 24 <= bv_unsigned sp - 2128 \/ bv_unsigned sp <= IM4_ROW.

Lemma length_CTRL_ROW_BYTES : length IM4_ROW_BYTES = 24%nat.
Proof. reflexivity. Qed.

Local Notation VALS := (sweep_vals T t base (Z.to_nat w)).

Definition INV (mc : word -> option byte) (k : nat) : Prop :=
  rw_cells rsegs mc (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  rw_cells rsegs mc (bv_unsigned sp + -232) [C8 (Z_to_bv 64 mx)] /\
  rw_cells rsegs mc (bv_unsigned sp + -240) [CB 8 J0] /\
  bytes_at rsegs mc (bv_unsigned sp + -224) (firstn k VALS ++ skipn k J) /\
  wr_at rsegs mc (bv_unsigned sp + -224) 120 /\
  stk rsegs mc lo (bv_unsigned sp + -240) /\
  munch [(bv_unsigned sp - 2128, bv_unsigned sp)] m mc /\ wmono rsegs m mc /\ mem_inv rsegs mc /\
  bytes_at rsegs mc t T /\ bytes_at rsegs mc al [Z_to_bv 8 base; Z_to_bv 8 w] /\
  bytes_at rsegs mc IM4_ROW IM4_ROW_BYTES /\
  ((8 + 3 * w <=? mx) = true -> rw_cells rsegs mc s [CB (Z.to_nat (34 * (8 + 3 * w))) junk]).

Lemma length_VALS : length VALS = (3 * Z.to_nat w)%nat.
Proof. apply length_sweep_vals. Qed.

Lemma INV_store : forall mc k, INV mc k -> (k < 3 * Z.to_nat w)%nat ->
  INV (write_to_mem mc (wa (bv_unsigned sp + -224 + Z.of_nat k)) [nth k VALS (Z_to_bv 8 0)]) (S k).
Proof.
  intros mc k (RS & RM & R0 & VB & VW & ST & MU & WM & MI & HT & HA & HRW & HR) Hk.
  pose proof length_VALS as Lv.
  assert (HS : store_ok rsegs mc (wa (bv_unsigned sp + -224 + Z.of_nat k)) 1 = true)
    by (apply (wr_at_store_ok rsegs mc _ 120 (Z.of_nat k) 1 VW); lia).
  set (b := nth k VALS (Z_to_bv 8 0)).
  unfold INV.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))))).
  - apply rw_cells_frame; [exact RS | lia | cbn [length]; lia | right; cbn [length cells_size csize]; lia].
  - apply rw_cells_frame; [exact RM | lia | cbn [length]; lia | left; cbn [length cells_size csize]; lia].
  - apply rw_cells_frame; [exact R0 | lia | cbn [length]; lia | left; cbn [length cells_size csize]; lia].
  - pose proof (bytes_at_write_inside rsegs mc _ _ (Z.of_nat k) [b] VB ltac:(lia)
                  ltac:(rewrite length_vbytes by lia; cbn [length]; lia)) as H.
    rewrite Nat2Z.id in H. rewrite (vstore VALS J k b (Z_to_bv 8 0)) in H by (try lia; reflexivity). exact H.
  - apply wr_at_write. exact VW.
  - apply stk_write; [exact ST | lia | cbn [length]; lia].
  - apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside]; left; cbn [length]; lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS].
  - apply bytes_at_write_other; [exact HT | lia | cbn [length]; lia | rewrite HLT; cbn [length]; lia].
  - apply bytes_at_write_other; [exact HA | lia | cbn [length]; lia | cbn [length]; lia].
  - apply bytes_at_write_other; [exact HRW | lia | cbn [length]; lia | rewrite length_CTRL_ROW_BYTES; cbn [length]; lia].
  - intros H. specialize (HR H). specialize (DROWS H).
    apply rw_cells_frame; [exact HR | lia | cbn [length]; lia |].
    cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. cbn [length]. lia.
Qed.

Definition Qbs : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                    (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\
    mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    bytes_at rsegs m' IM4_ROW IM4_ROW_BYTES /\
    if 8 + 3 * w <=? mx
    then r = Z_to_bv 64 (8 + 3 * w) /\
         munch [(bv_unsigned sp - 2128, bv_unsigned sp); (s, s + 34 * (8 + 3 * w))] m m' /\
         rw_cells rsegs m' s [CB (Z.to_nat (34 * (8 + 3 * w))) (SWEEP base (Z.to_nat w) VALS)]
    else r = Z_to_bv 64 (-1) /\
         munch [(bv_unsigned sp - 2128, bv_unsigned sp)] m m'.

Lemma transport_frame : forall mc m' W,
  munch W mc m' -> wmono rsegs mc m' ->
  disjoint_from W (bv_unsigned sp + -240) 240 ->
  rw_cells rsegs mc (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells rsegs mc (bv_unsigned sp + -232) [C8 (Z_to_bv 64 mx)] ->
  rw_cells rsegs mc (bv_unsigned sp + -240) [CB 8 J0] ->
  forall X, rw_cells rsegs mc (bv_unsigned sp + -224) [CB 120 X] ->
  rw_cells rsegs m' (bv_unsigned sp + -104)
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  rw_cells rsegs m' (bv_unsigned sp + -232) [C8 (Z_to_bv 64 mx)] /\
  rw_cells rsegs m' (bv_unsigned sp + -240) [CB 8 J0] /\
  rw_cells rsegs m' (bv_unsigned sp + -224) [CB 120 X].
Proof.
  intros mc m' W MU WM D RS RM R0 X RV.
  assert (G : forall A n, bv_unsigned sp + -240 <= A -> A + n <= bv_unsigned sp -> disjoint_from W A n).
  { clear -D. induction W as [|[a b] W IH]; intros A n H1 H2; cbn in *; [exact I|].
    destruct D as [D1 D2]. split; [lia | apply IH; [exact D2 | lia | lia]]. }
  split; [|split; [|split]]; eapply rw_cells_transport; eauto; cbn [cells_size csize]; apply G; lia.
Qed.

Lemma tail_ok : forall mc RA T0 T1 T2 A0 A1 A2 A3 A4 A5 A6 A7 S0' S5' S6' S7' S8' S9' S10' S11' T3 T4 T5 T6,
  INV mc (3 * Z.to_nat w) ->
  evt rsegs Qbs
    (MS (mkR RA (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp T0 T1 T2 S0' (Z_to_bv 64 s)
             A0 A1 A2 A3 A4 A5 A6 A7 (Z_to_bv 64 w) (Z_to_bv 64 al) (Z_to_bv 64 t) S5' S6' S7' S8' S9'
             S10' S11' T3 T4 T5 T6)
        F (Z_to_bv 64 0x15464) fc None mc (seg_rom rsegs)).
Proof.
  intros mc RA T0 T1 T2 A0 A1 A2 A3 A4 A5 A6 A7 S0' S5' S6' S7' S8' S9' S10' S11' T3 T4 T5 T6
    (RS & RM & R0 & VB & VW & ST & MU & WM & MI & HT & HA & HRW & HR).
  pose proof length_VALS as Lv.
  assert (RDB : ov_read_bytes rsegs mc (wa (al + 0)) 1 = Some [Z_to_bv 8 base])
    by (apply (rd_byte_at _ _ _ _ _ _ HA); [lia | cbn; lia | reflexivity]).
  rewrite Z.add_0_r in RDB.
  assert (U240 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -240)) = bv_unsigned sp + -240)
    by (apply unsigned_lit; lia).
  assert (VB' : bytes_at rsegs mc (bv_unsigned sp + -224) VALS).
  { rewrite (firstn_all2 VALS) in VB by lia. apply bytes_at_app in VB. exact (proj1 VB). }
  assert (RV : rw_cells rsegs mc (bv_unsigned sp + -224)
                 [CB 120 (firstn (3 * Z.to_nat w) VALS ++ skipn (3 * Z.to_nat w) J)]).
  { split; [split; [cbn [cells_wf cell_wf]; split; [rewrite length_vbytes by lia; exact HLJ | exact I] |] | exact VW].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact VB. }
  zstep. u8s.
  do 5 zstep.
  unfold reac_ctrl_build_grant_sweep_need, REAC_CTRL_BUILD_GRANT_SWEEP, REAC_CTRL_BUILD_GRANT_SWEEP_STACK in BGS.
  eapply evt_cut.
  { eapply BGS with (s := s) (mx := mx) (base := base) (w := w) (V := bv_unsigned sp + -224) (lo := lo)
                    (vals := VALS) (junk := junk).
    all: try reflexivity.
    all: try lia.
    all: try exact VB'.
    all: try exact MI.
    all: try exact HRW.
    all: try (rewrite U240; exact ST).
    all: try (apply sweep_vals_legal; [exact H01 | exact HLEG | lia | rewrite Z2Nat.id; lia]).
    all: try (rewrite U240; lia).
    intros H. assert (Hok : (8 + 3 * w <=? mx) = true) by (apply Z.leb_le; lia).
    pose proof (DROWS Hok). pose proof (DROWR Hok). rewrite U240.
    split; [exact (HR Hok) | split; [lia | split; lia]]. }
  intros ms' (x1 & x2 & x3 & r & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & m' & -> & WM' & MI' & ST' & HRW' & HIF).
  replace (ret_pc (Z_to_bv 64 0x1547c)) with (Z_to_bv 64 0x1547c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite U240 in ST'.
  destruct (8 + 3 * w <=? mx) eqn:HOK.
  - destruct HIF as (-> & MUc & RWc).
    pose proof (DROWS eq_refl) as DR.
    rewrite U240 in MUc.
    destruct (transport_frame mc m' _ MUc WM' ltac:(cbn [disjoint_from]; repeat split; try exact I; lia)
                RS RM R0 _ RV) as (RS' & RM' & R0' & RV').
    assert (MUf : munch [(bv_unsigned sp - 2128, bv_unsigned sp); (s, s + 34 * (8 + 3 * w))] m m').
    { apply (munch_trans _ m mc m').
      - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x (H1 & _ & _). split; [exact H1 | exact I].
      - eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside].
        intros x (H1 & H2 & _). repeat split; try exact I; lia. }
    pose proof (wmono_trans rsegs m mc m' WM WM') as WMf.
    clear RS RM R0 RV VB VW VB' ST MU WM MI HT HA HRW HR MUc WM'.
    do 15 zstep.
    release_frame R0' ST' (bv_unsigned sp + -232).
    release_frame RM' ST' (bv_unsigned sp + -224).
    release_frame RV' ST' (bv_unsigned sp + -104).
    release_frame RS' ST' (bv_unsigned sp).
    unfold Qbs. rewrite HOK. cbv iota.
    finish; try reflexivity.
  - destruct HIF as (-> & MUc).
    rewrite U240 in MUc.
    destruct (transport_frame mc m' _ MUc WM' ltac:(cbn [disjoint_from]; repeat split; try exact I; lia)
                RS RM R0 _ RV) as (RS' & RM' & R0' & RV').
    assert (MUf : munch [(bv_unsigned sp - 2128, bv_unsigned sp)] m m').
    { apply (munch_trans _ m mc m'); [exact MU |].
      eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside].
      intros x (H1 & _). repeat split; try exact I; lia. }
    pose proof (wmono_trans rsegs m mc m' WM WM') as WMf.
    clear RS RM R0 RV VB VW VB' ST MU WM MI HT HA HRW HR MUc WM'.
    do 15 zstep.
    release_frame R0' ST' (bv_unsigned sp + -232).
    release_frame RM' ST' (bv_unsigned sp + -224).
    release_frame RV' ST' (bv_unsigned sp + -104).
    release_frame RS' ST' (bv_unsigned sp).
    unfold Qbs. rewrite HOK. cbv iota.
    finish; try reflexivity.
Qed.

Lemma outer_ok : forall n c mc RA T0 T1 T2 A0 A1 A2 A3 A4 A5 A6 A7 S5' S6' S11' T3 T4 T5 T6 C3 C,
  (c + n = Z.to_nat w)%nat -> (0 < n)%nat -> INV mc (3 * c) ->
  C3 = 3 * Z.of_nat c -> C = Z.of_nat c ->
  evt rsegs Qbs
    (MS (mkR RA (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp T0 T1 T2 (Z_to_bv 64 C3) (Z_to_bv 64 s)
             A0 A1 A2 A3 A4 A5 A6 A7 (Z_to_bv 64 w) (Z_to_bv 64 al) (Z_to_bv 64 t) S5' S6'
             (Z_to_bv 64 C) (Z_to_bv 64 120) (Z_to_bv 64 (bv_unsigned sp + -224)) (Z_to_bv 64 3) S11' T3 T4 T5 T6)
        F (Z_to_bv 64 0x1541c) fc None mc (seg_rom rsegs)).
Proof.
  induction n as [|n IH];
    intros c mc RA T0 T1 T2 A0 A1 A2 A3 A4 A5 A6 A7 S5' S6' S11' T3 T4 T5 T6 C3 C Hcn Hn HI -> ->; [lia|].
  pose proof length_VALS as Lv.
  assert (Hc : (c < Z.to_nat w)%nat) by lia.
  pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HA & _).
  assert (RDB : ov_read_bytes rsegs mc (wa (al + 0)) 1 = Some [Z_to_bv 8 base])
    by (apply (rd_byte_at _ _ _ _ _ _ HA); [lia | cbn; lia | reflexivity]).
  rewrite Z.add_0_r in RDB. clear HA.
  pose proof EFF as EFF'. unfold reac_headamp_tx_effective_contract, REAC_HEADAMP_TX_EFFECTIVE in EFF'.
  zstep. zstep. u8s. zstep. zstep. zstep.
  rewrite (land255_small (base + Z.of_nat c)) by lia.
  do 4 zstep.
  pose proof HI as (_ & _ & _ & _ & VW0 & _ & _ & _ & _ & HT0 & _ & _).
  eapply evt_cut.
  { eapply EFF' with (t := t) (ch := base + Z.of_nat c) (p := 0) (T := T);
      [reflexivity | reflexivity | reflexivity | lia | lia | right; split; [exact HLT | split; [exact HT0 | exact HT4]]]. }
  intros ms' (e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11 & e12 & e13 & e14 & ->).
  replace (ret_pc (Z_to_bv 64 0x15440)) with (Z_to_bv 64 0x15440) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  zstep. try br_not.
  zstep. zstep.
  assert (HS : store_ok rsegs mc (wa (bv_unsigned sp + -224 + Z.of_nat (3 * c))) 1 = true)
    by (apply (wr_at_store_ok rsegs mc _ 120 (Z.of_nat (3 * c)) 1 VW0); lia).
  clear VW0 HT0.
  zstep.
  rewrite (le1_lit8 (eff T t (base + Z.of_nat c) 0)) by apply eff_range.
  replace (Z_to_bv 8 (eff T t (base + Z.of_nat c) 0)) with (nth (3 * c) VALS (Z_to_bv 8 0))
    by (rewrite <- (Nat.add_0_r (3 * c)), nth_sweep_vals by lia; reflexivity).
  pose proof (INV_store mc (3 * c) HI ltac:(lia)) as HI1. clear HI HS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end. clearbody m1.
  zstep. zstep. try br_taken.
  do 4 zstep.
  pose proof HI1 as (_ & _ & _ & _ & VW1 & _ & _ & _ & _ & HT1 & _ & _).
  eapply evt_cut.
  { eapply EFF' with (t := t) (ch := base + Z.of_nat c) (p := 1) (T := T);
      [reflexivity | reflexivity | reflexivity | lia | lia | right; split; [exact HLT | split; [exact HT1 | exact HT4]]]. }
  intros ms' (f1 & f2 & f3 & f4 & f5 & f6 & f7 & f8 & f9 & f10 & f11 & f12 & f13 & f14 & ->).
  replace (ret_pc (Z_to_bv 64 0x15440)) with (Z_to_bv 64 0x15440) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  zstep. try br_not.
  zstep. zstep.
  assert (HS : store_ok rsegs m1 (wa (bv_unsigned sp + -224 + Z.of_nat (S (3 * c)))) 1 = true)
    by (apply (wr_at_store_ok rsegs m1 _ 120 (Z.of_nat (S (3 * c))) 1 VW1); lia).
  clear VW1 HT1.
  zstep.
  rewrite (le1_lit8 (eff T t (base + Z.of_nat c) 1)) by apply eff_range.
  replace (Z_to_bv 8 (eff T t (base + Z.of_nat c) 1)) with (nth (S (3 * c)) VALS (Z_to_bv 8 0))
    by (replace (S (3 * c)) with (3 * c + 1)%nat by lia; rewrite nth_sweep_vals by lia; reflexivity).
  pose proof (INV_store m1 (S (3 * c)) HI1 ltac:(lia)) as HI2. clear HI1 HS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end. clearbody m2.
  zstep. zstep. try br_taken.
  do 4 zstep.
  pose proof HI2 as (_ & _ & _ & _ & VW2 & _ & _ & _ & _ & HT2 & _ & _).
  eapply evt_cut.
  { eapply EFF' with (t := t) (ch := base + Z.of_nat c) (p := 2) (T := T);
      [reflexivity | reflexivity | reflexivity | lia | lia | right; split; [exact HLT | split; [exact HT2 | exact HT4]]]. }
  intros ms' (g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & g9 & g10 & g11 & g12 & g13 & g14 & ->).
  replace (ret_pc (Z_to_bv 64 0x15440)) with (Z_to_bv 64 0x15440) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  zstep. try br_not.
  zstep. zstep.
  assert (HS : store_ok rsegs m2 (wa (bv_unsigned sp + -224 + Z.of_nat (S (S (3 * c))))) 1 = true)
    by (apply (wr_at_store_ok rsegs m2 _ 120 (Z.of_nat (S (S (3 * c)))) 1 VW2); lia).
  clear VW2 HT2.
  zstep.
  rewrite (le1_lit8 (eff T t (base + Z.of_nat c) 2)) by apply eff_range.
  replace (Z_to_bv 8 (eff T t (base + Z.of_nat c) 2)) with (nth (S (S (3 * c))) VALS (Z_to_bv 8 0))
    by (replace (S (S (3 * c))) with (3 * c + 2)%nat by lia; rewrite nth_sweep_vals by lia; reflexivity).
  pose proof (INV_store m2 (S (S (3 * c))) HI2 ltac:(lia)) as HI3. clear HI2 HS.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m3 := mm) in * end. clearbody m3.
  zstep. zstep. try br_not.
  zstep. zstep. zstep.
  if_cases HCW; zify_cond HCW.
  - eapply (IH (S c)).
    + lia.
    + lia.
    + replace (3 * S c)%nat with (S (S (S (3 * c)))) by lia. exact HI3.
    + lia.
    + lia.
  - eapply tail_ok.
    replace (3 * Z.to_nat w)%nat with (S (S (S (3 * c)))) by lia. exact HI3.
Qed.

End Loop.

Theorem reac_grant_build_sweep_holds :
  reac_headamp_tx_effective_contract -> reac_ctrl_build_grant_sweep_need -> reac_grant_build_sweep_contract.
Proof.
  intros EFF BGS.
  unfold reac_grant_build_sweep_contract, REAC_GRANT_BUILD_SWEEP, REAC_GRANT_BUILD_SWEEP_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m s mx al t base w lo T junk -> -> -> -> Hs Hmx Hal SP16 HMI ST LO HAL HLT HT HT4 DT H01 HLEG HROW DROW HROWS.
  pose proof (eq_refl : length IM4_ROW_BYTES = 24%nat) as HRL.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with 18446744073709551616 in Rsp, Hs, Hal.
  pose proof ST as (Hlo0 & _ & _).
  pose proof (bytes_at_bound rsegs m t _ HT) as Bt. rewrite HLT in Bt.
  change (Z.of_nat 460) with 460 in Bt. change (2 ^ 64) with 18446744073709551616 in Bt.
  pose proof (munch_refl [(bv_unsigned sp - 2128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 104%nat ST. rename FR into RS.
  carve_frame 120%nat ST. rename FR into RV.
  carve_frame 8%nat ST. rename FR into RM.
  carve_frame 8%nat ST. rename FR into R0.
  do 17 zstep.
  if_cases HC1; zify_cond HC1.
  { assert (HOK : bsw_ok s al mx base w = false)
      by (unfold bsw_ok; rewrite (proj2 (Z.eqb_eq s 0) HC1); reflexivity).
    exit_tail HOK sp. }
  zstep. zstep.
  if_cases HC2; zify_cond HC2.
  { assert (HOK : bsw_ok s al mx base w = false)
      by (unfold bsw_ok; rewrite (proj2 (Z.eqb_eq al 0) HC2), andb_false_r; reflexivity).
    exit_tail HOK sp. }
  destruct (HAL HC2) as (Hb & Hw & HALB & DAL). clear HAL.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
  pose proof (bytes_at_transport rsegs _ m mA al _ HALB MU ltac:(cbn [disjoint_from length]; lia)) as HALB0.
  clear HALB. rename HALB0 into HALB.
  assert (RDW : ov_read_bytes rsegs mA (wa (al + 1)) 1 = Some [Z_to_bv 8 w])
    by (apply (rd_byte_at _ _ _ _ _ _ HALB); [lia | cbn; lia | reflexivity]).
  assert (RDB : ov_read_bytes rsegs mA (wa (al + 0)) 1 = Some [Z_to_bv 8 base])
    by (apply (rd_byte_at _ _ _ _ _ _ HALB); [lia | cbn; lia | reflexivity]).
  rewrite Z.add_0_r in RDB.
  zstep. u8s. zstep. zstep. zstep.
  if_cases HC3; zify_cond HC3.
  { assert (HOK : bsw_ok s al mx base w = false)
      by (destruct (bsw_ok s al mx base w) eqn:E; [exfalso; apply bsw_ok_spec in E; Z.div_mod_to_equations; lia | reflexivity]).
    exit_tail HOK sp. }
  assert (HW : 1 <= w <= 40) by (Z.div_mod_to_equations; lia).
  zstep. zstep. u8s. zstep. zstep. zstep. zstep.
  if_cases HC4; zify_cond HC4.
  { assert (HOK : bsw_ok s al mx base w = false)
      by (destruct (bsw_ok s al mx base w) eqn:E; [exfalso; apply bsw_ok_spec in E; Z.div_mod_to_equations; lia | reflexivity]).
    exit_tail HOK sp. }
  assert (HBW : base + w <= 48) by (Z.div_mod_to_equations; lia).
  zstep. zstep.
  if_cases HC5; zify_cond HC5; [ | exfalso; Z.div_mod_to_equations; lia ].
  assert (HGO : bsw_ok s al mx base w = (8 + 3 * w <=? mx)) by (apply bsw_ok_go; lia).
  rewrite HGO in HROWS |- *. clear HGO.
  do 6 zstep.
  lazymatch type of RV with rw_cells _ _ _ [CB 120 ?JJ] =>
    assert (HLJ : length JJ = 120%nat) by (destruct RV as [[[HJ _] _] _]; exact HJ);
    lazymatch type of R0 with rw_cells _ _ _ [CB 8 ?JJ0] =>
      eapply outer_ok with (J := JJ) (J0 := JJ0) (junk := junk) (n := Z.to_nat w) (c := 0%nat) end end.
  all: try exact EFF; try exact BGS; try assumption; try lia.
  - unfold INV. cbn [firstn skipn app Nat.mul Nat.add].
    refine (conj RS (conj RM (conj R0 (conj _ (conj (proj2 RV) (conj ST (conj MU (conj WM (conj HMI (conj HT (conj HALB (conj HROW _)))))))))))).
    + pose proof RV as [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
    + intros H. destruct (HROWS H) as (R & DRW & DRR). eapply rw_cells_transport; [exact R | exact MU | exact WM |].
      cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia | exact I].
Qed.
