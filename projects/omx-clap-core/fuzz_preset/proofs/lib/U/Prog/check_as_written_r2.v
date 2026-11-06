From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Exec Frame FP Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct ex_value_c ex_value_m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strtod_c ex_value_c ex_ws_c check_as_written_s.
Import ListNotations.
Open Scope Z_scope.

Lemma caw_r2_rw_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[W B] R].
  apply cells_wf_app in W as [W1 W2]. rewrite cells_bytes_app in B. apply bytes_at_app in B as [B1 B2].
  rewrite cells_size_app in R. rewrite (cells_bytes_length cs1 W1) in B2.
  destruct R as (R1 & R2 & R3).
  split; split; try (split; assumption).
  - split; [lia|]. split; [lia|]. intros i Hi. apply R3. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply R3. lia.
Qed.

Lemma caw_r2_rw_conv : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E.
  assert (L : cells_size cs' = cells_size cs)
    by (rewrite <- (cells_bytes_length cs' W'), <- (cells_bytes_length cs W), E; reflexivity).
  split; [split; [exact W' | rewrite E; exact B] | rewrite L; exact R].
Qed.

Lemma caw_r2_task : forall m m' lo hi,
  MemNorm.task_mem rsegs m -> munch [(lo, hi)] m m' -> stk rsegs m lo hi -> MemNorm.task_mem rsegs m'.
Proof.
  intros m m' lo hi T MU (L1 & L2 & SK) a b E.
  destruct (Z_le_gt_dec lo (bv_unsigned a)) as [H1|H1];
    [destruct (Z_lt_ge_dec (bv_unsigned a) hi) as [H2|H2]|].
  - destruct (SK (bv_unsigned a) (conj H1 H2)) as [W _]. unfold wa in W. rewrite Z_to_bv_lit_self in W.
    destruct (m a) as [b'|] eqn:Em; [exact (T a b' Em)|].
    left. intro FS. apply W. unfold wview. rewrite Em, FS. reflexivity.
  - rewrite (MU a) in E by (cbn [outside]; split; [lia | exact I]). exact (T a b E).
  - rewrite (MU a) in E by (cbn [outside]; split; [lia | exact I]). exact (T a b E).
Qed.

Lemma caw_r2_foot : forall v D b k z, ex_off v D b k -> pj_foot v D z -> outside [(b, b + k)] z.
Proof.
  intros v D b k z [Hv HD] Hz. cbn [outside]. split; [|exact I].
  destruct Hz as [Hz | (bk & Hin & Hz)].
  - unfold ex_apart in Hv. lia.
  - rewrite Forall_forall in HD. specialize (HD bk Hin). unfold ex_apart, pj_holds in *. lia.
Qed.

Lemma caw_r2_bytes : forall W m m' a bs,
  bytes_at rsegs m a bs -> munch W m m' -> (Z.of_nat (length bs) <= 0 \/ disjoint_from W a (Z.of_nat (length bs))) ->
  bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs B MU [H | H].
  - destruct bs as [|b0 bs]; [|cbn [length] in H; lia].
    pose proof (bytes_at_bound _ _ _ _ B) as HB. apply bytes_at_nil. cbn [length Z.of_nat] in HB. lia.
  - exact (bytes_at_transport rsegs W m m' a bs B MU H).
Qed.

Lemma caw_r2_v : forall rcv doc, 0 <= rcv < 2 ^ 64 -> 0 <= doc < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 rcv)) + -1)))
                     (bv_unsigned (Z_to_bv 64 doc))) = Z_to_bv 64 (caw_v rcv doc).
Proof.
  intros rcv doc Hr Hd. rewrite (unsigned_lit doc) by lia. unfold caw_v.
  destruct (Z.eqb_spec rcv 0) as [->|Hn].
  - change (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0)) + -1))) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
  - assert (E : bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 rcv)) = 1).
    { rewrite v_sltu_b2z, (unsigned_lit rcv) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      replace (0 <? rcv) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    rewrite E. change (bv_unsigned (Z_to_bv 64 (1 + -1))) with 0. rewrite Z.land_0_l. reflexivity.
Qed.

(* The record at S1 + 8 after the stores of 0x13b0c, 0x13b10, 0x13b2c and 0x13b30, cut into the two pieces of ex_rec. *)
Lemma caw_r2_rec : forall m S1 j0 p e scr,
  rw_cells rsegs m S1 [CB 8 j0; C8 p; C8 e; C8 (Z_to_bv 64 0); C8 scr; C8 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (S1 + 8) [C8 p; C8 e; C4 (Z_to_bv 64 0)] /\
  rw_cells rsegs m (S1 + 8 + 24) [C8 scr; C4 (Z_to_bv 64 0)].
Proof.
  intros m S1 j0 p e scr H.
  apply (caw_r2_rw_app m S1 [CB 8 j0] [C8 p; C8 e; C8 (Z_to_bv 64 0); C8 scr; C8 (Z_to_bv 64 0)]) in H as [_ H].
  apply (caw_r2_rw_conv _ _ _ ([C8 p; C8 e; C4 (Z_to_bv 64 0)] ++ [CB 4 (skipn 4 (le8 (Z_to_bv 64 0)))] ++
                               [C8 scr; C4 (Z_to_bv 64 0)] ++ [CB 4 (skipn 4 (le8 (Z_to_bv 64 0)))])) in H;
    [| cbn [cells_wf cell_wf app]; repeat (split || reflexivity) | reflexivity].
  apply caw_r2_rw_app in H as [H1 H]. apply caw_r2_rw_app in H as [_ H]. apply caw_r2_rw_app in H as [H2 _].
  split; [replace (S1 + 8) with (S1 + Z.of_nat (cells_size [CB 8 j0])) by (cbn; lia); exact H1|].
  match type of H2 with rw_cells _ _ ?A _ => replace (S1 + 8 + 24) with A by (cbn; lia) end. exact H2.
Qed.

(* The pieces of the record that the call to 0x14cbc (ex_ws) reads, and the part that it keeps. *)
Lemma caw_r2_rec3 : forall m q a b c,
  rw_cells rsegs m q [C8 a; C8 b; C4 c] ->
  bytes_at rsegs m q (le8 a) /\ bytes_at rsegs m (q + 8) (le8 b) /\ wr_at rsegs m q 8 /\
  rw_cells rsegs m (q + 8) [C8 b; C4 c].
Proof.
  intros m q a b c H.
  change [C8 a; C8 b; C4 c] with ([C8 a] ++ [C8 b; C4 c]) in H.
  apply caw_r2_rw_app in H as [H1 H2].
  change (q + Z.of_nat (cells_size [C8 a])) with (q + 8) in H2.
  destruct H1 as [[_ B1] W1]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1.
  pose proof H2 as [[_ B2] _]. cbn [cells_bytes cbytes] in B2. apply bytes_at_app in B2 as [B2 _].
  split; [exact B1|]. split; [exact B2|]. split; [exact W1 | exact H2].
Qed.

Lemma caw_r2_rw8 : forall m q a, bytes_at rsegs m q (le8 a) -> wr_at rsegs m q 8 -> rw_cells rsegs m q [C8 a].
Proof.
  intros m q a B W. split; [split|].
  - split; exact I.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - exact W.
Qed.

Lemma caw_r2_skipn_map : forall (f : byte -> Z) n l, map f (skipn n l) = skipn n (map f l).
Proof. induction n as [|n IH]; intros [|a l]; cbn; auto. Qed.

Lemma caw_r2_rest : forall (l : list Z) k rest, rest = skipn k l ->
  skipn (Z.to_nat (Z.of_nat (length l) - Z.of_nat (length rest))) l = rest.
Proof.
  intros l k rest ->. rewrite length_skipn.
  destruct (Nat.le_gt_cases k (length l)) as [H|H].
  - replace (Z.to_nat (Z.of_nat (length l) - Z.of_nat (length l - k))) with k by lia. reflexivity.
  - rewrite (skipn_all2 l (n := k)) by lia. apply skipn_all2. lia.
Qed.

Lemma caw_r2_pe : forall e rest, Z.of_nat (length rest) <= e < 2 ^ 64 ->
  v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (e - Z.of_nat (length (skip rest)))))
                              (bv_unsigned (Z_to_bv 64 e)))) 1 = Z_to_bv 64 (if caw_pe rest then 1 else 0).
Proof.
  intros e rest He. pose proof (suf_len _ _ (suf_skip rest)) as HL. unfold caw_pe.
  rewrite (unsigned_lit e) by lia. rewrite (unsigned_lit (e - _)) by lia.
  pose proof (Z_lxor_range (e - Z.of_nat (length (skip rest))) e ltac:(lia) ltac:(lia)) as XR.
  rewrite v_sltiu_b2z, unsigned_lit by exact XR. change (bv_wrap 64 1) with 1.
  destruct (skip rest) as [|c r] eqn:Es.
  - cbn [length Z.of_nat]. rewrite Z.sub_0_r, Z.lxor_nilpotent. reflexivity.
  - assert (NZ : Z.lxor (e - Z.of_nat (length (c :: r))) e <> 0).
    { intro H. apply (proj1 (Z.lxor_eq_0_iff _ _)) in H. cbn [length] in H. rewrite Nat2Z.inj_succ in H.
      pose proof (Nat2Z.is_nonneg (length r)) as HR. lia. }
    replace (Z.lxor (e - Z.of_nat (length (c :: r))) e <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
Qed.

(* 0x13b1c..0x13b44 / 0x13b7c: malloc's NULL test (not taken), a1 = rc == 0 ? doc : NULL, the stores of struct ex's
   scratch and differs, jal ex_value (ret 0x13b3c); refused: jal free (ret 0x13b48); accepted: jal ex_ws (ret 0x13b68),
   s1 = (p == end), jal free (ret 0x13b80) *)
Theorem caw_run2 : ex_value_contract -> ex_ws_contract -> caw_run2_prop.
Proof.
  intros EXV EXW. unfold caw_run2_prop, CAW_AFTER_MALLOC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S1 data rcv doc bb lo x j0 j1 j2 lblk t D canary ev
    Esp Es0 Es1 Ea0 Etp Hrcv Hdoc RC S16 S62 ST LO GT BX D0 DL XL SB B4 BI BW VN VO A1 A2 A3 A4 A5 GG GD ER MI TM FC.
  subst sp s0 s1 a0.
  assert (KV : ex_value_K 0 = 13680) by reflexivity.
  assert (CG1 : STRTOD_GOT_GUARD = 0x23f98) by reflexivity.
  assert (CG2 : STRTOD_GUARD = 0x555b8) by reflexivity.
  assert (CG3 : STRTOD_ERRNO = 0x352a4) by reflexivity.
  assert (CG4 : STRTOD_GLOBALS_TOP = 0x56000) by reflexivity.
  assert (CG5 : STRTOD_IMG_LO = 0x10000) by reflexivity.
  pose proof (rw_cells_bound rsegs m S1 _ RC) as RCB. cbn [cells_size csize Nat.add] in RCB.
  pose proof (Nat2Z.is_nonneg (length x)) as XN.
  pose proof SB as (SB1 & SB2 & _).
  assert (STR : stk rsegs m (S1 + 8) (S1 + 48)).
  { pose proof (stk_of_rw_cells rsegs m S1 _ RC) as H. cbn [cells_size csize Nat.add] in H.
    apply (stk_split rsegs m S1 (S1 + 8) (S1 + 48)) in H as [_ H]; [|lia].
    apply (stk_split rsegs m (S1 + 8) (S1 + 48) (S1 + 48)) in H as [H _]; [exact H|lia]. }
  assert (TMK : forall m', munch [(S1 + 8, S1 + 48)] m m' -> MemNorm.task_mem rsegs m')
    by (intros m' MU'; exact (caw_r2_task m m' _ _ TM MU' STR)).
  assert (PJK : forall m', munch [(S1 + 8, S1 + 48)] m m' ->
            caw_v rcv doc = 0 \/
            pj_node rsegs m' (fun a k => In (a, k) D) (caw_v rcv doc) t D /\
            Forall (fun ak => 0 < fst ak /\ fst ak mod 8 = 0) D).
  { intros m' MU'. destruct VN as [VN | [VN VF]]; [left; exact VN|].
    destruct (Z.eq_dec (caw_v rcv doc) 0) as [V0 | V0]; [left; exact V0|]. right. split; [|exact VF].
    apply (pj_node_munch rsegs [(S1 + 8, S1 + 48)] m lblk m' (fun a k => In (a, k) D) _ t D VN);
      [intros a k Hak; exact Hak | exact MU' |].
    intros z Hz. destruct (VO V0) as (O1 & _). replace (S1 + 48) with (S1 + 8 + 40) by lia.
    exact (caw_r2_foot _ _ _ _ z O1 Hz). }
  assert (BXK : forall W m', munch W m m' ->
            (Z.of_nat (length x) <= 0 \/ disjoint_from W data (Z.of_nat (length x))) -> bytes_at rsegs m' data x)
    by (intros W m' MU' HD; exact (caw_r2_bytes W m m' data x BX MU' HD)).
  clear STR.
  pose proof (munch_refl [(S1 + 8, S1 + 48)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_cases HB; [zify_cond HB; lia | clear HB].
  do 7 step.
  rewrite (caw_r2_v rcv doc Hrcv Hdoc).
  destruct (caw_r2_rec m1 S1 j0 _ _ _ RC) as [R1 R2].
  clear RC.
  assert (USP : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; lia).
  pose proof (TMK m1 MU) as TM1. pose proof (PJK m1 MU) as VN1.
  assert (BX1 : bytes_at rsegs m1 data x)
    by (apply (BXK _ m1 MU); clear - A1 XN; unfold ex_apart in A1; cbn [disjoint_from]; lia).
  eapply evt_cut.
  { apply (EXV (Z_to_bv 64 80700) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 rcv) (Z_to_bv 64 doc)
              (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (caw_v rcv doc)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m1 (S1 + 8) (caw_v rcv doc) data 0 0 0 bb lo x (fun a k => In (a, k) D) t D
              canary ev); rewrite ?USP;
      [ first [reflexivity | f_equal; lia] | reflexivity | exact Etp
      | unfold ex_rec; rewrite Z.add_0_r; split; [exact R1 | exact R2]
      | clear - S16; Z.div_mod_to_equations; lia | lia
      | exact BX1 | exact D0 | exact DL | exact XL | lia | lia | left; reflexivity
      | exact SB | exact B4 | exact BI | exact BW | exact VN1
      | exact ST | exact LO | exact S16 | exact S62 | exact GT
      | exact A1 | exact A2 | exact A3 | unfold ex_apart; lia | exact A4 | exact A5 | exact VO
      | exact GG | exact GD | exact ER | exact MI | exact TM1 | exact FC ]. }
  intros ms' POST.
  destruct POST as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                    F' & fc' & m' & p' & d' & dl' & ev' & E & FK & FC' & MU' & WM' & MI' & TM' & ST' & ER' & REC' &
                    DL' & CASE).
  subst ms'. rewrite USP in MU', ST'.
  replace (ret_pc (Z_to_bv 64 80700)) with (Z_to_bv 64 80700) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  destruct REC' as [R1' R2']. replace (S1 + 8 + 24) with (S1 + 32) in R2' by lia.
  assert (MUT : munch [(S1 - ex_value_K 0, S1); (S1 + 8, S1 + 48); (bb, bb + Z.of_nat (length x) + 1);
                       (STRTOD_ERRNO, STRTOD_ERRNO + 4)] m m').
  { apply (munch_trans _ m m1 m').
    - eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    - eapply munch_weaken; [|exact MU']. unfold sub_fp; cbn [outside]; intros; lia. }
  assert (WMT : wmono rsegs m m') by (eapply wmono_trans; [exact WM | exact WM']).
  change (skipn (Z.to_nat 0) x) with x in CASE.
  destruct (ex_V 0 (map bv_unsigned x)) as [[u rest]|] eqn:EV.
  - destruct CASE as (Er & Ep & Ed & SB' & Hdl). subst r d'.
    destruct (ex_V_rest _ _ _ _ EV) as [RL [k Ek]]. rewrite length_map in RL.
    assert (P0 : 0 <= p' <= Z.of_nat (length x)) by lia.
    assert (MAPJ : map bv_unsigned (skipn (Z.to_nat p') x) = rest).
    { rewrite caw_r2_skipn_map, Ep. rewrite <- (length_map bv_unsigned x). exact (caw_r2_rest _ k rest Ek). }
    assert (BXM : bytes_at rsegs m' data x).
    { apply (BXK _ m' MUT). clear - A1 A3 A4 A5 XN KV. unfold ex_apart in *. cbn [disjoint_from]. lia. }
    destruct (caw_r2_rec3 m' (S1 + 8) _ _ _ R1') as (B0 & B8 & W0 & R8).
    replace (S1 + 8 + 8) with (S1 + 16) in B8, R8 by lia.
    step. if_cases HB; [clear HB | exfalso; vm_compute in HB; discriminate HB].
    do 2 step.
    eapply evt_cut.
    { apply (EXW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (S1 + 8) data p' x);
        [ first [reflexivity | f_equal; lia] | clear - S16; Z.div_mod_to_equations; lia
        | exact B0 | replace (S1 + 8 + 8) with (S1 + 16) by lia; exact B8 | exact W0 | exact BXM | exact D0
        | exact DL | exact P0
        | destruct (Nat.eq_dec (length x) 0) as [L0|L0]; [left; exact L0 | right; unfold ex_apart in A1; lia]
        | exact MI' ]. }
    intros ms' POST.
    destruct POST as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' &
                      t6'' & m'' & E2 & MUw & WMw & MIw & BW1).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 80744)) with (Z_to_bv 64 80744) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    remember (ex_ws_p1 data p' x) as v eqn:Ev.
    pose proof (caw_r2_rw8 m'' (S1 + 8) _ BW1 (wr_at_transport rsegs m' m'' (S1 + 8) 8 W0 WMw)) as R0.
    apply (rw_cells_transport rsegs [(S1 + 8, S1 + 8 + 8)] m' m'' _ _) in R8;
      [| exact MUw | exact WMw | cbn [disjoint_from]; lia].
    apply (rw_cells_transport rsegs [(S1 + 8, S1 + 8 + 8)] m' m'' _ _) in R2';
      [| exact MUw | exact WMw | cbn [disjoint_from]; lia].
    clear B0 B8 W0 R1' BW1.
    do 6 step.
    apply evt_done. unfold caw_mid2.
    do 16 eexists. exists F', fc', m'', dl'. split; [reflexivity|].
    split; [exact FK|]. split; [exact FC'|].
    split.
    { apply (munch_trans _ m m' m''); [exact MUT|].
      eapply munch_weaken; [|exact MUw]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WMT | exact WMw]|].
    split; [exact R2'|]. split; [exact DL'|]. rewrite EV.
    split; [reflexivity|]. split.
    + subst v. unfold ex_ws_p1. rewrite MAPJ. apply caw_r2_pe. lia.
    + clear - Hdl. split; intro H.
      * apply Hdl in H. destruct H as [H|H]; [lia | exact H].
      * apply Hdl. right. exact H.
  - destruct CASE as (Er & _ & _). subst r.
    step. if_cases HB; [exfalso; vm_compute in HB; discriminate HB | clear HB].
    step. step.
    apply evt_done. unfold caw_mid2.
    do 16 eexists. exists F', fc', m', dl'. split; [reflexivity|].
    split; [exact FK|]. split; [exact FC'|]. split; [exact MUT|]. split; [exact WMT|].
    split; [exact R2'|]. split; [exact DL'|]. rewrite EV. reflexivity.
Qed.
