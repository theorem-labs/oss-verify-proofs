From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Cells Exec Frame FP Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct strtod_c ex_value_c ex_value_m check_as_written_s.
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

Lemma caw_r2_le84 : forall v : word, le8 v = le4 v ++ skipn 4 (le8 v).
Proof. intros v. reflexivity. Qed.

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

Lemma caw_r2_ws_big : forall z, 32 < z -> ws z = false.
Proof.
  intros z H. unfold ws.
  destruct (Z.eqb_spec z 32), (Z.eqb_spec z 9), (Z.eqb_spec z 10), (Z.eqb_spec z 13); try lia; reflexivity.
Qed.

Lemma caw_r2_ws : forall z, 0 <= z <= 32 ->
  bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294977024 (bv_unsigned (Z_to_bv 64 z) mod 64)))) 1))
         (Z_to_bv 64 0) = negb (ws z).
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia.
  replace z with (Z.of_nat (Z.to_nat z)) by lia.
  assert (Hn : (Z.to_nat z <= 32)%nat) by lia. generalize (Z.to_nat z) Hn. clear. intros n Hn.
  do 33 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma caw_r2_skip_len : forall z y, ws z = false ->
  Z.of_nat (length (skip (z :: y))) = 1 + Z.of_nat (length y).
Proof. intros z y H. rewrite skip_nws by exact H. cbn [length]. lia. Qed.

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

Section Loop.
  Variables (m : word -> option byte) (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (e : Z).
  Hypothesis HE : e < 2 ^ 63.
  Lemma caw_r2_loop : forall ys a a4, bytes_at rsegs m a ys -> ys <> [] -> e = a + Z.of_nat (length ys) ->
    (forall a4' v, v = e - Z.of_nat (length (skip (map bv_unsigned ys))) ->
       evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 32) (Z_to_bv 64 e) (Z_to_bv 64 v)
                          (Z_to_bv 64 4294977024) a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 80720) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 32) (Z_to_bv 64 e) (Z_to_bv 64 a)
                       (Z_to_bv 64 4294977024) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 80688) fc None m (seg_rom rsegs)).
  Proof using HE.
    induction ys as [|b ys IH]; intros a a4 BY NE Ee K; [congruence|].
    remember (bv_unsigned b) as z eqn:Ez.
    assert (RZ : 0 <= z < 2 ^ 64) by (subst z; pose proof (zr_bv 8 b ltac:(vm_compute; congruence)) as H; exact H).
    assert (MB : map bv_unsigned (b :: ys) = z :: map bv_unsigned ys) by (cbn [map]; rewrite Ez; reflexivity).
    rewrite MB in K. clear MB.
    pose proof (bytes_at_bound _ _ _ _ BY) as BB. cbn [length] in BB, Ee.
    assert (RD : ov_read_bytes rsegs m (wa a) 1 = Some [b]).
    { pose proof (bytes_at_read rsegs m a (b :: ys) 0 1 BY ltac:(lia) ltac:(cbn; lia)) as R.
      rewrite Z.add_0_r in R. exact R. }
    change (b :: ys) with ([b] ++ ys) in BY. apply bytes_at_app in BY as [_ BY'].
    change (Z.of_nat (length [b])) with 1 in BY'.
    step. unfold zxb. rewrite <- Ez.
    step. if_cases HB.
    - zify_cond HB. pose proof (caw_r2_ws_big z HB) as WS.
      eapply K. rewrite (caw_r2_skip_len z _ WS), length_map. lia.
    - zify_cond HB.
      step. step. step. if_cases HB2; rewrite (caw_r2_ws z) in HB2 by lia.
      + apply negb_true_iff in HB2.
        eapply K. rewrite (caw_r2_skip_len z _ HB2), length_map. lia.
      + apply negb_false_iff in HB2.
        assert (SK : skip (z :: map bv_unsigned ys) = skip (map bv_unsigned ys)) by (apply skip_ws; exact HB2).
        rewrite SK in K. clear SK.
        step. step. if_cases HB3; zify_cond HB3.
        * eapply IH; [exact BY' | | lia | intros a4' v Ev; eapply K; exact Ev].
          intro E0. subst ys. cbn [length Z.of_nat] in Ee. Z.div_mod_to_equations. lia.
        * assert (E0 : ys = []) by (destruct ys as [|y0 ys]; [reflexivity | cbn [length] in Ee; Z.div_mod_to_equations; lia]).
          subst ys. step. eapply K. cbn [map skip length]. lia.
  Qed.
End Loop.

Theorem caw_run2 : ex_value_contract -> caw_run2_prop.
Proof.
  intros EXV. unfold caw_run2_prop, CAW_AFTER_MALLOC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S1 data rcv doc bb lo x j0 j1 j2 lblk t D canary ev
    Esp Es0 Es1 Ea0 Etp Hrcv Hdoc RC S16 S62 ST LO GT BX D0 DL XL SB B4 BI BW VN VO A1 A2 A3 A4 A5 GG GD ER MI TM FC.
  subst sp s0 s1 a0.
  assert (KV : ex_value_K 0 = 13152) by reflexivity.
  assert (CG1 : STRTOD_GOT_GUARD = 0x234e0) by reflexivity.
  assert (CG2 : STRTOD_GUARD = 0x54b08) by reflexivity.
  assert (CG3 : STRTOD_ERRNO = 0x347f4) by reflexivity.
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
            pj_node rsegs m' (fun a k => In (a, k) D) (caw_v rcv doc) t D /\ Forall (fun ak => 0 < fst ak) D).
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
  { apply (EXV (Z_to_bv 64 80624) (Z_to_bv 64 S1) gp tp t0 t1 t2 (Z_to_bv 64 rcv) (Z_to_bv 64 doc)
              (Z_to_bv 64 (S1 + 8)) (Z_to_bv 64 (caw_v rcv doc)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m1 (S1 + 8) (caw_v rcv doc) data 0 0 0 bb lo x (fun a k => In (a, k) D) t D
              canary ev); rewrite ?USP;
      [ reflexivity | reflexivity | exact Etp
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
  replace (ret_pc (Z_to_bv 64 80624)) with (Z_to_bv 64 80624) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
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
    assert (TAIL : forall w0 w3 w4 v, v = data + Z.of_nat (length x) - Z.of_nat (length (skip rest)) ->
      evt rsegs (caw_mid2 gp tp (Z_to_bv 64 rcv) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m S1 rcv doc bb x t)
        (MS (mkR (Z_to_bv 64 80624) (Z_to_bv 64 S1) gp tp t0' t1' t2' (Z_to_bv 64 rcv) (Z_to_bv 64 doc) w0
                 (Z_to_bv 64 (data + Z.of_nat (length x))) (Z_to_bv 64 v) w3 w4 a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F' (Z_to_bv 64 80720) fc' None m' (seg_rom rsegs))).
    { intros w0 w3 w4 v Ev. do 4 step.
      apply evt_done. unfold caw_mid2.
      do 16 eexists. exists F', fc', m', dl'. split; [reflexivity|].
      split; [exact FK|]. split; [exact FC'|]. split; [exact MUT|]. split; [exact WMT|].
      split; [exact R2'|]. split; [exact DL'|]. rewrite EV.
      split; [reflexivity|]. split.
      - subst v. apply caw_r2_pe. lia.
      - clear - Hdl. split; intro H.
        + apply Hdl in H. destruct H as [H|H]; [lia | exact H].
        + apply Hdl. right. exact H. }
    step. if_cases HB; [clear HB | exfalso; vm_compute in HB; discriminate HB].
    step. step.
    step. if_cases HB; zify_cond HB.
    + assert (R0 : rest = []) by (destruct rest as [|c r]; [reflexivity | cbn [length] in Ep; lia]).
      eapply TAIL. rewrite R0 in Ep |- *. cbn [skip length Z.of_nat] in Ep |- *. lia.
    + do 4 step.
      assert (P0 : 0 <= p' <= Z.of_nat (length x)) by lia.
      assert (MAPJ : map bv_unsigned (skipn (Z.to_nat p') x) = rest).
      { rewrite caw_r2_skipn_map, Ep. rewrite <- (length_map bv_unsigned x). exact (caw_r2_rest _ k rest Ek). }
      assert (BYJ : bytes_at rsegs m' (data + p') (skipn (Z.to_nat p') x)).
      { assert (BXM : bytes_at rsegs m' data x).
        { apply (BXK _ m' MUT). clear - A1 A3 A4 A5 XN KV. unfold ex_apart in *. cbn [disjoint_from]. lia. }
        rewrite <- (firstn_skipn (Z.to_nat p') x) in BXM. apply bytes_at_app in BXM as [_ BXM].
        rewrite length_firstn in BXM.
        replace (data + p') with (data + Z.of_nat (Nat.min (Z.to_nat p') (length x))) by lia. exact BXM. }
      eapply (caw_r2_loop m') with (ys := skipn (Z.to_nat p') x) (a := data + p').
      * lia.
      * exact BYJ.
      * intro E0. apply (f_equal (@length byte)) in E0. rewrite length_skipn in E0. cbn [length] in E0. lia.
      * rewrite length_skipn. lia.
      * intros a4'' v Ev. rewrite MAPJ in Ev. eapply TAIL. exact Ev.
  - destruct CASE as (Er & _ & _). subst r.
    step. if_cases HB; [exfalso; vm_compute in HB; discriminate HB | clear HB].
    step. step.
    apply evt_done. unfold caw_mid2.
    do 16 eexists. exists F', fc', m', dl'. split; [reflexivity|].
    split; [exact FK|]. split; [exact FC'|]. split; [exact MUT|]. split; [exact WMT|].
    split; [exact R2'|]. split; [exact DL'|]. rewrite EV. reflexivity.
Qed.
