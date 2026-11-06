From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel SlotNeeds_c LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SegCLib SweepRowCheck.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import reac_headamp_default_c reac_ctrl_identity_poll_block_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Spec Require Import StrFun.
Import ListNotations.
Open Scope Z_scope.

Section Sweep.
Variables (S s t base w rows : Z) (T ws st : list byte) (m0 : word -> option byte).
Hypothesis HS16 : S mod 16 = 0.
Hypothesis HLO : 0 <= S - 8784.
Hypothesis HS63 : S < 2 ^ 63.
Hypothesis Hw : 1 <= w <= 40.
Hypothesis Hb : 0 <= base /\ base + w <= 48.
Hypothesis Hrows : 8 + 3 * w <= rows < 256.
Hypothesis Hs : 0 < s /\ s + 34 * rows < 2 ^ 63 /\ (s + 34 * rows <= S - 8784 \/ S <= s).
Hypothesis Ht : 0 < t /\ t + 460 < 2 ^ 63 /\ (t + 460 <= S - 8784 \/ S <= t) /\ (s + 34 * rows <= t \/ t + 460 <= s).
Hypothesis HTl : length T = 460%nat.
Hypothesis HI1 : I1 T.
Hypothesis Hwsl : length ws = 144%nat.
Hypothesis Hstl : length st = 144%nat.
Hypothesis HH : Hrel T ws st.

Definition vals : list byte := sweep_vals T t base (Z.to_nat w).
Definition SW : list byte := SWEEP base (Z.to_nat w) vals.
Definition Wf : list (Z * Z) :=
  [(S - 8784, S - 592); (S - 592 + 50, S - 592 + 84); (S - 592 + 194, S - 592 + 198); (s, s + 34 * rows)].

Definition minv (m : word -> option byte) : Prop :=
  munch Wf m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ stk rsegs m (S - 8784) (S - 592) /\
  stk rsegs m (S - 592 + 50) (S - 592 + 84) /\ stk rsegs m (S - 592 + 194) (S - 592 + 198) /\
  bytes_at rsegs m t T /\ bytes_at rsegs m (S - 592 + 344) ws /\ bytes_at rsegs m (S - 592 + 200) st /\
  bytes_at rsegs m (S - 592 + 198) [Z_to_bv 8 base; Z_to_bv 8 w] /\ bytes_at rsegs m s SW.

Lemma length_concat34 : forall (L : list (list byte)), Forall (fun r => length r = 34%nat) L -> length (concat L) = (34 * length L)%nat.
Proof.
  induction L as [|r L IH]; intros HL; [reflexivity|]. inversion HL; subst. cbn [concat length].
  rewrite length_app, IH by assumption. lia.
Qed.

Lemma length_SW : Z.of_nat (length SW) = 34 * (8 + 3 * w).
Proof.
  unfold SW. rewrite SWEEP_rows, length_concat34 by (apply Forall_rowok_len, sweep_rows_ok).
  rewrite Nat2Z.inj_mul, length_sweep_rows by lia. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma sw_row : forall m k, 0 <= k < 8 + 3 * w -> bytes_at rsegs m s SW ->
  bytes_at rsegs m (s + 34 * k) (nth (Z.to_nat k) (sweep_rows base (Z.to_nat w) vals) []).
Proof.
  intros m k Hk HB. unfold SW in HB. rewrite SWEEP_rows in HB.
  eapply bytes_at_eqa; [apply concat_row; [apply Forall_rowok_len, sweep_rows_ok | | exact HB] | lia].
  pose proof (length_sweep_rows base (Z.to_nat w) vals ltac:(lia)). lia.
Qed.

Lemma ga_row_eff : forall c q, 0 <= c < w -> 0 <= q < 3 ->
  ga_row base vals (Z.to_nat c) (Z.to_nat q) = GA (base + c) q (eff T t (base + c) q).
Proof.
  intros c q Hc Hq. unfold ga_row, vals. rewrite vz_sweep_vals by lia. rewrite !Z2Nat.id by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma row_A0 : forall m q, 0 <= q < 3 -> bytes_at rsegs m s SW ->
  bytes_at rsegs m (s + 34 + 34 * q) (GA base q (eff T t base q)).
Proof.
  intros m q Hq HB. pose proof (sw_row m (1 + q) ltac:(lia) HB) as R.
  replace (Z.to_nat (1 + q)) with (1 + Z.to_nat q)%nat in R by lia. rewrite nth_row_A0 in R by lia.
  replace (ga_row base vals 0 (Z.to_nat q)) with (ga_row base vals (Z.to_nat 0) (Z.to_nat q)) in R by reflexivity.
  rewrite ga_row_eff in R by lia. rewrite Z.add_0_r in R. eapply bytes_at_eqa; [exact R | lia].
Qed.

Lemma row_A : forall m c q, 1 <= c < w -> 0 <= q < 3 -> bytes_at rsegs m s SW ->
  bytes_at rsegs m (s + 374 + 102 * (c - 1) + 34 * q) (GA (base + c) q (eff T t (base + c) q)).
Proof.
  intros m c q Hc Hq HB. pose proof (sw_row m (11 + 3 * (c - 1) + q) ltac:(lia) HB) as R.
  replace (Z.to_nat (11 + 3 * (c - 1) + q)) with (11 + 3 * (Z.to_nat c - 1) + Z.to_nat q)%nat in R by lia.
  rewrite nth_row_A in R by lia. rewrite ga_row_eff in R by lia. eapply bytes_at_eqa; [exact R | lia].
Qed.

Lemma row_B : forall m i, 0 <= i < 6 -> bytes_at rsegs m s SW ->
  bytes_at rsegs m (s + 170 + 34 * i) (GB i).
Proof.
  intros m i Hi HB. pose proof (sw_row m (5 + i) ltac:(lia) HB) as R.
  replace (Z.to_nat (5 + i)) with (5 + Z.to_nat i)%nat in R by lia. rewrite nth_row_B in R by lia.
  rewrite Z2Nat.id in R by lia. eapply bytes_at_eqa; [exact R | lia].
Qed.

Lemma row_0 : forall m, bytes_at rsegs m s SW -> bytes_at rsegs m s HEAD_ACK34.
Proof.
  intros m HB. pose proof (sw_row m 0 ltac:(lia) HB) as R. eapply bytes_at_eqa; [exact R | lia].
Qed.

Lemma row_4 : forall m, bytes_at rsegs m s SW -> bytes_at rsegs m (s + 136) HEAD_MARK34.
Proof.
  intros m HB. pose proof (sw_row m 4 ltac:(lia) HB) as R. eapply bytes_at_eqa; [exact R | lia].
Qed.

Ltac dj := cbn [disjoint_from]; rewrite ?length_SW; simpl_sizes; rewrite ?HTl, ?Hwsl, ?Hstl; cbn [length]; repeat split; try exact I; lia.

Lemma minv_callee : forall m m', minv m -> munch [(S - 8784, S - 592)] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' (S - 8784) (S - 592) -> minv m'.
Proof.
  intros m m' (MU & WM & _ & _ & S50 & S194 & BT & BW & BS & BA & BSW) MU' WM' MI' ST'.
  pose proof length_SW as LSW.
  unfold minv. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp, Wf. cbn [outside]. intros; tauto.
  - eapply wmono_trans; eassumption.
  - exact MI'.
  - exact ST'.
  - eapply stk_transport_disjoint; [exact S50 | exact MU' | exact WM' | cbn [disjoint_from]; split; [lia | exact I]].
  - eapply stk_transport_disjoint; [exact S194 | exact MU' | exact WM' | cbn [disjoint_from]; split; [lia | exact I]].
  - eapply bytes_at_transport; [exact BT | exact MU' | dj].
  - eapply bytes_at_transport; [exact BW | exact MU' | dj].
  - eapply bytes_at_transport; [exact BS | exact MU' | dj].
  - eapply bytes_at_transport; [exact BA | exact MU' | dj].
  - eapply bytes_at_transport; [exact BSW | exact MU' | dj].
Qed.

Lemma minv_poll : forall m m', minv m -> munch [(S - 592 - 16, S - 592); (S - 592 + 50, S - 592 + 84)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 8784) (S - 592) ->
  stk rsegs m' (S - 592 + 50) (S - 592 + 84) -> minv m'.
Proof.
  intros m m' (MU & WM & _ & _ & S50 & S194 & BT & BW & BS & BA & BSW) MU' WM' MI' ST' S50'.
  pose proof length_SW as LSW.
  unfold minv. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. unfold sub_fp, Wf. cbn [outside]. intros; repeat split; lia.
  - eapply wmono_trans; eassumption.
  - exact MI'.
  - exact ST'.
  - exact S50'.
  - eapply stk_transport_disjoint; [exact S194 | exact MU' | exact WM' | cbn [disjoint_from]; repeat split; lia].
  - eapply bytes_at_transport; [exact BT | exact MU' | dj].
  - eapply bytes_at_transport; [exact BW | exact MU' | dj].
  - eapply bytes_at_transport; [exact BS | exact MU' | dj].
  - eapply bytes_at_transport; [exact BA | exact MU' | dj].
  - eapply bytes_at_transport; [exact BSW | exact MU' | dj].
Qed.

Lemma minv_same : forall m m', minv m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> minv m'.
Proof.
  intros m m' MV MU' WM' MI'. pose proof MV as (_ & _ & _ & ST & _).
  eapply minv_callee; [exact MV | eapply munch_weaken; [|exact MU']; unfold sub_fp; cbn; tauto | exact WM' | exact MI' |].
  eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I].
Qed.

Lemma minv_store : forall m a bs, minv m -> S - 592 + 194 <= a -> a + 1 <= S - 592 + 198 -> length bs = 1%nat ->
  minv (write_to_mem m (wa a) bs).
Proof.
  intros m a bs (MU & WM & MI & ST & S50 & S194 & BT & BW & BS & BA & BSW) Ha1 Ha2 Hl.
  pose proof length_SW as LSW.
  destruct (stk_cells m _ _ a 1 S194 ltac:(lia) ltac:(lia)) as [junk RC].
  pose proof (rw_cells_store_ok rsegs m a [CB 1 junk] 0 (CB 1 junk) 1 RC eq_refl eq_refl) as SO.
  rewrite Z.add_0_r in SO.
  unfold minv. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  - apply munch_write; [exact MU | lia | rewrite Hl; lia | unfold Wf; cbn [inside]; rewrite Hl; lia].
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | rewrite Hl; exact SO].
  - apply stk_write; [exact ST | lia | rewrite Hl; lia].
  - apply stk_write; [exact S50 | lia | rewrite Hl; lia].
  - apply stk_write; [exact S194 | lia | rewrite Hl; lia].
  - apply bytes_at_write_other; [exact BT | lia | rewrite Hl; lia | rewrite Hl, HTl; lia].
  - apply bytes_at_write_other; [exact BW | lia | rewrite Hl; lia | rewrite Hl, Hwsl; lia].
  - apply bytes_at_write_other; [exact BS | lia | rewrite Hl; lia | rewrite Hl, Hstl; lia].
  - apply bytes_at_write_other; [exact BA | lia | rewrite Hl; lia | rewrite Hl; cbn [length]; lia].
  - apply bytes_at_write_other; [exact BSW | lia | rewrite Hl; lia | rewrite Hl, LSW; lia].
Qed.

Lemma minv_store_ok : forall m a, minv m -> S - 592 + 194 <= a -> a + 1 <= S - 592 + 198 ->
  store_ok rsegs m (wa a) 1 = true.
Proof.
  intros m a (_ & _ & _ & _ & _ & S194 & _) Ha1 Ha2.
  destruct (stk_cells m _ _ a 1 S194 ltac:(lia) ltac:(lia)) as [junk RC].
  pose proof (rw_cells_store_ok rsegs m a [CB 1 junk] 0 (CB 1 junk) 1 RC eq_refl eq_refl) as SO.
  rewrite Z.add_0_r in SO. exact SO.
Qed.

Lemma bytes_at_sub : forall m A bs k n, bytes_at rsegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n H Hl. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma ro_poll3 : forall i, 0 <= i < 6 -> ro_bytes rsegs (0x103f0 + 3 * i) (firstn 3 (skipn 20 (GB i))).
Proof.
  intros i Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as H by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]]; apply ro_bytes_b_sound; vm_compute; reflexivity.
Qed.

Lemma length_poll3 : forall i, length (firstn 3 (skipn 20 (GB i))) = 3%nat.
Proof. intros i. rewrite length_firstn, length_skipn, length_GB. reflexivity. Qed.

Lemma land255 : forall c, 0 <= c < 256 -> Z.land c 255 = c.
Proof. intros c Hc. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Hypothesis GAN : check_groupa_need.
Hypothesis DFL : reac_headamp_default_contract.
Hypothesis POLL : reac_ctrl_identity_poll_block_contract.
Hypothesis BCMP : bcmp_contract.

Lemma loopA0 : forall n q (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  n = Z.to_nat (3 - q) -> 0 <= q < 3 ->
  sp = Z_to_bv 64 (S - 592) -> s0 = Z_to_bv 64 t -> s1 = Z_to_bv 64 (S - 592 + 344) -> s2 = Z_to_bv 64 q ->
  s3 = Z_to_bv 64 s -> s4 = Z_to_bv 64 (s + 34 + 34 * q) -> s6 = Z_to_bv 64 3 -> s7 = Z_to_bv 64 (S - 592 + 200) ->
  minv m ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3 s4' s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13510) fc None m' (seg_rom rsegs) /\ minv m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134bc) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Hn Hq -> -> -> -> -> -> -> -> MV; [lia|].
  pose proof MV as (MU & WM & MI & ST & S50 & S194 & BT & BW & BS & BA & BSW).
  pose proof (bytes_byte_read m _ _ 0 BA ltac:(cbn; lia)) as RB. cbn [nth Z.of_nat] in RB. rewrite Z.add_0_r in RB.
  set (j := 3 * base + q).
  pose proof (bytes_byte_read m _ _ (Z.to_nat j) BW ltac:(lia)) as RW. rewrite Z2Nat.id in RW by lia.
  pose proof (bytes_byte_read m _ _ (Z.to_nat j) BS ltac:(lia)) as RS. rewrite Z2Nat.id in RS by lia.
  pose proof (byte_range (nth (Z.to_nat j) ws (Z_to_bv 8 0))) as BRW.
  pose proof (byte_range (nth (Z.to_nat j) st (Z_to_bv 8 0))) as BRS.
  assert (Hb256 : 0 <= base < 256) by lia.
  assert (Heff : eff T t base q = if bv_unsigned (nth (Z.to_nat j) ws (Z_to_bv 8 0)) =? 0 then dflt q
                                  else bv_unsigned (nth (Z.to_nat j) st (Z_to_bv 8 0))).
  { rewrite eff_cell by lia. destruct (HH base q ltac:(lia) ltac:(lia)) as [H1 H2].
    rewrite <- H1, <- H2. reflexivity. }
  zstep. cbv beta. rewrite (bv8_small base Hb256).
  zstep. rewrite ?Z.shiftl_mul_pow2 by lia. zstep. zstep. zstep. zstep. cbv beta.
  eapply evt_cut with (P := fun ms => exists r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14,
    ms = MS (mkR r0 (Z_to_bv 64 (S - 592)) gp tp r1 r2 r3 (Z_to_bv 64 t) (Z_to_bv 64 (S - 592 + 344)) r4 r5 r6 r7
                 (Z_to_bv 64 (eff T t base q)) r8 r9 r10 (Z_to_bv 64 q) (Z_to_bv 64 s) (Z_to_bv 64 (s + 34 + 34 * q))
                 (Z_to_bv 64 base) (Z_to_bv 64 3) (Z_to_bv 64 (S - 592 + 200)) s8 s9 s10 s11 r11 r12 r13 r14)
            F (Z_to_bv 64 0x134f0) fc None m (seg_rom rsegs)).
  2: { intros ms1 (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & ->).
       zstep. rewrite ?land255 by lia. zstep. zstep. zstep. zstep.
       eapply evt_cut.
       { eapply GAN with (row := s + 34 + 34 * q) (ch := base) (p := q) (t := t) (lo := S - 8784) (T := T).
         all: try reflexivity.
         all: try lia.
         all: try assumption.
         - apply row_A0; [lia | exact BSW].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)]. }
       intros ms2 (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & MU2 & WM2 & MI2 & ST2).
       retpc. rewrite unsigned_lit in MU2, ST2 by lia.
       pose proof (minv_callee m m2 MV MU2 WM2 MI2 ST2) as MV2.
       zstep. zstep. zstep.
       destruct (Z.eq_dec q 2) as [-> | Hq2].
       - ifc. apply evt_done. do 20 eexists. split; [reflexivity | exact MV2].
       - ifc. eapply IH with (q := q + 1).
         all: first [ reflexivity | (f_equal; lia) | lia | exact MV2 ]. }
  destruct (Z.eq_dec (bv_unsigned (nth (Z.to_nat j) ws (Z_to_bv 8 0))) 0) as [Hz | Hz].
  - rewrite Hz, Z.eqb_refl in Heff.
    zstep. ifc. zstep. zstep.
    eapply evt_cut; [eapply DFL; [reflexivity | lia] |].
    intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & ->). retpc.
    zstep. rewrite <- Heff. apply evt_done. do 15 eexists. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ 0) Hz) in Heff.
    zstep. ifc. zstep. zstep. cbv beta. zstep. rewrite <- Heff. apply evt_done. do 15 eexists. reflexivity.
Qed.

Lemma loopAi : forall n q c (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  n = Z.to_nat (3 - q) -> 0 <= q < 3 -> 1 <= c < w ->
  sp = Z_to_bv 64 (S - 592) -> s0 = Z_to_bv 64 t -> s2 = Z_to_bv 64 q ->
  s3 = Z_to_bv 64 s -> s4 = Z_to_bv 64 (s + 374 + 102 * (c - 1) + 34 * q) -> s6 = Z_to_bv 64 c ->
  s7 = Z_to_bv 64 (S - 592 + 344) -> s8 = Z_to_bv 64 3 -> s10 = Z_to_bv 64 (S - 592 + 200) -> s11 = Z_to_bv 64 c ->
  minv m ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s1' s2' s4' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3 s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x1359c) fc None m' (seg_rom rsegs) /\ minv m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1353c) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros q c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Hn Hq Hc -> -> -> -> -> -> -> -> -> -> MV; [lia|].
  pose proof MV as (MU & WM & MI & ST & S50 & S194 & BT & BW & BS & BA & BSW).
  pose proof (bytes_byte_read m _ _ 0 BA ltac:(cbn; lia)) as RB. cbn [nth Z.of_nat] in RB. rewrite Z.add_0_r in RB.
  set (j := 3 * (base + c) + q).
  pose proof (bytes_byte_read m _ _ (Z.to_nat j) BW ltac:(lia)) as RW. rewrite Z2Nat.id in RW by lia.
  pose proof (bytes_byte_read m _ _ (Z.to_nat j) BS ltac:(lia)) as RS. rewrite Z2Nat.id in RS by lia.
  pose proof (byte_range (nth (Z.to_nat j) ws (Z_to_bv 8 0))) as BRW.
  pose proof (byte_range (nth (Z.to_nat j) st (Z_to_bv 8 0))) as BRS.
  assert (Hb256 : 0 <= base < 256) by lia.
  assert (Heff : eff T t (base + c) q = if bv_unsigned (nth (Z.to_nat j) ws (Z_to_bv 8 0)) =? 0 then dflt q
                                  else bv_unsigned (nth (Z.to_nat j) st (Z_to_bv 8 0))).
  { rewrite eff_cell by lia. destruct (HH (base + c) q ltac:(lia) ltac:(lia)) as [H1 H2].
    rewrite <- H1, <- H2. reflexivity. }
  zstep. cbv beta. rewrite (bv8_small base Hb256).
  zstep. zstep. rewrite ?land255 by lia. zstep. rewrite ?Z.shiftl_mul_pow2 by lia. zstep. zstep. zstep. zstep. cbv beta.
  eapply evt_cut with (P := fun ms => exists r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14,
    ms = MS (mkR r0 (Z_to_bv 64 (S - 592)) gp tp r1 r2 r3 (Z_to_bv 64 t) (Z_to_bv 64 base) r4 r5 r6 r7
                 (Z_to_bv 64 (eff T t (base + c) q)) r8 r9 r10 (Z_to_bv 64 q) (Z_to_bv 64 s)
                 (Z_to_bv 64 (s + 374 + 102 * (c - 1) + 34 * q)) s5 (Z_to_bv 64 c) (Z_to_bv 64 (S - 592 + 344))
                 (Z_to_bv 64 3) s9 (Z_to_bv 64 (S - 592 + 200)) (Z_to_bv 64 c) r11 r12 r13 r14)
            F (Z_to_bv 64 0x13578) fc None m (seg_rom rsegs)).
  2: { intros ms1 (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & ->).
       zstep. zstep. rewrite ?land255 by lia. zstep. rewrite ?land255 by lia. zstep. zstep. zstep.
       eapply evt_cut.
       { eapply GAN with (row := s + 374 + 102 * (c - 1) + 34 * q) (ch := base + c) (p := q) (t := t) (lo := S - 8784) (T := T).
         all: try reflexivity.
         all: try lia.
         all: try assumption.
         - apply row_A; [lia | lia | exact BSW].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)].
         - unfold CHECK_GROUPA_STACK. all: rewrite ?unsigned_lit by lia; first [exact ST | lia | (Z.div_mod_to_equations; lia)]. }
       intros ms2 (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & MU2 & WM2 & MI2 & ST2).
       retpc. rewrite unsigned_lit in MU2, ST2 by lia.
       pose proof (minv_callee m m2 MV MU2 WM2 MI2 ST2) as MV2.
       zstep. zstep. zstep.
       destruct (Z.eq_dec q 2) as [-> | Hq2].
       - ifc. apply evt_done. do 20 eexists. split; [reflexivity | exact MV2].
       - ifc. eapply IH with (q := q + 1) (c := c).
         all: first [ reflexivity | (f_equal; lia) | lia | exact MV2 ]. }
  destruct (Z.eq_dec (bv_unsigned (nth (Z.to_nat j) ws (Z_to_bv 8 0))) 0) as [Hz | Hz].
  - rewrite Hz, Z.eqb_refl in Heff.
    zstep. ifc. zstep. zstep.
    eapply evt_cut; [eapply DFL; [reflexivity | lia] |].
    intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & ->). retpc.
    zstep. rewrite <- Heff. apply evt_done. do 15 eexists. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ 0) Hz) in Heff.
    zstep. ifc. zstep. zstep. cbv beta. zstep. rewrite <- Heff. apply evt_done. do 15 eexists. reflexivity.
Qed.

Lemma loopA : forall n c (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  n = Z.to_nat (w - c) -> 1 <= c < w ->
  sp = Z_to_bv 64 (S - 592) -> s0 = Z_to_bv 64 t -> s3 = Z_to_bv 64 s -> s5 = Z_to_bv 64 (s + 374 + 102 * (c - 1)) ->
  s6 = Z_to_bv 64 c -> s7 = Z_to_bv 64 (S - 592 + 344) -> s8 = Z_to_bv 64 3 -> s10 = Z_to_bv 64 (S - 592 + 200) ->
  s11 = Z_to_bv 64 c -> minv m ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s1' s2' s4' s5' s6' s11' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3 s4' s5' s6' s7 s8 s9 s10 s11' t3' t4' t5' t6')
               F (Z_to_bv 64 0x135b0) fc None m' (seg_rom rsegs) /\ minv m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13534) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros c ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Hn Hc -> -> -> -> -> -> -> -> -> MV; [lia|].
  zstep. zstep.
  eapply evt_cut.
  { eapply (loopAi 3 0 c); first [ reflexivity | (f_equal; lia) | lia | exact MV ]. }
  intros ms1 (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r18 & m1 & -> & MV1).
  pose proof MV1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BA & _).
  pose proof (bytes_byte_read m1 _ _ 1 BA ltac:(cbn; lia)) as RW. cbn [nth Z.of_nat] in RW.
  assert (Hw256 : 0 <= w < 256) by lia.
  zstep. cbv beta. rewrite (bv8_small w Hw256).
  zstep. rewrite swrap32_id by lia. zstep. zstep. zstep.
  destruct (Z.eq_dec (c + 1) w) as [Ec | Ec].
  - ifc. apply evt_done. do 23 eexists. split; [reflexivity | exact MV1].
  - ifc. eapply IH with (c := c + 1).
    all: first [ reflexivity | (f_equal; lia) | lia | exact MV1 ].
Qed.

Ltac sstore MV a :=
  let HS := fresh "HS" in
  pose proof (minv_store_ok _ a MV ltac:(lia) ltac:(lia)) as HS;
  zstep;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?A ?bs) _) =>
    let MV' := fresh "MV" in
    pose proof (minv_store m a bs MV ltac:(lia) ltac:(lia) ltac:(rewrite ?length_le1; reflexivity)) as MV';
    change (minv (write_to_mem m A bs)) in MV';
    clear HS MV; rename MV' into MV;
    let BW' := fresh "BWR" in
    pose proof (bytes_at_write_same rsegs m a bs ltac:(lia) ltac:(rewrite ?length_le1; cbn [length]; lia)) as BW';
    change (bytes_at rsegs (write_to_mem m A bs) a bs) in BW';
    let m' := fresh "m" in
    remember (write_to_mem m A bs) as m' eqn:Em'; clear Em'
  end.

Lemma loopB : forall n i (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  n = Z.to_nat (6 - i) -> 0 <= i < 6 ->
  sp = Z_to_bv 64 (S - 592) -> s2 = Z_to_bv 64 i -> s4 = Z_to_bv 64 (s + 190 + 34 * i) ->
  s5 = Z_to_bv 64 (0x103f0 + 3 * i) -> s6 = Z_to_bv 64 (6 - i) -> s7 = Z_to_bv 64 18 -> s8 = Z_to_bv 64 17 ->
  s10 = Z_to_bv 64 5 -> s11 = Z_to_bv 64 4370 -> minv m ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2' s3 s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13678) fc None m' (seg_rom rsegs) /\ minv m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135dc) fc None m (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Hn Hi -> -> -> -> -> -> -> -> -> MV; [lia|].
  pose proof MV as (MU & WM & MI & ST & S50 & S194 & BT & BW & BS & BA & BSW).
  destruct (stk_cells m _ _ (S - 592 + 50) 34 S50 ltac:(lia) ltac:(lia)) as [junk RJ].
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply POLL with (i := i) (lo := S - 8784) (junk := junk).
    all: try reflexivity.
    all: try lia.
    all: try assumption.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold REAC_CTRL_IDENTITY_POLL_BLOCK_FRAME. lia.
    - intros _. rewrite !unsigned_lit by lia. split; [exact RJ | lia]. }
  clear RJ.
  intros ms1 (u0 & u1 & u2 & r & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m1 & -> & MU1 & WM1 & MI1 & ST1 & HP).
  retpc.
  assert (PK : poll_ok i (Z_to_bv 64 (S - 592 + 50)) = true).
  { unfold poll_ok. rewrite unsigned_lit by lia. apply andb_true_intro. split; [apply andb_true_intro; split; apply Z.leb_le; lia|].
    apply negb_true_iff, Z.eqb_neq. lia. }
  rewrite PK in HP. destruct HP as [-> RW1].
  rewrite (unsigned_lit (S - 592 + 50)) in MU1, RW1 by lia. rewrite (unsigned_lit (S - 592)) in MU1, ST1 by lia.
  unfold REAC_CTRL_IDENTITY_POLL_BLOCK_FRAME in MU1.
  replace (S - 592 + 50 + 34) with (S - 592 + 84) in MU1 by lia.
  pose proof (stk_of_rw_cells rsegs m1 _ _ RW1) as S50'. cbn [cells_size csize Nat.add] in S50'.
  replace (S - 592 + 50 + Z.of_nat 34) with (S - 592 + 84) in S50' by lia.
  pose proof (minv_poll m m1 MV MU1 WM1 MI1 ST1 S50') as MV1.
  destruct (rw_cells_CB_bytes _ _ _ _ RW1) as [PB _]. clear RW1 MU1 WM1 ST1 S50'.
  clear MU WM MI ST S50 S194 BT BW BS BA BSW MV.
  pose proof MV1 as (_ & _ & MI1' & _ & _ & _ & _ & _ & _ & _ & BSW1).
  pose proof (row_B m1 i Hi BSW1) as RB1.
  zstep. ifc. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply BCMP with (ls := GB i) (rs := GB i) (v := 0).
    - rewrite unsigned_lit by lia. exact PB.
    - rewrite unsigned_lit by lia. eapply bytes_at_eqa; [exact RB1 | lia].
    - rewrite unsigned_lit by lia. apply memcmp_self. rewrite length_GB. lia.
    - exact MI1'. }
  intros ms2 H2. unfold memcmp_post in H2.
  destruct H2 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & _ & _).
  retpc.
  pose proof (minv_same m1 m2 MV1 MU2 WM2 MI2) as MV2. clear MU2 WM2 MI2 PB RB1 MV1 BSW1 MI1'.
  pose proof MV2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BSW2).
  pose proof (row_B m2 i Hi BSW2) as RB2.
  pose proof (bytes_byte_read m2 _ _ 16 RB2 ltac:(rewrite length_GB; lia)) as R16.
  pose proof (bytes_byte_read m2 _ _ 17 RB2 ltac:(rewrite length_GB; lia)) as R17.
  change (nth 16 (GB i) (Z_to_bv 8 0)) with (Z_to_bv 8 18) in R16.
  change (nth 17 (GB i) (Z_to_bv 8 0)) with (Z_to_bv 8 17) in R17.
  clear BSW2 RB2.
  zstep. ifc. zstep. cbv beta. zstep. cbv beta.
  sstore MV2 (S - 592 + 197).
  clear R16 R17. rename MV2 into MV.
  pose proof MV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BSW3).
  pose proof (row_B _ i Hi BSW3) as RB3.
  pose proof (bytes_byte_read _ _ _ 18 RB3 ltac:(rewrite length_GB; lia)) as R18.
  pose proof (bytes_byte_read _ _ _ 19 RB3 ltac:(rewrite length_GB; lia)) as R19.
  change (nth 18 (GB i) (Z_to_bv 8 0)) with (Z_to_bv 8 5) in R18.
  change (nth 19 (GB i) (Z_to_bv 8 0)) with (Z_to_bv 8 0) in R19.
  rewrite le1_lit in BWR.
  pose proof (bytes_byte_read _ _ _ 0 BWR ltac:(cbn; lia)) as R197. cbn [nth Z.of_nat] in R197. rewrite Z.add_0_r in R197.
  clear BSW3 RB3 BWR.
  zstep. cbv beta. zstep. cbv beta.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  zstep. zstep. zstep. cbv beta.
  replace (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  clear R18 R19 R197.
  sstore MV (S - 592 + 194). sstore MV (S - 592 + 195). sstore MV (S - 592 + 196).
  zstep. ifc. zstep. zstep. zstep. zstep.
  pose proof MV as (_ & _ & MI5 & _ & _ & _ & _ & _ & _ & _ & BSW5).
  pose proof (row_B _ i Hi BSW5) as RB5.
  pose proof (bytes_at_sub _ _ _ 20 3 RB5 ltac:(rewrite length_GB; lia)) as PL5.
  eapply evt_cut.
  { eapply BCMP with (ls := firstn 3 (skipn 20 (GB i))) (rs := firstn 3 (skipn 20 (GB i))) (v := 0).
    - rewrite unsigned_lit by lia. eapply bytes_at_eqa; [exact PL5 | lia].
    - rewrite unsigned_lit by lia. apply ro_bytes_at; [exact MI5 | lia | rewrite length_poll3; lia | apply ro_poll3; lia].
    - rewrite unsigned_lit by lia. apply memcmp_self. rewrite length_poll3. lia.
    - exact MI5. }
  intros ms6 H6. unfold memcmp_post in H6.
  destruct H6 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & mB & -> & MU6 & WM6 & MI6 & _ & _).
  retpc.
  pose proof (minv_same _ mB MV MU6 WM6 MI6) as MV6. clear MU6 WM6 MI6 PL5 RB5 BSW5 MI5 MV.
  zstep. ifc. zstep. rewrite swrap32_id by lia. zstep. zstep. zstep. zstep.
  destruct (Z.eq_dec i 5) as [-> | Hi5].
  - ifc. apply evt_done. do 21 eexists. split; [reflexivity | exact MV6].
  - ifc. eapply IH with (i := i + 1).
    all: first [ reflexivity | (f_equal; lia) | lia | exact MV6 ].
Qed.

Lemma ro_ack : ro_bytes rsegs 0x10402 HEAD_ACK34.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma ro_mark : ro_bytes rsegs 0x10424 HEAD_MARK34.
Proof. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma sweep_rest : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v32 : word),
  sp = Z_to_bv 64 (S - 592) -> s0 = Z_to_bv 64 t -> s2 = Z_to_bv 64 rows -> s3 = Z_to_bv 64 s ->
  a0 = Z_to_bv 64 (8 + 3 * w) -> minv m -> rw_cells rsegs m0 (S - 592 + 32) [C8 v32] ->
  evt rsegs (fun ms' => exists ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s4' s5' s6' s7' s8' s10' s11' t3' t4' t5' t6' m',
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 v32 (Z_to_bv 64 s) a1' a2' a3' a4' a5' a6' a7'
                    s2' s3 s4' s5' s6' s7' s8' s9 s10' s11' t3' t4' t5' t6')
               F (Z_to_bv 64 0x1367c) fc None m' (seg_rom rsegs) /\ minv m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m v32 -> -> -> -> -> MV HC32.
  pose proof MV as (MU & WM & MI & ST & S50 & S194 & BT & BW & BS & BA & BSW).
  pose proof (bytes_byte_read m _ _ 1 BA ltac:(cbn; lia)) as RW. cbn [nth Z.of_nat] in RW.
  assert (Hw256 : 0 <= w < 256) by lia.
  zstep. cbv beta. rewrite (bv8_small w Hw256).
  zstep. rewrite ?Z.shiftl_mul_pow2 by lia. zstep. zstep. zstep.
  rewrite (proj2 (Z.ltb_ge rows (w * 2 + w + 8))) by lia. cbn [Z.b2z].
  zstep. zstep. rewrite ?Z.lor_0_l.
  zstep. ifc. zstep. ifc.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply (rows_loop (sweep_rows base (Z.to_nat w) vals)) with (s := s) (k := 0) (n := 8 + 3 * w).
    all: first [ reflexivity | (f_equal; lia) | lia | idtac ].
    - pose proof (length_sweep_rows base (Z.to_nat w) vals ltac:(lia)). rewrite Z2Nat.id in H by lia. lia.
    - unfold sweep_rows. discriminate.
    - unfold SW in BSW. rewrite SWEEP_rows in BSW. eapply bytes_at_eqa; [exact BSW | lia].
    - apply sweep_rows_ok. }
  intros ms1 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & ->).
  zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply BCMP with (ls := HEAD_ACK34) (rs := HEAD_ACK34) (v := 0).
    - rewrite unsigned_lit by lia. apply row_0. exact BSW.
    - rewrite unsigned_lit by lia. apply ro_bytes_at; [exact MI | lia | unfold HEAD_ACK34; rewrite length_bl; cbn; lia | exact ro_ack].
    - rewrite unsigned_lit by lia. apply memcmp_self. reflexivity.
    - exact MI. }
  intros ms2 H2. unfold memcmp_post in H2.
  destruct H2 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & _ & _).
  retpc.
  pose proof (minv_same m m2 MV MU2 WM2 MI2) as MV2. clear MU2 WM2 MI2 MV MU WM MI ST S50 S194 BT BW BS BA BSW RW.
  pose proof MV2 as (_ & _ & MI2 & _ & _ & _ & _ & _ & _ & _ & BSW2).
  zstep. ifc. zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply BCMP with (ls := HEAD_MARK34) (rs := HEAD_MARK34) (v := 0).
    - rewrite unsigned_lit by lia. apply row_4. exact BSW2.
    - rewrite unsigned_lit by lia. apply ro_bytes_at; [exact MI2 | lia | unfold HEAD_MARK34; rewrite length_bl; cbn; lia | exact ro_mark].
    - rewrite unsigned_lit by lia. apply memcmp_self. reflexivity.
    - exact MI2. }
  intros ms3 H3. unfold memcmp_post in H3.
  destruct H3 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m3 & -> & MU3 & WM3 & MI3 & _ & _).
  retpc.
  pose proof (minv_same m2 m3 MV2 MU3 WM3 MI3) as MV3. clear MU3 WM3 MI3 MV2 MI2 BSW2.
  zstep. ifc. zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply (loopA0 3 0); first [ reflexivity | (f_equal; lia) | lia | exact MV3 ]. }
  intros ms4 (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & m4 & -> & MV4).
  pose proof MV4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BA4 & _).
  pose proof (bytes_byte_read m4 _ _ 1 BA4 ltac:(cbn; lia)) as RW4. cbn [nth Z.of_nat] in RW4.
  zstep. cbv beta. rewrite (bv8_small w Hw256). zstep. zstep.
  eapply evt_cut with (P := fun ms => exists r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 r24 m',
      ms = MS (mkR r0 (Z_to_bv 64 (S - 592)) gp tp r1 r2 r3 (Z_to_bv 64 t) r4 r5 r6 r7 r8 r9 r10 r11 r12
                   r13 (Z_to_bv 64 s) r14 r15 r16 r17 r18 s9 r19 r20 r21 r22 r23 r24)
              F (Z_to_bv 64 0x135b0) fc None m' (seg_rom rsegs) /\ minv m').
  { destruct (Z.eq_dec w 1) as [Ew | Ew].
    - ifc. apply evt_done. do 26 eexists. split; [reflexivity | exact MV4].
    - ifc. zstep. zstep. zstep. zstep. zstep. zstep.
      eapply evt_mono.
      { eapply (loopA (Z.to_nat (w - 1)) 1); first [ reflexivity | (f_equal; lia) | lia | exact MV4 ]. }
      intros ms5 (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z18 & z19 & z20 & z21 & m5 & -> & MV5).
      do 26 eexists. split; [reflexivity | exact MV5]. }
  intros ms6 (r0 & r1 & r2 & r3 & r4 & r5 & r6 & r7 & r8 & r9 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r18 & r19 & r20 & r21 & r22 & r23 & r24 & m6 & -> & MV6).
  clear MV4 BA4 RW4 MV3.
  pose proof MV6 as (MU6 & WM6 & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (rw_cells_transport rsegs _ m0 m6 _ _ HC32 MU6 WM6 ltac:(unfold Wf; cbn [disjoint_from]; simpl_sizes; slia2)) as C32.
  clear MU6 WM6.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  clear C32.
  eapply evt_cut.
  { eapply (loopB 6 0); first [ reflexivity | (f_equal; lia) | lia | exact MV6 ]. }
  intros ms7 (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q18 & q19 & m7 & -> & MV7).
  zstep. apply evt_done. do 24 eexists. split; [reflexivity | exact MV7].
Qed.

End Sweep.
