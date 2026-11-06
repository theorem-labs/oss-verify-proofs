From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Cells Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcMatch RcMatchLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import reac_ctrl_parse_c reac_box_model_block_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import reac_box_catalogue_match_c.
Import ListNotations.
Open Scope Z_scope.

Definition CM_TBL : list byte := match image_bytes rsegs CM_T 3256 with Some l => l | None => [] end.

Lemma CM_TBL_eq : image_bytes rsegs CM_T 3256 = Some CM_TBL.
Proof. vm_compute. reflexivity. Qed.

Lemma CM_TBL_len : length CM_TBL = 3256%nat.
Proof. exact (image_bytes_length rsegs 3256 CM_T CM_TBL CM_TBL_eq). Qed.

Definition cm_row (i : nat) : list byte := firstn 296 (skipn (296 * i) CM_TBL).

Lemma cm_row_ok : forall i, (i < 11)%nat -> synok (cm_row i) = true /\ gram (cm_row i) = nth i DECLS [].
Proof.
  intros i Hi.
  assert (E : forall j, (j < 11)%nat -> synok (cm_row j) && bool_decide (gram (cm_row j) = nth j DECLS []) = true).
  { intros j Hj. do 11 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. }
  pose proof (E i Hi) as Ei. apply andb_true_iff in Ei as [E1 E2].
  split; [exact E1|]. exact (bool_decide_eq_true_1 _ E2).
Qed.

Lemma cm_rc : forall i nb, (i < 11)%nat -> rc (cm_row i) 0 = 1 /\ synth (cm_row i) 0 nb = nth i DECLS [].
Proof.
  intros i nb Hi. destruct (cm_row_ok i Hi) as [A B]. unfold rc, synth. rewrite A.
  split; [reflexivity|]. rewrite <- B. reflexivity.
Qed.

Lemma cm_decl_len : forall i, (i < 11)%nat -> length (nth i DECLS []) = 32%nat.
Proof. intros i Hi. do 11 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Lemma cm_row_len : forall i, (i < 11)%nat -> length (cm_row i) = 296%nat.
Proof. intros i Hi. unfold cm_row. rewrite length_firstn, length_skipn, CM_TBL_len. lia. Qed.

Lemma cm_join : exists jb, image_bytes rsegs JOIN_0013 64 = Some jb.
Proof.
  exists (match image_bytes rsegs JOIN_0013 64 with Some l => l | None => [] end). vm_compute. reflexivity.
Qed.

Lemma mm_spec : forall n l r v, length l = n -> length r = n -> memcmp_model l r n = Some v ->
  (v = 0 <-> l = r) /\ -256 < v < 256.
Proof.
  induction n as [|n IH]; intros l r v Hl Hr H.
  - destruct l; [|discriminate]. destruct r; [|discriminate]. cbn in H. inversion H. split; [tauto|lia].
  - destruct l as [|a l]; [discriminate|]. destruct r as [|b r]; [discriminate|]. cbn in Hl, Hr, H.
    pose proof (byte_range a). pose proof (byte_range b).
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|E].
    + destruct (IH l r v ltac:(lia) ltac:(lia) H) as [I1 I2]. split; [|exact I2].
      apply bv_eq in E. subst b. split.
      * intros Hv. f_equal. apply I1. exact Hv.
      * intros Hq. apply I1. injection Hq as Hq. exact Hq.
    + inversion H; subst v. split; [|lia]. split; [lia|]. intros Hq. injection Hq as Hab _. subst b. contradiction.
Qed.

Lemma cm_eqb0 : forall v, -2^64 < v < 2^64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
  intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_wrap. change (0 mod 2^64) with 0.
  destruct (Z.eqb_spec v 0) as [E|E]; [subst; reflexivity|]. apply Z.eqb_neq. intros E'.
  apply E. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

Ltac cm_dj := cbn [disjoint_from cells_size csize Nat.add]; rewrite ?CM_TBL_len; repeat split; lia.

Ltac cm_tr MUc WMc m0 :=
  lazymatch type of MUc with
  | munch ?W ?m ?m' =>
    repeat match goal with
    | H : rw_cells rsegs m ?A ?cs |- _ =>
        apply (rw_cells_transport rsegs W m m' A cs) in H; [|exact MUc|exact WMc|cm_dj]
    | H : bytes_at rsegs m ?A ?bs |- _ =>
        apply (bytes_at_transport rsegs W m m' A bs) in H; [|exact MUc|cm_dj]
    | H : stk rsegs m ?lo ?hi |- _ =>
        apply (stk_transport_disjoint rsegs W m m' lo hi) in H; [|exact MUc|exact WMc|cm_dj]
    | H : wr_at rsegs m ?A ?n |- _ => apply (wr_at_transport rsegs m m' A n) in H; [|exact WMc]
    | H : munch ?W0 m0 m |- _ =>
        apply (munch_trans W0 m0 m m') in H;
        [|apply (munch_weaken W W0 m m'); [intros x Hx; cbn [outside] in *; repeat split; lia|exact MUc]]
    | H : wmono rsegs m0 m |- _ => apply (wmono_trans rsegs m0 m m') in H; [|exact WMc]
    end
  end.

Section Match.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (f len Sp : Z) (fb : list byte).
Hypothesis HPC : reac_ctrl_parse_contract.
Hypothesis HMB : reac_box_model_block_contract.
Hypothesis HBC : bcmp_contract.
Hypothesis Hf : 0 <= f < 2^64.
Hypothesis Hlen : 0 <= len < 2^64.
Hypothesis HS : Sp < 2^64.
Hypothesis HS16 : Sp mod 16 = 0.
Hypothesis HK : 272 <= Sp.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis HS3 : 50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m0 f fb /\ (f + 50 <= Sp - 272 \/ Sp <= f).
Hypothesis HTd : CM_T + 3256 <= Sp - 272 \/ Sp <= CM_T.
Hypothesis HJd : JOIN_0013 + 64 <= Sp - 272 \/ Sp <= JOIN_0013.

Local Abbreviation Post := (fun ms' : machine_state =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp - 272, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' (Sp - 272) Sp).

Definition frm (m : word -> option byte) : Prop :=
  exists j0 bb pb,
    rw_cells rsegs m (Sp + -112) [CB 4 j0] /\ rw_cells rsegs m (Sp + -108) [CB 32 bb] /\
    rw_cells rsegs m (Sp + -76) [CB 36 pb] /\
    rw_cells rsegs m (Sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk rsegs m (Sp - 272) (Sp + -112) /\ munch [(Sp - 272, Sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

Lemma mk_frm : forall m j0 bb pb,
  rw_cells rsegs m (Sp + -112) [CB 4 j0] -> rw_cells rsegs m (Sp + -108) [CB 32 bb] ->
  rw_cells rsegs m (Sp + -76) [CB 36 pb] -> rw_cells rsegs m (Sp + -40) [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m (Sp - 272) (Sp + -112) -> munch [(Sp - 272, Sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m -> frm m.
Proof.
  intros m j0 bb pb H1 H2 H3 H4 H5 H6 H7 H8. exists j0, bb, pb.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))).
Qed.

Lemma epi : forall r m (x1 y0 y1 y2 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp y0 y1 y2 (Z_to_bv 64 r) w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19
             s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x14670) fc None m (seg_rom rsegs)).
Proof.
  intros r m x1 y0 y1 y2 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 w19 u3 u4 u5 u6 Er
    (j0 & bb & pb & FA & FB & FP & FC & ST & MU & WM & MI).
  do 8 step.
  apply evt_done. exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, u3, u4, u5, u6, m.
  split; [subst r; unfold mkR; repeat f_equal; lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  pose proof (cm_frame_release rsegs m (Sp - 272) (Sp + -112) (Sp + -108) (Sp + -76) (Sp + -40) j0 bb pb _ ST
                ltac:(lia) FA FB FP FC ltac:(lia) ltac:(lia) ltac:(lia)) as R.
  change (Z.of_nat (cells_size [C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) with 40 in R.
  replace (Sp + -40 + 40) with Sp in R by lia. exact R.
Qed.

Ltac cm_mod := Z.div_mod_to_equations; lia.

Lemma loop : cm_gate len fb = true -> 0 < f -> f + 50 <= 2^64 -> (f + 50 <= Sp - 272 \/ Sp <= f) ->
  forall k i m (x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w9 w18 : word),
  w8 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) -> w9 = Z_to_bv 64 (f + 18) -> w18 = Z_to_bv 64 (Z.of_nat k) ->
  (i + k = 11)%nat -> (0 < k)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  frm m -> bytes_at rsegs m f fb -> bytes_at rsegs m CM_T CM_TBL ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -112)) gp tp y0 y1 y2 w8 w9 z0 z1 z2 z3 z4 z5 z6 z7 w18 (Z_to_bv 64 1)
             s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x14638) fc None m (seg_rom rsegs)).
Proof.
  intros G Hf0 Hf50 Hfd.
  induction k as [|k IH];
    intros i m x1 y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w9 w18 E8 E9 E18 Hik Hk Hnd FRM BF BT; [lia|].
  subst w8 w9 w18.
  assert (Hi : (i < 11)%nat) by lia.
  destruct FRM as (j0 & bb & pb & FA & FB & FP & FC & ST & MU & WM & MI).
  pose proof (cm_wr_of_rw rsegs m _ 32 bb FB) as WB.
  pose proof (bytes_at_sub rsegs m CM_T CM_TBL (296 * i) 296 BT ltac:(rewrite CM_TBL_len; lia)) as BR.
  apply (bytes_at_addr rsegs m _ (CM_T + 296 * Z.of_nat i)) in BR; [|lia].
  fold (cm_row i) in BR.
  step. step. step. step.
  eapply evt_cut.
  { eapply HMB with (p := CM_T + 296 * Z.of_nat i) (b := 0) (o := Sp + -108) (row := cm_row i)
                    (nb := @nil byte) (ob := bb).
    all: try reflexivity.
    all: rewrite ?unsigned_lit by lia.
    all: lazymatch goal with
         | |- stk _ _ _ _ => replace (Sp + -112 - 160) with (Sp - 272) by lia; exact ST
         | |- mem_inv _ _ => exact MI
         | |- _ mod 16 = 0 => cm_mod
         | |- _ <> 0 -> (_ \/ _) -> _ => intros _ [Hb|Hb]; discriminate Hb
         | |- _ <> 0 -> _ mod 8 = 0 /\ _ =>
             intros _; split; [|split; [apply cm_row_len; exact Hi|split; [exact BR|]]];
             [ replace (CM_T + 296 * Z.of_nat i) with ((15782 + 37 * Z.of_nat i) * 8) by (unfold CM_T; lia);
               apply Z_mod_mult
             | unfold CM_T in *; lia ]
         | |- _ <> 0 -> rw_cells _ _ _ _ /\ _ => intros _; split; [exact FB|]; unfold JOIN_0013 in *; lia
         | |- _ => unfold CM_T; lia
         end. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
              PB & WM' & MI' & ST').
  assert (Z0 : (CM_T + 296 * Z.of_nat i =? 0) || (Sp + -108 =? 0) = false).
  { apply orb_false_iff. split; apply Z.eqb_neq; unfold CM_T; lia. }
  rewrite Z0 in PB |- *. destruct PB as [BB MUm].
  destruct (cm_rc i (@nil byte) Hi) as [RC SY]. rewrite RC. rewrite SY in BB.
  rewrite unsigned_lit in MUm, ST' by lia.
  rewrite ret_pc_even by (try lia; reflexivity).
  clear FB ST MI Z0.
  cm_tr MUm WM' m0.
  replace (Sp + -112 - 160) with (Sp - 272) in ST' by lia.
  pose proof (cm_rw_of_bytes rsegs m' _ _ 32 BB (cm_decl_len i Hi) WB) as FB'.
  clear WB.
  step. if_false.
  step. step. step. step.
  pose proof (bytes_at_sub rsegs m' f fb 18 32 BF ltac:(lia)) as BK.
  apply (bytes_at_addr rsegs m' _ (f + 18)) in BK; [|lia].
  fold (cm_blk fb) in BK.
  assert (LK : length (cm_blk fb) = 32%nat) by (unfold cm_blk; rewrite length_firstn, length_skipn; lia).
  destruct (memcmp_model_total (cm_blk fb) (nth i DECLS []) 32 ltac:(lia) ltac:(rewrite cm_decl_len; lia))
    as [v Hv].
  pose proof (mm_spec 32 (cm_blk fb) (nth i DECLS []) v LK (cm_decl_len i Hi) Hv) as [MM VR].
  eapply evt_cut.
  { eapply HBC with (ls := cm_blk fb) (rs := nth i DECLS []) (v := v); rewrite ?unsigned_lit by lia.
    - exact BK.
    - exact BB.
    - exact Hv.
    - exact MI'. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'' &
              -> & MUb & WMb & MIb & _ & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  clear BK BB MI'.
  cm_tr MUb WMb m0.
  step.
  rewrite cm_eqb0 by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
  - eapply epi; [|eapply mk_frm; eassumption].
    symmetry. apply cm_want_hit; [exact G | exact Hi | symmetry; apply MM; exact V0 | exact Hnd].
  - assert (Hne : nth i DECLS [] <> cm_blk fb) by (intros Hq; apply V0; apply MM; symmetry; exact Hq).
    step. step. step.
    rewrite cm_eqb_lit by lia.
    match goal with |- context [?e =? 0] => destruct (Z.eqb_spec e 0) as [K0|K0] end; cbn [negb]; cbv iota.
    + assert (k = 0%nat) by lia. subst k.
      step.
      eapply epi; [|eapply mk_frm; eassumption].
      symmetry. apply cm_want_none. intros j Hj.
      destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; lia].
    + destruct k as [|k]; [lia|].
      eapply (IH (S i)); [f_equal; lia | reflexivity | f_equal; lia | lia | lia | |
                          eapply mk_frm; eassumption | eassumption | eassumption].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; lia].
Qed.

Lemma body : forall m (y0 y1 y2 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 : word),
  frm m -> bytes_at rsegs m CM_T CM_TBL ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 (Sp + -112)) gp tp y0 y1 y2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) z2 z3 z4 z5 z6 z7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x145d4) fc None m (seg_rom rsegs)).
Proof.
  intros m y0 y1 y2 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 FRM BT.
  step. step.
  rewrite cm_ltu_lit by lia.
  destruct (Z.ltb_spec len 50) as [L|L]; cbv iota.
  - step. eapply epi; [|exact FRM].
    symmetry. apply cm_gate_false. unfold cm_gate. rewrite (proj2 (Z.leb_gt 50 len) L). reflexivity.
  - destruct (HS3 L) as (Hf0 & Hf50 & BF0 & Hfd).
    destruct FRM as (j0 & bb & pb & FA & FB & FP & FC & ST & MU & WM & MI).
    pose proof (bytes_at_transport rsegs [(Sp - 272, Sp)] m0 m f fb BF0 MU ltac:(cm_dj)) as BF.
    assert (FRM : frm m) by (eapply mk_frm; eassumption).
    assert (GF : forall k c, (k = 12%nat /\ c = 136 \/ k = 13%nat /\ c = 25 \/ k = 16%nat /\ c = 205 \/
                              k = 17%nat /\ c = 234) -> bv_unsigned (nth k fb (Z_to_bv 8 0)) <> c ->
              want CM_T len fb = 0).
    { intros k c Hk Hne. apply cm_gate_false. unfold cm_gate, cp_v, cp_b, cp_z.
      rewrite (proj2 (Z.leb_le 50 len) L).
      destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; rewrite (proj2 (Z.eqb_neq _ _) Hne);
        rewrite ?andb_false_r; reflexivity. }
    pose proof (rd_byte rsegs m f fb 12 BF ltac:(lia)) as R12.
    pose proof (rd_byte rsegs m f fb 13 BF ltac:(lia)) as R13.
    pose proof (rd_byte rsegs m f fb 16 BF ltac:(lia)) as R16.
    pose proof (rd_byte rsegs m f fb 17 BF ltac:(lia)) as R17.
    pose proof (byte_range (nth 12 fb (Z_to_bv 8 0))). pose proof (byte_range (nth 13 fb (Z_to_bv 8 0))).
    pose proof (byte_range (nth 16 fb (Z_to_bv 8 0))). pose proof (byte_range (nth 17 fb (Z_to_bv 8 0))).
    step. step. step. step.
    rewrite cm_eqb_zxb by lia.
    destruct (Z.eqb_spec (bv_unsigned (nth 12 fb (Z_to_bv 8 0))) 136) as [E12|E12]; cbn [negb]; cbv iota.
    2:{ step. eapply epi; [|exact FRM]. symmetry. apply (GF 12%nat 136); [lia | exact E12]. }
    step. step. step.
    rewrite cm_eqb_zxb by lia.
    destruct (Z.eqb_spec (bv_unsigned (nth 13 fb (Z_to_bv 8 0))) 25) as [E13|E13]; cbn [negb]; cbv iota.
    2:{ step. eapply epi; [|exact FRM]. symmetry. apply (GF 13%nat 25); [lia | exact E13]. }
    step. step. step.
    rewrite cm_eqb_zxb by lia.
    destruct (Z.eqb_spec (bv_unsigned (nth 16 fb (Z_to_bv 8 0))) 205) as [E16|E16]; cbn [negb]; cbv iota.
    2:{ step. eapply epi; [|exact FRM]. symmetry. apply (GF 16%nat 205); [lia | exact E16]. }
    step. step. step.
    rewrite cm_eqb_zxb by lia.
    destruct (Z.eqb_spec (bv_unsigned (nth 17 fb (Z_to_bv 8 0))) 234) as [E17|E17]; cbn [negb]; cbv iota.
    2:{ step. eapply epi; [|exact FRM]. symmetry. apply (GF 17%nat 234); [lia | exact E17]. }
    clear FRM GF R12 R13 R16 R17.
    step. step. step.
    destruct (stk_split rsegs m (Sp - 272) (Sp + -112 - 80) (Sp + -112) ST ltac:(lia)) as [STlo SThi].
    clear ST.
    eapply evt_cut.
    { eapply HPC with (f := f) (n := len) (o := Sp + -76) (S := Sp + -112) (fr := fb) (junk := pb).
      all: unfold REAC_CTRL_PARSE_K; try reflexivity.
      all: lazymatch goal with
           | |- stk _ _ _ _ => exact SThi
           | |- mem_inv _ _ => exact MI
           | |- length _ = _ => exact Hfb
           | |- _ mod 16 = 0 => cm_mod
           | |- forall i, In i _ -> _ =>
               intros i Hi; apply (proj2 (proj2 BF)); rewrite Hfb; pose proof (cp_rd_lt39 len fb i Hi); lia
           | |- _ <> 0 -> _ => intros _; split; [cm_mod|split; [lia|split; [exact FP|split; [lia|intros _; lia]]]]
           | |- _ => lia
           end. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                MUp & WMp & MIp & STp & RWp).
    specialize (RWp ltac:(lia)).
    unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUp, STp.
    replace (Sp + -76 =? 0) with false in MUp by (symmetry; apply Z.eqb_neq; lia).
    cbn [app] in MUp.
    rewrite ret_pc_even by (try lia; reflexivity).
    clear FP SThi MI.
    cm_tr MUp WMp m0.
    pose proof (stk_merge rsegs m' (Sp - 272) (Sp + -112 - 80) (Sp + -112) STlo STp ltac:(lia)) as ST.
    clear STlo STp.
    assert (FRM : frm m') by (eapply mk_frm; eassumption).
    step. step.
    pose proof (ctrlparse_kind_range len fb) as KR.
    rewrite cm_eqb_lit by lia.
    destruct (Z.eqb_spec (fst (ctrlparse len fb)) 9) as [K9|K9]; cbn [negb]; cbv iota.
    2:{ step. eapply epi; [|exact FRM]. symmetry. apply cm_gate_false. unfold cm_gate, cp_v, cp_b, cp_z.
        rewrite (proj2 (Z.eqb_neq _ _) K9). rewrite !andb_false_r. reflexivity. }
    assert (G : cm_gate len fb = true).
    { unfold cm_gate, cp_v, cp_b, cp_z. rewrite (proj2 (Z.leb_le 50 len) L), E12, E13, E16, E17, K9. reflexivity. }
    do 5 step.
    eapply (loop G Hf0 Hf50 Hfd 11 0); [ first [reflexivity | (unfold CM_T; f_equal; lia) | (vm_compute; reflexivity)]
                                        | f_equal; lia | reflexivity | lia | lia | intros j Hj; lia
                                        | exact FRM | exact BF | exact BT ].
Qed.

End Match.

Theorem reac_box_catalogue_match_holds :
  reac_ctrl_parse_contract -> reac_box_model_block_contract -> bcmp_contract -> reac_box_catalogue_match_contract.
Proof.
  intros HPC HMB HBC. unfold reac_box_catalogue_match_contract, REAC_BOX_CATALOGUE_MATCH, CM_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f len Sp fb -> -> -> Hf Hlen HS HS16 HK ST Hwin Hfb HS3 HT MI.
  pose proof CM_TBL_len as Ltbl.
  assert (BT : bytes_at rsegs m CM_T CM_TBL).
  { apply (cm_bytes_img rsegs m CM_T 3256 CM_TBL CM_TBL_eq); [unfold CM_T; lia | unfold CM_T; lia |].
    intros a Ha. apply HT. lia. }
  pose proof (cm_img_apart rsegs CM_T 3256 CM_TBL (Sp - 272) Sp CM_TBL_eq ltac:(lia) ltac:(lia) Hwin) as HTd.
  destruct cm_join as [jb JB].
  pose proof (cm_img_apart rsegs JOIN_0013 64 jb (Sp - 272) Sp JB ltac:(lia) ltac:(lia) Hwin) as HJd.
  change (Z.of_nat 3256) with 3256 in HTd. change (Z.of_nat 64) with 64 in HJd.
  clear HT Hwin JB.
  pose proof (munch_refl [(Sp - 272, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  step.
  destruct (stk_carve rsegs m (Sp - 272) Sp 112 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 112) with 112 in ST1, FR.
  replace (Sp - 112) with (Sp + -112) in ST1, FR by lia.
  pose proof (rw_cells_split_CB rsegs m (Sp + -112) [] 112 junk [] [4; 32; 36; 40]%nat FR eq_refl) as FR'.
  clear FR. cbn [app mk_CB_cells] in FR'.
  step. step. step. step. step.
  match goal with H : rw_cells rsegs ?mm (Sp + -112) (?c1 :: ?c2 :: ?c3 :: ?cs) |- _ =>
    destruct (cm_frame_split rsegs mm _ (Sp + -108) (Sp + -76) (Sp + -40) c1 c2 c3 cs eq_refl eq_refl eq_refl H
                ltac:(lia) ltac:(lia) ltac:(lia)) as (FA & FB & FP & FC)
  end.
  eapply body; try eassumption.
  eapply mk_frm; eassumption.
Qed.
